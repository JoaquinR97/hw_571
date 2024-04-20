`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../hw4-multicycle/divider_unsigned_pipelined.sv"
`endif

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    input wire [4:0] rd, 
    input wire [4:0] rs1,
    input wire [4:0] rs2, 
    input wire [31:0] rd_data, 
    input wire [31:0] rs1_data,
    input wire [31:0] rs2_data, 
    input wire [31:0] alu_value, 
    input wire [31:0] flag,
    input wire [31:0] flag2,
    output wire [(8*32)-1:0] disasm
);
  // synthesis translate_off
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
  // synthesis translate_on
endmodule

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  // TODO: your code here
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

  // Assuming regs[0] should always read as 0
  assign rs1_data = (rs1 == 0) ? 32'd0 : regs[rs1];
  assign rs2_data = (rs2 == 0) ? 32'd0 : regs[rs2];

  always_ff @(posedge clk) begin
    if (rst) begin
        for (int i = 0; i < NumRegs; i++) begin
            regs[i] <= 32'd0;
        end
    end else begin
      if (we && rd != 0) begin
        regs[rd] <= rd_data;
      end

      regs[0] <= 0;
    end
  end

  
endmodule

/**
 * This enum is used to classify each cycle as it comes through the Writeback stage, identifying
 * if a valid insn is present or, if it is a stall cycle instead, the reason for the stall. The
 * enum values are mutually exclusive: only one should be set for any given cycle. These values
 * are compared against the trace-*.json files to ensure that the datapath is running with the
 * correct timing.
 *
 * You will need to set these values at various places within your pipeline, and propagate them
 * through the stages until they reach Writeback where they can be checked.
 */
typedef enum {
  /** invalid value, this should never appear after the initial reset sequence completes */
  CYCLE_INVALID = 0,
  /** a stall cycle that arose from the initial reset signal */
  CYCLE_RESET = 1,
  /** not a stall cycle, a valid insn is in Writeback */
  CYCLE_NO_STALL = 2,
  /** a stall cycle that arose from a taken branch/jump */
  CYCLE_TAKEN_BRANCH = 4,

  // the values below are only needed in HW5B

  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence.i insn */
  CYCLE_FENCEI = 32
} cycle_status_e;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_decode_t;

/** state at the start of execute stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;

  // logic [`REG_SIZE] rd_data; // Data to be written to the destination register
  // logic [4:0] rd; // Destination register address
  // logic [4:0] rs1, rs2; // Source register addresses
  logic [`REG_SIZE] rs1_data, rs2_data; // Data read from the source registers
  // logic write_enable; // Write enable signal
  // logic [`REG_SIZE] alu_value;
  // logic reset; // Reset signal
  // logic illegal_insn; // Reset signal

  // Instruction subsets
  logic [6:0] insn_funct7;
  logic [4:0] insn_rs2;
  logic [4:0] insn_rs1;
  logic [2:0] insn_funct3;
  logic [4:0] insn_rd;
  logic [`OPCODE_SIZE] insn_opcode;

  logic [11:0] imm_i;
  logic [11:0] imm_s;
  logic [12:0] imm_b;
  logic [20:0] imm_j;

  logic [31:0] imm_i_sext;
  logic [31:0] imm_s_sext;
  logic [31:0] imm_b_sext;
  logic [31:0] imm_j_sext;

  // Instruction type flags
  logic is_lui, is_auipc, is_jal, is_jalr;
  logic is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu;
  logic is_lb, is_lh, is_lw, is_lbu, is_lhu;
  logic is_sb, is_sh, is_sw;
  logic is_addi, is_slti, is_sltiu, is_xori, is_ori, is_andi;
  logic is_slli, is_srli, is_srai;
  logic is_add, is_sub, is_sll, is_slt, is_sltu, is_xor, is_srl, is_sra, is_or, is_and;
  logic is_mul, is_mulh, is_mulhsu, is_mulhu, is_div, is_divu, is_rem, is_remu;
  logic is_ecall, is_fence;
  logic halt;
} stage_execute_t;

// Memory stage
typedef struct packed {
  // logic [`REG_SIZE] inputbCLA32;
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  logic [`REG_SIZE] rd_data; // Data to be written to the destination register
  logic [4:0] rd; // Destination register address
  logic [4:0] rs1, rs2; // Source register addresses
  logic [`REG_SIZE] rs1_data, rs2_data; // Data read from the source registers
  logic [`REG_SIZE] effective_addr;
  logic write_enable; // Write enable signal
  // logic [`REG_SIZE] alu_value;
  logic reset; // Reset signal
  logic halt;
  logic illegal_insn; // Reset signal
  cycle_status_e cycle_status;
  logic [`OPCODE_SIZE] insn_opcode;
  logic is_lb, is_lh, is_lw, is_lbu, is_lhu;
  logic is_sb, is_sh, is_sw;
  logic is_div, is_divu;
  logic is_rem, is_remu;
} stage_memory_t;

// Writeback stage
typedef struct packed {
  // logic [`REG_SIZE] inputbCLA32;
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  logic [`REG_SIZE] rd_data; // Data to be written to the destination register
  logic [4:0] rd; // Destination register address
  logic [4:0] rs1, rs2; // Source register addresses
  logic [`REG_SIZE] rs1_data, rs2_data; // Data read from the source registers
  logic write_enable; // Write enable signal
  // logic [`REG_SIZE] alu_value;
  logic reset; // Reset signal
  logic halt;
  logic illegal_insn; // Reset signal
  cycle_status_e cycle_status;
} stage_writeback_t;

module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  logic [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // send PC to imem for next cycle
  logic [`REG_SIZE] pc_temp;

  assign pc_to_imem = f_pc_current;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= flag_taken ? pc_temp : (stall_flag_bf_execute ? f_pc_current : f_pc_current + 4);
    end
  end

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .rd   (5'b0),
      .rs1  (5'b0),
      .rs2  (5'b0),
      .rd_data   (32'b0),
      .rs1_data  (32'b0),
      .rs2_data  (32'b0),
      .alu_value  (32'b0),
      .flag  (flag),
      .flag2  (flag2),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages

  // Making temp variable to overwrite in always comb
  // This is for skipping in case of a branch
  cycle_status_e temp_cycle_status_d;

  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };
    end else begin
      begin
        decode_state <= '{
          pc: flag_taken ? 0 : (stall_flag_bf_execute ? decode_state.pc : pc_to_imem),
          insn: flag_taken ? 32'h00000000 : (stall_flag_bf_execute ? decode_state.insn : f_insn),
          cycle_status: flag_taken ? CYCLE_TAKEN_BRANCH : (stall_flag_bf_execute ? decode_state.cycle_status : f_cycle_status)
        };
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .rd   (5'b0),
      .rs1  (5'b0),
      .rs2  (5'b0),
      .rd_data   (32'b0),
      .rs1_data  (32'b0),
      .rs2_data  (32'b0),
      .alu_value  (32'b0),
      .flag  (flag),
      .flag2  (flag2),
      .disasm(d_disasm)
  );

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = decode_state.insn;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = decode_state.insn[31:20];
  wire [ 4:0] imm_shamt = decode_state.insn[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {decode_state.insn[31:12], 1'b0};

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  wire insn_lui = insn_opcode == OpLui;
  wire insn_auipc = insn_opcode == OpAuipc;
  wire insn_jal = insn_opcode == OpJal;
  wire insn_jalr = insn_opcode == OpJalr;

  wire insn_beq = insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b000;
  wire insn_bne = insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b001;
  wire insn_blt = insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b100;
  wire insn_bge = insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b111;

  wire insn_lb = insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b000;
  wire insn_lh = insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b001;
  wire insn_lw = insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && decode_state.insn[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && decode_state.insn[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && decode_state.insn[14:12] == 3'b010;

  wire insn_addi = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b000;
  wire insn_slti = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b011;
  wire insn_xori = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b100;
  wire insn_ori = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b110;
  wire insn_andi = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b111;

  wire insn_slli = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b001 && decode_state.insn[31:25] == 7'd0;
  wire insn_srli = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'd0;
  wire insn_srai = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'b0100000;

  wire insn_add = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b000 && decode_state.insn[31:25] == 7'd0;
  wire insn_sub  = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b000 && decode_state.insn[31:25] == 7'b0100000;
  wire insn_sll = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b001 && decode_state.insn[31:25] == 7'd0;
  wire insn_slt = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b010 && decode_state.insn[31:25] == 7'd0;
  wire insn_sltu = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b011 && decode_state.insn[31:25] == 7'd0;
  wire insn_xor = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b100 && decode_state.insn[31:25] == 7'd0;
  wire insn_srl = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'd0;
  wire insn_sra  = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'b0100000;
  wire insn_or = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b110 && decode_state.insn[31:25] == 7'd0;
  wire insn_and = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b111 && decode_state.insn[31:25] == 7'd0;

  wire insn_mul    = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b000;
  wire insn_mulh   = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b001;
  wire insn_mulhsu = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b010;
  wire insn_mulhu  = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b011;
  wire insn_div    = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b100;
  wire insn_divu   = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b101;
  wire insn_rem    = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b110;
  wire insn_remu   = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b111;

  wire insn_ecall = insn_opcode == OpEnviron && decode_state.insn[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

  // Reading from registers
  logic [`REG_SIZE] rs1_data_decode, rs2_data_decode; // Data read from the source registers (in case of overwrite)

  logic [`REG_SIZE] rs1_data_out, rs2_data_out; // Data read from the source registers

  /****************/
  /* EXECUTE STAGE*/
  /****************/

  stage_execute_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        insn_funct7: 0,
        insn_rs2: 0,
        insn_rs1: 0,
        rs1_data: 0,
        rs2_data: 0,
        insn_funct3: 0,
        insn_rd: 0,
        insn_opcode: 0,
        imm_i: 0,
        imm_s: 0,
        imm_b: 0,
        imm_j: 0,
        imm_i_sext: 0,
        imm_s_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        is_lui: 0, is_auipc: 0, is_jal: 0, is_jalr: 0,
        is_beq: 0, is_bne: 0, is_blt: 0, is_bge: 0, is_bltu: 0, is_bgeu: 0,
        is_lb: 0, is_lh: 0, is_lw: 0, is_lbu: 0, is_lhu: 0,
        is_sb: 0, is_sh: 0, is_sw: 0,
        is_addi: 0, is_slti: 0, is_sltiu: 0, is_xori: 0, is_ori: 0, is_andi: 0,
        is_slli: 0, is_srli: 0, is_srai: 0,
        is_add: 0, is_sub: 0, is_sll: 0, is_slt: 0, is_sltu: 0, is_xor: 0, is_srl: 0, is_sra: 0, is_or: 0, is_and: 0,
        is_mul: 0, is_mulh: 0, is_mulhsu: 0, is_mulhu: 0, is_div: 0, is_divu: 0, is_rem: 0, is_remu: 0,
        is_ecall: 0, is_fence: 0,
        halt: 0
      }; 
    end else begin
      execute_state <= '{
        pc: (flag_taken || stall_flag_bf_execute) ? 0 : decode_state.pc,
        insn: (flag_taken || stall_flag_bf_execute) ? 32'h00000000 : decode_state.insn,
        cycle_status: (flag_taken || stall_flag_bf_execute) ? CYCLE_TAKEN_BRANCH : decode_state.cycle_status,
        insn_funct7: insn_funct7,
        insn_rs1: (flag_taken || stall_flag_bf_execute) ? 0 : insn_rs1,
        rs1_data: (flag_taken || stall_flag_bf_execute) ? 0 : rs1_data_decode,
        insn_rs2: (flag_taken || stall_flag_bf_execute) ? 0 : insn_rs2,
        rs2_data: (flag_taken || stall_flag_bf_execute) ? 0 : rs2_data_decode,
        insn_funct3: insn_funct3,
        insn_rd: (flag_taken || stall_flag_bf_execute) ? 0 : (is_b_or_s ? 0 : insn_rd),
        insn_opcode: (flag_taken || stall_flag_bf_execute) ? 7'h0 : insn_opcode,
        imm_i: imm_i,
        imm_s: imm_s,
        imm_b: imm_b,
        imm_j: imm_j,
        imm_i_sext: imm_i_sext,
        imm_s_sext: imm_s_sext,
        imm_b_sext: imm_b_sext,
        imm_j_sext: imm_j_sext,
        is_lui: insn_lui,
        is_auipc: insn_auipc,
        is_jal: insn_jal,
        is_jalr: insn_jalr,
        is_beq: insn_beq,
        is_bne: insn_bne,
        is_blt: insn_blt,
        is_bge: insn_bge,
        is_bltu: insn_bltu,
        is_bgeu: insn_bgeu,
        is_lb: insn_lb,
        is_lh: insn_lh,
        is_lw: insn_lw,
        is_lbu: insn_lbu,
        is_lhu: insn_lhu,
        is_sb: insn_sb,
        is_sh: insn_sh,
        is_sw: insn_sw,
        is_addi: insn_addi,
        is_slti: insn_slti,
        is_sltiu: insn_sltiu,
        is_xori: insn_xori,
        is_ori: insn_ori,
        is_andi: insn_andi,
        is_slli: insn_slli,
        is_srli: insn_srli,
        is_srai: insn_srai,
        is_add: insn_add,
        is_sub: insn_sub,
        is_sll: insn_sll,
        is_slt: insn_slt,
        is_sltu: insn_sltu,
        is_xor: insn_xor,
        is_srl: insn_srl,
        is_sra: insn_sra,
        is_or: insn_or,
        is_and: insn_and,
        is_mul: insn_mul,
        is_mulh: insn_mulh,
        is_mulhsu: insn_mulhsu,
        is_mulhu: insn_mulhu,
        is_div: insn_div,
        is_divu: insn_divu,
        is_rem: insn_rem,
        is_remu: insn_remu,
        is_ecall: insn_ecall,
        is_fence: insn_fence,
        halt: halt_e
      };
    end
  end

  wire [255:0] e_disasm;
  Disasm #(
      .PREFIX("E")
  ) disasm_2execute (
      .insn  (execute_state.insn),
      .rd  (execute_state.insn_rd),
      .rs1  (execute_state.insn_rs1),
      .rs2  (execute_state.insn_rs2),
      .rd_data   (32'b0),
      .rs1_data  (execute_state.rs1_data),
      .rs2_data  (execute_state.rs2_data),
      .alu_value  (32'b0),
      .flag  (flag),
      .flag2  (flag2),
      .disasm(e_disasm)
  );

  // For all the datapath logic
  logic illegal_insn;
  
  // rf values
  logic [4:0] rd; // Destination register address
  logic [4:0] rs1, rs2; // Source register addresses
  logic [`REG_SIZE] rd_data; // Data to be written to the destination register
  logic [`REG_SIZE] alu_value; // Alu value to then be written
  logic [`REG_SIZE] rs1_data_bypass, rs2_data_bypass; // Data read from the source registers
  logic write_enable; // Write enable signal
  logic reset; // Reset signal
  logic [`REG_SIZE] flag; // Reset signal
  logic [`REG_SIZE] flag2; // Reset signal

  logic [`REG_SIZE] immediateShiftedLeft;
  logic [`REG_SIZE] inputaCLA32;
  logic [`REG_SIZE] inputbCLA32;
  logic [`REG_SIZE] cla_sum;
  logic adder_carry_in;

  // Alu flag has added to avoid a circular input into the CLA error
  logic stall_flag_bf_execute;
  logic flag_taken;
  logic alu_flag1;
  logic halt_e;

  // Multiplication
  logic [63:0] multiplication;
  logic signed [63:0] extended_rs1_data;
  logic [63:0] extended_rs2_data;

  // Our divider
  logic [`REG_SIZE] divider_input_a;
  logic [`REG_SIZE] divider_input_b;
  logic [`REG_SIZE] divider_quotient;
  logic [`REG_SIZE] divider_remainder;
  logic sign_result;
  logic [`REG_SIZE] temp_divider_value;
  logic [31:0] abs_a, abs_b;

  divider_unsigned_pipelined divider_instance(
      clk,
      rst,
      divider_input_a, 
      divider_input_b, 
      divider_remainder, 
      divider_quotient
  );

  // Memory
  logic [`REG_SIZE] effective_addr;

  logic is_u_or_j;
  logic is_i;

  always_comb begin
    // PC Current Update
    pc_temp = f_pc_current;

    // Set f instruction (pushed to decode)
    f_insn = insn_from_imem;

    rd_data = 32'b0;
    alu_value = cla_sum;

    rd = 5'b0; // Default to an invalid register address
    rs1 = 5'b0;
    rs2 = 5'b0;
    flag = 32'd1;
    flag2 = 32'd5;

    halt_e = 1'b0;

    // Divider
    divider_input_a = 32'b0;
    divider_input_b = 32'b0;
    temp_divider_value = 32'b0;
    abs_a = 32'b0;
    abs_b = 32'b0;

    // Multiplication
    multiplication = 64'b0;
    extended_rs1_data = 64'b0;
    extended_rs2_data = 64'b0;

    flag_taken = 1'b0;
    stall_flag_bf_execute = 1'b0;
    alu_flag1 = 1'b0;

    // flag2 = inputaCLA32;
    rs1_data_bypass = execute_state.rs1_data;
    rs2_data_bypass = execute_state.rs2_data;
    write_enable = 1'b0; // Default to not writing

    immediateShiftedLeft = 32'b0;
    inputaCLA32 = 32'b0;
    inputbCLA32 = 32'b0;
    // cla_sum = 32'b0; // Not needed as we are outputting this value
    adder_carry_in = 1'b0;

    reset = 1'b0;
    illegal_insn = 1'b0;

    // Memory
    effective_addr = 32'b0;
    
    // For edge cases with memory
    is_u_or_j = 1'b0;
    is_i = 1'b0;

    // WX Bypass
    if (execute_state.insn_rs1 == writeback_state.rd) begin
      rs1_data_bypass = writeback_state.rd_data;
      if (execute_state.insn_rs1 == 0) rs1_data_bypass = 0;
    end  
    
    if (execute_state.insn_rs2 == writeback_state.rd) begin
      rs2_data_bypass = writeback_state.rd_data;
      if (execute_state.insn_rs2 == 0) rs2_data_bypass = 0;
    end  

    // MX Bypass
    if (execute_state.insn_rs1 == memory_state.rd) begin
      rs1_data_bypass = memory_state.rd_data;
      if (execute_state.insn_rs1 == 0) rs1_data_bypass = 0;
    end  
    
    if (execute_state.insn_rs2 == memory_state.rd) begin
      rs2_data_bypass = memory_state.rd_data;
      if (execute_state.insn_rs2 == 0) rs2_data_bypass = 0;
    end 

    case (execute_state.insn_opcode)
      OpLui: begin
        if (execute_state.is_lui) begin
          rd_data = {execute_state.insn[31:12], 12'b0};
          rd = execute_state.insn_rd;
          write_enable = 1'b1;
        end
      end

      OpAuipc: begin
        if (execute_state.is_auipc) begin
          write_enable = 1'b1;
          rd = execute_state.insn_rd;
          immediateShiftedLeft = {execute_state.insn[31:12], 12'b0} + execute_state.pc;
          
          rd_data = immediateShiftedLeft;
        end
      end

      OpJal: begin
        if (execute_state.is_jal) begin
          write_enable = 1'b1;          
          rd = execute_state.insn_rd;

          // Save next cycle
          rd_data = pc_temp + 4;
          pc_temp = execute_state.pc + execute_state.imm_j_sext;

          // Flag to update to NOP other instructions
          flag_taken = 1'b1;
        end
      end

      OpJalr: begin
        if (execute_state.is_jalr) begin
          write_enable = 1'b1;
          rd = execute_state.insn_rd;
          rs1 = execute_state.insn_rs1;

          // Save next cycle
          rd_data = pc_temp + 4;
          pc_temp = (execute_state.rs1_data + execute_state.imm_i_sext) & ~32'b1;
        end
      end

      OpRegImm: begin
        write_enable = 1'b1;
        rd = execute_state.insn_rd; 
        rs1 = execute_state.insn_rs1;

        if (execute_state.is_addi) begin
          inputaCLA32 = rs1_data_bypass; // execute_state.rs1_data;
          inputbCLA32 = execute_state.imm_i_sext;
          alu_flag1 = 1'b1;
        end 
        
        if (execute_state.is_slti) begin
          rd_data = $signed(rs1_data_bypass) < $signed(execute_state.imm_i_sext) ? 32'b1 : 32'b0;
        end
        
        if (execute_state.is_sltiu) begin
          rd_data = $unsigned(rs1_data_bypass) < $unsigned(execute_state.imm_i_sext) ? 32'b1 : 32'b0;
        end
        
        if (execute_state.is_xori) begin
          rd_data = rs1_data_bypass ^ execute_state.imm_i_sext;
        end

        if (execute_state.is_ori) begin
          rd_data = rs1_data_bypass | execute_state.imm_i_sext;
        end

        if (execute_state.is_andi) begin
          rd_data = rs1_data_bypass & execute_state.imm_i_sext;
        end

        if (execute_state.is_slli) begin
          rd_data = rs1_data_bypass << execute_state.imm_i[4:0];
        end

        if (execute_state.is_srli) begin
          rd_data = rs1_data_bypass >> execute_state.imm_i[4:0];
        end

        if (execute_state.is_srai) begin
          rd_data = $signed(rs1_data_bypass) >>> execute_state.imm_i[4:0];
          flag = $signed(rs1_data_bypass) >>> execute_state.imm_i[4:0];
        end
      end

      OpRegReg: begin
        rd = execute_state.insn_rd;
        rs1 = execute_state.insn_rs1;
        rs2 = execute_state.insn_rs2;
        write_enable = 1'b1;

        if (execute_state.is_add) begin
          inputaCLA32 = rs1_data_bypass; // execute_state.rs1_data;
          inputbCLA32 = rs2_data_bypass; // execute_state.rs2_data;
          alu_flag1 = 1'b1;
        end

        if (execute_state.is_sub) begin
          inputaCLA32 = rs1_data_bypass;
          inputbCLA32 = ~rs2_data_bypass;  // two's compliment
          adder_carry_in = 1'b1;   // Set carry in to 1 for two's complement addition
          alu_flag1 = 1'b1;
        end

        if (execute_state.is_sll) begin
          rd_data = rs1_data_bypass << rs2_data_bypass[4:0];
        end

        if (execute_state.is_slt) begin
          rd_data = $signed(rs1_data_bypass) < $signed(rs2_data_bypass) ? 32'b1 : 32'b0;
        end

        if (execute_state.is_sltu) begin
          rd_data = $unsigned(rs1_data_bypass) < $unsigned(rs2_data_bypass) ? 32'b1 : 32'b0;
        end

        if (execute_state.is_xor) begin
          rd_data = rs1_data_bypass ^ rs2_data_bypass;
        end

        if (execute_state.is_srl) begin
          rd_data = rs1_data_bypass >> rs2_data_bypass[4:0];
        end

        if (execute_state.is_sra) begin
          rd_data = $signed(rs1_data_bypass) >>> rs2_data_bypass[4:0];
        end

        if (execute_state.is_or) begin
          rd_data = rs1_data_bypass | rs2_data_bypass;
        end

        if (execute_state.is_and) begin
          rd_data = rs1_data_bypass & rs2_data_bypass;
        end

        if (execute_state.is_mul) begin
          rd_data = $signed(rs1_data_bypass) * $signed(rs2_data_bypass);
        end

        if (execute_state.is_mulh) begin
          multiplication = $signed(rs1_data_bypass) * $signed(rs2_data_bypass);
          rd_data = multiplication[63:32];
        end

        if (execute_state.is_mulhsu) begin
          extended_rs1_data = $signed({{32{rs1_data_bypass[31]}}, rs1_data_bypass});
          extended_rs2_data = {32'd0, rs2_data_bypass};

          multiplication = extended_rs1_data * extended_rs2_data;
          rd_data = multiplication[63:32];
        end

        if (execute_state.is_mulhu) begin
          multiplication = $unsigned(rs1_data_bypass) * $unsigned(rs2_data_bypass);
          rd_data = multiplication[63:32];
        end

        if (execute_state.is_div) begin
          // Compute absolute values handling two's complement edge case
          abs_a = rs1_data_bypass[31] ? (~rs1_data_bypass + 1) : rs1_data_bypass;
          abs_b = rs2_data_bypass[31] ? (~rs2_data_bypass + 1) : rs2_data_bypass;

          // Assign absolute values for division
          divider_input_a = abs_a;
          divider_input_b = abs_b;

          // Stall for one cycle 
          stall_flag_bf_execute = 1'b1;
        end

        if (execute_state.is_divu) begin
          divider_input_a = rs1_data_bypass;
          divider_input_b = rs2_data_bypass;

          // Stall for one cycle 
          stall_flag_bf_execute = 1'b1;
        end

        if (execute_state.is_rem) begin
          // Compute absolute values handling two's complement edge case
          abs_a = rs1_data_bypass[31] ? (~rs1_data_bypass + 1) : rs1_data_bypass;
          abs_b = rs2_data_bypass[31] ? (~rs2_data_bypass + 1) : rs2_data_bypass;

          // Assign absolute values for division
          divider_input_a = abs_a;
          divider_input_b = abs_b;

          // Stall for one cycle 
          stall_flag_bf_execute = 1'b1;
        end

        if (execute_state.is_remu) begin
          if (rs2_data_bypass == 0) begin
            rd_data = rs1_data_bypass;
          end else begin
            divider_input_a = rs1_data_bypass;
            divider_input_b = rs2_data_bypass;

            // Stall for one cycle 
            stall_flag_bf_execute = 1'b1;
          end
        end
      end

      OpLoad: begin
        rd = execute_state.insn_rd;
        rs1 = execute_state.insn_rs1;
        write_enable = 1'b1;

        // Calculate effective address for memory access with alignement
        effective_addr = (rs1_data_bypass + $signed(execute_state.imm_i_sext)); 

        // Now check for dependent instructions in Decode to see if there is 
        if (insn_rs1 == rd || insn_rs2 == rd) begin

          // Edge case for the stall below
          if (insn_lui || insn_auipc || insn_jal) begin
            is_u_or_j = 1'b1;
          end

          if (insn_addi || insn_slti || insn_sltiu || insn_xori || insn_ori || insn_andi || insn_slli || insn_srli || insn_srai) begin
            is_i = 1'b1;
          end

          // Making sure we are not stalling for u or j
          if (!is_u_or_j) begin
            if (!is_i) begin
              stall_flag_bf_execute = 1'b1;
            end else if (is_i && insn_rs1 != rd) begin 
              stall_flag_bf_execute = 1'b1;
            end
          end
        end

        // All loading into memory occurs in the memory stage below
      end

      OpStore: begin
        effective_addr = rs1_data_bypass + $signed(execute_state.imm_s_sext);

        // All storing into memory occurs in the memory stage below
      end

      OpBranch: begin
        rs1 = execute_state.insn_rs1;
        rs2 = execute_state.insn_rs2;
        write_enable = 1'b0;

        if ((execute_state.is_beq && (rs1_data_bypass ==        rs2_data_bypass)) ||
          (execute_state.is_bne && (rs1_data_bypass != rs2_data_bypass)) ||
          (execute_state.is_blt && $signed(rs1_data_bypass) < $signed(rs2_data_bypass)) ||
          (execute_state.is_bge && $signed(rs1_data_bypass) >= $signed(rs2_data_bypass)) ||
          (execute_state.is_bltu && $unsigned(rs1_data_bypass) < $unsigned(rs2_data_bypass)) ||
          (execute_state.is_bgeu && $unsigned(rs1_data_bypass) >= $unsigned(rs2_data_bypass))) begin
          
          // Update PC to Next
          pc_temp = execute_state.pc + (execute_state.imm_b_sext);

          // Flag to update to NOP
          flag_taken = 1'b1;
        end
      end

      OpEnviron: begin
        if (execute_state.is_ecall) begin
          halt_e = 1'b1;
        end
      end

      OpMiscMem: begin
        if (execute_state.is_fence) begin
          // Encoding NOP as ADDI with immediate of zero (doing nothing) 
          inputaCLA32 = 32'b0;
          inputbCLA32 = 32'b0;
          alu_flag1 = 1'b1;

          // if we have a store in memory.store
          if (memory_state.store)
        end
      end

      default: begin
        illegal_insn = 1'b1;
      end
    endcase 
  end

  logic is_b_or_s;

  always_comb begin
    // Decoding
    is_b_or_s = 1'b0;

    if (insn_beq || insn_bne || insn_blt || insn_bge || insn_bltu || insn_bgeu || insn_sb || insn_sh || insn_sw) begin
      is_b_or_s = 1'b1;
    end

    // WD Bypass
    rs1_data_decode = rs1_data_out;
    rs2_data_decode = rs2_data_out;

    if (writeback_state.rd == insn_rs1) begin
      rs1_data_decode = writeback_state.rd_data;
      if (insn_rs1 == 0) rs1_data_decode = 0;
    end 
    
    if (writeback_state.rd == insn_rs2) begin
      rs2_data_decode = writeback_state.rd_data;
      if (insn_rs2 == 0) rs2_data_decode = 0;
    end
  end

  // Our CLA
  cla cla_instance(
      .a(inputaCLA32), 
      .b(inputbCLA32), 
      .cin(adder_carry_in), 
      .sum(cla_sum)
  );

  /****************/
  /* MEMORY STAGE*/
  /****************/
  // Memory stage wires
  // wire [`REG_SIZE] inputbCLA32_mem;
  // wire [`INSN_SIZE] insn_mem;
  // wire [`REG_SIZE] rd_data_mem;
  // wire [4:0] rd_mem;
  // wire [4:0] rs1_mem, rs2_mem;
  // wire [`REG_SIZE] rs1_data_mem, rs2_data_mem;
  // wire write_enable_mem;
  // wire reset_mem;
  // wire illegal_insn_mem;

  // Memory stage
  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
        pc: 0,
        insn: 0,
        rd_data: 0,
        rd: 0,
        rs1: 0,
        rs2: 0,
        rs1_data: 0,
        rs2_data: 0,
        effective_addr: 0,
        write_enable: 0,
        reset: 0,
        illegal_insn: 0,
        cycle_status: CYCLE_RESET,
        halt: 0,
        insn_opcode: 0,
        is_lb: 0,
        is_lh: 0,
        is_lw: 0,
        is_lbu: 0,
        is_lhu: 0,
        is_sb: 0,
        is_sh: 0,
        is_sw: 0,
        is_div: 0,
        is_divu: 0,
        is_rem: 0, is_remu: 0
      };
    end else begin
      memory_state <= '{
        pc: execute_state.pc,
        insn: execute_state.insn,
        rd_data: alu_flag1 ? alu_value : rd_data,
        rd: execute_state.insn_rd,
        rs1: execute_state.insn_rs1,
        rs2: execute_state.insn_rs2,
        rs1_data: rs1_data_bypass,
        rs2_data: rs2_data_bypass,
        effective_addr: effective_addr,
        write_enable: write_enable,
        reset: reset,
        illegal_insn: illegal_insn,
        cycle_status: execute_state.cycle_status,
        halt: halt_e,
        insn_opcode: execute_state.insn_opcode,
        is_lb: execute_state.is_lb,
        is_lh: execute_state.is_lh,
        is_lw: execute_state.is_lw,
        is_lbu: execute_state.is_lbu,
        is_lhu: execute_state.is_lhu,
        is_sb: execute_state.is_sb,
        is_sh: execute_state.is_sh,
        is_sw: execute_state.is_sw,
        is_div: execute_state.is_div,
        is_divu: execute_state.is_divu,
        is_rem: execute_state.is_rem, is_remu: execute_state.is_remu
      };
    end
  end

  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_3memory (
      .insn  (memory_state.insn),
      .rd   (memory_state.rd),
      .rs1  (memory_state.rs1),
      .rs2  (memory_state.rs2),
      .rd_data   (memory_state.rd_data),
      .rs1_data  (memory_state.rs1_data),
      .rs2_data  (memory_state.rs2_data),
      .alu_value  (32'b0),
      .flag  (flag),
      .flag2  (flag2),
      .disasm(m_disasm)
  );

  // Logic read from memory state
  logic [`REG_SIZE] rs1_data_memory, rs2_data_memory, rd_data_memory;
  logic [1:0] lowest_bits_memory_access;

  always_comb begin
    rs1_data_memory = memory_state.rs1_data;
    rs2_data_memory = memory_state.rs2_data;
    rd_data_memory = memory_state.rd_data;

    // For divider
    sign_result = 1'b0;

    // Initialize memory
    lowest_bits_memory_access = 2'b0;
    // store_data_to_dmem = 32'b0;
    store_we_to_dmem = 4'b0;
    addr_to_dmem = 32'b0;
    
    // WM Bypassing
    if (writeback_state.rd == memory_state.rs2) begin
      rs2_data_memory = writeback_state.rd_data;
      if (memory_state.rs2 == 0) rs2_data_memory = 0;
    end

    // Loading and storing instructions
    if (memory_state.insn_opcode == OpLoad) begin
        // Memory address
        lowest_bits_memory_access = memory_state.effective_addr[1:0]; 
        addr_to_dmem = memory_state.effective_addr & ~32'h3; 

        if (memory_state.is_lb || memory_state.is_lbu) begin
          case (lowest_bits_memory_access)
            2'b00: rd_data_memory = memory_state.is_lb ? {{24{load_data_from_dmem[7]}}, load_data_from_dmem[7:0]} : {{24{1'b0}}, load_data_from_dmem[7:0]};
            
            2'b01: rd_data_memory = memory_state.is_lb ? {{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]} : {{24{1'b0}}, load_data_from_dmem[15:8]};
            
            2'b10: rd_data_memory = memory_state.is_lb ? {{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]} : {{24{1'b0}}, load_data_from_dmem[23:16]};
            
            2'b11: rd_data_memory = memory_state.is_lb ? {{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]} : {{24{1'b0}}, load_data_from_dmem[31:24]};
          endcase
        end

        if (memory_state.is_lh || memory_state.is_lhu) begin
          case (lowest_bits_memory_access[1])
            1'b0: rd_data_memory = memory_state.is_lh ? {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]} : {{16{1'b0}}, load_data_from_dmem[15:0]};
            1'b1: rd_data_memory = memory_state.is_lh ? {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]} : {{16{1'b0}}, load_data_from_dmem[31:16]};
          endcase
        end

        if (memory_state.is_lw) begin
          rd_data_memory = load_data_from_dmem;
        end

    end else if (memory_state.insn_opcode == OpStore) begin
        lowest_bits_memory_access = memory_state.effective_addr[1:0]; 

        if (memory_state.is_sb) begin
          store_data_to_dmem = rs2_data_memory << (8 * lowest_bits_memory_access);
          store_we_to_dmem = 4'b0001 << lowest_bits_memory_access;
          addr_to_dmem = memory_state.effective_addr & ~32'h3;
        end
        if (memory_state.is_sh) begin
          if (lowest_bits_memory_access[1] == 1) begin
            store_data_to_dmem = rs2_data_memory << 16;
            store_we_to_dmem = 4'b1100;
          end 

          if (lowest_bits_memory_access[1] == 0) begin
            store_data_to_dmem = rs2_data_memory;
            store_we_to_dmem = 4'b0011;
          end
          
          addr_to_dmem = memory_state.effective_addr & ~32'h3;
        end
        if (memory_state.is_sw) begin
          store_data_to_dmem = rs2_data_memory;
          store_we_to_dmem = 4'b1111;
          addr_to_dmem = memory_state.effective_addr;
        end
    end else if (memory_state.insn_opcode == OpRegReg) begin
        if (memory_state.is_div) begin
          sign_result = (memory_state.rs1_data[31] != memory_state.rs2_data[31]); 

          if (sign_result) begin
            rd_data_memory = ((~divider_quotient) + (1'b1 * (|(~divider_quotient))) + (&divider_quotient * ({32{1'b1}})));
          end else begin
            rd_data_memory = divider_quotient;
          end
        end

        if (memory_state.is_divu) begin
          rd_data_memory = divider_quotient;   
        end

        if (memory_state.is_rem) begin
          sign_result = memory_state.rs1_data[31]; 

          // Sign result
          if (sign_result) begin
            rd_data_memory = ((~divider_remainder) + 1'b1);
          end else begin
            rd_data_memory = divider_remainder;
          end
        end

        if (memory_state.is_remu) begin
          if (memory_state.rs2_data != 0) begin
            rd_data_memory = divider_remainder;
          end
        end
    end
  end

  /****************/
  /*WRITEBACK STAGE*/
  /****************/
  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{
        // inputbCLA32: 0,
        pc: 0,
        insn: 0,
        rd_data: 0,
        rd: 0,
        rs1: 0,
        rs2: 0,
        rs1_data: 0,
        rs2_data: 0,
        write_enable: 0,
        reset: 0,
        illegal_insn: 0,
        cycle_status: CYCLE_RESET,
        halt: 0
      };
    end else begin
      writeback_state <= '{
        // inputbCLA32: memory_state.inputbCLA32,
        pc: memory_state.pc,
        insn: memory_state.insn,
        rd_data: rd_data_memory,
        rd: memory_state.rd,
        rs1: memory_state.rs1,
        rs2: memory_state.rs2,
        rs1_data: rs1_data_memory,
        rs2_data: rs2_data_memory,
        write_enable: memory_state.write_enable,
        reset: memory_state.reset,
        illegal_insn: memory_state.illegal_insn,
        cycle_status: memory_state.cycle_status,
        halt: memory_state.halt
      };
    end
  end

  assign trace_writeback_pc = writeback_state.pc;
  assign trace_writeback_insn = writeback_state.insn;
  assign trace_writeback_cycle_status = writeback_state.cycle_status;
  assign halt = writeback_state.halt;

  wire [255:0] w_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_4write (
      .insn  (writeback_state.insn),
      .rd   (writeback_state.rd),
      .rs1  (writeback_state.rs1),
      .rs2  (writeback_state.rs2),
      .rd_data   (writeback_state.rd_data),
      .rs1_data  (writeback_state.rs1_data),
      .rs2_data  (writeback_state.rs2_data),
      .alu_value  (32'b0),
      .flag  (flag),
      .flag2  (flag2),
      .disasm(w_disasm)
  );

  // Register file to output to writeback and read into rs1
  RegFile rf (
    .rd(writeback_state.rd),
    .rd_data(writeback_state.rd_data),
    .rs1(insn_rs1),
    .rs1_data(rs1_data_out),
    .rs2(insn_rs2),
    .rs2_data(rs2_data_out),
    .clk(clk),
    .we(writeback_state.write_enable),
    .rst(rst)
  );
endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem[NUM_WORDS];

  initial begin
    $readmemh("mem_initial_contents.hex", mem, 0);
  end

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/* This design has just one clock for both processor and memory. */
module RiscvProcessor (
    input  wire  clk,
    input  wire  rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) the_mem (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
