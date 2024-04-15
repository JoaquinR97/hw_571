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

  logic [`REG_SIZE] rd_data; // Data to be written to the destination register
  logic [4:0] rd; // Destination register address
  logic [4:0] rs1, rs2; // Source register addresses
  logic [`REG_SIZE] rs1_data, rs2_data; // Data read from the source registers
  logic write_enable; // Write enable signal
  logic [`REG_SIZE] alu_value;
  logic reset; // Reset signal
  logic illegal_insn; // Reset signal

  // Storing the instruction itself
  logic [`INSN_SIZE] insn_from_imem;

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
  // logic is_lui, is_auipc, is_jal, is_jalr;
  // logic is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu;
  // logic is_lb, is_lh, is_lw, is_lbu, is_lhu;
  // logic is_sb, is_sh, is_sw;
  // logic is_addi, is_slti, is_sltiu, is_xori, is_ori, is_andi;
  // logic is_slli, is_srli, is_srai;
  // logic is_add, is_sub, is_sll, is_slt, is_sltu, is_xor, is_srl, is_sra, is_or, is_and;
  // logic is_mul, is_mulh, is_mulhsu, is_mulhu, is_div, is_divu, is_rem, is_remu;
  // logic is_ecall, is_fence;
} stage_execute_t;

// Memory stage
typedef struct packed {
  // logic [`REG_SIZE] inputbCLA32;
  logic [`INSN_SIZE] insn;
  logic [`REG_SIZE] rd_data; // Data to be written to the destination register
  logic [4:0] rd; // Destination register address
  logic [4:0] rs1, rs2; // Source register addresses
  logic [`REG_SIZE] rs1_data, rs2_data; // Data read from the source registers
  logic write_enable; // Write enable signal
  logic [`REG_SIZE] alu_value;
  logic reset; // Reset signal
  logic illegal_insn; // Reset signal
  cycle_status_e cycle_status;
} stage_memory_t;

// Writeback stage
typedef struct packed {
  // logic [`REG_SIZE] inputbCLA32;
  logic [`INSN_SIZE] insn;
  logic [`REG_SIZE] rd_data; // Data to be written to the destination register
  logic [4:0] rd; // Destination register address
  logic [4:0] rs1, rs2; // Source register addresses
  logic [`REG_SIZE] rs1_data, rs2_data; // Data read from the source registers
  logic write_enable; // Write enable signal
  logic [`REG_SIZE] alu_value;
  logic reset; // Reset signal
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
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= f_pc_current + 4;
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

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
          pc: f_pc_current,
          insn: f_insn,
          cycle_status: f_cycle_status
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



  /****************/
  /* EXECUTE STAGE*/
  /****************/

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [ 4:0] imm_shamt = insn_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};

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

  wire insn_beq = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b000;
  wire insn_bne = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b001;
  wire insn_blt = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b100;
  wire insn_bge = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b111;

  wire insn_lb = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b000;
  wire insn_lh = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b001;
  wire insn_lw = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b010;

  wire insn_addi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b000;
  wire insn_slti = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b011;
  wire insn_xori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b100;
  wire insn_ori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b110;
  wire insn_andi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b111;

  wire insn_slli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_srli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_srai = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;

  wire insn_add = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'd0;
  wire insn_sub  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_sll = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_slt = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b010 && insn_from_imem[31:25] == 7'd0;
  wire insn_sltu = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b011 && insn_from_imem[31:25] == 7'd0;
  wire insn_xor = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b100 && insn_from_imem[31:25] == 7'd0;
  wire insn_srl = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_sra  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_or = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b110 && insn_from_imem[31:25] == 7'd0;
  wire insn_and = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b111 && insn_from_imem[31:25] == 7'd0;

  wire insn_mul    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b000;
  wire insn_mulh   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b001;
  wire insn_mulhsu = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b010;
  wire insn_mulhu  = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b011;
  wire insn_div    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b100;
  wire insn_divu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b101;
  wire insn_rem    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b110;
  wire insn_remu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b111;

  wire insn_ecall = insn_opcode == OpEnviron && insn_from_imem[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

  stage_execute_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        rd_data: 0,
        rd: 0,
        rs1: 0,
        rs2: 0,
        rs1_data: 0,
        rs2_data: 0,
        write_enable: 0,
        alu_value: 0,
        reset: 0,
        illegal_insn: 0,
        insn_from_imem: 0,
        insn_funct7: 0,
        insn_rs2: 0,
        insn_rs1: 0,
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
        imm_j_sext: 0
      }; 
    end else begin
      execute_state <= '{
        pc: decode_state.pc,
        insn: decode_state.insn,
        cycle_status: decode_state.cycle_status,
        rd_data: rd_data,
        rd: rd,
        rs1: rs1,
        rs2: rs2,
        rs1_data: rs1_data,
        rs2_data: rs2_data,
        write_enable: write_enable,
        alu_value: alu_value,
        reset: reset,
        illegal_insn: illegal_insn,
        insn_from_imem: insn_from_imem,
        insn_funct7: insn_funct7,
        insn_rs2: insn_rs2,
        insn_rs1: insn_rs1,
        insn_funct3: insn_funct3,
        insn_rd: insn_rd,
        insn_opcode: insn_opcode,
        imm_i: imm_i,
        imm_s: imm_s,
        imm_b: imm_b,
        imm_j: imm_j,
        imm_i_sext: imm_i_sext,
        imm_s_sext: imm_s_sext,
        imm_b_sext: imm_b_sext,
        imm_j_sext: imm_j_sext
      };
    end
  end

  wire [255:0] e_disasm;
  Disasm #(
      .PREFIX("E")
  ) disasm_2execute (
      .insn  (execute_state.insn),
      .rd  (execute_state.rd),
      .rs1  (execute_state.rs1),
      .rs2  (execute_state.rs2),
      .rd_data   (execute_state.rd_data),
      .rs1_data  (execute_state.rs1_data),
      .rs2_data  (execute_state.rs2_data),
      .alu_value  (execute_state.alu_value),
      .flag  (flag),
      .flag2  (flag2),
      .disasm(e_disasm)
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
        // inputbCLA32: 0,
        insn: 0,
        rd_data: 0,
        rd: 0,
        rs1: 0,
        rs2: 0,
        rs1_data: 0,
        rs2_data: 0,
        write_enable: 0,
        alu_value: 0,
        reset: 0,
        illegal_insn: 0,
        cycle_status: CYCLE_RESET
      };
    end else begin
      memory_state <= '{
        // inputbCLA32: inputbCLA32_mem,
        insn: execute_state.insn,
        rd_data: execute_state.rd_data,
        rd: execute_state.rd,
        rs1: execute_state.rs1,
        rs2: execute_state.rs2,
        rs1_data: execute_state.rs1_data,
        rs2_data: execute_state.rs2_data,
        write_enable: execute_state.write_enable,
        alu_value: execute_state.alu_value,
        reset: execute_state.reset,
        illegal_insn: execute_state.illegal_insn,
        cycle_status: execute_state.cycle_status
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
      .alu_value  (memory_state.alu_value),
      .flag  (flag),
      .flag2  (flag2),
      .disasm(m_disasm)
  );

  /****************/
  /* WRITEBACK STAGE*/
  /****************/
  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{
        // inputbCLA32: 0,
        insn: 0,
        rd_data: 0,
        rd: 0,
        rs1: 0,
        rs2: 0,
        rs1_data: 0,
        rs2_data: 0,
        alu_value: 0,
        write_enable: 0,
        reset: 0,
        illegal_insn: 0,
        cycle_status: CYCLE_RESET
      };
    end else begin
      writeback_state <= '{
        // inputbCLA32: memory_state.inputbCLA32,
        insn: memory_state.insn,
        rd_data: memory_state.rd_data,
        rd: memory_state.rd,
        rs1: memory_state.rs1,
        rs2: memory_state.rs2,
        rs1_data: memory_state.rs1_data,
        rs2_data: memory_state.rs2_data,
        write_enable: memory_state.write_enable,
        alu_value: memory_state.alu_value,
        reset: memory_state.reset,
        illegal_insn: memory_state.illegal_insn,
        cycle_status: memory_state.cycle_status
      };
    end
  end

  // For all the datapath logic
  logic illegal_insn;

  // rf values
  logic [`REG_SIZE] rd_data; // Data to be written to the destination register
  logic [`REG_SIZE] alu_value; // Alu value to then be written
  logic [4:0] rd; // Destination register address
  logic [4:0] rs1, rs2; // Source register addresses
  logic [`REG_SIZE] rs1_data, rs2_data; // Data read from the source registers
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

  always_comb begin
    rd_data = 32'b0;
    alu_value = cla_sum;
    rd = 5'b0; // Default to an invalid register address
    rs1 = 5'b0;
    rs2 = 5'b0;
    flag = 32'd1;
    flag2 = 32'd5;
    // flag2 = inputaCLA32;
    rs1_data_bypass = rs1_data;
    rs2_data_bypass = rs2_data;
    write_enable = 1'b0; // Default to not writing

    immediateShiftedLeft = 32'b0;
    inputaCLA32 = 32'b0;
    inputbCLA32 = 32'b0;
    // cla_sum = 32'b0; // Not needed as we are outputting this value
    adder_carry_in = 1'b0;

    reset = 1'b0;

    illegal_insn = 1'b0;

    // Execute stage operations
    case (insn_opcode)
      OpLui: begin
        if (insn_lui) begin
          rd_data = {insn_from_imem[31:12], 12'b0};
          rd = insn_rd;
          write_enable = 1'b1;
        end
      end

      OpRegImm: begin
        write_enable = 1'b1;
        rd = insn_rd; 
        rs1 = insn_rs1;

        if (insn_addi) begin
          inputaCLA32 = rs1_data;
          inputbCLA32 = imm_i_sext;
          rd_data = cla_sum;
        end
        
        if (insn_slti) begin
          rd_data = $signed(rs1_data) < $signed(imm_i_sext) ? 32'b1 : 32'b0;
        end
        
        // if (insn_sltiu) begin
        //   rd_data = $unsigned(rs1_data) < $unsigned(imm_i_sext) ? 32'b1 : 32'b0;
        // end
        
        // if (insn_xori) begin
        //   rd_data = rs1_data ^ imm_i_sext;
        // end

        // if (insn_ori) begin
        //   rd_data = rs1_data | imm_i_sext;
        // end

        // if (insn_andi) begin
        //   rd_data = rs1_data & imm_i_sext;
        // end

        // if (insn_slli) begin
        //   rd_data = rs1_data << imm_i[4:0];
        // end

        // if (insn_srli) begin
        //   rd_data = rs1_data >> imm_i[4:0];
        // end

        // if (insn_srai) begin
        //   rd_data = $signed(rs1_data) >>> imm_i[4:0];
        // end
      end


      OpRegReg: begin
        rd = insn_rd;
        rs1 = insn_rs1;
        rs2 = insn_rs2;
        write_enable = 1'b1;

        if (insn_add) begin
          inputaCLA32 = rs1_data;
          inputbCLA32 = rs2_data;
          rd_data = cla_sum;
        end

        // if (insn_sub) begin
        //   inputbCLA32 = ~rs2_data;  // two's compliment
        //   adder_carry_in = 1'b1;   // Set carry in to 1 for two's complement addition
        //   rd_data = cla_sum;
        // end

        // if (insn_sll) begin
        //   rd_data = rs1_data << rs2_data[4:0];
        // end

        // if (insn_slt) begin
        //   rd_data = $signed(rs1_data) < $signed(rs2_data) ? 32'b1 : 32'b0;
        // end

        // if (insn_sltu) begin
        //   rd_data = $unsigned(rs1_data) < $unsigned(rs2_data) ? 32'b1 : 32'b0;
        // end

        // if (insn_xor) begin
        //   rd_data = rs1_data ^ rs2_data;
        // end

        // if (insn_srl) begin
        //   rd_data = rs1_data >> rs2_data[4:0];
        // end

        // if (insn_sra) begin
        //   rd_data = $signed(rs1_data) >>> rs2_data[4:0];
        // end

        // if (insn_or) begin
        //   rd_data = rs1_data | rs2_data;
        // end

        // if (insn_and) begin
        //   rd_data = rs1_data & rs2_data;
        // end

        // if (insn_mul) begin
        //   rd_data = $signed(rs1_data) * $signed(rs2_data);
        // end

        // if (insn_mulh) begin
        //   multiplication = $signed(rs1_data) * $signed(rs2_data);
        //   rd_data = multiplication[63:32];
        // end

        // if (insn_mulhsu) begin
        //   extended_rs1_data = $signed({{32{rs1_data[31]}}, rs1_data});
        //   extended_rs2_data = {32'd0, rs2_data};

        //   multiplication = extended_rs1_data * extended_rs2_data;
        //   rd_data = multiplication[63:32];
        // end

        // if (insn_mulhu) begin
        //   multiplication = $unsigned(rs1_data) * $unsigned(rs2_data);
        //   rd_data = multiplication[63:32];
        // end

        // if (insn_div) begin
        //   logic sign_result = (rs1_data[31] != rs2_data[31]); 

        //   // Compute absolute values handling two's complement edge case
        //   abs_a = rs1_data[31] ? (~rs1_data + 1) : rs1_data;
        //   abs_b = rs2_data[31] ? (~rs2_data + 1) : rs2_data;

        //   // Assign absolute values for division
        //   divider_input_a = abs_a;
        //   divider_input_b = abs_b;

        //   if (sign_result) begin
        //     rd_data = ((~divider_quotient) + (1'b1 * (|(~divider_quotient))) + (&divider_quotient * ({32{1'b1}})));
        //   end else begin
        //     rd_data = divider_quotient;
        //   end
        // end

        // if (insn_divu) begin
        //   divider_input_a = rs1_data;
        //   divider_input_b = rs2_data;
        //   rd_data = divider_quotient;
        // end

        // if (insn_rem) begin
        //   logic sign_result = rs1_data[31]; 

        //   // Compute absolute values handling two's complement edge case
        //   abs_a = rs1_data[31] ? (~rs1_data + 1) : rs1_data;
        //   abs_b = rs2_data[31] ? (~rs2_data + 1) : rs2_data;

        //   // Assign absolute values for division
        //   divider_input_a = abs_a;
        //   divider_input_b = abs_b;

        //   if (sign_result) begin
        //     rd_data = ((~divider_remainder) + 1'b1);
        //   end else begin
        //     rd_data = divider_remainder;
        //   end
        // end

        // if (insn_remu) begin
        //   if (rs2_data == 0) begin
        //     rd_data = rs1_data;
        //   end else begin
        //     divider_input_a = rs1_data;
        //     divider_input_b = rs2_data;
        //     rd_data = divider_remainder;
        //   end
        // end
      end

      default: begin
        // illegal_insn = 1'b1;
      end
    endcase

    // MX Bypass
    if (execute_state.rs1 == memory_state.rd) begin
      inputaCLA32 = execute_state.alu_value;
    end else if (execute_state.rs2 == memory_state.rd) begin
      inputbCLA32 = execute_state.alu_value;
    end

    // WX Bypass
    if (execute_state.rs1 == writeback_state.rd) begin
      inputaCLA32 = writeback_state.alu_value;
    end else if (execute_state.rs2 == writeback_state.rd) begin
      inputbCLA32 = writeback_state.alu_value;
    end

    // WB Bypass
    if (writeback_state.rd == execute_state.rs1) begin
        inputaCLA32 = writeback_state.alu_value;
    end else if (writeback_state.rd == execute_state.rs2) begin
        inputbCLA32 = writeback_state.alu_value;
    end
  end

  

  // Our CLA
  cla cla_instance(
      .a(inputaCLA32), 
      .b(inputbCLA32), 
      .cin(adder_carry_in), 
      .sum(cla_sum)
  );

  RegFile rf (
    .rd(writeback_state.rd),
    .rd_data(writeback_state.rd_data),
    .rs1(writeback_state.rs1),
    .rs1_data(rs1_data),
    .rs2(writeback_state.rs2),
    .rs2_data(rs2_data),
    .clk(clk),
    .we(writeback_state.write_enable),
    .rst(writeback_state.reset)
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
