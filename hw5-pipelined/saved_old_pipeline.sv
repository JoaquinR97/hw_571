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

    // Writeback inputs
    input logic [4:0] wb_rd, 
    input logic [`REG_SIZE] wb_data,
    input logic wb_we,

    input logic clk,
    input logic we,
    input logic rst
);
  localparam int NumRegs = 32;
  genvar i;
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here
  assign regs[0] = 32'd0; // x0 is always zero

  // // Logic to determine if we are in a writeback stage
  always_ff @(posedge clk) begin
    rs1_data <= (rs1 == wb_rd && wb_we) ? wb_data : regs[rs1];
    rs2_data <= (rs2 == wb_rd && wb_we) ? wb_data : regs[rs2];
  end

  // Update data
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
  // logic [`REG_SIZE] pc;

  // Instruction data passed from instruction to instruction
  logic [`REG_SIZE] rd_data; // Data to be written to the destination register
  logic [4:0] rd; // Destination register address
  logic [4:0] rs1, rs2; // Source register addresses
  logic [`REG_SIZE] rs1_data, rs2_data; // Data read from the source registers
  logic write_enable; // Write enable signal
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
  logic is_lui, is_auipc, is_jal, is_jalr;
  logic is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu;
  logic is_lb, is_lh, is_lw, is_lbu, is_lhu;
  logic is_sb, is_sh, is_sw;
  logic is_addi, is_slti, is_sltiu, is_xori, is_ori, is_andi;
  logic is_slli, is_srli, is_srai;
  logic is_add, is_sub, is_sll, is_slt, is_sltu, is_xor, is_srl, is_sra, is_or, is_and;
  logic is_mul, is_mulh, is_mulhsu, is_mulhu, is_div, is_divu, is_rem, is_remu;
  logic is_ecall, is_fence;

  // logic [`REG_SIZE] alu_result;
  // logic [`REG_SIZE] mem_data;
  // logic [4:0] rd_scr_1;
  // logic [4:0] rd_scr_2;
  // logic [4:0] rd_dest;
  // logic we;
} pipeline_registers_t;

pipeline_registers_t fd_reg; // Holds state between Fetch and Decode stages
pipeline_registers_t dx_reg; // Holds state between Decode and Execute stages
pipeline_registers_t xm_reg; // Holds state between Execute and Memory stages
pipeline_registers_t mw_reg; // Holds state between Memory and Writeback stages
pipeline_registers_t w_reg; // Holds state after writeback stage (to write to registers after clock cycle)

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

// Function to decode the instruction
function void decode_instruction(
    logic [`INSN_SIZE] insn,
    ref pipeline_registers_t decoded_values
);
    decoded_values.rd_data = 32'b0;
    decoded_values.rd = 5'd0;
    decoded_values.rs1 = 5'd0;
    decoded_values.rs2 = 5'd0;
    decoded_values.rs1_data = 32'b0;
    decoded_values.rs2_data = 32'b0;
    decoded_values.write_enable = 1'b0;
    decoded_values.reset = 1'b0;
    decoded_values.illegal_insn = 1'b0;

    // Storing full instruction in decode struct
    decoded_values.insn_from_imem = insn;

    // Decode R-type instruction components
    decoded_values.insn_funct7 = insn[31:25];
    decoded_values.insn_rs2 = insn[24:20];
    decoded_values.insn_rs1 = insn[19:15];
    decoded_values.insn_funct3 = insn[14:12];
    decoded_values.insn_rd = insn[11:7];
    decoded_values.insn_opcode = insn[6:0];
    
    // Depending on your design, you may include additional decoding logic here
    decoded_values.imm_i = insn[31:20];
    decoded_values.imm_s = {insn[31:25], insn[11:7]};
    decoded_values.imm_b = {insn[31], insn[7], insn[30:25], insn[11:8], 1'b0};
    decoded_values.imm_j = {insn[31], insn[19:12], insn[20], insn[30:21], 1'b0};

    // Sign-extend the immediate values
    decoded_values.imm_i_sext = {{20{decoded_values.imm_i[11]}}, decoded_values.imm_i};
    decoded_values.imm_s_sext = {{20{decoded_values.imm_s[11]}}, decoded_values.imm_s};
    decoded_values.imm_b_sext = {{19{decoded_values.imm_b[12]}}, decoded_values.imm_b};
    decoded_values.imm_j_sext = {{11{decoded_values.imm_j[20]}}, decoded_values.imm_j};

    // insn[6:0] is the instruction opcode
    decoded_values.is_lui = insn[6:0] == OpLui;
    decoded_values.is_auipc = insn[6:0] == OpAuipc;
    decoded_values.is_jal = insn[6:0] == OpJal;
    decoded_values.is_jalr = insn[6:0] == OpJalr;

    // Branch instructions
    decoded_values.is_beq = (insn[6:0] == OpBranch) && (insn[14:12] == 3'b000);
    decoded_values.is_bne = (insn[6:0] == OpBranch) && (insn[14:12] == 3'b001);
    decoded_values.is_blt = (insn[6:0] == OpBranch) && (insn[14:12] == 3'b100);
    decoded_values.is_bge = (insn[6:0] == OpBranch) && (insn[14:12] == 3'b101);
    decoded_values.is_bltu = (insn[6:0] == OpBranch) && (insn[14:12] == 3'b110);
    decoded_values.is_bgeu = (insn[6:0] == OpBranch) && (insn[14:12] == 3'b111);

    // Load instructions 
    decoded_values.is_lb = (insn[6:0] == OpLoad) && (insn[14:12] == 3'b000);
    decoded_values.is_lh = (insn[6:0] == OpLoad) && (insn[14:12] == 3'b001);
    decoded_values.is_lw = (insn[6:0] == OpLoad) && (insn[14:12] == 3'b010);
    decoded_values.is_lbu = (insn[6:0] == OpLoad) && (insn[14:12] == 3'b100);
    decoded_values.is_lhu = (insn[6:0] == OpLoad) && (insn[14:12] == 3'b101);

    // Store instructions
    decoded_values.is_sb = (insn[6:0] == OpStore) && (insn[14:12] == 3'b000);
    decoded_values.is_sh = (insn[6:0] == OpStore) && (insn[14:12] == 3'b001);
    decoded_values.is_sw = (insn[6:0] == OpStore) && (insn[14:12] == 3'b010);

    // Immediate instructions continued
    decoded_values.is_addi = (insn[6:0] == OpRegImm) && (insn[14:12] == 3'b000);
    decoded_values.is_slti = (insn[6:0] == OpRegImm) && (insn[14:12] == 3'b010);
    decoded_values.is_sltiu = (insn[6:0] == OpRegImm) && (insn[14:12] == 3'b011);
    decoded_values.is_xori = (insn[6:0] == OpRegImm) && (insn[14:12] == 3'b100);
    decoded_values.is_ori = (insn[6:0] == OpRegImm) && (insn[14:12] == 3'b110);
    decoded_values.is_andi = (insn[6:0] == OpRegImm) && (insn[14:12] == 3'b111);

    // Shift Immediate instructions
    decoded_values.is_slli = (insn[6:0] == OpRegImm) && (insn[14:12] == 3'b001) && (insn[31:25] == 7'd0);
    decoded_values.is_srli = (insn[6:0] == OpRegImm) && (insn[14:12] == 3'b101) && (insn[31:25] == 7'd0);
    decoded_values.is_srai = (insn[6:0] == OpRegImm) && (insn[14:12] == 3'b101) && (insn[31:25] == 7'b0100000);

    // R-type arithmetic instructions
    decoded_values.is_add = (insn[6:0] == OpRegReg) && (insn[14:12] == 3'b000) && (insn[31:25] == 7'd0);
    decoded_values.is_sub = (insn[6:0] == OpRegReg) && (insn[14:12] == 3'b000) && (insn[31:25] == 7'b0100000);
    decoded_values.is_sll = (insn[6:0] == OpRegReg) && (insn[14:12] == 3'b001) && (insn[31:25] == 7'd0);
    decoded_values.is_slt = (insn[6:0] == OpRegReg) && (insn[14:12] == 3'b010) && (insn[31:25] == 7'd0);
    decoded_values.is_sltu = (insn[6:0] == OpRegReg) && (insn[14:12] == 3'b011) && (insn[31:25] == 7'd0);
    decoded_values.is_xor = (insn[6:0] == OpRegReg) && (insn[14:12] == 3'b100) && (insn[31:25] == 7'd0);
    decoded_values.is_srl = (insn[6:0] == OpRegReg) && (insn[14:12] == 3'b101) && (insn[31:25] == 7'd0);
    decoded_values.is_sra = (insn[6:0] == OpRegReg) && (insn[14:12] == 3'b101) && (insn[31:25] == 7'b0100000);
    decoded_values.is_or = (insn[6:0] == OpRegReg) && (insn[14:12] == 3'b110) && (insn[31:25] == 7'd0);
    decoded_values.is_and = (insn[6:0] == OpRegReg) && (insn[14:12] == 3'b111) && (insn[31:25] == 7'd0);

    // Multiplication and division instructions
    decoded_values.is_mul = (insn[6:0] == OpRegReg) && (insn[31:25] == 7'd1) && (insn[14:12] == 3'b000);
    decoded_values.is_mulh = (insn[6:0] == OpRegReg) && (insn[31:25] == 7'd1) && (insn[14:12] == 3'b001);
    decoded_values.is_mulhsu = (insn[6:0] == OpRegReg) && (insn[31:25] == 7'd1) && (insn[14:12] == 3'b010);
    decoded_values.is_mulhu = (insn[6:0] == OpRegReg) && (insn[31:25] == 7'd1) && (insn[14:12] == 3'b011);
    decoded_values.is_div = (insn[6:0] == OpRegReg) && (insn[31:25] == 7'd1) && (insn[14:12] == 3'b100);
    decoded_values.is_divu = (insn[6:0] == OpRegReg) && (insn[31:25] == 7'd1) && (insn[14:12] == 3'b101);
    decoded_values.is_rem = (insn[6:0] == OpRegReg) && (insn[31:25] == 7'd1) && (insn[14:12] == 3'b110);
    decoded_values.is_remu = (insn[6:0] == OpRegReg) && (insn[31:25] == 7'd1) && (insn[14:12] == 3'b111);

    // System instructions
    decoded_values.is_ecall = (insn[6:0] == OpEnviron) && (insn[31:7] == 25'd0);
    decoded_values.is_fence = (insn[6:0] == OpMiscMem);

endfunction

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_decode_t;


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
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm()
  );

  /****************/
  /* DECODE STAGE */
  /****************/
  logic [`INSN_SIZE] logic_insn_from_imem;

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };

      // Set all input reg bits to zero
      // fd_reg <= '0;
      // dx_reg <= '0;
      // xm_reg <= '0;
      // mw_reg <= '0;

      // decode_instruction(32'b0, fd_reg);
      // decode_instruction(32'b0, dx_reg);
      // decode_instruction(32'b0, xm_reg);
      // decode_instruction(32'b0, mw_reg);
      // decode_instruction(32'b0, w_reg);
    end else begin
        // Save incoming instruction at clock edge
        logic_insn_from_imem <= insn_from_imem;

        decode_state <= '{
          pc: f_pc_current,
          insn: f_insn,
          cycle_status: f_cycle_status
        };

        // Updating next regs as we loop
        decode_instruction(logic_insn_from_imem, fd_reg);

        xm_reg.rd_data <= next_xm_rd_data; // Use non-blocking assignment here
        xm_reg.rd <= next_xm_rd; // Use non-blocking assignment here
        xm_reg.write_enable <= next_xm_write_enable; // Use non-blocking assignment here

        // Propagating down (the previous fd_reg is decoded down)
        dx_reg <= fd_reg;
        xm_reg <= dx_reg;
        mw_reg <= xm_reg;
        w_reg <= mw_reg;

        // case (xm_reg.insn_opcode)
        //     OpLui: begin
        //         if (xm_reg.is_lui) begin
        //             xm_reg.rd_data <= {dx_reg.insn_from_imem[31:12], 12'b0}; 
        //             xm_reg.rd <= dx_reg.insn_rd; 
        //             xm_reg.write_enable <= 1'b1;
        //         end
        //     end
        //     // Add other cases as necessary, following the same pattern
        //     default: begin
        //         // Handle the default case, potentially a NOP or error handling
        //     end
        // endcase

    end
  end

  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm()
  );

  // rf values
  // logic [`REG_SIZE] rd_data; // Data to be written to the destination register
  // logic [4:0] rd; // Destination register address
  // logic [4:0] rs1, rs2; // Source register addresses
  // logic [`REG_SIZE] rs1_data, rs2_data; // Data read from the source registers
  // logic write_enable; // Write enable signal
  // logic reset; // Reset signal
  // logic illegal_insn; // Reset signal

  logic [`REG_SIZE] inputbCLA32;
  logic [`REG_SIZE] cla_sum;
  logic adder_carry_in;
  
  // Register Inputs in Writeback Stage
  logic [4:0] wb_rd;
  logic [`REG_SIZE] wb_data;
  logic wb_we;

  // Our CLA
  // cla cla_instance(
  //     .a(rs1_data), 
  //     .b(inputbCLA32), 
  //     .cin(adder_carry_in), 
  //     .sum(cla_sum)
  // );

  logic [`REG_SIZE] next_xm_rd_data;
  logic [4:0] next_xm_rd;
  logic next_xm_write_enable;

  // Declaration of intermediate signals
  logic [4:0] rf_rd, rf_rs1, rf_rs2, rf_wb_rd;
  logic [`REG_SIZE] rf_rd_data, rf_rs1_data, rf_rs2_data, rf_wb_data;
  logic rf_wb_we, rf_we, rf_rst;

  always_comb begin
    // write_enable = 1'b0;
    // reset = 1'b0;
    // illegal_insn = 0'b0;

    // rd = 5'b0; // Default to an invalid register address
    // rs1 = 5'b0;
    // rs2 = 5'b0

    adder_carry_in = 1'b0;
    inputbCLA32 = 32'b0;

    // Writeback stage inputs
    wb_rd = 5'b0;
    wb_data = 32'b0;
    wb_we = 1'b0;
  
    // Execute stage
    case (xm_reg.insn_opcode)
      OpLui: begin
        if (xm_reg.is_lui) begin
          // rd = insn_rd; // RD field
          // write_enable = 1'b1;
          // rd_data = {insn_from_imem[31:12], 12'b0}; // Immediate shifted left

          // // Since LUI is a simple operation, it could technically be 'executed' right here,
          // // by preparing its result for the next stage.
          next_xm_rd_data = {dx_reg.insn_from_imem[31:12], 12'b0}; // Constructing the value to load into the register.
          next_xm_rd = dx_reg.insn_rd; // Passing along the destination register.
          next_xm_write_enable = 1'b1; // Enabling write for the next stage.
        end
      end
      
      // OpRegReg: begin
      //   // Adding the 

      //   rs1 = insn_rs1;
      //   rs2 = insn_rs2;
      //   rd = insn_rd;
      //   write_enable = 1'b1;

      //   if (insn_add) begin
      //     if () begin
      //       // This is already set to zero above
      //       wb_we = 1'b1;
      //       wb_rd;
      //       wb_data
      //     end
      //     inputbCLA32 = rs2_data;
      //     rd_data = cla_sum;
      //   end
      // end

      // OpRegImm: begin
      //   write_enable = 1'b1;
      //   rd = insn_rd; 
      //   rs1 = insn_rs1;

      //   if (insn_addi) begin
      //     inputbCLA32 = imm_i_sext;
      //     rd_data = cla_sum;
      //   end
      // end
    
      default: begin
        // illegal_insn = 1'b1;
      end
    endcase

    rf_rd = 0;
    rf_rd_data = 0;
    rf_rs1 = 0;
    rf_rs1_data = 0;
    rf_rs2 = 0;
    rf_rs2_data = 0;
    rf_wb_rd = 0;
    rf_wb_data = 0;
    rf_wb_we = 0;
    rf_we = 0;
    rf_rst = 0;

    // Update intermediate signals based on pipeline logic
    rf_rd = w_reg.rd;
    rf_rd_data = w_reg.rd_data;
    rf_rs1 = w_reg.rs1;
    rf_rs1_data = w_reg.rs1_data;
    rf_rs2 = w_reg.rs2;
    rf_rs2_data = w_reg.rs2_data;
    rf_wb_rd = wb_rd; // Assuming wb_rd, wb_data, and wb_we are properly updated elsewhere
    rf_wb_data = wb_data;
    rf_wb_we = wb_we;
    rf_we = w_reg.write_enable;
    rf_rst = w_reg.reset;
  end

  // RegFile rf (
  //   .rd(w_reg.rd),
  //   .rd_data(w_reg.rd_data),
  //   .rs1(w_reg.rs1),
  //   .rs1_data(w_reg.rs1_data),
  //   .rs2(w_reg.rs2),
  //   .rs2_data(w_reg.rs2_data),
  //   .wb_rd(wb_rd),
  //   .wb_data(wb_data),
  //   .wb_we(wb_we),
  //   .clk(clk),
  //   .we(w_reg.write_enable),
  //   .rst(w_reg.reset)
  // );

  // Updating intermediate signals in always_ff block
  // always_ff @(posedge clk or posedge rst) begin
  //   if (rst) begin
  //     // Reset intermediate signals
  //     rf_rd = 0;
  //     rf_rd_data = 0;
  //     rf_rs1 = 0;
  //     rf_rs1_data = 0;
  //     rf_rs2 = 0;
  //     rf_rs2_data = 0;
  //     rf_wb_rd = 0;
  //     rf_wb_data = 0;
  //     rf_wb_we = 0;
  //     rf_we = 0;
  //     rf_rst = 0;

  //   end
  // end

  // Update register instruction by using w_reg logic
  RegFile rf (
      .rd(rf_rd),
      .rd_data(rf_rd_data),
      .rs1(rf_rs1),
      .rs1_data(rf_rs1_data),
      .rs2(rf_rs2),
      .rs2_data(rf_rs2_data),
      .wb_rd(rf_wb_rd),
      .wb_data(rf_wb_data),
      .wb_we(rf_wb_we),
      .clk(clk),
      .we(rf_we),
      .rst(rf_rst)
  );

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

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
  ) mem (
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
