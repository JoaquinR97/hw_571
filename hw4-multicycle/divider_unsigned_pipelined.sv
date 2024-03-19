`timescale 1ns / 1ns

module divider_unsigned_pipelined (
    input wire clk,
    input wire rst,
    input wire [31:0] i_dividend,
    input wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // Declare registers for pipeline stages
    logic [31:0] stage1_dividend[17];
    logic [31:0] stage1_remainder[17];
    logic [31:0] stage1_quotient[17];

    logic [31:0] stage1_dividend_output[17];
    logic [31:0] stage1_remainder_output[17];
    logic [31:0] stage1_quotient_output[17];

    // Add initial values for stage one
    assign stage1_dividend[0] = i_dividend;
    assign stage1_remainder[0] = 32'b0;
    assign stage1_quotient[0] = 32'b0;

    logic [31:0] stage2_dividend[17];
    logic [31:0] stage2_remainder[17];
    logic [31:0] stage2_quotient[17];

    logic [31:0] stage2_dividend_output[17];
    logic [31:0] stage2_remainder_output[17];
    logic [31:0] stage2_quotient_output[17];

    logic [31:0] divisor_temp;

    // Pipeline stage 1
    genvar i;
    generate
        for (i = 0; i < 16; i = i + 1) begin : stage1
            divu_1iter div_stage1_instance(
                .i_dividend(stage1_dividend[i]),
                .i_divisor(i_divisor),
                .i_remainder(stage1_remainder[i]),
                .i_quotient(stage1_quotient[i]),
                .o_dividend(stage1_dividend_output[i]),
                .o_remainder(stage1_remainder_output[i]),
                .o_quotient(stage1_quotient_output[i])
            );
            assign stage1_dividend[i + 1] = stage1_dividend_output[i];
            assign stage1_remainder[i + 1] = stage1_remainder_output[i];
            assign stage1_quotient[i + 1] = stage1_quotient_output[i];
        end
    endgenerate

    // Pipeline stage 2
    genvar j;
    generate
        for (j = 0; j < 16; j = j + 1) begin : stage2
            divu_1iter div_stage2_instance(
                .i_dividend(stage2_dividend[j]),
                .i_divisor(divisor_temp),
                .i_remainder(stage2_remainder[j]),
                .i_quotient(stage2_quotient[j]),
                .o_dividend(stage2_dividend_output[j]),
                .o_remainder(stage2_remainder_output[j]),
                .o_quotient(stage2_quotient_output[j])
            );

            assign stage2_dividend[j + 1] = stage2_dividend_output[j];
            assign stage2_remainder[j + 1] = stage2_remainder_output[j];
            assign stage2_quotient[j + 1] = stage2_quotient_output[j];
        end
    endgenerate

    // integer k;
    logic [31:0] stage2_dividend_intermediate;
    logic [31:0] stage2_remainder_intermediate;
    logic [31:0] stage2_quotient_intermediate;

    // Update registers at clock cycles
    always_ff @(posedge clk) begin
        if (rst) begin
            // Add reset logic
            /*for (k = 0; k <= 16; k = k + 1) begin
                stage1_dividend[k] <= 0;
                stage1_remainder[k] <= 0;
                stage1_quotient[k] <= 0;
            end */

            stage2_dividend_intermediate <= 0;
            stage2_remainder_intermediate <= 0;
            stage2_quotient_intermediate <= 0;
            divisor_temp <= 0;

        end else begin
            // First stage to second stage
            stage2_dividend_intermediate <= stage1_dividend_output[15];
            stage2_remainder_intermediate <= stage1_remainder_output[15];
            stage2_quotient_intermediate <= stage1_quotient_output[15];
            divisor_temp <= i_divisor;
        end
    end

    assign stage2_dividend[0] = stage2_dividend_intermediate;
    assign stage2_remainder[0] = stage2_remainder_intermediate;
    assign stage2_quotient[0] = stage2_quotient_intermediate;

    // Update output from the last completed second stage to output remainder and quotient
    assign o_remainder = stage2_remainder_output[15];
    assign o_quotient = stage2_quotient_output[15];
endmodule

module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient 
);
    wire [31:0] intermediate_remainder; 
    wire [31:0] new_quotient;
    wire [31:0] new_remainder;

    assign intermediate_remainder = (i_remainder << 1) | ((i_dividend >> 31) & 32'h00000001);

    assign new_quotient = intermediate_remainder < i_divisor ? i_quotient << 1 : (i_quotient << 1) | 32'h00000001;
    assign new_remainder = intermediate_remainder >= i_divisor ? intermediate_remainder - i_divisor : intermediate_remainder;

    assign o_dividend = i_dividend << 1;
    assign o_quotient = new_quotient;
    assign o_remainder = new_remainder;

endmodule
