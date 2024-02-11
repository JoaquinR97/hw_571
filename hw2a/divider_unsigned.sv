// Joaquin Revello 34033461

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input wire [31:0] i_dividend,
    input wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

// Declare wires that'll be used in the for loop
wire [31:0] dividend_wire[0:32]; // We have one extra loop for the output wire
wire [31:0] remainder_wire[0:32];
wire [31:0] quotient_wire[0:32];

// Initialize the first set of wires to the input
assign dividend_wire[0] = i_dividend;
assign remainder_wire[0] = 0;
assign quotient_wire[0] = 0; 

genvar i;
generate
    for (i = 0; i < 32; i = i + 1) begin : div_gen
        divu_1iter div_iteration_instance(
            .i_dividend(dividend_wire[i]),
            .i_divisor(i_divisor),
            .i_remainder(remainder_wire[i]),
            .i_quotient(quotient_wire[i]),
            .o_dividend(dividend_wire[i+1]),
            .o_remainder(remainder_wire[i+1]),
            .o_quotient(quotient_wire[i+1])
        );
    end
endgenerate

// Assign final output to last element of the wires
assign o_remainder = remainder_wire[32];
assign o_quotient = quotient_wire[32];

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
  /*
    for (int i = 0; i < 32; i++) {
        remainder = (remainder << 1) | ((dividend >> 31) & 0x1);
        if (remainder < divisor) {
            quotient = (quotient << 1);
        } else {
            quotient = (quotient << 1) | 0x1;
            remainder = remainder - divisor;
        }
        dividend = dividend << 1;
    }*/

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
