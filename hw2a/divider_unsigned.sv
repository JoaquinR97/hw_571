/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here

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

    assign intermediate_remainder = (i_remainder << 1) | ((i_dividend >> 31) & 1'b1);

    assign new_quotient = intermediate_remainder < i_divisor ? i_quotient << 1 : (i_quotient << 1) | 1'b1;
    assign new_remainder = intermediate_remainder >= i_divisor ? intermediate_remainder - i_divisor : intermediate_remainder;

    assign o_dividend = i_dividend << 1;
    assign o_quotient = new_quotient;
    assign o_remainder = new_remainder;

endmodule
