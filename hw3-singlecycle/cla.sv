`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   // TODO: your code here

   // Carry signals
   wire c1, c2, c3;

   // Carry-out
   assign c1 = gin[0] | (pin[0] & cin);
   assign c2 = gin[1] | (pin[1] & c1);
   assign c3 = gin[2] | (pin[2] & c2);
   assign cout[0] = c1;
   assign cout[1] = c2;
   assign cout[2] = c3;

   // Group propagate and generate
   assign pout = pin[0] & pin[1] & pin[2] & pin[3];
   
   assign gout = gin[3] | (gin[2] & pin[3]) | (gin[1] & pin[2] & pin[3]) | (gin[0] & pin[1] & pin[2] & pin[3]);

endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   // TODO: your code here

   // Intermediate carry signals
   wire c1, c2, c3, c4, c5, c6, c7;

   // Carry-out calculations
   assign c1 = gin[0] | (pin[0] & cin);
   assign c2 = gin[1] | (pin[1] & c1);
   assign c3 = gin[2] | (pin[2] & c2);
   assign c4 = gin[3] | (pin[3] & c3);
   assign c5 = gin[4] | (pin[4] & c4);
   assign c6 = gin[5] | (pin[5] & c5);
   assign c7 = gin[6] | (pin[6] & c6);
   assign cout[0] = c1;
   assign cout[1] = c2;
   assign cout[2] = c3;
   assign cout[3] = c4;
   assign cout[4] = c5;
   assign cout[5] = c6;
   assign cout[6] = c7;

   // Overall group propagate and generate
   assign pout = &pin; 

   // Find gout   
   assign gout = gin[7] | 
              (gin[6] & pin[7]) | 
              (gin[5] & pin[6] & pin[7]) | 
              (gin[4] & (|pin[7:5])) | 
              (gin[3] & (|pin[7:4])) |
              (gin[2] & (|pin[7:3])) |
              (gin[1] & (|pin[7:2])) |
              (gin[0] & (|pin[7:1]));

endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

    wire [31:0] g, p, c; 
    assign c[0] = cin;

    // Create gp1 modules
    genvar i;
    generate
        for (i = 0; i < 32; i = i + 1) begin : gp1_loop_i
            gp1 gp1_inst(a[i], b[i], g[i], p[i]);
        end
    endgenerate

    // Create gp4 modules
    wire [7:0] g_4, p_4;

    genvar j;
    parameter int output_c_indices[8] = '{1, 5, 9, 13, 17, 21, 25, 29};

    generate
        for (j = 0; j < 8; j = j + 1) begin : gp4_loop_j
            gp4 gp4_inst(g[4*j +: 4], p[4*j +: 4], c[4*j], g_4[j], p_4[j], c[output_c_indices[j] +: 3]);
        end
    endgenerate


    // Create gp8 modules
    wire g_8, p_8;
    wire [6:0] cout_intermediate_8;
    gp8 gp8_inst(g_4, p_4, c[0], g_8, p_8, cout_intermediate_8);

    // Connect gp8 c outputs to c wire
    assign c[4] = cout_intermediate_8[0];
    assign c[8] = cout_intermediate_8[1];
    assign c[12] = cout_intermediate_8[2];
    assign c[16] = cout_intermediate_8[3];
    assign c[20] = cout_intermediate_8[4];
    assign c[24] = cout_intermediate_8[5];
    assign c[28] = cout_intermediate_8[6];

    // Find the final sum value
    genvar s;
    generate
        for (s = 0; s < 32; s = s + 1) begin : sum_loop_s
            assign sum[s] = a[s] ^ b[s] ^ c[s];
        end
    endgenerate

endmodule

