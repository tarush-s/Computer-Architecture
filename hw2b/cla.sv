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

   assign gout = (| gin);
   assign pout = (& pin);

   assign cout[0] = (gin[0] | (pin[0] & cin));
   assign cout[1] = (gin[1] | pin[1] & ((gin[0] | (pin[0] & cin))));
   assign cout[2] = (gin[2] | pin[2] & ((gin[1] | pin[1] & ((gin[0] | (pin[0] & cin))))));

endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   // TODO: your code here
   assign gout = (| gin);
   assign pout = (& pin);

   assign cout[0] = (gin[0] | (pin[0] & cin));
   assign cout[1] = (gin[1] | pin[1] & (gin[0] | (pin[0] & cin)));
   assign cout[2] = (gin[2] | pin[2] & (gin[1] | pin[1] & ((gin[0] | (pin[0] & cin)))));
   assign cout[3] = (gin[3] | pin[3] & (gin[2] | pin[2] & ((gin[1] | pin[1] & ((gin[0] | (pin[0] & cin)))))));
   assign cout[4] = (gin[4] | pin[4] & (gin[3] | pin[3] & (gin[2] | pin[2] & ((gin[1] | pin[1] & ((gin[0] | (pin[0] & cin))))))));
   assign cout[5] = (gin[5] | pin[5] & (gin[4] | pin[4] & (gin[3] | pin[3] & (gin[2] | pin[2] & ((gin[1] | pin[1] & ((gin[0] | (pin[0] & cin)))))))));
   assign cout[6] = (gin[6] | pin[6] & (gin[5] | pin[5] & (gin[4] | pin[4] & (gin[3] | pin[3] & (gin[2] | pin[2] & ((gin[1] | pin[1] & ((gin[0] | (pin[0] & cin))))))))));

endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

   // TODO: your code here
   wire [31:0] g ;
   wire [31:0] p;
   wire [30:0] cout;
   wire [4:0] gout;
   wire [4:0] pout;
   logic [31:0] sum_temp;
   genvar i; 

   generate
      for(i = 0; i < 32; i = i +1) begin : gandpvals
         gp1 h1(.a(a[i]),
               .b(b[i]), 
               .g(g[i]),
               .p(p[i]));
      end : gandpvals
   endgenerate 

   gp8 b1 (.gin(g[7:0]),
            .pin(p[7:0]),
            .cin(cin),
            .gout(gout[0]),
            .pout(pout[0]),
            .cout(cout[6:0]));

   gp8 b2 (.gin(g[14:7]),
            .pin(p[14:7]),
            .cin(cout[6]),
            .gout(gout[1]),
            .pout(pout[1]),
            .cout(cout[13:7]));

   gp8 b3 (.gin(g[21:14]),
            .pin(p[21:14]),
            .cin(cout[13]),
            .gout(gout[2]),
            .pout(pout[2]),
            .cout(cout[20:14]));

   gp8 b4 (.gin(g[28:21]),
            .pin(p[28:21]),
            .cin(cout[20]),
            .gout(gout[3]),
            .pout(pout[3]),
            .cout(cout[27:21]));

   gp4 a1 (.gin(g[31:28]),
            .pin(p[31:28]),
            .cin(cout[27]),
            .gout(gout[4]),
            .pout(pout[4]),
            .cout(cout[30:28]));
 
   always @(a or b) begin
   integer j;
      for(j = 0; j < 32; j = j + 1) begin : calcsum32
         if(j == 0) begin : takecin
            sum_temp[j] <= a[j] ^ b[j] ^ cin;
         end : takecin
         else begin : takecout
            sum_temp[j] <= a[j] ^ b[j] ^ cout[j-1];
         end : takecout
      end : calcsum32  
   end   

   assign sum = sum_temp;
endmodule
