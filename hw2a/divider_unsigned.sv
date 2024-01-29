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
    }
    */
reg [31:0] remainder;
reg [31:0] quotient;
reg [31:0] dividend;

initial begin 
    dividend = i_dividend;
    remainder = i_remainder;
    quotient = i_quotient; 
end

always_comb begin 
    for(int i=0; i<32; i++) begin 
        remainder = (remainder << 1) | ((dividend >> 31) & 32'h0000_0001);
        if(remainder < i_divisor) begin 
            quotient = (quotient << 1);
        end 
        else begin 
            quotient = (quotient << 1) | 32'h0000_0001; 
            remainder = remainder - i_divisor;
        end 
        dividend = dividend << 1;
    end 
end 

assign o_dividend = dividend;
assign o_quotient = quotient;
assign o_remainder = remainder;

endmodule
