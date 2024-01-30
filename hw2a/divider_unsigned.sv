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
reg [31:0] tmp_quotient;
reg [31:0] tmp_remainder;
reg [31:0] tmp_dividend;

always_comb begin 
    for(int i=0; i<32; i++) begin 
        if( i == 0) begin 
            tmp_quotient = i_quotient;
            tmp_remainder = i_remainder;
            tmp_dividend = i_dividend;
        end 
        tmp_remainder = (tmp_remainder << 1) | (tmp_dividend >> 31) & 32'b1;
        if(tmp_remainder < i_divisor) begin 
            tmp_quotient = (tmp_quotient << 1);
        end 
        else begin 
            tmp_quotient = (tmp_quotient << 1) | 32'b1; 
            tmp_remainder = tmp_remainder - i_divisor;
        end 
        tmp_dividend = tmp_dividend << 1;
    end 
end 

assign o_dividend = tmp_dividend;
assign o_quotient = tmp_quotient;
assign o_remainder = tmp_remainder;

endmodule
