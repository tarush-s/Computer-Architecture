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
    
    always_comb 
    begin 
        for(int i = 0; i < 32; i = i + 1)
        begin
            i_remainder = (i_remainder << 1) | ((i_dividend >> 31) & 0x1);
            if(i_remainder < i_divisor)
                begin
                    i_quotient = i_quotient << 1;
                end
            else
                begin
                    i_quotient = (i_quotient << 1) | 0x1;
                    i_remainder = i_remainder - i_divisor;
                end
            i_dividend = i_dividend << 1;
        end 
    end 
    
    assign o_dividend = i_dividend;
    assign o_remainder = i_remainder;
    assign o_quotient = i_quotient;

endmodule
