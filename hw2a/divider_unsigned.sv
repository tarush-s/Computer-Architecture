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
    reg [31:0] out_dividend;
    reg [31:0] out_remainder; 
    reg [31:0] out_quotient; 
    reg [31:0] comp_divisor;
    
    initial begin
        comp_divisor = i_divisor;
        out_remainder = (i_remainder << 1) | ((i_dividend >> 31) & 32'h0000_0001);
        if(out_remainder < comp_divisor)
            begin
                out_quotient = i_quotient << 1;
            end
        else
            begin
                out_quotient = (i_quotient << 1) | {1'b1, {31{1'b0}}};
                out_remainder = i_remainder - comp_divisor;
            end
        out_dividend = i_dividend << 1;
    end

    always_comb begin
        for(int i = 1; i < 32; i = i + 1)
        begin
            out_remainder = (out_remainder << 1) | ((out_dividend >> 31) & 32'h0000_0001);
            if(out_remainder < comp_divisor)
                begin
                    out_quotient = (out_quotient << 1);
                end
            else
                begin
                    out_quotient = (out_quotient << 1) | 1'b1;
                    out_remainder = (out_remainder - comp_divisor);
                end
            out_dividend = out_dividend << 1;
        end 
    end

    assign o_dividend = out_dividend;
    assign o_remainder = out_remainder;
    assign o_quotient = out_quotient;

endmodule
