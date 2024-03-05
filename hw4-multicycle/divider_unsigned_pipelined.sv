/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_stage(
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_divisor
);
    wire [31:0] temp_output_dividend[15:0];
    wire [31:0] temp_output_remainder[15:0];
    wire [31:0] temp_output_quotient[15:0];

    genvar i;

    for(i = 0; i < 16; i=i+1) begin : gen16divider
        if( i == 0)begin : zeroth_iter
            divu_1iter d1(.i_dividend(i_dividend), 
                            .i_divisor(i_divisor), 
                            .i_remainder(i_remainder), 
                            .i_quotient(i_quotient), 
                            .o_dividend(temp_output_dividend[0]), 
                            .o_remainder(temp_output_remainder[0]), 
                            .o_quotient(temp_output_quotient[0]));
        end : zeroth_iter
        else begin : later_iter
            divu_1iter d2(.i_dividend(temp_output_dividend[i-1]), 
                            .i_divisor(i_divisor), 
                            .i_remainder(temp_output_remainder[i-1]),
                            .i_quotient(temp_output_quotient[i-1]), 
                            .o_dividend(temp_output_dividend[i]), 
                            .o_remainder(temp_output_remainder[i]), 
                            .o_quotient(temp_output_quotient[i]));
        end : later_iter
    end : gen16divider

    assign o_remainder = temp_output_remainder[15];
    assign o_quotient = temp_output_quotient[15]; 
    assign o_dividend = temp_output_dividend[15];
    assign o_divisor = i_divisor;
endmodule 

module divider_unsigned_pipelined (
    input wire clk, rst,
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here
    logic [31:0] stage1_i_remainder;
    logic [31:0] stage1_i_quotient;
    logic [31:0] stage1_o_remainder;
    logic [31:0] stage1_o_quotient;
    logic [31:0] stage1_o_dividend;
    logic [31:0] stage1_o_divisor;

    always_ff @( posedge clk ) begin 
        if(rst) begin
            stage1_i_remainder <= 32'b0;
            stage1_i_quotient <= 32'b0;
        end         
    end 

    divider_stage k1(.i_dividend(i_dividend),
                     .i_divisor(i_divisor),
                     .i_remainder(stage1_i_remainder),
                     .i_quotient(stage1_i_quotient),
                     .o_remainder(stage1_o_remainder),
                     .o_quotient(stage1_o_quotient),
                     .o_dividend(stage1_o_dividend),
                     .o_divisor(stage1_o_divisor));

    logic [31:0] stage2_i_dividend;
    logic [31:0] stage2_i_divisor;
    logic [31:0] stage2_i_remainder;
    logic [31:0] stage2_i_quotient;
    logic [31:0] stage2_o_remainder;
    logic [31:0] stage2_o_quotient;
    logic [31:0] stage2_o_dividend;
    logic [31:0] stage2_o_divisor;

    always_ff @( posedge clk ) begin 
        if( rst) begin
            stage2_i_dividend <= 32'b0;
            stage2_i_remainder <= 32'b0;
            stage2_i_quotient <= 32'b0;
            stage2_i_divisor <= 32'b0;
        end 
        
            stage2_i_dividend <= stage1_o_dividend;
            stage2_i_remainder <= stage1_o_remainder;
            stage2_i_quotient <= stage1_o_quotient;
            stage2_i_divisor <= stage1_o_divisor;
        
    end 

    divider_stage k2(.i_dividend(stage2_i_dividend),
                     .i_divisor(stage2_i_divisor),
                     .i_remainder(stage2_i_remainder),
                     .i_quotient(stage2_i_quotient),
                     .o_remainder(stage2_o_remainder),
                     .o_quotient(stage2_o_quotient),
                     .o_dividend(stage2_o_dividend),
                     .o_divisor(stage2_o_divisor));

    assign o_remainder = stage2_o_remainder;
    assign o_quotient = stage2_o_quotient;
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

    // TODO: copy your code from HW2A here
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
        tmp_quotient = i_quotient;
        tmp_remainder = i_remainder;
        tmp_dividend = i_dividend;

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

    assign o_dividend = tmp_dividend;
    assign o_quotient = tmp_quotient;
    assign o_remainder = tmp_remainder;

endmodule
