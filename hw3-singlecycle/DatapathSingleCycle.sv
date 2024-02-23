`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`include "../hw2a/divider_unsigned.sv"
`include "../hw2b/cla.sv"
//`include "cla.sv"

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];

  integer i; 
  always@(posedge clk) begin 
    if(rst == 1'b1) begin 
      for(i = 0; i < NumRegs; i++)
        regs[i] <=0;
    end
    else begin 
      if((rd!= 5'd0) && (we == 1'b1)) 
        regs[rd] <= rd_data;  
      end  
  end

endmodule

module DatapathSingleCycle (
    input wire clk,
    input wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`REG_SIZE] insn_from_imem,
    // addr_to_dmem is a read-write port
    output wire [`REG_SIZE] addr_to_dmem,
    input logic [`REG_SIZE] load_data_from_dmem,
    output wire [`REG_SIZE] store_data_to_dmem,
    output wire [3:0] store_we_to_dmem
);

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [ 4:0] imm_shamt = insn_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};

  // U - Immidiates 
  wire [19:0] imm_u; 
  assign imm_u = insn_from_imem[31:12];

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_i_ext = {{20{1'b0}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};
  wire [`REG_SIZE] imm_u_ext = {{12{1'b0}},imm_u[19:0]};

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;  
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11; //left
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11; 

  localparam bit [`OPCODE_SIZE] OpRegImm  = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11; //left
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  wire insn_lui = insn_opcode == OpLui;
  wire insn_auipc = insn_opcode == OpAuipc;
  wire insn_jal = insn_opcode == OpJal;
  wire insn_jalr = insn_opcode == OpJalr;

  wire insn_beq = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b000;
  wire insn_bne = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b001;
  wire insn_blt = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b100;
  wire insn_bge = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b111;

  wire insn_lb = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b000;
  wire insn_lh = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b001;
  wire insn_lw = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b010;

  wire insn_addi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b000;
  wire insn_slti = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b011;
  wire insn_xori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b100;
  wire insn_ori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b110;
  wire insn_andi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b111;

  wire insn_slli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_srli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_srai = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;

  wire insn_add = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'd0;
  wire insn_sub  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_sll = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_slt = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b010 && insn_from_imem[31:25] == 7'd0;
  wire insn_sltu = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b011 && insn_from_imem[31:25] == 7'd0;
  wire insn_xor = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b100 && insn_from_imem[31:25] == 7'd0;
  wire insn_srl = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_sra  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_or = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b110 && insn_from_imem[31:25] == 7'd0;
  wire insn_and = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b111 && insn_from_imem[31:25] == 7'd0;

  wire insn_mul    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b000;
  wire insn_mulh   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b001;
  wire insn_mulhsu = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b010;
  wire insn_mulhu  = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b011;
  wire insn_div    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b100;
  wire insn_divu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b101;
  wire insn_rem    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b110;
  wire insn_remu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b111;

  wire insn_ecall = insn_opcode == OpEnviron && insn_from_imem[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

  // synthesis translate_off
  // this code is only for simulation, not synthesis
  `include "RvDisassembler.sv"
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn_from_imem);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic...
  wire [(8*32)-1:0] disasm_wire;
  genvar i;
  for (i = 0; i < 32; i = i + 1) begin : gen_disasm
    assign disasm_wire[(((i+1))*8)-1:((i)*8)] = disasm_string[31-i];
  end
  // synthesis translate_on

  // program counter
  logic [`REG_SIZE] pcNext, pcCurrent;
  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      pcCurrent <= pcNext;
    end
  end
  assign pc_to_imem = pcCurrent;

  // cycle/insn_from_imem counters
  logic [`REG_SIZE] cycles_current, num_insns_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
      num_insns_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
      if (!rst) begin
        num_insns_current <= num_insns_current + 1;
      end
    end
  end

  // Control Signals for Reg File
  logic illegal_insn;
  logic [4:0] rd; 
  logic [`REG_SIZE] rd_data;
  logic [4:0] rs1;
  logic [`REG_SIZE] rs1_data;
  logic [4:0] rs2;
  logic [`REG_SIZE] rs2_data;
  logic we;
  // Control Signals for ALU (CLA Adder)
  logic cin; 
  logic [`REG_SIZE] sum;
  // Control Signals for MUX 
  logic [`REG_SIZE] CLA_A;
  logic [`REG_SIZE] CLA_B; 
  logic halt_signal;
  // Control Signals for data memeory  
  logic [`REG_SIZE] address_datamemory;
  logic [`REG_SIZE] address_intermediate;
  logic [`REG_SIZE] data_store;
  logic [3:0] we_datamem;
  logic [63:0] mulitply_result;
  // Control Signals for divider
  logic [`REG_SIZE] dividend;
  logic [`REG_SIZE] divisor;
  logic [`REG_SIZE] remainder;
  logic [`REG_SIZE] quotient;
  // Control Signals for branch
  logic branch_taken;
  // Control signals for Jal and Jalr
  logic [`REG_SIZE] pcIntermmidiate;

  always_comb begin
      // assign default values to control signals
      illegal_insn = 1'b0;
      we = 1'b1;
      cin = 1'b0;
      rd = insn_rd; 
      rs1 = insn_rs1;
      rs2 = insn_rs2;
      pcNext = 32'b0;
      rd_data = 32'b0;
      divisor = 32'b0;
      dividend = 32'b0;
      we_datamem = 4'b0;
      halt_signal = 1'b0;
      data_store = 32'b0;
      branch_taken = 1'b0;
      pcIntermmidiate = 32'b0;
      mulitply_result = 64'b0;
      CLA_A = $signed(rs1_data);
      CLA_B = $signed(rs2_data);
      address_datamemory = 32'b0;
      address_intermediate = rs1_data + imm_i_sext;

      case (insn_opcode)
        OpBranch: begin 
          we = 1'b0;
          if(insn_beq) begin 
            if(rs1_data == rs2_data) begin 
              pcNext = pcCurrent + imm_b_sext;
              branch_taken = 1'b1;
            end
            else begin 
              branch_taken = 1'b0;
            end 
          end
          else if(insn_bne)begin
            if(rs1_data != rs2_data) begin
              pcNext = pcCurrent + imm_b_sext;
              branch_taken = 1'b1;
              end
            else begin 
              branch_taken = 1'b0;
            end 
          end  
          else if(insn_blt)begin 
            if($signed(rs1_data) < $signed(rs2_data)) begin
              pcNext = pcCurrent + imm_b_sext;
              branch_taken = 1'b1;
            end 
            else begin 
              branch_taken = 1'b0;
            end
          end
          else if(insn_bge)begin 
            if($signed(rs1_data) >= $signed(rs2_data)) begin
              pcNext = pcCurrent + imm_b_sext;
              branch_taken = 1'b1;
            end
            else begin 
              branch_taken = 1'b0;
            end 
          end 
          else if(insn_bltu)begin 
            if($signed(rs1_data) < $unsigned(rs2_data)) begin
              pcNext = pcCurrent + imm_b_sext;
              branch_taken = 1'b1;
            end
            else begin 
              branch_taken = 1'b0;
            end
          end
          else if(insn_bgeu)begin 
            if($signed(rs1_data) >= $unsigned(rs2_data)) begin
              pcNext = pcCurrent + imm_b_sext;
              branch_taken = 1'b1;
            end
            else begin 
              branch_taken = 1'b0;
            end
          end 
          else begin 
            pcNext = pcCurrent + 32'd4;
          end       
        end 
        OpEnviron: begin
          we = 1'b0;
          if(insn_ecall) begin
            halt_signal = 1'b1;
          end
        end
        OpLui: begin
          if(rd == 5'b0)
            rd_data = 32'b0;
          else 
            rd_data = (imm_u_ext << 12);
        end
        OpAuipc: begin
          if(insn_auipc) begin 
            pcIntermmidiate = imm_u_ext << 12; 
            rd_data = pcCurrent + pcIntermmidiate; 
          end  
          else begin 
            illegal_insn = 1'b1;
          end 
        end 
        OpRegImm: begin 
          if(insn_addi) begin 
              CLA_B = imm_i_sext;
              rd_data = sum;
          end
          else if (insn_slti) begin 
            if($signed(imm_i_sext) > $signed(rs1_data))
              rd_data = 32'b1;
            else
              rd_data = 32'b0;
          end
          else if(insn_sltiu) begin
            if($signed(rs1_data) < $unsigned(imm_i_sext))
              rd_data = 32'b1;
            else
              rd_data = 32'b0;
          end  
          else if(insn_xori) begin 
            rd_data = $signed(rs1_data) ^ imm_i_sext;
          end 
          else if(insn_ori) begin
            rd_data = $signed(rs1_data) | imm_i_sext;
          end
          else if(insn_andi) begin
            rd_data = $signed(rs1_data) & imm_i_sext;
          end
          else if(insn_slli) begin
            rd_data = (rs1_data << (imm_i_ext[4:0]));
          end
          else if(insn_srli) begin
            rd_data = (rs1_data >> (imm_i_ext[4:0]));
          end
          else if(insn_srai) begin
            rd_data = ($signed(rs1_data) >>> (imm_i_ext[4:0]));
          end
          else begin 
            illegal_insn = 1'b1;
          end 
        end 
        OpRegReg: begin
          if(insn_add) begin 
            rd_data = sum;
          end
          else if(insn_sub) begin 
            CLA_A = rs1_data;
            CLA_B = ~rs2_data;
            cin = 1'b1;
            rd_data = sum;
          end
          else if(insn_sll) begin 
            rd_data = rs1_data << rs2_data[4:0];
          end
          else if(insn_slt) begin  
            if($signed(rs1_data) < $signed(rs2_data)) 
              rd_data = 32'b1;
            else 
              rd_data = 32'b0;
          end
          else if(insn_sltu) begin 
            rd_data = (rs1_data < $unsigned(rs2_data))? 32'b1:32'b0;
          end
          else if(insn_xor) begin 
            rd_data = rs1_data ^ rs2_data;
          end
          else if(insn_srl) begin 
            rd_data = rs1_data >> (rs2_data[4:0]);
          end
          else if(insn_sra) begin 
            rd_data = $signed(rs1_data) >>> (rs2_data[4:0]);
          end
          else if(insn_or) begin 
            rd_data = rs1_data | rs2_data;
          end
          else if(insn_and) begin 
            rd_data = rs1_data & rs2_data;
          end
          else if(insn_mul)begin 
            mulitply_result = (rs1_data * rs2_data);
            rd_data = mulitply_result[31:0];
          end 
          else if(insn_mulh)begin //recheck
            mulitply_result = ($signed(rs1_data) * $signed(rs2_data));
            rd_data = mulitply_result[63:32];
          end  
          else if(insn_mulhsu)begin //recheck
            mulitply_result = ($signed(rs1_data) * $unsigned(rs2_data));
            rd_data = mulitply_result[63:32];
          end
          else if(insn_mulhu)begin //recheck
            mulitply_result = ($unsigned(rs1_data) *  $unsigned(rs2_data));
            rd_data = mulitply_result[63:32];
          end
          else if(insn_div)begin //check 
            dividend = $signed(rs1_data); 
            divisor = $signed(rs2_data);
            rd_data = quotient;
          end
          else if(insn_divu)begin 
            dividend = $signed(rs1_data); 
            divisor =  $unsigned(rs2_data);
            rd_data = quotient;        
          end
          else if (insn_rem)begin //check
            dividend = rs1_data; 
            divisor = rs2_data;
            rd_data = remainder;
          end 
          else if(insn_remu)begin
            dividend = $signed(rs1_data); 
            divisor =  $unsigned(rs2_data);
            rd_data = remainder;
          end  
          else begin 
            illegal_insn = 1'b1;
          end                  
        end   
        OpJal: begin
          if(insn_jal) begin
            branch_taken = 1'b1;
            rd_data = pcCurrent + 32'd4;
            pcNext = pcCurrent + imm_j_sext;
          end 
          else begin 
            branch_taken = 1'b0;
          end 
        end
        OpJalr: begin
          if(insn_jalr)begin 
            branch_taken = 1'b1;
            rd_data = pcCurrent + 32'd4;
            pcIntermmidiate = (($signed(rs1_data) + $signed(imm_i_sext)) & 32'hFFFFFFFE);
            pcNext = pcCurrent + pcIntermmidiate;
          end 
          else begin 
            branch_taken = 1'b0;
          end
        end  
        // OpStore: begin
        //   if(insn_sb)begin
        //     address_datamemory = (rs1_data + {{24{imm_i_sext[7]}},imm_i_sext[7:0]});
        //     data_store = {24'b0,rs2_data[7:0]};
        //     we_datamem = 4'b0001;
        //   end
          // else if(insn_sh == 1'b1)begin
          //   address_datamemory = (rs1_data + {{16{imm_i_sext[15]}},imm_i_sext[15:0]});
          //   data_store = {{16{1'b0}},rs2_data[15:0]};
          //   we_datamem = 4'b0011;
          // end
          // else if(insn_sw == 1'b1)begin 
          //   address_datamemory = (rs1_data + imm_i_sext[31:0]);
          //   data_store = rs2_data;
          //   we_datamem = 4'b1111;
          // end
          // else begin 
          //   illegal_insn = 1'b1;
          // end        
      // end   
        OpLoad: begin //recheck 
          if(insn_lb) begin
            address_intermediate = (rs1_data + (imm_i_sext << 2));
            address_datamemory = (address_intermediate & 32'hFFFF_FFFC); 
            rd_data = {{24{load_data_from_dmem[7]}},load_data_from_dmem[7:0]}; 
            
          end  
        //   else if(insn_lh)begin 
        //     rd_data = load_data_from_dmem; 
        //     address_datamemory = {{16{address_intermediate[15]}},address_intermediate[15:0]};
        //   end
        //   else if(insn_lw)begin 
        //     rd_data = load_data_from_dmem; 
        //     address_datamemory = address_intermediate;
        //   end 
        //   else if(insn_lbu)begin 
        //     rd_data = load_data_from_dmem; 
        //     address_datamemory = {{24'b0},address_intermediate[7:0]};
        //   end 
        //   else if(insn_lhu)begin 
        //     rd_data = load_data_from_dmem; 
        //     address_datamemory = {{16'b0},address_intermediate[15:0]};
        //   end  
          else begin
            illegal_insn = 1'b1; 
          end 
        end 
        default: begin
          illegal_insn = 1'b1;
        end
      endcase
      // increment pc by 4
      if(branch_taken == 1'b0) begin 
        pcNext = pcCurrent + 32'd4;
      end 
    end 
  // take care of memeor alignment 
  assign store_data_to_dmem = data_store;
  assign store_we_to_dmem = we_datamem;
  assign addr_to_dmem = address_datamemory ;
  assign halt = halt_signal;

  divider_unsigned A1(.i_dividend(dividend),
                      .i_divisor(divisor),
                      .o_quotient(quotient),
                      .o_remainder(remainder));

  cla alu(.a(CLA_A),
          .b(CLA_B),
          .cin(cin),
          .sum(sum));

  RegFile rf(.rd(rd),
              .rd_data(rd_data),
              .rs1(rs1),
              .rs1_data(rs1_data),
              .rs2(rs2),
              .rs2_data(rs2_data),
              .clk(clk),
              .we(we),
              .rst(rst));

endmodule

/* A memory module that supports 1-cycle reads and writes, with one read-only port
 * and one read+write port.
 */
module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. See RiscvProcessor for clock details.
    input wire clock_mem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem [NUM_WORDS];

  initial begin
    $readmemh("mem_initial_contents.hex", mem, 0);
  end

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(posedge clock_mem) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clock_mem) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/*
This shows the relationship between clock_proc and clock_mem. The clock_mem is
phase-shifted 90° from clock_proc. You could think of one proc cycle being
broken down into 3 parts. During part 1 (which starts @posedge clock_proc)
the current PC is sent to the imem. In part 2 (starting @posedge clock_mem) we
read from imem. In part 3 (starting @negedge clock_mem) we read/write memory and
prepare register/PC updates, which occur at @posedge clock_proc.

        ____
 proc: |    |______
           ____
 mem:  ___|    |___
*/
module RiscvProcessor (
    input  wire  clock_proc,
    input  wire  clock_mem,
    input  wire  rst,
    output logic halt
);

  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) mem (
      .rst      (rst),
      .clock_mem (clock_mem),
      // imem is read-only
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      // dmem is read-write
      .addr_to_dmem(mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem  (mem_data_we)
  );

  DatapathSingleCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt)
  );

endmodule