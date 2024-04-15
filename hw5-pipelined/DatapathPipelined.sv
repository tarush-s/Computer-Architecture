`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../hw4-multicycle/divider_unsigned_pipelined.sv"
`endif

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
  // synthesis translate_off
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
  // synthesis translate_on
endmodule

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
  //genvar i;
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here
  assign regs[0] = 32'b0;
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];

  integer i; 
  always@(posedge clk) begin 
    if(rst == 1'b1) begin 
      for(i = 0; i < NumRegs; i++)
        regs[i] <=0;
    end
    else begin 
      if((rd!= 5'd0) && (we == 1'b1)) begin
        regs[rd] <= rd_data;  
      end 
      else begin
      end 
    end  
  end
endmodule

/**
 * This enum is used to classify each cycle as it comes through the Writeback stage, identifying
 * if a valid insn is present or, if it is a stall cycle instead, the reason for the stall. The
 * enum values are mutually exclusive: only one should be set for any given cycle. These values
 * are compared against the trace-*.json files to ensure that the datapath is running with the
 * correct timing.
 *
 * You will need to set these values at various places within your pipeline, and propagate them
 * through the stages until they reach Writeback where they can be checked.
 */
typedef enum {
  /** invalid value, this should never appear after the initial reset sequence completes */
  CYCLE_INVALID = 0,
  /** a stall cycle that arose from the initial reset signal */
  CYCLE_RESET = 1,
  /** not a stall cycle, a valid insn is in Writeback */
  CYCLE_NO_STALL = 2,
  /** a stall cycle that arose from a taken branch/jump */
  CYCLE_TAKEN_BRANCH = 4,

  // the values below are only needed in HW5B

  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence.i insn */
  CYCLE_FENCEI = 32
} cycle_status_e;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  logic [`OPCODE_SIZE] opcode;
  logic wd_1;
  logic wd_2;
  cycle_status_e cycle_status;
} stage_decode_t;

//** state at the start of the Execute stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  logic [`OPCODE_SIZE] op_code;
  cycle_status_e cycle_status;
  logic wx_1;
  logic wx_2;
  logic mx_1;
  logic mx_2;
  logic [`REG_SIZE] operand1;
  logic [`REG_SIZE] operand2;
  logic [`REG_SIZE] imm_value;
} stage_execute_t;

//** state at the start of the memory stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`REG_SIZE] operand1;
  logic [`REG_SIZE] operand2;
  logic [`REG_SIZE] imm_value;
  logic [`REG_SIZE] execute_result;
  logic branch_taken;
  logic [`REG_SIZE] load_store_adr_interm;
  logic [`REG_SIZE] load_store_address;
  logic wm_rd;
  logic [3:0] div_instruction;
} stage_memory_t;

//** state at the start of the writeback stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`REG_SIZE] operand1;
  logic [`REG_SIZE] operand2;
  logic [`REG_SIZE] imm_value;
  logic [`REG_SIZE] execute_result;
  logic [`REG_SIZE] memory_result;
} stage_writeback_t;

module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;
  logic [`REG_SIZE] branch_pc;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
    //  f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      if(branch_taken)begin // branch is not taken
        // adjust the pc to go back 3 clock cycles or 12 in decimal value 
        f_pc_current <= branch_pc;
      end 
      else if(load_use_stall || wm_address)begin 
        // stall for a cycle as load use in pipeline
      end
      else if(fence_stall)begin 
        // stall for fence preceded by store
      end 
      else if(div_stall)begin 
      end  
      else begin // branch is takken 
        // assume normal operation 
        f_pc_current <= f_pc_current + 32'd4;
      end 
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

  logic [6:0] f_insn_funct7;
  logic [4:0] f_insn_rs2;
  logic [4:0] f_insn_rs1;
  logic [2:0] f_insn_funct3;
  logic [4:0] f_insn_rd;
  logic [`OPCODE_SIZE] f_insn_opcode;
  logic [`REG_SIZE] f_insn_branch;

  logic wd_rs1_bypass;
  logic wd_rs2_bypass;
  logic [`REG_SIZE] f_pc;
  
  always_comb begin
    wd_rs1_bypass = 1'b0;
    wd_rs2_bypass = 1'b0;
    f_insn_branch = 32'b0; 
    f_pc = 32'b0;
    //decode the instruction at fetch stage 
    {f_insn_funct7, f_insn_rs2, f_insn_rs1, f_insn_funct3, f_insn_rd, f_insn_opcode} = f_insn;

    // handle wd bypassing 
    if((f_insn_rs1 == m_insn_rd) && (f_insn_rs1 != 5'b0) && (f_insn_rs2 == m_insn_rd) && (f_insn_rs2 != 5'b0) && (m_opcode != OpcodeBranch) && (m_opcode != OpcodeStore) && (f_insn_opcode != OpcodeAuipc) && (f_insn_opcode != OpcodeLui) && (f_insn_opcode != OpcodeJal) && (f_insn_opcode != OpcodeJalr))begin 
      wd_rs1_bypass = 1'b1; 
      wd_rs2_bypass = 1'b1; 
    end 
    if((f_insn_rs1 == m_insn_rd) && (f_insn_rs1 != 5'b0) && (m_opcode != OpcodeBranch) && (m_opcode != OpcodeStore) && (f_insn_opcode != OpcodeAuipc) && (f_insn_opcode != OpcodeLui) && (f_insn_opcode != OpcodeJal))begin
      wd_rs1_bypass = 1'b1; 
    end 
    else if((f_insn_rs2 == m_insn_rd) && (f_insn_rs2 != 5'b0) && (m_opcode != OpcodeBranch) && (m_opcode != OpcodeStore) && (f_insn_opcode != OpcodeRegImm) && (f_insn_opcode != OpcodeAuipc) && (f_insn_opcode != OpcodeLui) && (f_insn_opcode != OpcodeJal) && (f_insn_opcode != OpcodeJalr))begin
      wd_rs2_bypass = 1'b1; 
    end 
    else begin
       wd_rs1_bypass = 1'b0;
       wd_rs2_bypass = 1'b0;
    end
    //handle branching and stalls
    if(branch_taken)begin
      f_insn_branch = 32'b0;
      f_pc = 32'b0; 
      wd_rs1_bypass = 1'b0;
      wd_rs2_bypass = 1'b0;
      f_cycle_status = CYCLE_TAKEN_BRANCH;
    end  
    else if(fence_stall)begin
      f_pc = f_pc_current;
      f_insn_branch = f_insn;
      f_cycle_status = CYCLE_FENCEI; 
    end 
    else if(load_use_stall || wm_address)begin
      f_pc = f_pc_current;
      f_insn_branch = f_insn;
      f_cycle_status = CYCLE_LOAD2USE;
    end 
    else if(div_stall)begin 
      f_pc = f_pc_current;
      f_insn_branch = f_insn;
      f_cycle_status = CYCLE_DIV2USE;
    end 
    else begin
      f_pc = f_pc_current;
      f_insn_branch = f_insn; 
      f_cycle_status = CYCLE_NO_STALL;
    end 
  end 

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  logic [`REG_SIZE] d_pc_current;
  logic [`REG_SIZE] d_insn;
  logic [`OPCODE_SIZE] d_opcode;
  logic d_wd1_bypass;
  logic d_wd2_bypass;
  cycle_status_e d_cycle_status;
  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        opcode: 0,
        wd_1: 0,
        wd_2: 0,
        cycle_status: CYCLE_RESET
      };
    end 
    else if(load_use_stall || div_stall || fence_stall || wm_address)begin 
      // stall for a cycle as load use in pipeline
    end 
    // else if(div_stall)begin
    //   // stall for div use 
    // end 
    // else if(fence_stall)begin 
    //   // stall for fence 
    // end 
    else begin
      begin
        decode_state <= '{
          pc: f_pc,
          insn: f_insn_branch,
          opcode: f_insn_opcode,
          wd_1: wd_rs1_bypass,
          wd_2: wd_rs2_bypass,
          cycle_status: f_cycle_status
        };
      end
    end
  end
  assign d_insn = decode_state.insn;
  assign d_pc_current = decode_state.pc;
  assign d_wd1_bypass = decode_state.wd_1;
  assign d_wd2_bypass = decode_state.wd_2;
  assign d_cycle_status = decode_state.cycle_status;
  assign d_opcode = decode_state.opcode;

  //combinational logic between pc and decode stage 
  logic [`REG_SIZE] operand1;   // this value will store rs1_data 
  logic [`REG_SIZE] operand2;   // this value will store rs2_data 
  logic [`REG_SIZE] final_operand1;
  logic [`REG_SIZE] final_operand2;
  logic [`REG_SIZE] imm_val;    // this will store the immmidiate vlue nedded 
  logic [`REG_SIZE] rd_data;    // this will store the value to be written into the reg file
  // necessary signals for the reg file module
  logic we;
  // signal to decode the instruction 
  logic [6:0] insn_funct7;
  logic [4:0] insn_rs2;
  logic [4:0] insn_rs1;
  logic [2:0] insn_funct3;
  logic [4:0] insn_rd;
  logic [`OPCODE_SIZE] insn_opcode;
  logic [`REG_SIZE] rs1_data;
  logic [`REG_SIZE] rs2_data;
  logic [4:0] rd;
  logic [4:0] rs1;
  logic [4:0] rs2;
  // imm signals
  logic [11:0] imm_i;
  logic [ 4:0] imm_shamt;
  // S - stores
  logic [11:0] imm_s;
  // B - conditionals
  logic [12:0] imm_b;
  // J - unconditional jumps
  logic [20:0] imm_j;
  // U - Immidiates 
  logic [19:0] imm_u; 
  logic [`REG_SIZE] imm_i_sext;
  logic [`REG_SIZE] imm_i_ext;
  logic [`REG_SIZE] imm_s_sext;
  logic [`REG_SIZE] imm_b_sext;
  logic [`REG_SIZE] imm_j_sext;
  logic [`REG_SIZE] imm_u_ext;
  logic d_illegal_insn;
  logic wx_rs1_bypass;
  logic wx_rs2_bypass; 
  logic mx_rs1_bypass;
  logic mx_rs2_bypass;
  logic load_use_stall;
  logic [`REG_SIZE] d_insn_branch;
  logic [`REG_SIZE] d_pc;
  logic fence_stall;
  logic div_stall;
  logic wm_address;

  always_comb begin
    //assign default values 
    fence_stall = 1'b0; 
    operand1 = 32'b0;
    operand2 = 32'b0;
    d_pc = 32'b0;
    imm_val = 32'b0;
    wx_rs1_bypass = 1'b0;
    wx_rs2_bypass = 1'b0;
    mx_rs1_bypass = 1'b0;
    mx_rs2_bypass = 1'b0;
    load_use_stall = 1'b0;
    div_stall = 1'b0;
    d_illegal_insn = 1'b0;
    wm_address = 1'b0;
    // branch taken 
    // decode the instruction 
    {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = d_insn;
    // setup for I, S, B & J type instructions
    // I - short immediates and loads
    imm_i = d_insn[31:20];
    //imm_shamt = d_insn[24:20];
    // S - stores
    imm_s[11:5] = insn_funct7;
    imm_s[4:0] = insn_rd;
    // B - conditionals
    {imm_b[12], imm_b[10:5]} = insn_funct7;
    {imm_b[4:1], imm_b[11]} = insn_rd;
    imm_b[0] = 1'b0;
    // J - unconditional jumps
    {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {d_insn[31:12], 1'b0};
    // U - Immidiates 
    imm_u = d_insn[31:12];
    imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
    imm_i_ext = {{20{1'b0}}, imm_i[11:0]};
    imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
    imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
    imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};
    imm_u_ext = {{12{1'b0}},imm_u[19:0]};

    case(insn_opcode)
    OpcodeLui: begin
      operand1 = 32'b0;
      operand2 = 32'b0;
      imm_val =imm_u_ext;
    end 
    OpcodeRegImm:begin
      operand1 = rs1_data;
      operand2 = 32'b0;
      if(d_insn[14:12] == 3'b000) // addi 
        imm_val = imm_i_sext;
      else if(d_insn[14:12] == 3'b010) //slti
        imm_val = imm_i_sext;
      else if(d_insn[14:12] == 3'b011) //sltiu
        imm_val = imm_i_sext;
      else if(d_insn[14:12] == 3'b100) //xori
        imm_val = imm_i_sext;
      else if(d_insn[14:12] == 3'b110) //ori
        imm_val = imm_i_sext;  
      else if(d_insn[14:12] == 3'b111) //andi
        imm_val = imm_i_sext;
      else if((d_insn[14:12] == 3'b001) && (d_insn[31:25] == 7'd0)) //slli
        imm_val = imm_i_ext;
      else if((d_insn[14:12] == 3'b101) && (d_insn[31:25] == 7'd0)) //srli
        imm_val = imm_i_ext;
      else if((d_insn[14:12] == 3'b101) && (d_insn[31:25] == 7'b0100000)) //srai
        imm_val = imm_i_ext;
      else 
        imm_val = imm_i_ext;
    end 
    OpcodeRegReg: begin 
      operand1 = rs1_data;
      operand2 = rs2_data;
      // no need for an immidiate value 
      imm_val = 32'b0;
    end 
    OpcodeAuipc: begin 
      operand1 = 32'b0;
      operand2 = 32'b0;
      imm_val = imm_u_ext;
    end 
    OpcodeLoad: begin
      operand1 = rs1_data;
      operand2 = 32'b0;
      imm_val = imm_i_sext;
    end 
    OpcodeStore: begin
      operand1 = rs1_data;
      operand2 = rs2_data;
      imm_val = imm_s_sext;
    end 
    OpcodeBranch:begin 
      operand1 = rs1_data;
      operand2 = rs2_data;
      imm_val = imm_b_sext;
    end 
    OpcodeJalr: begin
      operand1 = rs1_data;
      operand2 = 32'b0;
      imm_val = imm_i_sext;
    end 
    OpcodeJal: begin 
      operand1 = 32'b0;
      operand2 = 32'b0;
      imm_val = imm_j_sext;
    end 
    OpcodeMiscMem: begin
      //fence instruction so it doesn't matter
      if((x_opcode_comb == OpcodeStore) || (m_opcode == OpcodeStore))begin 
        fence_stall = 1'b1;
      end 
      else begin 
        fence_stall = 1'b0;
        operand1 = 32'b0;
        operand2 = 32'b0;
        imm_val = 32'b0;
      end 
    end 
    OpcodeEnviron: begin
      // ecall instruction so it doesn't matter 
    end 
    default: begin
      d_illegal_insn = 1'b1;
    end 
    endcase
 
    if((div) && ((insn_rs1 == x_insn_rd) || (insn_rs2 == x_insn_rd)))begin 
      // the cycle after the system stall, div has got cirrect result in the execute stage 
      div_stall = 1'b1;
    end 
    else begin 
      div_stall = 1'b0;
    end 

    //Hazard detection
    
    // load use bypass and stall 
    if((((insn_rs1 == x_insn_rd) && (insn_rs1 != 5'b0) && (d_opcode != OpcodeStore) && (d_opcode != OpcodeAuipc) && (d_opcode != OpcodeLui)) || ((insn_rs2 == x_insn_rd) && (d_opcode != OpcodeLoad) && (d_opcode != OpcodeStore) && (insn_rs2 != 5'b0) && (d_opcode != OpcodeRegImm) && (d_opcode != OpcodeAuipc) && (d_opcode != OpcodeLui) && (d_opcode != OpcodeJal))) && (x_opcode_comb == OpcodeLoad))begin
      load_use_stall = 1'b1;
    end
    else begin
      load_use_stall = 1'b0;
    end 
    if((x_opcode == OpcodeLoad) && (d_opcode == OpcodeStore) && (insn_rs1 == x_insn_rd) && (x_insn_rd != 5'b0))begin
      wm_address = 1'b1;
    end
    else begin
      wm_address = 1'b0;
    end 
    // dont trigger branch when the instruction in the x stage is a branch instruction or a load instruction or a store instruction
    if((insn_rs1 == x_insn_rd) && (insn_rs1 != 5'b0) && (insn_rs2 == x_insn_rd) && (insn_rs2 != 5'b0) && (x_opcode_comb != OpcodeBranch) && (x_opcode_comb != OpcodeLoad)  && (x_opcode_comb != OpcodeStore) && (d_opcode != OpcodeAuipc) && (d_opcode != OpcodeLui) && (d_opcode != OpcodeJal) && (d_opcode != OpcodeJalr))begin
      mx_rs1_bypass = 1'b1;
      mx_rs2_bypass = 1'b1; 
    end  
    else if((insn_rs2 == x_insn_rd) && (insn_rs2 != 5'b0) && (x_opcode_comb != OpcodeBranch) && (x_opcode_comb != OpcodeLoad) && (x_opcode_comb != OpcodeLoad)  && (x_opcode_comb != OpcodeStore) && (d_opcode != OpcodeAuipc) && (d_opcode != OpcodeLui) && (d_opcode != OpcodeJal) && (d_opcode != OpcodeJalr))begin
      mx_rs2_bypass = 1'b1; 
    end 
    else if((insn_rs1 == x_insn_rd) && (insn_rs1 != 5'b0) && (x_opcode_comb != OpcodeBranch) && (x_opcode_comb != OpcodeLoad) && (x_opcode_comb != OpcodeLoad)  && (x_opcode_comb != OpcodeStore) && (d_opcode != OpcodeAuipc) && (d_opcode != OpcodeLui) && (d_opcode != OpcodeJal))begin 
      mx_rs1_bypass = 1'b1;
    end
    else begin
      mx_rs1_bypass = 1'b0;
      mx_rs2_bypass = 1'b0;
    end 
    // dont trigger branch when the instruction in the m stage is a branch instruction
    if((insn_rs1 == m_insn_rd) && (insn_rs1 != 5'b0) && (insn_rs2 == m_insn_rd) && (insn_rs2 != 5'b0) && (m_opcode != OpcodeStore) && (m_opcode != OpcodeBranch) && (d_opcode != OpcodeAuipc) && (d_opcode != OpcodeLui) && (d_opcode != OpcodeJal) && (d_opcode != OpcodeJalr))begin 
      wx_rs1_bypass = 1'b1; 
      wx_rs2_bypass = 1'b1; 
    end 
    else if((insn_rs1 == m_insn_rd) && (insn_rs1 != 5'b0) && (m_opcode != OpcodeStore) && (m_opcode != OpcodeBranch) && (d_opcode != OpcodeAuipc) && (d_opcode != OpcodeLui) && (d_opcode != OpcodeJal))begin
      wx_rs1_bypass = 1'b1; 
    end 
    else if((insn_rs2 == m_insn_rd) && (insn_rs2 != 5'b0) && (m_opcode != OpcodeStore) && (m_opcode != OpcodeBranch) && (d_opcode != OpcodeAuipc) && (d_opcode != OpcodeLui) && (d_opcode != OpcodeJal) && (d_opcode != OpcodeJalr))begin
      wx_rs2_bypass = 1'b1; 
    end 
    else begin 
        wx_rs1_bypass = 1'b0;
        wx_rs2_bypass = 1'b0;
    end 
    // handle wd bypassing 
    if(d_wd1_bypass)begin 
      operand1 = w_in;
    end
    if(d_wd2_bypass)begin 
      operand2 = w_in;
    end 
    d_insn_branch = d_insn;
    d_pc = d_pc_current;   
  end 

  RegFile rf(.rd(rd),
             .rd_data(rd_data),
             .rs1(insn_rs1),
             .rs1_data(rs1_data),
             .rs2(insn_rs2),
             .rs2_data(rs2_data),
             .clk(clk),
             .we(we),
             .rst(rst));

  // for simulation 
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm(d_disasm)
  );
  /*****************/
  /* EXECUTE STAGE */
  /******************/
  logic [`REG_SIZE] x_pc_current;
  logic [`REG_SIZE] x_insn;
  cycle_status_e x_cycle_status;
  logic [`REG_SIZE] x_operand1_temp;
  logic [`REG_SIZE] x_operand2_temp;
  logic [`REG_SIZE] x_imm;
  logic [`OPCODE_SIZE] x_opcode;
  logic d_mx_rs1_bypass;
  logic d_mx_rs2_bypass;
  logic d_wx_rs1_bypass;
  logic d_wx_rs2_bypass;

  stage_execute_t execute_state;
  always_ff@ (posedge clk)begin
    if(rst) begin
      execute_state <= '{
        pc : 0,
        insn : 0,
        op_code : 0,
        cycle_status : CYCLE_RESET,
        wx_1 : 0,
        wx_2 : 0,
        mx_1 : 0,
        mx_2 : 0,
        operand1 : 0,
        operand2 : 0,
        imm_value : 0
      };
    end 
    else if(div_stall)begin
      // stall for div use 
      execute_state <= 0;
      execute_state.cycle_status <= CYCLE_DIV2USE;
    end 
    else if(branch_taken)begin 
      execute_state <= 0;
      execute_state.cycle_status <= CYCLE_TAKEN_BRANCH;
    end 
    else if(load_use_stall || wm_address)begin 
      // send a bubble as load use in piepline
      execute_state <= 0;
      execute_state.cycle_status <= CYCLE_LOAD2USE;
    end 
    else if(fence_stall)begin 
      execute_state <= 0;
      execute_state.cycle_status <= CYCLE_FENCEI;
    end 
    else begin
      execute_state <= '{
        pc: d_pc,
        insn: d_insn_branch,
        op_code : insn_opcode,
        cycle_status: d_cycle_status,
        wx_1 : wx_rs1_bypass,
        wx_2 : wx_rs2_bypass,
        mx_1 : mx_rs1_bypass,
        mx_2 : mx_rs2_bypass,
        operand1 : operand1,
        operand2 : operand2,
        imm_value : imm_val
      };     
    end 
  end 
  assign d_mx_rs1_bypass = execute_state.mx_1;
  assign d_mx_rs2_bypass = execute_state.mx_2;
  assign d_wx_rs1_bypass = execute_state.wx_1;
  assign d_wx_rs2_bypass = execute_state.wx_2;
  assign x_operand1_temp = execute_state.operand1;
  assign x_operand2_temp = execute_state.operand2;
  assign x_imm = execute_state.imm_value;
  assign x_opcode = execute_state.op_code;
  assign x_insn =  execute_state.insn; // add an NOP if the branch is taken 
  assign x_pc_current = execute_state.pc;
  assign x_cycle_status = execute_state.cycle_status;
  // control sognals for the combinational logic 
  logic [`REG_SIZE] execute_result; 
  logic x_illegal_insn;
  logic [6:0] x_insn_funct7;
  logic [4:0] x_insn_rs2;
  logic [4:0] x_insn_rs1;
  logic [2:0] x_insn_funct3;
  logic [4:0] x_insn_rd;
  logic [`OPCODE_SIZE] x_opcode_comb;
  logic [`REG_SIZE] x_operand1;
  logic [`REG_SIZE] x_operand2;
  // control signal for the ALU 
  logic [`REG_SIZE] cla_a;
  logic [`REG_SIZE] cla_b;
  logic cin;
  logic [`REG_SIZE] adder_result;
  logic branch_taken;
  logic [`REG_SIZE] x_pc;
  logic [63:0] mul_result;
  logic [63:0] store_result;
  logic [`REG_SIZE] multiplicand;
  // Control Signals for data memeory  
  logic [`REG_SIZE] address_datamemory;
  logic [`REG_SIZE] address_intermediate;
  // control signal for wm bypass
  logic wm_bypass;
  //control signal for divider 
  logic [`REG_SIZE] dividend;
  logic [`REG_SIZE] divisor;
  logic [`REG_SIZE] remainder;
  logic [`REG_SIZE] quotient;
  logic [3:0] div_insn;
  logic div;

  always_comb begin
    //x_cycle_status = CYCLE_NO_STALL;
    // decode the instruction 
    //x_pc = 32'b0;
    x_insn_rs2 = 0;
    {x_insn_funct7, x_insn_rs2, x_insn_rs1, x_insn_funct3, x_insn_rd, x_opcode_comb} = x_insn;
    x_operand1 = 32'b0;
    x_operand2 = 32'b0;
    //handle branching 
    branch_taken = 1'b0;
    branch_pc = 32'b0;
    // multiplication signals
    mul_result = 64'b0;
    store_result = 64'b0;
    multiplicand = 32'b0;
    divisor = 32'b0;
    dividend = 32'b0;
    div_insn = 4'b0;
    div = 1'b0;
    //data memory signals
    address_datamemory = 32'b0;
    address_intermediate = 32'b0;
    wm_bypass = 1'b0;
    // handle hazards 
    if(d_mx_rs2_bypass)begin
      x_operand2 =  m_in;
    end 
    else if(d_wx_rs2_bypass)begin 
      x_operand2 = w_in;
    end 
    else begin
      x_operand2 = x_operand2_temp; 
    end 

    if(d_mx_rs1_bypass)begin
      x_operand1 =  m_in;
    end 
    else if(d_wx_rs1_bypass)begin
      x_operand1 = w_in; 
    end 
    else begin 
      x_operand1 = x_operand1_temp;
    end 
    
    x_illegal_insn = 1'b0;
    execute_result = 32'b0;
    cin = 1'b0;
    cla_a = 32'b0;
    cla_b = 32'b0;

    case(x_opcode_comb)
    OpcodeMiscMem: begin 
      // fence instruction      
    end 
    OpcodeLui: begin
      execute_result = (x_imm << 12); 
    end
    OpcodeAuipc: begin
      execute_result = (x_pc_current + (x_imm << 12)); 
    end 
    OpcodeJal: begin 
      execute_result = (x_pc_current + 32'd4);
      branch_taken = 1'b1;
      branch_pc = x_pc_current + x_imm;
    end 
    OpcodeJalr: begin 
      execute_result = (x_pc_current + 32'd4);
      branch_pc = (($signed(x_operand1) + $signed(x_imm)) & 32'hFFFFFFFE);
      branch_taken = 1'b1;
    end 
    OpcodeRegImm: begin
      if(x_insn[14:12] == 3'b000) begin //addi
        execute_result = x_operand1 + x_imm;
      end 
      else if(x_insn[14:12] == 3'b010) begin // slti
        execute_result = ($signed(x_operand1) < $signed(x_imm)) ? 32'b1 : 32'b0;
      end 
      else if(x_insn[14:12] == 3'b011) begin // sltiu
        if($signed(x_operand1) < $unsigned(x_imm)) begin
          execute_result = 32'b1;
        end 
        else begin
          execute_result = 32'b0;
        end 
      end
      else if(x_insn[14:12] == 3'b100) begin // xori
        execute_result = $signed(x_operand1) ^ x_imm;
      end  
      else if(x_insn[14:12] == 3'b110) begin // ori
        execute_result = $signed(x_operand1) | x_imm;
      end 
      else if(x_insn[14:12] == 3'b111) begin // andi
        execute_result = ($signed(x_operand1) & x_imm);
      end       
      else if((x_insn[14:12] == 3'b001) && (x_insn[31:25] == 7'd0)) begin // slli
        execute_result = (x_operand1 << (x_imm[4:0]));
      end  
      else if((x_insn[14:12] == 3'b101) && (x_insn[31:25] == 7'd0)) begin // srli
        execute_result = (x_operand1 >> x_imm[4:0]);
      end  
      else if((x_insn[14:12] == 3'b101) && (x_insn[31:25] == 7'b0100000)) begin // srai
        execute_result = $signed(x_operand1) >>> (x_imm[4:0]);
      end  
      else begin 
      end 
    end 
    OpcodeRegReg: begin
      if((x_insn[14:12] == 3'b000) && (x_insn[31:25] == 7'd0))begin // add
        cla_a = $signed(x_operand1);
        cla_b = $signed(x_operand2);
        execute_result = adder_result;
        //execute_result = $signed(x_operand1) + $signed(x_operand2);
      end 
      else if((x_insn[14:12] == 3'b000) && (x_insn[31:25] == 7'b0100000))begin // sub
        // cla_a = x_operand1;
        // cla_b = ~x_operand2;
        // cin = 1'b1;
        // execute_result = adder_result;
        execute_result = x_operand1 + ~x_operand2 + 32'b1;
      end 
      else if((x_insn[14:12] == 3'b001) && (x_insn[31:25] == 7'd0))begin // sll
        execute_result = (x_operand1 << x_operand2[4:0]);
      end 
      else if((x_insn[14:12] == 3'b010) && (x_insn[31:25] == 7'd0))begin // slt
        if($signed(x_operand1) < $signed(x_operand2))
          execute_result = 32'b1;
        else 
          execute_result = 32'b0;
      end
      else if((x_insn[14:12] == 3'b011) && (x_insn[31:25] == 7'd0))begin // sltu
        execute_result = (x_operand1 < $unsigned(x_operand2))? 32'b1 : 32'b0;
      end
      else if((x_insn[14:12] == 3'b100) && (x_insn[31:25] == 7'd0))begin // xor
        execute_result = (x_operand1 ^ x_operand2);
      end
      else if((x_insn[14:12] == 3'b101) && (x_insn[31:25] == 7'd0))begin // srl
        execute_result = (x_operand1 >> (x_operand2[4:0]));
      end
      else if((x_insn[14:12] == 3'b101) && (x_insn[31:25] == 7'b0100000))begin // sra
        execute_result = ($signed(x_operand1) >>> (x_operand2[4:0]));
      end
      else if((x_insn[14:12] == 3'b110) && (x_insn[31:25] == 7'd0))begin // or
        execute_result = (x_operand1 | x_operand2);
      end
      else if((x_insn[14:12] == 3'b111) && (x_insn[31:25] == 7'd0))begin // and
        execute_result = (x_operand1 & x_operand2);
      end
      else if((x_insn[14:12] == 3'b000) && (x_insn[31:25] == 7'd1))begin // mul
        mul_result = (x_operand1 * x_operand2);
        execute_result = mul_result[31:0];
      end
      else if((x_insn[14:12] == 3'b001) && (x_insn[31:25] == 7'd1))begin // mulh
        mul_result = ($signed(x_operand1) * $signed(x_operand2));
        execute_result = mul_result[63:32];
      end
      else if((x_insn[14:12] == 3'b010) && (x_insn[31:25] == 7'd1))begin // mulhsu
        multiplicand = (x_operand1[31]) ? (~x_operand1 + 32'b1) : x_operand1;
        mul_result = (multiplicand * $unsigned(x_operand2));
        if(x_operand1[31]) begin
          store_result = ~mul_result + 64'b1;
        end 
        else begin
          store_result = mul_result;
        end 
        execute_result = store_result[63:32];
      end
      else if((x_insn[14:12] == 3'b011) && (x_insn[31:25] == 7'd1))begin // mulhu
        mul_result = ($unsigned(x_operand1) *  $unsigned(x_operand2));
        execute_result = mul_result[63:32];
      end
      else if((x_insn[14:12] == 3'b100) && (x_insn[31:25] == 7'd1))begin // div
        div = 1'b1;
        div_insn = 4'b0001;
        dividend = (x_operand1[31]) ? (~x_operand1 + 32'b1) : x_operand1; 
        divisor = (x_operand2[31]) ? (~x_operand2 + 32'b1) : x_operand2;
        // if(( x_operand1 == 0 | x_operand2 == 0)) begin  
        //     execute_result = $signed(32'hFFFF_FFFF);             
        // end 
        // else if(x_operand1[31] != x_operand2[31]) begin
        //   execute_result = (~quotient + 32'b1);
        // end 
        // else begin 
        //   execute_result = quotient;
        // end 
      end 
      else if((x_insn[14:12] == 3'b101) && (x_insn[31:25] == 7'd1))begin // divu
        div = 1'b1;
        div_insn = 4'b0010;
        dividend = $signed(x_operand1); 
        divisor =  $unsigned(x_operand2);
        // execute_result = quotient;
      end 
      else if((x_insn[14:12] == 3'b110) && (x_insn[31:25] == 7'd1))begin // rem
        div = 1'b1;
        div_insn = 4'b0100;
        dividend = (x_operand1[31]) ? (~x_operand1 + 32'b1) : x_operand1; 
        divisor = (x_operand2[31]) ? (~x_operand2 + 32'b1) : x_operand2;
        // if(x_operand1 == 32'b0) begin  
        //   execute_result = (m_operand2[31]) ? (~x_operand2 + 32'b1) : x_operand2;             
        // end 
        // else if((x_operand1[31])) begin
        //   execute_result = (~remainder + 32'b1);
        // end 
        // else begin 
        //   execute_result = remainder;
        // end
      end 
      else if((x_insn[14:12] == 3'b111) && (x_insn[31:25] == 7'd1))begin // remu
        div = 1'b1;
        div_insn = 4'b1000;
        dividend = $signed(x_operand1); 
        divisor =  $unsigned(x_operand2);
       // execute_result = remainder;
      end 
      else begin 
        execute_result = 32'b0;
      end 
    end    
    OpcodeLoad: begin
      address_intermediate = $signed(x_operand1) + $signed(x_imm);
      address_datamemory = (address_intermediate & 32'hFFFF_FFFC); 
    end 
    OpcodeStore: begin 
      address_intermediate = $signed(x_operand1)  + $signed(x_imm);
      address_datamemory = (address_intermediate & 32'hFFFF_FFFC);   
    end 
    OpcodeBranch: begin
      if(x_insn[14:12] == 3'b000 )begin //beq
        if($signed(x_operand1) == $signed(x_operand2))begin
          branch_taken = 1'b1;
          branch_pc = x_pc_current + x_imm;
        end
        else begin
          branch_taken = 1'b0; 
        end  
      end
      else if(x_insn[14:12] == 3'b001)begin //bne
        if(x_operand1 != x_operand2)begin
          branch_taken = 1'b1;
          branch_pc = x_pc_current + x_imm;
        end 
        else begin
          branch_taken = 1'b0; 
        end  
      end  
      else if(x_insn[14:12] == 3'b100)begin //blt
        if($signed(x_operand1) < $signed(x_operand2))begin
          branch_taken = 1'b1; 
          branch_pc = x_pc_current + x_imm;
        end 
        else begin
          branch_taken = 1'b0; 
        end  
      end  
      else if(x_insn[14:12] == 3'b101)begin //bge
        if($signed(x_operand1) >= $signed(x_operand2))begin 
          branch_taken = 1'b1;
          branch_pc = x_pc_current + x_imm;
        end 
        else begin
          branch_taken = 1'b0; 
        end  
      end  
      else if(x_insn[14:12] == 3'b110)begin //bltu
        if($signed(x_operand1) < $unsigned(x_operand2))begin
          branch_taken = 1'b1;
          branch_pc = x_pc_current + x_imm;
        end 
        else begin
          branch_taken = 1'b0; 
        end  
      end
      else if(x_insn[14:12] == 3'b111)begin //bgeu
        if($signed(x_operand1) >= $unsigned(x_operand2))begin
          branch_taken = 1'b1;
          branch_pc = x_pc_current + x_imm; 
        end 
        else begin
          branch_taken = 1'b0; 
        end  
      end
      else begin
        branch_taken = 1'b0; 
      end     
    end 
    OpcodeEnviron: begin
      // ecall instruction so it doesn't matter 
    end 
    default: begin 
      x_illegal_insn = 1'b1;
    end  
    endcase

    //handle wm bypassing 
    if((x_opcode_comb == OpcodeStore) && (m_opcode == OpcodeLoad) && (x_insn_rs2 == m_insn_rd))begin 
      wm_bypass = 1'b1;
    end 
    else begin 
      wm_bypass = 1'b0;
    end 
  end 

  //*********fix this 
  cla a1(.a(cla_a),
          .b(cla_b),
          .cin(cin),
          .sum(adder_result));

  divider_unsigned_pipelined D1(.clk(clk),
                              .rst(rst),
                              .i_dividend(dividend),
                              .i_divisor(divisor),
                              .o_quotient(quotient),
                              .o_remainder(remainder));
  // for simulation 
  wire [255:0] e_disasm;
  Disasm #(
      .PREFIX("X")
  ) disasm_1execute (
      .insn  (execute_state.insn),
      .disasm(e_disasm)
  );
  /*****************/
  /* MEMORY STAGE */
  /******************/
  logic [`REG_SIZE] m_pc_current;
  logic [`REG_SIZE] m_insn;
  cycle_status_e m_cycle_status;
  logic [`REG_SIZE] m_operand1_temp;
  logic [`REG_SIZE] m_operand2_temp;
  logic [`REG_SIZE] m_imm;
  logic [`REG_SIZE] m_result;
  logic [`REG_SIZE] m_in;
  logic m_branch_taken;
  logic [`REG_SIZE] m_load_store_address;
  logic [`REG_SIZE] m_address_intermediate;  
  logic m_wm;
  logic [3:0] m_div_insn;

  stage_memory_t memory_state;
  always_ff@ (posedge clk)begin
    if(rst) begin
      memory_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        operand1 : 0,
        operand2 : 0,
        imm_value : 0,
        execute_result : 0,
        branch_taken : 0,
        load_store_adr_interm : 0,
        load_store_address : 0,
        wm_rd : 0,
        div_instruction : 0
      };
    end 
    else begin 
      memory_state <= '{
        pc: x_pc_current,
        insn: x_insn,
        cycle_status: x_cycle_status,
        operand1 : x_operand1,
        operand2 : x_operand2,
        imm_value : x_imm,
        execute_result : execute_result,
        branch_taken : branch_taken,
        load_store_adr_interm : address_intermediate,
        load_store_address : address_datamemory,
        wm_rd : wm_bypass,
        div_instruction : div_insn
      };
    end 
  end 

  assign m_operand1 = memory_state.operand1;
  assign m_operand2_temp = memory_state.operand2;
  assign m_imm = memory_state.imm_value;     
  assign m_in = memory_state.execute_result;
  assign m_insn = memory_state.insn;
  assign m_pc_current = memory_state.pc;
  assign m_branch_taken = memory_state.branch_taken;
  assign m_cycle_status = memory_state.cycle_status;
  assign m_load_store_address = memory_state.load_store_address;
  assign m_address_intermediate = memory_state.load_store_adr_interm;
  assign m_wm = memory_state.wm_rd;
  assign m_div_insn = memory_state.div_instruction;

  logic [`REG_SIZE] ms_addr_to_dmem;
  logic [`REG_SIZE] ms_load_data_from_dmem;
  logic [`REG_SIZE] ms_store_data_to_dmem;
  logic [3:0] ms_store_we_to_dmem;
  logic [6:0] m_insn_funct7;
  logic [4:0] m_insn_rs2;
  logic [4:0] m_insn_rs1;
  logic [2:0] m_insn_funct3;
  logic [4:0] m_insn_rd;
  logic [`OPCODE_SIZE] m_opcode;
  logic [`REG_SIZE] m_loaded_data;
  logic [`REG_SIZE] store_data;
  logic [3:0] datamem_we;
  logic [`REG_SIZE] m_operand2;
  logic [`REG_SIZE] m_operand1;
  logic [`REG_SIZE] data_from_mem;
  always_comb begin
    // decode the instruction 
    {m_insn_funct7, m_insn_rs2, m_insn_rs1, m_insn_funct3, m_insn_rd, m_opcode} = m_insn;
    m_result = 32'b0;
    store_data = 32'b0;
    datamem_we = 4'b0;
    data_from_mem = 32'b0;

    //handle wm bypass 
    if(m_wm)begin
      m_operand2 = w_in;
    end
    else begin
      m_operand2 = m_operand2_temp;
    end 

    case(m_opcode)
    OpcodeLoad: begin 
      // implement load here
      data_from_mem = load_data_from_dmem;
      if(m_insn[14:12] == 3'b000) begin //lb
        if(m_address_intermediate[1:0] == 2'b00) begin
          m_result = {{24{data_from_mem[7]}},data_from_mem[7:0]}; 
        end 
        else if(m_address_intermediate[1:0] == 2'b01) begin 
          m_result = {{24{data_from_mem[15]}},data_from_mem[15:8]};
        end 
        else if(m_address_intermediate[1:0] == 2'b10) begin 
          m_result = {{24{data_from_mem[23]}},data_from_mem[23:16]};
        end 
        else begin
          m_result = {{24{data_from_mem[31]}},data_from_mem[31:24]};  
        end 
      end
      else if(m_insn[14:12] == 3'b001) begin //lh
        if(m_address_intermediate[1:0] == 2'b00) begin
          m_result = {{16{data_from_mem[15]}},data_from_mem[15:0]}; 
        end 
        else begin
          m_result = {{16{data_from_mem[31]}},data_from_mem[31:16]}; 
        end 
      end
      else if(m_insn[14:12] == 3'b010) begin //lw
        m_result = data_from_mem[31:0];
      end
      else if(m_insn[14:12] == 3'b100) begin //lbu
        if(m_address_intermediate[1:0] == 2'b00) begin
          m_result = {{24'b0},data_from_mem[7:0]}; 
        end 
        else if(m_address_intermediate[1:0] == 2'b01) begin 
          m_result = {{24'b0},data_from_mem[15:8]};
        end 
        else if(m_address_intermediate[1:0] == 2'b10) begin 
          m_result = {{24'b0},data_from_mem[23:16]};
        end 
        else begin
          m_result = {{24'b0},data_from_mem[31:24]};  
        end 
      end
      else if(m_insn[14:12] == 3'b101) begin //lhu
        if(m_address_intermediate[1:0] == 2'b00) begin
          m_result = {{16'b0},data_from_mem[15:0]}; 
        end 
        else begin
          m_result = {{16'b0},data_from_mem[31:16]}; 
        end 
      end
      else begin
        m_result = 32'b0; 
      end 
    end
    OpcodeStore: begin
      // implemented store here 
      if(m_insn[14:12] == 3'b000)begin //sb
        store_data = {{4{m_operand2[7:0]}}};
        if(m_address_intermediate[1:0] == 2'b00) begin
          datamem_we = 4'b0001;
        end
        else if(m_address_intermediate[1:0] == 2'b01)begin
          datamem_we = 4'b0010;
        end
        else if(m_address_intermediate[1:0] == 2'b10) begin 
          datamem_we = 4'b0100;
        end
        else begin
          datamem_we = 4'b1000; 
        end 
      end
      else if(m_insn[14:12] == 3'b001)begin // sh
        store_data = {{2{m_operand2[15:0]}}};
        if(m_address_intermediate[1:0] == 2'b00) begin
          datamem_we = 4'b0011;
        end
        else begin 
          datamem_we = 4'b1100;
        end 
      end 
      else if(m_insn[14:12] == 3'b010)begin //sw
        store_data = $signed(m_operand2);
        datamem_we = 4'b1111;
      end 
      else begin 
        m_result =  32'b0;
      end 
    end  
    default: begin 
        if((m_div_insn == 4'b0001) )begin //div 
          if(( m_operand1 == 0 | m_operand2 == 0)) begin  
              m_result = $signed(32'hFFFF_FFFF);             
          end 
          else if(m_operand1[31] != m_operand2[31]) begin
            m_result = (~quotient + 32'b1);
          end 
          else begin 
            m_result = quotient;
          end 
        end
        else if((m_div_insn == 4'b0010))begin //divu 
          m_result = quotient; 
        end  
        else if((m_div_insn == 4'b0100) )begin //rem
          if(m_operand1 == 32'b0) begin  
            m_result = (m_operand2[31]) ? (~m_operand2 + 32'b1) : m_operand2;             
          end 
          else if((m_operand1[31])) begin
            m_result = (~remainder + 32'b1);
          end 
          else begin 
            m_result = remainder;
          end 
        end
        else if((m_div_insn == 4'b1000))begin //remu
          m_result = remainder;
        end
        else begin
          m_result = m_in; 
        end
      end 
    endcase 
  end 

  assign store_we_to_dmem = datamem_we;
  assign store_data_to_dmem = store_data;
  assign addr_to_dmem = m_load_store_address;
  //assign m_loaded_data = load_data_from_dmem;

  // for simulation 
  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_1memory (
      .insn  (memory_state.insn),
      .disasm(m_disasm)
  );
  /*****************/
  /* WRITEBACK STAGE */
  /******************/
  logic [`REG_SIZE] w_pc_current;
  logic [`REG_SIZE] w_insn;
  cycle_status_e w_cycle_status;
  logic [`REG_SIZE] w_operand1;
  logic [`REG_SIZE] w_operand2;
  logic [`REG_SIZE] w_imm;
  logic [`REG_SIZE] w_in;

  stage_writeback_t writeback_state;
  always_ff@ (posedge clk)begin
    if(rst) begin
      writeback_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        operand1 : 0,
        operand2 : 0,
        imm_value : 0,
        execute_result : 0,
        memory_result : 0
      };
    end  
    else begin 
      writeback_state <= '{
        pc: m_pc_current,
        insn: m_insn,
        cycle_status: m_cycle_status,
        operand1 : m_operand1,
        operand2 : m_operand2,
        imm_value : m_imm,
        execute_result : m_in,
        memory_result : m_result
      };
    end 
  end 
  assign w_operand1 = writeback_state.operand1;
  assign w_operand2 = writeback_state.operand2;
  assign w_imm = writeback_state.imm_value;
  assign w_in = writeback_state.memory_result;
  assign w_insn = writeback_state.insn;
  assign w_pc_current = writeback_state.pc;
  assign w_cycle_status = writeback_state.cycle_status;
  
  logic [6:0] w_insn_funct7;
  logic [4:0] w_insn_rs2;
  logic [4:0] w_insn_rs1;
  logic [2:0] w_insn_funct3;
  logic [4:0] w_insn_rd;
  logic [`OPCODE_SIZE] w_opcode;
  logic ecall_halt;

  always_comb begin 
    // decode the instruction 
    {w_insn_funct7, w_insn_rs2, w_insn_rs1, w_insn_funct3, w_insn_rd, w_opcode} = w_insn;

    we = 1'b0;
    rd_data = 32'b0;
    rd = 5'b0;
    ecall_halt = 1'b0;
    
    if((w_opcode == OpcodeEnviron) && (w_insn[31:7] == 25'd0))begin
      ecall_halt = 1'b1;
      we = 1'b0;
    end 
    else if((w_opcode != OpcodeBranch) && (w_opcode != OpcodeStore) && (w_insn != 32'b0) && (w_insn_rd != 5'b0)) begin
      we = 1'b1;
      rd_data = w_in;
      rd = w_insn_rd;
    end 
    else begin 
      we = 1'b0;
    end 
  end 

  assign trace_writeback_pc = w_pc_current;
  assign trace_writeback_insn = w_insn;
  assign trace_writeback_cycle_status = w_cycle_status;

  assign halt = ecall_halt;
  // for simulation 
  wire [255:0] w_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_1writeback (
      .insn  (writeback_state.insn),
      .disasm(w_disasm)
  );

endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

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
  logic [`REG_SIZE] mem[NUM_WORDS];

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

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
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

/* This design has just one clock for both processor and memory. */
module RiscvProcessor (
    input  wire  clk,
    input  wire  rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) the_mem  (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );
endmodule

