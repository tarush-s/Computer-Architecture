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
  logic load_store;
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
  logic load_store;
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

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      if(m_branch_taken == 1'b0)begin // branch is not taken
        // assume normal operation 
        f_pc_current <= f_pc_current + 32'd4;
      end 
      else begin // branch is takken 
        // adjust the pc to go back 2 cycles or 8 in value 
        f_pc_current <= ((f_pc_current -  32'd8) + m_imm);
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
  
  always_comb begin
    wd_rs1_bypass = 1'b0;
    wd_rs2_bypass = 1'b0;
    f_insn_branch = 32'b0; 
    //decode the instruction at fetch stage 
    {f_insn_funct7, f_insn_rs2, f_insn_rs1, f_insn_funct3, f_insn_rd, f_insn_opcode} = f_insn;

    // handle wd bypassing 
    if((f_insn_rs1 == m_insn_rd) && (f_insn_rs1 != 5'b0))begin
      wd_rs1_bypass = 1'b1; 
    end 
    else if((f_insn_rs2 == m_insn_rd) && (f_insn_rs2 != 5'b0))begin
      wd_rs2_bypass = 1'b1; 
    end 
    else begin
       wd_rs1_bypass = 1'b0;
       wd_rs2_bypass = 1'b0;
    end

    //handle branching 
    if(branch_taken)begin
      f_insn_branch = 32'b0; 
    end  
    else begin
      f_insn_branch = f_insn; 
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
        wd_1: 0,
        wd_2: 0,
        cycle_status: CYCLE_RESET
      };
       d_cycle_status <= CYCLE_RESET;
    end 
    else begin
      begin
        decode_state <= '{
          pc: f_pc_current,
          insn: f_insn_branch,
          wd_1: wd_rs1_bypass,
          wd_2: wd_rs2_bypass,
          cycle_status: f_cycle_status
        };
        d_cycle_status <= CYCLE_NO_STALL;
      end
    end
  end
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
  logic [`REG_SIZE] x_operand1;
  logic [`REG_SIZE] x_operand2;
  logic [`REG_SIZE] x_operand1_temp;
  logic [`REG_SIZE] x_operand2_temp;
  logic [`REG_SIZE] x_imm;
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
      x_cycle_status <= CYCLE_RESET;
    end 
    else begin 
      execute_state <= '{
        pc: d_pc_current,
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
      x_cycle_status <= CYCLE_NO_STALL;
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
  // control sognals for the combinational logic 
  logic [`REG_SIZE] execute_result; 
  logic load_or_store;
  logic x_illegal_insn;
  logic [6:0] x_insn_funct7;
  logic [4:0] x_insn_rs2;
  logic [4:0] x_insn_rs1;
  logic [2:0] x_insn_funct3;
  logic [4:0] x_insn_rd;
  logic [`OPCODE_SIZE] x_opcode;
  logic [`OPCODE_SIZE] x_opcode_ignore;
  // control signal for the ALU 
  logic [`REG_SIZE] cla_a;
  logic [`REG_SIZE] cla_b;
  logic cin;
  logic [`REG_SIZE] adder_result;
  logic branch_taken;
  logic [`REG_SIZE] branch_target;
  
  always_comb begin
    //x_cycle_status = CYCLE_NO_STALL;
    // decode the instruction 
    {x_insn_funct7, x_insn_rs2, x_insn_rs1, x_insn_funct3, x_insn_rd, x_opcode_ignore} = x_insn;
    x_operand1 = x_operand1_temp;
    x_operand2 = x_operand2_temp;
    //handle branching 
    branch_taken = 1'b0;
    // handle hazards 
    if(d_mx_rs2_bypass)begin
      x_operand2 =  m_in;
    end 
    else if(d_wx_rs2_bypass)begin 
      x_operand2 = w_in;
    end 

    if(d_mx_rs1_bypass)begin
      x_operand1 =  m_in;
    end 
    else if(d_wx_rs1_bypass)begin
       x_operand1 = w_in; 
    end 
    
  
    load_or_store = 1'b0;
    x_illegal_insn = 1'b0;
    execute_result = 32'b0;
    cin = 1'b0;
    cla_a = 32'b0;
    cla_b = 32'b0;

    case(x_opcode)
    OpcodeLui: begin
      execute_result = (x_imm << 12); 
    end
    OpcodeJal: begin //have to add to this 
      execute_result = (x_pc_current + 32'd4);
    end 
    OpcodeJalr: begin //have to add to this 
      execute_result = (x_pc_current + 32'd4);
    end 
    OpcodeRegImm: begin
      if(x_insn[14:12] == 3'b000) begin //addi
        execute_result = x_operand1 + x_imm;
      end 
      else if(x_insn[14:12] == 3'b010) begin // slti
        execute_result = ($signed(x_operand1) < $signed(x_imm)) ? 32'b1 : 32'b0;
      end 
      else if(x_insn[14:12] == 3'b011) begin // sltiu
        execute_result = ($signed(x_operand1) < $unsigned(x_imm)) ? 32'b1 : 32'b0;
      end
      else if(x_insn[14:12] == 3'b100) begin // xori
        execute_result = ($signed(x_operand1) ^ x_imm);
      end  
      else if(x_insn[14:12] == 3'b110) begin // ori
        execute_result = ($signed(x_operand1) | x_imm);
      end 
      else if(x_insn[14:12] == 3'b111) begin // andi
        execute_result = ($signed(x_operand1) & x_imm);
      end       
      else if((x_insn[14:12] == 3'b001) && (x_insn[31:25] == 7'd0)) begin // slli
        execute_result = (x_operand1 << x_imm[4:0]);
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
        // cla_a = $signed(x_operand1);
        // cla_b = $signed(x_operand2);
        // execute_result = adder_result;
        execute_result = $signed(x_operand1) + $signed(x_operand2);
      end 
      else if((x_insn[14:12] == 3'b000) && (x_insn[31:25] == 7'b0100000))begin // sub
        // cla_a = x_operand1;
        // cla_b = ~x_operand2;
        // cin = 1'b1;
        execute_result = x_operand1 + ~x_operand2 + 32'b1;
       end 
      else if((x_insn[14:12] == 3'b001) && (x_insn[31:25] == 7'd0))begin // sll
        execute_result = (x_operand1 << x_operand2[4:0]);
      end 
      else if((x_insn[14:12] == 3'b001) && (x_insn[31:25] == 7'd0))begin // slt
        execute_result = ($signed(x_operand1) < $signed(x_operand2))? 32'b1 : 32'b0;
      end
      else if((x_insn[14:12] == 3'b010) && (x_insn[31:25] == 7'd0))begin // sltu
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
      else begin 
      end 
    end    
    OpcodeBranch: begin
      if(x_insn[14:12] == 3'b000)begin //beq
        if($signed(x_operand1) == $signed(x_operand2))begin
         // x_cycle_status = CYCLE_TAKEN_BRANCH;
          branch_taken = 1'b1;
        end 
      end
      else if(x_insn[14:12] == 3'b001)begin //bne
        if(x_operand1 != x_operand2)begin
         // x_cycle_status = CYCLE_TAKEN_BRANCH;
          branch_taken = 1'b1;
        end 
      end  
      else if(x_insn[14:12] == 3'b100)begin //blt
        if($signed(x_operand1) < $signed(x_operand2))begin
         // x_cycle_status = CYCLE_TAKEN_BRANCH;
          branch_taken = 1'b1; 
        end 
      end  
      else if(x_insn[14:12] == 3'b101)begin //bge
        if($signed(x_operand1) >= $signed(x_operand2))begin 
         // x_cycle_status = CYCLE_TAKEN_BRANCH;
          branch_taken = 1'b1;
        end 
      end  
      else if(x_insn[14:12] == 3'b110)begin //bltu
        if($signed(x_operand1) < $unsigned(x_operand2))begin
         // x_cycle_status = CYCLE_TAKEN_BRANCH;
          branch_taken = 1'b1;
        end 
      end
      else if(x_insn[14:12] == 3'b111)begin //bgeu
        if($signed(operand1) >= $unsigned(operand2))begin
         // x_cycle_status = CYCLE_TAKEN_BRANCH;
          branch_taken = 1'b1; 
        end 
      end
      else begin
        branch_taken = 1'b0; 
      end     
    end 
    default: begin 
      x_illegal_insn = 1'b1;
    end  
    endcase
  end 

  //*********fix this 
  cla a1(.a(cla_a),
          .b(cla_b),
          .cin(cin),
          .sum(adder_result));

  // for simulation 
  Disasm #(
      .PREFIX("X")
  ) disasm_1execute (
      .insn  (execute_state.insn),
      .disasm()
  );
  /*****************/
  /* MEMORY STAGE */
  /******************/
  logic [`REG_SIZE] m_pc_current;
  logic [`REG_SIZE] m_insn;
  cycle_status_e m_cycle_status;
  logic [`REG_SIZE] m_operand1;
  logic [`REG_SIZE] m_operand2;
  logic [`REG_SIZE] m_imm;
  logic [`REG_SIZE] m_result;
  logic [`REG_SIZE] m_in;
  logic m_load_store;
  logic m_branch_taken;


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
        load_store : 0
      };
      m_cycle_status <= CYCLE_RESET;
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
        load_store : load_or_store
      };
      m_cycle_status <= CYCLE_NO_STALL;
    end 
  end 

  assign m_operand1 = memory_state.operand1;
  assign m_operand2 = memory_state.operand2;
  assign m_imm = memory_state.imm_value;     
  assign m_load_store = memory_state.load_store;
  assign m_in = memory_state.execute_result;
  assign m_insn = memory_state.insn;
  assign m_pc_current = memory_state.pc;
  assign m_branch_taken = memory_state.branch_taken;

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
  
  always_comb begin
    // decode the instruction 
    {m_insn_funct7, m_insn_rs2, m_insn_rs1, m_insn_funct3, m_insn_rd, m_opcode} = m_insn;

    m_result = 32'b0;
    if(m_load_store) begin
      // implement load store here
    end 
    else begin
      m_result =  m_in;
    end  
  end 

  // for simulation 
  Disasm #(
      .PREFIX("M")
  ) disasm_1memory (
      .insn  (memory_state.insn),
      .disasm()
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
  logic w_load_store;

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
        load_store : 0,
        memory_result : 0
      };
      w_cycle_status <= CYCLE_RESET;
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
        load_store : m_load_store,
        memory_result : m_result
      };
      w_cycle_status <= CYCLE_NO_STALL;
    end 
  end 
  assign w_operand1 = writeback_state.operand1;
  assign w_operand2 = writeback_state.operand2;
  assign w_imm = writeback_state.imm_value;
  assign w_load_store = writeback_state.load_store;
  assign w_in = writeback_state.memory_result;
  assign w_insn = writeback_state.insn;
  assign w_pc_current = writeback_state.pc;
  
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
    rd = w_insn[11:7];
    ecall_halt = 1'b0;
    
    if((w_opcode == OpcodeEnviron) && (w_insn[31:7] == 25'd0))begin
      ecall_halt = 1'b1;
    end 
    else begin
      if((w_opcode != OpcodeBranch) && (w_opcode != OpcodeStore) && (w_insn != 32'b0)) begin
        we = 1'b1;
        rd_data = w_in;
      end 
      else begin 
        we = 1'b0;
      end 
    end 
  end 

  assign halt = ecall_halt;
  // for simulation 
  Disasm #(
      .PREFIX("W")
  ) disasm_1writeback (
      .insn  (writeback_state.insn),
      .disasm()
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
  ) the_mem (
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
