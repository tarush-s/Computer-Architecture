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
  cycle_status_e cycle_status;
} stage_decode_t;

//** state at the start of the Execute stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`OPCODE_SIZE] opcode;
  logic [`REG_SIZE] operand1;
  logic [`REG_SIZE] operand2;
  logic [`REG_SIZE] imm_value;
} stage_execute_t;

//** state at the start of the memory stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`OPCODE_SIZE] opcode;
  logic [`REG_SIZE] operand1;
  logic [`REG_SIZE] operand2;
  logic [`REG_SIZE] imm_value;
  logic [`REG_SIZE] result;
  logic load_store;
} stage_memory_t;

//** state at the start of the writeback stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`OPCODE_SIZE] opcode;
  logic [`REG_SIZE] operand1;
  logic [`REG_SIZE] operand2;
  logic [`REG_SIZE] imm_value;
  logic [`REG_SIZE] result;
  logic load_store;
  logic [`REG_SIZE] memory_out;
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
      f_pc_current <= f_pc_current + 32'd4;
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm()
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  logic [`REG_SIZE] d_pc_current;
  logic [`REG_SIZE] d_insn;
  cycle_status_e d_cycle_status;
  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };
       d_cycle_status <= CYCLE_RESET;
    end 
    else begin
      begin
        decode_state <= '{
          pc: f_pc_current,
          insn: f_insn,
          cycle_status: f_cycle_status
        };
        //d_insn <= decode_state.insn;
        d_cycle_status <= CYCLE_NO_STALL;
      end
    end
  end
  assign d_insn = decode_state.insn;
  assign d_pc_current = decode_state.pc;

  //combinational logic between pc and decode stage 
  logic [`REG_SIZE] operand1;   // this value will store rs1_data 
  logic [`REG_SIZE] operand2;   // this value will store rs2_data 
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
  
  always_comb begin
    //assign default values 
    //we = 1'b0;
    operand1 = 32'b0;
    operand2 = 32'b0;
    imm_val = 32'b0;
    d_illegal_insn = 1'b0;
    // decode the instruction 
    {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = d_insn;
    // setup for I, S, B & J type instructions
    // I - short immediates and loads
    imm_i = d_insn[31:20];
    imm_shamt = d_insn[24:20];
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

    rs1 = insn_rs1;
    rs2 = insn_rs2;

    case(insn_opcode)
    OpcodeLui: begin
      operand1 = rs1_data;
      operand2 = rs2_data;
      imm_val =imm_u_ext;
    end 
    OpcodeRegImm:begin
      operand1 = rs1_data;
      operand2 = rs2_data;
      imm_val = imm_i_sext;
    end 
    OpcodeRegReg: begin 
      operand1 = rs1_data;
      operand2 = rs2_data;
      imm_val = imm_i_ext;
    end 
    OpcodeAuipc: begin 
      operand1 = rs1_data;
      operand2 = rs2_data;
      imm_val = imm_u_ext;
    end 
    OpcodeLoad: begin
      operand1 = rs1_data;
      operand2 = rs2_data;
      imm_val = imm_i_sext;
    end 
    OpcodeStore: begin
      operand1 = rs1_data;
      operand2 = rs2_data;
      imm_val = imm_i_sext;
    end 
    OpcodeBranch:begin 
      operand1 = rs1_data;
      operand2 = rs2_data;
      imm_val = imm_b_sext;
    end 
    OpcodeJalr: begin
      operand1 = rs1_data;
      operand2 = rs2_data;
      imm_val = imm_i_sext;
    end 
    OpcodeJal: begin 
      operand1 = rs1_data;
      operand2 = rs2_data;
      imm_val = imm_j_sext;
    end 
    OpcodeMiscMem: begin
      //fence instruction so it doesn't matter
      operand1 = rs1_data;
      operand2 = rs2_data;
      imm_val = imm_i_sext;
    end 
    default: begin
      d_illegal_insn = 1'b1;
    end 
    endcase
  end 

  RegFile rf(.rd(rd),
             .rd_data(rd_data),
             .rs1(rs1),
             .rs1_data(rs1_data),
             .rs2(rs2),
             .rs2_data(rs2_data),
             .clk(clk),
             .we(we),
             .rst(rst));
  // for simulation 
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm()
  );
  /*****************/
  /* EXECUTE STAGE */
  /******************/
  logic [`REG_SIZE] x_pc_current;
  logic [`REG_SIZE] x_insn;
  cycle_status_e x_cycle_status;
  logic [`OPCODE_SIZE] x_opcode;
  logic [`REG_SIZE] x_operand1;
  logic [`REG_SIZE] x_operand2;
  logic [`REG_SIZE] x_imm;

  stage_execute_t execute_state;
  always_ff@ (posedge clk)begin
    if(rst) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        opcode : 0,
        operand1 : 0,
        operand2 : 0,
        imm_value : 0
      };
    end 
    else begin 
      execute_state <= '{
        pc: d_pc_current,
        insn: d_insn,
        cycle_status: CYCLE_NO_STALL,
        opcode : insn_opcode,
        operand1 : operand1,
        operand2 : operand2,
        imm_value : imm_val
      };
      
      // x_opcode <= execute_state.opcode;
      // x_operand1 <= execute_state.operand1;
      // x_operand2 <= execute_state.operand2;
      // x_imm <= execute_state.imm_value;
      x_cycle_status <= CYCLE_NO_STALL;
    end 
  end 
  assign x_opcode = execute_state.opcode;
  assign x_operand1 = execute_state.operand1;
  assign x_operand2 = execute_state.operand2;
  assign x_imm = execute_state.imm_value;
  assign x_insn = execute_state.insn;
  assign x_pc_current = execute_state.pc;

  logic [`REG_SIZE] execute_result; 
  logic load_or_store;
  logic x_illegal_insn;

  always_comb begin
    execute_result = 32'b0;
    load_or_store = 1'b0;
    x_illegal_insn = 1'b1;

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
        execute_result = x_operand1 & x_imm;
      end 
      else if(x_insn[14:12] == 3'b010) begin // slti
        execute_result = (x_operand1 < x_imm) ? 32'b1 : 32'b0;
      end 
      else begin 
      end 
    end 
    OpcodeRegReg: begin
    end 
    default: begin 
      x_illegal_insn = 1'b1;
    end  
    endcase
  end 

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
  logic [`OPCODE_SIZE] m_opcode;
  logic [`REG_SIZE] m_operand1;
  logic [`REG_SIZE] m_operand2;
  logic [`REG_SIZE] m_imm;
  logic [`REG_SIZE] m_result;
  logic [`REG_SIZE] m_in;
  logic m_load_store;

  stage_memory_t memory_state;
  always_ff@ (posedge clk)begin
    if(rst) begin
      memory_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        opcode : 0,
        operand1 : 0,
        operand2 : 0,
        imm_value : 0,
        result : 0,
        load_store : 0
      };
    end 
    else begin 
      memory_state <= '{
        pc: x_pc_current,
        insn: x_insn,
        cycle_status: CYCLE_NO_STALL,
        opcode : x_opcode,
        operand1 : x_operand1,
        operand2 : x_operand2,
        imm_value : x_imm,
        result : execute_result,
        load_store : load_or_store
      };
      
      // m_opcode <= memory_state.opcode;
      // m_operand1 <= memory_state.operand1;
      // m_operand2 <= memory_state.operand2;
      // m_imm <= memory_state.imm_value;
      // m_cycle_status <= CYCLE_NO_STALL;
      
      // m_load_store <= memory_state.load_store;
    end 
  end 
  assign m_opcode = memory_state.opcode;
  assign m_operand1 = memory_state.operand1;
  assign m_operand2 = memory_state.operand2;
  assign m_imm = memory_state.imm_value;
  assign m_cycle_status = CYCLE_NO_STALL;     
  assign m_load_store = memory_state.load_store;
  assign m_in = memory_state.result;
  assign m_insn = memory_state.insn;
  assign m_pc_current = memory_state.pc;

  logic [`REG_SIZE] ms_addr_to_dmem;
  logic [`REG_SIZE] ms_load_data_from_dmem;
  logic [`REG_SIZE] ms_store_data_to_dmem;
  logic [3:0] ms_store_we_to_dmem;
  
  always_comb begin
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
  logic [`OPCODE_SIZE] w_opcode;
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
        opcode : 0,
        operand1 : 0,
        operand2 : 0,
        imm_value : 0,
        result : 0,
        load_store : 0,
        memory_out : 0
      };
    end 
    else begin 
      writeback_state <= '{
        pc: m_pc_current,
        insn: m_insn,
        cycle_status: CYCLE_NO_STALL,
        opcode : m_opcode,
        operand1 : m_operand1,
        operand2 : m_operand2,
        imm_value : m_imm,
        result : m_in,
        load_store : m_load_store,
        memory_out : m_result
      };
      
      w_opcode <= writeback_state.opcode;
      w_operand1 <= writeback_state.operand1;
      w_operand2 <= writeback_state.operand2;
      w_imm <= writeback_state.imm_value;
      w_cycle_status <= CYCLE_NO_STALL;
      
      w_load_store <= writeback_state.load_store;
    end 
  end 
  assign w_in = writeback_state.memory_out;
  assign w_insn = writeback_state.insn;
  assign w_pc_current = writeback_state.pc;

  always_comb begin 
    we = 1'b0;
    rd_data = 32'b0;
    rd = w_insn[11:7];
    if((w_opcode != OpcodeBranch) && (w_opcode != OpcodeStore)) begin
      we = 1'b1;
      rd_data = w_in;
    end 
    else begin 
      we = 1'b0;
    end 
  end 

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
  ) mem (
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
