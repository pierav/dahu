
module static_decoder #() (
    input logic [C::XLEN-1:0] pc_i,
    input logic [31:0] data_i,
    output C::si_t si_o
);

  RV::instruction_t instr;
  assign instr = RV::instruction_t'(data_i);
  C::fuop_t fuop;
  logic [C::XLEN-1:0] imm;
  logic valid;

  assign si_o.pc     = pc_i;
  assign si_o.tinst  = data_i;
  assign si_o.fu     = fuop.fu;
  assign si_o.op     = fuop.op;
  // Let's have fast calculation
  assign si_o.rs1    = data_i[19:15];
  assign si_o.rs2    = data_i[24:20];
  assign si_o.rd     = data_i[11:7];
  assign si_o.imm    = imm;
  assign si_o.valid  = valid;

  always_comb begin : decoder
    fuop = C::I_NOP;
    casez (data_i)
      RVI::ADD: begin fuop = C::I_ADD; end
      RVI::ADDI: begin fuop = C::I_ADDI; end
      RVI::ADDIW: begin fuop = C::I_ADDIW; end
      RVI::ADDW: begin fuop = C::I_ADDW; end
      RVI::AND: begin fuop = C::I_AND; end
      RVI::ANDI: begin fuop = C::I_ANDI; end
      RVI::AUIPC: begin fuop = C::I_AUIPC; end
      RVI::BEQ: begin fuop = C::I_BEQ; end
      RVI::BGE: begin fuop = C::I_BGE; end
      RVI::BGEU: begin fuop = C::I_BGEU; end
      RVI::BLT: begin fuop = C::I_BLT; end
      RVI::BLTU: begin fuop = C::I_BLTU; end
      RVI::BNE: begin fuop = C::I_BNE; end
      RVI::EBREAK: begin fuop = C::I_EBREAK; end
      RVI::ECALL: begin fuop = C::I_ECALL; end
      RVI::FENCE: begin fuop = C::I_FENCE; end
      RVI::JAL: begin fuop = C::I_JAL; end
      RVI::JALR: begin fuop = C::I_JALR; end
      RVI::LB: begin fuop = C::I_LB; end
      RVI::LBU: begin fuop = C::I_LBU; end
      RVI::LD: begin fuop = C::I_LD; end
      RVI::LH: begin fuop = C::I_LH; end
      RVI::LHU: begin fuop = C::I_LHU; end
      RVI::LUI: begin fuop = C::I_LUI; end
      RVI::LW: begin fuop = C::I_LW; end
      RVI::LWU: begin fuop = C::I_LWU; end
      RVI::OR: begin fuop = C::I_OR; end
      RVI::ORI: begin fuop = C::I_ORI; end
      RVI::SB: begin fuop = C::I_SB; end
      RVI::SD: begin fuop = C::I_SD; end
      RVI::SH: begin fuop = C::I_SH; end
      RVI::SLL: begin fuop = C::I_SLL; end
      RVI::SLLI: begin fuop = C::I_SLLI; end
      RVI::SLLIW: begin fuop = C::I_SLLIW; end
      RVI::SLLW: begin fuop = C::I_SLLW; end
      RVI::SLT: begin fuop = C::I_SLT; end
      RVI::SLTI: begin fuop = C::I_SLTI; end
      RVI::SLTIU: begin fuop = C::I_SLTIU; end
      RVI::SLTU: begin fuop = C::I_SLTU; end
      RVI::SRA: begin fuop = C::I_SRA; end
      RVI::SRAI: begin fuop = C::I_SRAI; end
      RVI::SRAIW: begin fuop = C::I_SRAIW; end
      RVI::SRAW: begin fuop = C::I_SRAW; end
      RVI::SRL: begin fuop = C::I_SRL; end
      RVI::SRLI: begin fuop = C::I_SRLI; end
      RVI::SRLIW: begin fuop = C::I_SRLIW; end
      RVI::SRLW: begin fuop = C::I_SRLW; end
      RVI::SUB: begin fuop = C::I_SUB; end
      RVI::SUBW: begin fuop = C::I_SUBW; end
      RVI::SW: begin fuop = C::I_SW; end
      RVI::XOR: begin fuop = C::I_XOR; end
      RVI::XORI: begin fuop = C::I_XORI; end
      default: begin
        valid = 1'b0;
      end
    endcase
  end
  
  always_comb begin : compute_imm
    // select immediate
    case (fuop.fmt)
      C::TYPE_I: begin
        imm = {{XLEN - 12{data_i[31]}}, data_i[31:20]};
      end
      C::TYPE_S: begin
        imm = {{XLEN - 12{data_i[31]}}, data_i[31:25], data_i[11:7]};
      end
      C::TYPE_B: begin
        imm = {{XLEN - 13{data_i[31]}}, data_i[31], data_i[7], data_i[30:25], data_i[11:8], 1'b0};
      end
      C::TYPE_U: begin
        imm = {{XLEN - 32{data_i[31]}}, data_i[31:12], 12'b0};
      end
      C::TYPE_J: begin
        imm  = {{XLEN - 20{data_i[31]}}, data_i[19:12], data_i[20], data_i[30:21],  1'b0};
      end
      default: begin
        imm  = {XLEN{1'b0}};
      end
    endcase
  end

endmodule
