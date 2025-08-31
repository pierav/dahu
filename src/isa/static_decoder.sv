
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

  always_comb begin : decoder
    valid = 1'b1;
    unique casez (data_i)
      /* Trap-Return Instructions */    
      RVI::SRET: begin fuop = C::I_SRET; end
      RVI::MRET: begin fuop = C::I_MRET; end
      /* Interrupt-Management Instructions */
      RVI::WFI:     begin fuop = C::I_WFI; end
      /* Supervisor Memory-Management Instrctions */
      RVI::SFENCE_VMA: begin fuop = C::I_SFENCE_VMA; end
      /* RV32I Base Instruction Set */
      RVI::LUI:     begin fuop = C::I_LUI; end
      RVI::AUIPC:   begin fuop = C::I_AUIPC; end
      RVI::JAL:     begin fuop = C::I_JAL; end
      RVI::JALR:    begin fuop = C::I_JALR; end
      RVI::BLT:     begin fuop = C::I_BLT; end
      RVI::BLTU:    begin fuop = C::I_BLTU; end
      RVI::BGE:     begin fuop = C::I_BGE; end
      RVI::BGEU:    begin fuop = C::I_BGEU; end
      RVI::BEQ:     begin fuop = C::I_BEQ; end
      RVI::BNE:     begin fuop = C::I_BNE; end
      RVI::LB:      begin fuop = C::I_LB; end
      RVI::LH:      begin fuop = C::I_LH; end
      RVI::LW:      begin fuop = C::I_LW; end
      RVI::LBU:     begin fuop = C::I_LBU; end
      RVI::LHU:     begin fuop = C::I_LHU; end
      RVI::SB:      begin fuop = C::I_SB; end
      RVI::SH:      begin fuop = C::I_SH; end
      RVI::SW:      begin fuop = C::I_SW; end
      RVI::ADDI:    begin fuop = C::I_ADDI; end
      RVI::SLTI:    begin fuop = C::I_SLTI; end
      RVI::SLTIU:   begin fuop = C::I_SLTIU; end
      RVI::XORI:    begin fuop = C::I_XORI; end
      RVI::ORI:     begin fuop = C::I_ORI; end
      RVI::ANDI:    begin fuop = C::I_ANDI; end
      RVI::ADD:     begin fuop = C::I_ADD; end
      RVI::SUB:     begin fuop = C::I_SUB; end
      RVI::SLL:     begin fuop = C::I_SLL; end
      RVI::SLT:     begin fuop = C::I_SLT; end
      RVI::SLTU:    begin fuop = C::I_SLTU; end
      RVI::XOR:     begin fuop = C::I_XOR; end
      RVI::SRL:     begin fuop = C::I_SRL; end
      RVI::SRA:     begin fuop = C::I_SRA; end
      RVI::OR:      begin fuop = C::I_OR; end
      RVI::AND:     begin fuop = C::I_AND; end
      RVI::FENCE:   begin fuop = C::I_FENCE; end
      RVI::ECALL:   begin fuop = C::I_ECALL; end
      RVI::EBREAK:  begin fuop = C::I_EBREAK; end
      /* RV64I Base Instruction Set (in addition to RV32I) */
      RVI::LWU:     begin fuop = C::I_LWU; end
      RVI::LD:      begin fuop = C::I_LD; end
      RVI::SD:      begin fuop = C::I_SD; end
      RVI::SLLI:    begin fuop = C::I_SLLI; end
      RVI::SRLI:    begin fuop = C::I_SRLI; end
      RVI::SRAI:    begin fuop = C::I_SRAI; end
      RVI::ADDIW:   begin fuop = C::I_ADDIW; end
      RVI::SLLIW:   begin fuop = C::I_SLLIW; end
      RVI::SRLIW:   begin fuop = C::I_SRLIW; end
      RVI::SRAIW:   begin fuop = C::I_SRAIW; end
      RVI::ADDW:    begin fuop = C::I_ADDW; end
      RVI::SUBW:    begin fuop = C::I_SUBW; end
      RVI::SLLW:    begin fuop = C::I_SLLW; end
      RVI::SRLW:    begin fuop = C::I_SRLW; end
      RVI::SRAW:    begin fuop = C::I_SRAW; end
       /* RV32/RV64 Zifencei Standard Extension */
      RVI::FENCE_I: begin fuop = C::I_FENCE_I; end
      /* RV32/RV64 Zicsr Standard Extension */
      RVI::CSRRW:   begin fuop = C::I_CSRRW; end
      RVI::CSRRS:   begin fuop = C::I_CSRRS; fuop.op = rs1 == 0 ? CSR_READ : CSR_SET; end
      RVI::CSRRC:   begin fuop = C::I_CSRRC; fuop.op = rs1 == 0 ? CSR_READ : CSR_CLEAR; end
      RVI::CSRRWI:  begin fuop = C::I_CSRRWI; end
      RVI::CSRRSI:  begin fuop = C::I_CSRRSI; fuop.op = rs1 == 0 ? CSR_READ : CSR_SET; end
      RVI::CSRRCI:  begin fuop = C::I_CSRRCI; fuop.op = rs1 == 0 ? CSR_READ : CSR_CLEAR; end
      /* RV32/RV64 M Standard Extension */
      RVI::MUL:     begin fuop = C::I_MUL; end
      RVI::MULH:    begin fuop = C::I_MULH; end
      RVI::MULHSU:  begin fuop = C::I_MULHSU; end
      RVI::MULHU:   begin fuop = C::I_MULHU; end
      RVI::DIV:     begin fuop = C::I_DIV; end
      RVI::DIVU:    begin fuop = C::I_DIVU; end
      RVI::REM:     begin fuop = C::I_REM; end
      RVI::REMU:    begin fuop = C::I_REMU; end
      RVI::MULW:    begin fuop = C::I_MULW; end
      RVI::DIVW:    begin fuop = C::I_DIVW; end
      RVI::DIVUW:   begin fuop = C::I_DIVUW; end
      RVI::REMW:    begin fuop = C::I_REMW; end
      RVI::REMUW:   begin fuop = C::I_REMUW; end
      default: begin
        valid = 1'b0;
        fuop = '0;
      end
    endcase
  end
  
  logic use_uimm;

  always_comb begin : compute_imm
    // select immediate
    use_uimm = 0;
    unique case (fuop.fmt)
      C::TYPE_I: begin
        imm = {{XLEN - 12{data_i[31]}}, data_i[31:20]};
      end
      C::TYPE_I_AND_UIMM: begin /* CSR + uimm */
        imm = XLEN'(data_i[31:20]);
        use_uimm = 1;
      end
      C::TYPE_R_FOR_CSR: begin /* CSR */
        imm = XLEN'(data_i[31:20]);
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
      C::TYPE_SHAMT: begin // Shift ammount
        imm =  XLEN'({data_i[25:20]});
      end
      default: begin
        imm  = {XLEN{1'b0}};
      end
    endcase
  end

  areg_id_t rs1, rs2, rd;
  assign rs1 = data_i[19:15]; // Let's have fast calculation
  assign rs2 = data_i[24:20];
  assign rd = data_i[11:7];
  logic rs1v, rs2v, rdv;
  // TODO TYPE_I_AND_UIMM
  assign rs1v = fuop.fmt inside {C::TYPE_R, C::TYPE_I, C::TYPE_SHAMT,
                                 C::TYPE_S, C::TYPE_B, C::TYPE_R_FOR_CSR};
  assign rs2v = fuop.fmt inside {C::TYPE_R, C::TYPE_S, C::TYPE_B};
  assign rdv  = fuop.fmt inside {C::TYPE_R, C::TYPE_I, C::TYPE_U,
                                 C::TYPE_J, C::TYPE_SHAMT, C::TYPE_R_FOR_CSR};
  logic is_not_hint;
  assign is_not_hint = !(rdv && rd == 0 && fuop.fu inside {FU_ALU, FU_MUL, FU_DIV});
  // In case of hint the instruction is converted to 1 cycle latency NOP
  // this avoids multiple WB of the same P(reg) in the same cycle.
  // We mv it to completion and not wb port
  // TODO: can we invalidate operands valid ?
  assign si_o.pc          = pc_i;
  assign si_o.tinst       = data_i;
  assign si_o.fu          = is_not_hint ? fuop.fu : FU_NONE;
  assign si_o.op          = is_not_hint ? fuop.op : NOP_OR_HINT;
  assign si_o.rs1         = rs1;
  assign si_o.rs2         = rs2;
  assign si_o.rd          = rd;
  assign si_o.rs1_valid   = rs1v; // hints Waits for operands ?
  assign si_o.rs2_valid   = rs2v;
  assign si_o.rd_valid    = is_not_hint ? rdv && rd != 0 : '0; // Ignore rd == zero
  assign si_o.imm         = imm;
  assign si_o.use_uimm    = use_uimm; // need use_pc ?
  assign si_o.size        = fuop.size;
  assign si_o.valid       = valid;


endmodule
