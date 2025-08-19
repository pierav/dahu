
#include "core_oracle/encoding.h"
#include <cstring>
#include <string>
#include <cstdio>
#include <cstdint>
#include <inttypes.h>

#define INST_LIST() \
  /* Trap-Return Instructions */   \
  INST(SRET, 0, 0, "sret%c", 0) \
  INST(MRET, 0, 0, "mret%c", 0) \
  /* Interrupt-Management Instructions */ \
  INST(WFI, 0, 0, "wfi%c", 0) \
  /* RV32/RV64 I Base Instruction Set */ \
  INST(LUI, 1, 0, "lui %s, %ld", rd(), u_imm()) \
  INST(AUIPC, 0, 1, "auipc %s, %ld", rd(), u_imm()) \
  INST(JAL, 0, 1, "jal %s, %lx", rd(), j_imm()) \
  INST(JALR, 1, 1, "jalr %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(BLT,  2, 0, "blt %s, %s, %ld", rs1(), rs2(), b_imm()) \
  INST(BLTU, 2, 0, "bltu %s, %s, %ld", rs1(), rs2(), b_imm()) \
  INST(BGE,  2, 0, "bge %s, %s, %ld", rs1(), rs2(), b_imm()) \
  INST(BGEU, 2, 0, "bgeu %s, %s, %ld", rs1(), rs2(), b_imm()) \
  INST(BEQ, 2, 0, "beq %s, %s, %ld", rs1(), rs2(), b_imm()) \
  INST(BNE, 2, 0, "bne %s, %s, %ld", rs1(), rs2(), b_imm()) \
  INST(LB, 1, 1, "lb %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(LH, 1, 1, "lh %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(LW, 1, 1, "lw %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(LBU, 1, 1, "lbu %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(LHU, 1, 1, "lhu %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(SB, 2, 0, "sb %s, %ld(%s)", rs1(), s_imm(), rs2()) \
  INST(SH, 2, 0, "sh %s, %ld(%s)", rs1(), s_imm(), rs2()) \
  INST(SW, 2, 0, "sw %s, %ld(%s)", rs1(), s_imm(), rs2()) \
  INST(ADD, 2, 1, "add %s, %s, %s", rd(), rs1(), rs2()) \
  INST(ADDI, 1, 1, "addi %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(ADDIW, 1, 1, "addi.w %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(ADDW, 1, 1, "add.w %s, %s, %s", rd(), rs1(), rs2()) \
  INST(AND, 2, 1, "and %s, %s, %s", rd(), rs1(), rs2()) \
  INST(ANDI, 2, 1, "and %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(OR, 2, 1, "or %s, %s, %s", rd(), rs1(), rs2()) \
  INST(ORI, 1, 1, "ori %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(XOR,  2, 1, "xor %s, %s, %s", rd(), rs1(), rs2()) \
  INST(XORI,1, 1, "xori %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(SLL, 2, 1, "sll %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SLLI, 1, 1, "slli %s, %s, %ld", rd(), rs1(), shamt()) \
  INST(SLLIW,1, 1, "slli.w %s, %s, %ld", rd(), rs1(), shamt()) \
  INST(SLLW, 2, 1, "sll.w %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SLT, 2, 1, "slt %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SLTI,1, 1, "slti %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(SLTIU,1, 1, "sltiu %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(SLTU, 2, 1, "sltu %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SRA,  2, 1, "sra %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SRAI,1, 1, "srai %s, %s, %ld", rd(), rs1(), shamt()) \
  INST(SRAIW,1, 1, "srai.w %s, %s, %ld", rd(), rs1(), shamt()) \
  INST(SRAW, 2, 1, "sra.w %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SRL, 2, 1, "srl %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SRLI,1, 1, "srli %s, %s, %ld", rd(), rs1(), shamt()) \
  INST(SRLIW,1, 1, "srli.w %s, %s, %ld", rd(), rs1(), shamt()) \
  INST(SRLW, 2, 1, "srl.w %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SUB,  2, 1, "sub %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SUBW,  2, 1, "sub.w %s, %s, %s", rd(), rs1(), rs2()) \
  INST(EBREAK, 0, 0, "ebreak (%lx)", instr) \
  INST(ECALL, 0, 0, "ecall (%lx)", instr) \
  INST(FENCE, 0, 0, "fence %s", iorw()) \
  INST(LD, 1, 1, "ld %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(LWU, 1, 1, "lwu %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(SD, 2, 0, "sd %s, %ld(%s)", rs1(), s_imm(), rs2()) \
  /* RV32/RV64 Zifencei Standard Extension */ \
  INST(FENCE_I, 0, 0, "fence.i%c", 0) \
  /* RV32/RV64 Zicsr Standard Extension */ \
  INST(CSRRC,  1, 1, "csrrc %s, %s, %s", rd(), csr(), rs1()) \
  INST(CSRRCI, 0, 1, "csrrci %s, %s, %d", rd(), csr(), csr_uimm()) \
  INST(CSRRS,  1, 1, "csrrs %s, %s, %s", rd(), csr(), rs1()) \
  INST(CSRRSI, 0, 1, "csrrsi %s, %s, %d", rd(), csr(), csr_uimm()) \
  INST(CSRRW,  1, 1, "csrrw %s, %s, %s", rd(), csr(), rs1()) \
  INST(CSRRWI, 0, 1, "csrrwi %s, %s, %d", rd(), csr(), csr_uimm()) \
  /* RV32/RV64 M Standard Extension */ \
  INST(MUL, 2, 1, "mul %s, %s, %s", rd(), rs1(), rs2()) \
  INST(MULH, 2, 1, "mulh %s, %s, %s", rd(), rs1(), rs2()) \
  INST(MULHSU, 2, 1, "mulhsu %s, %s, %s", rd(), rs1(), rs2()) \
  INST(MULHU, 2, 1, "mulhu %s, %s, %s", rd(), rs1(), rs2()) \
  INST(DIV, 2, 1, "div %s, %s, %s", rd(), rs1(), rs2()) \
  INST(DIVU, 2, 1, "divu %s, %s, %s", rd(), rs1(), rs2()) \
  INST(REM, 2, 1, "rem %s, %s, %s", rd(), rs1(), rs2()) \
  INST(REMU, 2, 1, "remu %s, %s, %s", rd(), rs1(), rs2()) \
  INST(MULW, 2, 1, "mulw %s, %s, %s", rd(), rs1(), rs2()) \
  INST(DIVW, 2, 1, "divw %s, %s, %s", rd(), rs1(), rs2()) \
  INST(DIVUW, 2, 1, "divuw %s, %s, %s", rd(), rs1(), rs2()) \
  INST(REMW, 2, 1, "remw %s, %s, %s", rd(), rs1(), rs2()) \
  INST(REMUW, 2, 1, "remuw %s, %s, %s", rd(), rs1(), rs2())

#define DISASSIZE 64

#define INSTKK(MASK, MATCH, nrsrc, nrdst, str, ...) \
    else if((instr & MASK) == MATCH) { \
        nr_src = nrsrc; \
        nr_dst = nrdst; \
        snprintf(disas, DISASSIZE, str, __VA_ARGS__); \
    }

#define INST(key, nrsrc, nrdst, str, ...) \
    INSTKK(MASK_##key, MATCH_##key, nrsrc, nrdst, str, __VA_ARGS__)


extern const char* FloatRegNames[];
extern const char* IntRegNames[];
const char* csr_name(uint32_t csr_num);

class StaticInst {
    public:
    uint64_t instr;
    char disas[DISASSIZE];
    char nr_src;
    char nr_dst;
    char rsidx[3];
    char rdidx[1];
    uint64_t imm;
    bool valid;
    
    // Taken from     riscv-isa-sim/riscv/decode.h
    bool     y(int lo) { return (instr >> lo) & 1; }
    uint64_t x(int lo, int len) { return (instr >> lo) & ((uint64_t(1) << len) - 1); }
    uint64_t xs(int lo, int len) { return int64_t(instr) << (64 - lo - len) >> (64 - len); }
    uint64_t imm_sign() { return xs(31, 1); }

    int64_t i_imm() { return xs(20, 12); }
    int64_t shamt() { return x(20, 6); }
    int64_t s_imm() { return x(7, 5) + (xs(25, 7) << 5); }
    int64_t b_imm() { return (x(8, 4) << 1) + (x(25, 6) << 5) + (x(7, 1) << 11) + (imm_sign() << 12); }
    int64_t u_imm() { return xs(12, 20) << 12; }
    int64_t j_imm() { return (x(21, 10) << 1) + (x(20, 1) << 11) + (x(12, 8) << 12) + (imm_sign() << 20); }
    uint32_t _rd() { return x(7, 5); }
    uint32_t _rs1() { return x(15, 5); }
    uint32_t _rs2() { return x(20, 5); }
    uint32_t _rs3() { return x(27, 5); }
    uint32_t _rm() { return x(12, 3); }
    uint32_t _csr() { return x(20, 12); }
    uint32_t _iorw() { return x(20, 8); }
    uint32_t csr_uimm() { return _rs1(); }

    const char *rs1(){ return IntRegNames[_rs1()]; }
    const char *rs2(){ return IntRegNames[_rs2()]; }
    const char *rs3(){ return IntRegNames[_rs3()]; }
    const char *rd(){ return IntRegNames[_rd()]; }
    const char *csr(){ return csr_name(_csr()); }

    char *iorw() {
        static char buff[12]; // a bit hacky
        snprintf(buff, 12, "%c%c%c%c,%c%c%c%c",
            y(23) ? 'r' : '\0',
            y(22) ? 'w' : '\0',
            y(21) ? 'i' : '\0',
            y(20) ? 'o' : '\0',
            y(27) ? 'r' : '\0',
            y(26) ? 'w' : '\0',
            y(25) ? 'i' : '\0',
            y(24) ? 'o' : '\0');
        return buff;
    }

    public:
    StaticInst() = default;
    StaticInst(uint32_t instr_) {
        instr = instr_;
        valid = true;
        // Hardwired by default
        rdidx[0] = _rd();
        rsidx[0] = _rs1();
        rsidx[1] = _rs2();
        rsidx[2] = _rs3();
        do {
            if (0) {} INST_LIST()
            else {
                valid = false;
                nr_src = 0;
                nr_dst = 0;
                memcpy(disas, "unimp", 6);
            }
        } while(0);
    }

    char *getDisas(){ return disas; }
    bool isInst(){ return valid; }
};



