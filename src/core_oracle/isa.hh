#pragma once

#include "core_oracle/encoding.h"
#include "core_oracle/utils.hh"
#include <cstring>
#include <string>
#include <cstdio>
#include <cstdint>
#include <inttypes.h>
#include <unordered_map>

enum inst_type_t {
    TYPE_MISC,
    TYPE_CSR,
    TYPE_LOAD,
    TYPE_STORE,
    TYPE_AMO,
    TYPE_ALU,
    TYPE_FPU,
    TYPE_CTRL,
};

#define INST_LIST() \
  /* Trap-Return Instructions */   \
  INST(SRET,    0, 0, TYPE_MISC, 8, "sret%c", 0) \
  INST(MRET,    0, 0, TYPE_MISC, 8, "mret%c", 0) \
  /* Interrupt-Management Instructions */ \
  INST(WFI,     0, 0, TYPE_MISC, 8, "wfi%c", 0) \
  /* RV32/RV64 I Base Instruction Set */ \
  INST(LUI,     0, 1, TYPE_ALU,  8, "lui %s, %ld", rd(), u_imm()) \
  INST(AUIPC,   0, 1, TYPE_ALU,  8, "auipc %s, %ld", rd(), u_imm()) \
  INST(JAL,     0, 1, TYPE_CTRL, 8, "jal %s, %lx", rd(), j_imm()) \
  INST(JALR,    1, 1, TYPE_CTRL, 8, "jalr %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(BLT,     2, 0, TYPE_CTRL, 8, "blt %s, %s, %ld", rs1(), rs2(), b_imm()) \
  INST(BLTU,    2, 0, TYPE_CTRL, 8, "bltu %s, %s, %ld", rs1(), rs2(), b_imm()) \
  INST(BGE,     2, 0, TYPE_CTRL, 8, "bge %s, %s, %ld", rs1(), rs2(), b_imm()) \
  INST(BGEU,    2, 0, TYPE_CTRL, 8, "bgeu %s, %s, %ld", rs1(), rs2(), b_imm()) \
  INST(BEQ,     2, 0, TYPE_CTRL, 8, "beq %s, %s, %ld", rs1(), rs2(), b_imm()) \
  INST(BNE,     2, 0, TYPE_CTRL, 8, "bne %s, %s, %ld", rs1(), rs2(), b_imm()) \
  INST(LB,      1, 1, TYPE_LOAD, 1, "lb %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(LH,      1, 1, TYPE_LOAD, 2, "lh %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(LW,      1, 1, TYPE_LOAD, 4, "lw %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(LD,      1, 1, TYPE_LOAD, 8, "ld %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(LBU,     1, 1, TYPE_LOAD, 1, "lbu %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(LHU,     1, 1, TYPE_LOAD, 2, "lhu %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(LWU,     1, 1, TYPE_LOAD, 4, "lwu %s, %ld(%s)", rd(), i_imm(), rs1()) \
  INST(SB,      2, 0, TYPE_STORE,1, "sb %s, %ld(%s)", rs2(), s_imm(), rs1()) \
  INST(SH,      2, 0, TYPE_STORE,2, "sh %s, %ld(%s)", rs2(), s_imm(), rs1()) \
  INST(SW,      2, 0, TYPE_STORE,4, "sw %s, %ld(%s)", rs2(), s_imm(), rs1()) \
  INST(SD,      2, 0, TYPE_STORE,8, "sd %s, %ld(%s)", rs2(), s_imm(), rs1()) \
  INST(ADD,     2, 1, TYPE_ALU,  8, "add %s, %s, %s", rd(), rs1(), rs2()) \
  INST(ADDI,    1, 1, TYPE_ALU,  8, "addi %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(ADDIW,   1, 1, TYPE_ALU,  4, "addi.w %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(ADDW,    1, 1, TYPE_ALU,  4, "add.w %s, %s, %s", rd(), rs1(), rs2()) \
  INST(AND,     2, 1, TYPE_ALU,  8, "and %s, %s, %s", rd(), rs1(), rs2()) \
  INST(ANDI,    1, 1, TYPE_ALU,  8, "and %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(OR,      2, 1, TYPE_ALU,  8, "or %s, %s, %s", rd(), rs1(), rs2()) \
  INST(ORI,     1, 1, TYPE_ALU,  8, "ori %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(XOR,     2, 1, TYPE_ALU,  8, "xor %s, %s, %s", rd(), rs1(), rs2()) \
  INST(XORI,    1, 1, TYPE_ALU,  8, "xori %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(SLL,     2, 1, TYPE_ALU,  8, "sll %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SLLI,    1, 1, TYPE_ALU,  8, "slli %s, %s, %ld", rd(), rs1(), shamt()) \
  INST(SLLIW,   1, 1, TYPE_ALU,  4, "slli.w %s, %s, %ld", rd(), rs1(), shamt()) \
  INST(SLLW,    2, 1, TYPE_ALU,  4, "sll.w %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SLT,     2, 1, TYPE_ALU,  8, "slt %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SLTI,    1, 1, TYPE_ALU,  8, "slti %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(SLTIU,   1, 1, TYPE_ALU,  8, "sltiu %s, %s, %ld", rd(), rs1(), i_imm()) \
  INST(SLTU,    2, 1, TYPE_ALU,  8, "sltu %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SRA,     2, 1, TYPE_ALU,  8, "sra %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SRAI,    1, 1, TYPE_ALU,  8, "srai %s, %s, %ld", rd(), rs1(), shamt()) \
  INST(SRAIW,   1, 1, TYPE_ALU,  4, "srai.w %s, %s, %ld", rd(), rs1(), shamt()) \
  INST(SRAW,    2, 1, TYPE_ALU,  4, "sra.w %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SRL,     2, 1, TYPE_ALU,  8, "srl %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SRLI,    1, 1, TYPE_ALU,  8, "srli %s, %s, %ld", rd(), rs1(), shamt()) \
  INST(SRLIW,   1, 1, TYPE_ALU,  4, "srli.w %s, %s, %ld", rd(), rs1(), shamt()) \
  INST(SRLW,    2, 1, TYPE_ALU,  4, "srl.w %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SUB,     2, 1, TYPE_ALU,  8, "sub %s, %s, %s", rd(), rs1(), rs2()) \
  INST(SUBW,    2, 1, TYPE_ALU,  4, "sub.w %s, %s, %s", rd(), rs1(), rs2()) \
  INST(EBREAK,  0, 0, TYPE_MISC, 8, "ebreak (%lx)", instr) \
  INST(ECALL,   0, 0, TYPE_MISC, 8, "ecall (%lx)", instr) \
  INST(FENCE,   0, 0, TYPE_MISC, 8, "fence %s", iorw()) \
  /* RV32/RV64 Zifencei Standard Extension */ \
  INST(FENCE_I, 0, 0, TYPE_MISC, 8, "fence.i%c", 0) \
  /* RV32/RV64 Zicsr Standard Extension */ \
  INST(CSRRC,   1, 1, TYPE_CSR,  8, "csrrc %s, %s, %s", rd(), csr(), rs1()) \
  INST(CSRRCI,  0, 1, TYPE_CSR,  8, "csrrci %s, %s, %d", rd(), csr(), csr_uimm()) \
  INST(CSRRS,   1, 1, TYPE_CSR,  8, "csrrs %s, %s, %s", rd(), csr(), rs1()) \
  INST(CSRRSI,  0, 1, TYPE_CSR,  8, "csrrsi %s, %s, %d", rd(), csr(), csr_uimm()) \
  INST(CSRRW,   1, 1, TYPE_CSR,  8, "csrrw %s, %s, %s", rd(), csr(), rs1()) \
  INST(CSRRWI,  0, 1, TYPE_CSR,  8, "csrrwi %s, %s, %d", rd(), csr(), csr_uimm()) \
  /* RV32/RV64 M Standard Extension */ \
  INST(MUL,     2, 1, TYPE_ALU,  8, "mul %s, %s, %s", rd(), rs1(), rs2()) \
  INST(MULH,    2, 1, TYPE_ALU,  8, "mulh %s, %s, %s", rd(), rs1(), rs2()) \
  INST(MULHSU,  2, 1, TYPE_ALU,  8, "mulhsu %s, %s, %s", rd(), rs1(), rs2()) \
  INST(MULHU,   2, 1, TYPE_ALU,  8, "mulhu %s, %s, %s", rd(), rs1(), rs2()) \
  INST(DIV,     2, 1, TYPE_ALU,  8, "div %s, %s, %s", rd(), rs1(), rs2()) \
  INST(DIVU,    2, 1, TYPE_ALU,  8, "divu %s, %s, %s", rd(), rs1(), rs2()) \
  INST(REM,     2, 1, TYPE_ALU,  8, "rem %s, %s, %s", rd(), rs1(), rs2()) \
  INST(REMU,    2, 1, TYPE_ALU,  8, "remu %s, %s, %s", rd(), rs1(), rs2()) \
  INST(MULW,    2, 1, TYPE_ALU,  4,  "mulw %s, %s, %s", rd(), rs1(), rs2()) \
  INST(DIVW,    2, 1, TYPE_ALU,  4,  "divw %s, %s, %s", rd(), rs1(), rs2()) \
  INST(DIVUW,   2, 1, TYPE_ALU,  4,  "divuw %s, %s, %s", rd(), rs1(), rs2()) \
  INST(REMW,    2, 1, TYPE_ALU,  4,  "remw %s, %s, %s", rd(), rs1(), rs2()) \
  INST(REMUW,   2, 1, TYPE_ALU,  4,  "remuw %s, %s, %s", rd(), rs1(), rs2())

#define DISASSIZE 64

#define INSTKK(MASK, MATCH, nrsrc, nrdst, type_, size_, str, ...) \
    else if((instr & MASK) == MATCH) { \
        nr_src = nrsrc; \
        nr_dst = nrdst; \
        type =  type_; \
        size = size_; \
        snprintf(disas, DISASSIZE, str, __VA_ARGS__); \
    }

#define INST(key, nrsrc, nrdst, type, size, str, ...) \
    INSTKK(MASK_##key, MATCH_##key, nrsrc, nrdst, type, size, str, __VA_ARGS__)


extern const char* FloatRegNames[];
extern const char* IntRegNames[];
const char* csr_name(uint32_t csr_num);
inline const char* reg_name(int reg) {
    if(reg < 32) {
        return IntRegNames[reg];
    } else if (reg < 64){
        return FloatRegNames[reg];
    } else {
        fatal("Invalid register %s !", reg);
        return "";
    }
}

class StaticInst {
    public:
    uint64_t instr;
    char disas[DISASSIZE];
    char nr_src;
    char nr_dst;
    inst_type_t type;
    char size;

    char rsidx[3];
    char rdidx[1];
    uint64_t imm;
    bool valid;
    
    // Taken from     riscv-isa-sim/riscv/decode.h
    bool     y(int lo) const { return (instr >> lo) & 1; }
    uint64_t x(int lo, int len) const { return (instr >> lo) & ((uint64_t(1) << len) - 1); }
    uint64_t xs(int lo, int len) const { return int64_t(instr) << (64 - lo - len) >> (64 - len); }
    uint64_t imm_sign() const { return xs(31, 1); }

    int64_t i_imm() const { return xs(20, 12); }
    int64_t shamt() const { return x(20, 6); }
    int64_t s_imm() const { return x(7, 5) + (xs(25, 7) << 5); }
    int64_t b_imm() const { return (x(8, 4) << 1) + (x(25, 6) << 5) + (x(7, 1) << 11) + (imm_sign() << 12); }
    int64_t u_imm() const { return xs(12, 20) << 12; }
    int64_t j_imm() const { return (x(21, 10) << 1) + (x(20, 1) << 11) + (x(12, 8) << 12) + (imm_sign() << 20); }
    uint32_t _rd()  const { return x(7, 5); }
    uint32_t _rs1() const { return x(15, 5); }
    uint32_t _rs2() const { return x(20, 5); }
    uint32_t _rs3() const { return x(27, 5); }
    uint32_t _rm()  const { return x(12, 3); }
    uint32_t _csr() const { return x(20, 12); }
    uint32_t _iorw()const { return x(20, 8); }
    uint32_t csr_uimm() const { return _rs1(); }

    const char *rs1() const { return IntRegNames[_rs1()]; }
    const char *rs2() const { return IntRegNames[_rs2()]; }
    const char *rs3() const { return IntRegNames[_rs3()]; }
    const char *rd()  const { return IntRegNames[_rd()]; }
    const char *csr() const { return csr_name(_csr()); }

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
        // Clear rd is x0
        if(nr_dst && rdidx[0] == 0){
            nr_dst = 0;
        }
    }

    const char *getDisas() const { return disas; }
    bool isInst() const { return valid; }
    
    static const StaticInst* decode(uint32_t inst);
};



