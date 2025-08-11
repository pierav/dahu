// Using DPI for trace display and checking because
// I’m really too lazy to do it in functional SystemVerilog.

#include <unordered_map>
#include <string>
#include <cstdio>
#include <cstdint>
#include <inttypes.h>
#include <iostream>
#include <iomanip>
#include <cassert>
#include "svdpi.h"
#include "core_oracle/isa.hh"

#define MAX_INST_IDS 65536
#define LOGFILE "trace.log"

using xlen_t = uint64_t;

/* Cache of static insts */
std::unordered_map<uint32_t /* opc*/, StaticInst> simap;

StaticInst* decode(uint32_t inst){
    if (!simap.count(inst)){
        simap[inst] = StaticInst(inst);
    }
    return &simap[inst];
}

uint64_t cycle = 0;

struct DynamicInst {
    xlen_t pc;
    StaticInst *si = nullptr;

    // Rename stage
    bool renammed = false;
    int prs1;
    bool prs1_renammed;
    int prs2;
    bool prs2_renammed;
    int prd;

    xlen_t rs1val;
    xlen_t rs2val;
    xlen_t rs3val;
    xlen_t rdval;

    bool issued;
    bool committed;

    DynamicInst() {};
    DynamicInst(xlen_t pc_, uint32_t inst) :
        pc(pc_), si(decode(inst)){};

    void dumpreg(std::ostream &os, std::string areg,
        int preg, int renammed) const {
        os << " " << areg;
        if (renammed){
            os << "\033[38;5;" << ((preg+16) * 97) % 256 << 'm';
            os << ":%";
            os << std::setfill('%') << std::setw(3) << preg;
            os << "\x1B[0m";
        } else {
            os << ":AREG";
        }
    }

    std::ostream& dump(std::ostream& os) const {
        os << std::setw(16) << std::right << cycle << ": "
           << std::setw(16) <<  std::setfill(' ') << std::hex << pc << ": "
           << "(" << std::setw(8) << std::setfill('0') << std::hex << si->instr << ") "
           << std::dec << std::setfill(' ') << si->getDisas();
        if (renammed) {
            os << '[';
            if(si->nr_dst){
                dumpreg(os, si->rd(), prd, true);
            }
            os << " <- ";
            if(si->nr_src >= 1){
                dumpreg(os, si->rs1(), prs1, prs1_renammed);
            }
            if(si->nr_src >= 2){
                dumpreg(os, si->rs2(), prs2, prs2_renammed);
            }
            os << " ]";
        }
        return os;
    }
};

std::ostream& operator<<(std::ostream& os, const DynamicInst& di) {
    return di.dump(os);
}

static DynamicInst inflight[MAX_INST_IDS];
static FILE* tracef = nullptr;

DynamicInst &getInst(int id, uint64_t pc){
    DynamicInst &inst = inflight[id % MAX_INST_IDS];
    assert(inst.pc == pc);
    assert(inst.si);
    return inst; 
}

// // DynamicInst stub
// struct rtl_si_t {
//     uint64_t    pc;    // PC of the instruction
//     uint32_t    tinst; // Assembly code
//     int         fu;    // functional unit to use
//     int         op;    // operation to perform
//     int         rs1;   // register source idx
//     bool        rs1_valid;
//     areg_id_t   rs2;   // register source idx
//     bool        rs2_valid;
//     areg_id_t   rd;    // register destination idx
//     bool        rd_valid;
//     uint64_t    imm;   // imm value
//     bool        valid; // Not UNIMP
// };

// struct rtl_di_t {
//     rtl_si_t    si;
//     int         id;
//     bool        fault;
//     bool        valid;
//     int         prs1;
//     int         prs2;
//     int         prd;
// };

extern "C" void dpi_instr_renamed(
    int id, uint64_t pc,
    int prs1,
    bool prs1_renammed,
    int prs2,
    bool prs2_renammed,
    int prd
){
    // std::cout << id << " rd:" << prd << " " << prs1 << " " << prs2 << std::endl;
    DynamicInst &inst = getInst(id, pc);
    inst.renammed = true;
    inst.prd = prd;
    inst.prs1 = prs1;
    inst.prs1_renammed = prs1_renammed;
    inst.prs2 = prs2;
    inst.prs2_renammed = prs2_renammed;
    std::cout << inst << std::endl;
}

extern "C" void dpi_monitor_init() {}

// Decode event
extern "C" void dpi_instr_decode(int id, uint64_t pc, uint32_t instr) {
    DynamicInst di = DynamicInst(pc, instr);
    inflight[id] = di;
    std::cout << di << std::endl;
    if(!di.si->isInst()){
        std::cout << "Not a valid inst\n";
        exit(1);
    }
}

// Issue event
extern "C" void dpi_instr_issue(int id, uint64_t pc, uint64_t rs1val, uint64_t rs2val, uint64_t rs3val) {
    DynamicInst &inst = getInst(id, pc);
    inst.rs1val = rs1val;
    inst.rs2val = rs2val;
    inst.rs3val = rs3val;
}

// Write-Back event
extern "C" void dpi_instr_writeback(int id, uint64_t pc, uint64_t rdval){
    DynamicInst &inst = getInst(id, pc);
    inst.rdval = rdval;
}

// Commit event
extern "C" void dpi_instr_commit(int id, uint64_t pc) {
    DynamicInst &inst = getInst(id, pc);
}

// Handle time locally
extern "C" void dpi_tick() {
    cycle++;
}
