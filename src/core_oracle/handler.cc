// Using DPI for trace display and checking because
// I’m really too lazy to do it in functional SystemVerilog.

#include <string>
#include <cstdio>
#include <cstdint>
#include <inttypes.h>
#include <iostream>
#include <iomanip>
#include <cassert>
#include "svdpi.h"
#include <fstream>

#include "core_oracle/dyninst.hh"
#include "core_oracle/checker.hh"


checker_t checker;



#define MAX_INST_IDS 65536
#define LOGFILE "trace.log"

uint64_t cycle = 0;

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

#define LOG_ALL 1

static std::ostream& out = std::cout;
static std::ofstream _out;

extern "C" void dpi_monitor_init() {
    std::cout << "*** Hello for dpi (src/core_oracle/handle.cc)" << std::endl;
    inflight[0].id = -1;
    // _out.open("commit.log");
}

// Decode event
extern "C" void dpi_instr_decode(int id, uint64_t pc, uint32_t instr) {
    if(inflight[id % MAX_INST_IDS].id == id){ // Already inserted
        return;
    }
    DynamicInst di = DynamicInst(id, pc, instr);
    inflight[id] = di;
    if(LOG_ALL){
        out << "Decod:" << di << std::endl;
    }
    if(!di.si->isInst()){
        out << "Not a valid inst\n";
        exit(1);
    }
}

extern "C" void dpi_instr_renamed(
    int id, uint64_t pc,
    int prs1,
    bool prs1_renammed,
    int prs2,
    bool prs2_renammed,
    int prd
){
    // out << id << " rd:" << prd << " " << prs1 << " " << prs2 << std::endl;
    DynamicInst &inst = getInst(id, pc);
    if(inst.renammed){
        return;
    }
    inst.renammed = true;
    inst.prd = prd;
    inst.prs1 = prs1;
    inst.prs1_renammed = prs1_renammed;
    inst.prs2 = prs2;
    inst.prs2_renammed = prs2_renammed;
    if(LOG_ALL){
        out << "Renam:" << inst << std::endl;
    }
}

// Issue event TODO FMA
extern "C" void dpi_instr_issue(
    int id, uint64_t pc,
    uint64_t rs1val,
    uint64_t rs2val
) {
    DynamicInst &inst = getInst(id, pc);
    if(inst.issued){
        return;
    }
    inst.issued = true;
    inst.rsval[0] = rs1val;
    inst.rsval[1] = rs2val;
    inst.rsval[2] = 0;
    if(LOG_ALL){
        out << "Issue:" << inst << std::endl;
    }
}

// Write-Back event
extern "C" void dpi_instr_writeback(
    int id,
    uint64_t pc,
    uint64_t rdval
){
    DynamicInst &inst = getInst(id, pc);
    if(inst.writeback){
        return;
    }
    inst.writeback = true;
    inst.rdval[0] = rdval;
    if(LOG_ALL){
        out << "Wr-Ba:" << inst << std::endl;
    }
}

// Commit event
extern "C" void dpi_instr_commit(int id, uint64_t pc) {
    DynamicInst &inst = getInst(id, pc);
    // out << std::setw(16) << std::setfill('0') << std::right << std::dec
    //     << cycle << ": "
    inst.committed = true;
    out << "DPI-Commit: "
        << inst << std::endl;
    checker.on_commit(&inst);
}

// Handle time locally
extern "C" void dpi_tick() {
    cycle++;
    std::cout << "------------ cycle " 
              << cycle 
              << " -----------" << std::endl;
}

extern "C" const char* dpi_inst_get_dump(int id, uint64_t pc){
    static std::string tmp; // Small hack to preserve data
    DynamicInst &inst = getInst(id, pc);
    std::ostringstream oss;
    oss << inst;
    tmp = oss.str();
    const char* cstr = tmp.c_str();
    return cstr;
}
