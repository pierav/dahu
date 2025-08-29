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
#include "cosim/spike_harness.hh"

#define NB_ID_BITS 20
#define MAX_INST_IDS (1 << NB_ID_BITS)
#define LOGFILE "trace.log"

#define LOG_ALL 0

static std::ostream& out = std::cout;
static std::ofstream _out;

spike_harness_t *cosim;
extern char *tb_binfile;
checker_t checker;
uint64_t cycle = 0;

static DynamicInst inflight[MAX_INST_IDS];
uint64_t push_cpt = 0, pop_cpt = 0;
uint64_t cnt = 0;

static FILE* tracef = nullptr;

DynamicInst &getInstUnsafe(int id){
    return inflight[id % MAX_INST_IDS];
}

DynamicInst &getInst(int id, uint64_t pc){
    DynamicInst &inst = getInstUnsafe(id);
    // std::cerr << "get inst at id=" 
    //           << std::hex << id << " pc=" << pc << " : "
    //           << inst << std::endl;
    if(inst.pc != pc) {
        fprintf(stderr, "Invalid PC %lx : extected %s", pc, inst.str());
    }
    assert(inst.pc == pc);
    assert(inst.si);
    return inst; 
}

DynamicInst &insertInst(int id, DynamicInst &inst){
    // std::cerr << "insertInst : id="  << std::hex << id << " : "
    //           << inst << std::endl;
    assert(cnt < 65536);
    assert(push_cpt % MAX_INST_IDS == id % MAX_INST_IDS);
    push_cpt ++;
    cnt ++;
    inflight[id % MAX_INST_IDS] = inst;
    return inflight[id % MAX_INST_IDS];
}

void squashFrom(DynamicInst &inst){
    // std::cerr << "SQUASH FROM " << inst << std::endl;
    uint64_t idx = inst.id;
    // Flush at commit only for now
    assert(idx % MAX_INST_IDS == pop_cpt % MAX_INST_IDS);
    // Move push cpt and update accordingly the count 
    push_cpt -= cnt -1;  // Clear all inflights (exclude ourserlf)
    cnt = 1;
    // while(1){
    //     if(inflight[idx % MAX_INST_IDS].id > id){ // TODO invalid care %N!!
            
    //         inflight_valid[idx % MAX_INST_IDS] = false;
    //     } else {
    //         break; // Stop loop
    //     }
    //     idx++;
    // }
}

void commitInst(DynamicInst &inst){
    // std::cerr << "Commit " << inst << std::endl;
    // Must commit the last
    assert(inst.id % MAX_INST_IDS == pop_cpt % MAX_INST_IDS);
    pop_cpt += 1;
    cnt -= 1;
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



void comsim_do_check_commit(DynamicInst &inst){
    // First check PC:
    fatal_if (cosim->get_pc() != inst.pc,
        "Invalid fetched PC : expected %016lx, got %016lx",
                cosim->get_pc(),
                inst.pc);
    // Check sources
    if(inst.si->nr_src >= 1){
        int idx = inst.si->_rs1();
        fatal_if (cosim->get_xreg(idx) != inst.rsval[0], "Invalid rs1");
    }
    if(inst.si->nr_src >= 2){
        int idx = inst.si->_rs2();
        fatal_if (cosim->get_xreg(idx) != inst.rsval[1], "Invalid rs2");
    }

    /* Do a cosim step */
    cosim->step1();

    if(inst.si->nr_dst){
        int idx = inst.si->_rd();
        uint64_t csr;
        if(inst.isCSR(csr) && 
            (csr == CSR_MCYCLE || csr == CSR_CYCLE ||
             csr == CSR_INSTRET || csr == CSR_MINSTRET)){
            // Fix the cosim time with the RTL time
            // TODO update internal csr before read ?
            cosim->set_xreg(idx, inst.rdval[0]);
        }
        fatal_if (cosim->get_xreg(idx) != inst.rdval[0],
            "Invalid rd : expected %016lx, got %016lx",
                cosim->get_xreg(idx),
                inst.rdval[0]);
    }
    

    /* Todo check CSR */
}

extern "C" void dpi_monitor_init() {
    std::cout << "*** Hello for dpi (src/core_oracle/handle.cc)" << std::endl;
    inflight[0].id = -1;
    // _out.open("commit.log");
    assert(cosim);
    // for(int i = 0; i < 100; i++){
    //     std::cout << cosim->step1() << std::endl;
    // }
}

// Decode event
extern "C" void dpi_instr_decode(
    int id,
    uint64_t pc,
    uint32_t instr,
    uint32_t is_uop,
    uint32_t is_uop_last
){
    DynamicInst _inst = DynamicInst(id, pc, instr, is_uop, is_uop_last);
    DynamicInst &inst = insertInst(id, _inst);

    if(LOG_ALL){
        out << "Decod:" << inst << std::endl;
        out << " is_uop " << is_uop <<  " is_uop_last" << is_uop_last << std::endl;
    }
    // if(!inst.si->isInst()){
    //     out << "Not a valid inst\n";
    //     exit(1);
    // }
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
    #if LOG_ALL
    out << "DPI-Commit: "
        << inst << std::endl;
    checker.on_commit(&inst);
    #endif
    commitInst(inst);
    // Ignore the uop decomposition : only check arch state
    if(!inst.is_uop || (inst.is_uop && inst.is_uop_last)){
        comsim_do_check_commit(inst);
    }
    
}

// Handle time locally
extern "C" void dpi_tick() {
    cycle++;
    #if LOG_ALL
    std::cout << "------------ cycle " 
              << cycle 
              << " -----------" << std::endl;
    #endif
}

extern "C" void dpi_squash_from(int id) {
    DynamicInst &inst = getInstUnsafe(id);
    squashFrom(inst);
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
