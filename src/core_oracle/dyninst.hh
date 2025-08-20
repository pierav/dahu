#pragma once

#include <string>
#include <cstdio>
#include <cstdint>
#include <inttypes.h>
#include "core_oracle/isa.hh"
#include "core_oracle/utils.hh"


struct DynamicInst {
    using xlen_t = uint64_t;

    uint64_t id;
    xlen_t pc;
    const StaticInst *si = nullptr;
    

    // Rename stage
    bool renammed = false;
    int prs1;
    bool prs1_renammed;
    int prs2;
    bool prs2_renammed;
    int prd;

    // issue stage
    bool issued = false;
    xlen_t rsval[3];

    // Ex stage
    bool executed = false;
    xlen_t rdval[1];

    // Writeback
    bool writeback = false;

    // Commit stage
    bool committed = false;

    DynamicInst() {};
    DynamicInst(uint64_t id_, xlen_t pc_, uint32_t inst) :
        id(id_), pc(pc_), si(StaticInst::decode(inst)){};

    void dumpreg(std::ostream &os, std::string areg,
        int preg, int renammed) const {
        os << " " << areg;
        if (renammed){
            os << "\033[38;5;" << std::dec
               << ((preg+16) * 97) % 256 << 'm';
            os << ":%";
            os << std::setfill('%') << std::setw(3) << preg;
            os << "\x1B[0m";
        } else {
            os << ":AREG";
        }
    }

    bool isLoad(uint64_t& addr, uint8_t& size, uint64_t& rdata){
        assert(si);
        assert(committed);
        if(si->type == TYPE_LOAD){
            size = si->size;
            addr = rsval[0] + si->i_imm();
            rdata = rdval[0];
            return true;
        }
        return false;
    }

    bool isStore(uint64_t& addr, uint8_t& size, uint64_t& wdata){
        assert(si);
        assert(committed);
        if(si->type == TYPE_STORE){
            size = si->size;
            addr = rsval[0] + si->s_imm();
            wdata = rsval[1];
            return true;
        }
        return false;
    }

    std::ostream& dump(std::ostream& os) const {
        os << std::setw(16) << std::setfill(' ') << std::hex 
           << pc << ": "
           << "(sn=" << std::setfill('0') << std::setw(3) << std::hex
           << id << ") "
           << "(" << std::setw(8) << std::setfill('0') << std::hex << si->instr << ") "
           << std::left << std::setw(25) << std::setfill(' ')
           << si->getDisas();
        if (renammed) {
            os << '[';
            if(si->nr_dst){
                dumpreg(os, si->rd(), prd, true);
                if(writeback){
                    os << ":" << std::right << std::setw(16) << std::setfill('0') << std::hex
                       << rdval[0];
                }
            }
            os << " <- ";
            if(si->nr_src >= 1){
                dumpreg(os, si->rs1(), prs1, prs1_renammed);
                if(issued){
                    os << ":" << std::right << std::setw(16) << std::setfill('0') << std::hex
                       << rsval[0];
                }
            }
            if(si->nr_src >= 2){
                dumpreg(os, si->rs2(), prs2, prs2_renammed);
                if(issued){
                    os << ":" << std::right << std::setw(16) << std::setfill('0') << std::hex
                       << rsval[1];
                }
            }
            os << " ]";
        }
        return os;
    }

    const char* str() const {
        static std::string s;
        std::ostringstream oss;
        dump(oss);
        s = oss.str();
        return s.c_str();
    }
};

std::ostream& operator<<(std::ostream& os, const DynamicInst& di) {
    return di.dump(os);
}
