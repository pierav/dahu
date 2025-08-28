#pragma once
#include "core_oracle/memory.hh"
#include "core_oracle/dyninst.hh"

struct checker_t {
    InfiniteMemory64 mem_checker;

    uint64_t rf[64];
    bool rfinit[64] = { 0 };

    void on_commit(DynamicInst* inst){
        check_reg(inst);
        check_mem(inst);
    }

    bool isBufferable(uint64_t paddr){
        return paddr >= 0x80000000 && paddr < 0x90000000; // TODO
    }

    void check_mem(DynamicInst* inst){
        uint64_t addr, rwdata;
        uint8_t size;
        // TODO: check bufferable (no io...)
        
        if(inst->isLoad(addr, size, rwdata)){
            if(isBufferable(addr)){
                mem_checker.check_load(addr, size, rwdata);
            }
        } else if(inst->isStore(addr, size, rwdata)){
            if(isBufferable(addr)){
                mem_checker.check_store(addr, size, rwdata);
            }
        }
    }

    void check_reg(DynamicInst* inst){
        // 0) Check src
        for(int i = 0; i < inst->si->nr_src; i++){
            const char reg = inst->si->rsidx[i];
            uint64_t val =  inst->rsval[i];
            if (!rfinit[reg]){ // For simpoint
                rf[reg] = val;
            }
            fatal_if(rf[reg] != val,
                "reg %s must be equal to %lx not %lx :: %s\n",
                reg_name(reg), rf[reg], val, inst->str());
        }

        // 1) Apply dsts
        for(int i = 0; i < inst->si->nr_dst; i++){
            const char reg = inst->si->rdidx[i];
            uint64_t val = inst->rdval[i];
            rf[reg] = val;
            rfinit[reg] = true;
            // std::cout << "Write " << val << " at id " << reg_name(reg) << std::endl;
        }
    }

};

