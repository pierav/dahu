#include "riscv/sim.h"
#include "riscv/processor.h"
#include "riscv/decode.h"
#include "riscv/cfg.h"
#include "riscv/mmu.h"
#include "riscv/decode.h"
#include "riscv/disasm.h"

#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <cstdint>
#include <cstring>

#define MYISA "rv64imafd"

#define BASE_ADDR 0x80000000
char host_mem[1024 * 1024]; // backing storage

struct mymem_t {
    const reg_t base_addr = BASE_ADDR;
    const reg_t mem_size  = 1024 * 1024; // 128 MB

    // Load 'size' bytes from memory at 'addr' into 'ret'
    bool load(reg_t addr, size_t size, uint8_t* ret) {
        if (addr < base_addr || addr + size > base_addr + mem_size) {
            std::cerr << "Load out of bounds: addr=0x" << std::hex << addr
                      << " size=" << std::dec << size << std::endl;
            return false;
        }
        std::memcpy(ret, host_mem + (addr - base_addr), size);
        // std::cout << "Load: addr=0x" << std::hex << addr
        //           << " size=" << std::dec << size << " data=";
        // for (size_t i = 0; i < size; i++)
        //     std::cout << std::hex << +ret[i] << " ";
        // std::cout << std::endl;
        return true;
    }

    // Store 'size' bytes from 'data' into memory at 'addr'
    bool store(reg_t addr, size_t size, const uint8_t* data) {
        if (addr < base_addr || addr + size > base_addr + mem_size) {
            std::cerr << "Store out of bounds: addr=0x" << std::hex << addr
                      << " size=" << std::dec << size << std::endl;
            return false;
        }
        std::memcpy(host_mem + (addr - base_addr), data, size);
        // std::cout << "Store: addr=0x" << std::hex << addr
        //           << " size=" << std::dec << size << " data=";
        // for (size_t i = 0; i < size; i++)
        //     std::cout << std::hex << +data[i] << " ";
        // std::cout << std::endl;
        return true;
    }
};


struct dummy_simif_t : public simif_t {
    mymem_t mem;
    cfg_t cfg;
    std::map<size_t, processor_t*> harts;

    dummy_simif_t() {
        cfg.isa = MYISA;
        cfg.priv = DEFAULT_PRIV;
    }
    char* addr_to_mem(reg_t paddr) override {
        char *ret = host_mem + paddr - BASE_ADDR;
        // std::cout << "SIMIF addr_2_mem:" << std::hex << paddr << "->" << (uintptr_t)ret << std::endl;
        return ret;
    }

    virtual bool mmio_load(reg_t paddr, size_t len, uint8_t* bytes) override {
        return mem.load(paddr, len, bytes);
    }

    virtual bool mmio_store(reg_t paddr, size_t len, const uint8_t* bytes) override {
        return mem.store(paddr, len, bytes);
    };
  
    // Callback for processors to let the simulation know they were reset.
    void proc_reset(unsigned id) override {
        std::cout << "Resetted " << id << std::endl;
    }

    const cfg_t& get_cfg() const override {
        return cfg;
    }
    
    const std::map<size_t, processor_t*>& get_harts() const override { 
        return harts;
    }
    
    const char* get_symbol(uint64_t) override { 
        return nullptr;
    }
};

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " program.bin" << std::endl;
        return 1;
    }

    // load binary file
    std::ifstream bin(argv[1], std::ios::binary | std::ios::ate);
    if (!bin) { std::cerr << "cannot open " << argv[1] << std::endl; return 1; }
    size_t size = bin.tellg();
    bin.seekg(0);
    std::vector<char> buf(size);
    bin.read(buf.data(), size);
    const uint8_t* binptr = reinterpret_cast<const uint8_t*>(buf.data());
    
    std::cout << "Initialize mem with bin " << argv[1] << std::endl;
    // memory region
   
    dummy_simif_t simif;
    // Write program in memory
    std::memmove(host_mem, binptr, size);

    // Create processor
    processor_t proc("RV64IM", "MSU", &simif.cfg, &simif, 0, false, nullptr, std::cout);

    std::cout << "Initialise proc PC to" << BASE_ADDR << std::endl;
    // Set PC to start of binary
    proc.get_state()->pc = BASE_ADDR;


    isa_parser_t isa_parser(MYISA, DEFAULT_PRIV);
    disassembler_t* disassembler = new disassembler_t(&isa_parser);

    // Step instructions
    for (int i = 0; i < 200; i++) {
        auto* st = proc.get_state();
        reg_t pc = st->pc;

        // Fetch 32-bit instruction from memory
        uint32_t insn_bits = 0;
        if (!simif.mmio_load(pc, sizeof(insn_bits), reinterpret_cast<uint8_t*>(&insn_bits))) {
            std::cerr << "Fetch fail at PC=0x" << std::hex << pc << std::endl;
            break;
        }

        // Decode instruction
        insn_t insn = insn_t(insn_bits);

        // Read Source registers (if any)
        int rs1 = insn.rs1();
        int rs2 = insn.rs2();
        reg_t rs1_val = (rs1 != 0) ? st->XPR[rs1] : 0;
        reg_t rs2_val = (rs2 != 0) ? st->XPR[rs2] : 0;

        // Disassemble
        std::string disasm_str = disassembler->disassemble(insn);
    
        // Step one instruction
        proc.step(1);

        // Destination register (if any)
        int rd = insn.rd();
        reg_t rd_val = (rd != 0) ? st->XPR[rd] : 0;
        
        std::cout << std::hex << pc << ": 0x" << insn_bits
                << "  " << disasm_str;
        if (rd != 0)  { 
            std::cout << " rd=x"  << rd  << "=" << std::hex << rd_val;
        }
        if (rs1 != 0) { 
            std::cout << " rs1=x" << rs1 << "=" << std::hex << rs1_val;
        }
        if (rs2 != 0) { 
            std::cout << " rs2=x" << rs2 << "=" << std::hex << rs2_val; 
        }
        std::cout << std::endl;
    }

    return 0;
}
