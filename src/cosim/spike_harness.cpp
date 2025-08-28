#include "riscv/sim.h"
#include "riscv/processor.h"
#include "riscv/decode.h"
#include "riscv/cfg.h"
#include "riscv/mmu.h"
#include "riscv/decode.h"
#include "riscv/disasm.h"
#include "riscv/devices.h"
#include "riscv/platform.h"

#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <cstdint>
#include <cstring>

#include "cosim/spike_harness.hh"

#define MYISA "rv64imafd"
#define RAM_BASE DRAM_BASE
#define RAM_SIZE (1 << 20)

struct dummy_simif_t : public simif_t {
    cfg_t cfg;
    bus_t bus;
    std::map<size_t, processor_t*> harts;

    dummy_simif_t(size_t nprocs = 1) {
        cfg.isa  = MYISA;
        cfg.priv = DEFAULT_PRIV;
        mem_t* ram = new mem_t(RAM_SIZE);
        clint_t* clint = new clint_t(this, 10000000 /*10 MHz*/, false);
        plic_t* plic = new plic_t(this, 1024);
        ns16550_t* uart = new ns16550_t(plic, 1, 0, 1);
        bus.add_device(RAM_BASE, ram);
        bus.add_device(CLINT_BASE, clint);
        bus.add_device(PLIC_BASE, plic);
        bus.add_device(NS16550_BASE, uart);
    }

    char* addr_to_mem(reg_t addr) override {
       return nullptr;
    }

    bool mmio_load(reg_t addr, size_t len, uint8_t* bytes) override {
        return bus.load(addr, len, bytes);
    }

    bool mmio_store(reg_t addr, size_t len, const uint8_t* bytes) override {
        return bus.store(addr, len, bytes);
    }
  
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


spike_harness_t::spike_harness_t(char *binfile) {
    simif = new dummy_simif_t();

    // load binary file
    std::ifstream bin(binfile, std::ios::binary | std::ios::ate);
    if (!bin) {
        std::cerr << "cannot open " << binfile << std::endl;
    }
    size_t size = bin.tellg();
    bin.seekg(0);
    std::vector<char> buf(size);
    bin.read(buf.data(), size);
    const uint8_t* binptr = reinterpret_cast<const uint8_t*>(buf.data());
    
    std::cout << "Initialize mem with bin " << binfile << std::endl;
    
    // Write program in memory
    simif->mmio_store(RAM_BASE, size, binptr);

    // Create processor
    proc = new processor_t("RV64IM", "MSU",
        &simif->cfg, simif, 0, false, nullptr, std::cout);

    std::cout << "Initialise proc PC to" << RAM_BASE << std::endl;
    // Set PC to start of binary
    proc->get_state()->pc = RAM_BASE;

    isa_parser_t isa_parser(MYISA, DEFAULT_PRIV);
    disassembler = new disassembler_t(&isa_parser);
}

std::string spike_harness_t::step1(){
    auto* st = proc->get_state();
    reg_t pc = st->pc;

    // Fetch 32-bit instruction from memory
    uint32_t insn_bits = 0;
    if (!simif->mmio_load(pc, sizeof(insn_bits), reinterpret_cast<uint8_t*>(&insn_bits))) {
        std::cerr << "Fetch fail at PC=0x" << std::hex << pc << std::endl;
        abort();
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
    proc->step(1);

    // Destination register (if any)
    if(0) {
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
    return disasm_str;
}


uint64_t spike_harness_t::get_pc(){
    return proc->get_state()->pc;
}

uint64_t spike_harness_t::get_xreg(int reg){
    return proc->get_state()->XPR[reg];
}



int mainx(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " program.bin" << std::endl;
        return 1;
    }

    spike_harness_t sh(argv[1]);

    // Step instructions
    for (int i = 0;; i++) {
        sh.step1();
    }

    return 0;
}
