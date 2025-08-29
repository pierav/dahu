#include <string>

class dummy_simif_t;
class disassembler_t;
class processor_t;

class spike_harness_t {
    // IO handler
    dummy_simif_t *simif;
    disassembler_t* disassembler;
    processor_t *proc;
    
    public:
    spike_harness_t(std::vector<uint8_t>& memimage);
    std::string step1();

    public:
    uint64_t get_pc();
    uint64_t get_xreg(int reg);
    void set_xreg(int reg, uint64_t value);
};
