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
    spike_harness_t(char *binfile);
    std::string step1();
};