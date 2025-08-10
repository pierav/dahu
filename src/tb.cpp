#include "Vsystem.h"
#include "Vsystem___024root.h" // ugly bypass
#include "verilated.h"
#include <iostream>
#include <cstdint>
#include <chrono>
#include <getopt.h> // for getopt_long
#include <fstream>

#define RAM_KEY(root) ((void*)root->system__DOT__simram__DOT__mem.m_storage)
#define RAM_SIZE (1 << 20)

struct args_t {
    bool verbose = false;
    std::string binfile;
};

struct OptionHelp {
    const char* name;
    const char* argName; // NULL if no argument
    char        shortOpt;
    const char* description;
};

static const OptionHelp optionHelp[] = {
    {"verbose", nullptr, 'v', "Enable verbose output"},
    {"bin",     "FILE",  'b', "Binary file"},
    {"help",    nullptr, 'h', "Show this help message"},
};

// TODO: autobuild the long_option
static struct option long_options[] = {
    {"verbose", no_argument,       0, 'v'},
    {"bin",     required_argument, 0, 'b'},
    {"help",    no_argument,       0, 'h'},
    {0, 0, 0, 0} // end marker
};

void printHelp(const char* progName) {
    std::cout << "Usage: " << progName << " [options] [args...]\n\n";
    std::cout << "Options:\n";
    for (auto& opt : optionHelp) {
        std::cout << "  -" << opt.shortOpt << ", --" << opt.name;
        if(opt.argName) {
            std::cout << " <" << opt.argName << ">";
        }
        std::cout << "      " << opt.description << "\n";
    }
}

int parse_args(int argc, char *argv[], args_t &args) {
    int opt;
    int option_index = 0;
    while ((opt = getopt_long(argc, argv, "v:b:h", long_options, &option_index)) != -1) {
        switch (opt) {
            case 'v':
                args.verbose = true;
                break;
            case 'b':
                args.binfile = optarg;
                break;
            case 'h':
                printHelp(argv[0]);
                exit(0);
            case '?':
                // Unknown option
                std::cerr << "Unknown option '" << argv[optind-1] << "'\n";
                return 1;
        }
    }
    return 0;
}


/* Utils */ 
size_t readBinaryFile(const std::string& path, char* dst, size_t n) {
    std::ifstream file(path, std::ios::binary | std::ios::ate); // open at end to get size
    if (!file) {
        std::cerr << "Error: Cannot open file '" << path << "'\n";
        exit(1);
    }
    size_t size = file.tellg();
    if(size > n){
        std::cerr << "Error: file is too big " 
                  << size << " > " << n << std::endl;
    }
    file.seekg(0, std::ios::beg);
    file.read(dst, size);
    return size;
}


using namespace std::chrono;

high_resolution_clock::time_point t_start, t_end;

void tic(){
    t_start = high_resolution_clock::now();
}

void tac(){
    auto t_end = high_resolution_clock::now();
    auto millis = duration_cast<milliseconds>(t_end - t_start).count();
    std::cout << "WCT: " << millis << " ms" << std::endl;
    t_start = t_end;
}

int main(int argc, char **argv) {
    std::cout << "Hello from tb.cpp" << std::endl;
    
    // Parse args
    args_t args;
    parse_args(argc, argv, args);
    
    // Sanity checks
  

    tic();
    printf ("V = %d\n", VERILATOR_VERSION_INTEGER);
    Verilated::commandArgs(argc, argv);
    Vsystem* dut = new Vsystem;

    uint64_t cycles = 0;
    // Signals
    bool clk = true;
    bool rstn = true;
    bool exit_o = false;
    uint64_t exit_code_o = 0;

    // Simulation variables
    const uint64_t MAX_CYCLES = 10000000;  // max cycles to avoid infinite loop

    // Initialise ram
    char *ram = (char*)RAM_KEY(dut->rootp);
    readBinaryFile(args.binfile, ram, RAM_SIZE);

    // for(int i = 0; i < 100; i++){
    //     ram[i] = i;
    // }

    for (uint64_t i = 1; i < MAX_CYCLES; i++) {
        // Toggle clock every half cycle:
        clk = !clk;
        
        // Reset logic: hold rstn low for first 5 posedges of clk
        if (i < 10) { // 5 full cycles = 10 half cycles
            rstn = false;
        } else {
            rstn = true;
        }
        
        // Adjust inputs and evaluate design 
        dut->clk = clk;
        dut->rstn = rstn;
        dut->eval();
        if(clk){
            Verilated::timeInc(1);
        }
        
        // Count cycles on posedge clk
        if (clk) {
            cycles++;
            // Sample outputs
            exit_o = dut->exit_o;
            exit_code_o = dut->exit_code_o;
            if (exit_o) {
                if (exit_code_o != 0) {
                    std::cout << "FAILURE (cycle " << cycles << "): exitcode: " << exit_code_o << std::endl;
                } else {
                    std::cout << "SUCCESS: elapsed cycles: " << cycles << std::endl;
                }
                break; // exit simulation
            }
        }
        // Todo heartbeat ?
    }

    delete dut;
    std::cout << "Elapsed " << cycles << " cycles" << std::endl;
    tac();
    return 0;
}

