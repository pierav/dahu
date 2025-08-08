#include "Vsystem.h"
#include "Vsystem___024root.h" // ugly bypass

#include "verilated.h"
#include <iostream>
#include <cstdint>
#include <chrono>

#define RAM_KEY(root) ((void*)root->system__DOT__simram__DOT__mem.m_storage)

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
    tic();

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
    
    printf ("V = %d\n", VERILATOR_VERSION_INTEGER);
    // Initialise ram
    uint64_t *ram = (uint64_t*)RAM_KEY(dut->rootp);
    for(int i = 0; i < 100; i++){
        ram[i] = i;
    }

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

