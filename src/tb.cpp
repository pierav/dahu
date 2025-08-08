#include "Vsystem.h"
#include "verilated.h"
#include <iostream>
#include <cstdint>

int main(int argc, char **argv) {
    std::cout << "Hello from tb.cpp" << std::endl;

    Verilated::commandArgs(argc, argv);
    Vsystem* dut = new Vsystem;

    uint64_t cycles = 0;
    // Signals
    bool clk = true;
    bool rstn = true;
    bool exit_o = false;
    uint64_t exit_code_o = 0;

    // Simulation variables
    const uint64_t MAX_CYCLES = 1000000;  // max cycles to avoid infinite loop

    for (uint64_t i = 0; i < MAX_CYCLES; i++) {
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
    }

    delete dut;
    return 0;
}

