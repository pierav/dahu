# dahu

Yet Another RISC-V CPU

Application-class, 8-stage pipeline

# Zen


# Simulation

```sh
# Build golden model
cd src/cosim/riscv-isa-sim 
./configure --prefix=`realpath ./build`
make
# Build RTL with verilator
make
# Run simulation

```

# Asic Synthesis

# RISC-V

use `-march=rv64imafd_zicsr_zifencei`

# Roadmap

## Functional Baseline

[x] Implement PC / Fetch / Decode / Rename stages
[x] Implement IEW / Commit stages
[x] Add basic functional units: ALU, MUL, DIV, Branch Queue + Branch ALU
[x] Add base LSU: 16-entry SQ with partial STLF, 1-entry LQ
[x] Add UART (ns16650) HW model
[x] Pass riscv-arch-test for RV64 : I, M
[ ] Add interrupt controller & timer: PLIC + CLINT
[ ] Implement fault/exception handling across the full pipeline
[ ] Add virtual memory support: TLB + hardware Page Table Walker
[ ] Integrate boot ROM with device tree
[ ] Boot linux !
[ ] Add FPU one day...

## Performance

[ ] Model realistic memory latency
[ ] Add instruction cache (I$)
[ ] Add data cache (D$) with MSHRs based LQ
[ ] Implement branch predictor: BTB + RAS + IPRED + TAGE-like design
[ ] Widen pipeline: increase frontend, issue, and commit widths
[ ] Optimize writeback bandwidth (e.g., delayed WB scheduling)
[ ] Add B risc-v extension
[ ] Secrets plans haha

## Synthesis

[ ] Setup synthesis flow
[ ] Analyze critical paths (target: 2 GHz)
[ ] Try retiming for MUL and DIV fu

## Emulation

[ ] Find an fpga... and some time

# Some Cool Things to Try in Another Life

[ ] Optimize reservation station selection
[ ] Optimize PRF banking reads/writes with a funky allocation scheme
[ ] Uop cache enhancements for branch prediction (BP) and JIT execution
[ ] Instruction slice backing for L1D misses
[ ] Hardware automatic predication
[ ] Frontend early load execution
[ ] L2 coherent NoC with a funky software layer between bootloader and OS

