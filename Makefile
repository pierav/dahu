

TOP = system
PKGS := src/C_pkg.sv
SRC := $(PKGS) $(wildcard src/system/*.sv)

VERILATOR := verilator/bin/verilator
		SVFLAGS :=  -Wall -Wpedantic \
	--cc src/tb.cpp --trace \
	--sv $(SRC) --Wno-DECLFILENAME --timing \
	--top-module $(TOP) \
	--exe --build \
	--Mdir build

EXEC := build/tb.elf

build: $(EXEC)

$(EXEC): $(SRC)
	mkdir -p $(@D)
	$(VERILATOR) $(SVFLAGS)

# 	$(MAKE) -C build


