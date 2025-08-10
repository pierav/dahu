
TOP = system
PKGS := src/C_pkg.sv src/core_oracle/handler_pkg.sv

SRC := $(PKGS) \
		$(wildcard src/isa/*.sv) \
		$(wildcard src/core/*.sv) \
		$(wildcard src/system/*.sv) \
		$(wildcard src/utils/*.sv)

SRC_DPI := $(wildcard src/core_oracle/*.cc)

VERILATOR := verilator/bin/verilator
		SVFLAGS :=  -Wall -Wpedantic \
	--cc $(SRC_DPI) src/tb.cpp \
	--CFLAGS "-I$(CURDIR)/src" \
	--trace \
	--sv $(SRC) --Wno-DECLFILENAME --timing \
	--Wno-UNUSEDSIGNAL \
	--Wno-IMPORTSTAR \
	--Wno-UNUSEDPARAM \
	--top-module $(TOP) \
	--exe --build \
	--Mdir build

EXEC := build/tb.elf

build: $(EXEC)

$(EXEC): $(SRC)
	mkdir -p $(@D)
	$(VERILATOR) $(SVFLAGS)



