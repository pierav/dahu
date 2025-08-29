
TOP = system
PKGS := src/C_pkg.sv src/core_oracle/handler_pkg.sv

SRC := $(PKGS) \
		$(wildcard src/isa/*.sv) \
		$(wildcard src/core/*.sv) \
		$(wildcard src/system/*.sv) \
		$(wildcard src/utils/*.sv)

SRC_DPI := $(wildcard src/tb/*.cpp) \
		   $(wildcard src/core_oracle/*.cc) \
		   $(wildcard src/cosim/*.cpp)

LIB_PATH = $(CURDIR)/src/cosim/riscv-isa-sim/build/lib/pkgconfig
pkgconf  = $(shell env PKG_CONFIG_PATH=$(LIB_PATH) pkg-config $1)
LIBS = riscv-riscv riscv-disasm riscv-fesvr

# 		  -std=c++2a -g -O2
CFLAGS := -std=c++2a -g -O2 $(call pkgconf, --cflags $(LIBS))
LDFLAGS :=  $(call pkgconf, --libs $(LIBS))

VERILATOR := verilator/bin/verilator
		SVFLAGS :=  -Wall -Wpedantic \
	--cc $(SRC_DPI)\
	--CFLAGS "$(CFLAGS) -I$(CURDIR)/src" \
	--LDFLAGS "$(LDFLAGS)" \
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



