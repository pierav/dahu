
TOP = system
PKGS := src/riscv_pkg.sv src/C_pkg.sv src/core_oracle/handler_pkg.sv

SRC := $(PKGS) \
		$(wildcard src/isa/*.sv) \
		$(wildcard src/core/*.sv) \
		$(wildcard src/system/*.sv) \
		$(wildcard src/utils/*.sv) \
		$(wildcard src/arith/*.sv)

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

###
# Compliance
###

COMPLIANCE_DIR 	  := $(CURDIR)/benchs/RVAT/build
COMPLIANCE_SIMDIR := $(CURDIR)/simdir

COMPLIANCE_BENCHS := $(shell find $(COMPLIANCE_DIR) -type f)
COMPLIANCE_RUNS   := $(subst $(COMPLIANCE_DIR), \
							 $(COMPLIANCE_SIMDIR), \
							 $(COMPLIANCE_BENCHS:.elf=.run))

$(COMPLIANCE_SIMDIR)/%.run: $(COMPLIANCE_DIR)/%.elf
	./riscv-isa-sim/spike $<
	./build/Vsystem -b $< && echo OK || echo FAIL

run_compliance: $(COMPLIANCE_RUNS)

#######################################################
# Synth
#######################################################

synth.flist: force
	@echo $(addprefix $(CURDIR)/,$(SRC)) | sed -s 's/ /\n/g' > $@

force:
	@:




