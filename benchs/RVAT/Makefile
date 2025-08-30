MARCH 	:= rv64imafd_zicsr_zifencei

RATPATH := riscv-arch-test/riscv-test-suite
PREFIX 	:= /workx/TOOLCHAINS/default-13.2/bin/riscv64-unknown-linux-gnu-
CC 		:= $(PREFIX)gcc
LDFLAGS	:= -Tlink.ld
CFLAGS 	:= -g -static -mcmodel=medany -fvisibility=hidden \
			-nostdlib -nostartfiles -march=$(MARCH) -mabi=lp64d
INC		:= -I$(RATPATH)/env/ -I.
DEFINES	:= -DXLEN=64 -DTEST_CASE_1

RISCV_EXTS := I M

# TODO F D A Zifencei privilege vm_sv39/src
# TODO late CMO B

FILTER_IN = $(foreach key,$(1),$(foreach v,$(2),$(if $(findstring $(key),$(v)),$(v),)))

SRC := $(foreach e,$(RISCV_EXTS), \
	  		$(shell find $(RATPATH)/rv64i_m/$e/src -name '*.S' -type f))

BIN := $(subst $(RATPATH)/rv64i_m,build,$(SRC:.S=.elf))

$(info $(BIN))

all: $(BIN)

V ?= @

build/%.elf: $(RATPATH)/rv64i_m/%.S model_test.h $(RATPATH)/env/arch_test.h
	mkdir -p $(@D)
	$(CC) $(LDFLAGS) $(CFLAGS) $(INC) $(DEFINES) $< -o $@

%.out: %.elf
	$(V) spike $< && echo "[OK] spike $<" || echo "[FAILURE] spike $<"

run: $(BIN:.elf=.out)

clean:
	rm -rf $(bin)

