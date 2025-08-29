
PREFIX = /workx/TOOLCHAINS/default-13.2/bin/riscv64-unknown-linux-gnu-
CC 			= $(PREFIX)gcc
OBJDUMP		= $(PREFIX)objdump
OBJCOPY		= $(PREFIX)objcopy

SRC			:= $(wildcard *.S)
ELFS 		:= $(addprefix build/,$(SRC:.S=.elf))
BINS 		:= $(addprefix build/,$(SRC:.S=.bin))
DUMPS		:= $(addprefix build/,$(SRC:.S=.dump))

.PRESERVE: $(ELFS) $(BINS)

CFLAGS 		?= -mcmodel=medany -march=rv64imafd_zicsr_zifencei \
			   -static -std=gnu99 -g -O3 \
		  	   -fno-common -fno-builtin-printf \
			   -fno-tree-loop-distribute-patterns
		  		   
LDFLAGS 	?= -static \
			   -nostdlib -nostartfiles -nodefaultlibs \
			   -lm -lgcc \
		 	   -T ../common/test.ld -Wl,-no-whole-archive

all: $(DUMPS) $(BINS)

build/%.elf: %.S
	mkdir -p $(@D)
	$(CC) $(CFLAGS) $(LDFLAGS) $< -o $@

build/%.bin: build/%.elf
	$(OBJCOPY) -O binary $< $@

build/%.dump: build/%.elf
	$(OBJDUMP) -d $< > $@
