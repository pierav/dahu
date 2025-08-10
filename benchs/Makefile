benchs = dhrystone

# -save-temps -dP

all: build/dhrystone.dump build/dhrystone.bin

PREFIX = /workx/TOOLCHAINS/default-13.2/bin/riscv64-unknown-linux-gnu-
CC 			= $(PREFIX)gcc
OBJDUMP		= $(PREFIX)objdump
OBJCOPY		= $(PREFIX)objcopy


# https://gcc.gnu.org/onlinedocs/gcc/RISC-V-Options.html

CFLAGS 		?= -mcmodel=medany -march=rv64imafd_zicsr_zifencei \
			   -static -std=gnu99 -g -O3 \
		  	   -fno-common -fno-builtin-printf \
			   -fno-tree-loop-distribute-patterns
		  		   
LDFLAGS 	?= -static \
			   -nostdlib -nostartfiles -nodefaultlibs \
			   -lm -lgcc \
		 	   -T common/test.ld -Wl,-no-whole-archive


SRC 	= common/crt.S \
		  $(wildcard common/*.c) \
		  $(wildcard dhrystone/*.c)
INC		= -Idhrystone -Icommon

build/dhrystone.elf: force
	mkdir -p $(@D)
	$(CC) $(CFLAGS) $(INC) $(SRC) -o $@ $(LDFLAGS)

build/%.bin: build/%.elf
	$(OBJCOPY) -O binary $< $@

build/%.dump: build/%.elf
	$(OBJDUMP) -d $< > $@

force:
	@

