.text
.globl _start
_start:
auipc ra, 4
auipc ra, 4
auipc ra, 4
jal ra, _start
jal _start
la t0, _start
jalr ra, t0
jalr t0
nop
call _start

.align 6
jal ra, _start
jal _start

.align 7
jal ra, _start
jal _start

.align 8
jal ra, _start
jal _start

# .align 19
# jal ra, _start
# jal _start

# # INVALID !
# # (.text+0x100004): relocation truncated to fit:
# # R_RISCV_JAL against symbol `_start' defined in .text section
# .align 20
# jal ra, _start
# jal _start

# # Valid
# call _start
# # 80100000:	fff00097          	auipc	ra,0xfff00
# # 80100004:	000080e7          	jalr	ra # 80000000 <_start>
