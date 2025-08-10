#pragma once
#include <stdarg.h>

// Used native types
#include <stddef.h>
#include <stdint.h>

int putchar(int ch);
int puts(const char *s);
int printf(const char *fmt, ...);
int sprintf(char *str, const char *fmt, ...);

#define static_assert(cond) switch(0) { case 0: case !!(long)(cond): ; }

#define read_csr(reg) ({ unsigned long __tmp; \
  asm volatile ("csrr %0, " #reg : "=r"(__tmp)); \
  __tmp; })

#define write_csr(reg, val) ({ \
  asm volatile ("csrw " #reg ", %0" :: "rK"(val)); })

#define swap_csr(reg, val) ({ unsigned long __tmp; \
  asm volatile ("csrrw %0, " #reg ", %1" : "=r"(__tmp) : "rK"(val)); \
  __tmp; })

#define set_csr(reg, bit) ({ unsigned long __tmp; \
  asm volatile ("csrrs %0, " #reg ", %1" : "=r"(__tmp) : "rK"(bit)); \
  __tmp; })

#define clear_csr(reg, bit) ({ unsigned long __tmp; \
  asm volatile ("csrrc %0, " #reg ", %1" : "=r"(__tmp) : "rK"(bit)); \
  __tmp; })

#define rdtime() read_csr(mtime)
#define rdcycle() read_csr(mcycle)
#define rdinstret() read_csr(minstret)



