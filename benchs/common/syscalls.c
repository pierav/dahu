#include "uart8250.h"
#include "util.h"
// # spike --dump-dts a
// SERIAL0: ns16550@10000000 {
//   compatible = "ns16550a";
//   clock-frequency = <10000000>;
//   interrupt-parent = <&PLIC>;
//   interrupts = <1>;
//   reg = <0x0 0x10000000 0x0 0x100>;
//   reg-shift = <0x0>;
//   reg-io-width = <0x1>;
// };

#define UART_ADDR 0x10000000
#define UART_FREQ 10000000
#define UART_BAUDRATE 115200
#define UART_REG_SHIFT 0
#define UART_REG_WIDTH 1

extern volatile unsigned long int tohost;
extern volatile unsigned long int fromhost;

void __attribute__((noreturn, noinline))
pass() {
    tohost = 1;  // FESVR exit OK
    while (1) { }
}

void __attribute__((noreturn, noinline))
fail(uintptr_t code) {
    tohost = (code << 1) | 1;  // FESVR exit
    while (1) { }
}

void __attribute__((noreturn, noinline))
exit(int code) {
    if (code) {  // GOOD TRAP / BAD TRAP exit
        fail(code);
    } else {
        pass();
    }
}

uintptr_t __attribute__((weak))
handle_trap(uintptr_t cause, uintptr_t epc, uintptr_t regs[32]) {
    exit(1337);
}

int __attribute__((weak))
main(int argc, char **argv) {
    // single-threaded programs override this function.
    puts("Implement main(), foo!\n");
    return -1;
}

void _init(int cid, int nc) {
    char num[2] = {cid, nc};
    char *argv[1] = {num};
    uart8250_init(UART_ADDR, UART_FREQ, UART_BAUDRATE,
                  UART_REG_SHIFT, UART_REG_WIDTH);

    int ret = main(2, argv);
    exit(ret);
}

int putchar(int ch) {
    uart8250_putc(ch);
    return 0;
}

