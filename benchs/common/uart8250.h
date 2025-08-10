#pragma once

static inline void __raw_writeb(unsigned char val, volatile void *addr){
	asm volatile("sb %0, 0(%1)" : : "r"(val), "r"(addr));
}

static inline void __raw_writew(unsigned short val, volatile void *addr){
	asm volatile("sh %0, 0(%1)" : : "r"(val), "r"(addr));
}

static inline void __raw_writel(unsigned int val, volatile void *addr){
	asm volatile("sw %0, 0(%1)" : : "r"(val), "r"(addr));
}

#if __riscv_xlen != 32
static inline void __raw_writeq(unsigned long int val, volatile void *addr){
	asm volatile("sd %0, 0(%1)" : : "r"(val), "r"(addr));
}
#endif

static inline unsigned char __raw_readb(const volatile void *addr){
	unsigned char val;
	asm volatile("lb %0, 0(%1)" : "=r"(val) : "r"(addr));
	return val;
}

static inline unsigned short __raw_readw(const volatile void *addr){
	unsigned short val;
	asm volatile("lh %0, 0(%1)" : "=r"(val) : "r"(addr));
	return val;
}

static inline unsigned int __raw_readl(const volatile void *addr){
	unsigned int val;
	asm volatile("lw %0, 0(%1)" : "=r"(val) : "r"(addr));
	return val;
}

#if __riscv_xlen != 32
static inline unsigned long int __raw_readq(const volatile void *addr){
	unsigned long int val;
	asm volatile("ld %0, 0(%1)" : "=r"(val) : "r"(addr));
	return val;
}
#endif

/* clang-format off */

#define __io_rbr()		do {} while (0)
#define __io_rar()		do {} while (0)
#define __io_rbw()		do {} while (0)
#define __io_raw()		do {} while (0)

#define readb_relaxed(c)	({ unsigned char  __v; __io_rbr(); __v = __raw_readb(c); __io_rar(); __v; })
#define readw_relaxed(c)	({ unsigned short __v; __io_rbr(); __v = __raw_readw(c); __io_rar(); __v; })
#define readl_relaxed(c)	({ unsigned int __v; __io_rbr(); __v = __raw_readl(c); __io_rar(); __v; })

#define writeb_relaxed(v,c)	({ __io_rbw(); __raw_writeb((v),(c)); __io_raw(); })
#define writew_relaxed(v,c)	({ __io_rbw(); __raw_writew((v),(c)); __io_raw(); })
#define writel_relaxed(v,c)	({ __io_rbw(); __raw_writel((v),(c)); __io_raw(); })

#define readq_relaxed(c)	({ unsigned long int __v; __io_rbr(); __v = __raw_readq(c); __io_rar(); __v; })
#define writeq_relaxed(v,c)	({ __io_rbw(); __raw_writeq((v),(c)); __io_raw(); })

#define __io_br()	do {} while (0)
#define __io_ar()	__asm__ __volatile__ ("fence i,r" : : : "memory");
#define __io_bw()	__asm__ __volatile__ ("fence w,o" : : : "memory");
#define __io_aw()	do {} while (0)

#define readb(c)	({ unsigned char  __v; __io_br(); __v = __raw_readb(c); __io_ar(); __v; })
#define readw(c)	({ unsigned short __v; __io_br(); __v = __raw_readw(c); __io_ar(); __v; })
#define readl(c)	({ unsigned int __v; __io_br(); __v = __raw_readl(c); __io_ar(); __v; })

#define writeb(v,c)	({ __io_bw(); __raw_writeb((v),(c)); __io_aw(); })
#define writew(v,c)	({ __io_bw(); __raw_writew((v),(c)); __io_aw(); })
#define writel(v,c)	({ __io_bw(); __raw_writel((v),(c)); __io_aw(); })


/* clang-format off */

#define UART_RBR_OFFSET		0	/* In:  Recieve Buffer Register */
#define UART_THR_OFFSET		0	/* Out: Transmitter Holding Register */
#define UART_DLL_OFFSET		0	/* Out: Divisor Latch Low */
#define UART_IER_OFFSET		1	/* I/O: Interrupt Enable Register */
#define UART_DLM_OFFSET		1	/* Out: Divisor Latch High */
#define UART_FCR_OFFSET		2	/* Out: FIFO Control Register */
#define UART_IIR_OFFSET		2	/* I/O: Interrupt Identification Register */
#define UART_LCR_OFFSET		3	/* Out: Line Control Register */
#define UART_MCR_OFFSET		4	/* Out: Modem Control Register */
#define UART_LSR_OFFSET		5	/* In:  Line Status Register */
#define UART_MSR_OFFSET		6	/* In:  Modem Status Register */
#define UART_SCR_OFFSET		7	/* I/O: Scratch Register */
#define UART_MDR1_OFFSET	8	/* I/O:  Mode Register */

#define UART_LSR_FIFOE		0x80	/* Fifo error */
#define UART_LSR_TEMT		0x40	/* Transmitter empty */
#define UART_LSR_THRE		0x20	/* Transmit-hold-register empty */
#define UART_LSR_BI		0x10	/* Break interrupt indicator */
#define UART_LSR_FE		0x08	/* Frame error indicator */
#define UART_LSR_PE		0x04	/* Parity error indicator */
#define UART_LSR_OE		0x02	/* Overrun error indicator */
#define UART_LSR_DR		0x01	/* Receiver data ready */
#define UART_LSR_BRK_ERROR_BITS	0x1E	/* BI, FE, PE, OE bits */

/* clang-format on */


static volatile void *uart8250_base;
static unsigned int uart8250_in_freq;
static unsigned int uart8250_baudrate;
static unsigned int uart8250_reg_width;
static unsigned int uart8250_reg_shift;

static unsigned int get_reg(unsigned int num)
{
	unsigned int offset = num << uart8250_reg_shift;

	if (uart8250_reg_width == 1)
		return readb(uart8250_base + offset);
	else if (uart8250_reg_width == 2)
		return readw(uart8250_base + offset);
	else
		return readl(uart8250_base + offset);
}

static void set_reg(unsigned int num, unsigned int val)
{
	unsigned int offset = num << uart8250_reg_shift;

	if (uart8250_reg_width == 1)
		writeb(val, uart8250_base + offset);
	else if (uart8250_reg_width == 2)
		writew(val, uart8250_base + offset);
	else
		writel(val, uart8250_base + offset);
}

static int uart8250_putc(int ch)
{
	while ((get_reg(UART_LSR_OFFSET) & UART_LSR_THRE) == 0)
		;
	set_reg(UART_THR_OFFSET, (char)ch);
	return 0;
}

static int uart8250_getc(void)
{
	if (get_reg(UART_LSR_OFFSET) & UART_LSR_DR)
		return get_reg(UART_RBR_OFFSET);
	return -1;
}


int uart8250_init(unsigned long base, unsigned int in_freq, unsigned int baudrate, unsigned int reg_shift,
		  unsigned int reg_width)
{
	unsigned short bdiv;
	uart8250_base      = (volatile void *)base;
	uart8250_reg_shift = reg_shift;
	uart8250_reg_width = reg_width;
	uart8250_in_freq   = in_freq;
	uart8250_baudrate  = baudrate;

	bdiv = uart8250_in_freq / (16 * uart8250_baudrate);

	/* Disable all interrupts */
	set_reg(UART_IER_OFFSET, 0x00);
	/* Enable DLAB */
	set_reg(UART_LCR_OFFSET, 0x80);

	if (bdiv) {
		/* Set divisor low byte */
		set_reg(UART_DLL_OFFSET, bdiv & 0xff);
		/* Set divisor high byte */
		set_reg(UART_DLM_OFFSET, (bdiv >> 8) & 0xff);
	}

	/* 8 bits, no parity, one stop bit */
	set_reg(UART_LCR_OFFSET, 0x03);
	/* Enable FIFO */
	set_reg(UART_FCR_OFFSET, 0x01);
	/* No modem control DTR RTS */
	set_reg(UART_MCR_OFFSET, 0x00);
	/* Clear line status */
	get_reg(UART_LSR_OFFSET);
	/* Read receive buffer */
	get_reg(UART_RBR_OFFSET);
	/* Set scratchpad */
	set_reg(UART_SCR_OFFSET, 0x00);

	return 0;
}
