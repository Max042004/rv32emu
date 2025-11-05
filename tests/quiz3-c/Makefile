.PHONY: clean

include ../../mk/toolchain.mk

ASFLAGS = -march=rv32i -mabi=ilp32
LDFLAGS = --oformat=elf32-littleriscv

%.o: %.S
	$(CROSS_COMPILE)as -R $(ASFLAGS) -o $@ $<

all: q3-rsqrt.elf

q3-rsqrt.elf: q3-rsqrt.o
	 $(CROSS_COMPILE)ld -o $@ -T q3-rsqrt.ld $(LDFLAGS) $<

clean:
	$(RM) q3-rsqrt.elf q3-rsqrt.o
