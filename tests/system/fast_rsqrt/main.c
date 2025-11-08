#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include "rinv_sqrt_testcases.h"

#define COMPILER_BARRIER() asm volatile("" ::: "memory")

#define printstr(ptr, length)                   \
    do {                                        \
        asm volatile(                           \
            "li a7, 0x40;"                 \
            "li a0, 0x1;" /* stdout */     \
            "mv a1, %0;"                   \
            "mv a2, %1;" /* length character */ \
            "ecall;"                            \
            :                                   \
            : "r"(ptr), "r"(length)             \
            : "a0", "a1", "a2", "a7", "memory");          \
    } while (0)

#define TEST_OUTPUT(msg, length) printstr(msg, length)

#define TEST_LOGGER(msg)                     \
    {                                        \
        char _msg[] = msg;                   \
        TEST_OUTPUT(_msg, sizeof(_msg) - 1); \
    }

extern uint64_t get_cycles(void);
extern uint64_t get_instret(void);

/* Bare metal memcpy implementation */
void *memcpy(void *dest, const void *src, size_t n)
{
    uint8_t *d = (uint8_t *) dest;
    const uint8_t *s = (const uint8_t *) src;
    while (n--)
        *d++ = *s++;
    return dest;
}

/* Software division for RV32I (no M extension) */
static unsigned long udiv(unsigned long dividend, unsigned long divisor)
{
    if (divisor == 0)
        return 0;

    unsigned long quotient = 0;
    unsigned long remainder = 0;

    for (int i = 31; i >= 0; i--) {
        remainder <<= 1;
        remainder |= (dividend >> i) & 1;

        if (remainder >= divisor) {
            remainder -= divisor;
            quotient |= (1UL << i);
        }
    }

    return quotient;
}

static unsigned long umod(unsigned long dividend, unsigned long divisor)
{
    if (divisor == 0)
        return 0;

    unsigned long remainder = 0;

    for (int i = 31; i >= 0; i--) {
        remainder <<= 1;
        remainder |= (dividend >> i) & 1;

        if (remainder >= divisor) {
            remainder -= divisor;
        }
    }

    return remainder;
}

/* Software multiplication for RV32I (no M extension) */
static uint32_t umul(uint32_t a, uint32_t b)
{
    uint32_t result = 0;
    while (b) {
        if (b & 1)
            result += a;
        a <<= 1;
        b >>= 1;
    }
    return result;
}

/* Provide __mulsi3 for GCC */
uint32_t __mulsi3(uint32_t a, uint32_t b)
{
    return umul(a, b);
}

/* Simple integer to hex string conversion */
static void print_hex(unsigned long val)
{
    char buf[20];
    char *p = buf + sizeof(buf) - 1;
    *p = '\n';
    p--;

    if (val == 0) {
        *p = '0';
        p--;
    } else {
        while (val > 0) {
            int digit = val & 0xf;
            *p = (digit < 10) ? ('0' + digit) : ('a' + digit - 10);
            p--;
            val >>= 4;
        }
    }

    p++;
    printstr(p, (buf + sizeof(buf) - p));
}

/* Simple integer to decimal string conversion */
static void print_dec(unsigned long val)
{
    char buf[20];
    char *p = buf + sizeof(buf) - 1;
    *p = '\0';
    p--;

    if (val == 0) {
        *p = '0';
        p--;
    } else {
        while (val > 0) {
            *p = '0' + umod(val, 10);
            p--;
            val = udiv(val, 10);
        }
    }

    p++;
    printstr(p, (buf + sizeof(buf) - p));
}

/* ============= Fast Reciprocal Square Root Assembly Declaration ============= */
extern void fast_rsqrt_asm();

/* === Fast Reciprocal Square Root  === */

static uint32_t clz(uint32_t a) {
	uint32_t lz = 0;
	for (uint32_t i = 16; i > 0; i >>= 1) {
		if (!(a >> i)) {
			lz += i;
		} else {
			a >>= i;
		}
	}
	return lz;
}

static uint64_t mul32(uint32_t a, uint32_t b) {
	uint64_t r = 0;
	for (int i = 0; i < 32; i++) {
		if (b & (1U << i)) {
			r += (uint64_t)a << i;
		}
	}
	return r;
}

static const uint16_t rsqrt_table[32] = {
	65535, 46341, 32768, 23170, 16384, /* 2^0 to 2^4 */
	11585, 8192,  5793,	 4096,	2896,  /* 2^5 to 2^9 */
	2048,  1448,  1024,	 724,	512,   /* 2^10 to 2^14 */
	362,   256,	  181,	 128,	90,	   /* 2^15 to 2^19 */
	64,	   45,	  32,	 23,	16,	   /* 2^20 to 2^24 */
	11,	   8,	  6,	 4,		3,	   /* 2^25 to 2^29 */
	2,	   1						   /* 2^30, 2^31 */
};

uint32_t newton_iter(uint32_t x, uint32_t y)
{
	uint32_t y2 = (uint32_t)mul32(y, y);		   // Q0.32
	uint32_t xy2 = (uint32_t)(mul32(x, y2) >> 16); // Q16.16
	uint64_t tmp = mul32(y, (3u << 16) - xy2);
	y = (uint32_t)((tmp >> 17) + ((tmp >> 16) & 1));
	return y;
}

/* 65536/sqrt(x) */
__attribute__((noinline)) uint32_t fast_rsqrt(uint32_t x) {
	if (x == 0)
		return 0xFFFFFFFF;
	if (x == 1)
		return 65536;
	
	int exp = 31 - clz(x);
	uint32_t y = rsqrt_table[exp]; // Q16.16

	if (x > (1u << exp)) {
		uint32_t y_next = (exp < 31) ? rsqrt_table[exp + 1] : 0;
		uint32_t delta = y - y_next;
		uint32_t frac =
			(uint32_t)((((uint64_t)x - (1UL << exp)) << 16) >> exp);
		y -= (uint32_t)(delta * frac) >> 16;
		if (x < 512) {			// 2^9
			y = newton_iter(x, y);
			y = newton_iter(x, y);		
		}
		else if (x < 33554432) {	// 2^25
			y = newton_iter(x, y);
		}
	}
	
	return y;
}

uint32_t relative_error(uint32_t y, uint32_t answer, uint32_t *diff,uint32_t *max_relative_error)
{
	if (y > answer) *diff = y - answer;
	else *diff = answer- y;
	int32_t relative_error = udiv(umul(*diff, 100), answer);
	if (relative_error > *max_relative_error) *max_relative_error = relative_error;
	return relative_error;	
}

void test_rsqrt() {
	uint64_t start_cycles, end_cycles, cycles_elapsed;
	uint64_t start_instret, end_instret, instret_elapsed;
	uint32_t max_relative_error = 0;
	
	for (int i = 0; i < testcase_num; i++) {
		COMPILER_BARRIER();
		start_cycles = get_cycles();
		start_instret = get_instret();
		COMPILER_BARRIER();
		
		uint32_t y = fast_rsqrt(testcase[i]);
		
		COMPILER_BARRIER();
		end_cycles = get_cycles();
		end_instret = get_instret();
		COMPILER_BARRIER();
		cycles_elapsed = end_cycles - start_cycles;
		instret_elapsed = end_instret - start_instret;

		uint32_t diff;
		uint32_t curr_re = relative_error(y, answer[i], &diff, &max_relative_error);

		if (i < 11 || (curr_re > 7 && testcase[i] < 38797312)) {
			TEST_LOGGER("== Testcase ");
			print_dec((unsigned long) i);
			TEST_LOGGER(" ==\nfast_rsqrt(");
			print_dec((unsigned long) testcase[i]);
			TEST_LOGGER("): ");
			print_dec((unsigned long) y);
			TEST_LOGGER("  , numerical diff = ");
			print_dec((unsigned long) diff);
			TEST_LOGGER(" , relative error = ");
			print_dec((unsigned long) curr_re);
			TEST_LOGGER("%\n");
			TEST_LOGGER("  Cycles: ");
			print_dec((unsigned long) cycles_elapsed);
			TEST_LOGGER("  Instructions: ");
			print_dec((unsigned long) instret_elapsed);
			TEST_LOGGER("\n\n");	
		}
	}

	if (max_relative_error >= 8) {
		TEST_LOGGER("TEST FAILED, relative error larger than 8%\n");
	}
	else {
		TEST_LOGGER("TEST SUCCUESSFUL, relative error less than 8%\n");
	}
}

int main(void)
{
    uint64_t start_cycles, end_cycles, cycles_elapsed;
    uint64_t start_instret, end_instret, instret_elapsed;

    TEST_LOGGER("\n======= Fast Reciprocal Square Root Tests =======\n\n");

    /* Test assembly */
    TEST_LOGGER("Test1: reciprocal square root assembly\n");
    COMPILER_BARRIER();
    start_cycles = get_cycles();
    start_instret = get_instret();
    COMPILER_BARRIER();

    fast_rsqrt_asm();

    COMPILER_BARRIER();
    end_cycles = get_cycles();
    end_instret = get_instret();
    COMPILER_BARRIER();
    cycles_elapsed = end_cycles - start_cycles;
    instret_elapsed = end_instret - start_instret;

    TEST_LOGGER("  Cycles: ");
    print_dec((unsigned long) cycles_elapsed);
    TEST_LOGGER("  Instructions: ");
    print_dec((unsigned long) instret_elapsed);
    TEST_LOGGER("\n\n\n")

    /* Test Bare Metal C program */
    TEST_LOGGER("Test2: reciprocal square root C\n");

    test_rsqrt();

    TEST_LOGGER("\n=== Tests Completed ===\n");

    return 0;
}
