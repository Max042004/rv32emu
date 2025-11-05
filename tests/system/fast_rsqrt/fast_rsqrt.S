.org 0

.set SYSWRITE, 64
.set SYSEXIT, 93
.set STDOUT, 1

    .data 
table:
    .short 65535, 46341, 32768, 23170, 16384      # 2^0 to 2^4
    .short 11585, 8192, 5793, 4096, 2896          # 2^5 to 2^9
    .short 2048, 1448, 1024, 724, 512             # 2^10 to 2^14
    .short 362, 256, 181, 128, 90                 # 2^15 to 2^19
    .short 64, 45, 32, 23, 16                     # 2^20 to 2^24
    .short 11, 8, 6, 4, 3                         # 2^25 to 2^29
    .short 2, 1

testcase:
    .word 0, 1, 4, 5, 1600
    .word 1000000, 12582912, 4294967293, 0xFFFFFFFE
    .word 0xFFFFFFFF

testcase_num: .word 10

newline: .ascii "\n"
       .set newline_size, .-newline

    .text
    .global fast_rsqrt_asm
    .type fast_rsqrt_asm, %function
    
fast_rsqrt_asm:
    addi x2, x2, -4
    sw x1, 0(x2)
    li x26, 0
    jal x0, test_loop
    
test_loop:
    lw  x5, testcase_num
    beq x26, x5, end
    la  x5, testcase
    slli x6, x26, 2
    add x5, x5, x6 
    lw  x10, 0(x5)
    jal x1, fast_rsqrt
    jal  x1, u32_to_dec
    li x10, STDOUT
    li  x17, SYSWRITE             # print unsigned（Ripes 若無 36，請改 a7=1）
    ecall
    addi x26, x26, 1
    
    li  x10, STDOUT
    la  x11, newline
    li  x12, 1             # print \n
    li  x17, SYSWRITE
    ecall
    jal x0, test_loop

end:
     lw x1, 0(x2)
     addi x2, x2, 4
     ret   
#    li a0, 0 # 0 signals success
#    li  x17, SYSEXIT
#    ecall

u32_to_dec:
    addi x2, x2, -48
    sw   x1, 44(x2)
    sw   x8, 40(x2)
    sw   x24, 36(x2)
    sw   x25, 32(x2)
    addi x8, x2, 0
    addi x24, x8, 16
    mv   x5, x0
    beq  x10, x0, .Lzero

.Lloop:
    mv   x25, x10
    li   x11, 0xCCCCCCCD

    jal  x1, init_mul32     # (a1:a0) = x * magic


    srli x10, x11, 3        # q = hi >> 3
    slli x11, x10, 3
    slli x12, x10, 1
    add  x11, x11, x12      # 10*q
    sub  x12, x25,  x11      # r
    addi x12, x12, 48       # '0'+r
    addi x24, x24, -1
    sb   x12, 0(x24)
    addi x5, x5, 1
    bne  x10, x0, .Lloop
    j    .Ldone

.Lzero:
    addi x24, x24, -1
    li   x25, 48
    sb   x25, 0(x24)
    addi x5, x0, 1

.Ldone:
    mv   x11, x24            # a1 = buf
    mv   x12, x5            # a2 = len
    lw   x25,32(x2)
    lw   x24,36(x2)
    lw   x8, 40(x2)
    lw   x1, 44(x2)
    addi x2, x2, 48
    jr   x1

.align 4
# init r, i
init_clz:
    li  x15, 0              # r
    li  x14, 16             # i
    jal x0, clz

clz_loop:
    srl  x13, x10, x14
    beq  x13, x0, add_lz
    srl  x10, x10, x14
    srli x14, x14, 1
    jal  x0, clz

add_lz:
    add  x15, x15, x14
    srli x14, x14, 1
    jal  x0, clz
    
clz:
    bne x14, x0, clz_loop
    mv  x10, x15
    jr  x1
    
init_mul32:
    li  x6, 0               # r_low
    li  x31, 0              # r_hi
    li  x7, 0               # i
    li  x28, 32             # 32
    jal x0, mul32

mul32_loop:
    li   x29, 1
    sll  x29, x29, x7
    and  x30, x11, x29
    beq  x30, x0, 1f
    mv   x15, x10
    sll  x14, x10, x7       # a64_low
    beq x7, x0, 0f    

    li x28, 32
    sub  x16, x28, x7       # 32 - i
    srl  x15, x15, x16      # a64_hi
    j 2f
0: li x15, 0

2:
    add  x6,  x6,  x14      # r_low += a64_low
    add  x31, x31, x15      # r_hi  += a64_hi
    sltu x17, x6,  x14      # carry
    add  x31, x31, x17
1:  addi x7, x7, 1          # i++
    blt  x7, x28, mul32_loop

mul32:
    blt x7, x28, mul32_loop
    mv  x10, x6             # r_low
    mv  x11, x31            # r_hi
    jr  x1

fast_rsqrt:
    beq x10, x0, ret_max    # x==0
    li  x5, 1
    beq x10, x5, ret_scale1 # x==1
    
    mv  x9, x10             # s1 = x
    addi x2, x2, -4
    sw  x1, 0(x2)
    jal x1, init_clz
    lw  x1, 0(x2)
    addi x2, x2, 4
    
    li  x5, 31
    sub x18, x5, x10        # s2 = 31 - clz()
    la  x6, table
    slli x28, x18, 1
    add x6, x6, x28
    lhu x19, 0(x6)          # s3 = rsqrt_table[exp]
    
    li  x5, 1
    sll x5, x5, x18
    bge x9, x5, intepol
    
    mv  x10, x19
    jr  x1
   
intepol:
    jal x29, y_next
    sub x23, x19, x22       # s7 = s3 - s6 (delta)
    
    li  x5, 1
    sll x5, x5, x18         # 1UL<<exp
    sub x6, x9, x5          # t1 = x_low
    mv  x7, x6
    slli x6, x6, 16
    srli x7, x7, 16
    srl  x6, x6, x18
    li  x28, 32 
    sub x28, x28, x18
    sll x7, x7, x28
    add x24, x6, x7         # s8 = frac
    
    mv  x10, x23
    mv  x11, x24 
    addi x2, x2, -4
    sw  x1, 0(x2)
    jal x1, call_mul32
    lw  x1, 0(x2)
    addi x2, x2, 4
    slli x5, x11, 16
    srli x6, x10, 16
    or   x5, x5, x6         # (delta*frac)>>16
    sub  x19, x19, x5
 
    addi x2, x2, -4
    sw  x1, 0(x2)
    jal x1, newton_iter
    lw  x1, 0(x2)
    addi x2, x2, 4
    
    mv  x10, x19
    jr  x1                   # return y

call_mul32:
    addi x2, x2, -4
    sw  x1, 0(x2)
    jal x1, init_mul32       # delta*frac
    lw  x1, 0(x2)
    addi x2, x2, 4
    jr  x1

y_next:
    li  x5, 31
    blt x18, x5, b1
    li  x22, 0               # s6 = 0
    jalr x0, x29, 0
    
b1:
    la   x6, table
    addi x7, x18, 1
    slli x7, x7, 1           # ×2,16-bit
    add  x6, x6, x7
    lhu  x22, 0(x6)          # s6 = rsqrt_table[exp+1]
    jalr x0, x29, 0
    
newton_iter:
    mv  x10, x19
    mv  x11, x19
    addi x2, x2, -4
    sw  x1, 0(x2)
    jal x1, call_mul32
    lw  x1, 0(x2)
    addi x2, x2, 4
    mv  x23, x10             # s7 = y2
    
    mv  x10, x9              # x
    mv  x11, x23             # y2
    addi x2, x2, -4
    sw  x1, 0(x2)
    jal x1, call_mul32
    lw  x1, 0(x2)
    addi x2, x2, 4
    slli x5, x11, 16         # hi << 16
    srli x6, x10, 16         # lo >> 16
    or   x24, x5, x6         # s8 = xy2
    
    mv  x10, x19
    li  x5, 3
    slli x5, x5, 16
    sub x5, x5, x24
    mv  x11, x5
    addi x2, x2, -4
    sw  x1, 0(x2)
    jal x1, call_mul32
    lw  x1, 0(x2)
    addi x2, x2, 4
    slli x5, x11, 15         # >>17 高半
    srli x6, x10, 17         # >>17 低半
    or   x19, x5, x6         # s3 = tmp >> 17

    srli x7, x10, 16         # round bit = (tmp >> 16) & 1
    andi x7, x7, 1
    add  x19, x19, x7        # y = (tmp >> 17) + round_bit

    # 2nd iteration
    mv  x10, x19
    mv  x11, x19
    addi x2, x2, -4
    sw  x1, 0(x2)
    jal x1, call_mul32
    lw  x1, 0(x2)
    addi x2, x2, 4
    mv  x23, x10
    
    mv  x10, x9
    mv  x11, x23
    addi x2, x2, -4
    sw  x1, 0(x2)
    jal x1, call_mul32
    lw  x1, 0(x2)
    addi x2, x2, 4
    slli x5, x11, 16
    srli x6, x10, 16
    or   x24, x5, x6
    
    mv  x10, x19
    li  x5, 3
    slli x5, x5, 16
    sub x5, x5, x24
    mv  x11, x5
    addi x2, x2, -4
    sw  x1, 0(x2)
    jal x1, call_mul32
    lw  x1, 0(x2)
    addi x2, x2, 4
    slli x5, x11, 15
    srli x6, x10, 17
    or   x19, x5, x6

    srli x7, x10, 16
    andi x7, x7, 1
    add  x19, x19, x7

    jr  x1

ret_max:
    addi x10, x0, -1
    jr   x1

ret_scale1:
    slli x10, x10, 16
    jr   x1

