.text

.globl main

main:
    li s5, 0x0
    li t3, 0x33
    li s2, 0x22
    li s6, 0x66
    li s7, 0x77
    nop
    nop
    nop
    lw s7, 40(s5)
    and s8, s7, t3
    or  t2, s6, s7
    sub s3, s7, s2
    ebreak 

.data

foo:
    .space 20
    .word 0xcafebabe
    .space 16
    .word 0xdeadbeef
