.text

.globl main

main:
    li t2, 0x22
    li t6, 0x66
    li s3, 0x33
    li s4, 0x44
    li s5, 0x55
    li s8, 0x88
    nop
    nop
    nop
    add s8, s4, s5
    sub s2, s8, s3
    or  s9, t6, s8
    and s7, s8, t2
    ebreak 

.data

foo:
    .space 20
    .word 0xcafebabe
    .space 16
    .word 0xdeadbeef
