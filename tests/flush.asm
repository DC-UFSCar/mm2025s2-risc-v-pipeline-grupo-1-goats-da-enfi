.text

.globl main

main:
    li s1, 0x12
    li s2, 0x12
    li t1, 0x11
    li t6, 0x66
    li s3, 0x33
    li s4, 0x44
    li s5, 0x55
    li s8, 0x88
    li s9, 0x99
    nop
    nop
    nop
    beq s1, s2, L1
    sub s8, t1, s3
    or  s9, t6, s5
L1:
    add s7, s3, s4
    ebreak 

.data

foo:
    .space 20
    .word 0xcafebabe
    .space 16
    .word 0xdeadbeef
