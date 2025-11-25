.text

.globl main

main:
    li s0, 0
    li t4, 0
    li s9, 99
    li s10, 1010
    li t1, 11
    li s8, 88
    li s11, 1111
    li t0, 1010
    li s6, 66
    li t2, 22
    li t3, 33

    lw  s2, 40(s0)
    add s3, s9, s10
    sub s4, t1, s8
    and s5, s11, t0
    sw  s6, 20(t4)
    or  s7, t2, t3
    ebreak 

.data

foo:
    .space 20
    .word 0xcafebabe
    .space 16
    .word 0xdeadbeef
