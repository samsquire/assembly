.globl main

main:
  push %rbp
  movq %rsp, %rbp
  sub $8, %rsp
  leaq -8(%rbp), %rax
  movq $100, (%rax)
  leave
  ret

