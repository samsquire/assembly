.globl main
main:
  push %rbp
  movq %rsp, %rbp
  subq $0x10, %rsp
  leaq 0x10(%rbp), %rdi
  movq $10, (%rdi)
  leave
  ret
