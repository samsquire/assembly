.globl main
main:
  push %rbp
  movq %rsp, %rbp
  subq $128, %rsp
  mov %rsp, %rdi  
  movq $3, %rax  
  movq $1, 10(%rdi,%rax,)
  leave
  ret
