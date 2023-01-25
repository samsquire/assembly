.globl main
.align 4
.CONSTANT3:
   .string "Value is %d"
.CONSTANT4:
   .long 5
.CONSTANT5:
   .long 6
main:
pushq   %rbp
movq    %rsp, %rbp
subq    $32, %rsp
movq %rdi, -24(%rbp)
movl %esi, -28(%rbp)
movl $5, -12(%rbp)
movl $6, -8(%rbp)
movl -12(%rbp), %edx 
movl -8(%rbp), %eax 
addl    %edx, %eax
movl    %eax, %esi
leaq .CONSTANT3(%rip), %rax 
movq    %rax, %rdi
call    printf@PLT
movl    $0, %eax
leave
ret
