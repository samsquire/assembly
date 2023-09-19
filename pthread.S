	.file	"pthread.c"
	.text
	.section	.rodata
.LC0:
	.string	"Hi from thread"
	.text
	.type	func, @function
func:
.LFB6:
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	leaq	.LC0(%rip), %rax
	movq	%rax, %rdi
	call	puts@PLT
	movl	$0, %eax
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE6:
	.size	func, .-func
	.globl	main
	.type	main, @function
main:
.LFB7:
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$96, %rsp
	movq	%fs:40, %rax
	movq	%rax, -8(%rbp)
	xorl	%eax, %eax

	leaq	-88(%rbp), %rdx
	leaq	-64(%rbp), %rsi
	leaq	-80(%rbp), %rax
	movq	%rdx, %rcx
	leaq	func(%rip), %rdx
	movq	%rax, %rdi
	call	pthread_create@PLT
	movl	%eax, -84(%rbp)

  pushq %rsp 
	subq	$96, %rsp
	leaq	-88(%rsp), %rdx
	leaq	-64(%rsp), %rsi
	leaq	-80(%rsp), %rax
	movq	%rdx, %rcx
	leaq	func(%rip), %rdx
	movq	%rax, %rdi
	call	pthread_create@PLT
	movl	%eax, -84(%rsp)

	addq	$96, %rsp
  popq %rsp

	movq	-80(%rbp), %rax
	leaq	-72(%rbp), %rdx
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	pthread_join@PLT
	movl	$0, %eax
	movq	-8(%rbp), %rdx
	subq	%fs:40, %rdx
	je	.L5
	call	__stack_chk_fail@PLT
.L5:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE7:
	.size	main, .-main
	.ident	"GCC: (Ubuntu 12.3.0-1ubuntu1~23.04) 12.3.0"
	.section	.note.GNU-stack,"",@progbits
	.section	.note.gnu.property,"a"
	.align 8
	.long	1f - 0f
	.long	4f - 1f
	.long	5
0:
	.string	"GNU"
1:
	.align 8
	.long	0xc0000002
	.long	3f - 2f
2:
	.long	0x3
3:
	.align 8
4:
