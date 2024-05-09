	.file	"basicassembly.c"
	.text
	.section	.rodata
.LC0:
	.string	"loop"
	.text
	.globl	main
	.type	main, @function
main:
.LFB0:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movl	%edi, -20(%rbp)
	movq	%rsi, -32(%rbp)
	movl	$1, -4(%rbp)
	jmp	.L2
.L4:
	leaq	.LC0(%rip), %rax
	movq	%rax, %rdi
	call	puts@PLT
	cmpq	$27, -32(%rbp)
	jne	.L3
	movl	$0, -4(%rbp)
.L3:
	addl	$1, -20(%rbp)
.L2:
	cmpl	$6, -20(%rbp)
	je	.L4
	movl	$0, %eax
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	main, .-main
	.ident	"GCC: (GNU) 11.3.0"
	.section	.note.GNU-stack,"",@progbits
