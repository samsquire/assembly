	.file	"tree234.c"
	.text
	.globl	newtree234
	.type	newtree234, @function
newtree234:
.LFB6:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movq	%rdi, -24(%rbp)
	movl	$16, %edi
	call	malloc@PLT
	movq	%rax, -8(%rbp)
	movq	-8(%rbp), %rax
	movq	$0, (%rax)
	movq	-8(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 8(%rax)
	movq	-8(%rbp), %rax
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE6:
	.size	newtree234, .-newtree234
	.type	freenode234, @function
freenode234:
.LFB7:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	cmpq	$0, -8(%rbp)
	je	.L6
	movq	-8(%rbp), %rax
	movq	8(%rax), %rax
	movq	%rax, %rdi
	call	freenode234
	movq	-8(%rbp), %rax
	movq	16(%rax), %rax
	movq	%rax, %rdi
	call	freenode234
	movq	-8(%rbp), %rax
	movq	24(%rax), %rax
	movq	%rax, %rdi
	call	freenode234
	movq	-8(%rbp), %rax
	movq	32(%rax), %rax
	movq	%rax, %rdi
	call	freenode234
	movq	-8(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
	jmp	.L3
.L6:
	nop
.L3:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE7:
	.size	freenode234, .-freenode234
	.globl	freetree234
	.type	freetree234, @function
freetree234:
.LFB8:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	movq	-8(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, %rdi
	call	freenode234
	movq	-8(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
	nop
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE8:
	.size	freetree234, .-freetree234
	.type	countnode234, @function
countnode234:
.LFB9:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -24(%rbp)
	movl	$0, -8(%rbp)
	cmpq	$0, -24(%rbp)
	jne	.L9
	movl	$0, %eax
	jmp	.L10
.L9:
	movl	$0, -4(%rbp)
	jmp	.L11
.L12:
	movq	-24(%rbp), %rax
	movl	-4(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %eax
	addl	%eax, -8(%rbp)
	addl	$1, -4(%rbp)
.L11:
	cmpl	$3, -4(%rbp)
	jle	.L12
	movl	$0, -4(%rbp)
	jmp	.L13
.L15:
	movq	-24(%rbp), %rax
	movl	-4(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	testq	%rax, %rax
	je	.L14
	addl	$1, -8(%rbp)
.L14:
	addl	$1, -4(%rbp)
.L13:
	cmpl	$2, -4(%rbp)
	jle	.L15
	movl	-8(%rbp), %eax
.L10:
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE9:
	.size	countnode234, .-countnode234
	.globl	count234
	.type	count234, @function
count234:
.LFB10:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$8, %rsp
	movq	%rdi, -8(%rbp)
	movq	-8(%rbp), %rax
	movq	(%rax), %rax
	testq	%rax, %rax
	je	.L17
	movq	-8(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, %rdi
	call	countnode234
	jmp	.L18
.L17:
	movl	$0, %eax
.L18:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE10:
	.size	count234, .-count234
	.type	add234_internal, @function
add234_internal:
.LFB11:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$112, %rsp
	movq	%rdi, -88(%rbp)
	movq	%rsi, -96(%rbp)
	movl	%edx, -100(%rbp)
	movq	-96(%rbp), %rax
	movq	%rax, -16(%rbp)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	testq	%rax, %rax
	jne	.L20
	movl	$80, %edi
	call	malloc@PLT
	movq	%rax, %rdx
	movq	-88(%rbp), %rax
	movq	%rdx, (%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	$0, 72(%rax)
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	movq	72(%rax), %rax
	movq	%rax, 64(%rdx)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	$0, 16(%rax)
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	movq	16(%rax), %rax
	movq	%rax, 8(%rdx)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	$0, 32(%rax)
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	movq	32(%rax), %rax
	movq	%rax, 24(%rdx)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movl	$0, 44(%rax)
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	movl	44(%rax), %eax
	movl	%eax, 40(%rdx)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movl	$0, 52(%rax)
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	movl	52(%rax), %eax
	movl	%eax, 48(%rdx)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	$0, (%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 56(%rax)
	movq	-16(%rbp), %rax
	jmp	.L21
.L20:
	movq	-88(%rbp), %rax
	movq	%rax, -40(%rbp)
	jmp	.L22
.L39:
	movq	-40(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -48(%rbp)
	cmpl	$0, -100(%rbp)
	js	.L23
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	jne	.L24
	movl	-100(%rbp), %eax
	movl	%eax, -64(%rbp)
	jmp	.L30
.L24:
	movq	-48(%rbp), %rax
	movl	40(%rax), %eax
	cmpl	%eax, -100(%rbp)
	jg	.L26
	movl	$0, -64(%rbp)
	jmp	.L30
.L26:
	movq	-48(%rbp), %rax
	movl	40(%rax), %edx
	movl	-100(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -100(%rbp)
	movq	-48(%rbp), %rax
	movl	44(%rax), %eax
	cmpl	%eax, -100(%rbp)
	jg	.L27
	movl	$1, -64(%rbp)
	jmp	.L30
.L27:
	movq	-48(%rbp), %rax
	movl	44(%rax), %edx
	movl	-100(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -100(%rbp)
	movq	-48(%rbp), %rax
	movl	48(%rax), %eax
	cmpl	%eax, -100(%rbp)
	jg	.L28
	movl	$2, -64(%rbp)
	jmp	.L30
.L28:
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	movl	-100(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -100(%rbp)
	movq	-48(%rbp), %rax
	movl	52(%rax), %eax
	cmpl	%eax, -100(%rbp)
	jg	.L29
	movl	$3, -64(%rbp)
	jmp	.L30
.L29:
	movl	$0, %eax
	jmp	.L21
.L23:
	movq	-88(%rbp), %rax
	movq	8(%rax), %rcx
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	*%rcx
	movl	%eax, -52(%rbp)
	cmpl	$0, -52(%rbp)
	jns	.L31
	movl	$0, -64(%rbp)
	jmp	.L30
.L31:
	cmpl	$0, -52(%rbp)
	jne	.L32
	movq	-48(%rbp), %rax
	movq	56(%rax), %rax
	jmp	.L21
.L32:
	movq	-48(%rbp), %rax
	movq	64(%rax), %rax
	testq	%rax, %rax
	je	.L33
	movq	-88(%rbp), %rax
	movq	8(%rax), %rcx
	movq	-48(%rbp), %rax
	movq	64(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	*%rcx
	movl	%eax, -52(%rbp)
	cmpl	$0, -52(%rbp)
	jns	.L34
.L33:
	movl	$1, -64(%rbp)
	jmp	.L30
.L34:
	cmpl	$0, -52(%rbp)
	jne	.L35
	movq	-48(%rbp), %rax
	movq	64(%rax), %rax
	jmp	.L21
.L35:
	movq	-48(%rbp), %rax
	movq	72(%rax), %rax
	testq	%rax, %rax
	je	.L36
	movq	-88(%rbp), %rax
	movq	8(%rax), %rcx
	movq	-48(%rbp), %rax
	movq	72(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	*%rcx
	movl	%eax, -52(%rbp)
	cmpl	$0, -52(%rbp)
	jns	.L37
.L36:
	movl	$2, -64(%rbp)
	jmp	.L30
.L37:
	cmpl	$0, -52(%rbp)
	jne	.L38
	movq	-48(%rbp), %rax
	movq	72(%rax), %rax
	jmp	.L21
.L38:
	movl	$3, -64(%rbp)
.L30:
	movl	-64(%rbp), %eax
	cltq
	leaq	0(,%rax,8), %rdx
	movq	-48(%rbp), %rax
	addq	%rdx, %rax
	addq	$8, %rax
	movq	%rax, -40(%rbp)
.L22:
	movq	-40(%rbp), %rax
	movq	(%rax), %rax
	testq	%rax, %rax
	jne	.L39
	movq	$0, -32(%rbp)
	movl	$0, -72(%rbp)
	movq	$0, -24(%rbp)
	movl	$0, -68(%rbp)
	jmp	.L40
.L72:
	movq	-48(%rbp), %rax
	movq	64(%rax), %rax
	testq	%rax, %rax
	jne	.L41
	movq	-48(%rbp), %rax
	addq	$8, %rax
	cmpq	%rax, -40(%rbp)
	jne	.L42
	movq	-48(%rbp), %rax
	movq	16(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 24(%rax)
	movq	-48(%rbp), %rax
	movl	44(%rax), %edx
	movq	-48(%rbp), %rax
	movl	%edx, 48(%rax)
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 64(%rax)
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 16(%rax)
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 44(%rax)
	movq	-48(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 56(%rax)
	movq	-48(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 8(%rax)
	movq	-48(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 40(%rax)
	jmp	.L43
.L42:
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 24(%rax)
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 48(%rax)
	movq	-48(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 64(%rax)
	movq	-48(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 16(%rax)
	movq	-48(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 44(%rax)
.L43:
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	je	.L44
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L44:
	movq	-48(%rbp), %rax
	movq	16(%rax), %rax
	testq	%rax, %rax
	je	.L45
	movq	-48(%rbp), %rax
	movq	16(%rax), %rax
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L45:
	movq	-48(%rbp), %rax
	movq	24(%rax), %rax
	testq	%rax, %rax
	je	.L84
	movq	-48(%rbp), %rax
	movq	24(%rax), %rax
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
	jmp	.L84
.L41:
	movq	-48(%rbp), %rax
	movq	72(%rax), %rax
	testq	%rax, %rax
	jne	.L48
	movq	-48(%rbp), %rax
	addq	$8, %rax
	cmpq	%rax, -40(%rbp)
	jne	.L49
	movq	-48(%rbp), %rax
	movq	24(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 32(%rax)
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	movq	-48(%rbp), %rax
	movl	%edx, 52(%rax)
	movq	-48(%rbp), %rax
	movq	64(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 72(%rax)
	movq	-48(%rbp), %rax
	movq	16(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 24(%rax)
	movq	-48(%rbp), %rax
	movl	44(%rax), %edx
	movq	-48(%rbp), %rax
	movl	%edx, 48(%rax)
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 64(%rax)
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 16(%rax)
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 44(%rax)
	movq	-48(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 56(%rax)
	movq	-48(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 8(%rax)
	movq	-48(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 40(%rax)
	jmp	.L50
.L49:
	movq	-48(%rbp), %rax
	addq	$16, %rax
	cmpq	%rax, -40(%rbp)
	jne	.L51
	movq	-48(%rbp), %rax
	movq	24(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 32(%rax)
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	movq	-48(%rbp), %rax
	movl	%edx, 52(%rax)
	movq	-48(%rbp), %rax
	movq	64(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 72(%rax)
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 24(%rax)
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 48(%rax)
	movq	-48(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 64(%rax)
	movq	-48(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 16(%rax)
	movq	-48(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 44(%rax)
	jmp	.L50
.L51:
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 32(%rax)
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 52(%rax)
	movq	-48(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 72(%rax)
	movq	-48(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 24(%rax)
	movq	-48(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 48(%rax)
.L50:
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	je	.L52
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L52:
	movq	-48(%rbp), %rax
	movq	16(%rax), %rax
	testq	%rax, %rax
	je	.L53
	movq	-48(%rbp), %rax
	movq	16(%rax), %rax
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L53:
	movq	-48(%rbp), %rax
	movq	24(%rax), %rax
	testq	%rax, %rax
	je	.L54
	movq	-48(%rbp), %rax
	movq	24(%rax), %rax
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L54:
	movq	-48(%rbp), %rax
	movq	32(%rax), %rax
	testq	%rax, %rax
	je	.L85
	movq	-48(%rbp), %rax
	movq	32(%rax), %rax
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
	jmp	.L85
.L48:
	movl	$80, %edi
	call	malloc@PLT
	movq	%rax, -8(%rbp)
	movq	-48(%rbp), %rax
	movq	(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, (%rax)
	movq	-48(%rbp), %rax
	addq	$8, %rax
	cmpq	%rax, -40(%rbp)
	jne	.L56
	movq	-8(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 8(%rax)
	movq	-8(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 40(%rax)
	movq	-8(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 56(%rax)
	movq	-8(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 16(%rax)
	movq	-8(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 44(%rax)
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 64(%rax)
	movq	-48(%rbp), %rax
	movq	16(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 24(%rax)
	movq	-48(%rbp), %rax
	movl	44(%rax), %edx
	movq	-8(%rbp), %rax
	movl	%edx, 48(%rax)
	movq	-48(%rbp), %rax
	movq	64(%rax), %rax
	movq	%rax, -96(%rbp)
	movq	-48(%rbp), %rax
	movq	24(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 8(%rax)
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	movq	-48(%rbp), %rax
	movl	%edx, 40(%rax)
	movq	-48(%rbp), %rax
	movq	72(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 56(%rax)
	movq	-48(%rbp), %rax
	movq	32(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 16(%rax)
	movq	-48(%rbp), %rax
	movl	52(%rax), %edx
	movq	-48(%rbp), %rax
	movl	%edx, 44(%rax)
	jmp	.L57
.L56:
	movq	-48(%rbp), %rax
	addq	$16, %rax
	cmpq	%rax, -40(%rbp)
	jne	.L58
	movq	-48(%rbp), %rax
	movq	8(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 8(%rax)
	movq	-48(%rbp), %rax
	movl	40(%rax), %edx
	movq	-8(%rbp), %rax
	movl	%edx, 40(%rax)
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 56(%rax)
	movq	-8(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 16(%rax)
	movq	-8(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 44(%rax)
	movq	-8(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 64(%rax)
	movq	-8(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 24(%rax)
	movq	-8(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 48(%rax)
	movq	-48(%rbp), %rax
	movq	64(%rax), %rax
	movq	%rax, -96(%rbp)
	movq	-48(%rbp), %rax
	movq	24(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 8(%rax)
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	movq	-48(%rbp), %rax
	movl	%edx, 40(%rax)
	movq	-48(%rbp), %rax
	movq	72(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 56(%rax)
	movq	-48(%rbp), %rax
	movq	32(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 16(%rax)
	movq	-48(%rbp), %rax
	movl	52(%rax), %edx
	movq	-48(%rbp), %rax
	movl	%edx, 44(%rax)
	jmp	.L57
.L58:
	movq	-48(%rbp), %rax
	addq	$24, %rax
	cmpq	%rax, -40(%rbp)
	jne	.L59
	movq	-48(%rbp), %rax
	movq	8(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 8(%rax)
	movq	-48(%rbp), %rax
	movl	40(%rax), %edx
	movq	-8(%rbp), %rax
	movl	%edx, 40(%rax)
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 56(%rax)
	movq	-48(%rbp), %rax
	movq	16(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 16(%rax)
	movq	-48(%rbp), %rax
	movl	44(%rax), %edx
	movq	-8(%rbp), %rax
	movl	%edx, 44(%rax)
	movq	-48(%rbp), %rax
	movq	64(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 64(%rax)
	movq	-8(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 24(%rax)
	movq	-8(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 48(%rax)
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 8(%rax)
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 40(%rax)
	movq	-48(%rbp), %rax
	movq	72(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 56(%rax)
	movq	-48(%rbp), %rax
	movq	32(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 16(%rax)
	movq	-48(%rbp), %rax
	movl	52(%rax), %edx
	movq	-48(%rbp), %rax
	movl	%edx, 44(%rax)
	jmp	.L57
.L59:
	movq	-48(%rbp), %rax
	movq	8(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 8(%rax)
	movq	-48(%rbp), %rax
	movl	40(%rax), %edx
	movq	-8(%rbp), %rax
	movl	%edx, 40(%rax)
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 56(%rax)
	movq	-48(%rbp), %rax
	movq	16(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 16(%rax)
	movq	-48(%rbp), %rax
	movl	44(%rax), %edx
	movq	-8(%rbp), %rax
	movl	%edx, 44(%rax)
	movq	-48(%rbp), %rax
	movq	64(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 64(%rax)
	movq	-48(%rbp), %rax
	movq	24(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 24(%rax)
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	movq	-8(%rbp), %rax
	movl	%edx, 48(%rax)
	movq	-48(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 8(%rax)
	movq	-48(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 40(%rax)
	movq	-48(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 56(%rax)
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 16(%rax)
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 44(%rax)
	movq	-48(%rbp), %rax
	movq	72(%rax), %rax
	movq	%rax, -96(%rbp)
.L57:
	movq	-48(%rbp), %rax
	movq	$0, 24(%rax)
	movq	-48(%rbp), %rax
	movq	24(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 32(%rax)
	movq	-48(%rbp), %rax
	movq	32(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 32(%rax)
	movq	-48(%rbp), %rax
	movl	$0, 48(%rax)
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	movq	-48(%rbp), %rax
	movl	%edx, 52(%rax)
	movq	-48(%rbp), %rax
	movl	52(%rax), %edx
	movq	-8(%rbp), %rax
	movl	%edx, 52(%rax)
	movq	-48(%rbp), %rax
	movq	$0, 64(%rax)
	movq	-48(%rbp), %rax
	movq	64(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 72(%rax)
	movq	-48(%rbp), %rax
	movq	72(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 72(%rax)
	movq	-8(%rbp), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	je	.L60
	movq	-8(%rbp), %rax
	movq	8(%rax), %rax
	movq	-8(%rbp), %rdx
	movq	%rdx, (%rax)
.L60:
	movq	-8(%rbp), %rax
	movq	16(%rax), %rax
	testq	%rax, %rax
	je	.L61
	movq	-8(%rbp), %rax
	movq	16(%rax), %rax
	movq	-8(%rbp), %rdx
	movq	%rdx, (%rax)
.L61:
	movq	-8(%rbp), %rax
	movq	24(%rax), %rax
	testq	%rax, %rax
	je	.L62
	movq	-8(%rbp), %rax
	movq	24(%rax), %rax
	movq	-8(%rbp), %rdx
	movq	%rdx, (%rax)
.L62:
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	je	.L63
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L63:
	movq	-48(%rbp), %rax
	movq	16(%rax), %rax
	testq	%rax, %rax
	je	.L64
	movq	-48(%rbp), %rax
	movq	16(%rax), %rax
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L64:
	movq	-8(%rbp), %rax
	movq	%rax, -32(%rbp)
	movq	-32(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	movl	%eax, -72(%rbp)
	movq	-48(%rbp), %rax
	movq	%rax, -24(%rbp)
	movq	-24(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	movl	%eax, -68(%rbp)
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	testq	%rax, %rax
	je	.L65
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	movq	8(%rax), %rax
	cmpq	%rax, -48(%rbp)
	jne	.L66
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	addq	$8, %rax
	jmp	.L67
.L66:
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	movq	16(%rax), %rax
	cmpq	%rax, -48(%rbp)
	jne	.L68
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	addq	$16, %rax
	jmp	.L67
.L68:
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	movq	24(%rax), %rax
	cmpq	%rax, -48(%rbp)
	jne	.L70
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	addq	$24, %rax
	jmp	.L67
.L70:
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	addq	$32, %rax
.L67:
	movq	%rax, -40(%rbp)
.L65:
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -48(%rbp)
.L40:
	cmpq	$0, -48(%rbp)
	jne	.L72
	jmp	.L47
.L84:
	nop
	jmp	.L47
.L85:
	nop
.L47:
	cmpq	$0, -48(%rbp)
	je	.L73
	jmp	.L74
.L81:
	movq	-48(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	movl	%eax, -60(%rbp)
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	movq	8(%rax), %rax
	cmpq	%rax, -48(%rbp)
	je	.L75
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	movq	16(%rax), %rax
	cmpq	%rax, -48(%rbp)
	je	.L76
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	movq	24(%rax), %rax
	cmpq	%rax, -48(%rbp)
	jne	.L77
	movl	$2, %eax
	jmp	.L80
.L77:
	movl	$3, %eax
	jmp	.L80
.L76:
	movl	$1, %eax
	jmp	.L80
.L75:
	movl	$0, %eax
.L80:
	movl	%eax, -56(%rbp)
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	movl	-56(%rbp), %edx
	movslq	%edx, %rdx
	leaq	8(%rdx), %rcx
	movl	-60(%rbp), %edx
	movl	%edx, 8(%rax,%rcx,4)
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -48(%rbp)
.L74:
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	testq	%rax, %rax
	jne	.L81
	jmp	.L82
.L73:
	movl	$80, %edi
	call	malloc@PLT
	movq	%rax, %rdx
	movq	-88(%rbp), %rax
	movq	%rdx, (%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 8(%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 40(%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 56(%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 16(%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 44(%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	$0, 64(%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	$0, 24(%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movl	$0, 48(%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	$0, 72(%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	$0, 32(%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movl	$0, 52(%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	$0, (%rax)
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	je	.L83
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	8(%rax), %rax
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	movq	%rdx, (%rax)
.L83:
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	16(%rax), %rax
	testq	%rax, %rax
	je	.L82
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	movq	16(%rax), %rax
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	movq	%rdx, (%rax)
.L82:
	movq	-16(%rbp), %rax
.L21:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE11:
	.size	add234_internal, .-add234_internal
	.globl	add234
	.type	add234, @function
add234:
.LFB12:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	movq	%rsi, -16(%rbp)
	movq	-8(%rbp), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	jne	.L87
	movl	$0, %eax
	jmp	.L88
.L87:
	movq	-16(%rbp), %rcx
	movq	-8(%rbp), %rax
	movl	$-1, %edx
	movq	%rcx, %rsi
	movq	%rax, %rdi
	call	add234_internal
.L88:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE12:
	.size	add234, .-add234
	.globl	addpos234
	.type	addpos234, @function
addpos234:
.LFB13:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movq	%rdi, -8(%rbp)
	movq	%rsi, -16(%rbp)
	movl	%edx, -20(%rbp)
	cmpl	$0, -20(%rbp)
	js	.L90
	movq	-8(%rbp), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	je	.L91
.L90:
	movl	$0, %eax
	jmp	.L92
.L91:
	movl	-20(%rbp), %edx
	movq	-16(%rbp), %rcx
	movq	-8(%rbp), %rax
	movq	%rcx, %rsi
	movq	%rax, %rdi
	call	add234_internal
.L92:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE13:
	.size	addpos234, .-addpos234
	.globl	index234
	.type	index234, @function
index234:
.LFB14:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movq	%rdi, -24(%rbp)
	movl	%esi, -28(%rbp)
	movq	-24(%rbp), %rax
	movq	(%rax), %rax
	testq	%rax, %rax
	jne	.L94
	movl	$0, %eax
	jmp	.L95
.L94:
	cmpl	$0, -28(%rbp)
	js	.L96
	movq	-24(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, %rdi
	call	countnode234
	cmpl	%eax, -28(%rbp)
	jl	.L97
.L96:
	movl	$0, %eax
	jmp	.L95
.L97:
	movq	-24(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -8(%rbp)
	jmp	.L98
.L105:
	movq	-8(%rbp), %rax
	movl	40(%rax), %eax
	cmpl	%eax, -28(%rbp)
	jge	.L99
	movq	-8(%rbp), %rax
	movq	8(%rax), %rax
	movq	%rax, -8(%rbp)
	jmp	.L98
.L99:
	movq	-8(%rbp), %rax
	movl	40(%rax), %edx
	movl	-28(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -28(%rbp)
	movl	-28(%rbp), %eax
	shrl	$31, %eax
	andl	$1, %eax
	testb	%al, %al
	je	.L100
	movq	-8(%rbp), %rax
	movq	56(%rax), %rax
	jmp	.L95
.L100:
	movq	-8(%rbp), %rax
	movl	44(%rax), %eax
	cmpl	%eax, -28(%rbp)
	jge	.L101
	movq	-8(%rbp), %rax
	movq	16(%rax), %rax
	movq	%rax, -8(%rbp)
	jmp	.L98
.L101:
	movq	-8(%rbp), %rax
	movl	44(%rax), %edx
	movl	-28(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -28(%rbp)
	movl	-28(%rbp), %eax
	shrl	$31, %eax
	andl	$1, %eax
	testb	%al, %al
	je	.L102
	movq	-8(%rbp), %rax
	movq	64(%rax), %rax
	jmp	.L95
.L102:
	movq	-8(%rbp), %rax
	movl	48(%rax), %eax
	cmpl	%eax, -28(%rbp)
	jge	.L103
	movq	-8(%rbp), %rax
	movq	24(%rax), %rax
	movq	%rax, -8(%rbp)
	jmp	.L98
.L103:
	movq	-8(%rbp), %rax
	movl	48(%rax), %edx
	movl	-28(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -28(%rbp)
	movl	-28(%rbp), %eax
	shrl	$31, %eax
	andl	$1, %eax
	testb	%al, %al
	je	.L104
	movq	-8(%rbp), %rax
	movq	72(%rax), %rax
	jmp	.L95
.L104:
	movq	-8(%rbp), %rax
	movq	32(%rax), %rax
	movq	%rax, -8(%rbp)
.L98:
	cmpq	$0, -8(%rbp)
	jne	.L105
	movl	$0, %eax
.L95:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE14:
	.size	index234, .-index234
	.section	.rodata
.LC0:
	.string	"tree234.c"
	.align 8
.LC1:
	.string	"relation == REL234_LT || relation == REL234_GT"
	.text
	.globl	findrelpos234
	.type	findrelpos234, @function
findrelpos234:
.LFB15:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$96, %rsp
	movq	%rdi, -56(%rbp)
	movq	%rsi, -64(%rbp)
	movq	%rdx, -72(%rbp)
	movl	%ecx, -76(%rbp)
	movq	%r8, -88(%rbp)
	movq	-56(%rbp), %rax
	movq	(%rax), %rax
	testq	%rax, %rax
	jne	.L107
	movl	$0, %eax
	jmp	.L108
.L107:
	cmpq	$0, -72(%rbp)
	jne	.L109
	movq	-56(%rbp), %rax
	movq	8(%rax), %rax
	movq	%rax, -72(%rbp)
.L109:
	movq	-56(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -16(%rbp)
	movl	$0, -36(%rbp)
	movl	$-1, -32(%rbp)
	movl	$0, -24(%rbp)
	cmpq	$0, -64(%rbp)
	jne	.L124
	cmpl	$1, -76(%rbp)
	je	.L111
	cmpl	$3, -76(%rbp)
	je	.L111
	leaq	__PRETTY_FUNCTION__.0(%rip), %rax
	movq	%rax, %rcx
	movl	$470, %edx
	leaq	.LC0(%rip), %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	call	__assert_fail@PLT
.L111:
	cmpl	$1, -76(%rbp)
	jne	.L112
	movl	$1, -24(%rbp)
	jmp	.L124
.L112:
	cmpl	$3, -76(%rbp)
	jne	.L124
	movl	$-1, -24(%rbp)
.L124:
	movl	$0, -28(%rbp)
	jmp	.L113
.L119:
	cmpl	$2, -28(%rbp)
	jg	.L114
	movq	-16(%rbp), %rax
	movl	-28(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	testq	%rax, %rax
	je	.L114
	cmpl	$0, -24(%rbp)
	jne	.L115
	movq	-16(%rbp), %rax
	movl	-28(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	movq	-64(%rbp), %rax
	movq	-72(%rbp), %rcx
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	*%rcx
	jmp	.L116
.L115:
	movl	-24(%rbp), %eax
.L116:
	movl	%eax, -20(%rbp)
	cmpl	$0, -20(%rbp)
	js	.L114
	movq	-16(%rbp), %rax
	movl	-28(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	testq	%rax, %rax
	je	.L117
	movq	-16(%rbp), %rax
	movl	-28(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %eax
	addl	%eax, -36(%rbp)
.L117:
	cmpl	$0, -20(%rbp)
	jne	.L118
	movl	-28(%rbp), %eax
	movl	%eax, -32(%rbp)
	jmp	.L114
.L118:
	addl	$1, -36(%rbp)
	addl	$1, -28(%rbp)
.L113:
	cmpl	$3, -28(%rbp)
	jle	.L119
.L114:
	cmpl	$0, -32(%rbp)
	jns	.L133
	movq	-16(%rbp), %rax
	movl	-28(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	testq	%rax, %rax
	je	.L134
	movq	-16(%rbp), %rax
	movl	-28(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -16(%rbp)
	jmp	.L124
.L133:
	nop
	jmp	.L121
.L134:
	nop
.L121:
	cmpl	$0, -32(%rbp)
	js	.L125
	cmpl	$1, -76(%rbp)
	je	.L126
	cmpl	$3, -76(%rbp)
	je	.L126
	cmpq	$0, -88(%rbp)
	je	.L127
	movq	-88(%rbp), %rax
	movl	-36(%rbp), %edx
	movl	%edx, (%rax)
.L127:
	movq	-16(%rbp), %rax
	movl	-32(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	jmp	.L108
.L126:
	cmpl	$1, -76(%rbp)
	jne	.L128
	subl	$1, -36(%rbp)
	jmp	.L129
.L128:
	addl	$1, -36(%rbp)
	jmp	.L129
.L125:
	cmpl	$0, -76(%rbp)
	jne	.L130
	movl	$0, %eax
	jmp	.L108
.L130:
	cmpl	$1, -76(%rbp)
	je	.L131
	cmpl	$2, -76(%rbp)
	jne	.L129
.L131:
	subl	$1, -36(%rbp)
.L129:
	movl	-36(%rbp), %edx
	movq	-56(%rbp), %rax
	movl	%edx, %esi
	movq	%rax, %rdi
	call	index234@PLT
	movq	%rax, -8(%rbp)
	cmpq	$0, -8(%rbp)
	je	.L132
	cmpq	$0, -88(%rbp)
	je	.L132
	movq	-88(%rbp), %rax
	movl	-36(%rbp), %edx
	movl	%edx, (%rax)
.L132:
	movq	-8(%rbp), %rax
.L108:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE15:
	.size	findrelpos234, .-findrelpos234
	.globl	find234
	.type	find234, @function
find234:
.LFB16:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movq	%rdi, -8(%rbp)
	movq	%rsi, -16(%rbp)
	movq	%rdx, -24(%rbp)
	movq	-24(%rbp), %rdx
	movq	-16(%rbp), %rsi
	movq	-8(%rbp), %rax
	movl	$0, %r8d
	movl	$0, %ecx
	movq	%rax, %rdi
	call	findrelpos234@PLT
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE16:
	.size	find234, .-find234
	.globl	findrel234
	.type	findrel234, @function
findrel234:
.LFB17:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movq	%rdi, -8(%rbp)
	movq	%rsi, -16(%rbp)
	movq	%rdx, -24(%rbp)
	movl	%ecx, -28(%rbp)
	movl	-28(%rbp), %ecx
	movq	-24(%rbp), %rdx
	movq	-16(%rbp), %rsi
	movq	-8(%rbp), %rax
	movl	$0, %r8d
	movq	%rax, %rdi
	call	findrelpos234@PLT
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE17:
	.size	findrel234, .-findrel234
	.globl	findpos234
	.type	findpos234, @function
findpos234:
.LFB18:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movq	%rdi, -8(%rbp)
	movq	%rsi, -16(%rbp)
	movq	%rdx, -24(%rbp)
	movq	%rcx, -32(%rbp)
	movq	-32(%rbp), %rcx
	movq	-24(%rbp), %rdx
	movq	-16(%rbp), %rsi
	movq	-8(%rbp), %rax
	movq	%rcx, %r8
	movl	$0, %ecx
	movq	%rax, %rdi
	call	findrelpos234@PLT
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE18:
	.size	findpos234, .-findpos234
	.type	delpos234_internal, @function
delpos234_internal:
.LFB19:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%rbx
	subq	$152, %rsp
	.cfi_offset 3, -24
	movq	%rdi, -152(%rbp)
	movl	%esi, -156(%rbp)
	movl	$-1, -144(%rbp)
	movq	$0, -104(%rbp)
	movq	-152(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -112(%rbp)
	jmp	.L142
.L170:
	movq	-112(%rbp), %rax
	movl	40(%rax), %eax
	cmpl	%eax, -156(%rbp)
	jge	.L143
	movl	$0, -140(%rbp)
	jmp	.L144
.L143:
	movq	-112(%rbp), %rax
	movl	40(%rax), %edx
	movl	-156(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -156(%rbp)
	movl	-156(%rbp), %eax
	shrl	$31, %eax
	andl	$1, %eax
	testb	%al, %al
	je	.L145
	movl	$0, -144(%rbp)
	jmp	.L146
.L145:
	movq	-112(%rbp), %rax
	movl	44(%rax), %eax
	cmpl	%eax, -156(%rbp)
	jge	.L147
	movl	$1, -140(%rbp)
	jmp	.L144
.L147:
	movq	-112(%rbp), %rax
	movl	44(%rax), %edx
	movl	-156(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -156(%rbp)
	movl	-156(%rbp), %eax
	shrl	$31, %eax
	andl	$1, %eax
	testb	%al, %al
	je	.L148
	movl	$1, -144(%rbp)
	jmp	.L146
.L148:
	movq	-112(%rbp), %rax
	movl	48(%rax), %eax
	cmpl	%eax, -156(%rbp)
	jge	.L149
	movl	$2, -140(%rbp)
	jmp	.L144
.L149:
	movq	-112(%rbp), %rax
	movl	48(%rax), %edx
	movl	-156(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -156(%rbp)
	movl	-156(%rbp), %eax
	shrl	$31, %eax
	andl	$1, %eax
	testb	%al, %al
	je	.L150
	movl	$2, -144(%rbp)
	jmp	.L146
.L150:
	movl	$3, -140(%rbp)
.L144:
	movq	-112(%rbp), %rax
	movl	-140(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -96(%rbp)
	movq	-96(%rbp), %rax
	movq	64(%rax), %rax
	testq	%rax, %rax
	jne	.L151
	cmpl	$0, -140(%rbp)
	jle	.L152
	movl	-140(%rbp), %eax
	leal	-1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	64(%rax), %rax
	testq	%rax, %rax
	je	.L152
	movl	-140(%rbp), %eax
	leal	-1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -72(%rbp)
	movq	-72(%rbp), %rax
	movq	72(%rax), %rax
	testq	%rax, %rax
	jne	.L153
	movq	-72(%rbp), %rax
	movq	64(%rax), %rax
	testq	%rax, %rax
	setne	%al
	movzbl	%al, %eax
	jmp	.L154
.L153:
	movl	$2, %eax
.L154:
	movl	%eax, -120(%rbp)
	movq	-96(%rbp), %rax
	movq	16(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 24(%rax)
	movq	-96(%rbp), %rax
	movl	44(%rax), %edx
	movq	-96(%rbp), %rax
	movl	%edx, 48(%rax)
	movq	-96(%rbp), %rax
	movq	56(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 64(%rax)
	movq	-96(%rbp), %rax
	movq	8(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 16(%rax)
	movq	-96(%rbp), %rax
	movl	40(%rax), %edx
	movq	-96(%rbp), %rax
	movl	%edx, 44(%rax)
	movl	-140(%rbp), %eax
	leal	-1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 56(%rax)
	movl	-120(%rbp), %eax
	leal	1(%rax), %edx
	movq	-72(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 8(%rax)
	movl	-120(%rbp), %eax
	leal	1(%rax), %edx
	movq	-72(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %edx
	movq	-96(%rbp), %rax
	movl	%edx, 40(%rax)
	movq	-96(%rbp), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	je	.L155
	movq	-96(%rbp), %rax
	movq	8(%rax), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, (%rax)
.L155:
	movl	-140(%rbp), %eax
	leal	-1(%rax), %ecx
	movq	-72(%rbp), %rax
	movl	-120(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	movq	-112(%rbp), %rax
	movslq	%ecx, %rcx
	addq	$6, %rcx
	movq	%rdx, 8(%rax,%rcx,8)
	movl	-120(%rbp), %eax
	leal	1(%rax), %edx
	movq	-72(%rbp), %rax
	movslq	%edx, %rdx
	movq	$0, 8(%rax,%rdx,8)
	movl	-120(%rbp), %eax
	leal	1(%rax), %edx
	movq	-72(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	$0, 8(%rax,%rdx,4)
	movq	-72(%rbp), %rax
	movl	-120(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	$0, 8(%rax,%rdx,8)
	movq	-96(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	movq	-112(%rbp), %rdx
	movl	-140(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$8, %rcx
	movl	%eax, 8(%rdx,%rcx,4)
	movl	-140(%rbp), %eax
	leal	-1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %eax
	addl	%eax, -156(%rbp)
	movl	-140(%rbp), %eax
	leal	-1(%rax), %ebx
	movq	-72(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	movq	-112(%rbp), %rdx
	movslq	%ebx, %rcx
	addq	$8, %rcx
	movl	%eax, 8(%rdx,%rcx,4)
	movl	-140(%rbp), %eax
	leal	-1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %eax
	subl	%eax, -156(%rbp)
	jmp	.L151
.L152:
	cmpl	$2, -140(%rbp)
	jg	.L156
	movl	-140(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	testq	%rax, %rax
	je	.L156
	movl	-140(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	64(%rax), %rax
	testq	%rax, %rax
	je	.L156
	movl	-140(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -64(%rbp)
	movq	-112(%rbp), %rax
	movl	-140(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 64(%rax)
	movq	-64(%rbp), %rax
	movq	8(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 24(%rax)
	movq	-64(%rbp), %rax
	movl	40(%rax), %edx
	movq	-96(%rbp), %rax
	movl	%edx, 48(%rax)
	movq	-96(%rbp), %rax
	movq	24(%rax), %rax
	testq	%rax, %rax
	je	.L157
	movq	-96(%rbp), %rax
	movq	24(%rax), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, (%rax)
.L157:
	movq	-64(%rbp), %rax
	movq	56(%rax), %rdx
	movq	-112(%rbp), %rax
	movl	-140(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$6, %rcx
	movq	%rdx, 8(%rax,%rcx,8)
	movq	-64(%rbp), %rax
	movq	16(%rax), %rdx
	movq	-64(%rbp), %rax
	movq	%rdx, 8(%rax)
	movq	-64(%rbp), %rax
	movl	44(%rax), %edx
	movq	-64(%rbp), %rax
	movl	%edx, 40(%rax)
	movl	$0, -136(%rbp)
	jmp	.L158
.L160:
	movl	-136(%rbp), %eax
	leal	2(%rax), %edx
	movl	-136(%rbp), %eax
	leal	1(%rax), %esi
	movq	-64(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rcx
	movq	-64(%rbp), %rax
	movslq	%esi, %rdx
	movq	%rcx, 8(%rax,%rdx,8)
	movl	-136(%rbp), %eax
	leal	2(%rax), %edx
	movl	-136(%rbp), %eax
	leal	1(%rax), %ecx
	movq	-64(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %edx
	movq	-64(%rbp), %rax
	movslq	%ecx, %rcx
	addq	$8, %rcx
	movl	%edx, 8(%rax,%rcx,4)
	movl	-136(%rbp), %eax
	leal	1(%rax), %edx
	movq	-64(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	movq	-64(%rbp), %rax
	movl	-136(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$6, %rcx
	movq	%rdx, 8(%rax,%rcx,8)
	addl	$1, -136(%rbp)
.L158:
	cmpl	$1, -136(%rbp)
	jg	.L159
	movl	-136(%rbp), %eax
	leal	1(%rax), %edx
	movq	-64(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	testq	%rax, %rax
	jne	.L160
.L159:
	movl	-136(%rbp), %eax
	leal	1(%rax), %edx
	movq	-64(%rbp), %rax
	movslq	%edx, %rdx
	movq	$0, 8(%rax,%rdx,8)
	movl	-136(%rbp), %eax
	leal	1(%rax), %edx
	movq	-64(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	$0, 8(%rax,%rdx,4)
	movq	-64(%rbp), %rax
	movl	-136(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	$0, 8(%rax,%rdx,8)
	movq	-96(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	movq	-112(%rbp), %rdx
	movl	-140(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$8, %rcx
	movl	%eax, 8(%rdx,%rcx,4)
	movl	-140(%rbp), %eax
	leal	1(%rax), %ebx
	movq	-64(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	movq	-112(%rbp), %rdx
	movslq	%ebx, %rcx
	addq	$8, %rcx
	movl	%eax, 8(%rdx,%rcx,4)
	jmp	.L151
.L156:
	cmpl	$0, -140(%rbp)
	jle	.L161
	subl	$1, -140(%rbp)
	movq	-112(%rbp), %rax
	movl	-140(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %edx
	movl	-156(%rbp), %eax
	addl	%edx, %eax
	addl	$1, %eax
	movl	%eax, -156(%rbp)
.L161:
	movq	-112(%rbp), %rax
	movl	-140(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -56(%rbp)
	movl	-140(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -96(%rbp)
	movq	-96(%rbp), %rax
	movq	16(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 32(%rax)
	movq	-96(%rbp), %rax
	movl	44(%rax), %edx
	movq	-96(%rbp), %rax
	movl	%edx, 52(%rax)
	movq	-96(%rbp), %rax
	movq	56(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 72(%rax)
	movq	-96(%rbp), %rax
	movq	8(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 24(%rax)
	movq	-96(%rbp), %rax
	movl	40(%rax), %edx
	movq	-96(%rbp), %rax
	movl	%edx, 48(%rax)
	movq	-112(%rbp), %rax
	movl	-140(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 64(%rax)
	movq	-56(%rbp), %rax
	movq	16(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 16(%rax)
	movq	-56(%rbp), %rax
	movl	44(%rax), %edx
	movq	-96(%rbp), %rax
	movl	%edx, 44(%rax)
	movq	-96(%rbp), %rax
	movq	16(%rax), %rax
	testq	%rax, %rax
	je	.L162
	movq	-96(%rbp), %rax
	movq	16(%rax), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, (%rax)
.L162:
	movq	-56(%rbp), %rax
	movq	56(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 56(%rax)
	movq	-56(%rbp), %rax
	movq	8(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, 8(%rax)
	movq	-56(%rbp), %rax
	movl	40(%rax), %edx
	movq	-96(%rbp), %rax
	movl	%edx, 40(%rax)
	movq	-96(%rbp), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	je	.L163
	movq	-96(%rbp), %rax
	movq	8(%rax), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, (%rax)
.L163:
	movl	-140(%rbp), %eax
	leal	1(%rax), %ebx
	movq	-96(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	movq	-112(%rbp), %rdx
	movslq	%ebx, %rcx
	addq	$8, %rcx
	movl	%eax, 8(%rdx,%rcx,4)
	movq	-56(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
	movl	-140(%rbp), %eax
	movl	%eax, -132(%rbp)
	jmp	.L164
.L168:
	movl	-132(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rcx
	movq	-112(%rbp), %rax
	movl	-132(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rcx, 8(%rax,%rdx,8)
	movl	-132(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %edx
	movq	-112(%rbp), %rax
	movl	-132(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$8, %rcx
	movl	%edx, 8(%rax,%rcx,4)
	cmpl	$1, -132(%rbp)
	jg	.L165
	movl	-132(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	jmp	.L166
.L165:
	movl	$0, %eax
.L166:
	movq	-112(%rbp), %rdx
	movl	-132(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$6, %rcx
	movq	%rax, 8(%rdx,%rcx,8)
	addl	$1, -132(%rbp)
.L164:
	cmpl	$2, -132(%rbp)
	jg	.L167
	movl	-132(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	testq	%rax, %rax
	jne	.L168
.L167:
	movq	-112(%rbp), %rax
	movl	-132(%rbp), %edx
	movslq	%edx, %rdx
	movq	$0, 8(%rax,%rdx,8)
	movq	-112(%rbp), %rax
	movl	-132(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	$0, 8(%rax,%rdx,4)
	cmpl	$2, -132(%rbp)
	jg	.L169
	movq	-112(%rbp), %rax
	movl	-132(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	$0, 8(%rax,%rdx,8)
.L169:
	movq	-112(%rbp), %rax
	movq	56(%rax), %rax
	testq	%rax, %rax
	jne	.L151
	movq	-152(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, (%rax)
	movq	-96(%rbp), %rax
	movq	$0, (%rax)
	movq	-112(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
.L151:
	movq	-96(%rbp), %rax
	movq	%rax, -112(%rbp)
.L142:
	cmpq	$0, -112(%rbp)
	jne	.L170
.L146:
	cmpq	$0, -104(%rbp)
	jne	.L171
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -104(%rbp)
.L171:
	cmpl	$-1, -144(%rbp)
	jne	.L172
	movl	$0, %eax
	jmp	.L173
.L172:
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	testq	%rax, %rax
	jne	.L174
	movq	-112(%rbp), %rax
	movq	64(%rax), %rax
	testq	%rax, %rax
	jne	.L174
	movq	-112(%rbp), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	jne	.L174
	movq	-112(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
	movq	-152(%rbp), %rax
	movq	$0, (%rax)
	movq	-104(%rbp), %rax
	jmp	.L173
.L174:
	movq	-112(%rbp), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	jne	.L175
	movq	-112(%rbp), %rax
	movq	64(%rax), %rax
	testq	%rax, %rax
	je	.L175
	movl	-144(%rbp), %eax
	movl	%eax, -128(%rbp)
	jmp	.L176
.L178:
	movl	-128(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	movq	-112(%rbp), %rax
	movl	-128(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$6, %rcx
	movq	%rdx, 8(%rax,%rcx,8)
	addl	$1, -128(%rbp)
.L176:
	cmpl	$1, -128(%rbp)
	jg	.L177
	movl	-128(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	testq	%rax, %rax
	jne	.L178
.L177:
	movq	-112(%rbp), %rax
	movl	-128(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	$0, 8(%rax,%rdx,8)
	jmp	.L179
.L186:
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	movq	8(%rax), %rax
	cmpq	%rax, -112(%rbp)
	je	.L180
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	movq	16(%rax), %rax
	cmpq	%rax, -112(%rbp)
	je	.L181
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	movq	24(%rax), %rax
	cmpq	%rax, -112(%rbp)
	jne	.L182
	movl	$2, %eax
	jmp	.L185
.L182:
	movl	$3, %eax
	jmp	.L185
.L181:
	movl	$1, %eax
	jmp	.L185
.L180:
	movl	$0, %eax
.L185:
	movl	%eax, -116(%rbp)
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	movl	-116(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %edx
	leal	-1(%rdx), %ecx
	movl	-116(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	%ecx, 8(%rax,%rdx,4)
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -112(%rbp)
.L179:
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	testq	%rax, %rax
	jne	.L186
	movq	-104(%rbp), %rax
	jmp	.L173
.L175:
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	64(%rax), %rax
	testq	%rax, %rax
	je	.L187
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -88(%rbp)
	jmp	.L188
.L195:
	movq	-88(%rbp), %rax
	movq	32(%rax), %rax
	testq	%rax, %rax
	je	.L189
	movq	-88(%rbp), %rax
	movq	32(%rax), %rax
	jmp	.L190
.L189:
	movq	-88(%rbp), %rax
	movq	24(%rax), %rax
	testq	%rax, %rax
	je	.L191
	movq	-88(%rbp), %rax
	movq	24(%rax), %rax
	jmp	.L190
.L191:
	movq	-88(%rbp), %rax
	movq	16(%rax), %rax
	testq	%rax, %rax
	je	.L193
	movq	-88(%rbp), %rax
	movq	16(%rax), %rax
	jmp	.L190
.L193:
	movq	-88(%rbp), %rax
	movq	8(%rax), %rax
.L190:
	movq	%rax, -88(%rbp)
.L188:
	movq	-88(%rbp), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	jne	.L195
	movq	-88(%rbp), %rax
	movq	72(%rax), %rax
	testq	%rax, %rax
	je	.L196
	movq	-88(%rbp), %rax
	movq	72(%rax), %rax
	jmp	.L197
.L196:
	movq	-88(%rbp), %rax
	movq	64(%rax), %rax
	testq	%rax, %rax
	je	.L198
	movq	-88(%rbp), %rax
	movq	64(%rax), %rax
	jmp	.L197
.L198:
	movq	-88(%rbp), %rax
	movq	56(%rax), %rax
.L197:
	movq	%rax, -24(%rbp)
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	leaq	6(%rdx), %rcx
	movq	-24(%rbp), %rdx
	movq	%rdx, 8(%rax,%rcx,8)
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %eax
	subl	$1, %eax
	movl	%eax, -156(%rbp)
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -112(%rbp)
	jmp	.L142
.L187:
	movl	-144(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	64(%rax), %rax
	testq	%rax, %rax
	je	.L201
	movl	-144(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -80(%rbp)
	jmp	.L202
.L203:
	movq	-80(%rbp), %rax
	movq	8(%rax), %rax
	movq	%rax, -80(%rbp)
.L202:
	movq	-80(%rbp), %rax
	movq	8(%rax), %rax
	testq	%rax, %rax
	jne	.L203
	movq	-80(%rbp), %rax
	movq	56(%rax), %rax
	movq	%rax, -32(%rbp)
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	leaq	6(%rdx), %rcx
	movq	-32(%rbp), %rdx
	movq	%rdx, 8(%rax,%rcx,8)
	movl	-144(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -112(%rbp)
	movl	$0, -156(%rbp)
	jmp	.L142
.L201:
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -48(%rbp)
	movl	-144(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -40(%rbp)
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 64(%rax)
	movq	-40(%rbp), %rax
	movq	8(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 24(%rax)
	movq	-40(%rbp), %rax
	movl	40(%rax), %edx
	movq	-48(%rbp), %rax
	movl	%edx, 48(%rax)
	movq	-48(%rbp), %rax
	movq	24(%rax), %rax
	testq	%rax, %rax
	je	.L204
	movq	-48(%rbp), %rax
	movq	24(%rax), %rax
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L204:
	movq	-40(%rbp), %rax
	movq	56(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 72(%rax)
	movq	-40(%rbp), %rax
	movq	16(%rax), %rdx
	movq	-48(%rbp), %rax
	movq	%rdx, 32(%rax)
	movq	-40(%rbp), %rax
	movl	44(%rax), %edx
	movq	-48(%rbp), %rax
	movl	%edx, 52(%rax)
	movq	-48(%rbp), %rax
	movq	32(%rax), %rax
	testq	%rax, %rax
	je	.L205
	movq	-48(%rbp), %rax
	movq	32(%rax), %rax
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L205:
	movq	-40(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
	movq	-48(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	movq	-112(%rbp), %rdx
	movl	-144(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$8, %rcx
	movl	%eax, 8(%rdx,%rcx,4)
	movl	-144(%rbp), %eax
	movl	%eax, -124(%rbp)
	jmp	.L206
.L208:
	movl	-124(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	movq	-112(%rbp), %rax
	movl	-124(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$6, %rcx
	movq	%rdx, 8(%rax,%rcx,8)
	movl	-124(%rbp), %eax
	leal	2(%rax), %edx
	movl	-124(%rbp), %eax
	leal	1(%rax), %esi
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rcx
	movq	-112(%rbp), %rax
	movslq	%esi, %rdx
	movq	%rcx, 8(%rax,%rdx,8)
	movl	-124(%rbp), %eax
	leal	2(%rax), %edx
	movl	-124(%rbp), %eax
	leal	1(%rax), %ecx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %edx
	movq	-112(%rbp), %rax
	movslq	%ecx, %rcx
	addq	$8, %rcx
	movl	%edx, 8(%rax,%rcx,4)
	addl	$1, -124(%rbp)
.L206:
	cmpl	$1, -124(%rbp)
	jg	.L207
	movl	-124(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	testq	%rax, %rax
	jne	.L208
.L207:
	movq	-112(%rbp), %rax
	movl	-124(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	$0, 8(%rax,%rdx,8)
	movl	-124(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	$0, 8(%rax,%rdx,8)
	movl	-124(%rbp), %eax
	leal	1(%rax), %edx
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	$0, 8(%rax,%rdx,4)
	movq	-112(%rbp), %rax
	movq	56(%rax), %rax
	testq	%rax, %rax
	jne	.L209
	movq	-152(%rbp), %rax
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
	movq	-48(%rbp), %rax
	movq	$0, (%rax)
	movq	-112(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
.L209:
	movq	-48(%rbp), %rax
	movq	%rax, -112(%rbp)
	movq	-48(%rbp), %rax
	movl	40(%rax), %edx
	movq	-48(%rbp), %rax
	movl	44(%rax), %eax
	addl	%edx, %eax
	addl	$1, %eax
	movl	%eax, -156(%rbp)
	jmp	.L142
.L173:
	movq	-8(%rbp), %rbx
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE19:
	.size	delpos234_internal, .-delpos234_internal
	.globl	delpos234
	.type	delpos234, @function
delpos234:
.LFB20:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	movl	%esi, -12(%rbp)
	cmpl	$0, -12(%rbp)
	js	.L212
	movq	-8(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, %rdi
	call	countnode234
	cmpl	%eax, -12(%rbp)
	jl	.L213
.L212:
	movl	$0, %eax
	jmp	.L214
.L213:
	movl	-12(%rbp), %edx
	movq	-8(%rbp), %rax
	movl	%edx, %esi
	movq	%rax, %rdi
	call	delpos234_internal
.L214:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE20:
	.size	delpos234, .-delpos234
	.globl	del234
	.type	del234, @function
del234:
.LFB21:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movq	%rdi, -24(%rbp)
	movq	%rsi, -32(%rbp)
	movq	%fs:40, %rax
	movq	%rax, -8(%rbp)
	xorl	%eax, %eax
	leaq	-12(%rbp), %rdx
	movq	-32(%rbp), %rsi
	movq	-24(%rbp), %rax
	movq	%rdx, %r8
	movl	$0, %ecx
	movl	$0, %edx
	movq	%rax, %rdi
	call	findrelpos234@PLT
	testq	%rax, %rax
	jne	.L216
	movl	$0, %eax
	jmp	.L218
.L216:
	movl	-12(%rbp), %edx
	movq	-24(%rbp), %rax
	movl	%edx, %esi
	movq	%rax, %rdi
	call	delpos234_internal
.L218:
	movq	-8(%rbp), %rdx
	subq	%fs:40, %rdx
	je	.L219
	call	__stack_chk_fail@PLT
.L219:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE21:
	.size	del234, .-del234
	.section	.rodata
	.align 8
	.type	__PRETTY_FUNCTION__.0, @object
	.size	__PRETTY_FUNCTION__.0, 14
__PRETTY_FUNCTION__.0:
	.string	"findrelpos234"
	.ident	"GCC: (GNU) 11.3.0"
	.section	.note.GNU-stack,"",@progbits
