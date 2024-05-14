	.file	"stream2-workqueue.c"
	.text
	.p2align 4
	.globl	pollthreads
	.type	pollthreads, @function
pollthreads:
.LFB73:
	.cfi_startproc
	cmpl	$1, 104(%rdi)
	movq	%rdi, %r9
	jle	.L15
	movq	48(%r9), %rax
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsi, %r10
	movq	%rdx, %r11
	pushq	%rbx
	.cfi_def_cfa_offset 24
	.cfi_offset 3, -24
	movq	%rcx, %rdi
	movq	1056(%rax), %rbx
	movl	$1, %eax
	.p2align 4,,10
	.p2align 3
.L8:
	movslq	%eax, %rdx
	movl	(%rbx,%rdx,4), %edx
	testl	%edx, %edx
	sete	%sil
	testb	$4, %dl
	jne	.L9
	testb	%sil, %sil
	je	.L3
.L9:
	movslq	(%r8), %rcx
	leal	1(%rcx), %ebp
	movl	%ebp, (%r8)
	movl	%eax, (%r11,%rcx,4)
.L3:
	andl	$8, %edx
	jne	.L10
	testb	%sil, %sil
	je	.L5
.L10:
	movslq	(%rdi), %rdx
	leal	1(%rdx), %ecx
	movl	%ecx, (%rdi)
	movl	%eax, (%r10,%rdx,4)
	addl	$1, %eax
	cmpl	%eax, 104(%r9)
	jg	.L8
	xorl	%eax, %eax
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L5:
	.cfi_restore_state
	addl	$1, %eax
	cmpl	%eax, 104(%r9)
	jg	.L8
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L15:
	.cfi_restore 3
	.cfi_restore 6
	xorl	%eax, %eax
	ret
	.cfi_endproc
.LFE73:
	.size	pollthreads, .-pollthreads
	.p2align 4
	.globl	findavailable
	.type	findavailable, @function
findavailable:
.LFB74:
	.cfi_startproc
	movq	%rdi, %r11
	movq	184(%rdi), %rdi
	movl	(%rdx), %r8d
	addq	$1, %rdi
	testq	%rdi, %rdi
	jle	.L20
	movq	160(%r11), %r10
	xorl	%ecx, %ecx
	xorl	%r9d, %r9d
	xorl	%eax, %eax
	jmp	.L22
	.p2align 4,,10
	.p2align 3
.L21:
	addl	$1, %ecx
	movslq	%ecx, %rax
	movq	%rax, %r9
	cmpq	%rdi, %rax
	jge	.L20
.L22:
	salq	$5, %rax
	cmpl	$1, 16(%r10,%rax)
	jne	.L21
	movslq	%r8d, %rax
	addl	$1, %r8d
	movq	%r9, (%rsi,%rax,8)
	movl	%r8d, (%rdx)
	movl	104(%r11), %eax
	addl	%eax, %eax
	cmpl	%eax, %r8d
	je	.L20
	movq	184(%r11), %rdi
	addl	$1, %ecx
	movslq	%ecx, %rax
	addq	$1, %rdi
	movq	%rax, %r9
	cmpq	%rdi, %rax
	jl	.L22
.L20:
	xorl	%eax, %eax
	testl	%r8d, %r8d
	sete	%al
	ret
	.cfi_endproc
.LFE74:
	.size	findavailable, .-findavailable
	.p2align 4
	.globl	singlewriter3
	.type	singlewriter3, @function
singlewriter3:
.LFB75:
	.cfi_startproc
	ret
	.cfi_endproc
.LFE75:
	.size	singlewriter3, .-singlewriter3
	.p2align 4
	.globl	singlewriter2
	.type	singlewriter2, @function
singlewriter2:
.LFB76:
	.cfi_startproc
	movl	512(%rdi), %eax
	testl	%eax, %eax
	je	.L32
	pushq	%r12
	.cfi_def_cfa_offset 16
	.cfi_offset 12, -16
	cltd
	pushq	%rbp
	.cfi_def_cfa_offset 24
	.cfi_offset 6, -24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
	movl	104(%rdi), %esi
	movq	%rdi, %rbx
	leal	-1(%rsi), %ecx
	idivl	%ecx
	testl	%edx, %edx
	je	.L35
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%rbp
	.cfi_def_cfa_offset 16
	popq	%r12
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L32:
	.cfi_restore 3
	.cfi_restore 6
	.cfi_restore 12
	ret
	.p2align 4,,10
	.p2align 3
.L35:
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
	.cfi_offset 6, -24
	.cfi_offset 12, -16
	movslq	100(%rdi), %rbp
	salq	$10, %rbp
	addq	48(%rdi), %rbp
	movl	$4, %edi
	movslq	804(%rbp), %rax
	leaq	(%rax,%rax,2), %r12
	salq	$4, %r12
	addq	792(%rbp), %r12
	leaq	8(%r12), %rsi
	call	clock_gettime@PLT
	movl	804(%rbp), %eax
	addl	$1, %eax
	cltd
	idivl	800(%rbp)
	movl	100(%rbx), %eax
	movl	%edx, 804(%rbp)
	movl	%eax, (%r12)
	movq	.LC0(%rip), %rax
	movq	%rax, 32(%r12)
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%rbp
	.cfi_def_cfa_offset 16
	popq	%r12
	.cfi_def_cfa_offset 8
	ret
	.cfi_endproc
.LFE76:
	.size	singlewriter2, .-singlewriter2
	.p2align 4
	.globl	singlewriter
	.type	singlewriter, @function
singlewriter:
.LFB77:
	.cfi_startproc
	pushq	%r13
	.cfi_def_cfa_offset 16
	.cfi_offset 13, -16
	movq	%rdx, %r13
	pushq	%r12
	.cfi_def_cfa_offset 24
	.cfi_offset 12, -24
	movq	%rcx, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 32
	.cfi_offset 6, -32
	movq	%r12, %r8
	movq	%rdi, %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 40
	.cfi_offset 3, -40
	movq	%rsi, %rbx
	subq	$40, %rsp
	.cfi_def_cfa_offset 80
	movq	48(%rdi), %rcx
	movq	%fs:40, %rax
	movq	%rax, 24(%rsp)
	xorl	%eax, %eax
	movl	$0, 12(%rsp)
	movl	524(%rcx), %eax
	movl	$0, 16(%rsp)
	movl	$0, 20(%rsp)
	addl	$1, %eax
	cltd
	idivl	104(%rdi)
	movl	%edx, 524(%rcx)
	leaq	20(%rsp), %rdx
	movq	%r13, %rcx
	call	findavailable@PLT
	cmpl	$1, %eax
	je	.L36
	leaq	16(%rsp), %r8
	leaq	12(%rsp), %rcx
	movq	%r12, %rdx
	movq	%r13, %rsi
	movq	%rbp, %rdi
	call	pollthreads@PLT
	movslq	12(%rsp), %r8
	testl	%r8d, %r8d
	jle	.L50
	movl	20(%rsp), %r9d
	xorl	%ecx, %ecx
	jmp	.L39
	.p2align 4,,10
	.p2align 3
.L58:
	movq	(%rbx,%rcx,8), %rax
	movslq	0(%r13,%rcx,4), %rdx
	leal	1(%rcx), %esi
	addq	$1, %rcx
	salq	$5, %rax
	addq	160(%rbp), %rax
	movq	%rdx, %rdi
	salq	$10, %rdx
	movd	(%rax), %xmm0
	movd	8(%rax), %xmm1
	movl	$2, 16(%rax)
	addq	48(%rbp), %rdx
	punpckldq	%xmm1, %xmm0
	movq	%rax, 168(%rdx)
	movl	%edi, 20(%rax)
	orl	$16, 200(%rdx)
	movq	%xmm0, 20(%rdx)
	cmpq	%rcx, %r8
	je	.L38
.L39:
	movl	%ecx, %esi
	cmpq	%r9, %rcx
	jne	.L58
.L38:
	movl	16(%rsp), %r9d
	testl	%r9d, %r9d
	jle	.L43
	movl	20(%rsp), %r8d
	addl	%esi, %r9d
	jmp	.L45
	.p2align 4,,10
	.p2align 3
.L56:
	leal	1(%rsi), %edi
	movslq	%esi, %rsi
	movslq	(%r12), %rdx
	addq	$4, %r12
	movq	(%rbx,%rsi,8), %rax
	movq	%rdx, %rcx
	salq	$10, %rdx
	addq	48(%rbp), %rdx
	salq	$5, %rax
	addq	160(%rbp), %rax
	movd	(%rax), %xmm0
	movd	8(%rax), %xmm2
	movl	$3, 16(%rax)
	movq	%rax, 176(%rdx)
	punpckldq	%xmm2, %xmm0
	movl	%ecx, 20(%rax)
	orl	$32, 200(%rdx)
	movq	%xmm0, 64(%rdx)
	cmpl	%r9d, %edi
	je	.L43
	movl	%edi, %esi
.L45:
	cmpl	%esi, %r8d
	jne	.L56
.L43:
	movl	104(%rbp), %edi
	testl	%edi, %edi
	jle	.L42
	movq	48(%rbp), %r8
	xorl	%edx, %edx
	.p2align 4,,10
	.p2align 3
.L48:
	movslq	%edx, %rcx
	movq	%rcx, %rax
	salq	$10, %rax
	addq	%r8, %rax
	movl	200(%rax), %esi
	testl	%esi, %esi
	je	.L46
	movq	32(%rax), %rax
	addl	$1, %edx
	movl	%esi, (%rax,%rcx,4)
	movl	104(%rbp), %edi
	cmpl	%edi, %edx
	jl	.L48
.L42:
	xorl	%eax, %eax
.L36:
	movq	24(%rsp), %rdx
	subq	%fs:40, %rdx
	jne	.L59
	addq	$40, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%rbp
	.cfi_def_cfa_offset 24
	popq	%r12
	.cfi_def_cfa_offset 16
	popq	%r13
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L46:
	.cfi_restore_state
	addl	$1, %edx
	cmpl	%edi, %edx
	jl	.L48
	jmp	.L42
.L50:
	xorl	%esi, %esi
	jmp	.L38
.L59:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE77:
	.size	singlewriter, .-singlewriter
	.p2align 4
	.globl	threadwork
	.type	threadwork, @function
threadwork:
.LFB78:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	movq	%rdi, %rbx
	movl	$4, %edi
	subq	$40, %rsp
	.cfi_def_cfa_offset 96
	movq	%fs:40, %rax
	movq	%rax, 24(%rsp)
	xorl	%eax, %eax
	movq	%rsp, %rsi
	call	clock_gettime@PLT
	cmpl	$2, 92(%rbx)
	je	.L85
.L61:
	movq	40(%rbx), %rbp
	movl	908(%rbx), %eax
	movabsq	$7378697629483820647, %rdx
	movq	896(%rbp), %rdi
	sall	$7, %eax
	cltq
	movq	(%rdi,%rax,8), %rcx
	movq	%rcx, %rax
	sarq	$63, %rcx
	imulq	%rdx
	movslq	904(%rbx), %rax
	sarq	%rdx
	subq	%rcx, %rdx
	movq	%rdx, %r12
	cmpq	%rax, %rdx
	je	.L67
	movslq	100(%rbx), %rbp
	movl	$4, %edi
	movl	$0, 384(%rbx)
	salq	$10, %rbp
	addq	48(%rbx), %rbp
	movslq	804(%rbp), %rax
	leaq	(%rax,%rax,2), %r13
	salq	$4, %r13
	addq	792(%rbp), %r13
	leaq	8(%r13), %rsi
	call	clock_gettime@PLT
	movl	804(%rbp), %eax
	addl	$1, %eax
	cltd
	idivl	800(%rbp)
	movl	100(%rbx), %eax
	movl	%edx, 804(%rbp)
	movq	40(%rbx), %rbp
	movl	%eax, 0(%r13)
	movl	908(%rbx), %eax
	movq	896(%rbp), %rdi
	movl	%eax, 44(%r13)
	movq	.LC0(%rip), %rax
	movq	%rax, 32(%r13)
.L67:
	movl	912(%rbx), %esi
	movq	840(%rbx), %r9
	movl	%r12d, 904(%rbx)
	movl	%esi, %eax
	sall	$7, %eax
	cltq
	movq	(%rdi,%rax,8), %rcx
	movslq	%esi, %rax
	leaq	(%rax,%rax,2), %rdx
	movl	(%r9,%rdx,4), %edx
	testq	%rcx, %rcx
	je	.L79
	movslq	%edx, %rdi
	cmpq	%rcx, %rdi
	jge	.L68
.L79:
	movl	104(%rbx), %r10d
	subl	$1, %r10d
	testl	%r10d, %r10d
	jle	.L68
	xorl	%r11d, %r11d
	jmp	.L76
	.p2align 4,,10
	.p2align 3
.L74:
	addl	$1, %r11d
	cmpl	%r11d, %r10d
	jle	.L68
.L75:
	movslq	%esi, %rax
	movq	40(%rbx), %rbp
	leaq	(%rax,%rax,2), %rdx
	movl	(%r9,%rdx,4), %edx
.L76:
	leaq	(%rax,%rax,2), %r8
	movslq	%edx, %rax
	sarl	$31, %edx
	addq	$1, 72(%rbx)
	imulq	$1717986919, %rax, %rax
	salq	$2, %r8
	movdqa	(%rsp), %xmm0
	leaq	(%r9,%r8), %rdi
	movl	4(%rdi), %ecx
	sarq	$33, %rax
	subl	%edx, %eax
	movl	%ecx, %r13d
	subl	$1, %eax
	movslq	%eax, %rdx
	movl	%eax, %r12d
	imulq	$-2139062143, %rdx, %rdx
	sarl	$31, %r12d
	shrq	$32, %rdx
	addl	%eax, %edx
	sarl	$7, %edx
	subl	%r12d, %edx
	movl	%edx, %r12d
	sall	$8, %r12d
	subl	%edx, %r12d
	xorl	%edx, %edx
	subl	%r12d, %eax
	movl	%esi, %r12d
	cltq
	testq	%rax, %rax
	cmovs	%rdx, %rax
	movslq	%ecx, %rdx
	sarl	$31, %r13d
	imulq	$-2139062143, %rdx, %rdx
	sall	$24, %r12d
	salq	$16, %rax
	shrq	$32, %rdx
	addl	%ecx, %edx
	sarl	$7, %edx
	subl	%r13d, %edx
	movl	%edx, %r13d
	sall	$8, %r13d
	subl	%edx, %r13d
	movl	%ecx, %edx
	subl	%r13d, %edx
	movslq	100(%rbx), %r13
	orl	%edx, %r12d
	movq	%r13, %r15
	salq	$10, %r13
	addq	48(%rbx), %r13
	movslq	%r12d, %r12
	movslq	804(%r13), %rdx
	orq	%rax, %r12
	movq	%rdx, %rax
	leaq	(%rdx,%rdx,2), %r14
	addl	$1, %eax
	salq	$4, %r14
	addq	792(%r13), %r14
	cltd
	movups	%xmm0, 8(%r14)
	idivl	800(%r13)
	movl	%edx, 804(%r13)
	movq	%r12, 24(%r14)
	addq	112(%rbp), %r12
	movl	%r15d, (%r14)
	movl	$1, 36(%r14)
	cmpb	$-1, (%r12)
	je	.L70
	addq	$1, 920(%rbx)
	movb	$-1, (%r12)
	movq	840(%rbx), %r9
	movl	104(%rbx), %r10d
	movl	912(%rbx), %esi
	leaq	(%r9,%r8), %rdi
	movl	4(%rdi), %ecx
	subl	$1, %r10d
.L70:
	cmpl	$4, %ecx
	jg	.L71
	addl	$1, %ecx
	addl	$1, (%rdi)
	movl	%ecx, 4(%rdi)
.L71:
	cmpl	$5, %ecx
	jne	.L72
	addl	$1, %esi
	movl	%esi, 912(%rbx)
	movl	$0, 4(%rdi)
.L72:
	cmpl	%esi, 908(%rbx)
	jne	.L73
	addl	$1, %esi
	movl	%esi, 912(%rbx)
.L73:
	cmpl	$5, %esi
	jne	.L74
	movl	$1, 912(%rbx)
	addl	$1, %r11d
	cmpl	%r11d, %r10d
	jle	.L68
	movl	$1, %esi
	jmp	.L75
	.p2align 4,,10
	.p2align 3
.L68:
	movq	24(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L86
	addq	$40, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L85:
	.cfi_restore_state
	movl	104(%rbx), %eax
	testl	%eax, %eax
	jle	.L65
	movl	384(%rbx), %ecx
	xorl	%edi, %edi
	movabsq	$7378697629483820647, %r10
	movabsq	$-9187201950435737471, %r9
	.p2align 4,,10
	.p2align 3
.L66:
	movl	908(%rbx), %r11d
	movq	40(%rbx), %r8
	movdqa	(%rsp), %xmm1
	movl	%r11d, %eax
	movq	896(%r8), %rdx
	sall	$24, %r11d
	sall	$7, %eax
	cltq
	movq	(%rdx,%rax,8), %rsi
	movq	%rsi, %rax
	sarq	$63, %rsi
	imulq	%r10
	movq	%rdx, %rax
	sarq	%rax
	subq	%rsi, %rax
	movq	%rax, %rbp
	imulq	%r9
	movq	%rbp, %rax
	sarq	$63, %rax
	leaq	(%rdx,%rbp), %rsi
	sarq	$7, %rsi
	subq	%rax, %rsi
	movq	%rbp, %rax
	movslq	100(%rbx), %rbp
	movq	%rsi, %rdx
	salq	$8, %rdx
	subq	%rsi, %rdx
	movslq	%ecx, %rsi
	imulq	$-2139062143, %rsi, %rsi
	subq	%rdx, %rax
	movl	%ecx, %edx
	sarl	$31, %edx
	sall	$16, %eax
	shrq	$32, %rsi
	addl	%ecx, %esi
	sarl	$7, %esi
	subl	%edx, %esi
	movl	%esi, %edx
	sall	$8, %edx
	subl	%esi, %edx
	subl	%edx, %ecx
	orl	%r11d, %ecx
	movq	%rbp, %r11
	salq	$10, %rbp
	addq	48(%rbx), %rbp
	movslq	804(%rbp), %rdx
	orl	%eax, %ecx
	movslq	%ecx, %rcx
	movq	%rdx, %rax
	leaq	(%rdx,%rdx,2), %rsi
	addl	$1, %eax
	salq	$4, %rsi
	addq	792(%rbp), %rsi
	cltd
	movups	%xmm1, 8(%rsi)
	idivl	800(%rbp)
	movl	%edx, 804(%rbp)
	movq	%rcx, 24(%rsi)
	addq	112(%r8), %rcx
	movl	%r11d, (%rsi)
	movl	$1, 36(%rsi)
	cmpb	$-1, (%rcx)
	je	.L63
	addq	$1, 80(%rbx)
.L63:
	movb	%r11b, (%rcx)
	movl	384(%rbx), %eax
	addl	$1, %edi
	addl	$1, %eax
	movslq	%eax, %rcx
	cltd
	imulq	$1717986919, %rcx, %rcx
	sarq	$33, %rcx
	subl	%edx, %ecx
	leal	(%rcx,%rcx,4), %edx
	subl	%edx, %eax
	movl	%eax, 384(%rbx)
	movl	%eax, %ecx
	cmpl	%edi, 104(%rbx)
	jg	.L66
.L65:
	movq	40(%rbx), %rdx
	movl	908(%rbx), %eax
	movq	896(%rdx), %rdx
	sall	$7, %eax
	cltq
	lock addq	$1, (%rdx,%rax,8)
	jmp	.L61
.L86:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE78:
	.size	threadwork, .-threadwork
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC1:
	.string	"started thread %d\n"
.LC2:
	.string	"%d thread exit\n"
	.text
	.p2align 4
	.globl	work
	.type	work, @function
work:
.LFB80:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset 3, -16
	movl	100(%rdi), %edx
	movq	%rdi, %rbx
	leaq	.LC1(%rip), %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movl	92(%rbx), %edx
	testl	%edx, %edx
	jle	.L88
	.p2align 4,,10
	.p2align 3
.L89:
	movq	%rbx, %rdi
	call	threadwork@PLT
	movl	92(%rbx), %eax
	testl	%eax, %eax
	jg	.L89
.L88:
	movl	100(%rbx), %edx
	leaq	.LC2(%rip), %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	call	__printf_chk@PLT
	popq	%rbx
	.cfi_def_cfa_offset 8
	ret
	.cfi_endproc
.LFE80:
	.size	work, .-work
	.p2align 4
	.globl	work2
	.type	work2, @function
work2:
.LFB79:
	.cfi_startproc
	jmp	.L96
	.p2align 4,,10
	.p2align 3
.L94:
	addq	$1, 72(%rdi)
.L96:
	cmpl	$1, 92(%rdi)
	je	.L94
	ret
	.cfi_endproc
.LFE79:
	.size	work2, .-work2
	.section	.rodata.str1.1
.LC3:
	.string	"read mask %d\n"
.LC4:
	.string	"write mask %d\n"
.LC5:
	.string	"prepwrite mask %d\n"
.LC6:
	.string	"Starting %d workers\n"
.LC7:
	.string	"Buffer size %ld\n"
.LC8:
	.string	"offset %ld\n"
.LC9:
	.string	"%ld chunks\n"
	.section	.rodata.str1.8,"aMS",@progbits,1
	.align 8
.LC10:
	.string	"assigning thread %d to cpu %d\n"
	.section	.rodata.str1.1
.LC16:
	.string	"runphased"
.LC17:
	.string	"draining"
.LC18:
	.string	"finished simulation."
.LC19:
	.string	"%ld reads\n"
.LC20:
	.string	"freq: %ld\n"
.LC21:
	.string	"freq_ps: %ld\n"
.LC22:
	.string	"freq latency2: %ld\n"
.LC23:
	.string	"freq per thread latency: %ld\n"
.LC24:
	.string	"freq latency: %ld\n"
.LC25:
	.string	"%ld successreads\n"
.LC26:
	.string	"%ld writes\n"
.LC27:
	.string	"freq_writes: %ld\n"
.LC28:
	.string	"freq_writes_total: %ld\n"
.LC29:
	.string	"freq_writes latency2: %ld\n"
	.section	.rodata.str1.8
	.align 8
.LC30:
	.string	"freq_writes per thread latency: %ld\n"
	.section	.rodata.str1.1
.LC31:
	.string	"freq_writes latency: %ld\n"
.LC32:
	.string	"writer speed"
.LC33:
	.string	"%ld\n"
.LC34:
	.string	"sw %ld\n"
.LC35:
	.string	"%ld good reads per second\n"
	.section	.rodata.str1.8
	.align 8
.LC36:
	.string	"%ld good reads per second latency\n"
	.section	.rodata.str1.1
.LC37:
	.string	"creating sample log"
.LC38:
	.string	"w"
.LC39:
	.string	"%ld%ld %d %d %ld %d %d\n"
	.section	.text.startup,"ax",@progbits
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB81:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	movl	$8, %edx
	movl	$1, %edi
	leaq	.LC3(%rip), %rsi
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	movl	$1, %r14d
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	movq	%r14, %r13
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	movl	$4294967295, %r12d
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$136, %rsp
	.cfi_def_cfa_offset 192
	movq	%fs:40, %rax
	movq	%rax, 120(%rsp)
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movl	$4, %edx
	leaq	.LC4(%rip), %rsi
	xorl	%eax, %eax
	movl	$1, %edi
	call	__printf_chk@PLT
	movl	$32, %edx
	leaq	.LC5(%rip), %rsi
	xorl	%eax, %eax
	movl	$1, %edi
	call	__printf_chk@PLT
	movl	$15, %edx
	leaq	.LC6(%rip), %rsi
	xorl	%eax, %eax
	movl	$1, %edi
	call	__printf_chk@PLT
	movl	$8, %esi
	movl	$15, %edi
	call	calloc@PLT
	movl	$56, %esi
	movl	$15, %edi
	movq	%rax, 48(%rsp)
	call	calloc@PLT
	movl	$15360, %esi
	movl	$1, %edi
	movq	%rax, 56(%rsp)
	call	calloc@PLT
	movq	%r12, %rdi
	movl	$1, %esi
	movq	%rax, %rbx
	call	calloc@PLT
	movq	%r12, %rdx
	movl	$-1, %esi
	movq	%rbx, %r14
	movq	%rax, %rdi
	movq	%rax, %rbp
	call	memset@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC7(%rip), %rsi
	call	__printf_chk@PLT
	movl	$32, %esi
	movl	$100, %edi
	call	calloc@PLT
	xorl	%edx, %edx
	movl	$1, %edi
	leaq	.LC8(%rip), %rsi
	movq	%rax, 16(%rsp)
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC9(%rip), %rsi
	call	__printf_chk@PLT
	movl	$4, %esi
	movl	$15, %edi
	call	calloc@PLT
	movl	$512, %edx
	leaq	72(%rsp), %rdi
	movl	$128, %esi
	movq	%rax, %r12
	call	posix_memalign@PLT
	movl	$12, %esi
	movl	$15, %edi
	testl	%eax, %eax
	movl	$0, %eax
	cmove	72(%rsp), %rax
	movq	%rax, 8(%rsp)
	call	calloc@PLT
	movq	%rbp, 112(%rbx)
	movl	$20, %esi
	movl	$10000000, %edi
	movq	%rax, 24(%rsp)
	call	calloc@PLT
	movl	$20, %esi
	movl	$10000000, %edi
	movq	%rax, %rbp
	call	calloc@PLT
	movq	%rbp, %xmm5
	xorl	%ebp, %ebp
	movq	%rax, %xmm6
	punpcklqdq	%xmm6, %xmm5
	movaps	%xmm5, 32(%rsp)
	.p2align 4,,10
	.p2align 3
.L99:
	movdqa	32(%rsp), %xmm1
	movl	$128, %esi
	movl	%r13d, (%rsp)
	leal	-1(%r13), %r15d
	movl	$1, %edi
	addq	$1024, %r14
	movaps	%xmm1, -96(%r14)
	call	calloc@PLT
	movl	%r13d, %ecx
	movl	$1, %esi
	movl	%r15d, %edx
	movq	%rax, -904(%r14)
	salq	%cl, %rsi
	movl	(%rsp), %ecx
	movl	$1, %edi
	orq	%rsi, (%rax)
	leaq	.LC10(%rip), %rsi
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	8(%rsp), %rax
	movl	%r15d, %edx
	movl	%ebp, -872(%r14)
	sarl	$2, %edx
	movdqa	.LC12(%rip), %xmm2
	movdqa	.LC13(%rip), %xmm3
	movl	$0, -896(%r14)
	movq	%rax, -128(%r14)
	addl	$1, %edx
	movq	.LC11(%rip), %rax
	movl	$48, %esi
	movdqa	.LC14(%rip), %xmm4
	movl	$10000000, %edi
	movl	%r15d, -924(%r14)
	addl	$286331153, %ebp
	movq	%rax, -932(%r14)
	movq	16(%rsp), %rax
	movl	$286331153, -876(%r14)
	movl	$15, -920(%r14)
	movq	%r12, -992(%r14)
	movl	$0, -4(%r12,%r13,4)
	addq	$1, %r13
	movl	%edx, -116(%r14)
	movl	$286331153, -880(%r14)
	movq	%rbx, -984(%r14)
	movq	%rbx, -976(%r14)
	movl	$14, -512(%r14)
	movl	$0, -640(%r14)
	movq	%rax, -864(%r14)
	movl	$0, -824(%r14)
	movl	$15, -216(%r14)
	movaps	%xmm2, -1024(%r14)
	movups	%xmm3, -840(%r14)
	movups	%xmm4, -248(%r14)
	call	calloc@PLT
	movl	$48, %esi
	movl	$10000, %edi
	movl	$10000000, -224(%r14)
	movq	%rax, -232(%r14)
	movq	24(%rsp), %rax
	movq	%rax, -184(%r14)
	call	calloc@PLT
	movl	$10000000, -72(%r14)
	movq	%rax, -208(%r14)
	cmpq	$16, %r13
	jne	.L99
	movq	56(%rsp), %rbp
	movq	48(%rsp), %r15
	movq	%rbx, (%rsp)
	movq	work@GOTPCREL(%rip), %r13
	leaq	840(%rbp), %rax
	movq	%r15, %r12
	movq	%rax, %r14
	.p2align 4,,10
	.p2align 3
.L100:
	movq	%rbx, %rcx
	movq	%rbp, %rsi
	movq	%r15, %rdi
	movq	%r13, %rdx
	call	pthread_create@PLT
	movq	120(%rbx), %rdx
	movq	(%r15), %rdi
	movl	$8, %esi
	addq	$56, %rbp
	addq	$8, %r15
	addq	$1024, %rbx
	call	pthread_setaffinity_np@PLT
	cmpq	%r14, %rbp
	jne	.L100
	movq	(%rsp), %rbx
	leaq	96(%rsp), %rsi
	leaq	80(%rsp), %rdi
	movdqa	.LC15(%rip), %xmm0
	leaq	64(%rsp), %r13
	movaps	%xmm0, 80(%rsp)
	pxor	%xmm0, %xmm0
	movaps	%xmm0, 96(%rsp)
	call	nanosleep@PLT
	leaq	.LC16(%rip), %rdi
	call	puts@PLT
	subl	$1, 92(%rbx)
	leaq	.LC17(%rip), %rdi
	subl	$1, 1116(%rbx)
	subl	$1, 2140(%rbx)
	subl	$1, 3164(%rbx)
	subl	$1, 4188(%rbx)
	subl	$1, 5212(%rbx)
	subl	$1, 6236(%rbx)
	subl	$1, 7260(%rbx)
	subl	$1, 8284(%rbx)
	subl	$1, 9308(%rbx)
	subl	$1, 10332(%rbx)
	subl	$1, 11356(%rbx)
	subl	$1, 12380(%rbx)
	subl	$1, 13404(%rbx)
	subl	$1, 14428(%rbx)
	call	puts@PLT
	movq	48(%rsp), %rbp
	subl	$1, 92(%rbx)
	subl	$1, 1116(%rbx)
	subl	$1, 2140(%rbx)
	subl	$1, 3164(%rbx)
	subl	$1, 4188(%rbx)
	subl	$1, 5212(%rbx)
	subl	$1, 6236(%rbx)
	subl	$1, 7260(%rbx)
	subl	$1, 8284(%rbx)
	subl	$1, 9308(%rbx)
	subl	$1, 10332(%rbx)
	subl	$1, 11356(%rbx)
	subl	$1, 12380(%rbx)
	subl	$1, 13404(%rbx)
	subl	$1, 14428(%rbx)
	addq	$120, %rbp
	.p2align 4,,10
	.p2align 3
.L101:
	movq	(%r12), %rdi
	movq	%r13, %rsi
	addq	$8, %r12
	call	pthread_join@PLT
	cmpq	%rbp, %r12
	jne	.L101
	leaq	.LC18(%rip), %rdi
	leaq	72(%rbx), %rbp
	xorl	%r12d, %r12d
	call	puts@PLT
	leaq	15432(%rbx), %r14
	leaq	.LC19(%rip), %r13
	.p2align 4,,10
	.p2align 3
.L102:
	movq	0(%rbp), %rdx
	movq	%r13, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	addq	$1024, %rbp
	call	__printf_chk@PLT
	addq	-1024(%rbp), %r12
	cmpq	%r14, %rbp
	jne	.L102
	movq	%r12, %rdx
	leaq	.LC20(%rip), %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC21(%rip), %rsi
	leaq	920(%rbx), %rbp
	call	__printf_chk@PLT
	movl	$1000000000, %eax
	leaq	.LC22(%rip), %rsi
	movl	$1, %edi
	cqto
	leaq	16280(%rbx), %r15
	leaq	.LC25(%rip), %r14
	idivq	%r12
	movq	%rax, %r12
	movq	%rax, %rdx
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC23(%rip), %rsi
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC24(%rip), %rsi
	xorl	%r12d, %r12d
	call	__printf_chk@PLT
	.p2align 4,,10
	.p2align 3
.L103:
	movq	0(%rbp), %rdx
	movq	%r14, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	addq	$1024, %rbp
	call	__printf_chk@PLT
	movq	-1024(%rbp), %r13
	addq	%r12, %r13
	movq	%r13, %r12
	cmpq	%rbp, %r15
	jne	.L103
	leaq	80(%rbx), %rbp
	leaq	15440(%rbx), %r15
	xorl	%r12d, %r12d
	leaq	.LC26(%rip), %r14
	.p2align 4,,10
	.p2align 3
.L104:
	movq	0(%rbp), %rdx
	movq	%r14, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	addq	$1024, %rbp
	addq	%rdx, %r12
	call	__printf_chk@PLT
	cmpq	%rbp, %r15
	jne	.L104
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	movl	$1000000000, %ebp
	leaq	.LC27(%rip), %rsi
	leaq	800(%rbx), %r14
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC28(%rip), %rsi
	call	__printf_chk@PLT
	movq	%rbp, %rax
	movl	$1, %edi
	leaq	.LC29(%rip), %rsi
	cqto
	idivq	%r12
	movq	%rax, %r12
	movq	%rax, %rdx
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC30(%rip), %rsi
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC31(%rip), %rsi
	leaq	.LC33(%rip), %r12
	call	__printf_chk@PLT
	leaq	.LC32(%rip), %rdi
	call	puts@PLT
	movq	%r12, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	240(%rbx), %rdx
	subq	224(%rbx), %rdx
	call	__printf_chk@PLT
	movq	%r12, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	256(%rbx), %rdx
	subq	224(%rbx), %rdx
	call	__printf_chk@PLT
	movq	%r12, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	240(%rbx), %rdx
	subq	256(%rbx), %rdx
	call	__printf_chk@PLT
	movq	%r12, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	288(%rbx), %rdx
	subq	272(%rbx), %rdx
	call	__printf_chk@PLT
	movq	%r12, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	272(%rbx), %rdx
	subq	288(%rbx), %rdx
	call	__printf_chk@PLT
	movq	%r12, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	272(%rbx), %rdx
	subq	256(%rbx), %rdx
	call	__printf_chk@PLT
	movq	320(%rbx), %rdx
	movl	$1, %edi
	subq	304(%rbx), %rdx
	leaq	.LC34(%rip), %rsi
	xorl	%eax, %eax
	addq	$16160, %rbx
	call	__printf_chk@PLT
	movq	%r13, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC35(%rip), %rsi
	call	__printf_chk@PLT
	movq	%rbp, %rax
	movl	$1, %edi
	leaq	.LC36(%rip), %rsi
	cqto
	idivq	%r13
	xorl	%r13d, %r13d
	movq	%rax, %rdx
	xorl	%eax, %eax
	call	__printf_chk@PLT
	leaq	.LC37(%rip), %rdi
	call	puts@PLT
	movl	$1, %esi
	movl	$100, %edi
	call	calloc@PLT
	movl	$1, %esi
	movl	$1000, %edi
	movq	%rax, %r12
	call	calloc@PLT
	movq	%r12, %rdi
	leaq	.LC38(%rip), %rsi
	movq	%rax, %rbp
	movabsq	$32481138738815347, %rax
	movq	%rax, (%r12)
	call	fopen@PLT
	movq	%rax, %r12
	.p2align 4,,10
	.p2align 3
.L105:
	movl	(%r14), %ecx
	xorl	%r15d, %r15d
	testl	%ecx, %ecx
	jle	.L108
.L121:
	movq	-8(%r14), %rsi
.L109:
	movslq	%r15d, %rax
	leaq	(%rax,%rax,2), %rdx
	salq	$4, %rdx
	addq	%rsi, %rdx
	cmpl	$1, 36(%rdx)
	je	.L123
	addl	$1, %r15d
	cmpl	%ecx, %r15d
	jl	.L109
.L108:
	addq	$1024, %r14
	cmpq	%r14, %rbx
	jne	.L105
.L110:
	movq	%r12, %rdi
	call	fclose@PLT
	movq	120(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L124
	addq	$136, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L123:
	.cfi_restore_state
	movq	%r13, %rax
	movl	$125, %ecx
	movq	%rbp, %rdi
	movl	$100, %esi
	rep stosq
	movl	$1000, %ecx
	movq	%rbp, %rdi
	addl	$1, %r15d
	leaq	.LC39(%rip), %r8
	movl	40(%rdx), %eax
	movq	8(%rdx), %r9
	pushq	%rax
	.cfi_def_cfa_offset 200
	movl	(%rdx), %eax
	pushq	%rax
	.cfi_def_cfa_offset 208
	movl	44(%rdx), %eax
	pushq	24(%rdx)
	.cfi_def_cfa_offset 216
	pushq	%rax
	.cfi_def_cfa_offset 224
	movl	32(%rdx), %eax
	pushq	%rax
	.cfi_def_cfa_offset 232
	xorl	%eax, %eax
	pushq	16(%rdx)
	.cfi_def_cfa_offset 240
	movl	$1, %edx
	call	__snprintf_chk@PLT
	addq	$48, %rsp
	.cfi_def_cfa_offset 192
	movq	%r12, %rsi
	movq	%rbp, %rdi
	call	fputs@PLT
	movl	(%r14), %ecx
	cmpl	%ecx, %r15d
	jl	.L121
	addq	$1024, %r14
	cmpq	%r14, %rbx
	jne	.L105
	jmp	.L110
.L124:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE81:
	.size	main, .-main
	.section	.rodata.cst8,"aM",@progbits,8
	.align 8
.LC0:
	.long	1
	.long	1
	.align 8
.LC11:
	.long	2
	.long	-1
	.section	.rodata.cst16,"aM",@progbits,16
	.align 16
.LC12:
	.quad	0
	.quad	4294967295
	.align 16
.LC13:
	.quad	4294967295
	.quad	1
	.align 16
.LC14:
	.quad	15
	.quad	15
	.align 16
.LC15:
	.quad	1
	.quad	0
	.ident	"GCC: (GNU) 11.3.0"
	.section	.note.GNU-stack,"",@progbits
