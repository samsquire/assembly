	.file	"stream2-workqueue.c"
	.text
	.p2align 4
	.globl	yield
	.type	yield, @function
yield:
.LFB73:
	.cfi_startproc
	ret
	.cfi_endproc
.LFE73:
	.size	yield, .-yield
	.p2align 4
	.globl	coroutine
	.type	coroutine, @function
coroutine:
.LFB74:
	.cfi_startproc
	cmpl	$1, (%rdx)
	jne	.L4
#APP
# 73 "stream2-workqueue.c" 1
	movq %rip, %rax
# 0 "" 2
	.p2align 4,,10
	.p2align 3
#NO_APP
.L5:
	cmpl	$1, (%rdx)
	movq	%rax, 16(%rsi)
	je	.L5
.L4:
	ret
	.cfi_endproc
.LFE74:
	.size	coroutine, .-coroutine
	.p2align 4
	.globl	pollthreads
	.type	pollthreads, @function
pollthreads:
.LFB75:
	.cfi_startproc
	cmpl	$1, 104(%rdi)
	movq	%rdi, %r9
	jle	.L21
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
.L14:
	movslq	%eax, %rdx
	movl	(%rbx,%rdx,4), %edx
	testl	%edx, %edx
	sete	%sil
	testb	$4, %dl
	jne	.L15
	testb	%sil, %sil
	je	.L9
.L15:
	movslq	(%r8), %rcx
	leal	1(%rcx), %ebp
	movl	%ebp, (%r8)
	movl	%eax, (%r11,%rcx,4)
.L9:
	andl	$8, %edx
	jne	.L16
	testb	%sil, %sil
	je	.L11
.L16:
	movslq	(%rdi), %rdx
	leal	1(%rdx), %ecx
	movl	%ecx, (%rdi)
	movl	%eax, (%r10,%rdx,4)
	addl	$1, %eax
	cmpl	%eax, 104(%r9)
	jg	.L14
	xorl	%eax, %eax
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L11:
	.cfi_restore_state
	addl	$1, %eax
	cmpl	%eax, 104(%r9)
	jg	.L14
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L21:
	.cfi_restore 3
	.cfi_restore 6
	xorl	%eax, %eax
	ret
	.cfi_endproc
.LFE75:
	.size	pollthreads, .-pollthreads
	.p2align 4
	.globl	findavailable
	.type	findavailable, @function
findavailable:
.LFB76:
	.cfi_startproc
	movq	%rdi, %r11
	movq	184(%rdi), %rdi
	movl	(%rdx), %r8d
	addq	$1, %rdi
	testq	%rdi, %rdi
	jle	.L25
	movq	160(%r11), %r10
	xorl	%ecx, %ecx
	xorl	%r9d, %r9d
	xorl	%eax, %eax
	jmp	.L27
	.p2align 4,,10
	.p2align 3
.L26:
	addl	$1, %ecx
	movslq	%ecx, %rax
	movq	%rax, %r9
	cmpq	%rdi, %rax
	jge	.L25
.L27:
	salq	$5, %rax
	cmpl	$1, 16(%r10,%rax)
	jne	.L26
	movslq	%r8d, %rax
	addl	$1, %r8d
	movq	%r9, (%rsi,%rax,8)
	movl	%r8d, (%rdx)
	movl	104(%r11), %eax
	addl	%eax, %eax
	cmpl	%eax, %r8d
	je	.L25
	movq	184(%r11), %rdi
	addl	$1, %ecx
	movslq	%ecx, %rax
	addq	$1, %rdi
	movq	%rax, %r9
	cmpq	%rdi, %rax
	jl	.L27
.L25:
	xorl	%eax, %eax
	testl	%r8d, %r8d
	sete	%al
	ret
	.cfi_endproc
.LFE76:
	.size	findavailable, .-findavailable
	.p2align 4
	.globl	singlewriter3
	.type	singlewriter3, @function
singlewriter3:
.LFB77:
	.cfi_startproc
	ret
	.cfi_endproc
.LFE77:
	.size	singlewriter3, .-singlewriter3
	.p2align 4
	.globl	singlewriter2
	.type	singlewriter2, @function
singlewriter2:
.LFB78:
	.cfi_startproc
	movl	512(%rdi), %eax
	testl	%eax, %eax
	je	.L37
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
	je	.L40
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%rbp
	.cfi_def_cfa_offset 16
	popq	%r12
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L37:
	.cfi_restore 3
	.cfi_restore 6
	.cfi_restore 12
	ret
	.p2align 4,,10
	.p2align 3
.L40:
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
.LFE78:
	.size	singlewriter2, .-singlewriter2
	.p2align 4
	.globl	singlewriter
	.type	singlewriter, @function
singlewriter:
.LFB79:
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
	je	.L41
	leaq	16(%rsp), %r8
	leaq	12(%rsp), %rcx
	movq	%r12, %rdx
	movq	%r13, %rsi
	movq	%rbp, %rdi
	call	pollthreads@PLT
	movslq	12(%rsp), %r8
	testl	%r8d, %r8d
	jle	.L55
	movl	20(%rsp), %r9d
	xorl	%ecx, %ecx
	jmp	.L44
	.p2align 4,,10
	.p2align 3
.L63:
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
	je	.L43
.L44:
	movl	%ecx, %esi
	cmpq	%r9, %rcx
	jne	.L63
.L43:
	movl	16(%rsp), %r9d
	testl	%r9d, %r9d
	jle	.L48
	movl	20(%rsp), %r8d
	addl	%esi, %r9d
	jmp	.L50
	.p2align 4,,10
	.p2align 3
.L61:
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
	je	.L48
	movl	%edi, %esi
.L50:
	cmpl	%esi, %r8d
	jne	.L61
.L48:
	movl	104(%rbp), %edi
	testl	%edi, %edi
	jle	.L47
	movq	48(%rbp), %r8
	xorl	%edx, %edx
	.p2align 4,,10
	.p2align 3
.L53:
	movslq	%edx, %rcx
	movq	%rcx, %rax
	salq	$10, %rax
	addq	%r8, %rax
	movl	200(%rax), %esi
	testl	%esi, %esi
	je	.L51
	movq	32(%rax), %rax
	addl	$1, %edx
	movl	%esi, (%rax,%rcx,4)
	movl	104(%rbp), %edi
	cmpl	%edi, %edx
	jl	.L53
.L47:
	xorl	%eax, %eax
.L41:
	movq	24(%rsp), %rdx
	subq	%fs:40, %rdx
	jne	.L64
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
.L51:
	.cfi_restore_state
	addl	$1, %edx
	cmpl	%edi, %edx
	jl	.L53
	jmp	.L47
.L55:
	xorl	%esi, %esi
	jmp	.L43
.L64:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE79:
	.size	singlewriter, .-singlewriter
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC1:
	.string	"%%rsp %p\n"
	.text
	.p2align 4
	.globl	threadwork
	.type	threadwork, @function
threadwork:
.LFB80:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	leaq	.LC1(%rip), %rsi
	pushq	%r13
	.cfi_def_cfa_offset 24
	.cfi_offset 13, -24
	pushq	%r12
	.cfi_def_cfa_offset 32
	.cfi_offset 12, -32
	pushq	%rbp
	.cfi_def_cfa_offset 40
	.cfi_offset 6, -40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset 3, -48
	movq	%rdi, %rbx
#APP
# 475 "stream2-workqueue.c" 1
	mov %rsp, %rdx
# 0 "" 2
#NO_APP
	subq	$32, %rsp
	.cfi_def_cfa_offset 80
	movq	%fs:40, %rax
	movq	%rax, 24(%rsp)
	xorl	%eax, %eax
	movq	968(%rdi), %rax
	movl	$1, %edi
	movq	%rdx, (%rax)
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%rsp, %rsi
	movl	$4, %edi
	call	clock_gettime@PLT
	cmpl	$2, 92(%rbx)
	je	.L89
.L66:
	movl	908(%rbx), %ebp
	movq	40(%rbx), %r12
	movslq	904(%rbx), %rcx
	movl	%ebp, %eax
	movq	896(%r12), %rdx
	sall	$7, %eax
	cltq
	movq	(%rdx,%rax,8), %rax
	cmpq	%rcx, %rax
	je	.L72
	movl	$0, 384(%rbx)
.L72:
	movl	912(%rbx), %esi
	movl	%eax, 904(%rbx)
	movq	840(%rbx), %r9
	movl	%esi, %eax
	sall	$7, %eax
	cltq
	movq	(%rdx,%rax,8), %rcx
	movslq	%esi, %rdx
	leaq	(%rdx,%rdx,2), %rax
	movl	(%r9,%rax,4), %eax
	testq	%rcx, %rcx
	je	.L84
	movslq	%eax, %rdi
	cmpq	%rcx, %rdi
	jge	.L73
.L84:
	movl	104(%rbx), %r10d
	subl	$1, %r10d
	testl	%r10d, %r10d
	jle	.L73
	xorl	%r11d, %r11d
	jmp	.L81
	.p2align 4,,10
	.p2align 3
.L79:
	addl	$1, %r11d
	cmpl	%r10d, %r11d
	jge	.L73
.L80:
	movslq	%esi, %rdx
	movq	40(%rbx), %r12
	leaq	(%rdx,%rdx,2), %rax
	movl	(%r9,%rax,4), %eax
.L81:
	subl	$1, %eax
	leaq	(%rdx,%rdx,2), %r8
	addq	$1, 72(%rbx)
	movslq	%eax, %rdx
	movl	%eax, %r13d
	salq	$2, %r8
	imulq	$-2139062143, %rdx, %rdx
	sarl	$31, %r13d
	leaq	(%r9,%r8), %rdi
	movl	4(%rdi), %ecx
	shrq	$32, %rdx
	movl	%ecx, %r14d
	addl	%eax, %edx
	sarl	$7, %edx
	subl	%r13d, %edx
	movl	%edx, %r13d
	sall	$8, %r13d
	subl	%edx, %r13d
	xorl	%edx, %edx
	subl	%r13d, %eax
	movl	%esi, %r13d
	cltq
	testq	%rax, %rax
	cmovs	%rdx, %rax
	movslq	%ecx, %rdx
	sarl	$31, %r14d
	imulq	$-2139062143, %rdx, %rdx
	sall	$24, %r13d
	salq	$16, %rax
	shrq	$32, %rdx
	addl	%ecx, %edx
	sarl	$7, %edx
	subl	%r14d, %edx
	movl	%edx, %r14d
	sall	$8, %r14d
	subl	%edx, %r14d
	movl	%ecx, %edx
	subl	%r14d, %edx
	orl	%edx, %r13d
	movslq	%r13d, %r13
	orq	%r13, %rax
	addq	112(%r12), %rax
	cmpb	$-1, (%rax)
	je	.L75
	addq	$1, 920(%rbx)
	movb	$-1, (%rax)
	movq	840(%rbx), %r9
	movl	104(%rbx), %r10d
	movl	912(%rbx), %esi
	leaq	(%r9,%r8), %rdi
	movl	908(%rbx), %ebp
	movl	4(%rdi), %ecx
	subl	$1, %r10d
.L75:
	cmpl	$4, %ecx
	jg	.L76
	addl	$1, %ecx
	addl	$1, (%rdi)
	movl	%ecx, 4(%rdi)
.L76:
	cmpl	$5, %ecx
	jne	.L77
	addl	$1, %esi
	movl	%esi, 912(%rbx)
	movl	$0, 4(%rdi)
.L77:
	cmpl	%esi, %ebp
	jne	.L78
	leal	1(%rbp), %esi
	movl	%esi, 912(%rbx)
.L78:
	cmpl	$5, %esi
	jne	.L79
	movl	$1, 912(%rbx)
	addl	$1, %r11d
	cmpl	%r10d, %r11d
	jge	.L73
	movl	$1, %esi
	jmp	.L80
	.p2align 4,,10
	.p2align 3
.L73:
	movq	24(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L90
	addq	$32, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 48
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%rbp
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r13
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L89:
	.cfi_restore_state
	movl	104(%rbx), %eax
	testl	%eax, %eax
	jle	.L70
	movl	384(%rbx), %ecx
	xorl	%esi, %esi
	movabsq	$-9187201950435737471, %r8
	.p2align 4,,10
	.p2align 3
.L71:
	movl	908(%rbx), %r10d
	movq	40(%rbx), %r9
	movl	100(%rbx), %edi
	movl	%r10d, %eax
	movq	896(%r9), %rdx
	sall	$24, %r10d
	sall	$7, %eax
	cltq
	movq	(%rdx,%rax,8), %r11
	movq	%r11, %rax
	imulq	%r8
	movq	%r11, %rax
	sarq	$63, %rax
	addq	%r11, %rdx
	sarq	$7, %rdx
	subq	%rax, %rdx
	movq	%rdx, %rax
	salq	$8, %rax
	subq	%rdx, %rax
	movslq	%ecx, %rdx
	imulq	$-2139062143, %rdx, %rdx
	subq	%rax, %r11
	movl	%ecx, %eax
	sarl	$31, %eax
	sall	$16, %r11d
	shrq	$32, %rdx
	addl	%ecx, %edx
	sarl	$7, %edx
	subl	%eax, %edx
	movl	%edx, %eax
	sall	$8, %eax
	subl	%edx, %eax
	subl	%eax, %ecx
	orl	%r10d, %ecx
	orl	%r11d, %ecx
	movslq	%ecx, %rcx
	addq	112(%r9), %rcx
	cmpb	$-1, (%rcx)
	je	.L68
	addq	$1, 80(%rbx)
	addl	$1, %esi
	movb	%dil, (%rcx)
	movl	384(%rbx), %eax
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
	cmpl	104(%rbx), %esi
	jl	.L71
.L70:
	movq	40(%rbx), %rdx
	movl	908(%rbx), %eax
	movq	896(%rdx), %rdx
	sall	$7, %eax
	cltq
	lock addq	$1, (%rdx,%rax,8)
	jmp	.L66
	.p2align 4,,10
	.p2align 3
.L68:
	movb	%dil, (%rcx)
	movl	384(%rbx), %eax
	addl	$1, %esi
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
	cmpl	%esi, 104(%rbx)
	jg	.L71
	jmp	.L70
.L90:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE80:
	.size	threadwork, .-threadwork
	.section	.rodata.str1.1
.LC2:
	.string	"started thread %d\n"
.LC3:
	.string	"%d thread exit\n"
	.text
	.p2align 4
	.globl	work
	.type	work, @function
work:
.LFB82:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset 3, -16
	movl	100(%rdi), %edx
	movq	%rdi, %rbx
	leaq	.LC2(%rip), %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movl	92(%rbx), %edx
	testl	%edx, %edx
	jle	.L92
	.p2align 4,,10
	.p2align 3
.L93:
	movq	%rbx, %rdi
	call	threadwork@PLT
	movl	92(%rbx), %eax
	testl	%eax, %eax
	jg	.L93
.L92:
	movl	100(%rbx), %edx
	leaq	.LC3(%rip), %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	call	__printf_chk@PLT
	popq	%rbx
	.cfi_def_cfa_offset 8
	ret
	.cfi_endproc
.LFE82:
	.size	work, .-work
	.p2align 4
	.globl	work2
	.type	work2, @function
work2:
.LFB81:
	.cfi_startproc
	jmp	.L100
	.p2align 4,,10
	.p2align 3
.L98:
	addq	$1, 72(%rdi)
.L100:
	cmpl	$1, 92(%rdi)
	je	.L98
	ret
	.cfi_endproc
.LFE81:
	.size	work2, .-work2
	.section	.rodata.str1.1
.LC4:
	.string	"read mask %d\n"
.LC5:
	.string	"write mask %d\n"
.LC6:
	.string	"prepwrite mask %d\n"
.LC7:
	.string	"Starting %d workers\n"
.LC8:
	.string	"Buffer size %ld\n"
.LC9:
	.string	"offset %ld\n"
.LC10:
	.string	"%ld chunks\n"
	.section	.rodata.str1.8,"aMS",@progbits,1
	.align 8
.LC11:
	.string	"assigning thread %d to cpu %d\n"
	.section	.rodata.str1.1
.LC17:
	.string	"runphased"
.LC18:
	.string	"draining"
.LC19:
	.string	"finished simulation."
.LC20:
	.string	"%ld reads\n"
.LC21:
	.string	"freq: %ld\n"
.LC22:
	.string	"freq_ps: %ld\n"
.LC23:
	.string	"freq latency2: %ld\n"
.LC24:
	.string	"freq per thread latency: %ld\n"
.LC25:
	.string	"freq latency: %ld\n"
.LC26:
	.string	"%ld successreads\n"
.LC27:
	.string	"%ld writes\n"
.LC28:
	.string	"freq_writes: %ld\n"
.LC29:
	.string	"freq_writes_total: %ld\n"
.LC30:
	.string	"freq_writes latency2: %ld\n"
	.section	.rodata.str1.8
	.align 8
.LC31:
	.string	"freq_writes per thread latency: %ld\n"
	.section	.rodata.str1.1
.LC32:
	.string	"freq_writes latency: %ld\n"
.LC33:
	.string	"writer speed"
.LC34:
	.string	"%ld\n"
.LC35:
	.string	"sw %ld\n"
.LC36:
	.string	"%ld good reads per second\n"
	.section	.rodata.str1.8
	.align 8
.LC37:
	.string	"%ld good reads per second latency\n"
	.section	.rodata.str1.1
.LC38:
	.string	"w"
.LC39:
	.string	"index %ld\n"
.LC40:
	.string	"rsp %ld\n"
.LC41:
	.string	"eip %ld\n"
	.section	.text.startup,"ax",@progbits
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB83:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	movl	$8, %edx
	movl	$1, %edi
	leaq	.LC4(%rip), %rsi
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	movl	$4294967295, %r13d
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$168, %rsp
	.cfi_def_cfa_offset 224
	movq	%fs:40, %rax
	movq	%rax, 152(%rsp)
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movl	$4, %edx
	leaq	.LC5(%rip), %rsi
	xorl	%eax, %eax
	movl	$1, %edi
	call	__printf_chk@PLT
	movl	$32, %edx
	leaq	.LC6(%rip), %rsi
	xorl	%eax, %eax
	movl	$1, %edi
	call	__printf_chk@PLT
	movl	$15, %edx
	leaq	.LC7(%rip), %rsi
	xorl	%eax, %eax
	movl	$1, %edi
	call	__printf_chk@PLT
	movl	$8, %esi
	movl	$15, %edi
	call	calloc@PLT
	movl	$56, %esi
	movl	$15, %edi
	movq	%rax, 80(%rsp)
	call	calloc@PLT
	movl	$15360, %esi
	movl	$1, %edi
	movq	%rax, 88(%rsp)
	call	calloc@PLT
	movq	%r13, %rdi
	movl	$1, %esi
	movq	%rax, %r12
	call	calloc@PLT
	movq	%r13, %rdx
	movl	$-1, %esi
	movq	%r12, %r15
	movq	%rax, %rdi
	movq	%rax, %rbx
	call	memset@PLT
	movq	%r13, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC8(%rip), %rsi
	call	__printf_chk@PLT
	movl	$32, %esi
	movl	$100, %edi
	call	calloc@PLT
	xorl	%edx, %edx
	movl	$1, %edi
	leaq	.LC9(%rip), %rsi
	movq	%rax, 32(%rsp)
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%r13, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC10(%rip), %rsi
	movl	$1, %r13d
	call	__printf_chk@PLT
	movl	$4, %esi
	movl	$15, %edi
	call	calloc@PLT
	movl	$512, %edx
	leaq	104(%rsp), %rdi
	movl	$128, %esi
	movq	%rax, 40(%rsp)
	call	posix_memalign@PLT
	movl	$12, %esi
	movl	$15, %edi
	testl	%eax, %eax
	movl	$0, %eax
	cmove	104(%rsp), %rax
	xorl	%r14d, %r14d
	movq	%rax, 24(%rsp)
	call	calloc@PLT
	movq	%rbx, 112(%r12)
	movl	$20, %esi
	movl	$100000000, %edi
	movq	%rax, 48(%rsp)
	call	calloc@PLT
	movl	$20, %esi
	movl	$100000000, %edi
	movq	%rax, %rbx
	call	calloc@PLT
	movq	%rbx, %xmm5
	movl	$8, %esi
	movl	$1, %edi
	movq	%rax, %xmm6
	punpcklqdq	%xmm6, %xmm5
	movaps	%xmm5, 64(%rsp)
	call	calloc@PLT
	movq	%r12, 16(%rsp)
	movq	%rax, 56(%rsp)
	.p2align 4,,10
	.p2align 3
.L104:
	movl	$32, %esi
	movl	$10, %edi
	movl	%r13d, 8(%rsp)
	leal	-1(%r13), %ebp
	call	calloc@PLT
	movq	%rax, 960(%r15)
	leaq	24(%rax), %r12
	leaq	344(%rax), %rbx
	.p2align 4,,10
	.p2align 3
.L103:
	movl	$4, %esi
	movl	$1, %edi
	addq	$32, %r12
	call	calloc@PLT
	movq	%rax, -32(%r12)
	cmpq	%rbx, %r12
	jne	.L103
	movq	56(%rsp), %rax
	movdqa	64(%rsp), %xmm1
	movl	$128, %esi
	movl	$1, %edi
	addq	$1024, %r15
	movq	%rax, -56(%r15)
	movaps	%xmm1, -96(%r15)
	call	calloc@PLT
	movzbl	8(%rsp), %ecx
	movl	$1, %edx
	leaq	.LC11(%rip), %rsi
	movq	%rax, -904(%r15)
	movl	$1, %edi
	salq	%cl, %rdx
	orq	%rdx, (%rax)
	movl	%r13d, %ecx
	movl	%ebp, %edx
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	24(%rsp), %rax
	movl	%r14d, -872(%r15)
	movl	$48, %esi
	movl	%ebp, -924(%r15)
	sarl	$2, %ebp
	movdqa	.LC13(%rip), %xmm2
	movl	$10000000, %edi
	movq	%rax, -128(%r15)
	addl	$1, %ebp
	movq	.LC12(%rip), %rax
	addl	$286331153, %r14d
	movdqa	.LC14(%rip), %xmm3
	movdqa	.LC15(%rip), %xmm4
	movl	$0, -896(%r15)
	movq	%rax, -932(%r15)
	movq	40(%rsp), %rax
	movl	$286331153, -876(%r15)
	movq	%rax, -992(%r15)
	movl	$15, -920(%r15)
	movl	$0, -4(%rax,%r13,4)
	movq	16(%rsp), %rax
	addq	$1, %r13
	movl	$286331153, -880(%r15)
	movq	%rax, -984(%r15)
	movq	%rax, -976(%r15)
	movq	32(%rsp), %rax
	movl	$14, -512(%r15)
	movl	$0, -640(%r15)
	movq	%rax, -864(%r15)
	movl	$0, -824(%r15)
	movl	%ebp, -116(%r15)
	movl	$15, -216(%r15)
	movaps	%xmm2, -1024(%r15)
	movups	%xmm3, -840(%r15)
	movups	%xmm4, -248(%r15)
	call	calloc@PLT
	movl	$48, %esi
	movl	$10000, %edi
	movl	$10000000, -224(%r15)
	movq	%rax, -232(%r15)
	movq	48(%rsp), %rax
	movq	%rax, -184(%r15)
	call	calloc@PLT
	movl	$100000000, -72(%r15)
	movq	%rax, -208(%r15)
	cmpq	$16, %r13
	jne	.L104
	movq	80(%rsp), %r15
	movq	88(%rsp), %rbx
	movq	16(%rsp), %r12
	movq	work@GOTPCREL(%rip), %r13
	movq	%r15, 8(%rsp)
	leaq	840(%rbx), %rax
	movq	%r12, %rbp
	movq	%rax, %r14
	.p2align 4,,10
	.p2align 3
.L105:
	movq	%rbp, %rcx
	movq	%rbx, %rsi
	movq	%r15, %rdi
	movq	%r13, %rdx
	call	pthread_create@PLT
	movq	120(%rbp), %rdx
	movq	(%r15), %rdi
	movl	$8, %esi
	addq	$56, %rbx
	addq	$8, %r15
	addq	$1024, %rbp
	call	pthread_setaffinity_np@PLT
	cmpq	%r14, %rbx
	jne	.L105
	leaq	112(%rsp), %rdi
	movq	8(%rsp), %rbp
	leaq	96(%rsp), %r13
	movdqa	.LC16(%rip), %xmm0
	leaq	128(%rsp), %rsi
	movaps	%xmm0, 112(%rsp)
	pxor	%xmm0, %xmm0
	movaps	%xmm0, 128(%rsp)
	call	nanosleep@PLT
	leaq	.LC17(%rip), %rdi
	call	puts@PLT
	subl	$1, 92(%r12)
	leaq	.LC18(%rip), %rdi
	subl	$1, 1116(%r12)
	subl	$1, 2140(%r12)
	subl	$1, 3164(%r12)
	subl	$1, 4188(%r12)
	subl	$1, 5212(%r12)
	subl	$1, 6236(%r12)
	subl	$1, 7260(%r12)
	subl	$1, 8284(%r12)
	subl	$1, 9308(%r12)
	subl	$1, 10332(%r12)
	subl	$1, 11356(%r12)
	subl	$1, 12380(%r12)
	subl	$1, 13404(%r12)
	subl	$1, 14428(%r12)
	call	puts@PLT
	movq	80(%rsp), %rbx
	subl	$1, 92(%r12)
	subl	$1, 1116(%r12)
	subl	$1, 2140(%r12)
	subl	$1, 3164(%r12)
	subl	$1, 4188(%r12)
	subl	$1, 5212(%r12)
	subl	$1, 6236(%r12)
	subl	$1, 7260(%r12)
	subl	$1, 8284(%r12)
	subl	$1, 9308(%r12)
	subl	$1, 10332(%r12)
	subl	$1, 11356(%r12)
	subl	$1, 12380(%r12)
	subl	$1, 13404(%r12)
	subl	$1, 14428(%r12)
	addq	$120, %rbx
	.p2align 4,,10
	.p2align 3
.L106:
	movq	0(%rbp), %rdi
	movq	%r13, %rsi
	addq	$8, %rbp
	call	pthread_join@PLT
	cmpq	%rbp, %rbx
	jne	.L106
	leaq	.LC19(%rip), %rdi
	leaq	72(%r12), %rbx
	xorl	%ebp, %ebp
	call	puts@PLT
	leaq	15432(%r12), %r14
	leaq	.LC20(%rip), %r13
	.p2align 4,,10
	.p2align 3
.L107:
	movq	(%rbx), %rdx
	movq	%r13, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	addq	$1024, %rbx
	call	__printf_chk@PLT
	addq	-1024(%rbx), %rbp
	cmpq	%rbx, %r14
	jne	.L107
	movq	%rbp, %rdx
	leaq	.LC21(%rip), %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%rbp, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC22(%rip), %rsi
	leaq	920(%r12), %rbx
	call	__printf_chk@PLT
	movl	$1000000000, %eax
	leaq	.LC23(%rip), %rsi
	movl	$1, %edi
	cqto
	leaq	16280(%r12), %r15
	leaq	.LC26(%rip), %r14
	idivq	%rbp
	xorl	%ebp, %ebp
	movq	%rax, %r13
	movq	%rax, %rdx
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%r13, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC24(%rip), %rsi
	call	__printf_chk@PLT
	movq	%r13, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC25(%rip), %rsi
	call	__printf_chk@PLT
	.p2align 4,,10
	.p2align 3
.L108:
	movq	(%rbx), %rdx
	movq	%r14, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	addq	$1024, %rbx
	call	__printf_chk@PLT
	addq	-1024(%rbx), %rbp
	movq	%rbp, %r13
	cmpq	%rbx, %r15
	jne	.L108
	leaq	80(%r12), %rbx
	xorl	%ebp, %ebp
	leaq	15440(%r12), %r15
	leaq	.LC27(%rip), %r14
	.p2align 4,,10
	.p2align 3
.L109:
	movq	(%rbx), %rdx
	movq	%r14, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	addq	$1024, %rbx
	addq	%rdx, %rbp
	call	__printf_chk@PLT
	cmpq	%rbx, %r15
	jne	.L109
	movq	%rbp, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	movl	$1000000000, %ebx
	leaq	.LC28(%rip), %rsi
	call	__printf_chk@PLT
	movq	%rbp, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC29(%rip), %rsi
	call	__printf_chk@PLT
	movq	%rbx, %rax
	movl	$1, %edi
	leaq	.LC30(%rip), %rsi
	cqto
	idivq	%rbp
	leaq	.LC34(%rip), %rbp
	movq	%rax, %r14
	movq	%rax, %rdx
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%r14, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC31(%rip), %rsi
	call	__printf_chk@PLT
	movq	%r14, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC32(%rip), %rsi
	call	__printf_chk@PLT
	leaq	.LC33(%rip), %rdi
	call	puts@PLT
	movq	%rbp, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	240(%r12), %rdx
	subq	224(%r12), %rdx
	call	__printf_chk@PLT
	movq	%rbp, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	256(%r12), %rdx
	subq	224(%r12), %rdx
	call	__printf_chk@PLT
	movq	%rbp, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	240(%r12), %rdx
	subq	256(%r12), %rdx
	call	__printf_chk@PLT
	movq	%rbp, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	288(%r12), %rdx
	subq	272(%r12), %rdx
	call	__printf_chk@PLT
	movq	%rbp, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	272(%r12), %rdx
	subq	288(%r12), %rdx
	call	__printf_chk@PLT
	movq	%rbp, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	272(%r12), %rdx
	subq	256(%r12), %rdx
	call	__printf_chk@PLT
	movq	320(%r12), %rdx
	movl	$1, %edi
	subq	304(%r12), %rdx
	leaq	.LC35(%rip), %rsi
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%r13, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC36(%rip), %rsi
	call	__printf_chk@PLT
	movq	%rbx, %rax
	movl	$1, %edi
	xorl	%ebx, %ebx
	cqto
	leaq	.LC37(%rip), %rsi
	idivq	%r13
	movq	%rax, %rdx
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movl	$1, %esi
	movl	$100, %edi
	call	calloc@PLT
	movl	$1, %esi
	movl	$1000, %edi
	movq	%rax, %r12
	call	calloc@PLT
	movdqa	.LC42(%rip), %xmm0
	movq	%r12, %rdi
	movb	$0, 16(%r12)
	leaq	.LC38(%rip), %rsi
	movq	%rax, %rbp
	movups	%xmm0, (%r12)
	call	fopen@PLT
	movl	$125, %ecx
	movq	%rbp, %rdi
	xorl	%r9d, %r9d
	movq	%rax, %r12
	movq	%rbx, %rax
	movl	$1, %edx
	movl	$100, %esi
	rep stosq
	leaq	.LC39(%rip), %r8
	movl	$1000, %ecx
	movq	%rbp, %rdi
	call	__snprintf_chk@PLT
	movq	%r12, %rsi
	movq	%rbp, %rdi
	call	fputs@PLT
	movq	%rbx, %rax
	movl	$125, %ecx
	movq	%rbp, %rdi
	rep stosq
	movl	$8, %r9d
	movl	$1000, %ecx
	movq	%rbp, %rdi
	leaq	.LC40(%rip), %r8
	movl	$1, %edx
	movl	$100, %esi
	call	__snprintf_chk@PLT
	movq	%r12, %rsi
	movq	%rbp, %rdi
	call	fputs@PLT
	movq	%rbx, %rax
	movl	$125, %ecx
	movq	%rbp, %rdi
	rep stosq
	movl	$16, %r9d
	movl	$1000, %ecx
	movq	%rbp, %rdi
	leaq	.LC41(%rip), %r8
	movl	$1, %edx
	movl	$100, %esi
	call	__snprintf_chk@PLT
	movq	%rbp, %rdi
	movq	%r12, %rsi
	call	fputs@PLT
	movq	%r12, %rdi
	call	fclose@PLT
	movq	152(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L119
	addq	$168, %rsp
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
.L119:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE83:
	.size	main, .-main
	.section	.rodata.cst8,"aM",@progbits,8
	.align 8
.LC0:
	.long	1
	.long	1
	.align 8
.LC12:
	.long	2
	.long	-1
	.section	.rodata.cst16,"aM",@progbits,16
	.align 16
.LC13:
	.quad	0
	.quad	4294967295
	.align 16
.LC14:
	.quad	4294967295
	.quad	1
	.align 16
.LC15:
	.quad	15
	.quad	15
	.align 16
.LC16:
	.quad	1
	.quad	0
	.align 16
.LC42:
	.quad	7956018264456458083
	.quad	8386676065534422629
	.ident	"GCC: (GNU) 11.3.0"
	.section	.note.GNU-stack,"",@progbits
