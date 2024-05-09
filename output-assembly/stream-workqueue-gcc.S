	.file	"stream-workqueue.c"
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
	subq	$40, %rsp
	.cfi_def_cfa_offset 96
	movq	40(%rdi), %rdx
	movq	%fs:40, %rax
	movq	%rax, 24(%rsp)
	xorl	%eax, %eax
	movl	908(%rdi), %eax
	movq	%rsp, %rsi
	movl	$4, %edi
	movq	896(%rdx), %rdx
	sall	$7, %eax
	cltq
	movq	(%rdx,%rax,8), %rbp
	call	clock_gettime@PLT
	movl	908(%rbx), %esi
	movq	40(%rbx), %r8
	addq	$1, 80(%rbx)
	movslq	104(%rbx), %r9
	movl	%esi, %eax
	movq	896(%r8), %rdx
	movslq	100(%rbx), %r12
	sall	$7, %eax
	movdqa	(%rsp), %xmm0
	cltq
	movq	%r12, %rdi
	movq	(%rdx,%rax,8), %rax
	cqto
	idivq	%r9
	movabsq	$-9187201950435737471, %rdx
	movq	%rax, %rcx
	imulq	%rdx
	movq	%rcx, %rax
	sarq	$63, %rax
	addq	%rcx, %rdx
	sarq	$7, %rdx
	subq	%rax, %rdx
	movq	%rdx, %rax
	salq	$8, %rax
	subq	%rdx, %rax
	subq	%rax, %rcx
	movl	%esi, %eax
	sall	$24, %eax
	salq	$16, %rcx
	orl	%r12d, %eax
	salq	$10, %r12
	addq	48(%rbx), %r12
	movslq	804(%r12), %rdx
	cltq
	orq	%rax, %rcx
	movq	%rdx, %rax
	leaq	(%rdx,%rdx,2), %rsi
	addl	$1, %eax
	salq	$4, %rsi
	addq	792(%r12), %rsi
	cltd
	movups	%xmm0, 8(%rsi)
	idivl	800(%r12)
	movq	112(%r8), %rax
	movl	%edx, 804(%r12)
	movl	%edi, (%rsi)
	movq	%rcx, 24(%rsi)
	movl	$1, 36(%rsi)
	movb	%dil, (%rax,%rcx)
	movq	40(%rbx), %rdx
	movl	908(%rbx), %eax
	movq	896(%rdx), %rdx
	sall	$7, %eax
	cltq
	lock addq	$1, (%rdx,%rax,8)
	movq	40(%rbx), %rax
	movslq	908(%rbx), %rdx
	movslq	104(%rbx), %rcx
	movq	896(%rax), %rax
	movq	(%rax,%rdx,8), %rax
	cqto
	idivq	%rcx
	movq	%rax, %r13
	movslq	904(%rbx), %rax
	cmpq	%r13, %rax
	je	.L61
	movslq	100(%rbx), %r14
	movl	$4, %edi
	salq	$10, %r14
	addq	48(%rbx), %r14
	movslq	804(%r14), %rax
	leaq	(%rax,%rax,2), %r15
	salq	$4, %r15
	addq	792(%r14), %r15
	leaq	8(%r15), %rsi
	call	clock_gettime@PLT
	movl	804(%r14), %eax
	addl	$1, %eax
	cltd
	idivl	800(%r14)
	movl	100(%rbx), %eax
	movl	%edx, 804(%r14)
	movl	%eax, (%r15)
	movq	.LC0(%rip), %rax
	movq	%rax, 32(%r15)
.L61:
	movq	840(%rbx), %rcx
	movl	%r13d, 904(%rbx)
	cmpq	%rbp, %rcx
	jge	.L63
	movslq	804(%r12), %rdx
	movdqa	(%rsp), %xmm1
	movslq	104(%rbx), %r8
	movl	512(%rbx), %esi
	movq	%rdx, %rax
	leaq	(%rdx,%rdx,2), %rdi
	addq	$1, 72(%rbx)
	movl	100(%rbx), %r11d
	addl	$1, %eax
	salq	$4, %rdi
	movl	912(%rbx), %r10d
	movq	%r8, %r9
	cltd
	addq	792(%r12), %rdi
	idivl	800(%r12)
	movups	%xmm1, 8(%rdi)
	movq	%rcx, %rax
	movl	%edx, 804(%r12)
	cqto
	movl	%esi, %r12d
	idivq	%r8
	movl	%r11d, (%rdi)
	movl	$1, 36(%rdi)
	movabsq	$-9187201950435737471, %rdx
	leaq	-2(%rax), %rbp
	movq	%rbp, %rax
	imulq	%rdx
	movq	%rbp, %rax
	sarq	$63, %rax
	addq	%rbp, %rdx
	sarq	$7, %rdx
	subq	%rax, %rdx
	movq	%rdx, %rax
	salq	$8, %rax
	subq	%rdx, %rax
	movq	%rbp, %rdx
	movl	%r10d, %ebp
	subq	%rax, %rdx
	movl	$0, %eax
	cmovs	%rax, %rdx
	movslq	%esi, %rax
	sarl	$31, %r12d
	imulq	$-2139062143, %rax, %rax
	sall	$24, %ebp
	salq	$16, %rdx
	shrq	$32, %rax
	addl	%esi, %eax
	sarl	$7, %eax
	subl	%r12d, %eax
	movl	%eax, %r12d
	sall	$8, %r12d
	subl	%eax, %r12d
	movl	%esi, %eax
	subl	%r12d, %eax
	orl	%eax, %ebp
	leal	1(%rsi), %eax
	movslq	%ebp, %rbp
	orq	%rbp, %rdx
	movq	%rdx, 24(%rdi)
	cmpl	%eax, %r8d
	je	.L72
.L65:
	cltd
	idivl	%r9d
	leal	1(%r11), %eax
	cmpl	%edx, %r11d
	cmovne	%edx, %eax
	movl	%eax, %esi
	leaq	1(%rcx), %rax
	cqto
	movq	%rax, 840(%rbx)
	idivq	%r8
	xorl	%eax, %eax
	testq	%rdx, %rdx
	cmovne	%esi, %eax
	movl	%eax, 512(%rbx)
.L63:
	movq	24(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L73
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
.L72:
	.cfi_restore_state
	addl	$1, %r10d
	movslq	%r10d, %rdx
	movl	%r10d, %esi
	imulq	$1717986919, %rdx, %rdx
	sarl	$31, %esi
	sarq	$33, %rdx
	subl	%esi, %edx
	leal	(%rdx,%rdx,4), %esi
	movl	%r10d, %edx
	subl	%esi, %edx
	movl	%edx, 912(%rbx)
	cmpl	908(%rbx), %edx
	jne	.L65
	addl	$1, %edx
	movslq	%edx, %rsi
	movl	%edx, %edi
	imulq	$1717986919, %rsi, %rsi
	sarl	$31, %edi
	sarq	$33, %rsi
	subl	%edi, %esi
	leal	(%rsi,%rsi,4), %esi
	subl	%esi, %edx
	movl	%edx, 912(%rbx)
	jmp	.L65
.L73:
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
	xorl	%eax, %eax
	leaq	.LC1(%rip), %rsi
	movl	$1, %edi
	call	__printf_chk@PLT
	cmpl	$1, 92(%rbx)
	jne	.L75
	.p2align 4,,10
	.p2align 3
.L76:
	movq	%rbx, %rdi
	call	threadwork@PLT
	cmpl	$1, 92(%rbx)
	je	.L76
.L75:
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
	jmp	.L83
	.p2align 4,,10
	.p2align 3
.L81:
	addq	$1, 72(%rdi)
.L83:
	cmpl	$1, 92(%rdi)
	je	.L81
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
	.string	"finished simulation."
.LC17:
	.string	"%ld reads\n"
.LC18:
	.string	"freq: %ld\n"
.LC19:
	.string	"freq_ps: %ld\n"
.LC20:
	.string	"freq latency2: %ld\n"
.LC21:
	.string	"freq per thread latency: %ld\n"
.LC22:
	.string	"freq latency: %ld\n"
.LC23:
	.string	"%ld writes\n"
.LC24:
	.string	"freq_writes: %ld\n"
.LC25:
	.string	"freq_writes_total: %ld\n"
.LC26:
	.string	"freq_writes latency2: %ld\n"
	.section	.rodata.str1.8
	.align 8
.LC27:
	.string	"freq_writes per thread latency: %ld\n"
	.section	.rodata.str1.1
.LC28:
	.string	"freq_writes latency: %ld\n"
.LC29:
	.string	"writer speed"
.LC30:
	.string	"%ld\n"
.LC31:
	.string	"sw %ld\n"
.LC32:
	.string	"samples%d"
.LC33:
	.string	"w"
.LC34:
	.string	"%ld%ld %d %ld %d %d\n"
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
	leaq	.LC3(%rip), %rsi
	movl	$1, %edi
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	leaq	.LC10(%rip), %r15
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
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
	subq	$104, %rsp
	.cfi_def_cfa_offset 160
	movq	%fs:40, %rax
	movq	%rax, 88(%rsp)
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
	movl	$12, %edx
	leaq	.LC6(%rip), %rsi
	xorl	%eax, %eax
	movl	$1, %edi
	call	__printf_chk@PLT
	movl	$8, %esi
	movl	$12, %edi
	call	calloc@PLT
	movl	$56, %esi
	movl	$12, %edi
	movq	%rax, 16(%rsp)
	call	calloc@PLT
	movl	$12288, %esi
	movl	$1, %edi
	movq	%rax, 24(%rsp)
	call	calloc@PLT
	movl	$1, %esi
	movq	%r12, %rdi
	movq	%rax, %rbx
	call	calloc@PLT
	movq	%r12, %rdx
	movl	$-1, %esi
	movq	%rax, %rdi
	movq	%rax, %r14
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
	movq	%rax, 8(%rsp)
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC9(%rip), %rsi
	call	__printf_chk@PLT
	movl	$4, %esi
	movl	$12, %edi
	call	calloc@PLT
	leaq	40(%rsp), %rdi
	movl	$512, %edx
	movl	$128, %esi
	movq	%rax, %rbp
	call	posix_memalign@PLT
	movq	%r14, 112(%rbx)
	movq	%rbx, %r14
	testl	%eax, %eax
	movl	$0, %eax
	cmove	40(%rsp), %rax
	xorl	%r13d, %r13d
	movq	%rax, (%rsp)
	.p2align 4,,10
	.p2align 3
.L86:
	movl	$128, %esi
	movl	$1, %edi
	addq	$1024, %r14
	call	calloc@PLT
	leal	1(%r13), %ecx
	movl	$1, %esi
	movl	%r13d, %edx
	salq	%cl, %rsi
	movq	%rax, -904(%r14)
	movl	$1, %edi
	orq	%rsi, (%rax)
	movq	%r15, %rsi
	xorl	%eax, %eax
	call	__printf_chk@PLT
	imull	$357913941, %r13d, %eax
	movl	%r13d, -924(%r14)
	movdqa	.LC12(%rip), %xmm1
	movl	$0, -896(%r14)
	movdqa	.LC13(%rip), %xmm2
	movl	$48, %esi
	movl	$10000000, %edi
	movq	%rbp, -992(%r14)
	movdqa	.LC14(%rip), %xmm3
	movl	%eax, -872(%r14)
	movq	(%rsp), %rax
	movl	$357913941, -876(%r14)
	movq	%rax, -128(%r14)
	movq	.LC11(%rip), %rax
	movl	$12, -920(%r14)
	movq	%rax, -932(%r14)
	movq	8(%rsp), %rax
	movl	$0, 0(%rbp,%r13,4)
	movq	%rax, -864(%r14)
	leal	(%r13,%r13), %eax
	addq	$1, %r13
	sarl	$2, %eax
	movq	%rbx, -984(%r14)
	addl	$1, %eax
	movl	$357913941, -880(%r14)
	movq	%rbx, -976(%r14)
	movl	$11, -512(%r14)
	movl	$11, -640(%r14)
	movl	$0, -824(%r14)
	movl	%eax, -116(%r14)
	movl	$12, -216(%r14)
	movaps	%xmm1, -1024(%r14)
	movups	%xmm2, -840(%r14)
	movups	%xmm3, -248(%r14)
	call	calloc@PLT
	movl	$48, %esi
	movl	$10000, %edi
	movl	$10000000, -224(%r14)
	movq	%rax, -232(%r14)
	call	calloc@PLT
	movq	%rax, -208(%r14)
	cmpq	$12, %r13
	jne	.L86
	movq	24(%rsp), %rbp
	movq	16(%rsp), %r15
	movq	%rbx, %r14
	movq	work@GOTPCREL(%rip), %r13
	leaq	672(%rbp), %rax
	movq	%r15, %r12
	movq	%rax, (%rsp)
	.p2align 4,,10
	.p2align 3
.L87:
	movq	%r14, %rcx
	movq	%rbp, %rsi
	movq	%r15, %rdi
	movq	%r13, %rdx
	call	pthread_create@PLT
	movq	120(%r14), %rdx
	movq	(%r15), %rdi
	movl	$8, %esi
	addq	$8, %r15
	addq	$56, %rbp
	addq	$1024, %r14
	call	pthread_setaffinity_np@PLT
	cmpq	(%rsp), %rbp
	jne	.L87
	movdqa	.LC15(%rip), %xmm0
	leaq	64(%rsp), %rsi
	leaq	48(%rsp), %rdi
	leaq	32(%rsp), %r13
	movaps	%xmm0, 48(%rsp)
	pxor	%xmm0, %xmm0
	movaps	%xmm0, 64(%rsp)
	call	nanosleep@PLT
	movq	16(%rsp), %rbp
	movl	$0, 92(%rbx)
	movl	$0, 1116(%rbx)
	movl	$0, 2140(%rbx)
	addq	$96, %rbp
	movl	$0, 3164(%rbx)
	movl	$0, 4188(%rbx)
	movl	$0, 5212(%rbx)
	movl	$0, 6236(%rbx)
	movl	$0, 7260(%rbx)
	movl	$0, 8284(%rbx)
	movl	$0, 9308(%rbx)
	movl	$0, 10332(%rbx)
	movl	$0, 11356(%rbx)
	.p2align 4,,10
	.p2align 3
.L88:
	movq	(%r12), %rdi
	movq	%r13, %rsi
	addq	$8, %r12
	call	pthread_join@PLT
	cmpq	%r12, %rbp
	jne	.L88
	leaq	.LC16(%rip), %rdi
	leaq	72(%rbx), %rbp
	xorl	%r12d, %r12d
	call	puts@PLT
	leaq	12360(%rbx), %r14
	leaq	.LC17(%rip), %r13
	.p2align 4,,10
	.p2align 3
.L89:
	movq	0(%rbp), %rdx
	movq	%r13, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	addq	$1024, %rbp
	call	__printf_chk@PLT
	addq	-1024(%rbp), %r12
	cmpq	%rbp, %r14
	jne	.L89
	movq	%r12, %rdx
	leaq	.LC18(%rip), %rsi
	leaq	80(%rbx), %rbp
	xorl	%eax, %eax
	movl	$1, %edi
	leaq	12368(%rbx), %r14
	leaq	.LC23(%rip), %r13
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC19(%rip), %rsi
	call	__printf_chk@PLT
	movl	$1000000000, %eax
	movl	$1, %edi
	leaq	.LC20(%rip), %rsi
	cqto
	idivq	%r12
	movq	%rax, %r12
	movq	%rax, %rdx
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC21(%rip), %rsi
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC22(%rip), %rsi
	xorl	%r12d, %r12d
	call	__printf_chk@PLT
	.p2align 4,,10
	.p2align 3
.L90:
	movq	0(%rbp), %rdx
	movq	%r13, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	addq	$1024, %rbp
	addq	%rdx, %r12
	call	__printf_chk@PLT
	cmpq	%r14, %rbp
	jne	.L90
	movq	%r12, %rdx
	leaq	.LC24(%rip), %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC25(%rip), %rsi
	leaq	.LC30(%rip), %rbp
	call	__printf_chk@PLT
	movl	$1000000000, %eax
	leaq	.LC26(%rip), %rsi
	movl	$1, %edi
	cqto
	leaq	800(%rbx), %r14
	idivq	%r12
	movq	%rax, %r12
	movq	%rax, %rdx
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC27(%rip), %rsi
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC28(%rip), %rsi
	call	__printf_chk@PLT
	leaq	.LC29(%rip), %rdi
	call	puts@PLT
	movq	%rbp, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	240(%rbx), %rdx
	subq	224(%rbx), %rdx
	call	__printf_chk@PLT
	movq	%rbp, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	256(%rbx), %rdx
	subq	224(%rbx), %rdx
	call	__printf_chk@PLT
	movq	%rbp, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	240(%rbx), %rdx
	subq	256(%rbx), %rdx
	call	__printf_chk@PLT
	movq	%rbp, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	288(%rbx), %rdx
	subq	272(%rbx), %rdx
	call	__printf_chk@PLT
	movq	%rbp, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	272(%rbx), %rdx
	subq	288(%rbx), %rdx
	call	__printf_chk@PLT
	movq	%rbp, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	movq	272(%rbx), %rdx
	subq	256(%rbx), %rdx
	call	__printf_chk@PLT
	movq	320(%rbx), %rdx
	movl	$1, %edi
	subq	304(%rbx), %rdx
	leaq	.LC31(%rip), %rsi
	xorl	%eax, %eax
	addq	$13088, %rbx
	xorl	%r13d, %r13d
	call	__printf_chk@PLT
	movl	$1, %esi
	movl	$100, %edi
	call	calloc@PLT
	movl	$1, %esi
	movl	$1000, %edi
	movq	%rax, %r12
	call	calloc@PLT
	movl	-12984(%rbx), %r9d
	movq	%r12, %rdi
	leaq	.LC32(%rip), %r8
	movl	$100, %ecx
	movl	$1, %edx
	movl	$100, %esi
	movq	%rax, %rbp
	xorl	%eax, %eax
	call	__snprintf_chk@PLT
	movq	%r12, %rdi
	leaq	.LC33(%rip), %rsi
	call	fopen@PLT
	movq	%rax, %r12
	.p2align 4,,10
	.p2align 3
.L91:
	movl	(%r14), %ecx
	xorl	%r15d, %r15d
	testl	%ecx, %ecx
	jle	.L94
.L106:
	movq	-8(%r14), %rsi
.L95:
	movslq	%r15d, %rax
	leaq	(%rax,%rax,2), %rdx
	salq	$4, %rdx
	addq	%rsi, %rdx
	cmpl	$1, 36(%rdx)
	je	.L108
	addl	$1, %r15d
	cmpl	%ecx, %r15d
	jl	.L95
.L94:
	addq	$1024, %r14
	cmpq	%rbx, %r14
	jne	.L91
.L96:
	movq	88(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L109
	addq	$104, %rsp
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
.L108:
	.cfi_restore_state
	movq	%r13, %rax
	movl	$125, %ecx
	movq	%rbp, %rdi
	subq	$8, %rsp
	.cfi_def_cfa_offset 168
	rep stosq
	movl	$100, %esi
	movq	%rbp, %rdi
	addl	$1, %r15d
	movl	$1000, %ecx
	leaq	.LC34(%rip), %r8
	movl	40(%rdx), %eax
	movq	8(%rdx), %r9
	pushq	%rax
	.cfi_def_cfa_offset 176
	movl	(%rdx), %eax
	pushq	%rax
	.cfi_def_cfa_offset 184
	movl	32(%rdx), %eax
	pushq	24(%rdx)
	.cfi_def_cfa_offset 192
	pushq	%rax
	.cfi_def_cfa_offset 200
	xorl	%eax, %eax
	pushq	16(%rdx)
	.cfi_def_cfa_offset 208
	movl	$1, %edx
	call	__snprintf_chk@PLT
	addq	$48, %rsp
	.cfi_def_cfa_offset 160
	movq	%r12, %rsi
	movq	%rbp, %rdi
	call	fputs@PLT
	movl	(%r14), %ecx
	cmpl	%ecx, %r15d
	jl	.L106
	addq	$1024, %r14
	cmpq	%rbx, %r14
	jne	.L91
	jmp	.L96
.L109:
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
	.long	1
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
	.quad	12
	.quad	12
	.align 16
.LC15:
	.quad	1
	.quad	0
	.ident	"GCC: (GNU) 11.3.0"
	.section	.note.GNU-stack,"",@progbits
