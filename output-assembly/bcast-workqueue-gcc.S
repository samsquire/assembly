	.file	"bcast-workqueue.c"
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
	movq	928(%rax), %rbx
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
	movslq	100(%rdi), %rax
	leaq	0(,%rax,8), %rbp
	subq	%rax, %rbp
	salq	$7, %rbp
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
	movq	%rbp, %rdi
	leaq	12(%rsp), %rcx
	leaq	16(%rsp), %r8
	movq	%r12, %rdx
	movq	%r13, %rsi
	call	pollthreads@PLT
	movslq	12(%rsp), %rdi
	testl	%edi, %edi
	jle	.L50
	movl	20(%rsp), %r8d
	xorl	%ecx, %ecx
	jmp	.L39
	.p2align 4,,10
	.p2align 3
.L58:
	movq	(%rbx,%rcx,8), %rdx
	movslq	0(%r13,%rcx,4), %r10
	leal	1(%rcx), %esi
	addq	$1, %rcx
	salq	$5, %rdx
	addq	160(%rbp), %rdx
	leaq	0(,%r10,8), %rax
	movd	(%rdx), %xmm0
	movd	8(%rdx), %xmm1
	subq	%r10, %rax
	movl	$2, 16(%rdx)
	salq	$7, %rax
	addq	48(%rbp), %rax
	punpckldq	%xmm1, %xmm0
	movq	%rdx, 168(%rax)
	movl	%r10d, 20(%rdx)
	orl	$16, 200(%rax)
	movq	%xmm0, 20(%rax)
	cmpq	%rcx, %rdi
	je	.L38
.L39:
	movl	%ecx, %esi
	cmpq	%r8, %rcx
	jne	.L58
.L38:
	movl	16(%rsp), %r8d
	testl	%r8d, %r8d
	jle	.L43
	movl	20(%rsp), %edi
	addl	%esi, %r8d
	jmp	.L45
	.p2align 4,,10
	.p2align 3
.L56:
	leal	1(%rsi), %ecx
	movslq	%esi, %rsi
	movl	(%r12), %r9d
	addq	$4, %r12
	movq	(%rbx,%rsi,8), %rdx
	movslq	%r9d, %rsi
	salq	$5, %rdx
	addq	160(%rbp), %rdx
	leaq	0(,%rsi,8), %rax
	movd	(%rdx), %xmm0
	movd	8(%rdx), %xmm2
	subq	%rsi, %rax
	movl	$3, 16(%rdx)
	salq	$7, %rax
	addq	48(%rbp), %rax
	punpckldq	%xmm2, %xmm0
	movq	%rdx, 176(%rax)
	movl	%r9d, 20(%rdx)
	orl	$32, 200(%rax)
	movq	%xmm0, 64(%rax)
	cmpl	%r8d, %ecx
	je	.L43
	movl	%ecx, %esi
.L45:
	cmpl	%esi, %edi
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
	leaq	0(,%rcx,8), %rax
	subq	%rcx, %rax
	salq	$7, %rax
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
	movq	40(%rdi), %r9
	movq	%rdi, %rcx
	movslq	104(%rcx), %rsi
	movl	100(%rcx), %r8d
	movq	848(%r9), %rdi
	addq	$1, 80(%rcx)
	movq	%rdi, %rax
	cqto
	idivq	%rsi
	movabsq	$-9187201950435737471, %rdx
	movq	%rax, %rsi
	imulq	%rdx
	movq	%rsi, %rax
	sarq	$63, %rax
	addq	%rsi, %rdx
	sarq	$7, %rdx
	subq	%rax, %rdx
	movq	%rdx, %rax
	salq	$8, %rax
	subq	%rdx, %rax
	subq	%rax, %rsi
	movslq	%r8d, %rax
	salq	$16, %rsi
	orq	%rax, %rsi
	movq	112(%r9), %rax
	movb	%r8b, (%rax,%rsi)
	movq	40(%rcx), %rax
	lock addq	$1, 848(%rax)
	movq	40(%rcx), %rax
	movslq	104(%rcx), %r8
	movq	840(%rcx), %rsi
	movq	848(%rax), %rax
	cqto
	idivq	%r8
	movl	%eax, 856(%rcx)
	cmpq	%rdi, %rsi
	jge	.L62
	movl	512(%rcx), %eax
	addq	$1, 72(%rcx)
	addl	$1, %eax
	cltd
	idivl	%r8d
	movl	%edx, 512(%rcx)
	cmpl	100(%rcx), %edx
	je	.L65
.L63:
	leaq	1(%rsi), %rax
	cqto
	movq	%rax, 840(%rcx)
	idivq	%r8
	testq	%rdx, %rdx
	jne	.L62
	movl	$0, 512(%rcx)
.L62:
	ret
	.p2align 4,,10
	.p2align 3
.L65:
	addl	$1, %edx
	movl	%edx, 512(%rcx)
	jmp	.L63
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
	jne	.L67
	.p2align 4,,10
	.p2align 3
.L68:
	movq	%rbx, %rdi
	call	threadwork@PLT
	cmpl	$1, 92(%rbx)
	je	.L68
.L67:
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
	jmp	.L75
	.p2align 4,,10
	.p2align 3
.L73:
	addq	$1, 72(%rdi)
.L75:
	cmpl	$1, 92(%rdi)
	je	.L73
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
	movl	$6, %edx
	leaq	.LC6(%rip), %rsi
	xorl	%eax, %eax
	movl	$1, %edi
	call	__printf_chk@PLT
	movl	$8, %esi
	movl	$6, %edi
	call	calloc@PLT
	movl	$56, %esi
	movl	$6, %edi
	movq	%rax, 16(%rsp)
	call	calloc@PLT
	movl	$5376, %esi
	movl	$1, %edi
	movq	%rax, 24(%rsp)
	call	calloc@PLT
	movl	$1, %esi
	movq	%r12, %rdi
	movq	%rax, %rbx
	call	calloc@PLT
	movq	%r12, %rdx
	movl	$-1, %esi
	movq	%rbx, %r15
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
	movq	%rax, 8(%rsp)
	xorl	%eax, %eax
	call	__printf_chk@PLT
	movq	%r12, %rdx
	movl	$1, %edi
	xorl	%eax, %eax
	leaq	.LC9(%rip), %rsi
	call	__printf_chk@PLT
	movl	$4, %esi
	movl	$6, %edi
	call	calloc@PLT
	movq	%rbp, 112(%rbx)
	xorl	%ebp, %ebp
	movq	%rax, %r13
	.p2align 4,,10
	.p2align 3
.L77:
	movl	$128, %esi
	movl	$1, %edi
	movl	%r14d, (%rsp)
	leal	-1(%r14), %r12d
	call	calloc@PLT
	movl	%r14d, %ecx
	movl	$1, %edx
	leaq	.LC10(%rip), %rsi
	movq	%rax, 120(%r15)
	salq	%cl, %rdx
	movl	(%rsp), %ecx
	movl	$1, %edi
	orq	%rdx, (%rax)
	movl	%r12d, %edx
	xorl	%eax, %eax
	addq	$896, %r15
	call	__printf_chk@PLT
	movq	.LC11(%rip), %rax
	movl	%ebp, -744(%r15)
	movl	$48, %esi
	movdqa	.LC12(%rip), %xmm1
	movl	$10000000, %edi
	movdqa	.LC13(%rip), %xmm2
	movl	$0, -768(%r15)
	movq	%rax, -804(%r15)
	movq	8(%rsp), %rax
	addl	$715827882, %ebp
	movdqa	.LC14(%rip), %xmm3
	movl	%r12d, -796(%r15)
	movl	$715827882, -748(%r15)
	movl	$6, -792(%r15)
	movq	%r13, -864(%r15)
	movl	$0, -4(%r13,%r14,4)
	addq	$1, %r14
	movl	$715827882, -752(%r15)
	movq	%rbx, -856(%r15)
	movq	%rbx, -848(%r15)
	movl	$5, -384(%r15)
	movl	$5, -512(%r15)
	movq	%rax, -736(%r15)
	movl	$0, -696(%r15)
	movl	$6, -88(%r15)
	movaps	%xmm1, -896(%r15)
	movups	%xmm2, -712(%r15)
	movups	%xmm3, -120(%r15)
	call	calloc@PLT
	movl	$48, %esi
	movl	$10000, %edi
	movl	$10000000, -96(%r15)
	movq	%rax, -104(%r15)
	call	calloc@PLT
	movq	%rax, -80(%r15)
	cmpq	$7, %r14
	jne	.L77
	movq	24(%rsp), %rbp
	movq	16(%rsp), %rax
	movq	%rbx, (%rsp)
	movq	%rbx, %r14
	movq	work@GOTPCREL(%rip), %r13
	leaq	336(%rbp), %rcx
	movq	%rax, %r12
	movq	%rax, %rbx
	movq	%rcx, %r15
	.p2align 4,,10
	.p2align 3
.L78:
	movq	%r14, %rcx
	movq	%rbp, %rsi
	movq	%rbx, %rdi
	movq	%r13, %rdx
	call	pthread_create@PLT
	movq	120(%r14), %rdx
	movq	(%rbx), %rdi
	movl	$8, %esi
	addq	$56, %rbp
	addq	$8, %rbx
	addq	$896, %r14
	call	pthread_setaffinity_np@PLT
	cmpq	%rbp, %r15
	jne	.L78
	movq	(%rsp), %rbx
	leaq	64(%rsp), %rsi
	leaq	48(%rsp), %rdi
	movdqa	.LC15(%rip), %xmm0
	leaq	40(%rsp), %r13
	movaps	%xmm0, 48(%rsp)
	pxor	%xmm0, %xmm0
	movaps	%xmm0, 64(%rsp)
	call	nanosleep@PLT
	movq	16(%rsp), %rbp
	movl	$0, 92(%rbx)
	movl	$0, 988(%rbx)
	movl	$0, 1884(%rbx)
	addq	$48, %rbp
	movl	$0, 2780(%rbx)
	movl	$0, 3676(%rbx)
	movl	$0, 4572(%rbx)
	.p2align 4,,10
	.p2align 3
.L79:
	movq	(%r12), %rdi
	movq	%r13, %rsi
	addq	$8, %r12
	call	pthread_join@PLT
	cmpq	%rbp, %r12
	jne	.L79
	leaq	.LC16(%rip), %rdi
	leaq	72(%rbx), %rbp
	xorl	%r12d, %r12d
	call	puts@PLT
	leaq	5448(%rbx), %r14
	leaq	.LC17(%rip), %r13
	.p2align 4,,10
	.p2align 3
.L80:
	movq	0(%rbp), %rdx
	movq	%r13, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	addq	$896, %rbp
	call	__printf_chk@PLT
	addq	-896(%rbp), %r12
	cmpq	%r14, %rbp
	jne	.L80
	movq	%r12, %rdx
	leaq	.LC18(%rip), %rsi
	leaq	80(%rbx), %rbp
	xorl	%eax, %eax
	movl	$1, %edi
	leaq	5456(%rbx), %r14
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
.L81:
	movq	0(%rbp), %rdx
	movq	%r13, %rsi
	movl	$1, %edi
	xorl	%eax, %eax
	addq	$896, %rbp
	addq	%rdx, %r12
	call	__printf_chk@PLT
	cmpq	%rbp, %r14
	jne	.L81
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
	movl	$1, %edi
	leaq	.LC26(%rip), %rsi
	cqto
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
	call	__printf_chk@PLT
	movq	88(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L89
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
.L89:
	.cfi_restore_state
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
	.quad	6
	.quad	6
	.align 16
.LC15:
	.quad	1
	.quad	0
	.ident	"GCC: (GNU) 11.3.0"
	.section	.note.GNU-stack,"",@progbits
