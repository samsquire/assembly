	.file	"stream2-workqueue.c"
	.text
	.globl	yield
	.type	yield, @function
yield:
.LFB6:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	nop
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE6:
	.size	yield, .-yield
	.section	.rodata
.LC0:
	.string	"%p %p %p coro\n"
.LC1:
	.string	"%ld\n"
	.text
	.globl	coroutine_func
	.type	coroutine_func, @function
coroutine_func:
.LFB7:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
#APP
# 72 "stream2-workqueue.c" 1
	movq %rdi, %rax
# 0 "" 2
#NO_APP
	movq	%rax, -24(%rbp)
#APP
# 73 "stream2-workqueue.c" 1
	movq %rsi, %rax
# 0 "" 2
#NO_APP
	movq	%rax, -16(%rbp)
#APP
# 74 "stream2-workqueue.c" 1
	movq %rdx, %rax
# 0 "" 2
#NO_APP
	movq	%rax, -8(%rbp)
	movq	-8(%rbp), %rcx
	movq	-16(%rbp), %rdx
	movq	-24(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC0(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movq	-16(%rbp), %rax
	movq	16(%rax), %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
#APP
# 80 "stream2-workqueue.c" 1
	lea 0(%rip), %r11
movq %r11, %rdx
# 0 "" 2
#NO_APP
	movq	-16(%rbp), %rax
	movq	%rdx, 16(%rax)
	movq	-24(%rbp), %rax
	movq	(%rax), %rax
	movl	%eax, -28(%rbp)
	movq	-24(%rbp), %rax
	movq	(%rax), %rax
#APP
# 85 "stream2-workqueue.c" 1
	movq %rax, %rsp
# 0 "" 2
#NO_APP
	movl	$0, %eax
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE7:
	.size	coroutine_func, .-coroutine_func
	.globl	pollthreads
	.type	pollthreads, @function
pollthreads:
.LFB8:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -40(%rbp)
	movq	%rsi, -48(%rbp)
	movq	%rdx, -56(%rbp)
	movq	%rcx, -64(%rbp)
	movq	%r8, -72(%rbp)
	movq	$4, -16(%rbp)
	movq	$8, -8(%rbp)
	movl	$1, -24(%rbp)
	jmp	.L5
.L10:
	movq	-40(%rbp), %rax
	movq	48(%rax), %rax
	addq	$1024, %rax
	movq	32(%rax), %rdx
	movl	-24(%rbp), %eax
	cltq
	salq	$2, %rax
	addq	%rdx, %rax
	movl	(%rax), %eax
	movl	%eax, -20(%rbp)
	movl	-20(%rbp), %eax
	cltq
	andq	-16(%rbp), %rax
	cmpq	%rax, -16(%rbp)
	je	.L6
	cmpl	$0, -20(%rbp)
	jne	.L7
.L6:
	movq	-72(%rbp), %rax
	movl	(%rax), %eax
	leal	1(%rax), %ecx
	movq	-72(%rbp), %rdx
	movl	%ecx, (%rdx)
	cltq
	leaq	0(,%rax,4), %rdx
	movq	-56(%rbp), %rax
	addq	%rax, %rdx
	movl	-24(%rbp), %eax
	movl	%eax, (%rdx)
.L7:
	movl	-20(%rbp), %eax
	cltq
	andq	-8(%rbp), %rax
	cmpq	%rax, -8(%rbp)
	je	.L8
	cmpl	$0, -20(%rbp)
	jne	.L9
.L8:
	movq	-64(%rbp), %rax
	movl	(%rax), %eax
	leal	1(%rax), %ecx
	movq	-64(%rbp), %rdx
	movl	%ecx, (%rdx)
	cltq
	leaq	0(,%rax,4), %rdx
	movq	-48(%rbp), %rax
	addq	%rax, %rdx
	movl	-24(%rbp), %eax
	movl	%eax, (%rdx)
.L9:
	addl	$1, -24(%rbp)
.L5:
	movq	-40(%rbp), %rax
	movl	104(%rax), %eax
	cmpl	%eax, -24(%rbp)
	jl	.L10
	movl	$0, %eax
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE8:
	.size	pollthreads, .-pollthreads
	.globl	findavailable
	.type	findavailable, @function
findavailable:
.LFB9:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -24(%rbp)
	movq	%rsi, -32(%rbp)
	movq	%rdx, -40(%rbp)
	movq	%rcx, -48(%rbp)
	movq	%r8, -56(%rbp)
	movl	$0, -4(%rbp)
	jmp	.L13
.L16:
	movq	-24(%rbp), %rax
	movq	160(%rax), %rdx
	movl	-4(%rbp), %eax
	cltq
	salq	$5, %rax
	addq	%rdx, %rax
	movl	16(%rax), %eax
	cmpl	$1, %eax
	jne	.L14
	movq	-40(%rbp), %rax
	movl	(%rax), %eax
	cltq
	leaq	0(,%rax,8), %rdx
	movq	-32(%rbp), %rax
	addq	%rax, %rdx
	movl	-4(%rbp), %eax
	cltq
	movq	%rax, (%rdx)
	movq	-40(%rbp), %rax
	movl	(%rax), %eax
	leal	1(%rax), %edx
	movq	-40(%rbp), %rax
	movl	%edx, (%rax)
	movq	-40(%rbp), %rax
	movl	(%rax), %edx
	movq	-24(%rbp), %rax
	movl	104(%rax), %eax
	addl	%eax, %eax
	cmpl	%eax, %edx
	je	.L19
.L14:
	addl	$1, -4(%rbp)
.L13:
	movl	-4(%rbp), %eax
	movslq	%eax, %rdx
	movq	-24(%rbp), %rax
	movq	184(%rax), %rax
	addq	$1, %rax
	cmpq	%rax, %rdx
	jl	.L16
	jmp	.L15
.L19:
	nop
.L15:
	movq	-40(%rbp), %rax
	movl	(%rax), %eax
	testl	%eax, %eax
	jne	.L17
	movl	$1, %eax
	jmp	.L18
.L17:
	movl	$0, %eax
.L18:
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE9:
	.size	findavailable, .-findavailable
	.globl	singlewriter3
	.type	singlewriter3, @function
singlewriter3:
.LFB10:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -24(%rbp)
	movq	%rsi, -32(%rbp)
	movq	%rdx, -40(%rbp)
	movq	%rcx, -48(%rbp)
	movl	$0, -4(%rbp)
	movq	-24(%rbp), %rax
	movl	384(%rax), %eax
	testl	%eax, %eax
	nop
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE10:
	.size	singlewriter3, .-singlewriter3
	.globl	singlewriter2
	.type	singlewriter2, @function
singlewriter2:
.LFB11:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$64, %rsp
	movq	%rdi, -40(%rbp)
	movq	%rsi, -48(%rbp)
	movq	%rdx, -56(%rbp)
	movq	%rcx, -64(%rbp)
	movl	$0, -20(%rbp)
	movq	-40(%rbp), %rax
	movl	512(%rax), %eax
	testl	%eax, %eax
	je	.L23
	movq	-40(%rbp), %rax
	movl	512(%rax), %eax
	movq	-40(%rbp), %rdx
	movl	104(%rdx), %edx
	leal	-1(%rdx), %ecx
	cltd
	idivl	%ecx
	movl	%edx, %eax
	testl	%eax, %eax
	jne	.L23
	movq	-40(%rbp), %rax
	movq	48(%rax), %rdx
	movq	-40(%rbp), %rax
	movl	100(%rax), %eax
	cltq
	salq	$10, %rax
	addq	%rdx, %rax
	movq	%rax, -16(%rbp)
	movq	-16(%rbp), %rax
	movq	792(%rax), %rcx
	movq	-16(%rbp), %rax
	movl	804(%rax), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$4, %rax
	addq	%rcx, %rax
	movq	%rax, -8(%rbp)
	movq	-8(%rbp), %rax
	addq	$8, %rax
	movq	%rax, %rsi
	movl	$4, %edi
	call	clock_gettime@PLT
	movq	-16(%rbp), %rax
	movl	804(%rax), %eax
	leal	1(%rax), %edx
	movq	-16(%rbp), %rax
	movl	800(%rax), %ecx
	movl	%edx, %eax
	cltd
	idivl	%ecx
	movq	-16(%rbp), %rax
	movl	%edx, 804(%rax)
	movq	-8(%rbp), %rax
	movl	$1, 32(%rax)
	movq	-40(%rbp), %rax
	movl	100(%rax), %edx
	movq	-8(%rbp), %rax
	movl	%edx, (%rax)
	movq	-8(%rbp), %rax
	movl	$1, 36(%rax)
.L23:
	nop
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE11:
	.size	singlewriter2, .-singlewriter2
	.globl	singlewriter
	.type	singlewriter, @function
singlewriter:
.LFB12:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$112, %rsp
	movq	%rdi, -88(%rbp)
	movq	%rsi, -96(%rbp)
	movq	%rdx, -104(%rbp)
	movq	%rcx, -112(%rbp)
	movq	%fs:40, %rax
	movq	%rax, -8(%rbp)
	xorl	%eax, %eax
	movq	-88(%rbp), %rax
	movq	48(%rax), %rax
	movl	524(%rax), %eax
	leal	1(%rax), %edx
	movq	-88(%rbp), %rax
	movl	104(%rax), %esi
	movq	-88(%rbp), %rax
	movq	48(%rax), %rcx
	movl	%edx, %eax
	cltd
	idivl	%esi
	movl	%edx, %eax
	movl	%eax, 524(%rcx)
	movl	$0, -80(%rbp)
	movl	$0, -76(%rbp)
	movl	$0, -72(%rbp)
	movq	-112(%rbp), %rdi
	movq	-104(%rbp), %rcx
	leaq	-72(%rbp), %rdx
	movq	-96(%rbp), %rsi
	movq	-88(%rbp), %rax
	movq	%rdi, %r8
	movq	%rax, %rdi
	call	findavailable@PLT
	movl	%eax, -52(%rbp)
	cmpl	$1, -52(%rbp)
	jne	.L25
	movl	$1, %eax
	jmp	.L38
.L25:
	leaq	-76(%rbp), %rdi
	leaq	-80(%rbp), %rcx
	movq	-112(%rbp), %rdx
	movq	-104(%rbp), %rsi
	movq	-88(%rbp), %rax
	movq	%rdi, %r8
	movq	%rax, %rdi
	call	pollthreads@PLT
	movl	$0, -68(%rbp)
	movl	$0, -64(%rbp)
	jmp	.L27
.L30:
	movl	-72(%rbp), %eax
	cmpl	%eax, -68(%rbp)
	je	.L40
	movl	-64(%rbp), %eax
	cltq
	leaq	0(,%rax,4), %rdx
	movq	-104(%rbp), %rax
	addq	%rdx, %rax
	movl	(%rax), %eax
	movl	%eax, -48(%rbp)
	movq	-88(%rbp), %rax
	movq	160(%rax), %rcx
	movl	-68(%rbp), %eax
	leal	1(%rax), %edx
	movl	%edx, -68(%rbp)
	cltq
	leaq	0(,%rax,8), %rdx
	movq	-96(%rbp), %rax
	addq	%rdx, %rax
	movq	(%rax), %rax
	salq	$5, %rax
	addq	%rcx, %rax
	movq	%rax, -24(%rbp)
	movq	-24(%rbp), %rax
	movl	$2, 16(%rax)
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	movl	-48(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rax, %rdx
	movq	-24(%rbp), %rax
	movq	%rax, 168(%rdx)
	movq	-24(%rbp), %rax
	movl	-48(%rbp), %edx
	movl	%edx, 20(%rax)
	movq	-24(%rbp), %rax
	movq	(%rax), %rax
	movl	%eax, -44(%rbp)
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	movl	-48(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rax, %rdx
	movl	-44(%rbp), %eax
	movl	%eax, 20(%rdx)
	movq	-24(%rbp), %rax
	movq	8(%rax), %rax
	movl	%eax, -40(%rbp)
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	movl	-48(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rax, %rdx
	movl	-40(%rbp), %eax
	movl	%eax, 24(%rdx)
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	movl	-48(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rdx, %rax
	movl	200(%rax), %edx
	movq	-88(%rbp), %rax
	movq	48(%rax), %rcx
	movl	-48(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rcx, %rax
	orl	$16, %edx
	movl	%edx, 200(%rax)
	addl	$1, -64(%rbp)
.L27:
	movl	-80(%rbp), %eax
	cmpl	%eax, -64(%rbp)
	jl	.L30
	jmp	.L29
.L40:
	nop
.L29:
	movl	$0, -60(%rbp)
	jmp	.L31
.L34:
	movl	-72(%rbp), %eax
	cmpl	%eax, -68(%rbp)
	je	.L41
	movl	-60(%rbp), %eax
	cltq
	leaq	0(,%rax,4), %rdx
	movq	-112(%rbp), %rax
	addq	%rdx, %rax
	movl	(%rax), %eax
	movl	%eax, -36(%rbp)
	movq	-88(%rbp), %rax
	movq	160(%rax), %rcx
	movl	-68(%rbp), %eax
	leal	1(%rax), %edx
	movl	%edx, -68(%rbp)
	cltq
	leaq	0(,%rax,8), %rdx
	movq	-96(%rbp), %rax
	addq	%rdx, %rax
	movq	(%rax), %rax
	salq	$5, %rax
	addq	%rcx, %rax
	movq	%rax, -16(%rbp)
	movq	-16(%rbp), %rax
	movl	$3, 16(%rax)
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	movl	-36(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rax, %rdx
	movq	-16(%rbp), %rax
	movq	%rax, 176(%rdx)
	movq	-16(%rbp), %rax
	movl	-36(%rbp), %edx
	movl	%edx, 20(%rax)
	movq	-16(%rbp), %rax
	movq	(%rax), %rax
	movl	%eax, -32(%rbp)
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	movl	-36(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rax, %rdx
	movl	-32(%rbp), %eax
	movl	%eax, 64(%rdx)
	movq	-16(%rbp), %rax
	movq	8(%rax), %rax
	movl	%eax, -28(%rbp)
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	movl	-36(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rax, %rdx
	movl	-28(%rbp), %eax
	movl	%eax, 68(%rdx)
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	movl	-36(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rdx, %rax
	movl	200(%rax), %edx
	movq	-88(%rbp), %rax
	movq	48(%rax), %rcx
	movl	-36(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rcx, %rax
	orl	$32, %edx
	movl	%edx, 200(%rax)
	addl	$1, -60(%rbp)
.L31:
	movl	-76(%rbp), %eax
	cmpl	%eax, -60(%rbp)
	jl	.L34
	jmp	.L33
.L41:
	nop
.L33:
	movl	$0, -56(%rbp)
	jmp	.L35
.L37:
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	movl	-56(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rdx, %rax
	movl	200(%rax), %eax
	testl	%eax, %eax
	je	.L36
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	movl	-56(%rbp), %eax
	cltq
	salq	$10, %rax
	leaq	(%rdx,%rax), %rcx
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	movl	-56(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rdx, %rax
	movq	32(%rax), %rdx
	movl	-56(%rbp), %eax
	cltq
	salq	$2, %rax
	addq	%rax, %rdx
	movl	200(%rcx), %eax
	movl	%eax, (%rdx)
.L36:
	addl	$1, -56(%rbp)
.L35:
	movq	-88(%rbp), %rax
	movl	104(%rax), %eax
	cmpl	%eax, -56(%rbp)
	jl	.L37
	movl	$0, %eax
.L38:
	movq	-8(%rbp), %rdx
	subq	%fs:40, %rdx
	je	.L39
	call	__stack_chk_fail@PLT
.L39:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE12:
	.size	singlewriter, .-singlewriter
	.globl	threadwork
	.type	threadwork, @function
threadwork:
.LFB13:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$144, %rsp
	movq	%rdi, -136(%rbp)
	movq	%fs:40, %rax
	movq	%rax, -8(%rbp)
	xorl	%eax, %eax
	movl	$5, -92(%rbp)
	movl	$1, -88(%rbp)
	movl	$255, -84(%rbp)
#APP
# 491 "stream2-workqueue.c" 1
	mov %rsp, %rax
# 0 "" 2
#NO_APP
	movq	%rax, -40(%rbp)
	movq	-136(%rbp), %rax
	movq	968(%rax), %rax
	movq	-40(%rbp), %rdx
	movq	%rdx, (%rax)
	movq	-136(%rbp), %rax
	movq	968(%rax), %rdx
	movq	-136(%rbp), %rax
	movq	960(%rax), %rax
	movl	$3, %esi
	movq	%rax, %rdi
	call	switch_to@PLT
	leaq	-32(%rbp), %rax
	movq	%rax, %rsi
	movl	$4, %edi
	call	clock_gettime@PLT
	movq	-136(%rbp), %rax
	movl	92(%rax), %eax
	cmpl	$2, %eax
	jne	.L43
	movl	$0, -104(%rbp)
	jmp	.L44
.L46:
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	movq	896(%rax), %rdx
	movq	-136(%rbp), %rax
	movl	908(%rax), %eax
	sall	$7, %eax
	cltq
	salq	$3, %rax
	addq	%rdx, %rax
	movq	(%rax), %rax
	movl	-88(%rbp), %edx
	movslq	%edx, %rdi
	cqto
	idivq	%rdi
	movq	%rax, %rdx
	movl	-84(%rbp), %eax
	movslq	%eax, %rcx
	movq	%rdx, %rax
	cqto
	idivq	%rcx
	movq	%rdx, %rax
	movl	%eax, -100(%rbp)
	movq	-136(%rbp), %rax
	movl	384(%rax), %eax
	movl	%eax, -96(%rbp)
	movq	-136(%rbp), %rax
	movl	908(%rax), %eax
	sall	$24, %eax
	movl	%eax, %edx
	movl	-100(%rbp), %eax
	sall	$16, %eax
	movl	%edx, %esi
	orl	%eax, %esi
	movl	-96(%rbp), %eax
	movslq	%eax, %rdx
	imulq	$-2139062143, %rdx, %rdx
	shrq	$32, %rdx
	addl	%eax, %edx
	sarl	$7, %edx
	movl	%eax, %edi
	sarl	$31, %edi
	movl	%edx, %ecx
	subl	%edi, %ecx
	movl	%ecx, %edx
	sall	$8, %edx
	subl	%ecx, %edx
	subl	%edx, %eax
	movl	%eax, %ecx
	movl	%esi, %eax
	orl	%ecx, %eax
	cltq
	movq	%rax, -72(%rbp)
	movq	-136(%rbp), %rax
	movq	48(%rax), %rdx
	movq	-136(%rbp), %rax
	movl	100(%rax), %eax
	cltq
	salq	$10, %rax
	addq	%rdx, %rax
	movq	%rax, -64(%rbp)
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	movq	112(%rax), %rdx
	movq	-72(%rbp), %rax
	addq	%rdx, %rax
	movzbl	(%rax), %eax
	cmpb	$-1, %al
	je	.L45
	movq	-136(%rbp), %rax
	movq	80(%rax), %rax
	leaq	1(%rax), %rdx
	movq	-136(%rbp), %rax
	movq	%rdx, 80(%rax)
.L45:
	movq	-136(%rbp), %rax
	movl	100(%rax), %edx
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	movq	112(%rax), %rcx
	movq	-72(%rbp), %rax
	addq	%rcx, %rax
	movb	%dl, (%rax)
	movq	-136(%rbp), %rax
	movl	384(%rax), %eax
	addl	$1, %eax
	cltd
	idivl	-92(%rbp)
	movq	-136(%rbp), %rax
	movl	%edx, 384(%rax)
	addl	$1, -104(%rbp)
.L44:
	movq	-136(%rbp), %rax
	movl	104(%rax), %eax
	cmpl	%eax, -104(%rbp)
	jl	.L46
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	movq	896(%rax), %rdx
	movq	-136(%rbp), %rax
	movl	908(%rax), %eax
	sall	$7, %eax
	cltq
	salq	$3, %rax
	addq	%rdx, %rax
	lock addq	$1, (%rax)
.L43:
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	movq	896(%rax), %rdx
	movq	-136(%rbp), %rax
	movl	908(%rax), %eax
	sall	$7, %eax
	cltq
	salq	$3, %rax
	addq	%rdx, %rax
	movq	(%rax), %rax
	movl	-88(%rbp), %edx
	movslq	%edx, %rdi
	cqto
	idivq	%rdi
	movq	%rax, -56(%rbp)
	movq	-136(%rbp), %rax
	movl	904(%rax), %eax
	cltq
	cmpq	%rax, -56(%rbp)
	je	.L47
	movq	-136(%rbp), %rax
	movl	$0, 384(%rax)
.L47:
	movq	-56(%rbp), %rax
	movl	%eax, %edx
	movq	-136(%rbp), %rax
	movl	%edx, 904(%rax)
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	movq	896(%rax), %rdx
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	sall	$7, %eax
	cltq
	salq	$3, %rax
	addq	%rdx, %rax
	movq	(%rax), %rax
	movq	%rax, -48(%rbp)
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	movl	(%rax), %eax
	cltq
	cmpq	%rax, -48(%rbp)
	jg	.L48
	cmpq	$0, -48(%rbp)
	jne	.L49
.L48:
	movl	$0, -108(%rbp)
	jmp	.L50
.L57:
	movq	-136(%rbp), %rax
	movq	72(%rax), %rax
	leaq	1(%rax), %rdx
	movq	-136(%rbp), %rax
	movq	%rdx, 72(%rax)
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	movl	(%rax), %eax
	cltd
	idivl	-88(%rbp)
	subl	$1, %eax
	cltd
	idivl	-84(%rbp)
	movl	%edx, %eax
	cltq
	movq	%rax, -80(%rbp)
	cmpq	$0, -80(%rbp)
	jns	.L51
	movq	$0, -80(%rbp)
.L51:
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	movl	4(%rax), %eax
	movl	%eax, -116(%rbp)
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	sall	$24, %eax
	movslq	%eax, %rdx
	movq	-80(%rbp), %rax
	salq	$16, %rax
	movq	%rdx, %rsi
	orq	%rax, %rsi
	movl	-116(%rbp), %eax
	movslq	%eax, %rdx
	imulq	$-2139062143, %rdx, %rdx
	shrq	$32, %rdx
	addl	%eax, %edx
	sarl	$7, %edx
	movl	%eax, %ecx
	sarl	$31, %ecx
	subl	%ecx, %edx
	movl	%edx, %ecx
	sall	$8, %ecx
	subl	%edx, %ecx
	subl	%ecx, %eax
	movl	%eax, %edx
	movslq	%edx, %rax
	orq	%rsi, %rax
	movq	%rax, -72(%rbp)
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	movl	%eax, -112(%rbp)
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	movq	112(%rax), %rdx
	movq	-72(%rbp), %rax
	addq	%rdx, %rax
	movzbl	(%rax), %eax
	cmpb	$-1, %al
	je	.L52
	movq	-136(%rbp), %rax
	movq	920(%rax), %rax
	leaq	1(%rax), %rdx
	movq	-136(%rbp), %rax
	movq	%rdx, 920(%rax)
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	movq	112(%rax), %rdx
	movq	-72(%rbp), %rax
	addq	%rdx, %rax
	movb	$-1, (%rax)
.L52:
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	movl	-112(%rbp), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	movl	4(%rax), %eax
	cmpl	%eax, -92(%rbp)
	jle	.L53
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	movl	-112(%rbp), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	movl	(%rax), %edx
	addl	$1, %edx
	movl	%edx, (%rax)
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	movl	-112(%rbp), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	movl	4(%rax), %ecx
	movq	-136(%rbp), %rax
	movq	840(%rax), %rsi
	movl	-112(%rbp), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rsi, %rax
	leal	1(%rcx), %edx
	movl	%edx, 4(%rax)
.L53:
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	movl	-112(%rbp), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	movl	4(%rax), %eax
	cmpl	%eax, -92(%rbp)
	jne	.L54
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	leal	1(%rax), %edx
	movq	-136(%rbp), %rax
	movl	%edx, 912(%rax)
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	movl	-112(%rbp), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	movl	$0, 4(%rax)
.L54:
	movq	-136(%rbp), %rax
	movl	912(%rax), %edx
	movq	-136(%rbp), %rax
	movl	908(%rax), %eax
	cmpl	%eax, %edx
	jne	.L55
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	leal	1(%rax), %edx
	movq	-136(%rbp), %rax
	movl	%edx, 912(%rax)
.L55:
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	cmpl	$5, %eax
	jne	.L56
	movq	-136(%rbp), %rax
	movl	$1, 912(%rax)
.L56:
	addl	$1, -108(%rbp)
.L50:
	movq	-136(%rbp), %rax
	movl	104(%rax), %eax
	subl	$1, %eax
	cmpl	%eax, -108(%rbp)
	jl	.L57
.L49:
	nop
	movq	-8(%rbp), %rdx
	subq	%fs:40, %rdx
	je	.L58
	call	__stack_chk_fail@PLT
.L58:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE13:
	.size	threadwork, .-threadwork
	.globl	work2
	.type	work2, @function
work2:
.LFB14:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -24(%rbp)
	movq	-24(%rbp), %rax
	movq	%rax, -8(%rbp)
	jmp	.L60
.L61:
	movq	-8(%rbp), %rax
	movq	72(%rax), %rax
	leaq	1(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 72(%rax)
.L60:
	movq	-8(%rbp), %rax
	movl	92(%rax), %eax
	cmpl	$1, %eax
	je	.L61
	nop
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE14:
	.size	work2, .-work2
	.section	.rodata
.LC2:
	.string	"started thread %d\n"
.LC3:
	.string	"%d thread exit\n"
	.text
	.globl	work
	.type	work, @function
work:
.LFB15:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$80, %rsp
	movq	%rdi, -72(%rbp)
	movq	-72(%rbp), %rax
	movq	%rax, -32(%rbp)
	movq	-32(%rbp), %rax
	movl	100(%rax), %eax
	movl	%eax, %esi
	leaq	.LC2(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, -56(%rbp)
	movq	-32(%rbp), %rax
	movl	100(%rax), %eax
	leal	1(%rax), %edx
	movq	-32(%rbp), %rax
	movl	104(%rax), %ecx
	movl	%edx, %eax
	cltd
	idivl	%ecx
	movl	%edx, -52(%rbp)
	movl	$0, -48(%rbp)
	movq	-32(%rbp), %rax
	movq	184(%rax), %rax
	addq	$1, %rax
	movl	$8, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -24(%rbp)
	movq	-32(%rbp), %rax
	movl	104(%rax), %eax
	cltq
	movl	$4, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -16(%rbp)
	movq	-32(%rbp), %rax
	movl	104(%rax), %eax
	cltq
	movl	$4, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -8(%rbp)
	movl	$0, -44(%rbp)
	jmp	.L63
.L64:
	movl	$0, -40(%rbp)
	movl	$0, -36(%rbp)
	movl	$0, -44(%rbp)
	movq	-32(%rbp), %rax
	movq	-32(%rbp), %rax
	movq	%rax, %rdi
	call	threadwork@PLT
.L63:
	movq	-32(%rbp), %rax
	movl	92(%rax), %eax
	testl	%eax, %eax
	jg	.L64
	movq	-32(%rbp), %rax
	movl	100(%rax), %eax
	movl	%eax, %esi
	leaq	.LC3(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	nop
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE15:
	.size	work, .-work
	.section	.rodata
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
	.align 8
.LC11:
	.string	"assigning thread %d to cpu %d\n"
.LC12:
	.string	"runphased"
.LC13:
	.string	"draining"
.LC14:
	.string	"finished simulation."
.LC15:
	.string	"%ld reads\n"
.LC16:
	.string	"freq: %ld\n"
.LC17:
	.string	"freq_ps: %ld\n"
.LC18:
	.string	"freq latency2: %ld\n"
.LC19:
	.string	"freq per thread latency: %ld\n"
.LC20:
	.string	"freq latency: %ld\n"
.LC21:
	.string	"%ld successreads\n"
.LC22:
	.string	"%ld writes\n"
.LC23:
	.string	"freq_writes: %ld\n"
.LC24:
	.string	"freq_writes_total: %ld\n"
.LC25:
	.string	"freq_writes latency2: %ld\n"
	.align 8
.LC26:
	.string	"freq_writes per thread latency: %ld\n"
.LC27:
	.string	"freq_writes latency: %ld\n"
.LC28:
	.string	"writer speed"
.LC29:
	.string	"sw %ld\n"
.LC30:
	.string	"%ld good reads per second\n"
	.align 8
.LC31:
	.string	"%ld good reads per second latency\n"
.LC32:
	.string	"coroutine.struct"
.LC33:
	.string	"w"
.LC34:
	.string	"index %ld\n"
.LC35:
	.string	"rsp %ld\n"
.LC36:
	.string	"eip %ld\n"
.LC37:
	.string	"data %ld\n"
.LC38:
	.string	"corourinedata.running %ld\n"
.LC39:
	.string	"size coroutine %ld\n"
	.text
	.globl	main
	.type	main, @function
main:
.LFB16:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%rbx
	subq	$376, %rsp
	.cfi_offset 3, -24
	movl	%edi, -372(%rbp)
	movq	%rsi, -384(%rbp)
	movq	%fs:40, %rax
	movq	%rax, -24(%rbp)
	xorl	%eax, %eax
	movl	$0, -352(%rbp)
	movl	$1, -348(%rbp)
	movl	$1, -364(%rbp)
	movl	$15, -360(%rbp)
	movl	-360(%rbp), %eax
	subl	$1, %eax
	movl	%eax, -356(%rbp)
	movl	$8, %esi
	leaq	.LC4(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$4, %esi
	leaq	.LC5(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$32, %esi
	leaq	.LC6(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-360(%rbp), %eax
	movl	%eax, %esi
	leaq	.LC7(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-360(%rbp), %eax
	cltq
	movl	$8, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -232(%rbp)
	movl	-360(%rbp), %eax
	cltq
	movl	$56, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -272(%rbp)
	movl	-360(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rsi
	movl	$1, %edi
	call	calloc@PLT
	movq	%rax, -264(%rbp)
	movq	$0, -256(%rbp)
	movl	$4294967295, %eax
	movq	%rax, -248(%rbp)
	movl	-364(%rbp), %eax
	cltq
	movq	-248(%rbp), %rdx
	imulq	%rdx, %rax
	movq	%rax, -240(%rbp)
	movl	-360(%rbp), %eax
	movslq	%eax, %rbx
	movq	-240(%rbp), %rax
	cqto
	idivq	%rbx
	movl	%eax, -368(%rbp)
	pxor	%xmm0, %xmm0
	cvtsi2sdq	-240(%rbp), %xmm0
	pxor	%xmm1, %xmm1
	cvtsi2sdq	-248(%rbp), %xmm1
	divsd	%xmm1, %xmm0
	movq	%xmm0, %rax
	movq	%rax, %xmm0
	call	ceil@PLT
	cvttsd2siq	%xmm0, %rax
	movq	%rax, -200(%rbp)
	movq	-240(%rbp), %rax
	movl	$1, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -192(%rbp)
	movq	-240(%rbp), %rdx
	movq	-192(%rbp), %rax
	movl	$-1, %esi
	movq	%rax, %rdi
	call	memset@PLT
	movq	-240(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC8(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, -300(%rbp)
	movl	-360(%rbp), %eax
	cltq
	movl	$4, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -184(%rbp)
	movl	-360(%rbp), %eax
	cltq
	movl	$4, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -176(%rbp)
	movl	$32, %esi
	movl	$100, %edi
	call	calloc@PLT
	movq	%rax, -168(%rbp)
	movq	-256(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC9(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movq	-248(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC10(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, -316(%rbp)
	movl	-360(%rbp), %eax
	cltq
	movl	$4, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -160(%rbp)
	leaq	-288(%rbp), %rax
	movl	$512, %edx
	movl	$128, %esi
	movq	%rax, %rdi
	call	posix_memalign@PLT
	movl	-360(%rbp), %eax
	cltq
	movl	$12, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -152(%rbp)
	movq	-264(%rbp), %rax
	movq	-192(%rbp), %rdx
	movq	%rdx, 112(%rax)
	movl	$100000000, -296(%rbp)
	movl	-296(%rbp), %eax
	cltq
	movl	$20, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -144(%rbp)
	movl	-296(%rbp), %eax
	cltq
	movl	$20, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -136(%rbp)
	movl	$8, %esi
	movl	$1, %edi
	call	calloc@PLT
	movq	%rax, -128(%rbp)
	movl	$0, -312(%rbp)
	jmp	.L66
.L71:
	movl	$32, %esi
	movl	$10, %edi
	call	calloc@PLT
	movq	%rax, -88(%rbp)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movq	-88(%rbp), %rax
	movq	%rax, 960(%rdx)
	movl	$0, -308(%rbp)
	jmp	.L67
.L68:
	leaq	-48(%rbp), %rax
	movl	$8016, %edx
	movl	$16, %esi
	movq	%rax, %rdi
	call	posix_memalign@PLT
	movl	$4, %esi
	movl	$1, %edi
	call	calloc@PLT
	movq	%rax, -72(%rbp)
	movl	-308(%rbp), %eax
	cltq
	salq	$5, %rax
	movq	%rax, %rdx
	movq	-88(%rbp), %rax
	addq	%rax, %rdx
	movq	-72(%rbp), %rax
	movq	%rax, 24(%rdx)
	movq	-72(%rbp), %rax
	movl	$1, (%rax)
	movl	-308(%rbp), %eax
	cltq
	salq	$5, %rax
	movq	%rax, %rdx
	movq	-88(%rbp), %rax
	addq	%rdx, %rax
	movq	coroutine_func@GOTPCREL(%rip), %rdx
	movq	%rdx, 16(%rax)
	movq	-48(%rbp), %rax
	leaq	8016(%rax), %rdx
	movl	-308(%rbp), %eax
	cltq
	salq	$5, %rax
	movq	%rax, %rcx
	movq	-88(%rbp), %rax
	addq	%rcx, %rax
	movq	%rdx, 8(%rax)
	addl	$1, -308(%rbp)
.L67:
	cmpl	$9, -308(%rbp)
	jle	.L68
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movq	-128(%rbp), %rax
	movq	%rax, 968(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movq	-144(%rbp), %rax
	movq	%rax, 928(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movq	-136(%rbp), %rax
	movq	%rax, 936(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	leaq	(%rdx,%rax), %rbx
	movl	$128, %esi
	movl	$1, %edi
	call	calloc@PLT
	movq	%rax, 120(%rbx)
	addl	$1, -316(%rbp)
	movl	-316(%rbp), %eax
	cltq
	movq	%rax, -80(%rbp)
	cmpq	$1023, -80(%rbp)
	ja	.L70
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	120(%rax), %rax
	movq	%rax, %rcx
	movq	-80(%rbp), %rax
	shrq	$6, %rax
	leaq	0(,%rax,8), %rdx
	addq	%rcx, %rdx
	movq	(%rdx), %rsi
	movq	-80(%rbp), %rdx
	andl	$63, %edx
	movl	$1, %edi
	movl	%edx, %ecx
	salq	%cl, %rdi
	movq	%rdi, %rcx
	movl	-312(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rdi
	salq	$10, %rdi
	movq	-264(%rbp), %rdx
	addq	%rdi, %rdx
	movq	120(%rdx), %rdx
	salq	$3, %rax
	addq	%rdx, %rax
	orq	%rcx, %rsi
	movq	%rsi, %rdx
	movq	%rdx, (%rax)
.L70:
	movl	-316(%rbp), %edx
	movl	-312(%rbp), %eax
	movl	%eax, %esi
	leaq	.LC11(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movl	-312(%rbp), %eax
	imull	-368(%rbp), %eax
	movl	%eax, 152(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movq	-288(%rbp), %rax
	movq	%rax, 896(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movl	-352(%rbp), %eax
	movl	%eax, 128(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movl	$2, 92(%rax)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movl	-312(%rbp), %eax
	movl	%eax, 100(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	-240(%rbp), %rdx
	movl	%edx, 96(%rax)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movl	-368(%rbp), %eax
	movl	%eax, 148(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movl	-360(%rbp), %eax
	movl	%eax, 104(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movq	-160(%rbp), %rax
	movq	%rax, 32(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	32(%rax), %rdx
	movl	-312(%rbp), %eax
	cltq
	salq	$2, %rax
	addq	%rdx, %rax
	movl	$0, (%rax)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movl	-368(%rbp), %eax
	movl	%eax, 144(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movq	-264(%rbp), %rax
	movq	%rax, 40(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movq	-264(%rbp), %rax
	movq	%rax, 48(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	$0, (%rax)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movq	-240(%rbp), %rax
	movq	%rax, 8(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movl	-360(%rbp), %edx
	subl	$1, %edx
	movl	%edx, 512(%rax)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movl	$0, 384(%rax)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movq	-168(%rbp), %rax
	movq	%rax, 160(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movq	-200(%rbp), %rax
	movq	%rax, 192(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movq	-248(%rbp), %rax
	movq	%rax, 184(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movl	$0, 200(%rax)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movl	-360(%rbp), %eax
	cltq
	movq	%rax, 776(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movl	-360(%rbp), %eax
	cltq
	movq	%rax, 784(%rdx)
	movl	-312(%rbp), %eax
	leal	3(%rax), %edx
	testl	%eax, %eax
	cmovs	%edx, %eax
	sarl	$2, %eax
	movl	%eax, %edx
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rcx
	movq	-264(%rbp), %rax
	addq	%rcx, %rax
	addl	$1, %edx
	movl	%edx, 908(%rax)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movl	-360(%rbp), %eax
	movl	%eax, 808(%rdx)
	movl	$10000000, -292(%rbp)
	movl	-292(%rbp), %eax
	cltq
	movl	-312(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	leaq	(%rcx,%rdx), %rbx
	movl	$48, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, 792(%rbx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movl	-292(%rbp), %eax
	movl	%eax, 800(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movq	-152(%rbp), %rax
	movq	%rax, 840(%rdx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	leaq	(%rdx,%rax), %rbx
	movl	$48, %esi
	movl	$10000, %edi
	call	calloc@PLT
	movq	%rax, 816(%rbx)
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movl	-296(%rbp), %eax
	movl	%eax, 952(%rdx)
	addl	$1, -312(%rbp)
.L66:
	movl	-312(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L71
	movl	$0, -304(%rbp)
	jmp	.L72
.L73:
	movl	-304(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	movl	-304(%rbp), %eax
	movslq	%eax, %rcx
	movq	%rcx, %rax
	salq	$3, %rax
	subq	%rcx, %rax
	salq	$3, %rax
	movq	%rax, %rcx
	movq	-272(%rbp), %rax
	leaq	(%rcx,%rax), %rsi
	movl	-304(%rbp), %eax
	cltq
	leaq	0(,%rax,8), %rcx
	movq	-232(%rbp), %rax
	addq	%rcx, %rax
	movq	%rdx, %rcx
	movq	work@GOTPCREL(%rip), %rdx
	movq	%rax, %rdi
	call	pthread_create@PLT
	movl	-304(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	120(%rax), %rdx
	movl	-304(%rbp), %eax
	cltq
	leaq	0(,%rax,8), %rcx
	movq	-232(%rbp), %rax
	addq	%rcx, %rax
	movq	(%rax), %rax
	movl	$8, %esi
	movq	%rax, %rdi
	call	pthread_setaffinity_np@PLT
	addl	$1, -304(%rbp)
.L72:
	movl	-304(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L73
	movl	-348(%rbp), %eax
	cltq
	movq	%rax, -64(%rbp)
	movq	$0, -56(%rbp)
	movq	$0, -48(%rbp)
	movq	$0, -40(%rbp)
	leaq	-48(%rbp), %rdx
	leaq	-64(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	nanosleep@PLT
	leaq	.LC12(%rip), %rax
	movq	%rax, %rdi
	call	puts@PLT
	movl	$0, -328(%rbp)
	jmp	.L74
.L75:
	movl	-328(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movl	92(%rax), %edx
	subl	$1, %edx
	movl	%edx, 92(%rax)
	addl	$1, -328(%rbp)
.L74:
	movl	-328(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L75
	leaq	.LC13(%rip), %rax
	movq	%rax, %rdi
	call	puts@PLT
	movl	$0, -324(%rbp)
	jmp	.L76
.L77:
	movl	-324(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movl	92(%rax), %edx
	subl	$1, %edx
	movl	%edx, 92(%rax)
	addl	$1, -324(%rbp)
.L76:
	movl	-324(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L77
	movl	$0, -320(%rbp)
	jmp	.L78
.L79:
	movl	-320(%rbp), %eax
	cltq
	leaq	0(,%rax,8), %rdx
	movq	-232(%rbp), %rax
	addq	%rdx, %rax
	movq	(%rax), %rax
	leaq	-280(%rbp), %rdx
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	pthread_join@PLT
	addl	$1, -320(%rbp)
.L78:
	movl	-320(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L79
	leaq	.LC14(%rip), %rax
	movq	%rax, %rdi
	call	puts@PLT
	movq	$0, -224(%rbp)
	movq	$1, -120(%rbp)
	movl	$0, -344(%rbp)
	jmp	.L80
.L81:
	movl	-344(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	72(%rax), %rax
	movq	%rax, %rsi
	leaq	.LC15(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-344(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	72(%rax), %rax
	addq	%rax, -224(%rbp)
	addl	$1, -344(%rbp)
.L80:
	movl	-344(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L81
	movl	-348(%rbp), %eax
	movslq	%eax, %rbx
	movq	-224(%rbp), %rax
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC16(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movq	-224(%rbp), %rax
	imulq	-120(%rbp), %rax
	movl	-348(%rbp), %edx
	movslq	%edx, %rbx
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC17(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-348(%rbp), %eax
	movslq	%eax, %rbx
	movq	-224(%rbp), %rax
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC18(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-348(%rbp), %eax
	movslq	%eax, %rbx
	movq	-224(%rbp), %rax
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	cqto
	idivq	-120(%rbp)
	movq	%rax, %rsi
	leaq	.LC19(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movq	-224(%rbp), %rax
	imulq	-120(%rbp), %rax
	movl	-348(%rbp), %edx
	movslq	%edx, %rbx
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC20(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movq	$0, -216(%rbp)
	movl	$0, -340(%rbp)
	jmp	.L82
.L83:
	movl	-340(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	920(%rax), %rax
	movq	%rax, %rsi
	leaq	.LC21(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-340(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	920(%rax), %rax
	addq	%rax, -216(%rbp)
	addl	$1, -340(%rbp)
.L82:
	movl	-340(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L83
	movq	$0, -208(%rbp)
	movl	$0, -336(%rbp)
	jmp	.L84
.L85:
	movl	-336(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	80(%rax), %rax
	addq	%rax, -208(%rbp)
	movl	-336(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	80(%rax), %rax
	movq	%rax, %rsi
	leaq	.LC22(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	addl	$1, -336(%rbp)
.L84:
	movl	-336(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L85
	movl	-348(%rbp), %eax
	movslq	%eax, %rbx
	movq	-208(%rbp), %rax
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC23(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movq	-208(%rbp), %rax
	imulq	-120(%rbp), %rax
	movl	-348(%rbp), %edx
	movslq	%edx, %rbx
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC24(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-348(%rbp), %eax
	movslq	%eax, %rbx
	movq	-208(%rbp), %rax
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC25(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-348(%rbp), %eax
	movslq	%eax, %rbx
	movq	-208(%rbp), %rax
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	cqto
	idivq	-120(%rbp)
	movq	%rax, %rsi
	leaq	.LC26(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movq	-208(%rbp), %rax
	imulq	-120(%rbp), %rax
	movl	-348(%rbp), %edx
	movslq	%edx, %rbx
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC27(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	leaq	.LC28(%rip), %rax
	movq	%rax, %rdi
	call	puts@PLT
	movl	$0, -332(%rbp)
	jmp	.L86
.L87:
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	240(%rax), %rax
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	movq	224(%rdx), %rdx
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	256(%rax), %rax
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	movq	224(%rdx), %rdx
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	240(%rax), %rax
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	movq	256(%rdx), %rdx
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	288(%rax), %rax
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	movq	272(%rdx), %rdx
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	272(%rax), %rax
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	movq	288(%rdx), %rdx
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	272(%rax), %rax
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	movq	256(%rdx), %rdx
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	movq	320(%rax), %rax
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	movq	304(%rdx), %rdx
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC29(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	addl	$1, -332(%rbp)
.L86:
	cmpl	$0, -332(%rbp)
	jle	.L87
	movl	-348(%rbp), %eax
	movslq	%eax, %rbx
	movq	-216(%rbp), %rax
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC30(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	-348(%rbp), %eax
	movslq	%eax, %rbx
	movq	-216(%rbp), %rax
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC31(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$1, %esi
	movl	$100, %edi
	call	calloc@PLT
	movq	%rax, -112(%rbp)
	movl	$1, %esi
	movl	$1000, %edi
	call	calloc@PLT
	movq	%rax, -104(%rbp)
	movq	-112(%rbp), %rax
	movl	$100, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	movq	-112(%rbp), %rax
	leaq	.LC32(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	movq	-112(%rbp), %rax
	leaq	.LC33(%rip), %rdx
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fopen@PLT
	movq	%rax, -96(%rbp)
	movq	-104(%rbp), %rax
	movl	$1000, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	movq	-104(%rbp), %rax
	movl	$0, %ecx
	leaq	.LC34(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	movq	-96(%rbp), %rdx
	movq	-104(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fputs@PLT
	movq	-104(%rbp), %rax
	movl	$1000, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	movq	-104(%rbp), %rax
	movl	$8, %ecx
	leaq	.LC35(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	movq	-96(%rbp), %rdx
	movq	-104(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fputs@PLT
	movq	-104(%rbp), %rax
	movl	$1000, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	movq	-104(%rbp), %rax
	movl	$16, %ecx
	leaq	.LC36(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	movq	-96(%rbp), %rdx
	movq	-104(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fputs@PLT
	movq	-104(%rbp), %rax
	movl	$1000, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	movq	-104(%rbp), %rax
	movl	$24, %ecx
	leaq	.LC37(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	movq	-96(%rbp), %rdx
	movq	-104(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fputs@PLT
	movq	-104(%rbp), %rax
	movl	$1000, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	movq	-104(%rbp), %rax
	movl	$0, %ecx
	leaq	.LC38(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	movq	-96(%rbp), %rdx
	movq	-104(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fputs@PLT
	movq	-104(%rbp), %rax
	movl	$1000, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	movq	-104(%rbp), %rax
	movl	$32, %ecx
	leaq	.LC39(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	movq	-96(%rbp), %rdx
	movq	-104(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fputs@PLT
	movq	-96(%rbp), %rax
	movq	%rax, %rdi
	call	fclose@PLT
	movl	$0, %eax
	movq	-24(%rbp), %rdx
	subq	%fs:40, %rdx
	je	.L89
	call	__stack_chk_fail@PLT
.L89:
	movq	-8(%rbp), %rbx
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE16:
	.size	main, .-main
	.ident	"GCC: (GNU) 11.3.0"
	.section	.note.GNU-stack,"",@progbits
