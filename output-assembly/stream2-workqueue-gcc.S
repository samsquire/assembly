	.file	"stream2-workqueue.c"
	.text
.Ltext0:
	.file 0 "/home/runner/assembly" "stream2-workqueue.c"
	.globl	yield
	.type	yield, @function
yield:
.LFB6:
	.file 1 "stream2-workqueue.c"
	.loc 1 63 13
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	.loc 1 65 1
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
	.loc 1 67 108
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
	.loc 1 68 2
	movq	-24(%rbp), %rcx
	movq	-16(%rbp), %rdx
	movq	-8(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC0(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 71 9
	jmp	.L3
.L4:
	.loc 1 76 5
	movq	-16(%rbp), %rax
	movq	16(%rax), %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
.L3:
	.loc 1 71 14
	movq	-24(%rbp), %rax
	movl	(%rax), %eax
	.loc 1 71 24
	cmpl	$1, %eax
	je	.L4
	.loc 1 80 10
	movl	$0, %eax
	.loc 1 83 1
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
	.loc 1 207 107
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
	.loc 1 208 8
	movq	$4, -16(%rbp)
	.loc 1 209 8
	movq	$8, -8(%rbp)
.LBB2:
	.loc 1 210 12
	movl	$1, -24(%rbp)
	.loc 1 210 3
	jmp	.L7
.L12:
.LBB3:
	.loc 1 212 20
	movq	-40(%rbp), %rax
	movq	48(%rax), %rax
	.loc 1 212 29
	addq	$1024, %rax
	.loc 1 212 32
	movq	32(%rax), %rdx
	.loc 1 212 40
	movl	-24(%rbp), %eax
	cltq
	salq	$2, %rax
	addq	%rdx, %rax
	.loc 1 212 9
	movl	(%rax), %eax
	movl	%eax, -20(%rbp)
	.loc 1 219 19
	movl	-20(%rbp), %eax
	cltq
	andq	-16(%rbp), %rax
	.loc 1 219 12
	cmpq	%rax, -16(%rbp)
	je	.L8
	.loc 1 219 31 discriminator 1
	cmpl	$0, -20(%rbp)
	jne	.L9
.L8:
	.loc 1 221 25
	movq	-72(%rbp), %rax
	movl	(%rax), %eax
	.loc 1 221 34
	leal	1(%rax), %ecx
	movq	-72(%rbp), %rdx
	movl	%ecx, (%rdx)
	cltq
	.loc 1 221 23
	leaq	0(,%rax,4), %rdx
	movq	-56(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 221 38
	movl	-24(%rbp), %eax
	movl	%eax, (%rdx)
.L9:
	.loc 1 223 15
	movl	-20(%rbp), %eax
	cltq
	andq	-8(%rbp), %rax
	.loc 1 223 8
	cmpq	%rax, -8(%rbp)
	je	.L10
	.loc 1 223 27 discriminator 1
	cmpl	$0, -20(%rbp)
	jne	.L11
.L10:
	.loc 1 224 21
	movq	-64(%rbp), %rax
	movl	(%rax), %eax
	.loc 1 224 30
	leal	1(%rax), %ecx
	movq	-64(%rbp), %rdx
	movl	%ecx, (%rdx)
	cltq
	.loc 1 224 19
	leaq	0(,%rax,4), %rdx
	movq	-48(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 224 34
	movl	-24(%rbp), %eax
	movl	%eax, (%rdx)
.L11:
.LBE3:
	.loc 1 210 43 discriminator 2
	addl	$1, -24(%rbp)
.L7:
	.loc 1 210 27 discriminator 1
	movq	-40(%rbp), %rax
	movl	104(%rax), %eax
	.loc 1 210 21 discriminator 1
	cmpl	%eax, -24(%rbp)
	jl	.L12
.LBE2:
	.loc 1 230 10
	movl	$0, %eax
	.loc 1 231 1
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
	.loc 1 234 117
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
.LBB4:
	.loc 1 235 12
	movl	$0, -4(%rbp)
	.loc 1 235 3
	jmp	.L15
.L18:
	.loc 1 237 17
	movq	-24(%rbp), %rax
	movq	160(%rax), %rdx
	.loc 1 237 27
	movl	-4(%rbp), %eax
	cltq
	salq	$5, %rax
	addq	%rdx, %rax
	.loc 1 237 30
	movl	16(%rax), %eax
	.loc 1 237 12
	cmpl	$1, %eax
	jne	.L16
	.loc 1 239 20
	movq	-40(%rbp), %rax
	movl	(%rax), %eax
	cltq
	.loc 1 239 19
	leaq	0(,%rax,8), %rdx
	movq	-32(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 239 35
	movl	-4(%rbp), %eax
	cltq
	movq	%rax, (%rdx)
	.loc 1 240 11
	movq	-40(%rbp), %rax
	movl	(%rax), %eax
	.loc 1 240 25
	leal	1(%rax), %edx
	movq	-40(%rbp), %rax
	movl	%edx, (%rax)
	.loc 1 241 15
	movq	-40(%rbp), %rax
	movl	(%rax), %edx
	.loc 1 241 37
	movq	-24(%rbp), %rax
	movl	104(%rax), %eax
	.loc 1 241 50
	addl	%eax, %eax
	.loc 1 241 13
	cmpl	%eax, %edx
	je	.L21
.L16:
	.loc 1 235 46 discriminator 2
	addl	$1, -4(%rbp)
.L15:
	.loc 1 235 21 discriminator 1
	movl	-4(%rbp), %eax
	movslq	%eax, %rdx
	.loc 1 235 27 discriminator 1
	movq	-24(%rbp), %rax
	movq	184(%rax), %rax
	.loc 1 235 39 discriminator 1
	addq	$1, %rax
	.loc 1 235 21 discriminator 1
	cmpq	%rax, %rdx
	jl	.L18
	jmp	.L17
.L21:
	.loc 1 242 12
	nop
.L17:
.LBE4:
	.loc 1 248 11
	movq	-40(%rbp), %rax
	movl	(%rax), %eax
	.loc 1 248 10
	testl	%eax, %eax
	jne	.L19
	.loc 1 251 16
	movl	$1, %eax
	jmp	.L20
.L19:
	.loc 1 253 10
	movl	$0, %eax
.L20:
	.loc 1 254 1
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
	.loc 1 256 96
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
	.loc 1 257 7
	movl	$0, -4(%rbp)
	.loc 1 287 11
	movq	-24(%rbp), %rax
	movl	384(%rax), %eax
	.loc 1 287 6
	testl	%eax, %eax
	.loc 1 295 1
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
	.loc 1 297 96
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
	.loc 1 298 7
	movl	$0, -20(%rbp)
	.loc 1 327 12
	movq	-40(%rbp), %rax
	movl	512(%rax), %eax
	.loc 1 327 7
	testl	%eax, %eax
	je	.L25
	.loc 1 327 38 discriminator 1
	movq	-40(%rbp), %rax
	movl	512(%rax), %eax
	.loc 1 327 58 discriminator 1
	movq	-40(%rbp), %rdx
	movl	104(%rdx), %edx
	.loc 1 327 71 discriminator 1
	leal	-1(%rdx), %ecx
	.loc 1 327 51 discriminator 1
	cltd
	idivl	%ecx
	movl	%edx, %eax
	.loc 1 327 30 discriminator 1
	testl	%eax, %eax
	jne	.L25
.LBB5:
	.loc 1 334 37
	movq	-40(%rbp), %rax
	movq	48(%rax), %rdx
	.loc 1 334 51
	movq	-40(%rbp), %rax
	movl	100(%rax), %eax
	cltq
	.loc 1 334 46
	salq	$10, %rax
	.loc 1 334 23
	addq	%rdx, %rax
	movq	%rax, -16(%rbp)
	.loc 1 335 39
	movq	-16(%rbp), %rax
	movq	792(%rax), %rcx
	.loc 1 335 54
	movq	-16(%rbp), %rax
	movl	804(%rax), %eax
	movslq	%eax, %rdx
	.loc 1 335 47
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$4, %rax
	.loc 1 335 24
	addq	%rcx, %rax
	movq	%rax, -8(%rbp)
	.loc 1 336 9
	movq	-8(%rbp), %rax
	addq	$8, %rax
	movq	%rax, %rsi
	movl	$4, %edi
	call	clock_gettime@PLT
	.loc 1 337 33
	movq	-16(%rbp), %rax
	movl	804(%rax), %eax
	.loc 1 337 48
	leal	1(%rax), %edx
	.loc 1 337 61
	movq	-16(%rbp), %rax
	movl	800(%rax), %ecx
	.loc 1 337 53
	movl	%edx, %eax
	cltd
	idivl	%ecx
	.loc 1 337 24
	movq	-16(%rbp), %rax
	movl	%edx, 804(%rax)
	.loc 1 338 21
	movq	-8(%rbp), %rax
	movl	$1, 32(%rax)
	.loc 1 339 29
	movq	-40(%rbp), %rax
	movl	100(%rax), %edx
	.loc 1 339 23
	movq	-8(%rbp), %rax
	movl	%edx, (%rax)
	.loc 1 340 20
	movq	-8(%rbp), %rax
	movl	$1, 36(%rax)
.L25:
.LBE5:
	.loc 1 347 1
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
	.loc 1 359 95
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
	.loc 1 359 95
	movq	%fs:40, %rax
	movq	%rax, -8(%rbp)
	xorl	%eax, %eax
	.loc 1 360 32
	movq	-88(%rbp), %rax
	movq	48(%rax), %rax
	.loc 1 360 44
	movl	524(%rax), %eax
	.loc 1 360 50
	leal	1(%rax), %edx
	.loc 1 360 61
	movq	-88(%rbp), %rax
	movl	104(%rax), %esi
	.loc 1 360 7
	movq	-88(%rbp), %rax
	movq	48(%rax), %rcx
	.loc 1 360 55
	movl	%edx, %eax
	cltd
	idivl	%esi
	movl	%edx, %eax
	.loc 1 360 25
	movl	%eax, 524(%rcx)
	.loc 1 361 7
	movl	$0, -80(%rbp)
	.loc 1 362 7
	movl	$0, -76(%rbp)
	.loc 1 363 7
	movl	$0, -72(%rbp)
	.loc 1 374 14
	movq	-112(%rbp), %rdi
	movq	-104(%rbp), %rcx
	leaq	-72(%rbp), %rdx
	movq	-96(%rbp), %rsi
	movq	-88(%rbp), %rax
	movq	%rdi, %r8
	movq	%rax, %rdi
	call	findavailable@PLT
	movl	%eax, -52(%rbp)
	.loc 1 378 6
	cmpl	$1, -52(%rbp)
	jne	.L27
	.loc 1 379 12
	movl	$1, %eax
	jmp	.L40
.L27:
	.loc 1 383 2
	leaq	-76(%rbp), %rdi
	leaq	-80(%rbp), %rcx
	movq	-112(%rbp), %rdx
	movq	-104(%rbp), %rsi
	movq	-88(%rbp), %rax
	movq	%rdi, %r8
	movq	%rax, %rdi
	call	pollthreads@PLT
	.loc 1 387 11
	movl	$0, -68(%rbp)
.LBB6:
	.loc 1 389 18
	movl	$0, -64(%rbp)
	.loc 1 389 9
	jmp	.L29
.L32:
.LBB7:
	.loc 1 390 29
	movl	-72(%rbp), %eax
	.loc 1 390 14
	cmpl	%eax, -68(%rbp)
	je	.L42
	.loc 1 394 36 discriminator 2
	movl	-64(%rbp), %eax
	cltq
	leaq	0(,%rax,4), %rdx
	movq	-104(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 394 15 discriminator 2
	movl	(%rax), %eax
	movl	%eax, -48(%rbp)
	.loc 1 396 38 discriminator 2
	movq	-88(%rbp), %rax
	movq	160(%rax), %rcx
	.loc 1 396 72 discriminator 2
	movl	-68(%rbp), %eax
	leal	1(%rax), %edx
	movl	%edx, -68(%rbp)
	cltq
	.loc 1 396 58 discriminator 2
	leaq	0(,%rax,8), %rdx
	movq	-96(%rbp), %rax
	addq	%rdx, %rax
	movq	(%rax), %rax
	.loc 1 396 48 discriminator 2
	salq	$5, %rax
	.loc 1 396 25 discriminator 2
	addq	%rcx, %rax
	movq	%rax, -24(%rbp)
	.loc 1 397 28 discriminator 2
	movq	-24(%rbp), %rax
	movl	$2, 16(%rax)
	.loc 1 401 15 discriminator 2
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	.loc 1 401 24 discriminator 2
	movl	-48(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rax, %rdx
	.loc 1 401 41 discriminator 2
	movq	-24(%rbp), %rax
	movq	%rax, 168(%rdx)
	.loc 1 403 24 discriminator 2
	movq	-24(%rbp), %rax
	movl	-48(%rbp), %edx
	movl	%edx, 20(%rax)
	.loc 1 404 28 discriminator 2
	movq	-24(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 404 15 discriminator 2
	movl	%eax, -44(%rbp)
	.loc 1 405 15 discriminator 2
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	.loc 1 405 24 discriminator 2
	movl	-48(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rax, %rdx
	.loc 1 405 39 discriminator 2
	movl	-44(%rbp), %eax
	movl	%eax, 20(%rdx)
	.loc 1 407 26 discriminator 2
	movq	-24(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 407 15 discriminator 2
	movl	%eax, -40(%rbp)
	.loc 1 408 15 discriminator 2
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	.loc 1 408 24 discriminator 2
	movl	-48(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rax, %rdx
	.loc 1 408 37 discriminator 2
	movl	-40(%rbp), %eax
	movl	%eax, 24(%rdx)
	.loc 1 412 47 discriminator 2
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	.loc 1 412 56 discriminator 2
	movl	-48(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rdx, %rax
	.loc 1 412 64 discriminator 2
	movl	200(%rax), %edx
	.loc 1 412 14 discriminator 2
	movq	-88(%rbp), %rax
	movq	48(%rax), %rcx
	.loc 1 412 23 discriminator 2
	movl	-48(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rcx, %rax
	.loc 1 412 73 discriminator 2
	orl	$16, %edx
	.loc 1 412 40 discriminator 2
	movl	%edx, 200(%rax)
.LBE7:
	.loc 1 389 40 discriminator 2
	addl	$1, -64(%rbp)
.L29:
	.loc 1 389 27 discriminator 1
	movl	-80(%rbp), %eax
	cmpl	%eax, -64(%rbp)
	jl	.L32
	jmp	.L31
.L42:
.LBB8:
	.loc 1 392 19
	nop
.L31:
.LBE8:
.LBE6:
.LBB9:
	.loc 1 416 13
	movl	$0, -60(%rbp)
	.loc 1 416 4
	jmp	.L33
.L36:
.LBB10:
	.loc 1 417 36
	movl	-72(%rbp), %eax
	.loc 1 417 20
	cmpl	%eax, -68(%rbp)
	je	.L43
	.loc 1 422 36 discriminator 2
	movl	-60(%rbp), %eax
	cltq
	leaq	0(,%rax,4), %rdx
	movq	-112(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 422 15 discriminator 2
	movl	(%rax), %eax
	movl	%eax, -36(%rbp)
	.loc 1 424 34 discriminator 2
	movq	-88(%rbp), %rax
	movq	160(%rax), %rcx
	.loc 1 424 68 discriminator 2
	movl	-68(%rbp), %eax
	leal	1(%rax), %edx
	movl	%edx, -68(%rbp)
	cltq
	.loc 1 424 54 discriminator 2
	leaq	0(,%rax,8), %rdx
	movq	-96(%rbp), %rax
	addq	%rdx, %rax
	movq	(%rax), %rax
	.loc 1 424 44 discriminator 2
	salq	$5, %rax
	.loc 1 424 21 discriminator 2
	addq	%rcx, %rax
	movq	%rax, -16(%rbp)
	.loc 1 426 24 discriminator 2
	movq	-16(%rbp), %rax
	movl	$3, 16(%rax)
	.loc 1 427 15 discriminator 2
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	.loc 1 427 24 discriminator 2
	movl	-36(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rax, %rdx
	.loc 1 427 41 discriminator 2
	movq	-16(%rbp), %rax
	movq	%rax, 176(%rdx)
	.loc 1 428 24 discriminator 2
	movq	-16(%rbp), %rax
	movl	-36(%rbp), %edx
	movl	%edx, 20(%rax)
	.loc 1 429 28 discriminator 2
	movq	-16(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 429 15 discriminator 2
	movl	%eax, -32(%rbp)
	.loc 1 430 15 discriminator 2
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	.loc 1 430 24 discriminator 2
	movl	-36(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rax, %rdx
	.loc 1 430 46 discriminator 2
	movl	-32(%rbp), %eax
	movl	%eax, 64(%rdx)
	.loc 1 432 26 discriminator 2
	movq	-16(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 432 15 discriminator 2
	movl	%eax, -28(%rbp)
	.loc 1 433 15 discriminator 2
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	.loc 1 433 24 discriminator 2
	movl	-36(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rax, %rdx
	.loc 1 433 44 discriminator 2
	movl	-28(%rbp), %eax
	movl	%eax, 68(%rdx)
	.loc 1 437 46 discriminator 2
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	.loc 1 437 55 discriminator 2
	movl	-36(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rdx, %rax
	.loc 1 437 63 discriminator 2
	movl	200(%rax), %edx
	.loc 1 437 14 discriminator 2
	movq	-88(%rbp), %rax
	movq	48(%rax), %rcx
	.loc 1 437 23 discriminator 2
	movl	-36(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rcx, %rax
	.loc 1 437 72 discriminator 2
	orl	$32, %edx
	.loc 1 437 40 discriminator 2
	movl	%edx, 200(%rax)
.LBE10:
	.loc 1 416 35 discriminator 2
	addl	$1, -60(%rbp)
.L33:
	.loc 1 416 22 discriminator 1
	movl	-76(%rbp), %eax
	cmpl	%eax, -60(%rbp)
	jl	.L36
	jmp	.L35
.L43:
.LBB11:
	.loc 1 420 19
	nop
.L35:
.LBE11:
.LBE9:
.LBB12:
	.loc 1 441 16
	movl	$0, -56(%rbp)
	.loc 1 441 7
	jmp	.L37
.L39:
	.loc 1 442 17
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	.loc 1 442 26
	movl	-56(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rdx, %rax
	.loc 1 442 29
	movl	200(%rax), %eax
	.loc 1 442 12
	testl	%eax, %eax
	je	.L38
	.loc 1 444 45
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	.loc 1 444 54
	movl	-56(%rbp), %eax
	cltq
	salq	$10, %rax
	leaq	(%rdx,%rax), %rcx
	.loc 1 444 15
	movq	-88(%rbp), %rax
	movq	48(%rax), %rdx
	.loc 1 444 24
	movl	-56(%rbp), %eax
	cltq
	salq	$10, %rax
	addq	%rdx, %rax
	.loc 1 444 27
	movq	32(%rax), %rdx
	.loc 1 444 35
	movl	-56(%rbp), %eax
	cltq
	salq	$2, %rax
	addq	%rax, %rdx
	.loc 1 444 57
	movl	200(%rcx), %eax
	.loc 1 444 39
	movl	%eax, (%rdx)
.L38:
	.loc 1 441 47 discriminator 2
	addl	$1, -56(%rbp)
.L37:
	.loc 1 441 31 discriminator 1
	movq	-88(%rbp), %rax
	movl	104(%rax), %eax
	.loc 1 441 25 discriminator 1
	cmpl	%eax, -56(%rbp)
	jl	.L39
.LBE12:
	.loc 1 450 10
	movl	$0, %eax
.L40:
	.loc 1 451 1 discriminator 1
	movq	-8(%rbp), %rdx
	subq	%fs:40, %rdx
	je	.L41
	.loc 1 451 1 is_stmt 0
	call	__stack_chk_fail@PLT
.L41:
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
	.loc 1 453 38 is_stmt 1
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$144, %rsp
	movq	%rdi, -136(%rbp)
	.loc 1 453 38
	movq	%fs:40, %rax
	movq	%rax, -8(%rbp)
	xorl	%eax, %eax
	.loc 1 454 7
	movl	$5, -92(%rbp)
	.loc 1 455 7
	movl	$1, -88(%rbp)
	.loc 1 456 7
	movl	$255, -84(%rbp)
	.loc 1 482 5
#APP
# 482 "stream2-workqueue.c" 1
	mov %rsp, %rax
# 0 "" 2
#NO_APP
	movq	%rax, -40(%rbp)
	.loc 1 483 7
	movq	-136(%rbp), %rax
	movq	968(%rax), %rax
	.loc 1 483 24
	movq	-40(%rbp), %rdx
	movq	%rdx, (%rax)
	.loc 1 490 3
	movq	-136(%rbp), %rax
	movq	968(%rax), %rdx
	movq	-136(%rbp), %rax
	movq	960(%rax), %rax
	movl	$3, %esi
	movq	%rax, %rdi
	call	switch_to@PLT
	.loc 1 495 1
	leaq	-32(%rbp), %rax
	movq	%rax, %rsi
	movl	$4, %edi
	call	clock_gettime@PLT
	.loc 1 498 11
	movq	-136(%rbp), %rax
	movl	92(%rax), %eax
	.loc 1 498 6
	cmpl	$2, %eax
	jne	.L45
.LBB13:
	.loc 1 502 13
	movl	$0, -104(%rbp)
	.loc 1 502 4
	jmp	.L46
.L48:
.LBB14:
	.loc 1 504 23
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	.loc 1 504 29
	movq	896(%rax), %rdx
	.loc 1 504 47
	movq	-136(%rbp), %rax
	movl	908(%rax), %eax
	.loc 1 504 58
	sall	$7, %eax
	cltq
	.loc 1 504 42
	salq	$3, %rax
	addq	%rdx, %rax
	movq	(%rax), %rax
	.loc 1 504 65
	movl	-88(%rbp), %edx
	movslq	%edx, %rdi
	cqto
	idivq	%rdi
	movq	%rax, %rdx
	.loc 1 504 80
	movl	-84(%rbp), %eax
	movslq	%eax, %rcx
	movq	%rdx, %rax
	cqto
	idivq	%rcx
	movq	%rdx, %rax
	.loc 1 504 9
	movl	%eax, -100(%rbp)
	.loc 1 507 9
	movq	-136(%rbp), %rax
	movl	384(%rax), %eax
	movl	%eax, -96(%rbp)
	.loc 1 509 19
	movq	-136(%rbp), %rax
	movl	908(%rax), %eax
	.loc 1 509 30
	sall	$24, %eax
	movl	%eax, %edx
	.loc 1 509 47
	movl	-100(%rbp), %eax
	sall	$16, %eax
	.loc 1 509 36
	movl	%edx, %esi
	orl	%eax, %esi
	.loc 1 509 63
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
	.loc 1 509 54
	movl	%esi, %eax
	orl	%ecx, %eax
	.loc 1 509 13
	cltq
	movq	%rax, -72(%rbp)
	.loc 1 534 31
	movq	-136(%rbp), %rax
	movq	48(%rax), %rdx
	.loc 1 534 45
	movq	-136(%rbp), %rax
	movl	100(%rax), %eax
	cltq
	.loc 1 534 40
	salq	$10, %rax
	.loc 1 534 17
	addq	%rdx, %rax
	movq	%rax, -64(%rbp)
	.loc 1 548 11
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	.loc 1 548 17
	movq	112(%rax), %rdx
	.loc 1 548 24
	movq	-72(%rbp), %rax
	addq	%rdx, %rax
	movzbl	(%rax), %eax
	.loc 1 548 6
	cmpb	$-1, %al
	je	.L47
	.loc 1 550 9
	movq	-136(%rbp), %rax
	movq	80(%rax), %rax
	.loc 1 550 22
	leaq	1(%rax), %rdx
	movq	-136(%rbp), %rax
	movq	%rdx, 80(%rax)
.L47:
	.loc 1 552 35 discriminator 2
	movq	-136(%rbp), %rax
	movl	100(%rax), %edx
	.loc 1 552 7 discriminator 2
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	.loc 1 552 13 discriminator 2
	movq	112(%rax), %rcx
	.loc 1 552 20 discriminator 2
	movq	-72(%rbp), %rax
	addq	%rcx, %rax
	.loc 1 552 29 discriminator 2
	movb	%dl, (%rax)
	.loc 1 562 30 discriminator 2
	movq	-136(%rbp), %rax
	movl	384(%rax), %eax
	.loc 1 562 44 discriminator 2
	addl	$1, %eax
	.loc 1 562 49 discriminator 2
	cltd
	idivl	-92(%rbp)
	.loc 1 562 23 discriminator 2
	movq	-136(%rbp), %rax
	movl	%edx, 384(%rax)
.LBE14:
	.loc 1 502 45 discriminator 2
	addl	$1, -104(%rbp)
.L46:
	.loc 1 502 29 discriminator 1
	movq	-136(%rbp), %rax
	movl	104(%rax), %eax
	.loc 1 502 23 discriminator 1
	cmpl	%eax, -104(%rbp)
	jl	.L48
.LBE13:
	.loc 1 566 29
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	.loc 1 566 35
	movq	896(%rax), %rdx
	.loc 1 566 53
	movq	-136(%rbp), %rax
	movl	908(%rax), %eax
	.loc 1 566 64
	sall	$7, %eax
	cltq
	.loc 1 566 48
	salq	$3, %rax
	.loc 1 566 24
	addq	%rdx, %rax
	.loc 1 566 5
	lock addq	$1, (%rax)
.L45:
	.loc 1 570 24
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	.loc 1 570 30
	movq	896(%rax), %rdx
	.loc 1 570 48
	movq	-136(%rbp), %rax
	movl	908(%rax), %eax
	.loc 1 570 59
	sall	$7, %eax
	cltq
	.loc 1 570 43
	salq	$3, %rax
	addq	%rdx, %rax
	movq	(%rax), %rax
	.loc 1 570 66
	movl	-88(%rbp), %edx
	movslq	%edx, %rdi
	.loc 1 570 8
	cqto
	idivq	%rdi
	movq	%rax, -56(%rbp)
	.loc 1 572 24
	movq	-136(%rbp), %rax
	movl	904(%rax), %eax
	cltq
	.loc 1 572 6
	cmpq	%rax, -56(%rbp)
	je	.L49
	.loc 1 574 25
	movq	-136(%rbp), %rax
	movl	$0, 384(%rax)
.L49:
	.loc 1 594 20
	movq	-56(%rbp), %rax
	movl	%eax, %edx
	movq	-136(%rbp), %rax
	movl	%edx, 904(%rax)
	.loc 1 611 24
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	.loc 1 611 30
	movq	896(%rax), %rdx
	.loc 1 611 48
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	.loc 1 611 61
	sall	$7, %eax
	cltq
	.loc 1 611 43
	salq	$3, %rax
	addq	%rdx, %rax
	.loc 1 611 8
	movq	(%rax), %rax
	movq	%rax, -48(%rbp)
	.loc 1 613 11
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	.loc 1 613 28
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	movslq	%eax, %rdx
	.loc 1 613 23
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	.loc 1 613 41
	movl	(%rax), %eax
	cltq
	.loc 1 613 6
	cmpq	%rax, -48(%rbp)
	jg	.L50
	.loc 1 613 61 discriminator 1
	cmpq	$0, -48(%rbp)
	jne	.L51
.L50:
.LBB15:
	.loc 1 614 14
	movl	$0, -108(%rbp)
	.loc 1 614 5
	jmp	.L52
.L59:
.LBB16:
	.loc 1 616 8
	movq	-136(%rbp), %rax
	movq	72(%rax), %rax
	.loc 1 616 14
	leaq	1(%rax), %rdx
	movq	-136(%rbp), %rax
	movq	%rdx, 72(%rax)
	.loc 1 622 31
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	.loc 1 622 48
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	movslq	%eax, %rdx
	.loc 1 622 43
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	.loc 1 622 62
	movl	(%rax), %eax
	.loc 1 622 70
	cltd
	idivl	-88(%rbp)
	.loc 1 622 85
	subl	$1, %eax
	.loc 1 622 90
	cltd
	idivl	-84(%rbp)
	movl	%edx, %eax
	.loc 1 622 17
	cltq
	movq	%rax, -80(%rbp)
	.loc 1 624 16
	cmpq	$0, -80(%rbp)
	jns	.L53
	.loc 1 625 20
	movq	$0, -80(%rbp)
.L53:
	.loc 1 631 22
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	.loc 1 631 39
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	movslq	%eax, %rdx
	.loc 1 631 34
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	.loc 1 631 9
	movl	4(%rax), %eax
	movl	%eax, -116(%rbp)
	.loc 1 633 18
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	.loc 1 633 31
	sall	$24, %eax
	movslq	%eax, %rdx
	.loc 1 633 45
	movq	-80(%rbp), %rax
	salq	$16, %rax
	.loc 1 633 37
	movq	%rdx, %rsi
	orq	%rax, %rsi
	.loc 1 633 61
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
	.loc 1 633 12
	orq	%rsi, %rax
	movq	%rax, -72(%rbp)
	.loc 1 645 9
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	movl	%eax, -112(%rbp)
	.loc 1 668 17
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	.loc 1 668 23
	movq	112(%rax), %rdx
	.loc 1 668 30
	movq	-72(%rbp), %rax
	addq	%rdx, %rax
	movzbl	(%rax), %eax
	.loc 1 668 12
	cmpb	$-1, %al
	je	.L54
	.loc 1 669 15
	movq	-136(%rbp), %rax
	movq	920(%rax), %rax
	.loc 1 669 29
	leaq	1(%rax), %rdx
	movq	-136(%rbp), %rax
	movq	%rdx, 920(%rax)
	.loc 1 671 15
	movq	-136(%rbp), %rax
	movq	40(%rax), %rax
	.loc 1 671 21
	movq	112(%rax), %rdx
	.loc 1 671 28
	movq	-72(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 671 37
	movb	$-1, (%rax)
.L54:
	.loc 1 706 13
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	.loc 1 706 25
	movl	-112(%rbp), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	.loc 1 706 36
	movl	4(%rax), %eax
	.loc 1 706 8
	cmpl	%eax, -92(%rbp)
	jle	.L55
	.loc 1 708 11
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	.loc 1 708 23
	movl	-112(%rbp), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	.loc 1 708 34
	movl	(%rax), %edx
	.loc 1 708 41
	addl	$1, %edx
	movl	%edx, (%rax)
	.loc 1 711 49
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	.loc 1 711 61
	movl	-112(%rbp), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	.loc 1 711 72
	movl	4(%rax), %ecx
	.loc 1 711 11
	movq	-136(%rbp), %rax
	movq	840(%rax), %rsi
	.loc 1 711 23
	movl	-112(%rbp), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rsi, %rax
	.loc 1 711 80
	leal	1(%rcx), %edx
	.loc 1 711 42
	movl	%edx, 4(%rax)
.L55:
	.loc 1 715 13
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	.loc 1 715 25
	movl	-112(%rbp), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	.loc 1 715 36
	movl	4(%rax), %eax
	.loc 1 715 8
	cmpl	%eax, -92(%rbp)
	jne	.L56
	.loc 1 717 31
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	.loc 1 717 44
	leal	1(%rax), %edx
	.loc 1 717 24
	movq	-136(%rbp), %rax
	movl	%edx, 912(%rax)
	.loc 1 719 5
	movq	-136(%rbp), %rax
	movq	840(%rax), %rcx
	.loc 1 719 17
	movl	-112(%rbp), %eax
	movslq	%eax, %rdx
	movq	%rdx, %rax
	addq	%rax, %rax
	addq	%rdx, %rax
	salq	$2, %rax
	addq	%rcx, %rax
	.loc 1 719 36
	movl	$0, 4(%rax)
.L56:
	.loc 1 722 13
	movq	-136(%rbp), %rax
	movl	912(%rax), %edx
	.loc 1 722 33
	movq	-136(%rbp), %rax
	movl	908(%rax), %eax
	.loc 1 722 8
	cmpl	%eax, %edx
	jne	.L57
	.loc 1 723 30
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	.loc 1 723 43
	leal	1(%rax), %edx
	.loc 1 723 24
	movq	-136(%rbp), %rax
	movl	%edx, 912(%rax)
.L57:
	.loc 1 726 13
	movq	-136(%rbp), %rax
	movl	912(%rax), %eax
	.loc 1 726 8
	cmpl	$5, %eax
	jne	.L58
	.loc 1 727 25
	movq	-136(%rbp), %rax
	movl	$1, 912(%rax)
.L58:
.LBE16:
	.loc 1 614 48 discriminator 2
	addl	$1, -108(%rbp)
.L52:
	.loc 1 614 29 discriminator 1
	movq	-136(%rbp), %rax
	movl	104(%rax), %eax
	.loc 1 614 42 discriminator 1
	subl	$1, %eax
	.loc 1 614 23 discriminator 1
	cmpl	%eax, -108(%rbp)
	jl	.L59
.L51:
.LBE15:
	.loc 1 816 1
	nop
	movq	-8(%rbp), %rdx
	subq	%fs:40, %rdx
	je	.L60
	call	__stack_chk_fail@PLT
.L60:
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
	.loc 1 818 26
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -24(%rbp)
	.loc 1 819 16
	movq	-24(%rbp), %rax
	movq	%rax, -8(%rbp)
	.loc 1 820 9
	jmp	.L62
.L63:
	.loc 1 821 5
	.loc 1 822 11
	movq	-8(%rbp), %rax
	movq	72(%rax), %rax
	.loc 1 822 17
	leaq	1(%rax), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, 72(%rax)
.L62:
	.loc 1 820 14
	movq	-8(%rbp), %rax
	movl	92(%rax), %eax
	.loc 1 820 24
	cmpl	$1, %eax
	je	.L63
	.loc 1 825 1
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
	.loc 1 827 25
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$80, %rsp
	movq	%rdi, -72(%rbp)
	.loc 1 832 16
	movq	-72(%rbp), %rax
	movq	%rax, -32(%rbp)
	.loc 1 833 3
	movq	-32(%rbp), %rax
	movl	100(%rax), %eax
	movl	%eax, %esi
	leaq	.LC2(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 836 7
	movl	$0, -56(%rbp)
	.loc 1 837 28
	movq	-32(%rbp), %rax
	movl	100(%rax), %eax
	.loc 1 837 42
	leal	1(%rax), %edx
	.loc 1 837 53
	movq	-32(%rbp), %rax
	movl	104(%rax), %ecx
	.loc 1 837 7
	movl	%edx, %eax
	cltd
	idivl	%ecx
	movl	%edx, -52(%rbp)
	.loc 1 838 7
	movl	$0, -48(%rbp)
	.loc 1 843 33
	movq	-32(%rbp), %rax
	movq	184(%rax), %rax
	.loc 1 843 45
	addq	$1, %rax
	.loc 1 843 22
	movl	$8, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -24(%rbp)
	.loc 1 844 35
	movq	-32(%rbp), %rax
	movl	104(%rax), %eax
	.loc 1 844 24
	cltq
	movl	$4, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -16(%rbp)
	.loc 1 845 35
	movq	-32(%rbp), %rax
	movl	104(%rax), %eax
	.loc 1 845 24
	cltq
	movl	$4, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -8(%rbp)
	.loc 1 848 7
	movl	$0, -44(%rbp)
	.loc 1 849 9
	jmp	.L65
.L66:
	.loc 1 850 13
	movl	$0, -40(%rbp)
	.loc 1 851 13
	movl	$0, -36(%rbp)
	.loc 1 852 10
	movl	$0, -44(%rbp)
	.loc 1 853 5
	movq	-32(%rbp), %rax
	.loc 1 857 7
	movq	-32(%rbp), %rax
	movq	%rax, %rdi
	call	threadwork@PLT
.L65:
	.loc 1 849 14
	movq	-32(%rbp), %rax
	movl	92(%rax), %eax
	.loc 1 849 24
	testl	%eax, %eax
	jg	.L66
	.loc 1 871 4
	movq	-32(%rbp), %rax
	movl	100(%rax), %eax
	movl	%eax, %esi
	leaq	.LC3(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 872 1
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
	.loc 1 874 33
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
	.loc 1 874 33
	movq	%fs:40, %rax
	movq	%rax, -24(%rbp)
	xorl	%eax, %eax
	.loc 1 875 7
	movl	$0, -352(%rbp)
	.loc 1 876 7
	movl	$1, -348(%rbp)
	.loc 1 877 7
	movl	$1, -364(%rbp)
	.loc 1 878 7
	movl	$15, -360(%rbp)
	.loc 1 880 7
	movl	-360(%rbp), %eax
	subl	$1, %eax
	movl	%eax, -356(%rbp)
	.loc 1 881 3
	movl	$8, %esi
	leaq	.LC4(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 882 3
	movl	$4, %esi
	leaq	.LC5(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 883 3
	movl	$32, %esi
	leaq	.LC6(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 884 3
	movl	-360(%rbp), %eax
	movl	%eax, %esi
	leaq	.LC7(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 885 23
	movl	-360(%rbp), %eax
	cltq
	movl	$8, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -232(%rbp)
	.loc 1 886 26
	movl	-360(%rbp), %eax
	cltq
	movl	$56, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -272(%rbp)
	.loc 1 887 23
	movl	-360(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rsi
	movl	$1, %edi
	call	calloc@PLT
	movq	%rax, -264(%rbp)
	.loc 1 889 8
	movq	$0, -256(%rbp)
	.loc 1 890 8
	movl	$4294967295, %eax
	movq	%rax, -248(%rbp)
	.loc 1 891 29
	movl	-364(%rbp), %eax
	cltq
	.loc 1 891 8
	movq	-248(%rbp), %rdx
	imulq	%rdx, %rax
	movq	%rax, -240(%rbp)
	.loc 1 892 26
	movl	-360(%rbp), %eax
	movslq	%eax, %rbx
	movq	-240(%rbp), %rax
	cqto
	idivq	%rbx
	.loc 1 892 7
	movl	%eax, -368(%rbp)
	.loc 1 893 25
	pxor	%xmm0, %xmm0
	cvtsi2sdq	-240(%rbp), %xmm0
	.loc 1 893 45
	pxor	%xmm1, %xmm1
	cvtsi2sdq	-248(%rbp), %xmm1
	.loc 1 893 20
	divsd	%xmm1, %xmm0
	movq	%xmm0, %rax
	movq	%rax, %xmm0
	call	ceil@PLT
	.loc 1 893 8
	cvttsd2siq	%xmm0, %rax
	movq	%rax, -200(%rbp)
	.loc 1 894 17
	movq	-240(%rbp), %rax
	movl	$1, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -192(%rbp)
	.loc 1 895 3
	movq	-240(%rbp), %rdx
	movq	-192(%rbp), %rax
	movl	$-1, %esi
	movq	%rax, %rdi
	call	memset@PLT
	.loc 1 896 3
	movq	-240(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC8(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 897 7
	movl	$0, -300(%rbp)
	.loc 1 898 23
	movl	-360(%rbp), %eax
	cltq
	movl	$4, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -184(%rbp)
	.loc 1 899 24
	movl	-360(%rbp), %eax
	cltq
	movl	$4, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -176(%rbp)
	.loc 1 900 28
	movl	$32, %esi
	movl	$100, %edi
	call	calloc@PLT
	movq	%rax, -168(%rbp)
	.loc 1 902 1
	movq	-256(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC9(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 904 1
	movq	-248(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC10(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 910 7
	movl	$0, -316(%rbp)
	.loc 1 911 50
	movl	-360(%rbp), %eax
	cltq
	movl	$4, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -160(%rbp)
	.loc 1 914 3
	leaq	-288(%rbp), %rax
	movl	$512, %edx
	movl	$128, %esi
	movq	%rax, %rdi
	call	posix_memalign@PLT
	.loc 1 915 32
	movl	-360(%rbp), %eax
	cltq
	movl	$12, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -152(%rbp)
	.loc 1 916 17
	movq	-264(%rbp), %rax
	movq	-192(%rbp), %rdx
	movq	%rdx, 112(%rax)
	.loc 1 917 7
	movl	$100000000, -296(%rbp)
	.loc 1 918 27
	movl	-296(%rbp), %eax
	cltq
	movl	$20, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -144(%rbp)
	.loc 1 919 28
	movl	-296(%rbp), %eax
	cltq
	movl	$20, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	movq	%rax, -136(%rbp)
	.loc 1 921 34
	movl	$8, %esi
	movl	$1, %edi
	call	calloc@PLT
	movq	%rax, -128(%rbp)
.LBB17:
	.loc 1 925 12
	movl	$0, -312(%rbp)
	.loc 1 925 3
	jmp	.L68
.L73:
.LBB18:
	.loc 1 927 30
	movl	$32, %esi
	movl	$10, %edi
	call	calloc@PLT
	movq	%rax, -88(%rbp)
	.loc 1 929 9
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 929 24
	movq	-88(%rbp), %rax
	movq	%rax, 960(%rdx)
.LBB19:
	.loc 1 930 14
	movl	$0, -308(%rbp)
	.loc 1 930 5
	jmp	.L69
.L70:
.LBB20:
	.loc 1 931 39 discriminator 3
	movl	$4, %esi
	movl	$1, %edi
	call	calloc@PLT
	movq	%rax, -72(%rbp)
	.loc 1 932 10 discriminator 3
	movl	-308(%rbp), %eax
	cltq
	salq	$5, %rax
	movq	%rax, %rdx
	movq	-88(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 932 19 discriminator 3
	movq	-72(%rbp), %rax
	movq	%rax, 24(%rdx)
	.loc 1 933 10 discriminator 3
	movl	-308(%rbp), %eax
	cltq
	salq	$5, %rax
	movq	%rax, %rdx
	movq	-88(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 933 20 discriminator 3
	movq	coroutine_func@GOTPCREL(%rip), %rdx
	.loc 1 933 18 discriminator 3
	movq	%rdx, 16(%rax)
.LBE20:
	.loc 1 930 30 discriminator 3
	addl	$1, -308(%rbp)
.L69:
	.loc 1 930 23 discriminator 1
	cmpl	$9, -308(%rbp)
	jle	.L70
.LBE19:
	.loc 1 935 9
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 935 23
	movq	-128(%rbp), %rax
	movq	%rax, 968(%rdx)
	.loc 1 936 9
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 936 19
	movq	-144(%rbp), %rax
	movq	%rax, 928(%rdx)
	.loc 1 937 9
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 937 20
	movq	-136(%rbp), %rax
	movq	%rax, 936(%rdx)
	.loc 1 938 9
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	leaq	(%rdx,%rax), %rbx
	.loc 1 938 23
	movl	$128, %esi
	movl	$1, %edi
	call	calloc@PLT
	.loc 1 938 21
	movq	%rax, 120(%rbx)
.LBB21:
	.loc 1 939 5
	addl	$1, -316(%rbp)
	movl	-316(%rbp), %eax
	cltq
	movq	%rax, -80(%rbp)
	cmpq	$1023, -80(%rbp)
	ja	.L72
	.loc 1 939 5 is_stmt 0 discriminator 1
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
.L72:
.LBE21:
	.loc 1 940 5 is_stmt 1 discriminator 4
	movl	-316(%rbp), %edx
	movl	-312(%rbp), %eax
	movl	%eax, %esi
	leaq	.LC11(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 941 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 941 29 discriminator 4
	movl	-312(%rbp), %eax
	imull	-368(%rbp), %eax
	.loc 1 941 25 discriminator 4
	movl	%eax, 152(%rdx)
	.loc 1 942 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 942 25 discriminator 4
	movq	-288(%rbp), %rax
	movq	%rax, 896(%rdx)
	.loc 1 943 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 943 22 discriminator 4
	movl	-352(%rbp), %eax
	movl	%eax, 128(%rdx)
	.loc 1 944 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 944 21 discriminator 4
	movl	$2, 92(%rax)
	.loc 1 945 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 945 25 discriminator 4
	movl	-312(%rbp), %eax
	movl	%eax, 100(%rdx)
	.loc 1 946 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 946 22 discriminator 4
	movq	-240(%rbp), %rdx
	movl	%edx, 96(%rax)
	.loc 1 948 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 948 24 discriminator 4
	movl	-368(%rbp), %eax
	movl	%eax, 148(%rdx)
	.loc 1 949 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 949 24 discriminator 4
	movl	-360(%rbp), %eax
	movl	%eax, 104(%rdx)
	.loc 1 950 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 950 21 discriminator 4
	movq	-160(%rbp), %rax
	movq	%rax, 32(%rdx)
	.loc 1 951 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 951 12 discriminator 4
	movq	32(%rax), %rdx
	.loc 1 951 20 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$2, %rax
	addq	%rdx, %rax
	.loc 1 951 24 discriminator 4
	movl	$0, (%rax)
	.loc 1 952 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 952 21 discriminator 4
	movl	-368(%rbp), %eax
	movl	%eax, 144(%rdx)
	.loc 1 953 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 953 18 discriminator 4
	movq	-264(%rbp), %rax
	movq	%rax, 40(%rdx)
	.loc 1 954 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 954 21 discriminator 4
	movq	-264(%rbp), %rax
	movq	%rax, 48(%rdx)
	.loc 1 956 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 956 18 discriminator 4
	movq	$0, (%rax)
	.loc 1 957 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 957 19 discriminator 4
	movq	-240(%rbp), %rax
	movq	%rax, 8(%rdx)
	.loc 1 958 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 958 37 discriminator 4
	movl	-360(%rbp), %edx
	subl	$1, %edx
	.loc 1 958 24 discriminator 4
	movl	%edx, 512(%rax)
	.loc 1 959 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 959 25 discriminator 4
	movl	$0, 384(%rax)
	.loc 1 960 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 960 22 discriminator 4
	movq	-168(%rbp), %rax
	movq	%rax, 160(%rdx)
	.loc 1 961 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 961 23 discriminator 4
	movq	-200(%rbp), %rax
	movq	%rax, 192(%rdx)
	.loc 1 962 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 962 23 discriminator 4
	movq	-248(%rbp), %rax
	movq	%rax, 184(%rdx)
	.loc 1 963 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 963 21 discriminator 4
	movl	$0, 200(%rax)
	.loc 1 964 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 964 22 discriminator 4
	movl	-360(%rbp), %eax
	cltq
	movq	%rax, 776(%rdx)
	.loc 1 965 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 965 23 discriminator 4
	movl	-360(%rbp), %eax
	cltq
	movq	%rax, 784(%rdx)
	.loc 1 966 31 discriminator 4
	movl	-312(%rbp), %eax
	leal	3(%rax), %edx
	testl	%eax, %eax
	cmovs	%edx, %eax
	sarl	$2, %eax
	movl	%eax, %edx
	.loc 1 966 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rcx
	movq	-264(%rbp), %rax
	addq	%rcx, %rax
	.loc 1 966 26 discriminator 4
	addl	$1, %edx
	.loc 1 966 22 discriminator 4
	movl	%edx, 908(%rax)
	.loc 1 967 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 967 23 discriminator 4
	movl	-360(%rbp), %eax
	movl	%eax, 808(%rdx)
	.loc 1 968 9 discriminator 4
	movl	$10000000, -292(%rbp)
	.loc 1 969 22 discriminator 4
	movl	-292(%rbp), %eax
	cltq
	.loc 1 969 9 discriminator 4
	movl	-312(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	leaq	(%rcx,%rdx), %rbx
	.loc 1 969 22 discriminator 4
	movl	$48, %esi
	movq	%rax, %rdi
	call	calloc@PLT
	.loc 1 969 20 discriminator 4
	movq	%rax, 792(%rbx)
	.loc 1 970 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 970 24 discriminator 4
	movl	-292(%rbp), %eax
	movl	%eax, 800(%rdx)
	.loc 1 971 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 971 24 discriminator 4
	movq	-152(%rbp), %rax
	movq	%rax, 840(%rdx)
	.loc 1 972 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	leaq	(%rdx,%rax), %rbx
	.loc 1 972 24 discriminator 4
	movl	$48, %esi
	movl	$10000, %edi
	call	calloc@PLT
	.loc 1 972 22 discriminator 4
	movq	%rax, 816(%rbx)
	.loc 1 973 9 discriminator 4
	movl	-312(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 973 24 discriminator 4
	movl	-296(%rbp), %eax
	movl	%eax, 952(%rdx)
.LBE18:
	.loc 1 925 37 discriminator 4
	addl	$1, -312(%rbp)
.L68:
	.loc 1 925 21 discriminator 2
	movl	-312(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L73
.LBE17:
.LBB22:
	.loc 1 976 12
	movl	$0, -304(%rbp)
	.loc 1 976 3
	jmp	.L74
.L75:
	.loc 1 977 53 discriminator 3
	movl	-304(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	.loc 1 977 48 discriminator 3
	movq	-264(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 977 37 discriminator 3
	movl	-304(%rbp), %eax
	movslq	%eax, %rcx
	movq	%rcx, %rax
	salq	$3, %rax
	subq	%rcx, %rax
	salq	$3, %rax
	movq	%rax, %rcx
	.loc 1 977 32 discriminator 3
	movq	-272(%rbp), %rax
	leaq	(%rcx,%rax), %rsi
	.loc 1 977 27 discriminator 3
	movl	-304(%rbp), %eax
	cltq
	leaq	0(,%rax,8), %rcx
	.loc 1 977 5 discriminator 3
	movq	-232(%rbp), %rax
	addq	%rcx, %rax
	movq	%rdx, %rcx
	movq	work@GOTPCREL(%rip), %rdx
	movq	%rax, %rdi
	call	pthread_create@PLT
	.loc 1 978 68 discriminator 3
	movl	-304(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 978 71 discriminator 3
	movq	120(%rax), %rdx
	.loc 1 978 34 discriminator 3
	movl	-304(%rbp), %eax
	cltq
	leaq	0(,%rax,8), %rcx
	movq	-232(%rbp), %rax
	addq	%rcx, %rax
	.loc 1 978 5 discriminator 3
	movq	(%rax), %rax
	movl	$8, %esi
	movq	%rax, %rdi
	call	pthread_setaffinity_np@PLT
	.loc 1 976 37 discriminator 3
	addl	$1, -304(%rbp)
.L74:
	.loc 1 976 21 discriminator 1
	movl	-304(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L75
.LBE22:
	.loc 1 981 19
	movl	-348(%rbp), %eax
	cltq
	movq	%rax, -64(%rbp)
	movq	$0, -56(%rbp)
	.loc 1 985 19
	movq	$0, -48(%rbp)
	movq	$0, -40(%rbp)
	.loc 1 990 3
	leaq	-48(%rbp), %rdx
	leaq	-64(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	nanosleep@PLT
	.loc 1 992 3
	leaq	.LC12(%rip), %rax
	movq	%rax, %rdi
	call	puts@PLT
.LBB23:
	.loc 1 993 12
	movl	$0, -328(%rbp)
	.loc 1 993 3
	jmp	.L76
.L77:
	.loc 1 994 9 discriminator 3
	movl	-328(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 994 12 discriminator 3
	movl	92(%rax), %edx
	.loc 1 994 20 discriminator 3
	subl	$1, %edx
	movl	%edx, 92(%rax)
	.loc 1 993 37 discriminator 3
	addl	$1, -328(%rbp)
.L76:
	.loc 1 993 21 discriminator 1
	movl	-328(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L77
.LBE23:
	.loc 1 998 2
	leaq	.LC13(%rip), %rax
	movq	%rax, %rdi
	call	puts@PLT
.LBB24:
	.loc 1 1001 12
	movl	$0, -324(%rbp)
	.loc 1 1001 3
	jmp	.L78
.L79:
	.loc 1 1002 9 discriminator 3
	movl	-324(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1002 12 discriminator 3
	movl	92(%rax), %edx
	.loc 1 1002 20 discriminator 3
	subl	$1, %edx
	movl	%edx, 92(%rax)
	.loc 1 1001 37 discriminator 3
	addl	$1, -324(%rbp)
.L78:
	.loc 1 1001 21 discriminator 1
	movl	-324(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L79
.LBE24:
.LBB25:
	.loc 1 1006 12
	movl	$0, -320(%rbp)
	.loc 1 1006 3
	jmp	.L80
.L81:
.LBB26:
	.loc 1 1008 24 discriminator 3
	movl	-320(%rbp), %eax
	cltq
	leaq	0(,%rax,8), %rdx
	movq	-232(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1008 5 discriminator 3
	movq	(%rax), %rax
	leaq	-280(%rbp), %rdx
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	pthread_join@PLT
.LBE26:
	.loc 1 1006 36 discriminator 3
	addl	$1, -320(%rbp)
.L80:
	.loc 1 1006 21 discriminator 1
	movl	-320(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L81
.LBE25:
	.loc 1 1010 3
	.loc 1 1011 3
	leaq	.LC14(%rip), %rax
	movq	%rax, %rdi
	call	puts@PLT
	.loc 1 1012 8
	movq	$0, -224(%rbp)
	.loc 1 1013 8
	movq	$1, -120(%rbp)
.LBB27:
	.loc 1 1014 12
	movl	$0, -344(%rbp)
	.loc 1 1014 3
	jmp	.L82
.L83:
	.loc 1 1015 31 discriminator 3
	movl	-344(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1015 5 discriminator 3
	movq	72(%rax), %rax
	movq	%rax, %rsi
	leaq	.LC15(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1016 17 discriminator 3
	movl	-344(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1016 20 discriminator 3
	movq	72(%rax), %rax
	.loc 1 1016 10 discriminator 3
	addq	%rax, -224(%rbp)
	.loc 1 1014 36 discriminator 3
	addl	$1, -344(%rbp)
.L82:
	.loc 1 1014 21 discriminator 1
	movl	-344(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L83
.LBE27:
	.loc 1 1018 3
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
	.loc 1 1019 33
	movq	-224(%rbp), %rax
	imulq	-120(%rbp), %rax
	.loc 1 1019 3
	movl	-348(%rbp), %edx
	movslq	%edx, %rbx
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC17(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1020 51
	movl	-348(%rbp), %eax
	movslq	%eax, %rbx
	movq	-224(%rbp), %rax
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	.loc 1 1020 3
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC18(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1021 62
	movl	-348(%rbp), %eax
	movslq	%eax, %rbx
	movq	-224(%rbp), %rax
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	.loc 1 1021 56
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	.loc 1 1021 3
	cqto
	idivq	-120(%rbp)
	movq	%rax, %rsi
	leaq	.LC19(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1022 50
	movq	-224(%rbp), %rax
	imulq	-120(%rbp), %rax
	.loc 1 1022 57
	movl	-348(%rbp), %edx
	movslq	%edx, %rbx
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	.loc 1 1022 3
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC20(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1024 8
	movq	$0, -216(%rbp)
.LBB28:
	.loc 1 1026 12
	movl	$0, -340(%rbp)
	.loc 1 1026 3
	jmp	.L84
.L85:
	.loc 1 1027 38 discriminator 3
	movl	-340(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1027 5 discriminator 3
	movq	920(%rax), %rax
	movq	%rax, %rsi
	leaq	.LC21(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1028 18 discriminator 3
	movl	-340(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1028 21 discriminator 3
	movq	920(%rax), %rax
	.loc 1 1028 11 discriminator 3
	addq	%rax, -216(%rbp)
	.loc 1 1026 36 discriminator 3
	addl	$1, -340(%rbp)
.L84:
	.loc 1 1026 21 discriminator 1
	movl	-340(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L85
.LBE28:
	.loc 1 1031 8
	movq	$0, -208(%rbp)
.LBB29:
	.loc 1 1033 12
	movl	$0, -336(%rbp)
	.loc 1 1033 3
	jmp	.L86
.L87:
	.loc 1 1034 24 discriminator 3
	movl	-336(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1034 27 discriminator 3
	movq	80(%rax), %rax
	.loc 1 1034 17 discriminator 3
	addq	%rax, -208(%rbp)
	.loc 1 1035 32 discriminator 3
	movl	-336(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1035 5 discriminator 3
	movq	80(%rax), %rax
	movq	%rax, %rsi
	leaq	.LC22(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1033 36 discriminator 3
	addl	$1, -336(%rbp)
.L86:
	.loc 1 1033 21 discriminator 1
	movl	-336(%rbp), %eax
	cmpl	-360(%rbp), %eax
	jl	.L87
.LBE29:
	.loc 1 1037 3
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
	.loc 1 1039 51
	movq	-208(%rbp), %rax
	imulq	-120(%rbp), %rax
	.loc 1 1039 3
	movl	-348(%rbp), %edx
	movslq	%edx, %rbx
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC24(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1040 65
	movl	-348(%rbp), %eax
	movslq	%eax, %rbx
	movq	-208(%rbp), %rax
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	.loc 1 1040 3
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC25(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1041 76
	movl	-348(%rbp), %eax
	movslq	%eax, %rbx
	movq	-208(%rbp), %rax
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	.loc 1 1041 62
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	.loc 1 1041 3
	cqto
	idivq	-120(%rbp)
	movq	%rax, %rsi
	leaq	.LC26(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1042 65
	movq	-208(%rbp), %rax
	imulq	-120(%rbp), %rax
	.loc 1 1042 74
	movl	-348(%rbp), %edx
	movslq	%edx, %rbx
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	.loc 1 1042 3
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC27(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1055 3
	leaq	.LC28(%rip), %rax
	movq	%rax, %rdi
	call	puts@PLT
.LBB30:
	.loc 1 1056 12
	movl	$0, -332(%rbp)
	.loc 1 1056 3
	jmp	.L88
.L89:
	.loc 1 1057 24 discriminator 3
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1057 32 discriminator 3
	movq	240(%rax), %rax
	.loc 1 1057 47 discriminator 3
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	.loc 1 1057 57 discriminator 3
	movq	224(%rdx), %rdx
	.loc 1 1057 4 discriminator 3
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1058 25 discriminator 3
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1058 35 discriminator 3
	movq	256(%rax), %rax
	.loc 1 1058 50 discriminator 3
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	.loc 1 1058 60 discriminator 3
	movq	224(%rdx), %rdx
	.loc 1 1058 5 discriminator 3
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1059 25 discriminator 3
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1059 33 discriminator 3
	movq	240(%rax), %rax
	.loc 1 1059 48 discriminator 3
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	.loc 1 1059 58 discriminator 3
	movq	256(%rdx), %rdx
	.loc 1 1059 5 discriminator 3
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1060 25 discriminator 3
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1060 36 discriminator 3
	movq	288(%rax), %rax
	.loc 1 1060 51 discriminator 3
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	.loc 1 1060 60 discriminator 3
	movq	272(%rdx), %rdx
	.loc 1 1060 5 discriminator 3
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1061 25 discriminator 3
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1061 34 discriminator 3
	movq	272(%rax), %rax
	.loc 1 1061 49 discriminator 3
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	.loc 1 1061 60 discriminator 3
	movq	288(%rdx), %rdx
	.loc 1 1061 5 discriminator 3
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1062 25 discriminator 3
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1062 34 discriminator 3
	movq	272(%rax), %rax
	.loc 1 1062 49 discriminator 3
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	.loc 1 1062 59 discriminator 3
	movq	256(%rdx), %rdx
	.loc 1 1062 5 discriminator 3
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1063 28 discriminator 3
	movl	-332(%rbp), %eax
	cltq
	salq	$10, %rax
	movq	%rax, %rdx
	movq	-264(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 1063 37 discriminator 3
	movq	320(%rax), %rax
	.loc 1 1063 52 discriminator 3
	movl	-332(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rdx, %rcx
	salq	$10, %rcx
	movq	-264(%rbp), %rdx
	addq	%rcx, %rdx
	.loc 1 1063 63 discriminator 3
	movq	304(%rdx), %rdx
	.loc 1 1063 5 discriminator 3
	subq	%rdx, %rax
	movq	%rax, %rsi
	leaq	.LC29(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1056 29 discriminator 3
	addl	$1, -332(%rbp)
.L88:
	.loc 1 1056 21 discriminator 1
	cmpl	$0, -332(%rbp)
	jle	.L89
.LBE30:
	.loc 1 1065 3
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
	.loc 1 1066 69
	movl	-348(%rbp), %eax
	movslq	%eax, %rbx
	movq	-216(%rbp), %rax
	cqto
	idivq	%rbx
	movq	%rax, %rbx
	.loc 1 1066 3
	movl	$1000000000, %eax
	cqto
	idivq	%rbx
	movq	%rax, %rsi
	leaq	.LC31(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 1124 21
	movl	$1, %esi
	movl	$100, %edi
	call	calloc@PLT
	movq	%rax, -112(%rbp)
	.loc 1 1125 16
	movl	$1, %esi
	movl	$1000, %edi
	call	calloc@PLT
	movq	%rax, -104(%rbp)
	.loc 1 1126 3
	movq	-112(%rbp), %rax
	movl	$100, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	.loc 1 1127 3
	movq	-112(%rbp), %rax
	leaq	.LC32(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	.loc 1 1128 20
	movq	-112(%rbp), %rax
	leaq	.LC33(%rip), %rdx
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fopen@PLT
	movq	%rax, -96(%rbp)
	.loc 1 1130 1
	movq	-104(%rbp), %rax
	movl	$1000, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	.loc 1 1131 3
	movq	-104(%rbp), %rax
	movl	$0, %ecx
	leaq	.LC34(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	.loc 1 1132 3
	movq	-96(%rbp), %rdx
	movq	-104(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fputs@PLT
	.loc 1 1134 3
	movq	-104(%rbp), %rax
	movl	$1000, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	.loc 1 1135 3
	movq	-104(%rbp), %rax
	movl	$8, %ecx
	leaq	.LC35(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	.loc 1 1136 3
	movq	-96(%rbp), %rdx
	movq	-104(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fputs@PLT
	.loc 1 1138 3
	movq	-104(%rbp), %rax
	movl	$1000, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	.loc 1 1139 3
	movq	-104(%rbp), %rax
	movl	$16, %ecx
	leaq	.LC36(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	.loc 1 1140 3
	movq	-96(%rbp), %rdx
	movq	-104(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fputs@PLT
	.loc 1 1143 3
	movq	-104(%rbp), %rax
	movl	$1000, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	.loc 1 1144 3
	movq	-104(%rbp), %rax
	movl	$24, %ecx
	leaq	.LC37(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	.loc 1 1145 3
	movq	-96(%rbp), %rdx
	movq	-104(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fputs@PLT
	.loc 1 1147 3
	movq	-104(%rbp), %rax
	movl	$1000, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	.loc 1 1148 3
	movq	-104(%rbp), %rax
	movl	$0, %ecx
	leaq	.LC38(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	.loc 1 1149 3
	movq	-96(%rbp), %rdx
	movq	-104(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fputs@PLT
	.loc 1 1151 3
	movq	-104(%rbp), %rax
	movl	$1000, %edx
	movl	$0, %esi
	movq	%rax, %rdi
	call	memset@PLT
	.loc 1 1152 3
	movq	-104(%rbp), %rax
	movl	$32, %ecx
	leaq	.LC39(%rip), %rdx
	movl	$100, %esi
	movq	%rax, %rdi
	movl	$0, %eax
	call	snprintf@PLT
	.loc 1 1153 3
	movq	-96(%rbp), %rdx
	movq	-104(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	fputs@PLT
	.loc 1 1155 3
	movq	-96(%rbp), %rax
	movq	%rax, %rdi
	call	fclose@PLT
	movl	$0, %eax
	.loc 1 1156 1
	movq	-24(%rbp), %rdx
	subq	%fs:40, %rdx
	je	.L91
	call	__stack_chk_fail@PLT
.L91:
	movq	-8(%rbp), %rbx
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE16:
	.size	main, .-main
.Letext0:
	.file 2 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/bits/types.h"
	.file 3 "/nix/store/1gf2flfqnpqbr1b4p4qz2f72y42bs56r-gcc-11.3.0/lib/gcc/x86_64-unknown-linux-gnu/11.3.0/include/stddef.h"
	.file 4 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/bits/types/struct_timespec.h"
	.file 5 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/bits/cpu-set.h"
	.file 6 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/bits/types/clockid_t.h"
	.file 7 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/bits/pthreadtypes.h"
	.file 8 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/bits/types/struct_FILE.h"
	.file 9 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/bits/types/FILE.h"
	.file 10 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/bits/stdint-uintn.h"
	.file 11 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/stdio.h"
	.file 12 "/nix/store/1gf2flfqnpqbr1b4p4qz2f72y42bs56r-gcc-11.3.0/lib/gcc/x86_64-unknown-linux-gnu/11.3.0/include-fixed/pthread.h"
	.file 13 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/time.h"
	.file 14 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/stdlib.h"
	.file 15 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/string.h"
	.file 16 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/bits/mathcalls.h"
	.section	.debug_info,"",@progbits
.Ldebug_info0:
	.long	0x180c
	.value	0x5
	.byte	0x1
	.byte	0x8
	.long	.Ldebug_abbrev0
	.uleb128 0x23
	.long	.LASF222
	.byte	0x1d
	.long	.LASF0
	.long	.LASF1
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.long	.Ldebug_line0
	.uleb128 0xa
	.byte	0x8
	.byte	0x7
	.long	.LASF2
	.uleb128 0xa
	.byte	0x4
	.byte	0x7
	.long	.LASF3
	.uleb128 0x24
	.byte	0x8
	.uleb128 0x17
	.long	0x3c
	.uleb128 0x5
	.long	0x48
	.uleb128 0xa
	.byte	0x1
	.byte	0x6
	.long	.LASF4
	.uleb128 0x18
	.long	0x48
	.uleb128 0x25
	.byte	0x4
	.byte	0x5
	.string	"int"
	.uleb128 0xa
	.byte	0x1
	.byte	0x8
	.long	.LASF5
	.uleb128 0xa
	.byte	0x2
	.byte	0x7
	.long	.LASF6
	.uleb128 0xa
	.byte	0x1
	.byte	0x6
	.long	.LASF7
	.uleb128 0xa
	.byte	0x2
	.byte	0x5
	.long	.LASF8
	.uleb128 0xa
	.byte	0x8
	.byte	0x5
	.long	.LASF9
	.uleb128 0x8
	.long	.LASF10
	.byte	0x2
	.byte	0x2d
	.byte	0x1b
	.long	0x2e
	.uleb128 0x8
	.long	.LASF11
	.byte	0x2
	.byte	0x98
	.byte	0x19
	.long	0x77
	.uleb128 0x8
	.long	.LASF12
	.byte	0x2
	.byte	0x99
	.byte	0x1b
	.long	0x77
	.uleb128 0x8
	.long	.LASF13
	.byte	0x2
	.byte	0xa0
	.byte	0x1a
	.long	0x77
	.uleb128 0x8
	.long	.LASF14
	.byte	0x2
	.byte	0xa9
	.byte	0x1d
	.long	0x54
	.uleb128 0x8
	.long	.LASF15
	.byte	0x2
	.byte	0xc5
	.byte	0x21
	.long	0x77
	.uleb128 0x8
	.long	.LASF16
	.byte	0x3
	.byte	0xd1
	.byte	0x17
	.long	0x2e
	.uleb128 0xe
	.long	.LASF29
	.byte	0x10
	.byte	0x4
	.byte	0xb
	.long	0xf9
	.uleb128 0x1
	.long	.LASF17
	.byte	0x4
	.byte	0x10
	.byte	0xc
	.long	0xa2
	.byte	0
	.uleb128 0x1
	.long	.LASF18
	.byte	0x4
	.byte	0x15
	.byte	0x15
	.long	0xba
	.byte	0x8
	.byte	0
	.uleb128 0x18
	.long	0xd2
	.uleb128 0x8
	.long	.LASF19
	.byte	0x5
	.byte	0x20
	.byte	0x19
	.long	0x2e
	.uleb128 0x26
	.byte	0x80
	.byte	0x5
	.byte	0x27
	.byte	0x9
	.long	0x121
	.uleb128 0x1
	.long	.LASF20
	.byte	0x5
	.byte	0x29
	.byte	0xe
	.long	0x121
	.byte	0
	.byte	0
	.uleb128 0x19
	.long	0xfe
	.long	0x131
	.uleb128 0x1a
	.long	0x2e
	.byte	0xf
	.byte	0
	.uleb128 0x8
	.long	.LASF21
	.byte	0x5
	.byte	0x2a
	.byte	0x3
	.long	0x10a
	.uleb128 0x18
	.long	0x131
	.uleb128 0x5
	.long	0x4f
	.uleb128 0x17
	.long	0x142
	.uleb128 0x8
	.long	.LASF22
	.byte	0x6
	.byte	0x7
	.byte	0x15
	.long	0xae
	.uleb128 0xa
	.byte	0x8
	.byte	0x7
	.long	.LASF23
	.uleb128 0x8
	.long	.LASF24
	.byte	0x7
	.byte	0x1b
	.byte	0x1b
	.long	0x2e
	.uleb128 0x27
	.long	.LASF27
	.byte	0x38
	.byte	0x7
	.byte	0x38
	.byte	0x7
	.long	0x18f
	.uleb128 0x1d
	.long	.LASF25
	.byte	0x3a
	.byte	0x8
	.long	0x18f
	.uleb128 0x1d
	.long	.LASF26
	.byte	0x3b
	.byte	0xc
	.long	0x77
	.byte	0
	.uleb128 0x19
	.long	0x48
	.long	0x19f
	.uleb128 0x1a
	.long	0x2e
	.byte	0x37
	.byte	0
	.uleb128 0x8
	.long	.LASF27
	.byte	0x7
	.byte	0x3e
	.byte	0x1e
	.long	0x16b
	.uleb128 0x18
	.long	0x19f
	.uleb128 0xa
	.byte	0x8
	.byte	0x5
	.long	.LASF28
	.uleb128 0xe
	.long	.LASF30
	.byte	0xd8
	.byte	0x8
	.byte	0x31
	.long	0x33d
	.uleb128 0x1
	.long	.LASF31
	.byte	0x8
	.byte	0x33
	.byte	0x7
	.long	0x54
	.byte	0
	.uleb128 0x1
	.long	.LASF32
	.byte	0x8
	.byte	0x36
	.byte	0x9
	.long	0x43
	.byte	0x8
	.uleb128 0x1
	.long	.LASF33
	.byte	0x8
	.byte	0x37
	.byte	0x9
	.long	0x43
	.byte	0x10
	.uleb128 0x1
	.long	.LASF34
	.byte	0x8
	.byte	0x38
	.byte	0x9
	.long	0x43
	.byte	0x18
	.uleb128 0x1
	.long	.LASF35
	.byte	0x8
	.byte	0x39
	.byte	0x9
	.long	0x43
	.byte	0x20
	.uleb128 0x1
	.long	.LASF36
	.byte	0x8
	.byte	0x3a
	.byte	0x9
	.long	0x43
	.byte	0x28
	.uleb128 0x1
	.long	.LASF37
	.byte	0x8
	.byte	0x3b
	.byte	0x9
	.long	0x43
	.byte	0x30
	.uleb128 0x1
	.long	.LASF38
	.byte	0x8
	.byte	0x3c
	.byte	0x9
	.long	0x43
	.byte	0x38
	.uleb128 0x1
	.long	.LASF39
	.byte	0x8
	.byte	0x3d
	.byte	0x9
	.long	0x43
	.byte	0x40
	.uleb128 0x1
	.long	.LASF40
	.byte	0x8
	.byte	0x40
	.byte	0x9
	.long	0x43
	.byte	0x48
	.uleb128 0x1
	.long	.LASF41
	.byte	0x8
	.byte	0x41
	.byte	0x9
	.long	0x43
	.byte	0x50
	.uleb128 0x1
	.long	.LASF42
	.byte	0x8
	.byte	0x42
	.byte	0x9
	.long	0x43
	.byte	0x58
	.uleb128 0x1
	.long	.LASF43
	.byte	0x8
	.byte	0x44
	.byte	0x16
	.long	0x356
	.byte	0x60
	.uleb128 0x1
	.long	.LASF44
	.byte	0x8
	.byte	0x46
	.byte	0x14
	.long	0x35b
	.byte	0x68
	.uleb128 0x1
	.long	.LASF45
	.byte	0x8
	.byte	0x48
	.byte	0x7
	.long	0x54
	.byte	0x70
	.uleb128 0x1
	.long	.LASF46
	.byte	0x8
	.byte	0x49
	.byte	0x7
	.long	0x54
	.byte	0x74
	.uleb128 0x1
	.long	.LASF47
	.byte	0x8
	.byte	0x4a
	.byte	0xb
	.long	0x8a
	.byte	0x78
	.uleb128 0x1
	.long	.LASF48
	.byte	0x8
	.byte	0x4d
	.byte	0x12
	.long	0x62
	.byte	0x80
	.uleb128 0x1
	.long	.LASF49
	.byte	0x8
	.byte	0x4e
	.byte	0xf
	.long	0x69
	.byte	0x82
	.uleb128 0x1
	.long	.LASF50
	.byte	0x8
	.byte	0x4f
	.byte	0x8
	.long	0x360
	.byte	0x83
	.uleb128 0x1
	.long	.LASF51
	.byte	0x8
	.byte	0x51
	.byte	0xf
	.long	0x370
	.byte	0x88
	.uleb128 0x1
	.long	.LASF52
	.byte	0x8
	.byte	0x59
	.byte	0xd
	.long	0x96
	.byte	0x90
	.uleb128 0x1
	.long	.LASF53
	.byte	0x8
	.byte	0x5b
	.byte	0x17
	.long	0x37a
	.byte	0x98
	.uleb128 0x1
	.long	.LASF54
	.byte	0x8
	.byte	0x5c
	.byte	0x19
	.long	0x384
	.byte	0xa0
	.uleb128 0x1
	.long	.LASF55
	.byte	0x8
	.byte	0x5d
	.byte	0x14
	.long	0x35b
	.byte	0xa8
	.uleb128 0x1
	.long	.LASF56
	.byte	0x8
	.byte	0x5e
	.byte	0x9
	.long	0x3c
	.byte	0xb0
	.uleb128 0x1
	.long	.LASF57
	.byte	0x8
	.byte	0x5f
	.byte	0xa
	.long	0xc6
	.byte	0xb8
	.uleb128 0x1
	.long	.LASF58
	.byte	0x8
	.byte	0x60
	.byte	0x7
	.long	0x54
	.byte	0xc0
	.uleb128 0x1
	.long	.LASF59
	.byte	0x8
	.byte	0x62
	.byte	0x8
	.long	0x389
	.byte	0xc4
	.byte	0
	.uleb128 0x8
	.long	.LASF60
	.byte	0x9
	.byte	0x7
	.byte	0x19
	.long	0x1b7
	.uleb128 0x28
	.long	.LASF223
	.byte	0x8
	.byte	0x2b
	.byte	0xe
	.uleb128 0x1c
	.long	.LASF61
	.uleb128 0x5
	.long	0x351
	.uleb128 0x5
	.long	0x1b7
	.uleb128 0x19
	.long	0x48
	.long	0x370
	.uleb128 0x1a
	.long	0x2e
	.byte	0
	.byte	0
	.uleb128 0x5
	.long	0x349
	.uleb128 0x1c
	.long	.LASF62
	.uleb128 0x5
	.long	0x375
	.uleb128 0x1c
	.long	.LASF63
	.uleb128 0x5
	.long	0x37f
	.uleb128 0x19
	.long	0x48
	.long	0x399
	.uleb128 0x1a
	.long	0x2e
	.byte	0x13
	.byte	0
	.uleb128 0x5
	.long	0x33d
	.uleb128 0xa
	.byte	0x4
	.byte	0x4
	.long	.LASF64
	.uleb128 0xa
	.byte	0x8
	.byte	0x4
	.long	.LASF65
	.uleb128 0x5
	.long	0x43
	.uleb128 0xa
	.byte	0x10
	.byte	0x4
	.long	.LASF66
	.uleb128 0x8
	.long	.LASF67
	.byte	0xa
	.byte	0x1b
	.byte	0x14
	.long	0x7e
	.uleb128 0xe
	.long	.LASF68
	.byte	0xc
	.byte	0x1
	.byte	0x17
	.long	0x3f8
	.uleb128 0x1
	.long	.LASF69
	.byte	0x1
	.byte	0x18
	.byte	0x7
	.long	0x54
	.byte	0
	.uleb128 0x1
	.long	.LASF70
	.byte	0x1
	.byte	0x19
	.byte	0x7
	.long	0x54
	.byte	0x4
	.uleb128 0x1
	.long	.LASF71
	.byte	0x1
	.byte	0x1a
	.byte	0x7
	.long	0x54
	.byte	0x8
	.byte	0
	.uleb128 0xe
	.long	.LASF72
	.byte	0x14
	.byte	0x1
	.byte	0x1d
	.long	0x445
	.uleb128 0x1
	.long	.LASF73
	.byte	0x1
	.byte	0x1e
	.byte	0x7
	.long	0x54
	.byte	0
	.uleb128 0x1
	.long	.LASF69
	.byte	0x1
	.byte	0x1f
	.byte	0x7
	.long	0x54
	.byte	0x4
	.uleb128 0x1
	.long	.LASF70
	.byte	0x1
	.byte	0x20
	.byte	0x7
	.long	0x54
	.byte	0x8
	.uleb128 0x1
	.long	.LASF71
	.byte	0x1
	.byte	0x21
	.byte	0x7
	.long	0x54
	.byte	0xc
	.uleb128 0x11
	.string	"set"
	.byte	0x22
	.byte	0x7
	.long	0x54
	.byte	0x10
	.byte	0
	.uleb128 0xe
	.long	.LASF74
	.byte	0x4
	.byte	0x1
	.byte	0x25
	.long	0x45f
	.uleb128 0x1
	.long	.LASF75
	.byte	0x1
	.byte	0x26
	.byte	0x7
	.long	0x54
	.byte	0
	.byte	0
	.uleb128 0xe
	.long	.LASF76
	.byte	0x8
	.byte	0x1
	.byte	0x29
	.long	0x478
	.uleb128 0x11
	.string	"rsp"
	.byte	0x2a
	.byte	0xc
	.long	0x3b8
	.byte	0
	.byte	0
	.uleb128 0xe
	.long	.LASF77
	.byte	0x20
	.byte	0x1
	.byte	0x2d
	.long	0x4b7
	.uleb128 0x1
	.long	.LASF78
	.byte	0x1
	.byte	0x2e
	.byte	0x7
	.long	0x54
	.byte	0
	.uleb128 0x11
	.string	"rsp"
	.byte	0x2f
	.byte	0xc
	.long	0x3b8
	.byte	0x8
	.uleb128 0x11
	.string	"eip"
	.byte	0x30
	.byte	0xc
	.long	0x3b8
	.byte	0x10
	.uleb128 0x1
	.long	.LASF79
	.byte	0x1
	.byte	0x31
	.byte	0x1a
	.long	0x4b7
	.byte	0x18
	.byte	0
	.uleb128 0x5
	.long	0x445
	.uleb128 0xe
	.long	.LASF80
	.byte	0x30
	.byte	0x1
	.byte	0x35
	.long	0x523
	.uleb128 0x1
	.long	.LASF71
	.byte	0x1
	.byte	0x36
	.byte	0x7
	.long	0x54
	.byte	0
	.uleb128 0x1
	.long	.LASF81
	.byte	0x1
	.byte	0x37
	.byte	0x13
	.long	0xd2
	.byte	0x8
	.uleb128 0x1
	.long	.LASF82
	.byte	0x1
	.byte	0x38
	.byte	0x8
	.long	0x77
	.byte	0x18
	.uleb128 0x1
	.long	.LASF83
	.byte	0x1
	.byte	0x39
	.byte	0x7
	.long	0x54
	.byte	0x20
	.uleb128 0x11
	.string	"set"
	.byte	0x3a
	.byte	0x7
	.long	0x54
	.byte	0x24
	.uleb128 0x1
	.long	.LASF84
	.byte	0x1
	.byte	0x3b
	.byte	0x7
	.long	0x54
	.byte	0x28
	.uleb128 0x1
	.long	.LASF73
	.byte	0x1
	.byte	0x3c
	.byte	0x7
	.long	0x54
	.byte	0x2c
	.byte	0
	.uleb128 0xe
	.long	.LASF85
	.byte	0x38
	.byte	0x1
	.byte	0x57
	.long	0x571
	.uleb128 0x1
	.long	.LASF86
	.byte	0x1
	.byte	0x58
	.byte	0x7
	.long	0x54
	.byte	0
	.uleb128 0x1
	.long	.LASF87
	.byte	0x1
	.byte	0x59
	.byte	0x7
	.long	0x54
	.byte	0x4
	.uleb128 0x1
	.long	.LASF88
	.byte	0x1
	.byte	0x5a
	.byte	0x13
	.long	0xd2
	.byte	0x8
	.uleb128 0x1
	.long	.LASF89
	.byte	0x1
	.byte	0x5b
	.byte	0x13
	.long	0xd2
	.byte	0x18
	.uleb128 0x1
	.long	.LASF90
	.byte	0x1
	.byte	0x5c
	.byte	0x13
	.long	0xd2
	.byte	0x28
	.byte	0
	.uleb128 0xe
	.long	.LASF91
	.byte	0x20
	.byte	0x1
	.byte	0x5e
	.long	0x5be
	.uleb128 0x1
	.long	.LASF92
	.byte	0x1
	.byte	0x5f
	.byte	0x8
	.long	0x77
	.byte	0
	.uleb128 0x11
	.string	"end"
	.byte	0x60
	.byte	0x8
	.long	0x77
	.byte	0x8
	.uleb128 0x1
	.long	.LASF87
	.byte	0x1
	.byte	0x61
	.byte	0x7
	.long	0x54
	.byte	0x10
	.uleb128 0x1
	.long	.LASF93
	.byte	0x1
	.byte	0x62
	.byte	0x7
	.long	0x54
	.byte	0x14
	.uleb128 0x1
	.long	.LASF78
	.byte	0x1
	.byte	0x63
	.byte	0x7
	.long	0x54
	.byte	0x18
	.byte	0
	.uleb128 0x29
	.long	.LASF224
	.value	0x400
	.byte	0x80
	.byte	0x1
	.byte	0x70
	.byte	0x8
	.long	0x982
	.uleb128 0x1
	.long	.LASF89
	.byte	0x1
	.byte	0x73
	.byte	0x8
	.long	0x77
	.byte	0
	.uleb128 0x1
	.long	.LASF94
	.byte	0x1
	.byte	0x74
	.byte	0x8
	.long	0x77
	.byte	0x8
	.uleb128 0x1
	.long	.LASF87
	.byte	0x1
	.byte	0x75
	.byte	0x7
	.long	0x54
	.byte	0x10
	.uleb128 0x1
	.long	.LASF92
	.byte	0x1
	.byte	0x76
	.byte	0x7
	.long	0x54
	.byte	0x14
	.uleb128 0x11
	.string	"end"
	.byte	0x77
	.byte	0x7
	.long	0x54
	.byte	0x18
	.uleb128 0x1
	.long	.LASF95
	.byte	0x1
	.byte	0x78
	.byte	0x9
	.long	0x982
	.byte	0x20
	.uleb128 0x1
	.long	.LASF96
	.byte	0x1
	.byte	0x79
	.byte	0x10
	.long	0x987
	.byte	0x28
	.uleb128 0x1
	.long	.LASF97
	.byte	0x1
	.byte	0x7a
	.byte	0x10
	.long	0x987
	.byte	0x30
	.uleb128 0x1
	.long	.LASF98
	.byte	0x1
	.byte	0x7b
	.byte	0x10
	.long	0x98c
	.byte	0x38
	.uleb128 0x1
	.long	.LASF99
	.byte	0x1
	.byte	0x7c
	.byte	0x7
	.long	0x54
	.byte	0x40
	.uleb128 0x1
	.long	.LASF100
	.byte	0x1
	.byte	0x7d
	.byte	0x7
	.long	0x54
	.byte	0x44
	.uleb128 0x1
	.long	.LASF101
	.byte	0x1
	.byte	0x7e
	.byte	0x8
	.long	0x77
	.byte	0x48
	.uleb128 0x1
	.long	.LASF102
	.byte	0x1
	.byte	0x7f
	.byte	0x8
	.long	0x77
	.byte	0x50
	.uleb128 0x1
	.long	.LASF86
	.byte	0x1
	.byte	0x80
	.byte	0x7
	.long	0x54
	.byte	0x58
	.uleb128 0x1
	.long	.LASF75
	.byte	0x1
	.byte	0x83
	.byte	0x7
	.long	0x54
	.byte	0x5c
	.uleb128 0x1
	.long	.LASF103
	.byte	0x1
	.byte	0x84
	.byte	0x7
	.long	0x54
	.byte	0x60
	.uleb128 0x1
	.long	.LASF104
	.byte	0x1
	.byte	0x85
	.byte	0x7
	.long	0x54
	.byte	0x64
	.uleb128 0x1
	.long	.LASF105
	.byte	0x1
	.byte	0x86
	.byte	0x7
	.long	0x54
	.byte	0x68
	.uleb128 0x1
	.long	.LASF106
	.byte	0x1
	.byte	0x87
	.byte	0x9
	.long	0x43
	.byte	0x70
	.uleb128 0x1
	.long	.LASF107
	.byte	0x1
	.byte	0x88
	.byte	0xe
	.long	0x991
	.byte	0x78
	.uleb128 0x1
	.long	.LASF108
	.byte	0x1
	.byte	0x89
	.byte	0x7
	.long	0x54
	.byte	0x80
	.uleb128 0x1
	.long	.LASF109
	.byte	0x1
	.byte	0x8a
	.byte	0x8
	.long	0x982
	.byte	0x88
	.uleb128 0x1
	.long	.LASF110
	.byte	0x1
	.byte	0x8b
	.byte	0x7
	.long	0x54
	.byte	0x90
	.uleb128 0x1
	.long	.LASF111
	.byte	0x1
	.byte	0x8c
	.byte	0x7
	.long	0x54
	.byte	0x94
	.uleb128 0x1
	.long	.LASF112
	.byte	0x1
	.byte	0x8d
	.byte	0x7
	.long	0x54
	.byte	0x98
	.uleb128 0x1
	.long	.LASF113
	.byte	0x1
	.byte	0x8f
	.byte	0x11
	.long	0x996
	.byte	0xa0
	.uleb128 0x1
	.long	.LASF114
	.byte	0x1
	.byte	0x90
	.byte	0x11
	.long	0x996
	.byte	0xa8
	.uleb128 0x1
	.long	.LASF115
	.byte	0x1
	.byte	0x91
	.byte	0x11
	.long	0x996
	.byte	0xb0
	.uleb128 0x1
	.long	.LASF116
	.byte	0x1
	.byte	0x93
	.byte	0x8
	.long	0x77
	.byte	0xb8
	.uleb128 0x1
	.long	.LASF117
	.byte	0x1
	.byte	0x94
	.byte	0x8
	.long	0x77
	.byte	0xc0
	.uleb128 0x1
	.long	.LASF118
	.byte	0x1
	.byte	0x95
	.byte	0x7
	.long	0x54
	.byte	0xc8
	.uleb128 0x1
	.long	.LASF119
	.byte	0x1
	.byte	0x96
	.byte	0x8
	.long	0x77
	.byte	0xd0
	.uleb128 0x1
	.long	.LASF120
	.byte	0x1
	.byte	0x97
	.byte	0x13
	.long	0xd2
	.byte	0xd8
	.uleb128 0x1
	.long	.LASF121
	.byte	0x1
	.byte	0x98
	.byte	0x13
	.long	0xd2
	.byte	0xe8
	.uleb128 0x1
	.long	.LASF122
	.byte	0x1
	.byte	0x99
	.byte	0x13
	.long	0xd2
	.byte	0xf8
	.uleb128 0x3
	.long	.LASF123
	.byte	0x9a
	.byte	0x13
	.long	0xd2
	.value	0x108
	.uleb128 0x3
	.long	.LASF124
	.byte	0x9b
	.byte	0x13
	.long	0xd2
	.value	0x118
	.uleb128 0x3
	.long	.LASF125
	.byte	0x9c
	.byte	0x13
	.long	0xd2
	.value	0x128
	.uleb128 0x3
	.long	.LASF126
	.byte	0x9d
	.byte	0x13
	.long	0xd2
	.value	0x138
	.uleb128 0x14
	.long	.LASF128
	.byte	0x9e
	.byte	0x7
	.long	0x54
	.value	0x180
	.uleb128 0x3
	.long	.LASF127
	.byte	0x9f
	.byte	0x7
	.long	0x54
	.value	0x184
	.uleb128 0x14
	.long	.LASF129
	.byte	0xa0
	.byte	0x7
	.long	0x54
	.value	0x200
	.uleb128 0x3
	.long	.LASF130
	.byte	0xa1
	.byte	0x7
	.long	0x54
	.value	0x204
	.uleb128 0x3
	.long	.LASF131
	.byte	0xa2
	.byte	0x7
	.long	0x54
	.value	0x208
	.uleb128 0x3
	.long	.LASF132
	.byte	0xa3
	.byte	0x7
	.long	0x54
	.value	0x20c
	.uleb128 0x3
	.long	.LASF133
	.byte	0xa4
	.byte	0x7
	.long	0x54
	.value	0x210
	.uleb128 0x3
	.long	.LASF134
	.byte	0xa5
	.byte	0x7
	.long	0x54
	.value	0x214
	.uleb128 0x3
	.long	.LASF135
	.byte	0xa6
	.byte	0x9
	.long	0x982
	.value	0x218
	.uleb128 0x3
	.long	.LASF136
	.byte	0xa7
	.byte	0x9
	.long	0x982
	.value	0x220
	.uleb128 0x14
	.long	.LASF137
	.byte	0xa8
	.byte	0x8
	.long	0x77
	.value	0x280
	.uleb128 0x14
	.long	.LASF138
	.byte	0xa9
	.byte	0x8
	.long	0x77
	.value	0x300
	.uleb128 0x3
	.long	.LASF139
	.byte	0xaa
	.byte	0x8
	.long	0x77
	.value	0x308
	.uleb128 0x3
	.long	.LASF140
	.byte	0xab
	.byte	0x8
	.long	0x77
	.value	0x310
	.uleb128 0x3
	.long	.LASF141
	.byte	0xac
	.byte	0x12
	.long	0x99b
	.value	0x318
	.uleb128 0x3
	.long	.LASF142
	.byte	0xad
	.byte	0x7
	.long	0x54
	.value	0x320
	.uleb128 0x3
	.long	.LASF143
	.byte	0xae
	.byte	0x7
	.long	0x54
	.value	0x324
	.uleb128 0x3
	.long	.LASF144
	.byte	0xaf
	.byte	0x7
	.long	0x54
	.value	0x328
	.uleb128 0x3
	.long	.LASF145
	.byte	0xb0
	.byte	0x12
	.long	0x99b
	.value	0x330
	.uleb128 0x3
	.long	.LASF146
	.byte	0xb1
	.byte	0x8
	.long	0x77
	.value	0x338
	.uleb128 0x3
	.long	.LASF147
	.byte	0xb2
	.byte	0x8
	.long	0x77
	.value	0x340
	.uleb128 0x3
	.long	.LASF148
	.byte	0xb3
	.byte	0x13
	.long	0x9a0
	.value	0x348
	.uleb128 0x14
	.long	.LASF149
	.byte	0xb4
	.byte	0xa
	.long	0x9a5
	.value	0x380
	.uleb128 0x3
	.long	.LASF150
	.byte	0xb5
	.byte	0x7
	.long	0x54
	.value	0x388
	.uleb128 0x3
	.long	.LASF151
	.byte	0xb6
	.byte	0x7
	.long	0x54
	.value	0x38c
	.uleb128 0x3
	.long	.LASF152
	.byte	0xb7
	.byte	0x7
	.long	0x54
	.value	0x390
	.uleb128 0x3
	.long	.LASF153
	.byte	0xb8
	.byte	0x8
	.long	0x77
	.value	0x398
	.uleb128 0x3
	.long	.LASF154
	.byte	0xb9
	.byte	0x13
	.long	0x9aa
	.value	0x3a0
	.uleb128 0x3
	.long	.LASF155
	.byte	0xba
	.byte	0x13
	.long	0x9aa
	.value	0x3a8
	.uleb128 0x3
	.long	.LASF156
	.byte	0xbb
	.byte	0x7
	.long	0x54
	.value	0x3b0
	.uleb128 0x3
	.long	.LASF157
	.byte	0xbc
	.byte	0x7
	.long	0x54
	.value	0x3b4
	.uleb128 0x3
	.long	.LASF158
	.byte	0xbd
	.byte	0x7
	.long	0x54
	.value	0x3b8
	.uleb128 0x3
	.long	.LASF159
	.byte	0xbe
	.byte	0x16
	.long	0x9af
	.value	0x3c0
	.uleb128 0x3
	.long	.LASF160
	.byte	0xbf
	.byte	0x16
	.long	0x9b4
	.value	0x3c8
	.byte	0
	.uleb128 0x5
	.long	0x54
	.uleb128 0x5
	.long	0x5be
	.uleb128 0x5
	.long	0x523
	.uleb128 0x5
	.long	0x131
	.uleb128 0x5
	.long	0x571
	.uleb128 0x5
	.long	0x4bc
	.uleb128 0x5
	.long	0x3c4
	.uleb128 0x5
	.long	0x77
	.uleb128 0x5
	.long	0x3f8
	.uleb128 0x5
	.long	0x478
	.uleb128 0x5
	.long	0x45f
	.uleb128 0x13
	.long	.LASF161
	.byte	0xb
	.byte	0xb2
	.byte	0xc
	.long	0x54
	.long	0x9cf
	.uleb128 0x4
	.long	0x399
	.byte	0
	.uleb128 0x10
	.long	.LASF162
	.byte	0xb
	.value	0x102
	.byte	0xe
	.long	0x399
	.long	0x9eb
	.uleb128 0x4
	.long	0x147
	.uleb128 0x4
	.long	0x147
	.byte	0
	.uleb128 0x10
	.long	.LASF163
	.byte	0xb
	.value	0x17a
	.byte	0xc
	.long	0x54
	.long	0xa0d
	.uleb128 0x4
	.long	0x43
	.uleb128 0x4
	.long	0xc6
	.uleb128 0x4
	.long	0x142
	.uleb128 0x1e
	.byte	0
	.uleb128 0x13
	.long	.LASF164
	.byte	0xc
	.byte	0xe4
	.byte	0xc
	.long	0x54
	.long	0xa28
	.uleb128 0x4
	.long	0x15f
	.uleb128 0x4
	.long	0xa28
	.byte	0
	.uleb128 0x5
	.long	0x3c
	.uleb128 0x10
	.long	.LASF165
	.byte	0xd
	.value	0x110
	.byte	0xc
	.long	0x54
	.long	0xa49
	.uleb128 0x4
	.long	0xa49
	.uleb128 0x4
	.long	0xa4e
	.byte	0
	.uleb128 0x5
	.long	0xf9
	.uleb128 0x5
	.long	0xd2
	.uleb128 0x10
	.long	.LASF166
	.byte	0xc
	.value	0x1f2
	.byte	0xc
	.long	0x54
	.long	0xa74
	.uleb128 0x4
	.long	0x15f
	.uleb128 0x4
	.long	0xc6
	.uleb128 0x4
	.long	0xa74
	.byte	0
	.uleb128 0x5
	.long	0x13d
	.uleb128 0x13
	.long	.LASF167
	.byte	0xc
	.byte	0xd3
	.byte	0xc
	.long	0x54
	.long	0xa9e
	.uleb128 0x4
	.long	0xaa3
	.uleb128 0x4
	.long	0xaad
	.uleb128 0x4
	.long	0xab2
	.uleb128 0x4
	.long	0x3e
	.byte	0
	.uleb128 0x5
	.long	0x15f
	.uleb128 0x17
	.long	0xa9e
	.uleb128 0x5
	.long	0x1ab
	.uleb128 0x17
	.long	0xaa8
	.uleb128 0x5
	.long	0xab7
	.uleb128 0x2a
	.long	0x3c
	.long	0xac6
	.uleb128 0x4
	.long	0x3c
	.byte	0
	.uleb128 0x10
	.long	.LASF168
	.byte	0xe
	.value	0x24a
	.byte	0xc
	.long	0x54
	.long	0xae7
	.uleb128 0x4
	.long	0xa28
	.uleb128 0x4
	.long	0xc6
	.uleb128 0x4
	.long	0xc6
	.byte	0
	.uleb128 0x13
	.long	.LASF169
	.byte	0xf
	.byte	0x3d
	.byte	0xe
	.long	0x3c
	.long	0xb07
	.uleb128 0x4
	.long	0x3c
	.uleb128 0x4
	.long	0x54
	.uleb128 0x4
	.long	0xc6
	.byte	0
	.uleb128 0x13
	.long	.LASF170
	.byte	0x10
	.byte	0x9f
	.byte	0x1
	.long	0x3a5
	.long	0xb1d
	.uleb128 0x4
	.long	0x3a5
	.byte	0
	.uleb128 0x10
	.long	.LASF171
	.byte	0xe
	.value	0x21f
	.byte	0xe
	.long	0x3c
	.long	0xb39
	.uleb128 0x4
	.long	0xc6
	.uleb128 0x4
	.long	0xc6
	.byte	0
	.uleb128 0x13
	.long	.LASF172
	.byte	0x1
	.byte	0x34
	.byte	0xc
	.long	0x54
	.long	0xb59
	.uleb128 0x4
	.long	0x9af
	.uleb128 0x4
	.long	0x54
	.uleb128 0x4
	.long	0x9b4
	.byte	0
	.uleb128 0x10
	.long	.LASF173
	.byte	0xd
	.value	0x117
	.byte	0xc
	.long	0x54
	.long	0xb75
	.uleb128 0x4
	.long	0x14c
	.uleb128 0x4
	.long	0xa4e
	.byte	0
	.uleb128 0x10
	.long	.LASF174
	.byte	0xb
	.value	0x164
	.byte	0xc
	.long	0x54
	.long	0xb8d
	.uleb128 0x4
	.long	0x142
	.uleb128 0x1e
	.byte	0
	.uleb128 0x15
	.long	.LASF96
	.value	0x36a
	.byte	0x5
	.long	0x54
	.quad	.LFB16
	.quad	.LFE16-.LFB16
	.uleb128 0x1
	.byte	0x9c
	.long	0x10bb
	.uleb128 0x7
	.long	.LASF175
	.value	0x36a
	.byte	0xe
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -388
	.uleb128 0x7
	.long	.LASF176
	.value	0x36a
	.byte	0x1b
	.long	0x3ac
	.uleb128 0x3
	.byte	0x91
	.sleb128 -400
	.uleb128 0x2
	.long	.LASF177
	.value	0x36b
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -368
	.uleb128 0x2
	.long	.LASF178
	.value	0x36c
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -364
	.uleb128 0x2
	.long	.LASF179
	.value	0x36d
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -380
	.uleb128 0x2
	.long	.LASF105
	.value	0x36e
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -376
	.uleb128 0x2
	.long	.LASF180
	.value	0x370
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -372
	.uleb128 0x2
	.long	.LASF71
	.value	0x375
	.byte	0xe
	.long	0xa9e
	.uleb128 0x3
	.byte	0x91
	.sleb128 -248
	.uleb128 0x2
	.long	.LASF181
	.value	0x376
	.byte	0x13
	.long	0x10bb
	.uleb128 0x3
	.byte	0x91
	.sleb128 -288
	.uleb128 0x2
	.long	.LASF79
	.value	0x377
	.byte	0x10
	.long	0x987
	.uleb128 0x3
	.byte	0x91
	.sleb128 -280
	.uleb128 0x2
	.long	.LASF182
	.value	0x379
	.byte	0x8
	.long	0x77
	.uleb128 0x3
	.byte	0x91
	.sleb128 -272
	.uleb128 0x2
	.long	.LASF116
	.value	0x37a
	.byte	0x8
	.long	0x77
	.uleb128 0x3
	.byte	0x91
	.sleb128 -264
	.uleb128 0x2
	.long	.LASF103
	.value	0x37b
	.byte	0x8
	.long	0x77
	.uleb128 0x3
	.byte	0x91
	.sleb128 -256
	.uleb128 0x2
	.long	.LASF110
	.value	0x37c
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -384
	.uleb128 0x2
	.long	.LASF117
	.value	0x37d
	.byte	0x8
	.long	0x77
	.uleb128 0x3
	.byte	0x91
	.sleb128 -216
	.uleb128 0x2
	.long	.LASF106
	.value	0x37e
	.byte	0x9
	.long	0x43
	.uleb128 0x3
	.byte	0x91
	.sleb128 -208
	.uleb128 0x2
	.long	.LASF183
	.value	0x381
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -316
	.uleb128 0x2
	.long	.LASF135
	.value	0x382
	.byte	0x9
	.long	0x982
	.uleb128 0x3
	.byte	0x91
	.sleb128 -200
	.uleb128 0x2
	.long	.LASF136
	.value	0x383
	.byte	0x9
	.long	0x982
	.uleb128 0x3
	.byte	0x91
	.sleb128 -192
	.uleb128 0x2
	.long	.LASF113
	.value	0x384
	.byte	0x11
	.long	0x996
	.uleb128 0x3
	.byte	0x91
	.sleb128 -184
	.uleb128 0x6
	.string	"cpu"
	.value	0x38e
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -332
	.uleb128 0x2b
	.long	.LASF95
	.byte	0x1
	.value	0x38f
	.byte	0x9
	.long	0x982
	.byte	0x80
	.uleb128 0x3
	.byte	0x91
	.sleb128 -176
	.uleb128 0x2
	.long	.LASF149
	.value	0x391
	.byte	0xa
	.long	0x9a5
	.uleb128 0x3
	.byte	0x91
	.sleb128 -304
	.uleb128 0x2
	.long	.LASF148
	.value	0x393
	.byte	0x13
	.long	0x9a0
	.uleb128 0x3
	.byte	0x91
	.sleb128 -168
	.uleb128 0x2
	.long	.LASF158
	.value	0x395
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -312
	.uleb128 0x2
	.long	.LASF154
	.value	0x396
	.byte	0x13
	.long	0x9aa
	.uleb128 0x3
	.byte	0x91
	.sleb128 -160
	.uleb128 0x2
	.long	.LASF155
	.value	0x397
	.byte	0x13
	.long	0x9aa
	.uleb128 0x3
	.byte	0x91
	.sleb128 -152
	.uleb128 0x2
	.long	.LASF160
	.value	0x399
	.byte	0x16
	.long	0x9b4
	.uleb128 0x3
	.byte	0x91
	.sleb128 -144
	.uleb128 0x2
	.long	.LASF81
	.value	0x3d5
	.byte	0x13
	.long	0xd2
	.uleb128 0x3
	.byte	0x91
	.sleb128 -80
	.uleb128 0x6
	.string	"rem"
	.value	0x3d9
	.byte	0x13
	.long	0xd2
	.uleb128 0x2
	.byte	0x91
	.sleb128 -64
	.uleb128 0x2
	.long	.LASF101
	.value	0x3f4
	.byte	0x8
	.long	0x77
	.uleb128 0x3
	.byte	0x91
	.sleb128 -240
	.uleb128 0x2
	.long	.LASF184
	.value	0x3f5
	.byte	0x8
	.long	0x77
	.uleb128 0x3
	.byte	0x91
	.sleb128 -136
	.uleb128 0x2
	.long	.LASF185
	.value	0x400
	.byte	0x8
	.long	0x77
	.uleb128 0x3
	.byte	0x91
	.sleb128 -232
	.uleb128 0x2
	.long	.LASF102
	.value	0x407
	.byte	0x8
	.long	0x77
	.uleb128 0x3
	.byte	0x91
	.sleb128 -224
	.uleb128 0x2
	.long	.LASF186
	.value	0x464
	.byte	0xa
	.long	0x43
	.uleb128 0x3
	.byte	0x91
	.sleb128 -128
	.uleb128 0x6
	.string	"buf"
	.value	0x465
	.byte	0xa
	.long	0x43
	.uleb128 0x3
	.byte	0x91
	.sleb128 -120
	.uleb128 0x2
	.long	.LASF187
	.value	0x468
	.byte	0x9
	.long	0x399
	.uleb128 0x3
	.byte	0x91
	.sleb128 -112
	.uleb128 0xb
	.quad	.LBB17
	.quad	.LBE17-.LBB17
	.long	0xebe
	.uleb128 0x6
	.string	"x"
	.value	0x39d
	.byte	0xc
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -328
	.uleb128 0xd
	.quad	.LBB18
	.quad	.LBE18-.LBB18
	.uleb128 0x6
	.string	"cos"
	.value	0x39f
	.byte	0x18
	.long	0x9af
	.uleb128 0x3
	.byte	0x91
	.sleb128 -104
	.uleb128 0x2
	.long	.LASF141
	.value	0x3c8
	.byte	0x9
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -308
	.uleb128 0xb
	.quad	.LBB19
	.quad	.LBE19-.LBB19
	.long	0xe9a
	.uleb128 0x6
	.string	"y"
	.value	0x3a2
	.byte	0xe
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -324
	.uleb128 0xd
	.quad	.LBB20
	.quad	.LBE20-.LBB20
	.uleb128 0x2
	.long	.LASF188
	.value	0x3a3
	.byte	0x1e
	.long	0x4b7
	.uleb128 0x3
	.byte	0x91
	.sleb128 -88
	.byte	0
	.byte	0
	.uleb128 0xd
	.quad	.LBB21
	.quad	.LBE21-.LBB21
	.uleb128 0x2
	.long	.LASF189
	.value	0x3ab
	.byte	0x5
	.long	0xc6
	.uleb128 0x3
	.byte	0x91
	.sleb128 -96
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0xb
	.quad	.LBB22
	.quad	.LBE22-.LBB22
	.long	0xee2
	.uleb128 0x6
	.string	"x"
	.value	0x3d0
	.byte	0xc
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -320
	.byte	0
	.uleb128 0xb
	.quad	.LBB23
	.quad	.LBE23-.LBB23
	.long	0xf06
	.uleb128 0x6
	.string	"x"
	.value	0x3e1
	.byte	0xc
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -344
	.byte	0
	.uleb128 0xb
	.quad	.LBB24
	.quad	.LBE24-.LBB24
	.long	0xf2a
	.uleb128 0x6
	.string	"x"
	.value	0x3e9
	.byte	0xc
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -340
	.byte	0
	.uleb128 0xb
	.quad	.LBB25
	.quad	.LBE25-.LBB25
	.long	0xf70
	.uleb128 0x6
	.string	"x"
	.value	0x3ee
	.byte	0xc
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -336
	.uleb128 0xd
	.quad	.LBB26
	.quad	.LBE26-.LBB26
	.uleb128 0x6
	.string	"res"
	.value	0x3ef
	.byte	0xb
	.long	0x3c
	.uleb128 0x3
	.byte	0x91
	.sleb128 -296
	.byte	0
	.byte	0
	.uleb128 0xb
	.quad	.LBB27
	.quad	.LBE27-.LBB27
	.long	0xf94
	.uleb128 0x6
	.string	"x"
	.value	0x3f6
	.byte	0xc
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -360
	.byte	0
	.uleb128 0xb
	.quad	.LBB28
	.quad	.LBE28-.LBB28
	.long	0xfb8
	.uleb128 0x6
	.string	"x"
	.value	0x402
	.byte	0xc
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -356
	.byte	0
	.uleb128 0xb
	.quad	.LBB29
	.quad	.LBE29-.LBB29
	.long	0xfdc
	.uleb128 0x6
	.string	"x"
	.value	0x409
	.byte	0xc
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -352
	.byte	0
	.uleb128 0xb
	.quad	.LBB30
	.quad	.LBE30-.LBB30
	.long	0x1000
	.uleb128 0x6
	.string	"x"
	.value	0x420
	.byte	0xc
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -348
	.byte	0
	.uleb128 0x16
	.long	0x1050
	.uleb128 0x9
	.long	.LASF186
	.value	0x42d
	.byte	0xa
	.long	0x43
	.uleb128 0x12
	.string	"buf"
	.value	0x42e
	.byte	0xa
	.long	0x43
	.uleb128 0x9
	.long	.LASF187
	.value	0x431
	.byte	0x9
	.long	0x399
	.uleb128 0xf
	.uleb128 0x12
	.string	"x"
	.value	0x433
	.byte	0xc
	.long	0x54
	.uleb128 0xf
	.uleb128 0x12
	.string	"y"
	.value	0x434
	.byte	0xe
	.long	0x54
	.uleb128 0xf
	.uleb128 0x9
	.long	.LASF190
	.value	0x435
	.byte	0x16
	.long	0x99b
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0xf
	.uleb128 0x9
	.long	.LASF186
	.value	0x448
	.byte	0xb
	.long	0x43
	.uleb128 0x12
	.string	"buf"
	.value	0x449
	.byte	0xa
	.long	0x43
	.uleb128 0x9
	.long	.LASF187
	.value	0x44c
	.byte	0x9
	.long	0x399
	.uleb128 0xf
	.uleb128 0x12
	.string	"x"
	.value	0x44e
	.byte	0xf
	.long	0x54
	.uleb128 0x16
	.long	0x109e
	.uleb128 0x12
	.string	"y"
	.value	0x44f
	.byte	0xe
	.long	0x54
	.uleb128 0xf
	.uleb128 0x9
	.long	.LASF191
	.value	0x450
	.byte	0x17
	.long	0x9aa
	.byte	0
	.byte	0
	.uleb128 0xf
	.uleb128 0x12
	.string	"y"
	.value	0x457
	.byte	0x11
	.long	0x54
	.uleb128 0xf
	.uleb128 0x9
	.long	.LASF191
	.value	0x458
	.byte	0x17
	.long	0x9aa
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x5
	.long	0x19f
	.uleb128 0x15
	.long	.LASF192
	.value	0x33b
	.byte	0x8
	.long	0x3c
	.quad	.LFB15
	.quad	.LFE15-.LFB15
	.uleb128 0x1
	.byte	0x9c
	.long	0x118b
	.uleb128 0x1f
	.string	"arg"
	.value	0x33b
	.byte	0x14
	.long	0x3c
	.uleb128 0x3
	.byte	0x91
	.sleb128 -88
	.uleb128 0x2
	.long	.LASF193
	.value	0x33e
	.byte	0x7
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0x2
	.long	.LASF194
	.value	0x33f
	.byte	0x7
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -52
	.uleb128 0x2
	.long	.LASF79
	.value	0x340
	.byte	0x10
	.long	0x987
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0x2
	.long	.LASF195
	.value	0x344
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -72
	.uleb128 0x2
	.long	.LASF196
	.value	0x345
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -68
	.uleb128 0x2
	.long	.LASF197
	.value	0x346
	.byte	0x7
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -64
	.uleb128 0x2
	.long	.LASF87
	.value	0x34b
	.byte	0xa
	.long	0x9a5
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x2
	.long	.LASF198
	.value	0x34c
	.byte	0x9
	.long	0x982
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.uleb128 0x2
	.long	.LASF199
	.value	0x34d
	.byte	0x9
	.long	0x982
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0x2
	.long	.LASF200
	.value	0x350
	.byte	0x7
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -60
	.byte	0
	.uleb128 0x20
	.long	.LASF201
	.value	0x332
	.byte	0x8
	.long	0x3c
	.quad	.LFB14
	.quad	.LFE14-.LFB14
	.uleb128 0x1
	.byte	0x9c
	.long	0x11cc
	.uleb128 0x1f
	.string	"arg"
	.value	0x332
	.byte	0x15
	.long	0x3c
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x2
	.long	.LASF79
	.value	0x333
	.byte	0x10
	.long	0x987
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.uleb128 0x15
	.long	.LASF202
	.value	0x1c5
	.byte	0x7
	.long	0x982
	.quad	.LFB13
	.quad	.LFE13-.LFB13
	.uleb128 0x1
	.byte	0x9c
	.long	0x13ae
	.uleb128 0x7
	.long	.LASF79
	.value	0x1c5
	.byte	0x20
	.long	0x987
	.uleb128 0x3
	.byte	0x91
	.sleb128 -152
	.uleb128 0x2
	.long	.LASF203
	.value	0x1c6
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -108
	.uleb128 0x2
	.long	.LASF204
	.value	0x1c7
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -104
	.uleb128 0x2
	.long	.LASF205
	.value	0x1c8
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -100
	.uleb128 0x2
	.long	.LASF81
	.value	0x1d8
	.byte	0x13
	.long	0xd2
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0x2
	.long	.LASF82
	.value	0x1da
	.byte	0x8
	.long	0x77
	.uleb128 0x3
	.byte	0x91
	.sleb128 -88
	.uleb128 0x6
	.string	"rsp"
	.value	0x1e1
	.byte	0xe
	.long	0x3b8
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0x2
	.long	.LASF206
	.value	0x23a
	.byte	0x8
	.long	0x77
	.uleb128 0x3
	.byte	0x91
	.sleb128 -72
	.uleb128 0x2
	.long	.LASF144
	.value	0x263
	.byte	0x8
	.long	0x77
	.uleb128 0x2
	.byte	0x91
	.sleb128 -64
	.uleb128 0xb
	.quad	.LBB13
	.quad	.LBE13-.LBB13
	.long	0x1301
	.uleb128 0x6
	.string	"x"
	.value	0x1f6
	.byte	0xd
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -120
	.uleb128 0xd
	.quad	.LBB14
	.quad	.LBE14-.LBB14
	.uleb128 0x2
	.long	.LASF69
	.value	0x1f8
	.byte	0x9
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -116
	.uleb128 0x2
	.long	.LASF70
	.value	0x1fb
	.byte	0x9
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -112
	.uleb128 0x2
	.long	.LASF71
	.value	0x216
	.byte	0x11
	.long	0x987
	.uleb128 0x3
	.byte	0x91
	.sleb128 -80
	.uleb128 0x16
	.long	0x12f1
	.uleb128 0x9
	.long	.LASF191
	.value	0x200
	.byte	0x11
	.long	0x9aa
	.byte	0
	.uleb128 0xf
	.uleb128 0x9
	.long	.LASF190
	.value	0x21a
	.byte	0x18
	.long	0x99b
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x16
	.long	0x131f
	.uleb128 0x9
	.long	.LASF71
	.value	0x248
	.byte	0x1c
	.long	0x987
	.uleb128 0x9
	.long	.LASF190
	.value	0x249
	.byte	0x18
	.long	0x99b
	.byte	0
	.uleb128 0xd
	.quad	.LBB15
	.quad	.LBE15-.LBB15
	.uleb128 0x6
	.string	"x"
	.value	0x266
	.byte	0xe
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -124
	.uleb128 0xd
	.quad	.LBB16
	.quad	.LBE16-.LBB16
	.uleb128 0x2
	.long	.LASF207
	.value	0x26e
	.byte	0x11
	.long	0x77
	.uleb128 0x3
	.byte	0x91
	.sleb128 -96
	.uleb128 0x2
	.long	.LASF70
	.value	0x277
	.byte	0x9
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -132
	.uleb128 0x2
	.long	.LASF208
	.value	0x285
	.byte	0x9
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -128
	.uleb128 0x16
	.long	0x1391
	.uleb128 0x9
	.long	.LASF191
	.value	0x27c
	.byte	0x15
	.long	0x9aa
	.byte	0
	.uleb128 0xf
	.uleb128 0x9
	.long	.LASF71
	.value	0x28d
	.byte	0xf
	.long	0x987
	.uleb128 0x9
	.long	.LASF190
	.value	0x28e
	.byte	0x18
	.long	0x99b
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x15
	.long	.LASF209
	.value	0x167
	.byte	0x5
	.long	0x54
	.quad	.LFB12
	.quad	.LFE12-.LFB12
	.uleb128 0x1
	.byte	0x9c
	.long	0x154d
	.uleb128 0x7
	.long	.LASF79
	.value	0x167
	.byte	0x1f
	.long	0x987
	.uleb128 0x3
	.byte	0x91
	.sleb128 -104
	.uleb128 0x7
	.long	.LASF87
	.value	0x167
	.byte	0x2c
	.long	0x9a5
	.uleb128 0x3
	.byte	0x91
	.sleb128 -112
	.uleb128 0x7
	.long	.LASF198
	.value	0x167
	.byte	0x3d
	.long	0x982
	.uleb128 0x3
	.byte	0x91
	.sleb128 -120
	.uleb128 0x7
	.long	.LASF199
	.value	0x167
	.byte	0x51
	.long	0x982
	.uleb128 0x3
	.byte	0x91
	.sleb128 -128
	.uleb128 0x2
	.long	.LASF194
	.value	0x169
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -96
	.uleb128 0x2
	.long	.LASF193
	.value	0x16a
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -92
	.uleb128 0x2
	.long	.LASF210
	.value	0x16b
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -88
	.uleb128 0x2
	.long	.LASF211
	.value	0x176
	.byte	0x7
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -68
	.uleb128 0x2
	.long	.LASF212
	.value	0x183
	.byte	0xb
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -84
	.uleb128 0xb
	.quad	.LBB6
	.quad	.LBE6-.LBB6
	.long	0x14c6
	.uleb128 0x6
	.string	"x"
	.value	0x185
	.byte	0x12
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -80
	.uleb128 0x21
	.long	.LLRL0
	.uleb128 0x2
	.long	.LASF71
	.value	0x18a
	.byte	0xf
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -64
	.uleb128 0x2
	.long	.LASF213
	.value	0x18c
	.byte	0x19
	.long	0x996
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x2
	.long	.LASF92
	.value	0x194
	.byte	0xf
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -60
	.uleb128 0x6
	.string	"end"
	.value	0x197
	.byte	0xf
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.byte	0
	.byte	0
	.uleb128 0xb
	.quad	.LBB9
	.quad	.LBE9-.LBB9
	.long	0x152c
	.uleb128 0x6
	.string	"x"
	.value	0x1a0
	.byte	0xd
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -76
	.uleb128 0x21
	.long	.LLRL1
	.uleb128 0x2
	.long	.LASF71
	.value	0x1a6
	.byte	0xf
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -52
	.uleb128 0x2
	.long	.LASF213
	.value	0x1a8
	.byte	0x15
	.long	0x996
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.uleb128 0x2
	.long	.LASF92
	.value	0x1ad
	.byte	0xf
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0x6
	.string	"end"
	.value	0x1b0
	.byte	0xf
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -44
	.byte	0
	.byte	0
	.uleb128 0xd
	.quad	.LBB12
	.quad	.LBE12-.LBB12
	.uleb128 0x6
	.string	"x"
	.value	0x1b9
	.byte	0x10
	.long	0x54
	.uleb128 0x3
	.byte	0x91
	.sleb128 -72
	.byte	0
	.byte	0
	.uleb128 0x15
	.long	.LASF214
	.value	0x129
	.byte	0x5
	.long	0x54
	.quad	.LFB11
	.quad	.LFE11-.LFB11
	.uleb128 0x1
	.byte	0x9c
	.long	0x15ed
	.uleb128 0x7
	.long	.LASF79
	.value	0x129
	.byte	0x20
	.long	0x987
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0x7
	.long	.LASF87
	.value	0x129
	.byte	0x2d
	.long	0x9a5
	.uleb128 0x2
	.byte	0x91
	.sleb128 -64
	.uleb128 0x7
	.long	.LASF198
	.value	0x129
	.byte	0x3e
	.long	0x982
	.uleb128 0x3
	.byte	0x91
	.sleb128 -72
	.uleb128 0x7
	.long	.LASF199
	.value	0x129
	.byte	0x52
	.long	0x982
	.uleb128 0x3
	.byte	0x91
	.sleb128 -80
	.uleb128 0x2
	.long	.LASF215
	.value	0x12a
	.byte	0x7
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -36
	.uleb128 0xd
	.quad	.LBB5
	.quad	.LBE5-.LBB5
	.uleb128 0x2
	.long	.LASF71
	.value	0x14e
	.byte	0x17
	.long	0x987
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.uleb128 0x2
	.long	.LASF190
	.value	0x14f
	.byte	0x18
	.long	0x99b
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.byte	0
	.uleb128 0x20
	.long	.LASF216
	.value	0x100
	.byte	0x5
	.long	0x54
	.quad	.LFB10
	.quad	.LFE10-.LFB10
	.uleb128 0x1
	.byte	0x9c
	.long	0x165b
	.uleb128 0x7
	.long	.LASF79
	.value	0x100
	.byte	0x20
	.long	0x987
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x7
	.long	.LASF87
	.value	0x100
	.byte	0x2d
	.long	0x9a5
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0x7
	.long	.LASF198
	.value	0x100
	.byte	0x3e
	.long	0x982
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0x7
	.long	.LASF199
	.value	0x100
	.byte	0x52
	.long	0x982
	.uleb128 0x2
	.byte	0x91
	.sleb128 -64
	.uleb128 0x2
	.long	.LASF215
	.value	0x101
	.byte	0x7
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -20
	.byte	0
	.uleb128 0x22
	.long	.LASF217
	.byte	0xea
	.long	0x54
	.quad	.LFB9
	.quad	.LFE9-.LFB9
	.uleb128 0x1
	.byte	0x9c
	.long	0x16e1
	.uleb128 0xc
	.long	.LASF79
	.byte	0xea
	.byte	0x21
	.long	0x987
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0xc
	.long	.LASF87
	.byte	0xea
	.byte	0x2e
	.long	0x9a5
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0xc
	.long	.LASF210
	.byte	0xea
	.byte	0x3f
	.long	0x982
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0xc
	.long	.LASF198
	.byte	0xea
	.byte	0x53
	.long	0x982
	.uleb128 0x2
	.byte	0x91
	.sleb128 -64
	.uleb128 0xc
	.long	.LASF199
	.byte	0xea
	.byte	0x67
	.long	0x982
	.uleb128 0x3
	.byte	0x91
	.sleb128 -72
	.uleb128 0xd
	.quad	.LBB4
	.quad	.LBE4-.LBB4
	.uleb128 0x1b
	.string	"x"
	.byte	0xeb
	.byte	0xc
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -20
	.byte	0
	.byte	0
	.uleb128 0x22
	.long	.LASF218
	.byte	0xcf
	.long	0x54
	.quad	.LFB8
	.quad	.LFE8-.LFB8
	.uleb128 0x1
	.byte	0x9c
	.long	0x17a4
	.uleb128 0xc
	.long	.LASF79
	.byte	0xcf
	.byte	0x1f
	.long	0x987
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0xc
	.long	.LASF198
	.byte	0xcf
	.byte	0x2b
	.long	0x982
	.uleb128 0x2
	.byte	0x91
	.sleb128 -64
	.uleb128 0xc
	.long	.LASF199
	.byte	0xcf
	.byte	0x3f
	.long	0x982
	.uleb128 0x3
	.byte	0x91
	.sleb128 -72
	.uleb128 0xc
	.long	.LASF194
	.byte	0xcf
	.byte	0x53
	.long	0x982
	.uleb128 0x3
	.byte	0x91
	.sleb128 -80
	.uleb128 0xc
	.long	.LASF193
	.byte	0xcf
	.byte	0x62
	.long	0x982
	.uleb128 0x3
	.byte	0x91
	.sleb128 -88
	.uleb128 0x1b
	.string	"WM"
	.byte	0xd0
	.byte	0x8
	.long	0x77
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.uleb128 0x1b
	.string	"RM"
	.byte	0xd1
	.byte	0x8
	.long	0x77
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0xd
	.quad	.LBB2
	.quad	.LBE2-.LBB2
	.uleb128 0x1b
	.string	"x"
	.byte	0xd2
	.byte	0xc
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0xd
	.quad	.LBB3
	.quad	.LBE3-.LBB3
	.uleb128 0x2c
	.long	.LASF219
	.byte	0x1
	.byte	0xd4
	.byte	0x9
	.long	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -36
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x2d
	.long	.LASF220
	.byte	0x1
	.byte	0x43
	.byte	0x5
	.long	0x54
	.quad	.LFB7
	.quad	.LFE7-.LFB7
	.uleb128 0x1
	.byte	0x9c
	.long	0x17f1
	.uleb128 0xc
	.long	.LASF160
	.byte	0x43
	.byte	0x27
	.long	0x9b4
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0xc
	.long	.LASF221
	.byte	0x43
	.byte	0x44
	.long	0x9af
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.uleb128 0xc
	.long	.LASF79
	.byte	0x43
	.byte	0x66
	.long	0x4b7
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.byte	0
	.uleb128 0x2e
	.long	.LASF225
	.byte	0x1
	.byte	0x3f
	.byte	0x5
	.long	0x54
	.quad	.LFB6
	.quad	.LFE6-.LFB6
	.uleb128 0x1
	.byte	0x9c
	.byte	0
	.section	.debug_abbrev,"",@progbits
.Ldebug_abbrev0:
	.uleb128 0x1
	.uleb128 0xd
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x38
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x2
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x3
	.uleb128 0xd
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x38
	.uleb128 0x5
	.byte	0
	.byte	0
	.uleb128 0x4
	.uleb128 0x5
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x5
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0x21
	.sleb128 8
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x6
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x7
	.uleb128 0x5
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x8
	.uleb128 0x16
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x9
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xa
	.uleb128 0x24
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3e
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0xe
	.byte	0
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xc
	.uleb128 0x5
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0xd
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.byte	0
	.byte	0
	.uleb128 0xe
	.uleb128 0x13
	.byte	0x1
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0x21
	.sleb128 8
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xf
	.uleb128 0xb
	.byte	0x1
	.byte	0
	.byte	0
	.uleb128 0x10
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x3c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x11
	.uleb128 0xd
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x38
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x12
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x13
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x3c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x14
	.uleb128 0xd
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x88
	.uleb128 0x21
	.sleb128 128
	.uleb128 0x38
	.uleb128 0x5
	.byte	0
	.byte	0
	.uleb128 0x15
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x7c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x16
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x17
	.uleb128 0x37
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x18
	.uleb128 0x26
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x19
	.uleb128 0x1
	.byte	0x1
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1a
	.uleb128 0x21
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2f
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x1b
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x1c
	.uleb128 0x13
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3c
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0x1d
	.uleb128 0xd
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 7
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1e
	.uleb128 0x18
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x1f
	.uleb128 0x5
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x20
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x7a
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x21
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x55
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x22
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0x21
	.sleb128 5
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x7a
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x23
	.uleb128 0x11
	.byte	0x1
	.uleb128 0x25
	.uleb128 0xe
	.uleb128 0x13
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0x1f
	.uleb128 0x1b
	.uleb128 0x1f
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x10
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x24
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x25
	.uleb128 0x24
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3e
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0x8
	.byte	0
	.byte	0
	.uleb128 0x26
	.uleb128 0x13
	.byte	0x1
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x27
	.uleb128 0x17
	.byte	0x1
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x28
	.uleb128 0x16
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x29
	.uleb128 0x13
	.byte	0x1
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0xb
	.uleb128 0x5
	.uleb128 0x88
	.uleb128 0xb
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x2a
	.uleb128 0x15
	.byte	0x1
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x2b
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x88
	.uleb128 0xb
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x2c
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x2d
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x7c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x2e
	.uleb128 0x2e
	.byte	0
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x7a
	.uleb128 0x19
	.byte	0
	.byte	0
	.byte	0
	.section	.debug_aranges,"",@progbits
	.long	0x2c
	.value	0x2
	.long	.Ldebug_info0
	.byte	0x8
	.byte	0
	.value	0
	.value	0
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.quad	0
	.quad	0
	.section	.debug_rnglists,"",@progbits
.Ldebug_ranges0:
	.long	.Ldebug_ranges3-.Ldebug_ranges2
.Ldebug_ranges2:
	.value	0x5
	.byte	0x8
	.byte	0
	.long	0
.LLRL0:
	.byte	0x4
	.uleb128 .LBB7-.Ltext0
	.uleb128 .LBE7-.Ltext0
	.byte	0x4
	.uleb128 .LBB8-.Ltext0
	.uleb128 .LBE8-.Ltext0
	.byte	0
.LLRL1:
	.byte	0x4
	.uleb128 .LBB10-.Ltext0
	.uleb128 .LBE10-.Ltext0
	.byte	0x4
	.uleb128 .LBB11-.Ltext0
	.uleb128 .LBE11-.Ltext0
	.byte	0
.Ldebug_ranges3:
	.section	.debug_line,"",@progbits
.Ldebug_line0:
	.section	.debug_str,"MS",@progbits,1
.LASF174:
	.string	"printf"
.LASF11:
	.string	"__off_t"
.LASF32:
	.string	"_IO_read_ptr"
.LASF129:
	.string	"readcursor"
.LASF212:
	.string	"assignedchunk"
.LASF106:
	.string	"works"
.LASF16:
	.string	"size_t"
.LASF192:
	.string	"work"
.LASF160:
	.string	"scheduler"
.LASF85:
	.string	"Work"
.LASF50:
	.string	"_shortbuf"
.LASF94:
	.string	"write"
.LASF74:
	.string	"CoroutineData"
.LASF7:
	.string	"signed char"
.LASF119:
	.string	"prev"
.LASF197:
	.string	"innerfind"
.LASF215:
	.string	"completed"
.LASF25:
	.string	"__size"
.LASF100:
	.string	"publishend"
.LASF202:
	.string	"threadwork"
.LASF73:
	.string	"stream"
.LASF38:
	.string	"_IO_buf_base"
.LASF95:
	.string	"readies"
.LASF121:
	.string	"wend"
.LASF23:
	.string	"long long unsigned int"
.LASF165:
	.string	"nanosleep"
.LASF114:
	.string	"reading"
.LASF79:
	.string	"data"
.LASF148:
	.string	"globalread"
.LASF131:
	.string	"oreadcursor"
.LASF173:
	.string	"clock_gettime"
.LASF53:
	.string	"_codecvt"
.LASF135:
	.string	"readcursors"
.LASF154:
	.string	"reads"
.LASF180:
	.string	"workers"
.LASF118:
	.string	"newmask"
.LASF28:
	.string	"long long int"
.LASF166:
	.string	"pthread_setaffinity_np"
.LASF164:
	.string	"pthread_join"
.LASF222:
	.string	"GNU C17 11.3.0 -mtune=generic -march=x86-64 -g -O2 -O0 -fPIC -fstack-protector-strong -fno-strict-overflow -frandom-seed=ipz9d8l24i --param=ssp-buffer-size=4"
.LASF193:
	.string	"writers"
.LASF20:
	.string	"__bits"
.LASF146:
	.string	"totalwrites"
.LASF88:
	.string	"created"
.LASF33:
	.string	"_IO_read_end"
.LASF147:
	.string	"totalreads"
.LASF168:
	.string	"posix_memalign"
.LASF209:
	.string	"singlewriter"
.LASF110:
	.string	"buckets"
.LASF9:
	.string	"long int"
.LASF45:
	.string	"_fileno"
.LASF31:
	.string	"_flags"
.LASF210:
	.string	"availableidx"
.LASF188:
	.string	"codata"
.LASF54:
	.string	"_wide_data"
.LASF139:
	.string	"prevread"
.LASF48:
	.string	"_cur_column"
.LASF111:
	.string	"availables"
.LASF62:
	.string	"_IO_codecvt"
.LASF109:
	.string	"primes"
.LASF102:
	.string	"freq_writes"
.LASF65:
	.string	"double"
.LASF133:
	.string	"readstep"
.LASF47:
	.string	"_old_offset"
.LASF52:
	.string	"_offset"
.LASF122:
	.string	"wavail"
.LASF143:
	.string	"currentepoch"
.LASF149:
	.string	"globalwrite"
.LASF156:
	.string	"cwrite"
.LASF141:
	.string	"epochs"
.LASF219:
	.string	"mask"
.LASF185:
	.string	"goods"
.LASF113:
	.string	"freelist"
.LASF136:
	.string	"writecursors"
.LASF151:
	.string	"mystream"
.LASF19:
	.string	"__cpu_mask"
.LASF181:
	.string	"attr"
.LASF61:
	.string	"_IO_marker"
.LASF125:
	.string	"swstart"
.LASF3:
	.string	"unsigned int"
.LASF56:
	.string	"_freeres_buf"
.LASF117:
	.string	"chunksize"
.LASF26:
	.string	"__align"
.LASF170:
	.string	"ceil"
.LASF126:
	.string	"swend"
.LASF2:
	.string	"long unsigned int"
.LASF103:
	.string	"worksize"
.LASF27:
	.string	"pthread_attr_t"
.LASF36:
	.string	"_IO_write_ptr"
.LASF76:
	.string	"Scheduler"
.LASF220:
	.string	"coroutine_func"
.LASF83:
	.string	"kind"
.LASF6:
	.string	"short unsigned int"
.LASF225:
	.string	"yield"
.LASF214:
	.string	"singlewriter2"
.LASF216:
	.string	"singlewriter3"
.LASF40:
	.string	"_IO_save_base"
.LASF184:
	.string	"sends"
.LASF199:
	.string	"readywriters"
.LASF97:
	.string	"threads"
.LASF155:
	.string	"writes"
.LASF51:
	.string	"_lock"
.LASF58:
	.string	"_mode"
.LASF183:
	.string	"chunkindex"
.LASF140:
	.string	"prevwrite"
.LASF86:
	.string	"taskindex"
.LASF144:
	.string	"thiswrite"
.LASF198:
	.string	"readyreaders"
.LASF206:
	.string	"thisgroup"
.LASF72:
	.string	"Access"
.LASF158:
	.string	"accesssize"
.LASF18:
	.string	"tv_nsec"
.LASF194:
	.string	"readers"
.LASF203:
	.string	"cursorlimit"
.LASF66:
	.string	"long double"
.LASF196:
	.string	"currentbucket"
.LASF17:
	.string	"tv_sec"
.LASF15:
	.string	"__syscall_slong_t"
.LASF178:
	.string	"seconds"
.LASF37:
	.string	"_IO_write_end"
.LASF39:
	.string	"_IO_buf_end"
.LASF67:
	.string	"uint64_t"
.LASF224:
	.string	"Data"
.LASF112:
	.string	"bucketstart"
.LASF223:
	.string	"_IO_lock_t"
.LASF30:
	.string	"_IO_FILE"
.LASF70:
	.string	"cursor"
.LASF84:
	.string	"dest"
.LASF123:
	.string	"wpoll"
.LASF205:
	.string	"epochwidth"
.LASF128:
	.string	"writecursor"
.LASF10:
	.string	"__uint64_t"
.LASF177:
	.string	"debug"
.LASF116:
	.string	"chunkslen"
.LASF162:
	.string	"fopen"
.LASF43:
	.string	"_markers"
.LASF14:
	.string	"__clockid_t"
.LASF191:
	.string	"access"
.LASF107:
	.string	"cpu_set"
.LASF99:
	.string	"publishstart"
.LASF24:
	.string	"pthread_t"
.LASF105:
	.string	"threadsize"
.LASF68:
	.string	"Cursor"
.LASF5:
	.string	"unsigned char"
.LASF80:
	.string	"Epoch"
.LASF132:
	.string	"step"
.LASF8:
	.string	"short int"
.LASF138:
	.string	"currentwrite"
.LASF44:
	.string	"_chain"
.LASF46:
	.string	"_flags2"
.LASF150:
	.string	"lastgroup"
.LASF217:
	.string	"findavailable"
.LASF218:
	.string	"pollthreads"
.LASF211:
	.string	"fill"
.LASF187:
	.string	"out_file"
.LASF29:
	.string	"timespec"
.LASF49:
	.string	"_vtable_offset"
.LASF221:
	.string	"coroutine"
.LASF200:
	.string	"stop"
.LASF171:
	.string	"calloc"
.LASF153:
	.string	"successreads"
.LASF90:
	.string	"written"
.LASF98:
	.string	"consumelist"
.LASF108:
	.string	"loglevel"
.LASF93:
	.string	"owner"
.LASF64:
	.string	"float"
.LASF213:
	.string	"chunk"
.LASF4:
	.string	"char"
.LASF176:
	.string	"argv"
.LASF190:
	.string	"epoch"
.LASF189:
	.string	"__cpu"
.LASF75:
	.string	"running"
.LASF78:
	.string	"index"
.LASF124:
	.string	"wassign"
.LASF82:
	.string	"buffer"
.LASF161:
	.string	"fclose"
.LASF71:
	.string	"thread"
.LASF208:
	.string	"thistream"
.LASF12:
	.string	"__off64_t"
.LASF182:
	.string	"offset"
.LASF34:
	.string	"_IO_read_base"
.LASF42:
	.string	"_IO_save_end"
.LASF157:
	.string	"cread"
.LASF163:
	.string	"snprintf"
.LASF104:
	.string	"threadindex"
.LASF142:
	.string	"epochssize"
.LASF81:
	.string	"time"
.LASF134:
	.string	"globalstep"
.LASF57:
	.string	"__pad5"
.LASF130:
	.string	"owritecursor"
.LASF137:
	.string	"currentread"
.LASF13:
	.string	"__time_t"
.LASF195:
	.string	"found"
.LASF59:
	.string	"_unused2"
.LASF91:
	.string	"Chunk"
.LASF172:
	.string	"switch_to"
.LASF169:
	.string	"memset"
.LASF101:
	.string	"freq"
.LASF115:
	.string	"writing"
.LASF167:
	.string	"pthread_create"
.LASF69:
	.string	"global"
.LASF87:
	.string	"available"
.LASF201:
	.string	"work2"
.LASF41:
	.string	"_IO_backup_base"
.LASF152:
	.string	"laststream"
.LASF186:
	.string	"filename"
.LASF77:
	.string	"Coroutine"
.LASF89:
	.string	"read"
.LASF179:
	.string	"worksize_each"
.LASF175:
	.string	"argc"
.LASF21:
	.string	"cpu_set_t"
.LASF55:
	.string	"_freeres_list"
.LASF145:
	.string	"writelog"
.LASF63:
	.string	"_IO_wide_data"
.LASF60:
	.string	"FILE"
.LASF92:
	.string	"start"
.LASF159:
	.string	"coroutines"
.LASF22:
	.string	"clockid_t"
.LASF207:
	.string	"past"
.LASF96:
	.string	"main"
.LASF35:
	.string	"_IO_write_base"
.LASF127:
	.string	"middle"
.LASF120:
	.string	"wstart"
.LASF204:
	.string	"epochsize"
	.section	.debug_line_str,"MS",@progbits,1
.LASF1:
	.string	"/home/runner/assembly"
.LASF0:
	.string	"stream2-workqueue.c"
	.ident	"GCC: (GNU) 11.3.0"
	.section	.note.GNU-stack,"",@progbits
