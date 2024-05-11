	.file	"tree234.c"
	.text
	.p2align 4
	.type	freenode234, @function
freenode234:
.LFB40:
	.cfi_startproc
	testq	%rdi, %rdi
	je	.L1
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	pushq	%r13
	.cfi_def_cfa_offset 24
	.cfi_offset 13, -24
	pushq	%r12
	.cfi_def_cfa_offset 32
	.cfi_offset 12, -32
	pushq	%rbp
	.cfi_def_cfa_offset 40
	.cfi_offset 6, -40
	movq	%rdi, %rbp
	subq	$8, %rsp
	.cfi_def_cfa_offset 48
	movq	8(%rdi), %r12
	testq	%r12, %r12
	je	.L3
	movq	8(%r12), %r13
	testq	%r13, %r13
	je	.L4
	movq	8(%r13), %rdi
	call	freenode234
	movq	16(%r13), %rdi
	call	freenode234
	movq	24(%r13), %rdi
	call	freenode234
	movq	32(%r13), %rdi
	call	freenode234
	movq	%r13, %rdi
	call	free@PLT
.L4:
	movq	16(%r12), %r13
	testq	%r13, %r13
	je	.L5
	movq	8(%r13), %rdi
	call	freenode234
	movq	16(%r13), %rdi
	call	freenode234
	movq	24(%r13), %rdi
	call	freenode234
	movq	32(%r13), %rdi
	call	freenode234
	movq	%r13, %rdi
	call	free@PLT
.L5:
	movq	24(%r12), %r13
	testq	%r13, %r13
	je	.L6
	movq	8(%r13), %r14
	testq	%r14, %r14
	je	.L7
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L7:
	movq	16(%r13), %r14
	testq	%r14, %r14
	je	.L8
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L8:
	movq	24(%r13), %r14
	testq	%r14, %r14
	je	.L9
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L9:
	movq	32(%r13), %r14
	testq	%r14, %r14
	je	.L10
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L10:
	movq	%r13, %rdi
	call	free@PLT
.L6:
	movq	32(%r12), %r13
	testq	%r13, %r13
	je	.L11
	movq	8(%r13), %rdi
	call	freenode234
	movq	16(%r13), %rdi
	call	freenode234
	movq	24(%r13), %rdi
	call	freenode234
	movq	32(%r13), %rdi
	call	freenode234
	movq	%r13, %rdi
	call	free@PLT
.L11:
	movq	%r12, %rdi
	call	free@PLT
.L3:
	movq	16(%rbp), %r12
	testq	%r12, %r12
	je	.L12
	movq	8(%r12), %r13
	testq	%r13, %r13
	je	.L13
	movq	8(%r13), %rdi
	call	freenode234
	movq	16(%r13), %rdi
	call	freenode234
	movq	24(%r13), %rdi
	call	freenode234
	movq	32(%r13), %rdi
	call	freenode234
	movq	%r13, %rdi
	call	free@PLT
.L13:
	movq	16(%r12), %r13
	testq	%r13, %r13
	je	.L14
	movq	8(%r13), %r14
	testq	%r14, %r14
	je	.L15
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L15:
	movq	16(%r13), %r14
	testq	%r14, %r14
	je	.L16
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L16:
	movq	24(%r13), %r14
	testq	%r14, %r14
	je	.L17
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L17:
	movq	32(%r13), %rdi
	call	freenode234
	movq	%r13, %rdi
	call	free@PLT
.L14:
	movq	24(%r12), %r13
	testq	%r13, %r13
	je	.L18
	movq	8(%r13), %rdi
	call	freenode234
	movq	16(%r13), %rdi
	call	freenode234
	movq	24(%r13), %rdi
	call	freenode234
	movq	32(%r13), %rdi
	call	freenode234
	movq	%r13, %rdi
	call	free@PLT
.L18:
	movq	32(%r12), %r13
	testq	%r13, %r13
	je	.L19
	movq	8(%r13), %rdi
	call	freenode234
	movq	16(%r13), %rdi
	call	freenode234
	movq	24(%r13), %rdi
	call	freenode234
	movq	32(%r13), %rdi
	call	freenode234
	movq	%r13, %rdi
	call	free@PLT
.L19:
	movq	%r12, %rdi
	call	free@PLT
.L12:
	movq	24(%rbp), %r12
	testq	%r12, %r12
	je	.L20
	movq	8(%r12), %r13
	testq	%r13, %r13
	je	.L21
	movq	8(%r13), %rdi
	call	freenode234
	movq	16(%r13), %rdi
	call	freenode234
	movq	24(%r13), %rdi
	call	freenode234
	movq	32(%r13), %rdi
	call	freenode234
	movq	%r13, %rdi
	call	free@PLT
.L21:
	movq	16(%r12), %r13
	testq	%r13, %r13
	je	.L22
	movq	8(%r13), %rdi
	call	freenode234
	movq	16(%r13), %rdi
	call	freenode234
	movq	24(%r13), %rdi
	call	freenode234
	movq	32(%r13), %rdi
	call	freenode234
	movq	%r13, %rdi
	call	free@PLT
.L22:
	movq	24(%r12), %r13
	testq	%r13, %r13
	je	.L23
	movq	8(%r13), %r14
	testq	%r14, %r14
	je	.L24
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L24:
	movq	16(%r13), %r14
	testq	%r14, %r14
	je	.L25
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L25:
	movq	24(%r13), %r14
	testq	%r14, %r14
	je	.L26
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L26:
	movq	32(%r13), %r14
	testq	%r14, %r14
	je	.L27
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L27:
	movq	%r13, %rdi
	call	free@PLT
.L23:
	movq	32(%r12), %r13
	testq	%r13, %r13
	je	.L28
	movq	8(%r13), %rdi
	call	freenode234
	movq	16(%r13), %rdi
	call	freenode234
	movq	24(%r13), %rdi
	call	freenode234
	movq	32(%r13), %rdi
	call	freenode234
	movq	%r13, %rdi
	call	free@PLT
.L28:
	movq	%r12, %rdi
	call	free@PLT
.L20:
	movq	32(%rbp), %r12
	testq	%r12, %r12
	je	.L29
	movq	8(%r12), %r13
	testq	%r13, %r13
	je	.L30
	movq	8(%r13), %r14
	testq	%r14, %r14
	je	.L31
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L31:
	movq	16(%r13), %r14
	testq	%r14, %r14
	je	.L32
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L32:
	movq	24(%r13), %r14
	testq	%r14, %r14
	je	.L33
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L33:
	movq	32(%r13), %r14
	testq	%r14, %r14
	je	.L34
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L34:
	movq	%r13, %rdi
	call	free@PLT
.L30:
	movq	16(%r12), %r13
	testq	%r13, %r13
	je	.L35
	movq	8(%r13), %rdi
	call	freenode234
	movq	16(%r13), %rdi
	call	freenode234
	movq	24(%r13), %rdi
	call	freenode234
	movq	32(%r13), %rdi
	call	freenode234
	movq	%r13, %rdi
	call	free@PLT
.L35:
	movq	24(%r12), %r13
	testq	%r13, %r13
	je	.L36
	movq	8(%r13), %rdi
	call	freenode234
	movq	16(%r13), %rdi
	call	freenode234
	movq	24(%r13), %rdi
	call	freenode234
	movq	32(%r13), %rdi
	call	freenode234
	movq	%r13, %rdi
	call	free@PLT
.L36:
	movq	32(%r12), %r13
	testq	%r13, %r13
	je	.L37
	movq	8(%r13), %rdi
	call	freenode234
	movq	16(%r13), %rdi
	call	freenode234
	movq	24(%r13), %rdi
	call	freenode234
	movq	32(%r13), %rdi
	call	freenode234
	movq	%r13, %rdi
	call	free@PLT
.L37:
	movq	%r12, %rdi
	call	free@PLT
.L29:
	addq	$8, %rsp
	.cfi_def_cfa_offset 40
	movq	%rbp, %rdi
	popq	%rbp
	.cfi_restore 6
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_restore 12
	.cfi_def_cfa_offset 24
	popq	%r13
	.cfi_restore 13
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_restore 14
	.cfi_def_cfa_offset 8
	jmp	free@PLT
	.p2align 4,,10
	.p2align 3
.L1:
	ret
	.cfi_endproc
.LFE40:
	.size	freenode234, .-freenode234
	.p2align 4
	.type	add234_internal, @function
add234_internal:
.LFB44:
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
	movq	%rsi, %r13
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	movq	%rdi, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$88, %rsp
	.cfi_def_cfa_offset 144
	movq	(%rdi), %rbp
	testq	%rbp, %rbp
	je	.L295
	testl	%edx, %edx
	js	.L150
.L296:
	movq	8(%rbp), %rax
	testq	%rax, %rax
	je	.L151
	movl	40(%rbp), %ecx
	cmpl	%edx, %ecx
	jge	.L222
	subl	$1, %edx
	movl	44(%rbp), %eax
	subl	%ecx, %edx
	cmpl	%edx, %eax
	jl	.L153
	movq	16(%rbp), %rax
	movl	$16, %ecx
.L154:
	testq	%rax, %rax
	je	.L285
.L222:
	movq	%rax, %rbp
	testl	%edx, %edx
	jns	.L296
.L150:
	movq	56(%rbp), %rsi
	movq	%r13, %rdi
	call	*8(%r12)
	testl	%eax, %eax
	js	.L297
	je	.L298
	movq	64(%rbp), %rsi
	testq	%rsi, %rsi
	je	.L289
	movq	%r13, %rdi
	call	*8(%r12)
	testl	%eax, %eax
	js	.L289
	je	.L299
	movq	72(%rbp), %rsi
	testq	%rsi, %rsi
	je	.L288
	movq	%r13, %rdi
	call	*8(%r12)
	testl	%eax, %eax
	js	.L288
	je	.L216
	movq	32(%rbp), %rbx
	movl	$32, %ecx
	.p2align 4,,10
	.p2align 3
.L157:
	testq	%rbx, %rbx
	jne	.L173
	jmp	.L285
	.p2align 4,,10
	.p2align 3
.L165:
	je	.L167
	movq	64(%rbx), %rsi
	testq	%rsi, %rsi
	je	.L284
	movq	%r13, %rdi
	call	*8(%r12)
	testl	%eax, %eax
	js	.L284
	je	.L170
	movq	72(%rbx), %rsi
	testq	%rsi, %rsi
	je	.L283
	movq	%r13, %rdi
	call	*8(%r12)
	testl	%eax, %eax
	js	.L283
	je	.L164
	movq	32(%rbx), %rax
	movl	$32, %ecx
	.p2align 4,,10
	.p2align 3
.L166:
	testq	%rax, %rax
	je	.L213
.L217:
	movq	%rax, %rbx
.L173:
	movq	56(%rbx), %rsi
	movq	%r13, %rdi
	call	*8(%r12)
	testl	%eax, %eax
	jns	.L165
	movq	8(%rbx), %rax
	movl	$8, %ecx
	testq	%rax, %rax
	jne	.L217
	.p2align 4,,10
	.p2align 3
.L213:
	movq	%r12, 72(%rsp)
	xorl	%r14d, %r14d
	addq	%rbx, %rcx
	leaq	8(%rbx), %r10
	movq	%r13, 8(%rsp)
	pxor	%xmm0, %xmm0
	xorl	%edx, %edx
	movq	%rcx, %r15
	movq	%r13, 64(%rsp)
	movl	%r14d, %r13d
	movq	%r10, %r14
	.p2align 4,,10
	.p2align 3
.L206:
	movq	64(%rbx), %rax
	movhlps	%xmm0, %xmm3
	movq	%xmm0, %r9
	movq	%xmm3, %r12
	movq	%rax, 56(%rsp)
	testq	%rax, %rax
	je	.L300
	movq	72(%rbx), %r11
	testq	%r11, %r11
	je	.L301
	movl	$80, %edi
	movl	%edx, 44(%rsp)
	movq	%r11, 32(%rsp)
	movq	%xmm0, 48(%rsp)
	movaps	%xmm0, 16(%rsp)
	call	malloc@PLT
	cmpq	%r15, %r14
	movl	44(%rsp), %edx
	pxor	%xmm2, %xmm2
	movq	%rax, %rbp
	movq	%rax, %xmm4
	movq	(%rbx), %rax
	movq	%rbx, %xmm1
	movq	32(%rsp), %r11
	movdqa	16(%rsp), %xmm0
	punpcklqdq	%xmm1, %xmm4
	movq	%rax, 0(%rbp)
	movq	48(%rsp), %r9
	je	.L302
	movq	8(%rbx), %xmm3
	movq	%r9, %xmm7
	movd	%edx, %xmm1
	leaq	16(%rbx), %rax
	movdqa	%xmm3, %xmm8
	punpcklqdq	%xmm7, %xmm8
	movd	40(%rbx), %xmm7
	punpckldq	%xmm1, %xmm7
	movq	56(%rbx), %xmm1
	movdqa	%xmm1, %xmm6
	movdqa	%xmm1, %xmm5
	movhps	8(%rsp), %xmm6
	movhps	56(%rsp), %xmm5
	cmpq	%rax, %r15
	je	.L303
	movq	16(%rbx), %r10
	movdqa	%xmm3, %xmm6
	leaq	24(%rbx), %rax
	movq	40(%rbx), %rdi
	movq	%r10, %xmm7
	punpcklqdq	%xmm7, %xmm6
	cmpq	%rax, %r15
	je	.L304
	movups	%xmm6, 8(%rbp)
	movl	%edx, %ecx
	movups	%xmm5, 56(%rbp)
	movq	24(%rbx), %rax
	movq	%rdi, 40(%rbp)
	movq	%rax, 24(%rbp)
	movl	48(%rbx), %eax
	movl	%eax, 48(%rbp)
	movq	8(%rsp), %rax
	movl	%edx, 40(%rbx)
	movq	%rax, 56(%rbx)
	movq	%r11, 8(%rsp)
	movq	%rax, %r11
	movups	%xmm0, 8(%rbx)
.L191:
	movups	%xmm2, 24(%rbx)
	movl	%r13d, 44(%rbx)
	movq	$0, 32(%rbp)
	movq	$0, 48(%rbx)
	movl	$0, 52(%rbp)
	movups	%xmm2, 64(%rbx)
	movq	8(%rbp), %rax
	movq	$0, 72(%rbp)
	testq	%rax, %rax
	je	.L194
	movq	%rbp, (%rax)
.L194:
	movq	16(%rbp), %rax
	testq	%rax, %rax
	je	.L195
	movq	%rbp, (%rax)
.L195:
	movq	24(%rbp), %rax
	testq	%rax, %rax
	je	.L196
	movq	%rbp, (%rax)
.L196:
	testq	%r9, %r9
	je	.L197
	movq	%rbx, (%r9)
.L197:
	testq	%r12, %r12
	je	.L198
	movq	%rbx, (%r12)
.L198:
	movl	44(%rbp), %edx
	addl	40(%rbp), %edx
	addl	48(%rbp), %edx
	cmpq	$1, 56(%rbp)
	sbbl	$-1, %edx
	movq	(%rbx), %rax
	cmpq	$1, 64(%rbp)
	sbbl	$-1, %edx
	addl	%ecx, %r13d
	cmpq	$1, %r11
	sbbl	$-1, %r13d
	testq	%rax, %rax
	je	.L305
	leaq	8(%rax), %r14
	movq	%r14, %r15
	cmpq	%rbx, 8(%rax)
	je	.L203
	leaq	16(%rax), %r15
	cmpq	%rbx, 16(%rax)
	je	.L203
	leaq	32(%rax), %r15
	cmpq	%rbx, 24(%rax)
	je	.L306
.L203:
	movdqa	%xmm4, %xmm0
	movq	%rax, %rbx
	jmp	.L206
	.p2align 4,,10
	.p2align 3
.L151:
	movslq	%edx, %rax
	leaq	8(,%rax,8), %rcx
	movq	8(%rbp,%rax,8), %rax
	testq	%rax, %rax
	jne	.L222
.L285:
	movq	%rbp, %rbx
	jmp	.L213
	.p2align 4,,10
	.p2align 3
.L297:
	movq	8(%rbp), %rbx
	movl	$8, %ecx
	jmp	.L157
	.p2align 4,,10
	.p2align 3
.L289:
	movq	16(%rbp), %rbx
	movl	$16, %ecx
	jmp	.L157
	.p2align 4,,10
	.p2align 3
.L284:
	movq	16(%rbx), %rax
	movl	$16, %ecx
	jmp	.L166
	.p2align 4,,10
	.p2align 3
.L153:
	subl	%eax, %edx
	movl	48(%rbp), %eax
	subl	$1, %edx
	cmpl	%edx, %eax
	jl	.L155
	movq	24(%rbp), %rax
	movl	$24, %ecx
	jmp	.L154
	.p2align 4,,10
	.p2align 3
.L283:
	movq	24(%rbx), %rax
	movl	$24, %ecx
	jmp	.L166
	.p2align 4,,10
	.p2align 3
.L288:
	movq	24(%rbp), %rbx
	movl	$24, %ecx
	jmp	.L157
	.p2align 4,,10
	.p2align 3
.L155:
	subl	%eax, %edx
	subl	$1, %edx
	cmpl	%edx, 52(%rbp)
	jl	.L215
	movq	32(%rbp), %rax
	movl	$32, %ecx
	jmp	.L154
	.p2align 4,,10
	.p2align 3
.L305:
	movl	$80, %edi
	movq	72(%rsp), %r12
	movl	%r13d, %r14d
	movl	%edx, %r15d
	movq	64(%rsp), %r13
	call	malloc@PLT
	movq	8(%rsp), %rdi
	movq	%rax, (%r12)
	movq	%rbp, 8(%rax)
	movl	%r15d, 40(%rax)
	movq	%rdi, 56(%rax)
	movq	%rbx, 16(%rax)
	movl	%r14d, 44(%rax)
	movq	$0, 64(%rax)
	movq	$0, 24(%rax)
	movq	$0, 72(%rax)
	movq	$0, 32(%rax)
	movq	$0, 48(%rax)
	movq	$0, (%rax)
	movq	%rax, 0(%rbp)
	movq	%rax, (%rbx)
.L239:
	addq	$88, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	movq	%r13, %rax
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
.L302:
	.cfi_restore_state
	movq	8(%rsp), %rax
	movups	%xmm0, 8(%rbp)
	movl	%r13d, 44(%rbp)
	movq	%rax, 56(%rbp)
	movq	56(%rbx), %rax
	movl	%edx, 40(%rbp)
	movq	%rax, 64(%rbp)
	movq	16(%rbx), %rax
	movq	%rax, 24(%rbp)
	movl	44(%rbx), %eax
	movl	%eax, 48(%rbp)
.L287:
	movq	64(%rbx), %rax
	movq	24(%rbx), %r9
	movq	%r11, 56(%rbx)
	movl	48(%rbx), %ecx
	movq	32(%rbx), %r12
	movq	%rax, 8(%rsp)
	movl	52(%rbx), %r13d
	movq	%r9, 8(%rbx)
	movl	%ecx, 40(%rbx)
	movq	%r12, 16(%rbx)
	jmp	.L191
	.p2align 4,,10
	.p2align 3
.L303:
	movq	%r12, 24(%rbp)
	movl	%r13d, 48(%rbp)
	movups	%xmm8, 8(%rbp)
	movq	%xmm7, 40(%rbp)
	movups	%xmm6, 56(%rbp)
	jmp	.L287
	.p2align 4,,10
	.p2align 3
.L304:
	movq	%r12, %xmm0
	movq	56(%rsp), %rax
	movl	%edx, 48(%rbp)
	movl	%r13d, %ecx
	movhps	32(%rbx), %xmm0
	movq	%rdi, 40(%rbp)
	movq	%r9, 24(%rbp)
	movq	%r12, %r9
	movq	32(%rbx), %r12
	movq	%r10, 16(%rbp)
	movq	%rax, 64(%rbp)
	movq	%xmm3, 8(%rbp)
	movq	%xmm1, 56(%rbp)
	movl	%r13d, 40(%rbx)
	movl	52(%rbx), %r13d
	movq	%r11, 56(%rbx)
	movups	%xmm0, 8(%rbx)
	jmp	.L191
	.p2align 4,,10
	.p2align 3
.L306:
	leaq	24(%rax), %r15
	jmp	.L203
.L300:
	movq	%r14, %r10
	movq	%xmm3, %r8
	movl	%r13d, %r14d
	movq	64(%rsp), %r13
	cmpq	%r15, %r10
	je	.L307
	movq	8(%rsp), %rax
	movl	%r14d, 48(%rbx)
	movl	%edx, 44(%rbx)
	movq	%rax, 64(%rbx)
	movq	8(%rbx), %rax
	movups	%xmm0, 16(%rbx)
.L185:
	testq	%rax, %rax
	je	.L186
	movq	%rbx, (%rax)
.L186:
	testq	%r9, %r9
	je	.L187
	movq	%rbx, (%r9)
.L187:
	testq	%r8, %r8
	je	.L180
	movq	%rbx, (%r8)
.L180:
	movq	(%rbx), %rdx
	testq	%rdx, %rdx
	jne	.L189
	jmp	.L239
	.p2align 4,,10
	.p2align 3
.L308:
	movq	%rax, %rdx
.L189:
	movl	44(%rbx), %eax
	addl	40(%rbx), %eax
	addl	48(%rbx), %eax
	addl	52(%rbx), %eax
	cmpq	$1, 56(%rbx)
	sbbl	$-1, %eax
	cmpq	$1, 64(%rbx)
	sbbl	$-1, %eax
	cmpq	$1, 72(%rbx)
	sbbl	$-1, %eax
	xorl	%ecx, %ecx
	cmpq	8(%rdx), %rbx
	je	.L209
	movl	$1, %ecx
	cmpq	16(%rdx), %rbx
	je	.L209
	xorl	%ecx, %ecx
	cmpq	24(%rdx), %rbx
	setne	%cl
	addl	$2, %ecx
.L209:
	movslq	%ecx, %rcx
	movq	%rdx, %rbx
	movl	%eax, 40(%rdx,%rcx,4)
	movq	(%rdx), %rax
	testq	%rax, %rax
	jne	.L308
	jmp	.L239
.L301:
	movq	8(%rsp), %xmm1
	movq	%r14, %r10
	movq	%xmm3, %r8
	movl	%r13d, %r14d
	movq	%r15, %rcx
	movq	64(%rsp), %r13
	movhps	56(%rsp), %xmm1
	cmpq	%r15, %r10
	je	.L309
	leaq	16(%rbx), %rax
	movq	8(%rbx), %rdi
	cmpq	%rax, %rcx
	je	.L310
	movq	8(%rsp), %rax
	movl	%r14d, 52(%rbx)
	movl	%edx, 48(%rbx)
	movq	%rax, 72(%rbx)
	movq	16(%rbx), %rax
	movups	%xmm0, 24(%rbx)
.L183:
	testq	%rdi, %rdi
	je	.L185
	movq	%rbx, (%rdi)
	jmp	.L185
.L307:
	movq	8(%rsp), %xmm1
	movl	44(%rbx), %eax
	movl	%edx, 40(%rbx)
	movq	%r12, %r9
	movq	16(%rbx), %rcx
	movl	%r14d, 44(%rbx)
	movhps	56(%rbx), %xmm1
	movl	%eax, 48(%rbx)
	movq	%xmm0, %rax
	movq	%rcx, 24(%rbx)
	movq	%rcx, %r8
	movups	%xmm1, 56(%rbx)
	movups	%xmm0, 8(%rbx)
	jmp	.L185
.L309:
	movd	%edx, %xmm1
	movq	24(%rbx), %rdi
	movq	16(%rbx), %rcx
	movq	%rax, 72(%rbx)
	movd	48(%rbx), %xmm3
	movd	44(%rbx), %xmm2
	movups	%xmm0, 8(%rbx)
	movq	%r12, %rax
	movq	%rdi, 32(%rbx)
	movq	%rdi, %r8
	movq	%rcx, %r9
	movq	%xmm0, %rdi
	punpckldq	%xmm3, %xmm2
	movd	%r14d, %xmm3
	movq	%rcx, 24(%rbx)
	punpckldq	%xmm3, %xmm1
	punpcklqdq	%xmm2, %xmm1
	movq	8(%rsp), %xmm2
	movups	%xmm1, 40(%rbx)
	movhps	56(%rbx), %xmm2
	movups	%xmm2, 56(%rbx)
	jmp	.L183
.L298:
	movq	%rbp, %rbx
.L167:
	movq	56(%rbx), %r13
	jmp	.L239
.L295:
	movl	$80, %edi
	call	malloc@PLT
	pxor	%xmm0, %xmm0
	movups	%xmm0, 40(%rax)
	pxor	%xmm0, %xmm0
	movq	%rax, (%r12)
	movq	$0, 72(%rax)
	movq	$0, 64(%rax)
	movq	$0, 32(%rax)
	movq	%r13, 56(%rax)
	movups	%xmm0, (%rax)
	movups	%xmm0, 16(%rax)
	jmp	.L239
.L299:
	movq	%rbp, %rbx
.L170:
	movq	64(%rbx), %r13
	jmp	.L239
.L310:
	movq	24(%rbx), %rcx
	movl	48(%rbx), %eax
	movl	%edx, 44(%rbx)
	movq	%r12, %r9
	movl	%r14d, 48(%rbx)
	movl	%eax, 52(%rbx)
	movq	%rcx, %r8
	movq	%xmm0, %rax
	movq	%rcx, 32(%rbx)
	movups	%xmm1, 64(%rbx)
	movups	%xmm0, 16(%rbx)
	jmp	.L183
.L215:
	xorl	%r13d, %r13d
	jmp	.L239
.L216:
	movq	%rbp, %rbx
.L164:
	movq	72(%rbx), %r13
	jmp	.L239
	.cfi_endproc
.LFE44:
	.size	add234_internal, .-add234_internal
	.p2align 4
	.type	delpos234_internal, @function
delpos234_internal:
.LFB52:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	movl	$-1, %r11d
	movl	%esi, %r15d
	xorl	%r10d, %r10d
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
	subq	$56, %rsp
	.cfi_def_cfa_offset 112
	movq	(%rdi), %r12
	movq	%rdi, 40(%rsp)
	.p2align 4,,10
	.p2align 3
.L312:
	testq	%r12, %r12
	je	.L471
.L347:
	movl	40(%r12), %eax
	cmpl	%r15d, %eax
	jle	.L313
	movq	8(%r12), %rdi
	cmpq	$0, 64(%rdi)
	je	.L314
.L470:
	movq	%rdi, %r12
	testq	%r12, %r12
	jne	.L347
.L471:
	testq	%r10, %r10
	je	.L472
.L348:
	cmpl	$-1, %r11d
	je	.L311
.L385:
	movq	(%r12), %rdx
	movq	8(%r12), %rax
	testq	%rdx, %rdx
	je	.L473
.L350:
	testq	%rax, %rax
	je	.L474
.L352:
	movslq	%r11d, %rbp
	movq	8(%r12,%rbp,8), %rbx
	cmpq	$0, 64(%rbx)
	jne	.L475
	leal	1(%r11), %r15d
	movslq	%r15d, %r13
	leaq	(%r12,%r13,8), %r14
	movq	8(%r14), %rdi
	cmpq	$0, 64(%rdi)
	movq	8(%rdi), %rax
	je	.L366
	movq	%rdi, %rax
	.p2align 4,,10
	.p2align 3
.L367:
	movq	%rax, %rdx
	movq	8(%rax), %rax
	testq	%rax, %rax
	jne	.L367
	movq	56(%rdx), %rax
	xorl	%r15d, %r15d
	movq	%rax, 56(%r12,%rbp,8)
	movq	%rdi, %r12
	jmp	.L312
	.p2align 4,,10
	.p2align 3
.L313:
	subl	$1, %r15d
	subl	%eax, %r15d
	js	.L316
	movl	44(%r12), %eax
	cmpl	%r15d, %eax
	jg	.L317
	subl	%eax, %r15d
	subl	$1, %r15d
	js	.L318
	movl	48(%r12), %eax
	cmpl	%r15d, %eax
	jg	.L319
	movl	%r15d, %edx
	subl	%eax, %edx
	subl	$1, %edx
	js	.L320
	movq	32(%r12), %rbx
	cmpq	$0, 64(%rbx)
	je	.L321
	movq	%rbx, %r12
	movl	%edx, %r15d
	jmp	.L312
	.p2align 4,,10
	.p2align 3
.L475:
	movq	%rbx, %rax
	jmp	.L361
	.p2align 4,,10
	.p2align 3
.L364:
	movq	32(%rax), %rdx
	testq	%rdx, %rdx
	je	.L476
.L403:
	movq	%rdx, %rax
.L361:
	movq	8(%rax), %rcx
	testq	%rcx, %rcx
	jne	.L364
	movq	72(%rax), %rdx
	testq	%rdx, %rdx
	je	.L477
.L365:
	movl	40(%r12,%rbp,4), %r15d
	movq	%rdx, 56(%r12,%rbp,8)
	movq	%rbx, %r12
	subl	$1, %r15d
	jmp	.L312
	.p2align 4,,10
	.p2align 3
.L476:
	movq	24(%rax), %rdx
	testq	%rdx, %rdx
	jne	.L403
	movq	16(%rax), %rax
	testq	%rax, %rax
	cmove	%rcx, %rax
	jmp	.L361
	.p2align 4,,10
	.p2align 3
.L316:
	xorl	%r11d, %r11d
	testq	%r10, %r10
	jne	.L385
	movq	(%r12), %rdx
	movq	56(%r12), %r10
	movq	8(%r12), %rax
	testq	%rdx, %rdx
	jne	.L350
	.p2align 4,,10
	.p2align 3
.L473:
	cmpq	$0, 64(%r12)
	je	.L478
	testq	%rax, %rax
	jne	.L352
.L384:
	cmpl	$2, %r11d
	je	.L353
	leal	1(%r11), %edx
	movslq	%edx, %rcx
	movq	56(%r12,%rcx,8), %rcx
	testq	%rcx, %rcx
	je	.L354
	movslq	%r11d, %rsi
	movq	%rcx, 56(%r12,%rsi,8)
	cmpl	$2, %edx
	je	.L353
	movq	72(%r12), %rdx
	testq	%rdx, %rdx
	je	.L479
	movq	%rdx, 64(%r12)
.L353:
	movl	$2, %r11d
.L354:
	movslq	%r11d, %rdx
	movq	$0, 56(%r12,%rdx,8)
	testq	%rax, %rax
	jne	.L358
	jmp	.L397
	.p2align 4,,10
	.p2align 3
.L401:
	movq	%rdx, %rax
.L358:
	xorl	%edx, %edx
	cmpq	%r12, 8(%rax)
	je	.L357
	movl	$1, %edx
	cmpq	%r12, 16(%rax)
	je	.L357
	xorl	%edx, %edx
	cmpq	%r12, 24(%rax)
	setne	%dl
	addl	$2, %edx
.L357:
	movslq	%edx, %rdx
	movq	%rax, %r12
	subl	$1, 40(%rax,%rdx,4)
	movq	(%rax), %rdx
	testq	%rdx, %rdx
	jne	.L401
.L397:
	movq	%r10, %r12
.L311:
	addq	$56, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	movq	%r12, %rax
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
.L474:
	.cfi_restore_state
	cmpq	$0, 64(%r12)
	je	.L352
	movq	%rdx, %rax
	jmp	.L384
	.p2align 4,,10
	.p2align 3
.L472:
	movslq	%r11d, %rax
	movq	56(%r10,%rax,8), %r10
	jmp	.L348
	.p2align 4,,10
	.p2align 3
.L317:
	movq	16(%r12), %rbx
	cmpq	$0, 64(%rbx)
	je	.L390
.L396:
	movq	%rbx, %r12
	jmp	.L312
	.p2align 4,,10
	.p2align 3
.L366:
	movq	56(%r12,%rbp,8), %rdx
	movq	%rax, 24(%rbx)
	movq	%rdx, 64(%rbx)
	movl	40(%rdi), %edx
	movl	%edx, 48(%rbx)
	testq	%rax, %rax
	je	.L368
	movq	%rbx, (%rax)
.L368:
	movq	56(%rdi), %rax
	movl	44(%rdi), %edx
	movq	%rax, 72(%rbx)
	movq	16(%rdi), %rax
	movl	%edx, 52(%rbx)
	movq	%rax, 32(%rbx)
	testq	%rax, %rax
	je	.L369
	movq	%rbx, (%rax)
.L369:
	movq	%r10, 16(%rsp)
	movl	%r11d, 8(%rsp)
	call	free@PLT
	movl	44(%rbx), %eax
	addl	40(%rbx), %eax
	addl	48(%rbx), %eax
	addl	52(%rbx), %eax
	cmpq	$1, 56(%rbx)
	movl	8(%rsp), %r11d
	sbbl	$-1, %eax
	cmpq	$1, 64(%rbx)
	movq	16(%rsp), %r10
	sbbl	$-1, %eax
	cmpq	$1, 72(%rbx)
	sbbl	$-1, %eax
	cmpl	$2, %r11d
	movl	%eax, 40(%r12,%rbp,4)
	je	.L373
	movq	56(%r14), %rax
	testq	%rax, %rax
	je	.L405
	movq	%rax, 56(%r12,%rbp,8)
	leal	2(%r11), %eax
	cltq
	leaq	(%r12,%rax,8), %rdx
	movq	8(%rdx), %rcx
	movq	%rcx, 8(%r14)
	leaq	8(%rax), %rcx
	movl	8(%r12,%rcx,4), %esi
	movl	%esi, 40(%r12,%r13,4)
	cmpl	$2, %r15d
	je	.L373
	movq	56(%rdx), %rsi
	testq	%rsi, %rsi
	je	.L480
	movq	%rsi, 56(%r14)
	movq	32(%r12), %rax
	movq	%rax, 8(%rdx)
	movl	52(%r12), %eax
	movl	%eax, 8(%r12,%rcx,4)
.L373:
	movl	$2, %edx
	movl	$3, %r13d
.L374:
	movslq	%edx, %rax
	movq	$0, 56(%r12,%rax,8)
	cmpq	$0, 56(%r12)
	movq	$0, 8(%r12,%r13,8)
	movl	$0, 40(%r12,%r13,4)
	je	.L481
.L377:
	movl	44(%rbx), %r15d
	addl	40(%rbx), %r15d
	movq	%rbx, %r12
	addl	$1, %r15d
	jmp	.L312
	.p2align 4,,10
	.p2align 3
.L314:
	movq	16(%r12), %rbx
	testq	%rbx, %rbx
	je	.L469
	xorl	%edx, %edx
	cmpq	$0, 64(%rbx)
	movl	$1, %ecx
	je	.L469
.L386:
	movq	56(%r12,%rdx,8), %rax
	movl	40(%rbx), %esi
	movq	%rax, 64(%rdi)
	movq	8(%rbx), %rax
	movl	%esi, 48(%rdi)
	movq	%rax, 24(%rdi)
	testq	%rax, %rax
	je	.L331
	movq	%rdi, (%rax)
.L331:
	movq	56(%rbx), %rax
	movq	%rax, 56(%r12,%rdx,8)
	movq	16(%rbx), %rax
	movq	%rax, 8(%rbx)
	movl	44(%rbx), %eax
	movl	%eax, 40(%rbx)
	movq	64(%rbx), %rax
	testq	%rax, %rax
	je	.L392
	movq	24(%rbx), %rsi
	movq	%rax, 56(%rbx)
	movq	72(%rbx), %rax
	movq	%rsi, 16(%rbx)
	movl	48(%rbx), %esi
	movl	%esi, 44(%rbx)
	testq	%rax, %rax
	je	.L393
	movq	32(%rbx), %rsi
	movq	%rax, 64(%rbx)
	movl	$3, %eax
	movq	%rsi, 24(%rbx)
	movl	52(%rbx), %esi
	movl	%esi, 48(%rbx)
	movl	$2, %esi
.L332:
	movq	$0, 8(%rbx,%rax,8)
	movl	$0, 40(%rbx,%rax,4)
	movl	44(%rdi), %eax
	movq	$0, 56(%rbx,%rsi,8)
	addl	40(%rdi), %eax
	addl	48(%rdi), %eax
	addl	52(%rdi), %eax
	cmpq	$1, 56(%rdi)
	sbbl	$-1, %eax
	cmpq	$1, 64(%rdi)
	sbbl	$-1, %eax
	cmpq	$1, 72(%rdi)
	sbbl	$-1, %eax
	movl	%eax, 40(%r12,%rdx,4)
	movl	44(%rbx), %eax
	addl	40(%rbx), %eax
	addl	48(%rbx), %eax
	addl	52(%rbx), %eax
	cmpq	$1, 56(%rbx)
	sbbl	$-1, %eax
	cmpq	$1, 64(%rbx)
	sbbl	$-1, %eax
	cmpq	$1, 72(%rbx)
	sbbl	$-1, %eax
	movl	%eax, 40(%r12,%rcx,4)
	jmp	.L470
	.p2align 4,,10
	.p2align 3
.L477:
	movq	64(%rax), %rdx
	testq	%rdx, %rdx
	jne	.L365
	movq	56(%rax), %rdx
	jmp	.L365
	.p2align 4,,10
	.p2align 3
.L478:
	testq	%rax, %rax
	jne	.L352
	movq	%r12, %rdi
	movq	%r10, 8(%rsp)
	call	free@PLT
	movq	40(%rsp), %rax
	movq	8(%rsp), %r12
	movq	$0, (%rax)
	jmp	.L311
	.p2align 4,,10
	.p2align 3
.L318:
	movl	$1, %r11d
	testq	%r10, %r10
	jne	.L385
	movq	64(%r12), %r10
	jmp	.L385
.L390:
	xorl	%r13d, %r13d
	movl	$1, %edx
.L322:
	movslq	%r13d, %rbp
	movq	8(%r12,%rbp,8), %rdi
	cmpq	$0, 64(%rdi)
	je	.L482
.L379:
	cmpq	$1, 72(%rdi)
	movq	16(%rbx), %rax
	sbbl	%r8d, %r8d
	addl	$3, %r8d
	cmpq	$1, 72(%rdi)
	movq	%rax, 24(%rbx)
	movl	44(%rbx), %eax
	movslq	%r8d, %r8
	sbbl	%ecx, %ecx
	movq	8(%rdi,%r8,8), %r9
	addl	$2, %ecx
	movl	%eax, 48(%rbx)
	movq	56(%rbx), %rax
	movq	%r9, %xmm0
	movq	%rax, 64(%rbx)
	movq	56(%r12,%rbp,8), %rsi
	movhps	8(%rbx), %xmm0
	movl	40(%rbx), %eax
	movups	%xmm0, 8(%rbx)
	movq	%rsi, 56(%rbx)
	movl	40(%rdi,%r8,4), %esi
	movd	%eax, %xmm1
	movd	%esi, %xmm0
	punpckldq	%xmm1, %xmm0
	movq	%xmm0, 40(%rbx)
	testq	%r9, %r9
	je	.L324
	movq	%rbx, (%r9)
.L324:
	movslq	%ecx, %rcx
	addq	$6, %rcx
	movq	8(%rdi,%rcx,8), %r9
	movq	%r9, 56(%r12,%rbp,8)
	movq	$0, 8(%rdi,%r8,8)
	movl	$0, 40(%rdi,%r8,4)
	addl	48(%rbx), %eax
	movq	$0, 8(%rdi,%rcx,8)
	addl	52(%rbx), %eax
	addl	%esi, %eax
	cmpq	$1, 56(%rbx)
	sbbl	$-1, %eax
	cmpq	$1, 64(%rbx)
	sbbl	$-1, %eax
	cmpq	$1, 72(%rbx)
	sbbl	$-1, %eax
	movl	%eax, 40(%r12,%rdx,4)
	addl	40(%r12,%rbp,4), %r15d
	movl	44(%rdi), %eax
	addl	40(%rdi), %eax
	addl	48(%rdi), %eax
	addl	52(%rdi), %eax
	cmpq	$1, 56(%rdi)
	sbbl	$-1, %eax
	cmpq	$1, 64(%rdi)
	sbbl	$-1, %eax
	cmpq	$1, 72(%rdi)
	sbbl	$-1, %eax
	movl	%eax, 40(%r12,%rbp,4)
	subl	%eax, %r15d
	movq	%rbx, %r12
	jmp	.L312
.L469:
	xorl	%r13d, %r13d
	xorl	%ebp, %ebp
	movl	$1, %edx
.L339:
	movq	16(%rbx), %rax
	movq	16(%rdi), %rcx
	leaq	(%r12,%rbp,8), %r14
	movq	56(%rbx), %rsi
	movl	44(%rdi), %r8d
	movq	%rax, 32(%rbx)
	movl	40(%rbx), %r9d
	movq	%rcx, %xmm0
	movl	44(%rbx), %eax
	movhps	8(%rbx), %xmm0
	movq	%rsi, 8(%rsp)
	movq	%rsi, 72(%rbx)
	movd	%r9d, %xmm2
	movl	%eax, 52(%rbx)
	movq	56(%r14), %rsi
	movups	%xmm0, 16(%rbx)
	movd	%r8d, %xmm0
	punpckldq	%xmm2, %xmm0
	movl	%r9d, 16(%rsp)
	movq	%rsi, 64(%rbx)
	movl	%r8d, 24(%rsp)
	movq	%xmm0, 44(%rbx)
	testq	%rcx, %rcx
	je	.L340
	movq	%rbx, (%rcx)
.L340:
	movq	56(%rdi), %r8
	movq	8(%rdi), %rcx
	movl	40(%rdi), %r9d
	movq	%r8, 56(%rbx)
	movq	%rcx, 8(%rbx)
	movl	%r9d, 40(%rbx)
	testq	%rcx, %rcx
	je	.L341
	movq	%rbx, (%rcx)
.L341:
	addl	16(%rsp), %eax
	addl	24(%rsp), %eax
	movq	%r10, 32(%rsp)
	addl	%r9d, %eax
	cmpq	$1, %r8
	movl	%r11d, 28(%rsp)
	sbbl	$-1, %eax
	cmpq	$1, %rsi
	sbbl	$-1, %eax
	cmpq	$1, 8(%rsp)
	sbbl	$-1, %eax
	movl	%eax, 40(%r12,%rdx,4)
	call	free@PLT
	leal	1(%r13), %esi
	movl	28(%rsp), %r11d
	movq	32(%rsp), %r10
	movslq	%esi, %rcx
	leaq	(%r12,%rcx,8), %rax
	movq	8(%rax), %rdx
	testq	%rdx, %rdx
	je	.L345
	leaq	8(%rcx), %rdi
	movq	%rdx, 8(%r14)
	movl	8(%r12,%rdi,4), %edx
	movl	%edx, 40(%r12,%rbp,4)
	cmpl	$2, %r13d
	je	.L346
	movq	56(%rax), %rdx
	movq	%rdx, 56(%r14)
	leal	2(%r13), %edx
	movslq	%edx, %rdx
	leaq	(%r12,%rdx,8), %r8
	movq	8(%r8), %r9
	testq	%r9, %r9
	je	.L394
	movq	%r9, 8(%rax)
	movl	40(%r12,%rdx,4), %edx
	movl	%edx, 8(%r12,%rdi,4)
	cmpl	$2, %esi
	je	.L346
	movq	56(%r8), %rdx
	movq	%rdx, 56(%rax)
	movq	32(%r12), %rax
	testq	%rax, %rax
	je	.L395
	movq	%rax, 8(%r8)
	movl	52(%r12), %eax
	movl	%eax, 48(%r12)
.L346:
	movq	$0, 72(%r12)
	movq	$0, 32(%r12)
	movl	$0, 52(%r12)
.L378:
	cmpq	$0, 56(%r12)
	jne	.L396
	movq	40(%rsp), %rax
	movq	%r12, %rdi
	movq	%r10, 16(%rsp)
	movq	%rbx, %r12
	movl	%r11d, 8(%rsp)
	movq	%rbx, (%rax)
	movq	$0, (%rbx)
	call	free@PLT
	movl	8(%rsp), %r11d
	movq	16(%rsp), %r10
	jmp	.L312
.L394:
	movq	%rcx, %rbp
.L345:
	movq	$0, 8(%r12,%rbp,8)
	movl	$0, 40(%r12,%rbp,4)
	movq	$0, 56(%r12,%rbp,8)
	jmp	.L378
.L319:
	movq	24(%r12), %rbx
	cmpq	$0, 64(%rbx)
	jne	.L396
	movl	$1, %r13d
	movl	$2, %edx
	jmp	.L322
.L481:
	movq	40(%rsp), %rax
	movq	%r12, %rdi
	movq	%r10, 16(%rsp)
	movl	%r11d, 8(%rsp)
	movq	%rbx, (%rax)
	movq	$0, (%rbx)
	call	free@PLT
	movq	16(%rsp), %r10
	movl	8(%rsp), %r11d
	jmp	.L377
.L320:
	movl	$2, %r11d
	testq	%r10, %r10
	jne	.L385
	movq	72(%r12), %r10
	jmp	.L385
.L405:
	movl	%r11d, %edx
	jmp	.L374
.L480:
	movl	$1, %edx
	movq	%rax, %r13
	jmp	.L374
.L321:
	movq	24(%r12), %rdi
	cmpq	$0, 64(%rdi)
	jne	.L406
	movl	$2, %r13d
	movl	$2, %ebp
	movl	$3, %edx
	jmp	.L339
.L392:
	movl	$1, %eax
	xorl	%esi, %esi
	jmp	.L332
.L393:
	movl	$2, %eax
	movl	$1, %esi
	jmp	.L332
.L395:
	movl	$2, %ebp
	jmp	.L345
.L479:
	movl	$1, %r11d
	jmp	.L354
.L482:
	leal	1(%rdx), %ecx
	movslq	%ecx, %rcx
	movq	8(%r12,%rcx,8), %rax
	testq	%rax, %rax
	je	.L465
	cmpq	$0, 64(%rax)
	je	.L465
	movq	%rbx, %rdi
	movq	%rax, %rbx
	jmp	.L386
	.p2align 4,,10
	.p2align 3
.L465:
	movl	40(%r12,%rbp,4), %eax
	movq	8(%r12,%rdx,8), %rbx
	leal	1(%r15,%rax), %r15d
	jmp	.L339
.L406:
	movl	%edx, %r15d
	movl	$2, %ebp
	movl	$3, %edx
	jmp	.L379
	.cfi_endproc
.LFE52:
	.size	delpos234_internal, .-delpos234_internal
	.p2align 4
	.globl	newtree234
	.type	newtree234, @function
newtree234:
.LFB39:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset 3, -16
	movq	%rdi, %rbx
	movl	$16, %edi
	call	malloc@PLT
	movq	$0, (%rax)
	movq	%rbx, 8(%rax)
	popq	%rbx
	.cfi_def_cfa_offset 8
	ret
	.cfi_endproc
.LFE39:
	.size	newtree234, .-newtree234
	.p2align 4
	.globl	freetree234
	.type	freetree234, @function
freetree234:
.LFB41:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	pushq	%r13
	.cfi_def_cfa_offset 24
	.cfi_offset 13, -24
	pushq	%r12
	.cfi_def_cfa_offset 32
	.cfi_offset 12, -32
	movq	%rdi, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 40
	.cfi_offset 6, -40
	subq	$8, %rsp
	.cfi_def_cfa_offset 48
	movq	(%rdi), %rbp
	testq	%rbp, %rbp
	je	.L486
	movq	8(%rbp), %r13
	testq	%r13, %r13
	je	.L487
	movq	8(%r13), %r14
	testq	%r14, %r14
	je	.L488
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L488:
	movq	16(%r13), %r14
	testq	%r14, %r14
	je	.L489
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L489:
	movq	24(%r13), %r14
	testq	%r14, %r14
	je	.L490
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L490:
	movq	32(%r13), %r14
	testq	%r14, %r14
	je	.L491
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L491:
	movq	%r13, %rdi
	call	free@PLT
.L487:
	movq	16(%rbp), %r13
	testq	%r13, %r13
	je	.L492
	movq	8(%r13), %r14
	testq	%r14, %r14
	je	.L493
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L493:
	movq	16(%r13), %r14
	testq	%r14, %r14
	je	.L494
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L494:
	movq	24(%r13), %r14
	testq	%r14, %r14
	je	.L495
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L495:
	movq	32(%r13), %r14
	testq	%r14, %r14
	je	.L496
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L496:
	movq	%r13, %rdi
	call	free@PLT
.L492:
	movq	24(%rbp), %r13
	testq	%r13, %r13
	je	.L497
	movq	8(%r13), %r14
	testq	%r14, %r14
	je	.L498
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L498:
	movq	16(%r13), %r14
	testq	%r14, %r14
	je	.L499
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L499:
	movq	24(%r13), %r14
	testq	%r14, %r14
	je	.L500
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L500:
	movq	32(%r13), %r14
	testq	%r14, %r14
	je	.L501
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L501:
	movq	%r13, %rdi
	call	free@PLT
.L497:
	movq	32(%rbp), %r13
	testq	%r13, %r13
	je	.L502
	movq	8(%r13), %r14
	testq	%r14, %r14
	je	.L503
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L503:
	movq	16(%r13), %r14
	testq	%r14, %r14
	je	.L504
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L504:
	movq	24(%r13), %r14
	testq	%r14, %r14
	je	.L505
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L505:
	movq	32(%r13), %r14
	testq	%r14, %r14
	je	.L506
	movq	8(%r14), %rdi
	call	freenode234
	movq	16(%r14), %rdi
	call	freenode234
	movq	24(%r14), %rdi
	call	freenode234
	movq	32(%r14), %rdi
	call	freenode234
	movq	%r14, %rdi
	call	free@PLT
.L506:
	movq	%r13, %rdi
	call	free@PLT
.L502:
	movq	%rbp, %rdi
	call	free@PLT
.L486:
	addq	$8, %rsp
	.cfi_def_cfa_offset 40
	movq	%r12, %rdi
	popq	%rbp
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r13
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	jmp	free@PLT
	.cfi_endproc
.LFE41:
	.size	freetree234, .-freetree234
	.p2align 4
	.globl	count234
	.type	count234, @function
count234:
.LFB43:
	.cfi_startproc
	movq	(%rdi), %rdx
	xorl	%eax, %eax
	testq	%rdx, %rdx
	je	.L571
	movl	44(%rdx), %eax
	addl	40(%rdx), %eax
	addl	48(%rdx), %eax
	addl	52(%rdx), %eax
	cmpq	$1, 56(%rdx)
	sbbl	$-1, %eax
	cmpq	$1, 64(%rdx)
	sbbl	$-1, %eax
	cmpq	$1, 72(%rdx)
	sbbl	$-1, %eax
.L571:
	ret
	.cfi_endproc
.LFE43:
	.size	count234, .-count234
	.p2align 4
	.globl	add234
	.type	add234, @function
add234:
.LFB45:
	.cfi_startproc
	cmpq	$0, 8(%rdi)
	je	.L579
	movl	$-1, %edx
	jmp	add234_internal
	.p2align 4,,10
	.p2align 3
.L579:
	xorl	%eax, %eax
	ret
	.cfi_endproc
.LFE45:
	.size	add234, .-add234
	.p2align 4
	.globl	addpos234
	.type	addpos234, @function
addpos234:
.LFB46:
	.cfi_startproc
	testl	%edx, %edx
	js	.L580
	cmpq	$0, 8(%rdi)
	jne	.L580
	jmp	add234_internal
	.p2align 4,,10
	.p2align 3
.L580:
	xorl	%eax, %eax
	ret
	.cfi_endproc
.LFE46:
	.size	addpos234, .-addpos234
	.p2align 4
	.globl	index234
	.type	index234, @function
index234:
.LFB47:
	.cfi_startproc
	movq	(%rdi), %rax
	testq	%rax, %rax
	je	.L598
	testl	%esi, %esi
	js	.L598
	movl	40(%rax), %edx
	movl	44(%rax), %ecx
	addl	%edx, %ecx
	addl	48(%rax), %ecx
	addl	52(%rax), %ecx
	cmpq	$1, 56(%rax)
	sbbl	$-1, %ecx
	cmpq	$1, 64(%rax)
	sbbl	$-1, %ecx
	cmpq	$1, 72(%rax)
	sbbl	$-1, %ecx
	cmpl	%esi, %ecx
	jg	.L596
	jmp	.L598
	.p2align 4,,10
	.p2align 3
.L602:
	movq	8(%rax), %rax
.L590:
	testq	%rax, %rax
	je	.L584
.L604:
	movl	40(%rax), %edx
.L596:
	cmpl	%esi, %edx
	jg	.L602
	subl	$1, %esi
	subl	%edx, %esi
	js	.L603
	movl	44(%rax), %edx
	cmpl	%esi, %edx
	jle	.L592
	movq	16(%rax), %rax
	testq	%rax, %rax
	jne	.L604
.L584:
	ret
	.p2align 4,,10
	.p2align 3
.L592:
	subl	%edx, %esi
	subl	$1, %esi
	js	.L605
	movl	48(%rax), %edx
	cmpl	%esi, %edx
	jle	.L594
	movq	24(%rax), %rax
	jmp	.L590
	.p2align 4,,10
	.p2align 3
.L594:
	subl	%edx, %esi
	subl	$1, %esi
	js	.L606
	movq	32(%rax), %rax
	jmp	.L590
	.p2align 4,,10
	.p2align 3
.L598:
	xorl	%eax, %eax
	ret
	.p2align 4,,10
	.p2align 3
.L603:
	movq	56(%rax), %rax
	ret
.L605:
	movq	64(%rax), %rax
	ret
.L606:
	movq	72(%rax), %rax
	ret
	.cfi_endproc
.LFE47:
	.size	index234, .-index234
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC0:
	.string	"tree234.c"
	.section	.rodata.str1.8,"aMS",@progbits,1
	.align 8
.LC1:
	.string	"relation == REL234_LT || relation == REL234_GT"
	.text
	.p2align 4
	.globl	findrelpos234
	.type	findrelpos234, @function
findrelpos234:
.LFB48:
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
	subq	$40, %rsp
	.cfi_def_cfa_offset 96
	movq	(%rdi), %r15
	movq	%rdi, 16(%rsp)
	movq	%rdx, (%rsp)
	movl	%ecx, 12(%rsp)
	movq	%r8, 24(%rsp)
	testq	%r15, %r15
	je	.L627
	cmpq	$0, (%rsp)
	movq	%rsi, %r12
	je	.L667
.L610:
	xorl	%ebx, %ebx
	testq	%r12, %r12
	je	.L668
.L611:
	xorl	%r13d, %r13d
	jmp	.L629
	.p2align 4,,10
	.p2align 3
.L670:
	cmpq	$0, 56(%r15)
	je	.L636
	movq	8(%r15), %rax
	cmpl	$-1, %ebx
	je	.L636
	testq	%rax, %rax
	je	.L616
	addl	40(%r15), %r13d
.L616:
	addl	$1, %r13d
	cmpq	$0, 64(%r15)
	je	.L638
	cmpq	$0, 16(%r15)
	je	.L617
	addl	44(%r15), %r13d
.L617:
	addl	$1, %r13d
	cmpq	$0, 72(%r15)
	je	.L639
	cmpq	$0, 24(%r15)
	je	.L618
	addl	48(%r15), %r13d
.L618:
	addl	$1, %r13d
.L619:
	movl	$3, %r14d
.L621:
	movslq	%r14d, %r9
	movq	8(%r15,%r9,8), %r15
	testq	%r15, %r15
	je	.L669
.L629:
	testl	%ebx, %ebx
	jne	.L670
	xorl	%ebp, %ebp
.L613:
	movq	56(%r15,%rbp,8), %rsi
	movl	%ebp, %r14d
	testq	%rsi, %rsi
	je	.L621
	movq	(%rsp), %rax
	movq	%r12, %rdi
	call	*%rax
	movq	8(%r15,%rbp,8), %rsi
	testl	%eax, %eax
	js	.L621
	testq	%rsi, %rsi
	je	.L622
	addl	40(%r15,%rbp,4), %r13d
.L622:
	testl	%eax, %eax
	je	.L623
	addq	$1, %rbp
	addl	$1, %r13d
	cmpq	$3, %rbp
	jne	.L613
	jmp	.L619
.L623:
	movl	12(%rsp), %eax
	andl	$-3, %eax
	cmpl	$1, %eax
	jne	.L671
	leal	-1(%r13), %eax
	leal	1(%r13), %ecx
	cmpl	$1, 12(%rsp)
	cmovne	%ecx, %eax
	movl	%eax, %r13d
.L626:
	movq	16(%rsp), %rdi
	movl	%r13d, %esi
	call	index234@PLT
	testq	%rax, %rax
	je	.L607
	movq	24(%rsp), %rdx
	testq	%rdx, %rdx
	je	.L607
	movl	%r13d, (%rdx)
.L607:
	addq	$40, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
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
.L669:
	.cfi_restore_state
	movl	12(%rsp), %eax
	testl	%eax, %eax
	je	.L627
	movl	12(%rsp), %eax
	subl	$1, %eax
	cmpl	$2, %eax
	sbbl	$0, %r13d
	jmp	.L626
.L668:
	movl	12(%rsp), %eax
	andl	$-3, %eax
	cmpl	$1, %eax
	jne	.L672
	xorl	%ebx, %ebx
	cmpl	$1, 12(%rsp)
	sete	%bl
	leal	-1(%rbx,%rbx), %ebx
	jmp	.L611
.L667:
	movq	8(%rdi), %rax
	movq	%rax, (%rsp)
	jmp	.L610
.L636:
	xorl	%r14d, %r14d
	jmp	.L621
.L671:
	movq	24(%rsp), %rax
	testq	%rax, %rax
	je	.L624
	movl	%r13d, (%rax)
.L624:
	movslq	%r14d, %r9
	movq	56(%r15,%r9,8), %rax
	addq	$40, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
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
.L627:
	.cfi_restore_state
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
.L638:
	.cfi_restore_state
	movl	$1, %r14d
	jmp	.L621
.L639:
	movl	$2, %r14d
	jmp	.L621
.L672:
	leaq	__PRETTY_FUNCTION__.0(%rip), %rcx
	movl	$470, %edx
	leaq	.LC0(%rip), %rsi
	leaq	.LC1(%rip), %rdi
	call	__assert_fail@PLT
	.cfi_endproc
.LFE48:
	.size	findrelpos234, .-findrelpos234
	.p2align 4
	.globl	find234
	.type	find234, @function
find234:
.LFB49:
	.cfi_startproc
	xorl	%r8d, %r8d
	xorl	%ecx, %ecx
	jmp	findrelpos234@PLT
	.cfi_endproc
.LFE49:
	.size	find234, .-find234
	.p2align 4
	.globl	findrel234
	.type	findrel234, @function
findrel234:
.LFB50:
	.cfi_startproc
	xorl	%r8d, %r8d
	jmp	findrelpos234@PLT
	.cfi_endproc
.LFE50:
	.size	findrel234, .-findrel234
	.p2align 4
	.globl	findpos234
	.type	findpos234, @function
findpos234:
.LFB51:
	.cfi_startproc
	movq	%rcx, %r8
	xorl	%ecx, %ecx
	jmp	findrelpos234@PLT
	.cfi_endproc
.LFE51:
	.size	findpos234, .-findpos234
	.p2align 4
	.globl	delpos234
	.type	delpos234, @function
delpos234:
.LFB53:
	.cfi_startproc
	testl	%esi, %esi
	js	.L676
	movq	(%rdi), %rdx
	testq	%rdx, %rdx
	je	.L676
	movl	44(%rdx), %eax
	addl	40(%rdx), %eax
	addl	48(%rdx), %eax
	addl	52(%rdx), %eax
	cmpq	$1, 56(%rdx)
	sbbl	$-1, %eax
	cmpq	$1, 64(%rdx)
	sbbl	$-1, %eax
	cmpq	$1, 72(%rdx)
	sbbl	$-1, %eax
	cmpl	%eax, %esi
	jge	.L676
	jmp	delpos234_internal
	.p2align 4,,10
	.p2align 3
.L676:
	xorl	%eax, %eax
	ret
	.cfi_endproc
.LFE53:
	.size	delpos234, .-delpos234
	.p2align 4
	.globl	del234
	.type	del234, @function
del234:
.LFB54:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	xorl	%ecx, %ecx
	xorl	%edx, %edx
	movq	%rdi, %rbp
	subq	$16, %rsp
	.cfi_def_cfa_offset 32
	movq	%fs:40, %rax
	movq	%rax, 8(%rsp)
	xorl	%eax, %eax
	leaq	4(%rsp), %r8
	call	findrelpos234@PLT
	testq	%rax, %rax
	je	.L686
	movl	4(%rsp), %esi
	movq	%rbp, %rdi
	call	delpos234_internal
.L686:
	movq	8(%rsp), %rdx
	subq	%fs:40, %rdx
	jne	.L693
	addq	$16, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	ret
.L693:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE54:
	.size	del234, .-del234
	.section	.rodata
	.align 8
	.type	__PRETTY_FUNCTION__.0, @object
	.size	__PRETTY_FUNCTION__.0, 14
__PRETTY_FUNCTION__.0:
	.string	"findrelpos234"
	.ident	"GCC: (GNU) 11.3.0"
	.section	.note.GNU-stack,"",@progbits
