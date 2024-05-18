	.file	"tree234.c"
	.text
.Ltext0:
	.file 0 "/home/runner/assembly" "tree234.c"
	.globl	newtree234
	.type	newtree234, @function
newtree234:
.LFB6:
	.file 1 "tree234.c"
	.loc 1 62 35
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movq	%rdi, -24(%rbp)
	.loc 1 63 20
	movl	$16, %edi
	call	malloc@PLT
	movq	%rax, -8(%rbp)
	.loc 1 65 15
	movq	-8(%rbp), %rax
	movq	$0, (%rax)
	.loc 1 66 14
	movq	-8(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 8(%rax)
	.loc 1 67 12
	movq	-8(%rbp), %rax
	.loc 1 68 1
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE6:
	.size	newtree234, .-newtree234
	.type	freenode234, @function
freenode234:
.LFB7:
	.loc 1 73 37
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	.loc 1 74 8
	cmpq	$0, -8(%rbp)
	je	.L6
	.loc 1 76 5
	movq	-8(%rbp), %rax
	movq	8(%rax), %rax
	movq	%rax, %rdi
	call	freenode234
	.loc 1 77 5
	movq	-8(%rbp), %rax
	movq	16(%rax), %rax
	movq	%rax, %rdi
	call	freenode234
	.loc 1 78 5
	movq	-8(%rbp), %rax
	movq	24(%rax), %rax
	movq	%rax, %rdi
	call	freenode234
	.loc 1 79 5
	movq	-8(%rbp), %rax
	movq	32(%rax), %rax
	movq	%rax, %rdi
	call	freenode234
	.loc 1 80 5
	movq	-8(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
	jmp	.L3
.L6:
	.loc 1 75 2
	nop
.L3:
	.loc 1 81 1
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
	.loc 1 82 30
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	.loc 1 83 5
	movq	-8(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, %rdi
	call	freenode234
	.loc 1 84 5
	movq	-8(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
	.loc 1 85 1
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
	.loc 1 90 37
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -24(%rbp)
	.loc 1 91 9
	movl	$0, -8(%rbp)
	.loc 1 93 8
	cmpq	$0, -24(%rbp)
	jne	.L9
	.loc 1 94 9
	movl	$0, %eax
	jmp	.L10
.L9:
	.loc 1 95 12
	movl	$0, -4(%rbp)
	.loc 1 95 5
	jmp	.L11
.L12:
	.loc 1 96 20 discriminator 3
	movq	-24(%rbp), %rax
	movl	-4(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %eax
	.loc 1 96 8 discriminator 3
	addl	%eax, -8(%rbp)
	.loc 1 95 25 discriminator 3
	addl	$1, -4(%rbp)
.L11:
	.loc 1 95 19 discriminator 1
	cmpl	$3, -4(%rbp)
	jle	.L12
	.loc 1 97 12
	movl	$0, -4(%rbp)
	.loc 1 97 5
	jmp	.L13
.L15:
	.loc 1 98 14
	movq	-24(%rbp), %rax
	movl	-4(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	.loc 1 98 5
	testq	%rax, %rax
	je	.L14
	.loc 1 99 11
	addl	$1, -8(%rbp)
.L14:
	.loc 1 97 25 discriminator 2
	addl	$1, -4(%rbp)
.L13:
	.loc 1 97 19 discriminator 1
	cmpl	$2, -4(%rbp)
	jle	.L15
	.loc 1 100 12
	movl	-8(%rbp), %eax
.L10:
	.loc 1 101 1
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
	.loc 1 106 26
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$8, %rsp
	movq	%rdi, -8(%rbp)
	.loc 1 107 10
	movq	-8(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 107 8
	testq	%rax, %rax
	je	.L17
	.loc 1 108 9
	movq	-8(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, %rdi
	call	countnode234
	jmp	.L18
.L17:
	.loc 1 110 9
	movl	$0, %eax
.L18:
	.loc 1 111 1
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE10:
	.size	count234, .-count234
	.type	add234_internal, @function
add234_internal:
.LFB11:
	.loc 1 117 62
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
	.loc 1 119 11
	movq	-96(%rbp), %rax
	movq	%rax, -16(%rbp)
	.loc 1 123 10
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 123 8
	testq	%rax, %rax
	jne	.L20
	.loc 1 124 12
	movl	$80, %edi
	call	malloc@PLT
	movq	%rax, %rdx
	.loc 1 124 10
	movq	-88(%rbp), %rax
	movq	%rdx, (%rax)
	.loc 1 125 23
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 125 40
	movq	$0, 72(%rax)
	.loc 1 125 3
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	.loc 1 125 36
	movq	72(%rax), %rax
	.loc 1 125 20
	movq	%rax, 64(%rdx)
	.loc 1 126 22
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 126 38
	movq	$0, 16(%rax)
	.loc 1 126 3
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	.loc 1 126 34
	movq	16(%rax), %rax
	.loc 1 126 19
	movq	%rax, 8(%rdx)
	.loc 1 127 22
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 127 38
	movq	$0, 32(%rax)
	.loc 1 127 3
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	.loc 1 127 34
	movq	32(%rax), %rax
	.loc 1 127 19
	movq	%rax, 24(%rdx)
	.loc 1 128 24
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 128 42
	movl	$0, 44(%rax)
	.loc 1 128 3
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	.loc 1 128 38
	movl	44(%rax), %eax
	.loc 1 128 21
	movl	%eax, 40(%rdx)
	.loc 1 129 24
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 129 42
	movl	$0, 52(%rax)
	.loc 1 129 3
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	.loc 1 129 38
	movl	52(%rax), %eax
	.loc 1 129 21
	movl	%eax, 48(%rdx)
	.loc 1 130 3
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 130 18
	movq	$0, (%rax)
	.loc 1 131 3
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 131 20
	movq	-96(%rbp), %rdx
	movq	%rdx, 56(%rax)
	.loc 1 133 9
	movq	-16(%rbp), %rax
	jmp	.L21
.L20:
	.loc 1 136 8
	movq	-88(%rbp), %rax
	movq	%rax, -40(%rbp)
	.loc 1 137 11
	jmp	.L22
.L39:
.LBB2:
	.loc 1 139 4
	movq	-40(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -48(%rbp)
	.loc 1 146 5
	cmpl	$0, -100(%rbp)
	js	.L23
	.loc 1 147 18
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 147 9
	testq	%rax, %rax
	jne	.L24
	.loc 1 154 12
	movl	-100(%rbp), %eax
	movl	%eax, -64(%rbp)
	jmp	.L30
.L24:
	.loc 1 162 29
	movq	-48(%rbp), %rax
	movl	40(%rax), %eax
	.loc 1 162 10
	cmpl	%eax, -100(%rbp)
	jg	.L26
	.loc 1 163 13
	movl	$0, -64(%rbp)
	.loc 1 164 4
	jmp	.L30
.L26:
	.loc 1 166 25
	movq	-48(%rbp), %rax
	movl	40(%rax), %edx
	.loc 1 166 13
	movl	-100(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -100(%rbp)
	.loc 1 167 29
	movq	-48(%rbp), %rax
	movl	44(%rax), %eax
	.loc 1 167 10
	cmpl	%eax, -100(%rbp)
	jg	.L27
	.loc 1 168 13
	movl	$1, -64(%rbp)
	.loc 1 169 4
	jmp	.L30
.L27:
	.loc 1 171 25
	movq	-48(%rbp), %rax
	movl	44(%rax), %edx
	.loc 1 171 13
	movl	-100(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -100(%rbp)
	.loc 1 172 29
	movq	-48(%rbp), %rax
	movl	48(%rax), %eax
	.loc 1 172 10
	cmpl	%eax, -100(%rbp)
	jg	.L28
	.loc 1 173 13
	movl	$2, -64(%rbp)
	.loc 1 174 4
	jmp	.L30
.L28:
	.loc 1 176 25
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	.loc 1 176 13
	movl	-100(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -100(%rbp)
	.loc 1 177 29
	movq	-48(%rbp), %rax
	movl	52(%rax), %eax
	.loc 1 177 10
	cmpl	%eax, -100(%rbp)
	jg	.L29
	.loc 1 178 13
	movl	$3, -64(%rbp)
	.loc 1 179 4
	jmp	.L30
.L29:
	.loc 1 181 14
	movl	$0, %eax
	jmp	.L21
.L23:
	.loc 1 185 16
	movq	-88(%rbp), %rax
	movq	8(%rax), %rcx
	.loc 1 185 15
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	*%rcx
.LVL0:
	movl	%eax, -52(%rbp)
	.loc 1 185 9
	cmpl	$0, -52(%rbp)
	jns	.L31
	.loc 1 186 12
	movl	$0, -64(%rbp)
	jmp	.L30
.L31:
	.loc 1 187 14
	cmpl	$0, -52(%rbp)
	jne	.L32
	.loc 1 188 18
	movq	-48(%rbp), %rax
	movq	56(%rax), %rax
	jmp	.L21
.L32:
	.loc 1 189 23
	movq	-48(%rbp), %rax
	movq	64(%rax), %rax
	.loc 1 189 14
	testq	%rax, %rax
	je	.L33
	.loc 1 189 44 discriminator 1
	movq	-88(%rbp), %rax
	movq	8(%rax), %rcx
	.loc 1 189 43 discriminator 1
	movq	-48(%rbp), %rax
	movq	64(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	*%rcx
.LVL1:
	movl	%eax, -52(%rbp)
	.loc 1 189 35 discriminator 1
	cmpl	$0, -52(%rbp)
	jns	.L34
.L33:
	.loc 1 190 12
	movl	$1, -64(%rbp)
	jmp	.L30
.L34:
	.loc 1 191 14
	cmpl	$0, -52(%rbp)
	jne	.L35
	.loc 1 192 18
	movq	-48(%rbp), %rax
	movq	64(%rax), %rax
	jmp	.L21
.L35:
	.loc 1 193 23
	movq	-48(%rbp), %rax
	movq	72(%rax), %rax
	.loc 1 193 14
	testq	%rax, %rax
	je	.L36
	.loc 1 193 44 discriminator 1
	movq	-88(%rbp), %rax
	movq	8(%rax), %rcx
	.loc 1 193 43 discriminator 1
	movq	-48(%rbp), %rax
	movq	72(%rax), %rdx
	movq	-96(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	*%rcx
.LVL2:
	movl	%eax, -52(%rbp)
	.loc 1 193 35 discriminator 1
	cmpl	$0, -52(%rbp)
	jns	.L37
.L36:
	.loc 1 194 12
	movl	$2, -64(%rbp)
	jmp	.L30
.L37:
	.loc 1 195 14
	cmpl	$0, -52(%rbp)
	jne	.L38
	.loc 1 196 18
	movq	-48(%rbp), %rax
	movq	72(%rax), %rax
	jmp	.L21
.L38:
	.loc 1 198 12
	movl	$3, -64(%rbp)
.L30:
	.loc 1 200 5
	movl	-64(%rbp), %eax
	cltq
	leaq	0(,%rax,8), %rdx
	movq	-48(%rbp), %rax
	addq	%rdx, %rax
	addq	$8, %rax
	movq	%rax, -40(%rbp)
.L22:
.LBE2:
	.loc 1 137 12
	movq	-40(%rbp), %rax
	movq	(%rax), %rax
	testq	%rax, %rax
	jne	.L39
	.loc 1 207 10
	movq	$0, -32(%rbp)
	.loc 1 207 26
	movl	$0, -72(%rbp)
	.loc 1 208 11
	movq	$0, -24(%rbp)
	.loc 1 208 26
	movl	$0, -68(%rbp)
	.loc 1 209 11
	jmp	.L40
.L72:
	.loc 1 218 14
	movq	-48(%rbp), %rax
	movq	64(%rax), %rax
	.loc 1 218 5
	testq	%rax, %rax
	jne	.L41
	.loc 1 222 16
	movq	-48(%rbp), %rax
	addq	$8, %rax
	.loc 1 222 9
	cmpq	%rax, -40(%rbp)
	jne	.L42
	.loc 1 224 23
	movq	-48(%rbp), %rax
	movq	16(%rax), %rdx
	.loc 1 224 14
	movq	-48(%rbp), %rax
	movq	%rdx, 24(%rax)
	.loc 1 224 56
	movq	-48(%rbp), %rax
	movl	44(%rax), %edx
	.loc 1 224 45
	movq	-48(%rbp), %rax
	movl	%edx, 48(%rax)
	.loc 1 225 25
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	.loc 1 225 15
	movq	-48(%rbp), %rax
	movq	%rdx, 64(%rax)
	.loc 1 226 14
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 16(%rax)
	.loc 1 226 45
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 44(%rax)
	.loc 1 227 15
	movq	-48(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 56(%rax)
	.loc 1 228 14
	movq	-48(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 8(%rax)
	.loc 1 228 45
	movq	-48(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 40(%rax)
	jmp	.L43
.L42:
	.loc 1 231 14
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 24(%rax)
	.loc 1 231 45
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 48(%rax)
	.loc 1 232 15
	movq	-48(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 64(%rax)
	.loc 1 233 14
	movq	-48(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 16(%rax)
	.loc 1 233 45
	movq	-48(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 44(%rax)
.L43:
	.loc 1 235 17
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 235 9
	testq	%rax, %rax
	je	.L44
	.loc 1 235 29 discriminator 1
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 235 41 discriminator 1
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L44:
	.loc 1 236 17
	movq	-48(%rbp), %rax
	movq	16(%rax), %rax
	.loc 1 236 9
	testq	%rax, %rax
	je	.L45
	.loc 1 236 29 discriminator 1
	movq	-48(%rbp), %rax
	movq	16(%rax), %rax
	.loc 1 236 41 discriminator 1
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L45:
	.loc 1 237 17
	movq	-48(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 237 9
	testq	%rax, %rax
	je	.L84
	.loc 1 237 29 discriminator 1
	movq	-48(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 237 41 discriminator 1
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
	.loc 1 239 6 discriminator 1
	jmp	.L84
.L41:
	.loc 1 240 21
	movq	-48(%rbp), %rax
	movq	72(%rax), %rax
	.loc 1 240 12
	testq	%rax, %rax
	jne	.L48
	.loc 1 244 16
	movq	-48(%rbp), %rax
	addq	$8, %rax
	.loc 1 244 9
	cmpq	%rax, -40(%rbp)
	jne	.L49
	.loc 1 246 23
	movq	-48(%rbp), %rax
	movq	24(%rax), %rdx
	.loc 1 246 14
	movq	-48(%rbp), %rax
	movq	%rdx, 32(%rax)
	.loc 1 246 55
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	.loc 1 246 44
	movq	-48(%rbp), %rax
	movl	%edx, 52(%rax)
	.loc 1 247 25
	movq	-48(%rbp), %rax
	movq	64(%rax), %rdx
	.loc 1 247 15
	movq	-48(%rbp), %rax
	movq	%rdx, 72(%rax)
	.loc 1 248 23
	movq	-48(%rbp), %rax
	movq	16(%rax), %rdx
	.loc 1 248 14
	movq	-48(%rbp), %rax
	movq	%rdx, 24(%rax)
	.loc 1 248 55
	movq	-48(%rbp), %rax
	movl	44(%rax), %edx
	.loc 1 248 44
	movq	-48(%rbp), %rax
	movl	%edx, 48(%rax)
	.loc 1 249 25
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	.loc 1 249 15
	movq	-48(%rbp), %rax
	movq	%rdx, 64(%rax)
	.loc 1 250 14
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 16(%rax)
	.loc 1 250 44
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 44(%rax)
	.loc 1 251 15
	movq	-48(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 56(%rax)
	.loc 1 252 14
	movq	-48(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 8(%rax)
	.loc 1 252 44
	movq	-48(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 40(%rax)
	jmp	.L50
.L49:
	.loc 1 253 23
	movq	-48(%rbp), %rax
	addq	$16, %rax
	.loc 1 253 16
	cmpq	%rax, -40(%rbp)
	jne	.L51
	.loc 1 255 23
	movq	-48(%rbp), %rax
	movq	24(%rax), %rdx
	.loc 1 255 14
	movq	-48(%rbp), %rax
	movq	%rdx, 32(%rax)
	.loc 1 255 55
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	.loc 1 255 44
	movq	-48(%rbp), %rax
	movl	%edx, 52(%rax)
	.loc 1 256 25
	movq	-48(%rbp), %rax
	movq	64(%rax), %rdx
	.loc 1 256 15
	movq	-48(%rbp), %rax
	movq	%rdx, 72(%rax)
	.loc 1 257 14
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 24(%rax)
	.loc 1 257 44
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 48(%rax)
	.loc 1 258 15
	movq	-48(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 64(%rax)
	.loc 1 259 14
	movq	-48(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 16(%rax)
	.loc 1 259 44
	movq	-48(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 44(%rax)
	jmp	.L50
.L51:
	.loc 1 262 14
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 32(%rax)
	.loc 1 262 44
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 52(%rax)
	.loc 1 263 15
	movq	-48(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 72(%rax)
	.loc 1 264 14
	movq	-48(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 24(%rax)
	.loc 1 264 44
	movq	-48(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 48(%rax)
.L50:
	.loc 1 266 17
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 266 9
	testq	%rax, %rax
	je	.L52
	.loc 1 266 29 discriminator 1
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 266 41 discriminator 1
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L52:
	.loc 1 267 17
	movq	-48(%rbp), %rax
	movq	16(%rax), %rax
	.loc 1 267 9
	testq	%rax, %rax
	je	.L53
	.loc 1 267 29 discriminator 1
	movq	-48(%rbp), %rax
	movq	16(%rax), %rax
	.loc 1 267 41 discriminator 1
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L53:
	.loc 1 268 17
	movq	-48(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 268 9
	testq	%rax, %rax
	je	.L54
	.loc 1 268 29 discriminator 1
	movq	-48(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 268 41 discriminator 1
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L54:
	.loc 1 269 17
	movq	-48(%rbp), %rax
	movq	32(%rax), %rax
	.loc 1 269 9
	testq	%rax, %rax
	je	.L85
	.loc 1 269 29 discriminator 1
	movq	-48(%rbp), %rax
	movq	32(%rax), %rax
	.loc 1 269 41 discriminator 1
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
	.loc 1 271 6 discriminator 1
	jmp	.L85
.L48:
.LBB3:
	.loc 1 273 19
	movl	$80, %edi
	call	malloc@PLT
	movq	%rax, -8(%rbp)
	.loc 1 274 19
	movq	-48(%rbp), %rax
	movq	(%rax), %rdx
	.loc 1 274 16
	movq	-8(%rbp), %rax
	movq	%rdx, (%rax)
	.loc 1 284 16
	movq	-48(%rbp), %rax
	addq	$8, %rax
	.loc 1 284 9
	cmpq	%rax, -40(%rbp)
	jne	.L56
	.loc 1 285 14
	movq	-8(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 8(%rax)
	.loc 1 285 44
	movq	-8(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 40(%rax)
	.loc 1 286 15
	movq	-8(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 56(%rax)
	.loc 1 287 14
	movq	-8(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 16(%rax)
	.loc 1 287 44
	movq	-8(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 44(%rax)
	.loc 1 288 25
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	.loc 1 288 15
	movq	-8(%rbp), %rax
	movq	%rdx, 64(%rax)
	.loc 1 289 23
	movq	-48(%rbp), %rax
	movq	16(%rax), %rdx
	.loc 1 289 14
	movq	-8(%rbp), %rax
	movq	%rdx, 24(%rax)
	.loc 1 289 55
	movq	-48(%rbp), %rax
	movl	44(%rax), %edx
	.loc 1 289 44
	movq	-8(%rbp), %rax
	movl	%edx, 48(%rax)
	.loc 1 290 5
	movq	-48(%rbp), %rax
	movq	64(%rax), %rax
	movq	%rax, -96(%rbp)
	.loc 1 291 23
	movq	-48(%rbp), %rax
	movq	24(%rax), %rdx
	.loc 1 291 14
	movq	-48(%rbp), %rax
	movq	%rdx, 8(%rax)
	.loc 1 291 55
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	.loc 1 291 44
	movq	-48(%rbp), %rax
	movl	%edx, 40(%rax)
	.loc 1 292 25
	movq	-48(%rbp), %rax
	movq	72(%rax), %rdx
	.loc 1 292 15
	movq	-48(%rbp), %rax
	movq	%rdx, 56(%rax)
	.loc 1 293 23
	movq	-48(%rbp), %rax
	movq	32(%rax), %rdx
	.loc 1 293 14
	movq	-48(%rbp), %rax
	movq	%rdx, 16(%rax)
	.loc 1 293 55
	movq	-48(%rbp), %rax
	movl	52(%rax), %edx
	.loc 1 293 44
	movq	-48(%rbp), %rax
	movl	%edx, 44(%rax)
	jmp	.L57
.L56:
	.loc 1 294 23
	movq	-48(%rbp), %rax
	addq	$16, %rax
	.loc 1 294 16
	cmpq	%rax, -40(%rbp)
	jne	.L58
	.loc 1 295 23
	movq	-48(%rbp), %rax
	movq	8(%rax), %rdx
	.loc 1 295 14
	movq	-8(%rbp), %rax
	movq	%rdx, 8(%rax)
	.loc 1 295 55
	movq	-48(%rbp), %rax
	movl	40(%rax), %edx
	.loc 1 295 44
	movq	-8(%rbp), %rax
	movl	%edx, 40(%rax)
	.loc 1 296 25
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	.loc 1 296 15
	movq	-8(%rbp), %rax
	movq	%rdx, 56(%rax)
	.loc 1 297 14
	movq	-8(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 16(%rax)
	.loc 1 297 44
	movq	-8(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 44(%rax)
	.loc 1 298 15
	movq	-8(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 64(%rax)
	.loc 1 299 14
	movq	-8(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 24(%rax)
	.loc 1 299 44
	movq	-8(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 48(%rax)
	.loc 1 300 5
	movq	-48(%rbp), %rax
	movq	64(%rax), %rax
	movq	%rax, -96(%rbp)
	.loc 1 301 23
	movq	-48(%rbp), %rax
	movq	24(%rax), %rdx
	.loc 1 301 14
	movq	-48(%rbp), %rax
	movq	%rdx, 8(%rax)
	.loc 1 301 55
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	.loc 1 301 44
	movq	-48(%rbp), %rax
	movl	%edx, 40(%rax)
	.loc 1 302 25
	movq	-48(%rbp), %rax
	movq	72(%rax), %rdx
	.loc 1 302 15
	movq	-48(%rbp), %rax
	movq	%rdx, 56(%rax)
	.loc 1 303 23
	movq	-48(%rbp), %rax
	movq	32(%rax), %rdx
	.loc 1 303 14
	movq	-48(%rbp), %rax
	movq	%rdx, 16(%rax)
	.loc 1 303 55
	movq	-48(%rbp), %rax
	movl	52(%rax), %edx
	.loc 1 303 44
	movq	-48(%rbp), %rax
	movl	%edx, 44(%rax)
	jmp	.L57
.L58:
	.loc 1 304 23
	movq	-48(%rbp), %rax
	addq	$24, %rax
	.loc 1 304 16
	cmpq	%rax, -40(%rbp)
	jne	.L59
	.loc 1 305 23
	movq	-48(%rbp), %rax
	movq	8(%rax), %rdx
	.loc 1 305 14
	movq	-8(%rbp), %rax
	movq	%rdx, 8(%rax)
	.loc 1 305 55
	movq	-48(%rbp), %rax
	movl	40(%rax), %edx
	.loc 1 305 44
	movq	-8(%rbp), %rax
	movl	%edx, 40(%rax)
	.loc 1 306 25
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	.loc 1 306 15
	movq	-8(%rbp), %rax
	movq	%rdx, 56(%rax)
	.loc 1 307 23
	movq	-48(%rbp), %rax
	movq	16(%rax), %rdx
	.loc 1 307 14
	movq	-8(%rbp), %rax
	movq	%rdx, 16(%rax)
	.loc 1 307 55
	movq	-48(%rbp), %rax
	movl	44(%rax), %edx
	.loc 1 307 44
	movq	-8(%rbp), %rax
	movl	%edx, 44(%rax)
	.loc 1 308 25
	movq	-48(%rbp), %rax
	movq	64(%rax), %rdx
	.loc 1 308 15
	movq	-8(%rbp), %rax
	movq	%rdx, 64(%rax)
	.loc 1 309 14
	movq	-8(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 24(%rax)
	.loc 1 309 44
	movq	-8(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 48(%rax)
	.loc 1 311 14
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 8(%rax)
	.loc 1 311 44
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 40(%rax)
	.loc 1 312 25
	movq	-48(%rbp), %rax
	movq	72(%rax), %rdx
	.loc 1 312 15
	movq	-48(%rbp), %rax
	movq	%rdx, 56(%rax)
	.loc 1 313 23
	movq	-48(%rbp), %rax
	movq	32(%rax), %rdx
	.loc 1 313 14
	movq	-48(%rbp), %rax
	movq	%rdx, 16(%rax)
	.loc 1 313 55
	movq	-48(%rbp), %rax
	movl	52(%rax), %edx
	.loc 1 313 44
	movq	-48(%rbp), %rax
	movl	%edx, 44(%rax)
	jmp	.L57
.L59:
	.loc 1 315 23
	movq	-48(%rbp), %rax
	movq	8(%rax), %rdx
	.loc 1 315 14
	movq	-8(%rbp), %rax
	movq	%rdx, 8(%rax)
	.loc 1 315 55
	movq	-48(%rbp), %rax
	movl	40(%rax), %edx
	.loc 1 315 44
	movq	-8(%rbp), %rax
	movl	%edx, 40(%rax)
	.loc 1 316 25
	movq	-48(%rbp), %rax
	movq	56(%rax), %rdx
	.loc 1 316 15
	movq	-8(%rbp), %rax
	movq	%rdx, 56(%rax)
	.loc 1 317 23
	movq	-48(%rbp), %rax
	movq	16(%rax), %rdx
	.loc 1 317 14
	movq	-8(%rbp), %rax
	movq	%rdx, 16(%rax)
	.loc 1 317 55
	movq	-48(%rbp), %rax
	movl	44(%rax), %edx
	.loc 1 317 44
	movq	-8(%rbp), %rax
	movl	%edx, 44(%rax)
	.loc 1 318 25
	movq	-48(%rbp), %rax
	movq	64(%rax), %rdx
	.loc 1 318 15
	movq	-8(%rbp), %rax
	movq	%rdx, 64(%rax)
	.loc 1 319 23
	movq	-48(%rbp), %rax
	movq	24(%rax), %rdx
	.loc 1 319 14
	movq	-8(%rbp), %rax
	movq	%rdx, 24(%rax)
	.loc 1 319 55
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	.loc 1 319 44
	movq	-8(%rbp), %rax
	movl	%edx, 48(%rax)
	.loc 1 320 14
	movq	-48(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 8(%rax)
	.loc 1 320 44
	movq	-48(%rbp), %rax
	movl	-72(%rbp), %edx
	movl	%edx, 40(%rax)
	.loc 1 321 15
	movq	-48(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, 56(%rax)
	.loc 1 322 14
	movq	-48(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 16(%rax)
	.loc 1 322 44
	movq	-48(%rbp), %rax
	movl	-68(%rbp), %edx
	movl	%edx, 44(%rax)
	.loc 1 323 5
	movq	-48(%rbp), %rax
	movq	72(%rax), %rax
	movq	%rax, -96(%rbp)
.L57:
	.loc 1 325 43
	movq	-48(%rbp), %rax
	movq	$0, 24(%rax)
	.loc 1 325 39
	movq	-48(%rbp), %rax
	movq	24(%rax), %rdx
	.loc 1 325 30
	movq	-48(%rbp), %rax
	movq	%rdx, 32(%rax)
	.loc 1 325 26
	movq	-48(%rbp), %rax
	movq	32(%rax), %rdx
	.loc 1 325 17
	movq	-8(%rbp), %rax
	movq	%rdx, 32(%rax)
	.loc 1 326 49
	movq	-48(%rbp), %rax
	movl	$0, 48(%rax)
	.loc 1 326 45
	movq	-48(%rbp), %rax
	movl	48(%rax), %edx
	.loc 1 326 34
	movq	-48(%rbp), %rax
	movl	%edx, 52(%rax)
	.loc 1 326 30
	movq	-48(%rbp), %rax
	movl	52(%rax), %edx
	.loc 1 326 19
	movq	-8(%rbp), %rax
	movl	%edx, 52(%rax)
	.loc 1 327 46
	movq	-48(%rbp), %rax
	movq	$0, 64(%rax)
	.loc 1 327 42
	movq	-48(%rbp), %rax
	movq	64(%rax), %rdx
	.loc 1 327 32
	movq	-48(%rbp), %rax
	movq	%rdx, 72(%rax)
	.loc 1 327 28
	movq	-48(%rbp), %rax
	movq	72(%rax), %rdx
	.loc 1 327 18
	movq	-8(%rbp), %rax
	movq	%rdx, 72(%rax)
	.loc 1 328 17
	movq	-8(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 328 9
	testq	%rax, %rax
	je	.L60
	.loc 1 328 29 discriminator 1
	movq	-8(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 328 41 discriminator 1
	movq	-8(%rbp), %rdx
	movq	%rdx, (%rax)
.L60:
	.loc 1 329 17
	movq	-8(%rbp), %rax
	movq	16(%rax), %rax
	.loc 1 329 9
	testq	%rax, %rax
	je	.L61
	.loc 1 329 29 discriminator 1
	movq	-8(%rbp), %rax
	movq	16(%rax), %rax
	.loc 1 329 41 discriminator 1
	movq	-8(%rbp), %rdx
	movq	%rdx, (%rax)
.L61:
	.loc 1 330 17
	movq	-8(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 330 9
	testq	%rax, %rax
	je	.L62
	.loc 1 330 29 discriminator 1
	movq	-8(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 330 41 discriminator 1
	movq	-8(%rbp), %rdx
	movq	%rdx, (%rax)
.L62:
	.loc 1 331 17
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 331 9
	testq	%rax, %rax
	je	.L63
	.loc 1 331 29 discriminator 1
	movq	-48(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 331 41 discriminator 1
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L63:
	.loc 1 332 17
	movq	-48(%rbp), %rax
	movq	16(%rax), %rax
	.loc 1 332 9
	testq	%rax, %rax
	je	.L64
	.loc 1 332 29 discriminator 1
	movq	-48(%rbp), %rax
	movq	16(%rax), %rax
	.loc 1 332 41 discriminator 1
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L64:
	.loc 1 340 11
	movq	-8(%rbp), %rax
	movq	%rax, -32(%rbp)
	.loc 1 340 26
	movq	-32(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	movl	%eax, -72(%rbp)
	.loc 1 341 12
	movq	-48(%rbp), %rax
	movq	%rax, -24(%rbp)
	.loc 1 341 26
	movq	-24(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	movl	%eax, -68(%rbp)
.LBE3:
	.loc 1 343 7
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 343 5
	testq	%rax, %rax
	je	.L65
	.loc 1 344 13
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 344 27
	movq	8(%rax), %rax
	.loc 1 344 58
	cmpq	%rax, -48(%rbp)
	jne	.L66
	.loc 1 344 40 discriminator 1
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 344 58 discriminator 1
	addq	$8, %rax
	jmp	.L67
.L66:
	.loc 1 345 6
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 345 20
	movq	16(%rax), %rax
	.loc 1 345 51
	cmpq	%rax, -48(%rbp)
	jne	.L68
	.loc 1 345 33 discriminator 1
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 345 51 discriminator 1
	addq	$16, %rax
	jmp	.L67
.L68:
	.loc 1 346 6
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 346 20
	movq	24(%rax), %rax
	.loc 1 346 51
	cmpq	%rax, -48(%rbp)
	jne	.L70
	.loc 1 346 33 discriminator 1
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 346 51 discriminator 1
	addq	$24, %rax
	jmp	.L67
.L70:
	.loc 1 347 7 discriminator 2
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 346 51 discriminator 2
	addq	$32, %rax
.L67:
	.loc 1 344 9 discriminator 2
	movq	%rax, -40(%rbp)
.L65:
	.loc 1 348 4
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -48(%rbp)
.L40:
	.loc 1 209 12
	cmpq	$0, -48(%rbp)
	jne	.L72
	jmp	.L47
.L84:
	.loc 1 239 6
	nop
	jmp	.L47
.L85:
	.loc 1 271 6
	nop
.L47:
	.loc 1 357 8
	cmpq	$0, -48(%rbp)
	je	.L73
	.loc 1 358 8
	jmp	.L74
.L81:
.LBB4:
	.loc 1 359 18
	movq	-48(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	movl	%eax, -60(%rbp)
	.loc 1 361 19
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 361 33
	movq	8(%rax), %rax
	.loc 1 361 46
	cmpq	%rax, -48(%rbp)
	je	.L75
	.loc 1 362 5
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 362 19
	movq	16(%rax), %rax
	.loc 1 362 32
	cmpq	%rax, -48(%rbp)
	je	.L76
	.loc 1 363 5
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 363 19
	movq	24(%rax), %rax
	.loc 1 363 32
	cmpq	%rax, -48(%rbp)
	jne	.L77
	.loc 1 363 32 is_stmt 0 discriminator 1
	movl	$2, %eax
	jmp	.L80
.L77:
	.loc 1 363 32 discriminator 2
	movl	$3, %eax
	jmp	.L80
.L76:
	.loc 1 362 32 is_stmt 1 discriminator 1
	movl	$1, %eax
	jmp	.L80
.L75:
	.loc 1 361 46 discriminator 1
	movl	$0, %eax
.L80:
	.loc 1 361 15 discriminator 3
	movl	%eax, -56(%rbp)
	.loc 1 364 7 discriminator 3
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 364 34 discriminator 3
	movl	-56(%rbp), %edx
	movslq	%edx, %rdx
	leaq	8(%rdx), %rcx
	movl	-60(%rbp), %edx
	movl	%edx, 8(%rax,%rcx,4)
	.loc 1 365 8 discriminator 3
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -48(%rbp)
.L74:
.LBE4:
	.loc 1 358 10
	movq	-48(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 358 9
	testq	%rax, %rax
	jne	.L81
	jmp	.L82
.L73:
	.loc 1 369 12
	movl	$80, %edi
	call	malloc@PLT
	movq	%rax, %rdx
	.loc 1 369 10
	movq	-88(%rbp), %rax
	movq	%rdx, (%rax)
	.loc 1 370 3
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 370 19
	movq	-32(%rbp), %rdx
	movq	%rdx, 8(%rax)
	.loc 1 370 32
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 370 50
	movl	-72(%rbp), %edx
	movl	%edx, 40(%rax)
	.loc 1 371 3
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 371 20
	movq	-96(%rbp), %rdx
	movq	%rdx, 56(%rax)
	.loc 1 372 3
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 372 19
	movq	-24(%rbp), %rdx
	movq	%rdx, 16(%rax)
	.loc 1 372 32
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 372 50
	movl	-68(%rbp), %edx
	movl	%edx, 44(%rax)
	.loc 1 373 3
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 373 20
	movq	$0, 64(%rax)
	.loc 1 374 3
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 374 19
	movq	$0, 24(%rax)
	.loc 1 374 32
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 374 50
	movl	$0, 48(%rax)
	.loc 1 375 3
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 375 20
	movq	$0, 72(%rax)
	.loc 1 376 3
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 376 19
	movq	$0, 32(%rax)
	.loc 1 376 32
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 376 50
	movl	$0, 52(%rax)
	.loc 1 377 3
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 377 18
	movq	$0, (%rax)
	.loc 1 378 7
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 378 19
	movq	8(%rax), %rax
	.loc 1 378 5
	testq	%rax, %rax
	je	.L83
	.loc 1 378 25 discriminator 1
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 378 37 discriminator 1
	movq	8(%rax), %rax
	.loc 1 378 52 discriminator 1
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	.loc 1 378 49 discriminator 1
	movq	%rdx, (%rax)
.L83:
	.loc 1 379 7
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 379 19
	movq	16(%rax), %rax
	.loc 1 379 5
	testq	%rax, %rax
	je	.L82
	.loc 1 379 25 discriminator 1
	movq	-88(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 379 37 discriminator 1
	movq	16(%rax), %rax
	.loc 1 379 52 discriminator 1
	movq	-88(%rbp), %rdx
	movq	(%rdx), %rdx
	.loc 1 379 49 discriminator 1
	movq	%rdx, (%rax)
.L82:
	.loc 1 386 12
	movq	-16(%rbp), %rax
.L21:
	.loc 1 387 1
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
	.loc 1 389 35
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	movq	%rsi, -16(%rbp)
	.loc 1 390 11
	movq	-8(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 390 8
	testq	%rax, %rax
	jne	.L87
	.loc 1 391 9
	movl	$0, %eax
	jmp	.L88
.L87:
	.loc 1 393 12
	movq	-16(%rbp), %rcx
	movq	-8(%rbp), %rax
	movl	$-1, %edx
	movq	%rcx, %rsi
	movq	%rax, %rdi
	call	add234_internal
.L88:
	.loc 1 394 1
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
	.loc 1 395 49
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
	.loc 1 396 8
	cmpl	$0, -20(%rbp)
	js	.L90
	.loc 1 397 3 discriminator 1
	movq	-8(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 396 19 discriminator 1
	testq	%rax, %rax
	je	.L91
.L90:
	.loc 1 398 9
	movl	$0, %eax
	jmp	.L92
.L91:
	.loc 1 400 12
	movl	-20(%rbp), %edx
	movq	-16(%rbp), %rcx
	movq	-8(%rbp), %rax
	movq	%rcx, %rsi
	movq	%rax, %rdi
	call	add234_internal
.L92:
	.loc 1 401 1
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
	.loc 1 407 39
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movq	%rdi, -24(%rbp)
	movl	%esi, -28(%rbp)
	.loc 1 410 11
	movq	-24(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 410 8
	testq	%rax, %rax
	jne	.L94
	.loc 1 411 9
	movl	$0, %eax
	jmp	.L95
.L94:
	.loc 1 413 8
	cmpl	$0, -28(%rbp)
	js	.L96
	.loc 1 413 31 discriminator 1
	movq	-24(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, %rdi
	call	countnode234
	.loc 1 413 19 discriminator 1
	cmpl	%eax, -28(%rbp)
	jl	.L97
.L96:
	.loc 1 414 9
	movl	$0, %eax
	jmp	.L95
.L97:
	.loc 1 416 7
	movq	-24(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -8(%rbp)
	.loc 1 418 11
	jmp	.L98
.L105:
	.loc 1 419 23
	movq	-8(%rbp), %rax
	movl	40(%rax), %eax
	.loc 1 419 5
	cmpl	%eax, -28(%rbp)
	jge	.L99
	.loc 1 420 8
	movq	-8(%rbp), %rax
	movq	8(%rax), %rax
	movq	%rax, -8(%rbp)
	jmp	.L98
.L99:
	.loc 1 421 29
	movq	-8(%rbp), %rax
	movl	40(%rax), %edx
	.loc 1 421 17
	movl	-28(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -28(%rbp)
	.loc 1 421 11
	movl	-28(%rbp), %eax
	shrl	$31, %eax
	andl	$1, %eax
	.loc 1 421 10
	testb	%al, %al
	je	.L100
	.loc 1 422 21
	movq	-8(%rbp), %rax
	movq	56(%rax), %rax
	jmp	.L95
.L100:
	.loc 1 423 28
	movq	-8(%rbp), %rax
	movl	44(%rax), %eax
	.loc 1 423 10
	cmpl	%eax, -28(%rbp)
	jge	.L101
	.loc 1 424 8
	movq	-8(%rbp), %rax
	movq	16(%rax), %rax
	movq	%rax, -8(%rbp)
	jmp	.L98
.L101:
	.loc 1 425 29
	movq	-8(%rbp), %rax
	movl	44(%rax), %edx
	.loc 1 425 17
	movl	-28(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -28(%rbp)
	.loc 1 425 11
	movl	-28(%rbp), %eax
	shrl	$31, %eax
	andl	$1, %eax
	.loc 1 425 10
	testb	%al, %al
	je	.L102
	.loc 1 426 21
	movq	-8(%rbp), %rax
	movq	64(%rax), %rax
	jmp	.L95
.L102:
	.loc 1 427 28
	movq	-8(%rbp), %rax
	movl	48(%rax), %eax
	.loc 1 427 10
	cmpl	%eax, -28(%rbp)
	jge	.L103
	.loc 1 428 8
	movq	-8(%rbp), %rax
	movq	24(%rax), %rax
	movq	%rax, -8(%rbp)
	jmp	.L98
.L103:
	.loc 1 429 29
	movq	-8(%rbp), %rax
	movl	48(%rax), %edx
	.loc 1 429 17
	movl	-28(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -28(%rbp)
	.loc 1 429 11
	movl	-28(%rbp), %eax
	shrl	$31, %eax
	andl	$1, %eax
	.loc 1 429 10
	testb	%al, %al
	je	.L104
	.loc 1 430 21
	movq	-8(%rbp), %rax
	movq	72(%rax), %rax
	jmp	.L95
.L104:
	.loc 1 432 8
	movq	-8(%rbp), %rax
	movq	32(%rax), %rax
	movq	%rax, -8(%rbp)
.L98:
	.loc 1 418 12
	cmpq	$0, -8(%rbp)
	jne	.L105
	.loc 1 436 12
	movl	$0, %eax
.L95:
	.loc 1 437 1
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
	.loc 1 447 33
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
	.loc 1 453 10
	movq	-56(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 453 8
	testq	%rax, %rax
	jne	.L107
	.loc 1 454 9
	movl	$0, %eax
	jmp	.L108
.L107:
	.loc 1 456 8
	cmpq	$0, -72(%rbp)
	jne	.L109
	.loc 1 457 6
	movq	-56(%rbp), %rax
	movq	8(%rax), %rax
	movq	%rax, -72(%rbp)
.L109:
	.loc 1 459 7
	movq	-56(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -16(%rbp)
	.loc 1 463 9
	movl	$0, -36(%rbp)
	.loc 1 464 12
	movl	$-1, -32(%rbp)
	.loc 1 468 12
	movl	$0, -24(%rbp)
	.loc 1 469 8
	cmpq	$0, -64(%rbp)
	jne	.L124
	.loc 1 470 2
	cmpl	$1, -76(%rbp)
	je	.L111
	.loc 1 470 2 is_stmt 0 discriminator 1
	cmpl	$3, -76(%rbp)
	je	.L111
	.loc 1 470 2 discriminator 2
	leaq	__PRETTY_FUNCTION__.0(%rip), %rax
	movq	%rax, %rcx
	movl	$470, %edx
	leaq	.LC0(%rip), %rax
	movq	%rax, %rsi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	call	__assert_fail@PLT
.L111:
	.loc 1 471 5 is_stmt 1
	cmpl	$1, -76(%rbp)
	jne	.L112
	.loc 1 472 13
	movl	$1, -24(%rbp)
	jmp	.L124
.L112:
	.loc 1 473 10
	cmpl	$3, -76(%rbp)
	jne	.L124
	.loc 1 474 13
	movl	$-1, -24(%rbp)
.L124:
	.loc 1 477 14
	movl	$0, -28(%rbp)
	.loc 1 477 2
	jmp	.L113
.L119:
	.loc 1 478 9
	cmpl	$2, -28(%rbp)
	jg	.L114
	.loc 1 478 33 discriminator 1
	movq	-16(%rbp), %rax
	movl	-28(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	.loc 1 478 22 discriminator 1
	testq	%rax, %rax
	je	.L114
	.loc 1 479 24
	cmpl	$0, -24(%rbp)
	jne	.L115
	.loc 1 479 26 discriminator 1
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
.LVL3:
	jmp	.L116
.L115:
	.loc 1 479 24 discriminator 2
	movl	-24(%rbp), %eax
.L116:
	.loc 1 479 6 discriminator 4
	movl	%eax, -20(%rbp)
	.loc 1 478 50 discriminator 4
	cmpl	$0, -20(%rbp)
	js	.L114
	.loc 1 482 17
	movq	-16(%rbp), %rax
	movl	-28(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	.loc 1 482 9
	testq	%rax, %rax
	je	.L117
	.loc 1 482 43 discriminator 1
	movq	-16(%rbp), %rax
	movl	-28(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %eax
	.loc 1 482 31 discriminator 1
	addl	%eax, -36(%rbp)
.L117:
	.loc 1 483 9
	cmpl	$0, -20(%rbp)
	jne	.L118
	.loc 1 484 10
	movl	-28(%rbp), %eax
	movl	%eax, -32(%rbp)
	.loc 1 485 3
	jmp	.L114
.L118:
	.loc 1 487 9 discriminator 2
	addl	$1, -36(%rbp)
	.loc 1 477 37 discriminator 2
	addl	$1, -28(%rbp)
.L113:
	.loc 1 477 26 discriminator 1
	cmpl	$3, -28(%rbp)
	jle	.L119
.L114:
	.loc 1 489 5
	cmpl	$0, -32(%rbp)
	jns	.L133
	.loc 1 491 13
	movq	-16(%rbp), %rax
	movl	-28(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	.loc 1 491 5
	testq	%rax, %rax
	je	.L134
	.loc 1 492 8
	movq	-16(%rbp), %rax
	movl	-28(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -16(%rbp)
	.loc 1 477 14
	jmp	.L124
.L133:
	.loc 1 490 6
	nop
	jmp	.L121
.L134:
	.loc 1 494 6
	nop
.L121:
	.loc 1 497 8
	cmpl	$0, -32(%rbp)
	js	.L125
	.loc 1 503 5
	cmpl	$1, -76(%rbp)
	je	.L126
	.loc 1 503 28 discriminator 1
	cmpl	$3, -76(%rbp)
	je	.L126
	.loc 1 504 9
	cmpq	$0, -88(%rbp)
	je	.L127
	.loc 1 504 24 discriminator 1
	movq	-88(%rbp), %rax
	movl	-36(%rbp), %edx
	movl	%edx, (%rax)
.L127:
	.loc 1 505 21
	movq	-16(%rbp), %rax
	movl	-32(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	jmp	.L108
.L126:
	.loc 1 514 5
	cmpl	$1, -76(%rbp)
	jne	.L128
	.loc 1 515 9
	subl	$1, -36(%rbp)
	jmp	.L129
.L128:
	.loc 1 517 9
	addl	$1, -36(%rbp)
	jmp	.L129
.L125:
	.loc 1 528 5
	cmpl	$0, -76(%rbp)
	jne	.L130
	.loc 1 529 13
	movl	$0, %eax
	jmp	.L108
.L130:
	.loc 1 536 5
	cmpl	$1, -76(%rbp)
	je	.L131
	.loc 1 536 28 discriminator 1
	cmpl	$2, -76(%rbp)
	jne	.L129
.L131:
	.loc 1 537 9
	subl	$1, -36(%rbp)
.L129:
	.loc 1 546 11
	movl	-36(%rbp), %edx
	movq	-56(%rbp), %rax
	movl	%edx, %esi
	movq	%rax, %rdi
	call	index234@PLT
	movq	%rax, -8(%rbp)
	.loc 1 547 8
	cmpq	$0, -8(%rbp)
	je	.L132
	.loc 1 547 13 discriminator 1
	cmpq	$0, -88(%rbp)
	je	.L132
	.loc 1 547 30 discriminator 2
	movq	-88(%rbp), %rax
	movl	-36(%rbp), %edx
	movl	%edx, (%rax)
.L132:
	.loc 1 548 12
	movq	-8(%rbp), %rax
.L108:
	.loc 1 549 1
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
	.loc 1 550 50
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
	.loc 1 551 12
	movq	-24(%rbp), %rdx
	movq	-16(%rbp), %rsi
	movq	-8(%rbp), %rax
	movl	$0, %r8d
	movl	$0, %ecx
	movq	%rax, %rdi
	call	findrelpos234@PLT
	.loc 1 552 1
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
	.loc 1 553 67
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
	.loc 1 554 12
	movl	-28(%rbp), %ecx
	movq	-24(%rbp), %rdx
	movq	-16(%rbp), %rsi
	movq	-8(%rbp), %rax
	movl	$0, %r8d
	movq	%rax, %rdi
	call	findrelpos234@PLT
	.loc 1 555 1
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
	.loc 1 556 65
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
	.loc 1 557 12
	movq	-32(%rbp), %rcx
	movq	-24(%rbp), %rdx
	movq	-16(%rbp), %rsi
	movq	-8(%rbp), %rax
	movq	%rcx, %r8
	movl	$0, %ecx
	movq	%rax, %rdi
	call	findrelpos234@PLT
	.loc 1 558 1
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE18:
	.size	findpos234, .-findpos234
	.type	delpos234_internal, @function
delpos234_internal:
.LFB19:
	.loc 1 564 56
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
	.loc 1 567 9
	movl	$-1, -144(%rbp)
	.loc 1 569 12
	movq	$0, -104(%rbp)
	.loc 1 571 7
	movq	-152(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -112(%rbp)
	.loc 1 574 8
	jmp	.L142
.L170:
.LBB5:
	.loc 1 585 27
	movq	-112(%rbp), %rax
	movl	40(%rax), %eax
	.loc 1 585 9
	cmpl	%eax, -156(%rbp)
	jge	.L143
	.loc 1 586 6
	movl	$0, -140(%rbp)
	jmp	.L144
.L143:
	.loc 1 587 35
	movq	-112(%rbp), %rax
	movl	40(%rax), %edx
	.loc 1 587 23
	movl	-156(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -156(%rbp)
	.loc 1 587 17
	movl	-156(%rbp), %eax
	shrl	$31, %eax
	andl	$1, %eax
	.loc 1 587 16
	testb	%al, %al
	je	.L145
	.loc 1 588 6
	movl	$0, -144(%rbp)
	.loc 1 588 11
	jmp	.L146
.L145:
	.loc 1 589 34
	movq	-112(%rbp), %rax
	movl	44(%rax), %eax
	.loc 1 589 16
	cmpl	%eax, -156(%rbp)
	jge	.L147
	.loc 1 590 6
	movl	$1, -140(%rbp)
	jmp	.L144
.L147:
	.loc 1 591 35
	movq	-112(%rbp), %rax
	movl	44(%rax), %edx
	.loc 1 591 23
	movl	-156(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -156(%rbp)
	.loc 1 591 17
	movl	-156(%rbp), %eax
	shrl	$31, %eax
	andl	$1, %eax
	.loc 1 591 16
	testb	%al, %al
	je	.L148
	.loc 1 592 6
	movl	$1, -144(%rbp)
	.loc 1 592 11
	jmp	.L146
.L148:
	.loc 1 593 34
	movq	-112(%rbp), %rax
	movl	48(%rax), %eax
	.loc 1 593 16
	cmpl	%eax, -156(%rbp)
	jge	.L149
	.loc 1 594 6
	movl	$2, -140(%rbp)
	jmp	.L144
.L149:
	.loc 1 595 35
	movq	-112(%rbp), %rax
	movl	48(%rax), %edx
	.loc 1 595 23
	movl	-156(%rbp), %eax
	subl	%edx, %eax
	subl	$1, %eax
	movl	%eax, -156(%rbp)
	.loc 1 595 17
	movl	-156(%rbp), %eax
	shrl	$31, %eax
	andl	$1, %eax
	.loc 1 595 16
	testb	%al, %al
	je	.L150
	.loc 1 596 6
	movl	$2, -144(%rbp)
	.loc 1 596 11
	jmp	.L146
.L150:
	.loc 1 598 6
	movl	$3, -140(%rbp)
.L144:
	.loc 1 605 10
	movq	-112(%rbp), %rax
	movl	-140(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -96(%rbp)
	.loc 1 606 21
	movq	-96(%rbp), %rax
	movq	64(%rax), %rax
	.loc 1 606 9
	testq	%rax, %rax
	jne	.L151
	.loc 1 608 6
	cmpl	$0, -140(%rbp)
	jle	.L152
	.loc 1 608 27 discriminator 1
	movl	-140(%rbp), %eax
	leal	-1(%rax), %edx
	.loc 1 608 24 discriminator 1
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	.loc 1 608 37 discriminator 1
	movq	64(%rax), %rax
	.loc 1 608 14 discriminator 1
	testq	%rax, %rax
	je	.L152
.LBB6:
	.loc 1 619 32
	movl	-140(%rbp), %eax
	leal	-1(%rax), %edx
	.loc 1 619 16
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -72(%rbp)
	.loc 1 620 33
	movq	-72(%rbp), %rax
	movq	72(%rax), %rax
	.loc 1 620 41
	testq	%rax, %rax
	jne	.L153
	.loc 1 621 19 discriminator 1
	movq	-72(%rbp), %rax
	movq	64(%rax), %rax
	.loc 1 621 27 discriminator 1
	testq	%rax, %rax
	setne	%al
	.loc 1 620 41 discriminator 1
	movzbl	%al, %eax
	jmp	.L154
.L153:
	.loc 1 620 41 is_stmt 0 discriminator 2
	movl	$2, %eax
.L154:
	.loc 1 620 11 is_stmt 1 discriminator 4
	movl	%eax, -120(%rbp)
	.loc 1 622 31 discriminator 4
	movq	-96(%rbp), %rax
	movq	16(%rax), %rdx
	.loc 1 622 20 discriminator 4
	movq	-96(%rbp), %rax
	movq	%rdx, 24(%rax)
	.loc 1 623 35 discriminator 4
	movq	-96(%rbp), %rax
	movl	44(%rax), %edx
	.loc 1 623 22 discriminator 4
	movq	-96(%rbp), %rax
	movl	%edx, 48(%rax)
	.loc 1 624 33 discriminator 4
	movq	-96(%rbp), %rax
	movq	56(%rax), %rdx
	.loc 1 624 21 discriminator 4
	movq	-96(%rbp), %rax
	movq	%rdx, 64(%rax)
	.loc 1 625 31 discriminator 4
	movq	-96(%rbp), %rax
	movq	8(%rax), %rdx
	.loc 1 625 20 discriminator 4
	movq	-96(%rbp), %rax
	movq	%rdx, 16(%rax)
	.loc 1 626 35 discriminator 4
	movq	-96(%rbp), %rax
	movl	40(%rax), %edx
	.loc 1 626 22 discriminator 4
	movq	-96(%rbp), %rax
	movl	%edx, 44(%rax)
	.loc 1 627 34 discriminator 4
	movl	-140(%rbp), %eax
	leal	-1(%rax), %edx
	.loc 1 627 31 discriminator 4
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	.loc 1 627 21 discriminator 4
	movq	-96(%rbp), %rax
	movq	%rdx, 56(%rax)
	.loc 1 628 40 discriminator 4
	movl	-120(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 628 31 discriminator 4
	movq	-72(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rdx
	.loc 1 628 20 discriminator 4
	movq	-96(%rbp), %rax
	movq	%rdx, 8(%rax)
	.loc 1 629 44 discriminator 4
	movl	-120(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 629 35 discriminator 4
	movq	-72(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %edx
	.loc 1 629 22 discriminator 4
	movq	-96(%rbp), %rax
	movl	%edx, 40(%rax)
	.loc 1 630 20 discriminator 4
	movq	-96(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 630 10 discriminator 4
	testq	%rax, %rax
	je	.L155
	.loc 1 630 34 discriminator 1
	movq	-96(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 630 46 discriminator 1
	movq	-96(%rbp), %rdx
	movq	%rdx, (%rax)
.L155:
	.loc 1 631 18
	movl	-140(%rbp), %eax
	leal	-1(%rax), %ecx
	.loc 1 631 34
	movq	-72(%rbp), %rax
	movl	-120(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	.loc 1 631 22
	movq	-112(%rbp), %rax
	movslq	%ecx, %rcx
	addq	$6, %rcx
	movq	%rdx, 8(%rax,%rcx,8)
	.loc 1 632 25
	movl	-120(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 632 29
	movq	-72(%rbp), %rax
	movslq	%edx, %rdx
	movq	$0, 8(%rax,%rdx,8)
	.loc 1 633 27
	movl	-120(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 633 31
	movq	-72(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	$0, 8(%rax,%rdx,4)
	.loc 1 634 28
	movq	-72(%rbp), %rax
	movl	-120(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	$0, 8(%rax,%rdx,8)
	.loc 1 635 23
	movq	-96(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	.loc 1 635 21
	movq	-112(%rbp), %rdx
	movl	-140(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$8, %rcx
	movl	%eax, 8(%rdx,%rcx,4)
	.loc 1 639 28
	movl	-140(%rbp), %eax
	leal	-1(%rax), %edx
	.loc 1 639 25
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %eax
	.loc 1 639 13
	addl	%eax, -156(%rbp)
	.loc 1 640 19
	movl	-140(%rbp), %eax
	leal	-1(%rax), %ebx
	.loc 1 640 25
	movq	-72(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	.loc 1 640 23
	movq	-112(%rbp), %rdx
	movslq	%ebx, %rcx
	addq	$8, %rcx
	movl	%eax, 8(%rdx,%rcx,4)
	.loc 1 641 28
	movl	-140(%rbp), %eax
	leal	-1(%rax), %edx
	.loc 1 641 25
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %eax
	.loc 1 641 13
	subl	%eax, -156(%rbp)
.LBE6:
	.loc 1 608 42
	jmp	.L151
.L152:
	.loc 1 644 13
	cmpl	$2, -140(%rbp)
	jg	.L156
	.loc 1 644 34 discriminator 1
	movl	-140(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 644 31 discriminator 1
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	.loc 1 644 21 discriminator 1
	testq	%rax, %rax
	je	.L156
	.loc 1 645 17 discriminator 2
	movl	-140(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 645 14 discriminator 2
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	.loc 1 645 27 discriminator 2
	movq	64(%rax), %rax
	.loc 1 644 38 discriminator 2
	testq	%rax, %rax
	je	.L156
.LBB7:
	.loc 1 655 32
	movl	-140(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 655 16
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -64(%rbp)
	.loc 1 657 31
	movq	-112(%rbp), %rax
	movl	-140(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	.loc 1 657 21
	movq	-96(%rbp), %rax
	movq	%rdx, 64(%rax)
	.loc 1 658 31
	movq	-64(%rbp), %rax
	movq	8(%rax), %rdx
	.loc 1 658 20
	movq	-96(%rbp), %rax
	movq	%rdx, 24(%rax)
	.loc 1 659 35
	movq	-64(%rbp), %rax
	movl	40(%rax), %edx
	.loc 1 659 22
	movq	-96(%rbp), %rax
	movl	%edx, 48(%rax)
	.loc 1 660 20
	movq	-96(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 660 10
	testq	%rax, %rax
	je	.L157
	.loc 1 660 34 discriminator 1
	movq	-96(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 660 46 discriminator 1
	movq	-96(%rbp), %rdx
	movq	%rdx, (%rax)
.L157:
	.loc 1 661 32
	movq	-64(%rbp), %rax
	movq	56(%rax), %rdx
	.loc 1 661 20
	movq	-112(%rbp), %rax
	movl	-140(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$6, %rcx
	movq	%rdx, 8(%rax,%rcx,8)
	.loc 1 662 31
	movq	-64(%rbp), %rax
	movq	16(%rax), %rdx
	.loc 1 662 20
	movq	-64(%rbp), %rax
	movq	%rdx, 8(%rax)
	.loc 1 663 35
	movq	-64(%rbp), %rax
	movl	44(%rax), %edx
	.loc 1 663 22
	movq	-64(%rbp), %rax
	movl	%edx, 40(%rax)
	.loc 1 664 14
	movl	$0, -136(%rbp)
	.loc 1 664 7
	jmp	.L158
.L160:
	.loc 1 665 32 discriminator 4
	movl	-136(%rbp), %eax
	leal	2(%rax), %edx
	.loc 1 665 15 discriminator 4
	movl	-136(%rbp), %eax
	leal	1(%rax), %esi
	.loc 1 665 30 discriminator 4
	movq	-64(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rcx
	.loc 1 665 19 discriminator 4
	movq	-64(%rbp), %rax
	movslq	%esi, %rdx
	movq	%rcx, 8(%rax,%rdx,8)
	.loc 1 666 36 discriminator 4
	movl	-136(%rbp), %eax
	leal	2(%rax), %edx
	.loc 1 666 17 discriminator 4
	movl	-136(%rbp), %eax
	leal	1(%rax), %ecx
	.loc 1 666 34 discriminator 4
	movq	-64(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %edx
	.loc 1 666 21 discriminator 4
	movq	-64(%rbp), %rax
	movslq	%ecx, %rcx
	addq	$8, %rcx
	movl	%edx, 8(%rax,%rcx,4)
	.loc 1 667 32 discriminator 4
	movl	-136(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 667 30 discriminator 4
	movq	-64(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	.loc 1 667 18 discriminator 4
	movq	-64(%rbp), %rax
	movl	-136(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$6, %rcx
	movq	%rdx, 8(%rax,%rcx,8)
	.loc 1 664 46 discriminator 4
	addl	$1, -136(%rbp)
.L158:
	.loc 1 664 25 discriminator 1
	cmpl	$1, -136(%rbp)
	jg	.L159
	.loc 1 664 40 discriminator 3
	movl	-136(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 664 38 discriminator 3
	movq	-64(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	.loc 1 664 25 discriminator 3
	testq	%rax, %rax
	jne	.L160
.L159:
	.loc 1 669 18
	movl	-136(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 669 22
	movq	-64(%rbp), %rax
	movslq	%edx, %rdx
	movq	$0, 8(%rax,%rdx,8)
	.loc 1 670 20
	movl	-136(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 670 24
	movq	-64(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	$0, 8(%rax,%rdx,4)
	.loc 1 671 21
	movq	-64(%rbp), %rax
	movl	-136(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	$0, 8(%rax,%rdx,8)
	.loc 1 672 23
	movq	-96(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	.loc 1 672 21
	movq	-112(%rbp), %rdx
	movl	-140(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$8, %rcx
	movl	%eax, 8(%rdx,%rcx,4)
	.loc 1 673 19
	movl	-140(%rbp), %eax
	leal	1(%rax), %ebx
	.loc 1 673 25
	movq	-64(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	.loc 1 673 23
	movq	-112(%rbp), %rdx
	movslq	%ebx, %rcx
	addq	$8, %rcx
	movl	%eax, 8(%rdx,%rcx,4)
.LBE7:
	.loc 1 645 32
	jmp	.L151
.L156:
.LBB8:
	.loc 1 698 10
	cmpl	$0, -140(%rbp)
	jle	.L161
	.loc 1 699 6
	subl	$1, -140(%rbp)
	.loc 1 700 22
	movq	-112(%rbp), %rax
	movl	-140(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %edx
	.loc 1 700 10
	movl	-156(%rbp), %eax
	addl	%edx, %eax
	addl	$1, %eax
	movl	%eax, -156(%rbp)
.L161:
	.loc 1 702 11
	movq	-112(%rbp), %rax
	movl	-140(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -56(%rbp)
	.loc 1 703 23
	movl	-140(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 703 11
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -96(%rbp)
	.loc 1 705 31
	movq	-96(%rbp), %rax
	movq	16(%rax), %rdx
	.loc 1 705 20
	movq	-96(%rbp), %rax
	movq	%rdx, 32(%rax)
	.loc 1 706 35
	movq	-96(%rbp), %rax
	movl	44(%rax), %edx
	.loc 1 706 22
	movq	-96(%rbp), %rax
	movl	%edx, 52(%rax)
	.loc 1 707 33
	movq	-96(%rbp), %rax
	movq	56(%rax), %rdx
	.loc 1 707 21
	movq	-96(%rbp), %rax
	movq	%rdx, 72(%rax)
	.loc 1 708 31
	movq	-96(%rbp), %rax
	movq	8(%rax), %rdx
	.loc 1 708 20
	movq	-96(%rbp), %rax
	movq	%rdx, 24(%rax)
	.loc 1 709 35
	movq	-96(%rbp), %rax
	movl	40(%rax), %edx
	.loc 1 709 22
	movq	-96(%rbp), %rax
	movl	%edx, 48(%rax)
	.loc 1 710 31
	movq	-112(%rbp), %rax
	movl	-140(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	.loc 1 710 21
	movq	-96(%rbp), %rax
	movq	%rdx, 64(%rax)
	.loc 1 711 31
	movq	-56(%rbp), %rax
	movq	16(%rax), %rdx
	.loc 1 711 20
	movq	-96(%rbp), %rax
	movq	%rdx, 16(%rax)
	.loc 1 712 35
	movq	-56(%rbp), %rax
	movl	44(%rax), %edx
	.loc 1 712 22
	movq	-96(%rbp), %rax
	movl	%edx, 44(%rax)
	.loc 1 713 20
	movq	-96(%rbp), %rax
	movq	16(%rax), %rax
	.loc 1 713 10
	testq	%rax, %rax
	je	.L162
	.loc 1 713 34 discriminator 1
	movq	-96(%rbp), %rax
	movq	16(%rax), %rax
	.loc 1 713 46 discriminator 1
	movq	-96(%rbp), %rdx
	movq	%rdx, (%rax)
.L162:
	.loc 1 714 33
	movq	-56(%rbp), %rax
	movq	56(%rax), %rdx
	.loc 1 714 21
	movq	-96(%rbp), %rax
	movq	%rdx, 56(%rax)
	.loc 1 715 31
	movq	-56(%rbp), %rax
	movq	8(%rax), %rdx
	.loc 1 715 20
	movq	-96(%rbp), %rax
	movq	%rdx, 8(%rax)
	.loc 1 716 35
	movq	-56(%rbp), %rax
	movl	40(%rax), %edx
	.loc 1 716 22
	movq	-96(%rbp), %rax
	movl	%edx, 40(%rax)
	.loc 1 717 20
	movq	-96(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 717 10
	testq	%rax, %rax
	je	.L163
	.loc 1 717 34 discriminator 1
	movq	-96(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 717 46 discriminator 1
	movq	-96(%rbp), %rdx
	movq	%rdx, (%rax)
.L163:
	.loc 1 719 19
	movl	-140(%rbp), %eax
	leal	1(%rax), %ebx
	.loc 1 719 25
	movq	-96(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	.loc 1 719 23
	movq	-112(%rbp), %rdx
	movslq	%ebx, %rcx
	addq	$8, %rcx
	movl	%eax, 8(%rdx,%rcx,4)
	.loc 1 721 7
	movq	-56(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
	.loc 1 727 14
	movl	-140(%rbp), %eax
	movl	%eax, -132(%rbp)
	.loc 1 727 7
	jmp	.L164
.L168:
	.loc 1 728 26
	movl	-132(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 728 24
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rcx
	.loc 1 728 15
	movq	-112(%rbp), %rax
	movl	-132(%rbp), %edx
	movslq	%edx, %rdx
	movq	%rcx, 8(%rax,%rdx,8)
	.loc 1 729 30
	movl	-132(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 729 28
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %edx
	.loc 1 729 17
	movq	-112(%rbp), %rax
	movl	-132(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$8, %rcx
	movl	%edx, 8(%rax,%rcx,4)
	.loc 1 730 38
	cmpl	$1, -132(%rbp)
	jg	.L165
	.loc 1 730 34 discriminator 1
	movl	-132(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 730 38 discriminator 1
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	jmp	.L166
.L165:
	.loc 1 730 38 is_stmt 0 discriminator 2
	movl	$0, %eax
.L166:
	.loc 1 730 16 is_stmt 1 discriminator 4
	movq	-112(%rbp), %rdx
	movl	-132(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$6, %rcx
	movq	%rax, 8(%rdx,%rcx,8)
	.loc 1 727 44 discriminator 4
	addl	$1, -132(%rbp)
.L164:
	.loc 1 727 26 discriminator 2
	cmpl	$2, -132(%rbp)
	jg	.L167
	.loc 1 727 38 discriminator 3
	movl	-132(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 727 36 discriminator 3
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	.loc 1 727 26 discriminator 3
	testq	%rax, %rax
	jne	.L168
.L167:
	.loc 1 732 18
	movq	-112(%rbp), %rax
	movl	-132(%rbp), %edx
	movslq	%edx, %rdx
	movq	$0, 8(%rax,%rdx,8)
	.loc 1 733 20
	movq	-112(%rbp), %rax
	movl	-132(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	$0, 8(%rax,%rdx,4)
	.loc 1 734 10
	cmpl	$2, -132(%rbp)
	jg	.L169
	.loc 1 734 30 discriminator 1
	movq	-112(%rbp), %rax
	movl	-132(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	$0, 8(%rax,%rdx,8)
.L169:
	.loc 1 737 20
	movq	-112(%rbp), %rax
	movq	56(%rax), %rax
	.loc 1 737 10
	testq	%rax, %rax
	jne	.L151
	.loc 1 743 12
	movq	-152(%rbp), %rax
	movq	-96(%rbp), %rdx
	movq	%rdx, (%rax)
	.loc 1 744 16
	movq	-96(%rbp), %rax
	movq	$0, (%rax)
	.loc 1 745 4
	movq	-112(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
.L151:
.LBE8:
	.loc 1 749 8
	movq	-96(%rbp), %rax
	movq	%rax, -112(%rbp)
.L142:
.LBE5:
	.loc 1 574 9
	cmpq	$0, -112(%rbp)
	jne	.L170
.L146:
	.loc 1 751 5
	cmpq	$0, -104(%rbp)
	jne	.L171
	.loc 1 752 13
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -104(%rbp)
.L171:
	.loc 1 754 5
	cmpl	$-1, -144(%rbp)
	jne	.L172
	.loc 1 755 13
	movl	$0, %eax
	jmp	.L173
.L172:
	.loc 1 762 8
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 762 5
	testq	%rax, %rax
	jne	.L174
	.loc 1 762 29 discriminator 1
	movq	-112(%rbp), %rax
	movq	64(%rax), %rax
	.loc 1 762 17 discriminator 1
	testq	%rax, %rax
	jne	.L174
	.loc 1 762 44 discriminator 2
	movq	-112(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 762 33 discriminator 2
	testq	%rax, %rax
	jne	.L174
	.loc 1 764 6
	movq	-112(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
	.loc 1 765 14
	movq	-152(%rbp), %rax
	movq	$0, (%rax)
	.loc 1 766 13
	movq	-104(%rbp), %rax
	jmp	.L173
.L174:
	.loc 1 775 14
	movq	-112(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 775 5
	testq	%rax, %rax
	jne	.L175
	.loc 1 775 29 discriminator 1
	movq	-112(%rbp), %rax
	movq	64(%rax), %rax
	.loc 1 775 18 discriminator 1
	testq	%rax, %rax
	je	.L175
.LBB9:
	.loc 1 783 13
	movl	-144(%rbp), %eax
	movl	%eax, -128(%rbp)
	.loc 1 783 6
	jmp	.L176
.L178:
	.loc 1 784 27 discriminator 4
	movl	-128(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 784 25 discriminator 4
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	.loc 1 784 15 discriminator 4
	movq	-112(%rbp), %rax
	movl	-128(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$6, %rcx
	movq	%rdx, 8(%rax,%rcx,8)
	.loc 1 783 44 discriminator 4
	addl	$1, -128(%rbp)
.L176:
	.loc 1 783 25 discriminator 1
	cmpl	$1, -128(%rbp)
	jg	.L177
	.loc 1 783 38 discriminator 3
	movl	-128(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 783 36 discriminator 3
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	.loc 1 783 25 discriminator 3
	testq	%rax, %rax
	jne	.L178
.L177:
	.loc 1 785 18
	movq	-112(%rbp), %rax
	movl	-128(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	$0, 8(%rax,%rdx,8)
	.loc 1 790 12
	jmp	.L179
.L186:
.LBB10:
	.loc 1 792 16
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 792 30
	movq	8(%rax), %rax
	.loc 1 792 43
	cmpq	%rax, -112(%rbp)
	je	.L180
	.loc 1 793 9
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 793 23
	movq	16(%rax), %rax
	.loc 1 793 36
	cmpq	%rax, -112(%rbp)
	je	.L181
	.loc 1 794 9
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 794 23
	movq	24(%rax), %rax
	.loc 1 794 36
	cmpq	%rax, -112(%rbp)
	jne	.L182
	.loc 1 794 36 is_stmt 0 discriminator 1
	movl	$2, %eax
	jmp	.L185
.L182:
	.loc 1 794 36 discriminator 2
	movl	$3, %eax
	jmp	.L185
.L181:
	.loc 1 793 36 is_stmt 1 discriminator 1
	movl	$1, %eax
	jmp	.L185
.L180:
	.loc 1 792 43 discriminator 1
	movl	$0, %eax
.L185:
	.loc 1 792 12 discriminator 3
	movl	%eax, -116(%rbp)
	.loc 1 795 4 discriminator 3
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 795 20 discriminator 3
	movl	-116(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %edx
	.loc 1 795 30 discriminator 3
	leal	-1(%rdx), %ecx
	movl	-116(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	%ecx, 8(%rax,%rdx,4)
	.loc 1 796 5 discriminator 3
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, -112(%rbp)
.L179:
.LBE10:
	.loc 1 790 14
	movq	-112(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 790 13
	testq	%rax, %rax
	jne	.L186
	.loc 1 798 13
	movq	-104(%rbp), %rax
	jmp	.L173
.L175:
.LBE9:
	.loc 1 799 20
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	.loc 1 799 31
	movq	64(%rax), %rax
	.loc 1 799 12
	testq	%rax, %rax
	je	.L187
.LBB11:
	.loc 1 808 15
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -88(%rbp)
	.loc 1 811 12
	jmp	.L188
.L195:
	.loc 1 812 15
	movq	-88(%rbp), %rax
	movq	32(%rax), %rax
	.loc 1 812 32
	testq	%rax, %rax
	je	.L189
	.loc 1 812 32 is_stmt 0 discriminator 1
	movq	-88(%rbp), %rax
	movq	32(%rax), %rax
	jmp	.L190
.L189:
	.loc 1 813 15 is_stmt 1
	movq	-88(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 813 32
	testq	%rax, %rax
	je	.L191
	.loc 1 813 32 is_stmt 0 discriminator 1
	movq	-88(%rbp), %rax
	movq	24(%rax), %rax
	jmp	.L190
.L191:
	.loc 1 814 15 is_stmt 1
	movq	-88(%rbp), %rax
	movq	16(%rax), %rax
	.loc 1 814 32
	testq	%rax, %rax
	je	.L193
	.loc 1 814 32 is_stmt 0 discriminator 1
	movq	-88(%rbp), %rax
	movq	16(%rax), %rax
	jmp	.L190
.L193:
	.loc 1 814 32 discriminator 2
	movq	-88(%rbp), %rax
	movq	8(%rax), %rax
.L190:
	.loc 1 812 5 is_stmt 1 discriminator 2
	movq	%rax, -88(%rbp)
.L188:
	.loc 1 811 20
	movq	-88(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 811 13
	testq	%rax, %rax
	jne	.L195
	.loc 1 816 24
	movq	-88(%rbp), %rax
	movq	72(%rax), %rax
	.loc 1 816 42
	testq	%rax, %rax
	je	.L196
	.loc 1 816 42 is_stmt 0 discriminator 1
	movq	-88(%rbp), %rax
	movq	72(%rax), %rax
	jmp	.L197
.L196:
	.loc 1 817 17 is_stmt 1
	movq	-88(%rbp), %rax
	movq	64(%rax), %rax
	.loc 1 817 35
	testq	%rax, %rax
	je	.L198
	.loc 1 817 35 is_stmt 0 discriminator 1
	movq	-88(%rbp), %rax
	movq	64(%rax), %rax
	jmp	.L197
.L198:
	.loc 1 817 35 discriminator 2
	movq	-88(%rbp), %rax
	movq	56(%rax), %rax
.L197:
	.loc 1 816 13 is_stmt 1 discriminator 2
	movq	%rax, -24(%rbp)
	.loc 1 818 19 discriminator 2
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	leaq	6(%rdx), %rcx
	movq	-24(%rbp), %rdx
	movq	%rdx, 8(%rax,%rcx,8)
	.loc 1 819 23 discriminator 2
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %eax
	.loc 1 819 12 discriminator 2
	subl	$1, %eax
	movl	%eax, -156(%rbp)
	.loc 1 820 8 discriminator 2
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -112(%rbp)
.LBE11:
	jmp	.L142
.L187:
	.loc 1 821 23
	movl	-144(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 821 20
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	.loc 1 821 33
	movq	64(%rax), %rax
	.loc 1 821 12
	testq	%rax, %rax
	je	.L201
.LBB12:
	.loc 1 826 29
	movl	-144(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 826 15
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -80(%rbp)
	.loc 1 829 12
	jmp	.L202
.L203:
	.loc 1 830 5
	movq	-80(%rbp), %rax
	movq	8(%rax), %rax
	movq	%rax, -80(%rbp)
.L202:
	.loc 1 829 20
	movq	-80(%rbp), %rax
	movq	8(%rax), %rax
	.loc 1 829 13
	testq	%rax, %rax
	jne	.L203
	.loc 1 832 13
	movq	-80(%rbp), %rax
	movq	56(%rax), %rax
	movq	%rax, -32(%rbp)
	.loc 1 833 19
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	leaq	6(%rdx), %rcx
	movq	-32(%rbp), %rdx
	movq	%rdx, 8(%rax,%rcx,8)
	.loc 1 834 20
	movl	-144(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 834 8
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -112(%rbp)
	.loc 1 835 12
	movl	$0, -156(%rbp)
.LBE12:
	jmp	.L142
.L201:
.LBB13:
	.loc 1 845 15
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -48(%rbp)
	.loc 1 845 47
	movl	-144(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 845 33
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rax
	movq	%rax, -40(%rbp)
	.loc 1 849 28
	movq	-112(%rbp), %rax
	movl	-144(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	.loc 1 849 18
	movq	-48(%rbp), %rax
	movq	%rdx, 64(%rax)
	.loc 1 850 26
	movq	-40(%rbp), %rax
	movq	8(%rax), %rdx
	.loc 1 850 17
	movq	-48(%rbp), %rax
	movq	%rdx, 24(%rax)
	.loc 1 851 30
	movq	-40(%rbp), %rax
	movl	40(%rax), %edx
	.loc 1 851 19
	movq	-48(%rbp), %rax
	movl	%edx, 48(%rax)
	.loc 1 852 17
	movq	-48(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 852 9
	testq	%rax, %rax
	je	.L204
	.loc 1 852 29 discriminator 1
	movq	-48(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 852 41 discriminator 1
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L204:
	.loc 1 853 28
	movq	-40(%rbp), %rax
	movq	56(%rax), %rdx
	.loc 1 853 18
	movq	-48(%rbp), %rax
	movq	%rdx, 72(%rax)
	.loc 1 854 26
	movq	-40(%rbp), %rax
	movq	16(%rax), %rdx
	.loc 1 854 17
	movq	-48(%rbp), %rax
	movq	%rdx, 32(%rax)
	.loc 1 855 30
	movq	-40(%rbp), %rax
	movl	44(%rax), %edx
	.loc 1 855 19
	movq	-48(%rbp), %rax
	movl	%edx, 52(%rax)
	.loc 1 856 17
	movq	-48(%rbp), %rax
	movq	32(%rax), %rax
	.loc 1 856 9
	testq	%rax, %rax
	je	.L205
	.loc 1 856 29 discriminator 1
	movq	-48(%rbp), %rax
	movq	32(%rax), %rax
	.loc 1 856 41 discriminator 1
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
.L205:
	.loc 1 857 6
	movq	-40(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
	.loc 1 858 22
	movq	-48(%rbp), %rax
	movq	%rax, %rdi
	call	countnode234
	.loc 1 858 20
	movq	-112(%rbp), %rdx
	movl	-144(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$8, %rcx
	movl	%eax, 8(%rdx,%rcx,4)
	.loc 1 863 13
	movl	-144(%rbp), %eax
	movl	%eax, -124(%rbp)
	.loc 1 863 6
	jmp	.L206
.L208:
	.loc 1 864 27 discriminator 4
	movl	-124(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 864 25 discriminator 4
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rdx
	.loc 1 864 15 discriminator 4
	movq	-112(%rbp), %rax
	movl	-124(%rbp), %ecx
	movslq	%ecx, %rcx
	addq	$6, %rcx
	movq	%rdx, 8(%rax,%rcx,8)
	.loc 1 865 27 discriminator 4
	movl	-124(%rbp), %eax
	leal	2(%rax), %edx
	.loc 1 865 12 discriminator 4
	movl	-124(%rbp), %eax
	leal	1(%rax), %esi
	.loc 1 865 25 discriminator 4
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	8(%rax,%rdx,8), %rcx
	.loc 1 865 16 discriminator 4
	movq	-112(%rbp), %rax
	movslq	%esi, %rdx
	movq	%rcx, 8(%rax,%rdx,8)
	.loc 1 866 31 discriminator 4
	movl	-124(%rbp), %eax
	leal	2(%rax), %edx
	.loc 1 866 14 discriminator 4
	movl	-124(%rbp), %eax
	leal	1(%rax), %ecx
	.loc 1 866 29 discriminator 4
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	8(%rax,%rdx,4), %edx
	.loc 1 866 18 discriminator 4
	movq	-112(%rbp), %rax
	movslq	%ecx, %rcx
	addq	$8, %rcx
	movl	%edx, 8(%rax,%rcx,4)
	.loc 1 863 44 discriminator 4
	addl	$1, -124(%rbp)
.L206:
	.loc 1 863 25 discriminator 1
	cmpl	$1, -124(%rbp)
	jg	.L207
	.loc 1 863 38 discriminator 3
	movl	-124(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 863 36 discriminator 3
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	8(%rax,%rdx,8), %rax
	.loc 1 863 25 discriminator 3
	testq	%rax, %rax
	jne	.L208
.L207:
	.loc 1 868 18
	movq	-112(%rbp), %rax
	movl	-124(%rbp), %edx
	movslq	%edx, %rdx
	addq	$6, %rdx
	movq	$0, 8(%rax,%rdx,8)
	.loc 1 869 15
	movl	-124(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 869 19
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	movq	$0, 8(%rax,%rdx,8)
	.loc 1 870 17
	movl	-124(%rbp), %eax
	leal	1(%rax), %edx
	.loc 1 870 21
	movq	-112(%rbp), %rax
	movslq	%edx, %rdx
	addq	$8, %rdx
	movl	$0, 8(%rax,%rdx,4)
	.loc 1 876 25
	movq	-112(%rbp), %rax
	movq	56(%rax), %rax
	.loc 1 876 16
	testq	%rax, %rax
	jne	.L209
	.loc 1 878 25
	movq	-152(%rbp), %rax
	movq	-48(%rbp), %rdx
	movq	%rdx, (%rax)
	.loc 1 879 27
	movq	-48(%rbp), %rax
	movq	$0, (%rax)
	.loc 1 880 17
	movq	-112(%rbp), %rax
	movq	%rax, %rdi
	call	free@PLT
.L209:
	.loc 1 886 8
	movq	-48(%rbp), %rax
	movq	%rax, -112(%rbp)
	.loc 1 887 23
	movq	-48(%rbp), %rax
	movl	40(%rax), %edx
	.loc 1 887 38
	movq	-48(%rbp), %rax
	movl	44(%rax), %eax
	.loc 1 887 27
	addl	%edx, %eax
	.loc 1 887 12
	addl	$1, %eax
	movl	%eax, -156(%rbp)
.LBE13:
	.loc 1 574 8
	jmp	.L142
.L173:
	.loc 1 890 1
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
	.loc 1 891 40
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	movl	%esi, -12(%rbp)
	.loc 1 892 8
	cmpl	$0, -12(%rbp)
	js	.L212
	.loc 1 892 31 discriminator 1
	movq	-8(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, %rdi
	call	countnode234
	.loc 1 892 19 discriminator 1
	cmpl	%eax, -12(%rbp)
	jl	.L213
.L212:
	.loc 1 893 9
	movl	$0, %eax
	jmp	.L214
.L213:
	.loc 1 894 12
	movl	-12(%rbp), %edx
	movq	-8(%rbp), %rax
	movl	%edx, %esi
	movq	%rax, %rdi
	call	delpos234_internal
.L214:
	.loc 1 895 1
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
	.loc 1 896 35
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movq	%rdi, -24(%rbp)
	movq	%rsi, -32(%rbp)
	.loc 1 896 35
	movq	%fs:40, %rax
	movq	%rax, -8(%rbp)
	xorl	%eax, %eax
	.loc 1 898 10
	leaq	-12(%rbp), %rdx
	movq	-32(%rbp), %rsi
	movq	-24(%rbp), %rax
	movq	%rdx, %r8
	movl	$0, %ecx
	movl	$0, %edx
	movq	%rax, %rdi
	call	findrelpos234@PLT
	.loc 1 898 8
	testq	%rax, %rax
	jne	.L216
	.loc 1 899 9
	movl	$0, %eax
	jmp	.L218
.L216:
	.loc 1 900 12
	movl	-12(%rbp), %edx
	movq	-24(%rbp), %rax
	movl	%edx, %esi
	movq	%rax, %rdi
	call	delpos234_internal
.L218:
	.loc 1 901 1 discriminator 1
	movq	-8(%rbp), %rdx
	subq	%fs:40, %rdx
	je	.L219
	.loc 1 901 1 is_stmt 0
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
	.text
.Letext0:
	.file 2 "/nix/store/1gf2flfqnpqbr1b4p4qz2f72y42bs56r-gcc-11.3.0/lib/gcc/x86_64-unknown-linux-gnu/11.3.0/include/stddef.h"
	.file 3 "tree234.h"
	.file 4 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/assert.h"
	.file 5 "/nix/store/4pqv2mwdn88h7xvsm7a5zplrd8sxzvw0-glibc-2.35-163-dev/include/stdlib.h"
	.section	.debug_info,"",@progbits
.Ldebug_info0:
	.long	0x9a1
	.value	0x5
	.byte	0x1
	.byte	0x8
	.long	.Ldebug_abbrev0
	.uleb128 0x15
	.long	.LASF60
	.byte	0x1d
	.long	.LASF0
	.long	.LASF1
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.long	.Ldebug_line0
	.uleb128 0xf
	.long	.LASF12
	.byte	0x2
	.byte	0xd1
	.byte	0x17
	.long	0x3a
	.uleb128 0x4
	.byte	0x8
	.byte	0x7
	.long	.LASF2
	.uleb128 0x4
	.byte	0x4
	.byte	0x7
	.long	.LASF3
	.uleb128 0x16
	.byte	0x8
	.uleb128 0x4
	.byte	0x1
	.byte	0x8
	.long	.LASF4
	.uleb128 0x4
	.byte	0x2
	.byte	0x7
	.long	.LASF5
	.uleb128 0x4
	.byte	0x1
	.byte	0x6
	.long	.LASF6
	.uleb128 0x4
	.byte	0x2
	.byte	0x5
	.long	.LASF7
	.uleb128 0x17
	.byte	0x4
	.byte	0x5
	.string	"int"
	.uleb128 0x4
	.byte	0x8
	.byte	0x5
	.long	.LASF8
	.uleb128 0x4
	.byte	0x1
	.byte	0x6
	.long	.LASF9
	.uleb128 0x13
	.long	0x74
	.uleb128 0x4
	.byte	0x8
	.byte	0x5
	.long	.LASF10
	.uleb128 0x4
	.byte	0x8
	.byte	0x7
	.long	.LASF11
	.uleb128 0xf
	.long	.LASF13
	.byte	0x3
	.byte	0x22
	.byte	0x1c
	.long	0x9a
	.uleb128 0x14
	.long	.LASF22
	.byte	0x10
	.byte	0x2f
	.long	0xbf
	.uleb128 0xc
	.long	.LASF14
	.byte	0x30
	.byte	0xe
	.long	0x159
	.byte	0
	.uleb128 0x18
	.string	"cmp"
	.byte	0x1
	.byte	0x31
	.byte	0xe
	.long	0xbf
	.byte	0x8
	.byte	0
	.uleb128 0xf
	.long	.LASF15
	.byte	0x3
	.byte	0x24
	.byte	0xf
	.long	0xcb
	.uleb128 0xb
	.long	0xd0
	.uleb128 0x19
	.long	0x66
	.long	0xe4
	.uleb128 0x6
	.long	0x48
	.uleb128 0x6
	.long	0x48
	.byte	0
	.uleb128 0x1a
	.byte	0x7
	.byte	0x4
	.long	0x41
	.byte	0x3
	.byte	0x7e
	.byte	0x6
	.long	0x111
	.uleb128 0xd
	.long	.LASF16
	.byte	0
	.uleb128 0xd
	.long	.LASF17
	.byte	0x1
	.uleb128 0xd
	.long	.LASF18
	.byte	0x2
	.uleb128 0xd
	.long	.LASF19
	.byte	0x3
	.uleb128 0xd
	.long	.LASF20
	.byte	0x4
	.byte	0
	.uleb128 0xf
	.long	.LASF21
	.byte	0x1
	.byte	0x2d
	.byte	0x1c
	.long	0x11d
	.uleb128 0x14
	.long	.LASF23
	.byte	0x50
	.byte	0x34
	.long	0x159
	.uleb128 0xc
	.long	.LASF24
	.byte	0x35
	.byte	0xe
	.long	0x159
	.byte	0
	.uleb128 0xc
	.long	.LASF25
	.byte	0x36
	.byte	0xe
	.long	0x15e
	.byte	0x8
	.uleb128 0xc
	.long	.LASF26
	.byte	0x37
	.byte	0x9
	.long	0x16e
	.byte	0x28
	.uleb128 0xc
	.long	.LASF27
	.byte	0x38
	.byte	0xb
	.long	0x17e
	.byte	0x38
	.byte	0
	.uleb128 0xb
	.long	0x111
	.uleb128 0x10
	.long	0x159
	.long	0x16e
	.uleb128 0x11
	.long	0x3a
	.byte	0x3
	.byte	0
	.uleb128 0x10
	.long	0x66
	.long	0x17e
	.uleb128 0x11
	.long	0x3a
	.byte	0x3
	.byte	0
	.uleb128 0x10
	.long	0x48
	.long	0x18e
	.uleb128 0x11
	.long	0x3a
	.byte	0x2
	.byte	0
	.uleb128 0x1b
	.long	.LASF28
	.byte	0x4
	.byte	0x43
	.byte	0xd
	.long	0x1af
	.uleb128 0x6
	.long	0x1af
	.uleb128 0x6
	.long	0x1af
	.uleb128 0x6
	.long	0x41
	.uleb128 0x6
	.long	0x1af
	.byte	0
	.uleb128 0xb
	.long	0x7b
	.uleb128 0x1c
	.long	.LASF61
	.byte	0x5
	.value	0x22b
	.byte	0xd
	.long	0x1c7
	.uleb128 0x6
	.long	0x48
	.byte	0
	.uleb128 0x1d
	.long	.LASF29
	.byte	0x5
	.value	0x21c
	.byte	0xe
	.long	0x48
	.long	0x1de
	.uleb128 0x6
	.long	0x2e
	.byte	0
	.uleb128 0x5
	.long	.LASF30
	.value	0x380
	.long	0x48
	.quad	.LFB21
	.quad	.LFE21-.LFB21
	.uleb128 0x1
	.byte	0x9c
	.long	0x229
	.uleb128 0x1
	.string	"t"
	.value	0x380
	.byte	0x17
	.long	0x229
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x1
	.string	"e"
	.value	0x380
	.byte	0x20
	.long	0x48
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0x3
	.long	.LASF32
	.value	0x381
	.byte	0x9
	.long	0x66
	.uleb128 0x2
	.byte	0x91
	.sleb128 -28
	.byte	0
	.uleb128 0xb
	.long	0x8e
	.uleb128 0x5
	.long	.LASF31
	.value	0x37b
	.long	0x48
	.quad	.LFB20
	.quad	.LFE20-.LFB20
	.uleb128 0x1
	.byte	0x9c
	.long	0x26c
	.uleb128 0x1
	.string	"t"
	.value	0x37b
	.byte	0x1a
	.long	0x229
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0x7
	.long	.LASF32
	.value	0x37b
	.byte	0x21
	.long	0x66
	.uleb128 0x2
	.byte	0x91
	.sleb128 -28
	.byte	0
	.uleb128 0x1e
	.long	.LASF48
	.byte	0x1
	.value	0x234
	.byte	0xe
	.long	0x48
	.quad	.LFB19
	.quad	.LFE19-.LFB19
	.uleb128 0x1
	.byte	0x9c
	.long	0x490
	.uleb128 0x1
	.string	"t"
	.value	0x234
	.byte	0x2a
	.long	0x229
	.uleb128 0x3
	.byte	0x91
	.sleb128 -168
	.uleb128 0x7
	.long	.LASF32
	.value	0x234
	.byte	0x31
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -172
	.uleb128 0x2
	.string	"n"
	.value	0x235
	.byte	0xe
	.long	0x159
	.uleb128 0x3
	.byte	0x91
	.sleb128 -128
	.uleb128 0x3
	.long	.LASF33
	.value	0x236
	.byte	0xb
	.long	0x48
	.uleb128 0x3
	.byte	0x91
	.sleb128 -120
	.uleb128 0x2
	.string	"ei"
	.value	0x237
	.byte	0x9
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -160
	.uleb128 0x8
	.quad	.LBB5
	.quad	.LBE5-.LBB5
	.long	0x3a9
	.uleb128 0x2
	.string	"ki"
	.value	0x23f
	.byte	0xa
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -156
	.uleb128 0x2
	.string	"sub"
	.value	0x240
	.byte	0xf
	.long	0x159
	.uleb128 0x3
	.byte	0x91
	.sleb128 -112
	.uleb128 0x8
	.quad	.LBB6
	.quad	.LBE6-.LBB6
	.long	0x344
	.uleb128 0x2
	.string	"sib"
	.value	0x26b
	.byte	0x10
	.long	0x159
	.uleb128 0x3
	.byte	0x91
	.sleb128 -88
	.uleb128 0x3
	.long	.LASF34
	.value	0x26c
	.byte	0xb
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -136
	.byte	0
	.uleb128 0x8
	.quad	.LBB7
	.quad	.LBE7-.LBB7
	.long	0x378
	.uleb128 0x2
	.string	"sib"
	.value	0x28f
	.byte	0x10
	.long	0x159
	.uleb128 0x3
	.byte	0x91
	.sleb128 -80
	.uleb128 0x2
	.string	"j"
	.value	0x290
	.byte	0xb
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -152
	.byte	0
	.uleb128 0x12
	.quad	.LBB8
	.quad	.LBE8-.LBB8
	.uleb128 0x2
	.string	"sib"
	.value	0x2b7
	.byte	0x10
	.long	0x159
	.uleb128 0x3
	.byte	0x91
	.sleb128 -72
	.uleb128 0x2
	.string	"j"
	.value	0x2b8
	.byte	0xb
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -148
	.byte	0
	.byte	0
	.uleb128 0x8
	.quad	.LBB9
	.quad	.LBE9-.LBB9
	.long	0x3ef
	.uleb128 0x2
	.string	"i"
	.value	0x30d
	.byte	0xa
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -144
	.uleb128 0x12
	.quad	.LBB10
	.quad	.LBE10-.LBB10
	.uleb128 0x3
	.long	.LASF35
	.value	0x317
	.byte	0x7
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -132
	.byte	0
	.byte	0
	.uleb128 0x8
	.quad	.LBB11
	.quad	.LBE11-.LBB11
	.long	0x422
	.uleb128 0x2
	.string	"m"
	.value	0x328
	.byte	0xf
	.long	0x159
	.uleb128 0x3
	.byte	0x91
	.sleb128 -104
	.uleb128 0x3
	.long	.LASF36
	.value	0x329
	.byte	0xc
	.long	0x48
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.byte	0
	.uleb128 0x8
	.quad	.LBB12
	.quad	.LBE12-.LBB12
	.long	0x455
	.uleb128 0x2
	.string	"m"
	.value	0x33a
	.byte	0xf
	.long	0x159
	.uleb128 0x3
	.byte	0x91
	.sleb128 -96
	.uleb128 0x3
	.long	.LASF36
	.value	0x33b
	.byte	0xc
	.long	0x48
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.byte	0
	.uleb128 0x12
	.quad	.LBB13
	.quad	.LBE13-.LBB13
	.uleb128 0x2
	.string	"a"
	.value	0x34d
	.byte	0xf
	.long	0x159
	.uleb128 0x2
	.byte	0x91
	.sleb128 -64
	.uleb128 0x2
	.string	"b"
	.value	0x34d
	.byte	0x21
	.long	0x159
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0x2
	.string	"j"
	.value	0x34e
	.byte	0xa
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -140
	.byte	0
	.byte	0
	.uleb128 0x5
	.long	.LASF37
	.value	0x22c
	.long	0x48
	.quad	.LFB18
	.quad	.LFE18-.LFB18
	.uleb128 0x1
	.byte	0x9c
	.long	0x4ea
	.uleb128 0x1
	.string	"t"
	.value	0x22c
	.byte	0x1b
	.long	0x229
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0x1
	.string	"e"
	.value	0x22c
	.byte	0x24
	.long	0x48
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.uleb128 0x1
	.string	"cmp"
	.value	0x22c
	.byte	0x30
	.long	0xbf
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x7
	.long	.LASF32
	.value	0x22c
	.byte	0x3a
	.long	0x4ea
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.byte	0
	.uleb128 0xb
	.long	0x66
	.uleb128 0x5
	.long	.LASF38
	.value	0x229
	.long	0x48
	.quad	.LFB17
	.quad	.LFE17-.LFB17
	.uleb128 0x1
	.byte	0x9c
	.long	0x549
	.uleb128 0x1
	.string	"t"
	.value	0x229
	.byte	0x1b
	.long	0x229
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0x1
	.string	"e"
	.value	0x229
	.byte	0x24
	.long	0x48
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.uleb128 0x1
	.string	"cmp"
	.value	0x229
	.byte	0x30
	.long	0xbf
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x7
	.long	.LASF39
	.value	0x229
	.byte	0x39
	.long	0x66
	.uleb128 0x2
	.byte	0x91
	.sleb128 -44
	.byte	0
	.uleb128 0x5
	.long	.LASF40
	.value	0x226
	.long	0x48
	.quad	.LFB16
	.quad	.LFE16-.LFB16
	.uleb128 0x1
	.byte	0x9c
	.long	0x594
	.uleb128 0x1
	.string	"t"
	.value	0x226
	.byte	0x18
	.long	0x229
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0x1
	.string	"e"
	.value	0x226
	.byte	0x21
	.long	0x48
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.uleb128 0x1
	.string	"cmp"
	.value	0x226
	.byte	0x2d
	.long	0xbf
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.byte	0
	.uleb128 0x5
	.long	.LASF41
	.value	0x1be
	.long	0x48
	.quad	.LFB15
	.quad	.LFE15-.LFB15
	.uleb128 0x1
	.byte	0x9c
	.long	0x67a
	.uleb128 0x1
	.string	"t"
	.value	0x1be
	.byte	0x1e
	.long	0x229
	.uleb128 0x3
	.byte	0x91
	.sleb128 -72
	.uleb128 0x1
	.string	"e"
	.value	0x1be
	.byte	0x27
	.long	0x48
	.uleb128 0x3
	.byte	0x91
	.sleb128 -80
	.uleb128 0x1
	.string	"cmp"
	.value	0x1be
	.byte	0x33
	.long	0xbf
	.uleb128 0x3
	.byte	0x91
	.sleb128 -88
	.uleb128 0x7
	.long	.LASF39
	.value	0x1bf
	.byte	0xb
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -92
	.uleb128 0x7
	.long	.LASF32
	.value	0x1bf
	.byte	0x1a
	.long	0x4ea
	.uleb128 0x3
	.byte	0x91
	.sleb128 -104
	.uleb128 0x2
	.string	"n"
	.value	0x1c0
	.byte	0xe
	.long	0x159
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.uleb128 0x2
	.string	"ret"
	.value	0x1c1
	.byte	0xb
	.long	0x48
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0x2
	.string	"c"
	.value	0x1c2
	.byte	0x9
	.long	0x66
	.uleb128 0x2
	.byte	0x91
	.sleb128 -36
	.uleb128 0x2
	.string	"idx"
	.value	0x1c3
	.byte	0x9
	.long	0x66
	.uleb128 0x2
	.byte	0x91
	.sleb128 -52
	.uleb128 0x3
	.long	.LASF42
	.value	0x1c3
	.byte	0xe
	.long	0x66
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0x3
	.long	.LASF43
	.value	0x1c3
	.byte	0x16
	.long	0x66
	.uleb128 0x2
	.byte	0x91
	.sleb128 -44
	.uleb128 0x3
	.long	.LASF44
	.value	0x1c3
	.byte	0x1e
	.long	0x66
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x1f
	.long	.LASF62
	.long	0x68a
	.uleb128 0x9
	.byte	0x3
	.quad	__PRETTY_FUNCTION__.0
	.byte	0
	.uleb128 0x10
	.long	0x7b
	.long	0x68a
	.uleb128 0x11
	.long	0x3a
	.byte	0xd
	.byte	0
	.uleb128 0x13
	.long	0x67a
	.uleb128 0x5
	.long	.LASF45
	.value	0x197
	.long	0x48
	.quad	.LFB14
	.quad	.LFE14-.LFB14
	.uleb128 0x1
	.byte	0x9c
	.long	0x6da
	.uleb128 0x1
	.string	"t"
	.value	0x197
	.byte	0x19
	.long	0x229
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x7
	.long	.LASF32
	.value	0x197
	.byte	0x20
	.long	0x66
	.uleb128 0x2
	.byte	0x91
	.sleb128 -44
	.uleb128 0x2
	.string	"n"
	.value	0x198
	.byte	0xe
	.long	0x159
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.uleb128 0x5
	.long	.LASF46
	.value	0x18b
	.long	0x48
	.quad	.LFB13
	.quad	.LFE13-.LFB13
	.uleb128 0x1
	.byte	0x9c
	.long	0x725
	.uleb128 0x1
	.string	"t"
	.value	0x18b
	.byte	0x1a
	.long	0x229
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0x1
	.string	"e"
	.value	0x18b
	.byte	0x23
	.long	0x48
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.uleb128 0x7
	.long	.LASF32
	.value	0x18b
	.byte	0x2a
	.long	0x66
	.uleb128 0x2
	.byte	0x91
	.sleb128 -36
	.byte	0
	.uleb128 0x5
	.long	.LASF47
	.value	0x185
	.long	0x48
	.quad	.LFB12
	.quad	.LFE12-.LFB12
	.uleb128 0x1
	.byte	0x9c
	.long	0x761
	.uleb128 0x1
	.string	"t"
	.value	0x185
	.byte	0x17
	.long	0x229
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0x1
	.string	"e"
	.value	0x185
	.byte	0x20
	.long	0x48
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.byte	0
	.uleb128 0x20
	.long	.LASF49
	.byte	0x1
	.byte	0x75
	.byte	0xe
	.long	0x48
	.quad	.LFB11
	.quad	.LFE11-.LFB11
	.uleb128 0x1
	.byte	0x9c
	.long	0x896
	.uleb128 0x9
	.string	"t"
	.byte	0x75
	.byte	0x27
	.long	0x229
	.uleb128 0x3
	.byte	0x91
	.sleb128 -104
	.uleb128 0x9
	.string	"e"
	.byte	0x75
	.byte	0x30
	.long	0x48
	.uleb128 0x3
	.byte	0x91
	.sleb128 -112
	.uleb128 0x21
	.long	.LASF32
	.byte	0x1
	.byte	0x75
	.byte	0x37
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -116
	.uleb128 0xe
	.string	"n"
	.byte	0x76
	.byte	0xe
	.long	0x159
	.uleb128 0x2
	.byte	0x91
	.sleb128 -64
	.uleb128 0xe
	.string	"np"
	.byte	0x76
	.byte	0x13
	.long	0x896
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0xa
	.long	.LASF50
	.byte	0x76
	.byte	0x18
	.long	0x159
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0xa
	.long	.LASF51
	.byte	0x76
	.byte	0x1f
	.long	0x159
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0xa
	.long	.LASF52
	.byte	0x77
	.byte	0xb
	.long	0x48
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.uleb128 0xe
	.string	"c"
	.byte	0x78
	.byte	0x9
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -68
	.uleb128 0xa
	.long	.LASF53
	.byte	0x78
	.byte	0xc
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -88
	.uleb128 0xa
	.long	.LASF54
	.byte	0x78
	.byte	0x14
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -84
	.uleb128 0x8
	.quad	.LBB2
	.quad	.LBE2-.LBB2
	.long	0x840
	.uleb128 0xa
	.long	.LASF35
	.byte	0x8a
	.byte	0x6
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -80
	.byte	0
	.uleb128 0x8
	.quad	.LBB3
	.quad	.LBE3-.LBB3
	.long	0x863
	.uleb128 0x2
	.string	"m"
	.value	0x111
	.byte	0xf
	.long	0x159
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.uleb128 0x12
	.quad	.LBB4
	.quad	.LBE4-.LBB4
	.uleb128 0x3
	.long	.LASF55
	.value	0x167
	.byte	0xa
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -76
	.uleb128 0x3
	.long	.LASF35
	.value	0x168
	.byte	0xa
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -72
	.byte	0
	.byte	0
	.uleb128 0xb
	.long	0x159
	.uleb128 0x22
	.long	.LASF56
	.byte	0x1
	.byte	0x6a
	.byte	0x5
	.long	0x66
	.quad	.LFB10
	.quad	.LFE10-.LFB10
	.uleb128 0x1
	.byte	0x9c
	.long	0x8ca
	.uleb128 0x9
	.string	"t"
	.byte	0x6a
	.byte	0x17
	.long	0x229
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.uleb128 0x23
	.long	.LASF57
	.byte	0x1
	.byte	0x5a
	.byte	0xc
	.long	0x66
	.quad	.LFB9
	.quad	.LFE9-.LFB9
	.uleb128 0x1
	.byte	0x9c
	.long	0x913
	.uleb128 0x9
	.string	"n"
	.byte	0x5a
	.byte	0x22
	.long	0x159
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0xa
	.long	.LASF55
	.byte	0x5b
	.byte	0x9
	.long	0x66
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0xe
	.string	"i"
	.byte	0x5c
	.byte	0x9
	.long	0x66
	.uleb128 0x2
	.byte	0x91
	.sleb128 -20
	.byte	0
	.uleb128 0x24
	.long	.LASF58
	.byte	0x1
	.byte	0x52
	.byte	0x6
	.quad	.LFB8
	.quad	.LFE8-.LFB8
	.uleb128 0x1
	.byte	0x9c
	.long	0x93e
	.uleb128 0x9
	.string	"t"
	.byte	0x52
	.byte	0x1b
	.long	0x229
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.uleb128 0x25
	.long	.LASF63
	.byte	0x1
	.byte	0x49
	.byte	0xd
	.quad	.LFB7
	.quad	.LFE7-.LFB7
	.uleb128 0x1
	.byte	0x9c
	.long	0x969
	.uleb128 0x9
	.string	"n"
	.byte	0x49
	.byte	0x22
	.long	0x159
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.uleb128 0x26
	.long	.LASF59
	.byte	0x1
	.byte	0x3e
	.byte	0xa
	.long	0x229
	.quad	.LFB6
	.quad	.LFE6-.LFB6
	.uleb128 0x1
	.byte	0x9c
	.uleb128 0x9
	.string	"cmp"
	.byte	0x3e
	.byte	0x1e
	.long	0xbf
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0xe
	.string	"ret"
	.byte	0x3f
	.byte	0xe
	.long	0x229
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.byte	0
	.section	.debug_abbrev,"",@progbits
.Ldebug_abbrev0:
	.uleb128 0x1
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
	.uleb128 0x2
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
	.uleb128 0x3
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
	.uleb128 0x4
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
	.uleb128 0x5
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
	.uleb128 0x21
	.sleb128 7
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
	.uleb128 0x6
	.uleb128 0x5
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
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
	.uleb128 0x9
	.uleb128 0x5
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
	.uleb128 0xa
	.uleb128 0x34
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
	.uleb128 0xb
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0x21
	.sleb128 8
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xc
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
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0xd
	.uleb128 0x28
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x1c
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0xe
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
	.uleb128 0xf
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
	.uleb128 0x10
	.uleb128 0x1
	.byte	0x1
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x11
	.uleb128 0x21
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2f
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x12
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.byte	0
	.byte	0
	.uleb128 0x13
	.uleb128 0x26
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x14
	.uleb128 0x13
	.byte	0x1
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0x21
	.sleb128 8
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x15
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
	.uleb128 0x16
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x17
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
	.uleb128 0x18
	.uleb128 0xd
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
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
	.uleb128 0x19
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
	.uleb128 0x1a
	.uleb128 0x4
	.byte	0x1
	.uleb128 0x3e
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
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
	.uleb128 0x1b
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
	.uleb128 0x87
	.uleb128 0x19
	.uleb128 0x3c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1c
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
	.uleb128 0x3c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1d
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
	.uleb128 0x1e
	.uleb128 0x2e
	.byte	0x1
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
	.uleb128 0x1f
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x34
	.uleb128 0x19
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x20
	.uleb128 0x2e
	.byte	0x1
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
	.uleb128 0x21
	.uleb128 0x5
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
	.uleb128 0x22
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
	.uleb128 0x23
	.uleb128 0x2e
	.byte	0x1
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
	.uleb128 0x7a
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x24
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
	.uleb128 0x25
	.uleb128 0x2e
	.byte	0x1
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
	.uleb128 0x26
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
	.section	.debug_line,"",@progbits
.Ldebug_line0:
	.section	.debug_str,"MS",@progbits,1
.LASF55:
	.string	"count"
.LASF29:
	.string	"malloc"
.LASF30:
	.string	"del234"
.LASF26:
	.string	"counts"
.LASF12:
	.string	"size_t"
.LASF11:
	.string	"long long unsigned int"
.LASF53:
	.string	"lcount"
.LASF25:
	.string	"kids"
.LASF61:
	.string	"free"
.LASF51:
	.string	"right"
.LASF10:
	.string	"long long int"
.LASF6:
	.string	"signed char"
.LASF60:
	.string	"GNU C17 11.3.0 -mtune=generic -march=x86-64 -g -O2 -O0 -fPIC -fstack-protector-strong -fno-strict-overflow -frandom-seed=ipz9d8l24i --param=ssp-buffer-size=4"
.LASF62:
	.string	"__PRETTY_FUNCTION__"
.LASF41:
	.string	"findrelpos234"
.LASF21:
	.string	"node234"
.LASF37:
	.string	"findpos234"
.LASF24:
	.string	"parent"
.LASF8:
	.string	"long int"
.LASF38:
	.string	"findrel234"
.LASF33:
	.string	"retval"
.LASF59:
	.string	"newtree234"
.LASF23:
	.string	"node234_Tag"
.LASF45:
	.string	"index234"
.LASF56:
	.string	"count234"
.LASF3:
	.string	"unsigned int"
.LASF27:
	.string	"elems"
.LASF2:
	.string	"long unsigned int"
.LASF52:
	.string	"orig_e"
.LASF5:
	.string	"short unsigned int"
.LASF57:
	.string	"countnode234"
.LASF54:
	.string	"rcount"
.LASF36:
	.string	"target"
.LASF46:
	.string	"addpos234"
.LASF35:
	.string	"childnum"
.LASF18:
	.string	"REL234_LE"
.LASF13:
	.string	"tree234"
.LASF17:
	.string	"REL234_LT"
.LASF63:
	.string	"freenode234"
.LASF47:
	.string	"add234"
.LASF28:
	.string	"__assert_fail"
.LASF44:
	.string	"cmpret"
.LASF16:
	.string	"REL234_EQ"
.LASF42:
	.string	"ecount"
.LASF4:
	.string	"unsigned char"
.LASF7:
	.string	"short int"
.LASF15:
	.string	"cmpfn234"
.LASF48:
	.string	"delpos234_internal"
.LASF22:
	.string	"tree234_Tag"
.LASF31:
	.string	"delpos234"
.LASF34:
	.string	"lastelem"
.LASF9:
	.string	"char"
.LASF32:
	.string	"index"
.LASF49:
	.string	"add234_internal"
.LASF39:
	.string	"relation"
.LASF40:
	.string	"find234"
.LASF20:
	.string	"REL234_GE"
.LASF19:
	.string	"REL234_GT"
.LASF58:
	.string	"freetree234"
.LASF43:
	.string	"kcount"
.LASF50:
	.string	"left"
.LASF14:
	.string	"root"
	.section	.debug_line_str,"MS",@progbits,1
.LASF1:
	.string	"/home/runner/assembly"
.LASF0:
	.string	"tree234.c"
	.ident	"GCC: (GNU) 11.3.0"
	.section	.note.GNU-stack,"",@progbits
