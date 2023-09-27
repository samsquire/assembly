	.file	"pthread.c"
	.text
.Ltext0:
	.file 0 "/home/sam/assembly" "pthread.c"
	.section	.rodata
.LC0:
	.string	"Hi from thread"
	.text
	.type	func, @function
func:
.LFB6:
	.file 1 "pthread.c"
	.loc 1 10 24
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	.loc 1 11 3
	leaq	.LC0(%rip), %rax
	movq	%rax, %rdi
	call	puts@PLT
	.loc 1 12 10
	movl	$0, %eax
	.loc 1 13 1
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE6:
	.size	func, .-func
	.section	.rodata
.LC1:
	.string	"thread 1 created %ld %ld\n"
	.text
	.globl	main
	.type	main, @function
main:
.LFB7:
	.loc 1 19 12
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$96, %rsp
	.loc 1 19 12
	movq	%fs:40, %rax
	movq	%rax, -8(%rbp)
	xorl	%eax, %eax
	.loc 1 27 11
	leaq	-88(%rbp), %rdx
	leaq	-64(%rbp), %rsi
	leaq	-80(%rbp), %rax
	movq	%rdx, %rcx
	leaq	func(%rip), %rdx
	movq	%rax, %rdi
	call	pthread_create@PLT
	movl	%eax, -84(%rbp)
	.loc 1 30 3
	movl	$56, %edx
	movl	$8, %esi
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 35 3
	movq	-80(%rbp), %rax
	leaq	-72(%rbp), %rdx
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	pthread_join@PLT
	movl	$0, %eax
	.loc 1 37 1
	movq	-8(%rbp), %rdx
	subq	%fs:40, %rdx
	je	.L5
	call	__stack_chk_fail@PLT
.L5:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE7:
	.size	main, .-main
.Letext0:
	.file 2 "/usr/include/x86_64-linux-gnu/bits/types.h"
	.file 3 "/usr/include/x86_64-linux-gnu/bits/pthreadtypes.h"
	.file 4 "/usr/include/stdio.h"
	.file 5 "/usr/include/pthread.h"
	.section	.debug_info,"",@progbits
.Ldebug_info0:
	.long	0x244
	.value	0x5
	.byte	0x1
	.byte	0x8
	.long	.Ldebug_abbrev0
	.uleb128 0xa
	.long	.LASF26
	.byte	0x1d
	.long	.LASF0
	.long	.LASF1
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.long	.Ldebug_line0
	.uleb128 0x1
	.byte	0x1
	.byte	0x8
	.long	.LASF2
	.uleb128 0x1
	.byte	0x2
	.byte	0x7
	.long	.LASF3
	.uleb128 0x1
	.byte	0x4
	.byte	0x7
	.long	.LASF4
	.uleb128 0x1
	.byte	0x8
	.byte	0x7
	.long	.LASF5
	.uleb128 0x1
	.byte	0x1
	.byte	0x6
	.long	.LASF6
	.uleb128 0x1
	.byte	0x2
	.byte	0x5
	.long	.LASF7
	.uleb128 0xb
	.byte	0x4
	.byte	0x5
	.string	"int"
	.uleb128 0x1
	.byte	0x8
	.byte	0x5
	.long	.LASF8
	.uleb128 0xc
	.byte	0x8
	.uleb128 0x6
	.long	0x66
	.uleb128 0x5
	.long	.LASF11
	.byte	0x2
	.byte	0xc2
	.byte	0x1b
	.long	0x5f
	.uleb128 0x1
	.byte	0x1
	.byte	0x6
	.long	.LASF9
	.uleb128 0x7
	.long	0x79
	.uleb128 0x3
	.long	0x80
	.uleb128 0x1
	.byte	0x8
	.byte	0x7
	.long	.LASF10
	.uleb128 0x5
	.long	.LASF12
	.byte	0x3
	.byte	0x1b
	.byte	0x1b
	.long	0x43
	.uleb128 0xd
	.long	.LASF15
	.byte	0x38
	.byte	0x3
	.byte	0x38
	.byte	0x7
	.long	0xc1
	.uleb128 0x8
	.long	.LASF13
	.byte	0x3a
	.byte	0x8
	.long	0xc1
	.uleb128 0x8
	.long	.LASF14
	.byte	0x3b
	.byte	0xc
	.long	0x5f
	.byte	0
	.uleb128 0xe
	.long	0x79
	.long	0xd1
	.uleb128 0xf
	.long	0x43
	.byte	0x37
	.byte	0
	.uleb128 0x5
	.long	.LASF15
	.byte	0x3
	.byte	0x3e
	.byte	0x1e
	.long	0x9d
	.uleb128 0x7
	.long	0xd1
	.uleb128 0x1
	.byte	0x8
	.byte	0x5
	.long	.LASF16
	.uleb128 0x5
	.long	.LASF17
	.byte	0x4
	.byte	0x4d
	.byte	0x13
	.long	0x6d
	.uleb128 0x10
	.long	.LASF24
	.byte	0x4
	.byte	0x1
	.byte	0xf
	.byte	0x8
	.long	0x110
	.uleb128 0x11
	.long	.LASF24
	.byte	0x1
	.byte	0x10
	.byte	0x7
	.long	0x58
	.byte	0
	.byte	0
	.uleb128 0x9
	.long	.LASF18
	.byte	0xdb
	.long	0x58
	.long	0x129
	.uleb128 0x2
	.long	0x91
	.uleb128 0x2
	.long	0x129
	.byte	0
	.uleb128 0x3
	.long	0x66
	.uleb128 0x12
	.long	.LASF19
	.byte	0x4
	.value	0x164
	.byte	0xc
	.long	0x58
	.long	0x146
	.uleb128 0x2
	.long	0x85
	.uleb128 0x13
	.byte	0
	.uleb128 0x9
	.long	.LASF20
	.byte	0xca
	.long	0x58
	.long	0x169
	.uleb128 0x2
	.long	0x16e
	.uleb128 0x2
	.long	0x178
	.uleb128 0x2
	.long	0x17d
	.uleb128 0x2
	.long	0x68
	.byte	0
	.uleb128 0x3
	.long	0x91
	.uleb128 0x6
	.long	0x169
	.uleb128 0x3
	.long	0xdd
	.uleb128 0x6
	.long	0x173
	.uleb128 0x3
	.long	0x182
	.uleb128 0x14
	.long	0x66
	.long	0x191
	.uleb128 0x2
	.long	0x66
	.byte	0
	.uleb128 0x15
	.long	.LASF27
	.byte	0x1
	.byte	0x13
	.byte	0x5
	.long	0x58
	.quad	.LFB7
	.quad	.LFE7-.LFB7
	.uleb128 0x1
	.byte	0x9c
	.long	0x219
	.uleb128 0x16
	.long	.LASF28
	.byte	0x1
	.byte	0x14
	.byte	0x17
	.long	0xe9
	.uleb128 0x4
	.long	.LASF21
	.byte	0x15
	.byte	0x17
	.long	0xd1
	.uleb128 0x3
	.byte	0x91
	.sleb128 -80
	.uleb128 0x4
	.long	.LASF22
	.byte	0x16
	.byte	0x17
	.long	0xd1
	.uleb128 0x3
	.byte	0x91
	.sleb128 -80
	.uleb128 0x4
	.long	.LASF23
	.byte	0x17
	.byte	0xd
	.long	0x91
	.uleb128 0x3
	.byte	0x91
	.sleb128 -96
	.uleb128 0x4
	.long	.LASF24
	.byte	0x19
	.byte	0xf
	.long	0xf5
	.uleb128 0x3
	.byte	0x91
	.sleb128 -104
	.uleb128 0x17
	.string	"s"
	.byte	0x1
	.byte	0x1b
	.byte	0x7
	.long	0x58
	.uleb128 0x3
	.byte	0x91
	.sleb128 -100
	.uleb128 0x4
	.long	.LASF25
	.byte	0x22
	.byte	0x9
	.long	0x66
	.uleb128 0x3
	.byte	0x91
	.sleb128 -88
	.byte	0
	.uleb128 0x18
	.long	.LASF29
	.byte	0x1
	.byte	0xa
	.byte	0x7
	.long	0x66
	.quad	.LFB6
	.quad	.LFE6-.LFB6
	.uleb128 0x1
	.byte	0x9c
	.uleb128 0x19
	.long	.LASF24
	.byte	0x1
	.byte	0xa
	.byte	0x12
	.long	0x66
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.byte	0
	.section	.debug_abbrev,"",@progbits
.Ldebug_abbrev0:
	.uleb128 0x1
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
	.uleb128 0x2
	.uleb128 0x5
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x3
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0x21
	.sleb128 8
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x4
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
	.uleb128 0x5
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
	.uleb128 0x6
	.uleb128 0x37
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x7
	.uleb128 0x26
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x8
	.uleb128 0xd
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 3
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x9
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 5
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0x21
	.sleb128 12
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
	.uleb128 0xa
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
	.uleb128 0xb
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
	.uleb128 0xc
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0xd
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
	.uleb128 0xe
	.uleb128 0x1
	.byte	0x1
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xf
	.uleb128 0x21
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2f
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x10
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
	.uleb128 0xb
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x11
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
	.uleb128 0x12
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
	.uleb128 0x13
	.uleb128 0x18
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x14
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
	.uleb128 0x15
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
	.byte	0
	.byte	0
	.uleb128 0x17
	.uleb128 0x34
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
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x18
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
	.byte	0
	.byte	0
	.uleb128 0x19
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
.LASF16:
	.string	"long long int"
.LASF4:
	.string	"unsigned int"
.LASF2:
	.string	"unsigned char"
.LASF27:
	.string	"main"
.LASF15:
	.string	"pthread_attr_t"
.LASF5:
	.string	"long unsigned int"
.LASF10:
	.string	"long long unsigned int"
.LASF24:
	.string	"data"
.LASF20:
	.string	"pthread_create"
.LASF11:
	.string	"__ssize_t"
.LASF28:
	.string	"stack_size"
.LASF22:
	.string	"attr2"
.LASF9:
	.string	"char"
.LASF17:
	.string	"ssize_t"
.LASF25:
	.string	"result"
.LASF26:
	.string	"GNU C17 12.3.0 -mtune=generic -march=x86-64 -g -fasynchronous-unwind-tables -fstack-protector-strong -fstack-clash-protection -fcf-protection"
.LASF8:
	.string	"long int"
.LASF18:
	.string	"pthread_join"
.LASF13:
	.string	"__size"
.LASF3:
	.string	"short unsigned int"
.LASF19:
	.string	"printf"
.LASF21:
	.string	"attr"
.LASF29:
	.string	"func"
.LASF14:
	.string	"__align"
.LASF7:
	.string	"short int"
.LASF23:
	.string	"thread"
.LASF6:
	.string	"signed char"
.LASF12:
	.string	"pthread_t"
	.section	.debug_line_str,"MS",@progbits,1
.LASF1:
	.string	"/home/sam/assembly"
.LASF0:
	.string	"pthread.c"
	.ident	"GCC: (Ubuntu 12.3.0-1ubuntu1~23.04) 12.3.0"
	.section	.note.GNU-stack,"",@progbits
	.section	.note.gnu.property,"a"
	.align 8
	.long	1f - 0f
	.long	4f - 1f
	.long	5
0:
	.string	"GNU"
1:
	.align 8
	.long	0xc0000002
	.long	3f - 2f
2:
	.long	0x3
3:
	.align 8
4:
