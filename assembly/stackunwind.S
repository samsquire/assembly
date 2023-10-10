.global main
.data
.LC0:
	.string	"%d infunc: %p %s\n"
	.text
	.globl	main
	.type	main, @function
.LC1:
	.string	"end of stacktrace\n"
	.text
	.globl	main
	.type	main, @function
.unknown:
	.string	"unknown"
	.text
	.globl	main
	.type	main, @function
.smain: 
  .text
  .string "main"
.sone: 
  .text
  .string "one"
.stwo: 
  .text
  .string "two"
.sthree: 
  .text
  .string "three"
.sstacktrace:
  .text
  .string "stacktrace"
one_stacksize = 0
two_stacksize = 0
three_stacksize = 0
.global stackstart
.data
stackstart:
  .long 0

.text
main:
  mov %rsp, stackstart(%rip)
  pushq %rbp
  mov %rsp, %rbp
  call one
  mov %rbp, %rsp
  popq %rbp
  ret

one:
  pushq %rbp
  mov %rsp, %rbp
  call two
  mov %rbp, %rsp
  popq %rbp
  ret

two:
  pushq %rbp
  mov %rsp, %rbp
  call three
  mov %rbp, %rsp
  popq %rbp
  ret

three:
  pushq %rbp
  mov %rsp, %rbp
  call stacktrace
  mov %rbp, %rsp
  popq %rbp
  ret

stacktrace:
  pushq %rbp
  mov %rsp, %rbp
  mov $0, %rsi
unwind:

  popq %rax

  leaq .unknown(%rip), %rcx  
  leaq one(%rip), %rdx
  cmp %rax, %rdx
  leaq .sone(%rip), %rcx
  jg equal
  leaq two(%rip), %rdx
  cmp %rax, %rdx
  leaq .stwo(%rip), %rcx
  jg equal
  leaq three(%rip), %rdx
  cmp %rax, %rdx
  leaq .sthree(%rip), %rcx
  jg equal

  leaq stacktrace(%rip), %rdx
  cmp %rax, %rdx
  leaq .sstacktrace(%rip), %rcx
  jg equal
  leaq .unknown(%rip), %rcx  
equal:
  pushq %rax
  pushq %rsi
  
 // RDI, RSI, RDX, RCX
  movq    %rax, %rdx
	leaq	.LC0(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax 

  popq %rsi
  popq %rax
  inc %rsi
  cmpq %rax, stackstart(%rip)
  je done 
  jl done
  jmp unwind 
  
done:
  movq    %rax, %rsi
	leaq	.LC1(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax 
  mov $1, %eax
  mov $0, %ebx 
  int $0x80

  
  
