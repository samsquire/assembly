.global main
.data
.LC8:
	.string	"A"
	.text
	.globl	main
	.type	main, @function
.LC9:
	.string	"B"
	.text
	.globl	main
	.type	main, @function
.YIELD:
	.string	"Y"
	.text
	.globl	main
	.type	main, @function
.P:
	.string	"P: %p\n"
	.text
	.globl	main
	.type	main, @function
.data
.align 32
.coroutines:
.align 32
    .zero 100000


.set VAR1, 0
.set COROUTINE_SIZE, 64
.text
.altmacro
.macro YIELD reset_rax {
    
  add $1, %rax
  movq $0, %rdx   // higher 64 bits of dividend
  movq $2, %rcx    // divisor
  div %rcx      // Remainder 3 is now in RDX, quotient 2 is in RAX.
  movq %rdx, %rax

  imul $COROUTINE_SIZE, %rax, %rdx
  pushq %rdx
  pushq %rax

  movq    %rdx, %rsi
	leaq	.YIELD(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

  popq %rax
  popq %rdx

  leaq .coroutines(%rip), %rbx
  add %rdx, %rbx
  jmp *(%rbx)


.endm
one:
  pushq %rax 
  movq    %rcx, %rsi
	leaq	.LC8(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
  popq %rax
  YIELD
two:
   
  pushq %rax 
  movq    %rcx, %rsi
	leaq	.LC9(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
  popq %rax
  YIELD

main:
  pushq %rbp
  movq %rsp, %rbp

  movq $0, %rcx
  imul $COROUTINE_SIZE, %rcx, %rcx

  leaq .coroutines(%rip), %rdx
  add %rcx, %rdx

  movq    %rdx, %rsi
	leaq	.P(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

  leaq one(%rip), %rcx 
  leaq .coroutines(%rip), %rdx
  movq %rcx, (%rdx) 
  leaq two(%rip), %rcx 
  add $8, %rdx
  movq %rcx, (%rdx) 

  movq $1, %rcx
  imul $COROUTINE_SIZE, %rcx, %rcx
  
  leaq .coroutines(%rip), %rdx
  add %rcx, %rdx
  leaq two(%rip), %rcx 
  movq %rcx, (%rdx) 
  leaq one(%rip), %rcx 
  add $8, %rdx
  movq %rcx, (%rdx) 
  
  
  movq $-1, %rax
  YIELD
  pop %rbp
  ret
