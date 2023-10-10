.global main

.macro JUMP target 
	addq $1, %rax
	jmp \target
.endm

.macro ADDCO 
	inc %rax
	popq %rsi
	addq %rsp, %rsi
.endm


.macro pushs number 
	inc %rax
	# pushq \number
.endm
.altmacro
.macro YIELD reset_rax {
    LOCAL next_inst, after_yield

    pushq %rax
    pushq %rcx
    pushq %rdx
    pushq %rbx

	# movq	%rsp, %rbp
  movq    %rcx, %rsi
	leaq	.LC8(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

    popq %rbx
    popq %rdx
    popq %rcx
    popq %rax
    pushq %rax
    pushq %rcx
    pushq %rdx
    pushq %rbx

    movq    %rcx, %rsi
	leaq	.LC6(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

    popq %rbx
    popq %rdx
    popq %rcx
    popq %rax
    

	#  local turns these labels into local labels, so multiple uses of
	#  YIELD don't create repeated labels.
	# swap rsp, by the stored value in rsp (this means we just saved
	# the value of the main program rsp to the co_data structure pointed
	# by rcx)
	xchg (%rcx), %rsp
	# swap rax, same as above
	xchgq 8(%rcx), %rax
	# swap rbx, same as above
	xchgq 16(%rcx), %rbx
 	# now we push onto the stack the instruction pointer for the coroutine
	# which will be used by the "ret" instruction further down
	pushq 24(%rcx)	
	# we call next_inst to get the instruction pointer of this coroutine.
	# We don't wanna return to the next "pop" so we will need to increment
	# this value so that a yield to this coroutine returns right after the
	# "ret". The call will put this rip into the stack
	call next_inst
next_inst:
	# move the just save rip into the rip of the _co_data[coroutine_id]
	popq 24(%rcx)
	# increment it so a yield from the other coroutine continues from right
	# after the ret
	addq $(after_yield-next_inst), 24(%rcx)
	# jump, using the value pushed 4 instructions above, into the coroutine
	ret
after_yield:
.endm
.data
.LC0:
	.string	"Pointer %p\n"
	.text
	.globl	main
	.type	main, @function
.LC1:
	.string	"Hi world %d\n"
	.text
	.globl	main
	.type	main, @function
.LC3:
	.string	"In coroutine: %d\n"
	.text
	.globl	main
	.type	main, @function
.LC4:
	.string	"Creating coroutine: %d\n"
	.text
	.globl	main
	.type	main, @function
.LC5:
	.string	"RDX: %p\n"
	.text
	.globl	main
	.type	main, @function
.LC6:
	.string	"YIELD (RCX): %p\n"
	.text
	.globl	main
	.type	main, @function
.LC7:
	.string	"Coroutine RCX: %p\n"
	.text
	.globl	main
	.type	main, @function
.LC8:
	.string	"YIELD RCX: %p\n"
	.text
	.globl	main
	.type	main, @function
.LC9:
	.string	"Coroutine loop\n"
	.text
	.globl	main
	.type	main, @function
.LC10:
	.string	"Created all coroutines\n"
	.text
	.globl	main
	.type	main, @function
.data
.align 32
.codata:
.align 32
	
    .skip 100000
.data_stack:
	.zero 100000, 0
.end_data_stack:

.text
costart:
	pushs $1
loop:
    # sub $8, %rsp
	# pushs $1
	# ADDCO
  pushq %rcx
  movq    %rcx, %rsi
	leaq	.LC7(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

  popq %rcx

  YIELD

  
	JUMP loop
main:
program:
    # PUSHS $5
    xor %rax, %rax
    sub $1024, %rsp
    movq %rsp, %rbp
print2:

    leaq .end_data_stack(%rip),%rdx
	leaq .codata(%rip), %rcx         
    movq %rcx, .codata(%rip)

    # sub     $8, %rbp
 	# pushq	%rbp

 	leaq	.LC0(%rip), %rax
 	movq	%rax, %rdi
    movq    %rcx, %rsi
 	movl	$0, %eax
 	call	printf@PLT
prepare:
	movl	$0, %eax
	leaq .codata(%rip), %rcx
    leaq .end_data_stack(%rip),%rdx
    # sub $8, %rsp
  movq $0, %rbx
    
init_co_loop:
	# Initialize the rsp
    movl $0, %esi
	movq %rdx,(%rcx)
	# Initialize the rip
	leaq costart(%rip),%rdi
    movq %rdi,24(%rcx)
	# Move to the next structure in _co_data
	addq $32, %rcx
	# Move back to the next coroutine start of the stack
	# Each coroutine in this example gets 80 bytes
	sub $80, %rdx
	# Loop stuff
	inc %rbx
print:

    pushq %rax
    pushq %rcx
    pushq %rdx
    pushq %rbx
    pushq %rsp

  movq %rbx, %rsi
  movl    %ebx, %esi
	leaq	.LC4(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

    popq %rsp
    popq %rbx
    popq %rdx
    popq %rcx
    popq %rax


    pushq %rax
    pushq %rcx
    pushq %rdx
    pushq %rbx
    pushq %rsp

	# movq	%rsp, %rbp
	leaq	.LC1(%rip), %rdi
    movl    %ebx, %esi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

    popq %rsp
    popq %rbx
    popq %rdx
    popq %rcx
    popq %rax

    pushq %rax
    pushq %rcx
    pushq %rdx
    pushq %rbx
    pushq %rsp

	leaq	.LC5(%rip), %rdi
    movl    %edx, %esi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

    popq %rsp
    popq %rbx
    popq %rdx
    popq %rcx
    popq %rax

init_co_loop2:
	cmp $10, %rbx 
	jl init_co_loop

	leaq	.LC10(%rip), %rax
	movq	%rax, %rdi
    movl    %edx, %esi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

	# movq	%rsp, %rbp
	movl	$0, %eax
  # popq %rax
co_initialized:
	# i = 0
	xor %rax, %rax
	# we will start with the first co-routine
	leaq .codata(%rip), %rcx         
_loop:
	# yield to the coroutine

	YIELD
    # sub $8, %rsp
    pushq %rax
    pushq %rcx
	leaq	.LC9(%rip), %rdi
    movl    %edx, %esi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

  popq %rcx
  popq %rax

	# i += 1
	inc %rax
	# move onto the next coroutine
	add $32, %rcx
	# Loop things
	cmp $10, %rax
	jl _loop
	jmp _exit

	# popq	%rbp
    ret
