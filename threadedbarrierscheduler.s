
.global main
.JOINED:
	.string	"Joined thread... %d\n"
	.text
.CREATED:
	.string	"created thread... %d %d\n"
	.text
.FINISHED:
	.string	"finished coroutines\n"
	.text
.TDATA:
	.string	"thread received data %p\n"
	.text
.TDATA2:
	.string	"thread data %p\n"
	.text
.TDATA3:
	.string	"thread's thread data is at %p\n"
	.text
.COR:
	.string	"coroutine function is %p\n"
	.text
.INIT:
	.string	"INIT RCX is %p\n"
	.text
.STARTED:
	.string	"Starting...\n"
	.text
.CALLING:
	.string	"Calling...\n"
	.text


.data
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

    pushq %rdi
    pushq %rsi
    pushq %rax
    pushq %rcx
    pushq %rdx
    pushq %rbx

	# movq	%rsp, %rbp
  movq    (%rcx), %rsi
	leaq	.LC8(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

    popq %rbx
    popq %rdx
    popq %rcx
    popq %rax
    popq %rsi
    popq %rdi 

    pushq %rdi
    pushq %rsi
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
    popq %rsi
    popq %rdi 
    
    pushq %rdi
    pushq %rsi
    pushq %rax
    pushq %rcx
    pushq %rdx
    pushq %rbx
  movq    24(%rcx), %rsi
	leaq	.COR(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

    popq %rbx
    popq %rdx
    popq %rcx
    popq %rax
    popq %rsi
    popq %rdi 
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
	.type	threadstart, @function
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
.codata2:
.align 32
	
    .skip 100000
.data_stack1:
	.zero 100000, 0
.end_data_stack1:
.codata1:
.align 32
	
    .skip 100000
.data_stack2:
	.zero 100000, 0
.end_data_stack2:

.text
costart:
	# pushs $1
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
.LFB7:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$256, %rsp
  movq $1, %rsi
	leaq	.STARTED(%rip), %rdi
	call	printf@PLT
	movl	$0, %eax
  movq $1, %rsi
	movq	%fs:40, %rax
	movq	%rax, -8(%rbp)
	xorl	%eax, %eax

  
	leaq .end_data_stack1(%rip), %rax
  movq %rax, -96(%rbp)         
  leaq .codata1(%rip), %rax
  movq %rax, -88(%rbp)
	leaq	-88(%rbp), %rdx
	leaq	-64(%rbp), %rsi
	leaq	-80(%rbp), %rax
	movq	%rdx, %rcx
	leaq	threadstart(%rip), %rdx
	movq	%rax, %rdi
	call	pthread_create@PLT
	movl	%eax, -84(%rbp)

	leaq	.JOINED(%rip), %rdi
	call	printf@PLT
	movl	$0, %eax

	movq	-80(%rbp), %rax
	leaq	-72(%rbp), %rdx
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	pthread_join@PLT
	movl	$0, %eax
	movq	-8(%rbp), %rdx
  
  movq $1, %rsi
  movq -80(%rbp), %rdx
	leaq	.CREATED(%rip), %rdi
	call	printf@PLT
	movl	$0, %eax
  movq $1, %rsi



	leaq .end_data_stack2(%rip), %rax
  movq %rax, -192(%rbp)         
  leaq .codata2(%rip), %rax
  movq %rax, -184(%rbp)
	leaq	-184(%rbp), %rdx
	leaq	-160(%rbp), %rsi
	leaq	-176(%rbp), %rax
	movq	%rdx, %rcx
	leaq	threadstart(%rip), %rdx
	movq	%rax, %rdi
	call	pthread_create@PLT
	movl	%eax, -180(%rbp)
  movq $2, %rsi
	leaq	.CREATED(%rip), %rdi
	call	printf@PLT
	movl	$0, %eax

	movq	-176(%rbp), %rax
	leaq	-168(%rbp), %rdx
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	pthread_join@PLT
	movl	$0, %eax
	movq	-8(%rbp), %rdx

  movq $2, %rsi
	leaq	.JOINED(%rip), %rdi
	call	printf@PLT
	movl	$0, %eax


	subq	%fs:40, %rdx
	leave
	ret
.LFE7:
	.size	main, .-main
	.ident	"GCC: (Ubuntu 12.3.0-1ubuntu1~23.04) 12.3.0"
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
threadstart:
program:
	pushq	%rbp
  movq %rsp, %rbp
  sub $1024, %rsp
  pushq %rdi
  movq %rdi, %rsi 
	leaq	.TDATA(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
    # PUSHS $5
    xor %rax, %rax
print2:
  popq %rdi
  pushq %rdi
  # movq %rdi, %rdx
  # addq $8, %rdx
  movq %rdi, %rdx
  subq $8, %rdx
  movq (%rdx), %rdx 
  mov %rdx, %rsi
	leaq .TDATA2(%rip), %rax
	movq %rax, %rdi
	movl $0, %eax
	call	printf@PLT
	movl	$0, %eax
  popq %rdi
  pushq %rdi
    movq %rdi, %rcx         
    movq %rcx, (%rcx)
  pushq %rcx 

  mov %rcx, %rsi
	leaq .TDATA3(%rip), %rax
	movq %rax, %rdi
	movl $0, %eax
	call	printf@PLT
	movl	$0, %eax
    # sub     $8, %rbp

  popq %rcx
  

  mov %rcx, %rsi
 	leaq	.LC0(%rip), %rax
 	movq	%rax, %rdi
    movq    %rcx, %rsi
 	movl	$0, %eax
 	call	printf@PLT


  popq %rdi
prepare:
	movl	$0, %eax
  movq %rdi, %rcx         
  movq %rdi, %rdx
  subq $8, %rdx
  movq (%rdx), %rdx 
    # sub $8, %rsp
  movq $0, %rbx
init_co_loop:
  pushq %rcx
  pushq %rdi
  pushq %rdx
 	leaq	.INIT(%rip), %rax
 	movq	%rax, %rdi
  movq    %rcx, %rsi
 	movl	$0, %eax
 	call	printf@PLT

	# Initialize the rsp
  movl $0, %esi
  pop %rdx
  pop %rdi
  pop %rcx

	movq %rdx, (%rcx)


	# Initialize the rip
  leaq costart(%rip), %rax
  movq %rax, 24(%rcx)
  movq %rsp, 32(%rcx)
	# Move to the next structure in _co_data
	addq $64, %rcx
	# Move back to the next coroutine start of the stack
	# Each coroutine in this example gets 80 bytes
	subq $80, %rdx
	# Loop stuff
	inc %rbx
print:
    pushq %rdi
    pushq %rsi
    pushq %rax
    pushq %rcx
    pushq %rdx
    pushq %rbx

  movq %rbx, %rsi
  movl    %ebx, %esi
	leaq	.LC4(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

    popq %rbx
    popq %rdx
    popq %rcx
    popq %rax
    popq %rsi
    popq %rdi 

    pushq %rdi
    pushq %rsi
    pushq %rax
    pushq %rcx
    pushq %rdx
    pushq %rbx

	# movq	%rsp, %rbp
	leaq	.LC1(%rip), %rdi
    movl    %ebx, %esi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

    popq %rbx
    popq %rdx
    popq %rcx
    popq %rax
    popq %rsi
    popq %rdi

    pushq %rdi
    pushq %rsi
    pushq %rax
    pushq %rcx
    pushq %rdx
    pushq %rbx

  
	leaq	.LC5(%rip), %rdi
    movq    %rdx, %rsi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

    popq %rbx
    popq %rdx
    popq %rcx
    popq %rax
    popq %rsi
    popq %rdi

init_co_loop2:
	cmp $10, %rbx 
	jl init_co_loop
  pushq %rdi
	leaq	.LC10(%rip), %rax
	movq	%rax, %rdi
    movl    %edx, %esi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

	# movq	%rsp, %rbp
	movl	$0, %eax
  popq %rdi
co_initialized:
	# i = 0
	xor %rax, %rax
	# we will start with the first co-routine
	mov %rdi, %rcx         
_loop:
	# yield to the coroutine

  movq 32(%rcx), %rsp
	YIELD

  movq 32(%rcx), %rsp
    # sub $8, %rsp
    pushq %rax
    pushq %rcx
    pushq %rdi
    pushq %rdx

	leaq	.LC9(%rip), %rdi
    movl    %edx, %esi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

  popq %rdx
  popq %rdi
  popq %rcx
  popq %rax

	# i += 1
	inc %rax
	# move onto the next coroutine
	add $64, %rcx
	# Loop things
	cmp $10, %rax
	jl _loop
  # jmp _exit
	# xchg -32(%rcx), %rsp

  # mov %rbp, %rsp
  # pushq %rbp 
  # addq $1024, %rsp
  # addq $1024, %rbp
	# movq	%rsp, %rbp

  sub $64, %rcx
  mov 32(%rcx), %rsp
  addq $1024, %rsp

	leaq	.FINISHED(%rip), %rdi
    movl    %edx, %esi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
  # subq $8, %rsp
  # subq $8, %rsp
  # mov %rsp, %rbp
  # popq %rax
  popq %rax
  ret
