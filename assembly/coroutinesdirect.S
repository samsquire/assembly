
.global main
.align 16
.JOINED:
	.string	"Joined thread... %d\n"
	.text
.CREATED:
	.string	"created thread... %d %d\n"
	.text
.FINISHED:
	.string	"finished coroutines\n"
	.text
.TINPUT:
	.string	"thread struct %p %p\n"
	.text
.TDATA:
	.string	"thread received data %p\n"
	.text
.TDATA2:
	.string	"thread data %p %p\n"
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
.INITL:
	.string	"Start INIT RCX is %p RDX is %p\n"
	.text
.STARTED:
	.string	"Starting... %p\n"
	.text
.CALLING:
	.string	"Calling...\n"
	.text
.ENDING:
	.string	"Ending... %p\n"
	.text
.JOINRES:
	.string	"Joinres... %x\n"
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
    LOCAL next_inst, after_yield, me

    pushq %rdi
    pushq %rsi
    pushq %rax
    pushq %rcx
    pushq %rdx
    pushq %rbx

	# movq	%rsp, %rbp
  sub $8, %rsp
  movq    (%rcx), %rsi
	leaq	.LC8(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
  add $8, %rsp
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

   sub $8, %rsp
    movq    %rcx, %rsi
	leaq	.LC6(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
    add $8, %rsp
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
  sub $8, %rsp
  movq    24(%rcx), %rsi
	leaq	.COR(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
  add $8, %rsp
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
  leaq me(%rip), %r11
  movq %r11, 24(%rcx)
  ret
me:
	# we call next_inst to get the instruction pointer of this coroutine.
	# We don't wanna return to the next "pop" so we will need to increment
	# this value so that a yield to this coroutine returns right after the
	# "ret". The call will put this rip into the stack
#	call next_inst
#next_inst:
	# move the just save rip into the rip of the _co_data[coroutine_id]
#	popq 24(%rcx)
	# increment it so a yield from the other coroutine continues from right
	# after the ret
#	addq $(after_yield-next_inst), 24(%rcx)
	# jump, using the value pushed 4 instructions above, into the coroutine
#	ret
#after_yield:
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
	.string	"YIELD RCX: %p\n"
	.text
	.globl	main
	.type	main, @function
.LC7:
	.string	"Coroutine RCX: %p\n"
	.text
	.globl	main
	.type	threadstart, @function
.LC8:
	.string	"YIELD (RCX): %p\n"
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
.align 16
    .skip 1000000
.data_stack1:
  .align 16
	.zero 1000000, 0
.end_data_stack1:
.codata1:
.align 16
    .skip 1000000
.data_stack2:
  .align 16
	.zero 1000000, 0
.end_data_stack2:

.text
costart:
	# pushs $1
loop:
    # sub $8, %rsp
	# pushs $1
	# ADDCO
  pushq %rcx
  sub $8, %rsp
  movq    %rcx, %rsi
	leaq	.LC7(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
  add $8, %rsp
  popq %rcx

  YIELD

  
	JUMP loop
main:
.LFB7:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$1024, %rsp
  # sub $, %rsp
	xorl	%eax, %eax
  movq %rbp, %rsi
	leaq	.STARTED(%rip), %rdi
	call	printf@PLT
	movl	$0, %eax

   movq $1, %rsi
   movq	%rax, -8(%rbp)

   # 1-6	RDI, RSI, RDX, RCX, R8, R9
   leaq .end_data_stack1(%rip), %rax
   
   movq %rax, -300(%rbp)   
   movq %rax, %rdx
   leaq .codata1(%rip), %rax
   movq %rax, %rsi
   movq %rax, -308(%rbp)

   leaq	.TINPUT(%rip), %rdi
   
	  call	printf@PLT
	movl	$0, %eax
   
   pxor %xmm0, %xmm0
   movq %xmm0, -100(%rbp)
   movq %xmm0, -208(%rbp)
   leaq	-308(%rbp), %rdx
   leaq	-100(%rbp), %rsi
   leaq	-208(%rbp), %rax
   movq	%rdx, %rcx
   leaq	threadstart(%rip), %rdx
   movq	%rax, %rdi
   call	pthread_create@PLT
   
   # movl	%eax, -84(%rbp)



 #  movq $1, %rsi
 #  movq -80(%rbp), %rdx
 #  leaq	.CREATED(%rip), %rdi
 #  call	printf@PLT
 #  movl	$0, %eax

   movq	-208(%rbp), %rax
   leaq	-72(%rbp), %rdx
   movq	%rdx, %rsi
   movq	%rax, %rdi
   call	pthread_join@PLT
   movl	$0, %eax
   # movq	-8(%rbp), %rdx
   
   movl %eax, %esi
   leaq	.JOINRES(%rip), %rdi
   call	printf@PLT
   movl	$0, %eax

   movq $1, %rsi
   leaq	.JOINED(%rip), %rdi
   call	printf@PLT
   movl	$0, %eax



   # sub $8, %rsp
   leaq .end_data_stack2(%rip), %rax
   movq %rax, -192(%rbp)         
   leaq .codata2(%rip), %rax
   movq %rax, -184(%rbp)
   leaq	-184(%rbp), %rdx
   leaq	-300(%rbp), %rsi
   leaq	-176(%rbp), %rax
   movq	%rdx, %rcx
   leaq	threadstart(%rip), %rdx
   movq	%rax, %rdi
   movq %xmm0, -160(%rbp)
   movq %xmm0, -176(%rbp)
  # call	pthread_create@PLT
   movl	%eax, -180(%rbp)
   
   movq $2, %rsi
   leaq	.CREATED(%rip), %rdi
   call	printf@PLT
   movl	$0, %eax

   movq	-176(%rbp), %rax
   leaq	-168(%rbp), %rdx
   movq	%rdx, %rsi
   movq	%rax, %rdi
   #call	pthread_join@PLT
   movl	$0, %eax
   movq	-8(%rbp), %rdx

   movq $2, %rsi
   leaq	.JOINED(%rip), %rdi
   call	printf@PLT
   movl	$0, %eax


   # subq	%fs:40, %rdx
   # popq %rax
   # movq $0, %rax
   #addq $256, %rsp
   movq %rbp, %rsi
   leaq	.ENDING(%rip), %rdi
   call	printf@PLT
   movl	$0, %eax
   movq %rsp, %rsi
   leaq	.ENDING(%rip), %rdi
   call	printf@PLT
   movl	$0, %eax
   # movq %rbp, %rsp
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
  sub $8, %rsp
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
  #movq %rdi, %rdx
  # 1-6	RDI, RSI, RDX, RCX, R8, R9
  movq %rdi, %rdx
  movq %rdi, %rsi
  #subq $8, %rdx
  addq $8, %rsi
  #, %rsi
  movq (%rdx), %rdx
  movq (%rsi), %rsi
  # mov %rdx, %rsi
	leaq .TDATA2(%rip), %rax
	movq %rax, %rdi
	movl $0, %eax
	call	printf@PLT
	movl	$0, %eax
  popq %rdi
  
  pushq %rdi
  movq %rdi, %rcx         
  movq (%rcx), %rcx
  pushq %rcx 
  
  
  subq $8, %rsp
  mov %rcx, %rsi
	leaq .TDATA3(%rip), %rax
	movq %rax, %rdi
	movl $0, %eax
	call	printf@PLT
	movl	$0, %eax
  
  addq $8, %rsp
  
  popq %rcx
  popq %rdi
  
  pushq %rcx
  pushq %rdi
  
#addq $8, %rsp
  mov %rcx, %rsi
  sub $8, %rsp
 	leaq	.LC0(%rip), %rax
 	movq	%rax, %rdi
    movq    %rcx, %rsi
 	movl	$0, %eax
 	call	printf@PLT
  addq $8, %rsp

  popq %rdi
  popq %rcx
  
prepare:
	movl	$0, %eax
  movq %rdi, %rcx         
  movq %rdi, %rdx
  # rdi is data, rdx is stack pointer, rcx is data


  addq $8, %rdx
  # address of the stack or data
  # dereference 
 movq (%rdx), %rdx
 movq (%rcx), %rcx


    # sub $8, %rsp

  pushq %rcx
  pushq %rdi
  pushq %rdx
  # 1-6	RDI, RSI, RDX, RCX, R8, R9
leaq	.INITL(%rip), %rax
 	movq	%rax, %rdi
  
  movq    %rcx, %rsi
  
 	movl	$0, %eax
 	call	printf@PLT
  popq %rdx
  popq %rdi
  popq %rcx
  
  movq $0, %rbx
init_co_loop:
  pushq %rcx
  pushq %rdi
  pushq %rdx
  #sub $8, %rsp
 	leaq	.INIT(%rip), %rax
 	movq	%rax, %rdi
  
  movq    %rcx, %rsi
 	movl	$0, %eax
 	call	printf@PLT
  #add $8, %rsp
	# Initialize the rsp
  movl $0, %esi
  popq %rdx
  popq %rdi
  popq %rcx

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
  subq $8, %rsp
  movq %rbx, %rsi
  movl    %ebx, %esi
	leaq	.LC4(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
  add $8, %rsp
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

  sub $8, %rsp
	# movq	%rsp, %rbp
	leaq	.LC1(%rip), %rdi
    movl    %ebx, %esi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
  add $8, %rsp
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

  subq $8, %rsp
	leaq	.LC5(%rip), %rdi
    movq    %rdx, %rsi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
  addq $8, %rsp
    popq %rbx
    popq %rdx
    popq %rcx
    popq %rax
    popq %rsi
    popq %rdi

init_co_loop2:
	cmp $10, %rbx 
	jl init_co_loop
  #pushq %rdi
  sub $8, %rsp
	leaq	.LC10(%rip), %rax
	movq	%rax, %rdi
    movl    %edx, %esi
	movl	$0, %eax
  #sub $8, %rsp
	call	printf@PLT
	movl	$0, %eax
  #add $8, %rsp
	# movq	%rsp, %rbp
	movl	$0, %eax
  popq %rdi
co_initialized:
	# i = 0
	xor %rax, %rax
	# we will start with the first co-routine
	mov %rdi, %rcx
  mov (%rcx), %rcx
_loop:
	# yield to the coroutine

  #movq 32(%rcx), %rsp
	YIELD

  movq 32(%rcx), %rsp
    # sub $8, %rsp
    pushq %rax
    pushq %rcx
    pushq %rdi
    pushq %rdx

   sub $8, %rsp
	leaq	.LC9(%rip), %rdi
    movl    %edx, %esi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
  add $8, %rsp
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
  # popq %rax
  popq %rax
  ret
