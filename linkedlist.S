.global main
.data

  
.linkedlist:
  .align 32
  .skip 100000
.text
.LC3:
	.string	"Linkedlist append: %d in ll %p\n"
	.text
	.globl	main
	.type	main, @function
.LC4:
	.string	"%x "
	.text
	.globl	main
	.type	main, @function
.LC5:
	.string	"\n"
	.text
	.globl	main
	.type	main, @function
main:
  pushq %rbp
  movq %rsp, %rbp
  leaq .linkedlist(%rip),%rdi
  movq $1, %rsi
  call insert_linked_list

  mov $64, %ecx  
row:
  pushq %rcx
  mov $10, %ecx 
  column:
    pushq %rcx
    leaq	.LC4(%rip), %rdi
    leaq .linkedlist(%rip),%rsi
    movl	$0, %eax
    call	printf@PLT
    movl	$0, %eax
    popq %rcx
    dec %ecx
    jnz column 
   
	leaq	.LC5(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
  popq %rcx
  dec %ecx
  jnz row

  popq %rbp
  ret
insert_linked_list:
  pushq %rbp
  movq %rsp, %rbp

  movq %rdi,%r8
/ allocate a new item
  addq $64,%r8
/ point the previous linked list at the beginning of this entry
  mov %r8, -32(%rdi)

/ the value we're putting into the new linked list
  movq %rsi, -16(%rdi)

  pushq %rdi
  pushq %r8

	leaq	.LC3(%rip), %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax

  popq %r8
  popq %rdi
/ return the new linked list item
  mov %r8d,%eax

  popq %rbp
  ret

