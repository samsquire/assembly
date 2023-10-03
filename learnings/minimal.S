.global main
.data
a.codata:
.data
    .skip 40

data_stack:
.data
    .zero 400, 0
a.end_data_stack:
.data
.LC0:
	.string	"It worked: %p\n"
	.text
	.globl	main
	.type	main, @function

.text
main:
    leaq a.end_data_stack(%rip),%rdx
	leaq a.codata(%rip), %rcx         
    pushq %rdx
    pushq %rcx

 	pushq	%rbp
 	movq	%rsp, %rbp
 	leaq	.LC0(%rip), %rax
    movq %rcx, %rsi
 	movq	%rax, %rdi
 	movl	$0, %eax
 	call	printf@PLT

    movq a.end_data_stack(%rip),%rdx
 	movq	%rsp, %rbp
 	leaq	.LC0(%rip), %rax
    movq %rdx, %rsi
 	movq	%rax, %rdi
 	movl	$0, %eax
 	call	printf@PLT

 	popq	%rbp
    popq %rcx
    popq %rdx
	movq    %rdx, (%rcx)
    ret

