.globl switch_to

.align 16
.MSG:
	.string	"CO CoroutineStruct %x\n"
	.text
.EIP:
	.string	"CO EIP... %x\n"
	.text
.CODATA:
	.string	"CO codata... %x\n"
	.text
	# switch_to(struct Coroutine * coroutines, int index, struct Scheduler * scheduler)
	# rdi, %rsi, %rdx, %rcx, %r8 and %r9
switch_to:
# popq %r11
pushq %rbp

movq %rsp, %rbp
subq $1024, %rsp



movq %rdi, (%rbp) # coroutine table
movq %rsi, -8(%rbp) # index
movq %rdx, -16(%rbp) # scheduler

movq %rdi, %rax
movq %rax, %r9
movq %r9, -24(%rbp) # coroutine object

leaq 16(%rdi), %rax
movq (%rax), %r9
movq %r9, -32(%rbp) # coroutine function

leaq 24(%rdi), %rax # load from coroutine object data object
movq (%rax), %r9
movq %r9, -40(%rbp) # coroutine data object

movq -24(%rbp), %r11
#

#pushq %r11
leaq .MSG(%rip), %rdi
movq %r11, %rsi
#call printf@plt
mov $0, %eax

#popq %r11

#pushq %r9
movq -32(%rbp), %r9

leaq .EIP(%rip), %rdi
movq %r9, %rsi
#call printf@plt
mov $0, %eax
#popq %r9
# coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data

#pushq %r9
leaq .CODATA(%rip), %rdi
movq -40(%rbp), %rsi
#call printf@plt
mov $0, %eax
#popq %r9

movq -16(%rbp), %rdi
movq -24(%rbp), %rsi
movq -40(%rbp), %rdx



movq -32(%rbp), %r9
leaq after(%rip), %r11

#movq %rbp, %rsp
# popq %rbp
add $1024, %rsp
# add $8, %rsp
popq %r11
popq %r11
pushq %r11
jmp *%r9
after:
ret