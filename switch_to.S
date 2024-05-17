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
.INDEX:
	.string	"Coroutine index... %d\n"
	.text
	# switch_to(struct Coroutine * coroutines, int index, struct Scheduler * scheduler)
	# rdi, %rsi, %rdx, %rcx, %r8 and %r9
switch_to:
# popq %r11
pushq %rbp

movq %rsp, %rbp
subq $1024, %rsp



movq %rdi, -56(%rbp) # coroutine table
movq %rsi, -8(%rbp) # index
movq %rdx, -16(%rbp) # scheduler

movq %rsi, %rax
imul $32, %rax
addq %rdi, %rax
mov %rax, %r11

mov %r11, %rax
movq %rax, %r9
movq %r9, -24(%rbp) # coroutine object

movq %r11, %rax
leaq 8(%rax), %rax
movq %rax, %r9
movq %r9, -48(%rbp) # rsp

movq %r11, %rax
leaq 16(%rax), %rax
movq (%rax), %r9
movq %r9, -32(%rbp) # coroutine function

movq %r11, %rax
leaq 24(%rax), %rax # load from coroutine object data object
movq (%rax), %r9
movq %r9, -40(%rbp) # coroutine data object
movq (%rax), %rcx

movq -24(%rbp), %r11
#

leaq .INDEX(%rip), %rdi
#call printf@plt
mov $0, %eax

#pushq %r11
leaq .MSG(%rip), %rdi
movq %r11, %rsi
# call printf@plt
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
#leaq after(%rip), %r11

#movq %rbp, %rsp
# popq %rbp
add $1024, %rsp
# add $8, %rsp
 #popq %r11
 popq %r11
#pushq %r11
#movq %r11, %rsp
jmp *%r9
#after:
#ret