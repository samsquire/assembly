# assembly

Welcome to Samuel Squire's assembly repository.

I am a beginner at assembly.

This repository has a Gnu Assembly port of the coroutines implementation of [Small VMS & Coroutines](https://blog.dziban.net/coroutines/) by [Marce Coll](https://github.com/MarceColl) in coroutines.S

In threadedcoroutines.S there is a multithreading with coroutines.

# tutorial

`rbp` is the frame pointer, it designates the position in the stack where local variables start in this function.

`rsp` is the stack pointer, it grows downwards or negatively.

To start a function with a function epilogue. We push the previous frame's pointer to the stack, so we can restore the %rsp to %rbp when the function ends:

```
push %rbp
movq %rsp, %rbp	
subq $32, %rsp 		# create room for 4x 8 byte (64 bit each) integers
```

To end a function with a function prologue:

```
leave
```

or 

```
addq $32, %rsp		# free the local variables on the stack
mov %rbp, %rsp		# restore the stack position to the beginning of the function frame 
popq %rbp			# just remove the current function's frame pointer

```

To deference a pointer of a local variable

```
leaq -32(%rbp), %rax
```

To send a struct to another function:

```
struct {
	int field1;
	int field2;
}
```

As an example, we send two global fields but they could of course be anything:

```
leaq .field1(%rip), %rax
moveq %rax, -32(%rbp)
leaq .field2(%rip), %rax
moveq %rax, -40(%rbp)

moveq -32(rbp), %rdi
call function
```



# calling convention

| Integer/Pointer Arguments 1-6 | RDI, RSI, RDX, RCX, R8, R9 |
| ----------------------------- | -------------------------- |
| Floating Point Arguments 1-8  | XMM0 - XMM7                |
| Excess Arguments              | Stack                      |
| Static chain pointer          | R10                        |
