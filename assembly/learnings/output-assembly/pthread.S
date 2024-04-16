
pthread:     file format elf64-x86-64


Disassembly of section .init:

0000000000401000 <_init>:
  401000:	f3 0f 1e fa          	endbr64
  401004:	48 83 ec 08          	sub    $0x8,%rsp
  401008:	48 8b 05 e9 2f 00 00 	mov    0x2fe9(%rip),%rax        # 403ff8 <__gmon_start__@Base>
  40100f:	48 85 c0             	test   %rax,%rax
  401012:	74 02                	je     401016 <_init+0x16>
  401014:	ff d0                	call   *%rax
  401016:	48 83 c4 08          	add    $0x8,%rsp
  40101a:	c3                   	ret

Disassembly of section .plt:

0000000000401020 <puts@plt-0x10>:
  401020:	ff 35 92 2f 00 00    	push   0x2f92(%rip)        # 403fb8 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 94 2f 00 00    	jmp    *0x2f94(%rip)        # 403fc0 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <puts@plt>:
  401030:	ff 25 92 2f 00 00    	jmp    *0x2f92(%rip)        # 403fc8 <puts@GLIBC_2.2.5>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <__stack_chk_fail@plt>:
  401040:	ff 25 8a 2f 00 00    	jmp    *0x2f8a(%rip)        # 403fd0 <__stack_chk_fail@GLIBC_2.4>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <__printf_chk@plt>:
  401050:	ff 25 82 2f 00 00    	jmp    *0x2f82(%rip)        # 403fd8 <__printf_chk@GLIBC_2.3.4>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <pthread_create@plt>:
  401060:	ff 25 7a 2f 00 00    	jmp    *0x2f7a(%rip)        # 403fe0 <pthread_create@GLIBC_2.34>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <pthread_join@plt>:
  401070:	ff 25 72 2f 00 00    	jmp    *0x2f72(%rip)        # 403fe8 <pthread_join@GLIBC_2.34>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

0000000000401080 <main>:

struct data {
  int data;
};

int main() {
  401080:	41 55                	push   %r13
  ssize_t             stack_size;
  pthread_attr_t      attr;;
  pthread_attr_t      attr2 = {0};
  401082:	66 0f ef c0          	pxor   %xmm0,%xmm0
int main() {
  401086:	41 54                	push   %r12
  401088:	55                   	push   %rbp
  401089:	48 81 ec a0 00 00 00 	sub    $0xa0,%rsp
  
  struct data data; 

   memset(&attr, 0, sizeof(pthread_attr_t));
  
  int s = pthread_create(&thread, &attr,
  401090:	49 c7 c4 80 12 40 00 	mov    $0x401280,%r12
int main() {
  401097:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4010a0:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  4010a8:	31 c0                	xor    %eax,%eax
  int s = pthread_create(&thread, &attr,
  4010aa:	4c 8d 6c 24 04       	lea    0x4(%rsp),%r13
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  4010af:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
  pthread_attr_t      attr2 = {0};
  4010b4:	0f 29 44 24 60       	movaps %xmm0,0x60(%rsp)
  int s = pthread_create(&thread, &attr,
  4010b9:	48 8d 7c 24 08       	lea    0x8(%rsp),%rdi
  4010be:	4c 89 e9             	mov    %r13,%rcx
  4010c1:	4c 89 e2             	mov    %r12,%rdx
  pthread_attr_t      attr2 = {0};
  4010c4:	0f 29 44 24 70       	movaps %xmm0,0x70(%rsp)
  4010c9:	0f 29 84 24 80 00 00 00 	movaps %xmm0,0x80(%rsp)
  
   int d = pthread_create(&thread2, &attr2,
                           func, &data); 
  printf("thread 2 created\n");
  void *result;
  pthread_join(thread, &result);
  4010d1:	48 8d 6c 24 18       	lea    0x18(%rsp),%rbp
  4010d6:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
  4010db:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  4010e0:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  pthread_attr_t      attr2 = {0};
  4010e5:	48 c7 84 24 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%rsp)
  pthread_t thread = {0};
  4010f1:	48 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%rsp)
  pthread_t thread2 = {0};
  4010fa:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
  401103:	48 c7 44 24 50 00 00 00 00 	movq   $0x0,0x50(%rsp)
  int s = pthread_create(&thread, &attr,
  40110c:	e8 4f ff ff ff       	call   401060 <pthread_create@plt>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  401111:	b9 38 00 00 00       	mov    $0x38,%ecx
  401116:	ba 08 00 00 00       	mov    $0x8,%edx
  40111b:	31 c0                	xor    %eax,%eax
  40111d:	48 8d 35 ef 0e 00 00 	lea    0xeef(%rip),%rsi        # 402013 <_IO_stdin_used+0x13>
  401124:	bf 01 00 00 00       	mov    $0x1,%edi
  401129:	e8 22 ff ff ff       	call   401050 <__printf_chk@plt>
   int d = pthread_create(&thread2, &attr2,
  40112e:	48 8d 74 24 60       	lea    0x60(%rsp),%rsi
  401133:	4c 89 e9             	mov    %r13,%rcx
  401136:	4c 89 e2             	mov    %r12,%rdx
  401139:	48 8d 7c 24 10       	lea    0x10(%rsp),%rdi
  40113e:	e8 1d ff ff ff       	call   401060 <pthread_create@plt>
  401143:	48 8d 3d e3 0e 00 00 	lea    0xee3(%rip),%rdi        # 40202d <_IO_stdin_used+0x2d>
  40114a:	e8 e1 fe ff ff       	call   401030 <puts@plt>
  pthread_join(thread, &result);
  40114f:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
  401154:	48 89 ee             	mov    %rbp,%rsi
  401157:	e8 14 ff ff ff       	call   401070 <pthread_join@plt>
   pthread_join(thread2, &result);
  40115c:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
  401161:	48 89 ee             	mov    %rbp,%rsi
  401164:	e8 07 ff ff ff       	call   401070 <pthread_join@plt>
}
  401169:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
  401171:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40117a:	75 0f                	jne    40118b <main+0x10b>
  40117c:	48 81 c4 a0 00 00 00 	add    $0xa0,%rsp
  401183:	31 c0                	xor    %eax,%eax
  401185:	5d                   	pop    %rbp
  401186:	41 5c                	pop    %r12
  401188:	41 5d                	pop    %r13
  40118a:	c3                   	ret
  40118b:	e8 b0 fe ff ff       	call   401040 <__stack_chk_fail@plt>

0000000000401190 <_start>:
  401190:	f3 0f 1e fa          	endbr64
  401194:	31 ed                	xor    %ebp,%ebp
  401196:	49 89 d1             	mov    %rdx,%r9
  401199:	5e                   	pop    %rsi
  40119a:	48 89 e2             	mov    %rsp,%rdx
  40119d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4011a1:	50                   	push   %rax
  4011a2:	54                   	push   %rsp
  4011a3:	45 31 c0             	xor    %r8d,%r8d
  4011a6:	31 c9                	xor    %ecx,%ecx
  4011a8:	48 c7 c7 80 10 40 00 	mov    $0x401080,%rdi
  4011af:	ff 15 3b 2e 00 00    	call   *0x2e3b(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  4011b5:	f4                   	hlt
  4011b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004011c0 <_dl_relocate_static_pie>:
  4011c0:	f3 0f 1e fa          	endbr64
  4011c4:	c3                   	ret
  4011c5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4011cf:	90                   	nop

00000000004011d0 <deregister_tm_clones>:
  4011d0:	b8 10 40 40 00       	mov    $0x404010,%eax
  4011d5:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  4011db:	74 13                	je     4011f0 <deregister_tm_clones+0x20>
  4011dd:	b8 00 00 00 00       	mov    $0x0,%eax
  4011e2:	48 85 c0             	test   %rax,%rax
  4011e5:	74 09                	je     4011f0 <deregister_tm_clones+0x20>
  4011e7:	bf 10 40 40 00       	mov    $0x404010,%edi
  4011ec:	ff e0                	jmp    *%rax
  4011ee:	66 90                	xchg   %ax,%ax
  4011f0:	c3                   	ret
  4011f1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4011fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401200 <register_tm_clones>:
  401200:	be 10 40 40 00       	mov    $0x404010,%esi
  401205:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  40120c:	48 89 f0             	mov    %rsi,%rax
  40120f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401213:	48 c1 f8 03          	sar    $0x3,%rax
  401217:	48 01 c6             	add    %rax,%rsi
  40121a:	48 d1 fe             	sar    %rsi
  40121d:	74 11                	je     401230 <register_tm_clones+0x30>
  40121f:	b8 00 00 00 00       	mov    $0x0,%eax
  401224:	48 85 c0             	test   %rax,%rax
  401227:	74 07                	je     401230 <register_tm_clones+0x30>
  401229:	bf 10 40 40 00       	mov    $0x404010,%edi
  40122e:	ff e0                	jmp    *%rax
  401230:	c3                   	ret
  401231:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40123c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401240 <__do_global_dtors_aux>:
  401240:	f3 0f 1e fa          	endbr64
  401244:	80 3d c5 2d 00 00 00 	cmpb   $0x0,0x2dc5(%rip)        # 404010 <__TMC_END__>
  40124b:	75 13                	jne    401260 <__do_global_dtors_aux+0x20>
  40124d:	55                   	push   %rbp
  40124e:	48 89 e5             	mov    %rsp,%rbp
  401251:	e8 7a ff ff ff       	call   4011d0 <deregister_tm_clones>
  401256:	c6 05 b3 2d 00 00 01 	movb   $0x1,0x2db3(%rip)        # 404010 <__TMC_END__>
  40125d:	5d                   	pop    %rbp
  40125e:	c3                   	ret
  40125f:	90                   	nop
  401260:	c3                   	ret
  401261:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40126c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401270 <frame_dummy>:
  401270:	f3 0f 1e fa          	endbr64
  401274:	eb 8a                	jmp    401200 <register_tm_clones>
  401276:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401280 <func>:
void *func(void *data) {
  401280:	48 83 ec 08          	sub    $0x8,%rsp
  401284:	48 8d 3d 79 0d 00 00 	lea    0xd79(%rip),%rdi        # 402004 <_IO_stdin_used+0x4>
  40128b:	e8 a0 fd ff ff       	call   401030 <puts@plt>
}
  401290:	31 c0                	xor    %eax,%eax
  401292:	48 83 c4 08          	add    $0x8,%rsp
  401296:	c3                   	ret

Disassembly of section .fini:

0000000000401298 <_fini>:
  401298:	f3 0f 1e fa          	endbr64
  40129c:	48 83 ec 08          	sub    $0x8,%rsp
  4012a0:	48 83 c4 08          	add    $0x8,%rsp
  4012a4:	c3                   	ret
