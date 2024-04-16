
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
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  401086:	b9 38 00 00 00       	mov    $0x38,%ecx
  40108b:	ba 08 00 00 00       	mov    $0x8,%edx
int main() {
  401090:	41 54                	push   %r12
  401092:	48 8d 35 7a 0f 00 00 	lea    0xf7a(%rip),%rsi        # 402013 <_IO_stdin_used+0x13>
  401099:	bf 01 00 00 00       	mov    $0x1,%edi
  40109e:	55                   	push   %rbp
  40109f:	48 81 ec a0 00 00 00 	sub    $0xa0,%rsp
  4010a6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4010af:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  4010b7:	31 c0                	xor    %eax,%eax
  pthread_attr_t      attr2 = {0};
  4010b9:	0f 29 44 24 60       	movaps %xmm0,0x60(%rsp)
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  4010be:	48 8d 6c 24 20       	lea    0x20(%rsp),%rbp
  
  struct data data; 

   memset(&attr, 0, sizeof(pthread_attr_t));
  printf("atrr %d %d\n", sizeof(pthread_t), sizeof(pthread_attr_t));
  int s = pthread_create(&thread, &attr,
  4010c3:	4c 8d 6c 24 04       	lea    0x4(%rsp),%r13
  pthread_attr_t      attr2 = {0};
  4010c8:	0f 29 44 24 70       	movaps %xmm0,0x70(%rsp)
  4010cd:	0f 29 84 24 80 00 00 00 	movaps %xmm0,0x80(%rsp)
  4010d5:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
  4010da:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  4010df:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  4010e4:	48 c7 84 24 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%rsp)
  pthread_t thread = {0};
  4010f0:	48 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%rsp)
  pthread_t thread2 = {0};
  4010f9:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
  401102:	48 c7 44 24 50 00 00 00 00 	movq   $0x0,0x50(%rsp)
  40110b:	e8 40 ff ff ff       	call   401050 <__printf_chk@plt>
  int s = pthread_create(&thread, &attr,
  401110:	48 89 ee             	mov    %rbp,%rsi
  401113:	48 8d 7c 24 08       	lea    0x8(%rsp),%rdi
  401118:	4c 89 e9             	mov    %r13,%rcx
  40111b:	49 c7 c4 a0 12 40 00 	mov    $0x4012a0,%r12
  
   int d = pthread_create(&thread2, &attr2,
                           func, &data); 
  printf("thread 2 created\n");
  void *result;
  pthread_join(thread, &result);
  401122:	48 8d 6c 24 18       	lea    0x18(%rsp),%rbp
  int s = pthread_create(&thread, &attr,
  401127:	4c 89 e2             	mov    %r12,%rdx
  40112a:	e8 31 ff ff ff       	call   401060 <pthread_create@plt>
  40112f:	b9 38 00 00 00       	mov    $0x38,%ecx
  401134:	ba 08 00 00 00       	mov    $0x8,%edx
  401139:	31 c0                	xor    %eax,%eax
  40113b:	48 8d 35 dd 0e 00 00 	lea    0xedd(%rip),%rsi        # 40201f <_IO_stdin_used+0x1f>
  401142:	bf 01 00 00 00       	mov    $0x1,%edi
  401147:	e8 04 ff ff ff       	call   401050 <__printf_chk@plt>
   int d = pthread_create(&thread2, &attr2,
  40114c:	48 8d 74 24 60       	lea    0x60(%rsp),%rsi
  401151:	4c 89 e9             	mov    %r13,%rcx
  401154:	4c 89 e2             	mov    %r12,%rdx
  401157:	48 8d 7c 24 10       	lea    0x10(%rsp),%rdi
  40115c:	e8 ff fe ff ff       	call   401060 <pthread_create@plt>
  401161:	48 8d 3d d1 0e 00 00 	lea    0xed1(%rip),%rdi        # 402039 <_IO_stdin_used+0x39>
  401168:	e8 c3 fe ff ff       	call   401030 <puts@plt>
  pthread_join(thread, &result);
  40116d:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
  401172:	48 89 ee             	mov    %rbp,%rsi
  401175:	e8 f6 fe ff ff       	call   401070 <pthread_join@plt>
   pthread_join(thread2, &result);
  40117a:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
  40117f:	48 89 ee             	mov    %rbp,%rsi
  401182:	e8 e9 fe ff ff       	call   401070 <pthread_join@plt>
}
  401187:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
  40118f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401198:	75 0f                	jne    4011a9 <main+0x129>
  40119a:	48 81 c4 a0 00 00 00 	add    $0xa0,%rsp
  4011a1:	31 c0                	xor    %eax,%eax
  4011a3:	5d                   	pop    %rbp
  4011a4:	41 5c                	pop    %r12
  4011a6:	41 5d                	pop    %r13
  4011a8:	c3                   	ret
  4011a9:	e8 92 fe ff ff       	call   401040 <__stack_chk_fail@plt>
  4011ae:	66 90                	xchg   %ax,%ax

00000000004011b0 <_start>:
  4011b0:	f3 0f 1e fa          	endbr64
  4011b4:	31 ed                	xor    %ebp,%ebp
  4011b6:	49 89 d1             	mov    %rdx,%r9
  4011b9:	5e                   	pop    %rsi
  4011ba:	48 89 e2             	mov    %rsp,%rdx
  4011bd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4011c1:	50                   	push   %rax
  4011c2:	54                   	push   %rsp
  4011c3:	45 31 c0             	xor    %r8d,%r8d
  4011c6:	31 c9                	xor    %ecx,%ecx
  4011c8:	48 c7 c7 80 10 40 00 	mov    $0x401080,%rdi
  4011cf:	ff 15 1b 2e 00 00    	call   *0x2e1b(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  4011d5:	f4                   	hlt
  4011d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004011e0 <_dl_relocate_static_pie>:
  4011e0:	f3 0f 1e fa          	endbr64
  4011e4:	c3                   	ret
  4011e5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4011ef:	90                   	nop

00000000004011f0 <deregister_tm_clones>:
  4011f0:	b8 10 40 40 00       	mov    $0x404010,%eax
  4011f5:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  4011fb:	74 13                	je     401210 <deregister_tm_clones+0x20>
  4011fd:	b8 00 00 00 00       	mov    $0x0,%eax
  401202:	48 85 c0             	test   %rax,%rax
  401205:	74 09                	je     401210 <deregister_tm_clones+0x20>
  401207:	bf 10 40 40 00       	mov    $0x404010,%edi
  40120c:	ff e0                	jmp    *%rax
  40120e:	66 90                	xchg   %ax,%ax
  401210:	c3                   	ret
  401211:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40121c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401220 <register_tm_clones>:
  401220:	be 10 40 40 00       	mov    $0x404010,%esi
  401225:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  40122c:	48 89 f0             	mov    %rsi,%rax
  40122f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401233:	48 c1 f8 03          	sar    $0x3,%rax
  401237:	48 01 c6             	add    %rax,%rsi
  40123a:	48 d1 fe             	sar    %rsi
  40123d:	74 11                	je     401250 <register_tm_clones+0x30>
  40123f:	b8 00 00 00 00       	mov    $0x0,%eax
  401244:	48 85 c0             	test   %rax,%rax
  401247:	74 07                	je     401250 <register_tm_clones+0x30>
  401249:	bf 10 40 40 00       	mov    $0x404010,%edi
  40124e:	ff e0                	jmp    *%rax
  401250:	c3                   	ret
  401251:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40125c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401260 <__do_global_dtors_aux>:
  401260:	f3 0f 1e fa          	endbr64
  401264:	80 3d a5 2d 00 00 00 	cmpb   $0x0,0x2da5(%rip)        # 404010 <__TMC_END__>
  40126b:	75 13                	jne    401280 <__do_global_dtors_aux+0x20>
  40126d:	55                   	push   %rbp
  40126e:	48 89 e5             	mov    %rsp,%rbp
  401271:	e8 7a ff ff ff       	call   4011f0 <deregister_tm_clones>
  401276:	c6 05 93 2d 00 00 01 	movb   $0x1,0x2d93(%rip)        # 404010 <__TMC_END__>
  40127d:	5d                   	pop    %rbp
  40127e:	c3                   	ret
  40127f:	90                   	nop
  401280:	c3                   	ret
  401281:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40128c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401290 <frame_dummy>:
  401290:	f3 0f 1e fa          	endbr64
  401294:	eb 8a                	jmp    401220 <register_tm_clones>
  401296:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004012a0 <func>:
void *func(void *data) {
  4012a0:	48 83 ec 08          	sub    $0x8,%rsp
  4012a4:	48 8d 3d 59 0d 00 00 	lea    0xd59(%rip),%rdi        # 402004 <_IO_stdin_used+0x4>
  4012ab:	e8 80 fd ff ff       	call   401030 <puts@plt>
}
  4012b0:	31 c0                	xor    %eax,%eax
  4012b2:	48 83 c4 08          	add    $0x8,%rsp
  4012b6:	c3                   	ret

Disassembly of section .fini:

00000000004012b8 <_fini>:
  4012b8:	f3 0f 1e fa          	endbr64
  4012bc:	48 83 ec 08          	sub    $0x8,%rsp
  4012c0:	48 83 c4 08          	add    $0x8,%rsp
  4012c4:	c3                   	ret
