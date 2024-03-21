
threadsafe-workqueue:     file format elf64-x86-64


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

0000000000401020 <__snprintf_chk@plt-0x10>:
  401020:	ff 35 72 2f 00 00    	push   0x2f72(%rip)        # 403f98 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 74 2f 00 00    	jmp    *0x2f74(%rip)        # 403fa0 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <__snprintf_chk@plt>:
  401030:	ff 25 72 2f 00 00    	jmp    *0x2f72(%rip)        # 403fa8 <__snprintf_chk@GLIBC_2.3.4>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <pthread_setaffinity_np@plt>:
  401040:	ff 25 6a 2f 00 00    	jmp    *0x2f6a(%rip)        # 403fb0 <pthread_setaffinity_np@GLIBC_2.34>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <puts@plt>:
  401050:	ff 25 62 2f 00 00    	jmp    *0x2f62(%rip)        # 403fb8 <puts@GLIBC_2.2.5>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <__stack_chk_fail@plt>:
  401060:	ff 25 5a 2f 00 00    	jmp    *0x2f5a(%rip)        # 403fc0 <__stack_chk_fail@GLIBC_2.4>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <nanosleep@plt>:
  401070:	ff 25 52 2f 00 00    	jmp    *0x2f52(%rip)        # 403fc8 <nanosleep@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <calloc@plt>:
  401080:	ff 25 4a 2f 00 00    	jmp    *0x2f4a(%rip)        # 403fd0 <calloc@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <__printf_chk@plt>:
  401090:	ff 25 42 2f 00 00    	jmp    *0x2f42(%rip)        # 403fd8 <__printf_chk@GLIBC_2.3.4>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <pthread_create@plt>:
  4010a0:	ff 25 3a 2f 00 00    	jmp    *0x2f3a(%rip)        # 403fe0 <pthread_create@GLIBC_2.34>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <pthread_join@plt>:
  4010b0:	ff 25 32 2f 00 00    	jmp    *0x2f32(%rip)        # 403fe8 <pthread_join@GLIBC_2.34>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

00000000004010c0 <main>:
    
    
    
  }

int main(int argc, char **argv) {
  4010c0:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4010c2:	ba 05 00 00 00       	mov    $0x5,%edx
  4010c7:	bf 01 00 00 00       	mov    $0x1,%edi
  4010cc:	48 8d 35 40 0f 00 00 	lea    0xf40(%rip),%rsi        # 402013 <_IO_stdin_used+0x13>
  4010d3:	41 56                	push   %r14
  4010d5:	41 55                	push   %r13
  4010d7:	41 54                	push   %r12
  4010d9:	55                   	push   %rbp
  4010da:	53                   	push   %rbx
  4010db:	48 83 ec 68          	sub    $0x68,%rsp
  4010df:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4010e8:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  4010ed:	31 c0                	xor    %eax,%eax
  4010ef:	e8 9c ff ff ff       	call   401090 <__printf_chk@plt>
  int worksize = 10;
  int threadsize = 5;
  printf("Starting %d workers\n", threadsize);
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  4010f4:	be 08 00 00 00       	mov    $0x8,%esi
  4010f9:	bf 05 00 00 00       	mov    $0x5,%edi
  4010fe:	e8 7d ff ff ff       	call   401080 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401103:	be 38 00 00 00       	mov    $0x38,%esi
  401108:	bf 05 00 00 00       	mov    $0x5,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40110d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401112:	e8 69 ff ff ff       	call   401080 <calloc@plt>
  struct Data *data = calloc(threadsize, sizeof(struct Data));
  401117:	be 48 00 00 00       	mov    $0x48,%esi
  40111c:	bf 05 00 00 00       	mov    $0x5,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401121:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  struct Data *data = calloc(threadsize, sizeof(struct Data));
  401126:	e8 55 ff ff ff       	call   401080 <calloc@plt>
  struct Work *works = calloc(100, sizeof(struct Work));
  40112b:	be 08 00 00 00       	mov    $0x8,%esi
  401130:	bf 64 00 00 00       	mov    $0x64,%edi
  401135:	66 48 0f 6e d0       	movq   %rax,%xmm2
  struct Data *data = calloc(threadsize, sizeof(struct Data));
  40113a:	48 89 c5             	mov    %rax,%rbp
  40113d:	66 0f 6c d2          	punpcklqdq %xmm2,%xmm2
  401141:	0f 29 14 24          	movaps %xmm2,(%rsp)
  struct Work *works = calloc(100, sizeof(struct Work));
  401145:	e8 36 ff ff ff       	call   401080 <calloc@plt>
  
  for (int i = 0; i < 100; i++) {
  40114a:	66 0f 6f 05 6e 0f 00 00 	movdqa 0xf6e(%rip),%xmm0        # 4020c0 <_IO_stdin_used+0xc0>
  401152:	48 89 c2             	mov    %rax,%rdx
  401155:	48 8d 88 20 03 00 00 	lea    0x320(%rax),%rcx
  40115c:	0f 1f 40 00          	nopl   0x0(%rax)
    works[i].taskindex = 2;
  401160:	0f 11 02             	movups %xmm0,(%rdx)
  for (int i = 0; i < 100; i++) {
  401163:	48 83 c2 10          	add    $0x10,%rdx
  401167:	48 39 d1             	cmp    %rdx,%rcx
  40116a:	75 f4                	jne    401160 <main+0xa0>
    works[i].available = 1;
    
  }
  int cpu = 0;
  data[0].works = works;
  40116c:	48 89 45 30          	mov    %rax,0x30(%rbp)
  for (int x = 0; x < threadsize ; x++) {
  401170:	49 89 ed             	mov    %rbp,%r13
  data[0].works = works;
  401173:	48 89 eb             	mov    %rbp,%rbx
  int cpu = 0;
  401176:	45 31 e4             	xor    %r12d,%r12d
  401179:	4c 8d 3d 20 0f 00 00 	lea    0xf20(%rip),%r15        # 4020a0 <_IO_stdin_used+0xa0>
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401180:	45 89 e6             	mov    %r12d,%r14d
  401183:	be 80 00 00 00       	mov    $0x80,%esi
    CPU_SET(cpu += 1, data[x].cpu_set);
  401188:	41 83 c4 01          	add    $0x1,%r12d
  for (int x = 0; x < threadsize ; x++) {
  40118c:	48 83 c3 48          	add    $0x48,%rbx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401190:	bf 01 00 00 00       	mov    $0x1,%edi
  401195:	e8 e6 fe ff ff       	call   401080 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  40119a:	44 89 e1             	mov    %r12d,%ecx
  40119d:	ba 01 00 00 00       	mov    $0x1,%edx
  4011a2:	4c 89 fe             	mov    %r15,%rsi
  4011a5:	48 d3 e2             	shl    %cl,%rdx
  4011a8:	48 09 10             	or     %rdx,(%rax)
  4011ab:	44 89 e1             	mov    %r12d,%ecx
  4011ae:	44 89 f2             	mov    %r14d,%edx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4011b1:	48 89 43 f0          	mov    %rax,-0x10(%rbx)
  4011b5:	bf 01 00 00 00       	mov    $0x1,%edi
  4011ba:	31 c0                	xor    %eax,%eax
  4011bc:	e8 cf fe ff ff       	call   401090 <__printf_chk@plt>
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].running = 1;
    data[x].threadindex = x;
    data[x].worksize = worksize;
    data[x].threadsize = threadsize;
    data[x].main = &data[0];
  4011c1:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
    data[x].threadindex = x;
  4011c6:	44 89 73 dc          	mov    %r14d,-0x24(%rbx)
    data[x].threads = data;
    data[x].wantindex = -1;
  4011ca:	48 8b 05 0f 0f 00 00 	mov    0xf0f(%rip),%rax        # 4020e0 <_IO_stdin_used+0xe0>
    data[x].worksize = worksize;
  4011d1:	c7 43 d8 0a 00 00 00 	movl   $0xa,-0x28(%rbx)
    data[x].threadsize = threadsize;
  4011d8:	c7 43 e0 05 00 00 00 	movl   $0x5,-0x20(%rbx)
    data[x].main = &data[0];
  4011df:	0f 11 4b b8          	movups %xmm1,-0x48(%rbx)
    data[x].wantindex = -1;
  4011e3:	48 89 43 d0          	mov    %rax,-0x30(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  4011e7:	41 83 fc 05          	cmp    $0x5,%r12d
  4011eb:	75 93                	jne    401180 <main+0xc0>
  4011ed:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
  4011f2:	49 c7 c6 d0 13 40 00 	mov    $0x4013d0,%r14
  4011f9:	4c 8d bd 68 01 00 00 	lea    0x168(%rbp),%r15
  401200:	4c 89 e3             	mov    %r12,%rbx
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  401203:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
  401208:	4c 89 e9             	mov    %r13,%rcx
  40120b:	4c 89 e7             	mov    %r12,%rdi
  40120e:	4c 89 f2             	mov    %r14,%rdx
  for (int x = 0; x < threadsize ; x++) {
  401211:	49 83 c5 48          	add    $0x48,%r13
  401215:	49 83 c4 08          	add    $0x8,%r12
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  401219:	e8 82 fe ff ff       	call   4010a0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  40121e:	49 8b 55 f0          	mov    -0x10(%r13),%rdx
  401222:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
  401227:	be 08 00 00 00       	mov    $0x8,%esi
  40122c:	e8 0f fe ff ff       	call   401040 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  401231:	4d 39 fd             	cmp    %r15,%r13
  401234:	75 cd                	jne    401203 <main+0x143>
  }
  struct timespec time = {
  401236:	66 0f 6f 05 92 0e 00 00 	movdqa 0xe92(%rip),%xmm0        # 4020d0 <_IO_stdin_used+0xd0>
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  40123e:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  401243:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
  struct timespec time = {
  401248:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  struct timespec rem = {
  40124d:	66 0f ef c0          	pxor   %xmm0,%xmm0
  401251:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  nanosleep(&time, &rem);
  401256:	e8 15 fe ff ff       	call   401070 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  40125b:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
  401260:	c7 45 1c 00 00 00 00 	movl   $0x0,0x1c(%rbp)
  401267:	c7 45 64 00 00 00 00 	movl   $0x0,0x64(%rbp)
  40126e:	c7 85 ac 00 00 00 00 00 00 00 	movl   $0x0,0xac(%rbp)
  401278:	49 83 c4 28          	add    $0x28,%r12
  40127c:	c7 85 f4 00 00 00 00 00 00 00 	movl   $0x0,0xf4(%rbp)
  401286:	c7 85 3c 01 00 00 00 00 00 00 	movl   $0x0,0x13c(%rbp)
    
  }
  for (int x = 0; x < threadsize; x++) {
  401290:	48 8d 6c 24 28       	lea    0x28(%rsp),%rbp
    void *res;
    pthread_join(thread[x], &res);
  401295:	48 8b 3b             	mov    (%rbx),%rdi
  401298:	48 89 ee             	mov    %rbp,%rsi
  for (int x = 0; x < threadsize; x++) {
  40129b:	48 83 c3 08          	add    $0x8,%rbx
    pthread_join(thread[x], &res);
  40129f:	e8 0c fe ff ff       	call   4010b0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  4012a4:	49 39 dc             	cmp    %rbx,%r12
  4012a7:	75 ec                	jne    401295 <main+0x1d5>
  4012a9:	48 8d 3d 78 0d 00 00 	lea    0xd78(%rip),%rdi        # 402028 <_IO_stdin_used+0x28>
  4012b0:	e8 9b fd ff ff       	call   401050 <puts@plt>
  }
  printf("finished simulation.\n");
  4012b5:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  4012ba:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4012c3:	75 11                	jne    4012d6 <main+0x216>
  4012c5:	48 83 c4 68          	add    $0x68,%rsp
  4012c9:	31 c0                	xor    %eax,%eax
  4012cb:	5b                   	pop    %rbx
  4012cc:	5d                   	pop    %rbp
  4012cd:	41 5c                	pop    %r12
  4012cf:	41 5d                	pop    %r13
  4012d1:	41 5e                	pop    %r14
  4012d3:	41 5f                	pop    %r15
  4012d5:	c3                   	ret
  4012d6:	e8 85 fd ff ff       	call   401060 <__stack_chk_fail@plt>
  4012db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000004012e0 <_start>:
  4012e0:	f3 0f 1e fa          	endbr64
  4012e4:	31 ed                	xor    %ebp,%ebp
  4012e6:	49 89 d1             	mov    %rdx,%r9
  4012e9:	5e                   	pop    %rsi
  4012ea:	48 89 e2             	mov    %rsp,%rdx
  4012ed:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4012f1:	50                   	push   %rax
  4012f2:	54                   	push   %rsp
  4012f3:	45 31 c0             	xor    %r8d,%r8d
  4012f6:	31 c9                	xor    %ecx,%ecx
  4012f8:	48 c7 c7 c0 10 40 00 	mov    $0x4010c0,%rdi
  4012ff:	ff 15 eb 2c 00 00    	call   *0x2ceb(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  401305:	f4                   	hlt
  401306:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401310 <_dl_relocate_static_pie>:
  401310:	f3 0f 1e fa          	endbr64
  401314:	c3                   	ret
  401315:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40131f:	90                   	nop

0000000000401320 <deregister_tm_clones>:
  401320:	b8 10 40 40 00       	mov    $0x404010,%eax
  401325:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  40132b:	74 13                	je     401340 <deregister_tm_clones+0x20>
  40132d:	b8 00 00 00 00       	mov    $0x0,%eax
  401332:	48 85 c0             	test   %rax,%rax
  401335:	74 09                	je     401340 <deregister_tm_clones+0x20>
  401337:	bf 10 40 40 00       	mov    $0x404010,%edi
  40133c:	ff e0                	jmp    *%rax
  40133e:	66 90                	xchg   %ax,%ax
  401340:	c3                   	ret
  401341:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40134c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401350 <register_tm_clones>:
  401350:	be 10 40 40 00       	mov    $0x404010,%esi
  401355:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  40135c:	48 89 f0             	mov    %rsi,%rax
  40135f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401363:	48 c1 f8 03          	sar    $0x3,%rax
  401367:	48 01 c6             	add    %rax,%rsi
  40136a:	48 d1 fe             	sar    %rsi
  40136d:	74 11                	je     401380 <register_tm_clones+0x30>
  40136f:	b8 00 00 00 00       	mov    $0x0,%eax
  401374:	48 85 c0             	test   %rax,%rax
  401377:	74 07                	je     401380 <register_tm_clones+0x30>
  401379:	bf 10 40 40 00       	mov    $0x404010,%edi
  40137e:	ff e0                	jmp    *%rax
  401380:	c3                   	ret
  401381:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40138c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401390 <__do_global_dtors_aux>:
  401390:	f3 0f 1e fa          	endbr64
  401394:	80 3d 75 2c 00 00 00 	cmpb   $0x0,0x2c75(%rip)        # 404010 <__TMC_END__>
  40139b:	75 13                	jne    4013b0 <__do_global_dtors_aux+0x20>
  40139d:	55                   	push   %rbp
  40139e:	48 89 e5             	mov    %rsp,%rbp
  4013a1:	e8 7a ff ff ff       	call   401320 <deregister_tm_clones>
  4013a6:	c6 05 63 2c 00 00 01 	movb   $0x1,0x2c63(%rip)        # 404010 <__TMC_END__>
  4013ad:	5d                   	pop    %rbp
  4013ae:	c3                   	ret
  4013af:	90                   	nop
  4013b0:	c3                   	ret
  4013b1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4013bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004013c0 <frame_dummy>:
  4013c0:	f3 0f 1e fa          	endbr64
  4013c4:	eb 8a                	jmp    401350 <register_tm_clones>
  4013c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004013d0 <work>:
void * work(void * arg) {
  4013d0:	41 56                	push   %r14
  char * output = calloc(100, sizeof(char));
  4013d2:	be 01 00 00 00       	mov    $0x1,%esi
void * work(void * arg) {
  4013d7:	41 55                	push   %r13
  4013d9:	41 54                	push   %r12
  4013db:	49 89 fc             	mov    %rdi,%r12
  char * output = calloc(100, sizeof(char));
  4013de:	bf 64 00 00 00       	mov    $0x64,%edi
void * work(void * arg) {
  4013e3:	55                   	push   %rbp
  4013e4:	53                   	push   %rbx
  char * output = calloc(100, sizeof(char));
  4013e5:	e8 96 fc ff ff       	call   401080 <calloc@plt>
  while (data->running == 1) {
  4013ea:	41 83 7c 24 1c 01    	cmpl   $0x1,0x1c(%r12)
  4013f0:	0f 85 5c 01 00 00    	jne    401552 <work+0x182>
  4013f6:	4d 8b 04 24          	mov    (%r12),%r8
  4013fa:	49 89 c5             	mov    %rax,%r13
  4013fd:	48 8d 2d 00 0c 00 00 	lea    0xc00(%rip),%rbp        # 402004 <_IO_stdin_used+0x4>
  401404:	eb 16                	jmp    40141c <work+0x4c>
  401406:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401410:	41 83 7c 24 1c 01    	cmpl   $0x1,0x1c(%r12)
  401416:	0f 85 36 01 00 00    	jne    401552 <work+0x182>
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  40141c:	31 c0                	xor    %eax,%eax
  40141e:	b9 0c 00 00 00       	mov    $0xc,%ecx
  401423:	4c 89 ef             	mov    %r13,%rdi
    if (data->threadindex != 0 && data->main->workindex >= data->worksize) { continue; }
  401426:	45 8b 4c 24 24       	mov    0x24(%r12),%r9d
  40142b:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  40142e:	41 8b 44 24 20       	mov    0x20(%r12),%eax
  401433:	45 85 c9             	test   %r9d,%r9d
  401436:	c7 07 00 00 00 00    	movl   $0x0,(%rdi)
  40143c:	0f 84 1e 01 00 00    	je     401560 <work+0x190>
  401442:	41 39 40 14          	cmp    %eax,0x14(%r8)
  401446:	7d c8                	jge    401410 <work+0x40>
    int target = (data->main->workindex);
  401448:	4d 8b 04 24          	mov    (%r12),%r8
   for (int x = 0 ; x < data->threadsize ; x++ ) {
  40144c:	41 8b 74 24 28       	mov    0x28(%r12),%esi
    int target = (data->main->workindex);
  401451:	41 8b 48 14          	mov    0x14(%r8),%ecx
   for (int x = 0 ; x < data->threadsize ; x++ ) {
  401455:	85 f6                	test   %esi,%esi
  401457:	0f 8e a6 01 00 00    	jle    401603 <work+0x233>
    if (data->main->works[x].available == 1 ) {
  40145d:	49 8b 78 30          	mov    0x30(%r8),%rdi
  401461:	48 63 d6             	movslq %esi,%rdx
  401464:	31 c0                	xor    %eax,%eax
  401466:	eb 15                	jmp    40147d <work+0xad>
  401468:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
   for (int x = 0 ; x < data->threadsize ; x++ ) {
  401470:	48 83 c0 01          	add    $0x1,%rax
  401474:	48 39 d0             	cmp    %rdx,%rax
  401477:	0f 84 3b 01 00 00    	je     4015b8 <work+0x1e8>
    if (data->main->works[x].available == 1 ) {
  40147d:	83 7c c7 04 01       	cmpl   $0x1,0x4(%rdi,%rax,8)
  401482:	89 c3                	mov    %eax,%ebx
  401484:	75 ea                	jne    401470 <work+0xa0>
      data->threads[data->threadindex].wantindex = target;
  401486:	49 63 4c 24 24       	movslq 0x24(%r12),%rcx
  40148b:	49 8b 54 24 08       	mov    0x8(%r12),%rdx
  401490:	49 89 c9             	mov    %rcx,%r9
  401493:	48 8d 0c c9          	lea    (%rcx,%rcx,8),%rcx
  401497:	4c 8d 14 ca          	lea    (%rdx,%rcx,8),%r10
  40149b:	41 89 42 18          	mov    %eax,0x18(%r10)
      for (int x = 0; x < data->threadsize ; x++ ) {
  40149f:	48 83 c2 18          	add    $0x18,%rdx
    int target = (data->main->workindex);
  4014a3:	31 c0                	xor    %eax,%eax
  4014a5:	0f 1f 00             	nopl   (%rax)
        if (x == data->threadindex) {
  4014a8:	44 39 c8             	cmp    %r9d,%eax
  4014ab:	74 0f                	je     4014bc <work+0xec>
        if (data->threads[x].wantindex != -1 && data->threads[x].wantindex == target /*&& data[x].failcounter > data->threads[data->threadindex].failcounter*/) {
  4014ad:	8b 0a                	mov    (%rdx),%ecx
  4014af:	83 f9 ff             	cmp    $0xffffffff,%ecx
  4014b2:	74 08                	je     4014bc <work+0xec>
  4014b4:	39 d9                	cmp    %ebx,%ecx
  4014b6:	0f 84 24 01 00 00    	je     4015e0 <work+0x210>
      for (int x = 0; x < data->threadsize ; x++ ) {
  4014bc:	83 c0 01             	add    $0x1,%eax
  4014bf:	48 83 c2 48          	add    $0x48,%rdx
  4014c3:	39 f0                	cmp    %esi,%eax
  4014c5:	75 e1                	jne    4014a8 <work+0xd8>
      if (available == 1 && data->main->works[target].available == 1) {
  4014c7:	48 63 c3             	movslq %ebx,%rax
  4014ca:	83 7c c7 04 01       	cmpl   $0x1,0x4(%rdi,%rax,8)
  4014cf:	4c 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%r14
  4014d7:	0f 85 33 ff ff ff    	jne    401410 <work+0x40>
        if (data->threadindex == 0) {
  4014dd:	45 85 c9             	test   %r9d,%r9d
  4014e0:	0f 85 0c 01 00 00    	jne    4015f2 <work+0x222>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  4014e6:	48 83 ec 08          	sub    $0x8,%rsp
  4014ea:	4c 8d 05 4f 0b 00 00 	lea    0xb4f(%rip),%r8        # 402040 <_IO_stdin_used+0x40>
  4014f1:	53                   	push   %rbx
  4014f2:	b9 64 00 00 00       	mov    $0x64,%ecx
  4014f7:	be 64 00 00 00       	mov    $0x64,%esi
  4014fc:	4c 89 ef             	mov    %r13,%rdi
  4014ff:	31 c0                	xor    %eax,%eax
  401501:	ba 01 00 00 00       	mov    $0x1,%edx
        data->main->workindex = (target + 1);
  401506:	83 c3 01             	add    $0x1,%ebx
  401509:	e8 22 fb ff ff       	call   401030 <__snprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  40150e:	4c 89 ef             	mov    %r13,%rdi
  401511:	e8 3a fb ff ff       	call   401050 <puts@plt>
        data->main->works[target].available = 0;
  401516:	4d 8b 04 24          	mov    (%r12),%r8
  40151a:	59                   	pop    %rcx
  40151b:	5e                   	pop    %rsi
        data->threads[data->threadindex].wantindex = -1;
  40151c:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
        data->main->works[target].available = 0;
  401521:	49 8b 40 30          	mov    0x30(%r8),%rax
  while (data->running == 1) {
  401525:	41 83 7c 24 1c 01    	cmpl   $0x1,0x1c(%r12)
        data->main->works[target].available = 0;
  40152b:	42 c7 44 30 04 00 00 00 00 	movl   $0x0,0x4(%rax,%r14,1)
        data->threads[data->threadindex].wantindex = -1;
  401534:	49 63 44 24 24       	movslq 0x24(%r12),%rax
  401539:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
  40153d:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
  401541:	c7 40 18 ff ff ff ff 	movl   $0xffffffff,0x18(%rax)
        data->main->workindex = (target + 1);
  401548:	41 89 58 14          	mov    %ebx,0x14(%r8)
  while (data->running == 1) {
  40154c:	0f 84 ca fe ff ff    	je     40141c <work+0x4c>
  }
  401552:	31 c0                	xor    %eax,%eax
  401554:	5b                   	pop    %rbx
  401555:	5d                   	pop    %rbp
  401556:	41 5c                	pop    %r12
  401558:	41 5d                	pop    %r13
  40155a:	41 5e                	pop    %r14
  40155c:	c3                   	ret
  40155d:	0f 1f 00             	nopl   (%rax)
    if (data->threadindex == 0 && data->main->workindex >= data->worksize) {
  401560:	41 39 40 14          	cmp    %eax,0x14(%r8)
  401564:	0f 8c de fe ff ff    	jl     401448 <work+0x78>
        data->main->workindex = 0;
  40156a:	41 c7 40 14 00 00 00 00 	movl   $0x0,0x14(%r8)
  401572:	48 89 ef             	mov    %rbp,%rdi
  401575:	e8 d6 fa ff ff       	call   401050 <puts@plt>
        for (int x = 0 ; x < data->worksize; x++) {
  40157a:	41 8b 54 24 20       	mov    0x20(%r12),%edx
  40157f:	85 d2                	test   %edx,%edx
  401581:	0f 8e c1 fe ff ff    	jle    401448 <work+0x78>
          data->main->works[x].available = 1;
  401587:	49 8b 04 24          	mov    (%r12),%rax
  40158b:	83 ea 01             	sub    $0x1,%edx
  40158e:	48 8b 48 30          	mov    0x30(%rax),%rcx
  401592:	48 8d 41 04          	lea    0x4(%rcx),%rax
  401596:	48 8d 54 d1 0c       	lea    0xc(%rcx,%rdx,8),%rdx
  40159b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4015a0:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
        for (int x = 0 ; x < data->worksize; x++) {
  4015a6:	48 83 c0 08          	add    $0x8,%rax
  4015aa:	48 39 c2             	cmp    %rax,%rdx
  4015ad:	75 f1                	jne    4015a0 <work+0x1d0>
  4015af:	e9 94 fe ff ff       	jmp    401448 <work+0x78>
  4015b4:	0f 1f 40 00          	nopl   0x0(%rax)
      data->threads[data->threadindex].wantindex = target;
  4015b8:	49 63 44 24 24       	movslq 0x24(%r12),%rax
  4015bd:	49 8b 54 24 08       	mov    0x8(%r12),%rdx
    int target = (data->main->workindex);
  4015c2:	89 cb                	mov    %ecx,%ebx
      data->threads[data->threadindex].wantindex = target;
  4015c4:	49 89 c1             	mov    %rax,%r9
  4015c7:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
  4015cb:	4c 8d 14 c2          	lea    (%rdx,%rax,8),%r10
  4015cf:	41 89 4a 18          	mov    %ecx,0x18(%r10)
      for (int x = 0; x < data->threadsize ; x++ ) {
  4015d3:	e9 c7 fe ff ff       	jmp    40149f <work+0xcf>
  4015d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          data->threads[data->threadindex].failcounter++;
  4015e0:	41 83 42 40 01       	addl   $0x1,0x40(%r10)
          data->threads[data->threadindex].wantindex = -1;
  4015e5:	41 c7 42 18 ff ff ff ff 	movl   $0xffffffff,0x18(%r10)
      if (available == 1 && data->main->works[target].available == 1) {
  4015ed:	e9 1e fe ff ff       	jmp    401410 <work+0x40>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  4015f2:	48 83 ec 08          	sub    $0x8,%rsp
  4015f6:	4c 8d 05 73 0a 00 00 	lea    0xa73(%rip),%r8        # 402070 <_IO_stdin_used+0x70>
  4015fd:	53                   	push   %rbx
  4015fe:	e9 ef fe ff ff       	jmp    4014f2 <work+0x122>
      data->threads[data->threadindex].wantindex = target;
  401603:	49 63 44 24 24       	movslq 0x24(%r12),%rax
  401608:	49 8b 54 24 08       	mov    0x8(%r12),%rdx
    int target = (data->main->workindex);
  40160d:	89 cb                	mov    %ecx,%ebx
      if (available == 1 && data->main->works[target].available == 1) {
  40160f:	49 8b 78 30          	mov    0x30(%r8),%rdi
      data->threads[data->threadindex].wantindex = target;
  401613:	49 89 c1             	mov    %rax,%r9
  401616:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
  40161a:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
  40161e:	89 48 18             	mov    %ecx,0x18(%rax)
      for (int x = 0; x < data->threadsize ; x++ ) {
  401621:	e9 a1 fe ff ff       	jmp    4014c7 <work+0xf7>

Disassembly of section .fini:

0000000000401628 <_fini>:
  401628:	f3 0f 1e fa          	endbr64
  40162c:	48 83 ec 08          	sub    $0x8,%rsp
  401630:	48 83 c4 08          	add    $0x8,%rsp
  401634:	c3                   	ret
