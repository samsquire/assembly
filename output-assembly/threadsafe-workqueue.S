
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
  4010c2:	ba 06 00 00 00       	mov    $0x6,%edx
  4010c7:	48 8d 35 ce 0f 00 00 	lea    0xfce(%rip),%rsi        # 40209c <_IO_stdin_used+0x9c>
  4010ce:	bf 01 00 00 00       	mov    $0x1,%edi
  4010d3:	41 56                	push   %r14
  4010d5:	4c 8d 3d 8c 0f 00 00 	lea    0xf8c(%rip),%r15        # 402068 <_IO_stdin_used+0x68>
  4010dc:	41 55                	push   %r13
  4010de:	41 54                	push   %r12
    works[i].taskindex = 2;
    works[i].available = 1;
    
  }
  int cpu = 0;
  data[0].works = works;
  4010e0:	41 bc 01 00 00 00    	mov    $0x1,%r12d
int main(int argc, char **argv) {
  4010e6:	55                   	push   %rbp
  4010e7:	53                   	push   %rbx
  4010e8:	48 83 ec 68          	sub    $0x68,%rsp
  4010ec:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4010f5:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  4010fa:	31 c0                	xor    %eax,%eax
  4010fc:	e8 8f ff ff ff       	call   401090 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401101:	be 08 00 00 00       	mov    $0x8,%esi
  401106:	bf 06 00 00 00       	mov    $0x6,%edi
  40110b:	e8 70 ff ff ff       	call   401080 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401110:	be 38 00 00 00       	mov    $0x38,%esi
  401115:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40111a:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  40111f:	e8 5c ff ff ff       	call   401080 <calloc@plt>
  struct Data *data = calloc(threadsize, sizeof(struct Data));
  401124:	be 50 00 00 00       	mov    $0x50,%esi
  401129:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  40112e:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  struct Data *data = calloc(threadsize, sizeof(struct Data));
  401133:	e8 48 ff ff ff       	call   401080 <calloc@plt>
  struct Work *works = calloc(worksize, sizeof(struct Work));
  401138:	be 08 00 00 00       	mov    $0x8,%esi
  40113d:	bf 0a 00 00 00       	mov    $0xa,%edi
  401142:	66 48 0f 6e d0       	movq   %rax,%xmm2
  struct Data *data = calloc(threadsize, sizeof(struct Data));
  401147:	48 89 c3             	mov    %rax,%rbx
  40114a:	66 0f 6c d2          	punpcklqdq %xmm2,%xmm2
  40114e:	49 89 dd             	mov    %rbx,%r13
  data[0].works = works;
  401151:	49 89 de             	mov    %rbx,%r14
  401154:	0f 29 14 24          	movaps %xmm2,(%rsp)
  struct Work *works = calloc(worksize, sizeof(struct Work));
  401158:	e8 23 ff ff ff       	call   401080 <calloc@plt>
    works[i].taskindex = 2;
  40115d:	66 0f 6f 05 7b 0f 00 00 	movdqa 0xf7b(%rip),%xmm0        # 4020e0 <_IO_stdin_used+0xe0>
  data[0].works = works;
  401165:	48 89 43 38          	mov    %rax,0x38(%rbx)
    works[i].taskindex = 2;
  401169:	0f 11 00             	movups %xmm0,(%rax)
  40116c:	0f 11 40 10          	movups %xmm0,0x10(%rax)
  401170:	0f 11 40 20          	movups %xmm0,0x20(%rax)
  401174:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  401178:	0f 11 40 40          	movups %xmm0,0x40(%rax)
  for (int x = 0; x < threadsize ; x++) {
  40117c:	0f 1f 40 00          	nopl   0x0(%rax)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401180:	be 80 00 00 00       	mov    $0x80,%esi
  401185:	bf 01 00 00 00       	mov    $0x1,%edi
  40118a:	41 8d 6c 24 ff       	lea    -0x1(%r12),%ebp
  for (int x = 0; x < threadsize ; x++) {
  40118f:	49 83 c6 50          	add    $0x50,%r14
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401193:	e8 e8 fe ff ff       	call   401080 <calloc@plt>
  401198:	43 8d 0c 24          	lea    (%r12,%r12,1),%ecx
    CPU_SET(cpu += 2, data[x].cpu_set);
  40119c:	ba 01 00 00 00       	mov    $0x1,%edx
  4011a1:	4c 89 fe             	mov    %r15,%rsi
  4011a4:	48 d3 e2             	shl    %cl,%rdx
  4011a7:	48 09 10             	or     %rdx,(%rax)
  4011aa:	bf 01 00 00 00       	mov    $0x1,%edi
  4011af:	89 ea                	mov    %ebp,%edx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4011b1:	49 89 46 f0          	mov    %rax,-0x10(%r14)
  4011b5:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  4011b7:	49 83 c4 01          	add    $0x1,%r12
  4011bb:	e8 d0 fe ff ff       	call   401090 <__printf_chk@plt>
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].running = 1;
    data[x].threadindex = x;
    data[x].worksize = worksize;
    data[x].threadsize = threadsize;
    data[x].main = &data[0];
  4011c0:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
    data[x].threads = data;
    data[x].wantindex = -1;
  4011c5:	48 8b 05 34 0f 00 00 	mov    0xf34(%rip),%rax        # 402100 <_IO_stdin_used+0x100>
    data[x].threadindex = x;
  4011cc:	41 89 6e dc          	mov    %ebp,-0x24(%r14)
    data[x].worksize = worksize;
  4011d0:	41 c7 46 d8 0a 00 00 00 	movl   $0xa,-0x28(%r14)
    data[x].threadsize = threadsize;
  4011d8:	41 c7 46 e0 06 00 00 00 	movl   $0x6,-0x20(%r14)
    data[x].main = &data[0];
  4011e0:	41 0f 11 4e b0       	movups %xmm1,-0x50(%r14)
    data[x].wantindex = -1;
  4011e5:	49 89 46 d0          	mov    %rax,-0x30(%r14)
  for (int x = 0; x < threadsize ; x++) {
  4011e9:	49 83 fc 07          	cmp    $0x7,%r12
  4011ed:	75 91                	jne    401180 <main+0xc0>
  4011ef:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
  4011f4:	49 c7 c6 20 14 40 00 	mov    $0x401420,%r14
  4011fb:	4c 8d bb e0 01 00 00 	lea    0x1e0(%rbx),%r15
  401202:	4c 89 e5             	mov    %r12,%rbp
  401205:	0f 1f 00             	nopl   (%rax)
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  401208:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
  40120d:	4c 89 e9             	mov    %r13,%rcx
  401210:	4c 89 e7             	mov    %r12,%rdi
  401213:	4c 89 f2             	mov    %r14,%rdx
  for (int x = 0; x < threadsize ; x++) {
  401216:	49 83 c5 50          	add    $0x50,%r13
  40121a:	49 83 c4 08          	add    $0x8,%r12
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  40121e:	e8 7d fe ff ff       	call   4010a0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401223:	49 8b 55 f0          	mov    -0x10(%r13),%rdx
  401227:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
  40122c:	be 08 00 00 00       	mov    $0x8,%esi
  401231:	e8 0a fe ff ff       	call   401040 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  401236:	4d 39 fd             	cmp    %r15,%r13
  401239:	75 cd                	jne    401208 <main+0x148>
  }
  struct timespec time = {
  40123b:	66 0f 6f 05 ad 0e 00 00 	movdqa 0xead(%rip),%xmm0        # 4020f0 <_IO_stdin_used+0xf0>
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  401243:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  401248:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
  40124d:	4c 8d 6c 24 28       	lea    0x28(%rsp),%r13
  struct timespec time = {
  401252:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  struct timespec rem = {
  401257:	66 0f ef c0          	pxor   %xmm0,%xmm0
  40125b:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  nanosleep(&time, &rem);
  401260:	e8 0b fe ff ff       	call   401070 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  401265:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
  40126a:	c7 43 24 00 00 00 00 	movl   $0x0,0x24(%rbx)
  401271:	c7 43 74 00 00 00 00 	movl   $0x0,0x74(%rbx)
  401278:	c7 83 c4 00 00 00 00 00 00 00 	movl   $0x0,0xc4(%rbx)
  401282:	49 83 c4 30          	add    $0x30,%r12
  401286:	c7 83 14 01 00 00 00 00 00 00 	movl   $0x0,0x114(%rbx)
  401290:	c7 83 64 01 00 00 00 00 00 00 	movl   $0x0,0x164(%rbx)
  40129a:	c7 83 b4 01 00 00 00 00 00 00 	movl   $0x0,0x1b4(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  4012a4:	0f 1f 40 00          	nopl   0x0(%rax)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  4012a8:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
  4012ac:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  4012af:	48 83 c5 08          	add    $0x8,%rbp
    pthread_join(thread[x], &res);
  4012b3:	e8 f8 fd ff ff       	call   4010b0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  4012b8:	4c 39 e5             	cmp    %r12,%rbp
  4012bb:	75 eb                	jne    4012a8 <main+0x1e8>
  4012bd:	48 8d 3d ed 0d 00 00 	lea    0xded(%rip),%rdi        # 4020b1 <_IO_stdin_used+0xb1>
  4012c4:	e8 87 fd ff ff       	call   401050 <puts@plt>
  }
  printf("finished simulation.\n");
  long freq = 0;
  for (int x= 0; x < threadsize; x++) {
    freq += data[x].freq;
  4012c9:	48 8b 53 60          	mov    0x60(%rbx),%rdx
  4012cd:	31 c0                	xor    %eax,%eax
  4012cf:	bf 01 00 00 00       	mov    $0x1,%edi
  4012d4:	48 03 93 b0 00 00 00 	add    0xb0(%rbx),%rdx
  4012db:	48 8d 35 e4 0d 00 00 	lea    0xde4(%rip),%rsi        # 4020c6 <_IO_stdin_used+0xc6>
  4012e2:	48 03 53 10          	add    0x10(%rbx),%rdx
  4012e6:	48 03 93 00 01 00 00 	add    0x100(%rbx),%rdx
  4012ed:	48 03 93 50 01 00 00 	add    0x150(%rbx),%rdx
  4012f4:	48 03 93 a0 01 00 00 	add    0x1a0(%rbx),%rdx
  4012fb:	e8 90 fd ff ff       	call   401090 <__printf_chk@plt>
  }
  printf("freq: %ld\n", freq);
  401300:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  401305:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40130e:	75 11                	jne    401321 <main+0x261>
  401310:	48 83 c4 68          	add    $0x68,%rsp
  401314:	31 c0                	xor    %eax,%eax
  401316:	5b                   	pop    %rbx
  401317:	5d                   	pop    %rbp
  401318:	41 5c                	pop    %r12
  40131a:	41 5d                	pop    %r13
  40131c:	41 5e                	pop    %r14
  40131e:	41 5f                	pop    %r15
  401320:	c3                   	ret
  401321:	e8 3a fd ff ff       	call   401060 <__stack_chk_fail@plt>
  401326:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401330 <_start>:
  401330:	f3 0f 1e fa          	endbr64
  401334:	31 ed                	xor    %ebp,%ebp
  401336:	49 89 d1             	mov    %rdx,%r9
  401339:	5e                   	pop    %rsi
  40133a:	48 89 e2             	mov    %rsp,%rdx
  40133d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401341:	50                   	push   %rax
  401342:	54                   	push   %rsp
  401343:	45 31 c0             	xor    %r8d,%r8d
  401346:	31 c9                	xor    %ecx,%ecx
  401348:	48 c7 c7 c0 10 40 00 	mov    $0x4010c0,%rdi
  40134f:	ff 15 9b 2c 00 00    	call   *0x2c9b(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  401355:	f4                   	hlt
  401356:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401360 <_dl_relocate_static_pie>:
  401360:	f3 0f 1e fa          	endbr64
  401364:	c3                   	ret
  401365:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40136f:	90                   	nop

0000000000401370 <deregister_tm_clones>:
  401370:	b8 10 40 40 00       	mov    $0x404010,%eax
  401375:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  40137b:	74 13                	je     401390 <deregister_tm_clones+0x20>
  40137d:	b8 00 00 00 00       	mov    $0x0,%eax
  401382:	48 85 c0             	test   %rax,%rax
  401385:	74 09                	je     401390 <deregister_tm_clones+0x20>
  401387:	bf 10 40 40 00       	mov    $0x404010,%edi
  40138c:	ff e0                	jmp    *%rax
  40138e:	66 90                	xchg   %ax,%ax
  401390:	c3                   	ret
  401391:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40139c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004013a0 <register_tm_clones>:
  4013a0:	be 10 40 40 00       	mov    $0x404010,%esi
  4013a5:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  4013ac:	48 89 f0             	mov    %rsi,%rax
  4013af:	48 c1 ee 3f          	shr    $0x3f,%rsi
  4013b3:	48 c1 f8 03          	sar    $0x3,%rax
  4013b7:	48 01 c6             	add    %rax,%rsi
  4013ba:	48 d1 fe             	sar    %rsi
  4013bd:	74 11                	je     4013d0 <register_tm_clones+0x30>
  4013bf:	b8 00 00 00 00       	mov    $0x0,%eax
  4013c4:	48 85 c0             	test   %rax,%rax
  4013c7:	74 07                	je     4013d0 <register_tm_clones+0x30>
  4013c9:	bf 10 40 40 00       	mov    $0x404010,%edi
  4013ce:	ff e0                	jmp    *%rax
  4013d0:	c3                   	ret
  4013d1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4013dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004013e0 <__do_global_dtors_aux>:
  4013e0:	f3 0f 1e fa          	endbr64
  4013e4:	80 3d 25 2c 00 00 00 	cmpb   $0x0,0x2c25(%rip)        # 404010 <__TMC_END__>
  4013eb:	75 13                	jne    401400 <__do_global_dtors_aux+0x20>
  4013ed:	55                   	push   %rbp
  4013ee:	48 89 e5             	mov    %rsp,%rbp
  4013f1:	e8 7a ff ff ff       	call   401370 <deregister_tm_clones>
  4013f6:	c6 05 13 2c 00 00 01 	movb   $0x1,0x2c13(%rip)        # 404010 <__TMC_END__>
  4013fd:	5d                   	pop    %rbp
  4013fe:	c3                   	ret
  4013ff:	90                   	nop
  401400:	c3                   	ret
  401401:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40140c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401410 <frame_dummy>:
  401410:	f3 0f 1e fa          	endbr64
  401414:	eb 8a                	jmp    4013a0 <register_tm_clones>
  401416:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401420 <work>:
void * work(void * arg) {
  401420:	41 57                	push   %r15
  char * output = calloc(100, sizeof(char));
  401422:	be 01 00 00 00       	mov    $0x1,%esi
void * work(void * arg) {
  401427:	41 56                	push   %r14
  401429:	41 55                	push   %r13
  40142b:	41 54                	push   %r12
  40142d:	55                   	push   %rbp
  40142e:	53                   	push   %rbx
  40142f:	48 89 fb             	mov    %rdi,%rbx
  char * output = calloc(100, sizeof(char));
  401432:	bf 64 00 00 00       	mov    $0x64,%edi
void * work(void * arg) {
  401437:	48 83 ec 08          	sub    $0x8,%rsp
  char * output = calloc(100, sizeof(char));
  40143b:	e8 40 fc ff ff       	call   401080 <calloc@plt>
  while (data->running == 1) {
  401440:	83 7b 24 01          	cmpl   $0x1,0x24(%rbx)
  401444:	0f 85 bb 01 00 00    	jne    401605 <work+0x1e5>
  40144a:	49 89 c6             	mov    %rax,%r14
  40144d:	45 31 ff             	xor    %r15d,%r15d
  401450:	4c 8d 2d 30 0c 00 00 	lea    0xc30(%rip),%r13        # 402087 <_IO_stdin_used+0x87>
  401457:	eb 11                	jmp    40146a <work+0x4a>
  401459:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401460:	83 7b 24 01          	cmpl   $0x1,0x24(%rbx)
  401464:	0f 85 9b 01 00 00    	jne    401605 <work+0x1e5>
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  40146a:	b9 0c 00 00 00       	mov    $0xc,%ecx
  40146f:	4c 89 f7             	mov    %r14,%rdi
  401472:	4c 89 f8             	mov    %r15,%rax
  401475:	f3 48 ab             	rep stos %rax,%es:(%rdi)
   if (data->threadindex != 0 && data->main->workindex >= data->worksize) { continue; }
  401478:	8b 4b 2c             	mov    0x2c(%rbx),%ecx
  40147b:	c7 07 00 00 00 00    	movl   $0x0,(%rdi)
  401481:	85 c9                	test   %ecx,%ecx
  401483:	74 0b                	je     401490 <work+0x70>
  401485:	48 8b 03             	mov    (%rbx),%rax
  401488:	8b 73 28             	mov    0x28(%rbx),%esi
  40148b:	39 70 1c             	cmp    %esi,0x1c(%rax)
  40148e:	7d d0                	jge    401460 <work+0x40>
    int target = (data->main->workindex);
  401490:	48 8b 3b             	mov    (%rbx),%rdi
   for (int x = target ; x < data->worksize ; x++ ) {
  401493:	8b 53 28             	mov    0x28(%rbx),%edx
    int target = (data->main->workindex);
  401496:	8b 6f 1c             	mov    0x1c(%rdi),%ebp
   for (int x = target ; x < data->worksize ; x++ ) {
  401499:	39 d5                	cmp    %edx,%ebp
  40149b:	0f 8d 7f 01 00 00    	jge    401620 <work+0x200>
  4014a1:	4c 63 d5             	movslq %ebp,%r10
    if (data->main->works[x].available == 1 ) {
  4014a4:	48 8b 4f 38          	mov    0x38(%rdi),%rcx
  4014a8:	89 e8                	mov    %ebp,%eax
  4014aa:	4e 8d 24 d5 00 00 00 00 	lea    0x0(,%r10,8),%r12
  4014b2:	eb 13                	jmp    4014c7 <work+0xa7>
  4014b4:	0f 1f 40 00          	nopl   0x0(%rax)
   for (int x = target ; x < data->worksize ; x++ ) {
  4014b8:	83 c0 01             	add    $0x1,%eax
  4014bb:	49 83 c4 08          	add    $0x8,%r12
  4014bf:	39 d0                	cmp    %edx,%eax
  4014c1:	0f 84 59 01 00 00    	je     401620 <work+0x200>
    if (data->main->works[x].available == 1 ) {
  4014c7:	42 83 7c 21 04 01    	cmpl   $0x1,0x4(%rcx,%r12,1)
  4014cd:	75 e9                	jne    4014b8 <work+0x98>
      data->threads[data->threadindex].wantindex = target;
  4014cf:	48 63 4b 2c          	movslq 0x2c(%rbx),%rcx
  4014d3:	48 8b 53 08          	mov    0x8(%rbx),%rdx
      for (int x = 0; x < data->threadsize ; x++ ) {
  4014d7:	89 c5                	mov    %eax,%ebp
      data->threads[data->threadindex].wantindex = target;
  4014d9:	48 8d 34 89          	lea    (%rcx,%rcx,4),%rsi
  4014dd:	49 89 c9             	mov    %rcx,%r9
      for (int x = 0; x < data->threadsize ; x++ ) {
  4014e0:	8b 4b 30             	mov    0x30(%rbx),%ecx
      data->threads[data->threadindex].wantindex = target;
  4014e3:	48 c1 e6 04          	shl    $0x4,%rsi
  4014e7:	48 01 d6             	add    %rdx,%rsi
  4014ea:	89 46 20             	mov    %eax,0x20(%rsi)
      for (int x = 0; x < data->threadsize ; x++ ) {
  4014ed:	85 c9                	test   %ecx,%ecx
  4014ef:	7e 4b                	jle    40153c <work+0x11c>
  4014f1:	48 83 c2 20          	add    $0x20,%rdx
  4014f5:	31 c0                	xor    %eax,%eax
  4014f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        if (x == data->threadindex) {
  401500:	44 39 c8             	cmp    %r9d,%eax
  401503:	74 12                	je     401517 <work+0xf7>
        if (data->threads[x].wantindex != -1 && data->threads[x].wantindex == target /*&& data[x].failcounter > data->threads[data->threadindex].failcounter*/) {
  401505:	44 8b 02             	mov    (%rdx),%r8d
  401508:	41 83 f8 ff          	cmp    $0xffffffff,%r8d
  40150c:	74 09                	je     401517 <work+0xf7>
  40150e:	41 39 e8             	cmp    %ebp,%r8d
  401511:	0f 84 39 01 00 00    	je     401650 <work+0x230>
      for (int x = 0; x < data->threadsize ; x++ ) {
  401517:	83 c0 01             	add    $0x1,%eax
  40151a:	48 83 c2 50          	add    $0x50,%rdx
  40151e:	39 c8                	cmp    %ecx,%eax
  401520:	7c de                	jl     401500 <work+0xe0>
      if (available == 1 && data->main->works[target].available == 1) {
  401522:	48 8b 57 38          	mov    0x38(%rdi),%rdx
  401526:	48 63 c5             	movslq %ebp,%rax
  401529:	4c 8d 24 c5 00 00 00 00 	lea    0x0(,%rax,8),%r12
  401531:	83 7c c2 04 01       	cmpl   $0x1,0x4(%rdx,%rax,8)
  401536:	0f 85 24 ff ff ff    	jne    401460 <work+0x40>
        data->freq++;
  40153c:	48 83 43 10 01       	addq   $0x1,0x10(%rbx)
        if (data->threadindex == 0) {
  401541:	45 85 c9             	test   %r9d,%r9d
  401544:	0f 85 16 01 00 00    	jne    401660 <work+0x240>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  40154a:	48 83 ec 08          	sub    $0x8,%rsp
  40154e:	4c 8d 05 b3 0a 00 00 	lea    0xab3(%rip),%r8        # 402008 <_IO_stdin_used+0x8>
  401555:	55                   	push   %rbp
  401556:	ba 01 00 00 00       	mov    $0x1,%edx
  40155b:	b9 64 00 00 00       	mov    $0x64,%ecx
  401560:	4c 89 f7             	mov    %r14,%rdi
  401563:	31 c0                	xor    %eax,%eax
  401565:	be 64 00 00 00       	mov    $0x64,%esi
        data->main->workindex = (target + 1);
  40156a:	83 c5 01             	add    $0x1,%ebp
  40156d:	e8 be fa ff ff       	call   401030 <__snprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  401572:	4c 89 f7             	mov    %r14,%rdi
  401575:	e8 d6 fa ff ff       	call   401050 <puts@plt>
  40157a:	58                   	pop    %rax
  40157b:	5a                   	pop    %rdx
        data->main->works[target].available = 0;
  40157c:	48 8b 13             	mov    (%rbx),%rdx
  40157f:	48 8b 42 38          	mov    0x38(%rdx),%rax
  401583:	42 c7 44 20 04 00 00 00 00 	movl   $0x0,0x4(%rax,%r12,1)
        data->threads[data->threadindex].wantindex = -1;
  40158c:	48 63 43 2c          	movslq 0x2c(%rbx),%rax
  401590:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  401594:	48 c1 e0 04          	shl    $0x4,%rax
  401598:	48 03 43 08          	add    0x8(%rbx),%rax
  40159c:	c7 40 20 ff ff ff ff 	movl   $0xffffffff,0x20(%rax)
        data->main->workindex = (target + 1);
  4015a3:	89 6a 1c             	mov    %ebp,0x1c(%rdx)
        if (data->main->workindex >= data->worksize){
  4015a6:	3b 6b 28             	cmp    0x28(%rbx),%ebp
  4015a9:	0f 8c b1 fe ff ff    	jl     401460 <work+0x40>
        data->main->workindex = 0;
  4015af:	c7 42 1c 00 00 00 00 	movl   $0x0,0x1c(%rdx)
  4015b6:	4c 89 ef             	mov    %r13,%rdi
  4015b9:	e8 92 fa ff ff       	call   401050 <puts@plt>
        for (int x = 0 ; x < data->worksize; x++) {
  4015be:	8b 4b 28             	mov    0x28(%rbx),%ecx
  4015c1:	85 c9                	test   %ecx,%ecx
  4015c3:	7e 2a                	jle    4015ef <work+0x1cf>
          data->main->works[x].available = 1;
  4015c5:	48 8b 03             	mov    (%rbx),%rax
  4015c8:	83 e9 01             	sub    $0x1,%ecx
  4015cb:	48 8b 50 38          	mov    0x38(%rax),%rdx
  4015cf:	48 8d 42 04          	lea    0x4(%rdx),%rax
  4015d3:	48 8d 54 ca 0c       	lea    0xc(%rdx,%rcx,8),%rdx
  4015d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  4015e0:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
        for (int x = 0 ; x < data->worksize; x++) {
  4015e6:	48 83 c0 08          	add    $0x8,%rax
  4015ea:	48 39 c2             	cmp    %rax,%rdx
  4015ed:	75 f1                	jne    4015e0 <work+0x1c0>
  4015ef:	48 8d 3d a0 0a 00 00 	lea    0xaa0(%rip),%rdi        # 402096 <_IO_stdin_used+0x96>
  4015f6:	e8 55 fa ff ff       	call   401050 <puts@plt>
  while (data->running == 1) {
  4015fb:	83 7b 24 01          	cmpl   $0x1,0x24(%rbx)
  4015ff:	0f 84 65 fe ff ff    	je     40146a <work+0x4a>
  }
  401605:	48 83 c4 08          	add    $0x8,%rsp
  401609:	31 c0                	xor    %eax,%eax
  40160b:	5b                   	pop    %rbx
  40160c:	5d                   	pop    %rbp
  40160d:	41 5c                	pop    %r12
  40160f:	41 5d                	pop    %r13
  401611:	41 5e                	pop    %r14
  401613:	41 5f                	pop    %r15
  401615:	c3                   	ret
  401616:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      data->threads[data->threadindex].wantindex = target;
  401620:	48 63 43 2c          	movslq 0x2c(%rbx),%rax
  401624:	48 8b 53 08          	mov    0x8(%rbx),%rdx
      for (int x = 0; x < data->threadsize ; x++ ) {
  401628:	8b 4b 30             	mov    0x30(%rbx),%ecx
      data->threads[data->threadindex].wantindex = target;
  40162b:	48 8d 34 80          	lea    (%rax,%rax,4),%rsi
  40162f:	49 89 c1             	mov    %rax,%r9
  401632:	48 c1 e6 04          	shl    $0x4,%rsi
  401636:	48 01 d6             	add    %rdx,%rsi
  401639:	89 6e 20             	mov    %ebp,0x20(%rsi)
      for (int x = 0; x < data->threadsize ; x++ ) {
  40163c:	85 c9                	test   %ecx,%ecx
  40163e:	0f 8f ad fe ff ff    	jg     4014f1 <work+0xd1>
  401644:	e9 d9 fe ff ff       	jmp    401522 <work+0x102>
  401649:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          data->threads[data->threadindex].failcounter++;
  401650:	83 46 48 01          	addl   $0x1,0x48(%rsi)
          data->threads[data->threadindex].wantindex = -1;
  401654:	c7 46 20 ff ff ff ff 	movl   $0xffffffff,0x20(%rsi)
      if (available == 1 && data->main->works[target].available == 1) {
  40165b:	e9 00 fe ff ff       	jmp    401460 <work+0x40>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401660:	48 83 ec 08          	sub    $0x8,%rsp
  401664:	4c 8d 05 cd 09 00 00 	lea    0x9cd(%rip),%r8        # 402038 <_IO_stdin_used+0x38>
  40166b:	55                   	push   %rbp
  40166c:	e9 e5 fe ff ff       	jmp    401556 <work+0x136>

Disassembly of section .fini:

0000000000401674 <_fini>:
  401674:	f3 0f 1e fa          	endbr64
  401678:	48 83 ec 08          	sub    $0x8,%rsp
  40167c:	48 83 c4 08          	add    $0x8,%rsp
  401680:	c3                   	ret
