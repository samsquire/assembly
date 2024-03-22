
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
  4010c2:	ba 07 00 00 00       	mov    $0x7,%edx
  4010c7:	bf 01 00 00 00       	mov    $0x1,%edi
  4010cc:	48 8d 35 c3 0f 00 00 	lea    0xfc3(%rip),%rsi        # 402096 <_IO_stdin_used+0x96>
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
  
  int primes[] = {3, 7, 13, 19, 23, 29, 31, 37};
  int threadsize = 7;
  int buckets = worksize / threadsize;
  printf("Starting %d workers\n", threadsize);
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  4010f4:	be 08 00 00 00       	mov    $0x8,%esi
  4010f9:	bf 07 00 00 00       	mov    $0x7,%edi
  4010fe:	e8 7d ff ff ff       	call   401080 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401103:	be 38 00 00 00       	mov    $0x38,%esi
  401108:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40110d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401112:	e8 69 ff ff ff       	call   401080 <calloc@plt>
  struct Data *data = calloc(threadsize, sizeof(struct Data));
  401117:	be 80 01 00 00       	mov    $0x180,%esi
  40111c:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401121:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  struct Data *data = calloc(threadsize, sizeof(struct Data));
  401126:	e8 55 ff ff ff       	call   401080 <calloc@plt>
  struct Work *works = calloc(worksize, sizeof(struct Work));
  40112b:	be 00 01 00 00       	mov    $0x100,%esi
  401130:	bf 80 96 98 00       	mov    $0x989680,%edi
  401135:	66 48 0f 6e d0       	movq   %rax,%xmm2
  struct Data *data = calloc(threadsize, sizeof(struct Data));
  40113a:	48 89 c3             	mov    %rax,%rbx
  40113d:	66 0f 6c d2          	punpcklqdq %xmm2,%xmm2
  401141:	0f 29 14 24          	movaps %xmm2,(%rsp)
  struct Work *works = calloc(worksize, sizeof(struct Work));
  401145:	e8 36 ff ff ff       	call   401080 <calloc@plt>
  
  for (int i = 0; i < worksize; i++) {
  40114a:	b9 00 80 96 98       	mov    $0x98968000,%ecx
  40114f:	48 89 c2             	mov    %rax,%rdx
  401152:	48 01 c1             	add    %rax,%rcx
  401155:	0f 1f 00             	nopl   (%rax)
    works[i].taskindex = 2;
  401158:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
  for (int i = 0; i < worksize; i++) {
  40115e:	48 81 c2 00 01 00 00 	add    $0x100,%rdx
    works[i].available = 1;
  401165:	c7 42 80 01 00 00 00 	movl   $0x1,-0x80(%rdx)
  for (int i = 0; i < worksize; i++) {
  40116c:	48 39 d1             	cmp    %rdx,%rcx
  40116f:	75 e7                	jne    401158 <main+0x98>
    
  }
  int cpu = 0;
  data[0].works = works;
  401171:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  401178:	49 89 dc             	mov    %rbx,%r12
  data[0].works = works;
  40117b:	49 89 dd             	mov    %rbx,%r13
  int cpu = 0;
  40117e:	31 ed                	xor    %ebp,%ebp
  401180:	4c 8d 3d e1 0e 00 00 	lea    0xee1(%rip),%r15        # 402068 <_IO_stdin_used+0x68>
  401187:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401190:	41 89 ee             	mov    %ebp,%r14d
  401193:	be 80 00 00 00       	mov    $0x80,%esi
  401198:	bf 01 00 00 00       	mov    $0x1,%edi
    CPU_SET(cpu += 1, data[x].cpu_set);
  40119d:	83 c5 01             	add    $0x1,%ebp
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4011a0:	e8 db fe ff ff       	call   401080 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  4011a5:	89 e9                	mov    %ebp,%ecx
  4011a7:	ba 01 00 00 00       	mov    $0x1,%edx
  4011ac:	4c 89 fe             	mov    %r15,%rsi
  4011af:	48 d3 e2             	shl    %cl,%rdx
  4011b2:	48 09 10             	or     %rdx,(%rax)
  4011b5:	89 e9                	mov    %ebp,%ecx
  4011b7:	44 89 f2             	mov    %r14d,%edx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4011ba:	49 89 85 20 01 00 00 	mov    %rax,0x120(%r13)
  4011c1:	bf 01 00 00 00       	mov    $0x1,%edi
  4011c6:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  4011c8:	49 81 c5 80 01 00 00 	add    $0x180,%r13
  4011cf:	e8 bc fe ff ff       	call   401090 <__printf_chk@plt>
    data[x].running = 1;
    data[x].threadindex = x;
    data[x].worksize = worksize;
    data[x].threadsize = threadsize;
    data[x].buckets = buckets;
    data[x].main = &data[0];
  4011d4:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
    data[x].threads = data;
    data[x].wantindex = -1;
  4011d9:	48 8b 05 f0 0e 00 00 	mov    0xef0(%rip),%rax        # 4020d0 <_IO_stdin_used+0xd0>
    data[x].loglevel = debug;
  4011e0:	41 c7 45 ac 00 00 00 00 	movl   $0x0,-0x54(%r13)
    data[x].threadindex = x;
  4011e8:	45 89 75 8c          	mov    %r14d,-0x74(%r13)
    data[x].worksize = worksize;
  4011ec:	41 c7 45 88 80 96 98 00 	movl   $0x989680,-0x78(%r13)
    data[x].threadsize = threadsize;
  4011f4:	41 c7 45 90 07 00 00 00 	movl   $0x7,-0x70(%r13)
    data[x].buckets = buckets;
  4011fc:	41 c7 45 b8 5b cc 15 00 	movl   $0x15cc5b,-0x48(%r13)
    data[x].main = &data[0];
  401204:	41 0f 29 8d 80 fe ff ff 	movaps %xmm1,-0x180(%r13)
    data[x].wantindex = -1;
  40120c:	49 89 45 80          	mov    %rax,-0x80(%r13)
  for (int x = 0; x < threadsize ; x++) {
  401210:	83 fd 07             	cmp    $0x7,%ebp
  401213:	0f 85 77 ff ff ff    	jne    401190 <main+0xd0>
  401219:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
  40121e:	49 c7 c6 60 14 40 00 	mov    $0x401460,%r14
  401225:	4c 8d bb 80 0a 00 00 	lea    0xa80(%rbx),%r15
  40122c:	49 89 ed             	mov    %rbp,%r13
  40122f:	90                   	nop
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  401230:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
  401235:	4c 89 e1             	mov    %r12,%rcx
  401238:	48 89 ef             	mov    %rbp,%rdi
  40123b:	4c 89 f2             	mov    %r14,%rdx
  for (int x = 0; x < threadsize ; x++) {
  40123e:	49 81 c4 80 01 00 00 	add    $0x180,%r12
  401245:	48 83 c5 08          	add    $0x8,%rbp
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  401249:	e8 52 fe ff ff       	call   4010a0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  40124e:	49 8b 54 24 a0       	mov    -0x60(%r12),%rdx
  401253:	48 8b 7d f8          	mov    -0x8(%rbp),%rdi
  401257:	be 08 00 00 00       	mov    $0x8,%esi
  40125c:	e8 df fd ff ff       	call   401040 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  401261:	4d 39 fc             	cmp    %r15,%r12
  401264:	75 ca                	jne    401230 <main+0x170>
  }
  struct timespec time = {
  401266:	66 0f 6f 05 72 0e 00 00 	movdqa 0xe72(%rip),%xmm0        # 4020e0 <_IO_stdin_used+0xe0>
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  40126e:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  401273:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
  401278:	4c 8d 64 24 28       	lea    0x28(%rsp),%r12
  struct timespec time = {
  40127d:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  struct timespec rem = {
  401282:	66 0f ef c0          	pxor   %xmm0,%xmm0
  401286:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  nanosleep(&time, &rem);
  40128b:	e8 e0 fd ff ff       	call   401070 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  401290:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
  401295:	c7 83 04 01 00 00 00 00 00 00 	movl   $0x0,0x104(%rbx)
  40129f:	c7 83 84 02 00 00 00 00 00 00 	movl   $0x0,0x284(%rbx)
  4012a9:	c7 83 04 04 00 00 00 00 00 00 	movl   $0x0,0x404(%rbx)
  4012b3:	48 83 c5 38          	add    $0x38,%rbp
  4012b7:	c7 83 84 05 00 00 00 00 00 00 	movl   $0x0,0x584(%rbx)
  4012c1:	c7 83 04 07 00 00 00 00 00 00 	movl   $0x0,0x704(%rbx)
  4012cb:	c7 83 84 08 00 00 00 00 00 00 	movl   $0x0,0x884(%rbx)
  4012d5:	c7 83 04 0a 00 00 00 00 00 00 	movl   $0x0,0xa04(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  4012df:	90                   	nop
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  4012e0:	49 8b 7d 00          	mov    0x0(%r13),%rdi
  4012e4:	4c 89 e6             	mov    %r12,%rsi
  for (int x = 0; x < threadsize; x++) {
  4012e7:	49 83 c5 08          	add    $0x8,%r13
    pthread_join(thread[x], &res);
  4012eb:	e8 c0 fd ff ff       	call   4010b0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  4012f0:	4c 39 ed             	cmp    %r13,%rbp
  4012f3:	75 eb                	jne    4012e0 <main+0x220>
  4012f5:	48 8d 3d af 0d 00 00 	lea    0xdaf(%rip),%rdi        # 4020ab <_IO_stdin_used+0xab>
  4012fc:	e8 4f fd ff ff       	call   401050 <puts@plt>
  }
  printf("finished simulation.\n");
  long freq = 0;
  for (int x= 0; x < threadsize; x++) {
    freq += data[x].freq;
  401301:	48 8b 93 90 01 00 00 	mov    0x190(%rbx),%rdx
  401308:	31 c0                	xor    %eax,%eax
  40130a:	48 03 93 10 03 00 00 	add    0x310(%rbx),%rdx
  401311:	48 8d 35 a8 0d 00 00 	lea    0xda8(%rip),%rsi        # 4020c0 <_IO_stdin_used+0xc0>
  401318:	48 03 53 10          	add    0x10(%rbx),%rdx
  40131c:	bf 01 00 00 00       	mov    $0x1,%edi
  401321:	48 03 93 90 04 00 00 	add    0x490(%rbx),%rdx
  401328:	48 03 93 10 06 00 00 	add    0x610(%rbx),%rdx
  40132f:	48 03 93 90 07 00 00 	add    0x790(%rbx),%rdx
  401336:	48 03 93 10 09 00 00 	add    0x910(%rbx),%rdx
  40133d:	e8 4e fd ff ff       	call   401090 <__printf_chk@plt>
  }
  printf("freq: %ld\n", freq);
  401342:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  401347:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401350:	75 11                	jne    401363 <main+0x2a3>
  401352:	48 83 c4 68          	add    $0x68,%rsp
  401356:	31 c0                	xor    %eax,%eax
  401358:	5b                   	pop    %rbx
  401359:	5d                   	pop    %rbp
  40135a:	41 5c                	pop    %r12
  40135c:	41 5d                	pop    %r13
  40135e:	41 5e                	pop    %r14
  401360:	41 5f                	pop    %r15
  401362:	c3                   	ret
  401363:	e8 f8 fc ff ff       	call   401060 <__stack_chk_fail@plt>
  401368:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000401370 <_start>:
  401370:	f3 0f 1e fa          	endbr64
  401374:	31 ed                	xor    %ebp,%ebp
  401376:	49 89 d1             	mov    %rdx,%r9
  401379:	5e                   	pop    %rsi
  40137a:	48 89 e2             	mov    %rsp,%rdx
  40137d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401381:	50                   	push   %rax
  401382:	54                   	push   %rsp
  401383:	45 31 c0             	xor    %r8d,%r8d
  401386:	31 c9                	xor    %ecx,%ecx
  401388:	48 c7 c7 c0 10 40 00 	mov    $0x4010c0,%rdi
  40138f:	ff 15 5b 2c 00 00    	call   *0x2c5b(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  401395:	f4                   	hlt
  401396:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004013a0 <_dl_relocate_static_pie>:
  4013a0:	f3 0f 1e fa          	endbr64
  4013a4:	c3                   	ret
  4013a5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4013af:	90                   	nop

00000000004013b0 <deregister_tm_clones>:
  4013b0:	b8 10 40 40 00       	mov    $0x404010,%eax
  4013b5:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  4013bb:	74 13                	je     4013d0 <deregister_tm_clones+0x20>
  4013bd:	b8 00 00 00 00       	mov    $0x0,%eax
  4013c2:	48 85 c0             	test   %rax,%rax
  4013c5:	74 09                	je     4013d0 <deregister_tm_clones+0x20>
  4013c7:	bf 10 40 40 00       	mov    $0x404010,%edi
  4013cc:	ff e0                	jmp    *%rax
  4013ce:	66 90                	xchg   %ax,%ax
  4013d0:	c3                   	ret
  4013d1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4013dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004013e0 <register_tm_clones>:
  4013e0:	be 10 40 40 00       	mov    $0x404010,%esi
  4013e5:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  4013ec:	48 89 f0             	mov    %rsi,%rax
  4013ef:	48 c1 ee 3f          	shr    $0x3f,%rsi
  4013f3:	48 c1 f8 03          	sar    $0x3,%rax
  4013f7:	48 01 c6             	add    %rax,%rsi
  4013fa:	48 d1 fe             	sar    %rsi
  4013fd:	74 11                	je     401410 <register_tm_clones+0x30>
  4013ff:	b8 00 00 00 00       	mov    $0x0,%eax
  401404:	48 85 c0             	test   %rax,%rax
  401407:	74 07                	je     401410 <register_tm_clones+0x30>
  401409:	bf 10 40 40 00       	mov    $0x404010,%edi
  40140e:	ff e0                	jmp    *%rax
  401410:	c3                   	ret
  401411:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40141c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401420 <__do_global_dtors_aux>:
  401420:	f3 0f 1e fa          	endbr64
  401424:	80 3d e5 2b 00 00 00 	cmpb   $0x0,0x2be5(%rip)        # 404010 <__TMC_END__>
  40142b:	75 13                	jne    401440 <__do_global_dtors_aux+0x20>
  40142d:	55                   	push   %rbp
  40142e:	48 89 e5             	mov    %rsp,%rbp
  401431:	e8 7a ff ff ff       	call   4013b0 <deregister_tm_clones>
  401436:	c6 05 d3 2b 00 00 01 	movb   $0x1,0x2bd3(%rip)        # 404010 <__TMC_END__>
  40143d:	5d                   	pop    %rbp
  40143e:	c3                   	ret
  40143f:	90                   	nop
  401440:	c3                   	ret
  401441:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40144c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401450 <frame_dummy>:
  401450:	f3 0f 1e fa          	endbr64
  401454:	eb 8a                	jmp    4013e0 <register_tm_clones>
  401456:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401460 <work>:
void * work(void * arg) {
  401460:	41 57                	push   %r15
  char * output = calloc(100, sizeof(char));
  401462:	be 01 00 00 00       	mov    $0x1,%esi
void * work(void * arg) {
  401467:	41 56                	push   %r14
  401469:	41 55                	push   %r13
  40146b:	49 89 fd             	mov    %rdi,%r13
  char * output = calloc(100, sizeof(char));
  40146e:	bf 64 00 00 00       	mov    $0x64,%edi
void * work(void * arg) {
  401473:	41 54                	push   %r12
  401475:	55                   	push   %rbp
  401476:	53                   	push   %rbx
  401477:	48 83 ec 08          	sub    $0x8,%rsp
  char * output = calloc(100, sizeof(char));
  40147b:	e8 00 fc ff ff       	call   401080 <calloc@plt>
  while (data->running == 1) {
  401480:	41 83 bd 04 01 00 00 01 	cmpl   $0x1,0x104(%r13)
  401488:	0f 85 d6 00 00 00    	jne    401564 <work+0x104>
  40148e:	49 89 c6             	mov    %rax,%r14
  401491:	4c 8d 25 ef 0b 00 00 	lea    0xbef(%rip),%r12        # 402087 <_IO_stdin_used+0x87>
  401498:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  4014a0:	31 c0                	xor    %eax,%eax
  4014a2:	4c 89 f7             	mov    %r14,%rdi
  4014a5:	b9 0c 00 00 00       	mov    $0xc,%ecx
  4014aa:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  4014ad:	c7 07 00 00 00 00    	movl   $0x0,(%rdi)
      int target = (data->threadindex * data->buckets);
  4014b3:	45 8b 8d 0c 01 00 00 	mov    0x10c(%r13),%r9d
   for (int x = data->workindex ; x < bucketlim ; x+= stride ) {
  4014ba:	41 8b 85 80 00 00 00 	mov    0x80(%r13),%eax
    int bucketlim = (data->threadindex + 1) * data->buckets;
  4014c1:	41 8d 69 01          	lea    0x1(%r9),%ebp
  4014c5:	41 0f af ad 38 01 00 00 	imul   0x138(%r13),%ebp
   for (int x = data->workindex ; x < bucketlim ; x+= stride ) {
  4014cd:	39 c5                	cmp    %eax,%ebp
  4014cf:	0f 8e a3 00 00 00    	jle    401578 <work+0x118>
    if (data->main->works[x].available == 1 ) {
  4014d5:	49 8b 55 00          	mov    0x0(%r13),%rdx
  4014d9:	48 63 d8             	movslq %eax,%rbx
  4014dc:	48 c1 e3 08          	shl    $0x8,%rbx
  4014e0:	48 8b 92 18 01 00 00 	mov    0x118(%rdx),%rdx
  4014e7:	eb 15                	jmp    4014fe <work+0x9e>
  4014e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
   for (int x = data->workindex ; x < bucketlim ; x+= stride ) {
  4014f0:	83 c0 01             	add    $0x1,%eax
  4014f3:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
  4014fa:	39 c5                	cmp    %eax,%ebp
  4014fc:	74 7a                	je     401578 <work+0x118>
    if (data->main->works[x].available == 1 ) {
  4014fe:	44 8b bc 1a 80 00 00 00 	mov    0x80(%rdx,%rbx,1),%r15d
  401506:	48 8d 34 1a          	lea    (%rdx,%rbx,1),%rsi
  40150a:	41 83 ff 01          	cmp    $0x1,%r15d
  40150e:	75 e0                	jne    4014f0 <work+0x90>
    data->workindex = target;
  401510:	41 89 85 80 00 00 00 	mov    %eax,0x80(%r13)
        data->freq++;
  401517:	49 83 45 10 01       	addq   $0x1,0x10(%r13)
        if (data->loglevel == 1) {
  40151c:	41 83 bd 2c 01 00 00 01 	cmpl   $0x1,0x12c(%r13)
  401524:	0f 84 26 01 00 00    	je     401650 <work+0x1f0>
        data->main->works[target].available = 0;
  40152a:	c7 86 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rsi)
        data->threads[data->threadindex].wantindex = -1;
  401534:	49 63 c1             	movslq %r9d,%rax
  401537:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
  40153b:	48 c1 e0 07          	shl    $0x7,%rax
  40153f:	49 03 45 08          	add    0x8(%r13),%rax
  401543:	c7 80 00 01 00 00 ff ff ff ff 	movl   $0xffffffff,0x100(%rax)
        if (found == 0) {
  40154d:	45 85 ff             	test   %r15d,%r15d
  401550:	0f 84 64 01 00 00    	je     4016ba <work+0x25a>
  while (data->running == 1) {
  401556:	41 83 bd 04 01 00 00 01 	cmpl   $0x1,0x104(%r13)
  40155e:	0f 84 3c ff ff ff    	je     4014a0 <work+0x40>
  }
  401564:	48 83 c4 08          	add    $0x8,%rsp
  401568:	31 c0                	xor    %eax,%eax
  40156a:	5b                   	pop    %rbx
  40156b:	5d                   	pop    %rbp
  40156c:	41 5c                	pop    %r12
  40156e:	41 5d                	pop    %r13
  401570:	41 5e                	pop    %r14
  401572:	41 5f                	pop    %r15
  401574:	c3                   	ret
  401575:	0f 1f 00             	nopl   (%rax)
   for (int x = target ; x < data->worksize ; x+= stride ) {
  401578:	49 63 bd 08 01 00 00 	movslq 0x108(%r13),%rdi
  40157f:	85 ff                	test   %edi,%edi
  401581:	0f 8e b9 01 00 00    	jle    401740 <work+0x2e0>
    if (data->main->works[x].available == 1 ) {
  401587:	49 8b 45 00          	mov    0x0(%r13),%rax
  40158b:	31 d2                	xor    %edx,%edx
  40158d:	48 8b 88 18 01 00 00 	mov    0x118(%rax),%rcx
  401594:	eb 1e                	jmp    4015b4 <work+0x154>
  401596:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
   for (int x = target ; x < data->worksize ; x+= stride ) {
  4015a0:	48 83 c2 01          	add    $0x1,%rdx
  4015a4:	48 81 c1 00 01 00 00 	add    $0x100,%rcx
  4015ab:	48 39 d7             	cmp    %rdx,%rdi
  4015ae:	0f 84 8c 01 00 00    	je     401740 <work+0x2e0>
  4015b4:	48 89 d3             	mov    %rdx,%rbx
  4015b7:	89 d0                	mov    %edx,%eax
    if (data->main->works[x].available == 1 ) {
  4015b9:	48 89 ce             	mov    %rcx,%rsi
  4015bc:	48 c1 e3 08          	shl    $0x8,%rbx
  4015c0:	83 b9 80 00 00 00 01 	cmpl   $0x1,0x80(%rcx)
  4015c7:	75 d7                	jne    4015a0 <work+0x140>
      data->threads[data->threadindex].wantindex = target;
  4015c9:	49 63 f9             	movslq %r9d,%rdi
  4015cc:	49 8b 4d 08          	mov    0x8(%r13),%rcx
    data->workindex = target;
  4015d0:	41 89 95 80 00 00 00 	mov    %edx,0x80(%r13)
      data->threads[data->threadindex].wantindex = target;
  4015d7:	4c 8d 04 7f          	lea    (%rdi,%rdi,2),%r8
      for (int x = 0; x < data->threadsize ; x++ ) {
  4015db:	41 8b bd 10 01 00 00 	mov    0x110(%r13),%edi
      data->threads[data->threadindex].wantindex = target;
  4015e2:	49 c1 e0 07          	shl    $0x7,%r8
  4015e6:	49 01 c8             	add    %rcx,%r8
  4015e9:	41 89 90 00 01 00 00 	mov    %edx,0x100(%r8)
      for (int x = 0; x < data->threadsize ; x++ ) {
  4015f0:	85 ff                	test   %edi,%edi
  4015f2:	7e 50                	jle    401644 <work+0x1e4>
  4015f4:	48 81 c1 00 01 00 00 	add    $0x100,%rcx
  4015fb:	31 d2                	xor    %edx,%edx
  4015fd:	0f 1f 00             	nopl   (%rax)
        if (x == data->threadindex) {
  401600:	41 39 d1             	cmp    %edx,%r9d
  401603:	74 0f                	je     401614 <work+0x1b4>
        if (data->threads[x].wantindex != -1 && data->threads[x].wantindex == target /*&& data[x].failcounter > data->threads[data->threadindex].failcounter*/) {
  401605:	8b 31                	mov    (%rcx),%esi
  401607:	83 fe ff             	cmp    $0xffffffff,%esi
  40160a:	74 08                	je     401614 <work+0x1b4>
  40160c:	39 c6                	cmp    %eax,%esi
  40160e:	0f 84 8e 00 00 00    	je     4016a2 <work+0x242>
      for (int x = 0; x < data->threadsize ; x++ ) {
  401614:	83 c2 01             	add    $0x1,%edx
  401617:	48 81 c1 80 01 00 00 	add    $0x180,%rcx
  40161e:	39 fa                	cmp    %edi,%edx
  401620:	7c de                	jl     401600 <work+0x1a0>
      if (available == 1 && data->main->works[target].available == 1) {
  401622:	48 63 d8             	movslq %eax,%rbx
  401625:	48 c1 e3 08          	shl    $0x8,%rbx
  401629:	49 8b 55 00          	mov    0x0(%r13),%rdx
  40162d:	48 8b b2 18 01 00 00 	mov    0x118(%rdx),%rsi
  401634:	48 01 de             	add    %rbx,%rsi
  401637:	83 be 80 00 00 00 01 	cmpl   $0x1,0x80(%rsi)
  40163e:	0f 85 12 ff ff ff    	jne    401556 <work+0xf6>
  401644:	45 31 ff             	xor    %r15d,%r15d
  401647:	e9 cb fe ff ff       	jmp    401517 <work+0xb7>
  40164c:	0f 1f 40 00          	nopl   0x0(%rax)
        if (data->threadindex == 0) {
  401650:	45 85 c9             	test   %r9d,%r9d
  401653:	0f 84 d1 00 00 00    	je     40172a <work+0x2ca>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401659:	48 83 ec 08          	sub    $0x8,%rsp
  40165d:	4c 8d 05 d4 09 00 00 	lea    0x9d4(%rip),%r8        # 402038 <_IO_stdin_used+0x38>
  401664:	50                   	push   %rax
  401665:	ba 01 00 00 00       	mov    $0x1,%edx
  40166a:	be 64 00 00 00       	mov    $0x64,%esi
  40166f:	4c 89 f7             	mov    %r14,%rdi
  401672:	31 c0                	xor    %eax,%eax
  401674:	b9 64 00 00 00       	mov    $0x64,%ecx
  401679:	e8 b2 f9 ff ff       	call   401030 <__snprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  40167e:	4c 89 f7             	mov    %r14,%rdi
  401681:	e8 ca f9 ff ff       	call   401050 <puts@plt>
        data->main->works[target].available = 0;
  401686:	49 8b 45 00          	mov    0x0(%r13),%rax
        data->threads[data->threadindex].wantindex = -1;
  40168a:	45 8b 8d 0c 01 00 00 	mov    0x10c(%r13),%r9d
        data->main->works[target].available = 0;
  401691:	48 8b b0 18 01 00 00 	mov    0x118(%rax),%rsi
  401698:	58                   	pop    %rax
  401699:	5a                   	pop    %rdx
  40169a:	48 01 de             	add    %rbx,%rsi
  40169d:	e9 88 fe ff ff       	jmp    40152a <work+0xca>
          data->threads[data->threadindex].failcounter++;
  4016a2:	41 83 80 28 01 00 00 01 	addl   $0x1,0x128(%r8)
          data->threads[data->threadindex].wantindex = -1;
  4016aa:	41 c7 80 00 01 00 00 ff ff ff ff 	movl   $0xffffffff,0x100(%r8)
      if (available == 1 && data->main->works[target].available == 1) {
  4016b5:	e9 9c fe ff ff       	jmp    401556 <work+0xf6>
        data->workindex = (data->threadindex * data->buckets);
  4016ba:	45 0f af 8d 38 01 00 00 	imul   0x138(%r13),%r9d
        if (data->loglevel == 1) { printf("work epoch end\n"); }
  4016c2:	41 83 bd 2c 01 00 00 01 	cmpl   $0x1,0x12c(%r13)
        data->workindex = (data->threadindex * data->buckets);
  4016ca:	45 89 8d 80 00 00 00 	mov    %r9d,0x80(%r13)
        if (data->loglevel == 1) { printf("work epoch end\n"); }
  4016d1:	0f 84 a5 00 00 00    	je     40177c <work+0x31c>
        for (int x = data->buckets * data->threadindex ; x < bucketlim; x++) {
  4016d7:	44 39 cd             	cmp    %r9d,%ebp
  4016da:	0f 8e 76 fe ff ff    	jle    401556 <work+0xf6>
          data->main->works[x].available = 1;
  4016e0:	49 8b 45 00          	mov    0x0(%r13),%rax
  4016e4:	8d 55 ff             	lea    -0x1(%rbp),%edx
  4016e7:	49 63 f1             	movslq %r9d,%rsi
  4016ea:	44 29 ca             	sub    %r9d,%edx
  4016ed:	48 8b 88 18 01 00 00 	mov    0x118(%rax),%rcx
  4016f4:	48 01 f2             	add    %rsi,%rdx
  4016f7:	48 89 f0             	mov    %rsi,%rax
  4016fa:	48 c1 e0 08          	shl    $0x8,%rax
  4016fe:	48 c1 e2 08          	shl    $0x8,%rdx
  401702:	48 01 c8             	add    %rcx,%rax
  401705:	48 8d 94 11 00 01 00 00 	lea    0x100(%rcx,%rdx,1),%rdx
  40170d:	0f 1f 00             	nopl   (%rax)
  401710:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
        for (int x = data->buckets * data->threadindex ; x < bucketlim; x++) {
  40171a:	48 05 00 01 00 00    	add    $0x100,%rax
  401720:	48 39 c2             	cmp    %rax,%rdx
  401723:	75 eb                	jne    401710 <work+0x2b0>
  401725:	e9 2c fe ff ff       	jmp    401556 <work+0xf6>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  40172a:	48 83 ec 08          	sub    $0x8,%rsp
  40172e:	4c 8d 05 d3 08 00 00 	lea    0x8d3(%rip),%r8        # 402008 <_IO_stdin_used+0x8>
  401735:	50                   	push   %rax
  401736:	e9 2a ff ff ff       	jmp    401665 <work+0x205>
  40173b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->threads[data->threadindex].wantindex = target;
  401740:	49 63 c1             	movslq %r9d,%rax
  401743:	49 8b 4d 08          	mov    0x8(%r13),%rcx
      for (int x = 0; x < data->threadsize ; x++ ) {
  401747:	41 8b bd 10 01 00 00 	mov    0x110(%r13),%edi
    data->workindex = target;
  40174e:	41 c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r13)
      data->threads[data->threadindex].wantindex = target;
  401759:	4c 8d 04 40          	lea    (%rax,%rax,2),%r8
  40175d:	49 c1 e0 07          	shl    $0x7,%r8
  401761:	49 01 c8             	add    %rcx,%r8
  401764:	41 c7 80 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r8)
      for (int x = 0; x < data->threadsize ; x++ ) {
  40176f:	85 ff                	test   %edi,%edi
  401771:	7f 25                	jg     401798 <work+0x338>
  401773:	31 db                	xor    %ebx,%ebx
  401775:	31 c0                	xor    %eax,%eax
  401777:	e9 ad fe ff ff       	jmp    401629 <work+0x1c9>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  40177c:	4c 89 e7             	mov    %r12,%rdi
  40177f:	e8 cc f8 ff ff       	call   401050 <puts@plt>
        for (int x = data->buckets * data->threadindex ; x < bucketlim; x++) {
  401784:	45 8b 8d 38 01 00 00 	mov    0x138(%r13),%r9d
  40178b:	45 0f af 8d 0c 01 00 00 	imul   0x10c(%r13),%r9d
  401793:	e9 3f ff ff ff       	jmp    4016d7 <work+0x277>
      for (int x = 0; x < data->threadsize ; x++ ) {
  401798:	31 c0                	xor    %eax,%eax
  40179a:	e9 55 fe ff ff       	jmp    4015f4 <work+0x194>

Disassembly of section .fini:

00000000004017a0 <_fini>:
  4017a0:	f3 0f 1e fa          	endbr64
  4017a4:	48 83 ec 08          	sub    $0x8,%rsp
  4017a8:	48 83 c4 08          	add    $0x8,%rsp
  4017ac:	c3                   	ret
