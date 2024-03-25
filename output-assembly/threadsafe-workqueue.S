
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
  401020:	ff 35 62 2f 00 00    	push   0x2f62(%rip)        # 403f88 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 64 2f 00 00    	jmp    *0x2f64(%rip)        # 403f90 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <__snprintf_chk@plt>:
  401030:	ff 25 62 2f 00 00    	jmp    *0x2f62(%rip)        # 403f98 <__snprintf_chk@GLIBC_2.3.4>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <pthread_setaffinity_np@plt>:
  401040:	ff 25 5a 2f 00 00    	jmp    *0x2f5a(%rip)        # 403fa0 <pthread_setaffinity_np@GLIBC_2.34>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <puts@plt>:
  401050:	ff 25 52 2f 00 00    	jmp    *0x2f52(%rip)        # 403fa8 <puts@GLIBC_2.2.5>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <__stack_chk_fail@plt>:
  401060:	ff 25 4a 2f 00 00    	jmp    *0x2f4a(%rip)        # 403fb0 <__stack_chk_fail@GLIBC_2.4>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <nanosleep@plt>:
  401070:	ff 25 42 2f 00 00    	jmp    *0x2f42(%rip)        # 403fb8 <nanosleep@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <srand@plt>:
  401080:	ff 25 3a 2f 00 00    	jmp    *0x2f3a(%rip)        # 403fc0 <srand@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <calloc@plt>:
  401090:	ff 25 32 2f 00 00    	jmp    *0x2f32(%rip)        # 403fc8 <calloc@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <time@plt>:
  4010a0:	ff 25 2a 2f 00 00    	jmp    *0x2f2a(%rip)        # 403fd0 <time@GLIBC_2.2.5>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <__printf_chk@plt>:
  4010b0:	ff 25 22 2f 00 00    	jmp    *0x2f22(%rip)        # 403fd8 <__printf_chk@GLIBC_2.3.4>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <pthread_create@plt>:
  4010c0:	ff 25 1a 2f 00 00    	jmp    *0x2f1a(%rip)        # 403fe0 <pthread_create@GLIBC_2.34>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010d0 <pthread_join@plt>:
  4010d0:	ff 25 12 2f 00 00    	jmp    *0x2f12(%rip)        # 403fe8 <pthread_join@GLIBC_2.34>
  4010d6:	68 0a 00 00 00       	push   $0xa
  4010db:	e9 40 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

00000000004010e0 <main>:
      }
     }
      }}
}

int main(int argc, char **argv) {
  4010e0:	41 57                	push   %r15
  int debug = 0;
  int worksize = 30;
  srand(time(NULL));
  4010e2:	31 ff                	xor    %edi,%edi
int main(int argc, char **argv) {
  4010e4:	41 56                	push   %r14
  4010e6:	41 55                	push   %r13
  4010e8:	41 54                	push   %r12
  4010ea:	55                   	push   %rbp
  4010eb:	53                   	push   %rbx
  4010ec:	48 83 ec 68          	sub    $0x68,%rsp
  4010f0:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4010f9:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  4010fe:	31 c0                	xor    %eax,%eax
  srand(time(NULL));
  401100:	e8 9b ff ff ff       	call   4010a0 <time@plt>
  401105:	89 c7                	mov    %eax,%edi
  401107:	e8 74 ff ff ff       	call   401080 <srand@plt>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  40110c:	ba 03 00 00 00       	mov    $0x3,%edx
  401111:	48 8d 35 03 0f 00 00 	lea    0xf03(%rip),%rsi        # 40201b <_IO_stdin_used+0x1b>
  401118:	31 c0                	xor    %eax,%eax
  40111a:	bf 01 00 00 00       	mov    $0x1,%edi
  40111f:	e8 8c ff ff ff       	call   4010b0 <__printf_chk@plt>
  int primes[] = {3, 7, 13, 19, 23, 29, 31, 37};
  int threadsize = 3;
  int buckets = worksize / threadsize;
  printf("Starting %d workers\n", threadsize);
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401124:	be 08 00 00 00       	mov    $0x8,%esi
  401129:	bf 03 00 00 00       	mov    $0x3,%edi
  40112e:	e8 5d ff ff ff       	call   401090 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401133:	be 38 00 00 00       	mov    $0x38,%esi
  401138:	bf 03 00 00 00       	mov    $0x3,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40113d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401142:	e8 49 ff ff ff       	call   401090 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401147:	be 80 04 00 00       	mov    $0x480,%esi
  40114c:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401151:	49 89 c4             	mov    %rax,%r12
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401154:	e8 37 ff ff ff       	call   401090 <calloc@plt>
  struct Work *works = calloc(worksize, sizeof(struct Work));
  401159:	be 00 01 00 00       	mov    $0x100,%esi
  40115e:	bf 1e 00 00 00       	mov    $0x1e,%edi
  401163:	66 48 0f 6e d0       	movq   %rax,%xmm2
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401168:	48 89 c3             	mov    %rax,%rbx
  40116b:	66 0f 6c d2          	punpcklqdq %xmm2,%xmm2
  40116f:	0f 29 14 24          	movaps %xmm2,(%rsp)
  struct Work *works = calloc(worksize, sizeof(struct Work));
  401173:	e8 18 ff ff ff       	call   401090 <calloc@plt>
  
  for (int i = 0; i < worksize; i++) {
  401178:	48 89 c2             	mov    %rax,%rdx
  40117b:	48 8d 88 00 1e 00 00 	lea    0x1e00(%rax),%rcx
  401182:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    works[i].taskindex = 2;
  401188:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
  for (int i = 0; i < worksize; i++) {
  40118e:	48 81 c2 00 01 00 00 	add    $0x100,%rdx
    works[i].available = 1;
  401195:	c7 42 80 01 00 00 00 	movl   $0x1,-0x80(%rdx)
  for (int i = 0; i < worksize; i++) {
  40119c:	48 39 d1             	cmp    %rdx,%rcx
  40119f:	75 e7                	jne    401188 <main+0xa8>
    
  }
  int cpu = 0;
  data[0].works = works;
  4011a1:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  4011a8:	48 89 dd             	mov    %rbx,%rbp
  data[0].works = works;
  4011ab:	49 89 de             	mov    %rbx,%r14
  int cpu = 0;
  4011ae:	45 31 ed             	xor    %r13d,%r13d
  4011b1:	4c 8d 3d f8 0e 00 00 	lea    0xef8(%rip),%r15        # 4020b0 <_IO_stdin_used+0xb0>
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4011b8:	be 80 00 00 00       	mov    $0x80,%esi
  4011bd:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0; x < threadsize ; x++) {
  4011c2:	49 81 c6 80 01 00 00 	add    $0x180,%r14
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4011c9:	e8 c2 fe ff ff       	call   401090 <calloc@plt>
  4011ce:	44 89 ea             	mov    %r13d,%edx
    CPU_SET(cpu += 1, data[x].cpu_set);
  4011d1:	41 83 c5 01          	add    $0x1,%r13d
  4011d5:	be 01 00 00 00       	mov    $0x1,%esi
  4011da:	44 89 e9             	mov    %r13d,%ecx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4011dd:	49 89 46 a0          	mov    %rax,-0x60(%r14)
  4011e1:	bf 01 00 00 00       	mov    $0x1,%edi
    CPU_SET(cpu += 1, data[x].cpu_set);
  4011e6:	48 d3 e6             	shl    %cl,%rsi
  4011e9:	48 09 30             	or     %rsi,(%rax)
  4011ec:	44 89 e9             	mov    %r13d,%ecx
  4011ef:	4c 89 fe             	mov    %r15,%rsi
  4011f2:	31 c0                	xor    %eax,%eax
  4011f4:	89 54 24 14          	mov    %edx,0x14(%rsp)
  4011f8:	e8 b3 fe ff ff       	call   4010b0 <__printf_chk@plt>
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].bucketstart = x * buckets ;
  4011fd:	43 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%eax
    data[x].loglevel = debug;
    data[x].running = 1;
    data[x].threadindex = x;
  401202:	8b 54 24 14          	mov    0x14(%rsp),%edx
    data[x].worksize = worksize;
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].buckets = buckets;
    data[x].main = &data[0];
  401206:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
    data[x].bucketstart = x * buckets ;
  40120b:	8d 44 00 f6          	lea    -0xa(%rax,%rax,1),%eax
    data[x].loglevel = debug;
  40120f:	41 c7 46 ac 00 00 00 00 	movl   $0x0,-0x54(%r14)
    data[x].bucketstart = x * buckets ;
  401217:	41 89 46 c0          	mov    %eax,-0x40(%r14)
    data[x].buckets = buckets;
  40121b:	48 8b 05 ae 0e 00 00 	mov    0xeae(%rip),%rax        # 4020d0 <_IO_stdin_used+0xd0>
    data[x].threadindex = x;
  401222:	41 89 56 8c          	mov    %edx,-0x74(%r14)
    data[x].buckets = buckets;
  401226:	49 89 46 b8          	mov    %rax,-0x48(%r14)
    data[x].threads = data;
    data[x].wantindex = -1;
  40122a:	48 8b 05 a7 0e 00 00 	mov    0xea7(%rip),%rax        # 4020d8 <_IO_stdin_used+0xd8>
    data[x].worksize = worksize;
  401231:	41 c7 46 88 1e 00 00 00 	movl   $0x1e,-0x78(%r14)
    data[x].threadsize = threadsize;
  401239:	41 c7 46 90 03 00 00 00 	movl   $0x3,-0x70(%r14)
    data[x].main = &data[0];
  401241:	41 0f 29 8e 80 fe ff ff 	movaps %xmm1,-0x180(%r14)
    data[x].wantindex = -1;
  401249:	49 89 46 80          	mov    %rax,-0x80(%r14)
  for (int x = 0; x < threadsize ; x++) {
  40124d:	41 83 fd 03          	cmp    $0x3,%r13d
  401251:	0f 85 61 ff ff ff    	jne    4011b8 <main+0xd8>
  401257:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
  40125c:	49 c7 c5 60 14 40 00 	mov    $0x401460,%r13
  401263:	4c 8d b3 80 04 00 00 	lea    0x480(%rbx),%r14
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  40126a:	48 89 e9             	mov    %rbp,%rcx
  40126d:	4c 89 ff             	mov    %r15,%rdi
  401270:	4c 89 ea             	mov    %r13,%rdx
  401273:	4c 89 e6             	mov    %r12,%rsi
  401276:	e8 45 fe ff ff       	call   4010c0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  40127b:	48 8b 95 20 01 00 00 	mov    0x120(%rbp),%rdx
  401282:	49 8b 3f             	mov    (%r15),%rdi
  401285:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  40128a:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
  401291:	49 83 c7 08          	add    $0x8,%r15
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401295:	e8 a6 fd ff ff       	call   401040 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  40129a:	49 39 ee             	cmp    %rbp,%r14
  40129d:	75 cb                	jne    40126a <main+0x18a>
  }
  struct timespec time = {
  40129f:	66 0f 6f 05 39 0e 00 00 	movdqa 0xe39(%rip),%xmm0        # 4020e0 <_IO_stdin_used+0xe0>
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  4012a7:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  4012ac:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    data[x].running = 0;
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  4012b1:	4c 8d 64 24 28       	lea    0x28(%rsp),%r12
  struct timespec time = {
  4012b6:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  struct timespec rem = {
  4012bb:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4012bf:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  nanosleep(&time, &rem);
  4012c4:	e8 a7 fd ff ff       	call   401070 <nanosleep@plt>
    pthread_join(thread[x], &res);
  4012c9:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
  4012ce:	4c 89 e6             	mov    %r12,%rsi
    data[x].running = 0;
  4012d1:	c7 83 04 01 00 00 00 00 00 00 	movl   $0x0,0x104(%rbx)
  4012db:	c7 83 84 02 00 00 00 00 00 00 	movl   $0x0,0x284(%rbx)
  4012e5:	c7 83 04 04 00 00 00 00 00 00 	movl   $0x0,0x404(%rbx)
    pthread_join(thread[x], &res);
  4012ef:	49 8b 3f             	mov    (%r15),%rdi
  4012f2:	e8 d9 fd ff ff       	call   4010d0 <pthread_join@plt>
  4012f7:	49 8b 7f 08          	mov    0x8(%r15),%rdi
  4012fb:	4c 89 e6             	mov    %r12,%rsi
  4012fe:	e8 cd fd ff ff       	call   4010d0 <pthread_join@plt>
  401303:	49 8b 7f 10          	mov    0x10(%r15),%rdi
  401307:	4c 89 e6             	mov    %r12,%rsi
  40130a:	e8 c1 fd ff ff       	call   4010d0 <pthread_join@plt>
  40130f:	48 8d 3d 1a 0d 00 00 	lea    0xd1a(%rip),%rdi        # 402030 <_IO_stdin_used+0x30>
  401316:	e8 35 fd ff ff       	call   401050 <puts@plt>
  }
  printf("finished simulation.\n");
  long freq = 0;
  for (int x= 0; x < threadsize; x++) {
    freq += data[x].freq;
  40131b:	48 8b 93 90 01 00 00 	mov    0x190(%rbx),%rdx
  401322:	31 c0                	xor    %eax,%eax
  401324:	48 03 53 10          	add    0x10(%rbx),%rdx
  401328:	48 8d 35 16 0d 00 00 	lea    0xd16(%rip),%rsi        # 402045 <_IO_stdin_used+0x45>
  40132f:	48 03 93 10 03 00 00 	add    0x310(%rbx),%rdx
  401336:	bf 01 00 00 00       	mov    $0x1,%edi
  40133b:	e8 70 fd ff ff       	call   4010b0 <__printf_chk@plt>
  }
  printf("freq: %ld\n", freq);
  401340:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  401345:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40134e:	75 11                	jne    401361 <main+0x281>
  401350:	48 83 c4 68          	add    $0x68,%rsp
  401354:	31 c0                	xor    %eax,%eax
  401356:	5b                   	pop    %rbx
  401357:	5d                   	pop    %rbp
  401358:	41 5c                	pop    %r12
  40135a:	41 5d                	pop    %r13
  40135c:	41 5e                	pop    %r14
  40135e:	41 5f                	pop    %r15
  401360:	c3                   	ret
  401361:	e8 fa fc ff ff       	call   401060 <__stack_chk_fail@plt>
  401366:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

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
  401388:	48 c7 c7 e0 10 40 00 	mov    $0x4010e0,%rdi
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
  40146b:	41 54                	push   %r12
  40146d:	49 89 fc             	mov    %rdi,%r12
  char * output = calloc(100, sizeof(char));
  401470:	bf 64 00 00 00       	mov    $0x64,%edi
void * work(void * arg) {
  401475:	55                   	push   %rbp
  401476:	53                   	push   %rbx
  401477:	48 83 ec 08          	sub    $0x8,%rsp
  char * output = calloc(100, sizeof(char));
  40147b:	e8 10 fc ff ff       	call   401090 <calloc@plt>
  int bucketstart = data->bucketstart;
  401480:	45 8b b4 24 40 01 00 00 	mov    0x140(%r12),%r14d
  401488:	bf 01 00 00 00       	mov    $0x1,%edi
  40148d:	48 8d 35 70 0b 00 00 	lea    0xb70(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  char * output = calloc(100, sizeof(char));
  401494:	48 89 c5             	mov    %rax,%rbp
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  401497:	41 8b 84 24 0c 01 00 00 	mov    0x10c(%r12),%eax
  40149f:	8d 58 01             	lea    0x1(%rax),%ebx
  4014a2:	89 d8                	mov    %ebx,%eax
  int bucketlim = ((data->threadindex + 1) * data->buckets) ;
  4014a4:	41 0f af 9c 24 38 01 00 00 	imul   0x138(%r12),%ebx
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  4014ad:	99                   	cltd
  4014ae:	41 f7 bc 24 10 01 00 00 	idivl  0x110(%r12)
  4014b6:	31 c0                	xor    %eax,%eax
  4014b8:	41 89 d5             	mov    %edx,%r13d
  4014bb:	89 da                	mov    %ebx,%edx
  4014bd:	e8 ee fb ff ff       	call   4010b0 <__printf_chk@plt>
  data->workindex = bucketstart;
  4014c2:	45 89 b4 24 80 00 00 00 	mov    %r14d,0x80(%r12)
  4014ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  while (data->running == 1) {
  4014d0:	41 83 bc 24 04 01 00 00 01 	cmpl   $0x1,0x104(%r12)
  4014d9:	0f 85 b9 01 00 00    	jne    401698 <work+0x238>
   for (int x = data->bucketstart ; x < bucketlim; x+= stride ) {
  4014df:	41 8b 84 24 40 01 00 00 	mov    0x140(%r12),%eax
  4014e7:	39 c3                	cmp    %eax,%ebx
  4014e9:	0f 8e e1 01 00 00    	jle    4016d0 <work+0x270>
    if (data->main->works[x].available == 1 ) {
  4014ef:	49 8b 14 24          	mov    (%r12),%rdx
  4014f3:	48 63 c8             	movslq %eax,%rcx
  4014f6:	48 c1 e1 08          	shl    $0x8,%rcx
  4014fa:	48 8b 92 18 01 00 00 	mov    0x118(%rdx),%rdx
  401501:	eb 17                	jmp    40151a <work+0xba>
  401503:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
   for (int x = data->bucketstart ; x < bucketlim; x+= stride ) {
  401508:	83 c0 01             	add    $0x1,%eax
  40150b:	48 81 c1 00 01 00 00 	add    $0x100,%rcx
  401512:	39 c3                	cmp    %eax,%ebx
  401514:	0f 84 b6 01 00 00    	je     4016d0 <work+0x270>
    if (data->main->works[x].available == 1 ) {
  40151a:	44 8b 84 0a 80 00 00 00 	mov    0x80(%rdx,%rcx,1),%r8d
  401522:	41 83 f8 01          	cmp    $0x1,%r8d
  401526:	75 e0                	jne    401508 <work+0xa8>
  data->workindex = target;
  401528:	41 89 84 24 80 00 00 00 	mov    %eax,0x80(%r12)
      for (int x = 0; x < data->threadsize ; x++ ) {
  401530:	45 8b 94 24 10 01 00 00 	mov    0x110(%r12),%r10d
    innerfind = 0;
  401538:	45 31 ff             	xor    %r15d,%r15d
      data->threads[data->threadindex].wantindex = target;
  40153b:	45 8b 8c 24 0c 01 00 00 	mov    0x10c(%r12),%r9d
  401543:	49 63 d1             	movslq %r9d,%rdx
  401546:	4d 8b 74 24 08       	mov    0x8(%r12),%r14
  40154b:	4c 8d 1c 52          	lea    (%rdx,%rdx,2),%r11
  40154f:	49 c1 e3 07          	shl    $0x7,%r11
  401553:	4d 01 f3             	add    %r14,%r11
  401556:	41 89 83 00 01 00 00 	mov    %eax,0x100(%r11)
      for (int x = 0; x < data->threadsize ; x++ ) {
  40155d:	45 85 d2             	test   %r10d,%r10d
  401560:	7e 31                	jle    401593 <work+0x133>
  401562:	49 8d b6 00 01 00 00 	lea    0x100(%r14),%rsi
  401569:	31 d2                	xor    %edx,%edx
  40156b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        if (x == data->threadindex) {
  401570:	44 39 ca             	cmp    %r9d,%edx
  401573:	74 0f                	je     401584 <work+0x124>
        if (data->threads[x].wantindex != -1 && data->threads[x].wantindex == target
  401575:	8b 3e                	mov    (%rsi),%edi
  401577:	39 c7                	cmp    %eax,%edi
  401579:	75 09                	jne    401584 <work+0x124>
  40157b:	83 ff ff             	cmp    $0xffffffff,%edi
  40157e:	0f 85 2c 01 00 00    	jne    4016b0 <work+0x250>
      for (int x = 0; x < data->threadsize ; x++ ) {
  401584:	83 c2 01             	add    $0x1,%edx
  401587:	48 81 c6 80 01 00 00 	add    $0x180,%rsi
  40158e:	44 39 d2             	cmp    %r10d,%edx
  401591:	75 dd                	jne    401570 <work+0x110>
      if (available == 1 && data->main->works[target].available == 1) {
  401593:	49 8b 14 24          	mov    (%r12),%rdx
  401597:	48 03 8a 18 01 00 00 	add    0x118(%rdx),%rcx
  40159e:	83 b9 80 00 00 00 01 	cmpl   $0x1,0x80(%rcx)
  4015a5:	0f 84 b5 01 00 00    	je     401760 <work+0x300>
    if (data->threadindex == 0) {
  4015ab:	45 85 c9             	test   %r9d,%r9d
  4015ae:	0f 85 1c ff ff ff    	jne    4014d0 <work+0x70>
     for (int x = 0 ; x< data->threadsize ; x++) {
  4015b4:	45 8b 94 24 10 01 00 00 	mov    0x110(%r12),%r10d
  4015bc:	45 85 d2             	test   %r10d,%r10d
  4015bf:	0f 8e 61 02 00 00    	jle    401826 <work+0x3c6>
  4015c5:	49 8d 96 3c 01 00 00 	lea    0x13c(%r14),%rdx
      for (int x = 0; x < data->threadsize ; x++ ) {
  4015cc:	31 c0                	xor    %eax,%eax
  4015ce:	31 c9                	xor    %ecx,%ecx
     for (int x = 0 ; x< data->threadsize ; x++) {
  4015d0:	83 c0 01             	add    $0x1,%eax
       availables += data->threads[x].availables;
  4015d3:	03 0a                	add    (%rdx),%ecx
     for (int x = 0 ; x< data->threadsize ; x++) {
  4015d5:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
  4015dc:	44 39 d0             	cmp    %r10d,%eax
  4015df:	7c ef                	jl     4015d0 <work+0x170>
     if (availables == 0) {
  4015e1:	85 c9                	test   %ecx,%ecx
  4015e3:	0f 85 e7 fe ff ff    	jne    4014d0 <work+0x70>
          data->workindex = data->bucketstart;
  4015e9:	41 8b 84 24 40 01 00 00 	mov    0x140(%r12),%eax
      if (data->loglevel == 1) { printf("all used\n"); }
  4015f1:	41 83 bc 24 2c 01 00 00 01 	cmpl   $0x1,0x12c(%r12)
          data->workindex = data->bucketstart;
  4015fa:	41 89 84 24 80 00 00 00 	mov    %eax,0x80(%r12)
      if (data->loglevel == 1) { printf("all used\n"); }
  401602:	0f 84 3d 02 00 00    	je     401845 <work+0x3e5>
          data->threads[x].availables = data->buckets;
  401608:	41 8b 8c 24 38 01 00 00 	mov    0x138(%r12),%ecx
  401610:	49 83 ee 80          	sub    $0xffffffffffffff80,%r14
  401614:	31 c0                	xor    %eax,%eax
  401616:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            data->threads[x].workindex = data->threads[x].bucketstart;
  401620:	41 8b 96 c0 00 00 00 	mov    0xc0(%r14),%edx
        for (int x = 0; x < data->threadsize ; x++) {
  401627:	83 c0 01             	add    $0x1,%eax
          data->threads[x].availables = data->buckets;
  40162a:	41 89 8e bc 00 00 00 	mov    %ecx,0xbc(%r14)
        for (int x = 0; x < data->threadsize ; x++) {
  401631:	49 81 c6 80 01 00 00 	add    $0x180,%r14
            data->threads[x].workindex = data->threads[x].bucketstart;
  401638:	41 89 96 80 fe ff ff 	mov    %edx,-0x180(%r14)
        for (int x = 0; x < data->threadsize ; x++) {
  40163f:	44 39 d0             	cmp    %r10d,%eax
  401642:	7c dc                	jl     401620 <work+0x1c0>
      for (int x = 0; x < data->worksize; x++) {
  401644:	41 8b 94 24 08 01 00 00 	mov    0x108(%r12),%edx
  40164c:	85 d2                	test   %edx,%edx
  40164e:	0f 8e 7c fe ff ff    	jle    4014d0 <work+0x70>
        data->main->works[x].available = 1;
  401654:	49 8b 04 24          	mov    (%r12),%rax
  401658:	83 ea 01             	sub    $0x1,%edx
  40165b:	48 c1 e2 08          	shl    $0x8,%rdx
  40165f:	48 8b 88 18 01 00 00 	mov    0x118(%rax),%rcx
  401666:	48 8d 81 80 00 00 00 	lea    0x80(%rcx),%rax
  40166d:	48 8d 94 11 80 01 00 00 	lea    0x180(%rcx,%rdx,1),%rdx
  401675:	0f 1f 00             	nopl   (%rax)
  401678:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
      for (int x = 0; x < data->worksize; x++) {
  40167e:	48 05 00 01 00 00    	add    $0x100,%rax
  401684:	48 39 c2             	cmp    %rax,%rdx
  401687:	75 ef                	jne    401678 <work+0x218>
  while (data->running == 1) {
  401689:	41 83 bc 24 04 01 00 00 01 	cmpl   $0x1,0x104(%r12)
  401692:	0f 84 47 fe ff ff    	je     4014df <work+0x7f>
}
  401698:	48 83 c4 08          	add    $0x8,%rsp
  40169c:	31 c0                	xor    %eax,%eax
  40169e:	5b                   	pop    %rbx
  40169f:	5d                   	pop    %rbp
  4016a0:	41 5c                	pop    %r12
  4016a2:	41 5d                	pop    %r13
  4016a4:	41 5e                	pop    %r14
  4016a6:	41 5f                	pop    %r15
  4016a8:	c3                   	ret
  4016a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          data->threads[data->threadindex].wantindex = -1;
  4016b0:	41 c7 83 00 01 00 00 ff ff ff ff 	movl   $0xffffffff,0x100(%r11)
    if (data->threadindex == 0) {
  4016bb:	45 85 c9             	test   %r9d,%r9d
  4016be:	0f 85 0c fe ff ff    	jne    4014d0 <work+0x70>
  4016c4:	e9 fc fe ff ff       	jmp    4015c5 <work+0x165>
  4016c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    currentbucket = (currentbucket + 1) % data->threadsize;
  4016d0:	41 8d 45 01          	lea    0x1(%r13),%eax
  4016d4:	45 8b 94 24 10 01 00 00 	mov    0x110(%r12),%r10d
    if (currentbucket == data->threadindex) { currentbucket = (currentbucket + 1) % data->threadsize;}
  4016dc:	45 8b 8c 24 0c 01 00 00 	mov    0x10c(%r12),%r9d
  data->workindex = target;
  4016e4:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
    currentbucket = (currentbucket + 1) % data->threadsize;
  4016f0:	99                   	cltd
  4016f1:	41 f7 fa             	idiv   %r10d
  4016f4:	41 89 d5             	mov    %edx,%r13d
    if (currentbucket == data->threadindex) { currentbucket = (currentbucket + 1) % data->threadsize;}
  4016f7:	41 39 d1             	cmp    %edx,%r9d
  4016fa:	75 0b                	jne    401707 <work+0x2a7>
  4016fc:	41 8d 45 01          	lea    0x1(%r13),%eax
  401700:	99                   	cltd
  401701:	41 f7 fa             	idiv   %r10d
  401704:	41 89 d5             	mov    %edx,%r13d
   for (int x = currentbucket * data->buckets ; x < (currentbucket * data->buckets) + data->buckets ; x+= stride ) {
  401707:	41 8b 94 24 38 01 00 00 	mov    0x138(%r12),%edx
  40170f:	89 d0                	mov    %edx,%eax
  401711:	41 0f af c5          	imul   %r13d,%eax
  401715:	01 c2                	add    %eax,%edx
  401717:	39 d0                	cmp    %edx,%eax
  401719:	0f 8d 99 00 00 00    	jge    4017b8 <work+0x358>
    if (data->main->works[x].available == 1 ) {
  40171f:	49 8b 0c 24          	mov    (%r12),%rcx
  401723:	48 8b b1 18 01 00 00 	mov    0x118(%rcx),%rsi
  40172a:	48 63 c8             	movslq %eax,%rcx
  40172d:	48 c1 e1 08          	shl    $0x8,%rcx
  401731:	eb 13                	jmp    401746 <work+0x2e6>
  401733:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
   for (int x = currentbucket * data->buckets ; x < (currentbucket * data->buckets) + data->buckets ; x+= stride ) {
  401738:	83 c0 01             	add    $0x1,%eax
  40173b:	48 81 c1 00 01 00 00 	add    $0x100,%rcx
  401742:	39 d0                	cmp    %edx,%eax
  401744:	74 72                	je     4017b8 <work+0x358>
    if (data->main->works[x].available == 1 ) {
  401746:	44 8b bc 0e 80 00 00 00 	mov    0x80(%rsi,%rcx,1),%r15d
  40174e:	41 83 ff 01          	cmp    $0x1,%r15d
  401752:	75 e4                	jne    401738 <work+0x2d8>
    found = 0;
  401754:	45 31 c0             	xor    %r8d,%r8d
  401757:	e9 e7 fd ff ff       	jmp    401543 <work+0xe3>
  40175c:	0f 1f 40 00          	nopl   0x0(%rax)
        if (innerfind == 1) {
  401760:	41 83 ff 01          	cmp    $0x1,%r15d
  401764:	75 14                	jne    40177a <work+0x31a>
       data->threads[currentbucket].availables--;
  401766:	49 63 d5             	movslq %r13d,%rdx
  401769:	48 8d 14 52          	lea    (%rdx,%rdx,2),%rdx
  40176d:	48 c1 e2 07          	shl    $0x7,%rdx
  401771:	41 83 ac 16 3c 01 00 00 01 	subl   $0x1,0x13c(%r14,%rdx,1)
        if (found == 1) {
  40177a:	41 83 f8 01          	cmp    $0x1,%r8d
  40177e:	75 09                	jne    401789 <work+0x329>
          data->availables--;
  401780:	41 83 ac 24 3c 01 00 00 01 	subl   $0x1,0x13c(%r12)
data->main->works[target].available = 0;
  401789:	c7 81 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rcx)
        data->freq++;
  401793:	49 83 44 24 10 01    	addq   $0x1,0x10(%r12)
        if (data->loglevel == 1) {
  401799:	41 83 bc 24 2c 01 00 00 01 	cmpl   $0x1,0x12c(%r12)
  4017a2:	74 23                	je     4017c7 <work+0x367>
        data->threads[data->threadindex].wantindex = -1;
  4017a4:	41 c7 83 00 01 00 00 ff ff ff ff 	movl   $0xffffffff,0x100(%r11)
  4017af:	e9 f7 fd ff ff       	jmp    4015ab <work+0x14b>
  4017b4:	0f 1f 40 00          	nopl   0x0(%rax)
   for (int x = currentbucket * data->buckets ; x < (currentbucket * data->buckets) + data->buckets ; x+= stride ) {
  4017b8:	31 c9                	xor    %ecx,%ecx
    found = 0;
  4017ba:	45 31 c0             	xor    %r8d,%r8d
      int target = 0;
  4017bd:	31 c0                	xor    %eax,%eax
    innerfind = 0;
  4017bf:	45 31 ff             	xor    %r15d,%r15d
  4017c2:	e9 7c fd ff ff       	jmp    401543 <work+0xe3>
        if (data->threadindex == 0) {
  4017c7:	45 85 c9             	test   %r9d,%r9d
  4017ca:	74 4c                	je     401818 <work+0x3b8>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  4017cc:	48 83 ec 08          	sub    $0x8,%rsp
  4017d0:	4c 8d 05 a9 08 00 00 	lea    0x8a9(%rip),%r8        # 402080 <_IO_stdin_used+0x80>
  4017d7:	50                   	push   %rax
  4017d8:	ba 01 00 00 00       	mov    $0x1,%edx
  4017dd:	b9 64 00 00 00       	mov    $0x64,%ecx
  4017e2:	48 89 ef             	mov    %rbp,%rdi
  4017e5:	31 c0                	xor    %eax,%eax
  4017e7:	be 64 00 00 00       	mov    $0x64,%esi
  4017ec:	e8 3f f8 ff ff       	call   401030 <__snprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4017f1:	48 89 ef             	mov    %rbp,%rdi
  4017f4:	e8 57 f8 ff ff       	call   401050 <puts@plt>
        data->threads[data->threadindex].wantindex = -1;
  4017f9:	49 63 84 24 0c 01 00 00 	movslq 0x10c(%r12),%rax
  401801:	4d 8b 74 24 08       	mov    0x8(%r12),%r14
  401806:	4c 8d 1c 40          	lea    (%rax,%rax,2),%r11
  40180a:	49 89 c1             	mov    %rax,%r9
  40180d:	58                   	pop    %rax
  40180e:	5a                   	pop    %rdx
  40180f:	49 c1 e3 07          	shl    $0x7,%r11
  401813:	4d 01 f3             	add    %r14,%r11
  401816:	eb 8c                	jmp    4017a4 <work+0x344>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401818:	48 83 ec 08          	sub    $0x8,%rsp
  40181c:	4c 8d 05 2d 08 00 00 	lea    0x82d(%rip),%r8        # 402050 <_IO_stdin_used+0x50>
  401823:	50                   	push   %rax
  401824:	eb b2                	jmp    4017d8 <work+0x378>
          data->workindex = data->bucketstart;
  401826:	41 8b 84 24 40 01 00 00 	mov    0x140(%r12),%eax
      if (data->loglevel == 1) { printf("all used\n"); }
  40182e:	41 83 bc 24 2c 01 00 00 01 	cmpl   $0x1,0x12c(%r12)
          data->workindex = data->bucketstart;
  401837:	41 89 84 24 80 00 00 00 	mov    %eax,0x80(%r12)
      if (data->loglevel == 1) { printf("all used\n"); }
  40183f:	0f 85 ff fd ff ff    	jne    401644 <work+0x1e4>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  401845:	48 8d 3d c6 07 00 00 	lea    0x7c6(%rip),%rdi        # 402012 <_IO_stdin_used+0x12>
  40184c:	e8 ff f7 ff ff       	call   401050 <puts@plt>
        for (int x = 0; x < data->threadsize ; x++) {
  401851:	45 8b 94 24 10 01 00 00 	mov    0x110(%r12),%r10d
  401859:	45 85 d2             	test   %r10d,%r10d
  40185c:	0f 8e e2 fd ff ff    	jle    401644 <work+0x1e4>
          data->threads[x].availables = data->buckets;
  401862:	4d 8b 74 24 08       	mov    0x8(%r12),%r14
  401867:	e9 9c fd ff ff       	jmp    401608 <work+0x1a8>

Disassembly of section .fini:

000000000040186c <_fini>:
  40186c:	f3 0f 1e fa          	endbr64
  401870:	48 83 ec 08          	sub    $0x8,%rsp
  401874:	48 83 c4 08          	add    $0x8,%rsp
  401878:	c3                   	ret
