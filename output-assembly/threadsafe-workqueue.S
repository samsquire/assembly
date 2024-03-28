
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

0000000000401020 <pthread_setaffinity_np@plt-0x10>:
  401020:	ff 35 7a 2f 00 00    	push   0x2f7a(%rip)        # 403fa0 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 7c 2f 00 00    	jmp    *0x2f7c(%rip)        # 403fa8 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <pthread_setaffinity_np@plt>:
  401030:	ff 25 7a 2f 00 00    	jmp    *0x2f7a(%rip)        # 403fb0 <pthread_setaffinity_np@GLIBC_2.34>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <puts@plt>:
  401040:	ff 25 72 2f 00 00    	jmp    *0x2f72(%rip)        # 403fb8 <puts@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <__stack_chk_fail@plt>:
  401050:	ff 25 6a 2f 00 00    	jmp    *0x2f6a(%rip)        # 403fc0 <__stack_chk_fail@GLIBC_2.4>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <nanosleep@plt>:
  401060:	ff 25 62 2f 00 00    	jmp    *0x2f62(%rip)        # 403fc8 <nanosleep@GLIBC_2.2.5>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <calloc@plt>:
  401070:	ff 25 5a 2f 00 00    	jmp    *0x2f5a(%rip)        # 403fd0 <calloc@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <__printf_chk@plt>:
  401080:	ff 25 52 2f 00 00    	jmp    *0x2f52(%rip)        # 403fd8 <__printf_chk@GLIBC_2.3.4>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <pthread_create@plt>:
  401090:	ff 25 4a 2f 00 00    	jmp    *0x2f4a(%rip)        # 403fe0 <pthread_create@GLIBC_2.34>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <pthread_join@plt>:
  4010a0:	ff 25 42 2f 00 00    	jmp    *0x2f42(%rip)        # 403fe8 <pthread_join@GLIBC_2.34>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

00000000004010b0 <main>:
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
}

int main(int argc, char **argv) {
  4010b0:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4010b2:	ba 08 00 00 00       	mov    $0x8,%edx
  4010b7:	bf 01 00 00 00       	mov    $0x1,%edi
  printf("Starting %d workers\n", threadsize);
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  
  long offset = 0;
  4010bc:	45 31 ff             	xor    %r15d,%r15d
int main(int argc, char **argv) {
  4010bf:	41 56                	push   %r14
  4010c1:	48 8d 35 73 0f 00 00 	lea    0xf73(%rip),%rsi        # 40203b <_IO_stdin_used+0x3b>
  4010c8:	41 55                	push   %r13
  4010ca:	4c 8d 2d ff 0f 00 00 	lea    0xfff(%rip),%r13        # 4020d0 <_IO_stdin_used+0xd0>
  4010d1:	41 54                	push   %r12
  4010d3:	55                   	push   %rbp
  4010d4:	53                   	push   %rbx
  4010d5:	48 83 ec 78          	sub    $0x78,%rsp
  4010d9:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4010e2:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  4010e7:	31 c0                	xor    %eax,%eax
  4010e9:	e8 92 ff ff ff       	call   401080 <__printf_chk@plt>
  4010ee:	ba 04 00 00 00       	mov    $0x4,%edx
  4010f3:	48 8d 35 53 0f 00 00 	lea    0xf53(%rip),%rsi        # 40204d <_IO_stdin_used+0x4d>
  4010fa:	31 c0                	xor    %eax,%eax
  4010fc:	bf 01 00 00 00       	mov    $0x1,%edi
  401101:	e8 7a ff ff ff       	call   401080 <__printf_chk@plt>
  401106:	ba 20 00 00 00       	mov    $0x20,%edx
  40110b:	48 8d 35 37 0f 00 00 	lea    0xf37(%rip),%rsi        # 402049 <_IO_stdin_used+0x49>
  401112:	31 c0                	xor    %eax,%eax
  401114:	bf 01 00 00 00       	mov    $0x1,%edi
  401119:	e8 62 ff ff ff       	call   401080 <__printf_chk@plt>
  40111e:	ba 08 00 00 00       	mov    $0x8,%edx
  401123:	48 8d 35 32 0f 00 00 	lea    0xf32(%rip),%rsi        # 40205c <_IO_stdin_used+0x5c>
  40112a:	31 c0                	xor    %eax,%eax
  40112c:	bf 01 00 00 00       	mov    $0x1,%edi
  401131:	e8 4a ff ff ff       	call   401080 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401136:	be 08 00 00 00       	mov    $0x8,%esi
  40113b:	bf 08 00 00 00       	mov    $0x8,%edi
  401140:	e8 2b ff ff ff       	call   401070 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401145:	be 38 00 00 00       	mov    $0x38,%esi
  40114a:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40114f:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401154:	e8 17 ff ff ff       	call   401070 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401159:	be 00 0c 00 00       	mov    $0xc00,%esi
  40115e:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401163:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401168:	e8 03 ff ff ff       	call   401070 <calloc@plt>
  long chunkslen = ((threadsize - 1) * 2) + threadsize;
  int worksize = chunkslen * worksize_each;
  int buckets = worksize / threadsize;
  long chunksize = ceil((double) worksize / (double) chunkslen);
  struct Work *works = calloc(worksize, sizeof(struct Work));
  40116d:	be 00 01 00 00       	mov    $0x100,%esi
  401172:	bf 16 00 00 00       	mov    $0x16,%edi
  401177:	66 48 0f 6e e8       	movq   %rax,%xmm5
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40117c:	48 89 c3             	mov    %rax,%rbx
  40117f:	66 0f 6c ed          	punpcklqdq %xmm5,%xmm5
  401183:	0f 29 2c 24          	movaps %xmm5,(%rsp)
  struct Work *works = calloc(worksize, sizeof(struct Work));
  401187:	e8 e4 fe ff ff       	call   401070 <calloc@plt>
  40118c:	ba 16 00 00 00       	mov    $0x16,%edx
  401191:	bf 01 00 00 00       	mov    $0x1,%edi
  401196:	48 8d 35 d4 0e 00 00 	lea    0xed4(%rip),%rsi        # 402071 <_IO_stdin_used+0x71>
  40119d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  4011a2:	31 c0                	xor    %eax,%eax
  4011a4:	e8 d7 fe ff ff       	call   401080 <__printf_chk@plt>
  printf("Buffer size %d\n", worksize);
  int chunkindex = 0;
  struct Chunk *freelist = calloc(chunkslen, sizeof(struct Chunk));
  4011a9:	be 00 01 00 00       	mov    $0x100,%esi
  4011ae:	bf 16 00 00 00       	mov    $0x16,%edi
  4011b3:	e8 b8 fe ff ff       	call   401070 <calloc@plt>
  4011b8:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
          for (int x = 0; x < chunkslen; x++) {
  4011bd:	49 89 c4             	mov    %rax,%r12
  4011c0:	45 89 fe             	mov    %r15d,%r14d
        
          
          long start = offset;
          
          
          long end = start + chunksize;
  4011c3:	4c 89 fd             	mov    %r15,%rbp
  4011c6:	49 83 c7 01          	add    $0x1,%r15
  4011ca:	4c 89 ee             	mov    %r13,%rsi
  4011cd:	4d 89 f8             	mov    %r15,%r8
  4011d0:	48 89 e9             	mov    %rbp,%rcx
  4011d3:	44 89 f2             	mov    %r14d,%edx
  4011d6:	bf 01 00 00 00       	mov    $0x1,%edi
  4011db:	31 c0                	xor    %eax,%eax
          for (int x = 0; x < chunkslen; x++) {
  4011dd:	49 81 c4 00 01 00 00 	add    $0x100,%r12
  4011e4:	e8 97 fe ff ff       	call   401080 <__printf_chk@plt>
          
          printf("writer giving %d between %ld and %ld\n", x, start, end);
          offset += chunksize;
        
         freelist[chunkindex].index = chunkindex;   freelist[chunkindex].available = FREE;
            freelist[chunkindex].start = start;
  4011e9:	66 48 0f 6e c5       	movq   %rbp,%xmm0
  4011ee:	66 49 0f 6e cf       	movq   %r15,%xmm1
         freelist[chunkindex].index = chunkindex;   freelist[chunkindex].available = FREE;
  4011f3:	45 89 74 24 88       	mov    %r14d,-0x78(%r12)
  4011f8:	41 c7 44 24 80 01 00 00 00 	movl   $0x1,-0x80(%r12)
            freelist[chunkindex].start = start;
  401201:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
  401205:	41 0f 29 84 24 00 ff ff ff 	movaps %xmm0,-0x100(%r12)
          for (int x = 0; x < chunkslen; x++) {
  40120e:	49 83 ff 16          	cmp    $0x16,%r15
  401212:	75 ac                	jne    4011c0 <main+0x110>
  401214:	ba 16 00 00 00       	mov    $0x16,%edx
  401219:	48 8d 35 61 0e 00 00 	lea    0xe61(%rip),%rsi        # 402081 <_IO_stdin_used+0x81>
  401220:	bf 01 00 00 00       	mov    $0x1,%edi
  401225:	31 c0                	xor    %eax,%eax
  401227:	e8 54 fe ff ff       	call   401080 <__printf_chk@plt>
freelist[chunkindex].end = end;
            chunkindex++;
        }

printf("%ld chunks\n", chunkslen);
  for (int i = 0; i < worksize; i++) {
  40122c:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
  401231:	48 89 c8             	mov    %rcx,%rax
  401234:	48 8d 91 00 16 00 00 	lea    0x1600(%rcx),%rdx
  40123b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    works[i].taskindex = 2;
  401240:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
  for (int i = 0; i < worksize; i++) {
  401246:	48 05 00 01 00 00    	add    $0x100,%rax
    works[i].available = 1;
  40124c:	c7 40 80 01 00 00 00 	movl   $0x1,-0x80(%rax)
  for (int i = 0; i < worksize; i++) {
  401253:	48 39 c2             	cmp    %rax,%rdx
  401256:	75 e8                	jne    401240 <main+0x190>
    
  }
  int cpu = 0;
  data[0].works = works;
  401258:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  40125d:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
  401262:	49 89 dc             	mov    %rbx,%r12
  401265:	49 89 de             	mov    %rbx,%r14
  401268:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
  int cpu = 0;
  40126d:	45 31 ed             	xor    %r13d,%r13d
  401270:	4c 8d 3d 81 0e 00 00 	lea    0xe81(%rip),%r15        # 4020f8 <_IO_stdin_used+0xf8>
  data[0].works = works;
  401277:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  40127e:	66 90                	xchg   %ax,%ax
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401280:	44 89 eb             	mov    %r13d,%ebx
  401283:	be 80 00 00 00       	mov    $0x80,%esi
    CPU_SET(cpu += 1, data[x].cpu_set);
  401288:	41 83 c5 01          	add    $0x1,%r13d
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  40128c:	bf 01 00 00 00       	mov    $0x1,%edi
  401291:	e8 da fd ff ff       	call   401070 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  401296:	44 89 e9             	mov    %r13d,%ecx
  401299:	ba 01 00 00 00       	mov    $0x1,%edx
  40129e:	4c 89 fe             	mov    %r15,%rsi
  4012a1:	48 d3 e2             	shl    %cl,%rdx
  4012a4:	48 09 10             	or     %rdx,(%rax)
  4012a7:	44 89 e9             	mov    %r13d,%ecx
  4012aa:	89 da                	mov    %ebx,%edx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4012ac:	49 89 86 20 01 00 00 	mov    %rax,0x120(%r14)
  4012b3:	bf 01 00 00 00       	mov    $0x1,%edi
  4012b8:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  4012ba:	49 81 c6 80 01 00 00 	add    $0x180,%r14
  4012c1:	e8 ba fd ff ff       	call   401080 <__printf_chk@plt>
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].bucketstart = x * buckets ;
  4012c6:	43 8d 44 2d fe       	lea    -0x2(%r13,%r13,1),%eax
    data[x].worksize = worksize;
    data[x].ready = 0;
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].buckets = buckets;
    data[x].main = &data[0];
  4012cb:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
    data[x].threads = data;
    data[x].wantindex = -1;
    data[x].read = 0;
  4012d0:	66 0f 6f 1d 58 0e 00 00 	movdqa 0xe58(%rip),%xmm3        # 402130 <_IO_stdin_used+0x130>
    data[x].bucketstart = x * buckets ;
  4012d8:	41 89 46 c0          	mov    %eax,-0x40(%r14)
    data[x].buckets = buckets;
  4012dc:	48 8b 05 35 0e 00 00 	mov    0xe35(%rip),%rax        # 402118 <_IO_stdin_used+0x118>
    data[x].write = worksize;
    
    data[x].freelist = freelist;
    data[x].chunksize = chunksize;
    data[x].chunkslen = chunkslen;
  4012e3:	66 0f 6f 25 55 0e 00 00 	movdqa 0xe55(%rip),%xmm4        # 402140 <_IO_stdin_used+0x140>
    data[x].loglevel = debug;
  4012eb:	41 c7 46 ac 00 00 00 00 	movl   $0x0,-0x54(%r14)
    data[x].buckets = buckets;
  4012f3:	49 89 46 b8          	mov    %rax,-0x48(%r14)
    data[x].wantindex = -1;
  4012f7:	48 8b 05 22 0e 00 00 	mov    0xe22(%rip),%rax        # 402120 <_IO_stdin_used+0x120>
    data[x].threadindex = x;
  4012fe:	41 89 5e 8c          	mov    %ebx,-0x74(%r14)
    data[x].worksize = worksize;
  401302:	41 c7 46 88 16 00 00 00 	movl   $0x16,-0x78(%r14)
    data[x].ready = 0;
  40130a:	49 c7 86 a8 fe ff ff 00 00 00 00 	movq   $0x0,-0x158(%r14)
    data[x].threadsize = threadsize;
  401315:	41 c7 46 90 08 00 00 00 	movl   $0x8,-0x70(%r14)
    data[x].main = &data[0];
  40131d:	41 0f 29 96 b0 fe ff ff 	movaps %xmm2,-0x150(%r14)
    data[x].wantindex = -1;
  401325:	49 89 46 80          	mov    %rax,-0x80(%r14)
    data[x].read = 0;
  401329:	41 0f 29 9e 80 fe ff ff 	movaps %xmm3,-0x180(%r14)
    data[x].freelist = freelist;
  401331:	49 89 6e c8          	mov    %rbp,-0x38(%r14)
    data[x].chunkslen = chunkslen;
  401335:	41 0f 29 66 e0       	movaps %xmm4,-0x20(%r14)
    data[x].newmask = 0;
  40133a:	49 c7 46 f0 00 00 00 00 	movq   $0x0,-0x10(%r14)
  for (int x = 0; x < threadsize ; x++) {
  401342:	41 83 fd 08          	cmp    $0x8,%r13d
  401346:	0f 85 34 ff ff ff    	jne    401280 <main+0x1d0>
  40134c:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
  401351:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
  401356:	49 c7 c5 e0 15 40 00 	mov    $0x4015e0,%r13
  40135d:	4c 8d b3 00 0c 00 00 	lea    0xc00(%rbx),%r14
  401364:	48 89 1c 24          	mov    %rbx,(%rsp)
  401368:	4c 89 fd             	mov    %r15,%rbp
  40136b:	4c 89 fb             	mov    %r15,%rbx
  40136e:	4d 89 f7             	mov    %r14,%r15
  401371:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
  401376:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  401380:	4c 89 e1             	mov    %r12,%rcx
  401383:	48 89 df             	mov    %rbx,%rdi
  401386:	4c 89 ea             	mov    %r13,%rdx
  401389:	4c 89 f6             	mov    %r14,%rsi
  40138c:	e8 ff fc ff ff       	call   401090 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401391:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
  401399:	48 8b 3b             	mov    (%rbx),%rdi
  40139c:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  4013a1:	49 81 c4 80 01 00 00 	add    $0x180,%r12
  4013a8:	48 83 c3 08          	add    $0x8,%rbx
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4013ac:	e8 7f fc ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  4013b1:	4d 39 e7             	cmp    %r12,%r15
  4013b4:	75 ca                	jne    401380 <main+0x2d0>
  }
  
  struct timespec time = {
  4013b6:	48 8b 1c 24          	mov    (%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  4013ba:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  4013bf:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec time = {
  4013c4:	66 0f 6f 05 84 0d 00 00 	movdqa 0xd84(%rip),%xmm0        # 402150 <_IO_stdin_used+0x150>
  4013cc:	4c 8d 6c 24 38       	lea    0x38(%rsp),%r13
  4013d1:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  4013d6:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4013da:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  4013df:	e8 7c fc ff ff       	call   401060 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  4013e4:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
  4013e9:	c7 83 04 01 00 00 00 00 00 00 	movl   $0x0,0x104(%rbx)
  4013f3:	c7 83 84 02 00 00 00 00 00 00 	movl   $0x0,0x284(%rbx)
  4013fd:	c7 83 04 04 00 00 00 00 00 00 	movl   $0x0,0x404(%rbx)
  401407:	49 83 c4 40          	add    $0x40,%r12
  40140b:	c7 83 84 05 00 00 00 00 00 00 	movl   $0x0,0x584(%rbx)
  401415:	c7 83 04 07 00 00 00 00 00 00 	movl   $0x0,0x704(%rbx)
  40141f:	c7 83 84 08 00 00 00 00 00 00 	movl   $0x0,0x884(%rbx)
  401429:	c7 83 04 0a 00 00 00 00 00 00 	movl   $0x0,0xa04(%rbx)
  401433:	c7 83 84 0b 00 00 00 00 00 00 	movl   $0x0,0xb84(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  40143d:	0f 1f 00             	nopl   (%rax)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401440:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
  401444:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  401447:	48 83 c5 08          	add    $0x8,%rbp
    pthread_join(thread[x], &res);
  40144b:	e8 50 fc ff ff       	call   4010a0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401450:	49 39 ec             	cmp    %rbp,%r12
  401453:	75 eb                	jne    401440 <main+0x390>
  401455:	48 8d 3d 31 0c 00 00 	lea    0xc31(%rip),%rdi        # 40208d <_IO_stdin_used+0x8d>
  40145c:	e8 df fb ff ff       	call   401040 <puts@plt>
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  for (int x= 0; x < threadsize; x++) {
    freq += data[x].freq;
  401461:	48 8b 8b d8 01 00 00 	mov    0x1d8(%rbx),%rcx
  401468:	bf 01 00 00 00       	mov    $0x1,%edi
  40146d:	48 03 8b 58 03 00 00 	add    0x358(%rbx),%rcx
  401474:	48 03 4b 58          	add    0x58(%rbx),%rcx
  401478:	48 03 8b d8 04 00 00 	add    0x4d8(%rbx),%rcx
  }
  printf("freq: %ld\n", freq / seconds);
  40147f:	48 ba 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rdx
    freq += data[x].freq;
  401489:	48 03 8b 58 06 00 00 	add    0x658(%rbx),%rcx
  401490:	48 03 8b d8 07 00 00 	add    0x7d8(%rbx),%rcx
  401497:	48 8d 35 04 0c 00 00 	lea    0xc04(%rip),%rsi        # 4020a2 <_IO_stdin_used+0xa2>
  40149e:	48 03 8b 58 09 00 00 	add    0x958(%rbx),%rcx
  4014a5:	48 03 8b d8 0a 00 00 	add    0xad8(%rbx),%rcx
  printf("freq: %ld\n", freq / seconds);
  4014ac:	48 89 c8             	mov    %rcx,%rax
  4014af:	48 c1 f9 3f          	sar    $0x3f,%rcx
  4014b3:	48 f7 ea             	imul   %rdx
  4014b6:	31 c0                	xor    %eax,%eax
  4014b8:	48 d1 fa             	sar    %rdx
  4014bb:	48 29 ca             	sub    %rcx,%rdx
  4014be:	e8 bd fb ff ff       	call   401080 <__printf_chk@plt>
  4014c3:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  4014c8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4014d1:	75 11                	jne    4014e4 <main+0x434>
  4014d3:	48 83 c4 78          	add    $0x78,%rsp
  4014d7:	31 c0                	xor    %eax,%eax
  4014d9:	5b                   	pop    %rbx
  4014da:	5d                   	pop    %rbp
  4014db:	41 5c                	pop    %r12
  4014dd:	41 5d                	pop    %r13
  4014df:	41 5e                	pop    %r14
  4014e1:	41 5f                	pop    %r15
  4014e3:	c3                   	ret
  4014e4:	e8 67 fb ff ff       	call   401050 <__stack_chk_fail@plt>
  4014e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000004014f0 <_start>:
  4014f0:	f3 0f 1e fa          	endbr64
  4014f4:	31 ed                	xor    %ebp,%ebp
  4014f6:	49 89 d1             	mov    %rdx,%r9
  4014f9:	5e                   	pop    %rsi
  4014fa:	48 89 e2             	mov    %rsp,%rdx
  4014fd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401501:	50                   	push   %rax
  401502:	54                   	push   %rsp
  401503:	45 31 c0             	xor    %r8d,%r8d
  401506:	31 c9                	xor    %ecx,%ecx
  401508:	48 c7 c7 b0 10 40 00 	mov    $0x4010b0,%rdi
  40150f:	ff 15 db 2a 00 00    	call   *0x2adb(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  401515:	f4                   	hlt
  401516:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401520 <_dl_relocate_static_pie>:
  401520:	f3 0f 1e fa          	endbr64
  401524:	c3                   	ret
  401525:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40152f:	90                   	nop

0000000000401530 <deregister_tm_clones>:
  401530:	b8 10 40 40 00       	mov    $0x404010,%eax
  401535:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  40153b:	74 13                	je     401550 <deregister_tm_clones+0x20>
  40153d:	b8 00 00 00 00       	mov    $0x0,%eax
  401542:	48 85 c0             	test   %rax,%rax
  401545:	74 09                	je     401550 <deregister_tm_clones+0x20>
  401547:	bf 10 40 40 00       	mov    $0x404010,%edi
  40154c:	ff e0                	jmp    *%rax
  40154e:	66 90                	xchg   %ax,%ax
  401550:	c3                   	ret
  401551:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40155c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401560 <register_tm_clones>:
  401560:	be 10 40 40 00       	mov    $0x404010,%esi
  401565:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  40156c:	48 89 f0             	mov    %rsi,%rax
  40156f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401573:	48 c1 f8 03          	sar    $0x3,%rax
  401577:	48 01 c6             	add    %rax,%rsi
  40157a:	48 d1 fe             	sar    %rsi
  40157d:	74 11                	je     401590 <register_tm_clones+0x30>
  40157f:	b8 00 00 00 00       	mov    $0x0,%eax
  401584:	48 85 c0             	test   %rax,%rax
  401587:	74 07                	je     401590 <register_tm_clones+0x30>
  401589:	bf 10 40 40 00       	mov    $0x404010,%edi
  40158e:	ff e0                	jmp    *%rax
  401590:	c3                   	ret
  401591:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40159c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004015a0 <__do_global_dtors_aux>:
  4015a0:	f3 0f 1e fa          	endbr64
  4015a4:	80 3d 65 2a 00 00 00 	cmpb   $0x0,0x2a65(%rip)        # 404010 <__TMC_END__>
  4015ab:	75 13                	jne    4015c0 <__do_global_dtors_aux+0x20>
  4015ad:	55                   	push   %rbp
  4015ae:	48 89 e5             	mov    %rsp,%rbp
  4015b1:	e8 7a ff ff ff       	call   401530 <deregister_tm_clones>
  4015b6:	c6 05 53 2a 00 00 01 	movb   $0x1,0x2a53(%rip)        # 404010 <__TMC_END__>
  4015bd:	5d                   	pop    %rbp
  4015be:	c3                   	ret
  4015bf:	90                   	nop
  4015c0:	c3                   	ret
  4015c1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4015cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004015d0 <frame_dummy>:
  4015d0:	f3 0f 1e fa          	endbr64
  4015d4:	eb 8a                	jmp    401560 <register_tm_clones>
  4015d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004015e0 <work>:
void * work(void * arg) {
  4015e0:	41 57                	push   %r15
  4015e2:	48 8d 35 1b 0a 00 00 	lea    0xa1b(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  4015e9:	41 56                	push   %r14
  4015eb:	41 55                	push   %r13
  4015ed:	41 54                	push   %r12
  4015ef:	55                   	push   %rbp
  4015f0:	53                   	push   %rbx
  4015f1:	48 89 fb             	mov    %rdi,%rbx
  4015f4:	48 83 ec 18          	sub    $0x18,%rsp
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  4015f8:	8b 87 0c 01 00 00    	mov    0x10c(%rdi),%eax
  int bucketstart = data->bucketstart;
  4015fe:	44 8b a7 40 01 00 00 	mov    0x140(%rdi),%r12d
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  401605:	8d 50 01             	lea    0x1(%rax),%edx
  401608:	31 c0                	xor    %eax,%eax
  int bucketlim = ((data->threadindex + 1) * data->buckets) ;
  40160a:	0f af 97 38 01 00 00 	imul   0x138(%rdi),%edx
  401611:	bf 01 00 00 00       	mov    $0x1,%edi
  401616:	e8 65 fa ff ff       	call   401080 <__printf_chk@plt>
  int * available = calloc(data->chunkslen + 1, sizeof(long));
  40161b:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
  401622:	be 08 00 00 00       	mov    $0x8,%esi
  401627:	48 8d 78 01          	lea    0x1(%rax),%rdi
  40162b:	e8 40 fa ff ff       	call   401070 <calloc@plt>
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  401630:	48 63 ab 10 01 00 00 	movslq 0x110(%rbx),%rbp
  401637:	be 04 00 00 00       	mov    $0x4,%esi
  int * available = calloc(data->chunkslen + 1, sizeof(long));
  40163c:	49 89 c6             	mov    %rax,%r14
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  40163f:	48 89 ef             	mov    %rbp,%rdi
  401642:	e8 29 fa ff ff       	call   401070 <calloc@plt>
  int * readywriters = calloc(data->threadsize, sizeof(int));
  401647:	be 04 00 00 00       	mov    $0x4,%esi
  40164c:	48 89 ef             	mov    %rbp,%rdi
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  40164f:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  int * readywriters = calloc(data->threadsize, sizeof(int));
  401654:	e8 17 fa ff ff       	call   401070 <calloc@plt>
  while (data->running == 1) {
  401659:	83 bb 04 01 00 00 01 	cmpl   $0x1,0x104(%rbx)
  401660:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
  data->workindex = bucketstart;
  401665:	44 89 a3 80 00 00 00 	mov    %r12d,0x80(%rbx)
  int * readywriters = calloc(data->threadsize, sizeof(int));
  40166c:	48 89 04 24          	mov    %rax,(%rsp)
  while (data->running == 1) {
  401670:	0f 85 a6 00 00 00    	jne    40171c <work+0x13c>
  401676:	4d 89 dd             	mov    %r11,%r13
  401679:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    if (data->threadindex == 0) {
  401680:	8b ab 0c 01 00 00    	mov    0x10c(%rbx),%ebp
  401686:	85 ed                	test   %ebp,%ebp
  401688:	0f 84 c2 00 00 00    	je     401750 <work+0x170>
      long mask = data->ready;
  40168e:	48 8b 43 28          	mov    0x28(%rbx),%rax
      if ((mask & PREP_WRITE_MASK) == PREP_WRITE_MASK) {
  401692:	49 89 c2             	mov    %rax,%r10
      data->prev = data->ready;
  401695:	48 89 83 78 01 00 00 	mov    %rax,0x178(%rbx)
      if ((mask & PREP_WRITE_MASK) == PREP_WRITE_MASK) {
  40169c:	41 83 e2 20          	and    $0x20,%r10d
      if ((mask & PREP_READ_MASK) == PREP_READ_MASK) {
  4016a0:	a8 10                	test   $0x10,%al
  4016a2:	0f 85 f0 02 00 00    	jne    401998 <work+0x3b8>
      if ((mask & PREP_WRITE_MASK) == PREP_WRITE_MASK) {
  4016a8:	4d 85 d2             	test   %r10,%r10
  4016ab:	74 62                	je     40170f <work+0x12f>
      if (data->publishstart < data->publishend) {
  4016ad:	48 8b 43 48          	mov    0x48(%rbx),%rax
  4016b1:	48 8b 4b 50          	mov    0x50(%rbx),%rcx
  4016b5:	bf 04 00 00 00       	mov    $0x4,%edi
  4016ba:	48 39 c8             	cmp    %rcx,%rax
  4016bd:	7d 50                	jge    40170f <work+0x12f>
        for (int x = data->publishstart ; x < data->publishend; x++) {
  4016bf:	89 c2                	mov    %eax,%edx
  4016c1:	48 98                	cltq
  4016c3:	48 39 c8             	cmp    %rcx,%rax
  4016c6:	7d 32                	jge    4016fa <work+0x11a>
          data->main->works[x].available = 1;
  4016c8:	48 8b 43 30          	mov    0x30(%rbx),%rax
  4016cc:	48 8b b0 18 01 00 00 	mov    0x118(%rax),%rsi
  4016d3:	48 63 c2             	movslq %edx,%rax
  4016d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4016e0:	48 c1 e0 08          	shl    $0x8,%rax
        for (int x = data->publishstart ; x < data->publishend; x++) {
  4016e4:	83 c2 01             	add    $0x1,%edx
          data->main->works[x].available = 1;
  4016e7:	c7 84 06 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rsi,%rax,1)
        for (int x = data->publishstart ; x < data->publishend; x++) {
  4016f2:	48 63 c2             	movslq %edx,%rax
  4016f5:	48 39 c8             	cmp    %rcx,%rax
  4016f8:	7c e6                	jl     4016e0 <work+0x100>
        data->writing->available = FREE;
  4016fa:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
  401701:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
        data->ready = newmask;
  40170b:	48 89 7b 28          	mov    %rdi,0x28(%rbx)
  while (data->running == 1) {
  40170f:	83 bb 04 01 00 00 01 	cmpl   $0x1,0x104(%rbx)
  401716:	0f 84 64 ff ff ff    	je     401680 <work+0xa0>
  40171c:	8b 93 0c 01 00 00    	mov    0x10c(%rbx),%edx
  401722:	48 8d 35 e9 08 00 00 	lea    0x8e9(%rip),%rsi        # 402012 <_IO_stdin_used+0x12>
  401729:	bf 01 00 00 00       	mov    $0x1,%edi
  40172e:	31 c0                	xor    %eax,%eax
  401730:	e8 4b f9 ff ff       	call   401080 <__printf_chk@plt>
}
  401735:	48 83 c4 18          	add    $0x18,%rsp
  401739:	31 c0                	xor    %eax,%eax
  40173b:	5b                   	pop    %rbx
  40173c:	5d                   	pop    %rbp
  40173d:	41 5c                	pop    %r12
  40173f:	41 5d                	pop    %r13
  401741:	41 5e                	pop    %r14
  401743:	41 5f                	pop    %r15
  401745:	c3                   	ret
  401746:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401750:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
  401757:	48 8d 48 01          	lea    0x1(%rax),%rcx
  40175b:	48 85 c9             	test   %rcx,%rcx
  40175e:	7e af                	jle    40170f <work+0x12f>
        if (data->freelist[x].available == FREE ) {
  401760:	48 8b bb 48 01 00 00 	mov    0x148(%rbx),%rdi
      for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401767:	31 d2                	xor    %edx,%edx
    int availableidx = 0;
  401769:	45 31 ff             	xor    %r15d,%r15d
  40176c:	31 c0                	xor    %eax,%eax
  40176e:	66 90                	xchg   %ax,%ax
        if (data->freelist[x].available == FREE ) {
  401770:	48 c1 e0 08          	shl    $0x8,%rax
  401774:	83 bc 07 80 00 00 00 01 	cmpl   $0x1,0x80(%rdi,%rax,1)
  40177c:	75 0b                	jne    401789 <work+0x1a9>
         available[availableidx] = x;
  40177e:	49 63 c7             	movslq %r15d,%rax
         availableidx++;
  401781:	41 83 c7 01          	add    $0x1,%r15d
         available[availableidx] = x;
  401785:	41 89 14 86          	mov    %edx,(%r14,%rax,4)
      for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401789:	83 c2 01             	add    $0x1,%edx
  40178c:	48 63 c2             	movslq %edx,%rax
  40178f:	48 39 c8             	cmp    %rcx,%rax
  401792:	7c dc                	jl     401770 <work+0x190>
      if (availableidx == 0) {
  401794:	45 85 ff             	test   %r15d,%r15d
  401797:	0f 84 72 ff ff ff    	je     40170f <work+0x12f>
  for (int x = 1; x < data->threadsize ; x++) {
  40179d:	44 8b 93 10 01 00 00 	mov    0x110(%rbx),%r10d
  4017a4:	41 83 fa 01          	cmp    $0x1,%r10d
  4017a8:	0f 8e a9 01 00 00    	jle    401957 <work+0x377>
  4017ae:	41 8d 52 fe          	lea    -0x2(%r10),%edx
    long mask = data->threads[x].ready;
  4017b2:	48 8b 73 38          	mov    0x38(%rbx),%rsi
  4017b6:	48 8d 14 52          	lea    (%rdx,%rdx,2),%rdx
  4017ba:	48 c1 e2 07          	shl    $0x7,%rdx
  4017be:	48 8d 86 f0 02 00 00 	lea    0x2f0(%rsi),%rax
  4017c5:	48 8d 94 16 70 04 00 00 	lea    0x470(%rsi,%rdx,1),%rdx
  4017cd:	0f 1f 00             	nopl   (%rax)
        data->threads[x].newmask = 0;
  4017d0:	48 c7 00 00 00 00 00 	movq   $0x0,(%rax)
  for (int x = 1; x < data->threadsize ; x++) {
  4017d7:	48 05 80 01 00 00    	add    $0x180,%rax
  4017dd:	48 39 c2             	cmp    %rax,%rdx
  4017e0:	75 ee                	jne    4017d0 <work+0x1f0>
    writers = 0;
  4017e2:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
  for (int x = 1; x < data->threadsize ; x++) {
  4017e7:	b8 01 00 00 00       	mov    $0x1,%eax
    readers = 0;
  4017ec:	45 31 c9             	xor    %r9d,%r9d
    writers = 0;
  4017ef:	45 31 c0             	xor    %r8d,%r8d
  4017f2:	48 8d 8e a8 01 00 00 	lea    0x1a8(%rsi),%rcx
  4017f9:	48 8b 34 24          	mov    (%rsp),%rsi
  4017fd:	0f 1f 00             	nopl   (%rax)
    long mask = data->threads[x].ready;
  401800:	48 8b 11             	mov    (%rcx),%rdx
        if ((data->threads[x].ready & WRITE_MASK) == WRITE_MASK || data->threads[x].ready == 0) {
  401803:	48 85 d2             	test   %rdx,%rdx
  401806:	41 0f 94 c3          	sete   %r11b
  40180a:	f6 c2 04             	test   $0x4,%dl
  40180d:	75 05                	jne    401814 <work+0x234>
  40180f:	45 84 db             	test   %r11b,%r11b
  401812:	74 0b                	je     40181f <work+0x23f>
          readywriters[writers++] = x;
  401814:	4d 63 e0             	movslq %r8d,%r12
  401817:	41 83 c0 01          	add    $0x1,%r8d
  40181b:	42 89 04 a6          	mov    %eax,(%rsi,%r12,4)
    if ((data->threads[x].ready & READ_MASK) == READ_MASK || data->threads[x].ready == 0) {
  40181f:	83 e2 08             	and    $0x8,%edx
  401822:	75 05                	jne    401829 <work+0x249>
  401824:	45 84 db             	test   %r11b,%r11b
  401827:	74 0c                	je     401835 <work+0x255>
      readyreaders[readers++] = x;
  401829:	49 63 d1             	movslq %r9d,%rdx
  40182c:	41 83 c1 01          	add    $0x1,%r9d
  401830:	41 89 44 95 00       	mov    %eax,0x0(%r13,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  401835:	83 c0 01             	add    $0x1,%eax
  401838:	48 81 c1 80 01 00 00 	add    $0x180,%rcx
  40183f:	41 39 c2             	cmp    %eax,%r10d
  401842:	75 bc                	jne    401800 <work+0x220>
        for (int x = 0; x < readers ; x++) {
  401844:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
  401849:	45 85 c9             	test   %r9d,%r9d
  40184c:	0f 8e 1e 02 00 00    	jle    401a70 <work+0x490>
  401852:	45 8d 59 ff          	lea    -0x1(%r9),%r11d
  401856:	44 89 54 24 08       	mov    %r10d,0x8(%rsp)
  40185b:	45 89 f9             	mov    %r15d,%r9d
  40185e:	31 c9                	xor    %ecx,%ecx
  401860:	eb 13                	jmp    401875 <work+0x295>
  401862:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (assignedchunk == availableidx) {
  401868:	48 83 c1 01          	add    $0x1,%rcx
  40186c:	49 39 c9             	cmp    %rcx,%r9
  40186f:	0f 84 d3 01 00 00    	je     401a48 <work+0x468>
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401875:	49 63 14 8e          	movslq (%r14,%rcx,4),%rdx
          int thread = readyreaders[x];
  401879:	49 63 44 8d 00       	movslq 0x0(%r13,%rcx,4),%rax
  40187e:	44 8d 61 01          	lea    0x1(%rcx),%r12d
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401882:	48 c1 e2 08          	shl    $0x8,%rdx
          int thread = readyreaders[x];
  401886:	49 89 c2             	mov    %rax,%r10
          data->threads[thread].reading = chunk;
  401889:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  40188d:	48 01 fa             	add    %rdi,%rdx
          data->threads[thread].reading = chunk;
  401890:	48 c1 e0 07          	shl    $0x7,%rax
          long start = chunk->start;
  401894:	66 0f 6f 02          	movdqa (%rdx),%xmm0
          data->threads[thread].reading = chunk;
  401898:	48 01 f0             	add    %rsi,%rax
          chunk->available = READING;
  40189b:	c7 82 80 00 00 00 02 00 00 00 	movl   $0x2,0x80(%rdx)
          data->threads[thread].reading = chunk;
  4018a5:	48 89 90 50 01 00 00 	mov    %rdx,0x150(%rax)
          chunk->owner = thread;
  4018ac:	44 89 92 84 00 00 00 	mov    %r10d,0x84(%rdx)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  4018b3:	48 83 88 70 01 00 00 10 	orq    $0x10,0x170(%rax)
          long start = chunk->start;
  4018bb:	0f 11 40 18          	movups %xmm0,0x18(%rax)
        for (int x = 0; x < readers ; x++) {
  4018bf:	49 39 cb             	cmp    %rcx,%r11
  4018c2:	75 a4                	jne    401868 <work+0x288>
  4018c4:	44 8b 54 24 08       	mov    0x8(%rsp),%r10d
   for (int x = 0; x < writers ; x++) {
  4018c9:	45 85 c0             	test   %r8d,%r8d
  4018cc:	0f 8e 92 00 00 00    	jle    401964 <work+0x384>
                if (assignedchunk  == availableidx) {
  4018d2:	45 39 e7             	cmp    %r12d,%r15d
  4018d5:	0f 84 45 01 00 00    	je     401a20 <work+0x440>
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  4018db:	48 8b bb 48 01 00 00 	mov    0x148(%rbx),%rdi
          data->threads[thread].writing = chunk;
  4018e2:	48 8b 73 38          	mov    0x38(%rbx),%rsi
  4018e6:	4c 8b 0c 24          	mov    (%rsp),%r9
      int assignedchunk = 0;
  4018ea:	31 c9                	xor    %ecx,%ecx
  4018ec:	eb 0f                	jmp    4018fd <work+0x31d>
  4018ee:	66 90                	xchg   %ax,%ax
                if (assignedchunk  == availableidx) {
  4018f0:	49 83 c1 04          	add    $0x4,%r9
  4018f4:	45 39 e7             	cmp    %r12d,%r15d
  4018f7:	0f 84 23 01 00 00    	je     401a20 <work+0x440>
          int thread = readywriters[x];
  4018fd:	49 63 c4             	movslq %r12d,%rax
  401900:	45 8b 11             	mov    (%r9),%r10d
   for (int x = 0; x < writers ; x++) {
  401903:	83 c1 01             	add    $0x1,%ecx
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401906:	41 83 c4 01          	add    $0x1,%r12d
  40190a:	49 63 14 86          	movslq (%r14,%rax,4),%rdx
          data->threads[thread].writing = chunk;
  40190e:	49 63 c2             	movslq %r10d,%rax
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401911:	48 c1 e2 08          	shl    $0x8,%rdx
          data->threads[thread].writing = chunk;
  401915:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401919:	48 01 fa             	add    %rdi,%rdx
          data->threads[thread].writing = chunk;
  40191c:	48 c1 e0 07          	shl    $0x7,%rax
          long start = chunk->start;
  401920:	66 0f 6f 0a          	movdqa (%rdx),%xmm1
          data->threads[thread].writing = chunk;
  401924:	48 01 f0             	add    %rsi,%rax
      chunk->available = WRITING;
  401927:	c7 82 80 00 00 00 03 00 00 00 	movl   $0x3,0x80(%rdx)
          data->threads[thread].writing = chunk;
  401931:	48 89 90 58 01 00 00 	mov    %rdx,0x158(%rax)
          chunk->owner = thread;
  401938:	44 89 92 84 00 00 00 	mov    %r10d,0x84(%rdx)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  40193f:	48 83 88 70 01 00 00 20 	orq    $0x20,0x170(%rax)
          long start = chunk->start;
  401947:	0f 11 48 48          	movups %xmm1,0x48(%rax)
   for (int x = 0; x < writers ; x++) {
  40194b:	41 39 c8             	cmp    %ecx,%r8d
  40194e:	7f a0                	jg     4018f0 <work+0x310>
      for (int x = 0; x < data->threadsize ; x++) {
  401950:	44 8b 93 10 01 00 00 	mov    0x110(%rbx),%r10d
  401957:	45 85 d2             	test   %r10d,%r10d
  40195a:	0f 8e af fd ff ff    	jle    40170f <work+0x12f>
  401960:	48 8b 73 38          	mov    0x38(%rbx),%rsi
  401964:	48 83 c6 28          	add    $0x28,%rsi
  401968:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        if (data->threads[x].newmask != 0) {
  401970:	48 8b 86 48 01 00 00 	mov    0x148(%rsi),%rax
  401977:	48 85 c0             	test   %rax,%rax
  40197a:	74 03                	je     40197f <work+0x39f>
          data->threads[x].ready = data->threads[x].newmask;
  40197c:	48 89 06             	mov    %rax,(%rsi)
      for (int x = 0; x < data->threadsize ; x++) {
  40197f:	83 c5 01             	add    $0x1,%ebp
  401982:	48 81 c6 80 01 00 00 	add    $0x180,%rsi
  401989:	41 39 ea             	cmp    %ebp,%r10d
  40198c:	7f e2                	jg     401970 <work+0x390>
  40198e:	e9 7c fd ff ff       	jmp    40170f <work+0x12f>
  401993:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int x = data->start; x < data->end; x++) {
  401998:	48 8b 43 18          	mov    0x18(%rbx),%rax
  40199c:	48 8b 7b 20          	mov    0x20(%rbx),%rdi
  4019a0:	89 c6                	mov    %eax,%esi
  4019a2:	48 98                	cltq
  4019a4:	48 39 c7             	cmp    %rax,%rdi
  4019a7:	7e 49                	jle    4019f2 <work+0x412>
        data->main->works[x].available = 0;
  4019a9:	48 8b 43 30          	mov    0x30(%rbx),%rax
  4019ad:	4c 8b 88 18 01 00 00 	mov    0x118(%rax),%r9
  4019b4:	48 8b 43 58          	mov    0x58(%rbx),%rax
  4019b8:	48 8d 48 01          	lea    0x1(%rax),%rcx
  4019bc:	48 63 c6             	movslq %esi,%rax
  4019bf:	90                   	nop
  4019c0:	48 c1 e0 08          	shl    $0x8,%rax
      for (int x = data->start; x < data->end; x++) {
  4019c4:	83 c6 01             	add    $0x1,%esi
        data->freq++;
  4019c7:	49 89 c8             	mov    %rcx,%r8
      for (int x = data->start; x < data->end; x++) {
  4019ca:	48 83 c1 01          	add    $0x1,%rcx
        data->main->works[x].available = 0;
  4019ce:	49 8d 14 01          	lea    (%r9,%rax,1),%rdx
      for (int x = data->start; x < data->end; x++) {
  4019d2:	48 63 c6             	movslq %esi,%rax
        data->main->works[x].available = 0;
  4019d5:	c7 82 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rdx)
      for (int x = data->start; x < data->end; x++) {
  4019df:	48 39 f8             	cmp    %rdi,%rax
  4019e2:	7c dc                	jl     4019c0 <work+0x3e0>
  4019e4:	4c 89 43 58          	mov    %r8,0x58(%rbx)
  4019e8:	c7 82 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rdx)
        data->reading->available = FREE;
  4019f2:	48 8b 83 50 01 00 00 	mov    0x150(%rbx),%rax
  4019f9:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
      if ((mask & PREP_WRITE_MASK) == PREP_WRITE_MASK) {
  401a03:	4d 85 d2             	test   %r10,%r10
  401a06:	74 0d                	je     401a15 <work+0x435>
      if (data->publishstart < data->publishend) {
  401a08:	48 8b 43 48          	mov    0x48(%rbx),%rax
  401a0c:	48 8b 4b 50          	mov    0x50(%rbx),%rcx
  401a10:	48 39 c8             	cmp    %rcx,%rax
  401a13:	7c 6c                	jl     401a81 <work+0x4a1>
        newmask = newmask | READ_MASK;
  401a15:	bf 08 00 00 00       	mov    $0x8,%edi
  401a1a:	e9 ec fc ff ff       	jmp    40170b <work+0x12b>
  401a1f:	90                   	nop
  401a20:	44 89 f9             	mov    %r15d,%ecx
  401a23:	44 89 e2             	mov    %r12d,%edx
  401a26:	48 8d 35 83 06 00 00 	lea    0x683(%rip),%rsi        # 4020b0 <_IO_stdin_used+0xb0>
  401a2d:	31 c0                	xor    %eax,%eax
  401a2f:	bf 01 00 00 00       	mov    $0x1,%edi
  401a34:	e8 47 f6 ff ff       	call   401080 <__printf_chk@plt>
      for (int x = 0; x < data->threadsize ; x++) {
  401a39:	44 8b 93 10 01 00 00 	mov    0x110(%rbx),%r10d
  401a40:	e9 12 ff ff ff       	jmp    401957 <work+0x377>
  401a45:	0f 1f 00             	nopl   (%rax)
  401a48:	48 8d 3d d3 05 00 00 	lea    0x5d3(%rip),%rdi        # 402022 <_IO_stdin_used+0x22>
  401a4f:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
  401a54:	e8 e7 f5 ff ff       	call   401040 <puts@plt>
   for (int x = 0; x < writers ; x++) {
  401a59:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
  401a5e:	45 85 c0             	test   %r8d,%r8d
  401a61:	0f 8f 6b fe ff ff    	jg     4018d2 <work+0x2f2>
  401a67:	e9 e4 fe ff ff       	jmp    401950 <work+0x370>
  401a6c:	0f 1f 40 00          	nopl   0x0(%rax)
  401a70:	45 85 c0             	test   %r8d,%r8d
  401a73:	0f 8e eb fe ff ff    	jle    401964 <work+0x384>
      int assignedchunk = 0;
  401a79:	45 31 e4             	xor    %r12d,%r12d
  401a7c:	e9 65 fe ff ff       	jmp    4018e6 <work+0x306>
      if (data->publishstart < data->publishend) {
  401a81:	bf 0c 00 00 00       	mov    $0xc,%edi
  401a86:	e9 34 fc ff ff       	jmp    4016bf <work+0xdf>

Disassembly of section .fini:

0000000000401a8c <_fini>:
  401a8c:	f3 0f 1e fa          	endbr64
  401a90:	48 83 ec 08          	sub    $0x8,%rsp
  401a94:	48 83 c4 08          	add    $0x8,%rsp
  401a98:	c3                   	ret
