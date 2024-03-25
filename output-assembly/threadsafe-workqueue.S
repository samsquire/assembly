
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
  4010bc:	48 8d 35 5f 0f 00 00 	lea    0xf5f(%rip),%rsi        # 402022 <_IO_stdin_used+0x22>
  4010c3:	41 56                	push   %r14
  4010c5:	4c 8d 35 bc 0f 00 00 	lea    0xfbc(%rip),%r14        # 402088 <_IO_stdin_used+0x88>
  4010cc:	41 55                	push   %r13
  printf("Starting %d workers\n", threadsize);
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  struct Work *works = calloc(worksize, sizeof(struct Work));
  long offset = 0;
  4010ce:	45 31 ed             	xor    %r13d,%r13d
int main(int argc, char **argv) {
  4010d1:	41 54                	push   %r12
  4010d3:	55                   	push   %rbp
  4010d4:	53                   	push   %rbx
  4010d5:	48 83 ec 78          	sub    $0x78,%rsp
  4010d9:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4010e2:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  4010e7:	31 c0                	xor    %eax,%eax
  4010e9:	e8 92 ff ff ff       	call   401080 <__printf_chk@plt>
  4010ee:	ba 04 00 00 00       	mov    $0x4,%edx
  4010f3:	48 8d 35 3a 0f 00 00 	lea    0xf3a(%rip),%rsi        # 402034 <_IO_stdin_used+0x34>
  4010fa:	31 c0                	xor    %eax,%eax
  4010fc:	bf 01 00 00 00       	mov    $0x1,%edi
  401101:	e8 7a ff ff ff       	call   401080 <__printf_chk@plt>
  401106:	ba 20 00 00 00       	mov    $0x20,%edx
  40110b:	48 8d 35 1e 0f 00 00 	lea    0xf1e(%rip),%rsi        # 402030 <_IO_stdin_used+0x30>
  401112:	31 c0                	xor    %eax,%eax
  401114:	bf 01 00 00 00       	mov    $0x1,%edi
  401119:	e8 62 ff ff ff       	call   401080 <__printf_chk@plt>
  40111e:	ba 07 00 00 00       	mov    $0x7,%edx
  401123:	48 8d 35 19 0f 00 00 	lea    0xf19(%rip),%rsi        # 402043 <_IO_stdin_used+0x43>
  40112a:	31 c0                	xor    %eax,%eax
  40112c:	bf 01 00 00 00       	mov    $0x1,%edi
  401131:	e8 4a ff ff ff       	call   401080 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401136:	be 08 00 00 00       	mov    $0x8,%esi
  40113b:	bf 07 00 00 00       	mov    $0x7,%edi
  401140:	e8 2b ff ff ff       	call   401070 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401145:	be 38 00 00 00       	mov    $0x38,%esi
  40114a:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40114f:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401154:	e8 17 ff ff ff       	call   401070 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401159:	be 80 0a 00 00       	mov    $0xa80,%esi
  40115e:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401163:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401168:	e8 03 ff ff ff       	call   401070 <calloc@plt>
  struct Work *works = calloc(worksize, sizeof(struct Work));
  40116d:	be 00 01 00 00       	mov    $0x100,%esi
  401172:	bf 0e 00 00 00       	mov    $0xe,%edi
  401177:	66 48 0f 6e e8       	movq   %rax,%xmm5
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40117c:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  401181:	66 0f 6c ed          	punpcklqdq %xmm5,%xmm5
  401185:	0f 29 2c 24          	movaps %xmm5,(%rsp)
  struct Work *works = calloc(worksize, sizeof(struct Work));
  401189:	e8 e2 fe ff ff       	call   401070 <calloc@plt>
  long chunksize = worksize /((threadsize - 1) * 2);
  long chunkslen = (threadsize - 1) * 2;
  int chunkindex = 0;
  struct Chunk *freelist = calloc(chunkslen, sizeof(struct Chunk));
  40118e:	be 20 00 00 00       	mov    $0x20,%esi
  401193:	bf 0c 00 00 00       	mov    $0xc,%edi
  struct Work *works = calloc(worksize, sizeof(struct Work));
  401198:	49 89 c4             	mov    %rax,%r12
  struct Chunk *freelist = calloc(chunkslen, sizeof(struct Chunk));
  40119b:	e8 d0 fe ff ff       	call   401070 <calloc@plt>
  4011a0:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
          for (int x = 0; x < chunkslen; x++) {
  4011a5:	49 89 c7             	mov    %rax,%r15
  4011a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  4011b0:	44 89 ed             	mov    %r13d,%ebp
        
          
          long start = offset;
          
          
          long end = start + chunksize;
  4011b3:	4c 89 eb             	mov    %r13,%rbx
  4011b6:	49 83 c5 01          	add    $0x1,%r13
  4011ba:	4c 89 f6             	mov    %r14,%rsi
  4011bd:	4d 89 e8             	mov    %r13,%r8
  4011c0:	48 89 d9             	mov    %rbx,%rcx
  4011c3:	89 ea                	mov    %ebp,%edx
  4011c5:	bf 01 00 00 00       	mov    $0x1,%edi
  4011ca:	31 c0                	xor    %eax,%eax
          for (int x = 0; x < chunkslen; x++) {
  4011cc:	49 83 c7 20          	add    $0x20,%r15
  4011d0:	e8 ab fe ff ff       	call   401080 <__printf_chk@plt>
          
          printf("writer giving %d between %ld and %ld\n", x, start, end);
          offset += chunksize;
        
         freelist[chunkindex].index = chunkindex;   freelist[chunkindex].available = FREE;
            freelist[chunkindex].start = start;
  4011d5:	66 48 0f 6e c3       	movq   %rbx,%xmm0
  4011da:	66 49 0f 6e cd       	movq   %r13,%xmm1
         freelist[chunkindex].index = chunkindex;   freelist[chunkindex].available = FREE;
  4011df:	41 89 6f f8          	mov    %ebp,-0x8(%r15)
            freelist[chunkindex].start = start;
  4011e3:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
         freelist[chunkindex].index = chunkindex;   freelist[chunkindex].available = FREE;
  4011e7:	41 c7 47 f0 01 00 00 00 	movl   $0x1,-0x10(%r15)
            freelist[chunkindex].start = start;
  4011ef:	41 0f 11 47 e0       	movups %xmm0,-0x20(%r15)
          for (int x = 0; x < chunkslen; x++) {
  4011f4:	49 83 fd 0c          	cmp    $0xc,%r13
  4011f8:	75 b6                	jne    4011b0 <main+0x100>
  4011fa:	ba 0c 00 00 00       	mov    $0xc,%edx
  4011ff:	bf 01 00 00 00       	mov    $0x1,%edi
  401204:	31 c0                	xor    %eax,%eax
  for (int i = 0; i < worksize; i++) {
    works[i].taskindex = 2;
    works[i].available = 1;
    
  }
  int cpu = 0;
  401206:	45 31 ed             	xor    %r13d,%r13d
  401209:	48 8d 35 48 0e 00 00 	lea    0xe48(%rip),%rsi        # 402058 <_IO_stdin_used+0x58>
  401210:	4c 8d 3d 99 0e 00 00 	lea    0xe99(%rip),%r15        # 4020b0 <_IO_stdin_used+0xb0>
  401217:	e8 64 fe ff ff       	call   401080 <__printf_chk@plt>
  data[0].works = works;
  40121c:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
  401221:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
    works[i].taskindex = 2;
  401226:	41 c7 04 24 02 00 00 00 	movl   $0x2,(%r12)
    works[i].available = 1;
  40122e:	41 c7 84 24 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r12)
    works[i].taskindex = 2;
  40123a:	48 8b 1d 97 0e 00 00 	mov    0xe97(%rip),%rbx        # 4020d8 <_IO_stdin_used+0xd8>
  401241:	41 c7 84 24 00 01 00 00 02 00 00 00 	movl   $0x2,0x100(%r12)
    works[i].available = 1;
  40124d:	41 c7 84 24 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r12)
    works[i].taskindex = 2;
  401259:	41 c7 84 24 00 02 00 00 02 00 00 00 	movl   $0x2,0x200(%r12)
    works[i].available = 1;
  401265:	41 c7 84 24 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%r12)
    works[i].taskindex = 2;
  401271:	41 c7 84 24 00 03 00 00 02 00 00 00 	movl   $0x2,0x300(%r12)
    works[i].available = 1;
  40127d:	41 c7 84 24 80 03 00 00 01 00 00 00 	movl   $0x1,0x380(%r12)
    works[i].taskindex = 2;
  401289:	41 c7 84 24 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%r12)
    works[i].available = 1;
  401295:	41 c7 84 24 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r12)
    works[i].taskindex = 2;
  4012a1:	41 c7 84 24 00 05 00 00 02 00 00 00 	movl   $0x2,0x500(%r12)
    works[i].available = 1;
  4012ad:	41 c7 84 24 80 05 00 00 01 00 00 00 	movl   $0x1,0x580(%r12)
    works[i].taskindex = 2;
  4012b9:	41 c7 84 24 00 06 00 00 02 00 00 00 	movl   $0x2,0x600(%r12)
    works[i].available = 1;
  4012c5:	41 c7 84 24 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r12)
    works[i].taskindex = 2;
  4012d1:	41 c7 84 24 00 07 00 00 02 00 00 00 	movl   $0x2,0x700(%r12)
    works[i].available = 1;
  4012dd:	41 c7 84 24 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r12)
    works[i].taskindex = 2;
  4012e9:	41 c7 84 24 00 08 00 00 02 00 00 00 	movl   $0x2,0x800(%r12)
    works[i].available = 1;
  4012f5:	41 c7 84 24 80 08 00 00 01 00 00 00 	movl   $0x1,0x880(%r12)
    works[i].taskindex = 2;
  401301:	41 c7 84 24 00 09 00 00 02 00 00 00 	movl   $0x2,0x900(%r12)
    works[i].available = 1;
  40130d:	41 c7 84 24 80 09 00 00 01 00 00 00 	movl   $0x1,0x980(%r12)
    works[i].taskindex = 2;
  401319:	41 c7 84 24 00 0a 00 00 02 00 00 00 	movl   $0x2,0xa00(%r12)
    works[i].available = 1;
  401325:	41 c7 84 24 80 0a 00 00 01 00 00 00 	movl   $0x1,0xa80(%r12)
    works[i].taskindex = 2;
  401331:	41 c7 84 24 00 0b 00 00 02 00 00 00 	movl   $0x2,0xb00(%r12)
    works[i].available = 1;
  40133d:	41 c7 84 24 80 0b 00 00 01 00 00 00 	movl   $0x1,0xb80(%r12)
    works[i].taskindex = 2;
  401349:	41 c7 84 24 00 0c 00 00 02 00 00 00 	movl   $0x2,0xc00(%r12)
    works[i].available = 1;
  401355:	41 c7 84 24 80 0c 00 00 01 00 00 00 	movl   $0x1,0xc80(%r12)
    works[i].taskindex = 2;
  401361:	41 c7 84 24 00 0d 00 00 02 00 00 00 	movl   $0x2,0xd00(%r12)
    works[i].available = 1;
  40136d:	41 c7 84 24 80 0d 00 00 01 00 00 00 	movl   $0x1,0xd80(%r12)
  data[0].works = works;
  401379:	4d 89 a6 18 01 00 00 	mov    %r12,0x118(%r14)
  for (int x = 0; x < threadsize ; x++) {
  401380:	4c 89 74 24 28       	mov    %r14,0x28(%rsp)
  401385:	0f 1f 00             	nopl   (%rax)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401388:	45 89 ec             	mov    %r13d,%r12d
  40138b:	be 80 00 00 00       	mov    $0x80,%esi
    CPU_SET(cpu += 1, data[x].cpu_set);
  401390:	41 83 c5 01          	add    $0x1,%r13d
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401394:	bf 01 00 00 00       	mov    $0x1,%edi
  401399:	e8 d2 fc ff ff       	call   401070 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  40139e:	44 89 e9             	mov    %r13d,%ecx
  4013a1:	ba 01 00 00 00       	mov    $0x1,%edx
  4013a6:	4c 89 fe             	mov    %r15,%rsi
  4013a9:	48 d3 e2             	shl    %cl,%rdx
  4013ac:	48 09 10             	or     %rdx,(%rax)
  4013af:	44 89 e9             	mov    %r13d,%ecx
  4013b2:	44 89 e2             	mov    %r12d,%edx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4013b5:	49 89 86 20 01 00 00 	mov    %rax,0x120(%r14)
  4013bc:	bf 01 00 00 00       	mov    $0x1,%edi
  4013c1:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  4013c3:	49 81 c6 80 01 00 00 	add    $0x180,%r14
  4013ca:	e8 b1 fc ff ff       	call   401080 <__printf_chk@plt>
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].bucketstart = x * buckets ;
  4013cf:	43 8d 44 2d fe       	lea    -0x2(%r13,%r13,1),%eax
    data[x].worksize = worksize;
    data[x].ready = 0;
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].buckets = buckets;
    data[x].main = &data[0];
  4013d4:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
    data[x].threads = data;
    data[x].wantindex = -1;
    data[x].read = 0;
  4013d9:	66 0f 6f 1d ff 0c 00 00 	movdqa 0xcff(%rip),%xmm3        # 4020e0 <_IO_stdin_used+0xe0>
    data[x].bucketstart = x * buckets ;
  4013e1:	41 89 46 c0          	mov    %eax,-0x40(%r14)
    data[x].write = worksize;
    data[x].ready = 1;
    data[x].freelist = freelist;
    data[x].chunksize = chunksize;
    data[x].chunkslen = chunkslen;
  4013e5:	66 0f 6f 25 03 0d 00 00 	movdqa 0xd03(%rip),%xmm4        # 4020f0 <_IO_stdin_used+0xf0>
    data[x].buckets = buckets;
  4013ed:	48 8b 05 dc 0c 00 00 	mov    0xcdc(%rip),%rax        # 4020d0 <_IO_stdin_used+0xd0>
    data[x].loglevel = debug;
  4013f4:	41 c7 46 ac 00 00 00 00 	movl   $0x0,-0x54(%r14)
    data[x].threadindex = x;
  4013fc:	45 89 66 8c          	mov    %r12d,-0x74(%r14)
    data[x].worksize = worksize;
  401400:	41 c7 46 88 0e 00 00 00 	movl   $0xe,-0x78(%r14)
    data[x].threadsize = threadsize;
  401408:	41 c7 46 90 07 00 00 00 	movl   $0x7,-0x70(%r14)
    data[x].buckets = buckets;
  401410:	49 89 46 b8          	mov    %rax,-0x48(%r14)
    data[x].main = &data[0];
  401414:	41 0f 29 96 b0 fe ff ff 	movaps %xmm2,-0x150(%r14)
    data[x].wantindex = -1;
  40141c:	49 89 5e 80          	mov    %rbx,-0x80(%r14)
    data[x].read = 0;
  401420:	41 0f 29 9e 80 fe ff ff 	movaps %xmm3,-0x180(%r14)
    data[x].ready = 1;
  401428:	41 c7 86 a8 fe ff ff 01 00 00 00 	movl   $0x1,-0x158(%r14)
    data[x].freelist = freelist;
  401433:	49 89 6e c8          	mov    %rbp,-0x38(%r14)
    data[x].chunkslen = chunkslen;
  401437:	41 0f 29 66 e0       	movaps %xmm4,-0x20(%r14)
  for (int x = 0; x < threadsize ; x++) {
  40143c:	41 83 fd 07          	cmp    $0x7,%r13d
  401440:	0f 85 42 ff ff ff    	jne    401388 <main+0x2d8>
  401446:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
  40144b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  401450:	4c 8b 64 24 28       	mov    0x28(%rsp),%r12
  401455:	49 c7 c5 c0 16 40 00 	mov    $0x4016c0,%r13
  40145c:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
  401461:	4c 89 fd             	mov    %r15,%rbp
  401464:	4c 8d b0 80 0a 00 00 	lea    0xa80(%rax),%r14
  40146b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  401470:	4c 89 e1             	mov    %r12,%rcx
  401473:	4c 89 ff             	mov    %r15,%rdi
  401476:	4c 89 ea             	mov    %r13,%rdx
  401479:	48 89 de             	mov    %rbx,%rsi
  40147c:	e8 0f fc ff ff       	call   401090 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401481:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
  401489:	49 8b 3f             	mov    (%r15),%rdi
  40148c:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  401491:	49 81 c4 80 01 00 00 	add    $0x180,%r12
  401498:	49 83 c7 08          	add    $0x8,%r15
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  40149c:	e8 8f fb ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  4014a1:	4d 39 f4             	cmp    %r14,%r12
  4014a4:	75 ca                	jne    401470 <main+0x3c0>
  }
  
  struct timespec time = {
  4014a6:	66 0f 6f 05 52 0c 00 00 	movdqa 0xc52(%rip),%xmm0        # 402100 <_IO_stdin_used+0x100>
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  4014ae:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  4014b3:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  4014b8:	4c 8d 6c 24 38       	lea    0x38(%rsp),%r13
  struct timespec time = {
  4014bd:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  4014c2:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4014c6:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  4014cb:	e8 90 fb ff ff       	call   401060 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  4014d0:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  4014d5:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
  4014da:	c7 80 04 01 00 00 00 00 00 00 	movl   $0x0,0x104(%rax)
  4014e4:	49 83 c4 38          	add    $0x38,%r12
  4014e8:	c7 80 84 02 00 00 00 00 00 00 	movl   $0x0,0x284(%rax)
  4014f2:	c7 80 04 04 00 00 00 00 00 00 	movl   $0x0,0x404(%rax)
  4014fc:	c7 80 84 05 00 00 00 00 00 00 	movl   $0x0,0x584(%rax)
  401506:	c7 80 04 07 00 00 00 00 00 00 	movl   $0x0,0x704(%rax)
  401510:	c7 80 84 08 00 00 00 00 00 00 	movl   $0x0,0x884(%rax)
  40151a:	c7 80 04 0a 00 00 00 00 00 00 	movl   $0x0,0xa04(%rax)
  for (int x = 0; x < threadsize ; x++) {
  401524:	0f 1f 40 00          	nopl   0x0(%rax)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401528:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
  40152c:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  40152f:	48 83 c5 08          	add    $0x8,%rbp
    pthread_join(thread[x], &res);
  401533:	e8 68 fb ff ff       	call   4010a0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401538:	49 39 ec             	cmp    %rbp,%r12
  40153b:	75 eb                	jne    401528 <main+0x478>
  40153d:	48 8d 3d 20 0b 00 00 	lea    0xb20(%rip),%rdi        # 402064 <_IO_stdin_used+0x64>
  401544:	e8 f7 fa ff ff       	call   401040 <puts@plt>
  }
  printf("finished simulation.\n");
  long freq = 0;
  for (int x= 0; x < threadsize; x++) {
    freq += data[x].freq;
  401549:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  40154e:	bf 01 00 00 00       	mov    $0x1,%edi
  }
  printf("freq: %ld\n", freq / seconds);
  401553:	48 ba 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rdx
  40155d:	48 8d 35 15 0b 00 00 	lea    0xb15(%rip),%rsi        # 402079 <_IO_stdin_used+0x79>
    freq += data[x].freq;
  401564:	48 8b 88 d8 01 00 00 	mov    0x1d8(%rax),%rcx
  40156b:	48 03 88 58 03 00 00 	add    0x358(%rax),%rcx
  401572:	48 03 48 58          	add    0x58(%rax),%rcx
  401576:	48 03 88 d8 04 00 00 	add    0x4d8(%rax),%rcx
  40157d:	48 03 88 58 06 00 00 	add    0x658(%rax),%rcx
  401584:	48 03 88 d8 07 00 00 	add    0x7d8(%rax),%rcx
  40158b:	48 03 88 58 09 00 00 	add    0x958(%rax),%rcx
  printf("freq: %ld\n", freq / seconds);
  401592:	48 89 c8             	mov    %rcx,%rax
  401595:	48 c1 f9 3f          	sar    $0x3f,%rcx
  401599:	48 f7 ea             	imul   %rdx
  40159c:	31 c0                	xor    %eax,%eax
  40159e:	48 d1 fa             	sar    %rdx
  4015a1:	48 29 ca             	sub    %rcx,%rdx
  4015a4:	e8 d7 fa ff ff       	call   401080 <__printf_chk@plt>
  4015a9:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  4015ae:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4015b7:	75 11                	jne    4015ca <main+0x51a>
  4015b9:	48 83 c4 78          	add    $0x78,%rsp
  4015bd:	31 c0                	xor    %eax,%eax
  4015bf:	5b                   	pop    %rbx
  4015c0:	5d                   	pop    %rbp
  4015c1:	41 5c                	pop    %r12
  4015c3:	41 5d                	pop    %r13
  4015c5:	41 5e                	pop    %r14
  4015c7:	41 5f                	pop    %r15
  4015c9:	c3                   	ret
  4015ca:	e8 81 fa ff ff       	call   401050 <__stack_chk_fail@plt>
  4015cf:	90                   	nop

00000000004015d0 <_start>:
  4015d0:	f3 0f 1e fa          	endbr64
  4015d4:	31 ed                	xor    %ebp,%ebp
  4015d6:	49 89 d1             	mov    %rdx,%r9
  4015d9:	5e                   	pop    %rsi
  4015da:	48 89 e2             	mov    %rsp,%rdx
  4015dd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4015e1:	50                   	push   %rax
  4015e2:	54                   	push   %rsp
  4015e3:	45 31 c0             	xor    %r8d,%r8d
  4015e6:	31 c9                	xor    %ecx,%ecx
  4015e8:	48 c7 c7 b0 10 40 00 	mov    $0x4010b0,%rdi
  4015ef:	ff 15 fb 29 00 00    	call   *0x29fb(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  4015f5:	f4                   	hlt
  4015f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401600 <_dl_relocate_static_pie>:
  401600:	f3 0f 1e fa          	endbr64
  401604:	c3                   	ret
  401605:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40160f:	90                   	nop

0000000000401610 <deregister_tm_clones>:
  401610:	b8 10 40 40 00       	mov    $0x404010,%eax
  401615:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  40161b:	74 13                	je     401630 <deregister_tm_clones+0x20>
  40161d:	b8 00 00 00 00       	mov    $0x0,%eax
  401622:	48 85 c0             	test   %rax,%rax
  401625:	74 09                	je     401630 <deregister_tm_clones+0x20>
  401627:	bf 10 40 40 00       	mov    $0x404010,%edi
  40162c:	ff e0                	jmp    *%rax
  40162e:	66 90                	xchg   %ax,%ax
  401630:	c3                   	ret
  401631:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40163c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401640 <register_tm_clones>:
  401640:	be 10 40 40 00       	mov    $0x404010,%esi
  401645:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  40164c:	48 89 f0             	mov    %rsi,%rax
  40164f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401653:	48 c1 f8 03          	sar    $0x3,%rax
  401657:	48 01 c6             	add    %rax,%rsi
  40165a:	48 d1 fe             	sar    %rsi
  40165d:	74 11                	je     401670 <register_tm_clones+0x30>
  40165f:	b8 00 00 00 00       	mov    $0x0,%eax
  401664:	48 85 c0             	test   %rax,%rax
  401667:	74 07                	je     401670 <register_tm_clones+0x30>
  401669:	bf 10 40 40 00       	mov    $0x404010,%edi
  40166e:	ff e0                	jmp    *%rax
  401670:	c3                   	ret
  401671:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40167c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401680 <__do_global_dtors_aux>:
  401680:	f3 0f 1e fa          	endbr64
  401684:	80 3d 85 29 00 00 00 	cmpb   $0x0,0x2985(%rip)        # 404010 <__TMC_END__>
  40168b:	75 13                	jne    4016a0 <__do_global_dtors_aux+0x20>
  40168d:	55                   	push   %rbp
  40168e:	48 89 e5             	mov    %rsp,%rbp
  401691:	e8 7a ff ff ff       	call   401610 <deregister_tm_clones>
  401696:	c6 05 73 29 00 00 01 	movb   $0x1,0x2973(%rip)        # 404010 <__TMC_END__>
  40169d:	5d                   	pop    %rbp
  40169e:	c3                   	ret
  40169f:	90                   	nop
  4016a0:	c3                   	ret
  4016a1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4016ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004016b0 <frame_dummy>:
  4016b0:	f3 0f 1e fa          	endbr64
  4016b4:	eb 8a                	jmp    401640 <register_tm_clones>
  4016b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004016c0 <work>:
void * work(void * arg) {
  4016c0:	41 57                	push   %r15
  4016c2:	48 8d 35 3b 09 00 00 	lea    0x93b(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  4016c9:	41 56                	push   %r14
  4016cb:	41 55                	push   %r13
  4016cd:	41 54                	push   %r12
  4016cf:	55                   	push   %rbp
  4016d0:	53                   	push   %rbx
  4016d1:	48 89 fb             	mov    %rdi,%rbx
  4016d4:	48 83 ec 18          	sub    $0x18,%rsp
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  4016d8:	8b 87 0c 01 00 00    	mov    0x10c(%rdi),%eax
  int bucketstart = data->bucketstart;
  4016de:	44 8b af 40 01 00 00 	mov    0x140(%rdi),%r13d
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  4016e5:	8d 50 01             	lea    0x1(%rax),%edx
  4016e8:	31 c0                	xor    %eax,%eax
  int bucketlim = ((data->threadindex + 1) * data->buckets) ;
  4016ea:	0f af 97 38 01 00 00 	imul   0x138(%rdi),%edx
  4016f1:	bf 01 00 00 00       	mov    $0x1,%edi
  4016f6:	e8 85 f9 ff ff       	call   401080 <__printf_chk@plt>
  int * available = calloc(data->chunkslen, sizeof(long));
  4016fb:	48 8b bb 60 01 00 00 	mov    0x160(%rbx),%rdi
  401702:	be 08 00 00 00       	mov    $0x8,%esi
  401707:	e8 64 f9 ff ff       	call   401070 <calloc@plt>
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  40170c:	4c 63 a3 10 01 00 00 	movslq 0x110(%rbx),%r12
  401713:	be 04 00 00 00       	mov    $0x4,%esi
  int * available = calloc(data->chunkslen, sizeof(long));
  401718:	48 89 c5             	mov    %rax,%rbp
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  40171b:	4c 89 e7             	mov    %r12,%rdi
  40171e:	e8 4d f9 ff ff       	call   401070 <calloc@plt>
  int * readywriters = calloc(data->threadsize, sizeof(int));
  401723:	be 04 00 00 00       	mov    $0x4,%esi
  401728:	4c 89 e7             	mov    %r12,%rdi
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  40172b:	49 89 c6             	mov    %rax,%r14
  int * readywriters = calloc(data->threadsize, sizeof(int));
  40172e:	e8 3d f9 ff ff       	call   401070 <calloc@plt>
  while (data->running == 1) {
  401733:	83 bb 04 01 00 00 01 	cmpl   $0x1,0x104(%rbx)
  data->workindex = bucketstart;
  40173a:	44 89 ab 80 00 00 00 	mov    %r13d,0x80(%rbx)
  while (data->running == 1) {
  401741:	0f 85 91 00 00 00    	jne    4017d8 <work+0x118>
  401747:	49 89 c7             	mov    %rax,%r15
  40174a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    if (data->threadindex == 0) {
  401750:	8b 83 0c 01 00 00    	mov    0x10c(%rbx),%eax
  401756:	85 c0                	test   %eax,%eax
  401758:	0f 84 aa 00 00 00    	je     401808 <work+0x148>
      long mask = data->ready;
  40175e:	8b 7b 28             	mov    0x28(%rbx),%edi
      if ((mask & PREP_READ_MASK) == PREP_READ_MASK) {
  401761:	40 f6 c7 10          	test   $0x10,%dil
  401765:	0f 85 bd 02 00 00    	jne    401a28 <work+0x368>
      if ((mask & PREP_WRITE_MASK) == PREP_WRITE_MASK) {
  40176b:	83 e7 20             	and    $0x20,%edi
  40176e:	74 5b                	je     4017cb <work+0x10b>
      if (data->publishstart < data->publishend) {
  401770:	48 8b 43 48          	mov    0x48(%rbx),%rax
  401774:	48 8b 4b 50          	mov    0x50(%rbx),%rcx
  401778:	bf 04 00 00 00       	mov    $0x4,%edi
  40177d:	48 39 c8             	cmp    %rcx,%rax
  401780:	7d 49                	jge    4017cb <work+0x10b>
        for (int x = data->publishstart ; x < data->publishend; x++) {
  401782:	89 c2                	mov    %eax,%edx
  401784:	48 98                	cltq
  401786:	48 39 c8             	cmp    %rcx,%rax
  401789:	7d 2f                	jge    4017ba <work+0xfa>
          data->main->works[x].available = 1;
  40178b:	48 8b 43 30          	mov    0x30(%rbx),%rax
  40178f:	48 8b b0 18 01 00 00 	mov    0x118(%rax),%rsi
  401796:	48 63 c2             	movslq %edx,%rax
  401799:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  4017a0:	48 c1 e0 08          	shl    $0x8,%rax
        for (int x = data->publishstart ; x < data->publishend; x++) {
  4017a4:	83 c2 01             	add    $0x1,%edx
          data->main->works[x].available = 1;
  4017a7:	c7 84 06 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rsi,%rax,1)
        for (int x = data->publishstart ; x < data->publishend; x++) {
  4017b2:	48 63 c2             	movslq %edx,%rax
  4017b5:	48 39 c8             	cmp    %rcx,%rax
  4017b8:	7c e6                	jl     4017a0 <work+0xe0>
        data->writing->available = FREE;
  4017ba:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
  4017c1:	c7 40 10 01 00 00 00 	movl   $0x1,0x10(%rax)
        data->ready = newmask;
  4017c8:	89 7b 28             	mov    %edi,0x28(%rbx)
  while (data->running == 1) {
  4017cb:	83 bb 04 01 00 00 01 	cmpl   $0x1,0x104(%rbx)
  4017d2:	0f 84 78 ff ff ff    	je     401750 <work+0x90>
  4017d8:	8b 93 0c 01 00 00    	mov    0x10c(%rbx),%edx
  4017de:	48 8d 35 2d 08 00 00 	lea    0x82d(%rip),%rsi        # 402012 <_IO_stdin_used+0x12>
  4017e5:	bf 01 00 00 00       	mov    $0x1,%edi
  4017ea:	31 c0                	xor    %eax,%eax
  4017ec:	e8 8f f8 ff ff       	call   401080 <__printf_chk@plt>
}
  4017f1:	48 83 c4 18          	add    $0x18,%rsp
  4017f5:	31 c0                	xor    %eax,%eax
  4017f7:	5b                   	pop    %rbx
  4017f8:	5d                   	pop    %rbp
  4017f9:	41 5c                	pop    %r12
  4017fb:	41 5d                	pop    %r13
  4017fd:	41 5e                	pop    %r14
  4017ff:	41 5f                	pop    %r15
  401801:	c3                   	ret
  401802:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401808:	48 8b 8b 60 01 00 00 	mov    0x160(%rbx),%rcx
  40180f:	4c 8d 41 01          	lea    0x1(%rcx),%r8
  401813:	4d 85 c0             	test   %r8,%r8
  401816:	7e b3                	jle    4017cb <work+0x10b>
        if (data->freelist[x].available == FREE ) {
  401818:	48 8b 8b 48 01 00 00 	mov    0x148(%rbx),%rcx
      for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40181f:	31 ff                	xor    %edi,%edi
    int availableidx = 0;
  401821:	31 d2                	xor    %edx,%edx
  401823:	31 f6                	xor    %esi,%esi
  401825:	0f 1f 00             	nopl   (%rax)
        if (data->freelist[x].available == FREE ) {
  401828:	48 c1 e6 05          	shl    $0x5,%rsi
  40182c:	83 7c 31 10 01       	cmpl   $0x1,0x10(%rcx,%rsi,1)
  401831:	75 0a                	jne    40183d <work+0x17d>
         available[availableidx] = x;
  401833:	48 63 f2             	movslq %edx,%rsi
          availableidx++;
  401836:	83 c2 01             	add    $0x1,%edx
         available[availableidx] = x;
  401839:	89 7c b5 00          	mov    %edi,0x0(%rbp,%rsi,4)
      for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40183d:	83 c7 01             	add    $0x1,%edi
  401840:	48 63 f7             	movslq %edi,%rsi
  401843:	4c 39 c6             	cmp    %r8,%rsi
  401846:	7c e0                	jl     401828 <work+0x168>
      if (availableidx == 0) {
  401848:	85 d2                	test   %edx,%edx
  40184a:	0f 84 7b ff ff ff    	je     4017cb <work+0x10b>
  for (int x = 1; x < data->threadsize ; x++) {
  401850:	8b b3 10 01 00 00    	mov    0x110(%rbx),%esi
          if (assignedchunk > availableidx) {
  401856:	89 d7                	mov    %edx,%edi
  401858:	c1 ef 1f             	shr    $0x1f,%edi
  for (int x = 1; x < data->threadsize ; x++) {
  40185b:	89 74 24 04          	mov    %esi,0x4(%rsp)
          if (assignedchunk > availableidx) {
  40185f:	89 7c 24 08          	mov    %edi,0x8(%rsp)
  for (int x = 1; x < data->threadsize ; x++) {
  401863:	83 fe 01             	cmp    $0x1,%esi
  401866:	0f 8e 40 02 00 00    	jle    401aac <work+0x3ec>
  40186c:	89 f7                	mov    %esi,%edi
        data->threads[x].newmask = 0;
  40186e:	4c 8b 5b 38          	mov    0x38(%rbx),%r11
  401872:	83 ef 02             	sub    $0x2,%edi
  401875:	48 8d 3c 7f          	lea    (%rdi,%rdi,2),%rdi
  401879:	49 8d b3 f0 02 00 00 	lea    0x2f0(%r11),%rsi
  401880:	48 c1 e7 07          	shl    $0x7,%rdi
  401884:	49 8d bc 3b 70 04 00 00 	lea    0x470(%r11,%rdi,1),%rdi
  40188c:	0f 1f 40 00          	nopl   0x0(%rax)
  401890:	48 c7 06 00 00 00 00 	movq   $0x0,(%rsi)
  for (int x = 1; x < data->threadsize ; x++) {
  401897:	48 81 c6 80 01 00 00 	add    $0x180,%rsi
  40189e:	48 39 f7             	cmp    %rsi,%rdi
  4018a1:	75 ed                	jne    401890 <work+0x1d0>
    writers = 0;
  4018a3:	89 44 24 0c          	mov    %eax,0xc(%rsp)
  4018a7:	8b 44 24 04          	mov    0x4(%rsp),%eax
  for (int x = 1; x < data->threadsize ; x++) {
  4018ab:	be 01 00 00 00       	mov    $0x1,%esi
    readers = 0;
  4018b0:	45 31 c0             	xor    %r8d,%r8d
  4018b3:	4d 8d 93 a8 01 00 00 	lea    0x1a8(%r11),%r10
    writers = 0;
  4018ba:	45 31 c9             	xor    %r9d,%r9d
  4018bd:	0f 1f 00             	nopl   (%rax)
        if ((data->threads[x].ready & WRITE_MASK) == WRITE_MASK || data->threads[x].ready == 0) {
  4018c0:	41 8b 3a             	mov    (%r10),%edi
  4018c3:	85 ff                	test   %edi,%edi
  4018c5:	41 0f 94 c4          	sete   %r12b
  4018c9:	40 f6 c7 04          	test   $0x4,%dil
  4018cd:	75 05                	jne    4018d4 <work+0x214>
  4018cf:	45 84 e4             	test   %r12b,%r12b
  4018d2:	74 0b                	je     4018df <work+0x21f>
          readywriters[writers++] = x;
  4018d4:	4d 63 e9             	movslq %r9d,%r13
  4018d7:	41 83 c1 01          	add    $0x1,%r9d
  4018db:	43 89 34 af          	mov    %esi,(%r15,%r13,4)
    if (data->threads[x].ready & (READ_MASK == READ_MASK) || data->threads[x].ready == 0) {
  4018df:	83 e7 01             	and    $0x1,%edi
  4018e2:	75 05                	jne    4018e9 <work+0x229>
  4018e4:	45 84 e4             	test   %r12b,%r12b
  4018e7:	74 0b                	je     4018f4 <work+0x234>
      readyreaders[readers++] = x;
  4018e9:	49 63 f8             	movslq %r8d,%rdi
  4018ec:	41 83 c0 01          	add    $0x1,%r8d
  4018f0:	41 89 34 be          	mov    %esi,(%r14,%rdi,4)
  for (int x = 1; x < data->threadsize ; x++) {
  4018f4:	83 c6 01             	add    $0x1,%esi
  4018f7:	49 81 c2 80 01 00 00 	add    $0x180,%r10
  4018fe:	39 c6                	cmp    %eax,%esi
  401900:	75 be                	jne    4018c0 <work+0x200>
   for (int x = 0; x < writers ; x++) {
  401902:	45 85 c9             	test   %r9d,%r9d
  401905:	8b 44 24 0c          	mov    0xc(%rsp),%eax
  401909:	41 0f 9e c5          	setle  %r13b
          if (assignedchunk > availableidx) {
  40190d:	45 85 c0             	test   %r8d,%r8d
  401910:	0f 8e af 01 00 00    	jle    401ac5 <work+0x405>
  401916:	80 7c 24 08 00       	cmpb   $0x0,0x8(%rsp)
  40191b:	0f 85 a4 01 00 00    	jne    401ac5 <work+0x405>
      int assignedchunk = 0;
  401921:	31 f6                	xor    %esi,%esi
  401923:	eb 08                	jmp    40192d <work+0x26d>
  401925:	0f 1f 00             	nopl   (%rax)
          if (assignedchunk > availableidx) {
  401928:	40 84 ff             	test   %dil,%dil
  40192b:	75 53                	jne    401980 <work+0x2c0>
          int thread = readyreaders[x];
  40192d:	48 63 fe             	movslq %esi,%rdi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401930:	83 c6 01             	add    $0x1,%esi
          int thread = readyreaders[x];
  401933:	45 8b 24 be          	mov    (%r14,%rdi,4),%r12d
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401937:	4c 63 54 bd 00       	movslq 0x0(%rbp,%rdi,4),%r10
          data->threads[thread].reading = chunk;
  40193c:	49 63 fc             	movslq %r12d,%rdi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  40193f:	49 c1 e2 05          	shl    $0x5,%r10
          data->threads[thread].reading = chunk;
  401943:	48 8d 3c 7f          	lea    (%rdi,%rdi,2),%rdi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401947:	49 01 ca             	add    %rcx,%r10
          data->threads[thread].reading = chunk;
  40194a:	48 c1 e7 07          	shl    $0x7,%rdi
          long start = chunk->start;
  40194e:	f3 41 0f 6f 02       	movdqu (%r10),%xmm0
          chunk->available = READING;
  401953:	41 c7 42 10 02 00 00 00 	movl   $0x2,0x10(%r10)
          data->threads[thread].reading = chunk;
  40195b:	4c 01 df             	add    %r11,%rdi
  40195e:	4c 89 97 50 01 00 00 	mov    %r10,0x150(%rdi)
          chunk->owner = thread;
  401965:	45 89 62 14          	mov    %r12d,0x14(%r10)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401969:	48 83 8f 70 01 00 00 10 	orq    $0x10,0x170(%rdi)
          if (assignedchunk > availableidx) {
  401971:	39 f2                	cmp    %esi,%edx
          long start = chunk->start;
  401973:	0f 11 47 18          	movups %xmm0,0x18(%rdi)
          if (assignedchunk > availableidx) {
  401977:	40 0f 9c c7          	setl   %dil
  40197b:	41 39 f0             	cmp    %esi,%r8d
  40197e:	7f a8                	jg     401928 <work+0x268>
  401980:	41 09 fd             	or     %edi,%r13d
                if (assignedchunk  > availableidx) {
  401983:	45 84 ed             	test   %r13b,%r13b
  401986:	74 0d                	je     401995 <work+0x2d5>
  401988:	eb 5d                	jmp    4019e7 <work+0x327>
  40198a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  401990:	41 39 c1             	cmp    %eax,%r9d
  401993:	7e 52                	jle    4019e7 <work+0x327>
          int thread = readywriters[x];
  401995:	48 63 f8             	movslq %eax,%rdi
   for (int x = 0; x < writers ; x++) {
  401998:	83 c0 01             	add    $0x1,%eax
          int thread = readywriters[x];
  40199b:	45 8b 14 bf          	mov    (%r15,%rdi,4),%r10d
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  40199f:	48 63 fe             	movslq %esi,%rdi
  4019a2:	83 c6 01             	add    $0x1,%esi
  4019a5:	4c 63 44 bd 00       	movslq 0x0(%rbp,%rdi,4),%r8
          data->threads[thread].writing = chunk;
  4019aa:	49 63 fa             	movslq %r10d,%rdi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  4019ad:	49 c1 e0 05          	shl    $0x5,%r8
          data->threads[thread].writing = chunk;
  4019b1:	48 8d 3c 7f          	lea    (%rdi,%rdi,2),%rdi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  4019b5:	49 01 c8             	add    %rcx,%r8
          data->threads[thread].writing = chunk;
  4019b8:	48 c1 e7 07          	shl    $0x7,%rdi
          long start = chunk->start;
  4019bc:	f3 41 0f 6f 08       	movdqu (%r8),%xmm1
          data->threads[thread].writing = chunk;
  4019c1:	4c 01 df             	add    %r11,%rdi
      chunk->available = WRITING;
  4019c4:	41 c7 40 10 03 00 00 00 	movl   $0x3,0x10(%r8)
          data->threads[thread].writing = chunk;
  4019cc:	4c 89 87 58 01 00 00 	mov    %r8,0x158(%rdi)
          chunk->owner = thread;
  4019d3:	45 89 50 14          	mov    %r10d,0x14(%r8)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  4019d7:	48 83 8f 70 01 00 00 20 	orq    $0x20,0x170(%rdi)
          long start = chunk->start;
  4019df:	0f 11 4f 48          	movups %xmm1,0x48(%rdi)
                if (assignedchunk  > availableidx) {
  4019e3:	39 f2                	cmp    %esi,%edx
  4019e5:	7d a9                	jge    401990 <work+0x2d0>
  4019e7:	8b 4c 24 04          	mov    0x4(%rsp),%ecx
  4019eb:	49 8d 43 28          	lea    0x28(%r11),%rax
  4019ef:	8d 51 ff             	lea    -0x1(%rcx),%edx
  4019f2:	48 8d 14 52          	lea    (%rdx,%rdx,2),%rdx
  4019f6:	48 c1 e2 07          	shl    $0x7,%rdx
  4019fa:	49 8d 8c 13 a8 01 00 00 	lea    0x1a8(%r11,%rdx,1),%rcx
  401a02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        data->threads[x].ready = data->threads[x].newmask;
  401a08:	48 8b 90 48 01 00 00 	mov    0x148(%rax),%rdx
      for (int x = 0; x < data->threadsize ; x++) {
  401a0f:	48 05 80 01 00 00    	add    $0x180,%rax
        data->threads[x].ready = data->threads[x].newmask;
  401a15:	89 90 80 fe ff ff    	mov    %edx,-0x180(%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401a1b:	48 39 c8             	cmp    %rcx,%rax
  401a1e:	75 e8                	jne    401a08 <work+0x348>
  401a20:	e9 a6 fd ff ff       	jmp    4017cb <work+0x10b>
  401a25:	0f 1f 00             	nopl   (%rax)
      for (int x = data->start; x < data->end; x++) {
  401a28:	48 8b 43 18          	mov    0x18(%rbx),%rax
  401a2c:	4c 8b 43 20          	mov    0x20(%rbx),%r8
  401a30:	89 c6                	mov    %eax,%esi
  401a32:	48 98                	cltq
  401a34:	49 39 c0             	cmp    %rax,%r8
  401a37:	7e 49                	jle    401a82 <work+0x3c2>
        data->main->works[x].available = 0;
  401a39:	48 8b 43 30          	mov    0x30(%rbx),%rax
  401a3d:	4c 8b 90 18 01 00 00 	mov    0x118(%rax),%r10
  401a44:	48 8b 43 58          	mov    0x58(%rbx),%rax
  401a48:	48 8d 48 01          	lea    0x1(%rax),%rcx
  401a4c:	48 63 c6             	movslq %esi,%rax
  401a4f:	90                   	nop
  401a50:	48 c1 e0 08          	shl    $0x8,%rax
      for (int x = data->start; x < data->end; x++) {
  401a54:	83 c6 01             	add    $0x1,%esi
        data->freq++;
  401a57:	49 89 c9             	mov    %rcx,%r9
      for (int x = data->start; x < data->end; x++) {
  401a5a:	48 83 c1 01          	add    $0x1,%rcx
        data->main->works[x].available = 0;
  401a5e:	49 8d 14 02          	lea    (%r10,%rax,1),%rdx
      for (int x = data->start; x < data->end; x++) {
  401a62:	48 63 c6             	movslq %esi,%rax
        data->main->works[x].available = 0;
  401a65:	c7 82 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rdx)
      for (int x = data->start; x < data->end; x++) {
  401a6f:	4c 39 c0             	cmp    %r8,%rax
  401a72:	7c dc                	jl     401a50 <work+0x390>
  401a74:	4c 89 4b 58          	mov    %r9,0x58(%rbx)
  401a78:	c7 82 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rdx)
        data->reading->available = FREE;
  401a82:	48 8b 83 50 01 00 00 	mov    0x150(%rbx),%rax
      if ((mask & PREP_WRITE_MASK) == PREP_WRITE_MASK) {
  401a89:	83 e7 20             	and    $0x20,%edi
        data->reading->available = FREE;
  401a8c:	c7 40 10 01 00 00 00 	movl   $0x1,0x10(%rax)
      if ((mask & PREP_WRITE_MASK) == PREP_WRITE_MASK) {
  401a93:	74 0d                	je     401aa2 <work+0x3e2>
      if (data->publishstart < data->publishend) {
  401a95:	48 8b 43 48          	mov    0x48(%rbx),%rax
  401a99:	48 8b 4b 50          	mov    0x50(%rbx),%rcx
  401a9d:	48 39 c8             	cmp    %rcx,%rax
  401aa0:	7c 19                	jl     401abb <work+0x3fb>
  401aa2:	bf 08 00 00 00       	mov    $0x8,%edi
  401aa7:	e9 1c fd ff ff       	jmp    4017c8 <work+0x108>
      for (int x = 0; x < data->threadsize ; x++) {
  401aac:	0f 85 19 fd ff ff    	jne    4017cb <work+0x10b>
  401ab2:	4c 8b 5b 38          	mov    0x38(%rbx),%r11
  401ab6:	e9 2c ff ff ff       	jmp    4019e7 <work+0x327>
      if (data->publishstart < data->publishend) {
  401abb:	bf 0c 00 00 00       	mov    $0xc,%edi
  401ac0:	e9 bd fc ff ff       	jmp    401782 <work+0xc2>
  401ac5:	44 0b 6c 24 08       	or     0x8(%rsp),%r13d
      int assignedchunk = 0;
  401aca:	31 f6                	xor    %esi,%esi
  401acc:	e9 b2 fe ff ff       	jmp    401983 <work+0x2c3>

Disassembly of section .fini:

0000000000401ad4 <_fini>:
  401ad4:	f3 0f 1e fa          	endbr64
  401ad8:	48 83 ec 08          	sub    $0x8,%rsp
  401adc:	48 83 c4 08          	add    $0x8,%rsp
  401ae0:	c3                   	ret
