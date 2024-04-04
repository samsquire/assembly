
bump-workqueue:     file format elf64-x86-64


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
  401020:	ff 35 72 2f 00 00    	push   0x2f72(%rip)        # 403f98 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 74 2f 00 00    	jmp    *0x2f74(%rip)        # 403fa0 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <pthread_setaffinity_np@plt>:
  401030:	ff 25 72 2f 00 00    	jmp    *0x2f72(%rip)        # 403fa8 <pthread_setaffinity_np@GLIBC_2.34>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <puts@plt>:
  401040:	ff 25 6a 2f 00 00    	jmp    *0x2f6a(%rip)        # 403fb0 <puts@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <clock_gettime@plt>:
  401050:	ff 25 62 2f 00 00    	jmp    *0x2f62(%rip)        # 403fb8 <clock_gettime@GLIBC_2.17>
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
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
}

int main(int argc, char **argv) {
  4010c0:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4010c2:	ba 08 00 00 00       	mov    $0x8,%edx
  4010c7:	bf 01 00 00 00       	mov    $0x1,%edi
  4010cc:	48 8d 35 85 0f 00 00 	lea    0xf85(%rip),%rsi        # 402058 <_IO_stdin_used+0x58>
  4010d3:	41 56                	push   %r14
  struct Work *works = calloc(worksize, sizeof(struct Work));
  printf("Buffer size %d\n", worksize);
  int chunkindex = 0;
  int * readcursors = calloc(threadsize, sizeof(int));
  int * writecursors = calloc(threadsize, sizeof(int));
  struct Chunk *freelist = calloc(chunkslen, sizeof(struct Chunk));
  4010d5:	41 be 09 00 00 00    	mov    $0x9,%r14d
int main(int argc, char **argv) {
  4010db:	41 55                	push   %r13
  4010dd:	4c 8d 2d ba 0f 00 00 	lea    0xfba(%rip),%r13        # 40209e <_IO_stdin_used+0x9e>
  4010e4:	41 54                	push   %r12
  4010e6:	55                   	push   %rbp
  struct Chunk *freelist = calloc(chunkslen, sizeof(struct Chunk));
  4010e7:	31 ed                	xor    %ebp,%ebp
int main(int argc, char **argv) {
  4010e9:	53                   	push   %rbx
  4010ea:	48 83 ec 78          	sub    $0x78,%rsp
  4010ee:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4010f7:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  4010fc:	31 c0                	xor    %eax,%eax
  4010fe:	e8 8d ff ff ff       	call   401090 <__printf_chk@plt>
  401103:	ba 04 00 00 00       	mov    $0x4,%edx
  401108:	48 8d 35 5b 0f 00 00 	lea    0xf5b(%rip),%rsi        # 40206a <_IO_stdin_used+0x6a>
  40110f:	31 c0                	xor    %eax,%eax
  401111:	bf 01 00 00 00       	mov    $0x1,%edi
  401116:	e8 75 ff ff ff       	call   401090 <__printf_chk@plt>
  40111b:	ba 20 00 00 00       	mov    $0x20,%edx
  401120:	48 8d 35 3f 0f 00 00 	lea    0xf3f(%rip),%rsi        # 402066 <_IO_stdin_used+0x66>
  401127:	31 c0                	xor    %eax,%eax
  401129:	bf 01 00 00 00       	mov    $0x1,%edi
  40112e:	e8 5d ff ff ff       	call   401090 <__printf_chk@plt>
  401133:	ba 08 00 00 00       	mov    $0x8,%edx
  401138:	48 8d 35 3a 0f 00 00 	lea    0xf3a(%rip),%rsi        # 402079 <_IO_stdin_used+0x79>
  40113f:	31 c0                	xor    %eax,%eax
  401141:	bf 01 00 00 00       	mov    $0x1,%edi
  401146:	e8 45 ff ff ff       	call   401090 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40114b:	be 08 00 00 00       	mov    $0x8,%esi
  401150:	bf 08 00 00 00       	mov    $0x8,%edi
  401155:	e8 26 ff ff ff       	call   401080 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  40115a:	be 38 00 00 00       	mov    $0x38,%esi
  40115f:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401164:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401169:	e8 12 ff ff ff       	call   401080 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40116e:	be 40 0c 00 00       	mov    $0xc40,%esi
  401173:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401178:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40117d:	e8 fe fe ff ff       	call   401080 <calloc@plt>
  struct Work *works = calloc(worksize, sizeof(struct Work));
  401182:	be 38 00 00 00       	mov    $0x38,%esi
  401187:	bf 88 00 00 00       	mov    $0x88,%edi
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40118c:	48 89 c3             	mov    %rax,%rbx
  struct Work *works = calloc(worksize, sizeof(struct Work));
  40118f:	e8 ec fe ff ff       	call   401080 <calloc@plt>
  401194:	ba 88 00 00 00       	mov    $0x88,%edx
  401199:	48 8d 35 ee 0e 00 00 	lea    0xeee(%rip),%rsi        # 40208e <_IO_stdin_used+0x8e>
  4011a0:	bf 01 00 00 00       	mov    $0x1,%edi
  4011a5:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  4011aa:	31 c0                	xor    %eax,%eax
  4011ac:	4c 8d bb 54 01 00 00 	lea    0x154(%rbx),%r15
  4011b3:	e8 d8 fe ff ff       	call   401090 <__printf_chk@plt>
  int * readcursors = calloc(threadsize, sizeof(int));
  4011b8:	be 04 00 00 00       	mov    $0x4,%esi
  4011bd:	bf 08 00 00 00       	mov    $0x8,%edi
  4011c2:	e8 b9 fe ff ff       	call   401080 <calloc@plt>
  int * writecursors = calloc(threadsize, sizeof(int));
  4011c7:	be 04 00 00 00       	mov    $0x4,%esi
  4011cc:	bf 08 00 00 00       	mov    $0x8,%edi
  int * readcursors = calloc(threadsize, sizeof(int));
  4011d1:	49 89 c4             	mov    %rax,%r12
  int * writecursors = calloc(threadsize, sizeof(int));
  4011d4:	e8 a7 fe ff ff       	call   401080 <calloc@plt>
  4011d9:	66 49 0f 6e ec       	movq   %r12,%xmm5
  struct Chunk *freelist = calloc(chunkslen, sizeof(struct Chunk));
  4011de:	be 20 00 00 00       	mov    $0x20,%esi
  4011e3:	bf 88 00 00 00       	mov    $0x88,%edi
  4011e8:	66 48 0f 6e f8       	movq   %rax,%xmm7
  4011ed:	66 0f 6c ef          	punpcklqdq %xmm7,%xmm5
  4011f1:	0f 29 2c 24          	movaps %xmm5,(%rsp)
  4011f5:	e8 86 fe ff ff       	call   401080 <calloc@plt>
  4011fa:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
          for (int x = 0; x < threadsize; x++) {
  4011ff:	90                   	nop
          offset += (threadsize * 2) + 1;
        
     data[chunkindex].writecursors = writecursors;
     data[chunkindex].readcursors = readcursors;
            
    data[chunkindex].owritecursor = middle + 1;
  401200:	41 8d 46 01          	lea    0x1(%r14),%eax
     data[chunkindex].readcursors = readcursors;
  401204:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
  401209:	4c 89 f2             	mov    %r14,%rdx
  40120c:	4c 89 ee             	mov    %r13,%rsi
    data[chunkindex].owritecursor = middle + 1;
  40120f:	41 89 47 08          	mov    %eax,0x8(%r15)
  401213:	bf 01 00 00 00       	mov    $0x1,%edi
  401218:	31 c0                	xor    %eax,%eax
          for (int x = 0; x < threadsize; x++) {
  40121a:	49 81 c7 88 01 00 00 	add    $0x188,%r15
     data[chunkindex].readcursors = readcursors;
  401221:	41 0f 11 8f 94 fe ff ff 	movups %xmm1,-0x16c(%r15)
  401229:	e8 62 fe ff ff       	call   401090 <__printf_chk@plt>
    printf("middle %ld\n", middle);
    data[chunkindex].middle = middle;
    data[chunkindex].readcursors[chunkindex] = middle;
  40122e:	49 8b 87 94 fe ff ff 	mov    -0x16c(%r15),%rax
    data[chunkindex].middle = middle;
  401235:	45 89 b7 78 fe ff ff 	mov    %r14d,-0x188(%r15)
    data[chunkindex].readcursors[chunkindex] = middle;
  40123c:	44 89 34 28          	mov    %r14d,(%rax,%rbp,1)
    data[chunkindex].writecursors[chunkindex] = middle;
  401240:	49 8b 87 9c fe ff ff 	mov    -0x164(%r15),%rax
  401247:	44 89 34 28          	mov    %r14d,(%rax,%rbp,1)
    data[chunkindex].oreadcursor = start;
  40124b:	41 8d 46 f7          	lea    -0x9(%r14),%eax
          for (int x = 0; x < threadsize; x++) {
  40124f:	49 83 c6 11          	add    $0x11,%r14
  401253:	48 83 c5 04          	add    $0x4,%rbp
    data[chunkindex].oreadcursor = start;
  401257:	41 89 87 84 fe ff ff 	mov    %eax,-0x17c(%r15)
          for (int x = 0; x < threadsize; x++) {
  40125e:	49 81 fe 91 00 00 00 	cmp    $0x91,%r14
  401265:	75 99                	jne    401200 <main+0x140>
  401267:	ba 88 00 00 00       	mov    $0x88,%edx
  40126c:	48 8d 35 37 0e 00 00 	lea    0xe37(%rip),%rsi        # 4020aa <_IO_stdin_used+0xaa>
  401273:	bf 01 00 00 00       	mov    $0x1,%edi
  401278:	31 c0                	xor    %eax,%eax
  40127a:	e8 11 fe ff ff       	call   401090 <__printf_chk@plt>
  40127f:	ba 88 00 00 00       	mov    $0x88,%edx
  401284:	48 8d 35 2a 0e 00 00 	lea    0xe2a(%rip),%rsi        # 4020b5 <_IO_stdin_used+0xb5>
  40128b:	31 c0                	xor    %eax,%eax
  40128d:	bf 01 00 00 00       	mov    $0x1,%edi
  401292:	e8 f9 fd ff ff       	call   401090 <__printf_chk@plt>
        
          }
printf("offset %d\n", offset);
  
printf("%ld chunks\n", chunkslen);
  for (int i = 0; i < worksize; i++) {
  401297:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    works[i].taskindex = 2;
  40129c:	48 ba 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rdx
  4012a6:	48 8d 88 c0 1d 00 00 	lea    0x1dc0(%rax),%rcx
  4012ad:	0f 1f 00             	nopl   (%rax)
  4012b0:	48 89 10             	mov    %rdx,(%rax)
  4012b3:	48 83 c0 70          	add    $0x70,%rax
  4012b7:	48 89 50 c8          	mov    %rdx,-0x38(%rax)
  for (int i = 0; i < worksize; i++) {
  4012bb:	48 39 c8             	cmp    %rcx,%rax
  4012be:	75 f0                	jne    4012b0 <main+0x1f0>
    works[i].available = 1;
    
  }
  int cpu = 0;
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  4012c0:	be 04 00 00 00       	mov    $0x4,%esi
  4012c5:	bf 08 00 00 00       	mov    $0x8,%edi
  data[0].works = works;
  4012ca:	49 89 dd             	mov    %rbx,%r13
  4012cd:	45 31 e4             	xor    %r12d,%r12d
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  4012d0:	e8 ab fd ff ff       	call   401080 <calloc@plt>
  4012d5:	66 48 0f 6e fb       	movq   %rbx,%xmm7
  4012da:	45 31 ff             	xor    %r15d,%r15d
  4012dd:	49 89 c1             	mov    %rax,%r9
  4012e0:	66 48 0f 6e f0       	movq   %rax,%xmm6
  data[0].works = works;
  4012e5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  4012ea:	66 0f 6c f7          	punpcklqdq %xmm7,%xmm6
  4012ee:	4d 89 ce             	mov    %r9,%r14
  4012f1:	48 89 43 78          	mov    %rax,0x78(%rbx)
  4012f5:	0f 29 34 24          	movaps %xmm6,(%rsp)
  for (int x = 0; x < threadsize ; x++) {
  4012f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401300:	44 89 fd             	mov    %r15d,%ebp
  401303:	be 80 00 00 00       	mov    $0x80,%esi
  401308:	bf 01 00 00 00       	mov    $0x1,%edi
    CPU_SET(cpu += 1, data[x].cpu_set);
  40130d:	41 83 c7 01          	add    $0x1,%r15d
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401311:	e8 6a fd ff ff       	call   401080 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  401316:	44 89 f9             	mov    %r15d,%ecx
  401319:	ba 01 00 00 00       	mov    $0x1,%edx
  40131e:	48 8d 35 eb 0d 00 00 	lea    0xdeb(%rip),%rsi        # 402110 <_IO_stdin_used+0x110>
  401325:	48 d3 e2             	shl    %cl,%rdx
  401328:	48 09 10             	or     %rdx,(%rax)
  40132b:	44 89 f9             	mov    %r15d,%ecx
  40132e:	89 ea                	mov    %ebp,%edx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401330:	49 89 85 80 00 00 00 	mov    %rax,0x80(%r13)
  401337:	bf 01 00 00 00       	mov    $0x1,%edi
  40133c:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  40133e:	49 83 c6 04          	add    $0x4,%r14
  401342:	49 81 c5 88 01 00 00 	add    $0x188,%r13
  401349:	e8 42 fd ff ff       	call   401090 <__printf_chk@plt>
    
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].readies = readies;
    data[x].readies[x] = 0;
    data[x].buckets = buckets;
  40134e:	48 8b 05 db 0d 00 00 	mov    0xddb(%rip),%rax        # 402130 <_IO_stdin_used+0x130>
    data[x].readies = readies;
  401355:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
    data[x].bucketstart = x * buckets ;
  40135a:	45 89 a5 18 ff ff ff 	mov    %r12d,-0xe8(%r13)
    data[x].main = &data[0];
    data[x].threads = data;
    data[x].wantindex = -1;
    data[x].read = 0;
  401361:	66 0f 6f 1d d7 0d 00 00 	movdqa 0xdd7(%rip),%xmm3        # 402140 <_IO_stdin_used+0x140>
    data[x].write = worksize;
    
    data[x].freelist = freelist;
    data[x].chunksize = chunksize;
    data[x].chunkslen = chunkslen;
  401369:	66 0f 6f 25 df 0d 00 00 	movdqa 0xddf(%rip),%xmm4        # 402150 <_IO_stdin_used+0x150>
    data[x].loglevel = debug;
  401371:	41 c7 85 00 ff ff ff 00 00 00 00 	movl   $0x0,-0x100(%r13)
  for (int x = 0; x < threadsize ; x++) {
  40137c:	41 83 c4 11          	add    $0x11,%r12d
    data[x].buckets = buckets;
  401380:	49 89 85 10 ff ff ff 	mov    %rax,-0xf0(%r13)
    data[x].wantindex = -1;
  401387:	48 8b 05 aa 0d 00 00 	mov    0xdaa(%rip),%rax        # 402138 <_IO_stdin_used+0x138>
    data[x].threadindex = x;
  40138e:	41 89 ad e4 fe ff ff 	mov    %ebp,-0x11c(%r13)
    data[x].wantindex = -1;
  401395:	49 89 85 d8 fe ff ff 	mov    %rax,-0x128(%r13)
    data[x].freelist = freelist;
  40139c:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    data[x].worksize = worksize;
  4013a1:	41 c7 85 e0 fe ff ff 88 00 00 00 	movl   $0x88,-0x120(%r13)
    data[x].threadsize = threadsize;
  4013ac:	41 c7 85 e8 fe ff ff 08 00 00 00 	movl   $0x8,-0x118(%r13)
    data[x].readies[x] = 0;
  4013b7:	41 c7 46 fc 00 00 00 00 	movl   $0x0,-0x4(%r14)
    data[x].readies = readies;
  4013bf:	41 0f 11 95 98 fe ff ff 	movups %xmm2,-0x168(%r13)
    data[x].threads = data;
  4013c7:	49 89 9d a8 fe ff ff 	mov    %rbx,-0x158(%r13)
    data[x].read = 0;
  4013ce:	41 0f 11 9d 78 fe ff ff 	movups %xmm3,-0x188(%r13)
    data[x].freelist = freelist;
  4013d6:	49 89 85 20 ff ff ff 	mov    %rax,-0xe0(%r13)
    data[x].chunkslen = chunkslen;
  4013dd:	41 0f 11 a5 38 ff ff ff 	movups %xmm4,-0xc8(%r13)
    data[x].newmask = 0;
  4013e5:	41 c7 85 48 ff ff ff 00 00 00 00 	movl   $0x0,-0xb8(%r13)
  for (int x = 0; x < threadsize ; x++) {
  4013f0:	41 83 ff 08          	cmp    $0x8,%r15d
  4013f4:	0f 85 06 ff ff ff    	jne    401300 <main+0x240>
  4013fa:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
  4013ff:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
  401404:	48 89 1c 24          	mov    %rbx,(%rsp)
  401408:	49 89 de             	mov    %rbx,%r14
  40140b:	49 c7 c5 a0 1c 40 00 	mov    $0x401ca0,%r13
  401412:	49 8d 87 c0 01 00 00 	lea    0x1c0(%r15),%rax
  401419:	4c 89 fb             	mov    %r15,%rbx
  40141c:	49 89 ec             	mov    %rbp,%r12
  40141f:	49 89 c7             	mov    %rax,%r15
  401422:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  401428:	4c 89 f1             	mov    %r14,%rcx
  40142b:	48 89 de             	mov    %rbx,%rsi
  40142e:	48 89 ef             	mov    %rbp,%rdi
  401431:	4c 89 ea             	mov    %r13,%rdx
  401434:	e8 67 fc ff ff       	call   4010a0 <pthread_create@plt>
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401439:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
  for (int x = 0; x < threadsize ; x++) {
  40143d:	48 83 c3 38          	add    $0x38,%rbx
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401441:	49 8b 96 80 00 00 00 	mov    0x80(%r14),%rdx
  401448:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  40144d:	48 83 c5 08          	add    $0x8,%rbp
  401451:	49 81 c6 88 01 00 00 	add    $0x188,%r14
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401458:	e8 d3 fb ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  40145d:	4c 39 fb             	cmp    %r15,%rbx
  401460:	75 c6                	jne    401428 <main+0x368>
  }
  
  struct timespec time = {
  401462:	48 8b 1c 24          	mov    (%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  401466:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  40146b:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec time = {
  401470:	66 0f 6f 05 e8 0c 00 00 	movdqa 0xce8(%rip),%xmm0        # 402160 <_IO_stdin_used+0x160>
  401478:	4c 8d 74 24 38       	lea    0x38(%rsp),%r14
  40147d:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  401482:	66 0f ef c0          	pxor   %xmm0,%xmm0
  401486:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  40148b:	e8 e0 fb ff ff       	call   401070 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  401490:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
  401495:	c7 43 64 00 00 00 00 	movl   $0x0,0x64(%rbx)
  40149c:	c7 83 ec 01 00 00 00 00 00 00 	movl   $0x0,0x1ec(%rbx)
  4014a6:	c7 83 74 03 00 00 00 00 00 00 	movl   $0x0,0x374(%rbx)
  4014b0:	49 83 c5 40          	add    $0x40,%r13
  4014b4:	c7 83 fc 04 00 00 00 00 00 00 	movl   $0x0,0x4fc(%rbx)
  4014be:	c7 83 84 06 00 00 00 00 00 00 	movl   $0x0,0x684(%rbx)
  4014c8:	c7 83 0c 08 00 00 00 00 00 00 	movl   $0x0,0x80c(%rbx)
  4014d2:	c7 83 94 09 00 00 00 00 00 00 	movl   $0x0,0x994(%rbx)
  4014dc:	c7 83 1c 0b 00 00 00 00 00 00 	movl   $0x0,0xb1c(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  4014e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  4014f0:	49 8b 3c 24          	mov    (%r12),%rdi
  4014f4:	4c 89 f6             	mov    %r14,%rsi
  for (int x = 0; x < threadsize; x++) {
  4014f7:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  4014fb:	e8 b0 fb ff ff       	call   4010b0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401500:	4d 39 e5             	cmp    %r12,%r13
  401503:	75 eb                	jne    4014f0 <main+0x430>
  401505:	48 8d 3d b5 0b 00 00 	lea    0xbb5(%rip),%rdi        # 4020c1 <_IO_stdin_used+0xc1>
  40150c:	4c 8d 63 48          	lea    0x48(%rbx),%r12
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  401510:	45 31 ed             	xor    %r13d,%r13d
  401513:	e8 28 fb ff ff       	call   401040 <puts@plt>
  for (int x = 0; x < threadsize; x++) {
  401518:	4c 8d b3 88 0c 00 00 	lea    0xc88(%rbx),%r14
  40151f:	4c 8d 3d b6 0b 00 00 	lea    0xbb6(%rip),%r15        # 4020dc <_IO_stdin_used+0xdc>
  401526:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401530:	49 8b 14 24          	mov    (%r12),%rdx
  401534:	4c 89 fe             	mov    %r15,%rsi
  401537:	bf 01 00 00 00       	mov    $0x1,%edi
  40153c:	31 c0                	xor    %eax,%eax
  40153e:	49 81 c4 88 01 00 00 	add    $0x188,%r12
  401545:	e8 46 fb ff ff       	call   401090 <__printf_chk@plt>
    printf("%ld\n", data[x].freq);
    freq += data[x].freq;
  40154a:	4d 03 ac 24 78 fe ff ff 	add    -0x188(%r12),%r13
  for (int x = 0; x < threadsize; x++) {
  401552:	4d 39 e6             	cmp    %r12,%r14
  401555:	75 d9                	jne    401530 <main+0x470>
  }
  printf("freq: %ld\n", freq/ seconds);
  401557:	4c 89 e8             	mov    %r13,%rax
  40155a:	49 c1 fd 3f          	sar    $0x3f,%r13
  40155e:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
  401568:	48 8d 35 67 0b 00 00 	lea    0xb67(%rip),%rsi        # 4020d6 <_IO_stdin_used+0xd6>
  40156f:	49 f7 ec             	imul   %r12
  401572:	bf 01 00 00 00       	mov    $0x1,%edi
  401577:	31 c0                	xor    %eax,%eax
  401579:	4c 8d 35 73 0b 00 00 	lea    0xb73(%rip),%r14        # 4020f3 <_IO_stdin_used+0xf3>
  401580:	48 d1 fa             	sar    %rdx
  401583:	4c 29 ea             	sub    %r13,%rdx
  401586:	e8 05 fb ff ff       	call   401090 <__printf_chk@plt>
  long freq_writes = 0;
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  40158b:	48 8b 8b d8 01 00 00 	mov    0x1d8(%rbx),%rcx
  401592:	bf 01 00 00 00       	mov    $0x1,%edi
  401597:	48 03 8b 60 03 00 00 	add    0x360(%rbx),%rcx
  40159e:	48 03 4b 50          	add    0x50(%rbx),%rcx
  4015a2:	48 03 8b e8 04 00 00 	add    0x4e8(%rbx),%rcx
  4015a9:	48 8d 35 31 0b 00 00 	lea    0xb31(%rip),%rsi        # 4020e1 <_IO_stdin_used+0xe1>
  4015b0:	48 03 8b 70 06 00 00 	add    0x670(%rbx),%rcx
  4015b7:	48 03 8b f8 07 00 00 	add    0x7f8(%rbx),%rcx
  4015be:	48 03 8b 80 09 00 00 	add    0x980(%rbx),%rcx
  4015c5:	48 03 8b 08 0b 00 00 	add    0xb08(%rbx),%rcx
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  4015cc:	48 89 c8             	mov    %rcx,%rax
  4015cf:	48 c1 f9 3f          	sar    $0x3f,%rcx
  4015d3:	49 f7 ec             	imul   %r12
  4015d6:	31 c0                	xor    %eax,%eax
  4015d8:	48 d1 fa             	sar    %rdx
  4015db:	48 29 ca             	sub    %rcx,%rdx
  4015de:	e8 ad fa ff ff       	call   401090 <__printf_chk@plt>

  for (int i = 0; i < threadsize * 2; i++) {
  4015e3:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  4015e8:	48 89 1c 24          	mov    %rbx,(%rsp)
  4015ec:	4c 8d 60 10          	lea    0x10(%rax),%r12
  4015f0:	4c 8d a8 90 03 00 00 	lea    0x390(%rax),%r13
  4015f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
   struct timespec created = works[i].created;
    struct timespec read = works[i].read;
  401600:	49 8b 5c 24 10       	mov    0x10(%r12),%rbx
    struct timespec written = works[i].written;
  401605:	49 8b 6c 24 20       	mov    0x20(%r12),%rbp
  40160a:	4c 89 f6             	mov    %r14,%rsi
  40160d:	31 c0                	xor    %eax,%eax
  40160f:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int i = 0; i < threadsize * 2; i++) {
  401614:	49 83 c4 38          	add    $0x38,%r12
    printf("%ldns\n", read.tv_nsec - created.tv_nsec);
  401618:	48 89 da             	mov    %rbx,%rdx
  40161b:	49 2b 54 24 c8       	sub    -0x38(%r12),%rdx
  401620:	e8 6b fa ff ff       	call   401090 <__printf_chk@plt>
    printf("%ldns\n", written.tv_nsec - read.tv_nsec);
  401625:	48 89 ea             	mov    %rbp,%rdx
  401628:	4c 89 f6             	mov    %r14,%rsi
  40162b:	bf 01 00 00 00       	mov    $0x1,%edi
  401630:	48 29 da             	sub    %rbx,%rdx
  401633:	31 c0                	xor    %eax,%eax
  401635:	e8 56 fa ff ff       	call   401090 <__printf_chk@plt>
  for (int i = 0; i < threadsize * 2; i++) {
  40163a:	4d 39 e5             	cmp    %r12,%r13
  40163d:	75 c1                	jne    401600 <main+0x540>
  40163f:	48 8b 1c 24          	mov    (%rsp),%rbx
  401643:	48 8d 3d b0 0a 00 00 	lea    0xab0(%rip),%rdi        # 4020fa <_IO_stdin_used+0xfa>
  40164a:	e8 f1 f9 ff ff       	call   401040 <puts@plt>
  40164f:	4c 89 fe             	mov    %r15,%rsi
  401652:	bf 01 00 00 00       	mov    $0x1,%edi
  401657:	31 c0                	xor    %eax,%eax
    
  }
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  401659:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
  401660:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  401667:	e8 24 fa ff ff       	call   401090 <__printf_chk@plt>
  40166c:	4c 89 fe             	mov    %r15,%rsi
  40166f:	bf 01 00 00 00       	mov    $0x1,%edi
  401674:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  401676:	48 8b 93 08 01 00 00 	mov    0x108(%rbx),%rdx
  40167d:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  401684:	e8 07 fa ff ff       	call   401090 <__printf_chk@plt>
  401689:	4c 89 fe             	mov    %r15,%rsi
  40168c:	bf 01 00 00 00       	mov    $0x1,%edi
  401691:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  401693:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
  40169a:	48 2b 93 08 01 00 00 	sub    0x108(%rbx),%rdx
  4016a1:	e8 ea f9 ff ff       	call   401090 <__printf_chk@plt>
  4016a6:	4c 89 fe             	mov    %r15,%rsi
  4016a9:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ae:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4016b0:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
  4016b7:	48 2b 93 18 01 00 00 	sub    0x118(%rbx),%rdx
  4016be:	e8 cd f9 ff ff       	call   401090 <__printf_chk@plt>
  4016c3:	4c 89 fe             	mov    %r15,%rsi
  4016c6:	bf 01 00 00 00       	mov    $0x1,%edi
  4016cb:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  4016cd:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
  4016d4:	48 2b 93 28 01 00 00 	sub    0x128(%rbx),%rdx
  4016db:	e8 b0 f9 ff ff       	call   401090 <__printf_chk@plt>
  4016e0:	4c 89 fe             	mov    %r15,%rsi
  4016e3:	bf 01 00 00 00       	mov    $0x1,%edi
  4016e8:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  4016ea:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
  4016f1:	48 2b 93 08 01 00 00 	sub    0x108(%rbx),%rdx
  4016f8:	e8 93 f9 ff ff       	call   401090 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  4016fd:	48 8b 93 48 01 00 00 	mov    0x148(%rbx),%rdx
  401704:	31 c0                	xor    %eax,%eax
  401706:	48 2b 93 38 01 00 00 	sub    0x138(%rbx),%rdx
  40170d:	48 8d 35 f3 09 00 00 	lea    0x9f3(%rip),%rsi        # 402107 <_IO_stdin_used+0x107>
  401714:	bf 01 00 00 00       	mov    $0x1,%edi
  401719:	e8 72 f9 ff ff       	call   401090 <__printf_chk@plt>
  } 
  
  40171e:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  401723:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40172c:	75 11                	jne    40173f <main+0x67f>
  40172e:	48 83 c4 78          	add    $0x78,%rsp
  401732:	31 c0                	xor    %eax,%eax
  401734:	5b                   	pop    %rbx
  401735:	5d                   	pop    %rbp
  401736:	41 5c                	pop    %r12
  401738:	41 5d                	pop    %r13
  40173a:	41 5e                	pop    %r14
  40173c:	41 5f                	pop    %r15
  40173e:	c3                   	ret
  40173f:	e8 1c f9 ff ff       	call   401060 <__stack_chk_fail@plt>
  401744:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40174e:	66 90                	xchg   %ax,%ax

0000000000401750 <_start>:
  401750:	f3 0f 1e fa          	endbr64
  401754:	31 ed                	xor    %ebp,%ebp
  401756:	49 89 d1             	mov    %rdx,%r9
  401759:	5e                   	pop    %rsi
  40175a:	48 89 e2             	mov    %rsp,%rdx
  40175d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401761:	50                   	push   %rax
  401762:	54                   	push   %rsp
  401763:	45 31 c0             	xor    %r8d,%r8d
  401766:	31 c9                	xor    %ecx,%ecx
  401768:	48 c7 c7 c0 10 40 00 	mov    $0x4010c0,%rdi
  40176f:	ff 15 7b 28 00 00    	call   *0x287b(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  401775:	f4                   	hlt
  401776:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401780 <_dl_relocate_static_pie>:
  401780:	f3 0f 1e fa          	endbr64
  401784:	c3                   	ret
  401785:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40178f:	90                   	nop

0000000000401790 <deregister_tm_clones>:
  401790:	b8 10 40 40 00       	mov    $0x404010,%eax
  401795:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  40179b:	74 13                	je     4017b0 <deregister_tm_clones+0x20>
  40179d:	b8 00 00 00 00       	mov    $0x0,%eax
  4017a2:	48 85 c0             	test   %rax,%rax
  4017a5:	74 09                	je     4017b0 <deregister_tm_clones+0x20>
  4017a7:	bf 10 40 40 00       	mov    $0x404010,%edi
  4017ac:	ff e0                	jmp    *%rax
  4017ae:	66 90                	xchg   %ax,%ax
  4017b0:	c3                   	ret
  4017b1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4017bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004017c0 <register_tm_clones>:
  4017c0:	be 10 40 40 00       	mov    $0x404010,%esi
  4017c5:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  4017cc:	48 89 f0             	mov    %rsi,%rax
  4017cf:	48 c1 ee 3f          	shr    $0x3f,%rsi
  4017d3:	48 c1 f8 03          	sar    $0x3,%rax
  4017d7:	48 01 c6             	add    %rax,%rsi
  4017da:	48 d1 fe             	sar    %rsi
  4017dd:	74 11                	je     4017f0 <register_tm_clones+0x30>
  4017df:	b8 00 00 00 00       	mov    $0x0,%eax
  4017e4:	48 85 c0             	test   %rax,%rax
  4017e7:	74 07                	je     4017f0 <register_tm_clones+0x30>
  4017e9:	bf 10 40 40 00       	mov    $0x404010,%edi
  4017ee:	ff e0                	jmp    *%rax
  4017f0:	c3                   	ret
  4017f1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4017fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401800 <__do_global_dtors_aux>:
  401800:	f3 0f 1e fa          	endbr64
  401804:	80 3d 05 28 00 00 00 	cmpb   $0x0,0x2805(%rip)        # 404010 <__TMC_END__>
  40180b:	75 13                	jne    401820 <__do_global_dtors_aux+0x20>
  40180d:	55                   	push   %rbp
  40180e:	48 89 e5             	mov    %rsp,%rbp
  401811:	e8 7a ff ff ff       	call   401790 <deregister_tm_clones>
  401816:	c6 05 f3 27 00 00 01 	movb   $0x1,0x27f3(%rip)        # 404010 <__TMC_END__>
  40181d:	5d                   	pop    %rbp
  40181e:	c3                   	ret
  40181f:	90                   	nop
  401820:	c3                   	ret
  401821:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40182c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401830 <frame_dummy>:
  401830:	f3 0f 1e fa          	endbr64
  401834:	eb 8a                	jmp    4017c0 <register_tm_clones>
  401836:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401840 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  401840:	83 7f 70 01          	cmpl   $0x1,0x70(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  401844:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  401847:	7e 77                	jle    4018c0 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  401849:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  40184d:	55                   	push   %rbp
  40184e:	49 89 f2             	mov    %rsi,%r10
  401851:	49 89 d3             	mov    %rdx,%r11
  401854:	53                   	push   %rbx
  401855:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  401858:	48 8b 98 a8 01 00 00 	mov    0x1a8(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  40185f:	b8 01 00 00 00       	mov    $0x1,%eax
  401864:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  401868:	48 63 d0             	movslq %eax,%rdx
  40186b:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  40186e:	85 d2                	test   %edx,%edx
  401870:	40 0f 94 c6          	sete   %sil
  401874:	f6 c2 04             	test   $0x4,%dl
  401877:	75 05                	jne    40187e <pollthreads+0x3e>
  401879:	40 84 f6             	test   %sil,%sil
  40187c:	74 0d                	je     40188b <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  40187e:	49 63 08             	movslq (%r8),%rcx
  401881:	8d 69 01             	lea    0x1(%rcx),%ebp
  401884:	41 89 28             	mov    %ebp,(%r8)
  401887:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  40188b:	83 e2 08             	and    $0x8,%edx
  40188e:	75 05                	jne    401895 <pollthreads+0x55>
  401890:	40 84 f6             	test   %sil,%sil
  401893:	74 1b                	je     4018b0 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  401895:	48 63 17             	movslq (%rdi),%rdx
  401898:	8d 4a 01             	lea    0x1(%rdx),%ecx
  40189b:	89 0f                	mov    %ecx,(%rdi)
  40189d:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  4018a1:	83 c0 01             	add    $0x1,%eax
  4018a4:	41 39 41 70          	cmp    %eax,0x70(%r9)
  4018a8:	7f be                	jg     401868 <pollthreads+0x28>
}
  4018aa:	31 c0                	xor    %eax,%eax
  4018ac:	5b                   	pop    %rbx
  4018ad:	5d                   	pop    %rbp
  4018ae:	c3                   	ret
  4018af:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  4018b0:	83 c0 01             	add    $0x1,%eax
  4018b3:	41 39 41 70          	cmp    %eax,0x70(%r9)
  4018b7:	7f af                	jg     401868 <pollthreads+0x28>
}
  4018b9:	31 c0                	xor    %eax,%eax
  4018bb:	5b                   	pop    %rbx
  4018bc:	5d                   	pop    %rbp
  4018bd:	c3                   	ret
  4018be:	66 90                	xchg   %ax,%ax
  4018c0:	31 c0                	xor    %eax,%eax
  4018c2:	c3                   	ret
  4018c3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4018ce:	66 90                	xchg   %ax,%ax

00000000004018d0 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  4018d0:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4018d3:	48 8b bf c0 00 00 00 	mov    0xc0(%rdi),%rdi
      if (*availableidx == 0) {
  4018da:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4018dd:	48 83 c7 01          	add    $0x1,%rdi
  4018e1:	48 85 ff             	test   %rdi,%rdi
  4018e4:	7e 66                	jle    40194c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  4018e6:	4d 8b 93 a8 00 00 00 	mov    0xa8(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4018ed:	31 c9                	xor    %ecx,%ecx
  4018ef:	45 31 c9             	xor    %r9d,%r9d
  4018f2:	31 c0                	xor    %eax,%eax
  4018f4:	eb 18                	jmp    40190e <findavailable+0x3e>
  4018f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401900:	83 c1 01             	add    $0x1,%ecx
  401903:	48 63 c1             	movslq %ecx,%rax
  401906:	49 89 c1             	mov    %rax,%r9
  401909:	48 39 f8             	cmp    %rdi,%rax
  40190c:	7d 3e                	jge    40194c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  40190e:	48 c1 e0 05          	shl    $0x5,%rax
  401912:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401918:	75 e6                	jne    401900 <findavailable+0x30>
         available[*availableidx] = x;
  40191a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  40191d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401921:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401925:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401928:	41 8b 43 70          	mov    0x70(%r11),%eax
  40192c:	01 c0                	add    %eax,%eax
  40192e:	41 39 c0             	cmp    %eax,%r8d
  401931:	74 19                	je     40194c <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401933:	49 8b bb c0 00 00 00 	mov    0xc0(%r11),%rdi
  40193a:	83 c1 01             	add    $0x1,%ecx
  40193d:	48 63 c1             	movslq %ecx,%rax
  401940:	48 83 c7 01          	add    $0x1,%rdi
  401944:	49 89 c1             	mov    %rax,%r9
  401947:	48 39 f8             	cmp    %rdi,%rax
  40194a:	7c c2                	jl     40190e <findavailable+0x3e>
      if (*availableidx == 0) {
  40194c:	31 c0                	xor    %eax,%eax
  40194e:	45 85 c0             	test   %r8d,%r8d
  401951:	0f 94 c0             	sete   %al
}
  401954:	c3                   	ret
  401955:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401960 <singlewriter2>:
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401960:	53                   	push   %rbx
  if ((data->readcursor % data->threadsize) == 0) {
  401961:	8b 87 58 01 00 00    	mov    0x158(%rdi),%eax
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401967:	48 89 fb             	mov    %rdi,%rbx
  if ((data->readcursor % data->threadsize) == 0) {
  40196a:	8b 4f 70             	mov    0x70(%rdi),%ecx
  40196d:	99                   	cltd
  40196e:	f7 f9                	idiv   %ecx
  401970:	85 d2                	test   %edx,%edx
  401972:	74 14                	je     401988 <singlewriter2+0x28>
  if ((data->writecursor % data->threadsize) == 0) {
  401974:	8b 83 50 01 00 00    	mov    0x150(%rbx),%eax
  40197a:	99                   	cltd
  40197b:	f7 f9                	idiv   %ecx
  40197d:	85 d2                	test   %edx,%edx
  40197f:	74 34                	je     4019b5 <singlewriter2+0x55>
}
  401981:	5b                   	pop    %rbx
  401982:	c3                   	ret
  401983:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    data->currentread++;
  401988:	83 87 80 01 00 00 01 	addl   $0x1,0x180(%rdi)
    data->readcursor = 0;
  40198f:	c7 87 58 01 00 00 00 00 00 00 	movl   $0x0,0x158(%rdi)
  401999:	48 8d 3d 64 06 00 00 	lea    0x664(%rip),%rdi        # 402004 <_IO_stdin_used+0x4>
  4019a0:	e8 9b f6 ff ff       	call   401040 <puts@plt>
  if ((data->writecursor % data->threadsize) == 0) {
  4019a5:	8b 83 50 01 00 00    	mov    0x150(%rbx),%eax
  4019ab:	8b 4b 70             	mov    0x70(%rbx),%ecx
  4019ae:	99                   	cltd
  4019af:	f7 f9                	idiv   %ecx
  4019b1:	85 d2                	test   %edx,%edx
  4019b3:	75 cc                	jne    401981 <singlewriter2+0x21>
    data->currentwrite++;
  4019b5:	83 83 84 01 00 00 01 	addl   $0x1,0x184(%rbx)
  4019bc:	48 8d 3d 4b 06 00 00 	lea    0x64b(%rip),%rdi        # 40200e <_IO_stdin_used+0xe>
    data->writecursor = 0;
  4019c3:	c7 83 50 01 00 00 00 00 00 00 	movl   $0x0,0x150(%rbx)
}
  4019cd:	5b                   	pop    %rbx
  4019ce:	e9 6d f6 ff ff       	jmp    401040 <puts@plt>
  4019d3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4019de:	66 90                	xchg   %ax,%ax

00000000004019e0 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  4019e0:	41 55                	push   %r13
  4019e2:	49 89 d5             	mov    %rdx,%r13
  4019e5:	41 54                	push   %r12
  4019e7:	49 89 cc             	mov    %rcx,%r12
  4019ea:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  4019eb:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  4019ee:	48 89 fd             	mov    %rdi,%rbp
  4019f1:	53                   	push   %rbx
  4019f2:	48 89 f3             	mov    %rsi,%rbx
  4019f5:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  4019f9:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  4019fd:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401a06:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401a0b:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401a0d:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401a15:	8b 81 64 01 00 00    	mov    0x164(%rcx),%eax
  int writers = 0;
  401a1b:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401a23:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401a2b:	83 c0 01             	add    $0x1,%eax
  401a2e:	99                   	cltd
  401a2f:	f7 7f 70             	idivl  0x70(%rdi)
  401a32:	89 91 64 01 00 00    	mov    %edx,0x164(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401a38:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401a3d:	4c 89 e9             	mov    %r13,%rcx
  401a40:	e8 8b fe ff ff       	call   4018d0 <findavailable>
  if (fill == 1) {
  401a45:	83 f8 01             	cmp    $0x1,%eax
  401a48:	0f 84 4c 01 00 00    	je     401b9a <singlewriter+0x1ba>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401a4e:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401a53:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401a58:	4c 89 e2             	mov    %r12,%rdx
  401a5b:	4c 89 ee             	mov    %r13,%rsi
  401a5e:	48 89 ef             	mov    %rbp,%rdi
  401a61:	e8 da fd ff ff       	call   401840 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401a66:	4c 63 44 24 0c       	movslq 0xc(%rsp),%r8
  401a6b:	45 85 c0             	test   %r8d,%r8d
  401a6e:	0f 8e 4d 01 00 00    	jle    401bc1 <singlewriter+0x1e1>
  401a74:	44 8b 4c 24 14       	mov    0x14(%rsp),%r9d
          if (assignedchunk == availableidx) {
  401a79:	31 c9                	xor    %ecx,%ecx
  401a7b:	eb 5b                	jmp    401ad8 <singlewriter+0xf8>
  401a7d:	0f 1f 00             	nopl   (%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401a80:	48 8b 04 cb          	mov    (%rbx,%rcx,8),%rax
          int thread = readyreaders[x];
  401a84:	49 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%rdx
  401a89:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401a8c:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401a90:	48 c1 e0 05          	shl    $0x5,%rax
  401a94:	48 03 85 a8 00 00 00 	add    0xa8(%rbp),%rax
          int thread = readyreaders[x];
  401a9b:	48 89 d7             	mov    %rdx,%rdi
          data->threads[thread].start = start;
  401a9e:	66 0f 6e 00          	movd   (%rax),%xmm0
  401aa2:	66 0f 6e 48 08       	movd   0x8(%rax),%xmm1
          data->threads[thread].reading = chunk;
  401aa7:	48 69 d2 88 01 00 00 	imul   $0x188,%rdx,%rdx
          chunk->available = READING;
  401aae:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
          data->threads[thread].reading = chunk;
  401ab5:	48 03 55 30          	add    0x30(%rbp),%rdx
          data->threads[thread].start = start;
  401ab9:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401abd:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
          chunk->owner = thread;
  401ac4:	89 78 14             	mov    %edi,0x14(%rax)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401ac7:	83 8a d0 00 00 00 10 	orl    $0x10,0xd0(%rdx)
          data->threads[thread].start = start;
  401ace:	66 0f d6 42 14       	movq   %xmm0,0x14(%rdx)
        for (int x = 0; x < readers ; x++) {
  401ad3:	49 39 c8             	cmp    %rcx,%r8
  401ad6:	74 07                	je     401adf <singlewriter+0xff>
  401ad8:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401ada:	4c 39 c9             	cmp    %r9,%rcx
  401add:	75 a1                	jne    401a80 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401adf:	44 8b 4c 24 10       	mov    0x10(%rsp),%r9d
  401ae4:	45 85 c9             	test   %r9d,%r9d
  401ae7:	7e 70                	jle    401b59 <singlewriter+0x179>
                if (assignedchunk  == availableidx) {
  401ae9:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
  401aee:	41 01 f1             	add    %esi,%r9d
  401af1:	eb 61                	jmp    401b54 <singlewriter+0x174>
  401af3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401af8:	8d 7e 01             	lea    0x1(%rsi),%edi
  401afb:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401afe:	49 63 14 24          	movslq (%r12),%rdx
   for (int x = 0; x < writers ; x++) {
  401b02:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b06:	48 8b 04 f3          	mov    (%rbx,%rsi,8),%rax
          int thread = readywriters[x];
  401b0a:	48 89 d1             	mov    %rdx,%rcx
          data->threads[thread].writing = chunk;
  401b0d:	48 69 d2 88 01 00 00 	imul   $0x188,%rdx,%rdx
  401b14:	48 03 55 30          	add    0x30(%rbp),%rdx
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b18:	48 c1 e0 05          	shl    $0x5,%rax
  401b1c:	48 03 85 a8 00 00 00 	add    0xa8(%rbp),%rax
          data->threads[thread].publishstart = start;
  401b23:	66 0f 6e 00          	movd   (%rax),%xmm0
  401b27:	66 0f 6e 50 08       	movd   0x8(%rax),%xmm2
      chunk->available = WRITING;
  401b2c:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
          data->threads[thread].writing = chunk;
  401b33:	48 89 82 b8 00 00 00 	mov    %rax,0xb8(%rdx)
          data->threads[thread].publishstart = start;
  401b3a:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          chunk->owner = thread;
  401b3e:	89 48 14             	mov    %ecx,0x14(%rax)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401b41:	83 8a d0 00 00 00 20 	orl    $0x20,0xd0(%rdx)
          data->threads[thread].publishstart = start;
  401b48:	66 0f d6 42 40       	movq   %xmm0,0x40(%rdx)
   for (int x = 0; x < writers ; x++) {
  401b4d:	44 39 cf             	cmp    %r9d,%edi
  401b50:	74 07                	je     401b59 <singlewriter+0x179>
  401b52:	89 fe                	mov    %edi,%esi
                if (assignedchunk  == availableidx) {
  401b54:	41 39 f0             	cmp    %esi,%r8d
  401b57:	75 9f                	jne    401af8 <singlewriter+0x118>
      for (int x = 0; x < data->threadsize ; x++) {
  401b59:	8b 7d 70             	mov    0x70(%rbp),%edi
  401b5c:	85 ff                	test   %edi,%edi
  401b5e:	7e 38                	jle    401b98 <singlewriter+0x1b8>
        if (data->threads[x].newmask != 0) {
  401b60:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401b64:	31 d2                	xor    %edx,%edx
  401b66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401b70:	48 63 ca             	movslq %edx,%rcx
  401b73:	48 69 c1 88 01 00 00 	imul   $0x188,%rcx,%rax
  401b7a:	4c 01 c0             	add    %r8,%rax
  401b7d:	8b b0 d0 00 00 00    	mov    0xd0(%rax),%esi
  401b83:	85 f6                	test   %esi,%esi
  401b85:	74 31                	je     401bb8 <singlewriter+0x1d8>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401b87:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401b8b:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401b8e:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401b91:	8b 7d 70             	mov    0x70(%rbp),%edi
  401b94:	39 fa                	cmp    %edi,%edx
  401b96:	7c d8                	jl     401b70 <singlewriter+0x190>
  return 0;
  401b98:	31 c0                	xor    %eax,%eax
}
  401b9a:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401b9f:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401ba8:	75 1e                	jne    401bc8 <singlewriter+0x1e8>
  401baa:	48 83 c4 28          	add    $0x28,%rsp
  401bae:	5b                   	pop    %rbx
  401baf:	5d                   	pop    %rbp
  401bb0:	41 5c                	pop    %r12
  401bb2:	41 5d                	pop    %r13
  401bb4:	c3                   	ret
  401bb5:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401bb8:	83 c2 01             	add    $0x1,%edx
  401bbb:	39 fa                	cmp    %edi,%edx
  401bbd:	7c b1                	jl     401b70 <singlewriter+0x190>
  401bbf:	eb d7                	jmp    401b98 <singlewriter+0x1b8>
      int assignedchunk = 0;
  401bc1:	31 f6                	xor    %esi,%esi
  401bc3:	e9 17 ff ff ff       	jmp    401adf <singlewriter+0xff>
}
  401bc8:	e8 93 f4 ff ff       	call   401060 <__stack_chk_fail@plt>
  401bcd:	0f 1f 00             	nopl   (%rax)

0000000000401bd0 <threadwork>:
int * threadwork(struct Data * data) {
  401bd0:	55                   	push   %rbp
  401bd1:	48 8d 35 41 04 00 00 	lea    0x441(%rip),%rsi        # 402019 <_IO_stdin_used+0x19>
  401bd8:	53                   	push   %rbx
  401bd9:	48 89 fb             	mov    %rdi,%rbx
  401bdc:	48 83 ec 08          	sub    $0x8,%rsp
  int buffer = 1 * (data->main->currentread % data->threadsize) + 2 * data->oreadcursor + 3 * data->readcursor + 4 * data->threadindex;
  401be0:	8b 87 58 01 00 00    	mov    0x158(%rdi),%eax
  401be6:	8b 97 60 01 00 00    	mov    0x160(%rdi),%edx
  401bec:	44 8b 47 6c          	mov    0x6c(%rdi),%r8d
        data->freq++;
  401bf0:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  int buffer = 1 * (data->main->currentread % data->threadsize) + 2 * data->oreadcursor + 3 * data->readcursor + 4 * data->threadindex;
  401bf5:	8d 04 40             	lea    (%rax,%rax,2),%eax
  401bf8:	8d 04 50             	lea    (%rax,%rdx,2),%eax
  401bfb:	42 8d 2c 80          	lea    (%rax,%r8,4),%ebp
  401bff:	48 8b 47 28          	mov    0x28(%rdi),%rax
  401c03:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401c09:	99                   	cltd
  401c0a:	f7 7f 70             	idivl  0x70(%rdi)
  401c0d:	bf 01 00 00 00       	mov    $0x1,%edi
  401c12:	31 c0                	xor    %eax,%eax
  401c14:	01 d5                	add    %edx,%ebp
  401c16:	44 89 c2             	mov    %r8d,%edx
  401c19:	89 e9                	mov    %ebp,%ecx
        data->main->works[buffer].available = 0;
  401c1b:	48 63 ed             	movslq %ebp,%rbp
  401c1e:	e8 6d f4 ff ff       	call   401090 <__printf_chk@plt>
  401c23:	48 8b 53 28          	mov    0x28(%rbx),%rdx
  401c27:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
  401c2f:	48 29 e8             	sub    %rbp,%rax
  401c32:	48 8b 4a 78          	mov    0x78(%rdx),%rcx
  401c36:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
  401c3a:	c7 40 04 00 00 00 00 	movl   $0x0,0x4(%rax)
         __atomic_fetch_add(&data->main->readcursor, 1, __ATOMIC_ACQUIRE);
  401c41:	f0 83 82 58 01 00 00 01 	lock addl $0x1,0x158(%rdx)
          data->main->works[(data->main->currentwrite % data->threadsize) + data->owritecursor + data->writecursor].available = 1;
  401c49:	48 8b 4b 28          	mov    0x28(%rbx),%rcx
  401c4d:	8b 81 84 01 00 00    	mov    0x184(%rcx),%eax
  401c53:	48 8b 71 78          	mov    0x78(%rcx),%rsi
  401c57:	99                   	cltd
  401c58:	f7 7b 70             	idivl  0x70(%rbx)
  401c5b:	8b 83 50 01 00 00    	mov    0x150(%rbx),%eax
  401c61:	03 83 5c 01 00 00    	add    0x15c(%rbx),%eax
  401c67:	01 c2                	add    %eax,%edx
  401c69:	48 63 d2             	movslq %edx,%rdx
  401c6c:	48 8d 04 d5 00 00 00 00 	lea    0x0(,%rdx,8),%rax
  401c74:	48 29 d0             	sub    %rdx,%rax
  401c77:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
  401c7b:	c7 40 04 01 00 00 00 	movl   $0x1,0x4(%rax)
          data->freq_writes++;
  401c82:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
        __atomic_fetch_add(&data->main->writecursor, 1, __ATOMIC_ACQUIRE);
  401c87:	f0 83 81 50 01 00 00 01 	lock addl $0x1,0x150(%rcx)
}
  401c8f:	48 83 c4 08          	add    $0x8,%rsp
  401c93:	5b                   	pop    %rbx
  401c94:	5d                   	pop    %rbp
  401c95:	c3                   	ret
  401c96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401ca0 <work>:
void * work(void * arg) {
  401ca0:	41 56                	push   %r14
  401ca2:	48 8d 35 7e 03 00 00 	lea    0x37e(%rip),%rsi        # 402027 <_IO_stdin_used+0x27>
  401ca9:	31 c0                	xor    %eax,%eax
  401cab:	41 55                	push   %r13
  401cad:	41 54                	push   %r12
  401caf:	55                   	push   %rbp
  401cb0:	53                   	push   %rbx
  401cb1:	8b 57 6c             	mov    0x6c(%rdi),%edx
  401cb4:	48 89 fb             	mov    %rdi,%rbx
  401cb7:	bf 01 00 00 00       	mov    $0x1,%edi
  401cbc:	e8 cf f3 ff ff       	call   401090 <__printf_chk@plt>
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  401cc1:	8b 43 6c             	mov    0x6c(%rbx),%eax
  401cc4:	48 8d 35 6f 03 00 00 	lea    0x36f(%rip),%rsi        # 40203a <_IO_stdin_used+0x3a>
  401ccb:	bf 01 00 00 00       	mov    $0x1,%edi
  int bucketstart = data->bucketstart;
  401cd0:	44 8b b3 a0 00 00 00 	mov    0xa0(%rbx),%r14d
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  401cd7:	8d 50 01             	lea    0x1(%rax),%edx
  401cda:	31 c0                	xor    %eax,%eax
  int bucketlim = ((data->threadindex + 1) * data->buckets) ;
  401cdc:	0f af 93 98 00 00 00 	imul   0x98(%rbx),%edx
  401ce3:	e8 a8 f3 ff ff       	call   401090 <__printf_chk@plt>
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  401ce8:	48 8b 83 c0 00 00 00 	mov    0xc0(%rbx),%rax
  401cef:	be 08 00 00 00       	mov    $0x8,%esi
  401cf4:	48 8d 78 01          	lea    0x1(%rax),%rdi
  401cf8:	e8 83 f3 ff ff       	call   401080 <calloc@plt>
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  401cfd:	4c 63 6b 70          	movslq 0x70(%rbx),%r13
  401d01:	be 04 00 00 00       	mov    $0x4,%esi
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  401d06:	48 89 c5             	mov    %rax,%rbp
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  401d09:	4c 89 ef             	mov    %r13,%rdi
  401d0c:	e8 6f f3 ff ff       	call   401080 <calloc@plt>
  int * readywriters = calloc(data->threadsize, sizeof(int));
  401d11:	be 04 00 00 00       	mov    $0x4,%esi
  401d16:	4c 89 ef             	mov    %r13,%rdi
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  401d19:	49 89 c4             	mov    %rax,%r12
  int * readywriters = calloc(data->threadsize, sizeof(int));
  401d1c:	e8 5f f3 ff ff       	call   401080 <calloc@plt>
  while (data->running == 1) {
  401d21:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  data->workindex = bucketstart;
  401d25:	44 89 73 5c          	mov    %r14d,0x5c(%rbx)
  while (data->running == 1) {
  401d29:	75 49                	jne    401d74 <work+0xd4>
  401d2b:	49 89 c5             	mov    %rax,%r13
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  401d2e:	4c 8d b3 30 01 00 00 	lea    0x130(%rbx),%r14
  401d35:	0f 1f 00             	nopl   (%rax)
    if (data->threadindex == 0) {
  401d38:	8b 43 6c             	mov    0x6c(%rbx),%eax
  401d3b:	85 c0                	test   %eax,%eax
  401d3d:	75 59                	jne    401d98 <work+0xf8>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  401d3f:	4c 89 f6             	mov    %r14,%rsi
  401d42:	bf 04 00 00 00       	mov    $0x4,%edi
  401d47:	e8 04 f3 ff ff       	call   401050 <clock_gettime@plt>
      singlewriter2(data, available, readyreaders, readywriters);
  401d4c:	4c 89 e9             	mov    %r13,%rcx
  401d4f:	4c 89 e2             	mov    %r12,%rdx
  401d52:	48 89 ee             	mov    %rbp,%rsi
  401d55:	48 89 df             	mov    %rbx,%rdi
  401d58:	e8 03 fc ff ff       	call   401960 <singlewriter2>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swend);
  401d5d:	48 8d b3 40 01 00 00 	lea    0x140(%rbx),%rsi
  401d64:	bf 04 00 00 00       	mov    $0x4,%edi
  401d69:	e8 e2 f2 ff ff       	call   401050 <clock_gettime@plt>
  while (data->running == 1) {
  401d6e:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  401d72:	74 c4                	je     401d38 <work+0x98>
  401d74:	8b 53 6c             	mov    0x6c(%rbx),%edx
  401d77:	48 8d 35 ca 02 00 00 	lea    0x2ca(%rip),%rsi        # 402048 <_IO_stdin_used+0x48>
  401d7e:	bf 01 00 00 00       	mov    $0x1,%edi
  401d83:	31 c0                	xor    %eax,%eax
  401d85:	e8 06 f3 ff ff       	call   401090 <__printf_chk@plt>
}
  401d8a:	5b                   	pop    %rbx
  401d8b:	5d                   	pop    %rbp
  401d8c:	41 5c                	pop    %r12
  401d8e:	41 5d                	pop    %r13
  401d90:	41 5e                	pop    %r14
  401d92:	c3                   	ret
  401d93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      threadwork(data);
  401d98:	48 89 df             	mov    %rbx,%rdi
  401d9b:	e8 30 fe ff ff       	call   401bd0 <threadwork>
  while (data->running == 1) {
  401da0:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  401da4:	74 92                	je     401d38 <work+0x98>
  401da6:	eb cc                	jmp    401d74 <work+0xd4>
  401da8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000401db0 <work2>:
  while (data->running == 1) {
  401db0:	eb 0b                	jmp    401dbd <work2+0xd>
  401db2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  401db8:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  401dbd:	83 7f 64 01          	cmpl   $0x1,0x64(%rdi)
  401dc1:	74 f5                	je     401db8 <work2+0x8>
}
  401dc3:	c3                   	ret

Disassembly of section .fini:

0000000000401dc4 <_fini>:
  401dc4:	f3 0f 1e fa          	endbr64
  401dc8:	48 83 ec 08          	sub    $0x8,%rsp
  401dcc:	48 83 c4 08          	add    $0x8,%rsp
  401dd0:	c3                   	ret
