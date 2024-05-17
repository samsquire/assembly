
stream2-workqueue:     file format elf64-x86-64


Disassembly of section .init:

0000000000401000 <_init>:
  401000:	f3 0f 1e fa          	endbr64
  401004:	48 83 ec 08          	sub    $0x8,%rsp
  401008:	48 8b 05 e9 3f 00 00 	mov    0x3fe9(%rip),%rax        # 404ff8 <__gmon_start__@Base>
  40100f:	48 85 c0             	test   %rax,%rax
  401012:	74 02                	je     401016 <_init+0x16>
  401014:	ff d0                	call   *%rax
  401016:	48 83 c4 08          	add    $0x8,%rsp
  40101a:	c3                   	ret

Disassembly of section .plt:

0000000000401020 <__snprintf_chk@plt-0x10>:
  401020:	ff 35 42 3f 00 00    	push   0x3f42(%rip)        # 404f68 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 44 3f 00 00    	jmp    *0x3f44(%rip)        # 404f70 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <__snprintf_chk@plt>:
  401030:	ff 25 42 3f 00 00    	jmp    *0x3f42(%rip)        # 404f78 <__snprintf_chk@GLIBC_2.3.4>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <pthread_setaffinity_np@plt>:
  401040:	ff 25 3a 3f 00 00    	jmp    *0x3f3a(%rip)        # 404f80 <pthread_setaffinity_np@GLIBC_2.34>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <puts@plt>:
  401050:	ff 25 32 3f 00 00    	jmp    *0x3f32(%rip)        # 404f88 <puts@GLIBC_2.2.5>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <clock_gettime@plt>:
  401060:	ff 25 2a 3f 00 00    	jmp    *0x3f2a(%rip)        # 404f90 <clock_gettime@GLIBC_2.17>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <fclose@plt>:
  401070:	ff 25 22 3f 00 00    	jmp    *0x3f22(%rip)        # 404f98 <fclose@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <__stack_chk_fail@plt>:
  401080:	ff 25 1a 3f 00 00    	jmp    *0x3f1a(%rip)        # 404fa0 <__stack_chk_fail@GLIBC_2.4>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <nanosleep@plt>:
  401090:	ff 25 12 3f 00 00    	jmp    *0x3f12(%rip)        # 404fa8 <nanosleep@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <fputs@plt>:
  4010a0:	ff 25 0a 3f 00 00    	jmp    *0x3f0a(%rip)        # 404fb0 <fputs@GLIBC_2.2.5>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <memset@plt>:
  4010b0:	ff 25 02 3f 00 00    	jmp    *0x3f02(%rip)        # 404fb8 <memset@GLIBC_2.2.5>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <calloc@plt>:
  4010c0:	ff 25 fa 3e 00 00    	jmp    *0x3efa(%rip)        # 404fc0 <calloc@GLIBC_2.2.5>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010d0 <__printf_chk@plt>:
  4010d0:	ff 25 f2 3e 00 00    	jmp    *0x3ef2(%rip)        # 404fc8 <__printf_chk@GLIBC_2.3.4>
  4010d6:	68 0a 00 00 00       	push   $0xa
  4010db:	e9 40 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010e0 <pthread_create@plt>:
  4010e0:	ff 25 ea 3e 00 00    	jmp    *0x3eea(%rip)        # 404fd0 <pthread_create@GLIBC_2.34>
  4010e6:	68 0b 00 00 00       	push   $0xb
  4010eb:	e9 30 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010f0 <fopen@plt>:
  4010f0:	ff 25 e2 3e 00 00    	jmp    *0x3ee2(%rip)        # 404fd8 <fopen@GLIBC_2.2.5>
  4010f6:	68 0c 00 00 00       	push   $0xc
  4010fb:	e9 20 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401100 <posix_memalign@plt>:
  401100:	ff 25 da 3e 00 00    	jmp    *0x3eda(%rip)        # 404fe0 <posix_memalign@GLIBC_2.2.5>
  401106:	68 0d 00 00 00       	push   $0xd
  40110b:	e9 10 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401110 <pthread_join@plt>:
  401110:	ff 25 d2 3e 00 00    	jmp    *0x3ed2(%rip)        # 404fe8 <pthread_join@GLIBC_2.34>
  401116:	68 0e 00 00 00       	push   $0xe
  40111b:	e9 00 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

0000000000401120 <main>:
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
}

int main(int argc, char **argv) {
  401120:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  401122:	ba 08 00 00 00       	mov    $0x8,%edx
  401127:	bf 01 00 00 00       	mov    $0x1,%edi
  40112c:	48 8d 35 03 1f 00 00 	lea    0x1f03(%rip),%rsi        # 403036 <_IO_stdin_used+0x36>
  401133:	41 56                	push   %r14
  401135:	41 55                	push   %r13
  long offset = 0;
  long chunkslen = 0xffffffff;
  long worksize = chunkslen * worksize_each;
  int buckets = worksize / threadsize;
  long chunksize = ceil((double) worksize / (double) chunkslen);
  char *works = calloc(worksize, sizeof(char));
  401137:	41 bd ff ff ff ff    	mov    $0xffffffff,%r13d
int main(int argc, char **argv) {
  40113d:	41 54                	push   %r12
  40113f:	55                   	push   %rbp
  401140:	53                   	push   %rbx
  401141:	48 81 ec a8 00 00 00 	sub    $0xa8,%rsp
  401148:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401151:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  401159:	31 c0                	xor    %eax,%eax
  40115b:	e8 70 ff ff ff       	call   4010d0 <__printf_chk@plt>
  401160:	ba 04 00 00 00       	mov    $0x4,%edx
  401165:	48 8d 35 dc 1e 00 00 	lea    0x1edc(%rip),%rsi        # 403048 <_IO_stdin_used+0x48>
  40116c:	31 c0                	xor    %eax,%eax
  40116e:	bf 01 00 00 00       	mov    $0x1,%edi
  401173:	e8 58 ff ff ff       	call   4010d0 <__printf_chk@plt>
  401178:	ba 20 00 00 00       	mov    $0x20,%edx
  40117d:	48 8d 35 c0 1e 00 00 	lea    0x1ec0(%rip),%rsi        # 403044 <_IO_stdin_used+0x44>
  401184:	31 c0                	xor    %eax,%eax
  401186:	bf 01 00 00 00       	mov    $0x1,%edi
  40118b:	e8 40 ff ff ff       	call   4010d0 <__printf_chk@plt>
  401190:	ba 08 00 00 00       	mov    $0x8,%edx
  401195:	48 8d 35 bb 1e 00 00 	lea    0x1ebb(%rip),%rsi        # 403057 <_IO_stdin_used+0x57>
  40119c:	31 c0                	xor    %eax,%eax
  40119e:	bf 01 00 00 00       	mov    $0x1,%edi
  4011a3:	e8 28 ff ff ff       	call   4010d0 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  4011a8:	be 08 00 00 00       	mov    $0x8,%esi
  4011ad:	bf 08 00 00 00       	mov    $0x8,%edi
  4011b2:	e8 09 ff ff ff       	call   4010c0 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  4011b7:	be 38 00 00 00       	mov    $0x38,%esi
  4011bc:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  4011c1:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  4011c6:	e8 f5 fe ff ff       	call   4010c0 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011cb:	be 00 20 00 00       	mov    $0x2000,%esi
  4011d0:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  4011d5:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011da:	e8 e1 fe ff ff       	call   4010c0 <calloc@plt>
  char *works = calloc(worksize, sizeof(char));
  4011df:	be 01 00 00 00       	mov    $0x1,%esi
  4011e4:	4c 89 ef             	mov    %r13,%rdi
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011e7:	49 89 c4             	mov    %rax,%r12
  char *works = calloc(worksize, sizeof(char));
  4011ea:	e8 d1 fe ff ff       	call   4010c0 <calloc@plt>
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  4011ef:	4c 89 ea             	mov    %r13,%rdx
  4011f2:	be ff ff ff ff       	mov    $0xffffffff,%esi
  4011f7:	48 89 c7             	mov    %rax,%rdi
  4011fa:	48 89 c3             	mov    %rax,%rbx
  4011fd:	e8 ae fe ff ff       	call   4010b0 <memset@plt>
  401202:	4c 89 ea             	mov    %r13,%rdx
  401205:	bf 01 00 00 00       	mov    $0x1,%edi
  40120a:	31 c0                	xor    %eax,%eax
  40120c:	48 8d 35 59 1e 00 00 	lea    0x1e59(%rip),%rsi        # 40306c <_IO_stdin_used+0x6c>
  401213:	e8 b8 fe ff ff       	call   4010d0 <__printf_chk@plt>
  memset(works, -1, worksize);
  printf("Buffer size %ld\n", worksize);
  int chunkindex = 0;
  int * readcursors = calloc(threadsize, sizeof(int));
  int * writecursors = calloc(threadsize, sizeof(int));
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  401218:	be 20 00 00 00       	mov    $0x20,%esi
  40121d:	bf 64 00 00 00       	mov    $0x64,%edi
  401222:	e8 99 fe ff ff       	call   4010c0 <calloc@plt>
  401227:	31 d2                	xor    %edx,%edx
  401229:	bf 01 00 00 00       	mov    $0x1,%edi
  40122e:	48 8d 35 48 1e 00 00 	lea    0x1e48(%rip),%rsi        # 40307d <_IO_stdin_used+0x7d>
  401235:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  40123a:	31 c0                	xor    %eax,%eax
  40123c:	e8 8f fe ff ff       	call   4010d0 <__printf_chk@plt>
  401241:	4c 89 ea             	mov    %r13,%rdx
  401244:	bf 01 00 00 00       	mov    $0x1,%edi
  401249:	31 c0                	xor    %eax,%eax
  40124b:	48 8d 35 37 1e 00 00 	lea    0x1e37(%rip),%rsi        # 403089 <_IO_stdin_used+0x89>
  401252:	e8 79 fe ff ff       	call   4010d0 <__printf_chk@plt>
   // works[i].taskindex = 2;
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  401257:	be 04 00 00 00       	mov    $0x4,%esi
  40125c:	bf 08 00 00 00       	mov    $0x8,%edi
  401261:	e8 5a fe ff ff       	call   4010c0 <calloc@plt>
  
  long * globalwrite;
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  401266:	ba 00 02 00 00       	mov    $0x200,%edx
  40126b:	48 8d 7c 24 68       	lea    0x68(%rsp),%rdi
  401270:	be 80 00 00 00       	mov    $0x80,%esi
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  401275:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  40127a:	e8 81 fe ff ff       	call   401100 <posix_memalign@plt>
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  40127f:	be 0c 00 00 00       	mov    $0xc,%esi
  401284:	bf 08 00 00 00       	mov    $0x8,%edi
  401289:	85 c0                	test   %eax,%eax
  40128b:	b8 00 00 00 00       	mov    $0x0,%eax
  401290:	48 0f 44 44 24 68    	cmove  0x68(%rsp),%rax
    
    data[x].coroutines = cos;
    for (int y = 0; y < 10; y++ ) {
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
      cos[y].data = codata;
      cos[y].eip = (uint64_t)coroutine_func;
  401296:	45 31 f6             	xor    %r14d,%r14d
  401299:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  40129e:	e8 1d fe ff ff       	call   4010c0 <calloc@plt>
  data[0].works = works;
  4012a3:	49 89 5c 24 70       	mov    %rbx,0x70(%r12)
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  4012a8:	be 14 00 00 00       	mov    $0x14,%esi
  4012ad:	bf 00 e1 f5 05       	mov    $0x5f5e100,%edi
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  4012b2:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  4012b7:	e8 04 fe ff ff       	call   4010c0 <calloc@plt>
  struct Access * writes = calloc(accesssize, sizeof(struct Access));
  4012bc:	be 14 00 00 00       	mov    $0x14,%esi
  4012c1:	bf 00 e1 f5 05       	mov    $0x5f5e100,%edi
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  4012c6:	48 89 c3             	mov    %rax,%rbx
  struct Access * writes = calloc(accesssize, sizeof(struct Access));
  4012c9:	e8 f2 fd ff ff       	call   4010c0 <calloc@plt>
  4012ce:	66 48 0f 6e eb       	movq   %rbx,%xmm5
  struct Scheduler * scheduler = calloc(1, sizeof(struct Scheduler));
  4012d3:	be 08 00 00 00       	mov    $0x8,%esi
  4012d8:	bf 01 00 00 00       	mov    $0x1,%edi
  4012dd:	66 48 0f 6e f0       	movq   %rax,%xmm6
  4012e2:	66 0f 6c ee          	punpcklqdq %xmm6,%xmm5
  4012e6:	0f 29 6c 24 40       	movaps %xmm5,0x40(%rsp)
  4012eb:	e8 d0 fd ff ff       	call   4010c0 <calloc@plt>
  4012f0:	4c 89 64 24 10       	mov    %r12,0x10(%rsp)
      cos[y].eip = (uint64_t)coroutine_func;
  4012f5:	48 c7 c5 60 1c 40 00 	mov    $0x401c60,%rbp
  struct Scheduler * scheduler = calloc(1, sizeof(struct Scheduler));
  4012fc:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  for (int x = 0; x < threadsize ; x++) {
  401301:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    struct Coroutine * cos = calloc(10, sizeof(struct Coroutine));
  401308:	be 20 00 00 00       	mov    $0x20,%esi
  40130d:	bf 0a 00 00 00       	mov    $0xa,%edi
  401312:	44 89 74 24 08       	mov    %r14d,0x8(%rsp)
  401317:	45 89 f5             	mov    %r14d,%r13d
  40131a:	e8 a1 fd ff ff       	call   4010c0 <calloc@plt>
    data[x].coroutines = cos;
  40131f:	49 89 84 24 c0 03 00 00 	mov    %rax,0x3c0(%r12)
    for (int y = 0; y < 10; y++ ) {
  401327:	4c 8d 78 10          	lea    0x10(%rax),%r15
  40132b:	48 8d 98 50 01 00 00 	lea    0x150(%rax),%rbx
  401332:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
  401338:	be 04 00 00 00       	mov    $0x4,%esi
  40133d:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int y = 0; y < 10; y++ ) {
  401342:	49 83 c7 20          	add    $0x20,%r15
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
  401346:	e8 75 fd ff ff       	call   4010c0 <calloc@plt>
      cos[y].eip = (uint64_t)coroutine_func;
  40134b:	49 89 6f e0          	mov    %rbp,-0x20(%r15)
      cos[y].data = codata;
  40134f:	49 89 47 e8          	mov    %rax,-0x18(%r15)
    for (int y = 0; y < 10; y++ ) {
  401353:	4c 39 fb             	cmp    %r15,%rbx
  401356:	75 e0                	jne    401338 <main+0x218>
    }
    data[x].scheduler = scheduler; 
  401358:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    data[x].reads = reads;
  40135d:	66 0f 6f 4c 24 40    	movdqa 0x40(%rsp),%xmm1
    data[x].writes = writes; 
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t)); 
  401363:	be 80 00 00 00       	mov    $0x80,%esi
  401368:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0; x < threadsize ; x++) {
  40136d:	49 81 c4 00 04 00 00 	add    $0x400,%r12
    data[x].scheduler = scheduler; 
  401374:	49 89 44 24 c8       	mov    %rax,-0x38(%r12)
    data[x].reads = reads;
  401379:	41 0f 29 4c 24 a0    	movaps %xmm1,-0x60(%r12)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t)); 
  40137f:	e8 3c fd ff ff       	call   4010c0 <calloc@plt>
  401384:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    CPU_SET(cpu += 1, data[x].cpu_set);
  401388:	ba 01 00 00 00       	mov    $0x1,%edx
  40138d:	48 8d 35 9c 1e 00 00 	lea    0x1e9c(%rip),%rsi        # 403230 <_IO_stdin_used+0x230>
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t)); 
  401394:	49 89 84 24 78 fc ff ff 	mov    %rax,-0x388(%r12)
  40139c:	bf 01 00 00 00       	mov    $0x1,%edi
  4013a1:	8d 4b 01             	lea    0x1(%rbx),%ecx
    CPU_SET(cpu += 1, data[x].cpu_set);
  4013a4:	48 d3 e2             	shl    %cl,%rdx
  4013a7:	48 09 10             	or     %rdx,(%rax)
  4013aa:	44 89 ea             	mov    %r13d,%edx
  4013ad:	31 c0                	xor    %eax,%eax
  4013af:	e8 1c fd ff ff       	call   4010d0 <__printf_chk@plt>
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].bucketstart = x * buckets ;
  4013b4:	89 d8                	mov    %ebx,%eax
    data[x].globalwrite = globalwrite;
    data[x].loglevel = debug;
    data[x].running = 2;
    data[x].threadindex = x;
  4013b6:	45 89 ac 24 64 fc ff ff 	mov    %r13d,-0x39c(%r12)
    data[x].chunksize = chunksize;
    data[x].chunkslen = chunkslen;
    data[x].newmask = 0;
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].mystream = 1 + (x / 4);
  4013be:	41 c1 fd 02          	sar    $0x2,%r13d
    data[x].bucketstart = x * buckets ;
  4013c2:	c1 e0 1d             	shl    $0x1d,%eax
    data[x].mystream = 1 + (x / 4);
  4013c5:	41 83 c5 01          	add    $0x1,%r13d
    data[x].loglevel = debug;
  4013c9:	41 c7 84 24 80 fc ff ff 00 00 00 00 	movl   $0x0,-0x380(%r12)
    data[x].read = 0;
  4013d5:	66 0f 6f 15 d3 1e 00 00 	movdqa 0x1ed3(%rip),%xmm2        # 4032b0 <_IO_stdin_used+0x2b0>
    data[x].bucketstart = x * buckets ;
  4013dd:	29 d8                	sub    %ebx,%eax
    data[x].chunkslen = chunkslen;
  4013df:	66 0f 6f 1d d9 1e 00 00 	movdqa 0x1ed9(%rip),%xmm3        # 4032c0 <_IO_stdin_used+0x2c0>
    data[x].availables = buckets;
  4013e7:	41 c7 84 24 94 fc ff ff ff ff ff 1f 	movl   $0x1fffffff,-0x36c(%r12)
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4013f3:	be 30 00 00 00       	mov    $0x30,%esi
    data[x].bucketstart = x * buckets ;
  4013f8:	41 89 84 24 98 fc ff ff 	mov    %eax,-0x368(%r12)
    data[x].globalwrite = globalwrite;
  401400:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401405:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].threadsize = threadsize;
  40140a:	41 c7 84 24 68 fc ff ff 08 00 00 00 	movl   $0x8,-0x398(%r12)
    data[x].prevread = threadsize;
  401416:	66 0f 6f 25 b2 1e 00 00 	movdqa 0x1eb2(%rip),%xmm4        # 4032d0 <_IO_stdin_used+0x2d0>
    data[x].globalwrite = globalwrite;
  40141e:	49 89 44 24 80       	mov    %rax,-0x80(%r12)
    data[x].running = 2;
  401423:	48 8b 05 7e 1e 00 00 	mov    0x1e7e(%rip),%rax        # 4032a8 <_IO_stdin_used+0x2a8>
  40142a:	49 89 84 24 5c fc ff ff 	mov    %rax,-0x3a4(%r12)
    data[x].readies = readies;
  401432:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
  401437:	49 89 84 24 20 fc ff ff 	mov    %rax,-0x3e0(%r12)
    data[x].readies[x] = 0;
  40143f:	42 c7 04 b0 00 00 00 00 	movl   $0x0,(%rax,%r14,4)
    data[x].main = &data[0];
  401447:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  for (int x = 0; x < threadsize ; x++) {
  40144c:	49 83 c6 01          	add    $0x1,%r14
    data[x].buckets = buckets;
  401450:	41 c7 84 24 90 fc ff ff ff ff ff 1f 	movl   $0x1fffffff,-0x370(%r12)
    data[x].main = &data[0];
  40145c:	49 89 84 24 28 fc ff ff 	mov    %rax,-0x3d8(%r12)
    data[x].threads = data;
  401464:	49 89 84 24 30 fc ff ff 	mov    %rax,-0x3d0(%r12)
    data[x].freelist = freelist;
  40146c:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    data[x].readcursor = threadsize - 1;
  401471:	41 c7 84 24 00 fe ff ff 07 00 00 00 	movl   $0x7,-0x200(%r12)
    data[x].writecursor = 0;
  40147d:	41 c7 84 24 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%r12)
    data[x].freelist = freelist;
  401489:	49 89 84 24 a0 fc ff ff 	mov    %rax,-0x360(%r12)
    data[x].newmask = 0;
  401491:	41 c7 84 24 c8 fc ff ff 00 00 00 00 	movl   $0x0,-0x338(%r12)
    data[x].mystream = 1 + (x / 4);
  40149d:	45 89 6c 24 8c       	mov    %r13d,-0x74(%r12)
    data[x].thiswrite = threadsize;
  4014a2:	41 c7 84 24 28 ff ff ff 08 00 00 00 	movl   $0x8,-0xd8(%r12)
    data[x].read = 0;
  4014ae:	41 0f 29 94 24 00 fc ff ff 	movaps %xmm2,-0x400(%r12)
    data[x].chunkslen = chunkslen;
  4014b7:	41 0f 11 9c 24 b8 fc ff ff 	movups %xmm3,-0x348(%r12)
    data[x].prevread = threadsize;
  4014c0:	41 0f 11 a4 24 08 ff ff ff 	movups %xmm4,-0xf8(%r12)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4014c9:	e8 f2 fb ff ff       	call   4010c0 <calloc@plt>
    data[x].epochssize = epochs;
    data[x].globalread = globalread;
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  4014ce:	be 30 00 00 00       	mov    $0x30,%esi
  4014d3:	bf 10 27 00 00       	mov    $0x2710,%edi
    data[x].epochssize = epochs;
  4014d8:	41 c7 84 24 20 ff ff ff 80 96 98 00 	movl   $0x989680,-0xe0(%r12)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4014e4:	49 89 84 24 18 ff ff ff 	mov    %rax,-0xe8(%r12)
    data[x].globalread = globalread;
  4014ec:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
  4014f1:	49 89 84 24 48 ff ff ff 	mov    %rax,-0xb8(%r12)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  4014f9:	e8 c2 fb ff ff       	call   4010c0 <calloc@plt>
    data[x].accesssize = accesssize;
  4014fe:	41 c7 44 24 b8 00 e1 f5 05 	movl   $0x5f5e100,-0x48(%r12)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  401507:	49 89 84 24 30 ff ff ff 	mov    %rax,-0xd0(%r12)
  for (int x = 0; x < threadsize ; x++) {
  40150f:	49 83 fe 08          	cmp    $0x8,%r14
  401513:	0f 85 ef fd ff ff    	jne    401308 <main+0x1e8>
  401519:	4c 8b 7c 24 50       	mov    0x50(%rsp),%r15
  40151e:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
  401523:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
  401528:	49 c7 c5 f0 23 40 00 	mov    $0x4023f0,%r13
  40152f:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
  401534:	48 8d 83 c0 01 00 00 	lea    0x1c0(%rbx),%rax
  40153b:	4c 89 e5             	mov    %r12,%rbp
  40153e:	49 89 c6             	mov    %rax,%r14
  401541:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  401548:	48 89 e9             	mov    %rbp,%rcx
  40154b:	48 89 de             	mov    %rbx,%rsi
  40154e:	4c 89 ff             	mov    %r15,%rdi
  401551:	4c 89 ea             	mov    %r13,%rdx
  401554:	e8 87 fb ff ff       	call   4010e0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401559:	48 8b 55 78          	mov    0x78(%rbp),%rdx
  40155d:	49 8b 3f             	mov    (%r15),%rdi
  401560:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  401565:	48 83 c3 38          	add    $0x38,%rbx
  401569:	49 83 c7 08          	add    $0x8,%r15
  40156d:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401574:	e8 c7 fa ff ff       	call   401040 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  401579:	49 39 de             	cmp    %rbx,%r14
  40157c:	75 ca                	jne    401548 <main+0x428>
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  40157e:	48 8d 7c 24 70       	lea    0x70(%rsp),%rdi
  struct timespec time = {
  401583:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
  401588:	4c 8d 6c 24 60       	lea    0x60(%rsp),%r13
  40158d:	66 0f 6f 05 4b 1d 00 00 	movdqa 0x1d4b(%rip),%xmm0        # 4032e0 <_IO_stdin_used+0x2e0>
  nanosleep(&time, &rem);
  401595:	48 8d b4 24 80 00 00 00 	lea    0x80(%rsp),%rsi
  struct timespec time = {
  40159d:	0f 29 44 24 70       	movaps %xmm0,0x70(%rsp)
  struct timespec rem = {
  4015a2:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4015a6:	0f 29 84 24 80 00 00 00 	movaps %xmm0,0x80(%rsp)
  nanosleep(&time, &rem);
  4015ae:	e8 dd fa ff ff       	call   401090 <nanosleep@plt>
  4015b3:	48 8d 3d db 1a 00 00 	lea    0x1adb(%rip),%rdi        # 403095 <_IO_stdin_used+0x95>
  4015ba:	e8 91 fa ff ff       	call   401050 <puts@plt>
  
  printf("runphased\n");
  for (int x = 0; x < threadsize ; x++) {
    data[x].running--;
  4015bf:	41 83 6c 24 5c 01    	subl   $0x1,0x5c(%r12)
  4015c5:	48 8d 3d d3 1a 00 00 	lea    0x1ad3(%rip),%rdi        # 40309f <_IO_stdin_used+0x9f>
  4015cc:	41 83 ac 24 5c 04 00 00 01 	subl   $0x1,0x45c(%r12)
  4015d5:	41 83 ac 24 5c 08 00 00 01 	subl   $0x1,0x85c(%r12)
  4015de:	41 83 ac 24 5c 0c 00 00 01 	subl   $0x1,0xc5c(%r12)
  4015e7:	41 83 ac 24 5c 10 00 00 01 	subl   $0x1,0x105c(%r12)
  4015f0:	41 83 ac 24 5c 14 00 00 01 	subl   $0x1,0x145c(%r12)
  4015f9:	41 83 ac 24 5c 18 00 00 01 	subl   $0x1,0x185c(%r12)
  401602:	41 83 ac 24 5c 1c 00 00 01 	subl   $0x1,0x1c5c(%r12)
  40160b:	e8 40 fa ff ff       	call   401050 <puts@plt>
  
 printf("draining\n");
 // time.tv_sec = 3;
//nanosleep(&time, &rem);
  for (int x = 0; x < threadsize ; x++) {
    data[x].running--;
  401610:	41 83 6c 24 5c 01    	subl   $0x1,0x5c(%r12)
  401616:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
  40161b:	41 83 ac 24 5c 04 00 00 01 	subl   $0x1,0x45c(%r12)
  401624:	41 83 ac 24 5c 08 00 00 01 	subl   $0x1,0x85c(%r12)
  40162d:	48 83 c3 40          	add    $0x40,%rbx
  401631:	41 83 ac 24 5c 0c 00 00 01 	subl   $0x1,0xc5c(%r12)
  40163a:	41 83 ac 24 5c 10 00 00 01 	subl   $0x1,0x105c(%r12)
  401643:	41 83 ac 24 5c 14 00 00 01 	subl   $0x1,0x145c(%r12)
  40164c:	41 83 ac 24 5c 18 00 00 01 	subl   $0x1,0x185c(%r12)
  401655:	41 83 ac 24 5c 1c 00 00 01 	subl   $0x1,0x1c5c(%r12)
  for (int x = 0; x < threadsize ; x++) {
  40165e:	66 90                	xchg   %ax,%ax
  }
  
  //nanosleep(&time, &rem);
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401660:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
  401664:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  401667:	48 83 c5 08          	add    $0x8,%rbp
    pthread_join(thread[x], &res);
  40166b:	e8 a0 fa ff ff       	call   401110 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401670:	48 39 eb             	cmp    %rbp,%rbx
  401673:	75 eb                	jne    401660 <main+0x540>
  401675:	48 8d 3d 2c 1a 00 00 	lea    0x1a2c(%rip),%rdi        # 4030a8 <_IO_stdin_used+0xa8>
  40167c:	49 8d 5c 24 48       	lea    0x48(%r12),%rbx
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  401681:	31 ed                	xor    %ebp,%ebp
  401683:	e8 c8 f9 ff ff       	call   401050 <puts@plt>
  long sends = 1;
  for (int x = 0; x < threadsize; x++) {
  401688:	4d 8d b4 24 48 20 00 00 	lea    0x2048(%r12),%r14
  401690:	4c 8d 2d 26 1a 00 00 	lea    0x1a26(%rip),%r13        # 4030bd <_IO_stdin_used+0xbd>
  401697:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  4016a0:	48 8b 13             	mov    (%rbx),%rdx
  4016a3:	4c 89 ee             	mov    %r13,%rsi
  4016a6:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ab:	31 c0                	xor    %eax,%eax
  4016ad:	48 81 c3 00 04 00 00 	add    $0x400,%rbx
  4016b4:	e8 17 fa ff ff       	call   4010d0 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  4016b9:	48 03 ab 00 fc ff ff 	add    -0x400(%rbx),%rbp
  for (int x = 0; x < threadsize; x++) {
  4016c0:	49 39 de             	cmp    %rbx,%r14
  4016c3:	75 db                	jne    4016a0 <main+0x580>
  4016c5:	48 89 ea             	mov    %rbp,%rdx
  4016c8:	48 8d 35 f9 19 00 00 	lea    0x19f9(%rip),%rsi        # 4030c8 <_IO_stdin_used+0xc8>
  4016cf:	bf 01 00 00 00       	mov    $0x1,%edi
  4016d4:	31 c0                	xor    %eax,%eax
  4016d6:	e8 f5 f9 ff ff       	call   4010d0 <__printf_chk@plt>
  4016db:	48 89 ea             	mov    %rbp,%rdx
  4016de:	bf 01 00 00 00       	mov    $0x1,%edi
  4016e3:	31 c0                	xor    %eax,%eax
  4016e5:	48 8d 35 e7 19 00 00 	lea    0x19e7(%rip),%rsi        # 4030d3 <_IO_stdin_used+0xd3>
  4016ec:	49 8d 9c 24 98 03 00 00 	lea    0x398(%r12),%rbx
  4016f4:	e8 d7 f9 ff ff       	call   4010d0 <__printf_chk@plt>
  }
  printf("freq: %ld\n", freq/ seconds);
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  4016f9:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  4016fe:	48 8d 35 dc 19 00 00 	lea    0x19dc(%rip),%rsi        # 4030e1 <_IO_stdin_used+0xe1>
  401705:	bf 01 00 00 00       	mov    $0x1,%edi
  40170a:	48 99                	cqto
  40170c:	4d 8d bc 24 98 23 00 00 	lea    0x2398(%r12),%r15
  401714:	4c 8d 35 0b 1a 00 00 	lea    0x1a0b(%rip),%r14        # 403126 <_IO_stdin_used+0x126>
  40171b:	48 f7 fd             	idiv   %rbp
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  
  long goods = 0;
  40171e:	31 ed                	xor    %ebp,%ebp
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  401720:	49 89 c5             	mov    %rax,%r13
  401723:	48 89 c2             	mov    %rax,%rdx
  401726:	31 c0                	xor    %eax,%eax
  401728:	e8 a3 f9 ff ff       	call   4010d0 <__printf_chk@plt>
  40172d:	4c 89 ea             	mov    %r13,%rdx
  401730:	bf 01 00 00 00       	mov    $0x1,%edi
  401735:	31 c0                	xor    %eax,%eax
  401737:	48 8d 35 b7 19 00 00 	lea    0x19b7(%rip),%rsi        # 4030f5 <_IO_stdin_used+0xf5>
  40173e:	e8 8d f9 ff ff       	call   4010d0 <__printf_chk@plt>
  401743:	4c 89 ea             	mov    %r13,%rdx
  401746:	bf 01 00 00 00       	mov    $0x1,%edi
  40174b:	31 c0                	xor    %eax,%eax
  40174d:	48 8d 35 bf 19 00 00 	lea    0x19bf(%rip),%rsi        # 403113 <_IO_stdin_used+0x113>
  401754:	e8 77 f9 ff ff       	call   4010d0 <__printf_chk@plt>

  for (int x = 0; x < threadsize; x++) {
  401759:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401760:	48 8b 13             	mov    (%rbx),%rdx
  401763:	4c 89 f6             	mov    %r14,%rsi
  401766:	bf 01 00 00 00       	mov    $0x1,%edi
  40176b:	31 c0                	xor    %eax,%eax
  40176d:	48 81 c3 00 04 00 00 	add    $0x400,%rbx
  401774:	e8 57 f9 ff ff       	call   4010d0 <__printf_chk@plt>
    printf("%ld successreads\n", data[x].successreads);
    goods += data[x].successreads;
  401779:	48 03 ab 00 fc ff ff 	add    -0x400(%rbx),%rbp
  401780:	49 89 ed             	mov    %rbp,%r13
  for (int x = 0; x < threadsize; x++) {
  401783:	49 39 df             	cmp    %rbx,%r15
  401786:	75 d8                	jne    401760 <main+0x640>
  401788:	49 8d 5c 24 50       	lea    0x50(%r12),%rbx
  }
  
  long freq_writes = 0;
  40178d:	31 ed                	xor    %ebp,%ebp
  40178f:	4d 8d bc 24 50 20 00 00 	lea    0x2050(%r12),%r15
  401797:	4c 8d 35 9a 19 00 00 	lea    0x199a(%rip),%r14        # 403138 <_IO_stdin_used+0x138>
  40179e:	66 90                	xchg   %ax,%ax
  
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  4017a0:	48 8b 13             	mov    (%rbx),%rdx
  4017a3:	4c 89 f6             	mov    %r14,%rsi
  4017a6:	bf 01 00 00 00       	mov    $0x1,%edi
  4017ab:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  4017ad:	48 81 c3 00 04 00 00 	add    $0x400,%rbx
    freq_writes += data[x].freq_writes;
  4017b4:	48 01 d5             	add    %rdx,%rbp
  4017b7:	e8 14 f9 ff ff       	call   4010d0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  4017bc:	49 39 df             	cmp    %rbx,%r15
  4017bf:	75 df                	jne    4017a0 <main+0x680>
  4017c1:	48 89 ea             	mov    %rbp,%rdx
  4017c4:	bf 01 00 00 00       	mov    $0x1,%edi
  4017c9:	31 c0                	xor    %eax,%eax
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  4017cb:	bb 00 ca 9a 3b       	mov    $0x3b9aca00,%ebx
  4017d0:	48 8d 35 6d 19 00 00 	lea    0x196d(%rip),%rsi        # 403144 <_IO_stdin_used+0x144>
  4017d7:	e8 f4 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  4017dc:	48 89 ea             	mov    %rbp,%rdx
  4017df:	bf 01 00 00 00       	mov    $0x1,%edi
  4017e4:	31 c0                	xor    %eax,%eax
  4017e6:	48 8d 35 69 19 00 00 	lea    0x1969(%rip),%rsi        # 403156 <_IO_stdin_used+0x156>
  4017ed:	e8 de f8 ff ff       	call   4010d0 <__printf_chk@plt>
  4017f2:	48 89 d8             	mov    %rbx,%rax
  4017f5:	bf 01 00 00 00       	mov    $0x1,%edi
  4017fa:	48 8d 35 6d 19 00 00 	lea    0x196d(%rip),%rsi        # 40316e <_IO_stdin_used+0x16e>
  401801:	48 99                	cqto
  401803:	48 f7 fd             	idiv   %rbp
  401806:	48 8d 2d e3 18 00 00 	lea    0x18e3(%rip),%rbp        # 4030f0 <_IO_stdin_used+0xf0>
  40180d:	49 89 c6             	mov    %rax,%r14
  401810:	48 89 c2             	mov    %rax,%rdx
  401813:	31 c0                	xor    %eax,%eax
  401815:	e8 b6 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  40181a:	4c 89 f2             	mov    %r14,%rdx
  40181d:	bf 01 00 00 00       	mov    $0x1,%edi
  401822:	31 c0                	xor    %eax,%eax
  401824:	48 8d 35 25 1a 00 00 	lea    0x1a25(%rip),%rsi        # 403250 <_IO_stdin_used+0x250>
  40182b:	e8 a0 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  401830:	4c 89 f2             	mov    %r14,%rdx
  401833:	bf 01 00 00 00       	mov    $0x1,%edi
  401838:	31 c0                	xor    %eax,%eax
  40183a:	48 8d 35 48 19 00 00 	lea    0x1948(%rip),%rsi        # 403189 <_IO_stdin_used+0x189>
  401841:	e8 8a f8 ff ff       	call   4010d0 <__printf_chk@plt>
  401846:	48 8d 3d 56 19 00 00 	lea    0x1956(%rip),%rdi        # 4031a3 <_IO_stdin_used+0x1a3>
  40184d:	e8 fe f7 ff ff       	call   401050 <puts@plt>
  401852:	48 89 ee             	mov    %rbp,%rsi
  401855:	bf 01 00 00 00       	mov    $0x1,%edi
  40185a:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  40185c:	49 8b 94 24 f0 00 00 00 	mov    0xf0(%r12),%rdx
  401864:	49 2b 94 24 e0 00 00 00 	sub    0xe0(%r12),%rdx
  40186c:	e8 5f f8 ff ff       	call   4010d0 <__printf_chk@plt>
  401871:	48 89 ee             	mov    %rbp,%rsi
  401874:	bf 01 00 00 00       	mov    $0x1,%edi
  401879:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  40187b:	49 8b 94 24 00 01 00 00 	mov    0x100(%r12),%rdx
  401883:	49 2b 94 24 e0 00 00 00 	sub    0xe0(%r12),%rdx
  40188b:	e8 40 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  401890:	48 89 ee             	mov    %rbp,%rsi
  401893:	bf 01 00 00 00       	mov    $0x1,%edi
  401898:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  40189a:	49 8b 94 24 f0 00 00 00 	mov    0xf0(%r12),%rdx
  4018a2:	49 2b 94 24 00 01 00 00 	sub    0x100(%r12),%rdx
  4018aa:	e8 21 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  4018af:	48 89 ee             	mov    %rbp,%rsi
  4018b2:	bf 01 00 00 00       	mov    $0x1,%edi
  4018b7:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4018b9:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
  4018c1:	49 2b 94 24 10 01 00 00 	sub    0x110(%r12),%rdx
  4018c9:	e8 02 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  4018ce:	48 89 ee             	mov    %rbp,%rsi
  4018d1:	bf 01 00 00 00       	mov    $0x1,%edi
  4018d6:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  4018d8:	49 8b 94 24 10 01 00 00 	mov    0x110(%r12),%rdx
  4018e0:	49 2b 94 24 20 01 00 00 	sub    0x120(%r12),%rdx
  4018e8:	e8 e3 f7 ff ff       	call   4010d0 <__printf_chk@plt>
  4018ed:	48 89 ee             	mov    %rbp,%rsi
  4018f0:	bf 01 00 00 00       	mov    $0x1,%edi
  4018f5:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  4018f7:	49 8b 94 24 10 01 00 00 	mov    0x110(%r12),%rdx
  4018ff:	49 2b 94 24 00 01 00 00 	sub    0x100(%r12),%rdx
  401907:	e8 c4 f7 ff ff       	call   4010d0 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  40190c:	49 8b 94 24 40 01 00 00 	mov    0x140(%r12),%rdx
  401914:	bf 01 00 00 00       	mov    $0x1,%edi
  401919:	49 2b 94 24 30 01 00 00 	sub    0x130(%r12),%rdx
  401921:	48 8d 35 88 18 00 00 	lea    0x1888(%rip),%rsi        # 4031b0 <_IO_stdin_used+0x1b0>
  401928:	31 c0                	xor    %eax,%eax
  40192a:	e8 a1 f7 ff ff       	call   4010d0 <__printf_chk@plt>
  40192f:	4c 89 ea             	mov    %r13,%rdx
  401932:	bf 01 00 00 00       	mov    $0x1,%edi
  401937:	31 c0                	xor    %eax,%eax
  401939:	48 8d 35 78 18 00 00 	lea    0x1878(%rip),%rsi        # 4031b8 <_IO_stdin_used+0x1b8>
  401940:	e8 8b f7 ff ff       	call   4010d0 <__printf_chk@plt>
  } 
  printf("%ld good reads per second\n", goods / seconds);
  printf("%ld good reads per second latency\n", 1000000000 / (goods / seconds));
  401945:	48 89 d8             	mov    %rbx,%rax
  401948:	bf 01 00 00 00       	mov    $0x1,%edi
  40194d:	31 db                	xor    %ebx,%ebx
  40194f:	48 99                	cqto
  401951:	48 8d 35 20 19 00 00 	lea    0x1920(%rip),%rsi        # 403278 <_IO_stdin_used+0x278>
  401958:	49 f7 fd             	idiv   %r13
  40195b:	48 89 c2             	mov    %rax,%rdx
  40195e:	31 c0                	xor    %eax,%eax
  401960:	e8 6b f7 ff ff       	call   4010d0 <__printf_chk@plt>
     }
   fclose(out_file);
   
 }

  char * filename = calloc(100, sizeof(char));
  401965:	be 01 00 00 00       	mov    $0x1,%esi
  40196a:	bf 64 00 00 00       	mov    $0x64,%edi
  40196f:	e8 4c f7 ff ff       	call   4010c0 <calloc@plt>
  char * buf = calloc(1000, sizeof(char));
  401974:	be 01 00 00 00       	mov    $0x1,%esi
  401979:	bf e8 03 00 00       	mov    $0x3e8,%edi
  char * filename = calloc(100, sizeof(char));
  40197e:	49 89 c4             	mov    %rax,%r12
  char * buf = calloc(1000, sizeof(char));
  401981:	e8 3a f7 ff ff       	call   4010c0 <calloc@plt>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401986:	66 0f 6f 05 62 19 00 00 	movdqa 0x1962(%rip),%xmm0        # 4032f0 <_IO_stdin_used+0x2f0>
  memset(filename, 0, 100);
  snprintf(filename, 100, "coroutine.struct");
  FILE *out_file = fopen(filename, "w");
  40198e:	4c 89 e7             	mov    %r12,%rdi
  401991:	41 c6 44 24 10 00    	movb   $0x0,0x10(%r12)
  401997:	48 8d 35 35 18 00 00 	lea    0x1835(%rip),%rsi        # 4031d3 <_IO_stdin_used+0x1d3>
  char * buf = calloc(1000, sizeof(char));
  40199e:	48 89 c5             	mov    %rax,%rbp
  4019a1:	41 0f 11 04 24       	movups %xmm0,(%r12)
  FILE *out_file = fopen(filename, "w");
  4019a6:	e8 45 f7 ff ff       	call   4010f0 <fopen@plt>
  4019ab:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  4019b0:	48 89 ef             	mov    %rbp,%rdi
  4019b3:	45 31 c9             	xor    %r9d,%r9d
  4019b6:	49 89 c4             	mov    %rax,%r12
  4019b9:	48 89 d8             	mov    %rbx,%rax
  4019bc:	ba 01 00 00 00       	mov    $0x1,%edx
  4019c1:	be 64 00 00 00       	mov    $0x64,%esi
  4019c6:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  4019c9:	4c 8d 05 05 18 00 00 	lea    0x1805(%rip),%r8        # 4031d5 <_IO_stdin_used+0x1d5>
  4019d0:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  4019d5:	48 89 ef             	mov    %rbp,%rdi
  4019d8:	e8 53 f6 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  4019dd:	4c 89 e6             	mov    %r12,%rsi
  4019e0:	48 89 ef             	mov    %rbp,%rdi
  4019e3:	e8 b8 f6 ff ff       	call   4010a0 <fputs@plt>
  4019e8:	48 89 d8             	mov    %rbx,%rax
  4019eb:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  4019f0:	48 89 ef             	mov    %rbp,%rdi
  4019f3:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  4019f6:	41 b9 08 00 00 00    	mov    $0x8,%r9d
  4019fc:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401a01:	48 89 ef             	mov    %rbp,%rdi
  401a04:	4c 8d 05 d5 17 00 00 	lea    0x17d5(%rip),%r8        # 4031e0 <_IO_stdin_used+0x1e0>
  401a0b:	ba 01 00 00 00       	mov    $0x1,%edx
  401a10:	be 64 00 00 00       	mov    $0x64,%esi
  401a15:	e8 16 f6 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401a1a:	4c 89 e6             	mov    %r12,%rsi
  401a1d:	48 89 ef             	mov    %rbp,%rdi
  401a20:	e8 7b f6 ff ff       	call   4010a0 <fputs@plt>
  401a25:	48 89 d8             	mov    %rbx,%rax
  401a28:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401a2d:	48 89 ef             	mov    %rbp,%rdi
  401a30:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401a33:	41 b9 10 00 00 00    	mov    $0x10,%r9d
  401a39:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401a3e:	48 89 ef             	mov    %rbp,%rdi
  401a41:	4c 8d 05 a1 17 00 00 	lea    0x17a1(%rip),%r8        # 4031e9 <_IO_stdin_used+0x1e9>
  401a48:	ba 01 00 00 00       	mov    $0x1,%edx
  401a4d:	be 64 00 00 00       	mov    $0x64,%esi
  401a52:	e8 d9 f5 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401a57:	4c 89 e6             	mov    %r12,%rsi
  401a5a:	48 89 ef             	mov    %rbp,%rdi
  401a5d:	e8 3e f6 ff ff       	call   4010a0 <fputs@plt>
  401a62:	48 89 d8             	mov    %rbx,%rax
  401a65:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401a6a:	48 89 ef             	mov    %rbp,%rdi
  401a6d:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401a70:	41 b9 18 00 00 00    	mov    $0x18,%r9d
  401a76:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401a7b:	48 89 ef             	mov    %rbp,%rdi
  401a7e:	4c 8d 05 6d 17 00 00 	lea    0x176d(%rip),%r8        # 4031f2 <_IO_stdin_used+0x1f2>
  401a85:	ba 01 00 00 00       	mov    $0x1,%edx
  401a8a:	be 64 00 00 00       	mov    $0x64,%esi
  401a8f:	e8 9c f5 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401a94:	4c 89 e6             	mov    %r12,%rsi
  401a97:	48 89 ef             	mov    %rbp,%rdi
  401a9a:	e8 01 f6 ff ff       	call   4010a0 <fputs@plt>
  401a9f:	48 89 d8             	mov    %rbx,%rax
  401aa2:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401aa7:	48 89 ef             	mov    %rbp,%rdi
  401aaa:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401aad:	45 31 c9             	xor    %r9d,%r9d
  401ab0:	4c 8d 05 45 17 00 00 	lea    0x1745(%rip),%r8        # 4031fc <_IO_stdin_used+0x1fc>
  401ab7:	48 89 ef             	mov    %rbp,%rdi
  401aba:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401abf:	ba 01 00 00 00       	mov    $0x1,%edx
  401ac4:	be 64 00 00 00       	mov    $0x64,%esi
  401ac9:	e8 62 f5 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401ace:	4c 89 e6             	mov    %r12,%rsi
  401ad1:	48 89 ef             	mov    %rbp,%rdi
  401ad4:	e8 c7 f5 ff ff       	call   4010a0 <fputs@plt>
  401ad9:	48 89 d8             	mov    %rbx,%rax
  401adc:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401ae1:	48 89 ef             	mov    %rbp,%rdi
  401ae4:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401ae7:	41 b9 20 00 00 00    	mov    $0x20,%r9d
  401aed:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401af2:	48 89 ef             	mov    %rbp,%rdi
  401af5:	4c 8d 05 1b 17 00 00 	lea    0x171b(%rip),%r8        # 403217 <_IO_stdin_used+0x217>
  401afc:	ba 01 00 00 00       	mov    $0x1,%edx
  401b01:	be 64 00 00 00       	mov    $0x64,%esi
  401b06:	e8 25 f5 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401b0b:	48 89 ef             	mov    %rbp,%rdi
  401b0e:	4c 89 e6             	mov    %r12,%rsi
  401b11:	e8 8a f5 ff ff       	call   4010a0 <fputs@plt>

  memset(buf, 0, 1000);
  snprintf(buf, 100, "size coroutine %ld\n", sizeof(struct Coroutine));
  fprintf(out_file, "%s", buf);
  
  fclose(out_file);
  401b16:	4c 89 e7             	mov    %r12,%rdi
  401b19:	e8 52 f5 ff ff       	call   401070 <fclose@plt>
  401b1e:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
  401b26:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401b2f:	75 14                	jne    401b45 <main+0xa25>
  401b31:	48 81 c4 a8 00 00 00 	add    $0xa8,%rsp
  401b38:	31 c0                	xor    %eax,%eax
  401b3a:	5b                   	pop    %rbx
  401b3b:	5d                   	pop    %rbp
  401b3c:	41 5c                	pop    %r12
  401b3e:	41 5d                	pop    %r13
  401b40:	41 5e                	pop    %r14
  401b42:	41 5f                	pop    %r15
  401b44:	c3                   	ret
  401b45:	e8 36 f5 ff ff       	call   401080 <__stack_chk_fail@plt>
  401b4a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000401b50 <set_fast_math>:
  401b50:	f3 0f 1e fa          	endbr64
  401b54:	0f ae 5c 24 fc       	stmxcsr -0x4(%rsp)
  401b59:	81 4c 24 fc 40 80 00 00 	orl    $0x8040,-0x4(%rsp)
  401b61:	0f ae 54 24 fc       	ldmxcsr -0x4(%rsp)
  401b66:	c3                   	ret
  401b67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000401b70 <_start>:
  401b70:	f3 0f 1e fa          	endbr64
  401b74:	31 ed                	xor    %ebp,%ebp
  401b76:	49 89 d1             	mov    %rdx,%r9
  401b79:	5e                   	pop    %rsi
  401b7a:	48 89 e2             	mov    %rsp,%rdx
  401b7d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401b81:	50                   	push   %rax
  401b82:	54                   	push   %rsp
  401b83:	45 31 c0             	xor    %r8d,%r8d
  401b86:	31 c9                	xor    %ecx,%ecx
  401b88:	48 c7 c7 20 11 40 00 	mov    $0x401120,%rdi
  401b8f:	ff 15 5b 34 00 00    	call   *0x345b(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  401b95:	f4                   	hlt
  401b96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401ba0 <_dl_relocate_static_pie>:
  401ba0:	f3 0f 1e fa          	endbr64
  401ba4:	c3                   	ret
  401ba5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401baf:	90                   	nop

0000000000401bb0 <deregister_tm_clones>:
  401bb0:	b8 10 50 40 00       	mov    $0x405010,%eax
  401bb5:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  401bbb:	74 13                	je     401bd0 <deregister_tm_clones+0x20>
  401bbd:	b8 00 00 00 00       	mov    $0x0,%eax
  401bc2:	48 85 c0             	test   %rax,%rax
  401bc5:	74 09                	je     401bd0 <deregister_tm_clones+0x20>
  401bc7:	bf 10 50 40 00       	mov    $0x405010,%edi
  401bcc:	ff e0                	jmp    *%rax
  401bce:	66 90                	xchg   %ax,%ax
  401bd0:	c3                   	ret
  401bd1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401bdc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401be0 <register_tm_clones>:
  401be0:	be 10 50 40 00       	mov    $0x405010,%esi
  401be5:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  401bec:	48 89 f0             	mov    %rsi,%rax
  401bef:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401bf3:	48 c1 f8 03          	sar    $0x3,%rax
  401bf7:	48 01 c6             	add    %rax,%rsi
  401bfa:	48 d1 fe             	sar    %rsi
  401bfd:	74 11                	je     401c10 <register_tm_clones+0x30>
  401bff:	b8 00 00 00 00       	mov    $0x0,%eax
  401c04:	48 85 c0             	test   %rax,%rax
  401c07:	74 07                	je     401c10 <register_tm_clones+0x30>
  401c09:	bf 10 50 40 00       	mov    $0x405010,%edi
  401c0e:	ff e0                	jmp    *%rax
  401c10:	c3                   	ret
  401c11:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401c1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401c20 <__do_global_dtors_aux>:
  401c20:	f3 0f 1e fa          	endbr64
  401c24:	80 3d e5 33 00 00 00 	cmpb   $0x0,0x33e5(%rip)        # 405010 <__TMC_END__>
  401c2b:	75 13                	jne    401c40 <__do_global_dtors_aux+0x20>
  401c2d:	55                   	push   %rbp
  401c2e:	48 89 e5             	mov    %rsp,%rbp
  401c31:	e8 7a ff ff ff       	call   401bb0 <deregister_tm_clones>
  401c36:	c6 05 d3 33 00 00 01 	movb   $0x1,0x33d3(%rip)        # 405010 <__TMC_END__>
  401c3d:	5d                   	pop    %rbp
  401c3e:	c3                   	ret
  401c3f:	90                   	nop
  401c40:	c3                   	ret
  401c41:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401c4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401c50 <frame_dummy>:
  401c50:	f3 0f 1e fa          	endbr64
  401c54:	eb 8a                	jmp    401be0 <register_tm_clones>
  401c56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401c60 <coroutine_func>:
int coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data) {
  401c60:	41 54                	push   %r12
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  401c62:	49 89 d0             	mov    %rdx,%r8
  401c65:	48 89 f1             	mov    %rsi,%rcx
  401c68:	31 c0                	xor    %eax,%eax
  401c6a:	55                   	push   %rbp
  401c6b:	48 89 f5             	mov    %rsi,%rbp
  401c6e:	48 8d 35 8f 13 00 00 	lea    0x138f(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  401c75:	53                   	push   %rbx
  401c76:	48 89 d3             	mov    %rdx,%rbx
  401c79:	48 89 fa             	mov    %rdi,%rdx
  401c7c:	bf 01 00 00 00       	mov    $0x1,%edi
  401c81:	e8 4a f4 ff ff       	call   4010d0 <__printf_chk@plt>
  while (data->running == 1) {
  401c86:	83 3b 01             	cmpl   $0x1,(%rbx)
  401c89:	75 25                	jne    401cb0 <coroutine_func+0x50>
  401c8b:	4c 8d 25 5e 14 00 00 	lea    0x145e(%rip),%r12        # 4030f0 <_IO_stdin_used+0xf0>
  401c92:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  401c98:	48 8b 55 10          	mov    0x10(%rbp),%rdx
  401c9c:	31 c0                	xor    %eax,%eax
  401c9e:	4c 89 e6             	mov    %r12,%rsi
  401ca1:	bf 01 00 00 00       	mov    $0x1,%edi
  401ca6:	e8 25 f4 ff ff       	call   4010d0 <__printf_chk@plt>
  401cab:	83 3b 01             	cmpl   $0x1,(%rbx)
  401cae:	74 e8                	je     401c98 <coroutine_func+0x38>
}
  401cb0:	5b                   	pop    %rbx
  401cb1:	31 c0                	xor    %eax,%eax
  401cb3:	5d                   	pop    %rbp
  401cb4:	41 5c                	pop    %r12
  401cb6:	c3                   	ret
  401cb7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000401cc0 <yield>:
}
  401cc0:	c3                   	ret
  401cc1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401ccc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401cd0 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  401cd0:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  401cd4:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  401cd7:	7e 77                	jle    401d50 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  401cd9:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  401cdd:	55                   	push   %rbp
  401cde:	49 89 f2             	mov    %rsi,%r10
  401ce1:	49 89 d3             	mov    %rdx,%r11
  401ce4:	53                   	push   %rbx
  401ce5:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  401ce8:	48 8b 98 20 04 00 00 	mov    0x420(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  401cef:	b8 01 00 00 00       	mov    $0x1,%eax
  401cf4:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  401cf8:	48 63 d0             	movslq %eax,%rdx
  401cfb:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  401cfe:	85 d2                	test   %edx,%edx
  401d00:	40 0f 94 c6          	sete   %sil
  401d04:	f6 c2 04             	test   $0x4,%dl
  401d07:	75 05                	jne    401d0e <pollthreads+0x3e>
  401d09:	40 84 f6             	test   %sil,%sil
  401d0c:	74 0d                	je     401d1b <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  401d0e:	49 63 08             	movslq (%r8),%rcx
  401d11:	8d 69 01             	lea    0x1(%rcx),%ebp
  401d14:	41 89 28             	mov    %ebp,(%r8)
  401d17:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  401d1b:	83 e2 08             	and    $0x8,%edx
  401d1e:	75 05                	jne    401d25 <pollthreads+0x55>
  401d20:	40 84 f6             	test   %sil,%sil
  401d23:	74 1b                	je     401d40 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  401d25:	48 63 17             	movslq (%rdi),%rdx
  401d28:	8d 4a 01             	lea    0x1(%rdx),%ecx
  401d2b:	89 0f                	mov    %ecx,(%rdi)
  401d2d:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  401d31:	83 c0 01             	add    $0x1,%eax
  401d34:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401d38:	7f be                	jg     401cf8 <pollthreads+0x28>
}
  401d3a:	31 c0                	xor    %eax,%eax
  401d3c:	5b                   	pop    %rbx
  401d3d:	5d                   	pop    %rbp
  401d3e:	c3                   	ret
  401d3f:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  401d40:	83 c0 01             	add    $0x1,%eax
  401d43:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401d47:	7f af                	jg     401cf8 <pollthreads+0x28>
}
  401d49:	31 c0                	xor    %eax,%eax
  401d4b:	5b                   	pop    %rbx
  401d4c:	5d                   	pop    %rbp
  401d4d:	c3                   	ret
  401d4e:	66 90                	xchg   %ax,%ax
  401d50:	31 c0                	xor    %eax,%eax
  401d52:	c3                   	ret
  401d53:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401d5e:	66 90                	xchg   %ax,%ax

0000000000401d60 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401d60:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401d63:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
      if (*availableidx == 0) {
  401d6a:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401d6d:	48 83 c7 01          	add    $0x1,%rdi
  401d71:	48 85 ff             	test   %rdi,%rdi
  401d74:	7e 66                	jle    401ddc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401d76:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401d7d:	31 c9                	xor    %ecx,%ecx
  401d7f:	45 31 c9             	xor    %r9d,%r9d
  401d82:	31 c0                	xor    %eax,%eax
  401d84:	eb 18                	jmp    401d9e <findavailable+0x3e>
  401d86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401d90:	83 c1 01             	add    $0x1,%ecx
  401d93:	48 63 c1             	movslq %ecx,%rax
  401d96:	49 89 c1             	mov    %rax,%r9
  401d99:	48 39 f8             	cmp    %rdi,%rax
  401d9c:	7d 3e                	jge    401ddc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401d9e:	48 c1 e0 05          	shl    $0x5,%rax
  401da2:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401da8:	75 e6                	jne    401d90 <findavailable+0x30>
         available[*availableidx] = x;
  401daa:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  401dad:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401db1:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401db5:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401db8:	41 8b 43 68          	mov    0x68(%r11),%eax
  401dbc:	01 c0                	add    %eax,%eax
  401dbe:	41 39 c0             	cmp    %eax,%r8d
  401dc1:	74 19                	je     401ddc <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401dc3:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  401dca:	83 c1 01             	add    $0x1,%ecx
  401dcd:	48 63 c1             	movslq %ecx,%rax
  401dd0:	48 83 c7 01          	add    $0x1,%rdi
  401dd4:	49 89 c1             	mov    %rax,%r9
  401dd7:	48 39 f8             	cmp    %rdi,%rax
  401dda:	7c c2                	jl     401d9e <findavailable+0x3e>
      if (*availableidx == 0) {
  401ddc:	31 c0                	xor    %eax,%eax
  401dde:	45 85 c0             	test   %r8d,%r8d
  401de1:	0f 94 c0             	sete   %al
}
  401de4:	c3                   	ret
  401de5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401df0 <singlewriter3>:
}
  401df0:	c3                   	ret
  401df1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401dfc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401e00 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401e00:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  401e06:	85 c0                	test   %eax,%eax
  401e08:	74 1e                	je     401e28 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401e0a:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401e0c:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401e0d:	55                   	push   %rbp
  401e0e:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401e0f:	8b 77 68             	mov    0x68(%rdi),%esi
  401e12:	48 89 fb             	mov    %rdi,%rbx
  401e15:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401e18:	f7 f9                	idiv   %ecx
  401e1a:	85 d2                	test   %edx,%edx
  401e1c:	74 12                	je     401e30 <singlewriter2+0x30>
}
  401e1e:	5b                   	pop    %rbx
  401e1f:	5d                   	pop    %rbp
  401e20:	41 5c                	pop    %r12
  401e22:	c3                   	ret
  401e23:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401e28:	c3                   	ret
  401e29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct Data * thread = &data->threads[data->threadindex];
  401e30:	48 63 6f 64          	movslq 0x64(%rdi),%rbp
  401e34:	48 c1 e5 0a          	shl    $0xa,%rbp
  401e38:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401e3c:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401e41:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401e48:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401e4c:	49 c1 e4 04          	shl    $0x4,%r12
  401e50:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401e57:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401e5c:	e8 ff f1 ff ff       	call   401060 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e61:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401e67:	83 c0 01             	add    $0x1,%eax
  401e6a:	99                   	cltd
  401e6b:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  401e71:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e74:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401e7a:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401e7e:	48 8b 05 1b 14 00 00 	mov    0x141b(%rip),%rax        # 4032a0 <_IO_stdin_used+0x2a0>
  401e85:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  401e8a:	5b                   	pop    %rbx
  401e8b:	5d                   	pop    %rbp
  401e8c:	41 5c                	pop    %r12
  401e8e:	c3                   	ret
  401e8f:	90                   	nop

0000000000401e90 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401e90:	41 55                	push   %r13
  401e92:	49 89 d5             	mov    %rdx,%r13
  401e95:	41 54                	push   %r12
  401e97:	49 89 cc             	mov    %rcx,%r12
  401e9a:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401e9b:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401e9e:	48 89 fd             	mov    %rdi,%rbp
  401ea1:	53                   	push   %rbx
  401ea2:	48 89 f3             	mov    %rsi,%rbx
  401ea5:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401ea9:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401ead:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401eb6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401ebb:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401ebd:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401ec5:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  401ecb:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401ed3:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401edb:	83 c0 01             	add    $0x1,%eax
  401ede:	99                   	cltd
  401edf:	f7 7f 68             	idivl  0x68(%rdi)
  401ee2:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401ee8:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401eed:	4c 89 e9             	mov    %r13,%rcx
  401ef0:	e8 6b fe ff ff       	call   401d60 <findavailable>
  if (fill == 1) {
  401ef5:	83 f8 01             	cmp    $0x1,%eax
  401ef8:	0f 84 3c 01 00 00    	je     40203a <singlewriter+0x1aa>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401efe:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401f03:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401f08:	4c 89 e2             	mov    %r12,%rdx
  401f0b:	4c 89 ee             	mov    %r13,%rsi
  401f0e:	48 89 ef             	mov    %rbp,%rdi
  401f11:	e8 ba fd ff ff       	call   401cd0 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401f16:	4c 63 44 24 0c       	movslq 0xc(%rsp),%r8
  401f1b:	45 85 c0             	test   %r8d,%r8d
  401f1e:	0f 8e 3d 01 00 00    	jle    402061 <singlewriter+0x1d1>
  401f24:	44 8b 4c 24 14       	mov    0x14(%rsp),%r9d
          if (assignedchunk == availableidx) {
  401f29:	31 c9                	xor    %ecx,%ecx
  401f2b:	eb 58                	jmp    401f85 <singlewriter+0xf5>
  401f2d:	0f 1f 00             	nopl   (%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401f30:	48 8b 04 cb          	mov    (%rbx,%rcx,8),%rax
          int thread = readyreaders[x];
  401f34:	49 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%rdx
  401f39:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401f3c:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401f40:	48 c1 e0 05          	shl    $0x5,%rax
  401f44:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
          int thread = readyreaders[x];
  401f4b:	48 89 d7             	mov    %rdx,%rdi
          data->threads[thread].reading = chunk;
  401f4e:	48 c1 e2 0a          	shl    $0xa,%rdx
          data->threads[thread].start = start;
  401f52:	66 0f 6e 00          	movd   (%rax),%xmm0
  401f56:	66 0f 6e 48 08       	movd   0x8(%rax),%xmm1
          chunk->available = READING;
  401f5b:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
          data->threads[thread].reading = chunk;
  401f62:	48 03 55 30          	add    0x30(%rbp),%rdx
          data->threads[thread].start = start;
  401f66:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401f6a:	48 89 82 a8 00 00 00 	mov    %rax,0xa8(%rdx)
          chunk->owner = thread;
  401f71:	89 78 14             	mov    %edi,0x14(%rax)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401f74:	83 8a c8 00 00 00 10 	orl    $0x10,0xc8(%rdx)
          data->threads[thread].start = start;
  401f7b:	66 0f d6 42 14       	movq   %xmm0,0x14(%rdx)
        for (int x = 0; x < readers ; x++) {
  401f80:	49 39 c8             	cmp    %rcx,%r8
  401f83:	74 07                	je     401f8c <singlewriter+0xfc>
  401f85:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401f87:	4c 39 c9             	cmp    %r9,%rcx
  401f8a:	75 a4                	jne    401f30 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401f8c:	44 8b 4c 24 10       	mov    0x10(%rsp),%r9d
  401f91:	45 85 c9             	test   %r9d,%r9d
  401f94:	7e 68                	jle    401ffe <singlewriter+0x16e>
                if (assignedchunk  == availableidx) {
  401f96:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
  401f9b:	41 01 f1             	add    %esi,%r9d
  401f9e:	eb 59                	jmp    401ff9 <singlewriter+0x169>
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401fa0:	8d 7e 01             	lea    0x1(%rsi),%edi
  401fa3:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401fa6:	49 63 14 24          	movslq (%r12),%rdx
   for (int x = 0; x < writers ; x++) {
  401faa:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401fae:	48 8b 04 f3          	mov    (%rbx,%rsi,8),%rax
          int thread = readywriters[x];
  401fb2:	48 89 d1             	mov    %rdx,%rcx
          data->threads[thread].writing = chunk;
  401fb5:	48 c1 e2 0a          	shl    $0xa,%rdx
  401fb9:	48 03 55 30          	add    0x30(%rbp),%rdx
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401fbd:	48 c1 e0 05          	shl    $0x5,%rax
  401fc1:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
          data->threads[thread].publishstart = start;
  401fc8:	66 0f 6e 00          	movd   (%rax),%xmm0
  401fcc:	66 0f 6e 50 08       	movd   0x8(%rax),%xmm2
      chunk->available = WRITING;
  401fd1:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
          data->threads[thread].writing = chunk;
  401fd8:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
          data->threads[thread].publishstart = start;
  401fdf:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          chunk->owner = thread;
  401fe3:	89 48 14             	mov    %ecx,0x14(%rax)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401fe6:	83 8a c8 00 00 00 20 	orl    $0x20,0xc8(%rdx)
          data->threads[thread].publishstart = start;
  401fed:	66 0f d6 42 40       	movq   %xmm0,0x40(%rdx)
   for (int x = 0; x < writers ; x++) {
  401ff2:	44 39 cf             	cmp    %r9d,%edi
  401ff5:	74 07                	je     401ffe <singlewriter+0x16e>
  401ff7:	89 fe                	mov    %edi,%esi
                if (assignedchunk  == availableidx) {
  401ff9:	41 39 f0             	cmp    %esi,%r8d
  401ffc:	75 a2                	jne    401fa0 <singlewriter+0x110>
      for (int x = 0; x < data->threadsize ; x++) {
  401ffe:	8b 7d 68             	mov    0x68(%rbp),%edi
  402001:	85 ff                	test   %edi,%edi
  402003:	7e 33                	jle    402038 <singlewriter+0x1a8>
        if (data->threads[x].newmask != 0) {
  402005:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  402009:	31 d2                	xor    %edx,%edx
  40200b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  402010:	48 63 ca             	movslq %edx,%rcx
  402013:	48 89 c8             	mov    %rcx,%rax
  402016:	48 c1 e0 0a          	shl    $0xa,%rax
  40201a:	4c 01 c0             	add    %r8,%rax
  40201d:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  402023:	85 f6                	test   %esi,%esi
  402025:	74 31                	je     402058 <singlewriter+0x1c8>
          data->threads[x].readies[x] = data->threads[x].newmask;
  402027:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  40202b:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  40202e:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  402031:	8b 7d 68             	mov    0x68(%rbp),%edi
  402034:	39 fa                	cmp    %edi,%edx
  402036:	7c d8                	jl     402010 <singlewriter+0x180>
  return 0;
  402038:	31 c0                	xor    %eax,%eax
}
  40203a:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  40203f:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  402048:	75 1e                	jne    402068 <singlewriter+0x1d8>
  40204a:	48 83 c4 28          	add    $0x28,%rsp
  40204e:	5b                   	pop    %rbx
  40204f:	5d                   	pop    %rbp
  402050:	41 5c                	pop    %r12
  402052:	41 5d                	pop    %r13
  402054:	c3                   	ret
  402055:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  402058:	83 c2 01             	add    $0x1,%edx
  40205b:	39 fa                	cmp    %edi,%edx
  40205d:	7c b1                	jl     402010 <singlewriter+0x180>
  40205f:	eb d7                	jmp    402038 <singlewriter+0x1a8>
      int assignedchunk = 0;
  402061:	31 f6                	xor    %esi,%esi
  402063:	e9 24 ff ff ff       	jmp    401f8c <singlewriter+0xfc>
}
  402068:	e8 13 f0 ff ff       	call   401080 <__stack_chk_fail@plt>
  40206d:	0f 1f 00             	nopl   (%rax)

0000000000402070 <threadwork>:
int * threadwork(struct Data * data) {
  402070:	41 56                	push   %r14
  switch_to(data->coroutines, 3, data->scheduler);  
  402072:	be 03 00 00 00       	mov    $0x3,%esi
int * threadwork(struct Data * data) {
  402077:	41 55                	push   %r13
  402079:	41 54                	push   %r12
  40207b:	55                   	push   %rbp
  40207c:	53                   	push   %rbx
  40207d:	48 89 fb             	mov    %rdi,%rbx
  402080:	48 83 ec 20          	sub    $0x20,%rsp
  data->scheduler->rsp = rsp;
  402084:	48 8b 97 c8 03 00 00 	mov    0x3c8(%rdi),%rdx
  switch_to(data->coroutines, 3, data->scheduler);  
  40208b:	48 8b bf c0 03 00 00 	mov    0x3c0(%rdi),%rdi
int * threadwork(struct Data * data) {
  402092:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40209b:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  4020a0:	31 c0                	xor    %eax,%eax
    asm( "mov %%rsp, %0" : "=rm" ( rsp ));
  4020a2:	48 89 e0             	mov    %rsp,%rax
  data->scheduler->rsp = rsp;
  4020a5:	48 89 02             	mov    %rax,(%rdx)
  switch_to(data->coroutines, 3, data->scheduler);  
  4020a8:	e8 00 04 00 00       	call   4024ad <switch_to>
clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  4020ad:	48 89 e6             	mov    %rsp,%rsi
  4020b0:	bf 04 00 00 00       	mov    $0x4,%edi
  4020b5:	e8 a6 ef ff ff       	call   401060 <clock_gettime@plt>
  if (data->running == 2) {
  4020ba:	83 7b 5c 02          	cmpl   $0x2,0x5c(%rbx)
  4020be:	0f 84 ec 01 00 00    	je     4022b0 <threadwork+0x240>
  long thisgroup = data->main->globalwrite[data->mystream * 128] / epochsize;
  4020c4:	8b ab 8c 03 00 00    	mov    0x38c(%rbx),%ebp
  4020ca:	4c 8b 63 28          	mov    0x28(%rbx),%r12
  if (thisgroup != data->lastgroup) {
  4020ce:	48 63 8b 88 03 00 00 	movslq 0x388(%rbx),%rcx
  long thisgroup = data->main->globalwrite[data->mystream * 128] / epochsize;
  4020d5:	89 e8                	mov    %ebp,%eax
  4020d7:	49 8b 94 24 80 03 00 00 	mov    0x380(%r12),%rdx
  4020df:	c1 e0 07             	shl    $0x7,%eax
  4020e2:	48 98                	cltq
  4020e4:	48 8b 04 c2          	mov    (%rdx,%rax,8),%rax
  if (thisgroup != data->lastgroup) {
  4020e8:	48 39 c8             	cmp    %rcx,%rax
  4020eb:	74 0a                	je     4020f7 <threadwork+0x87>
      data->writecursor = 0;
  4020ed:	c7 83 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rbx)
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  4020f7:	8b b3 90 03 00 00    	mov    0x390(%rbx),%esi
   data->lastgroup = thisgroup;
  4020fd:	89 83 88 03 00 00    	mov    %eax,0x388(%rbx)
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
  402103:	4c 8b 8b 48 03 00 00 	mov    0x348(%rbx),%r9
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  40210a:	89 f0                	mov    %esi,%eax
  40210c:	c1 e0 07             	shl    $0x7,%eax
  40210f:	48 98                	cltq
  402111:	48 8b 0c c2          	mov    (%rdx,%rax,8),%rcx
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
  402115:	48 63 d6             	movslq %esi,%rdx
  402118:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
  40211c:	41 8b 04 81          	mov    (%r9,%rax,4),%eax
  402120:	48 85 c9             	test   %rcx,%rcx
  402123:	74 0c                	je     402131 <threadwork+0xc1>
  402125:	48 63 f8             	movslq %eax,%rdi
  402128:	48 39 cf             	cmp    %rcx,%rdi
  40212b:	0f 8d 57 01 00 00    	jge    402288 <threadwork+0x218>
    for (int x = 0; x < data->threadsize - 1; x++) {
  402131:	44 8b 53 68          	mov    0x68(%rbx),%r10d
  402135:	41 83 ea 01          	sub    $0x1,%r10d
  402139:	45 85 d2             	test   %r10d,%r10d
  40213c:	0f 8e 46 01 00 00    	jle    402288 <threadwork+0x218>
  402142:	45 31 db             	xor    %r11d,%r11d
  402145:	eb 25                	jmp    40216c <threadwork+0xfc>
  402147:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  402150:	41 83 c3 01          	add    $0x1,%r11d
  402154:	45 39 d3             	cmp    %r10d,%r11d
  402157:	0f 8d 2b 01 00 00    	jge    402288 <threadwork+0x218>
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  40215d:	48 63 d6             	movslq %esi,%rdx
        if (data->main->works[buffer] != -1) {
  402160:	4c 8b 63 28          	mov    0x28(%rbx),%r12
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  402164:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
  402168:	41 8b 04 81          	mov    (%r9,%rax,4),%eax
  40216c:	83 e8 01             	sub    $0x1,%eax
  40216f:	4c 8d 04 52          	lea    (%rdx,%rdx,2),%r8
   data->freq++;
  402173:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  402178:	48 63 d0             	movslq %eax,%rdx
  40217b:	41 89 c5             	mov    %eax,%r13d
  40217e:	49 c1 e0 02          	shl    $0x2,%r8
  402182:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  402189:	41 c1 fd 1f          	sar    $0x1f,%r13d
  40218d:	4b 8d 3c 01          	lea    (%r9,%r8,1),%rdi
    int cursor = data->globalread[data->laststream].cursor;
  402191:	8b 4f 04             	mov    0x4(%rdi),%ecx
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  402194:	48 c1 ea 20          	shr    $0x20,%rdx
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  402198:	41 89 ce             	mov    %ecx,%r14d
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  40219b:	01 c2                	add    %eax,%edx
  40219d:	c1 fa 07             	sar    $0x7,%edx
  4021a0:	44 29 ea             	sub    %r13d,%edx
  4021a3:	41 89 d5             	mov    %edx,%r13d
  4021a6:	41 c1 e5 08          	shl    $0x8,%r13d
  4021aa:	41 29 d5             	sub    %edx,%r13d
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  4021ad:	31 d2                	xor    %edx,%edx
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  4021af:	44 29 e8             	sub    %r13d,%eax
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  4021b2:	41 89 f5             	mov    %esi,%r13d
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  4021b5:	48 98                	cltq
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  4021b7:	48 85 c0             	test   %rax,%rax
  4021ba:	48 0f 48 c2          	cmovs  %rdx,%rax
  4021be:	48 63 d1             	movslq %ecx,%rdx
  4021c1:	41 c1 fe 1f          	sar    $0x1f,%r14d
  4021c5:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  4021cc:	41 c1 e5 18          	shl    $0x18,%r13d
  4021d0:	48 c1 e0 10          	shl    $0x10,%rax
  4021d4:	48 c1 ea 20          	shr    $0x20,%rdx
  4021d8:	01 ca                	add    %ecx,%edx
  4021da:	c1 fa 07             	sar    $0x7,%edx
  4021dd:	44 29 f2             	sub    %r14d,%edx
  4021e0:	41 89 d6             	mov    %edx,%r14d
  4021e3:	41 c1 e6 08          	shl    $0x8,%r14d
  4021e7:	41 29 d6             	sub    %edx,%r14d
  4021ea:	89 ca                	mov    %ecx,%edx
  4021ec:	44 29 f2             	sub    %r14d,%edx
  4021ef:	41 09 d5             	or     %edx,%r13d
  4021f2:	4d 63 ed             	movslq %r13d,%r13
  4021f5:	4c 09 e8             	or     %r13,%rax
        if (data->main->works[buffer] != -1) {
  4021f8:	49 03 44 24 70       	add    0x70(%r12),%rax
  4021fd:	80 38 ff             	cmpb   $0xff,(%rax)
  402200:	74 2d                	je     40222f <threadwork+0x1bf>
          data->successreads++;
  402202:	48 83 83 98 03 00 00 01 	addq   $0x1,0x398(%rbx)
          data->main->works[buffer] = -1;
  40220a:	c6 00 ff             	movb   $0xff,(%rax)
    if (data->globalread[thistream].cursor < cursorlimit) {
  40220d:	4c 8b 8b 48 03 00 00 	mov    0x348(%rbx),%r9
    for (int x = 0; x < data->threadsize - 1; x++) {
  402214:	44 8b 53 68          	mov    0x68(%rbx),%r10d
      data->laststream = (data->laststream + 1);
  402218:	8b b3 90 03 00 00    	mov    0x390(%rbx),%esi
    if (data->globalread[thistream].cursor < cursorlimit) {
  40221e:	4b 8d 3c 01          	lea    (%r9,%r8,1),%rdi
    if (data->laststream == data->mystream) {
  402222:	8b ab 8c 03 00 00    	mov    0x38c(%rbx),%ebp
    if (data->globalread[thistream].cursor < cursorlimit) {
  402228:	8b 4f 04             	mov    0x4(%rdi),%ecx
  40222b:	41 83 ea 01          	sub    $0x1,%r10d
  40222f:	83 f9 04             	cmp    $0x4,%ecx
  402232:	7f 09                	jg     40223d <threadwork+0x1cd>
      data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1);
  402234:	83 c1 01             	add    $0x1,%ecx
      data->globalread[thistream].global++;
  402237:	83 07 01             	addl   $0x1,(%rdi)
      data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1);
  40223a:	89 4f 04             	mov    %ecx,0x4(%rdi)
    if (data->globalread[thistream].cursor == cursorlimit) {
  40223d:	83 f9 05             	cmp    $0x5,%ecx
  402240:	75 10                	jne    402252 <threadwork+0x1e2>
      data->laststream = (data->laststream + 1);
  402242:	83 c6 01             	add    $0x1,%esi
  402245:	89 b3 90 03 00 00    	mov    %esi,0x390(%rbx)
data->globalread[thistream].cursor = 0;
  40224b:	c7 47 04 00 00 00 00 	movl   $0x0,0x4(%rdi)
    if (data->laststream == data->mystream) {
  402252:	39 f5                	cmp    %esi,%ebp
  402254:	75 09                	jne    40225f <threadwork+0x1ef>
      data->laststream = data->laststream + 1;
  402256:	8d 75 01             	lea    0x1(%rbp),%esi
  402259:	89 b3 90 03 00 00    	mov    %esi,0x390(%rbx)
    if (data->laststream == 5) {
  40225f:	83 fe 05             	cmp    $0x5,%esi
  402262:	0f 85 e8 fe ff ff    	jne    402150 <threadwork+0xe0>
       data->laststream = 1;
  402268:	c7 83 90 03 00 00 01 00 00 00 	movl   $0x1,0x390(%rbx)
    for (int x = 0; x < data->threadsize - 1; x++) {
  402272:	41 83 c3 01          	add    $0x1,%r11d
  402276:	45 39 d3             	cmp    %r10d,%r11d
  402279:	7d 0d                	jge    402288 <threadwork+0x218>
  40227b:	be 01 00 00 00       	mov    $0x1,%esi
  402280:	e9 d8 fe ff ff       	jmp    40215d <threadwork+0xed>
  402285:	0f 1f 00             	nopl   (%rax)
}
  402288:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  40228d:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  402296:	0f 85 4c 01 00 00    	jne    4023e8 <threadwork+0x378>
  40229c:	48 83 c4 20          	add    $0x20,%rsp
  4022a0:	31 c0                	xor    %eax,%eax
  4022a2:	5b                   	pop    %rbx
  4022a3:	5d                   	pop    %rbp
  4022a4:	41 5c                	pop    %r12
  4022a6:	41 5d                	pop    %r13
  4022a8:	41 5e                	pop    %r14
  4022aa:	c3                   	ret
  4022ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
   for (int x = 0 ; x < data->threadsize ; x++) {
  4022b0:	8b 43 68             	mov    0x68(%rbx),%eax
  4022b3:	85 c0                	test   %eax,%eax
  4022b5:	0f 8e d2 00 00 00    	jle    40238d <threadwork+0x31d>
    int cursor = data->writecursor;
  4022bb:	8b 8b 80 01 00 00    	mov    0x180(%rbx),%ecx
   for (int x = 0 ; x < data->threadsize ; x++) {
  4022c1:	31 f6                	xor    %esi,%esi
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  4022c3:	49 b8 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%r8
  4022cd:	0f 1f 00             	nopl   (%rax)
  4022d0:	44 8b 93 8c 03 00 00 	mov    0x38c(%rbx),%r10d
  4022d7:	4c 8b 4b 28          	mov    0x28(%rbx),%r9
    if (data->threadindex == 1) {
  4022db:	8b 7b 64             	mov    0x64(%rbx),%edi
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  4022de:	44 89 d0             	mov    %r10d,%eax
  4022e1:	49 8b 91 80 03 00 00 	mov    0x380(%r9),%rdx
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  4022e8:	41 c1 e2 18          	shl    $0x18,%r10d
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  4022ec:	c1 e0 07             	shl    $0x7,%eax
  4022ef:	48 98                	cltq
  4022f1:	4c 8b 1c c2          	mov    (%rdx,%rax,8),%r11
  4022f5:	4c 89 d8             	mov    %r11,%rax
  4022f8:	49 f7 e8             	imul   %r8
  4022fb:	4c 89 d8             	mov    %r11,%rax
  4022fe:	48 c1 f8 3f          	sar    $0x3f,%rax
  402302:	4c 01 da             	add    %r11,%rdx
  402305:	48 c1 fa 07          	sar    $0x7,%rdx
  402309:	48 29 c2             	sub    %rax,%rdx
  40230c:	48 89 d0             	mov    %rdx,%rax
  40230f:	48 c1 e0 08          	shl    $0x8,%rax
  402313:	48 29 d0             	sub    %rdx,%rax
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  402316:	48 63 d1             	movslq %ecx,%rdx
  402319:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  402320:	49 29 c3             	sub    %rax,%r11
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  402323:	89 c8                	mov    %ecx,%eax
  402325:	c1 f8 1f             	sar    $0x1f,%eax
  402328:	41 c1 e3 10          	shl    $0x10,%r11d
  40232c:	48 c1 ea 20          	shr    $0x20,%rdx
  402330:	01 ca                	add    %ecx,%edx
  402332:	c1 fa 07             	sar    $0x7,%edx
  402335:	29 c2                	sub    %eax,%edx
  402337:	89 d0                	mov    %edx,%eax
  402339:	c1 e0 08             	shl    $0x8,%eax
  40233c:	29 d0                	sub    %edx,%eax
  40233e:	29 c1                	sub    %eax,%ecx
  402340:	44 09 d1             	or     %r10d,%ecx
  402343:	44 09 d9             	or     %r11d,%ecx
  if (data->main->works[buffer] != -1) {
  402346:	48 63 c9             	movslq %ecx,%rcx
  402349:	49 03 49 70          	add    0x70(%r9),%rcx
  40234d:	80 39 ff             	cmpb   $0xff,(%rcx)
  402350:	74 5e                	je     4023b0 <threadwork+0x340>
    data->freq_writes++;
  402352:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
   for (int x = 0 ; x < data->threadsize ; x++) {
  402357:	83 c6 01             	add    $0x1,%esi
  data->main->works[buffer] = data->threadindex;
  40235a:	40 88 39             	mov    %dil,(%rcx)
    data->writecursor = (data->writecursor + 1) % cursorlimit;
  40235d:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
  402363:	83 c0 01             	add    $0x1,%eax
  402366:	48 63 c8             	movslq %eax,%rcx
  402369:	99                   	cltd
  40236a:	48 69 c9 67 66 66 66 	imul   $0x66666667,%rcx,%rcx
  402371:	48 c1 f9 21          	sar    $0x21,%rcx
  402375:	29 d1                	sub    %edx,%ecx
  402377:	8d 14 89             	lea    (%rcx,%rcx,4),%edx
  40237a:	29 d0                	sub    %edx,%eax
  40237c:	89 83 80 01 00 00    	mov    %eax,0x180(%rbx)
  402382:	89 c1                	mov    %eax,%ecx
   for (int x = 0 ; x < data->threadsize ; x++) {
  402384:	3b 73 68             	cmp    0x68(%rbx),%esi
  402387:	0f 8c 43 ff ff ff    	jl     4022d0 <threadwork+0x260>
    __atomic_fetch_add(&data->main->globalwrite[data->mystream * 128], 1, __ATOMIC_RELAXED);
  40238d:	48 8b 53 28          	mov    0x28(%rbx),%rdx
  402391:	8b 83 8c 03 00 00    	mov    0x38c(%rbx),%eax
  402397:	48 8b 92 80 03 00 00 	mov    0x380(%rdx),%rdx
  40239e:	c1 e0 07             	shl    $0x7,%eax
  4023a1:	48 98                	cltq
  4023a3:	f0 48 83 04 c2 01    	lock addq $0x1,(%rdx,%rax,8)
  4023a9:	e9 16 fd ff ff       	jmp    4020c4 <threadwork+0x54>
  4023ae:	66 90                	xchg   %ax,%ax
  data->main->works[buffer] = data->threadindex;
  4023b0:	40 88 39             	mov    %dil,(%rcx)
    data->writecursor = (data->writecursor + 1) % cursorlimit;
  4023b3:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
   for (int x = 0 ; x < data->threadsize ; x++) {
  4023b9:	83 c6 01             	add    $0x1,%esi
    data->writecursor = (data->writecursor + 1) % cursorlimit;
  4023bc:	83 c0 01             	add    $0x1,%eax
  4023bf:	48 63 c8             	movslq %eax,%rcx
  4023c2:	99                   	cltd
  4023c3:	48 69 c9 67 66 66 66 	imul   $0x66666667,%rcx,%rcx
  4023ca:	48 c1 f9 21          	sar    $0x21,%rcx
  4023ce:	29 d1                	sub    %edx,%ecx
  4023d0:	8d 14 89             	lea    (%rcx,%rcx,4),%edx
  4023d3:	29 d0                	sub    %edx,%eax
  4023d5:	89 83 80 01 00 00    	mov    %eax,0x180(%rbx)
  4023db:	89 c1                	mov    %eax,%ecx
   for (int x = 0 ; x < data->threadsize ; x++) {
  4023dd:	39 73 68             	cmp    %esi,0x68(%rbx)
  4023e0:	0f 8f ea fe ff ff    	jg     4022d0 <threadwork+0x260>
  4023e6:	eb a5                	jmp    40238d <threadwork+0x31d>
}
  4023e8:	e8 93 ec ff ff       	call   401080 <__stack_chk_fail@plt>
  4023ed:	0f 1f 00             	nopl   (%rax)

00000000004023f0 <work>:
void * work(void * arg) {
  4023f0:	53                   	push   %rbx
  4023f1:	8b 57 64             	mov    0x64(%rdi),%edx
  4023f4:	48 89 fb             	mov    %rdi,%rbx
  4023f7:	48 8d 35 15 0c 00 00 	lea    0xc15(%rip),%rsi        # 403013 <_IO_stdin_used+0x13>
  4023fe:	bf 01 00 00 00       	mov    $0x1,%edi
  402403:	31 c0                	xor    %eax,%eax
  402405:	e8 c6 ec ff ff       	call   4010d0 <__printf_chk@plt>
  while (data->running > 0)  {
  40240a:	8b 53 5c             	mov    0x5c(%rbx),%edx
  40240d:	85 d2                	test   %edx,%edx
  40240f:	7e 16                	jle    402427 <work+0x37>
  402411:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      threadwork(data);
  402418:	48 89 df             	mov    %rbx,%rdi
  40241b:	e8 50 fc ff ff       	call   402070 <threadwork>
  while (data->running > 0)  {
  402420:	8b 43 5c             	mov    0x5c(%rbx),%eax
  402423:	85 c0                	test   %eax,%eax
  402425:	7f f1                	jg     402418 <work+0x28>
  402427:	8b 53 64             	mov    0x64(%rbx),%edx
  40242a:	48 8d 35 f5 0b 00 00 	lea    0xbf5(%rip),%rsi        # 403026 <_IO_stdin_used+0x26>
  402431:	bf 01 00 00 00       	mov    $0x1,%edi
  402436:	31 c0                	xor    %eax,%eax
  402438:	e8 93 ec ff ff       	call   4010d0 <__printf_chk@plt>
}
  40243d:	5b                   	pop    %rbx
  40243e:	c3                   	ret
  40243f:	90                   	nop

0000000000402440 <work2>:
  while (data->running == 1) {
  402440:	eb 0b                	jmp    40244d <work2+0xd>
  402442:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  402448:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  40244d:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  402451:	74 f5                	je     402448 <work2+0x8>
}
  402453:	c3                   	ret
  402454:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40245e:	66 90                	xchg   %ax,%ax

0000000000402460 <.MSG>:
  402460:	43                   	rex.XB
  402461:	4f 20 43 6f          	rex.WRXB and %r8b,0x6f(%r11)
  402465:	72 6f                	jb     4024d6 <switch_to+0x29>
  402467:	75 74                	jne    4024dd <switch_to+0x30>
  402469:	69 6e 65 53 74 72 75 	imul   $0x75727453,0x65(%rsi),%ebp
  402470:	63 74 20 25          	movsxd 0x25(%rax,%riz,1),%esi
  402474:	78 0a                	js     402480 <.EIP+0x9>
	...

0000000000402477 <.EIP>:
  402477:	43                   	rex.XB
  402478:	4f 20 45 49          	rex.WRXB and %r8b,0x49(%r13)
  40247c:	50                   	push   %rax
  40247d:	2e                   	cs
  40247e:	2e                   	cs
  40247f:	2e                   	cs
  402480:	20                   	.byte 0x20
  402481:	25                   	.byte 0x25
  402482:	78 0a                	js     40248e <.CODATA+0x9>
	...

0000000000402485 <.CODATA>:
  402485:	43                   	rex.XB
  402486:	4f 20 63 6f          	rex.WRXB and %r12b,0x6f(%r11)
  40248a:	64 61                	fs (bad)
  40248c:	74 61                	je     4024ef <switch_to+0x42>
  40248e:	2e                   	cs
  40248f:	2e                   	cs
  402490:	2e                   	cs
  402491:	20                   	.byte 0x20
  402492:	25                   	.byte 0x25
  402493:	78 0a                	js     40249f <.INDEX+0x9>
	...

0000000000402496 <.INDEX>:
  402496:	43 6f                	rex.XB outsl %ds:(%rsi),(%dx)
  402498:	72 6f                	jb     402509 <switch_to+0x5c>
  40249a:	75 74                	jne    402510 <switch_to+0x63>
  40249c:	69 6e 65 20 69 6e 64 	imul   $0x646e6920,0x65(%rsi),%ebp
  4024a3:	65 78 2e             	gs js  4024d4 <switch_to+0x27>
  4024a6:	2e                   	cs
  4024a7:	2e                   	cs
  4024a8:	20                   	.byte 0x20
  4024a9:	25                   	.byte 0x25
  4024aa:	64 0a 00             	or     %fs:(%rax),%al

00000000004024ad <switch_to>:
	.text
	# switch_to(struct Coroutine * coroutines, int index, struct Scheduler * scheduler)
	# rdi, %rsi, %rdx, %rcx, %r8 and %r9
switch_to:
# popq %r11
pushq %rbp
  4024ad:	55                   	push   %rbp

movq %rsp, %rbp
  4024ae:	48 89 e5             	mov    %rsp,%rbp
subq $1024, %rsp
  4024b1:	48 81 ec 00 04 00 00 	sub    $0x400,%rsp



movq %rdi, -56(%rbp) # coroutine table
  4024b8:	48 89 7d c8          	mov    %rdi,-0x38(%rbp)
movq %rsi, -8(%rbp) # index
  4024bc:	48 89 75 f8          	mov    %rsi,-0x8(%rbp)
movq %rdx, -16(%rbp) # scheduler
  4024c0:	48 89 55 f0          	mov    %rdx,-0x10(%rbp)

movq %rsi, %rax
  4024c4:	48 89 f0             	mov    %rsi,%rax
imul $32, %rax
  4024c7:	48 6b c0 20          	imul   $0x20,%rax,%rax
addq %rdi, %rax
  4024cb:	48 01 f8             	add    %rdi,%rax
mov %rax, %r11
  4024ce:	49 89 c3             	mov    %rax,%r11

mov %r11, %rax
  4024d1:	4c 89 d8             	mov    %r11,%rax
movq %rax, %r9
  4024d4:	49 89 c1             	mov    %rax,%r9
movq %r9, -24(%rbp) # coroutine object
  4024d7:	4c 89 4d e8          	mov    %r9,-0x18(%rbp)

movq %r11, %rax
  4024db:	4c 89 d8             	mov    %r11,%rax
leaq 8(%rax), %rax
  4024de:	48 8d 40 08          	lea    0x8(%rax),%rax
movq %rax, %r9
  4024e2:	49 89 c1             	mov    %rax,%r9
movq %r9, -48(%rbp) # rsp
  4024e5:	4c 89 4d d0          	mov    %r9,-0x30(%rbp)

movq %r11, %rax
  4024e9:	4c 89 d8             	mov    %r11,%rax
leaq 16(%rax), %rax
  4024ec:	48 8d 40 10          	lea    0x10(%rax),%rax
movq (%rax), %r9
  4024f0:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -32(%rbp) # coroutine function
  4024f3:	4c 89 4d e0          	mov    %r9,-0x20(%rbp)

movq %r11, %rax
  4024f7:	4c 89 d8             	mov    %r11,%rax
leaq 24(%rax), %rax # load from coroutine object data object
  4024fa:	48 8d 40 18          	lea    0x18(%rax),%rax
movq (%rax), %r9
  4024fe:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -40(%rbp) # coroutine data object
  402501:	4c 89 4d d8          	mov    %r9,-0x28(%rbp)
movq (%rax), %rcx
  402505:	48 8b 08             	mov    (%rax),%rcx

movq -24(%rbp), %r11
  402508:	4c 8b 5d e8          	mov    -0x18(%rbp),%r11
#

leaq .INDEX(%rip), %rdi
  40250c:	48 8d 3d 83 ff ff ff 	lea    -0x7d(%rip),%rdi        # 402496 <.INDEX>
#call printf@plt
mov $0, %eax
  402513:	b8 00 00 00 00       	mov    $0x0,%eax

#pushq %r11
leaq .MSG(%rip), %rdi
  402518:	48 8d 3d 41 ff ff ff 	lea    -0xbf(%rip),%rdi        # 402460 <.MSG>
movq %r11, %rsi
  40251f:	4c 89 de             	mov    %r11,%rsi
# call printf@plt
mov $0, %eax
  402522:	b8 00 00 00 00       	mov    $0x0,%eax

#popq %r11

#pushq %r9
movq -32(%rbp), %r9
  402527:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9

leaq .EIP(%rip), %rdi
  40252b:	48 8d 3d 45 ff ff ff 	lea    -0xbb(%rip),%rdi        # 402477 <.EIP>
movq %r9, %rsi
  402532:	4c 89 ce             	mov    %r9,%rsi
#call printf@plt
mov $0, %eax
  402535:	b8 00 00 00 00       	mov    $0x0,%eax
#popq %r9
# coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data

#pushq %r9
leaq .CODATA(%rip), %rdi
  40253a:	48 8d 3d 44 ff ff ff 	lea    -0xbc(%rip),%rdi        # 402485 <.CODATA>
movq -40(%rbp), %rsi
  402541:	48 8b 75 d8          	mov    -0x28(%rbp),%rsi
#call printf@plt
mov $0, %eax
  402545:	b8 00 00 00 00       	mov    $0x0,%eax
#popq %r9

movq -16(%rbp), %rdi
  40254a:	48 8b 7d f0          	mov    -0x10(%rbp),%rdi
movq -24(%rbp), %rsi
  40254e:	48 8b 75 e8          	mov    -0x18(%rbp),%rsi
movq -40(%rbp), %rdx
  402552:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx



movq -32(%rbp), %r9
  402556:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9
#leaq after(%rip), %r11

#movq %rbp, %rsp
# popq %rbp
add $1024, %rsp
  40255a:	48 81 c4 00 04 00 00 	add    $0x400,%rsp
# add $8, %rsp
 #popq %r11
 popq %r11
  402561:	41 5b                	pop    %r11
#pushq %r11
#movq %r11, %rsp
jmp *%r9
  402563:	41 ff e1             	jmp    *%r9

Disassembly of section .fini:

0000000000402568 <_fini>:
  402568:	f3 0f 1e fa          	endbr64
  40256c:	48 83 ec 08          	sub    $0x8,%rsp
  402570:	48 83 c4 08          	add    $0x8,%rsp
  402574:	c3                   	ret
