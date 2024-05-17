
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
  40112c:	48 8d 35 f4 1e 00 00 	lea    0x1ef4(%rip),%rsi        # 403027 <_IO_stdin_used+0x27>
  401133:	41 56                	push   %r14
    
    data[x].coroutines = cos;
    for (int y= 0; y < 10; y++ ) {
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
      cos[y].data = codata;
      cos[y].eip = (uint64_t)coroutine_func;
  401135:	41 be 01 00 00 00    	mov    $0x1,%r14d
int main(int argc, char **argv) {
  40113b:	41 55                	push   %r13
  40113d:	41 54                	push   %r12
  char *works = calloc(worksize, sizeof(char));
  40113f:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
int main(int argc, char **argv) {
  401145:	55                   	push   %rbp
  401146:	53                   	push   %rbx
  401147:	48 81 ec a8 00 00 00 	sub    $0xa8,%rsp
  40114e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401157:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  40115f:	31 c0                	xor    %eax,%eax
  401161:	e8 6a ff ff ff       	call   4010d0 <__printf_chk@plt>
  401166:	ba 04 00 00 00       	mov    $0x4,%edx
  40116b:	48 8d 35 c7 1e 00 00 	lea    0x1ec7(%rip),%rsi        # 403039 <_IO_stdin_used+0x39>
  401172:	31 c0                	xor    %eax,%eax
  401174:	bf 01 00 00 00       	mov    $0x1,%edi
  401179:	e8 52 ff ff ff       	call   4010d0 <__printf_chk@plt>
  40117e:	ba 20 00 00 00       	mov    $0x20,%edx
  401183:	48 8d 35 ab 1e 00 00 	lea    0x1eab(%rip),%rsi        # 403035 <_IO_stdin_used+0x35>
  40118a:	31 c0                	xor    %eax,%eax
  40118c:	bf 01 00 00 00       	mov    $0x1,%edi
  401191:	e8 3a ff ff ff       	call   4010d0 <__printf_chk@plt>
  401196:	ba 0f 00 00 00       	mov    $0xf,%edx
  40119b:	48 8d 35 a6 1e 00 00 	lea    0x1ea6(%rip),%rsi        # 403048 <_IO_stdin_used+0x48>
  4011a2:	31 c0                	xor    %eax,%eax
  4011a4:	bf 01 00 00 00       	mov    $0x1,%edi
  4011a9:	e8 22 ff ff ff       	call   4010d0 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  4011ae:	be 08 00 00 00       	mov    $0x8,%esi
  4011b3:	bf 0f 00 00 00       	mov    $0xf,%edi
  4011b8:	e8 03 ff ff ff       	call   4010c0 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  4011bd:	be 38 00 00 00       	mov    $0x38,%esi
  4011c2:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  4011c7:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  4011cc:	e8 ef fe ff ff       	call   4010c0 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011d1:	be 00 3c 00 00       	mov    $0x3c00,%esi
  4011d6:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  4011db:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011e0:	e8 db fe ff ff       	call   4010c0 <calloc@plt>
  char *works = calloc(worksize, sizeof(char));
  4011e5:	be 01 00 00 00       	mov    $0x1,%esi
  4011ea:	4c 89 e7             	mov    %r12,%rdi
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011ed:	49 89 c5             	mov    %rax,%r13
  char *works = calloc(worksize, sizeof(char));
  4011f0:	e8 cb fe ff ff       	call   4010c0 <calloc@plt>
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  4011f5:	4c 89 e2             	mov    %r12,%rdx
  4011f8:	be ff ff ff ff       	mov    $0xffffffff,%esi
  4011fd:	48 89 c7             	mov    %rax,%rdi
  401200:	48 89 c3             	mov    %rax,%rbx
  401203:	e8 a8 fe ff ff       	call   4010b0 <memset@plt>
  401208:	4c 89 e2             	mov    %r12,%rdx
  40120b:	bf 01 00 00 00       	mov    $0x1,%edi
  401210:	31 c0                	xor    %eax,%eax
  401212:	48 8d 35 44 1e 00 00 	lea    0x1e44(%rip),%rsi        # 40305d <_IO_stdin_used+0x5d>
  401219:	e8 b2 fe ff ff       	call   4010d0 <__printf_chk@plt>
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  40121e:	be 20 00 00 00       	mov    $0x20,%esi
  401223:	bf 64 00 00 00       	mov    $0x64,%edi
  401228:	e8 93 fe ff ff       	call   4010c0 <calloc@plt>
  40122d:	31 d2                	xor    %edx,%edx
  40122f:	bf 01 00 00 00       	mov    $0x1,%edi
  401234:	48 8d 35 33 1e 00 00 	lea    0x1e33(%rip),%rsi        # 40306e <_IO_stdin_used+0x6e>
  40123b:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  401240:	31 c0                	xor    %eax,%eax
  401242:	e8 89 fe ff ff       	call   4010d0 <__printf_chk@plt>
  401247:	4c 89 e2             	mov    %r12,%rdx
  40124a:	bf 01 00 00 00       	mov    $0x1,%edi
  40124f:	31 c0                	xor    %eax,%eax
  401251:	48 8d 35 22 1e 00 00 	lea    0x1e22(%rip),%rsi        # 40307a <_IO_stdin_used+0x7a>
  401258:	e8 73 fe ff ff       	call   4010d0 <__printf_chk@plt>
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  40125d:	be 04 00 00 00       	mov    $0x4,%esi
  401262:	bf 0f 00 00 00       	mov    $0xf,%edi
  401267:	e8 54 fe ff ff       	call   4010c0 <calloc@plt>
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  40126c:	ba 00 02 00 00       	mov    $0x200,%edx
  401271:	48 8d 7c 24 68       	lea    0x68(%rsp),%rdi
  401276:	be 80 00 00 00       	mov    $0x80,%esi
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  40127b:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  401280:	e8 7b fe ff ff       	call   401100 <posix_memalign@plt>
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  401285:	be 0c 00 00 00       	mov    $0xc,%esi
  40128a:	bf 0f 00 00 00       	mov    $0xf,%edi
  40128f:	85 c0                	test   %eax,%eax
  401291:	b8 00 00 00 00       	mov    $0x0,%eax
  401296:	48 0f 44 44 24 68    	cmove  0x68(%rsp),%rax
  40129c:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  4012a1:	e8 1a fe ff ff       	call   4010c0 <calloc@plt>
  data[0].works = works;
  4012a6:	49 89 5d 70          	mov    %rbx,0x70(%r13)
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  4012aa:	be 14 00 00 00       	mov    $0x14,%esi
  4012af:	bf 00 e1 f5 05       	mov    $0x5f5e100,%edi
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  4012b4:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  4012b9:	e8 02 fe ff ff       	call   4010c0 <calloc@plt>
  struct Access * writes = calloc(accesssize, sizeof(struct Access));
  4012be:	be 14 00 00 00       	mov    $0x14,%esi
  4012c3:	bf 00 e1 f5 05       	mov    $0x5f5e100,%edi
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  4012c8:	48 89 c3             	mov    %rax,%rbx
  struct Access * writes = calloc(accesssize, sizeof(struct Access));
  4012cb:	e8 f0 fd ff ff       	call   4010c0 <calloc@plt>
  4012d0:	66 48 0f 6e eb       	movq   %rbx,%xmm5
  struct Scheduler * scheduler = calloc(1, sizeof(struct Scheduler));
  4012d5:	be 08 00 00 00       	mov    $0x8,%esi
  4012da:	bf 01 00 00 00       	mov    $0x1,%edi
  4012df:	66 48 0f 6e f0       	movq   %rax,%xmm6
  4012e4:	66 0f 6c ee          	punpcklqdq %xmm6,%xmm5
  4012e8:	0f 29 6c 24 40       	movaps %xmm5,0x40(%rsp)
  4012ed:	e8 ce fd ff ff       	call   4010c0 <calloc@plt>
      cos[y].eip = (uint64_t)coroutine_func;
  4012f2:	c7 04 24 00 00 00 00 	movl   $0x0,(%rsp)
  4012f9:	48 c7 c5 50 1c 40 00 	mov    $0x401c50,%rbp
  struct Scheduler * scheduler = calloc(1, sizeof(struct Scheduler));
  401300:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  for (int x = 0; x < threadsize ; x++) {
  401305:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
  40130a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    struct Coroutine * cos = calloc(10, sizeof(struct Coroutine));
  401310:	be 20 00 00 00       	mov    $0x20,%esi
  401315:	bf 0a 00 00 00       	mov    $0xa,%edi
  40131a:	44 89 74 24 0c       	mov    %r14d,0xc(%rsp)
  40131f:	45 8d 66 ff          	lea    -0x1(%r14),%r12d
  401323:	e8 98 fd ff ff       	call   4010c0 <calloc@plt>
    data[x].coroutines = cos;
  401328:	49 89 85 c0 03 00 00 	mov    %rax,0x3c0(%r13)
    for (int y= 0; y < 10; y++ ) {
  40132f:	4c 8d 78 10          	lea    0x10(%rax),%r15
  401333:	48 8d 98 50 01 00 00 	lea    0x150(%rax),%rbx
  40133a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
  401340:	be 04 00 00 00       	mov    $0x4,%esi
  401345:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int y= 0; y < 10; y++ ) {
  40134a:	49 83 c7 20          	add    $0x20,%r15
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
  40134e:	e8 6d fd ff ff       	call   4010c0 <calloc@plt>
      cos[y].eip = (uint64_t)coroutine_func;
  401353:	49 89 6f e0          	mov    %rbp,-0x20(%r15)
      cos[y].data = codata;
  401357:	49 89 47 e8          	mov    %rax,-0x18(%r15)
    for (int y= 0; y < 10; y++ ) {
  40135b:	49 39 df             	cmp    %rbx,%r15
  40135e:	75 e0                	jne    401340 <main+0x220>
    } 
    data[x].scheduler = scheduler;
  401360:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    data[x].reads = reads;
  401365:	66 0f 6f 4c 24 40    	movdqa 0x40(%rsp),%xmm1
    data[x].writes = writes;
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  40136b:	be 80 00 00 00       	mov    $0x80,%esi
  401370:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0; x < threadsize ; x++) {
  401375:	49 81 c5 00 04 00 00 	add    $0x400,%r13
    data[x].scheduler = scheduler;
  40137c:	49 89 45 c8          	mov    %rax,-0x38(%r13)
    data[x].reads = reads;
  401380:	41 0f 29 4d a0       	movaps %xmm1,-0x60(%r13)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401385:	e8 36 fd ff ff       	call   4010c0 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  40138a:	0f b6 4c 24 0c       	movzbl 0xc(%rsp),%ecx
  40138f:	ba 01 00 00 00       	mov    $0x1,%edx
  401394:	48 8d 35 6d 1e 00 00 	lea    0x1e6d(%rip),%rsi        # 403208 <_IO_stdin_used+0x208>
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  40139b:	49 89 85 78 fc ff ff 	mov    %rax,-0x388(%r13)
  4013a2:	bf 01 00 00 00       	mov    $0x1,%edi
    CPU_SET(cpu += 1, data[x].cpu_set);
  4013a7:	48 d3 e2             	shl    %cl,%rdx
  4013aa:	48 09 10             	or     %rdx,(%rax)
  4013ad:	44 89 f1             	mov    %r14d,%ecx
  4013b0:	44 89 e2             	mov    %r12d,%edx
  4013b3:	31 c0                	xor    %eax,%eax
  4013b5:	e8 16 fd ff ff       	call   4010d0 <__printf_chk@plt>
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].bucketstart = x * buckets ;
    data[x].globalwrite = globalwrite;
  4013ba:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    data[x].bucketstart = x * buckets ;
  4013bf:	8b 1c 24             	mov    (%rsp),%ebx
    data[x].loglevel = debug;
    data[x].running = 2;
    data[x].threadindex = x;
  4013c2:	45 89 a5 64 fc ff ff 	mov    %r12d,-0x39c(%r13)
    data[x].chunksize = chunksize;
    data[x].chunkslen = chunkslen;
    data[x].newmask = 0;
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].mystream = 1 + (x / 4);
  4013c9:	41 c1 fc 02          	sar    $0x2,%r12d
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4013cd:	be 30 00 00 00       	mov    $0x30,%esi
  4013d2:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].loglevel = debug;
  4013d7:	41 c7 85 80 fc ff ff 00 00 00 00 	movl   $0x0,-0x380(%r13)
    data[x].globalwrite = globalwrite;
  4013e2:	49 89 45 80          	mov    %rax,-0x80(%r13)
    data[x].mystream = 1 + (x / 4);
  4013e6:	41 83 c4 01          	add    $0x1,%r12d
    data[x].running = 2;
  4013ea:	48 8b 05 8f 1e 00 00 	mov    0x1e8f(%rip),%rax        # 403280 <_IO_stdin_used+0x280>
    data[x].bucketstart = x * buckets ;
  4013f1:	41 89 9d 98 fc ff ff 	mov    %ebx,-0x368(%r13)
    data[x].read = 0;
  4013f8:	66 0f 6f 15 90 1e 00 00 	movdqa 0x1e90(%rip),%xmm2        # 403290 <_IO_stdin_used+0x290>
  for (int x = 0; x < threadsize ; x++) {
  401400:	81 c3 11 11 11 11    	add    $0x11111111,%ebx
    data[x].running = 2;
  401406:	49 89 85 5c fc ff ff 	mov    %rax,-0x3a4(%r13)
    data[x].readies = readies;
  40140d:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    data[x].chunkslen = chunkslen;
  401412:	66 0f 6f 1d 86 1e 00 00 	movdqa 0x1e86(%rip),%xmm3        # 4032a0 <_IO_stdin_used+0x2a0>
    data[x].prevread = threadsize;
  40141a:	66 0f 6f 25 8e 1e 00 00 	movdqa 0x1e8e(%rip),%xmm4        # 4032b0 <_IO_stdin_used+0x2b0>
    data[x].availables = buckets;
  401422:	41 c7 85 94 fc ff ff 11 11 11 11 	movl   $0x11111111,-0x36c(%r13)
    data[x].readies = readies;
  40142d:	49 89 85 20 fc ff ff 	mov    %rax,-0x3e0(%r13)
    data[x].threadsize = threadsize;
  401434:	41 c7 85 68 fc ff ff 0f 00 00 00 	movl   $0xf,-0x398(%r13)
    data[x].readies[x] = 0;
  40143f:	42 c7 44 b0 fc 00 00 00 00 	movl   $0x0,-0x4(%rax,%r14,4)
    data[x].main = &data[0];
  401448:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  for (int x = 0; x < threadsize ; x++) {
  40144d:	49 83 c6 01          	add    $0x1,%r14
    data[x].buckets = buckets;
  401451:	41 c7 85 90 fc ff ff 11 11 11 11 	movl   $0x11111111,-0x370(%r13)
    data[x].main = &data[0];
  40145c:	49 89 85 28 fc ff ff 	mov    %rax,-0x3d8(%r13)
    data[x].threads = data;
  401463:	49 89 85 30 fc ff ff 	mov    %rax,-0x3d0(%r13)
    data[x].freelist = freelist;
  40146a:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    data[x].readcursor = threadsize - 1;
  40146f:	41 c7 85 00 fe ff ff 0e 00 00 00 	movl   $0xe,-0x200(%r13)
    data[x].writecursor = 0;
  40147a:	41 c7 85 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%r13)
    data[x].freelist = freelist;
  401485:	49 89 85 a0 fc ff ff 	mov    %rax,-0x360(%r13)
    data[x].newmask = 0;
  40148c:	41 c7 85 c8 fc ff ff 00 00 00 00 	movl   $0x0,-0x338(%r13)
    data[x].mystream = 1 + (x / 4);
  401497:	45 89 65 8c          	mov    %r12d,-0x74(%r13)
    data[x].thiswrite = threadsize;
  40149b:	41 c7 85 28 ff ff ff 0f 00 00 00 	movl   $0xf,-0xd8(%r13)
    data[x].read = 0;
  4014a6:	41 0f 29 95 00 fc ff ff 	movaps %xmm2,-0x400(%r13)
    data[x].chunkslen = chunkslen;
  4014ae:	41 0f 11 9d b8 fc ff ff 	movups %xmm3,-0x348(%r13)
    data[x].prevread = threadsize;
  4014b6:	41 0f 11 a5 08 ff ff ff 	movups %xmm4,-0xf8(%r13)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4014be:	e8 fd fb ff ff       	call   4010c0 <calloc@plt>
    data[x].epochssize = epochs;
    data[x].globalread = globalread;
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  4014c3:	be 30 00 00 00       	mov    $0x30,%esi
  4014c8:	bf 10 27 00 00       	mov    $0x2710,%edi
    data[x].epochssize = epochs;
  4014cd:	41 c7 85 20 ff ff ff 80 96 98 00 	movl   $0x989680,-0xe0(%r13)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4014d8:	49 89 85 18 ff ff ff 	mov    %rax,-0xe8(%r13)
    data[x].globalread = globalread;
  4014df:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
  4014e4:	49 89 85 48 ff ff ff 	mov    %rax,-0xb8(%r13)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  4014eb:	e8 d0 fb ff ff       	call   4010c0 <calloc@plt>
    data[x].accesssize = accesssize;
  4014f0:	41 c7 45 b8 00 e1 f5 05 	movl   $0x5f5e100,-0x48(%r13)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  4014f8:	49 89 85 30 ff ff ff 	mov    %rax,-0xd0(%r13)
  for (int x = 0; x < threadsize ; x++) {
  4014ff:	89 1c 24             	mov    %ebx,(%rsp)
  401502:	49 83 fe 10          	cmp    $0x10,%r14
  401506:	0f 85 04 fe ff ff    	jne    401310 <main+0x1f0>
  40150c:	4c 8b 7c 24 50       	mov    0x50(%rsp),%r15
  401511:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
  401516:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
  40151b:	49 c7 c4 f0 23 40 00 	mov    $0x4023f0,%r12
  401522:	4c 89 3c 24          	mov    %r15,(%rsp)
  401526:	48 8d 83 48 03 00 00 	lea    0x348(%rbx),%rax
  40152d:	4c 89 ed             	mov    %r13,%rbp
  401530:	49 89 c6             	mov    %rax,%r14
  401533:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  401538:	48 89 e9             	mov    %rbp,%rcx
  40153b:	48 89 de             	mov    %rbx,%rsi
  40153e:	4c 89 ff             	mov    %r15,%rdi
  401541:	4c 89 e2             	mov    %r12,%rdx
  401544:	e8 97 fb ff ff       	call   4010e0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401549:	48 8b 55 78          	mov    0x78(%rbp),%rdx
  40154d:	49 8b 3f             	mov    (%r15),%rdi
  401550:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  401555:	48 83 c3 38          	add    $0x38,%rbx
  401559:	49 83 c7 08          	add    $0x8,%r15
  40155d:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401564:	e8 d7 fa ff ff       	call   401040 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  401569:	4c 39 f3             	cmp    %r14,%rbx
  40156c:	75 ca                	jne    401538 <main+0x418>
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  40156e:	48 8d 7c 24 70       	lea    0x70(%rsp),%rdi
  struct timespec time = {
  401573:	66 0f 6f 05 45 1d 00 00 	movdqa 0x1d45(%rip),%xmm0        # 4032c0 <_IO_stdin_used+0x2c0>
  40157b:	48 8b 2c 24          	mov    (%rsp),%rbp
  nanosleep(&time, &rem);
  40157f:	48 8d b4 24 80 00 00 00 	lea    0x80(%rsp),%rsi
  401587:	4c 8d 64 24 60       	lea    0x60(%rsp),%r12
  struct timespec time = {
  40158c:	0f 29 44 24 70       	movaps %xmm0,0x70(%rsp)
  struct timespec rem = {
  401591:	66 0f ef c0          	pxor   %xmm0,%xmm0
  401595:	0f 29 84 24 80 00 00 00 	movaps %xmm0,0x80(%rsp)
  nanosleep(&time, &rem);
  40159d:	e8 ee fa ff ff       	call   401090 <nanosleep@plt>
  4015a2:	48 8d 3d dd 1a 00 00 	lea    0x1add(%rip),%rdi        # 403086 <_IO_stdin_used+0x86>
  4015a9:	e8 a2 fa ff ff       	call   401050 <puts@plt>
  
  printf("runphased\n");
  for (int x = 0; x < threadsize ; x++) {
    data[x].running--;
  4015ae:	41 83 6d 5c 01       	subl   $0x1,0x5c(%r13)
  4015b3:	48 8d 3d d6 1a 00 00 	lea    0x1ad6(%rip),%rdi        # 403090 <_IO_stdin_used+0x90>
  4015ba:	41 83 ad 5c 04 00 00 01 	subl   $0x1,0x45c(%r13)
  4015c2:	41 83 ad 5c 08 00 00 01 	subl   $0x1,0x85c(%r13)
  4015ca:	41 83 ad 5c 0c 00 00 01 	subl   $0x1,0xc5c(%r13)
  4015d2:	41 83 ad 5c 10 00 00 01 	subl   $0x1,0x105c(%r13)
  4015da:	41 83 ad 5c 14 00 00 01 	subl   $0x1,0x145c(%r13)
  4015e2:	41 83 ad 5c 18 00 00 01 	subl   $0x1,0x185c(%r13)
  4015ea:	41 83 ad 5c 1c 00 00 01 	subl   $0x1,0x1c5c(%r13)
  4015f2:	41 83 ad 5c 20 00 00 01 	subl   $0x1,0x205c(%r13)
  4015fa:	41 83 ad 5c 24 00 00 01 	subl   $0x1,0x245c(%r13)
  401602:	41 83 ad 5c 28 00 00 01 	subl   $0x1,0x285c(%r13)
  40160a:	41 83 ad 5c 2c 00 00 01 	subl   $0x1,0x2c5c(%r13)
  401612:	41 83 ad 5c 30 00 00 01 	subl   $0x1,0x305c(%r13)
  40161a:	41 83 ad 5c 34 00 00 01 	subl   $0x1,0x345c(%r13)
  401622:	41 83 ad 5c 38 00 00 01 	subl   $0x1,0x385c(%r13)
  40162a:	e8 21 fa ff ff       	call   401050 <puts@plt>
  
 printf("draining\n");
 // time.tv_sec = 3;
//nanosleep(&time, &rem);
  for (int x = 0; x < threadsize ; x++) {
    data[x].running--;
  40162f:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
  401634:	41 83 6d 5c 01       	subl   $0x1,0x5c(%r13)
  401639:	41 83 ad 5c 04 00 00 01 	subl   $0x1,0x45c(%r13)
  401641:	41 83 ad 5c 08 00 00 01 	subl   $0x1,0x85c(%r13)
  401649:	41 83 ad 5c 0c 00 00 01 	subl   $0x1,0xc5c(%r13)
  401651:	41 83 ad 5c 10 00 00 01 	subl   $0x1,0x105c(%r13)
  401659:	41 83 ad 5c 14 00 00 01 	subl   $0x1,0x145c(%r13)
  401661:	41 83 ad 5c 18 00 00 01 	subl   $0x1,0x185c(%r13)
  401669:	41 83 ad 5c 1c 00 00 01 	subl   $0x1,0x1c5c(%r13)
  401671:	41 83 ad 5c 20 00 00 01 	subl   $0x1,0x205c(%r13)
  401679:	41 83 ad 5c 24 00 00 01 	subl   $0x1,0x245c(%r13)
  401681:	41 83 ad 5c 28 00 00 01 	subl   $0x1,0x285c(%r13)
  401689:	41 83 ad 5c 2c 00 00 01 	subl   $0x1,0x2c5c(%r13)
  401691:	41 83 ad 5c 30 00 00 01 	subl   $0x1,0x305c(%r13)
  401699:	41 83 ad 5c 34 00 00 01 	subl   $0x1,0x345c(%r13)
  4016a1:	41 83 ad 5c 38 00 00 01 	subl   $0x1,0x385c(%r13)
  for (int x = 0; x < threadsize ; x++) {
  4016a9:	48 83 c3 78          	add    $0x78,%rbx
  4016ad:	0f 1f 00             	nopl   (%rax)
  }
  
  //nanosleep(&time, &rem);
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  4016b0:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
  4016b4:	4c 89 e6             	mov    %r12,%rsi
  for (int x = 0; x < threadsize; x++) {
  4016b7:	48 83 c5 08          	add    $0x8,%rbp
    pthread_join(thread[x], &res);
  4016bb:	e8 50 fa ff ff       	call   401110 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  4016c0:	48 39 eb             	cmp    %rbp,%rbx
  4016c3:	75 eb                	jne    4016b0 <main+0x590>
  4016c5:	48 8d 3d cd 19 00 00 	lea    0x19cd(%rip),%rdi        # 403099 <_IO_stdin_used+0x99>
  4016cc:	49 8d 5d 48          	lea    0x48(%r13),%rbx
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  4016d0:	31 ed                	xor    %ebp,%ebp
  4016d2:	e8 79 f9 ff ff       	call   401050 <puts@plt>
  long sends = 1;
  for (int x = 0; x < threadsize; x++) {
  4016d7:	4d 8d b5 48 3c 00 00 	lea    0x3c48(%r13),%r14
  4016de:	4c 8d 25 c9 19 00 00 	lea    0x19c9(%rip),%r12        # 4030ae <_IO_stdin_used+0xae>
  4016e5:	0f 1f 00             	nopl   (%rax)
  4016e8:	48 8b 13             	mov    (%rbx),%rdx
  4016eb:	4c 89 e6             	mov    %r12,%rsi
  4016ee:	bf 01 00 00 00       	mov    $0x1,%edi
  4016f3:	31 c0                	xor    %eax,%eax
  4016f5:	48 81 c3 00 04 00 00 	add    $0x400,%rbx
  4016fc:	e8 cf f9 ff ff       	call   4010d0 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  401701:	48 03 ab 00 fc ff ff 	add    -0x400(%rbx),%rbp
  for (int x = 0; x < threadsize; x++) {
  401708:	49 39 de             	cmp    %rbx,%r14
  40170b:	75 db                	jne    4016e8 <main+0x5c8>
  40170d:	48 89 ea             	mov    %rbp,%rdx
  401710:	48 8d 35 a2 19 00 00 	lea    0x19a2(%rip),%rsi        # 4030b9 <_IO_stdin_used+0xb9>
  401717:	bf 01 00 00 00       	mov    $0x1,%edi
  40171c:	31 c0                	xor    %eax,%eax
  40171e:	e8 ad f9 ff ff       	call   4010d0 <__printf_chk@plt>
  401723:	48 89 ea             	mov    %rbp,%rdx
  401726:	bf 01 00 00 00       	mov    $0x1,%edi
  40172b:	31 c0                	xor    %eax,%eax
  40172d:	48 8d 35 90 19 00 00 	lea    0x1990(%rip),%rsi        # 4030c4 <_IO_stdin_used+0xc4>
  401734:	49 8d 9d 98 03 00 00 	lea    0x398(%r13),%rbx
  40173b:	e8 90 f9 ff ff       	call   4010d0 <__printf_chk@plt>
  }
  printf("freq: %ld\n", freq/ seconds);
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  401740:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  401745:	48 8d 35 86 19 00 00 	lea    0x1986(%rip),%rsi        # 4030d2 <_IO_stdin_used+0xd2>
  40174c:	bf 01 00 00 00       	mov    $0x1,%edi
  401751:	48 99                	cqto
  401753:	4d 8d bd 98 3f 00 00 	lea    0x3f98(%r13),%r15
  40175a:	4c 8d 35 b6 19 00 00 	lea    0x19b6(%rip),%r14        # 403117 <_IO_stdin_used+0x117>
  401761:	48 f7 fd             	idiv   %rbp
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  
  long goods = 0;
  401764:	31 ed                	xor    %ebp,%ebp
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  401766:	49 89 c4             	mov    %rax,%r12
  401769:	48 89 c2             	mov    %rax,%rdx
  40176c:	31 c0                	xor    %eax,%eax
  40176e:	e8 5d f9 ff ff       	call   4010d0 <__printf_chk@plt>
  401773:	4c 89 e2             	mov    %r12,%rdx
  401776:	bf 01 00 00 00       	mov    $0x1,%edi
  40177b:	31 c0                	xor    %eax,%eax
  40177d:	48 8d 35 62 19 00 00 	lea    0x1962(%rip),%rsi        # 4030e6 <_IO_stdin_used+0xe6>
  401784:	e8 47 f9 ff ff       	call   4010d0 <__printf_chk@plt>
  401789:	4c 89 e2             	mov    %r12,%rdx
  40178c:	bf 01 00 00 00       	mov    $0x1,%edi
  401791:	31 c0                	xor    %eax,%eax
  401793:	48 8d 35 6a 19 00 00 	lea    0x196a(%rip),%rsi        # 403104 <_IO_stdin_used+0x104>
  40179a:	e8 31 f9 ff ff       	call   4010d0 <__printf_chk@plt>

  for (int x = 0; x < threadsize; x++) {
  40179f:	90                   	nop
  4017a0:	48 8b 13             	mov    (%rbx),%rdx
  4017a3:	4c 89 f6             	mov    %r14,%rsi
  4017a6:	bf 01 00 00 00       	mov    $0x1,%edi
  4017ab:	31 c0                	xor    %eax,%eax
  4017ad:	48 81 c3 00 04 00 00 	add    $0x400,%rbx
  4017b4:	e8 17 f9 ff ff       	call   4010d0 <__printf_chk@plt>
    printf("%ld successreads\n", data[x].successreads);
    goods += data[x].successreads;
  4017b9:	48 03 ab 00 fc ff ff 	add    -0x400(%rbx),%rbp
  4017c0:	49 89 ec             	mov    %rbp,%r12
  for (int x = 0; x < threadsize; x++) {
  4017c3:	49 39 df             	cmp    %rbx,%r15
  4017c6:	75 d8                	jne    4017a0 <main+0x680>
  4017c8:	49 8d 5d 50          	lea    0x50(%r13),%rbx
  4017cc:	4d 8d bd 50 3c 00 00 	lea    0x3c50(%r13),%r15
  }
  
  long freq_writes = 0;
  4017d3:	31 ed                	xor    %ebp,%ebp
  4017d5:	4c 8d 35 4d 19 00 00 	lea    0x194d(%rip),%r14        # 403129 <_IO_stdin_used+0x129>
  4017dc:	0f 1f 40 00          	nopl   0x0(%rax)
  
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  4017e0:	48 8b 13             	mov    (%rbx),%rdx
  4017e3:	4c 89 f6             	mov    %r14,%rsi
  4017e6:	bf 01 00 00 00       	mov    $0x1,%edi
  4017eb:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  4017ed:	48 81 c3 00 04 00 00 	add    $0x400,%rbx
    freq_writes += data[x].freq_writes;
  4017f4:	48 01 d5             	add    %rdx,%rbp
  4017f7:	e8 d4 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  4017fc:	49 39 df             	cmp    %rbx,%r15
  4017ff:	75 df                	jne    4017e0 <main+0x6c0>
  401801:	48 89 ea             	mov    %rbp,%rdx
  401804:	bf 01 00 00 00       	mov    $0x1,%edi
  401809:	31 c0                	xor    %eax,%eax
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  40180b:	bb 00 ca 9a 3b       	mov    $0x3b9aca00,%ebx
  401810:	48 8d 35 1e 19 00 00 	lea    0x191e(%rip),%rsi        # 403135 <_IO_stdin_used+0x135>
  401817:	e8 b4 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  40181c:	48 89 ea             	mov    %rbp,%rdx
  40181f:	bf 01 00 00 00       	mov    $0x1,%edi
  401824:	31 c0                	xor    %eax,%eax
  401826:	48 8d 35 1a 19 00 00 	lea    0x191a(%rip),%rsi        # 403147 <_IO_stdin_used+0x147>
  40182d:	e8 9e f8 ff ff       	call   4010d0 <__printf_chk@plt>
  401832:	48 89 d8             	mov    %rbx,%rax
  401835:	bf 01 00 00 00       	mov    $0x1,%edi
  40183a:	48 8d 35 1e 19 00 00 	lea    0x191e(%rip),%rsi        # 40315f <_IO_stdin_used+0x15f>
  401841:	48 99                	cqto
  401843:	48 f7 fd             	idiv   %rbp
  401846:	48 8d 2d 94 18 00 00 	lea    0x1894(%rip),%rbp        # 4030e1 <_IO_stdin_used+0xe1>
  40184d:	49 89 c6             	mov    %rax,%r14
  401850:	48 89 c2             	mov    %rax,%rdx
  401853:	31 c0                	xor    %eax,%eax
  401855:	e8 76 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  40185a:	4c 89 f2             	mov    %r14,%rdx
  40185d:	bf 01 00 00 00       	mov    $0x1,%edi
  401862:	31 c0                	xor    %eax,%eax
  401864:	48 8d 35 bd 19 00 00 	lea    0x19bd(%rip),%rsi        # 403228 <_IO_stdin_used+0x228>
  40186b:	e8 60 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  401870:	4c 89 f2             	mov    %r14,%rdx
  401873:	bf 01 00 00 00       	mov    $0x1,%edi
  401878:	31 c0                	xor    %eax,%eax
  40187a:	48 8d 35 f9 18 00 00 	lea    0x18f9(%rip),%rsi        # 40317a <_IO_stdin_used+0x17a>
  401881:	e8 4a f8 ff ff       	call   4010d0 <__printf_chk@plt>
  401886:	48 8d 3d 07 19 00 00 	lea    0x1907(%rip),%rdi        # 403194 <_IO_stdin_used+0x194>
  40188d:	e8 be f7 ff ff       	call   401050 <puts@plt>
  401892:	48 89 ee             	mov    %rbp,%rsi
  401895:	bf 01 00 00 00       	mov    $0x1,%edi
  40189a:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  40189c:	49 8b 95 f0 00 00 00 	mov    0xf0(%r13),%rdx
  4018a3:	49 2b 95 e0 00 00 00 	sub    0xe0(%r13),%rdx
  4018aa:	e8 21 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  4018af:	48 89 ee             	mov    %rbp,%rsi
  4018b2:	bf 01 00 00 00       	mov    $0x1,%edi
  4018b7:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  4018b9:	49 8b 95 00 01 00 00 	mov    0x100(%r13),%rdx
  4018c0:	49 2b 95 e0 00 00 00 	sub    0xe0(%r13),%rdx
  4018c7:	e8 04 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  4018cc:	48 89 ee             	mov    %rbp,%rsi
  4018cf:	bf 01 00 00 00       	mov    $0x1,%edi
  4018d4:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  4018d6:	49 8b 95 f0 00 00 00 	mov    0xf0(%r13),%rdx
  4018dd:	49 2b 95 00 01 00 00 	sub    0x100(%r13),%rdx
  4018e4:	e8 e7 f7 ff ff       	call   4010d0 <__printf_chk@plt>
  4018e9:	48 89 ee             	mov    %rbp,%rsi
  4018ec:	bf 01 00 00 00       	mov    $0x1,%edi
  4018f1:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4018f3:	49 8b 95 20 01 00 00 	mov    0x120(%r13),%rdx
  4018fa:	49 2b 95 10 01 00 00 	sub    0x110(%r13),%rdx
  401901:	e8 ca f7 ff ff       	call   4010d0 <__printf_chk@plt>
  401906:	48 89 ee             	mov    %rbp,%rsi
  401909:	bf 01 00 00 00       	mov    $0x1,%edi
  40190e:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  401910:	49 8b 95 10 01 00 00 	mov    0x110(%r13),%rdx
  401917:	49 2b 95 20 01 00 00 	sub    0x120(%r13),%rdx
  40191e:	e8 ad f7 ff ff       	call   4010d0 <__printf_chk@plt>
  401923:	48 89 ee             	mov    %rbp,%rsi
  401926:	bf 01 00 00 00       	mov    $0x1,%edi
  40192b:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  40192d:	49 8b 95 10 01 00 00 	mov    0x110(%r13),%rdx
  401934:	49 2b 95 00 01 00 00 	sub    0x100(%r13),%rdx
  40193b:	e8 90 f7 ff ff       	call   4010d0 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  401940:	49 8b 95 40 01 00 00 	mov    0x140(%r13),%rdx
  401947:	bf 01 00 00 00       	mov    $0x1,%edi
  40194c:	49 2b 95 30 01 00 00 	sub    0x130(%r13),%rdx
  401953:	48 8d 35 47 18 00 00 	lea    0x1847(%rip),%rsi        # 4031a1 <_IO_stdin_used+0x1a1>
  40195a:	31 c0                	xor    %eax,%eax
  40195c:	e8 6f f7 ff ff       	call   4010d0 <__printf_chk@plt>
  401961:	4c 89 e2             	mov    %r12,%rdx
  401964:	bf 01 00 00 00       	mov    $0x1,%edi
  401969:	31 c0                	xor    %eax,%eax
  40196b:	48 8d 35 37 18 00 00 	lea    0x1837(%rip),%rsi        # 4031a9 <_IO_stdin_used+0x1a9>
  401972:	e8 59 f7 ff ff       	call   4010d0 <__printf_chk@plt>
  } 
  printf("%ld good reads per second\n", goods / seconds);
  printf("%ld good reads per second latency\n", 1000000000 / (goods / seconds));
  401977:	48 89 d8             	mov    %rbx,%rax
  40197a:	bf 01 00 00 00       	mov    $0x1,%edi
  40197f:	31 db                	xor    %ebx,%ebx
  401981:	48 99                	cqto
  401983:	48 8d 35 c6 18 00 00 	lea    0x18c6(%rip),%rsi        # 403250 <_IO_stdin_used+0x250>
  40198a:	49 f7 fc             	idiv   %r12
  40198d:	48 89 c2             	mov    %rax,%rdx
  401990:	31 c0                	xor    %eax,%eax
  401992:	e8 39 f7 ff ff       	call   4010d0 <__printf_chk@plt>
     }
   fclose(out_file);
   
 }

  char * filename = calloc(100, sizeof(char));
  401997:	be 01 00 00 00       	mov    $0x1,%esi
  40199c:	bf 64 00 00 00       	mov    $0x64,%edi
  4019a1:	e8 1a f7 ff ff       	call   4010c0 <calloc@plt>
  char * buf = calloc(1000, sizeof(char));
  4019a6:	be 01 00 00 00       	mov    $0x1,%esi
  4019ab:	bf e8 03 00 00       	mov    $0x3e8,%edi
  char * filename = calloc(100, sizeof(char));
  4019b0:	49 89 c4             	mov    %rax,%r12
  char * buf = calloc(1000, sizeof(char));
  4019b3:	e8 08 f7 ff ff       	call   4010c0 <calloc@plt>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  4019b8:	66 0f 6f 05 10 19 00 00 	movdqa 0x1910(%rip),%xmm0        # 4032d0 <_IO_stdin_used+0x2d0>
  memset(filename, 0, 100);
  snprintf(filename, 100, "coroutine.struct");
  FILE *out_file = fopen(filename, "w");
  4019c0:	4c 89 e7             	mov    %r12,%rdi
  4019c3:	41 c6 44 24 10 00    	movb   $0x0,0x10(%r12)
  4019c9:	48 8d 35 f4 17 00 00 	lea    0x17f4(%rip),%rsi        # 4031c4 <_IO_stdin_used+0x1c4>
  char * buf = calloc(1000, sizeof(char));
  4019d0:	48 89 c5             	mov    %rax,%rbp
  4019d3:	41 0f 11 04 24       	movups %xmm0,(%r12)
  FILE *out_file = fopen(filename, "w");
  4019d8:	e8 13 f7 ff ff       	call   4010f0 <fopen@plt>
  4019dd:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  4019e2:	48 89 ef             	mov    %rbp,%rdi
  4019e5:	45 31 c9             	xor    %r9d,%r9d
  4019e8:	49 89 c4             	mov    %rax,%r12
  4019eb:	48 89 d8             	mov    %rbx,%rax
  4019ee:	ba 01 00 00 00       	mov    $0x1,%edx
  4019f3:	be 64 00 00 00       	mov    $0x64,%esi
  4019f8:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  4019fb:	4c 8d 05 c4 17 00 00 	lea    0x17c4(%rip),%r8        # 4031c6 <_IO_stdin_used+0x1c6>
  401a02:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401a07:	48 89 ef             	mov    %rbp,%rdi
  401a0a:	e8 21 f6 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401a0f:	4c 89 e6             	mov    %r12,%rsi
  401a12:	48 89 ef             	mov    %rbp,%rdi
  401a15:	e8 86 f6 ff ff       	call   4010a0 <fputs@plt>
  401a1a:	48 89 d8             	mov    %rbx,%rax
  401a1d:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401a22:	48 89 ef             	mov    %rbp,%rdi
  401a25:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401a28:	41 b9 08 00 00 00    	mov    $0x8,%r9d
  401a2e:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401a33:	48 89 ef             	mov    %rbp,%rdi
  401a36:	4c 8d 05 94 17 00 00 	lea    0x1794(%rip),%r8        # 4031d1 <_IO_stdin_used+0x1d1>
  401a3d:	ba 01 00 00 00       	mov    $0x1,%edx
  401a42:	be 64 00 00 00       	mov    $0x64,%esi
  401a47:	e8 e4 f5 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401a4c:	4c 89 e6             	mov    %r12,%rsi
  401a4f:	48 89 ef             	mov    %rbp,%rdi
  401a52:	e8 49 f6 ff ff       	call   4010a0 <fputs@plt>
  401a57:	48 89 d8             	mov    %rbx,%rax
  401a5a:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401a5f:	48 89 ef             	mov    %rbp,%rdi
  401a62:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401a65:	41 b9 10 00 00 00    	mov    $0x10,%r9d
  401a6b:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401a70:	48 89 ef             	mov    %rbp,%rdi
  401a73:	4c 8d 05 60 17 00 00 	lea    0x1760(%rip),%r8        # 4031da <_IO_stdin_used+0x1da>
  401a7a:	ba 01 00 00 00       	mov    $0x1,%edx
  401a7f:	be 64 00 00 00       	mov    $0x64,%esi
  401a84:	e8 a7 f5 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401a89:	4c 89 e6             	mov    %r12,%rsi
  401a8c:	48 89 ef             	mov    %rbp,%rdi
  401a8f:	e8 0c f6 ff ff       	call   4010a0 <fputs@plt>
  401a94:	48 89 d8             	mov    %rbx,%rax
  401a97:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401a9c:	48 89 ef             	mov    %rbp,%rdi
  401a9f:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401aa2:	41 b9 18 00 00 00    	mov    $0x18,%r9d
  401aa8:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401aad:	48 89 ef             	mov    %rbp,%rdi
  401ab0:	4c 8d 05 2c 17 00 00 	lea    0x172c(%rip),%r8        # 4031e3 <_IO_stdin_used+0x1e3>
  401ab7:	ba 01 00 00 00       	mov    $0x1,%edx
  401abc:	be 64 00 00 00       	mov    $0x64,%esi
  401ac1:	e8 6a f5 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401ac6:	4c 89 e6             	mov    %r12,%rsi
  401ac9:	48 89 ef             	mov    %rbp,%rdi
  401acc:	e8 cf f5 ff ff       	call   4010a0 <fputs@plt>
  401ad1:	48 89 d8             	mov    %rbx,%rax
  401ad4:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401ad9:	48 89 ef             	mov    %rbp,%rdi
  401adc:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401adf:	45 31 c9             	xor    %r9d,%r9d
  401ae2:	4c 8d 05 04 17 00 00 	lea    0x1704(%rip),%r8        # 4031ed <_IO_stdin_used+0x1ed>
  401ae9:	48 89 ef             	mov    %rbp,%rdi
  401aec:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401af1:	ba 01 00 00 00       	mov    $0x1,%edx
  401af6:	be 64 00 00 00       	mov    $0x64,%esi
  401afb:	e8 30 f5 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401b00:	48 89 ef             	mov    %rbp,%rdi
  401b03:	4c 89 e6             	mov    %r12,%rsi
  401b06:	e8 95 f5 ff ff       	call   4010a0 <fputs@plt>
  memset(buf, 0, 1000);
  snprintf(buf, 100, "corourinedata.running %ld\n", offsetof(struct CoroutineData, running));
  fprintf(out_file, "%s", buf);
  
  
  fclose(out_file);
  401b0b:	4c 89 e7             	mov    %r12,%rdi
  401b0e:	e8 5d f5 ff ff       	call   401070 <fclose@plt>
  401b13:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
  401b1b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401b24:	75 14                	jne    401b3a <main+0xa1a>
  401b26:	48 81 c4 a8 00 00 00 	add    $0xa8,%rsp
  401b2d:	31 c0                	xor    %eax,%eax
  401b2f:	5b                   	pop    %rbx
  401b30:	5d                   	pop    %rbp
  401b31:	41 5c                	pop    %r12
  401b33:	41 5d                	pop    %r13
  401b35:	41 5e                	pop    %r14
  401b37:	41 5f                	pop    %r15
  401b39:	c3                   	ret
  401b3a:	e8 41 f5 ff ff       	call   401080 <__stack_chk_fail@plt>
  401b3f:	90                   	nop

0000000000401b40 <set_fast_math>:
  401b40:	f3 0f 1e fa          	endbr64
  401b44:	0f ae 5c 24 fc       	stmxcsr -0x4(%rsp)
  401b49:	81 4c 24 fc 40 80 00 00 	orl    $0x8040,-0x4(%rsp)
  401b51:	0f ae 54 24 fc       	ldmxcsr -0x4(%rsp)
  401b56:	c3                   	ret
  401b57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000401b60 <_start>:
  401b60:	f3 0f 1e fa          	endbr64
  401b64:	31 ed                	xor    %ebp,%ebp
  401b66:	49 89 d1             	mov    %rdx,%r9
  401b69:	5e                   	pop    %rsi
  401b6a:	48 89 e2             	mov    %rsp,%rdx
  401b6d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401b71:	50                   	push   %rax
  401b72:	54                   	push   %rsp
  401b73:	45 31 c0             	xor    %r8d,%r8d
  401b76:	31 c9                	xor    %ecx,%ecx
  401b78:	48 c7 c7 20 11 40 00 	mov    $0x401120,%rdi
  401b7f:	ff 15 6b 34 00 00    	call   *0x346b(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  401b85:	f4                   	hlt
  401b86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401b90 <_dl_relocate_static_pie>:
  401b90:	f3 0f 1e fa          	endbr64
  401b94:	c3                   	ret
  401b95:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401b9f:	90                   	nop

0000000000401ba0 <deregister_tm_clones>:
  401ba0:	b8 10 50 40 00       	mov    $0x405010,%eax
  401ba5:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  401bab:	74 13                	je     401bc0 <deregister_tm_clones+0x20>
  401bad:	b8 00 00 00 00       	mov    $0x0,%eax
  401bb2:	48 85 c0             	test   %rax,%rax
  401bb5:	74 09                	je     401bc0 <deregister_tm_clones+0x20>
  401bb7:	bf 10 50 40 00       	mov    $0x405010,%edi
  401bbc:	ff e0                	jmp    *%rax
  401bbe:	66 90                	xchg   %ax,%ax
  401bc0:	c3                   	ret
  401bc1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401bcc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401bd0 <register_tm_clones>:
  401bd0:	be 10 50 40 00       	mov    $0x405010,%esi
  401bd5:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  401bdc:	48 89 f0             	mov    %rsi,%rax
  401bdf:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401be3:	48 c1 f8 03          	sar    $0x3,%rax
  401be7:	48 01 c6             	add    %rax,%rsi
  401bea:	48 d1 fe             	sar    %rsi
  401bed:	74 11                	je     401c00 <register_tm_clones+0x30>
  401bef:	b8 00 00 00 00       	mov    $0x0,%eax
  401bf4:	48 85 c0             	test   %rax,%rax
  401bf7:	74 07                	je     401c00 <register_tm_clones+0x30>
  401bf9:	bf 10 50 40 00       	mov    $0x405010,%edi
  401bfe:	ff e0                	jmp    *%rax
  401c00:	c3                   	ret
  401c01:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401c0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401c10 <__do_global_dtors_aux>:
  401c10:	f3 0f 1e fa          	endbr64
  401c14:	80 3d f5 33 00 00 00 	cmpb   $0x0,0x33f5(%rip)        # 405010 <__TMC_END__>
  401c1b:	75 13                	jne    401c30 <__do_global_dtors_aux+0x20>
  401c1d:	55                   	push   %rbp
  401c1e:	48 89 e5             	mov    %rsp,%rbp
  401c21:	e8 7a ff ff ff       	call   401ba0 <deregister_tm_clones>
  401c26:	c6 05 e3 33 00 00 01 	movb   $0x1,0x33e3(%rip)        # 405010 <__TMC_END__>
  401c2d:	5d                   	pop    %rbp
  401c2e:	c3                   	ret
  401c2f:	90                   	nop
  401c30:	c3                   	ret
  401c31:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401c3c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401c40 <frame_dummy>:
  401c40:	f3 0f 1e fa          	endbr64
  401c44:	eb 8a                	jmp    401bd0 <register_tm_clones>
  401c46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401c50 <coroutine_func>:
  while (data->running == 1) {
  401c50:	83 3a 01             	cmpl   $0x1,(%rdx)
  401c53:	75 5b                	jne    401cb0 <coroutine_func+0x60>
int coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data) {
  401c55:	41 55                	push   %r13
  401c57:	4c 8d 2d 83 14 00 00 	lea    0x1483(%rip),%r13        # 4030e1 <_IO_stdin_used+0xe1>
  401c5e:	41 54                	push   %r12
  401c60:	49 89 f4             	mov    %rsi,%r12
  401c63:	55                   	push   %rbp
  401c64:	48 89 d5             	mov    %rdx,%rbp
  401c67:	53                   	push   %rbx
   asm("lea 0(%%rip), %%r11\n"
  401c68:	4c 8d 1d 00 00 00 00 	lea    0x0(%rip),%r11        # 401c6f <coroutine_func+0x1f>
  401c6f:	4c 89 db             	mov    %r11,%rbx
int coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data) {
  401c72:	48 83 ec 08          	sub    $0x8,%rsp
  401c76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
   asm("lea 0(%%rip), %%r11\n"
  401c80:	49 89 5c 24 10       	mov    %rbx,0x10(%r12)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  401c85:	31 c0                	xor    %eax,%eax
  401c87:	48 89 da             	mov    %rbx,%rdx
  401c8a:	4c 89 ee             	mov    %r13,%rsi
  401c8d:	bf 01 00 00 00       	mov    $0x1,%edi
  401c92:	e8 39 f4 ff ff       	call   4010d0 <__printf_chk@plt>
  while (data->running == 1) {
  401c97:	83 7d 00 01          	cmpl   $0x1,0x0(%rbp)
  401c9b:	74 e3                	je     401c80 <coroutine_func+0x30>
}
  401c9d:	48 83 c4 08          	add    $0x8,%rsp
  401ca1:	31 c0                	xor    %eax,%eax
  401ca3:	5b                   	pop    %rbx
  401ca4:	5d                   	pop    %rbp
  401ca5:	41 5c                	pop    %r12
  401ca7:	41 5d                	pop    %r13
  401ca9:	c3                   	ret
  401caa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  401cb0:	31 c0                	xor    %eax,%eax
  401cb2:	c3                   	ret
  401cb3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401cbe:	66 90                	xchg   %ax,%ax

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
  401e7e:	48 8b 05 f3 13 00 00 	mov    0x13f3(%rip),%rax        # 403278 <_IO_stdin_used+0x278>
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
  switch_to(data->coroutines, 0, data->scheduler);
  402072:	31 f6                	xor    %esi,%esi
int * threadwork(struct Data * data) {
  402074:	41 55                	push   %r13
  402076:	41 54                	push   %r12
  402078:	55                   	push   %rbp
  402079:	53                   	push   %rbx
  40207a:	48 89 fb             	mov    %rdi,%rbx
  40207d:	48 83 ec 20          	sub    $0x20,%rsp
  data->scheduler->rsp = rsp;
  402081:	48 8b 97 c8 03 00 00 	mov    0x3c8(%rdi),%rdx
  switch_to(data->coroutines, 0, data->scheduler);
  402088:	48 8b bf c0 03 00 00 	mov    0x3c0(%rdi),%rdi
int * threadwork(struct Data * data) {
  40208f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  402098:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  40209d:	31 c0                	xor    %eax,%eax
    asm( "mov %%rsp, %0" : "=rm" ( rsp ));
  40209f:	48 89 e0             	mov    %rsp,%rax
  data->scheduler->rsp = rsp;
  4020a2:	48 89 02             	mov    %rax,(%rdx)
  switch_to(data->coroutines, 0, data->scheduler);
  4020a5:	e8 ec 03 00 00       	call   402496 <switch_to>
clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  4020aa:	48 89 e6             	mov    %rsp,%rsi
  4020ad:	bf 04 00 00 00       	mov    $0x4,%edi
  4020b2:	e8 a9 ef ff ff       	call   401060 <clock_gettime@plt>
  if (data->running == 2) {
  4020b7:	83 7b 5c 02          	cmpl   $0x2,0x5c(%rbx)
  4020bb:	0f 84 e7 01 00 00    	je     4022a8 <threadwork+0x238>
  long thisgroup = data->main->globalwrite[data->mystream * 128] / epochsize;
  4020c1:	8b ab 8c 03 00 00    	mov    0x38c(%rbx),%ebp
  4020c7:	4c 8b 63 28          	mov    0x28(%rbx),%r12
  if (thisgroup != data->lastgroup) {
  4020cb:	48 63 8b 88 03 00 00 	movslq 0x388(%rbx),%rcx
  long thisgroup = data->main->globalwrite[data->mystream * 128] / epochsize;
  4020d2:	89 e8                	mov    %ebp,%eax
  4020d4:	49 8b 94 24 80 03 00 00 	mov    0x380(%r12),%rdx
  4020dc:	c1 e0 07             	shl    $0x7,%eax
  4020df:	48 98                	cltq
  4020e1:	48 8b 04 c2          	mov    (%rdx,%rax,8),%rax
  if (thisgroup != data->lastgroup) {
  4020e5:	48 39 c8             	cmp    %rcx,%rax
  4020e8:	74 0a                	je     4020f4 <threadwork+0x84>
      data->writecursor = 0;
  4020ea:	c7 83 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rbx)
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  4020f4:	8b b3 90 03 00 00    	mov    0x390(%rbx),%esi
   data->lastgroup = thisgroup;
  4020fa:	89 83 88 03 00 00    	mov    %eax,0x388(%rbx)
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
  402100:	4c 8b 8b 48 03 00 00 	mov    0x348(%rbx),%r9
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  402107:	89 f0                	mov    %esi,%eax
  402109:	c1 e0 07             	shl    $0x7,%eax
  40210c:	48 98                	cltq
  40210e:	48 8b 0c c2          	mov    (%rdx,%rax,8),%rcx
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
  402112:	48 63 d6             	movslq %esi,%rdx
  402115:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
  402119:	41 8b 04 81          	mov    (%r9,%rax,4),%eax
  40211d:	48 85 c9             	test   %rcx,%rcx
  402120:	74 0c                	je     40212e <threadwork+0xbe>
  402122:	48 63 f8             	movslq %eax,%rdi
  402125:	48 39 cf             	cmp    %rcx,%rdi
  402128:	0f 8d 52 01 00 00    	jge    402280 <threadwork+0x210>
    for (int x = 0; x < data->threadsize - 1; x++) {
  40212e:	44 8b 53 68          	mov    0x68(%rbx),%r10d
  402132:	41 83 ea 01          	sub    $0x1,%r10d
  402136:	45 85 d2             	test   %r10d,%r10d
  402139:	0f 8e 41 01 00 00    	jle    402280 <threadwork+0x210>
  40213f:	45 31 db             	xor    %r11d,%r11d
  402142:	eb 20                	jmp    402164 <threadwork+0xf4>
  402144:	0f 1f 40 00          	nopl   0x0(%rax)
  402148:	41 83 c3 01          	add    $0x1,%r11d
  40214c:	45 39 d3             	cmp    %r10d,%r11d
  40214f:	0f 8d 2b 01 00 00    	jge    402280 <threadwork+0x210>
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  402155:	48 63 d6             	movslq %esi,%rdx
        if (data->main->works[buffer] != -1) {
  402158:	4c 8b 63 28          	mov    0x28(%rbx),%r12
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  40215c:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
  402160:	41 8b 04 81          	mov    (%r9,%rax,4),%eax
  402164:	83 e8 01             	sub    $0x1,%eax
  402167:	4c 8d 04 52          	lea    (%rdx,%rdx,2),%r8
   data->freq++;
  40216b:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  402170:	48 63 d0             	movslq %eax,%rdx
  402173:	41 89 c5             	mov    %eax,%r13d
  402176:	49 c1 e0 02          	shl    $0x2,%r8
  40217a:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  402181:	41 c1 fd 1f          	sar    $0x1f,%r13d
  402185:	4b 8d 3c 01          	lea    (%r9,%r8,1),%rdi
    int cursor = data->globalread[data->laststream].cursor;
  402189:	8b 4f 04             	mov    0x4(%rdi),%ecx
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  40218c:	48 c1 ea 20          	shr    $0x20,%rdx
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  402190:	41 89 ce             	mov    %ecx,%r14d
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  402193:	01 c2                	add    %eax,%edx
  402195:	c1 fa 07             	sar    $0x7,%edx
  402198:	44 29 ea             	sub    %r13d,%edx
  40219b:	41 89 d5             	mov    %edx,%r13d
  40219e:	41 c1 e5 08          	shl    $0x8,%r13d
  4021a2:	41 29 d5             	sub    %edx,%r13d
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  4021a5:	31 d2                	xor    %edx,%edx
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  4021a7:	44 29 e8             	sub    %r13d,%eax
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  4021aa:	41 89 f5             	mov    %esi,%r13d
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  4021ad:	48 98                	cltq
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  4021af:	48 85 c0             	test   %rax,%rax
  4021b2:	48 0f 48 c2          	cmovs  %rdx,%rax
  4021b6:	48 63 d1             	movslq %ecx,%rdx
  4021b9:	41 c1 fe 1f          	sar    $0x1f,%r14d
  4021bd:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  4021c4:	41 c1 e5 18          	shl    $0x18,%r13d
  4021c8:	48 c1 e0 10          	shl    $0x10,%rax
  4021cc:	48 c1 ea 20          	shr    $0x20,%rdx
  4021d0:	01 ca                	add    %ecx,%edx
  4021d2:	c1 fa 07             	sar    $0x7,%edx
  4021d5:	44 29 f2             	sub    %r14d,%edx
  4021d8:	41 89 d6             	mov    %edx,%r14d
  4021db:	41 c1 e6 08          	shl    $0x8,%r14d
  4021df:	41 29 d6             	sub    %edx,%r14d
  4021e2:	89 ca                	mov    %ecx,%edx
  4021e4:	44 29 f2             	sub    %r14d,%edx
  4021e7:	41 09 d5             	or     %edx,%r13d
  4021ea:	4d 63 ed             	movslq %r13d,%r13
  4021ed:	4c 09 e8             	or     %r13,%rax
        if (data->main->works[buffer] != -1) {
  4021f0:	49 03 44 24 70       	add    0x70(%r12),%rax
  4021f5:	80 38 ff             	cmpb   $0xff,(%rax)
  4021f8:	74 2d                	je     402227 <threadwork+0x1b7>
          data->successreads++;
  4021fa:	48 83 83 98 03 00 00 01 	addq   $0x1,0x398(%rbx)
          data->main->works[buffer] = -1;
  402202:	c6 00 ff             	movb   $0xff,(%rax)
    if (data->globalread[thistream].cursor < cursorlimit) {
  402205:	4c 8b 8b 48 03 00 00 	mov    0x348(%rbx),%r9
    for (int x = 0; x < data->threadsize - 1; x++) {
  40220c:	44 8b 53 68          	mov    0x68(%rbx),%r10d
      data->laststream = (data->laststream + 1);
  402210:	8b b3 90 03 00 00    	mov    0x390(%rbx),%esi
    if (data->globalread[thistream].cursor < cursorlimit) {
  402216:	4b 8d 3c 01          	lea    (%r9,%r8,1),%rdi
    if (data->laststream == data->mystream) {
  40221a:	8b ab 8c 03 00 00    	mov    0x38c(%rbx),%ebp
    if (data->globalread[thistream].cursor < cursorlimit) {
  402220:	8b 4f 04             	mov    0x4(%rdi),%ecx
  402223:	41 83 ea 01          	sub    $0x1,%r10d
  402227:	83 f9 04             	cmp    $0x4,%ecx
  40222a:	7f 09                	jg     402235 <threadwork+0x1c5>
      data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1);
  40222c:	83 c1 01             	add    $0x1,%ecx
      data->globalread[thistream].global++;
  40222f:	83 07 01             	addl   $0x1,(%rdi)
      data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1);
  402232:	89 4f 04             	mov    %ecx,0x4(%rdi)
    if (data->globalread[thistream].cursor == cursorlimit) {
  402235:	83 f9 05             	cmp    $0x5,%ecx
  402238:	75 10                	jne    40224a <threadwork+0x1da>
      data->laststream = (data->laststream + 1);
  40223a:	83 c6 01             	add    $0x1,%esi
  40223d:	89 b3 90 03 00 00    	mov    %esi,0x390(%rbx)
data->globalread[thistream].cursor = 0;
  402243:	c7 47 04 00 00 00 00 	movl   $0x0,0x4(%rdi)
    if (data->laststream == data->mystream) {
  40224a:	39 f5                	cmp    %esi,%ebp
  40224c:	75 09                	jne    402257 <threadwork+0x1e7>
      data->laststream = data->laststream + 1;
  40224e:	8d 75 01             	lea    0x1(%rbp),%esi
  402251:	89 b3 90 03 00 00    	mov    %esi,0x390(%rbx)
    if (data->laststream == 5) {
  402257:	83 fe 05             	cmp    $0x5,%esi
  40225a:	0f 85 e8 fe ff ff    	jne    402148 <threadwork+0xd8>
       data->laststream = 1;
  402260:	c7 83 90 03 00 00 01 00 00 00 	movl   $0x1,0x390(%rbx)
    for (int x = 0; x < data->threadsize - 1; x++) {
  40226a:	41 83 c3 01          	add    $0x1,%r11d
  40226e:	45 39 d3             	cmp    %r10d,%r11d
  402271:	7d 0d                	jge    402280 <threadwork+0x210>
  402273:	be 01 00 00 00       	mov    $0x1,%esi
  402278:	e9 d8 fe ff ff       	jmp    402155 <threadwork+0xe5>
  40227d:	0f 1f 00             	nopl   (%rax)
}
  402280:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  402285:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40228e:	0f 85 54 01 00 00    	jne    4023e8 <threadwork+0x378>
  402294:	48 83 c4 20          	add    $0x20,%rsp
  402298:	31 c0                	xor    %eax,%eax
  40229a:	5b                   	pop    %rbx
  40229b:	5d                   	pop    %rbp
  40229c:	41 5c                	pop    %r12
  40229e:	41 5d                	pop    %r13
  4022a0:	41 5e                	pop    %r14
  4022a2:	c3                   	ret
  4022a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
   for (int x = 0 ; x < data->threadsize ; x++) {
  4022a8:	8b 43 68             	mov    0x68(%rbx),%eax
  4022ab:	85 c0                	test   %eax,%eax
  4022ad:	0f 8e d2 00 00 00    	jle    402385 <threadwork+0x315>
    int cursor = data->writecursor;
  4022b3:	8b 8b 80 01 00 00    	mov    0x180(%rbx),%ecx
   for (int x = 0 ; x < data->threadsize ; x++) {
  4022b9:	31 f6                	xor    %esi,%esi
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  4022bb:	49 b8 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%r8
  4022c5:	0f 1f 00             	nopl   (%rax)
  4022c8:	44 8b 93 8c 03 00 00 	mov    0x38c(%rbx),%r10d
  4022cf:	4c 8b 4b 28          	mov    0x28(%rbx),%r9
    if (data->threadindex == 1) {
  4022d3:	8b 7b 64             	mov    0x64(%rbx),%edi
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  4022d6:	44 89 d0             	mov    %r10d,%eax
  4022d9:	49 8b 91 80 03 00 00 	mov    0x380(%r9),%rdx
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  4022e0:	41 c1 e2 18          	shl    $0x18,%r10d
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  4022e4:	c1 e0 07             	shl    $0x7,%eax
  4022e7:	48 98                	cltq
  4022e9:	4c 8b 1c c2          	mov    (%rdx,%rax,8),%r11
  4022ed:	4c 89 d8             	mov    %r11,%rax
  4022f0:	49 f7 e8             	imul   %r8
  4022f3:	4c 89 d8             	mov    %r11,%rax
  4022f6:	48 c1 f8 3f          	sar    $0x3f,%rax
  4022fa:	4c 01 da             	add    %r11,%rdx
  4022fd:	48 c1 fa 07          	sar    $0x7,%rdx
  402301:	48 29 c2             	sub    %rax,%rdx
  402304:	48 89 d0             	mov    %rdx,%rax
  402307:	48 c1 e0 08          	shl    $0x8,%rax
  40230b:	48 29 d0             	sub    %rdx,%rax
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  40230e:	48 63 d1             	movslq %ecx,%rdx
  402311:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  402318:	49 29 c3             	sub    %rax,%r11
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  40231b:	89 c8                	mov    %ecx,%eax
  40231d:	c1 f8 1f             	sar    $0x1f,%eax
  402320:	41 c1 e3 10          	shl    $0x10,%r11d
  402324:	48 c1 ea 20          	shr    $0x20,%rdx
  402328:	01 ca                	add    %ecx,%edx
  40232a:	c1 fa 07             	sar    $0x7,%edx
  40232d:	29 c2                	sub    %eax,%edx
  40232f:	89 d0                	mov    %edx,%eax
  402331:	c1 e0 08             	shl    $0x8,%eax
  402334:	29 d0                	sub    %edx,%eax
  402336:	29 c1                	sub    %eax,%ecx
  402338:	44 09 d1             	or     %r10d,%ecx
  40233b:	44 09 d9             	or     %r11d,%ecx
  if (data->main->works[buffer] != -1) {
  40233e:	48 63 c9             	movslq %ecx,%rcx
  402341:	49 03 49 70          	add    0x70(%r9),%rcx
  402345:	80 39 ff             	cmpb   $0xff,(%rcx)
  402348:	74 66                	je     4023b0 <threadwork+0x340>
    data->freq_writes++;
  40234a:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
   for (int x = 0 ; x < data->threadsize ; x++) {
  40234f:	83 c6 01             	add    $0x1,%esi
  data->main->works[buffer] = data->threadindex;
  402352:	40 88 39             	mov    %dil,(%rcx)
    data->writecursor = (data->writecursor + 1) % cursorlimit;
  402355:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
  40235b:	83 c0 01             	add    $0x1,%eax
  40235e:	48 63 c8             	movslq %eax,%rcx
  402361:	99                   	cltd
  402362:	48 69 c9 67 66 66 66 	imul   $0x66666667,%rcx,%rcx
  402369:	48 c1 f9 21          	sar    $0x21,%rcx
  40236d:	29 d1                	sub    %edx,%ecx
  40236f:	8d 14 89             	lea    (%rcx,%rcx,4),%edx
  402372:	29 d0                	sub    %edx,%eax
  402374:	89 83 80 01 00 00    	mov    %eax,0x180(%rbx)
  40237a:	89 c1                	mov    %eax,%ecx
   for (int x = 0 ; x < data->threadsize ; x++) {
  40237c:	3b 73 68             	cmp    0x68(%rbx),%esi
  40237f:	0f 8c 43 ff ff ff    	jl     4022c8 <threadwork+0x258>
    __atomic_fetch_add(&data->main->globalwrite[data->mystream * 128], 1, __ATOMIC_RELAXED);
  402385:	48 8b 53 28          	mov    0x28(%rbx),%rdx
  402389:	8b 83 8c 03 00 00    	mov    0x38c(%rbx),%eax
  40238f:	48 8b 92 80 03 00 00 	mov    0x380(%rdx),%rdx
  402396:	c1 e0 07             	shl    $0x7,%eax
  402399:	48 98                	cltq
  40239b:	f0 48 83 04 c2 01    	lock addq $0x1,(%rdx,%rax,8)
  4023a1:	e9 1b fd ff ff       	jmp    4020c1 <threadwork+0x51>
  4023a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
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
  4023e0:	0f 8f e2 fe ff ff    	jg     4022c8 <threadwork+0x258>
  4023e6:	eb 9d                	jmp    402385 <threadwork+0x315>
}
  4023e8:	e8 93 ec ff ff       	call   401080 <__stack_chk_fail@plt>
  4023ed:	0f 1f 00             	nopl   (%rax)

00000000004023f0 <work>:
void * work(void * arg) {
  4023f0:	53                   	push   %rbx
  4023f1:	8b 57 64             	mov    0x64(%rdi),%edx
  4023f4:	48 89 fb             	mov    %rdi,%rbx
  4023f7:	48 8d 35 06 0c 00 00 	lea    0xc06(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
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
  40242a:	48 8d 35 e6 0b 00 00 	lea    0xbe6(%rip),%rsi        # 403017 <_IO_stdin_used+0x17>
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
  402465:	72 6f                	jb     4024d6 <switch_to+0x40>
  402467:	75 74                	jne    4024dd <switch_to+0x47>
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
  40248c:	74 61                	je     4024ef <switch_to+0x59>
  40248e:	2e                   	cs
  40248f:	2e                   	cs
  402490:	2e                   	cs
  402491:	20                   	.byte 0x20
  402492:	25                   	.byte 0x25
  402493:	78 0a                	js     40249f <switch_to+0x9>
	...

0000000000402496 <switch_to>:
	.text
	# switch_to(struct Coroutine * coroutines, int index, struct Scheduler * scheduler)
	# rdi, %rsi, %rdx, %rcx, %r8 and %r9
switch_to:
# popq %r11
pushq %rbp
  402496:	55                   	push   %rbp

movq %rsp, %rbp
  402497:	48 89 e5             	mov    %rsp,%rbp
subq $1024, %rsp
  40249a:	48 81 ec 00 04 00 00 	sub    $0x400,%rsp



movq %rdi, (%rbp) # coroutine table
  4024a1:	48 89 7d 00          	mov    %rdi,0x0(%rbp)
movq %rsi, -8(%rbp) # index
  4024a5:	48 89 75 f8          	mov    %rsi,-0x8(%rbp)
movq %rdx, -16(%rbp) # scheduler
  4024a9:	48 89 55 f0          	mov    %rdx,-0x10(%rbp)

movq %rdi, %rax
  4024ad:	48 89 f8             	mov    %rdi,%rax
movq %rax, %r9
  4024b0:	49 89 c1             	mov    %rax,%r9
movq %r9, -24(%rbp) # coroutine object
  4024b3:	4c 89 4d e8          	mov    %r9,-0x18(%rbp)

leaq 16(%rdi), %rax
  4024b7:	48 8d 47 10          	lea    0x10(%rdi),%rax
movq (%rax), %r9
  4024bb:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -32(%rbp) # coroutine function
  4024be:	4c 89 4d e0          	mov    %r9,-0x20(%rbp)

leaq 24(%rdi), %rax # load from coroutine object data object
  4024c2:	48 8d 47 18          	lea    0x18(%rdi),%rax
movq (%rax), %r9
  4024c6:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -40(%rbp) # coroutine data object
  4024c9:	4c 89 4d d8          	mov    %r9,-0x28(%rbp)

movq -24(%rbp), %r11
  4024cd:	4c 8b 5d e8          	mov    -0x18(%rbp),%r11
#

#pushq %r11
leaq .MSG(%rip), %rdi
  4024d1:	48 8d 3d 88 ff ff ff 	lea    -0x78(%rip),%rdi        # 402460 <.MSG>
movq %r11, %rsi
  4024d8:	4c 89 de             	mov    %r11,%rsi
#call printf@plt
mov $0, %eax
  4024db:	b8 00 00 00 00       	mov    $0x0,%eax

#popq %r11

#pushq %r9
movq -32(%rbp), %r9
  4024e0:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9

leaq .EIP(%rip), %rdi
  4024e4:	48 8d 3d 8c ff ff ff 	lea    -0x74(%rip),%rdi        # 402477 <.EIP>
movq %r9, %rsi
  4024eb:	4c 89 ce             	mov    %r9,%rsi
#call printf@plt
mov $0, %eax
  4024ee:	b8 00 00 00 00       	mov    $0x0,%eax
#popq %r9
# coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data

#pushq %r9
leaq .CODATA(%rip), %rdi
  4024f3:	48 8d 3d 8b ff ff ff 	lea    -0x75(%rip),%rdi        # 402485 <.CODATA>
movq -40(%rbp), %rsi
  4024fa:	48 8b 75 d8          	mov    -0x28(%rbp),%rsi
#call printf@plt
mov $0, %eax
  4024fe:	b8 00 00 00 00       	mov    $0x0,%eax
#popq %r9

movq -16(%rbp), %rdi
  402503:	48 8b 7d f0          	mov    -0x10(%rbp),%rdi
movq -24(%rbp), %rsi
  402507:	48 8b 75 e8          	mov    -0x18(%rbp),%rsi
movq -40(%rbp), %rdx
  40250b:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx



movq -32(%rbp), %r9
  40250f:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9
leaq after(%rip), %r11
  402513:	4c 8d 1d 10 00 00 00 	lea    0x10(%rip),%r11        # 40252a <after>

#movq %rbp, %rsp
# popq %rbp
add $1024, %rsp
  40251a:	48 81 c4 00 04 00 00 	add    $0x400,%rsp
# add $8, %rsp
popq %r11
  402521:	41 5b                	pop    %r11
popq %r11
  402523:	41 5b                	pop    %r11
pushq %r11
  402525:	41 53                	push   %r11
jmp *%r9
  402527:	41 ff e1             	jmp    *%r9

000000000040252a <after>:
after:
  40252a:	c3                   	ret

Disassembly of section .fini:

000000000040252c <_fini>:
  40252c:	f3 0f 1e fa          	endbr64
  402530:	48 83 ec 08          	sub    $0x8,%rsp
  402534:	48 83 c4 08          	add    $0x8,%rsp
  402538:	c3                   	ret
