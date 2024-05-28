
stream2-workqueue:     file format elf64-x86-64


Disassembly of section .init:

0000000000401000 <_init>:
  401000:	f3 0f 1e fa          	endbr64
  401004:	48 83 ec 08          	sub    $0x8,%rsp
  401008:	48 8b 05 e1 3f 00 00 	mov    0x3fe1(%rip),%rax        # 404ff0 <__gmon_start__@Base>
  40100f:	48 85 c0             	test   %rax,%rax
  401012:	74 02                	je     401016 <_init+0x16>
  401014:	ff d0                	call   *%rax
  401016:	48 83 c4 08          	add    $0x8,%rsp
  40101a:	c3                   	ret

Disassembly of section .plt:

0000000000401020 <__snprintf_chk@plt-0x10>:
  401020:	ff 35 32 3f 00 00    	push   0x3f32(%rip)        # 404f58 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 34 3f 00 00    	jmp    *0x3f34(%rip)        # 404f60 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <__snprintf_chk@plt>:
  401030:	ff 25 32 3f 00 00    	jmp    *0x3f32(%rip)        # 404f68 <__snprintf_chk@GLIBC_2.3.4>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <pthread_setaffinity_np@plt>:
  401040:	ff 25 2a 3f 00 00    	jmp    *0x3f2a(%rip)        # 404f70 <pthread_setaffinity_np@GLIBC_2.34>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <puts@plt>:
  401050:	ff 25 22 3f 00 00    	jmp    *0x3f22(%rip)        # 404f78 <puts@GLIBC_2.2.5>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <clock_gettime@plt>:
  401060:	ff 25 1a 3f 00 00    	jmp    *0x3f1a(%rip)        # 404f80 <clock_gettime@GLIBC_2.17>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <fclose@plt>:
  401070:	ff 25 12 3f 00 00    	jmp    *0x3f12(%rip)        # 404f88 <fclose@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <__stack_chk_fail@plt>:
  401080:	ff 25 0a 3f 00 00    	jmp    *0x3f0a(%rip)        # 404f90 <__stack_chk_fail@GLIBC_2.4>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <printf@plt>:
  401090:	ff 25 02 3f 00 00    	jmp    *0x3f02(%rip)        # 404f98 <printf@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <nanosleep@plt>:
  4010a0:	ff 25 fa 3e 00 00    	jmp    *0x3efa(%rip)        # 404fa0 <nanosleep@GLIBC_2.2.5>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <fputs@plt>:
  4010b0:	ff 25 f2 3e 00 00    	jmp    *0x3ef2(%rip)        # 404fa8 <fputs@GLIBC_2.2.5>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <memset@plt>:
  4010c0:	ff 25 ea 3e 00 00    	jmp    *0x3eea(%rip)        # 404fb0 <memset@GLIBC_2.2.5>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010d0 <calloc@plt>:
  4010d0:	ff 25 e2 3e 00 00    	jmp    *0x3ee2(%rip)        # 404fb8 <calloc@GLIBC_2.2.5>
  4010d6:	68 0a 00 00 00       	push   $0xa
  4010db:	e9 40 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010e0 <__printf_chk@plt>:
  4010e0:	ff 25 da 3e 00 00    	jmp    *0x3eda(%rip)        # 404fc0 <__printf_chk@GLIBC_2.3.4>
  4010e6:	68 0b 00 00 00       	push   $0xb
  4010eb:	e9 30 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010f0 <pthread_create@plt>:
  4010f0:	ff 25 d2 3e 00 00    	jmp    *0x3ed2(%rip)        # 404fc8 <pthread_create@GLIBC_2.34>
  4010f6:	68 0c 00 00 00       	push   $0xc
  4010fb:	e9 20 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401100 <fopen@plt>:
  401100:	ff 25 ca 3e 00 00    	jmp    *0x3eca(%rip)        # 404fd0 <fopen@GLIBC_2.2.5>
  401106:	68 0d 00 00 00       	push   $0xd
  40110b:	e9 10 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401110 <posix_memalign@plt>:
  401110:	ff 25 c2 3e 00 00    	jmp    *0x3ec2(%rip)        # 404fd8 <posix_memalign@GLIBC_2.2.5>
  401116:	68 0e 00 00 00       	push   $0xe
  40111b:	e9 00 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401120 <pthread_join@plt>:
  401120:	ff 25 ba 3e 00 00    	jmp    *0x3eba(%rip)        # 404fe0 <pthread_join@GLIBC_2.34>
  401126:	68 0f 00 00 00       	push   $0xf
  40112b:	e9 f0 fe ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

0000000000401130 <main>:
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
}

int main(int argc, char **argv) {
  401130:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  401132:	ba 08 00 00 00       	mov    $0x8,%edx
  401137:	bf 01 00 00 00       	mov    $0x1,%edi
  40113c:	48 8d 35 ff 1e 00 00 	lea    0x1eff(%rip),%rsi        # 403042 <_IO_stdin_used+0x42>
  401143:	41 56                	push   %r14
  401145:	41 55                	push   %r13
  401147:	41 54                	push   %r12
  long offset = 0;
  long chunkslen = 0xffffffff;
  long worksize = chunkslen * worksize_each;
  int buckets = worksize / threadsize;
  long chunksize = ceil((double) worksize / (double) chunkslen);
  char *works = calloc(worksize, sizeof(char));
  401149:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
int main(int argc, char **argv) {
  40114f:	55                   	push   %rbp
  401150:	53                   	push   %rbx
  401151:	48 81 ec b8 00 00 00 	sub    $0xb8,%rsp
  401158:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401161:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
  401169:	31 c0                	xor    %eax,%eax
  40116b:	4c 8d 6c 24 78       	lea    0x78(%rsp),%r13
  401170:	e8 6b ff ff ff       	call   4010e0 <__printf_chk@plt>
  401175:	ba 04 00 00 00       	mov    $0x4,%edx
  40117a:	48 8d 35 d3 1e 00 00 	lea    0x1ed3(%rip),%rsi        # 403054 <_IO_stdin_used+0x54>
  401181:	31 c0                	xor    %eax,%eax
  401183:	bf 01 00 00 00       	mov    $0x1,%edi
  401188:	e8 53 ff ff ff       	call   4010e0 <__printf_chk@plt>
  40118d:	ba 20 00 00 00       	mov    $0x20,%edx
  401192:	48 8d 35 b7 1e 00 00 	lea    0x1eb7(%rip),%rsi        # 403050 <_IO_stdin_used+0x50>
  401199:	31 c0                	xor    %eax,%eax
  40119b:	bf 01 00 00 00       	mov    $0x1,%edi
  4011a0:	e8 3b ff ff ff       	call   4010e0 <__printf_chk@plt>
  4011a5:	ba 0f 00 00 00       	mov    $0xf,%edx
  4011aa:	48 8d 35 b2 1e 00 00 	lea    0x1eb2(%rip),%rsi        # 403063 <_IO_stdin_used+0x63>
  4011b1:	31 c0                	xor    %eax,%eax
  4011b3:	bf 01 00 00 00       	mov    $0x1,%edi
  4011b8:	e8 23 ff ff ff       	call   4010e0 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  4011bd:	be 08 00 00 00       	mov    $0x8,%esi
  4011c2:	bf 0f 00 00 00       	mov    $0xf,%edi
  4011c7:	e8 04 ff ff ff       	call   4010d0 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  4011cc:	be 38 00 00 00       	mov    $0x38,%esi
  4011d1:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  4011d6:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  4011db:	e8 f0 fe ff ff       	call   4010d0 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011e0:	be 00 3c 00 00       	mov    $0x3c00,%esi
  4011e5:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  4011ea:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011ef:	e8 dc fe ff ff       	call   4010d0 <calloc@plt>
  char *works = calloc(worksize, sizeof(char));
  4011f4:	be 01 00 00 00       	mov    $0x1,%esi
  4011f9:	4c 89 e7             	mov    %r12,%rdi
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011fc:	49 89 c7             	mov    %rax,%r15
  4011ff:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  char *works = calloc(worksize, sizeof(char));
  401204:	e8 c7 fe ff ff       	call   4010d0 <calloc@plt>
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  401209:	4c 89 e2             	mov    %r12,%rdx
  40120c:	be ff ff ff ff       	mov    $0xffffffff,%esi
  401211:	48 89 c7             	mov    %rax,%rdi
  401214:	48 89 c3             	mov    %rax,%rbx
  401217:	e8 a4 fe ff ff       	call   4010c0 <memset@plt>
  40121c:	4c 89 e2             	mov    %r12,%rdx
  40121f:	bf 01 00 00 00       	mov    $0x1,%edi
  401224:	31 c0                	xor    %eax,%eax
  401226:	48 8d 35 4b 1e 00 00 	lea    0x1e4b(%rip),%rsi        # 403078 <_IO_stdin_used+0x78>
  40122d:	e8 ae fe ff ff       	call   4010e0 <__printf_chk@plt>
  memset(works, -1, worksize);
  printf("Buffer size %ld\n", worksize);
  int chunkindex = 0;
  int * readcursors = calloc(threadsize, sizeof(int));
  int * writecursors = calloc(threadsize, sizeof(int));
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  401232:	be 20 00 00 00       	mov    $0x20,%esi
  401237:	bf 64 00 00 00       	mov    $0x64,%edi
  40123c:	e8 8f fe ff ff       	call   4010d0 <calloc@plt>
  401241:	31 d2                	xor    %edx,%edx
  401243:	bf 01 00 00 00       	mov    $0x1,%edi
  401248:	48 8d 35 3a 1e 00 00 	lea    0x1e3a(%rip),%rsi        # 403089 <_IO_stdin_used+0x89>
  40124f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  401254:	31 c0                	xor    %eax,%eax
  401256:	e8 85 fe ff ff       	call   4010e0 <__printf_chk@plt>
  40125b:	4c 89 e2             	mov    %r12,%rdx
  40125e:	bf 01 00 00 00       	mov    $0x1,%edi
  401263:	31 c0                	xor    %eax,%eax
  401265:	48 8d 35 29 1e 00 00 	lea    0x1e29(%rip),%rsi        # 403095 <_IO_stdin_used+0x95>
  40126c:	e8 6f fe ff ff       	call   4010e0 <__printf_chk@plt>
   // works[i].taskindex = 2;
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  401271:	be 04 00 00 00       	mov    $0x4,%esi
  401276:	bf 0f 00 00 00       	mov    $0xf,%edi
  40127b:	e8 50 fe ff ff       	call   4010d0 <calloc@plt>
  
  long * globalwrite;
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  401280:	ba 00 02 00 00       	mov    $0x200,%edx
  401285:	48 8d 7c 24 70       	lea    0x70(%rsp),%rdi
  40128a:	be 80 00 00 00       	mov    $0x80,%esi
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  40128f:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  401294:	e8 77 fe ff ff       	call   401110 <posix_memalign@plt>
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  401299:	be 0c 00 00 00       	mov    $0xc,%esi
  40129e:	bf 0f 00 00 00       	mov    $0xf,%edi
  4012a3:	85 c0                	test   %eax,%eax
  4012a5:	b8 00 00 00 00       	mov    $0x0,%eax
  4012aa:	48 0f 44 44 24 70    	cmove  0x70(%rsp),%rax
  4012b0:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  4012b5:	e8 16 fe ff ff       	call   4010d0 <calloc@plt>
  data[0].works = works;
  4012ba:	49 89 5f 70          	mov    %rbx,0x70(%r15)
  int accesssize = 100000000;
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  4012be:	be 14 00 00 00       	mov    $0x14,%esi
  4012c3:	bf 00 e1 f5 05       	mov    $0x5f5e100,%edi
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  4012c8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  4012cd:	e8 fe fd ff ff       	call   4010d0 <calloc@plt>
  struct Access * writes = calloc(accesssize, sizeof(struct Access));
  4012d2:	be 14 00 00 00       	mov    $0x14,%esi
  4012d7:	bf 00 e1 f5 05       	mov    $0x5f5e100,%edi
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  4012dc:	48 89 c3             	mov    %rax,%rbx
  struct Access * writes = calloc(accesssize, sizeof(struct Access));
  4012df:	e8 ec fd ff ff       	call   4010d0 <calloc@plt>
  4012e4:	66 48 0f 6e eb       	movq   %rbx,%xmm5
      posix_memalign((void **)&stack, 16, 8016);
      
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
      cos[y].data = codata; 
      codata->running = 1;
      cos[y].eip = (uint64_t)coroutine_func;
  4012e9:	4c 89 fb             	mov    %r15,%rbx
  4012ec:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  4012f4:	66 48 0f 6e f0       	movq   %rax,%xmm6
  4012f9:	41 bf 01 00 00 00    	mov    $0x1,%r15d
  4012ff:	66 0f 6c ee          	punpcklqdq %xmm6,%xmm5
  401303:	0f 29 6c 24 40       	movaps %xmm5,0x40(%rsp)
  for (int x = 0; x < threadsize ; x++) {
  401308:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  401310:	41 8d 47 ff          	lea    -0x1(%r15),%eax
    struct Coroutine * cos = calloc(10, sizeof(struct Coroutine));
  401314:	be 20 00 00 00       	mov    $0x20,%esi
  401319:	bf 0a 00 00 00       	mov    $0xa,%edi
  40131e:	44 89 7c 24 10       	mov    %r15d,0x10(%rsp)
  401323:	89 44 24 14          	mov    %eax,0x14(%rsp)
  401327:	e8 a4 fd ff ff       	call   4010d0 <calloc@plt>
    data[x].coroutines = cos;
  40132c:	48 89 83 c0 03 00 00 	mov    %rax,0x3c0(%rbx)
    for (int y = 0; y < 10; y++ ) {
  401333:	4c 8d 70 08          	lea    0x8(%rax),%r14
  401337:	4c 8d a0 48 01 00 00 	lea    0x148(%rax),%r12
  40133e:	eb 3f                	jmp    40137f <main+0x24f>
  401340:	48 8b 6c 24 78       	mov    0x78(%rsp),%rbp
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
  401345:	be 04 00 00 00       	mov    $0x4,%esi
  40134a:	bf 01 00 00 00       	mov    $0x1,%edi
  40134f:	e8 7c fd ff ff       	call   4010d0 <calloc@plt>
      cos[y].data = codata; 
  401354:	49 89 46 10          	mov    %rax,0x10(%r14)
      codata->running = 1;
  401358:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
      cos[y].rsp = stack + 8016;
  40135e:	48 8d 85 50 1f 00 00 	lea    0x1f50(%rbp),%rax
  401365:	66 48 0f 6e c0       	movq   %rax,%xmm0
  40136a:	0f 16 05 87 3c 00 00 	movhps 0x3c87(%rip),%xmm0        # 404ff8 <_GLOBAL_OFFSET_TABLE_+0xa8>
    for (int y = 0; y < 10; y++ ) {
  401371:	49 83 c6 20          	add    $0x20,%r14
      cos[y].rsp = stack + 8016;
  401375:	41 0f 11 46 e0       	movups %xmm0,-0x20(%r14)
    for (int y = 0; y < 10; y++ ) {
  40137a:	4d 39 f4             	cmp    %r14,%r12
  40137d:	74 41                	je     4013c0 <main+0x290>
      posix_memalign((void **)&stack, 16, 8016);
  40137f:	ba 50 1f 00 00       	mov    $0x1f50,%edx
  401384:	be 10 00 00 00       	mov    $0x10,%esi
  401389:	4c 89 ef             	mov    %r13,%rdi
  40138c:	e8 7f fd ff ff       	call   401110 <posix_memalign@plt>
  401391:	85 c0                	test   %eax,%eax
  401393:	74 ab                	je     401340 <main+0x210>
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
  401395:	be 04 00 00 00       	mov    $0x4,%esi
  40139a:	bf 01 00 00 00       	mov    $0x1,%edi
  40139f:	e8 2c fd ff ff       	call   4010d0 <calloc@plt>
      cos[y].rsp = stack + 8016;
  4013a4:	f3 0f 7e 05 74 1f 00 00 	movq   0x1f74(%rip),%xmm0        # 403320 <_IO_stdin_used+0x320>
      cos[y].data = codata; 
  4013ac:	49 89 46 10          	mov    %rax,0x10(%r14)
      codata->running = 1;
  4013b0:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
      cos[y].rsp = stack + 8016;
  4013b6:	eb b2                	jmp    40136a <main+0x23a>
  4013b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    }
    struct Scheduler * scheduler = calloc(1, sizeof(struct Scheduler));
  4013c0:	be 08 00 00 00       	mov    $0x8,%esi
  4013c5:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0; x < threadsize ; x++) {
  4013ca:	48 81 c3 00 04 00 00 	add    $0x400,%rbx
    struct Scheduler * scheduler = calloc(1, sizeof(struct Scheduler));
  4013d1:	e8 fa fc ff ff       	call   4010d0 <calloc@plt>
    data[x].scheduler = scheduler;   
    data[x].reads = reads;
  4013d6:	66 0f 6f 4c 24 40    	movdqa 0x40(%rsp),%xmm1
    data[x].writes = writes; 
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t)); 
  4013dc:	be 80 00 00 00       	mov    $0x80,%esi
  4013e1:	bf 01 00 00 00       	mov    $0x1,%edi
    data[x].scheduler = scheduler;   
  4013e6:	48 89 43 c8          	mov    %rax,-0x38(%rbx)
    data[x].reads = reads;
  4013ea:	0f 29 4b a0          	movaps %xmm1,-0x60(%rbx)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t)); 
  4013ee:	e8 dd fc ff ff       	call   4010d0 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set); 
  4013f3:	0f b6 4c 24 10       	movzbl 0x10(%rsp),%ecx
  4013f8:	ba 01 00 00 00       	mov    $0x1,%edx
  4013fd:	44 8b 74 24 14       	mov    0x14(%rsp),%r14d
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t)); 
  401402:	48 89 83 78 fc ff ff 	mov    %rax,-0x388(%rbx)
  401409:	48 8d 35 90 1e 00 00 	lea    0x1e90(%rip),%rsi        # 4032a0 <_IO_stdin_used+0x2a0>
  401410:	bf 01 00 00 00       	mov    $0x1,%edi
    CPU_SET(cpu += 1, data[x].cpu_set); 
  401415:	48 d3 e2             	shl    %cl,%rdx
  401418:	48 09 10             	or     %rdx,(%rax)
  40141b:	44 89 f9             	mov    %r15d,%ecx
  40141e:	44 89 f2             	mov    %r14d,%edx
  401421:	31 c0                	xor    %eax,%eax
  401423:	e8 b8 fc ff ff       	call   4010e0 <__printf_chk@plt>
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].bucketstart = x * buckets; 
    data[x].globalwrite = globalwrite;
  401428:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    data[x].bucketstart = x * buckets; 
  40142d:	8b 6c 24 0c          	mov    0xc(%rsp),%ebp
    data[x].loglevel = debug;
    data[x].running = 2;
    data[x].threadindex = x;
  401431:	44 89 b3 64 fc ff ff 	mov    %r14d,-0x39c(%rbx)
    data[x].running = 2;
  401438:	48 8b 0d d9 1e 00 00 	mov    0x1ed9(%rip),%rcx        # 403318 <_IO_stdin_used+0x318>
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].readies = readies;
    data[x].readies[x] = 0;
    data[x].buckets = buckets;
    data[x].main = &data[0];
  40143f:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    data[x].loglevel = debug;
  401444:	c7 83 80 fc ff ff 00 00 00 00 	movl   $0x0,-0x380(%rbx)
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].mystream = 1 + (x / 4);
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40144e:	be 30 00 00 00       	mov    $0x30,%esi
    data[x].globalwrite = globalwrite;
  401453:	48 89 43 80          	mov    %rax,-0x80(%rbx)
    data[x].threadindex = x;
  401457:	44 89 f0             	mov    %r14d,%eax
    data[x].read = 0;
  40145a:	66 0f 6f 15 ce 1e 00 00 	movdqa 0x1ece(%rip),%xmm2        # 403330 <_IO_stdin_used+0x330>
    data[x].running = 2;
  401462:	48 89 8b 5c fc ff ff 	mov    %rcx,-0x3a4(%rbx)
    data[x].readies = readies;
  401469:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    data[x].mystream = 1 + (x / 4);
  40146e:	c1 f8 02             	sar    $0x2,%eax
    data[x].bucketstart = x * buckets; 
  401471:	89 ab 98 fc ff ff    	mov    %ebp,-0x368(%rbx)
    data[x].mystream = 1 + (x / 4);
  401477:	41 89 c6             	mov    %eax,%r14d
  for (int x = 0; x < threadsize ; x++) {
  40147a:	81 c5 11 11 11 11    	add    $0x11111111,%ebp
    data[x].chunkslen = chunkslen;
  401480:	66 0f 6f 1d b8 1e 00 00 	movdqa 0x1eb8(%rip),%xmm3        # 403340 <_IO_stdin_used+0x340>
    data[x].readies = readies;
  401488:	48 89 8b 20 fc ff ff 	mov    %rcx,-0x3e0(%rbx)
    data[x].mystream = 1 + (x / 4);
  40148f:	41 83 c6 01          	add    $0x1,%r14d
    data[x].prevread = threadsize;
  401493:	66 0f 6f 25 b5 1e 00 00 	movdqa 0x1eb5(%rip),%xmm4        # 403350 <_IO_stdin_used+0x350>
    data[x].availables = buckets;
  40149b:	c7 83 94 fc ff ff 11 11 11 11 	movl   $0x11111111,-0x36c(%rbx)
    data[x].threadsize = threadsize;
  4014a5:	c7 83 68 fc ff ff 0f 00 00 00 	movl   $0xf,-0x398(%rbx)
    data[x].readies[x] = 0;
  4014af:	42 c7 44 b9 fc 00 00 00 00 	movl   $0x0,-0x4(%rcx,%r15,4)
    data[x].freelist = freelist;
  4014b8:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
  for (int x = 0; x < threadsize ; x++) {
  4014bd:	49 83 c7 01          	add    $0x1,%r15
    data[x].main = &data[0];
  4014c1:	48 89 bb 28 fc ff ff 	mov    %rdi,-0x3d8(%rbx)
    data[x].threads = data;
  4014c8:	48 89 bb 30 fc ff ff 	mov    %rdi,-0x3d0(%rbx)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4014cf:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].freelist = freelist;
  4014d4:	48 89 8b a0 fc ff ff 	mov    %rcx,-0x360(%rbx)
    data[x].buckets = buckets;
  4014db:	c7 83 90 fc ff ff 11 11 11 11 	movl   $0x11111111,-0x370(%rbx)
    data[x].readcursor = threadsize - 1;
  4014e5:	c7 83 00 fe ff ff 0e 00 00 00 	movl   $0xe,-0x200(%rbx)
    data[x].writecursor = 0;
  4014ef:	c7 83 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%rbx)
    data[x].newmask = 0;
  4014f9:	c7 83 c8 fc ff ff 00 00 00 00 	movl   $0x0,-0x338(%rbx)
    data[x].mystream = 1 + (x / 4);
  401503:	44 89 73 8c          	mov    %r14d,-0x74(%rbx)
    data[x].thiswrite = threadsize;
  401507:	c7 83 28 ff ff ff 0f 00 00 00 	movl   $0xf,-0xd8(%rbx)
    data[x].read = 0;
  401511:	0f 29 93 00 fc ff ff 	movaps %xmm2,-0x400(%rbx)
    data[x].chunkslen = chunkslen;
  401518:	0f 11 9b b8 fc ff ff 	movups %xmm3,-0x348(%rbx)
    data[x].prevread = threadsize;
  40151f:	0f 11 a3 08 ff ff ff 	movups %xmm4,-0xf8(%rbx)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401526:	e8 a5 fb ff ff       	call   4010d0 <calloc@plt>
    data[x].epochssize = epochs;
    data[x].globalread = globalread;
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  40152b:	be 30 00 00 00       	mov    $0x30,%esi
  401530:	bf 10 27 00 00       	mov    $0x2710,%edi
    data[x].epochssize = epochs;
  401535:	c7 83 20 ff ff ff 80 96 98 00 	movl   $0x989680,-0xe0(%rbx)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40153f:	48 89 83 18 ff ff ff 	mov    %rax,-0xe8(%rbx)
    data[x].globalread = globalread;
  401546:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  40154b:	48 89 83 48 ff ff ff 	mov    %rax,-0xb8(%rbx)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  401552:	e8 79 fb ff ff       	call   4010d0 <calloc@plt>
    data[x].accesssize = accesssize;
  401557:	c7 43 b8 00 e1 f5 05 	movl   $0x5f5e100,-0x48(%rbx)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  40155e:	48 89 83 30 ff ff ff 	mov    %rax,-0xd0(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  401565:	89 6c 24 0c          	mov    %ebp,0xc(%rsp)
  401569:	49 83 ff 10          	cmp    $0x10,%r15
  40156d:	0f 85 9d fd ff ff    	jne    401310 <main+0x1e0>
  401573:	4c 8b 74 24 50       	mov    0x50(%rsp),%r14
  401578:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
  40157d:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
  401582:	49 c7 c4 d0 28 40 00 	mov    $0x4028d0,%r12
  401589:	4c 89 f5             	mov    %r14,%rbp
  40158c:	4c 8d ab 48 03 00 00 	lea    0x348(%rbx),%r13
  401593:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  401598:	4c 89 f9             	mov    %r15,%rcx
  40159b:	48 89 de             	mov    %rbx,%rsi
  40159e:	4c 89 f7             	mov    %r14,%rdi
  4015a1:	4c 89 e2             	mov    %r12,%rdx
  4015a4:	e8 47 fb ff ff       	call   4010f0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4015a9:	49 8b 57 78          	mov    0x78(%r15),%rdx
  4015ad:	49 8b 3e             	mov    (%r14),%rdi
  4015b0:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  4015b5:	48 83 c3 38          	add    $0x38,%rbx
  4015b9:	49 83 c6 08          	add    $0x8,%r14
  4015bd:	49 81 c7 00 04 00 00 	add    $0x400,%r15
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4015c4:	e8 77 fa ff ff       	call   401040 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  4015c9:	49 39 dd             	cmp    %rbx,%r13
  4015cc:	75 ca                	jne    401598 <main+0x468>
  }
  
  struct timespec time = {
  4015ce:	66 0f 6f 05 8a 1d 00 00 	movdqa 0x1d8a(%rip),%xmm0        # 403360 <_IO_stdin_used+0x360>
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  4015d6:	48 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%rsi
  4015de:	4c 8d 64 24 68       	lea    0x68(%rsp),%r12
  4015e3:	48 8d bc 24 80 00 00 00 	lea    0x80(%rsp),%rdi
  struct timespec time = {
  4015eb:	0f 29 84 24 80 00 00 00 	movaps %xmm0,0x80(%rsp)
  struct timespec rem = {
  4015f3:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4015f7:	0f 29 84 24 90 00 00 00 	movaps %xmm0,0x90(%rsp)
  nanosleep(&time, &rem);
  4015ff:	e8 9c fa ff ff       	call   4010a0 <nanosleep@plt>
  401604:	48 8d 3d 96 1a 00 00 	lea    0x1a96(%rip),%rdi        # 4030a1 <_IO_stdin_used+0xa1>
  40160b:	e8 40 fa ff ff       	call   401050 <puts@plt>
  
  printf("runphased\n");
  for (int x = 0; x < threadsize ; x++) {
    data[x].running--;
  401610:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
  401615:	48 8d 3d 8f 1a 00 00 	lea    0x1a8f(%rip),%rdi        # 4030ab <_IO_stdin_used+0xab>
  40161c:	83 6b 5c 01          	subl   $0x1,0x5c(%rbx)
  401620:	83 ab 5c 04 00 00 01 	subl   $0x1,0x45c(%rbx)
  401627:	83 ab 5c 08 00 00 01 	subl   $0x1,0x85c(%rbx)
  40162e:	83 ab 5c 0c 00 00 01 	subl   $0x1,0xc5c(%rbx)
  401635:	83 ab 5c 10 00 00 01 	subl   $0x1,0x105c(%rbx)
  40163c:	83 ab 5c 14 00 00 01 	subl   $0x1,0x145c(%rbx)
  401643:	83 ab 5c 18 00 00 01 	subl   $0x1,0x185c(%rbx)
  40164a:	83 ab 5c 1c 00 00 01 	subl   $0x1,0x1c5c(%rbx)
  401651:	83 ab 5c 20 00 00 01 	subl   $0x1,0x205c(%rbx)
  401658:	83 ab 5c 24 00 00 01 	subl   $0x1,0x245c(%rbx)
  40165f:	83 ab 5c 28 00 00 01 	subl   $0x1,0x285c(%rbx)
  401666:	83 ab 5c 2c 00 00 01 	subl   $0x1,0x2c5c(%rbx)
  40166d:	83 ab 5c 30 00 00 01 	subl   $0x1,0x305c(%rbx)
  401674:	83 ab 5c 34 00 00 01 	subl   $0x1,0x345c(%rbx)
  40167b:	83 ab 5c 38 00 00 01 	subl   $0x1,0x385c(%rbx)
  401682:	e8 c9 f9 ff ff       	call   401050 <puts@plt>
  
 printf("draining\n");
 // time.tv_sec = 3;
//nanosleep(&time, &rem);
  for (int x = 0; x < threadsize ; x++) {
    data[x].running--;
  401687:	83 6b 5c 01          	subl   $0x1,0x5c(%rbx)
  40168b:	83 ab 5c 04 00 00 01 	subl   $0x1,0x45c(%rbx)
  401692:	83 ab 5c 08 00 00 01 	subl   $0x1,0x85c(%rbx)
  401699:	83 ab 5c 0c 00 00 01 	subl   $0x1,0xc5c(%rbx)
  4016a0:	83 ab 5c 10 00 00 01 	subl   $0x1,0x105c(%rbx)
  4016a7:	83 ab 5c 14 00 00 01 	subl   $0x1,0x145c(%rbx)
  4016ae:	83 ab 5c 18 00 00 01 	subl   $0x1,0x185c(%rbx)
  4016b5:	83 ab 5c 1c 00 00 01 	subl   $0x1,0x1c5c(%rbx)
  4016bc:	83 ab 5c 20 00 00 01 	subl   $0x1,0x205c(%rbx)
  4016c3:	83 ab 5c 24 00 00 01 	subl   $0x1,0x245c(%rbx)
  4016ca:	83 ab 5c 28 00 00 01 	subl   $0x1,0x285c(%rbx)
  4016d1:	83 ab 5c 2c 00 00 01 	subl   $0x1,0x2c5c(%rbx)
  4016d8:	83 ab 5c 30 00 00 01 	subl   $0x1,0x305c(%rbx)
  4016df:	83 ab 5c 34 00 00 01 	subl   $0x1,0x345c(%rbx)
  4016e6:	83 ab 5c 38 00 00 01 	subl   $0x1,0x385c(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  4016ed:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
  4016f2:	48 83 c3 78          	add    $0x78,%rbx
  4016f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  }
  
  //nanosleep(&time, &rem);
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401700:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
  401704:	4c 89 e6             	mov    %r12,%rsi
  for (int x = 0; x < threadsize; x++) {
  401707:	48 83 c5 08          	add    $0x8,%rbp
    pthread_join(thread[x], &res);
  40170b:	e8 10 fa ff ff       	call   401120 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401710:	48 39 dd             	cmp    %rbx,%rbp
  401713:	75 eb                	jne    401700 <main+0x5d0>
  401715:	48 8d 3d 98 19 00 00 	lea    0x1998(%rip),%rdi        # 4030b4 <_IO_stdin_used+0xb4>
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  40171c:	31 ed                	xor    %ebp,%ebp
  40171e:	4c 8d 25 a4 19 00 00 	lea    0x19a4(%rip),%r12        # 4030c9 <_IO_stdin_used+0xc9>
  401725:	e8 26 f9 ff ff       	call   401050 <puts@plt>
  long sends = 1;
  for (int x = 0; x < threadsize; x++) {
  40172a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  40172f:	48 8d 58 48          	lea    0x48(%rax),%rbx
  401733:	4c 8d a8 48 3c 00 00 	lea    0x3c48(%rax),%r13
  40173a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  401740:	48 8b 13             	mov    (%rbx),%rdx
  401743:	4c 89 e6             	mov    %r12,%rsi
  401746:	bf 01 00 00 00       	mov    $0x1,%edi
  40174b:	31 c0                	xor    %eax,%eax
  40174d:	48 81 c3 00 04 00 00 	add    $0x400,%rbx
  401754:	e8 87 f9 ff ff       	call   4010e0 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  401759:	48 03 ab 00 fc ff ff 	add    -0x400(%rbx),%rbp
  for (int x = 0; x < threadsize; x++) {
  401760:	49 39 dd             	cmp    %rbx,%r13
  401763:	75 db                	jne    401740 <main+0x610>
  401765:	48 89 ea             	mov    %rbp,%rdx
  401768:	48 8d 35 65 19 00 00 	lea    0x1965(%rip),%rsi        # 4030d4 <_IO_stdin_used+0xd4>
  40176f:	bf 01 00 00 00       	mov    $0x1,%edi
  401774:	31 c0                	xor    %eax,%eax
  401776:	e8 65 f9 ff ff       	call   4010e0 <__printf_chk@plt>
  40177b:	48 89 ea             	mov    %rbp,%rdx
  40177e:	bf 01 00 00 00       	mov    $0x1,%edi
  401783:	31 c0                	xor    %eax,%eax
  401785:	48 8d 35 53 19 00 00 	lea    0x1953(%rip),%rsi        # 4030df <_IO_stdin_used+0xdf>
  40178c:	4c 8d 2d 9f 19 00 00 	lea    0x199f(%rip),%r13        # 403132 <_IO_stdin_used+0x132>
  401793:	e8 48 f9 ff ff       	call   4010e0 <__printf_chk@plt>
  }
  printf("freq: %ld\n", freq/ seconds);
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  401798:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40179d:	bf 01 00 00 00       	mov    $0x1,%edi
  4017a2:	48 8d 35 44 19 00 00 	lea    0x1944(%rip),%rsi        # 4030ed <_IO_stdin_used+0xed>
  4017a9:	48 99                	cqto
  4017ab:	48 f7 fd             	idiv   %rbp
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  
  long goods = 0;
  4017ae:	31 ed                	xor    %ebp,%ebp
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  4017b0:	49 89 c4             	mov    %rax,%r12
  4017b3:	48 89 c2             	mov    %rax,%rdx
  4017b6:	31 c0                	xor    %eax,%eax
  4017b8:	e8 23 f9 ff ff       	call   4010e0 <__printf_chk@plt>
  4017bd:	4c 89 e2             	mov    %r12,%rdx
  4017c0:	bf 01 00 00 00       	mov    $0x1,%edi
  4017c5:	31 c0                	xor    %eax,%eax
  4017c7:	48 8d 35 33 19 00 00 	lea    0x1933(%rip),%rsi        # 403101 <_IO_stdin_used+0x101>
  4017ce:	e8 0d f9 ff ff       	call   4010e0 <__printf_chk@plt>
  4017d3:	4c 89 e2             	mov    %r12,%rdx
  4017d6:	bf 01 00 00 00       	mov    $0x1,%edi
  4017db:	31 c0                	xor    %eax,%eax
  4017dd:	48 8d 35 3b 19 00 00 	lea    0x193b(%rip),%rsi        # 40311f <_IO_stdin_used+0x11f>
  4017e4:	e8 f7 f8 ff ff       	call   4010e0 <__printf_chk@plt>

  for (int x = 0; x < threadsize; x++) {
  4017e9:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  4017ee:	48 8d 98 98 03 00 00 	lea    0x398(%rax),%rbx
  4017f5:	4c 8d b0 98 3f 00 00 	lea    0x3f98(%rax),%r14
  4017fc:	0f 1f 40 00          	nopl   0x0(%rax)
  401800:	48 8b 13             	mov    (%rbx),%rdx
  401803:	4c 89 ee             	mov    %r13,%rsi
  401806:	bf 01 00 00 00       	mov    $0x1,%edi
  40180b:	31 c0                	xor    %eax,%eax
  40180d:	48 81 c3 00 04 00 00 	add    $0x400,%rbx
  401814:	e8 c7 f8 ff ff       	call   4010e0 <__printf_chk@plt>
    printf("%ld successreads\n", data[x].successreads);
    goods += data[x].successreads;
  401819:	48 03 ab 00 fc ff ff 	add    -0x400(%rbx),%rbp
  401820:	49 89 ec             	mov    %rbp,%r12
  for (int x = 0; x < threadsize; x++) {
  401823:	49 39 de             	cmp    %rbx,%r14
  401826:	75 d8                	jne    401800 <main+0x6d0>
  401828:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  }
  
  long freq_writes = 0;
  40182d:	31 ed                	xor    %ebp,%ebp
  40182f:	4c 8d 2d 0e 19 00 00 	lea    0x190e(%rip),%r13        # 403144 <_IO_stdin_used+0x144>
  401836:	48 8d 58 50          	lea    0x50(%rax),%rbx
  40183a:	4c 8d b0 50 3c 00 00 	lea    0x3c50(%rax),%r14
  401841:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  401848:	48 8b 13             	mov    (%rbx),%rdx
  40184b:	4c 89 ee             	mov    %r13,%rsi
  40184e:	bf 01 00 00 00       	mov    $0x1,%edi
  401853:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  401855:	48 81 c3 00 04 00 00 	add    $0x400,%rbx
    freq_writes += data[x].freq_writes;
  40185c:	48 01 d5             	add    %rdx,%rbp
  40185f:	e8 7c f8 ff ff       	call   4010e0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  401864:	49 39 de             	cmp    %rbx,%r14
  401867:	75 df                	jne    401848 <main+0x718>
  401869:	48 89 ea             	mov    %rbp,%rdx
  40186c:	bf 01 00 00 00       	mov    $0x1,%edi
  401871:	31 c0                	xor    %eax,%eax
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  401873:	bb 00 ca 9a 3b       	mov    $0x3b9aca00,%ebx
  401878:	48 8d 35 d1 18 00 00 	lea    0x18d1(%rip),%rsi        # 403150 <_IO_stdin_used+0x150>
  40187f:	e8 5c f8 ff ff       	call   4010e0 <__printf_chk@plt>
  401884:	48 89 ea             	mov    %rbp,%rdx
  401887:	bf 01 00 00 00       	mov    $0x1,%edi
  40188c:	31 c0                	xor    %eax,%eax
  40188e:	48 8d 35 cd 18 00 00 	lea    0x18cd(%rip),%rsi        # 403162 <_IO_stdin_used+0x162>
  401895:	e8 46 f8 ff ff       	call   4010e0 <__printf_chk@plt>
  40189a:	48 89 d8             	mov    %rbx,%rax
  40189d:	bf 01 00 00 00       	mov    $0x1,%edi
  4018a2:	48 8d 35 d1 18 00 00 	lea    0x18d1(%rip),%rsi        # 40317a <_IO_stdin_used+0x17a>
  4018a9:	48 99                	cqto
  4018ab:	48 f7 fd             	idiv   %rbp
  4018ae:	48 8d 2d 47 18 00 00 	lea    0x1847(%rip),%rbp        # 4030fc <_IO_stdin_used+0xfc>
  4018b5:	49 89 c5             	mov    %rax,%r13
  4018b8:	48 89 c2             	mov    %rax,%rdx
  4018bb:	31 c0                	xor    %eax,%eax
  4018bd:	e8 1e f8 ff ff       	call   4010e0 <__printf_chk@plt>
  4018c2:	4c 89 ea             	mov    %r13,%rdx
  4018c5:	bf 01 00 00 00       	mov    $0x1,%edi
  4018ca:	31 c0                	xor    %eax,%eax
  4018cc:	48 8d 35 ed 19 00 00 	lea    0x19ed(%rip),%rsi        # 4032c0 <_IO_stdin_used+0x2c0>
  4018d3:	e8 08 f8 ff ff       	call   4010e0 <__printf_chk@plt>
  4018d8:	4c 89 ea             	mov    %r13,%rdx
  4018db:	bf 01 00 00 00       	mov    $0x1,%edi
  4018e0:	31 c0                	xor    %eax,%eax
  4018e2:	48 8d 35 ac 18 00 00 	lea    0x18ac(%rip),%rsi        # 403195 <_IO_stdin_used+0x195>
  4018e9:	e8 f2 f7 ff ff       	call   4010e0 <__printf_chk@plt>
  4018ee:	48 8d 3d ba 18 00 00 	lea    0x18ba(%rip),%rdi        # 4031af <_IO_stdin_used+0x1af>
  4018f5:	e8 56 f7 ff ff       	call   401050 <puts@plt>
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  4018fa:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
  4018ff:	48 89 ee             	mov    %rbp,%rsi
  401902:	31 c0                	xor    %eax,%eax
  401904:	bf 01 00 00 00       	mov    $0x1,%edi
  401909:	49 8b 97 f0 00 00 00 	mov    0xf0(%r15),%rdx
  401910:	49 2b 97 e0 00 00 00 	sub    0xe0(%r15),%rdx
  401917:	4d 8d b7 20 03 00 00 	lea    0x320(%r15),%r14
  40191e:	4d 8d af 20 3f 00 00 	lea    0x3f20(%r15),%r13
  401925:	e8 b6 f7 ff ff       	call   4010e0 <__printf_chk@plt>
  40192a:	48 89 ee             	mov    %rbp,%rsi
  40192d:	bf 01 00 00 00       	mov    $0x1,%edi
  401932:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  401934:	49 8b 97 00 01 00 00 	mov    0x100(%r15),%rdx
  40193b:	49 2b 97 e0 00 00 00 	sub    0xe0(%r15),%rdx
  401942:	e8 99 f7 ff ff       	call   4010e0 <__printf_chk@plt>
  401947:	48 89 ee             	mov    %rbp,%rsi
  40194a:	bf 01 00 00 00       	mov    $0x1,%edi
  40194f:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  401951:	49 8b 97 f0 00 00 00 	mov    0xf0(%r15),%rdx
  401958:	49 2b 97 00 01 00 00 	sub    0x100(%r15),%rdx
  40195f:	e8 7c f7 ff ff       	call   4010e0 <__printf_chk@plt>
  401964:	48 89 ee             	mov    %rbp,%rsi
  401967:	bf 01 00 00 00       	mov    $0x1,%edi
  40196c:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  40196e:	49 8b 97 20 01 00 00 	mov    0x120(%r15),%rdx
  401975:	49 2b 97 10 01 00 00 	sub    0x110(%r15),%rdx
  40197c:	e8 5f f7 ff ff       	call   4010e0 <__printf_chk@plt>
  401981:	48 89 ee             	mov    %rbp,%rsi
  401984:	bf 01 00 00 00       	mov    $0x1,%edi
  401989:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  40198b:	49 8b 97 10 01 00 00 	mov    0x110(%r15),%rdx
  401992:	49 2b 97 20 01 00 00 	sub    0x120(%r15),%rdx
  401999:	e8 42 f7 ff ff       	call   4010e0 <__printf_chk@plt>
  40199e:	48 89 ee             	mov    %rbp,%rsi
  4019a1:	bf 01 00 00 00       	mov    $0x1,%edi
  4019a6:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  4019a8:	49 8b 97 10 01 00 00 	mov    0x110(%r15),%rdx
  4019af:	49 2b 97 00 01 00 00 	sub    0x100(%r15),%rdx
  4019b6:	e8 25 f7 ff ff       	call   4010e0 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  4019bb:	49 8b 97 40 01 00 00 	mov    0x140(%r15),%rdx
  4019c2:	bf 01 00 00 00       	mov    $0x1,%edi
  4019c7:	49 2b 97 30 01 00 00 	sub    0x130(%r15),%rdx
  4019ce:	48 8d 35 e7 17 00 00 	lea    0x17e7(%rip),%rsi        # 4031bc <_IO_stdin_used+0x1bc>
  4019d5:	31 c0                	xor    %eax,%eax
  4019d7:	e8 04 f7 ff ff       	call   4010e0 <__printf_chk@plt>
  4019dc:	4c 89 e2             	mov    %r12,%rdx
  4019df:	bf 01 00 00 00       	mov    $0x1,%edi
  4019e4:	31 c0                	xor    %eax,%eax
  4019e6:	48 8d 35 d7 17 00 00 	lea    0x17d7(%rip),%rsi        # 4031c4 <_IO_stdin_used+0x1c4>
  4019ed:	e8 ee f6 ff ff       	call   4010e0 <__printf_chk@plt>
  } 
  printf("%ld good reads per second\n", goods / seconds);
  printf("%ld good reads per second latency\n", 1000000000 / (goods / seconds));
  4019f2:	48 89 d8             	mov    %rbx,%rax
  4019f5:	bf 01 00 00 00       	mov    $0x1,%edi
  4019fa:	31 db                	xor    %ebx,%ebx
  4019fc:	48 99                	cqto
  4019fe:	48 8d 35 e3 18 00 00 	lea    0x18e3(%rip),%rsi        # 4032e8 <_IO_stdin_used+0x2e8>
  401a05:	49 f7 fc             	idiv   %r12
  401a08:	48 89 c2             	mov    %rax,%rdx
  401a0b:	31 c0                	xor    %eax,%eax
  401a0d:	e8 ce f6 ff ff       	call   4010e0 <__printf_chk@plt>
  401a12:	48 8d 3d c6 17 00 00 	lea    0x17c6(%rip),%rdi        # 4031df <_IO_stdin_used+0x1df>
  401a19:	e8 32 f6 ff ff       	call   401050 <puts@plt>
  if (SAMPLE == 1) {
    printf("creating sample log\n");
  char * filename = calloc(100, sizeof(char));
  401a1e:	be 01 00 00 00       	mov    $0x1,%esi
  401a23:	bf 64 00 00 00       	mov    $0x64,%edi
  401a28:	e8 a3 f6 ff ff       	call   4010d0 <calloc@plt>
  char * buf = calloc(1000, sizeof(char));
  401a2d:	be 01 00 00 00       	mov    $0x1,%esi
  401a32:	bf e8 03 00 00       	mov    $0x3e8,%edi
  char * filename = calloc(100, sizeof(char));
  401a37:	49 89 c4             	mov    %rax,%r12
  char * buf = calloc(1000, sizeof(char));
  401a3a:	e8 91 f6 ff ff       	call   4010d0 <calloc@plt>
  memset(filename, 0, 100);
  snprintf(filename, 100, "samples");
  FILE *out_file = fopen(filename, "w");
  401a3f:	4c 89 e7             	mov    %r12,%rdi
  401a42:	48 8d 35 aa 17 00 00 	lea    0x17aa(%rip),%rsi        # 4031f3 <_IO_stdin_used+0x1f3>
  char * buf = calloc(1000, sizeof(char));
  401a49:	48 89 c5             	mov    %rax,%rbp
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401a4c:	48 b8 73 61 6d 70 6c 65 73 00 	movabs $0x73656c706d6173,%rax
  401a56:	49 89 04 24          	mov    %rax,(%r12)
  FILE *out_file = fopen(filename, "w");
  401a5a:	e8 a1 f6 ff ff       	call   401100 <fopen@plt>
  401a5f:	49 89 c4             	mov    %rax,%r12
  
  for (int x = 0; x < threadsize; x++) {
  401a62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int y = 0; y < data[x].epochssize; y++) {
  401a68:	41 8b 0e             	mov    (%r14),%ecx
  401a6b:	45 31 ff             	xor    %r15d,%r15d
  401a6e:	85 c9                	test   %ecx,%ecx
  401a70:	7e 25                	jle    401a97 <main+0x967>
  401a72:	49 8b 76 f8          	mov    -0x8(%r14),%rsi
      struct Epoch * epoch = &data[x].epochs[y];
  401a76:	49 63 c7             	movslq %r15d,%rax
  401a79:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  401a7d:	48 c1 e2 04          	shl    $0x4,%rdx
  401a81:	48 01 f2             	add    %rsi,%rdx
      if (epoch->set == 1) {
  401a84:	83 7a 24 01          	cmpl   $0x1,0x24(%rdx)
  401a88:	0f 84 8a 03 00 00    	je     401e18 <main+0xce8>
    for (int y = 0; y < data[x].epochssize; y++) {
  401a8e:	41 83 c7 01          	add    $0x1,%r15d
  401a92:	44 39 f9             	cmp    %r15d,%ecx
  401a95:	7f df                	jg     401a76 <main+0x946>
  for (int x = 0; x < threadsize; x++) {
  401a97:	49 81 c6 00 04 00 00 	add    $0x400,%r14
  401a9e:	4d 39 f5             	cmp    %r14,%r13
  401aa1:	75 c5                	jne    401a68 <main+0x938>
        snprintf(buf, 100, "%ld%ld %d %d %ld %d %d\n", epoch->time.tv_sec, epoch->time.tv_nsec, epoch->kind, epoch->stream, epoch->buffer, epoch->thread, epoch->dest);
        fprintf(out_file, "%s", buf);
      }
    }
  }
    fclose(out_file);
  401aa3:	4c 89 e7             	mov    %r12,%rdi
  401aa6:	45 31 ed             	xor    %r13d,%r13d
  401aa9:	e8 c2 f5 ff ff       	call   401070 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  401aae:	48 8d 3d 58 17 00 00 	lea    0x1758(%rip),%rdi        # 40320d <_IO_stdin_used+0x20d>
  401ab5:	e8 96 f5 ff ff       	call   401050 <puts@plt>
    }
  } */

 if (ACCESSLOG == 1) {
   printf("creating access log\n");
   char * filename = calloc(100, sizeof(char));
  401aba:	be 01 00 00 00       	mov    $0x1,%esi
  401abf:	bf 64 00 00 00       	mov    $0x64,%edi
  401ac4:	e8 07 f6 ff ff       	call   4010d0 <calloc@plt>
  char * buf = calloc(1000, sizeof(char));
  401ac9:	be 01 00 00 00       	mov    $0x1,%esi
  401ace:	bf e8 03 00 00       	mov    $0x3e8,%edi
   char * filename = calloc(100, sizeof(char));
  401ad3:	49 89 c4             	mov    %rax,%r12
  char * buf = calloc(1000, sizeof(char));
  401ad6:	e8 f5 f5 ff ff       	call   4010d0 <calloc@plt>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401adb:	41 b8 67 00 00 00    	mov    $0x67,%r8d
  memset(filename, 0, 100);
  snprintf(filename, 100, "accesslog");
  FILE *out_file = fopen(filename, "w");
  401ae1:	4c 89 e7             	mov    %r12,%rdi
  401ae4:	48 8d 35 08 17 00 00 	lea    0x1708(%rip),%rsi        # 4031f3 <_IO_stdin_used+0x1f3>
  char * buf = calloc(1000, sizeof(char));
  401aeb:	48 89 c5             	mov    %rax,%rbp
  401aee:	66 45 89 44 24 08    	mov    %r8w,0x8(%r12)
  401af4:	48 b8 61 63 63 65 73 73 6c 6f 	movabs $0x6f6c737365636361,%rax
  401afe:	49 89 04 24          	mov    %rax,(%r12)
  FILE *out_file = fopen(filename, "w");
  401b02:	e8 f9 f5 ff ff       	call   401100 <fopen@plt>
  401b07:	49 89 c4             	mov    %rax,%r12

     for (int x = 0; x < threadsize; x++) {
  401b0a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  401b0f:	4c 8d b0 a0 03 00 00 	lea    0x3a0(%rax),%r14
  401b16:	4c 8d b8 a0 3f 00 00 	lea    0x3fa0(%rax),%r15
  401b1d:	0f 1f 00             	nopl   (%rax)
    for (int y = 0; y < data[x].accesssize; y++) {
  401b20:	41 8b 56 18          	mov    0x18(%r14),%edx
  401b24:	31 db                	xor    %ebx,%ebx
  401b26:	85 d2                	test   %edx,%edx
  401b28:	7e 45                	jle    401b6f <main+0xa3f>
  401b2a:	49 8b 0e             	mov    (%r14),%rcx
      struct Access * access = &data[x].reads[y];
  401b2d:	48 63 c3             	movslq %ebx,%rax
  401b30:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  401b34:	48 8d 34 81          	lea    (%rcx,%rax,4),%rsi
      if (access->set == 1) {
  401b38:	83 7e 10 01          	cmpl   $0x1,0x10(%rsi)
  401b3c:	0f 84 56 03 00 00    	je     401e98 <main+0xd68>
    for (int y = 0; y < data[x].accesssize; y++) {
  401b42:	83 c3 01             	add    $0x1,%ebx
  401b45:	39 da                	cmp    %ebx,%edx
  401b47:	7f e4                	jg     401b2d <main+0x9fd>
        memset(buf, 0, 1000);
        snprintf(buf, 100, "r %d %d %d\n", access->stream, access->global, access->cursor);
        fprintf(out_file, "%s", buf);
      }
    }
       for (int y = 0; y < data[x].accesssize; y++) {
  401b49:	85 d2                	test   %edx,%edx
  401b4b:	7e 22                	jle    401b6f <main+0xa3f>
  401b4d:	31 db                	xor    %ebx,%ebx
  401b4f:	49 8b 4e 08          	mov    0x8(%r14),%rcx
      struct Access * access = &data[x].writes[y];
  401b53:	48 63 c3             	movslq %ebx,%rax
  401b56:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  401b5a:	48 8d 34 81          	lea    (%rcx,%rax,4),%rsi
      if (access->set == 1) {
  401b5e:	83 7e 10 01          	cmpl   $0x1,0x10(%rsi)
  401b62:	0f 84 40 02 00 00    	je     401da8 <main+0xc78>
       for (int y = 0; y < data[x].accesssize; y++) {
  401b68:	83 c3 01             	add    $0x1,%ebx
  401b6b:	39 d3                	cmp    %edx,%ebx
  401b6d:	7c e4                	jl     401b53 <main+0xa23>
     for (int x = 0; x < threadsize; x++) {
  401b6f:	49 81 c6 00 04 00 00 	add    $0x400,%r14
  401b76:	4d 39 f7             	cmp    %r14,%r15
  401b79:	75 a5                	jne    401b20 <main+0x9f0>
        snprintf(buf, 100, "w %d %d %d\n", access->stream, access->global, access->cursor);
        fprintf(out_file, "%s", buf);
      }
       }
     }
   fclose(out_file);
  401b7b:	4c 89 e7             	mov    %r12,%rdi
  401b7e:	31 db                	xor    %ebx,%ebx
  401b80:	e8 eb f4 ff ff       	call   401070 <fclose@plt>
   
 }

  char * filename = calloc(100, sizeof(char));
  401b85:	be 01 00 00 00       	mov    $0x1,%esi
  401b8a:	bf 64 00 00 00       	mov    $0x64,%edi
  401b8f:	e8 3c f5 ff ff       	call   4010d0 <calloc@plt>
  char * buf = calloc(1000, sizeof(char));
  401b94:	be 01 00 00 00       	mov    $0x1,%esi
  401b99:	bf e8 03 00 00       	mov    $0x3e8,%edi
  char * filename = calloc(100, sizeof(char));
  401b9e:	49 89 c4             	mov    %rax,%r12
  char * buf = calloc(1000, sizeof(char));
  401ba1:	e8 2a f5 ff ff       	call   4010d0 <calloc@plt>
  401ba6:	66 0f 6f 05 c2 17 00 00 	movdqa 0x17c2(%rip),%xmm0        # 403370 <_IO_stdin_used+0x370>
  memset(filename, 0, 100);
  snprintf(filename, 100, "coroutine.struct");
  FILE *out_file = fopen(filename, "w");
  401bae:	4c 89 e7             	mov    %r12,%rdi
  401bb1:	41 c6 44 24 10 00    	movb   $0x0,0x10(%r12)
  401bb7:	48 8d 35 35 16 00 00 	lea    0x1635(%rip),%rsi        # 4031f3 <_IO_stdin_used+0x1f3>
  char * buf = calloc(1000, sizeof(char));
  401bbe:	48 89 c5             	mov    %rax,%rbp
  401bc1:	41 0f 11 04 24       	movups %xmm0,(%r12)
  FILE *out_file = fopen(filename, "w");
  401bc6:	e8 35 f5 ff ff       	call   401100 <fopen@plt>
  401bcb:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401bd0:	48 89 ef             	mov    %rbp,%rdi
  401bd3:	45 31 c9             	xor    %r9d,%r9d
  401bd6:	49 89 c4             	mov    %rax,%r12
  401bd9:	48 89 d8             	mov    %rbx,%rax
  401bdc:	ba 01 00 00 00       	mov    $0x1,%edx
  401be1:	be 64 00 00 00       	mov    $0x64,%esi
  401be6:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  401be9:	4c 8d 05 49 16 00 00 	lea    0x1649(%rip),%r8        # 403239 <_IO_stdin_used+0x239>
  401bf0:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401bf5:	48 89 ef             	mov    %rbp,%rdi
  401bf8:	e8 33 f4 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401bfd:	4c 89 e6             	mov    %r12,%rsi
  401c00:	48 89 ef             	mov    %rbp,%rdi
  401c03:	e8 a8 f4 ff ff       	call   4010b0 <fputs@plt>
  401c08:	48 89 d8             	mov    %rbx,%rax
  401c0b:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401c10:	48 89 ef             	mov    %rbp,%rdi
  401c13:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401c16:	41 b9 08 00 00 00    	mov    $0x8,%r9d
  401c1c:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401c21:	48 89 ef             	mov    %rbp,%rdi
  401c24:	4c 8d 05 65 16 00 00 	lea    0x1665(%rip),%r8        # 403290 <_IO_stdin_used+0x290>
  401c2b:	ba 01 00 00 00       	mov    $0x1,%edx
  401c30:	be 64 00 00 00       	mov    $0x64,%esi
  401c35:	e8 f6 f3 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401c3a:	4c 89 e6             	mov    %r12,%rsi
  401c3d:	48 89 ef             	mov    %rbp,%rdi
  401c40:	e8 6b f4 ff ff       	call   4010b0 <fputs@plt>
  401c45:	48 89 d8             	mov    %rbx,%rax
  401c48:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401c4d:	48 89 ef             	mov    %rbp,%rdi
  401c50:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401c53:	41 b9 10 00 00 00    	mov    $0x10,%r9d
  401c59:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401c5e:	48 89 ef             	mov    %rbp,%rdi
  401c61:	4c 8d 05 dc 15 00 00 	lea    0x15dc(%rip),%r8        # 403244 <_IO_stdin_used+0x244>
  401c68:	ba 01 00 00 00       	mov    $0x1,%edx
  401c6d:	be 64 00 00 00       	mov    $0x64,%esi
  401c72:	e8 b9 f3 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401c77:	4c 89 e6             	mov    %r12,%rsi
  401c7a:	48 89 ef             	mov    %rbp,%rdi
  401c7d:	e8 2e f4 ff ff       	call   4010b0 <fputs@plt>
  401c82:	48 89 d8             	mov    %rbx,%rax
  401c85:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401c8a:	48 89 ef             	mov    %rbp,%rdi
  401c8d:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401c90:	41 b9 18 00 00 00    	mov    $0x18,%r9d
  401c96:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401c9b:	48 89 ef             	mov    %rbp,%rdi
  401c9e:	4c 8d 05 a8 15 00 00 	lea    0x15a8(%rip),%r8        # 40324d <_IO_stdin_used+0x24d>
  401ca5:	ba 01 00 00 00       	mov    $0x1,%edx
  401caa:	be 64 00 00 00       	mov    $0x64,%esi
  401caf:	e8 7c f3 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401cb4:	4c 89 e6             	mov    %r12,%rsi
  401cb7:	48 89 ef             	mov    %rbp,%rdi
  401cba:	e8 f1 f3 ff ff       	call   4010b0 <fputs@plt>
  401cbf:	48 89 d8             	mov    %rbx,%rax
  401cc2:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401cc7:	48 89 ef             	mov    %rbp,%rdi
  401cca:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401ccd:	45 31 c9             	xor    %r9d,%r9d
  401cd0:	4c 8d 05 80 15 00 00 	lea    0x1580(%rip),%r8        # 403257 <_IO_stdin_used+0x257>
  401cd7:	48 89 ef             	mov    %rbp,%rdi
  401cda:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401cdf:	ba 01 00 00 00       	mov    $0x1,%edx
  401ce4:	be 64 00 00 00       	mov    $0x64,%esi
  401ce9:	e8 42 f3 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401cee:	4c 89 e6             	mov    %r12,%rsi
  401cf1:	48 89 ef             	mov    %rbp,%rdi
  401cf4:	e8 b7 f3 ff ff       	call   4010b0 <fputs@plt>
  401cf9:	48 89 d8             	mov    %rbx,%rax
  401cfc:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401d01:	48 89 ef             	mov    %rbp,%rdi
  401d04:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401d07:	41 b9 20 00 00 00    	mov    $0x20,%r9d
  401d0d:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401d12:	48 89 ef             	mov    %rbp,%rdi
  401d15:	4c 8d 05 56 15 00 00 	lea    0x1556(%rip),%r8        # 403272 <_IO_stdin_used+0x272>
  401d1c:	ba 01 00 00 00       	mov    $0x1,%edx
  401d21:	be 64 00 00 00       	mov    $0x64,%esi
  401d26:	e8 05 f3 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401d2b:	4c 89 e6             	mov    %r12,%rsi
  401d2e:	48 89 ef             	mov    %rbp,%rdi
  401d31:	e8 7a f3 ff ff       	call   4010b0 <fputs@plt>
  401d36:	48 89 d8             	mov    %rbx,%rax
  401d39:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401d3e:	48 89 ef             	mov    %rbp,%rdi
  401d41:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401d44:	45 31 c9             	xor    %r9d,%r9d
  401d47:	4c 8d 05 38 15 00 00 	lea    0x1538(%rip),%r8        # 403286 <_IO_stdin_used+0x286>
  401d4e:	48 89 ef             	mov    %rbp,%rdi
  401d51:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401d56:	ba 01 00 00 00       	mov    $0x1,%edx
  401d5b:	be 64 00 00 00       	mov    $0x64,%esi
  401d60:	e8 cb f2 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401d65:	48 89 ef             	mov    %rbp,%rdi
  401d68:	4c 89 e6             	mov    %r12,%rsi
  401d6b:	e8 40 f3 ff ff       	call   4010b0 <fputs@plt>
memset(buf, 0, 1000);
  snprintf(buf, 100, "scheduler.rsp %ld\n", offsetof(struct Scheduler, rsp));
  fprintf(out_file, "%s", buf);
  
  
  fclose(out_file);
  401d70:	4c 89 e7             	mov    %r12,%rdi
  401d73:	e8 f8 f2 ff ff       	call   401070 <fclose@plt>
  401d78:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
  401d80:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401d89:	0f 85 63 01 00 00    	jne    401ef2 <main+0xdc2>
  401d8f:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
  401d96:	31 c0                	xor    %eax,%eax
  401d98:	5b                   	pop    %rbx
  401d99:	5d                   	pop    %rbp
  401d9a:	41 5c                	pop    %r12
  401d9c:	41 5d                	pop    %r13
  401d9e:	41 5e                	pop    %r14
  401da0:	41 5f                	pop    %r15
  401da2:	c3                   	ret
  401da3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401da8:	4c 89 e8             	mov    %r13,%rax
  401dab:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401db0:	48 89 ef             	mov    %rbp,%rdi
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401db3:	ba 01 00 00 00       	mov    $0x1,%edx
  401db8:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  401dbb:	4c 8d 05 6b 14 00 00 	lea    0x146b(%rip),%r8        # 40322d <_IO_stdin_used+0x22d>
  401dc2:	48 89 ef             	mov    %rbp,%rdi
       for (int y = 0; y < data[x].accesssize; y++) {
  401dc5:	83 c3 01             	add    $0x1,%ebx
  401dc8:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401dcd:	8b 46 08             	mov    0x8(%rsi),%eax
  401dd0:	50                   	push   %rax
  401dd1:	8b 46 04             	mov    0x4(%rsi),%eax
  401dd4:	50                   	push   %rax
  401dd5:	44 8b 0e             	mov    (%rsi),%r9d
  401dd8:	31 c0                	xor    %eax,%eax
  401dda:	be 64 00 00 00       	mov    $0x64,%esi
  401ddf:	e8 4c f2 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401de4:	4c 89 e6             	mov    %r12,%rsi
  401de7:	48 89 ef             	mov    %rbp,%rdi
  401dea:	e8 c1 f2 ff ff       	call   4010b0 <fputs@plt>
  401def:	41 8b 56 18          	mov    0x18(%r14),%edx
  401df3:	58                   	pop    %rax
  401df4:	59                   	pop    %rcx
  401df5:	39 d3                	cmp    %edx,%ebx
  401df7:	0f 8c 52 fd ff ff    	jl     401b4f <main+0xa1f>
     for (int x = 0; x < threadsize; x++) {
  401dfd:	49 81 c6 00 04 00 00 	add    $0x400,%r14
  401e04:	4d 39 f7             	cmp    %r14,%r15
  401e07:	0f 85 13 fd ff ff    	jne    401b20 <main+0x9f0>
  401e0d:	e9 69 fd ff ff       	jmp    401b7b <main+0xa4b>
  401e12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  401e18:	48 89 d8             	mov    %rbx,%rax
  401e1b:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401e20:	48 89 ef             	mov    %rbp,%rdi
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401e23:	be 64 00 00 00       	mov    $0x64,%esi
  401e28:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  401e2b:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401e30:	48 89 ef             	mov    %rbp,%rdi
    for (int y = 0; y < data[x].epochssize; y++) {
  401e33:	41 83 c7 01          	add    $0x1,%r15d
  401e37:	4c 8d 05 b7 13 00 00 	lea    0x13b7(%rip),%r8        # 4031f5 <_IO_stdin_used+0x1f5>
  401e3e:	8b 42 28             	mov    0x28(%rdx),%eax
  401e41:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
  401e45:	50                   	push   %rax
  401e46:	8b 02                	mov    (%rdx),%eax
  401e48:	50                   	push   %rax
  401e49:	8b 42 2c             	mov    0x2c(%rdx),%eax
  401e4c:	ff 72 18             	push   0x18(%rdx)
  401e4f:	50                   	push   %rax
  401e50:	8b 42 20             	mov    0x20(%rdx),%eax
  401e53:	50                   	push   %rax
  401e54:	31 c0                	xor    %eax,%eax
  401e56:	ff 72 10             	push   0x10(%rdx)
  401e59:	ba 01 00 00 00       	mov    $0x1,%edx
  401e5e:	e8 cd f1 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401e63:	48 83 c4 30          	add    $0x30,%rsp
  401e67:	4c 89 e6             	mov    %r12,%rsi
  401e6a:	48 89 ef             	mov    %rbp,%rdi
  401e6d:	e8 3e f2 ff ff       	call   4010b0 <fputs@plt>
  401e72:	41 8b 0e             	mov    (%r14),%ecx
  401e75:	41 39 cf             	cmp    %ecx,%r15d
  401e78:	0f 8c f4 fb ff ff    	jl     401a72 <main+0x942>
  for (int x = 0; x < threadsize; x++) {
  401e7e:	49 81 c6 00 04 00 00 	add    $0x400,%r14
  401e85:	4d 39 f5             	cmp    %r14,%r13
  401e88:	0f 85 da fb ff ff    	jne    401a68 <main+0x938>
  401e8e:	e9 10 fc ff ff       	jmp    401aa3 <main+0x973>
  401e93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401e98:	4c 89 e8             	mov    %r13,%rax
  401e9b:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401ea0:	48 89 ef             	mov    %rbp,%rdi
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401ea3:	ba 01 00 00 00       	mov    $0x1,%edx
  401ea8:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  401eab:	4c 8d 05 6f 13 00 00 	lea    0x136f(%rip),%r8        # 403221 <_IO_stdin_used+0x221>
  401eb2:	48 89 ef             	mov    %rbp,%rdi
    for (int y = 0; y < data[x].accesssize; y++) {
  401eb5:	83 c3 01             	add    $0x1,%ebx
  401eb8:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401ebd:	8b 46 08             	mov    0x8(%rsi),%eax
  401ec0:	50                   	push   %rax
  401ec1:	8b 46 04             	mov    0x4(%rsi),%eax
  401ec4:	50                   	push   %rax
  401ec5:	44 8b 0e             	mov    (%rsi),%r9d
  401ec8:	31 c0                	xor    %eax,%eax
  401eca:	be 64 00 00 00       	mov    $0x64,%esi
  401ecf:	e8 5c f1 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401ed4:	4c 89 e6             	mov    %r12,%rsi
  401ed7:	48 89 ef             	mov    %rbp,%rdi
  401eda:	e8 d1 f1 ff ff       	call   4010b0 <fputs@plt>
  401edf:	41 8b 56 18          	mov    0x18(%r14),%edx
  401ee3:	5e                   	pop    %rsi
  401ee4:	5f                   	pop    %rdi
  401ee5:	39 d3                	cmp    %edx,%ebx
  401ee7:	0f 8c 3d fc ff ff    	jl     401b2a <main+0x9fa>
  401eed:	e9 57 fc ff ff       	jmp    401b49 <main+0xa19>
  401ef2:	e8 89 f1 ff ff       	call   401080 <__stack_chk_fail@plt>
  401ef7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000401f00 <set_fast_math>:
  401f00:	f3 0f 1e fa          	endbr64
  401f04:	0f ae 5c 24 fc       	stmxcsr -0x4(%rsp)
  401f09:	81 4c 24 fc 40 80 00 00 	orl    $0x8040,-0x4(%rsp)
  401f11:	0f ae 54 24 fc       	ldmxcsr -0x4(%rsp)
  401f16:	c3                   	ret
  401f17:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000401f20 <_start>:
  401f20:	f3 0f 1e fa          	endbr64
  401f24:	31 ed                	xor    %ebp,%ebp
  401f26:	49 89 d1             	mov    %rdx,%r9
  401f29:	5e                   	pop    %rsi
  401f2a:	48 89 e2             	mov    %rsp,%rdx
  401f2d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401f31:	50                   	push   %rax
  401f32:	54                   	push   %rsp
  401f33:	45 31 c0             	xor    %r8d,%r8d
  401f36:	31 c9                	xor    %ecx,%ecx
  401f38:	48 c7 c7 30 11 40 00 	mov    $0x401130,%rdi
  401f3f:	ff 15 a3 30 00 00    	call   *0x30a3(%rip)        # 404fe8 <__libc_start_main@GLIBC_2.34>
  401f45:	f4                   	hlt
  401f46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401f50 <_dl_relocate_static_pie>:
  401f50:	f3 0f 1e fa          	endbr64
  401f54:	c3                   	ret
  401f55:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401f5f:	90                   	nop

0000000000401f60 <deregister_tm_clones>:
  401f60:	b8 10 50 40 00       	mov    $0x405010,%eax
  401f65:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  401f6b:	74 13                	je     401f80 <deregister_tm_clones+0x20>
  401f6d:	b8 00 00 00 00       	mov    $0x0,%eax
  401f72:	48 85 c0             	test   %rax,%rax
  401f75:	74 09                	je     401f80 <deregister_tm_clones+0x20>
  401f77:	bf 10 50 40 00       	mov    $0x405010,%edi
  401f7c:	ff e0                	jmp    *%rax
  401f7e:	66 90                	xchg   %ax,%ax
  401f80:	c3                   	ret
  401f81:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401f8c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401f90 <register_tm_clones>:
  401f90:	be 10 50 40 00       	mov    $0x405010,%esi
  401f95:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  401f9c:	48 89 f0             	mov    %rsi,%rax
  401f9f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401fa3:	48 c1 f8 03          	sar    $0x3,%rax
  401fa7:	48 01 c6             	add    %rax,%rsi
  401faa:	48 d1 fe             	sar    %rsi
  401fad:	74 11                	je     401fc0 <register_tm_clones+0x30>
  401faf:	b8 00 00 00 00       	mov    $0x0,%eax
  401fb4:	48 85 c0             	test   %rax,%rax
  401fb7:	74 07                	je     401fc0 <register_tm_clones+0x30>
  401fb9:	bf 10 50 40 00       	mov    $0x405010,%edi
  401fbe:	ff e0                	jmp    *%rax
  401fc0:	c3                   	ret
  401fc1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401fcc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401fd0 <__do_global_dtors_aux>:
  401fd0:	f3 0f 1e fa          	endbr64
  401fd4:	80 3d 35 30 00 00 00 	cmpb   $0x0,0x3035(%rip)        # 405010 <__TMC_END__>
  401fdb:	75 13                	jne    401ff0 <__do_global_dtors_aux+0x20>
  401fdd:	55                   	push   %rbp
  401fde:	48 89 e5             	mov    %rsp,%rbp
  401fe1:	e8 7a ff ff ff       	call   401f60 <deregister_tm_clones>
  401fe6:	c6 05 23 30 00 00 01 	movb   $0x1,0x3023(%rip)        # 405010 <__TMC_END__>
  401fed:	5d                   	pop    %rbp
  401fee:	c3                   	ret
  401fef:	90                   	nop
  401ff0:	c3                   	ret
  401ff1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401ffc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000402000 <frame_dummy>:
  402000:	f3 0f 1e fa          	endbr64
  402004:	eb 8a                	jmp    401f90 <register_tm_clones>
  402006:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000402010 <coroutine_func>:
   coroutine->eip = &&resume;
  402010:	48 8d 15 f9 ff ff ff 	lea    -0x7(%rip),%rdx        # 402010 <coroutine_func>
uint64_t coroutine_func(void) {
  402017:	53                   	push   %rbx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  402018:	bf 01 00 00 00       	mov    $0x1,%edi
  40201d:	48 8d 35 e0 0f 00 00 	lea    0xfe0(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  asm ("movq %%rsi, %0" : "=r" (coroutine)::);
  402024:	48 89 f0             	mov    %rsi,%rax
   coroutine->eip = &&resume;
  402027:	48 89 50 10          	mov    %rdx,0x10(%rax)
  40202b:	31 c0                	xor    %eax,%eax
  asm("movq %%rdi, %0" : "=r" (scheduler));
  40202d:	48 89 fb             	mov    %rdi,%rbx
  402030:	48 8b 0b             	mov    (%rbx),%rcx
  402033:	48 89 da             	mov    %rbx,%rdx
  402036:	e8 a5 f0 ff ff       	call   4010e0 <__printf_chk@plt>
  return scheduler->rsp;
  40203b:	48 8b 03             	mov    (%rbx),%rax
}    
  40203e:	5b                   	pop    %rbx
  40203f:	c3                   	ret

0000000000402040 <yield>:
}
  402040:	c3                   	ret
  402041:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40204c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000402050 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  402050:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  402054:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  402057:	7e 77                	jle    4020d0 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  402059:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  40205d:	55                   	push   %rbp
  40205e:	49 89 f2             	mov    %rsi,%r10
  402061:	49 89 d3             	mov    %rdx,%r11
  402064:	53                   	push   %rbx
  402065:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  402068:	48 8b 98 20 04 00 00 	mov    0x420(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  40206f:	b8 01 00 00 00       	mov    $0x1,%eax
  402074:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  402078:	48 63 d0             	movslq %eax,%rdx
  40207b:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  40207e:	85 d2                	test   %edx,%edx
  402080:	40 0f 94 c6          	sete   %sil
  402084:	f6 c2 04             	test   $0x4,%dl
  402087:	75 05                	jne    40208e <pollthreads+0x3e>
  402089:	40 84 f6             	test   %sil,%sil
  40208c:	74 0d                	je     40209b <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  40208e:	49 63 08             	movslq (%r8),%rcx
  402091:	8d 69 01             	lea    0x1(%rcx),%ebp
  402094:	41 89 28             	mov    %ebp,(%r8)
  402097:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  40209b:	83 e2 08             	and    $0x8,%edx
  40209e:	75 05                	jne    4020a5 <pollthreads+0x55>
  4020a0:	40 84 f6             	test   %sil,%sil
  4020a3:	74 1b                	je     4020c0 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  4020a5:	48 63 17             	movslq (%rdi),%rdx
  4020a8:	8d 4a 01             	lea    0x1(%rdx),%ecx
  4020ab:	89 0f                	mov    %ecx,(%rdi)
  4020ad:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  4020b1:	83 c0 01             	add    $0x1,%eax
  4020b4:	41 39 41 68          	cmp    %eax,0x68(%r9)
  4020b8:	7f be                	jg     402078 <pollthreads+0x28>
}
  4020ba:	31 c0                	xor    %eax,%eax
  4020bc:	5b                   	pop    %rbx
  4020bd:	5d                   	pop    %rbp
  4020be:	c3                   	ret
  4020bf:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  4020c0:	83 c0 01             	add    $0x1,%eax
  4020c3:	41 39 41 68          	cmp    %eax,0x68(%r9)
  4020c7:	7f af                	jg     402078 <pollthreads+0x28>
}
  4020c9:	31 c0                	xor    %eax,%eax
  4020cb:	5b                   	pop    %rbx
  4020cc:	5d                   	pop    %rbp
  4020cd:	c3                   	ret
  4020ce:	66 90                	xchg   %ax,%ax
  4020d0:	31 c0                	xor    %eax,%eax
  4020d2:	c3                   	ret
  4020d3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4020de:	66 90                	xchg   %ax,%ax

00000000004020e0 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  4020e0:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4020e3:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
      if (*availableidx == 0) {
  4020ea:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4020ed:	48 83 c7 01          	add    $0x1,%rdi
  4020f1:	48 85 ff             	test   %rdi,%rdi
  4020f4:	7e 66                	jle    40215c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  4020f6:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4020fd:	31 c9                	xor    %ecx,%ecx
  4020ff:	45 31 c9             	xor    %r9d,%r9d
  402102:	31 c0                	xor    %eax,%eax
  402104:	eb 18                	jmp    40211e <findavailable+0x3e>
  402106:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  402110:	83 c1 01             	add    $0x1,%ecx
  402113:	48 63 c1             	movslq %ecx,%rax
  402116:	49 89 c1             	mov    %rax,%r9
  402119:	48 39 f8             	cmp    %rdi,%rax
  40211c:	7d 3e                	jge    40215c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  40211e:	48 c1 e0 05          	shl    $0x5,%rax
  402122:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  402128:	75 e6                	jne    402110 <findavailable+0x30>
         available[*availableidx] = x;
  40212a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  40212d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  402131:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  402135:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  402138:	41 8b 43 68          	mov    0x68(%r11),%eax
  40213c:	01 c0                	add    %eax,%eax
  40213e:	41 39 c0             	cmp    %eax,%r8d
  402141:	74 19                	je     40215c <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  402143:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  40214a:	83 c1 01             	add    $0x1,%ecx
  40214d:	48 63 c1             	movslq %ecx,%rax
  402150:	48 83 c7 01          	add    $0x1,%rdi
  402154:	49 89 c1             	mov    %rax,%r9
  402157:	48 39 f8             	cmp    %rdi,%rax
  40215a:	7c c2                	jl     40211e <findavailable+0x3e>
      if (*availableidx == 0) {
  40215c:	31 c0                	xor    %eax,%eax
  40215e:	45 85 c0             	test   %r8d,%r8d
  402161:	0f 94 c0             	sete   %al
}
  402164:	c3                   	ret
  402165:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000402170 <singlewriter3>:
}
  402170:	c3                   	ret
  402171:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40217c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000402180 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  402180:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  402186:	85 c0                	test   %eax,%eax
  402188:	74 1e                	je     4021a8 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40218a:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  40218c:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40218d:	55                   	push   %rbp
  40218e:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  40218f:	8b 77 68             	mov    0x68(%rdi),%esi
  402192:	48 89 fb             	mov    %rdi,%rbx
  402195:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  402198:	f7 f9                	idiv   %ecx
  40219a:	85 d2                	test   %edx,%edx
  40219c:	74 12                	je     4021b0 <singlewriter2+0x30>
}
  40219e:	5b                   	pop    %rbx
  40219f:	5d                   	pop    %rbp
  4021a0:	41 5c                	pop    %r12
  4021a2:	c3                   	ret
  4021a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4021a8:	c3                   	ret
  4021a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct Data * thread = &data->threads[data->threadindex];
  4021b0:	48 63 6f 64          	movslq 0x64(%rdi),%rbp
  4021b4:	48 c1 e5 0a          	shl    $0xa,%rbp
  4021b8:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  4021bc:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4021c1:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  4021c8:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  4021cc:	49 c1 e4 04          	shl    $0x4,%r12
  4021d0:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  4021d7:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  4021dc:	e8 7f ee ff ff       	call   401060 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4021e1:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  4021e7:	83 c0 01             	add    $0x1,%eax
  4021ea:	99                   	cltd
  4021eb:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  4021f1:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4021f4:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  4021fa:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  4021fe:	48 8b 05 0b 11 00 00 	mov    0x110b(%rip),%rax        # 403310 <_IO_stdin_used+0x310>
  402205:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  40220a:	5b                   	pop    %rbx
  40220b:	5d                   	pop    %rbp
  40220c:	41 5c                	pop    %r12
  40220e:	c3                   	ret
  40220f:	90                   	nop

0000000000402210 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  402210:	41 55                	push   %r13
  402212:	49 89 d5             	mov    %rdx,%r13
  402215:	41 54                	push   %r12
  402217:	49 89 cc             	mov    %rcx,%r12
  40221a:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  40221b:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40221e:	48 89 fd             	mov    %rdi,%rbp
  402221:	53                   	push   %rbx
  402222:	48 89 f3             	mov    %rsi,%rbx
  402225:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  402229:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40222d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  402236:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  40223b:	31 c0                	xor    %eax,%eax
  int readers = 0;
  40223d:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  402245:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  40224b:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  402253:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  40225b:	83 c0 01             	add    $0x1,%eax
  40225e:	99                   	cltd
  40225f:	f7 7f 68             	idivl  0x68(%rdi)
  402262:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  402268:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  40226d:	4c 89 e9             	mov    %r13,%rcx
  402270:	e8 6b fe ff ff       	call   4020e0 <findavailable>
  if (fill == 1) {
  402275:	83 f8 01             	cmp    $0x1,%eax
  402278:	0f 84 3c 01 00 00    	je     4023ba <singlewriter+0x1aa>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  40227e:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  402283:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  402288:	4c 89 e2             	mov    %r12,%rdx
  40228b:	4c 89 ee             	mov    %r13,%rsi
  40228e:	48 89 ef             	mov    %rbp,%rdi
  402291:	e8 ba fd ff ff       	call   402050 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  402296:	4c 63 44 24 0c       	movslq 0xc(%rsp),%r8
  40229b:	45 85 c0             	test   %r8d,%r8d
  40229e:	0f 8e 3d 01 00 00    	jle    4023e1 <singlewriter+0x1d1>
  4022a4:	44 8b 4c 24 14       	mov    0x14(%rsp),%r9d
          if (assignedchunk == availableidx) {
  4022a9:	31 c9                	xor    %ecx,%ecx
  4022ab:	eb 58                	jmp    402305 <singlewriter+0xf5>
  4022ad:	0f 1f 00             	nopl   (%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  4022b0:	48 8b 04 cb          	mov    (%rbx,%rcx,8),%rax
          int thread = readyreaders[x];
  4022b4:	49 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%rdx
  4022b9:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  4022bc:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  4022c0:	48 c1 e0 05          	shl    $0x5,%rax
  4022c4:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
          int thread = readyreaders[x];
  4022cb:	48 89 d7             	mov    %rdx,%rdi
          data->threads[thread].reading = chunk;
  4022ce:	48 c1 e2 0a          	shl    $0xa,%rdx
          data->threads[thread].start = start;
  4022d2:	66 0f 6e 00          	movd   (%rax),%xmm0
  4022d6:	66 0f 6e 48 08       	movd   0x8(%rax),%xmm1
          chunk->available = READING;
  4022db:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
          data->threads[thread].reading = chunk;
  4022e2:	48 03 55 30          	add    0x30(%rbp),%rdx
          data->threads[thread].start = start;
  4022e6:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  4022ea:	48 89 82 a8 00 00 00 	mov    %rax,0xa8(%rdx)
          chunk->owner = thread;
  4022f1:	89 78 14             	mov    %edi,0x14(%rax)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  4022f4:	83 8a c8 00 00 00 10 	orl    $0x10,0xc8(%rdx)
          data->threads[thread].start = start;
  4022fb:	66 0f d6 42 14       	movq   %xmm0,0x14(%rdx)
        for (int x = 0; x < readers ; x++) {
  402300:	49 39 c8             	cmp    %rcx,%r8
  402303:	74 07                	je     40230c <singlewriter+0xfc>
  402305:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  402307:	4c 39 c9             	cmp    %r9,%rcx
  40230a:	75 a4                	jne    4022b0 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  40230c:	44 8b 4c 24 10       	mov    0x10(%rsp),%r9d
  402311:	45 85 c9             	test   %r9d,%r9d
  402314:	7e 68                	jle    40237e <singlewriter+0x16e>
                if (assignedchunk  == availableidx) {
  402316:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
  40231b:	41 01 f1             	add    %esi,%r9d
  40231e:	eb 59                	jmp    402379 <singlewriter+0x169>
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  402320:	8d 7e 01             	lea    0x1(%rsi),%edi
  402323:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  402326:	49 63 14 24          	movslq (%r12),%rdx
   for (int x = 0; x < writers ; x++) {
  40232a:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  40232e:	48 8b 04 f3          	mov    (%rbx,%rsi,8),%rax
          int thread = readywriters[x];
  402332:	48 89 d1             	mov    %rdx,%rcx
          data->threads[thread].writing = chunk;
  402335:	48 c1 e2 0a          	shl    $0xa,%rdx
  402339:	48 03 55 30          	add    0x30(%rbp),%rdx
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  40233d:	48 c1 e0 05          	shl    $0x5,%rax
  402341:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
          data->threads[thread].publishstart = start;
  402348:	66 0f 6e 00          	movd   (%rax),%xmm0
  40234c:	66 0f 6e 50 08       	movd   0x8(%rax),%xmm2
      chunk->available = WRITING;
  402351:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
          data->threads[thread].writing = chunk;
  402358:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
          data->threads[thread].publishstart = start;
  40235f:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          chunk->owner = thread;
  402363:	89 48 14             	mov    %ecx,0x14(%rax)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  402366:	83 8a c8 00 00 00 20 	orl    $0x20,0xc8(%rdx)
          data->threads[thread].publishstart = start;
  40236d:	66 0f d6 42 40       	movq   %xmm0,0x40(%rdx)
   for (int x = 0; x < writers ; x++) {
  402372:	44 39 cf             	cmp    %r9d,%edi
  402375:	74 07                	je     40237e <singlewriter+0x16e>
  402377:	89 fe                	mov    %edi,%esi
                if (assignedchunk  == availableidx) {
  402379:	41 39 f0             	cmp    %esi,%r8d
  40237c:	75 a2                	jne    402320 <singlewriter+0x110>
      for (int x = 0; x < data->threadsize ; x++) {
  40237e:	8b 7d 68             	mov    0x68(%rbp),%edi
  402381:	85 ff                	test   %edi,%edi
  402383:	7e 33                	jle    4023b8 <singlewriter+0x1a8>
        if (data->threads[x].newmask != 0) {
  402385:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  402389:	31 d2                	xor    %edx,%edx
  40238b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  402390:	48 63 ca             	movslq %edx,%rcx
  402393:	48 89 c8             	mov    %rcx,%rax
  402396:	48 c1 e0 0a          	shl    $0xa,%rax
  40239a:	4c 01 c0             	add    %r8,%rax
  40239d:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  4023a3:	85 f6                	test   %esi,%esi
  4023a5:	74 31                	je     4023d8 <singlewriter+0x1c8>
          data->threads[x].readies[x] = data->threads[x].newmask;
  4023a7:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  4023ab:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  4023ae:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  4023b1:	8b 7d 68             	mov    0x68(%rbp),%edi
  4023b4:	39 fa                	cmp    %edi,%edx
  4023b6:	7c d8                	jl     402390 <singlewriter+0x180>
  return 0;
  4023b8:	31 c0                	xor    %eax,%eax
}
  4023ba:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  4023bf:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  4023c8:	75 1e                	jne    4023e8 <singlewriter+0x1d8>
  4023ca:	48 83 c4 28          	add    $0x28,%rsp
  4023ce:	5b                   	pop    %rbx
  4023cf:	5d                   	pop    %rbp
  4023d0:	41 5c                	pop    %r12
  4023d2:	41 5d                	pop    %r13
  4023d4:	c3                   	ret
  4023d5:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  4023d8:	83 c2 01             	add    $0x1,%edx
  4023db:	39 fa                	cmp    %edi,%edx
  4023dd:	7c b1                	jl     402390 <singlewriter+0x180>
  4023df:	eb d7                	jmp    4023b8 <singlewriter+0x1a8>
      int assignedchunk = 0;
  4023e1:	31 f6                	xor    %esi,%esi
  4023e3:	e9 24 ff ff ff       	jmp    40230c <singlewriter+0xfc>
}
  4023e8:	e8 93 ec ff ff       	call   401080 <__stack_chk_fail@plt>
  4023ed:	0f 1f 00             	nopl   (%rax)

00000000004023f0 <threadwork>:
int * threadwork(struct Data * data) {
  4023f0:	41 57                	push   %r15
  4023f2:	41 56                	push   %r14
  4023f4:	41 55                	push   %r13
  4023f6:	41 54                	push   %r12
  4023f8:	55                   	push   %rbp
  4023f9:	53                   	push   %rbx
  4023fa:	48 89 fb             	mov    %rdi,%rbx
  4023fd:	48 83 ec 28          	sub    $0x28,%rsp
  int cursorlimit = data->threadsize;
  402401:	8b 6f 68             	mov    0x68(%rdi),%ebp
clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  402404:	bf 04 00 00 00       	mov    $0x4,%edi
int * threadwork(struct Data * data) {
  402409:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  402412:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  402417:	31 c0                	xor    %eax,%eax
clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  402419:	48 89 e6             	mov    %rsp,%rsi
  40241c:	e8 3f ec ff ff       	call   401060 <clock_gettime@plt>
  if (data->running == 2) {
  402421:	83 7b 5c 02          	cmpl   $0x2,0x5c(%rbx)
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  402425:	4c 63 cd             	movslq %ebp,%r9
  if (data->running == 2) {
  402428:	0f 84 e2 02 00 00    	je     402710 <threadwork+0x320>
  long thisgroup = data->main->globalwrite[data->mystream * 128] / epochsize;
  40242e:	48 8b 43 28          	mov    0x28(%rbx),%rax
  402432:	48 8b 88 80 03 00 00 	mov    0x380(%rax),%rcx
  402439:	8b 83 8c 03 00 00    	mov    0x38c(%rbx),%eax
  40243f:	c1 e0 07             	shl    $0x7,%eax
  402442:	48 98                	cltq
  402444:	48 8b 04 c1          	mov    (%rcx,%rax,8),%rax
  402448:	48 99                	cqto
  40244a:	49 f7 f9             	idiv   %r9
  40244d:	49 89 c6             	mov    %rax,%r14
  if (thisgroup != data->lastgroup) {
  402450:	48 63 83 88 03 00 00 	movslq 0x388(%rbx),%rax
  402457:	4c 39 f0             	cmp    %r14,%rax
  40245a:	74 7f                	je     4024db <threadwork+0xeb>
             struct Data * thread = &data->threads[data->threadindex];
  40245c:	4c 63 63 64          	movslq 0x64(%rbx),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  402460:	bf 04 00 00 00       	mov    $0x4,%edi
      data->writecursor = 0;
  402465:	c7 83 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rbx)
             struct Data * thread = &data->threads[data->threadindex];
  40246f:	49 c1 e4 0a          	shl    $0xa,%r12
  402473:	4c 03 63 30          	add    0x30(%rbx),%r12
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  402477:	49 63 84 24 24 03 00 00 	movslq 0x324(%r12),%rax
  40247f:	4c 8d 2c 40          	lea    (%rax,%rax,2),%r13
  402483:	49 c1 e5 04          	shl    $0x4,%r13
  402487:	4d 03 ac 24 18 03 00 00 	add    0x318(%r12),%r13
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  40248f:	49 8d 75 08          	lea    0x8(%r13),%rsi
  402493:	e8 c8 eb ff ff       	call   401060 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402498:	41 8b 84 24 24 03 00 00 	mov    0x324(%r12),%eax
  4024a0:	83 c0 01             	add    $0x1,%eax
  4024a3:	99                   	cltd
  4024a4:	41 f7 bc 24 20 03 00 00 	idivl  0x320(%r12)
        epoch->thread = data->threadindex;
  4024ac:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4024af:	41 89 94 24 24 03 00 00 	mov    %edx,0x324(%r12)
        epoch->thread = data->threadindex;
  4024b7:	41 89 45 00          	mov    %eax,0x0(%r13)
        epoch->stream = data->mystream;
  4024bb:	8b 83 8c 03 00 00    	mov    0x38c(%rbx),%eax
  4024c1:	41 89 45 2c          	mov    %eax,0x2c(%r13)
        epoch->kind = NEW_EPOCH;
  4024c5:	48 8b 05 44 0e 00 00 	mov    0xe44(%rip),%rax        # 403310 <_IO_stdin_used+0x310>
  4024cc:	49 89 45 20          	mov    %rax,0x20(%r13)
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  4024d0:	48 8b 43 28          	mov    0x28(%rbx),%rax
  4024d4:	48 8b 88 80 03 00 00 	mov    0x380(%rax),%rcx
  4024db:	48 63 83 90 03 00 00 	movslq 0x390(%rbx),%rax
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
  4024e2:	4c 8b a3 48 03 00 00 	mov    0x348(%rbx),%r12
   data->lastgroup = thisgroup;
  4024e9:	44 89 b3 88 03 00 00 	mov    %r14d,0x388(%rbx)
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  4024f0:	89 c2                	mov    %eax,%edx
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
  4024f2:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  4024f6:	c1 e2 07             	shl    $0x7,%edx
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
  4024f9:	49 63 04 84          	movslq (%r12,%rax,4),%rax
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  4024fd:	48 63 d2             	movslq %edx,%rdx
  402500:	48 8b 14 d1          	mov    (%rcx,%rdx,8),%rdx
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
  402504:	48 39 d0             	cmp    %rdx,%rax
  402507:	7c 09                	jl     402512 <threadwork+0x122>
  402509:	48 85 d2             	test   %rdx,%rdx
  40250c:	0f 85 d7 01 00 00    	jne    4026e9 <threadwork+0x2f9>
    for (int x = 0; x < data->threadsize; x++) {
  402512:	8b 43 68             	mov    0x68(%rbx),%eax
  402515:	85 c0                	test   %eax,%eax
  402517:	0f 8e cc 01 00 00    	jle    4026e9 <threadwork+0x2f9>
  40251d:	45 31 d2             	xor    %r10d,%r10d
      if (x == data->threadindex) {
  402520:	44 8b 4b 64          	mov    0x64(%rbx),%r9d
  402524:	45 39 d1             	cmp    %r10d,%r9d
  402527:	0f 84 af 01 00 00    	je     4026dc <threadwork+0x2ec>
   data->freq++;
  40252d:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
    access->stream = data->laststream;
  402532:	66 41 0f 6e d1       	movd   %r9d,%xmm2
        epoch->time = time;
  402537:	66 0f 6f 24 24       	movdqa (%rsp),%xmm4
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  40253c:	48 63 83 90 03 00 00 	movslq 0x390(%rbx),%rax
    struct Access * access = &data->reads[data->cread];
  402543:	4c 63 b3 b4 03 00 00 	movslq 0x3b4(%rbx),%r14
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  40254a:	4c 8d 1c 40          	lea    (%rax,%rax,2),%r11
  40254e:	48 89 c7             	mov    %rax,%rdi
    struct Access * access = &data->reads[data->cread];
  402551:	4f 8d 3c b6          	lea    (%r14,%r14,4),%r15
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  402555:	49 c1 e3 02          	shl    $0x2,%r11
    access->stream = data->laststream;
  402559:	66 0f 6e c7          	movd   %edi,%xmm0
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  40255d:	4f 8d 04 1c          	lea    (%r12,%r11,1),%r8
  402561:	41 8b 00             	mov    (%r8),%eax
  402564:	99                   	cltd
  402565:	f7 fd                	idiv   %ebp
  402567:	83 e8 01             	sub    $0x1,%eax
  40256a:	48 63 d0             	movslq %eax,%rdx
  40256d:	89 c1                	mov    %eax,%ecx
  40256f:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  402576:	c1 f9 1f             	sar    $0x1f,%ecx
  402579:	48 c1 ea 20          	shr    $0x20,%rdx
  40257d:	01 c2                	add    %eax,%edx
  40257f:	c1 fa 07             	sar    $0x7,%edx
  402582:	29 ca                	sub    %ecx,%edx
  402584:	89 d1                	mov    %edx,%ecx
  402586:	c1 e1 08             	shl    $0x8,%ecx
  402589:	29 d1                	sub    %edx,%ecx
  40258b:	29 c8                	sub    %ecx,%eax
    int cursor = data->globalread[data->laststream].cursor;
  40258d:	49 63 48 04          	movslq 0x4(%r8),%rcx
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  402591:	4c 63 e8             	movslq %eax,%r13
    int cursor = data->globalread[data->laststream].cursor;
  402594:	48 89 ce             	mov    %rcx,%rsi
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  402597:	48 69 c9 81 80 80 80 	imul   $0xffffffff80808081,%rcx,%rcx
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  40259e:	4c 89 ea             	mov    %r13,%rdx
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  4025a1:	89 f0                	mov    %esi,%eax
  4025a3:	c1 f8 1f             	sar    $0x1f,%eax
  4025a6:	48 c1 e9 20          	shr    $0x20,%rcx
  4025aa:	01 f1                	add    %esi,%ecx
  4025ac:	c1 f9 07             	sar    $0x7,%ecx
  4025af:	29 c1                	sub    %eax,%ecx
  4025b1:	89 c8                	mov    %ecx,%eax
  4025b3:	c1 e0 08             	shl    $0x8,%eax
  4025b6:	29 c8                	sub    %ecx,%eax
  4025b8:	89 f1                	mov    %esi,%ecx
  4025ba:	29 c1                	sub    %eax,%ecx
  4025bc:	31 c0                	xor    %eax,%eax
  4025be:	4d 85 ed             	test   %r13,%r13
  4025c1:	4c 0f 48 e8          	cmovs  %rax,%r13
  4025c5:	89 f8                	mov    %edi,%eax
    access->stream = data->laststream;
  4025c7:	66 0f 6e c9          	movd   %ecx,%xmm1
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  4025cb:	c1 e0 18             	shl    $0x18,%eax
    access->stream = data->laststream;
  4025ce:	66 0f 62 ca          	punpckldq %xmm2,%xmm1
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  4025d2:	09 c8                	or     %ecx,%eax
  4025d4:	49 c1 e5 10          	shl    $0x10,%r13
struct Data * thread = &data->threads[data->threadindex];
  4025d8:	49 63 c9             	movslq %r9d,%rcx
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  4025db:	48 98                	cltq
  4025dd:	49 09 c5             	or     %rax,%r13
    struct Access * access = &data->reads[data->cread];
  4025e0:	4c 89 f0             	mov    %r14,%rax
  4025e3:	4c 8b b3 a0 03 00 00 	mov    0x3a0(%rbx),%r14
  4025ea:	4f 8d 34 be          	lea    (%r14,%r15,4),%r14
    access->global = past;
  4025ee:	45 31 ff             	xor    %r15d,%r15d
  4025f1:	85 d2                	test   %edx,%edx
  4025f3:	41 0f 48 d7          	cmovs  %r15d,%edx
    data->cread = (data->cread + 1) % data->accesssize;
  4025f7:	83 c0 01             	add    $0x1,%eax
struct Data * thread = &data->threads[data->threadindex];
  4025fa:	48 c1 e1 0a          	shl    $0xa,%rcx
  4025fe:	48 03 4b 30          	add    0x30(%rbx),%rcx
    access->set = 1;
  402602:	41 c7 46 10 01 00 00 00 	movl   $0x1,0x10(%r14)
    access->stream = data->laststream;
  40260a:	66 0f 6e da          	movd   %edx,%xmm3
    data->cread = (data->cread + 1) % data->accesssize;
  40260e:	99                   	cltd
    access->stream = data->laststream;
  40260f:	66 0f 62 c3          	punpckldq %xmm3,%xmm0
  402613:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
  402617:	41 0f 11 06          	movups %xmm0,(%r14)
    data->cread = (data->cread + 1) % data->accesssize;
  40261b:	f7 bb b8 03 00 00    	idivl  0x3b8(%rbx)
  402621:	89 93 b4 03 00 00    	mov    %edx,0x3b4(%rbx)
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  402627:	48 63 91 24 03 00 00 	movslq 0x324(%rcx),%rdx
  40262e:	48 89 d0             	mov    %rdx,%rax
  402631:	4c 8d 34 52          	lea    (%rdx,%rdx,2),%r14
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402635:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  402638:	49 c1 e6 04          	shl    $0x4,%r14
  40263c:	4c 03 b1 18 03 00 00 	add    0x318(%rcx),%r14
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402643:	99                   	cltd
        epoch->time = time;
  402644:	41 0f 11 66 08       	movups %xmm4,0x8(%r14)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402649:	f7 b9 20 03 00 00    	idivl  0x320(%rcx)
        if (data->main->works[buffer] != -1) {
  40264f:	48 8b 43 28          	mov    0x28(%rbx),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402653:	89 91 24 03 00 00    	mov    %edx,0x324(%rcx)
  epoch->buffer = buffer;
  402659:	4d 89 6e 18          	mov    %r13,0x18(%r14)
        if (data->main->works[buffer] != -1) {
  40265d:	4c 03 68 70          	add    0x70(%rax),%r13
        epoch->thread = data->threadindex;
  402661:	45 89 0e             	mov    %r9d,(%r14)
  epoch->set = 1;
  402664:	41 c7 46 24 01 00 00 00 	movl   $0x1,0x24(%r14)
        if (data->main->works[buffer] != -1) {
  40266c:	41 80 7d 00 ff       	cmpb   $0xff,0x0(%r13)
  402671:	74 22                	je     402695 <threadwork+0x2a5>
          data->successreads++;
  402673:	48 83 83 98 03 00 00 01 	addq   $0x1,0x398(%rbx)
          data->main->works[buffer] = -1;
  40267b:	41 c6 45 00 ff       	movb   $0xff,0x0(%r13)
    if (data->globalread[thistream].cursor < cursorlimit) {
  402680:	4c 8b a3 48 03 00 00 	mov    0x348(%rbx),%r12
      data->laststream = (data->laststream + 1);
  402687:	8b bb 90 03 00 00    	mov    0x390(%rbx),%edi
    if (data->globalread[thistream].cursor < cursorlimit) {
  40268d:	4f 8d 04 1c          	lea    (%r12,%r11,1),%r8
  402691:	41 8b 70 04          	mov    0x4(%r8),%esi
  402695:	39 f5                	cmp    %esi,%ebp
  402697:	7e 0b                	jle    4026a4 <threadwork+0x2b4>
      data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1);
  402699:	83 c6 01             	add    $0x1,%esi
      data->globalread[thistream].global++;
  40269c:	41 83 00 01          	addl   $0x1,(%r8)
      data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1);
  4026a0:	41 89 70 04          	mov    %esi,0x4(%r8)
    if (data->globalread[thistream].cursor == cursorlimit) {
  4026a4:	39 f5                	cmp    %esi,%ebp
  4026a6:	75 11                	jne    4026b9 <threadwork+0x2c9>
      data->laststream = (data->laststream + 1);
  4026a8:	83 c7 01             	add    $0x1,%edi
  4026ab:	89 bb 90 03 00 00    	mov    %edi,0x390(%rbx)
data->globalread[thistream].cursor = 0;
  4026b1:	41 c7 40 04 00 00 00 00 	movl   $0x0,0x4(%r8)
    if (data->laststream == data->mystream) {
  4026b9:	39 bb 8c 03 00 00    	cmp    %edi,0x38c(%rbx)
  4026bf:	75 09                	jne    4026ca <threadwork+0x2da>
      data->laststream = data->laststream + 1;
  4026c1:	83 c7 01             	add    $0x1,%edi
  4026c4:	89 bb 90 03 00 00    	mov    %edi,0x390(%rbx)
    if (data->laststream == 5) {
  4026ca:	83 ff 05             	cmp    $0x5,%edi
  4026cd:	75 0a                	jne    4026d9 <threadwork+0x2e9>
       data->laststream = 1;
  4026cf:	c7 83 90 03 00 00 01 00 00 00 	movl   $0x1,0x390(%rbx)
    for (int x = 0; x < data->threadsize; x++) {
  4026d9:	8b 43 68             	mov    0x68(%rbx),%eax
  4026dc:	41 83 c2 01          	add    $0x1,%r10d
  4026e0:	41 39 c2             	cmp    %eax,%r10d
  4026e3:	0f 8c 37 fe ff ff    	jl     402520 <threadwork+0x130>
}
  4026e9:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  4026ee:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4026f7:	0f 85 cc 01 00 00    	jne    4028c9 <threadwork+0x4d9>
  4026fd:	48 83 c4 28          	add    $0x28,%rsp
  402701:	31 c0                	xor    %eax,%eax
  402703:	5b                   	pop    %rbx
  402704:	5d                   	pop    %rbp
  402705:	41 5c                	pop    %r12
  402707:	41 5d                	pop    %r13
  402709:	41 5e                	pop    %r14
  40270b:	41 5f                	pop    %r15
  40270d:	c3                   	ret
  40270e:	66 90                	xchg   %ax,%ax
   for (int x = 0 ; x < data->threadsize ; x++) {
  402710:	8b 53 68             	mov    0x68(%rbx),%edx
  402713:	85 d2                	test   %edx,%edx
  402715:	0f 8e a2 01 00 00    	jle    4028bd <threadwork+0x4cd>
  40271b:	4c 8b 43 28          	mov    0x28(%rbx),%r8
  40271f:	8b 8b 8c 03 00 00    	mov    0x38c(%rbx),%ecx
  402725:	31 ff                	xor    %edi,%edi
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  402727:	49 ba 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%r10
  402731:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  402738:	89 c8                	mov    %ecx,%eax
  40273a:	4d 8b 98 80 03 00 00 	mov    0x380(%r8),%r11
    if (data->threadindex == x) { continue; }
  402741:	8b 73 64             	mov    0x64(%rbx),%esi
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  402744:	c1 e0 07             	shl    $0x7,%eax
  402747:	48 98                	cltq
  402749:	49 8d 04 c3          	lea    (%r11,%rax,8),%rax
    if (data->threadindex == x) { continue; }
  40274d:	39 fe                	cmp    %edi,%esi
  40274f:	0f 84 45 01 00 00    	je     40289a <threadwork+0x4aa>
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  402755:	48 8b 00             	mov    (%rax),%rax
    access->stream = data->mystream;
  402758:	66 0f 6e c1          	movd   %ecx,%xmm0
  40275c:	66 0f 6e ee          	movd   %esi,%xmm5
        epoch->time = time;
  402760:	66 0f 6f 3c 24       	movdqa (%rsp),%xmm7
struct Access * access = &data->writes[data->cwrite]; 
  402765:	4c 63 ab b0 03 00 00 	movslq 0x3b0(%rbx),%r13
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  40276c:	48 99                	cqto
  40276e:	49 f7 f9             	idiv   %r9
struct Access * access = &data->writes[data->cwrite]; 
  402771:	4f 8d 74 ad 00       	lea    0x0(%r13,%r13,4),%r14
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  402776:	49 89 c3             	mov    %rax,%r11
  402779:	49 f7 ea             	imul   %r10
  40277c:	4c 89 d8             	mov    %r11,%rax
  40277f:	48 c1 f8 3f          	sar    $0x3f,%rax
  402783:	4c 01 da             	add    %r11,%rdx
  402786:	48 c1 fa 07          	sar    $0x7,%rdx
  40278a:	48 29 c2             	sub    %rax,%rdx
  40278d:	48 89 d0             	mov    %rdx,%rax
  402790:	48 c1 e0 08          	shl    $0x8,%rax
  402794:	48 29 d0             	sub    %rdx,%rax
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  402797:	48 63 93 80 01 00 00 	movslq 0x180(%rbx),%rdx
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  40279e:	49 29 c3             	sub    %rax,%r11
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  4027a1:	48 89 d0             	mov    %rdx,%rax
  4027a4:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
    access->stream = data->mystream;
  4027ab:	66 41 0f 6e f3       	movd   %r11d,%xmm6
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  4027b0:	41 89 c4             	mov    %eax,%r12d
    access->stream = data->mystream;
  4027b3:	66 0f 62 c6          	punpckldq %xmm6,%xmm0
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  4027b7:	41 c1 fc 1f          	sar    $0x1f,%r12d
  4027bb:	48 c1 ea 20          	shr    $0x20,%rdx
  4027bf:	01 c2                	add    %eax,%edx
  4027c1:	c1 fa 07             	sar    $0x7,%edx
  4027c4:	44 29 e2             	sub    %r12d,%edx
  4027c7:	41 89 d4             	mov    %edx,%r12d
  4027ca:	41 c1 e4 08          	shl    $0x8,%r12d
  4027ce:	41 29 d4             	sub    %edx,%r12d
  4027d1:	44 29 e0             	sub    %r12d,%eax
  4027d4:	45 89 dc             	mov    %r11d,%r12d
  4027d7:	89 c2                	mov    %eax,%edx
  4027d9:	89 c8                	mov    %ecx,%eax
  4027db:	41 c1 e4 10          	shl    $0x10,%r12d
  struct Data * thread = &data->threads[data->threadindex];
  4027df:	48 63 ce             	movslq %esi,%rcx
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  4027e2:	c1 e0 18             	shl    $0x18,%eax
    access->stream = data->mystream;
  4027e5:	66 0f 6e ca          	movd   %edx,%xmm1
  struct Data * thread = &data->threads[data->threadindex];
  4027e9:	48 c1 e1 0a          	shl    $0xa,%rcx
  4027ed:	48 03 4b 30          	add    0x30(%rbx),%rcx
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  4027f1:	09 d0                	or     %edx,%eax
    access->stream = data->mystream;
  4027f3:	66 0f 62 cd          	punpckldq %xmm5,%xmm1
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  4027f7:	41 09 c4             	or     %eax,%r12d
struct Access * access = &data->writes[data->cwrite]; 
  4027fa:	4c 89 e8             	mov    %r13,%rax
  4027fd:	4c 8b ab a8 03 00 00 	mov    0x3a8(%rbx),%r13
    access->stream = data->mystream;
  402804:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
    data->cwrite = (data->cwrite + 1) % data->accesssize;
  402808:	83 c0 01             	add    $0x1,%eax
struct Access * access = &data->writes[data->cwrite]; 
  40280b:	4f 8d 6c b5 00       	lea    0x0(%r13,%r14,4),%r13
    data->cwrite = (data->cwrite + 1) % data->accesssize;
  402810:	99                   	cltd
    access->stream = data->mystream;
  402811:	41 0f 11 45 00       	movups %xmm0,0x0(%r13)
    data->cwrite = (data->cwrite + 1) % data->accesssize;
  402816:	f7 bb b8 03 00 00    	idivl  0x3b8(%rbx)
    access->set = 1;
  40281c:	41 c7 45 10 01 00 00 00 	movl   $0x1,0x10(%r13)
    data->cwrite = (data->cwrite + 1) % data->accesssize;
  402824:	89 93 b0 03 00 00    	mov    %edx,0x3b0(%rbx)
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  40282a:	48 63 91 24 03 00 00 	movslq 0x324(%rcx),%rdx
  402831:	48 89 d0             	mov    %rdx,%rax
  402834:	4c 8d 1c 52          	lea    (%rdx,%rdx,2),%r11
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402838:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  40283b:	49 c1 e3 04          	shl    $0x4,%r11
  40283f:	4c 03 99 18 03 00 00 	add    0x318(%rcx),%r11
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402846:	99                   	cltd
        epoch->time = time;
  402847:	41 0f 11 7b 08       	movups %xmm7,0x8(%r11)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40284c:	f7 b9 20 03 00 00    	idivl  0x320(%rcx)
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  402852:	49 63 c4             	movslq %r12d,%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402855:	89 91 24 03 00 00    	mov    %edx,0x324(%rcx)
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  40285b:	49 89 43 18          	mov    %rax,0x18(%r11)
  if (data->main->works[buffer] != -1) {
  40285f:	49 03 40 70          	add    0x70(%r8),%rax
        epoch->thread = data->threadindex;
  402863:	41 89 33             	mov    %esi,(%r11)
  epoch->set = 1;
  402866:	41 c7 43 24 01 00 00 00 	movl   $0x1,0x24(%r11)
  if (data->main->works[buffer] != -1) {
  40286e:	80 38 ff             	cmpb   $0xff,(%rax)
  402871:	74 05                	je     402878 <threadwork+0x488>
    data->freq_writes++;
  402873:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
  data->main->works[buffer] = data->threadindex;
  402878:	40 88 30             	mov    %sil,(%rax)
    data->writecursor = (data->writecursor + 1) % cursorlimit;
  40287b:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
  402881:	4c 8b 43 28          	mov    0x28(%rbx),%r8
  402885:	8b 8b 8c 03 00 00    	mov    0x38c(%rbx),%ecx
  40288b:	83 c0 01             	add    $0x1,%eax
  40288e:	99                   	cltd
  40288f:	f7 fd                	idiv   %ebp
  402891:	89 93 80 01 00 00    	mov    %edx,0x180(%rbx)
   for (int x = 0 ; x < data->threadsize ; x++) {
  402897:	8b 53 68             	mov    0x68(%rbx),%edx
  40289a:	83 c7 01             	add    $0x1,%edi
  40289d:	39 d7                	cmp    %edx,%edi
  40289f:	0f 8c 93 fe ff ff    	jl     402738 <threadwork+0x348>
    __atomic_fetch_add(&data->main->globalwrite[data->mystream * 128], 1, __ATOMIC_RELAXED);
  4028a5:	c1 e1 07             	shl    $0x7,%ecx
  4028a8:	49 8b 80 80 03 00 00 	mov    0x380(%r8),%rax
  4028af:	48 63 c9             	movslq %ecx,%rcx
  4028b2:	f0 48 83 04 c8 01    	lock addq $0x1,(%rax,%rcx,8)
  4028b8:	e9 71 fb ff ff       	jmp    40242e <threadwork+0x3e>
  4028bd:	4c 8b 43 28          	mov    0x28(%rbx),%r8
  4028c1:	8b 8b 8c 03 00 00    	mov    0x38c(%rbx),%ecx
  4028c7:	eb dc                	jmp    4028a5 <threadwork+0x4b5>
}
  4028c9:	e8 b2 e7 ff ff       	call   401080 <__stack_chk_fail@plt>
  4028ce:	66 90                	xchg   %ax,%ax

00000000004028d0 <work>:
void * work(void * arg) {
  4028d0:	53                   	push   %rbx
  4028d1:	8b 57 64             	mov    0x64(%rdi),%edx
  4028d4:	48 89 fb             	mov    %rdi,%rbx
  4028d7:	48 8d 35 41 07 00 00 	lea    0x741(%rip),%rsi        # 40301f <_IO_stdin_used+0x1f>
  4028de:	bf 01 00 00 00       	mov    $0x1,%edi
  4028e3:	31 c0                	xor    %eax,%eax
  4028e5:	e8 f6 e7 ff ff       	call   4010e0 <__printf_chk@plt>
  while (data->running > 0)  {
  4028ea:	8b 53 5c             	mov    0x5c(%rbx),%edx
  4028ed:	85 d2                	test   %edx,%edx
  4028ef:	7e 16                	jle    402907 <work+0x37>
  4028f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      threadwork(data);
  4028f8:	48 89 df             	mov    %rbx,%rdi
  4028fb:	e8 f0 fa ff ff       	call   4023f0 <threadwork>
  while (data->running > 0)  {
  402900:	8b 43 5c             	mov    0x5c(%rbx),%eax
  402903:	85 c0                	test   %eax,%eax
  402905:	7f f1                	jg     4028f8 <work+0x28>
  402907:	8b 53 64             	mov    0x64(%rbx),%edx
  40290a:	48 8d 35 21 07 00 00 	lea    0x721(%rip),%rsi        # 403032 <_IO_stdin_used+0x32>
  402911:	bf 01 00 00 00       	mov    $0x1,%edi
  402916:	31 c0                	xor    %eax,%eax
  402918:	e8 c3 e7 ff ff       	call   4010e0 <__printf_chk@plt>
}
  40291d:	5b                   	pop    %rbx
  40291e:	c3                   	ret
  40291f:	90                   	nop

0000000000402920 <work2>:
  while (data->running == 1) {
  402920:	eb 0b                	jmp    40292d <work2+0xd>
  402922:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  402928:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  40292d:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  402931:	74 f5                	je     402928 <work2+0x8>
}
  402933:	c3                   	ret
  402934:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40293e:	66 90                	xchg   %ax,%ax

0000000000402940 <.MSG>:
  402940:	43                   	rex.XB
  402941:	4f 20 43 6f          	rex.WRXB and %r8b,0x6f(%r11)
  402945:	72 6f                	jb     4029b6 <.CURSTACK+0x4>
  402947:	75 74                	jne    4029bd <.CURSTACK+0xb>
  402949:	69 6e 65 53 74 72 75 	imul   $0x75727453,0x65(%rsi),%ebp
  402950:	63 74 20 25          	movsxd 0x25(%rax,%riz,1),%esi
  402954:	78 0a                	js     402960 <.EIP+0x9>
	...

0000000000402957 <.EIP>:
  402957:	43                   	rex.XB
  402958:	4f 20 45 49          	rex.WRXB and %r8b,0x49(%r13)
  40295c:	50                   	push   %rax
  40295d:	2e                   	cs
  40295e:	2e                   	cs
  40295f:	2e                   	cs
  402960:	20                   	.byte 0x20
  402961:	25                   	.byte 0x25
  402962:	78 0a                	js     40296e <.CODATA+0x9>
	...

0000000000402965 <.CODATA>:
  402965:	43                   	rex.XB
  402966:	4f 20 63 6f          	rex.WRXB and %r12b,0x6f(%r11)
  40296a:	64 61                	fs (bad)
  40296c:	74 61                	je     4029cf <.SCHED+0xc>
  40296e:	2e                   	cs
  40296f:	2e                   	cs
  402970:	2e                   	cs
  402971:	20                   	.byte 0x20
  402972:	25                   	.byte 0x25
  402973:	78 0a                	js     40297f <.INDEX+0x9>
	...

0000000000402976 <.INDEX>:
  402976:	43 6f                	rex.XB outsl %ds:(%rsi),(%dx)
  402978:	72 6f                	jb     4029e9 <switch_to+0x16>
  40297a:	75 74                	jne    4029f0 <switch_to+0x1d>
  40297c:	69 6e 65 20 69 6e 64 	imul   $0x646e6920,0x65(%rsi),%ebp
  402983:	65 78 2e             	gs js  4029b4 <.CURSTACK+0x2>
  402986:	2e                   	cs
  402987:	2e                   	cs
  402988:	20                   	.byte 0x20
  402989:	25                   	.byte 0x25
  40298a:	64 0a 00             	or     %fs:(%rax),%al

000000000040298d <.RET>:
  40298d:	52                   	push   %rdx
  40298e:	65 74 75             	gs je  402a06 <switch_to+0x33>
  402991:	72 6e                	jb     402a01 <switch_to+0x2e>
  402993:	65 64 53             	gs fs push %rbx
  402996:	74 61                	je     4029f9 <switch_to+0x26>
  402998:	63 6b 2e             	movsxd 0x2e(%rbx),%ebp
  40299b:	2e                   	cs
  40299c:	2e                   	cs
  40299d:	20                   	.byte 0x20
  40299e:	25                   	.byte 0x25
  40299f:	70 0a                	jo     4029ab <.STACK+0x9>
	...

00000000004029a2 <.STACK>:
  4029a2:	43                   	rex.XB
  4029a3:	4f 20 53 74          	rex.WRXB and %r10b,0x74(%r11)
  4029a7:	61                   	(bad)
  4029a8:	63 6b 2e             	movsxd 0x2e(%rbx),%ebp
  4029ab:	2e                   	cs
  4029ac:	2e                   	cs
  4029ad:	20                   	.byte 0x20
  4029ae:	25                   	.byte 0x25
  4029af:	70 0a                	jo     4029bb <.CURSTACK+0x9>
	...

00000000004029b2 <.CURSTACK>:
  4029b2:	53                   	push   %rbx
  4029b3:	61                   	(bad)
  4029b4:	76 65                	jbe    402a1b <switch_to+0x48>
  4029b6:	64 53                	fs push %rbx
  4029b8:	74 61                	je     402a1b <switch_to+0x48>
  4029ba:	63 6b 2e             	movsxd 0x2e(%rbx),%ebp
  4029bd:	2e                   	cs
  4029be:	20                   	.byte 0x20
  4029bf:	25                   	.byte 0x25
  4029c0:	70 0a                	jo     4029cc <.SCHED+0x9>
	...

00000000004029c3 <.SCHED>:
  4029c3:	53                   	push   %rbx
  4029c4:	63 68 65             	movsxd 0x65(%rax),%ebp
  4029c7:	64 75 6c             	fs jne 402a36 <switch_to+0x63>
  4029ca:	65 72 2e             	gs jb  4029fb <switch_to+0x28>
  4029cd:	2e                   	cs
  4029ce:	20                   	.byte 0x20
  4029cf:	25                   	.byte 0x25
  4029d0:	70 0a                	jo     4029dc <switch_to+0x9>
	...

00000000004029d3 <switch_to>:
	.text
	# switch_to(struct Coroutine * coroutines, int index, struct Scheduler * scheduler)
	# rdi, %rsi, %rdx, %rcx, %r8 and %r9
switch_to:
# popq %r11
pushq %rbp
  4029d3:	55                   	push   %rbp

movq %rsp, %rbp
  4029d4:	48 89 e5             	mov    %rsp,%rbp
subq $1024, %rsp
  4029d7:	48 81 ec 00 04 00 00 	sub    $0x400,%rsp



movq %rdi, -56(%rbp) # coroutine table
  4029de:	48 89 7d c8          	mov    %rdi,-0x38(%rbp)
movq %rsi, -8(%rbp) # index
  4029e2:	48 89 75 f8          	mov    %rsi,-0x8(%rbp)
movq %rdx, -16(%rbp) # scheduler
  4029e6:	48 89 55 f0          	mov    %rdx,-0x10(%rbp)


movq %rsi, %rax
  4029ea:	48 89 f0             	mov    %rsi,%rax
imul $32, %rax
  4029ed:	48 6b c0 20          	imul   $0x20,%rax,%rax
addq %rdi, %rax
  4029f1:	48 01 f8             	add    %rdi,%rax
mov %rax, %r11
  4029f4:	49 89 c3             	mov    %rax,%r11

mov %r11, %rax
  4029f7:	4c 89 d8             	mov    %r11,%rax
movq %rax, %r9
  4029fa:	49 89 c1             	mov    %rax,%r9
movq %r9, -24(%rbp) # coroutine object
  4029fd:	4c 89 4d e8          	mov    %r9,-0x18(%rbp)

movq %r11, %rax
  402a01:	4c 89 d8             	mov    %r11,%rax
leaq 8(%rax), %rax
  402a04:	48 8d 40 08          	lea    0x8(%rax),%rax
movq %rax, %r9
  402a08:	49 89 c1             	mov    %rax,%r9
movq %r9, -48(%rbp) # rsp
  402a0b:	4c 89 4d d0          	mov    %r9,-0x30(%rbp)

movq %r11, %rax
  402a0f:	4c 89 d8             	mov    %r11,%rax
leaq 16(%rax), %rax
  402a12:	48 8d 40 10          	lea    0x10(%rax),%rax
movq (%rax), %r9
  402a16:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -32(%rbp) # coroutine function
  402a19:	4c 89 4d e0          	mov    %r9,-0x20(%rbp)

movq %r11, %rax
  402a1d:	4c 89 d8             	mov    %r11,%rax
leaq 8(%rax), %rax
  402a20:	48 8d 40 08          	lea    0x8(%rax),%rax
movq (%rax), %r9
  402a24:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -64(%rbp) # coroutine stack
  402a27:	4c 89 4d c0          	mov    %r9,-0x40(%rbp)

movq %r11, %rax
  402a2b:	4c 89 d8             	mov    %r11,%rax
leaq 24(%rax), %rax # load from coroutine object data object
  402a2e:	48 8d 40 18          	lea    0x18(%rax),%rax
movq (%rax), %r9
  402a32:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -40(%rbp) # coroutine data object
  402a35:	4c 89 4d d8          	mov    %r9,-0x28(%rbp)
movq (%rax), %rcx
  402a39:	48 8b 08             	mov    (%rax),%rcx

movq -24(%rbp), %r11
  402a3c:	4c 8b 5d e8          	mov    -0x18(%rbp),%r11
#

leaq .INDEX(%rip), %rdi
  402a40:	48 8d 3d 2f ff ff ff 	lea    -0xd1(%rip),%rdi        # 402976 <.INDEX>
#call printf@plt
mov $0, %eax
  402a47:	b8 00 00 00 00       	mov    $0x0,%eax

#pushq %r11
leaq .MSG(%rip), %rdi
  402a4c:	48 8d 3d ed fe ff ff 	lea    -0x113(%rip),%rdi        # 402940 <.MSG>
movq %r11, %rsi
  402a53:	4c 89 de             	mov    %r11,%rsi
# call printf@plt
mov $0, %eax
  402a56:	b8 00 00 00 00       	mov    $0x0,%eax

leaq .SCHED(%rip), %rdi
  402a5b:	48 8d 3d 61 ff ff ff 	lea    -0x9f(%rip),%rdi        # 4029c3 <.SCHED>
movq -16(%rbp), %rsi
  402a62:	48 8b 75 f0          	mov    -0x10(%rbp),%rsi
call printf@plt
  402a66:	e8 25 e6 ff ff       	call   401090 <printf@plt>
mov $0, %eax
  402a6b:	b8 00 00 00 00       	mov    $0x0,%eax

#popq %r11

#pushq %r9
movq -32(%rbp), %r9
  402a70:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9

leaq .EIP(%rip), %rdi
  402a74:	48 8d 3d dc fe ff ff 	lea    -0x124(%rip),%rdi        # 402957 <.EIP>
movq %r9, %rsi
  402a7b:	4c 89 ce             	mov    %r9,%rsi
#call printf@plt
mov $0, %eax
  402a7e:	b8 00 00 00 00       	mov    $0x0,%eax
#popq %r9
# coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data

#pushq %r9
leaq .CODATA(%rip), %rdi
  402a83:	48 8d 3d db fe ff ff 	lea    -0x125(%rip),%rdi        # 402965 <.CODATA>
movq -40(%rbp), %rsi
  402a8a:	48 8b 75 d8          	mov    -0x28(%rbp),%rsi
#call printf@plt
mov $0, %eax
  402a8e:	b8 00 00 00 00       	mov    $0x0,%eax





movq -16(%rbp), %rax
  402a93:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
movq %rsp, 0(%rax)
  402a97:	48 89 20             	mov    %rsp,(%rax)

leaq .CURSTACK(%rip), %rdi
  402a9a:	48 8d 3d 11 ff ff ff 	lea    -0xef(%rip),%rdi        # 4029b2 <.CURSTACK>
movq 0(%rax), %rsi
  402aa1:	48 8b 30             	mov    (%rax),%rsi
call printf@plt
  402aa4:	e8 e7 e5 ff ff       	call   401090 <printf@plt>
mov $0, %eax
  402aa9:	b8 00 00 00 00       	mov    $0x0,%eax





leaq .STACK(%rip), %rdi
  402aae:	48 8d 3d ed fe ff ff 	lea    -0x113(%rip),%rdi        # 4029a2 <.STACK>
movq -64(%rbp), %rsi
  402ab5:	48 8b 75 c0          	mov    -0x40(%rbp),%rsi
call printf@plt
  402ab9:	e8 d2 e5 ff ff       	call   401090 <printf@plt>
mov $0, %eax
  402abe:	b8 00 00 00 00       	mov    $0x0,%eax

movq -64(%rbp), %rsp # set stack to coroutine
  402ac3:	48 8b 65 c0          	mov    -0x40(%rbp),%rsp

movq -32(%rbp), %r9
  402ac7:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9
leaq after(%rip), %r11
  402acb:	4c 8d 1d 0f 00 00 00 	lea    0xf(%rip),%r11        # 402ae1 <after>
#sub $8, %rsp
#movq %r11, (%rsp) # set stack return address

movq -16(%rbp), %rdi
  402ad2:	48 8b 7d f0          	mov    -0x10(%rbp),%rdi
movq -24(%rbp), %rsi
  402ad6:	48 8b 75 e8          	mov    -0x18(%rbp),%rsi
movq -40(%rbp), %rdx
  402ada:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx

# pushq %rbp
#jmp *%r9
call *%r9
  402ade:	41 ff d1             	call   *%r9

0000000000402ae1 <after>:
# pushq %rbp
# popq %rbp
#movq %rsp, %rbp

#pushq %rax
movq %rax, %rsp
  402ae1:	48 89 c4             	mov    %rax,%rsp
# movq %rsp, %rbp

leaq .RET(%rip), %rdi
  402ae4:	48 8d 3d a2 fe ff ff 	lea    -0x15e(%rip),%rdi        # 40298d <.RET>
movq %rax, %rsi
  402aeb:	48 89 c6             	mov    %rax,%rsi
call printf@plt
  402aee:	e8 9d e5 ff ff       	call   401090 <printf@plt>
mov $0, %eax
  402af3:	b8 00 00 00 00       	mov    $0x0,%eax




#pop %rbp
add $1024, %rsp
  402af8:	48 81 c4 00 04 00 00 	add    $0x400,%rsp
#movq %rsp, %rbp
popq %rbp
  402aff:	5d                   	pop    %rbp
  402b00:	c3                   	ret

Disassembly of section .fini:

0000000000402b04 <_fini>:
  402b04:	f3 0f 1e fa          	endbr64
  402b08:	48 83 ec 08          	sub    $0x8,%rsp
  402b0c:	48 83 c4 08          	add    $0x8,%rsp
  402b10:	c3                   	ret
