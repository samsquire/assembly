
bcast-workqueue:     file format elf64-x86-64


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
  401020:	ff 35 6a 2f 00 00    	push   0x2f6a(%rip)        # 403f90 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 6c 2f 00 00    	jmp    *0x2f6c(%rip)        # 403f98 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <pthread_setaffinity_np@plt>:
  401030:	ff 25 6a 2f 00 00    	jmp    *0x2f6a(%rip)        # 403fa0 <pthread_setaffinity_np@GLIBC_2.34>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <puts@plt>:
  401040:	ff 25 62 2f 00 00    	jmp    *0x2f62(%rip)        # 403fa8 <puts@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <clock_gettime@plt>:
  401050:	ff 25 5a 2f 00 00    	jmp    *0x2f5a(%rip)        # 403fb0 <clock_gettime@GLIBC_2.17>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <__stack_chk_fail@plt>:
  401060:	ff 25 52 2f 00 00    	jmp    *0x2f52(%rip)        # 403fb8 <__stack_chk_fail@GLIBC_2.4>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <nanosleep@plt>:
  401070:	ff 25 4a 2f 00 00    	jmp    *0x2f4a(%rip)        # 403fc0 <nanosleep@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <memset@plt>:
  401080:	ff 25 42 2f 00 00    	jmp    *0x2f42(%rip)        # 403fc8 <memset@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <calloc@plt>:
  401090:	ff 25 3a 2f 00 00    	jmp    *0x2f3a(%rip)        # 403fd0 <calloc@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <__printf_chk@plt>:
  4010a0:	ff 25 32 2f 00 00    	jmp    *0x2f32(%rip)        # 403fd8 <__printf_chk@GLIBC_2.3.4>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <pthread_create@plt>:
  4010b0:	ff 25 2a 2f 00 00    	jmp    *0x2f2a(%rip)        # 403fe0 <pthread_create@GLIBC_2.34>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <pthread_join@plt>:
  4010c0:	ff 25 22 2f 00 00    	jmp    *0x2f22(%rip)        # 403fe8 <pthread_join@GLIBC_2.34>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

00000000004010d0 <main>:
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
}

int main(int argc, char **argv) {
  4010d0:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4010d2:	ba 08 00 00 00       	mov    $0x8,%edx
  4010d7:	bf 01 00 00 00       	mov    $0x1,%edi
  4010dc:	48 8d 35 44 0f 00 00 	lea    0xf44(%rip),%rsi        # 402027 <_IO_stdin_used+0x27>
  4010e3:	41 56                	push   %r14
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  data[0].works = works;
  4010e5:	41 be 01 00 00 00    	mov    $0x1,%r14d
int main(int argc, char **argv) {
  4010eb:	41 55                	push   %r13
  4010ed:	41 54                	push   %r12
  char *works = calloc(worksize, sizeof(char));
  4010ef:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
int main(int argc, char **argv) {
  4010f5:	55                   	push   %rbp
  4010f6:	53                   	push   %rbx
  4010f7:	48 83 ec 68          	sub    $0x68,%rsp
  4010fb:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401104:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  401109:	31 c0                	xor    %eax,%eax
  40110b:	e8 90 ff ff ff       	call   4010a0 <__printf_chk@plt>
  401110:	ba 04 00 00 00       	mov    $0x4,%edx
  401115:	48 8d 35 1d 0f 00 00 	lea    0xf1d(%rip),%rsi        # 402039 <_IO_stdin_used+0x39>
  40111c:	31 c0                	xor    %eax,%eax
  40111e:	bf 01 00 00 00       	mov    $0x1,%edi
  401123:	e8 78 ff ff ff       	call   4010a0 <__printf_chk@plt>
  401128:	ba 20 00 00 00       	mov    $0x20,%edx
  40112d:	48 8d 35 01 0f 00 00 	lea    0xf01(%rip),%rsi        # 402035 <_IO_stdin_used+0x35>
  401134:	31 c0                	xor    %eax,%eax
  401136:	bf 01 00 00 00       	mov    $0x1,%edi
  40113b:	e8 60 ff ff ff       	call   4010a0 <__printf_chk@plt>
  401140:	ba 04 00 00 00       	mov    $0x4,%edx
  401145:	48 8d 35 fc 0e 00 00 	lea    0xefc(%rip),%rsi        # 402048 <_IO_stdin_used+0x48>
  40114c:	31 c0                	xor    %eax,%eax
  40114e:	bf 01 00 00 00       	mov    $0x1,%edi
  401153:	e8 48 ff ff ff       	call   4010a0 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401158:	be 08 00 00 00       	mov    $0x8,%esi
  40115d:	bf 04 00 00 00       	mov    $0x4,%edi
  401162:	e8 29 ff ff ff       	call   401090 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401167:	be 38 00 00 00       	mov    $0x38,%esi
  40116c:	bf 04 00 00 00       	mov    $0x4,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401171:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401176:	e8 15 ff ff ff       	call   401090 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40117b:	be 00 0e 00 00       	mov    $0xe00,%esi
  401180:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401185:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40118a:	e8 01 ff ff ff       	call   401090 <calloc@plt>
  char *works = calloc(worksize, sizeof(char));
  40118f:	be 01 00 00 00       	mov    $0x1,%esi
  401194:	4c 89 e7             	mov    %r12,%rdi
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401197:	48 89 c3             	mov    %rax,%rbx
  char *works = calloc(worksize, sizeof(char));
  40119a:	e8 f1 fe ff ff       	call   401090 <calloc@plt>
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  40119f:	4c 89 e2             	mov    %r12,%rdx
  4011a2:	be ff ff ff ff       	mov    $0xffffffff,%esi
  data[0].works = works;
  4011a7:	49 89 df             	mov    %rbx,%r15
  4011aa:	48 89 c7             	mov    %rax,%rdi
  char *works = calloc(worksize, sizeof(char));
  4011ad:	48 89 c5             	mov    %rax,%rbp
  4011b0:	e8 cb fe ff ff       	call   401080 <memset@plt>
  4011b5:	4c 89 e2             	mov    %r12,%rdx
  4011b8:	bf 01 00 00 00       	mov    $0x1,%edi
  4011bd:	31 c0                	xor    %eax,%eax
  4011bf:	48 8d 35 97 0e 00 00 	lea    0xe97(%rip),%rsi        # 40205d <_IO_stdin_used+0x5d>
  4011c6:	e8 d5 fe ff ff       	call   4010a0 <__printf_chk@plt>
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4011cb:	be 20 00 00 00       	mov    $0x20,%esi
  4011d0:	bf 64 00 00 00       	mov    $0x64,%edi
  4011d5:	e8 b6 fe ff ff       	call   401090 <calloc@plt>
  4011da:	31 d2                	xor    %edx,%edx
  4011dc:	bf 01 00 00 00       	mov    $0x1,%edi
  4011e1:	48 8d 35 86 0e 00 00 	lea    0xe86(%rip),%rsi        # 40206e <_IO_stdin_used+0x6e>
  4011e8:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  4011ed:	31 c0                	xor    %eax,%eax
  4011ef:	e8 ac fe ff ff       	call   4010a0 <__printf_chk@plt>
  4011f4:	4c 89 e2             	mov    %r12,%rdx
  4011f7:	bf 01 00 00 00       	mov    $0x1,%edi
  4011fc:	31 c0                	xor    %eax,%eax
  4011fe:	48 8d 35 75 0e 00 00 	lea    0xe75(%rip),%rsi        # 40207a <_IO_stdin_used+0x7a>
  401205:	e8 96 fe ff ff       	call   4010a0 <__printf_chk@plt>
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  40120a:	be 04 00 00 00       	mov    $0x4,%esi
  40120f:	bf 04 00 00 00       	mov    $0x4,%edi
  401214:	e8 77 fe ff ff       	call   401090 <calloc@plt>
  data[0].works = works;
  401219:	48 89 6b 70          	mov    %rbp,0x70(%rbx)
  40121d:	31 ed                	xor    %ebp,%ebp
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  40121f:	49 89 c5             	mov    %rax,%r13
  for (int x = 0; x < threadsize ; x++) {
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401222:	be 80 00 00 00       	mov    $0x80,%esi
  401227:	bf 01 00 00 00       	mov    $0x1,%edi
  40122c:	44 89 34 24          	mov    %r14d,(%rsp)
  401230:	45 8d 66 ff          	lea    -0x1(%r14),%r12d
  401234:	e8 57 fe ff ff       	call   401090 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  401239:	44 89 f1             	mov    %r14d,%ecx
  40123c:	ba 01 00 00 00       	mov    $0x1,%edx
  401241:	48 8d 35 40 0f 00 00 	lea    0xf40(%rip),%rsi        # 402188 <_IO_stdin_used+0x188>
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401248:	49 89 47 78          	mov    %rax,0x78(%r15)
    CPU_SET(cpu += 1, data[x].cpu_set);
  40124c:	48 d3 e2             	shl    %cl,%rdx
  40124f:	8b 0c 24             	mov    (%rsp),%ecx
  401252:	bf 01 00 00 00       	mov    $0x1,%edi
  401257:	48 09 10             	or     %rdx,(%rax)
  40125a:	44 89 e2             	mov    %r12d,%edx
  40125d:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  40125f:	49 81 c7 80 03 00 00 	add    $0x380,%r15
  401266:	e8 35 fe ff ff       	call   4010a0 <__printf_chk@plt>
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].bucketstart = x * buckets ;
    data[x].loglevel = debug;
    data[x].running = 1;
  40126b:	48 8b 05 66 0f 00 00 	mov    0xf66(%rip),%rax        # 4021d8 <_IO_stdin_used+0x1d8>
    data[x].bucketstart = x * buckets ;
  401272:	41 89 af 18 fd ff ff 	mov    %ebp,-0x2e8(%r15)
    data[x].newmask = 0;
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401279:	be 30 00 00 00       	mov    $0x30,%esi
    data[x].read = 0;
  40127e:	66 0f 6f 0d 5a 0f 00 00 	movdqa 0xf5a(%rip),%xmm1        # 4021e0 <_IO_stdin_used+0x1e0>
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401286:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].chunkslen = chunkslen;
  40128b:	66 0f 6f 15 5d 0f 00 00 	movdqa 0xf5d(%rip),%xmm2        # 4021f0 <_IO_stdin_used+0x1f0>
    data[x].loglevel = debug;
  401293:	41 c7 87 00 fd ff ff 00 00 00 00 	movl   $0x0,-0x300(%r15)
    data[x].running = 1;
  40129e:	49 89 87 dc fc ff ff 	mov    %rax,-0x324(%r15)
    data[x].freelist = freelist;
  4012a5:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  for (int x = 0; x < threadsize ; x++) {
  4012aa:	81 c5 ff ff ff 3f    	add    $0x3fffffff,%ebp
    data[x].prevread = threadsize;
  4012b0:	66 0f 6f 1d 48 0f 00 00 	movdqa 0xf48(%rip),%xmm3        # 402200 <_IO_stdin_used+0x200>
    data[x].threadindex = x;
  4012b8:	45 89 a7 e4 fc ff ff 	mov    %r12d,-0x31c(%r15)
    data[x].availables = buckets;
  4012bf:	41 c7 87 14 fd ff ff ff ff ff 3f 	movl   $0x3fffffff,-0x2ec(%r15)
    data[x].threadsize = threadsize;
  4012ca:	41 c7 87 e8 fc ff ff 04 00 00 00 	movl   $0x4,-0x318(%r15)
    data[x].readies = readies;
  4012d5:	4d 89 af a0 fc ff ff 	mov    %r13,-0x360(%r15)
    data[x].readies[x] = 0;
  4012dc:	43 c7 44 b5 fc 00 00 00 00 	movl   $0x0,-0x4(%r13,%r14,4)
  for (int x = 0; x < threadsize ; x++) {
  4012e5:	49 83 c6 01          	add    $0x1,%r14
    data[x].buckets = buckets;
  4012e9:	41 c7 87 10 fd ff ff ff ff ff 3f 	movl   $0x3fffffff,-0x2f0(%r15)
    data[x].main = &data[0];
  4012f4:	49 89 9f a8 fc ff ff 	mov    %rbx,-0x358(%r15)
    data[x].threads = data;
  4012fb:	49 89 9f b0 fc ff ff 	mov    %rbx,-0x350(%r15)
    data[x].readcursor = threadsize - 1;
  401302:	41 c7 87 80 fe ff ff 03 00 00 00 	movl   $0x3,-0x180(%r15)
    data[x].writecursor = threadsize - 1;
  40130d:	41 c7 87 00 fe ff ff 03 00 00 00 	movl   $0x3,-0x200(%r15)
    data[x].freelist = freelist;
  401318:	49 89 87 20 fd ff ff 	mov    %rax,-0x2e0(%r15)
    data[x].newmask = 0;
  40131f:	41 c7 87 48 fd ff ff 00 00 00 00 	movl   $0x0,-0x2b8(%r15)
    data[x].thiswrite = threadsize;
  40132a:	41 c7 47 a8 04 00 00 00 	movl   $0x4,-0x58(%r15)
    data[x].read = 0;
  401332:	41 0f 29 8f 80 fc ff ff 	movaps %xmm1,-0x380(%r15)
    data[x].chunkslen = chunkslen;
  40133a:	41 0f 11 97 38 fd ff ff 	movups %xmm2,-0x2c8(%r15)
    data[x].prevread = threadsize;
  401342:	41 0f 11 5f 88       	movups %xmm3,-0x78(%r15)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401347:	e8 44 fd ff ff       	call   401090 <calloc@plt>
    data[x].epochssize = epochs;
    
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  40134c:	be 30 00 00 00       	mov    $0x30,%esi
  401351:	bf 10 27 00 00       	mov    $0x2710,%edi
    data[x].epochssize = epochs;
  401356:	41 c7 47 a0 80 96 98 00 	movl   $0x989680,-0x60(%r15)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40135e:	49 89 47 98          	mov    %rax,-0x68(%r15)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  401362:	e8 29 fd ff ff       	call   401090 <calloc@plt>
  401367:	49 89 47 b0          	mov    %rax,-0x50(%r15)
  for (int x = 0; x < threadsize ; x++) {
  40136b:	49 83 fe 05          	cmp    $0x5,%r14
  40136f:	0f 85 ad fe ff ff    	jne    401222 <main+0x152>
  401375:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
  40137a:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  40137f:	48 89 1c 24          	mov    %rbx,(%rsp)
  401383:	49 89 de             	mov    %rbx,%r14
  401386:	49 c7 c5 80 1c 40 00 	mov    $0x401c80,%r13
  40138d:	48 8d 8d e0 00 00 00 	lea    0xe0(%rbp),%rcx
  401394:	49 89 c4             	mov    %rax,%r12
  401397:	48 89 c3             	mov    %rax,%rbx
  40139a:	49 89 cf             	mov    %rcx,%r15
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  40139d:	4c 89 f1             	mov    %r14,%rcx
  4013a0:	48 89 ee             	mov    %rbp,%rsi
  4013a3:	48 89 df             	mov    %rbx,%rdi
  4013a6:	4c 89 ea             	mov    %r13,%rdx
  4013a9:	e8 02 fd ff ff       	call   4010b0 <pthread_create@plt>
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4013ae:	49 8b 56 78          	mov    0x78(%r14),%rdx
  4013b2:	48 8b 3b             	mov    (%rbx),%rdi
  4013b5:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  4013ba:	48 83 c5 38          	add    $0x38,%rbp
  4013be:	48 83 c3 08          	add    $0x8,%rbx
  4013c2:	49 81 c6 80 03 00 00 	add    $0x380,%r14
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4013c9:	e8 62 fc ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  4013ce:	4c 39 fd             	cmp    %r15,%rbp
  4013d1:	75 ca                	jne    40139d <main+0x2cd>
  }
  
  struct timespec time = {
  4013d3:	48 8b 1c 24          	mov    (%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  4013d7:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  4013dc:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
  struct timespec time = {
  4013e1:	66 0f 6f 05 27 0e 00 00 	movdqa 0xe27(%rip),%xmm0        # 402210 <_IO_stdin_used+0x210>
  4013e9:	4c 8d 6c 24 28       	lea    0x28(%rsp),%r13
  4013ee:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  struct timespec rem = {
  4013f3:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4013f7:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  nanosleep(&time, &rem);
  4013fc:	e8 6f fc ff ff       	call   401070 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  401401:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
  401406:	c7 43 5c 00 00 00 00 	movl   $0x0,0x5c(%rbx)
  40140d:	c7 83 dc 03 00 00 00 00 00 00 	movl   $0x0,0x3dc(%rbx)
  401417:	c7 83 5c 07 00 00 00 00 00 00 	movl   $0x0,0x75c(%rbx)
  401421:	48 83 c5 20          	add    $0x20,%rbp
  401425:	c7 83 dc 0a 00 00 00 00 00 00 	movl   $0x0,0xadc(%rbx)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  40142f:	49 8b 3c 24          	mov    (%r12),%rdi
  401433:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  401436:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  40143a:	e8 81 fc ff ff       	call   4010c0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  40143f:	49 39 ec             	cmp    %rbp,%r12
  401442:	75 eb                	jne    40142f <main+0x35f>
  401444:	48 8d 3d 3b 0c 00 00 	lea    0xc3b(%rip),%rdi        # 402086 <_IO_stdin_used+0x86>
  40144b:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  40144f:	45 31 e4             	xor    %r12d,%r12d
  401452:	e8 e9 fb ff ff       	call   401040 <puts@plt>
  long sends = 1;
  for (int x = 0; x < threadsize; x++) {
  401457:	4c 8d b3 48 0e 00 00 	lea    0xe48(%rbx),%r14
  40145e:	4c 8d 2d 36 0c 00 00 	lea    0xc36(%rip),%r13        # 40209b <_IO_stdin_used+0x9b>
  401465:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401469:	4c 89 ee             	mov    %r13,%rsi
  40146c:	bf 01 00 00 00       	mov    $0x1,%edi
  401471:	31 c0                	xor    %eax,%eax
  401473:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
  40147a:	e8 21 fc ff ff       	call   4010a0 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  40147f:	4c 03 a5 80 fc ff ff 	add    -0x380(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  401486:	4c 39 f5             	cmp    %r14,%rbp
  401489:	75 da                	jne    401465 <main+0x395>
  40148b:	4c 89 e2             	mov    %r12,%rdx
  40148e:	48 8d 35 11 0c 00 00 	lea    0xc11(%rip),%rsi        # 4020a6 <_IO_stdin_used+0xa6>
  401495:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  401499:	31 c0                	xor    %eax,%eax
  40149b:	bf 01 00 00 00       	mov    $0x1,%edi
  4014a0:	4c 8d b3 50 0e 00 00 	lea    0xe50(%rbx),%r14
  4014a7:	4c 8d 2d 56 0c 00 00 	lea    0xc56(%rip),%r13        # 402104 <_IO_stdin_used+0x104>
  4014ae:	e8 ed fb ff ff       	call   4010a0 <__printf_chk@plt>
  4014b3:	4c 89 e2             	mov    %r12,%rdx
  4014b6:	bf 01 00 00 00       	mov    $0x1,%edi
  4014bb:	31 c0                	xor    %eax,%eax
  4014bd:	48 8d 35 ed 0b 00 00 	lea    0xbed(%rip),%rsi        # 4020b1 <_IO_stdin_used+0xb1>
  4014c4:	e8 d7 fb ff ff       	call   4010a0 <__printf_chk@plt>
  }
  printf("freq: %ld\n", freq/ seconds);
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  4014c9:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  4014ce:	bf 01 00 00 00       	mov    $0x1,%edi
  4014d3:	48 8d 35 e5 0b 00 00 	lea    0xbe5(%rip),%rsi        # 4020bf <_IO_stdin_used+0xbf>
  4014da:	48 99                	cqto
  4014dc:	49 f7 fc             	idiv   %r12
  4014df:	49 89 c4             	mov    %rax,%r12
  4014e2:	48 89 c2             	mov    %rax,%rdx
  4014e5:	31 c0                	xor    %eax,%eax
  4014e7:	e8 b4 fb ff ff       	call   4010a0 <__printf_chk@plt>
  4014ec:	4c 89 e2             	mov    %r12,%rdx
  4014ef:	bf 01 00 00 00       	mov    $0x1,%edi
  4014f4:	31 c0                	xor    %eax,%eax
  4014f6:	48 8d 35 d6 0b 00 00 	lea    0xbd6(%rip),%rsi        # 4020d3 <_IO_stdin_used+0xd3>
  4014fd:	e8 9e fb ff ff       	call   4010a0 <__printf_chk@plt>
  401502:	4c 89 e2             	mov    %r12,%rdx
  401505:	bf 01 00 00 00       	mov    $0x1,%edi
  40150a:	31 c0                	xor    %eax,%eax
  40150c:	48 8d 35 de 0b 00 00 	lea    0xbde(%rip),%rsi        # 4020f1 <_IO_stdin_used+0xf1>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  long freq_writes = 0;
  401513:	45 31 e4             	xor    %r12d,%r12d
  401516:	e8 85 fb ff ff       	call   4010a0 <__printf_chk@plt>
  
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  40151b:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  40151f:	4c 89 ee             	mov    %r13,%rsi
  401522:	bf 01 00 00 00       	mov    $0x1,%edi
  401527:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  401529:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
    freq_writes += data[x].freq_writes;
  401530:	49 01 d4             	add    %rdx,%r12
  401533:	e8 68 fb ff ff       	call   4010a0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  401538:	4c 39 f5             	cmp    %r14,%rbp
  40153b:	75 de                	jne    40151b <main+0x44b>
  40153d:	4c 89 e2             	mov    %r12,%rdx
  401540:	48 8d 35 c9 0b 00 00 	lea    0xbc9(%rip),%rsi        # 402110 <_IO_stdin_used+0x110>
  401547:	bf 01 00 00 00       	mov    $0x1,%edi
  40154c:	31 c0                	xor    %eax,%eax
  40154e:	e8 4d fb ff ff       	call   4010a0 <__printf_chk@plt>
  401553:	4c 89 e2             	mov    %r12,%rdx
  401556:	bf 01 00 00 00       	mov    $0x1,%edi
  40155b:	31 c0                	xor    %eax,%eax
  40155d:	48 8d 35 be 0b 00 00 	lea    0xbbe(%rip),%rsi        # 402122 <_IO_stdin_used+0x122>
  401564:	48 8d 2d 63 0b 00 00 	lea    0xb63(%rip),%rbp        # 4020ce <_IO_stdin_used+0xce>
  40156b:	e8 30 fb ff ff       	call   4010a0 <__printf_chk@plt>
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  401570:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  401575:	bf 01 00 00 00       	mov    $0x1,%edi
  40157a:	48 8d 35 b9 0b 00 00 	lea    0xbb9(%rip),%rsi        # 40213a <_IO_stdin_used+0x13a>
  401581:	48 99                	cqto
  401583:	49 f7 fc             	idiv   %r12
  401586:	49 89 c4             	mov    %rax,%r12
  401589:	48 89 c2             	mov    %rax,%rdx
  40158c:	31 c0                	xor    %eax,%eax
  40158e:	e8 0d fb ff ff       	call   4010a0 <__printf_chk@plt>
  401593:	4c 89 e2             	mov    %r12,%rdx
  401596:	bf 01 00 00 00       	mov    $0x1,%edi
  40159b:	31 c0                	xor    %eax,%eax
  40159d:	48 8d 35 04 0c 00 00 	lea    0xc04(%rip),%rsi        # 4021a8 <_IO_stdin_used+0x1a8>
  4015a4:	e8 f7 fa ff ff       	call   4010a0 <__printf_chk@plt>
  4015a9:	4c 89 e2             	mov    %r12,%rdx
  4015ac:	bf 01 00 00 00       	mov    $0x1,%edi
  4015b1:	31 c0                	xor    %eax,%eax
  4015b3:	48 8d 35 9b 0b 00 00 	lea    0xb9b(%rip),%rsi        # 402155 <_IO_stdin_used+0x155>
  4015ba:	e8 e1 fa ff ff       	call   4010a0 <__printf_chk@plt>
  4015bf:	48 8d 3d a9 0b 00 00 	lea    0xba9(%rip),%rdi        # 40216f <_IO_stdin_used+0x16f>
  4015c6:	e8 75 fa ff ff       	call   401040 <puts@plt>
  4015cb:	48 89 ee             	mov    %rbp,%rsi
  4015ce:	bf 01 00 00 00       	mov    $0x1,%edi
  4015d3:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  4015d5:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  4015dc:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4015e3:	e8 b8 fa ff ff       	call   4010a0 <__printf_chk@plt>
  4015e8:	48 89 ee             	mov    %rbp,%rsi
  4015eb:	bf 01 00 00 00       	mov    $0x1,%edi
  4015f0:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  4015f2:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  4015f9:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  401600:	e8 9b fa ff ff       	call   4010a0 <__printf_chk@plt>
  401605:	48 89 ee             	mov    %rbp,%rsi
  401608:	bf 01 00 00 00       	mov    $0x1,%edi
  40160d:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  40160f:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  401616:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  40161d:	e8 7e fa ff ff       	call   4010a0 <__printf_chk@plt>
  401622:	48 89 ee             	mov    %rbp,%rsi
  401625:	bf 01 00 00 00       	mov    $0x1,%edi
  40162a:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  40162c:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  401633:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  40163a:	e8 61 fa ff ff       	call   4010a0 <__printf_chk@plt>
  40163f:	48 89 ee             	mov    %rbp,%rsi
  401642:	bf 01 00 00 00       	mov    $0x1,%edi
  401647:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  401649:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401650:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  401657:	e8 44 fa ff ff       	call   4010a0 <__printf_chk@plt>
  40165c:	48 89 ee             	mov    %rbp,%rsi
  40165f:	bf 01 00 00 00       	mov    $0x1,%edi
  401664:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  401666:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  40166d:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401674:	e8 27 fa ff ff       	call   4010a0 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  401679:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  401680:	bf 01 00 00 00       	mov    $0x1,%edi
  401685:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  40168c:	48 8d 35 e9 0a 00 00 	lea    0xae9(%rip),%rsi        # 40217c <_IO_stdin_used+0x17c>
  401693:	31 c0                	xor    %eax,%eax
  401695:	e8 06 fa ff ff       	call   4010a0 <__printf_chk@plt>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  40169a:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  40169f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4016a8:	75 11                	jne    4016bb <main+0x5eb>
  4016aa:	48 83 c4 68          	add    $0x68,%rsp
  4016ae:	31 c0                	xor    %eax,%eax
  4016b0:	5b                   	pop    %rbx
  4016b1:	5d                   	pop    %rbp
  4016b2:	41 5c                	pop    %r12
  4016b4:	41 5d                	pop    %r13
  4016b6:	41 5e                	pop    %r14
  4016b8:	41 5f                	pop    %r15
  4016ba:	c3                   	ret
  4016bb:	e8 a0 f9 ff ff       	call   401060 <__stack_chk_fail@plt>

00000000004016c0 <_start>:
  4016c0:	f3 0f 1e fa          	endbr64
  4016c4:	31 ed                	xor    %ebp,%ebp
  4016c6:	49 89 d1             	mov    %rdx,%r9
  4016c9:	5e                   	pop    %rsi
  4016ca:	48 89 e2             	mov    %rsp,%rdx
  4016cd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4016d1:	50                   	push   %rax
  4016d2:	54                   	push   %rsp
  4016d3:	45 31 c0             	xor    %r8d,%r8d
  4016d6:	31 c9                	xor    %ecx,%ecx
  4016d8:	48 c7 c7 d0 10 40 00 	mov    $0x4010d0,%rdi
  4016df:	ff 15 0b 29 00 00    	call   *0x290b(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  4016e5:	f4                   	hlt
  4016e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004016f0 <_dl_relocate_static_pie>:
  4016f0:	f3 0f 1e fa          	endbr64
  4016f4:	c3                   	ret
  4016f5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4016ff:	90                   	nop

0000000000401700 <deregister_tm_clones>:
  401700:	b8 10 40 40 00       	mov    $0x404010,%eax
  401705:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  40170b:	74 13                	je     401720 <deregister_tm_clones+0x20>
  40170d:	b8 00 00 00 00       	mov    $0x0,%eax
  401712:	48 85 c0             	test   %rax,%rax
  401715:	74 09                	je     401720 <deregister_tm_clones+0x20>
  401717:	bf 10 40 40 00       	mov    $0x404010,%edi
  40171c:	ff e0                	jmp    *%rax
  40171e:	66 90                	xchg   %ax,%ax
  401720:	c3                   	ret
  401721:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40172c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401730 <register_tm_clones>:
  401730:	be 10 40 40 00       	mov    $0x404010,%esi
  401735:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  40173c:	48 89 f0             	mov    %rsi,%rax
  40173f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401743:	48 c1 f8 03          	sar    $0x3,%rax
  401747:	48 01 c6             	add    %rax,%rsi
  40174a:	48 d1 fe             	sar    %rsi
  40174d:	74 11                	je     401760 <register_tm_clones+0x30>
  40174f:	b8 00 00 00 00       	mov    $0x0,%eax
  401754:	48 85 c0             	test   %rax,%rax
  401757:	74 07                	je     401760 <register_tm_clones+0x30>
  401759:	bf 10 40 40 00       	mov    $0x404010,%edi
  40175e:	ff e0                	jmp    *%rax
  401760:	c3                   	ret
  401761:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40176c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401770 <__do_global_dtors_aux>:
  401770:	f3 0f 1e fa          	endbr64
  401774:	80 3d 95 28 00 00 00 	cmpb   $0x0,0x2895(%rip)        # 404010 <__TMC_END__>
  40177b:	75 13                	jne    401790 <__do_global_dtors_aux+0x20>
  40177d:	55                   	push   %rbp
  40177e:	48 89 e5             	mov    %rsp,%rbp
  401781:	e8 7a ff ff ff       	call   401700 <deregister_tm_clones>
  401786:	c6 05 83 28 00 00 01 	movb   $0x1,0x2883(%rip)        # 404010 <__TMC_END__>
  40178d:	5d                   	pop    %rbp
  40178e:	c3                   	ret
  40178f:	90                   	nop
  401790:	c3                   	ret
  401791:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40179c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004017a0 <frame_dummy>:
  4017a0:	f3 0f 1e fa          	endbr64
  4017a4:	eb 8a                	jmp    401730 <register_tm_clones>
  4017a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004017b0 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  4017b0:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4017b4:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  4017b7:	7e 77                	jle    401830 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  4017b9:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4017bd:	55                   	push   %rbp
  4017be:	49 89 f2             	mov    %rsi,%r10
  4017c1:	49 89 d3             	mov    %rdx,%r11
  4017c4:	53                   	push   %rbx
  4017c5:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  4017c8:	48 8b 98 a0 03 00 00 	mov    0x3a0(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  4017cf:	b8 01 00 00 00       	mov    $0x1,%eax
  4017d4:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  4017d8:	48 63 d0             	movslq %eax,%rdx
  4017db:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  4017de:	85 d2                	test   %edx,%edx
  4017e0:	40 0f 94 c6          	sete   %sil
  4017e4:	f6 c2 04             	test   $0x4,%dl
  4017e7:	75 05                	jne    4017ee <pollthreads+0x3e>
  4017e9:	40 84 f6             	test   %sil,%sil
  4017ec:	74 0d                	je     4017fb <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  4017ee:	49 63 08             	movslq (%r8),%rcx
  4017f1:	8d 69 01             	lea    0x1(%rcx),%ebp
  4017f4:	41 89 28             	mov    %ebp,(%r8)
  4017f7:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  4017fb:	83 e2 08             	and    $0x8,%edx
  4017fe:	75 05                	jne    401805 <pollthreads+0x55>
  401800:	40 84 f6             	test   %sil,%sil
  401803:	74 1b                	je     401820 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  401805:	48 63 17             	movslq (%rdi),%rdx
  401808:	8d 4a 01             	lea    0x1(%rdx),%ecx
  40180b:	89 0f                	mov    %ecx,(%rdi)
  40180d:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  401811:	83 c0 01             	add    $0x1,%eax
  401814:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401818:	7f be                	jg     4017d8 <pollthreads+0x28>
}
  40181a:	31 c0                	xor    %eax,%eax
  40181c:	5b                   	pop    %rbx
  40181d:	5d                   	pop    %rbp
  40181e:	c3                   	ret
  40181f:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  401820:	83 c0 01             	add    $0x1,%eax
  401823:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401827:	7f af                	jg     4017d8 <pollthreads+0x28>
}
  401829:	31 c0                	xor    %eax,%eax
  40182b:	5b                   	pop    %rbx
  40182c:	5d                   	pop    %rbp
  40182d:	c3                   	ret
  40182e:	66 90                	xchg   %ax,%ax
  401830:	31 c0                	xor    %eax,%eax
  401832:	c3                   	ret
  401833:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40183e:	66 90                	xchg   %ax,%ax

0000000000401840 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401840:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401843:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
      if (*availableidx == 0) {
  40184a:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40184d:	48 83 c7 01          	add    $0x1,%rdi
  401851:	48 85 ff             	test   %rdi,%rdi
  401854:	7e 66                	jle    4018bc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401856:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40185d:	31 c9                	xor    %ecx,%ecx
  40185f:	45 31 c9             	xor    %r9d,%r9d
  401862:	31 c0                	xor    %eax,%eax
  401864:	eb 18                	jmp    40187e <findavailable+0x3e>
  401866:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401870:	83 c1 01             	add    $0x1,%ecx
  401873:	48 63 c1             	movslq %ecx,%rax
  401876:	49 89 c1             	mov    %rax,%r9
  401879:	48 39 f8             	cmp    %rdi,%rax
  40187c:	7d 3e                	jge    4018bc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  40187e:	48 c1 e0 05          	shl    $0x5,%rax
  401882:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401888:	75 e6                	jne    401870 <findavailable+0x30>
         available[*availableidx] = x;
  40188a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  40188d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401891:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401895:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401898:	41 8b 43 68          	mov    0x68(%r11),%eax
  40189c:	01 c0                	add    %eax,%eax
  40189e:	41 39 c0             	cmp    %eax,%r8d
  4018a1:	74 19                	je     4018bc <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4018a3:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  4018aa:	83 c1 01             	add    $0x1,%ecx
  4018ad:	48 63 c1             	movslq %ecx,%rax
  4018b0:	48 83 c7 01          	add    $0x1,%rdi
  4018b4:	49 89 c1             	mov    %rax,%r9
  4018b7:	48 39 f8             	cmp    %rdi,%rax
  4018ba:	7c c2                	jl     40187e <findavailable+0x3e>
      if (*availableidx == 0) {
  4018bc:	31 c0                	xor    %eax,%eax
  4018be:	45 85 c0             	test   %r8d,%r8d
  4018c1:	0f 94 c0             	sete   %al
}
  4018c4:	c3                   	ret
  4018c5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000004018d0 <singlewriter3>:
}
  4018d0:	c3                   	ret
  4018d1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4018dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004018e0 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4018e0:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  4018e6:	85 c0                	test   %eax,%eax
  4018e8:	74 1e                	je     401908 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  4018ea:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4018ec:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  4018ed:	55                   	push   %rbp
  4018ee:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4018ef:	8b 77 68             	mov    0x68(%rdi),%esi
  4018f2:	48 89 fb             	mov    %rdi,%rbx
  4018f5:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  4018f8:	f7 f9                	idiv   %ecx
  4018fa:	85 d2                	test   %edx,%edx
  4018fc:	74 12                	je     401910 <singlewriter2+0x30>
}
  4018fe:	5b                   	pop    %rbx
  4018ff:	5d                   	pop    %rbp
  401900:	41 5c                	pop    %r12
  401902:	c3                   	ret
  401903:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401908:	c3                   	ret
  401909:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct Data * thread = &data->threads[data->threadindex];
  401910:	48 63 47 64          	movslq 0x64(%rdi),%rax
  401914:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  40191c:	48 29 c5             	sub    %rax,%rbp
  40191f:	48 c1 e5 07          	shl    $0x7,%rbp
  401923:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401927:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  40192c:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401933:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401937:	49 c1 e4 04          	shl    $0x4,%r12
  40193b:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401942:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401947:	e8 04 f7 ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40194c:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401952:	83 c0 01             	add    $0x1,%eax
  401955:	99                   	cltd
  401956:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  40195c:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40195f:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401965:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401969:	48 8b 05 60 08 00 00 	mov    0x860(%rip),%rax        # 4021d0 <_IO_stdin_used+0x1d0>
  401970:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  401975:	5b                   	pop    %rbx
  401976:	5d                   	pop    %rbp
  401977:	41 5c                	pop    %r12
  401979:	c3                   	ret
  40197a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000401980 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401980:	41 55                	push   %r13
  401982:	49 89 d5             	mov    %rdx,%r13
  401985:	41 54                	push   %r12
  401987:	49 89 cc             	mov    %rcx,%r12
  40198a:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  40198b:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40198e:	48 89 fd             	mov    %rdi,%rbp
  401991:	53                   	push   %rbx
  401992:	48 89 f3             	mov    %rsi,%rbx
  401995:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401999:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40199d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4019a6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  4019ab:	31 c0                	xor    %eax,%eax
  int readers = 0;
  4019ad:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  4019b5:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  4019bb:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  4019c3:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  4019cb:	83 c0 01             	add    $0x1,%eax
  4019ce:	99                   	cltd
  4019cf:	f7 7f 68             	idivl  0x68(%rdi)
  4019d2:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  4019d8:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  4019dd:	4c 89 e9             	mov    %r13,%rcx
  4019e0:	e8 5b fe ff ff       	call   401840 <findavailable>
  if (fill == 1) {
  4019e5:	83 f8 01             	cmp    $0x1,%eax
  4019e8:	0f 84 64 01 00 00    	je     401b52 <singlewriter+0x1d2>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  4019ee:	48 89 ef             	mov    %rbp,%rdi
  4019f1:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  4019f6:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  4019fb:	4c 89 e2             	mov    %r12,%rdx
  4019fe:	4c 89 ee             	mov    %r13,%rsi
  401a01:	e8 aa fd ff ff       	call   4017b0 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401a06:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401a0b:	85 ff                	test   %edi,%edi
  401a0d:	0f 8e 66 01 00 00    	jle    401b79 <singlewriter+0x1f9>
  401a13:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401a18:	31 c9                	xor    %ecx,%ecx
  401a1a:	eb 62                	jmp    401a7e <singlewriter+0xfe>
  401a1c:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401a20:	48 8b 14 cb          	mov    (%rbx,%rcx,8),%rdx
          int thread = readyreaders[x];
  401a24:	4d 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%r10
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401a29:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401a2c:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401a30:	48 c1 e2 05          	shl    $0x5,%rdx
  401a34:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].reading = chunk;
  401a3b:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
          data->threads[thread].start = start;
  401a43:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401a47:	66 0f 6e 4a 08       	movd   0x8(%rdx),%xmm1
          data->threads[thread].reading = chunk;
  401a4c:	4c 29 d0             	sub    %r10,%rax
          chunk->available = READING;
  401a4f:	c7 42 10 02 00 00 00 	movl   $0x2,0x10(%rdx)
          data->threads[thread].reading = chunk;
  401a56:	48 c1 e0 07          	shl    $0x7,%rax
  401a5a:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].start = start;
  401a5e:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401a62:	48 89 90 a8 00 00 00 	mov    %rdx,0xa8(%rax)
          chunk->owner = thread;
  401a69:	44 89 52 14          	mov    %r10d,0x14(%rdx)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401a6d:	83 88 c8 00 00 00 10 	orl    $0x10,0xc8(%rax)
          data->threads[thread].start = start;
  401a74:	66 0f d6 40 14       	movq   %xmm0,0x14(%rax)
        for (int x = 0; x < readers ; x++) {
  401a79:	48 39 cf             	cmp    %rcx,%rdi
  401a7c:	74 07                	je     401a85 <singlewriter+0x105>
  401a7e:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401a80:	4c 39 c1             	cmp    %r8,%rcx
  401a83:	75 9b                	jne    401a20 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401a85:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401a8a:	45 85 c0             	test   %r8d,%r8d
  401a8d:	7e 7a                	jle    401b09 <singlewriter+0x189>
                if (assignedchunk  == availableidx) {
  401a8f:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401a93:	41 01 f0             	add    %esi,%r8d
  401a96:	eb 6d                	jmp    401b05 <singlewriter+0x185>
  401a98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401aa0:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401aa3:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401aa6:	45 8b 0c 24          	mov    (%r12),%r9d
   for (int x = 0; x < writers ; x++) {
  401aaa:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401aae:	48 8b 14 f3          	mov    (%rbx,%rsi,8),%rdx
          data->threads[thread].writing = chunk;
  401ab2:	49 63 f1             	movslq %r9d,%rsi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401ab5:	48 c1 e2 05          	shl    $0x5,%rdx
  401ab9:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].writing = chunk;
  401ac0:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
          data->threads[thread].publishstart = start;
  401ac8:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401acc:	66 0f 6e 52 08       	movd   0x8(%rdx),%xmm2
          data->threads[thread].writing = chunk;
  401ad1:	48 29 f0             	sub    %rsi,%rax
      chunk->available = WRITING;
  401ad4:	c7 42 10 03 00 00 00 	movl   $0x3,0x10(%rdx)
          data->threads[thread].writing = chunk;
  401adb:	48 c1 e0 07          	shl    $0x7,%rax
  401adf:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].publishstart = start;
  401ae3:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401ae7:	48 89 90 b0 00 00 00 	mov    %rdx,0xb0(%rax)
          chunk->owner = thread;
  401aee:	44 89 4a 14          	mov    %r9d,0x14(%rdx)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401af2:	83 88 c8 00 00 00 20 	orl    $0x20,0xc8(%rax)
          data->threads[thread].publishstart = start;
  401af9:	66 0f d6 40 40       	movq   %xmm0,0x40(%rax)
   for (int x = 0; x < writers ; x++) {
  401afe:	44 39 c1             	cmp    %r8d,%ecx
  401b01:	74 06                	je     401b09 <singlewriter+0x189>
  401b03:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401b05:	39 f7                	cmp    %esi,%edi
  401b07:	75 97                	jne    401aa0 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401b09:	8b 7d 68             	mov    0x68(%rbp),%edi
  401b0c:	85 ff                	test   %edi,%edi
  401b0e:	7e 40                	jle    401b50 <singlewriter+0x1d0>
        if (data->threads[x].newmask != 0) {
  401b10:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401b14:	31 d2                	xor    %edx,%edx
  401b16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401b20:	48 63 ca             	movslq %edx,%rcx
  401b23:	48 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rax
  401b2b:	48 29 c8             	sub    %rcx,%rax
  401b2e:	48 c1 e0 07          	shl    $0x7,%rax
  401b32:	4c 01 c0             	add    %r8,%rax
  401b35:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401b3b:	85 f6                	test   %esi,%esi
  401b3d:	74 31                	je     401b70 <singlewriter+0x1f0>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401b3f:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401b43:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401b46:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401b49:	8b 7d 68             	mov    0x68(%rbp),%edi
  401b4c:	39 fa                	cmp    %edi,%edx
  401b4e:	7c d0                	jl     401b20 <singlewriter+0x1a0>
  return 0;
  401b50:	31 c0                	xor    %eax,%eax
}
  401b52:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401b57:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401b60:	75 1e                	jne    401b80 <singlewriter+0x200>
  401b62:	48 83 c4 28          	add    $0x28,%rsp
  401b66:	5b                   	pop    %rbx
  401b67:	5d                   	pop    %rbp
  401b68:	41 5c                	pop    %r12
  401b6a:	41 5d                	pop    %r13
  401b6c:	c3                   	ret
  401b6d:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401b70:	83 c2 01             	add    $0x1,%edx
  401b73:	39 fa                	cmp    %edi,%edx
  401b75:	7c a9                	jl     401b20 <singlewriter+0x1a0>
  401b77:	eb d7                	jmp    401b50 <singlewriter+0x1d0>
      int assignedchunk = 0;
  401b79:	31 f6                	xor    %esi,%esi
  401b7b:	e9 05 ff ff ff       	jmp    401a85 <singlewriter+0x105>
}
  401b80:	e8 db f4 ff ff       	call   401060 <__stack_chk_fail@plt>
  401b85:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401b90 <threadwork>:
  long thiswrite = data->main->globalwrite;
  401b90:	4c 8b 4f 28          	mov    0x28(%rdi),%r9
int * threadwork(struct Data * data) {
  401b94:	48 89 f9             	mov    %rdi,%rcx
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401b97:	48 63 71 68          	movslq 0x68(%rcx),%rsi
  401b9b:	44 8b 41 64          	mov    0x64(%rcx),%r8d
  long thiswrite = data->main->globalwrite;
  401b9f:	49 8b b9 50 03 00 00 	mov    0x350(%r9),%rdi
   data->freq_writes++;
  401ba6:	48 83 41 50 01       	addq   $0x1,0x50(%rcx)
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401bab:	48 89 f8             	mov    %rdi,%rax
  401bae:	48 99                	cqto
  401bb0:	48 f7 fe             	idiv   %rsi
  401bb3:	48 ba 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%rdx
  401bbd:	48 89 c6             	mov    %rax,%rsi
  401bc0:	48 f7 ea             	imul   %rdx
  401bc3:	48 89 f0             	mov    %rsi,%rax
  401bc6:	48 c1 f8 3f          	sar    $0x3f,%rax
  401bca:	48 01 f2             	add    %rsi,%rdx
  401bcd:	48 c1 fa 07          	sar    $0x7,%rdx
  401bd1:	48 29 c2             	sub    %rax,%rdx
  401bd4:	48 89 d0             	mov    %rdx,%rax
  401bd7:	48 c1 e0 08          	shl    $0x8,%rax
  401bdb:	48 29 d0             	sub    %rdx,%rax
  401bde:	48 29 c6             	sub    %rax,%rsi
  401be1:	49 63 c0             	movslq %r8d,%rax
  401be4:	48 c1 e6 10          	shl    $0x10,%rsi
  401be8:	48 09 c6             	or     %rax,%rsi
  data->main->works[buffer] = data->threadindex;
  401beb:	49 8b 41 70          	mov    0x70(%r9),%rax
  401bef:	44 88 04 30          	mov    %r8b,(%rax,%rsi,1)
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_RELAXED);
  401bf3:	48 8b 41 28          	mov    0x28(%rcx),%rax
  401bf7:	f0 48 83 80 50 03 00 00 01 	lock addq $0x1,0x350(%rax)
   long thisgroup = data->main->globalwrite / data->threadsize;
  401c00:	48 8b 41 28          	mov    0x28(%rcx),%rax
  401c04:	4c 63 41 68          	movslq 0x68(%rcx),%r8
  if (data->globalread < thiswrite) {  
  401c08:	48 8b b1 48 03 00 00 	mov    0x348(%rcx),%rsi
   long thisgroup = data->main->globalwrite / data->threadsize;
  401c0f:	48 8b 80 50 03 00 00 	mov    0x350(%rax),%rax
  401c16:	48 99                	cqto
  401c18:	49 f7 f8             	idiv   %r8
   data->lastgroup = thisgroup;
  401c1b:	89 81 58 03 00 00    	mov    %eax,0x358(%rcx)
  if (data->globalread < thiswrite) {  
  401c21:	48 39 fe             	cmp    %rdi,%rsi
  401c24:	7d 3c                	jge    401c62 <threadwork+0xd2>
     data->readcursor = (data->readcursor + 1) % data->threadsize;
  401c26:	8b 81 00 02 00 00    	mov    0x200(%rcx),%eax
   data->freq++;
  401c2c:	48 83 41 48 01       	addq   $0x1,0x48(%rcx)
     data->readcursor = (data->readcursor + 1) % data->threadsize;
  401c31:	83 c0 01             	add    $0x1,%eax
  401c34:	99                   	cltd
  401c35:	41 f7 f8             	idiv   %r8d
  401c38:	89 91 00 02 00 00    	mov    %edx,0x200(%rcx)
         if (data->readcursor == data->threadindex) {
  401c3e:	3b 51 64             	cmp    0x64(%rcx),%edx
  401c41:	74 25                	je     401c68 <threadwork+0xd8>
      data->globalread++;
  401c43:	48 8d 46 01          	lea    0x1(%rsi),%rax
        if ((data->globalread % data->threadsize) == 0) {
  401c47:	48 99                	cqto
      data->globalread++;
  401c49:	48 89 81 48 03 00 00 	mov    %rax,0x348(%rcx)
        if ((data->globalread % data->threadsize) == 0) {
  401c50:	49 f7 f8             	idiv   %r8
  401c53:	48 85 d2             	test   %rdx,%rdx
  401c56:	75 0a                	jne    401c62 <threadwork+0xd2>
          data->readcursor = 0;
  401c58:	c7 81 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rcx)
}
  401c62:	c3                   	ret
  401c63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
           data->readcursor++;
  401c68:	83 c2 01             	add    $0x1,%edx
  401c6b:	89 91 00 02 00 00    	mov    %edx,0x200(%rcx)
  401c71:	eb d0                	jmp    401c43 <threadwork+0xb3>
  401c73:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401c7e:	66 90                	xchg   %ax,%ax

0000000000401c80 <work>:
void * work(void * arg) {
  401c80:	53                   	push   %rbx
  401c81:	8b 57 64             	mov    0x64(%rdi),%edx
  401c84:	48 89 fb             	mov    %rdi,%rbx
  401c87:	31 c0                	xor    %eax,%eax
  401c89:	48 8d 35 74 03 00 00 	lea    0x374(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  401c90:	bf 01 00 00 00       	mov    $0x1,%edi
  401c95:	e8 06 f4 ff ff       	call   4010a0 <__printf_chk@plt>
  while (data->running == 1) {
  401c9a:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401c9e:	75 0e                	jne    401cae <work+0x2e>
      threadwork(data);
  401ca0:	48 89 df             	mov    %rbx,%rdi
  401ca3:	e8 e8 fe ff ff       	call   401b90 <threadwork>
  while (data->running == 1) {
  401ca8:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401cac:	74 f2                	je     401ca0 <work+0x20>
  401cae:	8b 53 64             	mov    0x64(%rbx),%edx
  401cb1:	48 8d 35 5f 03 00 00 	lea    0x35f(%rip),%rsi        # 402017 <_IO_stdin_used+0x17>
  401cb8:	bf 01 00 00 00       	mov    $0x1,%edi
  401cbd:	31 c0                	xor    %eax,%eax
  401cbf:	e8 dc f3 ff ff       	call   4010a0 <__printf_chk@plt>
}
  401cc4:	5b                   	pop    %rbx
  401cc5:	c3                   	ret
  401cc6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401cd0 <work2>:
  while (data->running == 1) {
  401cd0:	eb 0b                	jmp    401cdd <work2+0xd>
  401cd2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  401cd8:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  401cdd:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  401ce1:	74 f5                	je     401cd8 <work2+0x8>
}
  401ce3:	c3                   	ret

Disassembly of section .fini:

0000000000401ce4 <_fini>:
  401ce4:	f3 0f 1e fa          	endbr64
  401ce8:	48 83 ec 08          	sub    $0x8,%rsp
  401cec:	48 83 c4 08          	add    $0x8,%rsp
  401cf0:	c3                   	ret
