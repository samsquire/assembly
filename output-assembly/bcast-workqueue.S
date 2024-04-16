
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
  401140:	ba 10 00 00 00       	mov    $0x10,%edx
  401145:	48 8d 35 fc 0e 00 00 	lea    0xefc(%rip),%rsi        # 402048 <_IO_stdin_used+0x48>
  40114c:	31 c0                	xor    %eax,%eax
  40114e:	bf 01 00 00 00       	mov    $0x1,%edi
  401153:	e8 48 ff ff ff       	call   4010a0 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401158:	be 08 00 00 00       	mov    $0x8,%esi
  40115d:	bf 10 00 00 00       	mov    $0x10,%edi
  401162:	e8 29 ff ff ff       	call   401090 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401167:	be 38 00 00 00       	mov    $0x38,%esi
  40116c:	bf 10 00 00 00       	mov    $0x10,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401171:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401176:	e8 15 ff ff ff       	call   401090 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40117b:	be 00 38 00 00       	mov    $0x3800,%esi
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
  4011fe:	48 8d 35 74 0e 00 00 	lea    0xe74(%rip),%rsi        # 402079 <_IO_stdin_used+0x79>
  401205:	e8 96 fe ff ff       	call   4010a0 <__printf_chk@plt>
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  40120a:	be 04 00 00 00       	mov    $0x4,%esi
  40120f:	bf 10 00 00 00       	mov    $0x10,%edi
  401214:	e8 77 fe ff ff       	call   401090 <calloc@plt>
  data[0].works = works;
  401219:	48 89 6b 70          	mov    %rbp,0x70(%rbx)
  40121d:	31 ed                	xor    %ebp,%ebp
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  40121f:	49 89 c5             	mov    %rax,%r13
  for (int x = 0; x < threadsize ; x++) {
  401222:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401228:	be 80 00 00 00       	mov    $0x80,%esi
  40122d:	bf 01 00 00 00       	mov    $0x1,%edi
  401232:	44 89 34 24          	mov    %r14d,(%rsp)
  401236:	45 8d 66 ff          	lea    -0x1(%r14),%r12d
  40123a:	e8 51 fe ff ff       	call   401090 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  40123f:	44 89 f1             	mov    %r14d,%ecx
  401242:	ba 01 00 00 00       	mov    $0x1,%edx
  401247:	48 8d 35 3a 0f 00 00 	lea    0xf3a(%rip),%rsi        # 402188 <_IO_stdin_used+0x188>
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  40124e:	49 89 47 78          	mov    %rax,0x78(%r15)
    CPU_SET(cpu += 1, data[x].cpu_set);
  401252:	48 d3 e2             	shl    %cl,%rdx
  401255:	8b 0c 24             	mov    (%rsp),%ecx
  401258:	bf 01 00 00 00       	mov    $0x1,%edi
  40125d:	48 09 10             	or     %rdx,(%rax)
  401260:	44 89 e2             	mov    %r12d,%edx
  401263:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  401265:	49 81 c7 80 03 00 00 	add    $0x380,%r15
  40126c:	e8 2f fe ff ff       	call   4010a0 <__printf_chk@plt>
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].bucketstart = x * buckets ;
    data[x].loglevel = debug;
    data[x].running = 1;
  401271:	48 8b 05 60 0f 00 00 	mov    0xf60(%rip),%rax        # 4021d8 <_IO_stdin_used+0x1d8>
    data[x].bucketstart = x * buckets ;
  401278:	41 89 af 18 fd ff ff 	mov    %ebp,-0x2e8(%r15)
    data[x].newmask = 0;
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40127f:	be 30 00 00 00       	mov    $0x30,%esi
    data[x].read = 0;
  401284:	66 0f 6f 0d 54 0f 00 00 	movdqa 0xf54(%rip),%xmm1        # 4021e0 <_IO_stdin_used+0x1e0>
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40128c:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].chunkslen = chunkslen;
  401291:	66 0f 6f 15 57 0f 00 00 	movdqa 0xf57(%rip),%xmm2        # 4021f0 <_IO_stdin_used+0x1f0>
    data[x].loglevel = debug;
  401299:	41 c7 87 00 fd ff ff 00 00 00 00 	movl   $0x0,-0x300(%r15)
    data[x].running = 1;
  4012a4:	49 89 87 dc fc ff ff 	mov    %rax,-0x324(%r15)
    data[x].freelist = freelist;
  4012ab:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  for (int x = 0; x < threadsize ; x++) {
  4012b0:	81 c5 ff ff ff 0f    	add    $0xfffffff,%ebp
    data[x].prevread = threadsize;
  4012b6:	66 0f 6f 1d 42 0f 00 00 	movdqa 0xf42(%rip),%xmm3        # 402200 <_IO_stdin_used+0x200>
    data[x].threadindex = x;
  4012be:	45 89 a7 e4 fc ff ff 	mov    %r12d,-0x31c(%r15)
    data[x].availables = buckets;
  4012c5:	41 c7 87 14 fd ff ff ff ff ff 0f 	movl   $0xfffffff,-0x2ec(%r15)
    data[x].threadsize = threadsize;
  4012d0:	41 c7 87 e8 fc ff ff 10 00 00 00 	movl   $0x10,-0x318(%r15)
    data[x].readies = readies;
  4012db:	4d 89 af a0 fc ff ff 	mov    %r13,-0x360(%r15)
    data[x].readies[x] = 0;
  4012e2:	43 c7 44 b5 fc 00 00 00 00 	movl   $0x0,-0x4(%r13,%r14,4)
  for (int x = 0; x < threadsize ; x++) {
  4012eb:	49 83 c6 01          	add    $0x1,%r14
    data[x].buckets = buckets;
  4012ef:	41 c7 87 10 fd ff ff ff ff ff 0f 	movl   $0xfffffff,-0x2f0(%r15)
    data[x].main = &data[0];
  4012fa:	49 89 9f a8 fc ff ff 	mov    %rbx,-0x358(%r15)
    data[x].threads = data;
  401301:	49 89 9f b0 fc ff ff 	mov    %rbx,-0x350(%r15)
    data[x].readcursor = threadsize - 1;
  401308:	41 c7 87 80 fe ff ff 0f 00 00 00 	movl   $0xf,-0x180(%r15)
    data[x].writecursor = threadsize - 1;
  401313:	41 c7 87 00 fe ff ff 0f 00 00 00 	movl   $0xf,-0x200(%r15)
    data[x].freelist = freelist;
  40131e:	49 89 87 20 fd ff ff 	mov    %rax,-0x2e0(%r15)
    data[x].newmask = 0;
  401325:	41 c7 87 48 fd ff ff 00 00 00 00 	movl   $0x0,-0x2b8(%r15)
    data[x].thiswrite = threadsize;
  401330:	41 c7 47 a8 10 00 00 00 	movl   $0x10,-0x58(%r15)
    data[x].read = 0;
  401338:	41 0f 29 8f 80 fc ff ff 	movaps %xmm1,-0x380(%r15)
    data[x].chunkslen = chunkslen;
  401340:	41 0f 11 97 38 fd ff ff 	movups %xmm2,-0x2c8(%r15)
    data[x].prevread = threadsize;
  401348:	41 0f 11 5f 88       	movups %xmm3,-0x78(%r15)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40134d:	e8 3e fd ff ff       	call   401090 <calloc@plt>
    data[x].epochssize = epochs;
    
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  401352:	be 30 00 00 00       	mov    $0x30,%esi
  401357:	bf 10 27 00 00       	mov    $0x2710,%edi
    data[x].epochssize = epochs;
  40135c:	41 c7 47 a0 80 96 98 00 	movl   $0x989680,-0x60(%r15)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401364:	49 89 47 98          	mov    %rax,-0x68(%r15)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  401368:	e8 23 fd ff ff       	call   401090 <calloc@plt>
  40136d:	49 89 47 b0          	mov    %rax,-0x50(%r15)
  for (int x = 0; x < threadsize ; x++) {
  401371:	49 83 fe 11          	cmp    $0x11,%r14
  401375:	0f 85 ad fe ff ff    	jne    401228 <main+0x158>
  40137b:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
  401380:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  401385:	48 89 1c 24          	mov    %rbx,(%rsp)
  401389:	49 89 de             	mov    %rbx,%r14
  40138c:	49 c7 c5 60 1d 40 00 	mov    $0x401d60,%r13
  401393:	48 8d 8d 80 03 00 00 	lea    0x380(%rbp),%rcx
  40139a:	49 89 c4             	mov    %rax,%r12
  40139d:	48 89 c3             	mov    %rax,%rbx
  4013a0:	49 89 cf             	mov    %rcx,%r15
  4013a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  4013a8:	4c 89 f1             	mov    %r14,%rcx
  4013ab:	48 89 ee             	mov    %rbp,%rsi
  4013ae:	48 89 df             	mov    %rbx,%rdi
  4013b1:	4c 89 ea             	mov    %r13,%rdx
  4013b4:	e8 f7 fc ff ff       	call   4010b0 <pthread_create@plt>
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4013b9:	49 8b 56 78          	mov    0x78(%r14),%rdx
  4013bd:	48 8b 3b             	mov    (%rbx),%rdi
  4013c0:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  4013c5:	48 83 c5 38          	add    $0x38,%rbp
  4013c9:	48 83 c3 08          	add    $0x8,%rbx
  4013cd:	49 81 c6 80 03 00 00 	add    $0x380,%r14
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4013d4:	e8 57 fc ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  4013d9:	4c 39 fd             	cmp    %r15,%rbp
  4013dc:	75 ca                	jne    4013a8 <main+0x2d8>
  }
  
  struct timespec time = {
  4013de:	48 8b 1c 24          	mov    (%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  4013e2:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  4013e7:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
  struct timespec time = {
  4013ec:	66 0f 6f 05 1c 0e 00 00 	movdqa 0xe1c(%rip),%xmm0        # 402210 <_IO_stdin_used+0x210>
  4013f4:	4c 8d 6c 24 28       	lea    0x28(%rsp),%r13
  4013f9:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  struct timespec rem = {
  4013fe:	66 0f ef c0          	pxor   %xmm0,%xmm0
  401402:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  nanosleep(&time, &rem);
  401407:	e8 64 fc ff ff       	call   401070 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  40140c:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
  401411:	c7 43 5c 00 00 00 00 	movl   $0x0,0x5c(%rbx)
  401418:	c7 83 dc 03 00 00 00 00 00 00 	movl   $0x0,0x3dc(%rbx)
  401422:	c7 83 5c 07 00 00 00 00 00 00 	movl   $0x0,0x75c(%rbx)
  40142c:	48 83 ed 80          	sub    $0xffffffffffffff80,%rbp
  401430:	c7 83 dc 0a 00 00 00 00 00 00 	movl   $0x0,0xadc(%rbx)
  40143a:	c7 83 5c 0e 00 00 00 00 00 00 	movl   $0x0,0xe5c(%rbx)
  401444:	c7 83 dc 11 00 00 00 00 00 00 	movl   $0x0,0x11dc(%rbx)
  40144e:	c7 83 5c 15 00 00 00 00 00 00 	movl   $0x0,0x155c(%rbx)
  401458:	c7 83 dc 18 00 00 00 00 00 00 	movl   $0x0,0x18dc(%rbx)
  401462:	c7 83 5c 1c 00 00 00 00 00 00 	movl   $0x0,0x1c5c(%rbx)
  40146c:	c7 83 dc 1f 00 00 00 00 00 00 	movl   $0x0,0x1fdc(%rbx)
  401476:	c7 83 5c 23 00 00 00 00 00 00 	movl   $0x0,0x235c(%rbx)
  401480:	c7 83 dc 26 00 00 00 00 00 00 	movl   $0x0,0x26dc(%rbx)
  40148a:	c7 83 5c 2a 00 00 00 00 00 00 	movl   $0x0,0x2a5c(%rbx)
  401494:	c7 83 dc 2d 00 00 00 00 00 00 	movl   $0x0,0x2ddc(%rbx)
  40149e:	c7 83 5c 31 00 00 00 00 00 00 	movl   $0x0,0x315c(%rbx)
  4014a8:	c7 83 dc 34 00 00 00 00 00 00 	movl   $0x0,0x34dc(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  4014b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  4014b8:	49 8b 3c 24          	mov    (%r12),%rdi
  4014bc:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  4014bf:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  4014c3:	e8 f8 fb ff ff       	call   4010c0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  4014c8:	49 39 ec             	cmp    %rbp,%r12
  4014cb:	75 eb                	jne    4014b8 <main+0x3e8>
  4014cd:	48 8d 3d b1 0b 00 00 	lea    0xbb1(%rip),%rdi        # 402085 <_IO_stdin_used+0x85>
  4014d4:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  4014d8:	45 31 e4             	xor    %r12d,%r12d
  4014db:	e8 60 fb ff ff       	call   401040 <puts@plt>
  long sends = 1;
  for (int x = 0; x < threadsize; x++) {
  4014e0:	4c 8d b3 48 38 00 00 	lea    0x3848(%rbx),%r14
  4014e7:	4c 8d 2d ac 0b 00 00 	lea    0xbac(%rip),%r13        # 40209a <_IO_stdin_used+0x9a>
  4014ee:	66 90                	xchg   %ax,%ax
  4014f0:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4014f4:	4c 89 ee             	mov    %r13,%rsi
  4014f7:	bf 01 00 00 00       	mov    $0x1,%edi
  4014fc:	31 c0                	xor    %eax,%eax
  4014fe:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
  401505:	e8 96 fb ff ff       	call   4010a0 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  40150a:	4c 03 a5 80 fc ff ff 	add    -0x380(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  401511:	4c 39 f5             	cmp    %r14,%rbp
  401514:	75 da                	jne    4014f0 <main+0x420>
  }
  printf("freq: %ld\n", freq/ seconds);
  401516:	4c 89 e0             	mov    %r12,%rax
  401519:	49 c1 fc 3f          	sar    $0x3f,%r12
  40151d:	48 ba 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rdx
  401527:	48 8d 35 77 0b 00 00 	lea    0xb77(%rip),%rsi        # 4020a5 <_IO_stdin_used+0xa5>
  40152e:	48 f7 ea             	imul   %rdx
  401531:	bf 01 00 00 00       	mov    $0x1,%edi
  401536:	31 c0                	xor    %eax,%eax
  401538:	4c 8d b3 50 38 00 00 	lea    0x3850(%rbx),%r14
  40153f:	4c 8d 2d bd 0b 00 00 	lea    0xbbd(%rip),%r13        # 402103 <_IO_stdin_used+0x103>
  401546:	48 d1 fa             	sar    %rdx
  401549:	4c 29 e2             	sub    %r12,%rdx
  40154c:	48 89 d5             	mov    %rdx,%rbp
  40154f:	e8 4c fb ff ff       	call   4010a0 <__printf_chk@plt>
  401554:	48 89 ea             	mov    %rbp,%rdx
  401557:	bf 01 00 00 00       	mov    $0x1,%edi
  40155c:	31 c0                	xor    %eax,%eax
  40155e:	48 8d 35 4b 0b 00 00 	lea    0xb4b(%rip),%rsi        # 4020b0 <_IO_stdin_used+0xb0>
  401565:	e8 36 fb ff ff       	call   4010a0 <__printf_chk@plt>
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  40156a:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40156f:	bf 01 00 00 00       	mov    $0x1,%edi
  401574:	48 8d 35 43 0b 00 00 	lea    0xb43(%rip),%rsi        # 4020be <_IO_stdin_used+0xbe>
  40157b:	48 99                	cqto
  40157d:	48 f7 fd             	idiv   %rbp
  401580:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  401584:	49 89 c4             	mov    %rax,%r12
  401587:	48 89 c2             	mov    %rax,%rdx
  40158a:	31 c0                	xor    %eax,%eax
  40158c:	e8 0f fb ff ff       	call   4010a0 <__printf_chk@plt>
  401591:	4c 89 e2             	mov    %r12,%rdx
  401594:	bf 01 00 00 00       	mov    $0x1,%edi
  401599:	31 c0                	xor    %eax,%eax
  40159b:	48 8d 35 30 0b 00 00 	lea    0xb30(%rip),%rsi        # 4020d2 <_IO_stdin_used+0xd2>
  4015a2:	e8 f9 fa ff ff       	call   4010a0 <__printf_chk@plt>
  4015a7:	4c 89 e2             	mov    %r12,%rdx
  4015aa:	bf 01 00 00 00       	mov    $0x1,%edi
  4015af:	31 c0                	xor    %eax,%eax
  4015b1:	48 8d 35 38 0b 00 00 	lea    0xb38(%rip),%rsi        # 4020f0 <_IO_stdin_used+0xf0>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  long freq_writes = 0;
  4015b8:	45 31 e4             	xor    %r12d,%r12d
  4015bb:	e8 e0 fa ff ff       	call   4010a0 <__printf_chk@plt>
  
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  4015c0:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4015c4:	4c 89 ee             	mov    %r13,%rsi
  4015c7:	bf 01 00 00 00       	mov    $0x1,%edi
  4015cc:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  4015ce:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
    freq_writes += data[x].freq_writes;
  4015d5:	49 01 d4             	add    %rdx,%r12
  4015d8:	e8 c3 fa ff ff       	call   4010a0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  4015dd:	49 39 ee             	cmp    %rbp,%r14
  4015e0:	75 de                	jne    4015c0 <main+0x4f0>
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  4015e2:	4c 89 e0             	mov    %r12,%rax
  4015e5:	49 c1 fc 3f          	sar    $0x3f,%r12
  4015e9:	bf 01 00 00 00       	mov    $0x1,%edi
  4015ee:	48 ba 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rdx
  4015f8:	48 f7 ea             	imul   %rdx
  4015fb:	48 8d 35 0d 0b 00 00 	lea    0xb0d(%rip),%rsi        # 40210f <_IO_stdin_used+0x10f>
  401602:	31 c0                	xor    %eax,%eax
  401604:	48 d1 fa             	sar    %rdx
  401607:	4c 29 e2             	sub    %r12,%rdx
  40160a:	48 89 d5             	mov    %rdx,%rbp
  40160d:	e8 8e fa ff ff       	call   4010a0 <__printf_chk@plt>
  401612:	48 89 ea             	mov    %rbp,%rdx
  401615:	bf 01 00 00 00       	mov    $0x1,%edi
  40161a:	31 c0                	xor    %eax,%eax
  40161c:	48 8d 35 fe 0a 00 00 	lea    0xafe(%rip),%rsi        # 402121 <_IO_stdin_used+0x121>
  401623:	e8 78 fa ff ff       	call   4010a0 <__printf_chk@plt>

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  401628:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40162d:	bf 01 00 00 00       	mov    $0x1,%edi
  401632:	48 8d 35 00 0b 00 00 	lea    0xb00(%rip),%rsi        # 402139 <_IO_stdin_used+0x139>
  401639:	48 99                	cqto
  40163b:	48 f7 fd             	idiv   %rbp
  40163e:	48 8d 2d 88 0a 00 00 	lea    0xa88(%rip),%rbp        # 4020cd <_IO_stdin_used+0xcd>
  401645:	49 89 c4             	mov    %rax,%r12
  401648:	48 89 c2             	mov    %rax,%rdx
  40164b:	31 c0                	xor    %eax,%eax
  40164d:	e8 4e fa ff ff       	call   4010a0 <__printf_chk@plt>
  401652:	4c 89 e2             	mov    %r12,%rdx
  401655:	bf 01 00 00 00       	mov    $0x1,%edi
  40165a:	31 c0                	xor    %eax,%eax
  40165c:	48 8d 35 45 0b 00 00 	lea    0xb45(%rip),%rsi        # 4021a8 <_IO_stdin_used+0x1a8>
  401663:	e8 38 fa ff ff       	call   4010a0 <__printf_chk@plt>
  401668:	4c 89 e2             	mov    %r12,%rdx
  40166b:	bf 01 00 00 00       	mov    $0x1,%edi
  401670:	31 c0                	xor    %eax,%eax
  401672:	48 8d 35 db 0a 00 00 	lea    0xadb(%rip),%rsi        # 402154 <_IO_stdin_used+0x154>
  401679:	e8 22 fa ff ff       	call   4010a0 <__printf_chk@plt>
  40167e:	48 8d 3d e9 0a 00 00 	lea    0xae9(%rip),%rdi        # 40216e <_IO_stdin_used+0x16e>
  401685:	e8 b6 f9 ff ff       	call   401040 <puts@plt>
  40168a:	48 89 ee             	mov    %rbp,%rsi
  40168d:	bf 01 00 00 00       	mov    $0x1,%edi
  401692:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  401694:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  40169b:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4016a2:	e8 f9 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  4016a7:	48 89 ee             	mov    %rbp,%rsi
  4016aa:	bf 01 00 00 00       	mov    $0x1,%edi
  4016af:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  4016b1:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  4016b8:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4016bf:	e8 dc f9 ff ff       	call   4010a0 <__printf_chk@plt>
  4016c4:	48 89 ee             	mov    %rbp,%rsi
  4016c7:	bf 01 00 00 00       	mov    $0x1,%edi
  4016cc:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  4016ce:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  4016d5:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  4016dc:	e8 bf f9 ff ff       	call   4010a0 <__printf_chk@plt>
  4016e1:	48 89 ee             	mov    %rbp,%rsi
  4016e4:	bf 01 00 00 00       	mov    $0x1,%edi
  4016e9:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4016eb:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  4016f2:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  4016f9:	e8 a2 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  4016fe:	48 89 ee             	mov    %rbp,%rsi
  401701:	bf 01 00 00 00       	mov    $0x1,%edi
  401706:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  401708:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  40170f:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  401716:	e8 85 f9 ff ff       	call   4010a0 <__printf_chk@plt>
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  40171b:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401722:	48 89 ee             	mov    %rbp,%rsi
  401725:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  40172c:	bf 01 00 00 00       	mov    $0x1,%edi
  401731:	31 c0                	xor    %eax,%eax
  401733:	e8 68 f9 ff ff       	call   4010a0 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  401738:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  40173f:	31 c0                	xor    %eax,%eax
  401741:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  401748:	48 8d 35 2c 0a 00 00 	lea    0xa2c(%rip),%rsi        # 40217b <_IO_stdin_used+0x17b>
  40174f:	bf 01 00 00 00       	mov    $0x1,%edi
  401754:	e8 47 f9 ff ff       	call   4010a0 <__printf_chk@plt>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  401759:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  40175e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401767:	75 11                	jne    40177a <main+0x6aa>
  401769:	48 83 c4 68          	add    $0x68,%rsp
  40176d:	31 c0                	xor    %eax,%eax
  40176f:	5b                   	pop    %rbx
  401770:	5d                   	pop    %rbp
  401771:	41 5c                	pop    %r12
  401773:	41 5d                	pop    %r13
  401775:	41 5e                	pop    %r14
  401777:	41 5f                	pop    %r15
  401779:	c3                   	ret
  40177a:	e8 e1 f8 ff ff       	call   401060 <__stack_chk_fail@plt>
  40177f:	90                   	nop

0000000000401780 <_start>:
  401780:	f3 0f 1e fa          	endbr64
  401784:	31 ed                	xor    %ebp,%ebp
  401786:	49 89 d1             	mov    %rdx,%r9
  401789:	5e                   	pop    %rsi
  40178a:	48 89 e2             	mov    %rsp,%rdx
  40178d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401791:	50                   	push   %rax
  401792:	54                   	push   %rsp
  401793:	45 31 c0             	xor    %r8d,%r8d
  401796:	31 c9                	xor    %ecx,%ecx
  401798:	48 c7 c7 d0 10 40 00 	mov    $0x4010d0,%rdi
  40179f:	ff 15 4b 28 00 00    	call   *0x284b(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  4017a5:	f4                   	hlt
  4017a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004017b0 <_dl_relocate_static_pie>:
  4017b0:	f3 0f 1e fa          	endbr64
  4017b4:	c3                   	ret
  4017b5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4017bf:	90                   	nop

00000000004017c0 <deregister_tm_clones>:
  4017c0:	b8 10 40 40 00       	mov    $0x404010,%eax
  4017c5:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  4017cb:	74 13                	je     4017e0 <deregister_tm_clones+0x20>
  4017cd:	b8 00 00 00 00       	mov    $0x0,%eax
  4017d2:	48 85 c0             	test   %rax,%rax
  4017d5:	74 09                	je     4017e0 <deregister_tm_clones+0x20>
  4017d7:	bf 10 40 40 00       	mov    $0x404010,%edi
  4017dc:	ff e0                	jmp    *%rax
  4017de:	66 90                	xchg   %ax,%ax
  4017e0:	c3                   	ret
  4017e1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4017ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004017f0 <register_tm_clones>:
  4017f0:	be 10 40 40 00       	mov    $0x404010,%esi
  4017f5:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  4017fc:	48 89 f0             	mov    %rsi,%rax
  4017ff:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401803:	48 c1 f8 03          	sar    $0x3,%rax
  401807:	48 01 c6             	add    %rax,%rsi
  40180a:	48 d1 fe             	sar    %rsi
  40180d:	74 11                	je     401820 <register_tm_clones+0x30>
  40180f:	b8 00 00 00 00       	mov    $0x0,%eax
  401814:	48 85 c0             	test   %rax,%rax
  401817:	74 07                	je     401820 <register_tm_clones+0x30>
  401819:	bf 10 40 40 00       	mov    $0x404010,%edi
  40181e:	ff e0                	jmp    *%rax
  401820:	c3                   	ret
  401821:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40182c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401830 <__do_global_dtors_aux>:
  401830:	f3 0f 1e fa          	endbr64
  401834:	80 3d d5 27 00 00 00 	cmpb   $0x0,0x27d5(%rip)        # 404010 <__TMC_END__>
  40183b:	75 13                	jne    401850 <__do_global_dtors_aux+0x20>
  40183d:	55                   	push   %rbp
  40183e:	48 89 e5             	mov    %rsp,%rbp
  401841:	e8 7a ff ff ff       	call   4017c0 <deregister_tm_clones>
  401846:	c6 05 c3 27 00 00 01 	movb   $0x1,0x27c3(%rip)        # 404010 <__TMC_END__>
  40184d:	5d                   	pop    %rbp
  40184e:	c3                   	ret
  40184f:	90                   	nop
  401850:	c3                   	ret
  401851:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40185c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401860 <frame_dummy>:
  401860:	f3 0f 1e fa          	endbr64
  401864:	eb 8a                	jmp    4017f0 <register_tm_clones>
  401866:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401870 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  401870:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  401874:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  401877:	7e 77                	jle    4018f0 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  401879:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  40187d:	55                   	push   %rbp
  40187e:	49 89 f2             	mov    %rsi,%r10
  401881:	49 89 d3             	mov    %rdx,%r11
  401884:	53                   	push   %rbx
  401885:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  401888:	48 8b 98 a0 03 00 00 	mov    0x3a0(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  40188f:	b8 01 00 00 00       	mov    $0x1,%eax
  401894:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  401898:	48 63 d0             	movslq %eax,%rdx
  40189b:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  40189e:	85 d2                	test   %edx,%edx
  4018a0:	40 0f 94 c6          	sete   %sil
  4018a4:	f6 c2 04             	test   $0x4,%dl
  4018a7:	75 05                	jne    4018ae <pollthreads+0x3e>
  4018a9:	40 84 f6             	test   %sil,%sil
  4018ac:	74 0d                	je     4018bb <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  4018ae:	49 63 08             	movslq (%r8),%rcx
  4018b1:	8d 69 01             	lea    0x1(%rcx),%ebp
  4018b4:	41 89 28             	mov    %ebp,(%r8)
  4018b7:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  4018bb:	83 e2 08             	and    $0x8,%edx
  4018be:	75 05                	jne    4018c5 <pollthreads+0x55>
  4018c0:	40 84 f6             	test   %sil,%sil
  4018c3:	74 1b                	je     4018e0 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  4018c5:	48 63 17             	movslq (%rdi),%rdx
  4018c8:	8d 4a 01             	lea    0x1(%rdx),%ecx
  4018cb:	89 0f                	mov    %ecx,(%rdi)
  4018cd:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  4018d1:	83 c0 01             	add    $0x1,%eax
  4018d4:	41 39 41 68          	cmp    %eax,0x68(%r9)
  4018d8:	7f be                	jg     401898 <pollthreads+0x28>
}
  4018da:	31 c0                	xor    %eax,%eax
  4018dc:	5b                   	pop    %rbx
  4018dd:	5d                   	pop    %rbp
  4018de:	c3                   	ret
  4018df:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  4018e0:	83 c0 01             	add    $0x1,%eax
  4018e3:	41 39 41 68          	cmp    %eax,0x68(%r9)
  4018e7:	7f af                	jg     401898 <pollthreads+0x28>
}
  4018e9:	31 c0                	xor    %eax,%eax
  4018eb:	5b                   	pop    %rbx
  4018ec:	5d                   	pop    %rbp
  4018ed:	c3                   	ret
  4018ee:	66 90                	xchg   %ax,%ax
  4018f0:	31 c0                	xor    %eax,%eax
  4018f2:	c3                   	ret
  4018f3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4018fe:	66 90                	xchg   %ax,%ax

0000000000401900 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401900:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401903:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
      if (*availableidx == 0) {
  40190a:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40190d:	48 83 c7 01          	add    $0x1,%rdi
  401911:	48 85 ff             	test   %rdi,%rdi
  401914:	7e 66                	jle    40197c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401916:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40191d:	31 c9                	xor    %ecx,%ecx
  40191f:	45 31 c9             	xor    %r9d,%r9d
  401922:	31 c0                	xor    %eax,%eax
  401924:	eb 18                	jmp    40193e <findavailable+0x3e>
  401926:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401930:	83 c1 01             	add    $0x1,%ecx
  401933:	48 63 c1             	movslq %ecx,%rax
  401936:	49 89 c1             	mov    %rax,%r9
  401939:	48 39 f8             	cmp    %rdi,%rax
  40193c:	7d 3e                	jge    40197c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  40193e:	48 c1 e0 05          	shl    $0x5,%rax
  401942:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401948:	75 e6                	jne    401930 <findavailable+0x30>
         available[*availableidx] = x;
  40194a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  40194d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401951:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401955:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401958:	41 8b 43 68          	mov    0x68(%r11),%eax
  40195c:	01 c0                	add    %eax,%eax
  40195e:	41 39 c0             	cmp    %eax,%r8d
  401961:	74 19                	je     40197c <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401963:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  40196a:	83 c1 01             	add    $0x1,%ecx
  40196d:	48 63 c1             	movslq %ecx,%rax
  401970:	48 83 c7 01          	add    $0x1,%rdi
  401974:	49 89 c1             	mov    %rax,%r9
  401977:	48 39 f8             	cmp    %rdi,%rax
  40197a:	7c c2                	jl     40193e <findavailable+0x3e>
      if (*availableidx == 0) {
  40197c:	31 c0                	xor    %eax,%eax
  40197e:	45 85 c0             	test   %r8d,%r8d
  401981:	0f 94 c0             	sete   %al
}
  401984:	c3                   	ret
  401985:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401990 <singlewriter3>:
}
  401990:	c3                   	ret
  401991:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40199c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004019a0 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4019a0:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  4019a6:	85 c0                	test   %eax,%eax
  4019a8:	74 1e                	je     4019c8 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  4019aa:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4019ac:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  4019ad:	55                   	push   %rbp
  4019ae:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4019af:	8b 77 68             	mov    0x68(%rdi),%esi
  4019b2:	48 89 fb             	mov    %rdi,%rbx
  4019b5:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  4019b8:	f7 f9                	idiv   %ecx
  4019ba:	85 d2                	test   %edx,%edx
  4019bc:	74 12                	je     4019d0 <singlewriter2+0x30>
}
  4019be:	5b                   	pop    %rbx
  4019bf:	5d                   	pop    %rbp
  4019c0:	41 5c                	pop    %r12
  4019c2:	c3                   	ret
  4019c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4019c8:	c3                   	ret
  4019c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct Data * thread = &data->threads[data->threadindex];
  4019d0:	48 63 47 64          	movslq 0x64(%rdi),%rax
  4019d4:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  4019dc:	48 29 c5             	sub    %rax,%rbp
  4019df:	48 c1 e5 07          	shl    $0x7,%rbp
  4019e3:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  4019e7:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4019ec:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  4019f3:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  4019f7:	49 c1 e4 04          	shl    $0x4,%r12
  4019fb:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401a02:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401a07:	e8 44 f6 ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401a0c:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401a12:	83 c0 01             	add    $0x1,%eax
  401a15:	99                   	cltd
  401a16:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  401a1c:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401a1f:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401a25:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401a29:	48 8b 05 a0 07 00 00 	mov    0x7a0(%rip),%rax        # 4021d0 <_IO_stdin_used+0x1d0>
  401a30:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  401a35:	5b                   	pop    %rbx
  401a36:	5d                   	pop    %rbp
  401a37:	41 5c                	pop    %r12
  401a39:	c3                   	ret
  401a3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000401a40 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a40:	41 55                	push   %r13
  401a42:	49 89 d5             	mov    %rdx,%r13
  401a45:	41 54                	push   %r12
  401a47:	49 89 cc             	mov    %rcx,%r12
  401a4a:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401a4b:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a4e:	48 89 fd             	mov    %rdi,%rbp
  401a51:	53                   	push   %rbx
  401a52:	48 89 f3             	mov    %rsi,%rbx
  401a55:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401a59:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a5d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401a66:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401a6b:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401a6d:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401a75:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  401a7b:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401a83:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401a8b:	83 c0 01             	add    $0x1,%eax
  401a8e:	99                   	cltd
  401a8f:	f7 7f 68             	idivl  0x68(%rdi)
  401a92:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401a98:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401a9d:	4c 89 e9             	mov    %r13,%rcx
  401aa0:	e8 5b fe ff ff       	call   401900 <findavailable>
  if (fill == 1) {
  401aa5:	83 f8 01             	cmp    $0x1,%eax
  401aa8:	0f 84 64 01 00 00    	je     401c12 <singlewriter+0x1d2>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401aae:	48 89 ef             	mov    %rbp,%rdi
  401ab1:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401ab6:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401abb:	4c 89 e2             	mov    %r12,%rdx
  401abe:	4c 89 ee             	mov    %r13,%rsi
  401ac1:	e8 aa fd ff ff       	call   401870 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401ac6:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401acb:	85 ff                	test   %edi,%edi
  401acd:	0f 8e 66 01 00 00    	jle    401c39 <singlewriter+0x1f9>
  401ad3:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401ad8:	31 c9                	xor    %ecx,%ecx
  401ada:	eb 62                	jmp    401b3e <singlewriter+0xfe>
  401adc:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401ae0:	48 8b 14 cb          	mov    (%rbx,%rcx,8),%rdx
          int thread = readyreaders[x];
  401ae4:	4d 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%r10
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401ae9:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401aec:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401af0:	48 c1 e2 05          	shl    $0x5,%rdx
  401af4:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].reading = chunk;
  401afb:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
          data->threads[thread].start = start;
  401b03:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401b07:	66 0f 6e 4a 08       	movd   0x8(%rdx),%xmm1
          data->threads[thread].reading = chunk;
  401b0c:	4c 29 d0             	sub    %r10,%rax
          chunk->available = READING;
  401b0f:	c7 42 10 02 00 00 00 	movl   $0x2,0x10(%rdx)
          data->threads[thread].reading = chunk;
  401b16:	48 c1 e0 07          	shl    $0x7,%rax
  401b1a:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].start = start;
  401b1e:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401b22:	48 89 90 a8 00 00 00 	mov    %rdx,0xa8(%rax)
          chunk->owner = thread;
  401b29:	44 89 52 14          	mov    %r10d,0x14(%rdx)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401b2d:	83 88 c8 00 00 00 10 	orl    $0x10,0xc8(%rax)
          data->threads[thread].start = start;
  401b34:	66 0f d6 40 14       	movq   %xmm0,0x14(%rax)
        for (int x = 0; x < readers ; x++) {
  401b39:	48 39 cf             	cmp    %rcx,%rdi
  401b3c:	74 07                	je     401b45 <singlewriter+0x105>
  401b3e:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401b40:	4c 39 c1             	cmp    %r8,%rcx
  401b43:	75 9b                	jne    401ae0 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401b45:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401b4a:	45 85 c0             	test   %r8d,%r8d
  401b4d:	7e 7a                	jle    401bc9 <singlewriter+0x189>
                if (assignedchunk  == availableidx) {
  401b4f:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401b53:	41 01 f0             	add    %esi,%r8d
  401b56:	eb 6d                	jmp    401bc5 <singlewriter+0x185>
  401b58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b60:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401b63:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401b66:	45 8b 0c 24          	mov    (%r12),%r9d
   for (int x = 0; x < writers ; x++) {
  401b6a:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b6e:	48 8b 14 f3          	mov    (%rbx,%rsi,8),%rdx
          data->threads[thread].writing = chunk;
  401b72:	49 63 f1             	movslq %r9d,%rsi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b75:	48 c1 e2 05          	shl    $0x5,%rdx
  401b79:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].writing = chunk;
  401b80:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
          data->threads[thread].publishstart = start;
  401b88:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401b8c:	66 0f 6e 52 08       	movd   0x8(%rdx),%xmm2
          data->threads[thread].writing = chunk;
  401b91:	48 29 f0             	sub    %rsi,%rax
      chunk->available = WRITING;
  401b94:	c7 42 10 03 00 00 00 	movl   $0x3,0x10(%rdx)
          data->threads[thread].writing = chunk;
  401b9b:	48 c1 e0 07          	shl    $0x7,%rax
  401b9f:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].publishstart = start;
  401ba3:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401ba7:	48 89 90 b0 00 00 00 	mov    %rdx,0xb0(%rax)
          chunk->owner = thread;
  401bae:	44 89 4a 14          	mov    %r9d,0x14(%rdx)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401bb2:	83 88 c8 00 00 00 20 	orl    $0x20,0xc8(%rax)
          data->threads[thread].publishstart = start;
  401bb9:	66 0f d6 40 40       	movq   %xmm0,0x40(%rax)
   for (int x = 0; x < writers ; x++) {
  401bbe:	44 39 c1             	cmp    %r8d,%ecx
  401bc1:	74 06                	je     401bc9 <singlewriter+0x189>
  401bc3:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401bc5:	39 f7                	cmp    %esi,%edi
  401bc7:	75 97                	jne    401b60 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401bc9:	8b 7d 68             	mov    0x68(%rbp),%edi
  401bcc:	85 ff                	test   %edi,%edi
  401bce:	7e 40                	jle    401c10 <singlewriter+0x1d0>
        if (data->threads[x].newmask != 0) {
  401bd0:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401bd4:	31 d2                	xor    %edx,%edx
  401bd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401be0:	48 63 ca             	movslq %edx,%rcx
  401be3:	48 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rax
  401beb:	48 29 c8             	sub    %rcx,%rax
  401bee:	48 c1 e0 07          	shl    $0x7,%rax
  401bf2:	4c 01 c0             	add    %r8,%rax
  401bf5:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401bfb:	85 f6                	test   %esi,%esi
  401bfd:	74 31                	je     401c30 <singlewriter+0x1f0>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401bff:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401c03:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401c06:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401c09:	8b 7d 68             	mov    0x68(%rbp),%edi
  401c0c:	39 fa                	cmp    %edi,%edx
  401c0e:	7c d0                	jl     401be0 <singlewriter+0x1a0>
  return 0;
  401c10:	31 c0                	xor    %eax,%eax
}
  401c12:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401c17:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401c20:	75 1e                	jne    401c40 <singlewriter+0x200>
  401c22:	48 83 c4 28          	add    $0x28,%rsp
  401c26:	5b                   	pop    %rbx
  401c27:	5d                   	pop    %rbp
  401c28:	41 5c                	pop    %r12
  401c2a:	41 5d                	pop    %r13
  401c2c:	c3                   	ret
  401c2d:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401c30:	83 c2 01             	add    $0x1,%edx
  401c33:	39 fa                	cmp    %edi,%edx
  401c35:	7c a9                	jl     401be0 <singlewriter+0x1a0>
  401c37:	eb d7                	jmp    401c10 <singlewriter+0x1d0>
      int assignedchunk = 0;
  401c39:	31 f6                	xor    %esi,%esi
  401c3b:	e9 05 ff ff ff       	jmp    401b45 <singlewriter+0x105>
}
  401c40:	e8 1b f4 ff ff       	call   401060 <__stack_chk_fail@plt>
  401c45:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401c50 <threadwork>:
int * threadwork(struct Data * data) {
  401c50:	48 89 f9             	mov    %rdi,%rcx
  long thiswrite = data->main->globalwrite;
  401c53:	48 8b 7f 28          	mov    0x28(%rdi),%rdi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401c57:	48 63 71 68          	movslq 0x68(%rcx),%rsi
  401c5b:	48 8b 87 38 03 00 00 	mov    0x338(%rdi),%rax
  long thiswrite = data->main->globalwrite;
  401c62:	4c 8b 87 50 03 00 00 	mov    0x350(%rdi),%r8
  long lastcursor = data->main->writecursor;
  401c69:	44 8b 8f 80 01 00 00 	mov    0x180(%rdi),%r9d
   data->freq_writes++;
  401c70:	48 83 41 50 01       	addq   $0x1,0x50(%rcx)
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401c75:	48 99                	cqto
  401c77:	48 f7 fe             	idiv   %rsi
    data->thiswrite = lastcursor;
  401c7a:	44 89 89 28 03 00 00 	mov    %r9d,0x328(%rcx)
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401c81:	44 8b 49 64          	mov    0x64(%rcx),%r9d
  401c85:	4c 89 c0             	mov    %r8,%rax
    data->prevwrite = lastwrite;
  401c88:	48 89 91 10 03 00 00 	mov    %rdx,0x310(%rcx)
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401c8f:	48 99                	cqto
  401c91:	48 f7 fe             	idiv   %rsi
  401c94:	48 ba 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%rdx
  401c9e:	48 89 c6             	mov    %rax,%rsi
  401ca1:	48 f7 ea             	imul   %rdx
  401ca4:	48 89 f0             	mov    %rsi,%rax
  401ca7:	48 c1 f8 3f          	sar    $0x3f,%rax
  401cab:	48 01 f2             	add    %rsi,%rdx
  401cae:	48 c1 fa 07          	sar    $0x7,%rdx
  401cb2:	48 29 c2             	sub    %rax,%rdx
  401cb5:	48 89 d0             	mov    %rdx,%rax
  401cb8:	48 c1 e0 08          	shl    $0x8,%rax
  401cbc:	48 29 d0             	sub    %rdx,%rax
  401cbf:	48 29 c6             	sub    %rax,%rsi
  401cc2:	49 63 c1             	movslq %r9d,%rax
  401cc5:	48 c1 e6 10          	shl    $0x10,%rsi
  401cc9:	48 09 c6             	or     %rax,%rsi
  data->main->works[buffer] = data->threadindex;
  401ccc:	48 8b 47 70          	mov    0x70(%rdi),%rax
  401cd0:	44 88 0c 30          	mov    %r9b,(%rax,%rsi,1)
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_RELAXED);
  401cd4:	48 8b 41 28          	mov    0x28(%rcx),%rax
  401cd8:	f0 48 83 80 50 03 00 00 01 	lock addq $0x1,0x350(%rax)
  long lastread = data->main->totalreads % data->threadsize;
  401ce1:	48 8b 41 28          	mov    0x28(%rcx),%rax
  401ce5:	48 63 79 68          	movslq 0x68(%rcx),%rdi
      if (data->globalread < thiswrite) {  
  401ce9:	48 8b b1 48 03 00 00 	mov    0x348(%rcx),%rsi
  long lastread = data->main->totalreads % data->threadsize;
  401cf0:	48 8b 80 40 03 00 00 	mov    0x340(%rax),%rax
   data->freq++;
  401cf7:	48 83 41 48 01       	addq   $0x1,0x48(%rcx)
  long lastread = data->main->totalreads % data->threadsize;
  401cfc:	48 99                	cqto
  401cfe:	48 f7 ff             	idiv   %rdi
   data->prevread = lastread;
  401d01:	48 89 91 08 03 00 00 	mov    %rdx,0x308(%rcx)
      if (data->globalread < thiswrite) {  
  401d08:	4c 39 c6             	cmp    %r8,%rsi
  401d0b:	7d 36                	jge    401d43 <threadwork+0xf3>
     data->readcursor = (data->readcursor + 1) % data->threadsize;
  401d0d:	8b 81 00 02 00 00    	mov    0x200(%rcx),%eax
  401d13:	83 c0 01             	add    $0x1,%eax
  401d16:	99                   	cltd
  401d17:	f7 ff                	idiv   %edi
  401d19:	89 91 00 02 00 00    	mov    %edx,0x200(%rcx)
         if (data->readcursor == data->threadindex) {
  401d1f:	3b 51 64             	cmp    0x64(%rcx),%edx
  401d22:	74 24                	je     401d48 <threadwork+0xf8>
      data->globalread++;
  401d24:	48 8d 46 01          	lea    0x1(%rsi),%rax
        if ((data->globalread % data->threadsize) == 0) {
  401d28:	48 99                	cqto
      data->globalread++;
  401d2a:	48 89 81 48 03 00 00 	mov    %rax,0x348(%rcx)
        if ((data->globalread % data->threadsize) == 0) {
  401d31:	48 f7 ff             	idiv   %rdi
  401d34:	48 85 d2             	test   %rdx,%rdx
  401d37:	75 0a                	jne    401d43 <threadwork+0xf3>
          data->readcursor = 0;
  401d39:	c7 81 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rcx)
}
  401d43:	c3                   	ret
  401d44:	0f 1f 40 00          	nopl   0x0(%rax)
           data->readcursor++;
  401d48:	83 c2 01             	add    $0x1,%edx
  401d4b:	89 91 00 02 00 00    	mov    %edx,0x200(%rcx)
  401d51:	eb d1                	jmp    401d24 <threadwork+0xd4>
  401d53:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401d5e:	66 90                	xchg   %ax,%ax

0000000000401d60 <work>:
void * work(void * arg) {
  401d60:	53                   	push   %rbx
  401d61:	8b 57 64             	mov    0x64(%rdi),%edx
  401d64:	48 89 fb             	mov    %rdi,%rbx
  401d67:	31 c0                	xor    %eax,%eax
  401d69:	48 8d 35 94 02 00 00 	lea    0x294(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  401d70:	bf 01 00 00 00       	mov    $0x1,%edi
  401d75:	e8 26 f3 ff ff       	call   4010a0 <__printf_chk@plt>
  while (data->running == 1) {
  401d7a:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401d7e:	75 0e                	jne    401d8e <work+0x2e>
      threadwork(data);
  401d80:	48 89 df             	mov    %rbx,%rdi
  401d83:	e8 c8 fe ff ff       	call   401c50 <threadwork>
  while (data->running == 1) {
  401d88:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401d8c:	74 f2                	je     401d80 <work+0x20>
  401d8e:	8b 53 64             	mov    0x64(%rbx),%edx
  401d91:	48 8d 35 7f 02 00 00 	lea    0x27f(%rip),%rsi        # 402017 <_IO_stdin_used+0x17>
  401d98:	bf 01 00 00 00       	mov    $0x1,%edi
  401d9d:	31 c0                	xor    %eax,%eax
  401d9f:	e8 fc f2 ff ff       	call   4010a0 <__printf_chk@plt>
}
  401da4:	5b                   	pop    %rbx
  401da5:	c3                   	ret
  401da6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401db0 <work2>:
  while (data->running == 1) {
  401db0:	eb 0b                	jmp    401dbd <work2+0xd>
  401db2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  401db8:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  401dbd:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  401dc1:	74 f5                	je     401db8 <work2+0x8>
}
  401dc3:	c3                   	ret

Disassembly of section .fini:

0000000000401dc4 <_fini>:
  401dc4:	f3 0f 1e fa          	endbr64
  401dc8:	48 83 ec 08          	sub    $0x8,%rsp
  401dcc:	48 83 c4 08          	add    $0x8,%rsp
  401dd0:	c3                   	ret
