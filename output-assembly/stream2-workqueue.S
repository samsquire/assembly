
stream2-workqueue:     file format elf64-x86-64


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
  401020:	ff 35 62 2f 00 00    	push   0x2f62(%rip)        # 403f88 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 64 2f 00 00    	jmp    *0x2f64(%rip)        # 403f90 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <pthread_setaffinity_np@plt>:
  401030:	ff 25 62 2f 00 00    	jmp    *0x2f62(%rip)        # 403f98 <pthread_setaffinity_np@GLIBC_2.34>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <puts@plt>:
  401040:	ff 25 5a 2f 00 00    	jmp    *0x2f5a(%rip)        # 403fa0 <puts@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <clock_gettime@plt>:
  401050:	ff 25 52 2f 00 00    	jmp    *0x2f52(%rip)        # 403fa8 <clock_gettime@GLIBC_2.17>
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

0000000000401080 <memset@plt>:
  401080:	ff 25 3a 2f 00 00    	jmp    *0x2f3a(%rip)        # 403fc0 <memset@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <calloc@plt>:
  401090:	ff 25 32 2f 00 00    	jmp    *0x2f32(%rip)        # 403fc8 <calloc@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <__printf_chk@plt>:
  4010a0:	ff 25 2a 2f 00 00    	jmp    *0x2f2a(%rip)        # 403fd0 <__printf_chk@GLIBC_2.3.4>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <pthread_create@plt>:
  4010b0:	ff 25 22 2f 00 00    	jmp    *0x2f22(%rip)        # 403fd8 <pthread_create@GLIBC_2.34>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <posix_memalign@plt>:
  4010c0:	ff 25 1a 2f 00 00    	jmp    *0x2f1a(%rip)        # 403fe0 <posix_memalign@GLIBC_2.2.5>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010d0 <pthread_join@plt>:
  4010d0:	ff 25 12 2f 00 00    	jmp    *0x2f12(%rip)        # 403fe8 <pthread_join@GLIBC_2.34>
  4010d6:	68 0a 00 00 00       	push   $0xa
  4010db:	e9 40 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

00000000004010e0 <main>:
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
}

int main(int argc, char **argv) {
  4010e0:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4010e2:	ba 08 00 00 00       	mov    $0x8,%edx
  4010e7:	bf 01 00 00 00       	mov    $0x1,%edi
  4010ec:	48 8d 35 34 0f 00 00 	lea    0xf34(%rip),%rsi        # 402027 <_IO_stdin_used+0x27>
  4010f3:	41 56                	push   %r14
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  
  long * globalwrite;
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  data[0].works = works;
  4010f5:	41 be 01 00 00 00    	mov    $0x1,%r14d
int main(int argc, char **argv) {
  4010fb:	41 55                	push   %r13
  4010fd:	4d 89 f5             	mov    %r14,%r13
  401100:	41 54                	push   %r12
  char *works = calloc(worksize, sizeof(char));
  401102:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
int main(int argc, char **argv) {
  401108:	55                   	push   %rbp
  401109:	53                   	push   %rbx
  40110a:	48 83 ec 78          	sub    $0x78,%rsp
  40110e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401117:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  40111c:	31 c0                	xor    %eax,%eax
  40111e:	e8 7d ff ff ff       	call   4010a0 <__printf_chk@plt>
  401123:	ba 04 00 00 00       	mov    $0x4,%edx
  401128:	48 8d 35 0a 0f 00 00 	lea    0xf0a(%rip),%rsi        # 402039 <_IO_stdin_used+0x39>
  40112f:	31 c0                	xor    %eax,%eax
  401131:	bf 01 00 00 00       	mov    $0x1,%edi
  401136:	e8 65 ff ff ff       	call   4010a0 <__printf_chk@plt>
  40113b:	ba 20 00 00 00       	mov    $0x20,%edx
  401140:	48 8d 35 ee 0e 00 00 	lea    0xeee(%rip),%rsi        # 402035 <_IO_stdin_used+0x35>
  401147:	31 c0                	xor    %eax,%eax
  401149:	bf 01 00 00 00       	mov    $0x1,%edi
  40114e:	e8 4d ff ff ff       	call   4010a0 <__printf_chk@plt>
  401153:	ba 0f 00 00 00       	mov    $0xf,%edx
  401158:	48 8d 35 e9 0e 00 00 	lea    0xee9(%rip),%rsi        # 402048 <_IO_stdin_used+0x48>
  40115f:	31 c0                	xor    %eax,%eax
  401161:	bf 01 00 00 00       	mov    $0x1,%edi
  401166:	e8 35 ff ff ff       	call   4010a0 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40116b:	be 08 00 00 00       	mov    $0x8,%esi
  401170:	bf 0f 00 00 00       	mov    $0xf,%edi
  401175:	e8 16 ff ff ff       	call   401090 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  40117a:	be 38 00 00 00       	mov    $0x38,%esi
  40117f:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401184:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401189:	e8 02 ff ff ff       	call   401090 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40118e:	be 00 3c 00 00       	mov    $0x3c00,%esi
  401193:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401198:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40119d:	e8 ee fe ff ff       	call   401090 <calloc@plt>
  char *works = calloc(worksize, sizeof(char));
  4011a2:	4c 89 e7             	mov    %r12,%rdi
  4011a5:	be 01 00 00 00       	mov    $0x1,%esi
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011aa:	48 89 c3             	mov    %rax,%rbx
  char *works = calloc(worksize, sizeof(char));
  4011ad:	e8 de fe ff ff       	call   401090 <calloc@plt>
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  4011b2:	4c 89 e2             	mov    %r12,%rdx
  4011b5:	be ff ff ff ff       	mov    $0xffffffff,%esi
  4011ba:	49 89 de             	mov    %rbx,%r14
  4011bd:	48 89 c7             	mov    %rax,%rdi
  4011c0:	48 89 c5             	mov    %rax,%rbp
  4011c3:	e8 b8 fe ff ff       	call   401080 <memset@plt>
  4011c8:	4c 89 e2             	mov    %r12,%rdx
  4011cb:	bf 01 00 00 00       	mov    $0x1,%edi
  4011d0:	31 c0                	xor    %eax,%eax
  4011d2:	48 8d 35 84 0e 00 00 	lea    0xe84(%rip),%rsi        # 40205d <_IO_stdin_used+0x5d>
  4011d9:	e8 c2 fe ff ff       	call   4010a0 <__printf_chk@plt>
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4011de:	be 20 00 00 00       	mov    $0x20,%esi
  4011e3:	bf 64 00 00 00       	mov    $0x64,%edi
  4011e8:	e8 a3 fe ff ff       	call   401090 <calloc@plt>
  4011ed:	31 d2                	xor    %edx,%edx
  4011ef:	bf 01 00 00 00       	mov    $0x1,%edi
  4011f4:	48 8d 35 73 0e 00 00 	lea    0xe73(%rip),%rsi        # 40206e <_IO_stdin_used+0x6e>
  4011fb:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  401200:	31 c0                	xor    %eax,%eax
  401202:	e8 99 fe ff ff       	call   4010a0 <__printf_chk@plt>
  401207:	4c 89 e2             	mov    %r12,%rdx
  40120a:	bf 01 00 00 00       	mov    $0x1,%edi
  40120f:	31 c0                	xor    %eax,%eax
  401211:	48 8d 35 62 0e 00 00 	lea    0xe62(%rip),%rsi        # 40207a <_IO_stdin_used+0x7a>
  401218:	e8 83 fe ff ff       	call   4010a0 <__printf_chk@plt>
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  40121d:	be 04 00 00 00       	mov    $0x4,%esi
  401222:	bf 0f 00 00 00       	mov    $0xf,%edi
  401227:	e8 64 fe ff ff       	call   401090 <calloc@plt>
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  40122c:	48 8d 7c 24 38       	lea    0x38(%rsp),%rdi
  401231:	ba 00 02 00 00       	mov    $0x200,%edx
  401236:	be 80 00 00 00       	mov    $0x80,%esi
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  40123b:	49 89 c4             	mov    %rax,%r12
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  40123e:	e8 7d fe ff ff       	call   4010c0 <posix_memalign@plt>
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  401243:	be 08 00 00 00       	mov    $0x8,%esi
  401248:	bf 0f 00 00 00       	mov    $0xf,%edi
  40124d:	85 c0                	test   %eax,%eax
  40124f:	b8 00 00 00 00       	mov    $0x0,%eax
  401254:	48 0f 44 44 24 38    	cmove  0x38(%rsp),%rax
  40125a:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  40125f:	e8 2c fe ff ff       	call   401090 <calloc@plt>
  data[0].works = works;
  401264:	48 89 6b 70          	mov    %rbp,0x70(%rbx)
  401268:	31 ed                	xor    %ebp,%ebp
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  40126a:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  for (int x = 0; x < threadsize ; x++) {
  40126f:	90                   	nop
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401270:	be 80 00 00 00       	mov    $0x80,%esi
  401275:	bf 01 00 00 00       	mov    $0x1,%edi
  40127a:	44 89 2c 24          	mov    %r13d,(%rsp)
  40127e:	45 8d 7d ff          	lea    -0x1(%r13),%r15d
  401282:	e8 09 fe ff ff       	call   401090 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  401287:	44 89 e9             	mov    %r13d,%ecx
  40128a:	be 01 00 00 00       	mov    $0x1,%esi
  40128f:	44 89 fa             	mov    %r15d,%edx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401292:	49 89 46 78          	mov    %rax,0x78(%r14)
    CPU_SET(cpu += 1, data[x].cpu_set);
  401296:	48 d3 e6             	shl    %cl,%rsi
  401299:	8b 0c 24             	mov    (%rsp),%ecx
  40129c:	bf 01 00 00 00       	mov    $0x1,%edi
  4012a1:	48 09 30             	or     %rsi,(%rax)
  4012a4:	48 8d 35 fd 0e 00 00 	lea    0xefd(%rip),%rsi        # 4021a8 <_IO_stdin_used+0x1a8>
  4012ab:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  4012ad:	49 81 c6 00 04 00 00 	add    $0x400,%r14
  4012b4:	e8 e7 fd ff ff       	call   4010a0 <__printf_chk@plt>
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].bucketstart = x * buckets ;
    data[x].globalwrite = globalwrite;
  4012b9:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    data[x].chunksize = chunksize;
    data[x].chunkslen = chunkslen;
    data[x].newmask = 0;
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].mystream = 1 + (x / 4);
  4012be:	44 89 fa             	mov    %r15d,%edx
    data[x].bucketstart = x * buckets ;
  4012c1:	41 89 ae 98 fc ff ff 	mov    %ebp,-0x368(%r14)
    data[x].mystream = 1 + (x / 4);
  4012c8:	c1 fa 02             	sar    $0x2,%edx
    data[x].read = 0;
  4012cb:	66 0f 6f 0d 2d 0f 00 00 	movdqa 0xf2d(%rip),%xmm1        # 402200 <_IO_stdin_used+0x200>
    data[x].chunkslen = chunkslen;
  4012d3:	66 0f 6f 15 35 0f 00 00 	movdqa 0xf35(%rip),%xmm2        # 402210 <_IO_stdin_used+0x210>
    data[x].loglevel = debug;
  4012db:	41 c7 86 80 fc ff ff 00 00 00 00 	movl   $0x0,-0x380(%r14)
    data[x].globalwrite = globalwrite;
  4012e6:	49 89 46 80          	mov    %rax,-0x80(%r14)
    data[x].mystream = 1 + (x / 4);
  4012ea:	83 c2 01             	add    $0x1,%edx
    data[x].running = 1;
  4012ed:	48 8b 05 04 0f 00 00 	mov    0xf04(%rip),%rax        # 4021f8 <_IO_stdin_used+0x1f8>
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4012f4:	be 30 00 00 00       	mov    $0x30,%esi
    data[x].prevread = threadsize;
  4012f9:	66 0f 6f 1d 1f 0f 00 00 	movdqa 0xf1f(%rip),%xmm3        # 402220 <_IO_stdin_used+0x220>
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401301:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].threadindex = x;
  401306:	45 89 be 64 fc ff ff 	mov    %r15d,-0x39c(%r14)
  for (int x = 0; x < threadsize ; x++) {
  40130d:	81 c5 11 11 11 11    	add    $0x11111111,%ebp
    data[x].running = 1;
  401313:	49 89 86 5c fc ff ff 	mov    %rax,-0x3a4(%r14)
    data[x].freelist = freelist;
  40131a:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    data[x].availables = buckets;
  40131f:	41 c7 86 94 fc ff ff 11 11 11 11 	movl   $0x11111111,-0x36c(%r14)
    data[x].threadsize = threadsize;
  40132a:	41 c7 86 68 fc ff ff 0f 00 00 00 	movl   $0xf,-0x398(%r14)
    data[x].readies = readies;
  401335:	4d 89 a6 20 fc ff ff 	mov    %r12,-0x3e0(%r14)
    data[x].readies[x] = 0;
  40133c:	43 c7 44 ac fc 00 00 00 00 	movl   $0x0,-0x4(%r12,%r13,4)
  for (int x = 0; x < threadsize ; x++) {
  401345:	49 83 c5 01          	add    $0x1,%r13
    data[x].mystream = 1 + (x / 4);
  401349:	41 89 56 8c          	mov    %edx,-0x74(%r14)
    data[x].buckets = buckets;
  40134d:	41 c7 86 90 fc ff ff 11 11 11 11 	movl   $0x11111111,-0x370(%r14)
    data[x].main = &data[0];
  401358:	49 89 9e 28 fc ff ff 	mov    %rbx,-0x3d8(%r14)
    data[x].threads = data;
  40135f:	49 89 9e 30 fc ff ff 	mov    %rbx,-0x3d0(%r14)
    data[x].readcursor = threadsize - 1;
  401366:	41 c7 86 00 fe ff ff 0e 00 00 00 	movl   $0xe,-0x200(%r14)
    data[x].writecursor = threadsize - 1;
  401371:	41 c7 86 80 fd ff ff 0e 00 00 00 	movl   $0xe,-0x280(%r14)
    data[x].freelist = freelist;
  40137c:	49 89 86 a0 fc ff ff 	mov    %rax,-0x360(%r14)
    data[x].newmask = 0;
  401383:	41 c7 86 c8 fc ff ff 00 00 00 00 	movl   $0x0,-0x338(%r14)
    data[x].thiswrite = threadsize;
  40138e:	41 c7 86 28 ff ff ff 0f 00 00 00 	movl   $0xf,-0xd8(%r14)
    data[x].read = 0;
  401399:	41 0f 29 8e 00 fc ff ff 	movaps %xmm1,-0x400(%r14)
    data[x].chunkslen = chunkslen;
  4013a1:	41 0f 11 96 b8 fc ff ff 	movups %xmm2,-0x348(%r14)
    data[x].prevread = threadsize;
  4013a9:	41 0f 11 9e 08 ff ff ff 	movups %xmm3,-0xf8(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4013b1:	e8 da fc ff ff       	call   401090 <calloc@plt>
    data[x].epochssize = epochs;
    data[x].globalread = globalread;
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  4013b6:	be 30 00 00 00       	mov    $0x30,%esi
  4013bb:	bf 10 27 00 00       	mov    $0x2710,%edi
    data[x].epochssize = epochs;
  4013c0:	41 c7 86 20 ff ff ff 80 96 98 00 	movl   $0x989680,-0xe0(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4013cb:	49 89 86 18 ff ff ff 	mov    %rax,-0xe8(%r14)
    data[x].globalread = globalread;
  4013d2:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  4013d7:	49 89 86 48 ff ff ff 	mov    %rax,-0xb8(%r14)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  4013de:	e8 ad fc ff ff       	call   401090 <calloc@plt>
  4013e3:	49 89 86 30 ff ff ff 	mov    %rax,-0xd0(%r14)
  for (int x = 0; x < threadsize ; x++) {
  4013ea:	49 83 fd 10          	cmp    $0x10,%r13
  4013ee:	0f 85 7c fe ff ff    	jne    401270 <main+0x190>
  4013f4:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
  4013f9:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
  4013fe:	48 89 1c 24          	mov    %rbx,(%rsp)
  401402:	49 c7 c5 50 1f 40 00 	mov    $0x401f50,%r13
  401409:	48 8d 85 48 03 00 00 	lea    0x348(%rbp),%rax
  401410:	4d 89 fc             	mov    %r15,%r12
  401413:	49 89 c6             	mov    %rax,%r14
  401416:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  401420:	48 89 d9             	mov    %rbx,%rcx
  401423:	48 89 ee             	mov    %rbp,%rsi
  401426:	4c 89 ff             	mov    %r15,%rdi
  401429:	4c 89 ea             	mov    %r13,%rdx
  40142c:	e8 7f fc ff ff       	call   4010b0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401431:	48 8b 53 78          	mov    0x78(%rbx),%rdx
  401435:	49 8b 3f             	mov    (%r15),%rdi
  401438:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  40143d:	48 83 c5 38          	add    $0x38,%rbp
  401441:	49 83 c7 08          	add    $0x8,%r15
  401445:	48 81 c3 00 04 00 00 	add    $0x400,%rbx
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  40144c:	e8 df fb ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  401451:	4c 39 f5             	cmp    %r14,%rbp
  401454:	75 ca                	jne    401420 <main+0x340>
  }
  
  struct timespec time = {
  401456:	48 8b 1c 24          	mov    (%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  40145a:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  40145f:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec time = {
  401464:	66 0f 6f 05 c4 0d 00 00 	movdqa 0xdc4(%rip),%xmm0        # 402230 <_IO_stdin_used+0x230>
  40146c:	4c 8d 6c 24 30       	lea    0x30(%rsp),%r13
  401471:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  401476:	66 0f ef c0          	pxor   %xmm0,%xmm0
  40147a:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  40147f:	e8 ec fb ff ff       	call   401070 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  401484:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
  401489:	c7 43 5c 00 00 00 00 	movl   $0x0,0x5c(%rbx)
  401490:	c7 83 5c 04 00 00 00 00 00 00 	movl   $0x0,0x45c(%rbx)
  40149a:	c7 83 5c 08 00 00 00 00 00 00 	movl   $0x0,0x85c(%rbx)
  4014a4:	48 83 c5 78          	add    $0x78,%rbp
  4014a8:	c7 83 5c 0c 00 00 00 00 00 00 	movl   $0x0,0xc5c(%rbx)
  4014b2:	c7 83 5c 10 00 00 00 00 00 00 	movl   $0x0,0x105c(%rbx)
  4014bc:	c7 83 5c 14 00 00 00 00 00 00 	movl   $0x0,0x145c(%rbx)
  4014c6:	c7 83 5c 18 00 00 00 00 00 00 	movl   $0x0,0x185c(%rbx)
  4014d0:	c7 83 5c 1c 00 00 00 00 00 00 	movl   $0x0,0x1c5c(%rbx)
  4014da:	c7 83 5c 20 00 00 00 00 00 00 	movl   $0x0,0x205c(%rbx)
  4014e4:	c7 83 5c 24 00 00 00 00 00 00 	movl   $0x0,0x245c(%rbx)
  4014ee:	c7 83 5c 28 00 00 00 00 00 00 	movl   $0x0,0x285c(%rbx)
  4014f8:	c7 83 5c 2c 00 00 00 00 00 00 	movl   $0x0,0x2c5c(%rbx)
  401502:	c7 83 5c 30 00 00 00 00 00 00 	movl   $0x0,0x305c(%rbx)
  40150c:	c7 83 5c 34 00 00 00 00 00 00 	movl   $0x0,0x345c(%rbx)
  401516:	c7 83 5c 38 00 00 00 00 00 00 	movl   $0x0,0x385c(%rbx)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401520:	49 8b 3c 24          	mov    (%r12),%rdi
  401524:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  401527:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  40152b:	e8 a0 fb ff ff       	call   4010d0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401530:	4c 39 e5             	cmp    %r12,%rbp
  401533:	75 eb                	jne    401520 <main+0x440>
  401535:	48 8d 3d 4a 0b 00 00 	lea    0xb4a(%rip),%rdi        # 402086 <_IO_stdin_used+0x86>
  40153c:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  401540:	45 31 e4             	xor    %r12d,%r12d
  401543:	e8 f8 fa ff ff       	call   401040 <puts@plt>
  long sends = 1;
  for (int x = 0; x < threadsize; x++) {
  401548:	4c 8d b3 48 3c 00 00 	lea    0x3c48(%rbx),%r14
  40154f:	4c 8d 2d 45 0b 00 00 	lea    0xb45(%rip),%r13        # 40209b <_IO_stdin_used+0x9b>
  401556:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401560:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401564:	4c 89 ee             	mov    %r13,%rsi
  401567:	bf 01 00 00 00       	mov    $0x1,%edi
  40156c:	31 c0                	xor    %eax,%eax
  40156e:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
  401575:	e8 26 fb ff ff       	call   4010a0 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  40157a:	4c 03 a5 00 fc ff ff 	add    -0x400(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  401581:	49 39 ee             	cmp    %rbp,%r14
  401584:	75 da                	jne    401560 <main+0x480>
  401586:	4c 89 e2             	mov    %r12,%rdx
  401589:	48 8d 35 16 0b 00 00 	lea    0xb16(%rip),%rsi        # 4020a6 <_IO_stdin_used+0xa6>
  401590:	bf 01 00 00 00       	mov    $0x1,%edi
  401595:	31 c0                	xor    %eax,%eax
  401597:	e8 04 fb ff ff       	call   4010a0 <__printf_chk@plt>
  40159c:	4c 89 e2             	mov    %r12,%rdx
  40159f:	bf 01 00 00 00       	mov    $0x1,%edi
  4015a4:	31 c0                	xor    %eax,%eax
  4015a6:	48 8d 35 04 0b 00 00 	lea    0xb04(%rip),%rsi        # 4020b1 <_IO_stdin_used+0xb1>
  4015ad:	48 8d ab 98 03 00 00 	lea    0x398(%rbx),%rbp
  4015b4:	e8 e7 fa ff ff       	call   4010a0 <__printf_chk@plt>
  }
  printf("freq: %ld\n", freq/ seconds);
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  4015b9:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  4015be:	48 8d 35 fa 0a 00 00 	lea    0xafa(%rip),%rsi        # 4020bf <_IO_stdin_used+0xbf>
  4015c5:	bf 01 00 00 00       	mov    $0x1,%edi
  4015ca:	48 99                	cqto
  4015cc:	4c 8d b3 98 3f 00 00 	lea    0x3f98(%rbx),%r14
  4015d3:	4c 8d 2d 2a 0b 00 00 	lea    0xb2a(%rip),%r13        # 402104 <_IO_stdin_used+0x104>
  4015da:	49 f7 fc             	idiv   %r12
  4015dd:	49 89 c4             	mov    %rax,%r12
  4015e0:	48 89 c2             	mov    %rax,%rdx
  4015e3:	31 c0                	xor    %eax,%eax
  4015e5:	e8 b6 fa ff ff       	call   4010a0 <__printf_chk@plt>
  4015ea:	4c 89 e2             	mov    %r12,%rdx
  4015ed:	bf 01 00 00 00       	mov    $0x1,%edi
  4015f2:	31 c0                	xor    %eax,%eax
  4015f4:	48 8d 35 d8 0a 00 00 	lea    0xad8(%rip),%rsi        # 4020d3 <_IO_stdin_used+0xd3>
  4015fb:	e8 a0 fa ff ff       	call   4010a0 <__printf_chk@plt>
  401600:	4c 89 e2             	mov    %r12,%rdx
  401603:	bf 01 00 00 00       	mov    $0x1,%edi
  401608:	31 c0                	xor    %eax,%eax
  40160a:	48 8d 35 e0 0a 00 00 	lea    0xae0(%rip),%rsi        # 4020f1 <_IO_stdin_used+0xf1>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  
  long goods = 0;
  401611:	45 31 e4             	xor    %r12d,%r12d
  401614:	e8 87 fa ff ff       	call   4010a0 <__printf_chk@plt>

  for (int x = 0; x < threadsize; x++) {
  401619:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401620:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401624:	4c 89 ee             	mov    %r13,%rsi
  401627:	bf 01 00 00 00       	mov    $0x1,%edi
  40162c:	31 c0                	xor    %eax,%eax
  40162e:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
  401635:	e8 66 fa ff ff       	call   4010a0 <__printf_chk@plt>
    printf("%ld successreads\n", data[x].successreads);
    goods += data[x].successreads;
  40163a:	4c 03 a5 00 fc ff ff 	add    -0x400(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  401641:	4c 39 f5             	cmp    %r14,%rbp
  401644:	75 da                	jne    401620 <main+0x540>
  401646:	4c 89 e2             	mov    %r12,%rdx
  401649:	48 8d 35 c6 0a 00 00 	lea    0xac6(%rip),%rsi        # 402116 <_IO_stdin_used+0x116>
  401650:	31 c0                	xor    %eax,%eax
  }
  printf("%d good reads\n", goods);
  long freq_writes = 0;
  401652:	45 31 e4             	xor    %r12d,%r12d
  401655:	bf 01 00 00 00       	mov    $0x1,%edi
  40165a:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  40165e:	4c 8d b3 50 3c 00 00 	lea    0x3c50(%rbx),%r14
  401665:	e8 36 fa ff ff       	call   4010a0 <__printf_chk@plt>
  
  for (int x = 0; x < threadsize; x++) {
  40166a:	4c 8d 2d b4 0a 00 00 	lea    0xab4(%rip),%r13        # 402125 <_IO_stdin_used+0x125>
  401671:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    freq_writes += data[x].freq_writes;
  401678:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  40167c:	4c 89 ee             	mov    %r13,%rsi
  40167f:	bf 01 00 00 00       	mov    $0x1,%edi
  401684:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  401686:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
    freq_writes += data[x].freq_writes;
  40168d:	49 01 d4             	add    %rdx,%r12
  401690:	e8 0b fa ff ff       	call   4010a0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  401695:	49 39 ee             	cmp    %rbp,%r14
  401698:	75 de                	jne    401678 <main+0x598>
  40169a:	4c 89 e2             	mov    %r12,%rdx
  40169d:	48 8d 35 8d 0a 00 00 	lea    0xa8d(%rip),%rsi        # 402131 <_IO_stdin_used+0x131>
  4016a4:	bf 01 00 00 00       	mov    $0x1,%edi
  4016a9:	31 c0                	xor    %eax,%eax
  4016ab:	e8 f0 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  4016b0:	4c 89 e2             	mov    %r12,%rdx
  4016b3:	bf 01 00 00 00       	mov    $0x1,%edi
  4016b8:	31 c0                	xor    %eax,%eax
  4016ba:	48 8d 35 82 0a 00 00 	lea    0xa82(%rip),%rsi        # 402143 <_IO_stdin_used+0x143>
  4016c1:	48 8d 2d 06 0a 00 00 	lea    0xa06(%rip),%rbp        # 4020ce <_IO_stdin_used+0xce>
  4016c8:	e8 d3 f9 ff ff       	call   4010a0 <__printf_chk@plt>
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  4016cd:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  4016d2:	bf 01 00 00 00       	mov    $0x1,%edi
  4016d7:	48 8d 35 7d 0a 00 00 	lea    0xa7d(%rip),%rsi        # 40215b <_IO_stdin_used+0x15b>
  4016de:	48 99                	cqto
  4016e0:	49 f7 fc             	idiv   %r12
  4016e3:	49 89 c4             	mov    %rax,%r12
  4016e6:	48 89 c2             	mov    %rax,%rdx
  4016e9:	31 c0                	xor    %eax,%eax
  4016eb:	e8 b0 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  4016f0:	4c 89 e2             	mov    %r12,%rdx
  4016f3:	bf 01 00 00 00       	mov    $0x1,%edi
  4016f8:	31 c0                	xor    %eax,%eax
  4016fa:	48 8d 35 c7 0a 00 00 	lea    0xac7(%rip),%rsi        # 4021c8 <_IO_stdin_used+0x1c8>
  401701:	e8 9a f9 ff ff       	call   4010a0 <__printf_chk@plt>
  401706:	4c 89 e2             	mov    %r12,%rdx
  401709:	bf 01 00 00 00       	mov    $0x1,%edi
  40170e:	31 c0                	xor    %eax,%eax
  401710:	48 8d 35 5f 0a 00 00 	lea    0xa5f(%rip),%rsi        # 402176 <_IO_stdin_used+0x176>
  401717:	e8 84 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  40171c:	48 8d 3d 6d 0a 00 00 	lea    0xa6d(%rip),%rdi        # 402190 <_IO_stdin_used+0x190>
  401723:	e8 18 f9 ff ff       	call   401040 <puts@plt>
  401728:	48 89 ee             	mov    %rbp,%rsi
  40172b:	bf 01 00 00 00       	mov    $0x1,%edi
  401730:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  401732:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  401739:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  401740:	e8 5b f9 ff ff       	call   4010a0 <__printf_chk@plt>
  401745:	48 89 ee             	mov    %rbp,%rsi
  401748:	bf 01 00 00 00       	mov    $0x1,%edi
  40174d:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  40174f:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  401756:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  40175d:	e8 3e f9 ff ff       	call   4010a0 <__printf_chk@plt>
  401762:	48 89 ee             	mov    %rbp,%rsi
  401765:	bf 01 00 00 00       	mov    $0x1,%edi
  40176a:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  40176c:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  401773:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  40177a:	e8 21 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  40177f:	48 89 ee             	mov    %rbp,%rsi
  401782:	bf 01 00 00 00       	mov    $0x1,%edi
  401787:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  401789:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  401790:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  401797:	e8 04 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  40179c:	48 89 ee             	mov    %rbp,%rsi
  40179f:	bf 01 00 00 00       	mov    $0x1,%edi
  4017a4:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  4017a6:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  4017ad:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  4017b4:	e8 e7 f8 ff ff       	call   4010a0 <__printf_chk@plt>
  4017b9:	48 89 ee             	mov    %rbp,%rsi
  4017bc:	bf 01 00 00 00       	mov    $0x1,%edi
  4017c1:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  4017c3:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  4017ca:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  4017d1:	e8 ca f8 ff ff       	call   4010a0 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  4017d6:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  4017dd:	bf 01 00 00 00       	mov    $0x1,%edi
  4017e2:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  4017e9:	48 8d 35 ad 09 00 00 	lea    0x9ad(%rip),%rsi        # 40219d <_IO_stdin_used+0x19d>
  4017f0:	31 c0                	xor    %eax,%eax
  4017f2:	e8 a9 f8 ff ff       	call   4010a0 <__printf_chk@plt>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  4017f7:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  4017fc:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401805:	75 11                	jne    401818 <main+0x738>
  401807:	48 83 c4 78          	add    $0x78,%rsp
  40180b:	31 c0                	xor    %eax,%eax
  40180d:	5b                   	pop    %rbx
  40180e:	5d                   	pop    %rbp
  40180f:	41 5c                	pop    %r12
  401811:	41 5d                	pop    %r13
  401813:	41 5e                	pop    %r14
  401815:	41 5f                	pop    %r15
  401817:	c3                   	ret
  401818:	e8 43 f8 ff ff       	call   401060 <__stack_chk_fail@plt>
  40181d:	0f 1f 00             	nopl   (%rax)

0000000000401820 <set_fast_math>:
  401820:	f3 0f 1e fa          	endbr64
  401824:	0f ae 5c 24 fc       	stmxcsr -0x4(%rsp)
  401829:	81 4c 24 fc 40 80 00 00 	orl    $0x8040,-0x4(%rsp)
  401831:	0f ae 54 24 fc       	ldmxcsr -0x4(%rsp)
  401836:	c3                   	ret
  401837:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000401840 <_start>:
  401840:	f3 0f 1e fa          	endbr64
  401844:	31 ed                	xor    %ebp,%ebp
  401846:	49 89 d1             	mov    %rdx,%r9
  401849:	5e                   	pop    %rsi
  40184a:	48 89 e2             	mov    %rsp,%rdx
  40184d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401851:	50                   	push   %rax
  401852:	54                   	push   %rsp
  401853:	45 31 c0             	xor    %r8d,%r8d
  401856:	31 c9                	xor    %ecx,%ecx
  401858:	48 c7 c7 e0 10 40 00 	mov    $0x4010e0,%rdi
  40185f:	ff 15 8b 27 00 00    	call   *0x278b(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  401865:	f4                   	hlt
  401866:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401870 <_dl_relocate_static_pie>:
  401870:	f3 0f 1e fa          	endbr64
  401874:	c3                   	ret
  401875:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40187f:	90                   	nop

0000000000401880 <deregister_tm_clones>:
  401880:	b8 10 40 40 00       	mov    $0x404010,%eax
  401885:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  40188b:	74 13                	je     4018a0 <deregister_tm_clones+0x20>
  40188d:	b8 00 00 00 00       	mov    $0x0,%eax
  401892:	48 85 c0             	test   %rax,%rax
  401895:	74 09                	je     4018a0 <deregister_tm_clones+0x20>
  401897:	bf 10 40 40 00       	mov    $0x404010,%edi
  40189c:	ff e0                	jmp    *%rax
  40189e:	66 90                	xchg   %ax,%ax
  4018a0:	c3                   	ret
  4018a1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4018ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004018b0 <register_tm_clones>:
  4018b0:	be 10 40 40 00       	mov    $0x404010,%esi
  4018b5:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  4018bc:	48 89 f0             	mov    %rsi,%rax
  4018bf:	48 c1 ee 3f          	shr    $0x3f,%rsi
  4018c3:	48 c1 f8 03          	sar    $0x3,%rax
  4018c7:	48 01 c6             	add    %rax,%rsi
  4018ca:	48 d1 fe             	sar    %rsi
  4018cd:	74 11                	je     4018e0 <register_tm_clones+0x30>
  4018cf:	b8 00 00 00 00       	mov    $0x0,%eax
  4018d4:	48 85 c0             	test   %rax,%rax
  4018d7:	74 07                	je     4018e0 <register_tm_clones+0x30>
  4018d9:	bf 10 40 40 00       	mov    $0x404010,%edi
  4018de:	ff e0                	jmp    *%rax
  4018e0:	c3                   	ret
  4018e1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4018ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004018f0 <__do_global_dtors_aux>:
  4018f0:	f3 0f 1e fa          	endbr64
  4018f4:	80 3d 15 27 00 00 00 	cmpb   $0x0,0x2715(%rip)        # 404010 <__TMC_END__>
  4018fb:	75 13                	jne    401910 <__do_global_dtors_aux+0x20>
  4018fd:	55                   	push   %rbp
  4018fe:	48 89 e5             	mov    %rsp,%rbp
  401901:	e8 7a ff ff ff       	call   401880 <deregister_tm_clones>
  401906:	c6 05 03 27 00 00 01 	movb   $0x1,0x2703(%rip)        # 404010 <__TMC_END__>
  40190d:	5d                   	pop    %rbp
  40190e:	c3                   	ret
  40190f:	90                   	nop
  401910:	c3                   	ret
  401911:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40191c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401920 <frame_dummy>:
  401920:	f3 0f 1e fa          	endbr64
  401924:	eb 8a                	jmp    4018b0 <register_tm_clones>
  401926:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401930 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  401930:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  401934:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  401937:	7e 77                	jle    4019b0 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  401939:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  40193d:	55                   	push   %rbp
  40193e:	49 89 f2             	mov    %rsi,%r10
  401941:	49 89 d3             	mov    %rdx,%r11
  401944:	53                   	push   %rbx
  401945:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  401948:	48 8b 98 20 04 00 00 	mov    0x420(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  40194f:	b8 01 00 00 00       	mov    $0x1,%eax
  401954:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  401958:	48 63 d0             	movslq %eax,%rdx
  40195b:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  40195e:	85 d2                	test   %edx,%edx
  401960:	40 0f 94 c6          	sete   %sil
  401964:	f6 c2 04             	test   $0x4,%dl
  401967:	75 05                	jne    40196e <pollthreads+0x3e>
  401969:	40 84 f6             	test   %sil,%sil
  40196c:	74 0d                	je     40197b <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  40196e:	49 63 08             	movslq (%r8),%rcx
  401971:	8d 69 01             	lea    0x1(%rcx),%ebp
  401974:	41 89 28             	mov    %ebp,(%r8)
  401977:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  40197b:	83 e2 08             	and    $0x8,%edx
  40197e:	75 05                	jne    401985 <pollthreads+0x55>
  401980:	40 84 f6             	test   %sil,%sil
  401983:	74 1b                	je     4019a0 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  401985:	48 63 17             	movslq (%rdi),%rdx
  401988:	8d 4a 01             	lea    0x1(%rdx),%ecx
  40198b:	89 0f                	mov    %ecx,(%rdi)
  40198d:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  401991:	83 c0 01             	add    $0x1,%eax
  401994:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401998:	7f be                	jg     401958 <pollthreads+0x28>
}
  40199a:	31 c0                	xor    %eax,%eax
  40199c:	5b                   	pop    %rbx
  40199d:	5d                   	pop    %rbp
  40199e:	c3                   	ret
  40199f:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  4019a0:	83 c0 01             	add    $0x1,%eax
  4019a3:	41 39 41 68          	cmp    %eax,0x68(%r9)
  4019a7:	7f af                	jg     401958 <pollthreads+0x28>
}
  4019a9:	31 c0                	xor    %eax,%eax
  4019ab:	5b                   	pop    %rbx
  4019ac:	5d                   	pop    %rbp
  4019ad:	c3                   	ret
  4019ae:	66 90                	xchg   %ax,%ax
  4019b0:	31 c0                	xor    %eax,%eax
  4019b2:	c3                   	ret
  4019b3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4019be:	66 90                	xchg   %ax,%ax

00000000004019c0 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  4019c0:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4019c3:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
      if (*availableidx == 0) {
  4019ca:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4019cd:	48 83 c7 01          	add    $0x1,%rdi
  4019d1:	48 85 ff             	test   %rdi,%rdi
  4019d4:	7e 66                	jle    401a3c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  4019d6:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4019dd:	31 c9                	xor    %ecx,%ecx
  4019df:	45 31 c9             	xor    %r9d,%r9d
  4019e2:	31 c0                	xor    %eax,%eax
  4019e4:	eb 18                	jmp    4019fe <findavailable+0x3e>
  4019e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4019f0:	83 c1 01             	add    $0x1,%ecx
  4019f3:	48 63 c1             	movslq %ecx,%rax
  4019f6:	49 89 c1             	mov    %rax,%r9
  4019f9:	48 39 f8             	cmp    %rdi,%rax
  4019fc:	7d 3e                	jge    401a3c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  4019fe:	48 c1 e0 05          	shl    $0x5,%rax
  401a02:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401a08:	75 e6                	jne    4019f0 <findavailable+0x30>
         available[*availableidx] = x;
  401a0a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  401a0d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401a11:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401a15:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401a18:	41 8b 43 68          	mov    0x68(%r11),%eax
  401a1c:	01 c0                	add    %eax,%eax
  401a1e:	41 39 c0             	cmp    %eax,%r8d
  401a21:	74 19                	je     401a3c <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a23:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  401a2a:	83 c1 01             	add    $0x1,%ecx
  401a2d:	48 63 c1             	movslq %ecx,%rax
  401a30:	48 83 c7 01          	add    $0x1,%rdi
  401a34:	49 89 c1             	mov    %rax,%r9
  401a37:	48 39 f8             	cmp    %rdi,%rax
  401a3a:	7c c2                	jl     4019fe <findavailable+0x3e>
      if (*availableidx == 0) {
  401a3c:	31 c0                	xor    %eax,%eax
  401a3e:	45 85 c0             	test   %r8d,%r8d
  401a41:	0f 94 c0             	sete   %al
}
  401a44:	c3                   	ret
  401a45:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401a50 <singlewriter3>:
}
  401a50:	c3                   	ret
  401a51:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401a5c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401a60 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401a60:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  401a66:	85 c0                	test   %eax,%eax
  401a68:	74 1e                	je     401a88 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a6a:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401a6c:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a6d:	55                   	push   %rbp
  401a6e:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401a6f:	8b 77 68             	mov    0x68(%rdi),%esi
  401a72:	48 89 fb             	mov    %rdi,%rbx
  401a75:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401a78:	f7 f9                	idiv   %ecx
  401a7a:	85 d2                	test   %edx,%edx
  401a7c:	74 12                	je     401a90 <singlewriter2+0x30>
}
  401a7e:	5b                   	pop    %rbx
  401a7f:	5d                   	pop    %rbp
  401a80:	41 5c                	pop    %r12
  401a82:	c3                   	ret
  401a83:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401a88:	c3                   	ret
  401a89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct Data * thread = &data->threads[data->threadindex];
  401a90:	48 63 6f 64          	movslq 0x64(%rdi),%rbp
  401a94:	48 c1 e5 0a          	shl    $0xa,%rbp
  401a98:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401a9c:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401aa1:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401aa8:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401aac:	49 c1 e4 04          	shl    $0x4,%r12
  401ab0:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401ab7:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401abc:	e8 8f f5 ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ac1:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401ac7:	83 c0 01             	add    $0x1,%eax
  401aca:	99                   	cltd
  401acb:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  401ad1:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ad4:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401ada:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401ade:	48 8b 05 0b 07 00 00 	mov    0x70b(%rip),%rax        # 4021f0 <_IO_stdin_used+0x1f0>
  401ae5:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  401aea:	5b                   	pop    %rbx
  401aeb:	5d                   	pop    %rbp
  401aec:	41 5c                	pop    %r12
  401aee:	c3                   	ret
  401aef:	90                   	nop

0000000000401af0 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401af0:	41 55                	push   %r13
  401af2:	49 89 d5             	mov    %rdx,%r13
  401af5:	41 54                	push   %r12
  401af7:	49 89 cc             	mov    %rcx,%r12
  401afa:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401afb:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401afe:	48 89 fd             	mov    %rdi,%rbp
  401b01:	53                   	push   %rbx
  401b02:	48 89 f3             	mov    %rsi,%rbx
  401b05:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401b09:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b0d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401b16:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401b1b:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401b1d:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401b25:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  401b2b:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401b33:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401b3b:	83 c0 01             	add    $0x1,%eax
  401b3e:	99                   	cltd
  401b3f:	f7 7f 68             	idivl  0x68(%rdi)
  401b42:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401b48:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401b4d:	4c 89 e9             	mov    %r13,%rcx
  401b50:	e8 6b fe ff ff       	call   4019c0 <findavailable>
  if (fill == 1) {
  401b55:	83 f8 01             	cmp    $0x1,%eax
  401b58:	0f 84 3c 01 00 00    	je     401c9a <singlewriter+0x1aa>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401b5e:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401b63:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401b68:	4c 89 e2             	mov    %r12,%rdx
  401b6b:	4c 89 ee             	mov    %r13,%rsi
  401b6e:	48 89 ef             	mov    %rbp,%rdi
  401b71:	e8 ba fd ff ff       	call   401930 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401b76:	4c 63 44 24 0c       	movslq 0xc(%rsp),%r8
  401b7b:	45 85 c0             	test   %r8d,%r8d
  401b7e:	0f 8e 3d 01 00 00    	jle    401cc1 <singlewriter+0x1d1>
  401b84:	44 8b 4c 24 14       	mov    0x14(%rsp),%r9d
          if (assignedchunk == availableidx) {
  401b89:	31 c9                	xor    %ecx,%ecx
  401b8b:	eb 58                	jmp    401be5 <singlewriter+0xf5>
  401b8d:	0f 1f 00             	nopl   (%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b90:	48 8b 04 cb          	mov    (%rbx,%rcx,8),%rax
          int thread = readyreaders[x];
  401b94:	49 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%rdx
  401b99:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401b9c:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401ba0:	48 c1 e0 05          	shl    $0x5,%rax
  401ba4:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
          int thread = readyreaders[x];
  401bab:	48 89 d7             	mov    %rdx,%rdi
          data->threads[thread].reading = chunk;
  401bae:	48 c1 e2 0a          	shl    $0xa,%rdx
          data->threads[thread].start = start;
  401bb2:	66 0f 6e 00          	movd   (%rax),%xmm0
  401bb6:	66 0f 6e 48 08       	movd   0x8(%rax),%xmm1
          chunk->available = READING;
  401bbb:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
          data->threads[thread].reading = chunk;
  401bc2:	48 03 55 30          	add    0x30(%rbp),%rdx
          data->threads[thread].start = start;
  401bc6:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401bca:	48 89 82 a8 00 00 00 	mov    %rax,0xa8(%rdx)
          chunk->owner = thread;
  401bd1:	89 78 14             	mov    %edi,0x14(%rax)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401bd4:	83 8a c8 00 00 00 10 	orl    $0x10,0xc8(%rdx)
          data->threads[thread].start = start;
  401bdb:	66 0f d6 42 14       	movq   %xmm0,0x14(%rdx)
        for (int x = 0; x < readers ; x++) {
  401be0:	49 39 c8             	cmp    %rcx,%r8
  401be3:	74 07                	je     401bec <singlewriter+0xfc>
  401be5:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401be7:	4c 39 c9             	cmp    %r9,%rcx
  401bea:	75 a4                	jne    401b90 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401bec:	44 8b 4c 24 10       	mov    0x10(%rsp),%r9d
  401bf1:	45 85 c9             	test   %r9d,%r9d
  401bf4:	7e 68                	jle    401c5e <singlewriter+0x16e>
                if (assignedchunk  == availableidx) {
  401bf6:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
  401bfb:	41 01 f1             	add    %esi,%r9d
  401bfe:	eb 59                	jmp    401c59 <singlewriter+0x169>
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c00:	8d 7e 01             	lea    0x1(%rsi),%edi
  401c03:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401c06:	49 63 14 24          	movslq (%r12),%rdx
   for (int x = 0; x < writers ; x++) {
  401c0a:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c0e:	48 8b 04 f3          	mov    (%rbx,%rsi,8),%rax
          int thread = readywriters[x];
  401c12:	48 89 d1             	mov    %rdx,%rcx
          data->threads[thread].writing = chunk;
  401c15:	48 c1 e2 0a          	shl    $0xa,%rdx
  401c19:	48 03 55 30          	add    0x30(%rbp),%rdx
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c1d:	48 c1 e0 05          	shl    $0x5,%rax
  401c21:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
          data->threads[thread].publishstart = start;
  401c28:	66 0f 6e 00          	movd   (%rax),%xmm0
  401c2c:	66 0f 6e 50 08       	movd   0x8(%rax),%xmm2
      chunk->available = WRITING;
  401c31:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
          data->threads[thread].writing = chunk;
  401c38:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
          data->threads[thread].publishstart = start;
  401c3f:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          chunk->owner = thread;
  401c43:	89 48 14             	mov    %ecx,0x14(%rax)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401c46:	83 8a c8 00 00 00 20 	orl    $0x20,0xc8(%rdx)
          data->threads[thread].publishstart = start;
  401c4d:	66 0f d6 42 40       	movq   %xmm0,0x40(%rdx)
   for (int x = 0; x < writers ; x++) {
  401c52:	44 39 cf             	cmp    %r9d,%edi
  401c55:	74 07                	je     401c5e <singlewriter+0x16e>
  401c57:	89 fe                	mov    %edi,%esi
                if (assignedchunk  == availableidx) {
  401c59:	41 39 f0             	cmp    %esi,%r8d
  401c5c:	75 a2                	jne    401c00 <singlewriter+0x110>
      for (int x = 0; x < data->threadsize ; x++) {
  401c5e:	8b 7d 68             	mov    0x68(%rbp),%edi
  401c61:	85 ff                	test   %edi,%edi
  401c63:	7e 33                	jle    401c98 <singlewriter+0x1a8>
        if (data->threads[x].newmask != 0) {
  401c65:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401c69:	31 d2                	xor    %edx,%edx
  401c6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401c70:	48 63 ca             	movslq %edx,%rcx
  401c73:	48 89 c8             	mov    %rcx,%rax
  401c76:	48 c1 e0 0a          	shl    $0xa,%rax
  401c7a:	4c 01 c0             	add    %r8,%rax
  401c7d:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401c83:	85 f6                	test   %esi,%esi
  401c85:	74 31                	je     401cb8 <singlewriter+0x1c8>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401c87:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401c8b:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401c8e:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401c91:	8b 7d 68             	mov    0x68(%rbp),%edi
  401c94:	39 fa                	cmp    %edi,%edx
  401c96:	7c d8                	jl     401c70 <singlewriter+0x180>
  return 0;
  401c98:	31 c0                	xor    %eax,%eax
}
  401c9a:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401c9f:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401ca8:	75 1e                	jne    401cc8 <singlewriter+0x1d8>
  401caa:	48 83 c4 28          	add    $0x28,%rsp
  401cae:	5b                   	pop    %rbx
  401caf:	5d                   	pop    %rbp
  401cb0:	41 5c                	pop    %r12
  401cb2:	41 5d                	pop    %r13
  401cb4:	c3                   	ret
  401cb5:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401cb8:	83 c2 01             	add    $0x1,%edx
  401cbb:	39 fa                	cmp    %edi,%edx
  401cbd:	7c b1                	jl     401c70 <singlewriter+0x180>
  401cbf:	eb d7                	jmp    401c98 <singlewriter+0x1a8>
      int assignedchunk = 0;
  401cc1:	31 f6                	xor    %esi,%esi
  401cc3:	e9 24 ff ff ff       	jmp    401bec <singlewriter+0xfc>
}
  401cc8:	e8 93 f3 ff ff       	call   401060 <__stack_chk_fail@plt>
  401ccd:	0f 1f 00             	nopl   (%rax)

0000000000401cd0 <threadwork>:
int * threadwork(struct Data * data) {
  401cd0:	41 55                	push   %r13
  401cd2:	41 54                	push   %r12
  401cd4:	55                   	push   %rbp
  401cd5:	53                   	push   %rbx
  401cd6:	48 89 fb             	mov    %rdi,%rbx
  401cd9:	48 83 ec 28          	sub    $0x28,%rsp
  long thiswrite = data->main->globalwrite[data->mystream * 128];
  401cdd:	48 8b 57 28          	mov    0x28(%rdi),%rdx
int * threadwork(struct Data * data) {
  401ce1:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401cea:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401cef:	31 c0                	xor    %eax,%eax
  long thiswrite = data->main->globalwrite[data->mystream * 128];
  401cf1:	8b 87 8c 03 00 00    	mov    0x38c(%rdi),%eax
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401cf7:	48 89 e6             	mov    %rsp,%rsi
  401cfa:	bf 04 00 00 00       	mov    $0x4,%edi
  long thiswrite = data->main->globalwrite[data->mystream * 128];
  401cff:	48 8b 92 80 03 00 00 	mov    0x380(%rdx),%rdx
  401d06:	c1 e0 07             	shl    $0x7,%eax
  401d09:	48 98                	cltq
  401d0b:	48 8b 2c c2          	mov    (%rdx,%rax,8),%rbp
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401d0f:	e8 3c f3 ff ff       	call   401050 <clock_gettime@plt>
        buffer = data->mystream << 24 | ( (data->main->globalwrite[data->mystream * 128] / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401d14:	44 8b 83 8c 03 00 00 	mov    0x38c(%rbx),%r8d
  401d1b:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
   data->freq_writes++;
  401d1f:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
        buffer = data->mystream << 24 | ( (data->main->globalwrite[data->mystream * 128] / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401d24:	4c 63 4b 68          	movslq 0x68(%rbx),%r9
  401d28:	44 89 c0             	mov    %r8d,%eax
  401d2b:	48 8b 97 80 03 00 00 	mov    0x380(%rdi),%rdx
  401d32:	8b 73 64             	mov    0x64(%rbx),%esi
  401d35:	41 c1 e0 18          	shl    $0x18,%r8d
  401d39:	c1 e0 07             	shl    $0x7,%eax
  401d3c:	48 98                	cltq
  401d3e:	41 09 f0             	or     %esi,%r8d
  401d41:	48 8b 04 c2          	mov    (%rdx,%rax,8),%rax
  401d45:	4d 63 c0             	movslq %r8d,%r8
  401d48:	48 99                	cqto
  401d4a:	49 f7 f9             	idiv   %r9
  401d4d:	48 ba 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%rdx
  401d57:	48 89 c1             	mov    %rax,%rcx
  401d5a:	48 f7 ea             	imul   %rdx
  401d5d:	48 89 c8             	mov    %rcx,%rax
  401d60:	48 c1 f8 3f          	sar    $0x3f,%rax
  401d64:	48 01 ca             	add    %rcx,%rdx
  401d67:	48 c1 fa 07          	sar    $0x7,%rdx
  401d6b:	48 29 c2             	sub    %rax,%rdx
  401d6e:	48 89 d0             	mov    %rdx,%rax
  401d71:	48 c1 e0 08          	shl    $0x8,%rax
  401d75:	48 29 d0             	sub    %rdx,%rax
  401d78:	48 29 c1             	sub    %rax,%rcx
  data->main->works[buffer] = data->threadindex;
  401d7b:	48 8b 47 70          	mov    0x70(%rdi),%rax
        buffer = data->mystream << 24 | ( (data->main->globalwrite[data->mystream * 128] / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401d7f:	48 c1 e1 10          	shl    $0x10,%rcx
  401d83:	4c 09 c1             	or     %r8,%rcx
  data->main->works[buffer] = data->threadindex;
  401d86:	40 88 34 08          	mov    %sil,(%rax,%rcx,1)
    __atomic_fetch_add(&data->main->globalwrite[data->mystream * 128], 1, __ATOMIC_RELAXED);
  401d8a:	48 8b 53 28          	mov    0x28(%rbx),%rdx
  401d8e:	8b 83 8c 03 00 00    	mov    0x38c(%rbx),%eax
  401d94:	48 8b 92 80 03 00 00 	mov    0x380(%rdx),%rdx
  401d9b:	c1 e0 07             	shl    $0x7,%eax
  401d9e:	48 98                	cltq
  401da0:	f0 48 83 04 c2 01    	lock addq $0x1,(%rdx,%rax,8)
   long thisgroup = data->main->globalwrite[data->mystream] / data->threadsize;
  401da6:	4c 8b 63 28          	mov    0x28(%rbx),%r12
  401daa:	48 63 93 8c 03 00 00 	movslq 0x38c(%rbx),%rdx
  401db1:	48 63 4b 68          	movslq 0x68(%rbx),%rcx
  401db5:	49 8b 84 24 80 03 00 00 	mov    0x380(%r12),%rax
  401dbd:	49 89 d3             	mov    %rdx,%r11
  401dc0:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
  401dc4:	48 99                	cqto
  401dc6:	48 f7 f9             	idiv   %rcx
  if (data->globalread[data->laststream].global < thiswrite) {  
  401dc9:	48 63 93 90 03 00 00 	movslq 0x390(%rbx),%rdx
   data->lastgroup = thisgroup;
  401dd0:	89 83 88 03 00 00    	mov    %eax,0x388(%rbx)
  if (data->globalread[data->laststream].global < thiswrite) {  
  401dd6:	48 8b 83 48 03 00 00 	mov    0x348(%rbx),%rax
  401ddd:	4c 8d 0c d0          	lea    (%rax,%rdx,8),%r9
  401de1:	49 63 01             	movslq (%r9),%rax
  401de4:	48 39 e8             	cmp    %rbp,%rax
  401de7:	0f 8d bf 00 00 00    	jge    401eac <threadwork+0x1dc>
  401ded:	49 89 d2             	mov    %rdx,%r10
            long past = (((data->globalread[data->laststream]).global / (data->threadsize)) - 1) % 0xff;
  401df0:	99                   	cltd
  401df1:	49 89 c0             	mov    %rax,%r8
   data->freq++;
  401df4:	48 89 cf             	mov    %rcx,%rdi
            long past = (((data->globalread[data->laststream]).global / (data->threadsize)) - 1) % 0xff;
  401df7:	f7 f9                	idiv   %ecx
        buffer = data->laststream << 24 | (past << 16) | data->globalread[data->laststream].cursor % 0xff;
  401df9:	41 8b 71 04          	mov    0x4(%r9),%esi
        if (data->threadindex == 1) {
  401dfd:	8b 6b 64             	mov    0x64(%rbx),%ebp
   data->freq++;
  401e00:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
        buffer = data->laststream << 24 | (past << 16) | data->globalread[data->laststream].cursor % 0xff;
  401e05:	41 89 f5             	mov    %esi,%r13d
            long past = (((data->globalread[data->laststream]).global / (data->threadsize)) - 1) % 0xff;
  401e08:	8d 50 ff             	lea    -0x1(%rax),%edx
  401e0b:	48 63 c2             	movslq %edx,%rax
  401e0e:	89 d1                	mov    %edx,%ecx
  401e10:	48 69 c0 81 80 80 80 	imul   $0xffffffff80808081,%rax,%rax
  401e17:	c1 f9 1f             	sar    $0x1f,%ecx
  401e1a:	48 c1 e8 20          	shr    $0x20,%rax
  401e1e:	01 d0                	add    %edx,%eax
  401e20:	c1 f8 07             	sar    $0x7,%eax
  401e23:	29 c8                	sub    %ecx,%eax
  401e25:	89 c1                	mov    %eax,%ecx
  401e27:	c1 e1 08             	shl    $0x8,%ecx
  401e2a:	29 c1                	sub    %eax,%ecx
        buffer = data->laststream << 24 | (past << 16) | data->globalread[data->laststream].cursor % 0xff;
  401e2c:	31 c0                	xor    %eax,%eax
            long past = (((data->globalread[data->laststream]).global / (data->threadsize)) - 1) % 0xff;
  401e2e:	29 ca                	sub    %ecx,%edx
        buffer = data->laststream << 24 | (past << 16) | data->globalread[data->laststream].cursor % 0xff;
  401e30:	48 63 ce             	movslq %esi,%rcx
            long past = (((data->globalread[data->laststream]).global / (data->threadsize)) - 1) % 0xff;
  401e33:	48 63 d2             	movslq %edx,%rdx
        buffer = data->laststream << 24 | (past << 16) | data->globalread[data->laststream].cursor % 0xff;
  401e36:	48 85 d2             	test   %rdx,%rdx
  401e39:	48 0f 48 d0          	cmovs  %rax,%rdx
  401e3d:	48 69 c9 81 80 80 80 	imul   $0xffffffff80808081,%rcx,%rcx
  401e44:	41 c1 fd 1f          	sar    $0x1f,%r13d
  401e48:	44 89 d0             	mov    %r10d,%eax
  401e4b:	c1 e0 18             	shl    $0x18,%eax
  401e4e:	48 c1 e2 10          	shl    $0x10,%rdx
  401e52:	48 c1 e9 20          	shr    $0x20,%rcx
  401e56:	01 f1                	add    %esi,%ecx
  401e58:	c1 f9 07             	sar    $0x7,%ecx
  401e5b:	44 29 e9             	sub    %r13d,%ecx
  401e5e:	41 89 cd             	mov    %ecx,%r13d
  401e61:	41 c1 e5 08          	shl    $0x8,%r13d
  401e65:	41 29 cd             	sub    %ecx,%r13d
  401e68:	89 f1                	mov    %esi,%ecx
  401e6a:	44 29 e9             	sub    %r13d,%ecx
  401e6d:	09 c8                	or     %ecx,%eax
  401e6f:	48 98                	cltq
  401e71:	48 09 c2             	or     %rax,%rdx
        if (data->main->works[buffer] != -1) {
  401e74:	49 8b 44 24 70       	mov    0x70(%r12),%rax
  401e79:	80 3c 10 ff          	cmpb   $0xff,(%rax,%rdx,1)
  401e7d:	74 08                	je     401e87 <threadwork+0x1b7>
          data->successreads++;
  401e7f:	48 83 83 98 03 00 00 01 	addq   $0x1,0x398(%rbx)
        data->globalread[data->laststream].global++;
  401e87:	41 83 c0 01          	add    $0x1,%r8d
    if (data->globalread[data->laststream].cursor + 1 == data->threadsize ) {
  401e8b:	8d 46 01             	lea    0x1(%rsi),%eax
        data->globalread[data->laststream].global++;
  401e8e:	45 89 01             	mov    %r8d,(%r9)
    if (data->globalread[data->laststream].cursor + 1 == data->threadsize ) {
  401e91:	39 c7                	cmp    %eax,%edi
  401e93:	74 3b                	je     401ed0 <threadwork+0x200>
    data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1) % data->threadsize;
  401e95:	99                   	cltd
  401e96:	f7 ff                	idiv   %edi
         if (data->globalread[thistream].cursor == data->threadindex) {
  401e98:	39 d5                	cmp    %edx,%ebp
  401e9a:	74 68                	je     401f04 <threadwork+0x234>
    data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1) % data->threadsize;
  401e9c:	41 89 51 04          	mov    %edx,0x4(%r9)
        if ((data->globalread[thistream].cursor % data->threadsize) == 0) {
  401ea0:	85 d2                	test   %edx,%edx
  401ea2:	75 08                	jne    401eac <threadwork+0x1dc>
          data->globalread[thistream].cursor = 0;
  401ea4:	41 c7 41 04 00 00 00 00 	movl   $0x0,0x4(%r9)
}
  401eac:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  401eb1:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401eba:	0f 85 7c 00 00 00    	jne    401f3c <threadwork+0x26c>
  401ec0:	48 83 c4 28          	add    $0x28,%rsp
  401ec4:	31 c0                	xor    %eax,%eax
  401ec6:	5b                   	pop    %rbx
  401ec7:	5d                   	pop    %rbp
  401ec8:	41 5c                	pop    %r12
  401eca:	41 5d                	pop    %r13
  401ecc:	c3                   	ret
  401ecd:	0f 1f 00             	nopl   (%rax)
       data->laststream = (data->laststream + 1) % 5;
  401ed0:	41 83 c2 01          	add    $0x1,%r10d
  401ed4:	49 63 d2             	movslq %r10d,%rdx
  401ed7:	44 89 d1             	mov    %r10d,%ecx
  401eda:	48 69 d2 67 66 66 66 	imul   $0x66666667,%rdx,%rdx
  401ee1:	c1 f9 1f             	sar    $0x1f,%ecx
  401ee4:	48 c1 fa 21          	sar    $0x21,%rdx
  401ee8:	29 ca                	sub    %ecx,%edx
  401eea:	8d 0c 92             	lea    (%rdx,%rdx,4),%ecx
  401eed:	44 89 d2             	mov    %r10d,%edx
  401ef0:	29 ca                	sub    %ecx,%edx
       if (data->laststream == data->mystream) {
  401ef2:	41 39 d3             	cmp    %edx,%r11d
  401ef5:	74 19                	je     401f10 <threadwork+0x240>
       data->laststream = (data->laststream + 1) % 5;
  401ef7:	89 93 90 03 00 00    	mov    %edx,0x390(%rbx)
    data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1) % data->threadsize;
  401efd:	99                   	cltd
  401efe:	f7 ff                	idiv   %edi
         if (data->globalread[thistream].cursor == data->threadindex) {
  401f00:	39 d5                	cmp    %edx,%ebp
  401f02:	75 98                	jne    401e9c <threadwork+0x1cc>
           data->globalread[thistream].cursor++;
  401f04:	8d 42 01             	lea    0x1(%rdx),%eax
        if ((data->globalread[thistream].cursor % data->threadsize) == 0) {
  401f07:	99                   	cltd
           data->globalread[thistream].cursor++;
  401f08:	41 89 41 04          	mov    %eax,0x4(%r9)
        if ((data->globalread[thistream].cursor % data->threadsize) == 0) {
  401f0c:	f7 ff                	idiv   %edi
  401f0e:	eb 90                	jmp    401ea0 <threadwork+0x1d0>
        data->laststream = (data->laststream + 1) % 5;
  401f10:	41 83 c3 01          	add    $0x1,%r11d
  401f14:	49 63 d3             	movslq %r11d,%rdx
  401f17:	44 89 d9             	mov    %r11d,%ecx
  401f1a:	48 69 d2 67 66 66 66 	imul   $0x66666667,%rdx,%rdx
  401f21:	c1 f9 1f             	sar    $0x1f,%ecx
  401f24:	48 c1 fa 21          	sar    $0x21,%rdx
  401f28:	29 ca                	sub    %ecx,%edx
  401f2a:	8d 14 92             	lea    (%rdx,%rdx,4),%edx
  401f2d:	41 29 d3             	sub    %edx,%r11d
  401f30:	44 89 9b 90 03 00 00 	mov    %r11d,0x390(%rbx)
  401f37:	e9 59 ff ff ff       	jmp    401e95 <threadwork+0x1c5>
}
  401f3c:	e8 1f f1 ff ff       	call   401060 <__stack_chk_fail@plt>
  401f41:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401f4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401f50 <work>:
void * work(void * arg) {
  401f50:	53                   	push   %rbx
  401f51:	8b 57 64             	mov    0x64(%rdi),%edx
  401f54:	48 89 fb             	mov    %rdi,%rbx
  401f57:	31 c0                	xor    %eax,%eax
  401f59:	48 8d 35 a4 00 00 00 	lea    0xa4(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  401f60:	bf 01 00 00 00       	mov    $0x1,%edi
  401f65:	e8 36 f1 ff ff       	call   4010a0 <__printf_chk@plt>
  while (data->running == 1) {
  401f6a:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401f6e:	75 0e                	jne    401f7e <work+0x2e>
      threadwork(data);
  401f70:	48 89 df             	mov    %rbx,%rdi
  401f73:	e8 58 fd ff ff       	call   401cd0 <threadwork>
  while (data->running == 1) {
  401f78:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401f7c:	74 f2                	je     401f70 <work+0x20>
  401f7e:	8b 53 64             	mov    0x64(%rbx),%edx
  401f81:	48 8d 35 8f 00 00 00 	lea    0x8f(%rip),%rsi        # 402017 <_IO_stdin_used+0x17>
  401f88:	bf 01 00 00 00       	mov    $0x1,%edi
  401f8d:	31 c0                	xor    %eax,%eax
  401f8f:	e8 0c f1 ff ff       	call   4010a0 <__printf_chk@plt>
}
  401f94:	5b                   	pop    %rbx
  401f95:	c3                   	ret
  401f96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401fa0 <work2>:
  while (data->running == 1) {
  401fa0:	eb 0b                	jmp    401fad <work2+0xd>
  401fa2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  401fa8:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  401fad:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  401fb1:	74 f5                	je     401fa8 <work2+0x8>
}
  401fb3:	c3                   	ret

Disassembly of section .fini:

0000000000401fb4 <_fini>:
  401fb4:	f3 0f 1e fa          	endbr64
  401fb8:	48 83 ec 08          	sub    $0x8,%rsp
  401fbc:	48 83 c4 08          	add    $0x8,%rsp
  401fc0:	c3                   	ret
