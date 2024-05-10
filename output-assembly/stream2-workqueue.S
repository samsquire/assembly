
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

0000000000401020 <pthread_setaffinity_np@plt-0x10>:
  401020:	ff 35 62 3f 00 00    	push   0x3f62(%rip)        # 404f88 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 64 3f 00 00    	jmp    *0x3f64(%rip)        # 404f90 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <pthread_setaffinity_np@plt>:
  401030:	ff 25 62 3f 00 00    	jmp    *0x3f62(%rip)        # 404f98 <pthread_setaffinity_np@GLIBC_2.34>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <puts@plt>:
  401040:	ff 25 5a 3f 00 00    	jmp    *0x3f5a(%rip)        # 404fa0 <puts@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <clock_gettime@plt>:
  401050:	ff 25 52 3f 00 00    	jmp    *0x3f52(%rip)        # 404fa8 <clock_gettime@GLIBC_2.17>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <__stack_chk_fail@plt>:
  401060:	ff 25 4a 3f 00 00    	jmp    *0x3f4a(%rip)        # 404fb0 <__stack_chk_fail@GLIBC_2.4>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <nanosleep@plt>:
  401070:	ff 25 42 3f 00 00    	jmp    *0x3f42(%rip)        # 404fb8 <nanosleep@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <memset@plt>:
  401080:	ff 25 3a 3f 00 00    	jmp    *0x3f3a(%rip)        # 404fc0 <memset@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <calloc@plt>:
  401090:	ff 25 32 3f 00 00    	jmp    *0x3f32(%rip)        # 404fc8 <calloc@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <__printf_chk@plt>:
  4010a0:	ff 25 2a 3f 00 00    	jmp    *0x3f2a(%rip)        # 404fd0 <__printf_chk@GLIBC_2.3.4>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <pthread_create@plt>:
  4010b0:	ff 25 22 3f 00 00    	jmp    *0x3f22(%rip)        # 404fd8 <pthread_create@GLIBC_2.34>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <posix_memalign@plt>:
  4010c0:	ff 25 1a 3f 00 00    	jmp    *0x3f1a(%rip)        # 404fe0 <posix_memalign@GLIBC_2.2.5>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010d0 <pthread_join@plt>:
  4010d0:	ff 25 12 3f 00 00    	jmp    *0x3f12(%rip)        # 404fe8 <pthread_join@GLIBC_2.34>
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
  4010ec:	48 8d 35 43 1f 00 00 	lea    0x1f43(%rip),%rsi        # 403036 <_IO_stdin_used+0x36>
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
  401128:	48 8d 35 19 1f 00 00 	lea    0x1f19(%rip),%rsi        # 403048 <_IO_stdin_used+0x48>
  40112f:	31 c0                	xor    %eax,%eax
  401131:	bf 01 00 00 00       	mov    $0x1,%edi
  401136:	e8 65 ff ff ff       	call   4010a0 <__printf_chk@plt>
  40113b:	ba 20 00 00 00       	mov    $0x20,%edx
  401140:	48 8d 35 fd 1e 00 00 	lea    0x1efd(%rip),%rsi        # 403044 <_IO_stdin_used+0x44>
  401147:	31 c0                	xor    %eax,%eax
  401149:	bf 01 00 00 00       	mov    $0x1,%edi
  40114e:	e8 4d ff ff ff       	call   4010a0 <__printf_chk@plt>
  401153:	ba 0f 00 00 00       	mov    $0xf,%edx
  401158:	48 8d 35 f8 1e 00 00 	lea    0x1ef8(%rip),%rsi        # 403057 <_IO_stdin_used+0x57>
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
  4011d2:	48 8d 35 93 1e 00 00 	lea    0x1e93(%rip),%rsi        # 40306c <_IO_stdin_used+0x6c>
  4011d9:	e8 c2 fe ff ff       	call   4010a0 <__printf_chk@plt>
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4011de:	be 20 00 00 00       	mov    $0x20,%esi
  4011e3:	bf 64 00 00 00       	mov    $0x64,%edi
  4011e8:	e8 a3 fe ff ff       	call   401090 <calloc@plt>
  4011ed:	31 d2                	xor    %edx,%edx
  4011ef:	bf 01 00 00 00       	mov    $0x1,%edi
  4011f4:	48 8d 35 82 1e 00 00 	lea    0x1e82(%rip),%rsi        # 40307d <_IO_stdin_used+0x7d>
  4011fb:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  401200:	31 c0                	xor    %eax,%eax
  401202:	e8 99 fe ff ff       	call   4010a0 <__printf_chk@plt>
  401207:	4c 89 e2             	mov    %r12,%rdx
  40120a:	bf 01 00 00 00       	mov    $0x1,%edi
  40120f:	31 c0                	xor    %eax,%eax
  401211:	48 8d 35 71 1e 00 00 	lea    0x1e71(%rip),%rsi        # 403089 <_IO_stdin_used+0x89>
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
  4012a4:	48 8d 35 2d 1f 00 00 	lea    0x1f2d(%rip),%rsi        # 4031d8 <_IO_stdin_used+0x1d8>
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
  4012cb:	66 0f 6f 0d 8d 1f 00 00 	movdqa 0x1f8d(%rip),%xmm1        # 403260 <_IO_stdin_used+0x260>
    data[x].chunkslen = chunkslen;
  4012d3:	66 0f 6f 15 95 1f 00 00 	movdqa 0x1f95(%rip),%xmm2        # 403270 <_IO_stdin_used+0x270>
    data[x].loglevel = debug;
  4012db:	41 c7 86 80 fc ff ff 00 00 00 00 	movl   $0x0,-0x380(%r14)
    data[x].globalwrite = globalwrite;
  4012e6:	49 89 46 80          	mov    %rax,-0x80(%r14)
    data[x].mystream = 1 + (x / 4);
  4012ea:	83 c2 01             	add    $0x1,%edx
    data[x].running = 2;
  4012ed:	48 8b 05 5c 1f 00 00 	mov    0x1f5c(%rip),%rax        # 403250 <_IO_stdin_used+0x250>
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4012f4:	be 30 00 00 00       	mov    $0x30,%esi
    data[x].prevread = threadsize;
  4012f9:	66 0f 6f 1d 7f 1f 00 00 	movdqa 0x1f7f(%rip),%xmm3        # 403280 <_IO_stdin_used+0x280>
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401301:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].threadindex = x;
  401306:	45 89 be 64 fc ff ff 	mov    %r15d,-0x39c(%r14)
  for (int x = 0; x < threadsize ; x++) {
  40130d:	81 c5 11 11 11 11    	add    $0x11111111,%ebp
    data[x].running = 2;
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
    data[x].writecursor = 0;
  401371:	41 c7 86 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%r14)
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
  401402:	49 c7 c5 00 21 40 00 	mov    $0x402100,%r13
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
  401464:	66 0f 6f 05 24 1e 00 00 	movdqa 0x1e24(%rip),%xmm0        # 403290 <_IO_stdin_used+0x290>
  40146c:	4c 8d 6c 24 30       	lea    0x30(%rsp),%r13
  401471:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  401476:	66 0f ef c0          	pxor   %xmm0,%xmm0
  40147a:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  40147f:	e8 ec fb ff ff       	call   401070 <nanosleep@plt>
  401484:	48 8d 3d 0a 1c 00 00 	lea    0x1c0a(%rip),%rdi        # 403095 <_IO_stdin_used+0x95>
  40148b:	e8 b0 fb ff ff       	call   401040 <puts@plt>
  
  printf("runphased\n");
  for (int x = 0; x < threadsize ; x++) {
    data[x].running--;
  401490:	83 6b 5c 01          	subl   $0x1,0x5c(%rbx)
  401494:	48 8d 3d 04 1c 00 00 	lea    0x1c04(%rip),%rdi        # 40309f <_IO_stdin_used+0x9f>
  40149b:	83 ab 5c 04 00 00 01 	subl   $0x1,0x45c(%rbx)
  4014a2:	83 ab 5c 08 00 00 01 	subl   $0x1,0x85c(%rbx)
  4014a9:	83 ab 5c 0c 00 00 01 	subl   $0x1,0xc5c(%rbx)
  4014b0:	83 ab 5c 10 00 00 01 	subl   $0x1,0x105c(%rbx)
  4014b7:	83 ab 5c 14 00 00 01 	subl   $0x1,0x145c(%rbx)
  4014be:	83 ab 5c 18 00 00 01 	subl   $0x1,0x185c(%rbx)
  4014c5:	83 ab 5c 1c 00 00 01 	subl   $0x1,0x1c5c(%rbx)
  4014cc:	83 ab 5c 20 00 00 01 	subl   $0x1,0x205c(%rbx)
  4014d3:	83 ab 5c 24 00 00 01 	subl   $0x1,0x245c(%rbx)
  4014da:	83 ab 5c 28 00 00 01 	subl   $0x1,0x285c(%rbx)
  4014e1:	83 ab 5c 2c 00 00 01 	subl   $0x1,0x2c5c(%rbx)
  4014e8:	83 ab 5c 30 00 00 01 	subl   $0x1,0x305c(%rbx)
  4014ef:	83 ab 5c 34 00 00 01 	subl   $0x1,0x345c(%rbx)
  4014f6:	83 ab 5c 38 00 00 01 	subl   $0x1,0x385c(%rbx)
  4014fd:	e8 3e fb ff ff       	call   401040 <puts@plt>
  
 printf("draining\n");
  //time.tv_sec = 3;
  //nanosleep(&time, &rem);
  for (int x = 0; x < threadsize ; x++) {
    data[x].running--;
  401502:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
  401507:	83 6b 5c 01          	subl   $0x1,0x5c(%rbx)
  40150b:	83 ab 5c 04 00 00 01 	subl   $0x1,0x45c(%rbx)
  401512:	83 ab 5c 08 00 00 01 	subl   $0x1,0x85c(%rbx)
  401519:	83 ab 5c 0c 00 00 01 	subl   $0x1,0xc5c(%rbx)
  401520:	83 ab 5c 10 00 00 01 	subl   $0x1,0x105c(%rbx)
  401527:	83 ab 5c 14 00 00 01 	subl   $0x1,0x145c(%rbx)
  40152e:	83 ab 5c 18 00 00 01 	subl   $0x1,0x185c(%rbx)
  401535:	83 ab 5c 1c 00 00 01 	subl   $0x1,0x1c5c(%rbx)
  40153c:	83 ab 5c 20 00 00 01 	subl   $0x1,0x205c(%rbx)
  401543:	83 ab 5c 24 00 00 01 	subl   $0x1,0x245c(%rbx)
  40154a:	83 ab 5c 28 00 00 01 	subl   $0x1,0x285c(%rbx)
  401551:	83 ab 5c 2c 00 00 01 	subl   $0x1,0x2c5c(%rbx)
  401558:	83 ab 5c 30 00 00 01 	subl   $0x1,0x305c(%rbx)
  40155f:	83 ab 5c 34 00 00 01 	subl   $0x1,0x345c(%rbx)
  401566:	83 ab 5c 38 00 00 01 	subl   $0x1,0x385c(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  40156d:	48 83 c5 78          	add    $0x78,%rbp
  401571:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  }
  
  //nanosleep(&time, &rem);
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401578:	49 8b 3c 24          	mov    (%r12),%rdi
  40157c:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  40157f:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  401583:	e8 48 fb ff ff       	call   4010d0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401588:	4c 39 e5             	cmp    %r12,%rbp
  40158b:	75 eb                	jne    401578 <main+0x498>
  40158d:	48 8d 3d 14 1b 00 00 	lea    0x1b14(%rip),%rdi        # 4030a8 <_IO_stdin_used+0xa8>
  401594:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  401598:	45 31 e4             	xor    %r12d,%r12d
  40159b:	e8 a0 fa ff ff       	call   401040 <puts@plt>
  long sends = 1;
  for (int x = 0; x < threadsize; x++) {
  4015a0:	4c 8d b3 48 3c 00 00 	lea    0x3c48(%rbx),%r14
  4015a7:	4c 8d 2d 0f 1b 00 00 	lea    0x1b0f(%rip),%r13        # 4030bd <_IO_stdin_used+0xbd>
  4015ae:	66 90                	xchg   %ax,%ax
  4015b0:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4015b4:	4c 89 ee             	mov    %r13,%rsi
  4015b7:	bf 01 00 00 00       	mov    $0x1,%edi
  4015bc:	31 c0                	xor    %eax,%eax
  4015be:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
  4015c5:	e8 d6 fa ff ff       	call   4010a0 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  4015ca:	4c 03 a5 00 fc ff ff 	add    -0x400(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  4015d1:	49 39 ee             	cmp    %rbp,%r14
  4015d4:	75 da                	jne    4015b0 <main+0x4d0>
  4015d6:	4c 89 e2             	mov    %r12,%rdx
  4015d9:	48 8d 35 e8 1a 00 00 	lea    0x1ae8(%rip),%rsi        # 4030c8 <_IO_stdin_used+0xc8>
  4015e0:	bf 01 00 00 00       	mov    $0x1,%edi
  4015e5:	31 c0                	xor    %eax,%eax
  4015e7:	e8 b4 fa ff ff       	call   4010a0 <__printf_chk@plt>
  4015ec:	4c 89 e2             	mov    %r12,%rdx
  4015ef:	bf 01 00 00 00       	mov    $0x1,%edi
  4015f4:	31 c0                	xor    %eax,%eax
  4015f6:	48 8d 35 d6 1a 00 00 	lea    0x1ad6(%rip),%rsi        # 4030d3 <_IO_stdin_used+0xd3>
  4015fd:	48 8d ab 98 03 00 00 	lea    0x398(%rbx),%rbp
  401604:	e8 97 fa ff ff       	call   4010a0 <__printf_chk@plt>
  }
  printf("freq: %ld\n", freq/ seconds);
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  401609:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40160e:	48 8d 35 cc 1a 00 00 	lea    0x1acc(%rip),%rsi        # 4030e1 <_IO_stdin_used+0xe1>
  401615:	bf 01 00 00 00       	mov    $0x1,%edi
  40161a:	48 99                	cqto
  40161c:	4c 8d bb 98 3f 00 00 	lea    0x3f98(%rbx),%r15
  401623:	4c 8d 35 fc 1a 00 00 	lea    0x1afc(%rip),%r14        # 403126 <_IO_stdin_used+0x126>
  40162a:	49 f7 fc             	idiv   %r12
  40162d:	49 89 c4             	mov    %rax,%r12
  401630:	48 89 c2             	mov    %rax,%rdx
  401633:	31 c0                	xor    %eax,%eax
  401635:	e8 66 fa ff ff       	call   4010a0 <__printf_chk@plt>
  40163a:	4c 89 e2             	mov    %r12,%rdx
  40163d:	bf 01 00 00 00       	mov    $0x1,%edi
  401642:	31 c0                	xor    %eax,%eax
  401644:	48 8d 35 aa 1a 00 00 	lea    0x1aaa(%rip),%rsi        # 4030f5 <_IO_stdin_used+0xf5>
  40164b:	e8 50 fa ff ff       	call   4010a0 <__printf_chk@plt>
  401650:	4c 89 e2             	mov    %r12,%rdx
  401653:	bf 01 00 00 00       	mov    $0x1,%edi
  401658:	31 c0                	xor    %eax,%eax
  40165a:	48 8d 35 b2 1a 00 00 	lea    0x1ab2(%rip),%rsi        # 403113 <_IO_stdin_used+0x113>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  
  long goods = 0;
  401661:	45 31 e4             	xor    %r12d,%r12d
  401664:	e8 37 fa ff ff       	call   4010a0 <__printf_chk@plt>

  for (int x = 0; x < threadsize; x++) {
  401669:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401670:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401674:	4c 89 f6             	mov    %r14,%rsi
  401677:	bf 01 00 00 00       	mov    $0x1,%edi
  40167c:	31 c0                	xor    %eax,%eax
  40167e:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
  401685:	e8 16 fa ff ff       	call   4010a0 <__printf_chk@plt>
    printf("%ld successreads\n", data[x].successreads);
    goods += data[x].successreads;
  40168a:	4c 8b ad 00 fc ff ff 	mov    -0x400(%rbp),%r13
  401691:	4d 01 e5             	add    %r12,%r13
  401694:	4d 89 ec             	mov    %r13,%r12
  for (int x = 0; x < threadsize; x++) {
  401697:	49 39 ef             	cmp    %rbp,%r15
  40169a:	75 d4                	jne    401670 <main+0x590>
  40169c:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  4016a0:	4c 8d bb 50 3c 00 00 	lea    0x3c50(%rbx),%r15
  }
  
  long freq_writes = 0;
  4016a7:	45 31 e4             	xor    %r12d,%r12d
  4016aa:	4c 8d 35 87 1a 00 00 	lea    0x1a87(%rip),%r14        # 403138 <_IO_stdin_used+0x138>
  4016b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  4016b8:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4016bc:	4c 89 f6             	mov    %r14,%rsi
  4016bf:	bf 01 00 00 00       	mov    $0x1,%edi
  4016c4:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  4016c6:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
    freq_writes += data[x].freq_writes;
  4016cd:	49 01 d4             	add    %rdx,%r12
  4016d0:	e8 cb f9 ff ff       	call   4010a0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  4016d5:	49 39 ef             	cmp    %rbp,%r15
  4016d8:	75 de                	jne    4016b8 <main+0x5d8>
  4016da:	4c 89 e2             	mov    %r12,%rdx
  4016dd:	bf 01 00 00 00       	mov    $0x1,%edi
  4016e2:	31 c0                	xor    %eax,%eax
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  4016e4:	bd 00 ca 9a 3b       	mov    $0x3b9aca00,%ebp
  4016e9:	48 8d 35 54 1a 00 00 	lea    0x1a54(%rip),%rsi        # 403144 <_IO_stdin_used+0x144>
  4016f0:	e8 ab f9 ff ff       	call   4010a0 <__printf_chk@plt>
  4016f5:	4c 89 e2             	mov    %r12,%rdx
  4016f8:	bf 01 00 00 00       	mov    $0x1,%edi
  4016fd:	31 c0                	xor    %eax,%eax
  4016ff:	48 8d 35 50 1a 00 00 	lea    0x1a50(%rip),%rsi        # 403156 <_IO_stdin_used+0x156>
  401706:	e8 95 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  40170b:	48 89 e8             	mov    %rbp,%rax
  40170e:	bf 01 00 00 00       	mov    $0x1,%edi
  401713:	48 8d 35 54 1a 00 00 	lea    0x1a54(%rip),%rsi        # 40316e <_IO_stdin_used+0x16e>
  40171a:	48 99                	cqto
  40171c:	49 f7 fc             	idiv   %r12
  40171f:	49 89 c4             	mov    %rax,%r12
  401722:	48 89 c2             	mov    %rax,%rdx
  401725:	31 c0                	xor    %eax,%eax
  401727:	e8 74 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  40172c:	4c 89 e2             	mov    %r12,%rdx
  40172f:	bf 01 00 00 00       	mov    $0x1,%edi
  401734:	31 c0                	xor    %eax,%eax
  401736:	48 8d 35 bb 1a 00 00 	lea    0x1abb(%rip),%rsi        # 4031f8 <_IO_stdin_used+0x1f8>
  40173d:	e8 5e f9 ff ff       	call   4010a0 <__printf_chk@plt>
  401742:	4c 89 e2             	mov    %r12,%rdx
  401745:	bf 01 00 00 00       	mov    $0x1,%edi
  40174a:	31 c0                	xor    %eax,%eax
  40174c:	48 8d 35 36 1a 00 00 	lea    0x1a36(%rip),%rsi        # 403189 <_IO_stdin_used+0x189>
  401753:	4c 8d 25 96 19 00 00 	lea    0x1996(%rip),%r12        # 4030f0 <_IO_stdin_used+0xf0>
  40175a:	e8 41 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  40175f:	48 8d 3d 3d 1a 00 00 	lea    0x1a3d(%rip),%rdi        # 4031a3 <_IO_stdin_used+0x1a3>
  401766:	e8 d5 f8 ff ff       	call   401040 <puts@plt>
  40176b:	4c 89 e6             	mov    %r12,%rsi
  40176e:	bf 01 00 00 00       	mov    $0x1,%edi
  401773:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  401775:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  40177c:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  401783:	e8 18 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  401788:	4c 89 e6             	mov    %r12,%rsi
  40178b:	bf 01 00 00 00       	mov    $0x1,%edi
  401790:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  401792:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  401799:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4017a0:	e8 fb f8 ff ff       	call   4010a0 <__printf_chk@plt>
  4017a5:	4c 89 e6             	mov    %r12,%rsi
  4017a8:	bf 01 00 00 00       	mov    $0x1,%edi
  4017ad:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  4017af:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  4017b6:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  4017bd:	e8 de f8 ff ff       	call   4010a0 <__printf_chk@plt>
  4017c2:	4c 89 e6             	mov    %r12,%rsi
  4017c5:	bf 01 00 00 00       	mov    $0x1,%edi
  4017ca:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4017cc:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  4017d3:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  4017da:	e8 c1 f8 ff ff       	call   4010a0 <__printf_chk@plt>
  4017df:	4c 89 e6             	mov    %r12,%rsi
  4017e2:	bf 01 00 00 00       	mov    $0x1,%edi
  4017e7:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  4017e9:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  4017f0:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  4017f7:	e8 a4 f8 ff ff       	call   4010a0 <__printf_chk@plt>
  4017fc:	4c 89 e6             	mov    %r12,%rsi
  4017ff:	bf 01 00 00 00       	mov    $0x1,%edi
  401804:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  401806:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  40180d:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401814:	e8 87 f8 ff ff       	call   4010a0 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  401819:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  401820:	bf 01 00 00 00       	mov    $0x1,%edi
  401825:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  40182c:	48 8d 35 7d 19 00 00 	lea    0x197d(%rip),%rsi        # 4031b0 <_IO_stdin_used+0x1b0>
  401833:	31 c0                	xor    %eax,%eax
  401835:	e8 66 f8 ff ff       	call   4010a0 <__printf_chk@plt>
  40183a:	4c 89 ea             	mov    %r13,%rdx
  40183d:	bf 01 00 00 00       	mov    $0x1,%edi
  401842:	31 c0                	xor    %eax,%eax
  401844:	48 8d 35 6d 19 00 00 	lea    0x196d(%rip),%rsi        # 4031b8 <_IO_stdin_used+0x1b8>
  40184b:	e8 50 f8 ff ff       	call   4010a0 <__printf_chk@plt>
  } 
  printf("%ld good reads per second\n", goods / seconds);
  printf("%ld good reads per second latency\n", 1000000000 / (goods / seconds));
  401850:	48 89 e8             	mov    %rbp,%rax
  401853:	bf 01 00 00 00       	mov    $0x1,%edi
  401858:	48 8d 35 c1 19 00 00 	lea    0x19c1(%rip),%rsi        # 403220 <_IO_stdin_used+0x220>
  40185f:	48 99                	cqto
  401861:	49 f7 fd             	idiv   %r13
  401864:	48 89 c2             	mov    %rax,%rdx
  401867:	31 c0                	xor    %eax,%eax
  401869:	e8 32 f8 ff ff       	call   4010a0 <__printf_chk@plt>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  40186e:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  401873:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40187c:	75 11                	jne    40188f <main+0x7af>
  40187e:	48 83 c4 78          	add    $0x78,%rsp
  401882:	31 c0                	xor    %eax,%eax
  401884:	5b                   	pop    %rbx
  401885:	5d                   	pop    %rbp
  401886:	41 5c                	pop    %r12
  401888:	41 5d                	pop    %r13
  40188a:	41 5e                	pop    %r14
  40188c:	41 5f                	pop    %r15
  40188e:	c3                   	ret
  40188f:	e8 cc f7 ff ff       	call   401060 <__stack_chk_fail@plt>
  401894:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40189e:	66 90                	xchg   %ax,%ax

00000000004018a0 <set_fast_math>:
  4018a0:	f3 0f 1e fa          	endbr64
  4018a4:	0f ae 5c 24 fc       	stmxcsr -0x4(%rsp)
  4018a9:	81 4c 24 fc 40 80 00 00 	orl    $0x8040,-0x4(%rsp)
  4018b1:	0f ae 54 24 fc       	ldmxcsr -0x4(%rsp)
  4018b6:	c3                   	ret
  4018b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000004018c0 <_start>:
  4018c0:	f3 0f 1e fa          	endbr64
  4018c4:	31 ed                	xor    %ebp,%ebp
  4018c6:	49 89 d1             	mov    %rdx,%r9
  4018c9:	5e                   	pop    %rsi
  4018ca:	48 89 e2             	mov    %rsp,%rdx
  4018cd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4018d1:	50                   	push   %rax
  4018d2:	54                   	push   %rsp
  4018d3:	45 31 c0             	xor    %r8d,%r8d
  4018d6:	31 c9                	xor    %ecx,%ecx
  4018d8:	48 c7 c7 e0 10 40 00 	mov    $0x4010e0,%rdi
  4018df:	ff 15 0b 37 00 00    	call   *0x370b(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  4018e5:	f4                   	hlt
  4018e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004018f0 <_dl_relocate_static_pie>:
  4018f0:	f3 0f 1e fa          	endbr64
  4018f4:	c3                   	ret
  4018f5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4018ff:	90                   	nop

0000000000401900 <deregister_tm_clones>:
  401900:	b8 10 50 40 00       	mov    $0x405010,%eax
  401905:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  40190b:	74 13                	je     401920 <deregister_tm_clones+0x20>
  40190d:	b8 00 00 00 00       	mov    $0x0,%eax
  401912:	48 85 c0             	test   %rax,%rax
  401915:	74 09                	je     401920 <deregister_tm_clones+0x20>
  401917:	bf 10 50 40 00       	mov    $0x405010,%edi
  40191c:	ff e0                	jmp    *%rax
  40191e:	66 90                	xchg   %ax,%ax
  401920:	c3                   	ret
  401921:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40192c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401930 <register_tm_clones>:
  401930:	be 10 50 40 00       	mov    $0x405010,%esi
  401935:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  40193c:	48 89 f0             	mov    %rsi,%rax
  40193f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401943:	48 c1 f8 03          	sar    $0x3,%rax
  401947:	48 01 c6             	add    %rax,%rsi
  40194a:	48 d1 fe             	sar    %rsi
  40194d:	74 11                	je     401960 <register_tm_clones+0x30>
  40194f:	b8 00 00 00 00       	mov    $0x0,%eax
  401954:	48 85 c0             	test   %rax,%rax
  401957:	74 07                	je     401960 <register_tm_clones+0x30>
  401959:	bf 10 50 40 00       	mov    $0x405010,%edi
  40195e:	ff e0                	jmp    *%rax
  401960:	c3                   	ret
  401961:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40196c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401970 <__do_global_dtors_aux>:
  401970:	f3 0f 1e fa          	endbr64
  401974:	80 3d 95 36 00 00 00 	cmpb   $0x0,0x3695(%rip)        # 405010 <__TMC_END__>
  40197b:	75 13                	jne    401990 <__do_global_dtors_aux+0x20>
  40197d:	55                   	push   %rbp
  40197e:	48 89 e5             	mov    %rsp,%rbp
  401981:	e8 7a ff ff ff       	call   401900 <deregister_tm_clones>
  401986:	c6 05 83 36 00 00 01 	movb   $0x1,0x3683(%rip)        # 405010 <__TMC_END__>
  40198d:	5d                   	pop    %rbp
  40198e:	c3                   	ret
  40198f:	90                   	nop
  401990:	c3                   	ret
  401991:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40199c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004019a0 <frame_dummy>:
  4019a0:	f3 0f 1e fa          	endbr64
  4019a4:	eb 8a                	jmp    401930 <register_tm_clones>
  4019a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004019b0 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  4019b0:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4019b4:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  4019b7:	7e 77                	jle    401a30 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  4019b9:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4019bd:	55                   	push   %rbp
  4019be:	49 89 f2             	mov    %rsi,%r10
  4019c1:	49 89 d3             	mov    %rdx,%r11
  4019c4:	53                   	push   %rbx
  4019c5:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  4019c8:	48 8b 98 20 04 00 00 	mov    0x420(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  4019cf:	b8 01 00 00 00       	mov    $0x1,%eax
  4019d4:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  4019d8:	48 63 d0             	movslq %eax,%rdx
  4019db:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  4019de:	85 d2                	test   %edx,%edx
  4019e0:	40 0f 94 c6          	sete   %sil
  4019e4:	f6 c2 04             	test   $0x4,%dl
  4019e7:	75 05                	jne    4019ee <pollthreads+0x3e>
  4019e9:	40 84 f6             	test   %sil,%sil
  4019ec:	74 0d                	je     4019fb <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  4019ee:	49 63 08             	movslq (%r8),%rcx
  4019f1:	8d 69 01             	lea    0x1(%rcx),%ebp
  4019f4:	41 89 28             	mov    %ebp,(%r8)
  4019f7:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  4019fb:	83 e2 08             	and    $0x8,%edx
  4019fe:	75 05                	jne    401a05 <pollthreads+0x55>
  401a00:	40 84 f6             	test   %sil,%sil
  401a03:	74 1b                	je     401a20 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  401a05:	48 63 17             	movslq (%rdi),%rdx
  401a08:	8d 4a 01             	lea    0x1(%rdx),%ecx
  401a0b:	89 0f                	mov    %ecx,(%rdi)
  401a0d:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  401a11:	83 c0 01             	add    $0x1,%eax
  401a14:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401a18:	7f be                	jg     4019d8 <pollthreads+0x28>
}
  401a1a:	31 c0                	xor    %eax,%eax
  401a1c:	5b                   	pop    %rbx
  401a1d:	5d                   	pop    %rbp
  401a1e:	c3                   	ret
  401a1f:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  401a20:	83 c0 01             	add    $0x1,%eax
  401a23:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401a27:	7f af                	jg     4019d8 <pollthreads+0x28>
}
  401a29:	31 c0                	xor    %eax,%eax
  401a2b:	5b                   	pop    %rbx
  401a2c:	5d                   	pop    %rbp
  401a2d:	c3                   	ret
  401a2e:	66 90                	xchg   %ax,%ax
  401a30:	31 c0                	xor    %eax,%eax
  401a32:	c3                   	ret
  401a33:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401a3e:	66 90                	xchg   %ax,%ax

0000000000401a40 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401a40:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a43:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
      if (*availableidx == 0) {
  401a4a:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a4d:	48 83 c7 01          	add    $0x1,%rdi
  401a51:	48 85 ff             	test   %rdi,%rdi
  401a54:	7e 66                	jle    401abc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401a56:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a5d:	31 c9                	xor    %ecx,%ecx
  401a5f:	45 31 c9             	xor    %r9d,%r9d
  401a62:	31 c0                	xor    %eax,%eax
  401a64:	eb 18                	jmp    401a7e <findavailable+0x3e>
  401a66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401a70:	83 c1 01             	add    $0x1,%ecx
  401a73:	48 63 c1             	movslq %ecx,%rax
  401a76:	49 89 c1             	mov    %rax,%r9
  401a79:	48 39 f8             	cmp    %rdi,%rax
  401a7c:	7d 3e                	jge    401abc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401a7e:	48 c1 e0 05          	shl    $0x5,%rax
  401a82:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401a88:	75 e6                	jne    401a70 <findavailable+0x30>
         available[*availableidx] = x;
  401a8a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  401a8d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401a91:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401a95:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401a98:	41 8b 43 68          	mov    0x68(%r11),%eax
  401a9c:	01 c0                	add    %eax,%eax
  401a9e:	41 39 c0             	cmp    %eax,%r8d
  401aa1:	74 19                	je     401abc <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401aa3:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  401aaa:	83 c1 01             	add    $0x1,%ecx
  401aad:	48 63 c1             	movslq %ecx,%rax
  401ab0:	48 83 c7 01          	add    $0x1,%rdi
  401ab4:	49 89 c1             	mov    %rax,%r9
  401ab7:	48 39 f8             	cmp    %rdi,%rax
  401aba:	7c c2                	jl     401a7e <findavailable+0x3e>
      if (*availableidx == 0) {
  401abc:	31 c0                	xor    %eax,%eax
  401abe:	45 85 c0             	test   %r8d,%r8d
  401ac1:	0f 94 c0             	sete   %al
}
  401ac4:	c3                   	ret
  401ac5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401ad0 <singlewriter3>:
}
  401ad0:	c3                   	ret
  401ad1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401adc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401ae0 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401ae0:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  401ae6:	85 c0                	test   %eax,%eax
  401ae8:	74 1e                	je     401b08 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401aea:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401aec:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401aed:	55                   	push   %rbp
  401aee:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401aef:	8b 77 68             	mov    0x68(%rdi),%esi
  401af2:	48 89 fb             	mov    %rdi,%rbx
  401af5:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401af8:	f7 f9                	idiv   %ecx
  401afa:	85 d2                	test   %edx,%edx
  401afc:	74 12                	je     401b10 <singlewriter2+0x30>
}
  401afe:	5b                   	pop    %rbx
  401aff:	5d                   	pop    %rbp
  401b00:	41 5c                	pop    %r12
  401b02:	c3                   	ret
  401b03:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401b08:	c3                   	ret
  401b09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct Data * thread = &data->threads[data->threadindex];
  401b10:	48 63 6f 64          	movslq 0x64(%rdi),%rbp
  401b14:	48 c1 e5 0a          	shl    $0xa,%rbp
  401b18:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401b1c:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401b21:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401b28:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401b2c:	49 c1 e4 04          	shl    $0x4,%r12
  401b30:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401b37:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401b3c:	e8 0f f5 ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401b41:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401b47:	83 c0 01             	add    $0x1,%eax
  401b4a:	99                   	cltd
  401b4b:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  401b51:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401b54:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401b5a:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401b5e:	48 8b 05 e3 16 00 00 	mov    0x16e3(%rip),%rax        # 403248 <_IO_stdin_used+0x248>
  401b65:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  401b6a:	5b                   	pop    %rbx
  401b6b:	5d                   	pop    %rbp
  401b6c:	41 5c                	pop    %r12
  401b6e:	c3                   	ret
  401b6f:	90                   	nop

0000000000401b70 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b70:	41 55                	push   %r13
  401b72:	49 89 d5             	mov    %rdx,%r13
  401b75:	41 54                	push   %r12
  401b77:	49 89 cc             	mov    %rcx,%r12
  401b7a:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401b7b:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b7e:	48 89 fd             	mov    %rdi,%rbp
  401b81:	53                   	push   %rbx
  401b82:	48 89 f3             	mov    %rsi,%rbx
  401b85:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401b89:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b8d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401b96:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401b9b:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401b9d:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401ba5:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  401bab:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401bb3:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401bbb:	83 c0 01             	add    $0x1,%eax
  401bbe:	99                   	cltd
  401bbf:	f7 7f 68             	idivl  0x68(%rdi)
  401bc2:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401bc8:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401bcd:	4c 89 e9             	mov    %r13,%rcx
  401bd0:	e8 6b fe ff ff       	call   401a40 <findavailable>
  if (fill == 1) {
  401bd5:	83 f8 01             	cmp    $0x1,%eax
  401bd8:	0f 84 3c 01 00 00    	je     401d1a <singlewriter+0x1aa>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401bde:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401be3:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401be8:	4c 89 e2             	mov    %r12,%rdx
  401beb:	4c 89 ee             	mov    %r13,%rsi
  401bee:	48 89 ef             	mov    %rbp,%rdi
  401bf1:	e8 ba fd ff ff       	call   4019b0 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401bf6:	4c 63 44 24 0c       	movslq 0xc(%rsp),%r8
  401bfb:	45 85 c0             	test   %r8d,%r8d
  401bfe:	0f 8e 3d 01 00 00    	jle    401d41 <singlewriter+0x1d1>
  401c04:	44 8b 4c 24 14       	mov    0x14(%rsp),%r9d
          if (assignedchunk == availableidx) {
  401c09:	31 c9                	xor    %ecx,%ecx
  401c0b:	eb 58                	jmp    401c65 <singlewriter+0xf5>
  401c0d:	0f 1f 00             	nopl   (%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c10:	48 8b 04 cb          	mov    (%rbx,%rcx,8),%rax
          int thread = readyreaders[x];
  401c14:	49 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%rdx
  401c19:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401c1c:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c20:	48 c1 e0 05          	shl    $0x5,%rax
  401c24:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
          int thread = readyreaders[x];
  401c2b:	48 89 d7             	mov    %rdx,%rdi
          data->threads[thread].reading = chunk;
  401c2e:	48 c1 e2 0a          	shl    $0xa,%rdx
          data->threads[thread].start = start;
  401c32:	66 0f 6e 00          	movd   (%rax),%xmm0
  401c36:	66 0f 6e 48 08       	movd   0x8(%rax),%xmm1
          chunk->available = READING;
  401c3b:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
          data->threads[thread].reading = chunk;
  401c42:	48 03 55 30          	add    0x30(%rbp),%rdx
          data->threads[thread].start = start;
  401c46:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401c4a:	48 89 82 a8 00 00 00 	mov    %rax,0xa8(%rdx)
          chunk->owner = thread;
  401c51:	89 78 14             	mov    %edi,0x14(%rax)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401c54:	83 8a c8 00 00 00 10 	orl    $0x10,0xc8(%rdx)
          data->threads[thread].start = start;
  401c5b:	66 0f d6 42 14       	movq   %xmm0,0x14(%rdx)
        for (int x = 0; x < readers ; x++) {
  401c60:	49 39 c8             	cmp    %rcx,%r8
  401c63:	74 07                	je     401c6c <singlewriter+0xfc>
  401c65:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401c67:	4c 39 c9             	cmp    %r9,%rcx
  401c6a:	75 a4                	jne    401c10 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401c6c:	44 8b 4c 24 10       	mov    0x10(%rsp),%r9d
  401c71:	45 85 c9             	test   %r9d,%r9d
  401c74:	7e 68                	jle    401cde <singlewriter+0x16e>
                if (assignedchunk  == availableidx) {
  401c76:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
  401c7b:	41 01 f1             	add    %esi,%r9d
  401c7e:	eb 59                	jmp    401cd9 <singlewriter+0x169>
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c80:	8d 7e 01             	lea    0x1(%rsi),%edi
  401c83:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401c86:	49 63 14 24          	movslq (%r12),%rdx
   for (int x = 0; x < writers ; x++) {
  401c8a:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c8e:	48 8b 04 f3          	mov    (%rbx,%rsi,8),%rax
          int thread = readywriters[x];
  401c92:	48 89 d1             	mov    %rdx,%rcx
          data->threads[thread].writing = chunk;
  401c95:	48 c1 e2 0a          	shl    $0xa,%rdx
  401c99:	48 03 55 30          	add    0x30(%rbp),%rdx
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c9d:	48 c1 e0 05          	shl    $0x5,%rax
  401ca1:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
          data->threads[thread].publishstart = start;
  401ca8:	66 0f 6e 00          	movd   (%rax),%xmm0
  401cac:	66 0f 6e 50 08       	movd   0x8(%rax),%xmm2
      chunk->available = WRITING;
  401cb1:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
          data->threads[thread].writing = chunk;
  401cb8:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
          data->threads[thread].publishstart = start;
  401cbf:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          chunk->owner = thread;
  401cc3:	89 48 14             	mov    %ecx,0x14(%rax)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401cc6:	83 8a c8 00 00 00 20 	orl    $0x20,0xc8(%rdx)
          data->threads[thread].publishstart = start;
  401ccd:	66 0f d6 42 40       	movq   %xmm0,0x40(%rdx)
   for (int x = 0; x < writers ; x++) {
  401cd2:	44 39 cf             	cmp    %r9d,%edi
  401cd5:	74 07                	je     401cde <singlewriter+0x16e>
  401cd7:	89 fe                	mov    %edi,%esi
                if (assignedchunk  == availableidx) {
  401cd9:	41 39 f0             	cmp    %esi,%r8d
  401cdc:	75 a2                	jne    401c80 <singlewriter+0x110>
      for (int x = 0; x < data->threadsize ; x++) {
  401cde:	8b 7d 68             	mov    0x68(%rbp),%edi
  401ce1:	85 ff                	test   %edi,%edi
  401ce3:	7e 33                	jle    401d18 <singlewriter+0x1a8>
        if (data->threads[x].newmask != 0) {
  401ce5:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401ce9:	31 d2                	xor    %edx,%edx
  401ceb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401cf0:	48 63 ca             	movslq %edx,%rcx
  401cf3:	48 89 c8             	mov    %rcx,%rax
  401cf6:	48 c1 e0 0a          	shl    $0xa,%rax
  401cfa:	4c 01 c0             	add    %r8,%rax
  401cfd:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401d03:	85 f6                	test   %esi,%esi
  401d05:	74 31                	je     401d38 <singlewriter+0x1c8>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401d07:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401d0b:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401d0e:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401d11:	8b 7d 68             	mov    0x68(%rbp),%edi
  401d14:	39 fa                	cmp    %edi,%edx
  401d16:	7c d8                	jl     401cf0 <singlewriter+0x180>
  return 0;
  401d18:	31 c0                	xor    %eax,%eax
}
  401d1a:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401d1f:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401d28:	75 1e                	jne    401d48 <singlewriter+0x1d8>
  401d2a:	48 83 c4 28          	add    $0x28,%rsp
  401d2e:	5b                   	pop    %rbx
  401d2f:	5d                   	pop    %rbp
  401d30:	41 5c                	pop    %r12
  401d32:	41 5d                	pop    %r13
  401d34:	c3                   	ret
  401d35:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401d38:	83 c2 01             	add    $0x1,%edx
  401d3b:	39 fa                	cmp    %edi,%edx
  401d3d:	7c b1                	jl     401cf0 <singlewriter+0x180>
  401d3f:	eb d7                	jmp    401d18 <singlewriter+0x1a8>
      int assignedchunk = 0;
  401d41:	31 f6                	xor    %esi,%esi
  401d43:	e9 24 ff ff ff       	jmp    401c6c <singlewriter+0xfc>
}
  401d48:	e8 13 f3 ff ff       	call   401060 <__stack_chk_fail@plt>
  401d4d:	0f 1f 00             	nopl   (%rax)

0000000000401d50 <threadwork>:
int * threadwork(struct Data * data) {
  401d50:	41 56                	push   %r14
  401d52:	41 55                	push   %r13
  401d54:	41 54                	push   %r12
  401d56:	55                   	push   %rbp
  401d57:	53                   	push   %rbx
  401d58:	48 89 fb             	mov    %rdi,%rbx
  401d5b:	48 83 ec 20          	sub    $0x20,%rsp
  long thiswrite = data->main->globalwrite[data->mystream * 128];
  401d5f:	48 8b 57 28          	mov    0x28(%rdi),%rdx
  int cursorlimit = data->threadsize;
  401d63:	8b 6f 68             	mov    0x68(%rdi),%ebp
int * threadwork(struct Data * data) {
  401d66:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401d6f:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401d74:	31 c0                	xor    %eax,%eax
  long thiswrite = data->main->globalwrite[data->mystream * 128];
  401d76:	8b 87 8c 03 00 00    	mov    0x38c(%rdi),%eax
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401d7c:	48 89 e6             	mov    %rsp,%rsi
  401d7f:	bf 04 00 00 00       	mov    $0x4,%edi
  long thiswrite = data->main->globalwrite[data->mystream * 128];
  401d84:	48 8b 92 80 03 00 00 	mov    0x380(%rdx),%rdx
  401d8b:	c1 e0 07             	shl    $0x7,%eax
  401d8e:	48 98                	cltq
  401d90:	4c 8b 2c c2          	mov    (%rdx,%rax,8),%r13
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401d94:	e8 b7 f2 ff ff       	call   401050 <clock_gettime@plt>
  if (data->running == 2) {
  401d99:	83 7b 5c 02          	cmpl   $0x2,0x5c(%rbx)
        buffer = data->mystream << 24 | ( (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth) << 16 | data->writecursor % 0xff;
  401d9d:	48 63 cd             	movslq %ebp,%rcx
  if (data->running == 2) {
  401da0:	0f 84 82 01 00 00    	je     401f28 <threadwork+0x1d8>
long thisgroup = data->main->globalwrite[data->mystream * 128] / epochsize;
  401da6:	4c 8b 4b 28          	mov    0x28(%rbx),%r9
  401daa:	8b 83 8c 03 00 00    	mov    0x38c(%rbx),%eax
  401db0:	49 8b 91 80 03 00 00 	mov    0x380(%r9),%rdx
  401db7:	c1 e0 07             	shl    $0x7,%eax
  401dba:	48 98                	cltq
  401dbc:	48 8b 04 c2          	mov    (%rdx,%rax,8),%rax
  401dc0:	48 99                	cqto
  401dc2:	48 f7 f9             	idiv   %rcx
  if (thisgroup != data->lastgroup) {
  401dc5:	48 63 93 88 03 00 00 	movslq 0x388(%rbx),%rdx
  401dcc:	48 39 c2             	cmp    %rax,%rdx
  401dcf:	74 0a                	je     401ddb <threadwork+0x8b>
      data->writecursor = 0;
  401dd1:	c7 83 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rbx)
  if (data->globalread[data->laststream].global < thiswrite) {  
  401ddb:	4c 63 a3 90 03 00 00 	movslq 0x390(%rbx),%r12
  401de2:	48 8b bb 48 03 00 00 	mov    0x348(%rbx),%rdi
   data->lastgroup = thisgroup;
  401de9:	89 83 88 03 00 00    	mov    %eax,0x388(%rbx)
  if (data->globalread[data->laststream].global < thiswrite) {  
  401def:	4d 89 e2             	mov    %r12,%r10
  401df2:	49 c1 e4 03          	shl    $0x3,%r12
  401df6:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
  401dfa:	48 63 16             	movslq (%rsi),%rdx
  401dfd:	48 89 d0             	mov    %rdx,%rax
  401e00:	4c 39 ea             	cmp    %r13,%rdx
  401e03:	0f 8d f9 00 00 00    	jge    401f02 <threadwork+0x1b2>
            long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  401e09:	99                   	cltd
   data->freq++;
  401e0a:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
        buffer = data->laststream << 24 | (past << 16) | data->globalread[data->laststream].cursor % 0xff;
  401e0f:	45 89 d6             	mov    %r10d,%r14d
            long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  401e12:	f7 fd                	idiv   %ebp
  401e14:	8d 48 ff             	lea    -0x1(%rax),%ecx
  401e17:	48 63 d1             	movslq %ecx,%rdx
  401e1a:	89 c8                	mov    %ecx,%eax
  401e1c:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401e23:	c1 f8 1f             	sar    $0x1f,%eax
  401e26:	48 c1 ea 20          	shr    $0x20,%rdx
  401e2a:	01 ca                	add    %ecx,%edx
  401e2c:	c1 fa 07             	sar    $0x7,%edx
  401e2f:	29 c2                	sub    %eax,%edx
  401e31:	89 d0                	mov    %edx,%eax
  401e33:	c1 e0 08             	shl    $0x8,%eax
  401e36:	29 d0                	sub    %edx,%eax
  401e38:	29 c1                	sub    %eax,%ecx
  401e3a:	31 c0                	xor    %eax,%eax
  401e3c:	48 63 c9             	movslq %ecx,%rcx
  401e3f:	48 85 c9             	test   %rcx,%rcx
  401e42:	48 0f 48 c8          	cmovs  %rax,%rcx
        buffer = data->laststream << 24 | (past << 16) | data->globalread[data->laststream].cursor % 0xff;
  401e46:	48 63 46 04          	movslq 0x4(%rsi),%rax
  401e4a:	41 c1 e6 18          	shl    $0x18,%r14d
  401e4e:	49 89 c0             	mov    %rax,%r8
  401e51:	48 69 c0 81 80 80 80 	imul   $0xffffffff80808081,%rax,%rax
  401e58:	44 89 c2             	mov    %r8d,%edx
  401e5b:	c1 fa 1f             	sar    $0x1f,%edx
  401e5e:	48 c1 e8 20          	shr    $0x20,%rax
  401e62:	44 01 c0             	add    %r8d,%eax
  401e65:	c1 f8 07             	sar    $0x7,%eax
  401e68:	29 d0                	sub    %edx,%eax
  401e6a:	89 c2                	mov    %eax,%edx
  401e6c:	c1 e2 08             	shl    $0x8,%edx
  401e6f:	29 c2                	sub    %eax,%edx
  401e71:	44 89 c0             	mov    %r8d,%eax
  401e74:	29 d0                	sub    %edx,%eax
  401e76:	41 09 c6             	or     %eax,%r14d
  401e79:	48 89 c8             	mov    %rcx,%rax
  401e7c:	48 c1 e0 10          	shl    $0x10,%rax
  401e80:	4d 63 f6             	movslq %r14d,%r14
  401e83:	49 09 c6             	or     %rax,%r14
    if (data->threadindex == 1) {
  401e86:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  401e8a:	0f 84 c8 01 00 00    	je     402058 <threadwork+0x308>
        if (data->main->works[buffer] != -1) {
  401e90:	4d 03 71 70          	add    0x70(%r9),%r14
  401e94:	41 80 3e ff          	cmpb   $0xff,(%r14)
  401e98:	74 1e                	je     401eb8 <threadwork+0x168>
          data->successreads++;
  401e9a:	48 83 83 98 03 00 00 01 	addq   $0x1,0x398(%rbx)
          data->globalread[thistream].cursor = 0;
  401ea2:	c7 46 04 00 00 00 00 	movl   $0x0,0x4(%rsi)
          data->main->works[buffer] = -1;
  401ea9:	41 c6 06 ff          	movb   $0xff,(%r14)
    if (data->globalread[thistream].global + 1 == thiswrite) {
  401ead:	48 8b bb 48 03 00 00 	mov    0x348(%rbx),%rdi
  401eb4:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
  401eb8:	44 8b 06             	mov    (%rsi),%r8d
      if (data->laststream == data->mystream) {
  401ebb:	44 8b 93 8c 03 00 00 	mov    0x38c(%rbx),%r10d
      data->laststream = (data->laststream + 1);
  401ec2:	8b 8b 90 03 00 00    	mov    0x390(%rbx),%ecx
    if (data->globalread[thistream].global + 1 == thiswrite) {
  401ec8:	45 8d 48 01          	lea    0x1(%r8),%r9d
  401ecc:	49 63 c1             	movslq %r9d,%rax
  401ecf:	49 39 c5             	cmp    %rax,%r13
  401ed2:	0f 84 b8 01 00 00    	je     402090 <threadwork+0x340>
    } else if (data->globalread[thistream].cursor < cursorlimit) {
  401ed8:	8b 56 04             	mov    0x4(%rsi),%edx
  401edb:	39 d5                	cmp    %edx,%ebp
  401edd:	0f 8f 3d 01 00 00    	jg     402020 <threadwork+0x2d0>
    if (data->globalread[thistream].cursor == cursorlimit) {
  401ee3:	39 d5                	cmp    %edx,%ebp
  401ee5:	0f 84 54 01 00 00    	je     40203f <threadwork+0x2ef>
    if (data->laststream == data->mystream) {
  401eeb:	44 39 d1             	cmp    %r10d,%ecx
  401eee:	75 09                	jne    401ef9 <threadwork+0x1a9>
      data->laststream = data->laststream + 1;
  401ef0:	83 c1 01             	add    $0x1,%ecx
  401ef3:	89 8b 90 03 00 00    	mov    %ecx,0x390(%rbx)
    if (data->laststream == 5) {
  401ef9:	83 f9 05             	cmp    $0x5,%ecx
  401efc:	0f 84 06 01 00 00    	je     402008 <threadwork+0x2b8>
}
  401f02:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  401f07:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401f10:	0f 85 dc 01 00 00    	jne    4020f2 <threadwork+0x3a2>
  401f16:	48 83 c4 20          	add    $0x20,%rsp
  401f1a:	31 c0                	xor    %eax,%eax
  401f1c:	5b                   	pop    %rbx
  401f1d:	5d                   	pop    %rbp
  401f1e:	41 5c                	pop    %r12
  401f20:	41 5d                	pop    %r13
  401f22:	41 5e                	pop    %r14
  401f24:	c3                   	ret
  401f25:	0f 1f 00             	nopl   (%rax)
        buffer = data->mystream << 24 | ( (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth) << 16 | data->writecursor % 0xff;
  401f28:	8b b3 8c 03 00 00    	mov    0x38c(%rbx),%esi
  401f2e:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
    if (data->threadindex == 1) {
  401f32:	44 8b 43 64          	mov    0x64(%rbx),%r8d
        buffer = data->mystream << 24 | ( (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth) << 16 | data->writecursor % 0xff;
  401f36:	89 f0                	mov    %esi,%eax
  401f38:	48 8b 97 80 03 00 00 	mov    0x380(%rdi),%rdx
  401f3f:	c1 e6 18             	shl    $0x18,%esi
  401f42:	c1 e0 07             	shl    $0x7,%eax
  401f45:	48 98                	cltq
  401f47:	48 8b 04 c2          	mov    (%rdx,%rax,8),%rax
  401f4b:	48 99                	cqto
  401f4d:	48 f7 f9             	idiv   %rcx
  401f50:	48 ba 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%rdx
  401f5a:	49 89 c1             	mov    %rax,%r9
  401f5d:	48 f7 ea             	imul   %rdx
  401f60:	4c 89 c8             	mov    %r9,%rax
  401f63:	48 c1 f8 3f          	sar    $0x3f,%rax
  401f67:	4c 01 ca             	add    %r9,%rdx
  401f6a:	48 c1 fa 07          	sar    $0x7,%rdx
  401f6e:	48 29 c2             	sub    %rax,%rdx
  401f71:	4c 89 c8             	mov    %r9,%rax
  401f74:	49 89 d2             	mov    %rdx,%r10
  401f77:	49 c1 e2 08          	shl    $0x8,%r10
  401f7b:	49 29 d2             	sub    %rdx,%r10
  401f7e:	48 63 93 80 01 00 00 	movslq 0x180(%rbx),%rdx
  401f85:	4c 29 d0             	sub    %r10,%rax
  401f88:	49 89 d1             	mov    %rdx,%r9
  401f8b:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401f92:	48 c1 e0 10          	shl    $0x10,%rax
  401f96:	45 89 ca             	mov    %r9d,%r10d
  401f99:	41 c1 fa 1f          	sar    $0x1f,%r10d
  401f9d:	48 c1 ea 20          	shr    $0x20,%rdx
  401fa1:	44 01 ca             	add    %r9d,%edx
  401fa4:	c1 fa 07             	sar    $0x7,%edx
  401fa7:	44 29 d2             	sub    %r10d,%edx
  401faa:	41 89 d2             	mov    %edx,%r10d
  401fad:	41 c1 e2 08          	shl    $0x8,%r10d
  401fb1:	41 29 d2             	sub    %edx,%r10d
  401fb4:	45 29 d1             	sub    %r10d,%r9d
  401fb7:	41 09 f1             	or     %esi,%r9d
  401fba:	4d 63 c9             	movslq %r9d,%r9
  401fbd:	4c 09 c8             	or     %r9,%rax
  if (data->main->works[buffer] != -1) {
  401fc0:	48 03 47 70          	add    0x70(%rdi),%rax
  401fc4:	80 38 ff             	cmpb   $0xff,(%rax)
  401fc7:	74 05                	je     401fce <threadwork+0x27e>
    data->freq_writes++;
  401fc9:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
  data->main->works[buffer] = data->threadindex;
  401fce:	44 88 00             	mov    %r8b,(%rax)
    data->writecursor = (data->writecursor + 1) % cursorlimit;
  401fd1:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
  401fd7:	83 c0 01             	add    $0x1,%eax
  401fda:	99                   	cltd
  401fdb:	f7 fd                	idiv   %ebp
    __atomic_fetch_add(&data->main->globalwrite[data->mystream * 128], 1, __ATOMIC_RELAXED);
  401fdd:	8b 83 8c 03 00 00    	mov    0x38c(%rbx),%eax
  401fe3:	c1 e0 07             	shl    $0x7,%eax
  401fe6:	48 98                	cltq
    data->writecursor = (data->writecursor + 1) % cursorlimit;
  401fe8:	89 93 80 01 00 00    	mov    %edx,0x180(%rbx)
    __atomic_fetch_add(&data->main->globalwrite[data->mystream * 128], 1, __ATOMIC_RELAXED);
  401fee:	48 8b 53 28          	mov    0x28(%rbx),%rdx
  401ff2:	48 8b 92 80 03 00 00 	mov    0x380(%rdx),%rdx
  401ff9:	f0 48 83 04 c2 01    	lock addq $0x1,(%rdx,%rax,8)
  401fff:	e9 a2 fd ff ff       	jmp    401da6 <threadwork+0x56>
  402004:	0f 1f 40 00          	nopl   0x0(%rax)
       data->laststream = 0;
  402008:	c7 83 90 03 00 00 00 00 00 00 	movl   $0x0,0x390(%rbx)
       data->globalread[data->laststream].cursor = 0;
  402012:	c7 47 04 00 00 00 00 	movl   $0x0,0x4(%rdi)
  402019:	e9 e4 fe ff ff       	jmp    401f02 <threadwork+0x1b2>
  40201e:	66 90                	xchg   %ax,%ax
      if (data->globalread[thistream].cursor + 1 == cursorlimit) {
  402020:	8d 42 01             	lea    0x1(%rdx),%eax
      data->globalread[thistream].global++;
  402023:	44 89 0e             	mov    %r9d,(%rsi)
      if (data->globalread[thistream].cursor + 1 == cursorlimit) {
  402026:	39 c5                	cmp    %eax,%ebp
  402028:	0f 84 aa 00 00 00    	je     4020d8 <threadwork+0x388>
        data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1) % cursorlimit;
  40202e:	99                   	cltd
  40202f:	45 89 c8             	mov    %r9d,%r8d
  402032:	f7 fd                	idiv   %ebp
  402034:	89 56 04             	mov    %edx,0x4(%rsi)
    if (data->globalread[thistream].cursor == cursorlimit) {
  402037:	39 d5                	cmp    %edx,%ebp
  402039:	0f 85 ac fe ff ff    	jne    401eeb <threadwork+0x19b>
      data->globalread[thistream].global++;
  40203f:	41 83 c0 01          	add    $0x1,%r8d
      data->globalread[thistream].cursor = 0;
  402043:	c7 46 04 00 00 00 00 	movl   $0x0,0x4(%rsi)
      data->globalread[thistream].global++;
  40204a:	44 89 06             	mov    %r8d,(%rsi)
      data->globalread[thistream].cursor = 0;
  40204d:	e9 99 fe ff ff       	jmp    401eeb <threadwork+0x19b>
  402052:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          printf("r %d %d %d %d\n", data->laststream, past, data->globalread[data->laststream].cursor, data->main->works[buffer]);
  402058:	49 8b 41 70          	mov    0x70(%r9),%rax
  40205c:	48 8d 35 a1 0f 00 00 	lea    0xfa1(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  402063:	bf 01 00 00 00       	mov    $0x1,%edi
  402068:	44 89 d2             	mov    %r10d,%edx
  40206b:	46 0f be 0c 30       	movsbl (%rax,%r14,1),%r9d
  402070:	31 c0                	xor    %eax,%eax
  402072:	e8 29 f0 ff ff       	call   4010a0 <__printf_chk@plt>
          data->globalread[thistream].cursor = 0;
  402077:	48 8b bb 48 03 00 00 	mov    0x348(%rbx),%rdi
        if (data->main->works[buffer] != -1) {
  40207e:	4c 8b 4b 28          	mov    0x28(%rbx),%r9
          data->globalread[thistream].cursor = 0;
  402082:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
  402086:	e9 05 fe ff ff       	jmp    401e90 <threadwork+0x140>
  40208b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->laststream = (data->laststream + 1);
  402090:	8d 41 01             	lea    0x1(%rcx),%eax
      data->globalread[thistream].cursor = 0;
  402093:	c7 46 04 00 00 00 00 	movl   $0x0,0x4(%rsi)
      data->globalread[thistream].global++;
  40209a:	44 89 0e             	mov    %r9d,(%rsi)
      data->laststream = (data->laststream + 1);
  40209d:	89 83 90 03 00 00    	mov    %eax,0x390(%rbx)
      if (data->laststream == data->mystream) {
  4020a3:	44 39 d0             	cmp    %r10d,%eax
  4020a6:	74 18                	je     4020c0 <threadwork+0x370>
    if (data->globalread[thistream].cursor == cursorlimit) {
  4020a8:	89 c1                	mov    %eax,%ecx
  4020aa:	85 ed                	test   %ebp,%ebp
  4020ac:	0f 85 47 fe ff ff    	jne    401ef9 <threadwork+0x1a9>
  4020b2:	45 89 c8             	mov    %r9d,%r8d
  4020b5:	eb 88                	jmp    40203f <threadwork+0x2ef>
  4020b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        data->laststream = (data->laststream + 1);
  4020c0:	83 c1 02             	add    $0x2,%ecx
  4020c3:	45 89 c8             	mov    %r9d,%r8d
  4020c6:	31 d2                	xor    %edx,%edx
  4020c8:	89 8b 90 03 00 00    	mov    %ecx,0x390(%rbx)
  4020ce:	e9 10 fe ff ff       	jmp    401ee3 <threadwork+0x193>
  4020d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        data->laststream = (data->laststream + 1);
  4020d8:	83 c1 01             	add    $0x1,%ecx
  4020db:	45 89 c8             	mov    %r9d,%r8d
  4020de:	31 d2                	xor    %edx,%edx
  4020e0:	89 8b 90 03 00 00    	mov    %ecx,0x390(%rbx)
        data->globalread[thistream].cursor = 0;
  4020e6:	c7 46 04 00 00 00 00 	movl   $0x0,0x4(%rsi)
  4020ed:	e9 f1 fd ff ff       	jmp    401ee3 <threadwork+0x193>
}
  4020f2:	e8 69 ef ff ff       	call   401060 <__stack_chk_fail@plt>
  4020f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000402100 <work>:
void * work(void * arg) {
  402100:	53                   	push   %rbx
  402101:	8b 57 64             	mov    0x64(%rdi),%edx
  402104:	48 89 fb             	mov    %rdi,%rbx
  402107:	48 8d 35 05 0f 00 00 	lea    0xf05(%rip),%rsi        # 403013 <_IO_stdin_used+0x13>
  40210e:	bf 01 00 00 00       	mov    $0x1,%edi
  402113:	31 c0                	xor    %eax,%eax
  402115:	e8 86 ef ff ff       	call   4010a0 <__printf_chk@plt>
  while (data->running > 0)  {
  40211a:	8b 53 5c             	mov    0x5c(%rbx),%edx
  40211d:	85 d2                	test   %edx,%edx
  40211f:	7e 16                	jle    402137 <work+0x37>
  402121:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      threadwork(data);
  402128:	48 89 df             	mov    %rbx,%rdi
  40212b:	e8 20 fc ff ff       	call   401d50 <threadwork>
  while (data->running > 0)  {
  402130:	8b 43 5c             	mov    0x5c(%rbx),%eax
  402133:	85 c0                	test   %eax,%eax
  402135:	7f f1                	jg     402128 <work+0x28>
  402137:	8b 53 64             	mov    0x64(%rbx),%edx
  40213a:	48 8d 35 e5 0e 00 00 	lea    0xee5(%rip),%rsi        # 403026 <_IO_stdin_used+0x26>
  402141:	bf 01 00 00 00       	mov    $0x1,%edi
  402146:	31 c0                	xor    %eax,%eax
  402148:	e8 53 ef ff ff       	call   4010a0 <__printf_chk@plt>
}
  40214d:	5b                   	pop    %rbx
  40214e:	c3                   	ret
  40214f:	90                   	nop

0000000000402150 <work2>:
  while (data->running == 1) {
  402150:	eb 0b                	jmp    40215d <work2+0xd>
  402152:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  402158:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  40215d:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  402161:	74 f5                	je     402158 <work2+0x8>
}
  402163:	c3                   	ret

Disassembly of section .fini:

0000000000402164 <_fini>:
  402164:	f3 0f 1e fa          	endbr64
  402168:	48 83 ec 08          	sub    $0x8,%rsp
  40216c:	48 83 c4 08          	add    $0x8,%rsp
  402170:	c3                   	ret
