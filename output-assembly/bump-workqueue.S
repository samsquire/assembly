
bump-workqueue:     file format elf64-x86-64


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
  401020:	ff 35 5a 3f 00 00    	push   0x3f5a(%rip)        # 404f80 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 5c 3f 00 00    	jmp    *0x3f5c(%rip)        # 404f88 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <__snprintf_chk@plt>:
  401030:	ff 25 5a 3f 00 00    	jmp    *0x3f5a(%rip)        # 404f90 <__snprintf_chk@GLIBC_2.3.4>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <pthread_setaffinity_np@plt>:
  401040:	ff 25 52 3f 00 00    	jmp    *0x3f52(%rip)        # 404f98 <pthread_setaffinity_np@GLIBC_2.34>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <puts@plt>:
  401050:	ff 25 4a 3f 00 00    	jmp    *0x3f4a(%rip)        # 404fa0 <puts@GLIBC_2.2.5>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <clock_gettime@plt>:
  401060:	ff 25 42 3f 00 00    	jmp    *0x3f42(%rip)        # 404fa8 <clock_gettime@GLIBC_2.17>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <__stack_chk_fail@plt>:
  401070:	ff 25 3a 3f 00 00    	jmp    *0x3f3a(%rip)        # 404fb0 <__stack_chk_fail@GLIBC_2.4>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <nanosleep@plt>:
  401080:	ff 25 32 3f 00 00    	jmp    *0x3f32(%rip)        # 404fb8 <nanosleep@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <fputs@plt>:
  401090:	ff 25 2a 3f 00 00    	jmp    *0x3f2a(%rip)        # 404fc0 <fputs@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <calloc@plt>:
  4010a0:	ff 25 22 3f 00 00    	jmp    *0x3f22(%rip)        # 404fc8 <calloc@GLIBC_2.2.5>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <__printf_chk@plt>:
  4010b0:	ff 25 1a 3f 00 00    	jmp    *0x3f1a(%rip)        # 404fd0 <__printf_chk@GLIBC_2.3.4>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <pthread_create@plt>:
  4010c0:	ff 25 12 3f 00 00    	jmp    *0x3f12(%rip)        # 404fd8 <pthread_create@GLIBC_2.34>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010d0 <fopen@plt>:
  4010d0:	ff 25 0a 3f 00 00    	jmp    *0x3f0a(%rip)        # 404fe0 <fopen@GLIBC_2.2.5>
  4010d6:	68 0a 00 00 00       	push   $0xa
  4010db:	e9 40 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010e0 <pthread_join@plt>:
  4010e0:	ff 25 02 3f 00 00    	jmp    *0x3f02(%rip)        # 404fe8 <pthread_join@GLIBC_2.34>
  4010e6:	68 0b 00 00 00       	push   $0xb
  4010eb:	e9 30 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

00000000004010f0 <main>:
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
}

int main(int argc, char **argv) {
  4010f0:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4010f2:	ba 08 00 00 00       	mov    $0x8,%edx
  4010f7:	bf 01 00 00 00       	mov    $0x1,%edi
  4010fc:	48 8d 35 32 1f 00 00 	lea    0x1f32(%rip),%rsi        # 403035 <_IO_stdin_used+0x35>
  401103:	41 56                	push   %r14
  char *works = calloc(worksize, sizeof(char));
  printf("Buffer size %ld\n", worksize);
  int chunkindex = 0;
  int * readcursors = calloc(threadsize, sizeof(int));
  int * writecursors = calloc(threadsize, sizeof(int));
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  401105:	41 be 09 00 00 00    	mov    $0x9,%r14d
int main(int argc, char **argv) {
  40110b:	41 55                	push   %r13
  char *works = calloc(worksize, sizeof(char));
  40110d:	41 bd ff ff ff ff    	mov    $0xffffffff,%r13d
int main(int argc, char **argv) {
  401113:	41 54                	push   %r12
  401115:	55                   	push   %rbp
  401116:	53                   	push   %rbx
  401117:	48 83 ec 78          	sub    $0x78,%rsp
  40111b:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401124:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  401129:	31 c0                	xor    %eax,%eax
  40112b:	e8 80 ff ff ff       	call   4010b0 <__printf_chk@plt>
  401130:	ba 04 00 00 00       	mov    $0x4,%edx
  401135:	48 8d 35 0b 1f 00 00 	lea    0x1f0b(%rip),%rsi        # 403047 <_IO_stdin_used+0x47>
  40113c:	31 c0                	xor    %eax,%eax
  40113e:	bf 01 00 00 00       	mov    $0x1,%edi
  401143:	e8 68 ff ff ff       	call   4010b0 <__printf_chk@plt>
  401148:	ba 20 00 00 00       	mov    $0x20,%edx
  40114d:	48 8d 35 ef 1e 00 00 	lea    0x1eef(%rip),%rsi        # 403043 <_IO_stdin_used+0x43>
  401154:	31 c0                	xor    %eax,%eax
  401156:	bf 01 00 00 00       	mov    $0x1,%edi
  40115b:	e8 50 ff ff ff       	call   4010b0 <__printf_chk@plt>
  401160:	ba 08 00 00 00       	mov    $0x8,%edx
  401165:	48 8d 35 ea 1e 00 00 	lea    0x1eea(%rip),%rsi        # 403056 <_IO_stdin_used+0x56>
  40116c:	31 c0                	xor    %eax,%eax
  40116e:	bf 01 00 00 00       	mov    $0x1,%edi
  401173:	e8 38 ff ff ff       	call   4010b0 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401178:	be 08 00 00 00       	mov    $0x8,%esi
  40117d:	bf 08 00 00 00       	mov    $0x8,%edi
  401182:	e8 19 ff ff ff       	call   4010a0 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401187:	be 38 00 00 00       	mov    $0x38,%esi
  40118c:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401191:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401196:	e8 05 ff ff ff       	call   4010a0 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40119b:	be 00 1c 00 00       	mov    $0x1c00,%esi
  4011a0:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  4011a5:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011aa:	e8 f1 fe ff ff       	call   4010a0 <calloc@plt>
  char *works = calloc(worksize, sizeof(char));
  4011af:	4c 89 ef             	mov    %r13,%rdi
  4011b2:	be 01 00 00 00       	mov    $0x1,%esi
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011b7:	48 89 c3             	mov    %rax,%rbx
  char *works = calloc(worksize, sizeof(char));
  4011ba:	e8 e1 fe ff ff       	call   4010a0 <calloc@plt>
  4011bf:	4c 89 ea             	mov    %r13,%rdx
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4011c2:	45 31 ed             	xor    %r13d,%r13d
  4011c5:	48 8d 35 9f 1e 00 00 	lea    0x1e9f(%rip),%rsi        # 40306b <_IO_stdin_used+0x6b>
  4011cc:	bf 01 00 00 00       	mov    $0x1,%edi
  char *works = calloc(worksize, sizeof(char));
  4011d1:	49 89 c4             	mov    %rax,%r12
  4011d4:	31 c0                	xor    %eax,%eax
  4011d6:	e8 d5 fe ff ff       	call   4010b0 <__printf_chk@plt>
  int * readcursors = calloc(threadsize, sizeof(int));
  4011db:	be 04 00 00 00       	mov    $0x4,%esi
  4011e0:	bf 08 00 00 00       	mov    $0x8,%edi
  4011e5:	4c 8d bb 84 01 00 00 	lea    0x184(%rbx),%r15
  4011ec:	e8 af fe ff ff       	call   4010a0 <calloc@plt>
  int * writecursors = calloc(threadsize, sizeof(int));
  4011f1:	be 04 00 00 00       	mov    $0x4,%esi
  4011f6:	bf 08 00 00 00       	mov    $0x8,%edi
  int * readcursors = calloc(threadsize, sizeof(int));
  4011fb:	48 89 c5             	mov    %rax,%rbp
  int * writecursors = calloc(threadsize, sizeof(int));
  4011fe:	e8 9d fe ff ff       	call   4010a0 <calloc@plt>
  401203:	66 48 0f 6e f5       	movq   %rbp,%xmm6
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  401208:	be 20 00 00 00       	mov    $0x20,%esi
  40120d:	bf 64 00 00 00       	mov    $0x64,%edi
  401212:	66 48 0f 6e c0       	movq   %rax,%xmm0
  401217:	48 8d 2d 5e 1e 00 00 	lea    0x1e5e(%rip),%rbp        # 40307c <_IO_stdin_used+0x7c>
  40121e:	66 0f 6c f0          	punpcklqdq %xmm0,%xmm6
  401222:	0f 29 74 24 10       	movaps %xmm6,0x10(%rsp)
  401227:	e8 74 fe ff ff       	call   4010a0 <calloc@plt>
  40122c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
          for (int x = 0; x < threadsize; x++) {
  401231:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          offset += (threadsize * 2) + 1;
        
     data[chunkindex].writecursors = writecursors;
     data[chunkindex].readcursors = readcursors;
            
    data[chunkindex].owritecursor = middle + 1;
  401238:	41 8d 46 01          	lea    0x1(%r14),%eax
     data[chunkindex].readcursors = readcursors;
  40123c:	66 0f 6f 4c 24 10    	movdqa 0x10(%rsp),%xmm1
  401242:	4c 89 f2             	mov    %r14,%rdx
  401245:	48 89 ee             	mov    %rbp,%rsi
    data[chunkindex].owritecursor = middle + 1;
  401248:	41 89 87 80 00 00 00 	mov    %eax,0x80(%r15)
  40124f:	bf 01 00 00 00       	mov    $0x1,%edi
  401254:	31 c0                	xor    %eax,%eax
          for (int x = 0; x < threadsize; x++) {
  401256:	49 81 c7 80 03 00 00 	add    $0x380,%r15
     data[chunkindex].readcursors = readcursors;
  40125d:	41 0f 11 8f 14 fd ff ff 	movups %xmm1,-0x2ec(%r15)
  401265:	e8 46 fe ff ff       	call   4010b0 <__printf_chk@plt>
    printf("middle %ld\n", middle);
    data[chunkindex].middle = middle;
    data[chunkindex].readcursors[chunkindex] = middle;
  40126a:	49 8b 87 14 fd ff ff 	mov    -0x2ec(%r15),%rax
    data[chunkindex].middle = middle;
  401271:	45 89 b7 80 fc ff ff 	mov    %r14d,-0x380(%r15)
    data[chunkindex].readcursors[chunkindex] = middle;
  401278:	46 89 34 28          	mov    %r14d,(%rax,%r13,1)
    data[chunkindex].writecursors[chunkindex] = middle;
  40127c:	49 8b 87 1c fd ff ff 	mov    -0x2e4(%r15),%rax
  401283:	46 89 34 28          	mov    %r14d,(%rax,%r13,1)
    data[chunkindex].oreadcursor = start;
  401287:	41 8d 46 f7          	lea    -0x9(%r14),%eax
          for (int x = 0; x < threadsize; x++) {
  40128b:	49 83 c6 11          	add    $0x11,%r14
  40128f:	49 83 c5 04          	add    $0x4,%r13
    data[chunkindex].oreadcursor = start;
  401293:	41 89 87 04 fd ff ff 	mov    %eax,-0x2fc(%r15)
          for (int x = 0; x < threadsize; x++) {
  40129a:	49 81 fe 91 00 00 00 	cmp    $0x91,%r14
  4012a1:	75 95                	jne    401238 <main+0x148>
  4012a3:	ba 88 00 00 00       	mov    $0x88,%edx
  4012a8:	bf 01 00 00 00       	mov    $0x1,%edi
  4012ad:	31 c0                	xor    %eax,%eax
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  data[0].works = works;
  4012af:	49 89 de             	mov    %rbx,%r14
  4012b2:	48 8d 35 cf 1d 00 00 	lea    0x1dcf(%rip),%rsi        # 403088 <_IO_stdin_used+0x88>
  int cpu = 0;
  4012b9:	45 31 ed             	xor    %r13d,%r13d
  4012bc:	e8 ef fd ff ff       	call   4010b0 <__printf_chk@plt>
  4012c1:	ba ff ff ff ff       	mov    $0xffffffff,%edx
  4012c6:	48 8d 35 c6 1d 00 00 	lea    0x1dc6(%rip),%rsi        # 403093 <_IO_stdin_used+0x93>
  4012cd:	31 c0                	xor    %eax,%eax
  4012cf:	bf 01 00 00 00       	mov    $0x1,%edi
  4012d4:	e8 d7 fd ff ff       	call   4010b0 <__printf_chk@plt>
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  4012d9:	be 04 00 00 00       	mov    $0x4,%esi
  4012de:	bf 08 00 00 00       	mov    $0x8,%edi
  4012e3:	e8 b8 fd ff ff       	call   4010a0 <calloc@plt>
  4012e8:	66 48 0f 6e f3       	movq   %rbx,%xmm6
  data[0].works = works;
  4012ed:	4c 89 63 78          	mov    %r12,0x78(%rbx)
  4012f1:	45 31 e4             	xor    %r12d,%r12d
  4012f4:	66 48 0f 6e f8       	movq   %rax,%xmm7
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  4012f9:	48 89 c5             	mov    %rax,%rbp
  4012fc:	66 0f 6c fe          	punpcklqdq %xmm6,%xmm7
  401300:	0f 29 7c 24 10       	movaps %xmm7,0x10(%rsp)
  for (int x = 0; x < threadsize ; x++) {
  401305:	0f 1f 00             	nopl   (%rax)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401308:	45 89 ef             	mov    %r13d,%r15d
  40130b:	be 80 00 00 00       	mov    $0x80,%esi
  401310:	bf 01 00 00 00       	mov    $0x1,%edi
    CPU_SET(cpu += 1, data[x].cpu_set);
  401315:	41 83 c5 01          	add    $0x1,%r13d
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401319:	e8 82 fd ff ff       	call   4010a0 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  40131e:	44 89 e9             	mov    %r13d,%ecx
  401321:	ba 01 00 00 00       	mov    $0x1,%edx
  401326:	48 8d 35 73 1e 00 00 	lea    0x1e73(%rip),%rsi        # 4031a0 <_IO_stdin_used+0x1a0>
  40132d:	48 d3 e2             	shl    %cl,%rdx
  401330:	48 09 10             	or     %rdx,(%rax)
  401333:	44 89 e9             	mov    %r13d,%ecx
  401336:	44 89 fa             	mov    %r15d,%edx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401339:	49 89 86 80 00 00 00 	mov    %rax,0x80(%r14)
  401340:	bf 01 00 00 00       	mov    $0x1,%edi
  401345:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  401347:	48 83 c5 04          	add    $0x4,%rbp
  40134b:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  401352:	e8 59 fd ff ff       	call   4010b0 <__printf_chk@plt>
    data[x].threadindex = x;
    data[x].worksize = worksize;
    
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].readies = readies;
  401357:	66 0f 6f 54 24 10    	movdqa 0x10(%rsp),%xmm2
    data[x].readies[x] = 0;
    data[x].buckets = buckets;
  40135d:	48 8b 05 64 1e 00 00 	mov    0x1e64(%rip),%rax        # 4031c8 <_IO_stdin_used+0x1c8>
    data[x].bucketstart = x * buckets ;
  401364:	45 89 a6 20 fd ff ff 	mov    %r12d,-0x2e0(%r14)
    data[x].main = &data[0];
    data[x].threads = data;
    data[x].wantindex = -1;
    data[x].read = 0;
  40136b:	66 0f 6f 1d 6d 1e 00 00 	movdqa 0x1e6d(%rip),%xmm3        # 4031e0 <_IO_stdin_used+0x1e0>
    data[x].newmask = 0;
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401373:	be 30 00 00 00       	mov    $0x30,%esi
    data[x].chunkslen = chunkslen;
  401378:	66 0f 6f 25 70 1e 00 00 	movdqa 0x1e70(%rip),%xmm4        # 4031f0 <_IO_stdin_used+0x1f0>
    data[x].loglevel = debug;
  401380:	41 c7 86 08 fd ff ff 00 00 00 00 	movl   $0x0,-0x2f8(%r14)
    data[x].buckets = buckets;
  40138b:	49 89 86 18 fd ff ff 	mov    %rax,-0x2e8(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401392:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].wantindex = -1;
  401397:	48 8b 05 32 1e 00 00 	mov    0x1e32(%rip),%rax        # 4031d0 <_IO_stdin_used+0x1d0>
  for (int x = 0; x < threadsize ; x++) {
  40139e:	41 81 c4 ff ff ff 1f 	add    $0x1fffffff,%r12d
    data[x].prevread = threadsize;
  4013a5:	66 0f 6f 2d 53 1e 00 00 	movdqa 0x1e53(%rip),%xmm5        # 403200 <_IO_stdin_used+0x200>
    data[x].threadindex = x;
  4013ad:	45 89 be ec fc ff ff 	mov    %r15d,-0x314(%r14)
    data[x].wantindex = -1;
  4013b4:	49 89 86 e0 fc ff ff 	mov    %rax,-0x320(%r14)
    data[x].freelist = freelist;
  4013bb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    data[x].worksize = worksize;
  4013c0:	41 c7 86 e8 fc ff ff ff ff ff ff 	movl   $0xffffffff,-0x318(%r14)
    data[x].threadsize = threadsize;
  4013cb:	41 c7 86 f0 fc ff ff 08 00 00 00 	movl   $0x8,-0x310(%r14)
    data[x].readies[x] = 0;
  4013d6:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
    data[x].threads = data;
  4013dd:	49 89 9e b0 fc ff ff 	mov    %rbx,-0x350(%r14)
    data[x].readcursor = threadsize - 1;
  4013e4:	41 c7 86 80 fe ff ff 07 00 00 00 	movl   $0x7,-0x180(%r14)
    data[x].writecursor = threadsize - 1;
  4013ef:	41 c7 86 00 fe ff ff 07 00 00 00 	movl   $0x7,-0x200(%r14)
    data[x].freelist = freelist;
  4013fa:	49 89 86 28 fd ff ff 	mov    %rax,-0x2d8(%r14)
    data[x].newmask = 0;
  401401:	41 c7 86 50 fd ff ff 00 00 00 00 	movl   $0x0,-0x2b0(%r14)
    data[x].thiswrite = threadsize;
  40140c:	41 c7 46 a8 08 00 00 00 	movl   $0x8,-0x58(%r14)
    data[x].readies = readies;
  401414:	41 0f 29 96 a0 fc ff ff 	movaps %xmm2,-0x360(%r14)
    data[x].read = 0;
  40141c:	41 0f 29 9e 80 fc ff ff 	movaps %xmm3,-0x380(%r14)
    data[x].chunkslen = chunkslen;
  401424:	41 0f 29 a6 40 fd ff ff 	movaps %xmm4,-0x2c0(%r14)
    data[x].prevread = threadsize;
  40142c:	41 0f 11 6e 88       	movups %xmm5,-0x78(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401431:	e8 6a fc ff ff       	call   4010a0 <calloc@plt>
    data[x].epochssize = epochs;
    
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  401436:	be 30 00 00 00       	mov    $0x30,%esi
  40143b:	bf 10 27 00 00       	mov    $0x2710,%edi
    data[x].epochssize = epochs;
  401440:	41 c7 46 a0 80 96 98 00 	movl   $0x989680,-0x60(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401448:	49 89 46 98          	mov    %rax,-0x68(%r14)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  40144c:	e8 4f fc ff ff       	call   4010a0 <calloc@plt>
  401451:	49 89 46 b0          	mov    %rax,-0x50(%r14)
  for (int x = 0; x < threadsize ; x++) {
  401455:	41 83 fd 08          	cmp    $0x8,%r13d
  401459:	0f 85 a9 fe ff ff    	jne    401308 <main+0x218>
  40145f:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
  401464:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
  401469:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  40146e:	49 89 de             	mov    %rbx,%r14
  401471:	49 c7 c5 c0 21 40 00 	mov    $0x4021c0,%r13
  401478:	48 8d bd c0 01 00 00 	lea    0x1c0(%rbp),%rdi
  40147f:	49 89 c4             	mov    %rax,%r12
  401482:	48 89 c3             	mov    %rax,%rbx
  401485:	49 89 ff             	mov    %rdi,%r15
  401488:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  401490:	4c 89 f1             	mov    %r14,%rcx
  401493:	48 89 ee             	mov    %rbp,%rsi
  401496:	48 89 df             	mov    %rbx,%rdi
  401499:	4c 89 ea             	mov    %r13,%rdx
  40149c:	e8 1f fc ff ff       	call   4010c0 <pthread_create@plt>
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4014a1:	48 8b 3b             	mov    (%rbx),%rdi
  for (int x = 0; x < threadsize ; x++) {
  4014a4:	48 83 c5 38          	add    $0x38,%rbp
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4014a8:	49 8b 96 80 00 00 00 	mov    0x80(%r14),%rdx
  4014af:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  4014b4:	48 83 c3 08          	add    $0x8,%rbx
  4014b8:	49 81 c6 80 03 00 00 	add    $0x380,%r14
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4014bf:	e8 7c fb ff ff       	call   401040 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  4014c4:	49 39 ef             	cmp    %rbp,%r15
  4014c7:	75 c7                	jne    401490 <main+0x3a0>
  }
  
  struct timespec time = {
  4014c9:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  4014ce:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  4014d3:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec time = {
  4014d8:	66 0f 6f 05 30 1d 00 00 	movdqa 0x1d30(%rip),%xmm0        # 403210 <_IO_stdin_used+0x210>
  4014e0:	4c 8d 6c 24 38       	lea    0x38(%rsp),%r13
  4014e5:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  4014ea:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4014ee:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  4014f3:	e8 88 fb ff ff       	call   401080 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  4014f8:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
  4014fd:	c7 43 64 00 00 00 00 	movl   $0x0,0x64(%rbx)
  401504:	c7 83 e4 03 00 00 00 00 00 00 	movl   $0x0,0x3e4(%rbx)
  40150e:	c7 83 64 07 00 00 00 00 00 00 	movl   $0x0,0x764(%rbx)
  401518:	48 83 c5 40          	add    $0x40,%rbp
  40151c:	c7 83 e4 0a 00 00 00 00 00 00 	movl   $0x0,0xae4(%rbx)
  401526:	c7 83 64 0e 00 00 00 00 00 00 	movl   $0x0,0xe64(%rbx)
  401530:	c7 83 e4 11 00 00 00 00 00 00 	movl   $0x0,0x11e4(%rbx)
  40153a:	c7 83 64 15 00 00 00 00 00 00 	movl   $0x0,0x1564(%rbx)
  401544:	c7 83 e4 18 00 00 00 00 00 00 	movl   $0x0,0x18e4(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  40154e:	66 90                	xchg   %ax,%ax
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401550:	49 8b 3c 24          	mov    (%r12),%rdi
  401554:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  401557:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  40155b:	e8 80 fb ff ff       	call   4010e0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401560:	49 39 ec             	cmp    %rbp,%r12
  401563:	75 eb                	jne    401550 <main+0x460>
  401565:	48 8d 3d 33 1b 00 00 	lea    0x1b33(%rip),%rdi        # 40309f <_IO_stdin_used+0x9f>
  40156c:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  401570:	45 31 e4             	xor    %r12d,%r12d
  401573:	e8 d8 fa ff ff       	call   401050 <puts@plt>
  for (int x = 0; x < threadsize; x++) {
  401578:	4c 8d b3 48 1c 00 00 	lea    0x1c48(%rbx),%r14
  40157f:	4c 8d 2d 2e 1b 00 00 	lea    0x1b2e(%rip),%r13        # 4030b4 <_IO_stdin_used+0xb4>
  401586:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401590:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401594:	4c 89 ee             	mov    %r13,%rsi
  401597:	bf 01 00 00 00       	mov    $0x1,%edi
  40159c:	31 c0                	xor    %eax,%eax
  40159e:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
  4015a5:	e8 06 fb ff ff       	call   4010b0 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  4015aa:	4c 03 a5 80 fc ff ff 	add    -0x380(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  4015b1:	4c 39 f5             	cmp    %r14,%rbp
  4015b4:	75 da                	jne    401590 <main+0x4a0>
  }
  printf("freq: %ld\n", freq/ seconds);
  4015b6:	4c 89 e0             	mov    %r12,%rax
  4015b9:	48 8d 35 ff 1a 00 00 	lea    0x1aff(%rip),%rsi        # 4030bf <_IO_stdin_used+0xbf>
  4015c0:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
  4015ca:	bf 01 00 00 00       	mov    $0x1,%edi
  4015cf:	48 f7 ed             	imul   %rbp
  4015d2:	4c 89 e0             	mov    %r12,%rax
  4015d5:	4c 8d b3 50 1c 00 00 	lea    0x1c50(%rbx),%r14
  4015dc:	48 c1 f8 3f          	sar    $0x3f,%rax
  4015e0:	48 d1 fa             	sar    %rdx
  4015e3:	48 29 c2             	sub    %rax,%rdx
  4015e6:	31 c0                	xor    %eax,%eax
  4015e8:	49 89 d5             	mov    %rdx,%r13
  4015eb:	e8 c0 fa ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq_ps: %ld\n", (freq*threadsize-1)/ seconds);
  4015f0:	4a 8d 0c e5 ff ff ff ff 	lea    -0x1(,%r12,8),%rcx
  4015f8:	bf 01 00 00 00       	mov    $0x1,%edi
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  4015fd:	41 bc 00 ca 9a 3b    	mov    $0x3b9aca00,%r12d
  printf("freq_ps: %ld\n", (freq*threadsize-1)/ seconds);
  401603:	48 89 c8             	mov    %rcx,%rax
  401606:	48 c1 f9 3f          	sar    $0x3f,%rcx
  40160a:	48 8d 35 b9 1a 00 00 	lea    0x1ab9(%rip),%rsi        # 4030ca <_IO_stdin_used+0xca>
  401611:	48 f7 ed             	imul   %rbp
  401614:	31 c0                	xor    %eax,%eax
  401616:	48 89 d5             	mov    %rdx,%rbp
  401619:	48 d1 fd             	sar    %rbp
  40161c:	48 29 cd             	sub    %rcx,%rbp
  40161f:	48 89 ea             	mov    %rbp,%rdx
  401622:	e8 89 fa ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  401627:	4c 89 e0             	mov    %r12,%rax
  40162a:	bf 01 00 00 00       	mov    $0x1,%edi
  40162f:	48 8d 35 a2 1a 00 00 	lea    0x1aa2(%rip),%rsi        # 4030d8 <_IO_stdin_used+0xd8>
  401636:	48 99                	cqto
  401638:	49 f7 fd             	idiv   %r13
  40163b:	4c 8d 2d bd 1a 00 00 	lea    0x1abd(%rip),%r13        # 4030ff <_IO_stdin_used+0xff>
  401642:	48 89 c2             	mov    %rax,%rdx
  401645:	31 c0                	xor    %eax,%eax
  401647:	e8 64 fa ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*threadsize-1)/seconds));
  40164c:	4c 89 e0             	mov    %r12,%rax
  40164f:	bf 01 00 00 00       	mov    $0x1,%edi
  long freq_writes = 0;
  401654:	45 31 e4             	xor    %r12d,%r12d
  printf("freq latency: %ld\n", 1000000000/((freq*threadsize-1)/seconds));
  401657:	48 99                	cqto
  401659:	48 8d 35 8c 1a 00 00 	lea    0x1a8c(%rip),%rsi        # 4030ec <_IO_stdin_used+0xec>
  401660:	48 f7 fd             	idiv   %rbp
  401663:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  401667:	48 89 c2             	mov    %rax,%rdx
  40166a:	31 c0                	xor    %eax,%eax
  40166c:	e8 3f fa ff ff       	call   4010b0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  401671:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    freq_writes += data[x].freq_writes;
  401678:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  40167c:	4c 89 ee             	mov    %r13,%rsi
  40167f:	bf 01 00 00 00       	mov    $0x1,%edi
  401684:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  401686:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
    freq_writes += data[x].freq_writes;
  40168d:	49 01 d4             	add    %rdx,%r12
  401690:	e8 1b fa ff ff       	call   4010b0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  401695:	4c 39 f5             	cmp    %r14,%rbp
  401698:	75 de                	jne    401678 <main+0x588>
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  40169a:	4c 89 e0             	mov    %r12,%rax
  40169d:	48 8d 35 67 1a 00 00 	lea    0x1a67(%rip),%rsi        # 40310b <_IO_stdin_used+0x10b>
  4016a4:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
  4016ae:	bf 01 00 00 00       	mov    $0x1,%edi
  4016b3:	48 f7 ed             	imul   %rbp
  4016b6:	4c 89 e0             	mov    %r12,%rax
  4016b9:	4c 8d b3 20 03 00 00 	lea    0x320(%rbx),%r14
  4016c0:	48 c1 f8 3f          	sar    $0x3f,%rax
  4016c4:	48 d1 fa             	sar    %rdx
  4016c7:	48 29 c2             	sub    %rax,%rdx
  4016ca:	31 c0                	xor    %eax,%eax
  4016cc:	49 89 d5             	mov    %rdx,%r13
  4016cf:	e8 dc f9 ff ff       	call   4010b0 <__printf_chk@plt>

  printf("freq_writes_total: %ld\n", (freq_writes * threadsize - 1) / seconds);
  4016d4:	4a 8d 0c e5 ff ff ff ff 	lea    -0x1(,%r12,8),%rcx
  4016dc:	bf 01 00 00 00       	mov    $0x1,%edi
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  4016e1:	41 bc 00 ca 9a 3b    	mov    $0x3b9aca00,%r12d
  printf("freq_writes_total: %ld\n", (freq_writes * threadsize - 1) / seconds);
  4016e7:	48 89 c8             	mov    %rcx,%rax
  4016ea:	48 c1 f9 3f          	sar    $0x3f,%rcx
  4016ee:	48 8d 35 28 1a 00 00 	lea    0x1a28(%rip),%rsi        # 40311d <_IO_stdin_used+0x11d>
  4016f5:	48 f7 ed             	imul   %rbp
  4016f8:	31 c0                	xor    %eax,%eax
  4016fa:	48 89 d5             	mov    %rdx,%rbp
  4016fd:	48 d1 fd             	sar    %rbp
  401700:	48 29 cd             	sub    %rcx,%rbp
  401703:	48 89 ea             	mov    %rbp,%rdx
  401706:	e8 a5 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  40170b:	4c 89 e0             	mov    %r12,%rax
  40170e:	bf 01 00 00 00       	mov    $0x1,%edi
  401713:	48 8d 35 1b 1a 00 00 	lea    0x1a1b(%rip),%rsi        # 403135 <_IO_stdin_used+0x135>
  40171a:	48 99                	cqto
  40171c:	49 f7 fd             	idiv   %r13
  40171f:	48 89 c2             	mov    %rax,%rdx
  401722:	31 c0                	xor    %eax,%eax
  401724:	e8 87 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * threadsize - 1) / seconds));
  401729:	4c 89 e0             	mov    %r12,%rax
  40172c:	bf 01 00 00 00       	mov    $0x1,%edi
  401731:	48 8d 35 18 1a 00 00 	lea    0x1a18(%rip),%rsi        # 403150 <_IO_stdin_used+0x150>
  401738:	48 99                	cqto
  40173a:	48 f7 fd             	idiv   %rbp
  40173d:	48 8d 2d a3 19 00 00 	lea    0x19a3(%rip),%rbp        # 4030e7 <_IO_stdin_used+0xe7>
  401744:	48 89 c2             	mov    %rax,%rdx
  401747:	31 c0                	xor    %eax,%eax
  401749:	e8 62 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  40174e:	48 8d 3d 15 1a 00 00 	lea    0x1a15(%rip),%rdi        # 40316a <_IO_stdin_used+0x16a>
  401755:	e8 f6 f8 ff ff       	call   401050 <puts@plt>
  40175a:	48 89 ee             	mov    %rbp,%rsi
  40175d:	bf 01 00 00 00       	mov    $0x1,%edi
  401762:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  401764:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
  40176b:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  401772:	e8 39 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  401777:	48 89 ee             	mov    %rbp,%rsi
  40177a:	bf 01 00 00 00       	mov    $0x1,%edi
  40177f:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  401781:	48 8b 93 08 01 00 00 	mov    0x108(%rbx),%rdx
  401788:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  40178f:	e8 1c f9 ff ff       	call   4010b0 <__printf_chk@plt>
  401794:	48 89 ee             	mov    %rbp,%rsi
  401797:	bf 01 00 00 00       	mov    $0x1,%edi
  40179c:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  40179e:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
  4017a5:	48 2b 93 08 01 00 00 	sub    0x108(%rbx),%rdx
  4017ac:	e8 ff f8 ff ff       	call   4010b0 <__printf_chk@plt>
  4017b1:	48 89 ee             	mov    %rbp,%rsi
  4017b4:	bf 01 00 00 00       	mov    $0x1,%edi
  4017b9:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4017bb:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
  4017c2:	48 2b 93 18 01 00 00 	sub    0x118(%rbx),%rdx
  4017c9:	e8 e2 f8 ff ff       	call   4010b0 <__printf_chk@plt>
  4017ce:	48 89 ee             	mov    %rbp,%rsi
  4017d1:	bf 01 00 00 00       	mov    $0x1,%edi
  4017d6:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  4017d8:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
  4017df:	48 2b 93 28 01 00 00 	sub    0x128(%rbx),%rdx
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  4017e6:	45 31 ed             	xor    %r13d,%r13d
  4017e9:	48 81 c3 20 1f 00 00 	add    $0x1f20,%rbx
  4017f0:	e8 bb f8 ff ff       	call   4010b0 <__printf_chk@plt>
  4017f5:	48 89 ee             	mov    %rbp,%rsi
  4017f8:	bf 01 00 00 00       	mov    $0x1,%edi
  4017fd:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  4017ff:	48 8b 93 f8 e1 ff ff 	mov    -0x1e08(%rbx),%rdx
  401806:	48 2b 93 e8 e1 ff ff 	sub    -0x1e18(%rbx),%rdx
  40180d:	e8 9e f8 ff ff       	call   4010b0 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  401812:	48 8b 93 28 e2 ff ff 	mov    -0x1dd8(%rbx),%rdx
  401819:	48 8d 35 57 19 00 00 	lea    0x1957(%rip),%rsi        # 403177 <_IO_stdin_used+0x177>
  401820:	31 c0                	xor    %eax,%eax
  401822:	48 2b 93 18 e2 ff ff 	sub    -0x1de8(%rbx),%rdx
  401829:	bf 01 00 00 00       	mov    $0x1,%edi
  40182e:	e8 7d f8 ff ff       	call   4010b0 <__printf_chk@plt>
  } 

  if (SAMPLE == 1) {
  char * filename = calloc(100, sizeof(char));
  401833:	be 01 00 00 00       	mov    $0x1,%esi
  401838:	bf 64 00 00 00       	mov    $0x64,%edi
  40183d:	e8 5e f8 ff ff       	call   4010a0 <calloc@plt>
  char * buf = calloc(1000, sizeof(char));
  401842:	be 01 00 00 00       	mov    $0x1,%esi
  401847:	bf e8 03 00 00       	mov    $0x3e8,%edi
  char * filename = calloc(100, sizeof(char));
  40184c:	49 89 c4             	mov    %rax,%r12
  char * buf = calloc(1000, sizeof(char));
  40184f:	e8 4c f8 ff ff       	call   4010a0 <calloc@plt>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401854:	44 8b 8b 50 e1 ff ff 	mov    -0x1eb0(%rbx),%r9d
  40185b:	4c 89 e7             	mov    %r12,%rdi
  40185e:	4c 8d 05 1a 19 00 00 	lea    0x191a(%rip),%r8        # 40317f <_IO_stdin_used+0x17f>
  401865:	b9 64 00 00 00       	mov    $0x64,%ecx
  40186a:	ba 01 00 00 00       	mov    $0x1,%edx
  40186f:	be 64 00 00 00       	mov    $0x64,%esi
  401874:	48 89 c5             	mov    %rax,%rbp
  401877:	31 c0                	xor    %eax,%eax
  401879:	e8 b2 f7 ff ff       	call   401030 <__snprintf_chk@plt>
  memset(filename, 0, 100);
  snprintf(filename, 100, "samples%d", data->threadsize);
  FILE *out_file = fopen(filename, "w");
  40187e:	4c 89 e7             	mov    %r12,%rdi
  401881:	48 8d 35 01 19 00 00 	lea    0x1901(%rip),%rsi        # 403189 <_IO_stdin_used+0x189>
  401888:	e8 43 f8 ff ff       	call   4010d0 <fopen@plt>
  40188d:	49 89 c4             	mov    %rax,%r12
  
  for (int x = 0; x < threadsize; x++) {
    for (int y = 0; y < data[x].epochssize; y++) {
  401890:	41 8b 0e             	mov    (%r14),%ecx
  401893:	45 31 ff             	xor    %r15d,%r15d
  401896:	85 c9                	test   %ecx,%ecx
  401898:	7e 21                	jle    4018bb <main+0x7cb>
  40189a:	49 8b 76 f8          	mov    -0x8(%r14),%rsi
      struct Epoch * epoch = &data[x].epochs[y];
  40189e:	49 63 c7             	movslq %r15d,%rax
  4018a1:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  4018a5:	48 c1 e2 04          	shl    $0x4,%rdx
  4018a9:	48 01 f2             	add    %rsi,%rdx
      if (epoch->set == 1) {
  4018ac:	83 7a 24 01          	cmpl   $0x1,0x24(%rdx)
  4018b0:	74 3e                	je     4018f0 <main+0x800>
    for (int y = 0; y < data[x].epochssize; y++) {
  4018b2:	41 83 c7 01          	add    $0x1,%r15d
  4018b6:	41 39 cf             	cmp    %ecx,%r15d
  4018b9:	7c e3                	jl     40189e <main+0x7ae>
  for (int x = 0; x < threadsize; x++) {
  4018bb:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  4018c2:	49 39 de             	cmp    %rbx,%r14
  4018c5:	75 c9                	jne    401890 <main+0x7a0>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  4018c7:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  4018cc:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4018d5:	0f 85 90 00 00 00    	jne    40196b <main+0x87b>
  4018db:	48 83 c4 78          	add    $0x78,%rsp
  4018df:	31 c0                	xor    %eax,%eax
  4018e1:	5b                   	pop    %rbx
  4018e2:	5d                   	pop    %rbp
  4018e3:	41 5c                	pop    %r12
  4018e5:	41 5d                	pop    %r13
  4018e7:	41 5e                	pop    %r14
  4018e9:	41 5f                	pop    %r15
  4018eb:	c3                   	ret
  4018ec:	0f 1f 40 00          	nopl   0x0(%rax)
  4018f0:	4c 89 e8             	mov    %r13,%rax
  4018f3:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  4018f8:	48 89 ef             	mov    %rbp,%rdi
  4018fb:	48 83 ec 08          	sub    $0x8,%rsp
  4018ff:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  401902:	be 64 00 00 00       	mov    $0x64,%esi
  401907:	48 89 ef             	mov    %rbp,%rdi
    for (int y = 0; y < data[x].epochssize; y++) {
  40190a:	41 83 c7 01          	add    $0x1,%r15d
  40190e:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401913:	4c 8d 05 71 18 00 00 	lea    0x1871(%rip),%r8        # 40318b <_IO_stdin_used+0x18b>
  40191a:	8b 42 28             	mov    0x28(%rdx),%eax
  40191d:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
  401921:	50                   	push   %rax
  401922:	8b 02                	mov    (%rdx),%eax
  401924:	50                   	push   %rax
  401925:	8b 42 20             	mov    0x20(%rdx),%eax
  401928:	ff 72 18             	push   0x18(%rdx)
  40192b:	50                   	push   %rax
  40192c:	31 c0                	xor    %eax,%eax
  40192e:	ff 72 10             	push   0x10(%rdx)
  401931:	ba 01 00 00 00       	mov    $0x1,%edx
  401936:	e8 f5 f6 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  40193b:	48 83 c4 30          	add    $0x30,%rsp
  40193f:	4c 89 e6             	mov    %r12,%rsi
  401942:	48 89 ef             	mov    %rbp,%rdi
  401945:	e8 46 f7 ff ff       	call   401090 <fputs@plt>
  40194a:	41 8b 0e             	mov    (%r14),%ecx
  40194d:	41 39 cf             	cmp    %ecx,%r15d
  401950:	0f 8c 44 ff ff ff    	jl     40189a <main+0x7aa>
  for (int x = 0; x < threadsize; x++) {
  401956:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  40195d:	49 39 de             	cmp    %rbx,%r14
  401960:	0f 85 2a ff ff ff    	jne    401890 <main+0x7a0>
  401966:	e9 5c ff ff ff       	jmp    4018c7 <main+0x7d7>
  40196b:	e8 00 f7 ff ff       	call   401070 <__stack_chk_fail@plt>

0000000000401970 <_start>:
  401970:	f3 0f 1e fa          	endbr64
  401974:	31 ed                	xor    %ebp,%ebp
  401976:	49 89 d1             	mov    %rdx,%r9
  401979:	5e                   	pop    %rsi
  40197a:	48 89 e2             	mov    %rsp,%rdx
  40197d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401981:	50                   	push   %rax
  401982:	54                   	push   %rsp
  401983:	45 31 c0             	xor    %r8d,%r8d
  401986:	31 c9                	xor    %ecx,%ecx
  401988:	48 c7 c7 f0 10 40 00 	mov    $0x4010f0,%rdi
  40198f:	ff 15 5b 36 00 00    	call   *0x365b(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  401995:	f4                   	hlt
  401996:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004019a0 <_dl_relocate_static_pie>:
  4019a0:	f3 0f 1e fa          	endbr64
  4019a4:	c3                   	ret
  4019a5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4019af:	90                   	nop

00000000004019b0 <deregister_tm_clones>:
  4019b0:	b8 10 50 40 00       	mov    $0x405010,%eax
  4019b5:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  4019bb:	74 13                	je     4019d0 <deregister_tm_clones+0x20>
  4019bd:	b8 00 00 00 00       	mov    $0x0,%eax
  4019c2:	48 85 c0             	test   %rax,%rax
  4019c5:	74 09                	je     4019d0 <deregister_tm_clones+0x20>
  4019c7:	bf 10 50 40 00       	mov    $0x405010,%edi
  4019cc:	ff e0                	jmp    *%rax
  4019ce:	66 90                	xchg   %ax,%ax
  4019d0:	c3                   	ret
  4019d1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4019dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004019e0 <register_tm_clones>:
  4019e0:	be 10 50 40 00       	mov    $0x405010,%esi
  4019e5:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  4019ec:	48 89 f0             	mov    %rsi,%rax
  4019ef:	48 c1 ee 3f          	shr    $0x3f,%rsi
  4019f3:	48 c1 f8 03          	sar    $0x3,%rax
  4019f7:	48 01 c6             	add    %rax,%rsi
  4019fa:	48 d1 fe             	sar    %rsi
  4019fd:	74 11                	je     401a10 <register_tm_clones+0x30>
  4019ff:	b8 00 00 00 00       	mov    $0x0,%eax
  401a04:	48 85 c0             	test   %rax,%rax
  401a07:	74 07                	je     401a10 <register_tm_clones+0x30>
  401a09:	bf 10 50 40 00       	mov    $0x405010,%edi
  401a0e:	ff e0                	jmp    *%rax
  401a10:	c3                   	ret
  401a11:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401a1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401a20 <__do_global_dtors_aux>:
  401a20:	f3 0f 1e fa          	endbr64
  401a24:	80 3d e5 35 00 00 00 	cmpb   $0x0,0x35e5(%rip)        # 405010 <__TMC_END__>
  401a2b:	75 13                	jne    401a40 <__do_global_dtors_aux+0x20>
  401a2d:	55                   	push   %rbp
  401a2e:	48 89 e5             	mov    %rsp,%rbp
  401a31:	e8 7a ff ff ff       	call   4019b0 <deregister_tm_clones>
  401a36:	c6 05 d3 35 00 00 01 	movb   $0x1,0x35d3(%rip)        # 405010 <__TMC_END__>
  401a3d:	5d                   	pop    %rbp
  401a3e:	c3                   	ret
  401a3f:	90                   	nop
  401a40:	c3                   	ret
  401a41:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401a4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401a50 <frame_dummy>:
  401a50:	f3 0f 1e fa          	endbr64
  401a54:	eb 8a                	jmp    4019e0 <register_tm_clones>
  401a56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401a60 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  401a60:	83 7f 70 01          	cmpl   $0x1,0x70(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  401a64:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  401a67:	7e 77                	jle    401ae0 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  401a69:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  401a6d:	55                   	push   %rbp
  401a6e:	49 89 f2             	mov    %rsi,%r10
  401a71:	49 89 d3             	mov    %rdx,%r11
  401a74:	53                   	push   %rbx
  401a75:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  401a78:	48 8b 98 a0 03 00 00 	mov    0x3a0(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  401a7f:	b8 01 00 00 00       	mov    $0x1,%eax
  401a84:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  401a88:	48 63 d0             	movslq %eax,%rdx
  401a8b:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  401a8e:	85 d2                	test   %edx,%edx
  401a90:	40 0f 94 c6          	sete   %sil
  401a94:	f6 c2 04             	test   $0x4,%dl
  401a97:	75 05                	jne    401a9e <pollthreads+0x3e>
  401a99:	40 84 f6             	test   %sil,%sil
  401a9c:	74 0d                	je     401aab <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  401a9e:	49 63 08             	movslq (%r8),%rcx
  401aa1:	8d 69 01             	lea    0x1(%rcx),%ebp
  401aa4:	41 89 28             	mov    %ebp,(%r8)
  401aa7:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  401aab:	83 e2 08             	and    $0x8,%edx
  401aae:	75 05                	jne    401ab5 <pollthreads+0x55>
  401ab0:	40 84 f6             	test   %sil,%sil
  401ab3:	74 1b                	je     401ad0 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  401ab5:	48 63 17             	movslq (%rdi),%rdx
  401ab8:	8d 4a 01             	lea    0x1(%rdx),%ecx
  401abb:	89 0f                	mov    %ecx,(%rdi)
  401abd:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  401ac1:	83 c0 01             	add    $0x1,%eax
  401ac4:	41 39 41 70          	cmp    %eax,0x70(%r9)
  401ac8:	7f be                	jg     401a88 <pollthreads+0x28>
}
  401aca:	31 c0                	xor    %eax,%eax
  401acc:	5b                   	pop    %rbx
  401acd:	5d                   	pop    %rbp
  401ace:	c3                   	ret
  401acf:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  401ad0:	83 c0 01             	add    $0x1,%eax
  401ad3:	41 39 41 70          	cmp    %eax,0x70(%r9)
  401ad7:	7f af                	jg     401a88 <pollthreads+0x28>
}
  401ad9:	31 c0                	xor    %eax,%eax
  401adb:	5b                   	pop    %rbx
  401adc:	5d                   	pop    %rbp
  401add:	c3                   	ret
  401ade:	66 90                	xchg   %ax,%ax
  401ae0:	31 c0                	xor    %eax,%eax
  401ae2:	c3                   	ret
  401ae3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401aee:	66 90                	xchg   %ax,%ax

0000000000401af0 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401af0:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401af3:	48 8b bf c0 00 00 00 	mov    0xc0(%rdi),%rdi
      if (*availableidx == 0) {
  401afa:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401afd:	48 83 c7 01          	add    $0x1,%rdi
  401b01:	48 85 ff             	test   %rdi,%rdi
  401b04:	7e 66                	jle    401b6c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401b06:	4d 8b 93 a8 00 00 00 	mov    0xa8(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401b0d:	31 c9                	xor    %ecx,%ecx
  401b0f:	45 31 c9             	xor    %r9d,%r9d
  401b12:	31 c0                	xor    %eax,%eax
  401b14:	eb 18                	jmp    401b2e <findavailable+0x3e>
  401b16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401b20:	83 c1 01             	add    $0x1,%ecx
  401b23:	48 63 c1             	movslq %ecx,%rax
  401b26:	49 89 c1             	mov    %rax,%r9
  401b29:	48 39 f8             	cmp    %rdi,%rax
  401b2c:	7d 3e                	jge    401b6c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401b2e:	48 c1 e0 05          	shl    $0x5,%rax
  401b32:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401b38:	75 e6                	jne    401b20 <findavailable+0x30>
         available[*availableidx] = x;
  401b3a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  401b3d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401b41:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401b45:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401b48:	41 8b 43 70          	mov    0x70(%r11),%eax
  401b4c:	01 c0                	add    %eax,%eax
  401b4e:	41 39 c0             	cmp    %eax,%r8d
  401b51:	74 19                	je     401b6c <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401b53:	49 8b bb c0 00 00 00 	mov    0xc0(%r11),%rdi
  401b5a:	83 c1 01             	add    $0x1,%ecx
  401b5d:	48 63 c1             	movslq %ecx,%rax
  401b60:	48 83 c7 01          	add    $0x1,%rdi
  401b64:	49 89 c1             	mov    %rax,%r9
  401b67:	48 39 f8             	cmp    %rdi,%rax
  401b6a:	7c c2                	jl     401b2e <findavailable+0x3e>
      if (*availableidx == 0) {
  401b6c:	31 c0                	xor    %eax,%eax
  401b6e:	45 85 c0             	test   %r8d,%r8d
  401b71:	0f 94 c0             	sete   %al
}
  401b74:	c3                   	ret
  401b75:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401b80 <singlewriter2>:
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b80:	41 54                	push   %r12
  401b82:	55                   	push   %rbp
  401b83:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401b84:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b8a:	48 89 fb             	mov    %rdi,%rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401b8d:	85 c0                	test   %eax,%eax
  401b8f:	74 0d                	je     401b9e <singlewriter2+0x1e>
  401b91:	8b 77 70             	mov    0x70(%rdi),%esi
  401b94:	99                   	cltd
  401b95:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401b98:	f7 f9                	idiv   %ecx
  401b9a:	85 d2                	test   %edx,%edx
  401b9c:	74 32                	je     401bd0 <singlewriter2+0x50>
  if (data->writecursor != 0 && (data->writecursor % (data->threadsize - 1)) == 0) {
  401b9e:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
  401ba4:	85 c0                	test   %eax,%eax
  401ba6:	74 1f                	je     401bc7 <singlewriter2+0x47>
  401ba8:	8b 73 70             	mov    0x70(%rbx),%esi
  401bab:	99                   	cltd
  401bac:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401baf:	f7 f9                	idiv   %ecx
  401bb1:	85 d2                	test   %edx,%edx
  401bb3:	75 12                	jne    401bc7 <singlewriter2+0x47>
    data->currentwrite++;
  401bb5:	48 83 83 00 03 00 00 01 	addq   $0x1,0x300(%rbx)
    data->writecursor = 0;
  401bbd:	c7 83 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rbx)
}
  401bc7:	5b                   	pop    %rbx
  401bc8:	5d                   	pop    %rbp
  401bc9:	41 5c                	pop    %r12
  401bcb:	c3                   	ret
  401bcc:	0f 1f 40 00          	nopl   0x0(%rax)
        struct Data * thread = &data->threads[data->threadindex];
  401bd0:	48 63 47 6c          	movslq 0x6c(%rdi),%rax
    data->currentread++;
  401bd4:	48 83 87 80 02 00 00 01 	addq   $0x1,0x280(%rdi)
    data->readcursor = 0;
  401bdc:	c7 87 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdi)
        struct Data * thread = &data->threads[data->threadindex];
  401be6:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  401bee:	48 29 c5             	sub    %rax,%rbp
  401bf1:	48 c1 e5 07          	shl    $0x7,%rbp
  401bf5:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401bf9:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401bfe:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401c05:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401c09:	49 c1 e4 04          	shl    $0x4,%r12
  401c0d:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401c14:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401c19:	e8 42 f4 ff ff       	call   401060 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401c1e:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401c24:	83 c0 01             	add    $0x1,%eax
  401c27:	99                   	cltd
  401c28:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  401c2e:	8b 43 6c             	mov    0x6c(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401c31:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401c37:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401c3b:	48 8b 05 7e 15 00 00 	mov    0x157e(%rip),%rax        # 4031c0 <_IO_stdin_used+0x1c0>
  401c42:	49 89 44 24 20       	mov    %rax,0x20(%r12)
  401c47:	e9 52 ff ff ff       	jmp    401b9e <singlewriter2+0x1e>
  401c4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401c50 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401c50:	41 55                	push   %r13
  401c52:	49 89 d5             	mov    %rdx,%r13
  401c55:	41 54                	push   %r12
  401c57:	49 89 cc             	mov    %rcx,%r12
  401c5a:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401c5b:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401c5e:	48 89 fd             	mov    %rdi,%rbp
  401c61:	53                   	push   %rbx
  401c62:	48 89 f3             	mov    %rsi,%rbx
  401c65:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401c69:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401c6d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401c76:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401c7b:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401c7d:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401c85:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  401c8b:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401c93:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401c9b:	83 c0 01             	add    $0x1,%eax
  401c9e:	99                   	cltd
  401c9f:	f7 7f 70             	idivl  0x70(%rdi)
  401ca2:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401ca8:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401cad:	4c 89 e9             	mov    %r13,%rcx
  401cb0:	e8 3b fe ff ff       	call   401af0 <findavailable>
  if (fill == 1) {
  401cb5:	83 f8 01             	cmp    $0x1,%eax
  401cb8:	0f 84 64 01 00 00    	je     401e22 <singlewriter+0x1d2>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401cbe:	48 89 ef             	mov    %rbp,%rdi
  401cc1:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401cc6:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401ccb:	4c 89 e2             	mov    %r12,%rdx
  401cce:	4c 89 ee             	mov    %r13,%rsi
  401cd1:	e8 8a fd ff ff       	call   401a60 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401cd6:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401cdb:	85 ff                	test   %edi,%edi
  401cdd:	0f 8e 66 01 00 00    	jle    401e49 <singlewriter+0x1f9>
  401ce3:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401ce8:	31 c9                	xor    %ecx,%ecx
  401cea:	eb 62                	jmp    401d4e <singlewriter+0xfe>
  401cec:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401cf0:	48 8b 14 cb          	mov    (%rbx,%rcx,8),%rdx
          int thread = readyreaders[x];
  401cf4:	4d 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%r10
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401cf9:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401cfc:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401d00:	48 c1 e2 05          	shl    $0x5,%rdx
  401d04:	48 03 95 a8 00 00 00 	add    0xa8(%rbp),%rdx
          data->threads[thread].reading = chunk;
  401d0b:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
          data->threads[thread].start = start;
  401d13:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401d17:	66 0f 6e 4a 08       	movd   0x8(%rdx),%xmm1
          data->threads[thread].reading = chunk;
  401d1c:	4c 29 d0             	sub    %r10,%rax
          chunk->available = READING;
  401d1f:	c7 42 10 02 00 00 00 	movl   $0x2,0x10(%rdx)
          data->threads[thread].reading = chunk;
  401d26:	48 c1 e0 07          	shl    $0x7,%rax
  401d2a:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].start = start;
  401d2e:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401d32:	48 89 90 b0 00 00 00 	mov    %rdx,0xb0(%rax)
          chunk->owner = thread;
  401d39:	44 89 52 14          	mov    %r10d,0x14(%rdx)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401d3d:	83 88 d0 00 00 00 10 	orl    $0x10,0xd0(%rax)
          data->threads[thread].start = start;
  401d44:	66 0f d6 40 14       	movq   %xmm0,0x14(%rax)
        for (int x = 0; x < readers ; x++) {
  401d49:	48 39 cf             	cmp    %rcx,%rdi
  401d4c:	74 07                	je     401d55 <singlewriter+0x105>
  401d4e:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401d50:	4c 39 c1             	cmp    %r8,%rcx
  401d53:	75 9b                	jne    401cf0 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401d55:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401d5a:	45 85 c0             	test   %r8d,%r8d
  401d5d:	7e 7a                	jle    401dd9 <singlewriter+0x189>
                if (assignedchunk  == availableidx) {
  401d5f:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401d63:	41 01 f0             	add    %esi,%r8d
  401d66:	eb 6d                	jmp    401dd5 <singlewriter+0x185>
  401d68:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401d70:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401d73:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401d76:	45 8b 0c 24          	mov    (%r12),%r9d
   for (int x = 0; x < writers ; x++) {
  401d7a:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401d7e:	48 8b 14 f3          	mov    (%rbx,%rsi,8),%rdx
          data->threads[thread].writing = chunk;
  401d82:	49 63 f1             	movslq %r9d,%rsi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401d85:	48 c1 e2 05          	shl    $0x5,%rdx
  401d89:	48 03 95 a8 00 00 00 	add    0xa8(%rbp),%rdx
          data->threads[thread].writing = chunk;
  401d90:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
          data->threads[thread].publishstart = start;
  401d98:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401d9c:	66 0f 6e 52 08       	movd   0x8(%rdx),%xmm2
          data->threads[thread].writing = chunk;
  401da1:	48 29 f0             	sub    %rsi,%rax
      chunk->available = WRITING;
  401da4:	c7 42 10 03 00 00 00 	movl   $0x3,0x10(%rdx)
          data->threads[thread].writing = chunk;
  401dab:	48 c1 e0 07          	shl    $0x7,%rax
  401daf:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].publishstart = start;
  401db3:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401db7:	48 89 90 b8 00 00 00 	mov    %rdx,0xb8(%rax)
          chunk->owner = thread;
  401dbe:	44 89 4a 14          	mov    %r9d,0x14(%rdx)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401dc2:	83 88 d0 00 00 00 20 	orl    $0x20,0xd0(%rax)
          data->threads[thread].publishstart = start;
  401dc9:	66 0f d6 40 40       	movq   %xmm0,0x40(%rax)
   for (int x = 0; x < writers ; x++) {
  401dce:	44 39 c1             	cmp    %r8d,%ecx
  401dd1:	74 06                	je     401dd9 <singlewriter+0x189>
  401dd3:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401dd5:	39 f7                	cmp    %esi,%edi
  401dd7:	75 97                	jne    401d70 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401dd9:	8b 7d 70             	mov    0x70(%rbp),%edi
  401ddc:	85 ff                	test   %edi,%edi
  401dde:	7e 40                	jle    401e20 <singlewriter+0x1d0>
        if (data->threads[x].newmask != 0) {
  401de0:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401de4:	31 d2                	xor    %edx,%edx
  401de6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401df0:	48 63 ca             	movslq %edx,%rcx
  401df3:	48 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rax
  401dfb:	48 29 c8             	sub    %rcx,%rax
  401dfe:	48 c1 e0 07          	shl    $0x7,%rax
  401e02:	4c 01 c0             	add    %r8,%rax
  401e05:	8b b0 d0 00 00 00    	mov    0xd0(%rax),%esi
  401e0b:	85 f6                	test   %esi,%esi
  401e0d:	74 31                	je     401e40 <singlewriter+0x1f0>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401e0f:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401e13:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401e16:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401e19:	8b 7d 70             	mov    0x70(%rbp),%edi
  401e1c:	39 fa                	cmp    %edi,%edx
  401e1e:	7c d0                	jl     401df0 <singlewriter+0x1a0>
  return 0;
  401e20:	31 c0                	xor    %eax,%eax
}
  401e22:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401e27:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401e30:	75 1e                	jne    401e50 <singlewriter+0x200>
  401e32:	48 83 c4 28          	add    $0x28,%rsp
  401e36:	5b                   	pop    %rbx
  401e37:	5d                   	pop    %rbp
  401e38:	41 5c                	pop    %r12
  401e3a:	41 5d                	pop    %r13
  401e3c:	c3                   	ret
  401e3d:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401e40:	83 c2 01             	add    $0x1,%edx
  401e43:	39 fa                	cmp    %edi,%edx
  401e45:	7c a9                	jl     401df0 <singlewriter+0x1a0>
  401e47:	eb d7                	jmp    401e20 <singlewriter+0x1d0>
      int assignedchunk = 0;
  401e49:	31 f6                	xor    %esi,%esi
  401e4b:	e9 05 ff ff ff       	jmp    401d55 <singlewriter+0x105>
}
  401e50:	e8 1b f2 ff ff       	call   401070 <__stack_chk_fail@plt>
  401e55:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401e60 <threadwork>:
int * threadwork(struct Data * data) {
  401e60:	41 57                	push   %r15
  401e62:	41 56                	push   %r14
  401e64:	41 55                	push   %r13
  401e66:	41 54                	push   %r12
  401e68:	55                   	push   %rbp
  401e69:	53                   	push   %rbx
  401e6a:	48 89 fb             	mov    %rdi,%rbx
  401e6d:	48 83 ec 28          	sub    $0x28,%rsp
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401e71:	48 63 4f 70          	movslq 0x70(%rdi),%rcx
  401e75:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401e7e:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401e83:	48 8b 47 28          	mov    0x28(%rdi),%rax
  long lastcursor = data->main->writecursor;
  401e87:	8b b0 80 01 00 00    	mov    0x180(%rax),%esi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401e8d:	48 8b 80 38 03 00 00 	mov    0x338(%rax),%rax
  401e94:	48 99                	cqto
    data->thiswrite = lastcursor;
  401e96:	89 b7 28 03 00 00    	mov    %esi,0x328(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401e9c:	48 89 e6             	mov    %rsp,%rsi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401e9f:	48 f7 f9             	idiv   %rcx
    data->prevwrite = lastwrite;
  401ea2:	48 89 97 10 03 00 00 	mov    %rdx,0x310(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401ea9:	bf 04 00 00 00       	mov    $0x4,%edi
  401eae:	e8 ad f1 ff ff       	call   401060 <clock_gettime@plt>
     for (int x = 1; x < data->threadsize ; x++) {
  401eb3:	8b 43 70             	mov    0x70(%rbx),%eax
   data->freq_writes++;
  401eb6:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
     for (int x = 1; x < data->threadsize ; x++) {
  401ebb:	b9 01 00 00 00       	mov    $0x1,%ecx
  401ec0:	83 f8 01             	cmp    $0x1,%eax
  401ec3:	0f 8f 2a 01 00 00    	jg     401ff3 <threadwork+0x193>
  401ec9:	e9 37 01 00 00       	jmp    402005 <threadwork+0x1a5>
  401ece:	66 90                	xchg   %ax,%ax
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401ed0:	48 63 83 80 01 00 00 	movslq 0x180(%rbx),%rax
  401ed7:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
        epoch->time = time;
  401edb:	66 0f 6f 04 24       	movdqa (%rsp),%xmm0
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401ee0:	48 89 c2             	mov    %rax,%rdx
  401ee3:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401eea:	41 89 d0             	mov    %edx,%r8d
  401eed:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401ef1:	48 c1 e8 20          	shr    $0x20,%rax
  401ef5:	01 d0                	add    %edx,%eax
  401ef7:	c1 f8 03             	sar    $0x3,%eax
  401efa:	44 29 c0             	sub    %r8d,%eax
  401efd:	41 89 c0             	mov    %eax,%r8d
  401f00:	41 c1 e0 04          	shl    $0x4,%r8d
  401f04:	41 29 c0             	sub    %eax,%r8d
  401f07:	89 f0                	mov    %esi,%eax
  401f09:	44 29 c2             	sub    %r8d,%edx
  401f0c:	c1 e0 18             	shl    $0x18,%eax
  401f0f:	09 c2                	or     %eax,%edx
  401f11:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  401f18:	41 89 d2             	mov    %edx,%r10d
  401f1b:	48 89 c2             	mov    %rax,%rdx
  401f1e:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401f25:	41 89 d0             	mov    %edx,%r8d
  401f28:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401f2c:	48 c1 e8 20          	shr    $0x20,%rax
  401f30:	01 d0                	add    %edx,%eax
  401f32:	c1 f8 03             	sar    $0x3,%eax
  401f35:	44 29 c0             	sub    %r8d,%eax
  401f38:	41 89 c0             	mov    %eax,%r8d
  401f3b:	41 c1 e0 04          	shl    $0x4,%r8d
  401f3f:	41 29 c0             	sub    %eax,%r8d
  401f42:	89 c8                	mov    %ecx,%eax
  401f44:	44 29 c2             	sub    %r8d,%edx
  401f47:	c1 e0 08             	shl    $0x8,%eax
  401f4a:	c1 e2 10             	shl    $0x10,%edx
  401f4d:	41 09 d2             	or     %edx,%r10d
  401f50:	41 09 c2             	or     %eax,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  401f53:	48 63 c6             	movslq %esi,%rax
  401f56:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401f5e:	4d 63 d2             	movslq %r10d,%r10
        struct Data * thread = &data->threads[data->threadindex];
  401f61:	49 29 c0             	sub    %rax,%r8
  401f64:	49 c1 e0 07          	shl    $0x7,%r8
  401f68:	4c 03 43 30          	add    0x30(%rbx),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401f6c:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  401f73:	48 89 d0             	mov    %rdx,%rax
  401f76:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401f7a:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401f7d:	49 c1 e1 04          	shl    $0x4,%r9
  401f81:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401f88:	99                   	cltd
        epoch->time = time;
  401f89:	41 0f 11 41 08       	movups %xmm0,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401f8e:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
        data->main->works[buffer] = data->threadindex;
  401f95:	48 8b 47 78          	mov    0x78(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401f99:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
        epoch->thread = data->threadindex;
  401fa0:	41 89 31             	mov    %esi,(%r9)
  epoch->dest = x;
  401fa3:	41 89 49 28          	mov    %ecx,0x28(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401fa7:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  401fab:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
        data->main->works[buffer] = data->threadindex;
  401fb3:	42 88 34 10          	mov    %sil,(%rax,%r10,1)
         data->writecursor = (data->writecursor + 1) % 0xf;
  401fb7:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
  401fbd:	8d 50 01             	lea    0x1(%rax),%edx
  401fc0:	48 63 c2             	movslq %edx,%rax
  401fc3:	89 d6                	mov    %edx,%esi
  401fc5:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401fcc:	c1 fe 1f             	sar    $0x1f,%esi
     for (int x = 1; x < data->threadsize ; x++) {
  401fcf:	83 c1 01             	add    $0x1,%ecx
         data->writecursor = (data->writecursor + 1) % 0xf;
  401fd2:	48 c1 e8 20          	shr    $0x20,%rax
  401fd6:	01 d0                	add    %edx,%eax
  401fd8:	c1 f8 03             	sar    $0x3,%eax
  401fdb:	29 f0                	sub    %esi,%eax
  401fdd:	89 c6                	mov    %eax,%esi
  401fdf:	c1 e6 04             	shl    $0x4,%esi
  401fe2:	29 c6                	sub    %eax,%esi
     for (int x = 1; x < data->threadsize ; x++) {
  401fe4:	8b 43 70             	mov    0x70(%rbx),%eax
         data->writecursor = (data->writecursor + 1) % 0xf;
  401fe7:	29 f2                	sub    %esi,%edx
  401fe9:	89 93 80 01 00 00    	mov    %edx,0x180(%rbx)
     for (int x = 1; x < data->threadsize ; x++) {
  401fef:	39 c1                	cmp    %eax,%ecx
  401ff1:	7d 12                	jge    402005 <threadwork+0x1a5>
  401ff3:	8b 73 6c             	mov    0x6c(%rbx),%esi
     if (x != data->threadindex) {
  401ff6:	39 ce                	cmp    %ecx,%esi
  401ff8:	0f 85 d2 fe ff ff    	jne    401ed0 <threadwork+0x70>
     for (int x = 1; x < data->threadsize ; x++) {
  401ffe:	8d 4e 01             	lea    0x1(%rsi),%ecx
  402001:	39 c1                	cmp    %eax,%ecx
  402003:	7c f1                	jl     401ff6 <threadwork+0x196>
    __atomic_fetch_add(&data->main->writecursor, 1, __ATOMIC_ACQUIRE);
  402005:	48 8b 43 28          	mov    0x28(%rbx),%rax
  402009:	f0 83 80 80 01 00 00 01 	lock addl $0x1,0x180(%rax)
  long lastread = data->main->totalreads % data->threadsize;
  402011:	4c 8b 5b 28          	mov    0x28(%rbx),%r11
  402015:	48 63 4b 70          	movslq 0x70(%rbx),%rcx
  402019:	49 8b 83 40 03 00 00 	mov    0x340(%r11),%rax
  402020:	49 89 c8             	mov    %rcx,%r8
   data->freq++;
  402023:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
  long lastread = data->main->totalreads % data->threadsize;
  402028:	48 99                	cqto
  40202a:	48 f7 f9             	idiv   %rcx
   data->prevread = lastread;
  40202d:	48 89 93 08 03 00 00 	mov    %rdx,0x308(%rbx)
  for (int y = 1 ; y < data->threadsize; y++) {
  402034:	83 f9 01             	cmp    $0x1,%ecx
  402037:	0f 8e 53 01 00 00    	jle    402190 <threadwork+0x330>
          if (y != data->threadindex) {
  40203d:	48 63 43 6c          	movslq 0x6c(%rbx),%rax
                struct Data * thread = &data->threads[data->threadindex];
  402041:	bf 80 03 00 00       	mov    $0x380,%edi
  for (int y = 1 ; y < data->threadsize; y++) {
  402046:	be 01 00 00 00       	mov    $0x1,%esi
              past = data->threadsize - 1;
  40204b:	8d 69 ff             	lea    -0x1(%rcx),%ebp
                struct Data * thread = &data->threads[data->threadindex];
  40204e:	4c 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%r10
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402056:	41 89 c4             	mov    %eax,%r12d
          if (y != data->threadindex) {
  402059:	49 89 c1             	mov    %rax,%r9
                struct Data * thread = &data->threads[data->threadindex];
  40205c:	49 29 c2             	sub    %rax,%r10
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40205f:	41 c1 e4 08          	shl    $0x8,%r12d
                struct Data * thread = &data->threads[data->threadindex];
  402063:	49 c1 e2 07          	shl    $0x7,%r10
  402067:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          if (y != data->threadindex) {
  402070:	44 39 ce             	cmp    %r9d,%esi
  402073:	0f 84 04 01 00 00    	je     40217d <threadwork+0x31d>
            long past = ((data->main->writecursor - 1) % 0xf);
  402079:	41 8b 83 80 01 00 00 	mov    0x180(%r11),%eax
            int rc = data->threads[x].writecursor;
  402080:	4c 8b 7b 30          	mov    0x30(%rbx),%r15
  402084:	41 be 0e 00 00 00    	mov    $0xe,%r14d
            long past = ((data->main->writecursor - 1) % 0xf);
  40208a:	8d 50 ff             	lea    -0x1(%rax),%edx
  40208d:	48 63 c2             	movslq %edx,%rax
  402090:	89 d1                	mov    %edx,%ecx
  402092:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402099:	c1 f9 1f             	sar    $0x1f,%ecx
  40209c:	48 c1 e8 20          	shr    $0x20,%rax
  4020a0:	01 d0                	add    %edx,%eax
  4020a2:	c1 f8 03             	sar    $0x3,%eax
  4020a5:	29 c8                	sub    %ecx,%eax
  4020a7:	89 c1                	mov    %eax,%ecx
  4020a9:	c1 e1 04             	shl    $0x4,%ecx
  4020ac:	29 c1                	sub    %eax,%ecx
              past = data->threadsize - 1;
  4020ae:	89 d0                	mov    %edx,%eax
            int rc = data->threads[x].writecursor;
  4020b0:	41 8b 94 3f 80 01 00 00 	mov    0x180(%r15,%rdi,1),%edx
              past = data->threadsize - 1;
  4020b8:	29 c8                	sub    %ecx,%eax
  4020ba:	0f 48 c5             	cmovs  %ebp,%eax
  4020bd:	48 63 c8             	movslq %eax,%rcx
            if (rc < 0) {
  4020c0:	85 d2                	test   %edx,%edx
  4020c2:	78 2d                	js     4020f1 <threadwork+0x291>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4020c4:	48 63 c2             	movslq %edx,%rax
  4020c7:	41 89 d5             	mov    %edx,%r13d
  4020ca:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  4020d1:	41 c1 fd 1f          	sar    $0x1f,%r13d
  4020d5:	48 c1 e8 20          	shr    $0x20,%rax
  4020d9:	01 d0                	add    %edx,%eax
  4020db:	c1 f8 03             	sar    $0x3,%eax
  4020de:	44 29 e8             	sub    %r13d,%eax
  4020e1:	41 89 c5             	mov    %eax,%r13d
  4020e4:	41 c1 e5 04          	shl    $0x4,%r13d
  4020e8:	41 29 c5             	sub    %eax,%r13d
  4020eb:	44 29 ea             	sub    %r13d,%edx
  4020ee:	4c 63 f2             	movslq %edx,%r14
                struct Data * thread = &data->threads[data->threadindex];
  4020f1:	4d 01 d7             	add    %r10,%r15
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4020f4:	48 c1 e1 10          	shl    $0x10,%rcx
            thepoch->time = time; 
  4020f8:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  4020fd:	49 63 97 24 03 00 00 	movslq 0x324(%r15),%rdx
  402104:	48 89 d0             	mov    %rdx,%rax
  402107:	4c 8d 2c 52          	lea    (%rdx,%rdx,2),%r13
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40210b:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  40210e:	49 c1 e5 04          	shl    $0x4,%r13
  402112:	4d 03 af 18 03 00 00 	add    0x318(%r15),%r13
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402119:	99                   	cltd
            thepoch->time = time; 
  40211a:	41 0f 11 4d 08       	movups %xmm1,0x8(%r13)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40211f:	41 f7 bf 20 03 00 00 	idivl  0x320(%r15)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402126:	89 f0                	mov    %esi,%eax
  402128:	c1 e0 18             	shl    $0x18,%eax
  40212b:	44 09 e0             	or     %r12d,%eax
  40212e:	48 98                	cltq
  402130:	48 09 c8             	or     %rcx,%rax
  402133:	4c 09 f0             	or     %r14,%rax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402136:	41 89 97 24 03 00 00 	mov    %edx,0x324(%r15)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40213d:	49 89 45 18          	mov    %rax,0x18(%r13)
          data->readcursor = (data->readcursor) % 0xf;
  402141:	48 63 83 00 02 00 00 	movslq 0x200(%rbx),%rax
                thepoch->thread = x;
  402148:	41 89 75 00          	mov    %esi,0x0(%r13)
          data->readcursor = (data->readcursor) % 0xf;
  40214c:	48 89 c2             	mov    %rax,%rdx
  40214f:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
          thepoch->set = 1;
  402156:	41 c7 45 24 01 00 00 00 	movl   $0x1,0x24(%r13)
          data->readcursor = (data->readcursor) % 0xf;
  40215e:	89 d1                	mov    %edx,%ecx
  402160:	c1 f9 1f             	sar    $0x1f,%ecx
  402163:	48 c1 e8 20          	shr    $0x20,%rax
  402167:	01 d0                	add    %edx,%eax
  402169:	c1 f8 03             	sar    $0x3,%eax
  40216c:	29 c8                	sub    %ecx,%eax
  40216e:	89 c1                	mov    %eax,%ecx
  402170:	c1 e1 04             	shl    $0x4,%ecx
  402173:	29 c1                	sub    %eax,%ecx
  402175:	29 ca                	sub    %ecx,%edx
  402177:	89 93 00 02 00 00    	mov    %edx,0x200(%rbx)
  for (int y = 1 ; y < data->threadsize; y++) {
  40217d:	83 c6 01             	add    $0x1,%esi
  402180:	48 81 c7 80 03 00 00 	add    $0x380,%rdi
  402187:	41 39 f0             	cmp    %esi,%r8d
  40218a:	0f 85 e0 fe ff ff    	jne    402070 <threadwork+0x210>
    __atomic_fetch_add(&data->main->readcursor, 1, __ATOMIC_ACQUIRE);
  402190:	f0 41 83 83 00 02 00 00 01 	lock addl $0x1,0x200(%r11)
}
  402199:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  40219e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4021a7:	75 11                	jne    4021ba <threadwork+0x35a>
  4021a9:	48 83 c4 28          	add    $0x28,%rsp
  4021ad:	31 c0                	xor    %eax,%eax
  4021af:	5b                   	pop    %rbx
  4021b0:	5d                   	pop    %rbp
  4021b1:	41 5c                	pop    %r12
  4021b3:	41 5d                	pop    %r13
  4021b5:	41 5e                	pop    %r14
  4021b7:	41 5f                	pop    %r15
  4021b9:	c3                   	ret
  4021ba:	e8 b1 ee ff ff       	call   401070 <__stack_chk_fail@plt>
  4021bf:	90                   	nop

00000000004021c0 <work>:
void * work(void * arg) {
  4021c0:	41 56                	push   %r14
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4021c2:	48 8d 35 3b 0e 00 00 	lea    0xe3b(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  4021c9:	31 c0                	xor    %eax,%eax
  4021cb:	41 55                	push   %r13
  4021cd:	41 54                	push   %r12
  4021cf:	55                   	push   %rbp
  4021d0:	53                   	push   %rbx
  4021d1:	8b 57 6c             	mov    0x6c(%rdi),%edx
  4021d4:	48 89 fb             	mov    %rdi,%rbx
  4021d7:	bf 01 00 00 00       	mov    $0x1,%edi
  4021dc:	e8 cf ee ff ff       	call   4010b0 <__printf_chk@plt>
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  4021e1:	8b 43 6c             	mov    0x6c(%rbx),%eax
  4021e4:	48 8d 35 2c 0e 00 00 	lea    0xe2c(%rip),%rsi        # 403017 <_IO_stdin_used+0x17>
  4021eb:	bf 01 00 00 00       	mov    $0x1,%edi
  int bucketstart = data->bucketstart;
  4021f0:	44 8b b3 a0 00 00 00 	mov    0xa0(%rbx),%r14d
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  4021f7:	8d 50 01             	lea    0x1(%rax),%edx
  4021fa:	31 c0                	xor    %eax,%eax
  int bucketlim = ((data->threadindex + 1) * data->buckets) ;
  4021fc:	0f af 93 98 00 00 00 	imul   0x98(%rbx),%edx
  402203:	e8 a8 ee ff ff       	call   4010b0 <__printf_chk@plt>
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  402208:	48 8b 83 c0 00 00 00 	mov    0xc0(%rbx),%rax
  40220f:	be 08 00 00 00       	mov    $0x8,%esi
  402214:	48 8d 78 01          	lea    0x1(%rax),%rdi
  402218:	e8 83 ee ff ff       	call   4010a0 <calloc@plt>
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  40221d:	4c 63 6b 70          	movslq 0x70(%rbx),%r13
  402221:	be 04 00 00 00       	mov    $0x4,%esi
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  402226:	48 89 c5             	mov    %rax,%rbp
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  402229:	4c 89 ef             	mov    %r13,%rdi
  40222c:	e8 6f ee ff ff       	call   4010a0 <calloc@plt>
  int * readywriters = calloc(data->threadsize, sizeof(int));
  402231:	be 04 00 00 00       	mov    $0x4,%esi
  402236:	4c 89 ef             	mov    %r13,%rdi
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  402239:	49 89 c4             	mov    %rax,%r12
  int * readywriters = calloc(data->threadsize, sizeof(int));
  40223c:	e8 5f ee ff ff       	call   4010a0 <calloc@plt>
  while (data->running == 1) {
  402241:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  data->workindex = bucketstart;
  402245:	44 89 73 5c          	mov    %r14d,0x5c(%rbx)
  while (data->running == 1) {
  402249:	75 49                	jne    402294 <work+0xd4>
  40224b:	49 89 c5             	mov    %rax,%r13
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  40224e:	4c 8d b3 30 01 00 00 	lea    0x130(%rbx),%r14
  402255:	0f 1f 00             	nopl   (%rax)
    if (data->threadindex == 0) {
  402258:	8b 43 6c             	mov    0x6c(%rbx),%eax
  40225b:	85 c0                	test   %eax,%eax
  40225d:	75 59                	jne    4022b8 <work+0xf8>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  40225f:	4c 89 f6             	mov    %r14,%rsi
  402262:	bf 04 00 00 00       	mov    $0x4,%edi
  402267:	e8 f4 ed ff ff       	call   401060 <clock_gettime@plt>
      singlewriter2(data, available, readyreaders, readywriters);
  40226c:	4c 89 e9             	mov    %r13,%rcx
  40226f:	4c 89 e2             	mov    %r12,%rdx
  402272:	48 89 ee             	mov    %rbp,%rsi
  402275:	48 89 df             	mov    %rbx,%rdi
  402278:	e8 03 f9 ff ff       	call   401b80 <singlewriter2>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swend);
  40227d:	48 8d b3 40 01 00 00 	lea    0x140(%rbx),%rsi
  402284:	bf 04 00 00 00       	mov    $0x4,%edi
  402289:	e8 d2 ed ff ff       	call   401060 <clock_gettime@plt>
  while (data->running == 1) {
  40228e:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  402292:	74 c4                	je     402258 <work+0x98>
  402294:	8b 53 6c             	mov    0x6c(%rbx),%edx
  402297:	48 8d 35 87 0d 00 00 	lea    0xd87(%rip),%rsi        # 403025 <_IO_stdin_used+0x25>
  40229e:	bf 01 00 00 00       	mov    $0x1,%edi
  4022a3:	31 c0                	xor    %eax,%eax
  4022a5:	e8 06 ee ff ff       	call   4010b0 <__printf_chk@plt>
}
  4022aa:	5b                   	pop    %rbx
  4022ab:	5d                   	pop    %rbp
  4022ac:	41 5c                	pop    %r12
  4022ae:	41 5d                	pop    %r13
  4022b0:	41 5e                	pop    %r14
  4022b2:	c3                   	ret
  4022b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      threadwork(data);
  4022b8:	48 89 df             	mov    %rbx,%rdi
  4022bb:	e8 a0 fb ff ff       	call   401e60 <threadwork>
  while (data->running == 1) {
  4022c0:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  4022c4:	74 92                	je     402258 <work+0x98>
  4022c6:	eb cc                	jmp    402294 <work+0xd4>
  4022c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

00000000004022d0 <work2>:
  while (data->running == 1) {
  4022d0:	eb 0b                	jmp    4022dd <work2+0xd>
  4022d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  4022d8:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  4022dd:	83 7f 64 01          	cmpl   $0x1,0x64(%rdi)
  4022e1:	74 f5                	je     4022d8 <work2+0x8>
}
  4022e3:	c3                   	ret

Disassembly of section .fini:

00000000004022e4 <_fini>:
  4022e4:	f3 0f 1e fa          	endbr64
  4022e8:	48 83 ec 08          	sub    $0x8,%rsp
  4022ec:	48 83 c4 08          	add    $0x8,%rsp
  4022f0:	c3                   	ret
