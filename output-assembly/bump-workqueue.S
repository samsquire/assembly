
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
  401105:	41 be 11 00 00 00    	mov    $0x11,%r14d
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
  401160:	ba 10 00 00 00       	mov    $0x10,%edx
  401165:	48 8d 35 ea 1e 00 00 	lea    0x1eea(%rip),%rsi        # 403056 <_IO_stdin_used+0x56>
  40116c:	31 c0                	xor    %eax,%eax
  40116e:	bf 01 00 00 00       	mov    $0x1,%edi
  401173:	e8 38 ff ff ff       	call   4010b0 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401178:	be 08 00 00 00       	mov    $0x8,%esi
  40117d:	bf 10 00 00 00       	mov    $0x10,%edi
  401182:	e8 19 ff ff ff       	call   4010a0 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401187:	be 38 00 00 00       	mov    $0x38,%esi
  40118c:	bf 10 00 00 00       	mov    $0x10,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401191:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401196:	e8 05 ff ff ff       	call   4010a0 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40119b:	be 00 1a 00 00       	mov    $0x1a00,%esi
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
  4011e0:	bf 10 00 00 00       	mov    $0x10,%edi
  4011e5:	4c 8d bb 54 01 00 00 	lea    0x154(%rbx),%r15
  4011ec:	e8 af fe ff ff       	call   4010a0 <calloc@plt>
  int * writecursors = calloc(threadsize, sizeof(int));
  4011f1:	be 04 00 00 00       	mov    $0x4,%esi
  4011f6:	bf 10 00 00 00       	mov    $0x10,%edi
  int * readcursors = calloc(threadsize, sizeof(int));
  4011fb:	48 89 c5             	mov    %rax,%rbp
  int * writecursors = calloc(threadsize, sizeof(int));
  4011fe:	e8 9d fe ff ff       	call   4010a0 <calloc@plt>
  401203:	66 48 0f 6e ed       	movq   %rbp,%xmm5
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  401208:	be 20 00 00 00       	mov    $0x20,%esi
  40120d:	bf 64 00 00 00       	mov    $0x64,%edi
  401212:	66 48 0f 6e f8       	movq   %rax,%xmm7
  401217:	48 8d 2d 5e 1e 00 00 	lea    0x1e5e(%rip),%rbp        # 40307c <_IO_stdin_used+0x7c>
  40121e:	66 0f 6c ef          	punpcklqdq %xmm7,%xmm5
  401222:	0f 29 6c 24 10       	movaps %xmm5,0x10(%rsp)
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
  401248:	41 89 47 08          	mov    %eax,0x8(%r15)
  40124c:	bf 01 00 00 00       	mov    $0x1,%edi
  401251:	31 c0                	xor    %eax,%eax
          for (int x = 0; x < threadsize; x++) {
  401253:	49 81 c7 a0 01 00 00 	add    $0x1a0,%r15
     data[chunkindex].readcursors = readcursors;
  40125a:	41 0f 11 8f 7c fe ff ff 	movups %xmm1,-0x184(%r15)
  401262:	e8 49 fe ff ff       	call   4010b0 <__printf_chk@plt>
    printf("middle %ld\n", middle);
    data[chunkindex].middle = middle;
    data[chunkindex].readcursors[chunkindex] = middle;
  401267:	49 8b 87 7c fe ff ff 	mov    -0x184(%r15),%rax
    data[chunkindex].middle = middle;
  40126e:	45 89 b7 60 fe ff ff 	mov    %r14d,-0x1a0(%r15)
    data[chunkindex].readcursors[chunkindex] = middle;
  401275:	46 89 34 28          	mov    %r14d,(%rax,%r13,1)
    data[chunkindex].writecursors[chunkindex] = middle;
  401279:	49 8b 87 84 fe ff ff 	mov    -0x17c(%r15),%rax
  401280:	46 89 34 28          	mov    %r14d,(%rax,%r13,1)
    data[chunkindex].oreadcursor = start;
  401284:	41 8d 46 ef          	lea    -0x11(%r14),%eax
          for (int x = 0; x < threadsize; x++) {
  401288:	49 83 c6 21          	add    $0x21,%r14
  40128c:	49 83 c5 04          	add    $0x4,%r13
    data[chunkindex].oreadcursor = start;
  401290:	41 89 87 6c fe ff ff 	mov    %eax,-0x194(%r15)
          for (int x = 0; x < threadsize; x++) {
  401297:	49 81 fe 21 02 00 00 	cmp    $0x221,%r14
  40129e:	75 98                	jne    401238 <main+0x148>
  4012a0:	ba 10 02 00 00       	mov    $0x210,%edx
  4012a5:	bf 01 00 00 00       	mov    $0x1,%edi
  4012aa:	31 c0                	xor    %eax,%eax
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  data[0].works = works;
  4012ac:	49 89 de             	mov    %rbx,%r14
  4012af:	48 8d 35 d2 1d 00 00 	lea    0x1dd2(%rip),%rsi        # 403088 <_IO_stdin_used+0x88>
  int cpu = 0;
  4012b6:	45 31 ed             	xor    %r13d,%r13d
  4012b9:	e8 f2 fd ff ff       	call   4010b0 <__printf_chk@plt>
  4012be:	ba ff ff ff ff       	mov    $0xffffffff,%edx
  4012c3:	48 8d 35 c9 1d 00 00 	lea    0x1dc9(%rip),%rsi        # 403093 <_IO_stdin_used+0x93>
  4012ca:	31 c0                	xor    %eax,%eax
  4012cc:	bf 01 00 00 00       	mov    $0x1,%edi
  4012d1:	e8 da fd ff ff       	call   4010b0 <__printf_chk@plt>
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  4012d6:	be 04 00 00 00       	mov    $0x4,%esi
  4012db:	bf 10 00 00 00       	mov    $0x10,%edi
  4012e0:	e8 bb fd ff ff       	call   4010a0 <calloc@plt>
  4012e5:	66 48 0f 6e fb       	movq   %rbx,%xmm7
  data[0].works = works;
  4012ea:	4c 89 63 78          	mov    %r12,0x78(%rbx)
  4012ee:	45 31 e4             	xor    %r12d,%r12d
  4012f1:	66 48 0f 6e f0       	movq   %rax,%xmm6
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  4012f6:	48 89 c5             	mov    %rax,%rbp
  4012f9:	66 0f 6c f7          	punpcklqdq %xmm7,%xmm6
  4012fd:	0f 29 74 24 10       	movaps %xmm6,0x10(%rsp)
  for (int x = 0; x < threadsize ; x++) {
  401302:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
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
  401326:	48 8d 35 db 1d 00 00 	lea    0x1ddb(%rip),%rsi        # 403108 <_IO_stdin_used+0x108>
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
  40134b:	49 81 c6 a0 01 00 00 	add    $0x1a0,%r14
  401352:	e8 59 fd ff ff       	call   4010b0 <__printf_chk@plt>
    data[x].threadindex = x;
    data[x].worksize = worksize;
    
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].readies = readies;
  401357:	66 0f 6f 54 24 10    	movdqa 0x10(%rsp),%xmm2
    data[x].readies[x] = 0;
    data[x].buckets = buckets;
  40135d:	48 8b 05 cc 1d 00 00 	mov    0x1dcc(%rip),%rax        # 403130 <_IO_stdin_used+0x130>
    data[x].bucketstart = x * buckets ;
  401364:	45 89 a6 00 ff ff ff 	mov    %r12d,-0x100(%r14)
    data[x].main = &data[0];
    data[x].threads = data;
    data[x].wantindex = -1;
    data[x].read = 0;
  40136b:	66 0f 6f 1d dd 1d 00 00 	movdqa 0x1ddd(%rip),%xmm3        # 403150 <_IO_stdin_used+0x150>
    data[x].write = worksize;
    
    data[x].freelist = freelist;
    data[x].chunksize = chunksize;
    data[x].chunkslen = chunkslen;
  401373:	66 0f 6f 25 e5 1d 00 00 	movdqa 0x1de5(%rip),%xmm4        # 403160 <_IO_stdin_used+0x160>
    data[x].loglevel = debug;
  40137b:	41 c7 86 e8 fe ff ff 00 00 00 00 	movl   $0x0,-0x118(%r14)
    data[x].newmask = 0;
    data[x].prevread = -1;
    data[x].prevwrite = -1;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401386:	be 28 00 00 00       	mov    $0x28,%esi
    data[x].buckets = buckets;
  40138b:	49 89 86 f8 fe ff ff 	mov    %rax,-0x108(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401392:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].wantindex = -1;
  401397:	48 8b 05 9a 1d 00 00 	mov    0x1d9a(%rip),%rax        # 403138 <_IO_stdin_used+0x138>
  for (int x = 0; x < threadsize ; x++) {
  40139e:	41 81 c4 ff ff ff 0f 	add    $0xfffffff,%r12d
    data[x].threadindex = x;
  4013a5:	45 89 be cc fe ff ff 	mov    %r15d,-0x134(%r14)
    data[x].wantindex = -1;
  4013ac:	49 89 86 c0 fe ff ff 	mov    %rax,-0x140(%r14)
    data[x].freelist = freelist;
  4013b3:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    data[x].worksize = worksize;
  4013b8:	41 c7 86 c8 fe ff ff ff ff ff ff 	movl   $0xffffffff,-0x138(%r14)
    data[x].freelist = freelist;
  4013c3:	49 89 86 08 ff ff ff 	mov    %rax,-0xf8(%r14)
    data[x].prevread = -1;
  4013ca:	48 8b 05 6f 1d 00 00 	mov    0x1d6f(%rip),%rax        # 403140 <_IO_stdin_used+0x140>
    data[x].threadsize = threadsize;
  4013d1:	41 c7 86 d0 fe ff ff 10 00 00 00 	movl   $0x10,-0x130(%r14)
    data[x].readies[x] = 0;
  4013dc:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
    data[x].threads = data;
  4013e3:	49 89 9e 90 fe ff ff 	mov    %rbx,-0x170(%r14)
    data[x].newmask = 0;
  4013ea:	41 c7 86 30 ff ff ff 00 00 00 00 	movl   $0x0,-0xd0(%r14)
    data[x].prevread = -1;
  4013f5:	49 89 46 e8          	mov    %rax,-0x18(%r14)
    data[x].readies = readies;
  4013f9:	41 0f 11 96 80 fe ff ff 	movups %xmm2,-0x180(%r14)
    data[x].read = 0;
  401401:	41 0f 11 9e 60 fe ff ff 	movups %xmm3,-0x1a0(%r14)
    data[x].chunkslen = chunkslen;
  401409:	41 0f 11 a6 20 ff ff ff 	movups %xmm4,-0xe0(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401411:	e8 8a fc ff ff       	call   4010a0 <calloc@plt>
    data[x].epochssize = epochs;
  401416:	41 c7 46 f8 80 96 98 00 	movl   $0x989680,-0x8(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40141e:	49 89 46 f0          	mov    %rax,-0x10(%r14)
  for (int x = 0; x < threadsize ; x++) {
  401422:	41 83 fd 10          	cmp    $0x10,%r13d
  401426:	0f 85 dc fe ff ff    	jne    401308 <main+0x218>
  40142c:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
  401431:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
  401436:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  40143b:	49 89 de             	mov    %rbx,%r14
  40143e:	49 c7 c5 90 20 40 00 	mov    $0x402090,%r13
  401445:	48 8d 85 80 03 00 00 	lea    0x380(%rbp),%rax
  40144c:	48 89 eb             	mov    %rbp,%rbx
  40144f:	4d 89 fc             	mov    %r15,%r12
  401452:	48 89 c5             	mov    %rax,%rbp
  401455:	0f 1f 00             	nopl   (%rax)
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  401458:	4c 89 f1             	mov    %r14,%rcx
  40145b:	48 89 de             	mov    %rbx,%rsi
  40145e:	4c 89 ff             	mov    %r15,%rdi
  401461:	4c 89 ea             	mov    %r13,%rdx
  401464:	e8 57 fc ff ff       	call   4010c0 <pthread_create@plt>
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401469:	49 8b 3f             	mov    (%r15),%rdi
  for (int x = 0; x < threadsize ; x++) {
  40146c:	48 83 c3 38          	add    $0x38,%rbx
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401470:	49 8b 96 80 00 00 00 	mov    0x80(%r14),%rdx
  401477:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  40147c:	49 83 c7 08          	add    $0x8,%r15
  401480:	49 81 c6 a0 01 00 00 	add    $0x1a0,%r14
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401487:	e8 b4 fb ff ff       	call   401040 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  40148c:	48 39 dd             	cmp    %rbx,%rbp
  40148f:	75 c7                	jne    401458 <main+0x368>
  }
  
  struct timespec time = {
  401491:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  401496:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  40149b:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec time = {
  4014a0:	66 0f 6f 05 c8 1c 00 00 	movdqa 0x1cc8(%rip),%xmm0        # 403170 <_IO_stdin_used+0x170>
  4014a8:	4c 8d 6c 24 38       	lea    0x38(%rsp),%r13
  4014ad:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  4014b2:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4014b6:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  4014bb:	e8 c0 fb ff ff       	call   401080 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  4014c0:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
  4014c5:	c7 43 64 00 00 00 00 	movl   $0x0,0x64(%rbx)
  4014cc:	c7 83 04 02 00 00 00 00 00 00 	movl   $0x0,0x204(%rbx)
  4014d6:	c7 83 a4 03 00 00 00 00 00 00 	movl   $0x0,0x3a4(%rbx)
  4014e0:	48 83 ed 80          	sub    $0xffffffffffffff80,%rbp
  4014e4:	c7 83 44 05 00 00 00 00 00 00 	movl   $0x0,0x544(%rbx)
  4014ee:	c7 83 e4 06 00 00 00 00 00 00 	movl   $0x0,0x6e4(%rbx)
  4014f8:	c7 83 84 08 00 00 00 00 00 00 	movl   $0x0,0x884(%rbx)
  401502:	c7 83 24 0a 00 00 00 00 00 00 	movl   $0x0,0xa24(%rbx)
  40150c:	c7 83 c4 0b 00 00 00 00 00 00 	movl   $0x0,0xbc4(%rbx)
  401516:	c7 83 64 0d 00 00 00 00 00 00 	movl   $0x0,0xd64(%rbx)
  401520:	c7 83 04 0f 00 00 00 00 00 00 	movl   $0x0,0xf04(%rbx)
  40152a:	c7 83 a4 10 00 00 00 00 00 00 	movl   $0x0,0x10a4(%rbx)
  401534:	c7 83 44 12 00 00 00 00 00 00 	movl   $0x0,0x1244(%rbx)
  40153e:	c7 83 e4 13 00 00 00 00 00 00 	movl   $0x0,0x13e4(%rbx)
  401548:	c7 83 84 15 00 00 00 00 00 00 	movl   $0x0,0x1584(%rbx)
  401552:	c7 83 24 17 00 00 00 00 00 00 	movl   $0x0,0x1724(%rbx)
  40155c:	c7 83 c4 18 00 00 00 00 00 00 	movl   $0x0,0x18c4(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  401566:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401570:	49 8b 3c 24          	mov    (%r12),%rdi
  401574:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  401577:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  40157b:	e8 60 fb ff ff       	call   4010e0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401580:	4c 39 e5             	cmp    %r12,%rbp
  401583:	75 eb                	jne    401570 <main+0x480>
  401585:	48 8d 3d 13 1b 00 00 	lea    0x1b13(%rip),%rdi        # 40309f <_IO_stdin_used+0x9f>
  40158c:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  401590:	45 31 e4             	xor    %r12d,%r12d
  401593:	e8 b8 fa ff ff       	call   401050 <puts@plt>
  for (int x = 0; x < threadsize; x++) {
  401598:	4c 8d b3 48 1a 00 00 	lea    0x1a48(%rbx),%r14
  40159f:	4c 8d 2d 14 1b 00 00 	lea    0x1b14(%rip),%r13        # 4030ba <_IO_stdin_used+0xba>
  4015a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4015b0:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4015b4:	4c 89 ee             	mov    %r13,%rsi
  4015b7:	bf 01 00 00 00       	mov    $0x1,%edi
  4015bc:	31 c0                	xor    %eax,%eax
  4015be:	48 81 c5 a0 01 00 00 	add    $0x1a0,%rbp
  4015c5:	e8 e6 fa ff ff       	call   4010b0 <__printf_chk@plt>
    printf("%ld\n", data[x].freq);
    freq += data[x].freq;
  4015ca:	4c 03 a5 60 fe ff ff 	add    -0x1a0(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  4015d1:	49 39 ee             	cmp    %rbp,%r14
  4015d4:	75 da                	jne    4015b0 <main+0x4c0>
  }
  printf("freq: %ld\n", freq/ seconds);
  4015d6:	4c 89 e0             	mov    %r12,%rax
  4015d9:	49 c1 fc 3f          	sar    $0x3f,%r12
  4015dd:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
  4015e7:	48 8d 35 c6 1a 00 00 	lea    0x1ac6(%rip),%rsi        # 4030b4 <_IO_stdin_used+0xb4>
  4015ee:	48 f7 ed             	imul   %rbp
  4015f1:	bf 01 00 00 00       	mov    $0x1,%edi
  4015f6:	31 c0                	xor    %eax,%eax
  4015f8:	4c 8d bb 98 01 00 00 	lea    0x198(%rbx),%r15
  4015ff:	48 d1 fa             	sar    %rdx
  401602:	4c 29 e2             	sub    %r12,%rdx
  401605:	e8 a6 fa ff ff       	call   4010b0 <__printf_chk@plt>
  long freq_writes = 0;
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  40160a:	48 8b 8b f0 01 00 00 	mov    0x1f0(%rbx),%rcx
  401611:	bf 01 00 00 00       	mov    $0x1,%edi
  401616:	48 03 8b 90 03 00 00 	add    0x390(%rbx),%rcx
  40161d:	48 03 4b 50          	add    0x50(%rbx),%rcx
  401621:	48 03 8b 30 05 00 00 	add    0x530(%rbx),%rcx
  401628:	48 8d 35 90 1a 00 00 	lea    0x1a90(%rip),%rsi        # 4030bf <_IO_stdin_used+0xbf>
  40162f:	48 03 8b d0 06 00 00 	add    0x6d0(%rbx),%rcx
  401636:	48 03 8b 70 08 00 00 	add    0x870(%rbx),%rcx
  40163d:	48 03 8b 10 0a 00 00 	add    0xa10(%rbx),%rcx
  401644:	48 03 8b b0 0b 00 00 	add    0xbb0(%rbx),%rcx
  40164b:	48 03 8b 50 0d 00 00 	add    0xd50(%rbx),%rcx
  401652:	48 03 8b f0 0e 00 00 	add    0xef0(%rbx),%rcx
  401659:	48 03 8b 90 10 00 00 	add    0x1090(%rbx),%rcx
  401660:	48 03 8b 30 12 00 00 	add    0x1230(%rbx),%rcx
  401667:	48 03 8b d0 13 00 00 	add    0x13d0(%rbx),%rcx
  40166e:	48 03 8b 70 15 00 00 	add    0x1570(%rbx),%rcx
  401675:	48 03 8b 10 17 00 00 	add    0x1710(%rbx),%rcx
  40167c:	48 03 8b b0 18 00 00 	add    0x18b0(%rbx),%rcx
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  401683:	48 89 c8             	mov    %rcx,%rax
  401686:	48 c1 f9 3f          	sar    $0x3f,%rcx
  40168a:	48 f7 ed             	imul   %rbp
  40168d:	31 c0                	xor    %eax,%eax
  40168f:	48 d1 fa             	sar    %rdx
  401692:	48 29 ca             	sub    %rcx,%rdx
  401695:	e8 16 fa ff ff       	call   4010b0 <__printf_chk@plt>
  40169a:	48 8d 3d 30 1a 00 00 	lea    0x1a30(%rip),%rdi        # 4030d1 <_IO_stdin_used+0xd1>
  4016a1:	e8 aa f9 ff ff       	call   401050 <puts@plt>
  4016a6:	4c 89 ee             	mov    %r13,%rsi
  4016a9:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ae:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  4016b0:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
  4016b7:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  4016be:	e8 ed f9 ff ff       	call   4010b0 <__printf_chk@plt>
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  4016c3:	48 8b 93 08 01 00 00 	mov    0x108(%rbx),%rdx
  4016ca:	4c 89 ee             	mov    %r13,%rsi
  4016cd:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  4016d4:	bf 01 00 00 00       	mov    $0x1,%edi
  4016d9:	31 c0                	xor    %eax,%eax
  4016db:	48 81 c3 98 1b 00 00 	add    $0x1b98,%rbx
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  4016e2:	45 31 f6             	xor    %r14d,%r14d
  4016e5:	e8 c6 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  4016ea:	4c 89 ee             	mov    %r13,%rsi
  4016ed:	bf 01 00 00 00       	mov    $0x1,%edi
  4016f2:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  4016f4:	48 8b 93 60 e5 ff ff 	mov    -0x1aa0(%rbx),%rdx
  4016fb:	48 2b 93 70 e5 ff ff 	sub    -0x1a90(%rbx),%rdx
  401702:	e8 a9 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  401707:	4c 89 ee             	mov    %r13,%rsi
  40170a:	bf 01 00 00 00       	mov    $0x1,%edi
  40170f:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  401711:	48 8b 93 90 e5 ff ff 	mov    -0x1a70(%rbx),%rdx
  401718:	48 2b 93 80 e5 ff ff 	sub    -0x1a80(%rbx),%rdx
  40171f:	e8 8c f9 ff ff       	call   4010b0 <__printf_chk@plt>
  401724:	4c 89 ee             	mov    %r13,%rsi
  401727:	bf 01 00 00 00       	mov    $0x1,%edi
  40172c:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  40172e:	48 8b 93 80 e5 ff ff 	mov    -0x1a80(%rbx),%rdx
  401735:	48 2b 93 90 e5 ff ff 	sub    -0x1a70(%rbx),%rdx
  40173c:	e8 6f f9 ff ff       	call   4010b0 <__printf_chk@plt>
  401741:	4c 89 ee             	mov    %r13,%rsi
  401744:	bf 01 00 00 00       	mov    $0x1,%edi
  401749:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  40174b:	48 8b 93 80 e5 ff ff 	mov    -0x1a80(%rbx),%rdx
  401752:	48 2b 93 70 e5 ff ff 	sub    -0x1a90(%rbx),%rdx
  401759:	e8 52 f9 ff ff       	call   4010b0 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  40175e:	48 8b 93 b0 e5 ff ff 	mov    -0x1a50(%rbx),%rdx
  401765:	48 8d 35 72 19 00 00 	lea    0x1972(%rip),%rsi        # 4030de <_IO_stdin_used+0xde>
  40176c:	31 c0                	xor    %eax,%eax
  40176e:	48 2b 93 a0 e5 ff ff 	sub    -0x1a60(%rbx),%rdx
  401775:	bf 01 00 00 00       	mov    $0x1,%edi
  40177a:	e8 31 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  } 

  if (SAMPLE == 1) {
  char * filename = calloc(100, sizeof(char));
  40177f:	be 01 00 00 00       	mov    $0x1,%esi
  401784:	bf 64 00 00 00       	mov    $0x64,%edi
  401789:	e8 12 f9 ff ff       	call   4010a0 <calloc@plt>
  char * buf = calloc(1000, sizeof(char));
  40178e:	be 01 00 00 00       	mov    $0x1,%esi
  401793:	bf e8 03 00 00       	mov    $0x3e8,%edi
  char * filename = calloc(100, sizeof(char));
  401798:	48 89 c5             	mov    %rax,%rbp
  char * buf = calloc(1000, sizeof(char));
  40179b:	e8 00 f9 ff ff       	call   4010a0 <calloc@plt>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  4017a0:	44 8b 8b d8 e4 ff ff 	mov    -0x1b28(%rbx),%r9d
  4017a7:	b9 64 00 00 00       	mov    $0x64,%ecx
  4017ac:	48 89 ef             	mov    %rbp,%rdi
  4017af:	4c 8d 05 30 19 00 00 	lea    0x1930(%rip),%r8        # 4030e6 <_IO_stdin_used+0xe6>
  4017b6:	ba 01 00 00 00       	mov    $0x1,%edx
  4017bb:	be 64 00 00 00       	mov    $0x64,%esi
  4017c0:	49 89 c4             	mov    %rax,%r12
  4017c3:	31 c0                	xor    %eax,%eax
  4017c5:	e8 66 f8 ff ff       	call   401030 <__snprintf_chk@plt>
  memset(filename, 0, 100);
  snprintf(filename, 100, "samples%d", data->threadsize);
  FILE *out_file = fopen(filename, "w");
  4017ca:	48 8d 35 1f 19 00 00 	lea    0x191f(%rip),%rsi        # 4030f0 <_IO_stdin_used+0xf0>
  4017d1:	48 89 ef             	mov    %rbp,%rdi
  4017d4:	e8 f7 f8 ff ff       	call   4010d0 <fopen@plt>
  4017d9:	49 89 c5             	mov    %rax,%r13
  
  for (int x = 0; x < threadsize; x++) {
  4017dc:	0f 1f 40 00          	nopl   0x0(%rax)
    for (int y = 0; y < data[x].epochssize; y++) {
  4017e0:	41 8b 0f             	mov    (%r15),%ecx
  4017e3:	31 ed                	xor    %ebp,%ebp
  4017e5:	85 c9                	test   %ecx,%ecx
  4017e7:	7e 1c                	jle    401805 <main+0x715>
  4017e9:	49 8b 77 f8          	mov    -0x8(%r15),%rsi
      struct Epoch * epoch = &data[x].epochs[y];
  4017ed:	48 63 c5             	movslq %ebp,%rax
  4017f0:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  4017f4:	48 8d 14 c6          	lea    (%rsi,%rax,8),%rdx
      if (epoch->set == 1) {
  4017f8:	83 7a 24 01          	cmpl   $0x1,0x24(%rdx)
  4017fc:	74 42                	je     401840 <main+0x750>
    for (int y = 0; y < data[x].epochssize; y++) {
  4017fe:	83 c5 01             	add    $0x1,%ebp
  401801:	39 cd                	cmp    %ecx,%ebp
  401803:	7c e8                	jl     4017ed <main+0x6fd>
  for (int x = 0; x < threadsize; x++) {
  401805:	49 81 c7 a0 01 00 00 	add    $0x1a0,%r15
  40180c:	4c 39 fb             	cmp    %r15,%rbx
  40180f:	75 cf                	jne    4017e0 <main+0x6f0>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  401811:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  401816:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40181f:	0f 85 8c 00 00 00    	jne    4018b1 <main+0x7c1>
  401825:	48 83 c4 78          	add    $0x78,%rsp
  401829:	31 c0                	xor    %eax,%eax
  40182b:	5b                   	pop    %rbx
  40182c:	5d                   	pop    %rbp
  40182d:	41 5c                	pop    %r12
  40182f:	41 5d                	pop    %r13
  401831:	41 5e                	pop    %r14
  401833:	41 5f                	pop    %r15
  401835:	c3                   	ret
  401836:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401840:	4c 89 f0             	mov    %r14,%rax
  401843:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401848:	4c 89 e7             	mov    %r12,%rdi
  40184b:	be 64 00 00 00       	mov    $0x64,%esi
  401850:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  401853:	4c 8d 05 98 18 00 00 	lea    0x1898(%rip),%r8        # 4030f2 <_IO_stdin_used+0xf2>
  40185a:	4c 89 e7             	mov    %r12,%rdi
    for (int y = 0; y < data[x].epochssize; y++) {
  40185d:	83 c5 01             	add    $0x1,%ebp
  401860:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401865:	8b 02                	mov    (%rdx),%eax
  401867:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
  40186b:	50                   	push   %rax
  40186c:	8b 42 20             	mov    0x20(%rdx),%eax
  40186f:	ff 72 18             	push   0x18(%rdx)
  401872:	50                   	push   %rax
  401873:	31 c0                	xor    %eax,%eax
  401875:	ff 72 10             	push   0x10(%rdx)
  401878:	ba 01 00 00 00       	mov    $0x1,%edx
  40187d:	e8 ae f7 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401882:	48 83 c4 20          	add    $0x20,%rsp
  401886:	4c 89 ee             	mov    %r13,%rsi
  401889:	4c 89 e7             	mov    %r12,%rdi
  40188c:	e8 ff f7 ff ff       	call   401090 <fputs@plt>
  401891:	41 8b 0f             	mov    (%r15),%ecx
  401894:	39 cd                	cmp    %ecx,%ebp
  401896:	0f 8c 4d ff ff ff    	jl     4017e9 <main+0x6f9>
  for (int x = 0; x < threadsize; x++) {
  40189c:	49 81 c7 a0 01 00 00 	add    $0x1a0,%r15
  4018a3:	4c 39 fb             	cmp    %r15,%rbx
  4018a6:	0f 85 34 ff ff ff    	jne    4017e0 <main+0x6f0>
  4018ac:	e9 60 ff ff ff       	jmp    401811 <main+0x721>
  4018b1:	e8 ba f7 ff ff       	call   401070 <__stack_chk_fail@plt>
  4018b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

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
  4018d8:	48 c7 c7 f0 10 40 00 	mov    $0x4010f0,%rdi
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
  4019b0:	83 7f 70 01          	cmpl   $0x1,0x70(%rdi)
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
  4019c8:	48 8b 98 c0 01 00 00 	mov    0x1c0(%rax),%rbx
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
  401a14:	41 39 41 70          	cmp    %eax,0x70(%r9)
  401a18:	7f be                	jg     4019d8 <pollthreads+0x28>
}
  401a1a:	31 c0                	xor    %eax,%eax
  401a1c:	5b                   	pop    %rbx
  401a1d:	5d                   	pop    %rbp
  401a1e:	c3                   	ret
  401a1f:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  401a20:	83 c0 01             	add    $0x1,%eax
  401a23:	41 39 41 70          	cmp    %eax,0x70(%r9)
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
  401a43:	48 8b bf c0 00 00 00 	mov    0xc0(%rdi),%rdi
      if (*availableidx == 0) {
  401a4a:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a4d:	48 83 c7 01          	add    $0x1,%rdi
  401a51:	48 85 ff             	test   %rdi,%rdi
  401a54:	7e 66                	jle    401abc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401a56:	4d 8b 93 a8 00 00 00 	mov    0xa8(%r11),%r10
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
  401a98:	41 8b 43 70          	mov    0x70(%r11),%eax
  401a9c:	01 c0                	add    %eax,%eax
  401a9e:	41 39 c0             	cmp    %eax,%r8d
  401aa1:	74 19                	je     401abc <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401aa3:	49 8b bb c0 00 00 00 	mov    0xc0(%r11),%rdi
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

0000000000401ad0 <singlewriter2>:
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401ad0:	41 54                	push   %r12
  401ad2:	55                   	push   %rbp
  401ad3:	53                   	push   %rbx
  401ad4:	48 89 fb             	mov    %rdi,%rbx
  if ((__atomic_load_n(&data->readcursor, __ATOMIC_SEQ_CST) % data->threadsize) == 0) {
  401ad7:	8b 87 58 01 00 00    	mov    0x158(%rdi),%eax
  401add:	99                   	cltd
  401ade:	8b 4f 70             	mov    0x70(%rdi),%ecx
  401ae1:	f7 f9                	idiv   %ecx
  401ae3:	85 d2                	test   %edx,%edx
  401ae5:	74 29                	je     401b10 <singlewriter2+0x40>
  if ((data->writecursor % data->threadsize) == 0) {
  401ae7:	8b 83 50 01 00 00    	mov    0x150(%rbx),%eax
  401aed:	99                   	cltd
  401aee:	f7 f9                	idiv   %ecx
  401af0:	85 d2                	test   %edx,%edx
  401af2:	75 11                	jne    401b05 <singlewriter2+0x35>
    data->currentwrite++;
  401af4:	83 83 84 01 00 00 01 	addl   $0x1,0x184(%rbx)
    data->writecursor = 0;
  401afb:	c7 83 50 01 00 00 00 00 00 00 	movl   $0x0,0x150(%rbx)
}
  401b05:	5b                   	pop    %rbx
  401b06:	5d                   	pop    %rbp
  401b07:	41 5c                	pop    %r12
  401b09:	c3                   	ret
  401b0a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        struct Data * thread = &data->threads[data->threadindex];
  401b10:	48 63 47 6c          	movslq 0x6c(%rdi),%rax
    data->currentread++;
  401b14:	83 87 80 01 00 00 01 	addl   $0x1,0x180(%rdi)
    data->readcursor = 0;
  401b1b:	c7 87 58 01 00 00 00 00 00 00 	movl   $0x0,0x158(%rdi)
        struct Data * thread = &data->threads[data->threadindex];
  401b25:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  401b29:	48 8d 2c 90          	lea    (%rax,%rdx,4),%rbp
  401b2d:	48 c1 e5 05          	shl    $0x5,%rbp
  401b31:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401b35:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401b3a:	48 63 85 9c 01 00 00 	movslq 0x19c(%rbp),%rax
  401b41:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  401b45:	48 8b 85 90 01 00 00 	mov    0x190(%rbp),%rax
  401b4c:	4c 8d 24 d0          	lea    (%rax,%rdx,8),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401b50:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401b55:	e8 06 f5 ff ff       	call   401060 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401b5a:	8b 85 9c 01 00 00    	mov    0x19c(%rbp),%eax
  401b60:	83 c0 01             	add    $0x1,%eax
  401b63:	99                   	cltd
  401b64:	f7 bd 98 01 00 00    	idivl  0x198(%rbp)
        epoch->thread = data->threadindex;
  401b6a:	8b 43 6c             	mov    0x6c(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401b6d:	89 95 9c 01 00 00    	mov    %edx,0x19c(%rbp)
        epoch->thread = data->threadindex;
  401b73:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401b77:	48 8b 05 aa 15 00 00 	mov    0x15aa(%rip),%rax        # 403128 <_IO_stdin_used+0x128>
  401b7e:	49 89 44 24 20       	mov    %rax,0x20(%r12)
  if ((data->writecursor % data->threadsize) == 0) {
  401b83:	8b 4b 70             	mov    0x70(%rbx),%ecx
  401b86:	e9 5c ff ff ff       	jmp    401ae7 <singlewriter2+0x17>
  401b8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000401b90 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b90:	41 55                	push   %r13
  401b92:	49 89 d5             	mov    %rdx,%r13
  401b95:	41 54                	push   %r12
  401b97:	49 89 cc             	mov    %rcx,%r12
  401b9a:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401b9b:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b9e:	48 89 fd             	mov    %rdi,%rbp
  401ba1:	53                   	push   %rbx
  401ba2:	48 89 f3             	mov    %rsi,%rbx
  401ba5:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401ba9:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401bad:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401bb6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401bbb:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401bbd:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401bc5:	8b 81 64 01 00 00    	mov    0x164(%rcx),%eax
  int writers = 0;
  401bcb:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401bd3:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401bdb:	83 c0 01             	add    $0x1,%eax
  401bde:	99                   	cltd
  401bdf:	f7 7f 70             	idivl  0x70(%rdi)
  401be2:	89 91 64 01 00 00    	mov    %edx,0x164(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401be8:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401bed:	4c 89 e9             	mov    %r13,%rcx
  401bf0:	e8 4b fe ff ff       	call   401a40 <findavailable>
  if (fill == 1) {
  401bf5:	83 f8 01             	cmp    $0x1,%eax
  401bf8:	0f 84 59 01 00 00    	je     401d57 <singlewriter+0x1c7>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401bfe:	48 89 ef             	mov    %rbp,%rdi
  401c01:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401c06:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401c0b:	4c 89 e2             	mov    %r12,%rdx
  401c0e:	4c 89 ee             	mov    %r13,%rsi
  401c11:	e8 9a fd ff ff       	call   4019b0 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401c16:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401c1b:	85 ff                	test   %edi,%edi
  401c1d:	0f 8e 5e 01 00 00    	jle    401d81 <singlewriter+0x1f1>
  401c23:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401c28:	31 c9                	xor    %ecx,%ecx
  401c2a:	eb 62                	jmp    401c8e <singlewriter+0xfe>
  401c2c:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c30:	48 8b 04 cb          	mov    (%rbx,%rcx,8),%rax
          int thread = readyreaders[x];
  401c34:	49 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%rdx
  401c39:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401c3c:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c40:	48 c1 e0 05          	shl    $0x5,%rax
  401c44:	48 03 85 a8 00 00 00 	add    0xa8(%rbp),%rax
          data->threads[thread].reading = chunk;
  401c4b:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
          int thread = readyreaders[x];
  401c4f:	49 89 d1             	mov    %rdx,%r9
          data->threads[thread].start = start;
  401c52:	66 0f 6e 00          	movd   (%rax),%xmm0
  401c56:	66 0f 6e 48 08       	movd   0x8(%rax),%xmm1
          data->threads[thread].reading = chunk;
  401c5b:	4a 8d 14 92          	lea    (%rdx,%r10,4),%rdx
          chunk->available = READING;
  401c5f:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
          data->threads[thread].reading = chunk;
  401c66:	48 c1 e2 05          	shl    $0x5,%rdx
  401c6a:	48 03 55 30          	add    0x30(%rbp),%rdx
          data->threads[thread].start = start;
  401c6e:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401c72:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
          chunk->owner = thread;
  401c79:	44 89 48 14          	mov    %r9d,0x14(%rax)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401c7d:	83 8a d0 00 00 00 10 	orl    $0x10,0xd0(%rdx)
          data->threads[thread].start = start;
  401c84:	66 0f d6 42 14       	movq   %xmm0,0x14(%rdx)
        for (int x = 0; x < readers ; x++) {
  401c89:	48 39 cf             	cmp    %rcx,%rdi
  401c8c:	74 07                	je     401c95 <singlewriter+0x105>
  401c8e:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401c90:	4c 39 c1             	cmp    %r8,%rcx
  401c93:	75 9b                	jne    401c30 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401c95:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401c9a:	45 85 c0             	test   %r8d,%r8d
  401c9d:	7e 77                	jle    401d16 <singlewriter+0x186>
                if (assignedchunk  == availableidx) {
  401c9f:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401ca3:	41 01 f0             	add    %esi,%r8d
  401ca6:	eb 6a                	jmp    401d12 <singlewriter+0x182>
  401ca8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401cb0:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401cb3:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401cb6:	49 63 14 24          	movslq (%r12),%rdx
   for (int x = 0; x < writers ; x++) {
  401cba:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401cbe:	48 8b 04 f3          	mov    (%rbx,%rsi,8),%rax
          data->threads[thread].writing = chunk;
  401cc2:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
          int thread = readywriters[x];
  401cc6:	49 89 d1             	mov    %rdx,%r9
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401cc9:	48 c1 e0 05          	shl    $0x5,%rax
  401ccd:	48 03 85 a8 00 00 00 	add    0xa8(%rbp),%rax
          data->threads[thread].writing = chunk;
  401cd4:	48 8d 14 b2          	lea    (%rdx,%rsi,4),%rdx
          data->threads[thread].publishstart = start;
  401cd8:	66 0f 6e 00          	movd   (%rax),%xmm0
  401cdc:	66 0f 6e 50 08       	movd   0x8(%rax),%xmm2
          data->threads[thread].writing = chunk;
  401ce1:	48 c1 e2 05          	shl    $0x5,%rdx
      chunk->available = WRITING;
  401ce5:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
          data->threads[thread].writing = chunk;
  401cec:	48 03 55 30          	add    0x30(%rbp),%rdx
          data->threads[thread].publishstart = start;
  401cf0:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401cf4:	48 89 82 b8 00 00 00 	mov    %rax,0xb8(%rdx)
          chunk->owner = thread;
  401cfb:	44 89 48 14          	mov    %r9d,0x14(%rax)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401cff:	83 8a d0 00 00 00 20 	orl    $0x20,0xd0(%rdx)
          data->threads[thread].publishstart = start;
  401d06:	66 0f d6 42 40       	movq   %xmm0,0x40(%rdx)
   for (int x = 0; x < writers ; x++) {
  401d0b:	44 39 c1             	cmp    %r8d,%ecx
  401d0e:	74 06                	je     401d16 <singlewriter+0x186>
  401d10:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401d12:	39 f7                	cmp    %esi,%edi
  401d14:	75 9a                	jne    401cb0 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401d16:	8b 7d 70             	mov    0x70(%rbp),%edi
  401d19:	85 ff                	test   %edi,%edi
  401d1b:	7e 38                	jle    401d55 <singlewriter+0x1c5>
        if (data->threads[x].newmask != 0) {
  401d1d:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401d21:	31 c9                	xor    %ecx,%ecx
  401d23:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401d28:	48 63 d1             	movslq %ecx,%rdx
  401d2b:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
  401d2f:	48 8d 04 82          	lea    (%rdx,%rax,4),%rax
  401d33:	48 c1 e0 05          	shl    $0x5,%rax
  401d37:	4c 01 c0             	add    %r8,%rax
  401d3a:	8b b0 d0 00 00 00    	mov    0xd0(%rax),%esi
  401d40:	85 f6                	test   %esi,%esi
  401d42:	74 34                	je     401d78 <singlewriter+0x1e8>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401d44:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401d48:	83 c1 01             	add    $0x1,%ecx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401d4b:	89 34 90             	mov    %esi,(%rax,%rdx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401d4e:	8b 7d 70             	mov    0x70(%rbp),%edi
  401d51:	39 f9                	cmp    %edi,%ecx
  401d53:	7c d3                	jl     401d28 <singlewriter+0x198>
  return 0;
  401d55:	31 c0                	xor    %eax,%eax
}
  401d57:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401d5c:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401d65:	75 21                	jne    401d88 <singlewriter+0x1f8>
  401d67:	48 83 c4 28          	add    $0x28,%rsp
  401d6b:	5b                   	pop    %rbx
  401d6c:	5d                   	pop    %rbp
  401d6d:	41 5c                	pop    %r12
  401d6f:	41 5d                	pop    %r13
  401d71:	c3                   	ret
  401d72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      for (int x = 0; x < data->threadsize ; x++) {
  401d78:	83 c1 01             	add    $0x1,%ecx
  401d7b:	39 f9                	cmp    %edi,%ecx
  401d7d:	7c a9                	jl     401d28 <singlewriter+0x198>
  401d7f:	eb d4                	jmp    401d55 <singlewriter+0x1c5>
      int assignedchunk = 0;
  401d81:	31 f6                	xor    %esi,%esi
  401d83:	e9 0d ff ff ff       	jmp    401c95 <singlewriter+0x105>
}
  401d88:	e8 e3 f2 ff ff       	call   401070 <__stack_chk_fail@plt>
  401d8d:	0f 1f 00             	nopl   (%rax)

0000000000401d90 <threadwork>:
int * threadwork(struct Data * data) {
  401d90:	41 57                	push   %r15
  401d92:	41 56                	push   %r14
  401d94:	41 55                	push   %r13
  401d96:	41 54                	push   %r12
  401d98:	55                   	push   %rbp
  401d99:	53                   	push   %rbx
  401d9a:	48 89 fb             	mov    %rdi,%rbx
  clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401d9d:	bf 04 00 00 00       	mov    $0x4,%edi
int * threadwork(struct Data * data) {
  401da2:	48 83 ec 38          	sub    $0x38,%rsp
  401da6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401daf:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  401db4:	31 c0                	xor    %eax,%eax
  clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401db6:	48 8d 74 24 10       	lea    0x10(%rsp),%rsi
  401dbb:	e8 a0 f2 ff ff       	call   401060 <clock_gettime@plt>
     for (int x = 0; x < data->threadsize ; x++) {
  401dc0:	8b 43 70             	mov    0x70(%rbx),%eax
  __atomic_fetch_add(&data->main->readcursor, 1, __ATOMIC_ACQUIRE);
  401dc3:	48 8b 4b 28          	mov    0x28(%rbx),%rcx
     for (int x = 0; x < data->threadsize ; x++) {
  401dc7:	85 c0                	test   %eax,%eax
  401dc9:	0f 8e 45 01 00 00    	jle    401f14 <threadwork+0x184>
        long buffer = (data->threadindex << 24) | (data->main->readcursor % 0xff) << 16 | x << 8 | data->readcursor % 0xff;
  401dcf:	8b 83 58 01 00 00    	mov    0x158(%rbx),%eax
     for (int x = 0; x < data->threadsize ; x++) {
  401dd5:	31 f6                	xor    %esi,%esi
  401dd7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        long buffer = (data->threadindex << 24) | (data->main->readcursor % 0xff) << 16 | x << 8 | data->readcursor % 0xff;
  401de0:	48 63 91 58 01 00 00 	movslq 0x158(%rcx),%rdx
  401de7:	41 89 c2             	mov    %eax,%r10d
  401dea:	8b 7b 6c             	mov    0x6c(%rbx),%edi
  401ded:	41 c1 fa 1f          	sar    $0x1f,%r10d
        epoch->time = time;
  401df1:	66 0f 6f 44 24 10    	movdqa 0x10(%rsp),%xmm0
        data->freq_writes++;
  401df7:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
        long buffer = (data->threadindex << 24) | (data->main->readcursor % 0xff) << 16 | x << 8 | data->readcursor % 0xff;
  401dfc:	49 89 d0             	mov    %rdx,%r8
  401dff:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401e06:	45 89 c1             	mov    %r8d,%r9d
  401e09:	41 c1 f9 1f          	sar    $0x1f,%r9d
  401e0d:	48 c1 ea 20          	shr    $0x20,%rdx
  401e11:	44 01 c2             	add    %r8d,%edx
  401e14:	c1 fa 07             	sar    $0x7,%edx
  401e17:	44 29 ca             	sub    %r9d,%edx
  401e1a:	41 89 d1             	mov    %edx,%r9d
  401e1d:	41 c1 e1 08          	shl    $0x8,%r9d
  401e21:	41 29 d1             	sub    %edx,%r9d
  401e24:	48 63 d0             	movslq %eax,%rdx
  401e27:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401e2e:	45 29 c8             	sub    %r9d,%r8d
  401e31:	41 89 f9             	mov    %edi,%r9d
  401e34:	41 c1 e1 18          	shl    $0x18,%r9d
  401e38:	41 c1 e0 10          	shl    $0x10,%r8d
  401e3c:	48 c1 ea 20          	shr    $0x20,%rdx
  401e40:	01 c2                	add    %eax,%edx
  401e42:	c1 fa 07             	sar    $0x7,%edx
  401e45:	44 29 d2             	sub    %r10d,%edx
  401e48:	41 89 d2             	mov    %edx,%r10d
  401e4b:	41 c1 e2 08          	shl    $0x8,%r10d
  401e4f:	41 29 d2             	sub    %edx,%r10d
  401e52:	44 29 d0             	sub    %r10d,%eax
  401e55:	44 09 c8             	or     %r9d,%eax
  401e58:	41 09 c0             	or     %eax,%r8d
  401e5b:	89 f0                	mov    %esi,%eax
  401e5d:	c1 e0 08             	shl    $0x8,%eax
  401e60:	45 89 c2             	mov    %r8d,%r10d
  401e63:	41 09 c2             	or     %eax,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  401e66:	48 63 c7             	movslq %edi,%rax
  401e69:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  401e6d:	4c 8d 04 90          	lea    (%rax,%rdx,4),%r8
  401e71:	49 c1 e0 05          	shl    $0x5,%r8
  401e75:	4c 03 43 30          	add    0x30(%rbx),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401e79:	49 63 90 9c 01 00 00 	movslq 0x19c(%r8),%rdx
  401e80:	48 89 d0             	mov    %rdx,%rax
  401e83:	4c 8d 0c 92          	lea    (%rdx,%rdx,4),%r9
  401e87:	49 8b 90 90 01 00 00 	mov    0x190(%r8),%rdx
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e8e:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401e91:	4e 8d 0c ca          	lea    (%rdx,%r9,8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e95:	99                   	cltd
  401e96:	41 f7 b8 98 01 00 00 	idivl  0x198(%r8)
        data->main->works[buffer] = 0;
  401e9d:	48 8b 41 78          	mov    0x78(%rcx),%rax
        epoch->time = time;
  401ea1:	41 0f 11 41 08       	movups %xmm0,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ea6:	41 89 90 9c 01 00 00 	mov    %edx,0x19c(%r8)
        long buffer = (data->threadindex << 24) | (data->main->readcursor % 0xff) << 16 | x << 8 | data->readcursor % 0xff;
  401ead:	4d 63 c2             	movslq %r10d,%r8
        epoch->thread = data->threadindex;
  401eb0:	41 89 39             	mov    %edi,(%r9)
        long buffer = (data->threadindex << 24) | (data->main->readcursor % 0xff) << 16 | x << 8 | data->readcursor % 0xff;
  401eb3:	4d 89 41 18          	mov    %r8,0x18(%r9)
  epoch->set = 1;
  401eb7:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
        data->main->works[buffer] = 0;
  401ebf:	42 c6 04 00 00       	movb   $0x0,(%rax,%r8,1)
          data->readcursor = (data->readcursor + 1) % 0xffffff;
  401ec4:	8b 83 58 01 00 00    	mov    0x158(%rbx),%eax
  401eca:	8d 50 01             	lea    0x1(%rax),%edx
  401ecd:	48 63 c2             	movslq %edx,%rax
  401ed0:	89 d1                	mov    %edx,%ecx
  401ed2:	48 69 c0 81 00 00 80 	imul   $0xffffffff80000081,%rax,%rax
  401ed9:	48 c1 e8 20          	shr    $0x20,%rax
  401edd:	01 d0                	add    %edx,%eax
  401edf:	c1 f9 1f             	sar    $0x1f,%ecx
     for (int x = 0; x < data->threadsize ; x++) {
  401ee2:	83 c6 01             	add    $0x1,%esi
          data->readcursor = (data->readcursor + 1) % 0xffffff;
  401ee5:	c1 f8 17             	sar    $0x17,%eax
  401ee8:	29 c8                	sub    %ecx,%eax
  401eea:	89 c1                	mov    %eax,%ecx
  401eec:	c1 e1 18             	shl    $0x18,%ecx
  401eef:	29 c1                	sub    %eax,%ecx
  401ef1:	89 d0                	mov    %edx,%eax
  401ef3:	29 c8                	sub    %ecx,%eax
    data->prevread = data->main->currentread;
  401ef5:	48 8b 4b 28          	mov    0x28(%rbx),%rcx
          data->readcursor = (data->readcursor + 1) % 0xffffff;
  401ef9:	89 83 58 01 00 00    	mov    %eax,0x158(%rbx)
    data->prevread = data->main->currentread;
  401eff:	8b 91 80 01 00 00    	mov    0x180(%rcx),%edx
  401f05:	89 93 88 01 00 00    	mov    %edx,0x188(%rbx)
     for (int x = 0; x < data->threadsize ; x++) {
  401f0b:	39 73 70             	cmp    %esi,0x70(%rbx)
  401f0e:	0f 8f cc fe ff ff    	jg     401de0 <threadwork+0x50>
  __atomic_fetch_add(&data->main->readcursor, 1, __ATOMIC_ACQUIRE);
  401f14:	f0 83 81 58 01 00 00 01 	lock addl $0x1,0x158(%rcx)
        for (int y = 0 ; y < data->threadsize; y++) {
  401f1c:	44 8b 53 70          	mov    0x70(%rbx),%r10d
  401f20:	45 85 d2             	test   %r10d,%r10d
  401f23:	0f 8e 3b 01 00 00    	jle    402064 <threadwork+0x2d4>
          int x = (data->threadindex + y) % data->threadsize;
  401f29:	8b 6b 6c             	mov    0x6c(%rbx),%ebp
          data->freq++;
  401f2c:	4c 8b 43 48          	mov    0x48(%rbx),%r8
  401f30:	41 8d 42 ff          	lea    -0x1(%r10),%eax
  401f34:	89 44 24 0c          	mov    %eax,0xc(%rsp)
  401f38:	4d 8d 6c 00 01       	lea    0x1(%r8,%rax,1),%r13
                struct Data * thread = &data->threads[data->threadindex];
  401f3d:	48 63 c5             	movslq %ebp,%rax
                long buffer = (x << 24) | past << 16 | data->threadindex << 8 | (rc) % 0xff;
  401f40:	41 89 ef             	mov    %ebp,%r15d
          int x = (data->threadindex + y) % data->threadsize;
  401f43:	41 89 ec             	mov    %ebp,%r12d
                struct Data * thread = &data->threads[data->threadindex];
  401f46:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
                long buffer = (x << 24) | past << 16 | data->threadindex << 8 | (rc) % 0xff;
  401f4a:	41 c1 e7 08          	shl    $0x8,%r15d
          int x = (data->threadindex + y) % data->threadsize;
  401f4e:	45 29 c4             	sub    %r8d,%r12d
                struct Data * thread = &data->threads[data->threadindex];
  401f51:	4c 8d 34 90          	lea    (%rax,%rdx,4),%r14
  401f55:	49 c1 e6 05          	shl    $0x5,%r14
  401f59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          int x = (data->threadindex + y) % data->threadsize;
  401f60:	43 8d 04 04          	lea    (%r12,%r8,1),%eax
          data->freq++;
  401f64:	49 83 c0 01          	add    $0x1,%r8
          int x = (data->threadindex + y) % data->threadsize;
  401f68:	99                   	cltd
          data->freq++;
  401f69:	4c 89 43 48          	mov    %r8,0x48(%rbx)
          int x = (data->threadindex + y) % data->threadsize;
  401f6d:	41 f7 fa             	idiv   %r10d
  401f70:	89 d6                	mov    %edx,%esi
          if (x != data->threadindex) {
  401f72:	39 ea                	cmp    %ebp,%edx
  401f74:	0f 84 e1 00 00 00    	je     40205b <threadwork+0x2cb>
            long past = ((data->main->readcursor - 1) % 0xff);
  401f7a:	48 8b 43 28          	mov    0x28(%rbx),%rax
            int rc = data->threads[x].readcursor - 2;
  401f7e:	48 8b 7b 30          	mov    0x30(%rbx),%rdi
  401f82:	41 bb fe 00 00 00    	mov    $0xfe,%r11d
            long past = ((data->main->readcursor - 1) % 0xff);
  401f88:	8b 80 58 01 00 00    	mov    0x158(%rax),%eax
  401f8e:	83 e8 01             	sub    $0x1,%eax
  401f91:	48 63 c8             	movslq %eax,%rcx
  401f94:	99                   	cltd
  401f95:	48 69 c9 81 80 80 80 	imul   $0xffffffff80808081,%rcx,%rcx
  401f9c:	48 c1 e9 20          	shr    $0x20,%rcx
  401fa0:	01 c1                	add    %eax,%ecx
  401fa2:	c1 f9 07             	sar    $0x7,%ecx
  401fa5:	29 d1                	sub    %edx,%ecx
  401fa7:	89 ca                	mov    %ecx,%edx
  401fa9:	c1 e2 08             	shl    $0x8,%edx
  401fac:	29 ca                	sub    %ecx,%edx
              past = data->threadsize - 1;
  401fae:	29 d0                	sub    %edx,%eax
  401fb0:	89 c1                	mov    %eax,%ecx
            int rc = data->threads[x].readcursor - 2;
  401fb2:	48 63 c6             	movslq %esi,%rax
              past = data->threadsize - 1;
  401fb5:	0f 48 4c 24 0c       	cmovs  0xc(%rsp),%ecx
            int rc = data->threads[x].readcursor - 2;
  401fba:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  401fbe:	48 8d 04 90          	lea    (%rax,%rdx,4),%rax
  401fc2:	48 63 c9             	movslq %ecx,%rcx
  401fc5:	48 c1 e0 05          	shl    $0x5,%rax
  401fc9:	8b 94 07 58 01 00 00 	mov    0x158(%rdi,%rax,1),%edx
            if (rc < 0) {
  401fd0:	83 ea 02             	sub    $0x2,%edx
  401fd3:	78 2d                	js     402002 <threadwork+0x272>
                long buffer = (x << 24) | past << 16 | data->threadindex << 8 | (rc) % 0xff;
  401fd5:	48 63 c2             	movslq %edx,%rax
  401fd8:	41 89 d1             	mov    %edx,%r9d
  401fdb:	48 69 c0 81 80 80 80 	imul   $0xffffffff80808081,%rax,%rax
  401fe2:	41 c1 f9 1f          	sar    $0x1f,%r9d
  401fe6:	48 c1 e8 20          	shr    $0x20,%rax
  401fea:	01 d0                	add    %edx,%eax
  401fec:	c1 f8 07             	sar    $0x7,%eax
  401fef:	44 29 c8             	sub    %r9d,%eax
  401ff2:	41 89 c1             	mov    %eax,%r9d
  401ff5:	41 c1 e1 08          	shl    $0x8,%r9d
  401ff9:	41 29 c1             	sub    %eax,%r9d
  401ffc:	44 29 ca             	sub    %r9d,%edx
  401fff:	4c 63 da             	movslq %edx,%r11
                struct Data * thread = &data->threads[data->threadindex];
  402002:	4c 01 f7             	add    %r14,%rdi
            thepoch->time = time; 
  402005:	66 0f 6f 4c 24 10    	movdqa 0x10(%rsp),%xmm1
                long buffer = (x << 24) | past << 16 | data->threadindex << 8 | (rc) % 0xff;
  40200b:	48 c1 e1 10          	shl    $0x10,%rcx
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  40200f:	48 63 97 9c 01 00 00 	movslq 0x19c(%rdi),%rdx
  402016:	48 89 d0             	mov    %rdx,%rax
  402019:	4c 8d 0c 92          	lea    (%rdx,%rdx,4),%r9
  40201d:	48 8b 97 90 01 00 00 	mov    0x190(%rdi),%rdx
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402024:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402027:	4e 8d 0c ca          	lea    (%rdx,%r9,8),%r9
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40202b:	99                   	cltd
  40202c:	f7 bf 98 01 00 00    	idivl  0x198(%rdi)
            thepoch->time = time; 
  402032:	41 0f 11 49 08       	movups %xmm1,0x8(%r9)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402037:	89 97 9c 01 00 00    	mov    %edx,0x19c(%rdi)
                thepoch->thread = x;
  40203d:	41 89 31             	mov    %esi,(%r9)
                long buffer = (x << 24) | past << 16 | data->threadindex << 8 | (rc) % 0xff;
  402040:	c1 e6 18             	shl    $0x18,%esi
  402043:	44 09 fe             	or     %r15d,%esi
          thepoch->set = 1;
  402046:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
                long buffer = (x << 24) | past << 16 | data->threadindex << 8 | (rc) % 0xff;
  40204e:	48 63 f6             	movslq %esi,%rsi
  402051:	48 09 f1             	or     %rsi,%rcx
  402054:	4c 09 d9             	or     %r11,%rcx
  402057:	49 89 49 18          	mov    %rcx,0x18(%r9)
        for (int y = 0 ; y < data->threadsize; y++) {
  40205b:	4d 39 e8             	cmp    %r13,%r8
  40205e:	0f 85 fc fe ff ff    	jne    401f60 <threadwork+0x1d0>
}
  402064:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
  402069:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  402072:	75 11                	jne    402085 <threadwork+0x2f5>
  402074:	48 83 c4 38          	add    $0x38,%rsp
  402078:	31 c0                	xor    %eax,%eax
  40207a:	5b                   	pop    %rbx
  40207b:	5d                   	pop    %rbp
  40207c:	41 5c                	pop    %r12
  40207e:	41 5d                	pop    %r13
  402080:	41 5e                	pop    %r14
  402082:	41 5f                	pop    %r15
  402084:	c3                   	ret
  402085:	e8 e6 ef ff ff       	call   401070 <__stack_chk_fail@plt>
  40208a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000402090 <work>:
void * work(void * arg) {
  402090:	41 56                	push   %r14
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  402092:	48 8d 35 6b 0f 00 00 	lea    0xf6b(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  402099:	31 c0                	xor    %eax,%eax
  40209b:	41 55                	push   %r13
  40209d:	41 54                	push   %r12
  40209f:	55                   	push   %rbp
  4020a0:	53                   	push   %rbx
  4020a1:	8b 57 6c             	mov    0x6c(%rdi),%edx
  4020a4:	48 89 fb             	mov    %rdi,%rbx
  4020a7:	bf 01 00 00 00       	mov    $0x1,%edi
  4020ac:	e8 ff ef ff ff       	call   4010b0 <__printf_chk@plt>
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  4020b1:	8b 43 6c             	mov    0x6c(%rbx),%eax
  4020b4:	48 8d 35 5c 0f 00 00 	lea    0xf5c(%rip),%rsi        # 403017 <_IO_stdin_used+0x17>
  4020bb:	bf 01 00 00 00       	mov    $0x1,%edi
  int bucketstart = data->bucketstart;
  4020c0:	44 8b b3 a0 00 00 00 	mov    0xa0(%rbx),%r14d
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  4020c7:	8d 50 01             	lea    0x1(%rax),%edx
  4020ca:	31 c0                	xor    %eax,%eax
  int bucketlim = ((data->threadindex + 1) * data->buckets) ;
  4020cc:	0f af 93 98 00 00 00 	imul   0x98(%rbx),%edx
  4020d3:	e8 d8 ef ff ff       	call   4010b0 <__printf_chk@plt>
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  4020d8:	48 8b 83 c0 00 00 00 	mov    0xc0(%rbx),%rax
  4020df:	be 08 00 00 00       	mov    $0x8,%esi
  4020e4:	48 8d 78 01          	lea    0x1(%rax),%rdi
  4020e8:	e8 b3 ef ff ff       	call   4010a0 <calloc@plt>
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  4020ed:	4c 63 6b 70          	movslq 0x70(%rbx),%r13
  4020f1:	be 04 00 00 00       	mov    $0x4,%esi
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  4020f6:	48 89 c5             	mov    %rax,%rbp
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  4020f9:	4c 89 ef             	mov    %r13,%rdi
  4020fc:	e8 9f ef ff ff       	call   4010a0 <calloc@plt>
  int * readywriters = calloc(data->threadsize, sizeof(int));
  402101:	be 04 00 00 00       	mov    $0x4,%esi
  402106:	4c 89 ef             	mov    %r13,%rdi
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  402109:	49 89 c4             	mov    %rax,%r12
  int * readywriters = calloc(data->threadsize, sizeof(int));
  40210c:	e8 8f ef ff ff       	call   4010a0 <calloc@plt>
  while (data->running == 1) {
  402111:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  data->workindex = bucketstart;
  402115:	44 89 73 5c          	mov    %r14d,0x5c(%rbx)
  while (data->running == 1) {
  402119:	75 49                	jne    402164 <work+0xd4>
  40211b:	49 89 c5             	mov    %rax,%r13
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  40211e:	4c 8d b3 30 01 00 00 	lea    0x130(%rbx),%r14
  402125:	0f 1f 00             	nopl   (%rax)
    if (data->threadindex == 0) {
  402128:	8b 43 6c             	mov    0x6c(%rbx),%eax
  40212b:	85 c0                	test   %eax,%eax
  40212d:	75 59                	jne    402188 <work+0xf8>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  40212f:	4c 89 f6             	mov    %r14,%rsi
  402132:	bf 04 00 00 00       	mov    $0x4,%edi
  402137:	e8 24 ef ff ff       	call   401060 <clock_gettime@plt>
      singlewriter2(data, available, readyreaders, readywriters);
  40213c:	4c 89 e9             	mov    %r13,%rcx
  40213f:	4c 89 e2             	mov    %r12,%rdx
  402142:	48 89 ee             	mov    %rbp,%rsi
  402145:	48 89 df             	mov    %rbx,%rdi
  402148:	e8 83 f9 ff ff       	call   401ad0 <singlewriter2>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swend);
  40214d:	48 8d b3 40 01 00 00 	lea    0x140(%rbx),%rsi
  402154:	bf 04 00 00 00       	mov    $0x4,%edi
  402159:	e8 02 ef ff ff       	call   401060 <clock_gettime@plt>
  while (data->running == 1) {
  40215e:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  402162:	74 c4                	je     402128 <work+0x98>
  402164:	8b 53 6c             	mov    0x6c(%rbx),%edx
  402167:	48 8d 35 b7 0e 00 00 	lea    0xeb7(%rip),%rsi        # 403025 <_IO_stdin_used+0x25>
  40216e:	bf 01 00 00 00       	mov    $0x1,%edi
  402173:	31 c0                	xor    %eax,%eax
  402175:	e8 36 ef ff ff       	call   4010b0 <__printf_chk@plt>
}
  40217a:	5b                   	pop    %rbx
  40217b:	5d                   	pop    %rbp
  40217c:	41 5c                	pop    %r12
  40217e:	41 5d                	pop    %r13
  402180:	41 5e                	pop    %r14
  402182:	c3                   	ret
  402183:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      threadwork(data);
  402188:	48 89 df             	mov    %rbx,%rdi
  40218b:	e8 00 fc ff ff       	call   401d90 <threadwork>
  while (data->running == 1) {
  402190:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  402194:	74 92                	je     402128 <work+0x98>
  402196:	eb cc                	jmp    402164 <work+0xd4>
  402198:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

00000000004021a0 <work2>:
  while (data->running == 1) {
  4021a0:	eb 0b                	jmp    4021ad <work2+0xd>
  4021a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  4021a8:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  4021ad:	83 7f 64 01          	cmpl   $0x1,0x64(%rdi)
  4021b1:	74 f5                	je     4021a8 <work2+0x8>
}
  4021b3:	c3                   	ret

Disassembly of section .fini:

00000000004021b4 <_fini>:
  4021b4:	f3 0f 1e fa          	endbr64
  4021b8:	48 83 ec 08          	sub    $0x8,%rsp
  4021bc:	48 83 c4 08          	add    $0x8,%rsp
  4021c0:	c3                   	ret
