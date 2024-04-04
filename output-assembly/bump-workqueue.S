
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

0000000000401020 <__snprintf_chk@plt-0x10>:
  401020:	ff 35 5a 2f 00 00    	push   0x2f5a(%rip)        # 403f80 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 5c 2f 00 00    	jmp    *0x2f5c(%rip)        # 403f88 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <__snprintf_chk@plt>:
  401030:	ff 25 5a 2f 00 00    	jmp    *0x2f5a(%rip)        # 403f90 <__snprintf_chk@GLIBC_2.3.4>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <pthread_setaffinity_np@plt>:
  401040:	ff 25 52 2f 00 00    	jmp    *0x2f52(%rip)        # 403f98 <pthread_setaffinity_np@GLIBC_2.34>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <puts@plt>:
  401050:	ff 25 4a 2f 00 00    	jmp    *0x2f4a(%rip)        # 403fa0 <puts@GLIBC_2.2.5>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <clock_gettime@plt>:
  401060:	ff 25 42 2f 00 00    	jmp    *0x2f42(%rip)        # 403fa8 <clock_gettime@GLIBC_2.17>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <__stack_chk_fail@plt>:
  401070:	ff 25 3a 2f 00 00    	jmp    *0x2f3a(%rip)        # 403fb0 <__stack_chk_fail@GLIBC_2.4>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <nanosleep@plt>:
  401080:	ff 25 32 2f 00 00    	jmp    *0x2f32(%rip)        # 403fb8 <nanosleep@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <fputs@plt>:
  401090:	ff 25 2a 2f 00 00    	jmp    *0x2f2a(%rip)        # 403fc0 <fputs@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <calloc@plt>:
  4010a0:	ff 25 22 2f 00 00    	jmp    *0x2f22(%rip)        # 403fc8 <calloc@GLIBC_2.2.5>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <__printf_chk@plt>:
  4010b0:	ff 25 1a 2f 00 00    	jmp    *0x2f1a(%rip)        # 403fd0 <__printf_chk@GLIBC_2.3.4>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <pthread_create@plt>:
  4010c0:	ff 25 12 2f 00 00    	jmp    *0x2f12(%rip)        # 403fd8 <pthread_create@GLIBC_2.34>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010d0 <fopen@plt>:
  4010d0:	ff 25 0a 2f 00 00    	jmp    *0x2f0a(%rip)        # 403fe0 <fopen@GLIBC_2.2.5>
  4010d6:	68 0a 00 00 00       	push   $0xa
  4010db:	e9 40 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010e0 <pthread_join@plt>:
  4010e0:	ff 25 02 2f 00 00    	jmp    *0x2f02(%rip)        # 403fe8 <pthread_join@GLIBC_2.34>
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
  4010fc:	48 8d 35 32 0f 00 00 	lea    0xf32(%rip),%rsi        # 402035 <_IO_stdin_used+0x35>
  401103:	41 56                	push   %r14
  char *works = calloc(worksize, sizeof(char));
  printf("Buffer size %ld\n", worksize);
  int chunkindex = 0;
  int * readcursors = calloc(threadsize, sizeof(int));
  int * writecursors = calloc(threadsize, sizeof(int));
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  401105:	41 be 0f 00 00 00    	mov    $0xf,%r14d
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
  401135:	48 8d 35 0b 0f 00 00 	lea    0xf0b(%rip),%rsi        # 402047 <_IO_stdin_used+0x47>
  40113c:	31 c0                	xor    %eax,%eax
  40113e:	bf 01 00 00 00       	mov    $0x1,%edi
  401143:	e8 68 ff ff ff       	call   4010b0 <__printf_chk@plt>
  401148:	ba 20 00 00 00       	mov    $0x20,%edx
  40114d:	48 8d 35 ef 0e 00 00 	lea    0xeef(%rip),%rsi        # 402043 <_IO_stdin_used+0x43>
  401154:	31 c0                	xor    %eax,%eax
  401156:	bf 01 00 00 00       	mov    $0x1,%edi
  40115b:	e8 50 ff ff ff       	call   4010b0 <__printf_chk@plt>
  401160:	ba 0e 00 00 00       	mov    $0xe,%edx
  401165:	48 8d 35 ea 0e 00 00 	lea    0xeea(%rip),%rsi        # 402056 <_IO_stdin_used+0x56>
  40116c:	31 c0                	xor    %eax,%eax
  40116e:	bf 01 00 00 00       	mov    $0x1,%edi
  401173:	e8 38 ff ff ff       	call   4010b0 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401178:	be 08 00 00 00       	mov    $0x8,%esi
  40117d:	bf 0e 00 00 00       	mov    $0xe,%edi
  401182:	e8 19 ff ff ff       	call   4010a0 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401187:	be 38 00 00 00       	mov    $0x38,%esi
  40118c:	bf 0e 00 00 00       	mov    $0xe,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401191:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401196:	e8 05 ff ff ff       	call   4010a0 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40119b:	be c0 16 00 00       	mov    $0x16c0,%esi
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
  4011c5:	48 8d 35 9f 0e 00 00 	lea    0xe9f(%rip),%rsi        # 40206b <_IO_stdin_used+0x6b>
  4011cc:	bf 01 00 00 00       	mov    $0x1,%edi
  char *works = calloc(worksize, sizeof(char));
  4011d1:	49 89 c4             	mov    %rax,%r12
  4011d4:	31 c0                	xor    %eax,%eax
  4011d6:	e8 d5 fe ff ff       	call   4010b0 <__printf_chk@plt>
  int * readcursors = calloc(threadsize, sizeof(int));
  4011db:	be 04 00 00 00       	mov    $0x4,%esi
  4011e0:	bf 0e 00 00 00       	mov    $0xe,%edi
  4011e5:	4c 8d bb 54 01 00 00 	lea    0x154(%rbx),%r15
  4011ec:	e8 af fe ff ff       	call   4010a0 <calloc@plt>
  int * writecursors = calloc(threadsize, sizeof(int));
  4011f1:	be 04 00 00 00       	mov    $0x4,%esi
  4011f6:	bf 0e 00 00 00       	mov    $0xe,%edi
  int * readcursors = calloc(threadsize, sizeof(int));
  4011fb:	48 89 c5             	mov    %rax,%rbp
  int * writecursors = calloc(threadsize, sizeof(int));
  4011fe:	e8 9d fe ff ff       	call   4010a0 <calloc@plt>
  401203:	66 48 0f 6e ed       	movq   %rbp,%xmm5
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  401208:	be 20 00 00 00       	mov    $0x20,%esi
  40120d:	bf 64 00 00 00       	mov    $0x64,%edi
  401212:	66 48 0f 6e f8       	movq   %rax,%xmm7
  401217:	48 8d 2d 5e 0e 00 00 	lea    0xe5e(%rip),%rbp        # 40207c <_IO_stdin_used+0x7c>
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
  401284:	41 8d 46 f1          	lea    -0xf(%r14),%eax
          for (int x = 0; x < threadsize; x++) {
  401288:	49 83 c6 1d          	add    $0x1d,%r14
  40128c:	49 83 c5 04          	add    $0x4,%r13
    data[chunkindex].oreadcursor = start;
  401290:	41 89 87 6c fe ff ff 	mov    %eax,-0x194(%r15)
          for (int x = 0; x < threadsize; x++) {
  401297:	49 81 fe a5 01 00 00 	cmp    $0x1a5,%r14
  40129e:	75 98                	jne    401238 <main+0x148>
  4012a0:	ba 96 01 00 00       	mov    $0x196,%edx
  4012a5:	bf 01 00 00 00       	mov    $0x1,%edi
  4012aa:	31 c0                	xor    %eax,%eax
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  data[0].works = works;
  4012ac:	49 89 de             	mov    %rbx,%r14
  4012af:	48 8d 35 d2 0d 00 00 	lea    0xdd2(%rip),%rsi        # 402088 <_IO_stdin_used+0x88>
  int cpu = 0;
  4012b6:	45 31 ed             	xor    %r13d,%r13d
  4012b9:	e8 f2 fd ff ff       	call   4010b0 <__printf_chk@plt>
  4012be:	ba ff ff ff ff       	mov    $0xffffffff,%edx
  4012c3:	48 8d 35 c9 0d 00 00 	lea    0xdc9(%rip),%rsi        # 402093 <_IO_stdin_used+0x93>
  4012ca:	31 c0                	xor    %eax,%eax
  4012cc:	bf 01 00 00 00       	mov    $0x1,%edi
  4012d1:	e8 da fd ff ff       	call   4010b0 <__printf_chk@plt>
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  4012d6:	be 04 00 00 00       	mov    $0x4,%esi
  4012db:	bf 0e 00 00 00       	mov    $0xe,%edi
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
  401326:	48 8d 35 db 0d 00 00 	lea    0xddb(%rip),%rsi        # 402108 <_IO_stdin_used+0x108>
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
  40135d:	48 8b 05 cc 0d 00 00 	mov    0xdcc(%rip),%rax        # 402130 <_IO_stdin_used+0x130>
    data[x].bucketstart = x * buckets ;
  401364:	45 89 a6 00 ff ff ff 	mov    %r12d,-0x100(%r14)
    data[x].main = &data[0];
    data[x].threads = data;
    data[x].wantindex = -1;
    data[x].read = 0;
  40136b:	66 0f 6f 1d dd 0d 00 00 	movdqa 0xddd(%rip),%xmm3        # 402150 <_IO_stdin_used+0x150>
    data[x].write = worksize;
    
    data[x].freelist = freelist;
    data[x].chunksize = chunksize;
    data[x].chunkslen = chunkslen;
  401373:	66 0f 6f 25 e5 0d 00 00 	movdqa 0xde5(%rip),%xmm4        # 402160 <_IO_stdin_used+0x160>
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
  401397:	48 8b 05 9a 0d 00 00 	mov    0xd9a(%rip),%rax        # 402138 <_IO_stdin_used+0x138>
  for (int x = 0; x < threadsize ; x++) {
  40139e:	41 81 c4 92 24 49 12 	add    $0x12492492,%r12d
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
  4013ca:	48 8b 05 6f 0d 00 00 	mov    0xd6f(%rip),%rax        # 402140 <_IO_stdin_used+0x140>
    data[x].threadsize = threadsize;
  4013d1:	41 c7 86 d0 fe ff ff 0e 00 00 00 	movl   $0xe,-0x130(%r14)
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
  401422:	41 83 fd 0e          	cmp    $0xe,%r13d
  401426:	0f 85 dc fe ff ff    	jne    401308 <main+0x218>
  40142c:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
  401431:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
  401436:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  40143b:	49 89 de             	mov    %rbx,%r14
  40143e:	49 c7 c5 90 1e 40 00 	mov    $0x401e90,%r13
  401445:	48 8d 85 10 03 00 00 	lea    0x310(%rbp),%rax
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
  4014a0:	66 0f 6f 05 c8 0c 00 00 	movdqa 0xcc8(%rip),%xmm0        # 402170 <_IO_stdin_used+0x170>
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
  4014e0:	48 83 c5 70          	add    $0x70,%rbp
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
  for (int x = 0; x < threadsize ; x++) {
  401552:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401558:	49 8b 3c 24          	mov    (%r12),%rdi
  40155c:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  40155f:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  401563:	e8 78 fb ff ff       	call   4010e0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401568:	4c 39 e5             	cmp    %r12,%rbp
  40156b:	75 eb                	jne    401558 <main+0x468>
  40156d:	48 8d 3d 2b 0b 00 00 	lea    0xb2b(%rip),%rdi        # 40209f <_IO_stdin_used+0x9f>
  401574:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  401578:	45 31 e4             	xor    %r12d,%r12d
  40157b:	e8 d0 fa ff ff       	call   401050 <puts@plt>
  for (int x = 0; x < threadsize; x++) {
  401580:	4c 8d b3 08 17 00 00 	lea    0x1708(%rbx),%r14
  401587:	4c 8d 2d 2c 0b 00 00 	lea    0xb2c(%rip),%r13        # 4020ba <_IO_stdin_used+0xba>
  40158e:	66 90                	xchg   %ax,%ax
  401590:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401594:	4c 89 ee             	mov    %r13,%rsi
  401597:	bf 01 00 00 00       	mov    $0x1,%edi
  40159c:	31 c0                	xor    %eax,%eax
  40159e:	48 81 c5 a0 01 00 00 	add    $0x1a0,%rbp
  4015a5:	e8 06 fb ff ff       	call   4010b0 <__printf_chk@plt>
    printf("%ld\n", data[x].freq);
    freq += data[x].freq;
  4015aa:	4c 03 a5 60 fe ff ff 	add    -0x1a0(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  4015b1:	49 39 ee             	cmp    %rbp,%r14
  4015b4:	75 da                	jne    401590 <main+0x4a0>
  4015b6:	4c 89 e2             	mov    %r12,%rdx
  4015b9:	48 8d 35 f4 0a 00 00 	lea    0xaf4(%rip),%rsi        # 4020b4 <_IO_stdin_used+0xb4>
  4015c0:	bf 01 00 00 00       	mov    $0x1,%edi
  4015c5:	31 c0                	xor    %eax,%eax
  4015c7:	e8 e4 fa ff ff       	call   4010b0 <__printf_chk@plt>
  }
  printf("freq: %ld\n", freq/ seconds);
  long freq_writes = 0;
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  4015cc:	48 8b 93 f0 01 00 00 	mov    0x1f0(%rbx),%rdx
  4015d3:	48 8d 35 e5 0a 00 00 	lea    0xae5(%rip),%rsi        # 4020bf <_IO_stdin_used+0xbf>
  4015da:	31 c0                	xor    %eax,%eax
  4015dc:	48 03 93 90 03 00 00 	add    0x390(%rbx),%rdx
  4015e3:	bf 01 00 00 00       	mov    $0x1,%edi
  4015e8:	48 03 53 50          	add    0x50(%rbx),%rdx
  4015ec:	48 03 93 30 05 00 00 	add    0x530(%rbx),%rdx
  4015f3:	48 03 93 d0 06 00 00 	add    0x6d0(%rbx),%rdx
  4015fa:	4c 8d bb 98 01 00 00 	lea    0x198(%rbx),%r15
  401601:	48 03 93 70 08 00 00 	add    0x870(%rbx),%rdx
  401608:	48 03 93 10 0a 00 00 	add    0xa10(%rbx),%rdx
  40160f:	48 03 93 b0 0b 00 00 	add    0xbb0(%rbx),%rdx
  401616:	48 03 93 50 0d 00 00 	add    0xd50(%rbx),%rdx
  40161d:	48 03 93 f0 0e 00 00 	add    0xef0(%rbx),%rdx
  401624:	48 03 93 90 10 00 00 	add    0x1090(%rbx),%rdx
  40162b:	48 03 93 30 12 00 00 	add    0x1230(%rbx),%rdx
  401632:	48 03 93 d0 13 00 00 	add    0x13d0(%rbx),%rdx
  401639:	48 03 93 70 15 00 00 	add    0x1570(%rbx),%rdx
  401640:	e8 6b fa ff ff       	call   4010b0 <__printf_chk@plt>
  401645:	48 8d 3d 85 0a 00 00 	lea    0xa85(%rip),%rdi        # 4020d1 <_IO_stdin_used+0xd1>
  40164c:	e8 ff f9 ff ff       	call   401050 <puts@plt>
  401651:	4c 89 ee             	mov    %r13,%rsi
  401654:	bf 01 00 00 00       	mov    $0x1,%edi
  401659:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  40165b:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
  401662:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  401669:	e8 42 fa ff ff       	call   4010b0 <__printf_chk@plt>
  40166e:	4c 89 ee             	mov    %r13,%rsi
  401671:	bf 01 00 00 00       	mov    $0x1,%edi
  401676:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  401678:	48 8b 93 08 01 00 00 	mov    0x108(%rbx),%rdx
  40167f:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  401686:	e8 25 fa ff ff       	call   4010b0 <__printf_chk@plt>
  40168b:	4c 89 ee             	mov    %r13,%rsi
  40168e:	bf 01 00 00 00       	mov    $0x1,%edi
  401693:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  401695:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
  40169c:	48 2b 93 08 01 00 00 	sub    0x108(%rbx),%rdx
  4016a3:	e8 08 fa ff ff       	call   4010b0 <__printf_chk@plt>
  4016a8:	4c 89 ee             	mov    %r13,%rsi
  4016ab:	bf 01 00 00 00       	mov    $0x1,%edi
  4016b0:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4016b2:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
  4016b9:	48 2b 93 18 01 00 00 	sub    0x118(%rbx),%rdx
  4016c0:	e8 eb f9 ff ff       	call   4010b0 <__printf_chk@plt>
  4016c5:	4c 89 ee             	mov    %r13,%rsi
  4016c8:	bf 01 00 00 00       	mov    $0x1,%edi
  4016cd:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  4016cf:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
  4016d6:	48 2b 93 28 01 00 00 	sub    0x128(%rbx),%rdx
  4016dd:	e8 ce f9 ff ff       	call   4010b0 <__printf_chk@plt>
  4016e2:	4c 89 ee             	mov    %r13,%rsi
  4016e5:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ea:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  4016ec:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
  4016f3:	48 2b 93 08 01 00 00 	sub    0x108(%rbx),%rdx
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  4016fa:	45 31 f6             	xor    %r14d,%r14d
  4016fd:	48 81 c3 58 18 00 00 	add    $0x1858,%rbx
  401704:	e8 a7 f9 ff ff       	call   4010b0 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  401709:	48 8b 93 f0 e8 ff ff 	mov    -0x1710(%rbx),%rdx
  401710:	48 8d 35 c7 09 00 00 	lea    0x9c7(%rip),%rsi        # 4020de <_IO_stdin_used+0xde>
  401717:	31 c0                	xor    %eax,%eax
  401719:	48 2b 93 e0 e8 ff ff 	sub    -0x1720(%rbx),%rdx
  401720:	bf 01 00 00 00       	mov    $0x1,%edi
  401725:	e8 86 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  } 
  
  char * filename = calloc(100, sizeof(char));
  40172a:	be 01 00 00 00       	mov    $0x1,%esi
  40172f:	bf 64 00 00 00       	mov    $0x64,%edi
  401734:	e8 67 f9 ff ff       	call   4010a0 <calloc@plt>
  char * buf = calloc(1000, sizeof(char));
  401739:	be 01 00 00 00       	mov    $0x1,%esi
  40173e:	bf e8 03 00 00       	mov    $0x3e8,%edi
  char * filename = calloc(100, sizeof(char));
  401743:	48 89 c5             	mov    %rax,%rbp
  char * buf = calloc(1000, sizeof(char));
  401746:	e8 55 f9 ff ff       	call   4010a0 <calloc@plt>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  40174b:	44 8b 8b 18 e8 ff ff 	mov    -0x17e8(%rbx),%r9d
  401752:	b9 64 00 00 00       	mov    $0x64,%ecx
  401757:	48 89 ef             	mov    %rbp,%rdi
  40175a:	4c 8d 05 85 09 00 00 	lea    0x985(%rip),%r8        # 4020e6 <_IO_stdin_used+0xe6>
  401761:	ba 01 00 00 00       	mov    $0x1,%edx
  401766:	be 64 00 00 00       	mov    $0x64,%esi
  40176b:	49 89 c4             	mov    %rax,%r12
  40176e:	31 c0                	xor    %eax,%eax
  401770:	e8 bb f8 ff ff       	call   401030 <__snprintf_chk@plt>
  memset(filename, 0, 100);
  snprintf(filename, 100, "samples%d", data->threadsize);
  FILE *out_file = fopen(filename, "w");
  401775:	48 8d 35 74 09 00 00 	lea    0x974(%rip),%rsi        # 4020f0 <_IO_stdin_used+0xf0>
  40177c:	48 89 ef             	mov    %rbp,%rdi
  40177f:	e8 4c f9 ff ff       	call   4010d0 <fopen@plt>
  401784:	49 89 c5             	mov    %rax,%r13
  
  for (int x = 0; x < threadsize; x++) {
  401787:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    for (int y = 0; y < data[x].epochssize; y++) {
  401790:	41 8b 0f             	mov    (%r15),%ecx
  401793:	31 ed                	xor    %ebp,%ebp
  401795:	85 c9                	test   %ecx,%ecx
  401797:	7e 1c                	jle    4017b5 <main+0x6c5>
  401799:	49 8b 77 f8          	mov    -0x8(%r15),%rsi
      struct Epoch * epoch = &data[x].epochs[y];
  40179d:	48 63 c5             	movslq %ebp,%rax
  4017a0:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  4017a4:	48 8d 14 c6          	lea    (%rsi,%rax,8),%rdx
      if (epoch->set == 1) {
  4017a8:	83 7a 20 01          	cmpl   $0x1,0x20(%rdx)
  4017ac:	74 42                	je     4017f0 <main+0x700>
    for (int y = 0; y < data[x].epochssize; y++) {
  4017ae:	83 c5 01             	add    $0x1,%ebp
  4017b1:	39 cd                	cmp    %ecx,%ebp
  4017b3:	7c e8                	jl     40179d <main+0x6ad>
  for (int x = 0; x < threadsize; x++) {
  4017b5:	49 81 c7 a0 01 00 00 	add    $0x1a0,%r15
  4017bc:	4c 39 fb             	cmp    %r15,%rbx
  4017bf:	75 cf                	jne    401790 <main+0x6a0>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  
  4017c1:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  4017c6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4017cf:	0f 85 8d 00 00 00    	jne    401862 <main+0x772>
  4017d5:	48 83 c4 78          	add    $0x78,%rsp
  4017d9:	31 c0                	xor    %eax,%eax
  4017db:	5b                   	pop    %rbx
  4017dc:	5d                   	pop    %rbp
  4017dd:	41 5c                	pop    %r12
  4017df:	41 5d                	pop    %r13
  4017e1:	41 5e                	pop    %r14
  4017e3:	41 5f                	pop    %r15
  4017e5:	c3                   	ret
  4017e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4017f0:	4c 89 f0             	mov    %r14,%rax
  4017f3:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  4017f8:	4c 89 e7             	mov    %r12,%rdi
  4017fb:	be 64 00 00 00       	mov    $0x64,%esi
  401800:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  401803:	4c 8d 05 e8 08 00 00 	lea    0x8e8(%rip),%r8        # 4020f2 <_IO_stdin_used+0xf2>
  40180a:	4c 89 e7             	mov    %r12,%rdi
    for (int y = 0; y < data[x].epochssize; y++) {
  40180d:	83 c5 01             	add    $0x1,%ebp
  401810:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401815:	8b 02                	mov    (%rdx),%eax
  401817:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
  40181b:	50                   	push   %rax
  40181c:	8b 42 18             	mov    0x18(%rdx),%eax
  40181f:	50                   	push   %rax
  401820:	8b 42 1c             	mov    0x1c(%rdx),%eax
  401823:	50                   	push   %rax
  401824:	31 c0                	xor    %eax,%eax
  401826:	ff 72 10             	push   0x10(%rdx)
  401829:	ba 01 00 00 00       	mov    $0x1,%edx
  40182e:	e8 fd f7 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401833:	48 83 c4 20          	add    $0x20,%rsp
  401837:	4c 89 ee             	mov    %r13,%rsi
  40183a:	4c 89 e7             	mov    %r12,%rdi
  40183d:	e8 4e f8 ff ff       	call   401090 <fputs@plt>
  401842:	41 8b 0f             	mov    (%r15),%ecx
  401845:	39 cd                	cmp    %ecx,%ebp
  401847:	0f 8c 4c ff ff ff    	jl     401799 <main+0x6a9>
  for (int x = 0; x < threadsize; x++) {
  40184d:	49 81 c7 a0 01 00 00 	add    $0x1a0,%r15
  401854:	4c 39 fb             	cmp    %r15,%rbx
  401857:	0f 85 33 ff ff ff    	jne    401790 <main+0x6a0>
  40185d:	e9 5f ff ff ff       	jmp    4017c1 <main+0x6d1>
  401862:	e8 09 f8 ff ff       	call   401070 <__stack_chk_fail@plt>
  401867:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000401870 <_start>:
  401870:	f3 0f 1e fa          	endbr64
  401874:	31 ed                	xor    %ebp,%ebp
  401876:	49 89 d1             	mov    %rdx,%r9
  401879:	5e                   	pop    %rsi
  40187a:	48 89 e2             	mov    %rsp,%rdx
  40187d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401881:	50                   	push   %rax
  401882:	54                   	push   %rsp
  401883:	45 31 c0             	xor    %r8d,%r8d
  401886:	31 c9                	xor    %ecx,%ecx
  401888:	48 c7 c7 f0 10 40 00 	mov    $0x4010f0,%rdi
  40188f:	ff 15 5b 27 00 00    	call   *0x275b(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  401895:	f4                   	hlt
  401896:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004018a0 <_dl_relocate_static_pie>:
  4018a0:	f3 0f 1e fa          	endbr64
  4018a4:	c3                   	ret
  4018a5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4018af:	90                   	nop

00000000004018b0 <deregister_tm_clones>:
  4018b0:	b8 10 40 40 00       	mov    $0x404010,%eax
  4018b5:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  4018bb:	74 13                	je     4018d0 <deregister_tm_clones+0x20>
  4018bd:	b8 00 00 00 00       	mov    $0x0,%eax
  4018c2:	48 85 c0             	test   %rax,%rax
  4018c5:	74 09                	je     4018d0 <deregister_tm_clones+0x20>
  4018c7:	bf 10 40 40 00       	mov    $0x404010,%edi
  4018cc:	ff e0                	jmp    *%rax
  4018ce:	66 90                	xchg   %ax,%ax
  4018d0:	c3                   	ret
  4018d1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4018dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004018e0 <register_tm_clones>:
  4018e0:	be 10 40 40 00       	mov    $0x404010,%esi
  4018e5:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  4018ec:	48 89 f0             	mov    %rsi,%rax
  4018ef:	48 c1 ee 3f          	shr    $0x3f,%rsi
  4018f3:	48 c1 f8 03          	sar    $0x3,%rax
  4018f7:	48 01 c6             	add    %rax,%rsi
  4018fa:	48 d1 fe             	sar    %rsi
  4018fd:	74 11                	je     401910 <register_tm_clones+0x30>
  4018ff:	b8 00 00 00 00       	mov    $0x0,%eax
  401904:	48 85 c0             	test   %rax,%rax
  401907:	74 07                	je     401910 <register_tm_clones+0x30>
  401909:	bf 10 40 40 00       	mov    $0x404010,%edi
  40190e:	ff e0                	jmp    *%rax
  401910:	c3                   	ret
  401911:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40191c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401920 <__do_global_dtors_aux>:
  401920:	f3 0f 1e fa          	endbr64
  401924:	80 3d e5 26 00 00 00 	cmpb   $0x0,0x26e5(%rip)        # 404010 <__TMC_END__>
  40192b:	75 13                	jne    401940 <__do_global_dtors_aux+0x20>
  40192d:	55                   	push   %rbp
  40192e:	48 89 e5             	mov    %rsp,%rbp
  401931:	e8 7a ff ff ff       	call   4018b0 <deregister_tm_clones>
  401936:	c6 05 d3 26 00 00 01 	movb   $0x1,0x26d3(%rip)        # 404010 <__TMC_END__>
  40193d:	5d                   	pop    %rbp
  40193e:	c3                   	ret
  40193f:	90                   	nop
  401940:	c3                   	ret
  401941:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40194c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401950 <frame_dummy>:
  401950:	f3 0f 1e fa          	endbr64
  401954:	eb 8a                	jmp    4018e0 <register_tm_clones>
  401956:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401960 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  401960:	83 7f 70 01          	cmpl   $0x1,0x70(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  401964:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  401967:	7e 77                	jle    4019e0 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  401969:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  40196d:	55                   	push   %rbp
  40196e:	49 89 f2             	mov    %rsi,%r10
  401971:	49 89 d3             	mov    %rdx,%r11
  401974:	53                   	push   %rbx
  401975:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  401978:	48 8b 98 c0 01 00 00 	mov    0x1c0(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  40197f:	b8 01 00 00 00       	mov    $0x1,%eax
  401984:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  401988:	48 63 d0             	movslq %eax,%rdx
  40198b:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  40198e:	85 d2                	test   %edx,%edx
  401990:	40 0f 94 c6          	sete   %sil
  401994:	f6 c2 04             	test   $0x4,%dl
  401997:	75 05                	jne    40199e <pollthreads+0x3e>
  401999:	40 84 f6             	test   %sil,%sil
  40199c:	74 0d                	je     4019ab <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  40199e:	49 63 08             	movslq (%r8),%rcx
  4019a1:	8d 69 01             	lea    0x1(%rcx),%ebp
  4019a4:	41 89 28             	mov    %ebp,(%r8)
  4019a7:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  4019ab:	83 e2 08             	and    $0x8,%edx
  4019ae:	75 05                	jne    4019b5 <pollthreads+0x55>
  4019b0:	40 84 f6             	test   %sil,%sil
  4019b3:	74 1b                	je     4019d0 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  4019b5:	48 63 17             	movslq (%rdi),%rdx
  4019b8:	8d 4a 01             	lea    0x1(%rdx),%ecx
  4019bb:	89 0f                	mov    %ecx,(%rdi)
  4019bd:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  4019c1:	83 c0 01             	add    $0x1,%eax
  4019c4:	41 39 41 70          	cmp    %eax,0x70(%r9)
  4019c8:	7f be                	jg     401988 <pollthreads+0x28>
}
  4019ca:	31 c0                	xor    %eax,%eax
  4019cc:	5b                   	pop    %rbx
  4019cd:	5d                   	pop    %rbp
  4019ce:	c3                   	ret
  4019cf:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  4019d0:	83 c0 01             	add    $0x1,%eax
  4019d3:	41 39 41 70          	cmp    %eax,0x70(%r9)
  4019d7:	7f af                	jg     401988 <pollthreads+0x28>
}
  4019d9:	31 c0                	xor    %eax,%eax
  4019db:	5b                   	pop    %rbx
  4019dc:	5d                   	pop    %rbp
  4019dd:	c3                   	ret
  4019de:	66 90                	xchg   %ax,%ax
  4019e0:	31 c0                	xor    %eax,%eax
  4019e2:	c3                   	ret
  4019e3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4019ee:	66 90                	xchg   %ax,%ax

00000000004019f0 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  4019f0:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4019f3:	48 8b bf c0 00 00 00 	mov    0xc0(%rdi),%rdi
      if (*availableidx == 0) {
  4019fa:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4019fd:	48 83 c7 01          	add    $0x1,%rdi
  401a01:	48 85 ff             	test   %rdi,%rdi
  401a04:	7e 66                	jle    401a6c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401a06:	4d 8b 93 a8 00 00 00 	mov    0xa8(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a0d:	31 c9                	xor    %ecx,%ecx
  401a0f:	45 31 c9             	xor    %r9d,%r9d
  401a12:	31 c0                	xor    %eax,%eax
  401a14:	eb 18                	jmp    401a2e <findavailable+0x3e>
  401a16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401a20:	83 c1 01             	add    $0x1,%ecx
  401a23:	48 63 c1             	movslq %ecx,%rax
  401a26:	49 89 c1             	mov    %rax,%r9
  401a29:	48 39 f8             	cmp    %rdi,%rax
  401a2c:	7d 3e                	jge    401a6c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401a2e:	48 c1 e0 05          	shl    $0x5,%rax
  401a32:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401a38:	75 e6                	jne    401a20 <findavailable+0x30>
         available[*availableidx] = x;
  401a3a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  401a3d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401a41:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401a45:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401a48:	41 8b 43 70          	mov    0x70(%r11),%eax
  401a4c:	01 c0                	add    %eax,%eax
  401a4e:	41 39 c0             	cmp    %eax,%r8d
  401a51:	74 19                	je     401a6c <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a53:	49 8b bb c0 00 00 00 	mov    0xc0(%r11),%rdi
  401a5a:	83 c1 01             	add    $0x1,%ecx
  401a5d:	48 63 c1             	movslq %ecx,%rax
  401a60:	48 83 c7 01          	add    $0x1,%rdi
  401a64:	49 89 c1             	mov    %rax,%r9
  401a67:	48 39 f8             	cmp    %rdi,%rax
  401a6a:	7c c2                	jl     401a2e <findavailable+0x3e>
      if (*availableidx == 0) {
  401a6c:	31 c0                	xor    %eax,%eax
  401a6e:	45 85 c0             	test   %r8d,%r8d
  401a71:	0f 94 c0             	sete   %al
}
  401a74:	c3                   	ret
  401a75:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401a80 <singlewriter2>:
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a80:	41 54                	push   %r12
  401a82:	55                   	push   %rbp
  401a83:	53                   	push   %rbx
  if ((data->readcursor % data->threadsize) == 0) {
  401a84:	8b 87 58 01 00 00    	mov    0x158(%rdi),%eax
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a8a:	48 89 fb             	mov    %rdi,%rbx
  if ((data->readcursor % data->threadsize) == 0) {
  401a8d:	8b 4f 70             	mov    0x70(%rdi),%ecx
  401a90:	99                   	cltd
  401a91:	f7 f9                	idiv   %ecx
  401a93:	85 d2                	test   %edx,%edx
  401a95:	74 29                	je     401ac0 <singlewriter2+0x40>
  if ((data->writecursor % data->threadsize) == 0) {
  401a97:	8b 83 50 01 00 00    	mov    0x150(%rbx),%eax
  401a9d:	99                   	cltd
  401a9e:	f7 f9                	idiv   %ecx
  401aa0:	85 d2                	test   %edx,%edx
  401aa2:	75 11                	jne    401ab5 <singlewriter2+0x35>
    data->currentwrite++;
  401aa4:	83 83 84 01 00 00 01 	addl   $0x1,0x184(%rbx)
    data->writecursor = 0;
  401aab:	c7 83 50 01 00 00 00 00 00 00 	movl   $0x0,0x150(%rbx)
}
  401ab5:	5b                   	pop    %rbx
  401ab6:	5d                   	pop    %rbp
  401ab7:	41 5c                	pop    %r12
  401ab9:	c3                   	ret
  401aba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        struct Data * thread = &data->threads[data->threadindex];
  401ac0:	48 63 47 6c          	movslq 0x6c(%rdi),%rax
    data->currentread++;
  401ac4:	83 87 80 01 00 00 01 	addl   $0x1,0x180(%rdi)
    data->readcursor = 0;
  401acb:	c7 87 58 01 00 00 00 00 00 00 	movl   $0x0,0x158(%rdi)
        struct Data * thread = &data->threads[data->threadindex];
  401ad5:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  401ad9:	48 8d 2c 90          	lea    (%rax,%rdx,4),%rbp
  401add:	48 c1 e5 05          	shl    $0x5,%rbp
  401ae1:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401ae5:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401aea:	48 63 85 9c 01 00 00 	movslq 0x19c(%rbp),%rax
  401af1:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  401af5:	48 8b 85 90 01 00 00 	mov    0x190(%rbp),%rax
  401afc:	4c 8d 24 d0          	lea    (%rax,%rdx,8),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401b00:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401b05:	e8 56 f5 ff ff       	call   401060 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401b0a:	8b 85 9c 01 00 00    	mov    0x19c(%rbp),%eax
  401b10:	83 c0 01             	add    $0x1,%eax
  401b13:	99                   	cltd
  401b14:	f7 bd 98 01 00 00    	idivl  0x198(%rbp)
        epoch->thread = data->threadindex;
  401b1a:	8b 43 6c             	mov    0x6c(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401b1d:	89 95 9c 01 00 00    	mov    %edx,0x19c(%rbp)
        epoch->thread = data->threadindex;
  401b23:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401b27:	48 8b 05 fa 05 00 00 	mov    0x5fa(%rip),%rax        # 402128 <_IO_stdin_used+0x128>
  401b2e:	49 89 44 24 1c       	mov    %rax,0x1c(%r12)
  if ((data->writecursor % data->threadsize) == 0) {
  401b33:	8b 4b 70             	mov    0x70(%rbx),%ecx
  401b36:	e9 5c ff ff ff       	jmp    401a97 <singlewriter2+0x17>
  401b3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000401b40 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b40:	41 55                	push   %r13
  401b42:	49 89 d5             	mov    %rdx,%r13
  401b45:	41 54                	push   %r12
  401b47:	49 89 cc             	mov    %rcx,%r12
  401b4a:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401b4b:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b4e:	48 89 fd             	mov    %rdi,%rbp
  401b51:	53                   	push   %rbx
  401b52:	48 89 f3             	mov    %rsi,%rbx
  401b55:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401b59:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b5d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401b66:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401b6b:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401b6d:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401b75:	8b 81 64 01 00 00    	mov    0x164(%rcx),%eax
  int writers = 0;
  401b7b:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401b83:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401b8b:	83 c0 01             	add    $0x1,%eax
  401b8e:	99                   	cltd
  401b8f:	f7 7f 70             	idivl  0x70(%rdi)
  401b92:	89 91 64 01 00 00    	mov    %edx,0x164(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401b98:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401b9d:	4c 89 e9             	mov    %r13,%rcx
  401ba0:	e8 4b fe ff ff       	call   4019f0 <findavailable>
  if (fill == 1) {
  401ba5:	83 f8 01             	cmp    $0x1,%eax
  401ba8:	0f 84 59 01 00 00    	je     401d07 <singlewriter+0x1c7>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401bae:	48 89 ef             	mov    %rbp,%rdi
  401bb1:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401bb6:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401bbb:	4c 89 e2             	mov    %r12,%rdx
  401bbe:	4c 89 ee             	mov    %r13,%rsi
  401bc1:	e8 9a fd ff ff       	call   401960 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401bc6:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401bcb:	85 ff                	test   %edi,%edi
  401bcd:	0f 8e 5e 01 00 00    	jle    401d31 <singlewriter+0x1f1>
  401bd3:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401bd8:	31 c9                	xor    %ecx,%ecx
  401bda:	eb 62                	jmp    401c3e <singlewriter+0xfe>
  401bdc:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401be0:	48 8b 04 cb          	mov    (%rbx,%rcx,8),%rax
          int thread = readyreaders[x];
  401be4:	49 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%rdx
  401be9:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401bec:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401bf0:	48 c1 e0 05          	shl    $0x5,%rax
  401bf4:	48 03 85 a8 00 00 00 	add    0xa8(%rbp),%rax
          data->threads[thread].reading = chunk;
  401bfb:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
          int thread = readyreaders[x];
  401bff:	49 89 d1             	mov    %rdx,%r9
          data->threads[thread].start = start;
  401c02:	66 0f 6e 00          	movd   (%rax),%xmm0
  401c06:	66 0f 6e 48 08       	movd   0x8(%rax),%xmm1
          data->threads[thread].reading = chunk;
  401c0b:	4a 8d 14 92          	lea    (%rdx,%r10,4),%rdx
          chunk->available = READING;
  401c0f:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
          data->threads[thread].reading = chunk;
  401c16:	48 c1 e2 05          	shl    $0x5,%rdx
  401c1a:	48 03 55 30          	add    0x30(%rbp),%rdx
          data->threads[thread].start = start;
  401c1e:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401c22:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
          chunk->owner = thread;
  401c29:	44 89 48 14          	mov    %r9d,0x14(%rax)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401c2d:	83 8a d0 00 00 00 10 	orl    $0x10,0xd0(%rdx)
          data->threads[thread].start = start;
  401c34:	66 0f d6 42 14       	movq   %xmm0,0x14(%rdx)
        for (int x = 0; x < readers ; x++) {
  401c39:	48 39 cf             	cmp    %rcx,%rdi
  401c3c:	74 07                	je     401c45 <singlewriter+0x105>
  401c3e:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401c40:	4c 39 c1             	cmp    %r8,%rcx
  401c43:	75 9b                	jne    401be0 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401c45:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401c4a:	45 85 c0             	test   %r8d,%r8d
  401c4d:	7e 77                	jle    401cc6 <singlewriter+0x186>
                if (assignedchunk  == availableidx) {
  401c4f:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401c53:	41 01 f0             	add    %esi,%r8d
  401c56:	eb 6a                	jmp    401cc2 <singlewriter+0x182>
  401c58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c60:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401c63:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401c66:	49 63 14 24          	movslq (%r12),%rdx
   for (int x = 0; x < writers ; x++) {
  401c6a:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c6e:	48 8b 04 f3          	mov    (%rbx,%rsi,8),%rax
          data->threads[thread].writing = chunk;
  401c72:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
          int thread = readywriters[x];
  401c76:	49 89 d1             	mov    %rdx,%r9
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c79:	48 c1 e0 05          	shl    $0x5,%rax
  401c7d:	48 03 85 a8 00 00 00 	add    0xa8(%rbp),%rax
          data->threads[thread].writing = chunk;
  401c84:	48 8d 14 b2          	lea    (%rdx,%rsi,4),%rdx
          data->threads[thread].publishstart = start;
  401c88:	66 0f 6e 00          	movd   (%rax),%xmm0
  401c8c:	66 0f 6e 50 08       	movd   0x8(%rax),%xmm2
          data->threads[thread].writing = chunk;
  401c91:	48 c1 e2 05          	shl    $0x5,%rdx
      chunk->available = WRITING;
  401c95:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
          data->threads[thread].writing = chunk;
  401c9c:	48 03 55 30          	add    0x30(%rbp),%rdx
          data->threads[thread].publishstart = start;
  401ca0:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401ca4:	48 89 82 b8 00 00 00 	mov    %rax,0xb8(%rdx)
          chunk->owner = thread;
  401cab:	44 89 48 14          	mov    %r9d,0x14(%rax)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401caf:	83 8a d0 00 00 00 20 	orl    $0x20,0xd0(%rdx)
          data->threads[thread].publishstart = start;
  401cb6:	66 0f d6 42 40       	movq   %xmm0,0x40(%rdx)
   for (int x = 0; x < writers ; x++) {
  401cbb:	44 39 c1             	cmp    %r8d,%ecx
  401cbe:	74 06                	je     401cc6 <singlewriter+0x186>
  401cc0:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401cc2:	39 f7                	cmp    %esi,%edi
  401cc4:	75 9a                	jne    401c60 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401cc6:	8b 7d 70             	mov    0x70(%rbp),%edi
  401cc9:	85 ff                	test   %edi,%edi
  401ccb:	7e 38                	jle    401d05 <singlewriter+0x1c5>
        if (data->threads[x].newmask != 0) {
  401ccd:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401cd1:	31 c9                	xor    %ecx,%ecx
  401cd3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401cd8:	48 63 d1             	movslq %ecx,%rdx
  401cdb:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
  401cdf:	48 8d 04 82          	lea    (%rdx,%rax,4),%rax
  401ce3:	48 c1 e0 05          	shl    $0x5,%rax
  401ce7:	4c 01 c0             	add    %r8,%rax
  401cea:	8b b0 d0 00 00 00    	mov    0xd0(%rax),%esi
  401cf0:	85 f6                	test   %esi,%esi
  401cf2:	74 34                	je     401d28 <singlewriter+0x1e8>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401cf4:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401cf8:	83 c1 01             	add    $0x1,%ecx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401cfb:	89 34 90             	mov    %esi,(%rax,%rdx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401cfe:	8b 7d 70             	mov    0x70(%rbp),%edi
  401d01:	39 f9                	cmp    %edi,%ecx
  401d03:	7c d3                	jl     401cd8 <singlewriter+0x198>
  return 0;
  401d05:	31 c0                	xor    %eax,%eax
}
  401d07:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401d0c:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401d15:	75 21                	jne    401d38 <singlewriter+0x1f8>
  401d17:	48 83 c4 28          	add    $0x28,%rsp
  401d1b:	5b                   	pop    %rbx
  401d1c:	5d                   	pop    %rbp
  401d1d:	41 5c                	pop    %r12
  401d1f:	41 5d                	pop    %r13
  401d21:	c3                   	ret
  401d22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      for (int x = 0; x < data->threadsize ; x++) {
  401d28:	83 c1 01             	add    $0x1,%ecx
  401d2b:	39 f9                	cmp    %edi,%ecx
  401d2d:	7c a9                	jl     401cd8 <singlewriter+0x198>
  401d2f:	eb d4                	jmp    401d05 <singlewriter+0x1c5>
      int assignedchunk = 0;
  401d31:	31 f6                	xor    %esi,%esi
  401d33:	e9 0d ff ff ff       	jmp    401c45 <singlewriter+0x105>
}
  401d38:	e8 33 f3 ff ff       	call   401070 <__stack_chk_fail@plt>
  401d3d:	0f 1f 00             	nopl   (%rax)

0000000000401d40 <threadwork>:
int * threadwork(struct Data * data) {
  401d40:	41 55                	push   %r13
  401d42:	41 54                	push   %r12
  401d44:	55                   	push   %rbp
  401d45:	53                   	push   %rbx
  401d46:	48 89 fb             	mov    %rdi,%rbx
  401d49:	48 83 ec 08          	sub    $0x8,%rsp
        long buffer = (data->threadindex << 16) | (data->main->readcursor % 0xff) << 8 | data->readcursor % 0xff;
  401d4d:	48 8b 47 28          	mov    0x28(%rdi),%rax
  401d51:	48 63 4f 6c          	movslq 0x6c(%rdi),%rcx
        data->freq++;
  401d55:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
        long buffer = (data->threadindex << 16) | (data->main->readcursor % 0xff) << 8 | data->readcursor % 0xff;
  401d5a:	48 63 80 58 01 00 00 	movslq 0x158(%rax),%rax
  401d61:	48 89 c2             	mov    %rax,%rdx
  401d64:	48 69 c0 81 80 80 80 	imul   $0xffffffff80808081,%rax,%rax
  401d6b:	89 d6                	mov    %edx,%esi
  401d6d:	c1 fe 1f             	sar    $0x1f,%esi
  401d70:	48 c1 e8 20          	shr    $0x20,%rax
  401d74:	01 d0                	add    %edx,%eax
  401d76:	c1 f8 07             	sar    $0x7,%eax
  401d79:	29 f0                	sub    %esi,%eax
  401d7b:	89 c6                	mov    %eax,%esi
  401d7d:	c1 e6 08             	shl    $0x8,%esi
  401d80:	29 c6                	sub    %eax,%esi
  401d82:	48 63 87 58 01 00 00 	movslq 0x158(%rdi),%rax
  401d89:	29 f2                	sub    %esi,%edx
  401d8b:	41 89 d4             	mov    %edx,%r12d
  401d8e:	48 89 c2             	mov    %rax,%rdx
  401d91:	48 69 c0 81 80 80 80 	imul   $0xffffffff80808081,%rax,%rax
  401d98:	89 d6                	mov    %edx,%esi
  401d9a:	41 c1 e4 08          	shl    $0x8,%r12d
  401d9e:	c1 fe 1f             	sar    $0x1f,%esi
  401da1:	48 c1 e8 20          	shr    $0x20,%rax
  401da5:	01 d0                	add    %edx,%eax
  401da7:	c1 f8 07             	sar    $0x7,%eax
  401daa:	29 f0                	sub    %esi,%eax
  401dac:	89 c6                	mov    %eax,%esi
  401dae:	c1 e6 08             	shl    $0x8,%esi
  401db1:	29 c6                	sub    %eax,%esi
  401db3:	89 c8                	mov    %ecx,%eax
  401db5:	29 f2                	sub    %esi,%edx
  401db7:	c1 e0 10             	shl    $0x10,%eax
  401dba:	09 c2                	or     %eax,%edx
        struct Data * thread = &data->threads[data->threadindex];
  401dbc:	48 8d 04 49          	lea    (%rcx,%rcx,2),%rax
  401dc0:	48 8d 2c 81          	lea    (%rcx,%rax,4),%rbp
        long buffer = (data->threadindex << 16) | (data->main->readcursor % 0xff) << 8 | data->readcursor % 0xff;
  401dc4:	41 09 d4             	or     %edx,%r12d
        struct Data * thread = &data->threads[data->threadindex];
  401dc7:	48 c1 e5 05          	shl    $0x5,%rbp
  401dcb:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401dcf:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401dd4:	48 63 85 9c 01 00 00 	movslq 0x19c(%rbp),%rax
  401ddb:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  401ddf:	48 8b 85 90 01 00 00 	mov    0x190(%rbp),%rax
  401de6:	4c 8d 2c d0          	lea    (%rax,%rdx,8),%r13
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401dea:	49 8d 75 08          	lea    0x8(%r13),%rsi
  401dee:	e8 6d f2 ff ff       	call   401060 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401df3:	8b 85 9c 01 00 00    	mov    0x19c(%rbp),%eax
  401df9:	83 c0 01             	add    $0x1,%eax
  401dfc:	99                   	cltd
  401dfd:	f7 bd 98 01 00 00    	idivl  0x198(%rbp)
        epoch->thread = data->threadindex;
  401e03:	8b 43 6c             	mov    0x6c(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e06:	89 95 9c 01 00 00    	mov    %edx,0x19c(%rbp)
        epoch->thread = data->threadindex;
  401e0c:	41 89 45 00          	mov    %eax,0x0(%r13)
        data->main->works[buffer] = 0;
  401e10:	48 8b 43 28          	mov    0x28(%rbx),%rax
  epoch->buffer = buffer;
  401e14:	45 89 65 18          	mov    %r12d,0x18(%r13)
        data->main->works[buffer] = 0;
  401e18:	4d 63 e4             	movslq %r12d,%r12
  401e1b:	48 8b 40 78          	mov    0x78(%rax),%rax
  epoch->set = 1;
  401e1f:	41 c7 45 20 01 00 00 00 	movl   $0x1,0x20(%r13)
        data->main->works[buffer] = 0;
  401e27:	42 c6 04 20 00       	movb   $0x0,(%rax,%r12,1)
          data->readcursor = (data->readcursor + 1) % 0xffffff;
  401e2c:	8b 83 58 01 00 00    	mov    0x158(%rbx),%eax
  401e32:	8d 50 01             	lea    0x1(%rax),%edx
  401e35:	48 63 c2             	movslq %edx,%rax
  401e38:	89 d1                	mov    %edx,%ecx
  401e3a:	48 69 c0 81 00 00 80 	imul   $0xffffffff80000081,%rax,%rax
  401e41:	48 c1 e8 20          	shr    $0x20,%rax
  401e45:	01 d0                	add    %edx,%eax
  401e47:	c1 f9 1f             	sar    $0x1f,%ecx
  401e4a:	c1 f8 17             	sar    $0x17,%eax
  401e4d:	29 c8                	sub    %ecx,%eax
  401e4f:	89 c1                	mov    %eax,%ecx
  401e51:	c1 e1 18             	shl    $0x18,%ecx
  401e54:	29 c1                	sub    %eax,%ecx
         __atomic_fetch_add(&data->main->readcursor, 1, __ATOMIC_ACQUIRE);
  401e56:	48 8b 43 28          	mov    0x28(%rbx),%rax
          data->readcursor = (data->readcursor + 1) % 0xffffff;
  401e5a:	29 ca                	sub    %ecx,%edx
  401e5c:	89 93 58 01 00 00    	mov    %edx,0x158(%rbx)
         __atomic_fetch_add(&data->main->readcursor, 1, __ATOMIC_ACQUIRE);
  401e62:	f0 83 80 58 01 00 00 01 	lock addl $0x1,0x158(%rax)
    data->prevread = data->main->currentread;
  401e6a:	48 8b 43 28          	mov    0x28(%rbx),%rax
  401e6e:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401e74:	89 83 88 01 00 00    	mov    %eax,0x188(%rbx)
}
  401e7a:	48 83 c4 08          	add    $0x8,%rsp
  401e7e:	5b                   	pop    %rbx
  401e7f:	5d                   	pop    %rbp
  401e80:	41 5c                	pop    %r12
  401e82:	41 5d                	pop    %r13
  401e84:	c3                   	ret
  401e85:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401e90 <work>:
void * work(void * arg) {
  401e90:	41 56                	push   %r14
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  401e92:	48 8d 35 6b 01 00 00 	lea    0x16b(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  401e99:	31 c0                	xor    %eax,%eax
  401e9b:	41 55                	push   %r13
  401e9d:	41 54                	push   %r12
  401e9f:	55                   	push   %rbp
  401ea0:	53                   	push   %rbx
  401ea1:	8b 57 6c             	mov    0x6c(%rdi),%edx
  401ea4:	48 89 fb             	mov    %rdi,%rbx
  401ea7:	bf 01 00 00 00       	mov    $0x1,%edi
  401eac:	e8 ff f1 ff ff       	call   4010b0 <__printf_chk@plt>
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  401eb1:	8b 43 6c             	mov    0x6c(%rbx),%eax
  401eb4:	48 8d 35 5c 01 00 00 	lea    0x15c(%rip),%rsi        # 402017 <_IO_stdin_used+0x17>
  401ebb:	bf 01 00 00 00       	mov    $0x1,%edi
  int bucketstart = data->bucketstart;
  401ec0:	44 8b b3 a0 00 00 00 	mov    0xa0(%rbx),%r14d
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  401ec7:	8d 50 01             	lea    0x1(%rax),%edx
  401eca:	31 c0                	xor    %eax,%eax
  int bucketlim = ((data->threadindex + 1) * data->buckets) ;
  401ecc:	0f af 93 98 00 00 00 	imul   0x98(%rbx),%edx
  401ed3:	e8 d8 f1 ff ff       	call   4010b0 <__printf_chk@plt>
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  401ed8:	48 8b 83 c0 00 00 00 	mov    0xc0(%rbx),%rax
  401edf:	be 08 00 00 00       	mov    $0x8,%esi
  401ee4:	48 8d 78 01          	lea    0x1(%rax),%rdi
  401ee8:	e8 b3 f1 ff ff       	call   4010a0 <calloc@plt>
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  401eed:	4c 63 6b 70          	movslq 0x70(%rbx),%r13
  401ef1:	be 04 00 00 00       	mov    $0x4,%esi
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  401ef6:	48 89 c5             	mov    %rax,%rbp
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  401ef9:	4c 89 ef             	mov    %r13,%rdi
  401efc:	e8 9f f1 ff ff       	call   4010a0 <calloc@plt>
  int * readywriters = calloc(data->threadsize, sizeof(int));
  401f01:	be 04 00 00 00       	mov    $0x4,%esi
  401f06:	4c 89 ef             	mov    %r13,%rdi
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  401f09:	49 89 c4             	mov    %rax,%r12
  int * readywriters = calloc(data->threadsize, sizeof(int));
  401f0c:	e8 8f f1 ff ff       	call   4010a0 <calloc@plt>
  while (data->running == 1) {
  401f11:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  data->workindex = bucketstart;
  401f15:	44 89 73 5c          	mov    %r14d,0x5c(%rbx)
  while (data->running == 1) {
  401f19:	75 49                	jne    401f64 <work+0xd4>
  401f1b:	49 89 c5             	mov    %rax,%r13
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  401f1e:	4c 8d b3 30 01 00 00 	lea    0x130(%rbx),%r14
  401f25:	0f 1f 00             	nopl   (%rax)
    if (data->threadindex == 0) {
  401f28:	8b 43 6c             	mov    0x6c(%rbx),%eax
  401f2b:	85 c0                	test   %eax,%eax
  401f2d:	75 59                	jne    401f88 <work+0xf8>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  401f2f:	4c 89 f6             	mov    %r14,%rsi
  401f32:	bf 04 00 00 00       	mov    $0x4,%edi
  401f37:	e8 24 f1 ff ff       	call   401060 <clock_gettime@plt>
      singlewriter2(data, available, readyreaders, readywriters);
  401f3c:	4c 89 e9             	mov    %r13,%rcx
  401f3f:	4c 89 e2             	mov    %r12,%rdx
  401f42:	48 89 ee             	mov    %rbp,%rsi
  401f45:	48 89 df             	mov    %rbx,%rdi
  401f48:	e8 33 fb ff ff       	call   401a80 <singlewriter2>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swend);
  401f4d:	48 8d b3 40 01 00 00 	lea    0x140(%rbx),%rsi
  401f54:	bf 04 00 00 00       	mov    $0x4,%edi
  401f59:	e8 02 f1 ff ff       	call   401060 <clock_gettime@plt>
  while (data->running == 1) {
  401f5e:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  401f62:	74 c4                	je     401f28 <work+0x98>
  401f64:	8b 53 6c             	mov    0x6c(%rbx),%edx
  401f67:	48 8d 35 b7 00 00 00 	lea    0xb7(%rip),%rsi        # 402025 <_IO_stdin_used+0x25>
  401f6e:	bf 01 00 00 00       	mov    $0x1,%edi
  401f73:	31 c0                	xor    %eax,%eax
  401f75:	e8 36 f1 ff ff       	call   4010b0 <__printf_chk@plt>
}
  401f7a:	5b                   	pop    %rbx
  401f7b:	5d                   	pop    %rbp
  401f7c:	41 5c                	pop    %r12
  401f7e:	41 5d                	pop    %r13
  401f80:	41 5e                	pop    %r14
  401f82:	c3                   	ret
  401f83:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      threadwork(data);
  401f88:	48 89 df             	mov    %rbx,%rdi
  401f8b:	e8 b0 fd ff ff       	call   401d40 <threadwork>
  while (data->running == 1) {
  401f90:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  401f94:	74 92                	je     401f28 <work+0x98>
  401f96:	eb cc                	jmp    401f64 <work+0xd4>
  401f98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000401fa0 <work2>:
  while (data->running == 1) {
  401fa0:	eb 0b                	jmp    401fad <work2+0xd>
  401fa2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  401fa8:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  401fad:	83 7f 64 01          	cmpl   $0x1,0x64(%rdi)
  401fb1:	74 f5                	je     401fa8 <work2+0x8>
}
  401fb3:	c3                   	ret

Disassembly of section .fini:

0000000000401fb4 <_fini>:
  401fb4:	f3 0f 1e fa          	endbr64
  401fb8:	48 83 ec 08          	sub    $0x8,%rsp
  401fbc:	48 83 c4 08          	add    $0x8,%rsp
  401fc0:	c3                   	ret
