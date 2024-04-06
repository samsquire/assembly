
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

0000000000401020 <pthread_setaffinity_np@plt-0x10>:
  401020:	ff 35 72 3f 00 00    	push   0x3f72(%rip)        # 404f98 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 74 3f 00 00    	jmp    *0x3f74(%rip)        # 404fa0 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <pthread_setaffinity_np@plt>:
  401030:	ff 25 72 3f 00 00    	jmp    *0x3f72(%rip)        # 404fa8 <pthread_setaffinity_np@GLIBC_2.34>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <puts@plt>:
  401040:	ff 25 6a 3f 00 00    	jmp    *0x3f6a(%rip)        # 404fb0 <puts@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <clock_gettime@plt>:
  401050:	ff 25 62 3f 00 00    	jmp    *0x3f62(%rip)        # 404fb8 <clock_gettime@GLIBC_2.17>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <__stack_chk_fail@plt>:
  401060:	ff 25 5a 3f 00 00    	jmp    *0x3f5a(%rip)        # 404fc0 <__stack_chk_fail@GLIBC_2.4>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <nanosleep@plt>:
  401070:	ff 25 52 3f 00 00    	jmp    *0x3f52(%rip)        # 404fc8 <nanosleep@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <calloc@plt>:
  401080:	ff 25 4a 3f 00 00    	jmp    *0x3f4a(%rip)        # 404fd0 <calloc@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <__printf_chk@plt>:
  401090:	ff 25 42 3f 00 00    	jmp    *0x3f42(%rip)        # 404fd8 <__printf_chk@GLIBC_2.3.4>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <pthread_create@plt>:
  4010a0:	ff 25 3a 3f 00 00    	jmp    *0x3f3a(%rip)        # 404fe0 <pthread_create@GLIBC_2.34>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <pthread_join@plt>:
  4010b0:	ff 25 32 3f 00 00    	jmp    *0x3f32(%rip)        # 404fe8 <pthread_join@GLIBC_2.34>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

00000000004010c0 <main>:
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
}

int main(int argc, char **argv) {
  4010c0:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4010c2:	ba 08 00 00 00       	mov    $0x8,%edx
  4010c7:	bf 01 00 00 00       	mov    $0x1,%edi
  4010cc:	48 8d 35 62 1f 00 00 	lea    0x1f62(%rip),%rsi        # 403035 <_IO_stdin_used+0x35>
  4010d3:	41 56                	push   %r14
  char *works = calloc(worksize, sizeof(char));
  printf("Buffer size %ld\n", worksize);
  int chunkindex = 0;
  int * readcursors = calloc(threadsize, sizeof(int));
  int * writecursors = calloc(threadsize, sizeof(int));
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4010d5:	41 be 11 00 00 00    	mov    $0x11,%r14d
int main(int argc, char **argv) {
  4010db:	41 55                	push   %r13
  char *works = calloc(worksize, sizeof(char));
  4010dd:	41 bd ff ff ff ff    	mov    $0xffffffff,%r13d
int main(int argc, char **argv) {
  4010e3:	41 54                	push   %r12
  4010e5:	55                   	push   %rbp
  4010e6:	53                   	push   %rbx
  4010e7:	48 83 ec 78          	sub    $0x78,%rsp
  4010eb:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4010f4:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  4010f9:	31 c0                	xor    %eax,%eax
  4010fb:	e8 90 ff ff ff       	call   401090 <__printf_chk@plt>
  401100:	ba 04 00 00 00       	mov    $0x4,%edx
  401105:	48 8d 35 3b 1f 00 00 	lea    0x1f3b(%rip),%rsi        # 403047 <_IO_stdin_used+0x47>
  40110c:	31 c0                	xor    %eax,%eax
  40110e:	bf 01 00 00 00       	mov    $0x1,%edi
  401113:	e8 78 ff ff ff       	call   401090 <__printf_chk@plt>
  401118:	ba 20 00 00 00       	mov    $0x20,%edx
  40111d:	48 8d 35 1f 1f 00 00 	lea    0x1f1f(%rip),%rsi        # 403043 <_IO_stdin_used+0x43>
  401124:	31 c0                	xor    %eax,%eax
  401126:	bf 01 00 00 00       	mov    $0x1,%edi
  40112b:	e8 60 ff ff ff       	call   401090 <__printf_chk@plt>
  401130:	ba 10 00 00 00       	mov    $0x10,%edx
  401135:	48 8d 35 1a 1f 00 00 	lea    0x1f1a(%rip),%rsi        # 403056 <_IO_stdin_used+0x56>
  40113c:	31 c0                	xor    %eax,%eax
  40113e:	bf 01 00 00 00       	mov    $0x1,%edi
  401143:	e8 48 ff ff ff       	call   401090 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401148:	be 08 00 00 00       	mov    $0x8,%esi
  40114d:	bf 10 00 00 00       	mov    $0x10,%edi
  401152:	e8 29 ff ff ff       	call   401080 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401157:	be 38 00 00 00       	mov    $0x38,%esi
  40115c:	bf 10 00 00 00       	mov    $0x10,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401161:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401166:	e8 15 ff ff ff       	call   401080 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40116b:	be 00 1a 00 00       	mov    $0x1a00,%esi
  401170:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401175:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40117a:	e8 01 ff ff ff       	call   401080 <calloc@plt>
  char *works = calloc(worksize, sizeof(char));
  40117f:	4c 89 ef             	mov    %r13,%rdi
  401182:	be 01 00 00 00       	mov    $0x1,%esi
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401187:	48 89 c3             	mov    %rax,%rbx
  char *works = calloc(worksize, sizeof(char));
  40118a:	e8 f1 fe ff ff       	call   401080 <calloc@plt>
  40118f:	4c 89 ea             	mov    %r13,%rdx
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  401192:	45 31 ed             	xor    %r13d,%r13d
  401195:	48 8d 35 cf 1e 00 00 	lea    0x1ecf(%rip),%rsi        # 40306b <_IO_stdin_used+0x6b>
  40119c:	bf 01 00 00 00       	mov    $0x1,%edi
  char *works = calloc(worksize, sizeof(char));
  4011a1:	49 89 c4             	mov    %rax,%r12
  4011a4:	31 c0                	xor    %eax,%eax
  4011a6:	e8 e5 fe ff ff       	call   401090 <__printf_chk@plt>
  int * readcursors = calloc(threadsize, sizeof(int));
  4011ab:	be 04 00 00 00       	mov    $0x4,%esi
  4011b0:	bf 10 00 00 00       	mov    $0x10,%edi
  4011b5:	4c 8d bb 54 01 00 00 	lea    0x154(%rbx),%r15
  4011bc:	e8 bf fe ff ff       	call   401080 <calloc@plt>
  int * writecursors = calloc(threadsize, sizeof(int));
  4011c1:	be 04 00 00 00       	mov    $0x4,%esi
  4011c6:	bf 10 00 00 00       	mov    $0x10,%edi
  int * readcursors = calloc(threadsize, sizeof(int));
  4011cb:	48 89 c5             	mov    %rax,%rbp
  int * writecursors = calloc(threadsize, sizeof(int));
  4011ce:	e8 ad fe ff ff       	call   401080 <calloc@plt>
  4011d3:	66 48 0f 6e ed       	movq   %rbp,%xmm5
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4011d8:	be 20 00 00 00       	mov    $0x20,%esi
  4011dd:	bf 64 00 00 00       	mov    $0x64,%edi
  4011e2:	66 48 0f 6e f8       	movq   %rax,%xmm7
  4011e7:	48 8d 2d 8e 1e 00 00 	lea    0x1e8e(%rip),%rbp        # 40307c <_IO_stdin_used+0x7c>
  4011ee:	66 0f 6c ef          	punpcklqdq %xmm7,%xmm5
  4011f2:	0f 29 6c 24 10       	movaps %xmm5,0x10(%rsp)
  4011f7:	e8 84 fe ff ff       	call   401080 <calloc@plt>
  4011fc:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
          for (int x = 0; x < threadsize; x++) {
  401201:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          offset += (threadsize * 2) + 1;
        
     data[chunkindex].writecursors = writecursors;
     data[chunkindex].readcursors = readcursors;
            
    data[chunkindex].owritecursor = middle + 1;
  401208:	41 8d 46 01          	lea    0x1(%r14),%eax
     data[chunkindex].readcursors = readcursors;
  40120c:	66 0f 6f 4c 24 10    	movdqa 0x10(%rsp),%xmm1
  401212:	4c 89 f2             	mov    %r14,%rdx
  401215:	48 89 ee             	mov    %rbp,%rsi
    data[chunkindex].owritecursor = middle + 1;
  401218:	41 89 47 08          	mov    %eax,0x8(%r15)
  40121c:	bf 01 00 00 00       	mov    $0x1,%edi
  401221:	31 c0                	xor    %eax,%eax
          for (int x = 0; x < threadsize; x++) {
  401223:	49 81 c7 a0 01 00 00 	add    $0x1a0,%r15
     data[chunkindex].readcursors = readcursors;
  40122a:	41 0f 11 8f 7c fe ff ff 	movups %xmm1,-0x184(%r15)
  401232:	e8 59 fe ff ff       	call   401090 <__printf_chk@plt>
    printf("middle %ld\n", middle);
    data[chunkindex].middle = middle;
    data[chunkindex].readcursors[chunkindex] = middle;
  401237:	49 8b 87 7c fe ff ff 	mov    -0x184(%r15),%rax
    data[chunkindex].middle = middle;
  40123e:	45 89 b7 60 fe ff ff 	mov    %r14d,-0x1a0(%r15)
    data[chunkindex].readcursors[chunkindex] = middle;
  401245:	46 89 34 28          	mov    %r14d,(%rax,%r13,1)
    data[chunkindex].writecursors[chunkindex] = middle;
  401249:	49 8b 87 84 fe ff ff 	mov    -0x17c(%r15),%rax
  401250:	46 89 34 28          	mov    %r14d,(%rax,%r13,1)
    data[chunkindex].oreadcursor = start;
  401254:	41 8d 46 ef          	lea    -0x11(%r14),%eax
          for (int x = 0; x < threadsize; x++) {
  401258:	49 83 c6 21          	add    $0x21,%r14
  40125c:	49 83 c5 04          	add    $0x4,%r13
    data[chunkindex].oreadcursor = start;
  401260:	41 89 87 6c fe ff ff 	mov    %eax,-0x194(%r15)
          for (int x = 0; x < threadsize; x++) {
  401267:	49 81 fe 21 02 00 00 	cmp    $0x221,%r14
  40126e:	75 98                	jne    401208 <main+0x148>
  401270:	ba 10 02 00 00       	mov    $0x210,%edx
  401275:	bf 01 00 00 00       	mov    $0x1,%edi
  40127a:	31 c0                	xor    %eax,%eax
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  data[0].works = works;
  40127c:	49 89 de             	mov    %rbx,%r14
  40127f:	48 8d 35 02 1e 00 00 	lea    0x1e02(%rip),%rsi        # 403088 <_IO_stdin_used+0x88>
  int cpu = 0;
  401286:	45 31 ed             	xor    %r13d,%r13d
  401289:	e8 02 fe ff ff       	call   401090 <__printf_chk@plt>
  40128e:	ba ff ff ff ff       	mov    $0xffffffff,%edx
  401293:	48 8d 35 f9 1d 00 00 	lea    0x1df9(%rip),%rsi        # 403093 <_IO_stdin_used+0x93>
  40129a:	31 c0                	xor    %eax,%eax
  40129c:	bf 01 00 00 00       	mov    $0x1,%edi
  4012a1:	e8 ea fd ff ff       	call   401090 <__printf_chk@plt>
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  4012a6:	be 04 00 00 00       	mov    $0x4,%esi
  4012ab:	bf 10 00 00 00       	mov    $0x10,%edi
  4012b0:	e8 cb fd ff ff       	call   401080 <calloc@plt>
  4012b5:	66 48 0f 6e fb       	movq   %rbx,%xmm7
  data[0].works = works;
  4012ba:	4c 89 63 78          	mov    %r12,0x78(%rbx)
  4012be:	45 31 e4             	xor    %r12d,%r12d
  4012c1:	66 48 0f 6e f0       	movq   %rax,%xmm6
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  4012c6:	48 89 c5             	mov    %rax,%rbp
  4012c9:	66 0f 6c f7          	punpcklqdq %xmm7,%xmm6
  4012cd:	0f 29 74 24 10       	movaps %xmm6,0x10(%rsp)
  for (int x = 0; x < threadsize ; x++) {
  4012d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4012d8:	45 89 ef             	mov    %r13d,%r15d
  4012db:	be 80 00 00 00       	mov    $0x80,%esi
  4012e0:	bf 01 00 00 00       	mov    $0x1,%edi
    CPU_SET(cpu += 1, data[x].cpu_set);
  4012e5:	41 83 c5 01          	add    $0x1,%r13d
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4012e9:	e8 92 fd ff ff       	call   401080 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  4012ee:	44 89 e9             	mov    %r13d,%ecx
  4012f1:	ba 01 00 00 00       	mov    $0x1,%edx
  4012f6:	48 8d 35 eb 1d 00 00 	lea    0x1deb(%rip),%rsi        # 4030e8 <_IO_stdin_used+0xe8>
  4012fd:	48 d3 e2             	shl    %cl,%rdx
  401300:	48 09 10             	or     %rdx,(%rax)
  401303:	44 89 e9             	mov    %r13d,%ecx
  401306:	44 89 fa             	mov    %r15d,%edx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401309:	49 89 86 80 00 00 00 	mov    %rax,0x80(%r14)
  401310:	bf 01 00 00 00       	mov    $0x1,%edi
  401315:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  401317:	48 83 c5 04          	add    $0x4,%rbp
  40131b:	49 81 c6 a0 01 00 00 	add    $0x1a0,%r14
  401322:	e8 69 fd ff ff       	call   401090 <__printf_chk@plt>
    data[x].threadindex = x;
    data[x].worksize = worksize;
    
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].readies = readies;
  401327:	66 0f 6f 54 24 10    	movdqa 0x10(%rsp),%xmm2
    data[x].readies[x] = 0;
    data[x].buckets = buckets;
  40132d:	48 8b 05 dc 1d 00 00 	mov    0x1ddc(%rip),%rax        # 403110 <_IO_stdin_used+0x110>
    data[x].bucketstart = x * buckets ;
  401334:	45 89 a6 00 ff ff ff 	mov    %r12d,-0x100(%r14)
    data[x].main = &data[0];
    data[x].threads = data;
    data[x].wantindex = -1;
    data[x].read = 0;
  40133b:	66 0f 6f 1d ed 1d 00 00 	movdqa 0x1ded(%rip),%xmm3        # 403130 <_IO_stdin_used+0x130>
    data[x].write = worksize;
    
    data[x].freelist = freelist;
    data[x].chunksize = chunksize;
    data[x].chunkslen = chunkslen;
  401343:	66 0f 6f 25 f5 1d 00 00 	movdqa 0x1df5(%rip),%xmm4        # 403140 <_IO_stdin_used+0x140>
    data[x].loglevel = debug;
  40134b:	41 c7 86 e8 fe ff ff 00 00 00 00 	movl   $0x0,-0x118(%r14)
    data[x].newmask = 0;
    data[x].prevread = -1;
    data[x].prevwrite = -1;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401356:	be 28 00 00 00       	mov    $0x28,%esi
    data[x].buckets = buckets;
  40135b:	49 89 86 f8 fe ff ff 	mov    %rax,-0x108(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401362:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].wantindex = -1;
  401367:	48 8b 05 aa 1d 00 00 	mov    0x1daa(%rip),%rax        # 403118 <_IO_stdin_used+0x118>
  for (int x = 0; x < threadsize ; x++) {
  40136e:	41 81 c4 ff ff ff 0f 	add    $0xfffffff,%r12d
    data[x].threadindex = x;
  401375:	45 89 be cc fe ff ff 	mov    %r15d,-0x134(%r14)
    data[x].wantindex = -1;
  40137c:	49 89 86 c0 fe ff ff 	mov    %rax,-0x140(%r14)
    data[x].freelist = freelist;
  401383:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    data[x].worksize = worksize;
  401388:	41 c7 86 c8 fe ff ff ff ff ff ff 	movl   $0xffffffff,-0x138(%r14)
    data[x].freelist = freelist;
  401393:	49 89 86 08 ff ff ff 	mov    %rax,-0xf8(%r14)
    data[x].prevread = -1;
  40139a:	48 8b 05 7f 1d 00 00 	mov    0x1d7f(%rip),%rax        # 403120 <_IO_stdin_used+0x120>
    data[x].threadsize = threadsize;
  4013a1:	41 c7 86 d0 fe ff ff 10 00 00 00 	movl   $0x10,-0x130(%r14)
    data[x].readies[x] = 0;
  4013ac:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
    data[x].threads = data;
  4013b3:	49 89 9e 90 fe ff ff 	mov    %rbx,-0x170(%r14)
    data[x].newmask = 0;
  4013ba:	41 c7 86 30 ff ff ff 00 00 00 00 	movl   $0x0,-0xd0(%r14)
    data[x].prevread = -1;
  4013c5:	49 89 46 e8          	mov    %rax,-0x18(%r14)
    data[x].readies = readies;
  4013c9:	41 0f 11 96 80 fe ff ff 	movups %xmm2,-0x180(%r14)
    data[x].read = 0;
  4013d1:	41 0f 11 9e 60 fe ff ff 	movups %xmm3,-0x1a0(%r14)
    data[x].chunkslen = chunkslen;
  4013d9:	41 0f 11 a6 20 ff ff ff 	movups %xmm4,-0xe0(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4013e1:	e8 9a fc ff ff       	call   401080 <calloc@plt>
    data[x].epochssize = epochs;
  4013e6:	41 c7 46 f8 80 96 98 00 	movl   $0x989680,-0x8(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4013ee:	49 89 46 f0          	mov    %rax,-0x10(%r14)
  for (int x = 0; x < threadsize ; x++) {
  4013f2:	41 83 fd 10          	cmp    $0x10,%r13d
  4013f6:	0f 85 dc fe ff ff    	jne    4012d8 <main+0x218>
  4013fc:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
  401401:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
  401406:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  40140b:	49 89 de             	mov    %rbx,%r14
  40140e:	49 c7 c5 50 1f 40 00 	mov    $0x401f50,%r13
  401415:	48 8d 8d 80 03 00 00 	lea    0x380(%rbp),%rcx
  40141c:	49 89 c4             	mov    %rax,%r12
  40141f:	48 89 c3             	mov    %rax,%rbx
  401422:	49 89 cf             	mov    %rcx,%r15
  401425:	0f 1f 00             	nopl   (%rax)
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  401428:	4c 89 f1             	mov    %r14,%rcx
  40142b:	48 89 ee             	mov    %rbp,%rsi
  40142e:	48 89 df             	mov    %rbx,%rdi
  401431:	4c 89 ea             	mov    %r13,%rdx
  401434:	e8 67 fc ff ff       	call   4010a0 <pthread_create@plt>
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401439:	48 8b 3b             	mov    (%rbx),%rdi
  for (int x = 0; x < threadsize ; x++) {
  40143c:	48 83 c5 38          	add    $0x38,%rbp
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401440:	49 8b 96 80 00 00 00 	mov    0x80(%r14),%rdx
  401447:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  40144c:	48 83 c3 08          	add    $0x8,%rbx
  401450:	49 81 c6 a0 01 00 00 	add    $0x1a0,%r14
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401457:	e8 d4 fb ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  40145c:	4c 39 fd             	cmp    %r15,%rbp
  40145f:	75 c7                	jne    401428 <main+0x368>
  }
  
  struct timespec time = {
  401461:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  401466:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  40146b:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec time = {
  401470:	66 0f 6f 05 d8 1c 00 00 	movdqa 0x1cd8(%rip),%xmm0        # 403150 <_IO_stdin_used+0x150>
  401478:	4c 8d 6c 24 38       	lea    0x38(%rsp),%r13
  40147d:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  401482:	66 0f ef c0          	pxor   %xmm0,%xmm0
  401486:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  40148b:	e8 e0 fb ff ff       	call   401070 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  401490:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
  401495:	c7 43 64 00 00 00 00 	movl   $0x0,0x64(%rbx)
  40149c:	c7 83 04 02 00 00 00 00 00 00 	movl   $0x0,0x204(%rbx)
  4014a6:	c7 83 a4 03 00 00 00 00 00 00 	movl   $0x0,0x3a4(%rbx)
  4014b0:	48 83 ed 80          	sub    $0xffffffffffffff80,%rbp
  4014b4:	c7 83 44 05 00 00 00 00 00 00 	movl   $0x0,0x544(%rbx)
  4014be:	c7 83 e4 06 00 00 00 00 00 00 	movl   $0x0,0x6e4(%rbx)
  4014c8:	c7 83 84 08 00 00 00 00 00 00 	movl   $0x0,0x884(%rbx)
  4014d2:	c7 83 24 0a 00 00 00 00 00 00 	movl   $0x0,0xa24(%rbx)
  4014dc:	c7 83 c4 0b 00 00 00 00 00 00 	movl   $0x0,0xbc4(%rbx)
  4014e6:	c7 83 64 0d 00 00 00 00 00 00 	movl   $0x0,0xd64(%rbx)
  4014f0:	c7 83 04 0f 00 00 00 00 00 00 	movl   $0x0,0xf04(%rbx)
  4014fa:	c7 83 a4 10 00 00 00 00 00 00 	movl   $0x0,0x10a4(%rbx)
  401504:	c7 83 44 12 00 00 00 00 00 00 	movl   $0x0,0x1244(%rbx)
  40150e:	c7 83 e4 13 00 00 00 00 00 00 	movl   $0x0,0x13e4(%rbx)
  401518:	c7 83 84 15 00 00 00 00 00 00 	movl   $0x0,0x1584(%rbx)
  401522:	c7 83 24 17 00 00 00 00 00 00 	movl   $0x0,0x1724(%rbx)
  40152c:	c7 83 c4 18 00 00 00 00 00 00 	movl   $0x0,0x18c4(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  401536:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401540:	49 8b 3c 24          	mov    (%r12),%rdi
  401544:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  401547:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  40154b:	e8 60 fb ff ff       	call   4010b0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401550:	4c 39 e5             	cmp    %r12,%rbp
  401553:	75 eb                	jne    401540 <main+0x480>
  401555:	48 8d 3d 43 1b 00 00 	lea    0x1b43(%rip),%rdi        # 40309f <_IO_stdin_used+0x9f>
  40155c:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  401560:	45 31 e4             	xor    %r12d,%r12d
  401563:	e8 d8 fa ff ff       	call   401040 <puts@plt>
  for (int x = 0; x < threadsize; x++) {
  401568:	4c 8d b3 48 1a 00 00 	lea    0x1a48(%rbx),%r14
  40156f:	4c 8d 2d 44 1b 00 00 	lea    0x1b44(%rip),%r13        # 4030ba <_IO_stdin_used+0xba>
  401576:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401580:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401584:	4c 89 ee             	mov    %r13,%rsi
  401587:	bf 01 00 00 00       	mov    $0x1,%edi
  40158c:	31 c0                	xor    %eax,%eax
  40158e:	48 81 c5 a0 01 00 00 	add    $0x1a0,%rbp
  401595:	e8 f6 fa ff ff       	call   401090 <__printf_chk@plt>
    printf("%ld\n", data[x].freq);
    freq += data[x].freq;
  40159a:	4c 03 a5 60 fe ff ff 	add    -0x1a0(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  4015a1:	49 39 ee             	cmp    %rbp,%r14
  4015a4:	75 da                	jne    401580 <main+0x4c0>
  4015a6:	4c 89 e2             	mov    %r12,%rdx
  4015a9:	48 8d 35 04 1b 00 00 	lea    0x1b04(%rip),%rsi        # 4030b4 <_IO_stdin_used+0xb4>
  4015b0:	bf 01 00 00 00       	mov    $0x1,%edi
  4015b5:	31 c0                	xor    %eax,%eax
  4015b7:	e8 d4 fa ff ff       	call   401090 <__printf_chk@plt>
  4015bc:	48 8d 35 fc 1a 00 00 	lea    0x1afc(%rip),%rsi        # 4030bf <_IO_stdin_used+0xbf>
  }
  printf("freq: %ld\n", freq/ seconds);
  long freq_writes = 0;
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  4015c3:	48 8b 93 f0 01 00 00 	mov    0x1f0(%rbx),%rdx
  4015ca:	31 c0                	xor    %eax,%eax
  4015cc:	48 03 93 90 03 00 00 	add    0x390(%rbx),%rdx
  4015d3:	bf 01 00 00 00       	mov    $0x1,%edi
  4015d8:	48 03 53 50          	add    0x50(%rbx),%rdx
  4015dc:	48 03 93 30 05 00 00 	add    0x530(%rbx),%rdx
  4015e3:	48 03 93 d0 06 00 00 	add    0x6d0(%rbx),%rdx
  4015ea:	48 03 93 70 08 00 00 	add    0x870(%rbx),%rdx
  4015f1:	48 03 93 10 0a 00 00 	add    0xa10(%rbx),%rdx
  4015f8:	48 03 93 b0 0b 00 00 	add    0xbb0(%rbx),%rdx
  4015ff:	48 03 93 50 0d 00 00 	add    0xd50(%rbx),%rdx
  401606:	48 03 93 f0 0e 00 00 	add    0xef0(%rbx),%rdx
  40160d:	48 03 93 90 10 00 00 	add    0x1090(%rbx),%rdx
  401614:	48 03 93 30 12 00 00 	add    0x1230(%rbx),%rdx
  40161b:	48 03 93 d0 13 00 00 	add    0x13d0(%rbx),%rdx
  401622:	48 03 93 70 15 00 00 	add    0x1570(%rbx),%rdx
  401629:	48 03 93 10 17 00 00 	add    0x1710(%rbx),%rdx
  401630:	48 03 93 b0 18 00 00 	add    0x18b0(%rbx),%rdx
  401637:	e8 54 fa ff ff       	call   401090 <__printf_chk@plt>
  40163c:	48 8d 3d 8e 1a 00 00 	lea    0x1a8e(%rip),%rdi        # 4030d1 <_IO_stdin_used+0xd1>
  401643:	e8 f8 f9 ff ff       	call   401040 <puts@plt>
  401648:	4c 89 ee             	mov    %r13,%rsi
  40164b:	bf 01 00 00 00       	mov    $0x1,%edi
  401650:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  401652:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
  401659:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  401660:	e8 2b fa ff ff       	call   401090 <__printf_chk@plt>
  401665:	4c 89 ee             	mov    %r13,%rsi
  401668:	bf 01 00 00 00       	mov    $0x1,%edi
  40166d:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  40166f:	48 8b 93 08 01 00 00 	mov    0x108(%rbx),%rdx
  401676:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  40167d:	e8 0e fa ff ff       	call   401090 <__printf_chk@plt>
  401682:	4c 89 ee             	mov    %r13,%rsi
  401685:	bf 01 00 00 00       	mov    $0x1,%edi
  40168a:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  40168c:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
  401693:	48 2b 93 08 01 00 00 	sub    0x108(%rbx),%rdx
  40169a:	e8 f1 f9 ff ff       	call   401090 <__printf_chk@plt>
  40169f:	4c 89 ee             	mov    %r13,%rsi
  4016a2:	bf 01 00 00 00       	mov    $0x1,%edi
  4016a7:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4016a9:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
  4016b0:	48 2b 93 18 01 00 00 	sub    0x118(%rbx),%rdx
  4016b7:	e8 d4 f9 ff ff       	call   401090 <__printf_chk@plt>
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  4016bc:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
  4016c3:	4c 89 ee             	mov    %r13,%rsi
  4016c6:	48 2b 93 28 01 00 00 	sub    0x128(%rbx),%rdx
  4016cd:	bf 01 00 00 00       	mov    $0x1,%edi
  4016d2:	31 c0                	xor    %eax,%eax
  4016d4:	e8 b7 f9 ff ff       	call   401090 <__printf_chk@plt>
  4016d9:	4c 89 ee             	mov    %r13,%rsi
  4016dc:	bf 01 00 00 00       	mov    $0x1,%edi
  4016e1:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  4016e3:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
  4016ea:	48 2b 93 08 01 00 00 	sub    0x108(%rbx),%rdx
  4016f1:	e8 9a f9 ff ff       	call   401090 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  4016f6:	48 8b 93 48 01 00 00 	mov    0x148(%rbx),%rdx
  4016fd:	31 c0                	xor    %eax,%eax
  4016ff:	48 2b 93 38 01 00 00 	sub    0x138(%rbx),%rdx
  401706:	48 8d 35 d1 19 00 00 	lea    0x19d1(%rip),%rsi        # 4030de <_IO_stdin_used+0xde>
  40170d:	bf 01 00 00 00       	mov    $0x1,%edi
  401712:	e8 79 f9 ff ff       	call   401090 <__printf_chk@plt>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  401717:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  40171c:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401725:	75 11                	jne    401738 <main+0x678>
  401727:	48 83 c4 78          	add    $0x78,%rsp
  40172b:	31 c0                	xor    %eax,%eax
  40172d:	5b                   	pop    %rbx
  40172e:	5d                   	pop    %rbp
  40172f:	41 5c                	pop    %r12
  401731:	41 5d                	pop    %r13
  401733:	41 5e                	pop    %r14
  401735:	41 5f                	pop    %r15
  401737:	c3                   	ret
  401738:	e8 23 f9 ff ff       	call   401060 <__stack_chk_fail@plt>
  40173d:	0f 1f 00             	nopl   (%rax)

0000000000401740 <_start>:
  401740:	f3 0f 1e fa          	endbr64
  401744:	31 ed                	xor    %ebp,%ebp
  401746:	49 89 d1             	mov    %rdx,%r9
  401749:	5e                   	pop    %rsi
  40174a:	48 89 e2             	mov    %rsp,%rdx
  40174d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401751:	50                   	push   %rax
  401752:	54                   	push   %rsp
  401753:	45 31 c0             	xor    %r8d,%r8d
  401756:	31 c9                	xor    %ecx,%ecx
  401758:	48 c7 c7 c0 10 40 00 	mov    $0x4010c0,%rdi
  40175f:	ff 15 8b 38 00 00    	call   *0x388b(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  401765:	f4                   	hlt
  401766:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401770 <_dl_relocate_static_pie>:
  401770:	f3 0f 1e fa          	endbr64
  401774:	c3                   	ret
  401775:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40177f:	90                   	nop

0000000000401780 <deregister_tm_clones>:
  401780:	b8 10 50 40 00       	mov    $0x405010,%eax
  401785:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  40178b:	74 13                	je     4017a0 <deregister_tm_clones+0x20>
  40178d:	b8 00 00 00 00       	mov    $0x0,%eax
  401792:	48 85 c0             	test   %rax,%rax
  401795:	74 09                	je     4017a0 <deregister_tm_clones+0x20>
  401797:	bf 10 50 40 00       	mov    $0x405010,%edi
  40179c:	ff e0                	jmp    *%rax
  40179e:	66 90                	xchg   %ax,%ax
  4017a0:	c3                   	ret
  4017a1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4017ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004017b0 <register_tm_clones>:
  4017b0:	be 10 50 40 00       	mov    $0x405010,%esi
  4017b5:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  4017bc:	48 89 f0             	mov    %rsi,%rax
  4017bf:	48 c1 ee 3f          	shr    $0x3f,%rsi
  4017c3:	48 c1 f8 03          	sar    $0x3,%rax
  4017c7:	48 01 c6             	add    %rax,%rsi
  4017ca:	48 d1 fe             	sar    %rsi
  4017cd:	74 11                	je     4017e0 <register_tm_clones+0x30>
  4017cf:	b8 00 00 00 00       	mov    $0x0,%eax
  4017d4:	48 85 c0             	test   %rax,%rax
  4017d7:	74 07                	je     4017e0 <register_tm_clones+0x30>
  4017d9:	bf 10 50 40 00       	mov    $0x405010,%edi
  4017de:	ff e0                	jmp    *%rax
  4017e0:	c3                   	ret
  4017e1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4017ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004017f0 <__do_global_dtors_aux>:
  4017f0:	f3 0f 1e fa          	endbr64
  4017f4:	80 3d 15 38 00 00 00 	cmpb   $0x0,0x3815(%rip)        # 405010 <__TMC_END__>
  4017fb:	75 13                	jne    401810 <__do_global_dtors_aux+0x20>
  4017fd:	55                   	push   %rbp
  4017fe:	48 89 e5             	mov    %rsp,%rbp
  401801:	e8 7a ff ff ff       	call   401780 <deregister_tm_clones>
  401806:	c6 05 03 38 00 00 01 	movb   $0x1,0x3803(%rip)        # 405010 <__TMC_END__>
  40180d:	5d                   	pop    %rbp
  40180e:	c3                   	ret
  40180f:	90                   	nop
  401810:	c3                   	ret
  401811:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40181c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401820 <frame_dummy>:
  401820:	f3 0f 1e fa          	endbr64
  401824:	eb 8a                	jmp    4017b0 <register_tm_clones>
  401826:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401830 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  401830:	83 7f 70 01          	cmpl   $0x1,0x70(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  401834:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  401837:	7e 77                	jle    4018b0 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  401839:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  40183d:	55                   	push   %rbp
  40183e:	49 89 f2             	mov    %rsi,%r10
  401841:	49 89 d3             	mov    %rdx,%r11
  401844:	53                   	push   %rbx
  401845:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  401848:	48 8b 98 c0 01 00 00 	mov    0x1c0(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  40184f:	b8 01 00 00 00       	mov    $0x1,%eax
  401854:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  401858:	48 63 d0             	movslq %eax,%rdx
  40185b:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  40185e:	85 d2                	test   %edx,%edx
  401860:	40 0f 94 c6          	sete   %sil
  401864:	f6 c2 04             	test   $0x4,%dl
  401867:	75 05                	jne    40186e <pollthreads+0x3e>
  401869:	40 84 f6             	test   %sil,%sil
  40186c:	74 0d                	je     40187b <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  40186e:	49 63 08             	movslq (%r8),%rcx
  401871:	8d 69 01             	lea    0x1(%rcx),%ebp
  401874:	41 89 28             	mov    %ebp,(%r8)
  401877:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  40187b:	83 e2 08             	and    $0x8,%edx
  40187e:	75 05                	jne    401885 <pollthreads+0x55>
  401880:	40 84 f6             	test   %sil,%sil
  401883:	74 1b                	je     4018a0 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  401885:	48 63 17             	movslq (%rdi),%rdx
  401888:	8d 4a 01             	lea    0x1(%rdx),%ecx
  40188b:	89 0f                	mov    %ecx,(%rdi)
  40188d:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  401891:	83 c0 01             	add    $0x1,%eax
  401894:	41 39 41 70          	cmp    %eax,0x70(%r9)
  401898:	7f be                	jg     401858 <pollthreads+0x28>
}
  40189a:	31 c0                	xor    %eax,%eax
  40189c:	5b                   	pop    %rbx
  40189d:	5d                   	pop    %rbp
  40189e:	c3                   	ret
  40189f:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  4018a0:	83 c0 01             	add    $0x1,%eax
  4018a3:	41 39 41 70          	cmp    %eax,0x70(%r9)
  4018a7:	7f af                	jg     401858 <pollthreads+0x28>
}
  4018a9:	31 c0                	xor    %eax,%eax
  4018ab:	5b                   	pop    %rbx
  4018ac:	5d                   	pop    %rbp
  4018ad:	c3                   	ret
  4018ae:	66 90                	xchg   %ax,%ax
  4018b0:	31 c0                	xor    %eax,%eax
  4018b2:	c3                   	ret
  4018b3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4018be:	66 90                	xchg   %ax,%ax

00000000004018c0 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  4018c0:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4018c3:	48 8b bf c0 00 00 00 	mov    0xc0(%rdi),%rdi
      if (*availableidx == 0) {
  4018ca:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4018cd:	48 83 c7 01          	add    $0x1,%rdi
  4018d1:	48 85 ff             	test   %rdi,%rdi
  4018d4:	7e 66                	jle    40193c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  4018d6:	4d 8b 93 a8 00 00 00 	mov    0xa8(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4018dd:	31 c9                	xor    %ecx,%ecx
  4018df:	45 31 c9             	xor    %r9d,%r9d
  4018e2:	31 c0                	xor    %eax,%eax
  4018e4:	eb 18                	jmp    4018fe <findavailable+0x3e>
  4018e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4018f0:	83 c1 01             	add    $0x1,%ecx
  4018f3:	48 63 c1             	movslq %ecx,%rax
  4018f6:	49 89 c1             	mov    %rax,%r9
  4018f9:	48 39 f8             	cmp    %rdi,%rax
  4018fc:	7d 3e                	jge    40193c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  4018fe:	48 c1 e0 05          	shl    $0x5,%rax
  401902:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401908:	75 e6                	jne    4018f0 <findavailable+0x30>
         available[*availableidx] = x;
  40190a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  40190d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401911:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401915:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401918:	41 8b 43 70          	mov    0x70(%r11),%eax
  40191c:	01 c0                	add    %eax,%eax
  40191e:	41 39 c0             	cmp    %eax,%r8d
  401921:	74 19                	je     40193c <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401923:	49 8b bb c0 00 00 00 	mov    0xc0(%r11),%rdi
  40192a:	83 c1 01             	add    $0x1,%ecx
  40192d:	48 63 c1             	movslq %ecx,%rax
  401930:	48 83 c7 01          	add    $0x1,%rdi
  401934:	49 89 c1             	mov    %rax,%r9
  401937:	48 39 f8             	cmp    %rdi,%rax
  40193a:	7c c2                	jl     4018fe <findavailable+0x3e>
      if (*availableidx == 0) {
  40193c:	31 c0                	xor    %eax,%eax
  40193e:	45 85 c0             	test   %r8d,%r8d
  401941:	0f 94 c0             	sete   %al
}
  401944:	c3                   	ret
  401945:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401950 <singlewriter2>:
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401950:	41 54                	push   %r12
  401952:	55                   	push   %rbp
  401953:	53                   	push   %rbx
  401954:	48 89 fb             	mov    %rdi,%rbx
  if ((__atomic_load_n(&data->readcursor, __ATOMIC_SEQ_CST) % data->threadsize) == 0) {
  401957:	8b 87 58 01 00 00    	mov    0x158(%rdi),%eax
  40195d:	99                   	cltd
  40195e:	8b 4f 70             	mov    0x70(%rdi),%ecx
  401961:	f7 f9                	idiv   %ecx
  401963:	85 d2                	test   %edx,%edx
  401965:	74 29                	je     401990 <singlewriter2+0x40>
  if ((data->writecursor % data->threadsize) == 0) {
  401967:	8b 83 50 01 00 00    	mov    0x150(%rbx),%eax
  40196d:	99                   	cltd
  40196e:	f7 f9                	idiv   %ecx
  401970:	85 d2                	test   %edx,%edx
  401972:	75 11                	jne    401985 <singlewriter2+0x35>
    data->currentwrite++;
  401974:	83 83 84 01 00 00 01 	addl   $0x1,0x184(%rbx)
    data->writecursor = 0;
  40197b:	c7 83 50 01 00 00 00 00 00 00 	movl   $0x0,0x150(%rbx)
}
  401985:	5b                   	pop    %rbx
  401986:	5d                   	pop    %rbp
  401987:	41 5c                	pop    %r12
  401989:	c3                   	ret
  40198a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        struct Data * thread = &data->threads[data->threadindex];
  401990:	48 63 47 6c          	movslq 0x6c(%rdi),%rax
    data->currentread++;
  401994:	83 87 80 01 00 00 01 	addl   $0x1,0x180(%rdi)
    data->readcursor = 0;
  40199b:	c7 87 58 01 00 00 00 00 00 00 	movl   $0x0,0x158(%rdi)
        struct Data * thread = &data->threads[data->threadindex];
  4019a5:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  4019a9:	48 8d 2c 90          	lea    (%rax,%rdx,4),%rbp
  4019ad:	48 c1 e5 05          	shl    $0x5,%rbp
  4019b1:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  4019b5:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4019ba:	48 63 85 9c 01 00 00 	movslq 0x19c(%rbp),%rax
  4019c1:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  4019c5:	48 8b 85 90 01 00 00 	mov    0x190(%rbp),%rax
  4019cc:	4c 8d 24 d0          	lea    (%rax,%rdx,8),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  4019d0:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  4019d5:	e8 76 f6 ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4019da:	8b 85 9c 01 00 00    	mov    0x19c(%rbp),%eax
  4019e0:	83 c0 01             	add    $0x1,%eax
  4019e3:	99                   	cltd
  4019e4:	f7 bd 98 01 00 00    	idivl  0x198(%rbp)
        epoch->thread = data->threadindex;
  4019ea:	8b 43 6c             	mov    0x6c(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4019ed:	89 95 9c 01 00 00    	mov    %edx,0x19c(%rbp)
        epoch->thread = data->threadindex;
  4019f3:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  4019f7:	48 8b 05 0a 17 00 00 	mov    0x170a(%rip),%rax        # 403108 <_IO_stdin_used+0x108>
  4019fe:	49 89 44 24 20       	mov    %rax,0x20(%r12)
  if ((data->writecursor % data->threadsize) == 0) {
  401a03:	8b 4b 70             	mov    0x70(%rbx),%ecx
  401a06:	e9 5c ff ff ff       	jmp    401967 <singlewriter2+0x17>
  401a0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000401a10 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a10:	41 55                	push   %r13
  401a12:	49 89 d5             	mov    %rdx,%r13
  401a15:	41 54                	push   %r12
  401a17:	49 89 cc             	mov    %rcx,%r12
  401a1a:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401a1b:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a1e:	48 89 fd             	mov    %rdi,%rbp
  401a21:	53                   	push   %rbx
  401a22:	48 89 f3             	mov    %rsi,%rbx
  401a25:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401a29:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a2d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401a36:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401a3b:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401a3d:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401a45:	8b 81 64 01 00 00    	mov    0x164(%rcx),%eax
  int writers = 0;
  401a4b:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401a53:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401a5b:	83 c0 01             	add    $0x1,%eax
  401a5e:	99                   	cltd
  401a5f:	f7 7f 70             	idivl  0x70(%rdi)
  401a62:	89 91 64 01 00 00    	mov    %edx,0x164(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401a68:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401a6d:	4c 89 e9             	mov    %r13,%rcx
  401a70:	e8 4b fe ff ff       	call   4018c0 <findavailable>
  if (fill == 1) {
  401a75:	83 f8 01             	cmp    $0x1,%eax
  401a78:	0f 84 59 01 00 00    	je     401bd7 <singlewriter+0x1c7>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401a7e:	48 89 ef             	mov    %rbp,%rdi
  401a81:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401a86:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401a8b:	4c 89 e2             	mov    %r12,%rdx
  401a8e:	4c 89 ee             	mov    %r13,%rsi
  401a91:	e8 9a fd ff ff       	call   401830 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401a96:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401a9b:	85 ff                	test   %edi,%edi
  401a9d:	0f 8e 5e 01 00 00    	jle    401c01 <singlewriter+0x1f1>
  401aa3:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401aa8:	31 c9                	xor    %ecx,%ecx
  401aaa:	eb 62                	jmp    401b0e <singlewriter+0xfe>
  401aac:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401ab0:	48 8b 04 cb          	mov    (%rbx,%rcx,8),%rax
          int thread = readyreaders[x];
  401ab4:	49 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%rdx
  401ab9:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401abc:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401ac0:	48 c1 e0 05          	shl    $0x5,%rax
  401ac4:	48 03 85 a8 00 00 00 	add    0xa8(%rbp),%rax
          data->threads[thread].reading = chunk;
  401acb:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
          int thread = readyreaders[x];
  401acf:	49 89 d1             	mov    %rdx,%r9
          data->threads[thread].start = start;
  401ad2:	66 0f 6e 00          	movd   (%rax),%xmm0
  401ad6:	66 0f 6e 48 08       	movd   0x8(%rax),%xmm1
          data->threads[thread].reading = chunk;
  401adb:	4a 8d 14 92          	lea    (%rdx,%r10,4),%rdx
          chunk->available = READING;
  401adf:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
          data->threads[thread].reading = chunk;
  401ae6:	48 c1 e2 05          	shl    $0x5,%rdx
  401aea:	48 03 55 30          	add    0x30(%rbp),%rdx
          data->threads[thread].start = start;
  401aee:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401af2:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
          chunk->owner = thread;
  401af9:	44 89 48 14          	mov    %r9d,0x14(%rax)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401afd:	83 8a d0 00 00 00 10 	orl    $0x10,0xd0(%rdx)
          data->threads[thread].start = start;
  401b04:	66 0f d6 42 14       	movq   %xmm0,0x14(%rdx)
        for (int x = 0; x < readers ; x++) {
  401b09:	48 39 cf             	cmp    %rcx,%rdi
  401b0c:	74 07                	je     401b15 <singlewriter+0x105>
  401b0e:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401b10:	4c 39 c1             	cmp    %r8,%rcx
  401b13:	75 9b                	jne    401ab0 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401b15:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401b1a:	45 85 c0             	test   %r8d,%r8d
  401b1d:	7e 77                	jle    401b96 <singlewriter+0x186>
                if (assignedchunk  == availableidx) {
  401b1f:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401b23:	41 01 f0             	add    %esi,%r8d
  401b26:	eb 6a                	jmp    401b92 <singlewriter+0x182>
  401b28:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b30:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401b33:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401b36:	49 63 14 24          	movslq (%r12),%rdx
   for (int x = 0; x < writers ; x++) {
  401b3a:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b3e:	48 8b 04 f3          	mov    (%rbx,%rsi,8),%rax
          data->threads[thread].writing = chunk;
  401b42:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
          int thread = readywriters[x];
  401b46:	49 89 d1             	mov    %rdx,%r9
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b49:	48 c1 e0 05          	shl    $0x5,%rax
  401b4d:	48 03 85 a8 00 00 00 	add    0xa8(%rbp),%rax
          data->threads[thread].writing = chunk;
  401b54:	48 8d 14 b2          	lea    (%rdx,%rsi,4),%rdx
          data->threads[thread].publishstart = start;
  401b58:	66 0f 6e 00          	movd   (%rax),%xmm0
  401b5c:	66 0f 6e 50 08       	movd   0x8(%rax),%xmm2
          data->threads[thread].writing = chunk;
  401b61:	48 c1 e2 05          	shl    $0x5,%rdx
      chunk->available = WRITING;
  401b65:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
          data->threads[thread].writing = chunk;
  401b6c:	48 03 55 30          	add    0x30(%rbp),%rdx
          data->threads[thread].publishstart = start;
  401b70:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401b74:	48 89 82 b8 00 00 00 	mov    %rax,0xb8(%rdx)
          chunk->owner = thread;
  401b7b:	44 89 48 14          	mov    %r9d,0x14(%rax)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401b7f:	83 8a d0 00 00 00 20 	orl    $0x20,0xd0(%rdx)
          data->threads[thread].publishstart = start;
  401b86:	66 0f d6 42 40       	movq   %xmm0,0x40(%rdx)
   for (int x = 0; x < writers ; x++) {
  401b8b:	44 39 c1             	cmp    %r8d,%ecx
  401b8e:	74 06                	je     401b96 <singlewriter+0x186>
  401b90:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401b92:	39 f7                	cmp    %esi,%edi
  401b94:	75 9a                	jne    401b30 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401b96:	8b 7d 70             	mov    0x70(%rbp),%edi
  401b99:	85 ff                	test   %edi,%edi
  401b9b:	7e 38                	jle    401bd5 <singlewriter+0x1c5>
        if (data->threads[x].newmask != 0) {
  401b9d:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401ba1:	31 c9                	xor    %ecx,%ecx
  401ba3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401ba8:	48 63 d1             	movslq %ecx,%rdx
  401bab:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
  401baf:	48 8d 04 82          	lea    (%rdx,%rax,4),%rax
  401bb3:	48 c1 e0 05          	shl    $0x5,%rax
  401bb7:	4c 01 c0             	add    %r8,%rax
  401bba:	8b b0 d0 00 00 00    	mov    0xd0(%rax),%esi
  401bc0:	85 f6                	test   %esi,%esi
  401bc2:	74 34                	je     401bf8 <singlewriter+0x1e8>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401bc4:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401bc8:	83 c1 01             	add    $0x1,%ecx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401bcb:	89 34 90             	mov    %esi,(%rax,%rdx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401bce:	8b 7d 70             	mov    0x70(%rbp),%edi
  401bd1:	39 f9                	cmp    %edi,%ecx
  401bd3:	7c d3                	jl     401ba8 <singlewriter+0x198>
  return 0;
  401bd5:	31 c0                	xor    %eax,%eax
}
  401bd7:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401bdc:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401be5:	75 21                	jne    401c08 <singlewriter+0x1f8>
  401be7:	48 83 c4 28          	add    $0x28,%rsp
  401beb:	5b                   	pop    %rbx
  401bec:	5d                   	pop    %rbp
  401bed:	41 5c                	pop    %r12
  401bef:	41 5d                	pop    %r13
  401bf1:	c3                   	ret
  401bf2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      for (int x = 0; x < data->threadsize ; x++) {
  401bf8:	83 c1 01             	add    $0x1,%ecx
  401bfb:	39 f9                	cmp    %edi,%ecx
  401bfd:	7c a9                	jl     401ba8 <singlewriter+0x198>
  401bff:	eb d4                	jmp    401bd5 <singlewriter+0x1c5>
      int assignedchunk = 0;
  401c01:	31 f6                	xor    %esi,%esi
  401c03:	e9 0d ff ff ff       	jmp    401b15 <singlewriter+0x105>
}
  401c08:	e8 53 f4 ff ff       	call   401060 <__stack_chk_fail@plt>
  401c0d:	0f 1f 00             	nopl   (%rax)

0000000000401c10 <threadwork>:
int * threadwork(struct Data * data) {
  401c10:	41 57                	push   %r15
  401c12:	41 56                	push   %r14
  401c14:	41 55                	push   %r13
  401c16:	41 54                	push   %r12
  401c18:	55                   	push   %rbp
  401c19:	53                   	push   %rbx
  401c1a:	48 89 fb             	mov    %rdi,%rbx
  clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401c1d:	bf 04 00 00 00       	mov    $0x4,%edi
int * threadwork(struct Data * data) {
  401c22:	48 83 ec 28          	sub    $0x28,%rsp
  401c26:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401c2f:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401c34:	31 c0                	xor    %eax,%eax
  clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401c36:	48 89 e6             	mov    %rsp,%rsi
  401c39:	e8 12 f4 ff ff       	call   401050 <clock_gettime@plt>
     for (int x = 1; x < data->threadsize ; x++) {
  401c3e:	8b 43 70             	mov    0x70(%rbx),%eax
  __atomic_fetch_add(&data->main->writecursor, 1, __ATOMIC_ACQUIRE);
  401c41:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
     for (int x = 1; x < data->threadsize ; x++) {
  401c45:	83 f8 01             	cmp    $0x1,%eax
  401c48:	0f 8e 53 01 00 00    	jle    401da1 <threadwork+0x191>
  401c4e:	b9 01 00 00 00       	mov    $0x1,%ecx
  401c53:	e9 37 01 00 00       	jmp    401d8f <threadwork+0x17f>
  401c58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401c60:	48 63 83 50 01 00 00 	movslq 0x150(%rbx),%rax
        epoch->time = time;
  401c67:	66 0f 6f 04 24       	movdqa (%rsp),%xmm0
        data->freq_writes++;
  401c6c:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401c71:	48 89 c2             	mov    %rax,%rdx
  401c74:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401c7b:	41 89 d0             	mov    %edx,%r8d
  401c7e:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401c82:	48 c1 e8 20          	shr    $0x20,%rax
  401c86:	01 d0                	add    %edx,%eax
  401c88:	c1 f8 03             	sar    $0x3,%eax
  401c8b:	44 29 c0             	sub    %r8d,%eax
  401c8e:	41 89 c0             	mov    %eax,%r8d
  401c91:	41 c1 e0 04          	shl    $0x4,%r8d
  401c95:	41 29 c0             	sub    %eax,%r8d
  401c98:	89 f0                	mov    %esi,%eax
  401c9a:	44 29 c2             	sub    %r8d,%edx
  401c9d:	c1 e0 18             	shl    $0x18,%eax
  401ca0:	09 c2                	or     %eax,%edx
  401ca2:	48 63 87 50 01 00 00 	movslq 0x150(%rdi),%rax
  401ca9:	41 89 d2             	mov    %edx,%r10d
  401cac:	48 89 c2             	mov    %rax,%rdx
  401caf:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401cb6:	41 89 d0             	mov    %edx,%r8d
  401cb9:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401cbd:	48 c1 e8 20          	shr    $0x20,%rax
  401cc1:	01 d0                	add    %edx,%eax
  401cc3:	c1 f8 03             	sar    $0x3,%eax
  401cc6:	44 29 c0             	sub    %r8d,%eax
  401cc9:	41 89 c0             	mov    %eax,%r8d
  401ccc:	41 c1 e0 04          	shl    $0x4,%r8d
  401cd0:	41 29 c0             	sub    %eax,%r8d
  401cd3:	89 c8                	mov    %ecx,%eax
  401cd5:	44 29 c2             	sub    %r8d,%edx
  401cd8:	c1 e0 08             	shl    $0x8,%eax
  401cdb:	c1 e2 10             	shl    $0x10,%edx
  401cde:	44 09 d2             	or     %r10d,%edx
  401ce1:	09 c2                	or     %eax,%edx
        struct Data * thread = &data->threads[data->threadindex];
  401ce3:	48 63 c6             	movslq %esi,%rax
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401ce6:	41 89 d2             	mov    %edx,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  401ce9:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  401ced:	4c 8d 04 90          	lea    (%rax,%rdx,4),%r8
  401cf1:	49 c1 e0 05          	shl    $0x5,%r8
  401cf5:	4c 03 43 30          	add    0x30(%rbx),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401cf9:	49 63 90 9c 01 00 00 	movslq 0x19c(%r8),%rdx
  401d00:	48 89 d0             	mov    %rdx,%rax
  401d03:	4c 8d 0c 92          	lea    (%rdx,%rdx,4),%r9
  401d07:	49 8b 90 90 01 00 00 	mov    0x190(%r8),%rdx
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d0e:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401d11:	4e 8d 0c ca          	lea    (%rdx,%r9,8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d15:	99                   	cltd
  401d16:	41 f7 b8 98 01 00 00 	idivl  0x198(%r8)
        data->main->works[buffer] = data->threadindex;
  401d1d:	48 8b 47 78          	mov    0x78(%rdi),%rax
        epoch->time = time;
  401d21:	41 0f 11 41 08       	movups %xmm0,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d26:	41 89 90 9c 01 00 00 	mov    %edx,0x19c(%r8)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401d2d:	49 63 d2             	movslq %r10d,%rdx
        epoch->thread = data->threadindex;
  401d30:	41 89 31             	mov    %esi,(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401d33:	49 89 51 18          	mov    %rdx,0x18(%r9)
  epoch->set = 1;
  401d37:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
        data->main->works[buffer] = data->threadindex;
  401d3f:	40 88 34 10          	mov    %sil,(%rax,%rdx,1)
         data->writecursor = (data->writecursor + 1) % 0xf;
  401d43:	8b 83 50 01 00 00    	mov    0x150(%rbx),%eax
    data->prevread = data->main->currentread;
  401d49:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
         data->writecursor = (data->writecursor + 1) % 0xf;
  401d4d:	8d 50 01             	lea    0x1(%rax),%edx
  401d50:	48 63 c2             	movslq %edx,%rax
  401d53:	89 d6                	mov    %edx,%esi
  401d55:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401d5c:	48 c1 e8 20          	shr    $0x20,%rax
  401d60:	01 d0                	add    %edx,%eax
  401d62:	c1 fe 1f             	sar    $0x1f,%esi
     for (int x = 1; x < data->threadsize ; x++) {
  401d65:	83 c1 01             	add    $0x1,%ecx
         data->writecursor = (data->writecursor + 1) % 0xf;
  401d68:	c1 f8 03             	sar    $0x3,%eax
  401d6b:	29 f0                	sub    %esi,%eax
  401d6d:	89 c6                	mov    %eax,%esi
  401d6f:	c1 e6 04             	shl    $0x4,%esi
  401d72:	29 c6                	sub    %eax,%esi
    data->prevread = data->main->currentread;
  401d74:	8b 87 80 01 00 00    	mov    0x180(%rdi),%eax
         data->writecursor = (data->writecursor + 1) % 0xf;
  401d7a:	29 f2                	sub    %esi,%edx
    data->prevread = data->main->currentread;
  401d7c:	89 83 88 01 00 00    	mov    %eax,0x188(%rbx)
     for (int x = 1; x < data->threadsize ; x++) {
  401d82:	8b 43 70             	mov    0x70(%rbx),%eax
         data->writecursor = (data->writecursor + 1) % 0xf;
  401d85:	89 93 50 01 00 00    	mov    %edx,0x150(%rbx)
     for (int x = 1; x < data->threadsize ; x++) {
  401d8b:	39 c8                	cmp    %ecx,%eax
  401d8d:	7e 12                	jle    401da1 <threadwork+0x191>
  401d8f:	8b 73 6c             	mov    0x6c(%rbx),%esi
     if (x != data->threadindex) {
  401d92:	39 ce                	cmp    %ecx,%esi
  401d94:	0f 85 c6 fe ff ff    	jne    401c60 <threadwork+0x50>
     for (int x = 1; x < data->threadsize ; x++) {
  401d9a:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401d9d:	39 c1                	cmp    %eax,%ecx
  401d9f:	7c f1                	jl     401d92 <threadwork+0x182>
  __atomic_fetch_add(&data->main->writecursor, 1, __ATOMIC_ACQUIRE);
  401da1:	f0 83 87 50 01 00 00 01 	lock addl $0x1,0x150(%rdi)
  for (int y = 1 ; y < data->threadsize; y++) {
  401da9:	44 8b 43 70          	mov    0x70(%rbx),%r8d
  401dad:	41 83 f8 01          	cmp    $0x1,%r8d
  401db1:	0f 8e 89 01 00 00    	jle    401f40 <threadwork+0x330>
          if (y != data->threadindex) {
  401db7:	48 63 43 6c          	movslq 0x6c(%rbx),%rax
    __atomic_fetch_add(&data->main->readcursor, 1, __ATOMIC_ACQUIRE);
  401dbb:	4c 8b 53 28          	mov    0x28(%rbx),%r10
                struct Data * thread = &data->threads[data->threadindex];
  401dbf:	bf a0 01 00 00       	mov    $0x1a0,%edi
  for (int y = 1 ; y < data->threadsize; y++) {
  401dc4:	be 01 00 00 00       	mov    $0x1,%esi
              past = data->threadsize - 1;
  401dc9:	41 8d 68 ff          	lea    -0x1(%r8),%ebp
                struct Data * thread = &data->threads[data->threadindex];
  401dcd:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401dd1:	41 89 c4             	mov    %eax,%r12d
          if (y != data->threadindex) {
  401dd4:	49 89 c1             	mov    %rax,%r9
                struct Data * thread = &data->threads[data->threadindex];
  401dd7:	4c 8d 1c 90          	lea    (%rax,%rdx,4),%r11
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401ddb:	41 c1 e4 08          	shl    $0x8,%r12d
                struct Data * thread = &data->threads[data->threadindex];
  401ddf:	49 c1 e3 05          	shl    $0x5,%r11
  401de3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (y != data->threadindex) {
  401de8:	44 39 ce             	cmp    %r9d,%esi
  401deb:	0f 84 09 01 00 00    	je     401efa <threadwork+0x2ea>
            int rc = data->threads[x].writecursor;
  401df1:	4c 8b 7b 30          	mov    0x30(%rbx),%r15
            long past = ((data->main->writecursor - 1) % 0xf);
  401df5:	41 8b 82 50 01 00 00 	mov    0x150(%r10),%eax
  401dfc:	41 be 0e 00 00 00    	mov    $0xe,%r14d
            data->freq++;
  401e02:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
            long past = ((data->main->writecursor - 1) % 0xf);
  401e07:	8d 50 ff             	lea    -0x1(%rax),%edx
  401e0a:	48 63 c2             	movslq %edx,%rax
  401e0d:	89 d1                	mov    %edx,%ecx
  401e0f:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401e16:	c1 f9 1f             	sar    $0x1f,%ecx
  401e19:	48 c1 e8 20          	shr    $0x20,%rax
  401e1d:	01 d0                	add    %edx,%eax
  401e1f:	c1 f8 03             	sar    $0x3,%eax
  401e22:	29 c8                	sub    %ecx,%eax
  401e24:	89 c1                	mov    %eax,%ecx
  401e26:	c1 e1 04             	shl    $0x4,%ecx
  401e29:	29 c1                	sub    %eax,%ecx
              past = data->threadsize - 1;
  401e2b:	89 d0                	mov    %edx,%eax
            int rc = data->threads[x].writecursor;
  401e2d:	41 8b 94 3f 50 01 00 00 	mov    0x150(%r15,%rdi,1),%edx
              past = data->threadsize - 1;
  401e35:	29 c8                	sub    %ecx,%eax
  401e37:	0f 48 c5             	cmovs  %ebp,%eax
  401e3a:	48 63 c8             	movslq %eax,%rcx
            if (rc < 0) {
  401e3d:	85 d2                	test   %edx,%edx
  401e3f:	78 2d                	js     401e6e <threadwork+0x25e>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401e41:	48 63 c2             	movslq %edx,%rax
  401e44:	41 89 d5             	mov    %edx,%r13d
  401e47:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401e4e:	41 c1 fd 1f          	sar    $0x1f,%r13d
  401e52:	48 c1 e8 20          	shr    $0x20,%rax
  401e56:	01 d0                	add    %edx,%eax
  401e58:	c1 f8 03             	sar    $0x3,%eax
  401e5b:	44 29 e8             	sub    %r13d,%eax
  401e5e:	41 89 c5             	mov    %eax,%r13d
  401e61:	41 c1 e5 04          	shl    $0x4,%r13d
  401e65:	41 29 c5             	sub    %eax,%r13d
  401e68:	44 29 ea             	sub    %r13d,%edx
  401e6b:	4c 63 f2             	movslq %edx,%r14
                struct Data * thread = &data->threads[data->threadindex];
  401e6e:	4d 01 df             	add    %r11,%r15
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401e71:	48 c1 e1 10          	shl    $0x10,%rcx
            thepoch->time = time; 
  401e75:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401e7a:	49 63 97 9c 01 00 00 	movslq 0x19c(%r15),%rdx
  401e81:	48 89 d0             	mov    %rdx,%rax
  401e84:	4c 8d 2c 92          	lea    (%rdx,%rdx,4),%r13
  401e88:	49 8b 97 90 01 00 00 	mov    0x190(%r15),%rdx
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e8f:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401e92:	4e 8d 2c ea          	lea    (%rdx,%r13,8),%r13
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e96:	99                   	cltd
  401e97:	41 f7 bf 98 01 00 00 	idivl  0x198(%r15)
            thepoch->time = time; 
  401e9e:	41 0f 11 4d 08       	movups %xmm1,0x8(%r13)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401ea3:	89 f0                	mov    %esi,%eax
  401ea5:	c1 e0 18             	shl    $0x18,%eax
  401ea8:	44 09 e0             	or     %r12d,%eax
  401eab:	48 98                	cltq
  401ead:	48 09 c8             	or     %rcx,%rax
  401eb0:	4c 09 f0             	or     %r14,%rax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401eb3:	41 89 97 9c 01 00 00 	mov    %edx,0x19c(%r15)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401eba:	49 89 45 18          	mov    %rax,0x18(%r13)
          data->readcursor = (data->readcursor) % 0xf;
  401ebe:	48 63 83 58 01 00 00 	movslq 0x158(%rbx),%rax
                thepoch->thread = x;
  401ec5:	41 89 75 00          	mov    %esi,0x0(%r13)
          data->readcursor = (data->readcursor) % 0xf;
  401ec9:	48 89 c2             	mov    %rax,%rdx
  401ecc:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
          thepoch->set = 1;
  401ed3:	41 c7 45 24 01 00 00 00 	movl   $0x1,0x24(%r13)
          data->readcursor = (data->readcursor) % 0xf;
  401edb:	89 d1                	mov    %edx,%ecx
  401edd:	c1 f9 1f             	sar    $0x1f,%ecx
  401ee0:	48 c1 e8 20          	shr    $0x20,%rax
  401ee4:	01 d0                	add    %edx,%eax
  401ee6:	c1 f8 03             	sar    $0x3,%eax
  401ee9:	29 c8                	sub    %ecx,%eax
  401eeb:	89 c1                	mov    %eax,%ecx
  401eed:	c1 e1 04             	shl    $0x4,%ecx
  401ef0:	29 c1                	sub    %eax,%ecx
  401ef2:	29 ca                	sub    %ecx,%edx
  401ef4:	89 93 58 01 00 00    	mov    %edx,0x158(%rbx)
  for (int y = 1 ; y < data->threadsize; y++) {
  401efa:	83 c6 01             	add    $0x1,%esi
  401efd:	48 81 c7 a0 01 00 00 	add    $0x1a0,%rdi
  401f04:	44 39 c6             	cmp    %r8d,%esi
  401f07:	0f 85 db fe ff ff    	jne    401de8 <threadwork+0x1d8>
    __atomic_fetch_add(&data->main->readcursor, 1, __ATOMIC_ACQUIRE);
  401f0d:	f0 41 83 82 58 01 00 00 01 	lock addl $0x1,0x158(%r10)
}
  401f16:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  401f1b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401f24:	75 20                	jne    401f46 <threadwork+0x336>
  401f26:	48 83 c4 28          	add    $0x28,%rsp
  401f2a:	31 c0                	xor    %eax,%eax
  401f2c:	5b                   	pop    %rbx
  401f2d:	5d                   	pop    %rbp
  401f2e:	41 5c                	pop    %r12
  401f30:	41 5d                	pop    %r13
  401f32:	41 5e                	pop    %r14
  401f34:	41 5f                	pop    %r15
  401f36:	c3                   	ret
  401f37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    __atomic_fetch_add(&data->main->readcursor, 1, __ATOMIC_ACQUIRE);
  401f40:	4c 8b 53 28          	mov    0x28(%rbx),%r10
  401f44:	eb c7                	jmp    401f0d <threadwork+0x2fd>
}
  401f46:	e8 15 f1 ff ff       	call   401060 <__stack_chk_fail@plt>
  401f4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000401f50 <work>:
void * work(void * arg) {
  401f50:	41 56                	push   %r14
  401f52:	48 8d 35 ab 10 00 00 	lea    0x10ab(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  401f59:	31 c0                	xor    %eax,%eax
  401f5b:	41 55                	push   %r13
  401f5d:	41 54                	push   %r12
  401f5f:	55                   	push   %rbp
  401f60:	53                   	push   %rbx
  401f61:	8b 57 6c             	mov    0x6c(%rdi),%edx
  401f64:	48 89 fb             	mov    %rdi,%rbx
  401f67:	bf 01 00 00 00       	mov    $0x1,%edi
  401f6c:	e8 1f f1 ff ff       	call   401090 <__printf_chk@plt>
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  401f71:	8b 43 6c             	mov    0x6c(%rbx),%eax
  401f74:	48 8d 35 9c 10 00 00 	lea    0x109c(%rip),%rsi        # 403017 <_IO_stdin_used+0x17>
  401f7b:	bf 01 00 00 00       	mov    $0x1,%edi
  int bucketstart = data->bucketstart;
  401f80:	44 8b b3 a0 00 00 00 	mov    0xa0(%rbx),%r14d
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  401f87:	8d 50 01             	lea    0x1(%rax),%edx
  401f8a:	31 c0                	xor    %eax,%eax
  int bucketlim = ((data->threadindex + 1) * data->buckets) ;
  401f8c:	0f af 93 98 00 00 00 	imul   0x98(%rbx),%edx
  401f93:	e8 f8 f0 ff ff       	call   401090 <__printf_chk@plt>
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  401f98:	48 8b 83 c0 00 00 00 	mov    0xc0(%rbx),%rax
  401f9f:	be 08 00 00 00       	mov    $0x8,%esi
  401fa4:	48 8d 78 01          	lea    0x1(%rax),%rdi
  401fa8:	e8 d3 f0 ff ff       	call   401080 <calloc@plt>
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  401fad:	4c 63 6b 70          	movslq 0x70(%rbx),%r13
  401fb1:	be 04 00 00 00       	mov    $0x4,%esi
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  401fb6:	48 89 c5             	mov    %rax,%rbp
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  401fb9:	4c 89 ef             	mov    %r13,%rdi
  401fbc:	e8 bf f0 ff ff       	call   401080 <calloc@plt>
  int * readywriters = calloc(data->threadsize, sizeof(int));
  401fc1:	be 04 00 00 00       	mov    $0x4,%esi
  401fc6:	4c 89 ef             	mov    %r13,%rdi
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  401fc9:	49 89 c4             	mov    %rax,%r12
  int * readywriters = calloc(data->threadsize, sizeof(int));
  401fcc:	e8 af f0 ff ff       	call   401080 <calloc@plt>
  while (data->running == 1) {
  401fd1:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  data->workindex = bucketstart;
  401fd5:	44 89 73 5c          	mov    %r14d,0x5c(%rbx)
  while (data->running == 1) {
  401fd9:	75 49                	jne    402024 <work+0xd4>
  401fdb:	49 89 c5             	mov    %rax,%r13
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  401fde:	4c 8d b3 30 01 00 00 	lea    0x130(%rbx),%r14
  401fe5:	0f 1f 00             	nopl   (%rax)
    if (data->threadindex == 0) {
  401fe8:	8b 43 6c             	mov    0x6c(%rbx),%eax
  401feb:	85 c0                	test   %eax,%eax
  401fed:	75 59                	jne    402048 <work+0xf8>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  401fef:	4c 89 f6             	mov    %r14,%rsi
  401ff2:	bf 04 00 00 00       	mov    $0x4,%edi
  401ff7:	e8 54 f0 ff ff       	call   401050 <clock_gettime@plt>
      singlewriter2(data, available, readyreaders, readywriters);
  401ffc:	4c 89 e9             	mov    %r13,%rcx
  401fff:	4c 89 e2             	mov    %r12,%rdx
  402002:	48 89 ee             	mov    %rbp,%rsi
  402005:	48 89 df             	mov    %rbx,%rdi
  402008:	e8 43 f9 ff ff       	call   401950 <singlewriter2>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swend);
  40200d:	48 8d b3 40 01 00 00 	lea    0x140(%rbx),%rsi
  402014:	bf 04 00 00 00       	mov    $0x4,%edi
  402019:	e8 32 f0 ff ff       	call   401050 <clock_gettime@plt>
  while (data->running == 1) {
  40201e:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  402022:	74 c4                	je     401fe8 <work+0x98>
  402024:	8b 53 6c             	mov    0x6c(%rbx),%edx
  402027:	48 8d 35 f7 0f 00 00 	lea    0xff7(%rip),%rsi        # 403025 <_IO_stdin_used+0x25>
  40202e:	bf 01 00 00 00       	mov    $0x1,%edi
  402033:	31 c0                	xor    %eax,%eax
  402035:	e8 56 f0 ff ff       	call   401090 <__printf_chk@plt>
}
  40203a:	5b                   	pop    %rbx
  40203b:	5d                   	pop    %rbp
  40203c:	41 5c                	pop    %r12
  40203e:	41 5d                	pop    %r13
  402040:	41 5e                	pop    %r14
  402042:	c3                   	ret
  402043:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      threadwork(data);
  402048:	48 89 df             	mov    %rbx,%rdi
  40204b:	e8 c0 fb ff ff       	call   401c10 <threadwork>
  while (data->running == 1) {
  402050:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  402054:	74 92                	je     401fe8 <work+0x98>
  402056:	eb cc                	jmp    402024 <work+0xd4>
  402058:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000402060 <work2>:
  while (data->running == 1) {
  402060:	eb 0b                	jmp    40206d <work2+0xd>
  402062:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  402068:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  40206d:	83 7f 64 01          	cmpl   $0x1,0x64(%rdi)
  402071:	74 f5                	je     402068 <work2+0x8>
}
  402073:	c3                   	ret

Disassembly of section .fini:

0000000000402074 <_fini>:
  402074:	f3 0f 1e fa          	endbr64
  402078:	48 83 ec 08          	sub    $0x8,%rsp
  40207c:	48 83 c4 08          	add    $0x8,%rsp
  402080:	c3                   	ret
