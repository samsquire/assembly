
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
  401020:	ff 35 72 2f 00 00    	push   0x2f72(%rip)        # 403f98 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 74 2f 00 00    	jmp    *0x2f74(%rip)        # 403fa0 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <pthread_setaffinity_np@plt>:
  401030:	ff 25 72 2f 00 00    	jmp    *0x2f72(%rip)        # 403fa8 <pthread_setaffinity_np@GLIBC_2.34>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <puts@plt>:
  401040:	ff 25 6a 2f 00 00    	jmp    *0x2f6a(%rip)        # 403fb0 <puts@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <clock_gettime@plt>:
  401050:	ff 25 62 2f 00 00    	jmp    *0x2f62(%rip)        # 403fb8 <clock_gettime@GLIBC_2.17>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <__stack_chk_fail@plt>:
  401060:	ff 25 5a 2f 00 00    	jmp    *0x2f5a(%rip)        # 403fc0 <__stack_chk_fail@GLIBC_2.4>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <nanosleep@plt>:
  401070:	ff 25 52 2f 00 00    	jmp    *0x2f52(%rip)        # 403fc8 <nanosleep@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <calloc@plt>:
  401080:	ff 25 4a 2f 00 00    	jmp    *0x2f4a(%rip)        # 403fd0 <calloc@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <__printf_chk@plt>:
  401090:	ff 25 42 2f 00 00    	jmp    *0x2f42(%rip)        # 403fd8 <__printf_chk@GLIBC_2.3.4>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <pthread_create@plt>:
  4010a0:	ff 25 3a 2f 00 00    	jmp    *0x2f3a(%rip)        # 403fe0 <pthread_create@GLIBC_2.34>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <pthread_join@plt>:
  4010b0:	ff 25 32 2f 00 00    	jmp    *0x2f32(%rip)        # 403fe8 <pthread_join@GLIBC_2.34>
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
  4010cc:	48 8d 35 54 0f 00 00 	lea    0xf54(%rip),%rsi        # 402027 <_IO_stdin_used+0x27>
  4010d3:	41 56                	push   %r14
  long offset = 0;
  long chunkslen = 0xffffffff;
  long worksize = chunkslen * worksize_each;
  int buckets = worksize / threadsize;
  long chunksize = ceil((double) worksize / (double) chunkslen);
  char *works = calloc(worksize, sizeof(char));
  4010d5:	41 be ff ff ff ff    	mov    $0xffffffff,%r14d
int main(int argc, char **argv) {
  4010db:	41 55                	push   %r13
 // for (int i = 0; i < worksize; i++) {
   // works[i].taskindex = 2;
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  4010dd:	45 31 ed             	xor    %r13d,%r13d
int main(int argc, char **argv) {
  4010e0:	41 54                	push   %r12
  4010e2:	55                   	push   %rbp
  4010e3:	53                   	push   %rbx
  4010e4:	48 83 ec 78          	sub    $0x78,%rsp
  4010e8:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4010f1:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  4010f6:	31 c0                	xor    %eax,%eax
  4010f8:	e8 93 ff ff ff       	call   401090 <__printf_chk@plt>
  4010fd:	ba 04 00 00 00       	mov    $0x4,%edx
  401102:	48 8d 35 30 0f 00 00 	lea    0xf30(%rip),%rsi        # 402039 <_IO_stdin_used+0x39>
  401109:	31 c0                	xor    %eax,%eax
  40110b:	bf 01 00 00 00       	mov    $0x1,%edi
  401110:	e8 7b ff ff ff       	call   401090 <__printf_chk@plt>
  401115:	ba 20 00 00 00       	mov    $0x20,%edx
  40111a:	48 8d 35 14 0f 00 00 	lea    0xf14(%rip),%rsi        # 402035 <_IO_stdin_used+0x35>
  401121:	31 c0                	xor    %eax,%eax
  401123:	bf 01 00 00 00       	mov    $0x1,%edi
  401128:	e8 63 ff ff ff       	call   401090 <__printf_chk@plt>
  40112d:	ba 0e 00 00 00       	mov    $0xe,%edx
  401132:	48 8d 35 0f 0f 00 00 	lea    0xf0f(%rip),%rsi        # 402048 <_IO_stdin_used+0x48>
  401139:	31 c0                	xor    %eax,%eax
  40113b:	bf 01 00 00 00       	mov    $0x1,%edi
  401140:	e8 4b ff ff ff       	call   401090 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401145:	be 08 00 00 00       	mov    $0x8,%esi
  40114a:	bf 0e 00 00 00       	mov    $0xe,%edi
  40114f:	e8 2c ff ff ff       	call   401080 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401154:	be 38 00 00 00       	mov    $0x38,%esi
  401159:	bf 0e 00 00 00       	mov    $0xe,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40115e:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401163:	e8 18 ff ff ff       	call   401080 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401168:	be 00 31 00 00       	mov    $0x3100,%esi
  40116d:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401172:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401177:	e8 04 ff ff ff       	call   401080 <calloc@plt>
  char *works = calloc(worksize, sizeof(char));
  40117c:	4c 89 f7             	mov    %r14,%rdi
  40117f:	be 01 00 00 00       	mov    $0x1,%esi
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401184:	48 89 c3             	mov    %rax,%rbx
  char *works = calloc(worksize, sizeof(char));
  401187:	e8 f4 fe ff ff       	call   401080 <calloc@plt>
  40118c:	4c 89 f2             	mov    %r14,%rdx
  40118f:	bf 01 00 00 00       	mov    $0x1,%edi
  401194:	48 8d 35 c2 0e 00 00 	lea    0xec2(%rip),%rsi        # 40205d <_IO_stdin_used+0x5d>
  40119b:	49 89 c4             	mov    %rax,%r12
  40119e:	31 c0                	xor    %eax,%eax
  4011a0:	e8 eb fe ff ff       	call   401090 <__printf_chk@plt>
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4011a5:	be 20 00 00 00       	mov    $0x20,%esi
  4011aa:	bf 64 00 00 00       	mov    $0x64,%edi
  4011af:	e8 cc fe ff ff       	call   401080 <calloc@plt>
  4011b4:	31 d2                	xor    %edx,%edx
  4011b6:	bf 01 00 00 00       	mov    $0x1,%edi
  4011bb:	48 8d 35 ac 0e 00 00 	lea    0xeac(%rip),%rsi        # 40206e <_IO_stdin_used+0x6e>
  4011c2:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  4011c7:	31 c0                	xor    %eax,%eax
  4011c9:	e8 c2 fe ff ff       	call   401090 <__printf_chk@plt>
  4011ce:	4c 89 f2             	mov    %r14,%rdx
  4011d1:	bf 01 00 00 00       	mov    $0x1,%edi
  4011d6:	31 c0                	xor    %eax,%eax
  4011d8:	48 8d 35 9a 0e 00 00 	lea    0xe9a(%rip),%rsi        # 402079 <_IO_stdin_used+0x79>
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  data[0].works = works;
  4011df:	49 89 de             	mov    %rbx,%r14
  4011e2:	e8 a9 fe ff ff       	call   401090 <__printf_chk@plt>
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  4011e7:	be 04 00 00 00       	mov    $0x4,%esi
  4011ec:	bf 0e 00 00 00       	mov    $0xe,%edi
  4011f1:	e8 8a fe ff ff       	call   401080 <calloc@plt>
  4011f6:	66 48 0f 6e f3       	movq   %rbx,%xmm6
  data[0].works = works;
  4011fb:	4c 89 63 70          	mov    %r12,0x70(%rbx)
  4011ff:	45 31 e4             	xor    %r12d,%r12d
  401202:	66 48 0f 6e e8       	movq   %rax,%xmm5
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  401207:	48 89 c5             	mov    %rax,%rbp
  40120a:	66 0f 6c ee          	punpcklqdq %xmm6,%xmm5
  40120e:	0f 29 6c 24 10       	movaps %xmm5,0x10(%rsp)
  for (int x = 0; x < threadsize ; x++) {
  401213:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401218:	45 89 ef             	mov    %r13d,%r15d
  40121b:	be 80 00 00 00       	mov    $0x80,%esi
  401220:	bf 01 00 00 00       	mov    $0x1,%edi
    CPU_SET(cpu += 1, data[x].cpu_set);
  401225:	41 83 c5 01          	add    $0x1,%r13d
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401229:	e8 52 fe ff ff       	call   401080 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  40122e:	44 89 e9             	mov    %r13d,%ecx
  401231:	ba 01 00 00 00       	mov    $0x1,%edx
  401236:	48 8d 35 4b 0f 00 00 	lea    0xf4b(%rip),%rsi        # 402188 <_IO_stdin_used+0x188>
  40123d:	48 d3 e2             	shl    %cl,%rdx
  401240:	48 09 10             	or     %rdx,(%rax)
  401243:	44 89 e9             	mov    %r13d,%ecx
  401246:	44 89 fa             	mov    %r15d,%edx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401249:	49 89 46 78          	mov    %rax,0x78(%r14)
  40124d:	bf 01 00 00 00       	mov    $0x1,%edi
  401252:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  401254:	48 83 c5 04          	add    $0x4,%rbp
  401258:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  40125f:	e8 2c fe ff ff       	call   401090 <__printf_chk@plt>
    data[x].threadindex = x;
    data[x].worksize = worksize;
    
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].readies = readies;
  401264:	66 0f 6f 4c 24 10    	movdqa 0x10(%rsp),%xmm1
    data[x].running = 1;
  40126a:	48 8b 05 67 0f 00 00 	mov    0xf67(%rip),%rax        # 4021d8 <_IO_stdin_used+0x1d8>
    data[x].bucketstart = x * buckets ;
  401271:	45 89 a6 18 fd ff ff 	mov    %r12d,-0x2e8(%r14)
    data[x].readies[x] = 0;
    data[x].buckets = buckets;
    data[x].main = &data[0];
    data[x].threads = data;
    
    data[x].read = 0;
  401278:	66 0f 6f 15 70 0f 00 00 	movdqa 0xf70(%rip),%xmm2        # 4021f0 <_IO_stdin_used+0x1f0>
    data[x].newmask = 0;
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401280:	be 30 00 00 00       	mov    $0x30,%esi
    data[x].chunkslen = chunkslen;
  401285:	66 0f 6f 1d 73 0f 00 00 	movdqa 0xf73(%rip),%xmm3        # 402200 <_IO_stdin_used+0x200>
    data[x].loglevel = debug;
  40128d:	41 c7 86 00 fd ff ff 00 00 00 00 	movl   $0x0,-0x300(%r14)
    data[x].running = 1;
  401298:	49 89 86 dc fc ff ff 	mov    %rax,-0x324(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40129f:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].buckets = buckets;
  4012a4:	48 8b 05 35 0f 00 00 	mov    0xf35(%rip),%rax        # 4021e0 <_IO_stdin_used+0x1e0>
  for (int x = 0; x < threadsize ; x++) {
  4012ab:	41 81 c4 92 24 49 12 	add    $0x12492492,%r12d
    data[x].prevread = threadsize;
  4012b2:	66 0f 6f 25 56 0f 00 00 	movdqa 0xf56(%rip),%xmm4        # 402210 <_IO_stdin_used+0x210>
    data[x].threadindex = x;
  4012ba:	45 89 be e4 fc ff ff 	mov    %r15d,-0x31c(%r14)
    data[x].buckets = buckets;
  4012c1:	49 89 86 10 fd ff ff 	mov    %rax,-0x2f0(%r14)
    data[x].freelist = freelist;
  4012c8:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    data[x].threadsize = threadsize;
  4012cd:	41 c7 86 e8 fc ff ff 0e 00 00 00 	movl   $0xe,-0x318(%r14)
    data[x].readies[x] = 0;
  4012d8:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
    data[x].threads = data;
  4012df:	49 89 9e b0 fc ff ff 	mov    %rbx,-0x350(%r14)
    data[x].readcursor = threadsize - 1;
  4012e6:	41 c7 86 80 fe ff ff 0d 00 00 00 	movl   $0xd,-0x180(%r14)
    data[x].writecursor = threadsize - 1;
  4012f1:	41 c7 86 00 fe ff ff 0d 00 00 00 	movl   $0xd,-0x200(%r14)
    data[x].freelist = freelist;
  4012fc:	49 89 86 20 fd ff ff 	mov    %rax,-0x2e0(%r14)
    data[x].newmask = 0;
  401303:	41 c7 86 48 fd ff ff 00 00 00 00 	movl   $0x0,-0x2b8(%r14)
    data[x].thiswrite = threadsize;
  40130e:	41 c7 46 a8 0e 00 00 00 	movl   $0xe,-0x58(%r14)
    data[x].readies = readies;
  401316:	41 0f 29 8e a0 fc ff ff 	movaps %xmm1,-0x360(%r14)
    data[x].read = 0;
  40131e:	41 0f 29 96 80 fc ff ff 	movaps %xmm2,-0x380(%r14)
    data[x].chunkslen = chunkslen;
  401326:	41 0f 11 9e 38 fd ff ff 	movups %xmm3,-0x2c8(%r14)
    data[x].prevread = threadsize;
  40132e:	41 0f 11 66 88       	movups %xmm4,-0x78(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401333:	e8 48 fd ff ff       	call   401080 <calloc@plt>
    data[x].epochssize = epochs;
    
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  401338:	be 30 00 00 00       	mov    $0x30,%esi
  40133d:	bf 10 27 00 00       	mov    $0x2710,%edi
    data[x].epochssize = epochs;
  401342:	41 c7 46 a0 80 96 98 00 	movl   $0x989680,-0x60(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40134a:	49 89 46 98          	mov    %rax,-0x68(%r14)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  40134e:	e8 2d fd ff ff       	call   401080 <calloc@plt>
  401353:	49 89 46 b0          	mov    %rax,-0x50(%r14)
  for (int x = 0; x < threadsize ; x++) {
  401357:	41 83 fd 0e          	cmp    $0xe,%r13d
  40135b:	0f 85 b7 fe ff ff    	jne    401218 <main+0x158>
  401361:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
  401366:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
  40136b:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  401370:	49 c7 c5 b0 1e 40 00 	mov    $0x401eb0,%r13
  401377:	48 8d 85 10 03 00 00 	lea    0x310(%rbp),%rax
  40137e:	4d 89 fc             	mov    %r15,%r12
  401381:	49 89 c6             	mov    %rax,%r14
  401384:	0f 1f 40 00          	nopl   0x0(%rax)
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  401388:	48 89 d9             	mov    %rbx,%rcx
  40138b:	48 89 ee             	mov    %rbp,%rsi
  40138e:	4c 89 ff             	mov    %r15,%rdi
  401391:	4c 89 ea             	mov    %r13,%rdx
  401394:	e8 07 fd ff ff       	call   4010a0 <pthread_create@plt>
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401399:	48 8b 53 78          	mov    0x78(%rbx),%rdx
  40139d:	49 8b 3f             	mov    (%r15),%rdi
  4013a0:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  4013a5:	48 83 c5 38          	add    $0x38,%rbp
  4013a9:	49 83 c7 08          	add    $0x8,%r15
  4013ad:	48 81 c3 80 03 00 00 	add    $0x380,%rbx
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4013b4:	e8 77 fc ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  4013b9:	4c 39 f5             	cmp    %r14,%rbp
  4013bc:	75 ca                	jne    401388 <main+0x2c8>
  }
  
  struct timespec time = {
  4013be:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  4013c3:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  4013c8:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec time = {
  4013cd:	66 0f 6f 05 4b 0e 00 00 	movdqa 0xe4b(%rip),%xmm0        # 402220 <_IO_stdin_used+0x220>
  4013d5:	4c 8d 6c 24 38       	lea    0x38(%rsp),%r13
  4013da:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  4013df:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4013e3:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  4013e8:	e8 83 fc ff ff       	call   401070 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  4013ed:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
  4013f2:	c7 43 5c 00 00 00 00 	movl   $0x0,0x5c(%rbx)
  4013f9:	c7 83 dc 03 00 00 00 00 00 00 	movl   $0x0,0x3dc(%rbx)
  401403:	c7 83 5c 07 00 00 00 00 00 00 	movl   $0x0,0x75c(%rbx)
  40140d:	48 83 c5 70          	add    $0x70,%rbp
  401411:	c7 83 dc 0a 00 00 00 00 00 00 	movl   $0x0,0xadc(%rbx)
  40141b:	c7 83 5c 0e 00 00 00 00 00 00 	movl   $0x0,0xe5c(%rbx)
  401425:	c7 83 dc 11 00 00 00 00 00 00 	movl   $0x0,0x11dc(%rbx)
  40142f:	c7 83 5c 15 00 00 00 00 00 00 	movl   $0x0,0x155c(%rbx)
  401439:	c7 83 dc 18 00 00 00 00 00 00 	movl   $0x0,0x18dc(%rbx)
  401443:	c7 83 5c 1c 00 00 00 00 00 00 	movl   $0x0,0x1c5c(%rbx)
  40144d:	c7 83 dc 1f 00 00 00 00 00 00 	movl   $0x0,0x1fdc(%rbx)
  401457:	c7 83 5c 23 00 00 00 00 00 00 	movl   $0x0,0x235c(%rbx)
  401461:	c7 83 dc 26 00 00 00 00 00 00 	movl   $0x0,0x26dc(%rbx)
  40146b:	c7 83 5c 2a 00 00 00 00 00 00 	movl   $0x0,0x2a5c(%rbx)
  401475:	c7 83 dc 2d 00 00 00 00 00 00 	movl   $0x0,0x2ddc(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  40147f:	90                   	nop
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401480:	49 8b 3c 24          	mov    (%r12),%rdi
  401484:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  401487:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  40148b:	e8 20 fc ff ff       	call   4010b0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401490:	49 39 ec             	cmp    %rbp,%r12
  401493:	75 eb                	jne    401480 <main+0x3c0>
  401495:	48 8d 3d e9 0b 00 00 	lea    0xbe9(%rip),%rdi        # 402085 <_IO_stdin_used+0x85>
  40149c:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  4014a0:	45 31 e4             	xor    %r12d,%r12d
  4014a3:	e8 98 fb ff ff       	call   401040 <puts@plt>
  long sends = 8;
  for (int x = 0; x < threadsize; x++) {
  4014a8:	4c 8d b3 48 31 00 00 	lea    0x3148(%rbx),%r14
  4014af:	4c 8d 2d e4 0b 00 00 	lea    0xbe4(%rip),%r13        # 40209a <_IO_stdin_used+0x9a>
  4014b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4014c0:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4014c4:	4c 89 ee             	mov    %r13,%rsi
  4014c7:	bf 01 00 00 00       	mov    $0x1,%edi
  4014cc:	31 c0                	xor    %eax,%eax
  4014ce:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
  4014d5:	e8 b6 fb ff ff       	call   401090 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  4014da:	4c 03 a5 80 fc ff ff 	add    -0x380(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  4014e1:	4c 39 f5             	cmp    %r14,%rbp
  4014e4:	75 da                	jne    4014c0 <main+0x400>
  }
  printf("freq: %ld\n", freq/ seconds);
  4014e6:	4c 89 e0             	mov    %r12,%rax
  4014e9:	48 8d 35 b5 0b 00 00 	lea    0xbb5(%rip),%rsi        # 4020a5 <_IO_stdin_used+0xa5>
  4014f0:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
  4014fa:	bf 01 00 00 00       	mov    $0x1,%edi
  4014ff:	48 f7 ed             	imul   %rbp
  401502:	4c 89 e0             	mov    %r12,%rax
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  401505:	49 c1 e4 03          	shl    $0x3,%r12
  401509:	4c 8d b3 50 31 00 00 	lea    0x3150(%rbx),%r14
  printf("freq: %ld\n", freq/ seconds);
  401510:	48 c1 f8 3f          	sar    $0x3f,%rax
  401514:	48 d1 fa             	sar    %rdx
  401517:	48 29 c2             	sub    %rax,%rdx
  40151a:	31 c0                	xor    %eax,%eax
  40151c:	49 89 d5             	mov    %rdx,%r13
  40151f:	e8 6c fb ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  401524:	4c 89 e0             	mov    %r12,%rax
  401527:	49 c1 fc 3f          	sar    $0x3f,%r12
  40152b:	48 8d 35 7e 0b 00 00 	lea    0xb7e(%rip),%rsi        # 4020b0 <_IO_stdin_used+0xb0>
  401532:	48 f7 ed             	imul   %rbp
  401535:	bf 01 00 00 00       	mov    $0x1,%edi
  40153a:	31 c0                	xor    %eax,%eax
  40153c:	48 89 d5             	mov    %rdx,%rbp
  40153f:	48 d1 fd             	sar    %rbp
  401542:	4c 29 e5             	sub    %r12,%rbp
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  401545:	41 bc 00 ca 9a 3b    	mov    $0x3b9aca00,%r12d
  40154b:	48 89 ea             	mov    %rbp,%rdx
  40154e:	e8 3d fb ff ff       	call   401090 <__printf_chk@plt>
  401553:	4c 89 e0             	mov    %r12,%rax
  401556:	bf 01 00 00 00       	mov    $0x1,%edi
  40155b:	48 8d 35 5c 0b 00 00 	lea    0xb5c(%rip),%rsi        # 4020be <_IO_stdin_used+0xbe>
  401562:	48 99                	cqto
  401564:	49 f7 fd             	idiv   %r13
  401567:	49 89 c5             	mov    %rax,%r13
  40156a:	48 89 c2             	mov    %rax,%rdx
  40156d:	31 c0                	xor    %eax,%eax
  40156f:	e8 1c fb ff ff       	call   401090 <__printf_chk@plt>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  401574:	4d 85 ed             	test   %r13,%r13
  401577:	49 8d 55 07          	lea    0x7(%r13),%rdx
  40157b:	48 8d 35 50 0b 00 00 	lea    0xb50(%rip),%rsi        # 4020d2 <_IO_stdin_used+0xd2>
  401582:	49 0f 49 d5          	cmovns %r13,%rdx
  401586:	bf 01 00 00 00       	mov    $0x1,%edi
  40158b:	31 c0                	xor    %eax,%eax
  40158d:	4c 8d 2d 6f 0b 00 00 	lea    0xb6f(%rip),%r13        # 402103 <_IO_stdin_used+0x103>
  401594:	48 c1 fa 03          	sar    $0x3,%rdx
  401598:	e8 f3 fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  40159d:	4c 89 e0             	mov    %r12,%rax
  4015a0:	bf 01 00 00 00       	mov    $0x1,%edi
  long freq_writes = 0;
  4015a5:	45 31 e4             	xor    %r12d,%r12d
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  4015a8:	48 99                	cqto
  4015aa:	48 8d 35 3f 0b 00 00 	lea    0xb3f(%rip),%rsi        # 4020f0 <_IO_stdin_used+0xf0>
  4015b1:	48 f7 fd             	idiv   %rbp
  4015b4:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  4015b8:	48 89 c2             	mov    %rax,%rdx
  4015bb:	31 c0                	xor    %eax,%eax
  4015bd:	e8 ce fa ff ff       	call   401090 <__printf_chk@plt>
  
  for (int x = 0; x < threadsize; x++) {
  4015c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    freq_writes += data[x].freq_writes;
  4015c8:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4015cc:	4c 89 ee             	mov    %r13,%rsi
  4015cf:	bf 01 00 00 00       	mov    $0x1,%edi
  4015d4:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  4015d6:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
    freq_writes += data[x].freq_writes;
  4015dd:	49 01 d4             	add    %rdx,%r12
  4015e0:	e8 ab fa ff ff       	call   401090 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  4015e5:	49 39 ee             	cmp    %rbp,%r14
  4015e8:	75 de                	jne    4015c8 <main+0x508>
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  4015ea:	4c 89 e0             	mov    %r12,%rax
  4015ed:	48 8d 35 1b 0b 00 00 	lea    0xb1b(%rip),%rsi        # 40210f <_IO_stdin_used+0x10f>
  4015f4:	bf 01 00 00 00       	mov    $0x1,%edi
  4015f9:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
  401603:	48 f7 ed             	imul   %rbp
  401606:	4c 89 e0             	mov    %r12,%rax

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  401609:	49 c1 e4 03          	shl    $0x3,%r12
  printf("freq_writes: %ld\n", freq_writes / seconds);
  40160d:	48 c1 f8 3f          	sar    $0x3f,%rax
  401611:	48 d1 fa             	sar    %rdx
  401614:	48 29 c2             	sub    %rax,%rdx
  401617:	31 c0                	xor    %eax,%eax
  401619:	49 89 d5             	mov    %rdx,%r13
  40161c:	e8 6f fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  401621:	4c 89 e0             	mov    %r12,%rax
  401624:	49 c1 fc 3f          	sar    $0x3f,%r12
  401628:	48 8d 35 f2 0a 00 00 	lea    0xaf2(%rip),%rsi        # 402121 <_IO_stdin_used+0x121>
  40162f:	48 f7 ed             	imul   %rbp
  401632:	bf 01 00 00 00       	mov    $0x1,%edi
  401637:	31 c0                	xor    %eax,%eax
  401639:	48 89 d5             	mov    %rdx,%rbp
  40163c:	48 d1 fd             	sar    %rbp
  40163f:	4c 29 e5             	sub    %r12,%rbp
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  401642:	41 bc 00 ca 9a 3b    	mov    $0x3b9aca00,%r12d
  401648:	48 89 ea             	mov    %rbp,%rdx
  40164b:	e8 40 fa ff ff       	call   401090 <__printf_chk@plt>
  401650:	4c 89 e0             	mov    %r12,%rax
  401653:	bf 01 00 00 00       	mov    $0x1,%edi
  401658:	48 8d 35 da 0a 00 00 	lea    0xada(%rip),%rsi        # 402139 <_IO_stdin_used+0x139>
  40165f:	48 99                	cqto
  401661:	49 f7 fd             	idiv   %r13
  401664:	49 89 c5             	mov    %rax,%r13
  401667:	48 89 c2             	mov    %rax,%rdx
  40166a:	31 c0                	xor    %eax,%eax
  40166c:	e8 1f fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes per thread latency: %ld\n", (1000000000/(freq_writes / seconds)) / sends);
  401671:	4d 85 ed             	test   %r13,%r13
  401674:	49 8d 55 07          	lea    0x7(%r13),%rdx
  401678:	48 8d 35 29 0b 00 00 	lea    0xb29(%rip),%rsi        # 4021a8 <_IO_stdin_used+0x1a8>
  40167f:	49 0f 49 d5          	cmovns %r13,%rdx
  401683:	bf 01 00 00 00       	mov    $0x1,%edi
  401688:	31 c0                	xor    %eax,%eax
  40168a:	48 c1 fa 03          	sar    $0x3,%rdx
  40168e:	e8 fd f9 ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * sends) / seconds));
  401693:	4c 89 e0             	mov    %r12,%rax
  401696:	bf 01 00 00 00       	mov    $0x1,%edi
  40169b:	48 8d 35 b2 0a 00 00 	lea    0xab2(%rip),%rsi        # 402154 <_IO_stdin_used+0x154>
  4016a2:	48 99                	cqto
  4016a4:	48 f7 fd             	idiv   %rbp
  4016a7:	48 8d 2d 1f 0a 00 00 	lea    0xa1f(%rip),%rbp        # 4020cd <_IO_stdin_used+0xcd>
  4016ae:	48 89 c2             	mov    %rax,%rdx
  4016b1:	31 c0                	xor    %eax,%eax
  4016b3:	e8 d8 f9 ff ff       	call   401090 <__printf_chk@plt>
  4016b8:	48 8d 3d af 0a 00 00 	lea    0xaaf(%rip),%rdi        # 40216e <_IO_stdin_used+0x16e>
  4016bf:	e8 7c f9 ff ff       	call   401040 <puts@plt>
  4016c4:	48 89 ee             	mov    %rbp,%rsi
  4016c7:	bf 01 00 00 00       	mov    $0x1,%edi
  4016cc:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  4016ce:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  4016d5:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4016dc:	e8 af f9 ff ff       	call   401090 <__printf_chk@plt>
  4016e1:	48 89 ee             	mov    %rbp,%rsi
  4016e4:	bf 01 00 00 00       	mov    $0x1,%edi
  4016e9:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  4016eb:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  4016f2:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4016f9:	e8 92 f9 ff ff       	call   401090 <__printf_chk@plt>
  4016fe:	48 89 ee             	mov    %rbp,%rsi
  401701:	bf 01 00 00 00       	mov    $0x1,%edi
  401706:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  401708:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  40170f:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401716:	e8 75 f9 ff ff       	call   401090 <__printf_chk@plt>
  40171b:	48 89 ee             	mov    %rbp,%rsi
  40171e:	bf 01 00 00 00       	mov    $0x1,%edi
  401723:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  401725:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  40172c:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  401733:	e8 58 f9 ff ff       	call   401090 <__printf_chk@plt>
  401738:	48 89 ee             	mov    %rbp,%rsi
  40173b:	bf 01 00 00 00       	mov    $0x1,%edi
  401740:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  401742:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401749:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  401750:	e8 3b f9 ff ff       	call   401090 <__printf_chk@plt>
  401755:	48 89 ee             	mov    %rbp,%rsi
  401758:	bf 01 00 00 00       	mov    $0x1,%edi
  40175d:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  40175f:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401766:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  40176d:	e8 1e f9 ff ff       	call   401090 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  401772:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  401779:	31 c0                	xor    %eax,%eax
  40177b:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  401782:	48 8d 35 f2 09 00 00 	lea    0x9f2(%rip),%rsi        # 40217b <_IO_stdin_used+0x17b>
  401789:	bf 01 00 00 00       	mov    $0x1,%edi
  40178e:	e8 fd f8 ff ff       	call   401090 <__printf_chk@plt>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  401793:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  401798:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4017a1:	75 11                	jne    4017b4 <main+0x6f4>
  4017a3:	48 83 c4 78          	add    $0x78,%rsp
  4017a7:	31 c0                	xor    %eax,%eax
  4017a9:	5b                   	pop    %rbx
  4017aa:	5d                   	pop    %rbp
  4017ab:	41 5c                	pop    %r12
  4017ad:	41 5d                	pop    %r13
  4017af:	41 5e                	pop    %r14
  4017b1:	41 5f                	pop    %r15
  4017b3:	c3                   	ret
  4017b4:	e8 a7 f8 ff ff       	call   401060 <__stack_chk_fail@plt>
  4017b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000004017c0 <_start>:
  4017c0:	f3 0f 1e fa          	endbr64
  4017c4:	31 ed                	xor    %ebp,%ebp
  4017c6:	49 89 d1             	mov    %rdx,%r9
  4017c9:	5e                   	pop    %rsi
  4017ca:	48 89 e2             	mov    %rsp,%rdx
  4017cd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4017d1:	50                   	push   %rax
  4017d2:	54                   	push   %rsp
  4017d3:	45 31 c0             	xor    %r8d,%r8d
  4017d6:	31 c9                	xor    %ecx,%ecx
  4017d8:	48 c7 c7 c0 10 40 00 	mov    $0x4010c0,%rdi
  4017df:	ff 15 0b 28 00 00    	call   *0x280b(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  4017e5:	f4                   	hlt
  4017e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004017f0 <_dl_relocate_static_pie>:
  4017f0:	f3 0f 1e fa          	endbr64
  4017f4:	c3                   	ret
  4017f5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4017ff:	90                   	nop

0000000000401800 <deregister_tm_clones>:
  401800:	b8 10 40 40 00       	mov    $0x404010,%eax
  401805:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  40180b:	74 13                	je     401820 <deregister_tm_clones+0x20>
  40180d:	b8 00 00 00 00       	mov    $0x0,%eax
  401812:	48 85 c0             	test   %rax,%rax
  401815:	74 09                	je     401820 <deregister_tm_clones+0x20>
  401817:	bf 10 40 40 00       	mov    $0x404010,%edi
  40181c:	ff e0                	jmp    *%rax
  40181e:	66 90                	xchg   %ax,%ax
  401820:	c3                   	ret
  401821:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40182c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401830 <register_tm_clones>:
  401830:	be 10 40 40 00       	mov    $0x404010,%esi
  401835:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  40183c:	48 89 f0             	mov    %rsi,%rax
  40183f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401843:	48 c1 f8 03          	sar    $0x3,%rax
  401847:	48 01 c6             	add    %rax,%rsi
  40184a:	48 d1 fe             	sar    %rsi
  40184d:	74 11                	je     401860 <register_tm_clones+0x30>
  40184f:	b8 00 00 00 00       	mov    $0x0,%eax
  401854:	48 85 c0             	test   %rax,%rax
  401857:	74 07                	je     401860 <register_tm_clones+0x30>
  401859:	bf 10 40 40 00       	mov    $0x404010,%edi
  40185e:	ff e0                	jmp    *%rax
  401860:	c3                   	ret
  401861:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40186c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401870 <__do_global_dtors_aux>:
  401870:	f3 0f 1e fa          	endbr64
  401874:	80 3d 95 27 00 00 00 	cmpb   $0x0,0x2795(%rip)        # 404010 <__TMC_END__>
  40187b:	75 13                	jne    401890 <__do_global_dtors_aux+0x20>
  40187d:	55                   	push   %rbp
  40187e:	48 89 e5             	mov    %rsp,%rbp
  401881:	e8 7a ff ff ff       	call   401800 <deregister_tm_clones>
  401886:	c6 05 83 27 00 00 01 	movb   $0x1,0x2783(%rip)        # 404010 <__TMC_END__>
  40188d:	5d                   	pop    %rbp
  40188e:	c3                   	ret
  40188f:	90                   	nop
  401890:	c3                   	ret
  401891:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40189c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004018a0 <frame_dummy>:
  4018a0:	f3 0f 1e fa          	endbr64
  4018a4:	eb 8a                	jmp    401830 <register_tm_clones>
  4018a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004018b0 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  4018b0:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4018b4:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  4018b7:	7e 77                	jle    401930 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  4018b9:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4018bd:	55                   	push   %rbp
  4018be:	49 89 f2             	mov    %rsi,%r10
  4018c1:	49 89 d3             	mov    %rdx,%r11
  4018c4:	53                   	push   %rbx
  4018c5:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  4018c8:	48 8b 98 a0 03 00 00 	mov    0x3a0(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  4018cf:	b8 01 00 00 00       	mov    $0x1,%eax
  4018d4:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  4018d8:	48 63 d0             	movslq %eax,%rdx
  4018db:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  4018de:	85 d2                	test   %edx,%edx
  4018e0:	40 0f 94 c6          	sete   %sil
  4018e4:	f6 c2 04             	test   $0x4,%dl
  4018e7:	75 05                	jne    4018ee <pollthreads+0x3e>
  4018e9:	40 84 f6             	test   %sil,%sil
  4018ec:	74 0d                	je     4018fb <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  4018ee:	49 63 08             	movslq (%r8),%rcx
  4018f1:	8d 69 01             	lea    0x1(%rcx),%ebp
  4018f4:	41 89 28             	mov    %ebp,(%r8)
  4018f7:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  4018fb:	83 e2 08             	and    $0x8,%edx
  4018fe:	75 05                	jne    401905 <pollthreads+0x55>
  401900:	40 84 f6             	test   %sil,%sil
  401903:	74 1b                	je     401920 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  401905:	48 63 17             	movslq (%rdi),%rdx
  401908:	8d 4a 01             	lea    0x1(%rdx),%ecx
  40190b:	89 0f                	mov    %ecx,(%rdi)
  40190d:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  401911:	83 c0 01             	add    $0x1,%eax
  401914:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401918:	7f be                	jg     4018d8 <pollthreads+0x28>
}
  40191a:	31 c0                	xor    %eax,%eax
  40191c:	5b                   	pop    %rbx
  40191d:	5d                   	pop    %rbp
  40191e:	c3                   	ret
  40191f:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  401920:	83 c0 01             	add    $0x1,%eax
  401923:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401927:	7f af                	jg     4018d8 <pollthreads+0x28>
}
  401929:	31 c0                	xor    %eax,%eax
  40192b:	5b                   	pop    %rbx
  40192c:	5d                   	pop    %rbp
  40192d:	c3                   	ret
  40192e:	66 90                	xchg   %ax,%ax
  401930:	31 c0                	xor    %eax,%eax
  401932:	c3                   	ret
  401933:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40193e:	66 90                	xchg   %ax,%ax

0000000000401940 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401940:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401943:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
      if (*availableidx == 0) {
  40194a:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40194d:	48 83 c7 01          	add    $0x1,%rdi
  401951:	48 85 ff             	test   %rdi,%rdi
  401954:	7e 66                	jle    4019bc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401956:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40195d:	31 c9                	xor    %ecx,%ecx
  40195f:	45 31 c9             	xor    %r9d,%r9d
  401962:	31 c0                	xor    %eax,%eax
  401964:	eb 18                	jmp    40197e <findavailable+0x3e>
  401966:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401970:	83 c1 01             	add    $0x1,%ecx
  401973:	48 63 c1             	movslq %ecx,%rax
  401976:	49 89 c1             	mov    %rax,%r9
  401979:	48 39 f8             	cmp    %rdi,%rax
  40197c:	7d 3e                	jge    4019bc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  40197e:	48 c1 e0 05          	shl    $0x5,%rax
  401982:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401988:	75 e6                	jne    401970 <findavailable+0x30>
         available[*availableidx] = x;
  40198a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  40198d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401991:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401995:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401998:	41 8b 43 68          	mov    0x68(%r11),%eax
  40199c:	01 c0                	add    %eax,%eax
  40199e:	41 39 c0             	cmp    %eax,%r8d
  4019a1:	74 19                	je     4019bc <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4019a3:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  4019aa:	83 c1 01             	add    $0x1,%ecx
  4019ad:	48 63 c1             	movslq %ecx,%rax
  4019b0:	48 83 c7 01          	add    $0x1,%rdi
  4019b4:	49 89 c1             	mov    %rax,%r9
  4019b7:	48 39 f8             	cmp    %rdi,%rax
  4019ba:	7c c2                	jl     40197e <findavailable+0x3e>
      if (*availableidx == 0) {
  4019bc:	31 c0                	xor    %eax,%eax
  4019be:	45 85 c0             	test   %r8d,%r8d
  4019c1:	0f 94 c0             	sete   %al
}
  4019c4:	c3                   	ret
  4019c5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000004019d0 <singlewriter3>:
}
  4019d0:	c3                   	ret
  4019d1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4019dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004019e0 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4019e0:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  4019e6:	85 c0                	test   %eax,%eax
  4019e8:	74 1e                	je     401a08 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  4019ea:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4019ec:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  4019ed:	55                   	push   %rbp
  4019ee:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4019ef:	8b 77 68             	mov    0x68(%rdi),%esi
  4019f2:	48 89 fb             	mov    %rdi,%rbx
  4019f5:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  4019f8:	f7 f9                	idiv   %ecx
  4019fa:	85 d2                	test   %edx,%edx
  4019fc:	74 12                	je     401a10 <singlewriter2+0x30>
}
  4019fe:	5b                   	pop    %rbx
  4019ff:	5d                   	pop    %rbp
  401a00:	41 5c                	pop    %r12
  401a02:	c3                   	ret
  401a03:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401a08:	c3                   	ret
  401a09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct Data * thread = &data->threads[data->threadindex];
  401a10:	48 63 47 64          	movslq 0x64(%rdi),%rax
  401a14:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  401a1c:	48 29 c5             	sub    %rax,%rbp
  401a1f:	48 c1 e5 07          	shl    $0x7,%rbp
  401a23:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401a27:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401a2c:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401a33:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401a37:	49 c1 e4 04          	shl    $0x4,%r12
  401a3b:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401a42:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401a47:	e8 04 f6 ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401a4c:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401a52:	83 c0 01             	add    $0x1,%eax
  401a55:	99                   	cltd
  401a56:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  401a5c:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401a5f:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401a65:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401a69:	48 8b 05 60 07 00 00 	mov    0x760(%rip),%rax        # 4021d0 <_IO_stdin_used+0x1d0>
  401a70:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  401a75:	5b                   	pop    %rbx
  401a76:	5d                   	pop    %rbp
  401a77:	41 5c                	pop    %r12
  401a79:	c3                   	ret
  401a7a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000401a80 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a80:	41 55                	push   %r13
  401a82:	49 89 d5             	mov    %rdx,%r13
  401a85:	41 54                	push   %r12
  401a87:	49 89 cc             	mov    %rcx,%r12
  401a8a:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401a8b:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a8e:	48 89 fd             	mov    %rdi,%rbp
  401a91:	53                   	push   %rbx
  401a92:	48 89 f3             	mov    %rsi,%rbx
  401a95:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401a99:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a9d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401aa6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401aab:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401aad:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401ab5:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  401abb:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401ac3:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401acb:	83 c0 01             	add    $0x1,%eax
  401ace:	99                   	cltd
  401acf:	f7 7f 68             	idivl  0x68(%rdi)
  401ad2:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401ad8:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401add:	4c 89 e9             	mov    %r13,%rcx
  401ae0:	e8 5b fe ff ff       	call   401940 <findavailable>
  if (fill == 1) {
  401ae5:	83 f8 01             	cmp    $0x1,%eax
  401ae8:	0f 84 64 01 00 00    	je     401c52 <singlewriter+0x1d2>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401aee:	48 89 ef             	mov    %rbp,%rdi
  401af1:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401af6:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401afb:	4c 89 e2             	mov    %r12,%rdx
  401afe:	4c 89 ee             	mov    %r13,%rsi
  401b01:	e8 aa fd ff ff       	call   4018b0 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401b06:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401b0b:	85 ff                	test   %edi,%edi
  401b0d:	0f 8e 66 01 00 00    	jle    401c79 <singlewriter+0x1f9>
  401b13:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401b18:	31 c9                	xor    %ecx,%ecx
  401b1a:	eb 62                	jmp    401b7e <singlewriter+0xfe>
  401b1c:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b20:	48 8b 14 cb          	mov    (%rbx,%rcx,8),%rdx
          int thread = readyreaders[x];
  401b24:	4d 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%r10
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b29:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401b2c:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b30:	48 c1 e2 05          	shl    $0x5,%rdx
  401b34:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].reading = chunk;
  401b3b:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
          data->threads[thread].start = start;
  401b43:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401b47:	66 0f 6e 4a 08       	movd   0x8(%rdx),%xmm1
          data->threads[thread].reading = chunk;
  401b4c:	4c 29 d0             	sub    %r10,%rax
          chunk->available = READING;
  401b4f:	c7 42 10 02 00 00 00 	movl   $0x2,0x10(%rdx)
          data->threads[thread].reading = chunk;
  401b56:	48 c1 e0 07          	shl    $0x7,%rax
  401b5a:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].start = start;
  401b5e:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401b62:	48 89 90 a8 00 00 00 	mov    %rdx,0xa8(%rax)
          chunk->owner = thread;
  401b69:	44 89 52 14          	mov    %r10d,0x14(%rdx)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401b6d:	83 88 c8 00 00 00 10 	orl    $0x10,0xc8(%rax)
          data->threads[thread].start = start;
  401b74:	66 0f d6 40 14       	movq   %xmm0,0x14(%rax)
        for (int x = 0; x < readers ; x++) {
  401b79:	48 39 cf             	cmp    %rcx,%rdi
  401b7c:	74 07                	je     401b85 <singlewriter+0x105>
  401b7e:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401b80:	4c 39 c1             	cmp    %r8,%rcx
  401b83:	75 9b                	jne    401b20 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401b85:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401b8a:	45 85 c0             	test   %r8d,%r8d
  401b8d:	7e 7a                	jle    401c09 <singlewriter+0x189>
                if (assignedchunk  == availableidx) {
  401b8f:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401b93:	41 01 f0             	add    %esi,%r8d
  401b96:	eb 6d                	jmp    401c05 <singlewriter+0x185>
  401b98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401ba0:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401ba3:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401ba6:	45 8b 0c 24          	mov    (%r12),%r9d
   for (int x = 0; x < writers ; x++) {
  401baa:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401bae:	48 8b 14 f3          	mov    (%rbx,%rsi,8),%rdx
          data->threads[thread].writing = chunk;
  401bb2:	49 63 f1             	movslq %r9d,%rsi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401bb5:	48 c1 e2 05          	shl    $0x5,%rdx
  401bb9:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].writing = chunk;
  401bc0:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
          data->threads[thread].publishstart = start;
  401bc8:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401bcc:	66 0f 6e 52 08       	movd   0x8(%rdx),%xmm2
          data->threads[thread].writing = chunk;
  401bd1:	48 29 f0             	sub    %rsi,%rax
      chunk->available = WRITING;
  401bd4:	c7 42 10 03 00 00 00 	movl   $0x3,0x10(%rdx)
          data->threads[thread].writing = chunk;
  401bdb:	48 c1 e0 07          	shl    $0x7,%rax
  401bdf:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].publishstart = start;
  401be3:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401be7:	48 89 90 b0 00 00 00 	mov    %rdx,0xb0(%rax)
          chunk->owner = thread;
  401bee:	44 89 4a 14          	mov    %r9d,0x14(%rdx)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401bf2:	83 88 c8 00 00 00 20 	orl    $0x20,0xc8(%rax)
          data->threads[thread].publishstart = start;
  401bf9:	66 0f d6 40 40       	movq   %xmm0,0x40(%rax)
   for (int x = 0; x < writers ; x++) {
  401bfe:	44 39 c1             	cmp    %r8d,%ecx
  401c01:	74 06                	je     401c09 <singlewriter+0x189>
  401c03:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401c05:	39 f7                	cmp    %esi,%edi
  401c07:	75 97                	jne    401ba0 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401c09:	8b 7d 68             	mov    0x68(%rbp),%edi
  401c0c:	85 ff                	test   %edi,%edi
  401c0e:	7e 40                	jle    401c50 <singlewriter+0x1d0>
        if (data->threads[x].newmask != 0) {
  401c10:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401c14:	31 d2                	xor    %edx,%edx
  401c16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401c20:	48 63 ca             	movslq %edx,%rcx
  401c23:	48 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rax
  401c2b:	48 29 c8             	sub    %rcx,%rax
  401c2e:	48 c1 e0 07          	shl    $0x7,%rax
  401c32:	4c 01 c0             	add    %r8,%rax
  401c35:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401c3b:	85 f6                	test   %esi,%esi
  401c3d:	74 31                	je     401c70 <singlewriter+0x1f0>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401c3f:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401c43:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401c46:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401c49:	8b 7d 68             	mov    0x68(%rbp),%edi
  401c4c:	39 fa                	cmp    %edi,%edx
  401c4e:	7c d0                	jl     401c20 <singlewriter+0x1a0>
  return 0;
  401c50:	31 c0                	xor    %eax,%eax
}
  401c52:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401c57:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401c60:	75 1e                	jne    401c80 <singlewriter+0x200>
  401c62:	48 83 c4 28          	add    $0x28,%rsp
  401c66:	5b                   	pop    %rbx
  401c67:	5d                   	pop    %rbp
  401c68:	41 5c                	pop    %r12
  401c6a:	41 5d                	pop    %r13
  401c6c:	c3                   	ret
  401c6d:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401c70:	83 c2 01             	add    $0x1,%edx
  401c73:	39 fa                	cmp    %edi,%edx
  401c75:	7c a9                	jl     401c20 <singlewriter+0x1a0>
  401c77:	eb d7                	jmp    401c50 <singlewriter+0x1d0>
      int assignedchunk = 0;
  401c79:	31 f6                	xor    %esi,%esi
  401c7b:	e9 05 ff ff ff       	jmp    401b85 <singlewriter+0x105>
}
  401c80:	e8 db f3 ff ff       	call   401060 <__stack_chk_fail@plt>
  401c85:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401c90 <threadwork>:
int * threadwork(struct Data * data) {
  401c90:	55                   	push   %rbp
  401c91:	53                   	push   %rbx
  401c92:	48 89 fb             	mov    %rdi,%rbx
  401c95:	48 83 ec 28          	sub    $0x28,%rsp
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401c99:	48 63 4f 68          	movslq 0x68(%rdi),%rcx
  long thiswrite = data->main->globalwrite;
  401c9d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401ca6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401cab:	48 8b 47 28          	mov    0x28(%rdi),%rax
  401caf:	48 8b a8 50 03 00 00 	mov    0x350(%rax),%rbp
  long lastcursor = data->main->writecursor;
  401cb6:	8b b0 80 01 00 00    	mov    0x180(%rax),%esi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401cbc:	48 8b 80 38 03 00 00 	mov    0x338(%rax),%rax
    data->thiswrite = lastcursor;
  401cc3:	89 b7 28 03 00 00    	mov    %esi,0x328(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401cc9:	48 89 e6             	mov    %rsp,%rsi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401ccc:	48 99                	cqto
  401cce:	48 f7 f9             	idiv   %rcx
    data->prevwrite = lastwrite;
  401cd1:	48 89 97 10 03 00 00 	mov    %rdx,0x310(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401cd8:	bf 04 00 00 00       	mov    $0x4,%edi
  401cdd:	e8 6e f3 ff ff       	call   401050 <clock_gettime@plt>
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401ce2:	4c 8b 53 28          	mov    0x28(%rbx),%r10
  401ce6:	48 63 4b 68          	movslq 0x68(%rbx),%rcx
  401cea:	48 bf 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%rdi
  401cf4:	44 8b 4b 64          	mov    0x64(%rbx),%r9d
   data->freq_writes++;
  401cf8:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401cfd:	49 8b 82 50 03 00 00 	mov    0x350(%r10),%rax
        epoch->time = time;
  401d04:	66 0f 6f 04 24       	movdqa (%rsp),%xmm0
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401d09:	48 99                	cqto
  401d0b:	48 f7 f9             	idiv   %rcx
  401d0e:	48 89 c1             	mov    %rax,%rcx
  401d11:	48 f7 ef             	imul   %rdi
  401d14:	48 89 c8             	mov    %rcx,%rax
  401d17:	48 c1 f8 3f          	sar    $0x3f,%rax
  401d1b:	48 01 ca             	add    %rcx,%rdx
  401d1e:	48 c1 fa 07          	sar    $0x7,%rdx
  401d22:	48 29 c2             	sub    %rax,%rdx
  401d25:	48 89 d0             	mov    %rdx,%rax
  401d28:	48 c1 e0 08          	shl    $0x8,%rax
  401d2c:	48 29 d0             	sub    %rdx,%rax
  401d2f:	48 29 c1             	sub    %rax,%rcx
  401d32:	49 63 c1             	movslq %r9d,%rax
        struct Data * thread = &data->threads[data->threadindex];
  401d35:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401d3d:	48 c1 e1 10          	shl    $0x10,%rcx
        struct Data * thread = &data->threads[data->threadindex];
  401d41:	48 29 c6             	sub    %rax,%rsi
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401d44:	48 09 c1             	or     %rax,%rcx
        struct Data * thread = &data->threads[data->threadindex];
  401d47:	48 c1 e6 07          	shl    $0x7,%rsi
  401d4b:	48 03 73 30          	add    0x30(%rbx),%rsi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401d4f:	48 63 96 24 03 00 00 	movslq 0x324(%rsi),%rdx
  401d56:	48 89 d0             	mov    %rdx,%rax
  401d59:	4c 8d 04 52          	lea    (%rdx,%rdx,2),%r8
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d5d:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401d60:	49 c1 e0 04          	shl    $0x4,%r8
  401d64:	4c 03 86 18 03 00 00 	add    0x318(%rsi),%r8
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d6b:	99                   	cltd
        epoch->time = time;
  401d6c:	41 0f 11 40 08       	movups %xmm0,0x8(%r8)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d71:	f7 be 20 03 00 00    	idivl  0x320(%rsi)
  data->main->works[buffer] = data->threadindex;
  401d77:	49 8b 42 70          	mov    0x70(%r10),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d7b:	89 96 24 03 00 00    	mov    %edx,0x324(%rsi)
        epoch->thread = data->threadindex;
  401d81:	45 89 08             	mov    %r9d,(%r8)
  epoch->buffer = buffer;
  401d84:	49 89 48 18          	mov    %rcx,0x18(%r8)
  epoch->set = 1;
  401d88:	41 c7 40 24 01 00 00 00 	movl   $0x1,0x24(%r8)
  data->main->works[buffer] = data->threadindex;
  401d90:	44 88 0c 08          	mov    %r9b,(%rax,%rcx,1)
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_RELAXED);
  401d94:	48 8b 43 28          	mov    0x28(%rbx),%rax
  401d98:	f0 48 83 80 50 03 00 00 01 	lock addq $0x1,0x350(%rax)
  long lastread = data->main->totalreads % data->threadsize;
  401da1:	48 8b 43 28          	mov    0x28(%rbx),%rax
  401da5:	4c 63 43 68          	movslq 0x68(%rbx),%r8
      if (data->globalread < thiswrite) {  
  401da9:	48 8b 8b 48 03 00 00 	mov    0x348(%rbx),%rcx
  long lastread = data->main->totalreads % data->threadsize;
  401db0:	48 8b 80 40 03 00 00 	mov    0x340(%rax),%rax
   data->freq++;
  401db7:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
  long lastread = data->main->totalreads % data->threadsize;
  401dbc:	48 99                	cqto
  401dbe:	49 f7 f8             	idiv   %r8
   data->prevread = lastread;
  401dc1:	48 89 93 08 03 00 00 	mov    %rdx,0x308(%rbx)
      if (data->globalread < thiswrite) {  
  401dc8:	48 39 e9             	cmp    %rbp,%rcx
  401dcb:	0f 8d bf 00 00 00    	jge    401e90 <threadwork+0x200>
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401dd1:	48 63 96 24 03 00 00 	movslq 0x324(%rsi),%rdx
            thepoch->time = time; 
  401dd8:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
         buffer = (past << 16) | data->readcursor;
  401ddd:	44 8b 93 00 02 00 00 	mov    0x200(%rbx),%r10d
                &data->threads[data->threadindex];
  401de4:	8b 6b 64             	mov    0x64(%rbx),%ebp
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401de7:	48 89 d0             	mov    %rdx,%rax
  401dea:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401dee:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401df1:	49 c1 e1 04          	shl    $0x4,%r9
  401df5:	4c 03 8e 18 03 00 00 	add    0x318(%rsi),%r9
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401dfc:	99                   	cltd
            thepoch->time = time; 
  401dfd:	41 0f 11 49 08       	movups %xmm1,0x8(%r9)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e02:	f7 be 20 03 00 00    	idivl  0x320(%rsi)
            long past = (((data->globalread) / (data->threadsize)) - 2) % 0xff;
  401e08:	48 89 c8             	mov    %rcx,%rax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e0b:	89 96 24 03 00 00    	mov    %edx,0x324(%rsi)
            long past = (((data->globalread) / (data->threadsize)) - 2) % 0xff;
  401e11:	48 99                	cqto
  401e13:	49 f7 f8             	idiv   %r8
          thepoch->set = 1;
  401e16:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
            long past = (((data->globalread) / (data->threadsize)) - 2) % 0xff;
  401e1e:	48 8d 70 fe          	lea    -0x2(%rax),%rsi
  401e22:	48 89 f0             	mov    %rsi,%rax
  401e25:	48 f7 ef             	imul   %rdi
  401e28:	48 89 f0             	mov    %rsi,%rax
  401e2b:	48 c1 f8 3f          	sar    $0x3f,%rax
  401e2f:	48 01 f2             	add    %rsi,%rdx
  401e32:	48 c1 fa 07          	sar    $0x7,%rdx
  401e36:	48 29 c2             	sub    %rax,%rdx
  401e39:	48 89 d0             	mov    %rdx,%rax
  401e3c:	48 c1 e0 08          	shl    $0x8,%rax
  401e40:	48 29 d0             	sub    %rdx,%rax
  401e43:	48 29 c6             	sub    %rax,%rsi
         buffer = (past << 16) | data->readcursor;
  401e46:	b8 00 00 00 00       	mov    $0x0,%eax
            long past = (((data->globalread) / (data->threadsize)) - 2) % 0xff;
  401e4b:	48 89 f2             	mov    %rsi,%rdx
         buffer = (past << 16) | data->readcursor;
  401e4e:	48 0f 48 d0          	cmovs  %rax,%rdx
  401e52:	49 63 c2             	movslq %r10d,%rax
  401e55:	48 c1 e2 10          	shl    $0x10,%rdx
  401e59:	48 09 c2             	or     %rax,%rdx
     data->readcursor = (data->readcursor + 1) % data->threadsize;
  401e5c:	41 8d 42 01          	lea    0x1(%r10),%eax
         buffer = (past << 16) | data->readcursor;
  401e60:	49 89 51 18          	mov    %rdx,0x18(%r9)
     data->readcursor = (data->readcursor + 1) % data->threadsize;
  401e64:	99                   	cltd
  401e65:	41 f7 f8             	idiv   %r8d
  401e68:	8d 45 01             	lea    0x1(%rbp),%eax
  401e6b:	39 d5                	cmp    %edx,%ebp
  401e6d:	0f 45 c2             	cmovne %edx,%eax
  401e70:	89 c6                	mov    %eax,%esi
      data->globalread++;
  401e72:	48 8d 41 01          	lea    0x1(%rcx),%rax
        if (data->globalread % data->threadsize == 0) {
  401e76:	48 99                	cqto
      data->globalread++;
  401e78:	48 89 83 48 03 00 00 	mov    %rax,0x348(%rbx)
        if (data->globalread % data->threadsize == 0) {
  401e7f:	49 f7 f8             	idiv   %r8
          data->readcursor = 0;
  401e82:	31 c0                	xor    %eax,%eax
  401e84:	48 85 d2             	test   %rdx,%rdx
  401e87:	0f 45 c6             	cmovne %esi,%eax
  401e8a:	89 83 00 02 00 00    	mov    %eax,0x200(%rbx)
}
  401e90:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  401e95:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401e9e:	75 09                	jne    401ea9 <threadwork+0x219>
  401ea0:	48 83 c4 28          	add    $0x28,%rsp
  401ea4:	31 c0                	xor    %eax,%eax
  401ea6:	5b                   	pop    %rbx
  401ea7:	5d                   	pop    %rbp
  401ea8:	c3                   	ret
  401ea9:	e8 b2 f1 ff ff       	call   401060 <__stack_chk_fail@plt>
  401eae:	66 90                	xchg   %ax,%ax

0000000000401eb0 <work>:
void * work(void * arg) {
  401eb0:	53                   	push   %rbx
  401eb1:	8b 57 64             	mov    0x64(%rdi),%edx
  401eb4:	48 89 fb             	mov    %rdi,%rbx
  401eb7:	31 c0                	xor    %eax,%eax
  401eb9:	48 8d 35 44 01 00 00 	lea    0x144(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  401ec0:	bf 01 00 00 00       	mov    $0x1,%edi
  401ec5:	e8 c6 f1 ff ff       	call   401090 <__printf_chk@plt>
  while (data->running == 1) {
  401eca:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401ece:	75 0e                	jne    401ede <work+0x2e>
      threadwork(data);
  401ed0:	48 89 df             	mov    %rbx,%rdi
  401ed3:	e8 b8 fd ff ff       	call   401c90 <threadwork>
  while (data->running == 1) {
  401ed8:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401edc:	74 f2                	je     401ed0 <work+0x20>
  401ede:	8b 53 64             	mov    0x64(%rbx),%edx
  401ee1:	48 8d 35 2f 01 00 00 	lea    0x12f(%rip),%rsi        # 402017 <_IO_stdin_used+0x17>
  401ee8:	bf 01 00 00 00       	mov    $0x1,%edi
  401eed:	31 c0                	xor    %eax,%eax
  401eef:	e8 9c f1 ff ff       	call   401090 <__printf_chk@plt>
}
  401ef4:	5b                   	pop    %rbx
  401ef5:	c3                   	ret
  401ef6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401f00 <work2>:
  while (data->running == 1) {
  401f00:	eb 0b                	jmp    401f0d <work2+0xd>
  401f02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  401f08:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  401f0d:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  401f11:	74 f5                	je     401f08 <work2+0x8>
}
  401f13:	c3                   	ret

Disassembly of section .fini:

0000000000401f14 <_fini>:
  401f14:	f3 0f 1e fa          	endbr64
  401f18:	48 83 ec 08          	sub    $0x8,%rsp
  401f1c:	48 83 c4 08          	add    $0x8,%rsp
  401f20:	c3                   	ret
