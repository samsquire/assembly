
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
  401366:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
  40136b:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  401370:	49 89 de             	mov    %rbx,%r14
  401373:	49 c7 c5 10 1e 40 00 	mov    $0x401e10,%r13
  40137a:	48 8d 8d 10 03 00 00 	lea    0x310(%rbp),%rcx
  401381:	49 89 c4             	mov    %rax,%r12
  401384:	48 89 c3             	mov    %rax,%rbx
  401387:	49 89 cf             	mov    %rcx,%r15
  40138a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  401390:	4c 89 f1             	mov    %r14,%rcx
  401393:	48 89 ee             	mov    %rbp,%rsi
  401396:	48 89 df             	mov    %rbx,%rdi
  401399:	4c 89 ea             	mov    %r13,%rdx
  40139c:	e8 ff fc ff ff       	call   4010a0 <pthread_create@plt>
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4013a1:	49 8b 56 78          	mov    0x78(%r14),%rdx
  4013a5:	48 8b 3b             	mov    (%rbx),%rdi
  4013a8:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  4013ad:	48 83 c5 38          	add    $0x38,%rbp
  4013b1:	48 83 c3 08          	add    $0x8,%rbx
  4013b5:	49 81 c6 80 03 00 00 	add    $0x380,%r14
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4013bc:	e8 6f fc ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  4013c1:	4c 39 fd             	cmp    %r15,%rbp
  4013c4:	75 ca                	jne    401390 <main+0x2d0>
  }
  
  struct timespec time = {
  4013c6:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  4013cb:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  4013d0:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec time = {
  4013d5:	66 0f 6f 05 43 0e 00 00 	movdqa 0xe43(%rip),%xmm0        # 402220 <_IO_stdin_used+0x220>
  4013dd:	4c 8d 6c 24 38       	lea    0x38(%rsp),%r13
  4013e2:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  4013e7:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4013eb:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  4013f0:	e8 7b fc ff ff       	call   401070 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  4013f5:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
  4013fa:	c7 43 5c 00 00 00 00 	movl   $0x0,0x5c(%rbx)
  401401:	c7 83 dc 03 00 00 00 00 00 00 	movl   $0x0,0x3dc(%rbx)
  40140b:	c7 83 5c 07 00 00 00 00 00 00 	movl   $0x0,0x75c(%rbx)
  401415:	48 83 c5 70          	add    $0x70,%rbp
  401419:	c7 83 dc 0a 00 00 00 00 00 00 	movl   $0x0,0xadc(%rbx)
  401423:	c7 83 5c 0e 00 00 00 00 00 00 	movl   $0x0,0xe5c(%rbx)
  40142d:	c7 83 dc 11 00 00 00 00 00 00 	movl   $0x0,0x11dc(%rbx)
  401437:	c7 83 5c 15 00 00 00 00 00 00 	movl   $0x0,0x155c(%rbx)
  401441:	c7 83 dc 18 00 00 00 00 00 00 	movl   $0x0,0x18dc(%rbx)
  40144b:	c7 83 5c 1c 00 00 00 00 00 00 	movl   $0x0,0x1c5c(%rbx)
  401455:	c7 83 dc 1f 00 00 00 00 00 00 	movl   $0x0,0x1fdc(%rbx)
  40145f:	c7 83 5c 23 00 00 00 00 00 00 	movl   $0x0,0x235c(%rbx)
  401469:	c7 83 dc 26 00 00 00 00 00 00 	movl   $0x0,0x26dc(%rbx)
  401473:	c7 83 5c 2a 00 00 00 00 00 00 	movl   $0x0,0x2a5c(%rbx)
  40147d:	c7 83 dc 2d 00 00 00 00 00 00 	movl   $0x0,0x2ddc(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  401487:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401490:	49 8b 3c 24          	mov    (%r12),%rdi
  401494:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  401497:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  40149b:	e8 10 fc ff ff       	call   4010b0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  4014a0:	49 39 ec             	cmp    %rbp,%r12
  4014a3:	75 eb                	jne    401490 <main+0x3d0>
  4014a5:	48 8d 3d d9 0b 00 00 	lea    0xbd9(%rip),%rdi        # 402085 <_IO_stdin_used+0x85>
  4014ac:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  4014b0:	45 31 e4             	xor    %r12d,%r12d
  4014b3:	e8 88 fb ff ff       	call   401040 <puts@plt>
  long sends = 1;
  for (int x = 0; x < threadsize; x++) {
  4014b8:	4c 8d b3 48 31 00 00 	lea    0x3148(%rbx),%r14
  4014bf:	4c 8d 2d d4 0b 00 00 	lea    0xbd4(%rip),%r13        # 40209a <_IO_stdin_used+0x9a>
  4014c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4014d0:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4014d4:	4c 89 ee             	mov    %r13,%rsi
  4014d7:	bf 01 00 00 00       	mov    $0x1,%edi
  4014dc:	31 c0                	xor    %eax,%eax
  4014de:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
  4014e5:	e8 a6 fb ff ff       	call   401090 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  4014ea:	4c 03 a5 80 fc ff ff 	add    -0x380(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  4014f1:	4c 39 f5             	cmp    %r14,%rbp
  4014f4:	75 da                	jne    4014d0 <main+0x410>
  }
  printf("freq: %ld\n", freq/ seconds);
  4014f6:	4c 89 e0             	mov    %r12,%rax
  4014f9:	49 c1 fc 3f          	sar    $0x3f,%r12
  4014fd:	48 ba 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rdx
  401507:	48 8d 35 97 0b 00 00 	lea    0xb97(%rip),%rsi        # 4020a5 <_IO_stdin_used+0xa5>
  40150e:	48 f7 ea             	imul   %rdx
  401511:	bf 01 00 00 00       	mov    $0x1,%edi
  401516:	31 c0                	xor    %eax,%eax
  401518:	4c 8d b3 50 31 00 00 	lea    0x3150(%rbx),%r14
  40151f:	4c 8d 2d dd 0b 00 00 	lea    0xbdd(%rip),%r13        # 402103 <_IO_stdin_used+0x103>
  401526:	48 d1 fa             	sar    %rdx
  401529:	4c 29 e2             	sub    %r12,%rdx
  40152c:	48 89 d5             	mov    %rdx,%rbp
  40152f:	e8 5c fb ff ff       	call   401090 <__printf_chk@plt>
  401534:	48 89 ea             	mov    %rbp,%rdx
  401537:	bf 01 00 00 00       	mov    $0x1,%edi
  40153c:	31 c0                	xor    %eax,%eax
  40153e:	48 8d 35 6b 0b 00 00 	lea    0xb6b(%rip),%rsi        # 4020b0 <_IO_stdin_used+0xb0>
  401545:	e8 46 fb ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  40154a:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40154f:	bf 01 00 00 00       	mov    $0x1,%edi
  401554:	48 8d 35 63 0b 00 00 	lea    0xb63(%rip),%rsi        # 4020be <_IO_stdin_used+0xbe>
  40155b:	48 99                	cqto
  40155d:	48 f7 fd             	idiv   %rbp
  401560:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  401564:	49 89 c4             	mov    %rax,%r12
  401567:	48 89 c2             	mov    %rax,%rdx
  40156a:	31 c0                	xor    %eax,%eax
  40156c:	e8 1f fb ff ff       	call   401090 <__printf_chk@plt>
  401571:	4c 89 e2             	mov    %r12,%rdx
  401574:	bf 01 00 00 00       	mov    $0x1,%edi
  401579:	31 c0                	xor    %eax,%eax
  40157b:	48 8d 35 50 0b 00 00 	lea    0xb50(%rip),%rsi        # 4020d2 <_IO_stdin_used+0xd2>
  401582:	e8 09 fb ff ff       	call   401090 <__printf_chk@plt>
  401587:	4c 89 e2             	mov    %r12,%rdx
  40158a:	bf 01 00 00 00       	mov    $0x1,%edi
  40158f:	31 c0                	xor    %eax,%eax
  401591:	48 8d 35 58 0b 00 00 	lea    0xb58(%rip),%rsi        # 4020f0 <_IO_stdin_used+0xf0>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  long freq_writes = 0;
  401598:	45 31 e4             	xor    %r12d,%r12d
  40159b:	e8 f0 fa ff ff       	call   401090 <__printf_chk@plt>
  
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  4015a0:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4015a4:	4c 89 ee             	mov    %r13,%rsi
  4015a7:	bf 01 00 00 00       	mov    $0x1,%edi
  4015ac:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  4015ae:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
    freq_writes += data[x].freq_writes;
  4015b5:	49 01 d4             	add    %rdx,%r12
  4015b8:	e8 d3 fa ff ff       	call   401090 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  4015bd:	49 39 ee             	cmp    %rbp,%r14
  4015c0:	75 de                	jne    4015a0 <main+0x4e0>
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  4015c2:	4c 89 e0             	mov    %r12,%rax
  4015c5:	49 c1 fc 3f          	sar    $0x3f,%r12
  4015c9:	bf 01 00 00 00       	mov    $0x1,%edi
  4015ce:	48 ba 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rdx
  4015d8:	48 f7 ea             	imul   %rdx
  4015db:	48 8d 35 2d 0b 00 00 	lea    0xb2d(%rip),%rsi        # 40210f <_IO_stdin_used+0x10f>
  4015e2:	31 c0                	xor    %eax,%eax
  4015e4:	48 d1 fa             	sar    %rdx
  4015e7:	4c 29 e2             	sub    %r12,%rdx
  4015ea:	48 89 d5             	mov    %rdx,%rbp
  4015ed:	e8 9e fa ff ff       	call   401090 <__printf_chk@plt>
  4015f2:	48 89 ea             	mov    %rbp,%rdx
  4015f5:	bf 01 00 00 00       	mov    $0x1,%edi
  4015fa:	31 c0                	xor    %eax,%eax
  4015fc:	48 8d 35 1e 0b 00 00 	lea    0xb1e(%rip),%rsi        # 402121 <_IO_stdin_used+0x121>
  401603:	e8 88 fa ff ff       	call   401090 <__printf_chk@plt>

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  401608:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40160d:	bf 01 00 00 00       	mov    $0x1,%edi
  401612:	48 8d 35 20 0b 00 00 	lea    0xb20(%rip),%rsi        # 402139 <_IO_stdin_used+0x139>
  401619:	48 99                	cqto
  40161b:	48 f7 fd             	idiv   %rbp
  40161e:	48 8d 2d a8 0a 00 00 	lea    0xaa8(%rip),%rbp        # 4020cd <_IO_stdin_used+0xcd>
  401625:	49 89 c4             	mov    %rax,%r12
  401628:	48 89 c2             	mov    %rax,%rdx
  40162b:	31 c0                	xor    %eax,%eax
  40162d:	e8 5e fa ff ff       	call   401090 <__printf_chk@plt>
  401632:	4c 89 e2             	mov    %r12,%rdx
  401635:	bf 01 00 00 00       	mov    $0x1,%edi
  40163a:	31 c0                	xor    %eax,%eax
  40163c:	48 8d 35 65 0b 00 00 	lea    0xb65(%rip),%rsi        # 4021a8 <_IO_stdin_used+0x1a8>
  401643:	e8 48 fa ff ff       	call   401090 <__printf_chk@plt>
  401648:	4c 89 e2             	mov    %r12,%rdx
  40164b:	bf 01 00 00 00       	mov    $0x1,%edi
  401650:	31 c0                	xor    %eax,%eax
  401652:	48 8d 35 fb 0a 00 00 	lea    0xafb(%rip),%rsi        # 402154 <_IO_stdin_used+0x154>
  401659:	e8 32 fa ff ff       	call   401090 <__printf_chk@plt>
  40165e:	48 8d 3d 09 0b 00 00 	lea    0xb09(%rip),%rdi        # 40216e <_IO_stdin_used+0x16e>
  401665:	e8 d6 f9 ff ff       	call   401040 <puts@plt>
  40166a:	48 89 ee             	mov    %rbp,%rsi
  40166d:	bf 01 00 00 00       	mov    $0x1,%edi
  401672:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  401674:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  40167b:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  401682:	e8 09 fa ff ff       	call   401090 <__printf_chk@plt>
  401687:	48 89 ee             	mov    %rbp,%rsi
  40168a:	bf 01 00 00 00       	mov    $0x1,%edi
  40168f:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  401691:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  401698:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  40169f:	e8 ec f9 ff ff       	call   401090 <__printf_chk@plt>
  4016a4:	48 89 ee             	mov    %rbp,%rsi
  4016a7:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ac:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  4016ae:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  4016b5:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  4016bc:	e8 cf f9 ff ff       	call   401090 <__printf_chk@plt>
  4016c1:	48 89 ee             	mov    %rbp,%rsi
  4016c4:	bf 01 00 00 00       	mov    $0x1,%edi
  4016c9:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4016cb:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  4016d2:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  4016d9:	e8 b2 f9 ff ff       	call   401090 <__printf_chk@plt>
  4016de:	48 89 ee             	mov    %rbp,%rsi
  4016e1:	bf 01 00 00 00       	mov    $0x1,%edi
  4016e6:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  4016e8:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  4016ef:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  4016f6:	e8 95 f9 ff ff       	call   401090 <__printf_chk@plt>
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  4016fb:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401702:	48 89 ee             	mov    %rbp,%rsi
  401705:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  40170c:	bf 01 00 00 00       	mov    $0x1,%edi
  401711:	31 c0                	xor    %eax,%eax
  401713:	e8 78 f9 ff ff       	call   401090 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  401718:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  40171f:	31 c0                	xor    %eax,%eax
  401721:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  401728:	48 8d 35 4c 0a 00 00 	lea    0xa4c(%rip),%rsi        # 40217b <_IO_stdin_used+0x17b>
  40172f:	bf 01 00 00 00       	mov    $0x1,%edi
  401734:	e8 57 f9 ff ff       	call   401090 <__printf_chk@plt>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  401739:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  40173e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401747:	75 11                	jne    40175a <main+0x69a>
  401749:	48 83 c4 78          	add    $0x78,%rsp
  40174d:	31 c0                	xor    %eax,%eax
  40174f:	5b                   	pop    %rbx
  401750:	5d                   	pop    %rbp
  401751:	41 5c                	pop    %r12
  401753:	41 5d                	pop    %r13
  401755:	41 5e                	pop    %r14
  401757:	41 5f                	pop    %r15
  401759:	c3                   	ret
  40175a:	e8 01 f9 ff ff       	call   401060 <__stack_chk_fail@plt>
  40175f:	90                   	nop

0000000000401760 <_start>:
  401760:	f3 0f 1e fa          	endbr64
  401764:	31 ed                	xor    %ebp,%ebp
  401766:	49 89 d1             	mov    %rdx,%r9
  401769:	5e                   	pop    %rsi
  40176a:	48 89 e2             	mov    %rsp,%rdx
  40176d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401771:	50                   	push   %rax
  401772:	54                   	push   %rsp
  401773:	45 31 c0             	xor    %r8d,%r8d
  401776:	31 c9                	xor    %ecx,%ecx
  401778:	48 c7 c7 c0 10 40 00 	mov    $0x4010c0,%rdi
  40177f:	ff 15 6b 28 00 00    	call   *0x286b(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  401785:	f4                   	hlt
  401786:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401790 <_dl_relocate_static_pie>:
  401790:	f3 0f 1e fa          	endbr64
  401794:	c3                   	ret
  401795:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40179f:	90                   	nop

00000000004017a0 <deregister_tm_clones>:
  4017a0:	b8 10 40 40 00       	mov    $0x404010,%eax
  4017a5:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  4017ab:	74 13                	je     4017c0 <deregister_tm_clones+0x20>
  4017ad:	b8 00 00 00 00       	mov    $0x0,%eax
  4017b2:	48 85 c0             	test   %rax,%rax
  4017b5:	74 09                	je     4017c0 <deregister_tm_clones+0x20>
  4017b7:	bf 10 40 40 00       	mov    $0x404010,%edi
  4017bc:	ff e0                	jmp    *%rax
  4017be:	66 90                	xchg   %ax,%ax
  4017c0:	c3                   	ret
  4017c1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4017cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004017d0 <register_tm_clones>:
  4017d0:	be 10 40 40 00       	mov    $0x404010,%esi
  4017d5:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  4017dc:	48 89 f0             	mov    %rsi,%rax
  4017df:	48 c1 ee 3f          	shr    $0x3f,%rsi
  4017e3:	48 c1 f8 03          	sar    $0x3,%rax
  4017e7:	48 01 c6             	add    %rax,%rsi
  4017ea:	48 d1 fe             	sar    %rsi
  4017ed:	74 11                	je     401800 <register_tm_clones+0x30>
  4017ef:	b8 00 00 00 00       	mov    $0x0,%eax
  4017f4:	48 85 c0             	test   %rax,%rax
  4017f7:	74 07                	je     401800 <register_tm_clones+0x30>
  4017f9:	bf 10 40 40 00       	mov    $0x404010,%edi
  4017fe:	ff e0                	jmp    *%rax
  401800:	c3                   	ret
  401801:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40180c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401810 <__do_global_dtors_aux>:
  401810:	f3 0f 1e fa          	endbr64
  401814:	80 3d f5 27 00 00 00 	cmpb   $0x0,0x27f5(%rip)        # 404010 <__TMC_END__>
  40181b:	75 13                	jne    401830 <__do_global_dtors_aux+0x20>
  40181d:	55                   	push   %rbp
  40181e:	48 89 e5             	mov    %rsp,%rbp
  401821:	e8 7a ff ff ff       	call   4017a0 <deregister_tm_clones>
  401826:	c6 05 e3 27 00 00 01 	movb   $0x1,0x27e3(%rip)        # 404010 <__TMC_END__>
  40182d:	5d                   	pop    %rbp
  40182e:	c3                   	ret
  40182f:	90                   	nop
  401830:	c3                   	ret
  401831:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40183c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401840 <frame_dummy>:
  401840:	f3 0f 1e fa          	endbr64
  401844:	eb 8a                	jmp    4017d0 <register_tm_clones>
  401846:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401850 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  401850:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  401854:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  401857:	7e 77                	jle    4018d0 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  401859:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  40185d:	55                   	push   %rbp
  40185e:	49 89 f2             	mov    %rsi,%r10
  401861:	49 89 d3             	mov    %rdx,%r11
  401864:	53                   	push   %rbx
  401865:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  401868:	48 8b 98 a0 03 00 00 	mov    0x3a0(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  40186f:	b8 01 00 00 00       	mov    $0x1,%eax
  401874:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  401878:	48 63 d0             	movslq %eax,%rdx
  40187b:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  40187e:	85 d2                	test   %edx,%edx
  401880:	40 0f 94 c6          	sete   %sil
  401884:	f6 c2 04             	test   $0x4,%dl
  401887:	75 05                	jne    40188e <pollthreads+0x3e>
  401889:	40 84 f6             	test   %sil,%sil
  40188c:	74 0d                	je     40189b <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  40188e:	49 63 08             	movslq (%r8),%rcx
  401891:	8d 69 01             	lea    0x1(%rcx),%ebp
  401894:	41 89 28             	mov    %ebp,(%r8)
  401897:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  40189b:	83 e2 08             	and    $0x8,%edx
  40189e:	75 05                	jne    4018a5 <pollthreads+0x55>
  4018a0:	40 84 f6             	test   %sil,%sil
  4018a3:	74 1b                	je     4018c0 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  4018a5:	48 63 17             	movslq (%rdi),%rdx
  4018a8:	8d 4a 01             	lea    0x1(%rdx),%ecx
  4018ab:	89 0f                	mov    %ecx,(%rdi)
  4018ad:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  4018b1:	83 c0 01             	add    $0x1,%eax
  4018b4:	41 39 41 68          	cmp    %eax,0x68(%r9)
  4018b8:	7f be                	jg     401878 <pollthreads+0x28>
}
  4018ba:	31 c0                	xor    %eax,%eax
  4018bc:	5b                   	pop    %rbx
  4018bd:	5d                   	pop    %rbp
  4018be:	c3                   	ret
  4018bf:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  4018c0:	83 c0 01             	add    $0x1,%eax
  4018c3:	41 39 41 68          	cmp    %eax,0x68(%r9)
  4018c7:	7f af                	jg     401878 <pollthreads+0x28>
}
  4018c9:	31 c0                	xor    %eax,%eax
  4018cb:	5b                   	pop    %rbx
  4018cc:	5d                   	pop    %rbp
  4018cd:	c3                   	ret
  4018ce:	66 90                	xchg   %ax,%ax
  4018d0:	31 c0                	xor    %eax,%eax
  4018d2:	c3                   	ret
  4018d3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4018de:	66 90                	xchg   %ax,%ax

00000000004018e0 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  4018e0:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4018e3:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
      if (*availableidx == 0) {
  4018ea:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4018ed:	48 83 c7 01          	add    $0x1,%rdi
  4018f1:	48 85 ff             	test   %rdi,%rdi
  4018f4:	7e 66                	jle    40195c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  4018f6:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4018fd:	31 c9                	xor    %ecx,%ecx
  4018ff:	45 31 c9             	xor    %r9d,%r9d
  401902:	31 c0                	xor    %eax,%eax
  401904:	eb 18                	jmp    40191e <findavailable+0x3e>
  401906:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401910:	83 c1 01             	add    $0x1,%ecx
  401913:	48 63 c1             	movslq %ecx,%rax
  401916:	49 89 c1             	mov    %rax,%r9
  401919:	48 39 f8             	cmp    %rdi,%rax
  40191c:	7d 3e                	jge    40195c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  40191e:	48 c1 e0 05          	shl    $0x5,%rax
  401922:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401928:	75 e6                	jne    401910 <findavailable+0x30>
         available[*availableidx] = x;
  40192a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  40192d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401931:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401935:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401938:	41 8b 43 68          	mov    0x68(%r11),%eax
  40193c:	01 c0                	add    %eax,%eax
  40193e:	41 39 c0             	cmp    %eax,%r8d
  401941:	74 19                	je     40195c <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401943:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  40194a:	83 c1 01             	add    $0x1,%ecx
  40194d:	48 63 c1             	movslq %ecx,%rax
  401950:	48 83 c7 01          	add    $0x1,%rdi
  401954:	49 89 c1             	mov    %rax,%r9
  401957:	48 39 f8             	cmp    %rdi,%rax
  40195a:	7c c2                	jl     40191e <findavailable+0x3e>
      if (*availableidx == 0) {
  40195c:	31 c0                	xor    %eax,%eax
  40195e:	45 85 c0             	test   %r8d,%r8d
  401961:	0f 94 c0             	sete   %al
}
  401964:	c3                   	ret
  401965:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401970 <singlewriter3>:
}
  401970:	c3                   	ret
  401971:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40197c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401980 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401980:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  401986:	85 c0                	test   %eax,%eax
  401988:	74 1e                	je     4019a8 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40198a:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  40198c:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40198d:	55                   	push   %rbp
  40198e:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  40198f:	8b 77 68             	mov    0x68(%rdi),%esi
  401992:	48 89 fb             	mov    %rdi,%rbx
  401995:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401998:	f7 f9                	idiv   %ecx
  40199a:	85 d2                	test   %edx,%edx
  40199c:	74 12                	je     4019b0 <singlewriter2+0x30>
}
  40199e:	5b                   	pop    %rbx
  40199f:	5d                   	pop    %rbp
  4019a0:	41 5c                	pop    %r12
  4019a2:	c3                   	ret
  4019a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4019a8:	c3                   	ret
  4019a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct Data * thread = &data->threads[data->threadindex];
  4019b0:	48 63 47 64          	movslq 0x64(%rdi),%rax
  4019b4:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  4019bc:	48 29 c5             	sub    %rax,%rbp
  4019bf:	48 c1 e5 07          	shl    $0x7,%rbp
  4019c3:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  4019c7:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4019cc:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  4019d3:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  4019d7:	49 c1 e4 04          	shl    $0x4,%r12
  4019db:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  4019e2:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  4019e7:	e8 64 f6 ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4019ec:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  4019f2:	83 c0 01             	add    $0x1,%eax
  4019f5:	99                   	cltd
  4019f6:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  4019fc:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4019ff:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401a05:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401a09:	48 8b 05 c0 07 00 00 	mov    0x7c0(%rip),%rax        # 4021d0 <_IO_stdin_used+0x1d0>
  401a10:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  401a15:	5b                   	pop    %rbx
  401a16:	5d                   	pop    %rbp
  401a17:	41 5c                	pop    %r12
  401a19:	c3                   	ret
  401a1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000401a20 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a20:	41 55                	push   %r13
  401a22:	49 89 d5             	mov    %rdx,%r13
  401a25:	41 54                	push   %r12
  401a27:	49 89 cc             	mov    %rcx,%r12
  401a2a:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401a2b:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a2e:	48 89 fd             	mov    %rdi,%rbp
  401a31:	53                   	push   %rbx
  401a32:	48 89 f3             	mov    %rsi,%rbx
  401a35:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401a39:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a3d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401a46:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401a4b:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401a4d:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401a55:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  401a5b:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401a63:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401a6b:	83 c0 01             	add    $0x1,%eax
  401a6e:	99                   	cltd
  401a6f:	f7 7f 68             	idivl  0x68(%rdi)
  401a72:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401a78:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401a7d:	4c 89 e9             	mov    %r13,%rcx
  401a80:	e8 5b fe ff ff       	call   4018e0 <findavailable>
  if (fill == 1) {
  401a85:	83 f8 01             	cmp    $0x1,%eax
  401a88:	0f 84 64 01 00 00    	je     401bf2 <singlewriter+0x1d2>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401a8e:	48 89 ef             	mov    %rbp,%rdi
  401a91:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401a96:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401a9b:	4c 89 e2             	mov    %r12,%rdx
  401a9e:	4c 89 ee             	mov    %r13,%rsi
  401aa1:	e8 aa fd ff ff       	call   401850 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401aa6:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401aab:	85 ff                	test   %edi,%edi
  401aad:	0f 8e 66 01 00 00    	jle    401c19 <singlewriter+0x1f9>
  401ab3:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401ab8:	31 c9                	xor    %ecx,%ecx
  401aba:	eb 62                	jmp    401b1e <singlewriter+0xfe>
  401abc:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401ac0:	48 8b 14 cb          	mov    (%rbx,%rcx,8),%rdx
          int thread = readyreaders[x];
  401ac4:	4d 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%r10
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401ac9:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401acc:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401ad0:	48 c1 e2 05          	shl    $0x5,%rdx
  401ad4:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].reading = chunk;
  401adb:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
          data->threads[thread].start = start;
  401ae3:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401ae7:	66 0f 6e 4a 08       	movd   0x8(%rdx),%xmm1
          data->threads[thread].reading = chunk;
  401aec:	4c 29 d0             	sub    %r10,%rax
          chunk->available = READING;
  401aef:	c7 42 10 02 00 00 00 	movl   $0x2,0x10(%rdx)
          data->threads[thread].reading = chunk;
  401af6:	48 c1 e0 07          	shl    $0x7,%rax
  401afa:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].start = start;
  401afe:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401b02:	48 89 90 a8 00 00 00 	mov    %rdx,0xa8(%rax)
          chunk->owner = thread;
  401b09:	44 89 52 14          	mov    %r10d,0x14(%rdx)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401b0d:	83 88 c8 00 00 00 10 	orl    $0x10,0xc8(%rax)
          data->threads[thread].start = start;
  401b14:	66 0f d6 40 14       	movq   %xmm0,0x14(%rax)
        for (int x = 0; x < readers ; x++) {
  401b19:	48 39 cf             	cmp    %rcx,%rdi
  401b1c:	74 07                	je     401b25 <singlewriter+0x105>
  401b1e:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401b20:	4c 39 c1             	cmp    %r8,%rcx
  401b23:	75 9b                	jne    401ac0 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401b25:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401b2a:	45 85 c0             	test   %r8d,%r8d
  401b2d:	7e 7a                	jle    401ba9 <singlewriter+0x189>
                if (assignedchunk  == availableidx) {
  401b2f:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401b33:	41 01 f0             	add    %esi,%r8d
  401b36:	eb 6d                	jmp    401ba5 <singlewriter+0x185>
  401b38:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b40:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401b43:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401b46:	45 8b 0c 24          	mov    (%r12),%r9d
   for (int x = 0; x < writers ; x++) {
  401b4a:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b4e:	48 8b 14 f3          	mov    (%rbx,%rsi,8),%rdx
          data->threads[thread].writing = chunk;
  401b52:	49 63 f1             	movslq %r9d,%rsi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b55:	48 c1 e2 05          	shl    $0x5,%rdx
  401b59:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].writing = chunk;
  401b60:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
          data->threads[thread].publishstart = start;
  401b68:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401b6c:	66 0f 6e 52 08       	movd   0x8(%rdx),%xmm2
          data->threads[thread].writing = chunk;
  401b71:	48 29 f0             	sub    %rsi,%rax
      chunk->available = WRITING;
  401b74:	c7 42 10 03 00 00 00 	movl   $0x3,0x10(%rdx)
          data->threads[thread].writing = chunk;
  401b7b:	48 c1 e0 07          	shl    $0x7,%rax
  401b7f:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].publishstart = start;
  401b83:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401b87:	48 89 90 b0 00 00 00 	mov    %rdx,0xb0(%rax)
          chunk->owner = thread;
  401b8e:	44 89 4a 14          	mov    %r9d,0x14(%rdx)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401b92:	83 88 c8 00 00 00 20 	orl    $0x20,0xc8(%rax)
          data->threads[thread].publishstart = start;
  401b99:	66 0f d6 40 40       	movq   %xmm0,0x40(%rax)
   for (int x = 0; x < writers ; x++) {
  401b9e:	44 39 c1             	cmp    %r8d,%ecx
  401ba1:	74 06                	je     401ba9 <singlewriter+0x189>
  401ba3:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401ba5:	39 f7                	cmp    %esi,%edi
  401ba7:	75 97                	jne    401b40 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401ba9:	8b 7d 68             	mov    0x68(%rbp),%edi
  401bac:	85 ff                	test   %edi,%edi
  401bae:	7e 40                	jle    401bf0 <singlewriter+0x1d0>
        if (data->threads[x].newmask != 0) {
  401bb0:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401bb4:	31 d2                	xor    %edx,%edx
  401bb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401bc0:	48 63 ca             	movslq %edx,%rcx
  401bc3:	48 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rax
  401bcb:	48 29 c8             	sub    %rcx,%rax
  401bce:	48 c1 e0 07          	shl    $0x7,%rax
  401bd2:	4c 01 c0             	add    %r8,%rax
  401bd5:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401bdb:	85 f6                	test   %esi,%esi
  401bdd:	74 31                	je     401c10 <singlewriter+0x1f0>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401bdf:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401be3:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401be6:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401be9:	8b 7d 68             	mov    0x68(%rbp),%edi
  401bec:	39 fa                	cmp    %edi,%edx
  401bee:	7c d0                	jl     401bc0 <singlewriter+0x1a0>
  return 0;
  401bf0:	31 c0                	xor    %eax,%eax
}
  401bf2:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401bf7:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401c00:	75 1e                	jne    401c20 <singlewriter+0x200>
  401c02:	48 83 c4 28          	add    $0x28,%rsp
  401c06:	5b                   	pop    %rbx
  401c07:	5d                   	pop    %rbp
  401c08:	41 5c                	pop    %r12
  401c0a:	41 5d                	pop    %r13
  401c0c:	c3                   	ret
  401c0d:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401c10:	83 c2 01             	add    $0x1,%edx
  401c13:	39 fa                	cmp    %edi,%edx
  401c15:	7c a9                	jl     401bc0 <singlewriter+0x1a0>
  401c17:	eb d7                	jmp    401bf0 <singlewriter+0x1d0>
      int assignedchunk = 0;
  401c19:	31 f6                	xor    %esi,%esi
  401c1b:	e9 05 ff ff ff       	jmp    401b25 <singlewriter+0x105>
}
  401c20:	e8 3b f4 ff ff       	call   401060 <__stack_chk_fail@plt>
  401c25:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401c30 <threadwork>:
int * threadwork(struct Data * data) {
  401c30:	53                   	push   %rbx
  long thiswrite = data->main->globalwrite;
  401c31:	4c 8b 57 28          	mov    0x28(%rdi),%r10
int * threadwork(struct Data * data) {
  401c35:	48 89 f9             	mov    %rdi,%rcx
  401c38:	66 0f ef c0          	pxor   %xmm0,%xmm0
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401c3c:	48 63 77 68          	movslq 0x68(%rdi),%rsi
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401c40:	44 8b 59 64          	mov    0x64(%rcx),%r11d
  401c44:	48 bb 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%rbx
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401c4e:	49 8b 82 38 03 00 00 	mov    0x338(%r10),%rax
  long thiswrite = data->main->globalwrite;
  401c55:	4d 8b 8a 50 03 00 00 	mov    0x350(%r10),%r9
  long lastcursor = data->main->writecursor;
  401c5c:	41 8b ba 80 01 00 00 	mov    0x180(%r10),%edi
   data->freq_writes++;
  401c63:	48 83 41 50 01       	addq   $0x1,0x50(%rcx)
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401c68:	48 99                	cqto
  401c6a:	48 f7 fe             	idiv   %rsi
    data->thiswrite = lastcursor;
  401c6d:	89 b9 28 03 00 00    	mov    %edi,0x328(%rcx)
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401c73:	4c 89 c8             	mov    %r9,%rax
    data->prevwrite = lastwrite;
  401c76:	48 89 91 10 03 00 00 	mov    %rdx,0x310(%rcx)
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401c7d:	48 99                	cqto
  401c7f:	48 f7 fe             	idiv   %rsi
  401c82:	49 89 c0             	mov    %rax,%r8
  401c85:	48 f7 eb             	imul   %rbx
  401c88:	4c 89 c0             	mov    %r8,%rax
  401c8b:	48 c1 f8 3f          	sar    $0x3f,%rax
  401c8f:	4c 01 c2             	add    %r8,%rdx
  401c92:	48 c1 fa 07          	sar    $0x7,%rdx
  401c96:	48 29 c2             	sub    %rax,%rdx
  401c99:	48 89 d0             	mov    %rdx,%rax
  401c9c:	48 c1 e0 08          	shl    $0x8,%rax
  401ca0:	48 29 d0             	sub    %rdx,%rax
  401ca3:	49 29 c0             	sub    %rax,%r8
  401ca6:	49 63 c3             	movslq %r11d,%rax
        struct Data * thread = &data->threads[data->threadindex];
  401ca9:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401cb1:	49 c1 e0 10          	shl    $0x10,%r8
        struct Data * thread = &data->threads[data->threadindex];
  401cb5:	48 29 c6             	sub    %rax,%rsi
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401cb8:	49 09 c0             	or     %rax,%r8
        struct Data * thread = &data->threads[data->threadindex];
  401cbb:	48 c1 e6 07          	shl    $0x7,%rsi
  401cbf:	48 03 71 30          	add    0x30(%rcx),%rsi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401cc3:	48 63 96 24 03 00 00 	movslq 0x324(%rsi),%rdx
  401cca:	48 89 d0             	mov    %rdx,%rax
  401ccd:	48 8d 3c 52          	lea    (%rdx,%rdx,2),%rdi
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401cd1:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401cd4:	48 c1 e7 04          	shl    $0x4,%rdi
  401cd8:	48 03 be 18 03 00 00 	add    0x318(%rsi),%rdi
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401cdf:	99                   	cltd
        epoch->time = time;
  401ce0:	0f 11 47 08          	movups %xmm0,0x8(%rdi)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ce4:	f7 be 20 03 00 00    	idivl  0x320(%rsi)
  data->main->works[buffer] = data->threadindex;
  401cea:	49 8b 42 70          	mov    0x70(%r10),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401cee:	89 96 24 03 00 00    	mov    %edx,0x324(%rsi)
        epoch->thread = data->threadindex;
  401cf4:	44 89 1f             	mov    %r11d,(%rdi)
  epoch->buffer = buffer;
  401cf7:	4c 89 47 18          	mov    %r8,0x18(%rdi)
  epoch->set = 1;
  401cfb:	c7 47 24 01 00 00 00 	movl   $0x1,0x24(%rdi)
  data->main->works[buffer] = data->threadindex;
  401d02:	46 88 1c 00          	mov    %r11b,(%rax,%r8,1)
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_RELAXED);
  401d06:	48 8b 41 28          	mov    0x28(%rcx),%rax
  401d0a:	f0 48 83 80 50 03 00 00 01 	lock addq $0x1,0x350(%rax)
  long lastread = data->main->totalreads % data->threadsize;
  401d13:	48 8b 41 28          	mov    0x28(%rcx),%rax
  401d17:	4c 63 41 68          	movslq 0x68(%rcx),%r8
      if (data->globalread < thiswrite) {  
  401d1b:	48 8b b9 48 03 00 00 	mov    0x348(%rcx),%rdi
  long lastread = data->main->totalreads % data->threadsize;
  401d22:	48 8b 80 40 03 00 00 	mov    0x340(%rax),%rax
   data->freq++;
  401d29:	48 83 41 48 01       	addq   $0x1,0x48(%rcx)
  long lastread = data->main->totalreads % data->threadsize;
  401d2e:	48 99                	cqto
  401d30:	49 f7 f8             	idiv   %r8
   data->prevread = lastread;
  401d33:	48 89 91 08 03 00 00 	mov    %rdx,0x308(%rcx)
      if (data->globalread < thiswrite) {  
  401d3a:	4c 39 cf             	cmp    %r9,%rdi
  401d3d:	0f 8d b9 00 00 00    	jge    401dfc <threadwork+0x1cc>
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401d43:	48 63 96 24 03 00 00 	movslq 0x324(%rsi),%rdx
         buffer = (past << 16) | data->readcursor;
  401d4a:	44 8b 91 00 02 00 00 	mov    0x200(%rcx),%r10d
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401d51:	48 89 d0             	mov    %rdx,%rax
  401d54:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d58:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401d5b:	49 c1 e1 04          	shl    $0x4,%r9
  401d5f:	4c 03 8e 18 03 00 00 	add    0x318(%rsi),%r9
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d66:	99                   	cltd
            thepoch->time = time; 
  401d67:	41 0f 11 41 08       	movups %xmm0,0x8(%r9)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d6c:	f7 be 20 03 00 00    	idivl  0x320(%rsi)
            long past = (((data->globalread) / (data->threadsize)) - 2) % 0xff;
  401d72:	48 89 f8             	mov    %rdi,%rax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d75:	89 96 24 03 00 00    	mov    %edx,0x324(%rsi)
            long past = (((data->globalread) / (data->threadsize)) - 2) % 0xff;
  401d7b:	48 99                	cqto
  401d7d:	49 f7 f8             	idiv   %r8
          thepoch->set = 1;
  401d80:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
            long past = (((data->globalread) / (data->threadsize)) - 2) % 0xff;
  401d88:	48 8d 70 fe          	lea    -0x2(%rax),%rsi
  401d8c:	48 89 f0             	mov    %rsi,%rax
  401d8f:	48 f7 eb             	imul   %rbx
  401d92:	48 89 f0             	mov    %rsi,%rax
  401d95:	48 c1 f8 3f          	sar    $0x3f,%rax
  401d99:	48 01 f2             	add    %rsi,%rdx
  401d9c:	48 c1 fa 07          	sar    $0x7,%rdx
  401da0:	48 29 c2             	sub    %rax,%rdx
  401da3:	48 89 d0             	mov    %rdx,%rax
  401da6:	48 c1 e0 08          	shl    $0x8,%rax
  401daa:	48 29 d0             	sub    %rdx,%rax
  401dad:	48 29 c6             	sub    %rax,%rsi
         buffer = (past << 16) | data->readcursor;
  401db0:	b8 00 00 00 00       	mov    $0x0,%eax
            long past = (((data->globalread) / (data->threadsize)) - 2) % 0xff;
  401db5:	48 89 f2             	mov    %rsi,%rdx
         buffer = (past << 16) | data->readcursor;
  401db8:	48 0f 48 d0          	cmovs  %rax,%rdx
  401dbc:	49 63 c2             	movslq %r10d,%rax
  401dbf:	48 c1 e2 10          	shl    $0x10,%rdx
  401dc3:	48 09 c2             	or     %rax,%rdx
     data->readcursor = (data->readcursor + 1) % data->threadsize;
  401dc6:	41 8d 42 01          	lea    0x1(%r10),%eax
         buffer = (past << 16) | data->readcursor;
  401dca:	49 89 51 18          	mov    %rdx,0x18(%r9)
     data->readcursor = (data->readcursor + 1) % data->threadsize;
  401dce:	99                   	cltd
  401dcf:	41 f7 f8             	idiv   %r8d
  401dd2:	89 91 00 02 00 00    	mov    %edx,0x200(%rcx)
         if (data->readcursor == data->threadindex) {
  401dd8:	3b 51 64             	cmp    0x64(%rcx),%edx
  401ddb:	74 23                	je     401e00 <threadwork+0x1d0>
      data->globalread++;
  401ddd:	48 8d 47 01          	lea    0x1(%rdi),%rax
        if (data->globalread % data->threadsize == 0) {
  401de1:	48 99                	cqto
      data->globalread++;
  401de3:	48 89 81 48 03 00 00 	mov    %rax,0x348(%rcx)
        if (data->globalread % data->threadsize == 0) {
  401dea:	49 f7 f8             	idiv   %r8
  401ded:	48 85 d2             	test   %rdx,%rdx
  401df0:	75 0a                	jne    401dfc <threadwork+0x1cc>
          data->readcursor = 0;
  401df2:	c7 81 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rcx)
}
  401dfc:	5b                   	pop    %rbx
  401dfd:	c3                   	ret
  401dfe:	66 90                	xchg   %ax,%ax
           data->readcursor++;
  401e00:	83 c2 01             	add    $0x1,%edx
  401e03:	89 91 00 02 00 00    	mov    %edx,0x200(%rcx)
  401e09:	eb d2                	jmp    401ddd <threadwork+0x1ad>
  401e0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000401e10 <work>:
void * work(void * arg) {
  401e10:	53                   	push   %rbx
  401e11:	8b 57 64             	mov    0x64(%rdi),%edx
  401e14:	48 89 fb             	mov    %rdi,%rbx
  401e17:	31 c0                	xor    %eax,%eax
  401e19:	48 8d 35 e4 01 00 00 	lea    0x1e4(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  401e20:	bf 01 00 00 00       	mov    $0x1,%edi
  401e25:	e8 66 f2 ff ff       	call   401090 <__printf_chk@plt>
  while (data->running == 1) {
  401e2a:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401e2e:	75 0e                	jne    401e3e <work+0x2e>
      threadwork(data);
  401e30:	48 89 df             	mov    %rbx,%rdi
  401e33:	e8 f8 fd ff ff       	call   401c30 <threadwork>
  while (data->running == 1) {
  401e38:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401e3c:	74 f2                	je     401e30 <work+0x20>
  401e3e:	8b 53 64             	mov    0x64(%rbx),%edx
  401e41:	48 8d 35 cf 01 00 00 	lea    0x1cf(%rip),%rsi        # 402017 <_IO_stdin_used+0x17>
  401e48:	bf 01 00 00 00       	mov    $0x1,%edi
  401e4d:	31 c0                	xor    %eax,%eax
  401e4f:	e8 3c f2 ff ff       	call   401090 <__printf_chk@plt>
}
  401e54:	5b                   	pop    %rbx
  401e55:	c3                   	ret
  401e56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401e60 <work2>:
  while (data->running == 1) {
  401e60:	eb 0b                	jmp    401e6d <work2+0xd>
  401e62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  401e68:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  401e6d:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  401e71:	74 f5                	je     401e68 <work2+0x8>
}
  401e73:	c3                   	ret

Disassembly of section .fini:

0000000000401e74 <_fini>:
  401e74:	f3 0f 1e fa          	endbr64
  401e78:	48 83 ec 08          	sub    $0x8,%rsp
  401e7c:	48 83 c4 08          	add    $0x8,%rsp
  401e80:	c3                   	ret
