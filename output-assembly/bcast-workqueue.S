
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
  40112d:	ba 0f 00 00 00       	mov    $0xf,%edx
  401132:	48 8d 35 0f 0f 00 00 	lea    0xf0f(%rip),%rsi        # 402048 <_IO_stdin_used+0x48>
  401139:	31 c0                	xor    %eax,%eax
  40113b:	bf 01 00 00 00       	mov    $0x1,%edi
  401140:	e8 4b ff ff ff       	call   401090 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401145:	be 08 00 00 00       	mov    $0x8,%esi
  40114a:	bf 0f 00 00 00       	mov    $0xf,%edi
  40114f:	e8 2c ff ff ff       	call   401080 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401154:	be 38 00 00 00       	mov    $0x38,%esi
  401159:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40115e:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401163:	e8 18 ff ff ff       	call   401080 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401168:	be 80 34 00 00       	mov    $0x3480,%esi
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
  4011ec:	bf 0f 00 00 00       	mov    $0xf,%edi
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
  4012ab:	41 81 c4 11 11 11 11 	add    $0x11111111,%r12d
    data[x].prevread = threadsize;
  4012b2:	66 0f 6f 25 56 0f 00 00 	movdqa 0xf56(%rip),%xmm4        # 402210 <_IO_stdin_used+0x210>
    data[x].threadindex = x;
  4012ba:	45 89 be e4 fc ff ff 	mov    %r15d,-0x31c(%r14)
    data[x].buckets = buckets;
  4012c1:	49 89 86 10 fd ff ff 	mov    %rax,-0x2f0(%r14)
    data[x].freelist = freelist;
  4012c8:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    data[x].threadsize = threadsize;
  4012cd:	41 c7 86 e8 fc ff ff 0f 00 00 00 	movl   $0xf,-0x318(%r14)
    data[x].readies[x] = 0;
  4012d8:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
    data[x].threads = data;
  4012df:	49 89 9e b0 fc ff ff 	mov    %rbx,-0x350(%r14)
    data[x].readcursor = threadsize - 1;
  4012e6:	41 c7 86 80 fe ff ff 0e 00 00 00 	movl   $0xe,-0x180(%r14)
    data[x].writecursor = threadsize - 1;
  4012f1:	41 c7 86 00 fe ff ff 0e 00 00 00 	movl   $0xe,-0x200(%r14)
    data[x].freelist = freelist;
  4012fc:	49 89 86 20 fd ff ff 	mov    %rax,-0x2e0(%r14)
    data[x].newmask = 0;
  401303:	41 c7 86 48 fd ff ff 00 00 00 00 	movl   $0x0,-0x2b8(%r14)
    data[x].thiswrite = threadsize;
  40130e:	41 c7 46 a8 0f 00 00 00 	movl   $0xf,-0x58(%r14)
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
  401357:	41 83 fd 0f          	cmp    $0xf,%r13d
  40135b:	0f 85 b7 fe ff ff    	jne    401218 <main+0x158>
  401361:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
  401366:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
  40136b:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  401370:	49 c7 c5 c0 1e 40 00 	mov    $0x401ec0,%r13
  401377:	48 8d 85 48 03 00 00 	lea    0x348(%rbp),%rax
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
  40140d:	48 83 c5 78          	add    $0x78,%rbp
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
  40147f:	c7 83 5c 31 00 00 00 00 00 00 	movl   $0x0,0x315c(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  401489:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    
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
  long sends = 8;
  for (int x = 0; x < threadsize; x++) {
  4014b8:	4c 8d b3 c8 34 00 00 	lea    0x34c8(%rbx),%r14
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
  4014f9:	48 8d 35 a5 0b 00 00 	lea    0xba5(%rip),%rsi        # 4020a5 <_IO_stdin_used+0xa5>
  401500:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
  40150a:	bf 01 00 00 00       	mov    $0x1,%edi
  40150f:	48 f7 ed             	imul   %rbp
  401512:	4c 89 e0             	mov    %r12,%rax
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  401515:	49 c1 e4 03          	shl    $0x3,%r12
  401519:	4c 8d b3 d0 34 00 00 	lea    0x34d0(%rbx),%r14
  printf("freq: %ld\n", freq/ seconds);
  401520:	48 c1 f8 3f          	sar    $0x3f,%rax
  401524:	48 d1 fa             	sar    %rdx
  401527:	48 29 c2             	sub    %rax,%rdx
  40152a:	31 c0                	xor    %eax,%eax
  40152c:	49 89 d5             	mov    %rdx,%r13
  40152f:	e8 5c fb ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  401534:	4c 89 e0             	mov    %r12,%rax
  401537:	49 c1 fc 3f          	sar    $0x3f,%r12
  40153b:	48 8d 35 6e 0b 00 00 	lea    0xb6e(%rip),%rsi        # 4020b0 <_IO_stdin_used+0xb0>
  401542:	48 f7 ed             	imul   %rbp
  401545:	bf 01 00 00 00       	mov    $0x1,%edi
  40154a:	31 c0                	xor    %eax,%eax
  40154c:	48 89 d5             	mov    %rdx,%rbp
  40154f:	48 d1 fd             	sar    %rbp
  401552:	4c 29 e5             	sub    %r12,%rbp
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  401555:	41 bc 00 ca 9a 3b    	mov    $0x3b9aca00,%r12d
  40155b:	48 89 ea             	mov    %rbp,%rdx
  40155e:	e8 2d fb ff ff       	call   401090 <__printf_chk@plt>
  401563:	4c 89 e0             	mov    %r12,%rax
  401566:	bf 01 00 00 00       	mov    $0x1,%edi
  40156b:	48 8d 35 4c 0b 00 00 	lea    0xb4c(%rip),%rsi        # 4020be <_IO_stdin_used+0xbe>
  401572:	48 99                	cqto
  401574:	49 f7 fd             	idiv   %r13
  401577:	49 89 c5             	mov    %rax,%r13
  40157a:	48 89 c2             	mov    %rax,%rdx
  40157d:	31 c0                	xor    %eax,%eax
  40157f:	e8 0c fb ff ff       	call   401090 <__printf_chk@plt>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  401584:	4d 85 ed             	test   %r13,%r13
  401587:	49 8d 55 07          	lea    0x7(%r13),%rdx
  40158b:	48 8d 35 40 0b 00 00 	lea    0xb40(%rip),%rsi        # 4020d2 <_IO_stdin_used+0xd2>
  401592:	49 0f 49 d5          	cmovns %r13,%rdx
  401596:	bf 01 00 00 00       	mov    $0x1,%edi
  40159b:	31 c0                	xor    %eax,%eax
  40159d:	4c 8d 2d 5f 0b 00 00 	lea    0xb5f(%rip),%r13        # 402103 <_IO_stdin_used+0x103>
  4015a4:	48 c1 fa 03          	sar    $0x3,%rdx
  4015a8:	e8 e3 fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  4015ad:	4c 89 e0             	mov    %r12,%rax
  4015b0:	bf 01 00 00 00       	mov    $0x1,%edi
  long freq_writes = 0;
  4015b5:	45 31 e4             	xor    %r12d,%r12d
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  4015b8:	48 99                	cqto
  4015ba:	48 8d 35 2f 0b 00 00 	lea    0xb2f(%rip),%rsi        # 4020f0 <_IO_stdin_used+0xf0>
  4015c1:	48 f7 fd             	idiv   %rbp
  4015c4:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  4015c8:	48 89 c2             	mov    %rax,%rdx
  4015cb:	31 c0                	xor    %eax,%eax
  4015cd:	e8 be fa ff ff       	call   401090 <__printf_chk@plt>
  
  for (int x = 0; x < threadsize; x++) {
  4015d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    freq_writes += data[x].freq_writes;
  4015d8:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4015dc:	4c 89 ee             	mov    %r13,%rsi
  4015df:	bf 01 00 00 00       	mov    $0x1,%edi
  4015e4:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  4015e6:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
    freq_writes += data[x].freq_writes;
  4015ed:	49 01 d4             	add    %rdx,%r12
  4015f0:	e8 9b fa ff ff       	call   401090 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  4015f5:	49 39 ee             	cmp    %rbp,%r14
  4015f8:	75 de                	jne    4015d8 <main+0x518>
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  4015fa:	4c 89 e0             	mov    %r12,%rax
  4015fd:	48 8d 35 0b 0b 00 00 	lea    0xb0b(%rip),%rsi        # 40210f <_IO_stdin_used+0x10f>
  401604:	bf 01 00 00 00       	mov    $0x1,%edi
  401609:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
  401613:	48 f7 ed             	imul   %rbp
  401616:	4c 89 e0             	mov    %r12,%rax

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  401619:	49 c1 e4 03          	shl    $0x3,%r12
  printf("freq_writes: %ld\n", freq_writes / seconds);
  40161d:	48 c1 f8 3f          	sar    $0x3f,%rax
  401621:	48 d1 fa             	sar    %rdx
  401624:	48 29 c2             	sub    %rax,%rdx
  401627:	31 c0                	xor    %eax,%eax
  401629:	49 89 d5             	mov    %rdx,%r13
  40162c:	e8 5f fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  401631:	4c 89 e0             	mov    %r12,%rax
  401634:	49 c1 fc 3f          	sar    $0x3f,%r12
  401638:	48 8d 35 e2 0a 00 00 	lea    0xae2(%rip),%rsi        # 402121 <_IO_stdin_used+0x121>
  40163f:	48 f7 ed             	imul   %rbp
  401642:	bf 01 00 00 00       	mov    $0x1,%edi
  401647:	31 c0                	xor    %eax,%eax
  401649:	48 89 d5             	mov    %rdx,%rbp
  40164c:	48 d1 fd             	sar    %rbp
  40164f:	4c 29 e5             	sub    %r12,%rbp
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  401652:	41 bc 00 ca 9a 3b    	mov    $0x3b9aca00,%r12d
  401658:	48 89 ea             	mov    %rbp,%rdx
  40165b:	e8 30 fa ff ff       	call   401090 <__printf_chk@plt>
  401660:	4c 89 e0             	mov    %r12,%rax
  401663:	bf 01 00 00 00       	mov    $0x1,%edi
  401668:	48 8d 35 ca 0a 00 00 	lea    0xaca(%rip),%rsi        # 402139 <_IO_stdin_used+0x139>
  40166f:	48 99                	cqto
  401671:	49 f7 fd             	idiv   %r13
  401674:	49 89 c5             	mov    %rax,%r13
  401677:	48 89 c2             	mov    %rax,%rdx
  40167a:	31 c0                	xor    %eax,%eax
  40167c:	e8 0f fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes per thread latency: %ld\n", (1000000000/(freq_writes / seconds)) / sends);
  401681:	4d 85 ed             	test   %r13,%r13
  401684:	49 8d 55 07          	lea    0x7(%r13),%rdx
  401688:	48 8d 35 19 0b 00 00 	lea    0xb19(%rip),%rsi        # 4021a8 <_IO_stdin_used+0x1a8>
  40168f:	49 0f 49 d5          	cmovns %r13,%rdx
  401693:	bf 01 00 00 00       	mov    $0x1,%edi
  401698:	31 c0                	xor    %eax,%eax
  40169a:	48 c1 fa 03          	sar    $0x3,%rdx
  40169e:	e8 ed f9 ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * sends) / seconds));
  4016a3:	4c 89 e0             	mov    %r12,%rax
  4016a6:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ab:	48 8d 35 a2 0a 00 00 	lea    0xaa2(%rip),%rsi        # 402154 <_IO_stdin_used+0x154>
  4016b2:	48 99                	cqto
  4016b4:	48 f7 fd             	idiv   %rbp
  4016b7:	48 8d 2d 0f 0a 00 00 	lea    0xa0f(%rip),%rbp        # 4020cd <_IO_stdin_used+0xcd>
  4016be:	48 89 c2             	mov    %rax,%rdx
  4016c1:	31 c0                	xor    %eax,%eax
  4016c3:	e8 c8 f9 ff ff       	call   401090 <__printf_chk@plt>
  4016c8:	48 8d 3d 9f 0a 00 00 	lea    0xa9f(%rip),%rdi        # 40216e <_IO_stdin_used+0x16e>
  4016cf:	e8 6c f9 ff ff       	call   401040 <puts@plt>
  4016d4:	48 89 ee             	mov    %rbp,%rsi
  4016d7:	bf 01 00 00 00       	mov    $0x1,%edi
  4016dc:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  4016de:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  4016e5:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4016ec:	e8 9f f9 ff ff       	call   401090 <__printf_chk@plt>
  4016f1:	48 89 ee             	mov    %rbp,%rsi
  4016f4:	bf 01 00 00 00       	mov    $0x1,%edi
  4016f9:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  4016fb:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  401702:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  401709:	e8 82 f9 ff ff       	call   401090 <__printf_chk@plt>
  40170e:	48 89 ee             	mov    %rbp,%rsi
  401711:	bf 01 00 00 00       	mov    $0x1,%edi
  401716:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  401718:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  40171f:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401726:	e8 65 f9 ff ff       	call   401090 <__printf_chk@plt>
  40172b:	48 89 ee             	mov    %rbp,%rsi
  40172e:	bf 01 00 00 00       	mov    $0x1,%edi
  401733:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  401735:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  40173c:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  401743:	e8 48 f9 ff ff       	call   401090 <__printf_chk@plt>
  401748:	48 89 ee             	mov    %rbp,%rsi
  40174b:	bf 01 00 00 00       	mov    $0x1,%edi
  401750:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  401752:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401759:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  401760:	e8 2b f9 ff ff       	call   401090 <__printf_chk@plt>
  401765:	48 89 ee             	mov    %rbp,%rsi
  401768:	bf 01 00 00 00       	mov    $0x1,%edi
  40176d:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  40176f:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401776:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  40177d:	e8 0e f9 ff ff       	call   401090 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  401782:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  401789:	31 c0                	xor    %eax,%eax
  40178b:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  401792:	48 8d 35 e2 09 00 00 	lea    0x9e2(%rip),%rsi        # 40217b <_IO_stdin_used+0x17b>
  401799:	bf 01 00 00 00       	mov    $0x1,%edi
  40179e:	e8 ed f8 ff ff       	call   401090 <__printf_chk@plt>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  4017a3:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  4017a8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4017b1:	75 11                	jne    4017c4 <main+0x704>
  4017b3:	48 83 c4 78          	add    $0x78,%rsp
  4017b7:	31 c0                	xor    %eax,%eax
  4017b9:	5b                   	pop    %rbx
  4017ba:	5d                   	pop    %rbp
  4017bb:	41 5c                	pop    %r12
  4017bd:	41 5d                	pop    %r13
  4017bf:	41 5e                	pop    %r14
  4017c1:	41 5f                	pop    %r15
  4017c3:	c3                   	ret
  4017c4:	e8 97 f8 ff ff       	call   401060 <__stack_chk_fail@plt>
  4017c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000004017d0 <_start>:
  4017d0:	f3 0f 1e fa          	endbr64
  4017d4:	31 ed                	xor    %ebp,%ebp
  4017d6:	49 89 d1             	mov    %rdx,%r9
  4017d9:	5e                   	pop    %rsi
  4017da:	48 89 e2             	mov    %rsp,%rdx
  4017dd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4017e1:	50                   	push   %rax
  4017e2:	54                   	push   %rsp
  4017e3:	45 31 c0             	xor    %r8d,%r8d
  4017e6:	31 c9                	xor    %ecx,%ecx
  4017e8:	48 c7 c7 c0 10 40 00 	mov    $0x4010c0,%rdi
  4017ef:	ff 15 fb 27 00 00    	call   *0x27fb(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  4017f5:	f4                   	hlt
  4017f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401800 <_dl_relocate_static_pie>:
  401800:	f3 0f 1e fa          	endbr64
  401804:	c3                   	ret
  401805:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40180f:	90                   	nop

0000000000401810 <deregister_tm_clones>:
  401810:	b8 10 40 40 00       	mov    $0x404010,%eax
  401815:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  40181b:	74 13                	je     401830 <deregister_tm_clones+0x20>
  40181d:	b8 00 00 00 00       	mov    $0x0,%eax
  401822:	48 85 c0             	test   %rax,%rax
  401825:	74 09                	je     401830 <deregister_tm_clones+0x20>
  401827:	bf 10 40 40 00       	mov    $0x404010,%edi
  40182c:	ff e0                	jmp    *%rax
  40182e:	66 90                	xchg   %ax,%ax
  401830:	c3                   	ret
  401831:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40183c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401840 <register_tm_clones>:
  401840:	be 10 40 40 00       	mov    $0x404010,%esi
  401845:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  40184c:	48 89 f0             	mov    %rsi,%rax
  40184f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401853:	48 c1 f8 03          	sar    $0x3,%rax
  401857:	48 01 c6             	add    %rax,%rsi
  40185a:	48 d1 fe             	sar    %rsi
  40185d:	74 11                	je     401870 <register_tm_clones+0x30>
  40185f:	b8 00 00 00 00       	mov    $0x0,%eax
  401864:	48 85 c0             	test   %rax,%rax
  401867:	74 07                	je     401870 <register_tm_clones+0x30>
  401869:	bf 10 40 40 00       	mov    $0x404010,%edi
  40186e:	ff e0                	jmp    *%rax
  401870:	c3                   	ret
  401871:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40187c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401880 <__do_global_dtors_aux>:
  401880:	f3 0f 1e fa          	endbr64
  401884:	80 3d 85 27 00 00 00 	cmpb   $0x0,0x2785(%rip)        # 404010 <__TMC_END__>
  40188b:	75 13                	jne    4018a0 <__do_global_dtors_aux+0x20>
  40188d:	55                   	push   %rbp
  40188e:	48 89 e5             	mov    %rsp,%rbp
  401891:	e8 7a ff ff ff       	call   401810 <deregister_tm_clones>
  401896:	c6 05 73 27 00 00 01 	movb   $0x1,0x2773(%rip)        # 404010 <__TMC_END__>
  40189d:	5d                   	pop    %rbp
  40189e:	c3                   	ret
  40189f:	90                   	nop
  4018a0:	c3                   	ret
  4018a1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4018ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004018b0 <frame_dummy>:
  4018b0:	f3 0f 1e fa          	endbr64
  4018b4:	eb 8a                	jmp    401840 <register_tm_clones>
  4018b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004018c0 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  4018c0:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4018c4:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  4018c7:	7e 77                	jle    401940 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  4018c9:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4018cd:	55                   	push   %rbp
  4018ce:	49 89 f2             	mov    %rsi,%r10
  4018d1:	49 89 d3             	mov    %rdx,%r11
  4018d4:	53                   	push   %rbx
  4018d5:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  4018d8:	48 8b 98 a0 03 00 00 	mov    0x3a0(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  4018df:	b8 01 00 00 00       	mov    $0x1,%eax
  4018e4:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  4018e8:	48 63 d0             	movslq %eax,%rdx
  4018eb:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  4018ee:	85 d2                	test   %edx,%edx
  4018f0:	40 0f 94 c6          	sete   %sil
  4018f4:	f6 c2 04             	test   $0x4,%dl
  4018f7:	75 05                	jne    4018fe <pollthreads+0x3e>
  4018f9:	40 84 f6             	test   %sil,%sil
  4018fc:	74 0d                	je     40190b <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  4018fe:	49 63 08             	movslq (%r8),%rcx
  401901:	8d 69 01             	lea    0x1(%rcx),%ebp
  401904:	41 89 28             	mov    %ebp,(%r8)
  401907:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  40190b:	83 e2 08             	and    $0x8,%edx
  40190e:	75 05                	jne    401915 <pollthreads+0x55>
  401910:	40 84 f6             	test   %sil,%sil
  401913:	74 1b                	je     401930 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  401915:	48 63 17             	movslq (%rdi),%rdx
  401918:	8d 4a 01             	lea    0x1(%rdx),%ecx
  40191b:	89 0f                	mov    %ecx,(%rdi)
  40191d:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  401921:	83 c0 01             	add    $0x1,%eax
  401924:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401928:	7f be                	jg     4018e8 <pollthreads+0x28>
}
  40192a:	31 c0                	xor    %eax,%eax
  40192c:	5b                   	pop    %rbx
  40192d:	5d                   	pop    %rbp
  40192e:	c3                   	ret
  40192f:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  401930:	83 c0 01             	add    $0x1,%eax
  401933:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401937:	7f af                	jg     4018e8 <pollthreads+0x28>
}
  401939:	31 c0                	xor    %eax,%eax
  40193b:	5b                   	pop    %rbx
  40193c:	5d                   	pop    %rbp
  40193d:	c3                   	ret
  40193e:	66 90                	xchg   %ax,%ax
  401940:	31 c0                	xor    %eax,%eax
  401942:	c3                   	ret
  401943:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40194e:	66 90                	xchg   %ax,%ax

0000000000401950 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401950:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401953:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
      if (*availableidx == 0) {
  40195a:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40195d:	48 83 c7 01          	add    $0x1,%rdi
  401961:	48 85 ff             	test   %rdi,%rdi
  401964:	7e 66                	jle    4019cc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401966:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40196d:	31 c9                	xor    %ecx,%ecx
  40196f:	45 31 c9             	xor    %r9d,%r9d
  401972:	31 c0                	xor    %eax,%eax
  401974:	eb 18                	jmp    40198e <findavailable+0x3e>
  401976:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401980:	83 c1 01             	add    $0x1,%ecx
  401983:	48 63 c1             	movslq %ecx,%rax
  401986:	49 89 c1             	mov    %rax,%r9
  401989:	48 39 f8             	cmp    %rdi,%rax
  40198c:	7d 3e                	jge    4019cc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  40198e:	48 c1 e0 05          	shl    $0x5,%rax
  401992:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401998:	75 e6                	jne    401980 <findavailable+0x30>
         available[*availableidx] = x;
  40199a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  40199d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  4019a1:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  4019a5:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  4019a8:	41 8b 43 68          	mov    0x68(%r11),%eax
  4019ac:	01 c0                	add    %eax,%eax
  4019ae:	41 39 c0             	cmp    %eax,%r8d
  4019b1:	74 19                	je     4019cc <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4019b3:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  4019ba:	83 c1 01             	add    $0x1,%ecx
  4019bd:	48 63 c1             	movslq %ecx,%rax
  4019c0:	48 83 c7 01          	add    $0x1,%rdi
  4019c4:	49 89 c1             	mov    %rax,%r9
  4019c7:	48 39 f8             	cmp    %rdi,%rax
  4019ca:	7c c2                	jl     40198e <findavailable+0x3e>
      if (*availableidx == 0) {
  4019cc:	31 c0                	xor    %eax,%eax
  4019ce:	45 85 c0             	test   %r8d,%r8d
  4019d1:	0f 94 c0             	sete   %al
}
  4019d4:	c3                   	ret
  4019d5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000004019e0 <singlewriter3>:
}
  4019e0:	c3                   	ret
  4019e1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4019ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004019f0 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4019f0:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  4019f6:	85 c0                	test   %eax,%eax
  4019f8:	74 1e                	je     401a18 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  4019fa:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4019fc:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  4019fd:	55                   	push   %rbp
  4019fe:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4019ff:	8b 77 68             	mov    0x68(%rdi),%esi
  401a02:	48 89 fb             	mov    %rdi,%rbx
  401a05:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401a08:	f7 f9                	idiv   %ecx
  401a0a:	85 d2                	test   %edx,%edx
  401a0c:	74 12                	je     401a20 <singlewriter2+0x30>
}
  401a0e:	5b                   	pop    %rbx
  401a0f:	5d                   	pop    %rbp
  401a10:	41 5c                	pop    %r12
  401a12:	c3                   	ret
  401a13:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401a18:	c3                   	ret
  401a19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct Data * thread = &data->threads[data->threadindex];
  401a20:	48 63 47 64          	movslq 0x64(%rdi),%rax
  401a24:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  401a2c:	48 29 c5             	sub    %rax,%rbp
  401a2f:	48 c1 e5 07          	shl    $0x7,%rbp
  401a33:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401a37:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401a3c:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401a43:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401a47:	49 c1 e4 04          	shl    $0x4,%r12
  401a4b:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401a52:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401a57:	e8 f4 f5 ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401a5c:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401a62:	83 c0 01             	add    $0x1,%eax
  401a65:	99                   	cltd
  401a66:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  401a6c:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401a6f:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401a75:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401a79:	48 8b 05 50 07 00 00 	mov    0x750(%rip),%rax        # 4021d0 <_IO_stdin_used+0x1d0>
  401a80:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  401a85:	5b                   	pop    %rbx
  401a86:	5d                   	pop    %rbp
  401a87:	41 5c                	pop    %r12
  401a89:	c3                   	ret
  401a8a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000401a90 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a90:	41 55                	push   %r13
  401a92:	49 89 d5             	mov    %rdx,%r13
  401a95:	41 54                	push   %r12
  401a97:	49 89 cc             	mov    %rcx,%r12
  401a9a:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401a9b:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a9e:	48 89 fd             	mov    %rdi,%rbp
  401aa1:	53                   	push   %rbx
  401aa2:	48 89 f3             	mov    %rsi,%rbx
  401aa5:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401aa9:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401aad:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401ab6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401abb:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401abd:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401ac5:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  401acb:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401ad3:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401adb:	83 c0 01             	add    $0x1,%eax
  401ade:	99                   	cltd
  401adf:	f7 7f 68             	idivl  0x68(%rdi)
  401ae2:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401ae8:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401aed:	4c 89 e9             	mov    %r13,%rcx
  401af0:	e8 5b fe ff ff       	call   401950 <findavailable>
  if (fill == 1) {
  401af5:	83 f8 01             	cmp    $0x1,%eax
  401af8:	0f 84 64 01 00 00    	je     401c62 <singlewriter+0x1d2>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401afe:	48 89 ef             	mov    %rbp,%rdi
  401b01:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401b06:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401b0b:	4c 89 e2             	mov    %r12,%rdx
  401b0e:	4c 89 ee             	mov    %r13,%rsi
  401b11:	e8 aa fd ff ff       	call   4018c0 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401b16:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401b1b:	85 ff                	test   %edi,%edi
  401b1d:	0f 8e 66 01 00 00    	jle    401c89 <singlewriter+0x1f9>
  401b23:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401b28:	31 c9                	xor    %ecx,%ecx
  401b2a:	eb 62                	jmp    401b8e <singlewriter+0xfe>
  401b2c:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b30:	48 8b 14 cb          	mov    (%rbx,%rcx,8),%rdx
          int thread = readyreaders[x];
  401b34:	4d 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%r10
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b39:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401b3c:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b40:	48 c1 e2 05          	shl    $0x5,%rdx
  401b44:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].reading = chunk;
  401b4b:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
          data->threads[thread].start = start;
  401b53:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401b57:	66 0f 6e 4a 08       	movd   0x8(%rdx),%xmm1
          data->threads[thread].reading = chunk;
  401b5c:	4c 29 d0             	sub    %r10,%rax
          chunk->available = READING;
  401b5f:	c7 42 10 02 00 00 00 	movl   $0x2,0x10(%rdx)
          data->threads[thread].reading = chunk;
  401b66:	48 c1 e0 07          	shl    $0x7,%rax
  401b6a:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].start = start;
  401b6e:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401b72:	48 89 90 a8 00 00 00 	mov    %rdx,0xa8(%rax)
          chunk->owner = thread;
  401b79:	44 89 52 14          	mov    %r10d,0x14(%rdx)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401b7d:	83 88 c8 00 00 00 10 	orl    $0x10,0xc8(%rax)
          data->threads[thread].start = start;
  401b84:	66 0f d6 40 14       	movq   %xmm0,0x14(%rax)
        for (int x = 0; x < readers ; x++) {
  401b89:	48 39 cf             	cmp    %rcx,%rdi
  401b8c:	74 07                	je     401b95 <singlewriter+0x105>
  401b8e:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401b90:	4c 39 c1             	cmp    %r8,%rcx
  401b93:	75 9b                	jne    401b30 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401b95:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401b9a:	45 85 c0             	test   %r8d,%r8d
  401b9d:	7e 7a                	jle    401c19 <singlewriter+0x189>
                if (assignedchunk  == availableidx) {
  401b9f:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401ba3:	41 01 f0             	add    %esi,%r8d
  401ba6:	eb 6d                	jmp    401c15 <singlewriter+0x185>
  401ba8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401bb0:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401bb3:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401bb6:	45 8b 0c 24          	mov    (%r12),%r9d
   for (int x = 0; x < writers ; x++) {
  401bba:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401bbe:	48 8b 14 f3          	mov    (%rbx,%rsi,8),%rdx
          data->threads[thread].writing = chunk;
  401bc2:	49 63 f1             	movslq %r9d,%rsi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401bc5:	48 c1 e2 05          	shl    $0x5,%rdx
  401bc9:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].writing = chunk;
  401bd0:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
          data->threads[thread].publishstart = start;
  401bd8:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401bdc:	66 0f 6e 52 08       	movd   0x8(%rdx),%xmm2
          data->threads[thread].writing = chunk;
  401be1:	48 29 f0             	sub    %rsi,%rax
      chunk->available = WRITING;
  401be4:	c7 42 10 03 00 00 00 	movl   $0x3,0x10(%rdx)
          data->threads[thread].writing = chunk;
  401beb:	48 c1 e0 07          	shl    $0x7,%rax
  401bef:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].publishstart = start;
  401bf3:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401bf7:	48 89 90 b0 00 00 00 	mov    %rdx,0xb0(%rax)
          chunk->owner = thread;
  401bfe:	44 89 4a 14          	mov    %r9d,0x14(%rdx)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401c02:	83 88 c8 00 00 00 20 	orl    $0x20,0xc8(%rax)
          data->threads[thread].publishstart = start;
  401c09:	66 0f d6 40 40       	movq   %xmm0,0x40(%rax)
   for (int x = 0; x < writers ; x++) {
  401c0e:	44 39 c1             	cmp    %r8d,%ecx
  401c11:	74 06                	je     401c19 <singlewriter+0x189>
  401c13:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401c15:	39 f7                	cmp    %esi,%edi
  401c17:	75 97                	jne    401bb0 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401c19:	8b 7d 68             	mov    0x68(%rbp),%edi
  401c1c:	85 ff                	test   %edi,%edi
  401c1e:	7e 40                	jle    401c60 <singlewriter+0x1d0>
        if (data->threads[x].newmask != 0) {
  401c20:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401c24:	31 d2                	xor    %edx,%edx
  401c26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401c30:	48 63 ca             	movslq %edx,%rcx
  401c33:	48 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rax
  401c3b:	48 29 c8             	sub    %rcx,%rax
  401c3e:	48 c1 e0 07          	shl    $0x7,%rax
  401c42:	4c 01 c0             	add    %r8,%rax
  401c45:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401c4b:	85 f6                	test   %esi,%esi
  401c4d:	74 31                	je     401c80 <singlewriter+0x1f0>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401c4f:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401c53:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401c56:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401c59:	8b 7d 68             	mov    0x68(%rbp),%edi
  401c5c:	39 fa                	cmp    %edi,%edx
  401c5e:	7c d0                	jl     401c30 <singlewriter+0x1a0>
  return 0;
  401c60:	31 c0                	xor    %eax,%eax
}
  401c62:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401c67:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401c70:	75 1e                	jne    401c90 <singlewriter+0x200>
  401c72:	48 83 c4 28          	add    $0x28,%rsp
  401c76:	5b                   	pop    %rbx
  401c77:	5d                   	pop    %rbp
  401c78:	41 5c                	pop    %r12
  401c7a:	41 5d                	pop    %r13
  401c7c:	c3                   	ret
  401c7d:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401c80:	83 c2 01             	add    $0x1,%edx
  401c83:	39 fa                	cmp    %edi,%edx
  401c85:	7c a9                	jl     401c30 <singlewriter+0x1a0>
  401c87:	eb d7                	jmp    401c60 <singlewriter+0x1d0>
      int assignedchunk = 0;
  401c89:	31 f6                	xor    %esi,%esi
  401c8b:	e9 05 ff ff ff       	jmp    401b95 <singlewriter+0x105>
}
  401c90:	e8 cb f3 ff ff       	call   401060 <__stack_chk_fail@plt>
  401c95:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401ca0 <threadwork>:
int * threadwork(struct Data * data) {
  401ca0:	55                   	push   %rbp
  401ca1:	53                   	push   %rbx
  401ca2:	48 89 fb             	mov    %rdi,%rbx
  401ca5:	48 83 ec 28          	sub    $0x28,%rsp
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401ca9:	48 63 4f 68          	movslq 0x68(%rdi),%rcx
  long thiswrite = data->main->globalwrite;
  401cad:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401cb6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401cbb:	48 8b 47 28          	mov    0x28(%rdi),%rax
  401cbf:	48 8b a8 50 03 00 00 	mov    0x350(%rax),%rbp
  long lastcursor = data->main->writecursor;
  401cc6:	8b b0 80 01 00 00    	mov    0x180(%rax),%esi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401ccc:	48 8b 80 38 03 00 00 	mov    0x338(%rax),%rax
    data->thiswrite = lastcursor;
  401cd3:	89 b7 28 03 00 00    	mov    %esi,0x328(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401cd9:	48 89 e6             	mov    %rsp,%rsi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401cdc:	48 99                	cqto
  401cde:	48 f7 f9             	idiv   %rcx
    data->prevwrite = lastwrite;
  401ce1:	48 89 97 10 03 00 00 	mov    %rdx,0x310(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401ce8:	bf 04 00 00 00       	mov    $0x4,%edi
  401ced:	e8 5e f3 ff ff       	call   401050 <clock_gettime@plt>
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401cf2:	4c 8b 53 28          	mov    0x28(%rbx),%r10
  401cf6:	48 63 4b 68          	movslq 0x68(%rbx),%rcx
  401cfa:	48 bf 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%rdi
  401d04:	44 8b 4b 64          	mov    0x64(%rbx),%r9d
   data->freq_writes++;
  401d08:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401d0d:	49 8b 82 50 03 00 00 	mov    0x350(%r10),%rax
        epoch->time = time;
  401d14:	66 0f 6f 04 24       	movdqa (%rsp),%xmm0
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401d19:	48 99                	cqto
  401d1b:	48 f7 f9             	idiv   %rcx
  401d1e:	48 89 c1             	mov    %rax,%rcx
  401d21:	48 f7 ef             	imul   %rdi
  401d24:	48 89 c8             	mov    %rcx,%rax
  401d27:	48 c1 f8 3f          	sar    $0x3f,%rax
  401d2b:	48 01 ca             	add    %rcx,%rdx
  401d2e:	48 c1 fa 07          	sar    $0x7,%rdx
  401d32:	48 29 c2             	sub    %rax,%rdx
  401d35:	48 89 d0             	mov    %rdx,%rax
  401d38:	48 c1 e0 08          	shl    $0x8,%rax
  401d3c:	48 29 d0             	sub    %rdx,%rax
  401d3f:	48 29 c1             	sub    %rax,%rcx
  401d42:	49 63 c1             	movslq %r9d,%rax
        struct Data * thread = &data->threads[data->threadindex];
  401d45:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401d4d:	48 c1 e1 10          	shl    $0x10,%rcx
        struct Data * thread = &data->threads[data->threadindex];
  401d51:	48 29 c6             	sub    %rax,%rsi
        long buffer = ( (data->main->globalwrite / (data->threadsize)) % 0xff) << 16 | data->threadindex;
  401d54:	48 09 c1             	or     %rax,%rcx
        struct Data * thread = &data->threads[data->threadindex];
  401d57:	48 c1 e6 07          	shl    $0x7,%rsi
  401d5b:	48 03 73 30          	add    0x30(%rbx),%rsi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401d5f:	48 63 96 24 03 00 00 	movslq 0x324(%rsi),%rdx
  401d66:	48 89 d0             	mov    %rdx,%rax
  401d69:	4c 8d 04 52          	lea    (%rdx,%rdx,2),%r8
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d6d:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401d70:	49 c1 e0 04          	shl    $0x4,%r8
  401d74:	4c 03 86 18 03 00 00 	add    0x318(%rsi),%r8
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d7b:	99                   	cltd
        epoch->time = time;
  401d7c:	41 0f 11 40 08       	movups %xmm0,0x8(%r8)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d81:	f7 be 20 03 00 00    	idivl  0x320(%rsi)
  data->main->works[buffer] = data->threadindex;
  401d87:	49 8b 42 70          	mov    0x70(%r10),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d8b:	89 96 24 03 00 00    	mov    %edx,0x324(%rsi)
        epoch->thread = data->threadindex;
  401d91:	45 89 08             	mov    %r9d,(%r8)
  epoch->buffer = buffer;
  401d94:	49 89 48 18          	mov    %rcx,0x18(%r8)
  epoch->set = 1;
  401d98:	41 c7 40 24 01 00 00 00 	movl   $0x1,0x24(%r8)
  data->main->works[buffer] = data->threadindex;
  401da0:	44 88 0c 08          	mov    %r9b,(%rax,%rcx,1)
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_RELAXED);
  401da4:	48 8b 43 28          	mov    0x28(%rbx),%rax
  401da8:	f0 48 83 80 50 03 00 00 01 	lock addq $0x1,0x350(%rax)
  long lastread = data->main->totalreads % data->threadsize;
  401db1:	48 8b 43 28          	mov    0x28(%rbx),%rax
  401db5:	4c 63 43 68          	movslq 0x68(%rbx),%r8
      if (data->globalread < thiswrite) {  
  401db9:	48 8b 8b 48 03 00 00 	mov    0x348(%rbx),%rcx
  long lastread = data->main->totalreads % data->threadsize;
  401dc0:	48 8b 80 40 03 00 00 	mov    0x340(%rax),%rax
   data->freq++;
  401dc7:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
  long lastread = data->main->totalreads % data->threadsize;
  401dcc:	48 99                	cqto
  401dce:	49 f7 f8             	idiv   %r8
   data->prevread = lastread;
  401dd1:	48 89 93 08 03 00 00 	mov    %rdx,0x308(%rbx)
      if (data->globalread < thiswrite) {  
  401dd8:	48 39 e9             	cmp    %rbp,%rcx
  401ddb:	0f 8d bf 00 00 00    	jge    401ea0 <threadwork+0x200>
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401de1:	48 63 96 24 03 00 00 	movslq 0x324(%rsi),%rdx
            thepoch->time = time; 
  401de8:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
         buffer = (past << 16) | data->readcursor;
  401ded:	44 8b 93 00 02 00 00 	mov    0x200(%rbx),%r10d
                &data->threads[data->threadindex];
  401df4:	8b 6b 64             	mov    0x64(%rbx),%ebp
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401df7:	48 89 d0             	mov    %rdx,%rax
  401dfa:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401dfe:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401e01:	49 c1 e1 04          	shl    $0x4,%r9
  401e05:	4c 03 8e 18 03 00 00 	add    0x318(%rsi),%r9
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e0c:	99                   	cltd
            thepoch->time = time; 
  401e0d:	41 0f 11 49 08       	movups %xmm1,0x8(%r9)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e12:	f7 be 20 03 00 00    	idivl  0x320(%rsi)
            long past = (((data->globalread) / (data->threadsize)) - 2) % 0xff;
  401e18:	48 89 c8             	mov    %rcx,%rax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e1b:	89 96 24 03 00 00    	mov    %edx,0x324(%rsi)
            long past = (((data->globalread) / (data->threadsize)) - 2) % 0xff;
  401e21:	48 99                	cqto
  401e23:	49 f7 f8             	idiv   %r8
          thepoch->set = 1;
  401e26:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
            long past = (((data->globalread) / (data->threadsize)) - 2) % 0xff;
  401e2e:	48 8d 70 fe          	lea    -0x2(%rax),%rsi
  401e32:	48 89 f0             	mov    %rsi,%rax
  401e35:	48 f7 ef             	imul   %rdi
  401e38:	48 89 f0             	mov    %rsi,%rax
  401e3b:	48 c1 f8 3f          	sar    $0x3f,%rax
  401e3f:	48 01 f2             	add    %rsi,%rdx
  401e42:	48 c1 fa 07          	sar    $0x7,%rdx
  401e46:	48 29 c2             	sub    %rax,%rdx
  401e49:	48 89 d0             	mov    %rdx,%rax
  401e4c:	48 c1 e0 08          	shl    $0x8,%rax
  401e50:	48 29 d0             	sub    %rdx,%rax
  401e53:	48 29 c6             	sub    %rax,%rsi
         buffer = (past << 16) | data->readcursor;
  401e56:	b8 00 00 00 00       	mov    $0x0,%eax
            long past = (((data->globalread) / (data->threadsize)) - 2) % 0xff;
  401e5b:	48 89 f2             	mov    %rsi,%rdx
         buffer = (past << 16) | data->readcursor;
  401e5e:	48 0f 48 d0          	cmovs  %rax,%rdx
  401e62:	49 63 c2             	movslq %r10d,%rax
  401e65:	48 c1 e2 10          	shl    $0x10,%rdx
  401e69:	48 09 c2             	or     %rax,%rdx
     data->readcursor = (data->readcursor + 1) % data->threadsize;
  401e6c:	41 8d 42 01          	lea    0x1(%r10),%eax
         buffer = (past << 16) | data->readcursor;
  401e70:	49 89 51 18          	mov    %rdx,0x18(%r9)
     data->readcursor = (data->readcursor + 1) % data->threadsize;
  401e74:	99                   	cltd
  401e75:	41 f7 f8             	idiv   %r8d
  401e78:	8d 45 01             	lea    0x1(%rbp),%eax
  401e7b:	39 d5                	cmp    %edx,%ebp
  401e7d:	0f 45 c2             	cmovne %edx,%eax
  401e80:	89 c6                	mov    %eax,%esi
      data->globalread++;
  401e82:	48 8d 41 01          	lea    0x1(%rcx),%rax
        if (data->globalread % data->threadsize == 0) {
  401e86:	48 99                	cqto
      data->globalread++;
  401e88:	48 89 83 48 03 00 00 	mov    %rax,0x348(%rbx)
        if (data->globalread % data->threadsize == 0) {
  401e8f:	49 f7 f8             	idiv   %r8
          data->readcursor = 0;
  401e92:	31 c0                	xor    %eax,%eax
  401e94:	48 85 d2             	test   %rdx,%rdx
  401e97:	0f 45 c6             	cmovne %esi,%eax
  401e9a:	89 83 00 02 00 00    	mov    %eax,0x200(%rbx)
}
  401ea0:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  401ea5:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401eae:	75 09                	jne    401eb9 <threadwork+0x219>
  401eb0:	48 83 c4 28          	add    $0x28,%rsp
  401eb4:	31 c0                	xor    %eax,%eax
  401eb6:	5b                   	pop    %rbx
  401eb7:	5d                   	pop    %rbp
  401eb8:	c3                   	ret
  401eb9:	e8 a2 f1 ff ff       	call   401060 <__stack_chk_fail@plt>
  401ebe:	66 90                	xchg   %ax,%ax

0000000000401ec0 <work>:
void * work(void * arg) {
  401ec0:	53                   	push   %rbx
  401ec1:	8b 57 64             	mov    0x64(%rdi),%edx
  401ec4:	48 89 fb             	mov    %rdi,%rbx
  401ec7:	31 c0                	xor    %eax,%eax
  401ec9:	48 8d 35 34 01 00 00 	lea    0x134(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  401ed0:	bf 01 00 00 00       	mov    $0x1,%edi
  401ed5:	e8 b6 f1 ff ff       	call   401090 <__printf_chk@plt>
  while (data->running == 1) {
  401eda:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401ede:	75 0e                	jne    401eee <work+0x2e>
      threadwork(data);
  401ee0:	48 89 df             	mov    %rbx,%rdi
  401ee3:	e8 b8 fd ff ff       	call   401ca0 <threadwork>
  while (data->running == 1) {
  401ee8:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401eec:	74 f2                	je     401ee0 <work+0x20>
  401eee:	8b 53 64             	mov    0x64(%rbx),%edx
  401ef1:	48 8d 35 1f 01 00 00 	lea    0x11f(%rip),%rsi        # 402017 <_IO_stdin_used+0x17>
  401ef8:	bf 01 00 00 00       	mov    $0x1,%edi
  401efd:	31 c0                	xor    %eax,%eax
  401eff:	e8 8c f1 ff ff       	call   401090 <__printf_chk@plt>
}
  401f04:	5b                   	pop    %rbx
  401f05:	c3                   	ret
  401f06:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401f10 <work2>:
  while (data->running == 1) {
  401f10:	eb 0b                	jmp    401f1d <work2+0xd>
  401f12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  401f18:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  401f1d:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  401f21:	74 f5                	je     401f18 <work2+0x8>
}
  401f23:	c3                   	ret

Disassembly of section .fini:

0000000000401f24 <_fini>:
  401f24:	f3 0f 1e fa          	endbr64
  401f28:	48 83 ec 08          	sub    $0x8,%rsp
  401f2c:	48 83 c4 08          	add    $0x8,%rsp
  401f30:	c3                   	ret
