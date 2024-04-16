
bump3-workqueue:     file format elf64-x86-64


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
  4010cc:	48 8d 35 54 1f 00 00 	lea    0x1f54(%rip),%rsi        # 403027 <_IO_stdin_used+0x27>
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
  401102:	48 8d 35 30 1f 00 00 	lea    0x1f30(%rip),%rsi        # 403039 <_IO_stdin_used+0x39>
  401109:	31 c0                	xor    %eax,%eax
  40110b:	bf 01 00 00 00       	mov    $0x1,%edi
  401110:	e8 7b ff ff ff       	call   401090 <__printf_chk@plt>
  401115:	ba 20 00 00 00       	mov    $0x20,%edx
  40111a:	48 8d 35 14 1f 00 00 	lea    0x1f14(%rip),%rsi        # 403035 <_IO_stdin_used+0x35>
  401121:	31 c0                	xor    %eax,%eax
  401123:	bf 01 00 00 00       	mov    $0x1,%edi
  401128:	e8 63 ff ff ff       	call   401090 <__printf_chk@plt>
  40112d:	ba 0e 00 00 00       	mov    $0xe,%edx
  401132:	48 8d 35 0f 1f 00 00 	lea    0x1f0f(%rip),%rsi        # 403048 <_IO_stdin_used+0x48>
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
  401194:	48 8d 35 c2 1e 00 00 	lea    0x1ec2(%rip),%rsi        # 40305d <_IO_stdin_used+0x5d>
  40119b:	49 89 c4             	mov    %rax,%r12
  40119e:	31 c0                	xor    %eax,%eax
  4011a0:	e8 eb fe ff ff       	call   401090 <__printf_chk@plt>
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4011a5:	be 20 00 00 00       	mov    $0x20,%esi
  4011aa:	bf 64 00 00 00       	mov    $0x64,%edi
  4011af:	e8 cc fe ff ff       	call   401080 <calloc@plt>
  4011b4:	31 d2                	xor    %edx,%edx
  4011b6:	bf 01 00 00 00       	mov    $0x1,%edi
  4011bb:	48 8d 35 ac 1e 00 00 	lea    0x1eac(%rip),%rsi        # 40306e <_IO_stdin_used+0x6e>
  4011c2:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  4011c7:	31 c0                	xor    %eax,%eax
  4011c9:	e8 c2 fe ff ff       	call   401090 <__printf_chk@plt>
  4011ce:	4c 89 f2             	mov    %r14,%rdx
  4011d1:	bf 01 00 00 00       	mov    $0x1,%edi
  4011d6:	31 c0                	xor    %eax,%eax
  4011d8:	48 8d 35 9a 1e 00 00 	lea    0x1e9a(%rip),%rsi        # 403079 <_IO_stdin_used+0x79>
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
  401236:	48 8d 35 4b 1f 00 00 	lea    0x1f4b(%rip),%rsi        # 403188 <_IO_stdin_used+0x188>
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
  40126a:	48 8b 05 67 1f 00 00 	mov    0x1f67(%rip),%rax        # 4031d8 <_IO_stdin_used+0x1d8>
    data[x].bucketstart = x * buckets ;
  401271:	45 89 a6 18 fd ff ff 	mov    %r12d,-0x2e8(%r14)
    data[x].readies[x] = 0;
    data[x].buckets = buckets;
    data[x].main = &data[0];
    data[x].threads = data;
    
    data[x].read = 0;
  401278:	66 0f 6f 15 70 1f 00 00 	movdqa 0x1f70(%rip),%xmm2        # 4031f0 <_IO_stdin_used+0x1f0>
    data[x].newmask = 0;
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401280:	be 30 00 00 00       	mov    $0x30,%esi
    data[x].chunkslen = chunkslen;
  401285:	66 0f 6f 1d 73 1f 00 00 	movdqa 0x1f73(%rip),%xmm3        # 403200 <_IO_stdin_used+0x200>
    data[x].loglevel = debug;
  40128d:	41 c7 86 00 fd ff ff 00 00 00 00 	movl   $0x0,-0x300(%r14)
    data[x].running = 1;
  401298:	49 89 86 dc fc ff ff 	mov    %rax,-0x324(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40129f:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].buckets = buckets;
  4012a4:	48 8b 05 35 1f 00 00 	mov    0x1f35(%rip),%rax        # 4031e0 <_IO_stdin_used+0x1e0>
  for (int x = 0; x < threadsize ; x++) {
  4012ab:	41 81 c4 92 24 49 12 	add    $0x12492492,%r12d
    data[x].prevread = threadsize;
  4012b2:	66 0f 6f 25 56 1f 00 00 	movdqa 0x1f56(%rip),%xmm4        # 403210 <_IO_stdin_used+0x210>
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
  401373:	49 c7 c5 70 20 40 00 	mov    $0x402070,%r13
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
  4013d5:	66 0f 6f 05 43 1e 00 00 	movdqa 0x1e43(%rip),%xmm0        # 403220 <_IO_stdin_used+0x220>
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
  4014a5:	48 8d 3d d9 1b 00 00 	lea    0x1bd9(%rip),%rdi        # 403085 <_IO_stdin_used+0x85>
  4014ac:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  4014b0:	45 31 e4             	xor    %r12d,%r12d
  4014b3:	e8 88 fb ff ff       	call   401040 <puts@plt>
  long sends = data->threadsize;
  4014b8:	4c 63 73 68          	movslq 0x68(%rbx),%r14
  for (int x = 0; x < threadsize; x++) {
  4014bc:	4c 8d bb 48 31 00 00 	lea    0x3148(%rbx),%r15
  4014c3:	4c 8d 2d d0 1b 00 00 	lea    0x1bd0(%rip),%r13        # 40309a <_IO_stdin_used+0x9a>
  4014ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
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
  4014f1:	4c 39 fd             	cmp    %r15,%rbp
  4014f4:	75 da                	jne    4014d0 <main+0x410>
  }
  printf("freq: %ld\n", freq/ seconds);
  4014f6:	4c 89 e0             	mov    %r12,%rax
  4014f9:	48 8d 35 a5 1b 00 00 	lea    0x1ba5(%rip),%rsi        # 4030a5 <_IO_stdin_used+0xa5>
  401500:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
  40150a:	bf 01 00 00 00       	mov    $0x1,%edi
  40150f:	48 f7 ed             	imul   %rbp
  401512:	4c 89 e0             	mov    %r12,%rax
  401515:	4c 8d bb 50 31 00 00 	lea    0x3150(%rbx),%r15
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  40151c:	4d 0f af e6          	imul   %r14,%r12
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
  40153b:	48 8d 35 6e 1b 00 00 	lea    0x1b6e(%rip),%rsi        # 4030b0 <_IO_stdin_used+0xb0>
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
  40156b:	48 8d 35 4c 1b 00 00 	lea    0x1b4c(%rip),%rsi        # 4030be <_IO_stdin_used+0xbe>
  401572:	48 99                	cqto
  401574:	49 f7 fd             	idiv   %r13
  401577:	49 89 c5             	mov    %rax,%r13
  40157a:	48 89 c2             	mov    %rax,%rdx
  40157d:	31 c0                	xor    %eax,%eax
  40157f:	e8 0c fb ff ff       	call   401090 <__printf_chk@plt>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  401584:	4c 89 e8             	mov    %r13,%rax
  401587:	bf 01 00 00 00       	mov    $0x1,%edi
  40158c:	48 8d 35 3f 1b 00 00 	lea    0x1b3f(%rip),%rsi        # 4030d2 <_IO_stdin_used+0xd2>
  401593:	48 99                	cqto
  401595:	4c 8d 2d 67 1b 00 00 	lea    0x1b67(%rip),%r13        # 403103 <_IO_stdin_used+0x103>
  40159c:	49 f7 fe             	idiv   %r14
  40159f:	48 89 c2             	mov    %rax,%rdx
  4015a2:	31 c0                	xor    %eax,%eax
  4015a4:	e8 e7 fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  4015a9:	4c 89 e0             	mov    %r12,%rax
  4015ac:	bf 01 00 00 00       	mov    $0x1,%edi
  long freq_writes = 0;
  4015b1:	45 31 e4             	xor    %r12d,%r12d
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  4015b4:	48 99                	cqto
  4015b6:	48 8d 35 33 1b 00 00 	lea    0x1b33(%rip),%rsi        # 4030f0 <_IO_stdin_used+0xf0>
  4015bd:	48 f7 fd             	idiv   %rbp
  4015c0:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  4015c4:	48 89 c2             	mov    %rax,%rdx
  4015c7:	31 c0                	xor    %eax,%eax
  4015c9:	e8 c2 fa ff ff       	call   401090 <__printf_chk@plt>
  
  for (int x = 0; x < threadsize; x++) {
  4015ce:	66 90                	xchg   %ax,%ax
    freq_writes += data[x].freq_writes;
  4015d0:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4015d4:	4c 89 ee             	mov    %r13,%rsi
  4015d7:	bf 01 00 00 00       	mov    $0x1,%edi
  4015dc:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  4015de:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
    freq_writes += data[x].freq_writes;
  4015e5:	49 01 d4             	add    %rdx,%r12
  4015e8:	e8 a3 fa ff ff       	call   401090 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  4015ed:	4c 39 fd             	cmp    %r15,%rbp
  4015f0:	75 de                	jne    4015d0 <main+0x510>
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  4015f2:	4c 89 e0             	mov    %r12,%rax
  4015f5:	48 8d 35 13 1b 00 00 	lea    0x1b13(%rip),%rsi        # 40310f <_IO_stdin_used+0x10f>
  4015fc:	bf 01 00 00 00       	mov    $0x1,%edi
  401601:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
  40160b:	48 f7 ed             	imul   %rbp
  40160e:	4c 89 e0             	mov    %r12,%rax

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  401611:	4d 0f af e6          	imul   %r14,%r12
  printf("freq_writes: %ld\n", freq_writes / seconds);
  401615:	48 c1 f8 3f          	sar    $0x3f,%rax
  401619:	48 d1 fa             	sar    %rdx
  40161c:	48 29 c2             	sub    %rax,%rdx
  40161f:	31 c0                	xor    %eax,%eax
  401621:	49 89 d5             	mov    %rdx,%r13
  401624:	e8 67 fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  401629:	4c 89 e0             	mov    %r12,%rax
  40162c:	49 c1 fc 3f          	sar    $0x3f,%r12
  401630:	48 8d 35 ea 1a 00 00 	lea    0x1aea(%rip),%rsi        # 403121 <_IO_stdin_used+0x121>
  401637:	48 f7 ed             	imul   %rbp
  40163a:	bf 01 00 00 00       	mov    $0x1,%edi
  40163f:	31 c0                	xor    %eax,%eax
  401641:	48 89 d5             	mov    %rdx,%rbp
  401644:	48 d1 fd             	sar    %rbp
  401647:	4c 29 e5             	sub    %r12,%rbp
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  40164a:	41 bc 00 ca 9a 3b    	mov    $0x3b9aca00,%r12d
  401650:	48 89 ea             	mov    %rbp,%rdx
  401653:	e8 38 fa ff ff       	call   401090 <__printf_chk@plt>
  401658:	4c 89 e0             	mov    %r12,%rax
  40165b:	bf 01 00 00 00       	mov    $0x1,%edi
  401660:	48 8d 35 d2 1a 00 00 	lea    0x1ad2(%rip),%rsi        # 403139 <_IO_stdin_used+0x139>
  401667:	48 99                	cqto
  401669:	49 f7 fd             	idiv   %r13
  40166c:	48 89 c2             	mov    %rax,%rdx
  40166f:	49 89 c5             	mov    %rax,%r13
  401672:	31 c0                	xor    %eax,%eax
  401674:	e8 17 fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes per thread latency: %ld\n", (1000000000/(freq_writes / seconds)) / sends);
  401679:	4c 89 e8             	mov    %r13,%rax
  40167c:	bf 01 00 00 00       	mov    $0x1,%edi
  401681:	48 8d 35 20 1b 00 00 	lea    0x1b20(%rip),%rsi        # 4031a8 <_IO_stdin_used+0x1a8>
  401688:	48 99                	cqto
  40168a:	49 f7 fe             	idiv   %r14
  40168d:	48 89 c2             	mov    %rax,%rdx
  401690:	31 c0                	xor    %eax,%eax
  401692:	e8 f9 f9 ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * sends) / seconds));
  401697:	4c 89 e0             	mov    %r12,%rax
  40169a:	bf 01 00 00 00       	mov    $0x1,%edi
  40169f:	48 8d 35 ae 1a 00 00 	lea    0x1aae(%rip),%rsi        # 403154 <_IO_stdin_used+0x154>
  4016a6:	48 99                	cqto
  4016a8:	48 f7 fd             	idiv   %rbp
  4016ab:	48 8d 2d 1b 1a 00 00 	lea    0x1a1b(%rip),%rbp        # 4030cd <_IO_stdin_used+0xcd>
  4016b2:	48 89 c2             	mov    %rax,%rdx
  4016b5:	31 c0                	xor    %eax,%eax
  4016b7:	e8 d4 f9 ff ff       	call   401090 <__printf_chk@plt>
  4016bc:	48 8d 3d ab 1a 00 00 	lea    0x1aab(%rip),%rdi        # 40316e <_IO_stdin_used+0x16e>
  4016c3:	e8 78 f9 ff ff       	call   401040 <puts@plt>
  4016c8:	48 89 ee             	mov    %rbp,%rsi
  4016cb:	bf 01 00 00 00       	mov    $0x1,%edi
  4016d0:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  4016d2:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  4016d9:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4016e0:	e8 ab f9 ff ff       	call   401090 <__printf_chk@plt>
  4016e5:	48 89 ee             	mov    %rbp,%rsi
  4016e8:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ed:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  4016ef:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  4016f6:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4016fd:	e8 8e f9 ff ff       	call   401090 <__printf_chk@plt>
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  401702:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  401709:	48 89 ee             	mov    %rbp,%rsi
  40170c:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401713:	bf 01 00 00 00       	mov    $0x1,%edi
  401718:	31 c0                	xor    %eax,%eax
  40171a:	e8 71 f9 ff ff       	call   401090 <__printf_chk@plt>
  40171f:	48 89 ee             	mov    %rbp,%rsi
  401722:	bf 01 00 00 00       	mov    $0x1,%edi
  401727:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  401729:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  401730:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  401737:	e8 54 f9 ff ff       	call   401090 <__printf_chk@plt>
  40173c:	48 89 ee             	mov    %rbp,%rsi
  40173f:	bf 01 00 00 00       	mov    $0x1,%edi
  401744:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  401746:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  40174d:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  401754:	e8 37 f9 ff ff       	call   401090 <__printf_chk@plt>
  401759:	48 89 ee             	mov    %rbp,%rsi
  40175c:	bf 01 00 00 00       	mov    $0x1,%edi
  401761:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  401763:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  40176a:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401771:	e8 1a f9 ff ff       	call   401090 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  401776:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  40177d:	31 c0                	xor    %eax,%eax
  40177f:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  401786:	48 8d 35 ee 19 00 00 	lea    0x19ee(%rip),%rsi        # 40317b <_IO_stdin_used+0x17b>
  40178d:	bf 01 00 00 00       	mov    $0x1,%edi
  401792:	e8 f9 f8 ff ff       	call   401090 <__printf_chk@plt>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  401797:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  40179c:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4017a5:	75 11                	jne    4017b8 <main+0x6f8>
  4017a7:	48 83 c4 78          	add    $0x78,%rsp
  4017ab:	31 c0                	xor    %eax,%eax
  4017ad:	5b                   	pop    %rbx
  4017ae:	5d                   	pop    %rbp
  4017af:	41 5c                	pop    %r12
  4017b1:	41 5d                	pop    %r13
  4017b3:	41 5e                	pop    %r14
  4017b5:	41 5f                	pop    %r15
  4017b7:	c3                   	ret
  4017b8:	e8 a3 f8 ff ff       	call   401060 <__stack_chk_fail@plt>
  4017bd:	0f 1f 00             	nopl   (%rax)

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
  4017df:	ff 15 0b 38 00 00    	call   *0x380b(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  4017e5:	f4                   	hlt
  4017e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004017f0 <_dl_relocate_static_pie>:
  4017f0:	f3 0f 1e fa          	endbr64
  4017f4:	c3                   	ret
  4017f5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4017ff:	90                   	nop

0000000000401800 <deregister_tm_clones>:
  401800:	b8 10 50 40 00       	mov    $0x405010,%eax
  401805:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  40180b:	74 13                	je     401820 <deregister_tm_clones+0x20>
  40180d:	b8 00 00 00 00       	mov    $0x0,%eax
  401812:	48 85 c0             	test   %rax,%rax
  401815:	74 09                	je     401820 <deregister_tm_clones+0x20>
  401817:	bf 10 50 40 00       	mov    $0x405010,%edi
  40181c:	ff e0                	jmp    *%rax
  40181e:	66 90                	xchg   %ax,%ax
  401820:	c3                   	ret
  401821:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40182c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401830 <register_tm_clones>:
  401830:	be 10 50 40 00       	mov    $0x405010,%esi
  401835:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  40183c:	48 89 f0             	mov    %rsi,%rax
  40183f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401843:	48 c1 f8 03          	sar    $0x3,%rax
  401847:	48 01 c6             	add    %rax,%rsi
  40184a:	48 d1 fe             	sar    %rsi
  40184d:	74 11                	je     401860 <register_tm_clones+0x30>
  40184f:	b8 00 00 00 00       	mov    $0x0,%eax
  401854:	48 85 c0             	test   %rax,%rax
  401857:	74 07                	je     401860 <register_tm_clones+0x30>
  401859:	bf 10 50 40 00       	mov    $0x405010,%edi
  40185e:	ff e0                	jmp    *%rax
  401860:	c3                   	ret
  401861:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40186c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401870 <__do_global_dtors_aux>:
  401870:	f3 0f 1e fa          	endbr64
  401874:	80 3d 95 37 00 00 00 	cmpb   $0x0,0x3795(%rip)        # 405010 <__TMC_END__>
  40187b:	75 13                	jne    401890 <__do_global_dtors_aux+0x20>
  40187d:	55                   	push   %rbp
  40187e:	48 89 e5             	mov    %rsp,%rbp
  401881:	e8 7a ff ff ff       	call   401800 <deregister_tm_clones>
  401886:	c6 05 83 37 00 00 01 	movb   $0x1,0x3783(%rip)        # 405010 <__TMC_END__>
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
  if (data->writecursor != 0 && (data->writecursor % (data->threadsize - 1)) == 0) {
  4019d0:	8b 87 80 01 00 00    	mov    0x180(%rdi),%eax
  4019d6:	85 c0                	test   %eax,%eax
  4019d8:	74 17                	je     4019f1 <singlewriter3+0x21>
  4019da:	8b 77 68             	mov    0x68(%rdi),%esi
  4019dd:	99                   	cltd
  4019de:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  4019e1:	f7 f9                	idiv   %ecx
  4019e3:	85 d2                	test   %edx,%edx
  4019e5:	75 0a                	jne    4019f1 <singlewriter3+0x21>
    data->writecursor = 0;
  4019e7:	c7 87 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rdi)
}
  4019f1:	c3                   	ret
  4019f2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4019fd:	0f 1f 00             	nopl   (%rax)

0000000000401a00 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401a00:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  401a06:	85 c0                	test   %eax,%eax
  401a08:	74 1e                	je     401a28 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a0a:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401a0c:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a0d:	55                   	push   %rbp
  401a0e:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401a0f:	8b 77 68             	mov    0x68(%rdi),%esi
  401a12:	48 89 fb             	mov    %rdi,%rbx
  401a15:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401a18:	f7 f9                	idiv   %ecx
  401a1a:	85 d2                	test   %edx,%edx
  401a1c:	74 12                	je     401a30 <singlewriter2+0x30>
}
  401a1e:	5b                   	pop    %rbx
  401a1f:	5d                   	pop    %rbp
  401a20:	41 5c                	pop    %r12
  401a22:	c3                   	ret
  401a23:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401a28:	c3                   	ret
  401a29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    data->readcursor = 0;
  401a30:	c7 87 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdi)
        struct Data * thread = &data->threads[data->threadindex];
  401a3a:	48 63 47 64          	movslq 0x64(%rdi),%rax
  401a3e:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  401a46:	48 29 c5             	sub    %rax,%rbp
  401a49:	48 c1 e5 07          	shl    $0x7,%rbp
  401a4d:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401a51:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401a56:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401a5d:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401a61:	49 c1 e4 04          	shl    $0x4,%r12
  401a65:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401a6c:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401a71:	e8 da f5 ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401a76:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401a7c:	83 c0 01             	add    $0x1,%eax
  401a7f:	99                   	cltd
  401a80:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  401a86:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401a89:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401a8f:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401a93:	48 8b 05 36 17 00 00 	mov    0x1736(%rip),%rax        # 4031d0 <_IO_stdin_used+0x1d0>
  401a9a:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  401a9f:	5b                   	pop    %rbx
  401aa0:	5d                   	pop    %rbp
  401aa1:	41 5c                	pop    %r12
  401aa3:	c3                   	ret
  401aa4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401aaf:	90                   	nop

0000000000401ab0 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401ab0:	41 55                	push   %r13
  401ab2:	49 89 d5             	mov    %rdx,%r13
  401ab5:	41 54                	push   %r12
  401ab7:	49 89 cc             	mov    %rcx,%r12
  401aba:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401abb:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401abe:	48 89 fd             	mov    %rdi,%rbp
  401ac1:	53                   	push   %rbx
  401ac2:	48 89 f3             	mov    %rsi,%rbx
  401ac5:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401ac9:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401acd:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401ad6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401adb:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401add:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401ae5:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  401aeb:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401af3:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401afb:	83 c0 01             	add    $0x1,%eax
  401afe:	99                   	cltd
  401aff:	f7 7f 68             	idivl  0x68(%rdi)
  401b02:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401b08:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401b0d:	4c 89 e9             	mov    %r13,%rcx
  401b10:	e8 2b fe ff ff       	call   401940 <findavailable>
  if (fill == 1) {
  401b15:	83 f8 01             	cmp    $0x1,%eax
  401b18:	0f 84 64 01 00 00    	je     401c82 <singlewriter+0x1d2>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401b1e:	48 89 ef             	mov    %rbp,%rdi
  401b21:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401b26:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401b2b:	4c 89 e2             	mov    %r12,%rdx
  401b2e:	4c 89 ee             	mov    %r13,%rsi
  401b31:	e8 7a fd ff ff       	call   4018b0 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401b36:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401b3b:	85 ff                	test   %edi,%edi
  401b3d:	0f 8e 66 01 00 00    	jle    401ca9 <singlewriter+0x1f9>
  401b43:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401b48:	31 c9                	xor    %ecx,%ecx
  401b4a:	eb 62                	jmp    401bae <singlewriter+0xfe>
  401b4c:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b50:	48 8b 14 cb          	mov    (%rbx,%rcx,8),%rdx
          int thread = readyreaders[x];
  401b54:	4d 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%r10
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b59:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401b5c:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b60:	48 c1 e2 05          	shl    $0x5,%rdx
  401b64:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].reading = chunk;
  401b6b:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
          data->threads[thread].start = start;
  401b73:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401b77:	66 0f 6e 4a 08       	movd   0x8(%rdx),%xmm1
          data->threads[thread].reading = chunk;
  401b7c:	4c 29 d0             	sub    %r10,%rax
          chunk->available = READING;
  401b7f:	c7 42 10 02 00 00 00 	movl   $0x2,0x10(%rdx)
          data->threads[thread].reading = chunk;
  401b86:	48 c1 e0 07          	shl    $0x7,%rax
  401b8a:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].start = start;
  401b8e:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401b92:	48 89 90 a8 00 00 00 	mov    %rdx,0xa8(%rax)
          chunk->owner = thread;
  401b99:	44 89 52 14          	mov    %r10d,0x14(%rdx)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401b9d:	83 88 c8 00 00 00 10 	orl    $0x10,0xc8(%rax)
          data->threads[thread].start = start;
  401ba4:	66 0f d6 40 14       	movq   %xmm0,0x14(%rax)
        for (int x = 0; x < readers ; x++) {
  401ba9:	48 39 cf             	cmp    %rcx,%rdi
  401bac:	74 07                	je     401bb5 <singlewriter+0x105>
  401bae:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401bb0:	4c 39 c1             	cmp    %r8,%rcx
  401bb3:	75 9b                	jne    401b50 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401bb5:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401bba:	45 85 c0             	test   %r8d,%r8d
  401bbd:	7e 7a                	jle    401c39 <singlewriter+0x189>
                if (assignedchunk  == availableidx) {
  401bbf:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401bc3:	41 01 f0             	add    %esi,%r8d
  401bc6:	eb 6d                	jmp    401c35 <singlewriter+0x185>
  401bc8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401bd0:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401bd3:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401bd6:	45 8b 0c 24          	mov    (%r12),%r9d
   for (int x = 0; x < writers ; x++) {
  401bda:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401bde:	48 8b 14 f3          	mov    (%rbx,%rsi,8),%rdx
          data->threads[thread].writing = chunk;
  401be2:	49 63 f1             	movslq %r9d,%rsi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401be5:	48 c1 e2 05          	shl    $0x5,%rdx
  401be9:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].writing = chunk;
  401bf0:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
          data->threads[thread].publishstart = start;
  401bf8:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401bfc:	66 0f 6e 52 08       	movd   0x8(%rdx),%xmm2
          data->threads[thread].writing = chunk;
  401c01:	48 29 f0             	sub    %rsi,%rax
      chunk->available = WRITING;
  401c04:	c7 42 10 03 00 00 00 	movl   $0x3,0x10(%rdx)
          data->threads[thread].writing = chunk;
  401c0b:	48 c1 e0 07          	shl    $0x7,%rax
  401c0f:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].publishstart = start;
  401c13:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401c17:	48 89 90 b0 00 00 00 	mov    %rdx,0xb0(%rax)
          chunk->owner = thread;
  401c1e:	44 89 4a 14          	mov    %r9d,0x14(%rdx)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401c22:	83 88 c8 00 00 00 20 	orl    $0x20,0xc8(%rax)
          data->threads[thread].publishstart = start;
  401c29:	66 0f d6 40 40       	movq   %xmm0,0x40(%rax)
   for (int x = 0; x < writers ; x++) {
  401c2e:	44 39 c1             	cmp    %r8d,%ecx
  401c31:	74 06                	je     401c39 <singlewriter+0x189>
  401c33:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401c35:	39 f7                	cmp    %esi,%edi
  401c37:	75 97                	jne    401bd0 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401c39:	8b 7d 68             	mov    0x68(%rbp),%edi
  401c3c:	85 ff                	test   %edi,%edi
  401c3e:	7e 40                	jle    401c80 <singlewriter+0x1d0>
        if (data->threads[x].newmask != 0) {
  401c40:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401c44:	31 d2                	xor    %edx,%edx
  401c46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401c50:	48 63 ca             	movslq %edx,%rcx
  401c53:	48 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rax
  401c5b:	48 29 c8             	sub    %rcx,%rax
  401c5e:	48 c1 e0 07          	shl    $0x7,%rax
  401c62:	4c 01 c0             	add    %r8,%rax
  401c65:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401c6b:	85 f6                	test   %esi,%esi
  401c6d:	74 31                	je     401ca0 <singlewriter+0x1f0>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401c6f:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401c73:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401c76:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401c79:	8b 7d 68             	mov    0x68(%rbp),%edi
  401c7c:	39 fa                	cmp    %edi,%edx
  401c7e:	7c d0                	jl     401c50 <singlewriter+0x1a0>
  return 0;
  401c80:	31 c0                	xor    %eax,%eax
}
  401c82:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401c87:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401c90:	75 1e                	jne    401cb0 <singlewriter+0x200>
  401c92:	48 83 c4 28          	add    $0x28,%rsp
  401c96:	5b                   	pop    %rbx
  401c97:	5d                   	pop    %rbp
  401c98:	41 5c                	pop    %r12
  401c9a:	41 5d                	pop    %r13
  401c9c:	c3                   	ret
  401c9d:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401ca0:	83 c2 01             	add    $0x1,%edx
  401ca3:	39 fa                	cmp    %edi,%edx
  401ca5:	7c a9                	jl     401c50 <singlewriter+0x1a0>
  401ca7:	eb d7                	jmp    401c80 <singlewriter+0x1d0>
      int assignedchunk = 0;
  401ca9:	31 f6                	xor    %esi,%esi
  401cab:	e9 05 ff ff ff       	jmp    401bb5 <singlewriter+0x105>
}
  401cb0:	e8 ab f3 ff ff       	call   401060 <__stack_chk_fail@plt>
  401cb5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401cc0 <threadwork>:
int * threadwork(struct Data * data) {
  401cc0:	41 57                	push   %r15
  401cc2:	41 56                	push   %r14
  401cc4:	41 55                	push   %r13
  401cc6:	41 54                	push   %r12
  401cc8:	55                   	push   %rbp
  401cc9:	53                   	push   %rbx
  401cca:	48 89 fb             	mov    %rdi,%rbx
  401ccd:	48 83 ec 38          	sub    $0x38,%rsp
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401cd1:	48 63 4f 68          	movslq 0x68(%rdi),%rcx
  long currentwrite = data->main->globalwrite;
  401cd5:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401cde:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  401ce3:	48 8b 47 28          	mov    0x28(%rdi),%rax
  long lastcursor = data->main->writecursor;
  401ce7:	8b b0 80 01 00 00    	mov    0x180(%rax),%esi
  long currentwrite = data->main->globalwrite;
  401ced:	48 8b a8 50 03 00 00 	mov    0x350(%rax),%rbp
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401cf4:	48 8b 80 38 03 00 00 	mov    0x338(%rax),%rax
    data->thiswrite = lastcursor;
  401cfb:	89 b7 28 03 00 00    	mov    %esi,0x328(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401d01:	48 8d 74 24 10       	lea    0x10(%rsp),%rsi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401d06:	48 99                	cqto
  401d08:	48 f7 f9             	idiv   %rcx
    data->prevwrite = lastwrite;
  401d0b:	48 89 97 10 03 00 00 	mov    %rdx,0x310(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401d12:	bf 04 00 00 00       	mov    $0x4,%edi
  401d17:	e8 34 f3 ff ff       	call   401050 <clock_gettime@plt>
    for (int n = 0; n < data->threadsize ; n++) {
  401d1c:	4c 63 53 68          	movslq 0x68(%rbx),%r10
   data->freq_writes++;
  401d20:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
    for (int n = 0; n < data->threadsize ; n++) {
  401d25:	45 85 d2             	test   %r10d,%r10d
  401d28:	0f 8e 35 01 00 00    	jle    401e63 <threadwork+0x1a3>
        long buffer = (data->threadindex << 24) | ((data->main->globalwrite / data->threadsize) % 0xff) << 16 | (x << 8) | (data->writecursor % 0xff);
  401d2e:	49 b9 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%r9
  401d38:	8b 4b 64             	mov    0x64(%rbx),%ecx
    for (int n = 0; n < data->threadsize ; n++) {
  401d3b:	31 f6                	xor    %esi,%esi
    int x = (data->threadindex + n) % data->threadsize;
  401d3d:	8d 04 31             	lea    (%rcx,%rsi,1),%eax
  401d40:	99                   	cltd
  401d41:	41 f7 fa             	idiv   %r10d
  401d44:	89 d7                	mov    %edx,%edi
     if (x != data->threadindex) {
  401d46:	39 d1                	cmp    %edx,%ecx
  401d48:	0f 84 09 01 00 00    	je     401e57 <threadwork+0x197>
        long buffer = (data->threadindex << 24) | ((data->main->globalwrite / data->threadsize) % 0xff) << 16 | (x << 8) | (data->writecursor % 0xff);
  401d4e:	4c 8b 43 28          	mov    0x28(%rbx),%r8
        epoch->time = time;
  401d52:	66 0f 6f 44 24 10    	movdqa 0x10(%rsp),%xmm0
        long buffer = (data->threadindex << 24) | ((data->main->globalwrite / data->threadsize) % 0xff) << 16 | (x << 8) | (data->writecursor % 0xff);
  401d58:	49 8b 80 50 03 00 00 	mov    0x350(%r8),%rax
  401d5f:	48 99                	cqto
  401d61:	49 f7 fa             	idiv   %r10
  401d64:	49 89 c2             	mov    %rax,%r10
  401d67:	49 f7 e9             	imul   %r9
  401d6a:	4c 89 d0             	mov    %r10,%rax
  401d6d:	48 c1 f8 3f          	sar    $0x3f,%rax
  401d71:	4c 01 d2             	add    %r10,%rdx
  401d74:	48 c1 fa 07          	sar    $0x7,%rdx
  401d78:	48 29 c2             	sub    %rax,%rdx
  401d7b:	48 89 d0             	mov    %rdx,%rax
  401d7e:	48 c1 e0 08          	shl    $0x8,%rax
  401d82:	48 29 d0             	sub    %rdx,%rax
  401d85:	48 63 93 80 01 00 00 	movslq 0x180(%rbx),%rdx
  401d8c:	49 29 c2             	sub    %rax,%r10
  401d8f:	89 f8                	mov    %edi,%eax
  401d91:	c1 e0 08             	shl    $0x8,%eax
  401d94:	49 c1 e2 10          	shl    $0x10,%r10
  401d98:	48 98                	cltq
  401d9a:	49 09 c2             	or     %rax,%r10
  401d9d:	48 89 d0             	mov    %rdx,%rax
  401da0:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401da7:	41 89 c3             	mov    %eax,%r11d
  401daa:	41 c1 fb 1f          	sar    $0x1f,%r11d
  401dae:	48 c1 ea 20          	shr    $0x20,%rdx
  401db2:	01 c2                	add    %eax,%edx
  401db4:	c1 fa 07             	sar    $0x7,%edx
  401db7:	44 29 da             	sub    %r11d,%edx
  401dba:	41 89 d3             	mov    %edx,%r11d
  401dbd:	41 c1 e3 08          	shl    $0x8,%r11d
  401dc1:	41 29 d3             	sub    %edx,%r11d
  401dc4:	89 ca                	mov    %ecx,%edx
  401dc6:	44 29 d8             	sub    %r11d,%eax
  401dc9:	c1 e2 18             	shl    $0x18,%edx
  401dcc:	09 d0                	or     %edx,%eax
  401dce:	48 98                	cltq
  401dd0:	49 09 c2             	or     %rax,%r10
        struct Data * thread = &data->threads[data->threadindex];
  401dd3:	48 63 c1             	movslq %ecx,%rax
        long buffer = (data->threadindex << 24) | ((data->main->globalwrite / data->threadsize) % 0xff) << 16 | (x << 8) | (data->writecursor % 0xff);
  401dd6:	4d 89 d4             	mov    %r10,%r12
        struct Data * thread = &data->threads[data->threadindex];
  401dd9:	4c 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%r10
  401de1:	49 29 c2             	sub    %rax,%r10
  401de4:	49 c1 e2 07          	shl    $0x7,%r10
  401de8:	4c 03 53 30          	add    0x30(%rbx),%r10
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401dec:	49 63 92 24 03 00 00 	movslq 0x324(%r10),%rdx
  401df3:	48 89 d0             	mov    %rdx,%rax
  401df6:	4c 8d 1c 52          	lea    (%rdx,%rdx,2),%r11
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401dfa:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401dfd:	49 c1 e3 04          	shl    $0x4,%r11
  401e01:	4d 03 9a 18 03 00 00 	add    0x318(%r10),%r11
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e08:	99                   	cltd
        epoch->time = time;
  401e09:	41 0f 11 43 08       	movups %xmm0,0x8(%r11)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e0e:	41 f7 ba 20 03 00 00 	idivl  0x320(%r10)
  data->main->works[buffer] = data->threadindex;
  401e15:	49 8b 40 70          	mov    0x70(%r8),%rax
    for (int n = 0; n < data->threadsize ; n++) {
  401e19:	83 c6 01             	add    $0x1,%esi
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e1c:	41 89 92 24 03 00 00 	mov    %edx,0x324(%r10)
        epoch->thread = data->threadindex;
  401e23:	41 89 0b             	mov    %ecx,(%r11)
  epoch->dest = x;
  401e26:	41 89 7b 28          	mov    %edi,0x28(%r11)
  epoch->buffer = buffer;
  401e2a:	4d 89 63 18          	mov    %r12,0x18(%r11)
  epoch->set = 1;
  401e2e:	41 c7 43 24 01 00 00 00 	movl   $0x1,0x24(%r11)
  data->main->works[buffer] = data->threadindex;
  401e36:	42 88 0c 20          	mov    %cl,(%rax,%r12,1)
    for (int n = 0; n < data->threadsize ; n++) {
  401e3a:	4c 63 53 68          	movslq 0x68(%rbx),%r10
  401e3e:	44 39 d6             	cmp    %r10d,%esi
  401e41:	7d 20                	jge    401e63 <threadwork+0x1a3>
  401e43:	8b 4b 64             	mov    0x64(%rbx),%ecx
    int x = (data->threadindex + n) % data->threadsize;
  401e46:	8d 04 31             	lea    (%rcx,%rsi,1),%eax
  401e49:	99                   	cltd
  401e4a:	41 f7 fa             	idiv   %r10d
  401e4d:	89 d7                	mov    %edx,%edi
     if (x != data->threadindex) {
  401e4f:	39 d1                	cmp    %edx,%ecx
  401e51:	0f 85 f7 fe ff ff    	jne    401d4e <threadwork+0x8e>
    for (int n = 0; n < data->threadsize ; n++) {
  401e57:	83 c6 01             	add    $0x1,%esi
  401e5a:	44 39 d6             	cmp    %r10d,%esi
  401e5d:	0f 8c da fe ff ff    	jl     401d3d <threadwork+0x7d>
  if ((data->main->globalwrite % data->threadsize == 0)) {
  401e63:	48 8b 4b 28          	mov    0x28(%rbx),%rcx
    data->writecursor = (data->writecursor + 1) % 0xff;
  401e67:	8b b3 80 01 00 00    	mov    0x180(%rbx),%esi
  if ((data->main->globalwrite % data->threadsize == 0)) {
  401e6d:	48 8b 81 50 03 00 00 	mov    0x350(%rcx),%rax
  401e74:	48 99                	cqto
  401e76:	49 f7 fa             	idiv   %r10
    data->writecursor = 0;
  401e79:	31 c0                	xor    %eax,%eax
  if ((data->main->globalwrite % data->threadsize == 0)) {
  401e7b:	48 85 d2             	test   %rdx,%rdx
  401e7e:	74 28                	je     401ea8 <threadwork+0x1e8>
    data->writecursor = (data->writecursor + 1) % 0xff;
  401e80:	8d 56 01             	lea    0x1(%rsi),%edx
  401e83:	48 63 c2             	movslq %edx,%rax
  401e86:	89 d6                	mov    %edx,%esi
  401e88:	48 69 c0 81 80 80 80 	imul   $0xffffffff80808081,%rax,%rax
  401e8f:	c1 fe 1f             	sar    $0x1f,%esi
  401e92:	48 c1 e8 20          	shr    $0x20,%rax
  401e96:	01 d0                	add    %edx,%eax
  401e98:	c1 f8 07             	sar    $0x7,%eax
  401e9b:	29 f0                	sub    %esi,%eax
  401e9d:	89 c6                	mov    %eax,%esi
  401e9f:	c1 e6 08             	shl    $0x8,%esi
  401ea2:	29 c6                	sub    %eax,%esi
  401ea4:	89 d0                	mov    %edx,%eax
  401ea6:	29 f0                	sub    %esi,%eax
  401ea8:	89 83 80 01 00 00    	mov    %eax,0x180(%rbx)
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_RELAXED);
  401eae:	f0 48 83 81 50 03 00 00 01 	lock addq $0x1,0x350(%rcx)
  if (data->globalread < currentwrite) {
  401eb7:	4c 8b 8b 48 03 00 00 	mov    0x348(%rbx),%r9
  401ebe:	49 39 e9             	cmp    %rbp,%r9
  401ec1:	0f 8d 81 01 00 00    	jge    402048 <threadwork+0x388>
  long lastread = data->main->totalreads % data->threadsize;
  401ec7:	48 8b 43 28          	mov    0x28(%rbx),%rax
  401ecb:	4c 63 5b 68          	movslq 0x68(%rbx),%r11
  401ecf:	48 8b 80 40 03 00 00 	mov    0x340(%rax),%rax
  401ed6:	4d 89 da             	mov    %r11,%r10
   data->freq++;
  401ed9:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
  long lastread = data->main->totalreads % data->threadsize;
  401ede:	48 99                	cqto
  401ee0:	49 f7 fb             	idiv   %r11
     data->readcursor = (data->readcursor + 1) % 0xf;
  401ee3:	8b 83 00 02 00 00    	mov    0x200(%rbx),%eax
  401ee9:	89 44 24 0c          	mov    %eax,0xc(%rsp)
   data->prevread = lastread;
  401eed:	48 89 93 08 03 00 00 	mov    %rdx,0x308(%rbx)
  for (int y = 0; y < data->threadsize; y++) {
  401ef4:	45 85 db             	test   %r11d,%r11d
  401ef7:	0f 8e 01 01 00 00    	jle    401ffe <threadwork+0x33e>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xff;
  401efd:	31 ed                	xor    %ebp,%ebp
  401eff:	85 c0                	test   %eax,%eax
  401f01:	ba 81 80 80 80       	mov    $0x80808081,%edx
    int x = ((data->threadindex + y) % data->threadsize);
  401f06:	44 8b 63 64          	mov    0x64(%rbx),%r12d
            long past = ((data->globalread / (data->threadsize)) % 0xff);
  401f0a:	49 bf 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%r15
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xff;
  401f14:	0f 49 e8             	cmovns %eax,%ebp
  401f17:	44 89 e7             	mov    %r12d,%edi
  401f1a:	47 8d 34 23          	lea    (%r11,%r12,1),%r14d
  401f1e:	89 e8                	mov    %ebp,%eax
  401f20:	48 0f af c2          	imul   %rdx,%rax
  401f24:	48 c1 e8 27          	shr    $0x27,%rax
  401f28:	89 c2                	mov    %eax,%edx
  401f2a:	c1 e2 08             	shl    $0x8,%edx
  401f2d:	29 c2                	sub    %eax,%edx
  401f2f:	44 89 e0             	mov    %r12d,%eax
  401f32:	c1 e0 08             	shl    $0x8,%eax
  401f35:	29 d5                	sub    %edx,%ebp
  401f37:	09 c5                	or     %eax,%ebp
                struct Data * thread = &data->threads[data->threadindex];
  401f39:	49 63 c4             	movslq %r12d,%rax
  401f3c:	4c 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%r13
  401f44:	48 63 ed             	movslq %ebp,%rbp
  401f47:	49 29 c5             	sub    %rax,%r13
  401f4a:	49 c1 e5 07          	shl    $0x7,%r13
  401f4e:	66 90                	xchg   %ax,%ax
    int x = ((data->threadindex + y) % data->threadsize);
  401f50:	89 f8                	mov    %edi,%eax
  401f52:	99                   	cltd
  401f53:	41 f7 fa             	idiv   %r10d
  401f56:	89 d1                	mov    %edx,%ecx
          if (x != data->threadindex) {
  401f58:	44 39 e2             	cmp    %r12d,%edx
  401f5b:	0f 84 91 00 00 00    	je     401ff2 <threadwork+0x332>
                struct Data * thread = &data->threads[data->threadindex];
  401f61:	4c 8b 43 30          	mov    0x30(%rbx),%r8
            thepoch->time = time; 
  401f65:	66 0f 6f 4c 24 10    	movdqa 0x10(%rsp),%xmm1
                struct Data * thread = &data->threads[data->threadindex];
  401f6b:	4d 01 e8             	add    %r13,%r8
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401f6e:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  401f75:	48 89 d0             	mov    %rdx,%rax
  401f78:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401f7c:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401f7f:	48 c1 e6 04          	shl    $0x4,%rsi
  401f83:	49 03 b0 18 03 00 00 	add    0x318(%r8),%rsi
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401f8a:	99                   	cltd
            thepoch->time = time; 
  401f8b:	0f 11 4e 08          	movups %xmm1,0x8(%rsi)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401f8f:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
            long past = ((data->globalread / (data->threadsize)) % 0xff);
  401f96:	4c 89 c8             	mov    %r9,%rax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401f99:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
            long past = ((data->globalread / (data->threadsize)) % 0xff);
  401fa0:	48 99                	cqto
  401fa2:	49 f7 fb             	idiv   %r11
                thepoch->thread = x;
  401fa5:	89 0e                	mov    %ecx,(%rsi)
          thepoch->set = 1;
  401fa7:	c7 46 24 01 00 00 00 	movl   $0x1,0x24(%rsi)
            long past = ((data->globalread / (data->threadsize)) % 0xff);
  401fae:	49 89 c0             	mov    %rax,%r8
  401fb1:	49 f7 ef             	imul   %r15
  401fb4:	4c 89 c0             	mov    %r8,%rax
  401fb7:	48 c1 f8 3f          	sar    $0x3f,%rax
  401fbb:	4c 01 c2             	add    %r8,%rdx
  401fbe:	48 c1 fa 07          	sar    $0x7,%rdx
  401fc2:	48 29 c2             	sub    %rax,%rdx
  401fc5:	48 89 d0             	mov    %rdx,%rax
  401fc8:	48 c1 e0 08          	shl    $0x8,%rax
  401fcc:	48 29 d0             	sub    %rdx,%rax
  401fcf:	4c 89 c2             	mov    %r8,%rdx
  401fd2:	48 29 c2             	sub    %rax,%rdx
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xff;
  401fd5:	b8 00 00 00 00       	mov    $0x0,%eax
  401fda:	48 0f 48 d0          	cmovs  %rax,%rdx
  401fde:	c1 e1 18             	shl    $0x18,%ecx
  401fe1:	48 63 c9             	movslq %ecx,%rcx
  401fe4:	48 c1 e2 10          	shl    $0x10,%rdx
  401fe8:	48 09 ea             	or     %rbp,%rdx
  401feb:	48 09 ca             	or     %rcx,%rdx
  401fee:	48 89 56 18          	mov    %rdx,0x18(%rsi)
  for (int y = 0; y < data->threadsize; y++) {
  401ff2:	83 c7 01             	add    $0x1,%edi
  401ff5:	44 39 f7             	cmp    %r14d,%edi
  401ff8:	0f 85 52 ff ff ff    	jne    401f50 <threadwork+0x290>
     data->readcursor = (data->readcursor + 1) % 0xf;
  401ffe:	8b 54 24 0c          	mov    0xc(%rsp),%edx
  402002:	83 c2 01             	add    $0x1,%edx
  402005:	48 63 c2             	movslq %edx,%rax
  402008:	89 d1                	mov    %edx,%ecx
  40200a:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402011:	c1 f9 1f             	sar    $0x1f,%ecx
  402014:	48 c1 e8 20          	shr    $0x20,%rax
  402018:	01 d0                	add    %edx,%eax
  40201a:	c1 f8 03             	sar    $0x3,%eax
  40201d:	29 c8                	sub    %ecx,%eax
  40201f:	89 d1                	mov    %edx,%ecx
  402021:	89 c6                	mov    %eax,%esi
  402023:	c1 e6 04             	shl    $0x4,%esi
  402026:	29 c6                	sub    %eax,%esi
  data->globalread++;
  402028:	49 8d 41 01          	lea    0x1(%r9),%rax
  if (data->globalread % (data->threadsize) == 0) {
  40202c:	48 99                	cqto
  data->globalread++;
  40202e:	48 89 83 48 03 00 00 	mov    %rax,0x348(%rbx)
     data->readcursor = (data->readcursor + 1) % 0xf;
  402035:	29 f1                	sub    %esi,%ecx
  if (data->globalread % (data->threadsize) == 0) {
  402037:	49 f7 fb             	idiv   %r11
    data->readcursor = 0;
  40203a:	31 c0                	xor    %eax,%eax
  40203c:	48 85 d2             	test   %rdx,%rdx
  40203f:	0f 45 c1             	cmovne %ecx,%eax
  402042:	89 83 00 02 00 00    	mov    %eax,0x200(%rbx)
}
  402048:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
  40204d:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  402056:	75 11                	jne    402069 <threadwork+0x3a9>
  402058:	48 83 c4 38          	add    $0x38,%rsp
  40205c:	31 c0                	xor    %eax,%eax
  40205e:	5b                   	pop    %rbx
  40205f:	5d                   	pop    %rbp
  402060:	41 5c                	pop    %r12
  402062:	41 5d                	pop    %r13
  402064:	41 5e                	pop    %r14
  402066:	41 5f                	pop    %r15
  402068:	c3                   	ret
  402069:	e8 f2 ef ff ff       	call   401060 <__stack_chk_fail@plt>
  40206e:	66 90                	xchg   %ax,%ax

0000000000402070 <work>:
void * work(void * arg) {
  402070:	53                   	push   %rbx
  402071:	8b 57 64             	mov    0x64(%rdi),%edx
  402074:	48 89 fb             	mov    %rdi,%rbx
  402077:	31 c0                	xor    %eax,%eax
  402079:	48 8d 35 84 0f 00 00 	lea    0xf84(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  402080:	bf 01 00 00 00       	mov    $0x1,%edi
  402085:	e8 06 f0 ff ff       	call   401090 <__printf_chk@plt>
  while (data->running == 1) {
  40208a:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  40208e:	75 0e                	jne    40209e <work+0x2e>
      threadwork(data);
  402090:	48 89 df             	mov    %rbx,%rdi
  402093:	e8 28 fc ff ff       	call   401cc0 <threadwork>
  while (data->running == 1) {
  402098:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  40209c:	74 f2                	je     402090 <work+0x20>
  40209e:	8b 53 64             	mov    0x64(%rbx),%edx
  4020a1:	48 8d 35 6f 0f 00 00 	lea    0xf6f(%rip),%rsi        # 403017 <_IO_stdin_used+0x17>
  4020a8:	bf 01 00 00 00       	mov    $0x1,%edi
  4020ad:	31 c0                	xor    %eax,%eax
  4020af:	e8 dc ef ff ff       	call   401090 <__printf_chk@plt>
}
  4020b4:	5b                   	pop    %rbx
  4020b5:	c3                   	ret
  4020b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004020c0 <work2>:
  while (data->running == 1) {
  4020c0:	eb 0b                	jmp    4020cd <work2+0xd>
  4020c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  4020c8:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  4020cd:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  4020d1:	74 f5                	je     4020c8 <work2+0x8>
}
  4020d3:	c3                   	ret

Disassembly of section .fini:

00000000004020d4 <_fini>:
  4020d4:	f3 0f 1e fa          	endbr64
  4020d8:	48 83 ec 08          	sub    $0x8,%rsp
  4020dc:	48 83 c4 08          	add    $0x8,%rsp
  4020e0:	c3                   	ret
