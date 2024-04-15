
bump2-workqueue:     file format elf64-x86-64


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
  40112d:	ba 0f 00 00 00       	mov    $0xf,%edx
  401132:	48 8d 35 0f 1f 00 00 	lea    0x1f0f(%rip),%rsi        # 403048 <_IO_stdin_used+0x48>
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
  4012ab:	41 81 c4 11 11 11 11 	add    $0x11111111,%r12d
    data[x].prevread = threadsize;
  4012b2:	66 0f 6f 25 56 1f 00 00 	movdqa 0x1f56(%rip),%xmm4        # 403210 <_IO_stdin_used+0x210>
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
  401370:	49 c7 c5 b0 2c 40 00 	mov    $0x402cb0,%r13
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
  4013cd:	66 0f 6f 05 4b 1e 00 00 	movdqa 0x1e4b(%rip),%xmm0        # 403220 <_IO_stdin_used+0x220>
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
  4014a5:	48 8d 3d d9 1b 00 00 	lea    0x1bd9(%rip),%rdi        # 403085 <_IO_stdin_used+0x85>
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
  4014bf:	4c 8d 2d d4 1b 00 00 	lea    0x1bd4(%rip),%r13        # 40309a <_IO_stdin_used+0x9a>
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
  4014f9:	48 8d 35 a5 1b 00 00 	lea    0x1ba5(%rip),%rsi        # 4030a5 <_IO_stdin_used+0xa5>
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
  401584:	4d 85 ed             	test   %r13,%r13
  401587:	49 8d 55 07          	lea    0x7(%r13),%rdx
  40158b:	48 8d 35 40 1b 00 00 	lea    0x1b40(%rip),%rsi        # 4030d2 <_IO_stdin_used+0xd2>
  401592:	49 0f 49 d5          	cmovns %r13,%rdx
  401596:	bf 01 00 00 00       	mov    $0x1,%edi
  40159b:	31 c0                	xor    %eax,%eax
  40159d:	4c 8d 2d 5f 1b 00 00 	lea    0x1b5f(%rip),%r13        # 403103 <_IO_stdin_used+0x103>
  4015a4:	48 c1 fa 03          	sar    $0x3,%rdx
  4015a8:	e8 e3 fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  4015ad:	4c 89 e0             	mov    %r12,%rax
  4015b0:	bf 01 00 00 00       	mov    $0x1,%edi
  long freq_writes = 0;
  4015b5:	45 31 e4             	xor    %r12d,%r12d
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  4015b8:	48 99                	cqto
  4015ba:	48 8d 35 2f 1b 00 00 	lea    0x1b2f(%rip),%rsi        # 4030f0 <_IO_stdin_used+0xf0>
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
  4015fd:	48 8d 35 0b 1b 00 00 	lea    0x1b0b(%rip),%rsi        # 40310f <_IO_stdin_used+0x10f>
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
  401638:	48 8d 35 e2 1a 00 00 	lea    0x1ae2(%rip),%rsi        # 403121 <_IO_stdin_used+0x121>
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
  401668:	48 8d 35 ca 1a 00 00 	lea    0x1aca(%rip),%rsi        # 403139 <_IO_stdin_used+0x139>
  40166f:	48 99                	cqto
  401671:	49 f7 fd             	idiv   %r13
  401674:	49 89 c5             	mov    %rax,%r13
  401677:	48 89 c2             	mov    %rax,%rdx
  40167a:	31 c0                	xor    %eax,%eax
  40167c:	e8 0f fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes per thread latency: %ld\n", (1000000000/(freq_writes / seconds)) / sends);
  401681:	4d 85 ed             	test   %r13,%r13
  401684:	49 8d 55 07          	lea    0x7(%r13),%rdx
  401688:	48 8d 35 19 1b 00 00 	lea    0x1b19(%rip),%rsi        # 4031a8 <_IO_stdin_used+0x1a8>
  40168f:	49 0f 49 d5          	cmovns %r13,%rdx
  401693:	bf 01 00 00 00       	mov    $0x1,%edi
  401698:	31 c0                	xor    %eax,%eax
  40169a:	48 c1 fa 03          	sar    $0x3,%rdx
  40169e:	e8 ed f9 ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * sends) / seconds));
  4016a3:	4c 89 e0             	mov    %r12,%rax
  4016a6:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ab:	48 8d 35 a2 1a 00 00 	lea    0x1aa2(%rip),%rsi        # 403154 <_IO_stdin_used+0x154>
  4016b2:	48 99                	cqto
  4016b4:	48 f7 fd             	idiv   %rbp
  4016b7:	48 8d 2d 0f 1a 00 00 	lea    0x1a0f(%rip),%rbp        # 4030cd <_IO_stdin_used+0xcd>
  4016be:	48 89 c2             	mov    %rax,%rdx
  4016c1:	31 c0                	xor    %eax,%eax
  4016c3:	e8 c8 f9 ff ff       	call   401090 <__printf_chk@plt>
  4016c8:	48 8d 3d 9f 1a 00 00 	lea    0x1a9f(%rip),%rdi        # 40316e <_IO_stdin_used+0x16e>
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
  401792:	48 8d 35 e2 19 00 00 	lea    0x19e2(%rip),%rsi        # 40317b <_IO_stdin_used+0x17b>
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
  4017ef:	ff 15 fb 37 00 00    	call   *0x37fb(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  4017f5:	f4                   	hlt
  4017f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401800 <_dl_relocate_static_pie>:
  401800:	f3 0f 1e fa          	endbr64
  401804:	c3                   	ret
  401805:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40180f:	90                   	nop

0000000000401810 <deregister_tm_clones>:
  401810:	b8 10 50 40 00       	mov    $0x405010,%eax
  401815:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  40181b:	74 13                	je     401830 <deregister_tm_clones+0x20>
  40181d:	b8 00 00 00 00       	mov    $0x0,%eax
  401822:	48 85 c0             	test   %rax,%rax
  401825:	74 09                	je     401830 <deregister_tm_clones+0x20>
  401827:	bf 10 50 40 00       	mov    $0x405010,%edi
  40182c:	ff e0                	jmp    *%rax
  40182e:	66 90                	xchg   %ax,%ax
  401830:	c3                   	ret
  401831:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40183c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401840 <register_tm_clones>:
  401840:	be 10 50 40 00       	mov    $0x405010,%esi
  401845:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  40184c:	48 89 f0             	mov    %rsi,%rax
  40184f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401853:	48 c1 f8 03          	sar    $0x3,%rax
  401857:	48 01 c6             	add    %rax,%rsi
  40185a:	48 d1 fe             	sar    %rsi
  40185d:	74 11                	je     401870 <register_tm_clones+0x30>
  40185f:	b8 00 00 00 00       	mov    $0x0,%eax
  401864:	48 85 c0             	test   %rax,%rax
  401867:	74 07                	je     401870 <register_tm_clones+0x30>
  401869:	bf 10 50 40 00       	mov    $0x405010,%edi
  40186e:	ff e0                	jmp    *%rax
  401870:	c3                   	ret
  401871:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40187c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401880 <__do_global_dtors_aux>:
  401880:	f3 0f 1e fa          	endbr64
  401884:	80 3d 85 37 00 00 00 	cmpb   $0x0,0x3785(%rip)        # 405010 <__TMC_END__>
  40188b:	75 13                	jne    4018a0 <__do_global_dtors_aux+0x20>
  40188d:	55                   	push   %rbp
  40188e:	48 89 e5             	mov    %rsp,%rbp
  401891:	e8 7a ff ff ff       	call   401810 <deregister_tm_clones>
  401896:	c6 05 73 37 00 00 01 	movb   $0x1,0x3773(%rip)        # 405010 <__TMC_END__>
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
  if (data->writecursor != 0 && (data->writecursor % (data->threadsize - 1)) == 0) {
  4019e0:	8b 87 80 01 00 00    	mov    0x180(%rdi),%eax
  4019e6:	85 c0                	test   %eax,%eax
  4019e8:	74 17                	je     401a01 <singlewriter3+0x21>
  4019ea:	8b 77 68             	mov    0x68(%rdi),%esi
  4019ed:	99                   	cltd
  4019ee:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  4019f1:	f7 f9                	idiv   %ecx
  4019f3:	85 d2                	test   %edx,%edx
  4019f5:	75 0a                	jne    401a01 <singlewriter3+0x21>
    data->writecursor = 0;
  4019f7:	c7 87 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rdi)
}
  401a01:	c3                   	ret
  401a02:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401a0d:	0f 1f 00             	nopl   (%rax)

0000000000401a10 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401a10:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  401a16:	85 c0                	test   %eax,%eax
  401a18:	74 1e                	je     401a38 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a1a:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401a1c:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a1d:	55                   	push   %rbp
  401a1e:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401a1f:	8b 77 68             	mov    0x68(%rdi),%esi
  401a22:	48 89 fb             	mov    %rdi,%rbx
  401a25:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401a28:	f7 f9                	idiv   %ecx
  401a2a:	85 d2                	test   %edx,%edx
  401a2c:	74 12                	je     401a40 <singlewriter2+0x30>
}
  401a2e:	5b                   	pop    %rbx
  401a2f:	5d                   	pop    %rbp
  401a30:	41 5c                	pop    %r12
  401a32:	c3                   	ret
  401a33:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401a38:	c3                   	ret
  401a39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    data->readcursor = 0;
  401a40:	c7 87 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdi)
        struct Data * thread = &data->threads[data->threadindex];
  401a4a:	48 63 47 64          	movslq 0x64(%rdi),%rax
  401a4e:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  401a56:	48 29 c5             	sub    %rax,%rbp
  401a59:	48 c1 e5 07          	shl    $0x7,%rbp
  401a5d:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401a61:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401a66:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401a6d:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401a71:	49 c1 e4 04          	shl    $0x4,%r12
  401a75:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401a7c:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401a81:	e8 ca f5 ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401a86:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401a8c:	83 c0 01             	add    $0x1,%eax
  401a8f:	99                   	cltd
  401a90:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  401a96:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401a99:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401a9f:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401aa3:	48 8b 05 26 17 00 00 	mov    0x1726(%rip),%rax        # 4031d0 <_IO_stdin_used+0x1d0>
  401aaa:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  401aaf:	5b                   	pop    %rbx
  401ab0:	5d                   	pop    %rbp
  401ab1:	41 5c                	pop    %r12
  401ab3:	c3                   	ret
  401ab4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401abf:	90                   	nop

0000000000401ac0 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401ac0:	41 55                	push   %r13
  401ac2:	49 89 d5             	mov    %rdx,%r13
  401ac5:	41 54                	push   %r12
  401ac7:	49 89 cc             	mov    %rcx,%r12
  401aca:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401acb:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401ace:	48 89 fd             	mov    %rdi,%rbp
  401ad1:	53                   	push   %rbx
  401ad2:	48 89 f3             	mov    %rsi,%rbx
  401ad5:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401ad9:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401add:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401ae6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401aeb:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401aed:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401af5:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  401afb:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401b03:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401b0b:	83 c0 01             	add    $0x1,%eax
  401b0e:	99                   	cltd
  401b0f:	f7 7f 68             	idivl  0x68(%rdi)
  401b12:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401b18:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401b1d:	4c 89 e9             	mov    %r13,%rcx
  401b20:	e8 2b fe ff ff       	call   401950 <findavailable>
  if (fill == 1) {
  401b25:	83 f8 01             	cmp    $0x1,%eax
  401b28:	0f 84 64 01 00 00    	je     401c92 <singlewriter+0x1d2>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401b2e:	48 89 ef             	mov    %rbp,%rdi
  401b31:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401b36:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401b3b:	4c 89 e2             	mov    %r12,%rdx
  401b3e:	4c 89 ee             	mov    %r13,%rsi
  401b41:	e8 7a fd ff ff       	call   4018c0 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401b46:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401b4b:	85 ff                	test   %edi,%edi
  401b4d:	0f 8e 66 01 00 00    	jle    401cb9 <singlewriter+0x1f9>
  401b53:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401b58:	31 c9                	xor    %ecx,%ecx
  401b5a:	eb 62                	jmp    401bbe <singlewriter+0xfe>
  401b5c:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b60:	48 8b 14 cb          	mov    (%rbx,%rcx,8),%rdx
          int thread = readyreaders[x];
  401b64:	4d 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%r10
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b69:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401b6c:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b70:	48 c1 e2 05          	shl    $0x5,%rdx
  401b74:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].reading = chunk;
  401b7b:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
          data->threads[thread].start = start;
  401b83:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401b87:	66 0f 6e 4a 08       	movd   0x8(%rdx),%xmm1
          data->threads[thread].reading = chunk;
  401b8c:	4c 29 d0             	sub    %r10,%rax
          chunk->available = READING;
  401b8f:	c7 42 10 02 00 00 00 	movl   $0x2,0x10(%rdx)
          data->threads[thread].reading = chunk;
  401b96:	48 c1 e0 07          	shl    $0x7,%rax
  401b9a:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].start = start;
  401b9e:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401ba2:	48 89 90 a8 00 00 00 	mov    %rdx,0xa8(%rax)
          chunk->owner = thread;
  401ba9:	44 89 52 14          	mov    %r10d,0x14(%rdx)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401bad:	83 88 c8 00 00 00 10 	orl    $0x10,0xc8(%rax)
          data->threads[thread].start = start;
  401bb4:	66 0f d6 40 14       	movq   %xmm0,0x14(%rax)
        for (int x = 0; x < readers ; x++) {
  401bb9:	48 39 cf             	cmp    %rcx,%rdi
  401bbc:	74 07                	je     401bc5 <singlewriter+0x105>
  401bbe:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401bc0:	4c 39 c1             	cmp    %r8,%rcx
  401bc3:	75 9b                	jne    401b60 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401bc5:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401bca:	45 85 c0             	test   %r8d,%r8d
  401bcd:	7e 7a                	jle    401c49 <singlewriter+0x189>
                if (assignedchunk  == availableidx) {
  401bcf:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401bd3:	41 01 f0             	add    %esi,%r8d
  401bd6:	eb 6d                	jmp    401c45 <singlewriter+0x185>
  401bd8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401be0:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401be3:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401be6:	45 8b 0c 24          	mov    (%r12),%r9d
   for (int x = 0; x < writers ; x++) {
  401bea:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401bee:	48 8b 14 f3          	mov    (%rbx,%rsi,8),%rdx
          data->threads[thread].writing = chunk;
  401bf2:	49 63 f1             	movslq %r9d,%rsi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401bf5:	48 c1 e2 05          	shl    $0x5,%rdx
  401bf9:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].writing = chunk;
  401c00:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
          data->threads[thread].publishstart = start;
  401c08:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401c0c:	66 0f 6e 52 08       	movd   0x8(%rdx),%xmm2
          data->threads[thread].writing = chunk;
  401c11:	48 29 f0             	sub    %rsi,%rax
      chunk->available = WRITING;
  401c14:	c7 42 10 03 00 00 00 	movl   $0x3,0x10(%rdx)
          data->threads[thread].writing = chunk;
  401c1b:	48 c1 e0 07          	shl    $0x7,%rax
  401c1f:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].publishstart = start;
  401c23:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401c27:	48 89 90 b0 00 00 00 	mov    %rdx,0xb0(%rax)
          chunk->owner = thread;
  401c2e:	44 89 4a 14          	mov    %r9d,0x14(%rdx)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401c32:	83 88 c8 00 00 00 20 	orl    $0x20,0xc8(%rax)
          data->threads[thread].publishstart = start;
  401c39:	66 0f d6 40 40       	movq   %xmm0,0x40(%rax)
   for (int x = 0; x < writers ; x++) {
  401c3e:	44 39 c1             	cmp    %r8d,%ecx
  401c41:	74 06                	je     401c49 <singlewriter+0x189>
  401c43:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401c45:	39 f7                	cmp    %esi,%edi
  401c47:	75 97                	jne    401be0 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401c49:	8b 7d 68             	mov    0x68(%rbp),%edi
  401c4c:	85 ff                	test   %edi,%edi
  401c4e:	7e 40                	jle    401c90 <singlewriter+0x1d0>
        if (data->threads[x].newmask != 0) {
  401c50:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401c54:	31 d2                	xor    %edx,%edx
  401c56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401c60:	48 63 ca             	movslq %edx,%rcx
  401c63:	48 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rax
  401c6b:	48 29 c8             	sub    %rcx,%rax
  401c6e:	48 c1 e0 07          	shl    $0x7,%rax
  401c72:	4c 01 c0             	add    %r8,%rax
  401c75:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401c7b:	85 f6                	test   %esi,%esi
  401c7d:	74 31                	je     401cb0 <singlewriter+0x1f0>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401c7f:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401c83:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401c86:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401c89:	8b 7d 68             	mov    0x68(%rbp),%edi
  401c8c:	39 fa                	cmp    %edi,%edx
  401c8e:	7c d0                	jl     401c60 <singlewriter+0x1a0>
  return 0;
  401c90:	31 c0                	xor    %eax,%eax
}
  401c92:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401c97:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401ca0:	75 1e                	jne    401cc0 <singlewriter+0x200>
  401ca2:	48 83 c4 28          	add    $0x28,%rsp
  401ca6:	5b                   	pop    %rbx
  401ca7:	5d                   	pop    %rbp
  401ca8:	41 5c                	pop    %r12
  401caa:	41 5d                	pop    %r13
  401cac:	c3                   	ret
  401cad:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401cb0:	83 c2 01             	add    $0x1,%edx
  401cb3:	39 fa                	cmp    %edi,%edx
  401cb5:	7c a9                	jl     401c60 <singlewriter+0x1a0>
  401cb7:	eb d7                	jmp    401c90 <singlewriter+0x1d0>
      int assignedchunk = 0;
  401cb9:	31 f6                	xor    %esi,%esi
  401cbb:	e9 05 ff ff ff       	jmp    401bc5 <singlewriter+0x105>
}
  401cc0:	e8 9b f3 ff ff       	call   401060 <__stack_chk_fail@plt>
  401cc5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401cd0 <threadwork>:
int * threadwork(struct Data * data) {
  401cd0:	55                   	push   %rbp
  401cd1:	53                   	push   %rbx
  401cd2:	48 89 fb             	mov    %rdi,%rbx
  401cd5:	48 83 ec 28          	sub    $0x28,%rsp
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401cd9:	48 63 4f 68          	movslq 0x68(%rdi),%rcx
  401cdd:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401ce6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401ceb:	48 8b 47 28          	mov    0x28(%rdi),%rax
  long lastcursor = data->main->writecursor;
  401cef:	8b b0 80 01 00 00    	mov    0x180(%rax),%esi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401cf5:	48 8b 80 38 03 00 00 	mov    0x338(%rax),%rax
  401cfc:	48 99                	cqto
    data->thiswrite = lastcursor;
  401cfe:	89 b7 28 03 00 00    	mov    %esi,0x328(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401d04:	48 89 e6             	mov    %rsp,%rsi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401d07:	48 f7 f9             	idiv   %rcx
    data->prevwrite = lastwrite;
  401d0a:	48 89 97 10 03 00 00 	mov    %rdx,0x310(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401d11:	bf 04 00 00 00       	mov    $0x4,%edi
  401d16:	e8 35 f3 ff ff       	call   401050 <clock_gettime@plt>
    int x = 2 + (data->threadindex + n) % data->threadsize - 2;
  401d1b:	8b 4b 64             	mov    0x64(%rbx),%ecx
   data->freq_writes++;
  401d1e:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
    int x = 2 + (data->threadindex + n) % data->threadsize - 2;
  401d23:	89 c8                	mov    %ecx,%eax
  401d25:	99                   	cltd
  401d26:	f7 7b 68             	idivl  0x68(%rbx)
     if (x != data->threadindex) {
  401d29:	39 d1                	cmp    %edx,%ecx
  401d2b:	0f 84 eb 00 00 00    	je     401e1c <threadwork+0x14c>
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401d31:	48 63 83 80 01 00 00 	movslq 0x180(%rbx),%rax
  401d38:	89 d6                	mov    %edx,%esi
  401d3a:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
        epoch->time = time;
  401d3e:	66 0f 6f 04 24       	movdqa (%rsp),%xmm0
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401d43:	48 89 c2             	mov    %rax,%rdx
  401d46:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401d4d:	41 89 d0             	mov    %edx,%r8d
  401d50:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401d54:	48 c1 e8 20          	shr    $0x20,%rax
  401d58:	01 d0                	add    %edx,%eax
  401d5a:	c1 f8 03             	sar    $0x3,%eax
  401d5d:	44 29 c0             	sub    %r8d,%eax
  401d60:	41 89 c0             	mov    %eax,%r8d
  401d63:	41 c1 e0 04          	shl    $0x4,%r8d
  401d67:	41 29 c0             	sub    %eax,%r8d
  401d6a:	89 c8                	mov    %ecx,%eax
  401d6c:	44 29 c2             	sub    %r8d,%edx
  401d6f:	c1 e0 18             	shl    $0x18,%eax
  401d72:	09 c2                	or     %eax,%edx
  401d74:	89 f0                	mov    %esi,%eax
  401d76:	c1 e0 08             	shl    $0x8,%eax
  401d79:	09 c2                	or     %eax,%edx
  401d7b:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  401d82:	41 89 d2             	mov    %edx,%r10d
  401d85:	48 89 c2             	mov    %rax,%rdx
  401d88:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401d8f:	41 89 d0             	mov    %edx,%r8d
  401d92:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401d96:	48 c1 e8 20          	shr    $0x20,%rax
  401d9a:	01 d0                	add    %edx,%eax
  401d9c:	c1 f8 03             	sar    $0x3,%eax
  401d9f:	44 29 c0             	sub    %r8d,%eax
  401da2:	41 89 c0             	mov    %eax,%r8d
  401da5:	41 c1 e0 04          	shl    $0x4,%r8d
  401da9:	41 29 c0             	sub    %eax,%r8d
        struct Data * thread = &data->threads[data->threadindex];
  401dac:	48 63 c1             	movslq %ecx,%rax
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401daf:	44 29 c2             	sub    %r8d,%edx
        struct Data * thread = &data->threads[data->threadindex];
  401db2:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
  401dba:	49 29 c0             	sub    %rax,%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401dbd:	c1 e2 10             	shl    $0x10,%edx
        struct Data * thread = &data->threads[data->threadindex];
  401dc0:	49 c1 e0 07          	shl    $0x7,%r8
  401dc4:	4c 03 43 30          	add    0x30(%rbx),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401dc8:	41 09 d2             	or     %edx,%r10d
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401dcb:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401dd2:	4d 63 d2             	movslq %r10d,%r10
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401dd5:	48 89 d0             	mov    %rdx,%rax
  401dd8:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ddc:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401ddf:	49 c1 e1 04          	shl    $0x4,%r9
  401de3:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401dea:	99                   	cltd
        epoch->time = time;
  401deb:	41 0f 11 41 08       	movups %xmm0,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401df0:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
  data->main->works[buffer] = data->threadindex;
  401df7:	48 8b 47 70          	mov    0x70(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401dfb:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
        epoch->thread = data->threadindex;
  401e02:	41 89 09             	mov    %ecx,(%r9)
  epoch->dest = x;
  401e05:	41 89 71 28          	mov    %esi,0x28(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401e09:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  401e0d:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
  data->main->works[buffer] = data->threadindex;
  401e15:	42 88 0c 10          	mov    %cl,(%rax,%r10,1)
  401e19:	8b 4b 64             	mov    0x64(%rbx),%ecx
    int x = 2 + (data->threadindex + n) % data->threadsize - 2;
  401e1c:	8d 41 01             	lea    0x1(%rcx),%eax
  401e1f:	99                   	cltd
  401e20:	f7 7b 68             	idivl  0x68(%rbx)
  401e23:	89 d6                	mov    %edx,%esi
     if (x != data->threadindex) {
  401e25:	39 d1                	cmp    %edx,%ecx
  401e27:	0f 84 ea 00 00 00    	je     401f17 <threadwork+0x247>
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401e2d:	48 63 83 80 01 00 00 	movslq 0x180(%rbx),%rax
  401e34:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
        epoch->time = time;
  401e38:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401e3d:	48 89 c2             	mov    %rax,%rdx
  401e40:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401e47:	41 89 d0             	mov    %edx,%r8d
  401e4a:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401e4e:	48 c1 e8 20          	shr    $0x20,%rax
  401e52:	01 d0                	add    %edx,%eax
  401e54:	c1 f8 03             	sar    $0x3,%eax
  401e57:	44 29 c0             	sub    %r8d,%eax
  401e5a:	41 89 c0             	mov    %eax,%r8d
  401e5d:	41 c1 e0 04          	shl    $0x4,%r8d
  401e61:	41 29 c0             	sub    %eax,%r8d
  401e64:	89 c8                	mov    %ecx,%eax
  401e66:	44 29 c2             	sub    %r8d,%edx
  401e69:	c1 e0 18             	shl    $0x18,%eax
  401e6c:	09 c2                	or     %eax,%edx
  401e6e:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  401e75:	41 89 d2             	mov    %edx,%r10d
  401e78:	48 89 c2             	mov    %rax,%rdx
  401e7b:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401e82:	41 89 d0             	mov    %edx,%r8d
  401e85:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401e89:	48 c1 e8 20          	shr    $0x20,%rax
  401e8d:	01 d0                	add    %edx,%eax
  401e8f:	c1 f8 03             	sar    $0x3,%eax
  401e92:	44 29 c0             	sub    %r8d,%eax
  401e95:	41 89 c0             	mov    %eax,%r8d
  401e98:	41 c1 e0 04          	shl    $0x4,%r8d
  401e9c:	41 29 c0             	sub    %eax,%r8d
  401e9f:	89 f0                	mov    %esi,%eax
  401ea1:	44 29 c2             	sub    %r8d,%edx
  401ea4:	c1 e0 08             	shl    $0x8,%eax
  401ea7:	c1 e2 10             	shl    $0x10,%edx
  401eaa:	41 09 d2             	or     %edx,%r10d
  401ead:	41 09 c2             	or     %eax,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  401eb0:	48 63 c1             	movslq %ecx,%rax
  401eb3:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401ebb:	4d 63 d2             	movslq %r10d,%r10
        struct Data * thread = &data->threads[data->threadindex];
  401ebe:	49 29 c0             	sub    %rax,%r8
  401ec1:	49 c1 e0 07          	shl    $0x7,%r8
  401ec5:	4c 03 43 30          	add    0x30(%rbx),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401ec9:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  401ed0:	48 89 d0             	mov    %rdx,%rax
  401ed3:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ed7:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401eda:	49 c1 e1 04          	shl    $0x4,%r9
  401ede:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ee5:	99                   	cltd
        epoch->time = time;
  401ee6:	41 0f 11 49 08       	movups %xmm1,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401eeb:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
  data->main->works[buffer] = data->threadindex;
  401ef2:	48 8b 47 70          	mov    0x70(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ef6:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
        epoch->thread = data->threadindex;
  401efd:	41 89 09             	mov    %ecx,(%r9)
  epoch->dest = x;
  401f00:	41 89 71 28          	mov    %esi,0x28(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401f04:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  401f08:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
  data->main->works[buffer] = data->threadindex;
  401f10:	42 88 0c 10          	mov    %cl,(%rax,%r10,1)
  401f14:	8b 4b 64             	mov    0x64(%rbx),%ecx
    int x = 2 + (data->threadindex + n) % data->threadsize - 2;
  401f17:	8d 41 02             	lea    0x2(%rcx),%eax
  401f1a:	99                   	cltd
  401f1b:	f7 7b 68             	idivl  0x68(%rbx)
  401f1e:	89 d6                	mov    %edx,%esi
     if (x != data->threadindex) {
  401f20:	39 d1                	cmp    %edx,%ecx
  401f22:	0f 84 ea 00 00 00    	je     402012 <threadwork+0x342>
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401f28:	48 63 83 80 01 00 00 	movslq 0x180(%rbx),%rax
  401f2f:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
        epoch->time = time;
  401f33:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401f38:	48 89 c2             	mov    %rax,%rdx
  401f3b:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401f42:	41 89 d0             	mov    %edx,%r8d
  401f45:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401f49:	48 c1 e8 20          	shr    $0x20,%rax
  401f4d:	01 d0                	add    %edx,%eax
  401f4f:	c1 f8 03             	sar    $0x3,%eax
  401f52:	44 29 c0             	sub    %r8d,%eax
  401f55:	41 89 c0             	mov    %eax,%r8d
  401f58:	41 c1 e0 04          	shl    $0x4,%r8d
  401f5c:	41 29 c0             	sub    %eax,%r8d
  401f5f:	89 c8                	mov    %ecx,%eax
  401f61:	44 29 c2             	sub    %r8d,%edx
  401f64:	c1 e0 18             	shl    $0x18,%eax
  401f67:	09 c2                	or     %eax,%edx
  401f69:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  401f70:	41 89 d2             	mov    %edx,%r10d
  401f73:	48 89 c2             	mov    %rax,%rdx
  401f76:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401f7d:	41 89 d0             	mov    %edx,%r8d
  401f80:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401f84:	48 c1 e8 20          	shr    $0x20,%rax
  401f88:	01 d0                	add    %edx,%eax
  401f8a:	c1 f8 03             	sar    $0x3,%eax
  401f8d:	44 29 c0             	sub    %r8d,%eax
  401f90:	41 89 c0             	mov    %eax,%r8d
  401f93:	41 c1 e0 04          	shl    $0x4,%r8d
  401f97:	41 29 c0             	sub    %eax,%r8d
  401f9a:	89 f0                	mov    %esi,%eax
  401f9c:	44 29 c2             	sub    %r8d,%edx
  401f9f:	c1 e0 08             	shl    $0x8,%eax
  401fa2:	c1 e2 10             	shl    $0x10,%edx
  401fa5:	41 09 d2             	or     %edx,%r10d
  401fa8:	41 09 c2             	or     %eax,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  401fab:	48 63 c1             	movslq %ecx,%rax
  401fae:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401fb6:	4d 63 d2             	movslq %r10d,%r10
        struct Data * thread = &data->threads[data->threadindex];
  401fb9:	49 29 c0             	sub    %rax,%r8
  401fbc:	49 c1 e0 07          	shl    $0x7,%r8
  401fc0:	4c 03 43 30          	add    0x30(%rbx),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401fc4:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  401fcb:	48 89 d0             	mov    %rdx,%rax
  401fce:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401fd2:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401fd5:	49 c1 e1 04          	shl    $0x4,%r9
  401fd9:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401fe0:	99                   	cltd
        epoch->time = time;
  401fe1:	41 0f 11 51 08       	movups %xmm2,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401fe6:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
  data->main->works[buffer] = data->threadindex;
  401fed:	48 8b 47 70          	mov    0x70(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ff1:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
        epoch->thread = data->threadindex;
  401ff8:	41 89 09             	mov    %ecx,(%r9)
  epoch->dest = x;
  401ffb:	41 89 71 28          	mov    %esi,0x28(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401fff:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  402003:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
  data->main->works[buffer] = data->threadindex;
  40200b:	42 88 0c 10          	mov    %cl,(%rax,%r10,1)
  40200f:	8b 4b 64             	mov    0x64(%rbx),%ecx
    int x = 2 + (data->threadindex + n) % data->threadsize - 2;
  402012:	8d 41 03             	lea    0x3(%rcx),%eax
  402015:	99                   	cltd
  402016:	f7 7b 68             	idivl  0x68(%rbx)
  402019:	89 d6                	mov    %edx,%esi
     if (x != data->threadindex) {
  40201b:	39 d1                	cmp    %edx,%ecx
  40201d:	0f 84 ea 00 00 00    	je     40210d <threadwork+0x43d>
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  402023:	48 63 83 80 01 00 00 	movslq 0x180(%rbx),%rax
  40202a:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
        epoch->time = time;
  40202e:	66 0f 6f 1c 24       	movdqa (%rsp),%xmm3
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  402033:	48 89 c2             	mov    %rax,%rdx
  402036:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  40203d:	41 89 d0             	mov    %edx,%r8d
  402040:	41 c1 f8 1f          	sar    $0x1f,%r8d
  402044:	48 c1 e8 20          	shr    $0x20,%rax
  402048:	01 d0                	add    %edx,%eax
  40204a:	c1 f8 03             	sar    $0x3,%eax
  40204d:	44 29 c0             	sub    %r8d,%eax
  402050:	41 89 c0             	mov    %eax,%r8d
  402053:	41 c1 e0 04          	shl    $0x4,%r8d
  402057:	41 29 c0             	sub    %eax,%r8d
  40205a:	89 c8                	mov    %ecx,%eax
  40205c:	44 29 c2             	sub    %r8d,%edx
  40205f:	c1 e0 18             	shl    $0x18,%eax
  402062:	09 c2                	or     %eax,%edx
  402064:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  40206b:	41 89 d2             	mov    %edx,%r10d
  40206e:	48 89 c2             	mov    %rax,%rdx
  402071:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402078:	41 89 d0             	mov    %edx,%r8d
  40207b:	41 c1 f8 1f          	sar    $0x1f,%r8d
  40207f:	48 c1 e8 20          	shr    $0x20,%rax
  402083:	01 d0                	add    %edx,%eax
  402085:	c1 f8 03             	sar    $0x3,%eax
  402088:	44 29 c0             	sub    %r8d,%eax
  40208b:	41 89 c0             	mov    %eax,%r8d
  40208e:	41 c1 e0 04          	shl    $0x4,%r8d
  402092:	41 29 c0             	sub    %eax,%r8d
  402095:	89 f0                	mov    %esi,%eax
  402097:	44 29 c2             	sub    %r8d,%edx
  40209a:	c1 e0 08             	shl    $0x8,%eax
  40209d:	c1 e2 10             	shl    $0x10,%edx
  4020a0:	41 09 d2             	or     %edx,%r10d
  4020a3:	41 09 c2             	or     %eax,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  4020a6:	48 63 c1             	movslq %ecx,%rax
  4020a9:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  4020b1:	4d 63 d2             	movslq %r10d,%r10
        struct Data * thread = &data->threads[data->threadindex];
  4020b4:	49 29 c0             	sub    %rax,%r8
  4020b7:	49 c1 e0 07          	shl    $0x7,%r8
  4020bb:	4c 03 43 30          	add    0x30(%rbx),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4020bf:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  4020c6:	48 89 d0             	mov    %rdx,%rax
  4020c9:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4020cd:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4020d0:	49 c1 e1 04          	shl    $0x4,%r9
  4020d4:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4020db:	99                   	cltd
        epoch->time = time;
  4020dc:	41 0f 11 59 08       	movups %xmm3,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4020e1:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
  data->main->works[buffer] = data->threadindex;
  4020e8:	48 8b 47 70          	mov    0x70(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4020ec:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
        epoch->thread = data->threadindex;
  4020f3:	41 89 09             	mov    %ecx,(%r9)
  epoch->dest = x;
  4020f6:	41 89 71 28          	mov    %esi,0x28(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  4020fa:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  4020fe:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
  data->main->works[buffer] = data->threadindex;
  402106:	42 88 0c 10          	mov    %cl,(%rax,%r10,1)
  40210a:	8b 4b 64             	mov    0x64(%rbx),%ecx
    int x = 2 + (data->threadindex + n) % data->threadsize - 2;
  40210d:	8d 41 04             	lea    0x4(%rcx),%eax
  402110:	99                   	cltd
  402111:	f7 7b 68             	idivl  0x68(%rbx)
  402114:	89 d6                	mov    %edx,%esi
     if (x != data->threadindex) {
  402116:	39 d1                	cmp    %edx,%ecx
  402118:	0f 84 ea 00 00 00    	je     402208 <threadwork+0x538>
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  40211e:	48 63 83 80 01 00 00 	movslq 0x180(%rbx),%rax
  402125:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
        epoch->time = time;
  402129:	66 0f 6f 24 24       	movdqa (%rsp),%xmm4
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  40212e:	48 89 c2             	mov    %rax,%rdx
  402131:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402138:	41 89 d0             	mov    %edx,%r8d
  40213b:	41 c1 f8 1f          	sar    $0x1f,%r8d
  40213f:	48 c1 e8 20          	shr    $0x20,%rax
  402143:	01 d0                	add    %edx,%eax
  402145:	c1 f8 03             	sar    $0x3,%eax
  402148:	44 29 c0             	sub    %r8d,%eax
  40214b:	41 89 c0             	mov    %eax,%r8d
  40214e:	41 c1 e0 04          	shl    $0x4,%r8d
  402152:	41 29 c0             	sub    %eax,%r8d
  402155:	89 c8                	mov    %ecx,%eax
  402157:	44 29 c2             	sub    %r8d,%edx
  40215a:	c1 e0 18             	shl    $0x18,%eax
  40215d:	09 c2                	or     %eax,%edx
  40215f:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  402166:	41 89 d2             	mov    %edx,%r10d
  402169:	48 89 c2             	mov    %rax,%rdx
  40216c:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402173:	41 89 d0             	mov    %edx,%r8d
  402176:	41 c1 f8 1f          	sar    $0x1f,%r8d
  40217a:	48 c1 e8 20          	shr    $0x20,%rax
  40217e:	01 d0                	add    %edx,%eax
  402180:	c1 f8 03             	sar    $0x3,%eax
  402183:	44 29 c0             	sub    %r8d,%eax
  402186:	41 89 c0             	mov    %eax,%r8d
  402189:	41 c1 e0 04          	shl    $0x4,%r8d
  40218d:	41 29 c0             	sub    %eax,%r8d
  402190:	89 f0                	mov    %esi,%eax
  402192:	44 29 c2             	sub    %r8d,%edx
  402195:	c1 e0 08             	shl    $0x8,%eax
  402198:	c1 e2 10             	shl    $0x10,%edx
  40219b:	41 09 d2             	or     %edx,%r10d
  40219e:	41 09 c2             	or     %eax,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  4021a1:	48 63 c1             	movslq %ecx,%rax
  4021a4:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  4021ac:	4d 63 d2             	movslq %r10d,%r10
        struct Data * thread = &data->threads[data->threadindex];
  4021af:	49 29 c0             	sub    %rax,%r8
  4021b2:	49 c1 e0 07          	shl    $0x7,%r8
  4021b6:	4c 03 43 30          	add    0x30(%rbx),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4021ba:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  4021c1:	48 89 d0             	mov    %rdx,%rax
  4021c4:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4021c8:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4021cb:	49 c1 e1 04          	shl    $0x4,%r9
  4021cf:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4021d6:	99                   	cltd
        epoch->time = time;
  4021d7:	41 0f 11 61 08       	movups %xmm4,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4021dc:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
  data->main->works[buffer] = data->threadindex;
  4021e3:	48 8b 47 70          	mov    0x70(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4021e7:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
        epoch->thread = data->threadindex;
  4021ee:	41 89 09             	mov    %ecx,(%r9)
  epoch->dest = x;
  4021f1:	41 89 71 28          	mov    %esi,0x28(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  4021f5:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  4021f9:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
  data->main->works[buffer] = data->threadindex;
  402201:	42 88 0c 10          	mov    %cl,(%rax,%r10,1)
  402205:	8b 4b 64             	mov    0x64(%rbx),%ecx
    int x = 2 + (data->threadindex + n) % data->threadsize - 2;
  402208:	8d 41 05             	lea    0x5(%rcx),%eax
  40220b:	99                   	cltd
  40220c:	f7 7b 68             	idivl  0x68(%rbx)
  40220f:	89 d6                	mov    %edx,%esi
     if (x != data->threadindex) {
  402211:	39 d1                	cmp    %edx,%ecx
  402213:	0f 84 ea 00 00 00    	je     402303 <threadwork+0x633>
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  402219:	48 63 83 80 01 00 00 	movslq 0x180(%rbx),%rax
  402220:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
        epoch->time = time;
  402224:	66 0f 6f 2c 24       	movdqa (%rsp),%xmm5
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  402229:	48 89 c2             	mov    %rax,%rdx
  40222c:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402233:	41 89 d0             	mov    %edx,%r8d
  402236:	41 c1 f8 1f          	sar    $0x1f,%r8d
  40223a:	48 c1 e8 20          	shr    $0x20,%rax
  40223e:	01 d0                	add    %edx,%eax
  402240:	c1 f8 03             	sar    $0x3,%eax
  402243:	44 29 c0             	sub    %r8d,%eax
  402246:	41 89 c0             	mov    %eax,%r8d
  402249:	41 c1 e0 04          	shl    $0x4,%r8d
  40224d:	41 29 c0             	sub    %eax,%r8d
  402250:	89 c8                	mov    %ecx,%eax
  402252:	44 29 c2             	sub    %r8d,%edx
  402255:	c1 e0 18             	shl    $0x18,%eax
  402258:	09 c2                	or     %eax,%edx
  40225a:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  402261:	41 89 d2             	mov    %edx,%r10d
  402264:	48 89 c2             	mov    %rax,%rdx
  402267:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  40226e:	41 89 d0             	mov    %edx,%r8d
  402271:	41 c1 f8 1f          	sar    $0x1f,%r8d
  402275:	48 c1 e8 20          	shr    $0x20,%rax
  402279:	01 d0                	add    %edx,%eax
  40227b:	c1 f8 03             	sar    $0x3,%eax
  40227e:	44 29 c0             	sub    %r8d,%eax
  402281:	41 89 c0             	mov    %eax,%r8d
  402284:	41 c1 e0 04          	shl    $0x4,%r8d
  402288:	41 29 c0             	sub    %eax,%r8d
  40228b:	89 f0                	mov    %esi,%eax
  40228d:	44 29 c2             	sub    %r8d,%edx
  402290:	c1 e0 08             	shl    $0x8,%eax
  402293:	c1 e2 10             	shl    $0x10,%edx
  402296:	41 09 d2             	or     %edx,%r10d
  402299:	41 09 c2             	or     %eax,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  40229c:	48 63 c1             	movslq %ecx,%rax
  40229f:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  4022a7:	4d 63 d2             	movslq %r10d,%r10
        struct Data * thread = &data->threads[data->threadindex];
  4022aa:	49 29 c0             	sub    %rax,%r8
  4022ad:	49 c1 e0 07          	shl    $0x7,%r8
  4022b1:	4c 03 43 30          	add    0x30(%rbx),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4022b5:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  4022bc:	48 89 d0             	mov    %rdx,%rax
  4022bf:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4022c3:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4022c6:	49 c1 e1 04          	shl    $0x4,%r9
  4022ca:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4022d1:	99                   	cltd
        epoch->time = time;
  4022d2:	41 0f 11 69 08       	movups %xmm5,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4022d7:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
  data->main->works[buffer] = data->threadindex;
  4022de:	48 8b 47 70          	mov    0x70(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4022e2:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
        epoch->thread = data->threadindex;
  4022e9:	41 89 09             	mov    %ecx,(%r9)
  epoch->dest = x;
  4022ec:	41 89 71 28          	mov    %esi,0x28(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  4022f0:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  4022f4:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
  data->main->works[buffer] = data->threadindex;
  4022fc:	42 88 0c 10          	mov    %cl,(%rax,%r10,1)
  402300:	8b 4b 64             	mov    0x64(%rbx),%ecx
    int x = 2 + (data->threadindex + n) % data->threadsize - 2;
  402303:	8d 41 06             	lea    0x6(%rcx),%eax
  402306:	99                   	cltd
  402307:	f7 7b 68             	idivl  0x68(%rbx)
  40230a:	89 d6                	mov    %edx,%esi
     if (x != data->threadindex) {
  40230c:	39 d1                	cmp    %edx,%ecx
  40230e:	0f 84 e7 00 00 00    	je     4023fb <threadwork+0x72b>
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  402314:	48 63 83 80 01 00 00 	movslq 0x180(%rbx),%rax
  40231b:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
        epoch->time = time;
  40231f:	66 0f 6f 34 24       	movdqa (%rsp),%xmm6
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  402324:	48 89 c2             	mov    %rax,%rdx
  402327:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  40232e:	41 89 d0             	mov    %edx,%r8d
  402331:	41 c1 f8 1f          	sar    $0x1f,%r8d
  402335:	48 c1 e8 20          	shr    $0x20,%rax
  402339:	01 d0                	add    %edx,%eax
  40233b:	c1 f8 03             	sar    $0x3,%eax
  40233e:	44 29 c0             	sub    %r8d,%eax
  402341:	41 89 c0             	mov    %eax,%r8d
  402344:	41 c1 e0 04          	shl    $0x4,%r8d
  402348:	41 29 c0             	sub    %eax,%r8d
  40234b:	89 c8                	mov    %ecx,%eax
  40234d:	44 29 c2             	sub    %r8d,%edx
  402350:	c1 e0 18             	shl    $0x18,%eax
  402353:	09 c2                	or     %eax,%edx
  402355:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  40235c:	41 89 d2             	mov    %edx,%r10d
  40235f:	48 89 c2             	mov    %rax,%rdx
  402362:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402369:	41 89 d0             	mov    %edx,%r8d
  40236c:	41 c1 f8 1f          	sar    $0x1f,%r8d
  402370:	48 c1 e8 20          	shr    $0x20,%rax
  402374:	01 d0                	add    %edx,%eax
  402376:	c1 f8 03             	sar    $0x3,%eax
  402379:	44 29 c0             	sub    %r8d,%eax
  40237c:	41 89 c0             	mov    %eax,%r8d
  40237f:	41 c1 e0 04          	shl    $0x4,%r8d
  402383:	41 29 c0             	sub    %eax,%r8d
  402386:	89 f0                	mov    %esi,%eax
  402388:	44 29 c2             	sub    %r8d,%edx
  40238b:	c1 e0 08             	shl    $0x8,%eax
  40238e:	c1 e2 10             	shl    $0x10,%edx
  402391:	41 09 d2             	or     %edx,%r10d
  402394:	41 09 c2             	or     %eax,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  402397:	48 63 c1             	movslq %ecx,%rax
  40239a:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  4023a2:	4d 63 d2             	movslq %r10d,%r10
        struct Data * thread = &data->threads[data->threadindex];
  4023a5:	49 29 c0             	sub    %rax,%r8
  4023a8:	49 c1 e0 07          	shl    $0x7,%r8
  4023ac:	4c 03 43 30          	add    0x30(%rbx),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4023b0:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  4023b7:	48 89 d0             	mov    %rdx,%rax
  4023ba:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4023be:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4023c1:	49 c1 e1 04          	shl    $0x4,%r9
  4023c5:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4023cc:	99                   	cltd
        epoch->time = time;
  4023cd:	41 0f 11 71 08       	movups %xmm6,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4023d2:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
  data->main->works[buffer] = data->threadindex;
  4023d9:	48 8b 47 70          	mov    0x70(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4023dd:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
        epoch->thread = data->threadindex;
  4023e4:	41 89 09             	mov    %ecx,(%r9)
  epoch->dest = x;
  4023e7:	41 89 71 28          	mov    %esi,0x28(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  4023eb:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  4023ef:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
  data->main->works[buffer] = data->threadindex;
  4023f7:	42 88 0c 10          	mov    %cl,(%rax,%r10,1)
    data->writecursor = (data->writecursor + 1) % 0xf;
  4023fb:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
  402401:	8d 50 01             	lea    0x1(%rax),%edx
  402404:	48 63 c2             	movslq %edx,%rax
  402407:	89 d1                	mov    %edx,%ecx
  402409:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402410:	c1 f9 1f             	sar    $0x1f,%ecx
  402413:	48 c1 e8 20          	shr    $0x20,%rax
  402417:	01 d0                	add    %edx,%eax
  402419:	c1 f8 03             	sar    $0x3,%eax
  40241c:	29 c8                	sub    %ecx,%eax
  40241e:	89 c1                	mov    %eax,%ecx
  402420:	c1 e1 04             	shl    $0x4,%ecx
  402423:	29 c1                	sub    %eax,%ecx
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_RELAXED);
  402425:	48 8b 43 28          	mov    0x28(%rbx),%rax
    data->writecursor = (data->writecursor + 1) % 0xf;
  402429:	29 ca                	sub    %ecx,%edx
  40242b:	89 93 80 01 00 00    	mov    %edx,0x180(%rbx)
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_RELAXED);
  402431:	f0 48 83 80 50 03 00 00 01 	lock addq $0x1,0x350(%rax)
  long lastread = data->main->totalreads % data->threadsize;
  40243a:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
  40243e:	48 63 4b 68          	movslq 0x68(%rbx),%rcx
  402442:	48 8b 87 40 03 00 00 	mov    0x340(%rdi),%rax
  402449:	48 89 ce             	mov    %rcx,%rsi
   data->freq++;
  40244c:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
  long lastread = data->main->totalreads % data->threadsize;
  402451:	48 99                	cqto
  402453:	48 f7 f9             	idiv   %rcx
    int x = 2 + ((data->threadindex + y) % data->threadsize - 2);
  402456:	8b 4b 64             	mov    0x64(%rbx),%ecx
  402459:	89 c8                	mov    %ecx,%eax
   data->prevread = lastread;
  40245b:	48 89 93 08 03 00 00 	mov    %rdx,0x308(%rbx)
    int x = 2 + ((data->threadindex + y) % data->threadsize - 2);
  402462:	99                   	cltd
  402463:	f7 fe                	idiv   %esi
  402465:	41 89 d1             	mov    %edx,%r9d
          if (x != data->threadindex) {
  402468:	39 d1                	cmp    %edx,%ecx
  40246a:	0f 84 04 01 00 00    	je     402574 <threadwork+0x8a4>
            long past = ((data->main->writecursor - 1) % 0xf);
  402470:	8b 87 80 01 00 00    	mov    0x180(%rdi),%eax
              past = data->threadsize - 1;
  402476:	44 8d 56 ff          	lea    -0x1(%rsi),%r10d
            long past = ((data->main->writecursor - 1) % 0xf);
  40247a:	8d 50 ff             	lea    -0x1(%rax),%edx
  40247d:	48 63 c2             	movslq %edx,%rax
  402480:	41 89 d0             	mov    %edx,%r8d
  402483:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  40248a:	41 c1 f8 1f          	sar    $0x1f,%r8d
  40248e:	48 c1 e8 20          	shr    $0x20,%rax
  402492:	01 d0                	add    %edx,%eax
  402494:	c1 f8 03             	sar    $0x3,%eax
  402497:	44 29 c0             	sub    %r8d,%eax
  40249a:	41 89 c0             	mov    %eax,%r8d
  40249d:	41 c1 e0 04          	shl    $0x4,%r8d
  4024a1:	41 29 c0             	sub    %eax,%r8d
              past = data->threadsize - 1;
  4024a4:	89 d0                	mov    %edx,%eax
            int rc = data->threads[x].writecursor;
  4024a6:	48 8b 53 30          	mov    0x30(%rbx),%rdx
              past = data->threadsize - 1;
  4024aa:	44 29 c0             	sub    %r8d,%eax
  4024ad:	41 0f 48 c2          	cmovs  %r10d,%eax
            int rc = data->threads[x].writecursor;
  4024b1:	4d 63 d1             	movslq %r9d,%r10
  4024b4:	4c 63 c0             	movslq %eax,%r8
  4024b7:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
  4024bf:	4c 29 d0             	sub    %r10,%rax
  4024c2:	48 c1 e0 07          	shl    $0x7,%rax
  4024c6:	44 8b 9c 02 80 01 00 00 	mov    0x180(%rdx,%rax,1),%r11d
            if (rc < 0) {
  4024ce:	45 85 db             	test   %r11d,%r11d
  4024d1:	0f 88 89 07 00 00    	js     402c60 <threadwork+0xf90>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4024d7:	49 63 c3             	movslq %r11d,%rax
  4024da:	45 89 da             	mov    %r11d,%r10d
  4024dd:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  4024e4:	41 c1 fa 1f          	sar    $0x1f,%r10d
  4024e8:	48 c1 e8 20          	shr    $0x20,%rax
  4024ec:	44 01 d8             	add    %r11d,%eax
  4024ef:	c1 f8 03             	sar    $0x3,%eax
  4024f2:	44 29 d0             	sub    %r10d,%eax
  4024f5:	41 89 c2             	mov    %eax,%r10d
  4024f8:	41 c1 e2 04          	shl    $0x4,%r10d
  4024fc:	41 29 c2             	sub    %eax,%r10d
  4024ff:	45 29 d3             	sub    %r10d,%r11d
  402502:	4d 63 db             	movslq %r11d,%r11
                struct Data * thread = &data->threads[data->threadindex];
  402505:	48 63 c1             	movslq %ecx,%rax
            thepoch->time = time; 
  402508:	66 0f 6f 3c 24       	movdqa (%rsp),%xmm7
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40250d:	49 c1 e0 10          	shl    $0x10,%r8
                struct Data * thread = &data->threads[data->threadindex];
  402511:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  402519:	48 29 c5             	sub    %rax,%rbp
  40251c:	48 c1 e5 07          	shl    $0x7,%rbp
  402520:	48 01 d5             	add    %rdx,%rbp
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402523:	48 63 95 24 03 00 00 	movslq 0x324(%rbp),%rdx
  40252a:	48 89 d0             	mov    %rdx,%rax
  40252d:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402531:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402534:	49 c1 e2 04          	shl    $0x4,%r10
  402538:	4c 03 95 18 03 00 00 	add    0x318(%rbp),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40253f:	99                   	cltd
            thepoch->time = time; 
  402540:	41 0f 11 7a 08       	movups %xmm7,0x8(%r10)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402545:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40254b:	89 c8                	mov    %ecx,%eax
  40254d:	c1 e0 08             	shl    $0x8,%eax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402550:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
                thepoch->thread = x;
  402556:	45 89 0a             	mov    %r9d,(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402559:	41 c1 e1 18          	shl    $0x18,%r9d
  40255d:	44 09 c8             	or     %r9d,%eax
          thepoch->set = 1;
  402560:	41 c7 42 24 01 00 00 00 	movl   $0x1,0x24(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402568:	48 98                	cltq
  40256a:	4c 09 c0             	or     %r8,%rax
  40256d:	4c 09 d8             	or     %r11,%rax
  402570:	49 89 42 18          	mov    %rax,0x18(%r10)
    int x = 2 + ((data->threadindex + y) % data->threadsize - 2);
  402574:	8d 41 01             	lea    0x1(%rcx),%eax
  402577:	99                   	cltd
  402578:	f7 fe                	idiv   %esi
  40257a:	41 89 d1             	mov    %edx,%r9d
          if (x != data->threadindex) {
  40257d:	39 ca                	cmp    %ecx,%edx
  40257f:	0f 84 05 01 00 00    	je     40268a <threadwork+0x9ba>
            long past = ((data->main->writecursor - 1) % 0xf);
  402585:	8b 87 80 01 00 00    	mov    0x180(%rdi),%eax
              past = data->threadsize - 1;
  40258b:	44 8d 56 ff          	lea    -0x1(%rsi),%r10d
            long past = ((data->main->writecursor - 1) % 0xf);
  40258f:	8d 50 ff             	lea    -0x1(%rax),%edx
  402592:	48 63 c2             	movslq %edx,%rax
  402595:	41 89 d0             	mov    %edx,%r8d
  402598:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  40259f:	41 c1 f8 1f          	sar    $0x1f,%r8d
  4025a3:	48 c1 e8 20          	shr    $0x20,%rax
  4025a7:	01 d0                	add    %edx,%eax
  4025a9:	c1 f8 03             	sar    $0x3,%eax
  4025ac:	44 29 c0             	sub    %r8d,%eax
  4025af:	41 89 c0             	mov    %eax,%r8d
  4025b2:	41 c1 e0 04          	shl    $0x4,%r8d
  4025b6:	41 29 c0             	sub    %eax,%r8d
              past = data->threadsize - 1;
  4025b9:	89 d0                	mov    %edx,%eax
            int rc = data->threads[x].writecursor;
  4025bb:	48 8b 53 30          	mov    0x30(%rbx),%rdx
              past = data->threadsize - 1;
  4025bf:	44 29 c0             	sub    %r8d,%eax
  4025c2:	41 0f 48 c2          	cmovs  %r10d,%eax
            int rc = data->threads[x].writecursor;
  4025c6:	4d 63 d1             	movslq %r9d,%r10
  4025c9:	4c 63 c0             	movslq %eax,%r8
  4025cc:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
  4025d4:	4c 29 d0             	sub    %r10,%rax
  4025d7:	48 c1 e0 07          	shl    $0x7,%rax
  4025db:	44 8b 9c 02 80 01 00 00 	mov    0x180(%rdx,%rax,1),%r11d
            if (rc < 0) {
  4025e3:	45 85 db             	test   %r11d,%r11d
  4025e6:	0f 88 64 06 00 00    	js     402c50 <threadwork+0xf80>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4025ec:	49 63 c3             	movslq %r11d,%rax
  4025ef:	45 89 da             	mov    %r11d,%r10d
  4025f2:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  4025f9:	41 c1 fa 1f          	sar    $0x1f,%r10d
  4025fd:	48 c1 e8 20          	shr    $0x20,%rax
  402601:	44 01 d8             	add    %r11d,%eax
  402604:	c1 f8 03             	sar    $0x3,%eax
  402607:	44 29 d0             	sub    %r10d,%eax
  40260a:	41 89 c2             	mov    %eax,%r10d
  40260d:	41 c1 e2 04          	shl    $0x4,%r10d
  402611:	41 29 c2             	sub    %eax,%r10d
  402614:	45 29 d3             	sub    %r10d,%r11d
  402617:	4d 63 db             	movslq %r11d,%r11
                struct Data * thread = &data->threads[data->threadindex];
  40261a:	48 63 c1             	movslq %ecx,%rax
            thepoch->time = time; 
  40261d:	66 0f 6f 04 24       	movdqa (%rsp),%xmm0
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402622:	49 c1 e0 10          	shl    $0x10,%r8
                struct Data * thread = &data->threads[data->threadindex];
  402626:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  40262e:	48 29 c5             	sub    %rax,%rbp
  402631:	48 c1 e5 07          	shl    $0x7,%rbp
  402635:	48 01 d5             	add    %rdx,%rbp
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402638:	48 63 95 24 03 00 00 	movslq 0x324(%rbp),%rdx
  40263f:	48 89 d0             	mov    %rdx,%rax
  402642:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402646:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402649:	49 c1 e2 04          	shl    $0x4,%r10
  40264d:	4c 03 95 18 03 00 00 	add    0x318(%rbp),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402654:	99                   	cltd
            thepoch->time = time; 
  402655:	41 0f 11 42 08       	movups %xmm0,0x8(%r10)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40265a:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402660:	44 89 c8             	mov    %r9d,%eax
  402663:	c1 e0 18             	shl    $0x18,%eax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402666:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40266c:	89 ca                	mov    %ecx,%edx
  40266e:	c1 e2 08             	shl    $0x8,%edx
                thepoch->thread = x;
  402671:	45 89 0a             	mov    %r9d,(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402674:	09 d0                	or     %edx,%eax
          thepoch->set = 1;
  402676:	41 c7 42 24 01 00 00 00 	movl   $0x1,0x24(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40267e:	48 98                	cltq
  402680:	4c 09 c0             	or     %r8,%rax
  402683:	4c 09 d8             	or     %r11,%rax
  402686:	49 89 42 18          	mov    %rax,0x18(%r10)
    int x = 2 + ((data->threadindex + y) % data->threadsize - 2);
  40268a:	8d 41 02             	lea    0x2(%rcx),%eax
  40268d:	99                   	cltd
  40268e:	f7 fe                	idiv   %esi
  402690:	41 89 d1             	mov    %edx,%r9d
          if (x != data->threadindex) {
  402693:	39 d1                	cmp    %edx,%ecx
  402695:	0f 84 05 01 00 00    	je     4027a0 <threadwork+0xad0>
            long past = ((data->main->writecursor - 1) % 0xf);
  40269b:	8b 87 80 01 00 00    	mov    0x180(%rdi),%eax
              past = data->threadsize - 1;
  4026a1:	44 8d 56 ff          	lea    -0x1(%rsi),%r10d
            long past = ((data->main->writecursor - 1) % 0xf);
  4026a5:	8d 50 ff             	lea    -0x1(%rax),%edx
  4026a8:	48 63 c2             	movslq %edx,%rax
  4026ab:	41 89 d0             	mov    %edx,%r8d
  4026ae:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  4026b5:	41 c1 f8 1f          	sar    $0x1f,%r8d
  4026b9:	48 c1 e8 20          	shr    $0x20,%rax
  4026bd:	01 d0                	add    %edx,%eax
  4026bf:	c1 f8 03             	sar    $0x3,%eax
  4026c2:	44 29 c0             	sub    %r8d,%eax
  4026c5:	41 89 c0             	mov    %eax,%r8d
  4026c8:	41 c1 e0 04          	shl    $0x4,%r8d
  4026cc:	41 29 c0             	sub    %eax,%r8d
              past = data->threadsize - 1;
  4026cf:	89 d0                	mov    %edx,%eax
            int rc = data->threads[x].writecursor;
  4026d1:	48 8b 53 30          	mov    0x30(%rbx),%rdx
              past = data->threadsize - 1;
  4026d5:	44 29 c0             	sub    %r8d,%eax
  4026d8:	41 0f 48 c2          	cmovs  %r10d,%eax
            int rc = data->threads[x].writecursor;
  4026dc:	4d 63 d1             	movslq %r9d,%r10
  4026df:	4c 63 c0             	movslq %eax,%r8
  4026e2:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
  4026ea:	4c 29 d0             	sub    %r10,%rax
  4026ed:	48 c1 e0 07          	shl    $0x7,%rax
  4026f1:	44 8b 9c 02 80 01 00 00 	mov    0x180(%rdx,%rax,1),%r11d
            if (rc < 0) {
  4026f9:	45 85 db             	test   %r11d,%r11d
  4026fc:	0f 88 7e 05 00 00    	js     402c80 <threadwork+0xfb0>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402702:	49 63 c3             	movslq %r11d,%rax
  402705:	45 89 da             	mov    %r11d,%r10d
  402708:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  40270f:	41 c1 fa 1f          	sar    $0x1f,%r10d
  402713:	48 c1 e8 20          	shr    $0x20,%rax
  402717:	44 01 d8             	add    %r11d,%eax
  40271a:	c1 f8 03             	sar    $0x3,%eax
  40271d:	44 29 d0             	sub    %r10d,%eax
  402720:	41 89 c2             	mov    %eax,%r10d
  402723:	41 c1 e2 04          	shl    $0x4,%r10d
  402727:	41 29 c2             	sub    %eax,%r10d
  40272a:	45 29 d3             	sub    %r10d,%r11d
  40272d:	4d 63 db             	movslq %r11d,%r11
                struct Data * thread = &data->threads[data->threadindex];
  402730:	48 63 c1             	movslq %ecx,%rax
            thepoch->time = time; 
  402733:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402738:	49 c1 e0 10          	shl    $0x10,%r8
                struct Data * thread = &data->threads[data->threadindex];
  40273c:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  402744:	48 29 c5             	sub    %rax,%rbp
  402747:	48 c1 e5 07          	shl    $0x7,%rbp
  40274b:	48 01 d5             	add    %rdx,%rbp
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  40274e:	48 63 95 24 03 00 00 	movslq 0x324(%rbp),%rdx
  402755:	48 89 d0             	mov    %rdx,%rax
  402758:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40275c:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  40275f:	49 c1 e2 04          	shl    $0x4,%r10
  402763:	4c 03 95 18 03 00 00 	add    0x318(%rbp),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40276a:	99                   	cltd
            thepoch->time = time; 
  40276b:	41 0f 11 4a 08       	movups %xmm1,0x8(%r10)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402770:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402776:	44 89 c8             	mov    %r9d,%eax
  402779:	c1 e0 18             	shl    $0x18,%eax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40277c:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402782:	89 ca                	mov    %ecx,%edx
  402784:	c1 e2 08             	shl    $0x8,%edx
                thepoch->thread = x;
  402787:	45 89 0a             	mov    %r9d,(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40278a:	09 d0                	or     %edx,%eax
          thepoch->set = 1;
  40278c:	41 c7 42 24 01 00 00 00 	movl   $0x1,0x24(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402794:	48 98                	cltq
  402796:	4c 09 c0             	or     %r8,%rax
  402799:	4c 09 d8             	or     %r11,%rax
  40279c:	49 89 42 18          	mov    %rax,0x18(%r10)
    int x = 2 + ((data->threadindex + y) % data->threadsize - 2);
  4027a0:	8d 41 03             	lea    0x3(%rcx),%eax
  4027a3:	99                   	cltd
  4027a4:	f7 fe                	idiv   %esi
  4027a6:	41 89 d1             	mov    %edx,%r9d
          if (x != data->threadindex) {
  4027a9:	39 d1                	cmp    %edx,%ecx
  4027ab:	0f 84 05 01 00 00    	je     4028b6 <threadwork+0xbe6>
            long past = ((data->main->writecursor - 1) % 0xf);
  4027b1:	8b 87 80 01 00 00    	mov    0x180(%rdi),%eax
              past = data->threadsize - 1;
  4027b7:	44 8d 56 ff          	lea    -0x1(%rsi),%r10d
            long past = ((data->main->writecursor - 1) % 0xf);
  4027bb:	8d 50 ff             	lea    -0x1(%rax),%edx
  4027be:	48 63 c2             	movslq %edx,%rax
  4027c1:	41 89 d0             	mov    %edx,%r8d
  4027c4:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  4027cb:	41 c1 f8 1f          	sar    $0x1f,%r8d
  4027cf:	48 c1 e8 20          	shr    $0x20,%rax
  4027d3:	01 d0                	add    %edx,%eax
  4027d5:	c1 f8 03             	sar    $0x3,%eax
  4027d8:	44 29 c0             	sub    %r8d,%eax
  4027db:	41 89 c0             	mov    %eax,%r8d
  4027de:	41 c1 e0 04          	shl    $0x4,%r8d
  4027e2:	41 29 c0             	sub    %eax,%r8d
              past = data->threadsize - 1;
  4027e5:	89 d0                	mov    %edx,%eax
            int rc = data->threads[x].writecursor;
  4027e7:	48 8b 53 30          	mov    0x30(%rbx),%rdx
              past = data->threadsize - 1;
  4027eb:	44 29 c0             	sub    %r8d,%eax
  4027ee:	41 0f 48 c2          	cmovs  %r10d,%eax
            int rc = data->threads[x].writecursor;
  4027f2:	4d 63 d1             	movslq %r9d,%r10
  4027f5:	4c 63 c0             	movslq %eax,%r8
  4027f8:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
  402800:	4c 29 d0             	sub    %r10,%rax
  402803:	48 c1 e0 07          	shl    $0x7,%rax
  402807:	44 8b 9c 02 80 01 00 00 	mov    0x180(%rdx,%rax,1),%r11d
            if (rc < 0) {
  40280f:	45 85 db             	test   %r11d,%r11d
  402812:	0f 88 58 04 00 00    	js     402c70 <threadwork+0xfa0>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402818:	49 63 c3             	movslq %r11d,%rax
  40281b:	45 89 da             	mov    %r11d,%r10d
  40281e:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402825:	41 c1 fa 1f          	sar    $0x1f,%r10d
  402829:	48 c1 e8 20          	shr    $0x20,%rax
  40282d:	44 01 d8             	add    %r11d,%eax
  402830:	c1 f8 03             	sar    $0x3,%eax
  402833:	44 29 d0             	sub    %r10d,%eax
  402836:	41 89 c2             	mov    %eax,%r10d
  402839:	41 c1 e2 04          	shl    $0x4,%r10d
  40283d:	41 29 c2             	sub    %eax,%r10d
  402840:	45 29 d3             	sub    %r10d,%r11d
  402843:	4d 63 db             	movslq %r11d,%r11
                struct Data * thread = &data->threads[data->threadindex];
  402846:	48 63 c1             	movslq %ecx,%rax
            thepoch->time = time; 
  402849:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40284e:	49 c1 e0 10          	shl    $0x10,%r8
                struct Data * thread = &data->threads[data->threadindex];
  402852:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  40285a:	48 29 c5             	sub    %rax,%rbp
  40285d:	48 c1 e5 07          	shl    $0x7,%rbp
  402861:	48 01 d5             	add    %rdx,%rbp
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402864:	48 63 95 24 03 00 00 	movslq 0x324(%rbp),%rdx
  40286b:	48 89 d0             	mov    %rdx,%rax
  40286e:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402872:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402875:	49 c1 e2 04          	shl    $0x4,%r10
  402879:	4c 03 95 18 03 00 00 	add    0x318(%rbp),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402880:	99                   	cltd
            thepoch->time = time; 
  402881:	41 0f 11 52 08       	movups %xmm2,0x8(%r10)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402886:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40288c:	44 89 c8             	mov    %r9d,%eax
  40288f:	c1 e0 18             	shl    $0x18,%eax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402892:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402898:	89 ca                	mov    %ecx,%edx
  40289a:	c1 e2 08             	shl    $0x8,%edx
                thepoch->thread = x;
  40289d:	45 89 0a             	mov    %r9d,(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4028a0:	09 d0                	or     %edx,%eax
          thepoch->set = 1;
  4028a2:	41 c7 42 24 01 00 00 00 	movl   $0x1,0x24(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4028aa:	48 98                	cltq
  4028ac:	4c 09 c0             	or     %r8,%rax
  4028af:	4c 09 d8             	or     %r11,%rax
  4028b2:	49 89 42 18          	mov    %rax,0x18(%r10)
    int x = 2 + ((data->threadindex + y) % data->threadsize - 2);
  4028b6:	8d 41 04             	lea    0x4(%rcx),%eax
  4028b9:	99                   	cltd
  4028ba:	f7 fe                	idiv   %esi
  4028bc:	41 89 d1             	mov    %edx,%r9d
          if (x != data->threadindex) {
  4028bf:	39 d1                	cmp    %edx,%ecx
  4028c1:	0f 84 05 01 00 00    	je     4029cc <threadwork+0xcfc>
            long past = ((data->main->writecursor - 1) % 0xf);
  4028c7:	8b 87 80 01 00 00    	mov    0x180(%rdi),%eax
              past = data->threadsize - 1;
  4028cd:	44 8d 56 ff          	lea    -0x1(%rsi),%r10d
            long past = ((data->main->writecursor - 1) % 0xf);
  4028d1:	8d 50 ff             	lea    -0x1(%rax),%edx
  4028d4:	48 63 c2             	movslq %edx,%rax
  4028d7:	41 89 d0             	mov    %edx,%r8d
  4028da:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  4028e1:	41 c1 f8 1f          	sar    $0x1f,%r8d
  4028e5:	48 c1 e8 20          	shr    $0x20,%rax
  4028e9:	01 d0                	add    %edx,%eax
  4028eb:	c1 f8 03             	sar    $0x3,%eax
  4028ee:	44 29 c0             	sub    %r8d,%eax
  4028f1:	41 89 c0             	mov    %eax,%r8d
  4028f4:	41 c1 e0 04          	shl    $0x4,%r8d
  4028f8:	41 29 c0             	sub    %eax,%r8d
              past = data->threadsize - 1;
  4028fb:	89 d0                	mov    %edx,%eax
            int rc = data->threads[x].writecursor;
  4028fd:	48 8b 53 30          	mov    0x30(%rbx),%rdx
              past = data->threadsize - 1;
  402901:	44 29 c0             	sub    %r8d,%eax
  402904:	41 0f 48 c2          	cmovs  %r10d,%eax
            int rc = data->threads[x].writecursor;
  402908:	4d 63 d1             	movslq %r9d,%r10
  40290b:	4c 63 c0             	movslq %eax,%r8
  40290e:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
  402916:	4c 29 d0             	sub    %r10,%rax
  402919:	48 c1 e0 07          	shl    $0x7,%rax
  40291d:	44 8b 9c 02 80 01 00 00 	mov    0x180(%rdx,%rax,1),%r11d
            if (rc < 0) {
  402925:	45 85 db             	test   %r11d,%r11d
  402928:	0f 88 72 03 00 00    	js     402ca0 <threadwork+0xfd0>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40292e:	49 63 c3             	movslq %r11d,%rax
  402931:	45 89 da             	mov    %r11d,%r10d
  402934:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  40293b:	41 c1 fa 1f          	sar    $0x1f,%r10d
  40293f:	48 c1 e8 20          	shr    $0x20,%rax
  402943:	44 01 d8             	add    %r11d,%eax
  402946:	c1 f8 03             	sar    $0x3,%eax
  402949:	44 29 d0             	sub    %r10d,%eax
  40294c:	41 89 c2             	mov    %eax,%r10d
  40294f:	41 c1 e2 04          	shl    $0x4,%r10d
  402953:	41 29 c2             	sub    %eax,%r10d
  402956:	45 29 d3             	sub    %r10d,%r11d
  402959:	4d 63 db             	movslq %r11d,%r11
                struct Data * thread = &data->threads[data->threadindex];
  40295c:	48 63 c1             	movslq %ecx,%rax
            thepoch->time = time; 
  40295f:	66 0f 6f 1c 24       	movdqa (%rsp),%xmm3
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402964:	49 c1 e0 10          	shl    $0x10,%r8
                struct Data * thread = &data->threads[data->threadindex];
  402968:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  402970:	48 29 c5             	sub    %rax,%rbp
  402973:	48 c1 e5 07          	shl    $0x7,%rbp
  402977:	48 01 d5             	add    %rdx,%rbp
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  40297a:	48 63 95 24 03 00 00 	movslq 0x324(%rbp),%rdx
  402981:	48 89 d0             	mov    %rdx,%rax
  402984:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402988:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  40298b:	49 c1 e2 04          	shl    $0x4,%r10
  40298f:	4c 03 95 18 03 00 00 	add    0x318(%rbp),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402996:	99                   	cltd
            thepoch->time = time; 
  402997:	41 0f 11 5a 08       	movups %xmm3,0x8(%r10)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40299c:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4029a2:	44 89 c8             	mov    %r9d,%eax
  4029a5:	c1 e0 18             	shl    $0x18,%eax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4029a8:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4029ae:	89 ca                	mov    %ecx,%edx
  4029b0:	c1 e2 08             	shl    $0x8,%edx
                thepoch->thread = x;
  4029b3:	45 89 0a             	mov    %r9d,(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4029b6:	09 d0                	or     %edx,%eax
          thepoch->set = 1;
  4029b8:	41 c7 42 24 01 00 00 00 	movl   $0x1,0x24(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4029c0:	48 98                	cltq
  4029c2:	4c 09 c0             	or     %r8,%rax
  4029c5:	4c 09 d8             	or     %r11,%rax
  4029c8:	49 89 42 18          	mov    %rax,0x18(%r10)
    int x = 2 + ((data->threadindex + y) % data->threadsize - 2);
  4029cc:	8d 41 05             	lea    0x5(%rcx),%eax
  4029cf:	99                   	cltd
  4029d0:	f7 fe                	idiv   %esi
  4029d2:	41 89 d1             	mov    %edx,%r9d
          if (x != data->threadindex) {
  4029d5:	39 d1                	cmp    %edx,%ecx
  4029d7:	0f 84 05 01 00 00    	je     402ae2 <threadwork+0xe12>
            long past = ((data->main->writecursor - 1) % 0xf);
  4029dd:	8b 87 80 01 00 00    	mov    0x180(%rdi),%eax
              past = data->threadsize - 1;
  4029e3:	44 8d 56 ff          	lea    -0x1(%rsi),%r10d
            long past = ((data->main->writecursor - 1) % 0xf);
  4029e7:	8d 50 ff             	lea    -0x1(%rax),%edx
  4029ea:	48 63 c2             	movslq %edx,%rax
  4029ed:	41 89 d0             	mov    %edx,%r8d
  4029f0:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  4029f7:	41 c1 f8 1f          	sar    $0x1f,%r8d
  4029fb:	48 c1 e8 20          	shr    $0x20,%rax
  4029ff:	01 d0                	add    %edx,%eax
  402a01:	c1 f8 03             	sar    $0x3,%eax
  402a04:	44 29 c0             	sub    %r8d,%eax
  402a07:	41 89 c0             	mov    %eax,%r8d
  402a0a:	41 c1 e0 04          	shl    $0x4,%r8d
  402a0e:	41 29 c0             	sub    %eax,%r8d
              past = data->threadsize - 1;
  402a11:	89 d0                	mov    %edx,%eax
            int rc = data->threads[x].writecursor;
  402a13:	48 8b 53 30          	mov    0x30(%rbx),%rdx
              past = data->threadsize - 1;
  402a17:	44 29 c0             	sub    %r8d,%eax
  402a1a:	41 0f 48 c2          	cmovs  %r10d,%eax
            int rc = data->threads[x].writecursor;
  402a1e:	4d 63 d1             	movslq %r9d,%r10
  402a21:	4c 63 c0             	movslq %eax,%r8
  402a24:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
  402a2c:	4c 29 d0             	sub    %r10,%rax
  402a2f:	48 c1 e0 07          	shl    $0x7,%rax
  402a33:	44 8b 9c 02 80 01 00 00 	mov    0x180(%rdx,%rax,1),%r11d
            if (rc < 0) {
  402a3b:	45 85 db             	test   %r11d,%r11d
  402a3e:	0f 88 4c 02 00 00    	js     402c90 <threadwork+0xfc0>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402a44:	49 63 c3             	movslq %r11d,%rax
  402a47:	45 89 da             	mov    %r11d,%r10d
  402a4a:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402a51:	41 c1 fa 1f          	sar    $0x1f,%r10d
  402a55:	48 c1 e8 20          	shr    $0x20,%rax
  402a59:	44 01 d8             	add    %r11d,%eax
  402a5c:	c1 f8 03             	sar    $0x3,%eax
  402a5f:	44 29 d0             	sub    %r10d,%eax
  402a62:	41 89 c2             	mov    %eax,%r10d
  402a65:	41 c1 e2 04          	shl    $0x4,%r10d
  402a69:	41 29 c2             	sub    %eax,%r10d
  402a6c:	45 29 d3             	sub    %r10d,%r11d
  402a6f:	4d 63 db             	movslq %r11d,%r11
                struct Data * thread = &data->threads[data->threadindex];
  402a72:	48 63 c1             	movslq %ecx,%rax
            thepoch->time = time; 
  402a75:	66 0f 6f 24 24       	movdqa (%rsp),%xmm4
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402a7a:	49 c1 e0 10          	shl    $0x10,%r8
                struct Data * thread = &data->threads[data->threadindex];
  402a7e:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  402a86:	48 29 c5             	sub    %rax,%rbp
  402a89:	48 c1 e5 07          	shl    $0x7,%rbp
  402a8d:	48 01 d5             	add    %rdx,%rbp
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402a90:	48 63 95 24 03 00 00 	movslq 0x324(%rbp),%rdx
  402a97:	48 89 d0             	mov    %rdx,%rax
  402a9a:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402a9e:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402aa1:	49 c1 e2 04          	shl    $0x4,%r10
  402aa5:	4c 03 95 18 03 00 00 	add    0x318(%rbp),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402aac:	99                   	cltd
            thepoch->time = time; 
  402aad:	41 0f 11 62 08       	movups %xmm4,0x8(%r10)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402ab2:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402ab8:	44 89 c8             	mov    %r9d,%eax
  402abb:	c1 e0 18             	shl    $0x18,%eax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402abe:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402ac4:	89 ca                	mov    %ecx,%edx
  402ac6:	c1 e2 08             	shl    $0x8,%edx
                thepoch->thread = x;
  402ac9:	45 89 0a             	mov    %r9d,(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402acc:	09 d0                	or     %edx,%eax
          thepoch->set = 1;
  402ace:	41 c7 42 24 01 00 00 00 	movl   $0x1,0x24(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402ad6:	48 98                	cltq
  402ad8:	4c 09 c0             	or     %r8,%rax
  402adb:	4c 09 d8             	or     %r11,%rax
  402ade:	49 89 42 18          	mov    %rax,0x18(%r10)
    int x = 2 + ((data->threadindex + y) % data->threadsize - 2);
  402ae2:	8d 41 06             	lea    0x6(%rcx),%eax
  402ae5:	99                   	cltd
  402ae6:	f7 fe                	idiv   %esi
  402ae8:	41 89 d0             	mov    %edx,%r8d
          if (x != data->threadindex) {
  402aeb:	39 ca                	cmp    %ecx,%edx
  402aed:	0f 84 05 01 00 00    	je     402bf8 <threadwork+0xf28>
            long past = ((data->main->writecursor - 1) % 0xf);
  402af3:	8b 87 80 01 00 00    	mov    0x180(%rdi),%eax
              past = data->threadsize - 1;
  402af9:	83 ee 01             	sub    $0x1,%esi
  402afc:	41 bb 0e 00 00 00    	mov    $0xe,%r11d
            long past = ((data->main->writecursor - 1) % 0xf);
  402b02:	8d 50 ff             	lea    -0x1(%rax),%edx
  402b05:	48 63 c2             	movslq %edx,%rax
  402b08:	41 89 d1             	mov    %edx,%r9d
  402b0b:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402b12:	41 c1 f9 1f          	sar    $0x1f,%r9d
  402b16:	48 c1 e8 20          	shr    $0x20,%rax
  402b1a:	01 d0                	add    %edx,%eax
  402b1c:	c1 f8 03             	sar    $0x3,%eax
  402b1f:	44 29 c8             	sub    %r9d,%eax
  402b22:	41 89 c1             	mov    %eax,%r9d
  402b25:	41 c1 e1 04          	shl    $0x4,%r9d
  402b29:	41 29 c1             	sub    %eax,%r9d
              past = data->threadsize - 1;
  402b2c:	89 d0                	mov    %edx,%eax
            int rc = data->threads[x].writecursor;
  402b2e:	48 8b 53 30          	mov    0x30(%rbx),%rdx
              past = data->threadsize - 1;
  402b32:	44 29 c8             	sub    %r9d,%eax
            int rc = data->threads[x].writecursor;
  402b35:	4d 63 c8             	movslq %r8d,%r9
              past = data->threadsize - 1;
  402b38:	0f 48 c6             	cmovs  %esi,%eax
  402b3b:	48 63 f0             	movslq %eax,%rsi
            int rc = data->threads[x].writecursor;
  402b3e:	4a 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%rax
  402b46:	4c 29 c8             	sub    %r9,%rax
  402b49:	48 c1 e0 07          	shl    $0x7,%rax
  402b4d:	44 8b 8c 02 80 01 00 00 	mov    0x180(%rdx,%rax,1),%r9d
            if (rc < 0) {
  402b55:	45 85 c9             	test   %r9d,%r9d
  402b58:	78 2e                	js     402b88 <threadwork+0xeb8>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402b5a:	49 63 c1             	movslq %r9d,%rax
  402b5d:	45 89 ca             	mov    %r9d,%r10d
  402b60:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402b67:	41 c1 fa 1f          	sar    $0x1f,%r10d
  402b6b:	48 c1 e8 20          	shr    $0x20,%rax
  402b6f:	44 01 c8             	add    %r9d,%eax
  402b72:	c1 f8 03             	sar    $0x3,%eax
  402b75:	44 29 d0             	sub    %r10d,%eax
  402b78:	41 89 c2             	mov    %eax,%r10d
  402b7b:	41 c1 e2 04          	shl    $0x4,%r10d
  402b7f:	41 29 c2             	sub    %eax,%r10d
  402b82:	45 29 d1             	sub    %r10d,%r9d
  402b85:	4d 63 d9             	movslq %r9d,%r11
                struct Data * thread = &data->threads[data->threadindex];
  402b88:	48 63 c1             	movslq %ecx,%rax
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402b8b:	c1 e1 08             	shl    $0x8,%ecx
            thepoch->time = time; 
  402b8e:	66 0f 6f 2c 24       	movdqa (%rsp),%xmm5
                struct Data * thread = &data->threads[data->threadindex];
  402b93:	4c 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%r9
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402b9b:	48 c1 e6 10          	shl    $0x10,%rsi
                struct Data * thread = &data->threads[data->threadindex];
  402b9f:	49 29 c1             	sub    %rax,%r9
  402ba2:	49 c1 e1 07          	shl    $0x7,%r9
  402ba6:	49 01 d1             	add    %rdx,%r9
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402ba9:	49 63 91 24 03 00 00 	movslq 0x324(%r9),%rdx
  402bb0:	48 89 d0             	mov    %rdx,%rax
  402bb3:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402bb7:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402bba:	49 c1 e2 04          	shl    $0x4,%r10
  402bbe:	4d 03 91 18 03 00 00 	add    0x318(%r9),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402bc5:	99                   	cltd
            thepoch->time = time; 
  402bc6:	41 0f 11 6a 08       	movups %xmm5,0x8(%r10)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402bcb:	41 f7 b9 20 03 00 00 	idivl  0x320(%r9)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402bd2:	44 89 c0             	mov    %r8d,%eax
  402bd5:	c1 e0 18             	shl    $0x18,%eax
  402bd8:	09 c8                	or     %ecx,%eax
  402bda:	48 98                	cltq
  402bdc:	48 09 f0             	or     %rsi,%rax
  402bdf:	4c 09 d8             	or     %r11,%rax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402be2:	41 89 91 24 03 00 00 	mov    %edx,0x324(%r9)
                thepoch->thread = x;
  402be9:	45 89 02             	mov    %r8d,(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402bec:	49 89 42 18          	mov    %rax,0x18(%r10)
          thepoch->set = 1;
  402bf0:	41 c7 42 24 01 00 00 00 	movl   $0x1,0x24(%r10)
     data->readcursor = (data->readcursor + 1) % 0xf;
  402bf8:	8b 83 00 02 00 00    	mov    0x200(%rbx),%eax
  402bfe:	8d 50 01             	lea    0x1(%rax),%edx
  402c01:	48 63 c2             	movslq %edx,%rax
  402c04:	89 d1                	mov    %edx,%ecx
  402c06:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402c0d:	c1 f9 1f             	sar    $0x1f,%ecx
  402c10:	48 c1 e8 20          	shr    $0x20,%rax
  402c14:	01 d0                	add    %edx,%eax
  402c16:	c1 f8 03             	sar    $0x3,%eax
  402c19:	29 c8                	sub    %ecx,%eax
  402c1b:	89 c1                	mov    %eax,%ecx
  402c1d:	c1 e1 04             	shl    $0x4,%ecx
  402c20:	29 c1                	sub    %eax,%ecx
  402c22:	29 ca                	sub    %ecx,%edx
  402c24:	89 93 00 02 00 00    	mov    %edx,0x200(%rbx)
    __atomic_fetch_add(&data->main->globalread, 1, __ATOMIC_RELAXED);
  402c2a:	f0 48 83 87 48 03 00 00 01 	lock addq $0x1,0x348(%rdi)
}
  402c33:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  402c38:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  402c41:	75 68                	jne    402cab <threadwork+0xfdb>
  402c43:	48 83 c4 28          	add    $0x28,%rsp
  402c47:	31 c0                	xor    %eax,%eax
  402c49:	5b                   	pop    %rbx
  402c4a:	5d                   	pop    %rbp
  402c4b:	c3                   	ret
  402c4c:	0f 1f 40 00          	nopl   0x0(%rax)
            if (rc < 0) {
  402c50:	41 bb 0e 00 00 00    	mov    $0xe,%r11d
  402c56:	e9 bf f9 ff ff       	jmp    40261a <threadwork+0x94a>
  402c5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  402c60:	41 bb 0e 00 00 00    	mov    $0xe,%r11d
  402c66:	e9 9a f8 ff ff       	jmp    402505 <threadwork+0x835>
  402c6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  402c70:	41 bb 0e 00 00 00    	mov    $0xe,%r11d
  402c76:	e9 cb fb ff ff       	jmp    402846 <threadwork+0xb76>
  402c7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  402c80:	41 bb 0e 00 00 00    	mov    $0xe,%r11d
  402c86:	e9 a5 fa ff ff       	jmp    402730 <threadwork+0xa60>
  402c8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  402c90:	41 bb 0e 00 00 00    	mov    $0xe,%r11d
  402c96:	e9 d7 fd ff ff       	jmp    402a72 <threadwork+0xda2>
  402c9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  402ca0:	41 bb 0e 00 00 00    	mov    $0xe,%r11d
  402ca6:	e9 b1 fc ff ff       	jmp    40295c <threadwork+0xc8c>
}
  402cab:	e8 b0 e3 ff ff       	call   401060 <__stack_chk_fail@plt>

0000000000402cb0 <work>:
void * work(void * arg) {
  402cb0:	41 56                	push   %r14
  402cb2:	48 8d 35 4b 03 00 00 	lea    0x34b(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  402cb9:	31 c0                	xor    %eax,%eax
  402cbb:	41 55                	push   %r13
  402cbd:	41 54                	push   %r12
  402cbf:	55                   	push   %rbp
  402cc0:	53                   	push   %rbx
  402cc1:	8b 57 64             	mov    0x64(%rdi),%edx
  402cc4:	48 89 fb             	mov    %rdi,%rbx
  402cc7:	bf 01 00 00 00       	mov    $0x1,%edi
  402ccc:	e8 bf e3 ff ff       	call   401090 <__printf_chk@plt>
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  402cd1:	48 8b 83 b8 00 00 00 	mov    0xb8(%rbx),%rax
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  402cd8:	4c 63 6b 68          	movslq 0x68(%rbx),%r13
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  402cdc:	be 08 00 00 00       	mov    $0x8,%esi
  402ce1:	48 8d 78 01          	lea    0x1(%rax),%rdi
  402ce5:	e8 96 e3 ff ff       	call   401080 <calloc@plt>
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  402cea:	be 04 00 00 00       	mov    $0x4,%esi
  402cef:	4c 89 ef             	mov    %r13,%rdi
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  402cf2:	48 89 c5             	mov    %rax,%rbp
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  402cf5:	e8 86 e3 ff ff       	call   401080 <calloc@plt>
  int * readywriters = calloc(data->threadsize, sizeof(int));
  402cfa:	be 04 00 00 00       	mov    $0x4,%esi
  402cff:	4c 89 ef             	mov    %r13,%rdi
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  402d02:	49 89 c4             	mov    %rax,%r12
  int * readywriters = calloc(data->threadsize, sizeof(int));
  402d05:	e8 76 e3 ff ff       	call   401080 <calloc@plt>
  while (data->running == 1) {
  402d0a:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  402d0e:	75 5f                	jne    402d6f <work+0xbf>
  402d10:	49 89 c5             	mov    %rax,%r13
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  402d13:	4c 8d b3 28 01 00 00 	lea    0x128(%rbx),%r14
  402d1a:	eb 17                	jmp    402d33 <work+0x83>
  402d1c:	0f 1f 40 00          	nopl   0x0(%rax)
    } else if (data->threadindex == 1) {
  402d20:	83 f8 01             	cmp    $0x1,%eax
  402d23:	74 6b                	je     402d90 <work+0xe0>
      threadwork(data);
  402d25:	48 89 df             	mov    %rbx,%rdi
  402d28:	e8 a3 ef ff ff       	call   401cd0 <threadwork>
  while (data->running == 1) {
  402d2d:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  402d31:	75 3c                	jne    402d6f <work+0xbf>
   if (data->threadindex == 0) {
  402d33:	8b 43 64             	mov    0x64(%rbx),%eax
  402d36:	85 c0                	test   %eax,%eax
  402d38:	75 e6                	jne    402d20 <work+0x70>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  402d3a:	4c 89 f6             	mov    %r14,%rsi
  402d3d:	bf 04 00 00 00       	mov    $0x4,%edi
  402d42:	e8 09 e3 ff ff       	call   401050 <clock_gettime@plt>
      singlewriter2(data, available, readyreaders, readywriters);
  402d47:	4c 89 e9             	mov    %r13,%rcx
  402d4a:	4c 89 e2             	mov    %r12,%rdx
  402d4d:	48 89 ee             	mov    %rbp,%rsi
  402d50:	48 89 df             	mov    %rbx,%rdi
  402d53:	e8 b8 ec ff ff       	call   401a10 <singlewriter2>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swend);
  402d58:	48 8d b3 38 01 00 00 	lea    0x138(%rbx),%rsi
  402d5f:	bf 04 00 00 00       	mov    $0x4,%edi
  402d64:	e8 e7 e2 ff ff       	call   401050 <clock_gettime@plt>
  while (data->running == 1) {
  402d69:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  402d6d:	74 c4                	je     402d33 <work+0x83>
  402d6f:	8b 53 64             	mov    0x64(%rbx),%edx
  402d72:	48 8d 35 9e 02 00 00 	lea    0x29e(%rip),%rsi        # 403017 <_IO_stdin_used+0x17>
  402d79:	bf 01 00 00 00       	mov    $0x1,%edi
  402d7e:	31 c0                	xor    %eax,%eax
  402d80:	e8 0b e3 ff ff       	call   401090 <__printf_chk@plt>
}
  402d85:	5b                   	pop    %rbx
  402d86:	5d                   	pop    %rbp
  402d87:	41 5c                	pop    %r12
  402d89:	41 5d                	pop    %r13
  402d8b:	41 5e                	pop    %r14
  402d8d:	c3                   	ret
  402d8e:	66 90                	xchg   %ax,%ax
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  402d90:	4c 89 f6             	mov    %r14,%rsi
  402d93:	bf 04 00 00 00       	mov    $0x4,%edi
  402d98:	e8 b3 e2 ff ff       	call   401050 <clock_gettime@plt>
      singlewriter3(data, available, readyreaders, readywriters);
  402d9d:	48 89 ee             	mov    %rbp,%rsi
  402da0:	48 89 df             	mov    %rbx,%rdi
  402da3:	4c 89 e9             	mov    %r13,%rcx
  402da6:	4c 89 e2             	mov    %r12,%rdx
  402da9:	e8 32 ec ff ff       	call   4019e0 <singlewriter3>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swend);
  402dae:	48 8d b3 38 01 00 00 	lea    0x138(%rbx),%rsi
  402db5:	bf 04 00 00 00       	mov    $0x4,%edi
  402dba:	e8 91 e2 ff ff       	call   401050 <clock_gettime@plt>
  402dbf:	e9 69 ff ff ff       	jmp    402d2d <work+0x7d>
  402dc4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  402dcf:	90                   	nop

0000000000402dd0 <work2>:
  while (data->running == 1) {
  402dd0:	eb 0b                	jmp    402ddd <work2+0xd>
  402dd2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  402dd8:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  402ddd:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  402de1:	74 f5                	je     402dd8 <work2+0x8>
}
  402de3:	c3                   	ret

Disassembly of section .fini:

0000000000402de4 <_fini>:
  402de4:	f3 0f 1e fa          	endbr64
  402de8:	48 83 ec 08          	sub    $0x8,%rsp
  402dec:	48 83 c4 08          	add    $0x8,%rsp
  402df0:	c3                   	ret
