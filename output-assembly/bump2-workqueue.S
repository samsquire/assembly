
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
  40112d:	ba 08 00 00 00       	mov    $0x8,%edx
  401132:	48 8d 35 0f 1f 00 00 	lea    0x1f0f(%rip),%rsi        # 403048 <_IO_stdin_used+0x48>
  401139:	31 c0                	xor    %eax,%eax
  40113b:	bf 01 00 00 00       	mov    $0x1,%edi
  401140:	e8 4b ff ff ff       	call   401090 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401145:	be 08 00 00 00       	mov    $0x8,%esi
  40114a:	bf 08 00 00 00       	mov    $0x8,%edi
  40114f:	e8 2c ff ff ff       	call   401080 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401154:	be 38 00 00 00       	mov    $0x38,%esi
  401159:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40115e:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401163:	e8 18 ff ff ff       	call   401080 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401168:	be 00 1c 00 00       	mov    $0x1c00,%esi
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
  4011c2:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
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
  4011ec:	bf 08 00 00 00       	mov    $0x8,%edi
  4011f1:	e8 8a fe ff ff       	call   401080 <calloc@plt>
  4011f6:	66 48 0f 6e f3       	movq   %rbx,%xmm6
  data[0].works = works;
  4011fb:	4c 89 63 70          	mov    %r12,0x70(%rbx)
  4011ff:	45 31 e4             	xor    %r12d,%r12d
  401202:	66 48 0f 6e e8       	movq   %rax,%xmm5
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  401207:	48 89 c5             	mov    %rax,%rbp
  40120a:	66 0f 6c ee          	punpcklqdq %xmm6,%xmm5
  40120e:	0f 29 2c 24          	movaps %xmm5,(%rsp)
  for (int x = 0; x < threadsize ; x++) {
  401212:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
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
  401264:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
    data[x].running = 1;
  401269:	48 8b 05 68 1f 00 00 	mov    0x1f68(%rip),%rax        # 4031d8 <_IO_stdin_used+0x1d8>
    data[x].bucketstart = x * buckets ;
  401270:	45 89 a6 18 fd ff ff 	mov    %r12d,-0x2e8(%r14)
    data[x].readies[x] = 0;
    data[x].buckets = buckets;
    data[x].main = &data[0];
    data[x].threads = data;
    
    data[x].read = 0;
  401277:	66 0f 6f 15 71 1f 00 00 	movdqa 0x1f71(%rip),%xmm2        # 4031f0 <_IO_stdin_used+0x1f0>
    data[x].newmask = 0;
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40127f:	be 30 00 00 00       	mov    $0x30,%esi
    data[x].chunkslen = chunkslen;
  401284:	66 0f 6f 1d 74 1f 00 00 	movdqa 0x1f74(%rip),%xmm3        # 403200 <_IO_stdin_used+0x200>
    data[x].loglevel = debug;
  40128c:	41 c7 86 00 fd ff ff 00 00 00 00 	movl   $0x0,-0x300(%r14)
    data[x].running = 1;
  401297:	49 89 86 dc fc ff ff 	mov    %rax,-0x324(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40129e:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].buckets = buckets;
  4012a3:	48 8b 05 36 1f 00 00 	mov    0x1f36(%rip),%rax        # 4031e0 <_IO_stdin_used+0x1e0>
  for (int x = 0; x < threadsize ; x++) {
  4012aa:	41 81 c4 ff ff ff 1f 	add    $0x1fffffff,%r12d
    data[x].prevread = threadsize;
  4012b1:	66 0f 6f 25 57 1f 00 00 	movdqa 0x1f57(%rip),%xmm4        # 403210 <_IO_stdin_used+0x210>
    data[x].threadindex = x;
  4012b9:	45 89 be e4 fc ff ff 	mov    %r15d,-0x31c(%r14)
    data[x].buckets = buckets;
  4012c0:	49 89 86 10 fd ff ff 	mov    %rax,-0x2f0(%r14)
    data[x].freelist = freelist;
  4012c7:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    data[x].threadsize = threadsize;
  4012cc:	41 c7 86 e8 fc ff ff 08 00 00 00 	movl   $0x8,-0x318(%r14)
    data[x].readies[x] = 0;
  4012d7:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
    data[x].threads = data;
  4012de:	49 89 9e b0 fc ff ff 	mov    %rbx,-0x350(%r14)
    data[x].readcursor = threadsize - 1;
  4012e5:	41 c7 86 80 fe ff ff 07 00 00 00 	movl   $0x7,-0x180(%r14)
    data[x].writecursor = threadsize - 1;
  4012f0:	41 c7 86 00 fe ff ff 07 00 00 00 	movl   $0x7,-0x200(%r14)
    data[x].freelist = freelist;
  4012fb:	49 89 86 20 fd ff ff 	mov    %rax,-0x2e0(%r14)
    data[x].newmask = 0;
  401302:	41 c7 86 48 fd ff ff 00 00 00 00 	movl   $0x0,-0x2b8(%r14)
    data[x].thiswrite = threadsize;
  40130d:	41 c7 46 a8 08 00 00 00 	movl   $0x8,-0x58(%r14)
    data[x].readies = readies;
  401315:	41 0f 29 8e a0 fc ff ff 	movaps %xmm1,-0x360(%r14)
    data[x].read = 0;
  40131d:	41 0f 29 96 80 fc ff ff 	movaps %xmm2,-0x380(%r14)
    data[x].chunkslen = chunkslen;
  401325:	41 0f 11 9e 38 fd ff ff 	movups %xmm3,-0x2c8(%r14)
    data[x].prevread = threadsize;
  40132d:	41 0f 11 66 88       	movups %xmm4,-0x78(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401332:	e8 49 fd ff ff       	call   401080 <calloc@plt>
    data[x].epochssize = epochs;
    
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  401337:	be 30 00 00 00       	mov    $0x30,%esi
  40133c:	bf 10 27 00 00       	mov    $0x2710,%edi
    data[x].epochssize = epochs;
  401341:	41 c7 46 a0 80 96 98 00 	movl   $0x989680,-0x60(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401349:	49 89 46 98          	mov    %rax,-0x68(%r14)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  40134d:	e8 2e fd ff ff       	call   401080 <calloc@plt>
  401352:	49 89 46 b0          	mov    %rax,-0x50(%r14)
  for (int x = 0; x < threadsize ; x++) {
  401356:	41 83 fd 08          	cmp    $0x8,%r13d
  40135a:	0f 85 b8 fe ff ff    	jne    401218 <main+0x158>
  401360:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
  401365:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
  40136a:	48 89 1c 24          	mov    %rbx,(%rsp)
  40136e:	49 c7 c5 e0 23 40 00 	mov    $0x4023e0,%r13
  401375:	48 8d 85 c0 01 00 00 	lea    0x1c0(%rbp),%rax
  40137c:	4d 89 fc             	mov    %r15,%r12
  40137f:	49 89 c6             	mov    %rax,%r14
  401382:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
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
  4013be:	48 8b 1c 24          	mov    (%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  4013c2:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  4013c7:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec time = {
  4013cc:	66 0f 6f 05 4c 1e 00 00 	movdqa 0x1e4c(%rip),%xmm0        # 403220 <_IO_stdin_used+0x220>
  4013d4:	4c 8d 6c 24 38       	lea    0x38(%rsp),%r13
  4013d9:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  4013de:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4013e2:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  4013e7:	e8 84 fc ff ff       	call   401070 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  4013ec:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
  4013f1:	c7 43 5c 00 00 00 00 	movl   $0x0,0x5c(%rbx)
  4013f8:	c7 83 dc 03 00 00 00 00 00 00 	movl   $0x0,0x3dc(%rbx)
  401402:	c7 83 5c 07 00 00 00 00 00 00 	movl   $0x0,0x75c(%rbx)
  40140c:	48 83 c5 40          	add    $0x40,%rbp
  401410:	c7 83 dc 0a 00 00 00 00 00 00 	movl   $0x0,0xadc(%rbx)
  40141a:	c7 83 5c 0e 00 00 00 00 00 00 	movl   $0x0,0xe5c(%rbx)
  401424:	c7 83 dc 11 00 00 00 00 00 00 	movl   $0x0,0x11dc(%rbx)
  40142e:	c7 83 5c 15 00 00 00 00 00 00 	movl   $0x0,0x155c(%rbx)
  401438:	c7 83 dc 18 00 00 00 00 00 00 	movl   $0x0,0x18dc(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  401442:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401448:	49 8b 3c 24          	mov    (%r12),%rdi
  40144c:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  40144f:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  401453:	e8 58 fc ff ff       	call   4010b0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401458:	49 39 ec             	cmp    %rbp,%r12
  40145b:	75 eb                	jne    401448 <main+0x388>
  40145d:	48 8d 3d 21 1c 00 00 	lea    0x1c21(%rip),%rdi        # 403085 <_IO_stdin_used+0x85>
  401464:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  401468:	45 31 e4             	xor    %r12d,%r12d
  40146b:	e8 d0 fb ff ff       	call   401040 <puts@plt>
  for (int x = 0; x < threadsize; x++) {
  401470:	4c 8d b3 48 1c 00 00 	lea    0x1c48(%rbx),%r14
  401477:	4c 8d 2d 1c 1c 00 00 	lea    0x1c1c(%rip),%r13        # 40309a <_IO_stdin_used+0x9a>
  40147e:	66 90                	xchg   %ax,%ax
  401480:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401484:	4c 89 ee             	mov    %r13,%rsi
  401487:	bf 01 00 00 00       	mov    $0x1,%edi
  40148c:	31 c0                	xor    %eax,%eax
  40148e:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
  401495:	e8 f6 fb ff ff       	call   401090 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  40149a:	4c 03 a5 80 fc ff ff 	add    -0x380(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  4014a1:	4c 39 f5             	cmp    %r14,%rbp
  4014a4:	75 da                	jne    401480 <main+0x3c0>
  }
  printf("freq: %ld\n", freq/ seconds);
  4014a6:	4c 89 e0             	mov    %r12,%rax
  4014a9:	48 8d 35 f5 1b 00 00 	lea    0x1bf5(%rip),%rsi        # 4030a5 <_IO_stdin_used+0xa5>
  4014b0:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
  4014ba:	bf 01 00 00 00       	mov    $0x1,%edi
  4014bf:	48 f7 ed             	imul   %rbp
  4014c2:	4c 89 e0             	mov    %r12,%rax
  4014c5:	4c 8d b3 50 1c 00 00 	lea    0x1c50(%rbx),%r14
  4014cc:	48 c1 f8 3f          	sar    $0x3f,%rax
  4014d0:	48 d1 fa             	sar    %rdx
  4014d3:	48 29 c2             	sub    %rax,%rdx
  4014d6:	31 c0                	xor    %eax,%eax
  4014d8:	49 89 d5             	mov    %rdx,%r13
  4014db:	e8 b0 fb ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_ps: %ld\n", (freq*threadsize-1)/ seconds);
  4014e0:	4a 8d 0c e5 ff ff ff ff 	lea    -0x1(,%r12,8),%rcx
  4014e8:	bf 01 00 00 00       	mov    $0x1,%edi
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  4014ed:	41 bc 00 ca 9a 3b    	mov    $0x3b9aca00,%r12d
  printf("freq_ps: %ld\n", (freq*threadsize-1)/ seconds);
  4014f3:	48 89 c8             	mov    %rcx,%rax
  4014f6:	48 c1 f9 3f          	sar    $0x3f,%rcx
  4014fa:	48 8d 35 af 1b 00 00 	lea    0x1baf(%rip),%rsi        # 4030b0 <_IO_stdin_used+0xb0>
  401501:	48 f7 ed             	imul   %rbp
  401504:	31 c0                	xor    %eax,%eax
  401506:	48 89 d5             	mov    %rdx,%rbp
  401509:	48 d1 fd             	sar    %rbp
  40150c:	48 29 cd             	sub    %rcx,%rbp
  40150f:	48 89 ea             	mov    %rbp,%rdx
  401512:	e8 79 fb ff ff       	call   401090 <__printf_chk@plt>
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  401517:	4c 89 e0             	mov    %r12,%rax
  40151a:	bf 01 00 00 00       	mov    $0x1,%edi
  40151f:	48 8d 35 98 1b 00 00 	lea    0x1b98(%rip),%rsi        # 4030be <_IO_stdin_used+0xbe>
  401526:	48 99                	cqto
  401528:	49 f7 fd             	idiv   %r13
  40152b:	49 89 c5             	mov    %rax,%r13
  40152e:	48 89 c2             	mov    %rax,%rdx
  401531:	31 c0                	xor    %eax,%eax
  401533:	e8 58 fb ff ff       	call   401090 <__printf_chk@plt>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/threadsize));
  401538:	4d 85 ed             	test   %r13,%r13
  40153b:	49 8d 55 07          	lea    0x7(%r13),%rdx
  40153f:	48 8d 35 8c 1b 00 00 	lea    0x1b8c(%rip),%rsi        # 4030d2 <_IO_stdin_used+0xd2>
  401546:	49 0f 49 d5          	cmovns %r13,%rdx
  40154a:	bf 01 00 00 00       	mov    $0x1,%edi
  40154f:	31 c0                	xor    %eax,%eax
  401551:	4c 8d 2d ab 1b 00 00 	lea    0x1bab(%rip),%r13        # 403103 <_IO_stdin_used+0x103>
  401558:	48 c1 fa 03          	sar    $0x3,%rdx
  40155c:	e8 2f fb ff ff       	call   401090 <__printf_chk@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*threadsize-1)/seconds));
  401561:	4c 89 e0             	mov    %r12,%rax
  401564:	bf 01 00 00 00       	mov    $0x1,%edi
  long freq_writes = 0;
  401569:	45 31 e4             	xor    %r12d,%r12d
  printf("freq latency: %ld\n", 1000000000/((freq*threadsize-1)/seconds));
  40156c:	48 99                	cqto
  40156e:	48 8d 35 7b 1b 00 00 	lea    0x1b7b(%rip),%rsi        # 4030f0 <_IO_stdin_used+0xf0>
  401575:	48 f7 fd             	idiv   %rbp
  401578:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  40157c:	48 89 c2             	mov    %rax,%rdx
  40157f:	31 c0                	xor    %eax,%eax
  401581:	e8 0a fb ff ff       	call   401090 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  401586:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    freq_writes += data[x].freq_writes;
  401590:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401594:	4c 89 ee             	mov    %r13,%rsi
  401597:	bf 01 00 00 00       	mov    $0x1,%edi
  40159c:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  40159e:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
    freq_writes += data[x].freq_writes;
  4015a5:	49 01 d4             	add    %rdx,%r12
  4015a8:	e8 e3 fa ff ff       	call   401090 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  4015ad:	49 39 ee             	cmp    %rbp,%r14
  4015b0:	75 de                	jne    401590 <main+0x4d0>
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  4015b2:	4c 89 e0             	mov    %r12,%rax
  4015b5:	48 8d 35 53 1b 00 00 	lea    0x1b53(%rip),%rsi        # 40310f <_IO_stdin_used+0x10f>
  4015bc:	bf 01 00 00 00       	mov    $0x1,%edi
  4015c1:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
  4015cb:	48 f7 ed             	imul   %rbp
  4015ce:	4c 89 e0             	mov    %r12,%rax
  4015d1:	48 c1 f8 3f          	sar    $0x3f,%rax
  4015d5:	48 d1 fa             	sar    %rdx
  4015d8:	48 29 c2             	sub    %rax,%rdx
  4015db:	31 c0                	xor    %eax,%eax
  4015dd:	49 89 d5             	mov    %rdx,%r13
  4015e0:	e8 ab fa ff ff       	call   401090 <__printf_chk@plt>

  printf("freq_writes_total: %ld\n", (freq_writes * threadsize - 2) / seconds);
  4015e5:	4a 8d 0c e5 fe ff ff ff 	lea    -0x2(,%r12,8),%rcx
  4015ed:	bf 01 00 00 00       	mov    $0x1,%edi
  4015f2:	48 8d 35 28 1b 00 00 	lea    0x1b28(%rip),%rsi        # 403121 <_IO_stdin_used+0x121>
  4015f9:	48 89 c8             	mov    %rcx,%rax
  4015fc:	48 c1 f9 3f          	sar    $0x3f,%rcx
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  401600:	41 bc 00 ca 9a 3b    	mov    $0x3b9aca00,%r12d
  printf("freq_writes_total: %ld\n", (freq_writes * threadsize - 2) / seconds);
  401606:	48 f7 ed             	imul   %rbp
  401609:	31 c0                	xor    %eax,%eax
  40160b:	48 89 d5             	mov    %rdx,%rbp
  40160e:	48 d1 fd             	sar    %rbp
  401611:	48 29 cd             	sub    %rcx,%rbp
  401614:	48 89 ea             	mov    %rbp,%rdx
  401617:	e8 74 fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  40161c:	4c 89 e0             	mov    %r12,%rax
  40161f:	bf 01 00 00 00       	mov    $0x1,%edi
  401624:	48 8d 35 0e 1b 00 00 	lea    0x1b0e(%rip),%rsi        # 403139 <_IO_stdin_used+0x139>
  40162b:	48 99                	cqto
  40162d:	49 f7 fd             	idiv   %r13
  401630:	49 89 c5             	mov    %rax,%r13
  401633:	48 89 c2             	mov    %rax,%rdx
  401636:	31 c0                	xor    %eax,%eax
  401638:	e8 53 fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes per thread latency: %ld\n", (1000000000/(freq_writes / seconds)) / threadsize);
  40163d:	4d 85 ed             	test   %r13,%r13
  401640:	49 8d 55 07          	lea    0x7(%r13),%rdx
  401644:	48 8d 35 5d 1b 00 00 	lea    0x1b5d(%rip),%rsi        # 4031a8 <_IO_stdin_used+0x1a8>
  40164b:	49 0f 49 d5          	cmovns %r13,%rdx
  40164f:	bf 01 00 00 00       	mov    $0x1,%edi
  401654:	31 c0                	xor    %eax,%eax
  401656:	48 c1 fa 03          	sar    $0x3,%rdx
  40165a:	e8 31 fa ff ff       	call   401090 <__printf_chk@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * threadsize - 2) / seconds));
  40165f:	4c 89 e0             	mov    %r12,%rax
  401662:	bf 01 00 00 00       	mov    $0x1,%edi
  401667:	48 8d 35 e6 1a 00 00 	lea    0x1ae6(%rip),%rsi        # 403154 <_IO_stdin_used+0x154>
  40166e:	48 99                	cqto
  401670:	48 f7 fd             	idiv   %rbp
  401673:	48 8d 2d 53 1a 00 00 	lea    0x1a53(%rip),%rbp        # 4030cd <_IO_stdin_used+0xcd>
  40167a:	48 89 c2             	mov    %rax,%rdx
  40167d:	31 c0                	xor    %eax,%eax
  40167f:	e8 0c fa ff ff       	call   401090 <__printf_chk@plt>
  401684:	48 8d 3d e3 1a 00 00 	lea    0x1ae3(%rip),%rdi        # 40316e <_IO_stdin_used+0x16e>
  40168b:	e8 b0 f9 ff ff       	call   401040 <puts@plt>
  401690:	48 89 ee             	mov    %rbp,%rsi
  401693:	bf 01 00 00 00       	mov    $0x1,%edi
  401698:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  40169a:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  4016a1:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4016a8:	e8 e3 f9 ff ff       	call   401090 <__printf_chk@plt>
  4016ad:	48 89 ee             	mov    %rbp,%rsi
  4016b0:	bf 01 00 00 00       	mov    $0x1,%edi
  4016b5:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  4016b7:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  4016be:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4016c5:	e8 c6 f9 ff ff       	call   401090 <__printf_chk@plt>
  4016ca:	48 89 ee             	mov    %rbp,%rsi
  4016cd:	bf 01 00 00 00       	mov    $0x1,%edi
  4016d2:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  4016d4:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  4016db:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  4016e2:	e8 a9 f9 ff ff       	call   401090 <__printf_chk@plt>
  4016e7:	48 89 ee             	mov    %rbp,%rsi
  4016ea:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ef:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4016f1:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  4016f8:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  4016ff:	e8 8c f9 ff ff       	call   401090 <__printf_chk@plt>
  401704:	48 89 ee             	mov    %rbp,%rsi
  401707:	bf 01 00 00 00       	mov    $0x1,%edi
  40170c:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  40170e:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401715:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  40171c:	e8 6f f9 ff ff       	call   401090 <__printf_chk@plt>
  401721:	48 89 ee             	mov    %rbp,%rsi
  401724:	bf 01 00 00 00       	mov    $0x1,%edi
  401729:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  40172b:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401732:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401739:	e8 52 f9 ff ff       	call   401090 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  40173e:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  401745:	31 c0                	xor    %eax,%eax
  401747:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  40174e:	48 8d 35 26 1a 00 00 	lea    0x1a26(%rip),%rsi        # 40317b <_IO_stdin_used+0x17b>
  401755:	bf 01 00 00 00       	mov    $0x1,%edi
  40175a:	e8 31 f9 ff ff       	call   401090 <__printf_chk@plt>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  40175f:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  401764:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40176d:	75 11                	jne    401780 <main+0x6c0>
  40176f:	48 83 c4 78          	add    $0x78,%rsp
  401773:	31 c0                	xor    %eax,%eax
  401775:	5b                   	pop    %rbx
  401776:	5d                   	pop    %rbp
  401777:	41 5c                	pop    %r12
  401779:	41 5d                	pop    %r13
  40177b:	41 5e                	pop    %r14
  40177d:	41 5f                	pop    %r15
  40177f:	c3                   	ret
  401780:	e8 db f8 ff ff       	call   401060 <__stack_chk_fail@plt>
  401785:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40178f:	90                   	nop

0000000000401790 <_start>:
  401790:	f3 0f 1e fa          	endbr64
  401794:	31 ed                	xor    %ebp,%ebp
  401796:	49 89 d1             	mov    %rdx,%r9
  401799:	5e                   	pop    %rsi
  40179a:	48 89 e2             	mov    %rsp,%rdx
  40179d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4017a1:	50                   	push   %rax
  4017a2:	54                   	push   %rsp
  4017a3:	45 31 c0             	xor    %r8d,%r8d
  4017a6:	31 c9                	xor    %ecx,%ecx
  4017a8:	48 c7 c7 c0 10 40 00 	mov    $0x4010c0,%rdi
  4017af:	ff 15 3b 38 00 00    	call   *0x383b(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  4017b5:	f4                   	hlt
  4017b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004017c0 <_dl_relocate_static_pie>:
  4017c0:	f3 0f 1e fa          	endbr64
  4017c4:	c3                   	ret
  4017c5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4017cf:	90                   	nop

00000000004017d0 <deregister_tm_clones>:
  4017d0:	b8 10 50 40 00       	mov    $0x405010,%eax
  4017d5:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  4017db:	74 13                	je     4017f0 <deregister_tm_clones+0x20>
  4017dd:	b8 00 00 00 00       	mov    $0x0,%eax
  4017e2:	48 85 c0             	test   %rax,%rax
  4017e5:	74 09                	je     4017f0 <deregister_tm_clones+0x20>
  4017e7:	bf 10 50 40 00       	mov    $0x405010,%edi
  4017ec:	ff e0                	jmp    *%rax
  4017ee:	66 90                	xchg   %ax,%ax
  4017f0:	c3                   	ret
  4017f1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4017fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401800 <register_tm_clones>:
  401800:	be 10 50 40 00       	mov    $0x405010,%esi
  401805:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  40180c:	48 89 f0             	mov    %rsi,%rax
  40180f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401813:	48 c1 f8 03          	sar    $0x3,%rax
  401817:	48 01 c6             	add    %rax,%rsi
  40181a:	48 d1 fe             	sar    %rsi
  40181d:	74 11                	je     401830 <register_tm_clones+0x30>
  40181f:	b8 00 00 00 00       	mov    $0x0,%eax
  401824:	48 85 c0             	test   %rax,%rax
  401827:	74 07                	je     401830 <register_tm_clones+0x30>
  401829:	bf 10 50 40 00       	mov    $0x405010,%edi
  40182e:	ff e0                	jmp    *%rax
  401830:	c3                   	ret
  401831:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40183c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401840 <__do_global_dtors_aux>:
  401840:	f3 0f 1e fa          	endbr64
  401844:	80 3d c5 37 00 00 00 	cmpb   $0x0,0x37c5(%rip)        # 405010 <__TMC_END__>
  40184b:	75 13                	jne    401860 <__do_global_dtors_aux+0x20>
  40184d:	55                   	push   %rbp
  40184e:	48 89 e5             	mov    %rsp,%rbp
  401851:	e8 7a ff ff ff       	call   4017d0 <deregister_tm_clones>
  401856:	c6 05 b3 37 00 00 01 	movb   $0x1,0x37b3(%rip)        # 405010 <__TMC_END__>
  40185d:	5d                   	pop    %rbp
  40185e:	c3                   	ret
  40185f:	90                   	nop
  401860:	c3                   	ret
  401861:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40186c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401870 <frame_dummy>:
  401870:	f3 0f 1e fa          	endbr64
  401874:	eb 8a                	jmp    401800 <register_tm_clones>
  401876:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401880 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  401880:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  401884:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  401887:	7e 77                	jle    401900 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  401889:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  40188d:	55                   	push   %rbp
  40188e:	49 89 f2             	mov    %rsi,%r10
  401891:	49 89 d3             	mov    %rdx,%r11
  401894:	53                   	push   %rbx
  401895:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  401898:	48 8b 98 a0 03 00 00 	mov    0x3a0(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  40189f:	b8 01 00 00 00       	mov    $0x1,%eax
  4018a4:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  4018a8:	48 63 d0             	movslq %eax,%rdx
  4018ab:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  4018ae:	85 d2                	test   %edx,%edx
  4018b0:	40 0f 94 c6          	sete   %sil
  4018b4:	f6 c2 04             	test   $0x4,%dl
  4018b7:	75 05                	jne    4018be <pollthreads+0x3e>
  4018b9:	40 84 f6             	test   %sil,%sil
  4018bc:	74 0d                	je     4018cb <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  4018be:	49 63 08             	movslq (%r8),%rcx
  4018c1:	8d 69 01             	lea    0x1(%rcx),%ebp
  4018c4:	41 89 28             	mov    %ebp,(%r8)
  4018c7:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  4018cb:	83 e2 08             	and    $0x8,%edx
  4018ce:	75 05                	jne    4018d5 <pollthreads+0x55>
  4018d0:	40 84 f6             	test   %sil,%sil
  4018d3:	74 1b                	je     4018f0 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  4018d5:	48 63 17             	movslq (%rdi),%rdx
  4018d8:	8d 4a 01             	lea    0x1(%rdx),%ecx
  4018db:	89 0f                	mov    %ecx,(%rdi)
  4018dd:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  4018e1:	83 c0 01             	add    $0x1,%eax
  4018e4:	41 39 41 68          	cmp    %eax,0x68(%r9)
  4018e8:	7f be                	jg     4018a8 <pollthreads+0x28>
}
  4018ea:	31 c0                	xor    %eax,%eax
  4018ec:	5b                   	pop    %rbx
  4018ed:	5d                   	pop    %rbp
  4018ee:	c3                   	ret
  4018ef:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  4018f0:	83 c0 01             	add    $0x1,%eax
  4018f3:	41 39 41 68          	cmp    %eax,0x68(%r9)
  4018f7:	7f af                	jg     4018a8 <pollthreads+0x28>
}
  4018f9:	31 c0                	xor    %eax,%eax
  4018fb:	5b                   	pop    %rbx
  4018fc:	5d                   	pop    %rbp
  4018fd:	c3                   	ret
  4018fe:	66 90                	xchg   %ax,%ax
  401900:	31 c0                	xor    %eax,%eax
  401902:	c3                   	ret
  401903:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40190e:	66 90                	xchg   %ax,%ax

0000000000401910 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401910:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401913:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
      if (*availableidx == 0) {
  40191a:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40191d:	48 83 c7 01          	add    $0x1,%rdi
  401921:	48 85 ff             	test   %rdi,%rdi
  401924:	7e 66                	jle    40198c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401926:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40192d:	31 c9                	xor    %ecx,%ecx
  40192f:	45 31 c9             	xor    %r9d,%r9d
  401932:	31 c0                	xor    %eax,%eax
  401934:	eb 18                	jmp    40194e <findavailable+0x3e>
  401936:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401940:	83 c1 01             	add    $0x1,%ecx
  401943:	48 63 c1             	movslq %ecx,%rax
  401946:	49 89 c1             	mov    %rax,%r9
  401949:	48 39 f8             	cmp    %rdi,%rax
  40194c:	7d 3e                	jge    40198c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  40194e:	48 c1 e0 05          	shl    $0x5,%rax
  401952:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401958:	75 e6                	jne    401940 <findavailable+0x30>
         available[*availableidx] = x;
  40195a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  40195d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401961:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401965:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401968:	41 8b 43 68          	mov    0x68(%r11),%eax
  40196c:	01 c0                	add    %eax,%eax
  40196e:	41 39 c0             	cmp    %eax,%r8d
  401971:	74 19                	je     40198c <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401973:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  40197a:	83 c1 01             	add    $0x1,%ecx
  40197d:	48 63 c1             	movslq %ecx,%rax
  401980:	48 83 c7 01          	add    $0x1,%rdi
  401984:	49 89 c1             	mov    %rax,%r9
  401987:	48 39 f8             	cmp    %rdi,%rax
  40198a:	7c c2                	jl     40194e <findavailable+0x3e>
      if (*availableidx == 0) {
  40198c:	31 c0                	xor    %eax,%eax
  40198e:	45 85 c0             	test   %r8d,%r8d
  401991:	0f 94 c0             	sete   %al
}
  401994:	c3                   	ret
  401995:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000004019a0 <singlewriter3>:
  if (data->writecursor != 0 && (data->writecursor % (data->threadsize - 1)) == 0) {
  4019a0:	8b 87 80 01 00 00    	mov    0x180(%rdi),%eax
  4019a6:	85 c0                	test   %eax,%eax
  4019a8:	74 17                	je     4019c1 <singlewriter3+0x21>
  4019aa:	8b 77 68             	mov    0x68(%rdi),%esi
  4019ad:	99                   	cltd
  4019ae:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  4019b1:	f7 f9                	idiv   %ecx
  4019b3:	85 d2                	test   %edx,%edx
  4019b5:	75 0a                	jne    4019c1 <singlewriter3+0x21>
    data->writecursor = 0;
  4019b7:	c7 87 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rdi)
}
  4019c1:	c3                   	ret
  4019c2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4019cd:	0f 1f 00             	nopl   (%rax)

00000000004019d0 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4019d0:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  4019d6:	85 c0                	test   %eax,%eax
  4019d8:	74 1e                	je     4019f8 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  4019da:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4019dc:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  4019dd:	55                   	push   %rbp
  4019de:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4019df:	8b 77 68             	mov    0x68(%rdi),%esi
  4019e2:	48 89 fb             	mov    %rdi,%rbx
  4019e5:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  4019e8:	f7 f9                	idiv   %ecx
  4019ea:	85 d2                	test   %edx,%edx
  4019ec:	74 12                	je     401a00 <singlewriter2+0x30>
}
  4019ee:	5b                   	pop    %rbx
  4019ef:	5d                   	pop    %rbp
  4019f0:	41 5c                	pop    %r12
  4019f2:	c3                   	ret
  4019f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4019f8:	c3                   	ret
  4019f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    data->readcursor = 0;
  401a00:	c7 87 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdi)
        struct Data * thread = &data->threads[data->threadindex];
  401a0a:	48 63 47 64          	movslq 0x64(%rdi),%rax
  401a0e:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  401a16:	48 29 c5             	sub    %rax,%rbp
  401a19:	48 c1 e5 07          	shl    $0x7,%rbp
  401a1d:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401a21:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401a26:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401a2d:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401a31:	49 c1 e4 04          	shl    $0x4,%r12
  401a35:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401a3c:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401a41:	e8 0a f6 ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401a46:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401a4c:	83 c0 01             	add    $0x1,%eax
  401a4f:	99                   	cltd
  401a50:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  401a56:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401a59:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401a5f:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401a63:	48 8b 05 66 17 00 00 	mov    0x1766(%rip),%rax        # 4031d0 <_IO_stdin_used+0x1d0>
  401a6a:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  401a6f:	5b                   	pop    %rbx
  401a70:	5d                   	pop    %rbp
  401a71:	41 5c                	pop    %r12
  401a73:	c3                   	ret
  401a74:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401a7f:	90                   	nop

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
  401ae0:	e8 2b fe ff ff       	call   401910 <findavailable>
  if (fill == 1) {
  401ae5:	83 f8 01             	cmp    $0x1,%eax
  401ae8:	0f 84 64 01 00 00    	je     401c52 <singlewriter+0x1d2>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401aee:	48 89 ef             	mov    %rbp,%rdi
  401af1:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401af6:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401afb:	4c 89 e2             	mov    %r12,%rdx
  401afe:	4c 89 ee             	mov    %r13,%rsi
  401b01:	e8 7a fd ff ff       	call   401880 <pollthreads>
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
  401c9d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401ca6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401cab:	48 8b 47 28          	mov    0x28(%rdi),%rax
  long lastcursor = data->main->writecursor;
  401caf:	8b b0 80 01 00 00    	mov    0x180(%rax),%esi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401cb5:	48 8b 80 38 03 00 00 	mov    0x338(%rax),%rax
  401cbc:	48 99                	cqto
    data->thiswrite = lastcursor;
  401cbe:	89 b7 28 03 00 00    	mov    %esi,0x328(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401cc4:	48 89 e6             	mov    %rsp,%rsi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401cc7:	48 f7 f9             	idiv   %rcx
    data->prevwrite = lastwrite;
  401cca:	48 89 97 10 03 00 00 	mov    %rdx,0x310(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401cd1:	bf 04 00 00 00       	mov    $0x4,%edi
  401cd6:	e8 75 f3 ff ff       	call   401050 <clock_gettime@plt>
    int x = 2 + (data->threadindex + n) % data->threadsize - 2;
  401cdb:	8b 4b 64             	mov    0x64(%rbx),%ecx
   data->freq_writes++;
  401cde:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
    int x = 2 + (data->threadindex + n) % data->threadsize - 2;
  401ce3:	89 c8                	mov    %ecx,%eax
  401ce5:	99                   	cltd
  401ce6:	f7 7b 68             	idivl  0x68(%rbx)
     if (x != data->threadindex) {
  401ce9:	39 d1                	cmp    %edx,%ecx
  401ceb:	0f 84 eb 00 00 00    	je     401ddc <threadwork+0x14c>
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401cf1:	48 63 83 80 01 00 00 	movslq 0x180(%rbx),%rax
  401cf8:	89 d6                	mov    %edx,%esi
  401cfa:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
        epoch->time = time;
  401cfe:	66 0f 6f 04 24       	movdqa (%rsp),%xmm0
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401d03:	48 89 c2             	mov    %rax,%rdx
  401d06:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401d0d:	41 89 d0             	mov    %edx,%r8d
  401d10:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401d14:	48 c1 e8 20          	shr    $0x20,%rax
  401d18:	01 d0                	add    %edx,%eax
  401d1a:	c1 f8 03             	sar    $0x3,%eax
  401d1d:	44 29 c0             	sub    %r8d,%eax
  401d20:	41 89 c0             	mov    %eax,%r8d
  401d23:	41 c1 e0 04          	shl    $0x4,%r8d
  401d27:	41 29 c0             	sub    %eax,%r8d
  401d2a:	89 c8                	mov    %ecx,%eax
  401d2c:	44 29 c2             	sub    %r8d,%edx
  401d2f:	c1 e0 18             	shl    $0x18,%eax
  401d32:	09 c2                	or     %eax,%edx
  401d34:	89 f0                	mov    %esi,%eax
  401d36:	c1 e0 08             	shl    $0x8,%eax
  401d39:	09 c2                	or     %eax,%edx
  401d3b:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  401d42:	41 89 d2             	mov    %edx,%r10d
  401d45:	48 89 c2             	mov    %rax,%rdx
  401d48:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401d4f:	41 89 d0             	mov    %edx,%r8d
  401d52:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401d56:	48 c1 e8 20          	shr    $0x20,%rax
  401d5a:	01 d0                	add    %edx,%eax
  401d5c:	c1 f8 03             	sar    $0x3,%eax
  401d5f:	44 29 c0             	sub    %r8d,%eax
  401d62:	41 89 c0             	mov    %eax,%r8d
  401d65:	41 c1 e0 04          	shl    $0x4,%r8d
  401d69:	41 29 c0             	sub    %eax,%r8d
        struct Data * thread = &data->threads[data->threadindex];
  401d6c:	48 63 c1             	movslq %ecx,%rax
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401d6f:	44 29 c2             	sub    %r8d,%edx
        struct Data * thread = &data->threads[data->threadindex];
  401d72:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
  401d7a:	49 29 c0             	sub    %rax,%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401d7d:	c1 e2 10             	shl    $0x10,%edx
        struct Data * thread = &data->threads[data->threadindex];
  401d80:	49 c1 e0 07          	shl    $0x7,%r8
  401d84:	4c 03 43 30          	add    0x30(%rbx),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401d88:	41 09 d2             	or     %edx,%r10d
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401d8b:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401d92:	4d 63 d2             	movslq %r10d,%r10
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401d95:	48 89 d0             	mov    %rdx,%rax
  401d98:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401d9c:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401d9f:	49 c1 e1 04          	shl    $0x4,%r9
  401da3:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401daa:	99                   	cltd
        epoch->time = time;
  401dab:	41 0f 11 41 08       	movups %xmm0,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401db0:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
  data->main->works[buffer] = data->threadindex;
  401db7:	48 8b 47 70          	mov    0x70(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401dbb:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
        epoch->thread = data->threadindex;
  401dc2:	41 89 09             	mov    %ecx,(%r9)
  epoch->dest = x;
  401dc5:	41 89 71 28          	mov    %esi,0x28(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401dc9:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  401dcd:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
  data->main->works[buffer] = data->threadindex;
  401dd5:	42 88 0c 10          	mov    %cl,(%rax,%r10,1)
  401dd9:	8b 4b 64             	mov    0x64(%rbx),%ecx
    int x = 2 + (data->threadindex + n) % data->threadsize - 2;
  401ddc:	8d 41 01             	lea    0x1(%rcx),%eax
  401ddf:	99                   	cltd
  401de0:	f7 7b 68             	idivl  0x68(%rbx)
  401de3:	89 d6                	mov    %edx,%esi
     if (x != data->threadindex) {
  401de5:	39 d1                	cmp    %edx,%ecx
  401de7:	0f 84 ea 00 00 00    	je     401ed7 <threadwork+0x247>
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401ded:	48 63 83 80 01 00 00 	movslq 0x180(%rbx),%rax
  401df4:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
        epoch->time = time;
  401df8:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401dfd:	48 89 c2             	mov    %rax,%rdx
  401e00:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401e07:	41 89 d0             	mov    %edx,%r8d
  401e0a:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401e0e:	48 c1 e8 20          	shr    $0x20,%rax
  401e12:	01 d0                	add    %edx,%eax
  401e14:	c1 f8 03             	sar    $0x3,%eax
  401e17:	44 29 c0             	sub    %r8d,%eax
  401e1a:	41 89 c0             	mov    %eax,%r8d
  401e1d:	41 c1 e0 04          	shl    $0x4,%r8d
  401e21:	41 29 c0             	sub    %eax,%r8d
  401e24:	89 c8                	mov    %ecx,%eax
  401e26:	44 29 c2             	sub    %r8d,%edx
  401e29:	c1 e0 18             	shl    $0x18,%eax
  401e2c:	09 c2                	or     %eax,%edx
  401e2e:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  401e35:	41 89 d2             	mov    %edx,%r10d
  401e38:	48 89 c2             	mov    %rax,%rdx
  401e3b:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401e42:	41 89 d0             	mov    %edx,%r8d
  401e45:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401e49:	48 c1 e8 20          	shr    $0x20,%rax
  401e4d:	01 d0                	add    %edx,%eax
  401e4f:	c1 f8 03             	sar    $0x3,%eax
  401e52:	44 29 c0             	sub    %r8d,%eax
  401e55:	41 89 c0             	mov    %eax,%r8d
  401e58:	41 c1 e0 04          	shl    $0x4,%r8d
  401e5c:	41 29 c0             	sub    %eax,%r8d
  401e5f:	89 f0                	mov    %esi,%eax
  401e61:	44 29 c2             	sub    %r8d,%edx
  401e64:	c1 e0 08             	shl    $0x8,%eax
  401e67:	c1 e2 10             	shl    $0x10,%edx
  401e6a:	41 09 d2             	or     %edx,%r10d
  401e6d:	41 09 c2             	or     %eax,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  401e70:	48 63 c1             	movslq %ecx,%rax
  401e73:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401e7b:	4d 63 d2             	movslq %r10d,%r10
        struct Data * thread = &data->threads[data->threadindex];
  401e7e:	49 29 c0             	sub    %rax,%r8
  401e81:	49 c1 e0 07          	shl    $0x7,%r8
  401e85:	4c 03 43 30          	add    0x30(%rbx),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401e89:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  401e90:	48 89 d0             	mov    %rdx,%rax
  401e93:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e97:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401e9a:	49 c1 e1 04          	shl    $0x4,%r9
  401e9e:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ea5:	99                   	cltd
        epoch->time = time;
  401ea6:	41 0f 11 49 08       	movups %xmm1,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401eab:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
  data->main->works[buffer] = data->threadindex;
  401eb2:	48 8b 47 70          	mov    0x70(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401eb6:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
        epoch->thread = data->threadindex;
  401ebd:	41 89 09             	mov    %ecx,(%r9)
  epoch->dest = x;
  401ec0:	41 89 71 28          	mov    %esi,0x28(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401ec4:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  401ec8:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
  data->main->works[buffer] = data->threadindex;
  401ed0:	42 88 0c 10          	mov    %cl,(%rax,%r10,1)
  401ed4:	8b 4b 64             	mov    0x64(%rbx),%ecx
    int x = 2 + (data->threadindex + n) % data->threadsize - 2;
  401ed7:	8d 41 02             	lea    0x2(%rcx),%eax
  401eda:	99                   	cltd
  401edb:	f7 7b 68             	idivl  0x68(%rbx)
  401ede:	89 d6                	mov    %edx,%esi
     if (x != data->threadindex) {
  401ee0:	39 d1                	cmp    %edx,%ecx
  401ee2:	0f 84 e7 00 00 00    	je     401fcf <threadwork+0x33f>
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401ee8:	48 63 83 80 01 00 00 	movslq 0x180(%rbx),%rax
  401eef:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
        epoch->time = time;
  401ef3:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401ef8:	48 89 c2             	mov    %rax,%rdx
  401efb:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401f02:	41 89 d0             	mov    %edx,%r8d
  401f05:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401f09:	48 c1 e8 20          	shr    $0x20,%rax
  401f0d:	01 d0                	add    %edx,%eax
  401f0f:	c1 f8 03             	sar    $0x3,%eax
  401f12:	44 29 c0             	sub    %r8d,%eax
  401f15:	41 89 c0             	mov    %eax,%r8d
  401f18:	41 c1 e0 04          	shl    $0x4,%r8d
  401f1c:	41 29 c0             	sub    %eax,%r8d
  401f1f:	89 c8                	mov    %ecx,%eax
  401f21:	44 29 c2             	sub    %r8d,%edx
  401f24:	c1 e0 18             	shl    $0x18,%eax
  401f27:	09 c2                	or     %eax,%edx
  401f29:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  401f30:	41 89 d2             	mov    %edx,%r10d
  401f33:	48 89 c2             	mov    %rax,%rdx
  401f36:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401f3d:	41 89 d0             	mov    %edx,%r8d
  401f40:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401f44:	48 c1 e8 20          	shr    $0x20,%rax
  401f48:	01 d0                	add    %edx,%eax
  401f4a:	c1 f8 03             	sar    $0x3,%eax
  401f4d:	44 29 c0             	sub    %r8d,%eax
  401f50:	41 89 c0             	mov    %eax,%r8d
  401f53:	41 c1 e0 04          	shl    $0x4,%r8d
  401f57:	41 29 c0             	sub    %eax,%r8d
  401f5a:	89 f0                	mov    %esi,%eax
  401f5c:	44 29 c2             	sub    %r8d,%edx
  401f5f:	c1 e0 08             	shl    $0x8,%eax
  401f62:	c1 e2 10             	shl    $0x10,%edx
  401f65:	41 09 d2             	or     %edx,%r10d
  401f68:	41 09 c2             	or     %eax,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  401f6b:	48 63 c1             	movslq %ecx,%rax
  401f6e:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401f76:	4d 63 d2             	movslq %r10d,%r10
        struct Data * thread = &data->threads[data->threadindex];
  401f79:	49 29 c0             	sub    %rax,%r8
  401f7c:	49 c1 e0 07          	shl    $0x7,%r8
  401f80:	4c 03 43 30          	add    0x30(%rbx),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401f84:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  401f8b:	48 89 d0             	mov    %rdx,%rax
  401f8e:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401f92:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401f95:	49 c1 e1 04          	shl    $0x4,%r9
  401f99:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401fa0:	99                   	cltd
        epoch->time = time;
  401fa1:	41 0f 11 51 08       	movups %xmm2,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401fa6:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
  data->main->works[buffer] = data->threadindex;
  401fad:	48 8b 47 70          	mov    0x70(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401fb1:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
        epoch->thread = data->threadindex;
  401fb8:	41 89 09             	mov    %ecx,(%r9)
  epoch->dest = x;
  401fbb:	41 89 71 28          	mov    %esi,0x28(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401fbf:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  401fc3:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
  data->main->works[buffer] = data->threadindex;
  401fcb:	42 88 0c 10          	mov    %cl,(%rax,%r10,1)
    data->writecursor = (data->writecursor + 1) % 0xf;
  401fcf:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
  401fd5:	8d 50 01             	lea    0x1(%rax),%edx
  401fd8:	48 63 c2             	movslq %edx,%rax
  401fdb:	89 d1                	mov    %edx,%ecx
  401fdd:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401fe4:	c1 f9 1f             	sar    $0x1f,%ecx
  401fe7:	48 c1 e8 20          	shr    $0x20,%rax
  401feb:	01 d0                	add    %edx,%eax
  401fed:	c1 f8 03             	sar    $0x3,%eax
  401ff0:	29 c8                	sub    %ecx,%eax
  401ff2:	89 c1                	mov    %eax,%ecx
  401ff4:	c1 e1 04             	shl    $0x4,%ecx
  401ff7:	29 c1                	sub    %eax,%ecx
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_ACQUIRE);
  401ff9:	48 8b 43 28          	mov    0x28(%rbx),%rax
    data->writecursor = (data->writecursor + 1) % 0xf;
  401ffd:	29 ca                	sub    %ecx,%edx
  401fff:	89 93 80 01 00 00    	mov    %edx,0x180(%rbx)
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_ACQUIRE);
  402005:	f0 48 83 80 50 03 00 00 01 	lock addq $0x1,0x350(%rax)
  long lastread = data->main->totalreads % data->threadsize;
  40200e:	48 8b 73 28          	mov    0x28(%rbx),%rsi
  402012:	48 63 4b 68          	movslq 0x68(%rbx),%rcx
    int x = 2 + ((data->threadindex + y) % data->threadsize - 2);
  402016:	8b 7b 64             	mov    0x64(%rbx),%edi
  long lastread = data->main->totalreads % data->threadsize;
  402019:	48 8b 86 40 03 00 00 	mov    0x340(%rsi),%rax
  402020:	49 89 c8             	mov    %rcx,%r8
   data->freq++;
  402023:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
  long lastread = data->main->totalreads % data->threadsize;
  402028:	48 99                	cqto
  40202a:	48 f7 f9             	idiv   %rcx
    int x = 2 + ((data->threadindex + y) % data->threadsize - 2);
  40202d:	89 f8                	mov    %edi,%eax
   data->prevread = lastread;
  40202f:	48 89 93 08 03 00 00 	mov    %rdx,0x308(%rbx)
    int x = 2 + ((data->threadindex + y) % data->threadsize - 2);
  402036:	99                   	cltd
  402037:	f7 f9                	idiv   %ecx
  402039:	41 89 d1             	mov    %edx,%r9d
          if (x != data->threadindex) {
  40203c:	39 d7                	cmp    %edx,%edi
  40203e:	0f 84 fd 00 00 00    	je     402141 <threadwork+0x4b1>
            long past = ((data->main->writecursor - 1) % 0xf);
  402044:	8b 86 80 01 00 00    	mov    0x180(%rsi),%eax
              past = data->threadsize - 1;
  40204a:	45 8d 50 ff          	lea    -0x1(%r8),%r10d
            long past = ((data->main->writecursor - 1) % 0xf);
  40204e:	8d 50 ff             	lea    -0x1(%rax),%edx
  402051:	48 63 c2             	movslq %edx,%rax
  402054:	89 d1                	mov    %edx,%ecx
  402056:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  40205d:	c1 f9 1f             	sar    $0x1f,%ecx
  402060:	48 c1 e8 20          	shr    $0x20,%rax
  402064:	01 d0                	add    %edx,%eax
  402066:	c1 f8 03             	sar    $0x3,%eax
  402069:	29 c8                	sub    %ecx,%eax
  40206b:	89 c1                	mov    %eax,%ecx
  40206d:	c1 e1 04             	shl    $0x4,%ecx
  402070:	29 c1                	sub    %eax,%ecx
              past = data->threadsize - 1;
  402072:	89 d0                	mov    %edx,%eax
            int rc = data->threads[x].writecursor;
  402074:	48 8b 53 30          	mov    0x30(%rbx),%rdx
              past = data->threadsize - 1;
  402078:	29 c8                	sub    %ecx,%eax
  40207a:	41 0f 48 c2          	cmovs  %r10d,%eax
            int rc = data->threads[x].writecursor;
  40207e:	4d 63 d1             	movslq %r9d,%r10
  402081:	48 63 c8             	movslq %eax,%rcx
  402084:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
  40208c:	4c 29 d0             	sub    %r10,%rax
  40208f:	48 c1 e0 07          	shl    $0x7,%rax
  402093:	44 8b 9c 02 80 01 00 00 	mov    0x180(%rdx,%rax,1),%r11d
            if (rc < 0) {
  40209b:	45 85 db             	test   %r11d,%r11d
  40209e:	0f 88 2c 03 00 00    	js     4023d0 <threadwork+0x740>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4020a4:	49 63 c3             	movslq %r11d,%rax
  4020a7:	45 89 da             	mov    %r11d,%r10d
  4020aa:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  4020b1:	41 c1 fa 1f          	sar    $0x1f,%r10d
  4020b5:	48 c1 e8 20          	shr    $0x20,%rax
  4020b9:	44 01 d8             	add    %r11d,%eax
  4020bc:	c1 f8 03             	sar    $0x3,%eax
  4020bf:	44 29 d0             	sub    %r10d,%eax
  4020c2:	41 89 c2             	mov    %eax,%r10d
  4020c5:	41 c1 e2 04          	shl    $0x4,%r10d
  4020c9:	41 29 c2             	sub    %eax,%r10d
  4020cc:	45 29 d3             	sub    %r10d,%r11d
  4020cf:	4d 63 db             	movslq %r11d,%r11
                struct Data * thread = &data->threads[data->threadindex];
  4020d2:	48 63 c7             	movslq %edi,%rax
            thepoch->time = time; 
  4020d5:	66 0f 6f 1c 24       	movdqa (%rsp),%xmm3
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4020da:	48 c1 e1 10          	shl    $0x10,%rcx
                struct Data * thread = &data->threads[data->threadindex];
  4020de:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  4020e6:	48 29 c5             	sub    %rax,%rbp
  4020e9:	48 c1 e5 07          	shl    $0x7,%rbp
  4020ed:	48 01 d5             	add    %rdx,%rbp
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  4020f0:	48 63 95 24 03 00 00 	movslq 0x324(%rbp),%rdx
  4020f7:	48 89 d0             	mov    %rdx,%rax
  4020fa:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4020fe:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402101:	49 c1 e2 04          	shl    $0x4,%r10
  402105:	4c 03 95 18 03 00 00 	add    0x318(%rbp),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40210c:	99                   	cltd
            thepoch->time = time; 
  40210d:	41 0f 11 5a 08       	movups %xmm3,0x8(%r10)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402112:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402118:	89 f8                	mov    %edi,%eax
  40211a:	c1 e0 08             	shl    $0x8,%eax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40211d:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
                thepoch->thread = x;
  402123:	45 89 0a             	mov    %r9d,(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402126:	41 c1 e1 18          	shl    $0x18,%r9d
  40212a:	44 09 c8             	or     %r9d,%eax
          thepoch->set = 1;
  40212d:	41 c7 42 24 01 00 00 00 	movl   $0x1,0x24(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402135:	48 98                	cltq
  402137:	48 09 c8             	or     %rcx,%rax
  40213a:	4c 09 d8             	or     %r11,%rax
  40213d:	49 89 42 18          	mov    %rax,0x18(%r10)
    int x = 2 + ((data->threadindex + y) % data->threadsize - 2);
  402141:	8d 47 01             	lea    0x1(%rdi),%eax
  402144:	99                   	cltd
  402145:	41 f7 f8             	idiv   %r8d
  402148:	41 89 d1             	mov    %edx,%r9d
          if (x != data->threadindex) {
  40214b:	39 fa                	cmp    %edi,%edx
  40214d:	0f 84 01 01 00 00    	je     402254 <threadwork+0x5c4>
            long past = ((data->main->writecursor - 1) % 0xf);
  402153:	8b 86 80 01 00 00    	mov    0x180(%rsi),%eax
              past = data->threadsize - 1;
  402159:	45 8d 50 ff          	lea    -0x1(%r8),%r10d
            long past = ((data->main->writecursor - 1) % 0xf);
  40215d:	8d 50 ff             	lea    -0x1(%rax),%edx
  402160:	48 63 c2             	movslq %edx,%rax
  402163:	89 d1                	mov    %edx,%ecx
  402165:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  40216c:	c1 f9 1f             	sar    $0x1f,%ecx
  40216f:	48 c1 e8 20          	shr    $0x20,%rax
  402173:	01 d0                	add    %edx,%eax
  402175:	c1 f8 03             	sar    $0x3,%eax
  402178:	29 c8                	sub    %ecx,%eax
  40217a:	89 c1                	mov    %eax,%ecx
  40217c:	c1 e1 04             	shl    $0x4,%ecx
  40217f:	29 c1                	sub    %eax,%ecx
              past = data->threadsize - 1;
  402181:	89 d0                	mov    %edx,%eax
            int rc = data->threads[x].writecursor;
  402183:	48 8b 53 30          	mov    0x30(%rbx),%rdx
              past = data->threadsize - 1;
  402187:	29 c8                	sub    %ecx,%eax
  402189:	41 0f 48 c2          	cmovs  %r10d,%eax
            int rc = data->threads[x].writecursor;
  40218d:	4d 63 d1             	movslq %r9d,%r10
  402190:	48 63 c8             	movslq %eax,%rcx
  402193:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
  40219b:	4c 29 d0             	sub    %r10,%rax
  40219e:	48 c1 e0 07          	shl    $0x7,%rax
  4021a2:	44 8b 9c 02 80 01 00 00 	mov    0x180(%rdx,%rax,1),%r11d
            if (rc < 0) {
  4021aa:	45 85 db             	test   %r11d,%r11d
  4021ad:	0f 88 0d 02 00 00    	js     4023c0 <threadwork+0x730>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4021b3:	49 63 c3             	movslq %r11d,%rax
  4021b6:	45 89 da             	mov    %r11d,%r10d
  4021b9:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  4021c0:	41 c1 fa 1f          	sar    $0x1f,%r10d
  4021c4:	48 c1 e8 20          	shr    $0x20,%rax
  4021c8:	44 01 d8             	add    %r11d,%eax
  4021cb:	c1 f8 03             	sar    $0x3,%eax
  4021ce:	44 29 d0             	sub    %r10d,%eax
  4021d1:	41 89 c2             	mov    %eax,%r10d
  4021d4:	41 c1 e2 04          	shl    $0x4,%r10d
  4021d8:	41 29 c2             	sub    %eax,%r10d
  4021db:	45 29 d3             	sub    %r10d,%r11d
  4021de:	4d 63 db             	movslq %r11d,%r11
                struct Data * thread = &data->threads[data->threadindex];
  4021e1:	48 63 c7             	movslq %edi,%rax
            thepoch->time = time; 
  4021e4:	66 0f 6f 24 24       	movdqa (%rsp),%xmm4
                struct Data * thread = &data->threads[data->threadindex];
  4021e9:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  4021f1:	48 29 c5             	sub    %rax,%rbp
  4021f4:	48 c1 e5 07          	shl    $0x7,%rbp
  4021f8:	48 01 d5             	add    %rdx,%rbp
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  4021fb:	48 63 95 24 03 00 00 	movslq 0x324(%rbp),%rdx
  402202:	48 89 d0             	mov    %rdx,%rax
  402205:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402209:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  40220c:	49 c1 e2 04          	shl    $0x4,%r10
  402210:	4c 03 95 18 03 00 00 	add    0x318(%rbp),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402217:	99                   	cltd
            thepoch->time = time; 
  402218:	41 0f 11 62 08       	movups %xmm4,0x8(%r10)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40221d:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402223:	89 f8                	mov    %edi,%eax
  402225:	c1 e0 08             	shl    $0x8,%eax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402228:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
                thepoch->thread = x;
  40222e:	45 89 0a             	mov    %r9d,(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402231:	41 c1 e1 18          	shl    $0x18,%r9d
  402235:	41 09 c1             	or     %eax,%r9d
  402238:	48 89 c8             	mov    %rcx,%rax
          thepoch->set = 1;
  40223b:	41 c7 42 24 01 00 00 00 	movl   $0x1,0x24(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402243:	4d 63 c9             	movslq %r9d,%r9
  402246:	48 c1 e0 10          	shl    $0x10,%rax
  40224a:	49 09 c1             	or     %rax,%r9
  40224d:	4d 09 d9             	or     %r11,%r9
  402250:	4d 89 4a 18          	mov    %r9,0x18(%r10)
    int x = 2 + ((data->threadindex + y) % data->threadsize - 2);
  402254:	8d 47 02             	lea    0x2(%rdi),%eax
  402257:	99                   	cltd
  402258:	41 f7 f8             	idiv   %r8d
  40225b:	41 89 d1             	mov    %edx,%r9d
          if (x != data->threadindex) {
  40225e:	39 fa                	cmp    %edi,%edx
  402260:	0f 84 05 01 00 00    	je     40236b <threadwork+0x6db>
            long past = ((data->main->writecursor - 1) % 0xf);
  402266:	8b 86 80 01 00 00    	mov    0x180(%rsi),%eax
  40226c:	41 bb 0e 00 00 00    	mov    $0xe,%r11d
  402272:	8d 50 ff             	lea    -0x1(%rax),%edx
  402275:	48 63 ca             	movslq %edx,%rcx
  402278:	89 d0                	mov    %edx,%eax
  40227a:	48 69 c9 89 88 88 88 	imul   $0xffffffff88888889,%rcx,%rcx
  402281:	c1 f8 1f             	sar    $0x1f,%eax
  402284:	48 c1 e9 20          	shr    $0x20,%rcx
  402288:	01 d1                	add    %edx,%ecx
  40228a:	c1 f9 03             	sar    $0x3,%ecx
  40228d:	29 c1                	sub    %eax,%ecx
              past = data->threadsize - 1;
  40228f:	41 8d 40 ff          	lea    -0x1(%r8),%eax
            int rc = data->threads[x].writecursor;
  402293:	4d 63 c1             	movslq %r9d,%r8
            long past = ((data->main->writecursor - 1) % 0xf);
  402296:	41 89 ca             	mov    %ecx,%r10d
  402299:	41 c1 e2 04          	shl    $0x4,%r10d
  40229d:	41 29 ca             	sub    %ecx,%r10d
              past = data->threadsize - 1;
  4022a0:	89 d1                	mov    %edx,%ecx
            int rc = data->threads[x].writecursor;
  4022a2:	48 8b 53 30          	mov    0x30(%rbx),%rdx
              past = data->threadsize - 1;
  4022a6:	44 29 d1             	sub    %r10d,%ecx
  4022a9:	0f 48 c8             	cmovs  %eax,%ecx
            int rc = data->threads[x].writecursor;
  4022ac:	4a 8d 04 c5 00 00 00 00 	lea    0x0(,%r8,8),%rax
  4022b4:	4c 29 c0             	sub    %r8,%rax
  4022b7:	48 c1 e0 07          	shl    $0x7,%rax
  4022bb:	48 63 c9             	movslq %ecx,%rcx
  4022be:	44 8b 84 02 80 01 00 00 	mov    0x180(%rdx,%rax,1),%r8d
            if (rc < 0) {
  4022c6:	45 85 c0             	test   %r8d,%r8d
  4022c9:	78 2e                	js     4022f9 <threadwork+0x669>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  4022cb:	49 63 c0             	movslq %r8d,%rax
  4022ce:	45 89 c2             	mov    %r8d,%r10d
  4022d1:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  4022d8:	41 c1 fa 1f          	sar    $0x1f,%r10d
  4022dc:	48 c1 e8 20          	shr    $0x20,%rax
  4022e0:	44 01 c0             	add    %r8d,%eax
  4022e3:	c1 f8 03             	sar    $0x3,%eax
  4022e6:	44 29 d0             	sub    %r10d,%eax
  4022e9:	41 89 c2             	mov    %eax,%r10d
  4022ec:	41 c1 e2 04          	shl    $0x4,%r10d
  4022f0:	41 29 c2             	sub    %eax,%r10d
  4022f3:	45 29 d0             	sub    %r10d,%r8d
  4022f6:	4d 63 d8             	movslq %r8d,%r11
                struct Data * thread = &data->threads[data->threadindex];
  4022f9:	48 63 c7             	movslq %edi,%rax
            thepoch->time = time; 
  4022fc:	66 0f 6f 2c 24       	movdqa (%rsp),%xmm5
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402301:	48 c1 e1 10          	shl    $0x10,%rcx
                struct Data * thread = &data->threads[data->threadindex];
  402305:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
  40230d:	49 29 c0             	sub    %rax,%r8
  402310:	49 c1 e0 07          	shl    $0x7,%r8
  402314:	49 01 d0             	add    %rdx,%r8
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402317:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  40231e:	48 89 d0             	mov    %rdx,%rax
  402321:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402325:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402328:	49 c1 e2 04          	shl    $0x4,%r10
  40232c:	4d 03 90 18 03 00 00 	add    0x318(%r8),%r10
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402333:	99                   	cltd
            thepoch->time = time; 
  402334:	41 0f 11 6a 08       	movups %xmm5,0x8(%r10)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402339:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402340:	89 f8                	mov    %edi,%eax
  402342:	c1 e0 08             	shl    $0x8,%eax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402345:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
                thepoch->thread = x;
  40234c:	45 89 0a             	mov    %r9d,(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40234f:	41 c1 e1 18          	shl    $0x18,%r9d
  402353:	41 09 c1             	or     %eax,%r9d
          thepoch->set = 1;
  402356:	41 c7 42 24 01 00 00 00 	movl   $0x1,0x24(%r10)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40235e:	4d 63 c9             	movslq %r9d,%r9
  402361:	49 09 c9             	or     %rcx,%r9
  402364:	4d 09 d9             	or     %r11,%r9
  402367:	4d 89 4a 18          	mov    %r9,0x18(%r10)
     data->readcursor = (data->readcursor + 1) % 0xf;
  40236b:	8b 83 00 02 00 00    	mov    0x200(%rbx),%eax
  402371:	8d 50 01             	lea    0x1(%rax),%edx
  402374:	48 63 c2             	movslq %edx,%rax
  402377:	89 d1                	mov    %edx,%ecx
  402379:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402380:	c1 f9 1f             	sar    $0x1f,%ecx
  402383:	48 c1 e8 20          	shr    $0x20,%rax
  402387:	01 d0                	add    %edx,%eax
  402389:	c1 f8 03             	sar    $0x3,%eax
  40238c:	29 c8                	sub    %ecx,%eax
  40238e:	89 c1                	mov    %eax,%ecx
  402390:	c1 e1 04             	shl    $0x4,%ecx
  402393:	29 c1                	sub    %eax,%ecx
  402395:	29 ca                	sub    %ecx,%edx
  402397:	89 93 00 02 00 00    	mov    %edx,0x200(%rbx)
    __atomic_fetch_add(&data->main->globalread, 1, __ATOMIC_ACQUIRE);
  40239d:	f0 48 83 86 48 03 00 00 01 	lock addq $0x1,0x348(%rsi)
}
  4023a6:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  4023ab:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4023b4:	75 25                	jne    4023db <threadwork+0x74b>
  4023b6:	48 83 c4 28          	add    $0x28,%rsp
  4023ba:	31 c0                	xor    %eax,%eax
  4023bc:	5b                   	pop    %rbx
  4023bd:	5d                   	pop    %rbp
  4023be:	c3                   	ret
  4023bf:	90                   	nop
            if (rc < 0) {
  4023c0:	41 bb 0e 00 00 00    	mov    $0xe,%r11d
  4023c6:	e9 16 fe ff ff       	jmp    4021e1 <threadwork+0x551>
  4023cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4023d0:	41 bb 0e 00 00 00    	mov    $0xe,%r11d
  4023d6:	e9 f7 fc ff ff       	jmp    4020d2 <threadwork+0x442>
}
  4023db:	e8 80 ec ff ff       	call   401060 <__stack_chk_fail@plt>

00000000004023e0 <work>:
void * work(void * arg) {
  4023e0:	41 56                	push   %r14
  4023e2:	48 8d 35 1b 0c 00 00 	lea    0xc1b(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  4023e9:	31 c0                	xor    %eax,%eax
  4023eb:	41 55                	push   %r13
  4023ed:	41 54                	push   %r12
  4023ef:	55                   	push   %rbp
  4023f0:	53                   	push   %rbx
  4023f1:	8b 57 64             	mov    0x64(%rdi),%edx
  4023f4:	48 89 fb             	mov    %rdi,%rbx
  4023f7:	bf 01 00 00 00       	mov    $0x1,%edi
  4023fc:	e8 8f ec ff ff       	call   401090 <__printf_chk@plt>
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  402401:	48 8b 83 b8 00 00 00 	mov    0xb8(%rbx),%rax
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  402408:	4c 63 6b 68          	movslq 0x68(%rbx),%r13
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  40240c:	be 08 00 00 00       	mov    $0x8,%esi
  402411:	48 8d 78 01          	lea    0x1(%rax),%rdi
  402415:	e8 66 ec ff ff       	call   401080 <calloc@plt>
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  40241a:	be 04 00 00 00       	mov    $0x4,%esi
  40241f:	4c 89 ef             	mov    %r13,%rdi
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  402422:	48 89 c5             	mov    %rax,%rbp
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  402425:	e8 56 ec ff ff       	call   401080 <calloc@plt>
  int * readywriters = calloc(data->threadsize, sizeof(int));
  40242a:	be 04 00 00 00       	mov    $0x4,%esi
  40242f:	4c 89 ef             	mov    %r13,%rdi
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  402432:	49 89 c4             	mov    %rax,%r12
  int * readywriters = calloc(data->threadsize, sizeof(int));
  402435:	e8 46 ec ff ff       	call   401080 <calloc@plt>
  while (data->running == 1) {
  40243a:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  40243e:	75 5f                	jne    40249f <work+0xbf>
  402440:	49 89 c5             	mov    %rax,%r13
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  402443:	4c 8d b3 28 01 00 00 	lea    0x128(%rbx),%r14
  40244a:	eb 17                	jmp    402463 <work+0x83>
  40244c:	0f 1f 40 00          	nopl   0x0(%rax)
    } else if (data->threadindex == 1) {
  402450:	83 f8 01             	cmp    $0x1,%eax
  402453:	74 6b                	je     4024c0 <work+0xe0>
      threadwork(data);
  402455:	48 89 df             	mov    %rbx,%rdi
  402458:	e8 33 f8 ff ff       	call   401c90 <threadwork>
  while (data->running == 1) {
  40245d:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  402461:	75 3c                	jne    40249f <work+0xbf>
   if (data->threadindex == 0) {
  402463:	8b 43 64             	mov    0x64(%rbx),%eax
  402466:	85 c0                	test   %eax,%eax
  402468:	75 e6                	jne    402450 <work+0x70>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  40246a:	4c 89 f6             	mov    %r14,%rsi
  40246d:	bf 04 00 00 00       	mov    $0x4,%edi
  402472:	e8 d9 eb ff ff       	call   401050 <clock_gettime@plt>
      singlewriter2(data, available, readyreaders, readywriters);
  402477:	4c 89 e9             	mov    %r13,%rcx
  40247a:	4c 89 e2             	mov    %r12,%rdx
  40247d:	48 89 ee             	mov    %rbp,%rsi
  402480:	48 89 df             	mov    %rbx,%rdi
  402483:	e8 48 f5 ff ff       	call   4019d0 <singlewriter2>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swend);
  402488:	48 8d b3 38 01 00 00 	lea    0x138(%rbx),%rsi
  40248f:	bf 04 00 00 00       	mov    $0x4,%edi
  402494:	e8 b7 eb ff ff       	call   401050 <clock_gettime@plt>
  while (data->running == 1) {
  402499:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  40249d:	74 c4                	je     402463 <work+0x83>
  40249f:	8b 53 64             	mov    0x64(%rbx),%edx
  4024a2:	48 8d 35 6e 0b 00 00 	lea    0xb6e(%rip),%rsi        # 403017 <_IO_stdin_used+0x17>
  4024a9:	bf 01 00 00 00       	mov    $0x1,%edi
  4024ae:	31 c0                	xor    %eax,%eax
  4024b0:	e8 db eb ff ff       	call   401090 <__printf_chk@plt>
}
  4024b5:	5b                   	pop    %rbx
  4024b6:	5d                   	pop    %rbp
  4024b7:	41 5c                	pop    %r12
  4024b9:	41 5d                	pop    %r13
  4024bb:	41 5e                	pop    %r14
  4024bd:	c3                   	ret
  4024be:	66 90                	xchg   %ax,%ax
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  4024c0:	4c 89 f6             	mov    %r14,%rsi
  4024c3:	bf 04 00 00 00       	mov    $0x4,%edi
  4024c8:	e8 83 eb ff ff       	call   401050 <clock_gettime@plt>
      singlewriter3(data, available, readyreaders, readywriters);
  4024cd:	48 89 ee             	mov    %rbp,%rsi
  4024d0:	48 89 df             	mov    %rbx,%rdi
  4024d3:	4c 89 e9             	mov    %r13,%rcx
  4024d6:	4c 89 e2             	mov    %r12,%rdx
  4024d9:	e8 c2 f4 ff ff       	call   4019a0 <singlewriter3>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swend);
  4024de:	48 8d b3 38 01 00 00 	lea    0x138(%rbx),%rsi
  4024e5:	bf 04 00 00 00       	mov    $0x4,%edi
  4024ea:	e8 61 eb ff ff       	call   401050 <clock_gettime@plt>
  4024ef:	e9 69 ff ff ff       	jmp    40245d <work+0x7d>
  4024f4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4024ff:	90                   	nop

0000000000402500 <work2>:
  while (data->running == 1) {
  402500:	eb 0b                	jmp    40250d <work2+0xd>
  402502:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  402508:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  40250d:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  402511:	74 f5                	je     402508 <work2+0x8>
}
  402513:	c3                   	ret

Disassembly of section .fini:

0000000000402514 <_fini>:
  402514:	f3 0f 1e fa          	endbr64
  402518:	48 83 ec 08          	sub    $0x8,%rsp
  40251c:	48 83 c4 08          	add    $0x8,%rsp
  402520:	c3                   	ret
