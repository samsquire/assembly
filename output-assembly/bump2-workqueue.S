
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
  4010fc:	48 8d 35 24 1f 00 00 	lea    0x1f24(%rip),%rsi        # 403027 <_IO_stdin_used+0x27>
  401103:	41 56                	push   %r14
  long offset = 0;
  long chunkslen = 0xffffffff;
  long worksize = chunkslen * worksize_each;
  int buckets = worksize / threadsize;
  long chunksize = ceil((double) worksize / (double) chunkslen);
  char *works = calloc(worksize, sizeof(char));
  401105:	41 be ff ff ff ff    	mov    $0xffffffff,%r14d
int main(int argc, char **argv) {
  40110b:	41 55                	push   %r13
 // for (int i = 0; i < worksize; i++) {
   // works[i].taskindex = 2;
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  40110d:	45 31 ed             	xor    %r13d,%r13d
int main(int argc, char **argv) {
  401110:	41 54                	push   %r12
  401112:	55                   	push   %rbp
  401113:	53                   	push   %rbx
  401114:	48 83 ec 78          	sub    $0x78,%rsp
  401118:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401121:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  401126:	31 c0                	xor    %eax,%eax
  401128:	e8 83 ff ff ff       	call   4010b0 <__printf_chk@plt>
  40112d:	ba 04 00 00 00       	mov    $0x4,%edx
  401132:	48 8d 35 00 1f 00 00 	lea    0x1f00(%rip),%rsi        # 403039 <_IO_stdin_used+0x39>
  401139:	31 c0                	xor    %eax,%eax
  40113b:	bf 01 00 00 00       	mov    $0x1,%edi
  401140:	e8 6b ff ff ff       	call   4010b0 <__printf_chk@plt>
  401145:	ba 20 00 00 00       	mov    $0x20,%edx
  40114a:	48 8d 35 e4 1e 00 00 	lea    0x1ee4(%rip),%rsi        # 403035 <_IO_stdin_used+0x35>
  401151:	31 c0                	xor    %eax,%eax
  401153:	bf 01 00 00 00       	mov    $0x1,%edi
  401158:	e8 53 ff ff ff       	call   4010b0 <__printf_chk@plt>
  40115d:	ba 05 00 00 00       	mov    $0x5,%edx
  401162:	48 8d 35 df 1e 00 00 	lea    0x1edf(%rip),%rsi        # 403048 <_IO_stdin_used+0x48>
  401169:	31 c0                	xor    %eax,%eax
  40116b:	bf 01 00 00 00       	mov    $0x1,%edi
  401170:	e8 3b ff ff ff       	call   4010b0 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401175:	be 08 00 00 00       	mov    $0x8,%esi
  40117a:	bf 05 00 00 00       	mov    $0x5,%edi
  40117f:	e8 1c ff ff ff       	call   4010a0 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401184:	be 38 00 00 00       	mov    $0x38,%esi
  401189:	bf 05 00 00 00       	mov    $0x5,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40118e:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401193:	e8 08 ff ff ff       	call   4010a0 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401198:	be 80 11 00 00       	mov    $0x1180,%esi
  40119d:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  4011a2:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011a7:	e8 f4 fe ff ff       	call   4010a0 <calloc@plt>
  char *works = calloc(worksize, sizeof(char));
  4011ac:	4c 89 f7             	mov    %r14,%rdi
  4011af:	be 01 00 00 00       	mov    $0x1,%esi
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  4011b4:	48 89 c3             	mov    %rax,%rbx
  char *works = calloc(worksize, sizeof(char));
  4011b7:	e8 e4 fe ff ff       	call   4010a0 <calloc@plt>
  4011bc:	4c 89 f2             	mov    %r14,%rdx
  4011bf:	bf 01 00 00 00       	mov    $0x1,%edi
  4011c4:	48 8d 35 92 1e 00 00 	lea    0x1e92(%rip),%rsi        # 40305d <_IO_stdin_used+0x5d>
  4011cb:	49 89 c4             	mov    %rax,%r12
  4011ce:	31 c0                	xor    %eax,%eax
  4011d0:	e8 db fe ff ff       	call   4010b0 <__printf_chk@plt>
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4011d5:	be 20 00 00 00       	mov    $0x20,%esi
  4011da:	bf 64 00 00 00       	mov    $0x64,%edi
  4011df:	e8 bc fe ff ff       	call   4010a0 <calloc@plt>
  4011e4:	31 d2                	xor    %edx,%edx
  4011e6:	bf 01 00 00 00       	mov    $0x1,%edi
  4011eb:	48 8d 35 7c 1e 00 00 	lea    0x1e7c(%rip),%rsi        # 40306e <_IO_stdin_used+0x6e>
  4011f2:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  4011f7:	31 c0                	xor    %eax,%eax
  4011f9:	e8 b2 fe ff ff       	call   4010b0 <__printf_chk@plt>
  4011fe:	4c 89 f2             	mov    %r14,%rdx
  401201:	bf 01 00 00 00       	mov    $0x1,%edi
  401206:	31 c0                	xor    %eax,%eax
  401208:	48 8d 35 6a 1e 00 00 	lea    0x1e6a(%rip),%rsi        # 403079 <_IO_stdin_used+0x79>
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  data[0].works = works;
  40120f:	49 89 de             	mov    %rbx,%r14
  401212:	e8 99 fe ff ff       	call   4010b0 <__printf_chk@plt>
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  401217:	be 04 00 00 00       	mov    $0x4,%esi
  40121c:	bf 05 00 00 00       	mov    $0x5,%edi
  401221:	e8 7a fe ff ff       	call   4010a0 <calloc@plt>
  401226:	66 48 0f 6e f3       	movq   %rbx,%xmm6
  data[0].works = works;
  40122b:	4c 89 63 70          	mov    %r12,0x70(%rbx)
  40122f:	45 31 e4             	xor    %r12d,%r12d
  401232:	66 48 0f 6e e8       	movq   %rax,%xmm5
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  401237:	48 89 c5             	mov    %rax,%rbp
  40123a:	66 0f 6c ee          	punpcklqdq %xmm6,%xmm5
  40123e:	0f 29 2c 24          	movaps %xmm5,(%rsp)
  for (int x = 0; x < threadsize ; x++) {
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401242:	45 89 ef             	mov    %r13d,%r15d
  401245:	be 80 00 00 00       	mov    $0x80,%esi
  40124a:	bf 01 00 00 00       	mov    $0x1,%edi
    CPU_SET(cpu += 1, data[x].cpu_set);
  40124f:	41 83 c5 01          	add    $0x1,%r13d
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401253:	e8 48 fe ff ff       	call   4010a0 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  401258:	44 89 e9             	mov    %r13d,%ecx
  40125b:	ba 01 00 00 00       	mov    $0x1,%edx
  401260:	48 8d 35 21 1f 00 00 	lea    0x1f21(%rip),%rsi        # 403188 <_IO_stdin_used+0x188>
  401267:	48 d3 e2             	shl    %cl,%rdx
  40126a:	48 09 10             	or     %rdx,(%rax)
  40126d:	44 89 e9             	mov    %r13d,%ecx
  401270:	44 89 fa             	mov    %r15d,%edx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401273:	49 89 46 78          	mov    %rax,0x78(%r14)
  401277:	bf 01 00 00 00       	mov    $0x1,%edi
  40127c:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  40127e:	48 83 c5 04          	add    $0x4,%rbp
  401282:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  401289:	e8 22 fe ff ff       	call   4010b0 <__printf_chk@plt>
    data[x].threadindex = x;
    data[x].worksize = worksize;
    
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].readies = readies;
  40128e:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
    data[x].running = 1;
  401293:	48 8b 05 16 1f 00 00 	mov    0x1f16(%rip),%rax        # 4031b0 <_IO_stdin_used+0x1b0>
    data[x].bucketstart = x * buckets ;
  40129a:	45 89 a6 18 fd ff ff 	mov    %r12d,-0x2e8(%r14)
    data[x].readies[x] = 0;
    data[x].buckets = buckets;
    data[x].main = &data[0];
    data[x].threads = data;
    
    data[x].read = 0;
  4012a1:	66 0f 6f 15 17 1f 00 00 	movdqa 0x1f17(%rip),%xmm2        # 4031c0 <_IO_stdin_used+0x1c0>
    data[x].newmask = 0;
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4012a9:	be 30 00 00 00       	mov    $0x30,%esi
    data[x].chunkslen = chunkslen;
  4012ae:	66 0f 6f 1d 1a 1f 00 00 	movdqa 0x1f1a(%rip),%xmm3        # 4031d0 <_IO_stdin_used+0x1d0>
    data[x].loglevel = debug;
  4012b6:	41 c7 86 00 fd ff ff 00 00 00 00 	movl   $0x0,-0x300(%r14)
    data[x].running = 1;
  4012c1:	49 89 86 dc fc ff ff 	mov    %rax,-0x324(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4012c8:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].buckets = buckets;
  4012cd:	48 8b 05 e4 1e 00 00 	mov    0x1ee4(%rip),%rax        # 4031b8 <_IO_stdin_used+0x1b8>
  for (int x = 0; x < threadsize ; x++) {
  4012d4:	41 81 c4 33 33 33 33 	add    $0x33333333,%r12d
    data[x].prevread = threadsize;
  4012db:	66 0f 6f 25 fd 1e 00 00 	movdqa 0x1efd(%rip),%xmm4        # 4031e0 <_IO_stdin_used+0x1e0>
    data[x].threadindex = x;
  4012e3:	45 89 be e4 fc ff ff 	mov    %r15d,-0x31c(%r14)
    data[x].buckets = buckets;
  4012ea:	49 89 86 10 fd ff ff 	mov    %rax,-0x2f0(%r14)
    data[x].freelist = freelist;
  4012f1:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    data[x].threadsize = threadsize;
  4012f6:	41 c7 86 e8 fc ff ff 05 00 00 00 	movl   $0x5,-0x318(%r14)
    data[x].readies[x] = 0;
  401301:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
    data[x].threads = data;
  401308:	49 89 9e b0 fc ff ff 	mov    %rbx,-0x350(%r14)
    data[x].readcursor = threadsize - 1;
  40130f:	41 c7 86 80 fe ff ff 04 00 00 00 	movl   $0x4,-0x180(%r14)
    data[x].writecursor = threadsize - 1;
  40131a:	41 c7 86 00 fe ff ff 04 00 00 00 	movl   $0x4,-0x200(%r14)
    data[x].freelist = freelist;
  401325:	49 89 86 20 fd ff ff 	mov    %rax,-0x2e0(%r14)
    data[x].newmask = 0;
  40132c:	41 c7 86 48 fd ff ff 00 00 00 00 	movl   $0x0,-0x2b8(%r14)
    data[x].thiswrite = threadsize;
  401337:	41 c7 46 a8 05 00 00 00 	movl   $0x5,-0x58(%r14)
    data[x].readies = readies;
  40133f:	41 0f 29 8e a0 fc ff ff 	movaps %xmm1,-0x360(%r14)
    data[x].read = 0;
  401347:	41 0f 29 96 80 fc ff ff 	movaps %xmm2,-0x380(%r14)
    data[x].chunkslen = chunkslen;
  40134f:	41 0f 11 9e 38 fd ff ff 	movups %xmm3,-0x2c8(%r14)
    data[x].prevread = threadsize;
  401357:	41 0f 11 66 88       	movups %xmm4,-0x78(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40135c:	e8 3f fd ff ff       	call   4010a0 <calloc@plt>
    data[x].epochssize = epochs;
    
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  401361:	be 30 00 00 00       	mov    $0x30,%esi
  401366:	bf 10 27 00 00       	mov    $0x2710,%edi
    data[x].epochssize = epochs;
  40136b:	41 c7 46 a0 80 96 98 00 	movl   $0x989680,-0x60(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401373:	49 89 46 98          	mov    %rax,-0x68(%r14)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  401377:	e8 24 fd ff ff       	call   4010a0 <calloc@plt>
  40137c:	49 89 46 b0          	mov    %rax,-0x50(%r14)
  for (int x = 0; x < threadsize ; x++) {
  401380:	41 83 fd 05          	cmp    $0x5,%r13d
  401384:	0f 85 b8 fe ff ff    	jne    401242 <main+0x152>
  40138a:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
  40138f:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
  401394:	48 89 1c 24          	mov    %rbx,(%rsp)
  401398:	49 89 de             	mov    %rbx,%r14
  40139b:	49 c7 c5 70 20 40 00 	mov    $0x402070,%r13
  4013a2:	48 8d 8d 18 01 00 00 	lea    0x118(%rbp),%rcx
  4013a9:	49 89 c4             	mov    %rax,%r12
  4013ac:	48 89 c3             	mov    %rax,%rbx
  4013af:	49 89 cf             	mov    %rcx,%r15
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  4013b2:	4c 89 f1             	mov    %r14,%rcx
  4013b5:	48 89 ee             	mov    %rbp,%rsi
  4013b8:	48 89 df             	mov    %rbx,%rdi
  4013bb:	4c 89 ea             	mov    %r13,%rdx
  4013be:	e8 fd fc ff ff       	call   4010c0 <pthread_create@plt>
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4013c3:	49 8b 56 78          	mov    0x78(%r14),%rdx
  4013c7:	48 8b 3b             	mov    (%rbx),%rdi
  4013ca:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  4013cf:	48 83 c5 38          	add    $0x38,%rbp
  4013d3:	48 83 c3 08          	add    $0x8,%rbx
  4013d7:	49 81 c6 80 03 00 00 	add    $0x380,%r14
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4013de:	e8 5d fc ff ff       	call   401040 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  4013e3:	4c 39 fd             	cmp    %r15,%rbp
  4013e6:	75 ca                	jne    4013b2 <main+0x2c2>
  }
  
  struct timespec time = {
  4013e8:	48 8b 1c 24          	mov    (%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  4013ec:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  4013f1:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec time = {
  4013f6:	66 0f 6f 05 f2 1d 00 00 	movdqa 0x1df2(%rip),%xmm0        # 4031f0 <_IO_stdin_used+0x1f0>
  4013fe:	4c 8d 6c 24 38       	lea    0x38(%rsp),%r13
  401403:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  401408:	66 0f ef c0          	pxor   %xmm0,%xmm0
  40140c:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  401411:	e8 6a fc ff ff       	call   401080 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  401416:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
  40141b:	c7 43 5c 00 00 00 00 	movl   $0x0,0x5c(%rbx)
  401422:	c7 83 dc 03 00 00 00 00 00 00 	movl   $0x0,0x3dc(%rbx)
  40142c:	c7 83 5c 07 00 00 00 00 00 00 	movl   $0x0,0x75c(%rbx)
  401436:	48 83 c5 28          	add    $0x28,%rbp
  40143a:	c7 83 dc 0a 00 00 00 00 00 00 	movl   $0x0,0xadc(%rbx)
  401444:	c7 83 5c 0e 00 00 00 00 00 00 	movl   $0x0,0xe5c(%rbx)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  40144e:	49 8b 3c 24          	mov    (%r12),%rdi
  401452:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  401455:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  401459:	e8 82 fc ff ff       	call   4010e0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  40145e:	4c 39 e5             	cmp    %r12,%rbp
  401461:	75 eb                	jne    40144e <main+0x35e>
  401463:	48 8d 3d 1b 1c 00 00 	lea    0x1c1b(%rip),%rdi        # 403085 <_IO_stdin_used+0x85>
  40146a:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  40146e:	45 31 e4             	xor    %r12d,%r12d
  401471:	e8 da fb ff ff       	call   401050 <puts@plt>
  for (int x = 0; x < threadsize; x++) {
  401476:	4c 8d b3 c8 11 00 00 	lea    0x11c8(%rbx),%r14
  40147d:	4c 8d 2d 16 1c 00 00 	lea    0x1c16(%rip),%r13        # 40309a <_IO_stdin_used+0x9a>
  401484:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401488:	4c 89 ee             	mov    %r13,%rsi
  40148b:	bf 01 00 00 00       	mov    $0x1,%edi
  401490:	31 c0                	xor    %eax,%eax
  401492:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
  401499:	e8 12 fc ff ff       	call   4010b0 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  40149e:	4c 03 a5 80 fc ff ff 	add    -0x380(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  4014a5:	49 39 ee             	cmp    %rbp,%r14
  4014a8:	75 da                	jne    401484 <main+0x394>
  }
  printf("freq: %ld\n", freq/ seconds);
  printf("freq_ps: %ld\n", (freq*threadsize-1)/ seconds);
  4014aa:	4f 8d 6c a4 ff       	lea    -0x1(%r12,%r12,4),%r13
  4014af:	4c 89 e2             	mov    %r12,%rdx
  4014b2:	bf 01 00 00 00       	mov    $0x1,%edi
  4014b7:	31 c0                	xor    %eax,%eax
  4014b9:	48 8d 35 e5 1b 00 00 	lea    0x1be5(%rip),%rsi        # 4030a5 <_IO_stdin_used+0xa5>
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  4014c0:	bd 00 ca 9a 3b       	mov    $0x3b9aca00,%ebp
  4014c5:	4c 8d b3 d0 11 00 00 	lea    0x11d0(%rbx),%r14
  4014cc:	e8 df fb ff ff       	call   4010b0 <__printf_chk@plt>
  4014d1:	4c 89 ea             	mov    %r13,%rdx
  4014d4:	bf 01 00 00 00       	mov    $0x1,%edi
  4014d9:	31 c0                	xor    %eax,%eax
  4014db:	48 8d 35 ce 1b 00 00 	lea    0x1bce(%rip),%rsi        # 4030b0 <_IO_stdin_used+0xb0>
  4014e2:	e8 c9 fb ff ff       	call   4010b0 <__printf_chk@plt>
  4014e7:	48 89 e8             	mov    %rbp,%rax
  4014ea:	bf 01 00 00 00       	mov    $0x1,%edi
  4014ef:	48 8d 35 c8 1b 00 00 	lea    0x1bc8(%rip),%rsi        # 4030be <_IO_stdin_used+0xbe>
  4014f6:	48 99                	cqto
  4014f8:	49 f7 fc             	idiv   %r12
  printf("freq latency: %ld\n", 1000000000/((freq*threadsize-1)/seconds));
  long freq_writes = 0;
  4014fb:	45 31 e4             	xor    %r12d,%r12d
  4014fe:	48 89 c2             	mov    %rax,%rdx
  401501:	31 c0                	xor    %eax,%eax
  401503:	e8 a8 fb ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*threadsize-1)/seconds));
  401508:	48 89 e8             	mov    %rbp,%rax
  40150b:	bf 01 00 00 00       	mov    $0x1,%edi
  401510:	48 8d 35 bb 1b 00 00 	lea    0x1bbb(%rip),%rsi        # 4030d2 <_IO_stdin_used+0xd2>
  401517:	48 99                	cqto
  401519:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  40151d:	49 f7 fd             	idiv   %r13
  401520:	4c 8d 2d be 1b 00 00 	lea    0x1bbe(%rip),%r13        # 4030e5 <_IO_stdin_used+0xe5>
  401527:	48 89 c2             	mov    %rax,%rdx
  40152a:	31 c0                	xor    %eax,%eax
  40152c:	e8 7f fb ff ff       	call   4010b0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  401531:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401535:	4c 89 ee             	mov    %r13,%rsi
  401538:	bf 01 00 00 00       	mov    $0x1,%edi
  40153d:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  40153f:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
    freq_writes += data[x].freq_writes;
  401546:	49 01 d4             	add    %rdx,%r12
  401549:	e8 62 fb ff ff       	call   4010b0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  40154e:	4c 39 f5             	cmp    %r14,%rbp
  401551:	75 de                	jne    401531 <main+0x441>
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);

  printf("freq_writes_total: %ld\n", (freq_writes * threadsize - 1) / seconds);
  401553:	4f 8d 6c a4 ff       	lea    -0x1(%r12,%r12,4),%r13
  401558:	4c 89 e2             	mov    %r12,%rdx
  40155b:	bf 01 00 00 00       	mov    $0x1,%edi
  401560:	31 c0                	xor    %eax,%eax
  401562:	48 8d 35 88 1b 00 00 	lea    0x1b88(%rip),%rsi        # 4030f1 <_IO_stdin_used+0xf1>
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  401569:	bd 00 ca 9a 3b       	mov    $0x3b9aca00,%ebp
  40156e:	4c 8d b3 20 03 00 00 	lea    0x320(%rbx),%r14
  401575:	e8 36 fb ff ff       	call   4010b0 <__printf_chk@plt>
  40157a:	4c 89 ea             	mov    %r13,%rdx
  40157d:	bf 01 00 00 00       	mov    $0x1,%edi
  401582:	31 c0                	xor    %eax,%eax
  401584:	48 8d 35 78 1b 00 00 	lea    0x1b78(%rip),%rsi        # 403103 <_IO_stdin_used+0x103>
  40158b:	e8 20 fb ff ff       	call   4010b0 <__printf_chk@plt>
  401590:	48 89 e8             	mov    %rbp,%rax
  401593:	bf 01 00 00 00       	mov    $0x1,%edi
  401598:	48 8d 35 7c 1b 00 00 	lea    0x1b7c(%rip),%rsi        # 40311b <_IO_stdin_used+0x11b>
  40159f:	48 99                	cqto
  4015a1:	49 f7 fc             	idiv   %r12
  4015a4:	48 89 c2             	mov    %rax,%rdx
  4015a7:	31 c0                	xor    %eax,%eax
  4015a9:	e8 02 fb ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * threadsize - 1) / seconds));
  4015ae:	48 89 e8             	mov    %rbp,%rax
  4015b1:	bf 01 00 00 00       	mov    $0x1,%edi
  4015b6:	48 8d 35 79 1b 00 00 	lea    0x1b79(%rip),%rsi        # 403136 <_IO_stdin_used+0x136>
  4015bd:	48 99                	cqto
  4015bf:	48 8d 2d 07 1b 00 00 	lea    0x1b07(%rip),%rbp        # 4030cd <_IO_stdin_used+0xcd>
  4015c6:	49 f7 fd             	idiv   %r13
  4015c9:	48 89 c2             	mov    %rax,%rdx
  4015cc:	31 c0                	xor    %eax,%eax
  4015ce:	e8 dd fa ff ff       	call   4010b0 <__printf_chk@plt>
  4015d3:	48 8d 3d 76 1b 00 00 	lea    0x1b76(%rip),%rdi        # 403150 <_IO_stdin_used+0x150>
  4015da:	e8 71 fa ff ff       	call   401050 <puts@plt>
  4015df:	48 89 ee             	mov    %rbp,%rsi
  4015e2:	bf 01 00 00 00       	mov    $0x1,%edi
  4015e7:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  4015e9:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  4015f0:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4015f7:	e8 b4 fa ff ff       	call   4010b0 <__printf_chk@plt>
  4015fc:	48 89 ee             	mov    %rbp,%rsi
  4015ff:	bf 01 00 00 00       	mov    $0x1,%edi
  401604:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  401606:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  40160d:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  401614:	e8 97 fa ff ff       	call   4010b0 <__printf_chk@plt>
  401619:	48 89 ee             	mov    %rbp,%rsi
  40161c:	bf 01 00 00 00       	mov    $0x1,%edi
  401621:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  401623:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  40162a:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401631:	e8 7a fa ff ff       	call   4010b0 <__printf_chk@plt>
  401636:	48 89 ee             	mov    %rbp,%rsi
  401639:	bf 01 00 00 00       	mov    $0x1,%edi
  40163e:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  401640:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  401647:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  40164e:	e8 5d fa ff ff       	call   4010b0 <__printf_chk@plt>
  401653:	48 89 ee             	mov    %rbp,%rsi
  401656:	bf 01 00 00 00       	mov    $0x1,%edi
  40165b:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  40165d:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401664:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  40166b:	e8 40 fa ff ff       	call   4010b0 <__printf_chk@plt>
  401670:	48 89 ee             	mov    %rbp,%rsi
  401673:	bf 01 00 00 00       	mov    $0x1,%edi
  401678:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  40167a:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401681:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401688:	e8 23 fa ff ff       	call   4010b0 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  40168d:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  401694:	bf 01 00 00 00       	mov    $0x1,%edi
  401699:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  4016a0:	48 8d 35 b6 1a 00 00 	lea    0x1ab6(%rip),%rsi        # 40315d <_IO_stdin_used+0x15d>
  4016a7:	31 c0                	xor    %eax,%eax
  4016a9:	48 81 c3 a0 14 00 00 	add    $0x14a0,%rbx
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  4016b0:	45 31 ed             	xor    %r13d,%r13d
  4016b3:	e8 f8 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  } 

  if (SAMPLE == 1) {
  char * filename = calloc(100, sizeof(char));
  4016b8:	be 01 00 00 00       	mov    $0x1,%esi
  4016bd:	bf 64 00 00 00       	mov    $0x64,%edi
  4016c2:	e8 d9 f9 ff ff       	call   4010a0 <calloc@plt>
  char * buf = calloc(1000, sizeof(char));
  4016c7:	be 01 00 00 00       	mov    $0x1,%esi
  4016cc:	bf e8 03 00 00       	mov    $0x3e8,%edi
  char * filename = calloc(100, sizeof(char));
  4016d1:	49 89 c4             	mov    %rax,%r12
  char * buf = calloc(1000, sizeof(char));
  4016d4:	e8 c7 f9 ff ff       	call   4010a0 <calloc@plt>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  4016d9:	44 8b 8b c8 eb ff ff 	mov    -0x1438(%rbx),%r9d
  4016e0:	4c 89 e7             	mov    %r12,%rdi
  4016e3:	4c 8d 05 7b 1a 00 00 	lea    0x1a7b(%rip),%r8        # 403165 <_IO_stdin_used+0x165>
  4016ea:	b9 64 00 00 00       	mov    $0x64,%ecx
  4016ef:	ba 01 00 00 00       	mov    $0x1,%edx
  4016f4:	be 64 00 00 00       	mov    $0x64,%esi
  4016f9:	48 89 c5             	mov    %rax,%rbp
  4016fc:	31 c0                	xor    %eax,%eax
  4016fe:	e8 2d f9 ff ff       	call   401030 <__snprintf_chk@plt>
  memset(filename, 0, 100);
  snprintf(filename, 100, "samples%d", data->threadsize);
  FILE *out_file = fopen(filename, "w");
  401703:	4c 89 e7             	mov    %r12,%rdi
  401706:	48 8d 35 62 1a 00 00 	lea    0x1a62(%rip),%rsi        # 40316f <_IO_stdin_used+0x16f>
  40170d:	e8 be f9 ff ff       	call   4010d0 <fopen@plt>
  401712:	49 89 c4             	mov    %rax,%r12
  
  for (int x = 0; x < threadsize; x++) {
    for (int y = 0; y < data[x].epochssize; y++) {
  401715:	41 8b 0e             	mov    (%r14),%ecx
  401718:	45 31 ff             	xor    %r15d,%r15d
  40171b:	85 c9                	test   %ecx,%ecx
  40171d:	7e 21                	jle    401740 <main+0x650>
  40171f:	49 8b 76 f8          	mov    -0x8(%r14),%rsi
      struct Epoch * epoch = &data[x].epochs[y];
  401723:	49 63 c7             	movslq %r15d,%rax
  401726:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  40172a:	48 c1 e2 04          	shl    $0x4,%rdx
  40172e:	48 01 f2             	add    %rsi,%rdx
      if (epoch->set == 1) {
  401731:	83 7a 24 01          	cmpl   $0x1,0x24(%rdx)
  401735:	74 41                	je     401778 <main+0x688>
    for (int y = 0; y < data[x].epochssize; y++) {
  401737:	41 83 c7 01          	add    $0x1,%r15d
  40173b:	41 39 cf             	cmp    %ecx,%r15d
  40173e:	7c e3                	jl     401723 <main+0x633>
  for (int x = 0; x < threadsize; x++) {
  401740:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  401747:	49 39 de             	cmp    %rbx,%r14
  40174a:	75 c9                	jne    401715 <main+0x625>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  40174c:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  401751:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40175a:	0f 85 93 00 00 00    	jne    4017f3 <main+0x703>
  401760:	48 83 c4 78          	add    $0x78,%rsp
  401764:	31 c0                	xor    %eax,%eax
  401766:	5b                   	pop    %rbx
  401767:	5d                   	pop    %rbp
  401768:	41 5c                	pop    %r12
  40176a:	41 5d                	pop    %r13
  40176c:	41 5e                	pop    %r14
  40176e:	41 5f                	pop    %r15
  401770:	c3                   	ret
  401771:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401778:	4c 89 e8             	mov    %r13,%rax
  40177b:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401780:	48 89 ef             	mov    %rbp,%rdi
  401783:	48 83 ec 08          	sub    $0x8,%rsp
  401787:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  40178a:	be 64 00 00 00       	mov    $0x64,%esi
  40178f:	48 89 ef             	mov    %rbp,%rdi
    for (int y = 0; y < data[x].epochssize; y++) {
  401792:	41 83 c7 01          	add    $0x1,%r15d
  401796:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  40179b:	4c 8d 05 cf 19 00 00 	lea    0x19cf(%rip),%r8        # 403171 <_IO_stdin_used+0x171>
  4017a2:	8b 42 28             	mov    0x28(%rdx),%eax
  4017a5:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
  4017a9:	50                   	push   %rax
  4017aa:	8b 02                	mov    (%rdx),%eax
  4017ac:	50                   	push   %rax
  4017ad:	8b 42 20             	mov    0x20(%rdx),%eax
  4017b0:	ff 72 18             	push   0x18(%rdx)
  4017b3:	50                   	push   %rax
  4017b4:	31 c0                	xor    %eax,%eax
  4017b6:	ff 72 10             	push   0x10(%rdx)
  4017b9:	ba 01 00 00 00       	mov    $0x1,%edx
  4017be:	e8 6d f8 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  4017c3:	48 83 c4 30          	add    $0x30,%rsp
  4017c7:	4c 89 e6             	mov    %r12,%rsi
  4017ca:	48 89 ef             	mov    %rbp,%rdi
  4017cd:	e8 be f8 ff ff       	call   401090 <fputs@plt>
  4017d2:	41 8b 0e             	mov    (%r14),%ecx
  4017d5:	41 39 cf             	cmp    %ecx,%r15d
  4017d8:	0f 8c 41 ff ff ff    	jl     40171f <main+0x62f>
  for (int x = 0; x < threadsize; x++) {
  4017de:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  4017e5:	49 39 de             	cmp    %rbx,%r14
  4017e8:	0f 85 27 ff ff ff    	jne    401715 <main+0x625>
  4017ee:	e9 59 ff ff ff       	jmp    40174c <main+0x65c>
  4017f3:	e8 78 f8 ff ff       	call   401070 <__stack_chk_fail@plt>
  4017f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000401800 <_start>:
  401800:	f3 0f 1e fa          	endbr64
  401804:	31 ed                	xor    %ebp,%ebp
  401806:	49 89 d1             	mov    %rdx,%r9
  401809:	5e                   	pop    %rsi
  40180a:	48 89 e2             	mov    %rsp,%rdx
  40180d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401811:	50                   	push   %rax
  401812:	54                   	push   %rsp
  401813:	45 31 c0             	xor    %r8d,%r8d
  401816:	31 c9                	xor    %ecx,%ecx
  401818:	48 c7 c7 f0 10 40 00 	mov    $0x4010f0,%rdi
  40181f:	ff 15 cb 37 00 00    	call   *0x37cb(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  401825:	f4                   	hlt
  401826:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401830 <_dl_relocate_static_pie>:
  401830:	f3 0f 1e fa          	endbr64
  401834:	c3                   	ret
  401835:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40183f:	90                   	nop

0000000000401840 <deregister_tm_clones>:
  401840:	b8 10 50 40 00       	mov    $0x405010,%eax
  401845:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  40184b:	74 13                	je     401860 <deregister_tm_clones+0x20>
  40184d:	b8 00 00 00 00       	mov    $0x0,%eax
  401852:	48 85 c0             	test   %rax,%rax
  401855:	74 09                	je     401860 <deregister_tm_clones+0x20>
  401857:	bf 10 50 40 00       	mov    $0x405010,%edi
  40185c:	ff e0                	jmp    *%rax
  40185e:	66 90                	xchg   %ax,%ax
  401860:	c3                   	ret
  401861:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40186c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401870 <register_tm_clones>:
  401870:	be 10 50 40 00       	mov    $0x405010,%esi
  401875:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  40187c:	48 89 f0             	mov    %rsi,%rax
  40187f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401883:	48 c1 f8 03          	sar    $0x3,%rax
  401887:	48 01 c6             	add    %rax,%rsi
  40188a:	48 d1 fe             	sar    %rsi
  40188d:	74 11                	je     4018a0 <register_tm_clones+0x30>
  40188f:	b8 00 00 00 00       	mov    $0x0,%eax
  401894:	48 85 c0             	test   %rax,%rax
  401897:	74 07                	je     4018a0 <register_tm_clones+0x30>
  401899:	bf 10 50 40 00       	mov    $0x405010,%edi
  40189e:	ff e0                	jmp    *%rax
  4018a0:	c3                   	ret
  4018a1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4018ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004018b0 <__do_global_dtors_aux>:
  4018b0:	f3 0f 1e fa          	endbr64
  4018b4:	80 3d 55 37 00 00 00 	cmpb   $0x0,0x3755(%rip)        # 405010 <__TMC_END__>
  4018bb:	75 13                	jne    4018d0 <__do_global_dtors_aux+0x20>
  4018bd:	55                   	push   %rbp
  4018be:	48 89 e5             	mov    %rsp,%rbp
  4018c1:	e8 7a ff ff ff       	call   401840 <deregister_tm_clones>
  4018c6:	c6 05 43 37 00 00 01 	movb   $0x1,0x3743(%rip)        # 405010 <__TMC_END__>
  4018cd:	5d                   	pop    %rbp
  4018ce:	c3                   	ret
  4018cf:	90                   	nop
  4018d0:	c3                   	ret
  4018d1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4018dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004018e0 <frame_dummy>:
  4018e0:	f3 0f 1e fa          	endbr64
  4018e4:	eb 8a                	jmp    401870 <register_tm_clones>
  4018e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004018f0 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  4018f0:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4018f4:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  4018f7:	7e 77                	jle    401970 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  4018f9:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4018fd:	55                   	push   %rbp
  4018fe:	49 89 f2             	mov    %rsi,%r10
  401901:	49 89 d3             	mov    %rdx,%r11
  401904:	53                   	push   %rbx
  401905:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  401908:	48 8b 98 a0 03 00 00 	mov    0x3a0(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  40190f:	b8 01 00 00 00       	mov    $0x1,%eax
  401914:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  401918:	48 63 d0             	movslq %eax,%rdx
  40191b:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  40191e:	85 d2                	test   %edx,%edx
  401920:	40 0f 94 c6          	sete   %sil
  401924:	f6 c2 04             	test   $0x4,%dl
  401927:	75 05                	jne    40192e <pollthreads+0x3e>
  401929:	40 84 f6             	test   %sil,%sil
  40192c:	74 0d                	je     40193b <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  40192e:	49 63 08             	movslq (%r8),%rcx
  401931:	8d 69 01             	lea    0x1(%rcx),%ebp
  401934:	41 89 28             	mov    %ebp,(%r8)
  401937:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  40193b:	83 e2 08             	and    $0x8,%edx
  40193e:	75 05                	jne    401945 <pollthreads+0x55>
  401940:	40 84 f6             	test   %sil,%sil
  401943:	74 1b                	je     401960 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  401945:	48 63 17             	movslq (%rdi),%rdx
  401948:	8d 4a 01             	lea    0x1(%rdx),%ecx
  40194b:	89 0f                	mov    %ecx,(%rdi)
  40194d:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  401951:	83 c0 01             	add    $0x1,%eax
  401954:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401958:	7f be                	jg     401918 <pollthreads+0x28>
}
  40195a:	31 c0                	xor    %eax,%eax
  40195c:	5b                   	pop    %rbx
  40195d:	5d                   	pop    %rbp
  40195e:	c3                   	ret
  40195f:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  401960:	83 c0 01             	add    $0x1,%eax
  401963:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401967:	7f af                	jg     401918 <pollthreads+0x28>
}
  401969:	31 c0                	xor    %eax,%eax
  40196b:	5b                   	pop    %rbx
  40196c:	5d                   	pop    %rbp
  40196d:	c3                   	ret
  40196e:	66 90                	xchg   %ax,%ax
  401970:	31 c0                	xor    %eax,%eax
  401972:	c3                   	ret
  401973:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40197e:	66 90                	xchg   %ax,%ax

0000000000401980 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401980:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401983:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
      if (*availableidx == 0) {
  40198a:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40198d:	48 83 c7 01          	add    $0x1,%rdi
  401991:	48 85 ff             	test   %rdi,%rdi
  401994:	7e 66                	jle    4019fc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401996:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  40199d:	31 c9                	xor    %ecx,%ecx
  40199f:	45 31 c9             	xor    %r9d,%r9d
  4019a2:	31 c0                	xor    %eax,%eax
  4019a4:	eb 18                	jmp    4019be <findavailable+0x3e>
  4019a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4019b0:	83 c1 01             	add    $0x1,%ecx
  4019b3:	48 63 c1             	movslq %ecx,%rax
  4019b6:	49 89 c1             	mov    %rax,%r9
  4019b9:	48 39 f8             	cmp    %rdi,%rax
  4019bc:	7d 3e                	jge    4019fc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  4019be:	48 c1 e0 05          	shl    $0x5,%rax
  4019c2:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  4019c8:	75 e6                	jne    4019b0 <findavailable+0x30>
         available[*availableidx] = x;
  4019ca:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  4019cd:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  4019d1:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  4019d5:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  4019d8:	41 8b 43 68          	mov    0x68(%r11),%eax
  4019dc:	01 c0                	add    %eax,%eax
  4019de:	41 39 c0             	cmp    %eax,%r8d
  4019e1:	74 19                	je     4019fc <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4019e3:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  4019ea:	83 c1 01             	add    $0x1,%ecx
  4019ed:	48 63 c1             	movslq %ecx,%rax
  4019f0:	48 83 c7 01          	add    $0x1,%rdi
  4019f4:	49 89 c1             	mov    %rax,%r9
  4019f7:	48 39 f8             	cmp    %rdi,%rax
  4019fa:	7c c2                	jl     4019be <findavailable+0x3e>
      if (*availableidx == 0) {
  4019fc:	31 c0                	xor    %eax,%eax
  4019fe:	45 85 c0             	test   %r8d,%r8d
  401a01:	0f 94 c0             	sete   %al
}
  401a04:	c3                   	ret
  401a05:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401a10 <singlewriter3>:
  if (data->writecursor != 0 && (data->writecursor % (data->threadsize - 1)) == 0) {
  401a10:	8b 87 80 01 00 00    	mov    0x180(%rdi),%eax
  401a16:	85 c0                	test   %eax,%eax
  401a18:	74 17                	je     401a31 <singlewriter3+0x21>
  401a1a:	8b 77 68             	mov    0x68(%rdi),%esi
  401a1d:	99                   	cltd
  401a1e:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401a21:	f7 f9                	idiv   %ecx
  401a23:	85 d2                	test   %edx,%edx
  401a25:	75 0a                	jne    401a31 <singlewriter3+0x21>
    data->writecursor = 0;
  401a27:	c7 87 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rdi)
}
  401a31:	c3                   	ret
  401a32:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401a3d:	0f 1f 00             	nopl   (%rax)

0000000000401a40 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401a40:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  401a46:	85 c0                	test   %eax,%eax
  401a48:	74 1e                	je     401a68 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a4a:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401a4c:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401a4d:	55                   	push   %rbp
  401a4e:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401a4f:	8b 77 68             	mov    0x68(%rdi),%esi
  401a52:	48 89 fb             	mov    %rdi,%rbx
  401a55:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401a58:	f7 f9                	idiv   %ecx
  401a5a:	85 d2                	test   %edx,%edx
  401a5c:	74 12                	je     401a70 <singlewriter2+0x30>
}
  401a5e:	5b                   	pop    %rbx
  401a5f:	5d                   	pop    %rbp
  401a60:	41 5c                	pop    %r12
  401a62:	c3                   	ret
  401a63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401a68:	c3                   	ret
  401a69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    data->readcursor = 0;
  401a70:	c7 87 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdi)
        struct Data * thread = &data->threads[data->threadindex];
  401a7a:	48 63 47 64          	movslq 0x64(%rdi),%rax
  401a7e:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  401a86:	48 29 c5             	sub    %rax,%rbp
  401a89:	48 c1 e5 07          	shl    $0x7,%rbp
  401a8d:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401a91:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401a96:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401a9d:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401aa1:	49 c1 e4 04          	shl    $0x4,%r12
  401aa5:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401aac:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401ab1:	e8 aa f5 ff ff       	call   401060 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ab6:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401abc:	83 c0 01             	add    $0x1,%eax
  401abf:	99                   	cltd
  401ac0:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  401ac6:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ac9:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401acf:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401ad3:	48 8b 05 ce 16 00 00 	mov    0x16ce(%rip),%rax        # 4031a8 <_IO_stdin_used+0x1a8>
  401ada:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  401adf:	5b                   	pop    %rbx
  401ae0:	5d                   	pop    %rbp
  401ae1:	41 5c                	pop    %r12
  401ae3:	c3                   	ret
  401ae4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401aef:	90                   	nop

0000000000401af0 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401af0:	41 55                	push   %r13
  401af2:	49 89 d5             	mov    %rdx,%r13
  401af5:	41 54                	push   %r12
  401af7:	49 89 cc             	mov    %rcx,%r12
  401afa:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401afb:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401afe:	48 89 fd             	mov    %rdi,%rbp
  401b01:	53                   	push   %rbx
  401b02:	48 89 f3             	mov    %rsi,%rbx
  401b05:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401b09:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b0d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401b16:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401b1b:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401b1d:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401b25:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  401b2b:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401b33:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401b3b:	83 c0 01             	add    $0x1,%eax
  401b3e:	99                   	cltd
  401b3f:	f7 7f 68             	idivl  0x68(%rdi)
  401b42:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401b48:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401b4d:	4c 89 e9             	mov    %r13,%rcx
  401b50:	e8 2b fe ff ff       	call   401980 <findavailable>
  if (fill == 1) {
  401b55:	83 f8 01             	cmp    $0x1,%eax
  401b58:	0f 84 64 01 00 00    	je     401cc2 <singlewriter+0x1d2>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401b5e:	48 89 ef             	mov    %rbp,%rdi
  401b61:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401b66:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401b6b:	4c 89 e2             	mov    %r12,%rdx
  401b6e:	4c 89 ee             	mov    %r13,%rsi
  401b71:	e8 7a fd ff ff       	call   4018f0 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401b76:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401b7b:	85 ff                	test   %edi,%edi
  401b7d:	0f 8e 66 01 00 00    	jle    401ce9 <singlewriter+0x1f9>
  401b83:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401b88:	31 c9                	xor    %ecx,%ecx
  401b8a:	eb 62                	jmp    401bee <singlewriter+0xfe>
  401b8c:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b90:	48 8b 14 cb          	mov    (%rbx,%rcx,8),%rdx
          int thread = readyreaders[x];
  401b94:	4d 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%r10
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401b99:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401b9c:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401ba0:	48 c1 e2 05          	shl    $0x5,%rdx
  401ba4:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].reading = chunk;
  401bab:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
          data->threads[thread].start = start;
  401bb3:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401bb7:	66 0f 6e 4a 08       	movd   0x8(%rdx),%xmm1
          data->threads[thread].reading = chunk;
  401bbc:	4c 29 d0             	sub    %r10,%rax
          chunk->available = READING;
  401bbf:	c7 42 10 02 00 00 00 	movl   $0x2,0x10(%rdx)
          data->threads[thread].reading = chunk;
  401bc6:	48 c1 e0 07          	shl    $0x7,%rax
  401bca:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].start = start;
  401bce:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401bd2:	48 89 90 a8 00 00 00 	mov    %rdx,0xa8(%rax)
          chunk->owner = thread;
  401bd9:	44 89 52 14          	mov    %r10d,0x14(%rdx)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401bdd:	83 88 c8 00 00 00 10 	orl    $0x10,0xc8(%rax)
          data->threads[thread].start = start;
  401be4:	66 0f d6 40 14       	movq   %xmm0,0x14(%rax)
        for (int x = 0; x < readers ; x++) {
  401be9:	48 39 cf             	cmp    %rcx,%rdi
  401bec:	74 07                	je     401bf5 <singlewriter+0x105>
  401bee:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401bf0:	4c 39 c1             	cmp    %r8,%rcx
  401bf3:	75 9b                	jne    401b90 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401bf5:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401bfa:	45 85 c0             	test   %r8d,%r8d
  401bfd:	7e 7a                	jle    401c79 <singlewriter+0x189>
                if (assignedchunk  == availableidx) {
  401bff:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401c03:	41 01 f0             	add    %esi,%r8d
  401c06:	eb 6d                	jmp    401c75 <singlewriter+0x185>
  401c08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c10:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401c13:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401c16:	45 8b 0c 24          	mov    (%r12),%r9d
   for (int x = 0; x < writers ; x++) {
  401c1a:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c1e:	48 8b 14 f3          	mov    (%rbx,%rsi,8),%rdx
          data->threads[thread].writing = chunk;
  401c22:	49 63 f1             	movslq %r9d,%rsi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c25:	48 c1 e2 05          	shl    $0x5,%rdx
  401c29:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].writing = chunk;
  401c30:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
          data->threads[thread].publishstart = start;
  401c38:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401c3c:	66 0f 6e 52 08       	movd   0x8(%rdx),%xmm2
          data->threads[thread].writing = chunk;
  401c41:	48 29 f0             	sub    %rsi,%rax
      chunk->available = WRITING;
  401c44:	c7 42 10 03 00 00 00 	movl   $0x3,0x10(%rdx)
          data->threads[thread].writing = chunk;
  401c4b:	48 c1 e0 07          	shl    $0x7,%rax
  401c4f:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].publishstart = start;
  401c53:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401c57:	48 89 90 b0 00 00 00 	mov    %rdx,0xb0(%rax)
          chunk->owner = thread;
  401c5e:	44 89 4a 14          	mov    %r9d,0x14(%rdx)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401c62:	83 88 c8 00 00 00 20 	orl    $0x20,0xc8(%rax)
          data->threads[thread].publishstart = start;
  401c69:	66 0f d6 40 40       	movq   %xmm0,0x40(%rax)
   for (int x = 0; x < writers ; x++) {
  401c6e:	44 39 c1             	cmp    %r8d,%ecx
  401c71:	74 06                	je     401c79 <singlewriter+0x189>
  401c73:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401c75:	39 f7                	cmp    %esi,%edi
  401c77:	75 97                	jne    401c10 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401c79:	8b 7d 68             	mov    0x68(%rbp),%edi
  401c7c:	85 ff                	test   %edi,%edi
  401c7e:	7e 40                	jle    401cc0 <singlewriter+0x1d0>
        if (data->threads[x].newmask != 0) {
  401c80:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401c84:	31 d2                	xor    %edx,%edx
  401c86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401c90:	48 63 ca             	movslq %edx,%rcx
  401c93:	48 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rax
  401c9b:	48 29 c8             	sub    %rcx,%rax
  401c9e:	48 c1 e0 07          	shl    $0x7,%rax
  401ca2:	4c 01 c0             	add    %r8,%rax
  401ca5:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401cab:	85 f6                	test   %esi,%esi
  401cad:	74 31                	je     401ce0 <singlewriter+0x1f0>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401caf:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401cb3:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401cb6:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401cb9:	8b 7d 68             	mov    0x68(%rbp),%edi
  401cbc:	39 fa                	cmp    %edi,%edx
  401cbe:	7c d0                	jl     401c90 <singlewriter+0x1a0>
  return 0;
  401cc0:	31 c0                	xor    %eax,%eax
}
  401cc2:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401cc7:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401cd0:	75 1e                	jne    401cf0 <singlewriter+0x200>
  401cd2:	48 83 c4 28          	add    $0x28,%rsp
  401cd6:	5b                   	pop    %rbx
  401cd7:	5d                   	pop    %rbp
  401cd8:	41 5c                	pop    %r12
  401cda:	41 5d                	pop    %r13
  401cdc:	c3                   	ret
  401cdd:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401ce0:	83 c2 01             	add    $0x1,%edx
  401ce3:	39 fa                	cmp    %edi,%edx
  401ce5:	7c a9                	jl     401c90 <singlewriter+0x1a0>
  401ce7:	eb d7                	jmp    401cc0 <singlewriter+0x1d0>
      int assignedchunk = 0;
  401ce9:	31 f6                	xor    %esi,%esi
  401ceb:	e9 05 ff ff ff       	jmp    401bf5 <singlewriter+0x105>
}
  401cf0:	e8 7b f3 ff ff       	call   401070 <__stack_chk_fail@plt>
  401cf5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401d00 <threadwork>:
int * threadwork(struct Data * data) {
  401d00:	41 57                	push   %r15
  401d02:	41 56                	push   %r14
  401d04:	41 55                	push   %r13
  401d06:	41 54                	push   %r12
  401d08:	55                   	push   %rbp
  401d09:	53                   	push   %rbx
  401d0a:	48 89 fb             	mov    %rdi,%rbx
  401d0d:	48 83 ec 28          	sub    $0x28,%rsp
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401d11:	48 63 4f 68          	movslq 0x68(%rdi),%rcx
  401d15:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401d1e:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401d23:	48 8b 47 28          	mov    0x28(%rdi),%rax
  long lastcursor = data->main->writecursor;
  401d27:	8b b0 80 01 00 00    	mov    0x180(%rax),%esi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401d2d:	48 8b 80 38 03 00 00 	mov    0x338(%rax),%rax
  401d34:	48 99                	cqto
    data->thiswrite = lastcursor;
  401d36:	89 b7 28 03 00 00    	mov    %esi,0x328(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401d3c:	48 89 e6             	mov    %rsp,%rsi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401d3f:	48 f7 f9             	idiv   %rcx
    data->prevwrite = lastwrite;
  401d42:	48 89 97 10 03 00 00 	mov    %rdx,0x310(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401d49:	bf 04 00 00 00       	mov    $0x4,%edi
  401d4e:	e8 0d f3 ff ff       	call   401060 <clock_gettime@plt>
     for (int x = 2; x < data->threadsize ; x++) {
  401d53:	8b 43 68             	mov    0x68(%rbx),%eax
   data->freq_writes++;
  401d56:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
     for (int x = 2; x < data->threadsize ; x++) {
  401d5b:	b9 02 00 00 00       	mov    $0x2,%ecx
  401d60:	83 f8 02             	cmp    $0x2,%eax
  401d63:	0f 8f f8 00 00 00    	jg     401e61 <threadwork+0x161>
  401d69:	e9 05 01 00 00       	jmp    401e73 <threadwork+0x173>
  401d6e:	66 90                	xchg   %ax,%ax
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401d70:	48 63 83 80 01 00 00 	movslq 0x180(%rbx),%rax
  401d77:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
        epoch->time = time;
  401d7b:	66 0f 6f 04 24       	movdqa (%rsp),%xmm0
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401d80:	48 89 c2             	mov    %rax,%rdx
  401d83:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401d8a:	41 89 d0             	mov    %edx,%r8d
  401d8d:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401d91:	48 c1 e8 20          	shr    $0x20,%rax
  401d95:	01 d0                	add    %edx,%eax
  401d97:	c1 f8 03             	sar    $0x3,%eax
  401d9a:	44 29 c0             	sub    %r8d,%eax
  401d9d:	41 89 c0             	mov    %eax,%r8d
  401da0:	41 c1 e0 04          	shl    $0x4,%r8d
  401da4:	41 29 c0             	sub    %eax,%r8d
  401da7:	89 f0                	mov    %esi,%eax
  401da9:	44 29 c2             	sub    %r8d,%edx
  401dac:	c1 e0 18             	shl    $0x18,%eax
  401daf:	09 c2                	or     %eax,%edx
  401db1:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  401db8:	41 89 d2             	mov    %edx,%r10d
  401dbb:	48 89 c2             	mov    %rax,%rdx
  401dbe:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401dc5:	41 89 d0             	mov    %edx,%r8d
  401dc8:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401dcc:	48 c1 e8 20          	shr    $0x20,%rax
  401dd0:	01 d0                	add    %edx,%eax
  401dd2:	c1 f8 03             	sar    $0x3,%eax
  401dd5:	44 29 c0             	sub    %r8d,%eax
  401dd8:	41 89 c0             	mov    %eax,%r8d
  401ddb:	41 c1 e0 04          	shl    $0x4,%r8d
  401ddf:	41 29 c0             	sub    %eax,%r8d
  401de2:	89 c8                	mov    %ecx,%eax
  401de4:	44 29 c2             	sub    %r8d,%edx
  401de7:	c1 e0 08             	shl    $0x8,%eax
  401dea:	c1 e2 10             	shl    $0x10,%edx
  401ded:	41 09 d2             	or     %edx,%r10d
  401df0:	41 09 c2             	or     %eax,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  401df3:	48 63 c6             	movslq %esi,%rax
  401df6:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401dfe:	4d 63 d2             	movslq %r10d,%r10
        struct Data * thread = &data->threads[data->threadindex];
  401e01:	49 29 c0             	sub    %rax,%r8
  401e04:	49 c1 e0 07          	shl    $0x7,%r8
  401e08:	4c 03 43 30          	add    0x30(%rbx),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401e0c:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  401e13:	48 89 d0             	mov    %rdx,%rax
  401e16:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e1a:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401e1d:	49 c1 e1 04          	shl    $0x4,%r9
  401e21:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e28:	99                   	cltd
        epoch->time = time;
  401e29:	41 0f 11 41 08       	movups %xmm0,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e2e:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
  data->main->works[buffer] = data->threadindex;
  401e35:	48 8b 47 70          	mov    0x70(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401e39:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
  epoch->dest = x;
  401e40:	41 89 49 28          	mov    %ecx,0x28(%r9)
     for (int x = 2; x < data->threadsize ; x++) {
  401e44:	83 c1 01             	add    $0x1,%ecx
        epoch->thread = data->threadindex;
  401e47:	41 89 31             	mov    %esi,(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401e4a:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  401e4e:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
  data->main->works[buffer] = data->threadindex;
  401e56:	42 88 34 10          	mov    %sil,(%rax,%r10,1)
     for (int x = 2; x < data->threadsize ; x++) {
  401e5a:	8b 43 68             	mov    0x68(%rbx),%eax
  401e5d:	39 c1                	cmp    %eax,%ecx
  401e5f:	7d 12                	jge    401e73 <threadwork+0x173>
  401e61:	8b 73 64             	mov    0x64(%rbx),%esi
     if (x != data->threadindex) {
  401e64:	39 ce                	cmp    %ecx,%esi
  401e66:	0f 85 04 ff ff ff    	jne    401d70 <threadwork+0x70>
     for (int x = 2; x < data->threadsize ; x++) {
  401e6c:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401e6f:	39 c1                	cmp    %eax,%ecx
  401e71:	7c f1                	jl     401e64 <threadwork+0x164>
    data->writecursor = (data->writecursor + 1) % 0xf;
  401e73:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
  401e79:	8d 50 01             	lea    0x1(%rax),%edx
  401e7c:	48 63 c2             	movslq %edx,%rax
  401e7f:	89 d1                	mov    %edx,%ecx
  401e81:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401e88:	c1 f9 1f             	sar    $0x1f,%ecx
  401e8b:	48 c1 e8 20          	shr    $0x20,%rax
  401e8f:	01 d0                	add    %edx,%eax
  401e91:	c1 f8 03             	sar    $0x3,%eax
  401e94:	29 c8                	sub    %ecx,%eax
  401e96:	89 c1                	mov    %eax,%ecx
  401e98:	c1 e1 04             	shl    $0x4,%ecx
  401e9b:	29 c1                	sub    %eax,%ecx
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_ACQUIRE);
  401e9d:	48 8b 43 28          	mov    0x28(%rbx),%rax
    data->writecursor = (data->writecursor + 1) % 0xf;
  401ea1:	29 ca                	sub    %ecx,%edx
  401ea3:	89 93 80 01 00 00    	mov    %edx,0x180(%rbx)
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_ACQUIRE);
  401ea9:	f0 48 83 80 50 03 00 00 01 	lock addq $0x1,0x350(%rax)
  long lastread = data->main->totalreads % data->threadsize;
  401eb2:	4c 8b 5b 28          	mov    0x28(%rbx),%r11
  401eb6:	48 63 4b 68          	movslq 0x68(%rbx),%rcx
  401eba:	49 8b 83 40 03 00 00 	mov    0x340(%r11),%rax
  401ec1:	49 89 c8             	mov    %rcx,%r8
   data->freq++;
  401ec4:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
  long lastread = data->main->totalreads % data->threadsize;
  401ec9:	48 99                	cqto
  401ecb:	48 f7 f9             	idiv   %rcx
   data->prevread = lastread;
  401ece:	48 89 93 08 03 00 00 	mov    %rdx,0x308(%rbx)
  for (int y = 2 ; y < data->threadsize; y++) {
  401ed5:	83 f9 02             	cmp    $0x2,%ecx
  401ed8:	0f 8e 22 01 00 00    	jle    402000 <threadwork+0x300>
          if (y != data->threadindex) {
  401ede:	48 63 43 64          	movslq 0x64(%rbx),%rax
                struct Data * thread = &data->threads[data->threadindex];
  401ee2:	bf 00 07 00 00       	mov    $0x700,%edi
  for (int y = 2 ; y < data->threadsize; y++) {
  401ee7:	be 02 00 00 00       	mov    $0x2,%esi
              past = data->threadsize - 1;
  401eec:	8d 69 ff             	lea    -0x1(%rcx),%ebp
                struct Data * thread = &data->threads[data->threadindex];
  401eef:	4c 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%r10
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401ef7:	41 89 c4             	mov    %eax,%r12d
          if (y != data->threadindex) {
  401efa:	49 89 c1             	mov    %rax,%r9
                struct Data * thread = &data->threads[data->threadindex];
  401efd:	49 29 c2             	sub    %rax,%r10
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401f00:	41 c1 e4 08          	shl    $0x8,%r12d
                struct Data * thread = &data->threads[data->threadindex];
  401f04:	49 c1 e2 07          	shl    $0x7,%r10
  401f08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (y != data->threadindex) {
  401f10:	44 39 ce             	cmp    %r9d,%esi
  401f13:	0f 84 d4 00 00 00    	je     401fed <threadwork+0x2ed>
            long past = ((data->main->writecursor - 1) % 0xf);
  401f19:	41 8b 83 80 01 00 00 	mov    0x180(%r11),%eax
            int rc = data->threads[x].writecursor;
  401f20:	4c 8b 7b 30          	mov    0x30(%rbx),%r15
  401f24:	41 be 0e 00 00 00    	mov    $0xe,%r14d
            long past = ((data->main->writecursor - 1) % 0xf);
  401f2a:	8d 50 ff             	lea    -0x1(%rax),%edx
  401f2d:	48 63 c2             	movslq %edx,%rax
  401f30:	89 d1                	mov    %edx,%ecx
  401f32:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401f39:	c1 f9 1f             	sar    $0x1f,%ecx
  401f3c:	48 c1 e8 20          	shr    $0x20,%rax
  401f40:	01 d0                	add    %edx,%eax
  401f42:	c1 f8 03             	sar    $0x3,%eax
  401f45:	29 c8                	sub    %ecx,%eax
  401f47:	89 c1                	mov    %eax,%ecx
  401f49:	c1 e1 04             	shl    $0x4,%ecx
  401f4c:	29 c1                	sub    %eax,%ecx
              past = data->threadsize - 1;
  401f4e:	89 d0                	mov    %edx,%eax
            int rc = data->threads[x].writecursor;
  401f50:	41 8b 94 3f 80 01 00 00 	mov    0x180(%r15,%rdi,1),%edx
              past = data->threadsize - 1;
  401f58:	29 c8                	sub    %ecx,%eax
  401f5a:	0f 48 c5             	cmovs  %ebp,%eax
  401f5d:	48 63 c8             	movslq %eax,%rcx
            if (rc < 0) {
  401f60:	85 d2                	test   %edx,%edx
  401f62:	78 2d                	js     401f91 <threadwork+0x291>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401f64:	48 63 c2             	movslq %edx,%rax
  401f67:	41 89 d5             	mov    %edx,%r13d
  401f6a:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401f71:	41 c1 fd 1f          	sar    $0x1f,%r13d
  401f75:	48 c1 e8 20          	shr    $0x20,%rax
  401f79:	01 d0                	add    %edx,%eax
  401f7b:	c1 f8 03             	sar    $0x3,%eax
  401f7e:	44 29 e8             	sub    %r13d,%eax
  401f81:	41 89 c5             	mov    %eax,%r13d
  401f84:	41 c1 e5 04          	shl    $0x4,%r13d
  401f88:	41 29 c5             	sub    %eax,%r13d
  401f8b:	44 29 ea             	sub    %r13d,%edx
  401f8e:	4c 63 f2             	movslq %edx,%r14
                struct Data * thread = &data->threads[data->threadindex];
  401f91:	4d 01 d7             	add    %r10,%r15
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401f94:	48 c1 e1 10          	shl    $0x10,%rcx
            thepoch->time = time; 
  401f98:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401f9d:	49 63 97 24 03 00 00 	movslq 0x324(%r15),%rdx
  401fa4:	48 89 d0             	mov    %rdx,%rax
  401fa7:	4c 8d 2c 52          	lea    (%rdx,%rdx,2),%r13
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401fab:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  401fae:	49 c1 e5 04          	shl    $0x4,%r13
  401fb2:	4d 03 af 18 03 00 00 	add    0x318(%r15),%r13
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401fb9:	99                   	cltd
            thepoch->time = time; 
  401fba:	41 0f 11 4d 08       	movups %xmm1,0x8(%r13)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401fbf:	41 f7 bf 20 03 00 00 	idivl  0x320(%r15)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401fc6:	89 f0                	mov    %esi,%eax
  401fc8:	c1 e0 18             	shl    $0x18,%eax
  401fcb:	44 09 e0             	or     %r12d,%eax
  401fce:	48 98                	cltq
  401fd0:	48 09 c8             	or     %rcx,%rax
  401fd3:	4c 09 f0             	or     %r14,%rax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401fd6:	41 89 97 24 03 00 00 	mov    %edx,0x324(%r15)
                thepoch->thread = x;
  401fdd:	41 89 75 00          	mov    %esi,0x0(%r13)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401fe1:	49 89 45 18          	mov    %rax,0x18(%r13)
          thepoch->set = 1;
  401fe5:	41 c7 45 24 01 00 00 00 	movl   $0x1,0x24(%r13)
  for (int y = 2 ; y < data->threadsize; y++) {
  401fed:	83 c6 01             	add    $0x1,%esi
  401ff0:	48 81 c7 80 03 00 00 	add    $0x380,%rdi
  401ff7:	41 39 f0             	cmp    %esi,%r8d
  401ffa:	0f 85 10 ff ff ff    	jne    401f10 <threadwork+0x210>
     data->readcursor = (data->readcursor + 1) % 0xf;
  402000:	8b 83 00 02 00 00    	mov    0x200(%rbx),%eax
  402006:	8d 50 01             	lea    0x1(%rax),%edx
  402009:	48 63 c2             	movslq %edx,%rax
  40200c:	89 d1                	mov    %edx,%ecx
  40200e:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402015:	c1 f9 1f             	sar    $0x1f,%ecx
  402018:	48 c1 e8 20          	shr    $0x20,%rax
  40201c:	01 d0                	add    %edx,%eax
  40201e:	c1 f8 03             	sar    $0x3,%eax
  402021:	29 c8                	sub    %ecx,%eax
  402023:	89 c1                	mov    %eax,%ecx
  402025:	c1 e1 04             	shl    $0x4,%ecx
  402028:	29 c1                	sub    %eax,%ecx
  40202a:	29 ca                	sub    %ecx,%edx
  40202c:	89 93 00 02 00 00    	mov    %edx,0x200(%rbx)
    __atomic_fetch_add(&data->main->globalread, 1, __ATOMIC_ACQUIRE);
  402032:	f0 49 83 83 48 03 00 00 01 	lock addq $0x1,0x348(%r11)
}
  40203b:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  402040:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  402049:	75 11                	jne    40205c <threadwork+0x35c>
  40204b:	48 83 c4 28          	add    $0x28,%rsp
  40204f:	31 c0                	xor    %eax,%eax
  402051:	5b                   	pop    %rbx
  402052:	5d                   	pop    %rbp
  402053:	41 5c                	pop    %r12
  402055:	41 5d                	pop    %r13
  402057:	41 5e                	pop    %r14
  402059:	41 5f                	pop    %r15
  40205b:	c3                   	ret
  40205c:	e8 0f f0 ff ff       	call   401070 <__stack_chk_fail@plt>
  402061:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40206c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000402070 <work>:
void * work(void * arg) {
  402070:	41 56                	push   %r14
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  402072:	48 8d 35 8b 0f 00 00 	lea    0xf8b(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  402079:	31 c0                	xor    %eax,%eax
  40207b:	41 55                	push   %r13
  40207d:	41 54                	push   %r12
  40207f:	55                   	push   %rbp
  402080:	53                   	push   %rbx
  402081:	8b 57 64             	mov    0x64(%rdi),%edx
  402084:	48 89 fb             	mov    %rdi,%rbx
  402087:	bf 01 00 00 00       	mov    $0x1,%edi
  40208c:	e8 1f f0 ff ff       	call   4010b0 <__printf_chk@plt>
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  402091:	48 8b 83 b8 00 00 00 	mov    0xb8(%rbx),%rax
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  402098:	4c 63 6b 68          	movslq 0x68(%rbx),%r13
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  40209c:	be 08 00 00 00       	mov    $0x8,%esi
  4020a1:	48 8d 78 01          	lea    0x1(%rax),%rdi
  4020a5:	e8 f6 ef ff ff       	call   4010a0 <calloc@plt>
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  4020aa:	be 04 00 00 00       	mov    $0x4,%esi
  4020af:	4c 89 ef             	mov    %r13,%rdi
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  4020b2:	48 89 c5             	mov    %rax,%rbp
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  4020b5:	e8 e6 ef ff ff       	call   4010a0 <calloc@plt>
  int * readywriters = calloc(data->threadsize, sizeof(int));
  4020ba:	be 04 00 00 00       	mov    $0x4,%esi
  4020bf:	4c 89 ef             	mov    %r13,%rdi
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  4020c2:	49 89 c4             	mov    %rax,%r12
  int * readywriters = calloc(data->threadsize, sizeof(int));
  4020c5:	e8 d6 ef ff ff       	call   4010a0 <calloc@plt>
  while (data->running == 1) {
  4020ca:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  4020ce:	75 5f                	jne    40212f <work+0xbf>
  4020d0:	49 89 c5             	mov    %rax,%r13
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  4020d3:	4c 8d b3 28 01 00 00 	lea    0x128(%rbx),%r14
  4020da:	eb 17                	jmp    4020f3 <work+0x83>
  4020dc:	0f 1f 40 00          	nopl   0x0(%rax)
    } else if (data->threadindex == 1) {
  4020e0:	83 f8 01             	cmp    $0x1,%eax
  4020e3:	74 6b                	je     402150 <work+0xe0>
      threadwork(data);
  4020e5:	48 89 df             	mov    %rbx,%rdi
  4020e8:	e8 13 fc ff ff       	call   401d00 <threadwork>
  while (data->running == 1) {
  4020ed:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  4020f1:	75 3c                	jne    40212f <work+0xbf>
   if (data->threadindex == 0) {
  4020f3:	8b 43 64             	mov    0x64(%rbx),%eax
  4020f6:	85 c0                	test   %eax,%eax
  4020f8:	75 e6                	jne    4020e0 <work+0x70>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  4020fa:	4c 89 f6             	mov    %r14,%rsi
  4020fd:	bf 04 00 00 00       	mov    $0x4,%edi
  402102:	e8 59 ef ff ff       	call   401060 <clock_gettime@plt>
      singlewriter2(data, available, readyreaders, readywriters);
  402107:	4c 89 e9             	mov    %r13,%rcx
  40210a:	4c 89 e2             	mov    %r12,%rdx
  40210d:	48 89 ee             	mov    %rbp,%rsi
  402110:	48 89 df             	mov    %rbx,%rdi
  402113:	e8 28 f9 ff ff       	call   401a40 <singlewriter2>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swend);
  402118:	48 8d b3 38 01 00 00 	lea    0x138(%rbx),%rsi
  40211f:	bf 04 00 00 00       	mov    $0x4,%edi
  402124:	e8 37 ef ff ff       	call   401060 <clock_gettime@plt>
  while (data->running == 1) {
  402129:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  40212d:	74 c4                	je     4020f3 <work+0x83>
  40212f:	8b 53 64             	mov    0x64(%rbx),%edx
  402132:	48 8d 35 de 0e 00 00 	lea    0xede(%rip),%rsi        # 403017 <_IO_stdin_used+0x17>
  402139:	bf 01 00 00 00       	mov    $0x1,%edi
  40213e:	31 c0                	xor    %eax,%eax
  402140:	e8 6b ef ff ff       	call   4010b0 <__printf_chk@plt>
}
  402145:	5b                   	pop    %rbx
  402146:	5d                   	pop    %rbp
  402147:	41 5c                	pop    %r12
  402149:	41 5d                	pop    %r13
  40214b:	41 5e                	pop    %r14
  40214d:	c3                   	ret
  40214e:	66 90                	xchg   %ax,%ax
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  402150:	4c 89 f6             	mov    %r14,%rsi
  402153:	bf 04 00 00 00       	mov    $0x4,%edi
  402158:	e8 03 ef ff ff       	call   401060 <clock_gettime@plt>
      singlewriter3(data, available, readyreaders, readywriters);
  40215d:	48 89 ee             	mov    %rbp,%rsi
  402160:	48 89 df             	mov    %rbx,%rdi
  402163:	4c 89 e9             	mov    %r13,%rcx
  402166:	4c 89 e2             	mov    %r12,%rdx
  402169:	e8 a2 f8 ff ff       	call   401a10 <singlewriter3>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swend);
  40216e:	48 8d b3 38 01 00 00 	lea    0x138(%rbx),%rsi
  402175:	bf 04 00 00 00       	mov    $0x4,%edi
  40217a:	e8 e1 ee ff ff       	call   401060 <clock_gettime@plt>
  40217f:	e9 69 ff ff ff       	jmp    4020ed <work+0x7d>
  402184:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40218f:	90                   	nop

0000000000402190 <work2>:
  while (data->running == 1) {
  402190:	eb 0b                	jmp    40219d <work2+0xd>
  402192:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  402198:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  40219d:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  4021a1:	74 f5                	je     402198 <work2+0x8>
}
  4021a3:	c3                   	ret

Disassembly of section .fini:

00000000004021a4 <_fini>:
  4021a4:	f3 0f 1e fa          	endbr64
  4021a8:	48 83 ec 08          	sub    $0x8,%rsp
  4021ac:	48 83 c4 08          	add    $0x8,%rsp
  4021b0:	c3                   	ret
