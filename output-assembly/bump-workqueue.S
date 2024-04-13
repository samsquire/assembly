
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
  40115d:	ba 10 00 00 00       	mov    $0x10,%edx
  401162:	48 8d 35 df 1e 00 00 	lea    0x1edf(%rip),%rsi        # 403048 <_IO_stdin_used+0x48>
  401169:	31 c0                	xor    %eax,%eax
  40116b:	bf 01 00 00 00       	mov    $0x1,%edi
  401170:	e8 3b ff ff ff       	call   4010b0 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401175:	be 08 00 00 00       	mov    $0x8,%esi
  40117a:	bf 10 00 00 00       	mov    $0x10,%edi
  40117f:	e8 1c ff ff ff       	call   4010a0 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401184:	be 38 00 00 00       	mov    $0x38,%esi
  401189:	bf 10 00 00 00       	mov    $0x10,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40118e:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401193:	e8 08 ff ff ff       	call   4010a0 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  401198:	be 00 38 00 00       	mov    $0x3800,%esi
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
  4011f2:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
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
  40121c:	bf 10 00 00 00       	mov    $0x10,%edi
  401221:	e8 7a fe ff ff       	call   4010a0 <calloc@plt>
  401226:	66 48 0f 6e f3       	movq   %rbx,%xmm6
  data[0].works = works;
  40122b:	4c 89 63 70          	mov    %r12,0x70(%rbx)
  40122f:	45 31 e4             	xor    %r12d,%r12d
  401232:	66 48 0f 6e e8       	movq   %rax,%xmm5
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  401237:	48 89 c5             	mov    %rax,%rbp
  40123a:	66 0f 6c ee          	punpcklqdq %xmm6,%xmm5
  40123e:	0f 29 6c 24 10       	movaps %xmm5,0x10(%rsp)
  for (int x = 0; x < threadsize ; x++) {
  401243:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401248:	45 89 ef             	mov    %r13d,%r15d
  40124b:	be 80 00 00 00       	mov    $0x80,%esi
  401250:	bf 01 00 00 00       	mov    $0x1,%edi
    CPU_SET(cpu += 1, data[x].cpu_set);
  401255:	41 83 c5 01          	add    $0x1,%r13d
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401259:	e8 42 fe ff ff       	call   4010a0 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  40125e:	44 89 e9             	mov    %r13d,%ecx
  401261:	ba 01 00 00 00       	mov    $0x1,%edx
  401266:	48 8d 35 1b 1f 00 00 	lea    0x1f1b(%rip),%rsi        # 403188 <_IO_stdin_used+0x188>
  40126d:	48 d3 e2             	shl    %cl,%rdx
  401270:	48 09 10             	or     %rdx,(%rax)
  401273:	44 89 e9             	mov    %r13d,%ecx
  401276:	44 89 fa             	mov    %r15d,%edx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401279:	49 89 46 78          	mov    %rax,0x78(%r14)
  40127d:	bf 01 00 00 00       	mov    $0x1,%edi
  401282:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  401284:	48 83 c5 04          	add    $0x4,%rbp
  401288:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  40128f:	e8 1c fe ff ff       	call   4010b0 <__printf_chk@plt>
    data[x].threadindex = x;
    data[x].worksize = worksize;
    
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].readies = readies;
  401294:	66 0f 6f 4c 24 10    	movdqa 0x10(%rsp),%xmm1
    data[x].running = 1;
  40129a:	48 8b 05 0f 1f 00 00 	mov    0x1f0f(%rip),%rax        # 4031b0 <_IO_stdin_used+0x1b0>
    data[x].bucketstart = x * buckets ;
  4012a1:	45 89 a6 18 fd ff ff 	mov    %r12d,-0x2e8(%r14)
    data[x].readies[x] = 0;
    data[x].buckets = buckets;
    data[x].main = &data[0];
    data[x].threads = data;
    
    data[x].read = 0;
  4012a8:	66 0f 6f 15 10 1f 00 00 	movdqa 0x1f10(%rip),%xmm2        # 4031c0 <_IO_stdin_used+0x1c0>
    data[x].newmask = 0;
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4012b0:	be 30 00 00 00       	mov    $0x30,%esi
    data[x].chunkslen = chunkslen;
  4012b5:	66 0f 6f 1d 13 1f 00 00 	movdqa 0x1f13(%rip),%xmm3        # 4031d0 <_IO_stdin_used+0x1d0>
    data[x].loglevel = debug;
  4012bd:	41 c7 86 00 fd ff ff 00 00 00 00 	movl   $0x0,-0x300(%r14)
    data[x].running = 1;
  4012c8:	49 89 86 dc fc ff ff 	mov    %rax,-0x324(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4012cf:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].buckets = buckets;
  4012d4:	48 8b 05 dd 1e 00 00 	mov    0x1edd(%rip),%rax        # 4031b8 <_IO_stdin_used+0x1b8>
  for (int x = 0; x < threadsize ; x++) {
  4012db:	41 81 c4 ff ff ff 0f 	add    $0xfffffff,%r12d
    data[x].prevread = threadsize;
  4012e2:	66 0f 6f 25 f6 1e 00 00 	movdqa 0x1ef6(%rip),%xmm4        # 4031e0 <_IO_stdin_used+0x1e0>
    data[x].threadindex = x;
  4012ea:	45 89 be e4 fc ff ff 	mov    %r15d,-0x31c(%r14)
    data[x].buckets = buckets;
  4012f1:	49 89 86 10 fd ff ff 	mov    %rax,-0x2f0(%r14)
    data[x].freelist = freelist;
  4012f8:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    data[x].threadsize = threadsize;
  4012fd:	41 c7 86 e8 fc ff ff 10 00 00 00 	movl   $0x10,-0x318(%r14)
    data[x].readies[x] = 0;
  401308:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
    data[x].threads = data;
  40130f:	49 89 9e b0 fc ff ff 	mov    %rbx,-0x350(%r14)
    data[x].readcursor = threadsize - 1;
  401316:	41 c7 86 80 fe ff ff 0f 00 00 00 	movl   $0xf,-0x180(%r14)
    data[x].writecursor = threadsize - 1;
  401321:	41 c7 86 00 fe ff ff 0f 00 00 00 	movl   $0xf,-0x200(%r14)
    data[x].freelist = freelist;
  40132c:	49 89 86 20 fd ff ff 	mov    %rax,-0x2e0(%r14)
    data[x].newmask = 0;
  401333:	41 c7 86 48 fd ff ff 00 00 00 00 	movl   $0x0,-0x2b8(%r14)
    data[x].thiswrite = threadsize;
  40133e:	41 c7 46 a8 10 00 00 00 	movl   $0x10,-0x58(%r14)
    data[x].readies = readies;
  401346:	41 0f 29 8e a0 fc ff ff 	movaps %xmm1,-0x360(%r14)
    data[x].read = 0;
  40134e:	41 0f 29 96 80 fc ff ff 	movaps %xmm2,-0x380(%r14)
    data[x].chunkslen = chunkslen;
  401356:	41 0f 11 9e 38 fd ff ff 	movups %xmm3,-0x2c8(%r14)
    data[x].prevread = threadsize;
  40135e:	41 0f 11 66 88       	movups %xmm4,-0x78(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401363:	e8 38 fd ff ff       	call   4010a0 <calloc@plt>
    data[x].epochssize = epochs;
    
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  401368:	be 30 00 00 00       	mov    $0x30,%esi
  40136d:	bf 10 27 00 00       	mov    $0x2710,%edi
    data[x].epochssize = epochs;
  401372:	41 c7 46 a0 80 96 98 00 	movl   $0x989680,-0x60(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  40137a:	49 89 46 98          	mov    %rax,-0x68(%r14)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  40137e:	e8 1d fd ff ff       	call   4010a0 <calloc@plt>
  401383:	49 89 46 b0          	mov    %rax,-0x50(%r14)
  for (int x = 0; x < threadsize ; x++) {
  401387:	41 83 fd 10          	cmp    $0x10,%r13d
  40138b:	0f 85 b7 fe ff ff    	jne    401248 <main+0x158>
  401391:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
  401396:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
  40139b:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  4013a0:	49 c7 c5 d0 21 40 00 	mov    $0x4021d0,%r13
  4013a7:	48 8d 85 80 03 00 00 	lea    0x380(%rbp),%rax
  4013ae:	4d 89 fc             	mov    %r15,%r12
  4013b1:	49 89 c6             	mov    %rax,%r14
  4013b4:	0f 1f 40 00          	nopl   0x0(%rax)
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  4013b8:	48 89 d9             	mov    %rbx,%rcx
  4013bb:	48 89 ee             	mov    %rbp,%rsi
  4013be:	4c 89 ff             	mov    %r15,%rdi
  4013c1:	4c 89 ea             	mov    %r13,%rdx
  4013c4:	e8 f7 fc ff ff       	call   4010c0 <pthread_create@plt>
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4013c9:	48 8b 53 78          	mov    0x78(%rbx),%rdx
  4013cd:	49 8b 3f             	mov    (%r15),%rdi
  4013d0:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  4013d5:	48 83 c5 38          	add    $0x38,%rbp
  4013d9:	49 83 c7 08          	add    $0x8,%r15
  4013dd:	48 81 c3 80 03 00 00 	add    $0x380,%rbx
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4013e4:	e8 57 fc ff ff       	call   401040 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  4013e9:	4c 39 f5             	cmp    %r14,%rbp
  4013ec:	75 ca                	jne    4013b8 <main+0x2c8>
  }
  
  struct timespec time = {
  4013ee:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  4013f3:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  4013f8:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec time = {
  4013fd:	66 0f 6f 05 eb 1d 00 00 	movdqa 0x1deb(%rip),%xmm0        # 4031f0 <_IO_stdin_used+0x1f0>
  401405:	4c 8d 6c 24 38       	lea    0x38(%rsp),%r13
  40140a:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  40140f:	66 0f ef c0          	pxor   %xmm0,%xmm0
  401413:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  401418:	e8 63 fc ff ff       	call   401080 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  40141d:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
  401422:	c7 43 5c 00 00 00 00 	movl   $0x0,0x5c(%rbx)
  401429:	c7 83 dc 03 00 00 00 00 00 00 	movl   $0x0,0x3dc(%rbx)
  401433:	c7 83 5c 07 00 00 00 00 00 00 	movl   $0x0,0x75c(%rbx)
  40143d:	48 83 ed 80          	sub    $0xffffffffffffff80,%rbp
  401441:	c7 83 dc 0a 00 00 00 00 00 00 	movl   $0x0,0xadc(%rbx)
  40144b:	c7 83 5c 0e 00 00 00 00 00 00 	movl   $0x0,0xe5c(%rbx)
  401455:	c7 83 dc 11 00 00 00 00 00 00 	movl   $0x0,0x11dc(%rbx)
  40145f:	c7 83 5c 15 00 00 00 00 00 00 	movl   $0x0,0x155c(%rbx)
  401469:	c7 83 dc 18 00 00 00 00 00 00 	movl   $0x0,0x18dc(%rbx)
  401473:	c7 83 5c 1c 00 00 00 00 00 00 	movl   $0x0,0x1c5c(%rbx)
  40147d:	c7 83 dc 1f 00 00 00 00 00 00 	movl   $0x0,0x1fdc(%rbx)
  401487:	c7 83 5c 23 00 00 00 00 00 00 	movl   $0x0,0x235c(%rbx)
  401491:	c7 83 dc 26 00 00 00 00 00 00 	movl   $0x0,0x26dc(%rbx)
  40149b:	c7 83 5c 2a 00 00 00 00 00 00 	movl   $0x0,0x2a5c(%rbx)
  4014a5:	c7 83 dc 2d 00 00 00 00 00 00 	movl   $0x0,0x2ddc(%rbx)
  4014af:	c7 83 5c 31 00 00 00 00 00 00 	movl   $0x0,0x315c(%rbx)
  4014b9:	c7 83 dc 34 00 00 00 00 00 00 	movl   $0x0,0x34dc(%rbx)
  for (int x = 0; x < threadsize ; x++) {
  4014c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  4014c8:	49 8b 3c 24          	mov    (%r12),%rdi
  4014cc:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  4014cf:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  4014d3:	e8 08 fc ff ff       	call   4010e0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  4014d8:	4c 39 e5             	cmp    %r12,%rbp
  4014db:	75 eb                	jne    4014c8 <main+0x3d8>
  4014dd:	48 8d 3d a1 1b 00 00 	lea    0x1ba1(%rip),%rdi        # 403085 <_IO_stdin_used+0x85>
  4014e4:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  4014e8:	45 31 e4             	xor    %r12d,%r12d
  4014eb:	e8 60 fb ff ff       	call   401050 <puts@plt>
  for (int x = 0; x < threadsize; x++) {
  4014f0:	4c 8d b3 48 38 00 00 	lea    0x3848(%rbx),%r14
  4014f7:	4c 8d 2d 9c 1b 00 00 	lea    0x1b9c(%rip),%r13        # 40309a <_IO_stdin_used+0x9a>
  4014fe:	66 90                	xchg   %ax,%ax
  401500:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401504:	4c 89 ee             	mov    %r13,%rsi
  401507:	bf 01 00 00 00       	mov    $0x1,%edi
  40150c:	31 c0                	xor    %eax,%eax
  40150e:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
  401515:	e8 96 fb ff ff       	call   4010b0 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  40151a:	4c 03 a5 80 fc ff ff 	add    -0x380(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  401521:	49 39 ee             	cmp    %rbp,%r14
  401524:	75 da                	jne    401500 <main+0x410>
  }
  printf("freq: %ld\n", freq/ seconds);
  printf("freq_ps: %ld\n", (freq*threadsize-1)/ seconds);
  401526:	4d 89 e5             	mov    %r12,%r13
  401529:	4c 89 e2             	mov    %r12,%rdx
  40152c:	48 8d 35 72 1b 00 00 	lea    0x1b72(%rip),%rsi        # 4030a5 <_IO_stdin_used+0xa5>
  401533:	31 c0                	xor    %eax,%eax
  401535:	49 c1 e5 04          	shl    $0x4,%r13
  401539:	bf 01 00 00 00       	mov    $0x1,%edi
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  40153e:	bd 00 ca 9a 3b       	mov    $0x3b9aca00,%ebp
  401543:	e8 68 fb ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq_ps: %ld\n", (freq*threadsize-1)/ seconds);
  401548:	49 83 ed 01          	sub    $0x1,%r13
  40154c:	bf 01 00 00 00       	mov    $0x1,%edi
  401551:	31 c0                	xor    %eax,%eax
  401553:	4c 89 ea             	mov    %r13,%rdx
  401556:	48 8d 35 53 1b 00 00 	lea    0x1b53(%rip),%rsi        # 4030b0 <_IO_stdin_used+0xb0>
  40155d:	4c 8d b3 50 38 00 00 	lea    0x3850(%rbx),%r14
  401564:	e8 47 fb ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  401569:	48 89 e8             	mov    %rbp,%rax
  40156c:	bf 01 00 00 00       	mov    $0x1,%edi
  401571:	48 8d 35 46 1b 00 00 	lea    0x1b46(%rip),%rsi        # 4030be <_IO_stdin_used+0xbe>
  401578:	48 99                	cqto
  40157a:	49 f7 fc             	idiv   %r12
  printf("freq latency: %ld\n", 1000000000/((freq*threadsize-1)/seconds));
  long freq_writes = 0;
  40157d:	45 31 e4             	xor    %r12d,%r12d
  401580:	48 89 c2             	mov    %rax,%rdx
  401583:	31 c0                	xor    %eax,%eax
  401585:	e8 26 fb ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*threadsize-1)/seconds));
  40158a:	48 89 e8             	mov    %rbp,%rax
  40158d:	bf 01 00 00 00       	mov    $0x1,%edi
  401592:	48 8d 35 39 1b 00 00 	lea    0x1b39(%rip),%rsi        # 4030d2 <_IO_stdin_used+0xd2>
  401599:	48 99                	cqto
  40159b:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  40159f:	49 f7 fd             	idiv   %r13
  4015a2:	4c 8d 2d 3c 1b 00 00 	lea    0x1b3c(%rip),%r13        # 4030e5 <_IO_stdin_used+0xe5>
  4015a9:	48 89 c2             	mov    %rax,%rdx
  4015ac:	31 c0                	xor    %eax,%eax
  4015ae:	e8 fd fa ff ff       	call   4010b0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  4015b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    freq_writes += data[x].freq_writes;
  4015b8:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4015bc:	4c 89 ee             	mov    %r13,%rsi
  4015bf:	bf 01 00 00 00       	mov    $0x1,%edi
  4015c4:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  4015c6:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
    freq_writes += data[x].freq_writes;
  4015cd:	49 01 d4             	add    %rdx,%r12
  4015d0:	e8 db fa ff ff       	call   4010b0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  4015d5:	4c 39 f5             	cmp    %r14,%rbp
  4015d8:	75 de                	jne    4015b8 <main+0x4c8>
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);

  printf("freq_writes_total: %ld\n", (freq_writes * threadsize - 1) / seconds);
  4015da:	4d 89 e5             	mov    %r12,%r13
  4015dd:	4c 89 e2             	mov    %r12,%rdx
  4015e0:	48 8d 35 0a 1b 00 00 	lea    0x1b0a(%rip),%rsi        # 4030f1 <_IO_stdin_used+0xf1>
  4015e7:	31 c0                	xor    %eax,%eax
  4015e9:	49 c1 e5 04          	shl    $0x4,%r13
  4015ed:	bf 01 00 00 00       	mov    $0x1,%edi
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  4015f2:	bd 00 ca 9a 3b       	mov    $0x3b9aca00,%ebp
  4015f7:	e8 b4 fa ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq_writes_total: %ld\n", (freq_writes * threadsize - 1) / seconds);
  4015fc:	49 83 ed 01          	sub    $0x1,%r13
  401600:	bf 01 00 00 00       	mov    $0x1,%edi
  401605:	31 c0                	xor    %eax,%eax
  401607:	4c 89 ea             	mov    %r13,%rdx
  40160a:	48 8d 35 f2 1a 00 00 	lea    0x1af2(%rip),%rsi        # 403103 <_IO_stdin_used+0x103>
  401611:	4c 8d b3 20 03 00 00 	lea    0x320(%rbx),%r14
  401618:	e8 93 fa ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  40161d:	48 89 e8             	mov    %rbp,%rax
  401620:	bf 01 00 00 00       	mov    $0x1,%edi
  401625:	48 8d 35 ef 1a 00 00 	lea    0x1aef(%rip),%rsi        # 40311b <_IO_stdin_used+0x11b>
  40162c:	48 99                	cqto
  40162e:	49 f7 fc             	idiv   %r12
  401631:	48 89 c2             	mov    %rax,%rdx
  401634:	31 c0                	xor    %eax,%eax
  401636:	e8 75 fa ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * threadsize - 1) / seconds));
  40163b:	48 89 e8             	mov    %rbp,%rax
  40163e:	bf 01 00 00 00       	mov    $0x1,%edi
  401643:	48 8d 35 ec 1a 00 00 	lea    0x1aec(%rip),%rsi        # 403136 <_IO_stdin_used+0x136>
  40164a:	48 99                	cqto
  40164c:	48 8d 2d 7a 1a 00 00 	lea    0x1a7a(%rip),%rbp        # 4030cd <_IO_stdin_used+0xcd>
  401653:	49 f7 fd             	idiv   %r13
  401656:	48 89 c2             	mov    %rax,%rdx
  401659:	31 c0                	xor    %eax,%eax
  40165b:	e8 50 fa ff ff       	call   4010b0 <__printf_chk@plt>
  401660:	48 8d 3d e9 1a 00 00 	lea    0x1ae9(%rip),%rdi        # 403150 <_IO_stdin_used+0x150>
  401667:	e8 e4 f9 ff ff       	call   401050 <puts@plt>
  40166c:	48 89 ee             	mov    %rbp,%rsi
  40166f:	bf 01 00 00 00       	mov    $0x1,%edi
  401674:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  401676:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  40167d:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  401684:	e8 27 fa ff ff       	call   4010b0 <__printf_chk@plt>
  401689:	48 89 ee             	mov    %rbp,%rsi
  40168c:	bf 01 00 00 00       	mov    $0x1,%edi
  401691:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  401693:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  40169a:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4016a1:	e8 0a fa ff ff       	call   4010b0 <__printf_chk@plt>
  4016a6:	48 89 ee             	mov    %rbp,%rsi
  4016a9:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ae:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  4016b0:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  4016b7:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  4016be:	e8 ed f9 ff ff       	call   4010b0 <__printf_chk@plt>
  4016c3:	48 89 ee             	mov    %rbp,%rsi
  4016c6:	bf 01 00 00 00       	mov    $0x1,%edi
  4016cb:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4016cd:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  4016d4:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  4016db:	e8 d0 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  4016e0:	48 89 ee             	mov    %rbp,%rsi
  4016e3:	bf 01 00 00 00       	mov    $0x1,%edi
  4016e8:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  4016ea:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  4016f1:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  4016f8:	e8 b3 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  4016fd:	48 89 ee             	mov    %rbp,%rsi
  401700:	bf 01 00 00 00       	mov    $0x1,%edi
  401705:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  401707:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  40170e:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401715:	e8 96 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  40171a:	bf 01 00 00 00       	mov    $0x1,%edi
  40171f:	31 c0                	xor    %eax,%eax
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  401721:	45 31 ed             	xor    %r13d,%r13d
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  401724:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  40172b:	48 8d 35 2b 1a 00 00 	lea    0x1a2b(%rip),%rsi        # 40315d <_IO_stdin_used+0x15d>
  401732:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  401739:	48 81 c3 20 3b 00 00 	add    $0x3b20,%rbx
  401740:	e8 6b f9 ff ff       	call   4010b0 <__printf_chk@plt>
  } 

  if (SAMPLE == 1) {
  char * filename = calloc(100, sizeof(char));
  401745:	be 01 00 00 00       	mov    $0x1,%esi
  40174a:	bf 64 00 00 00       	mov    $0x64,%edi
  40174f:	e8 4c f9 ff ff       	call   4010a0 <calloc@plt>
  char * buf = calloc(1000, sizeof(char));
  401754:	be 01 00 00 00       	mov    $0x1,%esi
  401759:	bf e8 03 00 00       	mov    $0x3e8,%edi
  char * filename = calloc(100, sizeof(char));
  40175e:	49 89 c4             	mov    %rax,%r12
  char * buf = calloc(1000, sizeof(char));
  401761:	e8 3a f9 ff ff       	call   4010a0 <calloc@plt>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401766:	44 8b 8b 48 c5 ff ff 	mov    -0x3ab8(%rbx),%r9d
  40176d:	4c 89 e7             	mov    %r12,%rdi
  401770:	4c 8d 05 ee 19 00 00 	lea    0x19ee(%rip),%r8        # 403165 <_IO_stdin_used+0x165>
  401777:	b9 64 00 00 00       	mov    $0x64,%ecx
  40177c:	ba 01 00 00 00       	mov    $0x1,%edx
  401781:	be 64 00 00 00       	mov    $0x64,%esi
  401786:	48 89 c5             	mov    %rax,%rbp
  401789:	31 c0                	xor    %eax,%eax
  40178b:	e8 a0 f8 ff ff       	call   401030 <__snprintf_chk@plt>
  memset(filename, 0, 100);
  snprintf(filename, 100, "samples%d", data->threadsize);
  FILE *out_file = fopen(filename, "w");
  401790:	4c 89 e7             	mov    %r12,%rdi
  401793:	48 8d 35 d5 19 00 00 	lea    0x19d5(%rip),%rsi        # 40316f <_IO_stdin_used+0x16f>
  40179a:	e8 31 f9 ff ff       	call   4010d0 <fopen@plt>
  40179f:	49 89 c4             	mov    %rax,%r12
  
  for (int x = 0; x < threadsize; x++) {
  4017a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int y = 0; y < data[x].epochssize; y++) {
  4017a8:	41 8b 0e             	mov    (%r14),%ecx
  4017ab:	45 31 ff             	xor    %r15d,%r15d
  4017ae:	85 c9                	test   %ecx,%ecx
  4017b0:	7e 21                	jle    4017d3 <main+0x6e3>
  4017b2:	49 8b 76 f8          	mov    -0x8(%r14),%rsi
      struct Epoch * epoch = &data[x].epochs[y];
  4017b6:	49 63 c7             	movslq %r15d,%rax
  4017b9:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  4017bd:	48 c1 e2 04          	shl    $0x4,%rdx
  4017c1:	48 01 f2             	add    %rsi,%rdx
      if (epoch->set == 1) {
  4017c4:	83 7a 24 01          	cmpl   $0x1,0x24(%rdx)
  4017c8:	74 3e                	je     401808 <main+0x718>
    for (int y = 0; y < data[x].epochssize; y++) {
  4017ca:	41 83 c7 01          	add    $0x1,%r15d
  4017ce:	41 39 cf             	cmp    %ecx,%r15d
  4017d1:	7c e3                	jl     4017b6 <main+0x6c6>
  for (int x = 0; x < threadsize; x++) {
  4017d3:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  4017da:	49 39 de             	cmp    %rbx,%r14
  4017dd:	75 c9                	jne    4017a8 <main+0x6b8>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  4017df:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  4017e4:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4017ed:	0f 85 90 00 00 00    	jne    401883 <main+0x793>
  4017f3:	48 83 c4 78          	add    $0x78,%rsp
  4017f7:	31 c0                	xor    %eax,%eax
  4017f9:	5b                   	pop    %rbx
  4017fa:	5d                   	pop    %rbp
  4017fb:	41 5c                	pop    %r12
  4017fd:	41 5d                	pop    %r13
  4017ff:	41 5e                	pop    %r14
  401801:	41 5f                	pop    %r15
  401803:	c3                   	ret
  401804:	0f 1f 40 00          	nopl   0x0(%rax)
  401808:	4c 89 e8             	mov    %r13,%rax
  40180b:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401810:	48 89 ef             	mov    %rbp,%rdi
  401813:	48 83 ec 08          	sub    $0x8,%rsp
  401817:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  40181a:	be 64 00 00 00       	mov    $0x64,%esi
  40181f:	48 89 ef             	mov    %rbp,%rdi
    for (int y = 0; y < data[x].epochssize; y++) {
  401822:	41 83 c7 01          	add    $0x1,%r15d
  401826:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  40182b:	4c 8d 05 3f 19 00 00 	lea    0x193f(%rip),%r8        # 403171 <_IO_stdin_used+0x171>
  401832:	8b 42 28             	mov    0x28(%rdx),%eax
  401835:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
  401839:	50                   	push   %rax
  40183a:	8b 02                	mov    (%rdx),%eax
  40183c:	50                   	push   %rax
  40183d:	8b 42 20             	mov    0x20(%rdx),%eax
  401840:	ff 72 18             	push   0x18(%rdx)
  401843:	50                   	push   %rax
  401844:	31 c0                	xor    %eax,%eax
  401846:	ff 72 10             	push   0x10(%rdx)
  401849:	ba 01 00 00 00       	mov    $0x1,%edx
  40184e:	e8 dd f7 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  401853:	48 83 c4 30          	add    $0x30,%rsp
  401857:	4c 89 e6             	mov    %r12,%rsi
  40185a:	48 89 ef             	mov    %rbp,%rdi
  40185d:	e8 2e f8 ff ff       	call   401090 <fputs@plt>
  401862:	41 8b 0e             	mov    (%r14),%ecx
  401865:	41 39 cf             	cmp    %ecx,%r15d
  401868:	0f 8c 44 ff ff ff    	jl     4017b2 <main+0x6c2>
  for (int x = 0; x < threadsize; x++) {
  40186e:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  401875:	49 39 de             	cmp    %rbx,%r14
  401878:	0f 85 2a ff ff ff    	jne    4017a8 <main+0x6b8>
  40187e:	e9 5c ff ff ff       	jmp    4017df <main+0x6ef>
  401883:	e8 e8 f7 ff ff       	call   401070 <__stack_chk_fail@plt>
  401888:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000401890 <_start>:
  401890:	f3 0f 1e fa          	endbr64
  401894:	31 ed                	xor    %ebp,%ebp
  401896:	49 89 d1             	mov    %rdx,%r9
  401899:	5e                   	pop    %rsi
  40189a:	48 89 e2             	mov    %rsp,%rdx
  40189d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4018a1:	50                   	push   %rax
  4018a2:	54                   	push   %rsp
  4018a3:	45 31 c0             	xor    %r8d,%r8d
  4018a6:	31 c9                	xor    %ecx,%ecx
  4018a8:	48 c7 c7 f0 10 40 00 	mov    $0x4010f0,%rdi
  4018af:	ff 15 3b 37 00 00    	call   *0x373b(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  4018b5:	f4                   	hlt
  4018b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004018c0 <_dl_relocate_static_pie>:
  4018c0:	f3 0f 1e fa          	endbr64
  4018c4:	c3                   	ret
  4018c5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4018cf:	90                   	nop

00000000004018d0 <deregister_tm_clones>:
  4018d0:	b8 10 50 40 00       	mov    $0x405010,%eax
  4018d5:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  4018db:	74 13                	je     4018f0 <deregister_tm_clones+0x20>
  4018dd:	b8 00 00 00 00       	mov    $0x0,%eax
  4018e2:	48 85 c0             	test   %rax,%rax
  4018e5:	74 09                	je     4018f0 <deregister_tm_clones+0x20>
  4018e7:	bf 10 50 40 00       	mov    $0x405010,%edi
  4018ec:	ff e0                	jmp    *%rax
  4018ee:	66 90                	xchg   %ax,%ax
  4018f0:	c3                   	ret
  4018f1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4018fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401900 <register_tm_clones>:
  401900:	be 10 50 40 00       	mov    $0x405010,%esi
  401905:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  40190c:	48 89 f0             	mov    %rsi,%rax
  40190f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401913:	48 c1 f8 03          	sar    $0x3,%rax
  401917:	48 01 c6             	add    %rax,%rsi
  40191a:	48 d1 fe             	sar    %rsi
  40191d:	74 11                	je     401930 <register_tm_clones+0x30>
  40191f:	b8 00 00 00 00       	mov    $0x0,%eax
  401924:	48 85 c0             	test   %rax,%rax
  401927:	74 07                	je     401930 <register_tm_clones+0x30>
  401929:	bf 10 50 40 00       	mov    $0x405010,%edi
  40192e:	ff e0                	jmp    *%rax
  401930:	c3                   	ret
  401931:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40193c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401940 <__do_global_dtors_aux>:
  401940:	f3 0f 1e fa          	endbr64
  401944:	80 3d c5 36 00 00 00 	cmpb   $0x0,0x36c5(%rip)        # 405010 <__TMC_END__>
  40194b:	75 13                	jne    401960 <__do_global_dtors_aux+0x20>
  40194d:	55                   	push   %rbp
  40194e:	48 89 e5             	mov    %rsp,%rbp
  401951:	e8 7a ff ff ff       	call   4018d0 <deregister_tm_clones>
  401956:	c6 05 b3 36 00 00 01 	movb   $0x1,0x36b3(%rip)        # 405010 <__TMC_END__>
  40195d:	5d                   	pop    %rbp
  40195e:	c3                   	ret
  40195f:	90                   	nop
  401960:	c3                   	ret
  401961:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40196c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401970 <frame_dummy>:
  401970:	f3 0f 1e fa          	endbr64
  401974:	eb 8a                	jmp    401900 <register_tm_clones>
  401976:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401980 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  401980:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  401984:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  401987:	7e 77                	jle    401a00 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  401989:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  40198d:	55                   	push   %rbp
  40198e:	49 89 f2             	mov    %rsi,%r10
  401991:	49 89 d3             	mov    %rdx,%r11
  401994:	53                   	push   %rbx
  401995:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  401998:	48 8b 98 a0 03 00 00 	mov    0x3a0(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  40199f:	b8 01 00 00 00       	mov    $0x1,%eax
  4019a4:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  4019a8:	48 63 d0             	movslq %eax,%rdx
  4019ab:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  4019ae:	85 d2                	test   %edx,%edx
  4019b0:	40 0f 94 c6          	sete   %sil
  4019b4:	f6 c2 04             	test   $0x4,%dl
  4019b7:	75 05                	jne    4019be <pollthreads+0x3e>
  4019b9:	40 84 f6             	test   %sil,%sil
  4019bc:	74 0d                	je     4019cb <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  4019be:	49 63 08             	movslq (%r8),%rcx
  4019c1:	8d 69 01             	lea    0x1(%rcx),%ebp
  4019c4:	41 89 28             	mov    %ebp,(%r8)
  4019c7:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  4019cb:	83 e2 08             	and    $0x8,%edx
  4019ce:	75 05                	jne    4019d5 <pollthreads+0x55>
  4019d0:	40 84 f6             	test   %sil,%sil
  4019d3:	74 1b                	je     4019f0 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  4019d5:	48 63 17             	movslq (%rdi),%rdx
  4019d8:	8d 4a 01             	lea    0x1(%rdx),%ecx
  4019db:	89 0f                	mov    %ecx,(%rdi)
  4019dd:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  4019e1:	83 c0 01             	add    $0x1,%eax
  4019e4:	41 39 41 68          	cmp    %eax,0x68(%r9)
  4019e8:	7f be                	jg     4019a8 <pollthreads+0x28>
}
  4019ea:	31 c0                	xor    %eax,%eax
  4019ec:	5b                   	pop    %rbx
  4019ed:	5d                   	pop    %rbp
  4019ee:	c3                   	ret
  4019ef:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  4019f0:	83 c0 01             	add    $0x1,%eax
  4019f3:	41 39 41 68          	cmp    %eax,0x68(%r9)
  4019f7:	7f af                	jg     4019a8 <pollthreads+0x28>
}
  4019f9:	31 c0                	xor    %eax,%eax
  4019fb:	5b                   	pop    %rbx
  4019fc:	5d                   	pop    %rbp
  4019fd:	c3                   	ret
  4019fe:	66 90                	xchg   %ax,%ax
  401a00:	31 c0                	xor    %eax,%eax
  401a02:	c3                   	ret
  401a03:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401a0e:	66 90                	xchg   %ax,%ax

0000000000401a10 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401a10:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a13:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
      if (*availableidx == 0) {
  401a1a:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a1d:	48 83 c7 01          	add    $0x1,%rdi
  401a21:	48 85 ff             	test   %rdi,%rdi
  401a24:	7e 66                	jle    401a8c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401a26:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a2d:	31 c9                	xor    %ecx,%ecx
  401a2f:	45 31 c9             	xor    %r9d,%r9d
  401a32:	31 c0                	xor    %eax,%eax
  401a34:	eb 18                	jmp    401a4e <findavailable+0x3e>
  401a36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401a40:	83 c1 01             	add    $0x1,%ecx
  401a43:	48 63 c1             	movslq %ecx,%rax
  401a46:	49 89 c1             	mov    %rax,%r9
  401a49:	48 39 f8             	cmp    %rdi,%rax
  401a4c:	7d 3e                	jge    401a8c <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401a4e:	48 c1 e0 05          	shl    $0x5,%rax
  401a52:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401a58:	75 e6                	jne    401a40 <findavailable+0x30>
         available[*availableidx] = x;
  401a5a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  401a5d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401a61:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401a65:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401a68:	41 8b 43 68          	mov    0x68(%r11),%eax
  401a6c:	01 c0                	add    %eax,%eax
  401a6e:	41 39 c0             	cmp    %eax,%r8d
  401a71:	74 19                	je     401a8c <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a73:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  401a7a:	83 c1 01             	add    $0x1,%ecx
  401a7d:	48 63 c1             	movslq %ecx,%rax
  401a80:	48 83 c7 01          	add    $0x1,%rdi
  401a84:	49 89 c1             	mov    %rax,%r9
  401a87:	48 39 f8             	cmp    %rdi,%rax
  401a8a:	7c c2                	jl     401a4e <findavailable+0x3e>
      if (*availableidx == 0) {
  401a8c:	31 c0                	xor    %eax,%eax
  401a8e:	45 85 c0             	test   %r8d,%r8d
  401a91:	0f 94 c0             	sete   %al
}
  401a94:	c3                   	ret
  401a95:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401aa0 <singlewriter3>:
  if (data->writecursor != 0 && (data->writecursor % (data->threadsize - 1)) == 0) {
  401aa0:	8b 87 80 01 00 00    	mov    0x180(%rdi),%eax
  401aa6:	85 c0                	test   %eax,%eax
  401aa8:	74 17                	je     401ac1 <singlewriter3+0x21>
  401aaa:	8b 77 68             	mov    0x68(%rdi),%esi
  401aad:	99                   	cltd
  401aae:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401ab1:	f7 f9                	idiv   %ecx
  401ab3:	85 d2                	test   %edx,%edx
  401ab5:	75 0a                	jne    401ac1 <singlewriter3+0x21>
    data->writecursor = 0;
  401ab7:	c7 87 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rdi)
}
  401ac1:	c3                   	ret
  401ac2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401acd:	0f 1f 00             	nopl   (%rax)

0000000000401ad0 <singlewriter2>:
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401ad0:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  401ad6:	85 c0                	test   %eax,%eax
  401ad8:	74 1e                	je     401af8 <singlewriter2+0x28>
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401ada:	41 54                	push   %r12
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401adc:	99                   	cltd
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401add:	55                   	push   %rbp
  401ade:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401adf:	8b 77 68             	mov    0x68(%rdi),%esi
  401ae2:	48 89 fb             	mov    %rdi,%rbx
  401ae5:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401ae8:	f7 f9                	idiv   %ecx
  401aea:	85 d2                	test   %edx,%edx
  401aec:	74 12                	je     401b00 <singlewriter2+0x30>
}
  401aee:	5b                   	pop    %rbx
  401aef:	5d                   	pop    %rbp
  401af0:	41 5c                	pop    %r12
  401af2:	c3                   	ret
  401af3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401af8:	c3                   	ret
  401af9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    data->readcursor = 0;
  401b00:	c7 87 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdi)
        struct Data * thread = &data->threads[data->threadindex];
  401b0a:	48 63 47 64          	movslq 0x64(%rdi),%rax
  401b0e:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  401b16:	48 29 c5             	sub    %rax,%rbp
  401b19:	48 c1 e5 07          	shl    $0x7,%rbp
  401b1d:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401b21:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401b26:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401b2d:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401b31:	49 c1 e4 04          	shl    $0x4,%r12
  401b35:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401b3c:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401b41:	e8 1a f5 ff ff       	call   401060 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401b46:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401b4c:	83 c0 01             	add    $0x1,%eax
  401b4f:	99                   	cltd
  401b50:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  401b56:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401b59:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401b5f:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401b63:	48 8b 05 3e 16 00 00 	mov    0x163e(%rip),%rax        # 4031a8 <_IO_stdin_used+0x1a8>
  401b6a:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
  401b6f:	5b                   	pop    %rbx
  401b70:	5d                   	pop    %rbp
  401b71:	41 5c                	pop    %r12
  401b73:	c3                   	ret
  401b74:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401b7f:	90                   	nop

0000000000401b80 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b80:	41 55                	push   %r13
  401b82:	49 89 d5             	mov    %rdx,%r13
  401b85:	41 54                	push   %r12
  401b87:	49 89 cc             	mov    %rcx,%r12
  401b8a:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401b8b:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b8e:	48 89 fd             	mov    %rdi,%rbp
  401b91:	53                   	push   %rbx
  401b92:	48 89 f3             	mov    %rsi,%rbx
  401b95:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401b99:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401b9d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401ba6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401bab:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401bad:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401bb5:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  401bbb:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401bc3:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401bcb:	83 c0 01             	add    $0x1,%eax
  401bce:	99                   	cltd
  401bcf:	f7 7f 68             	idivl  0x68(%rdi)
  401bd2:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401bd8:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401bdd:	4c 89 e9             	mov    %r13,%rcx
  401be0:	e8 2b fe ff ff       	call   401a10 <findavailable>
  if (fill == 1) {
  401be5:	83 f8 01             	cmp    $0x1,%eax
  401be8:	0f 84 64 01 00 00    	je     401d52 <singlewriter+0x1d2>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401bee:	48 89 ef             	mov    %rbp,%rdi
  401bf1:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401bf6:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401bfb:	4c 89 e2             	mov    %r12,%rdx
  401bfe:	4c 89 ee             	mov    %r13,%rsi
  401c01:	e8 7a fd ff ff       	call   401980 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401c06:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401c0b:	85 ff                	test   %edi,%edi
  401c0d:	0f 8e 66 01 00 00    	jle    401d79 <singlewriter+0x1f9>
  401c13:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401c18:	31 c9                	xor    %ecx,%ecx
  401c1a:	eb 62                	jmp    401c7e <singlewriter+0xfe>
  401c1c:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c20:	48 8b 14 cb          	mov    (%rbx,%rcx,8),%rdx
          int thread = readyreaders[x];
  401c24:	4d 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%r10
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c29:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401c2c:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c30:	48 c1 e2 05          	shl    $0x5,%rdx
  401c34:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].reading = chunk;
  401c3b:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
          data->threads[thread].start = start;
  401c43:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401c47:	66 0f 6e 4a 08       	movd   0x8(%rdx),%xmm1
          data->threads[thread].reading = chunk;
  401c4c:	4c 29 d0             	sub    %r10,%rax
          chunk->available = READING;
  401c4f:	c7 42 10 02 00 00 00 	movl   $0x2,0x10(%rdx)
          data->threads[thread].reading = chunk;
  401c56:	48 c1 e0 07          	shl    $0x7,%rax
  401c5a:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].start = start;
  401c5e:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401c62:	48 89 90 a8 00 00 00 	mov    %rdx,0xa8(%rax)
          chunk->owner = thread;
  401c69:	44 89 52 14          	mov    %r10d,0x14(%rdx)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401c6d:	83 88 c8 00 00 00 10 	orl    $0x10,0xc8(%rax)
          data->threads[thread].start = start;
  401c74:	66 0f d6 40 14       	movq   %xmm0,0x14(%rax)
        for (int x = 0; x < readers ; x++) {
  401c79:	48 39 cf             	cmp    %rcx,%rdi
  401c7c:	74 07                	je     401c85 <singlewriter+0x105>
  401c7e:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401c80:	4c 39 c1             	cmp    %r8,%rcx
  401c83:	75 9b                	jne    401c20 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401c85:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401c8a:	45 85 c0             	test   %r8d,%r8d
  401c8d:	7e 7a                	jle    401d09 <singlewriter+0x189>
                if (assignedchunk  == availableidx) {
  401c8f:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401c93:	41 01 f0             	add    %esi,%r8d
  401c96:	eb 6d                	jmp    401d05 <singlewriter+0x185>
  401c98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401ca0:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401ca3:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401ca6:	45 8b 0c 24          	mov    (%r12),%r9d
   for (int x = 0; x < writers ; x++) {
  401caa:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401cae:	48 8b 14 f3          	mov    (%rbx,%rsi,8),%rdx
          data->threads[thread].writing = chunk;
  401cb2:	49 63 f1             	movslq %r9d,%rsi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401cb5:	48 c1 e2 05          	shl    $0x5,%rdx
  401cb9:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
          data->threads[thread].writing = chunk;
  401cc0:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
          data->threads[thread].publishstart = start;
  401cc8:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401ccc:	66 0f 6e 52 08       	movd   0x8(%rdx),%xmm2
          data->threads[thread].writing = chunk;
  401cd1:	48 29 f0             	sub    %rsi,%rax
      chunk->available = WRITING;
  401cd4:	c7 42 10 03 00 00 00 	movl   $0x3,0x10(%rdx)
          data->threads[thread].writing = chunk;
  401cdb:	48 c1 e0 07          	shl    $0x7,%rax
  401cdf:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].publishstart = start;
  401ce3:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401ce7:	48 89 90 b0 00 00 00 	mov    %rdx,0xb0(%rax)
          chunk->owner = thread;
  401cee:	44 89 4a 14          	mov    %r9d,0x14(%rdx)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401cf2:	83 88 c8 00 00 00 20 	orl    $0x20,0xc8(%rax)
          data->threads[thread].publishstart = start;
  401cf9:	66 0f d6 40 40       	movq   %xmm0,0x40(%rax)
   for (int x = 0; x < writers ; x++) {
  401cfe:	44 39 c1             	cmp    %r8d,%ecx
  401d01:	74 06                	je     401d09 <singlewriter+0x189>
  401d03:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401d05:	39 f7                	cmp    %esi,%edi
  401d07:	75 97                	jne    401ca0 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401d09:	8b 7d 68             	mov    0x68(%rbp),%edi
  401d0c:	85 ff                	test   %edi,%edi
  401d0e:	7e 40                	jle    401d50 <singlewriter+0x1d0>
        if (data->threads[x].newmask != 0) {
  401d10:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401d14:	31 d2                	xor    %edx,%edx
  401d16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401d20:	48 63 ca             	movslq %edx,%rcx
  401d23:	48 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rax
  401d2b:	48 29 c8             	sub    %rcx,%rax
  401d2e:	48 c1 e0 07          	shl    $0x7,%rax
  401d32:	4c 01 c0             	add    %r8,%rax
  401d35:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401d3b:	85 f6                	test   %esi,%esi
  401d3d:	74 31                	je     401d70 <singlewriter+0x1f0>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401d3f:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401d43:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401d46:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401d49:	8b 7d 68             	mov    0x68(%rbp),%edi
  401d4c:	39 fa                	cmp    %edi,%edx
  401d4e:	7c d0                	jl     401d20 <singlewriter+0x1a0>
  return 0;
  401d50:	31 c0                	xor    %eax,%eax
}
  401d52:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401d57:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401d60:	75 1e                	jne    401d80 <singlewriter+0x200>
  401d62:	48 83 c4 28          	add    $0x28,%rsp
  401d66:	5b                   	pop    %rbx
  401d67:	5d                   	pop    %rbp
  401d68:	41 5c                	pop    %r12
  401d6a:	41 5d                	pop    %r13
  401d6c:	c3                   	ret
  401d6d:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401d70:	83 c2 01             	add    $0x1,%edx
  401d73:	39 fa                	cmp    %edi,%edx
  401d75:	7c a9                	jl     401d20 <singlewriter+0x1a0>
  401d77:	eb d7                	jmp    401d50 <singlewriter+0x1d0>
      int assignedchunk = 0;
  401d79:	31 f6                	xor    %esi,%esi
  401d7b:	e9 05 ff ff ff       	jmp    401c85 <singlewriter+0x105>
}
  401d80:	e8 eb f2 ff ff       	call   401070 <__stack_chk_fail@plt>
  401d85:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401d90 <threadwork>:
int * threadwork(struct Data * data) {
  401d90:	41 57                	push   %r15
  401d92:	41 56                	push   %r14
  401d94:	41 55                	push   %r13
  401d96:	41 54                	push   %r12
  401d98:	55                   	push   %rbp
  401d99:	53                   	push   %rbx
  401d9a:	48 89 fb             	mov    %rdi,%rbx
  401d9d:	48 83 ec 28          	sub    $0x28,%rsp
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401da1:	48 63 4f 68          	movslq 0x68(%rdi),%rcx
  401da5:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401dae:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401db3:	48 8b 47 28          	mov    0x28(%rdi),%rax
  long lastcursor = data->main->writecursor;
  401db7:	8b b0 80 01 00 00    	mov    0x180(%rax),%esi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401dbd:	48 8b 80 38 03 00 00 	mov    0x338(%rax),%rax
  401dc4:	48 99                	cqto
    data->thiswrite = lastcursor;
  401dc6:	89 b7 28 03 00 00    	mov    %esi,0x328(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401dcc:	48 89 e6             	mov    %rsp,%rsi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401dcf:	48 f7 f9             	idiv   %rcx
    data->prevwrite = lastwrite;
  401dd2:	48 89 97 10 03 00 00 	mov    %rdx,0x310(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401dd9:	bf 04 00 00 00       	mov    $0x4,%edi
  401dde:	e8 7d f2 ff ff       	call   401060 <clock_gettime@plt>
     for (int x = 0; x < data->threadsize ; x++) {
  401de3:	8b 43 68             	mov    0x68(%rbx),%eax
   data->freq_writes++;
  401de6:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
     for (int x = 0; x < data->threadsize ; x++) {
  401deb:	31 c9                	xor    %ecx,%ecx
  401ded:	85 c0                	test   %eax,%eax
  401def:	0f 8f fc 00 00 00    	jg     401ef1 <threadwork+0x161>
  401df5:	e9 09 01 00 00       	jmp    401f03 <threadwork+0x173>
  401dfa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401e00:	48 63 83 80 01 00 00 	movslq 0x180(%rbx),%rax
  401e07:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
        epoch->time = time;
  401e0b:	66 0f 6f 04 24       	movdqa (%rsp),%xmm0
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401e10:	48 89 c2             	mov    %rax,%rdx
  401e13:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401e1a:	41 89 d0             	mov    %edx,%r8d
  401e1d:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401e21:	48 c1 e8 20          	shr    $0x20,%rax
  401e25:	01 d0                	add    %edx,%eax
  401e27:	c1 f8 03             	sar    $0x3,%eax
  401e2a:	44 29 c0             	sub    %r8d,%eax
  401e2d:	41 89 c0             	mov    %eax,%r8d
  401e30:	41 c1 e0 04          	shl    $0x4,%r8d
  401e34:	41 29 c0             	sub    %eax,%r8d
  401e37:	89 f0                	mov    %esi,%eax
  401e39:	44 29 c2             	sub    %r8d,%edx
  401e3c:	c1 e0 18             	shl    $0x18,%eax
  401e3f:	09 c2                	or     %eax,%edx
  401e41:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  401e48:	41 89 d2             	mov    %edx,%r10d
  401e4b:	48 89 c2             	mov    %rax,%rdx
  401e4e:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401e55:	41 89 d0             	mov    %edx,%r8d
  401e58:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401e5c:	48 c1 e8 20          	shr    $0x20,%rax
  401e60:	01 d0                	add    %edx,%eax
  401e62:	c1 f8 03             	sar    $0x3,%eax
  401e65:	44 29 c0             	sub    %r8d,%eax
  401e68:	41 89 c0             	mov    %eax,%r8d
  401e6b:	41 c1 e0 04          	shl    $0x4,%r8d
  401e6f:	41 29 c0             	sub    %eax,%r8d
  401e72:	89 c8                	mov    %ecx,%eax
  401e74:	44 29 c2             	sub    %r8d,%edx
  401e77:	c1 e0 08             	shl    $0x8,%eax
  401e7a:	c1 e2 10             	shl    $0x10,%edx
  401e7d:	41 09 d2             	or     %edx,%r10d
  401e80:	41 09 c2             	or     %eax,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  401e83:	48 63 c6             	movslq %esi,%rax
  401e86:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401e8e:	4d 63 d2             	movslq %r10d,%r10
        struct Data * thread = &data->threads[data->threadindex];
  401e91:	49 29 c0             	sub    %rax,%r8
  401e94:	49 c1 e0 07          	shl    $0x7,%r8
  401e98:	4c 03 43 30          	add    0x30(%rbx),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401e9c:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  401ea3:	48 89 d0             	mov    %rdx,%rax
  401ea6:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401eaa:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401ead:	49 c1 e1 04          	shl    $0x4,%r9
  401eb1:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401eb8:	99                   	cltd
        epoch->time = time;
  401eb9:	41 0f 11 41 08       	movups %xmm0,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ebe:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
  data->main->works[buffer] = data->threadindex;
  401ec5:	48 8b 47 70          	mov    0x70(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ec9:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
  epoch->dest = x;
  401ed0:	41 89 49 28          	mov    %ecx,0x28(%r9)
     for (int x = 0; x < data->threadsize ; x++) {
  401ed4:	83 c1 01             	add    $0x1,%ecx
        epoch->thread = data->threadindex;
  401ed7:	41 89 31             	mov    %esi,(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401eda:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  401ede:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
  data->main->works[buffer] = data->threadindex;
  401ee6:	42 88 34 10          	mov    %sil,(%rax,%r10,1)
     for (int x = 0; x < data->threadsize ; x++) {
  401eea:	8b 43 68             	mov    0x68(%rbx),%eax
  401eed:	39 c1                	cmp    %eax,%ecx
  401eef:	7d 12                	jge    401f03 <threadwork+0x173>
  401ef1:	8b 73 64             	mov    0x64(%rbx),%esi
     if (x != data->threadindex) {
  401ef4:	39 ce                	cmp    %ecx,%esi
  401ef6:	0f 85 04 ff ff ff    	jne    401e00 <threadwork+0x70>
     for (int x = 0; x < data->threadsize ; x++) {
  401efc:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401eff:	39 c1                	cmp    %eax,%ecx
  401f01:	7c f1                	jl     401ef4 <threadwork+0x164>
    data->writecursor = (data->writecursor + 1) % 0xf;
  401f03:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
  401f09:	8d 50 01             	lea    0x1(%rax),%edx
  401f0c:	48 63 c2             	movslq %edx,%rax
  401f0f:	89 d1                	mov    %edx,%ecx
  401f11:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401f18:	c1 f9 1f             	sar    $0x1f,%ecx
  401f1b:	48 c1 e8 20          	shr    $0x20,%rax
  401f1f:	01 d0                	add    %edx,%eax
  401f21:	c1 f8 03             	sar    $0x3,%eax
  401f24:	29 c8                	sub    %ecx,%eax
  401f26:	89 c1                	mov    %eax,%ecx
  401f28:	c1 e1 04             	shl    $0x4,%ecx
  401f2b:	29 c1                	sub    %eax,%ecx
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_ACQUIRE);
  401f2d:	48 8b 43 28          	mov    0x28(%rbx),%rax
    data->writecursor = (data->writecursor + 1) % 0xf;
  401f31:	29 ca                	sub    %ecx,%edx
  401f33:	89 93 80 01 00 00    	mov    %edx,0x180(%rbx)
    __atomic_fetch_add(&data->main->globalwrite, 1, __ATOMIC_ACQUIRE);
  401f39:	f0 48 83 80 50 03 00 00 01 	lock addq $0x1,0x350(%rax)
    if (data->main->globalwrite != 0 && (data->main->globalwrite % (data->threadsize)) == 0) {
  401f42:	4c 8b 53 28          	mov    0x28(%rbx),%r10
  401f46:	49 8b 82 50 03 00 00 	mov    0x350(%r10),%rax
  401f4d:	48 85 c0             	test   %rax,%rax
  401f50:	0f 84 e9 01 00 00    	je     40213f <threadwork+0x3af>
  401f56:	48 63 4b 68          	movslq 0x68(%rbx),%rcx
  401f5a:	48 99                	cqto
  401f5c:	48 f7 f9             	idiv   %rcx
  401f5f:	49 89 c8             	mov    %rcx,%r8
  401f62:	48 85 d2             	test   %rdx,%rdx
  401f65:	0f 84 c5 01 00 00    	je     402130 <threadwork+0x3a0>
  long lastread = data->main->totalreads % data->threadsize;
  401f6b:	49 8b 82 40 03 00 00 	mov    0x340(%r10),%rax
   data->freq++;
  401f72:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
  long lastread = data->main->totalreads % data->threadsize;
  401f77:	48 99                	cqto
  401f79:	48 f7 f9             	idiv   %rcx
   data->prevread = lastread;
  401f7c:	48 89 93 08 03 00 00 	mov    %rdx,0x308(%rbx)
  for (int y = 0 ; y < data->threadsize; y++) {
  401f83:	45 85 c0             	test   %r8d,%r8d
  401f86:	0f 8e 1c 01 00 00    	jle    4020a8 <threadwork+0x318>
          if (y != data->threadindex) {
  401f8c:	48 63 43 64          	movslq 0x64(%rbx),%rax
                struct Data * thread = &data->threads[data->threadindex];
  401f90:	31 ff                	xor    %edi,%edi
  for (int y = 0 ; y < data->threadsize; y++) {
  401f92:	31 f6                	xor    %esi,%esi
              past = data->threadsize - 1;
  401f94:	41 8d 68 ff          	lea    -0x1(%r8),%ebp
                struct Data * thread = &data->threads[data->threadindex];
  401f98:	4c 8d 1c c5 00 00 00 00 	lea    0x0(,%rax,8),%r11
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401fa0:	41 89 c4             	mov    %eax,%r12d
          if (y != data->threadindex) {
  401fa3:	49 89 c1             	mov    %rax,%r9
                struct Data * thread = &data->threads[data->threadindex];
  401fa6:	49 29 c3             	sub    %rax,%r11
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  401fa9:	41 c1 e4 08          	shl    $0x8,%r12d
                struct Data * thread = &data->threads[data->threadindex];
  401fad:	49 c1 e3 07          	shl    $0x7,%r11
  401fb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          if (y != data->threadindex) {
  401fb8:	44 39 ce             	cmp    %r9d,%esi
  401fbb:	0f 84 d4 00 00 00    	je     402095 <threadwork+0x305>
            long past = ((data->main->writecursor - 1) % 0xf);
  401fc1:	41 8b 82 80 01 00 00 	mov    0x180(%r10),%eax
            int rc = data->threads[x].writecursor;
  401fc8:	4c 8b 7b 30          	mov    0x30(%rbx),%r15
  401fcc:	41 be 0e 00 00 00    	mov    $0xe,%r14d
            long past = ((data->main->writecursor - 1) % 0xf);
  401fd2:	8d 50 ff             	lea    -0x1(%rax),%edx
  401fd5:	48 63 c2             	movslq %edx,%rax
  401fd8:	89 d1                	mov    %edx,%ecx
  401fda:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401fe1:	c1 f9 1f             	sar    $0x1f,%ecx
  401fe4:	48 c1 e8 20          	shr    $0x20,%rax
  401fe8:	01 d0                	add    %edx,%eax
  401fea:	c1 f8 03             	sar    $0x3,%eax
  401fed:	29 c8                	sub    %ecx,%eax
  401fef:	89 c1                	mov    %eax,%ecx
  401ff1:	c1 e1 04             	shl    $0x4,%ecx
  401ff4:	29 c1                	sub    %eax,%ecx
              past = data->threadsize - 1;
  401ff6:	89 d0                	mov    %edx,%eax
            int rc = data->threads[x].writecursor;
  401ff8:	41 8b 94 3f 80 01 00 00 	mov    0x180(%r15,%rdi,1),%edx
              past = data->threadsize - 1;
  402000:	29 c8                	sub    %ecx,%eax
  402002:	0f 48 c5             	cmovs  %ebp,%eax
  402005:	48 63 c8             	movslq %eax,%rcx
            if (rc < 0) {
  402008:	85 d2                	test   %edx,%edx
  40200a:	78 2d                	js     402039 <threadwork+0x2a9>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40200c:	48 63 c2             	movslq %edx,%rax
  40200f:	41 89 d5             	mov    %edx,%r13d
  402012:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  402019:	41 c1 fd 1f          	sar    $0x1f,%r13d
  40201d:	48 c1 e8 20          	shr    $0x20,%rax
  402021:	01 d0                	add    %edx,%eax
  402023:	c1 f8 03             	sar    $0x3,%eax
  402026:	44 29 e8             	sub    %r13d,%eax
  402029:	41 89 c5             	mov    %eax,%r13d
  40202c:	41 c1 e5 04          	shl    $0x4,%r13d
  402030:	41 29 c5             	sub    %eax,%r13d
  402033:	44 29 ea             	sub    %r13d,%edx
  402036:	4c 63 f2             	movslq %edx,%r14
                struct Data * thread = &data->threads[data->threadindex];
  402039:	4d 01 df             	add    %r11,%r15
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40203c:	48 c1 e1 10          	shl    $0x10,%rcx
            thepoch->time = time; 
  402040:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402045:	49 63 97 24 03 00 00 	movslq 0x324(%r15),%rdx
  40204c:	48 89 d0             	mov    %rdx,%rax
  40204f:	4c 8d 2c 52          	lea    (%rdx,%rdx,2),%r13
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402053:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402056:	49 c1 e5 04          	shl    $0x4,%r13
  40205a:	4d 03 af 18 03 00 00 	add    0x318(%r15),%r13
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402061:	99                   	cltd
            thepoch->time = time; 
  402062:	41 0f 11 4d 08       	movups %xmm1,0x8(%r13)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402067:	41 f7 bf 20 03 00 00 	idivl  0x320(%r15)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40206e:	89 f0                	mov    %esi,%eax
  402070:	c1 e0 18             	shl    $0x18,%eax
  402073:	44 09 e0             	or     %r12d,%eax
  402076:	48 98                	cltq
  402078:	48 09 c8             	or     %rcx,%rax
  40207b:	4c 09 f0             	or     %r14,%rax
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40207e:	41 89 97 24 03 00 00 	mov    %edx,0x324(%r15)
                thepoch->thread = x;
  402085:	41 89 75 00          	mov    %esi,0x0(%r13)
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402089:	49 89 45 18          	mov    %rax,0x18(%r13)
          thepoch->set = 1;
  40208d:	41 c7 45 24 01 00 00 00 	movl   $0x1,0x24(%r13)
  for (int y = 0 ; y < data->threadsize; y++) {
  402095:	83 c6 01             	add    $0x1,%esi
  402098:	48 81 c7 80 03 00 00 	add    $0x380,%rdi
  40209f:	44 39 c6             	cmp    %r8d,%esi
  4020a2:	0f 85 10 ff ff ff    	jne    401fb8 <threadwork+0x228>
     data->readcursor = (data->readcursor + 1) % 0xf;
  4020a8:	8b 83 00 02 00 00    	mov    0x200(%rbx),%eax
  4020ae:	8d 50 01             	lea    0x1(%rax),%edx
  4020b1:	48 63 c2             	movslq %edx,%rax
  4020b4:	89 d1                	mov    %edx,%ecx
  4020b6:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  4020bd:	c1 f9 1f             	sar    $0x1f,%ecx
  4020c0:	48 c1 e8 20          	shr    $0x20,%rax
  4020c4:	01 d0                	add    %edx,%eax
  4020c6:	c1 f8 03             	sar    $0x3,%eax
  4020c9:	29 c8                	sub    %ecx,%eax
  4020cb:	89 c1                	mov    %eax,%ecx
  4020cd:	c1 e1 04             	shl    $0x4,%ecx
  4020d0:	29 c1                	sub    %eax,%ecx
  4020d2:	29 ca                	sub    %ecx,%edx
  4020d4:	89 93 00 02 00 00    	mov    %edx,0x200(%rbx)
    __atomic_fetch_add(&data->main->globalread, 1, __ATOMIC_ACQUIRE);
  4020da:	f0 49 83 82 48 03 00 00 01 	lock addq $0x1,0x348(%r10)
     if (data->main->globalread != 0 && (data->main->globalread % (data->threadsize)) == 0) {
  4020e3:	48 8b 4b 28          	mov    0x28(%rbx),%rcx
  4020e7:	48 8b 81 48 03 00 00 	mov    0x348(%rcx),%rax
  4020ee:	48 85 c0             	test   %rax,%rax
  4020f1:	74 0e                	je     402101 <threadwork+0x371>
  4020f3:	48 63 73 68          	movslq 0x68(%rbx),%rsi
  4020f7:	48 99                	cqto
  4020f9:	48 f7 fe             	idiv   %rsi
  4020fc:	48 85 d2             	test   %rdx,%rdx
  4020ff:	74 4f                	je     402150 <threadwork+0x3c0>
}
  402101:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  402106:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40210f:	0f 85 b0 00 00 00    	jne    4021c5 <threadwork+0x435>
  402115:	48 83 c4 28          	add    $0x28,%rsp
  402119:	31 c0                	xor    %eax,%eax
  40211b:	5b                   	pop    %rbx
  40211c:	5d                   	pop    %rbp
  40211d:	41 5c                	pop    %r12
  40211f:	41 5d                	pop    %r13
  402121:	41 5e                	pop    %r14
  402123:	41 5f                	pop    %r15
  402125:	c3                   	ret
  402126:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      __atomic_store_n(&data->main->globalwrite, 0, __ATOMIC_RELEASE);
  402130:	49 c7 82 50 03 00 00 00 00 00 00 	movq   $0x0,0x350(%r10)
  long lastread = data->main->totalreads % data->threadsize;
  40213b:	4c 8b 53 28          	mov    0x28(%rbx),%r10
  40213f:	48 63 4b 68          	movslq 0x68(%rbx),%rcx
  402143:	49 89 c8             	mov    %rcx,%r8
  402146:	e9 20 fe ff ff       	jmp    401f6b <threadwork+0x1db>
  40214b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  402150:	bf 04 00 00 00       	mov    $0x4,%edi
       __atomic_store_n(&data->main->globalread, 0, __ATOMIC_RELEASE);
  402155:	48 c7 81 48 03 00 00 00 00 00 00 	movq   $0x0,0x348(%rcx)
        struct Data * thread = &data->threads[data->threadindex];
  402160:	48 63 43 64          	movslq 0x64(%rbx),%rax
  402164:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  40216c:	48 29 c5             	sub    %rax,%rbp
  40216f:	48 c1 e5 07          	shl    $0x7,%rbp
  402173:	48 03 6b 30          	add    0x30(%rbx),%rbp
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  402177:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  40217e:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  402182:	49 c1 e4 04          	shl    $0x4,%r12
  402186:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  40218d:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  402192:	e8 c9 ee ff ff       	call   401060 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402197:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  40219d:	83 c0 01             	add    $0x1,%eax
  4021a0:	99                   	cltd
  4021a1:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  4021a7:	8b 43 64             	mov    0x64(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  4021aa:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  4021b0:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  4021b4:	48 8b 05 ed 0f 00 00 	mov    0xfed(%rip),%rax        # 4031a8 <_IO_stdin_used+0x1a8>
  4021bb:	49 89 44 24 20       	mov    %rax,0x20(%r12)
  4021c0:	e9 3c ff ff ff       	jmp    402101 <threadwork+0x371>
}
  4021c5:	e8 a6 ee ff ff       	call   401070 <__stack_chk_fail@plt>
  4021ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000004021d0 <work>:
void * work(void * arg) {
  4021d0:	53                   	push   %rbx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4021d1:	8b 57 64             	mov    0x64(%rdi),%edx
  4021d4:	48 89 fb             	mov    %rdi,%rbx
  4021d7:	31 c0                	xor    %eax,%eax
  4021d9:	48 8d 35 24 0e 00 00 	lea    0xe24(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  4021e0:	bf 01 00 00 00       	mov    $0x1,%edi
  4021e5:	e8 c6 ee ff ff       	call   4010b0 <__printf_chk@plt>
  while (data->running == 1) {
  4021ea:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  4021ee:	75 0e                	jne    4021fe <work+0x2e>
      threadwork(data);
  4021f0:	48 89 df             	mov    %rbx,%rdi
  4021f3:	e8 98 fb ff ff       	call   401d90 <threadwork>
  while (data->running == 1) {
  4021f8:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  4021fc:	74 f2                	je     4021f0 <work+0x20>
  4021fe:	8b 53 64             	mov    0x64(%rbx),%edx
  402201:	48 8d 35 0f 0e 00 00 	lea    0xe0f(%rip),%rsi        # 403017 <_IO_stdin_used+0x17>
  402208:	bf 01 00 00 00       	mov    $0x1,%edi
  40220d:	31 c0                	xor    %eax,%eax
  40220f:	e8 9c ee ff ff       	call   4010b0 <__printf_chk@plt>
}
  402214:	5b                   	pop    %rbx
  402215:	c3                   	ret
  402216:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000402220 <work2>:
  while (data->running == 1) {
  402220:	eb 0b                	jmp    40222d <work2+0xd>
  402222:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  402228:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  40222d:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  402231:	74 f5                	je     402228 <work2+0x8>
}
  402233:	c3                   	ret

Disassembly of section .fini:

0000000000402234 <_fini>:
  402234:	f3 0f 1e fa          	endbr64
  402238:	48 83 ec 08          	sub    $0x8,%rsp
  40223c:	48 83 c4 08          	add    $0x8,%rsp
  402240:	c3                   	ret
