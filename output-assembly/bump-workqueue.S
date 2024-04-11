
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
  4010fc:	48 8d 35 42 1f 00 00 	lea    0x1f42(%rip),%rsi        # 403045 <_IO_stdin_used+0x45>
  401103:	41 56                	push   %r14
  char *works = calloc(worksize, sizeof(char));
  printf("Buffer size %ld\n", worksize);
  int chunkindex = 0;
  int * readcursors = calloc(threadsize, sizeof(int));
  int * writecursors = calloc(threadsize, sizeof(int));
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  401105:	41 be 06 00 00 00    	mov    $0x6,%r14d
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
  401135:	48 8d 35 1b 1f 00 00 	lea    0x1f1b(%rip),%rsi        # 403057 <_IO_stdin_used+0x57>
  40113c:	31 c0                	xor    %eax,%eax
  40113e:	bf 01 00 00 00       	mov    $0x1,%edi
  401143:	e8 68 ff ff ff       	call   4010b0 <__printf_chk@plt>
  401148:	ba 20 00 00 00       	mov    $0x20,%edx
  40114d:	48 8d 35 ff 1e 00 00 	lea    0x1eff(%rip),%rsi        # 403053 <_IO_stdin_used+0x53>
  401154:	31 c0                	xor    %eax,%eax
  401156:	bf 01 00 00 00       	mov    $0x1,%edi
  40115b:	e8 50 ff ff ff       	call   4010b0 <__printf_chk@plt>
  401160:	ba 05 00 00 00       	mov    $0x5,%edx
  401165:	48 8d 35 fa 1e 00 00 	lea    0x1efa(%rip),%rsi        # 403066 <_IO_stdin_used+0x66>
  40116c:	31 c0                	xor    %eax,%eax
  40116e:	bf 01 00 00 00       	mov    $0x1,%edi
  401173:	e8 38 ff ff ff       	call   4010b0 <__printf_chk@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401178:	be 08 00 00 00       	mov    $0x8,%esi
  40117d:	bf 05 00 00 00       	mov    $0x5,%edi
  401182:	e8 19 ff ff ff       	call   4010a0 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401187:	be 38 00 00 00       	mov    $0x38,%esi
  40118c:	bf 05 00 00 00       	mov    $0x5,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401191:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  401196:	e8 05 ff ff ff       	call   4010a0 <calloc@plt>
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40119b:	be 80 11 00 00       	mov    $0x1180,%esi
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
  4011c5:	48 8d 35 af 1e 00 00 	lea    0x1eaf(%rip),%rsi        # 40307b <_IO_stdin_used+0x7b>
  4011cc:	bf 01 00 00 00       	mov    $0x1,%edi
  char *works = calloc(worksize, sizeof(char));
  4011d1:	49 89 c4             	mov    %rax,%r12
  4011d4:	31 c0                	xor    %eax,%eax
  4011d6:	e8 d5 fe ff ff       	call   4010b0 <__printf_chk@plt>
  int * readcursors = calloc(threadsize, sizeof(int));
  4011db:	be 04 00 00 00       	mov    $0x4,%esi
  4011e0:	bf 05 00 00 00       	mov    $0x5,%edi
  4011e5:	4c 8d bb 84 01 00 00 	lea    0x184(%rbx),%r15
  4011ec:	e8 af fe ff ff       	call   4010a0 <calloc@plt>
  int * writecursors = calloc(threadsize, sizeof(int));
  4011f1:	be 04 00 00 00       	mov    $0x4,%esi
  4011f6:	bf 05 00 00 00       	mov    $0x5,%edi
  int * readcursors = calloc(threadsize, sizeof(int));
  4011fb:	48 89 c5             	mov    %rax,%rbp
  int * writecursors = calloc(threadsize, sizeof(int));
  4011fe:	e8 9d fe ff ff       	call   4010a0 <calloc@plt>
  401203:	66 48 0f 6e f5       	movq   %rbp,%xmm6
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  401208:	be 20 00 00 00       	mov    $0x20,%esi
  40120d:	bf 64 00 00 00       	mov    $0x64,%edi
  401212:	66 48 0f 6e c0       	movq   %rax,%xmm0
  401217:	48 8d 2d 6e 1e 00 00 	lea    0x1e6e(%rip),%rbp        # 40308c <_IO_stdin_used+0x8c>
  40121e:	66 0f 6c f0          	punpcklqdq %xmm0,%xmm6
  401222:	0f 29 34 24          	movaps %xmm6,(%rsp)
  401226:	e8 75 fe ff ff       	call   4010a0 <calloc@plt>
  40122b:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
          offset += (threadsize * 2) + 1;
        
     data[chunkindex].writecursors = writecursors;
     data[chunkindex].readcursors = readcursors;
            
    data[chunkindex].owritecursor = middle + 1;
  401230:	41 8d 46 01          	lea    0x1(%r14),%eax
     data[chunkindex].readcursors = readcursors;
  401234:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
  401239:	4c 89 f2             	mov    %r14,%rdx
  40123c:	48 89 ee             	mov    %rbp,%rsi
    data[chunkindex].owritecursor = middle + 1;
  40123f:	41 89 87 80 00 00 00 	mov    %eax,0x80(%r15)
  401246:	bf 01 00 00 00       	mov    $0x1,%edi
  40124b:	31 c0                	xor    %eax,%eax
          for (int x = 0; x < threadsize; x++) {
  40124d:	49 81 c7 80 03 00 00 	add    $0x380,%r15
     data[chunkindex].readcursors = readcursors;
  401254:	41 0f 11 8f 14 fd ff ff 	movups %xmm1,-0x2ec(%r15)
  40125c:	e8 4f fe ff ff       	call   4010b0 <__printf_chk@plt>
    printf("middle %ld\n", middle);
    data[chunkindex].middle = middle;
    data[chunkindex].readcursors[chunkindex] = middle;
  401261:	49 8b 87 14 fd ff ff 	mov    -0x2ec(%r15),%rax
    data[chunkindex].middle = middle;
  401268:	45 89 b7 80 fc ff ff 	mov    %r14d,-0x380(%r15)
    data[chunkindex].readcursors[chunkindex] = middle;
  40126f:	46 89 34 28          	mov    %r14d,(%rax,%r13,1)
    data[chunkindex].writecursors[chunkindex] = middle;
  401273:	49 8b 87 1c fd ff ff 	mov    -0x2e4(%r15),%rax
  40127a:	46 89 34 28          	mov    %r14d,(%rax,%r13,1)
    data[chunkindex].oreadcursor = start;
  40127e:	41 8d 46 fa          	lea    -0x6(%r14),%eax
          for (int x = 0; x < threadsize; x++) {
  401282:	49 83 c6 0b          	add    $0xb,%r14
  401286:	49 83 c5 04          	add    $0x4,%r13
    data[chunkindex].oreadcursor = start;
  40128a:	41 89 87 04 fd ff ff 	mov    %eax,-0x2fc(%r15)
          for (int x = 0; x < threadsize; x++) {
  401291:	49 83 fe 3d          	cmp    $0x3d,%r14
  401295:	75 99                	jne    401230 <main+0x140>
  401297:	ba 37 00 00 00       	mov    $0x37,%edx
  40129c:	bf 01 00 00 00       	mov    $0x1,%edi
  4012a1:	31 c0                	xor    %eax,%eax
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  data[0].works = works;
  4012a3:	49 89 de             	mov    %rbx,%r14
  4012a6:	48 8d 35 eb 1d 00 00 	lea    0x1deb(%rip),%rsi        # 403098 <_IO_stdin_used+0x98>
  int cpu = 0;
  4012ad:	45 31 ed             	xor    %r13d,%r13d
  4012b0:	e8 fb fd ff ff       	call   4010b0 <__printf_chk@plt>
  4012b5:	ba ff ff ff ff       	mov    $0xffffffff,%edx
  4012ba:	48 8d 35 e2 1d 00 00 	lea    0x1de2(%rip),%rsi        # 4030a3 <_IO_stdin_used+0xa3>
  4012c1:	31 c0                	xor    %eax,%eax
  4012c3:	bf 01 00 00 00       	mov    $0x1,%edi
  4012c8:	e8 e3 fd ff ff       	call   4010b0 <__printf_chk@plt>
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  4012cd:	be 04 00 00 00       	mov    $0x4,%esi
  4012d2:	bf 05 00 00 00       	mov    $0x5,%edi
  4012d7:	e8 c4 fd ff ff       	call   4010a0 <calloc@plt>
  4012dc:	66 48 0f 6e f3       	movq   %rbx,%xmm6
  data[0].works = works;
  4012e1:	4c 89 63 78          	mov    %r12,0x78(%rbx)
  4012e5:	45 31 e4             	xor    %r12d,%r12d
  4012e8:	66 48 0f 6e f8       	movq   %rax,%xmm7
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  4012ed:	48 89 c5             	mov    %rax,%rbp
  4012f0:	66 0f 6c fe          	punpcklqdq %xmm6,%xmm7
  4012f4:	0f 29 3c 24          	movaps %xmm7,(%rsp)
  for (int x = 0; x < threadsize ; x++) {
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4012f8:	45 89 ef             	mov    %r13d,%r15d
  4012fb:	be 80 00 00 00       	mov    $0x80,%esi
  401300:	bf 01 00 00 00       	mov    $0x1,%edi
    CPU_SET(cpu += 1, data[x].cpu_set);
  401305:	41 83 c5 01          	add    $0x1,%r13d
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401309:	e8 92 fd ff ff       	call   4010a0 <calloc@plt>
    CPU_SET(cpu += 1, data[x].cpu_set);
  40130e:	44 89 e9             	mov    %r13d,%ecx
  401311:	ba 01 00 00 00       	mov    $0x1,%edx
  401316:	48 8d 35 93 1e 00 00 	lea    0x1e93(%rip),%rsi        # 4031b0 <_IO_stdin_used+0x1b0>
  40131d:	48 d3 e2             	shl    %cl,%rdx
  401320:	48 09 10             	or     %rdx,(%rax)
  401323:	44 89 e9             	mov    %r13d,%ecx
  401326:	44 89 fa             	mov    %r15d,%edx
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401329:	49 89 86 80 00 00 00 	mov    %rax,0x80(%r14)
  401330:	bf 01 00 00 00       	mov    $0x1,%edi
  401335:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize ; x++) {
  401337:	48 83 c5 04          	add    $0x4,%rbp
  40133b:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  401342:	e8 69 fd ff ff       	call   4010b0 <__printf_chk@plt>
    data[x].threadindex = x;
    data[x].worksize = worksize;
    
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].readies = readies;
  401347:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
    data[x].readies[x] = 0;
    data[x].buckets = buckets;
  40134c:	48 8b 05 85 1e 00 00 	mov    0x1e85(%rip),%rax        # 4031d8 <_IO_stdin_used+0x1d8>
    data[x].bucketstart = x * buckets ;
  401353:	45 89 a6 20 fd ff ff 	mov    %r12d,-0x2e0(%r14)
    data[x].main = &data[0];
    data[x].threads = data;
    data[x].wantindex = -1;
    data[x].read = 0;
  40135a:	66 0f 6f 1d 8e 1e 00 00 	movdqa 0x1e8e(%rip),%xmm3        # 4031f0 <_IO_stdin_used+0x1f0>
    data[x].newmask = 0;
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401362:	be 30 00 00 00       	mov    $0x30,%esi
    data[x].chunkslen = chunkslen;
  401367:	66 0f 6f 25 91 1e 00 00 	movdqa 0x1e91(%rip),%xmm4        # 403200 <_IO_stdin_used+0x200>
    data[x].loglevel = debug;
  40136f:	41 c7 86 08 fd ff ff 00 00 00 00 	movl   $0x0,-0x2f8(%r14)
    data[x].buckets = buckets;
  40137a:	49 89 86 18 fd ff ff 	mov    %rax,-0x2e8(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401381:	bf 80 96 98 00       	mov    $0x989680,%edi
    data[x].wantindex = -1;
  401386:	48 8b 05 53 1e 00 00 	mov    0x1e53(%rip),%rax        # 4031e0 <_IO_stdin_used+0x1e0>
  for (int x = 0; x < threadsize ; x++) {
  40138d:	41 81 c4 33 33 33 33 	add    $0x33333333,%r12d
    data[x].prevread = threadsize;
  401394:	66 0f 6f 2d 74 1e 00 00 	movdqa 0x1e74(%rip),%xmm5        # 403210 <_IO_stdin_used+0x210>
    data[x].threadindex = x;
  40139c:	45 89 be ec fc ff ff 	mov    %r15d,-0x314(%r14)
    data[x].wantindex = -1;
  4013a3:	49 89 86 e0 fc ff ff 	mov    %rax,-0x320(%r14)
    data[x].freelist = freelist;
  4013aa:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    data[x].worksize = worksize;
  4013af:	41 c7 86 e8 fc ff ff ff ff ff ff 	movl   $0xffffffff,-0x318(%r14)
    data[x].threadsize = threadsize;
  4013ba:	41 c7 86 f0 fc ff ff 05 00 00 00 	movl   $0x5,-0x310(%r14)
    data[x].readies[x] = 0;
  4013c5:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
    data[x].threads = data;
  4013cc:	49 89 9e b0 fc ff ff 	mov    %rbx,-0x350(%r14)
    data[x].readcursor = threadsize - 1;
  4013d3:	41 c7 86 80 fe ff ff 04 00 00 00 	movl   $0x4,-0x180(%r14)
    data[x].writecursor = threadsize - 1;
  4013de:	41 c7 86 00 fe ff ff 04 00 00 00 	movl   $0x4,-0x200(%r14)
    data[x].freelist = freelist;
  4013e9:	49 89 86 28 fd ff ff 	mov    %rax,-0x2d8(%r14)
    data[x].newmask = 0;
  4013f0:	41 c7 86 50 fd ff ff 00 00 00 00 	movl   $0x0,-0x2b0(%r14)
    data[x].thiswrite = threadsize;
  4013fb:	41 c7 46 a8 05 00 00 00 	movl   $0x5,-0x58(%r14)
    data[x].readies = readies;
  401403:	41 0f 29 96 a0 fc ff ff 	movaps %xmm2,-0x360(%r14)
    data[x].read = 0;
  40140b:	41 0f 29 9e 80 fc ff ff 	movaps %xmm3,-0x380(%r14)
    data[x].chunkslen = chunkslen;
  401413:	41 0f 29 a6 40 fd ff ff 	movaps %xmm4,-0x2c0(%r14)
    data[x].prevread = threadsize;
  40141b:	41 0f 11 6e 88       	movups %xmm5,-0x78(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401420:	e8 7b fc ff ff       	call   4010a0 <calloc@plt>
    data[x].epochssize = epochs;
    
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  401425:	be 30 00 00 00       	mov    $0x30,%esi
  40142a:	bf 10 27 00 00       	mov    $0x2710,%edi
    data[x].epochssize = epochs;
  40142f:	41 c7 46 a0 80 96 98 00 	movl   $0x989680,-0x60(%r14)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  401437:	49 89 46 98          	mov    %rax,-0x68(%r14)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  40143b:	e8 60 fc ff ff       	call   4010a0 <calloc@plt>
  401440:	49 89 46 b0          	mov    %rax,-0x50(%r14)
  for (int x = 0; x < threadsize ; x++) {
  401444:	41 83 fd 05          	cmp    $0x5,%r13d
  401448:	0f 85 aa fe ff ff    	jne    4012f8 <main+0x208>
  40144e:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
  401453:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
  401458:	48 89 1c 24          	mov    %rbx,(%rsp)
  40145c:	49 89 de             	mov    %rbx,%r14
  40145f:	49 c7 c5 30 21 40 00 	mov    $0x402130,%r13
  401466:	48 8d 8d 18 01 00 00 	lea    0x118(%rbp),%rcx
  40146d:	49 89 c4             	mov    %rax,%r12
  401470:	48 89 c3             	mov    %rax,%rbx
  401473:	49 89 cf             	mov    %rcx,%r15
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  401476:	4c 89 f1             	mov    %r14,%rcx
  401479:	48 89 ee             	mov    %rbp,%rsi
  40147c:	48 89 df             	mov    %rbx,%rdi
  40147f:	4c 89 ea             	mov    %r13,%rdx
  401482:	e8 39 fc ff ff       	call   4010c0 <pthread_create@plt>
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401487:	48 8b 3b             	mov    (%rbx),%rdi
  for (int x = 0; x < threadsize ; x++) {
  40148a:	48 83 c5 38          	add    $0x38,%rbp
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  40148e:	49 8b 96 80 00 00 00 	mov    0x80(%r14),%rdx
  401495:	be 08 00 00 00       	mov    $0x8,%esi
  for (int x = 0; x < threadsize ; x++) {
  40149a:	48 83 c3 08          	add    $0x8,%rbx
  40149e:	49 81 c6 80 03 00 00 	add    $0x380,%r14
     pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  4014a5:	e8 96 fb ff ff       	call   401040 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  4014aa:	49 39 ef             	cmp    %rbp,%r15
  4014ad:	75 c7                	jne    401476 <main+0x386>
  }
  
  struct timespec time = {
  4014af:	48 8b 1c 24          	mov    (%rsp),%rbx
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  4014b3:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  4014b8:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec time = {
  4014bd:	66 0f 6f 05 5b 1d 00 00 	movdqa 0x1d5b(%rip),%xmm0        # 403220 <_IO_stdin_used+0x220>
  4014c5:	4c 8d 6c 24 38       	lea    0x38(%rsp),%r13
  4014ca:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  struct timespec rem = {
  4014cf:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4014d3:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&time, &rem);
  4014d8:	e8 a3 fb ff ff       	call   401080 <nanosleep@plt>
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
  4014dd:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
  4014e2:	c7 43 64 00 00 00 00 	movl   $0x0,0x64(%rbx)
  4014e9:	c7 83 e4 03 00 00 00 00 00 00 	movl   $0x0,0x3e4(%rbx)
  4014f3:	c7 83 64 07 00 00 00 00 00 00 	movl   $0x0,0x764(%rbx)
  4014fd:	48 83 c5 28          	add    $0x28,%rbp
  401501:	c7 83 e4 0a 00 00 00 00 00 00 	movl   $0x0,0xae4(%rbx)
  40150b:	c7 83 64 0e 00 00 00 00 00 00 	movl   $0x0,0xe64(%rbx)
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401515:	49 8b 3c 24          	mov    (%r12),%rdi
  401519:	4c 89 ee             	mov    %r13,%rsi
  for (int x = 0; x < threadsize; x++) {
  40151c:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &res);
  401520:	e8 bb fb ff ff       	call   4010e0 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  401525:	49 39 ec             	cmp    %rbp,%r12
  401528:	75 eb                	jne    401515 <main+0x425>
  40152a:	48 8d 3d 7e 1b 00 00 	lea    0x1b7e(%rip),%rdi        # 4030af <_IO_stdin_used+0xaf>
  401531:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  401535:	45 31 e4             	xor    %r12d,%r12d
  401538:	e8 13 fb ff ff       	call   401050 <puts@plt>
  for (int x = 0; x < threadsize; x++) {
  40153d:	4c 8d b3 c8 11 00 00 	lea    0x11c8(%rbx),%r14
  401544:	4c 8d 2d 79 1b 00 00 	lea    0x1b79(%rip),%r13        # 4030c4 <_IO_stdin_used+0xc4>
  40154b:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  40154f:	4c 89 ee             	mov    %r13,%rsi
  401552:	bf 01 00 00 00       	mov    $0x1,%edi
  401557:	31 c0                	xor    %eax,%eax
  401559:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
  401560:	e8 4b fb ff ff       	call   4010b0 <__printf_chk@plt>
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  401565:	4c 03 a5 80 fc ff ff 	add    -0x380(%rbp),%r12
  for (int x = 0; x < threadsize; x++) {
  40156c:	4c 39 f5             	cmp    %r14,%rbp
  40156f:	75 da                	jne    40154b <main+0x45b>
  }
  printf("freq: %ld\n", freq/ seconds);
  printf("freq_ps: %ld\n", (freq*threadsize-1)/ seconds);
  401571:	4f 8d 6c a4 ff       	lea    -0x1(%r12,%r12,4),%r13
  401576:	4c 89 e2             	mov    %r12,%rdx
  401579:	bf 01 00 00 00       	mov    $0x1,%edi
  40157e:	31 c0                	xor    %eax,%eax
  401580:	48 8d 35 48 1b 00 00 	lea    0x1b48(%rip),%rsi        # 4030cf <_IO_stdin_used+0xcf>
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  401587:	bd 00 ca 9a 3b       	mov    $0x3b9aca00,%ebp
  40158c:	4c 8d b3 d0 11 00 00 	lea    0x11d0(%rbx),%r14
  401593:	e8 18 fb ff ff       	call   4010b0 <__printf_chk@plt>
  401598:	4c 89 ea             	mov    %r13,%rdx
  40159b:	bf 01 00 00 00       	mov    $0x1,%edi
  4015a0:	31 c0                	xor    %eax,%eax
  4015a2:	48 8d 35 31 1b 00 00 	lea    0x1b31(%rip),%rsi        # 4030da <_IO_stdin_used+0xda>
  4015a9:	e8 02 fb ff ff       	call   4010b0 <__printf_chk@plt>
  4015ae:	48 89 e8             	mov    %rbp,%rax
  4015b1:	bf 01 00 00 00       	mov    $0x1,%edi
  4015b6:	48 8d 35 2b 1b 00 00 	lea    0x1b2b(%rip),%rsi        # 4030e8 <_IO_stdin_used+0xe8>
  4015bd:	48 99                	cqto
  4015bf:	49 f7 fc             	idiv   %r12
  printf("freq latency: %ld\n", 1000000000/((freq*threadsize-1)/seconds));
  long freq_writes = 0;
  4015c2:	45 31 e4             	xor    %r12d,%r12d
  4015c5:	48 89 c2             	mov    %rax,%rdx
  4015c8:	31 c0                	xor    %eax,%eax
  4015ca:	e8 e1 fa ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*threadsize-1)/seconds));
  4015cf:	48 89 e8             	mov    %rbp,%rax
  4015d2:	bf 01 00 00 00       	mov    $0x1,%edi
  4015d7:	48 8d 35 1e 1b 00 00 	lea    0x1b1e(%rip),%rsi        # 4030fc <_IO_stdin_used+0xfc>
  4015de:	48 99                	cqto
  4015e0:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  4015e4:	49 f7 fd             	idiv   %r13
  4015e7:	4c 8d 2d 21 1b 00 00 	lea    0x1b21(%rip),%r13        # 40310f <_IO_stdin_used+0x10f>
  4015ee:	48 89 c2             	mov    %rax,%rdx
  4015f1:	31 c0                	xor    %eax,%eax
  4015f3:	e8 b8 fa ff ff       	call   4010b0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  4015f8:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4015fc:	4c 89 ee             	mov    %r13,%rsi
  4015ff:	bf 01 00 00 00       	mov    $0x1,%edi
  401604:	31 c0                	xor    %eax,%eax
  for (int x = 0; x < threadsize; x++) {
  401606:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
    freq_writes += data[x].freq_writes;
  40160d:	49 01 d4             	add    %rdx,%r12
  401610:	e8 9b fa ff ff       	call   4010b0 <__printf_chk@plt>
  for (int x = 0; x < threadsize; x++) {
  401615:	4c 39 f5             	cmp    %r14,%rbp
  401618:	75 de                	jne    4015f8 <main+0x508>
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);

  printf("freq_writes_total: %ld\n", (freq_writes * threadsize - 1) / seconds);
  40161a:	4f 8d 6c a4 ff       	lea    -0x1(%r12,%r12,4),%r13
  40161f:	4c 89 e2             	mov    %r12,%rdx
  401622:	bf 01 00 00 00       	mov    $0x1,%edi
  401627:	31 c0                	xor    %eax,%eax
  401629:	48 8d 35 eb 1a 00 00 	lea    0x1aeb(%rip),%rsi        # 40311b <_IO_stdin_used+0x11b>
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  401630:	bd 00 ca 9a 3b       	mov    $0x3b9aca00,%ebp
  401635:	4c 8d b3 20 03 00 00 	lea    0x320(%rbx),%r14
  40163c:	e8 6f fa ff ff       	call   4010b0 <__printf_chk@plt>
  401641:	4c 89 ea             	mov    %r13,%rdx
  401644:	bf 01 00 00 00       	mov    $0x1,%edi
  401649:	31 c0                	xor    %eax,%eax
  40164b:	48 8d 35 db 1a 00 00 	lea    0x1adb(%rip),%rsi        # 40312d <_IO_stdin_used+0x12d>
  401652:	e8 59 fa ff ff       	call   4010b0 <__printf_chk@plt>
  401657:	48 89 e8             	mov    %rbp,%rax
  40165a:	bf 01 00 00 00       	mov    $0x1,%edi
  40165f:	48 8d 35 df 1a 00 00 	lea    0x1adf(%rip),%rsi        # 403145 <_IO_stdin_used+0x145>
  401666:	48 99                	cqto
  401668:	49 f7 fc             	idiv   %r12
  40166b:	48 89 c2             	mov    %rax,%rdx
  40166e:	31 c0                	xor    %eax,%eax
  401670:	e8 3b fa ff ff       	call   4010b0 <__printf_chk@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * threadsize - 1) / seconds));
  401675:	48 89 e8             	mov    %rbp,%rax
  401678:	bf 01 00 00 00       	mov    $0x1,%edi
  40167d:	48 8d 35 dc 1a 00 00 	lea    0x1adc(%rip),%rsi        # 403160 <_IO_stdin_used+0x160>
  401684:	48 99                	cqto
  401686:	48 8d 2d 6a 1a 00 00 	lea    0x1a6a(%rip),%rbp        # 4030f7 <_IO_stdin_used+0xf7>
  40168d:	49 f7 fd             	idiv   %r13
  401690:	48 89 c2             	mov    %rax,%rdx
  401693:	31 c0                	xor    %eax,%eax
  401695:	e8 16 fa ff ff       	call   4010b0 <__printf_chk@plt>
  40169a:	48 8d 3d d9 1a 00 00 	lea    0x1ad9(%rip),%rdi        # 40317a <_IO_stdin_used+0x17a>
  4016a1:	e8 aa f9 ff ff       	call   401050 <puts@plt>
  4016a6:	48 89 ee             	mov    %rbp,%rsi
  4016a9:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ae:	31 c0                	xor    %eax,%eax
    
  }
  */
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  4016b0:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
  4016b7:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  4016be:	e8 ed f9 ff ff       	call   4010b0 <__printf_chk@plt>
  4016c3:	48 89 ee             	mov    %rbp,%rsi
  4016c6:	bf 01 00 00 00       	mov    $0x1,%edi
  4016cb:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  4016cd:	48 8b 93 08 01 00 00 	mov    0x108(%rbx),%rdx
  4016d4:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  4016db:	e8 d0 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  4016e0:	48 89 ee             	mov    %rbp,%rsi
  4016e3:	bf 01 00 00 00       	mov    $0x1,%edi
  4016e8:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  4016ea:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
  4016f1:	48 2b 93 08 01 00 00 	sub    0x108(%rbx),%rdx
  4016f8:	e8 b3 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  4016fd:	48 89 ee             	mov    %rbp,%rsi
  401700:	bf 01 00 00 00       	mov    $0x1,%edi
  401705:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  401707:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
  40170e:	48 2b 93 18 01 00 00 	sub    0x118(%rbx),%rdx
  401715:	e8 96 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  40171a:	48 89 ee             	mov    %rbp,%rsi
  40171d:	bf 01 00 00 00       	mov    $0x1,%edi
  401722:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  401724:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
  40172b:	48 2b 93 28 01 00 00 	sub    0x128(%rbx),%rdx
  401732:	e8 79 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  401737:	48 89 ee             	mov    %rbp,%rsi
  40173a:	bf 01 00 00 00       	mov    $0x1,%edi
  40173f:	31 c0                	xor    %eax,%eax
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  401741:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
  401748:	48 2b 93 08 01 00 00 	sub    0x108(%rbx),%rdx
  40174f:	e8 5c f9 ff ff       	call   4010b0 <__printf_chk@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  401754:	48 8b 93 48 01 00 00 	mov    0x148(%rbx),%rdx
  40175b:	bf 01 00 00 00       	mov    $0x1,%edi
  401760:	48 2b 93 38 01 00 00 	sub    0x138(%rbx),%rdx
  401767:	48 8d 35 19 1a 00 00 	lea    0x1a19(%rip),%rsi        # 403187 <_IO_stdin_used+0x187>
  40176e:	31 c0                	xor    %eax,%eax
  401770:	48 81 c3 a0 14 00 00 	add    $0x14a0,%rbx
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  401777:	45 31 ed             	xor    %r13d,%r13d
  40177a:	e8 31 f9 ff ff       	call   4010b0 <__printf_chk@plt>
  } 

  if (SAMPLE == 1) {
  char * filename = calloc(100, sizeof(char));
  40177f:	be 01 00 00 00       	mov    $0x1,%esi
  401784:	bf 64 00 00 00       	mov    $0x64,%edi
  401789:	e8 12 f9 ff ff       	call   4010a0 <calloc@plt>
  char * buf = calloc(1000, sizeof(char));
  40178e:	be 01 00 00 00       	mov    $0x1,%esi
  401793:	bf e8 03 00 00       	mov    $0x3e8,%edi
  char * filename = calloc(100, sizeof(char));
  401798:	49 89 c4             	mov    %rax,%r12
  char * buf = calloc(1000, sizeof(char));
  40179b:	e8 00 f9 ff ff       	call   4010a0 <calloc@plt>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  4017a0:	44 8b 8b d0 eb ff ff 	mov    -0x1430(%rbx),%r9d
  4017a7:	4c 89 e7             	mov    %r12,%rdi
  4017aa:	4c 8d 05 de 19 00 00 	lea    0x19de(%rip),%r8        # 40318f <_IO_stdin_used+0x18f>
  4017b1:	b9 64 00 00 00       	mov    $0x64,%ecx
  4017b6:	ba 01 00 00 00       	mov    $0x1,%edx
  4017bb:	be 64 00 00 00       	mov    $0x64,%esi
  4017c0:	48 89 c5             	mov    %rax,%rbp
  4017c3:	31 c0                	xor    %eax,%eax
  4017c5:	e8 66 f8 ff ff       	call   401030 <__snprintf_chk@plt>
  memset(filename, 0, 100);
  snprintf(filename, 100, "samples%d", data->threadsize);
  FILE *out_file = fopen(filename, "w");
  4017ca:	4c 89 e7             	mov    %r12,%rdi
  4017cd:	48 8d 35 c5 19 00 00 	lea    0x19c5(%rip),%rsi        # 403199 <_IO_stdin_used+0x199>
  4017d4:	e8 f7 f8 ff ff       	call   4010d0 <fopen@plt>
  4017d9:	49 89 c4             	mov    %rax,%r12
  
  for (int x = 0; x < threadsize; x++) {
    for (int y = 0; y < data[x].epochssize; y++) {
  4017dc:	41 8b 0e             	mov    (%r14),%ecx
  4017df:	45 31 ff             	xor    %r15d,%r15d
  4017e2:	85 c9                	test   %ecx,%ecx
  4017e4:	7e 21                	jle    401807 <main+0x717>
  4017e6:	49 8b 76 f8          	mov    -0x8(%r14),%rsi
      struct Epoch * epoch = &data[x].epochs[y];
  4017ea:	49 63 c7             	movslq %r15d,%rax
  4017ed:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  4017f1:	48 c1 e2 04          	shl    $0x4,%rdx
  4017f5:	48 01 f2             	add    %rsi,%rdx
      if (epoch->set == 1) {
  4017f8:	83 7a 24 01          	cmpl   $0x1,0x24(%rdx)
  4017fc:	74 42                	je     401840 <main+0x750>
    for (int y = 0; y < data[x].epochssize; y++) {
  4017fe:	41 83 c7 01          	add    $0x1,%r15d
  401802:	41 39 cf             	cmp    %ecx,%r15d
  401805:	7c e3                	jl     4017ea <main+0x6fa>
  for (int x = 0; x < threadsize; x++) {
  401807:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  40180e:	49 39 de             	cmp    %rbx,%r14
  401811:	75 c9                	jne    4017dc <main+0x6ec>
        fprintf(out_file, "%s", buf);
      }
    }
  }
  }
  401813:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  401818:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401821:	0f 85 94 00 00 00    	jne    4018bb <main+0x7cb>
  401827:	48 83 c4 78          	add    $0x78,%rsp
  40182b:	31 c0                	xor    %eax,%eax
  40182d:	5b                   	pop    %rbx
  40182e:	5d                   	pop    %rbp
  40182f:	41 5c                	pop    %r12
  401831:	41 5d                	pop    %r13
  401833:	41 5e                	pop    %r14
  401835:	41 5f                	pop    %r15
  401837:	c3                   	ret
  401838:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  401840:	4c 89 e8             	mov    %r13,%rax
  401843:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401848:	48 89 ef             	mov    %rbp,%rdi
  40184b:	48 83 ec 08          	sub    $0x8,%rsp
  40184f:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  401852:	be 64 00 00 00       	mov    $0x64,%esi
  401857:	48 89 ef             	mov    %rbp,%rdi
    for (int y = 0; y < data[x].epochssize; y++) {
  40185a:	41 83 c7 01          	add    $0x1,%r15d
  40185e:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401863:	4c 8d 05 31 19 00 00 	lea    0x1931(%rip),%r8        # 40319b <_IO_stdin_used+0x19b>
  40186a:	8b 42 28             	mov    0x28(%rdx),%eax
  40186d:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
  401871:	50                   	push   %rax
  401872:	8b 02                	mov    (%rdx),%eax
  401874:	50                   	push   %rax
  401875:	8b 42 20             	mov    0x20(%rdx),%eax
  401878:	ff 72 18             	push   0x18(%rdx)
  40187b:	50                   	push   %rax
  40187c:	31 c0                	xor    %eax,%eax
  40187e:	ff 72 10             	push   0x10(%rdx)
  401881:	ba 01 00 00 00       	mov    $0x1,%edx
  401886:	e8 a5 f7 ff ff       	call   401030 <__snprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  40188b:	48 83 c4 30          	add    $0x30,%rsp
  40188f:	4c 89 e6             	mov    %r12,%rsi
  401892:	48 89 ef             	mov    %rbp,%rdi
  401895:	e8 f6 f7 ff ff       	call   401090 <fputs@plt>
  40189a:	41 8b 0e             	mov    (%r14),%ecx
  40189d:	41 39 cf             	cmp    %ecx,%r15d
  4018a0:	0f 8c 40 ff ff ff    	jl     4017e6 <main+0x6f6>
  for (int x = 0; x < threadsize; x++) {
  4018a6:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  4018ad:	49 39 de             	cmp    %rbx,%r14
  4018b0:	0f 85 26 ff ff ff    	jne    4017dc <main+0x6ec>
  4018b6:	e9 58 ff ff ff       	jmp    401813 <main+0x723>
  4018bb:	e8 b0 f7 ff ff       	call   401070 <__stack_chk_fail@plt>

00000000004018c0 <_start>:
  4018c0:	f3 0f 1e fa          	endbr64
  4018c4:	31 ed                	xor    %ebp,%ebp
  4018c6:	49 89 d1             	mov    %rdx,%r9
  4018c9:	5e                   	pop    %rsi
  4018ca:	48 89 e2             	mov    %rsp,%rdx
  4018cd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4018d1:	50                   	push   %rax
  4018d2:	54                   	push   %rsp
  4018d3:	45 31 c0             	xor    %r8d,%r8d
  4018d6:	31 c9                	xor    %ecx,%ecx
  4018d8:	48 c7 c7 f0 10 40 00 	mov    $0x4010f0,%rdi
  4018df:	ff 15 0b 37 00 00    	call   *0x370b(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  4018e5:	f4                   	hlt
  4018e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004018f0 <_dl_relocate_static_pie>:
  4018f0:	f3 0f 1e fa          	endbr64
  4018f4:	c3                   	ret
  4018f5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4018ff:	90                   	nop

0000000000401900 <deregister_tm_clones>:
  401900:	b8 10 50 40 00       	mov    $0x405010,%eax
  401905:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  40190b:	74 13                	je     401920 <deregister_tm_clones+0x20>
  40190d:	b8 00 00 00 00       	mov    $0x0,%eax
  401912:	48 85 c0             	test   %rax,%rax
  401915:	74 09                	je     401920 <deregister_tm_clones+0x20>
  401917:	bf 10 50 40 00       	mov    $0x405010,%edi
  40191c:	ff e0                	jmp    *%rax
  40191e:	66 90                	xchg   %ax,%ax
  401920:	c3                   	ret
  401921:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40192c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401930 <register_tm_clones>:
  401930:	be 10 50 40 00       	mov    $0x405010,%esi
  401935:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  40193c:	48 89 f0             	mov    %rsi,%rax
  40193f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401943:	48 c1 f8 03          	sar    $0x3,%rax
  401947:	48 01 c6             	add    %rax,%rsi
  40194a:	48 d1 fe             	sar    %rsi
  40194d:	74 11                	je     401960 <register_tm_clones+0x30>
  40194f:	b8 00 00 00 00       	mov    $0x0,%eax
  401954:	48 85 c0             	test   %rax,%rax
  401957:	74 07                	je     401960 <register_tm_clones+0x30>
  401959:	bf 10 50 40 00       	mov    $0x405010,%edi
  40195e:	ff e0                	jmp    *%rax
  401960:	c3                   	ret
  401961:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40196c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401970 <__do_global_dtors_aux>:
  401970:	f3 0f 1e fa          	endbr64
  401974:	80 3d 95 36 00 00 00 	cmpb   $0x0,0x3695(%rip)        # 405010 <__TMC_END__>
  40197b:	75 13                	jne    401990 <__do_global_dtors_aux+0x20>
  40197d:	55                   	push   %rbp
  40197e:	48 89 e5             	mov    %rsp,%rbp
  401981:	e8 7a ff ff ff       	call   401900 <deregister_tm_clones>
  401986:	c6 05 83 36 00 00 01 	movb   $0x1,0x3683(%rip)        # 405010 <__TMC_END__>
  40198d:	5d                   	pop    %rbp
  40198e:	c3                   	ret
  40198f:	90                   	nop
  401990:	c3                   	ret
  401991:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40199c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004019a0 <frame_dummy>:
  4019a0:	f3 0f 1e fa          	endbr64
  4019a4:	eb 8a                	jmp    401930 <register_tm_clones>
  4019a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004019b0 <pollthreads>:
  for (int x = 1; x < data->threadsize ; x++) {
  4019b0:	83 7f 70 01          	cmpl   $0x1,0x70(%rdi)
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4019b4:	49 89 f9             	mov    %rdi,%r9
  for (int x = 1; x < data->threadsize ; x++) {
  4019b7:	7e 77                	jle    401a30 <pollthreads+0x80>
    int mask = data->threads[1].readies[x];
  4019b9:	49 8b 41 30          	mov    0x30(%r9),%rax
int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4019bd:	55                   	push   %rbp
  4019be:	49 89 f2             	mov    %rsi,%r10
  4019c1:	49 89 d3             	mov    %rdx,%r11
  4019c4:	53                   	push   %rbx
  4019c5:	48 89 cf             	mov    %rcx,%rdi
    int mask = data->threads[1].readies[x];
  4019c8:	48 8b 98 a0 03 00 00 	mov    0x3a0(%rax),%rbx
  for (int x = 1; x < data->threadsize ; x++) {
  4019cf:	b8 01 00 00 00       	mov    $0x1,%eax
  4019d4:	0f 1f 40 00          	nopl   0x0(%rax)
    int mask = data->threads[1].readies[x];
  4019d8:	48 63 d0             	movslq %eax,%rdx
  4019db:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
        if ((mask & WM) == WM || mask == 0) {
  4019de:	85 d2                	test   %edx,%edx
  4019e0:	40 0f 94 c6          	sete   %sil
  4019e4:	f6 c2 04             	test   $0x4,%dl
  4019e7:	75 05                	jne    4019ee <pollthreads+0x3e>
  4019e9:	40 84 f6             	test   %sil,%sil
  4019ec:	74 0d                	je     4019fb <pollthreads+0x4b>
          readywriters[(*writers)++] = x;
  4019ee:	49 63 08             	movslq (%r8),%rcx
  4019f1:	8d 69 01             	lea    0x1(%rcx),%ebp
  4019f4:	41 89 28             	mov    %ebp,(%r8)
  4019f7:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
    if ((mask & RM) == RM || mask == 0) {
  4019fb:	83 e2 08             	and    $0x8,%edx
  4019fe:	75 05                	jne    401a05 <pollthreads+0x55>
  401a00:	40 84 f6             	test   %sil,%sil
  401a03:	74 1b                	je     401a20 <pollthreads+0x70>
      readyreaders[(*readers)++] = x;
  401a05:	48 63 17             	movslq (%rdi),%rdx
  401a08:	8d 4a 01             	lea    0x1(%rdx),%ecx
  401a0b:	89 0f                	mov    %ecx,(%rdi)
  401a0d:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  for (int x = 1; x < data->threadsize ; x++) {
  401a11:	83 c0 01             	add    $0x1,%eax
  401a14:	41 39 41 70          	cmp    %eax,0x70(%r9)
  401a18:	7f be                	jg     4019d8 <pollthreads+0x28>
}
  401a1a:	31 c0                	xor    %eax,%eax
  401a1c:	5b                   	pop    %rbx
  401a1d:	5d                   	pop    %rbp
  401a1e:	c3                   	ret
  401a1f:	90                   	nop
  for (int x = 1; x < data->threadsize ; x++) {
  401a20:	83 c0 01             	add    $0x1,%eax
  401a23:	41 39 41 70          	cmp    %eax,0x70(%r9)
  401a27:	7f af                	jg     4019d8 <pollthreads+0x28>
}
  401a29:	31 c0                	xor    %eax,%eax
  401a2b:	5b                   	pop    %rbx
  401a2c:	5d                   	pop    %rbp
  401a2d:	c3                   	ret
  401a2e:	66 90                	xchg   %ax,%ax
  401a30:	31 c0                	xor    %eax,%eax
  401a32:	c3                   	ret
  401a33:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401a3e:	66 90                	xchg   %ax,%ax

0000000000401a40 <findavailable>:
int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401a40:	49 89 fb             	mov    %rdi,%r11
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a43:	48 8b bf c0 00 00 00 	mov    0xc0(%rdi),%rdi
      if (*availableidx == 0) {
  401a4a:	44 8b 02             	mov    (%rdx),%r8d
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a4d:	48 83 c7 01          	add    $0x1,%rdi
  401a51:	48 85 ff             	test   %rdi,%rdi
  401a54:	7e 66                	jle    401abc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401a56:	4d 8b 93 a8 00 00 00 	mov    0xa8(%r11),%r10
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401a5d:	31 c9                	xor    %ecx,%ecx
  401a5f:	45 31 c9             	xor    %r9d,%r9d
  401a62:	31 c0                	xor    %eax,%eax
  401a64:	eb 18                	jmp    401a7e <findavailable+0x3e>
  401a66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401a70:	83 c1 01             	add    $0x1,%ecx
  401a73:	48 63 c1             	movslq %ecx,%rax
  401a76:	49 89 c1             	mov    %rax,%r9
  401a79:	48 39 f8             	cmp    %rdi,%rax
  401a7c:	7d 3e                	jge    401abc <findavailable+0x7c>
        if (data->freelist[x].available == FREE ) {
  401a7e:	48 c1 e0 05          	shl    $0x5,%rax
  401a82:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401a88:	75 e6                	jne    401a70 <findavailable+0x30>
         available[*availableidx] = x;
  401a8a:	49 63 c0             	movslq %r8d,%rax
         (*availableidx)++;
  401a8d:	41 83 c0 01          	add    $0x1,%r8d
         available[*availableidx] = x;
  401a91:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
         (*availableidx)++;
  401a95:	44 89 02             	mov    %r8d,(%rdx)
         if ((*availableidx) == data->threadsize * 2) {
  401a98:	41 8b 43 70          	mov    0x70(%r11),%eax
  401a9c:	01 c0                	add    %eax,%eax
  401a9e:	41 39 c0             	cmp    %eax,%r8d
  401aa1:	74 19                	je     401abc <findavailable+0x7c>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401aa3:	49 8b bb c0 00 00 00 	mov    0xc0(%r11),%rdi
  401aaa:	83 c1 01             	add    $0x1,%ecx
  401aad:	48 63 c1             	movslq %ecx,%rax
  401ab0:	48 83 c7 01          	add    $0x1,%rdi
  401ab4:	49 89 c1             	mov    %rax,%r9
  401ab7:	48 39 f8             	cmp    %rdi,%rax
  401aba:	7c c2                	jl     401a7e <findavailable+0x3e>
      if (*availableidx == 0) {
  401abc:	31 c0                	xor    %eax,%eax
  401abe:	45 85 c0             	test   %r8d,%r8d
  401ac1:	0f 94 c0             	sete   %al
}
  401ac4:	c3                   	ret
  401ac5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401ad0 <singlewriter2>:
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401ad0:	41 54                	push   %r12
  401ad2:	55                   	push   %rbp
  401ad3:	53                   	push   %rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401ad4:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401ada:	48 89 fb             	mov    %rdi,%rbx
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401add:	85 c0                	test   %eax,%eax
  401adf:	74 0d                	je     401aee <singlewriter2+0x1e>
  401ae1:	8b 77 70             	mov    0x70(%rdi),%esi
  401ae4:	99                   	cltd
  401ae5:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401ae8:	f7 f9                	idiv   %ecx
  401aea:	85 d2                	test   %edx,%edx
  401aec:	74 32                	je     401b20 <singlewriter2+0x50>
  if (data->writecursor != 0 && (data->writecursor % (data->threadsize - 1)) == 0) {
  401aee:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
  401af4:	85 c0                	test   %eax,%eax
  401af6:	74 1f                	je     401b17 <singlewriter2+0x47>
  401af8:	8b 73 70             	mov    0x70(%rbx),%esi
  401afb:	99                   	cltd
  401afc:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401aff:	f7 f9                	idiv   %ecx
  401b01:	85 d2                	test   %edx,%edx
  401b03:	75 12                	jne    401b17 <singlewriter2+0x47>
    data->currentwrite++;
  401b05:	48 83 83 00 03 00 00 01 	addq   $0x1,0x300(%rbx)
    data->writecursor = 0;
  401b0d:	c7 83 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rbx)
}
  401b17:	5b                   	pop    %rbx
  401b18:	5d                   	pop    %rbp
  401b19:	41 5c                	pop    %r12
  401b1b:	c3                   	ret
  401b1c:	0f 1f 40 00          	nopl   0x0(%rax)
        struct Data * thread = &data->threads[data->threadindex];
  401b20:	48 63 47 6c          	movslq 0x6c(%rdi),%rax
    data->currentread++;
  401b24:	48 83 87 80 02 00 00 01 	addq   $0x1,0x280(%rdi)
    data->readcursor = 0;
  401b2c:	c7 87 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdi)
        struct Data * thread = &data->threads[data->threadindex];
  401b36:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  401b3e:	48 29 c5             	sub    %rax,%rbp
  401b41:	48 c1 e5 07          	shl    $0x7,%rbp
  401b45:	48 03 6f 30          	add    0x30(%rdi),%rbp
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401b49:	bf 04 00 00 00       	mov    $0x4,%edi
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401b4e:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401b55:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401b59:	49 c1 e4 04          	shl    $0x4,%r12
  401b5d:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401b64:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401b69:	e8 f2 f4 ff ff       	call   401060 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401b6e:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401b74:	83 c0 01             	add    $0x1,%eax
  401b77:	99                   	cltd
  401b78:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
        epoch->thread = data->threadindex;
  401b7e:	8b 43 6c             	mov    0x6c(%rbx),%eax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401b81:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
        epoch->thread = data->threadindex;
  401b87:	41 89 04 24          	mov    %eax,(%r12)
        epoch->kind = NEW_EPOCH;
  401b8b:	48 8b 05 3e 16 00 00 	mov    0x163e(%rip),%rax        # 4031d0 <_IO_stdin_used+0x1d0>
  401b92:	49 89 44 24 20       	mov    %rax,0x20(%r12)
  401b97:	e9 52 ff ff ff       	jmp    401aee <singlewriter2+0x1e>
  401b9c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401ba0 <singlewriter>:
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401ba0:	41 55                	push   %r13
  401ba2:	49 89 d5             	mov    %rdx,%r13
  401ba5:	41 54                	push   %r12
  401ba7:	49 89 cc             	mov    %rcx,%r12
  401baa:	55                   	push   %rbp
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401bab:	4d 89 e0             	mov    %r12,%r8
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401bae:	48 89 fd             	mov    %rdi,%rbp
  401bb1:	53                   	push   %rbx
  401bb2:	48 89 f3             	mov    %rsi,%rbx
  401bb5:	48 83 ec 28          	sub    $0x28,%rsp
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401bb9:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401bbd:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401bc6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401bcb:	31 c0                	xor    %eax,%eax
  int readers = 0;
  401bcd:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401bd5:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  int writers = 0;
  401bdb:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  int availableidx = 0;
  401be3:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401beb:	83 c0 01             	add    $0x1,%eax
  401bee:	99                   	cltd
  401bef:	f7 7f 70             	idivl  0x70(%rdi)
  401bf2:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  401bf8:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401bfd:	4c 89 e9             	mov    %r13,%rcx
  401c00:	e8 3b fe ff ff       	call   401a40 <findavailable>
  if (fill == 1) {
  401c05:	83 f8 01             	cmp    $0x1,%eax
  401c08:	0f 84 64 01 00 00    	je     401d72 <singlewriter+0x1d2>
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401c0e:	48 89 ef             	mov    %rbp,%rdi
  401c11:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401c16:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401c1b:	4c 89 e2             	mov    %r12,%rdx
  401c1e:	4c 89 ee             	mov    %r13,%rsi
  401c21:	e8 8a fd ff ff       	call   4019b0 <pollthreads>
        for (int x = 0; x < readers ; x++) {
  401c26:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401c2b:	85 ff                	test   %edi,%edi
  401c2d:	0f 8e 66 01 00 00    	jle    401d99 <singlewriter+0x1f9>
  401c33:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
          if (assignedchunk == availableidx) {
  401c38:	31 c9                	xor    %ecx,%ecx
  401c3a:	eb 62                	jmp    401c9e <singlewriter+0xfe>
  401c3c:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c40:	48 8b 14 cb          	mov    (%rbx,%rcx,8),%rdx
          int thread = readyreaders[x];
  401c44:	4d 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%r10
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c49:	8d 71 01             	lea    0x1(%rcx),%esi
        for (int x = 0; x < readers ; x++) {
  401c4c:	48 83 c1 01          	add    $0x1,%rcx
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401c50:	48 c1 e2 05          	shl    $0x5,%rdx
  401c54:	48 03 95 a8 00 00 00 	add    0xa8(%rbp),%rdx
          data->threads[thread].reading = chunk;
  401c5b:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
          data->threads[thread].start = start;
  401c63:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401c67:	66 0f 6e 4a 08       	movd   0x8(%rdx),%xmm1
          data->threads[thread].reading = chunk;
  401c6c:	4c 29 d0             	sub    %r10,%rax
          chunk->available = READING;
  401c6f:	c7 42 10 02 00 00 00 	movl   $0x2,0x10(%rdx)
          data->threads[thread].reading = chunk;
  401c76:	48 c1 e0 07          	shl    $0x7,%rax
  401c7a:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].start = start;
  401c7e:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          data->threads[thread].reading = chunk;
  401c82:	48 89 90 b0 00 00 00 	mov    %rdx,0xb0(%rax)
          chunk->owner = thread;
  401c89:	44 89 52 14          	mov    %r10d,0x14(%rdx)
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401c8d:	83 88 d0 00 00 00 10 	orl    $0x10,0xd0(%rax)
          data->threads[thread].start = start;
  401c94:	66 0f d6 40 14       	movq   %xmm0,0x14(%rax)
        for (int x = 0; x < readers ; x++) {
  401c99:	48 39 cf             	cmp    %rcx,%rdi
  401c9c:	74 07                	je     401ca5 <singlewriter+0x105>
  401c9e:	89 ce                	mov    %ecx,%esi
          if (assignedchunk == availableidx) {
  401ca0:	4c 39 c1             	cmp    %r8,%rcx
  401ca3:	75 9b                	jne    401c40 <singlewriter+0xa0>
   for (int x = 0; x < writers ; x++) {
  401ca5:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401caa:	45 85 c0             	test   %r8d,%r8d
  401cad:	7e 7a                	jle    401d29 <singlewriter+0x189>
                if (assignedchunk  == availableidx) {
  401caf:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401cb3:	41 01 f0             	add    %esi,%r8d
  401cb6:	eb 6d                	jmp    401d25 <singlewriter+0x185>
  401cb8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401cc0:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401cc3:	48 63 f6             	movslq %esi,%rsi
          int thread = readywriters[x];
  401cc6:	45 8b 0c 24          	mov    (%r12),%r9d
   for (int x = 0; x < writers ; x++) {
  401cca:	49 83 c4 04          	add    $0x4,%r12
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401cce:	48 8b 14 f3          	mov    (%rbx,%rsi,8),%rdx
          data->threads[thread].writing = chunk;
  401cd2:	49 63 f1             	movslq %r9d,%rsi
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401cd5:	48 c1 e2 05          	shl    $0x5,%rdx
  401cd9:	48 03 95 a8 00 00 00 	add    0xa8(%rbp),%rdx
          data->threads[thread].writing = chunk;
  401ce0:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
          data->threads[thread].publishstart = start;
  401ce8:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401cec:	66 0f 6e 52 08       	movd   0x8(%rdx),%xmm2
          data->threads[thread].writing = chunk;
  401cf1:	48 29 f0             	sub    %rsi,%rax
      chunk->available = WRITING;
  401cf4:	c7 42 10 03 00 00 00 	movl   $0x3,0x10(%rdx)
          data->threads[thread].writing = chunk;
  401cfb:	48 c1 e0 07          	shl    $0x7,%rax
  401cff:	48 03 45 30          	add    0x30(%rbp),%rax
          data->threads[thread].publishstart = start;
  401d03:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
          data->threads[thread].writing = chunk;
  401d07:	48 89 90 b8 00 00 00 	mov    %rdx,0xb8(%rax)
          chunk->owner = thread;
  401d0e:	44 89 4a 14          	mov    %r9d,0x14(%rdx)
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401d12:	83 88 d0 00 00 00 20 	orl    $0x20,0xd0(%rax)
          data->threads[thread].publishstart = start;
  401d19:	66 0f d6 40 40       	movq   %xmm0,0x40(%rax)
   for (int x = 0; x < writers ; x++) {
  401d1e:	44 39 c1             	cmp    %r8d,%ecx
  401d21:	74 06                	je     401d29 <singlewriter+0x189>
  401d23:	89 ce                	mov    %ecx,%esi
                if (assignedchunk  == availableidx) {
  401d25:	39 f7                	cmp    %esi,%edi
  401d27:	75 97                	jne    401cc0 <singlewriter+0x120>
      for (int x = 0; x < data->threadsize ; x++) {
  401d29:	8b 7d 70             	mov    0x70(%rbp),%edi
  401d2c:	85 ff                	test   %edi,%edi
  401d2e:	7e 40                	jle    401d70 <singlewriter+0x1d0>
        if (data->threads[x].newmask != 0) {
  401d30:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401d34:	31 d2                	xor    %edx,%edx
  401d36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401d40:	48 63 ca             	movslq %edx,%rcx
  401d43:	48 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rax
  401d4b:	48 29 c8             	sub    %rcx,%rax
  401d4e:	48 c1 e0 07          	shl    $0x7,%rax
  401d52:	4c 01 c0             	add    %r8,%rax
  401d55:	8b b0 d0 00 00 00    	mov    0xd0(%rax),%esi
  401d5b:	85 f6                	test   %esi,%esi
  401d5d:	74 31                	je     401d90 <singlewriter+0x1f0>
          data->threads[x].readies[x] = data->threads[x].newmask;
  401d5f:	48 8b 40 20          	mov    0x20(%rax),%rax
      for (int x = 0; x < data->threadsize ; x++) {
  401d63:	83 c2 01             	add    $0x1,%edx
          data->threads[x].readies[x] = data->threads[x].newmask;
  401d66:	89 34 88             	mov    %esi,(%rax,%rcx,4)
      for (int x = 0; x < data->threadsize ; x++) {
  401d69:	8b 7d 70             	mov    0x70(%rbp),%edi
  401d6c:	39 fa                	cmp    %edi,%edx
  401d6e:	7c d0                	jl     401d40 <singlewriter+0x1a0>
  return 0;
  401d70:	31 c0                	xor    %eax,%eax
}
  401d72:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401d77:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401d80:	75 1e                	jne    401da0 <singlewriter+0x200>
  401d82:	48 83 c4 28          	add    $0x28,%rsp
  401d86:	5b                   	pop    %rbx
  401d87:	5d                   	pop    %rbp
  401d88:	41 5c                	pop    %r12
  401d8a:	41 5d                	pop    %r13
  401d8c:	c3                   	ret
  401d8d:	0f 1f 00             	nopl   (%rax)
      for (int x = 0; x < data->threadsize ; x++) {
  401d90:	83 c2 01             	add    $0x1,%edx
  401d93:	39 fa                	cmp    %edi,%edx
  401d95:	7c a9                	jl     401d40 <singlewriter+0x1a0>
  401d97:	eb d7                	jmp    401d70 <singlewriter+0x1d0>
      int assignedchunk = 0;
  401d99:	31 f6                	xor    %esi,%esi
  401d9b:	e9 05 ff ff ff       	jmp    401ca5 <singlewriter+0x105>
}
  401da0:	e8 cb f2 ff ff       	call   401070 <__stack_chk_fail@plt>
  401da5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401db0 <threadwork>:
int * threadwork(struct Data * data) {
  401db0:	41 54                	push   %r12
  401db2:	55                   	push   %rbp
  401db3:	48 89 fd             	mov    %rdi,%rbp
  401db6:	53                   	push   %rbx
  401db7:	48 83 ec 20          	sub    $0x20,%rsp
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401dbb:	48 63 4f 70          	movslq 0x70(%rdi),%rcx
  401dbf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401dc8:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401dcd:	48 8b 47 28          	mov    0x28(%rdi),%rax
  long lastcursor = data->main->writecursor;
  401dd1:	8b b0 80 01 00 00    	mov    0x180(%rax),%esi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401dd7:	48 8b 80 38 03 00 00 	mov    0x338(%rax),%rax
  401dde:	48 99                	cqto
    data->thiswrite = lastcursor;
  401de0:	89 b7 28 03 00 00    	mov    %esi,0x328(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401de6:	48 89 e6             	mov    %rsp,%rsi
  long lastwrite = data->main->totalwrites % (data->threadsize);
  401de9:	48 f7 f9             	idiv   %rcx
    data->prevwrite = lastwrite;
  401dec:	48 89 97 10 03 00 00 	mov    %rdx,0x310(%rdi)
   clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401df3:	bf 04 00 00 00       	mov    $0x4,%edi
  401df8:	e8 63 f2 ff ff       	call   401060 <clock_gettime@plt>
     for (int x = 1; x < data->threadsize ; x++) {
  401dfd:	8b 45 70             	mov    0x70(%rbp),%eax
   data->freq_writes++;
  401e00:	48 83 45 50 01       	addq   $0x1,0x50(%rbp)
     for (int x = 1; x < data->threadsize ; x++) {
  401e05:	b9 01 00 00 00       	mov    $0x1,%ecx
  401e0a:	83 f8 01             	cmp    $0x1,%eax
  401e0d:	0f 8f fe 00 00 00    	jg     401f11 <threadwork+0x161>
  401e13:	e9 0b 01 00 00       	jmp    401f23 <threadwork+0x173>
  401e18:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401e20:	48 63 85 80 01 00 00 	movslq 0x180(%rbp),%rax
  401e27:	48 8b 7d 28          	mov    0x28(%rbp),%rdi
        epoch->time = time;
  401e2b:	66 0f 6f 04 24       	movdqa (%rsp),%xmm0
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401e30:	48 89 c2             	mov    %rax,%rdx
  401e33:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401e3a:	41 89 d0             	mov    %edx,%r8d
  401e3d:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401e41:	48 c1 e8 20          	shr    $0x20,%rax
  401e45:	01 d0                	add    %edx,%eax
  401e47:	c1 f8 03             	sar    $0x3,%eax
  401e4a:	44 29 c0             	sub    %r8d,%eax
  401e4d:	41 89 c0             	mov    %eax,%r8d
  401e50:	41 c1 e0 04          	shl    $0x4,%r8d
  401e54:	41 29 c0             	sub    %eax,%r8d
  401e57:	89 f0                	mov    %esi,%eax
  401e59:	44 29 c2             	sub    %r8d,%edx
  401e5c:	c1 e0 18             	shl    $0x18,%eax
  401e5f:	09 c2                	or     %eax,%edx
  401e61:	48 63 87 80 01 00 00 	movslq 0x180(%rdi),%rax
  401e68:	41 89 d2             	mov    %edx,%r10d
  401e6b:	48 89 c2             	mov    %rax,%rdx
  401e6e:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401e75:	41 89 d0             	mov    %edx,%r8d
  401e78:	41 c1 f8 1f          	sar    $0x1f,%r8d
  401e7c:	48 c1 e8 20          	shr    $0x20,%rax
  401e80:	01 d0                	add    %edx,%eax
  401e82:	c1 f8 03             	sar    $0x3,%eax
  401e85:	44 29 c0             	sub    %r8d,%eax
  401e88:	41 89 c0             	mov    %eax,%r8d
  401e8b:	41 c1 e0 04          	shl    $0x4,%r8d
  401e8f:	41 29 c0             	sub    %eax,%r8d
  401e92:	89 c8                	mov    %ecx,%eax
  401e94:	44 29 c2             	sub    %r8d,%edx
  401e97:	c1 e0 08             	shl    $0x8,%eax
  401e9a:	c1 e2 10             	shl    $0x10,%edx
  401e9d:	41 09 d2             	or     %edx,%r10d
  401ea0:	41 09 c2             	or     %eax,%r10d
        struct Data * thread = &data->threads[data->threadindex];
  401ea3:	48 63 c6             	movslq %esi,%rax
  401ea6:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401eae:	4d 63 d2             	movslq %r10d,%r10
        struct Data * thread = &data->threads[data->threadindex];
  401eb1:	49 29 c0             	sub    %rax,%r8
  401eb4:	49 c1 e0 07          	shl    $0x7,%r8
  401eb8:	4c 03 45 30          	add    0x30(%rbp),%r8
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401ebc:	49 63 90 24 03 00 00 	movslq 0x324(%r8),%rdx
  401ec3:	48 89 d0             	mov    %rdx,%rax
  401ec6:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401eca:	83 c0 01             	add    $0x1,%eax
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  401ecd:	49 c1 e1 04          	shl    $0x4,%r9
  401ed1:	4d 03 88 18 03 00 00 	add    0x318(%r8),%r9
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ed8:	99                   	cltd
        epoch->time = time;
  401ed9:	41 0f 11 41 08       	movups %xmm0,0x8(%r9)
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ede:	41 f7 b8 20 03 00 00 	idivl  0x320(%r8)
  data->main->works[buffer] = data->threadindex;
  401ee5:	48 8b 47 78          	mov    0x78(%rdi),%rax
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401ee9:	41 89 90 24 03 00 00 	mov    %edx,0x324(%r8)
  epoch->dest = x;
  401ef0:	41 89 49 28          	mov    %ecx,0x28(%r9)
     for (int x = 1; x < data->threadsize ; x++) {
  401ef4:	83 c1 01             	add    $0x1,%ecx
        epoch->thread = data->threadindex;
  401ef7:	41 89 31             	mov    %esi,(%r9)
        long buffer = (data->threadindex << 24) | (data->main->writecursor % 0xf) << 16 | (x << 8) | (data->writecursor % 0xf);
  401efa:	4d 89 51 18          	mov    %r10,0x18(%r9)
  epoch->set = 1;
  401efe:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
  data->main->works[buffer] = data->threadindex;
  401f06:	42 88 34 10          	mov    %sil,(%rax,%r10,1)
     for (int x = 1; x < data->threadsize ; x++) {
  401f0a:	8b 45 70             	mov    0x70(%rbp),%eax
  401f0d:	39 c1                	cmp    %eax,%ecx
  401f0f:	7d 12                	jge    401f23 <threadwork+0x173>
  401f11:	8b 75 6c             	mov    0x6c(%rbp),%esi
     if (x != data->threadindex) {
  401f14:	39 ce                	cmp    %ecx,%esi
  401f16:	0f 85 04 ff ff ff    	jne    401e20 <threadwork+0x70>
     for (int x = 1; x < data->threadsize ; x++) {
  401f1c:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401f1f:	39 c1                	cmp    %eax,%ecx
  401f21:	7c f1                	jl     401f14 <threadwork+0x164>
    data->writecursor = (data->writecursor + 1) % 0xf;
  401f23:	8b 85 80 01 00 00    	mov    0x180(%rbp),%eax
  401f29:	8d 50 01             	lea    0x1(%rax),%edx
  401f2c:	48 63 c2             	movslq %edx,%rax
  401f2f:	89 d1                	mov    %edx,%ecx
  401f31:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401f38:	c1 f9 1f             	sar    $0x1f,%ecx
  401f3b:	48 c1 e8 20          	shr    $0x20,%rax
  401f3f:	01 d0                	add    %edx,%eax
  401f41:	c1 f8 03             	sar    $0x3,%eax
  401f44:	29 c8                	sub    %ecx,%eax
  401f46:	89 c1                	mov    %eax,%ecx
  401f48:	c1 e1 04             	shl    $0x4,%ecx
  401f4b:	29 c1                	sub    %eax,%ecx
    __atomic_fetch_add(&data->main->writecursor, 1, __ATOMIC_ACQUIRE);
  401f4d:	48 8b 45 28          	mov    0x28(%rbp),%rax
    data->writecursor = (data->writecursor + 1) % 0xf;
  401f51:	29 ca                	sub    %ecx,%edx
  401f53:	89 95 80 01 00 00    	mov    %edx,0x180(%rbp)
    __atomic_fetch_add(&data->main->writecursor, 1, __ATOMIC_ACQUIRE);
  401f59:	f0 83 80 80 01 00 00 01 	lock addl $0x1,0x180(%rax)
  for (int y = 1 ; y < data->threadsize; y++) {
  401f61:	41 bc 01 00 00 00    	mov    $0x1,%r12d
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  401f67:	48 8d 1d 96 10 00 00 	lea    0x1096(%rip),%rbx        # 403004 <_IO_stdin_used+0x4>
  long lastread = data->main->totalreads % data->threadsize;
  401f6e:	48 8b 75 28          	mov    0x28(%rbp),%rsi
  401f72:	48 63 7d 70          	movslq 0x70(%rbp),%rdi
  401f76:	48 8b 86 40 03 00 00 	mov    0x340(%rsi),%rax
  401f7d:	48 89 f9             	mov    %rdi,%rcx
   data->freq++;
  401f80:	48 83 45 48 01       	addq   $0x1,0x48(%rbp)
  long lastread = data->main->totalreads % data->threadsize;
  401f85:	48 99                	cqto
  401f87:	48 f7 ff             	idiv   %rdi
   data->prevread = lastread;
  401f8a:	48 89 95 08 03 00 00 	mov    %rdx,0x308(%rbp)
  for (int y = 1 ; y < data->threadsize; y++) {
  401f91:	83 ff 01             	cmp    $0x1,%edi
  401f94:	0f 8e 36 01 00 00    	jle    4020d0 <threadwork+0x320>
  401f9a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (y != data->threadindex) {
  401fa0:	44 8b 45 6c          	mov    0x6c(%rbp),%r8d
  401fa4:	45 39 e0             	cmp    %r12d,%r8d
  401fa7:	0f 84 16 01 00 00    	je     4020c3 <threadwork+0x313>
            long past = ((data->main->writecursor - 1) % 0xf);
  401fad:	8b 86 80 01 00 00    	mov    0x180(%rsi),%eax
              past = data->threadsize - 1;
  401fb3:	83 e9 01             	sub    $0x1,%ecx
            int rc = data->threads[x].writecursor;
  401fb6:	4c 8b 4d 30          	mov    0x30(%rbp),%r9
            long past = ((data->main->writecursor - 1) % 0xf);
  401fba:	8d 50 ff             	lea    -0x1(%rax),%edx
  401fbd:	48 63 c2             	movslq %edx,%rax
  401fc0:	89 d7                	mov    %edx,%edi
  401fc2:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  401fc9:	c1 ff 1f             	sar    $0x1f,%edi
  401fcc:	48 c1 e8 20          	shr    $0x20,%rax
  401fd0:	01 d0                	add    %edx,%eax
  401fd2:	c1 f8 03             	sar    $0x3,%eax
  401fd5:	29 f8                	sub    %edi,%eax
  401fd7:	89 c7                	mov    %eax,%edi
  401fd9:	c1 e7 04             	shl    $0x4,%edi
  401fdc:	29 c7                	sub    %eax,%edi
              past = data->threadsize - 1;
  401fde:	89 d0                	mov    %edx,%eax
  401fe0:	29 f8                	sub    %edi,%eax
  401fe2:	0f 48 c1             	cmovs  %ecx,%eax
            int rc = data->threads[x].writecursor;
  401fe5:	49 63 cc             	movslq %r12d,%rcx
  401fe8:	48 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rdx
  401ff0:	48 29 ca             	sub    %rcx,%rdx
  401ff3:	48 98                	cltq
  401ff5:	48 c1 e2 07          	shl    $0x7,%rdx
  401ff9:	41 8b 8c 11 80 01 00 00 	mov    0x180(%r9,%rdx,1),%ecx
            if (rc < 0) {
  402001:	ba 0e 00 00 00       	mov    $0xe,%edx
  402006:	85 c9                	test   %ecx,%ecx
  402008:	78 26                	js     402030 <threadwork+0x280>
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40200a:	48 63 d1             	movslq %ecx,%rdx
  40200d:	89 cf                	mov    %ecx,%edi
  40200f:	48 69 d2 89 88 88 88 	imul   $0xffffffff88888889,%rdx,%rdx
  402016:	c1 ff 1f             	sar    $0x1f,%edi
  402019:	48 c1 ea 20          	shr    $0x20,%rdx
  40201d:	01 ca                	add    %ecx,%edx
  40201f:	c1 fa 03             	sar    $0x3,%edx
  402022:	29 fa                	sub    %edi,%edx
  402024:	89 d7                	mov    %edx,%edi
  402026:	c1 e7 04             	shl    $0x4,%edi
  402029:	29 d7                	sub    %edx,%edi
  40202b:	29 f9                	sub    %edi,%ecx
  40202d:	48 63 d1             	movslq %ecx,%rdx
  402030:	44 89 c1             	mov    %r8d,%ecx
  402033:	44 89 e7             	mov    %r12d,%edi
  402036:	48 c1 e0 10          	shl    $0x10,%rax
            thepoch->time = time; 
  40203a:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  40203f:	c1 e1 08             	shl    $0x8,%ecx
  402042:	c1 e7 18             	shl    $0x18,%edi
  402045:	09 cf                	or     %ecx,%edi
  402047:	48 63 ff             	movslq %edi,%rdi
  40204a:	48 09 c7             	or     %rax,%rdi
                struct Data * thread = &data->threads[data->threadindex];
  40204d:	49 63 c0             	movslq %r8d,%rax
  402050:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
         long buffer = (x << 24) | (past << 16) | (data->threadindex << 8) | (rc) % 0xf;
  402058:	48 09 d7             	or     %rdx,%rdi
                struct Data * thread = &data->threads[data->threadindex];
  40205b:	48 29 c1             	sub    %rax,%rcx
  40205e:	48 c1 e1 07          	shl    $0x7,%rcx
  402062:	4c 01 c9             	add    %r9,%rcx
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402065:	48 63 91 24 03 00 00 	movslq 0x324(%rcx),%rdx
  40206c:	48 89 d0             	mov    %rdx,%rax
  40206f:	4c 8d 0c 52          	lea    (%rdx,%rdx,2),%r9
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402073:	83 c0 01             	add    $0x1,%eax
                struct Epoch * thepoch = &thread->epochs[thread->currentepoch];
  402076:	49 c1 e1 04          	shl    $0x4,%r9
  40207a:	4c 03 89 18 03 00 00 	add    0x318(%rcx),%r9
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402081:	99                   	cltd
            thepoch->time = time; 
  402082:	41 0f 11 49 08       	movups %xmm1,0x8(%r9)
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402087:	f7 b9 20 03 00 00    	idivl  0x320(%rcx)
          printf("%d received %d\n", data->threadindex, data->main->works[buffer]);
  40208d:	48 8b 46 78          	mov    0x78(%rsi),%rax
  402091:	48 89 de             	mov    %rbx,%rsi
          thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  402094:	89 91 24 03 00 00    	mov    %edx,0x324(%rcx)
  40209a:	44 89 c2             	mov    %r8d,%edx
          thepoch->buffer = buffer;
  40209d:	49 89 79 18          	mov    %rdi,0x18(%r9)
                thepoch->thread = x;
  4020a1:	45 89 21             	mov    %r12d,(%r9)
          thepoch->set = 1;
  4020a4:	41 c7 41 24 01 00 00 00 	movl   $0x1,0x24(%r9)
          printf("%d received %d\n", data->threadindex, data->main->works[buffer]);
  4020ac:	0f be 0c 38          	movsbl (%rax,%rdi,1),%ecx
  4020b0:	31 c0                	xor    %eax,%eax
  4020b2:	bf 01 00 00 00       	mov    $0x1,%edi
  4020b7:	e8 f4 ef ff ff       	call   4010b0 <__printf_chk@plt>
  for (int y = 1 ; y < data->threadsize; y++) {
  4020bc:	8b 4d 70             	mov    0x70(%rbp),%ecx
    __atomic_fetch_add(&data->main->readcursor, 1, __ATOMIC_ACQUIRE);
  4020bf:	48 8b 75 28          	mov    0x28(%rbp),%rsi
  for (int y = 1 ; y < data->threadsize; y++) {
  4020c3:	41 83 c4 01          	add    $0x1,%r12d
  4020c7:	41 39 cc             	cmp    %ecx,%r12d
  4020ca:	0f 8c d0 fe ff ff    	jl     401fa0 <threadwork+0x1f0>
     data->readcursor = (data->readcursor + 1) % 0xf;
  4020d0:	8b 85 00 02 00 00    	mov    0x200(%rbp),%eax
  4020d6:	8d 50 01             	lea    0x1(%rax),%edx
  4020d9:	48 63 c2             	movslq %edx,%rax
  4020dc:	89 d1                	mov    %edx,%ecx
  4020de:	48 69 c0 89 88 88 88 	imul   $0xffffffff88888889,%rax,%rax
  4020e5:	c1 f9 1f             	sar    $0x1f,%ecx
  4020e8:	48 c1 e8 20          	shr    $0x20,%rax
  4020ec:	01 d0                	add    %edx,%eax
  4020ee:	c1 f8 03             	sar    $0x3,%eax
  4020f1:	29 c8                	sub    %ecx,%eax
  4020f3:	89 c1                	mov    %eax,%ecx
  4020f5:	c1 e1 04             	shl    $0x4,%ecx
  4020f8:	29 c1                	sub    %eax,%ecx
  4020fa:	29 ca                	sub    %ecx,%edx
  4020fc:	89 95 00 02 00 00    	mov    %edx,0x200(%rbp)
    __atomic_fetch_add(&data->main->readcursor, 1, __ATOMIC_ACQUIRE);
  402102:	f0 83 86 00 02 00 00 01 	lock addl $0x1,0x200(%rsi)
}
  40210a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  40210f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  402118:	75 0b                	jne    402125 <threadwork+0x375>
  40211a:	48 83 c4 20          	add    $0x20,%rsp
  40211e:	31 c0                	xor    %eax,%eax
  402120:	5b                   	pop    %rbx
  402121:	5d                   	pop    %rbp
  402122:	41 5c                	pop    %r12
  402124:	c3                   	ret
  402125:	e8 46 ef ff ff       	call   401070 <__stack_chk_fail@plt>
  40212a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000402130 <work>:
void * work(void * arg) {
  402130:	41 56                	push   %r14
  402132:	48 8d 35 db 0e 00 00 	lea    0xedb(%rip),%rsi        # 403014 <_IO_stdin_used+0x14>
  402139:	31 c0                	xor    %eax,%eax
  40213b:	41 55                	push   %r13
  40213d:	41 54                	push   %r12
  40213f:	55                   	push   %rbp
  402140:	53                   	push   %rbx
  402141:	8b 57 6c             	mov    0x6c(%rdi),%edx
  402144:	48 89 fb             	mov    %rdi,%rbx
  402147:	bf 01 00 00 00       	mov    $0x1,%edi
  40214c:	e8 5f ef ff ff       	call   4010b0 <__printf_chk@plt>
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  402151:	8b 43 6c             	mov    0x6c(%rbx),%eax
  402154:	48 8d 35 cc 0e 00 00 	lea    0xecc(%rip),%rsi        # 403027 <_IO_stdin_used+0x27>
  40215b:	bf 01 00 00 00       	mov    $0x1,%edi
  int bucketstart = data->bucketstart;
  402160:	44 8b b3 a0 00 00 00 	mov    0xa0(%rbx),%r14d
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  402167:	8d 50 01             	lea    0x1(%rax),%edx
  40216a:	31 c0                	xor    %eax,%eax
  int bucketlim = ((data->threadindex + 1) * data->buckets) ;
  40216c:	0f af 93 98 00 00 00 	imul   0x98(%rbx),%edx
  402173:	e8 38 ef ff ff       	call   4010b0 <__printf_chk@plt>
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  402178:	48 8b 83 c0 00 00 00 	mov    0xc0(%rbx),%rax
  40217f:	be 08 00 00 00       	mov    $0x8,%esi
  402184:	48 8d 78 01          	lea    0x1(%rax),%rdi
  402188:	e8 13 ef ff ff       	call   4010a0 <calloc@plt>
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  40218d:	4c 63 6b 70          	movslq 0x70(%rbx),%r13
  402191:	be 04 00 00 00       	mov    $0x4,%esi
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  402196:	48 89 c5             	mov    %rax,%rbp
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  402199:	4c 89 ef             	mov    %r13,%rdi
  40219c:	e8 ff ee ff ff       	call   4010a0 <calloc@plt>
  int * readywriters = calloc(data->threadsize, sizeof(int));
  4021a1:	be 04 00 00 00       	mov    $0x4,%esi
  4021a6:	4c 89 ef             	mov    %r13,%rdi
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  4021a9:	49 89 c4             	mov    %rax,%r12
  int * readywriters = calloc(data->threadsize, sizeof(int));
  4021ac:	e8 ef ee ff ff       	call   4010a0 <calloc@plt>
  while (data->running == 1) {
  4021b1:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  data->workindex = bucketstart;
  4021b5:	44 89 73 5c          	mov    %r14d,0x5c(%rbx)
  while (data->running == 1) {
  4021b9:	75 49                	jne    402204 <work+0xd4>
  4021bb:	49 89 c5             	mov    %rax,%r13
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  4021be:	4c 8d b3 30 01 00 00 	lea    0x130(%rbx),%r14
  4021c5:	0f 1f 00             	nopl   (%rax)
    if (data->threadindex == 0) {
  4021c8:	8b 43 6c             	mov    0x6c(%rbx),%eax
  4021cb:	85 c0                	test   %eax,%eax
  4021cd:	75 59                	jne    402228 <work+0xf8>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
  4021cf:	4c 89 f6             	mov    %r14,%rsi
  4021d2:	bf 04 00 00 00       	mov    $0x4,%edi
  4021d7:	e8 84 ee ff ff       	call   401060 <clock_gettime@plt>
      singlewriter2(data, available, readyreaders, readywriters);
  4021dc:	4c 89 e9             	mov    %r13,%rcx
  4021df:	4c 89 e2             	mov    %r12,%rdx
  4021e2:	48 89 ee             	mov    %rbp,%rsi
  4021e5:	48 89 df             	mov    %rbx,%rdi
  4021e8:	e8 e3 f8 ff ff       	call   401ad0 <singlewriter2>
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swend);
  4021ed:	48 8d b3 40 01 00 00 	lea    0x140(%rbx),%rsi
  4021f4:	bf 04 00 00 00       	mov    $0x4,%edi
  4021f9:	e8 62 ee ff ff       	call   401060 <clock_gettime@plt>
  while (data->running == 1) {
  4021fe:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  402202:	74 c4                	je     4021c8 <work+0x98>
  402204:	8b 53 6c             	mov    0x6c(%rbx),%edx
  402207:	48 8d 35 27 0e 00 00 	lea    0xe27(%rip),%rsi        # 403035 <_IO_stdin_used+0x35>
  40220e:	bf 01 00 00 00       	mov    $0x1,%edi
  402213:	31 c0                	xor    %eax,%eax
  402215:	e8 96 ee ff ff       	call   4010b0 <__printf_chk@plt>
}
  40221a:	5b                   	pop    %rbx
  40221b:	5d                   	pop    %rbp
  40221c:	41 5c                	pop    %r12
  40221e:	41 5d                	pop    %r13
  402220:	41 5e                	pop    %r14
  402222:	c3                   	ret
  402223:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      threadwork(data);
  402228:	48 89 df             	mov    %rbx,%rdi
  40222b:	e8 80 fb ff ff       	call   401db0 <threadwork>
  while (data->running == 1) {
  402230:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  402234:	74 92                	je     4021c8 <work+0x98>
  402236:	eb cc                	jmp    402204 <work+0xd4>
  402238:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000402240 <work2>:
  while (data->running == 1) {
  402240:	eb 0b                	jmp    40224d <work2+0xd>
  402242:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->freq++;
  402248:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  while (data->running == 1) {
  40224d:	83 7f 64 01          	cmpl   $0x1,0x64(%rdi)
  402251:	74 f5                	je     402248 <work2+0x8>
}
  402253:	c3                   	ret

Disassembly of section .fini:

0000000000402254 <_fini>:
  402254:	f3 0f 1e fa          	endbr64
  402258:	48 83 ec 08          	sub    $0x8,%rsp
  40225c:	48 83 c4 08          	add    $0x8,%rsp
  402260:	c3                   	ret
