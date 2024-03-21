
threadsafe-workqueue:     file format elf64-x86-64


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

0000000000401020 <__snprintf_chk@plt-0x10>:
  401020:	ff 35 72 2f 00 00    	push   0x2f72(%rip)        # 403f98 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 74 2f 00 00    	jmp    *0x2f74(%rip)        # 403fa0 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <__snprintf_chk@plt>:
  401030:	ff 25 72 2f 00 00    	jmp    *0x2f72(%rip)        # 403fa8 <__snprintf_chk@GLIBC_2.3.4>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <pthread_setaffinity_np@plt>:
  401040:	ff 25 6a 2f 00 00    	jmp    *0x2f6a(%rip)        # 403fb0 <pthread_setaffinity_np@GLIBC_2.34>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <puts@plt>:
  401050:	ff 25 62 2f 00 00    	jmp    *0x2f62(%rip)        # 403fb8 <puts@GLIBC_2.2.5>
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
    
    
    
  }

int main(int argc, char **argv) {
  4010c0:	41 55                	push   %r13
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4010c2:	ba 02 00 00 00       	mov    $0x2,%edx
  4010c7:	bf 01 00 00 00       	mov    $0x1,%edi
  4010cc:	48 8d 35 49 0f 00 00 	lea    0xf49(%rip),%rsi        # 40201c <_IO_stdin_used+0x1c>
  4010d3:	41 54                	push   %r12
  4010d5:	55                   	push   %rbp
  4010d6:	53                   	push   %rbx
  4010d7:	48 83 ec 58          	sub    $0x58,%rsp
  4010db:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4010e4:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  4010e9:	31 c0                	xor    %eax,%eax
  4010eb:	e8 a0 ff ff ff       	call   401090 <__printf_chk@plt>
  int worksize = 10;
  int threadsize = 2;
  printf("Starting %d workers\n", threadsize);
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  4010f0:	be 08 00 00 00       	mov    $0x8,%esi
  4010f5:	bf 02 00 00 00       	mov    $0x2,%edi
  4010fa:	e8 81 ff ff ff       	call   401080 <calloc@plt>
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  4010ff:	be 38 00 00 00       	mov    $0x38,%esi
  401104:	bf 02 00 00 00       	mov    $0x2,%edi
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  401109:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  40110c:	e8 6f ff ff ff       	call   401080 <calloc@plt>
  struct Data *data = calloc(threadsize, sizeof(struct Data));
  401111:	be 50 00 00 00       	mov    $0x50,%esi
  401116:	bf 02 00 00 00       	mov    $0x2,%edi
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  40111b:	49 89 c4             	mov    %rax,%r12
  struct Data *data = calloc(threadsize, sizeof(struct Data));
  40111e:	e8 5d ff ff ff       	call   401080 <calloc@plt>
  struct Work *works = calloc(100, sizeof(struct Work));
  401123:	be 08 00 00 00       	mov    $0x8,%esi
  401128:	bf 64 00 00 00       	mov    $0x64,%edi
  40112d:	66 48 0f 6e c8       	movq   %rax,%xmm1
  struct Data *data = calloc(threadsize, sizeof(struct Data));
  401132:	48 89 c3             	mov    %rax,%rbx
  401135:	66 0f 6c c9          	punpcklqdq %xmm1,%xmm1
  401139:	0f 29 0c 24          	movaps %xmm1,(%rsp)
  struct Work *works = calloc(100, sizeof(struct Work));
  40113d:	e8 3e ff ff ff       	call   401080 <calloc@plt>
  
  for (int i = 0; i < 100; i++) {
  401142:	66 0f 6f 05 96 0f 00 00 	movdqa 0xf96(%rip),%xmm0        # 4020e0 <_IO_stdin_used+0xe0>
  40114a:	48 89 c2             	mov    %rax,%rdx
  40114d:	48 8d 88 20 03 00 00 	lea    0x320(%rax),%rcx
  401154:	0f 1f 40 00          	nopl   0x0(%rax)
    works[i].taskindex = 2;
  401158:	0f 11 02             	movups %xmm0,(%rdx)
  for (int i = 0; i < 100; i++) {
  40115b:	48 83 c2 10          	add    $0x10,%rdx
  40115f:	48 39 ca             	cmp    %rcx,%rdx
  401162:	75 f4                	jne    401158 <main+0x98>
    
  }
  int cpu = 0;
  data[0].works = works;
  for (int x = 0; x < threadsize ; x++) {
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401164:	be 80 00 00 00       	mov    $0x80,%esi
  401169:	bf 01 00 00 00       	mov    $0x1,%edi
  data[0].works = works;
  40116e:	48 89 43 38          	mov    %rax,0x38(%rbx)
  401172:	4c 8d 2d 2f 0f 00 00 	lea    0xf2f(%rip),%r13        # 4020a8 <_IO_stdin_used+0xa8>
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401179:	e8 02 ff ff ff       	call   401080 <calloc@plt>
  40117e:	31 d2                	xor    %edx,%edx
  401180:	b9 02 00 00 00       	mov    $0x2,%ecx
  401185:	4c 89 ee             	mov    %r13,%rsi
    CPU_SET(cpu += 2, data[x].cpu_set);
  401188:	48 83 08 04          	orq    $0x4,(%rax)
  40118c:	bf 01 00 00 00       	mov    $0x1,%edi
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401191:	48 89 43 40          	mov    %rax,0x40(%rbx)
  401195:	31 c0                	xor    %eax,%eax
  401197:	e8 f4 fe ff ff       	call   401090 <__printf_chk@plt>
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].running = 1;
    data[x].threadindex = x;
    data[x].worksize = worksize;
    data[x].threadsize = threadsize;
    data[x].main = &data[0];
  40119c:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4011a1:	be 80 00 00 00       	mov    $0x80,%esi
    data[x].threads = data;
    data[x].wantindex = -1;
  4011a6:	66 0f 6f 05 42 0f 00 00 	movdqa 0xf42(%rip),%xmm0        # 4020f0 <_IO_stdin_used+0xf0>
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4011ae:	bf 01 00 00 00       	mov    $0x1,%edi
    data[x].threadsize = threadsize;
  4011b3:	c7 43 30 02 00 00 00 	movl   $0x2,0x30(%rbx)
    data[x].main = &data[0];
  4011ba:	0f 11 13             	movups %xmm2,(%rbx)
    data[x].wantindex = -1;
  4011bd:	0f 11 43 20          	movups %xmm0,0x20(%rbx)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4011c1:	e8 ba fe ff ff       	call   401080 <calloc@plt>
  4011c6:	4c 89 ee             	mov    %r13,%rsi
  4011c9:	b9 04 00 00 00       	mov    $0x4,%ecx
  4011ce:	ba 01 00 00 00       	mov    $0x1,%edx
    CPU_SET(cpu += 2, data[x].cpu_set);
  4011d3:	48 83 08 10          	orq    $0x10,(%rax)
  4011d7:	bf 01 00 00 00       	mov    $0x1,%edi
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  4011dc:	48 89 83 90 00 00 00 	mov    %rax,0x90(%rbx)
  4011e3:	31 c0                	xor    %eax,%eax
  4011e5:	e8 a6 fe ff ff       	call   401090 <__printf_chk@plt>
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  4011ea:	48 89 d9             	mov    %rbx,%rcx
  4011ed:	4c 89 e6             	mov    %r12,%rsi
  4011f0:	48 89 ef             	mov    %rbp,%rdi
  4011f3:	49 c7 c5 e0 13 40 00 	mov    $0x4013e0,%r13
    data[x].wantindex = -1;
  4011fa:	66 0f 6f 05 fe 0e 00 00 	movdqa 0xefe(%rip),%xmm0        # 402100 <_IO_stdin_used+0x100>
    data[x].main = &data[0];
  401202:	48 89 5b 50          	mov    %rbx,0x50(%rbx)
    data[x].threadsize = threadsize;
  401206:	c7 83 80 00 00 00 02 00 00 00 	movl   $0x2,0x80(%rbx)
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  401210:	4c 89 ea             	mov    %r13,%rdx
    data[x].wantindex = -1;
  401213:	0f 11 43 70          	movups %xmm0,0x70(%rbx)
    data[x].threads = data;
  401217:	48 89 5b 58          	mov    %rbx,0x58(%rbx)
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  40121b:	e8 80 fe ff ff       	call   4010a0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  401220:	48 8b 53 40          	mov    0x40(%rbx),%rdx
  401224:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
  401228:	be 08 00 00 00       	mov    $0x8,%esi
  40122d:	e8 0e fe ff ff       	call   401040 <pthread_setaffinity_np@plt>
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
  401232:	48 8d 4b 50          	lea    0x50(%rbx),%rcx
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  401236:	4c 89 e6             	mov    %r12,%rsi
  401239:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
  40123d:	4c 89 ea             	mov    %r13,%rdx
    data[x].running = 0;
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  401240:	4c 8d 64 24 18       	lea    0x18(%rsp),%r12
    pthread_create(&thread[x], &attr[0], work, &data[x]);
  401245:	e8 56 fe ff ff       	call   4010a0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  40124a:	48 8b 93 90 00 00 00 	mov    0x90(%rbx),%rdx
  401251:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
  401255:	be 08 00 00 00       	mov    $0x8,%esi
  40125a:	e8 e1 fd ff ff       	call   401040 <pthread_setaffinity_np@plt>
  nanosleep(&time, &rem);
  40125f:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
  401264:	48 8d 7c 24 20       	lea    0x20(%rsp),%rdi
  struct timespec time = {
  401269:	66 0f 6f 05 9f 0e 00 00 	movdqa 0xe9f(%rip),%xmm0        # 402110 <_IO_stdin_used+0x110>
  401271:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
  struct timespec rem = {
  401276:	66 0f ef c0          	pxor   %xmm0,%xmm0
  40127a:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  nanosleep(&time, &rem);
  40127f:	e8 ec fd ff ff       	call   401070 <nanosleep@plt>
    pthread_join(thread[x], &res);
  401284:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
  401288:	4c 89 e6             	mov    %r12,%rsi
    data[x].running = 0;
  40128b:	c7 43 24 00 00 00 00 	movl   $0x0,0x24(%rbx)
  401292:	c7 43 74 00 00 00 00 	movl   $0x0,0x74(%rbx)
  401299:	c7 83 c4 00 00 00 00 00 00 00 	movl   $0x0,0xc4(%rbx)
    pthread_join(thread[x], &res);
  4012a3:	e8 08 fe ff ff       	call   4010b0 <pthread_join@plt>
  4012a8:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
  4012ac:	4c 89 e6             	mov    %r12,%rsi
  4012af:	e8 fc fd ff ff       	call   4010b0 <pthread_join@plt>
  4012b4:	48 8d 3d 76 0d 00 00 	lea    0xd76(%rip),%rdi        # 402031 <_IO_stdin_used+0x31>
  4012bb:	e8 90 fd ff ff       	call   401050 <puts@plt>
  }
  printf("finished simulation.\n");
  4012c0:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
  4012c5:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4012ce:	75 0d                	jne    4012dd <main+0x21d>
  4012d0:	48 83 c4 58          	add    $0x58,%rsp
  4012d4:	31 c0                	xor    %eax,%eax
  4012d6:	5b                   	pop    %rbx
  4012d7:	5d                   	pop    %rbp
  4012d8:	41 5c                	pop    %r12
  4012da:	41 5d                	pop    %r13
  4012dc:	c3                   	ret
  4012dd:	e8 7e fd ff ff       	call   401060 <__stack_chk_fail@plt>
  4012e2:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4012ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004012f0 <_start>:
  4012f0:	f3 0f 1e fa          	endbr64
  4012f4:	31 ed                	xor    %ebp,%ebp
  4012f6:	49 89 d1             	mov    %rdx,%r9
  4012f9:	5e                   	pop    %rsi
  4012fa:	48 89 e2             	mov    %rsp,%rdx
  4012fd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401301:	50                   	push   %rax
  401302:	54                   	push   %rsp
  401303:	45 31 c0             	xor    %r8d,%r8d
  401306:	31 c9                	xor    %ecx,%ecx
  401308:	48 c7 c7 c0 10 40 00 	mov    $0x4010c0,%rdi
  40130f:	ff 15 db 2c 00 00    	call   *0x2cdb(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  401315:	f4                   	hlt
  401316:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401320 <_dl_relocate_static_pie>:
  401320:	f3 0f 1e fa          	endbr64
  401324:	c3                   	ret
  401325:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40132f:	90                   	nop

0000000000401330 <deregister_tm_clones>:
  401330:	b8 10 40 40 00       	mov    $0x404010,%eax
  401335:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  40133b:	74 13                	je     401350 <deregister_tm_clones+0x20>
  40133d:	b8 00 00 00 00       	mov    $0x0,%eax
  401342:	48 85 c0             	test   %rax,%rax
  401345:	74 09                	je     401350 <deregister_tm_clones+0x20>
  401347:	bf 10 40 40 00       	mov    $0x404010,%edi
  40134c:	ff e0                	jmp    *%rax
  40134e:	66 90                	xchg   %ax,%ax
  401350:	c3                   	ret
  401351:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40135c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401360 <register_tm_clones>:
  401360:	be 10 40 40 00       	mov    $0x404010,%esi
  401365:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  40136c:	48 89 f0             	mov    %rsi,%rax
  40136f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401373:	48 c1 f8 03          	sar    $0x3,%rax
  401377:	48 01 c6             	add    %rax,%rsi
  40137a:	48 d1 fe             	sar    %rsi
  40137d:	74 11                	je     401390 <register_tm_clones+0x30>
  40137f:	b8 00 00 00 00       	mov    $0x0,%eax
  401384:	48 85 c0             	test   %rax,%rax
  401387:	74 07                	je     401390 <register_tm_clones+0x30>
  401389:	bf 10 40 40 00       	mov    $0x404010,%edi
  40138e:	ff e0                	jmp    *%rax
  401390:	c3                   	ret
  401391:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40139c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004013a0 <__do_global_dtors_aux>:
  4013a0:	f3 0f 1e fa          	endbr64
  4013a4:	80 3d 65 2c 00 00 00 	cmpb   $0x0,0x2c65(%rip)        # 404010 <__TMC_END__>
  4013ab:	75 13                	jne    4013c0 <__do_global_dtors_aux+0x20>
  4013ad:	55                   	push   %rbp
  4013ae:	48 89 e5             	mov    %rsp,%rbp
  4013b1:	e8 7a ff ff ff       	call   401330 <deregister_tm_clones>
  4013b6:	c6 05 53 2c 00 00 01 	movb   $0x1,0x2c53(%rip)        # 404010 <__TMC_END__>
  4013bd:	5d                   	pop    %rbp
  4013be:	c3                   	ret
  4013bf:	90                   	nop
  4013c0:	c3                   	ret
  4013c1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4013cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004013d0 <frame_dummy>:
  4013d0:	f3 0f 1e fa          	endbr64
  4013d4:	eb 8a                	jmp    401360 <register_tm_clones>
  4013d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004013e0 <work>:
void * work(void * arg) {
  4013e0:	41 57                	push   %r15
  char * output = calloc(100, sizeof(char));
  4013e2:	be 01 00 00 00       	mov    $0x1,%esi
void * work(void * arg) {
  4013e7:	41 56                	push   %r14
  4013e9:	41 55                	push   %r13
  4013eb:	41 54                	push   %r12
  4013ed:	55                   	push   %rbp
  4013ee:	48 89 fd             	mov    %rdi,%rbp
  char * output = calloc(100, sizeof(char));
  4013f1:	bf 64 00 00 00       	mov    $0x64,%edi
void * work(void * arg) {
  4013f6:	53                   	push   %rbx
  4013f7:	48 83 ec 08          	sub    $0x8,%rsp
  char * output = calloc(100, sizeof(char));
  4013fb:	e8 80 fc ff ff       	call   401080 <calloc@plt>
        if (data->main->works[x].available == 1) {
  401400:	66 0f 6f 15 c8 0c 00 00 	movdqa 0xcc8(%rip),%xmm2        # 4020d0 <_IO_stdin_used+0xd0>
  char * output = calloc(100, sizeof(char));
  401408:	49 89 c7             	mov    %rax,%r15
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  40140b:	45 31 e4             	xor    %r12d,%r12d
  40140e:	66 90                	xchg   %ax,%ax
  while (data->running == 1) {
  401410:	44 8b 6d 24          	mov    0x24(%rbp),%r13d
  401414:	41 83 fd 01          	cmp    $0x1,%r13d
  401418:	0f 85 f3 02 00 00    	jne    401711 <work+0x331>
  40141e:	4c 89 ff             	mov    %r15,%rdi
  401421:	4c 89 e0             	mov    %r12,%rax
  401424:	b9 0c 00 00 00       	mov    $0xc,%ecx
  401429:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  40142c:	c7 07 00 00 00 00    	movl   $0x0,(%rdi)
      int target = (data->main->workindex) % data->worksize;
  401432:	4c 8b 45 00          	mov    0x0(%rbp),%r8
  401436:	8b 7d 28             	mov    0x28(%rbp),%edi
      data->threads[data->threadindex].wantindex = target;
  401439:	4c 8b 55 08          	mov    0x8(%rbp),%r10
      int target = (data->main->workindex) % data->worksize;
  40143d:	41 8b 40 1c          	mov    0x1c(%r8),%eax
  401441:	99                   	cltd
  401442:	f7 ff                	idiv   %edi
      data->threads[data->threadindex].wantindex = target;
  401444:	48 63 45 2c          	movslq 0x2c(%rbp),%rax
  401448:	4c 8d 1c 80          	lea    (%rax,%rax,4),%r11
  40144c:	49 89 c1             	mov    %rax,%r9
  40144f:	49 c1 e3 04          	shl    $0x4,%r11
  401453:	4d 01 d3             	add    %r10,%r11
  401456:	41 89 53 20          	mov    %edx,0x20(%r11)
      int target = (data->main->workindex) % data->worksize;
  40145a:	89 d3                	mov    %edx,%ebx
      for (int x = 0; x < data->threadsize ; x++ ) {
  40145c:	8b 55 30             	mov    0x30(%rbp),%edx
  40145f:	85 d2                	test   %edx,%edx
  401461:	0f 8e c1 01 00 00    	jle    401628 <work+0x248>
  401467:	31 c0                	xor    %eax,%eax
  401469:	eb 14                	jmp    40147f <work+0x9f>
  40146b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401470:	83 c0 01             	add    $0x1,%eax
  401473:	48 83 c1 50          	add    $0x50,%rcx
  401477:	39 d0                	cmp    %edx,%eax
  401479:	0f 84 a9 01 00 00    	je     401628 <work+0x248>
        if (x == data->threadindex) {
  40147f:	41 39 c1             	cmp    %eax,%r9d
  401482:	74 ec                	je     401470 <work+0x90>
        if (data->threads[x].wantindex != -1 && data->threads[x].wantindex == target && data[x].failcounter > data->threads[data->threadindex].failcounter) {
  401484:	41 8b 74 0a 20       	mov    0x20(%r10,%rcx,1),%esi
  401489:	83 fe ff             	cmp    $0xffffffff,%esi
  40148c:	74 e2                	je     401470 <work+0x90>
  40148e:	39 de                	cmp    %ebx,%esi
  401490:	75 de                	jne    401470 <work+0x90>
  401492:	41 8b 73 48          	mov    0x48(%r11),%esi
  401496:	39 74 0d 48          	cmp    %esi,0x48(%rbp,%rcx,1)
  40149a:	7e d4                	jle    401470 <work+0x90>
  40149c:	bf 01 00 00 00       	mov    $0x1,%edi
  4014a1:	44 89 ca             	mov    %r9d,%edx
  4014a4:	48 8d 35 59 0b 00 00 	lea    0xb59(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  4014ab:	31 c0                	xor    %eax,%eax
  4014ad:	e8 de fb ff ff       	call   401090 <__printf_chk@plt>
          data->threads[data->threadindex].wantindex = -1;
  4014b2:	48 63 45 2c          	movslq 0x2c(%rbp),%rax
      for (int x = 0; x < data->worksize ; x++) {
  4014b6:	8b 7d 28             	mov    0x28(%rbp),%edi
  4014b9:	66 0f 6f 15 0f 0c 00 00 	movdqa 0xc0f(%rip),%xmm2        # 4020d0 <_IO_stdin_used+0xd0>
          data->threads[data->threadindex].wantindex = -1;
  4014c1:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  4014c5:	48 c1 e0 04          	shl    $0x4,%rax
  4014c9:	48 03 45 08          	add    0x8(%rbp),%rax
          data->threads[data->threadindex].failcounter++;
  4014cd:	83 40 48 01          	addl   $0x1,0x48(%rax)
          data->threads[data->threadindex].wantindex = -1;
  4014d1:	c7 40 20 ff ff ff ff 	movl   $0xffffffff,0x20(%rax)
      if (available == 1 && data->main->works[target].available == 1) {
  4014d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      for (int x = 0; x < data->worksize ; x++) {
  4014e0:	85 ff                	test   %edi,%edi
  4014e2:	0f 8e eb 00 00 00    	jle    4015d3 <work+0x1f3>
        if (data->main->works[x].available == 1) {
  4014e8:	48 8b 45 00          	mov    0x0(%rbp),%rax
  4014ec:	8d 57 ff             	lea    -0x1(%rdi),%edx
  4014ef:	48 8b 70 38          	mov    0x38(%rax),%rsi
  4014f3:	83 fa 03             	cmp    $0x3,%edx
  4014f6:	0f 86 37 02 00 00    	jbe    401733 <work+0x353>
  4014fc:	89 d1                	mov    %edx,%ecx
  4014fe:	48 8d 46 04          	lea    0x4(%rsi),%rax
  401502:	66 0f 6f ca          	movdqa %xmm2,%xmm1
  401506:	c1 e9 02             	shr    $0x2,%ecx
  401509:	83 e9 01             	sub    $0x1,%ecx
  40150c:	48 c1 e1 05          	shl    $0x5,%rcx
  401510:	48 8d 4c 0e 24       	lea    0x24(%rsi,%rcx,1),%rcx
  401515:	0f 1f 00             	nopl   (%rax)
  401518:	f3 0f 6f 00          	movdqu (%rax),%xmm0
  40151c:	f3 0f 6f 60 10       	movdqu 0x10(%rax),%xmm4
  401521:	48 83 c0 20          	add    $0x20,%rax
  401525:	0f c6 c4 88          	shufps $0x88,%xmm4,%xmm0
  401529:	66 0f 76 c2          	pcmpeqd %xmm2,%xmm0
  40152d:	66 0f df c1          	pandn  %xmm1,%xmm0
  401531:	66 0f 6f c8          	movdqa %xmm0,%xmm1
      for (int x = 0; x < data->worksize ; x++) {
  401535:	48 39 c8             	cmp    %rcx,%rax
  401538:	75 de                	jne    401518 <work+0x138>
  40153a:	66 0f 6f d8          	movdqa %xmm0,%xmm3
  40153e:	83 e2 fc             	and    $0xfffffffc,%edx
  401541:	66 0f 73 db 08       	psrldq $0x8,%xmm3
  401546:	66 0f 6f c3          	movdqa %xmm3,%xmm0
  40154a:	66 0f 66 c1          	pcmpgtd %xmm1,%xmm0
  40154e:	66 0f db c8          	pand   %xmm0,%xmm1
  401552:	66 0f df c3          	pandn  %xmm3,%xmm0
  401556:	66 0f eb c1          	por    %xmm1,%xmm0
  40155a:	66 0f 6f d8          	movdqa %xmm0,%xmm3
  40155e:	66 0f 73 db 04       	psrldq $0x4,%xmm3
  401563:	66 0f 6f cb          	movdqa %xmm3,%xmm1
  401567:	66 0f 66 c8          	pcmpgtd %xmm0,%xmm1
  40156b:	66 0f db c1          	pand   %xmm1,%xmm0
  40156f:	66 0f df cb          	pandn  %xmm3,%xmm1
  401573:	66 0f eb c8          	por    %xmm0,%xmm1
  401577:	66 41 0f 7e cd       	movd   %xmm1,%r13d
        if (data->main->works[x].available == 1) {
  40157c:	48 63 c2             	movslq %edx,%rax
      for (int x = 0; x < data->worksize ; x++) {
  40157f:	83 c2 01             	add    $0x1,%edx
        if (data->main->works[x].available == 1) {
  401582:	83 7c c6 04 01       	cmpl   $0x1,0x4(%rsi,%rax,8)
  401587:	0f 84 33 01 00 00    	je     4016c0 <work+0x2e0>
      for (int x = 0; x < data->worksize ; x++) {
  40158d:	39 fa                	cmp    %edi,%edx
  40158f:	7d 38                	jge    4015c9 <work+0x1e9>
        if (data->main->works[x].available == 1) {
  401591:	48 63 c2             	movslq %edx,%rax
      for (int x = 0; x < data->worksize ; x++) {
  401594:	83 c2 01             	add    $0x1,%edx
        if (data->main->works[x].available == 1) {
  401597:	83 7c c6 04 01       	cmpl   $0x1,0x4(%rsi,%rax,8)
  40159c:	0f 84 3a 01 00 00    	je     4016dc <work+0x2fc>
      for (int x = 0; x < data->worksize ; x++) {
  4015a2:	39 d7                	cmp    %edx,%edi
  4015a4:	7e 23                	jle    4015c9 <work+0x1e9>
        if (data->main->works[x].available == 1) {
  4015a6:	48 63 c2             	movslq %edx,%rax
      for (int x = 0; x < data->worksize ; x++) {
  4015a9:	83 c2 01             	add    $0x1,%edx
        if (data->main->works[x].available == 1) {
  4015ac:	83 7c c6 04 01       	cmpl   $0x1,0x4(%rsi,%rax,8)
  4015b1:	0f 84 41 01 00 00    	je     4016f8 <work+0x318>
      for (int x = 0; x < data->worksize ; x++) {
  4015b7:	39 fa                	cmp    %edi,%edx
  4015b9:	7d 0e                	jge    4015c9 <work+0x1e9>
        if (data->main->works[x].available == 1) {
  4015bb:	48 63 d2             	movslq %edx,%rdx
  4015be:	83 7c d6 04 01       	cmpl   $0x1,0x4(%rsi,%rdx,8)
  4015c3:	0f 84 47 fe ff ff    	je     401410 <work+0x30>
      if (allunavailable == 1) {
  4015c9:	41 83 fd 01          	cmp    $0x1,%r13d
  4015cd:	0f 85 3d fe ff ff    	jne    401410 <work+0x30>
  4015d3:	48 8d 3d 33 0a 00 00 	lea    0xa33(%rip),%rdi        # 40200d <_IO_stdin_used+0xd>
  4015da:	e8 71 fa ff ff       	call   401050 <puts@plt>
        for (int x = 0 ; x < data->worksize; x++) {
  4015df:	8b 4d 28             	mov    0x28(%rbp),%ecx
  4015e2:	66 0f 6f 15 e6 0a 00 00 	movdqa 0xae6(%rip),%xmm2        # 4020d0 <_IO_stdin_used+0xd0>
  4015ea:	85 c9                	test   %ecx,%ecx
  4015ec:	0f 8e 19 fe ff ff    	jle    40140b <work+0x2b>
          data->main->works[x].available = 1;
  4015f2:	48 8b 45 00          	mov    0x0(%rbp),%rax
  4015f6:	83 e9 01             	sub    $0x1,%ecx
  4015f9:	48 8b 50 38          	mov    0x38(%rax),%rdx
  4015fd:	48 8d 42 04          	lea    0x4(%rdx),%rax
  401601:	48 8d 54 ca 0c       	lea    0xc(%rdx,%rcx,8),%rdx
  401606:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401610:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
        for (int x = 0 ; x < data->worksize; x++) {
  401616:	48 83 c0 08          	add    $0x8,%rax
  40161a:	48 39 d0             	cmp    %rdx,%rax
  40161d:	75 f1                	jne    401610 <work+0x230>
  40161f:	e9 e7 fd ff ff       	jmp    40140b <work+0x2b>
  401624:	0f 1f 40 00          	nopl   0x0(%rax)
      if (available == 1 && data->main->works[target].available == 1) {
  401628:	49 8b 50 38          	mov    0x38(%r8),%rdx
  40162c:	48 63 c3             	movslq %ebx,%rax
  40162f:	4c 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%r14
  401637:	83 7c c2 04 01       	cmpl   $0x1,0x4(%rdx,%rax,8)
  40163c:	0f 85 9e fe ff ff    	jne    4014e0 <work+0x100>
        if (data->threadindex == 0) {
  401642:	45 85 c9             	test   %r9d,%r9d
  401645:	0f 85 d7 00 00 00    	jne    401722 <work+0x342>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  40164b:	48 83 ec 08          	sub    $0x8,%rsp
  40164f:	4c 8d 05 f2 09 00 00 	lea    0x9f2(%rip),%r8        # 402048 <_IO_stdin_used+0x48>
  401656:	53                   	push   %rbx
  401657:	b9 64 00 00 00       	mov    $0x64,%ecx
  40165c:	ba 01 00 00 00       	mov    $0x1,%edx
  401661:	4c 89 ff             	mov    %r15,%rdi
  401664:	31 c0                	xor    %eax,%eax
  401666:	be 64 00 00 00       	mov    $0x64,%esi
  40166b:	e8 c0 f9 ff ff       	call   401030 <__snprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  401670:	4c 89 ff             	mov    %r15,%rdi
  401673:	e8 d8 f9 ff ff       	call   401050 <puts@plt>
        data->main->works[target].available = 0;
  401678:	48 8b 4d 00          	mov    0x0(%rbp),%rcx
  40167c:	58                   	pop    %rax
  40167d:	5a                   	pop    %rdx
        data->main->workindex = (target + 1) % data->worksize;
  40167e:	8b 7d 28             	mov    0x28(%rbp),%edi
        data->main->works[target].available = 0;
  401681:	48 8b 41 38          	mov    0x38(%rcx),%rax
  401685:	66 0f 6f 15 43 0a 00 00 	movdqa 0xa43(%rip),%xmm2        # 4020d0 <_IO_stdin_used+0xd0>
  40168d:	42 c7 44 30 04 00 00 00 00 	movl   $0x0,0x4(%rax,%r14,1)
        data->threads[data->threadindex].wantindex = -1;
  401696:	48 63 45 2c          	movslq 0x2c(%rbp),%rax
  40169a:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  40169e:	48 c1 e0 04          	shl    $0x4,%rax
  4016a2:	48 03 45 08          	add    0x8(%rbp),%rax
  4016a6:	c7 40 20 ff ff ff ff 	movl   $0xffffffff,0x20(%rax)
        data->main->workindex = (target + 1) % data->worksize;
  4016ad:	8d 43 01             	lea    0x1(%rbx),%eax
  4016b0:	99                   	cltd
  4016b1:	f7 ff                	idiv   %edi
  4016b3:	89 51 1c             	mov    %edx,0x1c(%rcx)
  4016b6:	e9 25 fe ff ff       	jmp    4014e0 <work+0x100>
  4016bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          allunavailable = 0;
  4016c0:	45 31 ed             	xor    %r13d,%r13d
      for (int x = 0; x < data->worksize ; x++) {
  4016c3:	39 fa                	cmp    %edi,%edx
  4016c5:	0f 8d 45 fd ff ff    	jge    401410 <work+0x30>
        if (data->main->works[x].available == 1) {
  4016cb:	48 63 c2             	movslq %edx,%rax
      for (int x = 0; x < data->worksize ; x++) {
  4016ce:	83 c2 01             	add    $0x1,%edx
        if (data->main->works[x].available == 1) {
  4016d1:	83 7c c6 04 01       	cmpl   $0x1,0x4(%rsi,%rax,8)
  4016d6:	0f 85 c6 fe ff ff    	jne    4015a2 <work+0x1c2>
          allunavailable = 0;
  4016dc:	45 31 ed             	xor    %r13d,%r13d
      for (int x = 0; x < data->worksize ; x++) {
  4016df:	39 fa                	cmp    %edi,%edx
  4016e1:	0f 8d 29 fd ff ff    	jge    401410 <work+0x30>
        if (data->main->works[x].available == 1) {
  4016e7:	48 63 c2             	movslq %edx,%rax
      for (int x = 0; x < data->worksize ; x++) {
  4016ea:	83 c2 01             	add    $0x1,%edx
        if (data->main->works[x].available == 1) {
  4016ed:	83 7c c6 04 01       	cmpl   $0x1,0x4(%rsi,%rax,8)
  4016f2:	0f 85 bf fe ff ff    	jne    4015b7 <work+0x1d7>
          allunavailable = 0;
  4016f8:	45 31 ed             	xor    %r13d,%r13d
      for (int x = 0; x < data->worksize ; x++) {
  4016fb:	39 fa                	cmp    %edi,%edx
  4016fd:	0f 8c b8 fe ff ff    	jl     4015bb <work+0x1db>
  while (data->running == 1) {
  401703:	44 8b 6d 24          	mov    0x24(%rbp),%r13d
  401707:	41 83 fd 01          	cmp    $0x1,%r13d
  40170b:	0f 84 0d fd ff ff    	je     40141e <work+0x3e>
  }
  401711:	48 83 c4 08          	add    $0x8,%rsp
  401715:	31 c0                	xor    %eax,%eax
  401717:	5b                   	pop    %rbx
  401718:	5d                   	pop    %rbp
  401719:	41 5c                	pop    %r12
  40171b:	41 5d                	pop    %r13
  40171d:	41 5e                	pop    %r14
  40171f:	41 5f                	pop    %r15
  401721:	c3                   	ret
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401722:	48 83 ec 08          	sub    $0x8,%rsp
  401726:	4c 8d 05 4b 09 00 00 	lea    0x94b(%rip),%r8        # 402078 <_IO_stdin_used+0x78>
  40172d:	53                   	push   %rbx
  40172e:	e9 24 ff ff ff       	jmp    401657 <work+0x277>
      for (int x = 0; x < data->worksize ; x++) {
  401733:	31 d2                	xor    %edx,%edx
  401735:	e9 42 fe ff ff       	jmp    40157c <work+0x19c>

Disassembly of section .fini:

000000000040173c <_fini>:
  40173c:	f3 0f 1e fa          	endbr64
  401740:	48 83 ec 08          	sub    $0x8,%rsp
  401744:	48 83 c4 08          	add    $0x8,%rsp
  401748:	c3                   	ret
