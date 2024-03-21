
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
  4010cc:	48 8d 35 40 0f 00 00 	lea    0xf40(%rip),%rsi        # 402013 <_IO_stdin_used+0x13>
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
  401142:	66 0f 6f 05 76 0f 00 00 	movdqa 0xf76(%rip),%xmm0        # 4020c0 <_IO_stdin_used+0xc0>
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
  401172:	4c 8d 2d 27 0f 00 00 	lea    0xf27(%rip),%r13        # 4020a0 <_IO_stdin_used+0xa0>
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
  4011a6:	66 0f 6f 05 22 0f 00 00 	movdqa 0xf22(%rip),%xmm0        # 4020d0 <_IO_stdin_used+0xd0>
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
  4011fa:	66 0f 6f 05 de 0e 00 00 	movdqa 0xede(%rip),%xmm0        # 4020e0 <_IO_stdin_used+0xe0>
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
  401269:	66 0f 6f 05 7f 0e 00 00 	movdqa 0xe7f(%rip),%xmm0        # 4020f0 <_IO_stdin_used+0xf0>
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
  4012b4:	48 8d 3d 6d 0d 00 00 	lea    0xd6d(%rip),%rdi        # 402028 <_IO_stdin_used+0x28>
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
  4013e0:	41 56                	push   %r14
  char * output = calloc(100, sizeof(char));
  4013e2:	be 01 00 00 00       	mov    $0x1,%esi
void * work(void * arg) {
  4013e7:	41 55                	push   %r13
  4013e9:	41 54                	push   %r12
  4013eb:	55                   	push   %rbp
  4013ec:	53                   	push   %rbx
  4013ed:	48 89 fb             	mov    %rdi,%rbx
  char * output = calloc(100, sizeof(char));
  4013f0:	bf 64 00 00 00       	mov    $0x64,%edi
  4013f5:	e8 86 fc ff ff       	call   401080 <calloc@plt>
  while (data->running == 1) {
  4013fa:	83 7b 24 01          	cmpl   $0x1,0x24(%rbx)
  4013fe:	0f 85 28 01 00 00    	jne    40152c <work+0x14c>
  401404:	4c 8b 03             	mov    (%rbx),%r8
  401407:	49 89 c5             	mov    %rax,%r13
  40140a:	48 8d 2d f3 0b 00 00 	lea    0xbf3(%rip),%rbp        # 402004 <_IO_stdin_used+0x4>
  401411:	eb 0f                	jmp    401422 <work+0x42>
  401413:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401418:	83 7b 24 01          	cmpl   $0x1,0x24(%rbx)
  40141c:	0f 85 0a 01 00 00    	jne    40152c <work+0x14c>
   case no work is done at all.  We detect these problems by referring
   non-existing functions.  */
__fortify_function void *
__NTH (memset (void *__dest, int __ch, size_t __len))
{
  return __builtin___memset_chk (__dest, __ch, __len,
  401422:	31 c0                	xor    %eax,%eax
  401424:	b9 0c 00 00 00       	mov    $0xc,%ecx
  401429:	4c 89 ef             	mov    %r13,%rdi
  40142c:	f3 48 ab             	rep stos %rax,%es:(%rdi)
    if (data->threadindex != 0 && data->main->workindex >= data->worksize) { continue; }
  40142f:	8b 4b 2c             	mov    0x2c(%rbx),%ecx
  401432:	8b 43 28             	mov    0x28(%rbx),%eax
  401435:	85 c9                	test   %ecx,%ecx
  401437:	c7 07 00 00 00 00    	movl   $0x0,(%rdi)
  40143d:	0f 84 f5 00 00 00    	je     401538 <work+0x158>
  401443:	41 39 40 1c          	cmp    %eax,0x1c(%r8)
  401447:	7d cf                	jge    401418 <work+0x38>
      data->threads[data->threadindex].wantindex = target;
  401449:	48 63 43 2c          	movslq 0x2c(%rbx),%rax
      int target = (data->main->workindex);
  40144d:	4c 8b 03             	mov    (%rbx),%r8
      data->threads[data->threadindex].wantindex = target;
  401450:	48 8b 53 08          	mov    0x8(%rbx),%rdx
      for (int x = 0; x < data->threadsize ; x++ ) {
  401454:	8b 73 30             	mov    0x30(%rbx),%esi
      data->threads[data->threadindex].wantindex = target;
  401457:	48 8d 3c 80          	lea    (%rax,%rax,4),%rdi
      int target = (data->main->workindex);
  40145b:	45 8b 60 1c          	mov    0x1c(%r8),%r12d
      data->threads[data->threadindex].wantindex = target;
  40145f:	49 89 c1             	mov    %rax,%r9
  401462:	48 c1 e7 04          	shl    $0x4,%rdi
  401466:	48 01 d7             	add    %rdx,%rdi
  401469:	44 89 67 20          	mov    %r12d,0x20(%rdi)
      for (int x = 0; x < data->threadsize ; x++ ) {
  40146d:	85 f6                	test   %esi,%esi
  40146f:	7e 2f                	jle    4014a0 <work+0xc0>
  401471:	48 83 c2 20          	add    $0x20,%rdx
  401475:	31 c0                	xor    %eax,%eax
  401477:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        if (x == data->threadindex) {
  401480:	41 39 c1             	cmp    %eax,%r9d
  401483:	74 10                	je     401495 <work+0xb5>
        if (data->threads[x].wantindex != -1 && data->threads[x].wantindex == target /*&& data[x].failcounter > data->threads[data->threadindex].failcounter*/) {
  401485:	8b 0a                	mov    (%rdx),%ecx
  401487:	83 f9 ff             	cmp    $0xffffffff,%ecx
  40148a:	74 09                	je     401495 <work+0xb5>
  40148c:	44 39 e1             	cmp    %r12d,%ecx
  40148f:	0f 84 f3 00 00 00    	je     401588 <work+0x1a8>
      for (int x = 0; x < data->threadsize ; x++ ) {
  401495:	83 c0 01             	add    $0x1,%eax
  401498:	48 83 c2 50          	add    $0x50,%rdx
  40149c:	39 f0                	cmp    %esi,%eax
  40149e:	75 e0                	jne    401480 <work+0xa0>
      if (available == 1 && data->main->works[target].available == 1) {
  4014a0:	49 8b 50 38          	mov    0x38(%r8),%rdx
  4014a4:	49 63 c4             	movslq %r12d,%rax
  4014a7:	4c 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%r14
  4014af:	83 7c c2 04 01       	cmpl   $0x1,0x4(%rdx,%rax,8)
  4014b4:	0f 85 5e ff ff ff    	jne    401418 <work+0x38>
        if (data->threadindex == 0) {
  4014ba:	45 85 c9             	test   %r9d,%r9d
  4014bd:	0f 85 d5 00 00 00    	jne    401598 <work+0x1b8>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  4014c3:	48 83 ec 08          	sub    $0x8,%rsp
  4014c7:	4c 8d 05 72 0b 00 00 	lea    0xb72(%rip),%r8        # 402040 <_IO_stdin_used+0x40>
  4014ce:	41 54                	push   %r12
  4014d0:	ba 01 00 00 00       	mov    $0x1,%edx
  4014d5:	b9 64 00 00 00       	mov    $0x64,%ecx
  4014da:	4c 89 ef             	mov    %r13,%rdi
  4014dd:	31 c0                	xor    %eax,%eax
  4014df:	be 64 00 00 00       	mov    $0x64,%esi
        data->main->workindex = (target + 1);
  4014e4:	41 83 c4 01          	add    $0x1,%r12d
  4014e8:	e8 43 fb ff ff       	call   401030 <__snprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4014ed:	4c 89 ef             	mov    %r13,%rdi
  4014f0:	e8 5b fb ff ff       	call   401050 <puts@plt>
        data->main->works[target].available = 0;
  4014f5:	4c 8b 03             	mov    (%rbx),%r8
  4014f8:	58                   	pop    %rax
  4014f9:	5a                   	pop    %rdx
  4014fa:	49 8b 40 38          	mov    0x38(%r8),%rax
  4014fe:	42 c7 44 30 04 00 00 00 00 	movl   $0x0,0x4(%rax,%r14,1)
        data->threads[data->threadindex].wantindex = -1;
  401507:	48 63 43 2c          	movslq 0x2c(%rbx),%rax
  40150b:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  40150f:	48 c1 e0 04          	shl    $0x4,%rax
  401513:	48 03 43 08          	add    0x8(%rbx),%rax
  while (data->running == 1) {
  401517:	83 7b 24 01          	cmpl   $0x1,0x24(%rbx)
        data->threads[data->threadindex].wantindex = -1;
  40151b:	c7 40 20 ff ff ff ff 	movl   $0xffffffff,0x20(%rax)
        data->main->workindex = (target + 1);
  401522:	45 89 60 1c          	mov    %r12d,0x1c(%r8)
  while (data->running == 1) {
  401526:	0f 84 f6 fe ff ff    	je     401422 <work+0x42>
  }
  40152c:	5b                   	pop    %rbx
  40152d:	5d                   	pop    %rbp
  40152e:	41 5c                	pop    %r12
  401530:	41 5d                	pop    %r13
  401532:	41 5e                	pop    %r14
  401534:	c3                   	ret
  401535:	0f 1f 00             	nopl   (%rax)
    if (data->threadindex == 0 && data->main->workindex >= data->worksize) {
  401538:	41 39 40 1c          	cmp    %eax,0x1c(%r8)
  40153c:	0f 8c 07 ff ff ff    	jl     401449 <work+0x69>
        data->main->workindex = 0;
  401542:	41 c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%r8)
  40154a:	48 89 ef             	mov    %rbp,%rdi
  40154d:	e8 fe fa ff ff       	call   401050 <puts@plt>
        for (int x = 0 ; x < data->worksize; x++) {
  401552:	8b 53 28             	mov    0x28(%rbx),%edx
  401555:	85 d2                	test   %edx,%edx
  401557:	0f 8e ec fe ff ff    	jle    401449 <work+0x69>
          data->main->works[x].available = 1;
  40155d:	48 8b 03             	mov    (%rbx),%rax
  401560:	83 ea 01             	sub    $0x1,%edx
  401563:	48 8b 48 38          	mov    0x38(%rax),%rcx
  401567:	48 8d 41 04          	lea    0x4(%rcx),%rax
  40156b:	48 8d 54 d1 0c       	lea    0xc(%rcx,%rdx,8),%rdx
  401570:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
        for (int x = 0 ; x < data->worksize; x++) {
  401576:	48 83 c0 08          	add    $0x8,%rax
  40157a:	48 39 c2             	cmp    %rax,%rdx
  40157d:	75 f1                	jne    401570 <work+0x190>
  40157f:	e9 c5 fe ff ff       	jmp    401449 <work+0x69>
  401584:	0f 1f 40 00          	nopl   0x0(%rax)
          data->threads[data->threadindex].failcounter++;
  401588:	83 47 48 01          	addl   $0x1,0x48(%rdi)
          data->threads[data->threadindex].wantindex = -1;
  40158c:	c7 47 20 ff ff ff ff 	movl   $0xffffffff,0x20(%rdi)
      if (available == 1 && data->main->works[target].available == 1) {
  401593:	e9 80 fe ff ff       	jmp    401418 <work+0x38>
  return __builtin___snprintf_chk (__s, __n, __USE_FORTIFY_LEVEL - 1,
  401598:	48 83 ec 08          	sub    $0x8,%rsp
  40159c:	4c 8d 05 cd 0a 00 00 	lea    0xacd(%rip),%r8        # 402070 <_IO_stdin_used+0x70>
  4015a3:	41 54                	push   %r12
  4015a5:	e9 26 ff ff ff       	jmp    4014d0 <work+0xf0>

Disassembly of section .fini:

00000000004015ac <_fini>:
  4015ac:	f3 0f 1e fa          	endbr64
  4015b0:	48 83 ec 08          	sub    $0x8,%rsp
  4015b4:	48 83 c4 08          	add    $0x8,%rsp
  4015b8:	c3                   	ret
