
stream2-workqueue:     file format elf64-x86-64


Disassembly of section .init:

0000000000401000 <_init>:
  401000:	f3 0f 1e fa          	endbr64
  401004:	48 83 ec 08          	sub    $0x8,%rsp
  401008:	48 8b 05 e9 4f 00 00 	mov    0x4fe9(%rip),%rax        # 405ff8 <__gmon_start__@Base>
  40100f:	48 85 c0             	test   %rax,%rax
  401012:	74 02                	je     401016 <_init+0x16>
  401014:	ff d0                	call   *%rax
  401016:	48 83 c4 08          	add    $0x8,%rsp
  40101a:	c3                   	ret

Disassembly of section .plt:

0000000000401020 <pthread_setaffinity_np@plt-0x10>:
  401020:	ff 35 3a 4f 00 00    	push   0x4f3a(%rip)        # 405f60 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 3c 4f 00 00    	jmp    *0x4f3c(%rip)        # 405f68 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <pthread_setaffinity_np@plt>:
  401030:	ff 25 3a 4f 00 00    	jmp    *0x4f3a(%rip)        # 405f70 <pthread_setaffinity_np@GLIBC_2.34>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <puts@plt>:
  401040:	ff 25 32 4f 00 00    	jmp    *0x4f32(%rip)        # 405f78 <puts@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <clock_gettime@plt>:
  401050:	ff 25 2a 4f 00 00    	jmp    *0x4f2a(%rip)        # 405f80 <clock_gettime@GLIBC_2.17>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <fclose@plt>:
  401060:	ff 25 22 4f 00 00    	jmp    *0x4f22(%rip)        # 405f88 <fclose@GLIBC_2.2.5>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <__stack_chk_fail@plt>:
  401070:	ff 25 1a 4f 00 00    	jmp    *0x4f1a(%rip)        # 405f90 <__stack_chk_fail@GLIBC_2.4>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <printf@plt>:
  401080:	ff 25 12 4f 00 00    	jmp    *0x4f12(%rip)        # 405f98 <printf@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <snprintf@plt>:
  401090:	ff 25 0a 4f 00 00    	jmp    *0x4f0a(%rip)        # 405fa0 <snprintf@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <nanosleep@plt>:
  4010a0:	ff 25 02 4f 00 00    	jmp    *0x4f02(%rip)        # 405fa8 <nanosleep@GLIBC_2.2.5>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <fputs@plt>:
  4010b0:	ff 25 fa 4e 00 00    	jmp    *0x4efa(%rip)        # 405fb0 <fputs@GLIBC_2.2.5>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <memset@plt>:
  4010c0:	ff 25 f2 4e 00 00    	jmp    *0x4ef2(%rip)        # 405fb8 <memset@GLIBC_2.2.5>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010d0 <calloc@plt>:
  4010d0:	ff 25 ea 4e 00 00    	jmp    *0x4eea(%rip)        # 405fc0 <calloc@GLIBC_2.2.5>
  4010d6:	68 0a 00 00 00       	push   $0xa
  4010db:	e9 40 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010e0 <pthread_create@plt>:
  4010e0:	ff 25 e2 4e 00 00    	jmp    *0x4ee2(%rip)        # 405fc8 <pthread_create@GLIBC_2.34>
  4010e6:	68 0b 00 00 00       	push   $0xb
  4010eb:	e9 30 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010f0 <fopen@plt>:
  4010f0:	ff 25 da 4e 00 00    	jmp    *0x4eda(%rip)        # 405fd0 <fopen@GLIBC_2.2.5>
  4010f6:	68 0c 00 00 00       	push   $0xc
  4010fb:	e9 20 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401100 <posix_memalign@plt>:
  401100:	ff 25 d2 4e 00 00    	jmp    *0x4ed2(%rip)        # 405fd8 <posix_memalign@GLIBC_2.2.5>
  401106:	68 0d 00 00 00       	push   $0xd
  40110b:	e9 10 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401110 <pthread_join@plt>:
  401110:	ff 25 ca 4e 00 00    	jmp    *0x4eca(%rip)        # 405fe0 <pthread_join@GLIBC_2.34>
  401116:	68 0e 00 00 00       	push   $0xe
  40111b:	e9 00 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401120 <ceil@plt>:
  401120:	ff 25 c2 4e 00 00    	jmp    *0x4ec2(%rip)        # 405fe8 <ceil@GLIBC_2.2.5>
  401126:	68 0f 00 00 00       	push   $0xf
  40112b:	e9 f0 fe ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

0000000000401130 <_start>:
  401130:	f3 0f 1e fa          	endbr64
  401134:	31 ed                	xor    %ebp,%ebp
  401136:	49 89 d1             	mov    %rdx,%r9
  401139:	5e                   	pop    %rsi
  40113a:	48 89 e2             	mov    %rsp,%rdx
  40113d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401141:	50                   	push   %rax
  401142:	54                   	push   %rsp
  401143:	45 31 c0             	xor    %r8d,%r8d
  401146:	31 c9                	xor    %ecx,%ecx
  401148:	48 c7 c7 8f 20 40 00 	mov    $0x40208f,%rdi
  40114f:	ff 15 9b 4e 00 00    	call   *0x4e9b(%rip)        # 405ff0 <__libc_start_main@GLIBC_2.34>
  401155:	f4                   	hlt
  401156:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401160 <_dl_relocate_static_pie>:
  401160:	f3 0f 1e fa          	endbr64
  401164:	c3                   	ret
  401165:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40116f:	90                   	nop

0000000000401170 <deregister_tm_clones>:
  401170:	b8 10 60 40 00       	mov    $0x406010,%eax
  401175:	48 3d 10 60 40 00    	cmp    $0x406010,%rax
  40117b:	74 13                	je     401190 <deregister_tm_clones+0x20>
  40117d:	b8 00 00 00 00       	mov    $0x0,%eax
  401182:	48 85 c0             	test   %rax,%rax
  401185:	74 09                	je     401190 <deregister_tm_clones+0x20>
  401187:	bf 10 60 40 00       	mov    $0x406010,%edi
  40118c:	ff e0                	jmp    *%rax
  40118e:	66 90                	xchg   %ax,%ax
  401190:	c3                   	ret
  401191:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40119c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004011a0 <register_tm_clones>:
  4011a0:	be 10 60 40 00       	mov    $0x406010,%esi
  4011a5:	48 81 ee 10 60 40 00 	sub    $0x406010,%rsi
  4011ac:	48 89 f0             	mov    %rsi,%rax
  4011af:	48 c1 ee 3f          	shr    $0x3f,%rsi
  4011b3:	48 c1 f8 03          	sar    $0x3,%rax
  4011b7:	48 01 c6             	add    %rax,%rsi
  4011ba:	48 d1 fe             	sar    %rsi
  4011bd:	74 11                	je     4011d0 <register_tm_clones+0x30>
  4011bf:	b8 00 00 00 00       	mov    $0x0,%eax
  4011c4:	48 85 c0             	test   %rax,%rax
  4011c7:	74 07                	je     4011d0 <register_tm_clones+0x30>
  4011c9:	bf 10 60 40 00       	mov    $0x406010,%edi
  4011ce:	ff e0                	jmp    *%rax
  4011d0:	c3                   	ret
  4011d1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4011dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004011e0 <__do_global_dtors_aux>:
  4011e0:	f3 0f 1e fa          	endbr64
  4011e4:	80 3d 25 4e 00 00 00 	cmpb   $0x0,0x4e25(%rip)        # 406010 <__TMC_END__>
  4011eb:	75 13                	jne    401200 <__do_global_dtors_aux+0x20>
  4011ed:	55                   	push   %rbp
  4011ee:	48 89 e5             	mov    %rsp,%rbp
  4011f1:	e8 7a ff ff ff       	call   401170 <deregister_tm_clones>
  4011f6:	c6 05 13 4e 00 00 01 	movb   $0x1,0x4e13(%rip)        # 406010 <__TMC_END__>
  4011fd:	5d                   	pop    %rbp
  4011fe:	c3                   	ret
  4011ff:	90                   	nop
  401200:	c3                   	ret
  401201:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40120c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401210 <frame_dummy>:
  401210:	f3 0f 1e fa          	endbr64
  401214:	eb 8a                	jmp    4011a0 <register_tm_clones>

0000000000401216 <yield>:
  int set;
  int dest;
  int stream;
};   
 
int yield() {
  401216:	55                   	push   %rbp
  401217:	48 89 e5             	mov    %rsp,%rbp
   
}
  40121a:	90                   	nop
  40121b:	5d                   	pop    %rbp
  40121c:	c3                   	ret

000000000040121d <coroutine_func>:

uint64_t coroutine_func(void) {
  40121d:	55                   	push   %rbp
  40121e:	48 89 e5             	mov    %rsp,%rbp
  401221:	48 83 ec 30          	sub    $0x30,%rsp
  struct Scheduler * scheduler;
  struct Coroutine * coroutine;
  struct CoroutineData * data;
  
  asm("movq %%rdi, %0" : "=r" (scheduler));
  401225:	48 89 f8             	mov    %rdi,%rax
  401228:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
  asm ("movq %%rsi, %0" : "=r" (coroutine)::);
  40122c:	48 89 f0             	mov    %rsi,%rax
  40122f:	48 89 45 e0          	mov    %rax,-0x20(%rbp)
asm ("movq %%rdx, %0" : "=r" (data)::);    
  401233:	48 89 d0             	mov    %rdx,%rax
  401236:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
// struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data) {
  uint64_t myrsp;
  asm("movq %%rsp, %0" :"=rm"(myrsp));   
  40123a:	48 89 e0             	mov    %rsp,%rax
  40123d:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
 printf("startrsp %p\n%p %p %p coro\n", myrsp, scheduler, coroutine, data);
  401241:	48 8b 75 e8          	mov    -0x18(%rbp),%rsi
  401245:	48 8b 4d e0          	mov    -0x20(%rbp),%rcx
  401249:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  40124d:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401251:	49 89 f0             	mov    %rsi,%r8
  401254:	48 89 c6             	mov    %rax,%rsi
  401257:	48 8d 05 aa 2d 00 00 	lea    0x2daa(%rip),%rax        # 404008 <_IO_stdin_used+0x8>
  40125e:	48 89 c7             	mov    %rax,%rdi
  401261:	b8 00 00 00 00       	mov    $0x0,%eax
  401266:	e8 15 fe ff ff       	call   401080 <printf@plt>
   
  //while (data->running == 1) {
   //printf("%ld\n", coroutine->eip); 
  //asm("lea %0, %%r11\n"
   //   "movq %%r11, %1" : "=rm" (coroutine->eip) ::"r11");
   coroutine->eip = &&resume;
  40126b:	48 8d 15 08 00 00 00 	lea    0x8(%rip),%rdx        # 40127a <coroutine_func+0x5d>
  401272:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401276:	48 89 50 10          	mov    %rdx,0x10(%rax)
  // cant clobber rsp from inside coroutind :-(
  
resume:
  asm("movq %%rdi, %0" : "=r" (scheduler));
  40127a:	48 89 f8             	mov    %rdi,%rax
  40127d:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    asm ("movq %%rsi, %0" : "=r" (coroutine)::);
  401281:	48 89 f0             	mov    %rsi,%rax
  401284:	48 89 45 e0          	mov    %rax,-0x20(%rbp)
  asm ("movq %%rdx, %0" : "=r" (data)::);    
  401288:	48 89 d0             	mov    %rdx,%rax
  40128b:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  //printf("resume\n");
    // yield(1, scheduler, coroutine)  {
  uint64_t rsp = scheduler->rsp;
  40128f:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401293:	48 8b 00             	mov    (%rax),%rax
  401296:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  printf("scheduler %p scheduler %p\n", scheduler, rsp);
  40129a:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  40129e:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4012a2:	48 89 c6             	mov    %rax,%rsi
  4012a5:	48 8d 05 77 2d 00 00 	lea    0x2d77(%rip),%rax        # 404023 <_IO_stdin_used+0x23>
  4012ac:	48 89 c7             	mov    %rax,%rdi
  4012af:	b8 00 00 00 00       	mov    $0x0,%eax
  4012b4:	e8 c7 fd ff ff       	call   401080 <printf@plt>

  //asm("movq %0, %%rsp" ::"rm"(scheduler->rsp): "rsp");  
         
 // }
  //printf("loop finished\n");
  return scheduler->rsp;
  4012b9:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4012bd:	48 8b 00             	mov    (%rax),%rax
}    
  4012c0:	c9                   	leave
  4012c1:	c3                   	ret

00000000004012c2 <pollthreads>:
// thread 2
if tasks.taskindex > threads[0].workindex:
  value = 2
*/

int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4012c2:	55                   	push   %rbp
  4012c3:	48 89 e5             	mov    %rsp,%rbp
  4012c6:	48 89 7d d8          	mov    %rdi,-0x28(%rbp)
  4012ca:	48 89 75 d0          	mov    %rsi,-0x30(%rbp)
  4012ce:	48 89 55 c8          	mov    %rdx,-0x38(%rbp)
  4012d2:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
  4012d6:	4c 89 45 b8          	mov    %r8,-0x48(%rbp)
  long WM = WRITE_MASK;
  4012da:	48 c7 45 f0 04 00 00 00 	movq   $0x4,-0x10(%rbp)
  long RM = READ_MASK;
  4012e2:	48 c7 45 f8 08 00 00 00 	movq   $0x8,-0x8(%rbp)
  for (int x = 1; x < data->threadsize ; x++) {
  4012ea:	c7 45 e8 01 00 00 00 	movl   $0x1,-0x18(%rbp)
  4012f1:	e9 9b 00 00 00       	jmp    401391 <pollthreads+0xcf>
  // printf("thread %d %ld\n", x, data->threads[x].ready);
    int mask = data->threads[1].readies[x];
  4012f6:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4012fa:	48 8b 40 30          	mov    0x30(%rax),%rax
  4012fe:	48 05 00 04 00 00    	add    $0x400,%rax
  401304:	48 8b 50 20          	mov    0x20(%rax),%rdx
  401308:	8b 45 e8             	mov    -0x18(%rbp),%eax
  40130b:	48 98                	cltq
  40130d:	48 c1 e0 02          	shl    $0x2,%rax
  401311:	48 01 d0             	add    %rdx,%rax
  401314:	8b 00                	mov    (%rax),%eax
  401316:	89 45 ec             	mov    %eax,-0x14(%rbp)
        //printf("pollpread? %ld %ld\n", mask, (mask & PREP_READ_MASK));
       // printf("pplreadmask? %ld %ld\n", mask, (mask & READ_MASK));
      //  printf("pollwritemask ? %ld %ld\n", mask, (mask & WRITE_MASK));
       // data->threads[x].newmask = 0;
        
        if ((mask & WM) == WM || mask == 0) {
  401319:	8b 45 ec             	mov    -0x14(%rbp),%eax
  40131c:	48 98                	cltq
  40131e:	48 23 45 f0          	and    -0x10(%rbp),%rax
  401322:	48 39 45 f0          	cmp    %rax,-0x10(%rbp)
  401326:	74 06                	je     40132e <pollthreads+0x6c>
  401328:	83 7d ec 00          	cmpl   $0x0,-0x14(%rbp)
  40132c:	75 25                	jne    401353 <pollthreads+0x91>
         //printf("found a writer\n");
          readywriters[(*writers)++] = x;
  40132e:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401332:	8b 00                	mov    (%rax),%eax
  401334:	8d 48 01             	lea    0x1(%rax),%ecx
  401337:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
  40133b:	89 0a                	mov    %ecx,(%rdx)
  40133d:	48 98                	cltq
  40133f:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401347:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
  40134b:	48 01 c2             	add    %rax,%rdx
  40134e:	8b 45 e8             	mov    -0x18(%rbp),%eax
  401351:	89 02                	mov    %eax,(%rdx)
        }
    if ((mask & RM) == RM || mask == 0) {
  401353:	8b 45 ec             	mov    -0x14(%rbp),%eax
  401356:	48 98                	cltq
  401358:	48 23 45 f8          	and    -0x8(%rbp),%rax
  40135c:	48 39 45 f8          	cmp    %rax,-0x8(%rbp)
  401360:	74 06                	je     401368 <pollthreads+0xa6>
  401362:	83 7d ec 00          	cmpl   $0x0,-0x14(%rbp)
  401366:	75 25                	jne    40138d <pollthreads+0xcb>
      readyreaders[(*readers)++] = x;
  401368:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
  40136c:	8b 00                	mov    (%rax),%eax
  40136e:	8d 48 01             	lea    0x1(%rax),%ecx
  401371:	48 8b 55 c0          	mov    -0x40(%rbp),%rdx
  401375:	89 0a                	mov    %ecx,(%rdx)
  401377:	48 98                	cltq
  401379:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401381:	48 8b 45 d0          	mov    -0x30(%rbp),%rax
  401385:	48 01 c2             	add    %rax,%rdx
  401388:	8b 45 e8             	mov    -0x18(%rbp),%eax
  40138b:	89 02                	mov    %eax,(%rdx)
  for (int x = 1; x < data->threadsize ; x++) {
  40138d:	83 45 e8 01          	addl   $0x1,-0x18(%rbp)
  401391:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401395:	8b 40 68             	mov    0x68(%rax),%eax
  401398:	39 45 e8             	cmp    %eax,-0x18(%rbp)
  40139b:	0f 8c 55 ff ff ff    	jl     4012f6 <pollthreads+0x34>
    // printf("found a reader\n");
    }
      }
  // printf("%d readers %d writers\n", *readers, *writers);
      
  return 0;
  4013a1:	b8 00 00 00 00       	mov    $0x0,%eax
}
  4013a6:	5d                   	pop    %rbp
  4013a7:	c3                   	ret

00000000004013a8 <findavailable>:


int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  4013a8:	55                   	push   %rbp
  4013a9:	48 89 e5             	mov    %rsp,%rbp
  4013ac:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  4013b0:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
  4013b4:	48 89 55 d8          	mov    %rdx,-0x28(%rbp)
  4013b8:	48 89 4d d0          	mov    %rcx,-0x30(%rbp)
  4013bc:	4c 89 45 c8          	mov    %r8,-0x38(%rbp)
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4013c0:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
  4013c7:	eb 64                	jmp    40142d <findavailable+0x85>
        
        if (data->freelist[x].available == FREE ) {
  4013c9:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4013cd:	48 8b 90 a0 00 00 00 	mov    0xa0(%rax),%rdx
  4013d4:	8b 45 fc             	mov    -0x4(%rbp),%eax
  4013d7:	48 98                	cltq
  4013d9:	48 c1 e0 05          	shl    $0x5,%rax
  4013dd:	48 01 d0             	add    %rdx,%rax
  4013e0:	8b 40 10             	mov    0x10(%rax),%eax
  4013e3:	83 f8 01             	cmp    $0x1,%eax
  4013e6:	75 41                	jne    401429 <findavailable+0x81>
          //printf("%d\n", *availableidx);
         available[*availableidx] = x;
  4013e8:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013ec:	8b 00                	mov    (%rax),%eax
  4013ee:	48 98                	cltq
  4013f0:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4013f8:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  4013fc:	48 01 c2             	add    %rax,%rdx
  4013ff:	8b 45 fc             	mov    -0x4(%rbp),%eax
  401402:	48 98                	cltq
  401404:	48 89 02             	mov    %rax,(%rdx)
         (*availableidx)++;
  401407:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  40140b:	8b 00                	mov    (%rax),%eax
  40140d:	8d 50 01             	lea    0x1(%rax),%edx
  401410:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401414:	89 10                	mov    %edx,(%rax)
         if ((*availableidx) == data->threadsize * 2) {
  401416:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  40141a:	8b 10                	mov    (%rax),%edx
  40141c:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401420:	8b 40 68             	mov    0x68(%rax),%eax
  401423:	01 c0                	add    %eax,%eax
  401425:	39 c2                	cmp    %eax,%edx
  401427:	74 20                	je     401449 <findavailable+0xa1>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401429:	83 45 fc 01          	addl   $0x1,-0x4(%rbp)
  40142d:	8b 45 fc             	mov    -0x4(%rbp),%eax
  401430:	48 63 d0             	movslq %eax,%rdx
  401433:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401437:	48 8b 80 b8 00 00 00 	mov    0xb8(%rax),%rax
  40143e:	48 83 c0 01          	add    $0x1,%rax
  401442:	48 39 c2             	cmp    %rax,%rdx
  401445:	7c 82                	jl     4013c9 <findavailable+0x21>
  401447:	eb 01                	jmp    40144a <findavailable+0xa2>
           break;
  401449:	90                   	nop
         }

         // printf("%d chunk is free\n", x);
        }
      }
      if (*availableidx == 0) {
  40144a:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  40144e:	8b 00                	mov    (%rax),%eax
  401450:	85 c0                	test   %eax,%eax
  401452:	75 07                	jne    40145b <findavailable+0xb3>
       //printf("no chunks avail\n");
        
        return 1;
  401454:	b8 01 00 00 00       	mov    $0x1,%eax
  401459:	eb 05                	jmp    401460 <findavailable+0xb8>
      }
  return 0;
  40145b:	b8 00 00 00 00       	mov    $0x0,%eax
}
  401460:	5d                   	pop    %rbp
  401461:	c3                   	ret

0000000000401462 <singlewriter3>:

int singlewriter3(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401462:	55                   	push   %rbp
  401463:	48 89 e5             	mov    %rsp,%rbp
  401466:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  40146a:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
  40146e:	48 89 55 d8          	mov    %rdx,-0x28(%rbp)
  401472:	48 89 4d d0          	mov    %rcx,-0x30(%rbp)
  int completed = 0;
  401476:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
   */



  //printf("%d %d\n", data->writecursor, data->writecursor % (data->threadsize - 1));
  if (data->writecursor != 0 && (data->writecursor % (data->threadsize - 1)) == 0) {
  40147d:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401481:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401487:	85 c0                	test   %eax,%eax
    //printf("writeepoch\n");
  } else {

  }

}
  401489:	90                   	nop
  40148a:	5d                   	pop    %rbp
  40148b:	c3                   	ret

000000000040148c <singlewriter2>:

int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40148c:	55                   	push   %rbp
  40148d:	48 89 e5             	mov    %rsp,%rbp
  401490:	48 83 ec 40          	sub    $0x40,%rsp
  401494:	48 89 7d d8          	mov    %rdi,-0x28(%rbp)
  401498:	48 89 75 d0          	mov    %rsi,-0x30(%rbp)
  40149c:	48 89 55 c8          	mov    %rdx,-0x38(%rbp)
  4014a0:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
  int completed = 0;
  4014a4:	c7 45 ec 00 00 00 00 	movl   $0x0,-0x14(%rbp)
   }
   */


//if ((__atomic_load_n(&data->readcursor, __ATOMIC_SEQ_CST) % data->threadsize) == 0) {
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  4014ab:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014af:	8b 80 00 02 00 00    	mov    0x200(%rax),%eax
  4014b5:	85 c0                	test   %eax,%eax
  4014b7:	0f 84 c7 00 00 00    	je     401584 <singlewriter2+0xf8>
  4014bd:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014c1:	8b 80 00 02 00 00    	mov    0x200(%rax),%eax
  4014c7:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  4014cb:	8b 52 68             	mov    0x68(%rdx),%edx
  4014ce:	8d 4a ff             	lea    -0x1(%rdx),%ecx
  4014d1:	99                   	cltd
  4014d2:	f7 f9                	idiv   %ecx
  4014d4:	89 d0                	mov    %edx,%eax
  4014d6:	85 c0                	test   %eax,%eax
  4014d8:	0f 85 a6 00 00 00    	jne    401584 <singlewriter2+0xf8>
   // data->readcursor = 0;
    //printf("readepoch\n");
    
  
        // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
        struct Data * thread = &data->threads[data->threadindex];
  4014de:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014e2:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4014e6:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014ea:	8b 40 64             	mov    0x64(%rax),%eax
  4014ed:	48 98                	cltq
  4014ef:	48 c1 e0 0a          	shl    $0xa,%rax
  4014f3:	48 01 d0             	add    %rdx,%rax
  4014f6:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4014fa:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4014fe:	48 8b 88 18 03 00 00 	mov    0x318(%rax),%rcx
  401505:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401509:	8b 80 24 03 00 00    	mov    0x324(%rax),%eax
  40150f:	48 63 d0             	movslq %eax,%rdx
  401512:	48 89 d0             	mov    %rdx,%rax
  401515:	48 01 c0             	add    %rax,%rax
  401518:	48 01 d0             	add    %rdx,%rax
  40151b:	48 c1 e0 04          	shl    $0x4,%rax
  40151f:	48 01 c8             	add    %rcx,%rax
  401522:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401526:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  40152a:	48 83 c0 08          	add    $0x8,%rax
  40152e:	48 89 c6             	mov    %rax,%rsi
  401531:	bf 04 00 00 00       	mov    $0x4,%edi
  401536:	e8 15 fb ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  40153b:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  40153f:	8b 80 24 03 00 00    	mov    0x324(%rax),%eax
  401545:	8d 50 01             	lea    0x1(%rax),%edx
  401548:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  40154c:	8b 88 20 03 00 00    	mov    0x320(%rax),%ecx
  401552:	89 d0                	mov    %edx,%eax
  401554:	99                   	cltd
  401555:	f7 f9                	idiv   %ecx
  401557:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  40155b:	89 90 24 03 00 00    	mov    %edx,0x324(%rax)
        epoch->kind = NEW_EPOCH;
  401561:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401565:	c7 40 20 01 00 00 00 	movl   $0x1,0x20(%rax)
        epoch->thread = data->threadindex;
  40156c:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401570:	8b 50 64             	mov    0x64(%rax),%edx
  401573:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401577:	89 10                	mov    %edx,(%rax)
        epoch->set = 1;
  401579:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  40157d:	c7 40 24 01 00 00 00 	movl   $0x1,0x24(%rax)
  } else {
    
  }

  
}
  401584:	90                   	nop
  401585:	c9                   	leave
  401586:	c3                   	ret

0000000000401587 <singlewriter>:



*/

int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401587:	55                   	push   %rbp
  401588:	48 89 e5             	mov    %rsp,%rbp
  40158b:	48 83 ec 70          	sub    $0x70,%rsp
  40158f:	48 89 7d a8          	mov    %rdi,-0x58(%rbp)
  401593:	48 89 75 a0          	mov    %rsi,-0x60(%rbp)
  401597:	48 89 55 98          	mov    %rdx,-0x68(%rbp)
  40159b:	48 89 4d 90          	mov    %rcx,-0x70(%rbp)
  40159f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4015a8:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  4015ac:	31 c0                	xor    %eax,%eax
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  4015ae:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015b2:	48 8b 40 30          	mov    0x30(%rax),%rax
  4015b6:	8b 80 0c 02 00 00    	mov    0x20c(%rax),%eax
  4015bc:	8d 50 01             	lea    0x1(%rax),%edx
  4015bf:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015c3:	8b 70 68             	mov    0x68(%rax),%esi
  4015c6:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015ca:	48 8b 48 30          	mov    0x30(%rax),%rcx
  4015ce:	89 d0                	mov    %edx,%eax
  4015d0:	99                   	cltd
  4015d1:	f7 fe                	idiv   %esi
  4015d3:	89 d0                	mov    %edx,%eax
  4015d5:	89 81 0c 02 00 00    	mov    %eax,0x20c(%rcx)
  int readers = 0;
  4015db:	c7 45 b0 00 00 00 00 	movl   $0x0,-0x50(%rbp)
  int writers = 0;
  4015e2:	c7 45 b4 00 00 00 00 	movl   $0x0,-0x4c(%rbp)
  int availableidx = 0;
  4015e9:	c7 45 b8 00 00 00 00 	movl   $0x0,-0x48(%rbp)
    readywriters[x] = x;
  }
  */
  //clock_gettime(CLOCK_MONOTONIC_RAW, &data->wstart);
  
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  4015f0:	48 8b 7d 90          	mov    -0x70(%rbp),%rdi
  4015f4:	48 8b 4d 98          	mov    -0x68(%rbp),%rcx
  4015f8:	48 8d 55 b8          	lea    -0x48(%rbp),%rdx
  4015fc:	48 8b 75 a0          	mov    -0x60(%rbp),%rsi
  401600:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401604:	49 89 f8             	mov    %rdi,%r8
  401607:	48 89 c7             	mov    %rax,%rdi
  40160a:	e8 99 fd ff ff       	call   4013a8 <findavailable>
  40160f:	89 45 cc             	mov    %eax,-0x34(%rbp)

//clock_gettime(CLOCK_MONOTONIC_RAW, &data->wavail);
  
  if (fill == 1) {
  401612:	83 7d cc 01          	cmpl   $0x1,-0x34(%rbp)
  401616:	75 0a                	jne    401622 <singlewriter+0x9b>
    return 1;
  401618:	b8 01 00 00 00       	mov    $0x1,%eax
  40161d:	e9 f9 02 00 00       	jmp    40191b <singlewriter+0x394>
  }
      
   //printf("buffers available %d\n", availableidx);
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401622:	48 8d 7d b4          	lea    -0x4c(%rbp),%rdi
  401626:	48 8d 4d b0          	lea    -0x50(%rbp),%rcx
  40162a:	48 8b 55 90          	mov    -0x70(%rbp),%rdx
  40162e:	48 8b 75 98          	mov    -0x68(%rbp),%rsi
  401632:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401636:	49 89 f8             	mov    %rdi,%r8
  401639:	48 89 c7             	mov    %rax,%rdi
  40163c:	e8 81 fc ff ff       	call   4012c2 <pollthreads>
      
  //clock_gettime(CLOCK_MONOTONIC_RAW, &data->wpoll);
      
      int assignedchunk = 0;
  401641:	c7 45 bc 00 00 00 00 	movl   $0x0,-0x44(%rbp)
      
        for (int x = 0; x < readers ; x++) {
  401648:	c7 45 c0 00 00 00 00 	movl   $0x0,-0x40(%rbp)
  40164f:	e9 10 01 00 00       	jmp    401764 <singlewriter+0x1dd>
          if (assignedchunk == availableidx) {
  401654:	8b 45 b8             	mov    -0x48(%rbp),%eax
  401657:	39 45 bc             	cmp    %eax,-0x44(%rbp)
  40165a:	0f 84 12 01 00 00    	je     401772 <singlewriter+0x1eb>
           // printf("not enough space readers\n");
                  break;
          }
          int thread = readyreaders[x];
  401660:	8b 45 c0             	mov    -0x40(%rbp),%eax
  401663:	48 98                	cltq
  401665:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  40166d:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  401671:	48 01 d0             	add    %rdx,%rax
  401674:	8b 00                	mov    (%rax),%eax
  401676:	89 45 d0             	mov    %eax,-0x30(%rbp)
          //printf("%d %p\n", thread, &data->freelist[available[assignedchunk]]);
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401679:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40167d:	48 8b 88 a0 00 00 00 	mov    0xa0(%rax),%rcx
  401684:	8b 45 bc             	mov    -0x44(%rbp),%eax
  401687:	8d 50 01             	lea    0x1(%rax),%edx
  40168a:	89 55 bc             	mov    %edx,-0x44(%rbp)
  40168d:	48 98                	cltq
  40168f:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  401697:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  40169b:	48 01 d0             	add    %rdx,%rax
  40169e:	48 8b 00             	mov    (%rax),%rax
  4016a1:	48 c1 e0 05          	shl    $0x5,%rax
  4016a5:	48 01 c8             	add    %rcx,%rax
  4016a8:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
          chunk->available = READING;
  4016ac:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016b0:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
          //printf("assign %p\n", chunk);


          data->threads[thread].reading = chunk;
  4016b7:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016bb:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016bf:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016c2:	48 98                	cltq
  4016c4:	48 c1 e0 0a          	shl    $0xa,%rax
  4016c8:	48 01 c2             	add    %rax,%rdx
  4016cb:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016cf:	48 89 82 a8 00 00 00 	mov    %rax,0xa8(%rdx)
          
          chunk->owner = thread;
  4016d6:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016da:	8b 55 d0             	mov    -0x30(%rbp),%edx
  4016dd:	89 50 14             	mov    %edx,0x14(%rax)
          int start = chunk->start;
  4016e0:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016e4:	48 8b 00             	mov    (%rax),%rax
  4016e7:	89 45 d4             	mov    %eax,-0x2c(%rbp)
          data->threads[thread].start = start;
  4016ea:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016ee:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016f2:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016f5:	48 98                	cltq
  4016f7:	48 c1 e0 0a          	shl    $0xa,%rax
  4016fb:	48 01 c2             	add    %rax,%rdx
  4016fe:	8b 45 d4             	mov    -0x2c(%rbp),%eax
  401701:	89 42 14             	mov    %eax,0x14(%rdx)
          
          int end = chunk->end;
  401704:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401708:	48 8b 40 08          	mov    0x8(%rax),%rax
  40170c:	89 45 d8             	mov    %eax,-0x28(%rbp)
          data->threads[thread].end = end;
  40170f:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401713:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401717:	8b 45 d0             	mov    -0x30(%rbp),%eax
  40171a:	48 98                	cltq
  40171c:	48 c1 e0 0a          	shl    $0xa,%rax
  401720:	48 01 c2             	add    %rax,%rdx
  401723:	8b 45 d8             	mov    -0x28(%rbp),%eax
  401726:	89 42 18             	mov    %eax,0x18(%rdx)
        // printf("reader giving %d between %ld and %ld\n", x, start, end);
        
         // clock_gettime(CLOCK_MONOTONIC_RAW, &data->main->works[start].created);
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401729:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40172d:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401731:	8b 45 d0             	mov    -0x30(%rbp),%eax
  401734:	48 98                	cltq
  401736:	48 c1 e0 0a          	shl    $0xa,%rax
  40173a:	48 01 d0             	add    %rdx,%rax
  40173d:	8b 90 c8 00 00 00    	mov    0xc8(%rax),%edx
  401743:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401747:	48 8b 48 30          	mov    0x30(%rax),%rcx
  40174b:	8b 45 d0             	mov    -0x30(%rbp),%eax
  40174e:	48 98                	cltq
  401750:	48 c1 e0 0a          	shl    $0xa,%rax
  401754:	48 01 c8             	add    %rcx,%rax
  401757:	83 ca 10             	or     $0x10,%edx
  40175a:	89 90 c8 00 00 00    	mov    %edx,0xc8(%rax)
        for (int x = 0; x < readers ; x++) {
  401760:	83 45 c0 01          	addl   $0x1,-0x40(%rbp)
  401764:	8b 45 b0             	mov    -0x50(%rbp),%eax
  401767:	39 45 c0             	cmp    %eax,-0x40(%rbp)
  40176a:	0f 8c e4 fe ff ff    	jl     401654 <singlewriter+0xcd>
  401770:	eb 01                	jmp    401773 <singlewriter+0x1ec>
                  break;
  401772:	90                   	nop
       // printf("read newmask ORed with %d\n", data->threads[thread].newmask);
        }
      
   for (int x = 0; x < writers ; x++) {
  401773:	c7 45 c4 00 00 00 00 	movl   $0x0,-0x3c(%rbp)
  40177a:	e9 10 01 00 00       	jmp    40188f <singlewriter+0x308>
                if (assignedchunk  == availableidx) {
  40177f:	8b 45 b8             	mov    -0x48(%rbp),%eax
  401782:	39 45 bc             	cmp    %eax,-0x44(%rbp)
  401785:	0f 84 12 01 00 00    	je     40189d <singlewriter+0x316>
                  
                 //printf("not enough space writer %d %d\n", assignedchunk, availableidx);
                  break;
                }
          int thread = readywriters[x];
  40178b:	8b 45 c4             	mov    -0x3c(%rbp),%eax
  40178e:	48 98                	cltq
  401790:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401798:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40179c:	48 01 d0             	add    %rdx,%rax
  40179f:	8b 00                	mov    (%rax),%eax
  4017a1:	89 45 dc             	mov    %eax,-0x24(%rbp)
     
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  4017a4:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4017a8:	48 8b 88 a0 00 00 00 	mov    0xa0(%rax),%rcx
  4017af:	8b 45 bc             	mov    -0x44(%rbp),%eax
  4017b2:	8d 50 01             	lea    0x1(%rax),%edx
  4017b5:	89 55 bc             	mov    %edx,-0x44(%rbp)
  4017b8:	48 98                	cltq
  4017ba:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4017c2:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  4017c6:	48 01 d0             	add    %rdx,%rax
  4017c9:	48 8b 00             	mov    (%rax),%rax
  4017cc:	48 c1 e0 05          	shl    $0x5,%rax
  4017d0:	48 01 c8             	add    %rcx,%rax
  4017d3:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
    
      chunk->available = WRITING;
  4017d7:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017db:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
          data->threads[thread].writing = chunk;
  4017e2:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4017e6:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4017ea:	8b 45 dc             	mov    -0x24(%rbp),%eax
  4017ed:	48 98                	cltq
  4017ef:	48 c1 e0 0a          	shl    $0xa,%rax
  4017f3:	48 01 c2             	add    %rax,%rdx
  4017f6:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017fa:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
          chunk->owner = thread;
  401801:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401805:	8b 55 dc             	mov    -0x24(%rbp),%edx
  401808:	89 50 14             	mov    %edx,0x14(%rax)
          int start = chunk->start;
  40180b:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  40180f:	48 8b 00             	mov    (%rax),%rax
  401812:	89 45 e0             	mov    %eax,-0x20(%rbp)
          data->threads[thread].publishstart = start;
  401815:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401819:	48 8b 50 30          	mov    0x30(%rax),%rdx
  40181d:	8b 45 dc             	mov    -0x24(%rbp),%eax
  401820:	48 98                	cltq
  401822:	48 c1 e0 0a          	shl    $0xa,%rax
  401826:	48 01 c2             	add    %rax,%rdx
  401829:	8b 45 e0             	mov    -0x20(%rbp),%eax
  40182c:	89 42 40             	mov    %eax,0x40(%rdx)
          
          int end = chunk->end;
  40182f:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401833:	48 8b 40 08          	mov    0x8(%rax),%rax
  401837:	89 45 e4             	mov    %eax,-0x1c(%rbp)
          data->threads[thread].publishend = end;
  40183a:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40183e:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401842:	8b 45 dc             	mov    -0x24(%rbp),%eax
  401845:	48 98                	cltq
  401847:	48 c1 e0 0a          	shl    $0xa,%rax
  40184b:	48 01 c2             	add    %rax,%rdx
  40184e:	8b 45 e4             	mov    -0x1c(%rbp),%eax
  401851:	89 42 44             	mov    %eax,0x44(%rdx)
        //  printf("writer giving %d between %ld and %ld\n", available[assignedchunk], start, end);
          // asm volatile ("sfence" ::: "memory");
     
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401854:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401858:	48 8b 50 30          	mov    0x30(%rax),%rdx
  40185c:	8b 45 dc             	mov    -0x24(%rbp),%eax
  40185f:	48 98                	cltq
  401861:	48 c1 e0 0a          	shl    $0xa,%rax
  401865:	48 01 d0             	add    %rdx,%rax
  401868:	8b 90 c8 00 00 00    	mov    0xc8(%rax),%edx
  40186e:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401872:	48 8b 48 30          	mov    0x30(%rax),%rcx
  401876:	8b 45 dc             	mov    -0x24(%rbp),%eax
  401879:	48 98                	cltq
  40187b:	48 c1 e0 0a          	shl    $0xa,%rax
  40187f:	48 01 c8             	add    %rcx,%rax
  401882:	83 ca 20             	or     $0x20,%edx
  401885:	89 90 c8 00 00 00    	mov    %edx,0xc8(%rax)
   for (int x = 0; x < writers ; x++) {
  40188b:	83 45 c4 01          	addl   $0x1,-0x3c(%rbp)
  40188f:	8b 45 b4             	mov    -0x4c(%rbp),%eax
  401892:	39 45 c4             	cmp    %eax,-0x3c(%rbp)
  401895:	0f 8c e4 fe ff ff    	jl     40177f <singlewriter+0x1f8>
  40189b:	eb 01                	jmp    40189e <singlewriter+0x317>
                  break;
  40189d:	90                   	nop
     //printf("write newmask ORed with %ld\n", data->threads[thread].newmask);
        
   } 
      for (int x = 0; x < data->threadsize ; x++) {
  40189e:	c7 45 c8 00 00 00 00 	movl   $0x0,-0x38(%rbp)
  4018a5:	eb 63                	jmp    40190a <singlewriter+0x383>
        if (data->threads[x].newmask != 0) {
  4018a7:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018ab:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4018af:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018b2:	48 98                	cltq
  4018b4:	48 c1 e0 0a          	shl    $0xa,%rax
  4018b8:	48 01 d0             	add    %rdx,%rax
  4018bb:	8b 80 c8 00 00 00    	mov    0xc8(%rax),%eax
  4018c1:	85 c0                	test   %eax,%eax
  4018c3:	74 41                	je     401906 <singlewriter+0x37f>
         // printf("thread %d %ld is now %ld\n", x, data->threads[x].ready, data->threads[x].newmask);
          data->threads[x].readies[x] = data->threads[x].newmask;
  4018c5:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018c9:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4018cd:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018d0:	48 98                	cltq
  4018d2:	48 c1 e0 0a          	shl    $0xa,%rax
  4018d6:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
  4018da:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018de:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4018e2:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018e5:	48 98                	cltq
  4018e7:	48 c1 e0 0a          	shl    $0xa,%rax
  4018eb:	48 01 d0             	add    %rdx,%rax
  4018ee:	48 8b 50 20          	mov    0x20(%rax),%rdx
  4018f2:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018f5:	48 98                	cltq
  4018f7:	48 c1 e0 02          	shl    $0x2,%rax
  4018fb:	48 01 c2             	add    %rax,%rdx
  4018fe:	8b 81 c8 00 00 00    	mov    0xc8(%rcx),%eax
  401904:	89 02                	mov    %eax,(%rdx)
      for (int x = 0; x < data->threadsize ; x++) {
  401906:	83 45 c8 01          	addl   $0x1,-0x38(%rbp)
  40190a:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40190e:	8b 40 68             	mov    0x68(%rax),%eax
  401911:	39 45 c8             	cmp    %eax,-0x38(%rbp)
  401914:	7c 91                	jl     4018a7 <singlewriter+0x320>
        
          
        }
      }
  // clock_gettime(CLOCK_MONOTONIC_RAW, &data->wassign);
  return 0;
  401916:	b8 00 00 00 00       	mov    $0x0,%eax
}
  40191b:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  40191f:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401928:	74 05                	je     40192f <singlewriter+0x3a8>
  40192a:	e8 41 f7 ff ff       	call   401070 <__stack_chk_fail@plt>
  40192f:	c9                   	leave
  401930:	c3                   	ret

0000000000401931 <threadwork>:

int * threadwork(struct Data * data) {
  401931:	55                   	push   %rbp
  401932:	48 89 e5             	mov    %rsp,%rbp
  401935:	48 81 ec 90 00 00 00 	sub    $0x90,%rsp
  40193c:	48 89 bd 78 ff ff ff 	mov    %rdi,-0x88(%rbp)
  401943:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40194c:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  401950:	31 c0                	xor    %eax,%eax
  int cursorlimit = 5;
  401952:	c7 45 a4 05 00 00 00 	movl   $0x5,-0x5c(%rbp)
  int epochsize = 1;
  401959:	c7 45 a8 01 00 00 00 	movl   $0x1,-0x58(%rbp)
  int epochwidth = 0xff;
  401960:	c7 45 ac ff 00 00 00 	movl   $0xff,-0x54(%rbp)

//printf("%ld %ld w%d\n", lastwrite, data->prevwrite, data->threadindex);
 //if (lastwrite != data->prevwrite) {
   
    uint64_t rsp;
    asm( "mov %%rsp, %0" : "=rm" ( rsp ));
  401967:	48 89 e0             	mov    %rsp,%rax
  40196a:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
  // switch_to(struct Coroutine * coroutines, int index
  //printf("table %x\n", (void *)data->coroutines);
 // printf("coroutine 3 %x\n", &data->coroutines[3]);
 // printf("coroutine eip %lx\n", data->coroutines[3].eip);
 // printf("coroutine data %lx\n", data->coroutines[3].data); 
  switch_to(data->coroutines, 3, data->scheduler);  
  40196e:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401975:	48 8b 90 c8 03 00 00 	mov    0x3c8(%rax),%rdx
  40197c:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401983:	48 8b 80 c0 03 00 00 	mov    0x3c0(%rax),%rax
  40198a:	be 03 00 00 00       	mov    $0x3,%esi
  40198f:	48 89 c7             	mov    %rax,%rdi
  401992:	e8 7c 1d 00 00       	call   403713 <switch_to>
  //printf("finished coroutine\n");
  //printf("%ld %ld w%d\n", lastwrite, data->prevwrite, data->threadindex);
     
       
clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401997:	48 8d 45 e0          	lea    -0x20(%rbp),%rax
  40199b:	48 89 c6             	mov    %rax,%rsi
  40199e:	bf 04 00 00 00       	mov    $0x4,%edi
  4019a3:	e8 a8 f6 ff ff       	call   401050 <clock_gettime@plt>
  //if (data->threadindex % 2 == 0) {
   
  if (data->running == 2) {
  4019a8:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019af:	8b 40 5c             	mov    0x5c(%rax),%eax
  4019b2:	83 f8 02             	cmp    $0x2,%eax
  4019b5:	0f 85 9f 01 00 00    	jne    401b5a <threadwork+0x229>
  //if (data ->threadindex == 0 ) {
      

   for (int x = 0 ; x < data->threadsize ; x++) {
  4019bb:	c7 45 98 00 00 00 00 	movl   $0x0,-0x68(%rbp)
  4019c2:	e9 50 01 00 00       	jmp    401b17 <threadwork+0x1e6>
      
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  4019c7:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019ce:	48 8b 40 28          	mov    0x28(%rax),%rax
  4019d2:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  4019d9:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019e0:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  4019e6:	c1 e0 07             	shl    $0x7,%eax
  4019e9:	48 98                	cltq
  4019eb:	48 c1 e0 03          	shl    $0x3,%rax
  4019ef:	48 01 d0             	add    %rdx,%rax
  4019f2:	48 8b 00             	mov    (%rax),%rax
  4019f5:	8b 55 a8             	mov    -0x58(%rbp),%edx
  4019f8:	48 63 fa             	movslq %edx,%rdi
  4019fb:	48 99                	cqto
  4019fd:	48 f7 ff             	idiv   %rdi
  401a00:	48 89 c2             	mov    %rax,%rdx
  401a03:	8b 45 ac             	mov    -0x54(%rbp),%eax
  401a06:	48 63 c8             	movslq %eax,%rcx
  401a09:	48 89 d0             	mov    %rdx,%rax
  401a0c:	48 99                	cqto
  401a0e:	48 f7 f9             	idiv   %rcx
  401a11:	48 89 d0             	mov    %rdx,%rax
  401a14:	89 45 9c             	mov    %eax,-0x64(%rbp)
    
      //  buffer = data->mystream << 24 | ( global << 16) | data->threadindex << 8 | data->writecursor % 0xff;
    int cursor = data->writecursor;
  401a17:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a1e:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401a24:	89 45 a0             	mov    %eax,-0x60(%rbp)
    //cursor = 0;
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  401a27:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a2e:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401a34:	c1 e0 18             	shl    $0x18,%eax
  401a37:	89 c2                	mov    %eax,%edx
  401a39:	8b 45 9c             	mov    -0x64(%rbp),%eax
  401a3c:	c1 e0 10             	shl    $0x10,%eax
  401a3f:	89 d6                	mov    %edx,%esi
  401a41:	09 c6                	or     %eax,%esi
  401a43:	8b 45 a0             	mov    -0x60(%rbp),%eax
  401a46:	48 63 d0             	movslq %eax,%rdx
  401a49:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401a50:	48 c1 ea 20          	shr    $0x20,%rdx
  401a54:	01 c2                	add    %eax,%edx
  401a56:	c1 fa 07             	sar    $0x7,%edx
  401a59:	89 c7                	mov    %eax,%edi
  401a5b:	c1 ff 1f             	sar    $0x1f,%edi
  401a5e:	89 d1                	mov    %edx,%ecx
  401a60:	29 f9                	sub    %edi,%ecx
  401a62:	89 ca                	mov    %ecx,%edx
  401a64:	c1 e2 08             	shl    $0x8,%edx
  401a67:	29 ca                	sub    %ecx,%edx
  401a69:	29 d0                	sub    %edx,%eax
  401a6b:	89 c1                	mov    %eax,%ecx
  401a6d:	89 f0                	mov    %esi,%eax
  401a6f:	09 c8                	or     %ecx,%eax
  401a71:	48 98                	cltq
  401a73:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
      buffer = data->mystream << 24 | ( (data->main->globalwrite[data->mystream * 128] / (data->threadsize)) % 0xff) << 16 | data->writecursor;
    }
    */
      // printf("%x\n", buffer);
        // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
  struct Data * thread = &data->threads[data->threadindex];
  401a77:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a7e:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401a82:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a89:	8b 40 64             	mov    0x64(%rax),%eax
  401a8c:	48 98                	cltq
  401a8e:	48 c1 e0 0a          	shl    $0xa,%rax
  401a92:	48 01 d0             	add    %rdx,%rax
  401a95:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
  epoch->buffer = buffer;
  epoch->set = 1;
  }
    
     // printf("alrrady filled\n");
  if (data->main->works[buffer] != -1) {
  401a99:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401aa0:	48 8b 40 28          	mov    0x28(%rax),%rax
  401aa4:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401aa8:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401aac:	48 01 d0             	add    %rdx,%rax
  401aaf:	0f b6 00             	movzbl (%rax),%eax
  401ab2:	3c ff                	cmp    $0xff,%al
  401ab4:	74 1a                	je     401ad0 <threadwork+0x19f>
    
    data->freq_writes++;
  401ab6:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401abd:	48 8b 40 50          	mov    0x50(%rax),%rax
  401ac1:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401ac5:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401acc:	48 89 50 50          	mov    %rdx,0x50(%rax)
  }
  data->main->works[buffer] = data->threadindex;
  401ad0:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ad7:	8b 50 64             	mov    0x64(%rax),%edx
  401ada:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ae1:	48 8b 40 28          	mov    0x28(%rax),%rax
  401ae5:	48 8b 48 70          	mov    0x70(%rax),%rcx
  401ae9:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401aed:	48 01 c8             	add    %rcx,%rax
  401af0:	88 10                	mov    %dl,(%rax)
         
         
  //  data->prevread = data->main->currentread;
     
     
    data->writecursor = (data->writecursor + 1) % cursorlimit;
  401af2:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401af9:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401aff:	83 c0 01             	add    $0x1,%eax
  401b02:	99                   	cltd
  401b03:	f7 7d a4             	idivl  -0x5c(%rbp)
  401b06:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b0d:	89 90 80 01 00 00    	mov    %edx,0x180(%rax)
   for (int x = 0 ; x < data->threadsize ; x++) {
  401b13:	83 45 98 01          	addl   $0x1,-0x68(%rbp)
  401b17:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b1e:	8b 40 68             	mov    0x68(%rax),%eax
  401b21:	39 45 98             	cmp    %eax,-0x68(%rbp)
  401b24:	0f 8c 9d fe ff ff    	jl     4019c7 <threadwork+0x96>
    
   }
      
    __atomic_fetch_add(&data->main->globalwrite[data->mystream * 128], 1, __ATOMIC_RELAXED);
  401b2a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b31:	48 8b 40 28          	mov    0x28(%rax),%rax
  401b35:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401b3c:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b43:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401b49:	c1 e0 07             	shl    $0x7,%eax
  401b4c:	48 98                	cltq
  401b4e:	48 c1 e0 03          	shl    $0x3,%rax
  401b52:	48 01 d0             	add    %rdx,%rax
  401b55:	f0 48 83 00 01       	lock addq $0x1,(%rax)
//}
  } 
  ///else {
  long thisgroup = data->main->globalwrite[data->mystream * 128] / epochsize;
  401b5a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b61:	48 8b 40 28          	mov    0x28(%rax),%rax
  401b65:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401b6c:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b73:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401b79:	c1 e0 07             	shl    $0x7,%eax
  401b7c:	48 98                	cltq
  401b7e:	48 c1 e0 03          	shl    $0x3,%rax
  401b82:	48 01 d0             	add    %rdx,%rax
  401b85:	48 8b 00             	mov    (%rax),%rax
  401b88:	8b 55 a8             	mov    -0x58(%rbp),%edx
  401b8b:	48 63 fa             	movslq %edx,%rdi
  401b8e:	48 99                	cqto
  401b90:	48 f7 ff             	idiv   %rdi
  401b93:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
  
  if (thisgroup != data->lastgroup) {
  401b97:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b9e:	8b 80 88 03 00 00    	mov    0x388(%rax),%eax
  401ba4:	48 98                	cltq
  401ba6:	48 39 45 c8          	cmp    %rax,-0x38(%rbp)
  401baa:	74 11                	je     401bbd <threadwork+0x28c>
     // printf("ndw group\n");
      data->writecursor = 0;
  401bac:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bb3:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
        epoch->thread = data->threadindex;
        epoch->stream = data->mystream;
        epoch->set = 1;
     }
   }
   data->lastgroup = thisgroup;
  401bbd:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
  401bc1:	89 c2                	mov    %eax,%edx
  401bc3:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bca:	89 90 88 03 00 00    	mov    %edx,0x388(%rax)
  //}
  
 //if (lastread != data->prevread)
 // {
   //printf("%ld  %ld r%d\n", data->main->currentread, data->prevread, data->threadindex);
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  401bd0:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bd7:	48 8b 40 28          	mov    0x28(%rax),%rax
  401bdb:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401be2:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401be9:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401bef:	c1 e0 07             	shl    $0x7,%eax
  401bf2:	48 98                	cltq
  401bf4:	48 c1 e0 03          	shl    $0x3,%rax
  401bf8:	48 01 d0             	add    %rdx,%rax
  401bfb:	48 8b 00             	mov    (%rax),%rax
  401bfe:	48 89 45 d0          	mov    %rax,-0x30(%rbp)
  
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
  401c02:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c09:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401c10:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c17:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401c1d:	48 63 d0             	movslq %eax,%rdx
  401c20:	48 89 d0             	mov    %rdx,%rax
  401c23:	48 01 c0             	add    %rax,%rax
  401c26:	48 01 d0             	add    %rdx,%rax
  401c29:	48 c1 e0 02          	shl    $0x2,%rax
  401c2d:	48 01 c8             	add    %rcx,%rax
  401c30:	8b 00                	mov    (%rax),%eax
  401c32:	48 98                	cltq
  401c34:	48 39 45 d0          	cmp    %rax,-0x30(%rbp)
  401c38:	7f 0b                	jg     401c45 <threadwork+0x314>
  401c3a:	48 83 7d d0 00       	cmpq   $0x0,-0x30(%rbp)
  401c3f:	0f 85 f9 02 00 00    	jne    401f3e <threadwork+0x60d>
    for (int x = 0; x < data->threadsize - 1; x++) {
  401c45:	c7 45 94 00 00 00 00 	movl   $0x0,-0x6c(%rbp)
  401c4c:	e9 d7 02 00 00       	jmp    401f28 <threadwork+0x5f7>
  // printf("%d\n", thiswrite);
   data->freq++;
  401c51:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c58:	48 8b 40 48          	mov    0x48(%rax),%rax
  401c5c:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401c60:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c67:	48 89 50 48          	mov    %rdx,0x48(%rax)
  
        
      
          
            
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  401c6b:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c72:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401c79:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c80:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401c86:	48 63 d0             	movslq %eax,%rdx
  401c89:	48 89 d0             	mov    %rdx,%rax
  401c8c:	48 01 c0             	add    %rax,%rax
  401c8f:	48 01 d0             	add    %rdx,%rax
  401c92:	48 c1 e0 02          	shl    $0x2,%rax
  401c96:	48 01 c8             	add    %rcx,%rax
  401c99:	8b 00                	mov    (%rax),%eax
  401c9b:	99                   	cltd
  401c9c:	f7 7d a8             	idivl  -0x58(%rbp)
  401c9f:	83 e8 01             	sub    $0x1,%eax
  401ca2:	99                   	cltd
  401ca3:	f7 7d ac             	idivl  -0x54(%rbp)
  401ca6:	89 d0                	mov    %edx,%eax
  401ca8:	48 98                	cltq
  401caa:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
        //long past = (((data->globalread[data->laststream]).global % epochwidth;
            if (past < 0) {
  401cae:	48 83 7d b0 00       	cmpq   $0x0,-0x50(%rbp)
  401cb3:	79 08                	jns    401cbd <threadwork+0x38c>
              past = 0;
  401cb5:	48 c7 45 b0 00 00 00 00 	movq   $0x0,-0x50(%rbp)
            }
            
            // long buffer = (data->threadindex << 24) | (data->main->globalwrite % 0xf) << 16 | (data->main->writecursor % 0xf);
        
       // buffer = data->laststream << 24 | (past << 16) | data->globalread[data->laststream].thread << 8, data->globalread[data->laststream].cursor % 0xff;
    int cursor = data->globalread[data->laststream].cursor;
  401cbd:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cc4:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401ccb:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cd2:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401cd8:	48 63 d0             	movslq %eax,%rdx
  401cdb:	48 89 d0             	mov    %rdx,%rax
  401cde:	48 01 c0             	add    %rax,%rax
  401ce1:	48 01 d0             	add    %rdx,%rax
  401ce4:	48 c1 e0 02          	shl    $0x2,%rax
  401ce8:	48 01 c8             	add    %rcx,%rax
  401ceb:	8b 40 04             	mov    0x4(%rax),%eax
  401cee:	89 45 8c             	mov    %eax,-0x74(%rbp)
    //cursor = 0;
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  401cf1:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cf8:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401cfe:	c1 e0 18             	shl    $0x18,%eax
  401d01:	48 63 d0             	movslq %eax,%rdx
  401d04:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
  401d08:	48 c1 e0 10          	shl    $0x10,%rax
  401d0c:	48 89 d6             	mov    %rdx,%rsi
  401d0f:	48 09 c6             	or     %rax,%rsi
  401d12:	8b 45 8c             	mov    -0x74(%rbp),%eax
  401d15:	48 63 d0             	movslq %eax,%rdx
  401d18:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401d1f:	48 c1 ea 20          	shr    $0x20,%rdx
  401d23:	01 c2                	add    %eax,%edx
  401d25:	c1 fa 07             	sar    $0x7,%edx
  401d28:	89 c1                	mov    %eax,%ecx
  401d2a:	c1 f9 1f             	sar    $0x1f,%ecx
  401d2d:	29 ca                	sub    %ecx,%edx
  401d2f:	89 d1                	mov    %edx,%ecx
  401d31:	c1 e1 08             	shl    $0x8,%ecx
  401d34:	29 d1                	sub    %edx,%ecx
  401d36:	29 c8                	sub    %ecx,%eax
  401d38:	89 c2                	mov    %eax,%edx
  401d3a:	48 63 c2             	movslq %edx,%rax
  401d3d:	48 09 f0             	or     %rsi,%rax
  401d40:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    access->cursor = data->globalread[data->laststream].cursor % 0xff;
    access->set = 1;
    data->cread = (data->cread + 1) % data->accesssize;
  }
    
    int thistream = data->laststream; 
  401d44:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d4b:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401d51:	89 45 90             	mov    %eax,-0x70(%rbp)
                // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
                //&data->threads[data->threadindex];

        // printf("%d\n", data->main->works[buffer]);
    
        if (data->main->works[buffer] != -1) {
  401d54:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d5b:	48 8b 40 28          	mov    0x28(%rax),%rax
  401d5f:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401d63:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401d67:	48 01 d0             	add    %rdx,%rax
  401d6a:	0f b6 00             	movzbl (%rax),%eax
  401d6d:	3c ff                	cmp    $0xff,%al
  401d6f:	74 39                	je     401daa <threadwork+0x479>
          data->successreads++;
  401d71:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d78:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  401d7f:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401d83:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d8a:	48 89 90 98 03 00 00 	mov    %rdx,0x398(%rax)
          
          data->main->works[buffer] = -1;
  401d91:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d98:	48 8b 40 28          	mov    0x28(%rax),%rax
  401d9c:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401da0:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401da4:	48 01 d0             	add    %rdx,%rax
  401da7:	c6 00 ff             	movb   $0xff,(%rax)
  
    
    
      
    
    if (data->globalread[thistream].cursor < cursorlimit) {
  401daa:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401db1:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401db8:	8b 45 90             	mov    -0x70(%rbp),%eax
  401dbb:	48 63 d0             	movslq %eax,%rdx
  401dbe:	48 89 d0             	mov    %rdx,%rax
  401dc1:	48 01 c0             	add    %rax,%rax
  401dc4:	48 01 d0             	add    %rdx,%rax
  401dc7:	48 c1 e0 02          	shl    $0x2,%rax
  401dcb:	48 01 c8             	add    %rcx,%rax
  401dce:	8b 40 04             	mov    0x4(%rax),%eax
  401dd1:	39 45 a4             	cmp    %eax,-0x5c(%rbp)
  401dd4:	7e 7c                	jle    401e52 <threadwork+0x521>
    
      data->globalread[thistream].global++;
  401dd6:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ddd:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401de4:	8b 45 90             	mov    -0x70(%rbp),%eax
  401de7:	48 63 d0             	movslq %eax,%rdx
  401dea:	48 89 d0             	mov    %rdx,%rax
  401ded:	48 01 c0             	add    %rax,%rax
  401df0:	48 01 d0             	add    %rdx,%rax
  401df3:	48 c1 e0 02          	shl    $0x2,%rax
  401df7:	48 01 c8             	add    %rcx,%rax
  401dfa:	8b 10                	mov    (%rax),%edx
  401dfc:	83 c2 01             	add    $0x1,%edx
  401dff:	89 10                	mov    %edx,(%rax)
        
        
      data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1);
  401e01:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e08:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401e0f:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e12:	48 63 d0             	movslq %eax,%rdx
  401e15:	48 89 d0             	mov    %rdx,%rax
  401e18:	48 01 c0             	add    %rax,%rax
  401e1b:	48 01 d0             	add    %rdx,%rax
  401e1e:	48 c1 e0 02          	shl    $0x2,%rax
  401e22:	48 01 c8             	add    %rcx,%rax
  401e25:	8b 48 04             	mov    0x4(%rax),%ecx
  401e28:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e2f:	48 8b b0 48 03 00 00 	mov    0x348(%rax),%rsi
  401e36:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e39:	48 63 d0             	movslq %eax,%rdx
  401e3c:	48 89 d0             	mov    %rdx,%rax
  401e3f:	48 01 c0             	add    %rax,%rax
  401e42:	48 01 d0             	add    %rdx,%rax
  401e45:	48 c1 e0 02          	shl    $0x2,%rax
  401e49:	48 01 f0             	add    %rsi,%rax
  401e4c:	8d 51 01             	lea    0x1(%rcx),%edx
  401e4f:	89 50 04             	mov    %edx,0x4(%rax)
      
      }
    
    if (data->globalread[thistream].cursor == cursorlimit) {
  401e52:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e59:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401e60:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e63:	48 63 d0             	movslq %eax,%rdx
  401e66:	48 89 d0             	mov    %rdx,%rax
  401e69:	48 01 c0             	add    %rax,%rax
  401e6c:	48 01 d0             	add    %rdx,%rax
  401e6f:	48 c1 e0 02          	shl    $0x2,%rax
  401e73:	48 01 c8             	add    %rcx,%rax
  401e76:	8b 40 04             	mov    0x4(%rax),%eax
  401e79:	39 45 a4             	cmp    %eax,-0x5c(%rbp)
  401e7c:	75 48                	jne    401ec6 <threadwork+0x595>
      
      data->laststream = (data->laststream + 1);
  401e7e:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e85:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401e8b:	8d 50 01             	lea    0x1(%rax),%edx
  401e8e:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e95:	89 90 90 03 00 00    	mov    %edx,0x390(%rax)
     // data->globalread[thistream].global++;
data->globalread[thistream].cursor = 0;
  401e9b:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ea2:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401ea9:	8b 45 90             	mov    -0x70(%rbp),%eax
  401eac:	48 63 d0             	movslq %eax,%rdx
  401eaf:	48 89 d0             	mov    %rdx,%rax
  401eb2:	48 01 c0             	add    %rax,%rax
  401eb5:	48 01 d0             	add    %rdx,%rax
  401eb8:	48 c1 e0 02          	shl    $0x2,%rax
  401ebc:	48 01 c8             	add    %rcx,%rax
  401ebf:	c7 40 04 00 00 00 00 	movl   $0x0,0x4(%rax)
    }
    
    if (data->laststream == data->mystream) {
  401ec6:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ecd:	8b 90 90 03 00 00    	mov    0x390(%rax),%edx
  401ed3:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401eda:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401ee0:	39 c2                	cmp    %eax,%edx
  401ee2:	75 1d                	jne    401f01 <threadwork+0x5d0>
      data->laststream = data->laststream + 1;
  401ee4:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401eeb:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401ef1:	8d 50 01             	lea    0x1(%rax),%edx
  401ef4:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401efb:	89 90 90 03 00 00    	mov    %edx,0x390(%rax)
     // data->globalread[data->laststream].cursor = 0;
    }
    if (data->laststream == 5) {
  401f01:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401f08:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401f0e:	83 f8 05             	cmp    $0x5,%eax
  401f11:	75 11                	jne    401f24 <threadwork+0x5f3>
       data->laststream = 1;
  401f13:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401f1a:	c7 80 90 03 00 00 01 00 00 00 	movl   $0x1,0x390(%rax)
    for (int x = 0; x < data->threadsize - 1; x++) {
  401f24:	83 45 94 01          	addl   $0x1,-0x6c(%rbp)
  401f28:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401f2f:	8b 40 68             	mov    0x68(%rax),%eax
  401f32:	83 e8 01             	sub    $0x1,%eax
  401f35:	39 45 94             	cmp    %eax,-0x6c(%rbp)
  401f38:	0f 8c 13 fd ff ff    	jl     401c51 <threadwork+0x320>
      
     //asm volatile ("sfence" ::: "memory");
  
      
       
}
  401f3e:	90                   	nop
  401f3f:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  401f43:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401f4c:	74 05                	je     401f53 <threadwork+0x622>
  401f4e:	e8 1d f1 ff ff       	call   401070 <__stack_chk_fail@plt>
  401f53:	c9                   	leave
  401f54:	c3                   	ret

0000000000401f55 <work2>:

void * work2(void * arg) {
  401f55:	55                   	push   %rbp
  401f56:	48 89 e5             	mov    %rsp,%rbp
  401f59:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  struct Data *data = (struct Data*) arg;
  401f5d:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401f61:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  while (data->running == 1) {
  401f65:	eb 14                	jmp    401f7b <work2+0x26>
    asm volatile ("" ::: "memory");
      data->freq++;
  401f67:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f6b:	48 8b 40 48          	mov    0x48(%rax),%rax
  401f6f:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401f73:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f77:	48 89 50 48          	mov    %rdx,0x48(%rax)
  while (data->running == 1) {
  401f7b:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f7f:	8b 40 5c             	mov    0x5c(%rax),%eax
  401f82:	83 f8 01             	cmp    $0x1,%eax
  401f85:	74 e0                	je     401f67 <work2+0x12>
  }
  
}
  401f87:	90                   	nop
  401f88:	5d                   	pop    %rbp
  401f89:	c3                   	ret

0000000000401f8a <work>:

void * work(void * arg) {
  401f8a:	55                   	push   %rbp
  401f8b:	48 89 e5             	mov    %rsp,%rbp
  401f8e:	48 83 ec 50          	sub    $0x50,%rsp
  401f92:	48 89 7d b8          	mov    %rdi,-0x48(%rbp)

  
  int writers;
  int readers;
  struct Data *data = (struct Data*) arg;
  401f96:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401f9a:	48 89 45 e0          	mov    %rax,-0x20(%rbp)
  printf("started thread %d\n", data->threadindex);
  401f9e:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fa2:	8b 40 64             	mov    0x64(%rax),%eax
  401fa5:	89 c6                	mov    %eax,%esi
  401fa7:	48 8d 05 90 20 00 00 	lea    0x2090(%rip),%rax        # 40403e <_IO_stdin_used+0x3e>
  401fae:	48 89 c7             	mov    %rax,%rdi
  401fb1:	b8 00 00 00 00       	mov    $0x0,%eax
  401fb6:	e8 c5 f0 ff ff       	call   401080 <printf@plt>
  
  
  int found = 0;
  401fbb:	c7 45 c8 00 00 00 00 	movl   $0x0,-0x38(%rbp)
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  401fc2:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fc6:	8b 40 64             	mov    0x64(%rax),%eax
  401fc9:	8d 50 01             	lea    0x1(%rax),%edx
  401fcc:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fd0:	8b 48 68             	mov    0x68(%rax),%ecx
  401fd3:	89 d0                	mov    %edx,%eax
  401fd5:	99                   	cltd
  401fd6:	f7 f9                	idiv   %ecx
  401fd8:	89 55 cc             	mov    %edx,-0x34(%rbp)
  int innerfind = 0;
  401fdb:	c7 45 d0 00 00 00 00 	movl   $0x0,-0x30(%rbp)
  
  
  
  
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  401fe2:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fe6:	48 8b 80 b8 00 00 00 	mov    0xb8(%rax),%rax
  401fed:	48 83 c0 01          	add    $0x1,%rax
  401ff1:	be 08 00 00 00       	mov    $0x8,%esi
  401ff6:	48 89 c7             	mov    %rax,%rdi
  401ff9:	e8 d2 f0 ff ff       	call   4010d0 <calloc@plt>
  401ffe:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  402002:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402006:	8b 40 68             	mov    0x68(%rax),%eax
  402009:	48 98                	cltq
  40200b:	be 04 00 00 00       	mov    $0x4,%esi
  402010:	48 89 c7             	mov    %rax,%rdi
  402013:	e8 b8 f0 ff ff       	call   4010d0 <calloc@plt>
  402018:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
  int * readywriters = calloc(data->threadsize, sizeof(int));
  40201c:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402020:	8b 40 68             	mov    0x68(%rax),%eax
  402023:	48 98                	cltq
  402025:	be 04 00 00 00       	mov    $0x4,%esi
  40202a:	48 89 c7             	mov    %rax,%rdi
  40202d:	e8 9e f0 ff ff       	call   4010d0 <calloc@plt>
  402032:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  
  
  int stop = 0;
  402036:	c7 45 d4 00 00 00 00 	movl   $0x0,-0x2c(%rbp)
  while (data->running > 0)  {
  40203d:	eb 25                	jmp    402064 <work+0xda>
    writers = 0;
  40203f:	c7 45 d8 00 00 00 00 	movl   $0x0,-0x28(%rbp)
    readers = 0;
  402046:	c7 45 dc 00 00 00 00 	movl   $0x0,-0x24(%rbp)
    stop = 0;
  40204d:	c7 45 d4 00 00 00 00 	movl   $0x0,-0x2c(%rbp)
    asm volatile ("":"=m" (data->running)::);
  402054:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
   // printf("write cycle\n");
    //memset(available, -1, data->threadsize);

      threadwork(data);
  402058:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  40205c:	48 89 c7             	mov    %rax,%rdi
  40205f:	e8 cd f8 ff ff       	call   401931 <threadwork>
  while (data->running > 0)  {
  402064:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402068:	8b 40 5c             	mov    0x5c(%rax),%eax
  40206b:	85 c0                	test   %eax,%eax
  40206d:	7f d0                	jg     40203f <work+0xb5>
        for (int x = 0 ; x < data->worksize; x++) {
          data->main->works[x].available = 1;
        }
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
  40206f:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402073:	8b 40 64             	mov    0x64(%rax),%eax
  402076:	89 c6                	mov    %eax,%esi
  402078:	48 8d 05 d2 1f 00 00 	lea    0x1fd2(%rip),%rax        # 404051 <_IO_stdin_used+0x51>
  40207f:	48 89 c7             	mov    %rax,%rdi
  402082:	b8 00 00 00 00       	mov    $0x0,%eax
  402087:	e8 f4 ef ff ff       	call   401080 <printf@plt>
}
  40208c:	90                   	nop
  40208d:	c9                   	leave
  40208e:	c3                   	ret

000000000040208f <main>:

int main(int argc, char **argv) {
  40208f:	55                   	push   %rbp
  402090:	48 89 e5             	mov    %rsp,%rbp
  402093:	53                   	push   %rbx
  402094:	48 81 ec 78 01 00 00 	sub    $0x178,%rsp
  40209b:	89 bd 8c fe ff ff    	mov    %edi,-0x174(%rbp)
  4020a1:	48 89 b5 80 fe ff ff 	mov    %rsi,-0x180(%rbp)
  4020a8:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4020b1:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  4020b5:	31 c0                	xor    %eax,%eax
  int debug = 0;
  4020b7:	c7 85 a0 fe ff ff 00 00 00 00 	movl   $0x0,-0x160(%rbp)
  int seconds = DURATION;
  4020c1:	c7 85 a4 fe ff ff 01 00 00 00 	movl   $0x1,-0x15c(%rbp)
  int worksize_each = 1;
  4020cb:	c7 85 94 fe ff ff 01 00 00 00 	movl   $0x1,-0x16c(%rbp)
  int threadsize = THREADS;
  4020d5:	c7 85 98 fe ff ff 0f 00 00 00 	movl   $0xf,-0x168(%rbp)
  
  int workers = threadsize - 1;
  4020df:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4020e5:	83 e8 01             	sub    $0x1,%eax
  4020e8:	89 85 9c fe ff ff    	mov    %eax,-0x164(%rbp)
  printf("read mask %d\n", READ_MASK);
  4020ee:	be 08 00 00 00       	mov    $0x8,%esi
  4020f3:	48 8d 05 67 1f 00 00 	lea    0x1f67(%rip),%rax        # 404061 <_IO_stdin_used+0x61>
  4020fa:	48 89 c7             	mov    %rax,%rdi
  4020fd:	b8 00 00 00 00       	mov    $0x0,%eax
  402102:	e8 79 ef ff ff       	call   401080 <printf@plt>
  printf("write mask %d\n", WRITE_MASK);
  402107:	be 04 00 00 00       	mov    $0x4,%esi
  40210c:	48 8d 05 5c 1f 00 00 	lea    0x1f5c(%rip),%rax        # 40406f <_IO_stdin_used+0x6f>
  402113:	48 89 c7             	mov    %rax,%rdi
  402116:	b8 00 00 00 00       	mov    $0x0,%eax
  40211b:	e8 60 ef ff ff       	call   401080 <printf@plt>
  printf("prepwrite mask %d\n", PREP_WRITE_MASK);
  402120:	be 20 00 00 00       	mov    $0x20,%esi
  402125:	48 8d 05 52 1f 00 00 	lea    0x1f52(%rip),%rax        # 40407e <_IO_stdin_used+0x7e>
  40212c:	48 89 c7             	mov    %rax,%rdi
  40212f:	b8 00 00 00 00       	mov    $0x0,%eax
  402134:	e8 47 ef ff ff       	call   401080 <printf@plt>
  printf("Starting %d workers\n", threadsize);
  402139:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40213f:	89 c6                	mov    %eax,%esi
  402141:	48 8d 05 49 1f 00 00 	lea    0x1f49(%rip),%rax        # 404091 <_IO_stdin_used+0x91>
  402148:	48 89 c7             	mov    %rax,%rdi
  40214b:	b8 00 00 00 00       	mov    $0x0,%eax
  402150:	e8 2b ef ff ff       	call   401080 <printf@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  402155:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40215b:	48 98                	cltq
  40215d:	be 08 00 00 00       	mov    $0x8,%esi
  402162:	48 89 c7             	mov    %rax,%rdi
  402165:	e8 66 ef ff ff       	call   4010d0 <calloc@plt>
  40216a:	48 89 85 18 ff ff ff 	mov    %rax,-0xe8(%rbp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  402171:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402177:	48 98                	cltq
  402179:	be 38 00 00 00       	mov    $0x38,%esi
  40217e:	48 89 c7             	mov    %rax,%rdi
  402181:	e8 4a ef ff ff       	call   4010d0 <calloc@plt>
  402186:	48 89 85 f0 fe ff ff 	mov    %rax,-0x110(%rbp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40218d:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402193:	48 98                	cltq
  402195:	48 c1 e0 0a          	shl    $0xa,%rax
  402199:	48 89 c6             	mov    %rax,%rsi
  40219c:	bf 01 00 00 00       	mov    $0x1,%edi
  4021a1:	e8 2a ef ff ff       	call   4010d0 <calloc@plt>
  4021a6:	48 89 85 f8 fe ff ff 	mov    %rax,-0x108(%rbp)
  
  long offset = 0;
  4021ad:	48 c7 85 00 ff ff ff 00 00 00 00 	movq   $0x0,-0x100(%rbp)
  long chunkslen = 0xffffffff;
  4021b8:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
  4021bd:	48 89 85 08 ff ff ff 	mov    %rax,-0xf8(%rbp)
  long worksize = chunkslen * worksize_each;
  4021c4:	8b 85 94 fe ff ff    	mov    -0x16c(%rbp),%eax
  4021ca:	48 98                	cltq
  4021cc:	48 8b 95 08 ff ff ff 	mov    -0xf8(%rbp),%rdx
  4021d3:	48 0f af c2          	imul   %rdx,%rax
  4021d7:	48 89 85 10 ff ff ff 	mov    %rax,-0xf0(%rbp)
  int buckets = worksize / threadsize;
  4021de:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4021e4:	48 63 d8             	movslq %eax,%rbx
  4021e7:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  4021ee:	48 99                	cqto
  4021f0:	48 f7 fb             	idiv   %rbx
  4021f3:	89 85 90 fe ff ff    	mov    %eax,-0x170(%rbp)
  long chunksize = ceil((double) worksize / (double) chunkslen);
  4021f9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4021fd:	f2 48 0f 2a 85 10 ff ff ff 	cvtsi2sdq -0xf0(%rbp),%xmm0
  402206:	66 0f ef c9          	pxor   %xmm1,%xmm1
  40220a:	f2 48 0f 2a 8d 08 ff ff ff 	cvtsi2sdq -0xf8(%rbp),%xmm1
  402213:	f2 0f 5e c1          	divsd  %xmm1,%xmm0
  402217:	66 48 0f 7e c0       	movq   %xmm0,%rax
  40221c:	66 48 0f 6e c0       	movq   %rax,%xmm0
  402221:	e8 fa ee ff ff       	call   401120 <ceil@plt>
  402226:	f2 48 0f 2c c0       	cvttsd2si %xmm0,%rax
  40222b:	48 89 85 38 ff ff ff 	mov    %rax,-0xc8(%rbp)
  char *works = calloc(worksize, sizeof(char));
  402232:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  402239:	be 01 00 00 00       	mov    $0x1,%esi
  40223e:	48 89 c7             	mov    %rax,%rdi
  402241:	e8 8a ee ff ff       	call   4010d0 <calloc@plt>
  402246:	48 89 85 40 ff ff ff 	mov    %rax,-0xc0(%rbp)
  memset(works, -1, worksize);
  40224d:	48 8b 95 10 ff ff ff 	mov    -0xf0(%rbp),%rdx
  402254:	48 8b 85 40 ff ff ff 	mov    -0xc0(%rbp),%rax
  40225b:	be ff ff ff ff       	mov    $0xffffffff,%esi
  402260:	48 89 c7             	mov    %rax,%rdi
  402263:	e8 58 ee ff ff       	call   4010c0 <memset@plt>
  printf("Buffer size %ld\n", worksize);
  402268:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  40226f:	48 89 c6             	mov    %rax,%rsi
  402272:	48 8d 05 2d 1e 00 00 	lea    0x1e2d(%rip),%rax        # 4040a6 <_IO_stdin_used+0xa6>
  402279:	48 89 c7             	mov    %rax,%rdi
  40227c:	b8 00 00 00 00       	mov    $0x0,%eax
  402281:	e8 fa ed ff ff       	call   401080 <printf@plt>
  int chunkindex = 0;
  402286:	c7 85 d4 fe ff ff 00 00 00 00 	movl   $0x0,-0x12c(%rbp)
  int * readcursors = calloc(threadsize, sizeof(int));
  402290:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402296:	48 98                	cltq
  402298:	be 04 00 00 00       	mov    $0x4,%esi
  40229d:	48 89 c7             	mov    %rax,%rdi
  4022a0:	e8 2b ee ff ff       	call   4010d0 <calloc@plt>
  4022a5:	48 89 85 48 ff ff ff 	mov    %rax,-0xb8(%rbp)
  int * writecursors = calloc(threadsize, sizeof(int));
  4022ac:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4022b2:	48 98                	cltq
  4022b4:	be 04 00 00 00       	mov    $0x4,%esi
  4022b9:	48 89 c7             	mov    %rax,%rdi
  4022bc:	e8 0f ee ff ff       	call   4010d0 <calloc@plt>
  4022c1:	48 89 85 50 ff ff ff 	mov    %rax,-0xb0(%rbp)
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4022c8:	be 20 00 00 00       	mov    $0x20,%esi
  4022cd:	bf 64 00 00 00       	mov    $0x64,%edi
  4022d2:	e8 f9 ed ff ff       	call   4010d0 <calloc@plt>
  4022d7:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)

printf("offset %ld\n", offset);
  4022de:	48 8b 85 00 ff ff ff 	mov    -0x100(%rbp),%rax
  4022e5:	48 89 c6             	mov    %rax,%rsi
  4022e8:	48 8d 05 c8 1d 00 00 	lea    0x1dc8(%rip),%rax        # 4040b7 <_IO_stdin_used+0xb7>
  4022ef:	48 89 c7             	mov    %rax,%rdi
  4022f2:	b8 00 00 00 00       	mov    $0x0,%eax
  4022f7:	e8 84 ed ff ff       	call   401080 <printf@plt>
  
printf("%ld chunks\n", chunkslen);
  4022fc:	48 8b 85 08 ff ff ff 	mov    -0xf8(%rbp),%rax
  402303:	48 89 c6             	mov    %rax,%rsi
  402306:	48 8d 05 b6 1d 00 00 	lea    0x1db6(%rip),%rax        # 4040c3 <_IO_stdin_used+0xc3>
  40230d:	48 89 c7             	mov    %rax,%rdi
  402310:	b8 00 00 00 00       	mov    $0x0,%eax
  402315:	e8 66 ed ff ff       	call   401080 <printf@plt>
 // for (int i = 0; i < worksize; i++) {
   // works[i].taskindex = 2;
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  40231a:	c7 85 c4 fe ff ff 00 00 00 00 	movl   $0x0,-0x13c(%rbp)
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  402324:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40232a:	48 98                	cltq
  40232c:	be 04 00 00 00       	mov    $0x4,%esi
  402331:	48 89 c7             	mov    %rax,%rdi
  402334:	e8 97 ed ff ff       	call   4010d0 <calloc@plt>
  402339:	48 89 85 60 ff ff ff 	mov    %rax,-0xa0(%rbp)
  
  long * globalwrite;
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  402340:	48 8d 85 e0 fe ff ff 	lea    -0x120(%rbp),%rax
  402347:	ba 00 02 00 00       	mov    $0x200,%edx
  40234c:	be 80 00 00 00       	mov    $0x80,%esi
  402351:	48 89 c7             	mov    %rax,%rdi
  402354:	e8 a7 ed ff ff       	call   401100 <posix_memalign@plt>
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  402359:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40235f:	48 98                	cltq
  402361:	be 0c 00 00 00       	mov    $0xc,%esi
  402366:	48 89 c7             	mov    %rax,%rdi
  402369:	e8 62 ed ff ff       	call   4010d0 <calloc@plt>
  40236e:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
  data[0].works = works;
  402375:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40237c:	48 8b 95 40 ff ff ff 	mov    -0xc0(%rbp),%rdx
  402383:	48 89 50 70          	mov    %rdx,0x70(%rax)
  int accesssize = 100000000;
  402387:	c7 85 d8 fe ff ff 00 e1 f5 05 	movl   $0x5f5e100,-0x128(%rbp)
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  402391:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  402397:	48 98                	cltq
  402399:	be 14 00 00 00       	mov    $0x14,%esi
  40239e:	48 89 c7             	mov    %rax,%rdi
  4023a1:	e8 2a ed ff ff       	call   4010d0 <calloc@plt>
  4023a6:	48 89 85 70 ff ff ff 	mov    %rax,-0x90(%rbp)
  struct Access * writes = calloc(accesssize, sizeof(struct Access));
  4023ad:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  4023b3:	48 98                	cltq
  4023b5:	be 14 00 00 00       	mov    $0x14,%esi
  4023ba:	48 89 c7             	mov    %rax,%rdi
  4023bd:	e8 0e ed ff ff       	call   4010d0 <calloc@plt>
  4023c2:	48 89 85 78 ff ff ff 	mov    %rax,-0x88(%rbp)

  

  
  
  for (int x = 0; x < threadsize ; x++) {
  4023c9:	c7 85 c8 fe ff ff 00 00 00 00 	movl   $0x0,-0x138(%rbp)
  4023d3:	e9 fb 06 00 00       	jmp    402ad3 <main+0xa44>
    
    struct Coroutine * cos = calloc(10, sizeof(struct Coroutine));
  4023d8:	be 20 00 00 00       	mov    $0x20,%esi
  4023dd:	bf 0a 00 00 00       	mov    $0xa,%edi
  4023e2:	e8 e9 ec ff ff       	call   4010d0 <calloc@plt>
  4023e7:	48 89 45 a0          	mov    %rax,-0x60(%rbp)
    
    data[x].coroutines = cos;
  4023eb:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4023f1:	48 98                	cltq
  4023f3:	48 c1 e0 0a          	shl    $0xa,%rax
  4023f7:	48 89 c2             	mov    %rax,%rdx
  4023fa:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402401:	48 01 c2             	add    %rax,%rdx
  402404:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  402408:	48 89 82 c0 03 00 00 	mov    %rax,0x3c0(%rdx)
    for (int y = 0; y < 10; y++ ) {
  40240f:	c7 85 cc fe ff ff 00 00 00 00 	movl   $0x0,-0x134(%rbp)
  402419:	e9 9e 00 00 00       	jmp    4024bc <main+0x42d>
      char * stack;
      posix_memalign((void **)&stack, 16, 8016);
  40241e:	48 8d 45 d0          	lea    -0x30(%rbp),%rax
  402422:	ba 50 1f 00 00       	mov    $0x1f50,%edx
  402427:	be 10 00 00 00       	mov    $0x10,%esi
  40242c:	48 89 c7             	mov    %rax,%rdi
  40242f:	e8 cc ec ff ff       	call   401100 <posix_memalign@plt>
      
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
  402434:	be 04 00 00 00       	mov    $0x4,%esi
  402439:	bf 01 00 00 00       	mov    $0x1,%edi
  40243e:	e8 8d ec ff ff       	call   4010d0 <calloc@plt>
  402443:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
      cos[y].data = codata; 
  402447:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  40244d:	48 98                	cltq
  40244f:	48 c1 e0 05          	shl    $0x5,%rax
  402453:	48 89 c2             	mov    %rax,%rdx
  402456:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  40245a:	48 01 c2             	add    %rax,%rdx
  40245d:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  402461:	48 89 42 18          	mov    %rax,0x18(%rdx)
      codata->running = 1;
  402465:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  402469:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
      cos[y].eip = (uint64_t)coroutine_func;
  40246f:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  402475:	48 98                	cltq
  402477:	48 c1 e0 05          	shl    $0x5,%rax
  40247b:	48 89 c2             	mov    %rax,%rdx
  40247e:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  402482:	48 01 d0             	add    %rdx,%rax
  402485:	48 c7 c2 1d 12 40 00 	mov    $0x40121d,%rdx
  40248c:	48 89 50 10          	mov    %rdx,0x10(%rax)
      cos[y].rsp = stack + 8016;
  402490:	48 8b 45 d0          	mov    -0x30(%rbp),%rax
  402494:	48 8d 90 50 1f 00 00 	lea    0x1f50(%rax),%rdx
  40249b:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  4024a1:	48 98                	cltq
  4024a3:	48 c1 e0 05          	shl    $0x5,%rax
  4024a7:	48 89 c1             	mov    %rax,%rcx
  4024aa:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  4024ae:	48 01 c8             	add    %rcx,%rax
  4024b1:	48 89 50 08          	mov    %rdx,0x8(%rax)
    for (int y = 0; y < 10; y++ ) {
  4024b5:	83 85 cc fe ff ff 01 	addl   $0x1,-0x134(%rbp)
  4024bc:	83 bd cc fe ff ff 09 	cmpl   $0x9,-0x134(%rbp)
  4024c3:	0f 8e 55 ff ff ff    	jle    40241e <main+0x38f>
    }
    struct Scheduler * scheduler = calloc(1, sizeof(struct Scheduler));
  4024c9:	be 08 00 00 00       	mov    $0x8,%esi
  4024ce:	bf 01 00 00 00       	mov    $0x1,%edi
  4024d3:	e8 f8 eb ff ff       	call   4010d0 <calloc@plt>
  4024d8:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
    data[x].scheduler = scheduler;   
  4024dc:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4024e2:	48 98                	cltq
  4024e4:	48 c1 e0 0a          	shl    $0xa,%rax
  4024e8:	48 89 c2             	mov    %rax,%rdx
  4024eb:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4024f2:	48 01 c2             	add    %rax,%rdx
  4024f5:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4024f9:	48 89 82 c8 03 00 00 	mov    %rax,0x3c8(%rdx)
    data[x].reads = reads;
  402500:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402506:	48 98                	cltq
  402508:	48 c1 e0 0a          	shl    $0xa,%rax
  40250c:	48 89 c2             	mov    %rax,%rdx
  40250f:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402516:	48 01 c2             	add    %rax,%rdx
  402519:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
  402520:	48 89 82 a0 03 00 00 	mov    %rax,0x3a0(%rdx)
    data[x].writes = writes; 
  402527:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40252d:	48 98                	cltq
  40252f:	48 c1 e0 0a          	shl    $0xa,%rax
  402533:	48 89 c2             	mov    %rax,%rdx
  402536:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40253d:	48 01 c2             	add    %rax,%rdx
  402540:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  402547:	48 89 82 a8 03 00 00 	mov    %rax,0x3a8(%rdx)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t)); 
  40254e:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402554:	48 98                	cltq
  402556:	48 c1 e0 0a          	shl    $0xa,%rax
  40255a:	48 89 c2             	mov    %rax,%rdx
  40255d:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402564:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  402568:	be 80 00 00 00       	mov    $0x80,%esi
  40256d:	bf 01 00 00 00       	mov    $0x1,%edi
  402572:	e8 59 eb ff ff       	call   4010d0 <calloc@plt>
  402577:	48 89 43 78          	mov    %rax,0x78(%rbx)
    CPU_SET(cpu += 1, data[x].cpu_set); 
  40257b:	83 85 c4 fe ff ff 01 	addl   $0x1,-0x13c(%rbp)
  402582:	8b 85 c4 fe ff ff    	mov    -0x13c(%rbp),%eax
  402588:	48 98                	cltq
  40258a:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  40258e:	48 81 7d b0 ff 03 00 00 	cmpq   $0x3ff,-0x50(%rbp)
  402596:	77 78                	ja     402610 <main+0x581>
  402598:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40259e:	48 98                	cltq
  4025a0:	48 c1 e0 0a          	shl    $0xa,%rax
  4025a4:	48 89 c2             	mov    %rax,%rdx
  4025a7:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4025ae:	48 01 d0             	add    %rdx,%rax
  4025b1:	48 8b 40 78          	mov    0x78(%rax),%rax
  4025b5:	48 89 c1             	mov    %rax,%rcx
  4025b8:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
  4025bc:	48 c1 e8 06          	shr    $0x6,%rax
  4025c0:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4025c8:	48 01 ca             	add    %rcx,%rdx
  4025cb:	48 8b 32             	mov    (%rdx),%rsi
  4025ce:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
  4025d2:	83 e2 3f             	and    $0x3f,%edx
  4025d5:	bf 01 00 00 00       	mov    $0x1,%edi
  4025da:	89 d1                	mov    %edx,%ecx
  4025dc:	48 d3 e7             	shl    %cl,%rdi
  4025df:	48 89 f9             	mov    %rdi,%rcx
  4025e2:	8b 95 c8 fe ff ff    	mov    -0x138(%rbp),%edx
  4025e8:	48 63 d2             	movslq %edx,%rdx
  4025eb:	48 89 d7             	mov    %rdx,%rdi
  4025ee:	48 c1 e7 0a          	shl    $0xa,%rdi
  4025f2:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4025f9:	48 01 fa             	add    %rdi,%rdx
  4025fc:	48 8b 52 78          	mov    0x78(%rdx),%rdx
  402600:	48 c1 e0 03          	shl    $0x3,%rax
  402604:	48 01 d0             	add    %rdx,%rax
  402607:	48 09 ce             	or     %rcx,%rsi
  40260a:	48 89 f2             	mov    %rsi,%rdx
  40260d:	48 89 10             	mov    %rdx,(%rax)
    printf("assigning thread %d to cpu %d\n", x, cpu);
  402610:	8b 95 c4 fe ff ff    	mov    -0x13c(%rbp),%edx
  402616:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40261c:	89 c6                	mov    %eax,%esi
  40261e:	48 8d 05 ab 1a 00 00 	lea    0x1aab(%rip),%rax        # 4040d0 <_IO_stdin_used+0xd0>
  402625:	48 89 c7             	mov    %rax,%rdi
  402628:	b8 00 00 00 00       	mov    $0x0,%eax
  40262d:	e8 4e ea ff ff       	call   401080 <printf@plt>
    data[x].bucketstart = x * buckets; 
  402632:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402638:	48 98                	cltq
  40263a:	48 c1 e0 0a          	shl    $0xa,%rax
  40263e:	48 89 c2             	mov    %rax,%rdx
  402641:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402648:	48 01 c2             	add    %rax,%rdx
  40264b:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402651:	0f af 85 90 fe ff ff 	imul   -0x170(%rbp),%eax
  402658:	89 82 98 00 00 00    	mov    %eax,0x98(%rdx)
    data[x].globalwrite = globalwrite;
  40265e:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402664:	48 98                	cltq
  402666:	48 c1 e0 0a          	shl    $0xa,%rax
  40266a:	48 89 c2             	mov    %rax,%rdx
  40266d:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402674:	48 01 c2             	add    %rax,%rdx
  402677:	48 8b 85 e0 fe ff ff 	mov    -0x120(%rbp),%rax
  40267e:	48 89 82 80 03 00 00 	mov    %rax,0x380(%rdx)
    data[x].loglevel = debug;
  402685:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40268b:	48 98                	cltq
  40268d:	48 c1 e0 0a          	shl    $0xa,%rax
  402691:	48 89 c2             	mov    %rax,%rdx
  402694:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40269b:	48 01 c2             	add    %rax,%rdx
  40269e:	8b 85 a0 fe ff ff    	mov    -0x160(%rbp),%eax
  4026a4:	89 82 80 00 00 00    	mov    %eax,0x80(%rdx)
    data[x].running = 2;
  4026aa:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026b0:	48 98                	cltq
  4026b2:	48 c1 e0 0a          	shl    $0xa,%rax
  4026b6:	48 89 c2             	mov    %rax,%rdx
  4026b9:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026c0:	48 01 d0             	add    %rdx,%rax
  4026c3:	c7 40 5c 02 00 00 00 	movl   $0x2,0x5c(%rax)
    data[x].threadindex = x;
  4026ca:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026d0:	48 98                	cltq
  4026d2:	48 c1 e0 0a          	shl    $0xa,%rax
  4026d6:	48 89 c2             	mov    %rax,%rdx
  4026d9:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026e0:	48 01 c2             	add    %rax,%rdx
  4026e3:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026e9:	89 42 64             	mov    %eax,0x64(%rdx)
    data[x].worksize = worksize;
  4026ec:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026f2:	48 98                	cltq
  4026f4:	48 c1 e0 0a          	shl    $0xa,%rax
  4026f8:	48 89 c2             	mov    %rax,%rdx
  4026fb:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402702:	48 01 d0             	add    %rdx,%rax
  402705:	48 8b 95 10 ff ff ff 	mov    -0xf0(%rbp),%rdx
  40270c:	89 50 60             	mov    %edx,0x60(%rax)
    
    data[x].availables = buckets;
  40270f:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402715:	48 98                	cltq
  402717:	48 c1 e0 0a          	shl    $0xa,%rax
  40271b:	48 89 c2             	mov    %rax,%rdx
  40271e:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402725:	48 01 c2             	add    %rax,%rdx
  402728:	8b 85 90 fe ff ff    	mov    -0x170(%rbp),%eax
  40272e:	89 82 94 00 00 00    	mov    %eax,0x94(%rdx)
    data[x].threadsize = threadsize;
  402734:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40273a:	48 98                	cltq
  40273c:	48 c1 e0 0a          	shl    $0xa,%rax
  402740:	48 89 c2             	mov    %rax,%rdx
  402743:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40274a:	48 01 c2             	add    %rax,%rdx
  40274d:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402753:	89 42 68             	mov    %eax,0x68(%rdx)
    data[x].readies = readies;
  402756:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40275c:	48 98                	cltq
  40275e:	48 c1 e0 0a          	shl    $0xa,%rax
  402762:	48 89 c2             	mov    %rax,%rdx
  402765:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40276c:	48 01 c2             	add    %rax,%rdx
  40276f:	48 8b 85 60 ff ff ff 	mov    -0xa0(%rbp),%rax
  402776:	48 89 42 20          	mov    %rax,0x20(%rdx)
    data[x].readies[x] = 0;
  40277a:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402780:	48 98                	cltq
  402782:	48 c1 e0 0a          	shl    $0xa,%rax
  402786:	48 89 c2             	mov    %rax,%rdx
  402789:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402790:	48 01 d0             	add    %rdx,%rax
  402793:	48 8b 50 20          	mov    0x20(%rax),%rdx
  402797:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40279d:	48 98                	cltq
  40279f:	48 c1 e0 02          	shl    $0x2,%rax
  4027a3:	48 01 d0             	add    %rdx,%rax
  4027a6:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    data[x].buckets = buckets;
  4027ac:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027b2:	48 98                	cltq
  4027b4:	48 c1 e0 0a          	shl    $0xa,%rax
  4027b8:	48 89 c2             	mov    %rax,%rdx
  4027bb:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027c2:	48 01 c2             	add    %rax,%rdx
  4027c5:	8b 85 90 fe ff ff    	mov    -0x170(%rbp),%eax
  4027cb:	89 82 90 00 00 00    	mov    %eax,0x90(%rdx)
    data[x].main = &data[0];
  4027d1:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027d7:	48 98                	cltq
  4027d9:	48 c1 e0 0a          	shl    $0xa,%rax
  4027dd:	48 89 c2             	mov    %rax,%rdx
  4027e0:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027e7:	48 01 c2             	add    %rax,%rdx
  4027ea:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027f1:	48 89 42 28          	mov    %rax,0x28(%rdx)
    data[x].threads = data;
  4027f5:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027fb:	48 98                	cltq
  4027fd:	48 c1 e0 0a          	shl    $0xa,%rax
  402801:	48 89 c2             	mov    %rax,%rdx
  402804:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40280b:	48 01 c2             	add    %rax,%rdx
  40280e:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402815:	48 89 42 30          	mov    %rax,0x30(%rdx)
    
    data[x].read = 0;
  402819:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40281f:	48 98                	cltq
  402821:	48 c1 e0 0a          	shl    $0xa,%rax
  402825:	48 89 c2             	mov    %rax,%rdx
  402828:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40282f:	48 01 d0             	add    %rdx,%rax
  402832:	48 c7 00 00 00 00 00 	movq   $0x0,(%rax)
    data[x].write = worksize;
  402839:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40283f:	48 98                	cltq
  402841:	48 c1 e0 0a          	shl    $0xa,%rax
  402845:	48 89 c2             	mov    %rax,%rdx
  402848:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40284f:	48 01 c2             	add    %rax,%rdx
  402852:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  402859:	48 89 42 08          	mov    %rax,0x8(%rdx)
    data[x].readcursor = threadsize - 1;
  40285d:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402863:	48 98                	cltq
  402865:	48 c1 e0 0a          	shl    $0xa,%rax
  402869:	48 89 c2             	mov    %rax,%rdx
  40286c:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402873:	48 01 d0             	add    %rdx,%rax
  402876:	8b 95 98 fe ff ff    	mov    -0x168(%rbp),%edx
  40287c:	83 ea 01             	sub    $0x1,%edx
  40287f:	89 90 00 02 00 00    	mov    %edx,0x200(%rax)
    data[x].writecursor = 0;
  402885:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40288b:	48 98                	cltq
  40288d:	48 c1 e0 0a          	shl    $0xa,%rax
  402891:	48 89 c2             	mov    %rax,%rdx
  402894:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40289b:	48 01 d0             	add    %rdx,%rax
  40289e:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    data[x].freelist = freelist;
  4028a8:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028ae:	48 98                	cltq
  4028b0:	48 c1 e0 0a          	shl    $0xa,%rax
  4028b4:	48 89 c2             	mov    %rax,%rdx
  4028b7:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4028be:	48 01 c2             	add    %rax,%rdx
  4028c1:	48 8b 85 58 ff ff ff 	mov    -0xa8(%rbp),%rax
  4028c8:	48 89 82 a0 00 00 00 	mov    %rax,0xa0(%rdx)
    data[x].chunksize = chunksize;
  4028cf:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028d5:	48 98                	cltq
  4028d7:	48 c1 e0 0a          	shl    $0xa,%rax
  4028db:	48 89 c2             	mov    %rax,%rdx
  4028de:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4028e5:	48 01 c2             	add    %rax,%rdx
  4028e8:	48 8b 85 38 ff ff ff 	mov    -0xc8(%rbp),%rax
  4028ef:	48 89 82 c0 00 00 00 	mov    %rax,0xc0(%rdx)
    data[x].chunkslen = chunkslen;
  4028f6:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028fc:	48 98                	cltq
  4028fe:	48 c1 e0 0a          	shl    $0xa,%rax
  402902:	48 89 c2             	mov    %rax,%rdx
  402905:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40290c:	48 01 c2             	add    %rax,%rdx
  40290f:	48 8b 85 08 ff ff ff 	mov    -0xf8(%rbp),%rax
  402916:	48 89 82 b8 00 00 00 	mov    %rax,0xb8(%rdx)
    data[x].newmask = 0;
  40291d:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402923:	48 98                	cltq
  402925:	48 c1 e0 0a          	shl    $0xa,%rax
  402929:	48 89 c2             	mov    %rax,%rdx
  40292c:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402933:	48 01 d0             	add    %rdx,%rax
  402936:	c7 80 c8 00 00 00 00 00 00 00 	movl   $0x0,0xc8(%rax)
    data[x].prevread = threadsize;
  402940:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402946:	48 98                	cltq
  402948:	48 c1 e0 0a          	shl    $0xa,%rax
  40294c:	48 89 c2             	mov    %rax,%rdx
  40294f:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402956:	48 01 c2             	add    %rax,%rdx
  402959:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40295f:	48 98                	cltq
  402961:	48 89 82 08 03 00 00 	mov    %rax,0x308(%rdx)
    data[x].prevwrite = threadsize;
  402968:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40296e:	48 98                	cltq
  402970:	48 c1 e0 0a          	shl    $0xa,%rax
  402974:	48 89 c2             	mov    %rax,%rdx
  402977:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40297e:	48 01 c2             	add    %rax,%rdx
  402981:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402987:	48 98                	cltq
  402989:	48 89 82 10 03 00 00 	mov    %rax,0x310(%rdx)
    data[x].mystream = 1 + (x / 4);
  402990:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402996:	8d 50 03             	lea    0x3(%rax),%edx
  402999:	85 c0                	test   %eax,%eax
  40299b:	0f 48 c2             	cmovs  %edx,%eax
  40299e:	c1 f8 02             	sar    $0x2,%eax
  4029a1:	89 c2                	mov    %eax,%edx
  4029a3:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4029a9:	48 98                	cltq
  4029ab:	48 c1 e0 0a          	shl    $0xa,%rax
  4029af:	48 89 c1             	mov    %rax,%rcx
  4029b2:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4029b9:	48 01 c8             	add    %rcx,%rax
  4029bc:	83 c2 01             	add    $0x1,%edx
  4029bf:	89 90 8c 03 00 00    	mov    %edx,0x38c(%rax)
    data[x].thiswrite = threadsize;
  4029c5:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4029cb:	48 98                	cltq
  4029cd:	48 c1 e0 0a          	shl    $0xa,%rax
  4029d1:	48 89 c2             	mov    %rax,%rdx
  4029d4:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4029db:	48 01 c2             	add    %rax,%rdx
  4029de:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4029e4:	89 82 28 03 00 00    	mov    %eax,0x328(%rdx)
    int epochs = 10000000;
  4029ea:	c7 85 dc fe ff ff 80 96 98 00 	movl   $0x989680,-0x124(%rbp)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4029f4:	8b 85 dc fe ff ff    	mov    -0x124(%rbp),%eax
  4029fa:	48 98                	cltq
  4029fc:	8b 95 c8 fe ff ff    	mov    -0x138(%rbp),%edx
  402a02:	48 63 d2             	movslq %edx,%rdx
  402a05:	48 89 d1             	mov    %rdx,%rcx
  402a08:	48 c1 e1 0a          	shl    $0xa,%rcx
  402a0c:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  402a13:	48 8d 1c 11          	lea    (%rcx,%rdx,1),%rbx
  402a17:	be 30 00 00 00       	mov    $0x30,%esi
  402a1c:	48 89 c7             	mov    %rax,%rdi
  402a1f:	e8 ac e6 ff ff       	call   4010d0 <calloc@plt>
  402a24:	48 89 83 18 03 00 00 	mov    %rax,0x318(%rbx)
    data[x].epochssize = epochs;
  402a2b:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a31:	48 98                	cltq
  402a33:	48 c1 e0 0a          	shl    $0xa,%rax
  402a37:	48 89 c2             	mov    %rax,%rdx
  402a3a:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a41:	48 01 c2             	add    %rax,%rdx
  402a44:	8b 85 dc fe ff ff    	mov    -0x124(%rbp),%eax
  402a4a:	89 82 20 03 00 00    	mov    %eax,0x320(%rdx)
    data[x].globalread = globalread;
  402a50:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a56:	48 98                	cltq
  402a58:	48 c1 e0 0a          	shl    $0xa,%rax
  402a5c:	48 89 c2             	mov    %rax,%rdx
  402a5f:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a66:	48 01 c2             	add    %rax,%rdx
  402a69:	48 8b 85 68 ff ff ff 	mov    -0x98(%rbp),%rax
  402a70:	48 89 82 48 03 00 00 	mov    %rax,0x348(%rdx)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  402a77:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a7d:	48 98                	cltq
  402a7f:	48 c1 e0 0a          	shl    $0xa,%rax
  402a83:	48 89 c2             	mov    %rax,%rdx
  402a86:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a8d:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  402a91:	be 30 00 00 00       	mov    $0x30,%esi
  402a96:	bf 10 27 00 00       	mov    $0x2710,%edi
  402a9b:	e8 30 e6 ff ff       	call   4010d0 <calloc@plt>
  402aa0:	48 89 83 30 03 00 00 	mov    %rax,0x330(%rbx)
    data[x].accesssize = accesssize;
  402aa7:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402aad:	48 98                	cltq
  402aaf:	48 c1 e0 0a          	shl    $0xa,%rax
  402ab3:	48 89 c2             	mov    %rax,%rdx
  402ab6:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402abd:	48 01 c2             	add    %rax,%rdx
  402ac0:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  402ac6:	89 82 b8 03 00 00    	mov    %eax,0x3b8(%rdx)
  for (int x = 0; x < threadsize ; x++) {
  402acc:	83 85 c8 fe ff ff 01 	addl   $0x1,-0x138(%rbp)
  402ad3:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402ad9:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402adf:	0f 8c f3 f8 ff ff    	jl     4023d8 <main+0x349>
  } 
  
  for (int x = 0; x < threadsize ; x++) {
  402ae5:	c7 85 d0 fe ff ff 00 00 00 00 	movl   $0x0,-0x130(%rbp)
  402aef:	e9 b8 00 00 00       	jmp    402bac <main+0xb1d>
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  402af4:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402afa:	48 98                	cltq
  402afc:	48 c1 e0 0a          	shl    $0xa,%rax
  402b00:	48 89 c2             	mov    %rax,%rdx
  402b03:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402b0a:	48 01 c2             	add    %rax,%rdx
  402b0d:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b13:	48 63 c8             	movslq %eax,%rcx
  402b16:	48 89 c8             	mov    %rcx,%rax
  402b19:	48 c1 e0 03          	shl    $0x3,%rax
  402b1d:	48 29 c8             	sub    %rcx,%rax
  402b20:	48 c1 e0 03          	shl    $0x3,%rax
  402b24:	48 89 c1             	mov    %rax,%rcx
  402b27:	48 8b 85 f0 fe ff ff 	mov    -0x110(%rbp),%rax
  402b2e:	48 8d 34 01          	lea    (%rcx,%rax,1),%rsi
  402b32:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b38:	48 98                	cltq
  402b3a:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
  402b42:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402b49:	48 01 c8             	add    %rcx,%rax
  402b4c:	48 89 d1             	mov    %rdx,%rcx
  402b4f:	48 c7 c2 8a 1f 40 00 	mov    $0x401f8a,%rdx
  402b56:	48 89 c7             	mov    %rax,%rdi
  402b59:	e8 82 e5 ff ff       	call   4010e0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  402b5e:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b64:	48 98                	cltq
  402b66:	48 c1 e0 0a          	shl    $0xa,%rax
  402b6a:	48 89 c2             	mov    %rax,%rdx
  402b6d:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402b74:	48 01 d0             	add    %rdx,%rax
  402b77:	48 8b 50 78          	mov    0x78(%rax),%rdx
  402b7b:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b81:	48 98                	cltq
  402b83:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
  402b8b:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402b92:	48 01 c8             	add    %rcx,%rax
  402b95:	48 8b 00             	mov    (%rax),%rax
  402b98:	be 08 00 00 00       	mov    $0x8,%esi
  402b9d:	48 89 c7             	mov    %rax,%rdi
  402ba0:	e8 8b e4 ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  402ba5:	83 85 d0 fe ff ff 01 	addl   $0x1,-0x130(%rbp)
  402bac:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402bb2:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402bb8:	0f 8c 36 ff ff ff    	jl     402af4 <main+0xa65>
  }
  
  struct timespec time = {
  402bbe:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402bc4:	48 98                	cltq
  402bc6:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
  402bca:	48 c7 45 c8 00 00 00 00 	movq   $0x0,-0x38(%rbp)
    seconds,
    0
  };
  struct timespec rem = {
  402bd2:	48 c7 45 d0 00 00 00 00 	movq   $0x0,-0x30(%rbp)
  402bda:	48 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%rbp)
    0,
    0
  };
  
  nanosleep(&time, &rem);
  402be2:	48 8d 55 d0          	lea    -0x30(%rbp),%rdx
  402be6:	48 8d 45 c0          	lea    -0x40(%rbp),%rax
  402bea:	48 89 d6             	mov    %rdx,%rsi
  402bed:	48 89 c7             	mov    %rax,%rdi
  402bf0:	e8 ab e4 ff ff       	call   4010a0 <nanosleep@plt>
  
  printf("runphased\n");
  402bf5:	48 8d 05 f3 14 00 00 	lea    0x14f3(%rip),%rax        # 4040ef <_IO_stdin_used+0xef>
  402bfc:	48 89 c7             	mov    %rax,%rdi
  402bff:	e8 3c e4 ff ff       	call   401040 <puts@plt>
  for (int x = 0; x < threadsize ; x++) {
  402c04:	c7 85 b8 fe ff ff 00 00 00 00 	movl   $0x0,-0x148(%rbp)
  402c0e:	eb 29                	jmp    402c39 <main+0xbaa>
    data[x].running--;
  402c10:	8b 85 b8 fe ff ff    	mov    -0x148(%rbp),%eax
  402c16:	48 98                	cltq
  402c18:	48 c1 e0 0a          	shl    $0xa,%rax
  402c1c:	48 89 c2             	mov    %rax,%rdx
  402c1f:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402c26:	48 01 d0             	add    %rdx,%rax
  402c29:	8b 50 5c             	mov    0x5c(%rax),%edx
  402c2c:	83 ea 01             	sub    $0x1,%edx
  402c2f:	89 50 5c             	mov    %edx,0x5c(%rax)
  for (int x = 0; x < threadsize ; x++) {
  402c32:	83 85 b8 fe ff ff 01 	addl   $0x1,-0x148(%rbp)
  402c39:	8b 85 b8 fe ff ff    	mov    -0x148(%rbp),%eax
  402c3f:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402c45:	7c c9                	jl     402c10 <main+0xb81>
    
  }
  
 printf("draining\n");
  402c47:	48 8d 05 ab 14 00 00 	lea    0x14ab(%rip),%rax        # 4040f9 <_IO_stdin_used+0xf9>
  402c4e:	48 89 c7             	mov    %rax,%rdi
  402c51:	e8 ea e3 ff ff       	call   401040 <puts@plt>
 // time.tv_sec = 3;
//nanosleep(&time, &rem);
  for (int x = 0; x < threadsize ; x++) {
  402c56:	c7 85 bc fe ff ff 00 00 00 00 	movl   $0x0,-0x144(%rbp)
  402c60:	eb 29                	jmp    402c8b <main+0xbfc>
    data[x].running--;
  402c62:	8b 85 bc fe ff ff    	mov    -0x144(%rbp),%eax
  402c68:	48 98                	cltq
  402c6a:	48 c1 e0 0a          	shl    $0xa,%rax
  402c6e:	48 89 c2             	mov    %rax,%rdx
  402c71:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402c78:	48 01 d0             	add    %rdx,%rax
  402c7b:	8b 50 5c             	mov    0x5c(%rax),%edx
  402c7e:	83 ea 01             	sub    $0x1,%edx
  402c81:	89 50 5c             	mov    %edx,0x5c(%rax)
  for (int x = 0; x < threadsize ; x++) {
  402c84:	83 85 bc fe ff ff 01 	addl   $0x1,-0x144(%rbp)
  402c8b:	8b 85 bc fe ff ff    	mov    -0x144(%rbp),%eax
  402c91:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402c97:	7c c9                	jl     402c62 <main+0xbd3>
  }
  
  //nanosleep(&time, &rem);
  for (int x = 0; x < threadsize; x++) {
  402c99:	c7 85 c0 fe ff ff 00 00 00 00 	movl   $0x0,-0x140(%rbp)
  402ca3:	eb 36                	jmp    402cdb <main+0xc4c>
    void *res;
    pthread_join(thread[x], &res);
  402ca5:	8b 85 c0 fe ff ff    	mov    -0x140(%rbp),%eax
  402cab:	48 98                	cltq
  402cad:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  402cb5:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402cbc:	48 01 d0             	add    %rdx,%rax
  402cbf:	48 8b 00             	mov    (%rax),%rax
  402cc2:	48 8d 95 e8 fe ff ff 	lea    -0x118(%rbp),%rdx
  402cc9:	48 89 d6             	mov    %rdx,%rsi
  402ccc:	48 89 c7             	mov    %rax,%rdi
  402ccf:	e8 3c e4 ff ff       	call   401110 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  402cd4:	83 85 c0 fe ff ff 01 	addl   $0x1,-0x140(%rbp)
  402cdb:	8b 85 c0 fe ff ff    	mov    -0x140(%rbp),%eax
  402ce1:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402ce7:	7c bc                	jl     402ca5 <main+0xc16>
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  402ce9:	48 8d 05 12 14 00 00 	lea    0x1412(%rip),%rax        # 404102 <_IO_stdin_used+0x102>
  402cf0:	48 89 c7             	mov    %rax,%rdi
  402cf3:	e8 48 e3 ff ff       	call   401040 <puts@plt>
  long freq = 0;
  402cf8:	48 c7 85 20 ff ff ff 00 00 00 00 	movq   $0x0,-0xe0(%rbp)
  long sends = 1;
  402d03:	48 c7 45 80 01 00 00 00 	movq   $0x1,-0x80(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402d0b:	c7 85 a8 fe ff ff 00 00 00 00 	movl   $0x0,-0x158(%rbp)
  402d15:	eb 5f                	jmp    402d76 <main+0xce7>
    printf("%ld reads\n", data[x].freq);
  402d17:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d1d:	48 98                	cltq
  402d1f:	48 c1 e0 0a          	shl    $0xa,%rax
  402d23:	48 89 c2             	mov    %rax,%rdx
  402d26:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402d2d:	48 01 d0             	add    %rdx,%rax
  402d30:	48 8b 40 48          	mov    0x48(%rax),%rax
  402d34:	48 89 c6             	mov    %rax,%rsi
  402d37:	48 8d 05 d9 13 00 00 	lea    0x13d9(%rip),%rax        # 404117 <_IO_stdin_used+0x117>
  402d3e:	48 89 c7             	mov    %rax,%rdi
  402d41:	b8 00 00 00 00       	mov    $0x0,%eax
  402d46:	e8 35 e3 ff ff       	call   401080 <printf@plt>
    freq += data[x].freq;
  402d4b:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d51:	48 98                	cltq
  402d53:	48 c1 e0 0a          	shl    $0xa,%rax
  402d57:	48 89 c2             	mov    %rax,%rdx
  402d5a:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402d61:	48 01 d0             	add    %rdx,%rax
  402d64:	48 8b 40 48          	mov    0x48(%rax),%rax
  402d68:	48 01 85 20 ff ff ff 	add    %rax,-0xe0(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402d6f:	83 85 a8 fe ff ff 01 	addl   $0x1,-0x158(%rbp)
  402d76:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d7c:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402d82:	7c 93                	jl     402d17 <main+0xc88>
  }
  printf("freq: %ld\n", freq/ seconds);
  402d84:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402d8a:	48 63 d8             	movslq %eax,%rbx
  402d8d:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402d94:	48 99                	cqto
  402d96:	48 f7 fb             	idiv   %rbx
  402d99:	48 89 c6             	mov    %rax,%rsi
  402d9c:	48 8d 05 7f 13 00 00 	lea    0x137f(%rip),%rax        # 404122 <_IO_stdin_used+0x122>
  402da3:	48 89 c7             	mov    %rax,%rdi
  402da6:	b8 00 00 00 00       	mov    $0x0,%eax
  402dab:	e8 d0 e2 ff ff       	call   401080 <printf@plt>
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  402db0:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402db7:	48 0f af 45 80       	imul   -0x80(%rbp),%rax
  402dbc:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402dc2:	48 63 da             	movslq %edx,%rbx
  402dc5:	48 99                	cqto
  402dc7:	48 f7 fb             	idiv   %rbx
  402dca:	48 89 c6             	mov    %rax,%rsi
  402dcd:	48 8d 05 59 13 00 00 	lea    0x1359(%rip),%rax        # 40412d <_IO_stdin_used+0x12d>
  402dd4:	48 89 c7             	mov    %rax,%rdi
  402dd7:	b8 00 00 00 00       	mov    $0x0,%eax
  402ddc:	e8 9f e2 ff ff       	call   401080 <printf@plt>
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  402de1:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402de7:	48 63 d8             	movslq %eax,%rbx
  402dea:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402df1:	48 99                	cqto
  402df3:	48 f7 fb             	idiv   %rbx
  402df6:	48 89 c3             	mov    %rax,%rbx
  402df9:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402dfe:	48 99                	cqto
  402e00:	48 f7 fb             	idiv   %rbx
  402e03:	48 89 c6             	mov    %rax,%rsi
  402e06:	48 8d 05 2e 13 00 00 	lea    0x132e(%rip),%rax        # 40413b <_IO_stdin_used+0x13b>
  402e0d:	48 89 c7             	mov    %rax,%rdi
  402e10:	b8 00 00 00 00       	mov    $0x0,%eax
  402e15:	e8 66 e2 ff ff       	call   401080 <printf@plt>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  402e1a:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402e20:	48 63 d8             	movslq %eax,%rbx
  402e23:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402e2a:	48 99                	cqto
  402e2c:	48 f7 fb             	idiv   %rbx
  402e2f:	48 89 c3             	mov    %rax,%rbx
  402e32:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402e37:	48 99                	cqto
  402e39:	48 f7 fb             	idiv   %rbx
  402e3c:	48 99                	cqto
  402e3e:	48 f7 7d 80          	idivq  -0x80(%rbp)
  402e42:	48 89 c6             	mov    %rax,%rsi
  402e45:	48 8d 05 03 13 00 00 	lea    0x1303(%rip),%rax        # 40414f <_IO_stdin_used+0x14f>
  402e4c:	48 89 c7             	mov    %rax,%rdi
  402e4f:	b8 00 00 00 00       	mov    $0x0,%eax
  402e54:	e8 27 e2 ff ff       	call   401080 <printf@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  402e59:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402e60:	48 0f af 45 80       	imul   -0x80(%rbp),%rax
  402e65:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402e6b:	48 63 da             	movslq %edx,%rbx
  402e6e:	48 99                	cqto
  402e70:	48 f7 fb             	idiv   %rbx
  402e73:	48 89 c3             	mov    %rax,%rbx
  402e76:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402e7b:	48 99                	cqto
  402e7d:	48 f7 fb             	idiv   %rbx
  402e80:	48 89 c6             	mov    %rax,%rsi
  402e83:	48 8d 05 e3 12 00 00 	lea    0x12e3(%rip),%rax        # 40416d <_IO_stdin_used+0x16d>
  402e8a:	48 89 c7             	mov    %rax,%rdi
  402e8d:	b8 00 00 00 00       	mov    $0x0,%eax
  402e92:	e8 e9 e1 ff ff       	call   401080 <printf@plt>
  
  long goods = 0;
  402e97:	48 c7 85 28 ff ff ff 00 00 00 00 	movq   $0x0,-0xd8(%rbp)

  for (int x = 0; x < threadsize; x++) {
  402ea2:	c7 85 ac fe ff ff 00 00 00 00 	movl   $0x0,-0x154(%rbp)
  402eac:	eb 65                	jmp    402f13 <main+0xe84>
    printf("%ld successreads\n", data[x].successreads);
  402eae:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402eb4:	48 98                	cltq
  402eb6:	48 c1 e0 0a          	shl    $0xa,%rax
  402eba:	48 89 c2             	mov    %rax,%rdx
  402ebd:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402ec4:	48 01 d0             	add    %rdx,%rax
  402ec7:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  402ece:	48 89 c6             	mov    %rax,%rsi
  402ed1:	48 8d 05 a8 12 00 00 	lea    0x12a8(%rip),%rax        # 404180 <_IO_stdin_used+0x180>
  402ed8:	48 89 c7             	mov    %rax,%rdi
  402edb:	b8 00 00 00 00       	mov    $0x0,%eax
  402ee0:	e8 9b e1 ff ff       	call   401080 <printf@plt>
    goods += data[x].successreads;
  402ee5:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402eeb:	48 98                	cltq
  402eed:	48 c1 e0 0a          	shl    $0xa,%rax
  402ef1:	48 89 c2             	mov    %rax,%rdx
  402ef4:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402efb:	48 01 d0             	add    %rdx,%rax
  402efe:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  402f05:	48 01 85 28 ff ff ff 	add    %rax,-0xd8(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402f0c:	83 85 ac fe ff ff 01 	addl   $0x1,-0x154(%rbp)
  402f13:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402f19:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402f1f:	7c 8d                	jl     402eae <main+0xe1f>
  }
  
  long freq_writes = 0;
  402f21:	48 c7 85 30 ff ff ff 00 00 00 00 	movq   $0x0,-0xd0(%rbp)
  
  for (int x = 0; x < threadsize; x++) {
  402f2c:	c7 85 b0 fe ff ff 00 00 00 00 	movl   $0x0,-0x150(%rbp)
  402f36:	eb 5f                	jmp    402f97 <main+0xf08>
    freq_writes += data[x].freq_writes;
  402f38:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f3e:	48 98                	cltq
  402f40:	48 c1 e0 0a          	shl    $0xa,%rax
  402f44:	48 89 c2             	mov    %rax,%rdx
  402f47:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402f4e:	48 01 d0             	add    %rdx,%rax
  402f51:	48 8b 40 50          	mov    0x50(%rax),%rax
  402f55:	48 01 85 30 ff ff ff 	add    %rax,-0xd0(%rbp)
    printf("%ld writes\n", data[x].freq_writes);
  402f5c:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f62:	48 98                	cltq
  402f64:	48 c1 e0 0a          	shl    $0xa,%rax
  402f68:	48 89 c2             	mov    %rax,%rdx
  402f6b:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402f72:	48 01 d0             	add    %rdx,%rax
  402f75:	48 8b 40 50          	mov    0x50(%rax),%rax
  402f79:	48 89 c6             	mov    %rax,%rsi
  402f7c:	48 8d 05 0f 12 00 00 	lea    0x120f(%rip),%rax        # 404192 <_IO_stdin_used+0x192>
  402f83:	48 89 c7             	mov    %rax,%rdi
  402f86:	b8 00 00 00 00       	mov    $0x0,%eax
  402f8b:	e8 f0 e0 ff ff       	call   401080 <printf@plt>
  for (int x = 0; x < threadsize; x++) {
  402f90:	83 85 b0 fe ff ff 01 	addl   $0x1,-0x150(%rbp)
  402f97:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f9d:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402fa3:	7c 93                	jl     402f38 <main+0xea9>
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  402fa5:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402fab:	48 63 d8             	movslq %eax,%rbx
  402fae:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402fb5:	48 99                	cqto
  402fb7:	48 f7 fb             	idiv   %rbx
  402fba:	48 89 c6             	mov    %rax,%rsi
  402fbd:	48 8d 05 da 11 00 00 	lea    0x11da(%rip),%rax        # 40419e <_IO_stdin_used+0x19e>
  402fc4:	48 89 c7             	mov    %rax,%rdi
  402fc7:	b8 00 00 00 00       	mov    $0x0,%eax
  402fcc:	e8 af e0 ff ff       	call   401080 <printf@plt>

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  402fd1:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402fd8:	48 0f af 45 80       	imul   -0x80(%rbp),%rax
  402fdd:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402fe3:	48 63 da             	movslq %edx,%rbx
  402fe6:	48 99                	cqto
  402fe8:	48 f7 fb             	idiv   %rbx
  402feb:	48 89 c6             	mov    %rax,%rsi
  402fee:	48 8d 05 bb 11 00 00 	lea    0x11bb(%rip),%rax        # 4041b0 <_IO_stdin_used+0x1b0>
  402ff5:	48 89 c7             	mov    %rax,%rdi
  402ff8:	b8 00 00 00 00       	mov    $0x0,%eax
  402ffd:	e8 7e e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  403002:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  403008:	48 63 d8             	movslq %eax,%rbx
  40300b:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  403012:	48 99                	cqto
  403014:	48 f7 fb             	idiv   %rbx
  403017:	48 89 c3             	mov    %rax,%rbx
  40301a:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40301f:	48 99                	cqto
  403021:	48 f7 fb             	idiv   %rbx
  403024:	48 89 c6             	mov    %rax,%rsi
  403027:	48 8d 05 9a 11 00 00 	lea    0x119a(%rip),%rax        # 4041c8 <_IO_stdin_used+0x1c8>
  40302e:	48 89 c7             	mov    %rax,%rdi
  403031:	b8 00 00 00 00       	mov    $0x0,%eax
  403036:	e8 45 e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes per thread latency: %ld\n", (1000000000/(freq_writes / seconds)) / sends);
  40303b:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  403041:	48 63 d8             	movslq %eax,%rbx
  403044:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  40304b:	48 99                	cqto
  40304d:	48 f7 fb             	idiv   %rbx
  403050:	48 89 c3             	mov    %rax,%rbx
  403053:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  403058:	48 99                	cqto
  40305a:	48 f7 fb             	idiv   %rbx
  40305d:	48 99                	cqto
  40305f:	48 f7 7d 80          	idivq  -0x80(%rbp)
  403063:	48 89 c6             	mov    %rax,%rsi
  403066:	48 8d 05 7b 11 00 00 	lea    0x117b(%rip),%rax        # 4041e8 <_IO_stdin_used+0x1e8>
  40306d:	48 89 c7             	mov    %rax,%rdi
  403070:	b8 00 00 00 00       	mov    $0x0,%eax
  403075:	e8 06 e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * sends) / seconds));
  40307a:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  403081:	48 0f af 45 80       	imul   -0x80(%rbp),%rax
  403086:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  40308c:	48 63 da             	movslq %edx,%rbx
  40308f:	48 99                	cqto
  403091:	48 f7 fb             	idiv   %rbx
  403094:	48 89 c3             	mov    %rax,%rbx
  403097:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40309c:	48 99                	cqto
  40309e:	48 f7 fb             	idiv   %rbx
  4030a1:	48 89 c6             	mov    %rax,%rsi
  4030a4:	48 8d 05 62 11 00 00 	lea    0x1162(%rip),%rax        # 40420d <_IO_stdin_used+0x20d>
  4030ab:	48 89 c7             	mov    %rax,%rdi
  4030ae:	b8 00 00 00 00       	mov    $0x0,%eax
  4030b3:	e8 c8 df ff ff       	call   401080 <printf@plt>
    printf("%ldns\n", read.tv_nsec - created.tv_nsec);
    printf("%ldns\n", written.tv_nsec - read.tv_nsec);
    
  }
  */
  printf("writer speed\n");
  4030b8:	48 8d 05 68 11 00 00 	lea    0x1168(%rip),%rax        # 404227 <_IO_stdin_used+0x227>
  4030bf:	48 89 c7             	mov    %rax,%rdi
  4030c2:	e8 79 df ff ff       	call   401040 <puts@plt>
  for (int x = 0; x < 1 ;  x++){
  4030c7:	c7 85 b4 fe ff ff 00 00 00 00 	movl   $0x0,-0x14c(%rbp)
  4030d1:	e9 84 02 00 00       	jmp    40335a <main+0x12cb>
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  4030d6:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4030dc:	48 98                	cltq
  4030de:	48 c1 e0 0a          	shl    $0xa,%rax
  4030e2:	48 89 c2             	mov    %rax,%rdx
  4030e5:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4030ec:	48 01 d0             	add    %rdx,%rax
  4030ef:	48 8b 80 f0 00 00 00 	mov    0xf0(%rax),%rax
  4030f6:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4030fc:	48 63 d2             	movslq %edx,%rdx
  4030ff:	48 89 d1             	mov    %rdx,%rcx
  403102:	48 c1 e1 0a          	shl    $0xa,%rcx
  403106:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  40310d:	48 01 ca             	add    %rcx,%rdx
  403110:	48 8b 92 e0 00 00 00 	mov    0xe0(%rdx),%rdx
  403117:	48 29 d0             	sub    %rdx,%rax
  40311a:	48 89 c6             	mov    %rax,%rsi
  40311d:	48 8d 05 10 11 00 00 	lea    0x1110(%rip),%rax        # 404234 <_IO_stdin_used+0x234>
  403124:	48 89 c7             	mov    %rax,%rdi
  403127:	b8 00 00 00 00       	mov    $0x0,%eax
  40312c:	e8 4f df ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  403131:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403137:	48 98                	cltq
  403139:	48 c1 e0 0a          	shl    $0xa,%rax
  40313d:	48 89 c2             	mov    %rax,%rdx
  403140:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403147:	48 01 d0             	add    %rdx,%rax
  40314a:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
  403151:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  403157:	48 63 d2             	movslq %edx,%rdx
  40315a:	48 89 d1             	mov    %rdx,%rcx
  40315d:	48 c1 e1 0a          	shl    $0xa,%rcx
  403161:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403168:	48 01 ca             	add    %rcx,%rdx
  40316b:	48 8b 92 e0 00 00 00 	mov    0xe0(%rdx),%rdx
  403172:	48 29 d0             	sub    %rdx,%rax
  403175:	48 89 c6             	mov    %rax,%rsi
  403178:	48 8d 05 b5 10 00 00 	lea    0x10b5(%rip),%rax        # 404234 <_IO_stdin_used+0x234>
  40317f:	48 89 c7             	mov    %rax,%rdi
  403182:	b8 00 00 00 00       	mov    $0x0,%eax
  403187:	e8 f4 de ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  40318c:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403192:	48 98                	cltq
  403194:	48 c1 e0 0a          	shl    $0xa,%rax
  403198:	48 89 c2             	mov    %rax,%rdx
  40319b:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4031a2:	48 01 d0             	add    %rdx,%rax
  4031a5:	48 8b 80 f0 00 00 00 	mov    0xf0(%rax),%rax
  4031ac:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4031b2:	48 63 d2             	movslq %edx,%rdx
  4031b5:	48 89 d1             	mov    %rdx,%rcx
  4031b8:	48 c1 e1 0a          	shl    $0xa,%rcx
  4031bc:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4031c3:	48 01 ca             	add    %rcx,%rdx
  4031c6:	48 8b 92 00 01 00 00 	mov    0x100(%rdx),%rdx
  4031cd:	48 29 d0             	sub    %rdx,%rax
  4031d0:	48 89 c6             	mov    %rax,%rsi
  4031d3:	48 8d 05 5a 10 00 00 	lea    0x105a(%rip),%rax        # 404234 <_IO_stdin_used+0x234>
  4031da:	48 89 c7             	mov    %rax,%rdi
  4031dd:	b8 00 00 00 00       	mov    $0x0,%eax
  4031e2:	e8 99 de ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4031e7:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4031ed:	48 98                	cltq
  4031ef:	48 c1 e0 0a          	shl    $0xa,%rax
  4031f3:	48 89 c2             	mov    %rax,%rdx
  4031f6:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4031fd:	48 01 d0             	add    %rdx,%rax
  403200:	48 8b 80 20 01 00 00 	mov    0x120(%rax),%rax
  403207:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  40320d:	48 63 d2             	movslq %edx,%rdx
  403210:	48 89 d1             	mov    %rdx,%rcx
  403213:	48 c1 e1 0a          	shl    $0xa,%rcx
  403217:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  40321e:	48 01 ca             	add    %rcx,%rdx
  403221:	48 8b 92 10 01 00 00 	mov    0x110(%rdx),%rdx
  403228:	48 29 d0             	sub    %rdx,%rax
  40322b:	48 89 c6             	mov    %rax,%rsi
  40322e:	48 8d 05 ff 0f 00 00 	lea    0xfff(%rip),%rax        # 404234 <_IO_stdin_used+0x234>
  403235:	48 89 c7             	mov    %rax,%rdi
  403238:	b8 00 00 00 00       	mov    $0x0,%eax
  40323d:	e8 3e de ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  403242:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403248:	48 98                	cltq
  40324a:	48 c1 e0 0a          	shl    $0xa,%rax
  40324e:	48 89 c2             	mov    %rax,%rdx
  403251:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403258:	48 01 d0             	add    %rdx,%rax
  40325b:	48 8b 80 10 01 00 00 	mov    0x110(%rax),%rax
  403262:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  403268:	48 63 d2             	movslq %edx,%rdx
  40326b:	48 89 d1             	mov    %rdx,%rcx
  40326e:	48 c1 e1 0a          	shl    $0xa,%rcx
  403272:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403279:	48 01 ca             	add    %rcx,%rdx
  40327c:	48 8b 92 20 01 00 00 	mov    0x120(%rdx),%rdx
  403283:	48 29 d0             	sub    %rdx,%rax
  403286:	48 89 c6             	mov    %rax,%rsi
  403289:	48 8d 05 a4 0f 00 00 	lea    0xfa4(%rip),%rax        # 404234 <_IO_stdin_used+0x234>
  403290:	48 89 c7             	mov    %rax,%rdi
  403293:	b8 00 00 00 00       	mov    $0x0,%eax
  403298:	e8 e3 dd ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  40329d:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4032a3:	48 98                	cltq
  4032a5:	48 c1 e0 0a          	shl    $0xa,%rax
  4032a9:	48 89 c2             	mov    %rax,%rdx
  4032ac:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4032b3:	48 01 d0             	add    %rdx,%rax
  4032b6:	48 8b 80 10 01 00 00 	mov    0x110(%rax),%rax
  4032bd:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4032c3:	48 63 d2             	movslq %edx,%rdx
  4032c6:	48 89 d1             	mov    %rdx,%rcx
  4032c9:	48 c1 e1 0a          	shl    $0xa,%rcx
  4032cd:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4032d4:	48 01 ca             	add    %rcx,%rdx
  4032d7:	48 8b 92 00 01 00 00 	mov    0x100(%rdx),%rdx
  4032de:	48 29 d0             	sub    %rdx,%rax
  4032e1:	48 89 c6             	mov    %rax,%rsi
  4032e4:	48 8d 05 49 0f 00 00 	lea    0xf49(%rip),%rax        # 404234 <_IO_stdin_used+0x234>
  4032eb:	48 89 c7             	mov    %rax,%rdi
  4032ee:	b8 00 00 00 00       	mov    $0x0,%eax
  4032f3:	e8 88 dd ff ff       	call   401080 <printf@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  4032f8:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4032fe:	48 98                	cltq
  403300:	48 c1 e0 0a          	shl    $0xa,%rax
  403304:	48 89 c2             	mov    %rax,%rdx
  403307:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40330e:	48 01 d0             	add    %rdx,%rax
  403311:	48 8b 80 40 01 00 00 	mov    0x140(%rax),%rax
  403318:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  40331e:	48 63 d2             	movslq %edx,%rdx
  403321:	48 89 d1             	mov    %rdx,%rcx
  403324:	48 c1 e1 0a          	shl    $0xa,%rcx
  403328:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  40332f:	48 01 ca             	add    %rcx,%rdx
  403332:	48 8b 92 30 01 00 00 	mov    0x130(%rdx),%rdx
  403339:	48 29 d0             	sub    %rdx,%rax
  40333c:	48 89 c6             	mov    %rax,%rsi
  40333f:	48 8d 05 f3 0e 00 00 	lea    0xef3(%rip),%rax        # 404239 <_IO_stdin_used+0x239>
  403346:	48 89 c7             	mov    %rax,%rdi
  403349:	b8 00 00 00 00       	mov    $0x0,%eax
  40334e:	e8 2d dd ff ff       	call   401080 <printf@plt>
  for (int x = 0; x < 1 ;  x++){
  403353:	83 85 b4 fe ff ff 01 	addl   $0x1,-0x14c(%rbp)
  40335a:	83 bd b4 fe ff ff 00 	cmpl   $0x0,-0x14c(%rbp)
  403361:	0f 8e 6f fd ff ff    	jle    4030d6 <main+0x1047>
  } 
  printf("%ld good reads per second\n", goods / seconds);
  403367:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  40336d:	48 63 d8             	movslq %eax,%rbx
  403370:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
  403377:	48 99                	cqto
  403379:	48 f7 fb             	idiv   %rbx
  40337c:	48 89 c6             	mov    %rax,%rsi
  40337f:	48 8d 05 bb 0e 00 00 	lea    0xebb(%rip),%rax        # 404241 <_IO_stdin_used+0x241>
  403386:	48 89 c7             	mov    %rax,%rdi
  403389:	b8 00 00 00 00       	mov    $0x0,%eax
  40338e:	e8 ed dc ff ff       	call   401080 <printf@plt>
  printf("%ld good reads per second latency\n", 1000000000 / (goods / seconds));
  403393:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  403399:	48 63 d8             	movslq %eax,%rbx
  40339c:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
  4033a3:	48 99                	cqto
  4033a5:	48 f7 fb             	idiv   %rbx
  4033a8:	48 89 c3             	mov    %rax,%rbx
  4033ab:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  4033b0:	48 99                	cqto
  4033b2:	48 f7 fb             	idiv   %rbx
  4033b5:	48 89 c6             	mov    %rax,%rsi
  4033b8:	48 8d 05 a1 0e 00 00 	lea    0xea1(%rip),%rax        # 404260 <_IO_stdin_used+0x260>
  4033bf:	48 89 c7             	mov    %rax,%rdi
  4033c2:	b8 00 00 00 00       	mov    $0x0,%eax
  4033c7:	e8 b4 dc ff ff       	call   401080 <printf@plt>
     }
   fclose(out_file);
   
 }

  char * filename = calloc(100, sizeof(char));
  4033cc:	be 01 00 00 00       	mov    $0x1,%esi
  4033d1:	bf 64 00 00 00       	mov    $0x64,%edi
  4033d6:	e8 f5 dc ff ff       	call   4010d0 <calloc@plt>
  4033db:	48 89 45 88          	mov    %rax,-0x78(%rbp)
  char * buf = calloc(1000, sizeof(char));
  4033df:	be 01 00 00 00       	mov    $0x1,%esi
  4033e4:	bf e8 03 00 00       	mov    $0x3e8,%edi
  4033e9:	e8 e2 dc ff ff       	call   4010d0 <calloc@plt>
  4033ee:	48 89 45 90          	mov    %rax,-0x70(%rbp)
  memset(filename, 0, 100);
  4033f2:	48 8b 45 88          	mov    -0x78(%rbp),%rax
  4033f6:	ba 64 00 00 00       	mov    $0x64,%edx
  4033fb:	be 00 00 00 00       	mov    $0x0,%esi
  403400:	48 89 c7             	mov    %rax,%rdi
  403403:	e8 b8 dc ff ff       	call   4010c0 <memset@plt>
  snprintf(filename, 100, "coroutine.struct");
  403408:	48 8b 45 88          	mov    -0x78(%rbp),%rax
  40340c:	48 8d 15 70 0e 00 00 	lea    0xe70(%rip),%rdx        # 404283 <_IO_stdin_used+0x283>
  403413:	be 64 00 00 00       	mov    $0x64,%esi
  403418:	48 89 c7             	mov    %rax,%rdi
  40341b:	b8 00 00 00 00       	mov    $0x0,%eax
  403420:	e8 6b dc ff ff       	call   401090 <snprintf@plt>
  FILE *out_file = fopen(filename, "w");
  403425:	48 8b 45 88          	mov    -0x78(%rbp),%rax
  403429:	48 8d 15 64 0e 00 00 	lea    0xe64(%rip),%rdx        # 404294 <_IO_stdin_used+0x294>
  403430:	48 89 d6             	mov    %rdx,%rsi
  403433:	48 89 c7             	mov    %rax,%rdi
  403436:	e8 b5 dc ff ff       	call   4010f0 <fopen@plt>
  40343b:	48 89 45 98          	mov    %rax,-0x68(%rbp)

memset(buf, 0, 1000);
  40343f:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403443:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403448:	be 00 00 00 00       	mov    $0x0,%esi
  40344d:	48 89 c7             	mov    %rax,%rdi
  403450:	e8 6b dc ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "index %ld\n", offsetof(struct Coroutine, index));
  403455:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403459:	b9 00 00 00 00       	mov    $0x0,%ecx
  40345e:	48 8d 15 31 0e 00 00 	lea    0xe31(%rip),%rdx        # 404296 <_IO_stdin_used+0x296>
  403465:	be 64 00 00 00       	mov    $0x64,%esi
  40346a:	48 89 c7             	mov    %rax,%rdi
  40346d:	b8 00 00 00 00       	mov    $0x0,%eax
  403472:	e8 19 dc ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  403477:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  40347b:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40347f:	48 89 d6             	mov    %rdx,%rsi
  403482:	48 89 c7             	mov    %rax,%rdi
  403485:	e8 26 dc ff ff       	call   4010b0 <fputs@plt>
  
  memset(buf, 0, 1000);
  40348a:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40348e:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403493:	be 00 00 00 00       	mov    $0x0,%esi
  403498:	48 89 c7             	mov    %rax,%rdi
  40349b:	e8 20 dc ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "rsp %ld\n", offsetof(struct Coroutine, rsp));
  4034a0:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4034a4:	b9 08 00 00 00       	mov    $0x8,%ecx
  4034a9:	48 8d 15 f1 0d 00 00 	lea    0xdf1(%rip),%rdx        # 4042a1 <_IO_stdin_used+0x2a1>
  4034b0:	be 64 00 00 00       	mov    $0x64,%esi
  4034b5:	48 89 c7             	mov    %rax,%rdi
  4034b8:	b8 00 00 00 00       	mov    $0x0,%eax
  4034bd:	e8 ce db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  4034c2:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  4034c6:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4034ca:	48 89 d6             	mov    %rdx,%rsi
  4034cd:	48 89 c7             	mov    %rax,%rdi
  4034d0:	e8 db db ff ff       	call   4010b0 <fputs@plt>
  
  memset(buf, 0, 1000);
  4034d5:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4034d9:	ba e8 03 00 00       	mov    $0x3e8,%edx
  4034de:	be 00 00 00 00       	mov    $0x0,%esi
  4034e3:	48 89 c7             	mov    %rax,%rdi
  4034e6:	e8 d5 db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "eip %ld\n", offsetof(struct Coroutine, eip));
  4034eb:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4034ef:	b9 10 00 00 00       	mov    $0x10,%ecx
  4034f4:	48 8d 15 af 0d 00 00 	lea    0xdaf(%rip),%rdx        # 4042aa <_IO_stdin_used+0x2aa>
  4034fb:	be 64 00 00 00       	mov    $0x64,%esi
  403500:	48 89 c7             	mov    %rax,%rdi
  403503:	b8 00 00 00 00       	mov    $0x0,%eax
  403508:	e8 83 db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  40350d:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  403511:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403515:	48 89 d6             	mov    %rdx,%rsi
  403518:	48 89 c7             	mov    %rax,%rdi
  40351b:	e8 90 db ff ff       	call   4010b0 <fputs@plt>


  memset(buf, 0, 1000);
  403520:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403524:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403529:	be 00 00 00 00       	mov    $0x0,%esi
  40352e:	48 89 c7             	mov    %rax,%rdi
  403531:	e8 8a db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "data %ld\n", offsetof(struct Coroutine, data));
  403536:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40353a:	b9 18 00 00 00       	mov    $0x18,%ecx
  40353f:	48 8d 15 6d 0d 00 00 	lea    0xd6d(%rip),%rdx        # 4042b3 <_IO_stdin_used+0x2b3>
  403546:	be 64 00 00 00       	mov    $0x64,%esi
  40354b:	48 89 c7             	mov    %rax,%rdi
  40354e:	b8 00 00 00 00       	mov    $0x0,%eax
  403553:	e8 38 db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  403558:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  40355c:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403560:	48 89 d6             	mov    %rdx,%rsi
  403563:	48 89 c7             	mov    %rax,%rdi
  403566:	e8 45 db ff ff       	call   4010b0 <fputs@plt>

  memset(buf, 0, 1000);
  40356b:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40356f:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403574:	be 00 00 00 00       	mov    $0x0,%esi
  403579:	48 89 c7             	mov    %rax,%rdi
  40357c:	e8 3f db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "corourinedata.running %ld\n", offsetof(struct CoroutineData, running));
  403581:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403585:	b9 00 00 00 00       	mov    $0x0,%ecx
  40358a:	48 8d 15 2c 0d 00 00 	lea    0xd2c(%rip),%rdx        # 4042bd <_IO_stdin_used+0x2bd>
  403591:	be 64 00 00 00       	mov    $0x64,%esi
  403596:	48 89 c7             	mov    %rax,%rdi
  403599:	b8 00 00 00 00       	mov    $0x0,%eax
  40359e:	e8 ed da ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  4035a3:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  4035a7:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4035ab:	48 89 d6             	mov    %rdx,%rsi
  4035ae:	48 89 c7             	mov    %rax,%rdi
  4035b1:	e8 fa da ff ff       	call   4010b0 <fputs@plt>

  memset(buf, 0, 1000);
  4035b6:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4035ba:	ba e8 03 00 00       	mov    $0x3e8,%edx
  4035bf:	be 00 00 00 00       	mov    $0x0,%esi
  4035c4:	48 89 c7             	mov    %rax,%rdi
  4035c7:	e8 f4 da ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "size coroutine %ld\n", sizeof(struct Coroutine));
  4035cc:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4035d0:	b9 20 00 00 00       	mov    $0x20,%ecx
  4035d5:	48 8d 15 fc 0c 00 00 	lea    0xcfc(%rip),%rdx        # 4042d8 <_IO_stdin_used+0x2d8>
  4035dc:	be 64 00 00 00       	mov    $0x64,%esi
  4035e1:	48 89 c7             	mov    %rax,%rdi
  4035e4:	b8 00 00 00 00       	mov    $0x0,%eax
  4035e9:	e8 a2 da ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  4035ee:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  4035f2:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4035f6:	48 89 d6             	mov    %rdx,%rsi
  4035f9:	48 89 c7             	mov    %rax,%rdi
  4035fc:	e8 af da ff ff       	call   4010b0 <fputs@plt>

memset(buf, 0, 1000);
  403601:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403605:	ba e8 03 00 00       	mov    $0x3e8,%edx
  40360a:	be 00 00 00 00       	mov    $0x0,%esi
  40360f:	48 89 c7             	mov    %rax,%rdi
  403612:	e8 a9 da ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "scheduler.rsp %ld\n", offsetof(struct Scheduler, rsp));
  403617:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40361b:	b9 00 00 00 00       	mov    $0x0,%ecx
  403620:	48 8d 15 c5 0c 00 00 	lea    0xcc5(%rip),%rdx        # 4042ec <_IO_stdin_used+0x2ec>
  403627:	be 64 00 00 00       	mov    $0x64,%esi
  40362c:	48 89 c7             	mov    %rax,%rdi
  40362f:	b8 00 00 00 00       	mov    $0x0,%eax
  403634:	e8 57 da ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  403639:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  40363d:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403641:	48 89 d6             	mov    %rdx,%rsi
  403644:	48 89 c7             	mov    %rax,%rdi
  403647:	e8 64 da ff ff       	call   4010b0 <fputs@plt>
  
  
  fclose(out_file);
  40364c:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403650:	48 89 c7             	mov    %rax,%rdi
  403653:	e8 08 da ff ff       	call   401060 <fclose@plt>
  403658:	b8 00 00 00 00       	mov    $0x0,%eax
  40365d:	48 8b 55 e8          	mov    -0x18(%rbp),%rdx
  403661:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  40366a:	74 05                	je     403671 <main+0x15e2>
  40366c:	e8 ff d9 ff ff       	call   401070 <__stack_chk_fail@plt>
  403671:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
  403675:	c9                   	leave
  403676:	c3                   	ret
  403677:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000403680 <.MSG>:
  403680:	43                   	rex.XB
  403681:	4f 20 43 6f          	rex.WRXB and %r8b,0x6f(%r11)
  403685:	72 6f                	jb     4036f6 <.CURSTACK+0x4>
  403687:	75 74                	jne    4036fd <.CURSTACK+0xb>
  403689:	69 6e 65 53 74 72 75 	imul   $0x75727453,0x65(%rsi),%ebp
  403690:	63 74 20 25          	movsxd 0x25(%rax,%riz,1),%esi
  403694:	78 0a                	js     4036a0 <.EIP+0x9>
	...

0000000000403697 <.EIP>:
  403697:	43                   	rex.XB
  403698:	4f 20 45 49          	rex.WRXB and %r8b,0x49(%r13)
  40369c:	50                   	push   %rax
  40369d:	2e                   	cs
  40369e:	2e                   	cs
  40369f:	2e                   	cs
  4036a0:	20                   	.byte 0x20
  4036a1:	25                   	.byte 0x25
  4036a2:	78 0a                	js     4036ae <.CODATA+0x9>
	...

00000000004036a5 <.CODATA>:
  4036a5:	43                   	rex.XB
  4036a6:	4f 20 63 6f          	rex.WRXB and %r12b,0x6f(%r11)
  4036aa:	64 61                	fs (bad)
  4036ac:	74 61                	je     40370f <.SCHED+0xc>
  4036ae:	2e                   	cs
  4036af:	2e                   	cs
  4036b0:	2e                   	cs
  4036b1:	20                   	.byte 0x20
  4036b2:	25                   	.byte 0x25
  4036b3:	78 0a                	js     4036bf <.INDEX+0x9>
	...

00000000004036b6 <.INDEX>:
  4036b6:	43 6f                	rex.XB outsl %ds:(%rsi),(%dx)
  4036b8:	72 6f                	jb     403729 <switch_to+0x16>
  4036ba:	75 74                	jne    403730 <switch_to+0x1d>
  4036bc:	69 6e 65 20 69 6e 64 	imul   $0x646e6920,0x65(%rsi),%ebp
  4036c3:	65 78 2e             	gs js  4036f4 <.CURSTACK+0x2>
  4036c6:	2e                   	cs
  4036c7:	2e                   	cs
  4036c8:	20                   	.byte 0x20
  4036c9:	25                   	.byte 0x25
  4036ca:	64 0a 00             	or     %fs:(%rax),%al

00000000004036cd <.RET>:
  4036cd:	52                   	push   %rdx
  4036ce:	65 74 75             	gs je  403746 <switch_to+0x33>
  4036d1:	72 6e                	jb     403741 <switch_to+0x2e>
  4036d3:	65 64 53             	gs fs push %rbx
  4036d6:	74 61                	je     403739 <switch_to+0x26>
  4036d8:	63 6b 2e             	movsxd 0x2e(%rbx),%ebp
  4036db:	2e                   	cs
  4036dc:	2e                   	cs
  4036dd:	20                   	.byte 0x20
  4036de:	25                   	.byte 0x25
  4036df:	70 0a                	jo     4036eb <.STACK+0x9>
	...

00000000004036e2 <.STACK>:
  4036e2:	43                   	rex.XB
  4036e3:	4f 20 53 74          	rex.WRXB and %r10b,0x74(%r11)
  4036e7:	61                   	(bad)
  4036e8:	63 6b 2e             	movsxd 0x2e(%rbx),%ebp
  4036eb:	2e                   	cs
  4036ec:	2e                   	cs
  4036ed:	20                   	.byte 0x20
  4036ee:	25                   	.byte 0x25
  4036ef:	70 0a                	jo     4036fb <.CURSTACK+0x9>
	...

00000000004036f2 <.CURSTACK>:
  4036f2:	53                   	push   %rbx
  4036f3:	61                   	(bad)
  4036f4:	76 65                	jbe    40375b <switch_to+0x48>
  4036f6:	64 53                	fs push %rbx
  4036f8:	74 61                	je     40375b <switch_to+0x48>
  4036fa:	63 6b 2e             	movsxd 0x2e(%rbx),%ebp
  4036fd:	2e                   	cs
  4036fe:	20                   	.byte 0x20
  4036ff:	25                   	.byte 0x25
  403700:	70 0a                	jo     40370c <.SCHED+0x9>
	...

0000000000403703 <.SCHED>:
  403703:	53                   	push   %rbx
  403704:	63 68 65             	movsxd 0x65(%rax),%ebp
  403707:	64 75 6c             	fs jne 403776 <switch_to+0x63>
  40370a:	65 72 2e             	gs jb  40373b <switch_to+0x28>
  40370d:	2e                   	cs
  40370e:	20                   	.byte 0x20
  40370f:	25                   	.byte 0x25
  403710:	70 0a                	jo     40371c <switch_to+0x9>
	...

0000000000403713 <switch_to>:
	.text
	# switch_to(struct Coroutine * coroutines, int index, struct Scheduler * scheduler)
	# rdi, %rsi, %rdx, %rcx, %r8 and %r9
switch_to:
# popq %r11
pushq %rbp
  403713:	55                   	push   %rbp

movq %rsp, %rbp
  403714:	48 89 e5             	mov    %rsp,%rbp
subq $1024, %rsp
  403717:	48 81 ec 00 04 00 00 	sub    $0x400,%rsp



movq %rdi, -56(%rbp) # coroutine table
  40371e:	48 89 7d c8          	mov    %rdi,-0x38(%rbp)
movq %rsi, -8(%rbp) # index
  403722:	48 89 75 f8          	mov    %rsi,-0x8(%rbp)
movq %rdx, -16(%rbp) # scheduler
  403726:	48 89 55 f0          	mov    %rdx,-0x10(%rbp)


movq %rsi, %rax
  40372a:	48 89 f0             	mov    %rsi,%rax
imul $32, %rax
  40372d:	48 6b c0 20          	imul   $0x20,%rax,%rax
addq %rdi, %rax
  403731:	48 01 f8             	add    %rdi,%rax
mov %rax, %r11
  403734:	49 89 c3             	mov    %rax,%r11

mov %r11, %rax
  403737:	4c 89 d8             	mov    %r11,%rax
movq %rax, %r9
  40373a:	49 89 c1             	mov    %rax,%r9
movq %r9, -24(%rbp) # coroutine object
  40373d:	4c 89 4d e8          	mov    %r9,-0x18(%rbp)

movq %r11, %rax
  403741:	4c 89 d8             	mov    %r11,%rax
leaq 8(%rax), %rax
  403744:	48 8d 40 08          	lea    0x8(%rax),%rax
movq %rax, %r9
  403748:	49 89 c1             	mov    %rax,%r9
movq %r9, -48(%rbp) # rsp
  40374b:	4c 89 4d d0          	mov    %r9,-0x30(%rbp)

movq %r11, %rax
  40374f:	4c 89 d8             	mov    %r11,%rax
leaq 16(%rax), %rax
  403752:	48 8d 40 10          	lea    0x10(%rax),%rax
movq (%rax), %r9
  403756:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -32(%rbp) # coroutine function
  403759:	4c 89 4d e0          	mov    %r9,-0x20(%rbp)

movq %r11, %rax
  40375d:	4c 89 d8             	mov    %r11,%rax
leaq 8(%rax), %rax
  403760:	48 8d 40 08          	lea    0x8(%rax),%rax
movq (%rax), %r9
  403764:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -64(%rbp) # coroutine stack
  403767:	4c 89 4d c0          	mov    %r9,-0x40(%rbp)

movq %r11, %rax
  40376b:	4c 89 d8             	mov    %r11,%rax
leaq 24(%rax), %rax # load from coroutine object data object
  40376e:	48 8d 40 18          	lea    0x18(%rax),%rax
movq (%rax), %r9
  403772:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -40(%rbp) # coroutine data object
  403775:	4c 89 4d d8          	mov    %r9,-0x28(%rbp)
movq (%rax), %rcx
  403779:	48 8b 08             	mov    (%rax),%rcx

movq -24(%rbp), %r11
  40377c:	4c 8b 5d e8          	mov    -0x18(%rbp),%r11
#

leaq .INDEX(%rip), %rdi
  403780:	48 8d 3d 2f ff ff ff 	lea    -0xd1(%rip),%rdi        # 4036b6 <.INDEX>
#call printf@plt
mov $0, %eax
  403787:	b8 00 00 00 00       	mov    $0x0,%eax

#pushq %r11
leaq .MSG(%rip), %rdi
  40378c:	48 8d 3d ed fe ff ff 	lea    -0x113(%rip),%rdi        # 403680 <.MSG>
movq %r11, %rsi
  403793:	4c 89 de             	mov    %r11,%rsi
# call printf@plt
mov $0, %eax
  403796:	b8 00 00 00 00       	mov    $0x0,%eax

leaq .SCHED(%rip), %rdi
  40379b:	48 8d 3d 61 ff ff ff 	lea    -0x9f(%rip),%rdi        # 403703 <.SCHED>
movq -16(%rbp), %rsi
  4037a2:	48 8b 75 f0          	mov    -0x10(%rbp),%rsi
call printf@plt
  4037a6:	e8 d5 d8 ff ff       	call   401080 <printf@plt>
mov $0, %eax
  4037ab:	b8 00 00 00 00       	mov    $0x0,%eax

#popq %r11

#pushq %r9
movq -32(%rbp), %r9
  4037b0:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9

leaq .EIP(%rip), %rdi
  4037b4:	48 8d 3d dc fe ff ff 	lea    -0x124(%rip),%rdi        # 403697 <.EIP>
movq %r9, %rsi
  4037bb:	4c 89 ce             	mov    %r9,%rsi
#call printf@plt
mov $0, %eax
  4037be:	b8 00 00 00 00       	mov    $0x0,%eax
#popq %r9
# coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data

#pushq %r9
leaq .CODATA(%rip), %rdi
  4037c3:	48 8d 3d db fe ff ff 	lea    -0x125(%rip),%rdi        # 4036a5 <.CODATA>
movq -40(%rbp), %rsi
  4037ca:	48 8b 75 d8          	mov    -0x28(%rbp),%rsi
#call printf@plt
mov $0, %eax
  4037ce:	b8 00 00 00 00       	mov    $0x0,%eax





movq -16(%rbp), %rax
  4037d3:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
movq %rsp, 0(%rax)
  4037d7:	48 89 20             	mov    %rsp,(%rax)

leaq .CURSTACK(%rip), %rdi
  4037da:	48 8d 3d 11 ff ff ff 	lea    -0xef(%rip),%rdi        # 4036f2 <.CURSTACK>
movq 0(%rax), %rsi
  4037e1:	48 8b 30             	mov    (%rax),%rsi
call printf@plt
  4037e4:	e8 97 d8 ff ff       	call   401080 <printf@plt>
mov $0, %eax
  4037e9:	b8 00 00 00 00       	mov    $0x0,%eax





leaq .STACK(%rip), %rdi
  4037ee:	48 8d 3d ed fe ff ff 	lea    -0x113(%rip),%rdi        # 4036e2 <.STACK>
movq -64(%rbp), %rsi
  4037f5:	48 8b 75 c0          	mov    -0x40(%rbp),%rsi
call printf@plt
  4037f9:	e8 82 d8 ff ff       	call   401080 <printf@plt>
mov $0, %eax
  4037fe:	b8 00 00 00 00       	mov    $0x0,%eax

movq -64(%rbp), %rsp # set stack to coroutine
  403803:	48 8b 65 c0          	mov    -0x40(%rbp),%rsp

movq -32(%rbp), %r9
  403807:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9
leaq after(%rip), %r11
  40380b:	4c 8d 1d 0f 00 00 00 	lea    0xf(%rip),%r11        # 403821 <after>
#sub $8, %rsp
#movq %r11, (%rsp) # set stack return address

movq -16(%rbp), %rdi
  403812:	48 8b 7d f0          	mov    -0x10(%rbp),%rdi
movq -24(%rbp), %rsi
  403816:	48 8b 75 e8          	mov    -0x18(%rbp),%rsi
movq -40(%rbp), %rdx
  40381a:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx

# pushq %rbp
#jmp *%r9
call *%r9
  40381e:	41 ff d1             	call   *%r9

0000000000403821 <after>:
# pushq %rbp
# popq %rbp
#movq %rsp, %rbp

#pushq %rax
movq %rax, %rsp
  403821:	48 89 c4             	mov    %rax,%rsp
# movq %rsp, %rbp

leaq .RET(%rip), %rdi
  403824:	48 8d 3d a2 fe ff ff 	lea    -0x15e(%rip),%rdi        # 4036cd <.RET>
movq %rax, %rsi
  40382b:	48 89 c6             	mov    %rax,%rsi
call printf@plt
  40382e:	e8 4d d8 ff ff       	call   401080 <printf@plt>
mov $0, %eax
  403833:	b8 00 00 00 00       	mov    $0x0,%eax




#pop %rbp
add $1024, %rsp
  403838:	48 81 c4 00 04 00 00 	add    $0x400,%rsp
#movq %rsp, %rbp
popq %rbp
  40383f:	5d                   	pop    %rbp
  403840:	c3                   	ret

Disassembly of section .fini:

0000000000403844 <_fini>:
  403844:	f3 0f 1e fa          	endbr64
  403848:	48 83 ec 08          	sub    $0x8,%rsp
  40384c:	48 83 c4 08          	add    $0x8,%rsp
  403850:	c3                   	ret
