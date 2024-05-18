
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
  401148:	48 c7 c7 90 20 40 00 	mov    $0x402090,%rdi
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

int coroutine_func(void) {
  40121d:	55                   	push   %rbp
  40121e:	48 89 e5             	mov    %rsp,%rbp
  401221:	48 83 ec 20          	sub    $0x20,%rsp
  struct Scheduler * scheduler;
  struct Coroutine * coroutine;
  struct CoroutineData * data;
  
  asm("movq %%rdi, %0" : "=r" (scheduler));
  401225:	48 89 f8             	mov    %rdi,%rax
  401228:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  asm ("movq %%rsi, %0" : "=r" (coroutine)::);
  40122c:	48 89 f0             	mov    %rsi,%rax
  40122f:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
asm ("movq %%rdx, %0" : "=r" (data)::);    
  401233:	48 89 d0             	mov    %rdx,%rax
  401236:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
// struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data) {
 printf("%p %p %p coro\n", scheduler, coroutine, data);
  40123a:	48 8b 4d f8          	mov    -0x8(%rbp),%rcx
  40123e:	48 8b 55 f0          	mov    -0x10(%rbp),%rdx
  401242:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401246:	48 89 c6             	mov    %rax,%rsi
  401249:	48 8d 05 b8 2d 00 00 	lea    0x2db8(%rip),%rax        # 404008 <_IO_stdin_used+0x8>
  401250:	48 89 c7             	mov    %rax,%rdi
  401253:	b8 00 00 00 00       	mov    $0x0,%eax
  401258:	e8 23 fe ff ff       	call   401080 <printf@plt>
   
  //while (data->running == 1) {
   printf("%ld\n", coroutine->eip); 
  40125d:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401261:	48 8b 40 10          	mov    0x10(%rax),%rax
  401265:	48 89 c6             	mov    %rax,%rsi
  401268:	48 8d 05 a8 2d 00 00 	lea    0x2da8(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  40126f:	48 89 c7             	mov    %rax,%rdi
  401272:	b8 00 00 00 00       	mov    $0x0,%eax
  401277:	e8 04 fe ff ff       	call   401080 <printf@plt>
  asm("lea 0(%%rip), %%r11\n"
  40127c:	4c 8d 1d 00 00 00 00 	lea    0x0(%rip),%r11        # 401283 <coroutine_func+0x66>
  401283:	4c 89 da             	mov    %r11,%rdx
  401286:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  40128a:	48 89 50 10          	mov    %rdx,0x10(%rax)
      "movq %%r11, %0" : "=rm" (coroutine->eip) ::"r11");
    
    // yield(1, scheduler, coroutine)
  printf("coro resumed\n");
  40128e:	48 8d 05 87 2d 00 00 	lea    0x2d87(%rip),%rax        # 40401c <_IO_stdin_used+0x1c>
  401295:	48 89 c7             	mov    %rax,%rdi
  401298:	e8 a3 fd ff ff       	call   401040 <puts@plt>
  asm("movq %0, %%rsp" ::"r"(scheduler->rsp));
  40129d:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4012a1:	48 8b 00             	mov    (%rax),%rax
  4012a4:	48 89 c4             	mov    %rax,%rsp
 // }
  //printf("loop finished\n");
  return 0; 
  4012a7:	b8 00 00 00 00       	mov    $0x0,%eax

 
}
  4012ac:	c9                   	leave
  4012ad:	c3                   	ret

00000000004012ae <pollthreads>:
// thread 2
if tasks.taskindex > threads[0].workindex:
  value = 2
*/

int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4012ae:	55                   	push   %rbp
  4012af:	48 89 e5             	mov    %rsp,%rbp
  4012b2:	48 89 7d d8          	mov    %rdi,-0x28(%rbp)
  4012b6:	48 89 75 d0          	mov    %rsi,-0x30(%rbp)
  4012ba:	48 89 55 c8          	mov    %rdx,-0x38(%rbp)
  4012be:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
  4012c2:	4c 89 45 b8          	mov    %r8,-0x48(%rbp)
  long WM = WRITE_MASK;
  4012c6:	48 c7 45 f0 04 00 00 00 	movq   $0x4,-0x10(%rbp)
  long RM = READ_MASK;
  4012ce:	48 c7 45 f8 08 00 00 00 	movq   $0x8,-0x8(%rbp)
  for (int x = 1; x < data->threadsize ; x++) {
  4012d6:	c7 45 e8 01 00 00 00 	movl   $0x1,-0x18(%rbp)
  4012dd:	e9 9b 00 00 00       	jmp    40137d <pollthreads+0xcf>
  // printf("thread %d %ld\n", x, data->threads[x].ready);
    int mask = data->threads[1].readies[x];
  4012e2:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4012e6:	48 8b 40 30          	mov    0x30(%rax),%rax
  4012ea:	48 05 00 04 00 00    	add    $0x400,%rax
  4012f0:	48 8b 50 20          	mov    0x20(%rax),%rdx
  4012f4:	8b 45 e8             	mov    -0x18(%rbp),%eax
  4012f7:	48 98                	cltq
  4012f9:	48 c1 e0 02          	shl    $0x2,%rax
  4012fd:	48 01 d0             	add    %rdx,%rax
  401300:	8b 00                	mov    (%rax),%eax
  401302:	89 45 ec             	mov    %eax,-0x14(%rbp)
        //printf("pollpread? %ld %ld\n", mask, (mask & PREP_READ_MASK));
       // printf("pplreadmask? %ld %ld\n", mask, (mask & READ_MASK));
      //  printf("pollwritemask ? %ld %ld\n", mask, (mask & WRITE_MASK));
       // data->threads[x].newmask = 0;
        
        if ((mask & WM) == WM || mask == 0) {
  401305:	8b 45 ec             	mov    -0x14(%rbp),%eax
  401308:	48 98                	cltq
  40130a:	48 23 45 f0          	and    -0x10(%rbp),%rax
  40130e:	48 39 45 f0          	cmp    %rax,-0x10(%rbp)
  401312:	74 06                	je     40131a <pollthreads+0x6c>
  401314:	83 7d ec 00          	cmpl   $0x0,-0x14(%rbp)
  401318:	75 25                	jne    40133f <pollthreads+0x91>
         //printf("found a writer\n");
          readywriters[(*writers)++] = x;
  40131a:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  40131e:	8b 00                	mov    (%rax),%eax
  401320:	8d 48 01             	lea    0x1(%rax),%ecx
  401323:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
  401327:	89 0a                	mov    %ecx,(%rdx)
  401329:	48 98                	cltq
  40132b:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401333:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
  401337:	48 01 c2             	add    %rax,%rdx
  40133a:	8b 45 e8             	mov    -0x18(%rbp),%eax
  40133d:	89 02                	mov    %eax,(%rdx)
        }
    if ((mask & RM) == RM || mask == 0) {
  40133f:	8b 45 ec             	mov    -0x14(%rbp),%eax
  401342:	48 98                	cltq
  401344:	48 23 45 f8          	and    -0x8(%rbp),%rax
  401348:	48 39 45 f8          	cmp    %rax,-0x8(%rbp)
  40134c:	74 06                	je     401354 <pollthreads+0xa6>
  40134e:	83 7d ec 00          	cmpl   $0x0,-0x14(%rbp)
  401352:	75 25                	jne    401379 <pollthreads+0xcb>
      readyreaders[(*readers)++] = x;
  401354:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
  401358:	8b 00                	mov    (%rax),%eax
  40135a:	8d 48 01             	lea    0x1(%rax),%ecx
  40135d:	48 8b 55 c0          	mov    -0x40(%rbp),%rdx
  401361:	89 0a                	mov    %ecx,(%rdx)
  401363:	48 98                	cltq
  401365:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  40136d:	48 8b 45 d0          	mov    -0x30(%rbp),%rax
  401371:	48 01 c2             	add    %rax,%rdx
  401374:	8b 45 e8             	mov    -0x18(%rbp),%eax
  401377:	89 02                	mov    %eax,(%rdx)
  for (int x = 1; x < data->threadsize ; x++) {
  401379:	83 45 e8 01          	addl   $0x1,-0x18(%rbp)
  40137d:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401381:	8b 40 68             	mov    0x68(%rax),%eax
  401384:	39 45 e8             	cmp    %eax,-0x18(%rbp)
  401387:	0f 8c 55 ff ff ff    	jl     4012e2 <pollthreads+0x34>
    // printf("found a reader\n");
    }
      }
  // printf("%d readers %d writers\n", *readers, *writers);
      
  return 0;
  40138d:	b8 00 00 00 00       	mov    $0x0,%eax
}
  401392:	5d                   	pop    %rbp
  401393:	c3                   	ret

0000000000401394 <findavailable>:


int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401394:	55                   	push   %rbp
  401395:	48 89 e5             	mov    %rsp,%rbp
  401398:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  40139c:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
  4013a0:	48 89 55 d8          	mov    %rdx,-0x28(%rbp)
  4013a4:	48 89 4d d0          	mov    %rcx,-0x30(%rbp)
  4013a8:	4c 89 45 c8          	mov    %r8,-0x38(%rbp)
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4013ac:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
  4013b3:	eb 64                	jmp    401419 <findavailable+0x85>
        
        if (data->freelist[x].available == FREE ) {
  4013b5:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4013b9:	48 8b 90 a0 00 00 00 	mov    0xa0(%rax),%rdx
  4013c0:	8b 45 fc             	mov    -0x4(%rbp),%eax
  4013c3:	48 98                	cltq
  4013c5:	48 c1 e0 05          	shl    $0x5,%rax
  4013c9:	48 01 d0             	add    %rdx,%rax
  4013cc:	8b 40 10             	mov    0x10(%rax),%eax
  4013cf:	83 f8 01             	cmp    $0x1,%eax
  4013d2:	75 41                	jne    401415 <findavailable+0x81>
          //printf("%d\n", *availableidx);
         available[*availableidx] = x;
  4013d4:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013d8:	8b 00                	mov    (%rax),%eax
  4013da:	48 98                	cltq
  4013dc:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4013e4:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  4013e8:	48 01 c2             	add    %rax,%rdx
  4013eb:	8b 45 fc             	mov    -0x4(%rbp),%eax
  4013ee:	48 98                	cltq
  4013f0:	48 89 02             	mov    %rax,(%rdx)
         (*availableidx)++;
  4013f3:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013f7:	8b 00                	mov    (%rax),%eax
  4013f9:	8d 50 01             	lea    0x1(%rax),%edx
  4013fc:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401400:	89 10                	mov    %edx,(%rax)
         if ((*availableidx) == data->threadsize * 2) {
  401402:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401406:	8b 10                	mov    (%rax),%edx
  401408:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  40140c:	8b 40 68             	mov    0x68(%rax),%eax
  40140f:	01 c0                	add    %eax,%eax
  401411:	39 c2                	cmp    %eax,%edx
  401413:	74 20                	je     401435 <findavailable+0xa1>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401415:	83 45 fc 01          	addl   $0x1,-0x4(%rbp)
  401419:	8b 45 fc             	mov    -0x4(%rbp),%eax
  40141c:	48 63 d0             	movslq %eax,%rdx
  40141f:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401423:	48 8b 80 b8 00 00 00 	mov    0xb8(%rax),%rax
  40142a:	48 83 c0 01          	add    $0x1,%rax
  40142e:	48 39 c2             	cmp    %rax,%rdx
  401431:	7c 82                	jl     4013b5 <findavailable+0x21>
  401433:	eb 01                	jmp    401436 <findavailable+0xa2>
           break;
  401435:	90                   	nop
         }

         // printf("%d chunk is free\n", x);
        }
      }
      if (*availableidx == 0) {
  401436:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  40143a:	8b 00                	mov    (%rax),%eax
  40143c:	85 c0                	test   %eax,%eax
  40143e:	75 07                	jne    401447 <findavailable+0xb3>
       //printf("no chunks avail\n");
        
        return 1;
  401440:	b8 01 00 00 00       	mov    $0x1,%eax
  401445:	eb 05                	jmp    40144c <findavailable+0xb8>
      }
  return 0;
  401447:	b8 00 00 00 00       	mov    $0x0,%eax
}
  40144c:	5d                   	pop    %rbp
  40144d:	c3                   	ret

000000000040144e <singlewriter3>:

int singlewriter3(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40144e:	55                   	push   %rbp
  40144f:	48 89 e5             	mov    %rsp,%rbp
  401452:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  401456:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
  40145a:	48 89 55 d8          	mov    %rdx,-0x28(%rbp)
  40145e:	48 89 4d d0          	mov    %rcx,-0x30(%rbp)
  int completed = 0;
  401462:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
   */



  //printf("%d %d\n", data->writecursor, data->writecursor % (data->threadsize - 1));
  if (data->writecursor != 0 && (data->writecursor % (data->threadsize - 1)) == 0) {
  401469:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  40146d:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401473:	85 c0                	test   %eax,%eax
    //printf("writeepoch\n");
  } else {

  }

}
  401475:	90                   	nop
  401476:	5d                   	pop    %rbp
  401477:	c3                   	ret

0000000000401478 <singlewriter2>:

int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401478:	55                   	push   %rbp
  401479:	48 89 e5             	mov    %rsp,%rbp
  40147c:	48 83 ec 40          	sub    $0x40,%rsp
  401480:	48 89 7d d8          	mov    %rdi,-0x28(%rbp)
  401484:	48 89 75 d0          	mov    %rsi,-0x30(%rbp)
  401488:	48 89 55 c8          	mov    %rdx,-0x38(%rbp)
  40148c:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
  int completed = 0;
  401490:	c7 45 ec 00 00 00 00 	movl   $0x0,-0x14(%rbp)
   }
   */


//if ((__atomic_load_n(&data->readcursor, __ATOMIC_SEQ_CST) % data->threadsize) == 0) {
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401497:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  40149b:	8b 80 00 02 00 00    	mov    0x200(%rax),%eax
  4014a1:	85 c0                	test   %eax,%eax
  4014a3:	0f 84 c7 00 00 00    	je     401570 <singlewriter2+0xf8>
  4014a9:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014ad:	8b 80 00 02 00 00    	mov    0x200(%rax),%eax
  4014b3:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  4014b7:	8b 52 68             	mov    0x68(%rdx),%edx
  4014ba:	8d 4a ff             	lea    -0x1(%rdx),%ecx
  4014bd:	99                   	cltd
  4014be:	f7 f9                	idiv   %ecx
  4014c0:	89 d0                	mov    %edx,%eax
  4014c2:	85 c0                	test   %eax,%eax
  4014c4:	0f 85 a6 00 00 00    	jne    401570 <singlewriter2+0xf8>
   // data->readcursor = 0;
    //printf("readepoch\n");
    
  
        // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
        struct Data * thread = &data->threads[data->threadindex];
  4014ca:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014ce:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4014d2:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014d6:	8b 40 64             	mov    0x64(%rax),%eax
  4014d9:	48 98                	cltq
  4014db:	48 c1 e0 0a          	shl    $0xa,%rax
  4014df:	48 01 d0             	add    %rdx,%rax
  4014e2:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4014e6:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4014ea:	48 8b 88 18 03 00 00 	mov    0x318(%rax),%rcx
  4014f1:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4014f5:	8b 80 24 03 00 00    	mov    0x324(%rax),%eax
  4014fb:	48 63 d0             	movslq %eax,%rdx
  4014fe:	48 89 d0             	mov    %rdx,%rax
  401501:	48 01 c0             	add    %rax,%rax
  401504:	48 01 d0             	add    %rdx,%rax
  401507:	48 c1 e0 04          	shl    $0x4,%rax
  40150b:	48 01 c8             	add    %rcx,%rax
  40150e:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401512:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401516:	48 83 c0 08          	add    $0x8,%rax
  40151a:	48 89 c6             	mov    %rax,%rsi
  40151d:	bf 04 00 00 00       	mov    $0x4,%edi
  401522:	e8 29 fb ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401527:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  40152b:	8b 80 24 03 00 00    	mov    0x324(%rax),%eax
  401531:	8d 50 01             	lea    0x1(%rax),%edx
  401534:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401538:	8b 88 20 03 00 00    	mov    0x320(%rax),%ecx
  40153e:	89 d0                	mov    %edx,%eax
  401540:	99                   	cltd
  401541:	f7 f9                	idiv   %ecx
  401543:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401547:	89 90 24 03 00 00    	mov    %edx,0x324(%rax)
        epoch->kind = NEW_EPOCH;
  40154d:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401551:	c7 40 20 01 00 00 00 	movl   $0x1,0x20(%rax)
        epoch->thread = data->threadindex;
  401558:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  40155c:	8b 50 64             	mov    0x64(%rax),%edx
  40155f:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401563:	89 10                	mov    %edx,(%rax)
        epoch->set = 1;
  401565:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401569:	c7 40 24 01 00 00 00 	movl   $0x1,0x24(%rax)
  } else {
    
  }

  
}
  401570:	90                   	nop
  401571:	c9                   	leave
  401572:	c3                   	ret

0000000000401573 <singlewriter>:



*/

int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401573:	55                   	push   %rbp
  401574:	48 89 e5             	mov    %rsp,%rbp
  401577:	48 83 ec 70          	sub    $0x70,%rsp
  40157b:	48 89 7d a8          	mov    %rdi,-0x58(%rbp)
  40157f:	48 89 75 a0          	mov    %rsi,-0x60(%rbp)
  401583:	48 89 55 98          	mov    %rdx,-0x68(%rbp)
  401587:	48 89 4d 90          	mov    %rcx,-0x70(%rbp)
  40158b:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401594:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  401598:	31 c0                	xor    %eax,%eax
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  40159a:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40159e:	48 8b 40 30          	mov    0x30(%rax),%rax
  4015a2:	8b 80 0c 02 00 00    	mov    0x20c(%rax),%eax
  4015a8:	8d 50 01             	lea    0x1(%rax),%edx
  4015ab:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015af:	8b 70 68             	mov    0x68(%rax),%esi
  4015b2:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015b6:	48 8b 48 30          	mov    0x30(%rax),%rcx
  4015ba:	89 d0                	mov    %edx,%eax
  4015bc:	99                   	cltd
  4015bd:	f7 fe                	idiv   %esi
  4015bf:	89 d0                	mov    %edx,%eax
  4015c1:	89 81 0c 02 00 00    	mov    %eax,0x20c(%rcx)
  int readers = 0;
  4015c7:	c7 45 b0 00 00 00 00 	movl   $0x0,-0x50(%rbp)
  int writers = 0;
  4015ce:	c7 45 b4 00 00 00 00 	movl   $0x0,-0x4c(%rbp)
  int availableidx = 0;
  4015d5:	c7 45 b8 00 00 00 00 	movl   $0x0,-0x48(%rbp)
    readywriters[x] = x;
  }
  */
  //clock_gettime(CLOCK_MONOTONIC_RAW, &data->wstart);
  
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  4015dc:	48 8b 7d 90          	mov    -0x70(%rbp),%rdi
  4015e0:	48 8b 4d 98          	mov    -0x68(%rbp),%rcx
  4015e4:	48 8d 55 b8          	lea    -0x48(%rbp),%rdx
  4015e8:	48 8b 75 a0          	mov    -0x60(%rbp),%rsi
  4015ec:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015f0:	49 89 f8             	mov    %rdi,%r8
  4015f3:	48 89 c7             	mov    %rax,%rdi
  4015f6:	e8 99 fd ff ff       	call   401394 <findavailable>
  4015fb:	89 45 cc             	mov    %eax,-0x34(%rbp)

//clock_gettime(CLOCK_MONOTONIC_RAW, &data->wavail);
  
  if (fill == 1) {
  4015fe:	83 7d cc 01          	cmpl   $0x1,-0x34(%rbp)
  401602:	75 0a                	jne    40160e <singlewriter+0x9b>
    return 1;
  401604:	b8 01 00 00 00       	mov    $0x1,%eax
  401609:	e9 f9 02 00 00       	jmp    401907 <singlewriter+0x394>
  }
      
   //printf("buffers available %d\n", availableidx);
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  40160e:	48 8d 7d b4          	lea    -0x4c(%rbp),%rdi
  401612:	48 8d 4d b0          	lea    -0x50(%rbp),%rcx
  401616:	48 8b 55 90          	mov    -0x70(%rbp),%rdx
  40161a:	48 8b 75 98          	mov    -0x68(%rbp),%rsi
  40161e:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401622:	49 89 f8             	mov    %rdi,%r8
  401625:	48 89 c7             	mov    %rax,%rdi
  401628:	e8 81 fc ff ff       	call   4012ae <pollthreads>
      
  //clock_gettime(CLOCK_MONOTONIC_RAW, &data->wpoll);
      
      int assignedchunk = 0;
  40162d:	c7 45 bc 00 00 00 00 	movl   $0x0,-0x44(%rbp)
      
        for (int x = 0; x < readers ; x++) {
  401634:	c7 45 c0 00 00 00 00 	movl   $0x0,-0x40(%rbp)
  40163b:	e9 10 01 00 00       	jmp    401750 <singlewriter+0x1dd>
          if (assignedchunk == availableidx) {
  401640:	8b 45 b8             	mov    -0x48(%rbp),%eax
  401643:	39 45 bc             	cmp    %eax,-0x44(%rbp)
  401646:	0f 84 12 01 00 00    	je     40175e <singlewriter+0x1eb>
           // printf("not enough space readers\n");
                  break;
          }
          int thread = readyreaders[x];
  40164c:	8b 45 c0             	mov    -0x40(%rbp),%eax
  40164f:	48 98                	cltq
  401651:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401659:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40165d:	48 01 d0             	add    %rdx,%rax
  401660:	8b 00                	mov    (%rax),%eax
  401662:	89 45 d0             	mov    %eax,-0x30(%rbp)
          //printf("%d %p\n", thread, &data->freelist[available[assignedchunk]]);
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401665:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401669:	48 8b 88 a0 00 00 00 	mov    0xa0(%rax),%rcx
  401670:	8b 45 bc             	mov    -0x44(%rbp),%eax
  401673:	8d 50 01             	lea    0x1(%rax),%edx
  401676:	89 55 bc             	mov    %edx,-0x44(%rbp)
  401679:	48 98                	cltq
  40167b:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  401683:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  401687:	48 01 d0             	add    %rdx,%rax
  40168a:	48 8b 00             	mov    (%rax),%rax
  40168d:	48 c1 e0 05          	shl    $0x5,%rax
  401691:	48 01 c8             	add    %rcx,%rax
  401694:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
          chunk->available = READING;
  401698:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  40169c:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
          //printf("assign %p\n", chunk);


          data->threads[thread].reading = chunk;
  4016a3:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016a7:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016ab:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016ae:	48 98                	cltq
  4016b0:	48 c1 e0 0a          	shl    $0xa,%rax
  4016b4:	48 01 c2             	add    %rax,%rdx
  4016b7:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016bb:	48 89 82 a8 00 00 00 	mov    %rax,0xa8(%rdx)
          
          chunk->owner = thread;
  4016c2:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016c6:	8b 55 d0             	mov    -0x30(%rbp),%edx
  4016c9:	89 50 14             	mov    %edx,0x14(%rax)
          int start = chunk->start;
  4016cc:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016d0:	48 8b 00             	mov    (%rax),%rax
  4016d3:	89 45 d4             	mov    %eax,-0x2c(%rbp)
          data->threads[thread].start = start;
  4016d6:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016da:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016de:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016e1:	48 98                	cltq
  4016e3:	48 c1 e0 0a          	shl    $0xa,%rax
  4016e7:	48 01 c2             	add    %rax,%rdx
  4016ea:	8b 45 d4             	mov    -0x2c(%rbp),%eax
  4016ed:	89 42 14             	mov    %eax,0x14(%rdx)
          
          int end = chunk->end;
  4016f0:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016f4:	48 8b 40 08          	mov    0x8(%rax),%rax
  4016f8:	89 45 d8             	mov    %eax,-0x28(%rbp)
          data->threads[thread].end = end;
  4016fb:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016ff:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401703:	8b 45 d0             	mov    -0x30(%rbp),%eax
  401706:	48 98                	cltq
  401708:	48 c1 e0 0a          	shl    $0xa,%rax
  40170c:	48 01 c2             	add    %rax,%rdx
  40170f:	8b 45 d8             	mov    -0x28(%rbp),%eax
  401712:	89 42 18             	mov    %eax,0x18(%rdx)
        // printf("reader giving %d between %ld and %ld\n", x, start, end);
        
         // clock_gettime(CLOCK_MONOTONIC_RAW, &data->main->works[start].created);
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401715:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401719:	48 8b 50 30          	mov    0x30(%rax),%rdx
  40171d:	8b 45 d0             	mov    -0x30(%rbp),%eax
  401720:	48 98                	cltq
  401722:	48 c1 e0 0a          	shl    $0xa,%rax
  401726:	48 01 d0             	add    %rdx,%rax
  401729:	8b 90 c8 00 00 00    	mov    0xc8(%rax),%edx
  40172f:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401733:	48 8b 48 30          	mov    0x30(%rax),%rcx
  401737:	8b 45 d0             	mov    -0x30(%rbp),%eax
  40173a:	48 98                	cltq
  40173c:	48 c1 e0 0a          	shl    $0xa,%rax
  401740:	48 01 c8             	add    %rcx,%rax
  401743:	83 ca 10             	or     $0x10,%edx
  401746:	89 90 c8 00 00 00    	mov    %edx,0xc8(%rax)
        for (int x = 0; x < readers ; x++) {
  40174c:	83 45 c0 01          	addl   $0x1,-0x40(%rbp)
  401750:	8b 45 b0             	mov    -0x50(%rbp),%eax
  401753:	39 45 c0             	cmp    %eax,-0x40(%rbp)
  401756:	0f 8c e4 fe ff ff    	jl     401640 <singlewriter+0xcd>
  40175c:	eb 01                	jmp    40175f <singlewriter+0x1ec>
                  break;
  40175e:	90                   	nop
       // printf("read newmask ORed with %d\n", data->threads[thread].newmask);
        }
      
   for (int x = 0; x < writers ; x++) {
  40175f:	c7 45 c4 00 00 00 00 	movl   $0x0,-0x3c(%rbp)
  401766:	e9 10 01 00 00       	jmp    40187b <singlewriter+0x308>
                if (assignedchunk  == availableidx) {
  40176b:	8b 45 b8             	mov    -0x48(%rbp),%eax
  40176e:	39 45 bc             	cmp    %eax,-0x44(%rbp)
  401771:	0f 84 12 01 00 00    	je     401889 <singlewriter+0x316>
                  
                 //printf("not enough space writer %d %d\n", assignedchunk, availableidx);
                  break;
                }
          int thread = readywriters[x];
  401777:	8b 45 c4             	mov    -0x3c(%rbp),%eax
  40177a:	48 98                	cltq
  40177c:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401784:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  401788:	48 01 d0             	add    %rdx,%rax
  40178b:	8b 00                	mov    (%rax),%eax
  40178d:	89 45 dc             	mov    %eax,-0x24(%rbp)
     
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401790:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401794:	48 8b 88 a0 00 00 00 	mov    0xa0(%rax),%rcx
  40179b:	8b 45 bc             	mov    -0x44(%rbp),%eax
  40179e:	8d 50 01             	lea    0x1(%rax),%edx
  4017a1:	89 55 bc             	mov    %edx,-0x44(%rbp)
  4017a4:	48 98                	cltq
  4017a6:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4017ae:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  4017b2:	48 01 d0             	add    %rdx,%rax
  4017b5:	48 8b 00             	mov    (%rax),%rax
  4017b8:	48 c1 e0 05          	shl    $0x5,%rax
  4017bc:	48 01 c8             	add    %rcx,%rax
  4017bf:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
    
      chunk->available = WRITING;
  4017c3:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017c7:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
          data->threads[thread].writing = chunk;
  4017ce:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4017d2:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4017d6:	8b 45 dc             	mov    -0x24(%rbp),%eax
  4017d9:	48 98                	cltq
  4017db:	48 c1 e0 0a          	shl    $0xa,%rax
  4017df:	48 01 c2             	add    %rax,%rdx
  4017e2:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017e6:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
          chunk->owner = thread;
  4017ed:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017f1:	8b 55 dc             	mov    -0x24(%rbp),%edx
  4017f4:	89 50 14             	mov    %edx,0x14(%rax)
          int start = chunk->start;
  4017f7:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017fb:	48 8b 00             	mov    (%rax),%rax
  4017fe:	89 45 e0             	mov    %eax,-0x20(%rbp)
          data->threads[thread].publishstart = start;
  401801:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401805:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401809:	8b 45 dc             	mov    -0x24(%rbp),%eax
  40180c:	48 98                	cltq
  40180e:	48 c1 e0 0a          	shl    $0xa,%rax
  401812:	48 01 c2             	add    %rax,%rdx
  401815:	8b 45 e0             	mov    -0x20(%rbp),%eax
  401818:	89 42 40             	mov    %eax,0x40(%rdx)
          
          int end = chunk->end;
  40181b:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  40181f:	48 8b 40 08          	mov    0x8(%rax),%rax
  401823:	89 45 e4             	mov    %eax,-0x1c(%rbp)
          data->threads[thread].publishend = end;
  401826:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40182a:	48 8b 50 30          	mov    0x30(%rax),%rdx
  40182e:	8b 45 dc             	mov    -0x24(%rbp),%eax
  401831:	48 98                	cltq
  401833:	48 c1 e0 0a          	shl    $0xa,%rax
  401837:	48 01 c2             	add    %rax,%rdx
  40183a:	8b 45 e4             	mov    -0x1c(%rbp),%eax
  40183d:	89 42 44             	mov    %eax,0x44(%rdx)
        //  printf("writer giving %d between %ld and %ld\n", available[assignedchunk], start, end);
          // asm volatile ("sfence" ::: "memory");
     
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401840:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401844:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401848:	8b 45 dc             	mov    -0x24(%rbp),%eax
  40184b:	48 98                	cltq
  40184d:	48 c1 e0 0a          	shl    $0xa,%rax
  401851:	48 01 d0             	add    %rdx,%rax
  401854:	8b 90 c8 00 00 00    	mov    0xc8(%rax),%edx
  40185a:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40185e:	48 8b 48 30          	mov    0x30(%rax),%rcx
  401862:	8b 45 dc             	mov    -0x24(%rbp),%eax
  401865:	48 98                	cltq
  401867:	48 c1 e0 0a          	shl    $0xa,%rax
  40186b:	48 01 c8             	add    %rcx,%rax
  40186e:	83 ca 20             	or     $0x20,%edx
  401871:	89 90 c8 00 00 00    	mov    %edx,0xc8(%rax)
   for (int x = 0; x < writers ; x++) {
  401877:	83 45 c4 01          	addl   $0x1,-0x3c(%rbp)
  40187b:	8b 45 b4             	mov    -0x4c(%rbp),%eax
  40187e:	39 45 c4             	cmp    %eax,-0x3c(%rbp)
  401881:	0f 8c e4 fe ff ff    	jl     40176b <singlewriter+0x1f8>
  401887:	eb 01                	jmp    40188a <singlewriter+0x317>
                  break;
  401889:	90                   	nop
     //printf("write newmask ORed with %ld\n", data->threads[thread].newmask);
        
   } 
      for (int x = 0; x < data->threadsize ; x++) {
  40188a:	c7 45 c8 00 00 00 00 	movl   $0x0,-0x38(%rbp)
  401891:	eb 63                	jmp    4018f6 <singlewriter+0x383>
        if (data->threads[x].newmask != 0) {
  401893:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401897:	48 8b 50 30          	mov    0x30(%rax),%rdx
  40189b:	8b 45 c8             	mov    -0x38(%rbp),%eax
  40189e:	48 98                	cltq
  4018a0:	48 c1 e0 0a          	shl    $0xa,%rax
  4018a4:	48 01 d0             	add    %rdx,%rax
  4018a7:	8b 80 c8 00 00 00    	mov    0xc8(%rax),%eax
  4018ad:	85 c0                	test   %eax,%eax
  4018af:	74 41                	je     4018f2 <singlewriter+0x37f>
         // printf("thread %d %ld is now %ld\n", x, data->threads[x].ready, data->threads[x].newmask);
          data->threads[x].readies[x] = data->threads[x].newmask;
  4018b1:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018b5:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4018b9:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018bc:	48 98                	cltq
  4018be:	48 c1 e0 0a          	shl    $0xa,%rax
  4018c2:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
  4018c6:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018ca:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4018ce:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018d1:	48 98                	cltq
  4018d3:	48 c1 e0 0a          	shl    $0xa,%rax
  4018d7:	48 01 d0             	add    %rdx,%rax
  4018da:	48 8b 50 20          	mov    0x20(%rax),%rdx
  4018de:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018e1:	48 98                	cltq
  4018e3:	48 c1 e0 02          	shl    $0x2,%rax
  4018e7:	48 01 c2             	add    %rax,%rdx
  4018ea:	8b 81 c8 00 00 00    	mov    0xc8(%rcx),%eax
  4018f0:	89 02                	mov    %eax,(%rdx)
      for (int x = 0; x < data->threadsize ; x++) {
  4018f2:	83 45 c8 01          	addl   $0x1,-0x38(%rbp)
  4018f6:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018fa:	8b 40 68             	mov    0x68(%rax),%eax
  4018fd:	39 45 c8             	cmp    %eax,-0x38(%rbp)
  401900:	7c 91                	jl     401893 <singlewriter+0x320>
        
          
        }
      }
  // clock_gettime(CLOCK_MONOTONIC_RAW, &data->wassign);
  return 0;
  401902:	b8 00 00 00 00       	mov    $0x0,%eax
}
  401907:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  40190b:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401914:	74 05                	je     40191b <singlewriter+0x3a8>
  401916:	e8 55 f7 ff ff       	call   401070 <__stack_chk_fail@plt>
  40191b:	c9                   	leave
  40191c:	c3                   	ret

000000000040191d <threadwork>:

int * threadwork(struct Data * data) {
  40191d:	55                   	push   %rbp
  40191e:	48 89 e5             	mov    %rsp,%rbp
  401921:	48 81 ec 90 00 00 00 	sub    $0x90,%rsp
  401928:	48 89 bd 78 ff ff ff 	mov    %rdi,-0x88(%rbp)
  40192f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401938:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  40193c:	31 c0                	xor    %eax,%eax
  int cursorlimit = 5;
  40193e:	c7 45 a4 05 00 00 00 	movl   $0x5,-0x5c(%rbp)
  int epochsize = 1;
  401945:	c7 45 a8 01 00 00 00 	movl   $0x1,-0x58(%rbp)
  int epochwidth = 0xff;
  40194c:	c7 45 ac ff 00 00 00 	movl   $0xff,-0x54(%rbp)

//printf("%ld %ld w%d\n", lastwrite, data->prevwrite, data->threadindex);
 //if (lastwrite != data->prevwrite) {
   
    uint64_t rsp;
    asm( "mov %%rsp, %0" : "=rm" ( rsp ));
  401953:	48 89 e0             	mov    %rsp,%rax
  401956:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
  data->scheduler->rsp = rsp;
  40195a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401961:	48 8b 80 c8 03 00 00 	mov    0x3c8(%rax),%rax
  401968:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  40196c:	48 89 10             	mov    %rdx,(%rax)
  // switch_to(struct Coroutine * coroutines, int index
  //printf("table %x\n", (void *)data->coroutines);
 // printf("coroutine 3 %x\n", &data->coroutines[3]);
 // printf("coroutine eip %lx\n", data->coroutines[3].eip);
 // printf("coroutine data %lx\n", data->coroutines[3].data);
  switch_to(data->coroutines, 3, data->scheduler);  
  40196f:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401976:	48 8b 90 c8 03 00 00 	mov    0x3c8(%rax),%rdx
  40197d:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401984:	48 8b 80 c0 03 00 00 	mov    0x3c0(%rax),%rax
  40198b:	be 03 00 00 00       	mov    $0x3,%esi
  401990:	48 89 c7             	mov    %rax,%rdi
  401993:	e8 00 1d 00 00       	call   403698 <switch_to>
  //printf("finished coroutine\n");
  //printf("%ld %ld w%d\n", lastwrite, data->prevwrite, data->threadindex);
     
       
clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401998:	48 8d 45 e0          	lea    -0x20(%rbp),%rax
  40199c:	48 89 c6             	mov    %rax,%rsi
  40199f:	bf 04 00 00 00       	mov    $0x4,%edi
  4019a4:	e8 a7 f6 ff ff       	call   401050 <clock_gettime@plt>
  //if (data->threadindex % 2 == 0) {
   
  if (data->running == 2) {
  4019a9:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019b0:	8b 40 5c             	mov    0x5c(%rax),%eax
  4019b3:	83 f8 02             	cmp    $0x2,%eax
  4019b6:	0f 85 9f 01 00 00    	jne    401b5b <threadwork+0x23e>
  //if (data ->threadindex == 0 ) {
      

   for (int x = 0 ; x < data->threadsize ; x++) {
  4019bc:	c7 45 98 00 00 00 00 	movl   $0x0,-0x68(%rbp)
  4019c3:	e9 50 01 00 00       	jmp    401b18 <threadwork+0x1fb>
      
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  4019c8:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019cf:	48 8b 40 28          	mov    0x28(%rax),%rax
  4019d3:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  4019da:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019e1:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  4019e7:	c1 e0 07             	shl    $0x7,%eax
  4019ea:	48 98                	cltq
  4019ec:	48 c1 e0 03          	shl    $0x3,%rax
  4019f0:	48 01 d0             	add    %rdx,%rax
  4019f3:	48 8b 00             	mov    (%rax),%rax
  4019f6:	8b 55 a8             	mov    -0x58(%rbp),%edx
  4019f9:	48 63 fa             	movslq %edx,%rdi
  4019fc:	48 99                	cqto
  4019fe:	48 f7 ff             	idiv   %rdi
  401a01:	48 89 c2             	mov    %rax,%rdx
  401a04:	8b 45 ac             	mov    -0x54(%rbp),%eax
  401a07:	48 63 c8             	movslq %eax,%rcx
  401a0a:	48 89 d0             	mov    %rdx,%rax
  401a0d:	48 99                	cqto
  401a0f:	48 f7 f9             	idiv   %rcx
  401a12:	48 89 d0             	mov    %rdx,%rax
  401a15:	89 45 9c             	mov    %eax,-0x64(%rbp)
    
      //  buffer = data->mystream << 24 | ( global << 16) | data->threadindex << 8 | data->writecursor % 0xff;
    int cursor = data->writecursor;
  401a18:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a1f:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401a25:	89 45 a0             	mov    %eax,-0x60(%rbp)
    //cursor = 0;
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  401a28:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a2f:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401a35:	c1 e0 18             	shl    $0x18,%eax
  401a38:	89 c2                	mov    %eax,%edx
  401a3a:	8b 45 9c             	mov    -0x64(%rbp),%eax
  401a3d:	c1 e0 10             	shl    $0x10,%eax
  401a40:	89 d6                	mov    %edx,%esi
  401a42:	09 c6                	or     %eax,%esi
  401a44:	8b 45 a0             	mov    -0x60(%rbp),%eax
  401a47:	48 63 d0             	movslq %eax,%rdx
  401a4a:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401a51:	48 c1 ea 20          	shr    $0x20,%rdx
  401a55:	01 c2                	add    %eax,%edx
  401a57:	c1 fa 07             	sar    $0x7,%edx
  401a5a:	89 c7                	mov    %eax,%edi
  401a5c:	c1 ff 1f             	sar    $0x1f,%edi
  401a5f:	89 d1                	mov    %edx,%ecx
  401a61:	29 f9                	sub    %edi,%ecx
  401a63:	89 ca                	mov    %ecx,%edx
  401a65:	c1 e2 08             	shl    $0x8,%edx
  401a68:	29 ca                	sub    %ecx,%edx
  401a6a:	29 d0                	sub    %edx,%eax
  401a6c:	89 c1                	mov    %eax,%ecx
  401a6e:	89 f0                	mov    %esi,%eax
  401a70:	09 c8                	or     %ecx,%eax
  401a72:	48 98                	cltq
  401a74:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
      buffer = data->mystream << 24 | ( (data->main->globalwrite[data->mystream * 128] / (data->threadsize)) % 0xff) << 16 | data->writecursor;
    }
    */
      // printf("%x\n", buffer);
        // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
  struct Data * thread = &data->threads[data->threadindex];
  401a78:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a7f:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401a83:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a8a:	8b 40 64             	mov    0x64(%rax),%eax
  401a8d:	48 98                	cltq
  401a8f:	48 c1 e0 0a          	shl    $0xa,%rax
  401a93:	48 01 d0             	add    %rdx,%rax
  401a96:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
  epoch->buffer = buffer;
  epoch->set = 1;
  }
    
     // printf("alrrady filled\n");
  if (data->main->works[buffer] != -1) {
  401a9a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401aa1:	48 8b 40 28          	mov    0x28(%rax),%rax
  401aa5:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401aa9:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401aad:	48 01 d0             	add    %rdx,%rax
  401ab0:	0f b6 00             	movzbl (%rax),%eax
  401ab3:	3c ff                	cmp    $0xff,%al
  401ab5:	74 1a                	je     401ad1 <threadwork+0x1b4>
    
    data->freq_writes++;
  401ab7:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401abe:	48 8b 40 50          	mov    0x50(%rax),%rax
  401ac2:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401ac6:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401acd:	48 89 50 50          	mov    %rdx,0x50(%rax)
  }
  data->main->works[buffer] = data->threadindex;
  401ad1:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ad8:	8b 50 64             	mov    0x64(%rax),%edx
  401adb:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ae2:	48 8b 40 28          	mov    0x28(%rax),%rax
  401ae6:	48 8b 48 70          	mov    0x70(%rax),%rcx
  401aea:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401aee:	48 01 c8             	add    %rcx,%rax
  401af1:	88 10                	mov    %dl,(%rax)
         
         
  //  data->prevread = data->main->currentread;
     
     
    data->writecursor = (data->writecursor + 1) % cursorlimit;
  401af3:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401afa:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401b00:	83 c0 01             	add    $0x1,%eax
  401b03:	99                   	cltd
  401b04:	f7 7d a4             	idivl  -0x5c(%rbp)
  401b07:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b0e:	89 90 80 01 00 00    	mov    %edx,0x180(%rax)
   for (int x = 0 ; x < data->threadsize ; x++) {
  401b14:	83 45 98 01          	addl   $0x1,-0x68(%rbp)
  401b18:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b1f:	8b 40 68             	mov    0x68(%rax),%eax
  401b22:	39 45 98             	cmp    %eax,-0x68(%rbp)
  401b25:	0f 8c 9d fe ff ff    	jl     4019c8 <threadwork+0xab>
    
   }
      
    __atomic_fetch_add(&data->main->globalwrite[data->mystream * 128], 1, __ATOMIC_RELAXED);
  401b2b:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b32:	48 8b 40 28          	mov    0x28(%rax),%rax
  401b36:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401b3d:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b44:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401b4a:	c1 e0 07             	shl    $0x7,%eax
  401b4d:	48 98                	cltq
  401b4f:	48 c1 e0 03          	shl    $0x3,%rax
  401b53:	48 01 d0             	add    %rdx,%rax
  401b56:	f0 48 83 00 01       	lock addq $0x1,(%rax)
//}
  } 
  ///else {
  long thisgroup = data->main->globalwrite[data->mystream * 128] / epochsize;
  401b5b:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b62:	48 8b 40 28          	mov    0x28(%rax),%rax
  401b66:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401b6d:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b74:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401b7a:	c1 e0 07             	shl    $0x7,%eax
  401b7d:	48 98                	cltq
  401b7f:	48 c1 e0 03          	shl    $0x3,%rax
  401b83:	48 01 d0             	add    %rdx,%rax
  401b86:	48 8b 00             	mov    (%rax),%rax
  401b89:	8b 55 a8             	mov    -0x58(%rbp),%edx
  401b8c:	48 63 fa             	movslq %edx,%rdi
  401b8f:	48 99                	cqto
  401b91:	48 f7 ff             	idiv   %rdi
  401b94:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
  
  if (thisgroup != data->lastgroup) {
  401b98:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b9f:	8b 80 88 03 00 00    	mov    0x388(%rax),%eax
  401ba5:	48 98                	cltq
  401ba7:	48 39 45 c8          	cmp    %rax,-0x38(%rbp)
  401bab:	74 11                	je     401bbe <threadwork+0x2a1>
     // printf("ndw group\n");
      data->writecursor = 0;
  401bad:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bb4:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
        epoch->thread = data->threadindex;
        epoch->stream = data->mystream;
        epoch->set = 1;
     }
   }
   data->lastgroup = thisgroup;
  401bbe:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
  401bc2:	89 c2                	mov    %eax,%edx
  401bc4:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bcb:	89 90 88 03 00 00    	mov    %edx,0x388(%rax)
  //}
  
 //if (lastread != data->prevread)
 // {
   //printf("%ld  %ld r%d\n", data->main->currentread, data->prevread, data->threadindex);
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  401bd1:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bd8:	48 8b 40 28          	mov    0x28(%rax),%rax
  401bdc:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401be3:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bea:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401bf0:	c1 e0 07             	shl    $0x7,%eax
  401bf3:	48 98                	cltq
  401bf5:	48 c1 e0 03          	shl    $0x3,%rax
  401bf9:	48 01 d0             	add    %rdx,%rax
  401bfc:	48 8b 00             	mov    (%rax),%rax
  401bff:	48 89 45 d0          	mov    %rax,-0x30(%rbp)
  
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
  401c03:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c0a:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401c11:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c18:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401c1e:	48 63 d0             	movslq %eax,%rdx
  401c21:	48 89 d0             	mov    %rdx,%rax
  401c24:	48 01 c0             	add    %rax,%rax
  401c27:	48 01 d0             	add    %rdx,%rax
  401c2a:	48 c1 e0 02          	shl    $0x2,%rax
  401c2e:	48 01 c8             	add    %rcx,%rax
  401c31:	8b 00                	mov    (%rax),%eax
  401c33:	48 98                	cltq
  401c35:	48 39 45 d0          	cmp    %rax,-0x30(%rbp)
  401c39:	7f 0b                	jg     401c46 <threadwork+0x329>
  401c3b:	48 83 7d d0 00       	cmpq   $0x0,-0x30(%rbp)
  401c40:	0f 85 f9 02 00 00    	jne    401f3f <threadwork+0x622>
    for (int x = 0; x < data->threadsize - 1; x++) {
  401c46:	c7 45 94 00 00 00 00 	movl   $0x0,-0x6c(%rbp)
  401c4d:	e9 d7 02 00 00       	jmp    401f29 <threadwork+0x60c>
  // printf("%d\n", thiswrite);
   data->freq++;
  401c52:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c59:	48 8b 40 48          	mov    0x48(%rax),%rax
  401c5d:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401c61:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c68:	48 89 50 48          	mov    %rdx,0x48(%rax)
  
        
      
          
            
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  401c6c:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c73:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401c7a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c81:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401c87:	48 63 d0             	movslq %eax,%rdx
  401c8a:	48 89 d0             	mov    %rdx,%rax
  401c8d:	48 01 c0             	add    %rax,%rax
  401c90:	48 01 d0             	add    %rdx,%rax
  401c93:	48 c1 e0 02          	shl    $0x2,%rax
  401c97:	48 01 c8             	add    %rcx,%rax
  401c9a:	8b 00                	mov    (%rax),%eax
  401c9c:	99                   	cltd
  401c9d:	f7 7d a8             	idivl  -0x58(%rbp)
  401ca0:	83 e8 01             	sub    $0x1,%eax
  401ca3:	99                   	cltd
  401ca4:	f7 7d ac             	idivl  -0x54(%rbp)
  401ca7:	89 d0                	mov    %edx,%eax
  401ca9:	48 98                	cltq
  401cab:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
        //long past = (((data->globalread[data->laststream]).global % epochwidth;
            if (past < 0) {
  401caf:	48 83 7d b0 00       	cmpq   $0x0,-0x50(%rbp)
  401cb4:	79 08                	jns    401cbe <threadwork+0x3a1>
              past = 0;
  401cb6:	48 c7 45 b0 00 00 00 00 	movq   $0x0,-0x50(%rbp)
            }
            
            // long buffer = (data->threadindex << 24) | (data->main->globalwrite % 0xf) << 16 | (data->main->writecursor % 0xf);
        
       // buffer = data->laststream << 24 | (past << 16) | data->globalread[data->laststream].thread << 8, data->globalread[data->laststream].cursor % 0xff;
    int cursor = data->globalread[data->laststream].cursor;
  401cbe:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cc5:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401ccc:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cd3:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401cd9:	48 63 d0             	movslq %eax,%rdx
  401cdc:	48 89 d0             	mov    %rdx,%rax
  401cdf:	48 01 c0             	add    %rax,%rax
  401ce2:	48 01 d0             	add    %rdx,%rax
  401ce5:	48 c1 e0 02          	shl    $0x2,%rax
  401ce9:	48 01 c8             	add    %rcx,%rax
  401cec:	8b 40 04             	mov    0x4(%rax),%eax
  401cef:	89 45 8c             	mov    %eax,-0x74(%rbp)
    //cursor = 0;
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  401cf2:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cf9:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401cff:	c1 e0 18             	shl    $0x18,%eax
  401d02:	48 63 d0             	movslq %eax,%rdx
  401d05:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
  401d09:	48 c1 e0 10          	shl    $0x10,%rax
  401d0d:	48 89 d6             	mov    %rdx,%rsi
  401d10:	48 09 c6             	or     %rax,%rsi
  401d13:	8b 45 8c             	mov    -0x74(%rbp),%eax
  401d16:	48 63 d0             	movslq %eax,%rdx
  401d19:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401d20:	48 c1 ea 20          	shr    $0x20,%rdx
  401d24:	01 c2                	add    %eax,%edx
  401d26:	c1 fa 07             	sar    $0x7,%edx
  401d29:	89 c1                	mov    %eax,%ecx
  401d2b:	c1 f9 1f             	sar    $0x1f,%ecx
  401d2e:	29 ca                	sub    %ecx,%edx
  401d30:	89 d1                	mov    %edx,%ecx
  401d32:	c1 e1 08             	shl    $0x8,%ecx
  401d35:	29 d1                	sub    %edx,%ecx
  401d37:	29 c8                	sub    %ecx,%eax
  401d39:	89 c2                	mov    %eax,%edx
  401d3b:	48 63 c2             	movslq %edx,%rax
  401d3e:	48 09 f0             	or     %rsi,%rax
  401d41:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    access->cursor = data->globalread[data->laststream].cursor % 0xff;
    access->set = 1;
    data->cread = (data->cread + 1) % data->accesssize;
  }
    
    int thistream = data->laststream; 
  401d45:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d4c:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401d52:	89 45 90             	mov    %eax,-0x70(%rbp)
                // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
                //&data->threads[data->threadindex];

        // printf("%d\n", data->main->works[buffer]);
    
        if (data->main->works[buffer] != -1) {
  401d55:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d5c:	48 8b 40 28          	mov    0x28(%rax),%rax
  401d60:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401d64:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401d68:	48 01 d0             	add    %rdx,%rax
  401d6b:	0f b6 00             	movzbl (%rax),%eax
  401d6e:	3c ff                	cmp    $0xff,%al
  401d70:	74 39                	je     401dab <threadwork+0x48e>
          data->successreads++;
  401d72:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d79:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  401d80:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401d84:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d8b:	48 89 90 98 03 00 00 	mov    %rdx,0x398(%rax)
          
          data->main->works[buffer] = -1;
  401d92:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d99:	48 8b 40 28          	mov    0x28(%rax),%rax
  401d9d:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401da1:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401da5:	48 01 d0             	add    %rdx,%rax
  401da8:	c6 00 ff             	movb   $0xff,(%rax)
  
    
    
      
    
    if (data->globalread[thistream].cursor < cursorlimit) {
  401dab:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401db2:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401db9:	8b 45 90             	mov    -0x70(%rbp),%eax
  401dbc:	48 63 d0             	movslq %eax,%rdx
  401dbf:	48 89 d0             	mov    %rdx,%rax
  401dc2:	48 01 c0             	add    %rax,%rax
  401dc5:	48 01 d0             	add    %rdx,%rax
  401dc8:	48 c1 e0 02          	shl    $0x2,%rax
  401dcc:	48 01 c8             	add    %rcx,%rax
  401dcf:	8b 40 04             	mov    0x4(%rax),%eax
  401dd2:	39 45 a4             	cmp    %eax,-0x5c(%rbp)
  401dd5:	7e 7c                	jle    401e53 <threadwork+0x536>
    
      data->globalread[thistream].global++;
  401dd7:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401dde:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401de5:	8b 45 90             	mov    -0x70(%rbp),%eax
  401de8:	48 63 d0             	movslq %eax,%rdx
  401deb:	48 89 d0             	mov    %rdx,%rax
  401dee:	48 01 c0             	add    %rax,%rax
  401df1:	48 01 d0             	add    %rdx,%rax
  401df4:	48 c1 e0 02          	shl    $0x2,%rax
  401df8:	48 01 c8             	add    %rcx,%rax
  401dfb:	8b 10                	mov    (%rax),%edx
  401dfd:	83 c2 01             	add    $0x1,%edx
  401e00:	89 10                	mov    %edx,(%rax)
        
        
      data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1);
  401e02:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e09:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401e10:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e13:	48 63 d0             	movslq %eax,%rdx
  401e16:	48 89 d0             	mov    %rdx,%rax
  401e19:	48 01 c0             	add    %rax,%rax
  401e1c:	48 01 d0             	add    %rdx,%rax
  401e1f:	48 c1 e0 02          	shl    $0x2,%rax
  401e23:	48 01 c8             	add    %rcx,%rax
  401e26:	8b 48 04             	mov    0x4(%rax),%ecx
  401e29:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e30:	48 8b b0 48 03 00 00 	mov    0x348(%rax),%rsi
  401e37:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e3a:	48 63 d0             	movslq %eax,%rdx
  401e3d:	48 89 d0             	mov    %rdx,%rax
  401e40:	48 01 c0             	add    %rax,%rax
  401e43:	48 01 d0             	add    %rdx,%rax
  401e46:	48 c1 e0 02          	shl    $0x2,%rax
  401e4a:	48 01 f0             	add    %rsi,%rax
  401e4d:	8d 51 01             	lea    0x1(%rcx),%edx
  401e50:	89 50 04             	mov    %edx,0x4(%rax)
      
      }
    
    if (data->globalread[thistream].cursor == cursorlimit) {
  401e53:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e5a:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401e61:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e64:	48 63 d0             	movslq %eax,%rdx
  401e67:	48 89 d0             	mov    %rdx,%rax
  401e6a:	48 01 c0             	add    %rax,%rax
  401e6d:	48 01 d0             	add    %rdx,%rax
  401e70:	48 c1 e0 02          	shl    $0x2,%rax
  401e74:	48 01 c8             	add    %rcx,%rax
  401e77:	8b 40 04             	mov    0x4(%rax),%eax
  401e7a:	39 45 a4             	cmp    %eax,-0x5c(%rbp)
  401e7d:	75 48                	jne    401ec7 <threadwork+0x5aa>
      
      data->laststream = (data->laststream + 1);
  401e7f:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e86:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401e8c:	8d 50 01             	lea    0x1(%rax),%edx
  401e8f:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e96:	89 90 90 03 00 00    	mov    %edx,0x390(%rax)
     // data->globalread[thistream].global++;
data->globalread[thistream].cursor = 0;
  401e9c:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ea3:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401eaa:	8b 45 90             	mov    -0x70(%rbp),%eax
  401ead:	48 63 d0             	movslq %eax,%rdx
  401eb0:	48 89 d0             	mov    %rdx,%rax
  401eb3:	48 01 c0             	add    %rax,%rax
  401eb6:	48 01 d0             	add    %rdx,%rax
  401eb9:	48 c1 e0 02          	shl    $0x2,%rax
  401ebd:	48 01 c8             	add    %rcx,%rax
  401ec0:	c7 40 04 00 00 00 00 	movl   $0x0,0x4(%rax)
    }
    
    if (data->laststream == data->mystream) {
  401ec7:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ece:	8b 90 90 03 00 00    	mov    0x390(%rax),%edx
  401ed4:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401edb:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401ee1:	39 c2                	cmp    %eax,%edx
  401ee3:	75 1d                	jne    401f02 <threadwork+0x5e5>
      data->laststream = data->laststream + 1;
  401ee5:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401eec:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401ef2:	8d 50 01             	lea    0x1(%rax),%edx
  401ef5:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401efc:	89 90 90 03 00 00    	mov    %edx,0x390(%rax)
     // data->globalread[data->laststream].cursor = 0;
    }
    if (data->laststream == 5) {
  401f02:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401f09:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401f0f:	83 f8 05             	cmp    $0x5,%eax
  401f12:	75 11                	jne    401f25 <threadwork+0x608>
       data->laststream = 1;
  401f14:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401f1b:	c7 80 90 03 00 00 01 00 00 00 	movl   $0x1,0x390(%rax)
    for (int x = 0; x < data->threadsize - 1; x++) {
  401f25:	83 45 94 01          	addl   $0x1,-0x6c(%rbp)
  401f29:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401f30:	8b 40 68             	mov    0x68(%rax),%eax
  401f33:	83 e8 01             	sub    $0x1,%eax
  401f36:	39 45 94             	cmp    %eax,-0x6c(%rbp)
  401f39:	0f 8c 13 fd ff ff    	jl     401c52 <threadwork+0x335>
      
     //asm volatile ("sfence" ::: "memory");
  
      
       
}
  401f3f:	90                   	nop
  401f40:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  401f44:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401f4d:	74 05                	je     401f54 <threadwork+0x637>
  401f4f:	e8 1c f1 ff ff       	call   401070 <__stack_chk_fail@plt>
  401f54:	c9                   	leave
  401f55:	c3                   	ret

0000000000401f56 <work2>:

void * work2(void * arg) {
  401f56:	55                   	push   %rbp
  401f57:	48 89 e5             	mov    %rsp,%rbp
  401f5a:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  struct Data *data = (struct Data*) arg;
  401f5e:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401f62:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  while (data->running == 1) {
  401f66:	eb 14                	jmp    401f7c <work2+0x26>
    asm volatile ("" ::: "memory");
      data->freq++;
  401f68:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f6c:	48 8b 40 48          	mov    0x48(%rax),%rax
  401f70:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401f74:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f78:	48 89 50 48          	mov    %rdx,0x48(%rax)
  while (data->running == 1) {
  401f7c:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f80:	8b 40 5c             	mov    0x5c(%rax),%eax
  401f83:	83 f8 01             	cmp    $0x1,%eax
  401f86:	74 e0                	je     401f68 <work2+0x12>
  }
  
}
  401f88:	90                   	nop
  401f89:	5d                   	pop    %rbp
  401f8a:	c3                   	ret

0000000000401f8b <work>:

void * work(void * arg) {
  401f8b:	55                   	push   %rbp
  401f8c:	48 89 e5             	mov    %rsp,%rbp
  401f8f:	48 83 ec 50          	sub    $0x50,%rsp
  401f93:	48 89 7d b8          	mov    %rdi,-0x48(%rbp)

  
  int writers;
  int readers;
  struct Data *data = (struct Data*) arg;
  401f97:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401f9b:	48 89 45 e0          	mov    %rax,-0x20(%rbp)
  printf("started thread %d\n", data->threadindex);
  401f9f:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fa3:	8b 40 64             	mov    0x64(%rax),%eax
  401fa6:	89 c6                	mov    %eax,%esi
  401fa8:	48 8d 05 7a 20 00 00 	lea    0x207a(%rip),%rax        # 404029 <_IO_stdin_used+0x29>
  401faf:	48 89 c7             	mov    %rax,%rdi
  401fb2:	b8 00 00 00 00       	mov    $0x0,%eax
  401fb7:	e8 c4 f0 ff ff       	call   401080 <printf@plt>
  
  
  int found = 0;
  401fbc:	c7 45 c8 00 00 00 00 	movl   $0x0,-0x38(%rbp)
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  401fc3:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fc7:	8b 40 64             	mov    0x64(%rax),%eax
  401fca:	8d 50 01             	lea    0x1(%rax),%edx
  401fcd:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fd1:	8b 48 68             	mov    0x68(%rax),%ecx
  401fd4:	89 d0                	mov    %edx,%eax
  401fd6:	99                   	cltd
  401fd7:	f7 f9                	idiv   %ecx
  401fd9:	89 55 cc             	mov    %edx,-0x34(%rbp)
  int innerfind = 0;
  401fdc:	c7 45 d0 00 00 00 00 	movl   $0x0,-0x30(%rbp)
  
  
  
  
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  401fe3:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fe7:	48 8b 80 b8 00 00 00 	mov    0xb8(%rax),%rax
  401fee:	48 83 c0 01          	add    $0x1,%rax
  401ff2:	be 08 00 00 00       	mov    $0x8,%esi
  401ff7:	48 89 c7             	mov    %rax,%rdi
  401ffa:	e8 d1 f0 ff ff       	call   4010d0 <calloc@plt>
  401fff:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  402003:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402007:	8b 40 68             	mov    0x68(%rax),%eax
  40200a:	48 98                	cltq
  40200c:	be 04 00 00 00       	mov    $0x4,%esi
  402011:	48 89 c7             	mov    %rax,%rdi
  402014:	e8 b7 f0 ff ff       	call   4010d0 <calloc@plt>
  402019:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
  int * readywriters = calloc(data->threadsize, sizeof(int));
  40201d:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402021:	8b 40 68             	mov    0x68(%rax),%eax
  402024:	48 98                	cltq
  402026:	be 04 00 00 00       	mov    $0x4,%esi
  40202b:	48 89 c7             	mov    %rax,%rdi
  40202e:	e8 9d f0 ff ff       	call   4010d0 <calloc@plt>
  402033:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  
  
  int stop = 0;
  402037:	c7 45 d4 00 00 00 00 	movl   $0x0,-0x2c(%rbp)
  while (data->running > 0)  {
  40203e:	eb 25                	jmp    402065 <work+0xda>
    writers = 0;
  402040:	c7 45 d8 00 00 00 00 	movl   $0x0,-0x28(%rbp)
    readers = 0;
  402047:	c7 45 dc 00 00 00 00 	movl   $0x0,-0x24(%rbp)
    stop = 0;
  40204e:	c7 45 d4 00 00 00 00 	movl   $0x0,-0x2c(%rbp)
    asm volatile ("":"=m" (data->running)::);
  402055:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
   // printf("write cycle\n");
    //memset(available, -1, data->threadsize);

      threadwork(data);
  402059:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  40205d:	48 89 c7             	mov    %rax,%rdi
  402060:	e8 b8 f8 ff ff       	call   40191d <threadwork>
  while (data->running > 0)  {
  402065:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402069:	8b 40 5c             	mov    0x5c(%rax),%eax
  40206c:	85 c0                	test   %eax,%eax
  40206e:	7f d0                	jg     402040 <work+0xb5>
        for (int x = 0 ; x < data->worksize; x++) {
          data->main->works[x].available = 1;
        }
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
  402070:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402074:	8b 40 64             	mov    0x64(%rax),%eax
  402077:	89 c6                	mov    %eax,%esi
  402079:	48 8d 05 bc 1f 00 00 	lea    0x1fbc(%rip),%rax        # 40403c <_IO_stdin_used+0x3c>
  402080:	48 89 c7             	mov    %rax,%rdi
  402083:	b8 00 00 00 00       	mov    $0x0,%eax
  402088:	e8 f3 ef ff ff       	call   401080 <printf@plt>
}
  40208d:	90                   	nop
  40208e:	c9                   	leave
  40208f:	c3                   	ret

0000000000402090 <main>:

int main(int argc, char **argv) {
  402090:	55                   	push   %rbp
  402091:	48 89 e5             	mov    %rsp,%rbp
  402094:	53                   	push   %rbx
  402095:	48 81 ec 78 01 00 00 	sub    $0x178,%rsp
  40209c:	89 bd 8c fe ff ff    	mov    %edi,-0x174(%rbp)
  4020a2:	48 89 b5 80 fe ff ff 	mov    %rsi,-0x180(%rbp)
  4020a9:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4020b2:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  4020b6:	31 c0                	xor    %eax,%eax
  int debug = 0;
  4020b8:	c7 85 a0 fe ff ff 00 00 00 00 	movl   $0x0,-0x160(%rbp)
  int seconds = DURATION;
  4020c2:	c7 85 a4 fe ff ff 01 00 00 00 	movl   $0x1,-0x15c(%rbp)
  int worksize_each = 1;
  4020cc:	c7 85 94 fe ff ff 01 00 00 00 	movl   $0x1,-0x16c(%rbp)
  int threadsize = THREADS;
  4020d6:	c7 85 98 fe ff ff 0f 00 00 00 	movl   $0xf,-0x168(%rbp)
  
  int workers = threadsize - 1;
  4020e0:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4020e6:	83 e8 01             	sub    $0x1,%eax
  4020e9:	89 85 9c fe ff ff    	mov    %eax,-0x164(%rbp)
  printf("read mask %d\n", READ_MASK);
  4020ef:	be 08 00 00 00       	mov    $0x8,%esi
  4020f4:	48 8d 05 51 1f 00 00 	lea    0x1f51(%rip),%rax        # 40404c <_IO_stdin_used+0x4c>
  4020fb:	48 89 c7             	mov    %rax,%rdi
  4020fe:	b8 00 00 00 00       	mov    $0x0,%eax
  402103:	e8 78 ef ff ff       	call   401080 <printf@plt>
  printf("write mask %d\n", WRITE_MASK);
  402108:	be 04 00 00 00       	mov    $0x4,%esi
  40210d:	48 8d 05 46 1f 00 00 	lea    0x1f46(%rip),%rax        # 40405a <_IO_stdin_used+0x5a>
  402114:	48 89 c7             	mov    %rax,%rdi
  402117:	b8 00 00 00 00       	mov    $0x0,%eax
  40211c:	e8 5f ef ff ff       	call   401080 <printf@plt>
  printf("prepwrite mask %d\n", PREP_WRITE_MASK);
  402121:	be 20 00 00 00       	mov    $0x20,%esi
  402126:	48 8d 05 3c 1f 00 00 	lea    0x1f3c(%rip),%rax        # 404069 <_IO_stdin_used+0x69>
  40212d:	48 89 c7             	mov    %rax,%rdi
  402130:	b8 00 00 00 00       	mov    $0x0,%eax
  402135:	e8 46 ef ff ff       	call   401080 <printf@plt>
  printf("Starting %d workers\n", threadsize);
  40213a:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402140:	89 c6                	mov    %eax,%esi
  402142:	48 8d 05 33 1f 00 00 	lea    0x1f33(%rip),%rax        # 40407c <_IO_stdin_used+0x7c>
  402149:	48 89 c7             	mov    %rax,%rdi
  40214c:	b8 00 00 00 00       	mov    $0x0,%eax
  402151:	e8 2a ef ff ff       	call   401080 <printf@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  402156:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40215c:	48 98                	cltq
  40215e:	be 08 00 00 00       	mov    $0x8,%esi
  402163:	48 89 c7             	mov    %rax,%rdi
  402166:	e8 65 ef ff ff       	call   4010d0 <calloc@plt>
  40216b:	48 89 85 18 ff ff ff 	mov    %rax,-0xe8(%rbp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  402172:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402178:	48 98                	cltq
  40217a:	be 38 00 00 00       	mov    $0x38,%esi
  40217f:	48 89 c7             	mov    %rax,%rdi
  402182:	e8 49 ef ff ff       	call   4010d0 <calloc@plt>
  402187:	48 89 85 f0 fe ff ff 	mov    %rax,-0x110(%rbp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40218e:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402194:	48 98                	cltq
  402196:	48 c1 e0 0a          	shl    $0xa,%rax
  40219a:	48 89 c6             	mov    %rax,%rsi
  40219d:	bf 01 00 00 00       	mov    $0x1,%edi
  4021a2:	e8 29 ef ff ff       	call   4010d0 <calloc@plt>
  4021a7:	48 89 85 f8 fe ff ff 	mov    %rax,-0x108(%rbp)
  
  long offset = 0;
  4021ae:	48 c7 85 00 ff ff ff 00 00 00 00 	movq   $0x0,-0x100(%rbp)
  long chunkslen = 0xffffffff;
  4021b9:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
  4021be:	48 89 85 08 ff ff ff 	mov    %rax,-0xf8(%rbp)
  long worksize = chunkslen * worksize_each;
  4021c5:	8b 85 94 fe ff ff    	mov    -0x16c(%rbp),%eax
  4021cb:	48 98                	cltq
  4021cd:	48 8b 95 08 ff ff ff 	mov    -0xf8(%rbp),%rdx
  4021d4:	48 0f af c2          	imul   %rdx,%rax
  4021d8:	48 89 85 10 ff ff ff 	mov    %rax,-0xf0(%rbp)
  int buckets = worksize / threadsize;
  4021df:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4021e5:	48 63 d8             	movslq %eax,%rbx
  4021e8:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  4021ef:	48 99                	cqto
  4021f1:	48 f7 fb             	idiv   %rbx
  4021f4:	89 85 90 fe ff ff    	mov    %eax,-0x170(%rbp)
  long chunksize = ceil((double) worksize / (double) chunkslen);
  4021fa:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4021fe:	f2 48 0f 2a 85 10 ff ff ff 	cvtsi2sdq -0xf0(%rbp),%xmm0
  402207:	66 0f ef c9          	pxor   %xmm1,%xmm1
  40220b:	f2 48 0f 2a 8d 08 ff ff ff 	cvtsi2sdq -0xf8(%rbp),%xmm1
  402214:	f2 0f 5e c1          	divsd  %xmm1,%xmm0
  402218:	66 48 0f 7e c0       	movq   %xmm0,%rax
  40221d:	66 48 0f 6e c0       	movq   %rax,%xmm0
  402222:	e8 f9 ee ff ff       	call   401120 <ceil@plt>
  402227:	f2 48 0f 2c c0       	cvttsd2si %xmm0,%rax
  40222c:	48 89 85 38 ff ff ff 	mov    %rax,-0xc8(%rbp)
  char *works = calloc(worksize, sizeof(char));
  402233:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  40223a:	be 01 00 00 00       	mov    $0x1,%esi
  40223f:	48 89 c7             	mov    %rax,%rdi
  402242:	e8 89 ee ff ff       	call   4010d0 <calloc@plt>
  402247:	48 89 85 40 ff ff ff 	mov    %rax,-0xc0(%rbp)
  memset(works, -1, worksize);
  40224e:	48 8b 95 10 ff ff ff 	mov    -0xf0(%rbp),%rdx
  402255:	48 8b 85 40 ff ff ff 	mov    -0xc0(%rbp),%rax
  40225c:	be ff ff ff ff       	mov    $0xffffffff,%esi
  402261:	48 89 c7             	mov    %rax,%rdi
  402264:	e8 57 ee ff ff       	call   4010c0 <memset@plt>
  printf("Buffer size %ld\n", worksize);
  402269:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  402270:	48 89 c6             	mov    %rax,%rsi
  402273:	48 8d 05 17 1e 00 00 	lea    0x1e17(%rip),%rax        # 404091 <_IO_stdin_used+0x91>
  40227a:	48 89 c7             	mov    %rax,%rdi
  40227d:	b8 00 00 00 00       	mov    $0x0,%eax
  402282:	e8 f9 ed ff ff       	call   401080 <printf@plt>
  int chunkindex = 0;
  402287:	c7 85 d4 fe ff ff 00 00 00 00 	movl   $0x0,-0x12c(%rbp)
  int * readcursors = calloc(threadsize, sizeof(int));
  402291:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402297:	48 98                	cltq
  402299:	be 04 00 00 00       	mov    $0x4,%esi
  40229e:	48 89 c7             	mov    %rax,%rdi
  4022a1:	e8 2a ee ff ff       	call   4010d0 <calloc@plt>
  4022a6:	48 89 85 48 ff ff ff 	mov    %rax,-0xb8(%rbp)
  int * writecursors = calloc(threadsize, sizeof(int));
  4022ad:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4022b3:	48 98                	cltq
  4022b5:	be 04 00 00 00       	mov    $0x4,%esi
  4022ba:	48 89 c7             	mov    %rax,%rdi
  4022bd:	e8 0e ee ff ff       	call   4010d0 <calloc@plt>
  4022c2:	48 89 85 50 ff ff ff 	mov    %rax,-0xb0(%rbp)
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4022c9:	be 20 00 00 00       	mov    $0x20,%esi
  4022ce:	bf 64 00 00 00       	mov    $0x64,%edi
  4022d3:	e8 f8 ed ff ff       	call   4010d0 <calloc@plt>
  4022d8:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)

printf("offset %ld\n", offset);
  4022df:	48 8b 85 00 ff ff ff 	mov    -0x100(%rbp),%rax
  4022e6:	48 89 c6             	mov    %rax,%rsi
  4022e9:	48 8d 05 b2 1d 00 00 	lea    0x1db2(%rip),%rax        # 4040a2 <_IO_stdin_used+0xa2>
  4022f0:	48 89 c7             	mov    %rax,%rdi
  4022f3:	b8 00 00 00 00       	mov    $0x0,%eax
  4022f8:	e8 83 ed ff ff       	call   401080 <printf@plt>
  
printf("%ld chunks\n", chunkslen);
  4022fd:	48 8b 85 08 ff ff ff 	mov    -0xf8(%rbp),%rax
  402304:	48 89 c6             	mov    %rax,%rsi
  402307:	48 8d 05 a0 1d 00 00 	lea    0x1da0(%rip),%rax        # 4040ae <_IO_stdin_used+0xae>
  40230e:	48 89 c7             	mov    %rax,%rdi
  402311:	b8 00 00 00 00       	mov    $0x0,%eax
  402316:	e8 65 ed ff ff       	call   401080 <printf@plt>
 // for (int i = 0; i < worksize; i++) {
   // works[i].taskindex = 2;
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  40231b:	c7 85 c4 fe ff ff 00 00 00 00 	movl   $0x0,-0x13c(%rbp)
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  402325:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40232b:	48 98                	cltq
  40232d:	be 04 00 00 00       	mov    $0x4,%esi
  402332:	48 89 c7             	mov    %rax,%rdi
  402335:	e8 96 ed ff ff       	call   4010d0 <calloc@plt>
  40233a:	48 89 85 60 ff ff ff 	mov    %rax,-0xa0(%rbp)
  
  long * globalwrite;
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  402341:	48 8d 85 e0 fe ff ff 	lea    -0x120(%rbp),%rax
  402348:	ba 00 02 00 00       	mov    $0x200,%edx
  40234d:	be 80 00 00 00       	mov    $0x80,%esi
  402352:	48 89 c7             	mov    %rax,%rdi
  402355:	e8 a6 ed ff ff       	call   401100 <posix_memalign@plt>
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  40235a:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402360:	48 98                	cltq
  402362:	be 0c 00 00 00       	mov    $0xc,%esi
  402367:	48 89 c7             	mov    %rax,%rdi
  40236a:	e8 61 ed ff ff       	call   4010d0 <calloc@plt>
  40236f:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
  data[0].works = works;
  402376:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40237d:	48 8b 95 40 ff ff ff 	mov    -0xc0(%rbp),%rdx
  402384:	48 89 50 70          	mov    %rdx,0x70(%rax)
  int accesssize = 100000000;
  402388:	c7 85 d8 fe ff ff 00 e1 f5 05 	movl   $0x5f5e100,-0x128(%rbp)
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  402392:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  402398:	48 98                	cltq
  40239a:	be 14 00 00 00       	mov    $0x14,%esi
  40239f:	48 89 c7             	mov    %rax,%rdi
  4023a2:	e8 29 ed ff ff       	call   4010d0 <calloc@plt>
  4023a7:	48 89 85 70 ff ff ff 	mov    %rax,-0x90(%rbp)
  struct Access * writes = calloc(accesssize, sizeof(struct Access));
  4023ae:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  4023b4:	48 98                	cltq
  4023b6:	be 14 00 00 00       	mov    $0x14,%esi
  4023bb:	48 89 c7             	mov    %rax,%rdi
  4023be:	e8 0d ed ff ff       	call   4010d0 <calloc@plt>
  4023c3:	48 89 85 78 ff ff ff 	mov    %rax,-0x88(%rbp)

  struct Scheduler * scheduler = calloc(1, sizeof(struct Scheduler));
  4023ca:	be 08 00 00 00       	mov    $0x8,%esi
  4023cf:	bf 01 00 00 00       	mov    $0x1,%edi
  4023d4:	e8 f7 ec ff ff       	call   4010d0 <calloc@plt>
  4023d9:	48 89 45 80          	mov    %rax,-0x80(%rbp)

  
  
  for (int x = 0; x < threadsize ; x++) {
  4023dd:	c7 85 c8 fe ff ff 00 00 00 00 	movl   $0x0,-0x138(%rbp)
  4023e7:	e9 e8 06 00 00       	jmp    402ad4 <main+0xa44>
    
    struct Coroutine * cos = calloc(10, sizeof(struct Coroutine));
  4023ec:	be 20 00 00 00       	mov    $0x20,%esi
  4023f1:	bf 0a 00 00 00       	mov    $0xa,%edi
  4023f6:	e8 d5 ec ff ff       	call   4010d0 <calloc@plt>
  4023fb:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
    
    data[x].coroutines = cos;
  4023ff:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402405:	48 98                	cltq
  402407:	48 c1 e0 0a          	shl    $0xa,%rax
  40240b:	48 89 c2             	mov    %rax,%rdx
  40240e:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402415:	48 01 c2             	add    %rax,%rdx
  402418:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40241c:	48 89 82 c0 03 00 00 	mov    %rax,0x3c0(%rdx)
    for (int y = 0; y < 10; y++ ) {
  402423:	c7 85 cc fe ff ff 00 00 00 00 	movl   $0x0,-0x134(%rbp)
  40242d:	e9 9e 00 00 00       	jmp    4024d0 <main+0x440>
      char * stack;
      posix_memalign((void **)&stack, 16, 8016);
  402432:	48 8d 45 d0          	lea    -0x30(%rbp),%rax
  402436:	ba 50 1f 00 00       	mov    $0x1f50,%edx
  40243b:	be 10 00 00 00       	mov    $0x10,%esi
  402440:	48 89 c7             	mov    %rax,%rdi
  402443:	e8 b8 ec ff ff       	call   401100 <posix_memalign@plt>
      
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
  402448:	be 04 00 00 00       	mov    $0x4,%esi
  40244d:	bf 01 00 00 00       	mov    $0x1,%edi
  402452:	e8 79 ec ff ff       	call   4010d0 <calloc@plt>
  402457:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
      cos[y].data = codata; 
  40245b:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  402461:	48 98                	cltq
  402463:	48 c1 e0 05          	shl    $0x5,%rax
  402467:	48 89 c2             	mov    %rax,%rdx
  40246a:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40246e:	48 01 c2             	add    %rax,%rdx
  402471:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  402475:	48 89 42 18          	mov    %rax,0x18(%rdx)
      codata->running = 1;
  402479:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  40247d:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
      cos[y].eip = (uint64_t)coroutine_func;
  402483:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  402489:	48 98                	cltq
  40248b:	48 c1 e0 05          	shl    $0x5,%rax
  40248f:	48 89 c2             	mov    %rax,%rdx
  402492:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  402496:	48 01 d0             	add    %rdx,%rax
  402499:	48 c7 c2 1d 12 40 00 	mov    $0x40121d,%rdx
  4024a0:	48 89 50 10          	mov    %rdx,0x10(%rax)
      cos[y].rsp = stack + 8016;
  4024a4:	48 8b 45 d0          	mov    -0x30(%rbp),%rax
  4024a8:	48 8d 90 50 1f 00 00 	lea    0x1f50(%rax),%rdx
  4024af:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  4024b5:	48 98                	cltq
  4024b7:	48 c1 e0 05          	shl    $0x5,%rax
  4024bb:	48 89 c1             	mov    %rax,%rcx
  4024be:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4024c2:	48 01 c8             	add    %rcx,%rax
  4024c5:	48 89 50 08          	mov    %rdx,0x8(%rax)
    for (int y = 0; y < 10; y++ ) {
  4024c9:	83 85 cc fe ff ff 01 	addl   $0x1,-0x134(%rbp)
  4024d0:	83 bd cc fe ff ff 09 	cmpl   $0x9,-0x134(%rbp)
  4024d7:	0f 8e 55 ff ff ff    	jle    402432 <main+0x3a2>
    }
    data[x].scheduler = scheduler;  
  4024dd:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4024e3:	48 98                	cltq
  4024e5:	48 c1 e0 0a          	shl    $0xa,%rax
  4024e9:	48 89 c2             	mov    %rax,%rdx
  4024ec:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4024f3:	48 01 c2             	add    %rax,%rdx
  4024f6:	48 8b 45 80          	mov    -0x80(%rbp),%rax
  4024fa:	48 89 82 c8 03 00 00 	mov    %rax,0x3c8(%rdx)
    data[x].reads = reads;
  402501:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402507:	48 98                	cltq
  402509:	48 c1 e0 0a          	shl    $0xa,%rax
  40250d:	48 89 c2             	mov    %rax,%rdx
  402510:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402517:	48 01 c2             	add    %rax,%rdx
  40251a:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
  402521:	48 89 82 a0 03 00 00 	mov    %rax,0x3a0(%rdx)
    data[x].writes = writes; 
  402528:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40252e:	48 98                	cltq
  402530:	48 c1 e0 0a          	shl    $0xa,%rax
  402534:	48 89 c2             	mov    %rax,%rdx
  402537:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40253e:	48 01 c2             	add    %rax,%rdx
  402541:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  402548:	48 89 82 a8 03 00 00 	mov    %rax,0x3a8(%rdx)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t)); 
  40254f:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402555:	48 98                	cltq
  402557:	48 c1 e0 0a          	shl    $0xa,%rax
  40255b:	48 89 c2             	mov    %rax,%rdx
  40255e:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402565:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  402569:	be 80 00 00 00       	mov    $0x80,%esi
  40256e:	bf 01 00 00 00       	mov    $0x1,%edi
  402573:	e8 58 eb ff ff       	call   4010d0 <calloc@plt>
  402578:	48 89 43 78          	mov    %rax,0x78(%rbx)
    CPU_SET(cpu += 1, data[x].cpu_set);
  40257c:	83 85 c4 fe ff ff 01 	addl   $0x1,-0x13c(%rbp)
  402583:	8b 85 c4 fe ff ff    	mov    -0x13c(%rbp),%eax
  402589:	48 98                	cltq
  40258b:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  40258f:	48 81 7d b0 ff 03 00 00 	cmpq   $0x3ff,-0x50(%rbp)
  402597:	77 78                	ja     402611 <main+0x581>
  402599:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40259f:	48 98                	cltq
  4025a1:	48 c1 e0 0a          	shl    $0xa,%rax
  4025a5:	48 89 c2             	mov    %rax,%rdx
  4025a8:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4025af:	48 01 d0             	add    %rdx,%rax
  4025b2:	48 8b 40 78          	mov    0x78(%rax),%rax
  4025b6:	48 89 c1             	mov    %rax,%rcx
  4025b9:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
  4025bd:	48 c1 e8 06          	shr    $0x6,%rax
  4025c1:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4025c9:	48 01 ca             	add    %rcx,%rdx
  4025cc:	48 8b 32             	mov    (%rdx),%rsi
  4025cf:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
  4025d3:	83 e2 3f             	and    $0x3f,%edx
  4025d6:	bf 01 00 00 00       	mov    $0x1,%edi
  4025db:	89 d1                	mov    %edx,%ecx
  4025dd:	48 d3 e7             	shl    %cl,%rdi
  4025e0:	48 89 f9             	mov    %rdi,%rcx
  4025e3:	8b 95 c8 fe ff ff    	mov    -0x138(%rbp),%edx
  4025e9:	48 63 d2             	movslq %edx,%rdx
  4025ec:	48 89 d7             	mov    %rdx,%rdi
  4025ef:	48 c1 e7 0a          	shl    $0xa,%rdi
  4025f3:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4025fa:	48 01 fa             	add    %rdi,%rdx
  4025fd:	48 8b 52 78          	mov    0x78(%rdx),%rdx
  402601:	48 c1 e0 03          	shl    $0x3,%rax
  402605:	48 01 d0             	add    %rdx,%rax
  402608:	48 09 ce             	or     %rcx,%rsi
  40260b:	48 89 f2             	mov    %rsi,%rdx
  40260e:	48 89 10             	mov    %rdx,(%rax)
    printf("assigning thread %d to cpu %d\n", x, cpu);
  402611:	8b 95 c4 fe ff ff    	mov    -0x13c(%rbp),%edx
  402617:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40261d:	89 c6                	mov    %eax,%esi
  40261f:	48 8d 05 9a 1a 00 00 	lea    0x1a9a(%rip),%rax        # 4040c0 <_IO_stdin_used+0xc0>
  402626:	48 89 c7             	mov    %rax,%rdi
  402629:	b8 00 00 00 00       	mov    $0x0,%eax
  40262e:	e8 4d ea ff ff       	call   401080 <printf@plt>
    data[x].bucketstart = x * buckets ;
  402633:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402639:	48 98                	cltq
  40263b:	48 c1 e0 0a          	shl    $0xa,%rax
  40263f:	48 89 c2             	mov    %rax,%rdx
  402642:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402649:	48 01 c2             	add    %rax,%rdx
  40264c:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402652:	0f af 85 90 fe ff ff 	imul   -0x170(%rbp),%eax
  402659:	89 82 98 00 00 00    	mov    %eax,0x98(%rdx)
    data[x].globalwrite = globalwrite;
  40265f:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402665:	48 98                	cltq
  402667:	48 c1 e0 0a          	shl    $0xa,%rax
  40266b:	48 89 c2             	mov    %rax,%rdx
  40266e:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402675:	48 01 c2             	add    %rax,%rdx
  402678:	48 8b 85 e0 fe ff ff 	mov    -0x120(%rbp),%rax
  40267f:	48 89 82 80 03 00 00 	mov    %rax,0x380(%rdx)
    data[x].loglevel = debug;
  402686:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40268c:	48 98                	cltq
  40268e:	48 c1 e0 0a          	shl    $0xa,%rax
  402692:	48 89 c2             	mov    %rax,%rdx
  402695:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40269c:	48 01 c2             	add    %rax,%rdx
  40269f:	8b 85 a0 fe ff ff    	mov    -0x160(%rbp),%eax
  4026a5:	89 82 80 00 00 00    	mov    %eax,0x80(%rdx)
    data[x].running = 2;
  4026ab:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026b1:	48 98                	cltq
  4026b3:	48 c1 e0 0a          	shl    $0xa,%rax
  4026b7:	48 89 c2             	mov    %rax,%rdx
  4026ba:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026c1:	48 01 d0             	add    %rdx,%rax
  4026c4:	c7 40 5c 02 00 00 00 	movl   $0x2,0x5c(%rax)
    data[x].threadindex = x;
  4026cb:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026d1:	48 98                	cltq
  4026d3:	48 c1 e0 0a          	shl    $0xa,%rax
  4026d7:	48 89 c2             	mov    %rax,%rdx
  4026da:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026e1:	48 01 c2             	add    %rax,%rdx
  4026e4:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026ea:	89 42 64             	mov    %eax,0x64(%rdx)
    data[x].worksize = worksize;
  4026ed:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026f3:	48 98                	cltq
  4026f5:	48 c1 e0 0a          	shl    $0xa,%rax
  4026f9:	48 89 c2             	mov    %rax,%rdx
  4026fc:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402703:	48 01 d0             	add    %rdx,%rax
  402706:	48 8b 95 10 ff ff ff 	mov    -0xf0(%rbp),%rdx
  40270d:	89 50 60             	mov    %edx,0x60(%rax)
    
    data[x].availables = buckets;
  402710:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402716:	48 98                	cltq
  402718:	48 c1 e0 0a          	shl    $0xa,%rax
  40271c:	48 89 c2             	mov    %rax,%rdx
  40271f:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402726:	48 01 c2             	add    %rax,%rdx
  402729:	8b 85 90 fe ff ff    	mov    -0x170(%rbp),%eax
  40272f:	89 82 94 00 00 00    	mov    %eax,0x94(%rdx)
    data[x].threadsize = threadsize;
  402735:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40273b:	48 98                	cltq
  40273d:	48 c1 e0 0a          	shl    $0xa,%rax
  402741:	48 89 c2             	mov    %rax,%rdx
  402744:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40274b:	48 01 c2             	add    %rax,%rdx
  40274e:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402754:	89 42 68             	mov    %eax,0x68(%rdx)
    data[x].readies = readies;
  402757:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40275d:	48 98                	cltq
  40275f:	48 c1 e0 0a          	shl    $0xa,%rax
  402763:	48 89 c2             	mov    %rax,%rdx
  402766:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40276d:	48 01 c2             	add    %rax,%rdx
  402770:	48 8b 85 60 ff ff ff 	mov    -0xa0(%rbp),%rax
  402777:	48 89 42 20          	mov    %rax,0x20(%rdx)
    data[x].readies[x] = 0;
  40277b:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402781:	48 98                	cltq
  402783:	48 c1 e0 0a          	shl    $0xa,%rax
  402787:	48 89 c2             	mov    %rax,%rdx
  40278a:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402791:	48 01 d0             	add    %rdx,%rax
  402794:	48 8b 50 20          	mov    0x20(%rax),%rdx
  402798:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40279e:	48 98                	cltq
  4027a0:	48 c1 e0 02          	shl    $0x2,%rax
  4027a4:	48 01 d0             	add    %rdx,%rax
  4027a7:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    data[x].buckets = buckets;
  4027ad:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027b3:	48 98                	cltq
  4027b5:	48 c1 e0 0a          	shl    $0xa,%rax
  4027b9:	48 89 c2             	mov    %rax,%rdx
  4027bc:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027c3:	48 01 c2             	add    %rax,%rdx
  4027c6:	8b 85 90 fe ff ff    	mov    -0x170(%rbp),%eax
  4027cc:	89 82 90 00 00 00    	mov    %eax,0x90(%rdx)
    data[x].main = &data[0];
  4027d2:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027d8:	48 98                	cltq
  4027da:	48 c1 e0 0a          	shl    $0xa,%rax
  4027de:	48 89 c2             	mov    %rax,%rdx
  4027e1:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027e8:	48 01 c2             	add    %rax,%rdx
  4027eb:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027f2:	48 89 42 28          	mov    %rax,0x28(%rdx)
    data[x].threads = data;
  4027f6:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027fc:	48 98                	cltq
  4027fe:	48 c1 e0 0a          	shl    $0xa,%rax
  402802:	48 89 c2             	mov    %rax,%rdx
  402805:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40280c:	48 01 c2             	add    %rax,%rdx
  40280f:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402816:	48 89 42 30          	mov    %rax,0x30(%rdx)
    
    data[x].read = 0;
  40281a:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402820:	48 98                	cltq
  402822:	48 c1 e0 0a          	shl    $0xa,%rax
  402826:	48 89 c2             	mov    %rax,%rdx
  402829:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402830:	48 01 d0             	add    %rdx,%rax
  402833:	48 c7 00 00 00 00 00 	movq   $0x0,(%rax)
    data[x].write = worksize;
  40283a:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402840:	48 98                	cltq
  402842:	48 c1 e0 0a          	shl    $0xa,%rax
  402846:	48 89 c2             	mov    %rax,%rdx
  402849:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402850:	48 01 c2             	add    %rax,%rdx
  402853:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  40285a:	48 89 42 08          	mov    %rax,0x8(%rdx)
    data[x].readcursor = threadsize - 1;
  40285e:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402864:	48 98                	cltq
  402866:	48 c1 e0 0a          	shl    $0xa,%rax
  40286a:	48 89 c2             	mov    %rax,%rdx
  40286d:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402874:	48 01 d0             	add    %rdx,%rax
  402877:	8b 95 98 fe ff ff    	mov    -0x168(%rbp),%edx
  40287d:	83 ea 01             	sub    $0x1,%edx
  402880:	89 90 00 02 00 00    	mov    %edx,0x200(%rax)
    data[x].writecursor = 0;
  402886:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40288c:	48 98                	cltq
  40288e:	48 c1 e0 0a          	shl    $0xa,%rax
  402892:	48 89 c2             	mov    %rax,%rdx
  402895:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40289c:	48 01 d0             	add    %rdx,%rax
  40289f:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    data[x].freelist = freelist;
  4028a9:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028af:	48 98                	cltq
  4028b1:	48 c1 e0 0a          	shl    $0xa,%rax
  4028b5:	48 89 c2             	mov    %rax,%rdx
  4028b8:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4028bf:	48 01 c2             	add    %rax,%rdx
  4028c2:	48 8b 85 58 ff ff ff 	mov    -0xa8(%rbp),%rax
  4028c9:	48 89 82 a0 00 00 00 	mov    %rax,0xa0(%rdx)
    data[x].chunksize = chunksize;
  4028d0:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028d6:	48 98                	cltq
  4028d8:	48 c1 e0 0a          	shl    $0xa,%rax
  4028dc:	48 89 c2             	mov    %rax,%rdx
  4028df:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4028e6:	48 01 c2             	add    %rax,%rdx
  4028e9:	48 8b 85 38 ff ff ff 	mov    -0xc8(%rbp),%rax
  4028f0:	48 89 82 c0 00 00 00 	mov    %rax,0xc0(%rdx)
    data[x].chunkslen = chunkslen;
  4028f7:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028fd:	48 98                	cltq
  4028ff:	48 c1 e0 0a          	shl    $0xa,%rax
  402903:	48 89 c2             	mov    %rax,%rdx
  402906:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40290d:	48 01 c2             	add    %rax,%rdx
  402910:	48 8b 85 08 ff ff ff 	mov    -0xf8(%rbp),%rax
  402917:	48 89 82 b8 00 00 00 	mov    %rax,0xb8(%rdx)
    data[x].newmask = 0;
  40291e:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402924:	48 98                	cltq
  402926:	48 c1 e0 0a          	shl    $0xa,%rax
  40292a:	48 89 c2             	mov    %rax,%rdx
  40292d:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402934:	48 01 d0             	add    %rdx,%rax
  402937:	c7 80 c8 00 00 00 00 00 00 00 	movl   $0x0,0xc8(%rax)
    data[x].prevread = threadsize;
  402941:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402947:	48 98                	cltq
  402949:	48 c1 e0 0a          	shl    $0xa,%rax
  40294d:	48 89 c2             	mov    %rax,%rdx
  402950:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402957:	48 01 c2             	add    %rax,%rdx
  40295a:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402960:	48 98                	cltq
  402962:	48 89 82 08 03 00 00 	mov    %rax,0x308(%rdx)
    data[x].prevwrite = threadsize;
  402969:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40296f:	48 98                	cltq
  402971:	48 c1 e0 0a          	shl    $0xa,%rax
  402975:	48 89 c2             	mov    %rax,%rdx
  402978:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40297f:	48 01 c2             	add    %rax,%rdx
  402982:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402988:	48 98                	cltq
  40298a:	48 89 82 10 03 00 00 	mov    %rax,0x310(%rdx)
    data[x].mystream = 1 + (x / 4);
  402991:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402997:	8d 50 03             	lea    0x3(%rax),%edx
  40299a:	85 c0                	test   %eax,%eax
  40299c:	0f 48 c2             	cmovs  %edx,%eax
  40299f:	c1 f8 02             	sar    $0x2,%eax
  4029a2:	89 c2                	mov    %eax,%edx
  4029a4:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4029aa:	48 98                	cltq
  4029ac:	48 c1 e0 0a          	shl    $0xa,%rax
  4029b0:	48 89 c1             	mov    %rax,%rcx
  4029b3:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4029ba:	48 01 c8             	add    %rcx,%rax
  4029bd:	83 c2 01             	add    $0x1,%edx
  4029c0:	89 90 8c 03 00 00    	mov    %edx,0x38c(%rax)
    data[x].thiswrite = threadsize;
  4029c6:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4029cc:	48 98                	cltq
  4029ce:	48 c1 e0 0a          	shl    $0xa,%rax
  4029d2:	48 89 c2             	mov    %rax,%rdx
  4029d5:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4029dc:	48 01 c2             	add    %rax,%rdx
  4029df:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4029e5:	89 82 28 03 00 00    	mov    %eax,0x328(%rdx)
    int epochs = 10000000;
  4029eb:	c7 85 dc fe ff ff 80 96 98 00 	movl   $0x989680,-0x124(%rbp)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4029f5:	8b 85 dc fe ff ff    	mov    -0x124(%rbp),%eax
  4029fb:	48 98                	cltq
  4029fd:	8b 95 c8 fe ff ff    	mov    -0x138(%rbp),%edx
  402a03:	48 63 d2             	movslq %edx,%rdx
  402a06:	48 89 d1             	mov    %rdx,%rcx
  402a09:	48 c1 e1 0a          	shl    $0xa,%rcx
  402a0d:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  402a14:	48 8d 1c 11          	lea    (%rcx,%rdx,1),%rbx
  402a18:	be 30 00 00 00       	mov    $0x30,%esi
  402a1d:	48 89 c7             	mov    %rax,%rdi
  402a20:	e8 ab e6 ff ff       	call   4010d0 <calloc@plt>
  402a25:	48 89 83 18 03 00 00 	mov    %rax,0x318(%rbx)
    data[x].epochssize = epochs;
  402a2c:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a32:	48 98                	cltq
  402a34:	48 c1 e0 0a          	shl    $0xa,%rax
  402a38:	48 89 c2             	mov    %rax,%rdx
  402a3b:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a42:	48 01 c2             	add    %rax,%rdx
  402a45:	8b 85 dc fe ff ff    	mov    -0x124(%rbp),%eax
  402a4b:	89 82 20 03 00 00    	mov    %eax,0x320(%rdx)
    data[x].globalread = globalread;
  402a51:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a57:	48 98                	cltq
  402a59:	48 c1 e0 0a          	shl    $0xa,%rax
  402a5d:	48 89 c2             	mov    %rax,%rdx
  402a60:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a67:	48 01 c2             	add    %rax,%rdx
  402a6a:	48 8b 85 68 ff ff ff 	mov    -0x98(%rbp),%rax
  402a71:	48 89 82 48 03 00 00 	mov    %rax,0x348(%rdx)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  402a78:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a7e:	48 98                	cltq
  402a80:	48 c1 e0 0a          	shl    $0xa,%rax
  402a84:	48 89 c2             	mov    %rax,%rdx
  402a87:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a8e:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  402a92:	be 30 00 00 00       	mov    $0x30,%esi
  402a97:	bf 10 27 00 00       	mov    $0x2710,%edi
  402a9c:	e8 2f e6 ff ff       	call   4010d0 <calloc@plt>
  402aa1:	48 89 83 30 03 00 00 	mov    %rax,0x330(%rbx)
    data[x].accesssize = accesssize;
  402aa8:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402aae:	48 98                	cltq
  402ab0:	48 c1 e0 0a          	shl    $0xa,%rax
  402ab4:	48 89 c2             	mov    %rax,%rdx
  402ab7:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402abe:	48 01 c2             	add    %rax,%rdx
  402ac1:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  402ac7:	89 82 b8 03 00 00    	mov    %eax,0x3b8(%rdx)
  for (int x = 0; x < threadsize ; x++) {
  402acd:	83 85 c8 fe ff ff 01 	addl   $0x1,-0x138(%rbp)
  402ad4:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402ada:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402ae0:	0f 8c 06 f9 ff ff    	jl     4023ec <main+0x35c>
  } 
  
  for (int x = 0; x < threadsize ; x++) {
  402ae6:	c7 85 d0 fe ff ff 00 00 00 00 	movl   $0x0,-0x130(%rbp)
  402af0:	e9 b8 00 00 00       	jmp    402bad <main+0xb1d>
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  402af5:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402afb:	48 98                	cltq
  402afd:	48 c1 e0 0a          	shl    $0xa,%rax
  402b01:	48 89 c2             	mov    %rax,%rdx
  402b04:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402b0b:	48 01 c2             	add    %rax,%rdx
  402b0e:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b14:	48 63 c8             	movslq %eax,%rcx
  402b17:	48 89 c8             	mov    %rcx,%rax
  402b1a:	48 c1 e0 03          	shl    $0x3,%rax
  402b1e:	48 29 c8             	sub    %rcx,%rax
  402b21:	48 c1 e0 03          	shl    $0x3,%rax
  402b25:	48 89 c1             	mov    %rax,%rcx
  402b28:	48 8b 85 f0 fe ff ff 	mov    -0x110(%rbp),%rax
  402b2f:	48 8d 34 01          	lea    (%rcx,%rax,1),%rsi
  402b33:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b39:	48 98                	cltq
  402b3b:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
  402b43:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402b4a:	48 01 c8             	add    %rcx,%rax
  402b4d:	48 89 d1             	mov    %rdx,%rcx
  402b50:	48 c7 c2 8b 1f 40 00 	mov    $0x401f8b,%rdx
  402b57:	48 89 c7             	mov    %rax,%rdi
  402b5a:	e8 81 e5 ff ff       	call   4010e0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  402b5f:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b65:	48 98                	cltq
  402b67:	48 c1 e0 0a          	shl    $0xa,%rax
  402b6b:	48 89 c2             	mov    %rax,%rdx
  402b6e:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402b75:	48 01 d0             	add    %rdx,%rax
  402b78:	48 8b 50 78          	mov    0x78(%rax),%rdx
  402b7c:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b82:	48 98                	cltq
  402b84:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
  402b8c:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402b93:	48 01 c8             	add    %rcx,%rax
  402b96:	48 8b 00             	mov    (%rax),%rax
  402b99:	be 08 00 00 00       	mov    $0x8,%esi
  402b9e:	48 89 c7             	mov    %rax,%rdi
  402ba1:	e8 8a e4 ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  402ba6:	83 85 d0 fe ff ff 01 	addl   $0x1,-0x130(%rbp)
  402bad:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402bb3:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402bb9:	0f 8c 36 ff ff ff    	jl     402af5 <main+0xa65>
  }
  
  struct timespec time = {
  402bbf:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402bc5:	48 98                	cltq
  402bc7:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
  402bcb:	48 c7 45 c8 00 00 00 00 	movq   $0x0,-0x38(%rbp)
    seconds,
    0
  };
  struct timespec rem = {
  402bd3:	48 c7 45 d0 00 00 00 00 	movq   $0x0,-0x30(%rbp)
  402bdb:	48 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%rbp)
    0,
    0
  };
  
  nanosleep(&time, &rem);
  402be3:	48 8d 55 d0          	lea    -0x30(%rbp),%rdx
  402be7:	48 8d 45 c0          	lea    -0x40(%rbp),%rax
  402beb:	48 89 d6             	mov    %rdx,%rsi
  402bee:	48 89 c7             	mov    %rax,%rdi
  402bf1:	e8 aa e4 ff ff       	call   4010a0 <nanosleep@plt>
  
  printf("runphased\n");
  402bf6:	48 8d 05 e2 14 00 00 	lea    0x14e2(%rip),%rax        # 4040df <_IO_stdin_used+0xdf>
  402bfd:	48 89 c7             	mov    %rax,%rdi
  402c00:	e8 3b e4 ff ff       	call   401040 <puts@plt>
  for (int x = 0; x < threadsize ; x++) {
  402c05:	c7 85 b8 fe ff ff 00 00 00 00 	movl   $0x0,-0x148(%rbp)
  402c0f:	eb 29                	jmp    402c3a <main+0xbaa>
    data[x].running--;
  402c11:	8b 85 b8 fe ff ff    	mov    -0x148(%rbp),%eax
  402c17:	48 98                	cltq
  402c19:	48 c1 e0 0a          	shl    $0xa,%rax
  402c1d:	48 89 c2             	mov    %rax,%rdx
  402c20:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402c27:	48 01 d0             	add    %rdx,%rax
  402c2a:	8b 50 5c             	mov    0x5c(%rax),%edx
  402c2d:	83 ea 01             	sub    $0x1,%edx
  402c30:	89 50 5c             	mov    %edx,0x5c(%rax)
  for (int x = 0; x < threadsize ; x++) {
  402c33:	83 85 b8 fe ff ff 01 	addl   $0x1,-0x148(%rbp)
  402c3a:	8b 85 b8 fe ff ff    	mov    -0x148(%rbp),%eax
  402c40:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402c46:	7c c9                	jl     402c11 <main+0xb81>
    
  }
  
 printf("draining\n");
  402c48:	48 8d 05 9a 14 00 00 	lea    0x149a(%rip),%rax        # 4040e9 <_IO_stdin_used+0xe9>
  402c4f:	48 89 c7             	mov    %rax,%rdi
  402c52:	e8 e9 e3 ff ff       	call   401040 <puts@plt>
 // time.tv_sec = 3;
//nanosleep(&time, &rem);
  for (int x = 0; x < threadsize ; x++) {
  402c57:	c7 85 bc fe ff ff 00 00 00 00 	movl   $0x0,-0x144(%rbp)
  402c61:	eb 29                	jmp    402c8c <main+0xbfc>
    data[x].running--;
  402c63:	8b 85 bc fe ff ff    	mov    -0x144(%rbp),%eax
  402c69:	48 98                	cltq
  402c6b:	48 c1 e0 0a          	shl    $0xa,%rax
  402c6f:	48 89 c2             	mov    %rax,%rdx
  402c72:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402c79:	48 01 d0             	add    %rdx,%rax
  402c7c:	8b 50 5c             	mov    0x5c(%rax),%edx
  402c7f:	83 ea 01             	sub    $0x1,%edx
  402c82:	89 50 5c             	mov    %edx,0x5c(%rax)
  for (int x = 0; x < threadsize ; x++) {
  402c85:	83 85 bc fe ff ff 01 	addl   $0x1,-0x144(%rbp)
  402c8c:	8b 85 bc fe ff ff    	mov    -0x144(%rbp),%eax
  402c92:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402c98:	7c c9                	jl     402c63 <main+0xbd3>
  }
  
  //nanosleep(&time, &rem);
  for (int x = 0; x < threadsize; x++) {
  402c9a:	c7 85 c0 fe ff ff 00 00 00 00 	movl   $0x0,-0x140(%rbp)
  402ca4:	eb 36                	jmp    402cdc <main+0xc4c>
    void *res;
    pthread_join(thread[x], &res);
  402ca6:	8b 85 c0 fe ff ff    	mov    -0x140(%rbp),%eax
  402cac:	48 98                	cltq
  402cae:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  402cb6:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402cbd:	48 01 d0             	add    %rdx,%rax
  402cc0:	48 8b 00             	mov    (%rax),%rax
  402cc3:	48 8d 95 e8 fe ff ff 	lea    -0x118(%rbp),%rdx
  402cca:	48 89 d6             	mov    %rdx,%rsi
  402ccd:	48 89 c7             	mov    %rax,%rdi
  402cd0:	e8 3b e4 ff ff       	call   401110 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  402cd5:	83 85 c0 fe ff ff 01 	addl   $0x1,-0x140(%rbp)
  402cdc:	8b 85 c0 fe ff ff    	mov    -0x140(%rbp),%eax
  402ce2:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402ce8:	7c bc                	jl     402ca6 <main+0xc16>
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  402cea:	48 8d 05 01 14 00 00 	lea    0x1401(%rip),%rax        # 4040f2 <_IO_stdin_used+0xf2>
  402cf1:	48 89 c7             	mov    %rax,%rdi
  402cf4:	e8 47 e3 ff ff       	call   401040 <puts@plt>
  long freq = 0;
  402cf9:	48 c7 85 20 ff ff ff 00 00 00 00 	movq   $0x0,-0xe0(%rbp)
  long sends = 1;
  402d04:	48 c7 45 88 01 00 00 00 	movq   $0x1,-0x78(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402d0c:	c7 85 a8 fe ff ff 00 00 00 00 	movl   $0x0,-0x158(%rbp)
  402d16:	eb 5f                	jmp    402d77 <main+0xce7>
    printf("%ld reads\n", data[x].freq);
  402d18:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d1e:	48 98                	cltq
  402d20:	48 c1 e0 0a          	shl    $0xa,%rax
  402d24:	48 89 c2             	mov    %rax,%rdx
  402d27:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402d2e:	48 01 d0             	add    %rdx,%rax
  402d31:	48 8b 40 48          	mov    0x48(%rax),%rax
  402d35:	48 89 c6             	mov    %rax,%rsi
  402d38:	48 8d 05 c8 13 00 00 	lea    0x13c8(%rip),%rax        # 404107 <_IO_stdin_used+0x107>
  402d3f:	48 89 c7             	mov    %rax,%rdi
  402d42:	b8 00 00 00 00       	mov    $0x0,%eax
  402d47:	e8 34 e3 ff ff       	call   401080 <printf@plt>
    freq += data[x].freq;
  402d4c:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d52:	48 98                	cltq
  402d54:	48 c1 e0 0a          	shl    $0xa,%rax
  402d58:	48 89 c2             	mov    %rax,%rdx
  402d5b:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402d62:	48 01 d0             	add    %rdx,%rax
  402d65:	48 8b 40 48          	mov    0x48(%rax),%rax
  402d69:	48 01 85 20 ff ff ff 	add    %rax,-0xe0(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402d70:	83 85 a8 fe ff ff 01 	addl   $0x1,-0x158(%rbp)
  402d77:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d7d:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402d83:	7c 93                	jl     402d18 <main+0xc88>
  }
  printf("freq: %ld\n", freq/ seconds);
  402d85:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402d8b:	48 63 d8             	movslq %eax,%rbx
  402d8e:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402d95:	48 99                	cqto
  402d97:	48 f7 fb             	idiv   %rbx
  402d9a:	48 89 c6             	mov    %rax,%rsi
  402d9d:	48 8d 05 6e 13 00 00 	lea    0x136e(%rip),%rax        # 404112 <_IO_stdin_used+0x112>
  402da4:	48 89 c7             	mov    %rax,%rdi
  402da7:	b8 00 00 00 00       	mov    $0x0,%eax
  402dac:	e8 cf e2 ff ff       	call   401080 <printf@plt>
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  402db1:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402db8:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  402dbd:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402dc3:	48 63 da             	movslq %edx,%rbx
  402dc6:	48 99                	cqto
  402dc8:	48 f7 fb             	idiv   %rbx
  402dcb:	48 89 c6             	mov    %rax,%rsi
  402dce:	48 8d 05 48 13 00 00 	lea    0x1348(%rip),%rax        # 40411d <_IO_stdin_used+0x11d>
  402dd5:	48 89 c7             	mov    %rax,%rdi
  402dd8:	b8 00 00 00 00       	mov    $0x0,%eax
  402ddd:	e8 9e e2 ff ff       	call   401080 <printf@plt>
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  402de2:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402de8:	48 63 d8             	movslq %eax,%rbx
  402deb:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402df2:	48 99                	cqto
  402df4:	48 f7 fb             	idiv   %rbx
  402df7:	48 89 c3             	mov    %rax,%rbx
  402dfa:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402dff:	48 99                	cqto
  402e01:	48 f7 fb             	idiv   %rbx
  402e04:	48 89 c6             	mov    %rax,%rsi
  402e07:	48 8d 05 1d 13 00 00 	lea    0x131d(%rip),%rax        # 40412b <_IO_stdin_used+0x12b>
  402e0e:	48 89 c7             	mov    %rax,%rdi
  402e11:	b8 00 00 00 00       	mov    $0x0,%eax
  402e16:	e8 65 e2 ff ff       	call   401080 <printf@plt>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  402e1b:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402e21:	48 63 d8             	movslq %eax,%rbx
  402e24:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402e2b:	48 99                	cqto
  402e2d:	48 f7 fb             	idiv   %rbx
  402e30:	48 89 c3             	mov    %rax,%rbx
  402e33:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402e38:	48 99                	cqto
  402e3a:	48 f7 fb             	idiv   %rbx
  402e3d:	48 99                	cqto
  402e3f:	48 f7 7d 88          	idivq  -0x78(%rbp)
  402e43:	48 89 c6             	mov    %rax,%rsi
  402e46:	48 8d 05 f2 12 00 00 	lea    0x12f2(%rip),%rax        # 40413f <_IO_stdin_used+0x13f>
  402e4d:	48 89 c7             	mov    %rax,%rdi
  402e50:	b8 00 00 00 00       	mov    $0x0,%eax
  402e55:	e8 26 e2 ff ff       	call   401080 <printf@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  402e5a:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402e61:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  402e66:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402e6c:	48 63 da             	movslq %edx,%rbx
  402e6f:	48 99                	cqto
  402e71:	48 f7 fb             	idiv   %rbx
  402e74:	48 89 c3             	mov    %rax,%rbx
  402e77:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402e7c:	48 99                	cqto
  402e7e:	48 f7 fb             	idiv   %rbx
  402e81:	48 89 c6             	mov    %rax,%rsi
  402e84:	48 8d 05 d2 12 00 00 	lea    0x12d2(%rip),%rax        # 40415d <_IO_stdin_used+0x15d>
  402e8b:	48 89 c7             	mov    %rax,%rdi
  402e8e:	b8 00 00 00 00       	mov    $0x0,%eax
  402e93:	e8 e8 e1 ff ff       	call   401080 <printf@plt>
  
  long goods = 0;
  402e98:	48 c7 85 28 ff ff ff 00 00 00 00 	movq   $0x0,-0xd8(%rbp)

  for (int x = 0; x < threadsize; x++) {
  402ea3:	c7 85 ac fe ff ff 00 00 00 00 	movl   $0x0,-0x154(%rbp)
  402ead:	eb 65                	jmp    402f14 <main+0xe84>
    printf("%ld successreads\n", data[x].successreads);
  402eaf:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402eb5:	48 98                	cltq
  402eb7:	48 c1 e0 0a          	shl    $0xa,%rax
  402ebb:	48 89 c2             	mov    %rax,%rdx
  402ebe:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402ec5:	48 01 d0             	add    %rdx,%rax
  402ec8:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  402ecf:	48 89 c6             	mov    %rax,%rsi
  402ed2:	48 8d 05 97 12 00 00 	lea    0x1297(%rip),%rax        # 404170 <_IO_stdin_used+0x170>
  402ed9:	48 89 c7             	mov    %rax,%rdi
  402edc:	b8 00 00 00 00       	mov    $0x0,%eax
  402ee1:	e8 9a e1 ff ff       	call   401080 <printf@plt>
    goods += data[x].successreads;
  402ee6:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402eec:	48 98                	cltq
  402eee:	48 c1 e0 0a          	shl    $0xa,%rax
  402ef2:	48 89 c2             	mov    %rax,%rdx
  402ef5:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402efc:	48 01 d0             	add    %rdx,%rax
  402eff:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  402f06:	48 01 85 28 ff ff ff 	add    %rax,-0xd8(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402f0d:	83 85 ac fe ff ff 01 	addl   $0x1,-0x154(%rbp)
  402f14:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402f1a:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402f20:	7c 8d                	jl     402eaf <main+0xe1f>
  }
  
  long freq_writes = 0;
  402f22:	48 c7 85 30 ff ff ff 00 00 00 00 	movq   $0x0,-0xd0(%rbp)
  
  for (int x = 0; x < threadsize; x++) {
  402f2d:	c7 85 b0 fe ff ff 00 00 00 00 	movl   $0x0,-0x150(%rbp)
  402f37:	eb 5f                	jmp    402f98 <main+0xf08>
    freq_writes += data[x].freq_writes;
  402f39:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f3f:	48 98                	cltq
  402f41:	48 c1 e0 0a          	shl    $0xa,%rax
  402f45:	48 89 c2             	mov    %rax,%rdx
  402f48:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402f4f:	48 01 d0             	add    %rdx,%rax
  402f52:	48 8b 40 50          	mov    0x50(%rax),%rax
  402f56:	48 01 85 30 ff ff ff 	add    %rax,-0xd0(%rbp)
    printf("%ld writes\n", data[x].freq_writes);
  402f5d:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f63:	48 98                	cltq
  402f65:	48 c1 e0 0a          	shl    $0xa,%rax
  402f69:	48 89 c2             	mov    %rax,%rdx
  402f6c:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402f73:	48 01 d0             	add    %rdx,%rax
  402f76:	48 8b 40 50          	mov    0x50(%rax),%rax
  402f7a:	48 89 c6             	mov    %rax,%rsi
  402f7d:	48 8d 05 fe 11 00 00 	lea    0x11fe(%rip),%rax        # 404182 <_IO_stdin_used+0x182>
  402f84:	48 89 c7             	mov    %rax,%rdi
  402f87:	b8 00 00 00 00       	mov    $0x0,%eax
  402f8c:	e8 ef e0 ff ff       	call   401080 <printf@plt>
  for (int x = 0; x < threadsize; x++) {
  402f91:	83 85 b0 fe ff ff 01 	addl   $0x1,-0x150(%rbp)
  402f98:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f9e:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402fa4:	7c 93                	jl     402f39 <main+0xea9>
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  402fa6:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402fac:	48 63 d8             	movslq %eax,%rbx
  402faf:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402fb6:	48 99                	cqto
  402fb8:	48 f7 fb             	idiv   %rbx
  402fbb:	48 89 c6             	mov    %rax,%rsi
  402fbe:	48 8d 05 c9 11 00 00 	lea    0x11c9(%rip),%rax        # 40418e <_IO_stdin_used+0x18e>
  402fc5:	48 89 c7             	mov    %rax,%rdi
  402fc8:	b8 00 00 00 00       	mov    $0x0,%eax
  402fcd:	e8 ae e0 ff ff       	call   401080 <printf@plt>

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  402fd2:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402fd9:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  402fde:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402fe4:	48 63 da             	movslq %edx,%rbx
  402fe7:	48 99                	cqto
  402fe9:	48 f7 fb             	idiv   %rbx
  402fec:	48 89 c6             	mov    %rax,%rsi
  402fef:	48 8d 05 aa 11 00 00 	lea    0x11aa(%rip),%rax        # 4041a0 <_IO_stdin_used+0x1a0>
  402ff6:	48 89 c7             	mov    %rax,%rdi
  402ff9:	b8 00 00 00 00       	mov    $0x0,%eax
  402ffe:	e8 7d e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  403003:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  403009:	48 63 d8             	movslq %eax,%rbx
  40300c:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  403013:	48 99                	cqto
  403015:	48 f7 fb             	idiv   %rbx
  403018:	48 89 c3             	mov    %rax,%rbx
  40301b:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  403020:	48 99                	cqto
  403022:	48 f7 fb             	idiv   %rbx
  403025:	48 89 c6             	mov    %rax,%rsi
  403028:	48 8d 05 89 11 00 00 	lea    0x1189(%rip),%rax        # 4041b8 <_IO_stdin_used+0x1b8>
  40302f:	48 89 c7             	mov    %rax,%rdi
  403032:	b8 00 00 00 00       	mov    $0x0,%eax
  403037:	e8 44 e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes per thread latency: %ld\n", (1000000000/(freq_writes / seconds)) / sends);
  40303c:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  403042:	48 63 d8             	movslq %eax,%rbx
  403045:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  40304c:	48 99                	cqto
  40304e:	48 f7 fb             	idiv   %rbx
  403051:	48 89 c3             	mov    %rax,%rbx
  403054:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  403059:	48 99                	cqto
  40305b:	48 f7 fb             	idiv   %rbx
  40305e:	48 99                	cqto
  403060:	48 f7 7d 88          	idivq  -0x78(%rbp)
  403064:	48 89 c6             	mov    %rax,%rsi
  403067:	48 8d 05 6a 11 00 00 	lea    0x116a(%rip),%rax        # 4041d8 <_IO_stdin_used+0x1d8>
  40306e:	48 89 c7             	mov    %rax,%rdi
  403071:	b8 00 00 00 00       	mov    $0x0,%eax
  403076:	e8 05 e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * sends) / seconds));
  40307b:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  403082:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  403087:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  40308d:	48 63 da             	movslq %edx,%rbx
  403090:	48 99                	cqto
  403092:	48 f7 fb             	idiv   %rbx
  403095:	48 89 c3             	mov    %rax,%rbx
  403098:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40309d:	48 99                	cqto
  40309f:	48 f7 fb             	idiv   %rbx
  4030a2:	48 89 c6             	mov    %rax,%rsi
  4030a5:	48 8d 05 51 11 00 00 	lea    0x1151(%rip),%rax        # 4041fd <_IO_stdin_used+0x1fd>
  4030ac:	48 89 c7             	mov    %rax,%rdi
  4030af:	b8 00 00 00 00       	mov    $0x0,%eax
  4030b4:	e8 c7 df ff ff       	call   401080 <printf@plt>
    printf("%ldns\n", read.tv_nsec - created.tv_nsec);
    printf("%ldns\n", written.tv_nsec - read.tv_nsec);
    
  }
  */
  printf("writer speed\n");
  4030b9:	48 8d 05 57 11 00 00 	lea    0x1157(%rip),%rax        # 404217 <_IO_stdin_used+0x217>
  4030c0:	48 89 c7             	mov    %rax,%rdi
  4030c3:	e8 78 df ff ff       	call   401040 <puts@plt>
  for (int x = 0; x < 1 ;  x++){
  4030c8:	c7 85 b4 fe ff ff 00 00 00 00 	movl   $0x0,-0x14c(%rbp)
  4030d2:	e9 84 02 00 00       	jmp    40335b <main+0x12cb>
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  4030d7:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4030dd:	48 98                	cltq
  4030df:	48 c1 e0 0a          	shl    $0xa,%rax
  4030e3:	48 89 c2             	mov    %rax,%rdx
  4030e6:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4030ed:	48 01 d0             	add    %rdx,%rax
  4030f0:	48 8b 80 f0 00 00 00 	mov    0xf0(%rax),%rax
  4030f7:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4030fd:	48 63 d2             	movslq %edx,%rdx
  403100:	48 89 d1             	mov    %rdx,%rcx
  403103:	48 c1 e1 0a          	shl    $0xa,%rcx
  403107:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  40310e:	48 01 ca             	add    %rcx,%rdx
  403111:	48 8b 92 e0 00 00 00 	mov    0xe0(%rdx),%rdx
  403118:	48 29 d0             	sub    %rdx,%rax
  40311b:	48 89 c6             	mov    %rax,%rsi
  40311e:	48 8d 05 f2 0e 00 00 	lea    0xef2(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  403125:	48 89 c7             	mov    %rax,%rdi
  403128:	b8 00 00 00 00       	mov    $0x0,%eax
  40312d:	e8 4e df ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  403132:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403138:	48 98                	cltq
  40313a:	48 c1 e0 0a          	shl    $0xa,%rax
  40313e:	48 89 c2             	mov    %rax,%rdx
  403141:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403148:	48 01 d0             	add    %rdx,%rax
  40314b:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
  403152:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  403158:	48 63 d2             	movslq %edx,%rdx
  40315b:	48 89 d1             	mov    %rdx,%rcx
  40315e:	48 c1 e1 0a          	shl    $0xa,%rcx
  403162:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403169:	48 01 ca             	add    %rcx,%rdx
  40316c:	48 8b 92 e0 00 00 00 	mov    0xe0(%rdx),%rdx
  403173:	48 29 d0             	sub    %rdx,%rax
  403176:	48 89 c6             	mov    %rax,%rsi
  403179:	48 8d 05 97 0e 00 00 	lea    0xe97(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  403180:	48 89 c7             	mov    %rax,%rdi
  403183:	b8 00 00 00 00       	mov    $0x0,%eax
  403188:	e8 f3 de ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  40318d:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403193:	48 98                	cltq
  403195:	48 c1 e0 0a          	shl    $0xa,%rax
  403199:	48 89 c2             	mov    %rax,%rdx
  40319c:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4031a3:	48 01 d0             	add    %rdx,%rax
  4031a6:	48 8b 80 f0 00 00 00 	mov    0xf0(%rax),%rax
  4031ad:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4031b3:	48 63 d2             	movslq %edx,%rdx
  4031b6:	48 89 d1             	mov    %rdx,%rcx
  4031b9:	48 c1 e1 0a          	shl    $0xa,%rcx
  4031bd:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4031c4:	48 01 ca             	add    %rcx,%rdx
  4031c7:	48 8b 92 00 01 00 00 	mov    0x100(%rdx),%rdx
  4031ce:	48 29 d0             	sub    %rdx,%rax
  4031d1:	48 89 c6             	mov    %rax,%rsi
  4031d4:	48 8d 05 3c 0e 00 00 	lea    0xe3c(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  4031db:	48 89 c7             	mov    %rax,%rdi
  4031de:	b8 00 00 00 00       	mov    $0x0,%eax
  4031e3:	e8 98 de ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4031e8:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4031ee:	48 98                	cltq
  4031f0:	48 c1 e0 0a          	shl    $0xa,%rax
  4031f4:	48 89 c2             	mov    %rax,%rdx
  4031f7:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4031fe:	48 01 d0             	add    %rdx,%rax
  403201:	48 8b 80 20 01 00 00 	mov    0x120(%rax),%rax
  403208:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  40320e:	48 63 d2             	movslq %edx,%rdx
  403211:	48 89 d1             	mov    %rdx,%rcx
  403214:	48 c1 e1 0a          	shl    $0xa,%rcx
  403218:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  40321f:	48 01 ca             	add    %rcx,%rdx
  403222:	48 8b 92 10 01 00 00 	mov    0x110(%rdx),%rdx
  403229:	48 29 d0             	sub    %rdx,%rax
  40322c:	48 89 c6             	mov    %rax,%rsi
  40322f:	48 8d 05 e1 0d 00 00 	lea    0xde1(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  403236:	48 89 c7             	mov    %rax,%rdi
  403239:	b8 00 00 00 00       	mov    $0x0,%eax
  40323e:	e8 3d de ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  403243:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403249:	48 98                	cltq
  40324b:	48 c1 e0 0a          	shl    $0xa,%rax
  40324f:	48 89 c2             	mov    %rax,%rdx
  403252:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403259:	48 01 d0             	add    %rdx,%rax
  40325c:	48 8b 80 10 01 00 00 	mov    0x110(%rax),%rax
  403263:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  403269:	48 63 d2             	movslq %edx,%rdx
  40326c:	48 89 d1             	mov    %rdx,%rcx
  40326f:	48 c1 e1 0a          	shl    $0xa,%rcx
  403273:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  40327a:	48 01 ca             	add    %rcx,%rdx
  40327d:	48 8b 92 20 01 00 00 	mov    0x120(%rdx),%rdx
  403284:	48 29 d0             	sub    %rdx,%rax
  403287:	48 89 c6             	mov    %rax,%rsi
  40328a:	48 8d 05 86 0d 00 00 	lea    0xd86(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  403291:	48 89 c7             	mov    %rax,%rdi
  403294:	b8 00 00 00 00       	mov    $0x0,%eax
  403299:	e8 e2 dd ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  40329e:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4032a4:	48 98                	cltq
  4032a6:	48 c1 e0 0a          	shl    $0xa,%rax
  4032aa:	48 89 c2             	mov    %rax,%rdx
  4032ad:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4032b4:	48 01 d0             	add    %rdx,%rax
  4032b7:	48 8b 80 10 01 00 00 	mov    0x110(%rax),%rax
  4032be:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4032c4:	48 63 d2             	movslq %edx,%rdx
  4032c7:	48 89 d1             	mov    %rdx,%rcx
  4032ca:	48 c1 e1 0a          	shl    $0xa,%rcx
  4032ce:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4032d5:	48 01 ca             	add    %rcx,%rdx
  4032d8:	48 8b 92 00 01 00 00 	mov    0x100(%rdx),%rdx
  4032df:	48 29 d0             	sub    %rdx,%rax
  4032e2:	48 89 c6             	mov    %rax,%rsi
  4032e5:	48 8d 05 2b 0d 00 00 	lea    0xd2b(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  4032ec:	48 89 c7             	mov    %rax,%rdi
  4032ef:	b8 00 00 00 00       	mov    $0x0,%eax
  4032f4:	e8 87 dd ff ff       	call   401080 <printf@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  4032f9:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4032ff:	48 98                	cltq
  403301:	48 c1 e0 0a          	shl    $0xa,%rax
  403305:	48 89 c2             	mov    %rax,%rdx
  403308:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40330f:	48 01 d0             	add    %rdx,%rax
  403312:	48 8b 80 40 01 00 00 	mov    0x140(%rax),%rax
  403319:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  40331f:	48 63 d2             	movslq %edx,%rdx
  403322:	48 89 d1             	mov    %rdx,%rcx
  403325:	48 c1 e1 0a          	shl    $0xa,%rcx
  403329:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403330:	48 01 ca             	add    %rcx,%rdx
  403333:	48 8b 92 30 01 00 00 	mov    0x130(%rdx),%rdx
  40333a:	48 29 d0             	sub    %rdx,%rax
  40333d:	48 89 c6             	mov    %rax,%rsi
  403340:	48 8d 05 dd 0e 00 00 	lea    0xedd(%rip),%rax        # 404224 <_IO_stdin_used+0x224>
  403347:	48 89 c7             	mov    %rax,%rdi
  40334a:	b8 00 00 00 00       	mov    $0x0,%eax
  40334f:	e8 2c dd ff ff       	call   401080 <printf@plt>
  for (int x = 0; x < 1 ;  x++){
  403354:	83 85 b4 fe ff ff 01 	addl   $0x1,-0x14c(%rbp)
  40335b:	83 bd b4 fe ff ff 00 	cmpl   $0x0,-0x14c(%rbp)
  403362:	0f 8e 6f fd ff ff    	jle    4030d7 <main+0x1047>
  } 
  printf("%ld good reads per second\n", goods / seconds);
  403368:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  40336e:	48 63 d8             	movslq %eax,%rbx
  403371:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
  403378:	48 99                	cqto
  40337a:	48 f7 fb             	idiv   %rbx
  40337d:	48 89 c6             	mov    %rax,%rsi
  403380:	48 8d 05 a5 0e 00 00 	lea    0xea5(%rip),%rax        # 40422c <_IO_stdin_used+0x22c>
  403387:	48 89 c7             	mov    %rax,%rdi
  40338a:	b8 00 00 00 00       	mov    $0x0,%eax
  40338f:	e8 ec dc ff ff       	call   401080 <printf@plt>
  printf("%ld good reads per second latency\n", 1000000000 / (goods / seconds));
  403394:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  40339a:	48 63 d8             	movslq %eax,%rbx
  40339d:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
  4033a4:	48 99                	cqto
  4033a6:	48 f7 fb             	idiv   %rbx
  4033a9:	48 89 c3             	mov    %rax,%rbx
  4033ac:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  4033b1:	48 99                	cqto
  4033b3:	48 f7 fb             	idiv   %rbx
  4033b6:	48 89 c6             	mov    %rax,%rsi
  4033b9:	48 8d 05 88 0e 00 00 	lea    0xe88(%rip),%rax        # 404248 <_IO_stdin_used+0x248>
  4033c0:	48 89 c7             	mov    %rax,%rdi
  4033c3:	b8 00 00 00 00       	mov    $0x0,%eax
  4033c8:	e8 b3 dc ff ff       	call   401080 <printf@plt>
     }
   fclose(out_file);
   
 }

  char * filename = calloc(100, sizeof(char));
  4033cd:	be 01 00 00 00       	mov    $0x1,%esi
  4033d2:	bf 64 00 00 00       	mov    $0x64,%edi
  4033d7:	e8 f4 dc ff ff       	call   4010d0 <calloc@plt>
  4033dc:	48 89 45 90          	mov    %rax,-0x70(%rbp)
  char * buf = calloc(1000, sizeof(char));
  4033e0:	be 01 00 00 00       	mov    $0x1,%esi
  4033e5:	bf e8 03 00 00       	mov    $0x3e8,%edi
  4033ea:	e8 e1 dc ff ff       	call   4010d0 <calloc@plt>
  4033ef:	48 89 45 98          	mov    %rax,-0x68(%rbp)
  memset(filename, 0, 100);
  4033f3:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4033f7:	ba 64 00 00 00       	mov    $0x64,%edx
  4033fc:	be 00 00 00 00       	mov    $0x0,%esi
  403401:	48 89 c7             	mov    %rax,%rdi
  403404:	e8 b7 dc ff ff       	call   4010c0 <memset@plt>
  snprintf(filename, 100, "coroutine.struct");
  403409:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40340d:	48 8d 15 57 0e 00 00 	lea    0xe57(%rip),%rdx        # 40426b <_IO_stdin_used+0x26b>
  403414:	be 64 00 00 00       	mov    $0x64,%esi
  403419:	48 89 c7             	mov    %rax,%rdi
  40341c:	b8 00 00 00 00       	mov    $0x0,%eax
  403421:	e8 6a dc ff ff       	call   401090 <snprintf@plt>
  FILE *out_file = fopen(filename, "w");
  403426:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40342a:	48 8d 15 4b 0e 00 00 	lea    0xe4b(%rip),%rdx        # 40427c <_IO_stdin_used+0x27c>
  403431:	48 89 d6             	mov    %rdx,%rsi
  403434:	48 89 c7             	mov    %rax,%rdi
  403437:	e8 b4 dc ff ff       	call   4010f0 <fopen@plt>
  40343c:	48 89 45 a0          	mov    %rax,-0x60(%rbp)

memset(buf, 0, 1000);
  403440:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403444:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403449:	be 00 00 00 00       	mov    $0x0,%esi
  40344e:	48 89 c7             	mov    %rax,%rdi
  403451:	e8 6a dc ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "index %ld\n", offsetof(struct Coroutine, index));
  403456:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40345a:	b9 00 00 00 00       	mov    $0x0,%ecx
  40345f:	48 8d 15 18 0e 00 00 	lea    0xe18(%rip),%rdx        # 40427e <_IO_stdin_used+0x27e>
  403466:	be 64 00 00 00       	mov    $0x64,%esi
  40346b:	48 89 c7             	mov    %rax,%rdi
  40346e:	b8 00 00 00 00       	mov    $0x0,%eax
  403473:	e8 18 dc ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  403478:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  40347c:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403480:	48 89 d6             	mov    %rdx,%rsi
  403483:	48 89 c7             	mov    %rax,%rdi
  403486:	e8 25 dc ff ff       	call   4010b0 <fputs@plt>
  
  memset(buf, 0, 1000);
  40348b:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40348f:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403494:	be 00 00 00 00       	mov    $0x0,%esi
  403499:	48 89 c7             	mov    %rax,%rdi
  40349c:	e8 1f dc ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "rsp %ld\n", offsetof(struct Coroutine, rsp));
  4034a1:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034a5:	b9 08 00 00 00       	mov    $0x8,%ecx
  4034aa:	48 8d 15 d8 0d 00 00 	lea    0xdd8(%rip),%rdx        # 404289 <_IO_stdin_used+0x289>
  4034b1:	be 64 00 00 00       	mov    $0x64,%esi
  4034b6:	48 89 c7             	mov    %rax,%rdi
  4034b9:	b8 00 00 00 00       	mov    $0x0,%eax
  4034be:	e8 cd db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  4034c3:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  4034c7:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034cb:	48 89 d6             	mov    %rdx,%rsi
  4034ce:	48 89 c7             	mov    %rax,%rdi
  4034d1:	e8 da db ff ff       	call   4010b0 <fputs@plt>
  
  memset(buf, 0, 1000);
  4034d6:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034da:	ba e8 03 00 00       	mov    $0x3e8,%edx
  4034df:	be 00 00 00 00       	mov    $0x0,%esi
  4034e4:	48 89 c7             	mov    %rax,%rdi
  4034e7:	e8 d4 db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "eip %ld\n", offsetof(struct Coroutine, eip));
  4034ec:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034f0:	b9 10 00 00 00       	mov    $0x10,%ecx
  4034f5:	48 8d 15 96 0d 00 00 	lea    0xd96(%rip),%rdx        # 404292 <_IO_stdin_used+0x292>
  4034fc:	be 64 00 00 00       	mov    $0x64,%esi
  403501:	48 89 c7             	mov    %rax,%rdi
  403504:	b8 00 00 00 00       	mov    $0x0,%eax
  403509:	e8 82 db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  40350e:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  403512:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403516:	48 89 d6             	mov    %rdx,%rsi
  403519:	48 89 c7             	mov    %rax,%rdi
  40351c:	e8 8f db ff ff       	call   4010b0 <fputs@plt>


  memset(buf, 0, 1000);
  403521:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403525:	ba e8 03 00 00       	mov    $0x3e8,%edx
  40352a:	be 00 00 00 00       	mov    $0x0,%esi
  40352f:	48 89 c7             	mov    %rax,%rdi
  403532:	e8 89 db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "data %ld\n", offsetof(struct Coroutine, data));
  403537:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40353b:	b9 18 00 00 00       	mov    $0x18,%ecx
  403540:	48 8d 15 54 0d 00 00 	lea    0xd54(%rip),%rdx        # 40429b <_IO_stdin_used+0x29b>
  403547:	be 64 00 00 00       	mov    $0x64,%esi
  40354c:	48 89 c7             	mov    %rax,%rdi
  40354f:	b8 00 00 00 00       	mov    $0x0,%eax
  403554:	e8 37 db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  403559:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  40355d:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403561:	48 89 d6             	mov    %rdx,%rsi
  403564:	48 89 c7             	mov    %rax,%rdi
  403567:	e8 44 db ff ff       	call   4010b0 <fputs@plt>

  memset(buf, 0, 1000);
  40356c:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403570:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403575:	be 00 00 00 00       	mov    $0x0,%esi
  40357a:	48 89 c7             	mov    %rax,%rdi
  40357d:	e8 3e db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "corourinedata.running %ld\n", offsetof(struct CoroutineData, running));
  403582:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403586:	b9 00 00 00 00       	mov    $0x0,%ecx
  40358b:	48 8d 15 13 0d 00 00 	lea    0xd13(%rip),%rdx        # 4042a5 <_IO_stdin_used+0x2a5>
  403592:	be 64 00 00 00       	mov    $0x64,%esi
  403597:	48 89 c7             	mov    %rax,%rdi
  40359a:	b8 00 00 00 00       	mov    $0x0,%eax
  40359f:	e8 ec da ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  4035a4:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  4035a8:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4035ac:	48 89 d6             	mov    %rdx,%rsi
  4035af:	48 89 c7             	mov    %rax,%rdi
  4035b2:	e8 f9 da ff ff       	call   4010b0 <fputs@plt>

  memset(buf, 0, 1000);
  4035b7:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4035bb:	ba e8 03 00 00       	mov    $0x3e8,%edx
  4035c0:	be 00 00 00 00       	mov    $0x0,%esi
  4035c5:	48 89 c7             	mov    %rax,%rdi
  4035c8:	e8 f3 da ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "size coroutine %ld\n", sizeof(struct Coroutine));
  4035cd:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4035d1:	b9 20 00 00 00       	mov    $0x20,%ecx
  4035d6:	48 8d 15 e3 0c 00 00 	lea    0xce3(%rip),%rdx        # 4042c0 <_IO_stdin_used+0x2c0>
  4035dd:	be 64 00 00 00       	mov    $0x64,%esi
  4035e2:	48 89 c7             	mov    %rax,%rdi
  4035e5:	b8 00 00 00 00       	mov    $0x0,%eax
  4035ea:	e8 a1 da ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  4035ef:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  4035f3:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4035f7:	48 89 d6             	mov    %rdx,%rsi
  4035fa:	48 89 c7             	mov    %rax,%rdi
  4035fd:	e8 ae da ff ff       	call   4010b0 <fputs@plt>
  
  fclose(out_file);
  403602:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  403606:	48 89 c7             	mov    %rax,%rdi
  403609:	e8 52 da ff ff       	call   401060 <fclose@plt>
  40360e:	b8 00 00 00 00       	mov    $0x0,%eax
  403613:	48 8b 55 e8          	mov    -0x18(%rbp),%rdx
  403617:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  403620:	74 05                	je     403627 <main+0x1597>
  403622:	e8 49 da ff ff       	call   401070 <__stack_chk_fail@plt>
  403627:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
  40362b:	c9                   	leave
  40362c:	c3                   	ret
  40362d:	0f 1f 00             	nopl   (%rax)

0000000000403630 <.MSG>:
  403630:	43                   	rex.XB
  403631:	4f 20 43 6f          	rex.WRXB and %r8b,0x6f(%r11)
  403635:	72 6f                	jb     4036a6 <switch_to+0xe>
  403637:	75 74                	jne    4036ad <switch_to+0x15>
  403639:	69 6e 65 53 74 72 75 	imul   $0x75727453,0x65(%rsi),%ebp
  403640:	63 74 20 25          	movsxd 0x25(%rax,%riz,1),%esi
  403644:	78 0a                	js     403650 <.EIP+0x9>
	...

0000000000403647 <.EIP>:
  403647:	43                   	rex.XB
  403648:	4f 20 45 49          	rex.WRXB and %r8b,0x49(%r13)
  40364c:	50                   	push   %rax
  40364d:	2e                   	cs
  40364e:	2e                   	cs
  40364f:	2e                   	cs
  403650:	20                   	.byte 0x20
  403651:	25                   	.byte 0x25
  403652:	78 0a                	js     40365e <.CODATA+0x9>
	...

0000000000403655 <.CODATA>:
  403655:	43                   	rex.XB
  403656:	4f 20 63 6f          	rex.WRXB and %r12b,0x6f(%r11)
  40365a:	64 61                	fs (bad)
  40365c:	74 61                	je     4036bf <switch_to+0x27>
  40365e:	2e                   	cs
  40365f:	2e                   	cs
  403660:	2e                   	cs
  403661:	20                   	.byte 0x20
  403662:	25                   	.byte 0x25
  403663:	78 0a                	js     40366f <.INDEX+0x9>
	...

0000000000403666 <.INDEX>:
  403666:	43 6f                	rex.XB outsl %ds:(%rsi),(%dx)
  403668:	72 6f                	jb     4036d9 <switch_to+0x41>
  40366a:	75 74                	jne    4036e0 <switch_to+0x48>
  40366c:	69 6e 65 20 69 6e 64 	imul   $0x646e6920,0x65(%rsi),%ebp
  403673:	65 78 2e             	gs js  4036a4 <switch_to+0xc>
  403676:	2e                   	cs
  403677:	2e                   	cs
  403678:	20                   	.byte 0x20
  403679:	25                   	.byte 0x25
  40367a:	64 0a 00             	or     %fs:(%rax),%al

000000000040367d <.RET>:
  40367d:	52                   	push   %rdx
  40367e:	65 74 75             	gs je  4036f6 <switch_to+0x5e>
  403681:	72 6e                	jb     4036f1 <switch_to+0x59>
  403683:	2e                   	cs
  403684:	2e                   	cs
  403685:	2e                   	cs
  403686:	20                   	.byte 0x20
  403687:	25                   	.byte 0x25
  403688:	64 0a 00             	or     %fs:(%rax),%al

000000000040368b <.STACK>:
  40368b:	53                   	push   %rbx
  40368c:	74 61                	je     4036ef <switch_to+0x57>
  40368e:	63 6b 2e             	movsxd 0x2e(%rbx),%ebp
  403691:	2e                   	cs
  403692:	2e                   	cs
  403693:	20                   	.byte 0x20
  403694:	25                   	.byte 0x25
  403695:	70 0a                	jo     4036a1 <switch_to+0x9>
	...

0000000000403698 <switch_to>:
	.text
	# switch_to(struct Coroutine * coroutines, int index, struct Scheduler * scheduler)
	# rdi, %rsi, %rdx, %rcx, %r8 and %r9
switch_to:
# popq %r11
pushq %rbp
  403698:	55                   	push   %rbp

movq %rsp, %rbp
  403699:	48 89 e5             	mov    %rsp,%rbp
subq $1024, %rsp
  40369c:	48 81 ec 00 04 00 00 	sub    $0x400,%rsp



movq %rdi, -56(%rbp) # coroutine table
  4036a3:	48 89 7d c8          	mov    %rdi,-0x38(%rbp)
movq %rsi, -8(%rbp) # index
  4036a7:	48 89 75 f8          	mov    %rsi,-0x8(%rbp)
movq %rdx, -16(%rbp) # scheduler
  4036ab:	48 89 55 f0          	mov    %rdx,-0x10(%rbp)

movq %rsi, %rax
  4036af:	48 89 f0             	mov    %rsi,%rax
imul $32, %rax
  4036b2:	48 6b c0 20          	imul   $0x20,%rax,%rax
addq %rdi, %rax
  4036b6:	48 01 f8             	add    %rdi,%rax
mov %rax, %r11
  4036b9:	49 89 c3             	mov    %rax,%r11

mov %r11, %rax
  4036bc:	4c 89 d8             	mov    %r11,%rax
movq %rax, %r9
  4036bf:	49 89 c1             	mov    %rax,%r9
movq %r9, -24(%rbp) # coroutine object
  4036c2:	4c 89 4d e8          	mov    %r9,-0x18(%rbp)

movq %r11, %rax
  4036c6:	4c 89 d8             	mov    %r11,%rax
leaq 8(%rax), %rax
  4036c9:	48 8d 40 08          	lea    0x8(%rax),%rax
movq %rax, %r9
  4036cd:	49 89 c1             	mov    %rax,%r9
movq %r9, -48(%rbp) # rsp
  4036d0:	4c 89 4d d0          	mov    %r9,-0x30(%rbp)

movq %r11, %rax
  4036d4:	4c 89 d8             	mov    %r11,%rax
leaq 16(%rax), %rax
  4036d7:	48 8d 40 10          	lea    0x10(%rax),%rax
movq (%rax), %r9
  4036db:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -32(%rbp) # coroutine function
  4036de:	4c 89 4d e0          	mov    %r9,-0x20(%rbp)

movq %r11, %rax
  4036e2:	4c 89 d8             	mov    %r11,%rax
leaq 8(%rax), %rax
  4036e5:	48 8d 40 08          	lea    0x8(%rax),%rax
movq (%rax), %r9
  4036e9:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -64(%rbp) # coroutine stack
  4036ec:	4c 89 4d c0          	mov    %r9,-0x40(%rbp)

movq %r11, %rax
  4036f0:	4c 89 d8             	mov    %r11,%rax
leaq 24(%rax), %rax # load from coroutine object data object
  4036f3:	48 8d 40 18          	lea    0x18(%rax),%rax
movq (%rax), %r9
  4036f7:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -40(%rbp) # coroutine data object
  4036fa:	4c 89 4d d8          	mov    %r9,-0x28(%rbp)
movq (%rax), %rcx
  4036fe:	48 8b 08             	mov    (%rax),%rcx

movq -24(%rbp), %r11
  403701:	4c 8b 5d e8          	mov    -0x18(%rbp),%r11
#

leaq .INDEX(%rip), %rdi
  403705:	48 8d 3d 5a ff ff ff 	lea    -0xa6(%rip),%rdi        # 403666 <.INDEX>
#call printf@plt
mov $0, %eax
  40370c:	b8 00 00 00 00       	mov    $0x0,%eax

#pushq %r11
leaq .MSG(%rip), %rdi
  403711:	48 8d 3d 18 ff ff ff 	lea    -0xe8(%rip),%rdi        # 403630 <.MSG>
movq %r11, %rsi
  403718:	4c 89 de             	mov    %r11,%rsi
# call printf@plt
mov $0, %eax
  40371b:	b8 00 00 00 00       	mov    $0x0,%eax

#popq %r11

#pushq %r9
movq -32(%rbp), %r9
  403720:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9

leaq .EIP(%rip), %rdi
  403724:	48 8d 3d 1c ff ff ff 	lea    -0xe4(%rip),%rdi        # 403647 <.EIP>
movq %r9, %rsi
  40372b:	4c 89 ce             	mov    %r9,%rsi
#call printf@plt
mov $0, %eax
  40372e:	b8 00 00 00 00       	mov    $0x0,%eax
#popq %r9
# coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data

#pushq %r9
leaq .CODATA(%rip), %rdi
  403733:	48 8d 3d 1b ff ff ff 	lea    -0xe5(%rip),%rdi        # 403655 <.CODATA>
movq -40(%rbp), %rsi
  40373a:	48 8b 75 d8          	mov    -0x28(%rbp),%rsi
#call printf@plt
mov $0, %eax
  40373e:	b8 00 00 00 00       	mov    $0x0,%eax
#pushq %r11
#movq %r11, %rsp

#mov %rbp, %rsp

movq -16(%rbp), %rdi
  403743:	48 8b 7d f0          	mov    -0x10(%rbp),%rdi
movq -24(%rbp), %rsi
  403747:	48 8b 75 e8          	mov    -0x18(%rbp),%rsi
movq -40(%rbp), %rdx
  40374b:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
#mov %rsp, %rbp
# pushq %r11



leaq .STACK(%rip), %rdi
  40374f:	48 8d 3d 35 ff ff ff 	lea    -0xcb(%rip),%rdi        # 40368b <.STACK>
movq -64(%rbp), %rsi
  403756:	48 8b 75 c0          	mov    -0x40(%rbp),%rsi
call printf@plt
  40375a:	e8 21 d9 ff ff       	call   401080 <printf@plt>
mov $0, %eax
  40375f:	b8 00 00 00 00       	mov    $0x0,%eax

movq -32(%rbp), %r9
  403764:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9
leaq after(%rip), %r11
  403768:	4c 8d 1d 0b 00 00 00 	lea    0xb(%rip),%r11        # 40377a <after>

movq -64(%rbp), %rsp # set stack to coroutine
  40376f:	48 8b 65 c0          	mov    -0x40(%rbp),%rsp
sub $8, %rsp
  403773:	48 83 ec 08          	sub    $0x8,%rsp
#movq %r11, (%rsp) # set stack return address


jmp *%r9
  403777:	41 ff e1             	jmp    *%r9

000000000040377a <after>:
after: 
# pushq %rbp

#movq %rsp, %rbp

leaq .RET(%rip), %rdi
  40377a:	48 8d 3d fc fe ff ff 	lea    -0x104(%rip),%rdi        # 40367d <.RET>
movq %r9, %rsi
  403781:	4c 89 ce             	mov    %r9,%rsi
call printf@plt
  403784:	e8 f7 d8 ff ff       	call   401080 <printf@plt>
mov $0, %eax
  403789:	b8 00 00 00 00       	mov    $0x0,%eax


#pop %rbp
add $1024, %rsp
  40378e:	48 81 c4 00 04 00 00 	add    $0x400,%rsp
#movq %rsp, %rbp
popq %rbp
  403795:	5d                   	pop    %rbp
  403796:	c3                   	ret

Disassembly of section .fini:

0000000000403798 <_fini>:
  403798:	f3 0f 1e fa          	endbr64
  40379c:	48 83 ec 08          	sub    $0x8,%rsp
  4037a0:	48 83 c4 08          	add    $0x8,%rsp
  4037a4:	c3                   	ret
