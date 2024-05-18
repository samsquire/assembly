
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
  401148:	48 c7 c7 6c 20 40 00 	mov    $0x40206c,%rdi
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
   //printf("%ld\n", coroutine->eip); 
  asm("lea 0(%%rip), %%r11\n"
  40125d:	4c 8d 1d 00 00 00 00 	lea    0x0(%rip),%r11        # 401264 <coroutine_func+0x47>
  401264:	4c 89 da             	mov    %r11,%rdx
  401267:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  40126b:	48 89 50 10          	mov    %rdx,0x10(%rax)
      "movq %%r11, %0" : "=rm" (coroutine->eip) ::"r11");
    
    // yield(1, scheduler, coroutine) 
  int rsp = scheduler->rsp;
  40126f:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401273:	48 8b 00             	mov    (%rax),%rax
  401276:	89 45 e4             	mov    %eax,-0x1c(%rbp)
  asm("movq %0, %%rsp" ::"rm"(scheduler->rsp));  
  401279:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  40127d:	48 8b 00             	mov    (%rax),%rax
  401280:	48 89 c4             	mov    %rax,%rsp
       
 // }
  //printf("loop finished\n");
  return 0;      
  401283:	b8 00 00 00 00       	mov    $0x0,%eax
}
  401288:	c9                   	leave
  401289:	c3                   	ret

000000000040128a <pollthreads>:
// thread 2
if tasks.taskindex > threads[0].workindex:
  value = 2
*/

int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  40128a:	55                   	push   %rbp
  40128b:	48 89 e5             	mov    %rsp,%rbp
  40128e:	48 89 7d d8          	mov    %rdi,-0x28(%rbp)
  401292:	48 89 75 d0          	mov    %rsi,-0x30(%rbp)
  401296:	48 89 55 c8          	mov    %rdx,-0x38(%rbp)
  40129a:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
  40129e:	4c 89 45 b8          	mov    %r8,-0x48(%rbp)
  long WM = WRITE_MASK;
  4012a2:	48 c7 45 f0 04 00 00 00 	movq   $0x4,-0x10(%rbp)
  long RM = READ_MASK;
  4012aa:	48 c7 45 f8 08 00 00 00 	movq   $0x8,-0x8(%rbp)
  for (int x = 1; x < data->threadsize ; x++) {
  4012b2:	c7 45 e8 01 00 00 00 	movl   $0x1,-0x18(%rbp)
  4012b9:	e9 9b 00 00 00       	jmp    401359 <pollthreads+0xcf>
  // printf("thread %d %ld\n", x, data->threads[x].ready);
    int mask = data->threads[1].readies[x];
  4012be:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4012c2:	48 8b 40 30          	mov    0x30(%rax),%rax
  4012c6:	48 05 00 04 00 00    	add    $0x400,%rax
  4012cc:	48 8b 50 20          	mov    0x20(%rax),%rdx
  4012d0:	8b 45 e8             	mov    -0x18(%rbp),%eax
  4012d3:	48 98                	cltq
  4012d5:	48 c1 e0 02          	shl    $0x2,%rax
  4012d9:	48 01 d0             	add    %rdx,%rax
  4012dc:	8b 00                	mov    (%rax),%eax
  4012de:	89 45 ec             	mov    %eax,-0x14(%rbp)
        //printf("pollpread? %ld %ld\n", mask, (mask & PREP_READ_MASK));
       // printf("pplreadmask? %ld %ld\n", mask, (mask & READ_MASK));
      //  printf("pollwritemask ? %ld %ld\n", mask, (mask & WRITE_MASK));
       // data->threads[x].newmask = 0;
        
        if ((mask & WM) == WM || mask == 0) {
  4012e1:	8b 45 ec             	mov    -0x14(%rbp),%eax
  4012e4:	48 98                	cltq
  4012e6:	48 23 45 f0          	and    -0x10(%rbp),%rax
  4012ea:	48 39 45 f0          	cmp    %rax,-0x10(%rbp)
  4012ee:	74 06                	je     4012f6 <pollthreads+0x6c>
  4012f0:	83 7d ec 00          	cmpl   $0x0,-0x14(%rbp)
  4012f4:	75 25                	jne    40131b <pollthreads+0x91>
         //printf("found a writer\n");
          readywriters[(*writers)++] = x;
  4012f6:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  4012fa:	8b 00                	mov    (%rax),%eax
  4012fc:	8d 48 01             	lea    0x1(%rax),%ecx
  4012ff:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
  401303:	89 0a                	mov    %ecx,(%rdx)
  401305:	48 98                	cltq
  401307:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  40130f:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
  401313:	48 01 c2             	add    %rax,%rdx
  401316:	8b 45 e8             	mov    -0x18(%rbp),%eax
  401319:	89 02                	mov    %eax,(%rdx)
        }
    if ((mask & RM) == RM || mask == 0) {
  40131b:	8b 45 ec             	mov    -0x14(%rbp),%eax
  40131e:	48 98                	cltq
  401320:	48 23 45 f8          	and    -0x8(%rbp),%rax
  401324:	48 39 45 f8          	cmp    %rax,-0x8(%rbp)
  401328:	74 06                	je     401330 <pollthreads+0xa6>
  40132a:	83 7d ec 00          	cmpl   $0x0,-0x14(%rbp)
  40132e:	75 25                	jne    401355 <pollthreads+0xcb>
      readyreaders[(*readers)++] = x;
  401330:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
  401334:	8b 00                	mov    (%rax),%eax
  401336:	8d 48 01             	lea    0x1(%rax),%ecx
  401339:	48 8b 55 c0          	mov    -0x40(%rbp),%rdx
  40133d:	89 0a                	mov    %ecx,(%rdx)
  40133f:	48 98                	cltq
  401341:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401349:	48 8b 45 d0          	mov    -0x30(%rbp),%rax
  40134d:	48 01 c2             	add    %rax,%rdx
  401350:	8b 45 e8             	mov    -0x18(%rbp),%eax
  401353:	89 02                	mov    %eax,(%rdx)
  for (int x = 1; x < data->threadsize ; x++) {
  401355:	83 45 e8 01          	addl   $0x1,-0x18(%rbp)
  401359:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  40135d:	8b 40 68             	mov    0x68(%rax),%eax
  401360:	39 45 e8             	cmp    %eax,-0x18(%rbp)
  401363:	0f 8c 55 ff ff ff    	jl     4012be <pollthreads+0x34>
    // printf("found a reader\n");
    }
      }
  // printf("%d readers %d writers\n", *readers, *writers);
      
  return 0;
  401369:	b8 00 00 00 00       	mov    $0x0,%eax
}
  40136e:	5d                   	pop    %rbp
  40136f:	c3                   	ret

0000000000401370 <findavailable>:


int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401370:	55                   	push   %rbp
  401371:	48 89 e5             	mov    %rsp,%rbp
  401374:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  401378:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
  40137c:	48 89 55 d8          	mov    %rdx,-0x28(%rbp)
  401380:	48 89 4d d0          	mov    %rcx,-0x30(%rbp)
  401384:	4c 89 45 c8          	mov    %r8,-0x38(%rbp)
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401388:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
  40138f:	eb 64                	jmp    4013f5 <findavailable+0x85>
        
        if (data->freelist[x].available == FREE ) {
  401391:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401395:	48 8b 90 a0 00 00 00 	mov    0xa0(%rax),%rdx
  40139c:	8b 45 fc             	mov    -0x4(%rbp),%eax
  40139f:	48 98                	cltq
  4013a1:	48 c1 e0 05          	shl    $0x5,%rax
  4013a5:	48 01 d0             	add    %rdx,%rax
  4013a8:	8b 40 10             	mov    0x10(%rax),%eax
  4013ab:	83 f8 01             	cmp    $0x1,%eax
  4013ae:	75 41                	jne    4013f1 <findavailable+0x81>
          //printf("%d\n", *availableidx);
         available[*availableidx] = x;
  4013b0:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013b4:	8b 00                	mov    (%rax),%eax
  4013b6:	48 98                	cltq
  4013b8:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4013c0:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  4013c4:	48 01 c2             	add    %rax,%rdx
  4013c7:	8b 45 fc             	mov    -0x4(%rbp),%eax
  4013ca:	48 98                	cltq
  4013cc:	48 89 02             	mov    %rax,(%rdx)
         (*availableidx)++;
  4013cf:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013d3:	8b 00                	mov    (%rax),%eax
  4013d5:	8d 50 01             	lea    0x1(%rax),%edx
  4013d8:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013dc:	89 10                	mov    %edx,(%rax)
         if ((*availableidx) == data->threadsize * 2) {
  4013de:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013e2:	8b 10                	mov    (%rax),%edx
  4013e4:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4013e8:	8b 40 68             	mov    0x68(%rax),%eax
  4013eb:	01 c0                	add    %eax,%eax
  4013ed:	39 c2                	cmp    %eax,%edx
  4013ef:	74 20                	je     401411 <findavailable+0xa1>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4013f1:	83 45 fc 01          	addl   $0x1,-0x4(%rbp)
  4013f5:	8b 45 fc             	mov    -0x4(%rbp),%eax
  4013f8:	48 63 d0             	movslq %eax,%rdx
  4013fb:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4013ff:	48 8b 80 b8 00 00 00 	mov    0xb8(%rax),%rax
  401406:	48 83 c0 01          	add    $0x1,%rax
  40140a:	48 39 c2             	cmp    %rax,%rdx
  40140d:	7c 82                	jl     401391 <findavailable+0x21>
  40140f:	eb 01                	jmp    401412 <findavailable+0xa2>
           break;
  401411:	90                   	nop
         }

         // printf("%d chunk is free\n", x);
        }
      }
      if (*availableidx == 0) {
  401412:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401416:	8b 00                	mov    (%rax),%eax
  401418:	85 c0                	test   %eax,%eax
  40141a:	75 07                	jne    401423 <findavailable+0xb3>
       //printf("no chunks avail\n");
        
        return 1;
  40141c:	b8 01 00 00 00       	mov    $0x1,%eax
  401421:	eb 05                	jmp    401428 <findavailable+0xb8>
      }
  return 0;
  401423:	b8 00 00 00 00       	mov    $0x0,%eax
}
  401428:	5d                   	pop    %rbp
  401429:	c3                   	ret

000000000040142a <singlewriter3>:

int singlewriter3(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40142a:	55                   	push   %rbp
  40142b:	48 89 e5             	mov    %rsp,%rbp
  40142e:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  401432:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
  401436:	48 89 55 d8          	mov    %rdx,-0x28(%rbp)
  40143a:	48 89 4d d0          	mov    %rcx,-0x30(%rbp)
  int completed = 0;
  40143e:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
   */



  //printf("%d %d\n", data->writecursor, data->writecursor % (data->threadsize - 1));
  if (data->writecursor != 0 && (data->writecursor % (data->threadsize - 1)) == 0) {
  401445:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401449:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  40144f:	85 c0                	test   %eax,%eax
    //printf("writeepoch\n");
  } else {

  }

}
  401451:	90                   	nop
  401452:	5d                   	pop    %rbp
  401453:	c3                   	ret

0000000000401454 <singlewriter2>:

int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401454:	55                   	push   %rbp
  401455:	48 89 e5             	mov    %rsp,%rbp
  401458:	48 83 ec 40          	sub    $0x40,%rsp
  40145c:	48 89 7d d8          	mov    %rdi,-0x28(%rbp)
  401460:	48 89 75 d0          	mov    %rsi,-0x30(%rbp)
  401464:	48 89 55 c8          	mov    %rdx,-0x38(%rbp)
  401468:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
  int completed = 0;
  40146c:	c7 45 ec 00 00 00 00 	movl   $0x0,-0x14(%rbp)
   }
   */


//if ((__atomic_load_n(&data->readcursor, __ATOMIC_SEQ_CST) % data->threadsize) == 0) {
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401473:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401477:	8b 80 00 02 00 00    	mov    0x200(%rax),%eax
  40147d:	85 c0                	test   %eax,%eax
  40147f:	0f 84 c7 00 00 00    	je     40154c <singlewriter2+0xf8>
  401485:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401489:	8b 80 00 02 00 00    	mov    0x200(%rax),%eax
  40148f:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  401493:	8b 52 68             	mov    0x68(%rdx),%edx
  401496:	8d 4a ff             	lea    -0x1(%rdx),%ecx
  401499:	99                   	cltd
  40149a:	f7 f9                	idiv   %ecx
  40149c:	89 d0                	mov    %edx,%eax
  40149e:	85 c0                	test   %eax,%eax
  4014a0:	0f 85 a6 00 00 00    	jne    40154c <singlewriter2+0xf8>
   // data->readcursor = 0;
    //printf("readepoch\n");
    
  
        // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
        struct Data * thread = &data->threads[data->threadindex];
  4014a6:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014aa:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4014ae:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014b2:	8b 40 64             	mov    0x64(%rax),%eax
  4014b5:	48 98                	cltq
  4014b7:	48 c1 e0 0a          	shl    $0xa,%rax
  4014bb:	48 01 d0             	add    %rdx,%rax
  4014be:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4014c2:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4014c6:	48 8b 88 18 03 00 00 	mov    0x318(%rax),%rcx
  4014cd:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4014d1:	8b 80 24 03 00 00    	mov    0x324(%rax),%eax
  4014d7:	48 63 d0             	movslq %eax,%rdx
  4014da:	48 89 d0             	mov    %rdx,%rax
  4014dd:	48 01 c0             	add    %rax,%rax
  4014e0:	48 01 d0             	add    %rdx,%rax
  4014e3:	48 c1 e0 04          	shl    $0x4,%rax
  4014e7:	48 01 c8             	add    %rcx,%rax
  4014ea:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  4014ee:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  4014f2:	48 83 c0 08          	add    $0x8,%rax
  4014f6:	48 89 c6             	mov    %rax,%rsi
  4014f9:	bf 04 00 00 00       	mov    $0x4,%edi
  4014fe:	e8 4d fb ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401503:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401507:	8b 80 24 03 00 00    	mov    0x324(%rax),%eax
  40150d:	8d 50 01             	lea    0x1(%rax),%edx
  401510:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401514:	8b 88 20 03 00 00    	mov    0x320(%rax),%ecx
  40151a:	89 d0                	mov    %edx,%eax
  40151c:	99                   	cltd
  40151d:	f7 f9                	idiv   %ecx
  40151f:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401523:	89 90 24 03 00 00    	mov    %edx,0x324(%rax)
        epoch->kind = NEW_EPOCH;
  401529:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  40152d:	c7 40 20 01 00 00 00 	movl   $0x1,0x20(%rax)
        epoch->thread = data->threadindex;
  401534:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401538:	8b 50 64             	mov    0x64(%rax),%edx
  40153b:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  40153f:	89 10                	mov    %edx,(%rax)
        epoch->set = 1;
  401541:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401545:	c7 40 24 01 00 00 00 	movl   $0x1,0x24(%rax)
  } else {
    
  }

  
}
  40154c:	90                   	nop
  40154d:	c9                   	leave
  40154e:	c3                   	ret

000000000040154f <singlewriter>:



*/

int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40154f:	55                   	push   %rbp
  401550:	48 89 e5             	mov    %rsp,%rbp
  401553:	48 83 ec 70          	sub    $0x70,%rsp
  401557:	48 89 7d a8          	mov    %rdi,-0x58(%rbp)
  40155b:	48 89 75 a0          	mov    %rsi,-0x60(%rbp)
  40155f:	48 89 55 98          	mov    %rdx,-0x68(%rbp)
  401563:	48 89 4d 90          	mov    %rcx,-0x70(%rbp)
  401567:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401570:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  401574:	31 c0                	xor    %eax,%eax
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401576:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40157a:	48 8b 40 30          	mov    0x30(%rax),%rax
  40157e:	8b 80 0c 02 00 00    	mov    0x20c(%rax),%eax
  401584:	8d 50 01             	lea    0x1(%rax),%edx
  401587:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40158b:	8b 70 68             	mov    0x68(%rax),%esi
  40158e:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401592:	48 8b 48 30          	mov    0x30(%rax),%rcx
  401596:	89 d0                	mov    %edx,%eax
  401598:	99                   	cltd
  401599:	f7 fe                	idiv   %esi
  40159b:	89 d0                	mov    %edx,%eax
  40159d:	89 81 0c 02 00 00    	mov    %eax,0x20c(%rcx)
  int readers = 0;
  4015a3:	c7 45 b0 00 00 00 00 	movl   $0x0,-0x50(%rbp)
  int writers = 0;
  4015aa:	c7 45 b4 00 00 00 00 	movl   $0x0,-0x4c(%rbp)
  int availableidx = 0;
  4015b1:	c7 45 b8 00 00 00 00 	movl   $0x0,-0x48(%rbp)
    readywriters[x] = x;
  }
  */
  //clock_gettime(CLOCK_MONOTONIC_RAW, &data->wstart);
  
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  4015b8:	48 8b 7d 90          	mov    -0x70(%rbp),%rdi
  4015bc:	48 8b 4d 98          	mov    -0x68(%rbp),%rcx
  4015c0:	48 8d 55 b8          	lea    -0x48(%rbp),%rdx
  4015c4:	48 8b 75 a0          	mov    -0x60(%rbp),%rsi
  4015c8:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015cc:	49 89 f8             	mov    %rdi,%r8
  4015cf:	48 89 c7             	mov    %rax,%rdi
  4015d2:	e8 99 fd ff ff       	call   401370 <findavailable>
  4015d7:	89 45 cc             	mov    %eax,-0x34(%rbp)

//clock_gettime(CLOCK_MONOTONIC_RAW, &data->wavail);
  
  if (fill == 1) {
  4015da:	83 7d cc 01          	cmpl   $0x1,-0x34(%rbp)
  4015de:	75 0a                	jne    4015ea <singlewriter+0x9b>
    return 1;
  4015e0:	b8 01 00 00 00       	mov    $0x1,%eax
  4015e5:	e9 f9 02 00 00       	jmp    4018e3 <singlewriter+0x394>
  }
      
   //printf("buffers available %d\n", availableidx);
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  4015ea:	48 8d 7d b4          	lea    -0x4c(%rbp),%rdi
  4015ee:	48 8d 4d b0          	lea    -0x50(%rbp),%rcx
  4015f2:	48 8b 55 90          	mov    -0x70(%rbp),%rdx
  4015f6:	48 8b 75 98          	mov    -0x68(%rbp),%rsi
  4015fa:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015fe:	49 89 f8             	mov    %rdi,%r8
  401601:	48 89 c7             	mov    %rax,%rdi
  401604:	e8 81 fc ff ff       	call   40128a <pollthreads>
      
  //clock_gettime(CLOCK_MONOTONIC_RAW, &data->wpoll);
      
      int assignedchunk = 0;
  401609:	c7 45 bc 00 00 00 00 	movl   $0x0,-0x44(%rbp)
      
        for (int x = 0; x < readers ; x++) {
  401610:	c7 45 c0 00 00 00 00 	movl   $0x0,-0x40(%rbp)
  401617:	e9 10 01 00 00       	jmp    40172c <singlewriter+0x1dd>
          if (assignedchunk == availableidx) {
  40161c:	8b 45 b8             	mov    -0x48(%rbp),%eax
  40161f:	39 45 bc             	cmp    %eax,-0x44(%rbp)
  401622:	0f 84 12 01 00 00    	je     40173a <singlewriter+0x1eb>
           // printf("not enough space readers\n");
                  break;
          }
          int thread = readyreaders[x];
  401628:	8b 45 c0             	mov    -0x40(%rbp),%eax
  40162b:	48 98                	cltq
  40162d:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401635:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  401639:	48 01 d0             	add    %rdx,%rax
  40163c:	8b 00                	mov    (%rax),%eax
  40163e:	89 45 d0             	mov    %eax,-0x30(%rbp)
          //printf("%d %p\n", thread, &data->freelist[available[assignedchunk]]);
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401641:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401645:	48 8b 88 a0 00 00 00 	mov    0xa0(%rax),%rcx
  40164c:	8b 45 bc             	mov    -0x44(%rbp),%eax
  40164f:	8d 50 01             	lea    0x1(%rax),%edx
  401652:	89 55 bc             	mov    %edx,-0x44(%rbp)
  401655:	48 98                	cltq
  401657:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  40165f:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  401663:	48 01 d0             	add    %rdx,%rax
  401666:	48 8b 00             	mov    (%rax),%rax
  401669:	48 c1 e0 05          	shl    $0x5,%rax
  40166d:	48 01 c8             	add    %rcx,%rax
  401670:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
          chunk->available = READING;
  401674:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401678:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
          //printf("assign %p\n", chunk);


          data->threads[thread].reading = chunk;
  40167f:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401683:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401687:	8b 45 d0             	mov    -0x30(%rbp),%eax
  40168a:	48 98                	cltq
  40168c:	48 c1 e0 0a          	shl    $0xa,%rax
  401690:	48 01 c2             	add    %rax,%rdx
  401693:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401697:	48 89 82 a8 00 00 00 	mov    %rax,0xa8(%rdx)
          
          chunk->owner = thread;
  40169e:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016a2:	8b 55 d0             	mov    -0x30(%rbp),%edx
  4016a5:	89 50 14             	mov    %edx,0x14(%rax)
          int start = chunk->start;
  4016a8:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016ac:	48 8b 00             	mov    (%rax),%rax
  4016af:	89 45 d4             	mov    %eax,-0x2c(%rbp)
          data->threads[thread].start = start;
  4016b2:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016b6:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016ba:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016bd:	48 98                	cltq
  4016bf:	48 c1 e0 0a          	shl    $0xa,%rax
  4016c3:	48 01 c2             	add    %rax,%rdx
  4016c6:	8b 45 d4             	mov    -0x2c(%rbp),%eax
  4016c9:	89 42 14             	mov    %eax,0x14(%rdx)
          
          int end = chunk->end;
  4016cc:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016d0:	48 8b 40 08          	mov    0x8(%rax),%rax
  4016d4:	89 45 d8             	mov    %eax,-0x28(%rbp)
          data->threads[thread].end = end;
  4016d7:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016db:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016df:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016e2:	48 98                	cltq
  4016e4:	48 c1 e0 0a          	shl    $0xa,%rax
  4016e8:	48 01 c2             	add    %rax,%rdx
  4016eb:	8b 45 d8             	mov    -0x28(%rbp),%eax
  4016ee:	89 42 18             	mov    %eax,0x18(%rdx)
        // printf("reader giving %d between %ld and %ld\n", x, start, end);
        
         // clock_gettime(CLOCK_MONOTONIC_RAW, &data->main->works[start].created);
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  4016f1:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016f5:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016f9:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016fc:	48 98                	cltq
  4016fe:	48 c1 e0 0a          	shl    $0xa,%rax
  401702:	48 01 d0             	add    %rdx,%rax
  401705:	8b 90 c8 00 00 00    	mov    0xc8(%rax),%edx
  40170b:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40170f:	48 8b 48 30          	mov    0x30(%rax),%rcx
  401713:	8b 45 d0             	mov    -0x30(%rbp),%eax
  401716:	48 98                	cltq
  401718:	48 c1 e0 0a          	shl    $0xa,%rax
  40171c:	48 01 c8             	add    %rcx,%rax
  40171f:	83 ca 10             	or     $0x10,%edx
  401722:	89 90 c8 00 00 00    	mov    %edx,0xc8(%rax)
        for (int x = 0; x < readers ; x++) {
  401728:	83 45 c0 01          	addl   $0x1,-0x40(%rbp)
  40172c:	8b 45 b0             	mov    -0x50(%rbp),%eax
  40172f:	39 45 c0             	cmp    %eax,-0x40(%rbp)
  401732:	0f 8c e4 fe ff ff    	jl     40161c <singlewriter+0xcd>
  401738:	eb 01                	jmp    40173b <singlewriter+0x1ec>
                  break;
  40173a:	90                   	nop
       // printf("read newmask ORed with %d\n", data->threads[thread].newmask);
        }
      
   for (int x = 0; x < writers ; x++) {
  40173b:	c7 45 c4 00 00 00 00 	movl   $0x0,-0x3c(%rbp)
  401742:	e9 10 01 00 00       	jmp    401857 <singlewriter+0x308>
                if (assignedchunk  == availableidx) {
  401747:	8b 45 b8             	mov    -0x48(%rbp),%eax
  40174a:	39 45 bc             	cmp    %eax,-0x44(%rbp)
  40174d:	0f 84 12 01 00 00    	je     401865 <singlewriter+0x316>
                  
                 //printf("not enough space writer %d %d\n", assignedchunk, availableidx);
                  break;
                }
          int thread = readywriters[x];
  401753:	8b 45 c4             	mov    -0x3c(%rbp),%eax
  401756:	48 98                	cltq
  401758:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401760:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  401764:	48 01 d0             	add    %rdx,%rax
  401767:	8b 00                	mov    (%rax),%eax
  401769:	89 45 dc             	mov    %eax,-0x24(%rbp)
     
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  40176c:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401770:	48 8b 88 a0 00 00 00 	mov    0xa0(%rax),%rcx
  401777:	8b 45 bc             	mov    -0x44(%rbp),%eax
  40177a:	8d 50 01             	lea    0x1(%rax),%edx
  40177d:	89 55 bc             	mov    %edx,-0x44(%rbp)
  401780:	48 98                	cltq
  401782:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  40178a:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  40178e:	48 01 d0             	add    %rdx,%rax
  401791:	48 8b 00             	mov    (%rax),%rax
  401794:	48 c1 e0 05          	shl    $0x5,%rax
  401798:	48 01 c8             	add    %rcx,%rax
  40179b:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
    
      chunk->available = WRITING;
  40179f:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017a3:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
          data->threads[thread].writing = chunk;
  4017aa:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4017ae:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4017b2:	8b 45 dc             	mov    -0x24(%rbp),%eax
  4017b5:	48 98                	cltq
  4017b7:	48 c1 e0 0a          	shl    $0xa,%rax
  4017bb:	48 01 c2             	add    %rax,%rdx
  4017be:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017c2:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
          chunk->owner = thread;
  4017c9:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017cd:	8b 55 dc             	mov    -0x24(%rbp),%edx
  4017d0:	89 50 14             	mov    %edx,0x14(%rax)
          int start = chunk->start;
  4017d3:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017d7:	48 8b 00             	mov    (%rax),%rax
  4017da:	89 45 e0             	mov    %eax,-0x20(%rbp)
          data->threads[thread].publishstart = start;
  4017dd:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4017e1:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4017e5:	8b 45 dc             	mov    -0x24(%rbp),%eax
  4017e8:	48 98                	cltq
  4017ea:	48 c1 e0 0a          	shl    $0xa,%rax
  4017ee:	48 01 c2             	add    %rax,%rdx
  4017f1:	8b 45 e0             	mov    -0x20(%rbp),%eax
  4017f4:	89 42 40             	mov    %eax,0x40(%rdx)
          
          int end = chunk->end;
  4017f7:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017fb:	48 8b 40 08          	mov    0x8(%rax),%rax
  4017ff:	89 45 e4             	mov    %eax,-0x1c(%rbp)
          data->threads[thread].publishend = end;
  401802:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401806:	48 8b 50 30          	mov    0x30(%rax),%rdx
  40180a:	8b 45 dc             	mov    -0x24(%rbp),%eax
  40180d:	48 98                	cltq
  40180f:	48 c1 e0 0a          	shl    $0xa,%rax
  401813:	48 01 c2             	add    %rax,%rdx
  401816:	8b 45 e4             	mov    -0x1c(%rbp),%eax
  401819:	89 42 44             	mov    %eax,0x44(%rdx)
        //  printf("writer giving %d between %ld and %ld\n", available[assignedchunk], start, end);
          // asm volatile ("sfence" ::: "memory");
     
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  40181c:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401820:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401824:	8b 45 dc             	mov    -0x24(%rbp),%eax
  401827:	48 98                	cltq
  401829:	48 c1 e0 0a          	shl    $0xa,%rax
  40182d:	48 01 d0             	add    %rdx,%rax
  401830:	8b 90 c8 00 00 00    	mov    0xc8(%rax),%edx
  401836:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40183a:	48 8b 48 30          	mov    0x30(%rax),%rcx
  40183e:	8b 45 dc             	mov    -0x24(%rbp),%eax
  401841:	48 98                	cltq
  401843:	48 c1 e0 0a          	shl    $0xa,%rax
  401847:	48 01 c8             	add    %rcx,%rax
  40184a:	83 ca 20             	or     $0x20,%edx
  40184d:	89 90 c8 00 00 00    	mov    %edx,0xc8(%rax)
   for (int x = 0; x < writers ; x++) {
  401853:	83 45 c4 01          	addl   $0x1,-0x3c(%rbp)
  401857:	8b 45 b4             	mov    -0x4c(%rbp),%eax
  40185a:	39 45 c4             	cmp    %eax,-0x3c(%rbp)
  40185d:	0f 8c e4 fe ff ff    	jl     401747 <singlewriter+0x1f8>
  401863:	eb 01                	jmp    401866 <singlewriter+0x317>
                  break;
  401865:	90                   	nop
     //printf("write newmask ORed with %ld\n", data->threads[thread].newmask);
        
   } 
      for (int x = 0; x < data->threadsize ; x++) {
  401866:	c7 45 c8 00 00 00 00 	movl   $0x0,-0x38(%rbp)
  40186d:	eb 63                	jmp    4018d2 <singlewriter+0x383>
        if (data->threads[x].newmask != 0) {
  40186f:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401873:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401877:	8b 45 c8             	mov    -0x38(%rbp),%eax
  40187a:	48 98                	cltq
  40187c:	48 c1 e0 0a          	shl    $0xa,%rax
  401880:	48 01 d0             	add    %rdx,%rax
  401883:	8b 80 c8 00 00 00    	mov    0xc8(%rax),%eax
  401889:	85 c0                	test   %eax,%eax
  40188b:	74 41                	je     4018ce <singlewriter+0x37f>
         // printf("thread %d %ld is now %ld\n", x, data->threads[x].ready, data->threads[x].newmask);
          data->threads[x].readies[x] = data->threads[x].newmask;
  40188d:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401891:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401895:	8b 45 c8             	mov    -0x38(%rbp),%eax
  401898:	48 98                	cltq
  40189a:	48 c1 e0 0a          	shl    $0xa,%rax
  40189e:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
  4018a2:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018a6:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4018aa:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018ad:	48 98                	cltq
  4018af:	48 c1 e0 0a          	shl    $0xa,%rax
  4018b3:	48 01 d0             	add    %rdx,%rax
  4018b6:	48 8b 50 20          	mov    0x20(%rax),%rdx
  4018ba:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018bd:	48 98                	cltq
  4018bf:	48 c1 e0 02          	shl    $0x2,%rax
  4018c3:	48 01 c2             	add    %rax,%rdx
  4018c6:	8b 81 c8 00 00 00    	mov    0xc8(%rcx),%eax
  4018cc:	89 02                	mov    %eax,(%rdx)
      for (int x = 0; x < data->threadsize ; x++) {
  4018ce:	83 45 c8 01          	addl   $0x1,-0x38(%rbp)
  4018d2:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018d6:	8b 40 68             	mov    0x68(%rax),%eax
  4018d9:	39 45 c8             	cmp    %eax,-0x38(%rbp)
  4018dc:	7c 91                	jl     40186f <singlewriter+0x320>
        
          
        }
      }
  // clock_gettime(CLOCK_MONOTONIC_RAW, &data->wassign);
  return 0;
  4018de:	b8 00 00 00 00       	mov    $0x0,%eax
}
  4018e3:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  4018e7:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  4018f0:	74 05                	je     4018f7 <singlewriter+0x3a8>
  4018f2:	e8 79 f7 ff ff       	call   401070 <__stack_chk_fail@plt>
  4018f7:	c9                   	leave
  4018f8:	c3                   	ret

00000000004018f9 <threadwork>:

int * threadwork(struct Data * data) {
  4018f9:	55                   	push   %rbp
  4018fa:	48 89 e5             	mov    %rsp,%rbp
  4018fd:	48 81 ec 90 00 00 00 	sub    $0x90,%rsp
  401904:	48 89 bd 78 ff ff ff 	mov    %rdi,-0x88(%rbp)
  40190b:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401914:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  401918:	31 c0                	xor    %eax,%eax
  int cursorlimit = 5;
  40191a:	c7 45 a4 05 00 00 00 	movl   $0x5,-0x5c(%rbp)
  int epochsize = 1;
  401921:	c7 45 a8 01 00 00 00 	movl   $0x1,-0x58(%rbp)
  int epochwidth = 0xff;
  401928:	c7 45 ac ff 00 00 00 	movl   $0xff,-0x54(%rbp)

//printf("%ld %ld w%d\n", lastwrite, data->prevwrite, data->threadindex);
 //if (lastwrite != data->prevwrite) {
   
    uint64_t rsp;
    asm( "mov %%rsp, %0" : "=rm" ( rsp ));
  40192f:	48 89 e0             	mov    %rsp,%rax
  401932:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
  data->scheduler->rsp = rsp;
  401936:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  40193d:	48 8b 80 c8 03 00 00 	mov    0x3c8(%rax),%rax
  401944:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  401948:	48 89 10             	mov    %rdx,(%rax)
  // switch_to(struct Coroutine * coroutines, int index
  //printf("table %x\n", (void *)data->coroutines);
 // printf("coroutine 3 %x\n", &data->coroutines[3]);
 // printf("coroutine eip %lx\n", data->coroutines[3].eip);
 // printf("coroutine data %lx\n", data->coroutines[3].data);
  switch_to(data->coroutines, 3, data->scheduler);  
  40194b:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401952:	48 8b 90 c8 03 00 00 	mov    0x3c8(%rax),%rdx
  401959:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401960:	48 8b 80 c0 03 00 00 	mov    0x3c0(%rax),%rax
  401967:	be 03 00 00 00       	mov    $0x3,%esi
  40196c:	48 89 c7             	mov    %rax,%rdi
  40196f:	e8 04 1d 00 00       	call   403678 <switch_to>
  //printf("finished coroutine\n");
  //printf("%ld %ld w%d\n", lastwrite, data->prevwrite, data->threadindex);
     
       
clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401974:	48 8d 45 e0          	lea    -0x20(%rbp),%rax
  401978:	48 89 c6             	mov    %rax,%rsi
  40197b:	bf 04 00 00 00       	mov    $0x4,%edi
  401980:	e8 cb f6 ff ff       	call   401050 <clock_gettime@plt>
  //if (data->threadindex % 2 == 0) {
   
  if (data->running == 2) {
  401985:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  40198c:	8b 40 5c             	mov    0x5c(%rax),%eax
  40198f:	83 f8 02             	cmp    $0x2,%eax
  401992:	0f 85 9f 01 00 00    	jne    401b37 <threadwork+0x23e>
  //if (data ->threadindex == 0 ) {
      

   for (int x = 0 ; x < data->threadsize ; x++) {
  401998:	c7 45 98 00 00 00 00 	movl   $0x0,-0x68(%rbp)
  40199f:	e9 50 01 00 00       	jmp    401af4 <threadwork+0x1fb>
      
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  4019a4:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019ab:	48 8b 40 28          	mov    0x28(%rax),%rax
  4019af:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  4019b6:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019bd:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  4019c3:	c1 e0 07             	shl    $0x7,%eax
  4019c6:	48 98                	cltq
  4019c8:	48 c1 e0 03          	shl    $0x3,%rax
  4019cc:	48 01 d0             	add    %rdx,%rax
  4019cf:	48 8b 00             	mov    (%rax),%rax
  4019d2:	8b 55 a8             	mov    -0x58(%rbp),%edx
  4019d5:	48 63 fa             	movslq %edx,%rdi
  4019d8:	48 99                	cqto
  4019da:	48 f7 ff             	idiv   %rdi
  4019dd:	48 89 c2             	mov    %rax,%rdx
  4019e0:	8b 45 ac             	mov    -0x54(%rbp),%eax
  4019e3:	48 63 c8             	movslq %eax,%rcx
  4019e6:	48 89 d0             	mov    %rdx,%rax
  4019e9:	48 99                	cqto
  4019eb:	48 f7 f9             	idiv   %rcx
  4019ee:	48 89 d0             	mov    %rdx,%rax
  4019f1:	89 45 9c             	mov    %eax,-0x64(%rbp)
    
      //  buffer = data->mystream << 24 | ( global << 16) | data->threadindex << 8 | data->writecursor % 0xff;
    int cursor = data->writecursor;
  4019f4:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019fb:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401a01:	89 45 a0             	mov    %eax,-0x60(%rbp)
    //cursor = 0;
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  401a04:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a0b:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401a11:	c1 e0 18             	shl    $0x18,%eax
  401a14:	89 c2                	mov    %eax,%edx
  401a16:	8b 45 9c             	mov    -0x64(%rbp),%eax
  401a19:	c1 e0 10             	shl    $0x10,%eax
  401a1c:	89 d6                	mov    %edx,%esi
  401a1e:	09 c6                	or     %eax,%esi
  401a20:	8b 45 a0             	mov    -0x60(%rbp),%eax
  401a23:	48 63 d0             	movslq %eax,%rdx
  401a26:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401a2d:	48 c1 ea 20          	shr    $0x20,%rdx
  401a31:	01 c2                	add    %eax,%edx
  401a33:	c1 fa 07             	sar    $0x7,%edx
  401a36:	89 c7                	mov    %eax,%edi
  401a38:	c1 ff 1f             	sar    $0x1f,%edi
  401a3b:	89 d1                	mov    %edx,%ecx
  401a3d:	29 f9                	sub    %edi,%ecx
  401a3f:	89 ca                	mov    %ecx,%edx
  401a41:	c1 e2 08             	shl    $0x8,%edx
  401a44:	29 ca                	sub    %ecx,%edx
  401a46:	29 d0                	sub    %edx,%eax
  401a48:	89 c1                	mov    %eax,%ecx
  401a4a:	89 f0                	mov    %esi,%eax
  401a4c:	09 c8                	or     %ecx,%eax
  401a4e:	48 98                	cltq
  401a50:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
      buffer = data->mystream << 24 | ( (data->main->globalwrite[data->mystream * 128] / (data->threadsize)) % 0xff) << 16 | data->writecursor;
    }
    */
      // printf("%x\n", buffer);
        // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
  struct Data * thread = &data->threads[data->threadindex];
  401a54:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a5b:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401a5f:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a66:	8b 40 64             	mov    0x64(%rax),%eax
  401a69:	48 98                	cltq
  401a6b:	48 c1 e0 0a          	shl    $0xa,%rax
  401a6f:	48 01 d0             	add    %rdx,%rax
  401a72:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
  epoch->buffer = buffer;
  epoch->set = 1;
  }
    
     // printf("alrrady filled\n");
  if (data->main->works[buffer] != -1) {
  401a76:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a7d:	48 8b 40 28          	mov    0x28(%rax),%rax
  401a81:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401a85:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401a89:	48 01 d0             	add    %rdx,%rax
  401a8c:	0f b6 00             	movzbl (%rax),%eax
  401a8f:	3c ff                	cmp    $0xff,%al
  401a91:	74 1a                	je     401aad <threadwork+0x1b4>
    
    data->freq_writes++;
  401a93:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a9a:	48 8b 40 50          	mov    0x50(%rax),%rax
  401a9e:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401aa2:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401aa9:	48 89 50 50          	mov    %rdx,0x50(%rax)
  }
  data->main->works[buffer] = data->threadindex;
  401aad:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ab4:	8b 50 64             	mov    0x64(%rax),%edx
  401ab7:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401abe:	48 8b 40 28          	mov    0x28(%rax),%rax
  401ac2:	48 8b 48 70          	mov    0x70(%rax),%rcx
  401ac6:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401aca:	48 01 c8             	add    %rcx,%rax
  401acd:	88 10                	mov    %dl,(%rax)
         
         
  //  data->prevread = data->main->currentread;
     
     
    data->writecursor = (data->writecursor + 1) % cursorlimit;
  401acf:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ad6:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401adc:	83 c0 01             	add    $0x1,%eax
  401adf:	99                   	cltd
  401ae0:	f7 7d a4             	idivl  -0x5c(%rbp)
  401ae3:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401aea:	89 90 80 01 00 00    	mov    %edx,0x180(%rax)
   for (int x = 0 ; x < data->threadsize ; x++) {
  401af0:	83 45 98 01          	addl   $0x1,-0x68(%rbp)
  401af4:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401afb:	8b 40 68             	mov    0x68(%rax),%eax
  401afe:	39 45 98             	cmp    %eax,-0x68(%rbp)
  401b01:	0f 8c 9d fe ff ff    	jl     4019a4 <threadwork+0xab>
    
   }
      
    __atomic_fetch_add(&data->main->globalwrite[data->mystream * 128], 1, __ATOMIC_RELAXED);
  401b07:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b0e:	48 8b 40 28          	mov    0x28(%rax),%rax
  401b12:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401b19:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b20:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401b26:	c1 e0 07             	shl    $0x7,%eax
  401b29:	48 98                	cltq
  401b2b:	48 c1 e0 03          	shl    $0x3,%rax
  401b2f:	48 01 d0             	add    %rdx,%rax
  401b32:	f0 48 83 00 01       	lock addq $0x1,(%rax)
//}
  } 
  ///else {
  long thisgroup = data->main->globalwrite[data->mystream * 128] / epochsize;
  401b37:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b3e:	48 8b 40 28          	mov    0x28(%rax),%rax
  401b42:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401b49:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b50:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401b56:	c1 e0 07             	shl    $0x7,%eax
  401b59:	48 98                	cltq
  401b5b:	48 c1 e0 03          	shl    $0x3,%rax
  401b5f:	48 01 d0             	add    %rdx,%rax
  401b62:	48 8b 00             	mov    (%rax),%rax
  401b65:	8b 55 a8             	mov    -0x58(%rbp),%edx
  401b68:	48 63 fa             	movslq %edx,%rdi
  401b6b:	48 99                	cqto
  401b6d:	48 f7 ff             	idiv   %rdi
  401b70:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
  
  if (thisgroup != data->lastgroup) {
  401b74:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b7b:	8b 80 88 03 00 00    	mov    0x388(%rax),%eax
  401b81:	48 98                	cltq
  401b83:	48 39 45 c8          	cmp    %rax,-0x38(%rbp)
  401b87:	74 11                	je     401b9a <threadwork+0x2a1>
     // printf("ndw group\n");
      data->writecursor = 0;
  401b89:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b90:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
        epoch->thread = data->threadindex;
        epoch->stream = data->mystream;
        epoch->set = 1;
     }
   }
   data->lastgroup = thisgroup;
  401b9a:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
  401b9e:	89 c2                	mov    %eax,%edx
  401ba0:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ba7:	89 90 88 03 00 00    	mov    %edx,0x388(%rax)
  //}
  
 //if (lastread != data->prevread)
 // {
   //printf("%ld  %ld r%d\n", data->main->currentread, data->prevread, data->threadindex);
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  401bad:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bb4:	48 8b 40 28          	mov    0x28(%rax),%rax
  401bb8:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401bbf:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bc6:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401bcc:	c1 e0 07             	shl    $0x7,%eax
  401bcf:	48 98                	cltq
  401bd1:	48 c1 e0 03          	shl    $0x3,%rax
  401bd5:	48 01 d0             	add    %rdx,%rax
  401bd8:	48 8b 00             	mov    (%rax),%rax
  401bdb:	48 89 45 d0          	mov    %rax,-0x30(%rbp)
  
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
  401bdf:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401be6:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401bed:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bf4:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401bfa:	48 63 d0             	movslq %eax,%rdx
  401bfd:	48 89 d0             	mov    %rdx,%rax
  401c00:	48 01 c0             	add    %rax,%rax
  401c03:	48 01 d0             	add    %rdx,%rax
  401c06:	48 c1 e0 02          	shl    $0x2,%rax
  401c0a:	48 01 c8             	add    %rcx,%rax
  401c0d:	8b 00                	mov    (%rax),%eax
  401c0f:	48 98                	cltq
  401c11:	48 39 45 d0          	cmp    %rax,-0x30(%rbp)
  401c15:	7f 0b                	jg     401c22 <threadwork+0x329>
  401c17:	48 83 7d d0 00       	cmpq   $0x0,-0x30(%rbp)
  401c1c:	0f 85 f9 02 00 00    	jne    401f1b <threadwork+0x622>
    for (int x = 0; x < data->threadsize - 1; x++) {
  401c22:	c7 45 94 00 00 00 00 	movl   $0x0,-0x6c(%rbp)
  401c29:	e9 d7 02 00 00       	jmp    401f05 <threadwork+0x60c>
  // printf("%d\n", thiswrite);
   data->freq++;
  401c2e:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c35:	48 8b 40 48          	mov    0x48(%rax),%rax
  401c39:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401c3d:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c44:	48 89 50 48          	mov    %rdx,0x48(%rax)
  
        
      
          
            
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  401c48:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c4f:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401c56:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c5d:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401c63:	48 63 d0             	movslq %eax,%rdx
  401c66:	48 89 d0             	mov    %rdx,%rax
  401c69:	48 01 c0             	add    %rax,%rax
  401c6c:	48 01 d0             	add    %rdx,%rax
  401c6f:	48 c1 e0 02          	shl    $0x2,%rax
  401c73:	48 01 c8             	add    %rcx,%rax
  401c76:	8b 00                	mov    (%rax),%eax
  401c78:	99                   	cltd
  401c79:	f7 7d a8             	idivl  -0x58(%rbp)
  401c7c:	83 e8 01             	sub    $0x1,%eax
  401c7f:	99                   	cltd
  401c80:	f7 7d ac             	idivl  -0x54(%rbp)
  401c83:	89 d0                	mov    %edx,%eax
  401c85:	48 98                	cltq
  401c87:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
        //long past = (((data->globalread[data->laststream]).global % epochwidth;
            if (past < 0) {
  401c8b:	48 83 7d b0 00       	cmpq   $0x0,-0x50(%rbp)
  401c90:	79 08                	jns    401c9a <threadwork+0x3a1>
              past = 0;
  401c92:	48 c7 45 b0 00 00 00 00 	movq   $0x0,-0x50(%rbp)
            }
            
            // long buffer = (data->threadindex << 24) | (data->main->globalwrite % 0xf) << 16 | (data->main->writecursor % 0xf);
        
       // buffer = data->laststream << 24 | (past << 16) | data->globalread[data->laststream].thread << 8, data->globalread[data->laststream].cursor % 0xff;
    int cursor = data->globalread[data->laststream].cursor;
  401c9a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ca1:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401ca8:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401caf:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401cb5:	48 63 d0             	movslq %eax,%rdx
  401cb8:	48 89 d0             	mov    %rdx,%rax
  401cbb:	48 01 c0             	add    %rax,%rax
  401cbe:	48 01 d0             	add    %rdx,%rax
  401cc1:	48 c1 e0 02          	shl    $0x2,%rax
  401cc5:	48 01 c8             	add    %rcx,%rax
  401cc8:	8b 40 04             	mov    0x4(%rax),%eax
  401ccb:	89 45 8c             	mov    %eax,-0x74(%rbp)
    //cursor = 0;
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  401cce:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cd5:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401cdb:	c1 e0 18             	shl    $0x18,%eax
  401cde:	48 63 d0             	movslq %eax,%rdx
  401ce1:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
  401ce5:	48 c1 e0 10          	shl    $0x10,%rax
  401ce9:	48 89 d6             	mov    %rdx,%rsi
  401cec:	48 09 c6             	or     %rax,%rsi
  401cef:	8b 45 8c             	mov    -0x74(%rbp),%eax
  401cf2:	48 63 d0             	movslq %eax,%rdx
  401cf5:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401cfc:	48 c1 ea 20          	shr    $0x20,%rdx
  401d00:	01 c2                	add    %eax,%edx
  401d02:	c1 fa 07             	sar    $0x7,%edx
  401d05:	89 c1                	mov    %eax,%ecx
  401d07:	c1 f9 1f             	sar    $0x1f,%ecx
  401d0a:	29 ca                	sub    %ecx,%edx
  401d0c:	89 d1                	mov    %edx,%ecx
  401d0e:	c1 e1 08             	shl    $0x8,%ecx
  401d11:	29 d1                	sub    %edx,%ecx
  401d13:	29 c8                	sub    %ecx,%eax
  401d15:	89 c2                	mov    %eax,%edx
  401d17:	48 63 c2             	movslq %edx,%rax
  401d1a:	48 09 f0             	or     %rsi,%rax
  401d1d:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    access->cursor = data->globalread[data->laststream].cursor % 0xff;
    access->set = 1;
    data->cread = (data->cread + 1) % data->accesssize;
  }
    
    int thistream = data->laststream; 
  401d21:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d28:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401d2e:	89 45 90             	mov    %eax,-0x70(%rbp)
                // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
                //&data->threads[data->threadindex];

        // printf("%d\n", data->main->works[buffer]);
    
        if (data->main->works[buffer] != -1) {
  401d31:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d38:	48 8b 40 28          	mov    0x28(%rax),%rax
  401d3c:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401d40:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401d44:	48 01 d0             	add    %rdx,%rax
  401d47:	0f b6 00             	movzbl (%rax),%eax
  401d4a:	3c ff                	cmp    $0xff,%al
  401d4c:	74 39                	je     401d87 <threadwork+0x48e>
          data->successreads++;
  401d4e:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d55:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  401d5c:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401d60:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d67:	48 89 90 98 03 00 00 	mov    %rdx,0x398(%rax)
          
          data->main->works[buffer] = -1;
  401d6e:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d75:	48 8b 40 28          	mov    0x28(%rax),%rax
  401d79:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401d7d:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401d81:	48 01 d0             	add    %rdx,%rax
  401d84:	c6 00 ff             	movb   $0xff,(%rax)
  
    
    
      
    
    if (data->globalread[thistream].cursor < cursorlimit) {
  401d87:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d8e:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401d95:	8b 45 90             	mov    -0x70(%rbp),%eax
  401d98:	48 63 d0             	movslq %eax,%rdx
  401d9b:	48 89 d0             	mov    %rdx,%rax
  401d9e:	48 01 c0             	add    %rax,%rax
  401da1:	48 01 d0             	add    %rdx,%rax
  401da4:	48 c1 e0 02          	shl    $0x2,%rax
  401da8:	48 01 c8             	add    %rcx,%rax
  401dab:	8b 40 04             	mov    0x4(%rax),%eax
  401dae:	39 45 a4             	cmp    %eax,-0x5c(%rbp)
  401db1:	7e 7c                	jle    401e2f <threadwork+0x536>
    
      data->globalread[thistream].global++;
  401db3:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401dba:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401dc1:	8b 45 90             	mov    -0x70(%rbp),%eax
  401dc4:	48 63 d0             	movslq %eax,%rdx
  401dc7:	48 89 d0             	mov    %rdx,%rax
  401dca:	48 01 c0             	add    %rax,%rax
  401dcd:	48 01 d0             	add    %rdx,%rax
  401dd0:	48 c1 e0 02          	shl    $0x2,%rax
  401dd4:	48 01 c8             	add    %rcx,%rax
  401dd7:	8b 10                	mov    (%rax),%edx
  401dd9:	83 c2 01             	add    $0x1,%edx
  401ddc:	89 10                	mov    %edx,(%rax)
        
        
      data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1);
  401dde:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401de5:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401dec:	8b 45 90             	mov    -0x70(%rbp),%eax
  401def:	48 63 d0             	movslq %eax,%rdx
  401df2:	48 89 d0             	mov    %rdx,%rax
  401df5:	48 01 c0             	add    %rax,%rax
  401df8:	48 01 d0             	add    %rdx,%rax
  401dfb:	48 c1 e0 02          	shl    $0x2,%rax
  401dff:	48 01 c8             	add    %rcx,%rax
  401e02:	8b 48 04             	mov    0x4(%rax),%ecx
  401e05:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e0c:	48 8b b0 48 03 00 00 	mov    0x348(%rax),%rsi
  401e13:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e16:	48 63 d0             	movslq %eax,%rdx
  401e19:	48 89 d0             	mov    %rdx,%rax
  401e1c:	48 01 c0             	add    %rax,%rax
  401e1f:	48 01 d0             	add    %rdx,%rax
  401e22:	48 c1 e0 02          	shl    $0x2,%rax
  401e26:	48 01 f0             	add    %rsi,%rax
  401e29:	8d 51 01             	lea    0x1(%rcx),%edx
  401e2c:	89 50 04             	mov    %edx,0x4(%rax)
      
      }
    
    if (data->globalread[thistream].cursor == cursorlimit) {
  401e2f:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e36:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401e3d:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e40:	48 63 d0             	movslq %eax,%rdx
  401e43:	48 89 d0             	mov    %rdx,%rax
  401e46:	48 01 c0             	add    %rax,%rax
  401e49:	48 01 d0             	add    %rdx,%rax
  401e4c:	48 c1 e0 02          	shl    $0x2,%rax
  401e50:	48 01 c8             	add    %rcx,%rax
  401e53:	8b 40 04             	mov    0x4(%rax),%eax
  401e56:	39 45 a4             	cmp    %eax,-0x5c(%rbp)
  401e59:	75 48                	jne    401ea3 <threadwork+0x5aa>
      
      data->laststream = (data->laststream + 1);
  401e5b:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e62:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401e68:	8d 50 01             	lea    0x1(%rax),%edx
  401e6b:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e72:	89 90 90 03 00 00    	mov    %edx,0x390(%rax)
     // data->globalread[thistream].global++;
data->globalread[thistream].cursor = 0;
  401e78:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e7f:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401e86:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e89:	48 63 d0             	movslq %eax,%rdx
  401e8c:	48 89 d0             	mov    %rdx,%rax
  401e8f:	48 01 c0             	add    %rax,%rax
  401e92:	48 01 d0             	add    %rdx,%rax
  401e95:	48 c1 e0 02          	shl    $0x2,%rax
  401e99:	48 01 c8             	add    %rcx,%rax
  401e9c:	c7 40 04 00 00 00 00 	movl   $0x0,0x4(%rax)
    }
    
    if (data->laststream == data->mystream) {
  401ea3:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401eaa:	8b 90 90 03 00 00    	mov    0x390(%rax),%edx
  401eb0:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401eb7:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401ebd:	39 c2                	cmp    %eax,%edx
  401ebf:	75 1d                	jne    401ede <threadwork+0x5e5>
      data->laststream = data->laststream + 1;
  401ec1:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ec8:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401ece:	8d 50 01             	lea    0x1(%rax),%edx
  401ed1:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ed8:	89 90 90 03 00 00    	mov    %edx,0x390(%rax)
     // data->globalread[data->laststream].cursor = 0;
    }
    if (data->laststream == 5) {
  401ede:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ee5:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401eeb:	83 f8 05             	cmp    $0x5,%eax
  401eee:	75 11                	jne    401f01 <threadwork+0x608>
       data->laststream = 1;
  401ef0:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ef7:	c7 80 90 03 00 00 01 00 00 00 	movl   $0x1,0x390(%rax)
    for (int x = 0; x < data->threadsize - 1; x++) {
  401f01:	83 45 94 01          	addl   $0x1,-0x6c(%rbp)
  401f05:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401f0c:	8b 40 68             	mov    0x68(%rax),%eax
  401f0f:	83 e8 01             	sub    $0x1,%eax
  401f12:	39 45 94             	cmp    %eax,-0x6c(%rbp)
  401f15:	0f 8c 13 fd ff ff    	jl     401c2e <threadwork+0x335>
      
     //asm volatile ("sfence" ::: "memory");
  
      
       
}
  401f1b:	90                   	nop
  401f1c:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  401f20:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401f29:	74 05                	je     401f30 <threadwork+0x637>
  401f2b:	e8 40 f1 ff ff       	call   401070 <__stack_chk_fail@plt>
  401f30:	c9                   	leave
  401f31:	c3                   	ret

0000000000401f32 <work2>:

void * work2(void * arg) {
  401f32:	55                   	push   %rbp
  401f33:	48 89 e5             	mov    %rsp,%rbp
  401f36:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  struct Data *data = (struct Data*) arg;
  401f3a:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401f3e:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  while (data->running == 1) {
  401f42:	eb 14                	jmp    401f58 <work2+0x26>
    asm volatile ("" ::: "memory");
      data->freq++;
  401f44:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f48:	48 8b 40 48          	mov    0x48(%rax),%rax
  401f4c:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401f50:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f54:	48 89 50 48          	mov    %rdx,0x48(%rax)
  while (data->running == 1) {
  401f58:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f5c:	8b 40 5c             	mov    0x5c(%rax),%eax
  401f5f:	83 f8 01             	cmp    $0x1,%eax
  401f62:	74 e0                	je     401f44 <work2+0x12>
  }
  
}
  401f64:	90                   	nop
  401f65:	5d                   	pop    %rbp
  401f66:	c3                   	ret

0000000000401f67 <work>:

void * work(void * arg) {
  401f67:	55                   	push   %rbp
  401f68:	48 89 e5             	mov    %rsp,%rbp
  401f6b:	48 83 ec 50          	sub    $0x50,%rsp
  401f6f:	48 89 7d b8          	mov    %rdi,-0x48(%rbp)

  
  int writers;
  int readers;
  struct Data *data = (struct Data*) arg;
  401f73:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401f77:	48 89 45 e0          	mov    %rax,-0x20(%rbp)
  printf("started thread %d\n", data->threadindex);
  401f7b:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401f7f:	8b 40 64             	mov    0x64(%rax),%eax
  401f82:	89 c6                	mov    %eax,%esi
  401f84:	48 8d 05 8c 20 00 00 	lea    0x208c(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  401f8b:	48 89 c7             	mov    %rax,%rdi
  401f8e:	b8 00 00 00 00       	mov    $0x0,%eax
  401f93:	e8 e8 f0 ff ff       	call   401080 <printf@plt>
  
  
  int found = 0;
  401f98:	c7 45 c8 00 00 00 00 	movl   $0x0,-0x38(%rbp)
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  401f9f:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fa3:	8b 40 64             	mov    0x64(%rax),%eax
  401fa6:	8d 50 01             	lea    0x1(%rax),%edx
  401fa9:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fad:	8b 48 68             	mov    0x68(%rax),%ecx
  401fb0:	89 d0                	mov    %edx,%eax
  401fb2:	99                   	cltd
  401fb3:	f7 f9                	idiv   %ecx
  401fb5:	89 55 cc             	mov    %edx,-0x34(%rbp)
  int innerfind = 0;
  401fb8:	c7 45 d0 00 00 00 00 	movl   $0x0,-0x30(%rbp)
  
  
  
  
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  401fbf:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fc3:	48 8b 80 b8 00 00 00 	mov    0xb8(%rax),%rax
  401fca:	48 83 c0 01          	add    $0x1,%rax
  401fce:	be 08 00 00 00       	mov    $0x8,%esi
  401fd3:	48 89 c7             	mov    %rax,%rdi
  401fd6:	e8 f5 f0 ff ff       	call   4010d0 <calloc@plt>
  401fdb:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  401fdf:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fe3:	8b 40 68             	mov    0x68(%rax),%eax
  401fe6:	48 98                	cltq
  401fe8:	be 04 00 00 00       	mov    $0x4,%esi
  401fed:	48 89 c7             	mov    %rax,%rdi
  401ff0:	e8 db f0 ff ff       	call   4010d0 <calloc@plt>
  401ff5:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
  int * readywriters = calloc(data->threadsize, sizeof(int));
  401ff9:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401ffd:	8b 40 68             	mov    0x68(%rax),%eax
  402000:	48 98                	cltq
  402002:	be 04 00 00 00       	mov    $0x4,%esi
  402007:	48 89 c7             	mov    %rax,%rdi
  40200a:	e8 c1 f0 ff ff       	call   4010d0 <calloc@plt>
  40200f:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  
  
  int stop = 0;
  402013:	c7 45 d4 00 00 00 00 	movl   $0x0,-0x2c(%rbp)
  while (data->running > 0)  {
  40201a:	eb 25                	jmp    402041 <work+0xda>
    writers = 0;
  40201c:	c7 45 d8 00 00 00 00 	movl   $0x0,-0x28(%rbp)
    readers = 0;
  402023:	c7 45 dc 00 00 00 00 	movl   $0x0,-0x24(%rbp)
    stop = 0;
  40202a:	c7 45 d4 00 00 00 00 	movl   $0x0,-0x2c(%rbp)
    asm volatile ("":"=m" (data->running)::);
  402031:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
   // printf("write cycle\n");
    //memset(available, -1, data->threadsize);

      threadwork(data);
  402035:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402039:	48 89 c7             	mov    %rax,%rdi
  40203c:	e8 b8 f8 ff ff       	call   4018f9 <threadwork>
  while (data->running > 0)  {
  402041:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402045:	8b 40 5c             	mov    0x5c(%rax),%eax
  402048:	85 c0                	test   %eax,%eax
  40204a:	7f d0                	jg     40201c <work+0xb5>
        for (int x = 0 ; x < data->worksize; x++) {
          data->main->works[x].available = 1;
        }
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
  40204c:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402050:	8b 40 64             	mov    0x64(%rax),%eax
  402053:	89 c6                	mov    %eax,%esi
  402055:	48 8d 05 ce 1f 00 00 	lea    0x1fce(%rip),%rax        # 40402a <_IO_stdin_used+0x2a>
  40205c:	48 89 c7             	mov    %rax,%rdi
  40205f:	b8 00 00 00 00       	mov    $0x0,%eax
  402064:	e8 17 f0 ff ff       	call   401080 <printf@plt>
}
  402069:	90                   	nop
  40206a:	c9                   	leave
  40206b:	c3                   	ret

000000000040206c <main>:

int main(int argc, char **argv) {
  40206c:	55                   	push   %rbp
  40206d:	48 89 e5             	mov    %rsp,%rbp
  402070:	53                   	push   %rbx
  402071:	48 81 ec 78 01 00 00 	sub    $0x178,%rsp
  402078:	89 bd 8c fe ff ff    	mov    %edi,-0x174(%rbp)
  40207e:	48 89 b5 80 fe ff ff 	mov    %rsi,-0x180(%rbp)
  402085:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40208e:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  402092:	31 c0                	xor    %eax,%eax
  int debug = 0;
  402094:	c7 85 a0 fe ff ff 00 00 00 00 	movl   $0x0,-0x160(%rbp)
  int seconds = DURATION;
  40209e:	c7 85 a4 fe ff ff 01 00 00 00 	movl   $0x1,-0x15c(%rbp)
  int worksize_each = 1;
  4020a8:	c7 85 94 fe ff ff 01 00 00 00 	movl   $0x1,-0x16c(%rbp)
  int threadsize = THREADS;
  4020b2:	c7 85 98 fe ff ff 0f 00 00 00 	movl   $0xf,-0x168(%rbp)
  
  int workers = threadsize - 1;
  4020bc:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4020c2:	83 e8 01             	sub    $0x1,%eax
  4020c5:	89 85 9c fe ff ff    	mov    %eax,-0x164(%rbp)
  printf("read mask %d\n", READ_MASK);
  4020cb:	be 08 00 00 00       	mov    $0x8,%esi
  4020d0:	48 8d 05 63 1f 00 00 	lea    0x1f63(%rip),%rax        # 40403a <_IO_stdin_used+0x3a>
  4020d7:	48 89 c7             	mov    %rax,%rdi
  4020da:	b8 00 00 00 00       	mov    $0x0,%eax
  4020df:	e8 9c ef ff ff       	call   401080 <printf@plt>
  printf("write mask %d\n", WRITE_MASK);
  4020e4:	be 04 00 00 00       	mov    $0x4,%esi
  4020e9:	48 8d 05 58 1f 00 00 	lea    0x1f58(%rip),%rax        # 404048 <_IO_stdin_used+0x48>
  4020f0:	48 89 c7             	mov    %rax,%rdi
  4020f3:	b8 00 00 00 00       	mov    $0x0,%eax
  4020f8:	e8 83 ef ff ff       	call   401080 <printf@plt>
  printf("prepwrite mask %d\n", PREP_WRITE_MASK);
  4020fd:	be 20 00 00 00       	mov    $0x20,%esi
  402102:	48 8d 05 4e 1f 00 00 	lea    0x1f4e(%rip),%rax        # 404057 <_IO_stdin_used+0x57>
  402109:	48 89 c7             	mov    %rax,%rdi
  40210c:	b8 00 00 00 00       	mov    $0x0,%eax
  402111:	e8 6a ef ff ff       	call   401080 <printf@plt>
  printf("Starting %d workers\n", threadsize);
  402116:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40211c:	89 c6                	mov    %eax,%esi
  40211e:	48 8d 05 45 1f 00 00 	lea    0x1f45(%rip),%rax        # 40406a <_IO_stdin_used+0x6a>
  402125:	48 89 c7             	mov    %rax,%rdi
  402128:	b8 00 00 00 00       	mov    $0x0,%eax
  40212d:	e8 4e ef ff ff       	call   401080 <printf@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  402132:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402138:	48 98                	cltq
  40213a:	be 08 00 00 00       	mov    $0x8,%esi
  40213f:	48 89 c7             	mov    %rax,%rdi
  402142:	e8 89 ef ff ff       	call   4010d0 <calloc@plt>
  402147:	48 89 85 18 ff ff ff 	mov    %rax,-0xe8(%rbp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  40214e:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402154:	48 98                	cltq
  402156:	be 38 00 00 00       	mov    $0x38,%esi
  40215b:	48 89 c7             	mov    %rax,%rdi
  40215e:	e8 6d ef ff ff       	call   4010d0 <calloc@plt>
  402163:	48 89 85 f0 fe ff ff 	mov    %rax,-0x110(%rbp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40216a:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402170:	48 98                	cltq
  402172:	48 c1 e0 0a          	shl    $0xa,%rax
  402176:	48 89 c6             	mov    %rax,%rsi
  402179:	bf 01 00 00 00       	mov    $0x1,%edi
  40217e:	e8 4d ef ff ff       	call   4010d0 <calloc@plt>
  402183:	48 89 85 f8 fe ff ff 	mov    %rax,-0x108(%rbp)
  
  long offset = 0;
  40218a:	48 c7 85 00 ff ff ff 00 00 00 00 	movq   $0x0,-0x100(%rbp)
  long chunkslen = 0xffffffff;
  402195:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
  40219a:	48 89 85 08 ff ff ff 	mov    %rax,-0xf8(%rbp)
  long worksize = chunkslen * worksize_each;
  4021a1:	8b 85 94 fe ff ff    	mov    -0x16c(%rbp),%eax
  4021a7:	48 98                	cltq
  4021a9:	48 8b 95 08 ff ff ff 	mov    -0xf8(%rbp),%rdx
  4021b0:	48 0f af c2          	imul   %rdx,%rax
  4021b4:	48 89 85 10 ff ff ff 	mov    %rax,-0xf0(%rbp)
  int buckets = worksize / threadsize;
  4021bb:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4021c1:	48 63 d8             	movslq %eax,%rbx
  4021c4:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  4021cb:	48 99                	cqto
  4021cd:	48 f7 fb             	idiv   %rbx
  4021d0:	89 85 90 fe ff ff    	mov    %eax,-0x170(%rbp)
  long chunksize = ceil((double) worksize / (double) chunkslen);
  4021d6:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4021da:	f2 48 0f 2a 85 10 ff ff ff 	cvtsi2sdq -0xf0(%rbp),%xmm0
  4021e3:	66 0f ef c9          	pxor   %xmm1,%xmm1
  4021e7:	f2 48 0f 2a 8d 08 ff ff ff 	cvtsi2sdq -0xf8(%rbp),%xmm1
  4021f0:	f2 0f 5e c1          	divsd  %xmm1,%xmm0
  4021f4:	66 48 0f 7e c0       	movq   %xmm0,%rax
  4021f9:	66 48 0f 6e c0       	movq   %rax,%xmm0
  4021fe:	e8 1d ef ff ff       	call   401120 <ceil@plt>
  402203:	f2 48 0f 2c c0       	cvttsd2si %xmm0,%rax
  402208:	48 89 85 38 ff ff ff 	mov    %rax,-0xc8(%rbp)
  char *works = calloc(worksize, sizeof(char));
  40220f:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  402216:	be 01 00 00 00       	mov    $0x1,%esi
  40221b:	48 89 c7             	mov    %rax,%rdi
  40221e:	e8 ad ee ff ff       	call   4010d0 <calloc@plt>
  402223:	48 89 85 40 ff ff ff 	mov    %rax,-0xc0(%rbp)
  memset(works, -1, worksize);
  40222a:	48 8b 95 10 ff ff ff 	mov    -0xf0(%rbp),%rdx
  402231:	48 8b 85 40 ff ff ff 	mov    -0xc0(%rbp),%rax
  402238:	be ff ff ff ff       	mov    $0xffffffff,%esi
  40223d:	48 89 c7             	mov    %rax,%rdi
  402240:	e8 7b ee ff ff       	call   4010c0 <memset@plt>
  printf("Buffer size %ld\n", worksize);
  402245:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  40224c:	48 89 c6             	mov    %rax,%rsi
  40224f:	48 8d 05 29 1e 00 00 	lea    0x1e29(%rip),%rax        # 40407f <_IO_stdin_used+0x7f>
  402256:	48 89 c7             	mov    %rax,%rdi
  402259:	b8 00 00 00 00       	mov    $0x0,%eax
  40225e:	e8 1d ee ff ff       	call   401080 <printf@plt>
  int chunkindex = 0;
  402263:	c7 85 d4 fe ff ff 00 00 00 00 	movl   $0x0,-0x12c(%rbp)
  int * readcursors = calloc(threadsize, sizeof(int));
  40226d:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402273:	48 98                	cltq
  402275:	be 04 00 00 00       	mov    $0x4,%esi
  40227a:	48 89 c7             	mov    %rax,%rdi
  40227d:	e8 4e ee ff ff       	call   4010d0 <calloc@plt>
  402282:	48 89 85 48 ff ff ff 	mov    %rax,-0xb8(%rbp)
  int * writecursors = calloc(threadsize, sizeof(int));
  402289:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40228f:	48 98                	cltq
  402291:	be 04 00 00 00       	mov    $0x4,%esi
  402296:	48 89 c7             	mov    %rax,%rdi
  402299:	e8 32 ee ff ff       	call   4010d0 <calloc@plt>
  40229e:	48 89 85 50 ff ff ff 	mov    %rax,-0xb0(%rbp)
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4022a5:	be 20 00 00 00       	mov    $0x20,%esi
  4022aa:	bf 64 00 00 00       	mov    $0x64,%edi
  4022af:	e8 1c ee ff ff       	call   4010d0 <calloc@plt>
  4022b4:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)

printf("offset %ld\n", offset);
  4022bb:	48 8b 85 00 ff ff ff 	mov    -0x100(%rbp),%rax
  4022c2:	48 89 c6             	mov    %rax,%rsi
  4022c5:	48 8d 05 c4 1d 00 00 	lea    0x1dc4(%rip),%rax        # 404090 <_IO_stdin_used+0x90>
  4022cc:	48 89 c7             	mov    %rax,%rdi
  4022cf:	b8 00 00 00 00       	mov    $0x0,%eax
  4022d4:	e8 a7 ed ff ff       	call   401080 <printf@plt>
  
printf("%ld chunks\n", chunkslen);
  4022d9:	48 8b 85 08 ff ff ff 	mov    -0xf8(%rbp),%rax
  4022e0:	48 89 c6             	mov    %rax,%rsi
  4022e3:	48 8d 05 b2 1d 00 00 	lea    0x1db2(%rip),%rax        # 40409c <_IO_stdin_used+0x9c>
  4022ea:	48 89 c7             	mov    %rax,%rdi
  4022ed:	b8 00 00 00 00       	mov    $0x0,%eax
  4022f2:	e8 89 ed ff ff       	call   401080 <printf@plt>
 // for (int i = 0; i < worksize; i++) {
   // works[i].taskindex = 2;
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  4022f7:	c7 85 c4 fe ff ff 00 00 00 00 	movl   $0x0,-0x13c(%rbp)
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  402301:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402307:	48 98                	cltq
  402309:	be 04 00 00 00       	mov    $0x4,%esi
  40230e:	48 89 c7             	mov    %rax,%rdi
  402311:	e8 ba ed ff ff       	call   4010d0 <calloc@plt>
  402316:	48 89 85 60 ff ff ff 	mov    %rax,-0xa0(%rbp)
  
  long * globalwrite;
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  40231d:	48 8d 85 e0 fe ff ff 	lea    -0x120(%rbp),%rax
  402324:	ba 00 02 00 00       	mov    $0x200,%edx
  402329:	be 80 00 00 00       	mov    $0x80,%esi
  40232e:	48 89 c7             	mov    %rax,%rdi
  402331:	e8 ca ed ff ff       	call   401100 <posix_memalign@plt>
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  402336:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40233c:	48 98                	cltq
  40233e:	be 0c 00 00 00       	mov    $0xc,%esi
  402343:	48 89 c7             	mov    %rax,%rdi
  402346:	e8 85 ed ff ff       	call   4010d0 <calloc@plt>
  40234b:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
  data[0].works = works;
  402352:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402359:	48 8b 95 40 ff ff ff 	mov    -0xc0(%rbp),%rdx
  402360:	48 89 50 70          	mov    %rdx,0x70(%rax)
  int accesssize = 100000000;
  402364:	c7 85 d8 fe ff ff 00 e1 f5 05 	movl   $0x5f5e100,-0x128(%rbp)
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  40236e:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  402374:	48 98                	cltq
  402376:	be 14 00 00 00       	mov    $0x14,%esi
  40237b:	48 89 c7             	mov    %rax,%rdi
  40237e:	e8 4d ed ff ff       	call   4010d0 <calloc@plt>
  402383:	48 89 85 70 ff ff ff 	mov    %rax,-0x90(%rbp)
  struct Access * writes = calloc(accesssize, sizeof(struct Access));
  40238a:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  402390:	48 98                	cltq
  402392:	be 14 00 00 00       	mov    $0x14,%esi
  402397:	48 89 c7             	mov    %rax,%rdi
  40239a:	e8 31 ed ff ff       	call   4010d0 <calloc@plt>
  40239f:	48 89 85 78 ff ff ff 	mov    %rax,-0x88(%rbp)

  struct Scheduler * scheduler = calloc(1, sizeof(struct Scheduler));
  4023a6:	be 08 00 00 00       	mov    $0x8,%esi
  4023ab:	bf 01 00 00 00       	mov    $0x1,%edi
  4023b0:	e8 1b ed ff ff       	call   4010d0 <calloc@plt>
  4023b5:	48 89 45 80          	mov    %rax,-0x80(%rbp)

  
  
  for (int x = 0; x < threadsize ; x++) {
  4023b9:	c7 85 c8 fe ff ff 00 00 00 00 	movl   $0x0,-0x138(%rbp)
  4023c3:	e9 e8 06 00 00       	jmp    402ab0 <main+0xa44>
    
    struct Coroutine * cos = calloc(10, sizeof(struct Coroutine));
  4023c8:	be 20 00 00 00       	mov    $0x20,%esi
  4023cd:	bf 0a 00 00 00       	mov    $0xa,%edi
  4023d2:	e8 f9 ec ff ff       	call   4010d0 <calloc@plt>
  4023d7:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
    
    data[x].coroutines = cos;
  4023db:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4023e1:	48 98                	cltq
  4023e3:	48 c1 e0 0a          	shl    $0xa,%rax
  4023e7:	48 89 c2             	mov    %rax,%rdx
  4023ea:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4023f1:	48 01 c2             	add    %rax,%rdx
  4023f4:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4023f8:	48 89 82 c0 03 00 00 	mov    %rax,0x3c0(%rdx)
    for (int y = 0; y < 10; y++ ) {
  4023ff:	c7 85 cc fe ff ff 00 00 00 00 	movl   $0x0,-0x134(%rbp)
  402409:	e9 9e 00 00 00       	jmp    4024ac <main+0x440>
      char * stack;
      posix_memalign((void **)&stack, 16, 8016);
  40240e:	48 8d 45 d0          	lea    -0x30(%rbp),%rax
  402412:	ba 50 1f 00 00       	mov    $0x1f50,%edx
  402417:	be 10 00 00 00       	mov    $0x10,%esi
  40241c:	48 89 c7             	mov    %rax,%rdi
  40241f:	e8 dc ec ff ff       	call   401100 <posix_memalign@plt>
      
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
  402424:	be 04 00 00 00       	mov    $0x4,%esi
  402429:	bf 01 00 00 00       	mov    $0x1,%edi
  40242e:	e8 9d ec ff ff       	call   4010d0 <calloc@plt>
  402433:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
      cos[y].data = codata; 
  402437:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  40243d:	48 98                	cltq
  40243f:	48 c1 e0 05          	shl    $0x5,%rax
  402443:	48 89 c2             	mov    %rax,%rdx
  402446:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40244a:	48 01 c2             	add    %rax,%rdx
  40244d:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  402451:	48 89 42 18          	mov    %rax,0x18(%rdx)
      codata->running = 1;
  402455:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  402459:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
      cos[y].eip = (uint64_t)coroutine_func;
  40245f:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  402465:	48 98                	cltq
  402467:	48 c1 e0 05          	shl    $0x5,%rax
  40246b:	48 89 c2             	mov    %rax,%rdx
  40246e:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  402472:	48 01 d0             	add    %rdx,%rax
  402475:	48 c7 c2 1d 12 40 00 	mov    $0x40121d,%rdx
  40247c:	48 89 50 10          	mov    %rdx,0x10(%rax)
      cos[y].rsp = stack + 8016;
  402480:	48 8b 45 d0          	mov    -0x30(%rbp),%rax
  402484:	48 8d 90 50 1f 00 00 	lea    0x1f50(%rax),%rdx
  40248b:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  402491:	48 98                	cltq
  402493:	48 c1 e0 05          	shl    $0x5,%rax
  402497:	48 89 c1             	mov    %rax,%rcx
  40249a:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40249e:	48 01 c8             	add    %rcx,%rax
  4024a1:	48 89 50 08          	mov    %rdx,0x8(%rax)
    for (int y = 0; y < 10; y++ ) {
  4024a5:	83 85 cc fe ff ff 01 	addl   $0x1,-0x134(%rbp)
  4024ac:	83 bd cc fe ff ff 09 	cmpl   $0x9,-0x134(%rbp)
  4024b3:	0f 8e 55 ff ff ff    	jle    40240e <main+0x3a2>
    }
    data[x].scheduler = scheduler;  
  4024b9:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4024bf:	48 98                	cltq
  4024c1:	48 c1 e0 0a          	shl    $0xa,%rax
  4024c5:	48 89 c2             	mov    %rax,%rdx
  4024c8:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4024cf:	48 01 c2             	add    %rax,%rdx
  4024d2:	48 8b 45 80          	mov    -0x80(%rbp),%rax
  4024d6:	48 89 82 c8 03 00 00 	mov    %rax,0x3c8(%rdx)
    data[x].reads = reads;
  4024dd:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4024e3:	48 98                	cltq
  4024e5:	48 c1 e0 0a          	shl    $0xa,%rax
  4024e9:	48 89 c2             	mov    %rax,%rdx
  4024ec:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4024f3:	48 01 c2             	add    %rax,%rdx
  4024f6:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
  4024fd:	48 89 82 a0 03 00 00 	mov    %rax,0x3a0(%rdx)
    data[x].writes = writes; 
  402504:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40250a:	48 98                	cltq
  40250c:	48 c1 e0 0a          	shl    $0xa,%rax
  402510:	48 89 c2             	mov    %rax,%rdx
  402513:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40251a:	48 01 c2             	add    %rax,%rdx
  40251d:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  402524:	48 89 82 a8 03 00 00 	mov    %rax,0x3a8(%rdx)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t)); 
  40252b:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402531:	48 98                	cltq
  402533:	48 c1 e0 0a          	shl    $0xa,%rax
  402537:	48 89 c2             	mov    %rax,%rdx
  40253a:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402541:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  402545:	be 80 00 00 00       	mov    $0x80,%esi
  40254a:	bf 01 00 00 00       	mov    $0x1,%edi
  40254f:	e8 7c eb ff ff       	call   4010d0 <calloc@plt>
  402554:	48 89 43 78          	mov    %rax,0x78(%rbx)
    CPU_SET(cpu += 1, data[x].cpu_set);
  402558:	83 85 c4 fe ff ff 01 	addl   $0x1,-0x13c(%rbp)
  40255f:	8b 85 c4 fe ff ff    	mov    -0x13c(%rbp),%eax
  402565:	48 98                	cltq
  402567:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  40256b:	48 81 7d b0 ff 03 00 00 	cmpq   $0x3ff,-0x50(%rbp)
  402573:	77 78                	ja     4025ed <main+0x581>
  402575:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40257b:	48 98                	cltq
  40257d:	48 c1 e0 0a          	shl    $0xa,%rax
  402581:	48 89 c2             	mov    %rax,%rdx
  402584:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40258b:	48 01 d0             	add    %rdx,%rax
  40258e:	48 8b 40 78          	mov    0x78(%rax),%rax
  402592:	48 89 c1             	mov    %rax,%rcx
  402595:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
  402599:	48 c1 e8 06          	shr    $0x6,%rax
  40259d:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4025a5:	48 01 ca             	add    %rcx,%rdx
  4025a8:	48 8b 32             	mov    (%rdx),%rsi
  4025ab:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
  4025af:	83 e2 3f             	and    $0x3f,%edx
  4025b2:	bf 01 00 00 00       	mov    $0x1,%edi
  4025b7:	89 d1                	mov    %edx,%ecx
  4025b9:	48 d3 e7             	shl    %cl,%rdi
  4025bc:	48 89 f9             	mov    %rdi,%rcx
  4025bf:	8b 95 c8 fe ff ff    	mov    -0x138(%rbp),%edx
  4025c5:	48 63 d2             	movslq %edx,%rdx
  4025c8:	48 89 d7             	mov    %rdx,%rdi
  4025cb:	48 c1 e7 0a          	shl    $0xa,%rdi
  4025cf:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4025d6:	48 01 fa             	add    %rdi,%rdx
  4025d9:	48 8b 52 78          	mov    0x78(%rdx),%rdx
  4025dd:	48 c1 e0 03          	shl    $0x3,%rax
  4025e1:	48 01 d0             	add    %rdx,%rax
  4025e4:	48 09 ce             	or     %rcx,%rsi
  4025e7:	48 89 f2             	mov    %rsi,%rdx
  4025ea:	48 89 10             	mov    %rdx,(%rax)
    printf("assigning thread %d to cpu %d\n", x, cpu);
  4025ed:	8b 95 c4 fe ff ff    	mov    -0x13c(%rbp),%edx
  4025f3:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4025f9:	89 c6                	mov    %eax,%esi
  4025fb:	48 8d 05 a6 1a 00 00 	lea    0x1aa6(%rip),%rax        # 4040a8 <_IO_stdin_used+0xa8>
  402602:	48 89 c7             	mov    %rax,%rdi
  402605:	b8 00 00 00 00       	mov    $0x0,%eax
  40260a:	e8 71 ea ff ff       	call   401080 <printf@plt>
    data[x].bucketstart = x * buckets ;
  40260f:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402615:	48 98                	cltq
  402617:	48 c1 e0 0a          	shl    $0xa,%rax
  40261b:	48 89 c2             	mov    %rax,%rdx
  40261e:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402625:	48 01 c2             	add    %rax,%rdx
  402628:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40262e:	0f af 85 90 fe ff ff 	imul   -0x170(%rbp),%eax
  402635:	89 82 98 00 00 00    	mov    %eax,0x98(%rdx)
    data[x].globalwrite = globalwrite;
  40263b:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402641:	48 98                	cltq
  402643:	48 c1 e0 0a          	shl    $0xa,%rax
  402647:	48 89 c2             	mov    %rax,%rdx
  40264a:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402651:	48 01 c2             	add    %rax,%rdx
  402654:	48 8b 85 e0 fe ff ff 	mov    -0x120(%rbp),%rax
  40265b:	48 89 82 80 03 00 00 	mov    %rax,0x380(%rdx)
    data[x].loglevel = debug;
  402662:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402668:	48 98                	cltq
  40266a:	48 c1 e0 0a          	shl    $0xa,%rax
  40266e:	48 89 c2             	mov    %rax,%rdx
  402671:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402678:	48 01 c2             	add    %rax,%rdx
  40267b:	8b 85 a0 fe ff ff    	mov    -0x160(%rbp),%eax
  402681:	89 82 80 00 00 00    	mov    %eax,0x80(%rdx)
    data[x].running = 2;
  402687:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40268d:	48 98                	cltq
  40268f:	48 c1 e0 0a          	shl    $0xa,%rax
  402693:	48 89 c2             	mov    %rax,%rdx
  402696:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40269d:	48 01 d0             	add    %rdx,%rax
  4026a0:	c7 40 5c 02 00 00 00 	movl   $0x2,0x5c(%rax)
    data[x].threadindex = x;
  4026a7:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026ad:	48 98                	cltq
  4026af:	48 c1 e0 0a          	shl    $0xa,%rax
  4026b3:	48 89 c2             	mov    %rax,%rdx
  4026b6:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026bd:	48 01 c2             	add    %rax,%rdx
  4026c0:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026c6:	89 42 64             	mov    %eax,0x64(%rdx)
    data[x].worksize = worksize;
  4026c9:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026cf:	48 98                	cltq
  4026d1:	48 c1 e0 0a          	shl    $0xa,%rax
  4026d5:	48 89 c2             	mov    %rax,%rdx
  4026d8:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026df:	48 01 d0             	add    %rdx,%rax
  4026e2:	48 8b 95 10 ff ff ff 	mov    -0xf0(%rbp),%rdx
  4026e9:	89 50 60             	mov    %edx,0x60(%rax)
    
    data[x].availables = buckets;
  4026ec:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026f2:	48 98                	cltq
  4026f4:	48 c1 e0 0a          	shl    $0xa,%rax
  4026f8:	48 89 c2             	mov    %rax,%rdx
  4026fb:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402702:	48 01 c2             	add    %rax,%rdx
  402705:	8b 85 90 fe ff ff    	mov    -0x170(%rbp),%eax
  40270b:	89 82 94 00 00 00    	mov    %eax,0x94(%rdx)
    data[x].threadsize = threadsize;
  402711:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402717:	48 98                	cltq
  402719:	48 c1 e0 0a          	shl    $0xa,%rax
  40271d:	48 89 c2             	mov    %rax,%rdx
  402720:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402727:	48 01 c2             	add    %rax,%rdx
  40272a:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402730:	89 42 68             	mov    %eax,0x68(%rdx)
    data[x].readies = readies;
  402733:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402739:	48 98                	cltq
  40273b:	48 c1 e0 0a          	shl    $0xa,%rax
  40273f:	48 89 c2             	mov    %rax,%rdx
  402742:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402749:	48 01 c2             	add    %rax,%rdx
  40274c:	48 8b 85 60 ff ff ff 	mov    -0xa0(%rbp),%rax
  402753:	48 89 42 20          	mov    %rax,0x20(%rdx)
    data[x].readies[x] = 0;
  402757:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40275d:	48 98                	cltq
  40275f:	48 c1 e0 0a          	shl    $0xa,%rax
  402763:	48 89 c2             	mov    %rax,%rdx
  402766:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40276d:	48 01 d0             	add    %rdx,%rax
  402770:	48 8b 50 20          	mov    0x20(%rax),%rdx
  402774:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40277a:	48 98                	cltq
  40277c:	48 c1 e0 02          	shl    $0x2,%rax
  402780:	48 01 d0             	add    %rdx,%rax
  402783:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    data[x].buckets = buckets;
  402789:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40278f:	48 98                	cltq
  402791:	48 c1 e0 0a          	shl    $0xa,%rax
  402795:	48 89 c2             	mov    %rax,%rdx
  402798:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40279f:	48 01 c2             	add    %rax,%rdx
  4027a2:	8b 85 90 fe ff ff    	mov    -0x170(%rbp),%eax
  4027a8:	89 82 90 00 00 00    	mov    %eax,0x90(%rdx)
    data[x].main = &data[0];
  4027ae:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027b4:	48 98                	cltq
  4027b6:	48 c1 e0 0a          	shl    $0xa,%rax
  4027ba:	48 89 c2             	mov    %rax,%rdx
  4027bd:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027c4:	48 01 c2             	add    %rax,%rdx
  4027c7:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027ce:	48 89 42 28          	mov    %rax,0x28(%rdx)
    data[x].threads = data;
  4027d2:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027d8:	48 98                	cltq
  4027da:	48 c1 e0 0a          	shl    $0xa,%rax
  4027de:	48 89 c2             	mov    %rax,%rdx
  4027e1:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027e8:	48 01 c2             	add    %rax,%rdx
  4027eb:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027f2:	48 89 42 30          	mov    %rax,0x30(%rdx)
    
    data[x].read = 0;
  4027f6:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027fc:	48 98                	cltq
  4027fe:	48 c1 e0 0a          	shl    $0xa,%rax
  402802:	48 89 c2             	mov    %rax,%rdx
  402805:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40280c:	48 01 d0             	add    %rdx,%rax
  40280f:	48 c7 00 00 00 00 00 	movq   $0x0,(%rax)
    data[x].write = worksize;
  402816:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40281c:	48 98                	cltq
  40281e:	48 c1 e0 0a          	shl    $0xa,%rax
  402822:	48 89 c2             	mov    %rax,%rdx
  402825:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40282c:	48 01 c2             	add    %rax,%rdx
  40282f:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  402836:	48 89 42 08          	mov    %rax,0x8(%rdx)
    data[x].readcursor = threadsize - 1;
  40283a:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402840:	48 98                	cltq
  402842:	48 c1 e0 0a          	shl    $0xa,%rax
  402846:	48 89 c2             	mov    %rax,%rdx
  402849:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402850:	48 01 d0             	add    %rdx,%rax
  402853:	8b 95 98 fe ff ff    	mov    -0x168(%rbp),%edx
  402859:	83 ea 01             	sub    $0x1,%edx
  40285c:	89 90 00 02 00 00    	mov    %edx,0x200(%rax)
    data[x].writecursor = 0;
  402862:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402868:	48 98                	cltq
  40286a:	48 c1 e0 0a          	shl    $0xa,%rax
  40286e:	48 89 c2             	mov    %rax,%rdx
  402871:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402878:	48 01 d0             	add    %rdx,%rax
  40287b:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    data[x].freelist = freelist;
  402885:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40288b:	48 98                	cltq
  40288d:	48 c1 e0 0a          	shl    $0xa,%rax
  402891:	48 89 c2             	mov    %rax,%rdx
  402894:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40289b:	48 01 c2             	add    %rax,%rdx
  40289e:	48 8b 85 58 ff ff ff 	mov    -0xa8(%rbp),%rax
  4028a5:	48 89 82 a0 00 00 00 	mov    %rax,0xa0(%rdx)
    data[x].chunksize = chunksize;
  4028ac:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028b2:	48 98                	cltq
  4028b4:	48 c1 e0 0a          	shl    $0xa,%rax
  4028b8:	48 89 c2             	mov    %rax,%rdx
  4028bb:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4028c2:	48 01 c2             	add    %rax,%rdx
  4028c5:	48 8b 85 38 ff ff ff 	mov    -0xc8(%rbp),%rax
  4028cc:	48 89 82 c0 00 00 00 	mov    %rax,0xc0(%rdx)
    data[x].chunkslen = chunkslen;
  4028d3:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028d9:	48 98                	cltq
  4028db:	48 c1 e0 0a          	shl    $0xa,%rax
  4028df:	48 89 c2             	mov    %rax,%rdx
  4028e2:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4028e9:	48 01 c2             	add    %rax,%rdx
  4028ec:	48 8b 85 08 ff ff ff 	mov    -0xf8(%rbp),%rax
  4028f3:	48 89 82 b8 00 00 00 	mov    %rax,0xb8(%rdx)
    data[x].newmask = 0;
  4028fa:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402900:	48 98                	cltq
  402902:	48 c1 e0 0a          	shl    $0xa,%rax
  402906:	48 89 c2             	mov    %rax,%rdx
  402909:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402910:	48 01 d0             	add    %rdx,%rax
  402913:	c7 80 c8 00 00 00 00 00 00 00 	movl   $0x0,0xc8(%rax)
    data[x].prevread = threadsize;
  40291d:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402923:	48 98                	cltq
  402925:	48 c1 e0 0a          	shl    $0xa,%rax
  402929:	48 89 c2             	mov    %rax,%rdx
  40292c:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402933:	48 01 c2             	add    %rax,%rdx
  402936:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40293c:	48 98                	cltq
  40293e:	48 89 82 08 03 00 00 	mov    %rax,0x308(%rdx)
    data[x].prevwrite = threadsize;
  402945:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40294b:	48 98                	cltq
  40294d:	48 c1 e0 0a          	shl    $0xa,%rax
  402951:	48 89 c2             	mov    %rax,%rdx
  402954:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40295b:	48 01 c2             	add    %rax,%rdx
  40295e:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402964:	48 98                	cltq
  402966:	48 89 82 10 03 00 00 	mov    %rax,0x310(%rdx)
    data[x].mystream = 1 + (x / 4);
  40296d:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402973:	8d 50 03             	lea    0x3(%rax),%edx
  402976:	85 c0                	test   %eax,%eax
  402978:	0f 48 c2             	cmovs  %edx,%eax
  40297b:	c1 f8 02             	sar    $0x2,%eax
  40297e:	89 c2                	mov    %eax,%edx
  402980:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402986:	48 98                	cltq
  402988:	48 c1 e0 0a          	shl    $0xa,%rax
  40298c:	48 89 c1             	mov    %rax,%rcx
  40298f:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402996:	48 01 c8             	add    %rcx,%rax
  402999:	83 c2 01             	add    $0x1,%edx
  40299c:	89 90 8c 03 00 00    	mov    %edx,0x38c(%rax)
    data[x].thiswrite = threadsize;
  4029a2:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4029a8:	48 98                	cltq
  4029aa:	48 c1 e0 0a          	shl    $0xa,%rax
  4029ae:	48 89 c2             	mov    %rax,%rdx
  4029b1:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4029b8:	48 01 c2             	add    %rax,%rdx
  4029bb:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4029c1:	89 82 28 03 00 00    	mov    %eax,0x328(%rdx)
    int epochs = 10000000;
  4029c7:	c7 85 dc fe ff ff 80 96 98 00 	movl   $0x989680,-0x124(%rbp)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4029d1:	8b 85 dc fe ff ff    	mov    -0x124(%rbp),%eax
  4029d7:	48 98                	cltq
  4029d9:	8b 95 c8 fe ff ff    	mov    -0x138(%rbp),%edx
  4029df:	48 63 d2             	movslq %edx,%rdx
  4029e2:	48 89 d1             	mov    %rdx,%rcx
  4029e5:	48 c1 e1 0a          	shl    $0xa,%rcx
  4029e9:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4029f0:	48 8d 1c 11          	lea    (%rcx,%rdx,1),%rbx
  4029f4:	be 30 00 00 00       	mov    $0x30,%esi
  4029f9:	48 89 c7             	mov    %rax,%rdi
  4029fc:	e8 cf e6 ff ff       	call   4010d0 <calloc@plt>
  402a01:	48 89 83 18 03 00 00 	mov    %rax,0x318(%rbx)
    data[x].epochssize = epochs;
  402a08:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a0e:	48 98                	cltq
  402a10:	48 c1 e0 0a          	shl    $0xa,%rax
  402a14:	48 89 c2             	mov    %rax,%rdx
  402a17:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a1e:	48 01 c2             	add    %rax,%rdx
  402a21:	8b 85 dc fe ff ff    	mov    -0x124(%rbp),%eax
  402a27:	89 82 20 03 00 00    	mov    %eax,0x320(%rdx)
    data[x].globalread = globalread;
  402a2d:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a33:	48 98                	cltq
  402a35:	48 c1 e0 0a          	shl    $0xa,%rax
  402a39:	48 89 c2             	mov    %rax,%rdx
  402a3c:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a43:	48 01 c2             	add    %rax,%rdx
  402a46:	48 8b 85 68 ff ff ff 	mov    -0x98(%rbp),%rax
  402a4d:	48 89 82 48 03 00 00 	mov    %rax,0x348(%rdx)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  402a54:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a5a:	48 98                	cltq
  402a5c:	48 c1 e0 0a          	shl    $0xa,%rax
  402a60:	48 89 c2             	mov    %rax,%rdx
  402a63:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a6a:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  402a6e:	be 30 00 00 00       	mov    $0x30,%esi
  402a73:	bf 10 27 00 00       	mov    $0x2710,%edi
  402a78:	e8 53 e6 ff ff       	call   4010d0 <calloc@plt>
  402a7d:	48 89 83 30 03 00 00 	mov    %rax,0x330(%rbx)
    data[x].accesssize = accesssize;
  402a84:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a8a:	48 98                	cltq
  402a8c:	48 c1 e0 0a          	shl    $0xa,%rax
  402a90:	48 89 c2             	mov    %rax,%rdx
  402a93:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a9a:	48 01 c2             	add    %rax,%rdx
  402a9d:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  402aa3:	89 82 b8 03 00 00    	mov    %eax,0x3b8(%rdx)
  for (int x = 0; x < threadsize ; x++) {
  402aa9:	83 85 c8 fe ff ff 01 	addl   $0x1,-0x138(%rbp)
  402ab0:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402ab6:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402abc:	0f 8c 06 f9 ff ff    	jl     4023c8 <main+0x35c>
  } 
  
  for (int x = 0; x < threadsize ; x++) {
  402ac2:	c7 85 d0 fe ff ff 00 00 00 00 	movl   $0x0,-0x130(%rbp)
  402acc:	e9 b8 00 00 00       	jmp    402b89 <main+0xb1d>
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  402ad1:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402ad7:	48 98                	cltq
  402ad9:	48 c1 e0 0a          	shl    $0xa,%rax
  402add:	48 89 c2             	mov    %rax,%rdx
  402ae0:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402ae7:	48 01 c2             	add    %rax,%rdx
  402aea:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402af0:	48 63 c8             	movslq %eax,%rcx
  402af3:	48 89 c8             	mov    %rcx,%rax
  402af6:	48 c1 e0 03          	shl    $0x3,%rax
  402afa:	48 29 c8             	sub    %rcx,%rax
  402afd:	48 c1 e0 03          	shl    $0x3,%rax
  402b01:	48 89 c1             	mov    %rax,%rcx
  402b04:	48 8b 85 f0 fe ff ff 	mov    -0x110(%rbp),%rax
  402b0b:	48 8d 34 01          	lea    (%rcx,%rax,1),%rsi
  402b0f:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b15:	48 98                	cltq
  402b17:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
  402b1f:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402b26:	48 01 c8             	add    %rcx,%rax
  402b29:	48 89 d1             	mov    %rdx,%rcx
  402b2c:	48 c7 c2 67 1f 40 00 	mov    $0x401f67,%rdx
  402b33:	48 89 c7             	mov    %rax,%rdi
  402b36:	e8 a5 e5 ff ff       	call   4010e0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  402b3b:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b41:	48 98                	cltq
  402b43:	48 c1 e0 0a          	shl    $0xa,%rax
  402b47:	48 89 c2             	mov    %rax,%rdx
  402b4a:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402b51:	48 01 d0             	add    %rdx,%rax
  402b54:	48 8b 50 78          	mov    0x78(%rax),%rdx
  402b58:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b5e:	48 98                	cltq
  402b60:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
  402b68:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402b6f:	48 01 c8             	add    %rcx,%rax
  402b72:	48 8b 00             	mov    (%rax),%rax
  402b75:	be 08 00 00 00       	mov    $0x8,%esi
  402b7a:	48 89 c7             	mov    %rax,%rdi
  402b7d:	e8 ae e4 ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  402b82:	83 85 d0 fe ff ff 01 	addl   $0x1,-0x130(%rbp)
  402b89:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b8f:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402b95:	0f 8c 36 ff ff ff    	jl     402ad1 <main+0xa65>
  }
  
  struct timespec time = {
  402b9b:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402ba1:	48 98                	cltq
  402ba3:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
  402ba7:	48 c7 45 c8 00 00 00 00 	movq   $0x0,-0x38(%rbp)
    seconds,
    0
  };
  struct timespec rem = {
  402baf:	48 c7 45 d0 00 00 00 00 	movq   $0x0,-0x30(%rbp)
  402bb7:	48 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%rbp)
    0,
    0
  };
  
  nanosleep(&time, &rem);
  402bbf:	48 8d 55 d0          	lea    -0x30(%rbp),%rdx
  402bc3:	48 8d 45 c0          	lea    -0x40(%rbp),%rax
  402bc7:	48 89 d6             	mov    %rdx,%rsi
  402bca:	48 89 c7             	mov    %rax,%rdi
  402bcd:	e8 ce e4 ff ff       	call   4010a0 <nanosleep@plt>
  
  printf("runphased\n");
  402bd2:	48 8d 05 ee 14 00 00 	lea    0x14ee(%rip),%rax        # 4040c7 <_IO_stdin_used+0xc7>
  402bd9:	48 89 c7             	mov    %rax,%rdi
  402bdc:	e8 5f e4 ff ff       	call   401040 <puts@plt>
  for (int x = 0; x < threadsize ; x++) {
  402be1:	c7 85 b8 fe ff ff 00 00 00 00 	movl   $0x0,-0x148(%rbp)
  402beb:	eb 29                	jmp    402c16 <main+0xbaa>
    data[x].running--;
  402bed:	8b 85 b8 fe ff ff    	mov    -0x148(%rbp),%eax
  402bf3:	48 98                	cltq
  402bf5:	48 c1 e0 0a          	shl    $0xa,%rax
  402bf9:	48 89 c2             	mov    %rax,%rdx
  402bfc:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402c03:	48 01 d0             	add    %rdx,%rax
  402c06:	8b 50 5c             	mov    0x5c(%rax),%edx
  402c09:	83 ea 01             	sub    $0x1,%edx
  402c0c:	89 50 5c             	mov    %edx,0x5c(%rax)
  for (int x = 0; x < threadsize ; x++) {
  402c0f:	83 85 b8 fe ff ff 01 	addl   $0x1,-0x148(%rbp)
  402c16:	8b 85 b8 fe ff ff    	mov    -0x148(%rbp),%eax
  402c1c:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402c22:	7c c9                	jl     402bed <main+0xb81>
    
  }
  
 printf("draining\n");
  402c24:	48 8d 05 a6 14 00 00 	lea    0x14a6(%rip),%rax        # 4040d1 <_IO_stdin_used+0xd1>
  402c2b:	48 89 c7             	mov    %rax,%rdi
  402c2e:	e8 0d e4 ff ff       	call   401040 <puts@plt>
 // time.tv_sec = 3;
//nanosleep(&time, &rem);
  for (int x = 0; x < threadsize ; x++) {
  402c33:	c7 85 bc fe ff ff 00 00 00 00 	movl   $0x0,-0x144(%rbp)
  402c3d:	eb 29                	jmp    402c68 <main+0xbfc>
    data[x].running--;
  402c3f:	8b 85 bc fe ff ff    	mov    -0x144(%rbp),%eax
  402c45:	48 98                	cltq
  402c47:	48 c1 e0 0a          	shl    $0xa,%rax
  402c4b:	48 89 c2             	mov    %rax,%rdx
  402c4e:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402c55:	48 01 d0             	add    %rdx,%rax
  402c58:	8b 50 5c             	mov    0x5c(%rax),%edx
  402c5b:	83 ea 01             	sub    $0x1,%edx
  402c5e:	89 50 5c             	mov    %edx,0x5c(%rax)
  for (int x = 0; x < threadsize ; x++) {
  402c61:	83 85 bc fe ff ff 01 	addl   $0x1,-0x144(%rbp)
  402c68:	8b 85 bc fe ff ff    	mov    -0x144(%rbp),%eax
  402c6e:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402c74:	7c c9                	jl     402c3f <main+0xbd3>
  }
  
  //nanosleep(&time, &rem);
  for (int x = 0; x < threadsize; x++) {
  402c76:	c7 85 c0 fe ff ff 00 00 00 00 	movl   $0x0,-0x140(%rbp)
  402c80:	eb 36                	jmp    402cb8 <main+0xc4c>
    void *res;
    pthread_join(thread[x], &res);
  402c82:	8b 85 c0 fe ff ff    	mov    -0x140(%rbp),%eax
  402c88:	48 98                	cltq
  402c8a:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  402c92:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402c99:	48 01 d0             	add    %rdx,%rax
  402c9c:	48 8b 00             	mov    (%rax),%rax
  402c9f:	48 8d 95 e8 fe ff ff 	lea    -0x118(%rbp),%rdx
  402ca6:	48 89 d6             	mov    %rdx,%rsi
  402ca9:	48 89 c7             	mov    %rax,%rdi
  402cac:	e8 5f e4 ff ff       	call   401110 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  402cb1:	83 85 c0 fe ff ff 01 	addl   $0x1,-0x140(%rbp)
  402cb8:	8b 85 c0 fe ff ff    	mov    -0x140(%rbp),%eax
  402cbe:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402cc4:	7c bc                	jl     402c82 <main+0xc16>
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  402cc6:	48 8d 05 0d 14 00 00 	lea    0x140d(%rip),%rax        # 4040da <_IO_stdin_used+0xda>
  402ccd:	48 89 c7             	mov    %rax,%rdi
  402cd0:	e8 6b e3 ff ff       	call   401040 <puts@plt>
  long freq = 0;
  402cd5:	48 c7 85 20 ff ff ff 00 00 00 00 	movq   $0x0,-0xe0(%rbp)
  long sends = 1;
  402ce0:	48 c7 45 88 01 00 00 00 	movq   $0x1,-0x78(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402ce8:	c7 85 a8 fe ff ff 00 00 00 00 	movl   $0x0,-0x158(%rbp)
  402cf2:	eb 5f                	jmp    402d53 <main+0xce7>
    printf("%ld reads\n", data[x].freq);
  402cf4:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402cfa:	48 98                	cltq
  402cfc:	48 c1 e0 0a          	shl    $0xa,%rax
  402d00:	48 89 c2             	mov    %rax,%rdx
  402d03:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402d0a:	48 01 d0             	add    %rdx,%rax
  402d0d:	48 8b 40 48          	mov    0x48(%rax),%rax
  402d11:	48 89 c6             	mov    %rax,%rsi
  402d14:	48 8d 05 d4 13 00 00 	lea    0x13d4(%rip),%rax        # 4040ef <_IO_stdin_used+0xef>
  402d1b:	48 89 c7             	mov    %rax,%rdi
  402d1e:	b8 00 00 00 00       	mov    $0x0,%eax
  402d23:	e8 58 e3 ff ff       	call   401080 <printf@plt>
    freq += data[x].freq;
  402d28:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d2e:	48 98                	cltq
  402d30:	48 c1 e0 0a          	shl    $0xa,%rax
  402d34:	48 89 c2             	mov    %rax,%rdx
  402d37:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402d3e:	48 01 d0             	add    %rdx,%rax
  402d41:	48 8b 40 48          	mov    0x48(%rax),%rax
  402d45:	48 01 85 20 ff ff ff 	add    %rax,-0xe0(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402d4c:	83 85 a8 fe ff ff 01 	addl   $0x1,-0x158(%rbp)
  402d53:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d59:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402d5f:	7c 93                	jl     402cf4 <main+0xc88>
  }
  printf("freq: %ld\n", freq/ seconds);
  402d61:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402d67:	48 63 d8             	movslq %eax,%rbx
  402d6a:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402d71:	48 99                	cqto
  402d73:	48 f7 fb             	idiv   %rbx
  402d76:	48 89 c6             	mov    %rax,%rsi
  402d79:	48 8d 05 7a 13 00 00 	lea    0x137a(%rip),%rax        # 4040fa <_IO_stdin_used+0xfa>
  402d80:	48 89 c7             	mov    %rax,%rdi
  402d83:	b8 00 00 00 00       	mov    $0x0,%eax
  402d88:	e8 f3 e2 ff ff       	call   401080 <printf@plt>
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  402d8d:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402d94:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  402d99:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402d9f:	48 63 da             	movslq %edx,%rbx
  402da2:	48 99                	cqto
  402da4:	48 f7 fb             	idiv   %rbx
  402da7:	48 89 c6             	mov    %rax,%rsi
  402daa:	48 8d 05 54 13 00 00 	lea    0x1354(%rip),%rax        # 404105 <_IO_stdin_used+0x105>
  402db1:	48 89 c7             	mov    %rax,%rdi
  402db4:	b8 00 00 00 00       	mov    $0x0,%eax
  402db9:	e8 c2 e2 ff ff       	call   401080 <printf@plt>
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  402dbe:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402dc4:	48 63 d8             	movslq %eax,%rbx
  402dc7:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402dce:	48 99                	cqto
  402dd0:	48 f7 fb             	idiv   %rbx
  402dd3:	48 89 c3             	mov    %rax,%rbx
  402dd6:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402ddb:	48 99                	cqto
  402ddd:	48 f7 fb             	idiv   %rbx
  402de0:	48 89 c6             	mov    %rax,%rsi
  402de3:	48 8d 05 29 13 00 00 	lea    0x1329(%rip),%rax        # 404113 <_IO_stdin_used+0x113>
  402dea:	48 89 c7             	mov    %rax,%rdi
  402ded:	b8 00 00 00 00       	mov    $0x0,%eax
  402df2:	e8 89 e2 ff ff       	call   401080 <printf@plt>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  402df7:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402dfd:	48 63 d8             	movslq %eax,%rbx
  402e00:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402e07:	48 99                	cqto
  402e09:	48 f7 fb             	idiv   %rbx
  402e0c:	48 89 c3             	mov    %rax,%rbx
  402e0f:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402e14:	48 99                	cqto
  402e16:	48 f7 fb             	idiv   %rbx
  402e19:	48 99                	cqto
  402e1b:	48 f7 7d 88          	idivq  -0x78(%rbp)
  402e1f:	48 89 c6             	mov    %rax,%rsi
  402e22:	48 8d 05 fe 12 00 00 	lea    0x12fe(%rip),%rax        # 404127 <_IO_stdin_used+0x127>
  402e29:	48 89 c7             	mov    %rax,%rdi
  402e2c:	b8 00 00 00 00       	mov    $0x0,%eax
  402e31:	e8 4a e2 ff ff       	call   401080 <printf@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  402e36:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402e3d:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  402e42:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402e48:	48 63 da             	movslq %edx,%rbx
  402e4b:	48 99                	cqto
  402e4d:	48 f7 fb             	idiv   %rbx
  402e50:	48 89 c3             	mov    %rax,%rbx
  402e53:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402e58:	48 99                	cqto
  402e5a:	48 f7 fb             	idiv   %rbx
  402e5d:	48 89 c6             	mov    %rax,%rsi
  402e60:	48 8d 05 de 12 00 00 	lea    0x12de(%rip),%rax        # 404145 <_IO_stdin_used+0x145>
  402e67:	48 89 c7             	mov    %rax,%rdi
  402e6a:	b8 00 00 00 00       	mov    $0x0,%eax
  402e6f:	e8 0c e2 ff ff       	call   401080 <printf@plt>
  
  long goods = 0;
  402e74:	48 c7 85 28 ff ff ff 00 00 00 00 	movq   $0x0,-0xd8(%rbp)

  for (int x = 0; x < threadsize; x++) {
  402e7f:	c7 85 ac fe ff ff 00 00 00 00 	movl   $0x0,-0x154(%rbp)
  402e89:	eb 65                	jmp    402ef0 <main+0xe84>
    printf("%ld successreads\n", data[x].successreads);
  402e8b:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402e91:	48 98                	cltq
  402e93:	48 c1 e0 0a          	shl    $0xa,%rax
  402e97:	48 89 c2             	mov    %rax,%rdx
  402e9a:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402ea1:	48 01 d0             	add    %rdx,%rax
  402ea4:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  402eab:	48 89 c6             	mov    %rax,%rsi
  402eae:	48 8d 05 a3 12 00 00 	lea    0x12a3(%rip),%rax        # 404158 <_IO_stdin_used+0x158>
  402eb5:	48 89 c7             	mov    %rax,%rdi
  402eb8:	b8 00 00 00 00       	mov    $0x0,%eax
  402ebd:	e8 be e1 ff ff       	call   401080 <printf@plt>
    goods += data[x].successreads;
  402ec2:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402ec8:	48 98                	cltq
  402eca:	48 c1 e0 0a          	shl    $0xa,%rax
  402ece:	48 89 c2             	mov    %rax,%rdx
  402ed1:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402ed8:	48 01 d0             	add    %rdx,%rax
  402edb:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  402ee2:	48 01 85 28 ff ff ff 	add    %rax,-0xd8(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402ee9:	83 85 ac fe ff ff 01 	addl   $0x1,-0x154(%rbp)
  402ef0:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402ef6:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402efc:	7c 8d                	jl     402e8b <main+0xe1f>
  }
  
  long freq_writes = 0;
  402efe:	48 c7 85 30 ff ff ff 00 00 00 00 	movq   $0x0,-0xd0(%rbp)
  
  for (int x = 0; x < threadsize; x++) {
  402f09:	c7 85 b0 fe ff ff 00 00 00 00 	movl   $0x0,-0x150(%rbp)
  402f13:	eb 5f                	jmp    402f74 <main+0xf08>
    freq_writes += data[x].freq_writes;
  402f15:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f1b:	48 98                	cltq
  402f1d:	48 c1 e0 0a          	shl    $0xa,%rax
  402f21:	48 89 c2             	mov    %rax,%rdx
  402f24:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402f2b:	48 01 d0             	add    %rdx,%rax
  402f2e:	48 8b 40 50          	mov    0x50(%rax),%rax
  402f32:	48 01 85 30 ff ff ff 	add    %rax,-0xd0(%rbp)
    printf("%ld writes\n", data[x].freq_writes);
  402f39:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f3f:	48 98                	cltq
  402f41:	48 c1 e0 0a          	shl    $0xa,%rax
  402f45:	48 89 c2             	mov    %rax,%rdx
  402f48:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402f4f:	48 01 d0             	add    %rdx,%rax
  402f52:	48 8b 40 50          	mov    0x50(%rax),%rax
  402f56:	48 89 c6             	mov    %rax,%rsi
  402f59:	48 8d 05 0a 12 00 00 	lea    0x120a(%rip),%rax        # 40416a <_IO_stdin_used+0x16a>
  402f60:	48 89 c7             	mov    %rax,%rdi
  402f63:	b8 00 00 00 00       	mov    $0x0,%eax
  402f68:	e8 13 e1 ff ff       	call   401080 <printf@plt>
  for (int x = 0; x < threadsize; x++) {
  402f6d:	83 85 b0 fe ff ff 01 	addl   $0x1,-0x150(%rbp)
  402f74:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f7a:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402f80:	7c 93                	jl     402f15 <main+0xea9>
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  402f82:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402f88:	48 63 d8             	movslq %eax,%rbx
  402f8b:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402f92:	48 99                	cqto
  402f94:	48 f7 fb             	idiv   %rbx
  402f97:	48 89 c6             	mov    %rax,%rsi
  402f9a:	48 8d 05 d5 11 00 00 	lea    0x11d5(%rip),%rax        # 404176 <_IO_stdin_used+0x176>
  402fa1:	48 89 c7             	mov    %rax,%rdi
  402fa4:	b8 00 00 00 00       	mov    $0x0,%eax
  402fa9:	e8 d2 e0 ff ff       	call   401080 <printf@plt>

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  402fae:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402fb5:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  402fba:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402fc0:	48 63 da             	movslq %edx,%rbx
  402fc3:	48 99                	cqto
  402fc5:	48 f7 fb             	idiv   %rbx
  402fc8:	48 89 c6             	mov    %rax,%rsi
  402fcb:	48 8d 05 b6 11 00 00 	lea    0x11b6(%rip),%rax        # 404188 <_IO_stdin_used+0x188>
  402fd2:	48 89 c7             	mov    %rax,%rdi
  402fd5:	b8 00 00 00 00       	mov    $0x0,%eax
  402fda:	e8 a1 e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  402fdf:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402fe5:	48 63 d8             	movslq %eax,%rbx
  402fe8:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402fef:	48 99                	cqto
  402ff1:	48 f7 fb             	idiv   %rbx
  402ff4:	48 89 c3             	mov    %rax,%rbx
  402ff7:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402ffc:	48 99                	cqto
  402ffe:	48 f7 fb             	idiv   %rbx
  403001:	48 89 c6             	mov    %rax,%rsi
  403004:	48 8d 05 95 11 00 00 	lea    0x1195(%rip),%rax        # 4041a0 <_IO_stdin_used+0x1a0>
  40300b:	48 89 c7             	mov    %rax,%rdi
  40300e:	b8 00 00 00 00       	mov    $0x0,%eax
  403013:	e8 68 e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes per thread latency: %ld\n", (1000000000/(freq_writes / seconds)) / sends);
  403018:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  40301e:	48 63 d8             	movslq %eax,%rbx
  403021:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  403028:	48 99                	cqto
  40302a:	48 f7 fb             	idiv   %rbx
  40302d:	48 89 c3             	mov    %rax,%rbx
  403030:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  403035:	48 99                	cqto
  403037:	48 f7 fb             	idiv   %rbx
  40303a:	48 99                	cqto
  40303c:	48 f7 7d 88          	idivq  -0x78(%rbp)
  403040:	48 89 c6             	mov    %rax,%rsi
  403043:	48 8d 05 76 11 00 00 	lea    0x1176(%rip),%rax        # 4041c0 <_IO_stdin_used+0x1c0>
  40304a:	48 89 c7             	mov    %rax,%rdi
  40304d:	b8 00 00 00 00       	mov    $0x0,%eax
  403052:	e8 29 e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * sends) / seconds));
  403057:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  40305e:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  403063:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  403069:	48 63 da             	movslq %edx,%rbx
  40306c:	48 99                	cqto
  40306e:	48 f7 fb             	idiv   %rbx
  403071:	48 89 c3             	mov    %rax,%rbx
  403074:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  403079:	48 99                	cqto
  40307b:	48 f7 fb             	idiv   %rbx
  40307e:	48 89 c6             	mov    %rax,%rsi
  403081:	48 8d 05 5d 11 00 00 	lea    0x115d(%rip),%rax        # 4041e5 <_IO_stdin_used+0x1e5>
  403088:	48 89 c7             	mov    %rax,%rdi
  40308b:	b8 00 00 00 00       	mov    $0x0,%eax
  403090:	e8 eb df ff ff       	call   401080 <printf@plt>
    printf("%ldns\n", read.tv_nsec - created.tv_nsec);
    printf("%ldns\n", written.tv_nsec - read.tv_nsec);
    
  }
  */
  printf("writer speed\n");
  403095:	48 8d 05 63 11 00 00 	lea    0x1163(%rip),%rax        # 4041ff <_IO_stdin_used+0x1ff>
  40309c:	48 89 c7             	mov    %rax,%rdi
  40309f:	e8 9c df ff ff       	call   401040 <puts@plt>
  for (int x = 0; x < 1 ;  x++){
  4030a4:	c7 85 b4 fe ff ff 00 00 00 00 	movl   $0x0,-0x14c(%rbp)
  4030ae:	e9 84 02 00 00       	jmp    403337 <main+0x12cb>
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  4030b3:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4030b9:	48 98                	cltq
  4030bb:	48 c1 e0 0a          	shl    $0xa,%rax
  4030bf:	48 89 c2             	mov    %rax,%rdx
  4030c2:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4030c9:	48 01 d0             	add    %rdx,%rax
  4030cc:	48 8b 80 f0 00 00 00 	mov    0xf0(%rax),%rax
  4030d3:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4030d9:	48 63 d2             	movslq %edx,%rdx
  4030dc:	48 89 d1             	mov    %rdx,%rcx
  4030df:	48 c1 e1 0a          	shl    $0xa,%rcx
  4030e3:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4030ea:	48 01 ca             	add    %rcx,%rdx
  4030ed:	48 8b 92 e0 00 00 00 	mov    0xe0(%rdx),%rdx
  4030f4:	48 29 d0             	sub    %rdx,%rax
  4030f7:	48 89 c6             	mov    %rax,%rsi
  4030fa:	48 8d 05 0b 11 00 00 	lea    0x110b(%rip),%rax        # 40420c <_IO_stdin_used+0x20c>
  403101:	48 89 c7             	mov    %rax,%rdi
  403104:	b8 00 00 00 00       	mov    $0x0,%eax
  403109:	e8 72 df ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  40310e:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403114:	48 98                	cltq
  403116:	48 c1 e0 0a          	shl    $0xa,%rax
  40311a:	48 89 c2             	mov    %rax,%rdx
  40311d:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403124:	48 01 d0             	add    %rdx,%rax
  403127:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
  40312e:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  403134:	48 63 d2             	movslq %edx,%rdx
  403137:	48 89 d1             	mov    %rdx,%rcx
  40313a:	48 c1 e1 0a          	shl    $0xa,%rcx
  40313e:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403145:	48 01 ca             	add    %rcx,%rdx
  403148:	48 8b 92 e0 00 00 00 	mov    0xe0(%rdx),%rdx
  40314f:	48 29 d0             	sub    %rdx,%rax
  403152:	48 89 c6             	mov    %rax,%rsi
  403155:	48 8d 05 b0 10 00 00 	lea    0x10b0(%rip),%rax        # 40420c <_IO_stdin_used+0x20c>
  40315c:	48 89 c7             	mov    %rax,%rdi
  40315f:	b8 00 00 00 00       	mov    $0x0,%eax
  403164:	e8 17 df ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  403169:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  40316f:	48 98                	cltq
  403171:	48 c1 e0 0a          	shl    $0xa,%rax
  403175:	48 89 c2             	mov    %rax,%rdx
  403178:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40317f:	48 01 d0             	add    %rdx,%rax
  403182:	48 8b 80 f0 00 00 00 	mov    0xf0(%rax),%rax
  403189:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  40318f:	48 63 d2             	movslq %edx,%rdx
  403192:	48 89 d1             	mov    %rdx,%rcx
  403195:	48 c1 e1 0a          	shl    $0xa,%rcx
  403199:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4031a0:	48 01 ca             	add    %rcx,%rdx
  4031a3:	48 8b 92 00 01 00 00 	mov    0x100(%rdx),%rdx
  4031aa:	48 29 d0             	sub    %rdx,%rax
  4031ad:	48 89 c6             	mov    %rax,%rsi
  4031b0:	48 8d 05 55 10 00 00 	lea    0x1055(%rip),%rax        # 40420c <_IO_stdin_used+0x20c>
  4031b7:	48 89 c7             	mov    %rax,%rdi
  4031ba:	b8 00 00 00 00       	mov    $0x0,%eax
  4031bf:	e8 bc de ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4031c4:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4031ca:	48 98                	cltq
  4031cc:	48 c1 e0 0a          	shl    $0xa,%rax
  4031d0:	48 89 c2             	mov    %rax,%rdx
  4031d3:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4031da:	48 01 d0             	add    %rdx,%rax
  4031dd:	48 8b 80 20 01 00 00 	mov    0x120(%rax),%rax
  4031e4:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4031ea:	48 63 d2             	movslq %edx,%rdx
  4031ed:	48 89 d1             	mov    %rdx,%rcx
  4031f0:	48 c1 e1 0a          	shl    $0xa,%rcx
  4031f4:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4031fb:	48 01 ca             	add    %rcx,%rdx
  4031fe:	48 8b 92 10 01 00 00 	mov    0x110(%rdx),%rdx
  403205:	48 29 d0             	sub    %rdx,%rax
  403208:	48 89 c6             	mov    %rax,%rsi
  40320b:	48 8d 05 fa 0f 00 00 	lea    0xffa(%rip),%rax        # 40420c <_IO_stdin_used+0x20c>
  403212:	48 89 c7             	mov    %rax,%rdi
  403215:	b8 00 00 00 00       	mov    $0x0,%eax
  40321a:	e8 61 de ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  40321f:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403225:	48 98                	cltq
  403227:	48 c1 e0 0a          	shl    $0xa,%rax
  40322b:	48 89 c2             	mov    %rax,%rdx
  40322e:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403235:	48 01 d0             	add    %rdx,%rax
  403238:	48 8b 80 10 01 00 00 	mov    0x110(%rax),%rax
  40323f:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  403245:	48 63 d2             	movslq %edx,%rdx
  403248:	48 89 d1             	mov    %rdx,%rcx
  40324b:	48 c1 e1 0a          	shl    $0xa,%rcx
  40324f:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403256:	48 01 ca             	add    %rcx,%rdx
  403259:	48 8b 92 20 01 00 00 	mov    0x120(%rdx),%rdx
  403260:	48 29 d0             	sub    %rdx,%rax
  403263:	48 89 c6             	mov    %rax,%rsi
  403266:	48 8d 05 9f 0f 00 00 	lea    0xf9f(%rip),%rax        # 40420c <_IO_stdin_used+0x20c>
  40326d:	48 89 c7             	mov    %rax,%rdi
  403270:	b8 00 00 00 00       	mov    $0x0,%eax
  403275:	e8 06 de ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  40327a:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403280:	48 98                	cltq
  403282:	48 c1 e0 0a          	shl    $0xa,%rax
  403286:	48 89 c2             	mov    %rax,%rdx
  403289:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403290:	48 01 d0             	add    %rdx,%rax
  403293:	48 8b 80 10 01 00 00 	mov    0x110(%rax),%rax
  40329a:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4032a0:	48 63 d2             	movslq %edx,%rdx
  4032a3:	48 89 d1             	mov    %rdx,%rcx
  4032a6:	48 c1 e1 0a          	shl    $0xa,%rcx
  4032aa:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4032b1:	48 01 ca             	add    %rcx,%rdx
  4032b4:	48 8b 92 00 01 00 00 	mov    0x100(%rdx),%rdx
  4032bb:	48 29 d0             	sub    %rdx,%rax
  4032be:	48 89 c6             	mov    %rax,%rsi
  4032c1:	48 8d 05 44 0f 00 00 	lea    0xf44(%rip),%rax        # 40420c <_IO_stdin_used+0x20c>
  4032c8:	48 89 c7             	mov    %rax,%rdi
  4032cb:	b8 00 00 00 00       	mov    $0x0,%eax
  4032d0:	e8 ab dd ff ff       	call   401080 <printf@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  4032d5:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4032db:	48 98                	cltq
  4032dd:	48 c1 e0 0a          	shl    $0xa,%rax
  4032e1:	48 89 c2             	mov    %rax,%rdx
  4032e4:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4032eb:	48 01 d0             	add    %rdx,%rax
  4032ee:	48 8b 80 40 01 00 00 	mov    0x140(%rax),%rax
  4032f5:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4032fb:	48 63 d2             	movslq %edx,%rdx
  4032fe:	48 89 d1             	mov    %rdx,%rcx
  403301:	48 c1 e1 0a          	shl    $0xa,%rcx
  403305:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  40330c:	48 01 ca             	add    %rcx,%rdx
  40330f:	48 8b 92 30 01 00 00 	mov    0x130(%rdx),%rdx
  403316:	48 29 d0             	sub    %rdx,%rax
  403319:	48 89 c6             	mov    %rax,%rsi
  40331c:	48 8d 05 ee 0e 00 00 	lea    0xeee(%rip),%rax        # 404211 <_IO_stdin_used+0x211>
  403323:	48 89 c7             	mov    %rax,%rdi
  403326:	b8 00 00 00 00       	mov    $0x0,%eax
  40332b:	e8 50 dd ff ff       	call   401080 <printf@plt>
  for (int x = 0; x < 1 ;  x++){
  403330:	83 85 b4 fe ff ff 01 	addl   $0x1,-0x14c(%rbp)
  403337:	83 bd b4 fe ff ff 00 	cmpl   $0x0,-0x14c(%rbp)
  40333e:	0f 8e 6f fd ff ff    	jle    4030b3 <main+0x1047>
  } 
  printf("%ld good reads per second\n", goods / seconds);
  403344:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  40334a:	48 63 d8             	movslq %eax,%rbx
  40334d:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
  403354:	48 99                	cqto
  403356:	48 f7 fb             	idiv   %rbx
  403359:	48 89 c6             	mov    %rax,%rsi
  40335c:	48 8d 05 b6 0e 00 00 	lea    0xeb6(%rip),%rax        # 404219 <_IO_stdin_used+0x219>
  403363:	48 89 c7             	mov    %rax,%rdi
  403366:	b8 00 00 00 00       	mov    $0x0,%eax
  40336b:	e8 10 dd ff ff       	call   401080 <printf@plt>
  printf("%ld good reads per second latency\n", 1000000000 / (goods / seconds));
  403370:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  403376:	48 63 d8             	movslq %eax,%rbx
  403379:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
  403380:	48 99                	cqto
  403382:	48 f7 fb             	idiv   %rbx
  403385:	48 89 c3             	mov    %rax,%rbx
  403388:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40338d:	48 99                	cqto
  40338f:	48 f7 fb             	idiv   %rbx
  403392:	48 89 c6             	mov    %rax,%rsi
  403395:	48 8d 05 9c 0e 00 00 	lea    0xe9c(%rip),%rax        # 404238 <_IO_stdin_used+0x238>
  40339c:	48 89 c7             	mov    %rax,%rdi
  40339f:	b8 00 00 00 00       	mov    $0x0,%eax
  4033a4:	e8 d7 dc ff ff       	call   401080 <printf@plt>
     }
   fclose(out_file);
   
 }

  char * filename = calloc(100, sizeof(char));
  4033a9:	be 01 00 00 00       	mov    $0x1,%esi
  4033ae:	bf 64 00 00 00       	mov    $0x64,%edi
  4033b3:	e8 18 dd ff ff       	call   4010d0 <calloc@plt>
  4033b8:	48 89 45 90          	mov    %rax,-0x70(%rbp)
  char * buf = calloc(1000, sizeof(char));
  4033bc:	be 01 00 00 00       	mov    $0x1,%esi
  4033c1:	bf e8 03 00 00       	mov    $0x3e8,%edi
  4033c6:	e8 05 dd ff ff       	call   4010d0 <calloc@plt>
  4033cb:	48 89 45 98          	mov    %rax,-0x68(%rbp)
  memset(filename, 0, 100);
  4033cf:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4033d3:	ba 64 00 00 00       	mov    $0x64,%edx
  4033d8:	be 00 00 00 00       	mov    $0x0,%esi
  4033dd:	48 89 c7             	mov    %rax,%rdi
  4033e0:	e8 db dc ff ff       	call   4010c0 <memset@plt>
  snprintf(filename, 100, "coroutine.struct");
  4033e5:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4033e9:	48 8d 15 6b 0e 00 00 	lea    0xe6b(%rip),%rdx        # 40425b <_IO_stdin_used+0x25b>
  4033f0:	be 64 00 00 00       	mov    $0x64,%esi
  4033f5:	48 89 c7             	mov    %rax,%rdi
  4033f8:	b8 00 00 00 00       	mov    $0x0,%eax
  4033fd:	e8 8e dc ff ff       	call   401090 <snprintf@plt>
  FILE *out_file = fopen(filename, "w");
  403402:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403406:	48 8d 15 5f 0e 00 00 	lea    0xe5f(%rip),%rdx        # 40426c <_IO_stdin_used+0x26c>
  40340d:	48 89 d6             	mov    %rdx,%rsi
  403410:	48 89 c7             	mov    %rax,%rdi
  403413:	e8 d8 dc ff ff       	call   4010f0 <fopen@plt>
  403418:	48 89 45 a0          	mov    %rax,-0x60(%rbp)

memset(buf, 0, 1000);
  40341c:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403420:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403425:	be 00 00 00 00       	mov    $0x0,%esi
  40342a:	48 89 c7             	mov    %rax,%rdi
  40342d:	e8 8e dc ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "index %ld\n", offsetof(struct Coroutine, index));
  403432:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403436:	b9 00 00 00 00       	mov    $0x0,%ecx
  40343b:	48 8d 15 2c 0e 00 00 	lea    0xe2c(%rip),%rdx        # 40426e <_IO_stdin_used+0x26e>
  403442:	be 64 00 00 00       	mov    $0x64,%esi
  403447:	48 89 c7             	mov    %rax,%rdi
  40344a:	b8 00 00 00 00       	mov    $0x0,%eax
  40344f:	e8 3c dc ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  403454:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  403458:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40345c:	48 89 d6             	mov    %rdx,%rsi
  40345f:	48 89 c7             	mov    %rax,%rdi
  403462:	e8 49 dc ff ff       	call   4010b0 <fputs@plt>
  
  memset(buf, 0, 1000);
  403467:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40346b:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403470:	be 00 00 00 00       	mov    $0x0,%esi
  403475:	48 89 c7             	mov    %rax,%rdi
  403478:	e8 43 dc ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "rsp %ld\n", offsetof(struct Coroutine, rsp));
  40347d:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403481:	b9 08 00 00 00       	mov    $0x8,%ecx
  403486:	48 8d 15 ec 0d 00 00 	lea    0xdec(%rip),%rdx        # 404279 <_IO_stdin_used+0x279>
  40348d:	be 64 00 00 00       	mov    $0x64,%esi
  403492:	48 89 c7             	mov    %rax,%rdi
  403495:	b8 00 00 00 00       	mov    $0x0,%eax
  40349a:	e8 f1 db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  40349f:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  4034a3:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034a7:	48 89 d6             	mov    %rdx,%rsi
  4034aa:	48 89 c7             	mov    %rax,%rdi
  4034ad:	e8 fe db ff ff       	call   4010b0 <fputs@plt>
  
  memset(buf, 0, 1000);
  4034b2:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034b6:	ba e8 03 00 00       	mov    $0x3e8,%edx
  4034bb:	be 00 00 00 00       	mov    $0x0,%esi
  4034c0:	48 89 c7             	mov    %rax,%rdi
  4034c3:	e8 f8 db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "eip %ld\n", offsetof(struct Coroutine, eip));
  4034c8:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034cc:	b9 10 00 00 00       	mov    $0x10,%ecx
  4034d1:	48 8d 15 aa 0d 00 00 	lea    0xdaa(%rip),%rdx        # 404282 <_IO_stdin_used+0x282>
  4034d8:	be 64 00 00 00       	mov    $0x64,%esi
  4034dd:	48 89 c7             	mov    %rax,%rdi
  4034e0:	b8 00 00 00 00       	mov    $0x0,%eax
  4034e5:	e8 a6 db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  4034ea:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  4034ee:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034f2:	48 89 d6             	mov    %rdx,%rsi
  4034f5:	48 89 c7             	mov    %rax,%rdi
  4034f8:	e8 b3 db ff ff       	call   4010b0 <fputs@plt>


  memset(buf, 0, 1000);
  4034fd:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403501:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403506:	be 00 00 00 00       	mov    $0x0,%esi
  40350b:	48 89 c7             	mov    %rax,%rdi
  40350e:	e8 ad db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "data %ld\n", offsetof(struct Coroutine, data));
  403513:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403517:	b9 18 00 00 00       	mov    $0x18,%ecx
  40351c:	48 8d 15 68 0d 00 00 	lea    0xd68(%rip),%rdx        # 40428b <_IO_stdin_used+0x28b>
  403523:	be 64 00 00 00       	mov    $0x64,%esi
  403528:	48 89 c7             	mov    %rax,%rdi
  40352b:	b8 00 00 00 00       	mov    $0x0,%eax
  403530:	e8 5b db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  403535:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  403539:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40353d:	48 89 d6             	mov    %rdx,%rsi
  403540:	48 89 c7             	mov    %rax,%rdi
  403543:	e8 68 db ff ff       	call   4010b0 <fputs@plt>

  memset(buf, 0, 1000);
  403548:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40354c:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403551:	be 00 00 00 00       	mov    $0x0,%esi
  403556:	48 89 c7             	mov    %rax,%rdi
  403559:	e8 62 db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "corourinedata.running %ld\n", offsetof(struct CoroutineData, running));
  40355e:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403562:	b9 00 00 00 00       	mov    $0x0,%ecx
  403567:	48 8d 15 27 0d 00 00 	lea    0xd27(%rip),%rdx        # 404295 <_IO_stdin_used+0x295>
  40356e:	be 64 00 00 00       	mov    $0x64,%esi
  403573:	48 89 c7             	mov    %rax,%rdi
  403576:	b8 00 00 00 00       	mov    $0x0,%eax
  40357b:	e8 10 db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  403580:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  403584:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403588:	48 89 d6             	mov    %rdx,%rsi
  40358b:	48 89 c7             	mov    %rax,%rdi
  40358e:	e8 1d db ff ff       	call   4010b0 <fputs@plt>

  memset(buf, 0, 1000);
  403593:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403597:	ba e8 03 00 00       	mov    $0x3e8,%edx
  40359c:	be 00 00 00 00       	mov    $0x0,%esi
  4035a1:	48 89 c7             	mov    %rax,%rdi
  4035a4:	e8 17 db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "size coroutine %ld\n", sizeof(struct Coroutine));
  4035a9:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4035ad:	b9 20 00 00 00       	mov    $0x20,%ecx
  4035b2:	48 8d 15 f7 0c 00 00 	lea    0xcf7(%rip),%rdx        # 4042b0 <_IO_stdin_used+0x2b0>
  4035b9:	be 64 00 00 00       	mov    $0x64,%esi
  4035be:	48 89 c7             	mov    %rax,%rdi
  4035c1:	b8 00 00 00 00       	mov    $0x0,%eax
  4035c6:	e8 c5 da ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  4035cb:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  4035cf:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4035d3:	48 89 d6             	mov    %rdx,%rsi
  4035d6:	48 89 c7             	mov    %rax,%rdi
  4035d9:	e8 d2 da ff ff       	call   4010b0 <fputs@plt>
  
  fclose(out_file);
  4035de:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  4035e2:	48 89 c7             	mov    %rax,%rdi
  4035e5:	e8 76 da ff ff       	call   401060 <fclose@plt>
  4035ea:	b8 00 00 00 00       	mov    $0x0,%eax
  4035ef:	48 8b 55 e8          	mov    -0x18(%rbp),%rdx
  4035f3:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  4035fc:	74 05                	je     403603 <main+0x1597>
  4035fe:	e8 6d da ff ff       	call   401070 <__stack_chk_fail@plt>
  403603:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
  403607:	c9                   	leave
  403608:	c3                   	ret
  403609:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000403610 <.MSG>:
  403610:	43                   	rex.XB
  403611:	4f 20 43 6f          	rex.WRXB and %r8b,0x6f(%r11)
  403615:	72 6f                	jb     403686 <switch_to+0xe>
  403617:	75 74                	jne    40368d <switch_to+0x15>
  403619:	69 6e 65 53 74 72 75 	imul   $0x75727453,0x65(%rsi),%ebp
  403620:	63 74 20 25          	movsxd 0x25(%rax,%riz,1),%esi
  403624:	78 0a                	js     403630 <.EIP+0x9>
	...

0000000000403627 <.EIP>:
  403627:	43                   	rex.XB
  403628:	4f 20 45 49          	rex.WRXB and %r8b,0x49(%r13)
  40362c:	50                   	push   %rax
  40362d:	2e                   	cs
  40362e:	2e                   	cs
  40362f:	2e                   	cs
  403630:	20                   	.byte 0x20
  403631:	25                   	.byte 0x25
  403632:	78 0a                	js     40363e <.CODATA+0x9>
	...

0000000000403635 <.CODATA>:
  403635:	43                   	rex.XB
  403636:	4f 20 63 6f          	rex.WRXB and %r12b,0x6f(%r11)
  40363a:	64 61                	fs (bad)
  40363c:	74 61                	je     40369f <switch_to+0x27>
  40363e:	2e                   	cs
  40363f:	2e                   	cs
  403640:	2e                   	cs
  403641:	20                   	.byte 0x20
  403642:	25                   	.byte 0x25
  403643:	78 0a                	js     40364f <.INDEX+0x9>
	...

0000000000403646 <.INDEX>:
  403646:	43 6f                	rex.XB outsl %ds:(%rsi),(%dx)
  403648:	72 6f                	jb     4036b9 <switch_to+0x41>
  40364a:	75 74                	jne    4036c0 <switch_to+0x48>
  40364c:	69 6e 65 20 69 6e 64 	imul   $0x646e6920,0x65(%rsi),%ebp
  403653:	65 78 2e             	gs js  403684 <switch_to+0xc>
  403656:	2e                   	cs
  403657:	2e                   	cs
  403658:	20                   	.byte 0x20
  403659:	25                   	.byte 0x25
  40365a:	64 0a 00             	or     %fs:(%rax),%al

000000000040365d <.RET>:
  40365d:	52                   	push   %rdx
  40365e:	65 74 75             	gs je  4036d6 <switch_to+0x5e>
  403661:	72 6e                	jb     4036d1 <switch_to+0x59>
  403663:	2e                   	cs
  403664:	2e                   	cs
  403665:	2e                   	cs
  403666:	20                   	.byte 0x20
  403667:	25                   	.byte 0x25
  403668:	78 0a                	js     403674 <.STACK+0x9>
	...

000000000040366b <.STACK>:
  40366b:	53                   	push   %rbx
  40366c:	74 61                	je     4036cf <switch_to+0x57>
  40366e:	63 6b 2e             	movsxd 0x2e(%rbx),%ebp
  403671:	2e                   	cs
  403672:	2e                   	cs
  403673:	20                   	.byte 0x20
  403674:	25                   	.byte 0x25
  403675:	70 0a                	jo     403681 <switch_to+0x9>
	...

0000000000403678 <switch_to>:
	.text
	# switch_to(struct Coroutine * coroutines, int index, struct Scheduler * scheduler)
	# rdi, %rsi, %rdx, %rcx, %r8 and %r9
switch_to:
# popq %r11
pushq %rbp
  403678:	55                   	push   %rbp

movq %rsp, %rbp
  403679:	48 89 e5             	mov    %rsp,%rbp
subq $1024, %rsp
  40367c:	48 81 ec 00 04 00 00 	sub    $0x400,%rsp



movq %rdi, -56(%rbp) # coroutine table
  403683:	48 89 7d c8          	mov    %rdi,-0x38(%rbp)
movq %rsi, -8(%rbp) # index
  403687:	48 89 75 f8          	mov    %rsi,-0x8(%rbp)
movq %rdx, -16(%rbp) # scheduler
  40368b:	48 89 55 f0          	mov    %rdx,-0x10(%rbp)

movq %rsi, %rax
  40368f:	48 89 f0             	mov    %rsi,%rax
imul $32, %rax
  403692:	48 6b c0 20          	imul   $0x20,%rax,%rax
addq %rdi, %rax
  403696:	48 01 f8             	add    %rdi,%rax
mov %rax, %r11
  403699:	49 89 c3             	mov    %rax,%r11

mov %r11, %rax
  40369c:	4c 89 d8             	mov    %r11,%rax
movq %rax, %r9
  40369f:	49 89 c1             	mov    %rax,%r9
movq %r9, -24(%rbp) # coroutine object
  4036a2:	4c 89 4d e8          	mov    %r9,-0x18(%rbp)

movq %r11, %rax
  4036a6:	4c 89 d8             	mov    %r11,%rax
leaq 8(%rax), %rax
  4036a9:	48 8d 40 08          	lea    0x8(%rax),%rax
movq %rax, %r9
  4036ad:	49 89 c1             	mov    %rax,%r9
movq %r9, -48(%rbp) # rsp
  4036b0:	4c 89 4d d0          	mov    %r9,-0x30(%rbp)

movq %r11, %rax
  4036b4:	4c 89 d8             	mov    %r11,%rax
leaq 16(%rax), %rax
  4036b7:	48 8d 40 10          	lea    0x10(%rax),%rax
movq (%rax), %r9
  4036bb:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -32(%rbp) # coroutine function
  4036be:	4c 89 4d e0          	mov    %r9,-0x20(%rbp)

movq %r11, %rax
  4036c2:	4c 89 d8             	mov    %r11,%rax
leaq 8(%rax), %rax
  4036c5:	48 8d 40 08          	lea    0x8(%rax),%rax
movq (%rax), %r9
  4036c9:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -64(%rbp) # coroutine stack
  4036cc:	4c 89 4d c0          	mov    %r9,-0x40(%rbp)

movq %r11, %rax
  4036d0:	4c 89 d8             	mov    %r11,%rax
leaq 24(%rax), %rax # load from coroutine object data object
  4036d3:	48 8d 40 18          	lea    0x18(%rax),%rax
movq (%rax), %r9
  4036d7:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -40(%rbp) # coroutine data object
  4036da:	4c 89 4d d8          	mov    %r9,-0x28(%rbp)
movq (%rax), %rcx
  4036de:	48 8b 08             	mov    (%rax),%rcx

movq -24(%rbp), %r11
  4036e1:	4c 8b 5d e8          	mov    -0x18(%rbp),%r11
#

leaq .INDEX(%rip), %rdi
  4036e5:	48 8d 3d 5a ff ff ff 	lea    -0xa6(%rip),%rdi        # 403646 <.INDEX>
#call printf@plt
mov $0, %eax
  4036ec:	b8 00 00 00 00       	mov    $0x0,%eax

#pushq %r11
leaq .MSG(%rip), %rdi
  4036f1:	48 8d 3d 18 ff ff ff 	lea    -0xe8(%rip),%rdi        # 403610 <.MSG>
movq %r11, %rsi
  4036f8:	4c 89 de             	mov    %r11,%rsi
# call printf@plt
mov $0, %eax
  4036fb:	b8 00 00 00 00       	mov    $0x0,%eax

#popq %r11

#pushq %r9
movq -32(%rbp), %r9
  403700:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9

leaq .EIP(%rip), %rdi
  403704:	48 8d 3d 1c ff ff ff 	lea    -0xe4(%rip),%rdi        # 403627 <.EIP>
movq %r9, %rsi
  40370b:	4c 89 ce             	mov    %r9,%rsi
#call printf@plt
mov $0, %eax
  40370e:	b8 00 00 00 00       	mov    $0x0,%eax
#popq %r9
# coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data

#pushq %r9
leaq .CODATA(%rip), %rdi
  403713:	48 8d 3d 1b ff ff ff 	lea    -0xe5(%rip),%rdi        # 403635 <.CODATA>
movq -40(%rbp), %rsi
  40371a:	48 8b 75 d8          	mov    -0x28(%rbp),%rsi
#call printf@plt
mov $0, %eax
  40371e:	b8 00 00 00 00       	mov    $0x0,%eax
#pushq %r11
#movq %r11, %rsp

#mov %rbp, %rsp

movq -16(%rbp), %rdi
  403723:	48 8b 7d f0          	mov    -0x10(%rbp),%rdi
movq -24(%rbp), %rsi
  403727:	48 8b 75 e8          	mov    -0x18(%rbp),%rsi
movq -40(%rbp), %rdx
  40372b:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
#mov %rsp, %rbp
# pushq %r11



leaq .STACK(%rip), %rdi
  40372f:	48 8d 3d 35 ff ff ff 	lea    -0xcb(%rip),%rdi        # 40366b <.STACK>
movq -64(%rbp), %rsi
  403736:	48 8b 75 c0          	mov    -0x40(%rbp),%rsi
call printf@plt
  40373a:	e8 41 d9 ff ff       	call   401080 <printf@plt>
mov $0, %eax
  40373f:	b8 00 00 00 00       	mov    $0x0,%eax

movq -32(%rbp), %r9
  403744:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9
leaq after(%rip), %r11
  403748:	4c 8d 1d 0f 00 00 00 	lea    0xf(%rip),%r11        # 40375e <after>

movq -64(%rbp), %rsp # set stack to coroutine
  40374f:	48 8b 65 c0          	mov    -0x40(%rbp),%rsp
sub $8, %rsp
  403753:	48 83 ec 08          	sub    $0x8,%rsp
movq %r11, (%rsp) # set stack return address
  403757:	4c 89 1c 24          	mov    %r11,(%rsp)

# pushq %rbp
jmp *%r9
  40375b:	41 ff e1             	jmp    *%r9

000000000040375e <after>:
after: 
# pushq %rbp
# popq %rbp
#movq %rsp, %rbp

leaq .RET(%rip), %rdi
  40375e:	48 8d 3d f8 fe ff ff 	lea    -0x108(%rip),%rdi        # 40365d <.RET>
movq %rsp, %rsi
  403765:	48 89 e6             	mov    %rsp,%rsi
call printf@plt
  403768:	e8 13 d9 ff ff       	call   401080 <printf@plt>
mov $0, %eax
  40376d:	b8 00 00 00 00       	mov    $0x0,%eax


#pop %rbp
add $1024, %rsp
  403772:	48 81 c4 00 04 00 00 	add    $0x400,%rsp
#movq %rsp, %rbp
#popq %rbp
  403779:	c3                   	ret

Disassembly of section .fini:

000000000040377c <_fini>:
  40377c:	f3 0f 1e fa          	endbr64
  403780:	48 83 ec 08          	sub    $0x8,%rsp
  403784:	48 83 c4 08          	add    $0x8,%rsp
  403788:	c3                   	ret
