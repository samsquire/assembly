
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
  401148:	48 c7 c7 7d 20 40 00 	mov    $0x40207d,%rdi
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
  asm("lea 0(%%rip), %%r11\n"
  40126b:	4c 8d 1d 00 00 00 00 	lea    0x0(%rip),%r11        # 401272 <coroutine_func+0x55>
  401272:	4c 89 da             	mov    %r11,%rdx
  401275:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401279:	48 89 50 10          	mov    %rdx,0x10(%rax)
      "movq %%r11, %0" : "=rm" (coroutine->eip) ::"r11");

  // cant clobber rsp from inside coroutind :-(
  
    // yield(1, scheduler, coroutine) 
  uint64_t rsp = scheduler->rsp;
  40127d:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401281:	48 8b 00             	mov    (%rax),%rax
  401284:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  printf("scheduler %p scheduler %p\n", scheduler, rsp);
  401288:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  40128c:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401290:	48 89 c6             	mov    %rax,%rsi
  401293:	48 8d 05 89 2d 00 00 	lea    0x2d89(%rip),%rax        # 404023 <_IO_stdin_used+0x23>
  40129a:	48 89 c7             	mov    %rax,%rdi
  40129d:	b8 00 00 00 00       	mov    $0x0,%eax
  4012a2:	e8 d9 fd ff ff       	call   401080 <printf@plt>
  //asm("movq %0, %%rsp" ::"rm"(scheduler->rsp): "rsp");  
         
 // }
  //printf("loop finished\n");
  return scheduler->rsp;
  4012a7:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4012ab:	48 8b 00             	mov    (%rax),%rax
}   
  4012ae:	c9                   	leave
  4012af:	c3                   	ret

00000000004012b0 <pollthreads>:
// thread 2
if tasks.taskindex > threads[0].workindex:
  value = 2
*/

int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  4012b0:	55                   	push   %rbp
  4012b1:	48 89 e5             	mov    %rsp,%rbp
  4012b4:	48 89 7d d8          	mov    %rdi,-0x28(%rbp)
  4012b8:	48 89 75 d0          	mov    %rsi,-0x30(%rbp)
  4012bc:	48 89 55 c8          	mov    %rdx,-0x38(%rbp)
  4012c0:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
  4012c4:	4c 89 45 b8          	mov    %r8,-0x48(%rbp)
  long WM = WRITE_MASK;
  4012c8:	48 c7 45 f0 04 00 00 00 	movq   $0x4,-0x10(%rbp)
  long RM = READ_MASK;
  4012d0:	48 c7 45 f8 08 00 00 00 	movq   $0x8,-0x8(%rbp)
  for (int x = 1; x < data->threadsize ; x++) {
  4012d8:	c7 45 e8 01 00 00 00 	movl   $0x1,-0x18(%rbp)
  4012df:	e9 9b 00 00 00       	jmp    40137f <pollthreads+0xcf>
  // printf("thread %d %ld\n", x, data->threads[x].ready);
    int mask = data->threads[1].readies[x];
  4012e4:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4012e8:	48 8b 40 30          	mov    0x30(%rax),%rax
  4012ec:	48 05 00 04 00 00    	add    $0x400,%rax
  4012f2:	48 8b 50 20          	mov    0x20(%rax),%rdx
  4012f6:	8b 45 e8             	mov    -0x18(%rbp),%eax
  4012f9:	48 98                	cltq
  4012fb:	48 c1 e0 02          	shl    $0x2,%rax
  4012ff:	48 01 d0             	add    %rdx,%rax
  401302:	8b 00                	mov    (%rax),%eax
  401304:	89 45 ec             	mov    %eax,-0x14(%rbp)
        //printf("pollpread? %ld %ld\n", mask, (mask & PREP_READ_MASK));
       // printf("pplreadmask? %ld %ld\n", mask, (mask & READ_MASK));
      //  printf("pollwritemask ? %ld %ld\n", mask, (mask & WRITE_MASK));
       // data->threads[x].newmask = 0;
        
        if ((mask & WM) == WM || mask == 0) {
  401307:	8b 45 ec             	mov    -0x14(%rbp),%eax
  40130a:	48 98                	cltq
  40130c:	48 23 45 f0          	and    -0x10(%rbp),%rax
  401310:	48 39 45 f0          	cmp    %rax,-0x10(%rbp)
  401314:	74 06                	je     40131c <pollthreads+0x6c>
  401316:	83 7d ec 00          	cmpl   $0x0,-0x14(%rbp)
  40131a:	75 25                	jne    401341 <pollthreads+0x91>
         //printf("found a writer\n");
          readywriters[(*writers)++] = x;
  40131c:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401320:	8b 00                	mov    (%rax),%eax
  401322:	8d 48 01             	lea    0x1(%rax),%ecx
  401325:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
  401329:	89 0a                	mov    %ecx,(%rdx)
  40132b:	48 98                	cltq
  40132d:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401335:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
  401339:	48 01 c2             	add    %rax,%rdx
  40133c:	8b 45 e8             	mov    -0x18(%rbp),%eax
  40133f:	89 02                	mov    %eax,(%rdx)
        }
    if ((mask & RM) == RM || mask == 0) {
  401341:	8b 45 ec             	mov    -0x14(%rbp),%eax
  401344:	48 98                	cltq
  401346:	48 23 45 f8          	and    -0x8(%rbp),%rax
  40134a:	48 39 45 f8          	cmp    %rax,-0x8(%rbp)
  40134e:	74 06                	je     401356 <pollthreads+0xa6>
  401350:	83 7d ec 00          	cmpl   $0x0,-0x14(%rbp)
  401354:	75 25                	jne    40137b <pollthreads+0xcb>
      readyreaders[(*readers)++] = x;
  401356:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
  40135a:	8b 00                	mov    (%rax),%eax
  40135c:	8d 48 01             	lea    0x1(%rax),%ecx
  40135f:	48 8b 55 c0          	mov    -0x40(%rbp),%rdx
  401363:	89 0a                	mov    %ecx,(%rdx)
  401365:	48 98                	cltq
  401367:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  40136f:	48 8b 45 d0          	mov    -0x30(%rbp),%rax
  401373:	48 01 c2             	add    %rax,%rdx
  401376:	8b 45 e8             	mov    -0x18(%rbp),%eax
  401379:	89 02                	mov    %eax,(%rdx)
  for (int x = 1; x < data->threadsize ; x++) {
  40137b:	83 45 e8 01          	addl   $0x1,-0x18(%rbp)
  40137f:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401383:	8b 40 68             	mov    0x68(%rax),%eax
  401386:	39 45 e8             	cmp    %eax,-0x18(%rbp)
  401389:	0f 8c 55 ff ff ff    	jl     4012e4 <pollthreads+0x34>
    // printf("found a reader\n");
    }
      }
  // printf("%d readers %d writers\n", *readers, *writers);
      
  return 0;
  40138f:	b8 00 00 00 00       	mov    $0x0,%eax
}
  401394:	5d                   	pop    %rbp
  401395:	c3                   	ret

0000000000401396 <findavailable>:


int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  401396:	55                   	push   %rbp
  401397:	48 89 e5             	mov    %rsp,%rbp
  40139a:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  40139e:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
  4013a2:	48 89 55 d8          	mov    %rdx,-0x28(%rbp)
  4013a6:	48 89 4d d0          	mov    %rcx,-0x30(%rbp)
  4013aa:	4c 89 45 c8          	mov    %r8,-0x38(%rbp)
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4013ae:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
  4013b5:	eb 64                	jmp    40141b <findavailable+0x85>
        
        if (data->freelist[x].available == FREE ) {
  4013b7:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4013bb:	48 8b 90 a0 00 00 00 	mov    0xa0(%rax),%rdx
  4013c2:	8b 45 fc             	mov    -0x4(%rbp),%eax
  4013c5:	48 98                	cltq
  4013c7:	48 c1 e0 05          	shl    $0x5,%rax
  4013cb:	48 01 d0             	add    %rdx,%rax
  4013ce:	8b 40 10             	mov    0x10(%rax),%eax
  4013d1:	83 f8 01             	cmp    $0x1,%eax
  4013d4:	75 41                	jne    401417 <findavailable+0x81>
          //printf("%d\n", *availableidx);
         available[*availableidx] = x;
  4013d6:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013da:	8b 00                	mov    (%rax),%eax
  4013dc:	48 98                	cltq
  4013de:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4013e6:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  4013ea:	48 01 c2             	add    %rax,%rdx
  4013ed:	8b 45 fc             	mov    -0x4(%rbp),%eax
  4013f0:	48 98                	cltq
  4013f2:	48 89 02             	mov    %rax,(%rdx)
         (*availableidx)++;
  4013f5:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013f9:	8b 00                	mov    (%rax),%eax
  4013fb:	8d 50 01             	lea    0x1(%rax),%edx
  4013fe:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401402:	89 10                	mov    %edx,(%rax)
         if ((*availableidx) == data->threadsize * 2) {
  401404:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401408:	8b 10                	mov    (%rax),%edx
  40140a:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  40140e:	8b 40 68             	mov    0x68(%rax),%eax
  401411:	01 c0                	add    %eax,%eax
  401413:	39 c2                	cmp    %eax,%edx
  401415:	74 20                	je     401437 <findavailable+0xa1>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401417:	83 45 fc 01          	addl   $0x1,-0x4(%rbp)
  40141b:	8b 45 fc             	mov    -0x4(%rbp),%eax
  40141e:	48 63 d0             	movslq %eax,%rdx
  401421:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401425:	48 8b 80 b8 00 00 00 	mov    0xb8(%rax),%rax
  40142c:	48 83 c0 01          	add    $0x1,%rax
  401430:	48 39 c2             	cmp    %rax,%rdx
  401433:	7c 82                	jl     4013b7 <findavailable+0x21>
  401435:	eb 01                	jmp    401438 <findavailable+0xa2>
           break;
  401437:	90                   	nop
         }

         // printf("%d chunk is free\n", x);
        }
      }
      if (*availableidx == 0) {
  401438:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  40143c:	8b 00                	mov    (%rax),%eax
  40143e:	85 c0                	test   %eax,%eax
  401440:	75 07                	jne    401449 <findavailable+0xb3>
       //printf("no chunks avail\n");
        
        return 1;
  401442:	b8 01 00 00 00       	mov    $0x1,%eax
  401447:	eb 05                	jmp    40144e <findavailable+0xb8>
      }
  return 0;
  401449:	b8 00 00 00 00       	mov    $0x0,%eax
}
  40144e:	5d                   	pop    %rbp
  40144f:	c3                   	ret

0000000000401450 <singlewriter3>:

int singlewriter3(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401450:	55                   	push   %rbp
  401451:	48 89 e5             	mov    %rsp,%rbp
  401454:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  401458:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
  40145c:	48 89 55 d8          	mov    %rdx,-0x28(%rbp)
  401460:	48 89 4d d0          	mov    %rcx,-0x30(%rbp)
  int completed = 0;
  401464:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
   */



  //printf("%d %d\n", data->writecursor, data->writecursor % (data->threadsize - 1));
  if (data->writecursor != 0 && (data->writecursor % (data->threadsize - 1)) == 0) {
  40146b:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  40146f:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401475:	85 c0                	test   %eax,%eax
    //printf("writeepoch\n");
  } else {

  }

}
  401477:	90                   	nop
  401478:	5d                   	pop    %rbp
  401479:	c3                   	ret

000000000040147a <singlewriter2>:

int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40147a:	55                   	push   %rbp
  40147b:	48 89 e5             	mov    %rsp,%rbp
  40147e:	48 83 ec 40          	sub    $0x40,%rsp
  401482:	48 89 7d d8          	mov    %rdi,-0x28(%rbp)
  401486:	48 89 75 d0          	mov    %rsi,-0x30(%rbp)
  40148a:	48 89 55 c8          	mov    %rdx,-0x38(%rbp)
  40148e:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
  int completed = 0;
  401492:	c7 45 ec 00 00 00 00 	movl   $0x0,-0x14(%rbp)
   }
   */


//if ((__atomic_load_n(&data->readcursor, __ATOMIC_SEQ_CST) % data->threadsize) == 0) {
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401499:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  40149d:	8b 80 00 02 00 00    	mov    0x200(%rax),%eax
  4014a3:	85 c0                	test   %eax,%eax
  4014a5:	0f 84 c7 00 00 00    	je     401572 <singlewriter2+0xf8>
  4014ab:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014af:	8b 80 00 02 00 00    	mov    0x200(%rax),%eax
  4014b5:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  4014b9:	8b 52 68             	mov    0x68(%rdx),%edx
  4014bc:	8d 4a ff             	lea    -0x1(%rdx),%ecx
  4014bf:	99                   	cltd
  4014c0:	f7 f9                	idiv   %ecx
  4014c2:	89 d0                	mov    %edx,%eax
  4014c4:	85 c0                	test   %eax,%eax
  4014c6:	0f 85 a6 00 00 00    	jne    401572 <singlewriter2+0xf8>
   // data->readcursor = 0;
    //printf("readepoch\n");
    
  
        // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
        struct Data * thread = &data->threads[data->threadindex];
  4014cc:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014d0:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4014d4:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014d8:	8b 40 64             	mov    0x64(%rax),%eax
  4014db:	48 98                	cltq
  4014dd:	48 c1 e0 0a          	shl    $0xa,%rax
  4014e1:	48 01 d0             	add    %rdx,%rax
  4014e4:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4014e8:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4014ec:	48 8b 88 18 03 00 00 	mov    0x318(%rax),%rcx
  4014f3:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4014f7:	8b 80 24 03 00 00    	mov    0x324(%rax),%eax
  4014fd:	48 63 d0             	movslq %eax,%rdx
  401500:	48 89 d0             	mov    %rdx,%rax
  401503:	48 01 c0             	add    %rax,%rax
  401506:	48 01 d0             	add    %rdx,%rax
  401509:	48 c1 e0 04          	shl    $0x4,%rax
  40150d:	48 01 c8             	add    %rcx,%rax
  401510:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  401514:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401518:	48 83 c0 08          	add    $0x8,%rax
  40151c:	48 89 c6             	mov    %rax,%rsi
  40151f:	bf 04 00 00 00       	mov    $0x4,%edi
  401524:	e8 27 fb ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401529:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  40152d:	8b 80 24 03 00 00    	mov    0x324(%rax),%eax
  401533:	8d 50 01             	lea    0x1(%rax),%edx
  401536:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  40153a:	8b 88 20 03 00 00    	mov    0x320(%rax),%ecx
  401540:	89 d0                	mov    %edx,%eax
  401542:	99                   	cltd
  401543:	f7 f9                	idiv   %ecx
  401545:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401549:	89 90 24 03 00 00    	mov    %edx,0x324(%rax)
        epoch->kind = NEW_EPOCH;
  40154f:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401553:	c7 40 20 01 00 00 00 	movl   $0x1,0x20(%rax)
        epoch->thread = data->threadindex;
  40155a:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  40155e:	8b 50 64             	mov    0x64(%rax),%edx
  401561:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401565:	89 10                	mov    %edx,(%rax)
        epoch->set = 1;
  401567:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  40156b:	c7 40 24 01 00 00 00 	movl   $0x1,0x24(%rax)
  } else {
    
  }

  
}
  401572:	90                   	nop
  401573:	c9                   	leave
  401574:	c3                   	ret

0000000000401575 <singlewriter>:



*/

int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401575:	55                   	push   %rbp
  401576:	48 89 e5             	mov    %rsp,%rbp
  401579:	48 83 ec 70          	sub    $0x70,%rsp
  40157d:	48 89 7d a8          	mov    %rdi,-0x58(%rbp)
  401581:	48 89 75 a0          	mov    %rsi,-0x60(%rbp)
  401585:	48 89 55 98          	mov    %rdx,-0x68(%rbp)
  401589:	48 89 4d 90          	mov    %rcx,-0x70(%rbp)
  40158d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401596:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  40159a:	31 c0                	xor    %eax,%eax
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  40159c:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015a0:	48 8b 40 30          	mov    0x30(%rax),%rax
  4015a4:	8b 80 0c 02 00 00    	mov    0x20c(%rax),%eax
  4015aa:	8d 50 01             	lea    0x1(%rax),%edx
  4015ad:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015b1:	8b 70 68             	mov    0x68(%rax),%esi
  4015b4:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015b8:	48 8b 48 30          	mov    0x30(%rax),%rcx
  4015bc:	89 d0                	mov    %edx,%eax
  4015be:	99                   	cltd
  4015bf:	f7 fe                	idiv   %esi
  4015c1:	89 d0                	mov    %edx,%eax
  4015c3:	89 81 0c 02 00 00    	mov    %eax,0x20c(%rcx)
  int readers = 0;
  4015c9:	c7 45 b0 00 00 00 00 	movl   $0x0,-0x50(%rbp)
  int writers = 0;
  4015d0:	c7 45 b4 00 00 00 00 	movl   $0x0,-0x4c(%rbp)
  int availableidx = 0;
  4015d7:	c7 45 b8 00 00 00 00 	movl   $0x0,-0x48(%rbp)
    readywriters[x] = x;
  }
  */
  //clock_gettime(CLOCK_MONOTONIC_RAW, &data->wstart);
  
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  4015de:	48 8b 7d 90          	mov    -0x70(%rbp),%rdi
  4015e2:	48 8b 4d 98          	mov    -0x68(%rbp),%rcx
  4015e6:	48 8d 55 b8          	lea    -0x48(%rbp),%rdx
  4015ea:	48 8b 75 a0          	mov    -0x60(%rbp),%rsi
  4015ee:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015f2:	49 89 f8             	mov    %rdi,%r8
  4015f5:	48 89 c7             	mov    %rax,%rdi
  4015f8:	e8 99 fd ff ff       	call   401396 <findavailable>
  4015fd:	89 45 cc             	mov    %eax,-0x34(%rbp)

//clock_gettime(CLOCK_MONOTONIC_RAW, &data->wavail);
  
  if (fill == 1) {
  401600:	83 7d cc 01          	cmpl   $0x1,-0x34(%rbp)
  401604:	75 0a                	jne    401610 <singlewriter+0x9b>
    return 1;
  401606:	b8 01 00 00 00       	mov    $0x1,%eax
  40160b:	e9 f9 02 00 00       	jmp    401909 <singlewriter+0x394>
  }
      
   //printf("buffers available %d\n", availableidx);
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  401610:	48 8d 7d b4          	lea    -0x4c(%rbp),%rdi
  401614:	48 8d 4d b0          	lea    -0x50(%rbp),%rcx
  401618:	48 8b 55 90          	mov    -0x70(%rbp),%rdx
  40161c:	48 8b 75 98          	mov    -0x68(%rbp),%rsi
  401620:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401624:	49 89 f8             	mov    %rdi,%r8
  401627:	48 89 c7             	mov    %rax,%rdi
  40162a:	e8 81 fc ff ff       	call   4012b0 <pollthreads>
      
  //clock_gettime(CLOCK_MONOTONIC_RAW, &data->wpoll);
      
      int assignedchunk = 0;
  40162f:	c7 45 bc 00 00 00 00 	movl   $0x0,-0x44(%rbp)
      
        for (int x = 0; x < readers ; x++) {
  401636:	c7 45 c0 00 00 00 00 	movl   $0x0,-0x40(%rbp)
  40163d:	e9 10 01 00 00       	jmp    401752 <singlewriter+0x1dd>
          if (assignedchunk == availableidx) {
  401642:	8b 45 b8             	mov    -0x48(%rbp),%eax
  401645:	39 45 bc             	cmp    %eax,-0x44(%rbp)
  401648:	0f 84 12 01 00 00    	je     401760 <singlewriter+0x1eb>
           // printf("not enough space readers\n");
                  break;
          }
          int thread = readyreaders[x];
  40164e:	8b 45 c0             	mov    -0x40(%rbp),%eax
  401651:	48 98                	cltq
  401653:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  40165b:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40165f:	48 01 d0             	add    %rdx,%rax
  401662:	8b 00                	mov    (%rax),%eax
  401664:	89 45 d0             	mov    %eax,-0x30(%rbp)
          //printf("%d %p\n", thread, &data->freelist[available[assignedchunk]]);
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401667:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40166b:	48 8b 88 a0 00 00 00 	mov    0xa0(%rax),%rcx
  401672:	8b 45 bc             	mov    -0x44(%rbp),%eax
  401675:	8d 50 01             	lea    0x1(%rax),%edx
  401678:	89 55 bc             	mov    %edx,-0x44(%rbp)
  40167b:	48 98                	cltq
  40167d:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  401685:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  401689:	48 01 d0             	add    %rdx,%rax
  40168c:	48 8b 00             	mov    (%rax),%rax
  40168f:	48 c1 e0 05          	shl    $0x5,%rax
  401693:	48 01 c8             	add    %rcx,%rax
  401696:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
          chunk->available = READING;
  40169a:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  40169e:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
          //printf("assign %p\n", chunk);


          data->threads[thread].reading = chunk;
  4016a5:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016a9:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016ad:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016b0:	48 98                	cltq
  4016b2:	48 c1 e0 0a          	shl    $0xa,%rax
  4016b6:	48 01 c2             	add    %rax,%rdx
  4016b9:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016bd:	48 89 82 a8 00 00 00 	mov    %rax,0xa8(%rdx)
          
          chunk->owner = thread;
  4016c4:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016c8:	8b 55 d0             	mov    -0x30(%rbp),%edx
  4016cb:	89 50 14             	mov    %edx,0x14(%rax)
          int start = chunk->start;
  4016ce:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016d2:	48 8b 00             	mov    (%rax),%rax
  4016d5:	89 45 d4             	mov    %eax,-0x2c(%rbp)
          data->threads[thread].start = start;
  4016d8:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016dc:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016e0:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016e3:	48 98                	cltq
  4016e5:	48 c1 e0 0a          	shl    $0xa,%rax
  4016e9:	48 01 c2             	add    %rax,%rdx
  4016ec:	8b 45 d4             	mov    -0x2c(%rbp),%eax
  4016ef:	89 42 14             	mov    %eax,0x14(%rdx)
          
          int end = chunk->end;
  4016f2:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016f6:	48 8b 40 08          	mov    0x8(%rax),%rax
  4016fa:	89 45 d8             	mov    %eax,-0x28(%rbp)
          data->threads[thread].end = end;
  4016fd:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401701:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401705:	8b 45 d0             	mov    -0x30(%rbp),%eax
  401708:	48 98                	cltq
  40170a:	48 c1 e0 0a          	shl    $0xa,%rax
  40170e:	48 01 c2             	add    %rax,%rdx
  401711:	8b 45 d8             	mov    -0x28(%rbp),%eax
  401714:	89 42 18             	mov    %eax,0x18(%rdx)
        // printf("reader giving %d between %ld and %ld\n", x, start, end);
        
         // clock_gettime(CLOCK_MONOTONIC_RAW, &data->main->works[start].created);
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  401717:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40171b:	48 8b 50 30          	mov    0x30(%rax),%rdx
  40171f:	8b 45 d0             	mov    -0x30(%rbp),%eax
  401722:	48 98                	cltq
  401724:	48 c1 e0 0a          	shl    $0xa,%rax
  401728:	48 01 d0             	add    %rdx,%rax
  40172b:	8b 90 c8 00 00 00    	mov    0xc8(%rax),%edx
  401731:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401735:	48 8b 48 30          	mov    0x30(%rax),%rcx
  401739:	8b 45 d0             	mov    -0x30(%rbp),%eax
  40173c:	48 98                	cltq
  40173e:	48 c1 e0 0a          	shl    $0xa,%rax
  401742:	48 01 c8             	add    %rcx,%rax
  401745:	83 ca 10             	or     $0x10,%edx
  401748:	89 90 c8 00 00 00    	mov    %edx,0xc8(%rax)
        for (int x = 0; x < readers ; x++) {
  40174e:	83 45 c0 01          	addl   $0x1,-0x40(%rbp)
  401752:	8b 45 b0             	mov    -0x50(%rbp),%eax
  401755:	39 45 c0             	cmp    %eax,-0x40(%rbp)
  401758:	0f 8c e4 fe ff ff    	jl     401642 <singlewriter+0xcd>
  40175e:	eb 01                	jmp    401761 <singlewriter+0x1ec>
                  break;
  401760:	90                   	nop
       // printf("read newmask ORed with %d\n", data->threads[thread].newmask);
        }
      
   for (int x = 0; x < writers ; x++) {
  401761:	c7 45 c4 00 00 00 00 	movl   $0x0,-0x3c(%rbp)
  401768:	e9 10 01 00 00       	jmp    40187d <singlewriter+0x308>
                if (assignedchunk  == availableidx) {
  40176d:	8b 45 b8             	mov    -0x48(%rbp),%eax
  401770:	39 45 bc             	cmp    %eax,-0x44(%rbp)
  401773:	0f 84 12 01 00 00    	je     40188b <singlewriter+0x316>
                  
                 //printf("not enough space writer %d %d\n", assignedchunk, availableidx);
                  break;
                }
          int thread = readywriters[x];
  401779:	8b 45 c4             	mov    -0x3c(%rbp),%eax
  40177c:	48 98                	cltq
  40177e:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401786:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40178a:	48 01 d0             	add    %rdx,%rax
  40178d:	8b 00                	mov    (%rax),%eax
  40178f:	89 45 dc             	mov    %eax,-0x24(%rbp)
     
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401792:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401796:	48 8b 88 a0 00 00 00 	mov    0xa0(%rax),%rcx
  40179d:	8b 45 bc             	mov    -0x44(%rbp),%eax
  4017a0:	8d 50 01             	lea    0x1(%rax),%edx
  4017a3:	89 55 bc             	mov    %edx,-0x44(%rbp)
  4017a6:	48 98                	cltq
  4017a8:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4017b0:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  4017b4:	48 01 d0             	add    %rdx,%rax
  4017b7:	48 8b 00             	mov    (%rax),%rax
  4017ba:	48 c1 e0 05          	shl    $0x5,%rax
  4017be:	48 01 c8             	add    %rcx,%rax
  4017c1:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
    
      chunk->available = WRITING;
  4017c5:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017c9:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
          data->threads[thread].writing = chunk;
  4017d0:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4017d4:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4017d8:	8b 45 dc             	mov    -0x24(%rbp),%eax
  4017db:	48 98                	cltq
  4017dd:	48 c1 e0 0a          	shl    $0xa,%rax
  4017e1:	48 01 c2             	add    %rax,%rdx
  4017e4:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017e8:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
          chunk->owner = thread;
  4017ef:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017f3:	8b 55 dc             	mov    -0x24(%rbp),%edx
  4017f6:	89 50 14             	mov    %edx,0x14(%rax)
          int start = chunk->start;
  4017f9:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017fd:	48 8b 00             	mov    (%rax),%rax
  401800:	89 45 e0             	mov    %eax,-0x20(%rbp)
          data->threads[thread].publishstart = start;
  401803:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401807:	48 8b 50 30          	mov    0x30(%rax),%rdx
  40180b:	8b 45 dc             	mov    -0x24(%rbp),%eax
  40180e:	48 98                	cltq
  401810:	48 c1 e0 0a          	shl    $0xa,%rax
  401814:	48 01 c2             	add    %rax,%rdx
  401817:	8b 45 e0             	mov    -0x20(%rbp),%eax
  40181a:	89 42 40             	mov    %eax,0x40(%rdx)
          
          int end = chunk->end;
  40181d:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401821:	48 8b 40 08          	mov    0x8(%rax),%rax
  401825:	89 45 e4             	mov    %eax,-0x1c(%rbp)
          data->threads[thread].publishend = end;
  401828:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40182c:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401830:	8b 45 dc             	mov    -0x24(%rbp),%eax
  401833:	48 98                	cltq
  401835:	48 c1 e0 0a          	shl    $0xa,%rax
  401839:	48 01 c2             	add    %rax,%rdx
  40183c:	8b 45 e4             	mov    -0x1c(%rbp),%eax
  40183f:	89 42 44             	mov    %eax,0x44(%rdx)
        //  printf("writer giving %d between %ld and %ld\n", available[assignedchunk], start, end);
          // asm volatile ("sfence" ::: "memory");
     
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401842:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401846:	48 8b 50 30          	mov    0x30(%rax),%rdx
  40184a:	8b 45 dc             	mov    -0x24(%rbp),%eax
  40184d:	48 98                	cltq
  40184f:	48 c1 e0 0a          	shl    $0xa,%rax
  401853:	48 01 d0             	add    %rdx,%rax
  401856:	8b 90 c8 00 00 00    	mov    0xc8(%rax),%edx
  40185c:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401860:	48 8b 48 30          	mov    0x30(%rax),%rcx
  401864:	8b 45 dc             	mov    -0x24(%rbp),%eax
  401867:	48 98                	cltq
  401869:	48 c1 e0 0a          	shl    $0xa,%rax
  40186d:	48 01 c8             	add    %rcx,%rax
  401870:	83 ca 20             	or     $0x20,%edx
  401873:	89 90 c8 00 00 00    	mov    %edx,0xc8(%rax)
   for (int x = 0; x < writers ; x++) {
  401879:	83 45 c4 01          	addl   $0x1,-0x3c(%rbp)
  40187d:	8b 45 b4             	mov    -0x4c(%rbp),%eax
  401880:	39 45 c4             	cmp    %eax,-0x3c(%rbp)
  401883:	0f 8c e4 fe ff ff    	jl     40176d <singlewriter+0x1f8>
  401889:	eb 01                	jmp    40188c <singlewriter+0x317>
                  break;
  40188b:	90                   	nop
     //printf("write newmask ORed with %ld\n", data->threads[thread].newmask);
        
   } 
      for (int x = 0; x < data->threadsize ; x++) {
  40188c:	c7 45 c8 00 00 00 00 	movl   $0x0,-0x38(%rbp)
  401893:	eb 63                	jmp    4018f8 <singlewriter+0x383>
        if (data->threads[x].newmask != 0) {
  401895:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401899:	48 8b 50 30          	mov    0x30(%rax),%rdx
  40189d:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018a0:	48 98                	cltq
  4018a2:	48 c1 e0 0a          	shl    $0xa,%rax
  4018a6:	48 01 d0             	add    %rdx,%rax
  4018a9:	8b 80 c8 00 00 00    	mov    0xc8(%rax),%eax
  4018af:	85 c0                	test   %eax,%eax
  4018b1:	74 41                	je     4018f4 <singlewriter+0x37f>
         // printf("thread %d %ld is now %ld\n", x, data->threads[x].ready, data->threads[x].newmask);
          data->threads[x].readies[x] = data->threads[x].newmask;
  4018b3:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018b7:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4018bb:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018be:	48 98                	cltq
  4018c0:	48 c1 e0 0a          	shl    $0xa,%rax
  4018c4:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
  4018c8:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018cc:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4018d0:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018d3:	48 98                	cltq
  4018d5:	48 c1 e0 0a          	shl    $0xa,%rax
  4018d9:	48 01 d0             	add    %rdx,%rax
  4018dc:	48 8b 50 20          	mov    0x20(%rax),%rdx
  4018e0:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018e3:	48 98                	cltq
  4018e5:	48 c1 e0 02          	shl    $0x2,%rax
  4018e9:	48 01 c2             	add    %rax,%rdx
  4018ec:	8b 81 c8 00 00 00    	mov    0xc8(%rcx),%eax
  4018f2:	89 02                	mov    %eax,(%rdx)
      for (int x = 0; x < data->threadsize ; x++) {
  4018f4:	83 45 c8 01          	addl   $0x1,-0x38(%rbp)
  4018f8:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018fc:	8b 40 68             	mov    0x68(%rax),%eax
  4018ff:	39 45 c8             	cmp    %eax,-0x38(%rbp)
  401902:	7c 91                	jl     401895 <singlewriter+0x320>
        
          
        }
      }
  // clock_gettime(CLOCK_MONOTONIC_RAW, &data->wassign);
  return 0;
  401904:	b8 00 00 00 00       	mov    $0x0,%eax
}
  401909:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  40190d:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401916:	74 05                	je     40191d <singlewriter+0x3a8>
  401918:	e8 53 f7 ff ff       	call   401070 <__stack_chk_fail@plt>
  40191d:	c9                   	leave
  40191e:	c3                   	ret

000000000040191f <threadwork>:

int * threadwork(struct Data * data) {
  40191f:	55                   	push   %rbp
  401920:	48 89 e5             	mov    %rsp,%rbp
  401923:	48 81 ec 90 00 00 00 	sub    $0x90,%rsp
  40192a:	48 89 bd 78 ff ff ff 	mov    %rdi,-0x88(%rbp)
  401931:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40193a:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  40193e:	31 c0                	xor    %eax,%eax
  int cursorlimit = 5;
  401940:	c7 45 a4 05 00 00 00 	movl   $0x5,-0x5c(%rbp)
  int epochsize = 1;
  401947:	c7 45 a8 01 00 00 00 	movl   $0x1,-0x58(%rbp)
  int epochwidth = 0xff;
  40194e:	c7 45 ac ff 00 00 00 	movl   $0xff,-0x54(%rbp)

//printf("%ld %ld w%d\n", lastwrite, data->prevwrite, data->threadindex);
 //if (lastwrite != data->prevwrite) {
   
    uint64_t rsp;
    asm( "mov %%rsp, %0" : "=rm" ( rsp ));
  401955:	48 89 e0             	mov    %rsp,%rax
  401958:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
  // switch_to(struct Coroutine * coroutines, int index
  //printf("table %x\n", (void *)data->coroutines);
 // printf("coroutine 3 %x\n", &data->coroutines[3]);
 // printf("coroutine eip %lx\n", data->coroutines[3].eip);
 // printf("coroutine data %lx\n", data->coroutines[3].data); 
  switch_to(data->coroutines, 3, data->scheduler);  
  40195c:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401963:	48 8b 90 c8 03 00 00 	mov    0x3c8(%rax),%rdx
  40196a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401971:	48 8b 80 c0 03 00 00 	mov    0x3c0(%rax),%rax
  401978:	be 03 00 00 00       	mov    $0x3,%esi
  40197d:	48 89 c7             	mov    %rax,%rdi
  401980:	e8 7e 1d 00 00       	call   403703 <switch_to>
  //printf("finished coroutine\n");
  //printf("%ld %ld w%d\n", lastwrite, data->prevwrite, data->threadindex);
     
       
clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401985:	48 8d 45 e0          	lea    -0x20(%rbp),%rax
  401989:	48 89 c6             	mov    %rax,%rsi
  40198c:	bf 04 00 00 00       	mov    $0x4,%edi
  401991:	e8 ba f6 ff ff       	call   401050 <clock_gettime@plt>
  //if (data->threadindex % 2 == 0) {
   
  if (data->running == 2) {
  401996:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  40199d:	8b 40 5c             	mov    0x5c(%rax),%eax
  4019a0:	83 f8 02             	cmp    $0x2,%eax
  4019a3:	0f 85 9f 01 00 00    	jne    401b48 <threadwork+0x229>
  //if (data ->threadindex == 0 ) {
      

   for (int x = 0 ; x < data->threadsize ; x++) {
  4019a9:	c7 45 98 00 00 00 00 	movl   $0x0,-0x68(%rbp)
  4019b0:	e9 50 01 00 00       	jmp    401b05 <threadwork+0x1e6>
      
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  4019b5:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019bc:	48 8b 40 28          	mov    0x28(%rax),%rax
  4019c0:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  4019c7:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019ce:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  4019d4:	c1 e0 07             	shl    $0x7,%eax
  4019d7:	48 98                	cltq
  4019d9:	48 c1 e0 03          	shl    $0x3,%rax
  4019dd:	48 01 d0             	add    %rdx,%rax
  4019e0:	48 8b 00             	mov    (%rax),%rax
  4019e3:	8b 55 a8             	mov    -0x58(%rbp),%edx
  4019e6:	48 63 fa             	movslq %edx,%rdi
  4019e9:	48 99                	cqto
  4019eb:	48 f7 ff             	idiv   %rdi
  4019ee:	48 89 c2             	mov    %rax,%rdx
  4019f1:	8b 45 ac             	mov    -0x54(%rbp),%eax
  4019f4:	48 63 c8             	movslq %eax,%rcx
  4019f7:	48 89 d0             	mov    %rdx,%rax
  4019fa:	48 99                	cqto
  4019fc:	48 f7 f9             	idiv   %rcx
  4019ff:	48 89 d0             	mov    %rdx,%rax
  401a02:	89 45 9c             	mov    %eax,-0x64(%rbp)
    
      //  buffer = data->mystream << 24 | ( global << 16) | data->threadindex << 8 | data->writecursor % 0xff;
    int cursor = data->writecursor;
  401a05:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a0c:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401a12:	89 45 a0             	mov    %eax,-0x60(%rbp)
    //cursor = 0;
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  401a15:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a1c:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401a22:	c1 e0 18             	shl    $0x18,%eax
  401a25:	89 c2                	mov    %eax,%edx
  401a27:	8b 45 9c             	mov    -0x64(%rbp),%eax
  401a2a:	c1 e0 10             	shl    $0x10,%eax
  401a2d:	89 d6                	mov    %edx,%esi
  401a2f:	09 c6                	or     %eax,%esi
  401a31:	8b 45 a0             	mov    -0x60(%rbp),%eax
  401a34:	48 63 d0             	movslq %eax,%rdx
  401a37:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401a3e:	48 c1 ea 20          	shr    $0x20,%rdx
  401a42:	01 c2                	add    %eax,%edx
  401a44:	c1 fa 07             	sar    $0x7,%edx
  401a47:	89 c7                	mov    %eax,%edi
  401a49:	c1 ff 1f             	sar    $0x1f,%edi
  401a4c:	89 d1                	mov    %edx,%ecx
  401a4e:	29 f9                	sub    %edi,%ecx
  401a50:	89 ca                	mov    %ecx,%edx
  401a52:	c1 e2 08             	shl    $0x8,%edx
  401a55:	29 ca                	sub    %ecx,%edx
  401a57:	29 d0                	sub    %edx,%eax
  401a59:	89 c1                	mov    %eax,%ecx
  401a5b:	89 f0                	mov    %esi,%eax
  401a5d:	09 c8                	or     %ecx,%eax
  401a5f:	48 98                	cltq
  401a61:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
      buffer = data->mystream << 24 | ( (data->main->globalwrite[data->mystream * 128] / (data->threadsize)) % 0xff) << 16 | data->writecursor;
    }
    */
      // printf("%x\n", buffer);
        // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
  struct Data * thread = &data->threads[data->threadindex];
  401a65:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a6c:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401a70:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a77:	8b 40 64             	mov    0x64(%rax),%eax
  401a7a:	48 98                	cltq
  401a7c:	48 c1 e0 0a          	shl    $0xa,%rax
  401a80:	48 01 d0             	add    %rdx,%rax
  401a83:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
  epoch->buffer = buffer;
  epoch->set = 1;
  }
    
     // printf("alrrady filled\n");
  if (data->main->works[buffer] != -1) {
  401a87:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a8e:	48 8b 40 28          	mov    0x28(%rax),%rax
  401a92:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401a96:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401a9a:	48 01 d0             	add    %rdx,%rax
  401a9d:	0f b6 00             	movzbl (%rax),%eax
  401aa0:	3c ff                	cmp    $0xff,%al
  401aa2:	74 1a                	je     401abe <threadwork+0x19f>
    
    data->freq_writes++;
  401aa4:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401aab:	48 8b 40 50          	mov    0x50(%rax),%rax
  401aaf:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401ab3:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401aba:	48 89 50 50          	mov    %rdx,0x50(%rax)
  }
  data->main->works[buffer] = data->threadindex;
  401abe:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ac5:	8b 50 64             	mov    0x64(%rax),%edx
  401ac8:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401acf:	48 8b 40 28          	mov    0x28(%rax),%rax
  401ad3:	48 8b 48 70          	mov    0x70(%rax),%rcx
  401ad7:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401adb:	48 01 c8             	add    %rcx,%rax
  401ade:	88 10                	mov    %dl,(%rax)
         
         
  //  data->prevread = data->main->currentread;
     
     
    data->writecursor = (data->writecursor + 1) % cursorlimit;
  401ae0:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ae7:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401aed:	83 c0 01             	add    $0x1,%eax
  401af0:	99                   	cltd
  401af1:	f7 7d a4             	idivl  -0x5c(%rbp)
  401af4:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401afb:	89 90 80 01 00 00    	mov    %edx,0x180(%rax)
   for (int x = 0 ; x < data->threadsize ; x++) {
  401b01:	83 45 98 01          	addl   $0x1,-0x68(%rbp)
  401b05:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b0c:	8b 40 68             	mov    0x68(%rax),%eax
  401b0f:	39 45 98             	cmp    %eax,-0x68(%rbp)
  401b12:	0f 8c 9d fe ff ff    	jl     4019b5 <threadwork+0x96>
    
   }
      
    __atomic_fetch_add(&data->main->globalwrite[data->mystream * 128], 1, __ATOMIC_RELAXED);
  401b18:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b1f:	48 8b 40 28          	mov    0x28(%rax),%rax
  401b23:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401b2a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b31:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401b37:	c1 e0 07             	shl    $0x7,%eax
  401b3a:	48 98                	cltq
  401b3c:	48 c1 e0 03          	shl    $0x3,%rax
  401b40:	48 01 d0             	add    %rdx,%rax
  401b43:	f0 48 83 00 01       	lock addq $0x1,(%rax)
//}
  } 
  ///else {
  long thisgroup = data->main->globalwrite[data->mystream * 128] / epochsize;
  401b48:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b4f:	48 8b 40 28          	mov    0x28(%rax),%rax
  401b53:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401b5a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b61:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401b67:	c1 e0 07             	shl    $0x7,%eax
  401b6a:	48 98                	cltq
  401b6c:	48 c1 e0 03          	shl    $0x3,%rax
  401b70:	48 01 d0             	add    %rdx,%rax
  401b73:	48 8b 00             	mov    (%rax),%rax
  401b76:	8b 55 a8             	mov    -0x58(%rbp),%edx
  401b79:	48 63 fa             	movslq %edx,%rdi
  401b7c:	48 99                	cqto
  401b7e:	48 f7 ff             	idiv   %rdi
  401b81:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
  
  if (thisgroup != data->lastgroup) {
  401b85:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b8c:	8b 80 88 03 00 00    	mov    0x388(%rax),%eax
  401b92:	48 98                	cltq
  401b94:	48 39 45 c8          	cmp    %rax,-0x38(%rbp)
  401b98:	74 11                	je     401bab <threadwork+0x28c>
     // printf("ndw group\n");
      data->writecursor = 0;
  401b9a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ba1:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
        epoch->thread = data->threadindex;
        epoch->stream = data->mystream;
        epoch->set = 1;
     }
   }
   data->lastgroup = thisgroup;
  401bab:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
  401baf:	89 c2                	mov    %eax,%edx
  401bb1:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bb8:	89 90 88 03 00 00    	mov    %edx,0x388(%rax)
  //}
  
 //if (lastread != data->prevread)
 // {
   //printf("%ld  %ld r%d\n", data->main->currentread, data->prevread, data->threadindex);
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  401bbe:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bc5:	48 8b 40 28          	mov    0x28(%rax),%rax
  401bc9:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401bd0:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bd7:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401bdd:	c1 e0 07             	shl    $0x7,%eax
  401be0:	48 98                	cltq
  401be2:	48 c1 e0 03          	shl    $0x3,%rax
  401be6:	48 01 d0             	add    %rdx,%rax
  401be9:	48 8b 00             	mov    (%rax),%rax
  401bec:	48 89 45 d0          	mov    %rax,-0x30(%rbp)
  
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
  401bf0:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bf7:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401bfe:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c05:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401c0b:	48 63 d0             	movslq %eax,%rdx
  401c0e:	48 89 d0             	mov    %rdx,%rax
  401c11:	48 01 c0             	add    %rax,%rax
  401c14:	48 01 d0             	add    %rdx,%rax
  401c17:	48 c1 e0 02          	shl    $0x2,%rax
  401c1b:	48 01 c8             	add    %rcx,%rax
  401c1e:	8b 00                	mov    (%rax),%eax
  401c20:	48 98                	cltq
  401c22:	48 39 45 d0          	cmp    %rax,-0x30(%rbp)
  401c26:	7f 0b                	jg     401c33 <threadwork+0x314>
  401c28:	48 83 7d d0 00       	cmpq   $0x0,-0x30(%rbp)
  401c2d:	0f 85 f9 02 00 00    	jne    401f2c <threadwork+0x60d>
    for (int x = 0; x < data->threadsize - 1; x++) {
  401c33:	c7 45 94 00 00 00 00 	movl   $0x0,-0x6c(%rbp)
  401c3a:	e9 d7 02 00 00       	jmp    401f16 <threadwork+0x5f7>
  // printf("%d\n", thiswrite);
   data->freq++;
  401c3f:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c46:	48 8b 40 48          	mov    0x48(%rax),%rax
  401c4a:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401c4e:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c55:	48 89 50 48          	mov    %rdx,0x48(%rax)
  
        
      
          
            
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  401c59:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c60:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401c67:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c6e:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401c74:	48 63 d0             	movslq %eax,%rdx
  401c77:	48 89 d0             	mov    %rdx,%rax
  401c7a:	48 01 c0             	add    %rax,%rax
  401c7d:	48 01 d0             	add    %rdx,%rax
  401c80:	48 c1 e0 02          	shl    $0x2,%rax
  401c84:	48 01 c8             	add    %rcx,%rax
  401c87:	8b 00                	mov    (%rax),%eax
  401c89:	99                   	cltd
  401c8a:	f7 7d a8             	idivl  -0x58(%rbp)
  401c8d:	83 e8 01             	sub    $0x1,%eax
  401c90:	99                   	cltd
  401c91:	f7 7d ac             	idivl  -0x54(%rbp)
  401c94:	89 d0                	mov    %edx,%eax
  401c96:	48 98                	cltq
  401c98:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
        //long past = (((data->globalread[data->laststream]).global % epochwidth;
            if (past < 0) {
  401c9c:	48 83 7d b0 00       	cmpq   $0x0,-0x50(%rbp)
  401ca1:	79 08                	jns    401cab <threadwork+0x38c>
              past = 0;
  401ca3:	48 c7 45 b0 00 00 00 00 	movq   $0x0,-0x50(%rbp)
            }
            
            // long buffer = (data->threadindex << 24) | (data->main->globalwrite % 0xf) << 16 | (data->main->writecursor % 0xf);
        
       // buffer = data->laststream << 24 | (past << 16) | data->globalread[data->laststream].thread << 8, data->globalread[data->laststream].cursor % 0xff;
    int cursor = data->globalread[data->laststream].cursor;
  401cab:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cb2:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401cb9:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cc0:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401cc6:	48 63 d0             	movslq %eax,%rdx
  401cc9:	48 89 d0             	mov    %rdx,%rax
  401ccc:	48 01 c0             	add    %rax,%rax
  401ccf:	48 01 d0             	add    %rdx,%rax
  401cd2:	48 c1 e0 02          	shl    $0x2,%rax
  401cd6:	48 01 c8             	add    %rcx,%rax
  401cd9:	8b 40 04             	mov    0x4(%rax),%eax
  401cdc:	89 45 8c             	mov    %eax,-0x74(%rbp)
    //cursor = 0;
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  401cdf:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ce6:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401cec:	c1 e0 18             	shl    $0x18,%eax
  401cef:	48 63 d0             	movslq %eax,%rdx
  401cf2:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
  401cf6:	48 c1 e0 10          	shl    $0x10,%rax
  401cfa:	48 89 d6             	mov    %rdx,%rsi
  401cfd:	48 09 c6             	or     %rax,%rsi
  401d00:	8b 45 8c             	mov    -0x74(%rbp),%eax
  401d03:	48 63 d0             	movslq %eax,%rdx
  401d06:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401d0d:	48 c1 ea 20          	shr    $0x20,%rdx
  401d11:	01 c2                	add    %eax,%edx
  401d13:	c1 fa 07             	sar    $0x7,%edx
  401d16:	89 c1                	mov    %eax,%ecx
  401d18:	c1 f9 1f             	sar    $0x1f,%ecx
  401d1b:	29 ca                	sub    %ecx,%edx
  401d1d:	89 d1                	mov    %edx,%ecx
  401d1f:	c1 e1 08             	shl    $0x8,%ecx
  401d22:	29 d1                	sub    %edx,%ecx
  401d24:	29 c8                	sub    %ecx,%eax
  401d26:	89 c2                	mov    %eax,%edx
  401d28:	48 63 c2             	movslq %edx,%rax
  401d2b:	48 09 f0             	or     %rsi,%rax
  401d2e:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    access->cursor = data->globalread[data->laststream].cursor % 0xff;
    access->set = 1;
    data->cread = (data->cread + 1) % data->accesssize;
  }
    
    int thistream = data->laststream; 
  401d32:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d39:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401d3f:	89 45 90             	mov    %eax,-0x70(%rbp)
                // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
                //&data->threads[data->threadindex];

        // printf("%d\n", data->main->works[buffer]);
    
        if (data->main->works[buffer] != -1) {
  401d42:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d49:	48 8b 40 28          	mov    0x28(%rax),%rax
  401d4d:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401d51:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401d55:	48 01 d0             	add    %rdx,%rax
  401d58:	0f b6 00             	movzbl (%rax),%eax
  401d5b:	3c ff                	cmp    $0xff,%al
  401d5d:	74 39                	je     401d98 <threadwork+0x479>
          data->successreads++;
  401d5f:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d66:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  401d6d:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401d71:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d78:	48 89 90 98 03 00 00 	mov    %rdx,0x398(%rax)
          
          data->main->works[buffer] = -1;
  401d7f:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d86:	48 8b 40 28          	mov    0x28(%rax),%rax
  401d8a:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401d8e:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401d92:	48 01 d0             	add    %rdx,%rax
  401d95:	c6 00 ff             	movb   $0xff,(%rax)
  
    
    
      
    
    if (data->globalread[thistream].cursor < cursorlimit) {
  401d98:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d9f:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401da6:	8b 45 90             	mov    -0x70(%rbp),%eax
  401da9:	48 63 d0             	movslq %eax,%rdx
  401dac:	48 89 d0             	mov    %rdx,%rax
  401daf:	48 01 c0             	add    %rax,%rax
  401db2:	48 01 d0             	add    %rdx,%rax
  401db5:	48 c1 e0 02          	shl    $0x2,%rax
  401db9:	48 01 c8             	add    %rcx,%rax
  401dbc:	8b 40 04             	mov    0x4(%rax),%eax
  401dbf:	39 45 a4             	cmp    %eax,-0x5c(%rbp)
  401dc2:	7e 7c                	jle    401e40 <threadwork+0x521>
    
      data->globalread[thistream].global++;
  401dc4:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401dcb:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401dd2:	8b 45 90             	mov    -0x70(%rbp),%eax
  401dd5:	48 63 d0             	movslq %eax,%rdx
  401dd8:	48 89 d0             	mov    %rdx,%rax
  401ddb:	48 01 c0             	add    %rax,%rax
  401dde:	48 01 d0             	add    %rdx,%rax
  401de1:	48 c1 e0 02          	shl    $0x2,%rax
  401de5:	48 01 c8             	add    %rcx,%rax
  401de8:	8b 10                	mov    (%rax),%edx
  401dea:	83 c2 01             	add    $0x1,%edx
  401ded:	89 10                	mov    %edx,(%rax)
        
        
      data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1);
  401def:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401df6:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401dfd:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e00:	48 63 d0             	movslq %eax,%rdx
  401e03:	48 89 d0             	mov    %rdx,%rax
  401e06:	48 01 c0             	add    %rax,%rax
  401e09:	48 01 d0             	add    %rdx,%rax
  401e0c:	48 c1 e0 02          	shl    $0x2,%rax
  401e10:	48 01 c8             	add    %rcx,%rax
  401e13:	8b 48 04             	mov    0x4(%rax),%ecx
  401e16:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e1d:	48 8b b0 48 03 00 00 	mov    0x348(%rax),%rsi
  401e24:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e27:	48 63 d0             	movslq %eax,%rdx
  401e2a:	48 89 d0             	mov    %rdx,%rax
  401e2d:	48 01 c0             	add    %rax,%rax
  401e30:	48 01 d0             	add    %rdx,%rax
  401e33:	48 c1 e0 02          	shl    $0x2,%rax
  401e37:	48 01 f0             	add    %rsi,%rax
  401e3a:	8d 51 01             	lea    0x1(%rcx),%edx
  401e3d:	89 50 04             	mov    %edx,0x4(%rax)
      
      }
    
    if (data->globalread[thistream].cursor == cursorlimit) {
  401e40:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e47:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401e4e:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e51:	48 63 d0             	movslq %eax,%rdx
  401e54:	48 89 d0             	mov    %rdx,%rax
  401e57:	48 01 c0             	add    %rax,%rax
  401e5a:	48 01 d0             	add    %rdx,%rax
  401e5d:	48 c1 e0 02          	shl    $0x2,%rax
  401e61:	48 01 c8             	add    %rcx,%rax
  401e64:	8b 40 04             	mov    0x4(%rax),%eax
  401e67:	39 45 a4             	cmp    %eax,-0x5c(%rbp)
  401e6a:	75 48                	jne    401eb4 <threadwork+0x595>
      
      data->laststream = (data->laststream + 1);
  401e6c:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e73:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401e79:	8d 50 01             	lea    0x1(%rax),%edx
  401e7c:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e83:	89 90 90 03 00 00    	mov    %edx,0x390(%rax)
     // data->globalread[thistream].global++;
data->globalread[thistream].cursor = 0;
  401e89:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e90:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401e97:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e9a:	48 63 d0             	movslq %eax,%rdx
  401e9d:	48 89 d0             	mov    %rdx,%rax
  401ea0:	48 01 c0             	add    %rax,%rax
  401ea3:	48 01 d0             	add    %rdx,%rax
  401ea6:	48 c1 e0 02          	shl    $0x2,%rax
  401eaa:	48 01 c8             	add    %rcx,%rax
  401ead:	c7 40 04 00 00 00 00 	movl   $0x0,0x4(%rax)
    }
    
    if (data->laststream == data->mystream) {
  401eb4:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ebb:	8b 90 90 03 00 00    	mov    0x390(%rax),%edx
  401ec1:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ec8:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401ece:	39 c2                	cmp    %eax,%edx
  401ed0:	75 1d                	jne    401eef <threadwork+0x5d0>
      data->laststream = data->laststream + 1;
  401ed2:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ed9:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401edf:	8d 50 01             	lea    0x1(%rax),%edx
  401ee2:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ee9:	89 90 90 03 00 00    	mov    %edx,0x390(%rax)
     // data->globalread[data->laststream].cursor = 0;
    }
    if (data->laststream == 5) {
  401eef:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ef6:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401efc:	83 f8 05             	cmp    $0x5,%eax
  401eff:	75 11                	jne    401f12 <threadwork+0x5f3>
       data->laststream = 1;
  401f01:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401f08:	c7 80 90 03 00 00 01 00 00 00 	movl   $0x1,0x390(%rax)
    for (int x = 0; x < data->threadsize - 1; x++) {
  401f12:	83 45 94 01          	addl   $0x1,-0x6c(%rbp)
  401f16:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401f1d:	8b 40 68             	mov    0x68(%rax),%eax
  401f20:	83 e8 01             	sub    $0x1,%eax
  401f23:	39 45 94             	cmp    %eax,-0x6c(%rbp)
  401f26:	0f 8c 13 fd ff ff    	jl     401c3f <threadwork+0x320>
      
     //asm volatile ("sfence" ::: "memory");
  
      
       
}
  401f2c:	90                   	nop
  401f2d:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  401f31:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401f3a:	74 05                	je     401f41 <threadwork+0x622>
  401f3c:	e8 2f f1 ff ff       	call   401070 <__stack_chk_fail@plt>
  401f41:	c9                   	leave
  401f42:	c3                   	ret

0000000000401f43 <work2>:

void * work2(void * arg) {
  401f43:	55                   	push   %rbp
  401f44:	48 89 e5             	mov    %rsp,%rbp
  401f47:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  struct Data *data = (struct Data*) arg;
  401f4b:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401f4f:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  while (data->running == 1) {
  401f53:	eb 14                	jmp    401f69 <work2+0x26>
    asm volatile ("" ::: "memory");
      data->freq++;
  401f55:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f59:	48 8b 40 48          	mov    0x48(%rax),%rax
  401f5d:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401f61:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f65:	48 89 50 48          	mov    %rdx,0x48(%rax)
  while (data->running == 1) {
  401f69:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f6d:	8b 40 5c             	mov    0x5c(%rax),%eax
  401f70:	83 f8 01             	cmp    $0x1,%eax
  401f73:	74 e0                	je     401f55 <work2+0x12>
  }
  
}
  401f75:	90                   	nop
  401f76:	5d                   	pop    %rbp
  401f77:	c3                   	ret

0000000000401f78 <work>:

void * work(void * arg) {
  401f78:	55                   	push   %rbp
  401f79:	48 89 e5             	mov    %rsp,%rbp
  401f7c:	48 83 ec 50          	sub    $0x50,%rsp
  401f80:	48 89 7d b8          	mov    %rdi,-0x48(%rbp)

  
  int writers;
  int readers;
  struct Data *data = (struct Data*) arg;
  401f84:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401f88:	48 89 45 e0          	mov    %rax,-0x20(%rbp)
  printf("started thread %d\n", data->threadindex);
  401f8c:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401f90:	8b 40 64             	mov    0x64(%rax),%eax
  401f93:	89 c6                	mov    %eax,%esi
  401f95:	48 8d 05 a2 20 00 00 	lea    0x20a2(%rip),%rax        # 40403e <_IO_stdin_used+0x3e>
  401f9c:	48 89 c7             	mov    %rax,%rdi
  401f9f:	b8 00 00 00 00       	mov    $0x0,%eax
  401fa4:	e8 d7 f0 ff ff       	call   401080 <printf@plt>
  
  
  int found = 0;
  401fa9:	c7 45 c8 00 00 00 00 	movl   $0x0,-0x38(%rbp)
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  401fb0:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fb4:	8b 40 64             	mov    0x64(%rax),%eax
  401fb7:	8d 50 01             	lea    0x1(%rax),%edx
  401fba:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fbe:	8b 48 68             	mov    0x68(%rax),%ecx
  401fc1:	89 d0                	mov    %edx,%eax
  401fc3:	99                   	cltd
  401fc4:	f7 f9                	idiv   %ecx
  401fc6:	89 55 cc             	mov    %edx,-0x34(%rbp)
  int innerfind = 0;
  401fc9:	c7 45 d0 00 00 00 00 	movl   $0x0,-0x30(%rbp)
  
  
  
  
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  401fd0:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fd4:	48 8b 80 b8 00 00 00 	mov    0xb8(%rax),%rax
  401fdb:	48 83 c0 01          	add    $0x1,%rax
  401fdf:	be 08 00 00 00       	mov    $0x8,%esi
  401fe4:	48 89 c7             	mov    %rax,%rdi
  401fe7:	e8 e4 f0 ff ff       	call   4010d0 <calloc@plt>
  401fec:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  401ff0:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401ff4:	8b 40 68             	mov    0x68(%rax),%eax
  401ff7:	48 98                	cltq
  401ff9:	be 04 00 00 00       	mov    $0x4,%esi
  401ffe:	48 89 c7             	mov    %rax,%rdi
  402001:	e8 ca f0 ff ff       	call   4010d0 <calloc@plt>
  402006:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
  int * readywriters = calloc(data->threadsize, sizeof(int));
  40200a:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  40200e:	8b 40 68             	mov    0x68(%rax),%eax
  402011:	48 98                	cltq
  402013:	be 04 00 00 00       	mov    $0x4,%esi
  402018:	48 89 c7             	mov    %rax,%rdi
  40201b:	e8 b0 f0 ff ff       	call   4010d0 <calloc@plt>
  402020:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  
  
  int stop = 0;
  402024:	c7 45 d4 00 00 00 00 	movl   $0x0,-0x2c(%rbp)
  while (data->running > 0)  {
  40202b:	eb 25                	jmp    402052 <work+0xda>
    writers = 0;
  40202d:	c7 45 d8 00 00 00 00 	movl   $0x0,-0x28(%rbp)
    readers = 0;
  402034:	c7 45 dc 00 00 00 00 	movl   $0x0,-0x24(%rbp)
    stop = 0;
  40203b:	c7 45 d4 00 00 00 00 	movl   $0x0,-0x2c(%rbp)
    asm volatile ("":"=m" (data->running)::);
  402042:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
   // printf("write cycle\n");
    //memset(available, -1, data->threadsize);

      threadwork(data);
  402046:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  40204a:	48 89 c7             	mov    %rax,%rdi
  40204d:	e8 cd f8 ff ff       	call   40191f <threadwork>
  while (data->running > 0)  {
  402052:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402056:	8b 40 5c             	mov    0x5c(%rax),%eax
  402059:	85 c0                	test   %eax,%eax
  40205b:	7f d0                	jg     40202d <work+0xb5>
        for (int x = 0 ; x < data->worksize; x++) {
          data->main->works[x].available = 1;
        }
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
  40205d:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402061:	8b 40 64             	mov    0x64(%rax),%eax
  402064:	89 c6                	mov    %eax,%esi
  402066:	48 8d 05 e4 1f 00 00 	lea    0x1fe4(%rip),%rax        # 404051 <_IO_stdin_used+0x51>
  40206d:	48 89 c7             	mov    %rax,%rdi
  402070:	b8 00 00 00 00       	mov    $0x0,%eax
  402075:	e8 06 f0 ff ff       	call   401080 <printf@plt>
}
  40207a:	90                   	nop
  40207b:	c9                   	leave
  40207c:	c3                   	ret

000000000040207d <main>:

int main(int argc, char **argv) {
  40207d:	55                   	push   %rbp
  40207e:	48 89 e5             	mov    %rsp,%rbp
  402081:	53                   	push   %rbx
  402082:	48 81 ec 78 01 00 00 	sub    $0x178,%rsp
  402089:	89 bd 8c fe ff ff    	mov    %edi,-0x174(%rbp)
  40208f:	48 89 b5 80 fe ff ff 	mov    %rsi,-0x180(%rbp)
  402096:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40209f:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  4020a3:	31 c0                	xor    %eax,%eax
  int debug = 0;
  4020a5:	c7 85 a0 fe ff ff 00 00 00 00 	movl   $0x0,-0x160(%rbp)
  int seconds = DURATION;
  4020af:	c7 85 a4 fe ff ff 01 00 00 00 	movl   $0x1,-0x15c(%rbp)
  int worksize_each = 1;
  4020b9:	c7 85 94 fe ff ff 01 00 00 00 	movl   $0x1,-0x16c(%rbp)
  int threadsize = THREADS;
  4020c3:	c7 85 98 fe ff ff 0f 00 00 00 	movl   $0xf,-0x168(%rbp)
  
  int workers = threadsize - 1;
  4020cd:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4020d3:	83 e8 01             	sub    $0x1,%eax
  4020d6:	89 85 9c fe ff ff    	mov    %eax,-0x164(%rbp)
  printf("read mask %d\n", READ_MASK);
  4020dc:	be 08 00 00 00       	mov    $0x8,%esi
  4020e1:	48 8d 05 79 1f 00 00 	lea    0x1f79(%rip),%rax        # 404061 <_IO_stdin_used+0x61>
  4020e8:	48 89 c7             	mov    %rax,%rdi
  4020eb:	b8 00 00 00 00       	mov    $0x0,%eax
  4020f0:	e8 8b ef ff ff       	call   401080 <printf@plt>
  printf("write mask %d\n", WRITE_MASK);
  4020f5:	be 04 00 00 00       	mov    $0x4,%esi
  4020fa:	48 8d 05 6e 1f 00 00 	lea    0x1f6e(%rip),%rax        # 40406f <_IO_stdin_used+0x6f>
  402101:	48 89 c7             	mov    %rax,%rdi
  402104:	b8 00 00 00 00       	mov    $0x0,%eax
  402109:	e8 72 ef ff ff       	call   401080 <printf@plt>
  printf("prepwrite mask %d\n", PREP_WRITE_MASK);
  40210e:	be 20 00 00 00       	mov    $0x20,%esi
  402113:	48 8d 05 64 1f 00 00 	lea    0x1f64(%rip),%rax        # 40407e <_IO_stdin_used+0x7e>
  40211a:	48 89 c7             	mov    %rax,%rdi
  40211d:	b8 00 00 00 00       	mov    $0x0,%eax
  402122:	e8 59 ef ff ff       	call   401080 <printf@plt>
  printf("Starting %d workers\n", threadsize);
  402127:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40212d:	89 c6                	mov    %eax,%esi
  40212f:	48 8d 05 5b 1f 00 00 	lea    0x1f5b(%rip),%rax        # 404091 <_IO_stdin_used+0x91>
  402136:	48 89 c7             	mov    %rax,%rdi
  402139:	b8 00 00 00 00       	mov    $0x0,%eax
  40213e:	e8 3d ef ff ff       	call   401080 <printf@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  402143:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402149:	48 98                	cltq
  40214b:	be 08 00 00 00       	mov    $0x8,%esi
  402150:	48 89 c7             	mov    %rax,%rdi
  402153:	e8 78 ef ff ff       	call   4010d0 <calloc@plt>
  402158:	48 89 85 18 ff ff ff 	mov    %rax,-0xe8(%rbp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  40215f:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402165:	48 98                	cltq
  402167:	be 38 00 00 00       	mov    $0x38,%esi
  40216c:	48 89 c7             	mov    %rax,%rdi
  40216f:	e8 5c ef ff ff       	call   4010d0 <calloc@plt>
  402174:	48 89 85 f0 fe ff ff 	mov    %rax,-0x110(%rbp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  40217b:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402181:	48 98                	cltq
  402183:	48 c1 e0 0a          	shl    $0xa,%rax
  402187:	48 89 c6             	mov    %rax,%rsi
  40218a:	bf 01 00 00 00       	mov    $0x1,%edi
  40218f:	e8 3c ef ff ff       	call   4010d0 <calloc@plt>
  402194:	48 89 85 f8 fe ff ff 	mov    %rax,-0x108(%rbp)
  
  long offset = 0;
  40219b:	48 c7 85 00 ff ff ff 00 00 00 00 	movq   $0x0,-0x100(%rbp)
  long chunkslen = 0xffffffff;
  4021a6:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
  4021ab:	48 89 85 08 ff ff ff 	mov    %rax,-0xf8(%rbp)
  long worksize = chunkslen * worksize_each;
  4021b2:	8b 85 94 fe ff ff    	mov    -0x16c(%rbp),%eax
  4021b8:	48 98                	cltq
  4021ba:	48 8b 95 08 ff ff ff 	mov    -0xf8(%rbp),%rdx
  4021c1:	48 0f af c2          	imul   %rdx,%rax
  4021c5:	48 89 85 10 ff ff ff 	mov    %rax,-0xf0(%rbp)
  int buckets = worksize / threadsize;
  4021cc:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4021d2:	48 63 d8             	movslq %eax,%rbx
  4021d5:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  4021dc:	48 99                	cqto
  4021de:	48 f7 fb             	idiv   %rbx
  4021e1:	89 85 90 fe ff ff    	mov    %eax,-0x170(%rbp)
  long chunksize = ceil((double) worksize / (double) chunkslen);
  4021e7:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4021eb:	f2 48 0f 2a 85 10 ff ff ff 	cvtsi2sdq -0xf0(%rbp),%xmm0
  4021f4:	66 0f ef c9          	pxor   %xmm1,%xmm1
  4021f8:	f2 48 0f 2a 8d 08 ff ff ff 	cvtsi2sdq -0xf8(%rbp),%xmm1
  402201:	f2 0f 5e c1          	divsd  %xmm1,%xmm0
  402205:	66 48 0f 7e c0       	movq   %xmm0,%rax
  40220a:	66 48 0f 6e c0       	movq   %rax,%xmm0
  40220f:	e8 0c ef ff ff       	call   401120 <ceil@plt>
  402214:	f2 48 0f 2c c0       	cvttsd2si %xmm0,%rax
  402219:	48 89 85 38 ff ff ff 	mov    %rax,-0xc8(%rbp)
  char *works = calloc(worksize, sizeof(char));
  402220:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  402227:	be 01 00 00 00       	mov    $0x1,%esi
  40222c:	48 89 c7             	mov    %rax,%rdi
  40222f:	e8 9c ee ff ff       	call   4010d0 <calloc@plt>
  402234:	48 89 85 40 ff ff ff 	mov    %rax,-0xc0(%rbp)
  memset(works, -1, worksize);
  40223b:	48 8b 95 10 ff ff ff 	mov    -0xf0(%rbp),%rdx
  402242:	48 8b 85 40 ff ff ff 	mov    -0xc0(%rbp),%rax
  402249:	be ff ff ff ff       	mov    $0xffffffff,%esi
  40224e:	48 89 c7             	mov    %rax,%rdi
  402251:	e8 6a ee ff ff       	call   4010c0 <memset@plt>
  printf("Buffer size %ld\n", worksize);
  402256:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  40225d:	48 89 c6             	mov    %rax,%rsi
  402260:	48 8d 05 3f 1e 00 00 	lea    0x1e3f(%rip),%rax        # 4040a6 <_IO_stdin_used+0xa6>
  402267:	48 89 c7             	mov    %rax,%rdi
  40226a:	b8 00 00 00 00       	mov    $0x0,%eax
  40226f:	e8 0c ee ff ff       	call   401080 <printf@plt>
  int chunkindex = 0;
  402274:	c7 85 d4 fe ff ff 00 00 00 00 	movl   $0x0,-0x12c(%rbp)
  int * readcursors = calloc(threadsize, sizeof(int));
  40227e:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402284:	48 98                	cltq
  402286:	be 04 00 00 00       	mov    $0x4,%esi
  40228b:	48 89 c7             	mov    %rax,%rdi
  40228e:	e8 3d ee ff ff       	call   4010d0 <calloc@plt>
  402293:	48 89 85 48 ff ff ff 	mov    %rax,-0xb8(%rbp)
  int * writecursors = calloc(threadsize, sizeof(int));
  40229a:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4022a0:	48 98                	cltq
  4022a2:	be 04 00 00 00       	mov    $0x4,%esi
  4022a7:	48 89 c7             	mov    %rax,%rdi
  4022aa:	e8 21 ee ff ff       	call   4010d0 <calloc@plt>
  4022af:	48 89 85 50 ff ff ff 	mov    %rax,-0xb0(%rbp)
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4022b6:	be 20 00 00 00       	mov    $0x20,%esi
  4022bb:	bf 64 00 00 00       	mov    $0x64,%edi
  4022c0:	e8 0b ee ff ff       	call   4010d0 <calloc@plt>
  4022c5:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)

printf("offset %ld\n", offset);
  4022cc:	48 8b 85 00 ff ff ff 	mov    -0x100(%rbp),%rax
  4022d3:	48 89 c6             	mov    %rax,%rsi
  4022d6:	48 8d 05 da 1d 00 00 	lea    0x1dda(%rip),%rax        # 4040b7 <_IO_stdin_used+0xb7>
  4022dd:	48 89 c7             	mov    %rax,%rdi
  4022e0:	b8 00 00 00 00       	mov    $0x0,%eax
  4022e5:	e8 96 ed ff ff       	call   401080 <printf@plt>
  
printf("%ld chunks\n", chunkslen);
  4022ea:	48 8b 85 08 ff ff ff 	mov    -0xf8(%rbp),%rax
  4022f1:	48 89 c6             	mov    %rax,%rsi
  4022f4:	48 8d 05 c8 1d 00 00 	lea    0x1dc8(%rip),%rax        # 4040c3 <_IO_stdin_used+0xc3>
  4022fb:	48 89 c7             	mov    %rax,%rdi
  4022fe:	b8 00 00 00 00       	mov    $0x0,%eax
  402303:	e8 78 ed ff ff       	call   401080 <printf@plt>
 // for (int i = 0; i < worksize; i++) {
   // works[i].taskindex = 2;
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  402308:	c7 85 c4 fe ff ff 00 00 00 00 	movl   $0x0,-0x13c(%rbp)
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  402312:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402318:	48 98                	cltq
  40231a:	be 04 00 00 00       	mov    $0x4,%esi
  40231f:	48 89 c7             	mov    %rax,%rdi
  402322:	e8 a9 ed ff ff       	call   4010d0 <calloc@plt>
  402327:	48 89 85 60 ff ff ff 	mov    %rax,-0xa0(%rbp)
  
  long * globalwrite;
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  40232e:	48 8d 85 e0 fe ff ff 	lea    -0x120(%rbp),%rax
  402335:	ba 00 02 00 00       	mov    $0x200,%edx
  40233a:	be 80 00 00 00       	mov    $0x80,%esi
  40233f:	48 89 c7             	mov    %rax,%rdi
  402342:	e8 b9 ed ff ff       	call   401100 <posix_memalign@plt>
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  402347:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40234d:	48 98                	cltq
  40234f:	be 0c 00 00 00       	mov    $0xc,%esi
  402354:	48 89 c7             	mov    %rax,%rdi
  402357:	e8 74 ed ff ff       	call   4010d0 <calloc@plt>
  40235c:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
  data[0].works = works;
  402363:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40236a:	48 8b 95 40 ff ff ff 	mov    -0xc0(%rbp),%rdx
  402371:	48 89 50 70          	mov    %rdx,0x70(%rax)
  int accesssize = 100000000;
  402375:	c7 85 d8 fe ff ff 00 e1 f5 05 	movl   $0x5f5e100,-0x128(%rbp)
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  40237f:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  402385:	48 98                	cltq
  402387:	be 14 00 00 00       	mov    $0x14,%esi
  40238c:	48 89 c7             	mov    %rax,%rdi
  40238f:	e8 3c ed ff ff       	call   4010d0 <calloc@plt>
  402394:	48 89 85 70 ff ff ff 	mov    %rax,-0x90(%rbp)
  struct Access * writes = calloc(accesssize, sizeof(struct Access));
  40239b:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  4023a1:	48 98                	cltq
  4023a3:	be 14 00 00 00       	mov    $0x14,%esi
  4023a8:	48 89 c7             	mov    %rax,%rdi
  4023ab:	e8 20 ed ff ff       	call   4010d0 <calloc@plt>
  4023b0:	48 89 85 78 ff ff ff 	mov    %rax,-0x88(%rbp)

  

  
  
  for (int x = 0; x < threadsize ; x++) {
  4023b7:	c7 85 c8 fe ff ff 00 00 00 00 	movl   $0x0,-0x138(%rbp)
  4023c1:	e9 fb 06 00 00       	jmp    402ac1 <main+0xa44>
    
    struct Coroutine * cos = calloc(10, sizeof(struct Coroutine));
  4023c6:	be 20 00 00 00       	mov    $0x20,%esi
  4023cb:	bf 0a 00 00 00       	mov    $0xa,%edi
  4023d0:	e8 fb ec ff ff       	call   4010d0 <calloc@plt>
  4023d5:	48 89 45 a0          	mov    %rax,-0x60(%rbp)
    
    data[x].coroutines = cos;
  4023d9:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4023df:	48 98                	cltq
  4023e1:	48 c1 e0 0a          	shl    $0xa,%rax
  4023e5:	48 89 c2             	mov    %rax,%rdx
  4023e8:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4023ef:	48 01 c2             	add    %rax,%rdx
  4023f2:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  4023f6:	48 89 82 c0 03 00 00 	mov    %rax,0x3c0(%rdx)
    for (int y = 0; y < 10; y++ ) {
  4023fd:	c7 85 cc fe ff ff 00 00 00 00 	movl   $0x0,-0x134(%rbp)
  402407:	e9 9e 00 00 00       	jmp    4024aa <main+0x42d>
      char * stack;
      posix_memalign((void **)&stack, 16, 8016);
  40240c:	48 8d 45 d0          	lea    -0x30(%rbp),%rax
  402410:	ba 50 1f 00 00       	mov    $0x1f50,%edx
  402415:	be 10 00 00 00       	mov    $0x10,%esi
  40241a:	48 89 c7             	mov    %rax,%rdi
  40241d:	e8 de ec ff ff       	call   401100 <posix_memalign@plt>
      
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
  402422:	be 04 00 00 00       	mov    $0x4,%esi
  402427:	bf 01 00 00 00       	mov    $0x1,%edi
  40242c:	e8 9f ec ff ff       	call   4010d0 <calloc@plt>
  402431:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
      cos[y].data = codata; 
  402435:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  40243b:	48 98                	cltq
  40243d:	48 c1 e0 05          	shl    $0x5,%rax
  402441:	48 89 c2             	mov    %rax,%rdx
  402444:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  402448:	48 01 c2             	add    %rax,%rdx
  40244b:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  40244f:	48 89 42 18          	mov    %rax,0x18(%rdx)
      codata->running = 1;
  402453:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  402457:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
      cos[y].eip = (uint64_t)coroutine_func;
  40245d:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  402463:	48 98                	cltq
  402465:	48 c1 e0 05          	shl    $0x5,%rax
  402469:	48 89 c2             	mov    %rax,%rdx
  40246c:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  402470:	48 01 d0             	add    %rdx,%rax
  402473:	48 c7 c2 1d 12 40 00 	mov    $0x40121d,%rdx
  40247a:	48 89 50 10          	mov    %rdx,0x10(%rax)
      cos[y].rsp = stack + 8016;
  40247e:	48 8b 45 d0          	mov    -0x30(%rbp),%rax
  402482:	48 8d 90 50 1f 00 00 	lea    0x1f50(%rax),%rdx
  402489:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  40248f:	48 98                	cltq
  402491:	48 c1 e0 05          	shl    $0x5,%rax
  402495:	48 89 c1             	mov    %rax,%rcx
  402498:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  40249c:	48 01 c8             	add    %rcx,%rax
  40249f:	48 89 50 08          	mov    %rdx,0x8(%rax)
    for (int y = 0; y < 10; y++ ) {
  4024a3:	83 85 cc fe ff ff 01 	addl   $0x1,-0x134(%rbp)
  4024aa:	83 bd cc fe ff ff 09 	cmpl   $0x9,-0x134(%rbp)
  4024b1:	0f 8e 55 ff ff ff    	jle    40240c <main+0x38f>
    }
    struct Scheduler * scheduler = calloc(1, sizeof(struct Scheduler));
  4024b7:	be 08 00 00 00       	mov    $0x8,%esi
  4024bc:	bf 01 00 00 00       	mov    $0x1,%edi
  4024c1:	e8 0a ec ff ff       	call   4010d0 <calloc@plt>
  4024c6:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
    data[x].scheduler = scheduler;   
  4024ca:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4024d0:	48 98                	cltq
  4024d2:	48 c1 e0 0a          	shl    $0xa,%rax
  4024d6:	48 89 c2             	mov    %rax,%rdx
  4024d9:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4024e0:	48 01 c2             	add    %rax,%rdx
  4024e3:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4024e7:	48 89 82 c8 03 00 00 	mov    %rax,0x3c8(%rdx)
    data[x].reads = reads;
  4024ee:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4024f4:	48 98                	cltq
  4024f6:	48 c1 e0 0a          	shl    $0xa,%rax
  4024fa:	48 89 c2             	mov    %rax,%rdx
  4024fd:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402504:	48 01 c2             	add    %rax,%rdx
  402507:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
  40250e:	48 89 82 a0 03 00 00 	mov    %rax,0x3a0(%rdx)
    data[x].writes = writes; 
  402515:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40251b:	48 98                	cltq
  40251d:	48 c1 e0 0a          	shl    $0xa,%rax
  402521:	48 89 c2             	mov    %rax,%rdx
  402524:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40252b:	48 01 c2             	add    %rax,%rdx
  40252e:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  402535:	48 89 82 a8 03 00 00 	mov    %rax,0x3a8(%rdx)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t)); 
  40253c:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402542:	48 98                	cltq
  402544:	48 c1 e0 0a          	shl    $0xa,%rax
  402548:	48 89 c2             	mov    %rax,%rdx
  40254b:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402552:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  402556:	be 80 00 00 00       	mov    $0x80,%esi
  40255b:	bf 01 00 00 00       	mov    $0x1,%edi
  402560:	e8 6b eb ff ff       	call   4010d0 <calloc@plt>
  402565:	48 89 43 78          	mov    %rax,0x78(%rbx)
    CPU_SET(cpu += 1, data[x].cpu_set); 
  402569:	83 85 c4 fe ff ff 01 	addl   $0x1,-0x13c(%rbp)
  402570:	8b 85 c4 fe ff ff    	mov    -0x13c(%rbp),%eax
  402576:	48 98                	cltq
  402578:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  40257c:	48 81 7d b0 ff 03 00 00 	cmpq   $0x3ff,-0x50(%rbp)
  402584:	77 78                	ja     4025fe <main+0x581>
  402586:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40258c:	48 98                	cltq
  40258e:	48 c1 e0 0a          	shl    $0xa,%rax
  402592:	48 89 c2             	mov    %rax,%rdx
  402595:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40259c:	48 01 d0             	add    %rdx,%rax
  40259f:	48 8b 40 78          	mov    0x78(%rax),%rax
  4025a3:	48 89 c1             	mov    %rax,%rcx
  4025a6:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
  4025aa:	48 c1 e8 06          	shr    $0x6,%rax
  4025ae:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4025b6:	48 01 ca             	add    %rcx,%rdx
  4025b9:	48 8b 32             	mov    (%rdx),%rsi
  4025bc:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
  4025c0:	83 e2 3f             	and    $0x3f,%edx
  4025c3:	bf 01 00 00 00       	mov    $0x1,%edi
  4025c8:	89 d1                	mov    %edx,%ecx
  4025ca:	48 d3 e7             	shl    %cl,%rdi
  4025cd:	48 89 f9             	mov    %rdi,%rcx
  4025d0:	8b 95 c8 fe ff ff    	mov    -0x138(%rbp),%edx
  4025d6:	48 63 d2             	movslq %edx,%rdx
  4025d9:	48 89 d7             	mov    %rdx,%rdi
  4025dc:	48 c1 e7 0a          	shl    $0xa,%rdi
  4025e0:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4025e7:	48 01 fa             	add    %rdi,%rdx
  4025ea:	48 8b 52 78          	mov    0x78(%rdx),%rdx
  4025ee:	48 c1 e0 03          	shl    $0x3,%rax
  4025f2:	48 01 d0             	add    %rdx,%rax
  4025f5:	48 09 ce             	or     %rcx,%rsi
  4025f8:	48 89 f2             	mov    %rsi,%rdx
  4025fb:	48 89 10             	mov    %rdx,(%rax)
    printf("assigning thread %d to cpu %d\n", x, cpu);
  4025fe:	8b 95 c4 fe ff ff    	mov    -0x13c(%rbp),%edx
  402604:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40260a:	89 c6                	mov    %eax,%esi
  40260c:	48 8d 05 bd 1a 00 00 	lea    0x1abd(%rip),%rax        # 4040d0 <_IO_stdin_used+0xd0>
  402613:	48 89 c7             	mov    %rax,%rdi
  402616:	b8 00 00 00 00       	mov    $0x0,%eax
  40261b:	e8 60 ea ff ff       	call   401080 <printf@plt>
    data[x].bucketstart = x * buckets; 
  402620:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402626:	48 98                	cltq
  402628:	48 c1 e0 0a          	shl    $0xa,%rax
  40262c:	48 89 c2             	mov    %rax,%rdx
  40262f:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402636:	48 01 c2             	add    %rax,%rdx
  402639:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40263f:	0f af 85 90 fe ff ff 	imul   -0x170(%rbp),%eax
  402646:	89 82 98 00 00 00    	mov    %eax,0x98(%rdx)
    data[x].globalwrite = globalwrite;
  40264c:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402652:	48 98                	cltq
  402654:	48 c1 e0 0a          	shl    $0xa,%rax
  402658:	48 89 c2             	mov    %rax,%rdx
  40265b:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402662:	48 01 c2             	add    %rax,%rdx
  402665:	48 8b 85 e0 fe ff ff 	mov    -0x120(%rbp),%rax
  40266c:	48 89 82 80 03 00 00 	mov    %rax,0x380(%rdx)
    data[x].loglevel = debug;
  402673:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402679:	48 98                	cltq
  40267b:	48 c1 e0 0a          	shl    $0xa,%rax
  40267f:	48 89 c2             	mov    %rax,%rdx
  402682:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402689:	48 01 c2             	add    %rax,%rdx
  40268c:	8b 85 a0 fe ff ff    	mov    -0x160(%rbp),%eax
  402692:	89 82 80 00 00 00    	mov    %eax,0x80(%rdx)
    data[x].running = 2;
  402698:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40269e:	48 98                	cltq
  4026a0:	48 c1 e0 0a          	shl    $0xa,%rax
  4026a4:	48 89 c2             	mov    %rax,%rdx
  4026a7:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026ae:	48 01 d0             	add    %rdx,%rax
  4026b1:	c7 40 5c 02 00 00 00 	movl   $0x2,0x5c(%rax)
    data[x].threadindex = x;
  4026b8:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026be:	48 98                	cltq
  4026c0:	48 c1 e0 0a          	shl    $0xa,%rax
  4026c4:	48 89 c2             	mov    %rax,%rdx
  4026c7:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026ce:	48 01 c2             	add    %rax,%rdx
  4026d1:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026d7:	89 42 64             	mov    %eax,0x64(%rdx)
    data[x].worksize = worksize;
  4026da:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026e0:	48 98                	cltq
  4026e2:	48 c1 e0 0a          	shl    $0xa,%rax
  4026e6:	48 89 c2             	mov    %rax,%rdx
  4026e9:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026f0:	48 01 d0             	add    %rdx,%rax
  4026f3:	48 8b 95 10 ff ff ff 	mov    -0xf0(%rbp),%rdx
  4026fa:	89 50 60             	mov    %edx,0x60(%rax)
    
    data[x].availables = buckets;
  4026fd:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402703:	48 98                	cltq
  402705:	48 c1 e0 0a          	shl    $0xa,%rax
  402709:	48 89 c2             	mov    %rax,%rdx
  40270c:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402713:	48 01 c2             	add    %rax,%rdx
  402716:	8b 85 90 fe ff ff    	mov    -0x170(%rbp),%eax
  40271c:	89 82 94 00 00 00    	mov    %eax,0x94(%rdx)
    data[x].threadsize = threadsize;
  402722:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402728:	48 98                	cltq
  40272a:	48 c1 e0 0a          	shl    $0xa,%rax
  40272e:	48 89 c2             	mov    %rax,%rdx
  402731:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402738:	48 01 c2             	add    %rax,%rdx
  40273b:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402741:	89 42 68             	mov    %eax,0x68(%rdx)
    data[x].readies = readies;
  402744:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40274a:	48 98                	cltq
  40274c:	48 c1 e0 0a          	shl    $0xa,%rax
  402750:	48 89 c2             	mov    %rax,%rdx
  402753:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40275a:	48 01 c2             	add    %rax,%rdx
  40275d:	48 8b 85 60 ff ff ff 	mov    -0xa0(%rbp),%rax
  402764:	48 89 42 20          	mov    %rax,0x20(%rdx)
    data[x].readies[x] = 0;
  402768:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40276e:	48 98                	cltq
  402770:	48 c1 e0 0a          	shl    $0xa,%rax
  402774:	48 89 c2             	mov    %rax,%rdx
  402777:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40277e:	48 01 d0             	add    %rdx,%rax
  402781:	48 8b 50 20          	mov    0x20(%rax),%rdx
  402785:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40278b:	48 98                	cltq
  40278d:	48 c1 e0 02          	shl    $0x2,%rax
  402791:	48 01 d0             	add    %rdx,%rax
  402794:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    data[x].buckets = buckets;
  40279a:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027a0:	48 98                	cltq
  4027a2:	48 c1 e0 0a          	shl    $0xa,%rax
  4027a6:	48 89 c2             	mov    %rax,%rdx
  4027a9:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027b0:	48 01 c2             	add    %rax,%rdx
  4027b3:	8b 85 90 fe ff ff    	mov    -0x170(%rbp),%eax
  4027b9:	89 82 90 00 00 00    	mov    %eax,0x90(%rdx)
    data[x].main = &data[0];
  4027bf:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027c5:	48 98                	cltq
  4027c7:	48 c1 e0 0a          	shl    $0xa,%rax
  4027cb:	48 89 c2             	mov    %rax,%rdx
  4027ce:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027d5:	48 01 c2             	add    %rax,%rdx
  4027d8:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027df:	48 89 42 28          	mov    %rax,0x28(%rdx)
    data[x].threads = data;
  4027e3:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027e9:	48 98                	cltq
  4027eb:	48 c1 e0 0a          	shl    $0xa,%rax
  4027ef:	48 89 c2             	mov    %rax,%rdx
  4027f2:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027f9:	48 01 c2             	add    %rax,%rdx
  4027fc:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402803:	48 89 42 30          	mov    %rax,0x30(%rdx)
    
    data[x].read = 0;
  402807:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40280d:	48 98                	cltq
  40280f:	48 c1 e0 0a          	shl    $0xa,%rax
  402813:	48 89 c2             	mov    %rax,%rdx
  402816:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40281d:	48 01 d0             	add    %rdx,%rax
  402820:	48 c7 00 00 00 00 00 	movq   $0x0,(%rax)
    data[x].write = worksize;
  402827:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40282d:	48 98                	cltq
  40282f:	48 c1 e0 0a          	shl    $0xa,%rax
  402833:	48 89 c2             	mov    %rax,%rdx
  402836:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40283d:	48 01 c2             	add    %rax,%rdx
  402840:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  402847:	48 89 42 08          	mov    %rax,0x8(%rdx)
    data[x].readcursor = threadsize - 1;
  40284b:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402851:	48 98                	cltq
  402853:	48 c1 e0 0a          	shl    $0xa,%rax
  402857:	48 89 c2             	mov    %rax,%rdx
  40285a:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402861:	48 01 d0             	add    %rdx,%rax
  402864:	8b 95 98 fe ff ff    	mov    -0x168(%rbp),%edx
  40286a:	83 ea 01             	sub    $0x1,%edx
  40286d:	89 90 00 02 00 00    	mov    %edx,0x200(%rax)
    data[x].writecursor = 0;
  402873:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402879:	48 98                	cltq
  40287b:	48 c1 e0 0a          	shl    $0xa,%rax
  40287f:	48 89 c2             	mov    %rax,%rdx
  402882:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402889:	48 01 d0             	add    %rdx,%rax
  40288c:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    data[x].freelist = freelist;
  402896:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40289c:	48 98                	cltq
  40289e:	48 c1 e0 0a          	shl    $0xa,%rax
  4028a2:	48 89 c2             	mov    %rax,%rdx
  4028a5:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4028ac:	48 01 c2             	add    %rax,%rdx
  4028af:	48 8b 85 58 ff ff ff 	mov    -0xa8(%rbp),%rax
  4028b6:	48 89 82 a0 00 00 00 	mov    %rax,0xa0(%rdx)
    data[x].chunksize = chunksize;
  4028bd:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028c3:	48 98                	cltq
  4028c5:	48 c1 e0 0a          	shl    $0xa,%rax
  4028c9:	48 89 c2             	mov    %rax,%rdx
  4028cc:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4028d3:	48 01 c2             	add    %rax,%rdx
  4028d6:	48 8b 85 38 ff ff ff 	mov    -0xc8(%rbp),%rax
  4028dd:	48 89 82 c0 00 00 00 	mov    %rax,0xc0(%rdx)
    data[x].chunkslen = chunkslen;
  4028e4:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028ea:	48 98                	cltq
  4028ec:	48 c1 e0 0a          	shl    $0xa,%rax
  4028f0:	48 89 c2             	mov    %rax,%rdx
  4028f3:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4028fa:	48 01 c2             	add    %rax,%rdx
  4028fd:	48 8b 85 08 ff ff ff 	mov    -0xf8(%rbp),%rax
  402904:	48 89 82 b8 00 00 00 	mov    %rax,0xb8(%rdx)
    data[x].newmask = 0;
  40290b:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402911:	48 98                	cltq
  402913:	48 c1 e0 0a          	shl    $0xa,%rax
  402917:	48 89 c2             	mov    %rax,%rdx
  40291a:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402921:	48 01 d0             	add    %rdx,%rax
  402924:	c7 80 c8 00 00 00 00 00 00 00 	movl   $0x0,0xc8(%rax)
    data[x].prevread = threadsize;
  40292e:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402934:	48 98                	cltq
  402936:	48 c1 e0 0a          	shl    $0xa,%rax
  40293a:	48 89 c2             	mov    %rax,%rdx
  40293d:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402944:	48 01 c2             	add    %rax,%rdx
  402947:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40294d:	48 98                	cltq
  40294f:	48 89 82 08 03 00 00 	mov    %rax,0x308(%rdx)
    data[x].prevwrite = threadsize;
  402956:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40295c:	48 98                	cltq
  40295e:	48 c1 e0 0a          	shl    $0xa,%rax
  402962:	48 89 c2             	mov    %rax,%rdx
  402965:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40296c:	48 01 c2             	add    %rax,%rdx
  40296f:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402975:	48 98                	cltq
  402977:	48 89 82 10 03 00 00 	mov    %rax,0x310(%rdx)
    data[x].mystream = 1 + (x / 4);
  40297e:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402984:	8d 50 03             	lea    0x3(%rax),%edx
  402987:	85 c0                	test   %eax,%eax
  402989:	0f 48 c2             	cmovs  %edx,%eax
  40298c:	c1 f8 02             	sar    $0x2,%eax
  40298f:	89 c2                	mov    %eax,%edx
  402991:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402997:	48 98                	cltq
  402999:	48 c1 e0 0a          	shl    $0xa,%rax
  40299d:	48 89 c1             	mov    %rax,%rcx
  4029a0:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4029a7:	48 01 c8             	add    %rcx,%rax
  4029aa:	83 c2 01             	add    $0x1,%edx
  4029ad:	89 90 8c 03 00 00    	mov    %edx,0x38c(%rax)
    data[x].thiswrite = threadsize;
  4029b3:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4029b9:	48 98                	cltq
  4029bb:	48 c1 e0 0a          	shl    $0xa,%rax
  4029bf:	48 89 c2             	mov    %rax,%rdx
  4029c2:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4029c9:	48 01 c2             	add    %rax,%rdx
  4029cc:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4029d2:	89 82 28 03 00 00    	mov    %eax,0x328(%rdx)
    int epochs = 10000000;
  4029d8:	c7 85 dc fe ff ff 80 96 98 00 	movl   $0x989680,-0x124(%rbp)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  4029e2:	8b 85 dc fe ff ff    	mov    -0x124(%rbp),%eax
  4029e8:	48 98                	cltq
  4029ea:	8b 95 c8 fe ff ff    	mov    -0x138(%rbp),%edx
  4029f0:	48 63 d2             	movslq %edx,%rdx
  4029f3:	48 89 d1             	mov    %rdx,%rcx
  4029f6:	48 c1 e1 0a          	shl    $0xa,%rcx
  4029fa:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  402a01:	48 8d 1c 11          	lea    (%rcx,%rdx,1),%rbx
  402a05:	be 30 00 00 00       	mov    $0x30,%esi
  402a0a:	48 89 c7             	mov    %rax,%rdi
  402a0d:	e8 be e6 ff ff       	call   4010d0 <calloc@plt>
  402a12:	48 89 83 18 03 00 00 	mov    %rax,0x318(%rbx)
    data[x].epochssize = epochs;
  402a19:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a1f:	48 98                	cltq
  402a21:	48 c1 e0 0a          	shl    $0xa,%rax
  402a25:	48 89 c2             	mov    %rax,%rdx
  402a28:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a2f:	48 01 c2             	add    %rax,%rdx
  402a32:	8b 85 dc fe ff ff    	mov    -0x124(%rbp),%eax
  402a38:	89 82 20 03 00 00    	mov    %eax,0x320(%rdx)
    data[x].globalread = globalread;
  402a3e:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a44:	48 98                	cltq
  402a46:	48 c1 e0 0a          	shl    $0xa,%rax
  402a4a:	48 89 c2             	mov    %rax,%rdx
  402a4d:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a54:	48 01 c2             	add    %rax,%rdx
  402a57:	48 8b 85 68 ff ff ff 	mov    -0x98(%rbp),%rax
  402a5e:	48 89 82 48 03 00 00 	mov    %rax,0x348(%rdx)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  402a65:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a6b:	48 98                	cltq
  402a6d:	48 c1 e0 0a          	shl    $0xa,%rax
  402a71:	48 89 c2             	mov    %rax,%rdx
  402a74:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a7b:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  402a7f:	be 30 00 00 00       	mov    $0x30,%esi
  402a84:	bf 10 27 00 00       	mov    $0x2710,%edi
  402a89:	e8 42 e6 ff ff       	call   4010d0 <calloc@plt>
  402a8e:	48 89 83 30 03 00 00 	mov    %rax,0x330(%rbx)
    data[x].accesssize = accesssize;
  402a95:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a9b:	48 98                	cltq
  402a9d:	48 c1 e0 0a          	shl    $0xa,%rax
  402aa1:	48 89 c2             	mov    %rax,%rdx
  402aa4:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402aab:	48 01 c2             	add    %rax,%rdx
  402aae:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  402ab4:	89 82 b8 03 00 00    	mov    %eax,0x3b8(%rdx)
  for (int x = 0; x < threadsize ; x++) {
  402aba:	83 85 c8 fe ff ff 01 	addl   $0x1,-0x138(%rbp)
  402ac1:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402ac7:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402acd:	0f 8c f3 f8 ff ff    	jl     4023c6 <main+0x349>
  } 
  
  for (int x = 0; x < threadsize ; x++) {
  402ad3:	c7 85 d0 fe ff ff 00 00 00 00 	movl   $0x0,-0x130(%rbp)
  402add:	e9 b8 00 00 00       	jmp    402b9a <main+0xb1d>
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  402ae2:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402ae8:	48 98                	cltq
  402aea:	48 c1 e0 0a          	shl    $0xa,%rax
  402aee:	48 89 c2             	mov    %rax,%rdx
  402af1:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402af8:	48 01 c2             	add    %rax,%rdx
  402afb:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b01:	48 63 c8             	movslq %eax,%rcx
  402b04:	48 89 c8             	mov    %rcx,%rax
  402b07:	48 c1 e0 03          	shl    $0x3,%rax
  402b0b:	48 29 c8             	sub    %rcx,%rax
  402b0e:	48 c1 e0 03          	shl    $0x3,%rax
  402b12:	48 89 c1             	mov    %rax,%rcx
  402b15:	48 8b 85 f0 fe ff ff 	mov    -0x110(%rbp),%rax
  402b1c:	48 8d 34 01          	lea    (%rcx,%rax,1),%rsi
  402b20:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b26:	48 98                	cltq
  402b28:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
  402b30:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402b37:	48 01 c8             	add    %rcx,%rax
  402b3a:	48 89 d1             	mov    %rdx,%rcx
  402b3d:	48 c7 c2 78 1f 40 00 	mov    $0x401f78,%rdx
  402b44:	48 89 c7             	mov    %rax,%rdi
  402b47:	e8 94 e5 ff ff       	call   4010e0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  402b4c:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b52:	48 98                	cltq
  402b54:	48 c1 e0 0a          	shl    $0xa,%rax
  402b58:	48 89 c2             	mov    %rax,%rdx
  402b5b:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402b62:	48 01 d0             	add    %rdx,%rax
  402b65:	48 8b 50 78          	mov    0x78(%rax),%rdx
  402b69:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b6f:	48 98                	cltq
  402b71:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
  402b79:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402b80:	48 01 c8             	add    %rcx,%rax
  402b83:	48 8b 00             	mov    (%rax),%rax
  402b86:	be 08 00 00 00       	mov    $0x8,%esi
  402b8b:	48 89 c7             	mov    %rax,%rdi
  402b8e:	e8 9d e4 ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  402b93:	83 85 d0 fe ff ff 01 	addl   $0x1,-0x130(%rbp)
  402b9a:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402ba0:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402ba6:	0f 8c 36 ff ff ff    	jl     402ae2 <main+0xa65>
  }
  
  struct timespec time = {
  402bac:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402bb2:	48 98                	cltq
  402bb4:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
  402bb8:	48 c7 45 c8 00 00 00 00 	movq   $0x0,-0x38(%rbp)
    seconds,
    0
  };
  struct timespec rem = {
  402bc0:	48 c7 45 d0 00 00 00 00 	movq   $0x0,-0x30(%rbp)
  402bc8:	48 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%rbp)
    0,
    0
  };
  
  nanosleep(&time, &rem);
  402bd0:	48 8d 55 d0          	lea    -0x30(%rbp),%rdx
  402bd4:	48 8d 45 c0          	lea    -0x40(%rbp),%rax
  402bd8:	48 89 d6             	mov    %rdx,%rsi
  402bdb:	48 89 c7             	mov    %rax,%rdi
  402bde:	e8 bd e4 ff ff       	call   4010a0 <nanosleep@plt>
  
  printf("runphased\n");
  402be3:	48 8d 05 05 15 00 00 	lea    0x1505(%rip),%rax        # 4040ef <_IO_stdin_used+0xef>
  402bea:	48 89 c7             	mov    %rax,%rdi
  402bed:	e8 4e e4 ff ff       	call   401040 <puts@plt>
  for (int x = 0; x < threadsize ; x++) {
  402bf2:	c7 85 b8 fe ff ff 00 00 00 00 	movl   $0x0,-0x148(%rbp)
  402bfc:	eb 29                	jmp    402c27 <main+0xbaa>
    data[x].running--;
  402bfe:	8b 85 b8 fe ff ff    	mov    -0x148(%rbp),%eax
  402c04:	48 98                	cltq
  402c06:	48 c1 e0 0a          	shl    $0xa,%rax
  402c0a:	48 89 c2             	mov    %rax,%rdx
  402c0d:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402c14:	48 01 d0             	add    %rdx,%rax
  402c17:	8b 50 5c             	mov    0x5c(%rax),%edx
  402c1a:	83 ea 01             	sub    $0x1,%edx
  402c1d:	89 50 5c             	mov    %edx,0x5c(%rax)
  for (int x = 0; x < threadsize ; x++) {
  402c20:	83 85 b8 fe ff ff 01 	addl   $0x1,-0x148(%rbp)
  402c27:	8b 85 b8 fe ff ff    	mov    -0x148(%rbp),%eax
  402c2d:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402c33:	7c c9                	jl     402bfe <main+0xb81>
    
  }
  
 printf("draining\n");
  402c35:	48 8d 05 bd 14 00 00 	lea    0x14bd(%rip),%rax        # 4040f9 <_IO_stdin_used+0xf9>
  402c3c:	48 89 c7             	mov    %rax,%rdi
  402c3f:	e8 fc e3 ff ff       	call   401040 <puts@plt>
 // time.tv_sec = 3;
//nanosleep(&time, &rem);
  for (int x = 0; x < threadsize ; x++) {
  402c44:	c7 85 bc fe ff ff 00 00 00 00 	movl   $0x0,-0x144(%rbp)
  402c4e:	eb 29                	jmp    402c79 <main+0xbfc>
    data[x].running--;
  402c50:	8b 85 bc fe ff ff    	mov    -0x144(%rbp),%eax
  402c56:	48 98                	cltq
  402c58:	48 c1 e0 0a          	shl    $0xa,%rax
  402c5c:	48 89 c2             	mov    %rax,%rdx
  402c5f:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402c66:	48 01 d0             	add    %rdx,%rax
  402c69:	8b 50 5c             	mov    0x5c(%rax),%edx
  402c6c:	83 ea 01             	sub    $0x1,%edx
  402c6f:	89 50 5c             	mov    %edx,0x5c(%rax)
  for (int x = 0; x < threadsize ; x++) {
  402c72:	83 85 bc fe ff ff 01 	addl   $0x1,-0x144(%rbp)
  402c79:	8b 85 bc fe ff ff    	mov    -0x144(%rbp),%eax
  402c7f:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402c85:	7c c9                	jl     402c50 <main+0xbd3>
  }
  
  //nanosleep(&time, &rem);
  for (int x = 0; x < threadsize; x++) {
  402c87:	c7 85 c0 fe ff ff 00 00 00 00 	movl   $0x0,-0x140(%rbp)
  402c91:	eb 36                	jmp    402cc9 <main+0xc4c>
    void *res;
    pthread_join(thread[x], &res);
  402c93:	8b 85 c0 fe ff ff    	mov    -0x140(%rbp),%eax
  402c99:	48 98                	cltq
  402c9b:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  402ca3:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402caa:	48 01 d0             	add    %rdx,%rax
  402cad:	48 8b 00             	mov    (%rax),%rax
  402cb0:	48 8d 95 e8 fe ff ff 	lea    -0x118(%rbp),%rdx
  402cb7:	48 89 d6             	mov    %rdx,%rsi
  402cba:	48 89 c7             	mov    %rax,%rdi
  402cbd:	e8 4e e4 ff ff       	call   401110 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  402cc2:	83 85 c0 fe ff ff 01 	addl   $0x1,-0x140(%rbp)
  402cc9:	8b 85 c0 fe ff ff    	mov    -0x140(%rbp),%eax
  402ccf:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402cd5:	7c bc                	jl     402c93 <main+0xc16>
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  402cd7:	48 8d 05 24 14 00 00 	lea    0x1424(%rip),%rax        # 404102 <_IO_stdin_used+0x102>
  402cde:	48 89 c7             	mov    %rax,%rdi
  402ce1:	e8 5a e3 ff ff       	call   401040 <puts@plt>
  long freq = 0;
  402ce6:	48 c7 85 20 ff ff ff 00 00 00 00 	movq   $0x0,-0xe0(%rbp)
  long sends = 1;
  402cf1:	48 c7 45 80 01 00 00 00 	movq   $0x1,-0x80(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402cf9:	c7 85 a8 fe ff ff 00 00 00 00 	movl   $0x0,-0x158(%rbp)
  402d03:	eb 5f                	jmp    402d64 <main+0xce7>
    printf("%ld reads\n", data[x].freq);
  402d05:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d0b:	48 98                	cltq
  402d0d:	48 c1 e0 0a          	shl    $0xa,%rax
  402d11:	48 89 c2             	mov    %rax,%rdx
  402d14:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402d1b:	48 01 d0             	add    %rdx,%rax
  402d1e:	48 8b 40 48          	mov    0x48(%rax),%rax
  402d22:	48 89 c6             	mov    %rax,%rsi
  402d25:	48 8d 05 eb 13 00 00 	lea    0x13eb(%rip),%rax        # 404117 <_IO_stdin_used+0x117>
  402d2c:	48 89 c7             	mov    %rax,%rdi
  402d2f:	b8 00 00 00 00       	mov    $0x0,%eax
  402d34:	e8 47 e3 ff ff       	call   401080 <printf@plt>
    freq += data[x].freq;
  402d39:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d3f:	48 98                	cltq
  402d41:	48 c1 e0 0a          	shl    $0xa,%rax
  402d45:	48 89 c2             	mov    %rax,%rdx
  402d48:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402d4f:	48 01 d0             	add    %rdx,%rax
  402d52:	48 8b 40 48          	mov    0x48(%rax),%rax
  402d56:	48 01 85 20 ff ff ff 	add    %rax,-0xe0(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402d5d:	83 85 a8 fe ff ff 01 	addl   $0x1,-0x158(%rbp)
  402d64:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d6a:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402d70:	7c 93                	jl     402d05 <main+0xc88>
  }
  printf("freq: %ld\n", freq/ seconds);
  402d72:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402d78:	48 63 d8             	movslq %eax,%rbx
  402d7b:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402d82:	48 99                	cqto
  402d84:	48 f7 fb             	idiv   %rbx
  402d87:	48 89 c6             	mov    %rax,%rsi
  402d8a:	48 8d 05 91 13 00 00 	lea    0x1391(%rip),%rax        # 404122 <_IO_stdin_used+0x122>
  402d91:	48 89 c7             	mov    %rax,%rdi
  402d94:	b8 00 00 00 00       	mov    $0x0,%eax
  402d99:	e8 e2 e2 ff ff       	call   401080 <printf@plt>
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  402d9e:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402da5:	48 0f af 45 80       	imul   -0x80(%rbp),%rax
  402daa:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402db0:	48 63 da             	movslq %edx,%rbx
  402db3:	48 99                	cqto
  402db5:	48 f7 fb             	idiv   %rbx
  402db8:	48 89 c6             	mov    %rax,%rsi
  402dbb:	48 8d 05 6b 13 00 00 	lea    0x136b(%rip),%rax        # 40412d <_IO_stdin_used+0x12d>
  402dc2:	48 89 c7             	mov    %rax,%rdi
  402dc5:	b8 00 00 00 00       	mov    $0x0,%eax
  402dca:	e8 b1 e2 ff ff       	call   401080 <printf@plt>
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  402dcf:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402dd5:	48 63 d8             	movslq %eax,%rbx
  402dd8:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402ddf:	48 99                	cqto
  402de1:	48 f7 fb             	idiv   %rbx
  402de4:	48 89 c3             	mov    %rax,%rbx
  402de7:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402dec:	48 99                	cqto
  402dee:	48 f7 fb             	idiv   %rbx
  402df1:	48 89 c6             	mov    %rax,%rsi
  402df4:	48 8d 05 40 13 00 00 	lea    0x1340(%rip),%rax        # 40413b <_IO_stdin_used+0x13b>
  402dfb:	48 89 c7             	mov    %rax,%rdi
  402dfe:	b8 00 00 00 00       	mov    $0x0,%eax
  402e03:	e8 78 e2 ff ff       	call   401080 <printf@plt>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  402e08:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402e0e:	48 63 d8             	movslq %eax,%rbx
  402e11:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402e18:	48 99                	cqto
  402e1a:	48 f7 fb             	idiv   %rbx
  402e1d:	48 89 c3             	mov    %rax,%rbx
  402e20:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402e25:	48 99                	cqto
  402e27:	48 f7 fb             	idiv   %rbx
  402e2a:	48 99                	cqto
  402e2c:	48 f7 7d 80          	idivq  -0x80(%rbp)
  402e30:	48 89 c6             	mov    %rax,%rsi
  402e33:	48 8d 05 15 13 00 00 	lea    0x1315(%rip),%rax        # 40414f <_IO_stdin_used+0x14f>
  402e3a:	48 89 c7             	mov    %rax,%rdi
  402e3d:	b8 00 00 00 00       	mov    $0x0,%eax
  402e42:	e8 39 e2 ff ff       	call   401080 <printf@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  402e47:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402e4e:	48 0f af 45 80       	imul   -0x80(%rbp),%rax
  402e53:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402e59:	48 63 da             	movslq %edx,%rbx
  402e5c:	48 99                	cqto
  402e5e:	48 f7 fb             	idiv   %rbx
  402e61:	48 89 c3             	mov    %rax,%rbx
  402e64:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402e69:	48 99                	cqto
  402e6b:	48 f7 fb             	idiv   %rbx
  402e6e:	48 89 c6             	mov    %rax,%rsi
  402e71:	48 8d 05 f5 12 00 00 	lea    0x12f5(%rip),%rax        # 40416d <_IO_stdin_used+0x16d>
  402e78:	48 89 c7             	mov    %rax,%rdi
  402e7b:	b8 00 00 00 00       	mov    $0x0,%eax
  402e80:	e8 fb e1 ff ff       	call   401080 <printf@plt>
  
  long goods = 0;
  402e85:	48 c7 85 28 ff ff ff 00 00 00 00 	movq   $0x0,-0xd8(%rbp)

  for (int x = 0; x < threadsize; x++) {
  402e90:	c7 85 ac fe ff ff 00 00 00 00 	movl   $0x0,-0x154(%rbp)
  402e9a:	eb 65                	jmp    402f01 <main+0xe84>
    printf("%ld successreads\n", data[x].successreads);
  402e9c:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402ea2:	48 98                	cltq
  402ea4:	48 c1 e0 0a          	shl    $0xa,%rax
  402ea8:	48 89 c2             	mov    %rax,%rdx
  402eab:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402eb2:	48 01 d0             	add    %rdx,%rax
  402eb5:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  402ebc:	48 89 c6             	mov    %rax,%rsi
  402ebf:	48 8d 05 ba 12 00 00 	lea    0x12ba(%rip),%rax        # 404180 <_IO_stdin_used+0x180>
  402ec6:	48 89 c7             	mov    %rax,%rdi
  402ec9:	b8 00 00 00 00       	mov    $0x0,%eax
  402ece:	e8 ad e1 ff ff       	call   401080 <printf@plt>
    goods += data[x].successreads;
  402ed3:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402ed9:	48 98                	cltq
  402edb:	48 c1 e0 0a          	shl    $0xa,%rax
  402edf:	48 89 c2             	mov    %rax,%rdx
  402ee2:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402ee9:	48 01 d0             	add    %rdx,%rax
  402eec:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  402ef3:	48 01 85 28 ff ff ff 	add    %rax,-0xd8(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402efa:	83 85 ac fe ff ff 01 	addl   $0x1,-0x154(%rbp)
  402f01:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402f07:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402f0d:	7c 8d                	jl     402e9c <main+0xe1f>
  }
  
  long freq_writes = 0;
  402f0f:	48 c7 85 30 ff ff ff 00 00 00 00 	movq   $0x0,-0xd0(%rbp)
  
  for (int x = 0; x < threadsize; x++) {
  402f1a:	c7 85 b0 fe ff ff 00 00 00 00 	movl   $0x0,-0x150(%rbp)
  402f24:	eb 5f                	jmp    402f85 <main+0xf08>
    freq_writes += data[x].freq_writes;
  402f26:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f2c:	48 98                	cltq
  402f2e:	48 c1 e0 0a          	shl    $0xa,%rax
  402f32:	48 89 c2             	mov    %rax,%rdx
  402f35:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402f3c:	48 01 d0             	add    %rdx,%rax
  402f3f:	48 8b 40 50          	mov    0x50(%rax),%rax
  402f43:	48 01 85 30 ff ff ff 	add    %rax,-0xd0(%rbp)
    printf("%ld writes\n", data[x].freq_writes);
  402f4a:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f50:	48 98                	cltq
  402f52:	48 c1 e0 0a          	shl    $0xa,%rax
  402f56:	48 89 c2             	mov    %rax,%rdx
  402f59:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402f60:	48 01 d0             	add    %rdx,%rax
  402f63:	48 8b 40 50          	mov    0x50(%rax),%rax
  402f67:	48 89 c6             	mov    %rax,%rsi
  402f6a:	48 8d 05 21 12 00 00 	lea    0x1221(%rip),%rax        # 404192 <_IO_stdin_used+0x192>
  402f71:	48 89 c7             	mov    %rax,%rdi
  402f74:	b8 00 00 00 00       	mov    $0x0,%eax
  402f79:	e8 02 e1 ff ff       	call   401080 <printf@plt>
  for (int x = 0; x < threadsize; x++) {
  402f7e:	83 85 b0 fe ff ff 01 	addl   $0x1,-0x150(%rbp)
  402f85:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f8b:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402f91:	7c 93                	jl     402f26 <main+0xea9>
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  402f93:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402f99:	48 63 d8             	movslq %eax,%rbx
  402f9c:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402fa3:	48 99                	cqto
  402fa5:	48 f7 fb             	idiv   %rbx
  402fa8:	48 89 c6             	mov    %rax,%rsi
  402fab:	48 8d 05 ec 11 00 00 	lea    0x11ec(%rip),%rax        # 40419e <_IO_stdin_used+0x19e>
  402fb2:	48 89 c7             	mov    %rax,%rdi
  402fb5:	b8 00 00 00 00       	mov    $0x0,%eax
  402fba:	e8 c1 e0 ff ff       	call   401080 <printf@plt>

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  402fbf:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402fc6:	48 0f af 45 80       	imul   -0x80(%rbp),%rax
  402fcb:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402fd1:	48 63 da             	movslq %edx,%rbx
  402fd4:	48 99                	cqto
  402fd6:	48 f7 fb             	idiv   %rbx
  402fd9:	48 89 c6             	mov    %rax,%rsi
  402fdc:	48 8d 05 cd 11 00 00 	lea    0x11cd(%rip),%rax        # 4041b0 <_IO_stdin_used+0x1b0>
  402fe3:	48 89 c7             	mov    %rax,%rdi
  402fe6:	b8 00 00 00 00       	mov    $0x0,%eax
  402feb:	e8 90 e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  402ff0:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402ff6:	48 63 d8             	movslq %eax,%rbx
  402ff9:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  403000:	48 99                	cqto
  403002:	48 f7 fb             	idiv   %rbx
  403005:	48 89 c3             	mov    %rax,%rbx
  403008:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40300d:	48 99                	cqto
  40300f:	48 f7 fb             	idiv   %rbx
  403012:	48 89 c6             	mov    %rax,%rsi
  403015:	48 8d 05 ac 11 00 00 	lea    0x11ac(%rip),%rax        # 4041c8 <_IO_stdin_used+0x1c8>
  40301c:	48 89 c7             	mov    %rax,%rdi
  40301f:	b8 00 00 00 00       	mov    $0x0,%eax
  403024:	e8 57 e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes per thread latency: %ld\n", (1000000000/(freq_writes / seconds)) / sends);
  403029:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  40302f:	48 63 d8             	movslq %eax,%rbx
  403032:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  403039:	48 99                	cqto
  40303b:	48 f7 fb             	idiv   %rbx
  40303e:	48 89 c3             	mov    %rax,%rbx
  403041:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  403046:	48 99                	cqto
  403048:	48 f7 fb             	idiv   %rbx
  40304b:	48 99                	cqto
  40304d:	48 f7 7d 80          	idivq  -0x80(%rbp)
  403051:	48 89 c6             	mov    %rax,%rsi
  403054:	48 8d 05 8d 11 00 00 	lea    0x118d(%rip),%rax        # 4041e8 <_IO_stdin_used+0x1e8>
  40305b:	48 89 c7             	mov    %rax,%rdi
  40305e:	b8 00 00 00 00       	mov    $0x0,%eax
  403063:	e8 18 e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * sends) / seconds));
  403068:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  40306f:	48 0f af 45 80       	imul   -0x80(%rbp),%rax
  403074:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  40307a:	48 63 da             	movslq %edx,%rbx
  40307d:	48 99                	cqto
  40307f:	48 f7 fb             	idiv   %rbx
  403082:	48 89 c3             	mov    %rax,%rbx
  403085:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40308a:	48 99                	cqto
  40308c:	48 f7 fb             	idiv   %rbx
  40308f:	48 89 c6             	mov    %rax,%rsi
  403092:	48 8d 05 74 11 00 00 	lea    0x1174(%rip),%rax        # 40420d <_IO_stdin_used+0x20d>
  403099:	48 89 c7             	mov    %rax,%rdi
  40309c:	b8 00 00 00 00       	mov    $0x0,%eax
  4030a1:	e8 da df ff ff       	call   401080 <printf@plt>
    printf("%ldns\n", read.tv_nsec - created.tv_nsec);
    printf("%ldns\n", written.tv_nsec - read.tv_nsec);
    
  }
  */
  printf("writer speed\n");
  4030a6:	48 8d 05 7a 11 00 00 	lea    0x117a(%rip),%rax        # 404227 <_IO_stdin_used+0x227>
  4030ad:	48 89 c7             	mov    %rax,%rdi
  4030b0:	e8 8b df ff ff       	call   401040 <puts@plt>
  for (int x = 0; x < 1 ;  x++){
  4030b5:	c7 85 b4 fe ff ff 00 00 00 00 	movl   $0x0,-0x14c(%rbp)
  4030bf:	e9 84 02 00 00       	jmp    403348 <main+0x12cb>
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  4030c4:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4030ca:	48 98                	cltq
  4030cc:	48 c1 e0 0a          	shl    $0xa,%rax
  4030d0:	48 89 c2             	mov    %rax,%rdx
  4030d3:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4030da:	48 01 d0             	add    %rdx,%rax
  4030dd:	48 8b 80 f0 00 00 00 	mov    0xf0(%rax),%rax
  4030e4:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4030ea:	48 63 d2             	movslq %edx,%rdx
  4030ed:	48 89 d1             	mov    %rdx,%rcx
  4030f0:	48 c1 e1 0a          	shl    $0xa,%rcx
  4030f4:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4030fb:	48 01 ca             	add    %rcx,%rdx
  4030fe:	48 8b 92 e0 00 00 00 	mov    0xe0(%rdx),%rdx
  403105:	48 29 d0             	sub    %rdx,%rax
  403108:	48 89 c6             	mov    %rax,%rsi
  40310b:	48 8d 05 22 11 00 00 	lea    0x1122(%rip),%rax        # 404234 <_IO_stdin_used+0x234>
  403112:	48 89 c7             	mov    %rax,%rdi
  403115:	b8 00 00 00 00       	mov    $0x0,%eax
  40311a:	e8 61 df ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  40311f:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403125:	48 98                	cltq
  403127:	48 c1 e0 0a          	shl    $0xa,%rax
  40312b:	48 89 c2             	mov    %rax,%rdx
  40312e:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403135:	48 01 d0             	add    %rdx,%rax
  403138:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
  40313f:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  403145:	48 63 d2             	movslq %edx,%rdx
  403148:	48 89 d1             	mov    %rdx,%rcx
  40314b:	48 c1 e1 0a          	shl    $0xa,%rcx
  40314f:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403156:	48 01 ca             	add    %rcx,%rdx
  403159:	48 8b 92 e0 00 00 00 	mov    0xe0(%rdx),%rdx
  403160:	48 29 d0             	sub    %rdx,%rax
  403163:	48 89 c6             	mov    %rax,%rsi
  403166:	48 8d 05 c7 10 00 00 	lea    0x10c7(%rip),%rax        # 404234 <_IO_stdin_used+0x234>
  40316d:	48 89 c7             	mov    %rax,%rdi
  403170:	b8 00 00 00 00       	mov    $0x0,%eax
  403175:	e8 06 df ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  40317a:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403180:	48 98                	cltq
  403182:	48 c1 e0 0a          	shl    $0xa,%rax
  403186:	48 89 c2             	mov    %rax,%rdx
  403189:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403190:	48 01 d0             	add    %rdx,%rax
  403193:	48 8b 80 f0 00 00 00 	mov    0xf0(%rax),%rax
  40319a:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4031a0:	48 63 d2             	movslq %edx,%rdx
  4031a3:	48 89 d1             	mov    %rdx,%rcx
  4031a6:	48 c1 e1 0a          	shl    $0xa,%rcx
  4031aa:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4031b1:	48 01 ca             	add    %rcx,%rdx
  4031b4:	48 8b 92 00 01 00 00 	mov    0x100(%rdx),%rdx
  4031bb:	48 29 d0             	sub    %rdx,%rax
  4031be:	48 89 c6             	mov    %rax,%rsi
  4031c1:	48 8d 05 6c 10 00 00 	lea    0x106c(%rip),%rax        # 404234 <_IO_stdin_used+0x234>
  4031c8:	48 89 c7             	mov    %rax,%rdi
  4031cb:	b8 00 00 00 00       	mov    $0x0,%eax
  4031d0:	e8 ab de ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  4031d5:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4031db:	48 98                	cltq
  4031dd:	48 c1 e0 0a          	shl    $0xa,%rax
  4031e1:	48 89 c2             	mov    %rax,%rdx
  4031e4:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4031eb:	48 01 d0             	add    %rdx,%rax
  4031ee:	48 8b 80 20 01 00 00 	mov    0x120(%rax),%rax
  4031f5:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4031fb:	48 63 d2             	movslq %edx,%rdx
  4031fe:	48 89 d1             	mov    %rdx,%rcx
  403201:	48 c1 e1 0a          	shl    $0xa,%rcx
  403205:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  40320c:	48 01 ca             	add    %rcx,%rdx
  40320f:	48 8b 92 10 01 00 00 	mov    0x110(%rdx),%rdx
  403216:	48 29 d0             	sub    %rdx,%rax
  403219:	48 89 c6             	mov    %rax,%rsi
  40321c:	48 8d 05 11 10 00 00 	lea    0x1011(%rip),%rax        # 404234 <_IO_stdin_used+0x234>
  403223:	48 89 c7             	mov    %rax,%rdi
  403226:	b8 00 00 00 00       	mov    $0x0,%eax
  40322b:	e8 50 de ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  403230:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403236:	48 98                	cltq
  403238:	48 c1 e0 0a          	shl    $0xa,%rax
  40323c:	48 89 c2             	mov    %rax,%rdx
  40323f:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403246:	48 01 d0             	add    %rdx,%rax
  403249:	48 8b 80 10 01 00 00 	mov    0x110(%rax),%rax
  403250:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  403256:	48 63 d2             	movslq %edx,%rdx
  403259:	48 89 d1             	mov    %rdx,%rcx
  40325c:	48 c1 e1 0a          	shl    $0xa,%rcx
  403260:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403267:	48 01 ca             	add    %rcx,%rdx
  40326a:	48 8b 92 20 01 00 00 	mov    0x120(%rdx),%rdx
  403271:	48 29 d0             	sub    %rdx,%rax
  403274:	48 89 c6             	mov    %rax,%rsi
  403277:	48 8d 05 b6 0f 00 00 	lea    0xfb6(%rip),%rax        # 404234 <_IO_stdin_used+0x234>
  40327e:	48 89 c7             	mov    %rax,%rdi
  403281:	b8 00 00 00 00       	mov    $0x0,%eax
  403286:	e8 f5 dd ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  40328b:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403291:	48 98                	cltq
  403293:	48 c1 e0 0a          	shl    $0xa,%rax
  403297:	48 89 c2             	mov    %rax,%rdx
  40329a:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4032a1:	48 01 d0             	add    %rdx,%rax
  4032a4:	48 8b 80 10 01 00 00 	mov    0x110(%rax),%rax
  4032ab:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4032b1:	48 63 d2             	movslq %edx,%rdx
  4032b4:	48 89 d1             	mov    %rdx,%rcx
  4032b7:	48 c1 e1 0a          	shl    $0xa,%rcx
  4032bb:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4032c2:	48 01 ca             	add    %rcx,%rdx
  4032c5:	48 8b 92 00 01 00 00 	mov    0x100(%rdx),%rdx
  4032cc:	48 29 d0             	sub    %rdx,%rax
  4032cf:	48 89 c6             	mov    %rax,%rsi
  4032d2:	48 8d 05 5b 0f 00 00 	lea    0xf5b(%rip),%rax        # 404234 <_IO_stdin_used+0x234>
  4032d9:	48 89 c7             	mov    %rax,%rdi
  4032dc:	b8 00 00 00 00       	mov    $0x0,%eax
  4032e1:	e8 9a dd ff ff       	call   401080 <printf@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  4032e6:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4032ec:	48 98                	cltq
  4032ee:	48 c1 e0 0a          	shl    $0xa,%rax
  4032f2:	48 89 c2             	mov    %rax,%rdx
  4032f5:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4032fc:	48 01 d0             	add    %rdx,%rax
  4032ff:	48 8b 80 40 01 00 00 	mov    0x140(%rax),%rax
  403306:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  40330c:	48 63 d2             	movslq %edx,%rdx
  40330f:	48 89 d1             	mov    %rdx,%rcx
  403312:	48 c1 e1 0a          	shl    $0xa,%rcx
  403316:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  40331d:	48 01 ca             	add    %rcx,%rdx
  403320:	48 8b 92 30 01 00 00 	mov    0x130(%rdx),%rdx
  403327:	48 29 d0             	sub    %rdx,%rax
  40332a:	48 89 c6             	mov    %rax,%rsi
  40332d:	48 8d 05 05 0f 00 00 	lea    0xf05(%rip),%rax        # 404239 <_IO_stdin_used+0x239>
  403334:	48 89 c7             	mov    %rax,%rdi
  403337:	b8 00 00 00 00       	mov    $0x0,%eax
  40333c:	e8 3f dd ff ff       	call   401080 <printf@plt>
  for (int x = 0; x < 1 ;  x++){
  403341:	83 85 b4 fe ff ff 01 	addl   $0x1,-0x14c(%rbp)
  403348:	83 bd b4 fe ff ff 00 	cmpl   $0x0,-0x14c(%rbp)
  40334f:	0f 8e 6f fd ff ff    	jle    4030c4 <main+0x1047>
  } 
  printf("%ld good reads per second\n", goods / seconds);
  403355:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  40335b:	48 63 d8             	movslq %eax,%rbx
  40335e:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
  403365:	48 99                	cqto
  403367:	48 f7 fb             	idiv   %rbx
  40336a:	48 89 c6             	mov    %rax,%rsi
  40336d:	48 8d 05 cd 0e 00 00 	lea    0xecd(%rip),%rax        # 404241 <_IO_stdin_used+0x241>
  403374:	48 89 c7             	mov    %rax,%rdi
  403377:	b8 00 00 00 00       	mov    $0x0,%eax
  40337c:	e8 ff dc ff ff       	call   401080 <printf@plt>
  printf("%ld good reads per second latency\n", 1000000000 / (goods / seconds));
  403381:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  403387:	48 63 d8             	movslq %eax,%rbx
  40338a:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
  403391:	48 99                	cqto
  403393:	48 f7 fb             	idiv   %rbx
  403396:	48 89 c3             	mov    %rax,%rbx
  403399:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40339e:	48 99                	cqto
  4033a0:	48 f7 fb             	idiv   %rbx
  4033a3:	48 89 c6             	mov    %rax,%rsi
  4033a6:	48 8d 05 b3 0e 00 00 	lea    0xeb3(%rip),%rax        # 404260 <_IO_stdin_used+0x260>
  4033ad:	48 89 c7             	mov    %rax,%rdi
  4033b0:	b8 00 00 00 00       	mov    $0x0,%eax
  4033b5:	e8 c6 dc ff ff       	call   401080 <printf@plt>
     }
   fclose(out_file);
   
 }

  char * filename = calloc(100, sizeof(char));
  4033ba:	be 01 00 00 00       	mov    $0x1,%esi
  4033bf:	bf 64 00 00 00       	mov    $0x64,%edi
  4033c4:	e8 07 dd ff ff       	call   4010d0 <calloc@plt>
  4033c9:	48 89 45 88          	mov    %rax,-0x78(%rbp)
  char * buf = calloc(1000, sizeof(char));
  4033cd:	be 01 00 00 00       	mov    $0x1,%esi
  4033d2:	bf e8 03 00 00       	mov    $0x3e8,%edi
  4033d7:	e8 f4 dc ff ff       	call   4010d0 <calloc@plt>
  4033dc:	48 89 45 90          	mov    %rax,-0x70(%rbp)
  memset(filename, 0, 100);
  4033e0:	48 8b 45 88          	mov    -0x78(%rbp),%rax
  4033e4:	ba 64 00 00 00       	mov    $0x64,%edx
  4033e9:	be 00 00 00 00       	mov    $0x0,%esi
  4033ee:	48 89 c7             	mov    %rax,%rdi
  4033f1:	e8 ca dc ff ff       	call   4010c0 <memset@plt>
  snprintf(filename, 100, "coroutine.struct");
  4033f6:	48 8b 45 88          	mov    -0x78(%rbp),%rax
  4033fa:	48 8d 15 82 0e 00 00 	lea    0xe82(%rip),%rdx        # 404283 <_IO_stdin_used+0x283>
  403401:	be 64 00 00 00       	mov    $0x64,%esi
  403406:	48 89 c7             	mov    %rax,%rdi
  403409:	b8 00 00 00 00       	mov    $0x0,%eax
  40340e:	e8 7d dc ff ff       	call   401090 <snprintf@plt>
  FILE *out_file = fopen(filename, "w");
  403413:	48 8b 45 88          	mov    -0x78(%rbp),%rax
  403417:	48 8d 15 76 0e 00 00 	lea    0xe76(%rip),%rdx        # 404294 <_IO_stdin_used+0x294>
  40341e:	48 89 d6             	mov    %rdx,%rsi
  403421:	48 89 c7             	mov    %rax,%rdi
  403424:	e8 c7 dc ff ff       	call   4010f0 <fopen@plt>
  403429:	48 89 45 98          	mov    %rax,-0x68(%rbp)

memset(buf, 0, 1000);
  40342d:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403431:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403436:	be 00 00 00 00       	mov    $0x0,%esi
  40343b:	48 89 c7             	mov    %rax,%rdi
  40343e:	e8 7d dc ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "index %ld\n", offsetof(struct Coroutine, index));
  403443:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403447:	b9 00 00 00 00       	mov    $0x0,%ecx
  40344c:	48 8d 15 43 0e 00 00 	lea    0xe43(%rip),%rdx        # 404296 <_IO_stdin_used+0x296>
  403453:	be 64 00 00 00       	mov    $0x64,%esi
  403458:	48 89 c7             	mov    %rax,%rdi
  40345b:	b8 00 00 00 00       	mov    $0x0,%eax
  403460:	e8 2b dc ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  403465:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  403469:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40346d:	48 89 d6             	mov    %rdx,%rsi
  403470:	48 89 c7             	mov    %rax,%rdi
  403473:	e8 38 dc ff ff       	call   4010b0 <fputs@plt>
  
  memset(buf, 0, 1000);
  403478:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40347c:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403481:	be 00 00 00 00       	mov    $0x0,%esi
  403486:	48 89 c7             	mov    %rax,%rdi
  403489:	e8 32 dc ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "rsp %ld\n", offsetof(struct Coroutine, rsp));
  40348e:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403492:	b9 08 00 00 00       	mov    $0x8,%ecx
  403497:	48 8d 15 03 0e 00 00 	lea    0xe03(%rip),%rdx        # 4042a1 <_IO_stdin_used+0x2a1>
  40349e:	be 64 00 00 00       	mov    $0x64,%esi
  4034a3:	48 89 c7             	mov    %rax,%rdi
  4034a6:	b8 00 00 00 00       	mov    $0x0,%eax
  4034ab:	e8 e0 db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  4034b0:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  4034b4:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4034b8:	48 89 d6             	mov    %rdx,%rsi
  4034bb:	48 89 c7             	mov    %rax,%rdi
  4034be:	e8 ed db ff ff       	call   4010b0 <fputs@plt>
  
  memset(buf, 0, 1000);
  4034c3:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4034c7:	ba e8 03 00 00       	mov    $0x3e8,%edx
  4034cc:	be 00 00 00 00       	mov    $0x0,%esi
  4034d1:	48 89 c7             	mov    %rax,%rdi
  4034d4:	e8 e7 db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "eip %ld\n", offsetof(struct Coroutine, eip));
  4034d9:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4034dd:	b9 10 00 00 00       	mov    $0x10,%ecx
  4034e2:	48 8d 15 c1 0d 00 00 	lea    0xdc1(%rip),%rdx        # 4042aa <_IO_stdin_used+0x2aa>
  4034e9:	be 64 00 00 00       	mov    $0x64,%esi
  4034ee:	48 89 c7             	mov    %rax,%rdi
  4034f1:	b8 00 00 00 00       	mov    $0x0,%eax
  4034f6:	e8 95 db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  4034fb:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  4034ff:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403503:	48 89 d6             	mov    %rdx,%rsi
  403506:	48 89 c7             	mov    %rax,%rdi
  403509:	e8 a2 db ff ff       	call   4010b0 <fputs@plt>


  memset(buf, 0, 1000);
  40350e:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403512:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403517:	be 00 00 00 00       	mov    $0x0,%esi
  40351c:	48 89 c7             	mov    %rax,%rdi
  40351f:	e8 9c db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "data %ld\n", offsetof(struct Coroutine, data));
  403524:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403528:	b9 18 00 00 00       	mov    $0x18,%ecx
  40352d:	48 8d 15 7f 0d 00 00 	lea    0xd7f(%rip),%rdx        # 4042b3 <_IO_stdin_used+0x2b3>
  403534:	be 64 00 00 00       	mov    $0x64,%esi
  403539:	48 89 c7             	mov    %rax,%rdi
  40353c:	b8 00 00 00 00       	mov    $0x0,%eax
  403541:	e8 4a db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  403546:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  40354a:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40354e:	48 89 d6             	mov    %rdx,%rsi
  403551:	48 89 c7             	mov    %rax,%rdi
  403554:	e8 57 db ff ff       	call   4010b0 <fputs@plt>

  memset(buf, 0, 1000);
  403559:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40355d:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403562:	be 00 00 00 00       	mov    $0x0,%esi
  403567:	48 89 c7             	mov    %rax,%rdi
  40356a:	e8 51 db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "corourinedata.running %ld\n", offsetof(struct CoroutineData, running));
  40356f:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403573:	b9 00 00 00 00       	mov    $0x0,%ecx
  403578:	48 8d 15 3e 0d 00 00 	lea    0xd3e(%rip),%rdx        # 4042bd <_IO_stdin_used+0x2bd>
  40357f:	be 64 00 00 00       	mov    $0x64,%esi
  403584:	48 89 c7             	mov    %rax,%rdi
  403587:	b8 00 00 00 00       	mov    $0x0,%eax
  40358c:	e8 ff da ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  403591:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  403595:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403599:	48 89 d6             	mov    %rdx,%rsi
  40359c:	48 89 c7             	mov    %rax,%rdi
  40359f:	e8 0c db ff ff       	call   4010b0 <fputs@plt>

  memset(buf, 0, 1000);
  4035a4:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4035a8:	ba e8 03 00 00       	mov    $0x3e8,%edx
  4035ad:	be 00 00 00 00       	mov    $0x0,%esi
  4035b2:	48 89 c7             	mov    %rax,%rdi
  4035b5:	e8 06 db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "size coroutine %ld\n", sizeof(struct Coroutine));
  4035ba:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4035be:	b9 20 00 00 00       	mov    $0x20,%ecx
  4035c3:	48 8d 15 0e 0d 00 00 	lea    0xd0e(%rip),%rdx        # 4042d8 <_IO_stdin_used+0x2d8>
  4035ca:	be 64 00 00 00       	mov    $0x64,%esi
  4035cf:	48 89 c7             	mov    %rax,%rdi
  4035d2:	b8 00 00 00 00       	mov    $0x0,%eax
  4035d7:	e8 b4 da ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  4035dc:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  4035e0:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4035e4:	48 89 d6             	mov    %rdx,%rsi
  4035e7:	48 89 c7             	mov    %rax,%rdi
  4035ea:	e8 c1 da ff ff       	call   4010b0 <fputs@plt>

memset(buf, 0, 1000);
  4035ef:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4035f3:	ba e8 03 00 00       	mov    $0x3e8,%edx
  4035f8:	be 00 00 00 00       	mov    $0x0,%esi
  4035fd:	48 89 c7             	mov    %rax,%rdi
  403600:	e8 bb da ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "scheduler.rsp %ld\n", offsetof(struct Scheduler, rsp));
  403605:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403609:	b9 00 00 00 00       	mov    $0x0,%ecx
  40360e:	48 8d 15 d7 0c 00 00 	lea    0xcd7(%rip),%rdx        # 4042ec <_IO_stdin_used+0x2ec>
  403615:	be 64 00 00 00       	mov    $0x64,%esi
  40361a:	48 89 c7             	mov    %rax,%rdi
  40361d:	b8 00 00 00 00       	mov    $0x0,%eax
  403622:	e8 69 da ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  403627:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
  40362b:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40362f:	48 89 d6             	mov    %rdx,%rsi
  403632:	48 89 c7             	mov    %rax,%rdi
  403635:	e8 76 da ff ff       	call   4010b0 <fputs@plt>
  
  
  fclose(out_file);
  40363a:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40363e:	48 89 c7             	mov    %rax,%rdi
  403641:	e8 1a da ff ff       	call   401060 <fclose@plt>
  403646:	b8 00 00 00 00       	mov    $0x0,%eax
  40364b:	48 8b 55 e8          	mov    -0x18(%rbp),%rdx
  40364f:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  403658:	74 05                	je     40365f <main+0x15e2>
  40365a:	e8 11 da ff ff       	call   401070 <__stack_chk_fail@plt>
  40365f:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
  403663:	c9                   	leave
  403664:	c3                   	ret
  403665:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40366f:	90                   	nop

0000000000403670 <.MSG>:
  403670:	43                   	rex.XB
  403671:	4f 20 43 6f          	rex.WRXB and %r8b,0x6f(%r11)
  403675:	72 6f                	jb     4036e6 <.CURSTACK+0x4>
  403677:	75 74                	jne    4036ed <.CURSTACK+0xb>
  403679:	69 6e 65 53 74 72 75 	imul   $0x75727453,0x65(%rsi),%ebp
  403680:	63 74 20 25          	movsxd 0x25(%rax,%riz,1),%esi
  403684:	78 0a                	js     403690 <.EIP+0x9>
	...

0000000000403687 <.EIP>:
  403687:	43                   	rex.XB
  403688:	4f 20 45 49          	rex.WRXB and %r8b,0x49(%r13)
  40368c:	50                   	push   %rax
  40368d:	2e                   	cs
  40368e:	2e                   	cs
  40368f:	2e                   	cs
  403690:	20                   	.byte 0x20
  403691:	25                   	.byte 0x25
  403692:	78 0a                	js     40369e <.CODATA+0x9>
	...

0000000000403695 <.CODATA>:
  403695:	43                   	rex.XB
  403696:	4f 20 63 6f          	rex.WRXB and %r12b,0x6f(%r11)
  40369a:	64 61                	fs (bad)
  40369c:	74 61                	je     4036ff <.SCHED+0xc>
  40369e:	2e                   	cs
  40369f:	2e                   	cs
  4036a0:	2e                   	cs
  4036a1:	20                   	.byte 0x20
  4036a2:	25                   	.byte 0x25
  4036a3:	78 0a                	js     4036af <.INDEX+0x9>
	...

00000000004036a6 <.INDEX>:
  4036a6:	43 6f                	rex.XB outsl %ds:(%rsi),(%dx)
  4036a8:	72 6f                	jb     403719 <switch_to+0x16>
  4036aa:	75 74                	jne    403720 <switch_to+0x1d>
  4036ac:	69 6e 65 20 69 6e 64 	imul   $0x646e6920,0x65(%rsi),%ebp
  4036b3:	65 78 2e             	gs js  4036e4 <.CURSTACK+0x2>
  4036b6:	2e                   	cs
  4036b7:	2e                   	cs
  4036b8:	20                   	.byte 0x20
  4036b9:	25                   	.byte 0x25
  4036ba:	64 0a 00             	or     %fs:(%rax),%al

00000000004036bd <.RET>:
  4036bd:	52                   	push   %rdx
  4036be:	65 74 75             	gs je  403736 <switch_to+0x33>
  4036c1:	72 6e                	jb     403731 <switch_to+0x2e>
  4036c3:	65 64 53             	gs fs push %rbx
  4036c6:	74 61                	je     403729 <switch_to+0x26>
  4036c8:	63 6b 2e             	movsxd 0x2e(%rbx),%ebp
  4036cb:	2e                   	cs
  4036cc:	2e                   	cs
  4036cd:	20                   	.byte 0x20
  4036ce:	25                   	.byte 0x25
  4036cf:	70 0a                	jo     4036db <.STACK+0x9>
	...

00000000004036d2 <.STACK>:
  4036d2:	43                   	rex.XB
  4036d3:	4f 20 53 74          	rex.WRXB and %r10b,0x74(%r11)
  4036d7:	61                   	(bad)
  4036d8:	63 6b 2e             	movsxd 0x2e(%rbx),%ebp
  4036db:	2e                   	cs
  4036dc:	2e                   	cs
  4036dd:	20                   	.byte 0x20
  4036de:	25                   	.byte 0x25
  4036df:	70 0a                	jo     4036eb <.CURSTACK+0x9>
	...

00000000004036e2 <.CURSTACK>:
  4036e2:	53                   	push   %rbx
  4036e3:	61                   	(bad)
  4036e4:	76 65                	jbe    40374b <switch_to+0x48>
  4036e6:	64 53                	fs push %rbx
  4036e8:	74 61                	je     40374b <switch_to+0x48>
  4036ea:	63 6b 2e             	movsxd 0x2e(%rbx),%ebp
  4036ed:	2e                   	cs
  4036ee:	20                   	.byte 0x20
  4036ef:	25                   	.byte 0x25
  4036f0:	70 0a                	jo     4036fc <.SCHED+0x9>
	...

00000000004036f3 <.SCHED>:
  4036f3:	53                   	push   %rbx
  4036f4:	63 68 65             	movsxd 0x65(%rax),%ebp
  4036f7:	64 75 6c             	fs jne 403766 <switch_to+0x63>
  4036fa:	65 72 2e             	gs jb  40372b <switch_to+0x28>
  4036fd:	2e                   	cs
  4036fe:	20                   	.byte 0x20
  4036ff:	25                   	.byte 0x25
  403700:	70 0a                	jo     40370c <switch_to+0x9>
	...

0000000000403703 <switch_to>:
	.text
	# switch_to(struct Coroutine * coroutines, int index, struct Scheduler * scheduler)
	# rdi, %rsi, %rdx, %rcx, %r8 and %r9
switch_to:
# popq %r11
pushq %rbp
  403703:	55                   	push   %rbp

movq %rsp, %rbp
  403704:	48 89 e5             	mov    %rsp,%rbp
subq $1024, %rsp
  403707:	48 81 ec 00 04 00 00 	sub    $0x400,%rsp



movq %rdi, -56(%rbp) # coroutine table
  40370e:	48 89 7d c8          	mov    %rdi,-0x38(%rbp)
movq %rsi, -8(%rbp) # index
  403712:	48 89 75 f8          	mov    %rsi,-0x8(%rbp)
movq %rdx, -16(%rbp) # scheduler
  403716:	48 89 55 f0          	mov    %rdx,-0x10(%rbp)


movq %rsi, %rax
  40371a:	48 89 f0             	mov    %rsi,%rax
imul $32, %rax
  40371d:	48 6b c0 20          	imul   $0x20,%rax,%rax
addq %rdi, %rax
  403721:	48 01 f8             	add    %rdi,%rax
mov %rax, %r11
  403724:	49 89 c3             	mov    %rax,%r11

mov %r11, %rax
  403727:	4c 89 d8             	mov    %r11,%rax
movq %rax, %r9
  40372a:	49 89 c1             	mov    %rax,%r9
movq %r9, -24(%rbp) # coroutine object
  40372d:	4c 89 4d e8          	mov    %r9,-0x18(%rbp)

movq %r11, %rax
  403731:	4c 89 d8             	mov    %r11,%rax
leaq 8(%rax), %rax
  403734:	48 8d 40 08          	lea    0x8(%rax),%rax
movq %rax, %r9
  403738:	49 89 c1             	mov    %rax,%r9
movq %r9, -48(%rbp) # rsp
  40373b:	4c 89 4d d0          	mov    %r9,-0x30(%rbp)

movq %r11, %rax
  40373f:	4c 89 d8             	mov    %r11,%rax
leaq 16(%rax), %rax
  403742:	48 8d 40 10          	lea    0x10(%rax),%rax
movq (%rax), %r9
  403746:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -32(%rbp) # coroutine function
  403749:	4c 89 4d e0          	mov    %r9,-0x20(%rbp)

movq %r11, %rax
  40374d:	4c 89 d8             	mov    %r11,%rax
leaq 8(%rax), %rax
  403750:	48 8d 40 08          	lea    0x8(%rax),%rax
movq (%rax), %r9
  403754:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -64(%rbp) # coroutine stack
  403757:	4c 89 4d c0          	mov    %r9,-0x40(%rbp)

movq %r11, %rax
  40375b:	4c 89 d8             	mov    %r11,%rax
leaq 24(%rax), %rax # load from coroutine object data object
  40375e:	48 8d 40 18          	lea    0x18(%rax),%rax
movq (%rax), %r9
  403762:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -40(%rbp) # coroutine data object
  403765:	4c 89 4d d8          	mov    %r9,-0x28(%rbp)
movq (%rax), %rcx
  403769:	48 8b 08             	mov    (%rax),%rcx

movq -24(%rbp), %r11
  40376c:	4c 8b 5d e8          	mov    -0x18(%rbp),%r11
#

leaq .INDEX(%rip), %rdi
  403770:	48 8d 3d 2f ff ff ff 	lea    -0xd1(%rip),%rdi        # 4036a6 <.INDEX>
#call printf@plt
mov $0, %eax
  403777:	b8 00 00 00 00       	mov    $0x0,%eax

#pushq %r11
leaq .MSG(%rip), %rdi
  40377c:	48 8d 3d ed fe ff ff 	lea    -0x113(%rip),%rdi        # 403670 <.MSG>
movq %r11, %rsi
  403783:	4c 89 de             	mov    %r11,%rsi
# call printf@plt
mov $0, %eax
  403786:	b8 00 00 00 00       	mov    $0x0,%eax

leaq .SCHED(%rip), %rdi
  40378b:	48 8d 3d 61 ff ff ff 	lea    -0x9f(%rip),%rdi        # 4036f3 <.SCHED>
movq -16(%rbp), %rsi
  403792:	48 8b 75 f0          	mov    -0x10(%rbp),%rsi
call printf@plt
  403796:	e8 e5 d8 ff ff       	call   401080 <printf@plt>
mov $0, %eax
  40379b:	b8 00 00 00 00       	mov    $0x0,%eax

#popq %r11

#pushq %r9
movq -32(%rbp), %r9
  4037a0:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9

leaq .EIP(%rip), %rdi
  4037a4:	48 8d 3d dc fe ff ff 	lea    -0x124(%rip),%rdi        # 403687 <.EIP>
movq %r9, %rsi
  4037ab:	4c 89 ce             	mov    %r9,%rsi
#call printf@plt
mov $0, %eax
  4037ae:	b8 00 00 00 00       	mov    $0x0,%eax
#popq %r9
# coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data

#pushq %r9
leaq .CODATA(%rip), %rdi
  4037b3:	48 8d 3d db fe ff ff 	lea    -0x125(%rip),%rdi        # 403695 <.CODATA>
movq -40(%rbp), %rsi
  4037ba:	48 8b 75 d8          	mov    -0x28(%rbp),%rsi
#call printf@plt
mov $0, %eax
  4037be:	b8 00 00 00 00       	mov    $0x0,%eax





movq -16(%rbp), %rax
  4037c3:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
movq %rsp, 0(%rax)
  4037c7:	48 89 20             	mov    %rsp,(%rax)

leaq .CURSTACK(%rip), %rdi
  4037ca:	48 8d 3d 11 ff ff ff 	lea    -0xef(%rip),%rdi        # 4036e2 <.CURSTACK>
movq 0(%rax), %rsi
  4037d1:	48 8b 30             	mov    (%rax),%rsi
call printf@plt
  4037d4:	e8 a7 d8 ff ff       	call   401080 <printf@plt>
mov $0, %eax
  4037d9:	b8 00 00 00 00       	mov    $0x0,%eax





leaq .STACK(%rip), %rdi
  4037de:	48 8d 3d ed fe ff ff 	lea    -0x113(%rip),%rdi        # 4036d2 <.STACK>
movq -64(%rbp), %rsi
  4037e5:	48 8b 75 c0          	mov    -0x40(%rbp),%rsi
call printf@plt
  4037e9:	e8 92 d8 ff ff       	call   401080 <printf@plt>
mov $0, %eax
  4037ee:	b8 00 00 00 00       	mov    $0x0,%eax

movq -64(%rbp), %rsp # set stack to coroutine
  4037f3:	48 8b 65 c0          	mov    -0x40(%rbp),%rsp

movq -32(%rbp), %r9
  4037f7:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9
leaq after(%rip), %r11
  4037fb:	4c 8d 1d 17 00 00 00 	lea    0x17(%rip),%r11        # 403819 <after>
sub $8, %rsp
  403802:	48 83 ec 08          	sub    $0x8,%rsp
movq %r11, (%rsp) # set stack return address
  403806:	4c 89 1c 24          	mov    %r11,(%rsp)

movq -16(%rbp), %rdi
  40380a:	48 8b 7d f0          	mov    -0x10(%rbp),%rdi
movq -24(%rbp), %rsi
  40380e:	48 8b 75 e8          	mov    -0x18(%rbp),%rsi
movq -40(%rbp), %rdx
  403812:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx

# pushq %rbp
jmp *%r9
  403816:	41 ff e1             	jmp    *%r9

0000000000403819 <after>:
# pushq %rbp
# popq %rbp
#movq %rsp, %rbp

#pushq %rax
movq %rax, %rsp
  403819:	48 89 c4             	mov    %rax,%rsp
# movq %rsp, %rbp

leaq .RET(%rip), %rdi
  40381c:	48 8d 3d 9a fe ff ff 	lea    -0x166(%rip),%rdi        # 4036bd <.RET>
movq %rax, %rsi
  403823:	48 89 c6             	mov    %rax,%rsi
call printf@plt
  403826:	e8 55 d8 ff ff       	call   401080 <printf@plt>
mov $0, %eax
  40382b:	b8 00 00 00 00       	mov    $0x0,%eax




#pop %rbp
add $1024, %rsp
  403830:	48 81 c4 00 04 00 00 	add    $0x400,%rsp
#movq %rsp, %rbp
popq %rbp
  403837:	5d                   	pop    %rbp
  403838:	c3                   	ret

Disassembly of section .fini:

000000000040383c <_fini>:
  40383c:	f3 0f 1e fa          	endbr64
  403840:	48 83 ec 08          	sub    $0x8,%rsp
  403844:	48 83 c4 08          	add    $0x8,%rsp
  403848:	c3                   	ret
