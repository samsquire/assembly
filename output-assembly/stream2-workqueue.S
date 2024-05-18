
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
  401148:	48 c7 c7 69 20 40 00 	mov    $0x402069,%rdi
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

int coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data) {
  40121d:	55                   	push   %rbp
  40121e:	48 89 e5             	mov    %rsp,%rbp
  401221:	48 83 ec 20          	sub    $0x20,%rsp
  401225:	48 89 7d f8          	mov    %rdi,-0x8(%rbp)
  401229:	48 89 75 f0          	mov    %rsi,-0x10(%rbp)
  40122d:	48 89 55 e8          	mov    %rdx,-0x18(%rbp)
 printf("%p %p %p coro\n", scheduler, coroutine, data); 
  401231:	48 8b 4d e8          	mov    -0x18(%rbp),%rcx
  401235:	48 8b 55 f0          	mov    -0x10(%rbp),%rdx
  401239:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  40123d:	48 89 c6             	mov    %rax,%rsi
  401240:	48 8d 05 c1 2d 00 00 	lea    0x2dc1(%rip),%rax        # 404008 <_IO_stdin_used+0x8>
  401247:	48 89 c7             	mov    %rax,%rdi
  40124a:	b8 00 00 00 00       	mov    $0x0,%eax
  40124f:	e8 2c fe ff ff       	call   401080 <printf@plt>


  while (data->running == 1) {
  401254:	eb 1f                	jmp    401275 <coroutine_func+0x58>
   /*asm("lea 0(%%rip), %%r11\n"
      "movq %%r11, %0" : "=rm" (coroutine->eip) ::"r11");
      */
    // yield(1, scheduler, coroutine);
    printf("%ld\n", coroutine->eip); 
  401256:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  40125a:	48 8b 40 10          	mov    0x10(%rax),%rax
  40125e:	48 89 c6             	mov    %rax,%rsi
  401261:	48 8d 05 af 2d 00 00 	lea    0x2daf(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  401268:	48 89 c7             	mov    %rax,%rdi
  40126b:	b8 00 00 00 00       	mov    $0x0,%eax
  401270:	e8 0b fe ff ff       	call   401080 <printf@plt>
  while (data->running == 1) {
  401275:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401279:	8b 00                	mov    (%rax),%eax
  40127b:	83 f8 01             	cmp    $0x1,%eax
  40127e:	74 d6                	je     401256 <coroutine_func+0x39>
         
  }
  //printf("loop finished\n");
  return 0; 
  401280:	b8 00 00 00 00       	mov    $0x0,%eax

 
}
  401285:	c9                   	leave
  401286:	c3                   	ret

0000000000401287 <pollthreads>:
// thread 2
if tasks.taskindex > threads[0].workindex:
  value = 2
*/

int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  401287:	55                   	push   %rbp
  401288:	48 89 e5             	mov    %rsp,%rbp
  40128b:	48 89 7d d8          	mov    %rdi,-0x28(%rbp)
  40128f:	48 89 75 d0          	mov    %rsi,-0x30(%rbp)
  401293:	48 89 55 c8          	mov    %rdx,-0x38(%rbp)
  401297:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
  40129b:	4c 89 45 b8          	mov    %r8,-0x48(%rbp)
  long WM = WRITE_MASK;
  40129f:	48 c7 45 f0 04 00 00 00 	movq   $0x4,-0x10(%rbp)
  long RM = READ_MASK;
  4012a7:	48 c7 45 f8 08 00 00 00 	movq   $0x8,-0x8(%rbp)
  for (int x = 1; x < data->threadsize ; x++) {
  4012af:	c7 45 e8 01 00 00 00 	movl   $0x1,-0x18(%rbp)
  4012b6:	e9 9b 00 00 00       	jmp    401356 <pollthreads+0xcf>
  // printf("thread %d %ld\n", x, data->threads[x].ready);
    int mask = data->threads[1].readies[x];
  4012bb:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4012bf:	48 8b 40 30          	mov    0x30(%rax),%rax
  4012c3:	48 05 00 04 00 00    	add    $0x400,%rax
  4012c9:	48 8b 50 20          	mov    0x20(%rax),%rdx
  4012cd:	8b 45 e8             	mov    -0x18(%rbp),%eax
  4012d0:	48 98                	cltq
  4012d2:	48 c1 e0 02          	shl    $0x2,%rax
  4012d6:	48 01 d0             	add    %rdx,%rax
  4012d9:	8b 00                	mov    (%rax),%eax
  4012db:	89 45 ec             	mov    %eax,-0x14(%rbp)
        //printf("pollpread? %ld %ld\n", mask, (mask & PREP_READ_MASK));
       // printf("pplreadmask? %ld %ld\n", mask, (mask & READ_MASK));
      //  printf("pollwritemask ? %ld %ld\n", mask, (mask & WRITE_MASK));
       // data->threads[x].newmask = 0;
        
        if ((mask & WM) == WM || mask == 0) {
  4012de:	8b 45 ec             	mov    -0x14(%rbp),%eax
  4012e1:	48 98                	cltq
  4012e3:	48 23 45 f0          	and    -0x10(%rbp),%rax
  4012e7:	48 39 45 f0          	cmp    %rax,-0x10(%rbp)
  4012eb:	74 06                	je     4012f3 <pollthreads+0x6c>
  4012ed:	83 7d ec 00          	cmpl   $0x0,-0x14(%rbp)
  4012f1:	75 25                	jne    401318 <pollthreads+0x91>
         //printf("found a writer\n");
          readywriters[(*writers)++] = x;
  4012f3:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  4012f7:	8b 00                	mov    (%rax),%eax
  4012f9:	8d 48 01             	lea    0x1(%rax),%ecx
  4012fc:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
  401300:	89 0a                	mov    %ecx,(%rdx)
  401302:	48 98                	cltq
  401304:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  40130c:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
  401310:	48 01 c2             	add    %rax,%rdx
  401313:	8b 45 e8             	mov    -0x18(%rbp),%eax
  401316:	89 02                	mov    %eax,(%rdx)
        }
    if ((mask & RM) == RM || mask == 0) {
  401318:	8b 45 ec             	mov    -0x14(%rbp),%eax
  40131b:	48 98                	cltq
  40131d:	48 23 45 f8          	and    -0x8(%rbp),%rax
  401321:	48 39 45 f8          	cmp    %rax,-0x8(%rbp)
  401325:	74 06                	je     40132d <pollthreads+0xa6>
  401327:	83 7d ec 00          	cmpl   $0x0,-0x14(%rbp)
  40132b:	75 25                	jne    401352 <pollthreads+0xcb>
      readyreaders[(*readers)++] = x;
  40132d:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
  401331:	8b 00                	mov    (%rax),%eax
  401333:	8d 48 01             	lea    0x1(%rax),%ecx
  401336:	48 8b 55 c0          	mov    -0x40(%rbp),%rdx
  40133a:	89 0a                	mov    %ecx,(%rdx)
  40133c:	48 98                	cltq
  40133e:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401346:	48 8b 45 d0          	mov    -0x30(%rbp),%rax
  40134a:	48 01 c2             	add    %rax,%rdx
  40134d:	8b 45 e8             	mov    -0x18(%rbp),%eax
  401350:	89 02                	mov    %eax,(%rdx)
  for (int x = 1; x < data->threadsize ; x++) {
  401352:	83 45 e8 01          	addl   $0x1,-0x18(%rbp)
  401356:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  40135a:	8b 40 68             	mov    0x68(%rax),%eax
  40135d:	39 45 e8             	cmp    %eax,-0x18(%rbp)
  401360:	0f 8c 55 ff ff ff    	jl     4012bb <pollthreads+0x34>
    // printf("found a reader\n");
    }
      }
  // printf("%d readers %d writers\n", *readers, *writers);
      
  return 0;
  401366:	b8 00 00 00 00       	mov    $0x0,%eax
}
  40136b:	5d                   	pop    %rbp
  40136c:	c3                   	ret

000000000040136d <findavailable>:


int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  40136d:	55                   	push   %rbp
  40136e:	48 89 e5             	mov    %rsp,%rbp
  401371:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  401375:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
  401379:	48 89 55 d8          	mov    %rdx,-0x28(%rbp)
  40137d:	48 89 4d d0          	mov    %rcx,-0x30(%rbp)
  401381:	4c 89 45 c8          	mov    %r8,-0x38(%rbp)
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  401385:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
  40138c:	eb 64                	jmp    4013f2 <findavailable+0x85>
        
        if (data->freelist[x].available == FREE ) {
  40138e:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401392:	48 8b 90 a0 00 00 00 	mov    0xa0(%rax),%rdx
  401399:	8b 45 fc             	mov    -0x4(%rbp),%eax
  40139c:	48 98                	cltq
  40139e:	48 c1 e0 05          	shl    $0x5,%rax
  4013a2:	48 01 d0             	add    %rdx,%rax
  4013a5:	8b 40 10             	mov    0x10(%rax),%eax
  4013a8:	83 f8 01             	cmp    $0x1,%eax
  4013ab:	75 41                	jne    4013ee <findavailable+0x81>
          //printf("%d\n", *availableidx);
         available[*availableidx] = x;
  4013ad:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013b1:	8b 00                	mov    (%rax),%eax
  4013b3:	48 98                	cltq
  4013b5:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4013bd:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  4013c1:	48 01 c2             	add    %rax,%rdx
  4013c4:	8b 45 fc             	mov    -0x4(%rbp),%eax
  4013c7:	48 98                	cltq
  4013c9:	48 89 02             	mov    %rax,(%rdx)
         (*availableidx)++;
  4013cc:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013d0:	8b 00                	mov    (%rax),%eax
  4013d2:	8d 50 01             	lea    0x1(%rax),%edx
  4013d5:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013d9:	89 10                	mov    %edx,(%rax)
         if ((*availableidx) == data->threadsize * 2) {
  4013db:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013df:	8b 10                	mov    (%rax),%edx
  4013e1:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4013e5:	8b 40 68             	mov    0x68(%rax),%eax
  4013e8:	01 c0                	add    %eax,%eax
  4013ea:	39 c2                	cmp    %eax,%edx
  4013ec:	74 20                	je     40140e <findavailable+0xa1>
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
  4013ee:	83 45 fc 01          	addl   $0x1,-0x4(%rbp)
  4013f2:	8b 45 fc             	mov    -0x4(%rbp),%eax
  4013f5:	48 63 d0             	movslq %eax,%rdx
  4013f8:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4013fc:	48 8b 80 b8 00 00 00 	mov    0xb8(%rax),%rax
  401403:	48 83 c0 01          	add    $0x1,%rax
  401407:	48 39 c2             	cmp    %rax,%rdx
  40140a:	7c 82                	jl     40138e <findavailable+0x21>
  40140c:	eb 01                	jmp    40140f <findavailable+0xa2>
           break;
  40140e:	90                   	nop
         }

         // printf("%d chunk is free\n", x);
        }
      }
      if (*availableidx == 0) {
  40140f:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401413:	8b 00                	mov    (%rax),%eax
  401415:	85 c0                	test   %eax,%eax
  401417:	75 07                	jne    401420 <findavailable+0xb3>
       //printf("no chunks avail\n");
        
        return 1;
  401419:	b8 01 00 00 00       	mov    $0x1,%eax
  40141e:	eb 05                	jmp    401425 <findavailable+0xb8>
      }
  return 0;
  401420:	b8 00 00 00 00       	mov    $0x0,%eax
}
  401425:	5d                   	pop    %rbp
  401426:	c3                   	ret

0000000000401427 <singlewriter3>:

int singlewriter3(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401427:	55                   	push   %rbp
  401428:	48 89 e5             	mov    %rsp,%rbp
  40142b:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  40142f:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
  401433:	48 89 55 d8          	mov    %rdx,-0x28(%rbp)
  401437:	48 89 4d d0          	mov    %rcx,-0x30(%rbp)
  int completed = 0;
  40143b:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
   */



  //printf("%d %d\n", data->writecursor, data->writecursor % (data->threadsize - 1));
  if (data->writecursor != 0 && (data->writecursor % (data->threadsize - 1)) == 0) {
  401442:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401446:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  40144c:	85 c0                	test   %eax,%eax
    //printf("writeepoch\n");
  } else {

  }

}
  40144e:	90                   	nop
  40144f:	5d                   	pop    %rbp
  401450:	c3                   	ret

0000000000401451 <singlewriter2>:

int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  401451:	55                   	push   %rbp
  401452:	48 89 e5             	mov    %rsp,%rbp
  401455:	48 83 ec 40          	sub    $0x40,%rsp
  401459:	48 89 7d d8          	mov    %rdi,-0x28(%rbp)
  40145d:	48 89 75 d0          	mov    %rsi,-0x30(%rbp)
  401461:	48 89 55 c8          	mov    %rdx,-0x38(%rbp)
  401465:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
  int completed = 0;
  401469:	c7 45 ec 00 00 00 00 	movl   $0x0,-0x14(%rbp)
   }
   */


//if ((__atomic_load_n(&data->readcursor, __ATOMIC_SEQ_CST) % data->threadsize) == 0) {
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
  401470:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401474:	8b 80 00 02 00 00    	mov    0x200(%rax),%eax
  40147a:	85 c0                	test   %eax,%eax
  40147c:	0f 84 c7 00 00 00    	je     401549 <singlewriter2+0xf8>
  401482:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401486:	8b 80 00 02 00 00    	mov    0x200(%rax),%eax
  40148c:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  401490:	8b 52 68             	mov    0x68(%rdx),%edx
  401493:	8d 4a ff             	lea    -0x1(%rdx),%ecx
  401496:	99                   	cltd
  401497:	f7 f9                	idiv   %ecx
  401499:	89 d0                	mov    %edx,%eax
  40149b:	85 c0                	test   %eax,%eax
  40149d:	0f 85 a6 00 00 00    	jne    401549 <singlewriter2+0xf8>
   // data->readcursor = 0;
    //printf("readepoch\n");
    
  
        // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
        struct Data * thread = &data->threads[data->threadindex];
  4014a3:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014a7:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4014ab:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014af:	8b 40 64             	mov    0x64(%rax),%eax
  4014b2:	48 98                	cltq
  4014b4:	48 c1 e0 0a          	shl    $0xa,%rax
  4014b8:	48 01 d0             	add    %rdx,%rax
  4014bb:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
  4014bf:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4014c3:	48 8b 88 18 03 00 00 	mov    0x318(%rax),%rcx
  4014ca:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4014ce:	8b 80 24 03 00 00    	mov    0x324(%rax),%eax
  4014d4:	48 63 d0             	movslq %eax,%rdx
  4014d7:	48 89 d0             	mov    %rdx,%rax
  4014da:	48 01 c0             	add    %rax,%rax
  4014dd:	48 01 d0             	add    %rdx,%rax
  4014e0:	48 c1 e0 04          	shl    $0x4,%rax
  4014e4:	48 01 c8             	add    %rcx,%rax
  4014e7:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  4014eb:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  4014ef:	48 83 c0 08          	add    $0x8,%rax
  4014f3:	48 89 c6             	mov    %rax,%rsi
  4014f6:	bf 04 00 00 00       	mov    $0x4,%edi
  4014fb:	e8 50 fb ff ff       	call   401050 <clock_gettime@plt>
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
  401500:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401504:	8b 80 24 03 00 00    	mov    0x324(%rax),%eax
  40150a:	8d 50 01             	lea    0x1(%rax),%edx
  40150d:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401511:	8b 88 20 03 00 00    	mov    0x320(%rax),%ecx
  401517:	89 d0                	mov    %edx,%eax
  401519:	99                   	cltd
  40151a:	f7 f9                	idiv   %ecx
  40151c:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401520:	89 90 24 03 00 00    	mov    %edx,0x324(%rax)
        epoch->kind = NEW_EPOCH;
  401526:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  40152a:	c7 40 20 01 00 00 00 	movl   $0x1,0x20(%rax)
        epoch->thread = data->threadindex;
  401531:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401535:	8b 50 64             	mov    0x64(%rax),%edx
  401538:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  40153c:	89 10                	mov    %edx,(%rax)
        epoch->set = 1;
  40153e:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401542:	c7 40 24 01 00 00 00 	movl   $0x1,0x24(%rax)
  } else {
    
  }

  
}
  401549:	90                   	nop
  40154a:	c9                   	leave
  40154b:	c3                   	ret

000000000040154c <singlewriter>:



*/

int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  40154c:	55                   	push   %rbp
  40154d:	48 89 e5             	mov    %rsp,%rbp
  401550:	48 83 ec 70          	sub    $0x70,%rsp
  401554:	48 89 7d a8          	mov    %rdi,-0x58(%rbp)
  401558:	48 89 75 a0          	mov    %rsi,-0x60(%rbp)
  40155c:	48 89 55 98          	mov    %rdx,-0x68(%rbp)
  401560:	48 89 4d 90          	mov    %rcx,-0x70(%rbp)
  401564:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40156d:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  401571:	31 c0                	xor    %eax,%eax
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  401573:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401577:	48 8b 40 30          	mov    0x30(%rax),%rax
  40157b:	8b 80 0c 02 00 00    	mov    0x20c(%rax),%eax
  401581:	8d 50 01             	lea    0x1(%rax),%edx
  401584:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401588:	8b 70 68             	mov    0x68(%rax),%esi
  40158b:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40158f:	48 8b 48 30          	mov    0x30(%rax),%rcx
  401593:	89 d0                	mov    %edx,%eax
  401595:	99                   	cltd
  401596:	f7 fe                	idiv   %esi
  401598:	89 d0                	mov    %edx,%eax
  40159a:	89 81 0c 02 00 00    	mov    %eax,0x20c(%rcx)
  int readers = 0;
  4015a0:	c7 45 b0 00 00 00 00 	movl   $0x0,-0x50(%rbp)
  int writers = 0;
  4015a7:	c7 45 b4 00 00 00 00 	movl   $0x0,-0x4c(%rbp)
  int availableidx = 0;
  4015ae:	c7 45 b8 00 00 00 00 	movl   $0x0,-0x48(%rbp)
    readywriters[x] = x;
  }
  */
  //clock_gettime(CLOCK_MONOTONIC_RAW, &data->wstart);
  
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);
  4015b5:	48 8b 7d 90          	mov    -0x70(%rbp),%rdi
  4015b9:	48 8b 4d 98          	mov    -0x68(%rbp),%rcx
  4015bd:	48 8d 55 b8          	lea    -0x48(%rbp),%rdx
  4015c1:	48 8b 75 a0          	mov    -0x60(%rbp),%rsi
  4015c5:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015c9:	49 89 f8             	mov    %rdi,%r8
  4015cc:	48 89 c7             	mov    %rax,%rdi
  4015cf:	e8 99 fd ff ff       	call   40136d <findavailable>
  4015d4:	89 45 cc             	mov    %eax,-0x34(%rbp)

//clock_gettime(CLOCK_MONOTONIC_RAW, &data->wavail);
  
  if (fill == 1) {
  4015d7:	83 7d cc 01          	cmpl   $0x1,-0x34(%rbp)
  4015db:	75 0a                	jne    4015e7 <singlewriter+0x9b>
    return 1;
  4015dd:	b8 01 00 00 00       	mov    $0x1,%eax
  4015e2:	e9 f9 02 00 00       	jmp    4018e0 <singlewriter+0x394>
  }
      
   //printf("buffers available %d\n", availableidx);
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
  4015e7:	48 8d 7d b4          	lea    -0x4c(%rbp),%rdi
  4015eb:	48 8d 4d b0          	lea    -0x50(%rbp),%rcx
  4015ef:	48 8b 55 90          	mov    -0x70(%rbp),%rdx
  4015f3:	48 8b 75 98          	mov    -0x68(%rbp),%rsi
  4015f7:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015fb:	49 89 f8             	mov    %rdi,%r8
  4015fe:	48 89 c7             	mov    %rax,%rdi
  401601:	e8 81 fc ff ff       	call   401287 <pollthreads>
      
  //clock_gettime(CLOCK_MONOTONIC_RAW, &data->wpoll);
      
      int assignedchunk = 0;
  401606:	c7 45 bc 00 00 00 00 	movl   $0x0,-0x44(%rbp)
      
        for (int x = 0; x < readers ; x++) {
  40160d:	c7 45 c0 00 00 00 00 	movl   $0x0,-0x40(%rbp)
  401614:	e9 10 01 00 00       	jmp    401729 <singlewriter+0x1dd>
          if (assignedchunk == availableidx) {
  401619:	8b 45 b8             	mov    -0x48(%rbp),%eax
  40161c:	39 45 bc             	cmp    %eax,-0x44(%rbp)
  40161f:	0f 84 12 01 00 00    	je     401737 <singlewriter+0x1eb>
           // printf("not enough space readers\n");
                  break;
          }
          int thread = readyreaders[x];
  401625:	8b 45 c0             	mov    -0x40(%rbp),%eax
  401628:	48 98                	cltq
  40162a:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401632:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  401636:	48 01 d0             	add    %rdx,%rax
  401639:	8b 00                	mov    (%rax),%eax
  40163b:	89 45 d0             	mov    %eax,-0x30(%rbp)
          //printf("%d %p\n", thread, &data->freelist[available[assignedchunk]]);
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  40163e:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401642:	48 8b 88 a0 00 00 00 	mov    0xa0(%rax),%rcx
  401649:	8b 45 bc             	mov    -0x44(%rbp),%eax
  40164c:	8d 50 01             	lea    0x1(%rax),%edx
  40164f:	89 55 bc             	mov    %edx,-0x44(%rbp)
  401652:	48 98                	cltq
  401654:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  40165c:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  401660:	48 01 d0             	add    %rdx,%rax
  401663:	48 8b 00             	mov    (%rax),%rax
  401666:	48 c1 e0 05          	shl    $0x5,%rax
  40166a:	48 01 c8             	add    %rcx,%rax
  40166d:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
          chunk->available = READING;
  401671:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401675:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
          //printf("assign %p\n", chunk);


          data->threads[thread].reading = chunk;
  40167c:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401680:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401684:	8b 45 d0             	mov    -0x30(%rbp),%eax
  401687:	48 98                	cltq
  401689:	48 c1 e0 0a          	shl    $0xa,%rax
  40168d:	48 01 c2             	add    %rax,%rdx
  401690:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401694:	48 89 82 a8 00 00 00 	mov    %rax,0xa8(%rdx)
          
          chunk->owner = thread;
  40169b:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  40169f:	8b 55 d0             	mov    -0x30(%rbp),%edx
  4016a2:	89 50 14             	mov    %edx,0x14(%rax)
          int start = chunk->start;
  4016a5:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016a9:	48 8b 00             	mov    (%rax),%rax
  4016ac:	89 45 d4             	mov    %eax,-0x2c(%rbp)
          data->threads[thread].start = start;
  4016af:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016b3:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016b7:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016ba:	48 98                	cltq
  4016bc:	48 c1 e0 0a          	shl    $0xa,%rax
  4016c0:	48 01 c2             	add    %rax,%rdx
  4016c3:	8b 45 d4             	mov    -0x2c(%rbp),%eax
  4016c6:	89 42 14             	mov    %eax,0x14(%rdx)
          
          int end = chunk->end;
  4016c9:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016cd:	48 8b 40 08          	mov    0x8(%rax),%rax
  4016d1:	89 45 d8             	mov    %eax,-0x28(%rbp)
          data->threads[thread].end = end;
  4016d4:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016d8:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016dc:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016df:	48 98                	cltq
  4016e1:	48 c1 e0 0a          	shl    $0xa,%rax
  4016e5:	48 01 c2             	add    %rax,%rdx
  4016e8:	8b 45 d8             	mov    -0x28(%rbp),%eax
  4016eb:	89 42 18             	mov    %eax,0x18(%rdx)
        // printf("reader giving %d between %ld and %ld\n", x, start, end);
        
         // clock_gettime(CLOCK_MONOTONIC_RAW, &data->main->works[start].created);
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
  4016ee:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016f2:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016f6:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016f9:	48 98                	cltq
  4016fb:	48 c1 e0 0a          	shl    $0xa,%rax
  4016ff:	48 01 d0             	add    %rdx,%rax
  401702:	8b 90 c8 00 00 00    	mov    0xc8(%rax),%edx
  401708:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40170c:	48 8b 48 30          	mov    0x30(%rax),%rcx
  401710:	8b 45 d0             	mov    -0x30(%rbp),%eax
  401713:	48 98                	cltq
  401715:	48 c1 e0 0a          	shl    $0xa,%rax
  401719:	48 01 c8             	add    %rcx,%rax
  40171c:	83 ca 10             	or     $0x10,%edx
  40171f:	89 90 c8 00 00 00    	mov    %edx,0xc8(%rax)
        for (int x = 0; x < readers ; x++) {
  401725:	83 45 c0 01          	addl   $0x1,-0x40(%rbp)
  401729:	8b 45 b0             	mov    -0x50(%rbp),%eax
  40172c:	39 45 c0             	cmp    %eax,-0x40(%rbp)
  40172f:	0f 8c e4 fe ff ff    	jl     401619 <singlewriter+0xcd>
  401735:	eb 01                	jmp    401738 <singlewriter+0x1ec>
                  break;
  401737:	90                   	nop
       // printf("read newmask ORed with %d\n", data->threads[thread].newmask);
        }
      
   for (int x = 0; x < writers ; x++) {
  401738:	c7 45 c4 00 00 00 00 	movl   $0x0,-0x3c(%rbp)
  40173f:	e9 10 01 00 00       	jmp    401854 <singlewriter+0x308>
                if (assignedchunk  == availableidx) {
  401744:	8b 45 b8             	mov    -0x48(%rbp),%eax
  401747:	39 45 bc             	cmp    %eax,-0x44(%rbp)
  40174a:	0f 84 12 01 00 00    	je     401862 <singlewriter+0x316>
                  
                 //printf("not enough space writer %d %d\n", assignedchunk, availableidx);
                  break;
                }
          int thread = readywriters[x];
  401750:	8b 45 c4             	mov    -0x3c(%rbp),%eax
  401753:	48 98                	cltq
  401755:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  40175d:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  401761:	48 01 d0             	add    %rdx,%rax
  401764:	8b 00                	mov    (%rax),%eax
  401766:	89 45 dc             	mov    %eax,-0x24(%rbp)
     
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
  401769:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40176d:	48 8b 88 a0 00 00 00 	mov    0xa0(%rax),%rcx
  401774:	8b 45 bc             	mov    -0x44(%rbp),%eax
  401777:	8d 50 01             	lea    0x1(%rax),%edx
  40177a:	89 55 bc             	mov    %edx,-0x44(%rbp)
  40177d:	48 98                	cltq
  40177f:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  401787:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  40178b:	48 01 d0             	add    %rdx,%rax
  40178e:	48 8b 00             	mov    (%rax),%rax
  401791:	48 c1 e0 05          	shl    $0x5,%rax
  401795:	48 01 c8             	add    %rcx,%rax
  401798:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
    
      chunk->available = WRITING;
  40179c:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017a0:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
          data->threads[thread].writing = chunk;
  4017a7:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4017ab:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4017af:	8b 45 dc             	mov    -0x24(%rbp),%eax
  4017b2:	48 98                	cltq
  4017b4:	48 c1 e0 0a          	shl    $0xa,%rax
  4017b8:	48 01 c2             	add    %rax,%rdx
  4017bb:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017bf:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
          chunk->owner = thread;
  4017c6:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017ca:	8b 55 dc             	mov    -0x24(%rbp),%edx
  4017cd:	89 50 14             	mov    %edx,0x14(%rax)
          int start = chunk->start;
  4017d0:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017d4:	48 8b 00             	mov    (%rax),%rax
  4017d7:	89 45 e0             	mov    %eax,-0x20(%rbp)
          data->threads[thread].publishstart = start;
  4017da:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4017de:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4017e2:	8b 45 dc             	mov    -0x24(%rbp),%eax
  4017e5:	48 98                	cltq
  4017e7:	48 c1 e0 0a          	shl    $0xa,%rax
  4017eb:	48 01 c2             	add    %rax,%rdx
  4017ee:	8b 45 e0             	mov    -0x20(%rbp),%eax
  4017f1:	89 42 40             	mov    %eax,0x40(%rdx)
          
          int end = chunk->end;
  4017f4:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017f8:	48 8b 40 08          	mov    0x8(%rax),%rax
  4017fc:	89 45 e4             	mov    %eax,-0x1c(%rbp)
          data->threads[thread].publishend = end;
  4017ff:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401803:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401807:	8b 45 dc             	mov    -0x24(%rbp),%eax
  40180a:	48 98                	cltq
  40180c:	48 c1 e0 0a          	shl    $0xa,%rax
  401810:	48 01 c2             	add    %rax,%rdx
  401813:	8b 45 e4             	mov    -0x1c(%rbp),%eax
  401816:	89 42 44             	mov    %eax,0x44(%rdx)
        //  printf("writer giving %d between %ld and %ld\n", available[assignedchunk], start, end);
          // asm volatile ("sfence" ::: "memory");
     
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
  401819:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40181d:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401821:	8b 45 dc             	mov    -0x24(%rbp),%eax
  401824:	48 98                	cltq
  401826:	48 c1 e0 0a          	shl    $0xa,%rax
  40182a:	48 01 d0             	add    %rdx,%rax
  40182d:	8b 90 c8 00 00 00    	mov    0xc8(%rax),%edx
  401833:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401837:	48 8b 48 30          	mov    0x30(%rax),%rcx
  40183b:	8b 45 dc             	mov    -0x24(%rbp),%eax
  40183e:	48 98                	cltq
  401840:	48 c1 e0 0a          	shl    $0xa,%rax
  401844:	48 01 c8             	add    %rcx,%rax
  401847:	83 ca 20             	or     $0x20,%edx
  40184a:	89 90 c8 00 00 00    	mov    %edx,0xc8(%rax)
   for (int x = 0; x < writers ; x++) {
  401850:	83 45 c4 01          	addl   $0x1,-0x3c(%rbp)
  401854:	8b 45 b4             	mov    -0x4c(%rbp),%eax
  401857:	39 45 c4             	cmp    %eax,-0x3c(%rbp)
  40185a:	0f 8c e4 fe ff ff    	jl     401744 <singlewriter+0x1f8>
  401860:	eb 01                	jmp    401863 <singlewriter+0x317>
                  break;
  401862:	90                   	nop
     //printf("write newmask ORed with %ld\n", data->threads[thread].newmask);
        
   } 
      for (int x = 0; x < data->threadsize ; x++) {
  401863:	c7 45 c8 00 00 00 00 	movl   $0x0,-0x38(%rbp)
  40186a:	eb 63                	jmp    4018cf <singlewriter+0x383>
        if (data->threads[x].newmask != 0) {
  40186c:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401870:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401874:	8b 45 c8             	mov    -0x38(%rbp),%eax
  401877:	48 98                	cltq
  401879:	48 c1 e0 0a          	shl    $0xa,%rax
  40187d:	48 01 d0             	add    %rdx,%rax
  401880:	8b 80 c8 00 00 00    	mov    0xc8(%rax),%eax
  401886:	85 c0                	test   %eax,%eax
  401888:	74 41                	je     4018cb <singlewriter+0x37f>
         // printf("thread %d %ld is now %ld\n", x, data->threads[x].ready, data->threads[x].newmask);
          data->threads[x].readies[x] = data->threads[x].newmask;
  40188a:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40188e:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401892:	8b 45 c8             	mov    -0x38(%rbp),%eax
  401895:	48 98                	cltq
  401897:	48 c1 e0 0a          	shl    $0xa,%rax
  40189b:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
  40189f:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018a3:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4018a7:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018aa:	48 98                	cltq
  4018ac:	48 c1 e0 0a          	shl    $0xa,%rax
  4018b0:	48 01 d0             	add    %rdx,%rax
  4018b3:	48 8b 50 20          	mov    0x20(%rax),%rdx
  4018b7:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018ba:	48 98                	cltq
  4018bc:	48 c1 e0 02          	shl    $0x2,%rax
  4018c0:	48 01 c2             	add    %rax,%rdx
  4018c3:	8b 81 c8 00 00 00    	mov    0xc8(%rcx),%eax
  4018c9:	89 02                	mov    %eax,(%rdx)
      for (int x = 0; x < data->threadsize ; x++) {
  4018cb:	83 45 c8 01          	addl   $0x1,-0x38(%rbp)
  4018cf:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018d3:	8b 40 68             	mov    0x68(%rax),%eax
  4018d6:	39 45 c8             	cmp    %eax,-0x38(%rbp)
  4018d9:	7c 91                	jl     40186c <singlewriter+0x320>
        
          
        }
      }
  // clock_gettime(CLOCK_MONOTONIC_RAW, &data->wassign);
  return 0;
  4018db:	b8 00 00 00 00       	mov    $0x0,%eax
}
  4018e0:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  4018e4:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  4018ed:	74 05                	je     4018f4 <singlewriter+0x3a8>
  4018ef:	e8 7c f7 ff ff       	call   401070 <__stack_chk_fail@plt>
  4018f4:	c9                   	leave
  4018f5:	c3                   	ret

00000000004018f6 <threadwork>:

int * threadwork(struct Data * data) {
  4018f6:	55                   	push   %rbp
  4018f7:	48 89 e5             	mov    %rsp,%rbp
  4018fa:	48 81 ec 90 00 00 00 	sub    $0x90,%rsp
  401901:	48 89 bd 78 ff ff ff 	mov    %rdi,-0x88(%rbp)
  401908:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401911:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  401915:	31 c0                	xor    %eax,%eax
  int cursorlimit = 5;
  401917:	c7 45 a4 05 00 00 00 	movl   $0x5,-0x5c(%rbp)
  int epochsize = 1;
  40191e:	c7 45 a8 01 00 00 00 	movl   $0x1,-0x58(%rbp)
  int epochwidth = 0xff;
  401925:	c7 45 ac ff 00 00 00 	movl   $0xff,-0x54(%rbp)

//printf("%ld %ld w%d\n", lastwrite, data->prevwrite, data->threadindex);
 //if (lastwrite != data->prevwrite) {
   
    uint64_t rsp;
    asm( "mov %%rsp, %0" : "=rm" ( rsp ));
  40192c:	48 89 e0             	mov    %rsp,%rax
  40192f:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
  data->scheduler->rsp = rsp;
  401933:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  40193a:	48 8b 80 c8 03 00 00 	mov    0x3c8(%rax),%rax
  401941:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  401945:	48 89 10             	mov    %rdx,(%rax)
  // switch_to(struct Coroutine * coroutines, int index
  //printf("table %x\n", (void *)data->coroutines);
 // printf("coroutine 3 %x\n", &data->coroutines[3]);
 // printf("coroutine eip %lx\n", data->coroutines[3].eip);
 // printf("coroutine data %lx\n", data->coroutines[3].data);
  switch_to(data->coroutines, 3, data->scheduler);  
  401948:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  40194f:	48 8b 90 c8 03 00 00 	mov    0x3c8(%rax),%rdx
  401956:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  40195d:	48 8b 80 c0 03 00 00 	mov    0x3c0(%rax),%rax
  401964:	be 03 00 00 00       	mov    $0x3,%esi
  401969:	48 89 c7             	mov    %rax,%rdi
  40196c:	e8 aa 1c 00 00       	call   40361b <switch_to>
  //printf("finished coroutine\n");
  //printf("%ld %ld w%d\n", lastwrite, data->prevwrite, data->threadindex);
     
       
clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  401971:	48 8d 45 e0          	lea    -0x20(%rbp),%rax
  401975:	48 89 c6             	mov    %rax,%rsi
  401978:	bf 04 00 00 00       	mov    $0x4,%edi
  40197d:	e8 ce f6 ff ff       	call   401050 <clock_gettime@plt>
  //if (data->threadindex % 2 == 0) {
   
  if (data->running == 2) {
  401982:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401989:	8b 40 5c             	mov    0x5c(%rax),%eax
  40198c:	83 f8 02             	cmp    $0x2,%eax
  40198f:	0f 85 9f 01 00 00    	jne    401b34 <threadwork+0x23e>
  //if (data ->threadindex == 0 ) {
      

   for (int x = 0 ; x < data->threadsize ; x++) {
  401995:	c7 45 98 00 00 00 00 	movl   $0x0,-0x68(%rbp)
  40199c:	e9 50 01 00 00       	jmp    401af1 <threadwork+0x1fb>
      
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
  4019a1:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019a8:	48 8b 40 28          	mov    0x28(%rax),%rax
  4019ac:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  4019b3:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019ba:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  4019c0:	c1 e0 07             	shl    $0x7,%eax
  4019c3:	48 98                	cltq
  4019c5:	48 c1 e0 03          	shl    $0x3,%rax
  4019c9:	48 01 d0             	add    %rdx,%rax
  4019cc:	48 8b 00             	mov    (%rax),%rax
  4019cf:	8b 55 a8             	mov    -0x58(%rbp),%edx
  4019d2:	48 63 fa             	movslq %edx,%rdi
  4019d5:	48 99                	cqto
  4019d7:	48 f7 ff             	idiv   %rdi
  4019da:	48 89 c2             	mov    %rax,%rdx
  4019dd:	8b 45 ac             	mov    -0x54(%rbp),%eax
  4019e0:	48 63 c8             	movslq %eax,%rcx
  4019e3:	48 89 d0             	mov    %rdx,%rax
  4019e6:	48 99                	cqto
  4019e8:	48 f7 f9             	idiv   %rcx
  4019eb:	48 89 d0             	mov    %rdx,%rax
  4019ee:	89 45 9c             	mov    %eax,-0x64(%rbp)
    
      //  buffer = data->mystream << 24 | ( global << 16) | data->threadindex << 8 | data->writecursor % 0xff;
    int cursor = data->writecursor;
  4019f1:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019f8:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  4019fe:	89 45 a0             	mov    %eax,-0x60(%rbp)
    //cursor = 0;
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;
  401a01:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a08:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401a0e:	c1 e0 18             	shl    $0x18,%eax
  401a11:	89 c2                	mov    %eax,%edx
  401a13:	8b 45 9c             	mov    -0x64(%rbp),%eax
  401a16:	c1 e0 10             	shl    $0x10,%eax
  401a19:	89 d6                	mov    %edx,%esi
  401a1b:	09 c6                	or     %eax,%esi
  401a1d:	8b 45 a0             	mov    -0x60(%rbp),%eax
  401a20:	48 63 d0             	movslq %eax,%rdx
  401a23:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401a2a:	48 c1 ea 20          	shr    $0x20,%rdx
  401a2e:	01 c2                	add    %eax,%edx
  401a30:	c1 fa 07             	sar    $0x7,%edx
  401a33:	89 c7                	mov    %eax,%edi
  401a35:	c1 ff 1f             	sar    $0x1f,%edi
  401a38:	89 d1                	mov    %edx,%ecx
  401a3a:	29 f9                	sub    %edi,%ecx
  401a3c:	89 ca                	mov    %ecx,%edx
  401a3e:	c1 e2 08             	shl    $0x8,%edx
  401a41:	29 ca                	sub    %ecx,%edx
  401a43:	29 d0                	sub    %edx,%eax
  401a45:	89 c1                	mov    %eax,%ecx
  401a47:	89 f0                	mov    %esi,%eax
  401a49:	09 c8                	or     %ecx,%eax
  401a4b:	48 98                	cltq
  401a4d:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
      buffer = data->mystream << 24 | ( (data->main->globalwrite[data->mystream * 128] / (data->threadsize)) % 0xff) << 16 | data->writecursor;
    }
    */
      // printf("%x\n", buffer);
        // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
  struct Data * thread = &data->threads[data->threadindex];
  401a51:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a58:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401a5c:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a63:	8b 40 64             	mov    0x64(%rax),%eax
  401a66:	48 98                	cltq
  401a68:	48 c1 e0 0a          	shl    $0xa,%rax
  401a6c:	48 01 d0             	add    %rdx,%rax
  401a6f:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
  epoch->buffer = buffer;
  epoch->set = 1;
  }
    
     // printf("alrrady filled\n");
  if (data->main->works[buffer] != -1) {
  401a73:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a7a:	48 8b 40 28          	mov    0x28(%rax),%rax
  401a7e:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401a82:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401a86:	48 01 d0             	add    %rdx,%rax
  401a89:	0f b6 00             	movzbl (%rax),%eax
  401a8c:	3c ff                	cmp    $0xff,%al
  401a8e:	74 1a                	je     401aaa <threadwork+0x1b4>
    
    data->freq_writes++;
  401a90:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a97:	48 8b 40 50          	mov    0x50(%rax),%rax
  401a9b:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401a9f:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401aa6:	48 89 50 50          	mov    %rdx,0x50(%rax)
  }
  data->main->works[buffer] = data->threadindex;
  401aaa:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ab1:	8b 50 64             	mov    0x64(%rax),%edx
  401ab4:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401abb:	48 8b 40 28          	mov    0x28(%rax),%rax
  401abf:	48 8b 48 70          	mov    0x70(%rax),%rcx
  401ac3:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401ac7:	48 01 c8             	add    %rcx,%rax
  401aca:	88 10                	mov    %dl,(%rax)
         
         
  //  data->prevread = data->main->currentread;
     
     
    data->writecursor = (data->writecursor + 1) % cursorlimit;
  401acc:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ad3:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401ad9:	83 c0 01             	add    $0x1,%eax
  401adc:	99                   	cltd
  401add:	f7 7d a4             	idivl  -0x5c(%rbp)
  401ae0:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ae7:	89 90 80 01 00 00    	mov    %edx,0x180(%rax)
   for (int x = 0 ; x < data->threadsize ; x++) {
  401aed:	83 45 98 01          	addl   $0x1,-0x68(%rbp)
  401af1:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401af8:	8b 40 68             	mov    0x68(%rax),%eax
  401afb:	39 45 98             	cmp    %eax,-0x68(%rbp)
  401afe:	0f 8c 9d fe ff ff    	jl     4019a1 <threadwork+0xab>
    
   }
      
    __atomic_fetch_add(&data->main->globalwrite[data->mystream * 128], 1, __ATOMIC_RELAXED);
  401b04:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b0b:	48 8b 40 28          	mov    0x28(%rax),%rax
  401b0f:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401b16:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b1d:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401b23:	c1 e0 07             	shl    $0x7,%eax
  401b26:	48 98                	cltq
  401b28:	48 c1 e0 03          	shl    $0x3,%rax
  401b2c:	48 01 d0             	add    %rdx,%rax
  401b2f:	f0 48 83 00 01       	lock addq $0x1,(%rax)
//}
  } 
  ///else {
  long thisgroup = data->main->globalwrite[data->mystream * 128] / epochsize;
  401b34:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b3b:	48 8b 40 28          	mov    0x28(%rax),%rax
  401b3f:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401b46:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b4d:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401b53:	c1 e0 07             	shl    $0x7,%eax
  401b56:	48 98                	cltq
  401b58:	48 c1 e0 03          	shl    $0x3,%rax
  401b5c:	48 01 d0             	add    %rdx,%rax
  401b5f:	48 8b 00             	mov    (%rax),%rax
  401b62:	8b 55 a8             	mov    -0x58(%rbp),%edx
  401b65:	48 63 fa             	movslq %edx,%rdi
  401b68:	48 99                	cqto
  401b6a:	48 f7 ff             	idiv   %rdi
  401b6d:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
  
  if (thisgroup != data->lastgroup) {
  401b71:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b78:	8b 80 88 03 00 00    	mov    0x388(%rax),%eax
  401b7e:	48 98                	cltq
  401b80:	48 39 45 c8          	cmp    %rax,-0x38(%rbp)
  401b84:	74 11                	je     401b97 <threadwork+0x2a1>
     // printf("ndw group\n");
      data->writecursor = 0;
  401b86:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b8d:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
        epoch->thread = data->threadindex;
        epoch->stream = data->mystream;
        epoch->set = 1;
     }
   }
   data->lastgroup = thisgroup;
  401b97:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
  401b9b:	89 c2                	mov    %eax,%edx
  401b9d:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ba4:	89 90 88 03 00 00    	mov    %edx,0x388(%rax)
  //}
  
 //if (lastread != data->prevread)
 // {
   //printf("%ld  %ld r%d\n", data->main->currentread, data->prevread, data->threadindex);
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  401baa:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bb1:	48 8b 40 28          	mov    0x28(%rax),%rax
  401bb5:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401bbc:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bc3:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401bc9:	c1 e0 07             	shl    $0x7,%eax
  401bcc:	48 98                	cltq
  401bce:	48 c1 e0 03          	shl    $0x3,%rax
  401bd2:	48 01 d0             	add    %rdx,%rax
  401bd5:	48 8b 00             	mov    (%rax),%rax
  401bd8:	48 89 45 d0          	mov    %rax,-0x30(%rbp)
  
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
  401bdc:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401be3:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401bea:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bf1:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401bf7:	48 63 d0             	movslq %eax,%rdx
  401bfa:	48 89 d0             	mov    %rdx,%rax
  401bfd:	48 01 c0             	add    %rax,%rax
  401c00:	48 01 d0             	add    %rdx,%rax
  401c03:	48 c1 e0 02          	shl    $0x2,%rax
  401c07:	48 01 c8             	add    %rcx,%rax
  401c0a:	8b 00                	mov    (%rax),%eax
  401c0c:	48 98                	cltq
  401c0e:	48 39 45 d0          	cmp    %rax,-0x30(%rbp)
  401c12:	7f 0b                	jg     401c1f <threadwork+0x329>
  401c14:	48 83 7d d0 00       	cmpq   $0x0,-0x30(%rbp)
  401c19:	0f 85 f9 02 00 00    	jne    401f18 <threadwork+0x622>
    for (int x = 0; x < data->threadsize - 1; x++) {
  401c1f:	c7 45 94 00 00 00 00 	movl   $0x0,-0x6c(%rbp)
  401c26:	e9 d7 02 00 00       	jmp    401f02 <threadwork+0x60c>
  // printf("%d\n", thiswrite);
   data->freq++;
  401c2b:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c32:	48 8b 40 48          	mov    0x48(%rax),%rax
  401c36:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401c3a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c41:	48 89 50 48          	mov    %rdx,0x48(%rax)
  
        
      
          
            
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
  401c45:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c4c:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401c53:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c5a:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401c60:	48 63 d0             	movslq %eax,%rdx
  401c63:	48 89 d0             	mov    %rdx,%rax
  401c66:	48 01 c0             	add    %rax,%rax
  401c69:	48 01 d0             	add    %rdx,%rax
  401c6c:	48 c1 e0 02          	shl    $0x2,%rax
  401c70:	48 01 c8             	add    %rcx,%rax
  401c73:	8b 00                	mov    (%rax),%eax
  401c75:	99                   	cltd
  401c76:	f7 7d a8             	idivl  -0x58(%rbp)
  401c79:	83 e8 01             	sub    $0x1,%eax
  401c7c:	99                   	cltd
  401c7d:	f7 7d ac             	idivl  -0x54(%rbp)
  401c80:	89 d0                	mov    %edx,%eax
  401c82:	48 98                	cltq
  401c84:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
        //long past = (((data->globalread[data->laststream]).global % epochwidth;
            if (past < 0) {
  401c88:	48 83 7d b0 00       	cmpq   $0x0,-0x50(%rbp)
  401c8d:	79 08                	jns    401c97 <threadwork+0x3a1>
              past = 0;
  401c8f:	48 c7 45 b0 00 00 00 00 	movq   $0x0,-0x50(%rbp)
            }
            
            // long buffer = (data->threadindex << 24) | (data->main->globalwrite % 0xf) << 16 | (data->main->writecursor % 0xf);
        
       // buffer = data->laststream << 24 | (past << 16) | data->globalread[data->laststream].thread << 8, data->globalread[data->laststream].cursor % 0xff;
    int cursor = data->globalread[data->laststream].cursor;
  401c97:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c9e:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401ca5:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cac:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401cb2:	48 63 d0             	movslq %eax,%rdx
  401cb5:	48 89 d0             	mov    %rdx,%rax
  401cb8:	48 01 c0             	add    %rax,%rax
  401cbb:	48 01 d0             	add    %rdx,%rax
  401cbe:	48 c1 e0 02          	shl    $0x2,%rax
  401cc2:	48 01 c8             	add    %rcx,%rax
  401cc5:	8b 40 04             	mov    0x4(%rax),%eax
  401cc8:	89 45 8c             	mov    %eax,-0x74(%rbp)
    //cursor = 0;
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
  401ccb:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cd2:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401cd8:	c1 e0 18             	shl    $0x18,%eax
  401cdb:	48 63 d0             	movslq %eax,%rdx
  401cde:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
  401ce2:	48 c1 e0 10          	shl    $0x10,%rax
  401ce6:	48 89 d6             	mov    %rdx,%rsi
  401ce9:	48 09 c6             	or     %rax,%rsi
  401cec:	8b 45 8c             	mov    -0x74(%rbp),%eax
  401cef:	48 63 d0             	movslq %eax,%rdx
  401cf2:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401cf9:	48 c1 ea 20          	shr    $0x20,%rdx
  401cfd:	01 c2                	add    %eax,%edx
  401cff:	c1 fa 07             	sar    $0x7,%edx
  401d02:	89 c1                	mov    %eax,%ecx
  401d04:	c1 f9 1f             	sar    $0x1f,%ecx
  401d07:	29 ca                	sub    %ecx,%edx
  401d09:	89 d1                	mov    %edx,%ecx
  401d0b:	c1 e1 08             	shl    $0x8,%ecx
  401d0e:	29 d1                	sub    %edx,%ecx
  401d10:	29 c8                	sub    %ecx,%eax
  401d12:	89 c2                	mov    %eax,%edx
  401d14:	48 63 c2             	movslq %edx,%rax
  401d17:	48 09 f0             	or     %rsi,%rax
  401d1a:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    access->cursor = data->globalread[data->laststream].cursor % 0xff;
    access->set = 1;
    data->cread = (data->cread + 1) % data->accesssize;
  }
    
    int thistream = data->laststream; 
  401d1e:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d25:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401d2b:	89 45 90             	mov    %eax,-0x70(%rbp)
                // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
                //&data->threads[data->threadindex];

        // printf("%d\n", data->main->works[buffer]);
    
        if (data->main->works[buffer] != -1) {
  401d2e:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d35:	48 8b 40 28          	mov    0x28(%rax),%rax
  401d39:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401d3d:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401d41:	48 01 d0             	add    %rdx,%rax
  401d44:	0f b6 00             	movzbl (%rax),%eax
  401d47:	3c ff                	cmp    $0xff,%al
  401d49:	74 39                	je     401d84 <threadwork+0x48e>
          data->successreads++;
  401d4b:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d52:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  401d59:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401d5d:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d64:	48 89 90 98 03 00 00 	mov    %rdx,0x398(%rax)
          
          data->main->works[buffer] = -1;
  401d6b:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d72:	48 8b 40 28          	mov    0x28(%rax),%rax
  401d76:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401d7a:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401d7e:	48 01 d0             	add    %rdx,%rax
  401d81:	c6 00 ff             	movb   $0xff,(%rax)
  
    
    
      
    
    if (data->globalread[thistream].cursor < cursorlimit) {
  401d84:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d8b:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401d92:	8b 45 90             	mov    -0x70(%rbp),%eax
  401d95:	48 63 d0             	movslq %eax,%rdx
  401d98:	48 89 d0             	mov    %rdx,%rax
  401d9b:	48 01 c0             	add    %rax,%rax
  401d9e:	48 01 d0             	add    %rdx,%rax
  401da1:	48 c1 e0 02          	shl    $0x2,%rax
  401da5:	48 01 c8             	add    %rcx,%rax
  401da8:	8b 40 04             	mov    0x4(%rax),%eax
  401dab:	39 45 a4             	cmp    %eax,-0x5c(%rbp)
  401dae:	7e 7c                	jle    401e2c <threadwork+0x536>
    
      data->globalread[thistream].global++;
  401db0:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401db7:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401dbe:	8b 45 90             	mov    -0x70(%rbp),%eax
  401dc1:	48 63 d0             	movslq %eax,%rdx
  401dc4:	48 89 d0             	mov    %rdx,%rax
  401dc7:	48 01 c0             	add    %rax,%rax
  401dca:	48 01 d0             	add    %rdx,%rax
  401dcd:	48 c1 e0 02          	shl    $0x2,%rax
  401dd1:	48 01 c8             	add    %rcx,%rax
  401dd4:	8b 10                	mov    (%rax),%edx
  401dd6:	83 c2 01             	add    $0x1,%edx
  401dd9:	89 10                	mov    %edx,(%rax)
        
        
      data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1);
  401ddb:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401de2:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401de9:	8b 45 90             	mov    -0x70(%rbp),%eax
  401dec:	48 63 d0             	movslq %eax,%rdx
  401def:	48 89 d0             	mov    %rdx,%rax
  401df2:	48 01 c0             	add    %rax,%rax
  401df5:	48 01 d0             	add    %rdx,%rax
  401df8:	48 c1 e0 02          	shl    $0x2,%rax
  401dfc:	48 01 c8             	add    %rcx,%rax
  401dff:	8b 48 04             	mov    0x4(%rax),%ecx
  401e02:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e09:	48 8b b0 48 03 00 00 	mov    0x348(%rax),%rsi
  401e10:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e13:	48 63 d0             	movslq %eax,%rdx
  401e16:	48 89 d0             	mov    %rdx,%rax
  401e19:	48 01 c0             	add    %rax,%rax
  401e1c:	48 01 d0             	add    %rdx,%rax
  401e1f:	48 c1 e0 02          	shl    $0x2,%rax
  401e23:	48 01 f0             	add    %rsi,%rax
  401e26:	8d 51 01             	lea    0x1(%rcx),%edx
  401e29:	89 50 04             	mov    %edx,0x4(%rax)
      
      }
    
    if (data->globalread[thistream].cursor == cursorlimit) {
  401e2c:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e33:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401e3a:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e3d:	48 63 d0             	movslq %eax,%rdx
  401e40:	48 89 d0             	mov    %rdx,%rax
  401e43:	48 01 c0             	add    %rax,%rax
  401e46:	48 01 d0             	add    %rdx,%rax
  401e49:	48 c1 e0 02          	shl    $0x2,%rax
  401e4d:	48 01 c8             	add    %rcx,%rax
  401e50:	8b 40 04             	mov    0x4(%rax),%eax
  401e53:	39 45 a4             	cmp    %eax,-0x5c(%rbp)
  401e56:	75 48                	jne    401ea0 <threadwork+0x5aa>
      
      data->laststream = (data->laststream + 1);
  401e58:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e5f:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401e65:	8d 50 01             	lea    0x1(%rax),%edx
  401e68:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e6f:	89 90 90 03 00 00    	mov    %edx,0x390(%rax)
     // data->globalread[thistream].global++;
data->globalread[thistream].cursor = 0;
  401e75:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e7c:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401e83:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e86:	48 63 d0             	movslq %eax,%rdx
  401e89:	48 89 d0             	mov    %rdx,%rax
  401e8c:	48 01 c0             	add    %rax,%rax
  401e8f:	48 01 d0             	add    %rdx,%rax
  401e92:	48 c1 e0 02          	shl    $0x2,%rax
  401e96:	48 01 c8             	add    %rcx,%rax
  401e99:	c7 40 04 00 00 00 00 	movl   $0x0,0x4(%rax)
    }
    
    if (data->laststream == data->mystream) {
  401ea0:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ea7:	8b 90 90 03 00 00    	mov    0x390(%rax),%edx
  401ead:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401eb4:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401eba:	39 c2                	cmp    %eax,%edx
  401ebc:	75 1d                	jne    401edb <threadwork+0x5e5>
      data->laststream = data->laststream + 1;
  401ebe:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ec5:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401ecb:	8d 50 01             	lea    0x1(%rax),%edx
  401ece:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ed5:	89 90 90 03 00 00    	mov    %edx,0x390(%rax)
     // data->globalread[data->laststream].cursor = 0;
    }
    if (data->laststream == 5) {
  401edb:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ee2:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401ee8:	83 f8 05             	cmp    $0x5,%eax
  401eeb:	75 11                	jne    401efe <threadwork+0x608>
       data->laststream = 1;
  401eed:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ef4:	c7 80 90 03 00 00 01 00 00 00 	movl   $0x1,0x390(%rax)
    for (int x = 0; x < data->threadsize - 1; x++) {
  401efe:	83 45 94 01          	addl   $0x1,-0x6c(%rbp)
  401f02:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401f09:	8b 40 68             	mov    0x68(%rax),%eax
  401f0c:	83 e8 01             	sub    $0x1,%eax
  401f0f:	39 45 94             	cmp    %eax,-0x6c(%rbp)
  401f12:	0f 8c 13 fd ff ff    	jl     401c2b <threadwork+0x335>
      
     //asm volatile ("sfence" ::: "memory");
  
      
       
}
  401f18:	90                   	nop
  401f19:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  401f1d:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401f26:	74 05                	je     401f2d <threadwork+0x637>
  401f28:	e8 43 f1 ff ff       	call   401070 <__stack_chk_fail@plt>
  401f2d:	c9                   	leave
  401f2e:	c3                   	ret

0000000000401f2f <work2>:

void * work2(void * arg) {
  401f2f:	55                   	push   %rbp
  401f30:	48 89 e5             	mov    %rsp,%rbp
  401f33:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  struct Data *data = (struct Data*) arg;
  401f37:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401f3b:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  while (data->running == 1) {
  401f3f:	eb 14                	jmp    401f55 <work2+0x26>
    asm volatile ("" ::: "memory");
      data->freq++;
  401f41:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f45:	48 8b 40 48          	mov    0x48(%rax),%rax
  401f49:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401f4d:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f51:	48 89 50 48          	mov    %rdx,0x48(%rax)
  while (data->running == 1) {
  401f55:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f59:	8b 40 5c             	mov    0x5c(%rax),%eax
  401f5c:	83 f8 01             	cmp    $0x1,%eax
  401f5f:	74 e0                	je     401f41 <work2+0x12>
  }
  
}
  401f61:	90                   	nop
  401f62:	5d                   	pop    %rbp
  401f63:	c3                   	ret

0000000000401f64 <work>:

void * work(void * arg) {
  401f64:	55                   	push   %rbp
  401f65:	48 89 e5             	mov    %rsp,%rbp
  401f68:	48 83 ec 50          	sub    $0x50,%rsp
  401f6c:	48 89 7d b8          	mov    %rdi,-0x48(%rbp)

  
  int writers;
  int readers;
  struct Data *data = (struct Data*) arg;
  401f70:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401f74:	48 89 45 e0          	mov    %rax,-0x20(%rbp)
  printf("started thread %d\n", data->threadindex);
  401f78:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401f7c:	8b 40 64             	mov    0x64(%rax),%eax
  401f7f:	89 c6                	mov    %eax,%esi
  401f81:	48 8d 05 94 20 00 00 	lea    0x2094(%rip),%rax        # 40401c <_IO_stdin_used+0x1c>
  401f88:	48 89 c7             	mov    %rax,%rdi
  401f8b:	b8 00 00 00 00       	mov    $0x0,%eax
  401f90:	e8 eb f0 ff ff       	call   401080 <printf@plt>
  
  
  int found = 0;
  401f95:	c7 45 c8 00 00 00 00 	movl   $0x0,-0x38(%rbp)
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  401f9c:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fa0:	8b 40 64             	mov    0x64(%rax),%eax
  401fa3:	8d 50 01             	lea    0x1(%rax),%edx
  401fa6:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401faa:	8b 48 68             	mov    0x68(%rax),%ecx
  401fad:	89 d0                	mov    %edx,%eax
  401faf:	99                   	cltd
  401fb0:	f7 f9                	idiv   %ecx
  401fb2:	89 55 cc             	mov    %edx,-0x34(%rbp)
  int innerfind = 0;
  401fb5:	c7 45 d0 00 00 00 00 	movl   $0x0,-0x30(%rbp)
  
  
  
  
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  401fbc:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fc0:	48 8b 80 b8 00 00 00 	mov    0xb8(%rax),%rax
  401fc7:	48 83 c0 01          	add    $0x1,%rax
  401fcb:	be 08 00 00 00       	mov    $0x8,%esi
  401fd0:	48 89 c7             	mov    %rax,%rdi
  401fd3:	e8 f8 f0 ff ff       	call   4010d0 <calloc@plt>
  401fd8:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  401fdc:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fe0:	8b 40 68             	mov    0x68(%rax),%eax
  401fe3:	48 98                	cltq
  401fe5:	be 04 00 00 00       	mov    $0x4,%esi
  401fea:	48 89 c7             	mov    %rax,%rdi
  401fed:	e8 de f0 ff ff       	call   4010d0 <calloc@plt>
  401ff2:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
  int * readywriters = calloc(data->threadsize, sizeof(int));
  401ff6:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401ffa:	8b 40 68             	mov    0x68(%rax),%eax
  401ffd:	48 98                	cltq
  401fff:	be 04 00 00 00       	mov    $0x4,%esi
  402004:	48 89 c7             	mov    %rax,%rdi
  402007:	e8 c4 f0 ff ff       	call   4010d0 <calloc@plt>
  40200c:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  
  
  int stop = 0;
  402010:	c7 45 d4 00 00 00 00 	movl   $0x0,-0x2c(%rbp)
  while (data->running > 0)  {
  402017:	eb 25                	jmp    40203e <work+0xda>
    writers = 0;
  402019:	c7 45 d8 00 00 00 00 	movl   $0x0,-0x28(%rbp)
    readers = 0;
  402020:	c7 45 dc 00 00 00 00 	movl   $0x0,-0x24(%rbp)
    stop = 0;
  402027:	c7 45 d4 00 00 00 00 	movl   $0x0,-0x2c(%rbp)
    asm volatile ("":"=m" (data->running)::);
  40202e:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
   // printf("write cycle\n");
    //memset(available, -1, data->threadsize);

      threadwork(data);
  402032:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402036:	48 89 c7             	mov    %rax,%rdi
  402039:	e8 b8 f8 ff ff       	call   4018f6 <threadwork>
  while (data->running > 0)  {
  40203e:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402042:	8b 40 5c             	mov    0x5c(%rax),%eax
  402045:	85 c0                	test   %eax,%eax
  402047:	7f d0                	jg     402019 <work+0xb5>
        for (int x = 0 ; x < data->worksize; x++) {
          data->main->works[x].available = 1;
        }
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
  402049:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  40204d:	8b 40 64             	mov    0x64(%rax),%eax
  402050:	89 c6                	mov    %eax,%esi
  402052:	48 8d 05 d6 1f 00 00 	lea    0x1fd6(%rip),%rax        # 40402f <_IO_stdin_used+0x2f>
  402059:	48 89 c7             	mov    %rax,%rdi
  40205c:	b8 00 00 00 00       	mov    $0x0,%eax
  402061:	e8 1a f0 ff ff       	call   401080 <printf@plt>
}
  402066:	90                   	nop
  402067:	c9                   	leave
  402068:	c3                   	ret

0000000000402069 <main>:

int main(int argc, char **argv) {
  402069:	55                   	push   %rbp
  40206a:	48 89 e5             	mov    %rsp,%rbp
  40206d:	53                   	push   %rbx
  40206e:	48 81 ec 78 01 00 00 	sub    $0x178,%rsp
  402075:	89 bd 8c fe ff ff    	mov    %edi,-0x174(%rbp)
  40207b:	48 89 b5 80 fe ff ff 	mov    %rsi,-0x180(%rbp)
  402082:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40208b:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  40208f:	31 c0                	xor    %eax,%eax
  int debug = 0;
  402091:	c7 85 a0 fe ff ff 00 00 00 00 	movl   $0x0,-0x160(%rbp)
  int seconds = DURATION;
  40209b:	c7 85 a4 fe ff ff 01 00 00 00 	movl   $0x1,-0x15c(%rbp)
  int worksize_each = 1;
  4020a5:	c7 85 94 fe ff ff 01 00 00 00 	movl   $0x1,-0x16c(%rbp)
  int threadsize = THREADS;
  4020af:	c7 85 98 fe ff ff 0f 00 00 00 	movl   $0xf,-0x168(%rbp)
  
  int workers = threadsize - 1;
  4020b9:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4020bf:	83 e8 01             	sub    $0x1,%eax
  4020c2:	89 85 9c fe ff ff    	mov    %eax,-0x164(%rbp)
  printf("read mask %d\n", READ_MASK);
  4020c8:	be 08 00 00 00       	mov    $0x8,%esi
  4020cd:	48 8d 05 6b 1f 00 00 	lea    0x1f6b(%rip),%rax        # 40403f <_IO_stdin_used+0x3f>
  4020d4:	48 89 c7             	mov    %rax,%rdi
  4020d7:	b8 00 00 00 00       	mov    $0x0,%eax
  4020dc:	e8 9f ef ff ff       	call   401080 <printf@plt>
  printf("write mask %d\n", WRITE_MASK);
  4020e1:	be 04 00 00 00       	mov    $0x4,%esi
  4020e6:	48 8d 05 60 1f 00 00 	lea    0x1f60(%rip),%rax        # 40404d <_IO_stdin_used+0x4d>
  4020ed:	48 89 c7             	mov    %rax,%rdi
  4020f0:	b8 00 00 00 00       	mov    $0x0,%eax
  4020f5:	e8 86 ef ff ff       	call   401080 <printf@plt>
  printf("prepwrite mask %d\n", PREP_WRITE_MASK);
  4020fa:	be 20 00 00 00       	mov    $0x20,%esi
  4020ff:	48 8d 05 56 1f 00 00 	lea    0x1f56(%rip),%rax        # 40405c <_IO_stdin_used+0x5c>
  402106:	48 89 c7             	mov    %rax,%rdi
  402109:	b8 00 00 00 00       	mov    $0x0,%eax
  40210e:	e8 6d ef ff ff       	call   401080 <printf@plt>
  printf("Starting %d workers\n", threadsize);
  402113:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402119:	89 c6                	mov    %eax,%esi
  40211b:	48 8d 05 4d 1f 00 00 	lea    0x1f4d(%rip),%rax        # 40406f <_IO_stdin_used+0x6f>
  402122:	48 89 c7             	mov    %rax,%rdi
  402125:	b8 00 00 00 00       	mov    $0x0,%eax
  40212a:	e8 51 ef ff ff       	call   401080 <printf@plt>
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  40212f:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402135:	48 98                	cltq
  402137:	be 08 00 00 00       	mov    $0x8,%esi
  40213c:	48 89 c7             	mov    %rax,%rdi
  40213f:	e8 8c ef ff ff       	call   4010d0 <calloc@plt>
  402144:	48 89 85 18 ff ff ff 	mov    %rax,-0xe8(%rbp)
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  40214b:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402151:	48 98                	cltq
  402153:	be 38 00 00 00       	mov    $0x38,%esi
  402158:	48 89 c7             	mov    %rax,%rdi
  40215b:	e8 70 ef ff ff       	call   4010d0 <calloc@plt>
  402160:	48 89 85 f0 fe ff ff 	mov    %rax,-0x110(%rbp)
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  402167:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40216d:	48 98                	cltq
  40216f:	48 c1 e0 0a          	shl    $0xa,%rax
  402173:	48 89 c6             	mov    %rax,%rsi
  402176:	bf 01 00 00 00       	mov    $0x1,%edi
  40217b:	e8 50 ef ff ff       	call   4010d0 <calloc@plt>
  402180:	48 89 85 f8 fe ff ff 	mov    %rax,-0x108(%rbp)
  
  long offset = 0;
  402187:	48 c7 85 00 ff ff ff 00 00 00 00 	movq   $0x0,-0x100(%rbp)
  long chunkslen = 0xffffffff;
  402192:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
  402197:	48 89 85 08 ff ff ff 	mov    %rax,-0xf8(%rbp)
  long worksize = chunkslen * worksize_each;
  40219e:	8b 85 94 fe ff ff    	mov    -0x16c(%rbp),%eax
  4021a4:	48 98                	cltq
  4021a6:	48 8b 95 08 ff ff ff 	mov    -0xf8(%rbp),%rdx
  4021ad:	48 0f af c2          	imul   %rdx,%rax
  4021b1:	48 89 85 10 ff ff ff 	mov    %rax,-0xf0(%rbp)
  int buckets = worksize / threadsize;
  4021b8:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4021be:	48 63 d8             	movslq %eax,%rbx
  4021c1:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  4021c8:	48 99                	cqto
  4021ca:	48 f7 fb             	idiv   %rbx
  4021cd:	89 85 90 fe ff ff    	mov    %eax,-0x170(%rbp)
  long chunksize = ceil((double) worksize / (double) chunkslen);
  4021d3:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4021d7:	f2 48 0f 2a 85 10 ff ff ff 	cvtsi2sdq -0xf0(%rbp),%xmm0
  4021e0:	66 0f ef c9          	pxor   %xmm1,%xmm1
  4021e4:	f2 48 0f 2a 8d 08 ff ff ff 	cvtsi2sdq -0xf8(%rbp),%xmm1
  4021ed:	f2 0f 5e c1          	divsd  %xmm1,%xmm0
  4021f1:	66 48 0f 7e c0       	movq   %xmm0,%rax
  4021f6:	66 48 0f 6e c0       	movq   %rax,%xmm0
  4021fb:	e8 20 ef ff ff       	call   401120 <ceil@plt>
  402200:	f2 48 0f 2c c0       	cvttsd2si %xmm0,%rax
  402205:	48 89 85 38 ff ff ff 	mov    %rax,-0xc8(%rbp)
  char *works = calloc(worksize, sizeof(char));
  40220c:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  402213:	be 01 00 00 00       	mov    $0x1,%esi
  402218:	48 89 c7             	mov    %rax,%rdi
  40221b:	e8 b0 ee ff ff       	call   4010d0 <calloc@plt>
  402220:	48 89 85 40 ff ff ff 	mov    %rax,-0xc0(%rbp)
  memset(works, -1, worksize);
  402227:	48 8b 95 10 ff ff ff 	mov    -0xf0(%rbp),%rdx
  40222e:	48 8b 85 40 ff ff ff 	mov    -0xc0(%rbp),%rax
  402235:	be ff ff ff ff       	mov    $0xffffffff,%esi
  40223a:	48 89 c7             	mov    %rax,%rdi
  40223d:	e8 7e ee ff ff       	call   4010c0 <memset@plt>
  printf("Buffer size %ld\n", worksize);
  402242:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  402249:	48 89 c6             	mov    %rax,%rsi
  40224c:	48 8d 05 31 1e 00 00 	lea    0x1e31(%rip),%rax        # 404084 <_IO_stdin_used+0x84>
  402253:	48 89 c7             	mov    %rax,%rdi
  402256:	b8 00 00 00 00       	mov    $0x0,%eax
  40225b:	e8 20 ee ff ff       	call   401080 <printf@plt>
  int chunkindex = 0;
  402260:	c7 85 d4 fe ff ff 00 00 00 00 	movl   $0x0,-0x12c(%rbp)
  int * readcursors = calloc(threadsize, sizeof(int));
  40226a:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402270:	48 98                	cltq
  402272:	be 04 00 00 00       	mov    $0x4,%esi
  402277:	48 89 c7             	mov    %rax,%rdi
  40227a:	e8 51 ee ff ff       	call   4010d0 <calloc@plt>
  40227f:	48 89 85 48 ff ff ff 	mov    %rax,-0xb8(%rbp)
  int * writecursors = calloc(threadsize, sizeof(int));
  402286:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40228c:	48 98                	cltq
  40228e:	be 04 00 00 00       	mov    $0x4,%esi
  402293:	48 89 c7             	mov    %rax,%rdi
  402296:	e8 35 ee ff ff       	call   4010d0 <calloc@plt>
  40229b:	48 89 85 50 ff ff ff 	mov    %rax,-0xb0(%rbp)
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));
  4022a2:	be 20 00 00 00       	mov    $0x20,%esi
  4022a7:	bf 64 00 00 00       	mov    $0x64,%edi
  4022ac:	e8 1f ee ff ff       	call   4010d0 <calloc@plt>
  4022b1:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)

printf("offset %ld\n", offset);
  4022b8:	48 8b 85 00 ff ff ff 	mov    -0x100(%rbp),%rax
  4022bf:	48 89 c6             	mov    %rax,%rsi
  4022c2:	48 8d 05 cc 1d 00 00 	lea    0x1dcc(%rip),%rax        # 404095 <_IO_stdin_used+0x95>
  4022c9:	48 89 c7             	mov    %rax,%rdi
  4022cc:	b8 00 00 00 00       	mov    $0x0,%eax
  4022d1:	e8 aa ed ff ff       	call   401080 <printf@plt>
  
printf("%ld chunks\n", chunkslen);
  4022d6:	48 8b 85 08 ff ff ff 	mov    -0xf8(%rbp),%rax
  4022dd:	48 89 c6             	mov    %rax,%rsi
  4022e0:	48 8d 05 ba 1d 00 00 	lea    0x1dba(%rip),%rax        # 4040a1 <_IO_stdin_used+0xa1>
  4022e7:	48 89 c7             	mov    %rax,%rdi
  4022ea:	b8 00 00 00 00       	mov    $0x0,%eax
  4022ef:	e8 8c ed ff ff       	call   401080 <printf@plt>
 // for (int i = 0; i < worksize; i++) {
   // works[i].taskindex = 2;
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  4022f4:	c7 85 c4 fe ff ff 00 00 00 00 	movl   $0x0,-0x13c(%rbp)
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  4022fe:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402304:	48 98                	cltq
  402306:	be 04 00 00 00       	mov    $0x4,%esi
  40230b:	48 89 c7             	mov    %rax,%rdi
  40230e:	e8 bd ed ff ff       	call   4010d0 <calloc@plt>
  402313:	48 89 85 60 ff ff ff 	mov    %rax,-0xa0(%rbp)
  
  long * globalwrite;
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  40231a:	48 8d 85 e0 fe ff ff 	lea    -0x120(%rbp),%rax
  402321:	ba 00 02 00 00       	mov    $0x200,%edx
  402326:	be 80 00 00 00       	mov    $0x80,%esi
  40232b:	48 89 c7             	mov    %rax,%rdi
  40232e:	e8 cd ed ff ff       	call   401100 <posix_memalign@plt>
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  402333:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402339:	48 98                	cltq
  40233b:	be 0c 00 00 00       	mov    $0xc,%esi
  402340:	48 89 c7             	mov    %rax,%rdi
  402343:	e8 88 ed ff ff       	call   4010d0 <calloc@plt>
  402348:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
  data[0].works = works;
  40234f:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402356:	48 8b 95 40 ff ff ff 	mov    -0xc0(%rbp),%rdx
  40235d:	48 89 50 70          	mov    %rdx,0x70(%rax)
  int accesssize = 100000000;
  402361:	c7 85 d8 fe ff ff 00 e1 f5 05 	movl   $0x5f5e100,-0x128(%rbp)
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  40236b:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  402371:	48 98                	cltq
  402373:	be 14 00 00 00       	mov    $0x14,%esi
  402378:	48 89 c7             	mov    %rax,%rdi
  40237b:	e8 50 ed ff ff       	call   4010d0 <calloc@plt>
  402380:	48 89 85 70 ff ff ff 	mov    %rax,-0x90(%rbp)
  struct Access * writes = calloc(accesssize, sizeof(struct Access));
  402387:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  40238d:	48 98                	cltq
  40238f:	be 14 00 00 00       	mov    $0x14,%esi
  402394:	48 89 c7             	mov    %rax,%rdi
  402397:	e8 34 ed ff ff       	call   4010d0 <calloc@plt>
  40239c:	48 89 85 78 ff ff ff 	mov    %rax,-0x88(%rbp)

  struct Scheduler * scheduler = calloc(1, sizeof(struct Scheduler));
  4023a3:	be 08 00 00 00       	mov    $0x8,%esi
  4023a8:	bf 01 00 00 00       	mov    $0x1,%edi
  4023ad:	e8 1e ed ff ff       	call   4010d0 <calloc@plt>
  4023b2:	48 89 45 80          	mov    %rax,-0x80(%rbp)

  
  
  for (int x = 0; x < threadsize ; x++) {
  4023b6:	c7 85 c8 fe ff ff 00 00 00 00 	movl   $0x0,-0x138(%rbp)
  4023c0:	e9 9c 06 00 00       	jmp    402a61 <main+0x9f8>
    
    struct Coroutine * cos = calloc(10, sizeof(struct Coroutine));
  4023c5:	be 20 00 00 00       	mov    $0x20,%esi
  4023ca:	bf 0a 00 00 00       	mov    $0xa,%edi
  4023cf:	e8 fc ec ff ff       	call   4010d0 <calloc@plt>
  4023d4:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
    
    data[x].coroutines = cos;
  4023d8:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4023de:	48 98                	cltq
  4023e0:	48 c1 e0 0a          	shl    $0xa,%rax
  4023e4:	48 89 c2             	mov    %rax,%rdx
  4023e7:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4023ee:	48 01 c2             	add    %rax,%rdx
  4023f1:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4023f5:	48 89 82 c0 03 00 00 	mov    %rax,0x3c0(%rdx)
    for (int y = 0; y < 10; y++ ) {
  4023fc:	c7 85 cc fe ff ff 00 00 00 00 	movl   $0x0,-0x134(%rbp)
  402406:	eb 59                	jmp    402461 <main+0x3f8>
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
  402408:	be 04 00 00 00       	mov    $0x4,%esi
  40240d:	bf 01 00 00 00       	mov    $0x1,%edi
  402412:	e8 b9 ec ff ff       	call   4010d0 <calloc@plt>
  402417:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
      cos[y].data = codata;
  40241b:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  402421:	48 98                	cltq
  402423:	48 c1 e0 05          	shl    $0x5,%rax
  402427:	48 89 c2             	mov    %rax,%rdx
  40242a:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40242e:	48 01 c2             	add    %rax,%rdx
  402431:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  402435:	48 89 42 18          	mov    %rax,0x18(%rdx)
      cos[y].eip = (uint64_t)coroutine_func;
  402439:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  40243f:	48 98                	cltq
  402441:	48 c1 e0 05          	shl    $0x5,%rax
  402445:	48 89 c2             	mov    %rax,%rdx
  402448:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40244c:	48 01 d0             	add    %rdx,%rax
  40244f:	48 c7 c2 1d 12 40 00 	mov    $0x40121d,%rdx
  402456:	48 89 50 10          	mov    %rdx,0x10(%rax)
    for (int y = 0; y < 10; y++ ) {
  40245a:	83 85 cc fe ff ff 01 	addl   $0x1,-0x134(%rbp)
  402461:	83 bd cc fe ff ff 09 	cmpl   $0x9,-0x134(%rbp)
  402468:	7e 9e                	jle    402408 <main+0x39f>
    }
    data[x].scheduler = scheduler; 
  40246a:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402470:	48 98                	cltq
  402472:	48 c1 e0 0a          	shl    $0xa,%rax
  402476:	48 89 c2             	mov    %rax,%rdx
  402479:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402480:	48 01 c2             	add    %rax,%rdx
  402483:	48 8b 45 80          	mov    -0x80(%rbp),%rax
  402487:	48 89 82 c8 03 00 00 	mov    %rax,0x3c8(%rdx)
    data[x].reads = reads;
  40248e:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402494:	48 98                	cltq
  402496:	48 c1 e0 0a          	shl    $0xa,%rax
  40249a:	48 89 c2             	mov    %rax,%rdx
  40249d:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4024a4:	48 01 c2             	add    %rax,%rdx
  4024a7:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
  4024ae:	48 89 82 a0 03 00 00 	mov    %rax,0x3a0(%rdx)
    data[x].writes = writes; 
  4024b5:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4024bb:	48 98                	cltq
  4024bd:	48 c1 e0 0a          	shl    $0xa,%rax
  4024c1:	48 89 c2             	mov    %rax,%rdx
  4024c4:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4024cb:	48 01 c2             	add    %rax,%rdx
  4024ce:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4024d5:	48 89 82 a8 03 00 00 	mov    %rax,0x3a8(%rdx)
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t)); 
  4024dc:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4024e2:	48 98                	cltq
  4024e4:	48 c1 e0 0a          	shl    $0xa,%rax
  4024e8:	48 89 c2             	mov    %rax,%rdx
  4024eb:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4024f2:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  4024f6:	be 80 00 00 00       	mov    $0x80,%esi
  4024fb:	bf 01 00 00 00       	mov    $0x1,%edi
  402500:	e8 cb eb ff ff       	call   4010d0 <calloc@plt>
  402505:	48 89 43 78          	mov    %rax,0x78(%rbx)
    CPU_SET(cpu += 1, data[x].cpu_set);
  402509:	83 85 c4 fe ff ff 01 	addl   $0x1,-0x13c(%rbp)
  402510:	8b 85 c4 fe ff ff    	mov    -0x13c(%rbp),%eax
  402516:	48 98                	cltq
  402518:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  40251c:	48 81 7d b0 ff 03 00 00 	cmpq   $0x3ff,-0x50(%rbp)
  402524:	77 78                	ja     40259e <main+0x535>
  402526:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40252c:	48 98                	cltq
  40252e:	48 c1 e0 0a          	shl    $0xa,%rax
  402532:	48 89 c2             	mov    %rax,%rdx
  402535:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40253c:	48 01 d0             	add    %rdx,%rax
  40253f:	48 8b 40 78          	mov    0x78(%rax),%rax
  402543:	48 89 c1             	mov    %rax,%rcx
  402546:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
  40254a:	48 c1 e8 06          	shr    $0x6,%rax
  40254e:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  402556:	48 01 ca             	add    %rcx,%rdx
  402559:	48 8b 32             	mov    (%rdx),%rsi
  40255c:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
  402560:	83 e2 3f             	and    $0x3f,%edx
  402563:	bf 01 00 00 00       	mov    $0x1,%edi
  402568:	89 d1                	mov    %edx,%ecx
  40256a:	48 d3 e7             	shl    %cl,%rdi
  40256d:	48 89 f9             	mov    %rdi,%rcx
  402570:	8b 95 c8 fe ff ff    	mov    -0x138(%rbp),%edx
  402576:	48 63 d2             	movslq %edx,%rdx
  402579:	48 89 d7             	mov    %rdx,%rdi
  40257c:	48 c1 e7 0a          	shl    $0xa,%rdi
  402580:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  402587:	48 01 fa             	add    %rdi,%rdx
  40258a:	48 8b 52 78          	mov    0x78(%rdx),%rdx
  40258e:	48 c1 e0 03          	shl    $0x3,%rax
  402592:	48 01 d0             	add    %rdx,%rax
  402595:	48 09 ce             	or     %rcx,%rsi
  402598:	48 89 f2             	mov    %rsi,%rdx
  40259b:	48 89 10             	mov    %rdx,(%rax)
    printf("assigning thread %d to cpu %d\n", x, cpu);
  40259e:	8b 95 c4 fe ff ff    	mov    -0x13c(%rbp),%edx
  4025a4:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4025aa:	89 c6                	mov    %eax,%esi
  4025ac:	48 8d 05 fd 1a 00 00 	lea    0x1afd(%rip),%rax        # 4040b0 <_IO_stdin_used+0xb0>
  4025b3:	48 89 c7             	mov    %rax,%rdi
  4025b6:	b8 00 00 00 00       	mov    $0x0,%eax
  4025bb:	e8 c0 ea ff ff       	call   401080 <printf@plt>
    data[x].bucketstart = x * buckets ;
  4025c0:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4025c6:	48 98                	cltq
  4025c8:	48 c1 e0 0a          	shl    $0xa,%rax
  4025cc:	48 89 c2             	mov    %rax,%rdx
  4025cf:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4025d6:	48 01 c2             	add    %rax,%rdx
  4025d9:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4025df:	0f af 85 90 fe ff ff 	imul   -0x170(%rbp),%eax
  4025e6:	89 82 98 00 00 00    	mov    %eax,0x98(%rdx)
    data[x].globalwrite = globalwrite;
  4025ec:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4025f2:	48 98                	cltq
  4025f4:	48 c1 e0 0a          	shl    $0xa,%rax
  4025f8:	48 89 c2             	mov    %rax,%rdx
  4025fb:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402602:	48 01 c2             	add    %rax,%rdx
  402605:	48 8b 85 e0 fe ff ff 	mov    -0x120(%rbp),%rax
  40260c:	48 89 82 80 03 00 00 	mov    %rax,0x380(%rdx)
    data[x].loglevel = debug;
  402613:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402619:	48 98                	cltq
  40261b:	48 c1 e0 0a          	shl    $0xa,%rax
  40261f:	48 89 c2             	mov    %rax,%rdx
  402622:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402629:	48 01 c2             	add    %rax,%rdx
  40262c:	8b 85 a0 fe ff ff    	mov    -0x160(%rbp),%eax
  402632:	89 82 80 00 00 00    	mov    %eax,0x80(%rdx)
    data[x].running = 2;
  402638:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40263e:	48 98                	cltq
  402640:	48 c1 e0 0a          	shl    $0xa,%rax
  402644:	48 89 c2             	mov    %rax,%rdx
  402647:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40264e:	48 01 d0             	add    %rdx,%rax
  402651:	c7 40 5c 02 00 00 00 	movl   $0x2,0x5c(%rax)
    data[x].threadindex = x;
  402658:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40265e:	48 98                	cltq
  402660:	48 c1 e0 0a          	shl    $0xa,%rax
  402664:	48 89 c2             	mov    %rax,%rdx
  402667:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40266e:	48 01 c2             	add    %rax,%rdx
  402671:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402677:	89 42 64             	mov    %eax,0x64(%rdx)
    data[x].worksize = worksize;
  40267a:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402680:	48 98                	cltq
  402682:	48 c1 e0 0a          	shl    $0xa,%rax
  402686:	48 89 c2             	mov    %rax,%rdx
  402689:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402690:	48 01 d0             	add    %rdx,%rax
  402693:	48 8b 95 10 ff ff ff 	mov    -0xf0(%rbp),%rdx
  40269a:	89 50 60             	mov    %edx,0x60(%rax)
    
    data[x].availables = buckets;
  40269d:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026a3:	48 98                	cltq
  4026a5:	48 c1 e0 0a          	shl    $0xa,%rax
  4026a9:	48 89 c2             	mov    %rax,%rdx
  4026ac:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026b3:	48 01 c2             	add    %rax,%rdx
  4026b6:	8b 85 90 fe ff ff    	mov    -0x170(%rbp),%eax
  4026bc:	89 82 94 00 00 00    	mov    %eax,0x94(%rdx)
    data[x].threadsize = threadsize;
  4026c2:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026c8:	48 98                	cltq
  4026ca:	48 c1 e0 0a          	shl    $0xa,%rax
  4026ce:	48 89 c2             	mov    %rax,%rdx
  4026d1:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026d8:	48 01 c2             	add    %rax,%rdx
  4026db:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4026e1:	89 42 68             	mov    %eax,0x68(%rdx)
    data[x].readies = readies;
  4026e4:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026ea:	48 98                	cltq
  4026ec:	48 c1 e0 0a          	shl    $0xa,%rax
  4026f0:	48 89 c2             	mov    %rax,%rdx
  4026f3:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026fa:	48 01 c2             	add    %rax,%rdx
  4026fd:	48 8b 85 60 ff ff ff 	mov    -0xa0(%rbp),%rax
  402704:	48 89 42 20          	mov    %rax,0x20(%rdx)
    data[x].readies[x] = 0;
  402708:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40270e:	48 98                	cltq
  402710:	48 c1 e0 0a          	shl    $0xa,%rax
  402714:	48 89 c2             	mov    %rax,%rdx
  402717:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40271e:	48 01 d0             	add    %rdx,%rax
  402721:	48 8b 50 20          	mov    0x20(%rax),%rdx
  402725:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40272b:	48 98                	cltq
  40272d:	48 c1 e0 02          	shl    $0x2,%rax
  402731:	48 01 d0             	add    %rdx,%rax
  402734:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    data[x].buckets = buckets;
  40273a:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402740:	48 98                	cltq
  402742:	48 c1 e0 0a          	shl    $0xa,%rax
  402746:	48 89 c2             	mov    %rax,%rdx
  402749:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402750:	48 01 c2             	add    %rax,%rdx
  402753:	8b 85 90 fe ff ff    	mov    -0x170(%rbp),%eax
  402759:	89 82 90 00 00 00    	mov    %eax,0x90(%rdx)
    data[x].main = &data[0];
  40275f:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402765:	48 98                	cltq
  402767:	48 c1 e0 0a          	shl    $0xa,%rax
  40276b:	48 89 c2             	mov    %rax,%rdx
  40276e:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402775:	48 01 c2             	add    %rax,%rdx
  402778:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40277f:	48 89 42 28          	mov    %rax,0x28(%rdx)
    data[x].threads = data;
  402783:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402789:	48 98                	cltq
  40278b:	48 c1 e0 0a          	shl    $0xa,%rax
  40278f:	48 89 c2             	mov    %rax,%rdx
  402792:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402799:	48 01 c2             	add    %rax,%rdx
  40279c:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027a3:	48 89 42 30          	mov    %rax,0x30(%rdx)
    
    data[x].read = 0;
  4027a7:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027ad:	48 98                	cltq
  4027af:	48 c1 e0 0a          	shl    $0xa,%rax
  4027b3:	48 89 c2             	mov    %rax,%rdx
  4027b6:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027bd:	48 01 d0             	add    %rdx,%rax
  4027c0:	48 c7 00 00 00 00 00 	movq   $0x0,(%rax)
    data[x].write = worksize;
  4027c7:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027cd:	48 98                	cltq
  4027cf:	48 c1 e0 0a          	shl    $0xa,%rax
  4027d3:	48 89 c2             	mov    %rax,%rdx
  4027d6:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027dd:	48 01 c2             	add    %rax,%rdx
  4027e0:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  4027e7:	48 89 42 08          	mov    %rax,0x8(%rdx)
    data[x].readcursor = threadsize - 1;
  4027eb:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027f1:	48 98                	cltq
  4027f3:	48 c1 e0 0a          	shl    $0xa,%rax
  4027f7:	48 89 c2             	mov    %rax,%rdx
  4027fa:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402801:	48 01 d0             	add    %rdx,%rax
  402804:	8b 95 98 fe ff ff    	mov    -0x168(%rbp),%edx
  40280a:	83 ea 01             	sub    $0x1,%edx
  40280d:	89 90 00 02 00 00    	mov    %edx,0x200(%rax)
    data[x].writecursor = 0;
  402813:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402819:	48 98                	cltq
  40281b:	48 c1 e0 0a          	shl    $0xa,%rax
  40281f:	48 89 c2             	mov    %rax,%rdx
  402822:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402829:	48 01 d0             	add    %rdx,%rax
  40282c:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    data[x].freelist = freelist;
  402836:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40283c:	48 98                	cltq
  40283e:	48 c1 e0 0a          	shl    $0xa,%rax
  402842:	48 89 c2             	mov    %rax,%rdx
  402845:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40284c:	48 01 c2             	add    %rax,%rdx
  40284f:	48 8b 85 58 ff ff ff 	mov    -0xa8(%rbp),%rax
  402856:	48 89 82 a0 00 00 00 	mov    %rax,0xa0(%rdx)
    data[x].chunksize = chunksize;
  40285d:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402863:	48 98                	cltq
  402865:	48 c1 e0 0a          	shl    $0xa,%rax
  402869:	48 89 c2             	mov    %rax,%rdx
  40286c:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402873:	48 01 c2             	add    %rax,%rdx
  402876:	48 8b 85 38 ff ff ff 	mov    -0xc8(%rbp),%rax
  40287d:	48 89 82 c0 00 00 00 	mov    %rax,0xc0(%rdx)
    data[x].chunkslen = chunkslen;
  402884:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40288a:	48 98                	cltq
  40288c:	48 c1 e0 0a          	shl    $0xa,%rax
  402890:	48 89 c2             	mov    %rax,%rdx
  402893:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40289a:	48 01 c2             	add    %rax,%rdx
  40289d:	48 8b 85 08 ff ff ff 	mov    -0xf8(%rbp),%rax
  4028a4:	48 89 82 b8 00 00 00 	mov    %rax,0xb8(%rdx)
    data[x].newmask = 0;
  4028ab:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028b1:	48 98                	cltq
  4028b3:	48 c1 e0 0a          	shl    $0xa,%rax
  4028b7:	48 89 c2             	mov    %rax,%rdx
  4028ba:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4028c1:	48 01 d0             	add    %rdx,%rax
  4028c4:	c7 80 c8 00 00 00 00 00 00 00 	movl   $0x0,0xc8(%rax)
    data[x].prevread = threadsize;
  4028ce:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028d4:	48 98                	cltq
  4028d6:	48 c1 e0 0a          	shl    $0xa,%rax
  4028da:	48 89 c2             	mov    %rax,%rdx
  4028dd:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4028e4:	48 01 c2             	add    %rax,%rdx
  4028e7:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4028ed:	48 98                	cltq
  4028ef:	48 89 82 08 03 00 00 	mov    %rax,0x308(%rdx)
    data[x].prevwrite = threadsize;
  4028f6:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028fc:	48 98                	cltq
  4028fe:	48 c1 e0 0a          	shl    $0xa,%rax
  402902:	48 89 c2             	mov    %rax,%rdx
  402905:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40290c:	48 01 c2             	add    %rax,%rdx
  40290f:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402915:	48 98                	cltq
  402917:	48 89 82 10 03 00 00 	mov    %rax,0x310(%rdx)
    data[x].mystream = 1 + (x / 4);
  40291e:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402924:	8d 50 03             	lea    0x3(%rax),%edx
  402927:	85 c0                	test   %eax,%eax
  402929:	0f 48 c2             	cmovs  %edx,%eax
  40292c:	c1 f8 02             	sar    $0x2,%eax
  40292f:	89 c2                	mov    %eax,%edx
  402931:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402937:	48 98                	cltq
  402939:	48 c1 e0 0a          	shl    $0xa,%rax
  40293d:	48 89 c1             	mov    %rax,%rcx
  402940:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402947:	48 01 c8             	add    %rcx,%rax
  40294a:	83 c2 01             	add    $0x1,%edx
  40294d:	89 90 8c 03 00 00    	mov    %edx,0x38c(%rax)
    data[x].thiswrite = threadsize;
  402953:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402959:	48 98                	cltq
  40295b:	48 c1 e0 0a          	shl    $0xa,%rax
  40295f:	48 89 c2             	mov    %rax,%rdx
  402962:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402969:	48 01 c2             	add    %rax,%rdx
  40296c:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402972:	89 82 28 03 00 00    	mov    %eax,0x328(%rdx)
    int epochs = 10000000;
  402978:	c7 85 dc fe ff ff 80 96 98 00 	movl   $0x989680,-0x124(%rbp)
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
  402982:	8b 85 dc fe ff ff    	mov    -0x124(%rbp),%eax
  402988:	48 98                	cltq
  40298a:	8b 95 c8 fe ff ff    	mov    -0x138(%rbp),%edx
  402990:	48 63 d2             	movslq %edx,%rdx
  402993:	48 89 d1             	mov    %rdx,%rcx
  402996:	48 c1 e1 0a          	shl    $0xa,%rcx
  40299a:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4029a1:	48 8d 1c 11          	lea    (%rcx,%rdx,1),%rbx
  4029a5:	be 30 00 00 00       	mov    $0x30,%esi
  4029aa:	48 89 c7             	mov    %rax,%rdi
  4029ad:	e8 1e e7 ff ff       	call   4010d0 <calloc@plt>
  4029b2:	48 89 83 18 03 00 00 	mov    %rax,0x318(%rbx)
    data[x].epochssize = epochs;
  4029b9:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4029bf:	48 98                	cltq
  4029c1:	48 c1 e0 0a          	shl    $0xa,%rax
  4029c5:	48 89 c2             	mov    %rax,%rdx
  4029c8:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4029cf:	48 01 c2             	add    %rax,%rdx
  4029d2:	8b 85 dc fe ff ff    	mov    -0x124(%rbp),%eax
  4029d8:	89 82 20 03 00 00    	mov    %eax,0x320(%rdx)
    data[x].globalread = globalread;
  4029de:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4029e4:	48 98                	cltq
  4029e6:	48 c1 e0 0a          	shl    $0xa,%rax
  4029ea:	48 89 c2             	mov    %rax,%rdx
  4029ed:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4029f4:	48 01 c2             	add    %rax,%rdx
  4029f7:	48 8b 85 68 ff ff ff 	mov    -0x98(%rbp),%rax
  4029fe:	48 89 82 48 03 00 00 	mov    %rax,0x348(%rdx)
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
  402a05:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a0b:	48 98                	cltq
  402a0d:	48 c1 e0 0a          	shl    $0xa,%rax
  402a11:	48 89 c2             	mov    %rax,%rdx
  402a14:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a1b:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  402a1f:	be 30 00 00 00       	mov    $0x30,%esi
  402a24:	bf 10 27 00 00       	mov    $0x2710,%edi
  402a29:	e8 a2 e6 ff ff       	call   4010d0 <calloc@plt>
  402a2e:	48 89 83 30 03 00 00 	mov    %rax,0x330(%rbx)
    data[x].accesssize = accesssize;
  402a35:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a3b:	48 98                	cltq
  402a3d:	48 c1 e0 0a          	shl    $0xa,%rax
  402a41:	48 89 c2             	mov    %rax,%rdx
  402a44:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a4b:	48 01 c2             	add    %rax,%rdx
  402a4e:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  402a54:	89 82 b8 03 00 00    	mov    %eax,0x3b8(%rdx)
  for (int x = 0; x < threadsize ; x++) {
  402a5a:	83 85 c8 fe ff ff 01 	addl   $0x1,-0x138(%rbp)
  402a61:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a67:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402a6d:	0f 8c 52 f9 ff ff    	jl     4023c5 <main+0x35c>
  } 
  
  for (int x = 0; x < threadsize ; x++) {
  402a73:	c7 85 d0 fe ff ff 00 00 00 00 	movl   $0x0,-0x130(%rbp)
  402a7d:	e9 b8 00 00 00       	jmp    402b3a <main+0xad1>
    pthread_create(&thread[x], &attr[x], work, &data[x]);
  402a82:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402a88:	48 98                	cltq
  402a8a:	48 c1 e0 0a          	shl    $0xa,%rax
  402a8e:	48 89 c2             	mov    %rax,%rdx
  402a91:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a98:	48 01 c2             	add    %rax,%rdx
  402a9b:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402aa1:	48 63 c8             	movslq %eax,%rcx
  402aa4:	48 89 c8             	mov    %rcx,%rax
  402aa7:	48 c1 e0 03          	shl    $0x3,%rax
  402aab:	48 29 c8             	sub    %rcx,%rax
  402aae:	48 c1 e0 03          	shl    $0x3,%rax
  402ab2:	48 89 c1             	mov    %rax,%rcx
  402ab5:	48 8b 85 f0 fe ff ff 	mov    -0x110(%rbp),%rax
  402abc:	48 8d 34 01          	lea    (%rcx,%rax,1),%rsi
  402ac0:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402ac6:	48 98                	cltq
  402ac8:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
  402ad0:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402ad7:	48 01 c8             	add    %rcx,%rax
  402ada:	48 89 d1             	mov    %rdx,%rcx
  402add:	48 c7 c2 64 1f 40 00 	mov    $0x401f64,%rdx
  402ae4:	48 89 c7             	mov    %rax,%rdi
  402ae7:	e8 f4 e5 ff ff       	call   4010e0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  402aec:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402af2:	48 98                	cltq
  402af4:	48 c1 e0 0a          	shl    $0xa,%rax
  402af8:	48 89 c2             	mov    %rax,%rdx
  402afb:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402b02:	48 01 d0             	add    %rdx,%rax
  402b05:	48 8b 50 78          	mov    0x78(%rax),%rdx
  402b09:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b0f:	48 98                	cltq
  402b11:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
  402b19:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402b20:	48 01 c8             	add    %rcx,%rax
  402b23:	48 8b 00             	mov    (%rax),%rax
  402b26:	be 08 00 00 00       	mov    $0x8,%esi
  402b2b:	48 89 c7             	mov    %rax,%rdi
  402b2e:	e8 fd e4 ff ff       	call   401030 <pthread_setaffinity_np@plt>
  for (int x = 0; x < threadsize ; x++) {
  402b33:	83 85 d0 fe ff ff 01 	addl   $0x1,-0x130(%rbp)
  402b3a:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b40:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402b46:	0f 8c 36 ff ff ff    	jl     402a82 <main+0xa19>
  }
  
  struct timespec time = {
  402b4c:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402b52:	48 98                	cltq
  402b54:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
  402b58:	48 c7 45 c8 00 00 00 00 	movq   $0x0,-0x38(%rbp)
    seconds,
    0
  };
  struct timespec rem = {
  402b60:	48 c7 45 d0 00 00 00 00 	movq   $0x0,-0x30(%rbp)
  402b68:	48 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%rbp)
    0,
    0
  };
  
  nanosleep(&time, &rem);
  402b70:	48 8d 55 d0          	lea    -0x30(%rbp),%rdx
  402b74:	48 8d 45 c0          	lea    -0x40(%rbp),%rax
  402b78:	48 89 d6             	mov    %rdx,%rsi
  402b7b:	48 89 c7             	mov    %rax,%rdi
  402b7e:	e8 1d e5 ff ff       	call   4010a0 <nanosleep@plt>
  
  printf("runphased\n");
  402b83:	48 8d 05 45 15 00 00 	lea    0x1545(%rip),%rax        # 4040cf <_IO_stdin_used+0xcf>
  402b8a:	48 89 c7             	mov    %rax,%rdi
  402b8d:	e8 ae e4 ff ff       	call   401040 <puts@plt>
  for (int x = 0; x < threadsize ; x++) {
  402b92:	c7 85 b8 fe ff ff 00 00 00 00 	movl   $0x0,-0x148(%rbp)
  402b9c:	eb 29                	jmp    402bc7 <main+0xb5e>
    data[x].running--;
  402b9e:	8b 85 b8 fe ff ff    	mov    -0x148(%rbp),%eax
  402ba4:	48 98                	cltq
  402ba6:	48 c1 e0 0a          	shl    $0xa,%rax
  402baa:	48 89 c2             	mov    %rax,%rdx
  402bad:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402bb4:	48 01 d0             	add    %rdx,%rax
  402bb7:	8b 50 5c             	mov    0x5c(%rax),%edx
  402bba:	83 ea 01             	sub    $0x1,%edx
  402bbd:	89 50 5c             	mov    %edx,0x5c(%rax)
  for (int x = 0; x < threadsize ; x++) {
  402bc0:	83 85 b8 fe ff ff 01 	addl   $0x1,-0x148(%rbp)
  402bc7:	8b 85 b8 fe ff ff    	mov    -0x148(%rbp),%eax
  402bcd:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402bd3:	7c c9                	jl     402b9e <main+0xb35>
    
  }
  
 printf("draining\n");
  402bd5:	48 8d 05 fd 14 00 00 	lea    0x14fd(%rip),%rax        # 4040d9 <_IO_stdin_used+0xd9>
  402bdc:	48 89 c7             	mov    %rax,%rdi
  402bdf:	e8 5c e4 ff ff       	call   401040 <puts@plt>
 // time.tv_sec = 3;
//nanosleep(&time, &rem);
  for (int x = 0; x < threadsize ; x++) {
  402be4:	c7 85 bc fe ff ff 00 00 00 00 	movl   $0x0,-0x144(%rbp)
  402bee:	eb 29                	jmp    402c19 <main+0xbb0>
    data[x].running--;
  402bf0:	8b 85 bc fe ff ff    	mov    -0x144(%rbp),%eax
  402bf6:	48 98                	cltq
  402bf8:	48 c1 e0 0a          	shl    $0xa,%rax
  402bfc:	48 89 c2             	mov    %rax,%rdx
  402bff:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402c06:	48 01 d0             	add    %rdx,%rax
  402c09:	8b 50 5c             	mov    0x5c(%rax),%edx
  402c0c:	83 ea 01             	sub    $0x1,%edx
  402c0f:	89 50 5c             	mov    %edx,0x5c(%rax)
  for (int x = 0; x < threadsize ; x++) {
  402c12:	83 85 bc fe ff ff 01 	addl   $0x1,-0x144(%rbp)
  402c19:	8b 85 bc fe ff ff    	mov    -0x144(%rbp),%eax
  402c1f:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402c25:	7c c9                	jl     402bf0 <main+0xb87>
  }
  
  //nanosleep(&time, &rem);
  for (int x = 0; x < threadsize; x++) {
  402c27:	c7 85 c0 fe ff ff 00 00 00 00 	movl   $0x0,-0x140(%rbp)
  402c31:	eb 36                	jmp    402c69 <main+0xc00>
    void *res;
    pthread_join(thread[x], &res);
  402c33:	8b 85 c0 fe ff ff    	mov    -0x140(%rbp),%eax
  402c39:	48 98                	cltq
  402c3b:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  402c43:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402c4a:	48 01 d0             	add    %rdx,%rax
  402c4d:	48 8b 00             	mov    (%rax),%rax
  402c50:	48 8d 95 e8 fe ff ff 	lea    -0x118(%rbp),%rdx
  402c57:	48 89 d6             	mov    %rdx,%rsi
  402c5a:	48 89 c7             	mov    %rax,%rdi
  402c5d:	e8 ae e4 ff ff       	call   401110 <pthread_join@plt>
  for (int x = 0; x < threadsize; x++) {
  402c62:	83 85 c0 fe ff ff 01 	addl   $0x1,-0x140(%rbp)
  402c69:	8b 85 c0 fe ff ff    	mov    -0x140(%rbp),%eax
  402c6f:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402c75:	7c bc                	jl     402c33 <main+0xbca>
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  402c77:	48 8d 05 64 14 00 00 	lea    0x1464(%rip),%rax        # 4040e2 <_IO_stdin_used+0xe2>
  402c7e:	48 89 c7             	mov    %rax,%rdi
  402c81:	e8 ba e3 ff ff       	call   401040 <puts@plt>
  long freq = 0;
  402c86:	48 c7 85 20 ff ff ff 00 00 00 00 	movq   $0x0,-0xe0(%rbp)
  long sends = 1;
  402c91:	48 c7 45 88 01 00 00 00 	movq   $0x1,-0x78(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402c99:	c7 85 a8 fe ff ff 00 00 00 00 	movl   $0x0,-0x158(%rbp)
  402ca3:	eb 5f                	jmp    402d04 <main+0xc9b>
    printf("%ld reads\n", data[x].freq);
  402ca5:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402cab:	48 98                	cltq
  402cad:	48 c1 e0 0a          	shl    $0xa,%rax
  402cb1:	48 89 c2             	mov    %rax,%rdx
  402cb4:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402cbb:	48 01 d0             	add    %rdx,%rax
  402cbe:	48 8b 40 48          	mov    0x48(%rax),%rax
  402cc2:	48 89 c6             	mov    %rax,%rsi
  402cc5:	48 8d 05 2b 14 00 00 	lea    0x142b(%rip),%rax        # 4040f7 <_IO_stdin_used+0xf7>
  402ccc:	48 89 c7             	mov    %rax,%rdi
  402ccf:	b8 00 00 00 00       	mov    $0x0,%eax
  402cd4:	e8 a7 e3 ff ff       	call   401080 <printf@plt>
    freq += data[x].freq;
  402cd9:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402cdf:	48 98                	cltq
  402ce1:	48 c1 e0 0a          	shl    $0xa,%rax
  402ce5:	48 89 c2             	mov    %rax,%rdx
  402ce8:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402cef:	48 01 d0             	add    %rdx,%rax
  402cf2:	48 8b 40 48          	mov    0x48(%rax),%rax
  402cf6:	48 01 85 20 ff ff ff 	add    %rax,-0xe0(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402cfd:	83 85 a8 fe ff ff 01 	addl   $0x1,-0x158(%rbp)
  402d04:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d0a:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402d10:	7c 93                	jl     402ca5 <main+0xc3c>
  }
  printf("freq: %ld\n", freq/ seconds);
  402d12:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402d18:	48 63 d8             	movslq %eax,%rbx
  402d1b:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402d22:	48 99                	cqto
  402d24:	48 f7 fb             	idiv   %rbx
  402d27:	48 89 c6             	mov    %rax,%rsi
  402d2a:	48 8d 05 d1 13 00 00 	lea    0x13d1(%rip),%rax        # 404102 <_IO_stdin_used+0x102>
  402d31:	48 89 c7             	mov    %rax,%rdi
  402d34:	b8 00 00 00 00       	mov    $0x0,%eax
  402d39:	e8 42 e3 ff ff       	call   401080 <printf@plt>
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  402d3e:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402d45:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  402d4a:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402d50:	48 63 da             	movslq %edx,%rbx
  402d53:	48 99                	cqto
  402d55:	48 f7 fb             	idiv   %rbx
  402d58:	48 89 c6             	mov    %rax,%rsi
  402d5b:	48 8d 05 ab 13 00 00 	lea    0x13ab(%rip),%rax        # 40410d <_IO_stdin_used+0x10d>
  402d62:	48 89 c7             	mov    %rax,%rdi
  402d65:	b8 00 00 00 00       	mov    $0x0,%eax
  402d6a:	e8 11 e3 ff ff       	call   401080 <printf@plt>
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  402d6f:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402d75:	48 63 d8             	movslq %eax,%rbx
  402d78:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402d7f:	48 99                	cqto
  402d81:	48 f7 fb             	idiv   %rbx
  402d84:	48 89 c3             	mov    %rax,%rbx
  402d87:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402d8c:	48 99                	cqto
  402d8e:	48 f7 fb             	idiv   %rbx
  402d91:	48 89 c6             	mov    %rax,%rsi
  402d94:	48 8d 05 80 13 00 00 	lea    0x1380(%rip),%rax        # 40411b <_IO_stdin_used+0x11b>
  402d9b:	48 89 c7             	mov    %rax,%rdi
  402d9e:	b8 00 00 00 00       	mov    $0x0,%eax
  402da3:	e8 d8 e2 ff ff       	call   401080 <printf@plt>
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  402da8:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402dae:	48 63 d8             	movslq %eax,%rbx
  402db1:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402db8:	48 99                	cqto
  402dba:	48 f7 fb             	idiv   %rbx
  402dbd:	48 89 c3             	mov    %rax,%rbx
  402dc0:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402dc5:	48 99                	cqto
  402dc7:	48 f7 fb             	idiv   %rbx
  402dca:	48 99                	cqto
  402dcc:	48 f7 7d 88          	idivq  -0x78(%rbp)
  402dd0:	48 89 c6             	mov    %rax,%rsi
  402dd3:	48 8d 05 55 13 00 00 	lea    0x1355(%rip),%rax        # 40412f <_IO_stdin_used+0x12f>
  402dda:	48 89 c7             	mov    %rax,%rdi
  402ddd:	b8 00 00 00 00       	mov    $0x0,%eax
  402de2:	e8 99 e2 ff ff       	call   401080 <printf@plt>
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  402de7:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402dee:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  402df3:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402df9:	48 63 da             	movslq %edx,%rbx
  402dfc:	48 99                	cqto
  402dfe:	48 f7 fb             	idiv   %rbx
  402e01:	48 89 c3             	mov    %rax,%rbx
  402e04:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402e09:	48 99                	cqto
  402e0b:	48 f7 fb             	idiv   %rbx
  402e0e:	48 89 c6             	mov    %rax,%rsi
  402e11:	48 8d 05 35 13 00 00 	lea    0x1335(%rip),%rax        # 40414d <_IO_stdin_used+0x14d>
  402e18:	48 89 c7             	mov    %rax,%rdi
  402e1b:	b8 00 00 00 00       	mov    $0x0,%eax
  402e20:	e8 5b e2 ff ff       	call   401080 <printf@plt>
  
  long goods = 0;
  402e25:	48 c7 85 28 ff ff ff 00 00 00 00 	movq   $0x0,-0xd8(%rbp)

  for (int x = 0; x < threadsize; x++) {
  402e30:	c7 85 ac fe ff ff 00 00 00 00 	movl   $0x0,-0x154(%rbp)
  402e3a:	eb 65                	jmp    402ea1 <main+0xe38>
    printf("%ld successreads\n", data[x].successreads);
  402e3c:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402e42:	48 98                	cltq
  402e44:	48 c1 e0 0a          	shl    $0xa,%rax
  402e48:	48 89 c2             	mov    %rax,%rdx
  402e4b:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402e52:	48 01 d0             	add    %rdx,%rax
  402e55:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  402e5c:	48 89 c6             	mov    %rax,%rsi
  402e5f:	48 8d 05 fa 12 00 00 	lea    0x12fa(%rip),%rax        # 404160 <_IO_stdin_used+0x160>
  402e66:	48 89 c7             	mov    %rax,%rdi
  402e69:	b8 00 00 00 00       	mov    $0x0,%eax
  402e6e:	e8 0d e2 ff ff       	call   401080 <printf@plt>
    goods += data[x].successreads;
  402e73:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402e79:	48 98                	cltq
  402e7b:	48 c1 e0 0a          	shl    $0xa,%rax
  402e7f:	48 89 c2             	mov    %rax,%rdx
  402e82:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402e89:	48 01 d0             	add    %rdx,%rax
  402e8c:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  402e93:	48 01 85 28 ff ff ff 	add    %rax,-0xd8(%rbp)
  for (int x = 0; x < threadsize; x++) {
  402e9a:	83 85 ac fe ff ff 01 	addl   $0x1,-0x154(%rbp)
  402ea1:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402ea7:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402ead:	7c 8d                	jl     402e3c <main+0xdd3>
  }
  
  long freq_writes = 0;
  402eaf:	48 c7 85 30 ff ff ff 00 00 00 00 	movq   $0x0,-0xd0(%rbp)
  
  for (int x = 0; x < threadsize; x++) {
  402eba:	c7 85 b0 fe ff ff 00 00 00 00 	movl   $0x0,-0x150(%rbp)
  402ec4:	eb 5f                	jmp    402f25 <main+0xebc>
    freq_writes += data[x].freq_writes;
  402ec6:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402ecc:	48 98                	cltq
  402ece:	48 c1 e0 0a          	shl    $0xa,%rax
  402ed2:	48 89 c2             	mov    %rax,%rdx
  402ed5:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402edc:	48 01 d0             	add    %rdx,%rax
  402edf:	48 8b 40 50          	mov    0x50(%rax),%rax
  402ee3:	48 01 85 30 ff ff ff 	add    %rax,-0xd0(%rbp)
    printf("%ld writes\n", data[x].freq_writes);
  402eea:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402ef0:	48 98                	cltq
  402ef2:	48 c1 e0 0a          	shl    $0xa,%rax
  402ef6:	48 89 c2             	mov    %rax,%rdx
  402ef9:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402f00:	48 01 d0             	add    %rdx,%rax
  402f03:	48 8b 40 50          	mov    0x50(%rax),%rax
  402f07:	48 89 c6             	mov    %rax,%rsi
  402f0a:	48 8d 05 61 12 00 00 	lea    0x1261(%rip),%rax        # 404172 <_IO_stdin_used+0x172>
  402f11:	48 89 c7             	mov    %rax,%rdi
  402f14:	b8 00 00 00 00       	mov    $0x0,%eax
  402f19:	e8 62 e1 ff ff       	call   401080 <printf@plt>
  for (int x = 0; x < threadsize; x++) {
  402f1e:	83 85 b0 fe ff ff 01 	addl   $0x1,-0x150(%rbp)
  402f25:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f2b:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402f31:	7c 93                	jl     402ec6 <main+0xe5d>
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);
  402f33:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402f39:	48 63 d8             	movslq %eax,%rbx
  402f3c:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402f43:	48 99                	cqto
  402f45:	48 f7 fb             	idiv   %rbx
  402f48:	48 89 c6             	mov    %rax,%rsi
  402f4b:	48 8d 05 2c 12 00 00 	lea    0x122c(%rip),%rax        # 40417e <_IO_stdin_used+0x17e>
  402f52:	48 89 c7             	mov    %rax,%rdi
  402f55:	b8 00 00 00 00       	mov    $0x0,%eax
  402f5a:	e8 21 e1 ff ff       	call   401080 <printf@plt>

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  402f5f:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402f66:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  402f6b:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402f71:	48 63 da             	movslq %edx,%rbx
  402f74:	48 99                	cqto
  402f76:	48 f7 fb             	idiv   %rbx
  402f79:	48 89 c6             	mov    %rax,%rsi
  402f7c:	48 8d 05 0d 12 00 00 	lea    0x120d(%rip),%rax        # 404190 <_IO_stdin_used+0x190>
  402f83:	48 89 c7             	mov    %rax,%rdi
  402f86:	b8 00 00 00 00       	mov    $0x0,%eax
  402f8b:	e8 f0 e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  402f90:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402f96:	48 63 d8             	movslq %eax,%rbx
  402f99:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402fa0:	48 99                	cqto
  402fa2:	48 f7 fb             	idiv   %rbx
  402fa5:	48 89 c3             	mov    %rax,%rbx
  402fa8:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402fad:	48 99                	cqto
  402faf:	48 f7 fb             	idiv   %rbx
  402fb2:	48 89 c6             	mov    %rax,%rsi
  402fb5:	48 8d 05 ec 11 00 00 	lea    0x11ec(%rip),%rax        # 4041a8 <_IO_stdin_used+0x1a8>
  402fbc:	48 89 c7             	mov    %rax,%rdi
  402fbf:	b8 00 00 00 00       	mov    $0x0,%eax
  402fc4:	e8 b7 e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes per thread latency: %ld\n", (1000000000/(freq_writes / seconds)) / sends);
  402fc9:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402fcf:	48 63 d8             	movslq %eax,%rbx
  402fd2:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402fd9:	48 99                	cqto
  402fdb:	48 f7 fb             	idiv   %rbx
  402fde:	48 89 c3             	mov    %rax,%rbx
  402fe1:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402fe6:	48 99                	cqto
  402fe8:	48 f7 fb             	idiv   %rbx
  402feb:	48 99                	cqto
  402fed:	48 f7 7d 88          	idivq  -0x78(%rbp)
  402ff1:	48 89 c6             	mov    %rax,%rsi
  402ff4:	48 8d 05 cd 11 00 00 	lea    0x11cd(%rip),%rax        # 4041c8 <_IO_stdin_used+0x1c8>
  402ffb:	48 89 c7             	mov    %rax,%rdi
  402ffe:	b8 00 00 00 00       	mov    $0x0,%eax
  403003:	e8 78 e0 ff ff       	call   401080 <printf@plt>
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * sends) / seconds));
  403008:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  40300f:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  403014:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  40301a:	48 63 da             	movslq %edx,%rbx
  40301d:	48 99                	cqto
  40301f:	48 f7 fb             	idiv   %rbx
  403022:	48 89 c3             	mov    %rax,%rbx
  403025:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40302a:	48 99                	cqto
  40302c:	48 f7 fb             	idiv   %rbx
  40302f:	48 89 c6             	mov    %rax,%rsi
  403032:	48 8d 05 b4 11 00 00 	lea    0x11b4(%rip),%rax        # 4041ed <_IO_stdin_used+0x1ed>
  403039:	48 89 c7             	mov    %rax,%rdi
  40303c:	b8 00 00 00 00       	mov    $0x0,%eax
  403041:	e8 3a e0 ff ff       	call   401080 <printf@plt>
    printf("%ldns\n", read.tv_nsec - created.tv_nsec);
    printf("%ldns\n", written.tv_nsec - read.tv_nsec);
    
  }
  */
  printf("writer speed\n");
  403046:	48 8d 05 ba 11 00 00 	lea    0x11ba(%rip),%rax        # 404207 <_IO_stdin_used+0x207>
  40304d:	48 89 c7             	mov    %rax,%rdi
  403050:	e8 eb df ff ff       	call   401040 <puts@plt>
  for (int x = 0; x < 1 ;  x++){
  403055:	c7 85 b4 fe ff ff 00 00 00 00 	movl   $0x0,-0x14c(%rbp)
  40305f:	e9 84 02 00 00       	jmp    4032e8 <main+0x127f>
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
  403064:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  40306a:	48 98                	cltq
  40306c:	48 c1 e0 0a          	shl    $0xa,%rax
  403070:	48 89 c2             	mov    %rax,%rdx
  403073:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40307a:	48 01 d0             	add    %rdx,%rax
  40307d:	48 8b 80 f0 00 00 00 	mov    0xf0(%rax),%rax
  403084:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  40308a:	48 63 d2             	movslq %edx,%rdx
  40308d:	48 89 d1             	mov    %rdx,%rcx
  403090:	48 c1 e1 0a          	shl    $0xa,%rcx
  403094:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  40309b:	48 01 ca             	add    %rcx,%rdx
  40309e:	48 8b 92 e0 00 00 00 	mov    0xe0(%rdx),%rdx
  4030a5:	48 29 d0             	sub    %rdx,%rax
  4030a8:	48 89 c6             	mov    %rax,%rsi
  4030ab:	48 8d 05 65 0f 00 00 	lea    0xf65(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  4030b2:	48 89 c7             	mov    %rax,%rdi
  4030b5:	b8 00 00 00 00       	mov    $0x0,%eax
  4030ba:	e8 c1 df ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
  4030bf:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4030c5:	48 98                	cltq
  4030c7:	48 c1 e0 0a          	shl    $0xa,%rax
  4030cb:	48 89 c2             	mov    %rax,%rdx
  4030ce:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4030d5:	48 01 d0             	add    %rdx,%rax
  4030d8:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
  4030df:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4030e5:	48 63 d2             	movslq %edx,%rdx
  4030e8:	48 89 d1             	mov    %rdx,%rcx
  4030eb:	48 c1 e1 0a          	shl    $0xa,%rcx
  4030ef:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4030f6:	48 01 ca             	add    %rcx,%rdx
  4030f9:	48 8b 92 e0 00 00 00 	mov    0xe0(%rdx),%rdx
  403100:	48 29 d0             	sub    %rdx,%rax
  403103:	48 89 c6             	mov    %rax,%rsi
  403106:	48 8d 05 0a 0f 00 00 	lea    0xf0a(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  40310d:	48 89 c7             	mov    %rax,%rdi
  403110:	b8 00 00 00 00       	mov    $0x0,%eax
  403115:	e8 66 df ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
  40311a:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403120:	48 98                	cltq
  403122:	48 c1 e0 0a          	shl    $0xa,%rax
  403126:	48 89 c2             	mov    %rax,%rdx
  403129:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403130:	48 01 d0             	add    %rdx,%rax
  403133:	48 8b 80 f0 00 00 00 	mov    0xf0(%rax),%rax
  40313a:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  403140:	48 63 d2             	movslq %edx,%rdx
  403143:	48 89 d1             	mov    %rdx,%rcx
  403146:	48 c1 e1 0a          	shl    $0xa,%rcx
  40314a:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403151:	48 01 ca             	add    %rcx,%rdx
  403154:	48 8b 92 00 01 00 00 	mov    0x100(%rdx),%rdx
  40315b:	48 29 d0             	sub    %rdx,%rax
  40315e:	48 89 c6             	mov    %rax,%rsi
  403161:	48 8d 05 af 0e 00 00 	lea    0xeaf(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  403168:	48 89 c7             	mov    %rax,%rdi
  40316b:	b8 00 00 00 00       	mov    $0x0,%eax
  403170:	e8 0b df ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
  403175:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  40317b:	48 98                	cltq
  40317d:	48 c1 e0 0a          	shl    $0xa,%rax
  403181:	48 89 c2             	mov    %rax,%rdx
  403184:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40318b:	48 01 d0             	add    %rdx,%rax
  40318e:	48 8b 80 20 01 00 00 	mov    0x120(%rax),%rax
  403195:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  40319b:	48 63 d2             	movslq %edx,%rdx
  40319e:	48 89 d1             	mov    %rdx,%rcx
  4031a1:	48 c1 e1 0a          	shl    $0xa,%rcx
  4031a5:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4031ac:	48 01 ca             	add    %rcx,%rdx
  4031af:	48 8b 92 10 01 00 00 	mov    0x110(%rdx),%rdx
  4031b6:	48 29 d0             	sub    %rdx,%rax
  4031b9:	48 89 c6             	mov    %rax,%rsi
  4031bc:	48 8d 05 54 0e 00 00 	lea    0xe54(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  4031c3:	48 89 c7             	mov    %rax,%rdi
  4031c6:	b8 00 00 00 00       	mov    $0x0,%eax
  4031cb:	e8 b0 de ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
  4031d0:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4031d6:	48 98                	cltq
  4031d8:	48 c1 e0 0a          	shl    $0xa,%rax
  4031dc:	48 89 c2             	mov    %rax,%rdx
  4031df:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4031e6:	48 01 d0             	add    %rdx,%rax
  4031e9:	48 8b 80 10 01 00 00 	mov    0x110(%rax),%rax
  4031f0:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4031f6:	48 63 d2             	movslq %edx,%rdx
  4031f9:	48 89 d1             	mov    %rdx,%rcx
  4031fc:	48 c1 e1 0a          	shl    $0xa,%rcx
  403200:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403207:	48 01 ca             	add    %rcx,%rdx
  40320a:	48 8b 92 20 01 00 00 	mov    0x120(%rdx),%rdx
  403211:	48 29 d0             	sub    %rdx,%rax
  403214:	48 89 c6             	mov    %rax,%rsi
  403217:	48 8d 05 f9 0d 00 00 	lea    0xdf9(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  40321e:	48 89 c7             	mov    %rax,%rdi
  403221:	b8 00 00 00 00       	mov    $0x0,%eax
  403226:	e8 55 de ff ff       	call   401080 <printf@plt>
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
  40322b:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403231:	48 98                	cltq
  403233:	48 c1 e0 0a          	shl    $0xa,%rax
  403237:	48 89 c2             	mov    %rax,%rdx
  40323a:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403241:	48 01 d0             	add    %rdx,%rax
  403244:	48 8b 80 10 01 00 00 	mov    0x110(%rax),%rax
  40324b:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  403251:	48 63 d2             	movslq %edx,%rdx
  403254:	48 89 d1             	mov    %rdx,%rcx
  403257:	48 c1 e1 0a          	shl    $0xa,%rcx
  40325b:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403262:	48 01 ca             	add    %rcx,%rdx
  403265:	48 8b 92 00 01 00 00 	mov    0x100(%rdx),%rdx
  40326c:	48 29 d0             	sub    %rdx,%rax
  40326f:	48 89 c6             	mov    %rax,%rsi
  403272:	48 8d 05 9e 0d 00 00 	lea    0xd9e(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  403279:	48 89 c7             	mov    %rax,%rdi
  40327c:	b8 00 00 00 00       	mov    $0x0,%eax
  403281:	e8 fa dd ff ff       	call   401080 <printf@plt>
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  403286:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  40328c:	48 98                	cltq
  40328e:	48 c1 e0 0a          	shl    $0xa,%rax
  403292:	48 89 c2             	mov    %rax,%rdx
  403295:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40329c:	48 01 d0             	add    %rdx,%rax
  40329f:	48 8b 80 40 01 00 00 	mov    0x140(%rax),%rax
  4032a6:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4032ac:	48 63 d2             	movslq %edx,%rdx
  4032af:	48 89 d1             	mov    %rdx,%rcx
  4032b2:	48 c1 e1 0a          	shl    $0xa,%rcx
  4032b6:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4032bd:	48 01 ca             	add    %rcx,%rdx
  4032c0:	48 8b 92 30 01 00 00 	mov    0x130(%rdx),%rdx
  4032c7:	48 29 d0             	sub    %rdx,%rax
  4032ca:	48 89 c6             	mov    %rax,%rsi
  4032cd:	48 8d 05 40 0f 00 00 	lea    0xf40(%rip),%rax        # 404214 <_IO_stdin_used+0x214>
  4032d4:	48 89 c7             	mov    %rax,%rdi
  4032d7:	b8 00 00 00 00       	mov    $0x0,%eax
  4032dc:	e8 9f dd ff ff       	call   401080 <printf@plt>
  for (int x = 0; x < 1 ;  x++){
  4032e1:	83 85 b4 fe ff ff 01 	addl   $0x1,-0x14c(%rbp)
  4032e8:	83 bd b4 fe ff ff 00 	cmpl   $0x0,-0x14c(%rbp)
  4032ef:	0f 8e 6f fd ff ff    	jle    403064 <main+0xffb>
  } 
  printf("%ld good reads per second\n", goods / seconds);
  4032f5:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  4032fb:	48 63 d8             	movslq %eax,%rbx
  4032fe:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
  403305:	48 99                	cqto
  403307:	48 f7 fb             	idiv   %rbx
  40330a:	48 89 c6             	mov    %rax,%rsi
  40330d:	48 8d 05 08 0f 00 00 	lea    0xf08(%rip),%rax        # 40421c <_IO_stdin_used+0x21c>
  403314:	48 89 c7             	mov    %rax,%rdi
  403317:	b8 00 00 00 00       	mov    $0x0,%eax
  40331c:	e8 5f dd ff ff       	call   401080 <printf@plt>
  printf("%ld good reads per second latency\n", 1000000000 / (goods / seconds));
  403321:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  403327:	48 63 d8             	movslq %eax,%rbx
  40332a:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
  403331:	48 99                	cqto
  403333:	48 f7 fb             	idiv   %rbx
  403336:	48 89 c3             	mov    %rax,%rbx
  403339:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40333e:	48 99                	cqto
  403340:	48 f7 fb             	idiv   %rbx
  403343:	48 89 c6             	mov    %rax,%rsi
  403346:	48 8d 05 eb 0e 00 00 	lea    0xeeb(%rip),%rax        # 404238 <_IO_stdin_used+0x238>
  40334d:	48 89 c7             	mov    %rax,%rdi
  403350:	b8 00 00 00 00       	mov    $0x0,%eax
  403355:	e8 26 dd ff ff       	call   401080 <printf@plt>
     }
   fclose(out_file);
   
 }

  char * filename = calloc(100, sizeof(char));
  40335a:	be 01 00 00 00       	mov    $0x1,%esi
  40335f:	bf 64 00 00 00       	mov    $0x64,%edi
  403364:	e8 67 dd ff ff       	call   4010d0 <calloc@plt>
  403369:	48 89 45 90          	mov    %rax,-0x70(%rbp)
  char * buf = calloc(1000, sizeof(char));
  40336d:	be 01 00 00 00       	mov    $0x1,%esi
  403372:	bf e8 03 00 00       	mov    $0x3e8,%edi
  403377:	e8 54 dd ff ff       	call   4010d0 <calloc@plt>
  40337c:	48 89 45 98          	mov    %rax,-0x68(%rbp)
  memset(filename, 0, 100);
  403380:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403384:	ba 64 00 00 00       	mov    $0x64,%edx
  403389:	be 00 00 00 00       	mov    $0x0,%esi
  40338e:	48 89 c7             	mov    %rax,%rdi
  403391:	e8 2a dd ff ff       	call   4010c0 <memset@plt>
  snprintf(filename, 100, "coroutine.struct");
  403396:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  40339a:	48 8d 15 ba 0e 00 00 	lea    0xeba(%rip),%rdx        # 40425b <_IO_stdin_used+0x25b>
  4033a1:	be 64 00 00 00       	mov    $0x64,%esi
  4033a6:	48 89 c7             	mov    %rax,%rdi
  4033a9:	b8 00 00 00 00       	mov    $0x0,%eax
  4033ae:	e8 dd dc ff ff       	call   401090 <snprintf@plt>
  FILE *out_file = fopen(filename, "w");
  4033b3:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4033b7:	48 8d 15 ae 0e 00 00 	lea    0xeae(%rip),%rdx        # 40426c <_IO_stdin_used+0x26c>
  4033be:	48 89 d6             	mov    %rdx,%rsi
  4033c1:	48 89 c7             	mov    %rax,%rdi
  4033c4:	e8 27 dd ff ff       	call   4010f0 <fopen@plt>
  4033c9:	48 89 45 a0          	mov    %rax,-0x60(%rbp)

memset(buf, 0, 1000);
  4033cd:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4033d1:	ba e8 03 00 00       	mov    $0x3e8,%edx
  4033d6:	be 00 00 00 00       	mov    $0x0,%esi
  4033db:	48 89 c7             	mov    %rax,%rdi
  4033de:	e8 dd dc ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "index %ld\n", offsetof(struct Coroutine, index));
  4033e3:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4033e7:	b9 00 00 00 00       	mov    $0x0,%ecx
  4033ec:	48 8d 15 7b 0e 00 00 	lea    0xe7b(%rip),%rdx        # 40426e <_IO_stdin_used+0x26e>
  4033f3:	be 64 00 00 00       	mov    $0x64,%esi
  4033f8:	48 89 c7             	mov    %rax,%rdi
  4033fb:	b8 00 00 00 00       	mov    $0x0,%eax
  403400:	e8 8b dc ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  403405:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  403409:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40340d:	48 89 d6             	mov    %rdx,%rsi
  403410:	48 89 c7             	mov    %rax,%rdi
  403413:	e8 98 dc ff ff       	call   4010b0 <fputs@plt>
  
  memset(buf, 0, 1000);
  403418:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40341c:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403421:	be 00 00 00 00       	mov    $0x0,%esi
  403426:	48 89 c7             	mov    %rax,%rdi
  403429:	e8 92 dc ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "rsp %ld\n", offsetof(struct Coroutine, rsp));
  40342e:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403432:	b9 08 00 00 00       	mov    $0x8,%ecx
  403437:	48 8d 15 3b 0e 00 00 	lea    0xe3b(%rip),%rdx        # 404279 <_IO_stdin_used+0x279>
  40343e:	be 64 00 00 00       	mov    $0x64,%esi
  403443:	48 89 c7             	mov    %rax,%rdi
  403446:	b8 00 00 00 00       	mov    $0x0,%eax
  40344b:	e8 40 dc ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  403450:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  403454:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403458:	48 89 d6             	mov    %rdx,%rsi
  40345b:	48 89 c7             	mov    %rax,%rdi
  40345e:	e8 4d dc ff ff       	call   4010b0 <fputs@plt>
  
  memset(buf, 0, 1000);
  403463:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403467:	ba e8 03 00 00       	mov    $0x3e8,%edx
  40346c:	be 00 00 00 00       	mov    $0x0,%esi
  403471:	48 89 c7             	mov    %rax,%rdi
  403474:	e8 47 dc ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "eip %ld\n", offsetof(struct Coroutine, eip));
  403479:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40347d:	b9 10 00 00 00       	mov    $0x10,%ecx
  403482:	48 8d 15 f9 0d 00 00 	lea    0xdf9(%rip),%rdx        # 404282 <_IO_stdin_used+0x282>
  403489:	be 64 00 00 00       	mov    $0x64,%esi
  40348e:	48 89 c7             	mov    %rax,%rdi
  403491:	b8 00 00 00 00       	mov    $0x0,%eax
  403496:	e8 f5 db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf );
  40349b:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  40349f:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034a3:	48 89 d6             	mov    %rdx,%rsi
  4034a6:	48 89 c7             	mov    %rax,%rdi
  4034a9:	e8 02 dc ff ff       	call   4010b0 <fputs@plt>


  memset(buf, 0, 1000);
  4034ae:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034b2:	ba e8 03 00 00       	mov    $0x3e8,%edx
  4034b7:	be 00 00 00 00       	mov    $0x0,%esi
  4034bc:	48 89 c7             	mov    %rax,%rdi
  4034bf:	e8 fc db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "data %ld\n", offsetof(struct Coroutine, data));
  4034c4:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034c8:	b9 18 00 00 00       	mov    $0x18,%ecx
  4034cd:	48 8d 15 b7 0d 00 00 	lea    0xdb7(%rip),%rdx        # 40428b <_IO_stdin_used+0x28b>
  4034d4:	be 64 00 00 00       	mov    $0x64,%esi
  4034d9:	48 89 c7             	mov    %rax,%rdi
  4034dc:	b8 00 00 00 00       	mov    $0x0,%eax
  4034e1:	e8 aa db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  4034e6:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  4034ea:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034ee:	48 89 d6             	mov    %rdx,%rsi
  4034f1:	48 89 c7             	mov    %rax,%rdi
  4034f4:	e8 b7 db ff ff       	call   4010b0 <fputs@plt>

  memset(buf, 0, 1000);
  4034f9:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034fd:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403502:	be 00 00 00 00       	mov    $0x0,%esi
  403507:	48 89 c7             	mov    %rax,%rdi
  40350a:	e8 b1 db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "corourinedata.running %ld\n", offsetof(struct CoroutineData, running));
  40350f:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403513:	b9 00 00 00 00       	mov    $0x0,%ecx
  403518:	48 8d 15 76 0d 00 00 	lea    0xd76(%rip),%rdx        # 404295 <_IO_stdin_used+0x295>
  40351f:	be 64 00 00 00       	mov    $0x64,%esi
  403524:	48 89 c7             	mov    %rax,%rdi
  403527:	b8 00 00 00 00       	mov    $0x0,%eax
  40352c:	e8 5f db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  403531:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  403535:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403539:	48 89 d6             	mov    %rdx,%rsi
  40353c:	48 89 c7             	mov    %rax,%rdi
  40353f:	e8 6c db ff ff       	call   4010b0 <fputs@plt>

  memset(buf, 0, 1000);
  403544:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403548:	ba e8 03 00 00       	mov    $0x3e8,%edx
  40354d:	be 00 00 00 00       	mov    $0x0,%esi
  403552:	48 89 c7             	mov    %rax,%rdi
  403555:	e8 66 db ff ff       	call   4010c0 <memset@plt>
  snprintf(buf, 100, "size coroutine %ld\n", sizeof(struct Coroutine));
  40355a:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40355e:	b9 20 00 00 00       	mov    $0x20,%ecx
  403563:	48 8d 15 46 0d 00 00 	lea    0xd46(%rip),%rdx        # 4042b0 <_IO_stdin_used+0x2b0>
  40356a:	be 64 00 00 00       	mov    $0x64,%esi
  40356f:	48 89 c7             	mov    %rax,%rdi
  403572:	b8 00 00 00 00       	mov    $0x0,%eax
  403577:	e8 14 db ff ff       	call   401090 <snprintf@plt>
  fprintf(out_file, "%s", buf);
  40357c:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  403580:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403584:	48 89 d6             	mov    %rdx,%rsi
  403587:	48 89 c7             	mov    %rax,%rdi
  40358a:	e8 21 db ff ff       	call   4010b0 <fputs@plt>
  
  fclose(out_file);
  40358f:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  403593:	48 89 c7             	mov    %rax,%rdi
  403596:	e8 c5 da ff ff       	call   401060 <fclose@plt>
  40359b:	b8 00 00 00 00       	mov    $0x0,%eax
  4035a0:	48 8b 55 e8          	mov    -0x18(%rbp),%rdx
  4035a4:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  4035ad:	74 05                	je     4035b4 <main+0x154b>
  4035af:	e8 bc da ff ff       	call   401070 <__stack_chk_fail@plt>
  4035b4:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
  4035b8:	c9                   	leave
  4035b9:	c3                   	ret
  4035ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000004035c0 <.MSG>:
  4035c0:	43                   	rex.XB
  4035c1:	4f 20 43 6f          	rex.WRXB and %r8b,0x6f(%r11)
  4035c5:	72 6f                	jb     403636 <switch_to+0x1b>
  4035c7:	75 74                	jne    40363d <switch_to+0x22>
  4035c9:	69 6e 65 53 74 72 75 	imul   $0x75727453,0x65(%rsi),%ebp
  4035d0:	63 74 20 25          	movsxd 0x25(%rax,%riz,1),%esi
  4035d4:	78 0a                	js     4035e0 <.EIP+0x9>
	...

00000000004035d7 <.EIP>:
  4035d7:	43                   	rex.XB
  4035d8:	4f 20 45 49          	rex.WRXB and %r8b,0x49(%r13)
  4035dc:	50                   	push   %rax
  4035dd:	2e                   	cs
  4035de:	2e                   	cs
  4035df:	2e                   	cs
  4035e0:	20                   	.byte 0x20
  4035e1:	25                   	.byte 0x25
  4035e2:	78 0a                	js     4035ee <.CODATA+0x9>
	...

00000000004035e5 <.CODATA>:
  4035e5:	43                   	rex.XB
  4035e6:	4f 20 63 6f          	rex.WRXB and %r12b,0x6f(%r11)
  4035ea:	64 61                	fs (bad)
  4035ec:	74 61                	je     40364f <switch_to+0x34>
  4035ee:	2e                   	cs
  4035ef:	2e                   	cs
  4035f0:	2e                   	cs
  4035f1:	20                   	.byte 0x20
  4035f2:	25                   	.byte 0x25
  4035f3:	78 0a                	js     4035ff <.INDEX+0x9>
	...

00000000004035f6 <.INDEX>:
  4035f6:	43 6f                	rex.XB outsl %ds:(%rsi),(%dx)
  4035f8:	72 6f                	jb     403669 <switch_to+0x4e>
  4035fa:	75 74                	jne    403670 <switch_to+0x55>
  4035fc:	69 6e 65 20 69 6e 64 	imul   $0x646e6920,0x65(%rsi),%ebp
  403603:	65 78 2e             	gs js  403634 <switch_to+0x19>
  403606:	2e                   	cs
  403607:	2e                   	cs
  403608:	20                   	.byte 0x20
  403609:	25                   	.byte 0x25
  40360a:	64 0a 00             	or     %fs:(%rax),%al

000000000040360d <.RET>:
  40360d:	52                   	push   %rdx
  40360e:	65 74 75             	gs je  403686 <switch_to+0x6b>
  403611:	72 6e                	jb     403681 <switch_to+0x66>
  403613:	2e                   	cs
  403614:	2e                   	cs
  403615:	2e                   	cs
  403616:	20                   	.byte 0x20
  403617:	25                   	.byte 0x25
  403618:	64 0a 00             	or     %fs:(%rax),%al

000000000040361b <switch_to>:
	.text
	# switch_to(struct Coroutine * coroutines, int index, struct Scheduler * scheduler)
	# rdi, %rsi, %rdx, %rcx, %r8 and %r9
switch_to:
# popq %r11
pushq %rbp
  40361b:	55                   	push   %rbp

movq %rsp, %rbp
  40361c:	48 89 e5             	mov    %rsp,%rbp
subq $1024, %rsp
  40361f:	48 81 ec 00 04 00 00 	sub    $0x400,%rsp



movq %rdi, -56(%rbp) # coroutine table
  403626:	48 89 7d c8          	mov    %rdi,-0x38(%rbp)
movq %rsi, -8(%rbp) # index
  40362a:	48 89 75 f8          	mov    %rsi,-0x8(%rbp)
movq %rdx, -16(%rbp) # scheduler
  40362e:	48 89 55 f0          	mov    %rdx,-0x10(%rbp)

movq %rsi, %rax
  403632:	48 89 f0             	mov    %rsi,%rax
imul $32, %rax
  403635:	48 6b c0 20          	imul   $0x20,%rax,%rax
addq %rdi, %rax
  403639:	48 01 f8             	add    %rdi,%rax
mov %rax, %r11
  40363c:	49 89 c3             	mov    %rax,%r11

mov %r11, %rax
  40363f:	4c 89 d8             	mov    %r11,%rax
movq %rax, %r9
  403642:	49 89 c1             	mov    %rax,%r9
movq %r9, -24(%rbp) # coroutine object
  403645:	4c 89 4d e8          	mov    %r9,-0x18(%rbp)

movq %r11, %rax
  403649:	4c 89 d8             	mov    %r11,%rax
leaq 8(%rax), %rax
  40364c:	48 8d 40 08          	lea    0x8(%rax),%rax
movq %rax, %r9
  403650:	49 89 c1             	mov    %rax,%r9
movq %r9, -48(%rbp) # rsp
  403653:	4c 89 4d d0          	mov    %r9,-0x30(%rbp)

movq %r11, %rax
  403657:	4c 89 d8             	mov    %r11,%rax
leaq 16(%rax), %rax
  40365a:	48 8d 40 10          	lea    0x10(%rax),%rax
movq (%rax), %r9
  40365e:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -32(%rbp) # coroutine function
  403661:	4c 89 4d e0          	mov    %r9,-0x20(%rbp)

movq %r11, %rax
  403665:	4c 89 d8             	mov    %r11,%rax
leaq 24(%rax), %rax # load from coroutine object data object
  403668:	48 8d 40 18          	lea    0x18(%rax),%rax
movq (%rax), %r9
  40366c:	4c 8b 08             	mov    (%rax),%r9
movq %r9, -40(%rbp) # coroutine data object
  40366f:	4c 89 4d d8          	mov    %r9,-0x28(%rbp)
movq (%rax), %rcx
  403673:	48 8b 08             	mov    (%rax),%rcx

movq -24(%rbp), %r11
  403676:	4c 8b 5d e8          	mov    -0x18(%rbp),%r11
#

leaq .INDEX(%rip), %rdi
  40367a:	48 8d 3d 75 ff ff ff 	lea    -0x8b(%rip),%rdi        # 4035f6 <.INDEX>
#call printf@plt
mov $0, %eax
  403681:	b8 00 00 00 00       	mov    $0x0,%eax

#pushq %r11
leaq .MSG(%rip), %rdi
  403686:	48 8d 3d 33 ff ff ff 	lea    -0xcd(%rip),%rdi        # 4035c0 <.MSG>
movq %r11, %rsi
  40368d:	4c 89 de             	mov    %r11,%rsi
# call printf@plt
mov $0, %eax
  403690:	b8 00 00 00 00       	mov    $0x0,%eax

#popq %r11

#pushq %r9
movq -32(%rbp), %r9
  403695:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9

leaq .EIP(%rip), %rdi
  403699:	48 8d 3d 37 ff ff ff 	lea    -0xc9(%rip),%rdi        # 4035d7 <.EIP>
movq %r9, %rsi
  4036a0:	4c 89 ce             	mov    %r9,%rsi
#call printf@plt
mov $0, %eax
  4036a3:	b8 00 00 00 00       	mov    $0x0,%eax
#popq %r9
# coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data

#pushq %r9
leaq .CODATA(%rip), %rdi
  4036a8:	48 8d 3d 36 ff ff ff 	lea    -0xca(%rip),%rdi        # 4035e5 <.CODATA>
movq -40(%rbp), %rsi
  4036af:	48 8b 75 d8          	mov    -0x28(%rbp),%rsi
#call printf@plt
mov $0, %eax
  4036b3:	b8 00 00 00 00       	mov    $0x0,%eax
#popq %r9




movq -32(%rbp), %r9
  4036b8:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9
leaq after(%rip), %r11
  4036bc:	4c 8d 1d 11 00 00 00 	lea    0x11(%rip),%r11        # 4036d4 <after>
#pushq %r11
#movq %r11, %rsp

#mov %rbp, %rsp

movq -16(%rbp), %rdi
  4036c3:	48 8b 7d f0          	mov    -0x10(%rbp),%rdi
movq -24(%rbp), %rsi
  4036c7:	48 8b 75 e8          	mov    -0x18(%rbp),%rsi
movq -40(%rbp), %rdx
  4036cb:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx

#subq $8, %rsp
# pushq %rbp
#mov %rsp, %rbp
pushq %r11
  4036cf:	41 53                	push   %r11


jmp *%r9
  4036d1:	41 ff e1             	jmp    *%r9

00000000004036d4 <after>:
after:
# pushq %rbp

movq %rsp, %rbp
  4036d4:	48 89 e5             	mov    %rsp,%rbp

leaq .RET(%rip), %rdi
  4036d7:	48 8d 3d 2f ff ff ff 	lea    -0xd1(%rip),%rdi        # 40360d <.RET>
movq %r9, %rsi
  4036de:	4c 89 ce             	mov    %r9,%rsi
call printf@plt
  4036e1:	e8 9a d9 ff ff       	call   401080 <printf@plt>
mov $0, %eax
  4036e6:	b8 00 00 00 00       	mov    $0x0,%eax


#pop %rbp
add $1024, %rsp
  4036eb:	48 81 c4 00 04 00 00 	add    $0x400,%rsp
#movq %rsp, %rbp
popq %rbp
  4036f2:	5d                   	pop    %rbp
  4036f3:	c3                   	ret

Disassembly of section .fini:

00000000004036f4 <_fini>:
  4036f4:	f3 0f 1e fa          	endbr64
  4036f8:	48 83 ec 08          	sub    $0x8,%rsp
  4036fc:	48 83 c4 08          	add    $0x8,%rsp
  403700:	c3                   	ret
