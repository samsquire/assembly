
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
  401148:	48 c7 c7 8b 20 40 00 	mov    $0x40208b,%rdi
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
  401216:	55                   	push   %rbp
  401217:	48 89 e5             	mov    %rsp,%rbp
  40121a:	90                   	nop
  40121b:	5d                   	pop    %rbp
  40121c:	c3                   	ret

000000000040121d <coroutine_func>:
  40121d:	55                   	push   %rbp
  40121e:	48 89 e5             	mov    %rsp,%rbp
  401221:	48 83 ec 20          	sub    $0x20,%rsp
  401225:	48 89 f8             	mov    %rdi,%rax
  401228:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  40122c:	48 89 f0             	mov    %rsi,%rax
  40122f:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
  401233:	48 89 d0             	mov    %rdx,%rax
  401236:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  40123a:	48 8b 4d f8          	mov    -0x8(%rbp),%rcx
  40123e:	48 8b 55 f0          	mov    -0x10(%rbp),%rdx
  401242:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401246:	48 89 c6             	mov    %rax,%rsi
  401249:	48 8d 05 b8 2d 00 00 	lea    0x2db8(%rip),%rax        # 404008 <_IO_stdin_used+0x8>
  401250:	48 89 c7             	mov    %rax,%rdi
  401253:	b8 00 00 00 00       	mov    $0x0,%eax
  401258:	e8 23 fe ff ff       	call   401080 <printf@plt>
  40125d:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401261:	48 8b 40 10          	mov    0x10(%rax),%rax
  401265:	48 89 c6             	mov    %rax,%rsi
  401268:	48 8d 05 a8 2d 00 00 	lea    0x2da8(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  40126f:	48 89 c7             	mov    %rax,%rdi
  401272:	b8 00 00 00 00       	mov    $0x0,%eax
  401277:	e8 04 fe ff ff       	call   401080 <printf@plt>
  40127c:	4c 8d 1d 00 00 00 00 	lea    0x0(%rip),%r11        # 401283 <coroutine_func+0x66>
  401283:	4c 89 da             	mov    %r11,%rdx
  401286:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  40128a:	48 89 50 10          	mov    %rdx,0x10(%rax)
  40128e:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401292:	48 8b 00             	mov    (%rax),%rax
  401295:	89 45 e4             	mov    %eax,-0x1c(%rbp)
  401298:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  40129c:	48 8b 00             	mov    (%rax),%rax
  40129f:	48 89 c4             	mov    %rax,%rsp
  4012a2:	b8 00 00 00 00       	mov    $0x0,%eax
  4012a7:	c9                   	leave
  4012a8:	c3                   	ret

00000000004012a9 <pollthreads>:
  4012a9:	55                   	push   %rbp
  4012aa:	48 89 e5             	mov    %rsp,%rbp
  4012ad:	48 89 7d d8          	mov    %rdi,-0x28(%rbp)
  4012b1:	48 89 75 d0          	mov    %rsi,-0x30(%rbp)
  4012b5:	48 89 55 c8          	mov    %rdx,-0x38(%rbp)
  4012b9:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
  4012bd:	4c 89 45 b8          	mov    %r8,-0x48(%rbp)
  4012c1:	48 c7 45 f0 04 00 00 00 	movq   $0x4,-0x10(%rbp)
  4012c9:	48 c7 45 f8 08 00 00 00 	movq   $0x8,-0x8(%rbp)
  4012d1:	c7 45 e8 01 00 00 00 	movl   $0x1,-0x18(%rbp)
  4012d8:	e9 9b 00 00 00       	jmp    401378 <pollthreads+0xcf>
  4012dd:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4012e1:	48 8b 40 30          	mov    0x30(%rax),%rax
  4012e5:	48 05 00 04 00 00    	add    $0x400,%rax
  4012eb:	48 8b 50 20          	mov    0x20(%rax),%rdx
  4012ef:	8b 45 e8             	mov    -0x18(%rbp),%eax
  4012f2:	48 98                	cltq
  4012f4:	48 c1 e0 02          	shl    $0x2,%rax
  4012f8:	48 01 d0             	add    %rdx,%rax
  4012fb:	8b 00                	mov    (%rax),%eax
  4012fd:	89 45 ec             	mov    %eax,-0x14(%rbp)
  401300:	8b 45 ec             	mov    -0x14(%rbp),%eax
  401303:	48 98                	cltq
  401305:	48 23 45 f0          	and    -0x10(%rbp),%rax
  401309:	48 39 45 f0          	cmp    %rax,-0x10(%rbp)
  40130d:	74 06                	je     401315 <pollthreads+0x6c>
  40130f:	83 7d ec 00          	cmpl   $0x0,-0x14(%rbp)
  401313:	75 25                	jne    40133a <pollthreads+0x91>
  401315:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401319:	8b 00                	mov    (%rax),%eax
  40131b:	8d 48 01             	lea    0x1(%rax),%ecx
  40131e:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
  401322:	89 0a                	mov    %ecx,(%rdx)
  401324:	48 98                	cltq
  401326:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  40132e:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
  401332:	48 01 c2             	add    %rax,%rdx
  401335:	8b 45 e8             	mov    -0x18(%rbp),%eax
  401338:	89 02                	mov    %eax,(%rdx)
  40133a:	8b 45 ec             	mov    -0x14(%rbp),%eax
  40133d:	48 98                	cltq
  40133f:	48 23 45 f8          	and    -0x8(%rbp),%rax
  401343:	48 39 45 f8          	cmp    %rax,-0x8(%rbp)
  401347:	74 06                	je     40134f <pollthreads+0xa6>
  401349:	83 7d ec 00          	cmpl   $0x0,-0x14(%rbp)
  40134d:	75 25                	jne    401374 <pollthreads+0xcb>
  40134f:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
  401353:	8b 00                	mov    (%rax),%eax
  401355:	8d 48 01             	lea    0x1(%rax),%ecx
  401358:	48 8b 55 c0          	mov    -0x40(%rbp),%rdx
  40135c:	89 0a                	mov    %ecx,(%rdx)
  40135e:	48 98                	cltq
  401360:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401368:	48 8b 45 d0          	mov    -0x30(%rbp),%rax
  40136c:	48 01 c2             	add    %rax,%rdx
  40136f:	8b 45 e8             	mov    -0x18(%rbp),%eax
  401372:	89 02                	mov    %eax,(%rdx)
  401374:	83 45 e8 01          	addl   $0x1,-0x18(%rbp)
  401378:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  40137c:	8b 40 68             	mov    0x68(%rax),%eax
  40137f:	39 45 e8             	cmp    %eax,-0x18(%rbp)
  401382:	0f 8c 55 ff ff ff    	jl     4012dd <pollthreads+0x34>
  401388:	b8 00 00 00 00       	mov    $0x0,%eax
  40138d:	5d                   	pop    %rbp
  40138e:	c3                   	ret

000000000040138f <findavailable>:
  40138f:	55                   	push   %rbp
  401390:	48 89 e5             	mov    %rsp,%rbp
  401393:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  401397:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
  40139b:	48 89 55 d8          	mov    %rdx,-0x28(%rbp)
  40139f:	48 89 4d d0          	mov    %rcx,-0x30(%rbp)
  4013a3:	4c 89 45 c8          	mov    %r8,-0x38(%rbp)
  4013a7:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
  4013ae:	eb 64                	jmp    401414 <findavailable+0x85>
  4013b0:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4013b4:	48 8b 90 a0 00 00 00 	mov    0xa0(%rax),%rdx
  4013bb:	8b 45 fc             	mov    -0x4(%rbp),%eax
  4013be:	48 98                	cltq
  4013c0:	48 c1 e0 05          	shl    $0x5,%rax
  4013c4:	48 01 d0             	add    %rdx,%rax
  4013c7:	8b 40 10             	mov    0x10(%rax),%eax
  4013ca:	83 f8 01             	cmp    $0x1,%eax
  4013cd:	75 41                	jne    401410 <findavailable+0x81>
  4013cf:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013d3:	8b 00                	mov    (%rax),%eax
  4013d5:	48 98                	cltq
  4013d7:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4013df:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  4013e3:	48 01 c2             	add    %rax,%rdx
  4013e6:	8b 45 fc             	mov    -0x4(%rbp),%eax
  4013e9:	48 98                	cltq
  4013eb:	48 89 02             	mov    %rax,(%rdx)
  4013ee:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013f2:	8b 00                	mov    (%rax),%eax
  4013f4:	8d 50 01             	lea    0x1(%rax),%edx
  4013f7:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4013fb:	89 10                	mov    %edx,(%rax)
  4013fd:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401401:	8b 10                	mov    (%rax),%edx
  401403:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401407:	8b 40 68             	mov    0x68(%rax),%eax
  40140a:	01 c0                	add    %eax,%eax
  40140c:	39 c2                	cmp    %eax,%edx
  40140e:	74 20                	je     401430 <findavailable+0xa1>
  401410:	83 45 fc 01          	addl   $0x1,-0x4(%rbp)
  401414:	8b 45 fc             	mov    -0x4(%rbp),%eax
  401417:	48 63 d0             	movslq %eax,%rdx
  40141a:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  40141e:	48 8b 80 b8 00 00 00 	mov    0xb8(%rax),%rax
  401425:	48 83 c0 01          	add    $0x1,%rax
  401429:	48 39 c2             	cmp    %rax,%rdx
  40142c:	7c 82                	jl     4013b0 <findavailable+0x21>
  40142e:	eb 01                	jmp    401431 <findavailable+0xa2>
  401430:	90                   	nop
  401431:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401435:	8b 00                	mov    (%rax),%eax
  401437:	85 c0                	test   %eax,%eax
  401439:	75 07                	jne    401442 <findavailable+0xb3>
  40143b:	b8 01 00 00 00       	mov    $0x1,%eax
  401440:	eb 05                	jmp    401447 <findavailable+0xb8>
  401442:	b8 00 00 00 00       	mov    $0x0,%eax
  401447:	5d                   	pop    %rbp
  401448:	c3                   	ret

0000000000401449 <singlewriter3>:
  401449:	55                   	push   %rbp
  40144a:	48 89 e5             	mov    %rsp,%rbp
  40144d:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  401451:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
  401455:	48 89 55 d8          	mov    %rdx,-0x28(%rbp)
  401459:	48 89 4d d0          	mov    %rcx,-0x30(%rbp)
  40145d:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
  401464:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401468:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  40146e:	85 c0                	test   %eax,%eax
  401470:	90                   	nop
  401471:	5d                   	pop    %rbp
  401472:	c3                   	ret

0000000000401473 <singlewriter2>:
  401473:	55                   	push   %rbp
  401474:	48 89 e5             	mov    %rsp,%rbp
  401477:	48 83 ec 40          	sub    $0x40,%rsp
  40147b:	48 89 7d d8          	mov    %rdi,-0x28(%rbp)
  40147f:	48 89 75 d0          	mov    %rsi,-0x30(%rbp)
  401483:	48 89 55 c8          	mov    %rdx,-0x38(%rbp)
  401487:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
  40148b:	c7 45 ec 00 00 00 00 	movl   $0x0,-0x14(%rbp)
  401492:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401496:	8b 80 00 02 00 00    	mov    0x200(%rax),%eax
  40149c:	85 c0                	test   %eax,%eax
  40149e:	0f 84 c7 00 00 00    	je     40156b <singlewriter2+0xf8>
  4014a4:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014a8:	8b 80 00 02 00 00    	mov    0x200(%rax),%eax
  4014ae:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  4014b2:	8b 52 68             	mov    0x68(%rdx),%edx
  4014b5:	8d 4a ff             	lea    -0x1(%rdx),%ecx
  4014b8:	99                   	cltd
  4014b9:	f7 f9                	idiv   %ecx
  4014bb:	89 d0                	mov    %edx,%eax
  4014bd:	85 c0                	test   %eax,%eax
  4014bf:	0f 85 a6 00 00 00    	jne    40156b <singlewriter2+0xf8>
  4014c5:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014c9:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4014cd:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  4014d1:	8b 40 64             	mov    0x64(%rax),%eax
  4014d4:	48 98                	cltq
  4014d6:	48 c1 e0 0a          	shl    $0xa,%rax
  4014da:	48 01 d0             	add    %rdx,%rax
  4014dd:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
  4014e1:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4014e5:	48 8b 88 18 03 00 00 	mov    0x318(%rax),%rcx
  4014ec:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4014f0:	8b 80 24 03 00 00    	mov    0x324(%rax),%eax
  4014f6:	48 63 d0             	movslq %eax,%rdx
  4014f9:	48 89 d0             	mov    %rdx,%rax
  4014fc:	48 01 c0             	add    %rax,%rax
  4014ff:	48 01 d0             	add    %rdx,%rax
  401502:	48 c1 e0 04          	shl    $0x4,%rax
  401506:	48 01 c8             	add    %rcx,%rax
  401509:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  40150d:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401511:	48 83 c0 08          	add    $0x8,%rax
  401515:	48 89 c6             	mov    %rax,%rsi
  401518:	bf 04 00 00 00       	mov    $0x4,%edi
  40151d:	e8 2e fb ff ff       	call   401050 <clock_gettime@plt>
  401522:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401526:	8b 80 24 03 00 00    	mov    0x324(%rax),%eax
  40152c:	8d 50 01             	lea    0x1(%rax),%edx
  40152f:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401533:	8b 88 20 03 00 00    	mov    0x320(%rax),%ecx
  401539:	89 d0                	mov    %edx,%eax
  40153b:	99                   	cltd
  40153c:	f7 f9                	idiv   %ecx
  40153e:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  401542:	89 90 24 03 00 00    	mov    %edx,0x324(%rax)
  401548:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  40154c:	c7 40 20 01 00 00 00 	movl   $0x1,0x20(%rax)
  401553:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
  401557:	8b 50 64             	mov    0x64(%rax),%edx
  40155a:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  40155e:	89 10                	mov    %edx,(%rax)
  401560:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401564:	c7 40 24 01 00 00 00 	movl   $0x1,0x24(%rax)
  40156b:	90                   	nop
  40156c:	c9                   	leave
  40156d:	c3                   	ret

000000000040156e <singlewriter>:
  40156e:	55                   	push   %rbp
  40156f:	48 89 e5             	mov    %rsp,%rbp
  401572:	48 83 ec 70          	sub    $0x70,%rsp
  401576:	48 89 7d a8          	mov    %rdi,-0x58(%rbp)
  40157a:	48 89 75 a0          	mov    %rsi,-0x60(%rbp)
  40157e:	48 89 55 98          	mov    %rdx,-0x68(%rbp)
  401582:	48 89 4d 90          	mov    %rcx,-0x70(%rbp)
  401586:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40158f:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  401593:	31 c0                	xor    %eax,%eax
  401595:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401599:	48 8b 40 30          	mov    0x30(%rax),%rax
  40159d:	8b 80 0c 02 00 00    	mov    0x20c(%rax),%eax
  4015a3:	8d 50 01             	lea    0x1(%rax),%edx
  4015a6:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015aa:	8b 70 68             	mov    0x68(%rax),%esi
  4015ad:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015b1:	48 8b 48 30          	mov    0x30(%rax),%rcx
  4015b5:	89 d0                	mov    %edx,%eax
  4015b7:	99                   	cltd
  4015b8:	f7 fe                	idiv   %esi
  4015ba:	89 d0                	mov    %edx,%eax
  4015bc:	89 81 0c 02 00 00    	mov    %eax,0x20c(%rcx)
  4015c2:	c7 45 b0 00 00 00 00 	movl   $0x0,-0x50(%rbp)
  4015c9:	c7 45 b4 00 00 00 00 	movl   $0x0,-0x4c(%rbp)
  4015d0:	c7 45 b8 00 00 00 00 	movl   $0x0,-0x48(%rbp)
  4015d7:	48 8b 7d 90          	mov    -0x70(%rbp),%rdi
  4015db:	48 8b 4d 98          	mov    -0x68(%rbp),%rcx
  4015df:	48 8d 55 b8          	lea    -0x48(%rbp),%rdx
  4015e3:	48 8b 75 a0          	mov    -0x60(%rbp),%rsi
  4015e7:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4015eb:	49 89 f8             	mov    %rdi,%r8
  4015ee:	48 89 c7             	mov    %rax,%rdi
  4015f1:	e8 99 fd ff ff       	call   40138f <findavailable>
  4015f6:	89 45 cc             	mov    %eax,-0x34(%rbp)
  4015f9:	83 7d cc 01          	cmpl   $0x1,-0x34(%rbp)
  4015fd:	75 0a                	jne    401609 <singlewriter+0x9b>
  4015ff:	b8 01 00 00 00       	mov    $0x1,%eax
  401604:	e9 f9 02 00 00       	jmp    401902 <singlewriter+0x394>
  401609:	48 8d 7d b4          	lea    -0x4c(%rbp),%rdi
  40160d:	48 8d 4d b0          	lea    -0x50(%rbp),%rcx
  401611:	48 8b 55 90          	mov    -0x70(%rbp),%rdx
  401615:	48 8b 75 98          	mov    -0x68(%rbp),%rsi
  401619:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40161d:	49 89 f8             	mov    %rdi,%r8
  401620:	48 89 c7             	mov    %rax,%rdi
  401623:	e8 81 fc ff ff       	call   4012a9 <pollthreads>
  401628:	c7 45 bc 00 00 00 00 	movl   $0x0,-0x44(%rbp)
  40162f:	c7 45 c0 00 00 00 00 	movl   $0x0,-0x40(%rbp)
  401636:	e9 10 01 00 00       	jmp    40174b <singlewriter+0x1dd>
  40163b:	8b 45 b8             	mov    -0x48(%rbp),%eax
  40163e:	39 45 bc             	cmp    %eax,-0x44(%rbp)
  401641:	0f 84 12 01 00 00    	je     401759 <singlewriter+0x1eb>
  401647:	8b 45 c0             	mov    -0x40(%rbp),%eax
  40164a:	48 98                	cltq
  40164c:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  401654:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  401658:	48 01 d0             	add    %rdx,%rax
  40165b:	8b 00                	mov    (%rax),%eax
  40165d:	89 45 d0             	mov    %eax,-0x30(%rbp)
  401660:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401664:	48 8b 88 a0 00 00 00 	mov    0xa0(%rax),%rcx
  40166b:	8b 45 bc             	mov    -0x44(%rbp),%eax
  40166e:	8d 50 01             	lea    0x1(%rax),%edx
  401671:	89 55 bc             	mov    %edx,-0x44(%rbp)
  401674:	48 98                	cltq
  401676:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  40167e:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  401682:	48 01 d0             	add    %rdx,%rax
  401685:	48 8b 00             	mov    (%rax),%rax
  401688:	48 c1 e0 05          	shl    $0x5,%rax
  40168c:	48 01 c8             	add    %rcx,%rax
  40168f:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  401693:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401697:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
  40169e:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016a2:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016a6:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016a9:	48 98                	cltq
  4016ab:	48 c1 e0 0a          	shl    $0xa,%rax
  4016af:	48 01 c2             	add    %rax,%rdx
  4016b2:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016b6:	48 89 82 a8 00 00 00 	mov    %rax,0xa8(%rdx)
  4016bd:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016c1:	8b 55 d0             	mov    -0x30(%rbp),%edx
  4016c4:	89 50 14             	mov    %edx,0x14(%rax)
  4016c7:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016cb:	48 8b 00             	mov    (%rax),%rax
  4016ce:	89 45 d4             	mov    %eax,-0x2c(%rbp)
  4016d1:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016d5:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016d9:	8b 45 d0             	mov    -0x30(%rbp),%eax
  4016dc:	48 98                	cltq
  4016de:	48 c1 e0 0a          	shl    $0xa,%rax
  4016e2:	48 01 c2             	add    %rax,%rdx
  4016e5:	8b 45 d4             	mov    -0x2c(%rbp),%eax
  4016e8:	89 42 14             	mov    %eax,0x14(%rdx)
  4016eb:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  4016ef:	48 8b 40 08          	mov    0x8(%rax),%rax
  4016f3:	89 45 d8             	mov    %eax,-0x28(%rbp)
  4016f6:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4016fa:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4016fe:	8b 45 d0             	mov    -0x30(%rbp),%eax
  401701:	48 98                	cltq
  401703:	48 c1 e0 0a          	shl    $0xa,%rax
  401707:	48 01 c2             	add    %rax,%rdx
  40170a:	8b 45 d8             	mov    -0x28(%rbp),%eax
  40170d:	89 42 18             	mov    %eax,0x18(%rdx)
  401710:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401714:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401718:	8b 45 d0             	mov    -0x30(%rbp),%eax
  40171b:	48 98                	cltq
  40171d:	48 c1 e0 0a          	shl    $0xa,%rax
  401721:	48 01 d0             	add    %rdx,%rax
  401724:	8b 90 c8 00 00 00    	mov    0xc8(%rax),%edx
  40172a:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40172e:	48 8b 48 30          	mov    0x30(%rax),%rcx
  401732:	8b 45 d0             	mov    -0x30(%rbp),%eax
  401735:	48 98                	cltq
  401737:	48 c1 e0 0a          	shl    $0xa,%rax
  40173b:	48 01 c8             	add    %rcx,%rax
  40173e:	83 ca 10             	or     $0x10,%edx
  401741:	89 90 c8 00 00 00    	mov    %edx,0xc8(%rax)
  401747:	83 45 c0 01          	addl   $0x1,-0x40(%rbp)
  40174b:	8b 45 b0             	mov    -0x50(%rbp),%eax
  40174e:	39 45 c0             	cmp    %eax,-0x40(%rbp)
  401751:	0f 8c e4 fe ff ff    	jl     40163b <singlewriter+0xcd>
  401757:	eb 01                	jmp    40175a <singlewriter+0x1ec>
  401759:	90                   	nop
  40175a:	c7 45 c4 00 00 00 00 	movl   $0x0,-0x3c(%rbp)
  401761:	e9 10 01 00 00       	jmp    401876 <singlewriter+0x308>
  401766:	8b 45 b8             	mov    -0x48(%rbp),%eax
  401769:	39 45 bc             	cmp    %eax,-0x44(%rbp)
  40176c:	0f 84 12 01 00 00    	je     401884 <singlewriter+0x316>
  401772:	8b 45 c4             	mov    -0x3c(%rbp),%eax
  401775:	48 98                	cltq
  401777:	48 8d 14 85 00 00 00 00 	lea    0x0(,%rax,4),%rdx
  40177f:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  401783:	48 01 d0             	add    %rdx,%rax
  401786:	8b 00                	mov    (%rax),%eax
  401788:	89 45 dc             	mov    %eax,-0x24(%rbp)
  40178b:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40178f:	48 8b 88 a0 00 00 00 	mov    0xa0(%rax),%rcx
  401796:	8b 45 bc             	mov    -0x44(%rbp),%eax
  401799:	8d 50 01             	lea    0x1(%rax),%edx
  40179c:	89 55 bc             	mov    %edx,-0x44(%rbp)
  40179f:	48 98                	cltq
  4017a1:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4017a9:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  4017ad:	48 01 d0             	add    %rdx,%rax
  4017b0:	48 8b 00             	mov    (%rax),%rax
  4017b3:	48 c1 e0 05          	shl    $0x5,%rax
  4017b7:	48 01 c8             	add    %rcx,%rax
  4017ba:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
  4017be:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017c2:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
  4017c9:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4017cd:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4017d1:	8b 45 dc             	mov    -0x24(%rbp),%eax
  4017d4:	48 98                	cltq
  4017d6:	48 c1 e0 0a          	shl    $0xa,%rax
  4017da:	48 01 c2             	add    %rax,%rdx
  4017dd:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017e1:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
  4017e8:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017ec:	8b 55 dc             	mov    -0x24(%rbp),%edx
  4017ef:	89 50 14             	mov    %edx,0x14(%rax)
  4017f2:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  4017f6:	48 8b 00             	mov    (%rax),%rax
  4017f9:	89 45 e0             	mov    %eax,-0x20(%rbp)
  4017fc:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401800:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401804:	8b 45 dc             	mov    -0x24(%rbp),%eax
  401807:	48 98                	cltq
  401809:	48 c1 e0 0a          	shl    $0xa,%rax
  40180d:	48 01 c2             	add    %rax,%rdx
  401810:	8b 45 e0             	mov    -0x20(%rbp),%eax
  401813:	89 42 40             	mov    %eax,0x40(%rdx)
  401816:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  40181a:	48 8b 40 08          	mov    0x8(%rax),%rax
  40181e:	89 45 e4             	mov    %eax,-0x1c(%rbp)
  401821:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401825:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401829:	8b 45 dc             	mov    -0x24(%rbp),%eax
  40182c:	48 98                	cltq
  40182e:	48 c1 e0 0a          	shl    $0xa,%rax
  401832:	48 01 c2             	add    %rax,%rdx
  401835:	8b 45 e4             	mov    -0x1c(%rbp),%eax
  401838:	89 42 44             	mov    %eax,0x44(%rdx)
  40183b:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  40183f:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401843:	8b 45 dc             	mov    -0x24(%rbp),%eax
  401846:	48 98                	cltq
  401848:	48 c1 e0 0a          	shl    $0xa,%rax
  40184c:	48 01 d0             	add    %rdx,%rax
  40184f:	8b 90 c8 00 00 00    	mov    0xc8(%rax),%edx
  401855:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401859:	48 8b 48 30          	mov    0x30(%rax),%rcx
  40185d:	8b 45 dc             	mov    -0x24(%rbp),%eax
  401860:	48 98                	cltq
  401862:	48 c1 e0 0a          	shl    $0xa,%rax
  401866:	48 01 c8             	add    %rcx,%rax
  401869:	83 ca 20             	or     $0x20,%edx
  40186c:	89 90 c8 00 00 00    	mov    %edx,0xc8(%rax)
  401872:	83 45 c4 01          	addl   $0x1,-0x3c(%rbp)
  401876:	8b 45 b4             	mov    -0x4c(%rbp),%eax
  401879:	39 45 c4             	cmp    %eax,-0x3c(%rbp)
  40187c:	0f 8c e4 fe ff ff    	jl     401766 <singlewriter+0x1f8>
  401882:	eb 01                	jmp    401885 <singlewriter+0x317>
  401884:	90                   	nop
  401885:	c7 45 c8 00 00 00 00 	movl   $0x0,-0x38(%rbp)
  40188c:	eb 63                	jmp    4018f1 <singlewriter+0x383>
  40188e:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  401892:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401896:	8b 45 c8             	mov    -0x38(%rbp),%eax
  401899:	48 98                	cltq
  40189b:	48 c1 e0 0a          	shl    $0xa,%rax
  40189f:	48 01 d0             	add    %rdx,%rax
  4018a2:	8b 80 c8 00 00 00    	mov    0xc8(%rax),%eax
  4018a8:	85 c0                	test   %eax,%eax
  4018aa:	74 41                	je     4018ed <singlewriter+0x37f>
  4018ac:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018b0:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4018b4:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018b7:	48 98                	cltq
  4018b9:	48 c1 e0 0a          	shl    $0xa,%rax
  4018bd:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
  4018c1:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018c5:	48 8b 50 30          	mov    0x30(%rax),%rdx
  4018c9:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018cc:	48 98                	cltq
  4018ce:	48 c1 e0 0a          	shl    $0xa,%rax
  4018d2:	48 01 d0             	add    %rdx,%rax
  4018d5:	48 8b 50 20          	mov    0x20(%rax),%rdx
  4018d9:	8b 45 c8             	mov    -0x38(%rbp),%eax
  4018dc:	48 98                	cltq
  4018de:	48 c1 e0 02          	shl    $0x2,%rax
  4018e2:	48 01 c2             	add    %rax,%rdx
  4018e5:	8b 81 c8 00 00 00    	mov    0xc8(%rcx),%eax
  4018eb:	89 02                	mov    %eax,(%rdx)
  4018ed:	83 45 c8 01          	addl   $0x1,-0x38(%rbp)
  4018f1:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4018f5:	8b 40 68             	mov    0x68(%rax),%eax
  4018f8:	39 45 c8             	cmp    %eax,-0x38(%rbp)
  4018fb:	7c 91                	jl     40188e <singlewriter+0x320>
  4018fd:	b8 00 00 00 00       	mov    $0x0,%eax
  401902:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  401906:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  40190f:	74 05                	je     401916 <singlewriter+0x3a8>
  401911:	e8 5a f7 ff ff       	call   401070 <__stack_chk_fail@plt>
  401916:	c9                   	leave
  401917:	c3                   	ret

0000000000401918 <threadwork>:
  401918:	55                   	push   %rbp
  401919:	48 89 e5             	mov    %rsp,%rbp
  40191c:	48 81 ec 90 00 00 00 	sub    $0x90,%rsp
  401923:	48 89 bd 78 ff ff ff 	mov    %rdi,-0x88(%rbp)
  40192a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401933:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  401937:	31 c0                	xor    %eax,%eax
  401939:	c7 45 a4 05 00 00 00 	movl   $0x5,-0x5c(%rbp)
  401940:	c7 45 a8 01 00 00 00 	movl   $0x1,-0x58(%rbp)
  401947:	c7 45 ac ff 00 00 00 	movl   $0xff,-0x54(%rbp)
  40194e:	48 89 e0             	mov    %rsp,%rax
  401951:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
  401955:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  40195c:	48 8b 80 c8 03 00 00 	mov    0x3c8(%rax),%rax
  401963:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  401967:	48 89 10             	mov    %rdx,(%rax)
  40196a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401971:	48 8b 90 c8 03 00 00 	mov    0x3c8(%rax),%rdx
  401978:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  40197f:	48 8b 80 c0 03 00 00 	mov    0x3c0(%rax),%rax
  401986:	be 03 00 00 00       	mov    $0x3,%esi
  40198b:	48 89 c7             	mov    %rax,%rdi
  40198e:	e8 05 1d 00 00       	call   403698 <switch_to>
  401993:	48 8d 45 e0          	lea    -0x20(%rbp),%rax
  401997:	48 89 c6             	mov    %rax,%rsi
  40199a:	bf 04 00 00 00       	mov    $0x4,%edi
  40199f:	e8 ac f6 ff ff       	call   401050 <clock_gettime@plt>
  4019a4:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019ab:	8b 40 5c             	mov    0x5c(%rax),%eax
  4019ae:	83 f8 02             	cmp    $0x2,%eax
  4019b1:	0f 85 9f 01 00 00    	jne    401b56 <threadwork+0x23e>
  4019b7:	c7 45 98 00 00 00 00 	movl   $0x0,-0x68(%rbp)
  4019be:	e9 50 01 00 00       	jmp    401b13 <threadwork+0x1fb>
  4019c3:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019ca:	48 8b 40 28          	mov    0x28(%rax),%rax
  4019ce:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  4019d5:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  4019dc:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  4019e2:	c1 e0 07             	shl    $0x7,%eax
  4019e5:	48 98                	cltq
  4019e7:	48 c1 e0 03          	shl    $0x3,%rax
  4019eb:	48 01 d0             	add    %rdx,%rax
  4019ee:	48 8b 00             	mov    (%rax),%rax
  4019f1:	8b 55 a8             	mov    -0x58(%rbp),%edx
  4019f4:	48 63 fa             	movslq %edx,%rdi
  4019f7:	48 99                	cqto
  4019f9:	48 f7 ff             	idiv   %rdi
  4019fc:	48 89 c2             	mov    %rax,%rdx
  4019ff:	8b 45 ac             	mov    -0x54(%rbp),%eax
  401a02:	48 63 c8             	movslq %eax,%rcx
  401a05:	48 89 d0             	mov    %rdx,%rax
  401a08:	48 99                	cqto
  401a0a:	48 f7 f9             	idiv   %rcx
  401a0d:	48 89 d0             	mov    %rdx,%rax
  401a10:	89 45 9c             	mov    %eax,-0x64(%rbp)
  401a13:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a1a:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401a20:	89 45 a0             	mov    %eax,-0x60(%rbp)
  401a23:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a2a:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401a30:	c1 e0 18             	shl    $0x18,%eax
  401a33:	89 c2                	mov    %eax,%edx
  401a35:	8b 45 9c             	mov    -0x64(%rbp),%eax
  401a38:	c1 e0 10             	shl    $0x10,%eax
  401a3b:	89 d6                	mov    %edx,%esi
  401a3d:	09 c6                	or     %eax,%esi
  401a3f:	8b 45 a0             	mov    -0x60(%rbp),%eax
  401a42:	48 63 d0             	movslq %eax,%rdx
  401a45:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401a4c:	48 c1 ea 20          	shr    $0x20,%rdx
  401a50:	01 c2                	add    %eax,%edx
  401a52:	c1 fa 07             	sar    $0x7,%edx
  401a55:	89 c7                	mov    %eax,%edi
  401a57:	c1 ff 1f             	sar    $0x1f,%edi
  401a5a:	89 d1                	mov    %edx,%ecx
  401a5c:	29 f9                	sub    %edi,%ecx
  401a5e:	89 ca                	mov    %ecx,%edx
  401a60:	c1 e2 08             	shl    $0x8,%edx
  401a63:	29 ca                	sub    %ecx,%edx
  401a65:	29 d0                	sub    %edx,%eax
  401a67:	89 c1                	mov    %eax,%ecx
  401a69:	89 f0                	mov    %esi,%eax
  401a6b:	09 c8                	or     %ecx,%eax
  401a6d:	48 98                	cltq
  401a6f:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
  401a73:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a7a:	48 8b 50 30          	mov    0x30(%rax),%rdx
  401a7e:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a85:	8b 40 64             	mov    0x64(%rax),%eax
  401a88:	48 98                	cltq
  401a8a:	48 c1 e0 0a          	shl    $0xa,%rax
  401a8e:	48 01 d0             	add    %rdx,%rax
  401a91:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
  401a95:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401a9c:	48 8b 40 28          	mov    0x28(%rax),%rax
  401aa0:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401aa4:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401aa8:	48 01 d0             	add    %rdx,%rax
  401aab:	0f b6 00             	movzbl (%rax),%eax
  401aae:	3c ff                	cmp    $0xff,%al
  401ab0:	74 1a                	je     401acc <threadwork+0x1b4>
  401ab2:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ab9:	48 8b 40 50          	mov    0x50(%rax),%rax
  401abd:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401ac1:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ac8:	48 89 50 50          	mov    %rdx,0x50(%rax)
  401acc:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ad3:	8b 50 64             	mov    0x64(%rax),%edx
  401ad6:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401add:	48 8b 40 28          	mov    0x28(%rax),%rax
  401ae1:	48 8b 48 70          	mov    0x70(%rax),%rcx
  401ae5:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401ae9:	48 01 c8             	add    %rcx,%rax
  401aec:	88 10                	mov    %dl,(%rax)
  401aee:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401af5:	8b 80 80 01 00 00    	mov    0x180(%rax),%eax
  401afb:	83 c0 01             	add    $0x1,%eax
  401afe:	99                   	cltd
  401aff:	f7 7d a4             	idivl  -0x5c(%rbp)
  401b02:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b09:	89 90 80 01 00 00    	mov    %edx,0x180(%rax)
  401b0f:	83 45 98 01          	addl   $0x1,-0x68(%rbp)
  401b13:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b1a:	8b 40 68             	mov    0x68(%rax),%eax
  401b1d:	39 45 98             	cmp    %eax,-0x68(%rbp)
  401b20:	0f 8c 9d fe ff ff    	jl     4019c3 <threadwork+0xab>
  401b26:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b2d:	48 8b 40 28          	mov    0x28(%rax),%rax
  401b31:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401b38:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b3f:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401b45:	c1 e0 07             	shl    $0x7,%eax
  401b48:	48 98                	cltq
  401b4a:	48 c1 e0 03          	shl    $0x3,%rax
  401b4e:	48 01 d0             	add    %rdx,%rax
  401b51:	f0 48 83 00 01       	lock addq $0x1,(%rax)
  401b56:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b5d:	48 8b 40 28          	mov    0x28(%rax),%rax
  401b61:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401b68:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b6f:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401b75:	c1 e0 07             	shl    $0x7,%eax
  401b78:	48 98                	cltq
  401b7a:	48 c1 e0 03          	shl    $0x3,%rax
  401b7e:	48 01 d0             	add    %rdx,%rax
  401b81:	48 8b 00             	mov    (%rax),%rax
  401b84:	8b 55 a8             	mov    -0x58(%rbp),%edx
  401b87:	48 63 fa             	movslq %edx,%rdi
  401b8a:	48 99                	cqto
  401b8c:	48 f7 ff             	idiv   %rdi
  401b8f:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
  401b93:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401b9a:	8b 80 88 03 00 00    	mov    0x388(%rax),%eax
  401ba0:	48 98                	cltq
  401ba2:	48 39 45 c8          	cmp    %rax,-0x38(%rbp)
  401ba6:	74 11                	je     401bb9 <threadwork+0x2a1>
  401ba8:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401baf:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
  401bb9:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
  401bbd:	89 c2                	mov    %eax,%edx
  401bbf:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bc6:	89 90 88 03 00 00    	mov    %edx,0x388(%rax)
  401bcc:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401bd3:	48 8b 40 28          	mov    0x28(%rax),%rax
  401bd7:	48 8b 90 80 03 00 00 	mov    0x380(%rax),%rdx
  401bde:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401be5:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401beb:	c1 e0 07             	shl    $0x7,%eax
  401bee:	48 98                	cltq
  401bf0:	48 c1 e0 03          	shl    $0x3,%rax
  401bf4:	48 01 d0             	add    %rdx,%rax
  401bf7:	48 8b 00             	mov    (%rax),%rax
  401bfa:	48 89 45 d0          	mov    %rax,-0x30(%rbp)
  401bfe:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c05:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401c0c:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c13:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401c19:	48 63 d0             	movslq %eax,%rdx
  401c1c:	48 89 d0             	mov    %rdx,%rax
  401c1f:	48 01 c0             	add    %rax,%rax
  401c22:	48 01 d0             	add    %rdx,%rax
  401c25:	48 c1 e0 02          	shl    $0x2,%rax
  401c29:	48 01 c8             	add    %rcx,%rax
  401c2c:	8b 00                	mov    (%rax),%eax
  401c2e:	48 98                	cltq
  401c30:	48 39 45 d0          	cmp    %rax,-0x30(%rbp)
  401c34:	7f 0b                	jg     401c41 <threadwork+0x329>
  401c36:	48 83 7d d0 00       	cmpq   $0x0,-0x30(%rbp)
  401c3b:	0f 85 f9 02 00 00    	jne    401f3a <threadwork+0x622>
  401c41:	c7 45 94 00 00 00 00 	movl   $0x0,-0x6c(%rbp)
  401c48:	e9 d7 02 00 00       	jmp    401f24 <threadwork+0x60c>
  401c4d:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c54:	48 8b 40 48          	mov    0x48(%rax),%rax
  401c58:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401c5c:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c63:	48 89 50 48          	mov    %rdx,0x48(%rax)
  401c67:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c6e:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401c75:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401c7c:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401c82:	48 63 d0             	movslq %eax,%rdx
  401c85:	48 89 d0             	mov    %rdx,%rax
  401c88:	48 01 c0             	add    %rax,%rax
  401c8b:	48 01 d0             	add    %rdx,%rax
  401c8e:	48 c1 e0 02          	shl    $0x2,%rax
  401c92:	48 01 c8             	add    %rcx,%rax
  401c95:	8b 00                	mov    (%rax),%eax
  401c97:	99                   	cltd
  401c98:	f7 7d a8             	idivl  -0x58(%rbp)
  401c9b:	83 e8 01             	sub    $0x1,%eax
  401c9e:	99                   	cltd
  401c9f:	f7 7d ac             	idivl  -0x54(%rbp)
  401ca2:	89 d0                	mov    %edx,%eax
  401ca4:	48 98                	cltq
  401ca6:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  401caa:	48 83 7d b0 00       	cmpq   $0x0,-0x50(%rbp)
  401caf:	79 08                	jns    401cb9 <threadwork+0x3a1>
  401cb1:	48 c7 45 b0 00 00 00 00 	movq   $0x0,-0x50(%rbp)
  401cb9:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cc0:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401cc7:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cce:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401cd4:	48 63 d0             	movslq %eax,%rdx
  401cd7:	48 89 d0             	mov    %rdx,%rax
  401cda:	48 01 c0             	add    %rax,%rax
  401cdd:	48 01 d0             	add    %rdx,%rax
  401ce0:	48 c1 e0 02          	shl    $0x2,%rax
  401ce4:	48 01 c8             	add    %rcx,%rax
  401ce7:	8b 40 04             	mov    0x4(%rax),%eax
  401cea:	89 45 8c             	mov    %eax,-0x74(%rbp)
  401ced:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401cf4:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401cfa:	c1 e0 18             	shl    $0x18,%eax
  401cfd:	48 63 d0             	movslq %eax,%rdx
  401d00:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
  401d04:	48 c1 e0 10          	shl    $0x10,%rax
  401d08:	48 89 d6             	mov    %rdx,%rsi
  401d0b:	48 09 c6             	or     %rax,%rsi
  401d0e:	8b 45 8c             	mov    -0x74(%rbp),%eax
  401d11:	48 63 d0             	movslq %eax,%rdx
  401d14:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401d1b:	48 c1 ea 20          	shr    $0x20,%rdx
  401d1f:	01 c2                	add    %eax,%edx
  401d21:	c1 fa 07             	sar    $0x7,%edx
  401d24:	89 c1                	mov    %eax,%ecx
  401d26:	c1 f9 1f             	sar    $0x1f,%ecx
  401d29:	29 ca                	sub    %ecx,%edx
  401d2b:	89 d1                	mov    %edx,%ecx
  401d2d:	c1 e1 08             	shl    $0x8,%ecx
  401d30:	29 d1                	sub    %edx,%ecx
  401d32:	29 c8                	sub    %ecx,%eax
  401d34:	89 c2                	mov    %eax,%edx
  401d36:	48 63 c2             	movslq %edx,%rax
  401d39:	48 09 f0             	or     %rsi,%rax
  401d3c:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
  401d40:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d47:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401d4d:	89 45 90             	mov    %eax,-0x70(%rbp)
  401d50:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d57:	48 8b 40 28          	mov    0x28(%rax),%rax
  401d5b:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401d5f:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401d63:	48 01 d0             	add    %rdx,%rax
  401d66:	0f b6 00             	movzbl (%rax),%eax
  401d69:	3c ff                	cmp    $0xff,%al
  401d6b:	74 39                	je     401da6 <threadwork+0x48e>
  401d6d:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d74:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  401d7b:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401d7f:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d86:	48 89 90 98 03 00 00 	mov    %rdx,0x398(%rax)
  401d8d:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401d94:	48 8b 40 28          	mov    0x28(%rax),%rax
  401d98:	48 8b 50 70          	mov    0x70(%rax),%rdx
  401d9c:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401da0:	48 01 d0             	add    %rdx,%rax
  401da3:	c6 00 ff             	movb   $0xff,(%rax)
  401da6:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401dad:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401db4:	8b 45 90             	mov    -0x70(%rbp),%eax
  401db7:	48 63 d0             	movslq %eax,%rdx
  401dba:	48 89 d0             	mov    %rdx,%rax
  401dbd:	48 01 c0             	add    %rax,%rax
  401dc0:	48 01 d0             	add    %rdx,%rax
  401dc3:	48 c1 e0 02          	shl    $0x2,%rax
  401dc7:	48 01 c8             	add    %rcx,%rax
  401dca:	8b 40 04             	mov    0x4(%rax),%eax
  401dcd:	39 45 a4             	cmp    %eax,-0x5c(%rbp)
  401dd0:	7e 7c                	jle    401e4e <threadwork+0x536>
  401dd2:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401dd9:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401de0:	8b 45 90             	mov    -0x70(%rbp),%eax
  401de3:	48 63 d0             	movslq %eax,%rdx
  401de6:	48 89 d0             	mov    %rdx,%rax
  401de9:	48 01 c0             	add    %rax,%rax
  401dec:	48 01 d0             	add    %rdx,%rax
  401def:	48 c1 e0 02          	shl    $0x2,%rax
  401df3:	48 01 c8             	add    %rcx,%rax
  401df6:	8b 10                	mov    (%rax),%edx
  401df8:	83 c2 01             	add    $0x1,%edx
  401dfb:	89 10                	mov    %edx,(%rax)
  401dfd:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e04:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401e0b:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e0e:	48 63 d0             	movslq %eax,%rdx
  401e11:	48 89 d0             	mov    %rdx,%rax
  401e14:	48 01 c0             	add    %rax,%rax
  401e17:	48 01 d0             	add    %rdx,%rax
  401e1a:	48 c1 e0 02          	shl    $0x2,%rax
  401e1e:	48 01 c8             	add    %rcx,%rax
  401e21:	8b 48 04             	mov    0x4(%rax),%ecx
  401e24:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e2b:	48 8b b0 48 03 00 00 	mov    0x348(%rax),%rsi
  401e32:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e35:	48 63 d0             	movslq %eax,%rdx
  401e38:	48 89 d0             	mov    %rdx,%rax
  401e3b:	48 01 c0             	add    %rax,%rax
  401e3e:	48 01 d0             	add    %rdx,%rax
  401e41:	48 c1 e0 02          	shl    $0x2,%rax
  401e45:	48 01 f0             	add    %rsi,%rax
  401e48:	8d 51 01             	lea    0x1(%rcx),%edx
  401e4b:	89 50 04             	mov    %edx,0x4(%rax)
  401e4e:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e55:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401e5c:	8b 45 90             	mov    -0x70(%rbp),%eax
  401e5f:	48 63 d0             	movslq %eax,%rdx
  401e62:	48 89 d0             	mov    %rdx,%rax
  401e65:	48 01 c0             	add    %rax,%rax
  401e68:	48 01 d0             	add    %rdx,%rax
  401e6b:	48 c1 e0 02          	shl    $0x2,%rax
  401e6f:	48 01 c8             	add    %rcx,%rax
  401e72:	8b 40 04             	mov    0x4(%rax),%eax
  401e75:	39 45 a4             	cmp    %eax,-0x5c(%rbp)
  401e78:	75 48                	jne    401ec2 <threadwork+0x5aa>
  401e7a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e81:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401e87:	8d 50 01             	lea    0x1(%rax),%edx
  401e8a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e91:	89 90 90 03 00 00    	mov    %edx,0x390(%rax)
  401e97:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401e9e:	48 8b 88 48 03 00 00 	mov    0x348(%rax),%rcx
  401ea5:	8b 45 90             	mov    -0x70(%rbp),%eax
  401ea8:	48 63 d0             	movslq %eax,%rdx
  401eab:	48 89 d0             	mov    %rdx,%rax
  401eae:	48 01 c0             	add    %rax,%rax
  401eb1:	48 01 d0             	add    %rdx,%rax
  401eb4:	48 c1 e0 02          	shl    $0x2,%rax
  401eb8:	48 01 c8             	add    %rcx,%rax
  401ebb:	c7 40 04 00 00 00 00 	movl   $0x0,0x4(%rax)
  401ec2:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ec9:	8b 90 90 03 00 00    	mov    0x390(%rax),%edx
  401ecf:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ed6:	8b 80 8c 03 00 00    	mov    0x38c(%rax),%eax
  401edc:	39 c2                	cmp    %eax,%edx
  401ede:	75 1d                	jne    401efd <threadwork+0x5e5>
  401ee0:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ee7:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401eed:	8d 50 01             	lea    0x1(%rax),%edx
  401ef0:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401ef7:	89 90 90 03 00 00    	mov    %edx,0x390(%rax)
  401efd:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401f04:	8b 80 90 03 00 00    	mov    0x390(%rax),%eax
  401f0a:	83 f8 05             	cmp    $0x5,%eax
  401f0d:	75 11                	jne    401f20 <threadwork+0x608>
  401f0f:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401f16:	c7 80 90 03 00 00 01 00 00 00 	movl   $0x1,0x390(%rax)
  401f20:	83 45 94 01          	addl   $0x1,-0x6c(%rbp)
  401f24:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  401f2b:	8b 40 68             	mov    0x68(%rax),%eax
  401f2e:	83 e8 01             	sub    $0x1,%eax
  401f31:	39 45 94             	cmp    %eax,-0x6c(%rbp)
  401f34:	0f 8c 13 fd ff ff    	jl     401c4d <threadwork+0x335>
  401f3a:	90                   	nop
  401f3b:	48 8b 55 f8          	mov    -0x8(%rbp),%rdx
  401f3f:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401f48:	74 05                	je     401f4f <threadwork+0x637>
  401f4a:	e8 21 f1 ff ff       	call   401070 <__stack_chk_fail@plt>
  401f4f:	c9                   	leave
  401f50:	c3                   	ret

0000000000401f51 <work2>:
  401f51:	55                   	push   %rbp
  401f52:	48 89 e5             	mov    %rsp,%rbp
  401f55:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  401f59:	48 8b 45 e8          	mov    -0x18(%rbp),%rax
  401f5d:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  401f61:	eb 14                	jmp    401f77 <work2+0x26>
  401f63:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f67:	48 8b 40 48          	mov    0x48(%rax),%rax
  401f6b:	48 8d 50 01          	lea    0x1(%rax),%rdx
  401f6f:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f73:	48 89 50 48          	mov    %rdx,0x48(%rax)
  401f77:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  401f7b:	8b 40 5c             	mov    0x5c(%rax),%eax
  401f7e:	83 f8 01             	cmp    $0x1,%eax
  401f81:	74 e0                	je     401f63 <work2+0x12>
  401f83:	90                   	nop
  401f84:	5d                   	pop    %rbp
  401f85:	c3                   	ret

0000000000401f86 <work>:
  401f86:	55                   	push   %rbp
  401f87:	48 89 e5             	mov    %rsp,%rbp
  401f8a:	48 83 ec 50          	sub    $0x50,%rsp
  401f8e:	48 89 7d b8          	mov    %rdi,-0x48(%rbp)
  401f92:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  401f96:	48 89 45 e0          	mov    %rax,-0x20(%rbp)
  401f9a:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401f9e:	8b 40 64             	mov    0x64(%rax),%eax
  401fa1:	89 c6                	mov    %eax,%esi
  401fa3:	48 8d 05 72 20 00 00 	lea    0x2072(%rip),%rax        # 40401c <_IO_stdin_used+0x1c>
  401faa:	48 89 c7             	mov    %rax,%rdi
  401fad:	b8 00 00 00 00       	mov    $0x0,%eax
  401fb2:	e8 c9 f0 ff ff       	call   401080 <printf@plt>
  401fb7:	c7 45 c8 00 00 00 00 	movl   $0x0,-0x38(%rbp)
  401fbe:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fc2:	8b 40 64             	mov    0x64(%rax),%eax
  401fc5:	8d 50 01             	lea    0x1(%rax),%edx
  401fc8:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fcc:	8b 48 68             	mov    0x68(%rax),%ecx
  401fcf:	89 d0                	mov    %edx,%eax
  401fd1:	99                   	cltd
  401fd2:	f7 f9                	idiv   %ecx
  401fd4:	89 55 cc             	mov    %edx,-0x34(%rbp)
  401fd7:	c7 45 d0 00 00 00 00 	movl   $0x0,-0x30(%rbp)
  401fde:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  401fe2:	48 8b 80 b8 00 00 00 	mov    0xb8(%rax),%rax
  401fe9:	48 83 c0 01          	add    $0x1,%rax
  401fed:	be 08 00 00 00       	mov    $0x8,%esi
  401ff2:	48 89 c7             	mov    %rax,%rdi
  401ff5:	e8 d6 f0 ff ff       	call   4010d0 <calloc@plt>
  401ffa:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  401ffe:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402002:	8b 40 68             	mov    0x68(%rax),%eax
  402005:	48 98                	cltq
  402007:	be 04 00 00 00       	mov    $0x4,%esi
  40200c:	48 89 c7             	mov    %rax,%rdi
  40200f:	e8 bc f0 ff ff       	call   4010d0 <calloc@plt>
  402014:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
  402018:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  40201c:	8b 40 68             	mov    0x68(%rax),%eax
  40201f:	48 98                	cltq
  402021:	be 04 00 00 00       	mov    $0x4,%esi
  402026:	48 89 c7             	mov    %rax,%rdi
  402029:	e8 a2 f0 ff ff       	call   4010d0 <calloc@plt>
  40202e:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
  402032:	c7 45 d4 00 00 00 00 	movl   $0x0,-0x2c(%rbp)
  402039:	eb 25                	jmp    402060 <work+0xda>
  40203b:	c7 45 d8 00 00 00 00 	movl   $0x0,-0x28(%rbp)
  402042:	c7 45 dc 00 00 00 00 	movl   $0x0,-0x24(%rbp)
  402049:	c7 45 d4 00 00 00 00 	movl   $0x0,-0x2c(%rbp)
  402050:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402054:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402058:	48 89 c7             	mov    %rax,%rdi
  40205b:	e8 b8 f8 ff ff       	call   401918 <threadwork>
  402060:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  402064:	8b 40 5c             	mov    0x5c(%rax),%eax
  402067:	85 c0                	test   %eax,%eax
  402069:	7f d0                	jg     40203b <work+0xb5>
  40206b:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  40206f:	8b 40 64             	mov    0x64(%rax),%eax
  402072:	89 c6                	mov    %eax,%esi
  402074:	48 8d 05 b4 1f 00 00 	lea    0x1fb4(%rip),%rax        # 40402f <_IO_stdin_used+0x2f>
  40207b:	48 89 c7             	mov    %rax,%rdi
  40207e:	b8 00 00 00 00       	mov    $0x0,%eax
  402083:	e8 f8 ef ff ff       	call   401080 <printf@plt>
  402088:	90                   	nop
  402089:	c9                   	leave
  40208a:	c3                   	ret

000000000040208b <main>:
  40208b:	55                   	push   %rbp
  40208c:	48 89 e5             	mov    %rsp,%rbp
  40208f:	53                   	push   %rbx
  402090:	48 81 ec 78 01 00 00 	sub    $0x178,%rsp
  402097:	89 bd 8c fe ff ff    	mov    %edi,-0x174(%rbp)
  40209d:	48 89 b5 80 fe ff ff 	mov    %rsi,-0x180(%rbp)
  4020a4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4020ad:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
  4020b1:	31 c0                	xor    %eax,%eax
  4020b3:	c7 85 a0 fe ff ff 00 00 00 00 	movl   $0x0,-0x160(%rbp)
  4020bd:	c7 85 a4 fe ff ff 01 00 00 00 	movl   $0x1,-0x15c(%rbp)
  4020c7:	c7 85 94 fe ff ff 01 00 00 00 	movl   $0x1,-0x16c(%rbp)
  4020d1:	c7 85 98 fe ff ff 0f 00 00 00 	movl   $0xf,-0x168(%rbp)
  4020db:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4020e1:	83 e8 01             	sub    $0x1,%eax
  4020e4:	89 85 9c fe ff ff    	mov    %eax,-0x164(%rbp)
  4020ea:	be 08 00 00 00       	mov    $0x8,%esi
  4020ef:	48 8d 05 49 1f 00 00 	lea    0x1f49(%rip),%rax        # 40403f <_IO_stdin_used+0x3f>
  4020f6:	48 89 c7             	mov    %rax,%rdi
  4020f9:	b8 00 00 00 00       	mov    $0x0,%eax
  4020fe:	e8 7d ef ff ff       	call   401080 <printf@plt>
  402103:	be 04 00 00 00       	mov    $0x4,%esi
  402108:	48 8d 05 3e 1f 00 00 	lea    0x1f3e(%rip),%rax        # 40404d <_IO_stdin_used+0x4d>
  40210f:	48 89 c7             	mov    %rax,%rdi
  402112:	b8 00 00 00 00       	mov    $0x0,%eax
  402117:	e8 64 ef ff ff       	call   401080 <printf@plt>
  40211c:	be 20 00 00 00       	mov    $0x20,%esi
  402121:	48 8d 05 34 1f 00 00 	lea    0x1f34(%rip),%rax        # 40405c <_IO_stdin_used+0x5c>
  402128:	48 89 c7             	mov    %rax,%rdi
  40212b:	b8 00 00 00 00       	mov    $0x0,%eax
  402130:	e8 4b ef ff ff       	call   401080 <printf@plt>
  402135:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40213b:	89 c6                	mov    %eax,%esi
  40213d:	48 8d 05 2b 1f 00 00 	lea    0x1f2b(%rip),%rax        # 40406f <_IO_stdin_used+0x6f>
  402144:	48 89 c7             	mov    %rax,%rdi
  402147:	b8 00 00 00 00       	mov    $0x0,%eax
  40214c:	e8 2f ef ff ff       	call   401080 <printf@plt>
  402151:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402157:	48 98                	cltq
  402159:	be 08 00 00 00       	mov    $0x8,%esi
  40215e:	48 89 c7             	mov    %rax,%rdi
  402161:	e8 6a ef ff ff       	call   4010d0 <calloc@plt>
  402166:	48 89 85 18 ff ff ff 	mov    %rax,-0xe8(%rbp)
  40216d:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402173:	48 98                	cltq
  402175:	be 38 00 00 00       	mov    $0x38,%esi
  40217a:	48 89 c7             	mov    %rax,%rdi
  40217d:	e8 4e ef ff ff       	call   4010d0 <calloc@plt>
  402182:	48 89 85 f0 fe ff ff 	mov    %rax,-0x110(%rbp)
  402189:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40218f:	48 98                	cltq
  402191:	48 c1 e0 0a          	shl    $0xa,%rax
  402195:	48 89 c6             	mov    %rax,%rsi
  402198:	bf 01 00 00 00       	mov    $0x1,%edi
  40219d:	e8 2e ef ff ff       	call   4010d0 <calloc@plt>
  4021a2:	48 89 85 f8 fe ff ff 	mov    %rax,-0x108(%rbp)
  4021a9:	48 c7 85 00 ff ff ff 00 00 00 00 	movq   $0x0,-0x100(%rbp)
  4021b4:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
  4021b9:	48 89 85 08 ff ff ff 	mov    %rax,-0xf8(%rbp)
  4021c0:	8b 85 94 fe ff ff    	mov    -0x16c(%rbp),%eax
  4021c6:	48 98                	cltq
  4021c8:	48 8b 95 08 ff ff ff 	mov    -0xf8(%rbp),%rdx
  4021cf:	48 0f af c2          	imul   %rdx,%rax
  4021d3:	48 89 85 10 ff ff ff 	mov    %rax,-0xf0(%rbp)
  4021da:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4021e0:	48 63 d8             	movslq %eax,%rbx
  4021e3:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  4021ea:	48 99                	cqto
  4021ec:	48 f7 fb             	idiv   %rbx
  4021ef:	89 85 90 fe ff ff    	mov    %eax,-0x170(%rbp)
  4021f5:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4021f9:	f2 48 0f 2a 85 10 ff ff ff 	cvtsi2sdq -0xf0(%rbp),%xmm0
  402202:	66 0f ef c9          	pxor   %xmm1,%xmm1
  402206:	f2 48 0f 2a 8d 08 ff ff ff 	cvtsi2sdq -0xf8(%rbp),%xmm1
  40220f:	f2 0f 5e c1          	divsd  %xmm1,%xmm0
  402213:	66 48 0f 7e c0       	movq   %xmm0,%rax
  402218:	66 48 0f 6e c0       	movq   %rax,%xmm0
  40221d:	e8 fe ee ff ff       	call   401120 <ceil@plt>
  402222:	f2 48 0f 2c c0       	cvttsd2si %xmm0,%rax
  402227:	48 89 85 38 ff ff ff 	mov    %rax,-0xc8(%rbp)
  40222e:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  402235:	be 01 00 00 00       	mov    $0x1,%esi
  40223a:	48 89 c7             	mov    %rax,%rdi
  40223d:	e8 8e ee ff ff       	call   4010d0 <calloc@plt>
  402242:	48 89 85 40 ff ff ff 	mov    %rax,-0xc0(%rbp)
  402249:	48 8b 95 10 ff ff ff 	mov    -0xf0(%rbp),%rdx
  402250:	48 8b 85 40 ff ff ff 	mov    -0xc0(%rbp),%rax
  402257:	be ff ff ff ff       	mov    $0xffffffff,%esi
  40225c:	48 89 c7             	mov    %rax,%rdi
  40225f:	e8 5c ee ff ff       	call   4010c0 <memset@plt>
  402264:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  40226b:	48 89 c6             	mov    %rax,%rsi
  40226e:	48 8d 05 0f 1e 00 00 	lea    0x1e0f(%rip),%rax        # 404084 <_IO_stdin_used+0x84>
  402275:	48 89 c7             	mov    %rax,%rdi
  402278:	b8 00 00 00 00       	mov    $0x0,%eax
  40227d:	e8 fe ed ff ff       	call   401080 <printf@plt>
  402282:	c7 85 d4 fe ff ff 00 00 00 00 	movl   $0x0,-0x12c(%rbp)
  40228c:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402292:	48 98                	cltq
  402294:	be 04 00 00 00       	mov    $0x4,%esi
  402299:	48 89 c7             	mov    %rax,%rdi
  40229c:	e8 2f ee ff ff       	call   4010d0 <calloc@plt>
  4022a1:	48 89 85 48 ff ff ff 	mov    %rax,-0xb8(%rbp)
  4022a8:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4022ae:	48 98                	cltq
  4022b0:	be 04 00 00 00       	mov    $0x4,%esi
  4022b5:	48 89 c7             	mov    %rax,%rdi
  4022b8:	e8 13 ee ff ff       	call   4010d0 <calloc@plt>
  4022bd:	48 89 85 50 ff ff ff 	mov    %rax,-0xb0(%rbp)
  4022c4:	be 20 00 00 00       	mov    $0x20,%esi
  4022c9:	bf 64 00 00 00       	mov    $0x64,%edi
  4022ce:	e8 fd ed ff ff       	call   4010d0 <calloc@plt>
  4022d3:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)
  4022da:	48 8b 85 00 ff ff ff 	mov    -0x100(%rbp),%rax
  4022e1:	48 89 c6             	mov    %rax,%rsi
  4022e4:	48 8d 05 aa 1d 00 00 	lea    0x1daa(%rip),%rax        # 404095 <_IO_stdin_used+0x95>
  4022eb:	48 89 c7             	mov    %rax,%rdi
  4022ee:	b8 00 00 00 00       	mov    $0x0,%eax
  4022f3:	e8 88 ed ff ff       	call   401080 <printf@plt>
  4022f8:	48 8b 85 08 ff ff ff 	mov    -0xf8(%rbp),%rax
  4022ff:	48 89 c6             	mov    %rax,%rsi
  402302:	48 8d 05 98 1d 00 00 	lea    0x1d98(%rip),%rax        # 4040a1 <_IO_stdin_used+0xa1>
  402309:	48 89 c7             	mov    %rax,%rdi
  40230c:	b8 00 00 00 00       	mov    $0x0,%eax
  402311:	e8 6a ed ff ff       	call   401080 <printf@plt>
  402316:	c7 85 c4 fe ff ff 00 00 00 00 	movl   $0x0,-0x13c(%rbp)
  402320:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402326:	48 98                	cltq
  402328:	be 04 00 00 00       	mov    $0x4,%esi
  40232d:	48 89 c7             	mov    %rax,%rdi
  402330:	e8 9b ed ff ff       	call   4010d0 <calloc@plt>
  402335:	48 89 85 60 ff ff ff 	mov    %rax,-0xa0(%rbp)
  40233c:	48 8d 85 e0 fe ff ff 	lea    -0x120(%rbp),%rax
  402343:	ba 00 02 00 00       	mov    $0x200,%edx
  402348:	be 80 00 00 00       	mov    $0x80,%esi
  40234d:	48 89 c7             	mov    %rax,%rdi
  402350:	e8 ab ed ff ff       	call   401100 <posix_memalign@plt>
  402355:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40235b:	48 98                	cltq
  40235d:	be 0c 00 00 00       	mov    $0xc,%esi
  402362:	48 89 c7             	mov    %rax,%rdi
  402365:	e8 66 ed ff ff       	call   4010d0 <calloc@plt>
  40236a:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
  402371:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402378:	48 8b 95 40 ff ff ff 	mov    -0xc0(%rbp),%rdx
  40237f:	48 89 50 70          	mov    %rdx,0x70(%rax)
  402383:	c7 85 d8 fe ff ff 00 e1 f5 05 	movl   $0x5f5e100,-0x128(%rbp)
  40238d:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  402393:	48 98                	cltq
  402395:	be 14 00 00 00       	mov    $0x14,%esi
  40239a:	48 89 c7             	mov    %rax,%rdi
  40239d:	e8 2e ed ff ff       	call   4010d0 <calloc@plt>
  4023a2:	48 89 85 70 ff ff ff 	mov    %rax,-0x90(%rbp)
  4023a9:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  4023af:	48 98                	cltq
  4023b1:	be 14 00 00 00       	mov    $0x14,%esi
  4023b6:	48 89 c7             	mov    %rax,%rdi
  4023b9:	e8 12 ed ff ff       	call   4010d0 <calloc@plt>
  4023be:	48 89 85 78 ff ff ff 	mov    %rax,-0x88(%rbp)
  4023c5:	be 08 00 00 00       	mov    $0x8,%esi
  4023ca:	bf 01 00 00 00       	mov    $0x1,%edi
  4023cf:	e8 fc ec ff ff       	call   4010d0 <calloc@plt>
  4023d4:	48 89 45 80          	mov    %rax,-0x80(%rbp)
  4023d8:	c7 85 c8 fe ff ff 00 00 00 00 	movl   $0x0,-0x138(%rbp)
  4023e2:	e9 e8 06 00 00       	jmp    402acf <main+0xa44>
  4023e7:	be 20 00 00 00       	mov    $0x20,%esi
  4023ec:	bf 0a 00 00 00       	mov    $0xa,%edi
  4023f1:	e8 da ec ff ff       	call   4010d0 <calloc@plt>
  4023f6:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
  4023fa:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402400:	48 98                	cltq
  402402:	48 c1 e0 0a          	shl    $0xa,%rax
  402406:	48 89 c2             	mov    %rax,%rdx
  402409:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402410:	48 01 c2             	add    %rax,%rdx
  402413:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  402417:	48 89 82 c0 03 00 00 	mov    %rax,0x3c0(%rdx)
  40241e:	c7 85 cc fe ff ff 00 00 00 00 	movl   $0x0,-0x134(%rbp)
  402428:	e9 9e 00 00 00       	jmp    4024cb <main+0x440>
  40242d:	48 8d 45 d0          	lea    -0x30(%rbp),%rax
  402431:	ba 50 1f 00 00       	mov    $0x1f50,%edx
  402436:	be 10 00 00 00       	mov    $0x10,%esi
  40243b:	48 89 c7             	mov    %rax,%rdi
  40243e:	e8 bd ec ff ff       	call   401100 <posix_memalign@plt>
  402443:	be 04 00 00 00       	mov    $0x4,%esi
  402448:	bf 01 00 00 00       	mov    $0x1,%edi
  40244d:	e8 7e ec ff ff       	call   4010d0 <calloc@plt>
  402452:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
  402456:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  40245c:	48 98                	cltq
  40245e:	48 c1 e0 05          	shl    $0x5,%rax
  402462:	48 89 c2             	mov    %rax,%rdx
  402465:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  402469:	48 01 c2             	add    %rax,%rdx
  40246c:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  402470:	48 89 42 18          	mov    %rax,0x18(%rdx)
  402474:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
  402478:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  40247e:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  402484:	48 98                	cltq
  402486:	48 c1 e0 05          	shl    $0x5,%rax
  40248a:	48 89 c2             	mov    %rax,%rdx
  40248d:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  402491:	48 01 d0             	add    %rdx,%rax
  402494:	48 c7 c2 1d 12 40 00 	mov    $0x40121d,%rdx
  40249b:	48 89 50 10          	mov    %rdx,0x10(%rax)
  40249f:	48 8b 45 d0          	mov    -0x30(%rbp),%rax
  4024a3:	48 8d 90 50 1f 00 00 	lea    0x1f50(%rax),%rdx
  4024aa:	8b 85 cc fe ff ff    	mov    -0x134(%rbp),%eax
  4024b0:	48 98                	cltq
  4024b2:	48 c1 e0 05          	shl    $0x5,%rax
  4024b6:	48 89 c1             	mov    %rax,%rcx
  4024b9:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
  4024bd:	48 01 c8             	add    %rcx,%rax
  4024c0:	48 89 50 08          	mov    %rdx,0x8(%rax)
  4024c4:	83 85 cc fe ff ff 01 	addl   $0x1,-0x134(%rbp)
  4024cb:	83 bd cc fe ff ff 09 	cmpl   $0x9,-0x134(%rbp)
  4024d2:	0f 8e 55 ff ff ff    	jle    40242d <main+0x3a2>
  4024d8:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4024de:	48 98                	cltq
  4024e0:	48 c1 e0 0a          	shl    $0xa,%rax
  4024e4:	48 89 c2             	mov    %rax,%rdx
  4024e7:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4024ee:	48 01 c2             	add    %rax,%rdx
  4024f1:	48 8b 45 80          	mov    -0x80(%rbp),%rax
  4024f5:	48 89 82 c8 03 00 00 	mov    %rax,0x3c8(%rdx)
  4024fc:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402502:	48 98                	cltq
  402504:	48 c1 e0 0a          	shl    $0xa,%rax
  402508:	48 89 c2             	mov    %rax,%rdx
  40250b:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402512:	48 01 c2             	add    %rax,%rdx
  402515:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
  40251c:	48 89 82 a0 03 00 00 	mov    %rax,0x3a0(%rdx)
  402523:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402529:	48 98                	cltq
  40252b:	48 c1 e0 0a          	shl    $0xa,%rax
  40252f:	48 89 c2             	mov    %rax,%rdx
  402532:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402539:	48 01 c2             	add    %rax,%rdx
  40253c:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
  402543:	48 89 82 a8 03 00 00 	mov    %rax,0x3a8(%rdx)
  40254a:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402550:	48 98                	cltq
  402552:	48 c1 e0 0a          	shl    $0xa,%rax
  402556:	48 89 c2             	mov    %rax,%rdx
  402559:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402560:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  402564:	be 80 00 00 00       	mov    $0x80,%esi
  402569:	bf 01 00 00 00       	mov    $0x1,%edi
  40256e:	e8 5d eb ff ff       	call   4010d0 <calloc@plt>
  402573:	48 89 43 78          	mov    %rax,0x78(%rbx)
  402577:	83 85 c4 fe ff ff 01 	addl   $0x1,-0x13c(%rbp)
  40257e:	8b 85 c4 fe ff ff    	mov    -0x13c(%rbp),%eax
  402584:	48 98                	cltq
  402586:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  40258a:	48 81 7d b0 ff 03 00 00 	cmpq   $0x3ff,-0x50(%rbp)
  402592:	77 78                	ja     40260c <main+0x581>
  402594:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40259a:	48 98                	cltq
  40259c:	48 c1 e0 0a          	shl    $0xa,%rax
  4025a0:	48 89 c2             	mov    %rax,%rdx
  4025a3:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4025aa:	48 01 d0             	add    %rdx,%rax
  4025ad:	48 8b 40 78          	mov    0x78(%rax),%rax
  4025b1:	48 89 c1             	mov    %rax,%rcx
  4025b4:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
  4025b8:	48 c1 e8 06          	shr    $0x6,%rax
  4025bc:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4025c4:	48 01 ca             	add    %rcx,%rdx
  4025c7:	48 8b 32             	mov    (%rdx),%rsi
  4025ca:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
  4025ce:	83 e2 3f             	and    $0x3f,%edx
  4025d1:	bf 01 00 00 00       	mov    $0x1,%edi
  4025d6:	89 d1                	mov    %edx,%ecx
  4025d8:	48 d3 e7             	shl    %cl,%rdi
  4025db:	48 89 f9             	mov    %rdi,%rcx
  4025de:	8b 95 c8 fe ff ff    	mov    -0x138(%rbp),%edx
  4025e4:	48 63 d2             	movslq %edx,%rdx
  4025e7:	48 89 d7             	mov    %rdx,%rdi
  4025ea:	48 c1 e7 0a          	shl    $0xa,%rdi
  4025ee:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4025f5:	48 01 fa             	add    %rdi,%rdx
  4025f8:	48 8b 52 78          	mov    0x78(%rdx),%rdx
  4025fc:	48 c1 e0 03          	shl    $0x3,%rax
  402600:	48 01 d0             	add    %rdx,%rax
  402603:	48 09 ce             	or     %rcx,%rsi
  402606:	48 89 f2             	mov    %rsi,%rdx
  402609:	48 89 10             	mov    %rdx,(%rax)
  40260c:	8b 95 c4 fe ff ff    	mov    -0x13c(%rbp),%edx
  402612:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402618:	89 c6                	mov    %eax,%esi
  40261a:	48 8d 05 8f 1a 00 00 	lea    0x1a8f(%rip),%rax        # 4040b0 <_IO_stdin_used+0xb0>
  402621:	48 89 c7             	mov    %rax,%rdi
  402624:	b8 00 00 00 00       	mov    $0x0,%eax
  402629:	e8 52 ea ff ff       	call   401080 <printf@plt>
  40262e:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402634:	48 98                	cltq
  402636:	48 c1 e0 0a          	shl    $0xa,%rax
  40263a:	48 89 c2             	mov    %rax,%rdx
  40263d:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402644:	48 01 c2             	add    %rax,%rdx
  402647:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40264d:	0f af 85 90 fe ff ff 	imul   -0x170(%rbp),%eax
  402654:	89 82 98 00 00 00    	mov    %eax,0x98(%rdx)
  40265a:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402660:	48 98                	cltq
  402662:	48 c1 e0 0a          	shl    $0xa,%rax
  402666:	48 89 c2             	mov    %rax,%rdx
  402669:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402670:	48 01 c2             	add    %rax,%rdx
  402673:	48 8b 85 e0 fe ff ff 	mov    -0x120(%rbp),%rax
  40267a:	48 89 82 80 03 00 00 	mov    %rax,0x380(%rdx)
  402681:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402687:	48 98                	cltq
  402689:	48 c1 e0 0a          	shl    $0xa,%rax
  40268d:	48 89 c2             	mov    %rax,%rdx
  402690:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402697:	48 01 c2             	add    %rax,%rdx
  40269a:	8b 85 a0 fe ff ff    	mov    -0x160(%rbp),%eax
  4026a0:	89 82 80 00 00 00    	mov    %eax,0x80(%rdx)
  4026a6:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026ac:	48 98                	cltq
  4026ae:	48 c1 e0 0a          	shl    $0xa,%rax
  4026b2:	48 89 c2             	mov    %rax,%rdx
  4026b5:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026bc:	48 01 d0             	add    %rdx,%rax
  4026bf:	c7 40 5c 02 00 00 00 	movl   $0x2,0x5c(%rax)
  4026c6:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026cc:	48 98                	cltq
  4026ce:	48 c1 e0 0a          	shl    $0xa,%rax
  4026d2:	48 89 c2             	mov    %rax,%rdx
  4026d5:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026dc:	48 01 c2             	add    %rax,%rdx
  4026df:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026e5:	89 42 64             	mov    %eax,0x64(%rdx)
  4026e8:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4026ee:	48 98                	cltq
  4026f0:	48 c1 e0 0a          	shl    $0xa,%rax
  4026f4:	48 89 c2             	mov    %rax,%rdx
  4026f7:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4026fe:	48 01 d0             	add    %rdx,%rax
  402701:	48 8b 95 10 ff ff ff 	mov    -0xf0(%rbp),%rdx
  402708:	89 50 60             	mov    %edx,0x60(%rax)
  40270b:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402711:	48 98                	cltq
  402713:	48 c1 e0 0a          	shl    $0xa,%rax
  402717:	48 89 c2             	mov    %rax,%rdx
  40271a:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402721:	48 01 c2             	add    %rax,%rdx
  402724:	8b 85 90 fe ff ff    	mov    -0x170(%rbp),%eax
  40272a:	89 82 94 00 00 00    	mov    %eax,0x94(%rdx)
  402730:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402736:	48 98                	cltq
  402738:	48 c1 e0 0a          	shl    $0xa,%rax
  40273c:	48 89 c2             	mov    %rax,%rdx
  40273f:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402746:	48 01 c2             	add    %rax,%rdx
  402749:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40274f:	89 42 68             	mov    %eax,0x68(%rdx)
  402752:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402758:	48 98                	cltq
  40275a:	48 c1 e0 0a          	shl    $0xa,%rax
  40275e:	48 89 c2             	mov    %rax,%rdx
  402761:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402768:	48 01 c2             	add    %rax,%rdx
  40276b:	48 8b 85 60 ff ff ff 	mov    -0xa0(%rbp),%rax
  402772:	48 89 42 20          	mov    %rax,0x20(%rdx)
  402776:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40277c:	48 98                	cltq
  40277e:	48 c1 e0 0a          	shl    $0xa,%rax
  402782:	48 89 c2             	mov    %rax,%rdx
  402785:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40278c:	48 01 d0             	add    %rdx,%rax
  40278f:	48 8b 50 20          	mov    0x20(%rax),%rdx
  402793:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402799:	48 98                	cltq
  40279b:	48 c1 e0 02          	shl    $0x2,%rax
  40279f:	48 01 d0             	add    %rdx,%rax
  4027a2:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
  4027a8:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027ae:	48 98                	cltq
  4027b0:	48 c1 e0 0a          	shl    $0xa,%rax
  4027b4:	48 89 c2             	mov    %rax,%rdx
  4027b7:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027be:	48 01 c2             	add    %rax,%rdx
  4027c1:	8b 85 90 fe ff ff    	mov    -0x170(%rbp),%eax
  4027c7:	89 82 90 00 00 00    	mov    %eax,0x90(%rdx)
  4027cd:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027d3:	48 98                	cltq
  4027d5:	48 c1 e0 0a          	shl    $0xa,%rax
  4027d9:	48 89 c2             	mov    %rax,%rdx
  4027dc:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027e3:	48 01 c2             	add    %rax,%rdx
  4027e6:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4027ed:	48 89 42 28          	mov    %rax,0x28(%rdx)
  4027f1:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4027f7:	48 98                	cltq
  4027f9:	48 c1 e0 0a          	shl    $0xa,%rax
  4027fd:	48 89 c2             	mov    %rax,%rdx
  402800:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402807:	48 01 c2             	add    %rax,%rdx
  40280a:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402811:	48 89 42 30          	mov    %rax,0x30(%rdx)
  402815:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40281b:	48 98                	cltq
  40281d:	48 c1 e0 0a          	shl    $0xa,%rax
  402821:	48 89 c2             	mov    %rax,%rdx
  402824:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40282b:	48 01 d0             	add    %rdx,%rax
  40282e:	48 c7 00 00 00 00 00 	movq   $0x0,(%rax)
  402835:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40283b:	48 98                	cltq
  40283d:	48 c1 e0 0a          	shl    $0xa,%rax
  402841:	48 89 c2             	mov    %rax,%rdx
  402844:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40284b:	48 01 c2             	add    %rax,%rdx
  40284e:	48 8b 85 10 ff ff ff 	mov    -0xf0(%rbp),%rax
  402855:	48 89 42 08          	mov    %rax,0x8(%rdx)
  402859:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40285f:	48 98                	cltq
  402861:	48 c1 e0 0a          	shl    $0xa,%rax
  402865:	48 89 c2             	mov    %rax,%rdx
  402868:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40286f:	48 01 d0             	add    %rdx,%rax
  402872:	8b 95 98 fe ff ff    	mov    -0x168(%rbp),%edx
  402878:	83 ea 01             	sub    $0x1,%edx
  40287b:	89 90 00 02 00 00    	mov    %edx,0x200(%rax)
  402881:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402887:	48 98                	cltq
  402889:	48 c1 e0 0a          	shl    $0xa,%rax
  40288d:	48 89 c2             	mov    %rax,%rdx
  402890:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402897:	48 01 d0             	add    %rdx,%rax
  40289a:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
  4028a4:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028aa:	48 98                	cltq
  4028ac:	48 c1 e0 0a          	shl    $0xa,%rax
  4028b0:	48 89 c2             	mov    %rax,%rdx
  4028b3:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4028ba:	48 01 c2             	add    %rax,%rdx
  4028bd:	48 8b 85 58 ff ff ff 	mov    -0xa8(%rbp),%rax
  4028c4:	48 89 82 a0 00 00 00 	mov    %rax,0xa0(%rdx)
  4028cb:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028d1:	48 98                	cltq
  4028d3:	48 c1 e0 0a          	shl    $0xa,%rax
  4028d7:	48 89 c2             	mov    %rax,%rdx
  4028da:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4028e1:	48 01 c2             	add    %rax,%rdx
  4028e4:	48 8b 85 38 ff ff ff 	mov    -0xc8(%rbp),%rax
  4028eb:	48 89 82 c0 00 00 00 	mov    %rax,0xc0(%rdx)
  4028f2:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4028f8:	48 98                	cltq
  4028fa:	48 c1 e0 0a          	shl    $0xa,%rax
  4028fe:	48 89 c2             	mov    %rax,%rdx
  402901:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402908:	48 01 c2             	add    %rax,%rdx
  40290b:	48 8b 85 08 ff ff ff 	mov    -0xf8(%rbp),%rax
  402912:	48 89 82 b8 00 00 00 	mov    %rax,0xb8(%rdx)
  402919:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40291f:	48 98                	cltq
  402921:	48 c1 e0 0a          	shl    $0xa,%rax
  402925:	48 89 c2             	mov    %rax,%rdx
  402928:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40292f:	48 01 d0             	add    %rdx,%rax
  402932:	c7 80 c8 00 00 00 00 00 00 00 	movl   $0x0,0xc8(%rax)
  40293c:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402942:	48 98                	cltq
  402944:	48 c1 e0 0a          	shl    $0xa,%rax
  402948:	48 89 c2             	mov    %rax,%rdx
  40294b:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402952:	48 01 c2             	add    %rax,%rdx
  402955:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  40295b:	48 98                	cltq
  40295d:	48 89 82 08 03 00 00 	mov    %rax,0x308(%rdx)
  402964:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  40296a:	48 98                	cltq
  40296c:	48 c1 e0 0a          	shl    $0xa,%rax
  402970:	48 89 c2             	mov    %rax,%rdx
  402973:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40297a:	48 01 c2             	add    %rax,%rdx
  40297d:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  402983:	48 98                	cltq
  402985:	48 89 82 10 03 00 00 	mov    %rax,0x310(%rdx)
  40298c:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402992:	8d 50 03             	lea    0x3(%rax),%edx
  402995:	85 c0                	test   %eax,%eax
  402997:	0f 48 c2             	cmovs  %edx,%eax
  40299a:	c1 f8 02             	sar    $0x2,%eax
  40299d:	89 c2                	mov    %eax,%edx
  40299f:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4029a5:	48 98                	cltq
  4029a7:	48 c1 e0 0a          	shl    $0xa,%rax
  4029ab:	48 89 c1             	mov    %rax,%rcx
  4029ae:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4029b5:	48 01 c8             	add    %rcx,%rax
  4029b8:	83 c2 01             	add    $0x1,%edx
  4029bb:	89 90 8c 03 00 00    	mov    %edx,0x38c(%rax)
  4029c1:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  4029c7:	48 98                	cltq
  4029c9:	48 c1 e0 0a          	shl    $0xa,%rax
  4029cd:	48 89 c2             	mov    %rax,%rdx
  4029d0:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4029d7:	48 01 c2             	add    %rax,%rdx
  4029da:	8b 85 98 fe ff ff    	mov    -0x168(%rbp),%eax
  4029e0:	89 82 28 03 00 00    	mov    %eax,0x328(%rdx)
  4029e6:	c7 85 dc fe ff ff 80 96 98 00 	movl   $0x989680,-0x124(%rbp)
  4029f0:	8b 85 dc fe ff ff    	mov    -0x124(%rbp),%eax
  4029f6:	48 98                	cltq
  4029f8:	8b 95 c8 fe ff ff    	mov    -0x138(%rbp),%edx
  4029fe:	48 63 d2             	movslq %edx,%rdx
  402a01:	48 89 d1             	mov    %rdx,%rcx
  402a04:	48 c1 e1 0a          	shl    $0xa,%rcx
  402a08:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  402a0f:	48 8d 1c 11          	lea    (%rcx,%rdx,1),%rbx
  402a13:	be 30 00 00 00       	mov    $0x30,%esi
  402a18:	48 89 c7             	mov    %rax,%rdi
  402a1b:	e8 b0 e6 ff ff       	call   4010d0 <calloc@plt>
  402a20:	48 89 83 18 03 00 00 	mov    %rax,0x318(%rbx)
  402a27:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a2d:	48 98                	cltq
  402a2f:	48 c1 e0 0a          	shl    $0xa,%rax
  402a33:	48 89 c2             	mov    %rax,%rdx
  402a36:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a3d:	48 01 c2             	add    %rax,%rdx
  402a40:	8b 85 dc fe ff ff    	mov    -0x124(%rbp),%eax
  402a46:	89 82 20 03 00 00    	mov    %eax,0x320(%rdx)
  402a4c:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a52:	48 98                	cltq
  402a54:	48 c1 e0 0a          	shl    $0xa,%rax
  402a58:	48 89 c2             	mov    %rax,%rdx
  402a5b:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a62:	48 01 c2             	add    %rax,%rdx
  402a65:	48 8b 85 68 ff ff ff 	mov    -0x98(%rbp),%rax
  402a6c:	48 89 82 48 03 00 00 	mov    %rax,0x348(%rdx)
  402a73:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402a79:	48 98                	cltq
  402a7b:	48 c1 e0 0a          	shl    $0xa,%rax
  402a7f:	48 89 c2             	mov    %rax,%rdx
  402a82:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402a89:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  402a8d:	be 30 00 00 00       	mov    $0x30,%esi
  402a92:	bf 10 27 00 00       	mov    $0x2710,%edi
  402a97:	e8 34 e6 ff ff       	call   4010d0 <calloc@plt>
  402a9c:	48 89 83 30 03 00 00 	mov    %rax,0x330(%rbx)
  402aa3:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402aa9:	48 98                	cltq
  402aab:	48 c1 e0 0a          	shl    $0xa,%rax
  402aaf:	48 89 c2             	mov    %rax,%rdx
  402ab2:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402ab9:	48 01 c2             	add    %rax,%rdx
  402abc:	8b 85 d8 fe ff ff    	mov    -0x128(%rbp),%eax
  402ac2:	89 82 b8 03 00 00    	mov    %eax,0x3b8(%rdx)
  402ac8:	83 85 c8 fe ff ff 01 	addl   $0x1,-0x138(%rbp)
  402acf:	8b 85 c8 fe ff ff    	mov    -0x138(%rbp),%eax
  402ad5:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402adb:	0f 8c 06 f9 ff ff    	jl     4023e7 <main+0x35c>
  402ae1:	c7 85 d0 fe ff ff 00 00 00 00 	movl   $0x0,-0x130(%rbp)
  402aeb:	e9 b8 00 00 00       	jmp    402ba8 <main+0xb1d>
  402af0:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402af6:	48 98                	cltq
  402af8:	48 c1 e0 0a          	shl    $0xa,%rax
  402afc:	48 89 c2             	mov    %rax,%rdx
  402aff:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402b06:	48 01 c2             	add    %rax,%rdx
  402b09:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b0f:	48 63 c8             	movslq %eax,%rcx
  402b12:	48 89 c8             	mov    %rcx,%rax
  402b15:	48 c1 e0 03          	shl    $0x3,%rax
  402b19:	48 29 c8             	sub    %rcx,%rax
  402b1c:	48 c1 e0 03          	shl    $0x3,%rax
  402b20:	48 89 c1             	mov    %rax,%rcx
  402b23:	48 8b 85 f0 fe ff ff 	mov    -0x110(%rbp),%rax
  402b2a:	48 8d 34 01          	lea    (%rcx,%rax,1),%rsi
  402b2e:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b34:	48 98                	cltq
  402b36:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
  402b3e:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402b45:	48 01 c8             	add    %rcx,%rax
  402b48:	48 89 d1             	mov    %rdx,%rcx
  402b4b:	48 c7 c2 86 1f 40 00 	mov    $0x401f86,%rdx
  402b52:	48 89 c7             	mov    %rax,%rdi
  402b55:	e8 86 e5 ff ff       	call   4010e0 <pthread_create@plt>
  402b5a:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b60:	48 98                	cltq
  402b62:	48 c1 e0 0a          	shl    $0xa,%rax
  402b66:	48 89 c2             	mov    %rax,%rdx
  402b69:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402b70:	48 01 d0             	add    %rdx,%rax
  402b73:	48 8b 50 78          	mov    0x78(%rax),%rdx
  402b77:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402b7d:	48 98                	cltq
  402b7f:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
  402b87:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402b8e:	48 01 c8             	add    %rcx,%rax
  402b91:	48 8b 00             	mov    (%rax),%rax
  402b94:	be 08 00 00 00       	mov    $0x8,%esi
  402b99:	48 89 c7             	mov    %rax,%rdi
  402b9c:	e8 8f e4 ff ff       	call   401030 <pthread_setaffinity_np@plt>
  402ba1:	83 85 d0 fe ff ff 01 	addl   $0x1,-0x130(%rbp)
  402ba8:	8b 85 d0 fe ff ff    	mov    -0x130(%rbp),%eax
  402bae:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402bb4:	0f 8c 36 ff ff ff    	jl     402af0 <main+0xa65>
  402bba:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402bc0:	48 98                	cltq
  402bc2:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
  402bc6:	48 c7 45 c8 00 00 00 00 	movq   $0x0,-0x38(%rbp)
  402bce:	48 c7 45 d0 00 00 00 00 	movq   $0x0,-0x30(%rbp)
  402bd6:	48 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%rbp)
  402bde:	48 8d 55 d0          	lea    -0x30(%rbp),%rdx
  402be2:	48 8d 45 c0          	lea    -0x40(%rbp),%rax
  402be6:	48 89 d6             	mov    %rdx,%rsi
  402be9:	48 89 c7             	mov    %rax,%rdi
  402bec:	e8 af e4 ff ff       	call   4010a0 <nanosleep@plt>
  402bf1:	48 8d 05 d7 14 00 00 	lea    0x14d7(%rip),%rax        # 4040cf <_IO_stdin_used+0xcf>
  402bf8:	48 89 c7             	mov    %rax,%rdi
  402bfb:	e8 40 e4 ff ff       	call   401040 <puts@plt>
  402c00:	c7 85 b8 fe ff ff 00 00 00 00 	movl   $0x0,-0x148(%rbp)
  402c0a:	eb 29                	jmp    402c35 <main+0xbaa>
  402c0c:	8b 85 b8 fe ff ff    	mov    -0x148(%rbp),%eax
  402c12:	48 98                	cltq
  402c14:	48 c1 e0 0a          	shl    $0xa,%rax
  402c18:	48 89 c2             	mov    %rax,%rdx
  402c1b:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402c22:	48 01 d0             	add    %rdx,%rax
  402c25:	8b 50 5c             	mov    0x5c(%rax),%edx
  402c28:	83 ea 01             	sub    $0x1,%edx
  402c2b:	89 50 5c             	mov    %edx,0x5c(%rax)
  402c2e:	83 85 b8 fe ff ff 01 	addl   $0x1,-0x148(%rbp)
  402c35:	8b 85 b8 fe ff ff    	mov    -0x148(%rbp),%eax
  402c3b:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402c41:	7c c9                	jl     402c0c <main+0xb81>
  402c43:	48 8d 05 8f 14 00 00 	lea    0x148f(%rip),%rax        # 4040d9 <_IO_stdin_used+0xd9>
  402c4a:	48 89 c7             	mov    %rax,%rdi
  402c4d:	e8 ee e3 ff ff       	call   401040 <puts@plt>
  402c52:	c7 85 bc fe ff ff 00 00 00 00 	movl   $0x0,-0x144(%rbp)
  402c5c:	eb 29                	jmp    402c87 <main+0xbfc>
  402c5e:	8b 85 bc fe ff ff    	mov    -0x144(%rbp),%eax
  402c64:	48 98                	cltq
  402c66:	48 c1 e0 0a          	shl    $0xa,%rax
  402c6a:	48 89 c2             	mov    %rax,%rdx
  402c6d:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402c74:	48 01 d0             	add    %rdx,%rax
  402c77:	8b 50 5c             	mov    0x5c(%rax),%edx
  402c7a:	83 ea 01             	sub    $0x1,%edx
  402c7d:	89 50 5c             	mov    %edx,0x5c(%rax)
  402c80:	83 85 bc fe ff ff 01 	addl   $0x1,-0x144(%rbp)
  402c87:	8b 85 bc fe ff ff    	mov    -0x144(%rbp),%eax
  402c8d:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402c93:	7c c9                	jl     402c5e <main+0xbd3>
  402c95:	c7 85 c0 fe ff ff 00 00 00 00 	movl   $0x0,-0x140(%rbp)
  402c9f:	eb 36                	jmp    402cd7 <main+0xc4c>
  402ca1:	8b 85 c0 fe ff ff    	mov    -0x140(%rbp),%eax
  402ca7:	48 98                	cltq
  402ca9:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  402cb1:	48 8b 85 18 ff ff ff 	mov    -0xe8(%rbp),%rax
  402cb8:	48 01 d0             	add    %rdx,%rax
  402cbb:	48 8b 00             	mov    (%rax),%rax
  402cbe:	48 8d 95 e8 fe ff ff 	lea    -0x118(%rbp),%rdx
  402cc5:	48 89 d6             	mov    %rdx,%rsi
  402cc8:	48 89 c7             	mov    %rax,%rdi
  402ccb:	e8 40 e4 ff ff       	call   401110 <pthread_join@plt>
  402cd0:	83 85 c0 fe ff ff 01 	addl   $0x1,-0x140(%rbp)
  402cd7:	8b 85 c0 fe ff ff    	mov    -0x140(%rbp),%eax
  402cdd:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402ce3:	7c bc                	jl     402ca1 <main+0xc16>
  402ce5:	48 8d 05 f6 13 00 00 	lea    0x13f6(%rip),%rax        # 4040e2 <_IO_stdin_used+0xe2>
  402cec:	48 89 c7             	mov    %rax,%rdi
  402cef:	e8 4c e3 ff ff       	call   401040 <puts@plt>
  402cf4:	48 c7 85 20 ff ff ff 00 00 00 00 	movq   $0x0,-0xe0(%rbp)
  402cff:	48 c7 45 88 01 00 00 00 	movq   $0x1,-0x78(%rbp)
  402d07:	c7 85 a8 fe ff ff 00 00 00 00 	movl   $0x0,-0x158(%rbp)
  402d11:	eb 5f                	jmp    402d72 <main+0xce7>
  402d13:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d19:	48 98                	cltq
  402d1b:	48 c1 e0 0a          	shl    $0xa,%rax
  402d1f:	48 89 c2             	mov    %rax,%rdx
  402d22:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402d29:	48 01 d0             	add    %rdx,%rax
  402d2c:	48 8b 40 48          	mov    0x48(%rax),%rax
  402d30:	48 89 c6             	mov    %rax,%rsi
  402d33:	48 8d 05 bd 13 00 00 	lea    0x13bd(%rip),%rax        # 4040f7 <_IO_stdin_used+0xf7>
  402d3a:	48 89 c7             	mov    %rax,%rdi
  402d3d:	b8 00 00 00 00       	mov    $0x0,%eax
  402d42:	e8 39 e3 ff ff       	call   401080 <printf@plt>
  402d47:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d4d:	48 98                	cltq
  402d4f:	48 c1 e0 0a          	shl    $0xa,%rax
  402d53:	48 89 c2             	mov    %rax,%rdx
  402d56:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402d5d:	48 01 d0             	add    %rdx,%rax
  402d60:	48 8b 40 48          	mov    0x48(%rax),%rax
  402d64:	48 01 85 20 ff ff ff 	add    %rax,-0xe0(%rbp)
  402d6b:	83 85 a8 fe ff ff 01 	addl   $0x1,-0x158(%rbp)
  402d72:	8b 85 a8 fe ff ff    	mov    -0x158(%rbp),%eax
  402d78:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402d7e:	7c 93                	jl     402d13 <main+0xc88>
  402d80:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402d86:	48 63 d8             	movslq %eax,%rbx
  402d89:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402d90:	48 99                	cqto
  402d92:	48 f7 fb             	idiv   %rbx
  402d95:	48 89 c6             	mov    %rax,%rsi
  402d98:	48 8d 05 63 13 00 00 	lea    0x1363(%rip),%rax        # 404102 <_IO_stdin_used+0x102>
  402d9f:	48 89 c7             	mov    %rax,%rdi
  402da2:	b8 00 00 00 00       	mov    $0x0,%eax
  402da7:	e8 d4 e2 ff ff       	call   401080 <printf@plt>
  402dac:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402db3:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  402db8:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402dbe:	48 63 da             	movslq %edx,%rbx
  402dc1:	48 99                	cqto
  402dc3:	48 f7 fb             	idiv   %rbx
  402dc6:	48 89 c6             	mov    %rax,%rsi
  402dc9:	48 8d 05 3d 13 00 00 	lea    0x133d(%rip),%rax        # 40410d <_IO_stdin_used+0x10d>
  402dd0:	48 89 c7             	mov    %rax,%rdi
  402dd3:	b8 00 00 00 00       	mov    $0x0,%eax
  402dd8:	e8 a3 e2 ff ff       	call   401080 <printf@plt>
  402ddd:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402de3:	48 63 d8             	movslq %eax,%rbx
  402de6:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402ded:	48 99                	cqto
  402def:	48 f7 fb             	idiv   %rbx
  402df2:	48 89 c3             	mov    %rax,%rbx
  402df5:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402dfa:	48 99                	cqto
  402dfc:	48 f7 fb             	idiv   %rbx
  402dff:	48 89 c6             	mov    %rax,%rsi
  402e02:	48 8d 05 12 13 00 00 	lea    0x1312(%rip),%rax        # 40411b <_IO_stdin_used+0x11b>
  402e09:	48 89 c7             	mov    %rax,%rdi
  402e0c:	b8 00 00 00 00       	mov    $0x0,%eax
  402e11:	e8 6a e2 ff ff       	call   401080 <printf@plt>
  402e16:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402e1c:	48 63 d8             	movslq %eax,%rbx
  402e1f:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402e26:	48 99                	cqto
  402e28:	48 f7 fb             	idiv   %rbx
  402e2b:	48 89 c3             	mov    %rax,%rbx
  402e2e:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402e33:	48 99                	cqto
  402e35:	48 f7 fb             	idiv   %rbx
  402e38:	48 99                	cqto
  402e3a:	48 f7 7d 88          	idivq  -0x78(%rbp)
  402e3e:	48 89 c6             	mov    %rax,%rsi
  402e41:	48 8d 05 e7 12 00 00 	lea    0x12e7(%rip),%rax        # 40412f <_IO_stdin_used+0x12f>
  402e48:	48 89 c7             	mov    %rax,%rdi
  402e4b:	b8 00 00 00 00       	mov    $0x0,%eax
  402e50:	e8 2b e2 ff ff       	call   401080 <printf@plt>
  402e55:	48 8b 85 20 ff ff ff 	mov    -0xe0(%rbp),%rax
  402e5c:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  402e61:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402e67:	48 63 da             	movslq %edx,%rbx
  402e6a:	48 99                	cqto
  402e6c:	48 f7 fb             	idiv   %rbx
  402e6f:	48 89 c3             	mov    %rax,%rbx
  402e72:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  402e77:	48 99                	cqto
  402e79:	48 f7 fb             	idiv   %rbx
  402e7c:	48 89 c6             	mov    %rax,%rsi
  402e7f:	48 8d 05 c7 12 00 00 	lea    0x12c7(%rip),%rax        # 40414d <_IO_stdin_used+0x14d>
  402e86:	48 89 c7             	mov    %rax,%rdi
  402e89:	b8 00 00 00 00       	mov    $0x0,%eax
  402e8e:	e8 ed e1 ff ff       	call   401080 <printf@plt>
  402e93:	48 c7 85 28 ff ff ff 00 00 00 00 	movq   $0x0,-0xd8(%rbp)
  402e9e:	c7 85 ac fe ff ff 00 00 00 00 	movl   $0x0,-0x154(%rbp)
  402ea8:	eb 65                	jmp    402f0f <main+0xe84>
  402eaa:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402eb0:	48 98                	cltq
  402eb2:	48 c1 e0 0a          	shl    $0xa,%rax
  402eb6:	48 89 c2             	mov    %rax,%rdx
  402eb9:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402ec0:	48 01 d0             	add    %rdx,%rax
  402ec3:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  402eca:	48 89 c6             	mov    %rax,%rsi
  402ecd:	48 8d 05 8c 12 00 00 	lea    0x128c(%rip),%rax        # 404160 <_IO_stdin_used+0x160>
  402ed4:	48 89 c7             	mov    %rax,%rdi
  402ed7:	b8 00 00 00 00       	mov    $0x0,%eax
  402edc:	e8 9f e1 ff ff       	call   401080 <printf@plt>
  402ee1:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402ee7:	48 98                	cltq
  402ee9:	48 c1 e0 0a          	shl    $0xa,%rax
  402eed:	48 89 c2             	mov    %rax,%rdx
  402ef0:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402ef7:	48 01 d0             	add    %rdx,%rax
  402efa:	48 8b 80 98 03 00 00 	mov    0x398(%rax),%rax
  402f01:	48 01 85 28 ff ff ff 	add    %rax,-0xd8(%rbp)
  402f08:	83 85 ac fe ff ff 01 	addl   $0x1,-0x154(%rbp)
  402f0f:	8b 85 ac fe ff ff    	mov    -0x154(%rbp),%eax
  402f15:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402f1b:	7c 8d                	jl     402eaa <main+0xe1f>
  402f1d:	48 c7 85 30 ff ff ff 00 00 00 00 	movq   $0x0,-0xd0(%rbp)
  402f28:	c7 85 b0 fe ff ff 00 00 00 00 	movl   $0x0,-0x150(%rbp)
  402f32:	eb 5f                	jmp    402f93 <main+0xf08>
  402f34:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f3a:	48 98                	cltq
  402f3c:	48 c1 e0 0a          	shl    $0xa,%rax
  402f40:	48 89 c2             	mov    %rax,%rdx
  402f43:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402f4a:	48 01 d0             	add    %rdx,%rax
  402f4d:	48 8b 40 50          	mov    0x50(%rax),%rax
  402f51:	48 01 85 30 ff ff ff 	add    %rax,-0xd0(%rbp)
  402f58:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f5e:	48 98                	cltq
  402f60:	48 c1 e0 0a          	shl    $0xa,%rax
  402f64:	48 89 c2             	mov    %rax,%rdx
  402f67:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  402f6e:	48 01 d0             	add    %rdx,%rax
  402f71:	48 8b 40 50          	mov    0x50(%rax),%rax
  402f75:	48 89 c6             	mov    %rax,%rsi
  402f78:	48 8d 05 f3 11 00 00 	lea    0x11f3(%rip),%rax        # 404172 <_IO_stdin_used+0x172>
  402f7f:	48 89 c7             	mov    %rax,%rdi
  402f82:	b8 00 00 00 00       	mov    $0x0,%eax
  402f87:	e8 f4 e0 ff ff       	call   401080 <printf@plt>
  402f8c:	83 85 b0 fe ff ff 01 	addl   $0x1,-0x150(%rbp)
  402f93:	8b 85 b0 fe ff ff    	mov    -0x150(%rbp),%eax
  402f99:	3b 85 98 fe ff ff    	cmp    -0x168(%rbp),%eax
  402f9f:	7c 93                	jl     402f34 <main+0xea9>
  402fa1:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  402fa7:	48 63 d8             	movslq %eax,%rbx
  402faa:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402fb1:	48 99                	cqto
  402fb3:	48 f7 fb             	idiv   %rbx
  402fb6:	48 89 c6             	mov    %rax,%rsi
  402fb9:	48 8d 05 be 11 00 00 	lea    0x11be(%rip),%rax        # 40417e <_IO_stdin_used+0x17e>
  402fc0:	48 89 c7             	mov    %rax,%rdi
  402fc3:	b8 00 00 00 00       	mov    $0x0,%eax
  402fc8:	e8 b3 e0 ff ff       	call   401080 <printf@plt>
  402fcd:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  402fd4:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  402fd9:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  402fdf:	48 63 da             	movslq %edx,%rbx
  402fe2:	48 99                	cqto
  402fe4:	48 f7 fb             	idiv   %rbx
  402fe7:	48 89 c6             	mov    %rax,%rsi
  402fea:	48 8d 05 9f 11 00 00 	lea    0x119f(%rip),%rax        # 404190 <_IO_stdin_used+0x190>
  402ff1:	48 89 c7             	mov    %rax,%rdi
  402ff4:	b8 00 00 00 00       	mov    $0x0,%eax
  402ff9:	e8 82 e0 ff ff       	call   401080 <printf@plt>
  402ffe:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  403004:	48 63 d8             	movslq %eax,%rbx
  403007:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  40300e:	48 99                	cqto
  403010:	48 f7 fb             	idiv   %rbx
  403013:	48 89 c3             	mov    %rax,%rbx
  403016:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40301b:	48 99                	cqto
  40301d:	48 f7 fb             	idiv   %rbx
  403020:	48 89 c6             	mov    %rax,%rsi
  403023:	48 8d 05 7e 11 00 00 	lea    0x117e(%rip),%rax        # 4041a8 <_IO_stdin_used+0x1a8>
  40302a:	48 89 c7             	mov    %rax,%rdi
  40302d:	b8 00 00 00 00       	mov    $0x0,%eax
  403032:	e8 49 e0 ff ff       	call   401080 <printf@plt>
  403037:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  40303d:	48 63 d8             	movslq %eax,%rbx
  403040:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  403047:	48 99                	cqto
  403049:	48 f7 fb             	idiv   %rbx
  40304c:	48 89 c3             	mov    %rax,%rbx
  40304f:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  403054:	48 99                	cqto
  403056:	48 f7 fb             	idiv   %rbx
  403059:	48 99                	cqto
  40305b:	48 f7 7d 88          	idivq  -0x78(%rbp)
  40305f:	48 89 c6             	mov    %rax,%rsi
  403062:	48 8d 05 5f 11 00 00 	lea    0x115f(%rip),%rax        # 4041c8 <_IO_stdin_used+0x1c8>
  403069:	48 89 c7             	mov    %rax,%rdi
  40306c:	b8 00 00 00 00       	mov    $0x0,%eax
  403071:	e8 0a e0 ff ff       	call   401080 <printf@plt>
  403076:	48 8b 85 30 ff ff ff 	mov    -0xd0(%rbp),%rax
  40307d:	48 0f af 45 88       	imul   -0x78(%rbp),%rax
  403082:	8b 95 a4 fe ff ff    	mov    -0x15c(%rbp),%edx
  403088:	48 63 da             	movslq %edx,%rbx
  40308b:	48 99                	cqto
  40308d:	48 f7 fb             	idiv   %rbx
  403090:	48 89 c3             	mov    %rax,%rbx
  403093:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  403098:	48 99                	cqto
  40309a:	48 f7 fb             	idiv   %rbx
  40309d:	48 89 c6             	mov    %rax,%rsi
  4030a0:	48 8d 05 46 11 00 00 	lea    0x1146(%rip),%rax        # 4041ed <_IO_stdin_used+0x1ed>
  4030a7:	48 89 c7             	mov    %rax,%rdi
  4030aa:	b8 00 00 00 00       	mov    $0x0,%eax
  4030af:	e8 cc df ff ff       	call   401080 <printf@plt>
  4030b4:	48 8d 05 4c 11 00 00 	lea    0x114c(%rip),%rax        # 404207 <_IO_stdin_used+0x207>
  4030bb:	48 89 c7             	mov    %rax,%rdi
  4030be:	e8 7d df ff ff       	call   401040 <puts@plt>
  4030c3:	c7 85 b4 fe ff ff 00 00 00 00 	movl   $0x0,-0x14c(%rbp)
  4030cd:	e9 84 02 00 00       	jmp    403356 <main+0x12cb>
  4030d2:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4030d8:	48 98                	cltq
  4030da:	48 c1 e0 0a          	shl    $0xa,%rax
  4030de:	48 89 c2             	mov    %rax,%rdx
  4030e1:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4030e8:	48 01 d0             	add    %rdx,%rax
  4030eb:	48 8b 80 f0 00 00 00 	mov    0xf0(%rax),%rax
  4030f2:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4030f8:	48 63 d2             	movslq %edx,%rdx
  4030fb:	48 89 d1             	mov    %rdx,%rcx
  4030fe:	48 c1 e1 0a          	shl    $0xa,%rcx
  403102:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403109:	48 01 ca             	add    %rcx,%rdx
  40310c:	48 8b 92 e0 00 00 00 	mov    0xe0(%rdx),%rdx
  403113:	48 29 d0             	sub    %rdx,%rax
  403116:	48 89 c6             	mov    %rax,%rsi
  403119:	48 8d 05 f7 0e 00 00 	lea    0xef7(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  403120:	48 89 c7             	mov    %rax,%rdi
  403123:	b8 00 00 00 00       	mov    $0x0,%eax
  403128:	e8 53 df ff ff       	call   401080 <printf@plt>
  40312d:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403133:	48 98                	cltq
  403135:	48 c1 e0 0a          	shl    $0xa,%rax
  403139:	48 89 c2             	mov    %rax,%rdx
  40313c:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403143:	48 01 d0             	add    %rdx,%rax
  403146:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
  40314d:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  403153:	48 63 d2             	movslq %edx,%rdx
  403156:	48 89 d1             	mov    %rdx,%rcx
  403159:	48 c1 e1 0a          	shl    $0xa,%rcx
  40315d:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403164:	48 01 ca             	add    %rcx,%rdx
  403167:	48 8b 92 e0 00 00 00 	mov    0xe0(%rdx),%rdx
  40316e:	48 29 d0             	sub    %rdx,%rax
  403171:	48 89 c6             	mov    %rax,%rsi
  403174:	48 8d 05 9c 0e 00 00 	lea    0xe9c(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  40317b:	48 89 c7             	mov    %rax,%rdi
  40317e:	b8 00 00 00 00       	mov    $0x0,%eax
  403183:	e8 f8 de ff ff       	call   401080 <printf@plt>
  403188:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  40318e:	48 98                	cltq
  403190:	48 c1 e0 0a          	shl    $0xa,%rax
  403194:	48 89 c2             	mov    %rax,%rdx
  403197:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40319e:	48 01 d0             	add    %rdx,%rax
  4031a1:	48 8b 80 f0 00 00 00 	mov    0xf0(%rax),%rax
  4031a8:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4031ae:	48 63 d2             	movslq %edx,%rdx
  4031b1:	48 89 d1             	mov    %rdx,%rcx
  4031b4:	48 c1 e1 0a          	shl    $0xa,%rcx
  4031b8:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4031bf:	48 01 ca             	add    %rcx,%rdx
  4031c2:	48 8b 92 00 01 00 00 	mov    0x100(%rdx),%rdx
  4031c9:	48 29 d0             	sub    %rdx,%rax
  4031cc:	48 89 c6             	mov    %rax,%rsi
  4031cf:	48 8d 05 41 0e 00 00 	lea    0xe41(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  4031d6:	48 89 c7             	mov    %rax,%rdi
  4031d9:	b8 00 00 00 00       	mov    $0x0,%eax
  4031de:	e8 9d de ff ff       	call   401080 <printf@plt>
  4031e3:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4031e9:	48 98                	cltq
  4031eb:	48 c1 e0 0a          	shl    $0xa,%rax
  4031ef:	48 89 c2             	mov    %rax,%rdx
  4031f2:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4031f9:	48 01 d0             	add    %rdx,%rax
  4031fc:	48 8b 80 20 01 00 00 	mov    0x120(%rax),%rax
  403203:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  403209:	48 63 d2             	movslq %edx,%rdx
  40320c:	48 89 d1             	mov    %rdx,%rcx
  40320f:	48 c1 e1 0a          	shl    $0xa,%rcx
  403213:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  40321a:	48 01 ca             	add    %rcx,%rdx
  40321d:	48 8b 92 10 01 00 00 	mov    0x110(%rdx),%rdx
  403224:	48 29 d0             	sub    %rdx,%rax
  403227:	48 89 c6             	mov    %rax,%rsi
  40322a:	48 8d 05 e6 0d 00 00 	lea    0xde6(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  403231:	48 89 c7             	mov    %rax,%rdi
  403234:	b8 00 00 00 00       	mov    $0x0,%eax
  403239:	e8 42 de ff ff       	call   401080 <printf@plt>
  40323e:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  403244:	48 98                	cltq
  403246:	48 c1 e0 0a          	shl    $0xa,%rax
  40324a:	48 89 c2             	mov    %rax,%rdx
  40324d:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  403254:	48 01 d0             	add    %rdx,%rax
  403257:	48 8b 80 10 01 00 00 	mov    0x110(%rax),%rax
  40325e:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  403264:	48 63 d2             	movslq %edx,%rdx
  403267:	48 89 d1             	mov    %rdx,%rcx
  40326a:	48 c1 e1 0a          	shl    $0xa,%rcx
  40326e:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  403275:	48 01 ca             	add    %rcx,%rdx
  403278:	48 8b 92 20 01 00 00 	mov    0x120(%rdx),%rdx
  40327f:	48 29 d0             	sub    %rdx,%rax
  403282:	48 89 c6             	mov    %rax,%rsi
  403285:	48 8d 05 8b 0d 00 00 	lea    0xd8b(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  40328c:	48 89 c7             	mov    %rax,%rdi
  40328f:	b8 00 00 00 00       	mov    $0x0,%eax
  403294:	e8 e7 dd ff ff       	call   401080 <printf@plt>
  403299:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  40329f:	48 98                	cltq
  4032a1:	48 c1 e0 0a          	shl    $0xa,%rax
  4032a5:	48 89 c2             	mov    %rax,%rdx
  4032a8:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  4032af:	48 01 d0             	add    %rdx,%rax
  4032b2:	48 8b 80 10 01 00 00 	mov    0x110(%rax),%rax
  4032b9:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  4032bf:	48 63 d2             	movslq %edx,%rdx
  4032c2:	48 89 d1             	mov    %rdx,%rcx
  4032c5:	48 c1 e1 0a          	shl    $0xa,%rcx
  4032c9:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  4032d0:	48 01 ca             	add    %rcx,%rdx
  4032d3:	48 8b 92 00 01 00 00 	mov    0x100(%rdx),%rdx
  4032da:	48 29 d0             	sub    %rdx,%rax
  4032dd:	48 89 c6             	mov    %rax,%rsi
  4032e0:	48 8d 05 30 0d 00 00 	lea    0xd30(%rip),%rax        # 404017 <_IO_stdin_used+0x17>
  4032e7:	48 89 c7             	mov    %rax,%rdi
  4032ea:	b8 00 00 00 00       	mov    $0x0,%eax
  4032ef:	e8 8c dd ff ff       	call   401080 <printf@plt>
  4032f4:	8b 85 b4 fe ff ff    	mov    -0x14c(%rbp),%eax
  4032fa:	48 98                	cltq
  4032fc:	48 c1 e0 0a          	shl    $0xa,%rax
  403300:	48 89 c2             	mov    %rax,%rdx
  403303:	48 8b 85 f8 fe ff ff 	mov    -0x108(%rbp),%rax
  40330a:	48 01 d0             	add    %rdx,%rax
  40330d:	48 8b 80 40 01 00 00 	mov    0x140(%rax),%rax
  403314:	8b 95 b4 fe ff ff    	mov    -0x14c(%rbp),%edx
  40331a:	48 63 d2             	movslq %edx,%rdx
  40331d:	48 89 d1             	mov    %rdx,%rcx
  403320:	48 c1 e1 0a          	shl    $0xa,%rcx
  403324:	48 8b 95 f8 fe ff ff 	mov    -0x108(%rbp),%rdx
  40332b:	48 01 ca             	add    %rcx,%rdx
  40332e:	48 8b 92 30 01 00 00 	mov    0x130(%rdx),%rdx
  403335:	48 29 d0             	sub    %rdx,%rax
  403338:	48 89 c6             	mov    %rax,%rsi
  40333b:	48 8d 05 d2 0e 00 00 	lea    0xed2(%rip),%rax        # 404214 <_IO_stdin_used+0x214>
  403342:	48 89 c7             	mov    %rax,%rdi
  403345:	b8 00 00 00 00       	mov    $0x0,%eax
  40334a:	e8 31 dd ff ff       	call   401080 <printf@plt>
  40334f:	83 85 b4 fe ff ff 01 	addl   $0x1,-0x14c(%rbp)
  403356:	83 bd b4 fe ff ff 00 	cmpl   $0x0,-0x14c(%rbp)
  40335d:	0f 8e 6f fd ff ff    	jle    4030d2 <main+0x1047>
  403363:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  403369:	48 63 d8             	movslq %eax,%rbx
  40336c:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
  403373:	48 99                	cqto
  403375:	48 f7 fb             	idiv   %rbx
  403378:	48 89 c6             	mov    %rax,%rsi
  40337b:	48 8d 05 9a 0e 00 00 	lea    0xe9a(%rip),%rax        # 40421c <_IO_stdin_used+0x21c>
  403382:	48 89 c7             	mov    %rax,%rdi
  403385:	b8 00 00 00 00       	mov    $0x0,%eax
  40338a:	e8 f1 dc ff ff       	call   401080 <printf@plt>
  40338f:	8b 85 a4 fe ff ff    	mov    -0x15c(%rbp),%eax
  403395:	48 63 d8             	movslq %eax,%rbx
  403398:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
  40339f:	48 99                	cqto
  4033a1:	48 f7 fb             	idiv   %rbx
  4033a4:	48 89 c3             	mov    %rax,%rbx
  4033a7:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  4033ac:	48 99                	cqto
  4033ae:	48 f7 fb             	idiv   %rbx
  4033b1:	48 89 c6             	mov    %rax,%rsi
  4033b4:	48 8d 05 7d 0e 00 00 	lea    0xe7d(%rip),%rax        # 404238 <_IO_stdin_used+0x238>
  4033bb:	48 89 c7             	mov    %rax,%rdi
  4033be:	b8 00 00 00 00       	mov    $0x0,%eax
  4033c3:	e8 b8 dc ff ff       	call   401080 <printf@plt>
  4033c8:	be 01 00 00 00       	mov    $0x1,%esi
  4033cd:	bf 64 00 00 00       	mov    $0x64,%edi
  4033d2:	e8 f9 dc ff ff       	call   4010d0 <calloc@plt>
  4033d7:	48 89 45 90          	mov    %rax,-0x70(%rbp)
  4033db:	be 01 00 00 00       	mov    $0x1,%esi
  4033e0:	bf e8 03 00 00       	mov    $0x3e8,%edi
  4033e5:	e8 e6 dc ff ff       	call   4010d0 <calloc@plt>
  4033ea:	48 89 45 98          	mov    %rax,-0x68(%rbp)
  4033ee:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  4033f2:	ba 64 00 00 00       	mov    $0x64,%edx
  4033f7:	be 00 00 00 00       	mov    $0x0,%esi
  4033fc:	48 89 c7             	mov    %rax,%rdi
  4033ff:	e8 bc dc ff ff       	call   4010c0 <memset@plt>
  403404:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403408:	48 8d 15 4c 0e 00 00 	lea    0xe4c(%rip),%rdx        # 40425b <_IO_stdin_used+0x25b>
  40340f:	be 64 00 00 00       	mov    $0x64,%esi
  403414:	48 89 c7             	mov    %rax,%rdi
  403417:	b8 00 00 00 00       	mov    $0x0,%eax
  40341c:	e8 6f dc ff ff       	call   401090 <snprintf@plt>
  403421:	48 8b 45 90          	mov    -0x70(%rbp),%rax
  403425:	48 8d 15 40 0e 00 00 	lea    0xe40(%rip),%rdx        # 40426c <_IO_stdin_used+0x26c>
  40342c:	48 89 d6             	mov    %rdx,%rsi
  40342f:	48 89 c7             	mov    %rax,%rdi
  403432:	e8 b9 dc ff ff       	call   4010f0 <fopen@plt>
  403437:	48 89 45 a0          	mov    %rax,-0x60(%rbp)
  40343b:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40343f:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403444:	be 00 00 00 00       	mov    $0x0,%esi
  403449:	48 89 c7             	mov    %rax,%rdi
  40344c:	e8 6f dc ff ff       	call   4010c0 <memset@plt>
  403451:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403455:	b9 00 00 00 00       	mov    $0x0,%ecx
  40345a:	48 8d 15 0d 0e 00 00 	lea    0xe0d(%rip),%rdx        # 40426e <_IO_stdin_used+0x26e>
  403461:	be 64 00 00 00       	mov    $0x64,%esi
  403466:	48 89 c7             	mov    %rax,%rdi
  403469:	b8 00 00 00 00       	mov    $0x0,%eax
  40346e:	e8 1d dc ff ff       	call   401090 <snprintf@plt>
  403473:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  403477:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40347b:	48 89 d6             	mov    %rdx,%rsi
  40347e:	48 89 c7             	mov    %rax,%rdi
  403481:	e8 2a dc ff ff       	call   4010b0 <fputs@plt>
  403486:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40348a:	ba e8 03 00 00       	mov    $0x3e8,%edx
  40348f:	be 00 00 00 00       	mov    $0x0,%esi
  403494:	48 89 c7             	mov    %rax,%rdi
  403497:	e8 24 dc ff ff       	call   4010c0 <memset@plt>
  40349c:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034a0:	b9 08 00 00 00       	mov    $0x8,%ecx
  4034a5:	48 8d 15 cd 0d 00 00 	lea    0xdcd(%rip),%rdx        # 404279 <_IO_stdin_used+0x279>
  4034ac:	be 64 00 00 00       	mov    $0x64,%esi
  4034b1:	48 89 c7             	mov    %rax,%rdi
  4034b4:	b8 00 00 00 00       	mov    $0x0,%eax
  4034b9:	e8 d2 db ff ff       	call   401090 <snprintf@plt>
  4034be:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  4034c2:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034c6:	48 89 d6             	mov    %rdx,%rsi
  4034c9:	48 89 c7             	mov    %rax,%rdi
  4034cc:	e8 df db ff ff       	call   4010b0 <fputs@plt>
  4034d1:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034d5:	ba e8 03 00 00       	mov    $0x3e8,%edx
  4034da:	be 00 00 00 00       	mov    $0x0,%esi
  4034df:	48 89 c7             	mov    %rax,%rdi
  4034e2:	e8 d9 db ff ff       	call   4010c0 <memset@plt>
  4034e7:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4034eb:	b9 10 00 00 00       	mov    $0x10,%ecx
  4034f0:	48 8d 15 8b 0d 00 00 	lea    0xd8b(%rip),%rdx        # 404282 <_IO_stdin_used+0x282>
  4034f7:	be 64 00 00 00       	mov    $0x64,%esi
  4034fc:	48 89 c7             	mov    %rax,%rdi
  4034ff:	b8 00 00 00 00       	mov    $0x0,%eax
  403504:	e8 87 db ff ff       	call   401090 <snprintf@plt>
  403509:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  40350d:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403511:	48 89 d6             	mov    %rdx,%rsi
  403514:	48 89 c7             	mov    %rax,%rdi
  403517:	e8 94 db ff ff       	call   4010b0 <fputs@plt>
  40351c:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403520:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403525:	be 00 00 00 00       	mov    $0x0,%esi
  40352a:	48 89 c7             	mov    %rax,%rdi
  40352d:	e8 8e db ff ff       	call   4010c0 <memset@plt>
  403532:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403536:	b9 18 00 00 00       	mov    $0x18,%ecx
  40353b:	48 8d 15 49 0d 00 00 	lea    0xd49(%rip),%rdx        # 40428b <_IO_stdin_used+0x28b>
  403542:	be 64 00 00 00       	mov    $0x64,%esi
  403547:	48 89 c7             	mov    %rax,%rdi
  40354a:	b8 00 00 00 00       	mov    $0x0,%eax
  40354f:	e8 3c db ff ff       	call   401090 <snprintf@plt>
  403554:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  403558:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40355c:	48 89 d6             	mov    %rdx,%rsi
  40355f:	48 89 c7             	mov    %rax,%rdi
  403562:	e8 49 db ff ff       	call   4010b0 <fputs@plt>
  403567:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  40356b:	ba e8 03 00 00       	mov    $0x3e8,%edx
  403570:	be 00 00 00 00       	mov    $0x0,%esi
  403575:	48 89 c7             	mov    %rax,%rdi
  403578:	e8 43 db ff ff       	call   4010c0 <memset@plt>
  40357d:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  403581:	b9 00 00 00 00       	mov    $0x0,%ecx
  403586:	48 8d 15 08 0d 00 00 	lea    0xd08(%rip),%rdx        # 404295 <_IO_stdin_used+0x295>
  40358d:	be 64 00 00 00       	mov    $0x64,%esi
  403592:	48 89 c7             	mov    %rax,%rdi
  403595:	b8 00 00 00 00       	mov    $0x0,%eax
  40359a:	e8 f1 da ff ff       	call   401090 <snprintf@plt>
  40359f:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  4035a3:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4035a7:	48 89 d6             	mov    %rdx,%rsi
  4035aa:	48 89 c7             	mov    %rax,%rdi
  4035ad:	e8 fe da ff ff       	call   4010b0 <fputs@plt>
  4035b2:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4035b6:	ba e8 03 00 00       	mov    $0x3e8,%edx
  4035bb:	be 00 00 00 00       	mov    $0x0,%esi
  4035c0:	48 89 c7             	mov    %rax,%rdi
  4035c3:	e8 f8 da ff ff       	call   4010c0 <memset@plt>
  4035c8:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4035cc:	b9 20 00 00 00       	mov    $0x20,%ecx
  4035d1:	48 8d 15 d8 0c 00 00 	lea    0xcd8(%rip),%rdx        # 4042b0 <_IO_stdin_used+0x2b0>
  4035d8:	be 64 00 00 00       	mov    $0x64,%esi
  4035dd:	48 89 c7             	mov    %rax,%rdi
  4035e0:	b8 00 00 00 00       	mov    $0x0,%eax
  4035e5:	e8 a6 da ff ff       	call   401090 <snprintf@plt>
  4035ea:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
  4035ee:	48 8b 45 98          	mov    -0x68(%rbp),%rax
  4035f2:	48 89 d6             	mov    %rdx,%rsi
  4035f5:	48 89 c7             	mov    %rax,%rdi
  4035f8:	e8 b3 da ff ff       	call   4010b0 <fputs@plt>
  4035fd:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
  403601:	48 89 c7             	mov    %rax,%rdi
  403604:	e8 57 da ff ff       	call   401060 <fclose@plt>
  403609:	b8 00 00 00 00       	mov    $0x0,%eax
  40360e:	48 8b 55 e8          	mov    -0x18(%rbp),%rdx
  403612:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  40361b:	74 05                	je     403622 <main+0x1597>
  40361d:	e8 4e da ff ff       	call   401070 <__stack_chk_fail@plt>
  403622:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
  403626:	c9                   	leave
  403627:	c3                   	ret
  403628:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

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
  403698:	55                   	push   %rbp
  403699:	48 89 e5             	mov    %rsp,%rbp
  40369c:	48 81 ec 00 04 00 00 	sub    $0x400,%rsp
  4036a3:	48 89 7d c8          	mov    %rdi,-0x38(%rbp)
  4036a7:	48 89 75 f8          	mov    %rsi,-0x8(%rbp)
  4036ab:	48 89 55 f0          	mov    %rdx,-0x10(%rbp)
  4036af:	48 89 f0             	mov    %rsi,%rax
  4036b2:	48 6b c0 20          	imul   $0x20,%rax,%rax
  4036b6:	48 01 f8             	add    %rdi,%rax
  4036b9:	49 89 c3             	mov    %rax,%r11
  4036bc:	4c 89 d8             	mov    %r11,%rax
  4036bf:	49 89 c1             	mov    %rax,%r9
  4036c2:	4c 89 4d e8          	mov    %r9,-0x18(%rbp)
  4036c6:	4c 89 d8             	mov    %r11,%rax
  4036c9:	48 8d 40 08          	lea    0x8(%rax),%rax
  4036cd:	49 89 c1             	mov    %rax,%r9
  4036d0:	4c 89 4d d0          	mov    %r9,-0x30(%rbp)
  4036d4:	4c 89 d8             	mov    %r11,%rax
  4036d7:	48 8d 40 10          	lea    0x10(%rax),%rax
  4036db:	4c 8b 08             	mov    (%rax),%r9
  4036de:	4c 89 4d e0          	mov    %r9,-0x20(%rbp)
  4036e2:	4c 89 d8             	mov    %r11,%rax
  4036e5:	48 8d 40 08          	lea    0x8(%rax),%rax
  4036e9:	4c 8b 08             	mov    (%rax),%r9
  4036ec:	4c 89 4d c0          	mov    %r9,-0x40(%rbp)
  4036f0:	4c 89 d8             	mov    %r11,%rax
  4036f3:	48 8d 40 18          	lea    0x18(%rax),%rax
  4036f7:	4c 8b 08             	mov    (%rax),%r9
  4036fa:	4c 89 4d d8          	mov    %r9,-0x28(%rbp)
  4036fe:	48 8b 08             	mov    (%rax),%rcx
  403701:	4c 8b 5d e8          	mov    -0x18(%rbp),%r11
  403705:	48 8d 3d 5a ff ff ff 	lea    -0xa6(%rip),%rdi        # 403666 <.INDEX>
  40370c:	b8 00 00 00 00       	mov    $0x0,%eax
  403711:	48 8d 3d 18 ff ff ff 	lea    -0xe8(%rip),%rdi        # 403630 <.MSG>
  403718:	4c 89 de             	mov    %r11,%rsi
  40371b:	b8 00 00 00 00       	mov    $0x0,%eax
  403720:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9
  403724:	48 8d 3d 1c ff ff ff 	lea    -0xe4(%rip),%rdi        # 403647 <.EIP>
  40372b:	4c 89 ce             	mov    %r9,%rsi
  40372e:	b8 00 00 00 00       	mov    $0x0,%eax
  403733:	48 8d 3d 1b ff ff ff 	lea    -0xe5(%rip),%rdi        # 403655 <.CODATA>
  40373a:	48 8b 75 d8          	mov    -0x28(%rbp),%rsi
  40373e:	b8 00 00 00 00       	mov    $0x0,%eax
  403743:	48 8b 7d f0          	mov    -0x10(%rbp),%rdi
  403747:	48 8b 75 e8          	mov    -0x18(%rbp),%rsi
  40374b:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  40374f:	48 8d 3d 35 ff ff ff 	lea    -0xcb(%rip),%rdi        # 40368b <.STACK>
  403756:	48 8b 75 c0          	mov    -0x40(%rbp),%rsi
  40375a:	e8 21 d9 ff ff       	call   401080 <printf@plt>
  40375f:	b8 00 00 00 00       	mov    $0x0,%eax
  403764:	4c 8b 4d e0          	mov    -0x20(%rbp),%r9
  403768:	4c 8d 1d 0f 00 00 00 	lea    0xf(%rip),%r11        # 40377e <after>
  40376f:	48 8b 65 c0          	mov    -0x40(%rbp),%rsp
  403773:	48 83 ec 08          	sub    $0x8,%rsp
  403777:	4c 89 1c 24          	mov    %r11,(%rsp)
  40377b:	41 ff e1             	jmp    *%r9

000000000040377e <after>:
  40377e:	48 8d 3d f8 fe ff ff 	lea    -0x108(%rip),%rdi        # 40367d <.RET>
  403785:	4c 89 ce             	mov    %r9,%rsi
  403788:	e8 f3 d8 ff ff       	call   401080 <printf@plt>
  40378d:	b8 00 00 00 00       	mov    $0x0,%eax
  403792:	48 81 c4 00 04 00 00 	add    $0x400,%rsp
  403799:	5d                   	pop    %rbp
  40379a:	c3                   	ret

Disassembly of section .fini:

000000000040379c <_fini>:
  40379c:	f3 0f 1e fa          	endbr64
  4037a0:	48 83 ec 08          	sub    $0x8,%rsp
  4037a4:	48 83 c4 08          	add    $0x8,%rsp
  4037a8:	c3                   	ret
