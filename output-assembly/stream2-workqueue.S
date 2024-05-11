
stream2-workqueue:     file format elf64-x86-64


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

0000000000401020 <pthread_setaffinity_np@plt-0x10>:
  401020:	ff 35 62 3f 00 00    	push   0x3f62(%rip)        # 404f88 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 64 3f 00 00    	jmp    *0x3f64(%rip)        # 404f90 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <pthread_setaffinity_np@plt>:
  401030:	ff 25 62 3f 00 00    	jmp    *0x3f62(%rip)        # 404f98 <pthread_setaffinity_np@GLIBC_2.34>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <puts@plt>:
  401040:	ff 25 5a 3f 00 00    	jmp    *0x3f5a(%rip)        # 404fa0 <puts@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <clock_gettime@plt>:
  401050:	ff 25 52 3f 00 00    	jmp    *0x3f52(%rip)        # 404fa8 <clock_gettime@GLIBC_2.17>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <__stack_chk_fail@plt>:
  401060:	ff 25 4a 3f 00 00    	jmp    *0x3f4a(%rip)        # 404fb0 <__stack_chk_fail@GLIBC_2.4>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <nanosleep@plt>:
  401070:	ff 25 42 3f 00 00    	jmp    *0x3f42(%rip)        # 404fb8 <nanosleep@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <memset@plt>:
  401080:	ff 25 3a 3f 00 00    	jmp    *0x3f3a(%rip)        # 404fc0 <memset@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <calloc@plt>:
  401090:	ff 25 32 3f 00 00    	jmp    *0x3f32(%rip)        # 404fc8 <calloc@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <__printf_chk@plt>:
  4010a0:	ff 25 2a 3f 00 00    	jmp    *0x3f2a(%rip)        # 404fd0 <__printf_chk@GLIBC_2.3.4>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <pthread_create@plt>:
  4010b0:	ff 25 22 3f 00 00    	jmp    *0x3f22(%rip)        # 404fd8 <pthread_create@GLIBC_2.34>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <posix_memalign@plt>:
  4010c0:	ff 25 1a 3f 00 00    	jmp    *0x3f1a(%rip)        # 404fe0 <posix_memalign@GLIBC_2.2.5>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010d0 <pthread_join@plt>:
  4010d0:	ff 25 12 3f 00 00    	jmp    *0x3f12(%rip)        # 404fe8 <pthread_join@GLIBC_2.34>
  4010d6:	68 0a 00 00 00       	push   $0xa
  4010db:	e9 40 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

00000000004010e0 <main>:
  4010e0:	41 57                	push   %r15
  4010e2:	ba 08 00 00 00       	mov    $0x8,%edx
  4010e7:	bf 01 00 00 00       	mov    $0x1,%edi
  4010ec:	48 8d 35 34 1f 00 00 	lea    0x1f34(%rip),%rsi        # 403027 <_IO_stdin_used+0x27>
  4010f3:	41 56                	push   %r14
  4010f5:	41 be 01 00 00 00    	mov    $0x1,%r14d
  4010fb:	41 55                	push   %r13
  4010fd:	4d 89 f5             	mov    %r14,%r13
  401100:	41 54                	push   %r12
  401102:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
  401108:	55                   	push   %rbp
  401109:	53                   	push   %rbx
  40110a:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
  401111:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40111a:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
  40111f:	31 c0                	xor    %eax,%eax
  401121:	e8 7a ff ff ff       	call   4010a0 <__printf_chk@plt>
  401126:	ba 04 00 00 00       	mov    $0x4,%edx
  40112b:	48 8d 35 07 1f 00 00 	lea    0x1f07(%rip),%rsi        # 403039 <_IO_stdin_used+0x39>
  401132:	31 c0                	xor    %eax,%eax
  401134:	bf 01 00 00 00       	mov    $0x1,%edi
  401139:	e8 62 ff ff ff       	call   4010a0 <__printf_chk@plt>
  40113e:	ba 20 00 00 00       	mov    $0x20,%edx
  401143:	48 8d 35 eb 1e 00 00 	lea    0x1eeb(%rip),%rsi        # 403035 <_IO_stdin_used+0x35>
  40114a:	31 c0                	xor    %eax,%eax
  40114c:	bf 01 00 00 00       	mov    $0x1,%edi
  401151:	e8 4a ff ff ff       	call   4010a0 <__printf_chk@plt>
  401156:	ba 0f 00 00 00       	mov    $0xf,%edx
  40115b:	48 8d 35 e6 1e 00 00 	lea    0x1ee6(%rip),%rsi        # 403048 <_IO_stdin_used+0x48>
  401162:	31 c0                	xor    %eax,%eax
  401164:	bf 01 00 00 00       	mov    $0x1,%edi
  401169:	e8 32 ff ff ff       	call   4010a0 <__printf_chk@plt>
  40116e:	be 08 00 00 00       	mov    $0x8,%esi
  401173:	bf 0f 00 00 00       	mov    $0xf,%edi
  401178:	e8 13 ff ff ff       	call   401090 <calloc@plt>
  40117d:	be 38 00 00 00       	mov    $0x38,%esi
  401182:	bf 0f 00 00 00       	mov    $0xf,%edi
  401187:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  40118c:	e8 ff fe ff ff       	call   401090 <calloc@plt>
  401191:	be 00 3c 00 00       	mov    $0x3c00,%esi
  401196:	bf 01 00 00 00       	mov    $0x1,%edi
  40119b:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  4011a0:	e8 eb fe ff ff       	call   401090 <calloc@plt>
  4011a5:	4c 89 e7             	mov    %r12,%rdi
  4011a8:	be 01 00 00 00       	mov    $0x1,%esi
  4011ad:	48 89 c3             	mov    %rax,%rbx
  4011b0:	e8 db fe ff ff       	call   401090 <calloc@plt>
  4011b5:	4c 89 e2             	mov    %r12,%rdx
  4011b8:	be ff ff ff ff       	mov    $0xffffffff,%esi
  4011bd:	49 89 de             	mov    %rbx,%r14
  4011c0:	48 89 c7             	mov    %rax,%rdi
  4011c3:	48 89 c5             	mov    %rax,%rbp
  4011c6:	e8 b5 fe ff ff       	call   401080 <memset@plt>
  4011cb:	4c 89 e2             	mov    %r12,%rdx
  4011ce:	bf 01 00 00 00       	mov    $0x1,%edi
  4011d3:	31 c0                	xor    %eax,%eax
  4011d5:	48 8d 35 81 1e 00 00 	lea    0x1e81(%rip),%rsi        # 40305d <_IO_stdin_used+0x5d>
  4011dc:	e8 bf fe ff ff       	call   4010a0 <__printf_chk@plt>
  4011e1:	be 20 00 00 00       	mov    $0x20,%esi
  4011e6:	bf 64 00 00 00       	mov    $0x64,%edi
  4011eb:	e8 a0 fe ff ff       	call   401090 <calloc@plt>
  4011f0:	31 d2                	xor    %edx,%edx
  4011f2:	bf 01 00 00 00       	mov    $0x1,%edi
  4011f7:	48 8d 35 70 1e 00 00 	lea    0x1e70(%rip),%rsi        # 40306e <_IO_stdin_used+0x6e>
  4011fe:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  401203:	31 c0                	xor    %eax,%eax
  401205:	e8 96 fe ff ff       	call   4010a0 <__printf_chk@plt>
  40120a:	4c 89 e2             	mov    %r12,%rdx
  40120d:	bf 01 00 00 00       	mov    $0x1,%edi
  401212:	31 c0                	xor    %eax,%eax
  401214:	48 8d 35 5f 1e 00 00 	lea    0x1e5f(%rip),%rsi        # 40307a <_IO_stdin_used+0x7a>
  40121b:	e8 80 fe ff ff       	call   4010a0 <__printf_chk@plt>
  401220:	be 04 00 00 00       	mov    $0x4,%esi
  401225:	bf 0f 00 00 00       	mov    $0xf,%edi
  40122a:	e8 61 fe ff ff       	call   401090 <calloc@plt>
  40122f:	ba 00 02 00 00       	mov    $0x200,%edx
  401234:	48 8d 7c 24 48       	lea    0x48(%rsp),%rdi
  401239:	be 80 00 00 00       	mov    $0x80,%esi
  40123e:	49 89 c4             	mov    %rax,%r12
  401241:	e8 7a fe ff ff       	call   4010c0 <posix_memalign@plt>
  401246:	be 0c 00 00 00       	mov    $0xc,%esi
  40124b:	bf 0f 00 00 00       	mov    $0xf,%edi
  401250:	85 c0                	test   %eax,%eax
  401252:	b8 00 00 00 00       	mov    $0x0,%eax
  401257:	48 0f 44 44 24 48    	cmove  0x48(%rsp),%rax
  40125d:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  401262:	e8 29 fe ff ff       	call   401090 <calloc@plt>
  401267:	48 89 6b 70          	mov    %rbp,0x70(%rbx)
  40126b:	be 14 00 00 00       	mov    $0x14,%esi
  401270:	bf 80 96 98 00       	mov    $0x989680,%edi
  401275:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  40127a:	e8 11 fe ff ff       	call   401090 <calloc@plt>
  40127f:	be 14 00 00 00       	mov    $0x14,%esi
  401284:	bf 80 96 98 00       	mov    $0x989680,%edi
  401289:	48 89 c5             	mov    %rax,%rbp
  40128c:	e8 ff fd ff ff       	call   401090 <calloc@plt>
  401291:	66 48 0f 6e ed       	movq   %rbp,%xmm5
  401296:	31 ed                	xor    %ebp,%ebp
  401298:	66 48 0f 6e f0       	movq   %rax,%xmm6
  40129d:	66 0f 6c ee          	punpcklqdq %xmm6,%xmm5
  4012a1:	0f 29 6c 24 20       	movaps %xmm5,0x20(%rsp)
  4012a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4012b0:	66 0f 6f 4c 24 20    	movdqa 0x20(%rsp),%xmm1
  4012b6:	be 80 00 00 00       	mov    $0x80,%esi
  4012bb:	44 89 2c 24          	mov    %r13d,(%rsp)
  4012bf:	45 8d 7d ff          	lea    -0x1(%r13),%r15d
  4012c3:	bf 01 00 00 00       	mov    $0x1,%edi
  4012c8:	49 81 c6 00 04 00 00 	add    $0x400,%r14
  4012cf:	41 0f 29 4e a0       	movaps %xmm1,-0x60(%r14)
  4012d4:	e8 b7 fd ff ff       	call   401090 <calloc@plt>
  4012d9:	44 89 e9             	mov    %r13d,%ecx
  4012dc:	be 01 00 00 00       	mov    $0x1,%esi
  4012e1:	44 89 fa             	mov    %r15d,%edx
  4012e4:	49 89 86 78 fc ff ff 	mov    %rax,-0x388(%r14)
  4012eb:	48 d3 e6             	shl    %cl,%rsi
  4012ee:	8b 0c 24             	mov    (%rsp),%ecx
  4012f1:	bf 01 00 00 00       	mov    $0x1,%edi
  4012f6:	48 09 30             	or     %rsi,(%rax)
  4012f9:	48 8d 35 c8 1e 00 00 	lea    0x1ec8(%rip),%rsi        # 4031c8 <_IO_stdin_used+0x1c8>
  401300:	31 c0                	xor    %eax,%eax
  401302:	e8 99 fd ff ff       	call   4010a0 <__printf_chk@plt>
  401307:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  40130c:	44 89 fa             	mov    %r15d,%edx
  40130f:	41 89 ae 98 fc ff ff 	mov    %ebp,-0x368(%r14)
  401316:	c1 fa 02             	sar    $0x2,%edx
  401319:	66 0f 6f 15 2f 1f 00 00 	movdqa 0x1f2f(%rip),%xmm2        # 403250 <_IO_stdin_used+0x250>
  401321:	66 0f 6f 1d 37 1f 00 00 	movdqa 0x1f37(%rip),%xmm3        # 403260 <_IO_stdin_used+0x260>
  401329:	41 c7 86 80 fc ff ff 00 00 00 00 	movl   $0x0,-0x380(%r14)
  401334:	49 89 46 80          	mov    %rax,-0x80(%r14)
  401338:	83 c2 01             	add    $0x1,%edx
  40133b:	48 8b 05 fe 1e 00 00 	mov    0x1efe(%rip),%rax        # 403240 <_IO_stdin_used+0x240>
  401342:	be 30 00 00 00       	mov    $0x30,%esi
  401347:	66 0f 6f 25 21 1f 00 00 	movdqa 0x1f21(%rip),%xmm4        # 403270 <_IO_stdin_used+0x270>
  40134f:	bf 80 96 98 00       	mov    $0x989680,%edi
  401354:	45 89 be 64 fc ff ff 	mov    %r15d,-0x39c(%r14)
  40135b:	81 c5 11 11 11 11    	add    $0x11111111,%ebp
  401361:	49 89 86 5c fc ff ff 	mov    %rax,-0x3a4(%r14)
  401368:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  40136d:	41 c7 86 94 fc ff ff 11 11 11 11 	movl   $0x11111111,-0x36c(%r14)
  401378:	41 c7 86 68 fc ff ff 0f 00 00 00 	movl   $0xf,-0x398(%r14)
  401383:	4d 89 a6 20 fc ff ff 	mov    %r12,-0x3e0(%r14)
  40138a:	43 c7 44 ac fc 00 00 00 00 	movl   $0x0,-0x4(%r12,%r13,4)
  401393:	49 83 c5 01          	add    $0x1,%r13
  401397:	41 89 56 8c          	mov    %edx,-0x74(%r14)
  40139b:	41 c7 86 90 fc ff ff 11 11 11 11 	movl   $0x11111111,-0x370(%r14)
  4013a6:	49 89 9e 28 fc ff ff 	mov    %rbx,-0x3d8(%r14)
  4013ad:	49 89 9e 30 fc ff ff 	mov    %rbx,-0x3d0(%r14)
  4013b4:	41 c7 86 00 fe ff ff 0e 00 00 00 	movl   $0xe,-0x200(%r14)
  4013bf:	41 c7 86 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%r14)
  4013ca:	49 89 86 a0 fc ff ff 	mov    %rax,-0x360(%r14)
  4013d1:	41 c7 86 c8 fc ff ff 00 00 00 00 	movl   $0x0,-0x338(%r14)
  4013dc:	41 c7 86 28 ff ff ff 0f 00 00 00 	movl   $0xf,-0xd8(%r14)
  4013e7:	41 0f 29 96 00 fc ff ff 	movaps %xmm2,-0x400(%r14)
  4013ef:	41 0f 11 9e b8 fc ff ff 	movups %xmm3,-0x348(%r14)
  4013f7:	41 0f 11 a6 08 ff ff ff 	movups %xmm4,-0xf8(%r14)
  4013ff:	e8 8c fc ff ff       	call   401090 <calloc@plt>
  401404:	be 30 00 00 00       	mov    $0x30,%esi
  401409:	bf 10 27 00 00       	mov    $0x2710,%edi
  40140e:	41 c7 86 20 ff ff ff 80 96 98 00 	movl   $0x989680,-0xe0(%r14)
  401419:	49 89 86 18 ff ff ff 	mov    %rax,-0xe8(%r14)
  401420:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  401425:	49 89 86 48 ff ff ff 	mov    %rax,-0xb8(%r14)
  40142c:	e8 5f fc ff ff       	call   401090 <calloc@plt>
  401431:	41 c7 46 b8 80 96 98 00 	movl   $0x989680,-0x48(%r14)
  401439:	49 89 86 30 ff ff ff 	mov    %rax,-0xd0(%r14)
  401440:	49 83 fd 10          	cmp    $0x10,%r13
  401444:	0f 85 66 fe ff ff    	jne    4012b0 <main+0x1d0>
  40144a:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
  40144f:	4c 8b 7c 24 30       	mov    0x30(%rsp),%r15
  401454:	48 89 1c 24          	mov    %rbx,(%rsp)
  401458:	49 c7 c5 60 20 40 00 	mov    $0x402060,%r13
  40145f:	48 8d 85 48 03 00 00 	lea    0x348(%rbp),%rax
  401466:	4d 89 fc             	mov    %r15,%r12
  401469:	49 89 c6             	mov    %rax,%r14
  40146c:	0f 1f 40 00          	nopl   0x0(%rax)
  401470:	48 89 d9             	mov    %rbx,%rcx
  401473:	48 89 ee             	mov    %rbp,%rsi
  401476:	4c 89 ff             	mov    %r15,%rdi
  401479:	4c 89 ea             	mov    %r13,%rdx
  40147c:	e8 2f fc ff ff       	call   4010b0 <pthread_create@plt>
  401481:	48 8b 53 78          	mov    0x78(%rbx),%rdx
  401485:	49 8b 3f             	mov    (%r15),%rdi
  401488:	be 08 00 00 00       	mov    $0x8,%esi
  40148d:	48 83 c5 38          	add    $0x38,%rbp
  401491:	49 83 c7 08          	add    $0x8,%r15
  401495:	48 81 c3 00 04 00 00 	add    $0x400,%rbx
  40149c:	e8 8f fb ff ff       	call   401030 <pthread_setaffinity_np@plt>
  4014a1:	4c 39 f5             	cmp    %r14,%rbp
  4014a4:	75 ca                	jne    401470 <main+0x390>
  4014a6:	48 8b 1c 24          	mov    (%rsp),%rbx
  4014aa:	48 8d 74 24 60       	lea    0x60(%rsp),%rsi
  4014af:	48 8d 7c 24 50       	lea    0x50(%rsp),%rdi
  4014b4:	66 0f 6f 05 c4 1d 00 00 	movdqa 0x1dc4(%rip),%xmm0        # 403280 <_IO_stdin_used+0x280>
  4014bc:	4c 8d 6c 24 40       	lea    0x40(%rsp),%r13
  4014c1:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  4014c6:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4014ca:	0f 29 44 24 60       	movaps %xmm0,0x60(%rsp)
  4014cf:	e8 9c fb ff ff       	call   401070 <nanosleep@plt>
  4014d4:	48 8d 3d ab 1b 00 00 	lea    0x1bab(%rip),%rdi        # 403086 <_IO_stdin_used+0x86>
  4014db:	e8 60 fb ff ff       	call   401040 <puts@plt>
  4014e0:	83 6b 5c 01          	subl   $0x1,0x5c(%rbx)
  4014e4:	48 8d 3d a5 1b 00 00 	lea    0x1ba5(%rip),%rdi        # 403090 <_IO_stdin_used+0x90>
  4014eb:	83 ab 5c 04 00 00 01 	subl   $0x1,0x45c(%rbx)
  4014f2:	83 ab 5c 08 00 00 01 	subl   $0x1,0x85c(%rbx)
  4014f9:	83 ab 5c 0c 00 00 01 	subl   $0x1,0xc5c(%rbx)
  401500:	83 ab 5c 10 00 00 01 	subl   $0x1,0x105c(%rbx)
  401507:	83 ab 5c 14 00 00 01 	subl   $0x1,0x145c(%rbx)
  40150e:	83 ab 5c 18 00 00 01 	subl   $0x1,0x185c(%rbx)
  401515:	83 ab 5c 1c 00 00 01 	subl   $0x1,0x1c5c(%rbx)
  40151c:	83 ab 5c 20 00 00 01 	subl   $0x1,0x205c(%rbx)
  401523:	83 ab 5c 24 00 00 01 	subl   $0x1,0x245c(%rbx)
  40152a:	83 ab 5c 28 00 00 01 	subl   $0x1,0x285c(%rbx)
  401531:	83 ab 5c 2c 00 00 01 	subl   $0x1,0x2c5c(%rbx)
  401538:	83 ab 5c 30 00 00 01 	subl   $0x1,0x305c(%rbx)
  40153f:	83 ab 5c 34 00 00 01 	subl   $0x1,0x345c(%rbx)
  401546:	83 ab 5c 38 00 00 01 	subl   $0x1,0x385c(%rbx)
  40154d:	e8 ee fa ff ff       	call   401040 <puts@plt>
  401552:	48 8b 6c 24 30       	mov    0x30(%rsp),%rbp
  401557:	83 6b 5c 01          	subl   $0x1,0x5c(%rbx)
  40155b:	83 ab 5c 04 00 00 01 	subl   $0x1,0x45c(%rbx)
  401562:	83 ab 5c 08 00 00 01 	subl   $0x1,0x85c(%rbx)
  401569:	83 ab 5c 0c 00 00 01 	subl   $0x1,0xc5c(%rbx)
  401570:	83 ab 5c 10 00 00 01 	subl   $0x1,0x105c(%rbx)
  401577:	83 ab 5c 14 00 00 01 	subl   $0x1,0x145c(%rbx)
  40157e:	83 ab 5c 18 00 00 01 	subl   $0x1,0x185c(%rbx)
  401585:	83 ab 5c 1c 00 00 01 	subl   $0x1,0x1c5c(%rbx)
  40158c:	83 ab 5c 20 00 00 01 	subl   $0x1,0x205c(%rbx)
  401593:	83 ab 5c 24 00 00 01 	subl   $0x1,0x245c(%rbx)
  40159a:	83 ab 5c 28 00 00 01 	subl   $0x1,0x285c(%rbx)
  4015a1:	83 ab 5c 2c 00 00 01 	subl   $0x1,0x2c5c(%rbx)
  4015a8:	83 ab 5c 30 00 00 01 	subl   $0x1,0x305c(%rbx)
  4015af:	83 ab 5c 34 00 00 01 	subl   $0x1,0x345c(%rbx)
  4015b6:	83 ab 5c 38 00 00 01 	subl   $0x1,0x385c(%rbx)
  4015bd:	48 83 c5 78          	add    $0x78,%rbp
  4015c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  4015c8:	49 8b 3c 24          	mov    (%r12),%rdi
  4015cc:	4c 89 ee             	mov    %r13,%rsi
  4015cf:	49 83 c4 08          	add    $0x8,%r12
  4015d3:	e8 f8 fa ff ff       	call   4010d0 <pthread_join@plt>
  4015d8:	4c 39 e5             	cmp    %r12,%rbp
  4015db:	75 eb                	jne    4015c8 <main+0x4e8>
  4015dd:	48 8d 3d b5 1a 00 00 	lea    0x1ab5(%rip),%rdi        # 403099 <_IO_stdin_used+0x99>
  4015e4:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  4015e8:	45 31 e4             	xor    %r12d,%r12d
  4015eb:	e8 50 fa ff ff       	call   401040 <puts@plt>
  4015f0:	4c 8d b3 48 3c 00 00 	lea    0x3c48(%rbx),%r14
  4015f7:	4c 8d 2d b0 1a 00 00 	lea    0x1ab0(%rip),%r13        # 4030ae <_IO_stdin_used+0xae>
  4015fe:	66 90                	xchg   %ax,%ax
  401600:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401604:	4c 89 ee             	mov    %r13,%rsi
  401607:	bf 01 00 00 00       	mov    $0x1,%edi
  40160c:	31 c0                	xor    %eax,%eax
  40160e:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
  401615:	e8 86 fa ff ff       	call   4010a0 <__printf_chk@plt>
  40161a:	4c 03 a5 00 fc ff ff 	add    -0x400(%rbp),%r12
  401621:	49 39 ee             	cmp    %rbp,%r14
  401624:	75 da                	jne    401600 <main+0x520>
  401626:	4c 89 e2             	mov    %r12,%rdx
  401629:	48 8d 35 89 1a 00 00 	lea    0x1a89(%rip),%rsi        # 4030b9 <_IO_stdin_used+0xb9>
  401630:	bf 01 00 00 00       	mov    $0x1,%edi
  401635:	31 c0                	xor    %eax,%eax
  401637:	e8 64 fa ff ff       	call   4010a0 <__printf_chk@plt>
  40163c:	4c 89 e2             	mov    %r12,%rdx
  40163f:	bf 01 00 00 00       	mov    $0x1,%edi
  401644:	31 c0                	xor    %eax,%eax
  401646:	48 8d 35 77 1a 00 00 	lea    0x1a77(%rip),%rsi        # 4030c4 <_IO_stdin_used+0xc4>
  40164d:	48 8d ab 98 03 00 00 	lea    0x398(%rbx),%rbp
  401654:	e8 47 fa ff ff       	call   4010a0 <__printf_chk@plt>
  401659:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40165e:	48 8d 35 6d 1a 00 00 	lea    0x1a6d(%rip),%rsi        # 4030d2 <_IO_stdin_used+0xd2>
  401665:	bf 01 00 00 00       	mov    $0x1,%edi
  40166a:	48 99                	cqto
  40166c:	4c 8d bb 98 3f 00 00 	lea    0x3f98(%rbx),%r15
  401673:	4c 8d 35 9d 1a 00 00 	lea    0x1a9d(%rip),%r14        # 403117 <_IO_stdin_used+0x117>
  40167a:	49 f7 fc             	idiv   %r12
  40167d:	49 89 c4             	mov    %rax,%r12
  401680:	48 89 c2             	mov    %rax,%rdx
  401683:	31 c0                	xor    %eax,%eax
  401685:	e8 16 fa ff ff       	call   4010a0 <__printf_chk@plt>
  40168a:	4c 89 e2             	mov    %r12,%rdx
  40168d:	bf 01 00 00 00       	mov    $0x1,%edi
  401692:	31 c0                	xor    %eax,%eax
  401694:	48 8d 35 4b 1a 00 00 	lea    0x1a4b(%rip),%rsi        # 4030e6 <_IO_stdin_used+0xe6>
  40169b:	e8 00 fa ff ff       	call   4010a0 <__printf_chk@plt>
  4016a0:	4c 89 e2             	mov    %r12,%rdx
  4016a3:	bf 01 00 00 00       	mov    $0x1,%edi
  4016a8:	31 c0                	xor    %eax,%eax
  4016aa:	48 8d 35 53 1a 00 00 	lea    0x1a53(%rip),%rsi        # 403104 <_IO_stdin_used+0x104>
  4016b1:	45 31 e4             	xor    %r12d,%r12d
  4016b4:	e8 e7 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  4016b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  4016c0:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  4016c4:	4c 89 f6             	mov    %r14,%rsi
  4016c7:	bf 01 00 00 00       	mov    $0x1,%edi
  4016cc:	31 c0                	xor    %eax,%eax
  4016ce:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
  4016d5:	e8 c6 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  4016da:	4c 8b ad 00 fc ff ff 	mov    -0x400(%rbp),%r13
  4016e1:	4d 01 e5             	add    %r12,%r13
  4016e4:	4d 89 ec             	mov    %r13,%r12
  4016e7:	49 39 ef             	cmp    %rbp,%r15
  4016ea:	75 d4                	jne    4016c0 <main+0x5e0>
  4016ec:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  4016f0:	4c 8d bb 50 3c 00 00 	lea    0x3c50(%rbx),%r15
  4016f7:	45 31 e4             	xor    %r12d,%r12d
  4016fa:	4c 8d 35 28 1a 00 00 	lea    0x1a28(%rip),%r14        # 403129 <_IO_stdin_used+0x129>
  401701:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401708:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  40170c:	4c 89 f6             	mov    %r14,%rsi
  40170f:	bf 01 00 00 00       	mov    $0x1,%edi
  401714:	31 c0                	xor    %eax,%eax
  401716:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
  40171d:	49 01 d4             	add    %rdx,%r12
  401720:	e8 7b f9 ff ff       	call   4010a0 <__printf_chk@plt>
  401725:	49 39 ef             	cmp    %rbp,%r15
  401728:	75 de                	jne    401708 <main+0x628>
  40172a:	4c 89 e2             	mov    %r12,%rdx
  40172d:	bf 01 00 00 00       	mov    $0x1,%edi
  401732:	31 c0                	xor    %eax,%eax
  401734:	bd 00 ca 9a 3b       	mov    $0x3b9aca00,%ebp
  401739:	48 8d 35 f5 19 00 00 	lea    0x19f5(%rip),%rsi        # 403135 <_IO_stdin_used+0x135>
  401740:	e8 5b f9 ff ff       	call   4010a0 <__printf_chk@plt>
  401745:	4c 89 e2             	mov    %r12,%rdx
  401748:	bf 01 00 00 00       	mov    $0x1,%edi
  40174d:	31 c0                	xor    %eax,%eax
  40174f:	48 8d 35 f1 19 00 00 	lea    0x19f1(%rip),%rsi        # 403147 <_IO_stdin_used+0x147>
  401756:	e8 45 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  40175b:	48 89 e8             	mov    %rbp,%rax
  40175e:	bf 01 00 00 00       	mov    $0x1,%edi
  401763:	48 8d 35 f5 19 00 00 	lea    0x19f5(%rip),%rsi        # 40315f <_IO_stdin_used+0x15f>
  40176a:	48 99                	cqto
  40176c:	49 f7 fc             	idiv   %r12
  40176f:	49 89 c4             	mov    %rax,%r12
  401772:	48 89 c2             	mov    %rax,%rdx
  401775:	31 c0                	xor    %eax,%eax
  401777:	e8 24 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  40177c:	4c 89 e2             	mov    %r12,%rdx
  40177f:	bf 01 00 00 00       	mov    $0x1,%edi
  401784:	31 c0                	xor    %eax,%eax
  401786:	48 8d 35 5b 1a 00 00 	lea    0x1a5b(%rip),%rsi        # 4031e8 <_IO_stdin_used+0x1e8>
  40178d:	e8 0e f9 ff ff       	call   4010a0 <__printf_chk@plt>
  401792:	4c 89 e2             	mov    %r12,%rdx
  401795:	bf 01 00 00 00       	mov    $0x1,%edi
  40179a:	31 c0                	xor    %eax,%eax
  40179c:	48 8d 35 d7 19 00 00 	lea    0x19d7(%rip),%rsi        # 40317a <_IO_stdin_used+0x17a>
  4017a3:	4c 8d 25 37 19 00 00 	lea    0x1937(%rip),%r12        # 4030e1 <_IO_stdin_used+0xe1>
  4017aa:	e8 f1 f8 ff ff       	call   4010a0 <__printf_chk@plt>
  4017af:	48 8d 3d de 19 00 00 	lea    0x19de(%rip),%rdi        # 403194 <_IO_stdin_used+0x194>
  4017b6:	e8 85 f8 ff ff       	call   401040 <puts@plt>
  4017bb:	4c 89 e6             	mov    %r12,%rsi
  4017be:	bf 01 00 00 00       	mov    $0x1,%edi
  4017c3:	31 c0                	xor    %eax,%eax
  4017c5:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  4017cc:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4017d3:	e8 c8 f8 ff ff       	call   4010a0 <__printf_chk@plt>
  4017d8:	4c 89 e6             	mov    %r12,%rsi
  4017db:	bf 01 00 00 00       	mov    $0x1,%edi
  4017e0:	31 c0                	xor    %eax,%eax
  4017e2:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  4017e9:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4017f0:	e8 ab f8 ff ff       	call   4010a0 <__printf_chk@plt>
  4017f5:	4c 89 e6             	mov    %r12,%rsi
  4017f8:	bf 01 00 00 00       	mov    $0x1,%edi
  4017fd:	31 c0                	xor    %eax,%eax
  4017ff:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  401806:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  40180d:	e8 8e f8 ff ff       	call   4010a0 <__printf_chk@plt>
  401812:	4c 89 e6             	mov    %r12,%rsi
  401815:	bf 01 00 00 00       	mov    $0x1,%edi
  40181a:	31 c0                	xor    %eax,%eax
  40181c:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  401823:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  40182a:	e8 71 f8 ff ff       	call   4010a0 <__printf_chk@plt>
  40182f:	4c 89 e6             	mov    %r12,%rsi
  401832:	bf 01 00 00 00       	mov    $0x1,%edi
  401837:	31 c0                	xor    %eax,%eax
  401839:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401840:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  401847:	e8 54 f8 ff ff       	call   4010a0 <__printf_chk@plt>
  40184c:	4c 89 e6             	mov    %r12,%rsi
  40184f:	bf 01 00 00 00       	mov    $0x1,%edi
  401854:	31 c0                	xor    %eax,%eax
  401856:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  40185d:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401864:	e8 37 f8 ff ff       	call   4010a0 <__printf_chk@plt>
  401869:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  401870:	bf 01 00 00 00       	mov    $0x1,%edi
  401875:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  40187c:	48 8d 35 1e 19 00 00 	lea    0x191e(%rip),%rsi        # 4031a1 <_IO_stdin_used+0x1a1>
  401883:	31 c0                	xor    %eax,%eax
  401885:	e8 16 f8 ff ff       	call   4010a0 <__printf_chk@plt>
  40188a:	4c 89 ea             	mov    %r13,%rdx
  40188d:	bf 01 00 00 00       	mov    $0x1,%edi
  401892:	31 c0                	xor    %eax,%eax
  401894:	48 8d 35 0e 19 00 00 	lea    0x190e(%rip),%rsi        # 4031a9 <_IO_stdin_used+0x1a9>
  40189b:	e8 00 f8 ff ff       	call   4010a0 <__printf_chk@plt>
  4018a0:	48 89 e8             	mov    %rbp,%rax
  4018a3:	bf 01 00 00 00       	mov    $0x1,%edi
  4018a8:	48 8d 35 61 19 00 00 	lea    0x1961(%rip),%rsi        # 403210 <_IO_stdin_used+0x210>
  4018af:	48 99                	cqto
  4018b1:	49 f7 fd             	idiv   %r13
  4018b4:	48 89 c2             	mov    %rax,%rdx
  4018b7:	31 c0                	xor    %eax,%eax
  4018b9:	e8 e2 f7 ff ff       	call   4010a0 <__printf_chk@plt>
  4018be:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
  4018c3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4018cc:	75 14                	jne    4018e2 <main+0x802>
  4018ce:	48 81 c4 88 00 00 00 	add    $0x88,%rsp
  4018d5:	31 c0                	xor    %eax,%eax
  4018d7:	5b                   	pop    %rbx
  4018d8:	5d                   	pop    %rbp
  4018d9:	41 5c                	pop    %r12
  4018db:	41 5d                	pop    %r13
  4018dd:	41 5e                	pop    %r14
  4018df:	41 5f                	pop    %r15
  4018e1:	c3                   	ret
  4018e2:	e8 79 f7 ff ff       	call   401060 <__stack_chk_fail@plt>
  4018e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000004018f0 <set_fast_math>:
  4018f0:	f3 0f 1e fa          	endbr64
  4018f4:	0f ae 5c 24 fc       	stmxcsr -0x4(%rsp)
  4018f9:	81 4c 24 fc 40 80 00 00 	orl    $0x8040,-0x4(%rsp)
  401901:	0f ae 54 24 fc       	ldmxcsr -0x4(%rsp)
  401906:	c3                   	ret
  401907:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000401910 <_start>:
  401910:	f3 0f 1e fa          	endbr64
  401914:	31 ed                	xor    %ebp,%ebp
  401916:	49 89 d1             	mov    %rdx,%r9
  401919:	5e                   	pop    %rsi
  40191a:	48 89 e2             	mov    %rsp,%rdx
  40191d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401921:	50                   	push   %rax
  401922:	54                   	push   %rsp
  401923:	45 31 c0             	xor    %r8d,%r8d
  401926:	31 c9                	xor    %ecx,%ecx
  401928:	48 c7 c7 e0 10 40 00 	mov    $0x4010e0,%rdi
  40192f:	ff 15 bb 36 00 00    	call   *0x36bb(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  401935:	f4                   	hlt
  401936:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401940 <_dl_relocate_static_pie>:
  401940:	f3 0f 1e fa          	endbr64
  401944:	c3                   	ret
  401945:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40194f:	90                   	nop

0000000000401950 <deregister_tm_clones>:
  401950:	b8 10 50 40 00       	mov    $0x405010,%eax
  401955:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  40195b:	74 13                	je     401970 <deregister_tm_clones+0x20>
  40195d:	b8 00 00 00 00       	mov    $0x0,%eax
  401962:	48 85 c0             	test   %rax,%rax
  401965:	74 09                	je     401970 <deregister_tm_clones+0x20>
  401967:	bf 10 50 40 00       	mov    $0x405010,%edi
  40196c:	ff e0                	jmp    *%rax
  40196e:	66 90                	xchg   %ax,%ax
  401970:	c3                   	ret
  401971:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40197c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401980 <register_tm_clones>:
  401980:	be 10 50 40 00       	mov    $0x405010,%esi
  401985:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  40198c:	48 89 f0             	mov    %rsi,%rax
  40198f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401993:	48 c1 f8 03          	sar    $0x3,%rax
  401997:	48 01 c6             	add    %rax,%rsi
  40199a:	48 d1 fe             	sar    %rsi
  40199d:	74 11                	je     4019b0 <register_tm_clones+0x30>
  40199f:	b8 00 00 00 00       	mov    $0x0,%eax
  4019a4:	48 85 c0             	test   %rax,%rax
  4019a7:	74 07                	je     4019b0 <register_tm_clones+0x30>
  4019a9:	bf 10 50 40 00       	mov    $0x405010,%edi
  4019ae:	ff e0                	jmp    *%rax
  4019b0:	c3                   	ret
  4019b1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4019bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004019c0 <__do_global_dtors_aux>:
  4019c0:	f3 0f 1e fa          	endbr64
  4019c4:	80 3d 45 36 00 00 00 	cmpb   $0x0,0x3645(%rip)        # 405010 <__TMC_END__>
  4019cb:	75 13                	jne    4019e0 <__do_global_dtors_aux+0x20>
  4019cd:	55                   	push   %rbp
  4019ce:	48 89 e5             	mov    %rsp,%rbp
  4019d1:	e8 7a ff ff ff       	call   401950 <deregister_tm_clones>
  4019d6:	c6 05 33 36 00 00 01 	movb   $0x1,0x3633(%rip)        # 405010 <__TMC_END__>
  4019dd:	5d                   	pop    %rbp
  4019de:	c3                   	ret
  4019df:	90                   	nop
  4019e0:	c3                   	ret
  4019e1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4019ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004019f0 <frame_dummy>:
  4019f0:	f3 0f 1e fa          	endbr64
  4019f4:	eb 8a                	jmp    401980 <register_tm_clones>
  4019f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401a00 <pollthreads>:
  401a00:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
  401a04:	49 89 f9             	mov    %rdi,%r9
  401a07:	7e 77                	jle    401a80 <pollthreads+0x80>
  401a09:	49 8b 41 30          	mov    0x30(%r9),%rax
  401a0d:	55                   	push   %rbp
  401a0e:	49 89 f2             	mov    %rsi,%r10
  401a11:	49 89 d3             	mov    %rdx,%r11
  401a14:	53                   	push   %rbx
  401a15:	48 89 cf             	mov    %rcx,%rdi
  401a18:	48 8b 98 20 04 00 00 	mov    0x420(%rax),%rbx
  401a1f:	b8 01 00 00 00       	mov    $0x1,%eax
  401a24:	0f 1f 40 00          	nopl   0x0(%rax)
  401a28:	48 63 d0             	movslq %eax,%rdx
  401a2b:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
  401a2e:	85 d2                	test   %edx,%edx
  401a30:	40 0f 94 c6          	sete   %sil
  401a34:	f6 c2 04             	test   $0x4,%dl
  401a37:	75 05                	jne    401a3e <pollthreads+0x3e>
  401a39:	40 84 f6             	test   %sil,%sil
  401a3c:	74 0d                	je     401a4b <pollthreads+0x4b>
  401a3e:	49 63 08             	movslq (%r8),%rcx
  401a41:	8d 69 01             	lea    0x1(%rcx),%ebp
  401a44:	41 89 28             	mov    %ebp,(%r8)
  401a47:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
  401a4b:	83 e2 08             	and    $0x8,%edx
  401a4e:	75 05                	jne    401a55 <pollthreads+0x55>
  401a50:	40 84 f6             	test   %sil,%sil
  401a53:	74 1b                	je     401a70 <pollthreads+0x70>
  401a55:	48 63 17             	movslq (%rdi),%rdx
  401a58:	8d 4a 01             	lea    0x1(%rdx),%ecx
  401a5b:	89 0f                	mov    %ecx,(%rdi)
  401a5d:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  401a61:	83 c0 01             	add    $0x1,%eax
  401a64:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401a68:	7f be                	jg     401a28 <pollthreads+0x28>
  401a6a:	31 c0                	xor    %eax,%eax
  401a6c:	5b                   	pop    %rbx
  401a6d:	5d                   	pop    %rbp
  401a6e:	c3                   	ret
  401a6f:	90                   	nop
  401a70:	83 c0 01             	add    $0x1,%eax
  401a73:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401a77:	7f af                	jg     401a28 <pollthreads+0x28>
  401a79:	31 c0                	xor    %eax,%eax
  401a7b:	5b                   	pop    %rbx
  401a7c:	5d                   	pop    %rbp
  401a7d:	c3                   	ret
  401a7e:	66 90                	xchg   %ax,%ax
  401a80:	31 c0                	xor    %eax,%eax
  401a82:	c3                   	ret
  401a83:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401a8e:	66 90                	xchg   %ax,%ax

0000000000401a90 <findavailable>:
  401a90:	49 89 fb             	mov    %rdi,%r11
  401a93:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
  401a9a:	44 8b 02             	mov    (%rdx),%r8d
  401a9d:	48 83 c7 01          	add    $0x1,%rdi
  401aa1:	48 85 ff             	test   %rdi,%rdi
  401aa4:	7e 66                	jle    401b0c <findavailable+0x7c>
  401aa6:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  401aad:	31 c9                	xor    %ecx,%ecx
  401aaf:	45 31 c9             	xor    %r9d,%r9d
  401ab2:	31 c0                	xor    %eax,%eax
  401ab4:	eb 18                	jmp    401ace <findavailable+0x3e>
  401ab6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401ac0:	83 c1 01             	add    $0x1,%ecx
  401ac3:	48 63 c1             	movslq %ecx,%rax
  401ac6:	49 89 c1             	mov    %rax,%r9
  401ac9:	48 39 f8             	cmp    %rdi,%rax
  401acc:	7d 3e                	jge    401b0c <findavailable+0x7c>
  401ace:	48 c1 e0 05          	shl    $0x5,%rax
  401ad2:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401ad8:	75 e6                	jne    401ac0 <findavailable+0x30>
  401ada:	49 63 c0             	movslq %r8d,%rax
  401add:	41 83 c0 01          	add    $0x1,%r8d
  401ae1:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
  401ae5:	44 89 02             	mov    %r8d,(%rdx)
  401ae8:	41 8b 43 68          	mov    0x68(%r11),%eax
  401aec:	01 c0                	add    %eax,%eax
  401aee:	41 39 c0             	cmp    %eax,%r8d
  401af1:	74 19                	je     401b0c <findavailable+0x7c>
  401af3:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  401afa:	83 c1 01             	add    $0x1,%ecx
  401afd:	48 63 c1             	movslq %ecx,%rax
  401b00:	48 83 c7 01          	add    $0x1,%rdi
  401b04:	49 89 c1             	mov    %rax,%r9
  401b07:	48 39 f8             	cmp    %rdi,%rax
  401b0a:	7c c2                	jl     401ace <findavailable+0x3e>
  401b0c:	31 c0                	xor    %eax,%eax
  401b0e:	45 85 c0             	test   %r8d,%r8d
  401b11:	0f 94 c0             	sete   %al
  401b14:	c3                   	ret
  401b15:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401b20 <singlewriter3>:
  401b20:	c3                   	ret
  401b21:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401b2c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401b30 <singlewriter2>:
  401b30:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  401b36:	85 c0                	test   %eax,%eax
  401b38:	74 1e                	je     401b58 <singlewriter2+0x28>
  401b3a:	41 54                	push   %r12
  401b3c:	99                   	cltd
  401b3d:	55                   	push   %rbp
  401b3e:	53                   	push   %rbx
  401b3f:	8b 77 68             	mov    0x68(%rdi),%esi
  401b42:	48 89 fb             	mov    %rdi,%rbx
  401b45:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401b48:	f7 f9                	idiv   %ecx
  401b4a:	85 d2                	test   %edx,%edx
  401b4c:	74 12                	je     401b60 <singlewriter2+0x30>
  401b4e:	5b                   	pop    %rbx
  401b4f:	5d                   	pop    %rbp
  401b50:	41 5c                	pop    %r12
  401b52:	c3                   	ret
  401b53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401b58:	c3                   	ret
  401b59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401b60:	48 63 6f 64          	movslq 0x64(%rdi),%rbp
  401b64:	48 c1 e5 0a          	shl    $0xa,%rbp
  401b68:	48 03 6f 30          	add    0x30(%rdi),%rbp
  401b6c:	bf 04 00 00 00       	mov    $0x4,%edi
  401b71:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401b78:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401b7c:	49 c1 e4 04          	shl    $0x4,%r12
  401b80:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
  401b87:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401b8c:	e8 bf f4 ff ff       	call   401050 <clock_gettime@plt>
  401b91:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401b97:	83 c0 01             	add    $0x1,%eax
  401b9a:	99                   	cltd
  401b9b:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
  401ba1:	8b 43 64             	mov    0x64(%rbx),%eax
  401ba4:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
  401baa:	41 89 04 24          	mov    %eax,(%r12)
  401bae:	48 8b 05 83 16 00 00 	mov    0x1683(%rip),%rax        # 403238 <_IO_stdin_used+0x238>
  401bb5:	49 89 44 24 20       	mov    %rax,0x20(%r12)
  401bba:	5b                   	pop    %rbx
  401bbb:	5d                   	pop    %rbp
  401bbc:	41 5c                	pop    %r12
  401bbe:	c3                   	ret
  401bbf:	90                   	nop

0000000000401bc0 <singlewriter>:
  401bc0:	41 55                	push   %r13
  401bc2:	49 89 d5             	mov    %rdx,%r13
  401bc5:	41 54                	push   %r12
  401bc7:	49 89 cc             	mov    %rcx,%r12
  401bca:	55                   	push   %rbp
  401bcb:	4d 89 e0             	mov    %r12,%r8
  401bce:	48 89 fd             	mov    %rdi,%rbp
  401bd1:	53                   	push   %rbx
  401bd2:	48 89 f3             	mov    %rsi,%rbx
  401bd5:	48 83 ec 28          	sub    $0x28,%rsp
  401bd9:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
  401bdd:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401be6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401beb:	31 c0                	xor    %eax,%eax
  401bed:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  401bf5:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  401bfb:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  401c03:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  401c0b:	83 c0 01             	add    $0x1,%eax
  401c0e:	99                   	cltd
  401c0f:	f7 7f 68             	idivl  0x68(%rdi)
  401c12:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  401c18:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401c1d:	4c 89 e9             	mov    %r13,%rcx
  401c20:	e8 6b fe ff ff       	call   401a90 <findavailable>
  401c25:	83 f8 01             	cmp    $0x1,%eax
  401c28:	0f 84 3c 01 00 00    	je     401d6a <singlewriter+0x1aa>
  401c2e:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401c33:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401c38:	4c 89 e2             	mov    %r12,%rdx
  401c3b:	4c 89 ee             	mov    %r13,%rsi
  401c3e:	48 89 ef             	mov    %rbp,%rdi
  401c41:	e8 ba fd ff ff       	call   401a00 <pollthreads>
  401c46:	4c 63 44 24 0c       	movslq 0xc(%rsp),%r8
  401c4b:	45 85 c0             	test   %r8d,%r8d
  401c4e:	0f 8e 3d 01 00 00    	jle    401d91 <singlewriter+0x1d1>
  401c54:	44 8b 4c 24 14       	mov    0x14(%rsp),%r9d
  401c59:	31 c9                	xor    %ecx,%ecx
  401c5b:	eb 58                	jmp    401cb5 <singlewriter+0xf5>
  401c5d:	0f 1f 00             	nopl   (%rax)
  401c60:	48 8b 04 cb          	mov    (%rbx,%rcx,8),%rax
  401c64:	49 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%rdx
  401c69:	8d 71 01             	lea    0x1(%rcx),%esi
  401c6c:	48 83 c1 01          	add    $0x1,%rcx
  401c70:	48 c1 e0 05          	shl    $0x5,%rax
  401c74:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
  401c7b:	48 89 d7             	mov    %rdx,%rdi
  401c7e:	48 c1 e2 0a          	shl    $0xa,%rdx
  401c82:	66 0f 6e 00          	movd   (%rax),%xmm0
  401c86:	66 0f 6e 48 08       	movd   0x8(%rax),%xmm1
  401c8b:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
  401c92:	48 03 55 30          	add    0x30(%rbp),%rdx
  401c96:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
  401c9a:	48 89 82 a8 00 00 00 	mov    %rax,0xa8(%rdx)
  401ca1:	89 78 14             	mov    %edi,0x14(%rax)
  401ca4:	83 8a c8 00 00 00 10 	orl    $0x10,0xc8(%rdx)
  401cab:	66 0f d6 42 14       	movq   %xmm0,0x14(%rdx)
  401cb0:	49 39 c8             	cmp    %rcx,%r8
  401cb3:	74 07                	je     401cbc <singlewriter+0xfc>
  401cb5:	89 ce                	mov    %ecx,%esi
  401cb7:	4c 39 c9             	cmp    %r9,%rcx
  401cba:	75 a4                	jne    401c60 <singlewriter+0xa0>
  401cbc:	44 8b 4c 24 10       	mov    0x10(%rsp),%r9d
  401cc1:	45 85 c9             	test   %r9d,%r9d
  401cc4:	7e 68                	jle    401d2e <singlewriter+0x16e>
  401cc6:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
  401ccb:	41 01 f1             	add    %esi,%r9d
  401cce:	eb 59                	jmp    401d29 <singlewriter+0x169>
  401cd0:	8d 7e 01             	lea    0x1(%rsi),%edi
  401cd3:	48 63 f6             	movslq %esi,%rsi
  401cd6:	49 63 14 24          	movslq (%r12),%rdx
  401cda:	49 83 c4 04          	add    $0x4,%r12
  401cde:	48 8b 04 f3          	mov    (%rbx,%rsi,8),%rax
  401ce2:	48 89 d1             	mov    %rdx,%rcx
  401ce5:	48 c1 e2 0a          	shl    $0xa,%rdx
  401ce9:	48 03 55 30          	add    0x30(%rbp),%rdx
  401ced:	48 c1 e0 05          	shl    $0x5,%rax
  401cf1:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
  401cf8:	66 0f 6e 00          	movd   (%rax),%xmm0
  401cfc:	66 0f 6e 50 08       	movd   0x8(%rax),%xmm2
  401d01:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
  401d08:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
  401d0f:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
  401d13:	89 48 14             	mov    %ecx,0x14(%rax)
  401d16:	83 8a c8 00 00 00 20 	orl    $0x20,0xc8(%rdx)
  401d1d:	66 0f d6 42 40       	movq   %xmm0,0x40(%rdx)
  401d22:	44 39 cf             	cmp    %r9d,%edi
  401d25:	74 07                	je     401d2e <singlewriter+0x16e>
  401d27:	89 fe                	mov    %edi,%esi
  401d29:	41 39 f0             	cmp    %esi,%r8d
  401d2c:	75 a2                	jne    401cd0 <singlewriter+0x110>
  401d2e:	8b 7d 68             	mov    0x68(%rbp),%edi
  401d31:	85 ff                	test   %edi,%edi
  401d33:	7e 33                	jle    401d68 <singlewriter+0x1a8>
  401d35:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401d39:	31 d2                	xor    %edx,%edx
  401d3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401d40:	48 63 ca             	movslq %edx,%rcx
  401d43:	48 89 c8             	mov    %rcx,%rax
  401d46:	48 c1 e0 0a          	shl    $0xa,%rax
  401d4a:	4c 01 c0             	add    %r8,%rax
  401d4d:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401d53:	85 f6                	test   %esi,%esi
  401d55:	74 31                	je     401d88 <singlewriter+0x1c8>
  401d57:	48 8b 40 20          	mov    0x20(%rax),%rax
  401d5b:	83 c2 01             	add    $0x1,%edx
  401d5e:	89 34 88             	mov    %esi,(%rax,%rcx,4)
  401d61:	8b 7d 68             	mov    0x68(%rbp),%edi
  401d64:	39 fa                	cmp    %edi,%edx
  401d66:	7c d8                	jl     401d40 <singlewriter+0x180>
  401d68:	31 c0                	xor    %eax,%eax
  401d6a:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401d6f:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401d78:	75 1e                	jne    401d98 <singlewriter+0x1d8>
  401d7a:	48 83 c4 28          	add    $0x28,%rsp
  401d7e:	5b                   	pop    %rbx
  401d7f:	5d                   	pop    %rbp
  401d80:	41 5c                	pop    %r12
  401d82:	41 5d                	pop    %r13
  401d84:	c3                   	ret
  401d85:	0f 1f 00             	nopl   (%rax)
  401d88:	83 c2 01             	add    $0x1,%edx
  401d8b:	39 fa                	cmp    %edi,%edx
  401d8d:	7c b1                	jl     401d40 <singlewriter+0x180>
  401d8f:	eb d7                	jmp    401d68 <singlewriter+0x1a8>
  401d91:	31 f6                	xor    %esi,%esi
  401d93:	e9 24 ff ff ff       	jmp    401cbc <singlewriter+0xfc>
  401d98:	e8 c3 f2 ff ff       	call   401060 <__stack_chk_fail@plt>
  401d9d:	0f 1f 00             	nopl   (%rax)

0000000000401da0 <threadwork>:
  401da0:	41 54                	push   %r12
  401da2:	55                   	push   %rbp
  401da3:	53                   	push   %rbx
  401da4:	48 89 fb             	mov    %rdi,%rbx
  401da7:	48 83 ec 20          	sub    $0x20,%rsp
  401dab:	8b 6f 68             	mov    0x68(%rdi),%ebp
  401dae:	bf 04 00 00 00       	mov    $0x4,%edi
  401db3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401dbc:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401dc1:	31 c0                	xor    %eax,%eax
  401dc3:	48 89 e6             	mov    %rsp,%rsi
  401dc6:	e8 85 f2 ff ff       	call   401050 <clock_gettime@plt>
  401dcb:	83 7b 5c 02          	cmpl   $0x2,0x5c(%rbx)
  401dcf:	48 63 cd             	movslq %ebp,%rcx
  401dd2:	0f 84 a8 01 00 00    	je     401f80 <threadwork+0x1e0>
  401dd8:	44 8b 8b 8c 03 00 00 	mov    0x38c(%rbx),%r9d
  401ddf:	4c 8b 53 28          	mov    0x28(%rbx),%r10
  401de3:	44 89 c8             	mov    %r9d,%eax
  401de6:	49 8b b2 80 03 00 00 	mov    0x380(%r10),%rsi
  401ded:	c1 e0 07             	shl    $0x7,%eax
  401df0:	48 98                	cltq
  401df2:	48 8b 04 c6          	mov    (%rsi,%rax,8),%rax
  401df6:	48 99                	cqto
  401df8:	48 f7 f9             	idiv   %rcx
  401dfb:	48 63 93 88 03 00 00 	movslq 0x388(%rbx),%rdx
  401e02:	48 39 c2             	cmp    %rax,%rdx
  401e05:	74 0a                	je     401e11 <threadwork+0x71>
  401e07:	c7 83 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rbx)
  401e11:	8b 8b 90 03 00 00    	mov    0x390(%rbx),%ecx
  401e17:	89 83 88 03 00 00    	mov    %eax,0x388(%rbx)
  401e1d:	48 8b bb 48 03 00 00 	mov    0x348(%rbx),%rdi
  401e24:	89 c8                	mov    %ecx,%eax
  401e26:	c1 e0 07             	shl    $0x7,%eax
  401e29:	48 98                	cltq
  401e2b:	48 8b 14 c6          	mov    (%rsi,%rax,8),%rdx
  401e2f:	48 63 c1             	movslq %ecx,%rax
  401e32:	4c 8d 04 40          	lea    (%rax,%rax,2),%r8
  401e36:	49 c1 e0 02          	shl    $0x2,%r8
  401e3a:	4c 01 c7             	add    %r8,%rdi
  401e3d:	8b 07                	mov    (%rdi),%eax
  401e3f:	48 85 d2             	test   %rdx,%rdx
  401e42:	74 0c                	je     401e50 <threadwork+0xb0>
  401e44:	48 63 f0             	movslq %eax,%rsi
  401e47:	48 39 d6             	cmp    %rdx,%rsi
  401e4a:	0f 8d cc 00 00 00    	jge    401f1c <threadwork+0x17c>
  401e50:	99                   	cltd
  401e51:	8b 77 04             	mov    0x4(%rdi),%esi
  401e54:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
  401e59:	f7 fd                	idiv   %ebp
  401e5b:	41 89 f4             	mov    %esi,%r12d
  401e5e:	83 e8 01             	sub    $0x1,%eax
  401e61:	48 63 d0             	movslq %eax,%rdx
  401e64:	41 89 c3             	mov    %eax,%r11d
  401e67:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401e6e:	41 c1 fb 1f          	sar    $0x1f,%r11d
  401e72:	48 c1 ea 20          	shr    $0x20,%rdx
  401e76:	01 c2                	add    %eax,%edx
  401e78:	c1 fa 07             	sar    $0x7,%edx
  401e7b:	44 29 da             	sub    %r11d,%edx
  401e7e:	41 89 d3             	mov    %edx,%r11d
  401e81:	41 c1 e3 08          	shl    $0x8,%r11d
  401e85:	41 29 d3             	sub    %edx,%r11d
  401e88:	31 d2                	xor    %edx,%edx
  401e8a:	44 29 d8             	sub    %r11d,%eax
  401e8d:	41 89 cb             	mov    %ecx,%r11d
  401e90:	48 98                	cltq
  401e92:	48 85 c0             	test   %rax,%rax
  401e95:	48 0f 48 c2          	cmovs  %rdx,%rax
  401e99:	48 63 d6             	movslq %esi,%rdx
  401e9c:	41 c1 fc 1f          	sar    $0x1f,%r12d
  401ea0:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401ea7:	41 c1 e3 18          	shl    $0x18,%r11d
  401eab:	48 c1 e0 10          	shl    $0x10,%rax
  401eaf:	48 c1 ea 20          	shr    $0x20,%rdx
  401eb3:	01 f2                	add    %esi,%edx
  401eb5:	c1 fa 07             	sar    $0x7,%edx
  401eb8:	44 29 e2             	sub    %r12d,%edx
  401ebb:	41 89 d4             	mov    %edx,%r12d
  401ebe:	41 c1 e4 08          	shl    $0x8,%r12d
  401ec2:	41 29 d4             	sub    %edx,%r12d
  401ec5:	89 f2                	mov    %esi,%edx
  401ec7:	44 29 e2             	sub    %r12d,%edx
  401eca:	41 09 d3             	or     %edx,%r11d
  401ecd:	4d 63 db             	movslq %r11d,%r11
  401ed0:	4c 09 d8             	or     %r11,%rax
  401ed3:	49 03 42 70          	add    0x70(%r10),%rax
  401ed7:	80 38 ff             	cmpb   $0xff,(%rax)
  401eda:	74 25                	je     401f01 <threadwork+0x161>
  401edc:	48 83 83 98 03 00 00 01 	addq   $0x1,0x398(%rbx)
  401ee4:	c6 00 ff             	movb   $0xff,(%rax)
  401ee7:	48 8b bb 48 03 00 00 	mov    0x348(%rbx),%rdi
  401eee:	8b 8b 90 03 00 00    	mov    0x390(%rbx),%ecx
  401ef4:	44 8b 8b 8c 03 00 00 	mov    0x38c(%rbx),%r9d
  401efb:	4c 01 c7             	add    %r8,%rdi
  401efe:	8b 77 04             	mov    0x4(%rdi),%esi
  401f01:	39 f5                	cmp    %esi,%ebp
  401f03:	7e 09                	jle    401f0e <threadwork+0x16e>
  401f05:	83 c6 01             	add    $0x1,%esi
  401f08:	83 07 01             	addl   $0x1,(%rdi)
  401f0b:	89 77 04             	mov    %esi,0x4(%rdi)
  401f0e:	39 f5                	cmp    %esi,%ebp
  401f10:	74 2e                	je     401f40 <threadwork+0x1a0>
  401f12:	41 39 c9             	cmp    %ecx,%r9d
  401f15:	74 59                	je     401f70 <threadwork+0x1d0>
  401f17:	83 f9 05             	cmp    $0x5,%ecx
  401f1a:	74 44                	je     401f60 <threadwork+0x1c0>
  401f1c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  401f21:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401f2a:	0f 85 28 01 00 00    	jne    402058 <threadwork+0x2b8>
  401f30:	48 83 c4 20          	add    $0x20,%rsp
  401f34:	31 c0                	xor    %eax,%eax
  401f36:	5b                   	pop    %rbx
  401f37:	5d                   	pop    %rbp
  401f38:	41 5c                	pop    %r12
  401f3a:	c3                   	ret
  401f3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401f40:	83 c1 01             	add    $0x1,%ecx
  401f43:	89 8b 90 03 00 00    	mov    %ecx,0x390(%rbx)
  401f49:	c7 47 04 00 00 00 00 	movl   $0x0,0x4(%rdi)
  401f50:	41 39 c9             	cmp    %ecx,%r9d
  401f53:	75 c2                	jne    401f17 <threadwork+0x177>
  401f55:	eb 19                	jmp    401f70 <threadwork+0x1d0>
  401f57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  401f60:	c7 83 90 03 00 00 01 00 00 00 	movl   $0x1,0x390(%rbx)
  401f6a:	eb b0                	jmp    401f1c <threadwork+0x17c>
  401f6c:	0f 1f 40 00          	nopl   0x0(%rax)
  401f70:	83 c1 01             	add    $0x1,%ecx
  401f73:	89 8b 90 03 00 00    	mov    %ecx,0x390(%rbx)
  401f79:	83 f9 05             	cmp    $0x5,%ecx
  401f7c:	75 9e                	jne    401f1c <threadwork+0x17c>
  401f7e:	eb e0                	jmp    401f60 <threadwork+0x1c0>
  401f80:	8b b3 8c 03 00 00    	mov    0x38c(%rbx),%esi
  401f86:	48 8b 7b 28          	mov    0x28(%rbx),%rdi
  401f8a:	44 8b 43 64          	mov    0x64(%rbx),%r8d
  401f8e:	89 f0                	mov    %esi,%eax
  401f90:	48 8b 97 80 03 00 00 	mov    0x380(%rdi),%rdx
  401f97:	c1 e6 18             	shl    $0x18,%esi
  401f9a:	c1 e0 07             	shl    $0x7,%eax
  401f9d:	48 98                	cltq
  401f9f:	48 8b 04 c2          	mov    (%rdx,%rax,8),%rax
  401fa3:	48 99                	cqto
  401fa5:	48 f7 f9             	idiv   %rcx
  401fa8:	48 ba 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%rdx
  401fb2:	49 89 c1             	mov    %rax,%r9
  401fb5:	48 f7 ea             	imul   %rdx
  401fb8:	4c 89 c8             	mov    %r9,%rax
  401fbb:	48 c1 f8 3f          	sar    $0x3f,%rax
  401fbf:	4c 01 ca             	add    %r9,%rdx
  401fc2:	48 c1 fa 07          	sar    $0x7,%rdx
  401fc6:	48 29 c2             	sub    %rax,%rdx
  401fc9:	48 89 d0             	mov    %rdx,%rax
  401fcc:	48 c1 e0 08          	shl    $0x8,%rax
  401fd0:	48 29 d0             	sub    %rdx,%rax
  401fd3:	48 63 93 80 01 00 00 	movslq 0x180(%rbx),%rdx
  401fda:	49 29 c1             	sub    %rax,%r9
  401fdd:	48 89 d0             	mov    %rdx,%rax
  401fe0:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  401fe7:	41 c1 e1 10          	shl    $0x10,%r9d
  401feb:	41 89 c2             	mov    %eax,%r10d
  401fee:	41 c1 fa 1f          	sar    $0x1f,%r10d
  401ff2:	48 c1 ea 20          	shr    $0x20,%rdx
  401ff6:	01 c2                	add    %eax,%edx
  401ff8:	c1 fa 07             	sar    $0x7,%edx
  401ffb:	44 29 d2             	sub    %r10d,%edx
  401ffe:	41 89 d2             	mov    %edx,%r10d
  402001:	41 c1 e2 08          	shl    $0x8,%r10d
  402005:	41 29 d2             	sub    %edx,%r10d
  402008:	44 29 d0             	sub    %r10d,%eax
  40200b:	09 c6                	or     %eax,%esi
  40200d:	41 09 f1             	or     %esi,%r9d
  402010:	4d 63 c9             	movslq %r9d,%r9
  402013:	4c 03 4f 70          	add    0x70(%rdi),%r9
  402017:	41 80 39 ff          	cmpb   $0xff,(%r9)
  40201b:	74 05                	je     402022 <threadwork+0x282>
  40201d:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
  402022:	45 88 01             	mov    %r8b,(%r9)
  402025:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
  40202b:	83 c0 01             	add    $0x1,%eax
  40202e:	99                   	cltd
  40202f:	f7 fd                	idiv   %ebp
  402031:	8b 83 8c 03 00 00    	mov    0x38c(%rbx),%eax
  402037:	c1 e0 07             	shl    $0x7,%eax
  40203a:	48 98                	cltq
  40203c:	89 93 80 01 00 00    	mov    %edx,0x180(%rbx)
  402042:	48 8b 53 28          	mov    0x28(%rbx),%rdx
  402046:	48 8b 92 80 03 00 00 	mov    0x380(%rdx),%rdx
  40204d:	f0 48 83 04 c2 01    	lock addq $0x1,(%rdx,%rax,8)
  402053:	e9 80 fd ff ff       	jmp    401dd8 <threadwork+0x38>
  402058:	e8 03 f0 ff ff       	call   401060 <__stack_chk_fail@plt>
  40205d:	0f 1f 00             	nopl   (%rax)

0000000000402060 <work>:
  402060:	53                   	push   %rbx
  402061:	8b 57 64             	mov    0x64(%rdi),%edx
  402064:	48 89 fb             	mov    %rdi,%rbx
  402067:	48 8d 35 96 0f 00 00 	lea    0xf96(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  40206e:	bf 01 00 00 00       	mov    $0x1,%edi
  402073:	31 c0                	xor    %eax,%eax
  402075:	e8 26 f0 ff ff       	call   4010a0 <__printf_chk@plt>
  40207a:	8b 53 5c             	mov    0x5c(%rbx),%edx
  40207d:	85 d2                	test   %edx,%edx
  40207f:	7e 16                	jle    402097 <work+0x37>
  402081:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  402088:	48 89 df             	mov    %rbx,%rdi
  40208b:	e8 10 fd ff ff       	call   401da0 <threadwork>
  402090:	8b 43 5c             	mov    0x5c(%rbx),%eax
  402093:	85 c0                	test   %eax,%eax
  402095:	7f f1                	jg     402088 <work+0x28>
  402097:	8b 53 64             	mov    0x64(%rbx),%edx
  40209a:	48 8d 35 76 0f 00 00 	lea    0xf76(%rip),%rsi        # 403017 <_IO_stdin_used+0x17>
  4020a1:	bf 01 00 00 00       	mov    $0x1,%edi
  4020a6:	31 c0                	xor    %eax,%eax
  4020a8:	e8 f3 ef ff ff       	call   4010a0 <__printf_chk@plt>
  4020ad:	5b                   	pop    %rbx
  4020ae:	c3                   	ret
  4020af:	90                   	nop

00000000004020b0 <work2>:
  4020b0:	eb 0b                	jmp    4020bd <work2+0xd>
  4020b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  4020b8:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  4020bd:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  4020c1:	74 f5                	je     4020b8 <work2+0x8>
  4020c3:	c3                   	ret

Disassembly of section .fini:

00000000004020c4 <_fini>:
  4020c4:	f3 0f 1e fa          	endbr64
  4020c8:	48 83 ec 08          	sub    $0x8,%rsp
  4020cc:	48 83 c4 08          	add    $0x8,%rsp
  4020d0:	c3                   	ret
