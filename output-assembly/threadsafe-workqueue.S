
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

0000000000401020 <pthread_setaffinity_np@plt-0x10>:
  401020:	ff 35 72 2f 00 00    	push   0x2f72(%rip)        # 403f98 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 74 2f 00 00    	jmp    *0x2f74(%rip)        # 403fa0 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <pthread_setaffinity_np@plt>:
  401030:	ff 25 72 2f 00 00    	jmp    *0x2f72(%rip)        # 403fa8 <pthread_setaffinity_np@GLIBC_2.34>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <puts@plt>:
  401040:	ff 25 6a 2f 00 00    	jmp    *0x2f6a(%rip)        # 403fb0 <puts@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <clock_gettime@plt>:
  401050:	ff 25 62 2f 00 00    	jmp    *0x2f62(%rip)        # 403fb8 <clock_gettime@GLIBC_2.17>
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
  4010c0:	41 57                	push   %r15
  4010c2:	ba 08 00 00 00       	mov    $0x8,%edx
  4010c7:	bf 01 00 00 00       	mov    $0x1,%edi
  4010cc:	48 8d 35 62 0f 00 00 	lea    0xf62(%rip),%rsi        # 402035 <_IO_stdin_used+0x35>
  4010d3:	41 56                	push   %r14
  4010d5:	41 55                	push   %r13
  4010d7:	41 54                	push   %r12
  4010d9:	55                   	push   %rbp
  4010da:	53                   	push   %rbx
  4010db:	48 83 ec 78          	sub    $0x78,%rsp
  4010df:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4010e8:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  4010ed:	31 c0                	xor    %eax,%eax
  4010ef:	e8 9c ff ff ff       	call   401090 <__printf_chk@plt>
  4010f4:	ba 04 00 00 00       	mov    $0x4,%edx
  4010f9:	48 8d 35 47 0f 00 00 	lea    0xf47(%rip),%rsi        # 402047 <_IO_stdin_used+0x47>
  401100:	31 c0                	xor    %eax,%eax
  401102:	bf 01 00 00 00       	mov    $0x1,%edi
  401107:	e8 84 ff ff ff       	call   401090 <__printf_chk@plt>
  40110c:	ba 20 00 00 00       	mov    $0x20,%edx
  401111:	48 8d 35 2b 0f 00 00 	lea    0xf2b(%rip),%rsi        # 402043 <_IO_stdin_used+0x43>
  401118:	31 c0                	xor    %eax,%eax
  40111a:	bf 01 00 00 00       	mov    $0x1,%edi
  40111f:	e8 6c ff ff ff       	call   401090 <__printf_chk@plt>
  401124:	ba 08 00 00 00       	mov    $0x8,%edx
  401129:	48 8d 35 26 0f 00 00 	lea    0xf26(%rip),%rsi        # 402056 <_IO_stdin_used+0x56>
  401130:	31 c0                	xor    %eax,%eax
  401132:	bf 01 00 00 00       	mov    $0x1,%edi
  401137:	e8 54 ff ff ff       	call   401090 <__printf_chk@plt>
  40113c:	be 08 00 00 00       	mov    $0x8,%esi
  401141:	bf 08 00 00 00       	mov    $0x8,%edi
  401146:	e8 35 ff ff ff       	call   401080 <calloc@plt>
  40114b:	be 38 00 00 00       	mov    $0x38,%esi
  401150:	bf 08 00 00 00       	mov    $0x8,%edi
  401155:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  40115a:	e8 21 ff ff ff       	call   401080 <calloc@plt>
  40115f:	be 80 0a 00 00       	mov    $0xa80,%esi
  401164:	bf 01 00 00 00       	mov    $0x1,%edi
  401169:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  40116e:	e8 0d ff ff ff       	call   401080 <calloc@plt>
  401173:	be 38 00 00 00       	mov    $0x38,%esi
  401178:	bf f4 01 00 00       	mov    $0x1f4,%edi
  40117d:	48 89 c3             	mov    %rax,%rbx
  401180:	e8 fb fe ff ff       	call   401080 <calloc@plt>
  401185:	ba f4 01 00 00       	mov    $0x1f4,%edx
  40118a:	bf 01 00 00 00       	mov    $0x1,%edi
  40118f:	48 8d 35 d5 0e 00 00 	lea    0xed5(%rip),%rsi        # 40206b <_IO_stdin_used+0x6b>
  401196:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  40119b:	31 c0                	xor    %eax,%eax
  40119d:	e8 ee fe ff ff       	call   401090 <__printf_chk@plt>
  4011a2:	be 20 00 00 00       	mov    $0x20,%esi
  4011a7:	bf f4 01 00 00       	mov    $0x1f4,%edi
  4011ac:	e8 cf fe ff ff       	call   401080 <calloc@plt>
  4011b1:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  4011b6:	48 89 c2             	mov    %rax,%rdx
  4011b9:	31 c0                	xor    %eax,%eax
  4011bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4011c0:	89 c1                	mov    %eax,%ecx
  4011c2:	66 48 0f 6e c0       	movq   %rax,%xmm0
  4011c7:	48 83 c0 01          	add    $0x1,%rax
  4011cb:	48 83 c2 20          	add    $0x20,%rdx
  4011cf:	66 48 0f 6e c8       	movq   %rax,%xmm1
  4011d4:	89 4a f8             	mov    %ecx,-0x8(%rdx)
  4011d7:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
  4011db:	c7 42 f0 01 00 00 00 	movl   $0x1,-0x10(%rdx)
  4011e2:	0f 11 42 e0          	movups %xmm0,-0x20(%rdx)
  4011e6:	48 3d f4 01 00 00    	cmp    $0x1f4,%rax
  4011ec:	75 d2                	jne    4011c0 <main+0x100>
  4011ee:	ba f4 01 00 00       	mov    $0x1f4,%edx
  4011f3:	48 8d 35 81 0e 00 00 	lea    0xe81(%rip),%rsi        # 40207b <_IO_stdin_used+0x7b>
  4011fa:	bf 01 00 00 00       	mov    $0x1,%edi
  4011ff:	31 c0                	xor    %eax,%eax
  401201:	e8 8a fe ff ff       	call   401090 <__printf_chk@plt>
  401206:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  40120b:	48 ba 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rdx
  401215:	48 8d 88 60 6d 00 00 	lea    0x6d60(%rax),%rcx
  40121c:	0f 1f 40 00          	nopl   0x0(%rax)
  401220:	48 89 10             	mov    %rdx,(%rax)
  401223:	48 83 c0 70          	add    $0x70,%rax
  401227:	48 89 50 c8          	mov    %rdx,-0x38(%rax)
  40122b:	48 39 c8             	cmp    %rcx,%rax
  40122e:	75 f0                	jne    401220 <main+0x160>
  401230:	be 04 00 00 00       	mov    $0x4,%esi
  401235:	bf 08 00 00 00       	mov    $0x8,%edi
  40123a:	49 89 de             	mov    %rbx,%r14
  40123d:	45 31 ed             	xor    %r13d,%r13d
  401240:	e8 3b fe ff ff       	call   401080 <calloc@plt>
  401245:	66 48 0f 6e f3       	movq   %rbx,%xmm6
  40124a:	45 31 ff             	xor    %r15d,%r15d
  40124d:	49 89 c1             	mov    %rax,%r9
  401250:	66 48 0f 6e e8       	movq   %rax,%xmm5
  401255:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  40125a:	66 0f 6c ee          	punpcklqdq %xmm6,%xmm5
  40125e:	4d 89 cc             	mov    %r9,%r12
  401261:	48 89 43 78          	mov    %rax,0x78(%rbx)
  401265:	0f 29 2c 24          	movaps %xmm5,(%rsp)
  401269:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401270:	44 89 fd             	mov    %r15d,%ebp
  401273:	be 80 00 00 00       	mov    $0x80,%esi
  401278:	bf 01 00 00 00       	mov    $0x1,%edi
  40127d:	41 83 c7 01          	add    $0x1,%r15d
  401281:	e8 fa fd ff ff       	call   401080 <calloc@plt>
  401286:	44 89 f9             	mov    %r15d,%ecx
  401289:	ba 01 00 00 00       	mov    $0x1,%edx
  40128e:	48 8d 35 43 0e 00 00 	lea    0xe43(%rip),%rsi        # 4020d8 <_IO_stdin_used+0xd8>
  401295:	48 d3 e2             	shl    %cl,%rdx
  401298:	48 09 10             	or     %rdx,(%rax)
  40129b:	44 89 f9             	mov    %r15d,%ecx
  40129e:	89 ea                	mov    %ebp,%edx
  4012a0:	49 89 86 80 00 00 00 	mov    %rax,0x80(%r14)
  4012a7:	bf 01 00 00 00       	mov    $0x1,%edi
  4012ac:	31 c0                	xor    %eax,%eax
  4012ae:	49 83 c4 04          	add    $0x4,%r12
  4012b2:	49 81 c6 50 01 00 00 	add    $0x150,%r14
  4012b9:	e8 d2 fd ff ff       	call   401090 <__printf_chk@plt>
  4012be:	48 8b 05 33 0e 00 00 	mov    0xe33(%rip),%rax        # 4020f8 <_IO_stdin_used+0xf8>
  4012c5:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
  4012ca:	45 89 ae 50 ff ff ff 	mov    %r13d,-0xb0(%r14)
  4012d1:	66 0f 6f 1d 37 0e 00 00 	movdqa 0xe37(%rip),%xmm3        # 402110 <_IO_stdin_used+0x110>
  4012d9:	66 0f 6f 25 3f 0e 00 00 	movdqa 0xe3f(%rip),%xmm4        # 402120 <_IO_stdin_used+0x120>
  4012e1:	41 c7 86 38 ff ff ff 00 00 00 00 	movl   $0x0,-0xc8(%r14)
  4012ec:	41 83 c5 3e          	add    $0x3e,%r13d
  4012f0:	49 89 86 48 ff ff ff 	mov    %rax,-0xb8(%r14)
  4012f7:	48 8b 05 02 0e 00 00 	mov    0xe02(%rip),%rax        # 402100 <_IO_stdin_used+0x100>
  4012fe:	41 89 ae 1c ff ff ff 	mov    %ebp,-0xe4(%r14)
  401305:	49 89 86 10 ff ff ff 	mov    %rax,-0xf0(%r14)
  40130c:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  401311:	41 c7 86 18 ff ff ff f4 01 00 00 	movl   $0x1f4,-0xe8(%r14)
  40131c:	41 c7 86 20 ff ff ff 08 00 00 00 	movl   $0x8,-0xe0(%r14)
  401327:	41 c7 44 24 fc 00 00 00 00 	movl   $0x0,-0x4(%r12)
  401330:	41 0f 11 96 d0 fe ff ff 	movups %xmm2,-0x130(%r14)
  401338:	49 89 9e e0 fe ff ff 	mov    %rbx,-0x120(%r14)
  40133f:	41 0f 11 9e b0 fe ff ff 	movups %xmm3,-0x150(%r14)
  401347:	49 89 86 58 ff ff ff 	mov    %rax,-0xa8(%r14)
  40134e:	41 0f 11 a6 70 ff ff ff 	movups %xmm4,-0x90(%r14)
  401356:	41 c7 46 80 00 00 00 00 	movl   $0x0,-0x80(%r14)
  40135e:	41 83 ff 08          	cmp    $0x8,%r15d
  401362:	0f 85 08 ff ff ff    	jne    401270 <main+0x1b0>
  401368:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
  40136d:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
  401372:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
  401377:	49 89 de             	mov    %rbx,%r14
  40137a:	49 c7 c5 f0 1b 40 00 	mov    $0x401bf0,%r13
  401381:	49 8d 87 c0 01 00 00 	lea    0x1c0(%r15),%rax
  401388:	4c 89 fb             	mov    %r15,%rbx
  40138b:	49 89 ec             	mov    %rbp,%r12
  40138e:	49 89 c7             	mov    %rax,%r15
  401391:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401398:	4c 89 f1             	mov    %r14,%rcx
  40139b:	48 89 de             	mov    %rbx,%rsi
  40139e:	48 89 ef             	mov    %rbp,%rdi
  4013a1:	4c 89 ea             	mov    %r13,%rdx
  4013a4:	e8 f7 fc ff ff       	call   4010a0 <pthread_create@plt>
  4013a9:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
  4013ad:	48 83 c3 38          	add    $0x38,%rbx
  4013b1:	49 8b 96 80 00 00 00 	mov    0x80(%r14),%rdx
  4013b8:	be 08 00 00 00       	mov    $0x8,%esi
  4013bd:	48 83 c5 08          	add    $0x8,%rbp
  4013c1:	49 81 c6 50 01 00 00 	add    $0x150,%r14
  4013c8:	e8 63 fc ff ff       	call   401030 <pthread_setaffinity_np@plt>
  4013cd:	49 39 df             	cmp    %rbx,%r15
  4013d0:	75 c6                	jne    401398 <main+0x2d8>
  4013d2:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
  4013d7:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  4013dc:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  4013e1:	66 0f 6f 05 47 0d 00 00 	movdqa 0xd47(%rip),%xmm0        # 402130 <_IO_stdin_used+0x130>
  4013e9:	4c 8d 74 24 38       	lea    0x38(%rsp),%r14
  4013ee:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  4013f3:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4013f7:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  4013fc:	e8 6f fc ff ff       	call   401070 <nanosleep@plt>
  401401:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
  401406:	c7 43 64 00 00 00 00 	movl   $0x0,0x64(%rbx)
  40140d:	c7 83 b4 01 00 00 00 00 00 00 	movl   $0x0,0x1b4(%rbx)
  401417:	c7 83 04 03 00 00 00 00 00 00 	movl   $0x0,0x304(%rbx)
  401421:	49 83 c5 40          	add    $0x40,%r13
  401425:	c7 83 54 04 00 00 00 00 00 00 	movl   $0x0,0x454(%rbx)
  40142f:	c7 83 a4 05 00 00 00 00 00 00 	movl   $0x0,0x5a4(%rbx)
  401439:	c7 83 f4 06 00 00 00 00 00 00 	movl   $0x0,0x6f4(%rbx)
  401443:	c7 83 44 08 00 00 00 00 00 00 	movl   $0x0,0x844(%rbx)
  40144d:	c7 83 94 09 00 00 00 00 00 00 	movl   $0x0,0x994(%rbx)
  401457:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  401460:	49 8b 3c 24          	mov    (%r12),%rdi
  401464:	4c 89 f6             	mov    %r14,%rsi
  401467:	49 83 c4 08          	add    $0x8,%r12
  40146b:	e8 40 fc ff ff       	call   4010b0 <pthread_join@plt>
  401470:	4d 39 ec             	cmp    %r13,%r12
  401473:	75 eb                	jne    401460 <main+0x3a0>
  401475:	48 8d 3d 0b 0c 00 00 	lea    0xc0b(%rip),%rdi        # 402087 <_IO_stdin_used+0x87>
  40147c:	4c 8d 63 48          	lea    0x48(%rbx),%r12
  401480:	45 31 ed             	xor    %r13d,%r13d
  401483:	e8 b8 fb ff ff       	call   401040 <puts@plt>
  401488:	4c 8d bb c8 0a 00 00 	lea    0xac8(%rbx),%r15
  40148f:	4c 8d 35 7d 0b 00 00 	lea    0xb7d(%rip),%r14        # 402013 <_IO_stdin_used+0x13>
  401496:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4014a0:	49 8b 14 24          	mov    (%r12),%rdx
  4014a4:	4c 89 f6             	mov    %r14,%rsi
  4014a7:	bf 01 00 00 00       	mov    $0x1,%edi
  4014ac:	31 c0                	xor    %eax,%eax
  4014ae:	49 81 c4 50 01 00 00 	add    $0x150,%r12
  4014b5:	e8 d6 fb ff ff       	call   401090 <__printf_chk@plt>
  4014ba:	4d 03 ac 24 b0 fe ff ff 	add    -0x150(%r12),%r13
  4014c2:	4d 39 e7             	cmp    %r12,%r15
  4014c5:	75 d9                	jne    4014a0 <main+0x3e0>
  4014c7:	4c 89 e8             	mov    %r13,%rax
  4014ca:	49 c1 fd 3f          	sar    $0x3f,%r13
  4014ce:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
  4014d8:	48 8d 35 bd 0b 00 00 	lea    0xbbd(%rip),%rsi        # 40209c <_IO_stdin_used+0x9c>
  4014df:	49 f7 ec             	imul   %r12
  4014e2:	bf 01 00 00 00       	mov    $0x1,%edi
  4014e7:	31 c0                	xor    %eax,%eax
  4014e9:	4c 8d 35 c9 0b 00 00 	lea    0xbc9(%rip),%r14        # 4020b9 <_IO_stdin_used+0xb9>
  4014f0:	48 d1 fa             	sar    %rdx
  4014f3:	4c 29 ea             	sub    %r13,%rdx
  4014f6:	e8 95 fb ff ff       	call   401090 <__printf_chk@plt>
  4014fb:	48 8b 8b a0 01 00 00 	mov    0x1a0(%rbx),%rcx
  401502:	bf 01 00 00 00       	mov    $0x1,%edi
  401507:	48 03 8b f0 02 00 00 	add    0x2f0(%rbx),%rcx
  40150e:	48 03 4b 50          	add    0x50(%rbx),%rcx
  401512:	48 03 8b 40 04 00 00 	add    0x440(%rbx),%rcx
  401519:	48 8d 35 87 0b 00 00 	lea    0xb87(%rip),%rsi        # 4020a7 <_IO_stdin_used+0xa7>
  401520:	48 03 8b 90 05 00 00 	add    0x590(%rbx),%rcx
  401527:	48 03 8b e0 06 00 00 	add    0x6e0(%rbx),%rcx
  40152e:	48 03 8b 30 08 00 00 	add    0x830(%rbx),%rcx
  401535:	48 03 8b 80 09 00 00 	add    0x980(%rbx),%rcx
  40153c:	48 89 c8             	mov    %rcx,%rax
  40153f:	48 c1 f9 3f          	sar    $0x3f,%rcx
  401543:	49 f7 ec             	imul   %r12
  401546:	31 c0                	xor    %eax,%eax
  401548:	48 d1 fa             	sar    %rdx
  40154b:	48 29 ca             	sub    %rcx,%rdx
  40154e:	e8 3d fb ff ff       	call   401090 <__printf_chk@plt>
  401553:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  401558:	4c 8d 60 10          	lea    0x10(%rax),%r12
  40155c:	48 8d a8 90 03 00 00 	lea    0x390(%rax),%rbp
  401563:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401568:	4d 8b 7c 24 10       	mov    0x10(%r12),%r15
  40156d:	4d 8b 6c 24 20       	mov    0x20(%r12),%r13
  401572:	4c 89 f6             	mov    %r14,%rsi
  401575:	31 c0                	xor    %eax,%eax
  401577:	bf 01 00 00 00       	mov    $0x1,%edi
  40157c:	49 83 c4 38          	add    $0x38,%r12
  401580:	4c 89 fa             	mov    %r15,%rdx
  401583:	49 2b 54 24 c8       	sub    -0x38(%r12),%rdx
  401588:	e8 03 fb ff ff       	call   401090 <__printf_chk@plt>
  40158d:	4c 89 ea             	mov    %r13,%rdx
  401590:	4c 89 f6             	mov    %r14,%rsi
  401593:	bf 01 00 00 00       	mov    $0x1,%edi
  401598:	4c 29 fa             	sub    %r15,%rdx
  40159b:	31 c0                	xor    %eax,%eax
  40159d:	e8 ee fa ff ff       	call   401090 <__printf_chk@plt>
  4015a2:	4c 39 e5             	cmp    %r12,%rbp
  4015a5:	75 c1                	jne    401568 <main+0x4a8>
  4015a7:	48 8d 2d f4 0a 00 00 	lea    0xaf4(%rip),%rbp        # 4020a2 <_IO_stdin_used+0xa2>
  4015ae:	48 8d 3d 0b 0b 00 00 	lea    0xb0b(%rip),%rdi        # 4020c0 <_IO_stdin_used+0xc0>
  4015b5:	e8 86 fa ff ff       	call   401040 <puts@plt>
  4015ba:	48 89 ee             	mov    %rbp,%rsi
  4015bd:	bf 01 00 00 00       	mov    $0x1,%edi
  4015c2:	31 c0                	xor    %eax,%eax
  4015c4:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
  4015cb:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  4015d2:	e8 b9 fa ff ff       	call   401090 <__printf_chk@plt>
  4015d7:	48 89 ee             	mov    %rbp,%rsi
  4015da:	bf 01 00 00 00       	mov    $0x1,%edi
  4015df:	31 c0                	xor    %eax,%eax
  4015e1:	48 8b 93 08 01 00 00 	mov    0x108(%rbx),%rdx
  4015e8:	48 2b 93 e8 00 00 00 	sub    0xe8(%rbx),%rdx
  4015ef:	e8 9c fa ff ff       	call   401090 <__printf_chk@plt>
  4015f4:	48 89 ee             	mov    %rbp,%rsi
  4015f7:	bf 01 00 00 00       	mov    $0x1,%edi
  4015fc:	31 c0                	xor    %eax,%eax
  4015fe:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
  401605:	48 2b 93 08 01 00 00 	sub    0x108(%rbx),%rdx
  40160c:	e8 7f fa ff ff       	call   401090 <__printf_chk@plt>
  401611:	48 89 ee             	mov    %rbp,%rsi
  401614:	bf 01 00 00 00       	mov    $0x1,%edi
  401619:	31 c0                	xor    %eax,%eax
  40161b:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
  401622:	48 2b 93 18 01 00 00 	sub    0x118(%rbx),%rdx
  401629:	e8 62 fa ff ff       	call   401090 <__printf_chk@plt>
  40162e:	48 89 ee             	mov    %rbp,%rsi
  401631:	bf 01 00 00 00       	mov    $0x1,%edi
  401636:	31 c0                	xor    %eax,%eax
  401638:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
  40163f:	48 2b 93 28 01 00 00 	sub    0x128(%rbx),%rdx
  401646:	e8 45 fa ff ff       	call   401090 <__printf_chk@plt>
  40164b:	48 89 ee             	mov    %rbp,%rsi
  40164e:	bf 01 00 00 00       	mov    $0x1,%edi
  401653:	31 c0                	xor    %eax,%eax
  401655:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
  40165c:	48 2b 93 08 01 00 00 	sub    0x108(%rbx),%rdx
  401663:	e8 28 fa ff ff       	call   401090 <__printf_chk@plt>
  401668:	48 8b 93 48 01 00 00 	mov    0x148(%rbx),%rdx
  40166f:	31 c0                	xor    %eax,%eax
  401671:	48 2b 93 38 01 00 00 	sub    0x138(%rbx),%rdx
  401678:	48 8d 35 4e 0a 00 00 	lea    0xa4e(%rip),%rsi        # 4020cd <_IO_stdin_used+0xcd>
  40167f:	bf 01 00 00 00       	mov    $0x1,%edi
  401684:	e8 07 fa ff ff       	call   401090 <__printf_chk@plt>
  401689:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  40168e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401697:	75 11                	jne    4016aa <main+0x5ea>
  401699:	48 83 c4 78          	add    $0x78,%rsp
  40169d:	31 c0                	xor    %eax,%eax
  40169f:	5b                   	pop    %rbx
  4016a0:	5d                   	pop    %rbp
  4016a1:	41 5c                	pop    %r12
  4016a3:	41 5d                	pop    %r13
  4016a5:	41 5e                	pop    %r14
  4016a7:	41 5f                	pop    %r15
  4016a9:	c3                   	ret
  4016aa:	e8 b1 f9 ff ff       	call   401060 <__stack_chk_fail@plt>
  4016af:	90                   	nop

00000000004016b0 <_start>:
  4016b0:	f3 0f 1e fa          	endbr64
  4016b4:	31 ed                	xor    %ebp,%ebp
  4016b6:	49 89 d1             	mov    %rdx,%r9
  4016b9:	5e                   	pop    %rsi
  4016ba:	48 89 e2             	mov    %rsp,%rdx
  4016bd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4016c1:	50                   	push   %rax
  4016c2:	54                   	push   %rsp
  4016c3:	45 31 c0             	xor    %r8d,%r8d
  4016c6:	31 c9                	xor    %ecx,%ecx
  4016c8:	48 c7 c7 c0 10 40 00 	mov    $0x4010c0,%rdi
  4016cf:	ff 15 1b 29 00 00    	call   *0x291b(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  4016d5:	f4                   	hlt
  4016d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004016e0 <_dl_relocate_static_pie>:
  4016e0:	f3 0f 1e fa          	endbr64
  4016e4:	c3                   	ret
  4016e5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4016ef:	90                   	nop

00000000004016f0 <deregister_tm_clones>:
  4016f0:	b8 10 40 40 00       	mov    $0x404010,%eax
  4016f5:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  4016fb:	74 13                	je     401710 <deregister_tm_clones+0x20>
  4016fd:	b8 00 00 00 00       	mov    $0x0,%eax
  401702:	48 85 c0             	test   %rax,%rax
  401705:	74 09                	je     401710 <deregister_tm_clones+0x20>
  401707:	bf 10 40 40 00       	mov    $0x404010,%edi
  40170c:	ff e0                	jmp    *%rax
  40170e:	66 90                	xchg   %ax,%ax
  401710:	c3                   	ret
  401711:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40171c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401720 <register_tm_clones>:
  401720:	be 10 40 40 00       	mov    $0x404010,%esi
  401725:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  40172c:	48 89 f0             	mov    %rsi,%rax
  40172f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401733:	48 c1 f8 03          	sar    $0x3,%rax
  401737:	48 01 c6             	add    %rax,%rsi
  40173a:	48 d1 fe             	sar    %rsi
  40173d:	74 11                	je     401750 <register_tm_clones+0x30>
  40173f:	b8 00 00 00 00       	mov    $0x0,%eax
  401744:	48 85 c0             	test   %rax,%rax
  401747:	74 07                	je     401750 <register_tm_clones+0x30>
  401749:	bf 10 40 40 00       	mov    $0x404010,%edi
  40174e:	ff e0                	jmp    *%rax
  401750:	c3                   	ret
  401751:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40175c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401760 <__do_global_dtors_aux>:
  401760:	f3 0f 1e fa          	endbr64
  401764:	80 3d a5 28 00 00 00 	cmpb   $0x0,0x28a5(%rip)        # 404010 <__TMC_END__>
  40176b:	75 13                	jne    401780 <__do_global_dtors_aux+0x20>
  40176d:	55                   	push   %rbp
  40176e:	48 89 e5             	mov    %rsp,%rbp
  401771:	e8 7a ff ff ff       	call   4016f0 <deregister_tm_clones>
  401776:	c6 05 93 28 00 00 01 	movb   $0x1,0x2893(%rip)        # 404010 <__TMC_END__>
  40177d:	5d                   	pop    %rbp
  40177e:	c3                   	ret
  40177f:	90                   	nop
  401780:	c3                   	ret
  401781:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40178c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401790 <frame_dummy>:
  401790:	f3 0f 1e fa          	endbr64
  401794:	eb 8a                	jmp    401720 <register_tm_clones>
  401796:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004017a0 <pollthreads>:
  4017a0:	83 7f 70 01          	cmpl   $0x1,0x70(%rdi)
  4017a4:	49 89 f9             	mov    %rdi,%r9
  4017a7:	7e 77                	jle    401820 <pollthreads+0x80>
  4017a9:	49 8b 41 30          	mov    0x30(%r9),%rax
  4017ad:	55                   	push   %rbp
  4017ae:	49 89 f2             	mov    %rsi,%r10
  4017b1:	49 89 d3             	mov    %rdx,%r11
  4017b4:	53                   	push   %rbx
  4017b5:	48 89 cf             	mov    %rcx,%rdi
  4017b8:	48 8b 98 70 01 00 00 	mov    0x170(%rax),%rbx
  4017bf:	b8 01 00 00 00       	mov    $0x1,%eax
  4017c4:	0f 1f 40 00          	nopl   0x0(%rax)
  4017c8:	48 63 d0             	movslq %eax,%rdx
  4017cb:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
  4017ce:	85 d2                	test   %edx,%edx
  4017d0:	40 0f 94 c6          	sete   %sil
  4017d4:	f6 c2 04             	test   $0x4,%dl
  4017d7:	75 05                	jne    4017de <pollthreads+0x3e>
  4017d9:	40 84 f6             	test   %sil,%sil
  4017dc:	74 0d                	je     4017eb <pollthreads+0x4b>
  4017de:	49 63 08             	movslq (%r8),%rcx
  4017e1:	8d 69 01             	lea    0x1(%rcx),%ebp
  4017e4:	41 89 28             	mov    %ebp,(%r8)
  4017e7:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
  4017eb:	83 e2 08             	and    $0x8,%edx
  4017ee:	75 05                	jne    4017f5 <pollthreads+0x55>
  4017f0:	40 84 f6             	test   %sil,%sil
  4017f3:	74 1b                	je     401810 <pollthreads+0x70>
  4017f5:	48 63 17             	movslq (%rdi),%rdx
  4017f8:	8d 4a 01             	lea    0x1(%rdx),%ecx
  4017fb:	89 0f                	mov    %ecx,(%rdi)
  4017fd:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  401801:	83 c0 01             	add    $0x1,%eax
  401804:	41 39 41 70          	cmp    %eax,0x70(%r9)
  401808:	7f be                	jg     4017c8 <pollthreads+0x28>
  40180a:	31 c0                	xor    %eax,%eax
  40180c:	5b                   	pop    %rbx
  40180d:	5d                   	pop    %rbp
  40180e:	c3                   	ret
  40180f:	90                   	nop
  401810:	83 c0 01             	add    $0x1,%eax
  401813:	41 39 41 70          	cmp    %eax,0x70(%r9)
  401817:	7f af                	jg     4017c8 <pollthreads+0x28>
  401819:	31 c0                	xor    %eax,%eax
  40181b:	5b                   	pop    %rbx
  40181c:	5d                   	pop    %rbp
  40181d:	c3                   	ret
  40181e:	66 90                	xchg   %ax,%ax
  401820:	31 c0                	xor    %eax,%eax
  401822:	c3                   	ret
  401823:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40182e:	66 90                	xchg   %ax,%ax

0000000000401830 <findavailable>:
  401830:	49 89 fb             	mov    %rdi,%r11
  401833:	48 8b bf c0 00 00 00 	mov    0xc0(%rdi),%rdi
  40183a:	44 8b 02             	mov    (%rdx),%r8d
  40183d:	48 83 c7 01          	add    $0x1,%rdi
  401841:	48 85 ff             	test   %rdi,%rdi
  401844:	7e 66                	jle    4018ac <findavailable+0x7c>
  401846:	4d 8b 93 a8 00 00 00 	mov    0xa8(%r11),%r10
  40184d:	31 c9                	xor    %ecx,%ecx
  40184f:	45 31 c9             	xor    %r9d,%r9d
  401852:	31 c0                	xor    %eax,%eax
  401854:	eb 18                	jmp    40186e <findavailable+0x3e>
  401856:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401860:	83 c1 01             	add    $0x1,%ecx
  401863:	48 63 c1             	movslq %ecx,%rax
  401866:	49 89 c1             	mov    %rax,%r9
  401869:	48 39 f8             	cmp    %rdi,%rax
  40186c:	7d 3e                	jge    4018ac <findavailable+0x7c>
  40186e:	48 c1 e0 05          	shl    $0x5,%rax
  401872:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401878:	75 e6                	jne    401860 <findavailable+0x30>
  40187a:	49 63 c0             	movslq %r8d,%rax
  40187d:	41 83 c0 01          	add    $0x1,%r8d
  401881:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
  401885:	44 89 02             	mov    %r8d,(%rdx)
  401888:	41 8b 43 70          	mov    0x70(%r11),%eax
  40188c:	01 c0                	add    %eax,%eax
  40188e:	41 39 c0             	cmp    %eax,%r8d
  401891:	74 19                	je     4018ac <findavailable+0x7c>
  401893:	49 8b bb c0 00 00 00 	mov    0xc0(%r11),%rdi
  40189a:	83 c1 01             	add    $0x1,%ecx
  40189d:	48 63 c1             	movslq %ecx,%rax
  4018a0:	48 83 c7 01          	add    $0x1,%rdi
  4018a4:	49 89 c1             	mov    %rax,%r9
  4018a7:	48 39 f8             	cmp    %rdi,%rax
  4018aa:	7c c2                	jl     40186e <findavailable+0x3e>
  4018ac:	31 c0                	xor    %eax,%eax
  4018ae:	45 85 c0             	test   %r8d,%r8d
  4018b1:	0f 94 c0             	sete   %al
  4018b4:	c3                   	ret
  4018b5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000004018c0 <singlewriter>:
  4018c0:	41 55                	push   %r13
  4018c2:	49 89 d5             	mov    %rdx,%r13
  4018c5:	49 89 c8             	mov    %rcx,%r8
  4018c8:	41 54                	push   %r12
  4018ca:	49 89 cc             	mov    %rcx,%r12
  4018cd:	4c 89 e9             	mov    %r13,%rcx
  4018d0:	55                   	push   %rbp
  4018d1:	48 89 fd             	mov    %rdi,%rbp
  4018d4:	53                   	push   %rbx
  4018d5:	48 89 f3             	mov    %rsi,%rbx
  4018d8:	48 83 ec 28          	sub    $0x28,%rsp
  4018dc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4018e5:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  4018ea:	31 c0                	xor    %eax,%eax
  4018ec:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  4018f1:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  4018f9:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  401901:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  401909:	e8 22 ff ff ff       	call   401830 <findavailable>
  40190e:	83 f8 01             	cmp    $0x1,%eax
  401911:	0f 84 50 01 00 00    	je     401a67 <singlewriter+0x1a7>
  401917:	48 89 ef             	mov    %rbp,%rdi
  40191a:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  40191f:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401924:	4c 89 e2             	mov    %r12,%rdx
  401927:	4c 89 ee             	mov    %r13,%rsi
  40192a:	e8 71 fe ff ff       	call   4017a0 <pollthreads>
  40192f:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401934:	85 ff                	test   %edi,%edi
  401936:	0f 8e 55 01 00 00    	jle    401a91 <singlewriter+0x1d1>
  40193c:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
  401941:	31 c9                	xor    %ecx,%ecx
  401943:	eb 61                	jmp    4019a6 <singlewriter+0xe6>
  401945:	0f 1f 00             	nopl   (%rax)
  401948:	48 8b 04 cb          	mov    (%rbx,%rcx,8),%rax
  40194c:	49 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%rdx
  401951:	8d 71 01             	lea    0x1(%rcx),%esi
  401954:	48 83 c1 01          	add    $0x1,%rcx
  401958:	48 c1 e0 05          	shl    $0x5,%rax
  40195c:	48 03 85 a8 00 00 00 	add    0xa8(%rbp),%rax
  401963:	4c 8d 14 92          	lea    (%rdx,%rdx,4),%r10
  401967:	49 89 d1             	mov    %rdx,%r9
  40196a:	66 0f 6e 00          	movd   (%rax),%xmm0
  40196e:	66 0f 6e 48 08       	movd   0x8(%rax),%xmm1
  401973:	4a 8d 14 92          	lea    (%rdx,%r10,4),%rdx
  401977:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
  40197e:	48 c1 e2 04          	shl    $0x4,%rdx
  401982:	48 03 55 30          	add    0x30(%rbp),%rdx
  401986:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
  40198a:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
  401991:	44 89 48 14          	mov    %r9d,0x14(%rax)
  401995:	83 8a d0 00 00 00 10 	orl    $0x10,0xd0(%rdx)
  40199c:	66 0f d6 42 14       	movq   %xmm0,0x14(%rdx)
  4019a1:	48 39 cf             	cmp    %rcx,%rdi
  4019a4:	74 07                	je     4019ad <singlewriter+0xed>
  4019a6:	89 ce                	mov    %ecx,%esi
  4019a8:	4c 39 c1             	cmp    %r8,%rcx
  4019ab:	75 9b                	jne    401948 <singlewriter+0x88>
  4019ad:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  4019b2:	45 85 c0             	test   %r8d,%r8d
  4019b5:	7e 6f                	jle    401a26 <singlewriter+0x166>
  4019b7:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  4019bb:	41 01 f0             	add    %esi,%r8d
  4019be:	eb 62                	jmp    401a22 <singlewriter+0x162>
  4019c0:	8d 4e 01             	lea    0x1(%rsi),%ecx
  4019c3:	48 63 f6             	movslq %esi,%rsi
  4019c6:	49 63 14 24          	movslq (%r12),%rdx
  4019ca:	49 83 c4 04          	add    $0x4,%r12
  4019ce:	48 8b 04 f3          	mov    (%rbx,%rsi,8),%rax
  4019d2:	48 8d 34 92          	lea    (%rdx,%rdx,4),%rsi
  4019d6:	49 89 d1             	mov    %rdx,%r9
  4019d9:	48 c1 e0 05          	shl    $0x5,%rax
  4019dd:	48 03 85 a8 00 00 00 	add    0xa8(%rbp),%rax
  4019e4:	48 8d 14 b2          	lea    (%rdx,%rsi,4),%rdx
  4019e8:	66 0f 6e 00          	movd   (%rax),%xmm0
  4019ec:	66 0f 6e 50 08       	movd   0x8(%rax),%xmm2
  4019f1:	48 c1 e2 04          	shl    $0x4,%rdx
  4019f5:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
  4019fc:	48 03 55 30          	add    0x30(%rbp),%rdx
  401a00:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
  401a04:	48 89 82 b8 00 00 00 	mov    %rax,0xb8(%rdx)
  401a0b:	44 89 48 14          	mov    %r9d,0x14(%rax)
  401a0f:	83 8a d0 00 00 00 20 	orl    $0x20,0xd0(%rdx)
  401a16:	66 0f d6 42 40       	movq   %xmm0,0x40(%rdx)
  401a1b:	44 39 c1             	cmp    %r8d,%ecx
  401a1e:	74 06                	je     401a26 <singlewriter+0x166>
  401a20:	89 ce                	mov    %ecx,%esi
  401a22:	39 f7                	cmp    %esi,%edi
  401a24:	75 9a                	jne    4019c0 <singlewriter+0x100>
  401a26:	8b 7d 70             	mov    0x70(%rbp),%edi
  401a29:	85 ff                	test   %edi,%edi
  401a2b:	7e 38                	jle    401a65 <singlewriter+0x1a5>
  401a2d:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401a31:	31 c9                	xor    %ecx,%ecx
  401a33:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401a38:	48 63 d1             	movslq %ecx,%rdx
  401a3b:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
  401a3f:	48 8d 04 82          	lea    (%rdx,%rax,4),%rax
  401a43:	48 c1 e0 04          	shl    $0x4,%rax
  401a47:	4c 01 c0             	add    %r8,%rax
  401a4a:	8b b0 d0 00 00 00    	mov    0xd0(%rax),%esi
  401a50:	85 f6                	test   %esi,%esi
  401a52:	74 34                	je     401a88 <singlewriter+0x1c8>
  401a54:	48 8b 40 20          	mov    0x20(%rax),%rax
  401a58:	83 c1 01             	add    $0x1,%ecx
  401a5b:	89 34 90             	mov    %esi,(%rax,%rdx,4)
  401a5e:	8b 7d 70             	mov    0x70(%rbp),%edi
  401a61:	39 f9                	cmp    %edi,%ecx
  401a63:	7c d3                	jl     401a38 <singlewriter+0x178>
  401a65:	31 c0                	xor    %eax,%eax
  401a67:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401a6c:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401a75:	75 21                	jne    401a98 <singlewriter+0x1d8>
  401a77:	48 83 c4 28          	add    $0x28,%rsp
  401a7b:	5b                   	pop    %rbx
  401a7c:	5d                   	pop    %rbp
  401a7d:	41 5c                	pop    %r12
  401a7f:	41 5d                	pop    %r13
  401a81:	c3                   	ret
  401a82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  401a88:	83 c1 01             	add    $0x1,%ecx
  401a8b:	39 f9                	cmp    %edi,%ecx
  401a8d:	7c a9                	jl     401a38 <singlewriter+0x178>
  401a8f:	eb d4                	jmp    401a65 <singlewriter+0x1a5>
  401a91:	31 f6                	xor    %esi,%esi
  401a93:	e9 15 ff ff ff       	jmp    4019ad <singlewriter+0xed>
  401a98:	e8 c3 f5 ff ff       	call   401060 <__stack_chk_fail@plt>
  401a9d:	0f 1f 00             	nopl   (%rax)

0000000000401aa0 <threadwork>:
  401aa0:	53                   	push   %rbx
  401aa1:	48 63 4f 6c          	movslq 0x6c(%rdi),%rcx
  401aa5:	48 89 fa             	mov    %rdi,%rdx
  401aa8:	48 8b 47 20          	mov    0x20(%rdi),%rax
  401aac:	4c 8d 04 88          	lea    (%rax,%rcx,4),%r8
  401ab0:	49 63 08             	movslq (%r8),%rcx
  401ab3:	41 89 c9             	mov    %ecx,%r9d
  401ab6:	48 89 c8             	mov    %rcx,%rax
  401ab9:	48 89 8f d8 00 00 00 	mov    %rcx,0xd8(%rdi)
  401ac0:	41 83 e1 20          	and    $0x20,%r9d
  401ac4:	a8 10                	test   $0x10,%al
  401ac6:	0f 85 84 00 00 00    	jne    401b50 <threadwork+0xb0>
  401acc:	45 85 c9             	test   %r9d,%r9d
  401acf:	74 79                	je     401b4a <threadwork+0xaa>
  401ad1:	41 ba 04 00 00 00    	mov    $0x4,%r10d
  401ad7:	44 8b 4a 40          	mov    0x40(%rdx),%r9d
  401adb:	8b 4a 44             	mov    0x44(%rdx),%ecx
  401ade:	41 39 c9             	cmp    %ecx,%r9d
  401ae1:	7d 56                	jge    401b39 <threadwork+0x99>
  401ae3:	48 8b 42 28          	mov    0x28(%rdx),%rax
  401ae7:	49 63 f9             	movslq %r9d,%rdi
  401aea:	8d 71 ff             	lea    -0x1(%rcx),%esi
  401aed:	4c 8b 5a 50          	mov    0x50(%rdx),%r11
  401af1:	44 29 ce             	sub    %r9d,%esi
  401af4:	48 8b 58 78          	mov    0x78(%rax),%rbx
  401af8:	48 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rax
  401b00:	48 29 f8             	sub    %rdi,%rax
  401b03:	48 01 f7             	add    %rsi,%rdi
  401b06:	48 8d 0c fd 00 00 00 00 	lea    0x0(,%rdi,8),%rcx
  401b0e:	48 8d 04 c3          	lea    (%rbx,%rax,8),%rax
  401b12:	48 29 f9             	sub    %rdi,%rcx
  401b15:	48 8d 4c cb 38       	lea    0x38(%rbx,%rcx,8),%rcx
  401b1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  401b20:	c7 40 04 01 00 00 00 	movl   $0x1,0x4(%rax)
  401b27:	48 83 c0 38          	add    $0x38,%rax
  401b2b:	48 39 c8             	cmp    %rcx,%rax
  401b2e:	75 f0                	jne    401b20 <threadwork+0x80>
  401b30:	49 8d 44 33 01       	lea    0x1(%r11,%rsi,1),%rax
  401b35:	48 89 42 50          	mov    %rax,0x50(%rdx)
  401b39:	48 8b 82 b8 00 00 00 	mov    0xb8(%rdx),%rax
  401b40:	c7 40 10 01 00 00 00 	movl   $0x1,0x10(%rax)
  401b47:	45 89 10             	mov    %r10d,(%r8)
  401b4a:	5b                   	pop    %rbx
  401b4b:	c3                   	ret
  401b4c:	0f 1f 40 00          	nopl   0x0(%rax)
  401b50:	8b 5f 14             	mov    0x14(%rdi),%ebx
  401b53:	8b 4f 18             	mov    0x18(%rdi),%ecx
  401b56:	39 d9                	cmp    %ebx,%ecx
  401b58:	7e 60                	jle    401bba <threadwork+0x11a>
  401b5a:	48 8b 47 28          	mov    0x28(%rdi),%rax
  401b5e:	8d 71 ff             	lea    -0x1(%rcx),%esi
  401b61:	4c 8b 5f 48          	mov    0x48(%rdi),%r11
  401b65:	48 63 fb             	movslq %ebx,%rdi
  401b68:	29 de                	sub    %ebx,%esi
  401b6a:	4c 8b 50 78          	mov    0x78(%rax),%r10
  401b6e:	48 8d 0c 3e          	lea    (%rsi,%rdi,1),%rcx
  401b72:	48 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rax
  401b7a:	48 29 f8             	sub    %rdi,%rax
  401b7d:	48 8d 3c cd 00 00 00 00 	lea    0x0(,%rcx,8),%rdi
  401b85:	48 29 cf             	sub    %rcx,%rdi
  401b88:	49 8d 04 c2          	lea    (%r10,%rax,8),%rax
  401b8c:	48 c1 e7 03          	shl    $0x3,%rdi
  401b90:	49 8d 4c 3a 38       	lea    0x38(%r10,%rdi,1),%rcx
  401b95:	0f 1f 00             	nopl   (%rax)
  401b98:	c7 40 04 00 00 00 00 	movl   $0x0,0x4(%rax)
  401b9f:	48 83 c0 38          	add    $0x38,%rax
  401ba3:	48 39 c8             	cmp    %rcx,%rax
  401ba6:	75 f0                	jne    401b98 <threadwork+0xf8>
  401ba8:	49 8d 44 33 01       	lea    0x1(%r11,%rsi,1),%rax
  401bad:	48 89 42 48          	mov    %rax,0x48(%rdx)
  401bb1:	41 c7 44 3a 04 00 00 00 00 	movl   $0x0,0x4(%r10,%rdi,1)
  401bba:	48 8b 82 b0 00 00 00 	mov    0xb0(%rdx),%rax
  401bc1:	41 ba 08 00 00 00    	mov    $0x8,%r10d
  401bc7:	c7 40 10 01 00 00 00 	movl   $0x1,0x10(%rax)
  401bce:	45 85 c9             	test   %r9d,%r9d
  401bd1:	0f 84 70 ff ff ff    	je     401b47 <threadwork+0xa7>
  401bd7:	41 ba 0c 00 00 00    	mov    $0xc,%r10d
  401bdd:	e9 f5 fe ff ff       	jmp    401ad7 <threadwork+0x37>
  401be2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401bed:	0f 1f 00             	nopl   (%rax)

0000000000401bf0 <work>:
  401bf0:	41 56                	push   %r14
  401bf2:	48 8d 35 0b 04 00 00 	lea    0x40b(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  401bf9:	31 c0                	xor    %eax,%eax
  401bfb:	41 55                	push   %r13
  401bfd:	41 54                	push   %r12
  401bff:	55                   	push   %rbp
  401c00:	53                   	push   %rbx
  401c01:	8b 57 6c             	mov    0x6c(%rdi),%edx
  401c04:	48 89 fb             	mov    %rdi,%rbx
  401c07:	bf 01 00 00 00       	mov    $0x1,%edi
  401c0c:	e8 7f f4 ff ff       	call   401090 <__printf_chk@plt>
  401c11:	8b 43 6c             	mov    0x6c(%rbx),%eax
  401c14:	48 8d 35 fc 03 00 00 	lea    0x3fc(%rip),%rsi        # 402017 <_IO_stdin_used+0x17>
  401c1b:	bf 01 00 00 00       	mov    $0x1,%edi
  401c20:	44 8b b3 a0 00 00 00 	mov    0xa0(%rbx),%r14d
  401c27:	8d 50 01             	lea    0x1(%rax),%edx
  401c2a:	31 c0                	xor    %eax,%eax
  401c2c:	0f af 93 98 00 00 00 	imul   0x98(%rbx),%edx
  401c33:	e8 58 f4 ff ff       	call   401090 <__printf_chk@plt>
  401c38:	48 8b 83 c0 00 00 00 	mov    0xc0(%rbx),%rax
  401c3f:	be 08 00 00 00       	mov    $0x8,%esi
  401c44:	48 8d 78 01          	lea    0x1(%rax),%rdi
  401c48:	e8 33 f4 ff ff       	call   401080 <calloc@plt>
  401c4d:	4c 63 6b 70          	movslq 0x70(%rbx),%r13
  401c51:	be 04 00 00 00       	mov    $0x4,%esi
  401c56:	48 89 c5             	mov    %rax,%rbp
  401c59:	4c 89 ef             	mov    %r13,%rdi
  401c5c:	e8 1f f4 ff ff       	call   401080 <calloc@plt>
  401c61:	be 04 00 00 00       	mov    $0x4,%esi
  401c66:	4c 89 ef             	mov    %r13,%rdi
  401c69:	49 89 c4             	mov    %rax,%r12
  401c6c:	e8 0f f4 ff ff       	call   401080 <calloc@plt>
  401c71:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  401c75:	44 89 73 5c          	mov    %r14d,0x5c(%rbx)
  401c79:	75 49                	jne    401cc4 <work+0xd4>
  401c7b:	49 89 c5             	mov    %rax,%r13
  401c7e:	4c 8d b3 30 01 00 00 	lea    0x130(%rbx),%r14
  401c85:	0f 1f 00             	nopl   (%rax)
  401c88:	8b 43 6c             	mov    0x6c(%rbx),%eax
  401c8b:	85 c0                	test   %eax,%eax
  401c8d:	75 59                	jne    401ce8 <work+0xf8>
  401c8f:	4c 89 f6             	mov    %r14,%rsi
  401c92:	bf 04 00 00 00       	mov    $0x4,%edi
  401c97:	e8 b4 f3 ff ff       	call   401050 <clock_gettime@plt>
  401c9c:	4c 89 e9             	mov    %r13,%rcx
  401c9f:	4c 89 e2             	mov    %r12,%rdx
  401ca2:	48 89 ee             	mov    %rbp,%rsi
  401ca5:	48 89 df             	mov    %rbx,%rdi
  401ca8:	e8 13 fc ff ff       	call   4018c0 <singlewriter>
  401cad:	48 8d b3 40 01 00 00 	lea    0x140(%rbx),%rsi
  401cb4:	bf 04 00 00 00       	mov    $0x4,%edi
  401cb9:	e8 92 f3 ff ff       	call   401050 <clock_gettime@plt>
  401cbe:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  401cc2:	74 c4                	je     401c88 <work+0x98>
  401cc4:	8b 53 6c             	mov    0x6c(%rbx),%edx
  401cc7:	48 8d 35 57 03 00 00 	lea    0x357(%rip),%rsi        # 402025 <_IO_stdin_used+0x25>
  401cce:	bf 01 00 00 00       	mov    $0x1,%edi
  401cd3:	31 c0                	xor    %eax,%eax
  401cd5:	e8 b6 f3 ff ff       	call   401090 <__printf_chk@plt>
  401cda:	5b                   	pop    %rbx
  401cdb:	5d                   	pop    %rbp
  401cdc:	41 5c                	pop    %r12
  401cde:	41 5d                	pop    %r13
  401ce0:	41 5e                	pop    %r14
  401ce2:	c3                   	ret
  401ce3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401ce8:	48 89 df             	mov    %rbx,%rdi
  401ceb:	e8 b0 fd ff ff       	call   401aa0 <threadwork>
  401cf0:	83 7b 64 01          	cmpl   $0x1,0x64(%rbx)
  401cf4:	74 92                	je     401c88 <work+0x98>
  401cf6:	eb cc                	jmp    401cc4 <work+0xd4>
  401cf8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000401d00 <work2>:
  401d00:	eb 0b                	jmp    401d0d <work2+0xd>
  401d02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  401d08:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  401d0d:	83 7f 64 01          	cmpl   $0x1,0x64(%rdi)
  401d11:	74 f5                	je     401d08 <work2+0x8>
  401d13:	c3                   	ret

Disassembly of section .fini:

0000000000401d14 <_fini>:
  401d14:	f3 0f 1e fa          	endbr64
  401d18:	48 83 ec 08          	sub    $0x8,%rsp
  401d1c:	48 83 c4 08          	add    $0x8,%rsp
  401d20:	c3                   	ret
