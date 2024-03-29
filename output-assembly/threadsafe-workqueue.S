
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
  401020:	ff 35 7a 2f 00 00    	push   0x2f7a(%rip)        # 403fa0 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 7c 2f 00 00    	jmp    *0x2f7c(%rip)        # 403fa8 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <pthread_setaffinity_np@plt>:
  401030:	ff 25 7a 2f 00 00    	jmp    *0x2f7a(%rip)        # 403fb0 <pthread_setaffinity_np@GLIBC_2.34>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <puts@plt>:
  401040:	ff 25 72 2f 00 00    	jmp    *0x2f72(%rip)        # 403fb8 <puts@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <__stack_chk_fail@plt>:
  401050:	ff 25 6a 2f 00 00    	jmp    *0x2f6a(%rip)        # 403fc0 <__stack_chk_fail@GLIBC_2.4>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <nanosleep@plt>:
  401060:	ff 25 62 2f 00 00    	jmp    *0x2f62(%rip)        # 403fc8 <nanosleep@GLIBC_2.2.5>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <calloc@plt>:
  401070:	ff 25 5a 2f 00 00    	jmp    *0x2f5a(%rip)        # 403fd0 <calloc@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <__printf_chk@plt>:
  401080:	ff 25 52 2f 00 00    	jmp    *0x2f52(%rip)        # 403fd8 <__printf_chk@GLIBC_2.3.4>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <pthread_create@plt>:
  401090:	ff 25 4a 2f 00 00    	jmp    *0x2f4a(%rip)        # 403fe0 <pthread_create@GLIBC_2.34>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <pthread_join@plt>:
  4010a0:	ff 25 42 2f 00 00    	jmp    *0x2f42(%rip)        # 403fe8 <pthread_join@GLIBC_2.34>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

00000000004010b0 <main>:
  4010b0:	41 57                	push   %r15
  4010b2:	ba 08 00 00 00       	mov    $0x8,%edx
  4010b7:	bf 01 00 00 00       	mov    $0x1,%edi
  4010bc:	48 8d 35 78 0f 00 00 	lea    0xf78(%rip),%rsi        # 40203b <_IO_stdin_used+0x3b>
  4010c3:	41 56                	push   %r14
  4010c5:	45 31 f6             	xor    %r14d,%r14d
  4010c8:	41 55                	push   %r13
  4010ca:	41 54                	push   %r12
  4010cc:	55                   	push   %rbp
  4010cd:	48 8d 2d ec 0f 00 00 	lea    0xfec(%rip),%rbp        # 4020c0 <_IO_stdin_used+0xc0>
  4010d4:	53                   	push   %rbx
  4010d5:	48 83 ec 78          	sub    $0x78,%rsp
  4010d9:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4010e2:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  4010e7:	31 c0                	xor    %eax,%eax
  4010e9:	e8 92 ff ff ff       	call   401080 <__printf_chk@plt>
  4010ee:	ba 04 00 00 00       	mov    $0x4,%edx
  4010f3:	48 8d 35 53 0f 00 00 	lea    0xf53(%rip),%rsi        # 40204d <_IO_stdin_used+0x4d>
  4010fa:	31 c0                	xor    %eax,%eax
  4010fc:	bf 01 00 00 00       	mov    $0x1,%edi
  401101:	e8 7a ff ff ff       	call   401080 <__printf_chk@plt>
  401106:	ba 20 00 00 00       	mov    $0x20,%edx
  40110b:	48 8d 35 37 0f 00 00 	lea    0xf37(%rip),%rsi        # 402049 <_IO_stdin_used+0x49>
  401112:	31 c0                	xor    %eax,%eax
  401114:	bf 01 00 00 00       	mov    $0x1,%edi
  401119:	e8 62 ff ff ff       	call   401080 <__printf_chk@plt>
  40111e:	ba 04 00 00 00       	mov    $0x4,%edx
  401123:	48 8d 35 32 0f 00 00 	lea    0xf32(%rip),%rsi        # 40205c <_IO_stdin_used+0x5c>
  40112a:	31 c0                	xor    %eax,%eax
  40112c:	bf 01 00 00 00       	mov    $0x1,%edi
  401131:	e8 4a ff ff ff       	call   401080 <__printf_chk@plt>
  401136:	be 08 00 00 00       	mov    $0x8,%esi
  40113b:	bf 04 00 00 00       	mov    $0x4,%edi
  401140:	e8 2b ff ff ff       	call   401070 <calloc@plt>
  401145:	be 38 00 00 00       	mov    $0x38,%esi
  40114a:	bf 04 00 00 00       	mov    $0x4,%edi
  40114f:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401154:	e8 17 ff ff ff       	call   401070 <calloc@plt>
  401159:	be 00 06 00 00       	mov    $0x600,%esi
  40115e:	bf 01 00 00 00       	mov    $0x1,%edi
  401163:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  401168:	e8 03 ff ff ff       	call   401070 <calloc@plt>
  40116d:	be 08 00 00 00       	mov    $0x8,%esi
  401172:	bf 0a 00 00 00       	mov    $0xa,%edi
  401177:	48 89 c3             	mov    %rax,%rbx
  40117a:	e8 f1 fe ff ff       	call   401070 <calloc@plt>
  40117f:	ba 0a 00 00 00       	mov    $0xa,%edx
  401184:	bf 01 00 00 00       	mov    $0x1,%edi
  401189:	48 8d 35 e1 0e 00 00 	lea    0xee1(%rip),%rsi        # 402071 <_IO_stdin_used+0x71>
  401190:	48 89 04 24          	mov    %rax,(%rsp)
  401194:	31 c0                	xor    %eax,%eax
  401196:	e8 e5 fe ff ff       	call   401080 <__printf_chk@plt>
  40119b:	be 20 00 00 00       	mov    $0x20,%esi
  4011a0:	bf 0a 00 00 00       	mov    $0xa,%edi
  4011a5:	e8 c6 fe ff ff       	call   401070 <calloc@plt>
  4011aa:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  4011af:	49 89 c7             	mov    %rax,%r15
  4011b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  4011b8:	45 89 f5             	mov    %r14d,%r13d
  4011bb:	4d 89 f4             	mov    %r14,%r12
  4011be:	49 83 c6 01          	add    $0x1,%r14
  4011c2:	48 89 ee             	mov    %rbp,%rsi
  4011c5:	4d 89 f0             	mov    %r14,%r8
  4011c8:	4c 89 e1             	mov    %r12,%rcx
  4011cb:	44 89 ea             	mov    %r13d,%edx
  4011ce:	bf 01 00 00 00       	mov    $0x1,%edi
  4011d3:	31 c0                	xor    %eax,%eax
  4011d5:	49 83 c7 20          	add    $0x20,%r15
  4011d9:	e8 a2 fe ff ff       	call   401080 <__printf_chk@plt>
  4011de:	66 49 0f 6e c4       	movq   %r12,%xmm0
  4011e3:	66 49 0f 6e ce       	movq   %r14,%xmm1
  4011e8:	45 89 6f f8          	mov    %r13d,-0x8(%r15)
  4011ec:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
  4011f0:	41 c7 47 f0 01 00 00 00 	movl   $0x1,-0x10(%r15)
  4011f8:	41 0f 11 47 e0       	movups %xmm0,-0x20(%r15)
  4011fd:	49 83 fe 0a          	cmp    $0xa,%r14
  401201:	75 b5                	jne    4011b8 <main+0x108>
  401203:	ba 0a 00 00 00       	mov    $0xa,%edx
  401208:	48 8d 35 72 0e 00 00 	lea    0xe72(%rip),%rsi        # 402081 <_IO_stdin_used+0x81>
  40120f:	31 c0                	xor    %eax,%eax
  401211:	31 ed                	xor    %ebp,%ebp
  401213:	bf 01 00 00 00       	mov    $0x1,%edi
  401218:	49 89 ec             	mov    %rbp,%r12
  40121b:	49 89 dd             	mov    %rbx,%r13
  40121e:	e8 5d fe ff ff       	call   401080 <__printf_chk@plt>
  401223:	4c 8b 3c 24          	mov    (%rsp),%r15
  401227:	be 08 00 00 00       	mov    $0x8,%esi
  40122c:	66 0f 6f 05 dc 0e 00 00 	movdqa 0xedc(%rip),%xmm0        # 402110 <_IO_stdin_used+0x110>
  401234:	bf 04 00 00 00       	mov    $0x4,%edi
  401239:	41 0f 11 07          	movups %xmm0,(%r15)
  40123d:	41 0f 11 47 10       	movups %xmm0,0x10(%r15)
  401242:	41 0f 11 47 20       	movups %xmm0,0x20(%r15)
  401247:	41 0f 11 47 30       	movups %xmm0,0x30(%r15)
  40124c:	41 0f 11 47 40       	movups %xmm0,0x40(%r15)
  401251:	e8 1a fe ff ff       	call   401070 <calloc@plt>
  401256:	66 48 0f 6e f3       	movq   %rbx,%xmm6
  40125b:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
  401260:	66 48 0f 6e e8       	movq   %rax,%xmm5
  401265:	4c 89 bb e0 00 00 00 	mov    %r15,0xe0(%rbx)
  40126c:	48 89 c5             	mov    %rax,%rbp
  40126f:	4c 8d 3d 72 0e 00 00 	lea    0xe72(%rip),%r15        # 4020e8 <_IO_stdin_used+0xe8>
  401276:	66 0f 6c ee          	punpcklqdq %xmm6,%xmm5
  40127a:	0f 29 2c 24          	movaps %xmm5,(%rsp)
  40127e:	be 80 00 00 00       	mov    $0x80,%esi
  401283:	bf 01 00 00 00       	mov    $0x1,%edi
  401288:	49 81 c5 80 01 00 00 	add    $0x180,%r13
  40128f:	e8 dc fd ff ff       	call   401070 <calloc@plt>
  401294:	41 8d 4c 24 01       	lea    0x1(%r12),%ecx
  401299:	ba 01 00 00 00       	mov    $0x1,%edx
  40129e:	4c 89 fe             	mov    %r15,%rsi
  4012a1:	48 d3 e2             	shl    %cl,%rdx
  4012a4:	48 09 10             	or     %rdx,(%rax)
  4012a7:	bf 01 00 00 00       	mov    $0x1,%edi
  4012ac:	44 89 e2             	mov    %r12d,%edx
  4012af:	49 89 85 68 ff ff ff 	mov    %rax,-0x98(%r13)
  4012b6:	31 c0                	xor    %eax,%eax
  4012b8:	e8 c3 fd ff ff       	call   401080 <__printf_chk@plt>
  4012bd:	43 8d 04 24          	lea    (%r12,%r12,1),%eax
  4012c1:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
  4012c6:	66 0f 6f 1d 52 0e 00 00 	movdqa 0xe52(%rip),%xmm3        # 402120 <_IO_stdin_used+0x120>
  4012ce:	41 89 45 88          	mov    %eax,-0x78(%r13)
  4012d2:	48 8b 05 77 0e 00 00 	mov    0xe77(%rip),%rax        # 402150 <_IO_stdin_used+0x150>
  4012d9:	66 0f 6f 25 4f 0e 00 00 	movdqa 0xe4f(%rip),%xmm4        # 402130 <_IO_stdin_used+0x130>
  4012e1:	45 89 a5 54 ff ff ff 	mov    %r12d,-0xac(%r13)
  4012e8:	49 89 45 80          	mov    %rax,-0x80(%r13)
  4012ec:	48 8b 05 65 0e 00 00 	mov    0xe65(%rip),%rax        # 402158 <_IO_stdin_used+0x158>
  4012f3:	4a c7 44 e5 00 00 00 00 00 	movq   $0x0,0x0(%rbp,%r12,8)
  4012fc:	49 83 c4 01          	add    $0x1,%r12
  401300:	49 89 85 48 ff ff ff 	mov    %rax,-0xb8(%r13)
  401307:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  40130c:	41 c7 85 70 ff ff ff 00 00 00 00 	movl   $0x0,-0x90(%r13)
  401317:	41 c7 85 50 ff ff ff 0a 00 00 00 	movl   $0xa,-0xb0(%r13)
  401322:	41 c7 85 58 ff ff ff 04 00 00 00 	movl   $0x4,-0xa8(%r13)
  40132d:	41 0f 29 95 00 ff ff ff 	movaps %xmm2,-0x100(%r13)
  401335:	49 89 9d 10 ff ff ff 	mov    %rbx,-0xf0(%r13)
  40133c:	41 0f 29 9d 80 fe ff ff 	movaps %xmm3,-0x180(%r13)
  401344:	49 89 45 90          	mov    %rax,-0x70(%r13)
  401348:	41 0f 11 65 a8       	movups %xmm4,-0x58(%r13)
  40134d:	49 c7 45 b8 00 00 00 00 	movq   $0x0,-0x48(%r13)
  401355:	49 83 fc 04          	cmp    $0x4,%r12
  401359:	0f 85 1f ff ff ff    	jne    40127e <main+0x1ce>
  40135f:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
  401364:	4c 8d b3 00 06 00 00 	lea    0x600(%rbx),%r14
  40136b:	48 89 1c 24          	mov    %rbx,(%rsp)
  40136f:	4c 8b 64 24 28       	mov    0x28(%rsp),%r12
  401374:	49 c7 c5 30 1a 40 00 	mov    $0x401a30,%r13
  40137b:	4c 89 fd             	mov    %r15,%rbp
  40137e:	4c 89 fb             	mov    %r15,%rbx
  401381:	4d 89 f7             	mov    %r14,%r15
  401384:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
  401389:	4c 89 e1             	mov    %r12,%rcx
  40138c:	48 89 df             	mov    %rbx,%rdi
  40138f:	4c 89 ea             	mov    %r13,%rdx
  401392:	4c 89 f6             	mov    %r14,%rsi
  401395:	e8 f6 fc ff ff       	call   401090 <pthread_create@plt>
  40139a:	49 8b 94 24 e8 00 00 00 	mov    0xe8(%r12),%rdx
  4013a2:	48 8b 3b             	mov    (%rbx),%rdi
  4013a5:	be 08 00 00 00       	mov    $0x8,%esi
  4013aa:	49 81 c4 80 01 00 00 	add    $0x180,%r12
  4013b1:	48 83 c3 08          	add    $0x8,%rbx
  4013b5:	e8 76 fc ff ff       	call   401030 <pthread_setaffinity_np@plt>
  4013ba:	4d 39 e7             	cmp    %r12,%r15
  4013bd:	75 ca                	jne    401389 <main+0x2d9>
  4013bf:	48 8b 1c 24          	mov    (%rsp),%rbx
  4013c3:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  4013c8:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  4013cd:	66 0f 6f 05 6b 0d 00 00 	movdqa 0xd6b(%rip),%xmm0        # 402140 <_IO_stdin_used+0x140>
  4013d5:	4c 8d 6c 24 38       	lea    0x38(%rsp),%r13
  4013da:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  4013df:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4013e3:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  4013e8:	e8 73 fc ff ff       	call   401060 <nanosleep@plt>
  4013ed:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
  4013f2:	c7 83 cc 00 00 00 00 00 00 00 	movl   $0x0,0xcc(%rbx)
  4013fc:	c7 83 4c 02 00 00 00 00 00 00 	movl   $0x0,0x24c(%rbx)
  401406:	c7 83 cc 03 00 00 00 00 00 00 	movl   $0x0,0x3cc(%rbx)
  401410:	49 83 c4 20          	add    $0x20,%r12
  401414:	c7 83 4c 05 00 00 00 00 00 00 	movl   $0x0,0x54c(%rbx)
  40141e:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
  401422:	4c 89 ee             	mov    %r13,%rsi
  401425:	48 83 c5 08          	add    $0x8,%rbp
  401429:	e8 72 fc ff ff       	call   4010a0 <pthread_join@plt>
  40142e:	4c 39 e5             	cmp    %r12,%rbp
  401431:	75 eb                	jne    40141e <main+0x36e>
  401433:	48 8d 3d 53 0c 00 00 	lea    0xc53(%rip),%rdi        # 40208d <_IO_stdin_used+0x8d>
  40143a:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
  401444:	e8 f7 fb ff ff       	call   401040 <puts@plt>
  401449:	48 8b 8b b0 03 00 00 	mov    0x3b0(%rbx),%rcx
  401450:	bf 01 00 00 00       	mov    $0x1,%edi
  401455:	48 03 8b 30 02 00 00 	add    0x230(%rbx),%rcx
  40145c:	48 03 8b b0 00 00 00 	add    0xb0(%rbx),%rcx
  401463:	48 03 8b 30 05 00 00 	add    0x530(%rbx),%rcx
  40146a:	48 8d 35 31 0c 00 00 	lea    0xc31(%rip),%rsi        # 4020a2 <_IO_stdin_used+0xa2>
  401471:	48 89 c8             	mov    %rcx,%rax
  401474:	48 c1 f9 3f          	sar    $0x3f,%rcx
  401478:	48 f7 ed             	imul   %rbp
  40147b:	31 c0                	xor    %eax,%eax
  40147d:	48 d1 fa             	sar    %rdx
  401480:	48 29 ca             	sub    %rcx,%rdx
  401483:	e8 f8 fb ff ff       	call   401080 <__printf_chk@plt>
  401488:	48 8b 8b 38 02 00 00 	mov    0x238(%rbx),%rcx
  40148f:	bf 01 00 00 00       	mov    $0x1,%edi
  401494:	48 03 8b b8 03 00 00 	add    0x3b8(%rbx),%rcx
  40149b:	48 03 8b b8 00 00 00 	add    0xb8(%rbx),%rcx
  4014a2:	48 03 8b 38 05 00 00 	add    0x538(%rbx),%rcx
  4014a9:	48 8d 35 fd 0b 00 00 	lea    0xbfd(%rip),%rsi        # 4020ad <_IO_stdin_used+0xad>
  4014b0:	48 89 c8             	mov    %rcx,%rax
  4014b3:	48 c1 f9 3f          	sar    $0x3f,%rcx
  4014b7:	48 f7 ed             	imul   %rbp
  4014ba:	31 c0                	xor    %eax,%eax
  4014bc:	48 d1 fa             	sar    %rdx
  4014bf:	48 29 ca             	sub    %rcx,%rdx
  4014c2:	e8 b9 fb ff ff       	call   401080 <__printf_chk@plt>
  4014c7:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  4014cc:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4014d5:	75 11                	jne    4014e8 <main+0x438>
  4014d7:	48 83 c4 78          	add    $0x78,%rsp
  4014db:	31 c0                	xor    %eax,%eax
  4014dd:	5b                   	pop    %rbx
  4014de:	5d                   	pop    %rbp
  4014df:	41 5c                	pop    %r12
  4014e1:	41 5d                	pop    %r13
  4014e3:	41 5e                	pop    %r14
  4014e5:	41 5f                	pop    %r15
  4014e7:	c3                   	ret
  4014e8:	e8 63 fb ff ff       	call   401050 <__stack_chk_fail@plt>
  4014ed:	0f 1f 00             	nopl   (%rax)

00000000004014f0 <_start>:
  4014f0:	f3 0f 1e fa          	endbr64
  4014f4:	31 ed                	xor    %ebp,%ebp
  4014f6:	49 89 d1             	mov    %rdx,%r9
  4014f9:	5e                   	pop    %rsi
  4014fa:	48 89 e2             	mov    %rsp,%rdx
  4014fd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401501:	50                   	push   %rax
  401502:	54                   	push   %rsp
  401503:	45 31 c0             	xor    %r8d,%r8d
  401506:	31 c9                	xor    %ecx,%ecx
  401508:	48 c7 c7 b0 10 40 00 	mov    $0x4010b0,%rdi
  40150f:	ff 15 db 2a 00 00    	call   *0x2adb(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  401515:	f4                   	hlt
  401516:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401520 <_dl_relocate_static_pie>:
  401520:	f3 0f 1e fa          	endbr64
  401524:	c3                   	ret
  401525:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40152f:	90                   	nop

0000000000401530 <deregister_tm_clones>:
  401530:	b8 10 40 40 00       	mov    $0x404010,%eax
  401535:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  40153b:	74 13                	je     401550 <deregister_tm_clones+0x20>
  40153d:	b8 00 00 00 00       	mov    $0x0,%eax
  401542:	48 85 c0             	test   %rax,%rax
  401545:	74 09                	je     401550 <deregister_tm_clones+0x20>
  401547:	bf 10 40 40 00       	mov    $0x404010,%edi
  40154c:	ff e0                	jmp    *%rax
  40154e:	66 90                	xchg   %ax,%ax
  401550:	c3                   	ret
  401551:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40155c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401560 <register_tm_clones>:
  401560:	be 10 40 40 00       	mov    $0x404010,%esi
  401565:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  40156c:	48 89 f0             	mov    %rsi,%rax
  40156f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401573:	48 c1 f8 03          	sar    $0x3,%rax
  401577:	48 01 c6             	add    %rax,%rsi
  40157a:	48 d1 fe             	sar    %rsi
  40157d:	74 11                	je     401590 <register_tm_clones+0x30>
  40157f:	b8 00 00 00 00       	mov    $0x0,%eax
  401584:	48 85 c0             	test   %rax,%rax
  401587:	74 07                	je     401590 <register_tm_clones+0x30>
  401589:	bf 10 40 40 00       	mov    $0x404010,%edi
  40158e:	ff e0                	jmp    *%rax
  401590:	c3                   	ret
  401591:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40159c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004015a0 <__do_global_dtors_aux>:
  4015a0:	f3 0f 1e fa          	endbr64
  4015a4:	80 3d 65 2a 00 00 00 	cmpb   $0x0,0x2a65(%rip)        # 404010 <__TMC_END__>
  4015ab:	75 13                	jne    4015c0 <__do_global_dtors_aux+0x20>
  4015ad:	55                   	push   %rbp
  4015ae:	48 89 e5             	mov    %rsp,%rbp
  4015b1:	e8 7a ff ff ff       	call   401530 <deregister_tm_clones>
  4015b6:	c6 05 53 2a 00 00 01 	movb   $0x1,0x2a53(%rip)        # 404010 <__TMC_END__>
  4015bd:	5d                   	pop    %rbp
  4015be:	c3                   	ret
  4015bf:	90                   	nop
  4015c0:	c3                   	ret
  4015c1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4015cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004015d0 <frame_dummy>:
  4015d0:	f3 0f 1e fa          	endbr64
  4015d4:	eb 8a                	jmp    401560 <register_tm_clones>
  4015d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004015e0 <pollthreads>:
  4015e0:	83 bf d8 00 00 00 01 	cmpl   $0x1,0xd8(%rdi)
  4015e7:	0f 8e 93 00 00 00    	jle    401680 <pollthreads+0xa0>
  4015ed:	55                   	push   %rbp
  4015ee:	4c 8b 9f 90 00 00 00 	mov    0x90(%rdi),%r11
  4015f5:	49 89 f1             	mov    %rsi,%r9
  4015f8:	49 89 d2             	mov    %rdx,%r10
  4015fb:	53                   	push   %rbx
  4015fc:	48 89 ce             	mov    %rcx,%rsi
  4015ff:	ba 01 00 00 00       	mov    $0x1,%edx
  401604:	0f 1f 40 00          	nopl   0x0(%rax)
  401608:	48 63 ca             	movslq %edx,%rcx
  40160b:	48 8d 04 49          	lea    (%rcx,%rcx,2),%rax
  40160f:	48 c1 e0 07          	shl    $0x7,%rax
  401613:	4c 01 d8             	add    %r11,%rax
  401616:	48 8b 98 80 00 00 00 	mov    0x80(%rax),%rbx
  40161d:	48 c7 80 38 01 00 00 00 00 00 00 	movq   $0x0,0x138(%rax)
  401628:	48 8b 04 cb          	mov    (%rbx,%rcx,8),%rax
  40162c:	48 85 c0             	test   %rax,%rax
  40162f:	0f 94 c3             	sete   %bl
  401632:	a8 04                	test   $0x4,%al
  401634:	75 04                	jne    40163a <pollthreads+0x5a>
  401636:	84 db                	test   %bl,%bl
  401638:	74 0d                	je     401647 <pollthreads+0x67>
  40163a:	49 63 08             	movslq (%r8),%rcx
  40163d:	8d 69 01             	lea    0x1(%rcx),%ebp
  401640:	41 89 28             	mov    %ebp,(%r8)
  401643:	41 89 14 8a          	mov    %edx,(%r10,%rcx,4)
  401647:	a8 08                	test   $0x8,%al
  401649:	75 04                	jne    40164f <pollthreads+0x6f>
  40164b:	84 db                	test   %bl,%bl
  40164d:	74 21                	je     401670 <pollthreads+0x90>
  40164f:	48 63 06             	movslq (%rsi),%rax
  401652:	8d 48 01             	lea    0x1(%rax),%ecx
  401655:	89 0e                	mov    %ecx,(%rsi)
  401657:	41 89 14 81          	mov    %edx,(%r9,%rax,4)
  40165b:	83 c2 01             	add    $0x1,%edx
  40165e:	39 97 d8 00 00 00    	cmp    %edx,0xd8(%rdi)
  401664:	7f a2                	jg     401608 <pollthreads+0x28>
  401666:	31 c0                	xor    %eax,%eax
  401668:	5b                   	pop    %rbx
  401669:	5d                   	pop    %rbp
  40166a:	c3                   	ret
  40166b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401670:	83 c2 01             	add    $0x1,%edx
  401673:	39 97 d8 00 00 00    	cmp    %edx,0xd8(%rdi)
  401679:	7f 8d                	jg     401608 <pollthreads+0x28>
  40167b:	31 c0                	xor    %eax,%eax
  40167d:	5b                   	pop    %rbx
  40167e:	5d                   	pop    %rbp
  40167f:	c3                   	ret
  401680:	31 c0                	xor    %eax,%eax
  401682:	c3                   	ret
  401683:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40168e:	66 90                	xchg   %ax,%ax

0000000000401690 <findavailable>:
  401690:	49 89 fb             	mov    %rdi,%r11
  401693:	48 8b bf 28 01 00 00 	mov    0x128(%rdi),%rdi
  40169a:	44 8b 0a             	mov    (%rdx),%r9d
  40169d:	48 83 c7 01          	add    $0x1,%rdi
  4016a1:	48 85 ff             	test   %rdi,%rdi
  4016a4:	7e 2c                	jle    4016d2 <findavailable+0x42>
  4016a6:	4d 8b 93 10 01 00 00 	mov    0x110(%r11),%r10
  4016ad:	31 c9                	xor    %ecx,%ecx
  4016af:	45 31 c0             	xor    %r8d,%r8d
  4016b2:	31 c0                	xor    %eax,%eax
  4016b4:	0f 1f 40 00          	nopl   0x0(%rax)
  4016b8:	48 c1 e0 05          	shl    $0x5,%rax
  4016bc:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  4016c2:	74 1c                	je     4016e0 <findavailable+0x50>
  4016c4:	83 c1 01             	add    $0x1,%ecx
  4016c7:	48 63 c1             	movslq %ecx,%rax
  4016ca:	49 89 c0             	mov    %rax,%r8
  4016cd:	48 39 f8             	cmp    %rdi,%rax
  4016d0:	7c e6                	jl     4016b8 <findavailable+0x28>
  4016d2:	31 c0                	xor    %eax,%eax
  4016d4:	45 85 c9             	test   %r9d,%r9d
  4016d7:	0f 94 c0             	sete   %al
  4016da:	c3                   	ret
  4016db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4016e0:	49 63 c1             	movslq %r9d,%rax
  4016e3:	83 c1 01             	add    $0x1,%ecx
  4016e6:	41 83 c1 01          	add    $0x1,%r9d
  4016ea:	4c 89 04 c6          	mov    %r8,(%rsi,%rax,8)
  4016ee:	49 8b bb 28 01 00 00 	mov    0x128(%r11),%rdi
  4016f5:	4c 63 c1             	movslq %ecx,%r8
  4016f8:	44 89 0a             	mov    %r9d,(%rdx)
  4016fb:	4c 89 c0             	mov    %r8,%rax
  4016fe:	48 83 c7 01          	add    $0x1,%rdi
  401702:	4c 39 c7             	cmp    %r8,%rdi
  401705:	7f b1                	jg     4016b8 <findavailable+0x28>
  401707:	31 c0                	xor    %eax,%eax
  401709:	45 85 c9             	test   %r9d,%r9d
  40170c:	0f 94 c0             	sete   %al
  40170f:	c3                   	ret

0000000000401710 <singlewriter>:
  401710:	41 56                	push   %r14
  401712:	49 89 c8             	mov    %rcx,%r8
  401715:	41 55                	push   %r13
  401717:	49 89 d5             	mov    %rdx,%r13
  40171a:	41 54                	push   %r12
  40171c:	49 89 cc             	mov    %rcx,%r12
  40171f:	4c 89 e9             	mov    %r13,%rcx
  401722:	55                   	push   %rbp
  401723:	48 89 f5             	mov    %rsi,%rbp
  401726:	53                   	push   %rbx
  401727:	48 89 fb             	mov    %rdi,%rbx
  40172a:	48 83 ec 20          	sub    $0x20,%rsp
  40172e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401737:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  40173c:	31 c0                	xor    %eax,%eax
  40173e:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401743:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  40174b:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  401753:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  40175b:	e8 30 ff ff ff       	call   401690 <findavailable>
  401760:	83 f8 01             	cmp    $0x1,%eax
  401763:	0f 84 5b 01 00 00    	je     4018c4 <singlewriter+0x1b4>
  401769:	48 89 df             	mov    %rbx,%rdi
  40176c:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401771:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401776:	4c 89 e2             	mov    %r12,%rdx
  401779:	4c 89 ee             	mov    %r13,%rsi
  40177c:	e8 5f fe ff ff       	call   4015e0 <pollthreads>
  401781:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401786:	85 ff                	test   %edi,%edi
  401788:	0f 8e 53 01 00 00    	jle    4018e1 <singlewriter+0x1d1>
  40178e:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
  401793:	31 c9                	xor    %ecx,%ecx
  401795:	eb 5e                	jmp    4017f5 <singlewriter+0xe5>
  401797:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  4017a0:	48 8b 54 cd 00       	mov    0x0(%rbp,%rcx,8),%rdx
  4017a5:	49 63 44 8d 00       	movslq 0x0(%r13,%rcx,4),%rax
  4017aa:	44 8d 71 01          	lea    0x1(%rcx),%r14d
  4017ae:	48 83 c1 01          	add    $0x1,%rcx
  4017b2:	48 c1 e2 05          	shl    $0x5,%rdx
  4017b6:	48 03 93 10 01 00 00 	add    0x110(%rbx),%rdx
  4017bd:	48 89 c6             	mov    %rax,%rsi
  4017c0:	f3 0f 6f 02          	movdqu (%rdx),%xmm0
  4017c4:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
  4017c8:	c7 42 10 02 00 00 00 	movl   $0x2,0x10(%rdx)
  4017cf:	48 c1 e0 07          	shl    $0x7,%rax
  4017d3:	48 03 83 90 00 00 00 	add    0x90(%rbx),%rax
  4017da:	48 89 90 18 01 00 00 	mov    %rdx,0x118(%rax)
  4017e1:	89 72 14             	mov    %esi,0x14(%rdx)
  4017e4:	48 83 88 38 01 00 00 10 	orq    $0x10,0x138(%rax)
  4017ec:	0f 11 40 18          	movups %xmm0,0x18(%rax)
  4017f0:	48 39 cf             	cmp    %rcx,%rdi
  4017f3:	74 14                	je     401809 <singlewriter+0xf9>
  4017f5:	41 89 ce             	mov    %ecx,%r14d
  4017f8:	49 39 c8             	cmp    %rcx,%r8
  4017fb:	75 a3                	jne    4017a0 <singlewriter+0x90>
  4017fd:	48 8d 3d 00 08 00 00 	lea    0x800(%rip),%rdi        # 402004 <_IO_stdin_used+0x4>
  401804:	e8 37 f8 ff ff       	call   401040 <puts@plt>
  401809:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  40180e:	45 85 c0             	test   %r8d,%r8d
  401811:	7e 6f                	jle    401882 <singlewriter+0x172>
  401813:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401817:	45 01 f0             	add    %r14d,%r8d
  40181a:	eb 61                	jmp    40187d <singlewriter+0x16d>
  40181c:	0f 1f 40 00          	nopl   0x0(%rax)
  401820:	41 8d 76 01          	lea    0x1(%r14),%esi
  401824:	4d 63 f6             	movslq %r14d,%r14
  401827:	49 63 04 24          	movslq (%r12),%rax
  40182b:	49 83 c4 04          	add    $0x4,%r12
  40182f:	4a 8b 54 f5 00       	mov    0x0(%rbp,%r14,8),%rdx
  401834:	48 89 c1             	mov    %rax,%rcx
  401837:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
  40183b:	48 c1 e2 05          	shl    $0x5,%rdx
  40183f:	48 03 93 10 01 00 00 	add    0x110(%rbx),%rdx
  401846:	48 c1 e0 07          	shl    $0x7,%rax
  40184a:	48 03 83 90 00 00 00 	add    0x90(%rbx),%rax
  401851:	f3 0f 6f 0a          	movdqu (%rdx),%xmm1
  401855:	c7 42 10 03 00 00 00 	movl   $0x3,0x10(%rdx)
  40185c:	48 89 90 20 01 00 00 	mov    %rdx,0x120(%rax)
  401863:	89 4a 14             	mov    %ecx,0x14(%rdx)
  401866:	48 83 88 38 01 00 00 20 	orq    $0x20,0x138(%rax)
  40186e:	0f 29 88 a0 00 00 00 	movaps %xmm1,0xa0(%rax)
  401875:	44 39 c6             	cmp    %r8d,%esi
  401878:	74 08                	je     401882 <singlewriter+0x172>
  40187a:	41 89 f6             	mov    %esi,%r14d
  40187d:	44 39 f7             	cmp    %r14d,%edi
  401880:	75 9e                	jne    401820 <singlewriter+0x110>
  401882:	48 63 b3 d8 00 00 00 	movslq 0xd8(%rbx),%rsi
  401889:	85 f6                	test   %esi,%esi
  40188b:	7e 35                	jle    4018c2 <singlewriter+0x1b2>
  40188d:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
  401894:	48 c1 e6 03          	shl    $0x3,%rsi
  401898:	31 d2                	xor    %edx,%edx
  40189a:	48 05 38 01 00 00    	add    $0x138,%rax
  4018a0:	48 8b 08             	mov    (%rax),%rcx
  4018a3:	48 85 c9             	test   %rcx,%rcx
  4018a6:	74 0b                	je     4018b3 <singlewriter+0x1a3>
  4018a8:	48 8b b8 48 ff ff ff 	mov    -0xb8(%rax),%rdi
  4018af:	48 89 0c 17          	mov    %rcx,(%rdi,%rdx,1)
  4018b3:	48 83 c2 08          	add    $0x8,%rdx
  4018b7:	48 05 80 01 00 00    	add    $0x180,%rax
  4018bd:	48 39 f2             	cmp    %rsi,%rdx
  4018c0:	75 de                	jne    4018a0 <singlewriter+0x190>
  4018c2:	31 c0                	xor    %eax,%eax
  4018c4:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  4018c9:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  4018d2:	75 15                	jne    4018e9 <singlewriter+0x1d9>
  4018d4:	48 83 c4 20          	add    $0x20,%rsp
  4018d8:	5b                   	pop    %rbx
  4018d9:	5d                   	pop    %rbp
  4018da:	41 5c                	pop    %r12
  4018dc:	41 5d                	pop    %r13
  4018de:	41 5e                	pop    %r14
  4018e0:	c3                   	ret
  4018e1:	45 31 f6             	xor    %r14d,%r14d
  4018e4:	e9 20 ff ff ff       	jmp    401809 <singlewriter+0xf9>
  4018e9:	e8 62 f7 ff ff       	call   401050 <__stack_chk_fail@plt>
  4018ee:	66 90                	xchg   %ax,%ax

00000000004018f0 <threadwork>:
  4018f0:	53                   	push   %rbx
  4018f1:	48 89 f8             	mov    %rdi,%rax
  4018f4:	48 63 8f d4 00 00 00 	movslq 0xd4(%rdi),%rcx
  4018fb:	48 8b 97 80 00 00 00 	mov    0x80(%rdi),%rdx
  401902:	48 63 8f d4 00 00 00 	movslq 0xd4(%rdi),%rcx
  401909:	48 8b 97 80 00 00 00 	mov    0x80(%rdi),%rdx
  401910:	48 8d 1c ca          	lea    (%rdx,%rcx,8),%rbx
  401914:	4c 8b 1b             	mov    (%rbx),%r11
  401917:	4c 89 9f 40 01 00 00 	mov    %r11,0x140(%rdi)
  40191e:	41 f6 c3 10          	test   $0x10,%r11b
  401922:	75 74                	jne    401998 <threadwork+0xa8>
  401924:	41 83 e3 20          	and    $0x20,%r11d
  401928:	74 66                	je     401990 <threadwork+0xa0>
  40192a:	41 b9 04 00 00 00    	mov    $0x4,%r9d
  401930:	48 8b 88 a0 00 00 00 	mov    0xa0(%rax),%rcx
  401937:	48 8b b8 a8 00 00 00 	mov    0xa8(%rax),%rdi
  40193e:	89 ca                	mov    %ecx,%edx
  401940:	48 63 c9             	movslq %ecx,%rcx
  401943:	48 39 f9             	cmp    %rdi,%rcx
  401946:	7d 37                	jge    40197f <threadwork+0x8f>
  401948:	48 8b 88 88 00 00 00 	mov    0x88(%rax),%rcx
  40194f:	48 8b b0 b8 00 00 00 	mov    0xb8(%rax),%rsi
  401956:	4c 8b 81 e0 00 00 00 	mov    0xe0(%rcx),%r8
  40195d:	48 63 ca             	movslq %edx,%rcx
  401960:	41 c7 44 c8 04 01 00 00 00 	movl   $0x1,0x4(%r8,%rcx,8)
  401969:	83 c2 01             	add    $0x1,%edx
  40196c:	48 83 c6 01          	add    $0x1,%rsi
  401970:	48 63 ca             	movslq %edx,%rcx
  401973:	48 39 f9             	cmp    %rdi,%rcx
  401976:	7c e8                	jl     401960 <threadwork+0x70>
  401978:	48 89 b0 b8 00 00 00 	mov    %rsi,0xb8(%rax)
  40197f:	48 8b 80 20 01 00 00 	mov    0x120(%rax),%rax
  401986:	c7 40 10 01 00 00 00 	movl   $0x1,0x10(%rax)
  40198d:	4c 89 0b             	mov    %r9,(%rbx)
  401990:	5b                   	pop    %rbx
  401991:	c3                   	ret
  401992:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  401998:	48 8b 57 18          	mov    0x18(%rdi),%rdx
  40199c:	4c 8b 47 20          	mov    0x20(%rdi),%r8
  4019a0:	89 d1                	mov    %edx,%ecx
  4019a2:	48 63 d2             	movslq %edx,%rdx
  4019a5:	4c 39 c2             	cmp    %r8,%rdx
  4019a8:	7d 51                	jge    4019fb <threadwork+0x10b>
  4019aa:	48 8b 97 88 00 00 00 	mov    0x88(%rdi),%rdx
  4019b1:	48 8b bf b0 00 00 00 	mov    0xb0(%rdi),%rdi
  4019b8:	48 63 f1             	movslq %ecx,%rsi
  4019bb:	4c 8b 92 e0 00 00 00 	mov    0xe0(%rdx),%r10
  4019c2:	48 8d 57 01          	lea    0x1(%rdi),%rdx
  4019c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4019d0:	83 c1 01             	add    $0x1,%ecx
  4019d3:	49 8d 3c f2          	lea    (%r10,%rsi,8),%rdi
  4019d7:	49 89 d1             	mov    %rdx,%r9
  4019da:	48 83 c2 01          	add    $0x1,%rdx
  4019de:	48 63 f1             	movslq %ecx,%rsi
  4019e1:	c7 47 04 00 00 00 00 	movl   $0x0,0x4(%rdi)
  4019e8:	4c 39 c6             	cmp    %r8,%rsi
  4019eb:	7c e3                	jl     4019d0 <threadwork+0xe0>
  4019ed:	4c 89 88 b0 00 00 00 	mov    %r9,0xb0(%rax)
  4019f4:	c7 47 04 00 00 00 00 	movl   $0x0,0x4(%rdi)
  4019fb:	48 8b 90 18 01 00 00 	mov    0x118(%rax),%rdx
  401a02:	41 83 e3 20          	and    $0x20,%r11d
  401a06:	41 b9 08 00 00 00    	mov    $0x8,%r9d
  401a0c:	c7 42 10 01 00 00 00 	movl   $0x1,0x10(%rdx)
  401a13:	0f 84 74 ff ff ff    	je     40198d <threadwork+0x9d>
  401a19:	41 b9 0c 00 00 00    	mov    $0xc,%r9d
  401a1f:	e9 0c ff ff ff       	jmp    401930 <threadwork+0x40>
  401a24:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401a2f:	90                   	nop

0000000000401a30 <work>:
  401a30:	41 56                	push   %r14
  401a32:	48 8d 35 e4 05 00 00 	lea    0x5e4(%rip),%rsi        # 40201d <_IO_stdin_used+0x1d>
  401a39:	41 55                	push   %r13
  401a3b:	41 54                	push   %r12
  401a3d:	55                   	push   %rbp
  401a3e:	53                   	push   %rbx
  401a3f:	8b 87 d4 00 00 00    	mov    0xd4(%rdi),%eax
  401a45:	48 89 fb             	mov    %rdi,%rbx
  401a48:	44 8b b7 08 01 00 00 	mov    0x108(%rdi),%r14d
  401a4f:	8d 50 01             	lea    0x1(%rax),%edx
  401a52:	31 c0                	xor    %eax,%eax
  401a54:	0f af 97 00 01 00 00 	imul   0x100(%rdi),%edx
  401a5b:	bf 01 00 00 00       	mov    $0x1,%edi
  401a60:	e8 1b f6 ff ff       	call   401080 <__printf_chk@plt>
  401a65:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
  401a6c:	be 08 00 00 00       	mov    $0x8,%esi
  401a71:	48 8d 78 01          	lea    0x1(%rax),%rdi
  401a75:	e8 f6 f5 ff ff       	call   401070 <calloc@plt>
  401a7a:	48 63 ab d8 00 00 00 	movslq 0xd8(%rbx),%rbp
  401a81:	be 04 00 00 00       	mov    $0x4,%esi
  401a86:	49 89 c5             	mov    %rax,%r13
  401a89:	48 89 ef             	mov    %rbp,%rdi
  401a8c:	e8 df f5 ff ff       	call   401070 <calloc@plt>
  401a91:	48 89 ef             	mov    %rbp,%rdi
  401a94:	be 04 00 00 00       	mov    $0x4,%esi
  401a99:	49 89 c4             	mov    %rax,%r12
  401a9c:	e8 cf f5 ff ff       	call   401070 <calloc@plt>
  401aa1:	83 bb cc 00 00 00 01 	cmpl   $0x1,0xcc(%rbx)
  401aa8:	44 89 b3 c4 00 00 00 	mov    %r14d,0xc4(%rbx)
  401aaf:	48 89 c5             	mov    %rax,%rbp
  401ab2:	75 28                	jne    401adc <work+0xac>
  401ab4:	0f 1f 40 00          	nopl   0x0(%rax)
  401ab8:	8b 83 d4 00 00 00    	mov    0xd4(%rbx),%eax
  401abe:	85 c0                	test   %eax,%eax
  401ac0:	75 3e                	jne    401b00 <work+0xd0>
  401ac2:	48 89 e9             	mov    %rbp,%rcx
  401ac5:	4c 89 e2             	mov    %r12,%rdx
  401ac8:	4c 89 ee             	mov    %r13,%rsi
  401acb:	48 89 df             	mov    %rbx,%rdi
  401ace:	e8 3d fc ff ff       	call   401710 <singlewriter>
  401ad3:	83 bb cc 00 00 00 01 	cmpl   $0x1,0xcc(%rbx)
  401ada:	74 dc                	je     401ab8 <work+0x88>
  401adc:	8b 93 d4 00 00 00    	mov    0xd4(%rbx),%edx
  401ae2:	48 8d 35 42 05 00 00 	lea    0x542(%rip),%rsi        # 40202b <_IO_stdin_used+0x2b>
  401ae9:	bf 01 00 00 00       	mov    $0x1,%edi
  401aee:	31 c0                	xor    %eax,%eax
  401af0:	e8 8b f5 ff ff       	call   401080 <__printf_chk@plt>
  401af5:	5b                   	pop    %rbx
  401af6:	5d                   	pop    %rbp
  401af7:	41 5c                	pop    %r12
  401af9:	41 5d                	pop    %r13
  401afb:	41 5e                	pop    %r14
  401afd:	c3                   	ret
  401afe:	66 90                	xchg   %ax,%ax
  401b00:	48 89 df             	mov    %rbx,%rdi
  401b03:	e8 e8 fd ff ff       	call   4018f0 <threadwork>
  401b08:	83 bb cc 00 00 00 01 	cmpl   $0x1,0xcc(%rbx)
  401b0f:	74 a7                	je     401ab8 <work+0x88>
  401b11:	eb c9                	jmp    401adc <work+0xac>

Disassembly of section .fini:

0000000000401b14 <_fini>:
  401b14:	f3 0f 1e fa          	endbr64
  401b18:	48 83 ec 08          	sub    $0x8,%rsp
  401b1c:	48 83 c4 08          	add    $0x8,%rsp
  401b20:	c3                   	ret
