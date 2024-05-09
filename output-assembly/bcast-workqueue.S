
bcast-workqueue:     file format elf64-x86-64


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
  401020:	ff 35 6a 2f 00 00    	push   0x2f6a(%rip)        # 403f90 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 6c 2f 00 00    	jmp    *0x2f6c(%rip)        # 403f98 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <pthread_setaffinity_np@plt>:
  401030:	ff 25 6a 2f 00 00    	jmp    *0x2f6a(%rip)        # 403fa0 <pthread_setaffinity_np@GLIBC_2.34>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <puts@plt>:
  401040:	ff 25 62 2f 00 00    	jmp    *0x2f62(%rip)        # 403fa8 <puts@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <clock_gettime@plt>:
  401050:	ff 25 5a 2f 00 00    	jmp    *0x2f5a(%rip)        # 403fb0 <clock_gettime@GLIBC_2.17>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <__stack_chk_fail@plt>:
  401060:	ff 25 52 2f 00 00    	jmp    *0x2f52(%rip)        # 403fb8 <__stack_chk_fail@GLIBC_2.4>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <nanosleep@plt>:
  401070:	ff 25 4a 2f 00 00    	jmp    *0x2f4a(%rip)        # 403fc0 <nanosleep@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <memset@plt>:
  401080:	ff 25 42 2f 00 00    	jmp    *0x2f42(%rip)        # 403fc8 <memset@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <calloc@plt>:
  401090:	ff 25 3a 2f 00 00    	jmp    *0x2f3a(%rip)        # 403fd0 <calloc@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <__printf_chk@plt>:
  4010a0:	ff 25 32 2f 00 00    	jmp    *0x2f32(%rip)        # 403fd8 <__printf_chk@GLIBC_2.3.4>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <pthread_create@plt>:
  4010b0:	ff 25 2a 2f 00 00    	jmp    *0x2f2a(%rip)        # 403fe0 <pthread_create@GLIBC_2.34>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <pthread_join@plt>:
  4010c0:	ff 25 22 2f 00 00    	jmp    *0x2f22(%rip)        # 403fe8 <pthread_join@GLIBC_2.34>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

00000000004010d0 <main>:
  4010d0:	41 57                	push   %r15
  4010d2:	ba 08 00 00 00       	mov    $0x8,%edx
  4010d7:	bf 01 00 00 00       	mov    $0x1,%edi
  4010dc:	48 8d 35 44 0f 00 00 	lea    0xf44(%rip),%rsi        # 402027 <_IO_stdin_used+0x27>
  4010e3:	41 56                	push   %r14
  4010e5:	41 be 01 00 00 00    	mov    $0x1,%r14d
  4010eb:	41 55                	push   %r13
  4010ed:	41 54                	push   %r12
  4010ef:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
  4010f5:	55                   	push   %rbp
  4010f6:	53                   	push   %rbx
  4010f7:	48 83 ec 68          	sub    $0x68,%rsp
  4010fb:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401104:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  401109:	31 c0                	xor    %eax,%eax
  40110b:	e8 90 ff ff ff       	call   4010a0 <__printf_chk@plt>
  401110:	ba 04 00 00 00       	mov    $0x4,%edx
  401115:	48 8d 35 1d 0f 00 00 	lea    0xf1d(%rip),%rsi        # 402039 <_IO_stdin_used+0x39>
  40111c:	31 c0                	xor    %eax,%eax
  40111e:	bf 01 00 00 00       	mov    $0x1,%edi
  401123:	e8 78 ff ff ff       	call   4010a0 <__printf_chk@plt>
  401128:	ba 20 00 00 00       	mov    $0x20,%edx
  40112d:	48 8d 35 01 0f 00 00 	lea    0xf01(%rip),%rsi        # 402035 <_IO_stdin_used+0x35>
  401134:	31 c0                	xor    %eax,%eax
  401136:	bf 01 00 00 00       	mov    $0x1,%edi
  40113b:	e8 60 ff ff ff       	call   4010a0 <__printf_chk@plt>
  401140:	ba 06 00 00 00       	mov    $0x6,%edx
  401145:	48 8d 35 fc 0e 00 00 	lea    0xefc(%rip),%rsi        # 402048 <_IO_stdin_used+0x48>
  40114c:	31 c0                	xor    %eax,%eax
  40114e:	bf 01 00 00 00       	mov    $0x1,%edi
  401153:	e8 48 ff ff ff       	call   4010a0 <__printf_chk@plt>
  401158:	be 08 00 00 00       	mov    $0x8,%esi
  40115d:	bf 06 00 00 00       	mov    $0x6,%edi
  401162:	e8 29 ff ff ff       	call   401090 <calloc@plt>
  401167:	be 38 00 00 00       	mov    $0x38,%esi
  40116c:	bf 06 00 00 00       	mov    $0x6,%edi
  401171:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  401176:	e8 15 ff ff ff       	call   401090 <calloc@plt>
  40117b:	be 00 15 00 00       	mov    $0x1500,%esi
  401180:	bf 01 00 00 00       	mov    $0x1,%edi
  401185:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  40118a:	e8 01 ff ff ff       	call   401090 <calloc@plt>
  40118f:	be 01 00 00 00       	mov    $0x1,%esi
  401194:	4c 89 e7             	mov    %r12,%rdi
  401197:	48 89 c3             	mov    %rax,%rbx
  40119a:	e8 f1 fe ff ff       	call   401090 <calloc@plt>
  40119f:	4c 89 e2             	mov    %r12,%rdx
  4011a2:	be ff ff ff ff       	mov    $0xffffffff,%esi
  4011a7:	49 89 df             	mov    %rbx,%r15
  4011aa:	48 89 c7             	mov    %rax,%rdi
  4011ad:	48 89 c5             	mov    %rax,%rbp
  4011b0:	e8 cb fe ff ff       	call   401080 <memset@plt>
  4011b5:	4c 89 e2             	mov    %r12,%rdx
  4011b8:	bf 01 00 00 00       	mov    $0x1,%edi
  4011bd:	31 c0                	xor    %eax,%eax
  4011bf:	48 8d 35 97 0e 00 00 	lea    0xe97(%rip),%rsi        # 40205d <_IO_stdin_used+0x5d>
  4011c6:	e8 d5 fe ff ff       	call   4010a0 <__printf_chk@plt>
  4011cb:	be 20 00 00 00       	mov    $0x20,%esi
  4011d0:	bf 64 00 00 00       	mov    $0x64,%edi
  4011d5:	e8 b6 fe ff ff       	call   401090 <calloc@plt>
  4011da:	31 d2                	xor    %edx,%edx
  4011dc:	bf 01 00 00 00       	mov    $0x1,%edi
  4011e1:	48 8d 35 86 0e 00 00 	lea    0xe86(%rip),%rsi        # 40206e <_IO_stdin_used+0x6e>
  4011e8:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  4011ed:	31 c0                	xor    %eax,%eax
  4011ef:	e8 ac fe ff ff       	call   4010a0 <__printf_chk@plt>
  4011f4:	4c 89 e2             	mov    %r12,%rdx
  4011f7:	bf 01 00 00 00       	mov    $0x1,%edi
  4011fc:	31 c0                	xor    %eax,%eax
  4011fe:	48 8d 35 75 0e 00 00 	lea    0xe75(%rip),%rsi        # 40207a <_IO_stdin_used+0x7a>
  401205:	e8 96 fe ff ff       	call   4010a0 <__printf_chk@plt>
  40120a:	be 04 00 00 00       	mov    $0x4,%esi
  40120f:	bf 06 00 00 00       	mov    $0x6,%edi
  401214:	e8 77 fe ff ff       	call   401090 <calloc@plt>
  401219:	48 89 6b 70          	mov    %rbp,0x70(%rbx)
  40121d:	31 ed                	xor    %ebp,%ebp
  40121f:	49 89 c5             	mov    %rax,%r13
  401222:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  401228:	be 80 00 00 00       	mov    $0x80,%esi
  40122d:	bf 01 00 00 00       	mov    $0x1,%edi
  401232:	44 89 34 24          	mov    %r14d,(%rsp)
  401236:	45 8d 66 ff          	lea    -0x1(%r14),%r12d
  40123a:	e8 51 fe ff ff       	call   401090 <calloc@plt>
  40123f:	44 89 f1             	mov    %r14d,%ecx
  401242:	ba 01 00 00 00       	mov    $0x1,%edx
  401247:	48 8d 35 3a 0f 00 00 	lea    0xf3a(%rip),%rsi        # 402188 <_IO_stdin_used+0x188>
  40124e:	49 89 47 78          	mov    %rax,0x78(%r15)
  401252:	48 d3 e2             	shl    %cl,%rdx
  401255:	8b 0c 24             	mov    (%rsp),%ecx
  401258:	bf 01 00 00 00       	mov    $0x1,%edi
  40125d:	48 09 10             	or     %rdx,(%rax)
  401260:	44 89 e2             	mov    %r12d,%edx
  401263:	31 c0                	xor    %eax,%eax
  401265:	49 81 c7 80 03 00 00 	add    $0x380,%r15
  40126c:	e8 2f fe ff ff       	call   4010a0 <__printf_chk@plt>
  401271:	48 8b 05 60 0f 00 00 	mov    0xf60(%rip),%rax        # 4021d8 <_IO_stdin_used+0x1d8>
  401278:	41 89 af 18 fd ff ff 	mov    %ebp,-0x2e8(%r15)
  40127f:	be 30 00 00 00       	mov    $0x30,%esi
  401284:	66 0f 6f 0d 54 0f 00 00 	movdqa 0xf54(%rip),%xmm1        # 4021e0 <_IO_stdin_used+0x1e0>
  40128c:	bf 80 96 98 00       	mov    $0x989680,%edi
  401291:	66 0f 6f 15 57 0f 00 00 	movdqa 0xf57(%rip),%xmm2        # 4021f0 <_IO_stdin_used+0x1f0>
  401299:	41 c7 87 00 fd ff ff 00 00 00 00 	movl   $0x0,-0x300(%r15)
  4012a4:	49 89 87 dc fc ff ff 	mov    %rax,-0x324(%r15)
  4012ab:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  4012b0:	81 c5 aa aa aa 2a    	add    $0x2aaaaaaa,%ebp
  4012b6:	66 0f 6f 1d 42 0f 00 00 	movdqa 0xf42(%rip),%xmm3        # 402200 <_IO_stdin_used+0x200>
  4012be:	45 89 a7 e4 fc ff ff 	mov    %r12d,-0x31c(%r15)
  4012c5:	41 c7 87 14 fd ff ff aa aa aa 2a 	movl   $0x2aaaaaaa,-0x2ec(%r15)
  4012d0:	41 c7 87 e8 fc ff ff 06 00 00 00 	movl   $0x6,-0x318(%r15)
  4012db:	4d 89 af a0 fc ff ff 	mov    %r13,-0x360(%r15)
  4012e2:	43 c7 44 b5 fc 00 00 00 00 	movl   $0x0,-0x4(%r13,%r14,4)
  4012eb:	49 83 c6 01          	add    $0x1,%r14
  4012ef:	41 c7 87 10 fd ff ff aa aa aa 2a 	movl   $0x2aaaaaaa,-0x2f0(%r15)
  4012fa:	49 89 9f a8 fc ff ff 	mov    %rbx,-0x358(%r15)
  401301:	49 89 9f b0 fc ff ff 	mov    %rbx,-0x350(%r15)
  401308:	41 c7 87 80 fe ff ff 05 00 00 00 	movl   $0x5,-0x180(%r15)
  401313:	41 c7 87 00 fe ff ff 05 00 00 00 	movl   $0x5,-0x200(%r15)
  40131e:	49 89 87 20 fd ff ff 	mov    %rax,-0x2e0(%r15)
  401325:	41 c7 87 48 fd ff ff 00 00 00 00 	movl   $0x0,-0x2b8(%r15)
  401330:	41 c7 47 a8 06 00 00 00 	movl   $0x6,-0x58(%r15)
  401338:	41 0f 29 8f 80 fc ff ff 	movaps %xmm1,-0x380(%r15)
  401340:	41 0f 11 97 38 fd ff ff 	movups %xmm2,-0x2c8(%r15)
  401348:	41 0f 11 5f 88       	movups %xmm3,-0x78(%r15)
  40134d:	e8 3e fd ff ff       	call   401090 <calloc@plt>
  401352:	be 30 00 00 00       	mov    $0x30,%esi
  401357:	bf 10 27 00 00       	mov    $0x2710,%edi
  40135c:	41 c7 47 a0 80 96 98 00 	movl   $0x989680,-0x60(%r15)
  401364:	49 89 47 98          	mov    %rax,-0x68(%r15)
  401368:	e8 23 fd ff ff       	call   401090 <calloc@plt>
  40136d:	49 89 47 b0          	mov    %rax,-0x50(%r15)
  401371:	49 83 fe 07          	cmp    $0x7,%r14
  401375:	0f 85 ad fe ff ff    	jne    401228 <main+0x158>
  40137b:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
  401380:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  401385:	48 89 1c 24          	mov    %rbx,(%rsp)
  401389:	49 89 de             	mov    %rbx,%r14
  40138c:	49 c7 c5 e0 1c 40 00 	mov    $0x401ce0,%r13
  401393:	48 8d 8d 50 01 00 00 	lea    0x150(%rbp),%rcx
  40139a:	49 89 c4             	mov    %rax,%r12
  40139d:	48 89 c3             	mov    %rax,%rbx
  4013a0:	49 89 cf             	mov    %rcx,%r15
  4013a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4013a8:	4c 89 f1             	mov    %r14,%rcx
  4013ab:	48 89 ee             	mov    %rbp,%rsi
  4013ae:	48 89 df             	mov    %rbx,%rdi
  4013b1:	4c 89 ea             	mov    %r13,%rdx
  4013b4:	e8 f7 fc ff ff       	call   4010b0 <pthread_create@plt>
  4013b9:	49 8b 56 78          	mov    0x78(%r14),%rdx
  4013bd:	48 8b 3b             	mov    (%rbx),%rdi
  4013c0:	be 08 00 00 00       	mov    $0x8,%esi
  4013c5:	48 83 c5 38          	add    $0x38,%rbp
  4013c9:	48 83 c3 08          	add    $0x8,%rbx
  4013cd:	49 81 c6 80 03 00 00 	add    $0x380,%r14
  4013d4:	e8 57 fc ff ff       	call   401030 <pthread_setaffinity_np@plt>
  4013d9:	49 39 ef             	cmp    %rbp,%r15
  4013dc:	75 ca                	jne    4013a8 <main+0x2d8>
  4013de:	48 8b 1c 24          	mov    (%rsp),%rbx
  4013e2:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  4013e7:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
  4013ec:	66 0f 6f 05 1c 0e 00 00 	movdqa 0xe1c(%rip),%xmm0        # 402210 <_IO_stdin_used+0x210>
  4013f4:	4c 8d 6c 24 28       	lea    0x28(%rsp),%r13
  4013f9:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  4013fe:	66 0f ef c0          	pxor   %xmm0,%xmm0
  401402:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  401407:	e8 64 fc ff ff       	call   401070 <nanosleep@plt>
  40140c:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
  401411:	c7 43 5c 00 00 00 00 	movl   $0x0,0x5c(%rbx)
  401418:	c7 83 dc 03 00 00 00 00 00 00 	movl   $0x0,0x3dc(%rbx)
  401422:	c7 83 5c 07 00 00 00 00 00 00 	movl   $0x0,0x75c(%rbx)
  40142c:	48 83 c5 30          	add    $0x30,%rbp
  401430:	c7 83 dc 0a 00 00 00 00 00 00 	movl   $0x0,0xadc(%rbx)
  40143a:	c7 83 5c 0e 00 00 00 00 00 00 	movl   $0x0,0xe5c(%rbx)
  401444:	c7 83 dc 11 00 00 00 00 00 00 	movl   $0x0,0x11dc(%rbx)
  40144e:	66 90                	xchg   %ax,%ax
  401450:	49 8b 3c 24          	mov    (%r12),%rdi
  401454:	4c 89 ee             	mov    %r13,%rsi
  401457:	49 83 c4 08          	add    $0x8,%r12
  40145b:	e8 60 fc ff ff       	call   4010c0 <pthread_join@plt>
  401460:	49 39 ec             	cmp    %rbp,%r12
  401463:	75 eb                	jne    401450 <main+0x380>
  401465:	48 8d 3d 1a 0c 00 00 	lea    0xc1a(%rip),%rdi        # 402086 <_IO_stdin_used+0x86>
  40146c:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  401470:	45 31 e4             	xor    %r12d,%r12d
  401473:	e8 c8 fb ff ff       	call   401040 <puts@plt>
  401478:	4c 8d b3 48 15 00 00 	lea    0x1548(%rbx),%r14
  40147f:	4c 8d 2d 15 0c 00 00 	lea    0xc15(%rip),%r13        # 40209b <_IO_stdin_used+0x9b>
  401486:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401490:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401494:	4c 89 ee             	mov    %r13,%rsi
  401497:	bf 01 00 00 00       	mov    $0x1,%edi
  40149c:	31 c0                	xor    %eax,%eax
  40149e:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
  4014a5:	e8 f6 fb ff ff       	call   4010a0 <__printf_chk@plt>
  4014aa:	4c 03 a5 80 fc ff ff 	add    -0x380(%rbp),%r12
  4014b1:	4c 39 f5             	cmp    %r14,%rbp
  4014b4:	75 da                	jne    401490 <main+0x3c0>
  4014b6:	4c 89 e2             	mov    %r12,%rdx
  4014b9:	48 8d 35 e6 0b 00 00 	lea    0xbe6(%rip),%rsi        # 4020a6 <_IO_stdin_used+0xa6>
  4014c0:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  4014c4:	31 c0                	xor    %eax,%eax
  4014c6:	bf 01 00 00 00       	mov    $0x1,%edi
  4014cb:	4c 8d b3 50 15 00 00 	lea    0x1550(%rbx),%r14
  4014d2:	4c 8d 2d 2b 0c 00 00 	lea    0xc2b(%rip),%r13        # 402104 <_IO_stdin_used+0x104>
  4014d9:	e8 c2 fb ff ff       	call   4010a0 <__printf_chk@plt>
  4014de:	4c 89 e2             	mov    %r12,%rdx
  4014e1:	bf 01 00 00 00       	mov    $0x1,%edi
  4014e6:	31 c0                	xor    %eax,%eax
  4014e8:	48 8d 35 c2 0b 00 00 	lea    0xbc2(%rip),%rsi        # 4020b1 <_IO_stdin_used+0xb1>
  4014ef:	e8 ac fb ff ff       	call   4010a0 <__printf_chk@plt>
  4014f4:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  4014f9:	bf 01 00 00 00       	mov    $0x1,%edi
  4014fe:	48 8d 35 ba 0b 00 00 	lea    0xbba(%rip),%rsi        # 4020bf <_IO_stdin_used+0xbf>
  401505:	48 99                	cqto
  401507:	49 f7 fc             	idiv   %r12
  40150a:	49 89 c4             	mov    %rax,%r12
  40150d:	48 89 c2             	mov    %rax,%rdx
  401510:	31 c0                	xor    %eax,%eax
  401512:	e8 89 fb ff ff       	call   4010a0 <__printf_chk@plt>
  401517:	4c 89 e2             	mov    %r12,%rdx
  40151a:	bf 01 00 00 00       	mov    $0x1,%edi
  40151f:	31 c0                	xor    %eax,%eax
  401521:	48 8d 35 ab 0b 00 00 	lea    0xbab(%rip),%rsi        # 4020d3 <_IO_stdin_used+0xd3>
  401528:	e8 73 fb ff ff       	call   4010a0 <__printf_chk@plt>
  40152d:	4c 89 e2             	mov    %r12,%rdx
  401530:	bf 01 00 00 00       	mov    $0x1,%edi
  401535:	31 c0                	xor    %eax,%eax
  401537:	48 8d 35 b3 0b 00 00 	lea    0xbb3(%rip),%rsi        # 4020f1 <_IO_stdin_used+0xf1>
  40153e:	45 31 e4             	xor    %r12d,%r12d
  401541:	e8 5a fb ff ff       	call   4010a0 <__printf_chk@plt>
  401546:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401550:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401554:	4c 89 ee             	mov    %r13,%rsi
  401557:	bf 01 00 00 00       	mov    $0x1,%edi
  40155c:	31 c0                	xor    %eax,%eax
  40155e:	48 81 c5 80 03 00 00 	add    $0x380,%rbp
  401565:	49 01 d4             	add    %rdx,%r12
  401568:	e8 33 fb ff ff       	call   4010a0 <__printf_chk@plt>
  40156d:	49 39 ee             	cmp    %rbp,%r14
  401570:	75 de                	jne    401550 <main+0x480>
  401572:	4c 89 e2             	mov    %r12,%rdx
  401575:	48 8d 35 94 0b 00 00 	lea    0xb94(%rip),%rsi        # 402110 <_IO_stdin_used+0x110>
  40157c:	bf 01 00 00 00       	mov    $0x1,%edi
  401581:	31 c0                	xor    %eax,%eax
  401583:	e8 18 fb ff ff       	call   4010a0 <__printf_chk@plt>
  401588:	4c 89 e2             	mov    %r12,%rdx
  40158b:	bf 01 00 00 00       	mov    $0x1,%edi
  401590:	31 c0                	xor    %eax,%eax
  401592:	48 8d 35 89 0b 00 00 	lea    0xb89(%rip),%rsi        # 402122 <_IO_stdin_used+0x122>
  401599:	48 8d 2d 2e 0b 00 00 	lea    0xb2e(%rip),%rbp        # 4020ce <_IO_stdin_used+0xce>
  4015a0:	e8 fb fa ff ff       	call   4010a0 <__printf_chk@plt>
  4015a5:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  4015aa:	bf 01 00 00 00       	mov    $0x1,%edi
  4015af:	48 8d 35 84 0b 00 00 	lea    0xb84(%rip),%rsi        # 40213a <_IO_stdin_used+0x13a>
  4015b6:	48 99                	cqto
  4015b8:	49 f7 fc             	idiv   %r12
  4015bb:	49 89 c4             	mov    %rax,%r12
  4015be:	48 89 c2             	mov    %rax,%rdx
  4015c1:	31 c0                	xor    %eax,%eax
  4015c3:	e8 d8 fa ff ff       	call   4010a0 <__printf_chk@plt>
  4015c8:	4c 89 e2             	mov    %r12,%rdx
  4015cb:	bf 01 00 00 00       	mov    $0x1,%edi
  4015d0:	31 c0                	xor    %eax,%eax
  4015d2:	48 8d 35 cf 0b 00 00 	lea    0xbcf(%rip),%rsi        # 4021a8 <_IO_stdin_used+0x1a8>
  4015d9:	e8 c2 fa ff ff       	call   4010a0 <__printf_chk@plt>
  4015de:	4c 89 e2             	mov    %r12,%rdx
  4015e1:	bf 01 00 00 00       	mov    $0x1,%edi
  4015e6:	31 c0                	xor    %eax,%eax
  4015e8:	48 8d 35 66 0b 00 00 	lea    0xb66(%rip),%rsi        # 402155 <_IO_stdin_used+0x155>
  4015ef:	e8 ac fa ff ff       	call   4010a0 <__printf_chk@plt>
  4015f4:	48 8d 3d 74 0b 00 00 	lea    0xb74(%rip),%rdi        # 40216f <_IO_stdin_used+0x16f>
  4015fb:	e8 40 fa ff ff       	call   401040 <puts@plt>
  401600:	48 89 ee             	mov    %rbp,%rsi
  401603:	bf 01 00 00 00       	mov    $0x1,%edi
  401608:	31 c0                	xor    %eax,%eax
  40160a:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  401611:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  401618:	e8 83 fa ff ff       	call   4010a0 <__printf_chk@plt>
  40161d:	48 89 ee             	mov    %rbp,%rsi
  401620:	bf 01 00 00 00       	mov    $0x1,%edi
  401625:	31 c0                	xor    %eax,%eax
  401627:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  40162e:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  401635:	e8 66 fa ff ff       	call   4010a0 <__printf_chk@plt>
  40163a:	48 89 ee             	mov    %rbp,%rsi
  40163d:	bf 01 00 00 00       	mov    $0x1,%edi
  401642:	31 c0                	xor    %eax,%eax
  401644:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  40164b:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401652:	e8 49 fa ff ff       	call   4010a0 <__printf_chk@plt>
  401657:	48 89 ee             	mov    %rbp,%rsi
  40165a:	bf 01 00 00 00       	mov    $0x1,%edi
  40165f:	31 c0                	xor    %eax,%eax
  401661:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  401668:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  40166f:	e8 2c fa ff ff       	call   4010a0 <__printf_chk@plt>
  401674:	48 89 ee             	mov    %rbp,%rsi
  401677:	bf 01 00 00 00       	mov    $0x1,%edi
  40167c:	31 c0                	xor    %eax,%eax
  40167e:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401685:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  40168c:	e8 0f fa ff ff       	call   4010a0 <__printf_chk@plt>
  401691:	48 89 ee             	mov    %rbp,%rsi
  401694:	bf 01 00 00 00       	mov    $0x1,%edi
  401699:	31 c0                	xor    %eax,%eax
  40169b:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  4016a2:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  4016a9:	e8 f2 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  4016ae:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  4016b5:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ba:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  4016c1:	48 8d 35 b4 0a 00 00 	lea    0xab4(%rip),%rsi        # 40217c <_IO_stdin_used+0x17c>
  4016c8:	31 c0                	xor    %eax,%eax
  4016ca:	e8 d1 f9 ff ff       	call   4010a0 <__printf_chk@plt>
  4016cf:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  4016d4:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4016dd:	75 11                	jne    4016f0 <main+0x620>
  4016df:	48 83 c4 68          	add    $0x68,%rsp
  4016e3:	31 c0                	xor    %eax,%eax
  4016e5:	5b                   	pop    %rbx
  4016e6:	5d                   	pop    %rbp
  4016e7:	41 5c                	pop    %r12
  4016e9:	41 5d                	pop    %r13
  4016eb:	41 5e                	pop    %r14
  4016ed:	41 5f                	pop    %r15
  4016ef:	c3                   	ret
  4016f0:	e8 6b f9 ff ff       	call   401060 <__stack_chk_fail@plt>
  4016f5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4016ff:	90                   	nop

0000000000401700 <set_fast_math>:
  401700:	f3 0f 1e fa          	endbr64
  401704:	0f ae 5c 24 fc       	stmxcsr -0x4(%rsp)
  401709:	81 4c 24 fc 40 80 00 00 	orl    $0x8040,-0x4(%rsp)
  401711:	0f ae 54 24 fc       	ldmxcsr -0x4(%rsp)
  401716:	c3                   	ret
  401717:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000401720 <_start>:
  401720:	f3 0f 1e fa          	endbr64
  401724:	31 ed                	xor    %ebp,%ebp
  401726:	49 89 d1             	mov    %rdx,%r9
  401729:	5e                   	pop    %rsi
  40172a:	48 89 e2             	mov    %rsp,%rdx
  40172d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401731:	50                   	push   %rax
  401732:	54                   	push   %rsp
  401733:	45 31 c0             	xor    %r8d,%r8d
  401736:	31 c9                	xor    %ecx,%ecx
  401738:	48 c7 c7 d0 10 40 00 	mov    $0x4010d0,%rdi
  40173f:	ff 15 ab 28 00 00    	call   *0x28ab(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  401745:	f4                   	hlt
  401746:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401750 <_dl_relocate_static_pie>:
  401750:	f3 0f 1e fa          	endbr64
  401754:	c3                   	ret
  401755:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40175f:	90                   	nop

0000000000401760 <deregister_tm_clones>:
  401760:	b8 10 40 40 00       	mov    $0x404010,%eax
  401765:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  40176b:	74 13                	je     401780 <deregister_tm_clones+0x20>
  40176d:	b8 00 00 00 00       	mov    $0x0,%eax
  401772:	48 85 c0             	test   %rax,%rax
  401775:	74 09                	je     401780 <deregister_tm_clones+0x20>
  401777:	bf 10 40 40 00       	mov    $0x404010,%edi
  40177c:	ff e0                	jmp    *%rax
  40177e:	66 90                	xchg   %ax,%ax
  401780:	c3                   	ret
  401781:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40178c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401790 <register_tm_clones>:
  401790:	be 10 40 40 00       	mov    $0x404010,%esi
  401795:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  40179c:	48 89 f0             	mov    %rsi,%rax
  40179f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  4017a3:	48 c1 f8 03          	sar    $0x3,%rax
  4017a7:	48 01 c6             	add    %rax,%rsi
  4017aa:	48 d1 fe             	sar    %rsi
  4017ad:	74 11                	je     4017c0 <register_tm_clones+0x30>
  4017af:	b8 00 00 00 00       	mov    $0x0,%eax
  4017b4:	48 85 c0             	test   %rax,%rax
  4017b7:	74 07                	je     4017c0 <register_tm_clones+0x30>
  4017b9:	bf 10 40 40 00       	mov    $0x404010,%edi
  4017be:	ff e0                	jmp    *%rax
  4017c0:	c3                   	ret
  4017c1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4017cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004017d0 <__do_global_dtors_aux>:
  4017d0:	f3 0f 1e fa          	endbr64
  4017d4:	80 3d 35 28 00 00 00 	cmpb   $0x0,0x2835(%rip)        # 404010 <__TMC_END__>
  4017db:	75 13                	jne    4017f0 <__do_global_dtors_aux+0x20>
  4017dd:	55                   	push   %rbp
  4017de:	48 89 e5             	mov    %rsp,%rbp
  4017e1:	e8 7a ff ff ff       	call   401760 <deregister_tm_clones>
  4017e6:	c6 05 23 28 00 00 01 	movb   $0x1,0x2823(%rip)        # 404010 <__TMC_END__>
  4017ed:	5d                   	pop    %rbp
  4017ee:	c3                   	ret
  4017ef:	90                   	nop
  4017f0:	c3                   	ret
  4017f1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4017fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401800 <frame_dummy>:
  401800:	f3 0f 1e fa          	endbr64
  401804:	eb 8a                	jmp    401790 <register_tm_clones>
  401806:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401810 <pollthreads>:
  401810:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
  401814:	49 89 f9             	mov    %rdi,%r9
  401817:	7e 77                	jle    401890 <pollthreads+0x80>
  401819:	49 8b 41 30          	mov    0x30(%r9),%rax
  40181d:	55                   	push   %rbp
  40181e:	49 89 f2             	mov    %rsi,%r10
  401821:	49 89 d3             	mov    %rdx,%r11
  401824:	53                   	push   %rbx
  401825:	48 89 cf             	mov    %rcx,%rdi
  401828:	48 8b 98 a0 03 00 00 	mov    0x3a0(%rax),%rbx
  40182f:	b8 01 00 00 00       	mov    $0x1,%eax
  401834:	0f 1f 40 00          	nopl   0x0(%rax)
  401838:	48 63 d0             	movslq %eax,%rdx
  40183b:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
  40183e:	85 d2                	test   %edx,%edx
  401840:	40 0f 94 c6          	sete   %sil
  401844:	f6 c2 04             	test   $0x4,%dl
  401847:	75 05                	jne    40184e <pollthreads+0x3e>
  401849:	40 84 f6             	test   %sil,%sil
  40184c:	74 0d                	je     40185b <pollthreads+0x4b>
  40184e:	49 63 08             	movslq (%r8),%rcx
  401851:	8d 69 01             	lea    0x1(%rcx),%ebp
  401854:	41 89 28             	mov    %ebp,(%r8)
  401857:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
  40185b:	83 e2 08             	and    $0x8,%edx
  40185e:	75 05                	jne    401865 <pollthreads+0x55>
  401860:	40 84 f6             	test   %sil,%sil
  401863:	74 1b                	je     401880 <pollthreads+0x70>
  401865:	48 63 17             	movslq (%rdi),%rdx
  401868:	8d 4a 01             	lea    0x1(%rdx),%ecx
  40186b:	89 0f                	mov    %ecx,(%rdi)
  40186d:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  401871:	83 c0 01             	add    $0x1,%eax
  401874:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401878:	7f be                	jg     401838 <pollthreads+0x28>
  40187a:	31 c0                	xor    %eax,%eax
  40187c:	5b                   	pop    %rbx
  40187d:	5d                   	pop    %rbp
  40187e:	c3                   	ret
  40187f:	90                   	nop
  401880:	83 c0 01             	add    $0x1,%eax
  401883:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401887:	7f af                	jg     401838 <pollthreads+0x28>
  401889:	31 c0                	xor    %eax,%eax
  40188b:	5b                   	pop    %rbx
  40188c:	5d                   	pop    %rbp
  40188d:	c3                   	ret
  40188e:	66 90                	xchg   %ax,%ax
  401890:	31 c0                	xor    %eax,%eax
  401892:	c3                   	ret
  401893:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40189e:	66 90                	xchg   %ax,%ax

00000000004018a0 <findavailable>:
  4018a0:	49 89 fb             	mov    %rdi,%r11
  4018a3:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
  4018aa:	44 8b 02             	mov    (%rdx),%r8d
  4018ad:	48 83 c7 01          	add    $0x1,%rdi
  4018b1:	48 85 ff             	test   %rdi,%rdi
  4018b4:	7e 66                	jle    40191c <findavailable+0x7c>
  4018b6:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  4018bd:	31 c9                	xor    %ecx,%ecx
  4018bf:	45 31 c9             	xor    %r9d,%r9d
  4018c2:	31 c0                	xor    %eax,%eax
  4018c4:	eb 18                	jmp    4018de <findavailable+0x3e>
  4018c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4018d0:	83 c1 01             	add    $0x1,%ecx
  4018d3:	48 63 c1             	movslq %ecx,%rax
  4018d6:	49 89 c1             	mov    %rax,%r9
  4018d9:	48 39 f8             	cmp    %rdi,%rax
  4018dc:	7d 3e                	jge    40191c <findavailable+0x7c>
  4018de:	48 c1 e0 05          	shl    $0x5,%rax
  4018e2:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  4018e8:	75 e6                	jne    4018d0 <findavailable+0x30>
  4018ea:	49 63 c0             	movslq %r8d,%rax
  4018ed:	41 83 c0 01          	add    $0x1,%r8d
  4018f1:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
  4018f5:	44 89 02             	mov    %r8d,(%rdx)
  4018f8:	41 8b 43 68          	mov    0x68(%r11),%eax
  4018fc:	01 c0                	add    %eax,%eax
  4018fe:	41 39 c0             	cmp    %eax,%r8d
  401901:	74 19                	je     40191c <findavailable+0x7c>
  401903:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  40190a:	83 c1 01             	add    $0x1,%ecx
  40190d:	48 63 c1             	movslq %ecx,%rax
  401910:	48 83 c7 01          	add    $0x1,%rdi
  401914:	49 89 c1             	mov    %rax,%r9
  401917:	48 39 f8             	cmp    %rdi,%rax
  40191a:	7c c2                	jl     4018de <findavailable+0x3e>
  40191c:	31 c0                	xor    %eax,%eax
  40191e:	45 85 c0             	test   %r8d,%r8d
  401921:	0f 94 c0             	sete   %al
  401924:	c3                   	ret
  401925:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401930 <singlewriter3>:
  401930:	c3                   	ret
  401931:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40193c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401940 <singlewriter2>:
  401940:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  401946:	85 c0                	test   %eax,%eax
  401948:	74 1e                	je     401968 <singlewriter2+0x28>
  40194a:	41 54                	push   %r12
  40194c:	99                   	cltd
  40194d:	55                   	push   %rbp
  40194e:	53                   	push   %rbx
  40194f:	8b 77 68             	mov    0x68(%rdi),%esi
  401952:	48 89 fb             	mov    %rdi,%rbx
  401955:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401958:	f7 f9                	idiv   %ecx
  40195a:	85 d2                	test   %edx,%edx
  40195c:	74 12                	je     401970 <singlewriter2+0x30>
  40195e:	5b                   	pop    %rbx
  40195f:	5d                   	pop    %rbp
  401960:	41 5c                	pop    %r12
  401962:	c3                   	ret
  401963:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401968:	c3                   	ret
  401969:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401970:	48 63 47 64          	movslq 0x64(%rdi),%rax
  401974:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
  40197c:	48 29 c5             	sub    %rax,%rbp
  40197f:	48 c1 e5 07          	shl    $0x7,%rbp
  401983:	48 03 6f 30          	add    0x30(%rdi),%rbp
  401987:	bf 04 00 00 00       	mov    $0x4,%edi
  40198c:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401993:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401997:	49 c1 e4 04          	shl    $0x4,%r12
  40199b:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
  4019a2:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  4019a7:	e8 a4 f6 ff ff       	call   401050 <clock_gettime@plt>
  4019ac:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  4019b2:	83 c0 01             	add    $0x1,%eax
  4019b5:	99                   	cltd
  4019b6:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
  4019bc:	8b 43 64             	mov    0x64(%rbx),%eax
  4019bf:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
  4019c5:	41 89 04 24          	mov    %eax,(%r12)
  4019c9:	48 8b 05 00 08 00 00 	mov    0x800(%rip),%rax        # 4021d0 <_IO_stdin_used+0x1d0>
  4019d0:	49 89 44 24 20       	mov    %rax,0x20(%r12)
  4019d5:	5b                   	pop    %rbx
  4019d6:	5d                   	pop    %rbp
  4019d7:	41 5c                	pop    %r12
  4019d9:	c3                   	ret
  4019da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000004019e0 <singlewriter>:
  4019e0:	41 55                	push   %r13
  4019e2:	49 89 d5             	mov    %rdx,%r13
  4019e5:	41 54                	push   %r12
  4019e7:	49 89 cc             	mov    %rcx,%r12
  4019ea:	55                   	push   %rbp
  4019eb:	4d 89 e0             	mov    %r12,%r8
  4019ee:	48 89 fd             	mov    %rdi,%rbp
  4019f1:	53                   	push   %rbx
  4019f2:	48 89 f3             	mov    %rsi,%rbx
  4019f5:	48 83 ec 28          	sub    $0x28,%rsp
  4019f9:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
  4019fd:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401a06:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401a0b:	31 c0                	xor    %eax,%eax
  401a0d:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  401a15:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  401a1b:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  401a23:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  401a2b:	83 c0 01             	add    $0x1,%eax
  401a2e:	99                   	cltd
  401a2f:	f7 7f 68             	idivl  0x68(%rdi)
  401a32:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  401a38:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401a3d:	4c 89 e9             	mov    %r13,%rcx
  401a40:	e8 5b fe ff ff       	call   4018a0 <findavailable>
  401a45:	83 f8 01             	cmp    $0x1,%eax
  401a48:	0f 84 64 01 00 00    	je     401bb2 <singlewriter+0x1d2>
  401a4e:	48 89 ef             	mov    %rbp,%rdi
  401a51:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401a56:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401a5b:	4c 89 e2             	mov    %r12,%rdx
  401a5e:	4c 89 ee             	mov    %r13,%rsi
  401a61:	e8 aa fd ff ff       	call   401810 <pollthreads>
  401a66:	48 63 7c 24 0c       	movslq 0xc(%rsp),%rdi
  401a6b:	85 ff                	test   %edi,%edi
  401a6d:	0f 8e 66 01 00 00    	jle    401bd9 <singlewriter+0x1f9>
  401a73:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
  401a78:	31 c9                	xor    %ecx,%ecx
  401a7a:	eb 62                	jmp    401ade <singlewriter+0xfe>
  401a7c:	0f 1f 40 00          	nopl   0x0(%rax)
  401a80:	48 8b 14 cb          	mov    (%rbx,%rcx,8),%rdx
  401a84:	4d 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%r10
  401a89:	8d 71 01             	lea    0x1(%rcx),%esi
  401a8c:	48 83 c1 01          	add    $0x1,%rcx
  401a90:	48 c1 e2 05          	shl    $0x5,%rdx
  401a94:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
  401a9b:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
  401aa3:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401aa7:	66 0f 6e 4a 08       	movd   0x8(%rdx),%xmm1
  401aac:	4c 29 d0             	sub    %r10,%rax
  401aaf:	c7 42 10 02 00 00 00 	movl   $0x2,0x10(%rdx)
  401ab6:	48 c1 e0 07          	shl    $0x7,%rax
  401aba:	48 03 45 30          	add    0x30(%rbp),%rax
  401abe:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
  401ac2:	48 89 90 a8 00 00 00 	mov    %rdx,0xa8(%rax)
  401ac9:	44 89 52 14          	mov    %r10d,0x14(%rdx)
  401acd:	83 88 c8 00 00 00 10 	orl    $0x10,0xc8(%rax)
  401ad4:	66 0f d6 40 14       	movq   %xmm0,0x14(%rax)
  401ad9:	48 39 cf             	cmp    %rcx,%rdi
  401adc:	74 07                	je     401ae5 <singlewriter+0x105>
  401ade:	89 ce                	mov    %ecx,%esi
  401ae0:	4c 39 c1             	cmp    %r8,%rcx
  401ae3:	75 9b                	jne    401a80 <singlewriter+0xa0>
  401ae5:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
  401aea:	45 85 c0             	test   %r8d,%r8d
  401aed:	7e 7a                	jle    401b69 <singlewriter+0x189>
  401aef:	8b 7c 24 14          	mov    0x14(%rsp),%edi
  401af3:	41 01 f0             	add    %esi,%r8d
  401af6:	eb 6d                	jmp    401b65 <singlewriter+0x185>
  401af8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  401b00:	8d 4e 01             	lea    0x1(%rsi),%ecx
  401b03:	48 63 f6             	movslq %esi,%rsi
  401b06:	45 8b 0c 24          	mov    (%r12),%r9d
  401b0a:	49 83 c4 04          	add    $0x4,%r12
  401b0e:	48 8b 14 f3          	mov    (%rbx,%rsi,8),%rdx
  401b12:	49 63 f1             	movslq %r9d,%rsi
  401b15:	48 c1 e2 05          	shl    $0x5,%rdx
  401b19:	48 03 95 a0 00 00 00 	add    0xa0(%rbp),%rdx
  401b20:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
  401b28:	66 0f 6e 02          	movd   (%rdx),%xmm0
  401b2c:	66 0f 6e 52 08       	movd   0x8(%rdx),%xmm2
  401b31:	48 29 f0             	sub    %rsi,%rax
  401b34:	c7 42 10 03 00 00 00 	movl   $0x3,0x10(%rdx)
  401b3b:	48 c1 e0 07          	shl    $0x7,%rax
  401b3f:	48 03 45 30          	add    0x30(%rbp),%rax
  401b43:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
  401b47:	48 89 90 b0 00 00 00 	mov    %rdx,0xb0(%rax)
  401b4e:	44 89 4a 14          	mov    %r9d,0x14(%rdx)
  401b52:	83 88 c8 00 00 00 20 	orl    $0x20,0xc8(%rax)
  401b59:	66 0f d6 40 40       	movq   %xmm0,0x40(%rax)
  401b5e:	44 39 c1             	cmp    %r8d,%ecx
  401b61:	74 06                	je     401b69 <singlewriter+0x189>
  401b63:	89 ce                	mov    %ecx,%esi
  401b65:	39 f7                	cmp    %esi,%edi
  401b67:	75 97                	jne    401b00 <singlewriter+0x120>
  401b69:	8b 7d 68             	mov    0x68(%rbp),%edi
  401b6c:	85 ff                	test   %edi,%edi
  401b6e:	7e 40                	jle    401bb0 <singlewriter+0x1d0>
  401b70:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401b74:	31 d2                	xor    %edx,%edx
  401b76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401b80:	48 63 ca             	movslq %edx,%rcx
  401b83:	48 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rax
  401b8b:	48 29 c8             	sub    %rcx,%rax
  401b8e:	48 c1 e0 07          	shl    $0x7,%rax
  401b92:	4c 01 c0             	add    %r8,%rax
  401b95:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401b9b:	85 f6                	test   %esi,%esi
  401b9d:	74 31                	je     401bd0 <singlewriter+0x1f0>
  401b9f:	48 8b 40 20          	mov    0x20(%rax),%rax
  401ba3:	83 c2 01             	add    $0x1,%edx
  401ba6:	89 34 88             	mov    %esi,(%rax,%rcx,4)
  401ba9:	8b 7d 68             	mov    0x68(%rbp),%edi
  401bac:	39 fa                	cmp    %edi,%edx
  401bae:	7c d0                	jl     401b80 <singlewriter+0x1a0>
  401bb0:	31 c0                	xor    %eax,%eax
  401bb2:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401bb7:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401bc0:	75 1e                	jne    401be0 <singlewriter+0x200>
  401bc2:	48 83 c4 28          	add    $0x28,%rsp
  401bc6:	5b                   	pop    %rbx
  401bc7:	5d                   	pop    %rbp
  401bc8:	41 5c                	pop    %r12
  401bca:	41 5d                	pop    %r13
  401bcc:	c3                   	ret
  401bcd:	0f 1f 00             	nopl   (%rax)
  401bd0:	83 c2 01             	add    $0x1,%edx
  401bd3:	39 fa                	cmp    %edi,%edx
  401bd5:	7c a9                	jl     401b80 <singlewriter+0x1a0>
  401bd7:	eb d7                	jmp    401bb0 <singlewriter+0x1d0>
  401bd9:	31 f6                	xor    %esi,%esi
  401bdb:	e9 05 ff ff ff       	jmp    401ae5 <singlewriter+0x105>
  401be0:	e8 7b f4 ff ff       	call   401060 <__stack_chk_fail@plt>
  401be5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401bf0 <threadwork>:
  401bf0:	4c 8b 4f 28          	mov    0x28(%rdi),%r9
  401bf4:	48 89 f9             	mov    %rdi,%rcx
  401bf7:	48 63 71 68          	movslq 0x68(%rcx),%rsi
  401bfb:	44 8b 41 64          	mov    0x64(%rcx),%r8d
  401bff:	49 8b b9 50 03 00 00 	mov    0x350(%r9),%rdi
  401c06:	48 83 41 50 01       	addq   $0x1,0x50(%rcx)
  401c0b:	48 89 f8             	mov    %rdi,%rax
  401c0e:	48 99                	cqto
  401c10:	48 f7 fe             	idiv   %rsi
  401c13:	48 ba 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%rdx
  401c1d:	48 89 c6             	mov    %rax,%rsi
  401c20:	48 f7 ea             	imul   %rdx
  401c23:	48 89 f0             	mov    %rsi,%rax
  401c26:	48 c1 f8 3f          	sar    $0x3f,%rax
  401c2a:	48 01 f2             	add    %rsi,%rdx
  401c2d:	48 c1 fa 07          	sar    $0x7,%rdx
  401c31:	48 29 c2             	sub    %rax,%rdx
  401c34:	48 89 d0             	mov    %rdx,%rax
  401c37:	48 c1 e0 08          	shl    $0x8,%rax
  401c3b:	48 29 d0             	sub    %rdx,%rax
  401c3e:	48 29 c6             	sub    %rax,%rsi
  401c41:	49 63 c0             	movslq %r8d,%rax
  401c44:	48 c1 e6 10          	shl    $0x10,%rsi
  401c48:	48 09 c6             	or     %rax,%rsi
  401c4b:	49 8b 41 70          	mov    0x70(%r9),%rax
  401c4f:	44 88 04 30          	mov    %r8b,(%rax,%rsi,1)
  401c53:	48 8b 41 28          	mov    0x28(%rcx),%rax
  401c57:	f0 48 83 80 50 03 00 00 01 	lock addq $0x1,0x350(%rax)
  401c60:	48 8b 41 28          	mov    0x28(%rcx),%rax
  401c64:	4c 63 41 68          	movslq 0x68(%rcx),%r8
  401c68:	48 8b b1 48 03 00 00 	mov    0x348(%rcx),%rsi
  401c6f:	48 8b 80 50 03 00 00 	mov    0x350(%rax),%rax
  401c76:	48 99                	cqto
  401c78:	49 f7 f8             	idiv   %r8
  401c7b:	89 81 58 03 00 00    	mov    %eax,0x358(%rcx)
  401c81:	48 39 fe             	cmp    %rdi,%rsi
  401c84:	7d 3c                	jge    401cc2 <threadwork+0xd2>
  401c86:	8b 81 00 02 00 00    	mov    0x200(%rcx),%eax
  401c8c:	48 83 41 48 01       	addq   $0x1,0x48(%rcx)
  401c91:	83 c0 01             	add    $0x1,%eax
  401c94:	99                   	cltd
  401c95:	41 f7 f8             	idiv   %r8d
  401c98:	89 91 00 02 00 00    	mov    %edx,0x200(%rcx)
  401c9e:	3b 51 64             	cmp    0x64(%rcx),%edx
  401ca1:	74 25                	je     401cc8 <threadwork+0xd8>
  401ca3:	48 8d 46 01          	lea    0x1(%rsi),%rax
  401ca7:	48 99                	cqto
  401ca9:	48 89 81 48 03 00 00 	mov    %rax,0x348(%rcx)
  401cb0:	49 f7 f8             	idiv   %r8
  401cb3:	48 85 d2             	test   %rdx,%rdx
  401cb6:	75 0a                	jne    401cc2 <threadwork+0xd2>
  401cb8:	c7 81 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rcx)
  401cc2:	c3                   	ret
  401cc3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401cc8:	83 c2 01             	add    $0x1,%edx
  401ccb:	89 91 00 02 00 00    	mov    %edx,0x200(%rcx)
  401cd1:	eb d0                	jmp    401ca3 <threadwork+0xb3>
  401cd3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401cde:	66 90                	xchg   %ax,%ax

0000000000401ce0 <work>:
  401ce0:	53                   	push   %rbx
  401ce1:	8b 57 64             	mov    0x64(%rdi),%edx
  401ce4:	48 89 fb             	mov    %rdi,%rbx
  401ce7:	31 c0                	xor    %eax,%eax
  401ce9:	48 8d 35 14 03 00 00 	lea    0x314(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  401cf0:	bf 01 00 00 00       	mov    $0x1,%edi
  401cf5:	e8 a6 f3 ff ff       	call   4010a0 <__printf_chk@plt>
  401cfa:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401cfe:	75 0e                	jne    401d0e <work+0x2e>
  401d00:	48 89 df             	mov    %rbx,%rdi
  401d03:	e8 e8 fe ff ff       	call   401bf0 <threadwork>
  401d08:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  401d0c:	74 f2                	je     401d00 <work+0x20>
  401d0e:	8b 53 64             	mov    0x64(%rbx),%edx
  401d11:	48 8d 35 ff 02 00 00 	lea    0x2ff(%rip),%rsi        # 402017 <_IO_stdin_used+0x17>
  401d18:	bf 01 00 00 00       	mov    $0x1,%edi
  401d1d:	31 c0                	xor    %eax,%eax
  401d1f:	e8 7c f3 ff ff       	call   4010a0 <__printf_chk@plt>
  401d24:	5b                   	pop    %rbx
  401d25:	c3                   	ret
  401d26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401d30 <work2>:
  401d30:	eb 0b                	jmp    401d3d <work2+0xd>
  401d32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  401d38:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  401d3d:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  401d41:	74 f5                	je     401d38 <work2+0x8>
  401d43:	c3                   	ret

Disassembly of section .fini:

0000000000401d44 <_fini>:
  401d44:	f3 0f 1e fa          	endbr64
  401d48:	48 83 ec 08          	sub    $0x8,%rsp
  401d4c:	48 83 c4 08          	add    $0x8,%rsp
  401d50:	c3                   	ret
