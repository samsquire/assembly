
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

0000000000401020 <__snprintf_chk@plt-0x10>:
  401020:	ff 35 42 3f 00 00    	push   0x3f42(%rip)        # 404f68 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 44 3f 00 00    	jmp    *0x3f44(%rip)        # 404f70 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <__snprintf_chk@plt>:
  401030:	ff 25 42 3f 00 00    	jmp    *0x3f42(%rip)        # 404f78 <__snprintf_chk@GLIBC_2.3.4>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <pthread_setaffinity_np@plt>:
  401040:	ff 25 3a 3f 00 00    	jmp    *0x3f3a(%rip)        # 404f80 <pthread_setaffinity_np@GLIBC_2.34>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <puts@plt>:
  401050:	ff 25 32 3f 00 00    	jmp    *0x3f32(%rip)        # 404f88 <puts@GLIBC_2.2.5>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <clock_gettime@plt>:
  401060:	ff 25 2a 3f 00 00    	jmp    *0x3f2a(%rip)        # 404f90 <clock_gettime@GLIBC_2.17>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <fclose@plt>:
  401070:	ff 25 22 3f 00 00    	jmp    *0x3f22(%rip)        # 404f98 <fclose@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <__stack_chk_fail@plt>:
  401080:	ff 25 1a 3f 00 00    	jmp    *0x3f1a(%rip)        # 404fa0 <__stack_chk_fail@GLIBC_2.4>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <nanosleep@plt>:
  401090:	ff 25 12 3f 00 00    	jmp    *0x3f12(%rip)        # 404fa8 <nanosleep@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <fputs@plt>:
  4010a0:	ff 25 0a 3f 00 00    	jmp    *0x3f0a(%rip)        # 404fb0 <fputs@GLIBC_2.2.5>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <memset@plt>:
  4010b0:	ff 25 02 3f 00 00    	jmp    *0x3f02(%rip)        # 404fb8 <memset@GLIBC_2.2.5>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <calloc@plt>:
  4010c0:	ff 25 fa 3e 00 00    	jmp    *0x3efa(%rip)        # 404fc0 <calloc@GLIBC_2.2.5>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010d0 <__printf_chk@plt>:
  4010d0:	ff 25 f2 3e 00 00    	jmp    *0x3ef2(%rip)        # 404fc8 <__printf_chk@GLIBC_2.3.4>
  4010d6:	68 0a 00 00 00       	push   $0xa
  4010db:	e9 40 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010e0 <pthread_create@plt>:
  4010e0:	ff 25 ea 3e 00 00    	jmp    *0x3eea(%rip)        # 404fd0 <pthread_create@GLIBC_2.34>
  4010e6:	68 0b 00 00 00       	push   $0xb
  4010eb:	e9 30 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010f0 <fopen@plt>:
  4010f0:	ff 25 e2 3e 00 00    	jmp    *0x3ee2(%rip)        # 404fd8 <fopen@GLIBC_2.2.5>
  4010f6:	68 0c 00 00 00       	push   $0xc
  4010fb:	e9 20 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401100 <posix_memalign@plt>:
  401100:	ff 25 da 3e 00 00    	jmp    *0x3eda(%rip)        # 404fe0 <posix_memalign@GLIBC_2.2.5>
  401106:	68 0d 00 00 00       	push   $0xd
  40110b:	e9 10 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401110 <pthread_join@plt>:
  401110:	ff 25 d2 3e 00 00    	jmp    *0x3ed2(%rip)        # 404fe8 <pthread_join@GLIBC_2.34>
  401116:	68 0e 00 00 00       	push   $0xe
  40111b:	e9 00 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

0000000000401120 <main>:
  401120:	41 57                	push   %r15
  401122:	ba 08 00 00 00       	mov    $0x8,%edx
  401127:	bf 01 00 00 00       	mov    $0x1,%edi
  40112c:	48 8d 35 f4 1e 00 00 	lea    0x1ef4(%rip),%rsi        # 403027 <_IO_stdin_used+0x27>
  401133:	41 56                	push   %r14
  401135:	41 be 01 00 00 00    	mov    $0x1,%r14d
  40113b:	41 55                	push   %r13
  40113d:	4d 89 f5             	mov    %r14,%r13
  401140:	41 54                	push   %r12
  401142:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
  401148:	55                   	push   %rbp
  401149:	53                   	push   %rbx
  40114a:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
  401151:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40115a:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
  40115f:	31 c0                	xor    %eax,%eax
  401161:	e8 6a ff ff ff       	call   4010d0 <__printf_chk@plt>
  401166:	ba 04 00 00 00       	mov    $0x4,%edx
  40116b:	48 8d 35 c7 1e 00 00 	lea    0x1ec7(%rip),%rsi        # 403039 <_IO_stdin_used+0x39>
  401172:	31 c0                	xor    %eax,%eax
  401174:	bf 01 00 00 00       	mov    $0x1,%edi
  401179:	e8 52 ff ff ff       	call   4010d0 <__printf_chk@plt>
  40117e:	ba 20 00 00 00       	mov    $0x20,%edx
  401183:	48 8d 35 ab 1e 00 00 	lea    0x1eab(%rip),%rsi        # 403035 <_IO_stdin_used+0x35>
  40118a:	31 c0                	xor    %eax,%eax
  40118c:	bf 01 00 00 00       	mov    $0x1,%edi
  401191:	e8 3a ff ff ff       	call   4010d0 <__printf_chk@plt>
  401196:	ba 0f 00 00 00       	mov    $0xf,%edx
  40119b:	48 8d 35 a6 1e 00 00 	lea    0x1ea6(%rip),%rsi        # 403048 <_IO_stdin_used+0x48>
  4011a2:	31 c0                	xor    %eax,%eax
  4011a4:	bf 01 00 00 00       	mov    $0x1,%edi
  4011a9:	e8 22 ff ff ff       	call   4010d0 <__printf_chk@plt>
  4011ae:	be 08 00 00 00       	mov    $0x8,%esi
  4011b3:	bf 0f 00 00 00       	mov    $0xf,%edi
  4011b8:	e8 03 ff ff ff       	call   4010c0 <calloc@plt>
  4011bd:	be 38 00 00 00       	mov    $0x38,%esi
  4011c2:	bf 0f 00 00 00       	mov    $0xf,%edi
  4011c7:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  4011cc:	e8 ef fe ff ff       	call   4010c0 <calloc@plt>
  4011d1:	be 00 3c 00 00       	mov    $0x3c00,%esi
  4011d6:	bf 01 00 00 00       	mov    $0x1,%edi
  4011db:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  4011e0:	e8 db fe ff ff       	call   4010c0 <calloc@plt>
  4011e5:	4c 89 e7             	mov    %r12,%rdi
  4011e8:	be 01 00 00 00       	mov    $0x1,%esi
  4011ed:	48 89 c3             	mov    %rax,%rbx
  4011f0:	e8 cb fe ff ff       	call   4010c0 <calloc@plt>
  4011f5:	4c 89 e2             	mov    %r12,%rdx
  4011f8:	be ff ff ff ff       	mov    $0xffffffff,%esi
  4011fd:	49 89 de             	mov    %rbx,%r14
  401200:	48 89 c7             	mov    %rax,%rdi
  401203:	48 89 c5             	mov    %rax,%rbp
  401206:	e8 a5 fe ff ff       	call   4010b0 <memset@plt>
  40120b:	4c 89 e2             	mov    %r12,%rdx
  40120e:	bf 01 00 00 00       	mov    $0x1,%edi
  401213:	31 c0                	xor    %eax,%eax
  401215:	48 8d 35 41 1e 00 00 	lea    0x1e41(%rip),%rsi        # 40305d <_IO_stdin_used+0x5d>
  40121c:	e8 af fe ff ff       	call   4010d0 <__printf_chk@plt>
  401221:	be 20 00 00 00       	mov    $0x20,%esi
  401226:	bf 64 00 00 00       	mov    $0x64,%edi
  40122b:	e8 90 fe ff ff       	call   4010c0 <calloc@plt>
  401230:	31 d2                	xor    %edx,%edx
  401232:	bf 01 00 00 00       	mov    $0x1,%edi
  401237:	48 8d 35 30 1e 00 00 	lea    0x1e30(%rip),%rsi        # 40306e <_IO_stdin_used+0x6e>
  40123e:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  401243:	31 c0                	xor    %eax,%eax
  401245:	e8 86 fe ff ff       	call   4010d0 <__printf_chk@plt>
  40124a:	4c 89 e2             	mov    %r12,%rdx
  40124d:	bf 01 00 00 00       	mov    $0x1,%edi
  401252:	31 c0                	xor    %eax,%eax
  401254:	48 8d 35 1f 1e 00 00 	lea    0x1e1f(%rip),%rsi        # 40307a <_IO_stdin_used+0x7a>
  40125b:	e8 70 fe ff ff       	call   4010d0 <__printf_chk@plt>
  401260:	be 04 00 00 00       	mov    $0x4,%esi
  401265:	bf 0f 00 00 00       	mov    $0xf,%edi
  40126a:	e8 51 fe ff ff       	call   4010c0 <calloc@plt>
  40126f:	ba 00 02 00 00       	mov    $0x200,%edx
  401274:	48 8d 7c 24 48       	lea    0x48(%rsp),%rdi
  401279:	be 80 00 00 00       	mov    $0x80,%esi
  40127e:	49 89 c4             	mov    %rax,%r12
  401281:	e8 7a fe ff ff       	call   401100 <posix_memalign@plt>
  401286:	be 0c 00 00 00       	mov    $0xc,%esi
  40128b:	bf 0f 00 00 00       	mov    $0xf,%edi
  401290:	85 c0                	test   %eax,%eax
  401292:	b8 00 00 00 00       	mov    $0x0,%eax
  401297:	48 0f 44 44 24 48    	cmove  0x48(%rsp),%rax
  40129d:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  4012a2:	e8 19 fe ff ff       	call   4010c0 <calloc@plt>
  4012a7:	48 89 6b 70          	mov    %rbp,0x70(%rbx)
  4012ab:	be 14 00 00 00       	mov    $0x14,%esi
  4012b0:	bf 80 96 98 00       	mov    $0x989680,%edi
  4012b5:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  4012ba:	e8 01 fe ff ff       	call   4010c0 <calloc@plt>
  4012bf:	be 14 00 00 00       	mov    $0x14,%esi
  4012c4:	bf 80 96 98 00       	mov    $0x989680,%edi
  4012c9:	48 89 c5             	mov    %rax,%rbp
  4012cc:	e8 ef fd ff ff       	call   4010c0 <calloc@plt>
  4012d1:	66 48 0f 6e ed       	movq   %rbp,%xmm5
  4012d6:	31 ed                	xor    %ebp,%ebp
  4012d8:	66 48 0f 6e f0       	movq   %rax,%xmm6
  4012dd:	66 0f 6c ee          	punpcklqdq %xmm6,%xmm5
  4012e1:	0f 29 6c 24 20       	movaps %xmm5,0x20(%rsp)
  4012e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4012f0:	66 0f 6f 4c 24 20    	movdqa 0x20(%rsp),%xmm1
  4012f6:	be 80 00 00 00       	mov    $0x80,%esi
  4012fb:	44 89 2c 24          	mov    %r13d,(%rsp)
  4012ff:	45 8d 7d ff          	lea    -0x1(%r13),%r15d
  401303:	bf 01 00 00 00       	mov    $0x1,%edi
  401308:	49 81 c6 00 04 00 00 	add    $0x400,%r14
  40130f:	41 0f 29 4e a0       	movaps %xmm1,-0x60(%r14)
  401314:	e8 a7 fd ff ff       	call   4010c0 <calloc@plt>
  401319:	44 89 e9             	mov    %r13d,%ecx
  40131c:	be 01 00 00 00       	mov    $0x1,%esi
  401321:	44 89 fa             	mov    %r15d,%edx
  401324:	49 89 86 78 fc ff ff 	mov    %rax,-0x388(%r14)
  40132b:	48 d3 e6             	shl    %cl,%rsi
  40132e:	8b 0c 24             	mov    (%rsp),%ecx
  401331:	bf 01 00 00 00       	mov    $0x1,%edi
  401336:	48 09 30             	or     %rsi,(%rax)
  401339:	48 8d 35 b8 1e 00 00 	lea    0x1eb8(%rip),%rsi        # 4031f8 <_IO_stdin_used+0x1f8>
  401340:	31 c0                	xor    %eax,%eax
  401342:	e8 89 fd ff ff       	call   4010d0 <__printf_chk@plt>
  401347:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  40134c:	44 89 fa             	mov    %r15d,%edx
  40134f:	41 89 ae 98 fc ff ff 	mov    %ebp,-0x368(%r14)
  401356:	c1 fa 02             	sar    $0x2,%edx
  401359:	66 0f 6f 15 1f 1f 00 00 	movdqa 0x1f1f(%rip),%xmm2        # 403280 <_IO_stdin_used+0x280>
  401361:	66 0f 6f 1d 27 1f 00 00 	movdqa 0x1f27(%rip),%xmm3        # 403290 <_IO_stdin_used+0x290>
  401369:	41 c7 86 80 fc ff ff 00 00 00 00 	movl   $0x0,-0x380(%r14)
  401374:	49 89 46 80          	mov    %rax,-0x80(%r14)
  401378:	83 c2 01             	add    $0x1,%edx
  40137b:	48 8b 05 ee 1e 00 00 	mov    0x1eee(%rip),%rax        # 403270 <_IO_stdin_used+0x270>
  401382:	be 30 00 00 00       	mov    $0x30,%esi
  401387:	66 0f 6f 25 11 1f 00 00 	movdqa 0x1f11(%rip),%xmm4        # 4032a0 <_IO_stdin_used+0x2a0>
  40138f:	bf 80 96 98 00       	mov    $0x989680,%edi
  401394:	45 89 be 64 fc ff ff 	mov    %r15d,-0x39c(%r14)
  40139b:	81 c5 11 11 11 11    	add    $0x11111111,%ebp
  4013a1:	49 89 86 5c fc ff ff 	mov    %rax,-0x3a4(%r14)
  4013a8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  4013ad:	41 c7 86 94 fc ff ff 11 11 11 11 	movl   $0x11111111,-0x36c(%r14)
  4013b8:	41 c7 86 68 fc ff ff 0f 00 00 00 	movl   $0xf,-0x398(%r14)
  4013c3:	4d 89 a6 20 fc ff ff 	mov    %r12,-0x3e0(%r14)
  4013ca:	43 c7 44 ac fc 00 00 00 00 	movl   $0x0,-0x4(%r12,%r13,4)
  4013d3:	49 83 c5 01          	add    $0x1,%r13
  4013d7:	41 89 56 8c          	mov    %edx,-0x74(%r14)
  4013db:	41 c7 86 90 fc ff ff 11 11 11 11 	movl   $0x11111111,-0x370(%r14)
  4013e6:	49 89 9e 28 fc ff ff 	mov    %rbx,-0x3d8(%r14)
  4013ed:	49 89 9e 30 fc ff ff 	mov    %rbx,-0x3d0(%r14)
  4013f4:	41 c7 86 00 fe ff ff 0e 00 00 00 	movl   $0xe,-0x200(%r14)
  4013ff:	41 c7 86 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%r14)
  40140a:	49 89 86 a0 fc ff ff 	mov    %rax,-0x360(%r14)
  401411:	41 c7 86 c8 fc ff ff 00 00 00 00 	movl   $0x0,-0x338(%r14)
  40141c:	41 c7 86 28 ff ff ff 0f 00 00 00 	movl   $0xf,-0xd8(%r14)
  401427:	41 0f 29 96 00 fc ff ff 	movaps %xmm2,-0x400(%r14)
  40142f:	41 0f 11 9e b8 fc ff ff 	movups %xmm3,-0x348(%r14)
  401437:	41 0f 11 a6 08 ff ff ff 	movups %xmm4,-0xf8(%r14)
  40143f:	e8 7c fc ff ff       	call   4010c0 <calloc@plt>
  401444:	be 30 00 00 00       	mov    $0x30,%esi
  401449:	bf 10 27 00 00       	mov    $0x2710,%edi
  40144e:	41 c7 86 20 ff ff ff 80 96 98 00 	movl   $0x989680,-0xe0(%r14)
  401459:	49 89 86 18 ff ff ff 	mov    %rax,-0xe8(%r14)
  401460:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  401465:	49 89 86 48 ff ff ff 	mov    %rax,-0xb8(%r14)
  40146c:	e8 4f fc ff ff       	call   4010c0 <calloc@plt>
  401471:	41 c7 46 b8 80 96 98 00 	movl   $0x989680,-0x48(%r14)
  401479:	49 89 86 30 ff ff ff 	mov    %rax,-0xd0(%r14)
  401480:	49 83 fd 10          	cmp    $0x10,%r13
  401484:	0f 85 66 fe ff ff    	jne    4012f0 <main+0x1d0>
  40148a:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
  40148f:	4c 8b 7c 24 30       	mov    0x30(%rsp),%r15
  401494:	48 89 1c 24          	mov    %rbx,(%rsp)
  401498:	49 c7 c5 90 23 40 00 	mov    $0x402390,%r13
  40149f:	48 8d 85 48 03 00 00 	lea    0x348(%rbp),%rax
  4014a6:	4d 89 fc             	mov    %r15,%r12
  4014a9:	49 89 c6             	mov    %rax,%r14
  4014ac:	0f 1f 40 00          	nopl   0x0(%rax)
  4014b0:	48 89 d9             	mov    %rbx,%rcx
  4014b3:	48 89 ee             	mov    %rbp,%rsi
  4014b6:	4c 89 ff             	mov    %r15,%rdi
  4014b9:	4c 89 ea             	mov    %r13,%rdx
  4014bc:	e8 1f fc ff ff       	call   4010e0 <pthread_create@plt>
  4014c1:	48 8b 53 78          	mov    0x78(%rbx),%rdx
  4014c5:	49 8b 3f             	mov    (%r15),%rdi
  4014c8:	be 08 00 00 00       	mov    $0x8,%esi
  4014cd:	48 83 c5 38          	add    $0x38,%rbp
  4014d1:	49 83 c7 08          	add    $0x8,%r15
  4014d5:	48 81 c3 00 04 00 00 	add    $0x400,%rbx
  4014dc:	e8 5f fb ff ff       	call   401040 <pthread_setaffinity_np@plt>
  4014e1:	4c 39 f5             	cmp    %r14,%rbp
  4014e4:	75 ca                	jne    4014b0 <main+0x390>
  4014e6:	48 8b 1c 24          	mov    (%rsp),%rbx
  4014ea:	48 8d 74 24 60       	lea    0x60(%rsp),%rsi
  4014ef:	48 8d 7c 24 50       	lea    0x50(%rsp),%rdi
  4014f4:	66 0f 6f 05 b4 1d 00 00 	movdqa 0x1db4(%rip),%xmm0        # 4032b0 <_IO_stdin_used+0x2b0>
  4014fc:	4c 8d 6c 24 40       	lea    0x40(%rsp),%r13
  401501:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  401506:	66 0f ef c0          	pxor   %xmm0,%xmm0
  40150a:	0f 29 44 24 60       	movaps %xmm0,0x60(%rsp)
  40150f:	e8 7c fb ff ff       	call   401090 <nanosleep@plt>
  401514:	48 8d 3d 6b 1b 00 00 	lea    0x1b6b(%rip),%rdi        # 403086 <_IO_stdin_used+0x86>
  40151b:	e8 30 fb ff ff       	call   401050 <puts@plt>
  401520:	83 6b 5c 01          	subl   $0x1,0x5c(%rbx)
  401524:	48 8d 3d 65 1b 00 00 	lea    0x1b65(%rip),%rdi        # 403090 <_IO_stdin_used+0x90>
  40152b:	83 ab 5c 04 00 00 01 	subl   $0x1,0x45c(%rbx)
  401532:	83 ab 5c 08 00 00 01 	subl   $0x1,0x85c(%rbx)
  401539:	83 ab 5c 0c 00 00 01 	subl   $0x1,0xc5c(%rbx)
  401540:	83 ab 5c 10 00 00 01 	subl   $0x1,0x105c(%rbx)
  401547:	83 ab 5c 14 00 00 01 	subl   $0x1,0x145c(%rbx)
  40154e:	83 ab 5c 18 00 00 01 	subl   $0x1,0x185c(%rbx)
  401555:	83 ab 5c 1c 00 00 01 	subl   $0x1,0x1c5c(%rbx)
  40155c:	83 ab 5c 20 00 00 01 	subl   $0x1,0x205c(%rbx)
  401563:	83 ab 5c 24 00 00 01 	subl   $0x1,0x245c(%rbx)
  40156a:	83 ab 5c 28 00 00 01 	subl   $0x1,0x285c(%rbx)
  401571:	83 ab 5c 2c 00 00 01 	subl   $0x1,0x2c5c(%rbx)
  401578:	83 ab 5c 30 00 00 01 	subl   $0x1,0x305c(%rbx)
  40157f:	83 ab 5c 34 00 00 01 	subl   $0x1,0x345c(%rbx)
  401586:	83 ab 5c 38 00 00 01 	subl   $0x1,0x385c(%rbx)
  40158d:	e8 be fa ff ff       	call   401050 <puts@plt>
  401592:	48 8b 6c 24 30       	mov    0x30(%rsp),%rbp
  401597:	83 6b 5c 01          	subl   $0x1,0x5c(%rbx)
  40159b:	83 ab 5c 04 00 00 01 	subl   $0x1,0x45c(%rbx)
  4015a2:	83 ab 5c 08 00 00 01 	subl   $0x1,0x85c(%rbx)
  4015a9:	83 ab 5c 0c 00 00 01 	subl   $0x1,0xc5c(%rbx)
  4015b0:	83 ab 5c 10 00 00 01 	subl   $0x1,0x105c(%rbx)
  4015b7:	83 ab 5c 14 00 00 01 	subl   $0x1,0x145c(%rbx)
  4015be:	83 ab 5c 18 00 00 01 	subl   $0x1,0x185c(%rbx)
  4015c5:	83 ab 5c 1c 00 00 01 	subl   $0x1,0x1c5c(%rbx)
  4015cc:	83 ab 5c 20 00 00 01 	subl   $0x1,0x205c(%rbx)
  4015d3:	83 ab 5c 24 00 00 01 	subl   $0x1,0x245c(%rbx)
  4015da:	83 ab 5c 28 00 00 01 	subl   $0x1,0x285c(%rbx)
  4015e1:	83 ab 5c 2c 00 00 01 	subl   $0x1,0x2c5c(%rbx)
  4015e8:	83 ab 5c 30 00 00 01 	subl   $0x1,0x305c(%rbx)
  4015ef:	83 ab 5c 34 00 00 01 	subl   $0x1,0x345c(%rbx)
  4015f6:	83 ab 5c 38 00 00 01 	subl   $0x1,0x385c(%rbx)
  4015fd:	48 83 c5 78          	add    $0x78,%rbp
  401601:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401608:	49 8b 3c 24          	mov    (%r12),%rdi
  40160c:	4c 89 ee             	mov    %r13,%rsi
  40160f:	49 83 c4 08          	add    $0x8,%r12
  401613:	e8 f8 fa ff ff       	call   401110 <pthread_join@plt>
  401618:	49 39 ec             	cmp    %rbp,%r12
  40161b:	75 eb                	jne    401608 <main+0x4e8>
  40161d:	48 8d 3d 75 1a 00 00 	lea    0x1a75(%rip),%rdi        # 403099 <_IO_stdin_used+0x99>
  401624:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  401628:	45 31 e4             	xor    %r12d,%r12d
  40162b:	e8 20 fa ff ff       	call   401050 <puts@plt>
  401630:	4c 8d b3 48 3c 00 00 	lea    0x3c48(%rbx),%r14
  401637:	4c 8d 2d 70 1a 00 00 	lea    0x1a70(%rip),%r13        # 4030ae <_IO_stdin_used+0xae>
  40163e:	66 90                	xchg   %ax,%ax
  401640:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401644:	4c 89 ee             	mov    %r13,%rsi
  401647:	bf 01 00 00 00       	mov    $0x1,%edi
  40164c:	31 c0                	xor    %eax,%eax
  40164e:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
  401655:	e8 76 fa ff ff       	call   4010d0 <__printf_chk@plt>
  40165a:	4c 03 a5 00 fc ff ff 	add    -0x400(%rbp),%r12
  401661:	4c 39 f5             	cmp    %r14,%rbp
  401664:	75 da                	jne    401640 <main+0x520>
  401666:	4c 89 e2             	mov    %r12,%rdx
  401669:	48 8d 35 49 1a 00 00 	lea    0x1a49(%rip),%rsi        # 4030b9 <_IO_stdin_used+0xb9>
  401670:	bf 01 00 00 00       	mov    $0x1,%edi
  401675:	31 c0                	xor    %eax,%eax
  401677:	e8 54 fa ff ff       	call   4010d0 <__printf_chk@plt>
  40167c:	4c 89 e2             	mov    %r12,%rdx
  40167f:	bf 01 00 00 00       	mov    $0x1,%edi
  401684:	31 c0                	xor    %eax,%eax
  401686:	48 8d 35 37 1a 00 00 	lea    0x1a37(%rip),%rsi        # 4030c4 <_IO_stdin_used+0xc4>
  40168d:	48 8d ab 98 03 00 00 	lea    0x398(%rbx),%rbp
  401694:	e8 37 fa ff ff       	call   4010d0 <__printf_chk@plt>
  401699:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40169e:	48 8d 35 2d 1a 00 00 	lea    0x1a2d(%rip),%rsi        # 4030d2 <_IO_stdin_used+0xd2>
  4016a5:	bf 01 00 00 00       	mov    $0x1,%edi
  4016aa:	48 99                	cqto
  4016ac:	4c 8d bb 98 3f 00 00 	lea    0x3f98(%rbx),%r15
  4016b3:	4c 8d 35 5d 1a 00 00 	lea    0x1a5d(%rip),%r14        # 403117 <_IO_stdin_used+0x117>
  4016ba:	49 f7 fc             	idiv   %r12
  4016bd:	49 89 c4             	mov    %rax,%r12
  4016c0:	48 89 c2             	mov    %rax,%rdx
  4016c3:	31 c0                	xor    %eax,%eax
  4016c5:	e8 06 fa ff ff       	call   4010d0 <__printf_chk@plt>
  4016ca:	4c 89 e2             	mov    %r12,%rdx
  4016cd:	bf 01 00 00 00       	mov    $0x1,%edi
  4016d2:	31 c0                	xor    %eax,%eax
  4016d4:	48 8d 35 0b 1a 00 00 	lea    0x1a0b(%rip),%rsi        # 4030e6 <_IO_stdin_used+0xe6>
  4016db:	e8 f0 f9 ff ff       	call   4010d0 <__printf_chk@plt>
  4016e0:	4c 89 e2             	mov    %r12,%rdx
  4016e3:	bf 01 00 00 00       	mov    $0x1,%edi
  4016e8:	31 c0                	xor    %eax,%eax
  4016ea:	48 8d 35 13 1a 00 00 	lea    0x1a13(%rip),%rsi        # 403104 <_IO_stdin_used+0x104>
  4016f1:	45 31 e4             	xor    %r12d,%r12d
  4016f4:	e8 d7 f9 ff ff       	call   4010d0 <__printf_chk@plt>
  4016f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401700:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401704:	4c 89 f6             	mov    %r14,%rsi
  401707:	bf 01 00 00 00       	mov    $0x1,%edi
  40170c:	31 c0                	xor    %eax,%eax
  40170e:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
  401715:	e8 b6 f9 ff ff       	call   4010d0 <__printf_chk@plt>
  40171a:	4c 8b ad 00 fc ff ff 	mov    -0x400(%rbp),%r13
  401721:	4d 01 e5             	add    %r12,%r13
  401724:	4d 89 ec             	mov    %r13,%r12
  401727:	49 39 ef             	cmp    %rbp,%r15
  40172a:	75 d4                	jne    401700 <main+0x5e0>
  40172c:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  401730:	4c 8d bb 50 3c 00 00 	lea    0x3c50(%rbx),%r15
  401737:	45 31 e4             	xor    %r12d,%r12d
  40173a:	4c 8d 35 e8 19 00 00 	lea    0x19e8(%rip),%r14        # 403129 <_IO_stdin_used+0x129>
  401741:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401748:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  40174c:	4c 89 f6             	mov    %r14,%rsi
  40174f:	bf 01 00 00 00       	mov    $0x1,%edi
  401754:	31 c0                	xor    %eax,%eax
  401756:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
  40175d:	49 01 d4             	add    %rdx,%r12
  401760:	e8 6b f9 ff ff       	call   4010d0 <__printf_chk@plt>
  401765:	49 39 ef             	cmp    %rbp,%r15
  401768:	75 de                	jne    401748 <main+0x628>
  40176a:	4c 89 e2             	mov    %r12,%rdx
  40176d:	bf 01 00 00 00       	mov    $0x1,%edi
  401772:	31 c0                	xor    %eax,%eax
  401774:	bd 00 ca 9a 3b       	mov    $0x3b9aca00,%ebp
  401779:	48 8d 35 b5 19 00 00 	lea    0x19b5(%rip),%rsi        # 403135 <_IO_stdin_used+0x135>
  401780:	4c 8d b3 20 03 00 00 	lea    0x320(%rbx),%r14
  401787:	e8 44 f9 ff ff       	call   4010d0 <__printf_chk@plt>
  40178c:	4c 89 e2             	mov    %r12,%rdx
  40178f:	bf 01 00 00 00       	mov    $0x1,%edi
  401794:	31 c0                	xor    %eax,%eax
  401796:	48 8d 35 aa 19 00 00 	lea    0x19aa(%rip),%rsi        # 403147 <_IO_stdin_used+0x147>
  40179d:	e8 2e f9 ff ff       	call   4010d0 <__printf_chk@plt>
  4017a2:	48 89 e8             	mov    %rbp,%rax
  4017a5:	bf 01 00 00 00       	mov    $0x1,%edi
  4017aa:	48 8d 35 ae 19 00 00 	lea    0x19ae(%rip),%rsi        # 40315f <_IO_stdin_used+0x15f>
  4017b1:	48 99                	cqto
  4017b3:	49 f7 fc             	idiv   %r12
  4017b6:	49 89 c4             	mov    %rax,%r12
  4017b9:	48 89 c2             	mov    %rax,%rdx
  4017bc:	31 c0                	xor    %eax,%eax
  4017be:	e8 0d f9 ff ff       	call   4010d0 <__printf_chk@plt>
  4017c3:	4c 89 e2             	mov    %r12,%rdx
  4017c6:	bf 01 00 00 00       	mov    $0x1,%edi
  4017cb:	31 c0                	xor    %eax,%eax
  4017cd:	48 8d 35 44 1a 00 00 	lea    0x1a44(%rip),%rsi        # 403218 <_IO_stdin_used+0x218>
  4017d4:	e8 f7 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  4017d9:	4c 89 e2             	mov    %r12,%rdx
  4017dc:	bf 01 00 00 00       	mov    $0x1,%edi
  4017e1:	31 c0                	xor    %eax,%eax
  4017e3:	48 8d 35 90 19 00 00 	lea    0x1990(%rip),%rsi        # 40317a <_IO_stdin_used+0x17a>
  4017ea:	4c 8d 25 f0 18 00 00 	lea    0x18f0(%rip),%r12        # 4030e1 <_IO_stdin_used+0xe1>
  4017f1:	e8 da f8 ff ff       	call   4010d0 <__printf_chk@plt>
  4017f6:	48 8d 3d 97 19 00 00 	lea    0x1997(%rip),%rdi        # 403194 <_IO_stdin_used+0x194>
  4017fd:	e8 4e f8 ff ff       	call   401050 <puts@plt>
  401802:	4c 89 e6             	mov    %r12,%rsi
  401805:	bf 01 00 00 00       	mov    $0x1,%edi
  40180a:	31 c0                	xor    %eax,%eax
  40180c:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  401813:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  40181a:	e8 b1 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  40181f:	4c 89 e6             	mov    %r12,%rsi
  401822:	bf 01 00 00 00       	mov    $0x1,%edi
  401827:	31 c0                	xor    %eax,%eax
  401829:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  401830:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  401837:	e8 94 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  40183c:	4c 89 e6             	mov    %r12,%rsi
  40183f:	bf 01 00 00 00       	mov    $0x1,%edi
  401844:	31 c0                	xor    %eax,%eax
  401846:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  40184d:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401854:	e8 77 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  401859:	4c 89 e6             	mov    %r12,%rsi
  40185c:	bf 01 00 00 00       	mov    $0x1,%edi
  401861:	31 c0                	xor    %eax,%eax
  401863:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  40186a:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  401871:	e8 5a f8 ff ff       	call   4010d0 <__printf_chk@plt>
  401876:	4c 89 e6             	mov    %r12,%rsi
  401879:	bf 01 00 00 00       	mov    $0x1,%edi
  40187e:	31 c0                	xor    %eax,%eax
  401880:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401887:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  40188e:	e8 3d f8 ff ff       	call   4010d0 <__printf_chk@plt>
  401893:	4c 89 e6             	mov    %r12,%rsi
  401896:	bf 01 00 00 00       	mov    $0x1,%edi
  40189b:	31 c0                	xor    %eax,%eax
  40189d:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  4018a4:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  4018ab:	e8 20 f8 ff ff       	call   4010d0 <__printf_chk@plt>
  4018b0:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  4018b7:	bf 01 00 00 00       	mov    $0x1,%edi
  4018bc:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  4018c3:	48 8d 35 d7 18 00 00 	lea    0x18d7(%rip),%rsi        # 4031a1 <_IO_stdin_used+0x1a1>
  4018ca:	31 c0                	xor    %eax,%eax
  4018cc:	48 81 c3 20 3f 00 00 	add    $0x3f20,%rbx
  4018d3:	e8 f8 f7 ff ff       	call   4010d0 <__printf_chk@plt>
  4018d8:	4c 89 ea             	mov    %r13,%rdx
  4018db:	bf 01 00 00 00       	mov    $0x1,%edi
  4018e0:	31 c0                	xor    %eax,%eax
  4018e2:	48 8d 35 c0 18 00 00 	lea    0x18c0(%rip),%rsi        # 4031a9 <_IO_stdin_used+0x1a9>
  4018e9:	e8 e2 f7 ff ff       	call   4010d0 <__printf_chk@plt>
  4018ee:	48 89 e8             	mov    %rbp,%rax
  4018f1:	bf 01 00 00 00       	mov    $0x1,%edi
  4018f6:	48 8d 35 43 19 00 00 	lea    0x1943(%rip),%rsi        # 403240 <_IO_stdin_used+0x240>
  4018fd:	48 99                	cqto
  4018ff:	49 f7 fd             	idiv   %r13
  401902:	45 31 ed             	xor    %r13d,%r13d
  401905:	48 89 c2             	mov    %rax,%rdx
  401908:	31 c0                	xor    %eax,%eax
  40190a:	e8 c1 f7 ff ff       	call   4010d0 <__printf_chk@plt>
  40190f:	48 8d 3d ae 18 00 00 	lea    0x18ae(%rip),%rdi        # 4031c4 <_IO_stdin_used+0x1c4>
  401916:	e8 35 f7 ff ff       	call   401050 <puts@plt>
  40191b:	be 01 00 00 00       	mov    $0x1,%esi
  401920:	bf 64 00 00 00       	mov    $0x64,%edi
  401925:	e8 96 f7 ff ff       	call   4010c0 <calloc@plt>
  40192a:	be 01 00 00 00       	mov    $0x1,%esi
  40192f:	bf e8 03 00 00       	mov    $0x3e8,%edi
  401934:	49 89 c4             	mov    %rax,%r12
  401937:	e8 84 f7 ff ff       	call   4010c0 <calloc@plt>
  40193c:	4c 89 e7             	mov    %r12,%rdi
  40193f:	48 8d 35 92 18 00 00 	lea    0x1892(%rip),%rsi        # 4031d8 <_IO_stdin_used+0x1d8>
  401946:	48 89 c5             	mov    %rax,%rbp
  401949:	48 b8 73 61 6d 70 6c 65 73 00 	movabs $0x73656c706d6173,%rax
  401953:	49 89 04 24          	mov    %rax,(%r12)
  401957:	e8 94 f7 ff ff       	call   4010f0 <fopen@plt>
  40195c:	49 89 c4             	mov    %rax,%r12
  40195f:	90                   	nop
  401960:	41 8b 0e             	mov    (%r14),%ecx
  401963:	45 31 ff             	xor    %r15d,%r15d
  401966:	85 c9                	test   %ecx,%ecx
  401968:	7e 21                	jle    40198b <main+0x86b>
  40196a:	49 8b 76 f8          	mov    -0x8(%r14),%rsi
  40196e:	49 63 c7             	movslq %r15d,%rax
  401971:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  401975:	48 c1 e2 04          	shl    $0x4,%rdx
  401979:	48 01 f2             	add    %rsi,%rdx
  40197c:	83 7a 24 01          	cmpl   $0x1,0x24(%rdx)
  401980:	74 4e                	je     4019d0 <main+0x8b0>
  401982:	41 83 c7 01          	add    $0x1,%r15d
  401986:	41 39 cf             	cmp    %ecx,%r15d
  401989:	7c e3                	jl     40196e <main+0x84e>
  40198b:	49 81 c6 00 04 00 00 	add    $0x400,%r14
  401992:	4c 39 f3             	cmp    %r14,%rbx
  401995:	75 c9                	jne    401960 <main+0x840>
  401997:	4c 89 e7             	mov    %r12,%rdi
  40199a:	e8 d1 f6 ff ff       	call   401070 <fclose@plt>
  40199f:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
  4019a4:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4019ad:	0f 85 98 00 00 00    	jne    401a4b <main+0x92b>
  4019b3:	48 81 c4 88 00 00 00 	add    $0x88,%rsp
  4019ba:	31 c0                	xor    %eax,%eax
  4019bc:	5b                   	pop    %rbx
  4019bd:	5d                   	pop    %rbp
  4019be:	41 5c                	pop    %r12
  4019c0:	41 5d                	pop    %r13
  4019c2:	41 5e                	pop    %r14
  4019c4:	41 5f                	pop    %r15
  4019c6:	c3                   	ret
  4019c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  4019d0:	4c 89 e8             	mov    %r13,%rax
  4019d3:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  4019d8:	48 89 ef             	mov    %rbp,%rdi
  4019db:	be 64 00 00 00       	mov    $0x64,%esi
  4019e0:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  4019e3:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  4019e8:	48 89 ef             	mov    %rbp,%rdi
  4019eb:	41 83 c7 01          	add    $0x1,%r15d
  4019ef:	4c 8d 05 e4 17 00 00 	lea    0x17e4(%rip),%r8        # 4031da <_IO_stdin_used+0x1da>
  4019f6:	8b 42 28             	mov    0x28(%rdx),%eax
  4019f9:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
  4019fd:	50                   	push   %rax
  4019fe:	8b 02                	mov    (%rdx),%eax
  401a00:	50                   	push   %rax
  401a01:	8b 42 2c             	mov    0x2c(%rdx),%eax
  401a04:	ff 72 18             	push   0x18(%rdx)
  401a07:	50                   	push   %rax
  401a08:	8b 42 20             	mov    0x20(%rdx),%eax
  401a0b:	50                   	push   %rax
  401a0c:	31 c0                	xor    %eax,%eax
  401a0e:	ff 72 10             	push   0x10(%rdx)
  401a11:	ba 01 00 00 00       	mov    $0x1,%edx
  401a16:	e8 15 f6 ff ff       	call   401030 <__snprintf_chk@plt>
  401a1b:	48 83 c4 30          	add    $0x30,%rsp
  401a1f:	4c 89 e6             	mov    %r12,%rsi
  401a22:	48 89 ef             	mov    %rbp,%rdi
  401a25:	e8 76 f6 ff ff       	call   4010a0 <fputs@plt>
  401a2a:	41 8b 0e             	mov    (%r14),%ecx
  401a2d:	41 39 cf             	cmp    %ecx,%r15d
  401a30:	0f 8c 34 ff ff ff    	jl     40196a <main+0x84a>
  401a36:	49 81 c6 00 04 00 00 	add    $0x400,%r14
  401a3d:	4c 39 f3             	cmp    %r14,%rbx
  401a40:	0f 85 1a ff ff ff    	jne    401960 <main+0x840>
  401a46:	e9 4c ff ff ff       	jmp    401997 <main+0x877>
  401a4b:	e8 30 f6 ff ff       	call   401080 <__stack_chk_fail@plt>

0000000000401a50 <set_fast_math>:
  401a50:	f3 0f 1e fa          	endbr64
  401a54:	0f ae 5c 24 fc       	stmxcsr -0x4(%rsp)
  401a59:	81 4c 24 fc 40 80 00 00 	orl    $0x8040,-0x4(%rsp)
  401a61:	0f ae 54 24 fc       	ldmxcsr -0x4(%rsp)
  401a66:	c3                   	ret
  401a67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000401a70 <_start>:
  401a70:	f3 0f 1e fa          	endbr64
  401a74:	31 ed                	xor    %ebp,%ebp
  401a76:	49 89 d1             	mov    %rdx,%r9
  401a79:	5e                   	pop    %rsi
  401a7a:	48 89 e2             	mov    %rsp,%rdx
  401a7d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401a81:	50                   	push   %rax
  401a82:	54                   	push   %rsp
  401a83:	45 31 c0             	xor    %r8d,%r8d
  401a86:	31 c9                	xor    %ecx,%ecx
  401a88:	48 c7 c7 20 11 40 00 	mov    $0x401120,%rdi
  401a8f:	ff 15 5b 35 00 00    	call   *0x355b(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  401a95:	f4                   	hlt
  401a96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401aa0 <_dl_relocate_static_pie>:
  401aa0:	f3 0f 1e fa          	endbr64
  401aa4:	c3                   	ret
  401aa5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401aaf:	90                   	nop

0000000000401ab0 <deregister_tm_clones>:
  401ab0:	b8 10 50 40 00       	mov    $0x405010,%eax
  401ab5:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  401abb:	74 13                	je     401ad0 <deregister_tm_clones+0x20>
  401abd:	b8 00 00 00 00       	mov    $0x0,%eax
  401ac2:	48 85 c0             	test   %rax,%rax
  401ac5:	74 09                	je     401ad0 <deregister_tm_clones+0x20>
  401ac7:	bf 10 50 40 00       	mov    $0x405010,%edi
  401acc:	ff e0                	jmp    *%rax
  401ace:	66 90                	xchg   %ax,%ax
  401ad0:	c3                   	ret
  401ad1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401adc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401ae0 <register_tm_clones>:
  401ae0:	be 10 50 40 00       	mov    $0x405010,%esi
  401ae5:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  401aec:	48 89 f0             	mov    %rsi,%rax
  401aef:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401af3:	48 c1 f8 03          	sar    $0x3,%rax
  401af7:	48 01 c6             	add    %rax,%rsi
  401afa:	48 d1 fe             	sar    %rsi
  401afd:	74 11                	je     401b10 <register_tm_clones+0x30>
  401aff:	b8 00 00 00 00       	mov    $0x0,%eax
  401b04:	48 85 c0             	test   %rax,%rax
  401b07:	74 07                	je     401b10 <register_tm_clones+0x30>
  401b09:	bf 10 50 40 00       	mov    $0x405010,%edi
  401b0e:	ff e0                	jmp    *%rax
  401b10:	c3                   	ret
  401b11:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401b1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401b20 <__do_global_dtors_aux>:
  401b20:	f3 0f 1e fa          	endbr64
  401b24:	80 3d e5 34 00 00 00 	cmpb   $0x0,0x34e5(%rip)        # 405010 <__TMC_END__>
  401b2b:	75 13                	jne    401b40 <__do_global_dtors_aux+0x20>
  401b2d:	55                   	push   %rbp
  401b2e:	48 89 e5             	mov    %rsp,%rbp
  401b31:	e8 7a ff ff ff       	call   401ab0 <deregister_tm_clones>
  401b36:	c6 05 d3 34 00 00 01 	movb   $0x1,0x34d3(%rip)        # 405010 <__TMC_END__>
  401b3d:	5d                   	pop    %rbp
  401b3e:	c3                   	ret
  401b3f:	90                   	nop
  401b40:	c3                   	ret
  401b41:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401b4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401b50 <frame_dummy>:
  401b50:	f3 0f 1e fa          	endbr64
  401b54:	eb 8a                	jmp    401ae0 <register_tm_clones>
  401b56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401b60 <pollthreads>:
  401b60:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
  401b64:	49 89 f9             	mov    %rdi,%r9
  401b67:	7e 77                	jle    401be0 <pollthreads+0x80>
  401b69:	49 8b 41 30          	mov    0x30(%r9),%rax
  401b6d:	55                   	push   %rbp
  401b6e:	49 89 f2             	mov    %rsi,%r10
  401b71:	49 89 d3             	mov    %rdx,%r11
  401b74:	53                   	push   %rbx
  401b75:	48 89 cf             	mov    %rcx,%rdi
  401b78:	48 8b 98 20 04 00 00 	mov    0x420(%rax),%rbx
  401b7f:	b8 01 00 00 00       	mov    $0x1,%eax
  401b84:	0f 1f 40 00          	nopl   0x0(%rax)
  401b88:	48 63 d0             	movslq %eax,%rdx
  401b8b:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
  401b8e:	85 d2                	test   %edx,%edx
  401b90:	40 0f 94 c6          	sete   %sil
  401b94:	f6 c2 04             	test   $0x4,%dl
  401b97:	75 05                	jne    401b9e <pollthreads+0x3e>
  401b99:	40 84 f6             	test   %sil,%sil
  401b9c:	74 0d                	je     401bab <pollthreads+0x4b>
  401b9e:	49 63 08             	movslq (%r8),%rcx
  401ba1:	8d 69 01             	lea    0x1(%rcx),%ebp
  401ba4:	41 89 28             	mov    %ebp,(%r8)
  401ba7:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
  401bab:	83 e2 08             	and    $0x8,%edx
  401bae:	75 05                	jne    401bb5 <pollthreads+0x55>
  401bb0:	40 84 f6             	test   %sil,%sil
  401bb3:	74 1b                	je     401bd0 <pollthreads+0x70>
  401bb5:	48 63 17             	movslq (%rdi),%rdx
  401bb8:	8d 4a 01             	lea    0x1(%rdx),%ecx
  401bbb:	89 0f                	mov    %ecx,(%rdi)
  401bbd:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  401bc1:	83 c0 01             	add    $0x1,%eax
  401bc4:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401bc8:	7f be                	jg     401b88 <pollthreads+0x28>
  401bca:	31 c0                	xor    %eax,%eax
  401bcc:	5b                   	pop    %rbx
  401bcd:	5d                   	pop    %rbp
  401bce:	c3                   	ret
  401bcf:	90                   	nop
  401bd0:	83 c0 01             	add    $0x1,%eax
  401bd3:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401bd7:	7f af                	jg     401b88 <pollthreads+0x28>
  401bd9:	31 c0                	xor    %eax,%eax
  401bdb:	5b                   	pop    %rbx
  401bdc:	5d                   	pop    %rbp
  401bdd:	c3                   	ret
  401bde:	66 90                	xchg   %ax,%ax
  401be0:	31 c0                	xor    %eax,%eax
  401be2:	c3                   	ret
  401be3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401bee:	66 90                	xchg   %ax,%ax

0000000000401bf0 <findavailable>:
  401bf0:	49 89 fb             	mov    %rdi,%r11
  401bf3:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
  401bfa:	44 8b 02             	mov    (%rdx),%r8d
  401bfd:	48 83 c7 01          	add    $0x1,%rdi
  401c01:	48 85 ff             	test   %rdi,%rdi
  401c04:	7e 66                	jle    401c6c <findavailable+0x7c>
  401c06:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  401c0d:	31 c9                	xor    %ecx,%ecx
  401c0f:	45 31 c9             	xor    %r9d,%r9d
  401c12:	31 c0                	xor    %eax,%eax
  401c14:	eb 18                	jmp    401c2e <findavailable+0x3e>
  401c16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401c20:	83 c1 01             	add    $0x1,%ecx
  401c23:	48 63 c1             	movslq %ecx,%rax
  401c26:	49 89 c1             	mov    %rax,%r9
  401c29:	48 39 f8             	cmp    %rdi,%rax
  401c2c:	7d 3e                	jge    401c6c <findavailable+0x7c>
  401c2e:	48 c1 e0 05          	shl    $0x5,%rax
  401c32:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401c38:	75 e6                	jne    401c20 <findavailable+0x30>
  401c3a:	49 63 c0             	movslq %r8d,%rax
  401c3d:	41 83 c0 01          	add    $0x1,%r8d
  401c41:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
  401c45:	44 89 02             	mov    %r8d,(%rdx)
  401c48:	41 8b 43 68          	mov    0x68(%r11),%eax
  401c4c:	01 c0                	add    %eax,%eax
  401c4e:	41 39 c0             	cmp    %eax,%r8d
  401c51:	74 19                	je     401c6c <findavailable+0x7c>
  401c53:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  401c5a:	83 c1 01             	add    $0x1,%ecx
  401c5d:	48 63 c1             	movslq %ecx,%rax
  401c60:	48 83 c7 01          	add    $0x1,%rdi
  401c64:	49 89 c1             	mov    %rax,%r9
  401c67:	48 39 f8             	cmp    %rdi,%rax
  401c6a:	7c c2                	jl     401c2e <findavailable+0x3e>
  401c6c:	31 c0                	xor    %eax,%eax
  401c6e:	45 85 c0             	test   %r8d,%r8d
  401c71:	0f 94 c0             	sete   %al
  401c74:	c3                   	ret
  401c75:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401c80 <singlewriter3>:
  401c80:	c3                   	ret
  401c81:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401c8c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401c90 <singlewriter2>:
  401c90:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  401c96:	85 c0                	test   %eax,%eax
  401c98:	74 1e                	je     401cb8 <singlewriter2+0x28>
  401c9a:	41 54                	push   %r12
  401c9c:	99                   	cltd
  401c9d:	55                   	push   %rbp
  401c9e:	53                   	push   %rbx
  401c9f:	8b 77 68             	mov    0x68(%rdi),%esi
  401ca2:	48 89 fb             	mov    %rdi,%rbx
  401ca5:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401ca8:	f7 f9                	idiv   %ecx
  401caa:	85 d2                	test   %edx,%edx
  401cac:	74 12                	je     401cc0 <singlewriter2+0x30>
  401cae:	5b                   	pop    %rbx
  401caf:	5d                   	pop    %rbp
  401cb0:	41 5c                	pop    %r12
  401cb2:	c3                   	ret
  401cb3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401cb8:	c3                   	ret
  401cb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401cc0:	48 63 6f 64          	movslq 0x64(%rdi),%rbp
  401cc4:	48 c1 e5 0a          	shl    $0xa,%rbp
  401cc8:	48 03 6f 30          	add    0x30(%rdi),%rbp
  401ccc:	bf 04 00 00 00       	mov    $0x4,%edi
  401cd1:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401cd8:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401cdc:	49 c1 e4 04          	shl    $0x4,%r12
  401ce0:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
  401ce7:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401cec:	e8 6f f3 ff ff       	call   401060 <clock_gettime@plt>
  401cf1:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401cf7:	83 c0 01             	add    $0x1,%eax
  401cfa:	99                   	cltd
  401cfb:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
  401d01:	8b 43 64             	mov    0x64(%rbx),%eax
  401d04:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
  401d0a:	41 89 04 24          	mov    %eax,(%r12)
  401d0e:	48 8b 05 53 15 00 00 	mov    0x1553(%rip),%rax        # 403268 <_IO_stdin_used+0x268>
  401d15:	49 89 44 24 20       	mov    %rax,0x20(%r12)
  401d1a:	5b                   	pop    %rbx
  401d1b:	5d                   	pop    %rbp
  401d1c:	41 5c                	pop    %r12
  401d1e:	c3                   	ret
  401d1f:	90                   	nop

0000000000401d20 <singlewriter>:
  401d20:	41 55                	push   %r13
  401d22:	49 89 d5             	mov    %rdx,%r13
  401d25:	41 54                	push   %r12
  401d27:	49 89 cc             	mov    %rcx,%r12
  401d2a:	55                   	push   %rbp
  401d2b:	4d 89 e0             	mov    %r12,%r8
  401d2e:	48 89 fd             	mov    %rdi,%rbp
  401d31:	53                   	push   %rbx
  401d32:	48 89 f3             	mov    %rsi,%rbx
  401d35:	48 83 ec 28          	sub    $0x28,%rsp
  401d39:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
  401d3d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401d46:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401d4b:	31 c0                	xor    %eax,%eax
  401d4d:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  401d55:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  401d5b:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  401d63:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  401d6b:	83 c0 01             	add    $0x1,%eax
  401d6e:	99                   	cltd
  401d6f:	f7 7f 68             	idivl  0x68(%rdi)
  401d72:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  401d78:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401d7d:	4c 89 e9             	mov    %r13,%rcx
  401d80:	e8 6b fe ff ff       	call   401bf0 <findavailable>
  401d85:	83 f8 01             	cmp    $0x1,%eax
  401d88:	0f 84 3c 01 00 00    	je     401eca <singlewriter+0x1aa>
  401d8e:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401d93:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401d98:	4c 89 e2             	mov    %r12,%rdx
  401d9b:	4c 89 ee             	mov    %r13,%rsi
  401d9e:	48 89 ef             	mov    %rbp,%rdi
  401da1:	e8 ba fd ff ff       	call   401b60 <pollthreads>
  401da6:	4c 63 44 24 0c       	movslq 0xc(%rsp),%r8
  401dab:	45 85 c0             	test   %r8d,%r8d
  401dae:	0f 8e 3d 01 00 00    	jle    401ef1 <singlewriter+0x1d1>
  401db4:	44 8b 4c 24 14       	mov    0x14(%rsp),%r9d
  401db9:	31 c9                	xor    %ecx,%ecx
  401dbb:	eb 58                	jmp    401e15 <singlewriter+0xf5>
  401dbd:	0f 1f 00             	nopl   (%rax)
  401dc0:	48 8b 04 cb          	mov    (%rbx,%rcx,8),%rax
  401dc4:	49 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%rdx
  401dc9:	8d 71 01             	lea    0x1(%rcx),%esi
  401dcc:	48 83 c1 01          	add    $0x1,%rcx
  401dd0:	48 c1 e0 05          	shl    $0x5,%rax
  401dd4:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
  401ddb:	48 89 d7             	mov    %rdx,%rdi
  401dde:	48 c1 e2 0a          	shl    $0xa,%rdx
  401de2:	66 0f 6e 00          	movd   (%rax),%xmm0
  401de6:	66 0f 6e 48 08       	movd   0x8(%rax),%xmm1
  401deb:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
  401df2:	48 03 55 30          	add    0x30(%rbp),%rdx
  401df6:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
  401dfa:	48 89 82 a8 00 00 00 	mov    %rax,0xa8(%rdx)
  401e01:	89 78 14             	mov    %edi,0x14(%rax)
  401e04:	83 8a c8 00 00 00 10 	orl    $0x10,0xc8(%rdx)
  401e0b:	66 0f d6 42 14       	movq   %xmm0,0x14(%rdx)
  401e10:	49 39 c8             	cmp    %rcx,%r8
  401e13:	74 07                	je     401e1c <singlewriter+0xfc>
  401e15:	89 ce                	mov    %ecx,%esi
  401e17:	4c 39 c9             	cmp    %r9,%rcx
  401e1a:	75 a4                	jne    401dc0 <singlewriter+0xa0>
  401e1c:	44 8b 4c 24 10       	mov    0x10(%rsp),%r9d
  401e21:	45 85 c9             	test   %r9d,%r9d
  401e24:	7e 68                	jle    401e8e <singlewriter+0x16e>
  401e26:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
  401e2b:	41 01 f1             	add    %esi,%r9d
  401e2e:	eb 59                	jmp    401e89 <singlewriter+0x169>
  401e30:	8d 7e 01             	lea    0x1(%rsi),%edi
  401e33:	48 63 f6             	movslq %esi,%rsi
  401e36:	49 63 14 24          	movslq (%r12),%rdx
  401e3a:	49 83 c4 04          	add    $0x4,%r12
  401e3e:	48 8b 04 f3          	mov    (%rbx,%rsi,8),%rax
  401e42:	48 89 d1             	mov    %rdx,%rcx
  401e45:	48 c1 e2 0a          	shl    $0xa,%rdx
  401e49:	48 03 55 30          	add    0x30(%rbp),%rdx
  401e4d:	48 c1 e0 05          	shl    $0x5,%rax
  401e51:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
  401e58:	66 0f 6e 00          	movd   (%rax),%xmm0
  401e5c:	66 0f 6e 50 08       	movd   0x8(%rax),%xmm2
  401e61:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
  401e68:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
  401e6f:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
  401e73:	89 48 14             	mov    %ecx,0x14(%rax)
  401e76:	83 8a c8 00 00 00 20 	orl    $0x20,0xc8(%rdx)
  401e7d:	66 0f d6 42 40       	movq   %xmm0,0x40(%rdx)
  401e82:	44 39 cf             	cmp    %r9d,%edi
  401e85:	74 07                	je     401e8e <singlewriter+0x16e>
  401e87:	89 fe                	mov    %edi,%esi
  401e89:	41 39 f0             	cmp    %esi,%r8d
  401e8c:	75 a2                	jne    401e30 <singlewriter+0x110>
  401e8e:	8b 7d 68             	mov    0x68(%rbp),%edi
  401e91:	85 ff                	test   %edi,%edi
  401e93:	7e 33                	jle    401ec8 <singlewriter+0x1a8>
  401e95:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401e99:	31 d2                	xor    %edx,%edx
  401e9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401ea0:	48 63 ca             	movslq %edx,%rcx
  401ea3:	48 89 c8             	mov    %rcx,%rax
  401ea6:	48 c1 e0 0a          	shl    $0xa,%rax
  401eaa:	4c 01 c0             	add    %r8,%rax
  401ead:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401eb3:	85 f6                	test   %esi,%esi
  401eb5:	74 31                	je     401ee8 <singlewriter+0x1c8>
  401eb7:	48 8b 40 20          	mov    0x20(%rax),%rax
  401ebb:	83 c2 01             	add    $0x1,%edx
  401ebe:	89 34 88             	mov    %esi,(%rax,%rcx,4)
  401ec1:	8b 7d 68             	mov    0x68(%rbp),%edi
  401ec4:	39 fa                	cmp    %edi,%edx
  401ec6:	7c d8                	jl     401ea0 <singlewriter+0x180>
  401ec8:	31 c0                	xor    %eax,%eax
  401eca:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401ecf:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401ed8:	75 1e                	jne    401ef8 <singlewriter+0x1d8>
  401eda:	48 83 c4 28          	add    $0x28,%rsp
  401ede:	5b                   	pop    %rbx
  401edf:	5d                   	pop    %rbp
  401ee0:	41 5c                	pop    %r12
  401ee2:	41 5d                	pop    %r13
  401ee4:	c3                   	ret
  401ee5:	0f 1f 00             	nopl   (%rax)
  401ee8:	83 c2 01             	add    $0x1,%edx
  401eeb:	39 fa                	cmp    %edi,%edx
  401eed:	7c b1                	jl     401ea0 <singlewriter+0x180>
  401eef:	eb d7                	jmp    401ec8 <singlewriter+0x1a8>
  401ef1:	31 f6                	xor    %esi,%esi
  401ef3:	e9 24 ff ff ff       	jmp    401e1c <singlewriter+0xfc>
  401ef8:	e8 83 f1 ff ff       	call   401080 <__stack_chk_fail@plt>
  401efd:	0f 1f 00             	nopl   (%rax)

0000000000401f00 <threadwork>:
  401f00:	41 57                	push   %r15
  401f02:	41 56                	push   %r14
  401f04:	41 55                	push   %r13
  401f06:	41 54                	push   %r12
  401f08:	55                   	push   %rbp
  401f09:	53                   	push   %rbx
  401f0a:	48 89 fb             	mov    %rdi,%rbx
  401f0d:	bf 04 00 00 00       	mov    $0x4,%edi
  401f12:	48 83 ec 28          	sub    $0x28,%rsp
  401f16:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401f1f:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401f24:	31 c0                	xor    %eax,%eax
  401f26:	48 89 e6             	mov    %rsp,%rsi
  401f29:	e8 32 f1 ff ff       	call   401060 <clock_gettime@plt>
  401f2e:	83 7b 5c 02          	cmpl   $0x2,0x5c(%rbx)
  401f32:	0f 84 d8 02 00 00    	je     402210 <threadwork+0x310>
  401f38:	48 8b 6b 28          	mov    0x28(%rbx),%rbp
  401f3c:	8b 83 8c 03 00 00    	mov    0x38c(%rbx),%eax
  401f42:	48 ba 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rdx
  401f4c:	48 8b bd 80 03 00 00 	mov    0x380(%rbp),%rdi
  401f53:	c1 e0 07             	shl    $0x7,%eax
  401f56:	48 98                	cltq
  401f58:	48 8b 0c c7          	mov    (%rdi,%rax,8),%rcx
  401f5c:	48 89 c8             	mov    %rcx,%rax
  401f5f:	48 c1 f9 3f          	sar    $0x3f,%rcx
  401f63:	48 f7 ea             	imul   %rdx
  401f66:	48 63 83 88 03 00 00 	movslq 0x388(%rbx),%rax
  401f6d:	48 d1 fa             	sar    %rdx
  401f70:	48 29 ca             	sub    %rcx,%rdx
  401f73:	49 89 d4             	mov    %rdx,%r12
  401f76:	48 39 c2             	cmp    %rax,%rdx
  401f79:	74 77                	je     401ff2 <threadwork+0xf2>
  401f7b:	48 63 6b 64          	movslq 0x64(%rbx),%rbp
  401f7f:	bf 04 00 00 00       	mov    $0x4,%edi
  401f84:	c7 83 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rbx)
  401f8e:	48 c1 e5 0a          	shl    $0xa,%rbp
  401f92:	48 03 6b 30          	add    0x30(%rbx),%rbp
  401f96:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401f9d:	4c 8d 2c 40          	lea    (%rax,%rax,2),%r13
  401fa1:	49 c1 e5 04          	shl    $0x4,%r13
  401fa5:	4c 03 ad 18 03 00 00 	add    0x318(%rbp),%r13
  401fac:	49 8d 75 08          	lea    0x8(%r13),%rsi
  401fb0:	e8 ab f0 ff ff       	call   401060 <clock_gettime@plt>
  401fb5:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401fbb:	83 c0 01             	add    $0x1,%eax
  401fbe:	99                   	cltd
  401fbf:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
  401fc5:	8b 43 64             	mov    0x64(%rbx),%eax
  401fc8:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
  401fce:	48 8b 6b 28          	mov    0x28(%rbx),%rbp
  401fd2:	41 89 45 00          	mov    %eax,0x0(%r13)
  401fd6:	8b 83 8c 03 00 00    	mov    0x38c(%rbx),%eax
  401fdc:	48 8b bd 80 03 00 00 	mov    0x380(%rbp),%rdi
  401fe3:	41 89 45 2c          	mov    %eax,0x2c(%r13)
  401fe7:	48 8b 05 7a 12 00 00 	mov    0x127a(%rip),%rax        # 403268 <_IO_stdin_used+0x268>
  401fee:	49 89 45 20          	mov    %rax,0x20(%r13)
  401ff2:	8b b3 90 03 00 00    	mov    0x390(%rbx),%esi
  401ff8:	4c 8b 8b 48 03 00 00 	mov    0x348(%rbx),%r9
  401fff:	44 89 a3 88 03 00 00 	mov    %r12d,0x388(%rbx)
  402006:	89 f0                	mov    %esi,%eax
  402008:	c1 e0 07             	shl    $0x7,%eax
  40200b:	48 98                	cltq
  40200d:	48 8b 0c c7          	mov    (%rdi,%rax,8),%rcx
  402011:	48 63 c6             	movslq %esi,%rax
  402014:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  402018:	41 8b 14 91          	mov    (%r9,%rdx,4),%edx
  40201c:	48 85 c9             	test   %rcx,%rcx
  40201f:	74 0c                	je     40202d <threadwork+0x12d>
  402021:	48 63 fa             	movslq %edx,%rdi
  402024:	48 39 cf             	cmp    %rcx,%rdi
  402027:	0f 8d bb 01 00 00    	jge    4021e8 <threadwork+0x2e8>
  40202d:	44 8b 53 68          	mov    0x68(%rbx),%r10d
  402031:	41 83 ea 01          	sub    $0x1,%r10d
  402035:	45 85 d2             	test   %r10d,%r10d
  402038:	0f 8e aa 01 00 00    	jle    4021e8 <threadwork+0x2e8>
  40203e:	45 31 db             	xor    %r11d,%r11d
  402041:	eb 21                	jmp    402064 <threadwork+0x164>
  402043:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  402048:	41 83 c3 01          	add    $0x1,%r11d
  40204c:	45 39 da             	cmp    %r11d,%r10d
  40204f:	0f 8e 93 01 00 00    	jle    4021e8 <threadwork+0x2e8>
  402055:	48 63 c6             	movslq %esi,%rax
  402058:	48 8b 6b 28          	mov    0x28(%rbx),%rbp
  40205c:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  402060:	41 8b 14 91          	mov    (%r9,%rdx,4),%edx
  402064:	4c 8d 04 40          	lea    (%rax,%rax,2),%r8
  402068:	48 63 c2             	movslq %edx,%rax
  40206b:	c1 fa 1f             	sar    $0x1f,%edx
  40206e:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
  402073:	48 69 c0 67 66 66 66 	imul   $0x66666667,%rax,%rax
  40207a:	49 c1 e0 02          	shl    $0x2,%r8
  40207e:	66 0f 6f 04 24       	movdqa (%rsp),%xmm0
  402083:	4b 8d 3c 01          	lea    (%r9,%r8,1),%rdi
  402087:	8b 4f 04             	mov    0x4(%rdi),%ecx
  40208a:	48 c1 f8 21          	sar    $0x21,%rax
  40208e:	29 d0                	sub    %edx,%eax
  402090:	41 89 cd             	mov    %ecx,%r13d
  402093:	83 e8 01             	sub    $0x1,%eax
  402096:	48 63 d0             	movslq %eax,%rdx
  402099:	41 89 c4             	mov    %eax,%r12d
  40209c:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  4020a3:	41 c1 fc 1f          	sar    $0x1f,%r12d
  4020a7:	48 c1 ea 20          	shr    $0x20,%rdx
  4020ab:	01 c2                	add    %eax,%edx
  4020ad:	c1 fa 07             	sar    $0x7,%edx
  4020b0:	44 29 e2             	sub    %r12d,%edx
  4020b3:	41 89 d4             	mov    %edx,%r12d
  4020b6:	41 c1 e4 08          	shl    $0x8,%r12d
  4020ba:	41 29 d4             	sub    %edx,%r12d
  4020bd:	31 d2                	xor    %edx,%edx
  4020bf:	44 29 e0             	sub    %r12d,%eax
  4020c2:	41 89 f4             	mov    %esi,%r12d
  4020c5:	48 98                	cltq
  4020c7:	48 85 c0             	test   %rax,%rax
  4020ca:	48 0f 48 c2          	cmovs  %rdx,%rax
  4020ce:	48 63 d1             	movslq %ecx,%rdx
  4020d1:	41 c1 fd 1f          	sar    $0x1f,%r13d
  4020d5:	48 69 d2 81 80 80 80 	imul   $0xffffffff80808081,%rdx,%rdx
  4020dc:	41 c1 e4 18          	shl    $0x18,%r12d
  4020e0:	48 c1 e0 10          	shl    $0x10,%rax
  4020e4:	48 c1 ea 20          	shr    $0x20,%rdx
  4020e8:	01 ca                	add    %ecx,%edx
  4020ea:	c1 fa 07             	sar    $0x7,%edx
  4020ed:	44 29 ea             	sub    %r13d,%edx
  4020f0:	41 89 d5             	mov    %edx,%r13d
  4020f3:	41 c1 e5 08          	shl    $0x8,%r13d
  4020f7:	41 29 d5             	sub    %edx,%r13d
  4020fa:	89 ca                	mov    %ecx,%edx
  4020fc:	44 29 ea             	sub    %r13d,%edx
  4020ff:	4c 63 6b 64          	movslq 0x64(%rbx),%r13
  402103:	41 09 d4             	or     %edx,%r12d
  402106:	4d 89 ef             	mov    %r13,%r15
  402109:	49 c1 e5 0a          	shl    $0xa,%r13
  40210d:	4c 03 6b 30          	add    0x30(%rbx),%r13
  402111:	4d 63 e4             	movslq %r12d,%r12
  402114:	49 63 95 24 03 00 00 	movslq 0x324(%r13),%rdx
  40211b:	49 09 c4             	or     %rax,%r12
  40211e:	48 89 d0             	mov    %rdx,%rax
  402121:	4c 8d 34 52          	lea    (%rdx,%rdx,2),%r14
  402125:	83 c0 01             	add    $0x1,%eax
  402128:	49 c1 e6 04          	shl    $0x4,%r14
  40212c:	4d 03 b5 18 03 00 00 	add    0x318(%r13),%r14
  402133:	99                   	cltd
  402134:	41 0f 11 46 08       	movups %xmm0,0x8(%r14)
  402139:	41 f7 bd 20 03 00 00 	idivl  0x320(%r13)
  402140:	41 89 95 24 03 00 00 	mov    %edx,0x324(%r13)
  402147:	4d 89 66 18          	mov    %r12,0x18(%r14)
  40214b:	4c 03 65 70          	add    0x70(%rbp),%r12
  40214f:	45 89 3e             	mov    %r15d,(%r14)
  402152:	41 c7 46 24 01 00 00 00 	movl   $0x1,0x24(%r14)
  40215a:	41 80 3c 24 ff       	cmpb   $0xff,(%r12)
  40215f:	74 29                	je     40218a <threadwork+0x28a>
  402161:	48 83 83 98 03 00 00 01 	addq   $0x1,0x398(%rbx)
  402169:	41 c6 04 24 ff       	movb   $0xff,(%r12)
  40216e:	4c 8b 8b 48 03 00 00 	mov    0x348(%rbx),%r9
  402175:	44 8b 53 68          	mov    0x68(%rbx),%r10d
  402179:	8b b3 90 03 00 00    	mov    0x390(%rbx),%esi
  40217f:	4b 8d 3c 01          	lea    (%r9,%r8,1),%rdi
  402183:	8b 4f 04             	mov    0x4(%rdi),%ecx
  402186:	41 83 ea 01          	sub    $0x1,%r10d
  40218a:	83 f9 04             	cmp    $0x4,%ecx
  40218d:	7f 09                	jg     402198 <threadwork+0x298>
  40218f:	83 c1 01             	add    $0x1,%ecx
  402192:	83 07 01             	addl   $0x1,(%rdi)
  402195:	89 4f 04             	mov    %ecx,0x4(%rdi)
  402198:	83 f9 05             	cmp    $0x5,%ecx
  40219b:	75 10                	jne    4021ad <threadwork+0x2ad>
  40219d:	83 c6 01             	add    $0x1,%esi
  4021a0:	89 b3 90 03 00 00    	mov    %esi,0x390(%rbx)
  4021a6:	c7 47 04 00 00 00 00 	movl   $0x0,0x4(%rdi)
  4021ad:	39 b3 8c 03 00 00    	cmp    %esi,0x38c(%rbx)
  4021b3:	75 09                	jne    4021be <threadwork+0x2be>
  4021b5:	83 c6 01             	add    $0x1,%esi
  4021b8:	89 b3 90 03 00 00    	mov    %esi,0x390(%rbx)
  4021be:	83 fe 05             	cmp    $0x5,%esi
  4021c1:	0f 85 81 fe ff ff    	jne    402048 <threadwork+0x148>
  4021c7:	c7 83 90 03 00 00 01 00 00 00 	movl   $0x1,0x390(%rbx)
  4021d1:	41 83 c3 01          	add    $0x1,%r11d
  4021d5:	45 39 da             	cmp    %r11d,%r10d
  4021d8:	7e 0e                	jle    4021e8 <threadwork+0x2e8>
  4021da:	be 01 00 00 00       	mov    $0x1,%esi
  4021df:	e9 71 fe ff ff       	jmp    402055 <threadwork+0x155>
  4021e4:	0f 1f 40 00          	nopl   0x0(%rax)
  4021e8:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  4021ed:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4021f6:	0f 85 83 01 00 00    	jne    40237f <threadwork+0x47f>
  4021fc:	48 83 c4 28          	add    $0x28,%rsp
  402200:	31 c0                	xor    %eax,%eax
  402202:	5b                   	pop    %rbx
  402203:	5d                   	pop    %rbp
  402204:	41 5c                	pop    %r12
  402206:	41 5d                	pop    %r13
  402208:	41 5e                	pop    %r14
  40220a:	41 5f                	pop    %r15
  40220c:	c3                   	ret
  40220d:	0f 1f 00             	nopl   (%rax)
  402210:	8b 43 68             	mov    0x68(%rbx),%eax
  402213:	85 c0                	test   %eax,%eax
  402215:	0f 8e 43 01 00 00    	jle    40235e <threadwork+0x45e>
  40221b:	8b 8b 80 01 00 00    	mov    0x180(%rbx),%ecx
  402221:	31 ff                	xor    %edi,%edi
  402223:	49 ba 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r10
  40222d:	49 b9 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%r9
  402237:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  402240:	44 8b 9b 8c 03 00 00 	mov    0x38c(%rbx),%r11d
  402247:	4c 8b 43 28          	mov    0x28(%rbx),%r8
  40224b:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
  402250:	44 89 d8             	mov    %r11d,%eax
  402253:	49 8b 90 80 03 00 00 	mov    0x380(%r8),%rdx
  40225a:	41 c1 e3 18          	shl    $0x18,%r11d
  40225e:	c1 e0 07             	shl    $0x7,%eax
  402261:	48 98                	cltq
  402263:	48 8b 34 c2          	mov    (%rdx,%rax,8),%rsi
  402267:	48 89 f0             	mov    %rsi,%rax
  40226a:	48 c1 fe 3f          	sar    $0x3f,%rsi
  40226e:	49 f7 ea             	imul   %r10
  402271:	48 89 d0             	mov    %rdx,%rax
  402274:	48 d1 f8             	sar    %rax
  402277:	48 29 f0             	sub    %rsi,%rax
  40227a:	48 89 c5             	mov    %rax,%rbp
  40227d:	49 f7 e9             	imul   %r9
  402280:	48 89 e8             	mov    %rbp,%rax
  402283:	48 c1 f8 3f          	sar    $0x3f,%rax
  402287:	48 8d 34 2a          	lea    (%rdx,%rbp,1),%rsi
  40228b:	48 c1 fe 07          	sar    $0x7,%rsi
  40228f:	48 29 c6             	sub    %rax,%rsi
  402292:	48 89 e8             	mov    %rbp,%rax
  402295:	48 63 6b 64          	movslq 0x64(%rbx),%rbp
  402299:	48 89 f2             	mov    %rsi,%rdx
  40229c:	48 c1 e2 08          	shl    $0x8,%rdx
  4022a0:	48 29 f2             	sub    %rsi,%rdx
  4022a3:	48 63 f1             	movslq %ecx,%rsi
  4022a6:	48 69 f6 81 80 80 80 	imul   $0xffffffff80808081,%rsi,%rsi
  4022ad:	48 29 d0             	sub    %rdx,%rax
  4022b0:	89 ca                	mov    %ecx,%edx
  4022b2:	c1 fa 1f             	sar    $0x1f,%edx
  4022b5:	c1 e0 10             	shl    $0x10,%eax
  4022b8:	48 c1 ee 20          	shr    $0x20,%rsi
  4022bc:	01 ce                	add    %ecx,%esi
  4022be:	c1 fe 07             	sar    $0x7,%esi
  4022c1:	29 d6                	sub    %edx,%esi
  4022c3:	89 f2                	mov    %esi,%edx
  4022c5:	c1 e2 08             	shl    $0x8,%edx
  4022c8:	29 f2                	sub    %esi,%edx
  4022ca:	29 d1                	sub    %edx,%ecx
  4022cc:	44 09 d9             	or     %r11d,%ecx
  4022cf:	49 89 eb             	mov    %rbp,%r11
  4022d2:	48 c1 e5 0a          	shl    $0xa,%rbp
  4022d6:	48 03 6b 30          	add    0x30(%rbx),%rbp
  4022da:	48 63 95 24 03 00 00 	movslq 0x324(%rbp),%rdx
  4022e1:	09 c1                	or     %eax,%ecx
  4022e3:	48 63 c9             	movslq %ecx,%rcx
  4022e6:	48 89 d0             	mov    %rdx,%rax
  4022e9:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
  4022ed:	83 c0 01             	add    $0x1,%eax
  4022f0:	48 c1 e6 04          	shl    $0x4,%rsi
  4022f4:	48 03 b5 18 03 00 00 	add    0x318(%rbp),%rsi
  4022fb:	99                   	cltd
  4022fc:	0f 11 4e 08          	movups %xmm1,0x8(%rsi)
  402300:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
  402306:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
  40230c:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
  402310:	49 03 48 70          	add    0x70(%r8),%rcx
  402314:	44 89 1e             	mov    %r11d,(%rsi)
  402317:	c7 46 24 01 00 00 00 	movl   $0x1,0x24(%rsi)
  40231e:	80 39 ff             	cmpb   $0xff,(%rcx)
  402321:	74 05                	je     402328 <threadwork+0x428>
  402323:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
  402328:	44 88 19             	mov    %r11b,(%rcx)
  40232b:	8b 83 80 01 00 00    	mov    0x180(%rbx),%eax
  402331:	83 c7 01             	add    $0x1,%edi
  402334:	83 c0 01             	add    $0x1,%eax
  402337:	48 63 c8             	movslq %eax,%rcx
  40233a:	99                   	cltd
  40233b:	48 69 c9 67 66 66 66 	imul   $0x66666667,%rcx,%rcx
  402342:	48 c1 f9 21          	sar    $0x21,%rcx
  402346:	29 d1                	sub    %edx,%ecx
  402348:	8d 14 89             	lea    (%rcx,%rcx,4),%edx
  40234b:	29 d0                	sub    %edx,%eax
  40234d:	89 83 80 01 00 00    	mov    %eax,0x180(%rbx)
  402353:	89 c1                	mov    %eax,%ecx
  402355:	39 7b 68             	cmp    %edi,0x68(%rbx)
  402358:	0f 8f e2 fe ff ff    	jg     402240 <threadwork+0x340>
  40235e:	48 8b 53 28          	mov    0x28(%rbx),%rdx
  402362:	8b 83 8c 03 00 00    	mov    0x38c(%rbx),%eax
  402368:	48 8b 92 80 03 00 00 	mov    0x380(%rdx),%rdx
  40236f:	c1 e0 07             	shl    $0x7,%eax
  402372:	48 98                	cltq
  402374:	f0 48 83 04 c2 01    	lock addq $0x1,(%rdx,%rax,8)
  40237a:	e9 b9 fb ff ff       	jmp    401f38 <threadwork+0x38>
  40237f:	e8 fc ec ff ff       	call   401080 <__stack_chk_fail@plt>
  402384:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40238f:	90                   	nop

0000000000402390 <work>:
  402390:	53                   	push   %rbx
  402391:	8b 57 64             	mov    0x64(%rdi),%edx
  402394:	48 89 fb             	mov    %rdi,%rbx
  402397:	48 8d 35 66 0c 00 00 	lea    0xc66(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  40239e:	bf 01 00 00 00       	mov    $0x1,%edi
  4023a3:	31 c0                	xor    %eax,%eax
  4023a5:	e8 26 ed ff ff       	call   4010d0 <__printf_chk@plt>
  4023aa:	8b 53 5c             	mov    0x5c(%rbx),%edx
  4023ad:	85 d2                	test   %edx,%edx
  4023af:	7e 16                	jle    4023c7 <work+0x37>
  4023b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  4023b8:	48 89 df             	mov    %rbx,%rdi
  4023bb:	e8 40 fb ff ff       	call   401f00 <threadwork>
  4023c0:	8b 43 5c             	mov    0x5c(%rbx),%eax
  4023c3:	85 c0                	test   %eax,%eax
  4023c5:	7f f1                	jg     4023b8 <work+0x28>
  4023c7:	8b 53 64             	mov    0x64(%rbx),%edx
  4023ca:	48 8d 35 46 0c 00 00 	lea    0xc46(%rip),%rsi        # 403017 <_IO_stdin_used+0x17>
  4023d1:	bf 01 00 00 00       	mov    $0x1,%edi
  4023d6:	31 c0                	xor    %eax,%eax
  4023d8:	e8 f3 ec ff ff       	call   4010d0 <__printf_chk@plt>
  4023dd:	5b                   	pop    %rbx
  4023de:	c3                   	ret
  4023df:	90                   	nop

00000000004023e0 <work2>:
  4023e0:	eb 0b                	jmp    4023ed <work2+0xd>
  4023e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  4023e8:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  4023ed:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  4023f1:	74 f5                	je     4023e8 <work2+0x8>
  4023f3:	c3                   	ret

Disassembly of section .fini:

00000000004023f4 <_fini>:
  4023f4:	f3 0f 1e fa          	endbr64
  4023f8:	48 83 ec 08          	sub    $0x8,%rsp
  4023fc:	48 83 c4 08          	add    $0x8,%rsp
  402400:	c3                   	ret
