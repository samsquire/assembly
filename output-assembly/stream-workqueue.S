
stream-workqueue:     file format elf64-x86-64


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
  401020:	ff 35 4a 3f 00 00    	push   0x3f4a(%rip)        # 404f70 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 4c 3f 00 00    	jmp    *0x3f4c(%rip)        # 404f78 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <__snprintf_chk@plt>:
  401030:	ff 25 4a 3f 00 00    	jmp    *0x3f4a(%rip)        # 404f80 <__snprintf_chk@GLIBC_2.3.4>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <pthread_setaffinity_np@plt>:
  401040:	ff 25 42 3f 00 00    	jmp    *0x3f42(%rip)        # 404f88 <pthread_setaffinity_np@GLIBC_2.34>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <puts@plt>:
  401050:	ff 25 3a 3f 00 00    	jmp    *0x3f3a(%rip)        # 404f90 <puts@GLIBC_2.2.5>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <clock_gettime@plt>:
  401060:	ff 25 32 3f 00 00    	jmp    *0x3f32(%rip)        # 404f98 <clock_gettime@GLIBC_2.17>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <__stack_chk_fail@plt>:
  401070:	ff 25 2a 3f 00 00    	jmp    *0x3f2a(%rip)        # 404fa0 <__stack_chk_fail@GLIBC_2.4>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <nanosleep@plt>:
  401080:	ff 25 22 3f 00 00    	jmp    *0x3f22(%rip)        # 404fa8 <nanosleep@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <fputs@plt>:
  401090:	ff 25 1a 3f 00 00    	jmp    *0x3f1a(%rip)        # 404fb0 <fputs@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <memset@plt>:
  4010a0:	ff 25 12 3f 00 00    	jmp    *0x3f12(%rip)        # 404fb8 <memset@GLIBC_2.2.5>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <calloc@plt>:
  4010b0:	ff 25 0a 3f 00 00    	jmp    *0x3f0a(%rip)        # 404fc0 <calloc@GLIBC_2.2.5>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <__printf_chk@plt>:
  4010c0:	ff 25 02 3f 00 00    	jmp    *0x3f02(%rip)        # 404fc8 <__printf_chk@GLIBC_2.3.4>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010d0 <pthread_create@plt>:
  4010d0:	ff 25 fa 3e 00 00    	jmp    *0x3efa(%rip)        # 404fd0 <pthread_create@GLIBC_2.34>
  4010d6:	68 0a 00 00 00       	push   $0xa
  4010db:	e9 40 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010e0 <fopen@plt>:
  4010e0:	ff 25 f2 3e 00 00    	jmp    *0x3ef2(%rip)        # 404fd8 <fopen@GLIBC_2.2.5>
  4010e6:	68 0b 00 00 00       	push   $0xb
  4010eb:	e9 30 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010f0 <posix_memalign@plt>:
  4010f0:	ff 25 ea 3e 00 00    	jmp    *0x3eea(%rip)        # 404fe0 <posix_memalign@GLIBC_2.2.5>
  4010f6:	68 0c 00 00 00       	push   $0xc
  4010fb:	e9 20 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401100 <pthread_join@plt>:
  401100:	ff 25 e2 3e 00 00    	jmp    *0x3ee2(%rip)        # 404fe8 <pthread_join@GLIBC_2.34>
  401106:	68 0d 00 00 00       	push   $0xd
  40110b:	e9 10 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

0000000000401110 <main>:
  401110:	41 57                	push   %r15
  401112:	ba 08 00 00 00       	mov    $0x8,%edx
  401117:	48 8d 35 09 1f 00 00 	lea    0x1f09(%rip),%rsi        # 403027 <_IO_stdin_used+0x27>
  40111e:	bf 01 00 00 00       	mov    $0x1,%edi
  401123:	41 56                	push   %r14
  401125:	4c 8d 3d 7c 20 00 00 	lea    0x207c(%rip),%r15        # 4031a8 <_IO_stdin_used+0x1a8>
  40112c:	41 55                	push   %r13
  40112e:	41 54                	push   %r12
  401130:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
  401136:	55                   	push   %rbp
  401137:	53                   	push   %rbx
  401138:	48 83 ec 68          	sub    $0x68,%rsp
  40113c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401145:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  40114a:	31 c0                	xor    %eax,%eax
  40114c:	e8 6f ff ff ff       	call   4010c0 <__printf_chk@plt>
  401151:	ba 04 00 00 00       	mov    $0x4,%edx
  401156:	48 8d 35 dc 1e 00 00 	lea    0x1edc(%rip),%rsi        # 403039 <_IO_stdin_used+0x39>
  40115d:	31 c0                	xor    %eax,%eax
  40115f:	bf 01 00 00 00       	mov    $0x1,%edi
  401164:	e8 57 ff ff ff       	call   4010c0 <__printf_chk@plt>
  401169:	ba 20 00 00 00       	mov    $0x20,%edx
  40116e:	48 8d 35 c0 1e 00 00 	lea    0x1ec0(%rip),%rsi        # 403035 <_IO_stdin_used+0x35>
  401175:	31 c0                	xor    %eax,%eax
  401177:	bf 01 00 00 00       	mov    $0x1,%edi
  40117c:	e8 3f ff ff ff       	call   4010c0 <__printf_chk@plt>
  401181:	ba 0c 00 00 00       	mov    $0xc,%edx
  401186:	48 8d 35 bb 1e 00 00 	lea    0x1ebb(%rip),%rsi        # 403048 <_IO_stdin_used+0x48>
  40118d:	31 c0                	xor    %eax,%eax
  40118f:	bf 01 00 00 00       	mov    $0x1,%edi
  401194:	e8 27 ff ff ff       	call   4010c0 <__printf_chk@plt>
  401199:	be 08 00 00 00       	mov    $0x8,%esi
  40119e:	bf 0c 00 00 00       	mov    $0xc,%edi
  4011a3:	e8 08 ff ff ff       	call   4010b0 <calloc@plt>
  4011a8:	be 38 00 00 00       	mov    $0x38,%esi
  4011ad:	bf 0c 00 00 00       	mov    $0xc,%edi
  4011b2:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  4011b7:	e8 f4 fe ff ff       	call   4010b0 <calloc@plt>
  4011bc:	be 00 30 00 00       	mov    $0x3000,%esi
  4011c1:	bf 01 00 00 00       	mov    $0x1,%edi
  4011c6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  4011cb:	e8 e0 fe ff ff       	call   4010b0 <calloc@plt>
  4011d0:	be 01 00 00 00       	mov    $0x1,%esi
  4011d5:	4c 89 e7             	mov    %r12,%rdi
  4011d8:	48 89 c3             	mov    %rax,%rbx
  4011db:	e8 d0 fe ff ff       	call   4010b0 <calloc@plt>
  4011e0:	4c 89 e2             	mov    %r12,%rdx
  4011e3:	be ff ff ff ff       	mov    $0xffffffff,%esi
  4011e8:	48 89 c7             	mov    %rax,%rdi
  4011eb:	49 89 c6             	mov    %rax,%r14
  4011ee:	e8 ad fe ff ff       	call   4010a0 <memset@plt>
  4011f3:	4c 89 e2             	mov    %r12,%rdx
  4011f6:	bf 01 00 00 00       	mov    $0x1,%edi
  4011fb:	31 c0                	xor    %eax,%eax
  4011fd:	48 8d 35 59 1e 00 00 	lea    0x1e59(%rip),%rsi        # 40305d <_IO_stdin_used+0x5d>
  401204:	e8 b7 fe ff ff       	call   4010c0 <__printf_chk@plt>
  401209:	be 20 00 00 00       	mov    $0x20,%esi
  40120e:	bf 64 00 00 00       	mov    $0x64,%edi
  401213:	e8 98 fe ff ff       	call   4010b0 <calloc@plt>
  401218:	31 d2                	xor    %edx,%edx
  40121a:	bf 01 00 00 00       	mov    $0x1,%edi
  40121f:	48 8d 35 48 1e 00 00 	lea    0x1e48(%rip),%rsi        # 40306e <_IO_stdin_used+0x6e>
  401226:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  40122b:	31 c0                	xor    %eax,%eax
  40122d:	e8 8e fe ff ff       	call   4010c0 <__printf_chk@plt>
  401232:	4c 89 e2             	mov    %r12,%rdx
  401235:	bf 01 00 00 00       	mov    $0x1,%edi
  40123a:	31 c0                	xor    %eax,%eax
  40123c:	48 8d 35 37 1e 00 00 	lea    0x1e37(%rip),%rsi        # 40307a <_IO_stdin_used+0x7a>
  401243:	e8 78 fe ff ff       	call   4010c0 <__printf_chk@plt>
  401248:	be 04 00 00 00       	mov    $0x4,%esi
  40124d:	bf 0c 00 00 00       	mov    $0xc,%edi
  401252:	e8 59 fe ff ff       	call   4010b0 <calloc@plt>
  401257:	48 8d 7c 24 28       	lea    0x28(%rsp),%rdi
  40125c:	ba 00 02 00 00       	mov    $0x200,%edx
  401261:	be 80 00 00 00       	mov    $0x80,%esi
  401266:	48 89 c5             	mov    %rax,%rbp
  401269:	e8 82 fe ff ff       	call   4010f0 <posix_memalign@plt>
  40126e:	4c 89 73 70          	mov    %r14,0x70(%rbx)
  401272:	49 89 de             	mov    %rbx,%r14
  401275:	85 c0                	test   %eax,%eax
  401277:	b8 00 00 00 00       	mov    $0x0,%eax
  40127c:	48 0f 44 44 24 28    	cmove  0x28(%rsp),%rax
  401282:	45 31 ed             	xor    %r13d,%r13d
  401285:	48 89 04 24          	mov    %rax,(%rsp)
  401289:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401290:	be 80 00 00 00       	mov    $0x80,%esi
  401295:	bf 01 00 00 00       	mov    $0x1,%edi
  40129a:	49 81 c6 00 04 00 00 	add    $0x400,%r14
  4012a1:	e8 0a fe ff ff       	call   4010b0 <calloc@plt>
  4012a6:	41 8d 4d 01          	lea    0x1(%r13),%ecx
  4012aa:	be 01 00 00 00       	mov    $0x1,%esi
  4012af:	44 89 ea             	mov    %r13d,%edx
  4012b2:	48 d3 e6             	shl    %cl,%rsi
  4012b5:	49 89 86 78 fc ff ff 	mov    %rax,-0x388(%r14)
  4012bc:	bf 01 00 00 00       	mov    $0x1,%edi
  4012c1:	48 09 30             	or     %rsi,(%rax)
  4012c4:	4c 89 fe             	mov    %r15,%rsi
  4012c7:	31 c0                	xor    %eax,%eax
  4012c9:	e8 f2 fd ff ff       	call   4010c0 <__printf_chk@plt>
  4012ce:	41 69 c5 55 55 55 15 	imul   $0x15555555,%r13d,%eax
  4012d5:	45 89 ae 64 fc ff ff 	mov    %r13d,-0x39c(%r14)
  4012dc:	66 0f 6f 0d 1c 1f 00 00 	movdqa 0x1f1c(%rip),%xmm1        # 403200 <_IO_stdin_used+0x200>
  4012e4:	41 c7 86 80 fc ff ff 00 00 00 00 	movl   $0x0,-0x380(%r14)
  4012ef:	66 0f 6f 15 19 1f 00 00 	movdqa 0x1f19(%rip),%xmm2        # 403210 <_IO_stdin_used+0x210>
  4012f7:	be 30 00 00 00       	mov    $0x30,%esi
  4012fc:	bf 80 96 98 00       	mov    $0x989680,%edi
  401301:	49 89 ae 20 fc ff ff 	mov    %rbp,-0x3e0(%r14)
  401308:	66 0f 6f 1d 10 1f 00 00 	movdqa 0x1f10(%rip),%xmm3        # 403220 <_IO_stdin_used+0x220>
  401310:	41 89 86 98 fc ff ff 	mov    %eax,-0x368(%r14)
  401317:	48 8b 04 24          	mov    (%rsp),%rax
  40131b:	41 c7 86 94 fc ff ff 55 55 55 15 	movl   $0x15555555,-0x36c(%r14)
  401326:	49 89 46 80          	mov    %rax,-0x80(%r14)
  40132a:	48 8b 05 c7 1e 00 00 	mov    0x1ec7(%rip),%rax        # 4031f8 <_IO_stdin_used+0x1f8>
  401331:	41 c7 86 68 fc ff ff 0c 00 00 00 	movl   $0xc,-0x398(%r14)
  40133c:	49 89 86 5c fc ff ff 	mov    %rax,-0x3a4(%r14)
  401343:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  401348:	42 c7 44 ad 00 00 00 00 00 	movl   $0x0,0x0(%rbp,%r13,4)
  401351:	49 89 86 a0 fc ff ff 	mov    %rax,-0x360(%r14)
  401358:	43 8d 44 2d 00       	lea    0x0(%r13,%r13,1),%eax
  40135d:	49 83 c5 01          	add    $0x1,%r13
  401361:	c1 f8 02             	sar    $0x2,%eax
  401364:	49 89 9e 28 fc ff ff 	mov    %rbx,-0x3d8(%r14)
  40136b:	83 c0 01             	add    $0x1,%eax
  40136e:	41 c7 86 90 fc ff ff 55 55 55 15 	movl   $0x15555555,-0x370(%r14)
  401379:	49 89 9e 30 fc ff ff 	mov    %rbx,-0x3d0(%r14)
  401380:	41 c7 86 00 fe ff ff 0b 00 00 00 	movl   $0xb,-0x200(%r14)
  40138b:	41 c7 86 80 fd ff ff 0b 00 00 00 	movl   $0xb,-0x280(%r14)
  401396:	41 c7 86 c8 fc ff ff 00 00 00 00 	movl   $0x0,-0x338(%r14)
  4013a1:	41 89 46 8c          	mov    %eax,-0x74(%r14)
  4013a5:	41 c7 86 28 ff ff ff 0c 00 00 00 	movl   $0xc,-0xd8(%r14)
  4013b0:	41 0f 29 8e 00 fc ff ff 	movaps %xmm1,-0x400(%r14)
  4013b8:	41 0f 11 96 b8 fc ff ff 	movups %xmm2,-0x348(%r14)
  4013c0:	41 0f 11 9e 08 ff ff ff 	movups %xmm3,-0xf8(%r14)
  4013c8:	e8 e3 fc ff ff       	call   4010b0 <calloc@plt>
  4013cd:	be 30 00 00 00       	mov    $0x30,%esi
  4013d2:	bf 10 27 00 00       	mov    $0x2710,%edi
  4013d7:	41 c7 86 20 ff ff ff 80 96 98 00 	movl   $0x989680,-0xe0(%r14)
  4013e2:	49 89 86 18 ff ff ff 	mov    %rax,-0xe8(%r14)
  4013e9:	e8 c2 fc ff ff       	call   4010b0 <calloc@plt>
  4013ee:	49 89 86 30 ff ff ff 	mov    %rax,-0xd0(%r14)
  4013f5:	49 83 fd 0c          	cmp    $0xc,%r13
  4013f9:	0f 85 91 fe ff ff    	jne    401290 <main+0x180>
  4013ff:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
  401404:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
  401409:	49 89 de             	mov    %rbx,%r14
  40140c:	49 c7 c5 10 21 40 00 	mov    $0x402110,%r13
  401413:	48 8d 85 a0 02 00 00 	lea    0x2a0(%rbp),%rax
  40141a:	4d 89 fc             	mov    %r15,%r12
  40141d:	48 89 04 24          	mov    %rax,(%rsp)
  401421:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401428:	4c 89 f1             	mov    %r14,%rcx
  40142b:	48 89 ee             	mov    %rbp,%rsi
  40142e:	4c 89 ff             	mov    %r15,%rdi
  401431:	4c 89 ea             	mov    %r13,%rdx
  401434:	e8 97 fc ff ff       	call   4010d0 <pthread_create@plt>
  401439:	49 8b 56 78          	mov    0x78(%r14),%rdx
  40143d:	49 8b 3f             	mov    (%r15),%rdi
  401440:	be 08 00 00 00       	mov    $0x8,%esi
  401445:	49 83 c7 08          	add    $0x8,%r15
  401449:	48 83 c5 38          	add    $0x38,%rbp
  40144d:	49 81 c6 00 04 00 00 	add    $0x400,%r14
  401454:	e8 e7 fb ff ff       	call   401040 <pthread_setaffinity_np@plt>
  401459:	48 3b 2c 24          	cmp    (%rsp),%rbp
  40145d:	75 c9                	jne    401428 <main+0x318>
  40145f:	66 0f 6f 05 c9 1d 00 00 	movdqa 0x1dc9(%rip),%xmm0        # 403230 <_IO_stdin_used+0x230>
  401467:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  40146c:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
  401471:	4c 8d 6c 24 20       	lea    0x20(%rsp),%r13
  401476:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  40147b:	66 0f ef c0          	pxor   %xmm0,%xmm0
  40147f:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  401484:	e8 f7 fb ff ff       	call   401080 <nanosleep@plt>
  401489:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
  40148e:	c7 43 5c 00 00 00 00 	movl   $0x0,0x5c(%rbx)
  401495:	c7 83 5c 04 00 00 00 00 00 00 	movl   $0x0,0x45c(%rbx)
  40149f:	c7 83 5c 08 00 00 00 00 00 00 	movl   $0x0,0x85c(%rbx)
  4014a9:	48 83 c5 60          	add    $0x60,%rbp
  4014ad:	c7 83 5c 0c 00 00 00 00 00 00 	movl   $0x0,0xc5c(%rbx)
  4014b7:	c7 83 5c 10 00 00 00 00 00 00 	movl   $0x0,0x105c(%rbx)
  4014c1:	c7 83 5c 14 00 00 00 00 00 00 	movl   $0x0,0x145c(%rbx)
  4014cb:	c7 83 5c 18 00 00 00 00 00 00 	movl   $0x0,0x185c(%rbx)
  4014d5:	c7 83 5c 1c 00 00 00 00 00 00 	movl   $0x0,0x1c5c(%rbx)
  4014df:	c7 83 5c 20 00 00 00 00 00 00 	movl   $0x0,0x205c(%rbx)
  4014e9:	c7 83 5c 24 00 00 00 00 00 00 	movl   $0x0,0x245c(%rbx)
  4014f3:	c7 83 5c 28 00 00 00 00 00 00 	movl   $0x0,0x285c(%rbx)
  4014fd:	c7 83 5c 2c 00 00 00 00 00 00 	movl   $0x0,0x2c5c(%rbx)
  401507:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  401510:	49 8b 3c 24          	mov    (%r12),%rdi
  401514:	4c 89 ee             	mov    %r13,%rsi
  401517:	49 83 c4 08          	add    $0x8,%r12
  40151b:	e8 e0 fb ff ff       	call   401100 <pthread_join@plt>
  401520:	4c 39 e5             	cmp    %r12,%rbp
  401523:	75 eb                	jne    401510 <main+0x400>
  401525:	48 8d 3d 5a 1b 00 00 	lea    0x1b5a(%rip),%rdi        # 403086 <_IO_stdin_used+0x86>
  40152c:	48 8d 6b 48          	lea    0x48(%rbx),%rbp
  401530:	45 31 e4             	xor    %r12d,%r12d
  401533:	e8 18 fb ff ff       	call   401050 <puts@plt>
  401538:	4c 8d b3 48 30 00 00 	lea    0x3048(%rbx),%r14
  40153f:	4c 8d 2d 55 1b 00 00 	lea    0x1b55(%rip),%r13        # 40309b <_IO_stdin_used+0x9b>
  401546:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401550:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401554:	4c 89 ee             	mov    %r13,%rsi
  401557:	bf 01 00 00 00       	mov    $0x1,%edi
  40155c:	31 c0                	xor    %eax,%eax
  40155e:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
  401565:	e8 56 fb ff ff       	call   4010c0 <__printf_chk@plt>
  40156a:	4c 03 a5 00 fc ff ff 	add    -0x400(%rbp),%r12
  401571:	49 39 ee             	cmp    %rbp,%r14
  401574:	75 da                	jne    401550 <main+0x440>
  401576:	4c 89 e2             	mov    %r12,%rdx
  401579:	48 8d 35 26 1b 00 00 	lea    0x1b26(%rip),%rsi        # 4030a6 <_IO_stdin_used+0xa6>
  401580:	48 8d 6b 50          	lea    0x50(%rbx),%rbp
  401584:	31 c0                	xor    %eax,%eax
  401586:	bf 01 00 00 00       	mov    $0x1,%edi
  40158b:	4c 8d b3 50 30 00 00 	lea    0x3050(%rbx),%r14
  401592:	4c 8d 2d 6b 1b 00 00 	lea    0x1b6b(%rip),%r13        # 403104 <_IO_stdin_used+0x104>
  401599:	e8 22 fb ff ff       	call   4010c0 <__printf_chk@plt>
  40159e:	4c 89 e2             	mov    %r12,%rdx
  4015a1:	bf 01 00 00 00       	mov    $0x1,%edi
  4015a6:	31 c0                	xor    %eax,%eax
  4015a8:	48 8d 35 02 1b 00 00 	lea    0x1b02(%rip),%rsi        # 4030b1 <_IO_stdin_used+0xb1>
  4015af:	e8 0c fb ff ff       	call   4010c0 <__printf_chk@plt>
  4015b4:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  4015b9:	bf 01 00 00 00       	mov    $0x1,%edi
  4015be:	48 8d 35 fa 1a 00 00 	lea    0x1afa(%rip),%rsi        # 4030bf <_IO_stdin_used+0xbf>
  4015c5:	48 99                	cqto
  4015c7:	49 f7 fc             	idiv   %r12
  4015ca:	49 89 c4             	mov    %rax,%r12
  4015cd:	48 89 c2             	mov    %rax,%rdx
  4015d0:	31 c0                	xor    %eax,%eax
  4015d2:	e8 e9 fa ff ff       	call   4010c0 <__printf_chk@plt>
  4015d7:	4c 89 e2             	mov    %r12,%rdx
  4015da:	bf 01 00 00 00       	mov    $0x1,%edi
  4015df:	31 c0                	xor    %eax,%eax
  4015e1:	48 8d 35 eb 1a 00 00 	lea    0x1aeb(%rip),%rsi        # 4030d3 <_IO_stdin_used+0xd3>
  4015e8:	e8 d3 fa ff ff       	call   4010c0 <__printf_chk@plt>
  4015ed:	4c 89 e2             	mov    %r12,%rdx
  4015f0:	bf 01 00 00 00       	mov    $0x1,%edi
  4015f5:	31 c0                	xor    %eax,%eax
  4015f7:	48 8d 35 f3 1a 00 00 	lea    0x1af3(%rip),%rsi        # 4030f1 <_IO_stdin_used+0xf1>
  4015fe:	45 31 e4             	xor    %r12d,%r12d
  401601:	e8 ba fa ff ff       	call   4010c0 <__printf_chk@plt>
  401606:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401610:	48 8b 55 00          	mov    0x0(%rbp),%rdx
  401614:	4c 89 ee             	mov    %r13,%rsi
  401617:	bf 01 00 00 00       	mov    $0x1,%edi
  40161c:	31 c0                	xor    %eax,%eax
  40161e:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
  401625:	49 01 d4             	add    %rdx,%r12
  401628:	e8 93 fa ff ff       	call   4010c0 <__printf_chk@plt>
  40162d:	4c 39 f5             	cmp    %r14,%rbp
  401630:	75 de                	jne    401610 <main+0x500>
  401632:	4c 89 e2             	mov    %r12,%rdx
  401635:	48 8d 35 d4 1a 00 00 	lea    0x1ad4(%rip),%rsi        # 403110 <_IO_stdin_used+0x110>
  40163c:	bf 01 00 00 00       	mov    $0x1,%edi
  401641:	31 c0                	xor    %eax,%eax
  401643:	e8 78 fa ff ff       	call   4010c0 <__printf_chk@plt>
  401648:	4c 89 e2             	mov    %r12,%rdx
  40164b:	bf 01 00 00 00       	mov    $0x1,%edi
  401650:	31 c0                	xor    %eax,%eax
  401652:	48 8d 35 c9 1a 00 00 	lea    0x1ac9(%rip),%rsi        # 403122 <_IO_stdin_used+0x122>
  401659:	48 8d 2d 6e 1a 00 00 	lea    0x1a6e(%rip),%rbp        # 4030ce <_IO_stdin_used+0xce>
  401660:	e8 5b fa ff ff       	call   4010c0 <__printf_chk@plt>
  401665:	b8 00 ca 9a 3b       	mov    $0x3b9aca00,%eax
  40166a:	48 8d 35 c9 1a 00 00 	lea    0x1ac9(%rip),%rsi        # 40313a <_IO_stdin_used+0x13a>
  401671:	bf 01 00 00 00       	mov    $0x1,%edi
  401676:	48 99                	cqto
  401678:	4c 8d b3 20 03 00 00 	lea    0x320(%rbx),%r14
  40167f:	49 f7 fc             	idiv   %r12
  401682:	49 89 c4             	mov    %rax,%r12
  401685:	48 89 c2             	mov    %rax,%rdx
  401688:	31 c0                	xor    %eax,%eax
  40168a:	e8 31 fa ff ff       	call   4010c0 <__printf_chk@plt>
  40168f:	4c 89 e2             	mov    %r12,%rdx
  401692:	bf 01 00 00 00       	mov    $0x1,%edi
  401697:	31 c0                	xor    %eax,%eax
  401699:	48 8d 35 28 1b 00 00 	lea    0x1b28(%rip),%rsi        # 4031c8 <_IO_stdin_used+0x1c8>
  4016a0:	e8 1b fa ff ff       	call   4010c0 <__printf_chk@plt>
  4016a5:	4c 89 e2             	mov    %r12,%rdx
  4016a8:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ad:	31 c0                	xor    %eax,%eax
  4016af:	48 8d 35 9f 1a 00 00 	lea    0x1a9f(%rip),%rsi        # 403155 <_IO_stdin_used+0x155>
  4016b6:	e8 05 fa ff ff       	call   4010c0 <__printf_chk@plt>
  4016bb:	48 8d 3d ad 1a 00 00 	lea    0x1aad(%rip),%rdi        # 40316f <_IO_stdin_used+0x16f>
  4016c2:	e8 89 f9 ff ff       	call   401050 <puts@plt>
  4016c7:	48 89 ee             	mov    %rbp,%rsi
  4016ca:	bf 01 00 00 00       	mov    $0x1,%edi
  4016cf:	31 c0                	xor    %eax,%eax
  4016d1:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  4016d8:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4016df:	e8 dc f9 ff ff       	call   4010c0 <__printf_chk@plt>
  4016e4:	48 89 ee             	mov    %rbp,%rsi
  4016e7:	bf 01 00 00 00       	mov    $0x1,%edi
  4016ec:	31 c0                	xor    %eax,%eax
  4016ee:	48 8b 93 00 01 00 00 	mov    0x100(%rbx),%rdx
  4016f5:	48 2b 93 e0 00 00 00 	sub    0xe0(%rbx),%rdx
  4016fc:	e8 bf f9 ff ff       	call   4010c0 <__printf_chk@plt>
  401701:	48 89 ee             	mov    %rbp,%rsi
  401704:	bf 01 00 00 00       	mov    $0x1,%edi
  401709:	31 c0                	xor    %eax,%eax
  40170b:	48 8b 93 f0 00 00 00 	mov    0xf0(%rbx),%rdx
  401712:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401719:	e8 a2 f9 ff ff       	call   4010c0 <__printf_chk@plt>
  40171e:	48 89 ee             	mov    %rbp,%rsi
  401721:	bf 01 00 00 00       	mov    $0x1,%edi
  401726:	31 c0                	xor    %eax,%eax
  401728:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
  40172f:	48 2b 93 10 01 00 00 	sub    0x110(%rbx),%rdx
  401736:	e8 85 f9 ff ff       	call   4010c0 <__printf_chk@plt>
  40173b:	48 89 ee             	mov    %rbp,%rsi
  40173e:	bf 01 00 00 00       	mov    $0x1,%edi
  401743:	31 c0                	xor    %eax,%eax
  401745:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  40174c:	48 2b 93 20 01 00 00 	sub    0x120(%rbx),%rdx
  401753:	e8 68 f9 ff ff       	call   4010c0 <__printf_chk@plt>
  401758:	48 89 ee             	mov    %rbp,%rsi
  40175b:	bf 01 00 00 00       	mov    $0x1,%edi
  401760:	31 c0                	xor    %eax,%eax
  401762:	48 8b 93 10 01 00 00 	mov    0x110(%rbx),%rdx
  401769:	48 2b 93 00 01 00 00 	sub    0x100(%rbx),%rdx
  401770:	e8 4b f9 ff ff       	call   4010c0 <__printf_chk@plt>
  401775:	48 8b 93 40 01 00 00 	mov    0x140(%rbx),%rdx
  40177c:	bf 01 00 00 00       	mov    $0x1,%edi
  401781:	48 2b 93 30 01 00 00 	sub    0x130(%rbx),%rdx
  401788:	48 8d 35 ed 19 00 00 	lea    0x19ed(%rip),%rsi        # 40317c <_IO_stdin_used+0x17c>
  40178f:	31 c0                	xor    %eax,%eax
  401791:	48 81 c3 20 33 00 00 	add    $0x3320,%rbx
  401798:	45 31 ed             	xor    %r13d,%r13d
  40179b:	e8 20 f9 ff ff       	call   4010c0 <__printf_chk@plt>
  4017a0:	be 01 00 00 00       	mov    $0x1,%esi
  4017a5:	bf 64 00 00 00       	mov    $0x64,%edi
  4017aa:	e8 01 f9 ff ff       	call   4010b0 <calloc@plt>
  4017af:	be 01 00 00 00       	mov    $0x1,%esi
  4017b4:	bf e8 03 00 00       	mov    $0x3e8,%edi
  4017b9:	49 89 c4             	mov    %rax,%r12
  4017bc:	e8 ef f8 ff ff       	call   4010b0 <calloc@plt>
  4017c1:	44 8b 8b 48 cd ff ff 	mov    -0x32b8(%rbx),%r9d
  4017c8:	4c 89 e7             	mov    %r12,%rdi
  4017cb:	4c 8d 05 b2 19 00 00 	lea    0x19b2(%rip),%r8        # 403184 <_IO_stdin_used+0x184>
  4017d2:	b9 64 00 00 00       	mov    $0x64,%ecx
  4017d7:	ba 01 00 00 00       	mov    $0x1,%edx
  4017dc:	be 64 00 00 00       	mov    $0x64,%esi
  4017e1:	48 89 c5             	mov    %rax,%rbp
  4017e4:	31 c0                	xor    %eax,%eax
  4017e6:	e8 45 f8 ff ff       	call   401030 <__snprintf_chk@plt>
  4017eb:	4c 89 e7             	mov    %r12,%rdi
  4017ee:	48 8d 35 99 19 00 00 	lea    0x1999(%rip),%rsi        # 40318e <_IO_stdin_used+0x18e>
  4017f5:	e8 e6 f8 ff ff       	call   4010e0 <fopen@plt>
  4017fa:	49 89 c4             	mov    %rax,%r12
  4017fd:	0f 1f 00             	nopl   (%rax)
  401800:	41 8b 0e             	mov    (%r14),%ecx
  401803:	45 31 ff             	xor    %r15d,%r15d
  401806:	85 c9                	test   %ecx,%ecx
  401808:	7e 21                	jle    40182b <main+0x71b>
  40180a:	49 8b 76 f8          	mov    -0x8(%r14),%rsi
  40180e:	49 63 c7             	movslq %r15d,%rax
  401811:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  401815:	48 c1 e2 04          	shl    $0x4,%rdx
  401819:	48 01 f2             	add    %rsi,%rdx
  40181c:	83 7a 24 01          	cmpl   $0x1,0x24(%rdx)
  401820:	74 3e                	je     401860 <main+0x750>
  401822:	41 83 c7 01          	add    $0x1,%r15d
  401826:	41 39 cf             	cmp    %ecx,%r15d
  401829:	7c e3                	jl     40180e <main+0x6fe>
  40182b:	49 81 c6 00 04 00 00 	add    $0x400,%r14
  401832:	49 39 de             	cmp    %rbx,%r14
  401835:	75 c9                	jne    401800 <main+0x6f0>
  401837:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  40183c:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401845:	0f 85 90 00 00 00    	jne    4018db <main+0x7cb>
  40184b:	48 83 c4 68          	add    $0x68,%rsp
  40184f:	31 c0                	xor    %eax,%eax
  401851:	5b                   	pop    %rbx
  401852:	5d                   	pop    %rbp
  401853:	41 5c                	pop    %r12
  401855:	41 5d                	pop    %r13
  401857:	41 5e                	pop    %r14
  401859:	41 5f                	pop    %r15
  40185b:	c3                   	ret
  40185c:	0f 1f 40 00          	nopl   0x0(%rax)
  401860:	4c 89 e8             	mov    %r13,%rax
  401863:	b9 7d 00 00 00       	mov    $0x7d,%ecx
  401868:	48 89 ef             	mov    %rbp,%rdi
  40186b:	48 83 ec 08          	sub    $0x8,%rsp
  40186f:	f3 48 ab             	rep stos %rax,%es:(%rdi)
  401872:	be 64 00 00 00       	mov    $0x64,%esi
  401877:	48 89 ef             	mov    %rbp,%rdi
  40187a:	41 83 c7 01          	add    $0x1,%r15d
  40187e:	b9 e8 03 00 00       	mov    $0x3e8,%ecx
  401883:	4c 8d 05 06 19 00 00 	lea    0x1906(%rip),%r8        # 403190 <_IO_stdin_used+0x190>
  40188a:	8b 42 28             	mov    0x28(%rdx),%eax
  40188d:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
  401891:	50                   	push   %rax
  401892:	8b 02                	mov    (%rdx),%eax
  401894:	50                   	push   %rax
  401895:	8b 42 20             	mov    0x20(%rdx),%eax
  401898:	ff 72 18             	push   0x18(%rdx)
  40189b:	50                   	push   %rax
  40189c:	31 c0                	xor    %eax,%eax
  40189e:	ff 72 10             	push   0x10(%rdx)
  4018a1:	ba 01 00 00 00       	mov    $0x1,%edx
  4018a6:	e8 85 f7 ff ff       	call   401030 <__snprintf_chk@plt>
  4018ab:	48 83 c4 30          	add    $0x30,%rsp
  4018af:	4c 89 e6             	mov    %r12,%rsi
  4018b2:	48 89 ef             	mov    %rbp,%rdi
  4018b5:	e8 d6 f7 ff ff       	call   401090 <fputs@plt>
  4018ba:	41 8b 0e             	mov    (%r14),%ecx
  4018bd:	41 39 cf             	cmp    %ecx,%r15d
  4018c0:	0f 8c 44 ff ff ff    	jl     40180a <main+0x6fa>
  4018c6:	49 81 c6 00 04 00 00 	add    $0x400,%r14
  4018cd:	49 39 de             	cmp    %rbx,%r14
  4018d0:	0f 85 2a ff ff ff    	jne    401800 <main+0x6f0>
  4018d6:	e9 5c ff ff ff       	jmp    401837 <main+0x727>
  4018db:	e8 90 f7 ff ff       	call   401070 <__stack_chk_fail@plt>

00000000004018e0 <set_fast_math>:
  4018e0:	f3 0f 1e fa          	endbr64
  4018e4:	0f ae 5c 24 fc       	stmxcsr -0x4(%rsp)
  4018e9:	81 4c 24 fc 40 80 00 00 	orl    $0x8040,-0x4(%rsp)
  4018f1:	0f ae 54 24 fc       	ldmxcsr -0x4(%rsp)
  4018f6:	c3                   	ret
  4018f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000401900 <_start>:
  401900:	f3 0f 1e fa          	endbr64
  401904:	31 ed                	xor    %ebp,%ebp
  401906:	49 89 d1             	mov    %rdx,%r9
  401909:	5e                   	pop    %rsi
  40190a:	48 89 e2             	mov    %rsp,%rdx
  40190d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  401911:	50                   	push   %rax
  401912:	54                   	push   %rsp
  401913:	45 31 c0             	xor    %r8d,%r8d
  401916:	31 c9                	xor    %ecx,%ecx
  401918:	48 c7 c7 10 11 40 00 	mov    $0x401110,%rdi
  40191f:	ff 15 cb 36 00 00    	call   *0x36cb(%rip)        # 404ff0 <__libc_start_main@GLIBC_2.34>
  401925:	f4                   	hlt
  401926:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401930 <_dl_relocate_static_pie>:
  401930:	f3 0f 1e fa          	endbr64
  401934:	c3                   	ret
  401935:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40193f:	90                   	nop

0000000000401940 <deregister_tm_clones>:
  401940:	b8 10 50 40 00       	mov    $0x405010,%eax
  401945:	48 3d 10 50 40 00    	cmp    $0x405010,%rax
  40194b:	74 13                	je     401960 <deregister_tm_clones+0x20>
  40194d:	b8 00 00 00 00       	mov    $0x0,%eax
  401952:	48 85 c0             	test   %rax,%rax
  401955:	74 09                	je     401960 <deregister_tm_clones+0x20>
  401957:	bf 10 50 40 00       	mov    $0x405010,%edi
  40195c:	ff e0                	jmp    *%rax
  40195e:	66 90                	xchg   %ax,%ax
  401960:	c3                   	ret
  401961:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40196c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401970 <register_tm_clones>:
  401970:	be 10 50 40 00       	mov    $0x405010,%esi
  401975:	48 81 ee 10 50 40 00 	sub    $0x405010,%rsi
  40197c:	48 89 f0             	mov    %rsi,%rax
  40197f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401983:	48 c1 f8 03          	sar    $0x3,%rax
  401987:	48 01 c6             	add    %rax,%rsi
  40198a:	48 d1 fe             	sar    %rsi
  40198d:	74 11                	je     4019a0 <register_tm_clones+0x30>
  40198f:	b8 00 00 00 00       	mov    $0x0,%eax
  401994:	48 85 c0             	test   %rax,%rax
  401997:	74 07                	je     4019a0 <register_tm_clones+0x30>
  401999:	bf 10 50 40 00       	mov    $0x405010,%edi
  40199e:	ff e0                	jmp    *%rax
  4019a0:	c3                   	ret
  4019a1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4019ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004019b0 <__do_global_dtors_aux>:
  4019b0:	f3 0f 1e fa          	endbr64
  4019b4:	80 3d 55 36 00 00 00 	cmpb   $0x0,0x3655(%rip)        # 405010 <__TMC_END__>
  4019bb:	75 13                	jne    4019d0 <__do_global_dtors_aux+0x20>
  4019bd:	55                   	push   %rbp
  4019be:	48 89 e5             	mov    %rsp,%rbp
  4019c1:	e8 7a ff ff ff       	call   401940 <deregister_tm_clones>
  4019c6:	c6 05 43 36 00 00 01 	movb   $0x1,0x3643(%rip)        # 405010 <__TMC_END__>
  4019cd:	5d                   	pop    %rbp
  4019ce:	c3                   	ret
  4019cf:	90                   	nop
  4019d0:	c3                   	ret
  4019d1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4019dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004019e0 <frame_dummy>:
  4019e0:	f3 0f 1e fa          	endbr64
  4019e4:	eb 8a                	jmp    401970 <register_tm_clones>
  4019e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004019f0 <pollthreads>:
  4019f0:	83 7f 68 01          	cmpl   $0x1,0x68(%rdi)
  4019f4:	49 89 f9             	mov    %rdi,%r9
  4019f7:	7e 77                	jle    401a70 <pollthreads+0x80>
  4019f9:	49 8b 41 30          	mov    0x30(%r9),%rax
  4019fd:	55                   	push   %rbp
  4019fe:	49 89 f2             	mov    %rsi,%r10
  401a01:	49 89 d3             	mov    %rdx,%r11
  401a04:	53                   	push   %rbx
  401a05:	48 89 cf             	mov    %rcx,%rdi
  401a08:	48 8b 98 20 04 00 00 	mov    0x420(%rax),%rbx
  401a0f:	b8 01 00 00 00       	mov    $0x1,%eax
  401a14:	0f 1f 40 00          	nopl   0x0(%rax)
  401a18:	48 63 d0             	movslq %eax,%rdx
  401a1b:	8b 14 93             	mov    (%rbx,%rdx,4),%edx
  401a1e:	85 d2                	test   %edx,%edx
  401a20:	40 0f 94 c6          	sete   %sil
  401a24:	f6 c2 04             	test   $0x4,%dl
  401a27:	75 05                	jne    401a2e <pollthreads+0x3e>
  401a29:	40 84 f6             	test   %sil,%sil
  401a2c:	74 0d                	je     401a3b <pollthreads+0x4b>
  401a2e:	49 63 08             	movslq (%r8),%rcx
  401a31:	8d 69 01             	lea    0x1(%rcx),%ebp
  401a34:	41 89 28             	mov    %ebp,(%r8)
  401a37:	41 89 04 8b          	mov    %eax,(%r11,%rcx,4)
  401a3b:	83 e2 08             	and    $0x8,%edx
  401a3e:	75 05                	jne    401a45 <pollthreads+0x55>
  401a40:	40 84 f6             	test   %sil,%sil
  401a43:	74 1b                	je     401a60 <pollthreads+0x70>
  401a45:	48 63 17             	movslq (%rdi),%rdx
  401a48:	8d 4a 01             	lea    0x1(%rdx),%ecx
  401a4b:	89 0f                	mov    %ecx,(%rdi)
  401a4d:	41 89 04 92          	mov    %eax,(%r10,%rdx,4)
  401a51:	83 c0 01             	add    $0x1,%eax
  401a54:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401a58:	7f be                	jg     401a18 <pollthreads+0x28>
  401a5a:	31 c0                	xor    %eax,%eax
  401a5c:	5b                   	pop    %rbx
  401a5d:	5d                   	pop    %rbp
  401a5e:	c3                   	ret
  401a5f:	90                   	nop
  401a60:	83 c0 01             	add    $0x1,%eax
  401a63:	41 39 41 68          	cmp    %eax,0x68(%r9)
  401a67:	7f af                	jg     401a18 <pollthreads+0x28>
  401a69:	31 c0                	xor    %eax,%eax
  401a6b:	5b                   	pop    %rbx
  401a6c:	5d                   	pop    %rbp
  401a6d:	c3                   	ret
  401a6e:	66 90                	xchg   %ax,%ax
  401a70:	31 c0                	xor    %eax,%eax
  401a72:	c3                   	ret
  401a73:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401a7e:	66 90                	xchg   %ax,%ax

0000000000401a80 <findavailable>:
  401a80:	49 89 fb             	mov    %rdi,%r11
  401a83:	48 8b bf b8 00 00 00 	mov    0xb8(%rdi),%rdi
  401a8a:	44 8b 02             	mov    (%rdx),%r8d
  401a8d:	48 83 c7 01          	add    $0x1,%rdi
  401a91:	48 85 ff             	test   %rdi,%rdi
  401a94:	7e 66                	jle    401afc <findavailable+0x7c>
  401a96:	4d 8b 93 a0 00 00 00 	mov    0xa0(%r11),%r10
  401a9d:	31 c9                	xor    %ecx,%ecx
  401a9f:	45 31 c9             	xor    %r9d,%r9d
  401aa2:	31 c0                	xor    %eax,%eax
  401aa4:	eb 18                	jmp    401abe <findavailable+0x3e>
  401aa6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  401ab0:	83 c1 01             	add    $0x1,%ecx
  401ab3:	48 63 c1             	movslq %ecx,%rax
  401ab6:	49 89 c1             	mov    %rax,%r9
  401ab9:	48 39 f8             	cmp    %rdi,%rax
  401abc:	7d 3e                	jge    401afc <findavailable+0x7c>
  401abe:	48 c1 e0 05          	shl    $0x5,%rax
  401ac2:	41 83 7c 02 10 01    	cmpl   $0x1,0x10(%r10,%rax,1)
  401ac8:	75 e6                	jne    401ab0 <findavailable+0x30>
  401aca:	49 63 c0             	movslq %r8d,%rax
  401acd:	41 83 c0 01          	add    $0x1,%r8d
  401ad1:	4c 89 0c c6          	mov    %r9,(%rsi,%rax,8)
  401ad5:	44 89 02             	mov    %r8d,(%rdx)
  401ad8:	41 8b 43 68          	mov    0x68(%r11),%eax
  401adc:	01 c0                	add    %eax,%eax
  401ade:	41 39 c0             	cmp    %eax,%r8d
  401ae1:	74 19                	je     401afc <findavailable+0x7c>
  401ae3:	49 8b bb b8 00 00 00 	mov    0xb8(%r11),%rdi
  401aea:	83 c1 01             	add    $0x1,%ecx
  401aed:	48 63 c1             	movslq %ecx,%rax
  401af0:	48 83 c7 01          	add    $0x1,%rdi
  401af4:	49 89 c1             	mov    %rax,%r9
  401af7:	48 39 f8             	cmp    %rdi,%rax
  401afa:	7c c2                	jl     401abe <findavailable+0x3e>
  401afc:	31 c0                	xor    %eax,%eax
  401afe:	45 85 c0             	test   %r8d,%r8d
  401b01:	0f 94 c0             	sete   %al
  401b04:	c3                   	ret
  401b05:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000401b10 <singlewriter3>:
  401b10:	c3                   	ret
  401b11:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401b1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401b20 <singlewriter2>:
  401b20:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  401b26:	85 c0                	test   %eax,%eax
  401b28:	74 1e                	je     401b48 <singlewriter2+0x28>
  401b2a:	41 54                	push   %r12
  401b2c:	99                   	cltd
  401b2d:	55                   	push   %rbp
  401b2e:	53                   	push   %rbx
  401b2f:	8b 77 68             	mov    0x68(%rdi),%esi
  401b32:	48 89 fb             	mov    %rdi,%rbx
  401b35:	8d 4e ff             	lea    -0x1(%rsi),%ecx
  401b38:	f7 f9                	idiv   %ecx
  401b3a:	85 d2                	test   %edx,%edx
  401b3c:	74 12                	je     401b50 <singlewriter2+0x30>
  401b3e:	5b                   	pop    %rbx
  401b3f:	5d                   	pop    %rbp
  401b40:	41 5c                	pop    %r12
  401b42:	c3                   	ret
  401b43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401b48:	c3                   	ret
  401b49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401b50:	48 63 6f 64          	movslq 0x64(%rdi),%rbp
  401b54:	48 c1 e5 0a          	shl    $0xa,%rbp
  401b58:	48 03 6f 30          	add    0x30(%rdi),%rbp
  401b5c:	bf 04 00 00 00       	mov    $0x4,%edi
  401b61:	48 63 85 24 03 00 00 	movslq 0x324(%rbp),%rax
  401b68:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  401b6c:	49 c1 e4 04          	shl    $0x4,%r12
  401b70:	4c 03 a5 18 03 00 00 	add    0x318(%rbp),%r12
  401b77:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
  401b7c:	e8 df f4 ff ff       	call   401060 <clock_gettime@plt>
  401b81:	8b 85 24 03 00 00    	mov    0x324(%rbp),%eax
  401b87:	83 c0 01             	add    $0x1,%eax
  401b8a:	99                   	cltd
  401b8b:	f7 bd 20 03 00 00    	idivl  0x320(%rbp)
  401b91:	8b 43 64             	mov    0x64(%rbx),%eax
  401b94:	89 95 24 03 00 00    	mov    %edx,0x324(%rbp)
  401b9a:	41 89 04 24          	mov    %eax,(%r12)
  401b9e:	48 8b 05 4b 16 00 00 	mov    0x164b(%rip),%rax        # 4031f0 <_IO_stdin_used+0x1f0>
  401ba5:	49 89 44 24 20       	mov    %rax,0x20(%r12)
  401baa:	5b                   	pop    %rbx
  401bab:	5d                   	pop    %rbp
  401bac:	41 5c                	pop    %r12
  401bae:	c3                   	ret
  401baf:	90                   	nop

0000000000401bb0 <singlewriter>:
  401bb0:	41 55                	push   %r13
  401bb2:	49 89 d5             	mov    %rdx,%r13
  401bb5:	41 54                	push   %r12
  401bb7:	49 89 cc             	mov    %rcx,%r12
  401bba:	55                   	push   %rbp
  401bbb:	4d 89 e0             	mov    %r12,%r8
  401bbe:	48 89 fd             	mov    %rdi,%rbp
  401bc1:	53                   	push   %rbx
  401bc2:	48 89 f3             	mov    %rsi,%rbx
  401bc5:	48 83 ec 28          	sub    $0x28,%rsp
  401bc9:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
  401bcd:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401bd6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401bdb:	31 c0                	xor    %eax,%eax
  401bdd:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
  401be5:	8b 81 0c 02 00 00    	mov    0x20c(%rcx),%eax
  401beb:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  401bf3:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
  401bfb:	83 c0 01             	add    $0x1,%eax
  401bfe:	99                   	cltd
  401bff:	f7 7f 68             	idivl  0x68(%rdi)
  401c02:	89 91 0c 02 00 00    	mov    %edx,0x20c(%rcx)
  401c08:	48 8d 54 24 14       	lea    0x14(%rsp),%rdx
  401c0d:	4c 89 e9             	mov    %r13,%rcx
  401c10:	e8 6b fe ff ff       	call   401a80 <findavailable>
  401c15:	83 f8 01             	cmp    $0x1,%eax
  401c18:	0f 84 3c 01 00 00    	je     401d5a <singlewriter+0x1aa>
  401c1e:	4c 8d 44 24 10       	lea    0x10(%rsp),%r8
  401c23:	48 8d 4c 24 0c       	lea    0xc(%rsp),%rcx
  401c28:	4c 89 e2             	mov    %r12,%rdx
  401c2b:	4c 89 ee             	mov    %r13,%rsi
  401c2e:	48 89 ef             	mov    %rbp,%rdi
  401c31:	e8 ba fd ff ff       	call   4019f0 <pollthreads>
  401c36:	4c 63 44 24 0c       	movslq 0xc(%rsp),%r8
  401c3b:	45 85 c0             	test   %r8d,%r8d
  401c3e:	0f 8e 3d 01 00 00    	jle    401d81 <singlewriter+0x1d1>
  401c44:	44 8b 4c 24 14       	mov    0x14(%rsp),%r9d
  401c49:	31 c9                	xor    %ecx,%ecx
  401c4b:	eb 58                	jmp    401ca5 <singlewriter+0xf5>
  401c4d:	0f 1f 00             	nopl   (%rax)
  401c50:	48 8b 04 cb          	mov    (%rbx,%rcx,8),%rax
  401c54:	49 63 54 8d 00       	movslq 0x0(%r13,%rcx,4),%rdx
  401c59:	8d 71 01             	lea    0x1(%rcx),%esi
  401c5c:	48 83 c1 01          	add    $0x1,%rcx
  401c60:	48 c1 e0 05          	shl    $0x5,%rax
  401c64:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
  401c6b:	48 89 d7             	mov    %rdx,%rdi
  401c6e:	48 c1 e2 0a          	shl    $0xa,%rdx
  401c72:	66 0f 6e 00          	movd   (%rax),%xmm0
  401c76:	66 0f 6e 48 08       	movd   0x8(%rax),%xmm1
  401c7b:	c7 40 10 02 00 00 00 	movl   $0x2,0x10(%rax)
  401c82:	48 03 55 30          	add    0x30(%rbp),%rdx
  401c86:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
  401c8a:	48 89 82 a8 00 00 00 	mov    %rax,0xa8(%rdx)
  401c91:	89 78 14             	mov    %edi,0x14(%rax)
  401c94:	83 8a c8 00 00 00 10 	orl    $0x10,0xc8(%rdx)
  401c9b:	66 0f d6 42 14       	movq   %xmm0,0x14(%rdx)
  401ca0:	49 39 c8             	cmp    %rcx,%r8
  401ca3:	74 07                	je     401cac <singlewriter+0xfc>
  401ca5:	89 ce                	mov    %ecx,%esi
  401ca7:	4c 39 c9             	cmp    %r9,%rcx
  401caa:	75 a4                	jne    401c50 <singlewriter+0xa0>
  401cac:	44 8b 4c 24 10       	mov    0x10(%rsp),%r9d
  401cb1:	45 85 c9             	test   %r9d,%r9d
  401cb4:	7e 68                	jle    401d1e <singlewriter+0x16e>
  401cb6:	44 8b 44 24 14       	mov    0x14(%rsp),%r8d
  401cbb:	41 01 f1             	add    %esi,%r9d
  401cbe:	eb 59                	jmp    401d19 <singlewriter+0x169>
  401cc0:	8d 7e 01             	lea    0x1(%rsi),%edi
  401cc3:	48 63 f6             	movslq %esi,%rsi
  401cc6:	49 63 14 24          	movslq (%r12),%rdx
  401cca:	49 83 c4 04          	add    $0x4,%r12
  401cce:	48 8b 04 f3          	mov    (%rbx,%rsi,8),%rax
  401cd2:	48 89 d1             	mov    %rdx,%rcx
  401cd5:	48 c1 e2 0a          	shl    $0xa,%rdx
  401cd9:	48 03 55 30          	add    0x30(%rbp),%rdx
  401cdd:	48 c1 e0 05          	shl    $0x5,%rax
  401ce1:	48 03 85 a0 00 00 00 	add    0xa0(%rbp),%rax
  401ce8:	66 0f 6e 00          	movd   (%rax),%xmm0
  401cec:	66 0f 6e 50 08       	movd   0x8(%rax),%xmm2
  401cf1:	c7 40 10 03 00 00 00 	movl   $0x3,0x10(%rax)
  401cf8:	48 89 82 b0 00 00 00 	mov    %rax,0xb0(%rdx)
  401cff:	66 0f 62 c2          	punpckldq %xmm2,%xmm0
  401d03:	89 48 14             	mov    %ecx,0x14(%rax)
  401d06:	83 8a c8 00 00 00 20 	orl    $0x20,0xc8(%rdx)
  401d0d:	66 0f d6 42 40       	movq   %xmm0,0x40(%rdx)
  401d12:	44 39 cf             	cmp    %r9d,%edi
  401d15:	74 07                	je     401d1e <singlewriter+0x16e>
  401d17:	89 fe                	mov    %edi,%esi
  401d19:	41 39 f0             	cmp    %esi,%r8d
  401d1c:	75 a2                	jne    401cc0 <singlewriter+0x110>
  401d1e:	8b 7d 68             	mov    0x68(%rbp),%edi
  401d21:	85 ff                	test   %edi,%edi
  401d23:	7e 33                	jle    401d58 <singlewriter+0x1a8>
  401d25:	4c 8b 45 30          	mov    0x30(%rbp),%r8
  401d29:	31 d2                	xor    %edx,%edx
  401d2b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  401d30:	48 63 ca             	movslq %edx,%rcx
  401d33:	48 89 c8             	mov    %rcx,%rax
  401d36:	48 c1 e0 0a          	shl    $0xa,%rax
  401d3a:	4c 01 c0             	add    %r8,%rax
  401d3d:	8b b0 c8 00 00 00    	mov    0xc8(%rax),%esi
  401d43:	85 f6                	test   %esi,%esi
  401d45:	74 31                	je     401d78 <singlewriter+0x1c8>
  401d47:	48 8b 40 20          	mov    0x20(%rax),%rax
  401d4b:	83 c2 01             	add    $0x1,%edx
  401d4e:	89 34 88             	mov    %esi,(%rax,%rcx,4)
  401d51:	8b 7d 68             	mov    0x68(%rbp),%edi
  401d54:	39 fa                	cmp    %edi,%edx
  401d56:	7c d8                	jl     401d30 <singlewriter+0x180>
  401d58:	31 c0                	xor    %eax,%eax
  401d5a:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  401d5f:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  401d68:	75 1e                	jne    401d88 <singlewriter+0x1d8>
  401d6a:	48 83 c4 28          	add    $0x28,%rsp
  401d6e:	5b                   	pop    %rbx
  401d6f:	5d                   	pop    %rbp
  401d70:	41 5c                	pop    %r12
  401d72:	41 5d                	pop    %r13
  401d74:	c3                   	ret
  401d75:	0f 1f 00             	nopl   (%rax)
  401d78:	83 c2 01             	add    $0x1,%edx
  401d7b:	39 fa                	cmp    %edi,%edx
  401d7d:	7c b1                	jl     401d30 <singlewriter+0x180>
  401d7f:	eb d7                	jmp    401d58 <singlewriter+0x1a8>
  401d81:	31 f6                	xor    %esi,%esi
  401d83:	e9 24 ff ff ff       	jmp    401cac <singlewriter+0xfc>
  401d88:	e8 e3 f2 ff ff       	call   401070 <__stack_chk_fail@plt>
  401d8d:	0f 1f 00             	nopl   (%rax)

0000000000401d90 <threadwork>:
  401d90:	41 57                	push   %r15
  401d92:	41 56                	push   %r14
  401d94:	41 55                	push   %r13
  401d96:	41 54                	push   %r12
  401d98:	55                   	push   %rbp
  401d99:	53                   	push   %rbx
  401d9a:	48 89 fb             	mov    %rdi,%rbx
  401d9d:	48 83 ec 28          	sub    $0x28,%rsp
  401da1:	48 8b 57 28          	mov    0x28(%rdi),%rdx
  401da5:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  401dae:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  401db3:	31 c0                	xor    %eax,%eax
  401db5:	8b 87 8c 03 00 00    	mov    0x38c(%rdi),%eax
  401dbb:	48 89 e6             	mov    %rsp,%rsi
  401dbe:	bf 04 00 00 00       	mov    $0x4,%edi
  401dc3:	48 8b 92 80 03 00 00 	mov    0x380(%rdx),%rdx
  401dca:	c1 e0 07             	shl    $0x7,%eax
  401dcd:	48 98                	cltq
  401dcf:	48 8b 2c c2          	mov    (%rdx,%rax,8),%rbp
  401dd3:	e8 88 f2 ff ff       	call   401060 <clock_gettime@plt>
  401dd8:	8b b3 8c 03 00 00    	mov    0x38c(%rbx),%esi
  401dde:	4c 8b 43 28          	mov    0x28(%rbx),%r8
  401de2:	48 83 43 50 01       	addq   $0x1,0x50(%rbx)
  401de7:	4c 63 4b 68          	movslq 0x68(%rbx),%r9
  401deb:	89 f0                	mov    %esi,%eax
  401ded:	49 8b 90 80 03 00 00 	mov    0x380(%r8),%rdx
  401df4:	4c 63 63 64          	movslq 0x64(%rbx),%r12
  401df8:	c1 e0 07             	shl    $0x7,%eax
  401dfb:	66 0f 6f 04 24       	movdqa (%rsp),%xmm0
  401e00:	48 98                	cltq
  401e02:	4c 89 e7             	mov    %r12,%rdi
  401e05:	48 8b 04 c2          	mov    (%rdx,%rax,8),%rax
  401e09:	48 99                	cqto
  401e0b:	49 f7 f9             	idiv   %r9
  401e0e:	48 ba 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%rdx
  401e18:	48 89 c1             	mov    %rax,%rcx
  401e1b:	48 f7 ea             	imul   %rdx
  401e1e:	48 89 c8             	mov    %rcx,%rax
  401e21:	48 c1 f8 3f          	sar    $0x3f,%rax
  401e25:	48 01 ca             	add    %rcx,%rdx
  401e28:	48 c1 fa 07          	sar    $0x7,%rdx
  401e2c:	48 29 c2             	sub    %rax,%rdx
  401e2f:	48 89 d0             	mov    %rdx,%rax
  401e32:	48 c1 e0 08          	shl    $0x8,%rax
  401e36:	48 29 d0             	sub    %rdx,%rax
  401e39:	48 29 c1             	sub    %rax,%rcx
  401e3c:	89 f0                	mov    %esi,%eax
  401e3e:	c1 e0 18             	shl    $0x18,%eax
  401e41:	48 c1 e1 10          	shl    $0x10,%rcx
  401e45:	44 09 e0             	or     %r12d,%eax
  401e48:	49 c1 e4 0a          	shl    $0xa,%r12
  401e4c:	4c 03 63 30          	add    0x30(%rbx),%r12
  401e50:	49 63 94 24 24 03 00 00 	movslq 0x324(%r12),%rdx
  401e58:	48 98                	cltq
  401e5a:	48 09 c1             	or     %rax,%rcx
  401e5d:	48 89 d0             	mov    %rdx,%rax
  401e60:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
  401e64:	83 c0 01             	add    $0x1,%eax
  401e67:	48 c1 e6 04          	shl    $0x4,%rsi
  401e6b:	49 03 b4 24 18 03 00 00 	add    0x318(%r12),%rsi
  401e73:	99                   	cltd
  401e74:	0f 11 46 08          	movups %xmm0,0x8(%rsi)
  401e78:	41 f7 bc 24 20 03 00 00 	idivl  0x320(%r12)
  401e80:	49 8b 40 70          	mov    0x70(%r8),%rax
  401e84:	41 89 94 24 24 03 00 00 	mov    %edx,0x324(%r12)
  401e8c:	89 3e                	mov    %edi,(%rsi)
  401e8e:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
  401e92:	c7 46 24 01 00 00 00 	movl   $0x1,0x24(%rsi)
  401e99:	40 88 3c 08          	mov    %dil,(%rax,%rcx,1)
  401e9d:	48 8b 53 28          	mov    0x28(%rbx),%rdx
  401ea1:	8b 83 8c 03 00 00    	mov    0x38c(%rbx),%eax
  401ea7:	48 8b 92 80 03 00 00 	mov    0x380(%rdx),%rdx
  401eae:	c1 e0 07             	shl    $0x7,%eax
  401eb1:	48 98                	cltq
  401eb3:	f0 48 83 04 c2 01    	lock addq $0x1,(%rdx,%rax,8)
  401eb9:	48 8b 43 28          	mov    0x28(%rbx),%rax
  401ebd:	48 63 93 8c 03 00 00 	movslq 0x38c(%rbx),%rdx
  401ec4:	48 63 4b 68          	movslq 0x68(%rbx),%rcx
  401ec8:	48 8b 80 80 03 00 00 	mov    0x380(%rax),%rax
  401ecf:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
  401ed3:	48 99                	cqto
  401ed5:	48 f7 f9             	idiv   %rcx
  401ed8:	49 89 c5             	mov    %rax,%r13
  401edb:	48 63 83 88 03 00 00 	movslq 0x388(%rbx),%rax
  401ee2:	4c 39 e8             	cmp    %r13,%rax
  401ee5:	74 5a                	je     401f41 <threadwork+0x1b1>
  401ee7:	4c 63 73 64          	movslq 0x64(%rbx),%r14
  401eeb:	bf 04 00 00 00       	mov    $0x4,%edi
  401ef0:	49 c1 e6 0a          	shl    $0xa,%r14
  401ef4:	4c 03 73 30          	add    0x30(%rbx),%r14
  401ef8:	49 63 86 24 03 00 00 	movslq 0x324(%r14),%rax
  401eff:	4c 8d 3c 40          	lea    (%rax,%rax,2),%r15
  401f03:	49 c1 e7 04          	shl    $0x4,%r15
  401f07:	4d 03 be 18 03 00 00 	add    0x318(%r14),%r15
  401f0e:	49 8d 77 08          	lea    0x8(%r15),%rsi
  401f12:	e8 49 f1 ff ff       	call   401060 <clock_gettime@plt>
  401f17:	41 8b 86 24 03 00 00 	mov    0x324(%r14),%eax
  401f1e:	83 c0 01             	add    $0x1,%eax
  401f21:	99                   	cltd
  401f22:	41 f7 be 20 03 00 00 	idivl  0x320(%r14)
  401f29:	8b 43 64             	mov    0x64(%rbx),%eax
  401f2c:	41 89 96 24 03 00 00 	mov    %edx,0x324(%r14)
  401f33:	41 89 07             	mov    %eax,(%r15)
  401f36:	48 8b 05 b3 12 00 00 	mov    0x12b3(%rip),%rax        # 4031f0 <_IO_stdin_used+0x1f0>
  401f3d:	49 89 47 20          	mov    %rax,0x20(%r15)
  401f41:	48 8b 8b 48 03 00 00 	mov    0x348(%rbx),%rcx
  401f48:	44 89 ab 88 03 00 00 	mov    %r13d,0x388(%rbx)
  401f4f:	48 39 e9             	cmp    %rbp,%rcx
  401f52:	0f 8d 1d 01 00 00    	jge    402075 <threadwork+0x2e5>
  401f58:	49 63 94 24 24 03 00 00 	movslq 0x324(%r12),%rdx
  401f60:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
  401f65:	4c 63 43 68          	movslq 0x68(%rbx),%r8
  401f69:	8b b3 00 02 00 00    	mov    0x200(%rbx),%esi
  401f6f:	48 89 d0             	mov    %rdx,%rax
  401f72:	48 8d 3c 52          	lea    (%rdx,%rdx,2),%rdi
  401f76:	48 83 43 48 01       	addq   $0x1,0x48(%rbx)
  401f7b:	44 8b 5b 64          	mov    0x64(%rbx),%r11d
  401f7f:	83 c0 01             	add    $0x1,%eax
  401f82:	48 c1 e7 04          	shl    $0x4,%rdi
  401f86:	44 8b 93 90 03 00 00 	mov    0x390(%rbx),%r10d
  401f8d:	4d 89 c1             	mov    %r8,%r9
  401f90:	99                   	cltd
  401f91:	49 03 bc 24 18 03 00 00 	add    0x318(%r12),%rdi
  401f99:	41 f7 bc 24 20 03 00 00 	idivl  0x320(%r12)
  401fa1:	0f 11 4f 08          	movups %xmm1,0x8(%rdi)
  401fa5:	48 89 c8             	mov    %rcx,%rax
  401fa8:	41 89 94 24 24 03 00 00 	mov    %edx,0x324(%r12)
  401fb0:	48 99                	cqto
  401fb2:	41 89 f4             	mov    %esi,%r12d
  401fb5:	49 f7 f8             	idiv   %r8
  401fb8:	44 89 1f             	mov    %r11d,(%rdi)
  401fbb:	c7 47 24 01 00 00 00 	movl   $0x1,0x24(%rdi)
  401fc2:	48 ba 81 80 80 80 80 80 80 80 	movabs $0x8080808080808081,%rdx
  401fcc:	48 8d 68 fe          	lea    -0x2(%rax),%rbp
  401fd0:	48 89 e8             	mov    %rbp,%rax
  401fd3:	48 f7 ea             	imul   %rdx
  401fd6:	48 89 e8             	mov    %rbp,%rax
  401fd9:	48 c1 f8 3f          	sar    $0x3f,%rax
  401fdd:	48 01 ea             	add    %rbp,%rdx
  401fe0:	48 c1 fa 07          	sar    $0x7,%rdx
  401fe4:	48 29 c2             	sub    %rax,%rdx
  401fe7:	48 89 d0             	mov    %rdx,%rax
  401fea:	48 c1 e0 08          	shl    $0x8,%rax
  401fee:	48 29 d0             	sub    %rdx,%rax
  401ff1:	48 89 ea             	mov    %rbp,%rdx
  401ff4:	44 89 d5             	mov    %r10d,%ebp
  401ff7:	48 29 c2             	sub    %rax,%rdx
  401ffa:	b8 00 00 00 00       	mov    $0x0,%eax
  401fff:	48 0f 48 d0          	cmovs  %rax,%rdx
  402003:	48 63 c6             	movslq %esi,%rax
  402006:	41 c1 fc 1f          	sar    $0x1f,%r12d
  40200a:	48 69 c0 81 80 80 80 	imul   $0xffffffff80808081,%rax,%rax
  402011:	c1 e5 18             	shl    $0x18,%ebp
  402014:	48 c1 e2 10          	shl    $0x10,%rdx
  402018:	48 c1 e8 20          	shr    $0x20,%rax
  40201c:	01 f0                	add    %esi,%eax
  40201e:	c1 f8 07             	sar    $0x7,%eax
  402021:	44 29 e0             	sub    %r12d,%eax
  402024:	41 89 c4             	mov    %eax,%r12d
  402027:	41 c1 e4 08          	shl    $0x8,%r12d
  40202b:	41 29 c4             	sub    %eax,%r12d
  40202e:	89 f0                	mov    %esi,%eax
  402030:	44 29 e0             	sub    %r12d,%eax
  402033:	09 c5                	or     %eax,%ebp
  402035:	8d 46 01             	lea    0x1(%rsi),%eax
  402038:	48 63 ed             	movslq %ebp,%rbp
  40203b:	48 09 ea             	or     %rbp,%rdx
  40203e:	48 89 57 18          	mov    %rdx,0x18(%rdi)
  402042:	41 39 c0             	cmp    %eax,%r8d
  402045:	74 59                	je     4020a0 <threadwork+0x310>
  402047:	99                   	cltd
  402048:	41 f7 f9             	idiv   %r9d
  40204b:	41 8d 43 01          	lea    0x1(%r11),%eax
  40204f:	41 39 d3             	cmp    %edx,%r11d
  402052:	0f 45 c2             	cmovne %edx,%eax
  402055:	89 c6                	mov    %eax,%esi
  402057:	48 8d 41 01          	lea    0x1(%rcx),%rax
  40205b:	48 99                	cqto
  40205d:	48 89 83 48 03 00 00 	mov    %rax,0x348(%rbx)
  402064:	49 f7 f8             	idiv   %r8
  402067:	31 c0                	xor    %eax,%eax
  402069:	48 85 d2             	test   %rdx,%rdx
  40206c:	0f 45 c6             	cmovne %esi,%eax
  40206f:	89 83 00 02 00 00    	mov    %eax,0x200(%rbx)
  402075:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  40207a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  402083:	75 77                	jne    4020fc <threadwork+0x36c>
  402085:	48 83 c4 28          	add    $0x28,%rsp
  402089:	31 c0                	xor    %eax,%eax
  40208b:	5b                   	pop    %rbx
  40208c:	5d                   	pop    %rbp
  40208d:	41 5c                	pop    %r12
  40208f:	41 5d                	pop    %r13
  402091:	41 5e                	pop    %r14
  402093:	41 5f                	pop    %r15
  402095:	c3                   	ret
  402096:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4020a0:	41 83 c2 01          	add    $0x1,%r10d
  4020a4:	49 63 d2             	movslq %r10d,%rdx
  4020a7:	44 89 d6             	mov    %r10d,%esi
  4020aa:	48 69 d2 67 66 66 66 	imul   $0x66666667,%rdx,%rdx
  4020b1:	c1 fe 1f             	sar    $0x1f,%esi
  4020b4:	48 c1 fa 21          	sar    $0x21,%rdx
  4020b8:	29 f2                	sub    %esi,%edx
  4020ba:	8d 34 92             	lea    (%rdx,%rdx,4),%esi
  4020bd:	44 89 d2             	mov    %r10d,%edx
  4020c0:	29 f2                	sub    %esi,%edx
  4020c2:	89 93 90 03 00 00    	mov    %edx,0x390(%rbx)
  4020c8:	3b 93 8c 03 00 00    	cmp    0x38c(%rbx),%edx
  4020ce:	0f 85 73 ff ff ff    	jne    402047 <threadwork+0x2b7>
  4020d4:	83 c2 01             	add    $0x1,%edx
  4020d7:	48 63 f2             	movslq %edx,%rsi
  4020da:	89 d7                	mov    %edx,%edi
  4020dc:	48 69 f6 67 66 66 66 	imul   $0x66666667,%rsi,%rsi
  4020e3:	c1 ff 1f             	sar    $0x1f,%edi
  4020e6:	48 c1 fe 21          	sar    $0x21,%rsi
  4020ea:	29 fe                	sub    %edi,%esi
  4020ec:	8d 34 b6             	lea    (%rsi,%rsi,4),%esi
  4020ef:	29 f2                	sub    %esi,%edx
  4020f1:	89 93 90 03 00 00    	mov    %edx,0x390(%rbx)
  4020f7:	e9 4b ff ff ff       	jmp    402047 <threadwork+0x2b7>
  4020fc:	e8 6f ef ff ff       	call   401070 <__stack_chk_fail@plt>
  402101:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40210c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000402110 <work>:
  402110:	53                   	push   %rbx
  402111:	8b 57 64             	mov    0x64(%rdi),%edx
  402114:	48 89 fb             	mov    %rdi,%rbx
  402117:	31 c0                	xor    %eax,%eax
  402119:	48 8d 35 e4 0e 00 00 	lea    0xee4(%rip),%rsi        # 403004 <_IO_stdin_used+0x4>
  402120:	bf 01 00 00 00       	mov    $0x1,%edi
  402125:	e8 96 ef ff ff       	call   4010c0 <__printf_chk@plt>
  40212a:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  40212e:	75 0e                	jne    40213e <work+0x2e>
  402130:	48 89 df             	mov    %rbx,%rdi
  402133:	e8 58 fc ff ff       	call   401d90 <threadwork>
  402138:	83 7b 5c 01          	cmpl   $0x1,0x5c(%rbx)
  40213c:	74 f2                	je     402130 <work+0x20>
  40213e:	8b 53 64             	mov    0x64(%rbx),%edx
  402141:	48 8d 35 cf 0e 00 00 	lea    0xecf(%rip),%rsi        # 403017 <_IO_stdin_used+0x17>
  402148:	bf 01 00 00 00       	mov    $0x1,%edi
  40214d:	31 c0                	xor    %eax,%eax
  40214f:	e8 6c ef ff ff       	call   4010c0 <__printf_chk@plt>
  402154:	5b                   	pop    %rbx
  402155:	c3                   	ret
  402156:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000402160 <work2>:
  402160:	eb 0b                	jmp    40216d <work2+0xd>
  402162:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  402168:	48 83 47 48 01       	addq   $0x1,0x48(%rdi)
  40216d:	83 7f 5c 01          	cmpl   $0x1,0x5c(%rdi)
  402171:	74 f5                	je     402168 <work2+0x8>
  402173:	c3                   	ret

Disassembly of section .fini:

0000000000402174 <_fini>:
  402174:	f3 0f 1e fa          	endbr64
  402178:	48 83 ec 08          	sub    $0x8,%rsp
  40217c:	48 83 c4 08          	add    $0x8,%rsp
  402180:	c3                   	ret
