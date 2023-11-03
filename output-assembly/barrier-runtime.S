
barrier-runtime:     file format elf64-x86-64


Disassembly of section .init:

0000000000001000 <_init>:
    1000:	f3 0f 1e fa          	endbr64
    1004:	48 83 ec 08          	sub    $0x8,%rsp
    1008:	48 8b 05 d9 3f 00 00 	mov    0x3fd9(%rip),%rax        # 4fe8 <__gmon_start__@Base>
    100f:	48 85 c0             	test   %rax,%rax
    1012:	74 02                	je     1016 <_init+0x16>
    1014:	ff d0                	call   *%rax
    1016:	48 83 c4 08          	add    $0x8,%rsp
    101a:	c3                   	ret

Disassembly of section .plt:

0000000000001020 <.plt>:
    1020:	ff 35 3a 3f 00 00    	push   0x3f3a(%rip)        # 4f60 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:	ff 25 3c 3f 00 00    	jmp    *0x3f3c(%rip)        # 4f68 <_GLOBAL_OFFSET_TABLE_+0x10>
    102c:	0f 1f 40 00          	nopl   0x0(%rax)
    1030:	f3 0f 1e fa          	endbr64
    1034:	68 00 00 00 00       	push   $0x0
    1039:	e9 e2 ff ff ff       	jmp    1020 <_init+0x20>
    103e:	66 90                	xchg   %ax,%ax
    1040:	f3 0f 1e fa          	endbr64
    1044:	68 01 00 00 00       	push   $0x1
    1049:	e9 d2 ff ff ff       	jmp    1020 <_init+0x20>
    104e:	66 90                	xchg   %ax,%ax
    1050:	f3 0f 1e fa          	endbr64
    1054:	68 02 00 00 00       	push   $0x2
    1059:	e9 c2 ff ff ff       	jmp    1020 <_init+0x20>
    105e:	66 90                	xchg   %ax,%ax
    1060:	f3 0f 1e fa          	endbr64
    1064:	68 03 00 00 00       	push   $0x3
    1069:	e9 b2 ff ff ff       	jmp    1020 <_init+0x20>
    106e:	66 90                	xchg   %ax,%ax
    1070:	f3 0f 1e fa          	endbr64
    1074:	68 04 00 00 00       	push   $0x4
    1079:	e9 a2 ff ff ff       	jmp    1020 <_init+0x20>
    107e:	66 90                	xchg   %ax,%ax
    1080:	f3 0f 1e fa          	endbr64
    1084:	68 05 00 00 00       	push   $0x5
    1089:	e9 92 ff ff ff       	jmp    1020 <_init+0x20>
    108e:	66 90                	xchg   %ax,%ax
    1090:	f3 0f 1e fa          	endbr64
    1094:	68 06 00 00 00       	push   $0x6
    1099:	e9 82 ff ff ff       	jmp    1020 <_init+0x20>
    109e:	66 90                	xchg   %ax,%ax
    10a0:	f3 0f 1e fa          	endbr64
    10a4:	68 07 00 00 00       	push   $0x7
    10a9:	e9 72 ff ff ff       	jmp    1020 <_init+0x20>
    10ae:	66 90                	xchg   %ax,%ax
    10b0:	f3 0f 1e fa          	endbr64
    10b4:	68 08 00 00 00       	push   $0x8
    10b9:	e9 62 ff ff ff       	jmp    1020 <_init+0x20>
    10be:	66 90                	xchg   %ax,%ax
    10c0:	f3 0f 1e fa          	endbr64
    10c4:	68 09 00 00 00       	push   $0x9
    10c9:	e9 52 ff ff ff       	jmp    1020 <_init+0x20>
    10ce:	66 90                	xchg   %ax,%ax
    10d0:	f3 0f 1e fa          	endbr64
    10d4:	68 0a 00 00 00       	push   $0xa
    10d9:	e9 42 ff ff ff       	jmp    1020 <_init+0x20>
    10de:	66 90                	xchg   %ax,%ax
    10e0:	f3 0f 1e fa          	endbr64
    10e4:	68 0b 00 00 00       	push   $0xb
    10e9:	e9 32 ff ff ff       	jmp    1020 <_init+0x20>
    10ee:	66 90                	xchg   %ax,%ax
    10f0:	f3 0f 1e fa          	endbr64
    10f4:	68 0c 00 00 00       	push   $0xc
    10f9:	e9 22 ff ff ff       	jmp    1020 <_init+0x20>
    10fe:	66 90                	xchg   %ax,%ax

Disassembly of section .plt.got:

0000000000001100 <__cxa_finalize@plt>:
    1100:	f3 0f 1e fa          	endbr64
    1104:	ff 25 ee 3e 00 00    	jmp    *0x3eee(%rip)        # 4ff8 <__cxa_finalize@GLIBC_2.2.5>
    110a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000001110 <putchar@plt>:
    1110:	f3 0f 1e fa          	endbr64
    1114:	ff 25 56 3e 00 00    	jmp    *0x3e56(%rip)        # 4f70 <putchar@GLIBC_2.2.5>
    111a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001120 <puts@plt>:
    1120:	f3 0f 1e fa          	endbr64
    1124:	ff 25 4e 3e 00 00    	jmp    *0x3e4e(%rip)        # 4f78 <puts@GLIBC_2.2.5>
    112a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001130 <clock_gettime@plt>:
    1130:	f3 0f 1e fa          	endbr64
    1134:	ff 25 46 3e 00 00    	jmp    *0x3e46(%rip)        # 4f80 <clock_gettime@GLIBC_2.17>
    113a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001140 <__stack_chk_fail@plt>:
    1140:	f3 0f 1e fa          	endbr64
    1144:	ff 25 3e 3e 00 00    	jmp    *0x3e3e(%rip)        # 4f88 <__stack_chk_fail@GLIBC_2.4>
    114a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001150 <nanosleep@plt>:
    1150:	f3 0f 1e fa          	endbr64
    1154:	ff 25 36 3e 00 00    	jmp    *0x3e36(%rip)        # 4f90 <nanosleep@GLIBC_2.2.5>
    115a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001160 <calloc@plt>:
    1160:	f3 0f 1e fa          	endbr64
    1164:	ff 25 2e 3e 00 00    	jmp    *0x3e2e(%rip)        # 4f98 <calloc@GLIBC_2.2.5>
    116a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001170 <io_uring_queue_init@plt>:
    1170:	f3 0f 1e fa          	endbr64
    1174:	ff 25 26 3e 00 00    	jmp    *0x3e26(%rip)        # 4fa0 <io_uring_queue_init@LIBURING_2.0>
    117a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001180 <malloc@plt>:
    1180:	f3 0f 1e fa          	endbr64
    1184:	ff 25 1e 3e 00 00    	jmp    *0x3e1e(%rip)        # 4fa8 <malloc@GLIBC_2.2.5>
    118a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001190 <__printf_chk@plt>:
    1190:	f3 0f 1e fa          	endbr64
    1194:	ff 25 16 3e 00 00    	jmp    *0x3e16(%rip)        # 4fb0 <__printf_chk@GLIBC_2.3.4>
    119a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011a0 <pthread_create@plt>:
    11a0:	f3 0f 1e fa          	endbr64
    11a4:	ff 25 0e 3e 00 00    	jmp    *0x3e0e(%rip)        # 4fb8 <pthread_create@GLIBC_2.34>
    11aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011b0 <exit@plt>:
    11b0:	f3 0f 1e fa          	endbr64
    11b4:	ff 25 06 3e 00 00    	jmp    *0x3e06(%rip)        # 4fc0 <exit@GLIBC_2.2.5>
    11ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011c0 <pthread_join@plt>:
    11c0:	f3 0f 1e fa          	endbr64
    11c4:	ff 25 fe 3d 00 00    	jmp    *0x3dfe(%rip)        # 4fc8 <pthread_join@GLIBC_2.34>
    11ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011d0 <__sprintf_chk@plt>:
    11d0:	f3 0f 1e fa          	endbr64
    11d4:	ff 25 f6 3d 00 00    	jmp    *0x3df6(%rip)        # 4fd0 <__sprintf_chk@GLIBC_2.3.4>
    11da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

00000000000011e0 <main>:
    11e0:	f3 0f 1e fa          	endbr64
    11e4:	41 57                	push   %r15
    11e6:	48 8d 3d 1b 20 00 00 	lea    0x201b(%rip),%rdi        # 3208 <_IO_stdin_used+0x208>
    11ed:	41 56                	push   %r14
    11ef:	41 55                	push   %r13
    11f1:	41 54                	push   %r12
    11f3:	55                   	push   %rbp
    11f4:	53                   	push   %rbx
    11f5:	48 83 ec 68          	sub    $0x68,%rsp
    11f9:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1202:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    1207:	31 c0                	xor    %eax,%eax
    1209:	e8 12 ff ff ff       	call   1120 <puts@plt>
    120e:	ba 0a 00 00 00       	mov    $0xa,%edx
    1213:	48 8d 35 b2 1e 00 00 	lea    0x1eb2(%rip),%rsi        # 30cc <_IO_stdin_used+0xcc>
    121a:	31 c0                	xor    %eax,%eax
    121c:	bf 01 00 00 00       	mov    $0x1,%edi
    1221:	e8 6a ff ff ff       	call   1190 <__printf_chk@plt>
    1226:	ba 7f 96 98 00       	mov    $0x98967f,%edx
    122b:	48 8d 35 06 20 00 00 	lea    0x2006(%rip),%rsi        # 3238 <_IO_stdin_used+0x238>
    1232:	31 c0                	xor    %eax,%eax
    1234:	bf 01 00 00 00       	mov    $0x1,%edi
    1239:	e8 52 ff ff ff       	call   1190 <__printf_chk@plt>
    123e:	ba 9f 86 01 00       	mov    $0x1869f,%edx
    1243:	48 8d 35 1e 20 00 00 	lea    0x201e(%rip),%rsi        # 3268 <_IO_stdin_used+0x268>
    124a:	31 c0                	xor    %eax,%eax
    124c:	bf 01 00 00 00       	mov    $0x1,%edi
    1251:	e8 3a ff ff ff       	call   1190 <__printf_chk@plt>
    1256:	be 18 00 00 00       	mov    $0x18,%esi
    125b:	bf 01 00 00 00       	mov    $0x1,%edi
    1260:	e8 fb fe ff ff       	call   1160 <calloc@plt>
    1265:	be 40 00 00 00       	mov    $0x40,%esi
    126a:	bf 0f 00 00 00       	mov    $0xf,%edi
    126f:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    1274:	e8 e7 fe ff ff       	call   1160 <calloc@plt>
    1279:	be 10 00 00 00       	mov    $0x10,%esi
    127e:	bf 03 00 00 00       	mov    $0x3,%edi
    1283:	49 89 c5             	mov    %rax,%r13
    1286:	e8 d5 fe ff ff       	call   1160 <calloc@plt>
    128b:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    1290:	48 89 c3             	mov    %rax,%rbx
    1293:	48 8d 68 30          	lea    0x30(%rax),%rbp
    1297:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    129c:	c7 03 7f 96 98 00    	movl   $0x98967f,(%rbx)
    12a2:	be 10 00 00 00       	mov    $0x10,%esi
    12a7:	bf 7f 96 98 00       	mov    $0x98967f,%edi
    12ac:	e8 af fe ff ff       	call   1160 <calloc@plt>
    12b1:	48 89 43 08          	mov    %rax,0x8(%rbx)
    12b5:	48 8d 90 f0 67 89 09 	lea    0x98967f0(%rax),%rdx
    12bc:	0f 1f 40 00          	nopl   0x0(%rax)
    12c0:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    12c7:	48 83 c0 10          	add    $0x10,%rax
    12cb:	48 39 d0             	cmp    %rdx,%rax
    12ce:	75 f0                	jne    12c0 <main+0xe0>
    12d0:	48 83 c3 10          	add    $0x10,%rbx
    12d4:	48 39 eb             	cmp    %rbp,%rbx
    12d7:	75 c3                	jne    129c <main+0xbc>
    12d9:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
    12e1:	31 c9                	xor    %ecx,%ecx
    12e3:	4d 89 ef             	mov    %r13,%r15
    12e6:	4c 89 6c 24 38       	mov    %r13,0x38(%rsp)
    12eb:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    12f0:	41 89 0f             	mov    %ecx,(%r15)
    12f3:	be 98 00 00 00       	mov    $0x98,%esi
    12f8:	31 ed                	xor    %ebp,%ebp
    12fa:	41 c7 47 28 0b 00 00 00 	movl   $0xb,0x28(%r15)
    1302:	bf 0b 00 00 00       	mov    $0xb,%edi
    1307:	49 89 47 10          	mov    %rax,0x10(%r15)
    130b:	48 8b 05 ce 20 00 00 	mov    0x20ce(%rip),%rax        # 33e0 <_IO_stdin_used+0x3e0>
    1312:	89 4c 24 20          	mov    %ecx,0x20(%rsp)
    1316:	49 89 47 18          	mov    %rax,0x18(%r15)
    131a:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    131f:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    1324:	49 89 47 30          	mov    %rax,0x30(%r15)
    1328:	e8 33 fe ff ff       	call   1160 <calloc@plt>
    132d:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    1332:	48 89 c3             	mov    %rax,%rbx
    1335:	49 89 47 20          	mov    %rax,0x20(%r15)
    1339:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
    133e:	89 ce                	mov    %ecx,%esi
    1340:	89 4c 24 24          	mov    %ecx,0x24(%rsp)
    1344:	48 89 da             	mov    %rbx,%rdx
    1347:	48 0f af f0          	imul   %rax,%rsi
    134b:	48 c1 ee 21          	shr    $0x21,%rsi
    134f:	8d 04 76             	lea    (%rsi,%rsi,2),%eax
    1352:	89 ce                	mov    %ecx,%esi
    1354:	29 c6                	sub    %eax,%esi
    1356:	89 74 24 2c          	mov    %esi,0x2c(%rsp)
    135a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1360:	4c 63 ed             	movslq %ebp,%r13
    1363:	4b 8d 44 ed 00       	lea    0x0(%r13,%r13,8),%rax
    1368:	4d 8d 64 45 00       	lea    0x0(%r13,%rax,2),%r12
    136d:	8b 44 24 08          	mov    0x8(%rsp),%eax
    1371:	49 c1 e4 03          	shl    $0x3,%r12
    1375:	4a 8d 1c 22          	lea    (%rdx,%r12,1),%rbx
    1379:	39 c5                	cmp    %eax,%ebp
    137b:	0f 84 6f 08 00 00    	je     1bf0 <main+0xa10>
    1381:	be 20 00 00 00       	mov    $0x20,%esi
    1386:	bf 0a 00 00 00       	mov    $0xa,%edi
    138b:	e8 d0 fd ff ff       	call   1160 <calloc@plt>
    1390:	89 6c 24 10          	mov    %ebp,0x10(%rsp)
    1394:	4c 89 64 24 18       	mov    %r12,0x18(%rsp)
    1399:	49 89 c6             	mov    %rax,%r14
    139c:	48 89 43 70          	mov    %rax,0x70(%rbx)
    13a0:	48 8d 98 40 01 00 00 	lea    0x140(%rax),%rbx
    13a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    13b0:	be 08 00 00 00       	mov    $0x8,%esi
    13b5:	bf 9f 86 01 00       	mov    $0x1869f,%edi
    13ba:	49 83 c6 20          	add    $0x20,%r14
    13be:	e8 9d fd ff ff       	call   1160 <calloc@plt>
    13c3:	be 08 00 00 00       	mov    $0x8,%esi
    13c8:	bf 9f 86 01 00       	mov    $0x1869f,%edi
    13cd:	49 89 c4             	mov    %rax,%r12
    13d0:	e8 8b fd ff ff       	call   1160 <calloc@plt>
    13d5:	be 18 00 00 00       	mov    $0x18,%esi
    13da:	bf 02 00 00 00       	mov    $0x2,%edi
    13df:	48 89 c5             	mov    %rax,%rbp
    13e2:	e8 79 fd ff ff       	call   1160 <calloc@plt>
    13e7:	48 8d 70 18          	lea    0x18(%rax),%rsi
    13eb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    13f3:	49 89 46 e0          	mov    %rax,-0x20(%r14)
    13f7:	49 89 76 e8          	mov    %rsi,-0x18(%r14)
    13fb:	4c 89 20             	mov    %r12,(%rax)
    13fe:	48 89 68 18          	mov    %rbp,0x18(%rax)
    1402:	48 c7 40 10 9f 86 01 00 	movq   $0x1869f,0x10(%rax)
    140a:	48 c7 40 20 00 00 00 00 	movq   $0x0,0x20(%rax)
    1412:	48 c7 40 28 9f 86 01 00 	movq   $0x1869f,0x28(%rax)
    141a:	49 39 de             	cmp    %rbx,%r14
    141d:	75 91                	jne    13b0 <main+0x1d0>
    141f:	be 01 00 00 00       	mov    $0x1,%esi
    1424:	bf 00 01 00 00       	mov    $0x100,%edi
    1429:	8b 6c 24 10          	mov    0x10(%rsp),%ebp
    142d:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    1432:	e8 29 fd ff ff       	call   1160 <calloc@plt>
    1437:	bf 18 00 00 00       	mov    $0x18,%edi
    143c:	48 89 c3             	mov    %rax,%rbx
    143f:	e8 3c fd ff ff       	call   1180 <malloc@plt>
    1444:	44 8b 74 24 20       	mov    0x20(%rsp),%r14d
    1449:	48 89 df             	mov    %rbx,%rdi
    144c:	41 89 e9             	mov    %ebp,%r9d
    144f:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    1454:	48 8d 0d 35 1e 00 00 	lea    0x1e35(%rip),%rcx        # 3290 <_IO_stdin_used+0x290>
    145b:	ba 00 01 00 00       	mov    $0x100,%edx
    1460:	31 c0                	xor    %eax,%eax
    1462:	45 89 f0             	mov    %r14d,%r8d
    1465:	be 01 00 00 00       	mov    $0x1,%esi
    146a:	e8 61 fd ff ff       	call   11d0 <__sprintf_chk@plt>
    146f:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    1474:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    1479:	b9 cd cc cc cc       	mov    $0xcccccccd,%ecx
    147e:	49 8b 57 20          	mov    0x20(%r15),%rdx
    1482:	be 20 00 00 00       	mov    $0x20,%esi
    1487:	49 89 42 08          	mov    %rax,0x8(%r10)
    148b:	8d 45 01             	lea    0x1(%rbp),%eax
    148e:	49 89 1a             	mov    %rbx,(%r10)
    1491:	48 89 c3             	mov    %rax,%rbx
    1494:	48 0f af c1          	imul   %rcx,%rax
    1498:	4d 89 6a 10          	mov    %r13,0x10(%r10)
    149c:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
    14a0:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    14a5:	48 c1 e8 23          	shr    $0x23,%rax
    14a9:	8d 0c 80             	lea    (%rax,%rax,4),%ecx
    14ac:	89 d8                	mov    %ebx,%eax
    14ae:	01 c9                	add    %ecx,%ecx
    14b0:	29 c8                	sub    %ecx,%eax
    14b2:	41 89 85 90 00 00 00 	mov    %eax,0x90(%r13)
    14b9:	4d 89 95 88 00 00 00 	mov    %r10,0x88(%r13)
    14c0:	41 c7 85 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r13)
    14cb:	49 c7 45 58 3f 42 0f 00 	movq   $0xf423f,0x58(%r13)
    14d3:	49 8b 7d 58          	mov    0x58(%r13),%rdi
    14d7:	e8 84 fc ff ff       	call   1160 <calloc@plt>
    14dc:	83 fd 09             	cmp    $0x9,%ebp
    14df:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    14e4:	49 89 45 50          	mov    %rax,0x50(%r13)
    14e8:	49 c7 45 60 00 00 00 00 	movq   $0x0,0x60(%r13)
    14f0:	45 89 75 38          	mov    %r14d,0x38(%r13)
    14f4:	4d 89 7d 30          	mov    %r15,0x30(%r13)
    14f8:	41 c7 45 40 01 00 00 00 	movl   $0x1,0x40(%r13)
    1500:	41 c7 45 08 00 00 00 00 	movl   $0x0,0x8(%r13)
    1508:	41 c7 45 3c 0a 00 00 00 	movl   $0xa,0x3c(%r13)
    1510:	41 c7 45 44 0b 00 00 00 	movl   $0xb,0x44(%r13)
    1518:	41 c7 85 84 00 00 00 0a 00 00 00 	movl   $0xa,0x84(%r13)
    1523:	41 89 6d 00          	mov    %ebp,0x0(%r13)
    1527:	0f 84 a3 06 00 00    	je     1bd0 <main+0x9f0>
    152d:	8b 44 24 24          	mov    0x24(%rsp),%eax
    1531:	39 c5                	cmp    %eax,%ebp
    1533:	75 12                	jne    1547 <main+0x367>
    1535:	83 7c 24 28 02       	cmpl   $0x2,0x28(%rsp)
    153a:	7f 0b                	jg     1547 <main+0x367>
    153c:	83 7c 24 2c 01       	cmpl   $0x1,0x2c(%rsp)
    1541:	0f 84 b9 06 00 00    	je     1c00 <main+0xa20>
    1547:	48 8d 05 d2 0f 00 00 	lea    0xfd2(%rip),%rax        # 2520 <barriered_work>
    154e:	49 89 45 20          	mov    %rax,0x20(%r13)
    1552:	83 fb 0b             	cmp    $0xb,%ebx
    1555:	74 07                	je     155e <main+0x37e>
    1557:	89 dd                	mov    %ebx,%ebp
    1559:	e9 02 fe ff ff       	jmp    1360 <main+0x180>
    155e:	48 8d 05 7b 09 00 00 	lea    0x97b(%rip),%rax        # 1ee0 <barriered_reset>
    1565:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    156a:	48 89 82 10 06 00 00 	mov    %rax,0x610(%rdx)
    1571:	8b 44 24 20          	mov    0x20(%rsp),%eax
    1575:	48 83 c1 01          	add    $0x1,%rcx
    1579:	4c 89 ba 20 06 00 00 	mov    %r15,0x620(%rdx)
    1580:	49 83 c7 40          	add    $0x40,%r15
    1584:	c7 82 30 06 00 00 01 00 00 00 	movl   $0x1,0x630(%rdx)
    158e:	c7 82 f8 05 00 00 00 00 00 00 	movl   $0x0,0x5f8(%rdx)
    1598:	c7 82 f0 05 00 00 0a 00 00 00 	movl   $0xa,0x5f0(%rdx)
    15a2:	c7 82 2c 06 00 00 0a 00 00 00 	movl   $0xa,0x62c(%rdx)
    15ac:	89 82 28 06 00 00    	mov    %eax,0x628(%rdx)
    15b2:	c7 82 74 06 00 00 0a 00 00 00 	movl   $0xa,0x674(%rdx)
    15bc:	c7 82 34 06 00 00 0b 00 00 00 	movl   $0xb,0x634(%rdx)
    15c6:	48 83 f9 0f          	cmp    $0xf,%rcx
    15ca:	0f 85 1b fd ff ff    	jne    12eb <main+0x10b>
    15d0:	4c 8b 6c 24 38       	mov    0x38(%rsp),%r13
    15d5:	be 38 00 00 00       	mov    $0x38,%esi
    15da:	bf 0f 00 00 00       	mov    $0xf,%edi
    15df:	45 31 f6             	xor    %r14d,%r14d
    15e2:	49 8d 85 c0 02 00 00 	lea    0x2c0(%r13),%rax
    15e9:	4d 89 ef             	mov    %r13,%r15
    15ec:	4d 89 ad d0 02 00 00 	mov    %r13,0x2d0(%r13)
    15f3:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    15f8:	49 8b 45 20          	mov    0x20(%r13),%rax
    15fc:	41 c7 85 d8 02 00 00 0a 00 00 00 	movl   $0xa,0x2d8(%r13)
    1607:	41 c7 85 c0 02 00 00 0b 00 00 00 	movl   $0xb,0x2c0(%r13)
    1612:	41 c7 85 e8 02 00 00 0b 00 00 00 	movl   $0xb,0x2e8(%r13)
    161d:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    1624:	49 8b 45 60          	mov    0x60(%r13),%rax
    1628:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    162f:	49 8b 85 a0 00 00 00 	mov    0xa0(%r13),%rax
    1636:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    163d:	49 8b 85 e0 00 00 00 	mov    0xe0(%r13),%rax
    1644:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    164b:	49 8b 85 20 01 00 00 	mov    0x120(%r13),%rax
    1652:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    1659:	49 8b 85 60 01 00 00 	mov    0x160(%r13),%rax
    1660:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    1667:	49 8b 85 a0 01 00 00 	mov    0x1a0(%r13),%rax
    166e:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    1675:	49 8b 85 e0 01 00 00 	mov    0x1e0(%r13),%rax
    167c:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    1683:	49 8b 85 20 02 00 00 	mov    0x220(%r13),%rax
    168a:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    1691:	49 8b 85 60 02 00 00 	mov    0x260(%r13),%rax
    1698:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    169f:	e8 bc fa ff ff       	call   1160 <calloc@plt>
    16a4:	be 38 00 00 00       	mov    $0x38,%esi
    16a9:	bf 0f 00 00 00       	mov    $0xf,%edi
    16ae:	48 89 c3             	mov    %rax,%rbx
    16b1:	e8 aa fa ff ff       	call   1160 <calloc@plt>
    16b6:	be 38 00 00 00       	mov    $0x38,%esi
    16bb:	bf 0f 00 00 00       	mov    $0xf,%edi
    16c0:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    16c5:	e8 96 fa ff ff       	call   1160 <calloc@plt>
    16ca:	be 08 00 00 00       	mov    $0x8,%esi
    16cf:	bf 0f 00 00 00       	mov    $0xf,%edi
    16d4:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    16d9:	e8 82 fa ff ff       	call   1160 <calloc@plt>
    16de:	4d 89 ad 90 02 00 00 	mov    %r13,0x290(%r13)
    16e5:	49 8d 8d 80 02 00 00 	lea    0x280(%r13),%rcx
    16ec:	48 8d b3 30 02 00 00 	lea    0x230(%rbx),%rsi
    16f3:	41 c7 85 84 02 00 00 00 00 00 00 	movl   $0x0,0x284(%r13)
    16fe:	49 89 c4             	mov    %rax,%r12
    1701:	48 8d 78 50          	lea    0x50(%rax),%rdi
    1705:	48 8d 15 94 08 00 00 	lea    0x894(%rip),%rdx        # 1fa0 <timer_thread>
    170c:	41 c7 85 ac 02 00 00 01 00 00 00 	movl   $0x1,0x2ac(%r13)
    1717:	4c 89 e5             	mov    %r12,%rbp
    171a:	41 c7 85 a8 02 00 00 0b 00 00 00 	movl   $0xb,0x2a8(%r13)
    1725:	41 c7 85 98 02 00 00 0a 00 00 00 	movl   $0xa,0x298(%r13)
    1730:	41 c7 85 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%r13)
    173b:	e8 60 fa ff ff       	call   11a0 <pthread_create@plt>
    1740:	41 c7 47 04 01 00 00 00 	movl   $0x1,0x4(%r15)
    1748:	44 89 f2             	mov    %r14d,%edx
    174b:	bf 01 00 00 00       	mov    $0x1,%edi
    1750:	31 c0                	xor    %eax,%eax
    1752:	41 c7 47 2c 01 00 00 00 	movl   $0x1,0x2c(%r15)
    175a:	48 8d 35 57 1b 00 00 	lea    0x1b57(%rip),%rsi        # 32b8 <_IO_stdin_used+0x2b8>
    1761:	41 83 c6 01          	add    $0x1,%r14d
    1765:	e8 26 fa ff ff       	call   1190 <__printf_chk@plt>
    176a:	4c 89 f9             	mov    %r15,%rcx
    176d:	48 89 de             	mov    %rbx,%rsi
    1770:	48 89 ef             	mov    %rbp,%rdi
    1773:	48 8d 15 d6 05 00 00 	lea    0x5d6(%rip),%rdx        # 1d50 <barriered_thread>
    177a:	49 83 c7 40          	add    $0x40,%r15
    177e:	48 83 c5 08          	add    $0x8,%rbp
    1782:	48 83 c3 38          	add    $0x38,%rbx
    1786:	e8 15 fa ff ff       	call   11a0 <pthread_create@plt>
    178b:	41 83 fe 0a          	cmp    $0xa,%r14d
    178f:	75 af                	jne    1740 <main+0x560>
    1791:	4d 89 ad d0 02 00 00 	mov    %r13,0x2d0(%r13)
    1798:	ba 0b 00 00 00       	mov    $0xb,%edx
    179d:	bf 01 00 00 00       	mov    $0x1,%edi
    17a2:	31 c0                	xor    %eax,%eax
    17a4:	41 c7 85 c4 02 00 00 02 00 00 00 	movl   $0x2,0x2c4(%r13)
    17af:	49 8d 6c 24 60       	lea    0x60(%r12),%rbp
    17b4:	48 8d 35 36 19 00 00 	lea    0x1936(%rip),%rsi        # 30f1 <_IO_stdin_used+0xf1>
    17bb:	41 be 0c 00 00 00    	mov    $0xc,%r14d
    17c1:	41 c7 85 ec 02 00 00 01 00 00 00 	movl   $0x1,0x2ec(%r13)
    17cc:	4d 8d bd 00 03 00 00 	lea    0x300(%r13),%r15
    17d3:	41 c7 85 e8 02 00 00 00 00 00 00 	movl   $0x0,0x2e8(%r13)
    17de:	41 c7 85 d8 02 00 00 0a 00 00 00 	movl   $0xa,0x2d8(%r13)
    17e9:	41 c7 85 c0 02 00 00 0b 00 00 00 	movl   $0xb,0x2c0(%r13)
    17f4:	e8 97 f9 ff ff       	call   1190 <__printf_chk@plt>
    17f9:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    17fe:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    1803:	49 8d 7c 24 58       	lea    0x58(%r12),%rdi
    1808:	48 8d 15 31 07 00 00 	lea    0x731(%rip),%rdx        # 1f40 <io_thread>
    180f:	48 81 c6 68 02 00 00 	add    $0x268,%rsi
    1816:	e8 85 f9 ff ff       	call   11a0 <pthread_create@plt>
    181b:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    1820:	4c 89 e0             	mov    %r12,%rax
    1823:	48 81 c3 a0 02 00 00 	add    $0x2a0,%rbx
    182a:	49 89 dc             	mov    %rbx,%r12
    182d:	48 89 c3             	mov    %rax,%rbx
    1830:	44 89 f2             	mov    %r14d,%edx
    1833:	48 8d 35 ce 18 00 00 	lea    0x18ce(%rip),%rsi        # 3108 <_IO_stdin_used+0x108>
    183a:	bf 01 00 00 00       	mov    $0x1,%edi
    183f:	31 c0                	xor    %eax,%eax
    1841:	e8 4a f9 ff ff       	call   1190 <__printf_chk@plt>
    1846:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    184b:	45 89 37             	mov    %r14d,(%r15)
    184e:	4c 89 e6             	mov    %r12,%rsi
    1851:	48 8b 0d 88 1b 00 00 	mov    0x1b88(%rip),%rcx        # 33e0 <_IO_stdin_used+0x3e0>
    1858:	4d 89 6f 10          	mov    %r13,0x10(%r15)
    185c:	48 89 ef             	mov    %rbp,%rdi
    185f:	48 8d 15 0a 0b 00 00 	lea    0xb0a(%rip),%rdx        # 2370 <external_thread>
    1866:	49 89 47 38          	mov    %rax,0x38(%r15)
    186a:	41 83 c6 01          	add    $0x1,%r14d
    186e:	48 83 c5 08          	add    $0x8,%rbp
    1872:	49 83 c4 38          	add    $0x38,%r12
    1876:	49 89 4f 18          	mov    %rcx,0x18(%r15)
    187a:	4c 89 f9             	mov    %r15,%rcx
    187d:	49 83 c7 40          	add    $0x40,%r15
    1881:	41 c7 47 c4 03 00 00 00 	movl   $0x3,-0x3c(%r15)
    1889:	41 c7 47 ec 01 00 00 00 	movl   $0x1,-0x14(%r15)
    1891:	41 c7 47 e8 00 00 00 00 	movl   $0x0,-0x18(%r15)
    1899:	e8 02 f9 ff ff       	call   11a0 <pthread_create@plt>
    189e:	48 83 44 24 48 10    	addq   $0x10,0x48(%rsp)
    18a4:	41 83 fe 0f          	cmp    $0xf,%r14d
    18a8:	75 86                	jne    1830 <main+0x650>
    18aa:	48 8d 3d 74 18 00 00 	lea    0x1874(%rip),%rdi        # 3125 <_IO_stdin_used+0x125>
    18b1:	49 89 dc             	mov    %rbx,%r12
    18b4:	31 db                	xor    %ebx,%ebx
    18b6:	e8 65 f8 ff ff       	call   1120 <puts@plt>
    18bb:	4c 8d 74 24 50       	lea    0x50(%rsp),%r14
    18c0:	48 8d 2d 7c 18 00 00 	lea    0x187c(%rip),%rbp        # 3143 <_IO_stdin_used+0x143>
    18c7:	49 8b 3c dc          	mov    (%r12,%rbx,8),%rdi
    18cb:	4c 89 f6             	mov    %r14,%rsi
    18ce:	e8 ed f8 ff ff       	call   11c0 <pthread_join@plt>
    18d3:	89 da                	mov    %ebx,%edx
    18d5:	48 89 ee             	mov    %rbp,%rsi
    18d8:	bf 01 00 00 00       	mov    $0x1,%edi
    18dd:	31 c0                	xor    %eax,%eax
    18df:	48 83 c3 01          	add    $0x1,%rbx
    18e3:	e8 a8 f8 ff ff       	call   1190 <__printf_chk@plt>
    18e8:	48 83 fb 0f          	cmp    $0xf,%rbx
    18ec:	75 d9                	jne    18c7 <main+0x6e7>
    18ee:	31 db                	xor    %ebx,%ebx
    18f0:	49 8d 4d 20          	lea    0x20(%r13),%rcx
    18f4:	49 8d b5 a0 02 00 00 	lea    0x2a0(%r13),%rsi
    18fb:	45 31 ff             	xor    %r15d,%r15d
    18fe:	45 31 e4             	xor    %r12d,%r12d
    1901:	45 31 ed             	xor    %r13d,%r13d
    1904:	45 31 f6             	xor    %r14d,%r14d
    1907:	31 ed                	xor    %ebp,%ebp
    1909:	48 89 da             	mov    %rbx,%rdx
    190c:	48 63 79 08          	movslq 0x8(%rcx),%rdi
    1910:	85 ff                	test   %edi,%edi
    1912:	0f 8e 07 01 00 00    	jle    1a1f <main+0x83f>
    1918:	48 8b 01             	mov    (%rcx),%rax
    191b:	4c 8d 04 ff          	lea    (%rdi,%rdi,8),%r8
    191f:	4a 8d 3c 47          	lea    (%rdi,%r8,2),%rdi
    1923:	48 8d 3c f8          	lea    (%rax,%rdi,8),%rdi
    1927:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    1930:	4c 8b 40 10          	mov    0x10(%rax),%r8
    1934:	48 05 98 00 00 00    	add    $0x98,%rax
    193a:	4c 01 c5             	add    %r8,%rbp
    193d:	4c 8b 40 80          	mov    -0x80(%rax),%r8
    1941:	4d 01 c6             	add    %r8,%r14
    1944:	4c 8b 40 d0          	mov    -0x30(%rax),%r8
    1948:	4d 01 c5             	add    %r8,%r13
    194b:	4c 8b 40 e0          	mov    -0x20(%rax),%r8
    194f:	4d 01 c4             	add    %r8,%r12
    1952:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    1956:	4d 03 78 10          	add    0x10(%r8),%r15
    195a:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    195e:	49 03 50 18          	add    0x18(%r8),%rdx
    1962:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    1966:	4d 03 78 30          	add    0x30(%r8),%r15
    196a:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    196e:	49 03 50 38          	add    0x38(%r8),%rdx
    1972:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    1976:	4d 03 78 50          	add    0x50(%r8),%r15
    197a:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    197e:	49 03 50 58          	add    0x58(%r8),%rdx
    1982:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    1986:	4d 03 78 70          	add    0x70(%r8),%r15
    198a:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    198e:	49 03 50 78          	add    0x78(%r8),%rdx
    1992:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    1996:	4d 03 b8 90 00 00 00 	add    0x90(%r8),%r15
    199d:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    19a1:	49 03 90 98 00 00 00 	add    0x98(%r8),%rdx
    19a8:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    19ac:	4d 03 b8 b0 00 00 00 	add    0xb0(%r8),%r15
    19b3:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    19b7:	49 03 90 b8 00 00 00 	add    0xb8(%r8),%rdx
    19be:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    19c2:	4d 03 b8 d0 00 00 00 	add    0xd0(%r8),%r15
    19c9:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    19cd:	49 03 90 d8 00 00 00 	add    0xd8(%r8),%rdx
    19d4:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    19d8:	4d 03 b8 f0 00 00 00 	add    0xf0(%r8),%r15
    19df:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    19e3:	49 03 90 f8 00 00 00 	add    0xf8(%r8),%rdx
    19ea:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    19ee:	4d 03 b8 10 01 00 00 	add    0x110(%r8),%r15
    19f5:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    19f9:	49 03 90 18 01 00 00 	add    0x118(%r8),%rdx
    1a00:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    1a04:	4d 03 b8 30 01 00 00 	add    0x130(%r8),%r15
    1a0b:	4c 8b 40 d8          	mov    -0x28(%rax),%r8
    1a0f:	49 03 90 38 01 00 00 	add    0x138(%r8),%rdx
    1a16:	48 39 f8             	cmp    %rdi,%rax
    1a19:	0f 85 11 ff ff ff    	jne    1930 <main+0x750>
    1a1f:	48 83 c1 40          	add    $0x40,%rcx
    1a23:	48 39 ce             	cmp    %rcx,%rsi
    1a26:	0f 85 e0 fe ff ff    	jne    190c <main+0x72c>
    1a2c:	48 89 d3             	mov    %rdx,%rbx
    1a2f:	48 8d 35 21 17 00 00 	lea    0x1721(%rip),%rsi        # 3157 <_IO_stdin_used+0x157>
    1a36:	48 89 ea             	mov    %rbp,%rdx
    1a39:	31 c0                	xor    %eax,%eax
    1a3b:	bf 01 00 00 00       	mov    $0x1,%edi
    1a40:	e8 4b f7 ff ff       	call   1190 <__printf_chk@plt>
    1a45:	bf 0a 00 00 00       	mov    $0xa,%edi
    1a4a:	e8 c1 f6 ff ff       	call   1110 <putchar@plt>
    1a4f:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    1a54:	bf 01 00 00 00       	mov    $0x1,%edi
    1a59:	48 8d 35 0b 17 00 00 	lea    0x170b(%rip),%rsi        # 316b <_IO_stdin_used+0x16b>
    1a60:	48 8b 10             	mov    (%rax),%rdx
    1a63:	31 c0                	xor    %eax,%eax
    1a65:	e8 26 f7 ff ff       	call   1190 <__printf_chk@plt>
    1a6a:	4c 89 f2             	mov    %r14,%rdx
    1a6d:	bf 01 00 00 00       	mov    $0x1,%edi
    1a72:	31 c0                	xor    %eax,%eax
    1a74:	48 8d 35 05 17 00 00 	lea    0x1705(%rip),%rsi        # 3180 <_IO_stdin_used+0x180>
    1a7b:	49 be 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%r14
    1a85:	e8 06 f7 ff ff       	call   1190 <__printf_chk@plt>
    1a8a:	bf 0a 00 00 00       	mov    $0xa,%edi
    1a8f:	e8 7c f6 ff ff       	call   1110 <putchar@plt>
    1a94:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    1a99:	bf 01 00 00 00       	mov    $0x1,%edi
    1a9e:	48 8d 35 3b 18 00 00 	lea    0x183b(%rip),%rsi        # 32e0 <_IO_stdin_used+0x2e0>
    1aa5:	48 8b 08             	mov    (%rax),%rcx
    1aa8:	48 89 c8             	mov    %rcx,%rax
    1aab:	49 f7 ee             	imul   %r14
    1aae:	31 c0                	xor    %eax,%eax
    1ab0:	48 01 ca             	add    %rcx,%rdx
    1ab3:	48 c1 f9 3f          	sar    $0x3f,%rcx
    1ab7:	48 c1 fa 04          	sar    $0x4,%rdx
    1abb:	48 29 ca             	sub    %rcx,%rdx
    1abe:	e8 cd f6 ff ff       	call   1190 <__printf_chk@plt>
    1ac3:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    1ac8:	bf 01 00 00 00       	mov    $0x1,%edi
    1acd:	48 8d 35 2c 18 00 00 	lea    0x182c(%rip),%rsi        # 3300 <_IO_stdin_used+0x300>
    1ad4:	48 8b 50 08          	mov    0x8(%rax),%rdx
    1ad8:	31 c0                	xor    %eax,%eax
    1ada:	e8 b1 f6 ff ff       	call   1190 <__printf_chk@plt>
    1adf:	4c 89 e8             	mov    %r13,%rax
    1ae2:	bf 01 00 00 00       	mov    $0x1,%edi
    1ae7:	48 8d 35 3a 18 00 00 	lea    0x183a(%rip),%rsi        # 3328 <_IO_stdin_used+0x328>
    1aee:	49 f7 ee             	imul   %r14
    1af1:	31 c0                	xor    %eax,%eax
    1af3:	4c 01 ea             	add    %r13,%rdx
    1af6:	49 c1 fd 3f          	sar    $0x3f,%r13
    1afa:	48 c1 fa 04          	sar    $0x4,%rdx
    1afe:	4c 29 ea             	sub    %r13,%rdx
    1b01:	e8 8a f6 ff ff       	call   1190 <__printf_chk@plt>
    1b06:	4c 89 e0             	mov    %r12,%rax
    1b09:	bf 01 00 00 00       	mov    $0x1,%edi
    1b0e:	48 8d 35 43 18 00 00 	lea    0x1843(%rip),%rsi        # 3358 <_IO_stdin_used+0x358>
    1b15:	49 f7 ee             	imul   %r14
    1b18:	31 c0                	xor    %eax,%eax
    1b1a:	4c 01 e2             	add    %r12,%rdx
    1b1d:	49 c1 fc 3f          	sar    $0x3f,%r12
    1b21:	48 c1 fa 04          	sar    $0x4,%rdx
    1b25:	4c 29 e2             	sub    %r12,%rdx
    1b28:	e8 63 f6 ff ff       	call   1190 <__printf_chk@plt>
    1b2d:	48 89 e8             	mov    %rbp,%rax
    1b30:	bf 01 00 00 00       	mov    $0x1,%edi
    1b35:	48 8d 35 4c 18 00 00 	lea    0x184c(%rip),%rsi        # 3388 <_IO_stdin_used+0x388>
    1b3c:	49 f7 ee             	imul   %r14
    1b3f:	48 01 ea             	add    %rbp,%rdx
    1b42:	48 c1 fd 3f          	sar    $0x3f,%rbp
    1b46:	31 c0                	xor    %eax,%eax
    1b48:	48 c1 fa 04          	sar    $0x4,%rdx
    1b4c:	48 29 ea             	sub    %rbp,%rdx
    1b4f:	e8 3c f6 ff ff       	call   1190 <__printf_chk@plt>
    1b54:	4c 89 f8             	mov    %r15,%rax
    1b57:	bf 01 00 00 00       	mov    $0x1,%edi
    1b5c:	48 8d 35 2a 16 00 00 	lea    0x162a(%rip),%rsi        # 318d <_IO_stdin_used+0x18d>
    1b63:	49 f7 ee             	imul   %r14
    1b66:	31 c0                	xor    %eax,%eax
    1b68:	4c 01 fa             	add    %r15,%rdx
    1b6b:	49 c1 ff 3f          	sar    $0x3f,%r15
    1b6f:	48 c1 fa 04          	sar    $0x4,%rdx
    1b73:	4c 29 fa             	sub    %r15,%rdx
    1b76:	e8 15 f6 ff ff       	call   1190 <__printf_chk@plt>
    1b7b:	48 89 d8             	mov    %rbx,%rax
    1b7e:	bf 01 00 00 00       	mov    $0x1,%edi
    1b83:	48 8d 35 14 16 00 00 	lea    0x1614(%rip),%rsi        # 319e <_IO_stdin_used+0x19e>
    1b8a:	49 f7 ee             	imul   %r14
    1b8d:	31 c0                	xor    %eax,%eax
    1b8f:	48 01 da             	add    %rbx,%rdx
    1b92:	48 c1 fb 3f          	sar    $0x3f,%rbx
    1b96:	48 c1 fa 04          	sar    $0x4,%rdx
    1b9a:	48 29 da             	sub    %rbx,%rdx
    1b9d:	e8 ee f5 ff ff       	call   1190 <__printf_chk@plt>
    1ba2:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    1ba7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1bb0:	0f 85 98 00 00 00    	jne    1c4e <main+0xa6e>
    1bb6:	48 83 c4 68          	add    $0x68,%rsp
    1bba:	31 c0                	xor    %eax,%eax
    1bbc:	5b                   	pop    %rbx
    1bbd:	5d                   	pop    %rbp
    1bbe:	41 5c                	pop    %r12
    1bc0:	41 5d                	pop    %r13
    1bc2:	41 5e                	pop    %r14
    1bc4:	41 5f                	pop    %r15
    1bc6:	c3                   	ret
    1bc7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    1bd0:	48 8d 05 49 09 00 00 	lea    0x949(%rip),%rax        # 2520 <barriered_work>
    1bd7:	bb 0a 00 00 00       	mov    $0xa,%ebx
    1bdc:	49 89 45 20          	mov    %rax,0x20(%r13)
    1be0:	89 dd                	mov    %ebx,%ebp
    1be2:	e9 79 f7 ff ff       	jmp    1360 <main+0x180>
    1be7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    1bf0:	48 8d 05 a9 02 00 00 	lea    0x2a9(%rip),%rax        # 1ea0 <do_protected_write>
    1bf7:	48 89 43 28          	mov    %rax,0x28(%rbx)
    1bfb:	e9 81 f7 ff ff       	jmp    1381 <main+0x1a1>
    1c00:	8b 54 24 20          	mov    0x20(%rsp),%edx
    1c04:	48 8d 35 d4 14 00 00 	lea    0x14d4(%rip),%rsi        # 30df <_IO_stdin_used+0xdf>
    1c0b:	bf 01 00 00 00       	mov    $0x1,%edi
    1c10:	31 c0                	xor    %eax,%eax
    1c12:	e8 79 f5 ff ff       	call   1190 <__printf_chk@plt>
    1c17:	48 63 44 24 28       	movslq 0x28(%rsp),%rax
    1c1c:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    1c21:	48 89 c1             	mov    %rax,%rcx
    1c24:	48 c1 e0 04          	shl    $0x4,%rax
    1c28:	48 01 d0             	add    %rdx,%rax
    1c2b:	49 8b 57 20          	mov    0x20(%r15),%rdx
    1c2f:	49 89 47 38          	mov    %rax,0x38(%r15)
    1c33:	48 8d 05 56 0b 00 00 	lea    0xb56(%rip),%rax        # 2790 <barriered_work_ingest>
    1c3a:	49 01 d4             	add    %rdx,%r12
    1c3d:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    1c42:	8d 41 01             	lea    0x1(%rcx),%eax
    1c45:	89 44 24 28          	mov    %eax,0x28(%rsp)
    1c49:	e9 04 f9 ff ff       	jmp    1552 <main+0x372>
    1c4e:	e8 ed f4 ff ff       	call   1140 <__stack_chk_fail@plt>
    1c53:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    1c5d:	0f 1f 00             	nopl   (%rax)

0000000000001c60 <_start>:
    1c60:	f3 0f 1e fa          	endbr64
    1c64:	31 ed                	xor    %ebp,%ebp
    1c66:	49 89 d1             	mov    %rdx,%r9
    1c69:	5e                   	pop    %rsi
    1c6a:	48 89 e2             	mov    %rsp,%rdx
    1c6d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1c71:	50                   	push   %rax
    1c72:	54                   	push   %rsp
    1c73:	45 31 c0             	xor    %r8d,%r8d
    1c76:	31 c9                	xor    %ecx,%ecx
    1c78:	48 8d 3d 61 f5 ff ff 	lea    -0xa9f(%rip),%rdi        # 11e0 <main>
    1c7f:	ff 15 53 33 00 00    	call   *0x3353(%rip)        # 4fd8 <__libc_start_main@GLIBC_2.34>
    1c85:	f4                   	hlt
    1c86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001c90 <deregister_tm_clones>:
    1c90:	48 8d 3d 79 33 00 00 	lea    0x3379(%rip),%rdi        # 5010 <__TMC_END__>
    1c97:	48 8d 05 72 33 00 00 	lea    0x3372(%rip),%rax        # 5010 <__TMC_END__>
    1c9e:	48 39 f8             	cmp    %rdi,%rax
    1ca1:	74 15                	je     1cb8 <deregister_tm_clones+0x28>
    1ca3:	48 8b 05 36 33 00 00 	mov    0x3336(%rip),%rax        # 4fe0 <_ITM_deregisterTMCloneTable@Base>
    1caa:	48 85 c0             	test   %rax,%rax
    1cad:	74 09                	je     1cb8 <deregister_tm_clones+0x28>
    1caf:	ff e0                	jmp    *%rax
    1cb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1cb8:	c3                   	ret
    1cb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001cc0 <register_tm_clones>:
    1cc0:	48 8d 3d 49 33 00 00 	lea    0x3349(%rip),%rdi        # 5010 <__TMC_END__>
    1cc7:	48 8d 35 42 33 00 00 	lea    0x3342(%rip),%rsi        # 5010 <__TMC_END__>
    1cce:	48 29 fe             	sub    %rdi,%rsi
    1cd1:	48 89 f0             	mov    %rsi,%rax
    1cd4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1cd8:	48 c1 f8 03          	sar    $0x3,%rax
    1cdc:	48 01 c6             	add    %rax,%rsi
    1cdf:	48 d1 fe             	sar    %rsi
    1ce2:	74 14                	je     1cf8 <register_tm_clones+0x38>
    1ce4:	48 8b 05 05 33 00 00 	mov    0x3305(%rip),%rax        # 4ff0 <_ITM_registerTMCloneTable@Base>
    1ceb:	48 85 c0             	test   %rax,%rax
    1cee:	74 08                	je     1cf8 <register_tm_clones+0x38>
    1cf0:	ff e0                	jmp    *%rax
    1cf2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1cf8:	c3                   	ret
    1cf9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001d00 <__do_global_dtors_aux>:
    1d00:	f3 0f 1e fa          	endbr64
    1d04:	80 3d 05 33 00 00 00 	cmpb   $0x0,0x3305(%rip)        # 5010 <__TMC_END__>
    1d0b:	75 2b                	jne    1d38 <__do_global_dtors_aux+0x38>
    1d0d:	55                   	push   %rbp
    1d0e:	48 83 3d e2 32 00 00 00 	cmpq   $0x0,0x32e2(%rip)        # 4ff8 <__cxa_finalize@GLIBC_2.2.5>
    1d16:	48 89 e5             	mov    %rsp,%rbp
    1d19:	74 0c                	je     1d27 <__do_global_dtors_aux+0x27>
    1d1b:	48 8b 3d e6 32 00 00 	mov    0x32e6(%rip),%rdi        # 5008 <__dso_handle>
    1d22:	e8 d9 f3 ff ff       	call   1100 <__cxa_finalize@plt>
    1d27:	e8 64 ff ff ff       	call   1c90 <deregister_tm_clones>
    1d2c:	c6 05 dd 32 00 00 01 	movb   $0x1,0x32dd(%rip)        # 5010 <__TMC_END__>
    1d33:	5d                   	pop    %rbp
    1d34:	c3                   	ret
    1d35:	0f 1f 00             	nopl   (%rax)
    1d38:	c3                   	ret
    1d39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001d40 <frame_dummy>:
    1d40:	f3 0f 1e fa          	endbr64
    1d44:	e9 77 ff ff ff       	jmp    1cc0 <register_tm_clones>
    1d49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001d50 <barriered_thread>:
    1d50:	f3 0f 1e fa          	endbr64
    1d54:	8b 47 2c             	mov    0x2c(%rdi),%eax
    1d57:	83 f8 01             	cmp    $0x1,%eax
    1d5a:	0f 85 33 01 00 00    	jne    1e93 <barriered_thread+0x143>
    1d60:	41 55                	push   %r13
    1d62:	41 54                	push   %r12
    1d64:	49 89 fc             	mov    %rdi,%r12
    1d67:	55                   	push   %rbp
    1d68:	31 ed                	xor    %ebp,%ebp
    1d6a:	53                   	push   %rbx
    1d6b:	48 83 ec 08          	sub    $0x8,%rsp
    1d6f:	44 8b 57 28          	mov    0x28(%rdi),%r10d
    1d73:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    1d78:	44 39 d5             	cmp    %r10d,%ebp
    1d7b:	7c 0b                	jl     1d88 <barriered_thread+0x38>
    1d7d:	31 ed                	xor    %ebp,%ebp
    1d7f:	45 85 d2             	test   %r10d,%r10d
    1d82:	0f 8e f0 00 00 00    	jle    1e78 <barriered_thread+0x128>
    1d88:	48 63 c5             	movslq %ebp,%rax
    1d8b:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    1d8f:	48 8d 1c 50          	lea    (%rax,%rdx,2),%rbx
    1d93:	48 c1 e3 03          	shl    $0x3,%rbx
    1d97:	eb 1a                	jmp    1db3 <barriered_thread+0x63>
    1d99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1da0:	83 c5 01             	add    $0x1,%ebp
    1da3:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    1daa:	44 39 d5             	cmp    %r10d,%ebp
    1dad:	0f 8d c5 00 00 00    	jge    1e78 <barriered_thread+0x128>
    1db3:	49 8b 54 24 20       	mov    0x20(%r12),%rdx
    1db8:	48 01 da             	add    %rbx,%rdx
    1dbb:	8b 42 40             	mov    0x40(%rdx),%eax
    1dbe:	83 f8 01             	cmp    $0x1,%eax
    1dc1:	75 dd                	jne    1da0 <barriered_thread+0x50>
    1dc3:	45 8b 5c 24 18       	mov    0x18(%r12),%r11d
    1dc8:	8d 4d ff             	lea    -0x1(%rbp),%ecx
    1dcb:	41 8d 42 ff          	lea    -0x1(%r10),%eax
    1dcf:	85 ed                	test   %ebp,%ebp
    1dd1:	0f 4f c1             	cmovg  %ecx,%eax
    1dd4:	4d 8b 6c 24 10       	mov    0x10(%r12),%r13
    1dd9:	45 85 db             	test   %r11d,%r11d
    1ddc:	7e 4d                	jle    1e2b <barriered_thread+0xdb>
    1dde:	48 98                	cltq
    1de0:	4d 63 c3             	movslq %r11d,%r8
    1de3:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    1de7:	49 c1 e0 06          	shl    $0x6,%r8
    1deb:	4c 8d 0c 48          	lea    (%rax,%rcx,2),%r9
    1def:	4d 01 e8             	add    %r13,%r8
    1df2:	4c 89 e8             	mov    %r13,%rax
    1df5:	31 c9                	xor    %ecx,%ecx
    1df7:	49 c1 e1 03          	shl    $0x3,%r9
    1dfb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    1e00:	48 8b 70 20          	mov    0x20(%rax),%rsi
    1e04:	4c 01 ce             	add    %r9,%rsi
    1e07:	8b 76 08             	mov    0x8(%rsi),%esi
    1e0a:	8b 7a 08             	mov    0x8(%rdx),%edi
    1e0d:	39 f7                	cmp    %esi,%edi
    1e0f:	40 0f 94 c6          	sete   %sil
    1e13:	48 83 c0 40          	add    $0x40,%rax
    1e17:	40 0f b6 f6          	movzbl %sil,%esi
    1e1b:	01 f1                	add    %esi,%ecx
    1e1d:	4c 39 c0             	cmp    %r8,%rax
    1e20:	75 de                	jne    1e00 <barriered_thread+0xb0>
    1e22:	41 39 cb             	cmp    %ecx,%r11d
    1e25:	74 04                	je     1e2b <barriered_thread+0xdb>
    1e27:	85 c9                	test   %ecx,%ecx
    1e29:	75 4d                	jne    1e78 <barriered_thread+0x128>
    1e2b:	49 63 04 24          	movslq (%r12),%rax
    1e2f:	c7 42 40 00 00 00 00 	movl   $0x0,0x40(%rdx)
    1e36:	48 8b 52 20          	mov    0x20(%rdx),%rdx
    1e3a:	48 c1 e0 06          	shl    $0x6,%rax
    1e3e:	49 8b 7c 05 20       	mov    0x20(%r13,%rax,1),%rdi
    1e43:	48 01 df             	add    %rbx,%rdi
    1e46:	ff d2                	call   *%rdx
    1e48:	49 8b 54 24 20       	mov    0x20(%r12),%rdx
    1e4d:	48 01 da             	add    %rbx,%rdx
    1e50:	8b 42 08             	mov    0x8(%rdx),%eax
    1e53:	83 c0 01             	add    $0x1,%eax
    1e56:	89 42 08             	mov    %eax,0x8(%rdx)
    1e59:	0f ae f0             	mfence
    1e5c:	45 8b 54 24 28       	mov    0x28(%r12),%r10d
    1e61:	83 c5 01             	add    $0x1,%ebp
    1e64:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    1e6b:	44 39 d5             	cmp    %r10d,%ebp
    1e6e:	0f 8c 3f ff ff ff    	jl     1db3 <barriered_thread+0x63>
    1e74:	0f 1f 40 00          	nopl   0x0(%rax)
    1e78:	41 8b 44 24 2c       	mov    0x2c(%r12),%eax
    1e7d:	83 f8 01             	cmp    $0x1,%eax
    1e80:	0f 84 f2 fe ff ff    	je     1d78 <barriered_thread+0x28>
    1e86:	48 83 c4 08          	add    $0x8,%rsp
    1e8a:	31 c0                	xor    %eax,%eax
    1e8c:	5b                   	pop    %rbx
    1e8d:	5d                   	pop    %rbp
    1e8e:	41 5c                	pop    %r12
    1e90:	41 5d                	pop    %r13
    1e92:	c3                   	ret
    1e93:	31 c0                	xor    %eax,%eax
    1e95:	c3                   	ret
    1e96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001ea0 <do_protected_write>:
    1ea0:	f3 0f 1e fa          	endbr64
    1ea4:	48 8b 47 30          	mov    0x30(%rdi),%rax
    1ea8:	48 8b 57 18          	mov    0x18(%rdi),%rdx
    1eac:	48 8b 40 30          	mov    0x30(%rax),%rax
    1eb0:	48 83 c2 01          	add    $0x1,%rdx
    1eb4:	48 89 57 18          	mov    %rdx,0x18(%rdi)
    1eb8:	48 8b 48 08          	mov    0x8(%rax),%rcx
    1ebc:	48 83 00 01          	addq   $0x1,(%rax)
    1ec0:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    1ec7:	48 85 c9             	test   %rcx,%rcx
    1eca:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    1ed1:	48 0f 4f d6          	cmovg  %rsi,%rdx
    1ed5:	48 89 50 08          	mov    %rdx,0x8(%rax)
    1ed9:	31 c0                	xor    %eax,%eax
    1edb:	c3                   	ret
    1edc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000001ee0 <barriered_reset>:
    1ee0:	f3 0f 1e fa          	endbr64
    1ee4:	8b 47 44             	mov    0x44(%rdi),%eax
    1ee7:	85 c0                	test   %eax,%eax
    1ee9:	7e 48                	jle    1f33 <barriered_reset+0x53>
    1eeb:	31 d2                	xor    %edx,%edx
    1eed:	31 c9                	xor    %ecx,%ecx
    1eef:	90                   	nop
    1ef0:	48 8b 77 30          	mov    0x30(%rdi),%rsi
    1ef4:	48 63 47 38          	movslq 0x38(%rdi),%rax
    1ef8:	83 c1 01             	add    $0x1,%ecx
    1efb:	48 c1 e0 06          	shl    $0x6,%rax
    1eff:	48 03 46 10          	add    0x10(%rsi),%rax
    1f03:	48 8b 70 20          	mov    0x20(%rax),%rsi
    1f07:	48 01 d6             	add    %rdx,%rsi
    1f0a:	8b 46 08             	mov    0x8(%rsi),%eax
    1f0d:	83 c0 01             	add    $0x1,%eax
    1f10:	89 46 08             	mov    %eax,0x8(%rsi)
    1f13:	48 8b 47 30          	mov    0x30(%rdi),%rax
    1f17:	48 8b 70 20          	mov    0x20(%rax),%rsi
    1f1b:	48 01 d6             	add    %rdx,%rsi
    1f1e:	48 81 c2 98 00 00 00 	add    $0x98,%rdx
    1f25:	c7 46 40 01 00 00 00 	movl   $0x1,0x40(%rsi)
    1f2c:	8b 47 44             	mov    0x44(%rdi),%eax
    1f2f:	39 c8                	cmp    %ecx,%eax
    1f31:	7f bd                	jg     1ef0 <barriered_reset+0x10>
    1f33:	0f ae f0             	mfence
    1f36:	31 c0                	xor    %eax,%eax
    1f38:	c3                   	ret
    1f39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001f40 <io_thread>:
    1f40:	f3 0f 1e fa          	endbr64
    1f44:	48 81 ec e8 00 00 00 	sub    $0xe8,%rsp
    1f4b:	31 d2                	xor    %edx,%edx
    1f4d:	bf 00 01 00 00       	mov    $0x100,%edi
    1f52:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1f5b:	48 89 84 24 d8 00 00 00 	mov    %rax,0xd8(%rsp)
    1f63:	31 c0                	xor    %eax,%eax
    1f65:	48 89 e6             	mov    %rsp,%rsi
    1f68:	e8 03 f2 ff ff       	call   1170 <io_uring_queue_init@plt>
    1f6d:	48 8d 3d 90 10 00 00 	lea    0x1090(%rip),%rdi        # 3004 <_IO_stdin_used+0x4>
    1f74:	e8 a7 f1 ff ff       	call   1120 <puts@plt>
    1f79:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
    1f81:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1f8a:	75 0a                	jne    1f96 <io_thread+0x56>
    1f8c:	31 c0                	xor    %eax,%eax
    1f8e:	48 81 c4 e8 00 00 00 	add    $0xe8,%rsp
    1f95:	c3                   	ret
    1f96:	e8 a5 f1 ff ff       	call   1140 <__stack_chk_fail@plt>
    1f9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000001fa0 <timer_thread>:
    1fa0:	f3 0f 1e fa          	endbr64
    1fa4:	41 57                	push   %r15
    1fa6:	48 8d 35 6a 10 00 00 	lea    0x106a(%rip),%rsi        # 3017 <_IO_stdin_used+0x17>
    1fad:	49 89 ff             	mov    %rdi,%r15
    1fb0:	41 56                	push   %r14
    1fb2:	41 55                	push   %r13
    1fb4:	41 54                	push   %r12
    1fb6:	55                   	push   %rbp
    1fb7:	53                   	push   %rbx
    1fb8:	48 83 ec 58          	sub    $0x58,%rsp
    1fbc:	8b 17                	mov    (%rdi),%edx
    1fbe:	bf 01 00 00 00       	mov    $0x1,%edi
    1fc3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1fcc:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    1fd1:	31 c0                	xor    %eax,%eax
    1fd3:	e8 b8 f1 ff ff       	call   1190 <__printf_chk@plt>
    1fd8:	66 0f 6f 05 d0 13 00 00 	movdqa 0x13d0(%rip),%xmm0        # 33b0 <_IO_stdin_used+0x3b0>
    1fe0:	ba 20 4e 00 00       	mov    $0x4e20,%edx
    1fe5:	31 c0                	xor    %eax,%eax
    1fe7:	48 8d 35 3b 10 00 00 	lea    0x103b(%rip),%rsi        # 3029 <_IO_stdin_used+0x29>
    1fee:	bf 01 00 00 00       	mov    $0x1,%edi
    1ff3:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    1ff8:	e8 93 f1 ff ff       	call   1190 <__printf_chk@plt>
    1ffd:	4d 63 77 2c          	movslq 0x2c(%r15),%r14
    2001:	45 85 f6             	test   %r14d,%r14d
    2004:	0f 84 9e 00 00 00    	je     20a8 <timer_thread+0x108>
    200a:	45 31 ed             	xor    %r13d,%r13d
    200d:	45 31 f6             	xor    %r14d,%r14d
    2010:	49 89 e4             	mov    %rsp,%r12
    2013:	31 db                	xor    %ebx,%ebx
    2015:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    201a:	48 89 ef             	mov    %rbp,%rdi
    201d:	4c 89 e6             	mov    %r12,%rsi
    2020:	41 83 c5 01          	add    $0x1,%r13d
    2024:	e8 27 f1 ff ff       	call   1150 <nanosleep@plt>
    2029:	41 8b 47 18          	mov    0x18(%r15),%eax
    202d:	41 8d 7e 01          	lea    0x1(%r14),%edi
    2031:	85 c0                	test   %eax,%eax
    2033:	7e 4e                	jle    2083 <timer_thread+0xe3>
    2035:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    2039:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    203d:	4c 63 c0             	movslq %eax,%r8
    2040:	4d 8d 0c 56          	lea    (%r14,%rdx,2),%r9
    2044:	49 c1 e0 06          	shl    $0x6,%r8
    2048:	49 c1 e1 03          	shl    $0x3,%r9
    204c:	49 01 c8             	add    %rcx,%r8
    204f:	90                   	nop
    2050:	89 f8                	mov    %edi,%eax
    2052:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    2056:	99                   	cltd
    2057:	f7 79 28             	idivl  0x28(%rcx)
    205a:	48 83 c1 40          	add    $0x40,%rcx
    205e:	48 63 d2             	movslq %edx,%rdx
    2061:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    2065:	48 8d 04 42          	lea    (%rdx,%rax,2),%rax
    2069:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    206d:	4c 01 ce             	add    %r9,%rsi
    2070:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2077:	c7 46 48 00 00 00 00 	movl   $0x0,0x48(%rsi)
    207e:	4c 39 c1             	cmp    %r8,%rcx
    2081:	75 cd                	jne    2050 <timer_thread+0xb0>
    2083:	0f ae f0             	mfence
    2086:	49 8b 47 10          	mov    0x10(%r15),%rax
    208a:	39 78 28             	cmp    %edi,0x28(%rax)
    208d:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    2091:	0f 4e fb             	cmovle %ebx,%edi
    2094:	4c 63 f7             	movslq %edi,%r14
    2097:	85 c0                	test   %eax,%eax
    2099:	74 0d                	je     20a8 <timer_thread+0x108>
    209b:	41 81 fd 20 4e 00 00 	cmp    $0x4e20,%r13d
    20a2:	0f 85 72 ff ff ff    	jne    201a <timer_thread+0x7a>
    20a8:	48 8d 3d 90 0f 00 00 	lea    0xf90(%rip),%rdi        # 303f <_IO_stdin_used+0x3f>
    20af:	e8 6c f0 ff ff       	call   1120 <puts@plt>
    20b4:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    20b8:	85 d2                	test   %edx,%edx
    20ba:	7e 52                	jle    210e <timer_thread+0x16e>
    20bc:	49 63 47 28          	movslq 0x28(%r15),%rax
    20c0:	85 c0                	test   %eax,%eax
    20c2:	7e 4a                	jle    210e <timer_thread+0x16e>
    20c4:	48 89 d1             	mov    %rdx,%rcx
    20c7:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    20cb:	4d 8b 47 10          	mov    0x10(%r15),%r8
    20cf:	31 f6                	xor    %esi,%esi
    20d1:	48 8d 3c 50          	lea    (%rax,%rdx,2),%rdi
    20d5:	48 c1 e1 06          	shl    $0x6,%rcx
    20d9:	48 c1 e7 03          	shl    $0x3,%rdi
    20dd:	49 8b 44 30 20       	mov    0x20(%r8,%rsi,1),%rax
    20e2:	48 8d 14 07          	lea    (%rdi,%rax,1),%rdx
    20e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    20f0:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    20fa:	48 05 98 00 00 00    	add    $0x98,%rax
    2100:	48 39 d0             	cmp    %rdx,%rax
    2103:	75 eb                	jne    20f0 <timer_thread+0x150>
    2105:	48 83 c6 40          	add    $0x40,%rsi
    2109:	48 39 f1             	cmp    %rsi,%rcx
    210c:	75 cf                	jne    20dd <timer_thread+0x13d>
    210e:	0f ae f0             	mfence
    2111:	66 0f 6f 05 a7 12 00 00 	movdqa 0x12a7(%rip),%xmm0        # 33c0 <_IO_stdin_used+0x3c0>
    2119:	48 8d 2d 44 0f 00 00 	lea    0xf44(%rip),%rbp        # 3064 <_IO_stdin_used+0x64>
    2120:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    2125:	41 8b 47 18          	mov    0x18(%r15),%eax
    2129:	45 8d 6e 01          	lea    0x1(%r14),%r13d
    212d:	85 c0                	test   %eax,%eax
    212f:	7e 53                	jle    2184 <timer_thread+0x1e4>
    2131:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    2135:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    2139:	48 63 f8             	movslq %eax,%rdi
    213c:	4d 8d 04 56          	lea    (%r14,%rdx,2),%r8
    2140:	48 c1 e7 06          	shl    $0x6,%rdi
    2144:	49 c1 e0 03          	shl    $0x3,%r8
    2148:	48 01 cf             	add    %rcx,%rdi
    214b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2150:	44 89 e8             	mov    %r13d,%eax
    2153:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    2157:	99                   	cltd
    2158:	f7 79 28             	idivl  0x28(%rcx)
    215b:	48 83 c1 40          	add    $0x40,%rcx
    215f:	48 63 c2             	movslq %edx,%rax
    2162:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    2166:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    216a:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    216e:	4c 01 c6             	add    %r8,%rsi
    2171:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2178:	c7 46 48 00 00 00 00 	movl   $0x0,0x48(%rsi)
    217f:	48 39 f9             	cmp    %rdi,%rcx
    2182:	75 cc                	jne    2150 <timer_thread+0x1b0>
    2184:	0f ae f0             	mfence
    2187:	49 8b 47 10          	mov    0x10(%r15),%rax
    218b:	44 39 68 28          	cmp    %r13d,0x28(%rax)
    218f:	7f 03                	jg     2194 <timer_thread+0x1f4>
    2191:	45 31 ed             	xor    %r13d,%r13d
    2194:	45 8b 47 18          	mov    0x18(%r15),%r8d
    2198:	45 85 c0             	test   %r8d,%r8d
    219b:	0f 8e dd 00 00 00    	jle    227e <timer_thread+0x2de>
    21a1:	31 db                	xor    %ebx,%ebx
    21a3:	45 31 e4             	xor    %r12d,%r12d
    21a6:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    21ac:	0f 1f 40 00          	nopl   0x0(%rax)
    21b0:	45 31 f6             	xor    %r14d,%r14d
    21b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    21b8:	45 85 c0             	test   %r8d,%r8d
    21bb:	0f 8e 81 00 00 00    	jle    2242 <timer_thread+0x2a2>
    21c1:	49 8b 47 10          	mov    0x10(%r15),%rax
    21c5:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    21c9:	49 63 f8             	movslq %r8d,%rdi
    21cc:	49 8d 14 56          	lea    (%r14,%rdx,2),%rdx
    21d0:	48 8b 44 18 20       	mov    0x20(%rax,%rbx,1),%rax
    21d5:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    21d9:	31 d2                	xor    %edx,%edx
    21db:	eb 1e                	jmp    21fb <timer_thread+0x25b>
    21dd:	0f 1f 00             	nopl   (%rax)
    21e0:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    21e4:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    21e9:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    21ed:	48 85 f6             	test   %rsi,%rsi
    21f0:	7f 21                	jg     2213 <timer_thread+0x273>
    21f2:	48 83 c2 01          	add    $0x1,%rdx
    21f6:	48 39 d7             	cmp    %rdx,%rdi
    21f9:	74 47                	je     2242 <timer_thread+0x2a2>
    21fb:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    21ff:	48 89 d0             	mov    %rdx,%rax
    2202:	48 c1 e0 05          	shl    $0x5,%rax
    2206:	48 8b 34 06          	mov    (%rsi,%rax,1),%rsi
    220a:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    220e:	48 85 f6             	test   %rsi,%rsi
    2211:	7e cd                	jle    21e0 <timer_thread+0x240>
    2213:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    2217:	bf 01 00 00 00       	mov    $0x1,%edi
    221c:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    2221:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    2225:	48 8b 49 70          	mov    0x70(%rcx),%rcx
    2229:	48 89 ee             	mov    %rbp,%rsi
    222c:	48 8b 04 01          	mov    (%rcx,%rax,1),%rax
    2230:	48 8b 48 08          	mov    0x8(%rax),%rcx
    2234:	31 c0                	xor    %eax,%eax
    2236:	e8 55 ef ff ff       	call   1190 <__printf_chk@plt>
    223b:	45 8b 47 18          	mov    0x18(%r15),%r8d
    223f:	45 31 c9             	xor    %r9d,%r9d
    2242:	49 83 c6 01          	add    $0x1,%r14
    2246:	45 39 f0             	cmp    %r14d,%r8d
    2249:	0f 8f 69 ff ff ff    	jg     21b8 <timer_thread+0x218>
    224f:	41 83 c4 01          	add    $0x1,%r12d
    2253:	45 39 c4             	cmp    %r8d,%r12d
    2256:	7d 09                	jge    2261 <timer_thread+0x2c1>
    2258:	48 83 c3 40          	add    $0x40,%rbx
    225c:	e9 4f ff ff ff       	jmp    21b0 <timer_thread+0x210>
    2261:	41 83 f9 01          	cmp    $0x1,%r9d
    2265:	74 17                	je     227e <timer_thread+0x2de>
    2267:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    226c:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    2271:	4d 63 f5             	movslq %r13d,%r14
    2274:	e8 d7 ee ff ff       	call   1150 <nanosleep@plt>
    2279:	e9 a7 fe ff ff       	jmp    2125 <timer_thread+0x185>
    227e:	48 8d 3d d6 0d 00 00 	lea    0xdd6(%rip),%rdi        # 305b <_IO_stdin_used+0x5b>
    2285:	48 8d 1d e9 0d 00 00 	lea    0xde9(%rip),%rbx        # 3075 <_IO_stdin_used+0x75>
    228c:	e8 8f ee ff ff       	call   1120 <puts@plt>
    2291:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    2295:	85 c0                	test   %eax,%eax
    2297:	0f 84 9d 00 00 00    	je     233a <timer_thread+0x39a>
    229d:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    22a1:	85 d2                	test   %edx,%edx
    22a3:	7e 1b                	jle    22c0 <timer_thread+0x320>
    22a5:	49 8b 47 10          	mov    0x10(%r15),%rax
    22a9:	48 c1 e2 06          	shl    $0x6,%rdx
    22ad:	48 01 c2             	add    %rax,%rdx
    22b0:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
    22b7:	48 83 c0 40          	add    $0x40,%rax
    22bb:	48 39 c2             	cmp    %rax,%rdx
    22be:	75 f0                	jne    22b0 <timer_thread+0x310>
    22c0:	49 63 47 18          	movslq 0x18(%r15),%rax
    22c4:	85 c0                	test   %eax,%eax
    22c6:	7e 53                	jle    231b <timer_thread+0x37b>
    22c8:	41 8b 57 28          	mov    0x28(%r15),%edx
    22cc:	85 d2                	test   %edx,%edx
    22ce:	7e 4b                	jle    231b <timer_thread+0x37b>
    22d0:	48 c1 e0 06          	shl    $0x6,%rax
    22d4:	4d 8b 47 10          	mov    0x10(%r15),%r8
    22d8:	31 c9                	xor    %ecx,%ecx
    22da:	48 89 c6             	mov    %rax,%rsi
    22dd:	48 63 c2             	movslq %edx,%rax
    22e0:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    22e4:	48 8d 3c 50          	lea    (%rax,%rdx,2),%rdi
    22e8:	48 c1 e7 03          	shl    $0x3,%rdi
    22ec:	0f 1f 40 00          	nopl   0x0(%rax)
    22f0:	49 8b 44 08 20       	mov    0x20(%r8,%rcx,1),%rax
    22f5:	48 8d 14 38          	lea    (%rax,%rdi,1),%rdx
    22f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    2300:	c7 40 48 00 00 00 00 	movl   $0x0,0x48(%rax)
    2307:	48 05 98 00 00 00    	add    $0x98,%rax
    230d:	48 39 c2             	cmp    %rax,%rdx
    2310:	75 ee                	jne    2300 <timer_thread+0x360>
    2312:	48 83 c1 40          	add    $0x40,%rcx
    2316:	48 39 ce             	cmp    %rcx,%rsi
    2319:	75 d5                	jne    22f0 <timer_thread+0x350>
    231b:	0f ae f0             	mfence
    231e:	48 89 df             	mov    %rbx,%rdi
    2321:	e8 fa ed ff ff       	call   1120 <puts@plt>
    2326:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
    232e:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    2332:	85 c0                	test   %eax,%eax
    2334:	0f 85 63 ff ff ff    	jne    229d <timer_thread+0x2fd>
    233a:	48 8d 3d 3b 0d 00 00 	lea    0xd3b(%rip),%rdi        # 307c <_IO_stdin_used+0x7c>
    2341:	e8 da ed ff ff       	call   1120 <puts@plt>
    2346:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    234b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    2354:	75 11                	jne    2367 <timer_thread+0x3c7>
    2356:	48 83 c4 58          	add    $0x58,%rsp
    235a:	31 c0                	xor    %eax,%eax
    235c:	5b                   	pop    %rbx
    235d:	5d                   	pop    %rbp
    235e:	41 5c                	pop    %r12
    2360:	41 5d                	pop    %r13
    2362:	41 5e                	pop    %r14
    2364:	41 5f                	pop    %r15
    2366:	c3                   	ret
    2367:	e8 d4 ed ff ff       	call   1140 <__stack_chk_fail@plt>
    236c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000002370 <external_thread>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	41 55                	push   %r13
    2376:	41 54                	push   %r12
    2378:	55                   	push   %rbp
    2379:	53                   	push   %rbx
    237a:	48 83 ec 38          	sub    $0x38,%rsp
    237e:	66 0f 6f 05 4a 10 00 00 	movdqa 0x104a(%rip),%xmm0        # 33d0 <_IO_stdin_used+0x3d0>
    2386:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    238f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2394:	31 c0                	xor    %eax,%eax
    2396:	0f 29 04 24          	movaps %xmm0,(%rsp)
    239a:	8b 47 2c             	mov    0x2c(%rdi),%eax
    239d:	83 f8 01             	cmp    $0x1,%eax
    23a0:	75 64                	jne    2406 <external_thread+0x96>
    23a2:	49 89 fd             	mov    %rdi,%r13
    23a5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    23aa:	48 89 e3             	mov    %rsp,%rbx
    23ad:	4c 8d 25 de 0c 00 00 	lea    0xcde(%rip),%r12        # 3092 <_IO_stdin_used+0x92>
    23b4:	0f 1f 40 00          	nopl   0x0(%rax)
    23b8:	48 89 ee             	mov    %rbp,%rsi
    23bb:	48 89 df             	mov    %rbx,%rdi
    23be:	e8 8d ed ff ff       	call   1150 <nanosleep@plt>
    23c3:	49 8b 45 38          	mov    0x38(%r13),%rax
    23c7:	48 63 08             	movslq (%rax),%rcx
    23ca:	85 c9                	test   %ecx,%ecx
    23cc:	7e 2c                	jle    23fa <external_thread+0x8a>
    23ce:	48 8b 40 08          	mov    0x8(%rax),%rax
    23d2:	48 c1 e1 04          	shl    $0x4,%rcx
    23d6:	48 01 c1             	add    %rax,%rcx
    23d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    23e0:	8b 50 08             	mov    0x8(%rax),%edx
    23e3:	85 d2                	test   %edx,%edx
    23e5:	75 0a                	jne    23f1 <external_thread+0x81>
    23e7:	4c 89 20             	mov    %r12,(%rax)
    23ea:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    23f1:	48 83 c0 10          	add    $0x10,%rax
    23f5:	48 39 c1             	cmp    %rax,%rcx
    23f8:	75 e6                	jne    23e0 <external_thread+0x70>
    23fa:	0f ae f0             	mfence
    23fd:	41 8b 45 2c          	mov    0x2c(%r13),%eax
    2401:	83 f8 01             	cmp    $0x1,%eax
    2404:	74 b2                	je     23b8 <external_thread+0x48>
    2406:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    240b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    2414:	75 0d                	jne    2423 <external_thread+0xb3>
    2416:	48 83 c4 38          	add    $0x38,%rsp
    241a:	31 c0                	xor    %eax,%eax
    241c:	5b                   	pop    %rbx
    241d:	5d                   	pop    %rbp
    241e:	41 5c                	pop    %r12
    2420:	41 5d                	pop    %r13
    2422:	c3                   	ret
    2423:	e8 18 ed ff ff       	call   1140 <__stack_chk_fail@plt>
    2428:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000002430 <receive>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	8b 57 3c             	mov    0x3c(%rdi),%edx
    2437:	85 d2                	test   %edx,%edx
    2439:	0f 8e d1 00 00 00    	jle    2510 <receive+0xe0>
    243f:	48 89 f8             	mov    %rdi,%rax
    2442:	45 31 db             	xor    %r11d,%r11d
    2445:	0f 1f 00             	nopl   (%rax)
    2448:	48 8b 50 70          	mov    0x70(%rax),%rdx
    244c:	4c 89 df             	mov    %r11,%rdi
    244f:	48 c1 e7 05          	shl    $0x5,%rdi
    2453:	4c 8b 0c 3a          	mov    (%rdx,%rdi,1),%r9
    2457:	49 8b 51 08          	mov    0x8(%r9),%rdx
    245b:	48 85 d2             	test   %rdx,%rdx
    245e:	0f 8e 94 00 00 00    	jle    24f8 <receive+0xc8>
    2464:	4d 8b 11             	mov    (%r9),%r10
    2467:	31 d2                	xor    %edx,%edx
    2469:	eb 12                	jmp    247d <receive+0x4d>
    246b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2470:	49 8b 49 08          	mov    0x8(%r9),%rcx
    2474:	48 83 c2 01          	add    $0x1,%rdx
    2478:	48 39 d1             	cmp    %rdx,%rcx
    247b:	7e 7b                	jle    24f8 <receive+0xc8>
    247d:	48 8b 48 78          	mov    0x78(%rax),%rcx
    2481:	49 8b 34 d2          	mov    (%r10,%rdx,8),%rsi
    2485:	48 83 c1 01          	add    $0x1,%rcx
    2489:	4c 8b 46 10          	mov    0x10(%rsi),%r8
    248d:	48 89 48 78          	mov    %rcx,0x78(%rax)
    2491:	48 8b 48 10          	mov    0x10(%rax),%rcx
    2495:	48 83 c1 01          	add    $0x1,%rcx
    2499:	48 89 48 10          	mov    %rcx,0x10(%rax)
    249d:	48 8b 48 70          	mov    0x70(%rax),%rcx
    24a1:	48 83 44 39 18 01    	addq   $0x1,0x18(%rcx,%rdi,1)
    24a7:	48 63 08             	movslq (%rax),%rcx
    24aa:	49 39 c8             	cmp    %rcx,%r8
    24ad:	75 c1                	jne    2470 <receive+0x40>
    24af:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    24b3:	48 63 48 38          	movslq 0x38(%rax),%rcx
    24b7:	48 39 ce             	cmp    %rcx,%rsi
    24ba:	75 b4                	jne    2470 <receive+0x40>
    24bc:	48 83 ec 08          	sub    $0x8,%rsp
    24c0:	48 63 50 38          	movslq 0x38(%rax),%rdx
    24c4:	48 63 00             	movslq (%rax),%rax
    24c7:	31 c9                	xor    %ecx,%ecx
    24c9:	bf 01 00 00 00       	mov    $0x1,%edi
    24ce:	48 39 f2             	cmp    %rsi,%rdx
    24d1:	48 8d 35 e0 0c 00 00 	lea    0xce0(%rip),%rsi        # 31b8 <_IO_stdin_used+0x1b8>
    24d8:	0f 94 c1             	sete   %cl
    24db:	31 d2                	xor    %edx,%edx
    24dd:	4c 39 c0             	cmp    %r8,%rax
    24e0:	0f 94 c2             	sete   %dl
    24e3:	31 c0                	xor    %eax,%eax
    24e5:	e8 a6 ec ff ff       	call   1190 <__printf_chk@plt>
    24ea:	bf 01 00 00 00       	mov    $0x1,%edi
    24ef:	e8 bc ec ff ff       	call   11b0 <exit@plt>
    24f4:	0f 1f 40 00          	nopl   0x0(%rax)
    24f8:	49 c7 41 08 00 00 00 00 	movq   $0x0,0x8(%r9)
    2500:	8b 50 3c             	mov    0x3c(%rax),%edx
    2503:	49 83 c3 01          	add    $0x1,%r11
    2507:	44 39 da             	cmp    %r11d,%edx
    250a:	0f 8f 38 ff ff ff    	jg     2448 <receive+0x18>
    2510:	c3                   	ret
    2511:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    251c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000002520 <barriered_work>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	41 54                	push   %r12
    2526:	55                   	push   %rbp
    2527:	53                   	push   %rbx
    2528:	8b 57 38             	mov    0x38(%rdi),%edx
    252b:	48 89 fb             	mov    %rdi,%rbx
    252e:	8b 07                	mov    (%rdi),%eax
    2530:	39 c2                	cmp    %eax,%edx
    2532:	0f 84 c8 00 00 00    	je     2600 <barriered_work+0xe0>
    2538:	e8 f3 fe ff ff       	call   2430 <receive>
    253d:	8b 43 48             	mov    0x48(%rbx),%eax
    2540:	83 f8 01             	cmp    $0x1,%eax
    2543:	75 17                	jne    255c <barriered_work+0x3c>
    2545:	0f 1f 00             	nopl   (%rax)
    2548:	48 8b 43 10          	mov    0x10(%rbx),%rax
    254c:	48 83 c0 01          	add    $0x1,%rax
    2550:	48 89 43 10          	mov    %rax,0x10(%rbx)
    2554:	8b 43 48             	mov    0x48(%rbx),%eax
    2557:	83 f8 01             	cmp    $0x1,%eax
    255a:	74 ec                	je     2548 <barriered_work+0x28>
    255c:	8b 83 80 00 00 00    	mov    0x80(%rbx),%eax
    2562:	83 f8 01             	cmp    $0x1,%eax
    2565:	74 0a                	je     2571 <barriered_work+0x51>
    2567:	0f ae f0             	mfence
    256a:	31 c0                	xor    %eax,%eax
    256c:	5b                   	pop    %rbx
    256d:	5d                   	pop    %rbp
    256e:	41 5c                	pop    %r12
    2570:	c3                   	ret
    2571:	8b 43 3c             	mov    0x3c(%rbx),%eax
    2574:	85 c0                	test   %eax,%eax
    2576:	7e ef                	jle    2567 <barriered_work+0x47>
    2578:	45 31 c9             	xor    %r9d,%r9d
    257b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2580:	8b 43 38             	mov    0x38(%rbx),%eax
    2583:	44 39 c8             	cmp    %r9d,%eax
    2586:	74 5e                	je     25e6 <barriered_work+0xc6>
    2588:	48 8b 43 70          	mov    0x70(%rbx),%rax
    258c:	4c 89 c9             	mov    %r9,%rcx
    258f:	48 c1 e1 05          	shl    $0x5,%rcx
    2593:	48 8b 54 08 08       	mov    0x8(%rax,%rcx,1),%rdx
    2598:	48 8b 42 08          	mov    0x8(%rdx),%rax
    259c:	48 63 7a 10          	movslq 0x10(%rdx),%rdi
    25a0:	48 39 f8             	cmp    %rdi,%rax
    25a3:	7d 41                	jge    25e6 <barriered_work+0xc6>
    25a5:	4c 8b 02             	mov    (%rdx),%r8
    25a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    25b0:	48 8b 43 10          	mov    0x10(%rbx),%rax
    25b4:	48 83 c0 01          	add    $0x1,%rax
    25b8:	48 89 43 10          	mov    %rax,0x10(%rbx)
    25bc:	48 8b 43 70          	mov    0x70(%rbx),%rax
    25c0:	48 83 44 08 10 01    	addq   $0x1,0x10(%rax,%rcx,1)
    25c6:	48 8b 42 08          	mov    0x8(%rdx),%rax
    25ca:	48 8d 70 01          	lea    0x1(%rax),%rsi
    25ce:	48 89 72 08          	mov    %rsi,0x8(%rdx)
    25d2:	48 8b b3 88 00 00 00 	mov    0x88(%rbx),%rsi
    25d9:	49 89 34 c0          	mov    %rsi,(%r8,%rax,8)
    25dd:	48 8b 42 08          	mov    0x8(%rdx),%rax
    25e1:	48 39 f8             	cmp    %rdi,%rax
    25e4:	7c ca                	jl     25b0 <barriered_work+0x90>
    25e6:	8b 43 3c             	mov    0x3c(%rbx),%eax
    25e9:	49 83 c1 01          	add    $0x1,%r9
    25ed:	44 39 c8             	cmp    %r9d,%eax
    25f0:	7f 8e                	jg     2580 <barriered_work+0x60>
    25f2:	e9 70 ff ff ff       	jmp    2567 <barriered_work+0x47>
    25f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    2600:	e8 2b fe ff ff       	call   2430 <receive>
    2605:	8b 3b                	mov    (%rbx),%edi
    2607:	8b 43 3c             	mov    0x3c(%rbx),%eax
    260a:	85 c0                	test   %eax,%eax
    260c:	0f 8e b3 00 00 00    	jle    26c5 <barriered_work+0x1a5>
    2612:	48 63 c7             	movslq %edi,%rax
    2615:	31 ed                	xor    %ebp,%ebp
    2617:	83 c7 01             	add    $0x1,%edi
    261a:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    261e:	4c 8d 1c 50          	lea    (%rax,%rdx,2),%r11
    2622:	49 c1 e3 03          	shl    $0x3,%r11
    2626:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    2630:	8b 43 3c             	mov    0x3c(%rbx),%eax
    2633:	49 89 ea             	mov    %rbp,%r10
    2636:	49 89 e9             	mov    %rbp,%r9
    2639:	31 c9                	xor    %ecx,%ecx
    263b:	49 c1 e2 06          	shl    $0x6,%r10
    263f:	49 c1 e1 05          	shl    $0x5,%r9
    2643:	85 c0                	test   %eax,%eax
    2645:	7e 6f                	jle    26b6 <barriered_work+0x196>
    2647:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    2650:	44 8b 63 3c          	mov    0x3c(%rbx),%r12d
    2654:	48 8b 43 30          	mov    0x30(%rbx),%rax
    2658:	48 8b 40 10          	mov    0x10(%rax),%rax
    265c:	4a 8b 74 10 20       	mov    0x20(%rax,%r10,1),%rsi
    2661:	4c 01 de             	add    %r11,%rsi
    2664:	4c 8b 46 70          	mov    0x70(%rsi),%r8
    2668:	48 8b 43 30          	mov    0x30(%rbx),%rax
    266c:	48 89 ce             	mov    %rcx,%rsi
    266f:	48 c1 e6 06          	shl    $0x6,%rsi
    2673:	48 03 70 10          	add    0x10(%rax),%rsi
    2677:	89 f8                	mov    %edi,%eax
    2679:	99                   	cltd
    267a:	41 f7 fc             	idiv   %r12d
    267d:	89 d0                	mov    %edx,%eax
    267f:	f7 d8                	neg    %eax
    2681:	0f 49 d0             	cmovns %eax,%edx
    2684:	48 63 d2             	movslq %edx,%rdx
    2687:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    268b:	48 8d 14 42          	lea    (%rdx,%rax,2),%rdx
    268f:	48 8b 46 20          	mov    0x20(%rsi),%rax
    2693:	48 8d 04 d0          	lea    (%rax,%rdx,8),%rax
    2697:	48 89 ca             	mov    %rcx,%rdx
    269a:	48 83 c1 01          	add    $0x1,%rcx
    269e:	48 c1 e2 05          	shl    $0x5,%rdx
    26a2:	48 8b 40 70          	mov    0x70(%rax),%rax
    26a6:	49 8b 54 10 08       	mov    0x8(%r8,%rdx,1),%rdx
    26ab:	4a 89 14 08          	mov    %rdx,(%rax,%r9,1)
    26af:	8b 43 3c             	mov    0x3c(%rbx),%eax
    26b2:	39 c8                	cmp    %ecx,%eax
    26b4:	7f 9a                	jg     2650 <barriered_work+0x130>
    26b6:	8b 43 3c             	mov    0x3c(%rbx),%eax
    26b9:	48 83 c5 01          	add    $0x1,%rbp
    26bd:	39 e8                	cmp    %ebp,%eax
    26bf:	0f 8f 6b ff ff ff    	jg     2630 <barriered_work+0x110>
    26c5:	0f ae f0             	mfence
    26c8:	48 8b 73 50          	mov    0x50(%rbx),%rsi
    26cc:	48 8b 43 60          	mov    0x60(%rbx),%rax
    26d0:	31 ff                	xor    %edi,%edi
    26d2:	48 c1 e0 05          	shl    $0x5,%rax
    26d6:	48 01 c6             	add    %rax,%rsi
    26d9:	e8 52 ea ff ff       	call   1130 <clock_gettime@plt>
    26de:	48 8b 43 30          	mov    0x30(%rbx),%rax
    26e2:	48 8b 40 30          	mov    0x30(%rax),%rax
    26e6:	8b 78 10             	mov    0x10(%rax),%edi
    26e9:	8d 6f 01             	lea    0x1(%rdi),%ebp
    26ec:	89 68 10             	mov    %ebp,0x10(%rax)
    26ef:	8b 43 48             	mov    0x48(%rbx),%eax
    26f2:	83 f8 01             	cmp    $0x1,%eax
    26f5:	75 46                	jne    273d <barriered_work+0x21d>
    26f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    2700:	48 8b 43 10          	mov    0x10(%rbx),%rax
    2704:	48 83 c0 01          	add    $0x1,%rax
    2708:	48 89 43 10          	mov    %rax,0x10(%rbx)
    270c:	48 8b 4b 28          	mov    0x28(%rbx),%rcx
    2710:	48 8b 73 30          	mov    0x30(%rbx),%rsi
    2714:	48 63 43 38          	movslq 0x38(%rbx),%rax
    2718:	48 63 13             	movslq (%rbx),%rdx
    271b:	48 c1 e0 06          	shl    $0x6,%rax
    271f:	48 03 46 10          	add    0x10(%rsi),%rax
    2723:	48 8b 40 20          	mov    0x20(%rax),%rax
    2727:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
    272b:	48 8d 14 72          	lea    (%rdx,%rsi,2),%rdx
    272f:	48 8d 3c d0          	lea    (%rax,%rdx,8),%rdi
    2733:	ff d1                	call   *%rcx
    2735:	8b 43 48             	mov    0x48(%rbx),%eax
    2738:	83 f8 01             	cmp    $0x1,%eax
    273b:	74 c3                	je     2700 <barriered_work+0x1e0>
    273d:	48 8b 43 30          	mov    0x30(%rbx),%rax
    2741:	48 8b 40 30          	mov    0x30(%rax),%rax
    2745:	3b 68 10             	cmp    0x10(%rax),%ebp
    2748:	75 32                	jne    277c <barriered_work+0x25c>
    274a:	48 8b 53 50          	mov    0x50(%rbx),%rdx
    274e:	48 8b 43 60          	mov    0x60(%rbx),%rax
    2752:	31 ff                	xor    %edi,%edi
    2754:	48 c1 e0 05          	shl    $0x5,%rax
    2758:	48 8d 74 02 10       	lea    0x10(%rdx,%rax,1),%rsi
    275d:	e8 ce e9 ff ff       	call   1130 <clock_gettime@plt>
    2762:	48 8b 43 60          	mov    0x60(%rbx),%rax
    2766:	48 8b 4b 58          	mov    0x58(%rbx),%rcx
    276a:	48 83 c0 01          	add    $0x1,%rax
    276e:	48 99                	cqto
    2770:	48 f7 f9             	idiv   %rcx
    2773:	48 89 53 60          	mov    %rdx,0x60(%rbx)
    2777:	e9 eb fd ff ff       	jmp    2567 <barriered_work+0x47>
    277c:	48 8d 3d 1b 09 00 00 	lea    0x91b(%rip),%rdi        # 309e <_IO_stdin_used+0x9e>
    2783:	e8 98 e9 ff ff       	call   1120 <puts@plt>
    2788:	eb c0                	jmp    274a <barriered_work+0x22a>
    278a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002790 <barriered_work_ingest>:
    2790:	f3 0f 1e fa          	endbr64
    2794:	48 83 ec 08          	sub    $0x8,%rsp
    2798:	48 8b 47 30          	mov    0x30(%rdi),%rax
    279c:	48 8b 40 38          	mov    0x38(%rax),%rax
    27a0:	8b 00                	mov    (%rax),%eax
    27a2:	85 c0                	test   %eax,%eax
    27a4:	7e 57                	jle    27fd <barriered_work_ingest+0x6d>
    27a6:	31 c0                	xor    %eax,%eax
    27a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    27b0:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
    27b4:	48 89 c2             	mov    %rax,%rdx
    27b7:	48 c1 e2 04          	shl    $0x4,%rdx
    27bb:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    27bf:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    27c3:	48 01 d6             	add    %rdx,%rsi
    27c6:	8b 4e 08             	mov    0x8(%rsi),%ecx
    27c9:	83 f9 01             	cmp    $0x1,%ecx
    27cc:	75 1f                	jne    27ed <barriered_work_ingest+0x5d>
    27ce:	48 8b 4f 68          	mov    0x68(%rdi),%rcx
    27d2:	48 83 c1 01          	add    $0x1,%rcx
    27d6:	48 89 4f 68          	mov    %rcx,0x68(%rdi)
    27da:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
    27de:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    27e2:	48 03 51 08          	add    0x8(%rcx),%rdx
    27e6:	c7 42 08 00 00 00 00 	movl   $0x0,0x8(%rdx)
    27ed:	48 8b 57 30          	mov    0x30(%rdi),%rdx
    27f1:	48 83 c0 01          	add    $0x1,%rax
    27f5:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    27f9:	39 02                	cmp    %eax,(%rdx)
    27fb:	7f b3                	jg     27b0 <barriered_work_ingest+0x20>
    27fd:	0f ae f0             	mfence
    2800:	e8 1b fd ff ff       	call   2520 <barriered_work>
    2805:	31 c0                	xor    %eax,%eax
    2807:	48 83 c4 08          	add    $0x8,%rsp
    280b:	c3                   	ret
    280c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000002810 <barriered_nulltask>:
    2810:	f3 0f 1e fa          	endbr64
    2814:	31 c0                	xor    %eax,%eax
    2816:	c3                   	ret
    2817:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000002820 <barriered_steal>:
    2820:	f3 0f 1e fa          	endbr64
    2824:	31 c0                	xor    %eax,%eax
    2826:	c3                   	ret
    2827:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000002830 <after>:
    2830:	f3 0f 1e fa          	endbr64
    2834:	31 c0                	xor    %eax,%eax
    2836:	48 39 d7             	cmp    %rdx,%rdi
    2839:	7e 08                	jle    2843 <after+0x13>
    283b:	31 c0                	xor    %eax,%eax
    283d:	48 39 ce             	cmp    %rcx,%rsi
    2840:	0f 9f c0             	setg   %al
    2843:	c3                   	ret
    2844:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    284f:	90                   	nop

0000000000002850 <within>:
    2850:	f3 0f 1e fa          	endbr64
    2854:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    2859:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    285e:	31 c0                	xor    %eax,%eax
    2860:	48 39 d7             	cmp    %rdx,%rdi
    2863:	7f 18                	jg     287d <within+0x2d>
    2865:	4d 39 d8             	cmp    %r11,%r8
    2868:	0f 9e c2             	setle  %dl
    286b:	48 39 ce             	cmp    %rcx,%rsi
    286e:	0f 9e c0             	setle  %al
    2871:	21 c2                	and    %eax,%edx
    2873:	31 c0                	xor    %eax,%eax
    2875:	4d 39 d1             	cmp    %r10,%r9
    2878:	0f 9e c0             	setle  %al
    287b:	21 d0                	and    %edx,%eax
    287d:	c3                   	ret
    287e:	66 90                	xchg   %ax,%ax

0000000000002880 <overlap>:
    2880:	f3 0f 1e fa          	endbr64
    2884:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    2889:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    288e:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2893:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    2898:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
    289d:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    28a2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    28a7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    28ac:	48 39 fe             	cmp    %rdi,%rsi
    28af:	7d 2f                	jge    28e0 <overlap+0x60>
    28b1:	48 39 ca             	cmp    %rcx,%rdx
    28b4:	7d 62                	jge    2918 <overlap+0x98>
    28b6:	4d 39 da             	cmp    %r11,%r10
    28b9:	7e 0e                	jle    28c9 <overlap+0x49>
    28bb:	b8 01 00 00 00       	mov    $0x1,%eax
    28c0:	4d 39 c1             	cmp    %r8,%r9
    28c3:	0f 8f 7f 00 00 00    	jg     2948 <overlap+0xc8>
    28c9:	31 c0                	xor    %eax,%eax
    28cb:	4d 39 c1             	cmp    %r8,%r9
    28ce:	7c 4c                	jl     291c <overlap+0x9c>
    28d0:	31 c0                	xor    %eax,%eax
    28d2:	4d 39 da             	cmp    %r11,%r10
    28d5:	0f 9d c0             	setge  %al
    28d8:	c3                   	ret
    28d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    28e0:	7e 4e                	jle    2930 <overlap+0xb0>
    28e2:	48 39 ca             	cmp    %rcx,%rdx
    28e5:	7f 39                	jg     2920 <overlap+0xa0>
    28e7:	75 31                	jne    291a <overlap+0x9a>
    28e9:	4d 39 c1             	cmp    %r8,%r9
    28ec:	7f 2c                	jg     291a <overlap+0x9a>
    28ee:	b8 01 00 00 00       	mov    $0x1,%eax
    28f3:	4d 39 da             	cmp    %r11,%r10
    28f6:	7e 24                	jle    291c <overlap+0x9c>
    28f8:	48 39 ca             	cmp    %rcx,%rdx
    28fb:	0f 94 c2             	sete   %dl
    28fe:	48 39 fe             	cmp    %rdi,%rsi
    2901:	0f 94 c0             	sete   %al
    2904:	21 c2                	and    %eax,%edx
    2906:	31 c0                	xor    %eax,%eax
    2908:	4d 39 c1             	cmp    %r8,%r9
    290b:	0f 94 c0             	sete   %al
    290e:	21 d0                	and    %edx,%eax
    2910:	c3                   	ret
    2911:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    2918:	74 af                	je     28c9 <overlap+0x49>
    291a:	31 c0                	xor    %eax,%eax
    291c:	c3                   	ret
    291d:	0f 1f 00             	nopl   (%rax)
    2920:	4d 39 c1             	cmp    %r8,%r9
    2923:	7d c4                	jge    28e9 <overlap+0x69>
    2925:	b8 01 00 00 00       	mov    $0x1,%eax
    292a:	4d 39 da             	cmp    %r11,%r10
    292d:	7d ba                	jge    28e9 <overlap+0x69>
    292f:	c3                   	ret
    2930:	48 39 ca             	cmp    %rcx,%rdx
    2933:	7c 94                	jl     28c9 <overlap+0x49>
    2935:	4d 39 c1             	cmp    %r8,%r9
    2938:	7e b4                	jle    28ee <overlap+0x6e>
    293a:	48 39 ca             	cmp    %rcx,%rdx
    293d:	74 91                	je     28d0 <overlap+0x50>
    293f:	eb d9                	jmp    291a <overlap+0x9a>
    2941:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    2948:	c3                   	ret
    2949:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000002950 <verify>:
    2950:	f3 0f 1e fa          	endbr64
    2954:	85 f6                	test   %esi,%esi
    2956:	0f 8e 0a 03 00 00    	jle    2c66 <verify+0x316>
    295c:	41 57                	push   %r15
    295e:	45 31 ff             	xor    %r15d,%r15d
    2961:	41 56                	push   %r14
    2963:	41 89 f6             	mov    %esi,%r14d
    2966:	41 55                	push   %r13
    2968:	4c 8d 6f 20          	lea    0x20(%rdi),%r13
    296c:	41 54                	push   %r12
    296e:	55                   	push   %rbp
    296f:	53                   	push   %rbx
    2970:	48 83 ec 48          	sub    $0x48,%rsp
    2974:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    2979:	4c 89 6c 24 08       	mov    %r13,0x8(%rsp)
    297e:	45 31 e4             	xor    %r12d,%r12d
    2981:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    2986:	45 39 e7             	cmp    %r12d,%r15d
    2989:	0f 84 37 02 00 00    	je     2bc6 <verify+0x276>
    298f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    2994:	8b 50 08             	mov    0x8(%rax),%edx
    2997:	85 d2                	test   %edx,%edx
    2999:	0f 8e 27 02 00 00    	jle    2bc6 <verify+0x276>
    299f:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    29a8:	31 ed                	xor    %ebp,%ebp
    29aa:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    29af:	44 89 fa             	mov    %r15d,%edx
    29b2:	48 8d 35 f5 06 00 00 	lea    0x6f5(%rip),%rsi        # 30ae <_IO_stdin_used+0xae>
    29b9:	bf 01 00 00 00       	mov    $0x1,%edi
    29be:	31 c0                	xor    %eax,%eax
    29c0:	e8 cb e7 ff ff       	call   1190 <__printf_chk@plt>
    29c5:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    29ca:	8b 40 08             	mov    0x8(%rax),%eax
    29cd:	85 c0                	test   %eax,%eax
    29cf:	0f 8e d2 01 00 00    	jle    2ba7 <verify+0x257>
    29d5:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    29da:	89 6c 24 34          	mov    %ebp,0x34(%rsp)
    29de:	45 31 e4             	xor    %r12d,%r12d
    29e1:	44 89 7c 24 38       	mov    %r15d,0x38(%rsp)
    29e6:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    29eb:	44 89 74 24 3c       	mov    %r14d,0x3c(%rsp)
    29f0:	4c 03 28             	add    (%rax),%r13
    29f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    29f8:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    29fd:	4b 8d 04 e4          	lea    (%r12,%r12,8),%rax
    2a01:	49 8b 4d 60          	mov    0x60(%r13),%rcx
    2a05:	48 8d 35 b7 06 00 00 	lea    0x6b7(%rip),%rsi        # 30c3 <_IO_stdin_used+0xc3>
    2a0c:	49 8d 2c 44          	lea    (%r12,%rax,2),%rbp
    2a10:	bf 01 00 00 00       	mov    $0x1,%edi
    2a15:	48 8b 03             	mov    (%rbx),%rax
    2a18:	48 c1 e5 03          	shl    $0x3,%rbp
    2a1c:	48 01 e8             	add    %rbp,%rax
    2a1f:	48 8b 50 60          	mov    0x60(%rax),%rdx
    2a23:	31 c0                	xor    %eax,%eax
    2a25:	e8 66 e7 ff ff       	call   1190 <__printf_chk@plt>
    2a2a:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    2a2f:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    2a34:	4c 03 28             	add    (%rax),%r13
    2a37:	49 8b 45 60          	mov    0x60(%r13),%rax
    2a3b:	48 85 c0             	test   %rax,%rax
    2a3e:	0f 8e 42 01 00 00    	jle    2b86 <verify+0x236>
    2a44:	48 8b 13             	mov    (%rbx),%rdx
    2a47:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    2a4c:	45 31 ff             	xor    %r15d,%r15d
    2a4f:	48 01 ea             	add    %rbp,%rdx
    2a52:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    2a58:	48 8b 42 60          	mov    0x60(%rdx),%rax
    2a5c:	4d 89 fc             	mov    %r15,%r12
    2a5f:	31 db                	xor    %ebx,%ebx
    2a61:	49 c1 e4 05          	shl    $0x5,%r12
    2a65:	48 85 c0             	test   %rax,%rax
    2a68:	7f 37                	jg     2aa1 <verify+0x151>
    2a6a:	e9 01 01 00 00       	jmp    2b70 <verify+0x220>
    2a6f:	90                   	nop
    2a70:	48 39 f1             	cmp    %rsi,%rcx
    2a73:	0f 8d 67 01 00 00    	jge    2be0 <verify+0x290>
    2a79:	4d 39 da             	cmp    %r11,%r10
    2a7c:	7e 09                	jle    2a87 <verify+0x137>
    2a7e:	49 39 c6             	cmp    %rax,%r14
    2a81:	0f 8c 81 00 00 00    	jl     2b08 <verify+0x1b8>
    2a87:	4d 39 da             	cmp    %r11,%r10
    2a8a:	0f 8d 9b 01 00 00    	jge    2c2b <verify+0x2db>
    2a90:	48 8b 42 60          	mov    0x60(%rdx),%rax
    2a94:	48 83 c3 01          	add    $0x1,%rbx
    2a98:	48 39 d8             	cmp    %rbx,%rax
    2a9b:	0f 8e cf 00 00 00    	jle    2b70 <verify+0x220>
    2aa1:	48 8b 42 50          	mov    0x50(%rdx),%rax
    2aa5:	49 89 d9             	mov    %rbx,%r9
    2aa8:	49 8b 4d 50          	mov    0x50(%r13),%rcx
    2aac:	49 c1 e1 05          	shl    $0x5,%r9
    2ab0:	4c 01 e1             	add    %r12,%rcx
    2ab3:	4c 01 c8             	add    %r9,%rax
    2ab6:	4c 8b 01             	mov    (%rcx),%r8
    2ab9:	48 8b 38             	mov    (%rax),%rdi
    2abc:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    2ac0:	4c 8b 59 10          	mov    0x10(%rcx),%r11
    2ac4:	4c 8b 71 18          	mov    0x18(%rcx),%r14
    2ac8:	4c 8b 50 10          	mov    0x10(%rax),%r10
    2acc:	48 8b 48 08          	mov    0x8(%rax),%rcx
    2ad0:	48 8b 40 18          	mov    0x18(%rax),%rax
    2ad4:	4c 39 c7             	cmp    %r8,%rdi
    2ad7:	7c 97                	jl     2a70 <verify+0x120>
    2ad9:	0f 8e 31 01 00 00    	jle    2c10 <verify+0x2c0>
    2adf:	48 39 f1             	cmp    %rsi,%rcx
    2ae2:	0f 8f 08 01 00 00    	jg     2bf0 <verify+0x2a0>
    2ae8:	75 a6                	jne    2a90 <verify+0x140>
    2aea:	4d 39 da             	cmp    %r11,%r10
    2aed:	7f a1                	jg     2a90 <verify+0x140>
    2aef:	49 39 c6             	cmp    %rax,%r14
    2af2:	7d 14                	jge    2b08 <verify+0x1b8>
    2af4:	4c 39 c7             	cmp    %r8,%rdi
    2af7:	75 97                	jne    2a90 <verify+0x140>
    2af9:	48 39 f1             	cmp    %rsi,%rcx
    2afc:	75 92                	jne    2a90 <verify+0x140>
    2afe:	4d 39 da             	cmp    %r11,%r10
    2b01:	75 8d                	jne    2a90 <verify+0x140>
    2b03:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2b08:	48 8b 72 50          	mov    0x50(%rdx),%rsi
    2b0c:	49 8b 45 50          	mov    0x50(%r13),%rax
    2b10:	bf 01 00 00 00       	mov    $0x1,%edi
    2b15:	48 83 c3 01          	add    $0x1,%rbx
    2b19:	48 8b 4a 50          	mov    0x50(%rdx),%rcx
    2b1d:	49 8b 55 50          	mov    0x50(%r13),%rdx
    2b21:	4e 8b 44 20 08       	mov    0x8(%rax,%r12,1),%r8
    2b26:	31 c0                	xor    %eax,%eax
    2b28:	4a 8b 4c 09 10       	mov    0x10(%rcx,%r9,1),%rcx
    2b2d:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    2b31:	4e 8b 4c 0e 18       	mov    0x18(%rsi,%r9,1),%r9
    2b36:	48 8d 35 a3 06 00 00 	lea    0x6a3(%rip),%rsi        # 31e0 <_IO_stdin_used+0x1e0>
    2b3d:	e8 4e e6 ff ff       	call   1190 <__printf_chk@plt>
    2b42:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    2b47:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    2b4c:	4c 03 28             	add    (%rax),%r13
    2b4f:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    2b54:	48 8b 10             	mov    (%rax),%rdx
    2b57:	48 01 ea             	add    %rbp,%rdx
    2b5a:	48 8b 42 60          	mov    0x60(%rdx),%rax
    2b5e:	48 39 d8             	cmp    %rbx,%rax
    2b61:	0f 8f 3a ff ff ff    	jg     2aa1 <verify+0x151>
    2b67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    2b70:	49 8b 45 60          	mov    0x60(%r13),%rax
    2b74:	49 83 c7 01          	add    $0x1,%r15
    2b78:	4c 39 f8             	cmp    %r15,%rax
    2b7b:	0f 8f d7 fe ff ff    	jg     2a58 <verify+0x108>
    2b81:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
    2b86:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    2b8b:	49 83 c4 01          	add    $0x1,%r12
    2b8f:	44 39 60 08          	cmp    %r12d,0x8(%rax)
    2b93:	0f 8f 5f fe ff ff    	jg     29f8 <verify+0xa8>
    2b99:	8b 6c 24 34          	mov    0x34(%rsp),%ebp
    2b9d:	44 8b 7c 24 38       	mov    0x38(%rsp),%r15d
    2ba2:	44 8b 74 24 3c       	mov    0x3c(%rsp),%r14d
    2ba7:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    2bac:	83 c5 01             	add    $0x1,%ebp
    2baf:	48 81 44 24 18 98 00 00 00 	addq   $0x98,0x18(%rsp)
    2bb8:	39 68 08             	cmp    %ebp,0x8(%rax)
    2bbb:	0f 8f ee fd ff ff    	jg     29af <verify+0x5f>
    2bc1:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    2bc6:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    2bcb:	48 83 44 24 08 40    	addq   $0x40,0x8(%rsp)
    2bd1:	41 39 c6             	cmp    %eax,%r14d
    2bd4:	74 63                	je     2c39 <verify+0x2e9>
    2bd6:	41 89 c4             	mov    %eax,%r12d
    2bd9:	e9 a8 fd ff ff       	jmp    2986 <verify+0x36>
    2bde:	66 90                	xchg   %ax,%ax
    2be0:	0f 85 aa fe ff ff    	jne    2a90 <verify+0x140>
    2be6:	e9 9c fe ff ff       	jmp    2a87 <verify+0x137>
    2beb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2bf0:	49 39 c6             	cmp    %rax,%r14
    2bf3:	0f 8e f1 fe ff ff    	jle    2aea <verify+0x19a>
    2bf9:	4d 39 da             	cmp    %r11,%r10
    2bfc:	0f 8d e8 fe ff ff    	jge    2aea <verify+0x19a>
    2c02:	e9 01 ff ff ff       	jmp    2b08 <verify+0x1b8>
    2c07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    2c10:	48 39 f1             	cmp    %rsi,%rcx
    2c13:	0f 8c 6e fe ff ff    	jl     2a87 <verify+0x137>
    2c19:	4d 39 da             	cmp    %r11,%r10
    2c1c:	0f 8e cd fe ff ff    	jle    2aef <verify+0x19f>
    2c22:	48 39 f1             	cmp    %rsi,%rcx
    2c25:	0f 85 65 fe ff ff    	jne    2a90 <verify+0x140>
    2c2b:	49 39 c6             	cmp    %rax,%r14
    2c2e:	0f 8f 5c fe ff ff    	jg     2a90 <verify+0x140>
    2c34:	e9 cf fe ff ff       	jmp    2b08 <verify+0x1b8>
    2c39:	48 83 44 24 10 40    	addq   $0x40,0x10(%rsp)
    2c3f:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    2c44:	41 8d 47 01          	lea    0x1(%r15),%eax
    2c48:	45 39 e7             	cmp    %r12d,%r15d
    2c4b:	74 08                	je     2c55 <verify+0x305>
    2c4d:	41 89 c7             	mov    %eax,%r15d
    2c50:	e9 24 fd ff ff       	jmp    2979 <verify+0x29>
    2c55:	48 83 c4 48          	add    $0x48,%rsp
    2c59:	31 c0                	xor    %eax,%eax
    2c5b:	5b                   	pop    %rbx
    2c5c:	5d                   	pop    %rbp
    2c5d:	41 5c                	pop    %r12
    2c5f:	41 5d                	pop    %r13
    2c61:	41 5e                	pop    %r14
    2c63:	41 5f                	pop    %r15
    2c65:	c3                   	ret
    2c66:	31 c0                	xor    %eax,%eax
    2c68:	c3                   	ret

Disassembly of section .fini:

0000000000002c6c <_fini>:
    2c6c:	f3 0f 1e fa          	endbr64
    2c70:	48 83 ec 08          	sub    $0x8,%rsp
    2c74:	48 83 c4 08          	add    $0x8,%rsp
    2c78:	c3                   	ret
