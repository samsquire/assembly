
branchless:     file format elf64-x86-64


Disassembly of section .init:

0000000000001000 <_init>:
    1000:	f3 0f 1e fa          	endbr64
    1004:	48 83 ec 08          	sub    $0x8,%rsp
    1008:	48 8d 05 e1 01 00 00 	lea    0x1e1(%rip),%rax        # 11f0 <__gmon_start__>
    100f:	48 85 c0             	test   %rax,%rax
    1012:	74 02                	je     1016 <_init+0x16>
    1014:	ff d0                	call   *%rax
    1016:	48 83 c4 08          	add    $0x8,%rsp
    101a:	c3                   	ret

Disassembly of section .plt:

0000000000001020 <.plt>:
    1020:	ff 35 5a 2f 00 00    	push   0x2f5a(%rip)        # 3f80 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:	ff 25 5c 2f 00 00    	jmp    *0x2f5c(%rip)        # 3f88 <_GLOBAL_OFFSET_TABLE_+0x10>
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

Disassembly of section .plt.got:

00000000000010b0 <__cxa_finalize@plt>:
    10b0:	f3 0f 1e fa          	endbr64
    10b4:	ff 25 3e 2f 00 00    	jmp    *0x2f3e(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    10ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

00000000000010c0 <free@plt>:
    10c0:	f3 0f 1e fa          	endbr64
    10c4:	ff 25 c6 2e 00 00    	jmp    *0x2ec6(%rip)        # 3f90 <free@GLIBC_2.2.5>
    10ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010d0 <puts@plt>:
    10d0:	f3 0f 1e fa          	endbr64
    10d4:	ff 25 be 2e 00 00    	jmp    *0x2ebe(%rip)        # 3f98 <puts@GLIBC_2.2.5>
    10da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010e0 <__stack_chk_fail@plt>:
    10e0:	f3 0f 1e fa          	endbr64
    10e4:	ff 25 b6 2e 00 00    	jmp    *0x2eb6(%rip)        # 3fa0 <__stack_chk_fail@GLIBC_2.4>
    10ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010f0 <__monstartup@plt>:
    10f0:	f3 0f 1e fa          	endbr64
    10f4:	ff 25 ae 2e 00 00    	jmp    *0x2eae(%rip)        # 3fa8 <__monstartup@GLIBC_2.2.5>
    10fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001100 <strtol@plt>:
    1100:	f3 0f 1e fa          	endbr64
    1104:	ff 25 a6 2e 00 00    	jmp    *0x2ea6(%rip)        # 3fb0 <strtol@GLIBC_2.2.5>
    110a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001110 <__printf_chk@plt>:
    1110:	f3 0f 1e fa          	endbr64
    1114:	ff 25 9e 2e 00 00    	jmp    *0x2e9e(%rip)        # 3fb8 <__printf_chk@GLIBC_2.3.4>
    111a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001120 <__cxa_atexit@plt>:
    1120:	f3 0f 1e fa          	endbr64
    1124:	ff 25 96 2e 00 00    	jmp    *0x2e96(%rip)        # 3fc0 <__cxa_atexit@GLIBC_2.2.5>
    112a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001130 <getline@plt>:
    1130:	f3 0f 1e fa          	endbr64
    1134:	ff 25 8e 2e 00 00    	jmp    *0x2e8e(%rip)        # 3fc8 <getline@GLIBC_2.2.5>
    113a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000001140 <main>:

    return num;
}

int main(int argc, char *argv[])
{
    1140:	f3 0f 1e fa          	endbr64
    1144:	55                   	push   %rbp
    1145:	48 89 e5             	mov    %rsp,%rbp
    1148:	41 54                	push   %r12
    114a:	53                   	push   %rbx
    114b:	ff 15 97 2e 00 00    	call   *0x2e97(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
    int num1 = getnum();
    1151:	31 c0                	xor    %eax,%eax
    1153:	e8 b8 01 00 00       	call   1310 <getnum>
    1158:	89 c3                	mov    %eax,%ebx
    int num2 = getnum();
    115a:	31 c0                	xor    %eax,%eax
    115c:	e8 af 01 00 00       	call   1310 <getnum>
    1161:	41 89 c4             	mov    %eax,%r12d
    int num3 = getnum();
    1164:	31 c0                	xor    %eax,%eax
    1166:	e8 a5 01 00 00       	call   1310 <getnum>
    long c = (num1 > 1500);
    long m = (num2 > 1600) << 1;
    long z = (num3 > 1700) << 2;
    116b:	31 d2                	xor    %edx,%edx
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    116d:	bf 01 00 00 00       	mov    $0x1,%edi
    1172:	48 8d 35 c1 0e 00 00 	lea    0xec1(%rip),%rsi        # 203a <_IO_stdin_used+0x3a>
    1179:	3d a4 06 00 00       	cmp    $0x6a4,%eax
    117e:	0f 9f c2             	setg   %dl
    long m = (num2 > 1600) << 1;
    1181:	31 c0                	xor    %eax,%eax
    long z = (num3 > 1700) << 2;
    1183:	48 c1 e2 02          	shl    $0x2,%rdx
    long m = (num2 > 1600) << 1;
    1187:	41 81 fc 40 06 00 00 	cmp    $0x640,%r12d
    118e:	0f 9f c0             	setg   %al
    1191:	48 01 c0             	add    %rax,%rax

    printf("result: %ld\n",  c | m | z);
    1194:	48 09 c2             	or     %rax,%rdx
    long c = (num1 > 1500);
    1197:	31 c0                	xor    %eax,%eax
    1199:	81 fb dc 05 00 00    	cmp    $0x5dc,%ebx
    119f:	0f 9f c0             	setg   %al
    printf("result: %ld\n",  c | m | z);
    11a2:	48 09 c2             	or     %rax,%rdx
    11a5:	31 c0                	xor    %eax,%eax
    11a7:	e8 64 ff ff ff       	call   1110 <__printf_chk@plt>

    return 0;
}
    11ac:	5b                   	pop    %rbx
    11ad:	31 c0                	xor    %eax,%eax
    11af:	41 5c                	pop    %r12
    11b1:	5d                   	pop    %rbp
    11b2:	c3                   	ret
    11b3:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    11bd:	0f 1f 00             	nopl   (%rax)

00000000000011c0 <_start>:
    11c0:	f3 0f 1e fa          	endbr64
    11c4:	31 ed                	xor    %ebp,%ebp
    11c6:	49 89 d1             	mov    %rdx,%r9
    11c9:	5e                   	pop    %rsi
    11ca:	48 89 e2             	mov    %rsp,%rdx
    11cd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    11d1:	50                   	push   %rax
    11d2:	54                   	push   %rsp
    11d3:	45 31 c0             	xor    %r8d,%r8d
    11d6:	31 c9                	xor    %ecx,%ecx
    11d8:	48 8d 3d 61 ff ff ff 	lea    -0x9f(%rip),%rdi        # 1140 <main>
    11df:	ff 15 eb 2d 00 00    	call   *0x2deb(%rip)        # 3fd0 <__libc_start_main@GLIBC_2.34>
    11e5:	f4                   	hlt
    11e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000011f0 <__gmon_start__>:
    11f0:	f3 0f 1e fa          	endbr64
    11f4:	8b 05 1e 2e 00 00    	mov    0x2e1e(%rip),%eax        # 4018 <called.0>
    11fa:	85 c0                	test   %eax,%eax
    11fc:	74 02                	je     1200 <__gmon_start__+0x10>
    11fe:	c3                   	ret
    11ff:	90                   	nop
    1200:	48 83 ec 08          	sub    $0x8,%rsp
    1204:	48 8d 35 22 02 00 00 	lea    0x222(%rip),%rsi        # 142d <etext>
    120b:	48 8d 3d ee ed ff ff 	lea    -0x1212(%rip),%rdi        # 0 <__executable_start>
    1212:	c7 05 fc 2d 00 00 01 00 00 00 	movl   $0x1,0x2dfc(%rip)        # 4018 <called.0>
    121c:	e8 cf fe ff ff       	call   10f0 <__monstartup@plt>
    1221:	48 8b 3d b8 2d 00 00 	mov    0x2db8(%rip),%rdi        # 3fe0 <_mcleanup@GLIBC_2.2.5>
    1228:	48 83 c4 08          	add    $0x8,%rsp
    122c:	e9 bf 01 00 00       	jmp    13f0 <atexit>
    1231:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    123b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000001240 <_dl_relocate_static_pie>:
    1240:	f3 0f 1e fa          	endbr64
    1244:	c3                   	ret
    1245:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    124f:	90                   	nop

0000000000001250 <deregister_tm_clones>:
    1250:	48 8d 3d b9 2d 00 00 	lea    0x2db9(%rip),%rdi        # 4010 <stdin@GLIBC_2.2.5>
    1257:	48 8d 05 b2 2d 00 00 	lea    0x2db2(%rip),%rax        # 4010 <stdin@GLIBC_2.2.5>
    125e:	48 39 f8             	cmp    %rdi,%rax
    1261:	74 15                	je     1278 <deregister_tm_clones+0x28>
    1263:	48 8b 05 6e 2d 00 00 	mov    0x2d6e(%rip),%rax        # 3fd8 <_ITM_deregisterTMCloneTable@Base>
    126a:	48 85 c0             	test   %rax,%rax
    126d:	74 09                	je     1278 <deregister_tm_clones+0x28>
    126f:	ff e0                	jmp    *%rax
    1271:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1278:	c3                   	ret
    1279:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001280 <register_tm_clones>:
    1280:	48 8d 3d 89 2d 00 00 	lea    0x2d89(%rip),%rdi        # 4010 <stdin@GLIBC_2.2.5>
    1287:	48 8d 35 82 2d 00 00 	lea    0x2d82(%rip),%rsi        # 4010 <stdin@GLIBC_2.2.5>
    128e:	48 29 fe             	sub    %rdi,%rsi
    1291:	48 89 f0             	mov    %rsi,%rax
    1294:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1298:	48 c1 f8 03          	sar    $0x3,%rax
    129c:	48 01 c6             	add    %rax,%rsi
    129f:	48 d1 fe             	sar    %rsi
    12a2:	74 14                	je     12b8 <register_tm_clones+0x38>
    12a4:	48 8b 05 45 2d 00 00 	mov    0x2d45(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    12ab:	48 85 c0             	test   %rax,%rax
    12ae:	74 08                	je     12b8 <register_tm_clones+0x38>
    12b0:	ff e0                	jmp    *%rax
    12b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    12b8:	c3                   	ret
    12b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000012c0 <__do_global_dtors_aux>:
    12c0:	f3 0f 1e fa          	endbr64
    12c4:	80 3d 51 2d 00 00 00 	cmpb   $0x0,0x2d51(%rip)        # 401c <completed.0>
    12cb:	75 2b                	jne    12f8 <__do_global_dtors_aux+0x38>
    12cd:	55                   	push   %rbp
    12ce:	48 83 3d 22 2d 00 00 00 	cmpq   $0x0,0x2d22(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    12d6:	48 89 e5             	mov    %rsp,%rbp
    12d9:	74 0c                	je     12e7 <__do_global_dtors_aux+0x27>
    12db:	48 8b 3d 26 2d 00 00 	mov    0x2d26(%rip),%rdi        # 4008 <__dso_handle>
    12e2:	e8 c9 fd ff ff       	call   10b0 <__cxa_finalize@plt>
    12e7:	e8 64 ff ff ff       	call   1250 <deregister_tm_clones>
    12ec:	c6 05 29 2d 00 00 01 	movb   $0x1,0x2d29(%rip)        # 401c <completed.0>
    12f3:	5d                   	pop    %rbp
    12f4:	c3                   	ret
    12f5:	0f 1f 00             	nopl   (%rax)
    12f8:	c3                   	ret
    12f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001300 <frame_dummy>:
    1300:	f3 0f 1e fa          	endbr64
    1304:	e9 77 ff ff ff       	jmp    1280 <register_tm_clones>
    1309:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001310 <getnum>:
int getnum() {
    1310:	f3 0f 1e fa          	endbr64
    1314:	55                   	push   %rbp
    1315:	48 89 e5             	mov    %rsp,%rbp
    1318:	53                   	push   %rbx
    1319:	48 83 ec 28          	sub    $0x28,%rsp
    131d:	ff 15 c5 2c 00 00    	call   *0x2cc5(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
    read = getline(&buffer, &len, stdin);
    1323:	48 8b 15 e6 2c 00 00 	mov    0x2ce6(%rip),%rdx        # 4010 <stdin@GLIBC_2.2.5>
int getnum() {
    132a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1333:	48 89 45 e8          	mov    %rax,-0x18(%rbp)
    1337:	31 c0                	xor    %eax,%eax
    read = getline(&buffer, &len, stdin);
    1339:	48 8d 75 e0          	lea    -0x20(%rbp),%rsi
    133d:	48 8d 7d d8          	lea    -0x28(%rbp),%rdi
    char *buffer = NULL;
    1341:	48 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%rbp)
    long len = 0;
    1349:	48 c7 45 e0 00 00 00 00 	movq   $0x0,-0x20(%rbp)
    read = getline(&buffer, &len, stdin);
    1351:	e8 da fd ff ff       	call   1130 <getline@plt>
    1356:	89 c3                	mov    %eax,%ebx
    if (-1 != read)
    1358:	83 f8 ff             	cmp    $0xffffffff,%eax
    135b:	74 73                	je     13d0 <getnum+0xc0>
        puts(buffer);
    135d:	48 8b 7d d8          	mov    -0x28(%rbp),%rdi
    1361:	e8 6a fd ff ff       	call   10d0 <puts@plt>
    1366:	48 8b 4d e0          	mov    -0x20(%rbp),%rcx
    136a:	89 da                	mov    %ebx,%edx
    136c:	48 8d 35 a1 0c 00 00 	lea    0xca1(%rip),%rsi        # 2014 <_IO_stdin_used+0x14>
    1373:	31 c0                	xor    %eax,%eax
    1375:	bf 01 00 00 00       	mov    $0x1,%edi
    137a:	e8 91 fd ff ff       	call   1110 <__printf_chk@plt>
    long long num = strtol(buffer, NULL, 10); 
    137f:	48 8b 7d d8          	mov    -0x28(%rbp),%rdi
    1383:	ba 0a 00 00 00       	mov    $0xa,%edx
    1388:	31 f6                	xor    %esi,%esi
    138a:	e8 71 fd ff ff       	call   1100 <strtol@plt>
    138f:	48 8d 35 97 0c 00 00 	lea    0xc97(%rip),%rsi        # 202d <_IO_stdin_used+0x2d>
    1396:	bf 01 00 00 00       	mov    $0x1,%edi
    139b:	48 89 c2             	mov    %rax,%rdx
    139e:	48 89 c3             	mov    %rax,%rbx
    13a1:	31 c0                	xor    %eax,%eax
    13a3:	e8 68 fd ff ff       	call   1110 <__printf_chk@plt>
    free(buffer);
    13a8:	48 8b 7d d8          	mov    -0x28(%rbp),%rdi
    13ac:	e8 0f fd ff ff       	call   10c0 <free@plt>
    return num;
    13b1:	89 d8                	mov    %ebx,%eax
}
    13b3:	48 8b 55 e8          	mov    -0x18(%rbp),%rdx
    13b7:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
    13c0:	75 1c                	jne    13de <getnum+0xce>
    13c2:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    13c6:	c9                   	leave
    13c7:	c3                   	ret
    13c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    13d0:	48 8d 3d 2d 0c 00 00 	lea    0xc2d(%rip),%rdi        # 2004 <_IO_stdin_used+0x4>
    13d7:	e8 f4 fc ff ff       	call   10d0 <puts@plt>
    13dc:	eb 88                	jmp    1366 <getnum+0x56>
    13de:	e8 fd fc ff ff       	call   10e0 <__stack_chk_fail@plt>
    13e3:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    13ed:	0f 1f 00             	nopl   (%rax)

00000000000013f0 <atexit>:
    13f0:	f3 0f 1e fa          	endbr64
    13f4:	48 8b 15 0d 2c 00 00 	mov    0x2c0d(%rip),%rdx        # 4008 <__dso_handle>
    13fb:	31 f6                	xor    %esi,%esi
    13fd:	e9 1e fd ff ff       	jmp    1120 <__cxa_atexit@plt>
    1402:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    140c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000001410 <__stack_chk_fail_local>:
    1410:	f3 0f 1e fa          	endbr64
    1414:	50                   	push   %rax
    1415:	58                   	pop    %rax
    1416:	48 83 ec 08          	sub    $0x8,%rsp
    141a:	e8 c1 fc ff ff       	call   10e0 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000001420 <_fini>:
    1420:	f3 0f 1e fa          	endbr64
    1424:	48 83 ec 08          	sub    $0x8,%rsp
    1428:	48 83 c4 08          	add    $0x8,%rsp
    142c:	c3                   	ret
