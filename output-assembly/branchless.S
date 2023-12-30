
branchless:     file format elf64-x86-64


Disassembly of section .init:

0000000000001000 <_init>:
    1000:	f3 0f 1e fa          	endbr64
    1004:	48 83 ec 08          	sub    $0x8,%rsp
    1008:	48 8b 05 d9 2f 00 00 	mov    0x2fd9(%rip),%rax        # 3fe8 <__gmon_start__@Base>
    100f:	48 85 c0             	test   %rax,%rax
    1012:	74 02                	je     1016 <_init+0x16>
    1014:	ff d0                	call   *%rax
    1016:	48 83 c4 08          	add    $0x8,%rsp
    101a:	c3                   	ret

Disassembly of section .plt:

0000000000001020 <.plt>:
    1020:	ff 35 72 2f 00 00    	push   0x2f72(%rip)        # 3f98 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:	ff 25 74 2f 00 00    	jmp    *0x2f74(%rip)        # 3fa0 <_GLOBAL_OFFSET_TABLE_+0x10>
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

Disassembly of section .plt.got:

0000000000001090 <__cxa_finalize@plt>:
    1090:	f3 0f 1e fa          	endbr64
    1094:	ff 25 5e 2f 00 00    	jmp    *0x2f5e(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    109a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

00000000000010a0 <free@plt>:
    10a0:	f3 0f 1e fa          	endbr64
    10a4:	ff 25 fe 2e 00 00    	jmp    *0x2efe(%rip)        # 3fa8 <free@GLIBC_2.2.5>
    10aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010b0 <puts@plt>:
    10b0:	f3 0f 1e fa          	endbr64
    10b4:	ff 25 f6 2e 00 00    	jmp    *0x2ef6(%rip)        # 3fb0 <puts@GLIBC_2.2.5>
    10ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010c0 <__stack_chk_fail@plt>:
    10c0:	f3 0f 1e fa          	endbr64
    10c4:	ff 25 ee 2e 00 00    	jmp    *0x2eee(%rip)        # 3fb8 <__stack_chk_fail@GLIBC_2.4>
    10ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010d0 <strtol@plt>:
    10d0:	f3 0f 1e fa          	endbr64
    10d4:	ff 25 e6 2e 00 00    	jmp    *0x2ee6(%rip)        # 3fc0 <strtol@GLIBC_2.2.5>
    10da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010e0 <__printf_chk@plt>:
    10e0:	f3 0f 1e fa          	endbr64
    10e4:	ff 25 de 2e 00 00    	jmp    *0x2ede(%rip)        # 3fc8 <__printf_chk@GLIBC_2.3.4>
    10ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010f0 <getline@plt>:
    10f0:	f3 0f 1e fa          	endbr64
    10f4:	ff 25 d6 2e 00 00    	jmp    *0x2ed6(%rip)        # 3fd0 <getline@GLIBC_2.2.5>
    10fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000001100 <main>:

    return num;
}

int main(int argc, char *argv[])
{
    1100:	f3 0f 1e fa          	endbr64
    1104:	55                   	push   %rbp
    int num1 = getnum();
    1105:	31 c0                	xor    %eax,%eax
{
    1107:	53                   	push   %rbx
    1108:	48 83 ec 08          	sub    $0x8,%rsp
    int num1 = getnum();
    110c:	e8 4f 01 00 00       	call   1260 <getnum>
    1111:	89 c3                	mov    %eax,%ebx
    int num2 = getnum();
    1113:	31 c0                	xor    %eax,%eax
    1115:	e8 46 01 00 00       	call   1260 <getnum>
    111a:	89 c5                	mov    %eax,%ebp
    int num3 = getnum();
    111c:	31 c0                	xor    %eax,%eax
    111e:	e8 3d 01 00 00       	call   1260 <getnum>
    long c = (num1 > 1500);
    long m = (num2 > 1600) << 1;
    long z = (num3 > 1700) << 2;
    1123:	31 d2                	xor    %edx,%edx
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    1125:	bf 01 00 00 00       	mov    $0x1,%edi
    112a:	48 8d 35 09 0f 00 00 	lea    0xf09(%rip),%rsi        # 203a <_IO_stdin_used+0x3a>
    1131:	3d a4 06 00 00       	cmp    $0x6a4,%eax
    1136:	0f 9f c2             	setg   %dl
    long m = (num2 > 1600) << 1;
    1139:	31 c0                	xor    %eax,%eax
    long z = (num3 > 1700) << 2;
    113b:	48 c1 e2 02          	shl    $0x2,%rdx
    long m = (num2 > 1600) << 1;
    113f:	81 fd 40 06 00 00    	cmp    $0x640,%ebp
    1145:	0f 9f c0             	setg   %al
    1148:	48 01 c0             	add    %rax,%rax

    printf("result: %ld\n",  c | m | z);
    114b:	48 09 c2             	or     %rax,%rdx
    long c = (num1 > 1500);
    114e:	31 c0                	xor    %eax,%eax
    1150:	81 fb dc 05 00 00    	cmp    $0x5dc,%ebx
    1156:	0f 9f c0             	setg   %al
    printf("result: %ld\n",  c | m | z);
    1159:	48 09 c2             	or     %rax,%rdx
    115c:	31 c0                	xor    %eax,%eax
    115e:	e8 7d ff ff ff       	call   10e0 <__printf_chk@plt>

    return 0;
}
    1163:	48 83 c4 08          	add    $0x8,%rsp
    1167:	31 c0                	xor    %eax,%eax
    1169:	5b                   	pop    %rbx
    116a:	5d                   	pop    %rbp
    116b:	c3                   	ret
    116c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000001170 <_start>:
    1170:	f3 0f 1e fa          	endbr64
    1174:	31 ed                	xor    %ebp,%ebp
    1176:	49 89 d1             	mov    %rdx,%r9
    1179:	5e                   	pop    %rsi
    117a:	48 89 e2             	mov    %rsp,%rdx
    117d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1181:	50                   	push   %rax
    1182:	54                   	push   %rsp
    1183:	45 31 c0             	xor    %r8d,%r8d
    1186:	31 c9                	xor    %ecx,%ecx
    1188:	48 8d 3d 71 ff ff ff 	lea    -0x8f(%rip),%rdi        # 1100 <main>
    118f:	ff 15 43 2e 00 00    	call   *0x2e43(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1195:	f4                   	hlt
    1196:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000011a0 <deregister_tm_clones>:
    11a0:	48 8d 3d 69 2e 00 00 	lea    0x2e69(%rip),%rdi        # 4010 <stdin@GLIBC_2.2.5>
    11a7:	48 8d 05 62 2e 00 00 	lea    0x2e62(%rip),%rax        # 4010 <stdin@GLIBC_2.2.5>
    11ae:	48 39 f8             	cmp    %rdi,%rax
    11b1:	74 15                	je     11c8 <deregister_tm_clones+0x28>
    11b3:	48 8b 05 26 2e 00 00 	mov    0x2e26(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    11ba:	48 85 c0             	test   %rax,%rax
    11bd:	74 09                	je     11c8 <deregister_tm_clones+0x28>
    11bf:	ff e0                	jmp    *%rax
    11c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    11c8:	c3                   	ret
    11c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000011d0 <register_tm_clones>:
    11d0:	48 8d 3d 39 2e 00 00 	lea    0x2e39(%rip),%rdi        # 4010 <stdin@GLIBC_2.2.5>
    11d7:	48 8d 35 32 2e 00 00 	lea    0x2e32(%rip),%rsi        # 4010 <stdin@GLIBC_2.2.5>
    11de:	48 29 fe             	sub    %rdi,%rsi
    11e1:	48 89 f0             	mov    %rsi,%rax
    11e4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    11e8:	48 c1 f8 03          	sar    $0x3,%rax
    11ec:	48 01 c6             	add    %rax,%rsi
    11ef:	48 d1 fe             	sar    %rsi
    11f2:	74 14                	je     1208 <register_tm_clones+0x38>
    11f4:	48 8b 05 f5 2d 00 00 	mov    0x2df5(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    11fb:	48 85 c0             	test   %rax,%rax
    11fe:	74 08                	je     1208 <register_tm_clones+0x38>
    1200:	ff e0                	jmp    *%rax
    1202:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1208:	c3                   	ret
    1209:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001210 <__do_global_dtors_aux>:
    1210:	f3 0f 1e fa          	endbr64
    1214:	80 3d fd 2d 00 00 00 	cmpb   $0x0,0x2dfd(%rip)        # 4018 <completed.0>
    121b:	75 2b                	jne    1248 <__do_global_dtors_aux+0x38>
    121d:	55                   	push   %rbp
    121e:	48 83 3d d2 2d 00 00 00 	cmpq   $0x0,0x2dd2(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1226:	48 89 e5             	mov    %rsp,%rbp
    1229:	74 0c                	je     1237 <__do_global_dtors_aux+0x27>
    122b:	48 8b 3d d6 2d 00 00 	mov    0x2dd6(%rip),%rdi        # 4008 <__dso_handle>
    1232:	e8 59 fe ff ff       	call   1090 <__cxa_finalize@plt>
    1237:	e8 64 ff ff ff       	call   11a0 <deregister_tm_clones>
    123c:	c6 05 d5 2d 00 00 01 	movb   $0x1,0x2dd5(%rip)        # 4018 <completed.0>
    1243:	5d                   	pop    %rbp
    1244:	c3                   	ret
    1245:	0f 1f 00             	nopl   (%rax)
    1248:	c3                   	ret
    1249:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001250 <frame_dummy>:
    1250:	f3 0f 1e fa          	endbr64
    1254:	e9 77 ff ff ff       	jmp    11d0 <register_tm_clones>
    1259:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001260 <getnum>:
int getnum() {
    1260:	f3 0f 1e fa          	endbr64
    1264:	53                   	push   %rbx
    1265:	48 83 ec 20          	sub    $0x20,%rsp
    read = getline(&buffer, &len, stdin);
    1269:	48 8b 15 a0 2d 00 00 	mov    0x2da0(%rip),%rdx        # 4010 <stdin@GLIBC_2.2.5>
int getnum() {
    1270:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1279:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    127e:	31 c0                	xor    %eax,%eax
    read = getline(&buffer, &len, stdin);
    1280:	48 8d 74 24 10       	lea    0x10(%rsp),%rsi
    1285:	48 8d 7c 24 08       	lea    0x8(%rsp),%rdi
    char *buffer = NULL;
    128a:	48 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%rsp)
    long len = 0;
    1293:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
    read = getline(&buffer, &len, stdin);
    129c:	e8 4f fe ff ff       	call   10f0 <getline@plt>
    12a1:	89 c3                	mov    %eax,%ebx
    if (-1 != read)
    12a3:	83 f8 ff             	cmp    $0xffffffff,%eax
    12a6:	74 78                	je     1320 <getnum+0xc0>
        puts(buffer);
    12a8:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    12ad:	e8 fe fd ff ff       	call   10b0 <puts@plt>
    12b2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    12b7:	89 da                	mov    %ebx,%edx
    12b9:	48 8d 35 54 0d 00 00 	lea    0xd54(%rip),%rsi        # 2014 <_IO_stdin_used+0x14>
    12c0:	31 c0                	xor    %eax,%eax
    12c2:	bf 01 00 00 00       	mov    $0x1,%edi
    12c7:	e8 14 fe ff ff       	call   10e0 <__printf_chk@plt>
    long long num = strtol(buffer, NULL, 10); 
    12cc:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    12d1:	ba 0a 00 00 00       	mov    $0xa,%edx
    12d6:	31 f6                	xor    %esi,%esi
    12d8:	e8 f3 fd ff ff       	call   10d0 <strtol@plt>
    12dd:	48 8d 35 49 0d 00 00 	lea    0xd49(%rip),%rsi        # 202d <_IO_stdin_used+0x2d>
    12e4:	bf 01 00 00 00       	mov    $0x1,%edi
    12e9:	48 89 c2             	mov    %rax,%rdx
    12ec:	48 89 c3             	mov    %rax,%rbx
    12ef:	31 c0                	xor    %eax,%eax
    12f1:	e8 ea fd ff ff       	call   10e0 <__printf_chk@plt>
    free(buffer);
    12f6:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    12fb:	e8 a0 fd ff ff       	call   10a0 <free@plt>
    return num;
    1300:	89 d8                	mov    %ebx,%eax
}
    1302:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    1307:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
    1310:	75 1c                	jne    132e <getnum+0xce>
    1312:	48 83 c4 20          	add    $0x20,%rsp
    1316:	5b                   	pop    %rbx
    1317:	c3                   	ret
    1318:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    1320:	48 8d 3d dd 0c 00 00 	lea    0xcdd(%rip),%rdi        # 2004 <_IO_stdin_used+0x4>
    1327:	e8 84 fd ff ff       	call   10b0 <puts@plt>
    132c:	eb 84                	jmp    12b2 <getnum+0x52>
    132e:	e8 8d fd ff ff       	call   10c0 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000001334 <_fini>:
    1334:	f3 0f 1e fa          	endbr64
    1338:	48 83 ec 08          	sub    $0x8,%rsp
    133c:	48 83 c4 08          	add    $0x8,%rsp
    1340:	c3                   	ret
