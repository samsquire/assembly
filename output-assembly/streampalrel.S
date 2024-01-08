
streampalrel:     file format elf64-x86-64


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

00000000000010a0 <__stack_chk_fail@plt>:
    10a0:	f3 0f 1e fa          	endbr64
    10a4:	ff 25 fe 2e 00 00    	jmp    *0x2efe(%rip)        # 3fa8 <__stack_chk_fail@GLIBC_2.4>
    10aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010b0 <nanosleep@plt>:
    10b0:	f3 0f 1e fa          	endbr64
    10b4:	ff 25 f6 2e 00 00    	jmp    *0x2ef6(%rip)        # 3fb0 <nanosleep@GLIBC_2.2.5>
    10ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010c0 <calloc@plt>:
    10c0:	f3 0f 1e fa          	endbr64
    10c4:	ff 25 ee 2e 00 00    	jmp    *0x2eee(%rip)        # 3fb8 <calloc@GLIBC_2.2.5>
    10ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010d0 <__printf_chk@plt>:
    10d0:	f3 0f 1e fa          	endbr64
    10d4:	ff 25 e6 2e 00 00    	jmp    *0x2ee6(%rip)        # 3fc0 <__printf_chk@GLIBC_2.3.4>
    10da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010e0 <pthread_create@plt>:
    10e0:	f3 0f 1e fa          	endbr64
    10e4:	ff 25 de 2e 00 00    	jmp    *0x2ede(%rip)        # 3fc8 <pthread_create@GLIBC_2.34>
    10ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010f0 <pthread_join@plt>:
    10f0:	f3 0f 1e fa          	endbr64
    10f4:	ff 25 d6 2e 00 00    	jmp    *0x2ed6(%rip)        # 3fd0 <pthread_join@GLIBC_2.34>
    10fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000001100 <main>:
  }
  
  return (void*)log->result;
}

int main() {
    1100:	f3 0f 1e fa          	endbr64
    1104:	41 57                	push   %r15
  int thread_count = 12; 
  int total_threads = thread_count;
  int data_size = 1000000;

  struct Log * logs = calloc(thread_count, sizeof(struct Log));
    1106:	be 40 00 00 00       	mov    $0x40,%esi
    110b:	bf 0c 00 00 00       	mov    $0xc,%edi
int main() {
    1110:	41 56                	push   %r14
    1112:	41 55                	push   %r13
    1114:	41 54                	push   %r12
  struct Log ** logptrs = calloc(thread_count, sizeof(struct Log*));
    1116:	45 31 e4             	xor    %r12d,%r12d
int main() {
    1119:	55                   	push   %rbp
    111a:	53                   	push   %rbx
    111b:	48 83 ec 48          	sub    $0x48,%rsp
    111f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1128:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    112d:	31 c0                	xor    %eax,%eax
  struct Log * logs = calloc(thread_count, sizeof(struct Log));
    112f:	e8 8c ff ff ff       	call   10c0 <calloc@plt>
  struct Log ** logptrs = calloc(thread_count, sizeof(struct Log*));
    1134:	be 08 00 00 00       	mov    $0x8,%esi
    1139:	bf 0c 00 00 00       	mov    $0xc,%edi
  struct Log * logs = calloc(thread_count, sizeof(struct Log));
    113e:	48 89 c3             	mov    %rax,%rbx
  struct Log ** logptrs = calloc(thread_count, sizeof(struct Log*));
    1141:	e8 7a ff ff ff       	call   10c0 <calloc@plt>
    1146:	48 89 dd             	mov    %rbx,%rbp
    1149:	49 89 c5             	mov    %rax,%r13
  for (int x = 0 ; x < thread_count ; x++) {
    114c:	0f 1f 40 00          	nopl   0x0(%rax)
    logs[x].running = 1;
    logs[x].thread_index = x;
    1150:	44 89 65 00          	mov    %r12d,0x0(%rbp)
    logs[x].data_size = data_size;
    logs[x].thread_count = thread_count;
    logs[x].data = calloc(data_size, sizeof(int));
    1154:	be 04 00 00 00       	mov    $0x4,%esi
    1159:	bf 40 42 0f 00       	mov    $0xf4240,%edi
    logs[x].running = 1;
    115e:	c7 45 28 01 00 00 00 	movl   $0x1,0x28(%rbp)
    logs[x].data_size = data_size;
    1165:	c7 45 18 40 42 0f 00 	movl   $0xf4240,0x18(%rbp)
    logs[x].thread_count = thread_count;
    116c:	c7 45 04 0c 00 00 00 	movl   $0xc,0x4(%rbp)
    logs[x].data = calloc(data_size, sizeof(int));
    1173:	e8 48 ff ff ff       	call   10c0 <calloc@plt>
    logs[x].data[0] = 1;
    logs[x].mine = 1;
    logs[x].others = logptrs;
    logptrs[x] = &logs[x];
    1178:	4b 89 6c e5 00       	mov    %rbp,0x0(%r13,%r12,8)
  for (int x = 0 ; x < thread_count ; x++) {
    117d:	49 83 c4 01          	add    $0x1,%r12
    1181:	48 83 c5 40          	add    $0x40,%rbp
    logs[x].data = calloc(data_size, sizeof(int));
    1185:	48 89 45 d0          	mov    %rax,-0x30(%rbp)
    logs[x].mine = 1;
    1189:	48 c7 45 f8 01 00 00 00 	movq   $0x1,-0x8(%rbp)
    logs[x].others = logptrs;
    1191:	4c 89 6d c8          	mov    %r13,-0x38(%rbp)
    logs[x].data[0] = 1;
    1195:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  for (int x = 0 ; x < thread_count ; x++) {
    119b:	49 83 fc 0c          	cmp    $0xc,%r12
    119f:	75 af                	jne    1150 <main+0x50>
  }
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    11a1:	be 08 00 00 00       	mov    $0x8,%esi
    11a6:	bf 0c 00 00 00       	mov    $0xc,%edi
  pthread_attr_t      *attr = calloc(total_threads, sizeof(pthread_attr_t));
    11ab:	49 89 df             	mov    %rbx,%r15
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    11ae:	e8 0d ff ff ff       	call   10c0 <calloc@plt>
  pthread_attr_t      *attr = calloc(total_threads, sizeof(pthread_attr_t));
    11b3:	be 38 00 00 00       	mov    $0x38,%esi
    11b8:	bf 0c 00 00 00       	mov    $0xc,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    11bd:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *attr = calloc(total_threads, sizeof(pthread_attr_t));
    11c0:	e8 fb fe ff ff       	call   10c0 <calloc@plt>

  for (int x = 0 ; x < thread_count ; x++) {
    11c5:	4c 8d 75 60          	lea    0x60(%rbp),%r14
  pthread_attr_t      *attr = calloc(total_threads, sizeof(pthread_attr_t));
    11c9:	49 89 ec             	mov    %rbp,%r12
    11cc:	49 89 c5             	mov    %rax,%r13
    11cf:	90                   	nop
    pthread_create(&thread[x], &attr[x], &stream, &logs[x]);
    11d0:	4c 89 f9             	mov    %r15,%rcx
    11d3:	4c 89 ee             	mov    %r13,%rsi
    11d6:	4c 89 e7             	mov    %r12,%rdi
  for (int x = 0 ; x < thread_count ; x++) {
    11d9:	49 83 c4 08          	add    $0x8,%r12
    pthread_create(&thread[x], &attr[x], &stream, &logs[x]);
    11dd:	48 8d 15 6c 02 00 00 	lea    0x26c(%rip),%rdx        # 1450 <stream>
  for (int x = 0 ; x < thread_count ; x++) {
    11e4:	49 83 c5 38          	add    $0x38,%r13
    11e8:	49 83 c7 40          	add    $0x40,%r15
    pthread_create(&thread[x], &attr[x], &stream, &logs[x]);
    11ec:	e8 ef fe ff ff       	call   10e0 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    11f1:	4d 39 f4             	cmp    %r14,%r12
    11f4:	75 da                	jne    11d0 <main+0xd0>
  }

  
  struct timespec rem2;
  struct timespec preempt = {
    11f6:	66 0f 6f 05 42 0e 00 00 	movdqa 0xe42(%rip),%xmm0        # 2040 <_IO_stdin_used+0x40>
    5,
    0 };
  nanosleep(&preempt , &rem2);
    11fe:	48 8d 74 24 10       	lea    0x10(%rsp),%rsi
    1203:	48 8d 7c 24 20       	lea    0x20(%rsp),%rdi
  struct timespec preempt = {
    1208:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
  nanosleep(&preempt , &rem2);
    120d:	e8 9e fe ff ff       	call   10b0 <nanosleep@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    logs[x].running = 0;
    1212:	c7 43 28 00 00 00 00 	movl   $0x0,0x28(%rbx)
    1219:	c7 43 68 00 00 00 00 	movl   $0x0,0x68(%rbx)
    1220:	c7 83 a8 00 00 00 00 00 00 00 	movl   $0x0,0xa8(%rbx)
    122a:	c7 83 e8 00 00 00 00 00 00 00 	movl   $0x0,0xe8(%rbx)
    1234:	c7 83 28 01 00 00 00 00 00 00 	movl   $0x0,0x128(%rbx)
    123e:	c7 83 68 01 00 00 00 00 00 00 	movl   $0x0,0x168(%rbx)
    1248:	c7 83 a8 01 00 00 00 00 00 00 	movl   $0x0,0x1a8(%rbx)
    1252:	c7 83 e8 01 00 00 00 00 00 00 	movl   $0x0,0x1e8(%rbx)
    125c:	c7 83 28 02 00 00 00 00 00 00 	movl   $0x0,0x228(%rbx)
    1266:	c7 83 68 02 00 00 00 00 00 00 	movl   $0x0,0x268(%rbx)
    1270:	c7 83 a8 02 00 00 00 00 00 00 	movl   $0x0,0x2a8(%rbx)
    127a:	c7 83 e8 02 00 00 00 00 00 00 	movl   $0x0,0x2e8(%rbx)
  }
  asm volatile ("sfence":::"memory");
    1284:	0f ae f8             	sfence

  for (int x = 0 ; x < thread_count ; x++) {
    1287:	4c 8d 64 24 08       	lea    0x8(%rsp),%r12
    128c:	0f 1f 40 00          	nopl   0x0(%rax)
    void * result; 
    pthread_join(thread[x], &result);
    1290:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    1294:	4c 89 e6             	mov    %r12,%rsi
  for (int x = 0 ; x < thread_count ; x++) {
    1297:	48 83 c5 08          	add    $0x8,%rbp
    pthread_join(thread[x], &result);
    129b:	e8 50 fe ff ff       	call   10f0 <pthread_join@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    12a0:	4c 39 f5             	cmp    %r14,%rbp
    12a3:	75 eb                	jne    1290 <main+0x190>
    12a5:	4c 8d 63 04          	lea    0x4(%rbx),%r12
  }
  long mine = 0;
    12a9:	45 31 ed             	xor    %r13d,%r13d
    12ac:	48 81 c3 04 03 00 00 	add    $0x304,%rbx
    12b3:	48 8d 2d 61 0d 00 00 	lea    0xd61(%rip),%rbp        # 201b <_IO_stdin_used+0x1b>
    12ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  for (int x = 0 ; x < thread_count ; x++) {
    long start = 0;
    for (int y  = 0 ; y < logs[x].thread_count ; y++) {
    12c0:	49 63 04 24          	movslq (%r12),%rax
    long start = 0;
    12c4:	31 ff                	xor    %edi,%edi
    for (int y  = 0 ; y < logs[x].thread_count ; y++) {
    12c6:	85 c0                	test   %eax,%eax
    12c8:	7e 36                	jle    1300 <main+0x200>
    12ca:	49 8b 4c 24 04       	mov    0x4(%r12),%rcx
      start += logs[x].others[y]->data[logs[x].others[y]->index % logs[x].data_size];
    12cf:	4d 63 44 24 14       	movslq 0x14(%r12),%r8
    long start = 0;
    12d4:	31 ff                	xor    %edi,%edi
    12d6:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    12da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      start += logs[x].others[y]->data[logs[x].others[y]->index % logs[x].data_size];
    12e0:	48 8b 31             	mov    (%rcx),%rsi
    for (int y  = 0 ; y < logs[x].thread_count ; y++) {
    12e3:	48 83 c1 08          	add    $0x8,%rcx
      start += logs[x].others[y]->data[logs[x].others[y]->index % logs[x].data_size];
    12e7:	48 8b 46 20          	mov    0x20(%rsi),%rax
    12eb:	48 99                	cqto
    12ed:	49 f7 f8             	idiv   %r8
    12f0:	48 8b 46 10          	mov    0x10(%rsi),%rax
    12f4:	48 63 04 90          	movslq (%rax,%rdx,4),%rax
    12f8:	48 01 c7             	add    %rax,%rdi
    for (int y  = 0 ; y < logs[x].thread_count ; y++) {
    12fb:	4c 39 c9             	cmp    %r9,%rcx
    12fe:	75 e0                	jne    12e0 <main+0x1e0>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    1300:	48 89 fa             	mov    %rdi,%rdx
    1303:	48 89 ee             	mov    %rbp,%rsi
    1306:	bf 01 00 00 00       	mov    $0x1,%edi
    130b:	31 c0                	xor    %eax,%eax
    130d:	e8 be fd ff ff       	call   10d0 <__printf_chk@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    1312:	49 83 c4 40          	add    $0x40,%r12
    }
    printf("start %ld result\n", start);
    mine += logs[x].mine;
    1316:	4d 03 6c 24 f4       	add    -0xc(%r12),%r13
  for (int x = 0 ; x < thread_count ; x++) {
    131b:	4c 39 e3             	cmp    %r12,%rbx
    131e:	75 a0                	jne    12c0 <main+0x1c0>
    1320:	31 c0                	xor    %eax,%eax
    1322:	4c 89 ea             	mov    %r13,%rdx
    1325:	bf 01 00 00 00       	mov    $0x1,%edi
    132a:	48 8d 35 fc 0c 00 00 	lea    0xcfc(%rip),%rsi        # 202d <_IO_stdin_used+0x2d>
    1331:	e8 9a fd ff ff       	call   10d0 <__printf_chk@plt>
  }
  printf("mine %ld result\n", mine);
}
    1336:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    133b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1344:	75 11                	jne    1357 <main+0x257>
    1346:	48 83 c4 48          	add    $0x48,%rsp
    134a:	31 c0                	xor    %eax,%eax
    134c:	5b                   	pop    %rbx
    134d:	5d                   	pop    %rbp
    134e:	41 5c                	pop    %r12
    1350:	41 5d                	pop    %r13
    1352:	41 5e                	pop    %r14
    1354:	41 5f                	pop    %r15
    1356:	c3                   	ret
    1357:	e8 44 fd ff ff       	call   10a0 <__stack_chk_fail@plt>
    135c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000001360 <_start>:
    1360:	f3 0f 1e fa          	endbr64
    1364:	31 ed                	xor    %ebp,%ebp
    1366:	49 89 d1             	mov    %rdx,%r9
    1369:	5e                   	pop    %rsi
    136a:	48 89 e2             	mov    %rsp,%rdx
    136d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1371:	50                   	push   %rax
    1372:	54                   	push   %rsp
    1373:	45 31 c0             	xor    %r8d,%r8d
    1376:	31 c9                	xor    %ecx,%ecx
    1378:	48 8d 3d 81 fd ff ff 	lea    -0x27f(%rip),%rdi        # 1100 <main>
    137f:	ff 15 53 2c 00 00    	call   *0x2c53(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1385:	f4                   	hlt
    1386:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001390 <deregister_tm_clones>:
    1390:	48 8d 3d 79 2c 00 00 	lea    0x2c79(%rip),%rdi        # 4010 <__TMC_END__>
    1397:	48 8d 05 72 2c 00 00 	lea    0x2c72(%rip),%rax        # 4010 <__TMC_END__>
    139e:	48 39 f8             	cmp    %rdi,%rax
    13a1:	74 15                	je     13b8 <deregister_tm_clones+0x28>
    13a3:	48 8b 05 36 2c 00 00 	mov    0x2c36(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    13aa:	48 85 c0             	test   %rax,%rax
    13ad:	74 09                	je     13b8 <deregister_tm_clones+0x28>
    13af:	ff e0                	jmp    *%rax
    13b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    13b8:	c3                   	ret
    13b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000013c0 <register_tm_clones>:
    13c0:	48 8d 3d 49 2c 00 00 	lea    0x2c49(%rip),%rdi        # 4010 <__TMC_END__>
    13c7:	48 8d 35 42 2c 00 00 	lea    0x2c42(%rip),%rsi        # 4010 <__TMC_END__>
    13ce:	48 29 fe             	sub    %rdi,%rsi
    13d1:	48 89 f0             	mov    %rsi,%rax
    13d4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    13d8:	48 c1 f8 03          	sar    $0x3,%rax
    13dc:	48 01 c6             	add    %rax,%rsi
    13df:	48 d1 fe             	sar    %rsi
    13e2:	74 14                	je     13f8 <register_tm_clones+0x38>
    13e4:	48 8b 05 05 2c 00 00 	mov    0x2c05(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    13eb:	48 85 c0             	test   %rax,%rax
    13ee:	74 08                	je     13f8 <register_tm_clones+0x38>
    13f0:	ff e0                	jmp    *%rax
    13f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    13f8:	c3                   	ret
    13f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001400 <__do_global_dtors_aux>:
    1400:	f3 0f 1e fa          	endbr64
    1404:	80 3d 05 2c 00 00 00 	cmpb   $0x0,0x2c05(%rip)        # 4010 <__TMC_END__>
    140b:	75 2b                	jne    1438 <__do_global_dtors_aux+0x38>
    140d:	55                   	push   %rbp
    140e:	48 83 3d e2 2b 00 00 00 	cmpq   $0x0,0x2be2(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1416:	48 89 e5             	mov    %rsp,%rbp
    1419:	74 0c                	je     1427 <__do_global_dtors_aux+0x27>
    141b:	48 8b 3d e6 2b 00 00 	mov    0x2be6(%rip),%rdi        # 4008 <__dso_handle>
    1422:	e8 69 fc ff ff       	call   1090 <__cxa_finalize@plt>
    1427:	e8 64 ff ff ff       	call   1390 <deregister_tm_clones>
    142c:	c6 05 dd 2b 00 00 01 	movb   $0x1,0x2bdd(%rip)        # 4010 <__TMC_END__>
    1433:	5d                   	pop    %rbp
    1434:	c3                   	ret
    1435:	0f 1f 00             	nopl   (%rax)
    1438:	c3                   	ret
    1439:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001440 <frame_dummy>:
    1440:	f3 0f 1e fa          	endbr64
    1444:	e9 77 ff ff ff       	jmp    13c0 <register_tm_clones>
    1449:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001450 <stream>:
void* stream(void * arg) {
    1450:	f3 0f 1e fa          	endbr64
    1454:	41 54                	push   %r12
    1456:	48 8d 35 a7 0b 00 00 	lea    0xba7(%rip),%rsi        # 2004 <_IO_stdin_used+0x4>
    145d:	31 c0                	xor    %eax,%eax
    145f:	55                   	push   %rbp
    1460:	53                   	push   %rbx
    1461:	8b 17                	mov    (%rdi),%edx
    1463:	48 89 fb             	mov    %rdi,%rbx
    1466:	bf 01 00 00 00       	mov    $0x1,%edi
    146b:	e8 60 fc ff ff       	call   10d0 <__printf_chk@plt>
  while (log->running) {
    1470:	8b 4b 28             	mov    0x28(%rbx),%ecx
    1473:	85 c9                	test   %ecx,%ecx
    1475:	0f 84 c4 00 00 00    	je     153f <stream+0xef>
    for (int x = 0 ; x < log->data_size; x++) {
    147b:	44 8b 43 18          	mov    0x18(%rbx),%r8d
    147f:	90                   	nop
    for (int x  = 0 ; x < log->thread_count ; x++) {
    1480:	48 63 43 04          	movslq 0x4(%rbx),%rax
    long start = 0;
    1484:	45 31 db             	xor    %r11d,%r11d
    for (int x  = 0 ; x < log->thread_count ; x++) {
    1487:	85 c0                	test   %eax,%eax
    1489:	7e 35                	jle    14c0 <stream+0x70>
    148b:	48 8b 73 08          	mov    0x8(%rbx),%rsi
      start += log->others[x]->data[log->others[x]->index % log->data_size];
    148f:	49 63 c8             	movslq %r8d,%rcx
    long start = 0;
    1492:	45 31 db             	xor    %r11d,%r11d
    1495:	4c 8d 0c c6          	lea    (%rsi,%rax,8),%r9
    1499:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      start += log->others[x]->data[log->others[x]->index % log->data_size];
    14a0:	48 8b 3e             	mov    (%rsi),%rdi
    for (int x  = 0 ; x < log->thread_count ; x++) {
    14a3:	48 83 c6 08          	add    $0x8,%rsi
      start += log->others[x]->data[log->others[x]->index % log->data_size];
    14a7:	48 8b 47 20          	mov    0x20(%rdi),%rax
    14ab:	48 99                	cqto
    14ad:	48 f7 f9             	idiv   %rcx
    14b0:	48 8b 47 10          	mov    0x10(%rdi),%rax
    14b4:	48 63 04 90          	movslq (%rax,%rdx,4),%rax
    14b8:	49 01 c3             	add    %rax,%r11
    for (int x  = 0 ; x < log->thread_count ; x++) {
    14bb:	49 39 f1             	cmp    %rsi,%r9
    14be:	75 e0                	jne    14a0 <stream+0x50>
    for (int x = 0 ; x < log->data_size; x++) {
    14c0:	45 85 c0             	test   %r8d,%r8d
    14c3:	0f 8e 87 00 00 00    	jle    1550 <stream+0x100>
    14c9:	4c 8b 63 20          	mov    0x20(%rbx),%r12
      log->data[(log->index + 1) % log->data_size] = log->data[log->index % log->data_size] + 1;    
    14cd:	4c 8b 53 10          	mov    0x10(%rbx),%r10
    for (int x = 0 ; x < log->data_size; x++) {
    14d1:	45 31 c9             	xor    %r9d,%r9d
    14d4:	49 63 c8             	movslq %r8d,%rcx
    14d7:	48 8b 6b 38          	mov    0x38(%rbx),%rbp
      log->data[(log->index + 1) % log->data_size] = log->data[log->index % log->data_size] + 1;    
    14db:	4c 89 e6             	mov    %r12,%rsi
    14de:	66 90                	xchg   %ax,%ax
    14e0:	48 89 f0             	mov    %rsi,%rax
    14e3:	48 89 f7             	mov    %rsi,%rdi
    14e6:	48 83 c6 01          	add    $0x1,%rsi
    for (int x = 0 ; x < log->data_size; x++) {
    14ea:	41 83 c1 01          	add    $0x1,%r9d
      log->data[(log->index + 1) % log->data_size] = log->data[log->index % log->data_size] + 1;    
    14ee:	48 99                	cqto
    14f0:	48 f7 f9             	idiv   %rcx
    14f3:	48 89 f0             	mov    %rsi,%rax
    14f6:	45 8b 04 92          	mov    (%r10,%rdx,4),%r8d
    14fa:	48 99                	cqto
    14fc:	48 f7 f9             	idiv   %rcx
    14ff:	41 83 c0 01          	add    $0x1,%r8d
      log->result = start + log->data[log->index % log->data_size];
    1503:	48 89 f8             	mov    %rdi,%rax
      log->data[(log->index + 1) % log->data_size] = log->data[log->index % log->data_size] + 1;    
    1506:	45 89 04 92          	mov    %r8d,(%r10,%rdx,4)
      log->result = start + log->data[log->index % log->data_size];
    150a:	48 63 4b 18          	movslq 0x18(%rbx),%rcx
    150e:	48 99                	cqto
    1510:	48 f7 f9             	idiv   %rcx
    1513:	49 89 c8             	mov    %rcx,%r8
    1516:	49 63 04 92          	movslq (%r10,%rdx,4),%rax
    for (int x = 0 ; x < log->data_size; x++) {
    151a:	44 39 c9             	cmp    %r9d,%ecx
    151d:	7f c1                	jg     14e0 <stream+0x90>
      log->result = start + log->data[log->index % log->data_size];
    151f:	4c 01 d8             	add    %r11,%rax
      log->mine++;
    1522:	4c 29 e5             	sub    %r12,%rbp
    1525:	48 89 73 20          	mov    %rsi,0x20(%rbx)
      log->result = start + log->data[log->index % log->data_size];
    1529:	48 89 43 30          	mov    %rax,0x30(%rbx)
  while (log->running) {
    152d:	8b 43 28             	mov    0x28(%rbx),%eax
      log->mine++;
    1530:	48 01 f5             	add    %rsi,%rbp
    1533:	48 89 6b 38          	mov    %rbp,0x38(%rbx)
  while (log->running) {
    1537:	85 c0                	test   %eax,%eax
    1539:	0f 85 41 ff ff ff    	jne    1480 <stream+0x30>
  return (void*)log->result;
    153f:	48 8b 43 30          	mov    0x30(%rbx),%rax
}
    1543:	5b                   	pop    %rbx
    1544:	5d                   	pop    %rbp
    1545:	41 5c                	pop    %r12
    1547:	c3                   	ret
    1548:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  while (log->running) {
    1550:	8b 53 28             	mov    0x28(%rbx),%edx
    1553:	85 d2                	test   %edx,%edx
    1555:	74 e8                	je     153f <stream+0xef>
    1557:	eb fe                	jmp    1557 <stream+0x107>

Disassembly of section .fini:

000000000000155c <_fini>:
    155c:	f3 0f 1e fa          	endbr64
    1560:	48 83 ec 08          	sub    $0x8,%rsp
    1564:	48 83 c4 08          	add    $0x8,%rsp
    1568:	c3                   	ret
