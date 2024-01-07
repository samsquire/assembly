
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
  
  return log->result;
}

int main() {
    1100:	f3 0f 1e fa          	endbr64
    1104:	41 57                	push   %r15
  int thread_count = 12; 
  int total_threads = thread_count;
  int data_size = 1000000;

  struct Log * logs = calloc(thread_count, sizeof(struct Log));
    1106:	be 38 00 00 00       	mov    $0x38,%esi
    110b:	bf 0c 00 00 00       	mov    $0xc,%edi
int main() {
    1110:	41 56                	push   %r14
    1112:	41 55                	push   %r13
    1114:	41 54                	push   %r12
    1116:	55                   	push   %rbp
  struct Log ** logptrs = calloc(thread_count, sizeof(struct Log*));
    1117:	31 ed                	xor    %ebp,%ebp
int main() {
    1119:	53                   	push   %rbx
    111a:	48 83 ec 48          	sub    $0x48,%rsp
    111e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1127:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    112c:	31 c0                	xor    %eax,%eax
  struct Log * logs = calloc(thread_count, sizeof(struct Log));
    112e:	e8 8d ff ff ff       	call   10c0 <calloc@plt>
  struct Log ** logptrs = calloc(thread_count, sizeof(struct Log*));
    1133:	be 08 00 00 00       	mov    $0x8,%esi
    1138:	bf 0c 00 00 00       	mov    $0xc,%edi
  struct Log * logs = calloc(thread_count, sizeof(struct Log));
    113d:	49 89 c5             	mov    %rax,%r13
  struct Log ** logptrs = calloc(thread_count, sizeof(struct Log*));
    1140:	e8 7b ff ff ff       	call   10c0 <calloc@plt>
    1145:	4d 89 ec             	mov    %r13,%r12
    1148:	4c 89 eb             	mov    %r13,%rbx
    114b:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < thread_count ; x++) {
    114e:	66 90                	xchg   %ax,%ax
    logs[x].running = 1;
    logs[x].thread_index = x;
    1150:	89 2b                	mov    %ebp,(%rbx)
    logs[x].data_size = data_size;
    logs[x].thread_count = thread_count;
    logs[x].data = calloc(data_size, sizeof(int));
    1152:	be 04 00 00 00       	mov    $0x4,%esi
    1157:	bf 40 42 0f 00       	mov    $0xf4240,%edi
    logs[x].running = 1;
    115c:	c7 43 28 01 00 00 00 	movl   $0x1,0x28(%rbx)
    logs[x].data_size = data_size;
    1163:	c7 43 18 40 42 0f 00 	movl   $0xf4240,0x18(%rbx)
    logs[x].thread_count = thread_count;
    116a:	c7 43 04 0c 00 00 00 	movl   $0xc,0x4(%rbx)
    logs[x].data = calloc(data_size, sizeof(int));
    1171:	e8 4a ff ff ff       	call   10c0 <calloc@plt>
    logs[x].data[0] = 1;
    logs[x].others = logptrs;
    logptrs[x] = &logs[x];
    1176:	49 89 1c ee          	mov    %rbx,(%r14,%rbp,8)
  for (int x = 0 ; x < thread_count ; x++) {
    117a:	48 83 c5 01          	add    $0x1,%rbp
    117e:	48 83 c3 38          	add    $0x38,%rbx
    logs[x].data = calloc(data_size, sizeof(int));
    1182:	48 89 43 d8          	mov    %rax,-0x28(%rbx)
    logs[x].others = logptrs;
    1186:	4c 89 73 d0          	mov    %r14,-0x30(%rbx)
    logs[x].data[0] = 1;
    118a:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  for (int x = 0 ; x < thread_count ; x++) {
    1190:	48 83 fd 0c          	cmp    $0xc,%rbp
    1194:	75 ba                	jne    1150 <main+0x50>
  }
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    1196:	be 08 00 00 00       	mov    $0x8,%esi
    119b:	bf 0c 00 00 00       	mov    $0xc,%edi
    11a0:	e8 1b ff ff ff       	call   10c0 <calloc@plt>
  pthread_attr_t      *attr = calloc(total_threads, sizeof(pthread_attr_t));
    11a5:	be 38 00 00 00       	mov    $0x38,%esi
    11aa:	bf 0c 00 00 00       	mov    $0xc,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    11af:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *attr = calloc(total_threads, sizeof(pthread_attr_t));
    11b2:	e8 09 ff ff ff       	call   10c0 <calloc@plt>

  for (int x = 0 ; x < thread_count ; x++) {
    11b7:	4c 8d 73 60          	lea    0x60(%rbx),%r14
  pthread_attr_t      *attr = calloc(total_threads, sizeof(pthread_attr_t));
    11bb:	48 89 dd             	mov    %rbx,%rbp
    11be:	49 89 c7             	mov    %rax,%r15
    11c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    pthread_create(&thread[x], &attr[x], &stream, &logs[x]);
    11c8:	4c 89 e1             	mov    %r12,%rcx
    11cb:	4c 89 fe             	mov    %r15,%rsi
    11ce:	48 89 ef             	mov    %rbp,%rdi
  for (int x = 0 ; x < thread_count ; x++) {
    11d1:	48 83 c5 08          	add    $0x8,%rbp
    pthread_create(&thread[x], &attr[x], &stream, &logs[x]);
    11d5:	48 8d 15 04 02 00 00 	lea    0x204(%rip),%rdx        # 13e0 <stream>
  for (int x = 0 ; x < thread_count ; x++) {
    11dc:	49 83 c7 38          	add    $0x38,%r15
    11e0:	49 83 c4 38          	add    $0x38,%r12
    pthread_create(&thread[x], &attr[x], &stream, &logs[x]);
    11e4:	e8 f7 fe ff ff       	call   10e0 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    11e9:	4c 39 f5             	cmp    %r14,%rbp
    11ec:	75 da                	jne    11c8 <main+0xc8>
  }

  
  struct timespec rem2;
  struct timespec preempt = {
    11ee:	66 0f 6f 05 3a 0e 00 00 	movdqa 0xe3a(%rip),%xmm0        # 2030 <_IO_stdin_used+0x30>
    5,
    0 };
  nanosleep(&preempt , &rem2);
    11f6:	48 8d 74 24 10       	lea    0x10(%rsp),%rsi
    11fb:	48 8d 7c 24 20       	lea    0x20(%rsp),%rdi
  struct timespec preempt = {
    1200:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
  nanosleep(&preempt , &rem2);
    1205:	e8 a6 fe ff ff       	call   10b0 <nanosleep@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    logs[x].running = 0;
    120a:	41 c7 45 28 00 00 00 00 	movl   $0x0,0x28(%r13)
    1212:	41 c7 45 60 00 00 00 00 	movl   $0x0,0x60(%r13)
    121a:	41 c7 85 98 00 00 00 00 00 00 00 	movl   $0x0,0x98(%r13)
    1225:	41 c7 85 d0 00 00 00 00 00 00 00 	movl   $0x0,0xd0(%r13)
    1230:	41 c7 85 08 01 00 00 00 00 00 00 	movl   $0x0,0x108(%r13)
    123b:	41 c7 85 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%r13)
    1246:	41 c7 85 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%r13)
    1251:	41 c7 85 b0 01 00 00 00 00 00 00 	movl   $0x0,0x1b0(%r13)
    125c:	41 c7 85 e8 01 00 00 00 00 00 00 	movl   $0x0,0x1e8(%r13)
    1267:	41 c7 85 20 02 00 00 00 00 00 00 	movl   $0x0,0x220(%r13)
    1272:	41 c7 85 58 02 00 00 00 00 00 00 	movl   $0x0,0x258(%r13)
    127d:	41 c7 85 90 02 00 00 00 00 00 00 	movl   $0x0,0x290(%r13)
  }
  asm volatile ("sfence":::"memory");
    1288:	0f ae f8             	sfence

  for (int x = 0 ; x < thread_count ; x++) {
    128b:	48 8d 2d 89 0d 00 00 	lea    0xd89(%rip),%rbp        # 201b <_IO_stdin_used+0x1b>
    1292:	4c 8d 64 24 08       	lea    0x8(%rsp),%r12
    1297:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    void * result; 
    pthread_join(thread[x], &result);
    12a0:	48 8b 3b             	mov    (%rbx),%rdi
    12a3:	4c 89 e6             	mov    %r12,%rsi
  for (int x = 0 ; x < thread_count ; x++) {
    12a6:	48 83 c3 08          	add    $0x8,%rbx
    pthread_join(thread[x], &result);
    12aa:	e8 41 fe ff ff       	call   10f0 <pthread_join@plt>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    12af:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    12b4:	48 89 ee             	mov    %rbp,%rsi
    12b7:	31 c0                	xor    %eax,%eax
    12b9:	bf 01 00 00 00       	mov    $0x1,%edi
    12be:	e8 0d fe ff ff       	call   10d0 <__printf_chk@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    12c3:	4c 39 f3             	cmp    %r14,%rbx
    12c6:	75 d8                	jne    12a0 <main+0x1a0>
    printf("thread %ld result\n", (long)result);
  }
}
    12c8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    12cd:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    12d6:	75 11                	jne    12e9 <main+0x1e9>
    12d8:	48 83 c4 48          	add    $0x48,%rsp
    12dc:	31 c0                	xor    %eax,%eax
    12de:	5b                   	pop    %rbx
    12df:	5d                   	pop    %rbp
    12e0:	41 5c                	pop    %r12
    12e2:	41 5d                	pop    %r13
    12e4:	41 5e                	pop    %r14
    12e6:	41 5f                	pop    %r15
    12e8:	c3                   	ret
    12e9:	e8 b2 fd ff ff       	call   10a0 <__stack_chk_fail@plt>
    12ee:	66 90                	xchg   %ax,%ax

00000000000012f0 <_start>:
    12f0:	f3 0f 1e fa          	endbr64
    12f4:	31 ed                	xor    %ebp,%ebp
    12f6:	49 89 d1             	mov    %rdx,%r9
    12f9:	5e                   	pop    %rsi
    12fa:	48 89 e2             	mov    %rsp,%rdx
    12fd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1301:	50                   	push   %rax
    1302:	54                   	push   %rsp
    1303:	45 31 c0             	xor    %r8d,%r8d
    1306:	31 c9                	xor    %ecx,%ecx
    1308:	48 8d 3d f1 fd ff ff 	lea    -0x20f(%rip),%rdi        # 1100 <main>
    130f:	ff 15 c3 2c 00 00    	call   *0x2cc3(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1315:	f4                   	hlt
    1316:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001320 <deregister_tm_clones>:
    1320:	48 8d 3d e9 2c 00 00 	lea    0x2ce9(%rip),%rdi        # 4010 <__TMC_END__>
    1327:	48 8d 05 e2 2c 00 00 	lea    0x2ce2(%rip),%rax        # 4010 <__TMC_END__>
    132e:	48 39 f8             	cmp    %rdi,%rax
    1331:	74 15                	je     1348 <deregister_tm_clones+0x28>
    1333:	48 8b 05 a6 2c 00 00 	mov    0x2ca6(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    133a:	48 85 c0             	test   %rax,%rax
    133d:	74 09                	je     1348 <deregister_tm_clones+0x28>
    133f:	ff e0                	jmp    *%rax
    1341:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1348:	c3                   	ret
    1349:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001350 <register_tm_clones>:
    1350:	48 8d 3d b9 2c 00 00 	lea    0x2cb9(%rip),%rdi        # 4010 <__TMC_END__>
    1357:	48 8d 35 b2 2c 00 00 	lea    0x2cb2(%rip),%rsi        # 4010 <__TMC_END__>
    135e:	48 29 fe             	sub    %rdi,%rsi
    1361:	48 89 f0             	mov    %rsi,%rax
    1364:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1368:	48 c1 f8 03          	sar    $0x3,%rax
    136c:	48 01 c6             	add    %rax,%rsi
    136f:	48 d1 fe             	sar    %rsi
    1372:	74 14                	je     1388 <register_tm_clones+0x38>
    1374:	48 8b 05 75 2c 00 00 	mov    0x2c75(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    137b:	48 85 c0             	test   %rax,%rax
    137e:	74 08                	je     1388 <register_tm_clones+0x38>
    1380:	ff e0                	jmp    *%rax
    1382:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1388:	c3                   	ret
    1389:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001390 <__do_global_dtors_aux>:
    1390:	f3 0f 1e fa          	endbr64
    1394:	80 3d 75 2c 00 00 00 	cmpb   $0x0,0x2c75(%rip)        # 4010 <__TMC_END__>
    139b:	75 2b                	jne    13c8 <__do_global_dtors_aux+0x38>
    139d:	55                   	push   %rbp
    139e:	48 83 3d 52 2c 00 00 00 	cmpq   $0x0,0x2c52(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    13a6:	48 89 e5             	mov    %rsp,%rbp
    13a9:	74 0c                	je     13b7 <__do_global_dtors_aux+0x27>
    13ab:	48 8b 3d 56 2c 00 00 	mov    0x2c56(%rip),%rdi        # 4008 <__dso_handle>
    13b2:	e8 d9 fc ff ff       	call   1090 <__cxa_finalize@plt>
    13b7:	e8 64 ff ff ff       	call   1320 <deregister_tm_clones>
    13bc:	c6 05 4d 2c 00 00 01 	movb   $0x1,0x2c4d(%rip)        # 4010 <__TMC_END__>
    13c3:	5d                   	pop    %rbp
    13c4:	c3                   	ret
    13c5:	0f 1f 00             	nopl   (%rax)
    13c8:	c3                   	ret
    13c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000013d0 <frame_dummy>:
    13d0:	f3 0f 1e fa          	endbr64
    13d4:	e9 77 ff ff ff       	jmp    1350 <register_tm_clones>
    13d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000013e0 <stream>:
void* stream(void * arg) {
    13e0:	f3 0f 1e fa          	endbr64
    13e4:	41 54                	push   %r12
    13e6:	48 8d 35 17 0c 00 00 	lea    0xc17(%rip),%rsi        # 2004 <_IO_stdin_used+0x4>
    13ed:	31 c0                	xor    %eax,%eax
    13ef:	55                   	push   %rbp
    13f0:	53                   	push   %rbx
    13f1:	8b 17                	mov    (%rdi),%edx
    13f3:	48 89 fb             	mov    %rdi,%rbx
    13f6:	bf 01 00 00 00       	mov    $0x1,%edi
    13fb:	e8 d0 fc ff ff       	call   10d0 <__printf_chk@plt>
  while (log->running) {
    1400:	8b 4b 28             	mov    0x28(%rbx),%ecx
    1403:	85 c9                	test   %ecx,%ecx
    1405:	0f 84 d5 00 00 00    	je     14e0 <stream+0x100>
    for (int x = 0 ; x < log->data_size; x++) {
    140b:	48 63 4b 18          	movslq 0x18(%rbx),%rcx
    log->result = start + log->data[log->index % log->data_size];
    140f:	4c 8b 53 10          	mov    0x10(%rbx),%r10
    1413:	48 8b 73 20          	mov    0x20(%rbx),%rsi
    for (int x = 0 ; x < log->data_size; x++) {
    1417:	49 89 c8             	mov    %rcx,%r8
    141a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x  = 0 ; x < log->thread_count ; x++) {
    1420:	44 8b 63 04          	mov    0x4(%rbx),%r12d
    long start = 0;
    1424:	45 31 db             	xor    %r11d,%r11d
    for (int x  = 0 ; x < log->thread_count ; x++) {
    1427:	45 85 e4             	test   %r12d,%r12d
    142a:	7e 34                	jle    1460 <stream+0x80>
    142c:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    1430:	49 63 c4             	movslq %r12d,%rax
    long start = 0;
    1433:	45 31 db             	xor    %r11d,%r11d
    1436:	48 8d 2c c7          	lea    (%rdi,%rax,8),%rbp
    143a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      start += log->others[x]->data[log->others[x]->index % log->data_size];
    1440:	4c 8b 0f             	mov    (%rdi),%r9
    for (int x  = 0 ; x < log->thread_count ; x++) {
    1443:	48 83 c7 08          	add    $0x8,%rdi
      start += log->others[x]->data[log->others[x]->index % log->data_size];
    1447:	49 8b 41 20          	mov    0x20(%r9),%rax
    144b:	48 99                	cqto
    144d:	48 f7 f9             	idiv   %rcx
    1450:	49 8b 41 10          	mov    0x10(%r9),%rax
    1454:	48 63 04 90          	movslq (%rax,%rdx,4),%rax
    1458:	49 01 c3             	add    %rax,%r11
    for (int x  = 0 ; x < log->thread_count ; x++) {
    145b:	48 39 ef             	cmp    %rbp,%rdi
    145e:	75 e0                	jne    1440 <stream+0x60>
    for (int x = 0 ; x < log->data_size; x++) {
    1460:	45 85 c0             	test   %r8d,%r8d
    1463:	7e 6b                	jle    14d0 <stream+0xf0>
    1465:	45 31 c9             	xor    %r9d,%r9d
    1468:	eb 09                	jmp    1473 <stream+0x93>
    146a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1470:	49 63 c8             	movslq %r8d,%rcx
      log->data[(log->index + 1) % log->data_size] = log->data[log->index % log->data_size] + 1;    
    1473:	48 89 f0             	mov    %rsi,%rax
    1476:	48 83 c6 01          	add    $0x1,%rsi
    for (int x = 0 ; x < log->data_size; x++) {
    147a:	41 83 c1 01          	add    $0x1,%r9d
      log->data[(log->index + 1) % log->data_size] = log->data[log->index % log->data_size] + 1;    
    147e:	48 99                	cqto
    1480:	48 f7 f9             	idiv   %rcx
    1483:	48 89 f0             	mov    %rsi,%rax
    1486:	41 8b 3c 92          	mov    (%r10,%rdx,4),%edi
    148a:	48 99                	cqto
    148c:	48 f7 f9             	idiv   %rcx
    148f:	83 c7 01             	add    $0x1,%edi
    1492:	41 89 3c 92          	mov    %edi,(%r10,%rdx,4)
    for (int x = 0 ; x < log->data_size; x++) {
    1496:	44 8b 43 18          	mov    0x18(%rbx),%r8d
    149a:	45 39 c8             	cmp    %r9d,%r8d
    149d:	7f d1                	jg     1470 <stream+0x90>
    log->result = start + log->data[log->index % log->data_size];
    149f:	48 89 f0             	mov    %rsi,%rax
    14a2:	49 63 c8             	movslq %r8d,%rcx
    14a5:	48 89 73 20          	mov    %rsi,0x20(%rbx)
    14a9:	48 99                	cqto
    14ab:	48 f7 f9             	idiv   %rcx
    14ae:	49 63 04 92          	movslq (%r10,%rdx,4),%rax
  while (log->running) {
    14b2:	8b 53 28             	mov    0x28(%rbx),%edx
    14b5:	85 d2                	test   %edx,%edx
    14b7:	0f 85 63 ff ff ff    	jne    1420 <stream+0x40>
    log->result = start + log->data[log->index % log->data_size];
    14bd:	4c 01 d8             	add    %r11,%rax
    14c0:	48 89 43 30          	mov    %rax,0x30(%rbx)
}
    14c4:	5b                   	pop    %rbx
    14c5:	5d                   	pop    %rbp
    14c6:	41 5c                	pop    %r12
    14c8:	c3                   	ret
    14c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (log->running) {
    14d0:	8b 43 28             	mov    0x28(%rbx),%eax
    14d3:	85 c0                	test   %eax,%eax
    14d5:	74 12                	je     14e9 <stream+0x109>
    for (int x  = 0 ; x < log->thread_count ; x++) {
    14d7:	45 85 e4             	test   %r12d,%r12d
    14da:	7e fb                	jle    14d7 <stream+0xf7>
    14dc:	eb fe                	jmp    14dc <stream+0xfc>
    14de:	66 90                	xchg   %ax,%ax
  return log->result;
    14e0:	48 8b 43 30          	mov    0x30(%rbx),%rax
}
    14e4:	5b                   	pop    %rbx
    14e5:	5d                   	pop    %rbp
    14e6:	41 5c                	pop    %r12
    14e8:	c3                   	ret
    log->result = start + log->data[log->index % log->data_size];
    14e9:	48 89 f0             	mov    %rsi,%rax
    14ec:	48 99                	cqto
    14ee:	48 f7 f9             	idiv   %rcx
    14f1:	49 63 04 92          	movslq (%r10,%rdx,4),%rax
    14f5:	eb c6                	jmp    14bd <stream+0xdd>

Disassembly of section .fini:

00000000000014f8 <_fini>:
    14f8:	f3 0f 1e fa          	endbr64
    14fc:	48 83 ec 08          	sub    $0x8,%rsp
    1500:	48 83 c4 08          	add    $0x8,%rsp
    1504:	c3                   	ret
