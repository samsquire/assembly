
disruptor:     file format elf64-x86-64


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
    1020:	ff 35 52 2f 00 00    	push   0x2f52(%rip)        # 3f78 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:	ff 25 54 2f 00 00    	jmp    *0x2f54(%rip)        # 3f80 <_GLOBAL_OFFSET_TABLE_+0x10>
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

Disassembly of section .plt.got:

00000000000010d0 <__cxa_finalize@plt>:
    10d0:	f3 0f 1e fa          	endbr64
    10d4:	ff 25 1e 2f 00 00    	jmp    *0x2f1e(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    10da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

00000000000010e0 <puts@plt>:
    10e0:	f3 0f 1e fa          	endbr64
    10e4:	ff 25 9e 2e 00 00    	jmp    *0x2e9e(%rip)        # 3f88 <puts@GLIBC_2.2.5>
    10ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010f0 <clock_gettime@plt>:
    10f0:	f3 0f 1e fa          	endbr64
    10f4:	ff 25 96 2e 00 00    	jmp    *0x2e96(%rip)        # 3f90 <clock_gettime@GLIBC_2.17>
    10fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001100 <__stack_chk_fail@plt>:
    1100:	f3 0f 1e fa          	endbr64
    1104:	ff 25 8e 2e 00 00    	jmp    *0x2e8e(%rip)        # 3f98 <__stack_chk_fail@GLIBC_2.4>
    110a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001110 <nanosleep@plt>:
    1110:	f3 0f 1e fa          	endbr64
    1114:	ff 25 86 2e 00 00    	jmp    *0x2e86(%rip)        # 3fa0 <nanosleep@GLIBC_2.2.5>
    111a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001120 <pthread_attr_setschedpolicy@plt>:
    1120:	f3 0f 1e fa          	endbr64
    1124:	ff 25 7e 2e 00 00    	jmp    *0x2e7e(%rip)        # 3fa8 <pthread_attr_setschedpolicy@GLIBC_2.2.5>
    112a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001130 <calloc@plt>:
    1130:	f3 0f 1e fa          	endbr64
    1134:	ff 25 76 2e 00 00    	jmp    *0x2e76(%rip)        # 3fb0 <calloc@GLIBC_2.2.5>
    113a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001140 <__printf_chk@plt>:
    1140:	f3 0f 1e fa          	endbr64
    1144:	ff 25 6e 2e 00 00    	jmp    *0x2e6e(%rip)        # 3fb8 <__printf_chk@GLIBC_2.3.4>
    114a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001150 <pthread_create@plt>:
    1150:	f3 0f 1e fa          	endbr64
    1154:	ff 25 66 2e 00 00    	jmp    *0x2e66(%rip)        # 3fc0 <pthread_create@GLIBC_2.34>
    115a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001160 <exit@plt>:
    1160:	f3 0f 1e fa          	endbr64
    1164:	ff 25 5e 2e 00 00    	jmp    *0x2e5e(%rip)        # 3fc8 <exit@GLIBC_2.2.5>
    116a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001170 <pthread_join@plt>:
    1170:	f3 0f 1e fa          	endbr64
    1174:	ff 25 56 2e 00 00    	jmp    *0x2e56(%rip)        # 3fd0 <pthread_join@GLIBC_2.34>
    117a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000001180 <main>:
  } 
  printf("Finished\n");
  return 0;
}

int main() {
    1180:	f3 0f 1e fa          	endbr64
    1184:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    1186:	ba 00 10 00 00       	mov    $0x1000,%edx
    118b:	bf 01 00 00 00       	mov    $0x1,%edi
    int coreend = corestart + 3; 
    int receiver = sender + 1; 
    printf("%d is linked to %d\n", receiver, sender);
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    CPU_ZERO(sendercpu);
    for (int j = 0 ; j < cores; j++) {
    1190:	45 31 ff             	xor    %r15d,%r15d
int main() {
    1193:	41 56                	push   %r14
    1195:	48 8d 35 df 0e 00 00 	lea    0xedf(%rip),%rsi        # 207b <_IO_stdin_used+0x7b>
    119c:	4c 8d 35 8d 0e 00 00 	lea    0xe8d(%rip),%r14        # 2030 <_IO_stdin_used+0x30>
    11a3:	41 55                	push   %r13
    11a5:	41 54                	push   %r12
    11a7:	55                   	push   %rbp
      printf("assigning sender %d to core %d\n", sender, j);
      CPU_SET(j, sendercpu);
    11a8:	bd 01 00 00 00       	mov    $0x1,%ebp
int main() {
    11ad:	53                   	push   %rbx
    11ae:	48 83 ec 48          	sub    $0x48,%rsp
    11b2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    11bb:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    11c0:	31 c0                	xor    %eax,%eax
    11c2:	e8 79 ff ff ff       	call   1140 <__printf_chk@plt>
    11c7:	ba 01 00 00 00       	mov    $0x1,%edx
    11cc:	48 8d 35 c6 0e 00 00 	lea    0xec6(%rip),%rsi        # 2099 <_IO_stdin_used+0x99>
    11d3:	31 c0                	xor    %eax,%eax
    11d5:	bf 01 00 00 00       	mov    $0x1,%edi
    11da:	e8 61 ff ff ff       	call   1140 <__printf_chk@plt>
  struct Thread *thread_data = calloc(groups * 2, sizeof(struct Thread)); 
    11df:	be c0 00 00 00       	mov    $0xc0,%esi
    11e4:	bf 02 00 00 00       	mov    $0x2,%edi
    11e9:	e8 42 ff ff ff       	call   1130 <calloc@plt>
  pthread_attr_t      *attr = calloc(groups * 2, sizeof(pthread_attr_t));
    11ee:	be 38 00 00 00       	mov    $0x38,%esi
    11f3:	bf 02 00 00 00       	mov    $0x2,%edi
  struct Thread *thread_data = calloc(groups * 2, sizeof(struct Thread)); 
    11f8:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *attr = calloc(groups * 2, sizeof(pthread_attr_t));
    11fb:	e8 30 ff ff ff       	call   1130 <calloc@plt>
  pthread_t *thread = calloc(groups * 2, sizeof(pthread_t));
    1200:	be 08 00 00 00       	mov    $0x8,%esi
    1205:	bf 02 00 00 00       	mov    $0x2,%edi
  pthread_attr_t      *attr = calloc(groups * 2, sizeof(pthread_attr_t));
    120a:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_t *thread = calloc(groups * 2, sizeof(pthread_t));
    120f:	e8 1c ff ff ff       	call   1130 <calloc@plt>
    1214:	31 c9                	xor    %ecx,%ecx
    1216:	ba 01 00 00 00       	mov    $0x1,%edx
    121b:	48 8d 35 87 0e 00 00 	lea    0xe87(%rip),%rsi        # 20a9 <_IO_stdin_used+0xa9>
    1222:	bf 01 00 00 00       	mov    $0x1,%edi
    1227:	49 89 c5             	mov    %rax,%r13
    122a:	31 c0                	xor    %eax,%eax
    122c:	e8 0f ff ff ff       	call   1140 <__printf_chk@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1231:	be 80 00 00 00       	mov    $0x80,%esi
    1236:	bf 01 00 00 00       	mov    $0x1,%edi
    123b:	e8 f0 fe ff ff       	call   1130 <calloc@plt>
    1240:	48 89 c3             	mov    %rax,%rbx
    for (int j = 0 ; j < cores; j++) {
    1243:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    1248:	44 89 f9             	mov    %r15d,%ecx
    124b:	31 d2                	xor    %edx,%edx
    124d:	4c 89 f6             	mov    %r14,%rsi
    1250:	bf 01 00 00 00       	mov    $0x1,%edi
    1255:	31 c0                	xor    %eax,%eax
    1257:	e8 e4 fe ff ff       	call   1140 <__printf_chk@plt>
      CPU_SET(j, sendercpu);
    125c:	44 89 f9             	mov    %r15d,%ecx
    125f:	48 89 e8             	mov    %rbp,%rax
    for (int j = 0 ; j < cores; j++) {
    1262:	41 83 c7 01          	add    $0x1,%r15d
      CPU_SET(j, sendercpu);
    1266:	48 d3 e0             	shl    %cl,%rax
    1269:	48 09 03             	or     %rax,(%rbx)
    for (int j = 0 ; j < cores; j++) {
    126c:	41 83 ff 06          	cmp    $0x6,%r15d
    1270:	75 d6                	jne    1248 <main+0xc8>
    }
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1272:	be 80 00 00 00       	mov    $0x80,%esi
    1277:	bf 01 00 00 00       	mov    $0x1,%edi
    CPU_ZERO(receivercpu);
    for (int j = 0 ; j < cores ; j++) {
    127c:	45 31 f6             	xor    %r14d,%r14d
      printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    127f:	bd 01 00 00 00       	mov    $0x1,%ebp
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1284:	e8 a7 fe ff ff       	call   1130 <calloc@plt>
    1289:	49 89 c7             	mov    %rax,%r15
    for (int j = 0 ; j < cores ; j++) {
    128c:	0f 1f 40 00          	nopl   0x0(%rax)
    1290:	44 89 f1             	mov    %r14d,%ecx
    1293:	ba 01 00 00 00       	mov    $0x1,%edx
    1298:	bf 01 00 00 00       	mov    $0x1,%edi
    129d:	31 c0                	xor    %eax,%eax
    129f:	48 8d 35 aa 0d 00 00 	lea    0xdaa(%rip),%rsi        # 2050 <_IO_stdin_used+0x50>
    12a6:	e8 95 fe ff ff       	call   1140 <__printf_chk@plt>
      CPU_SET(j, receivercpu);
    12ab:	44 89 f1             	mov    %r14d,%ecx
    12ae:	48 89 e8             	mov    %rbp,%rax
    for (int j = 0 ; j < cores ; j++) {
    12b1:	41 83 c6 01          	add    $0x1,%r14d
      CPU_SET(j, receivercpu);
    12b5:	48 d3 e0             	shl    %cl,%rax
    12b8:	49 09 07             	or     %rax,(%r15)
    for (int j = 0 ; j < cores ; j++) {
    12bb:	41 83 fe 06          	cmp    $0x6,%r14d
    12bf:	75 cf                	jne    1290 <main+0x110>
    }
     
    thread_data[sender].thread_index = sender;
    12c1:	41 c7 04 24 00 00 00 00 	movl   $0x0,(%r12)
    thread_data[sender].cpu_set = sendercpu;
    thread_data[sender].mode = WRITER;
    thread_data[sender].running = 1;
    thread_data[sender].size = buffer_size;
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    12c9:	be 28 00 00 00       	mov    $0x28,%esi
    12ce:	bf 00 10 00 00       	mov    $0x1000,%edi
    thread_data[sender].mode = WRITER;
    12d3:	41 c7 84 24 84 00 00 00 00 00 00 00 	movl   $0x0,0x84(%r12)
    thread_data[sender].cpu_set = sendercpu;
    12df:	49 89 9c 24 98 00 00 00 	mov    %rbx,0x98(%r12)
    thread_data[sender].running = 1;
    12e7:	41 c7 84 24 90 00 00 00 01 00 00 00 	movl   $0x1,0x90(%r12)
    thread_data[sender].size = buffer_size;
    12f3:	49 c7 84 24 88 00 00 00 00 10 00 00 	movq   $0x1000,0x88(%r12)
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    12ff:	e8 2c fe ff ff       	call   1130 <calloc@plt>
    1304:	31 d2                	xor    %edx,%edx
    1306:	bf 01 00 00 00       	mov    $0x1,%edi
    130b:	48 8d 35 ab 0d 00 00 	lea    0xdab(%rip),%rsi        # 20bd <_IO_stdin_used+0xbd>
    1312:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    1317:	31 c0                	xor    %eax,%eax
    1319:	e8 22 fe ff ff       	call   1140 <__printf_chk@plt>
    131e:	31 d2                	xor    %edx,%edx
    1320:	48 8d 35 ab 0d 00 00 	lea    0xdab(%rip),%rsi        # 20d2 <_IO_stdin_used+0xd2>
    1327:	31 c0                	xor    %eax,%eax
    printf("Created data for %d\n", sender);
    thread_data[receiver].thread_index = receiver;
    thread_data[receiver].cpu_set = receivercpu;
    1329:	4d 89 bc 24 58 01 00 00 	mov    %r15,0x158(%r12)
    1331:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[receiver].running = 1;
    1336:	41 c7 84 24 50 01 00 00 01 00 00 00 	movl   $0x1,0x150(%r12)
    thread_data[receiver].thread_index = receiver;
    1342:	41 c7 84 24 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%r12)
    thread_data[receiver].mode = READER;
    134e:	41 c7 84 24 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%r12)
    thread_data[receiver].size = buffer_size;
    135a:	49 c7 84 24 48 01 00 00 00 10 00 00 	movq   $0x1000,0x148(%r12)
    thread_data[receiver].sender = &thread_data[sender];
    1366:	4d 89 a4 24 c8 00 00 00 	mov    %r12,0xc8(%r12)
    136e:	e8 cd fd ff ff       	call   1140 <__printf_chk@plt>
    1373:	ba 01 00 00 00       	mov    $0x1,%edx
    1378:	48 8d 35 6e 0d 00 00 	lea    0xd6e(%rip),%rsi        # 20ed <_IO_stdin_used+0xed>
    137f:	31 c0                	xor    %eax,%eax
    1381:	bf 01 00 00 00       	mov    $0x1,%edi
    1386:	e8 b5 fd ff ff       	call   1140 <__printf_chk@plt>
    printf("Creating sender thread %d\n", sender);
    printf("Creating receiver thread %d\n", receiver);
    asm volatile ("mfence" ::: "memory");
    138b:	0f ae f0             	mfence
  }
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 2; 
    int receiver = sender + 1; 
    
    pthread_create(&thread[receiver], &attr[receiver], &disruptor_thread, &thread_data[receiver]);
    138e:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    1393:	48 8d 1d a6 02 00 00 	lea    0x2a6(%rip),%rbx        # 1640 <disruptor_thread>
    139a:	49 8d 7d 08          	lea    0x8(%r13),%rdi
    139e:	49 8d 8c 24 c0 00 00 00 	lea    0xc0(%r12),%rcx
    13a6:	48 89 da             	mov    %rbx,%rdx
    13a9:	48 8d 68 38          	lea    0x38(%rax),%rbp
    13ad:	48 89 ee             	mov    %rbp,%rsi
    13b0:	e8 9b fd ff ff       	call   1150 <pthread_create@plt>
    int ret = pthread_attr_setschedpolicy(&attr[receiver], SCHED_RR);
    13b5:	be 02 00 00 00       	mov    $0x2,%esi
    13ba:	48 89 ef             	mov    %rbp,%rdi
    13bd:	e8 5e fd ff ff       	call   1120 <pthread_attr_setschedpolicy@plt>
    if (ret) {
    13c2:	85 c0                	test   %eax,%eax
    13c4:	0f 85 61 01 00 00    	jne    152b <main+0x3ab>
            printf("pthread setschedpolicy failed\n");
            exit(1);
    }
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    13ca:	48 89 da             	mov    %rbx,%rdx
    13cd:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    13d2:	4c 89 e1             	mov    %r12,%rcx
    13d5:	4c 89 ef             	mov    %r13,%rdi
    13d8:	48 89 de             	mov    %rbx,%rsi
    13db:	e8 70 fd ff ff       	call   1150 <pthread_create@plt>
    ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_RR);
    13e0:	be 02 00 00 00       	mov    $0x2,%esi
    13e5:	48 89 df             	mov    %rbx,%rdi
    13e8:	e8 33 fd ff ff       	call   1120 <pthread_attr_setschedpolicy@plt>
    13ed:	89 c5                	mov    %eax,%ebp
    if (ret) {
    13ef:	85 c0                	test   %eax,%eax
    13f1:	0f 85 34 01 00 00    	jne    152b <main+0x3ab>
    13f7:	48 8d 3d 2a 0d 00 00 	lea    0xd2a(%rip),%rdi        # 2128 <_IO_stdin_used+0x128>
    13fe:	31 db                	xor    %ebx,%ebx
    1400:	e8 db fc ff ff       	call   10e0 <puts@plt>
    // printf("Waiting before starting next disruptor %ld ns\n", TICK);
    // nanosleep(&preempt , &rem2);
    }
  int seconds = 10;
  struct timespec rem2;
  struct timespec preempt = {
    1405:	66 0f 6f 05 93 0d 00 00 	movdqa 0xd93(%rip),%xmm0        # 21a0 <_IO_stdin_used+0x1a0>
    140d:	ba 0a 00 00 00       	mov    $0xa,%edx
    1412:	31 c0                	xor    %eax,%eax
    1414:	48 8d 35 1c 0d 00 00 	lea    0xd1c(%rip),%rsi        # 2137 <_IO_stdin_used+0x137>
    141b:	bf 01 00 00 00       	mov    $0x1,%edi
    1420:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
    1425:	e8 16 fd ff ff       	call   1140 <__printf_chk@plt>
    seconds,
    0 };
  printf("Sleeping for %d seconds\n", seconds);
  nanosleep(&preempt , &rem2);
    142a:	48 8d 74 24 10       	lea    0x10(%rsp),%rsi
    142f:	48 8d 7c 24 20       	lea    0x20(%rsp),%rdi
    1434:	e8 d7 fc ff ff       	call   1110 <nanosleep@plt>
  for (int x = 0 ; x < groups ; x++) {
    void * res1;
    void * res2;
    int sender = x * 2; 
    int receiver = sender + 1; 
    pthread_join(thread[sender], res1);
    1439:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    143d:	31 f6                	xor    %esi,%esi
    thread_data[sender].running = 0;
    143f:	41 c7 84 24 90 00 00 00 00 00 00 00 	movl   $0x0,0x90(%r12)
    thread_data[receiver].running = 0;
    144b:	41 c7 84 24 50 01 00 00 00 00 00 00 	movl   $0x0,0x150(%r12)
    pthread_join(thread[sender], res1);
    1457:	e8 14 fd ff ff       	call   1170 <pthread_join@plt>
    pthread_join(thread[receiver], res2);
    145c:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    1460:	31 f6                	xor    %esi,%esi
    1462:	4c 8d 2d 04 0d 00 00 	lea    0xd04(%rip),%r13        # 216d <_IO_stdin_used+0x16d>
    1469:	e8 02 fd ff ff       	call   1170 <pthread_join@plt>
    146e:	31 d2                	xor    %edx,%edx
    1470:	48 8d 35 d9 0c 00 00 	lea    0xcd9(%rip),%rsi        # 2150 <_IO_stdin_used+0x150>
    1477:	31 c0                	xor    %eax,%eax
    1479:	bf 01 00 00 00       	mov    $0x1,%edi
    147e:	e8 bd fc ff ff       	call   1140 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 2; 
    int receiver = sender + 1;
    int incompletes = 0;
    printf("Inspecting sender %d\n", sender);
    printf("%d %d\n", thread_data[sender].start, thread_data[sender].end);
    1483:	41 8b 8c 24 80 00 00 00 	mov    0x80(%r12),%ecx
    148b:	41 8b 54 24 40       	mov    0x40(%r12),%edx
    1490:	31 c0                	xor    %eax,%eax
    1492:	48 8d 35 cd 0c 00 00 	lea    0xccd(%rip),%rsi        # 2166 <_IO_stdin_used+0x166>
    1499:	bf 01 00 00 00       	mov    $0x1,%edi
    149e:	e8 9d fc ff ff       	call   1140 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    14a3:	eb 13                	jmp    14b8 <main+0x338>
    14a5:	0f 1f 00             	nopl   (%rax)
    14a8:	48 83 c3 28          	add    $0x28,%rbx
        struct timespec end = thread_data[sender].data[y].end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("rb %d Read %ld %ld\n", sender, seconds, seconds2);
      } else {
        incompletes++;
    14ac:	83 c5 01             	add    $0x1,%ebp
    for (int y = 0 ; y < buffer_size; y++) {
    14af:	48 81 fb 00 80 02 00 	cmp    $0x28000,%rbx
    14b6:	74 3d                	je     14f5 <main+0x375>
      if (thread_data[sender].data[y].complete == 1) {
    14b8:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    14bd:	48 01 d8             	add    %rbx,%rax
    14c0:	8b 50 20             	mov    0x20(%rax),%edx
    14c3:	83 fa 01             	cmp    $0x1,%edx
    14c6:	75 e0                	jne    14a8 <main+0x328>
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    14c8:	4c 8b 40 18          	mov    0x18(%rax),%r8
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    14cc:	48 8b 48 10          	mov    0x10(%rax),%rcx
    14d0:	31 d2                	xor    %edx,%edx
    14d2:	4c 89 ee             	mov    %r13,%rsi
    14d5:	48 2b 08             	sub    (%rax),%rcx
    14d8:	4c 2b 40 08          	sub    0x8(%rax),%r8
    14dc:	bf 01 00 00 00       	mov    $0x1,%edi
    14e1:	31 c0                	xor    %eax,%eax
    14e3:	e8 58 fc ff ff       	call   1140 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    14e8:	48 83 c3 28          	add    $0x28,%rbx
    14ec:	48 81 fb 00 80 02 00 	cmp    $0x28000,%rbx
    14f3:	75 c3                	jne    14b8 <main+0x338>
    14f5:	31 c0                	xor    %eax,%eax
    14f7:	89 ea                	mov    %ebp,%edx
    14f9:	48 8d 35 81 0c 00 00 	lea    0xc81(%rip),%rsi        # 2181 <_IO_stdin_used+0x181>
    1500:	bf 01 00 00 00       	mov    $0x1,%edi
    1505:	e8 36 fc ff ff       	call   1140 <__printf_chk@plt>
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    150a:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    150f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1518:	75 27                	jne    1541 <main+0x3c1>
    151a:	48 83 c4 48          	add    $0x48,%rsp
    151e:	31 c0                	xor    %eax,%eax
    1520:	5b                   	pop    %rbx
    1521:	5d                   	pop    %rbp
    1522:	41 5c                	pop    %r12
    1524:	41 5d                	pop    %r13
    1526:	41 5e                	pop    %r14
    1528:	41 5f                	pop    %r15
    152a:	c3                   	ret
    152b:	48 8d 3d d8 0b 00 00 	lea    0xbd8(%rip),%rdi        # 210a <_IO_stdin_used+0x10a>
    1532:	e8 a9 fb ff ff       	call   10e0 <puts@plt>
            exit(1);
    1537:	bf 01 00 00 00       	mov    $0x1,%edi
    153c:	e8 1f fc ff ff       	call   1160 <exit@plt>
}
    1541:	e8 ba fb ff ff       	call   1100 <__stack_chk_fail@plt>
    1546:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001550 <_start>:
    1550:	f3 0f 1e fa          	endbr64
    1554:	31 ed                	xor    %ebp,%ebp
    1556:	49 89 d1             	mov    %rdx,%r9
    1559:	5e                   	pop    %rsi
    155a:	48 89 e2             	mov    %rsp,%rdx
    155d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1561:	50                   	push   %rax
    1562:	54                   	push   %rsp
    1563:	45 31 c0             	xor    %r8d,%r8d
    1566:	31 c9                	xor    %ecx,%ecx
    1568:	48 8d 3d 11 fc ff ff 	lea    -0x3ef(%rip),%rdi        # 1180 <main>
    156f:	ff 15 63 2a 00 00    	call   *0x2a63(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1575:	f4                   	hlt
    1576:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001580 <deregister_tm_clones>:
    1580:	48 8d 3d 89 2a 00 00 	lea    0x2a89(%rip),%rdi        # 4010 <__TMC_END__>
    1587:	48 8d 05 82 2a 00 00 	lea    0x2a82(%rip),%rax        # 4010 <__TMC_END__>
    158e:	48 39 f8             	cmp    %rdi,%rax
    1591:	74 15                	je     15a8 <deregister_tm_clones+0x28>
    1593:	48 8b 05 46 2a 00 00 	mov    0x2a46(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    159a:	48 85 c0             	test   %rax,%rax
    159d:	74 09                	je     15a8 <deregister_tm_clones+0x28>
    159f:	ff e0                	jmp    *%rax
    15a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    15a8:	c3                   	ret
    15a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000015b0 <register_tm_clones>:
    15b0:	48 8d 3d 59 2a 00 00 	lea    0x2a59(%rip),%rdi        # 4010 <__TMC_END__>
    15b7:	48 8d 35 52 2a 00 00 	lea    0x2a52(%rip),%rsi        # 4010 <__TMC_END__>
    15be:	48 29 fe             	sub    %rdi,%rsi
    15c1:	48 89 f0             	mov    %rsi,%rax
    15c4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    15c8:	48 c1 f8 03          	sar    $0x3,%rax
    15cc:	48 01 c6             	add    %rax,%rsi
    15cf:	48 d1 fe             	sar    %rsi
    15d2:	74 14                	je     15e8 <register_tm_clones+0x38>
    15d4:	48 8b 05 15 2a 00 00 	mov    0x2a15(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    15db:	48 85 c0             	test   %rax,%rax
    15de:	74 08                	je     15e8 <register_tm_clones+0x38>
    15e0:	ff e0                	jmp    *%rax
    15e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    15e8:	c3                   	ret
    15e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000015f0 <__do_global_dtors_aux>:
    15f0:	f3 0f 1e fa          	endbr64
    15f4:	80 3d 15 2a 00 00 00 	cmpb   $0x0,0x2a15(%rip)        # 4010 <__TMC_END__>
    15fb:	75 2b                	jne    1628 <__do_global_dtors_aux+0x38>
    15fd:	55                   	push   %rbp
    15fe:	48 83 3d f2 29 00 00 00 	cmpq   $0x0,0x29f2(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1606:	48 89 e5             	mov    %rsp,%rbp
    1609:	74 0c                	je     1617 <__do_global_dtors_aux+0x27>
    160b:	48 8b 3d f6 29 00 00 	mov    0x29f6(%rip),%rdi        # 4008 <__dso_handle>
    1612:	e8 b9 fa ff ff       	call   10d0 <__cxa_finalize@plt>
    1617:	e8 64 ff ff ff       	call   1580 <deregister_tm_clones>
    161c:	c6 05 ed 29 00 00 01 	movb   $0x1,0x29ed(%rip)        # 4010 <__TMC_END__>
    1623:	5d                   	pop    %rbp
    1624:	c3                   	ret
    1625:	0f 1f 00             	nopl   (%rax)
    1628:	c3                   	ret
    1629:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001630 <frame_dummy>:
    1630:	f3 0f 1e fa          	endbr64
    1634:	e9 77 ff ff ff       	jmp    15b0 <register_tm_clones>
    1639:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001640 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    1640:	f3 0f 1e fa          	endbr64
    1644:	55                   	push   %rbp
    1645:	48 8d 35 bc 09 00 00 	lea    0x9bc(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    164c:	31 c0                	xor    %eax,%eax
    164e:	53                   	push   %rbx
    164f:	48 89 fb             	mov    %rdi,%rbx
    1652:	48 83 ec 08          	sub    $0x8,%rsp
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    1656:	8b 8f 84 00 00 00    	mov    0x84(%rdi),%ecx
    165c:	8b 17                	mov    (%rdi),%edx
    165e:	bf 01 00 00 00       	mov    $0x1,%edi
    1663:	e8 d8 fa ff ff       	call   1140 <__printf_chk@plt>
  if (data->mode == WRITER) {
    1668:	8b 83 84 00 00 00    	mov    0x84(%rbx),%eax
    166e:	85 c0                	test   %eax,%eax
    1670:	74 4b                	je     16bd <disruptor_thread+0x7d>
  else if (data->mode == READER) {
    1672:	8b 83 84 00 00 00    	mov    0x84(%rbx),%eax
    1678:	83 f8 01             	cmp    $0x1,%eax
    167b:	0f 84 af 00 00 00    	je     1730 <disruptor_thread+0xf0>
    1681:	48 8d 3d ea 09 00 00 	lea    0x9ea(%rip),%rdi        # 2072 <_IO_stdin_used+0x72>
    1688:	e8 53 fa ff ff       	call   10e0 <puts@plt>
}
    168d:	48 83 c4 08          	add    $0x8,%rsp
    1691:	31 c0                	xor    %eax,%eax
    1693:	5b                   	pop    %rbx
    1694:	5d                   	pop    %rbp
    1695:	c3                   	ret
    1696:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      if ((data->end + 1) % data->size == data->start) {
    16a0:	8b 83 80 00 00 00    	mov    0x80(%rbx),%eax
    16a6:	48 63 4b 40          	movslq 0x40(%rbx),%rcx
    16aa:	83 c0 01             	add    $0x1,%eax
    16ad:	48 98                	cltq
    16af:	48 99                	cqto
    16b1:	48 f7 bb 88 00 00 00 	idivq  0x88(%rbx)
    16b8:	48 39 ca             	cmp    %rcx,%rdx
    16bb:	75 13                	jne    16d0 <disruptor_thread+0x90>
    while (data->running == 1) {
    16bd:	8b 83 90 00 00 00    	mov    0x90(%rbx),%eax
    16c3:	83 f8 01             	cmp    $0x1,%eax
    16c6:	74 d8                	je     16a0 <disruptor_thread+0x60>
    16c8:	eb b7                	jmp    1681 <disruptor_thread+0x41>
    16ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[data->end].start);
    16d0:	48 63 83 80 00 00 00 	movslq 0x80(%rbx),%rax
    16d7:	bf 04 00 00 00       	mov    $0x4,%edi
    16dc:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    16e0:	48 8b 43 10          	mov    0x10(%rbx),%rax
    16e4:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    16e8:	e8 03 fa ff ff       	call   10f0 <clock_gettime@plt>
        data->data[data->end].complete = 0;
    16ed:	48 63 83 80 00 00 00 	movslq 0x80(%rbx),%rax
    16f4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    16f8:	48 8b 43 10          	mov    0x10(%rbx),%rax
    16fc:	48 8d 04 d0          	lea    (%rax,%rdx,8),%rax
    1700:	c7 40 20 00 00 00 00 	movl   $0x0,0x20(%rax)
        data->end = (data->end + 1) % data->size;
    1707:	8b 83 80 00 00 00    	mov    0x80(%rbx),%eax
    170d:	83 c0 01             	add    $0x1,%eax
    1710:	48 98                	cltq
    1712:	48 99                	cqto
    1714:	48 f7 bb 88 00 00 00 	idivq  0x88(%rbx)
    171b:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
        asm volatile ("mfence" ::: "memory");
    1721:	0f ae f0             	mfence
    1724:	eb 97                	jmp    16bd <disruptor_thread+0x7d>
    1726:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    while (data->running == 1) {
    1730:	8b 83 90 00 00 00    	mov    0x90(%rbx),%eax
    struct Thread *sender = data->sender;
    1736:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    while (data->running == 1) {
    173a:	83 f8 01             	cmp    $0x1,%eax
    173d:	0f 85 3e ff ff ff    	jne    1681 <disruptor_thread+0x41>
      if (sender->end == sender->start) {
    1743:	8b 95 80 00 00 00    	mov    0x80(%rbp),%edx
    1749:	8b 45 40             	mov    0x40(%rbp),%eax
    174c:	39 c2                	cmp    %eax,%edx
    174e:	75 1f                	jne    176f <disruptor_thread+0x12f>
        asm volatile ("mfence" ::: "memory");
    1750:	0f ae f0             	mfence
    while (data->running == 1) {
    1753:	8b 83 90 00 00 00    	mov    0x90(%rbx),%eax
    1759:	83 f8 01             	cmp    $0x1,%eax
    175c:	0f 85 1f ff ff ff    	jne    1681 <disruptor_thread+0x41>
      if (sender->end == sender->start) {
    1762:	8b 95 80 00 00 00    	mov    0x80(%rbp),%edx
    1768:	8b 45 40             	mov    0x40(%rbp),%eax
    176b:	39 c2                	cmp    %eax,%edx
    176d:	74 e1                	je     1750 <disruptor_thread+0x110>
        clock_gettime(CLOCK_MONOTONIC_RAW, &sender->data[sender->start].end);
    176f:	48 63 45 40          	movslq 0x40(%rbp),%rax
    1773:	bf 04 00 00 00       	mov    $0x4,%edi
    1778:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    177c:	48 8b 45 10          	mov    0x10(%rbp),%rax
    1780:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    1785:	e8 66 f9 ff ff       	call   10f0 <clock_gettime@plt>
        sender->data[sender->start].complete = 1;
    178a:	48 63 45 40          	movslq 0x40(%rbp),%rax
    178e:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    1792:	48 8b 45 10          	mov    0x10(%rbp),%rax
    1796:	48 8d 04 d0          	lea    (%rax,%rdx,8),%rax
    179a:	c7 40 20 01 00 00 00 	movl   $0x1,0x20(%rax)
        sender->start = (sender->start + 1) % data->size;
    17a1:	8b 45 40             	mov    0x40(%rbp),%eax
    17a4:	83 c0 01             	add    $0x1,%eax
    17a7:	48 98                	cltq
    17a9:	48 99                	cqto
    17ab:	48 f7 bb 88 00 00 00 	idivq  0x88(%rbx)
    17b2:	89 55 40             	mov    %edx,0x40(%rbp)
    while (data->running == 1) {
    17b5:	8b 83 90 00 00 00    	mov    0x90(%rbx),%eax
    17bb:	83 f8 01             	cmp    $0x1,%eax
    17be:	74 83                	je     1743 <disruptor_thread+0x103>
    17c0:	e9 bc fe ff ff       	jmp    1681 <disruptor_thread+0x41>

Disassembly of section .fini:

00000000000017c8 <_fini>:
    17c8:	f3 0f 1e fa          	endbr64
    17cc:	48 83 ec 08          	sub    $0x8,%rsp
    17d0:	48 83 c4 08          	add    $0x8,%rsp
    17d4:	c3                   	ret
