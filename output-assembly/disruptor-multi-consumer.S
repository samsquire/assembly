
disruptor-multi-consumer:     file format elf64-x86-64


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
    1020:	ff 35 42 2f 00 00    	push   0x2f42(%rip)        # 3f68 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:	ff 25 44 2f 00 00    	jmp    *0x2f44(%rip)        # 3f70 <_GLOBAL_OFFSET_TABLE_+0x10>
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

Disassembly of section .plt.got:

00000000000010f0 <__cxa_finalize@plt>:
    10f0:	f3 0f 1e fa          	endbr64
    10f4:	ff 25 fe 2e 00 00    	jmp    *0x2efe(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    10fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000001100 <pthread_setaffinity_np@plt>:
    1100:	f3 0f 1e fa          	endbr64
    1104:	ff 25 6e 2e 00 00    	jmp    *0x2e6e(%rip)        # 3f78 <pthread_setaffinity_np@GLIBC_2.34>
    110a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001110 <puts@plt>:
    1110:	f3 0f 1e fa          	endbr64
    1114:	ff 25 66 2e 00 00    	jmp    *0x2e66(%rip)        # 3f80 <puts@GLIBC_2.2.5>
    111a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001120 <clock_gettime@plt>:
    1120:	f3 0f 1e fa          	endbr64
    1124:	ff 25 5e 2e 00 00    	jmp    *0x2e5e(%rip)        # 3f88 <clock_gettime@GLIBC_2.17>
    112a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001130 <__stack_chk_fail@plt>:
    1130:	f3 0f 1e fa          	endbr64
    1134:	ff 25 56 2e 00 00    	jmp    *0x2e56(%rip)        # 3f90 <__stack_chk_fail@GLIBC_2.4>
    113a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001140 <nanosleep@plt>:
    1140:	f3 0f 1e fa          	endbr64
    1144:	ff 25 4e 2e 00 00    	jmp    *0x2e4e(%rip)        # 3f98 <nanosleep@GLIBC_2.2.5>
    114a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001150 <pthread_attr_setschedpolicy@plt>:
    1150:	f3 0f 1e fa          	endbr64
    1154:	ff 25 46 2e 00 00    	jmp    *0x2e46(%rip)        # 3fa0 <pthread_attr_setschedpolicy@GLIBC_2.2.5>
    115a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001160 <calloc@plt>:
    1160:	f3 0f 1e fa          	endbr64
    1164:	ff 25 3e 2e 00 00    	jmp    *0x2e3e(%rip)        # 3fa8 <calloc@GLIBC_2.2.5>
    116a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001170 <__printf_chk@plt>:
    1170:	f3 0f 1e fa          	endbr64
    1174:	ff 25 36 2e 00 00    	jmp    *0x2e36(%rip)        # 3fb0 <__printf_chk@GLIBC_2.3.4>
    117a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001180 <pthread_create@plt>:
    1180:	f3 0f 1e fa          	endbr64
    1184:	ff 25 2e 2e 00 00    	jmp    *0x2e2e(%rip)        # 3fb8 <pthread_create@GLIBC_2.34>
    118a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001190 <pthread_attr_setschedparam@plt>:
    1190:	f3 0f 1e fa          	endbr64
    1194:	ff 25 26 2e 00 00    	jmp    *0x2e26(%rip)        # 3fc0 <pthread_attr_setschedparam@GLIBC_2.2.5>
    119a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011a0 <exit@plt>:
    11a0:	f3 0f 1e fa          	endbr64
    11a4:	ff 25 1e 2e 00 00    	jmp    *0x2e1e(%rip)        # 3fc8 <exit@GLIBC_2.2.5>
    11aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011b0 <pthread_join@plt>:
    11b0:	f3 0f 1e fa          	endbr64
    11b4:	ff 25 16 2e 00 00    	jmp    *0x2e16(%rip)        # 3fd0 <pthread_join@GLIBC_2.34>
    11ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

00000000000011c0 <main>:
  } 
  printf("Finished %d\n", data->mode);
  return 0;
}

int main() {
    11c0:	f3 0f 1e fa          	endbr64
    11c4:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    11c6:	b9 00 00 10 00       	mov    $0x100000,%ecx
    11cb:	ba 14 00 00 00       	mov    $0x14,%edx
    11d0:	48 8d 35 59 0e 00 00 	lea    0xe59(%rip),%rsi        # 2030 <_IO_stdin_used+0x30>
    11d7:	41 56                	push   %r14
    11d9:	bf 01 00 00 00       	mov    $0x1,%edi
    11de:	41 55                	push   %r13
    11e0:	41 54                	push   %r12
    11e2:	55                   	push   %rbp
    11e3:	53                   	push   %rbx
    11e4:	48 83 ec 68          	sub    $0x68,%rsp
    11e8:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    11f1:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    11f6:	31 c0                	xor    %eax,%eax
    11f8:	e8 73 ff ff ff       	call   1170 <__printf_chk@plt>
    11fd:	ba 01 00 00 00       	mov    $0x1,%edx
    1202:	48 8d 35 a1 0e 00 00 	lea    0xea1(%rip),%rsi        # 20aa <_IO_stdin_used+0xaa>
    1209:	31 c0                	xor    %eax,%eax
    120b:	bf 01 00 00 00       	mov    $0x1,%edi
    1210:	e8 5b ff ff ff       	call   1170 <__printf_chk@plt>
    1215:	ba 02 00 00 00       	mov    $0x2,%edx
    121a:	48 8d 35 99 0e 00 00 	lea    0xe99(%rip),%rsi        # 20ba <_IO_stdin_used+0xba>
    1221:	31 c0                	xor    %eax,%eax
    1223:	bf 01 00 00 00       	mov    $0x1,%edi
    1228:	e8 43 ff ff ff       	call   1170 <__printf_chk@plt>
    122d:	ba 03 00 00 00       	mov    $0x3,%edx
    1232:	48 8d 35 93 0e 00 00 	lea    0xe93(%rip),%rsi        # 20cc <_IO_stdin_used+0xcc>
    1239:	31 c0                	xor    %eax,%eax
    123b:	bf 01 00 00 00       	mov    $0x1,%edi
    1240:	e8 2b ff ff ff       	call   1170 <__printf_chk@plt>
  int other_count = 2;
  int group_size = writers_count + other_count;
  printf("Readers count %d\n", other_count);
  int thread_count = groups * (other_count + writers_count);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1245:	be 00 02 00 00       	mov    $0x200,%esi
    124a:	bf 03 00 00 00       	mov    $0x3,%edi
    124f:	e8 0c ff ff ff       	call   1160 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1254:	be 38 00 00 00       	mov    $0x38,%esi
    1259:	bf 03 00 00 00       	mov    $0x3,%edi
    125e:	66 48 0f 6e c8       	movq   %rax,%xmm1
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1263:	48 89 c3             	mov    %rax,%rbx
    1266:	66 0f 6c c9          	punpcklqdq %xmm1,%xmm1
    126a:	0f 29 0c 24          	movaps %xmm1,(%rsp)
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    126e:	e8 ed fe ff ff       	call   1160 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1273:	be 08 00 00 00       	mov    $0x8,%esi
    1278:	bf 03 00 00 00       	mov    $0x3,%edi
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    127d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1282:	e8 d9 fe ff ff       	call   1160 <calloc@plt>
  // 0, 3, 6
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1; 
    int receiver2 = receiver + 1; 
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1287:	be 80 00 00 00       	mov    $0x80,%esi
    128c:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1291:	49 89 c5             	mov    %rax,%r13
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1294:	e8 c7 fe ff ff       	call   1160 <calloc@plt>
    CPU_ZERO(sendercpu);
    for (int j = 0 ; j < cores ; j++) {
      // printf("assigning sender %d to core %d\n", sender, j);
      CPU_SET(j, sendercpu);
    }
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1299:	be 80 00 00 00       	mov    $0x80,%esi
    129e:	bf 01 00 00 00       	mov    $0x1,%edi
      CPU_SET(j, sendercpu);
    12a3:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12aa:	48 89 c5             	mov    %rax,%rbp
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12ad:	e8 ae fe ff ff       	call   1160 <calloc@plt>
    for (int j = 0; j < cores ; j++) {
      // printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    }
     
    thread_data[sender].thread_index = sender;
    12b2:	c7 03 00 00 00 00    	movl   $0x0,(%rbx)
    thread_data[sender].mode = WRITER;
    thread_data[sender].running = 1;
    thread_data[sender].size = buffer_size;
    thread_data[sender].end = 0;
    thread_data[sender].sender = &thread_data[sender];
    thread_data[sender].readers = calloc(other_count, sizeof(struct Thread*));
    12b8:	be 08 00 00 00       	mov    $0x8,%esi
    12bd:	bf 02 00 00 00       	mov    $0x2,%edi
      CPU_SET(j, receivercpu);
    12c2:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12c9:	49 89 c6             	mov    %rax,%r14
    thread_data[sender].cpu_set = sendercpu;
    12cc:	48 89 ab 18 01 00 00 	mov    %rbp,0x118(%rbx)
    thread_data[sender].mode = WRITER;
    12d3:	c7 83 04 01 00 00 00 00 00 00 	movl   $0x0,0x104(%rbx)
    thread_data[sender].size = buffer_size;
    12dd:	48 c7 83 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%rbx)
    thread_data[sender].running = 1;
    12e8:	c7 83 10 01 00 00 01 00 00 00 	movl   $0x1,0x110(%rbx)
    thread_data[sender].end = 0;
    12f2:	c7 83 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbx)
    thread_data[sender].sender = &thread_data[sender];
    12fc:	48 89 5b 08          	mov    %rbx,0x8(%rbx)
    thread_data[sender].readers = calloc(other_count, sizeof(struct Thread*));
    1300:	e8 5b fe ff ff       	call   1160 <calloc@plt>
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    1305:	be 80 01 00 00       	mov    $0x180,%esi
    130a:	bf 00 00 10 00       	mov    $0x100000,%edi
    thread_data[sender].readers = calloc(other_count, sizeof(struct Thread*));
    130f:	48 89 83 80 01 00 00 	mov    %rax,0x180(%rbx)
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    1316:	e8 45 fe ff ff       	call   1160 <calloc@plt>
    131b:	48 89 43 18          	mov    %rax,0x18(%rbx)
    131f:	49 89 c4             	mov    %rax,%r12
    for (int n = 0 ; n < buffer_size ; n++) {
    1322:	48 8d a8 00 01 00 00 	lea    0x100(%rax),%rbp
    1329:	49 81 c4 00 01 00 18 	add    $0x18000100,%r12
      thread_data[sender].data[n].complete = calloc(other_count, sizeof(int));
    1330:	be 04 00 00 00       	mov    $0x4,%esi
    1335:	bf 02 00 00 00       	mov    $0x2,%edi
    for (int n = 0 ; n < buffer_size ; n++) {
    133a:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
      thread_data[sender].data[n].complete = calloc(other_count, sizeof(int));
    1341:	e8 1a fe ff ff       	call   1160 <calloc@plt>
    1346:	48 89 85 80 fe ff ff 	mov    %rax,-0x180(%rbp)
    for (int n = 0 ; n < buffer_size ; n++) {
    134d:	4c 39 e5             	cmp    %r12,%rbp
    1350:	75 de                	jne    1330 <main+0x170>
    }
    thread_data[sender].other_count = other_count;
    1352:	c7 83 88 01 00 00 02 00 00 00 	movl   $0x2,0x188(%rbx)
    // printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    135c:	48 8d ab 00 02 00 00 	lea    0x200(%rbx),%rbp
    thread_data[sender].other_count = other_count;
    1363:	b8 01 00 00 00       	mov    $0x1,%eax
      thread_data[j].thread_index = j;
      thread_data[j].reader_index = receiver_index;
    1368:	8d 50 ff             	lea    -0x1(%rax),%edx
      thread_data[j].thread_index = j;
    136b:	89 45 00             	mov    %eax,0x0(%rbp)
    136e:	89 c6                	mov    %eax,%esi
      thread_data[j].cpu_set = receivercpu;
      thread_data[j].running = 1;
    1370:	c7 85 10 01 00 00 01 00 00 00 	movl   $0x1,0x110(%rbp)
      thread_data[j].reader_index = receiver_index;
    137a:	89 95 8c 01 00 00    	mov    %edx,0x18c(%rbp)
      thread_data[j].cpu_set = receivercpu;
    1380:	4c 89 b5 18 01 00 00 	mov    %r14,0x118(%rbp)
      thread_data[j].mode = READER;
    1387:	c7 85 04 01 00 00 01 00 00 00 	movl   $0x1,0x104(%rbp)
      if (j == receiver) {
    1391:	48 83 f8 01          	cmp    $0x1,%rax
    1395:	0f 84 9e 02 00 00    	je     1639 <main+0x479>
        for (int n = 0 ; n < buffer_size ; n++) {
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
        }
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
    139b:	66 0f 6f 1c 24       	movdqa (%rsp),%xmm3
    13a0:	45 31 c0             	xor    %r8d,%r8d
    13a3:	b9 01 00 00 00       	mov    $0x1,%ecx
    13a8:	89 f2                	mov    %esi,%edx
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    13aa:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    13b1:	48 8d 35 a0 0c 00 00 	lea    0xca0(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
    13b8:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].size = buffer_size;
    13bd:	48 c7 85 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%rbp)
      thread_data[j].sender = &thread_data[sender];
    13c8:	0f 11 5d 08          	movups %xmm3,0x8(%rbp)
      thread_data[j].readers = thread_data[sender].readers;
    13cc:	48 89 85 80 01 00 00 	mov    %rax,0x180(%rbp)
      thread_data[j].start = 0;
    13d3:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    13dd:	48 89 68 08          	mov    %rbp,0x8(%rax)
    13e1:	31 c0                	xor    %eax,%eax
    13e3:	e8 88 fd ff ff       	call   1170 <__printf_chk@plt>
    13e8:	31 d2                	xor    %edx,%edx
    13ea:	48 8d 35 f2 0c 00 00 	lea    0xcf2(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    13f1:	31 c0                	xor    %eax,%eax
    13f3:	bf 01 00 00 00       	mov    $0x1,%edi
    13f8:	e8 73 fd ff ff       	call   1170 <__printf_chk@plt>
      printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
    }
    printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    13fd:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    1400:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    1405:	c7 44 24 2c 00 00 00 00 	movl   $0x0,0x2c(%rsp)
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1; 
    
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    140d:	4d 8d 65 08          	lea    0x8(%r13),%r12
  param.sched_priority = 0;
    1411:	41 be 01 00 00 00    	mov    $0x1,%r14d
    1417:	48 8d 68 38          	lea    0x38(%rax),%rbp
    141b:	48 8d 35 c1 0c 00 00 	lea    0xcc1(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    1422:	bf 01 00 00 00       	mov    $0x1,%edi
    1427:	31 c0                	xor    %eax,%eax
    1429:	44 89 f2             	mov    %r14d,%edx
    142c:	e8 3f fd ff ff       	call   1170 <__printf_chk@plt>
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    1431:	31 f6                	xor    %esi,%esi
    1433:	48 89 ef             	mov    %rbp,%rdi
    1436:	e8 15 fd ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    143b:	85 c0                	test   %eax,%eax
    143d:	0f 85 9c 02 00 00    	jne    16df <main+0x51f>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    1443:	48 8d 74 24 2c       	lea    0x2c(%rsp),%rsi
    1448:	48 89 ef             	mov    %rbp,%rdi
    144b:	e8 40 fd ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1450:	85 c0                	test   %eax,%eax
    1452:	0f 85 a2 02 00 00    	jne    16fa <main+0x53a>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1458:	4c 89 f1             	mov    %r14,%rcx
    145b:	48 89 ee             	mov    %rbp,%rsi
    145e:	4c 89 e7             	mov    %r12,%rdi
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    1461:	48 83 c5 38          	add    $0x38,%rbp
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1465:	48 c1 e1 09          	shl    $0x9,%rcx
    1469:	48 8d 15 90 03 00 00 	lea    0x390(%rip),%rdx        # 1800 <disruptor_thread>
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    1470:	49 83 c4 08          	add    $0x8,%r12
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1474:	48 01 d9             	add    %rbx,%rcx
    1477:	e8 04 fd ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    147c:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
    1481:	be 08 00 00 00       	mov    $0x8,%esi
    1486:	48 8b 93 18 03 00 00 	mov    0x318(%rbx),%rdx
    148d:	e8 6e fc ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    1492:	49 83 fe 01          	cmp    $0x1,%r14
    1496:	75 0b                	jne    14a3 <main+0x2e3>
    1498:	41 be 02 00 00 00    	mov    $0x2,%r14d
    149e:	e9 78 ff ff ff       	jmp    141b <main+0x25b>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    14a3:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    14a8:	31 f6                	xor    %esi,%esi
    14aa:	4c 89 f7             	mov    %r14,%rdi
    14ad:	e8 9e fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    14b2:	85 c0                	test   %eax,%eax
    14b4:	0f 85 25 02 00 00    	jne    16df <main+0x51f>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    14ba:	48 8d 74 24 28       	lea    0x28(%rsp),%rsi
    14bf:	4c 89 f7             	mov    %r14,%rdi
      param2.sched_priority = 0;
    14c2:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    14ca:	e8 c1 fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    14cf:	85 c0                	test   %eax,%eax
    14d1:	0f 85 23 02 00 00    	jne    16fa <main+0x53a>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    14d7:	48 89 d9             	mov    %rbx,%rcx
    14da:	48 8d 15 1f 03 00 00 	lea    0x31f(%rip),%rdx        # 1800 <disruptor_thread>
    14e1:	4c 89 f6             	mov    %r14,%rsi
    14e4:	4c 89 ef             	mov    %r13,%rdi
    14e7:	e8 94 fc ff ff       	call   1180 <pthread_create@plt>
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    14ec:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    14f0:	be 08 00 00 00       	mov    $0x8,%esi
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + 1; 
    pthread_join(thread[sender], res1);
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    14f5:	31 ed                	xor    %ebp,%ebp
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    14f7:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
    14fe:	4c 8d 25 65 0c 00 00 	lea    0xc65(%rip),%r12        # 216a <_IO_stdin_used+0x16a>
    1505:	e8 f6 fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
  struct timespec preempt = {
    150a:	66 0f 6f 05 7e 0c 00 00 	movdqa 0xc7e(%rip),%xmm0        # 2190 <_IO_stdin_used+0x190>
    1512:	ba 0a 00 00 00       	mov    $0xa,%edx
    1517:	31 c0                	xor    %eax,%eax
    1519:	48 8d 35 1b 0c 00 00 	lea    0xc1b(%rip),%rsi        # 213b <_IO_stdin_used+0x13b>
    1520:	bf 01 00 00 00       	mov    $0x1,%edi
    1525:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    152a:	e8 41 fc ff ff       	call   1170 <__printf_chk@plt>
  nanosleep(&preempt , &rem2);
    152f:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    1534:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    1539:	e8 02 fc ff ff       	call   1140 <nanosleep@plt>
    pthread_join(thread[sender], res1);
    153e:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    1542:	31 f6                	xor    %esi,%esi
    thread_data[sender].running = 0;
    1544:	c7 83 10 01 00 00 00 00 00 00 	movl   $0x0,0x110(%rbx)
      thread_data[j].running = 0;
    154e:	c7 83 10 03 00 00 00 00 00 00 	movl   $0x0,0x310(%rbx)
    1558:	c7 83 10 05 00 00 00 00 00 00 	movl   $0x0,0x510(%rbx)
    pthread_join(thread[sender], res1);
    1562:	e8 49 fc ff ff       	call   11b0 <pthread_join@plt>
      pthread_join(thread[j], res2);
    1567:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    156b:	48 89 ee             	mov    %rbp,%rsi
    156e:	e8 3d fc ff ff       	call   11b0 <pthread_join@plt>
    1573:	49 8b 7d 10          	mov    0x10(%r13),%rdi
    1577:	48 89 ee             	mov    %rbp,%rsi
    157a:	e8 31 fc ff ff       	call   11b0 <pthread_join@plt>
    157f:	ba 01 00 00 00       	mov    $0x1,%edx
    1584:	48 8d 35 c9 0b 00 00 	lea    0xbc9(%rip),%rsi        # 2154 <_IO_stdin_used+0x154>
    158b:	31 c0                	xor    %eax,%eax
    158d:	bf 01 00 00 00       	mov    $0x1,%edi
    1592:	e8 d9 fb ff ff       	call   1170 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1;
    int incompletes = 0;
    printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    1597:	eb 17                	jmp    15b0 <main+0x3f0>
    1599:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    15a0:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    15a7:	48 81 fd 00 00 00 18 	cmp    $0x18000000,%rbp
    15ae:	74 4f                	je     15ff <main+0x43f>
      int compcount = 0;
      for (int n = 0 ; n < 2 ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    15b0:	48 8b 43 18          	mov    0x18(%rbx),%rax
    15b4:	48 01 e8             	add    %rbp,%rax
    15b7:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
    15be:	83 3a 01             	cmpl   $0x1,(%rdx)
    15c1:	75 dd                	jne    15a0 <main+0x3e0>
    15c3:	83 7a 04 01          	cmpl   $0x1,0x4(%rdx)
    15c7:	75 d7                	jne    15a0 <main+0x3e0>
      if (compcount == 2) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
          struct timespec end = thread_data[sender].data[y].end;
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    15c9:	4c 8b 80 88 00 00 00 	mov    0x88(%rax),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    15d0:	48 8b 88 80 00 00 00 	mov    0x80(%rax),%rcx
    15d7:	31 d2                	xor    %edx,%edx
    15d9:	4c 89 e6             	mov    %r12,%rsi
    15dc:	48 2b 08             	sub    (%rax),%rcx
    15df:	4c 2b 40 08          	sub    0x8(%rax),%r8
    15e3:	31 c0                	xor    %eax,%eax
    15e5:	bf 01 00 00 00       	mov    $0x1,%edi
    15ea:	e8 81 fb ff ff       	call   1170 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    15ef:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    15f6:	48 81 fd 00 00 00 18 	cmp    $0x18000000,%rbp
    15fd:	75 b1                	jne    15b0 <main+0x3f0>
    15ff:	31 d2                	xor    %edx,%edx
    1601:	31 c0                	xor    %eax,%eax
    1603:	48 8d 35 74 0b 00 00 	lea    0xb74(%rip),%rsi        # 217e <_IO_stdin_used+0x17e>
    160a:	bf 01 00 00 00       	mov    $0x1,%edi
    160f:	e8 5c fb ff ff       	call   1170 <__printf_chk@plt>
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    1614:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    1619:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1622:	0f 85 cd 00 00 00    	jne    16f5 <main+0x535>
    1628:	48 83 c4 68          	add    $0x68,%rsp
    162c:	31 c0                	xor    %eax,%eax
    162e:	5b                   	pop    %rbx
    162f:	5d                   	pop    %rbp
    1630:	41 5c                	pop    %r12
    1632:	41 5d                	pop    %r13
    1634:	41 5e                	pop    %r14
    1636:	41 5f                	pop    %r15
    1638:	c3                   	ret
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    1639:	be 80 01 00 00       	mov    $0x180,%esi
    163e:	bf 00 00 10 00       	mov    $0x100000,%edi
    1643:	e8 18 fb ff ff       	call   1160 <calloc@plt>
    1648:	48 89 45 18          	mov    %rax,0x18(%rbp)
    164c:	49 89 c4             	mov    %rax,%r12
        for (int n = 0 ; n < buffer_size ; n++) {
    164f:	4c 8d b8 00 01 00 00 	lea    0x100(%rax),%r15
    1656:	49 81 c4 00 01 00 18 	add    $0x18000100,%r12
    165d:	0f 1f 00             	nopl   (%rax)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1660:	be 04 00 00 00       	mov    $0x4,%esi
    1665:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    166a:	49 81 c7 80 01 00 00 	add    $0x180,%r15
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1671:	e8 ea fa ff ff       	call   1160 <calloc@plt>
    1676:	49 89 87 80 fe ff ff 	mov    %rax,-0x180(%r15)
        for (int n = 0 ; n < buffer_size ; n++) {
    167d:	4d 39 fc             	cmp    %r15,%r12
    1680:	75 de                	jne    1660 <main+0x4a0>
      thread_data[j].sender = &thread_data[sender];
    1682:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
    1687:	45 31 c0             	xor    %r8d,%r8d
    168a:	31 c9                	xor    %ecx,%ecx
    168c:	ba 01 00 00 00       	mov    $0x1,%edx
      thread_data[j].readers = thread_data[sender].readers;
    1691:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    1698:	48 8d 35 b9 09 00 00 	lea    0x9b9(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
      thread_data[j].size = buffer_size;
    169f:	48 c7 85 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%rbp)
    16aa:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].start = 0;
    16af:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
      thread_data[j].readers = thread_data[sender].readers;
    16b9:	48 89 85 80 01 00 00 	mov    %rax,0x180(%rbp)
      thread_data[j].sender = &thread_data[sender];
    16c0:	0f 11 55 08          	movups %xmm2,0x8(%rbp)
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    16c4:	48 89 28             	mov    %rbp,(%rax)
    16c7:	31 c0                	xor    %eax,%eax
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    16c9:	48 81 c5 00 02 00 00 	add    $0x200,%rbp
    16d0:	e8 9b fa ff ff       	call   1170 <__printf_chk@plt>
    16d5:	b8 02 00 00 00       	mov    $0x2,%eax
    16da:	e9 89 fc ff ff       	jmp    1368 <main+0x1a8>
    16df:	48 8d 3d 1a 0a 00 00 	lea    0xa1a(%rip),%rdi        # 2100 <_IO_stdin_used+0x100>
    16e6:	e8 25 fa ff ff       	call   1110 <puts@plt>
               exit(1);
    16eb:	bf 01 00 00 00       	mov    $0x1,%edi
    16f0:	e8 ab fa ff ff       	call   11a0 <exit@plt>
}
    16f5:	e8 36 fa ff ff       	call   1130 <__stack_chk_fail@plt>
    16fa:	48 8d 3d 1d 0a 00 00 	lea    0xa1d(%rip),%rdi        # 211e <_IO_stdin_used+0x11e>
    1701:	e8 0a fa ff ff       	call   1110 <puts@plt>
              exit(1);
    1706:	bf 01 00 00 00       	mov    $0x1,%edi
    170b:	e8 90 fa ff ff       	call   11a0 <exit@plt>

0000000000001710 <_start>:
    1710:	f3 0f 1e fa          	endbr64
    1714:	31 ed                	xor    %ebp,%ebp
    1716:	49 89 d1             	mov    %rdx,%r9
    1719:	5e                   	pop    %rsi
    171a:	48 89 e2             	mov    %rsp,%rdx
    171d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1721:	50                   	push   %rax
    1722:	54                   	push   %rsp
    1723:	45 31 c0             	xor    %r8d,%r8d
    1726:	31 c9                	xor    %ecx,%ecx
    1728:	48 8d 3d 91 fa ff ff 	lea    -0x56f(%rip),%rdi        # 11c0 <main>
    172f:	ff 15 a3 28 00 00    	call   *0x28a3(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1735:	f4                   	hlt
    1736:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001740 <deregister_tm_clones>:
    1740:	48 8d 3d c9 28 00 00 	lea    0x28c9(%rip),%rdi        # 4010 <__TMC_END__>
    1747:	48 8d 05 c2 28 00 00 	lea    0x28c2(%rip),%rax        # 4010 <__TMC_END__>
    174e:	48 39 f8             	cmp    %rdi,%rax
    1751:	74 15                	je     1768 <deregister_tm_clones+0x28>
    1753:	48 8b 05 86 28 00 00 	mov    0x2886(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    175a:	48 85 c0             	test   %rax,%rax
    175d:	74 09                	je     1768 <deregister_tm_clones+0x28>
    175f:	ff e0                	jmp    *%rax
    1761:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1768:	c3                   	ret
    1769:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001770 <register_tm_clones>:
    1770:	48 8d 3d 99 28 00 00 	lea    0x2899(%rip),%rdi        # 4010 <__TMC_END__>
    1777:	48 8d 35 92 28 00 00 	lea    0x2892(%rip),%rsi        # 4010 <__TMC_END__>
    177e:	48 29 fe             	sub    %rdi,%rsi
    1781:	48 89 f0             	mov    %rsi,%rax
    1784:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1788:	48 c1 f8 03          	sar    $0x3,%rax
    178c:	48 01 c6             	add    %rax,%rsi
    178f:	48 d1 fe             	sar    %rsi
    1792:	74 14                	je     17a8 <register_tm_clones+0x38>
    1794:	48 8b 05 55 28 00 00 	mov    0x2855(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    179b:	48 85 c0             	test   %rax,%rax
    179e:	74 08                	je     17a8 <register_tm_clones+0x38>
    17a0:	ff e0                	jmp    *%rax
    17a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    17a8:	c3                   	ret
    17a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017b0 <__do_global_dtors_aux>:
    17b0:	f3 0f 1e fa          	endbr64
    17b4:	80 3d 55 28 00 00 00 	cmpb   $0x0,0x2855(%rip)        # 4010 <__TMC_END__>
    17bb:	75 2b                	jne    17e8 <__do_global_dtors_aux+0x38>
    17bd:	55                   	push   %rbp
    17be:	48 83 3d 32 28 00 00 00 	cmpq   $0x0,0x2832(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    17c6:	48 89 e5             	mov    %rsp,%rbp
    17c9:	74 0c                	je     17d7 <__do_global_dtors_aux+0x27>
    17cb:	48 8b 3d 36 28 00 00 	mov    0x2836(%rip),%rdi        # 4008 <__dso_handle>
    17d2:	e8 19 f9 ff ff       	call   10f0 <__cxa_finalize@plt>
    17d7:	e8 64 ff ff ff       	call   1740 <deregister_tm_clones>
    17dc:	c6 05 2d 28 00 00 01 	movb   $0x1,0x282d(%rip)        # 4010 <__TMC_END__>
    17e3:	5d                   	pop    %rbp
    17e4:	c3                   	ret
    17e5:	0f 1f 00             	nopl   (%rax)
    17e8:	c3                   	ret
    17e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017f0 <frame_dummy>:
    17f0:	f3 0f 1e fa          	endbr64
    17f4:	e9 77 ff ff ff       	jmp    1770 <register_tm_clones>
    17f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001800 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    1800:	f3 0f 1e fa          	endbr64
    1804:	41 55                	push   %r13
    1806:	48 8d 35 fb 07 00 00 	lea    0x7fb(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    180d:	31 c0                	xor    %eax,%eax
    180f:	41 54                	push   %r12
    1811:	55                   	push   %rbp
    1812:	53                   	push   %rbx
    1813:	48 89 fb             	mov    %rdi,%rbx
    1816:	48 83 ec 08          	sub    $0x8,%rsp
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    181a:	8b 8f 04 01 00 00    	mov    0x104(%rdi),%ecx
    1820:	8b 17                	mov    (%rdi),%edx
    1822:	bf 01 00 00 00       	mov    $0x1,%edi
    1827:	e8 44 f9 ff ff       	call   1170 <__printf_chk@plt>
  if (data->mode == WRITER) {
    182c:	8b 83 04 01 00 00    	mov    0x104(%rbx),%eax
    1832:	85 c0                	test   %eax,%eax
    1834:	74 3a                	je     1870 <disruptor_thread+0x70>
  } else if (data->mode == READER) {
    1836:	8b 83 04 01 00 00    	mov    0x104(%rbx),%eax
    183c:	83 f8 01             	cmp    $0x1,%eax
    183f:	0f 84 bb 00 00 00    	je     1900 <disruptor_thread+0x100>
  printf("Finished %d\n", data->mode);
    1845:	8b 93 04 01 00 00    	mov    0x104(%rbx),%edx
    184b:	48 8d 35 3f 08 00 00 	lea    0x83f(%rip),%rsi        # 2091 <_IO_stdin_used+0x91>
    1852:	bf 01 00 00 00       	mov    $0x1,%edi
    1857:	31 c0                	xor    %eax,%eax
    1859:	e8 12 f9 ff ff       	call   1170 <__printf_chk@plt>
}
    185e:	48 83 c4 08          	add    $0x8,%rsp
    1862:	31 c0                	xor    %eax,%eax
    1864:	5b                   	pop    %rbx
    1865:	5d                   	pop    %rbp
    1866:	41 5c                	pop    %r12
    1868:	41 5d                	pop    %r13
    186a:	c3                   	ret
    186b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    1870:	48 8d 3d 0e 08 00 00 	lea    0x80e(%rip),%rdi        # 2085 <_IO_stdin_used+0x85>
    1877:	e8 94 f8 ff ff       	call   1110 <puts@plt>
    struct Thread *me = data->sender;
    187c:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    while (data->running == 1) {
    1880:	8b 83 10 01 00 00    	mov    0x110(%rbx),%eax
    1886:	83 f8 01             	cmp    $0x1,%eax
    1889:	75 ba                	jne    1845 <disruptor_thread+0x45>
      asm volatile ("sfence" ::: "memory");
    188b:	0f ae f8             	sfence
        if ((data->end + 1) % me->size == me->start) {
    188e:	8b 83 00 01 00 00    	mov    0x100(%rbx),%eax
    1894:	48 8b 8d 08 01 00 00 	mov    0x108(%rbp),%rcx
    189b:	83 c0 01             	add    $0x1,%eax
    189e:	48 98                	cltq
    18a0:	48 99                	cqto
    18a2:	48 f7 f9             	idiv   %rcx
    18a5:	48 63 85 80 00 00 00 	movslq 0x80(%rbp),%rax
    18ac:	48 39 c2             	cmp    %rax,%rdx
    18af:	74 cf                	je     1880 <disruptor_thread+0x80>
            int changed = me->end;
    18b1:	48 63 b5 00 01 00 00 	movslq 0x100(%rbp),%rsi
            while (!__sync_bool_compare_and_swap(&me->end, changed, (changed + 1) % me->size)) {
    18b8:	8d 46 01             	lea    0x1(%rsi),%eax
    18bb:	48 98                	cltq
    18bd:	48 99                	cqto
    18bf:	48 f7 f9             	idiv   %rcx
    18c2:	89 f0                	mov    %esi,%eax
    18c4:	f0 0f b1 95 00 01 00 00 	lock cmpxchg %edx,0x100(%rbp)
    18cc:	0f 85 ab 00 00 00    	jne    197d <disruptor_thread+0x17d>
            clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    18d2:	4c 8d 24 76          	lea    (%rsi,%rsi,2),%r12
    18d6:	48 8b 75 18          	mov    0x18(%rbp),%rsi
    18da:	bf 04 00 00 00       	mov    $0x4,%edi
    18df:	49 c1 e4 07          	shl    $0x7,%r12
    18e3:	4c 01 e6             	add    %r12,%rsi
    18e6:	e8 35 f8 ff ff       	call   1120 <clock_gettime@plt>
            me->data[changed].complete[1] = 1;
    18eb:	48 8b 45 18          	mov    0x18(%rbp),%rax
    18ef:	4a 8b 84 20 00 01 00 00 	mov    0x100(%rax,%r12,1),%rax
    18f7:	c7 40 04 01 00 00 00 	movl   $0x1,0x4(%rax)
    18fe:	eb 80                	jmp    1880 <disruptor_thread+0x80>
    1900:	48 8d 3d 97 07 00 00 	lea    0x797(%rip),%rdi        # 209e <_IO_stdin_used+0x9e>
    1907:	e8 04 f8 ff ff       	call   1110 <puts@plt>
    struct Thread *sender = data->sender;
    190c:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    struct Snapshot * rdata = sender->data;
    1910:	4c 8b 6d 18          	mov    0x18(%rbp),%r13
    while (data->running == 1) {
    1914:	0f 1f 40 00          	nopl   0x0(%rax)
    1918:	8b 83 10 01 00 00    	mov    0x110(%rbx),%eax
    191e:	83 f8 01             	cmp    $0x1,%eax
    1921:	0f 85 1e ff ff ff    	jne    1845 <disruptor_thread+0x45>
      if (sender->end == sender->start) {
    1927:	48 63 8d 80 00 00 00 	movslq 0x80(%rbp),%rcx
    192e:	39 8d 00 01 00 00    	cmp    %ecx,0x100(%rbp)
    1934:	74 e2                	je     1918 <disruptor_thread+0x118>
          if (__sync_bool_compare_and_swap(&sender->start, changed, (changed + 1) % sender->size)) {
    1936:	8d 41 01             	lea    0x1(%rcx),%eax
    1939:	48 98                	cltq
    193b:	48 99                	cqto
    193d:	48 f7 bd 08 01 00 00 	idivq  0x108(%rbp)
    1944:	89 c8                	mov    %ecx,%eax
    1946:	f0 0f b1 95 80 00 00 00 	lock cmpxchg %edx,0x80(%rbp)
    194e:	75 c8                	jne    1918 <disruptor_thread+0x118>
            clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end);
    1950:	4c 8d 24 49          	lea    (%rcx,%rcx,2),%r12
    1954:	bf 04 00 00 00       	mov    $0x4,%edi
    1959:	49 c1 e4 07          	shl    $0x7,%r12
    195d:	4d 01 ec             	add    %r13,%r12
    1960:	49 8d b4 24 80 00 00 00 	lea    0x80(%r12),%rsi
    1968:	e8 b3 f7 ff ff       	call   1120 <clock_gettime@plt>
            rdata[changed].complete[0] = 1;
    196d:	49 8b 84 24 00 01 00 00 	mov    0x100(%r12),%rax
    1975:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
            cachedEnd = sender->end;
    197b:	eb 9b                	jmp    1918 <disruptor_thread+0x118>
              changed = me->end;
    197d:	48 63 b5 00 01 00 00 	movslq 0x100(%rbp),%rsi
            while (!__sync_bool_compare_and_swap(&me->end, changed, (changed + 1) % me->size)) {
    1984:	48 8b 8d 08 01 00 00 	mov    0x108(%rbp),%rcx
    198b:	e9 28 ff ff ff       	jmp    18b8 <disruptor_thread+0xb8>

0000000000001990 <min>:
int min(long a, long b) {
    1990:	f3 0f 1e fa          	endbr64
  if (a < b) return a;
    1994:	48 39 f7             	cmp    %rsi,%rdi
    1997:	7c 02                	jl     199b <min+0xb>
  if (b < a) return b;
    1999:	7f 05                	jg     19a0 <min+0x10>
  if (a < b) return a;
    199b:	89 f8                	mov    %edi,%eax
    199d:	c3                   	ret
    199e:	66 90                	xchg   %ax,%ax
  if (b < a) return b;
    19a0:	89 f0                	mov    %esi,%eax
}
    19a2:	c3                   	ret

Disassembly of section .fini:

00000000000019a4 <_fini>:
    19a4:	f3 0f 1e fa          	endbr64
    19a8:	48 83 ec 08          	sub    $0x8,%rsp
    19ac:	48 83 c4 08          	add    $0x8,%rsp
    19b0:	c3                   	ret
