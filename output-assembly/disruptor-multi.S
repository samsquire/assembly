
disruptor-multi:     file format elf64-x86-64


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
  printf("Finished\n");
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
    11e4:	48 83 ec 58          	sub    $0x58,%rsp
    11e8:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    11f1:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    11f6:	31 c0                	xor    %eax,%eax
    11f8:	e8 73 ff ff ff       	call   1170 <__printf_chk@plt>
    11fd:	ba 01 00 00 00       	mov    $0x1,%edx
    1202:	48 8d 35 87 0e 00 00 	lea    0xe87(%rip),%rsi        # 2090 <_IO_stdin_used+0x90>
    1209:	31 c0                	xor    %eax,%eax
    120b:	bf 01 00 00 00       	mov    $0x1,%edi
    1210:	e8 5b ff ff ff       	call   1170 <__printf_chk@plt>
    1215:	ba 02 00 00 00       	mov    $0x2,%edx
    121a:	48 8d 35 7f 0e 00 00 	lea    0xe7f(%rip),%rsi        # 20a0 <_IO_stdin_used+0xa0>
    1221:	31 c0                	xor    %eax,%eax
    1223:	bf 01 00 00 00       	mov    $0x1,%edi
    1228:	e8 43 ff ff ff       	call   1170 <__printf_chk@plt>
    122d:	ba 03 00 00 00       	mov    $0x3,%edx
    1232:	48 8d 35 79 0e 00 00 	lea    0xe79(%rip),%rsi        # 20b2 <_IO_stdin_used+0xb2>
    1239:	31 c0                	xor    %eax,%eax
    123b:	bf 01 00 00 00       	mov    $0x1,%edi
    1240:	e8 2b ff ff ff       	call   1170 <__printf_chk@plt>
  int readers_count = 2;
  int group_size = writers_count + readers_count;
  printf("Readers count %d\n", readers_count);
  int thread_count = groups * (readers_count + writers_count);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1245:	be 00 02 00 00       	mov    $0x200,%esi
    124a:	bf 03 00 00 00       	mov    $0x3,%edi
    124f:	e8 0c ff ff ff       	call   1160 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1254:	be 38 00 00 00       	mov    $0x38,%esi
    1259:	bf 03 00 00 00       	mov    $0x3,%edi
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    125e:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1261:	e8 fa fe ff ff       	call   1160 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1266:	be 08 00 00 00       	mov    $0x8,%esi
    126b:	bf 03 00 00 00       	mov    $0x3,%edi
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1270:	49 89 c7             	mov    %rax,%r15
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1273:	e8 e8 fe ff ff       	call   1160 <calloc@plt>
  // 0, 3, 6
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1; 
    int receiver2 = receiver + 1; 
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1278:	be 80 00 00 00       	mov    $0x80,%esi
    127d:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1282:	49 89 c4             	mov    %rax,%r12
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1285:	e8 d6 fe ff ff       	call   1160 <calloc@plt>
    CPU_ZERO(sendercpu);
    for (int j = 0 ; j < cores ; j++) {
      // printf("assigning sender %d to core %d\n", sender, j);
      CPU_SET(j, sendercpu);
    }
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    128a:	be 80 00 00 00       	mov    $0x80,%esi
    128f:	bf 01 00 00 00       	mov    $0x1,%edi
      CPU_SET(j, sendercpu);
    1294:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    129b:	48 89 c5             	mov    %rax,%rbp
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    129e:	e8 bd fe ff ff       	call   1160 <calloc@plt>
    for (int j = 0; j < cores ; j++) {
      // printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    }
     
    thread_data[sender].thread_index = sender;
    12a3:	c7 03 00 00 00 00    	movl   $0x0,(%rbx)
    thread_data[sender].cpu_set = sendercpu;
    thread_data[sender].mode = WRITER;
    thread_data[sender].running = 1;
    thread_data[sender].size = buffer_size;
    thread_data[sender].end = 0;
    thread_data[sender].readers = calloc(readers_count, sizeof(struct Thread*));
    12a9:	be 08 00 00 00       	mov    $0x8,%esi
    12ae:	bf 02 00 00 00       	mov    $0x2,%edi
      CPU_SET(j, receivercpu);
    12b3:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12ba:	49 89 c5             	mov    %rax,%r13
    thread_data[sender].mode = WRITER;
    12bd:	c7 83 04 01 00 00 00 00 00 00 	movl   $0x0,0x104(%rbx)
    thread_data[sender].cpu_set = sendercpu;
    12c7:	48 89 ab 18 01 00 00 	mov    %rbp,0x118(%rbx)
    thread_data[sender].running = 1;
    12ce:	c7 83 10 01 00 00 01 00 00 00 	movl   $0x1,0x110(%rbx)
    thread_data[sender].size = buffer_size;
    12d8:	48 c7 83 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%rbx)
    thread_data[sender].end = 0;
    12e3:	c7 83 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbx)
    thread_data[sender].readers = calloc(readers_count, sizeof(struct Thread*));
    12ed:	e8 6e fe ff ff       	call   1160 <calloc@plt>
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    12f2:	be 80 01 00 00       	mov    $0x180,%esi
    12f7:	bf 00 00 10 00       	mov    $0x100000,%edi
    thread_data[sender].readers = calloc(readers_count, sizeof(struct Thread*));
    12fc:	48 89 83 80 01 00 00 	mov    %rax,0x180(%rbx)
    1303:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    1308:	e8 53 fe ff ff       	call   1160 <calloc@plt>
    130d:	48 89 43 10          	mov    %rax,0x10(%rbx)
    1311:	48 89 c5             	mov    %rax,%rbp
    for (int n = 0 ; n < buffer_size ; n++) {
    1314:	4c 8d b0 80 00 00 00 	lea    0x80(%rax),%r14
    131b:	48 81 c5 80 00 00 18 	add    $0x18000080,%rbp
    1322:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      thread_data[sender].data[n].end = calloc(readers_count, sizeof(struct timespec));
    1328:	be 10 00 00 00       	mov    $0x10,%esi
    132d:	bf 02 00 00 00       	mov    $0x2,%edi
    for (int n = 0 ; n < buffer_size ; n++) {
    1332:	49 81 c6 80 01 00 00 	add    $0x180,%r14
      thread_data[sender].data[n].end = calloc(readers_count, sizeof(struct timespec));
    1339:	e8 22 fe ff ff       	call   1160 <calloc@plt>
      thread_data[sender].data[n].complete = calloc(readers_count, sizeof(int));
    133e:	be 04 00 00 00       	mov    $0x4,%esi
    1343:	bf 02 00 00 00       	mov    $0x2,%edi
      thread_data[sender].data[n].end = calloc(readers_count, sizeof(struct timespec));
    1348:	49 89 86 80 fe ff ff 	mov    %rax,-0x180(%r14)
      thread_data[sender].data[n].complete = calloc(readers_count, sizeof(int));
    134f:	e8 0c fe ff ff       	call   1160 <calloc@plt>
    1354:	49 89 86 00 ff ff ff 	mov    %rax,-0x100(%r14)
    for (int n = 0 ; n < buffer_size ; n++) {
    135b:	49 39 ee             	cmp    %rbp,%r14
    135e:	75 c8                	jne    1328 <main+0x168>
    }
    thread_data[sender].readers_count = readers_count;
    // printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
      thread_data[j].thread_index = j;
    1360:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    1365:	45 31 c0             	xor    %r8d,%r8d
    1368:	48 8d 83 00 02 00 00 	lea    0x200(%rbx),%rax
      thread_data[j].reader_index = receiver_index;
      thread_data[j].cpu_set = receivercpu;
      thread_data[j].running = 1;
    136f:	c7 83 10 03 00 00 01 00 00 00 	movl   $0x1,0x310(%rbx)
    thread_data[sender].readers_count = readers_count;
    1379:	c7 83 88 01 00 00 02 00 00 00 	movl   $0x2,0x188(%rbx)
    1383:	48 8d 2d ce 0c 00 00 	lea    0xcce(%rip),%rbp        # 2058 <_IO_stdin_used+0x58>
    138a:	ba 01 00 00 00       	mov    $0x1,%edx
    138f:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].mode = READER;
    1394:	c7 83 04 03 00 00 01 00 00 00 	movl   $0x1,0x304(%rbx)
    139e:	48 89 ee             	mov    %rbp,%rsi
      thread_data[j].thread_index = j;
    13a1:	48 89 01             	mov    %rax,(%rcx)
    13a4:	31 c9                	xor    %ecx,%ecx
    13a6:	31 c0                	xor    %eax,%eax
    13a8:	c7 83 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rbx)
      thread_data[j].reader_index = receiver_index;
    13b2:	c7 83 8c 03 00 00 00 00 00 00 	movl   $0x0,0x38c(%rbx)
      thread_data[j].cpu_set = receivercpu;
    13bc:	4c 89 ab 18 03 00 00 	mov    %r13,0x318(%rbx)
      thread_data[j].size = buffer_size;
    13c3:	48 c7 83 08 03 00 00 00 00 10 00 	movq   $0x100000,0x308(%rbx)
      thread_data[j].sender = &thread_data[sender];
    13ce:	48 89 9b 08 02 00 00 	mov    %rbx,0x208(%rbx)
      thread_data[j].start = 0;
    13d5:	c7 83 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rbx)
    13df:	e8 8c fd ff ff       	call   1170 <__printf_chk@plt>
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    13e4:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    13eb:	45 31 c0             	xor    %r8d,%r8d
      thread_data[j].thread_index = j;
    13ee:	48 8d 93 00 04 00 00 	lea    0x400(%rbx),%rdx
      thread_data[j].cpu_set = receivercpu;
    13f5:	4c 89 ab 18 05 00 00 	mov    %r13,0x518(%rbx)
    13fc:	b9 01 00 00 00       	mov    $0x1,%ecx
    1401:	48 89 ee             	mov    %rbp,%rsi
    1404:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].running = 1;
    1409:	c7 83 10 05 00 00 01 00 00 00 	movl   $0x1,0x510(%rbx)
      thread_data[j].thread_index = j;
    1413:	c7 83 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%rbx)
      thread_data[j].mode = READER;
    141d:	c7 83 04 05 00 00 01 00 00 00 	movl   $0x1,0x504(%rbx)
      thread_data[j].reader_index = receiver_index;
    1427:	c7 83 8c 05 00 00 01 00 00 00 	movl   $0x1,0x58c(%rbx)
      thread_data[j].size = buffer_size;
    1431:	48 c7 83 08 05 00 00 00 00 10 00 	movq   $0x100000,0x508(%rbx)
      thread_data[j].sender = &thread_data[sender];
    143c:	48 89 9b 08 04 00 00 	mov    %rbx,0x408(%rbx)
      thread_data[j].start = 0;
    1443:	c7 83 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rbx)
      thread_data[j].thread_index = j;
    144d:	48 89 50 08          	mov    %rdx,0x8(%rax)
    1451:	ba 02 00 00 00       	mov    $0x2,%edx
    1456:	31 c0                	xor    %eax,%eax
    1458:	e8 13 fd ff ff       	call   1170 <__printf_chk@plt>
    145d:	31 d2                	xor    %edx,%edx
    145f:	48 8d 35 63 0c 00 00 	lea    0xc63(%rip),%rsi        # 20c9 <_IO_stdin_used+0xc9>
    1466:	31 c0                	xor    %eax,%eax
    1468:	bf 01 00 00 00       	mov    $0x1,%edi
    146d:	e8 fe fc ff ff       	call   1170 <__printf_chk@plt>
      printf("Setting up receiver thread %d %d to sender %d\n", j, receiver_index, sender);
    }
    printf("Creating sender thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    1472:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    1475:	41 be 01 00 00 00    	mov    $0x1,%r14d
    147b:	49 8d 6f 38          	lea    0x38(%r15),%rbp
    147f:	4d 8d 6c 24 08       	lea    0x8(%r12),%r13
    1484:	c7 44 24 1c 00 00 00 00 	movl   $0x0,0x1c(%rsp)
    148c:	48 8d 35 51 0c 00 00 	lea    0xc51(%rip),%rsi        # 20e4 <_IO_stdin_used+0xe4>
    1493:	bf 01 00 00 00       	mov    $0x1,%edi
    1498:	31 c0                	xor    %eax,%eax
    149a:	44 89 f2             	mov    %r14d,%edx
    149d:	e8 ce fc ff ff       	call   1170 <__printf_chk@plt>
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    14a2:	31 f6                	xor    %esi,%esi
    14a4:	48 89 ef             	mov    %rbp,%rdi
    14a7:	e8 a4 fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    14ac:	85 c0                	test   %eax,%eax
    14ae:	0f 85 2a 02 00 00    	jne    16de <main+0x51e>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    14b4:	48 8d 74 24 1c       	lea    0x1c(%rsp),%rsi
    14b9:	48 89 ef             	mov    %rbp,%rdi
    14bc:	e8 cf fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    14c1:	85 c0                	test   %eax,%eax
    14c3:	0f 85 30 02 00 00    	jne    16f9 <main+0x539>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    14c9:	4c 89 f1             	mov    %r14,%rcx
    14cc:	48 89 ee             	mov    %rbp,%rsi
    14cf:	4c 89 ef             	mov    %r13,%rdi
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
    14d2:	48 83 c5 38          	add    $0x38,%rbp
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    14d6:	48 c1 e1 09          	shl    $0x9,%rcx
    14da:	48 8d 15 1f 03 00 00 	lea    0x31f(%rip),%rdx        # 1800 <disruptor_thread>
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
    14e1:	49 83 c5 08          	add    $0x8,%r13
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    14e5:	48 01 d9             	add    %rbx,%rcx
    14e8:	e8 93 fc ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    14ed:	49 8b 7d f8          	mov    -0x8(%r13),%rdi
    14f1:	be 08 00 00 00       	mov    $0x8,%esi
    14f6:	48 8b 93 18 03 00 00 	mov    0x318(%rbx),%rdx
    14fd:	e8 fe fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
    1502:	49 83 fe 01          	cmp    $0x1,%r14
    1506:	75 0b                	jne    1513 <main+0x353>
    1508:	41 be 02 00 00 00    	mov    $0x2,%r14d
    150e:	e9 79 ff ff ff       	jmp    148c <main+0x2cc>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    1513:	31 f6                	xor    %esi,%esi
    1515:	4c 89 ff             	mov    %r15,%rdi
    1518:	e8 33 fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    151d:	85 c0                	test   %eax,%eax
    151f:	0f 85 b9 01 00 00    	jne    16de <main+0x51e>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1525:	48 8d 74 24 18       	lea    0x18(%rsp),%rsi
    152a:	4c 89 ff             	mov    %r15,%rdi
      param2.sched_priority = 0;
    152d:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1535:	e8 56 fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    153a:	85 c0                	test   %eax,%eax
    153c:	0f 85 b7 01 00 00    	jne    16f9 <main+0x539>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    1542:	48 89 d9             	mov    %rbx,%rcx
    1545:	4c 89 e7             	mov    %r12,%rdi
    1548:	48 8d 15 b1 02 00 00 	lea    0x2b1(%rip),%rdx        # 1800 <disruptor_thread>
    154f:	4c 89 fe             	mov    %r15,%rsi
    1552:	e8 29 fc ff ff       	call   1180 <pthread_create@plt>
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    1557:	49 8b 3c 24          	mov    (%r12),%rdi
    155b:	be 08 00 00 00       	mov    $0x8,%esi
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + 1; 
    pthread_join(thread[sender], res1);
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    1560:	31 ed                	xor    %ebp,%ebp
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    1562:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
    1569:	e8 92 fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
  struct timespec preempt = {
    156e:	66 0f 6f 05 2a 0c 00 00 	movdqa 0xc2a(%rip),%xmm0        # 21a0 <_IO_stdin_used+0x1a0>
    1576:	ba 0a 00 00 00       	mov    $0xa,%edx
    157b:	31 c0                	xor    %eax,%eax
    157d:	48 8d 35 b8 0b 00 00 	lea    0xbb8(%rip),%rsi        # 213c <_IO_stdin_used+0x13c>
    1584:	bf 01 00 00 00       	mov    $0x1,%edi
    1589:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    158e:	e8 dd fb ff ff       	call   1170 <__printf_chk@plt>
  nanosleep(&preempt , &rem2);
    1593:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    1598:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    159d:	e8 9e fb ff ff       	call   1140 <nanosleep@plt>
    pthread_join(thread[sender], res1);
    15a2:	49 8b 3c 24          	mov    (%r12),%rdi
    15a6:	31 f6                	xor    %esi,%esi
    thread_data[sender].running = 0;
    15a8:	c7 83 10 01 00 00 00 00 00 00 	movl   $0x0,0x110(%rbx)
      thread_data[j].running = 0;
    15b2:	c7 83 10 03 00 00 00 00 00 00 	movl   $0x0,0x310(%rbx)
    15bc:	c7 83 10 05 00 00 00 00 00 00 	movl   $0x0,0x510(%rbx)
    pthread_join(thread[sender], res1);
    15c6:	e8 e5 fb ff ff       	call   11b0 <pthread_join@plt>
      pthread_join(thread[j], res2);
    15cb:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    15d0:	48 89 ee             	mov    %rbp,%rsi
    15d3:	e8 d8 fb ff ff       	call   11b0 <pthread_join@plt>
    15d8:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    15dd:	48 89 ee             	mov    %rbp,%rsi
    15e0:	4c 8d 25 84 0b 00 00 	lea    0xb84(%rip),%r12        # 216b <_IO_stdin_used+0x16b>
    15e7:	e8 c4 fb ff ff       	call   11b0 <pthread_join@plt>
    15ec:	31 d2                	xor    %edx,%edx
    15ee:	48 8d 35 60 0b 00 00 	lea    0xb60(%rip),%rsi        # 2155 <_IO_stdin_used+0x155>
    15f5:	31 c0                	xor    %eax,%eax
    15f7:	bf 01 00 00 00       	mov    $0x1,%edi
    15fc:	e8 6f fb ff ff       	call   1170 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1;
    int incompletes = 0;
    printf("Inspecting sender %d\n", sender);
    for (int y = 0 ; y < buffer_size; y++) {
    1601:	eb 19                	jmp    161c <main+0x45c>
    1603:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    1608:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    160f:	48 81 fd 00 00 00 18 	cmp    $0x18000000,%rbp
    1616:	0f 84 8c 00 00 00    	je     16a8 <main+0x4e8>
      int compcount = 0;
      for (int n = 0 ; n < readers_count ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    161c:	48 8b 53 10          	mov    0x10(%rbx),%rdx
    1620:	48 01 ea             	add    %rbp,%rdx
    1623:	48 8b 82 00 01 00 00 	mov    0x100(%rdx),%rax
    162a:	8b 08                	mov    (%rax),%ecx
    162c:	8b 40 04             	mov    0x4(%rax),%eax
    162f:	83 f9 01             	cmp    $0x1,%ecx
    1632:	75 d4                	jne    1608 <main+0x448>
    1634:	83 f8 01             	cmp    $0x1,%eax
    1637:	75 cf                	jne    1608 <main+0x448>
      }
      if (compcount == readers_count) {
        for (int n = 0 ; n < readers_count ; n++) {
            // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
            struct timespec start = thread_data[sender].data[y].start;
            struct timespec end = thread_data[sender].data[y].end[n];
    1639:	48 8b 82 80 00 00 00 	mov    0x80(%rdx),%rax
    1640:	31 c9                	xor    %ecx,%ecx
    1642:	4c 89 e6             	mov    %r12,%rsi
    1645:	bf 01 00 00 00       	mov    $0x1,%edi
            const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
            const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    164a:	4c 8b 48 08          	mov    0x8(%rax),%r9
            const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    164e:	4c 8b 00             	mov    (%rax),%r8
    1651:	31 c0                	xor    %eax,%eax
    1653:	4c 2b 4a 08          	sub    0x8(%rdx),%r9
    1657:	4c 2b 02             	sub    (%rdx),%r8
    165a:	31 d2                	xor    %edx,%edx
    165c:	e8 0f fb ff ff       	call   1170 <__printf_chk@plt>
            struct timespec start = thread_data[sender].data[y].start;
    1661:	48 8b 43 10          	mov    0x10(%rbx),%rax
    1665:	b9 01 00 00 00       	mov    $0x1,%ecx
    166a:	4c 89 e6             	mov    %r12,%rsi
    166d:	bf 01 00 00 00       	mov    $0x1,%edi
    1672:	48 01 e8             	add    %rbp,%rax
    for (int y = 0 ; y < buffer_size; y++) {
    1675:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
            struct timespec end = thread_data[sender].data[y].end[n];
    167c:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
            const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    1683:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
            const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    1687:	4c 8b 42 10          	mov    0x10(%rdx),%r8
    168b:	31 d2                	xor    %edx,%edx
    168d:	4c 2b 48 08          	sub    0x8(%rax),%r9
    1691:	4c 2b 00             	sub    (%rax),%r8
    1694:	31 c0                	xor    %eax,%eax
    1696:	e8 d5 fa ff ff       	call   1170 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    169b:	48 81 fd 00 00 00 18 	cmp    $0x18000000,%rbp
    16a2:	0f 85 74 ff ff ff    	jne    161c <main+0x45c>
    16a8:	31 d2                	xor    %edx,%edx
    16aa:	31 c0                	xor    %eax,%eax
    16ac:	48 8d 35 cf 0a 00 00 	lea    0xacf(%rip),%rsi        # 2182 <_IO_stdin_used+0x182>
    16b3:	bf 01 00 00 00       	mov    $0x1,%edi
    16b8:	e8 b3 fa ff ff       	call   1170 <__printf_chk@plt>
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    16bd:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    16c2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    16cb:	75 27                	jne    16f4 <main+0x534>
    16cd:	48 83 c4 58          	add    $0x58,%rsp
    16d1:	31 c0                	xor    %eax,%eax
    16d3:	5b                   	pop    %rbx
    16d4:	5d                   	pop    %rbp
    16d5:	41 5c                	pop    %r12
    16d7:	41 5d                	pop    %r13
    16d9:	41 5e                	pop    %r14
    16db:	41 5f                	pop    %r15
    16dd:	c3                   	ret
    16de:	48 8d 3d 1c 0a 00 00 	lea    0xa1c(%rip),%rdi        # 2101 <_IO_stdin_used+0x101>
    16e5:	e8 26 fa ff ff       	call   1110 <puts@plt>
               exit(1);
    16ea:	bf 01 00 00 00       	mov    $0x1,%edi
    16ef:	e8 ac fa ff ff       	call   11a0 <exit@plt>
}
    16f4:	e8 37 fa ff ff       	call   1130 <__stack_chk_fail@plt>
    16f9:	48 8d 3d 1f 0a 00 00 	lea    0xa1f(%rip),%rdi        # 211f <_IO_stdin_used+0x11f>
    1700:	e8 0b fa ff ff       	call   1110 <puts@plt>
              exit(1);
    1705:	bf 01 00 00 00       	mov    $0x1,%edi
    170a:	e8 91 fa ff ff       	call   11a0 <exit@plt>
    170f:	90                   	nop

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
    1804:	41 57                	push   %r15
    1806:	48 8d 35 fb 07 00 00 	lea    0x7fb(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    180d:	31 c0                	xor    %eax,%eax
    180f:	41 56                	push   %r14
    1811:	41 55                	push   %r13
    1813:	41 54                	push   %r12
    1815:	55                   	push   %rbp
    1816:	48 89 fd             	mov    %rdi,%rbp
    1819:	53                   	push   %rbx
    181a:	48 83 ec 18          	sub    $0x18,%rsp
    181e:	8b 17                	mov    (%rdi),%edx
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    1820:	8b 8f 04 01 00 00    	mov    0x104(%rdi),%ecx
    1826:	bf 01 00 00 00       	mov    $0x1,%edi
    182b:	e8 40 f9 ff ff       	call   1170 <__printf_chk@plt>
  int next = (data->end + 1) % data->size;
    1830:	8b 85 00 01 00 00    	mov    0x100(%rbp),%eax
  if (data->mode == WRITER) {
    1836:	8b 95 04 01 00 00    	mov    0x104(%rbp),%edx
  int mina = data->size;
    183c:	4c 8b a5 08 01 00 00 	mov    0x108(%rbp),%r12
  if (data->mode == WRITER) {
    1843:	85 d2                	test   %edx,%edx
    1845:	0f 85 0c 01 00 00    	jne    1957 <disruptor_thread+0x157>
  int next = (data->end + 1) % data->size;
    184b:	83 c0 01             	add    $0x1,%eax
    184e:	48 98                	cltq
    1850:	48 99                	cqto
    1852:	49 f7 fc             	idiv   %r12
    1855:	89 d3                	mov    %edx,%ebx
    1857:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    while (data->running == 1) {
    1860:	8b 85 10 01 00 00    	mov    0x110(%rbp),%eax
    1866:	83 f8 01             	cmp    $0x1,%eax
    1869:	0f 85 cb 00 00 00    	jne    193a <disruptor_thread+0x13a>
      asm volatile ("sfence" ::: "memory");
    186f:	0f ae f8             	sfence
      for (int x  = 0 ; x < data->readers_count; x++) {
    1872:	48 63 95 88 01 00 00 	movslq 0x188(%rbp),%rdx
    1879:	85 d2                	test   %edx,%edx
    187b:	0f 8e 84 01 00 00    	jle    1a05 <disruptor_thread+0x205>
    1881:	48 8b 85 80 01 00 00 	mov    0x180(%rbp),%rax
    1888:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    188c:	0f 1f 40 00          	nopl   0x0(%rax)
        if (next == data->readers[x]->start) {
    1890:	48 8b 08             	mov    (%rax),%rcx
    1893:	8b 89 80 00 00 00    	mov    0x80(%rcx),%ecx
    1899:	39 cb                	cmp    %ecx,%ebx
    189b:	74 c3                	je     1860 <disruptor_thread+0x60>
      for (int x  = 0 ; x < data->readers_count; x++) {
    189d:	48 83 c0 08          	add    $0x8,%rax
    18a1:	48 39 c6             	cmp    %rax,%rsi
    18a4:	75 ea                	jne    1890 <disruptor_thread+0x90>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[changed].start);
    18a6:	48 8b 4d 10          	mov    0x10(%rbp),%rcx
    18aa:	31 d2                	xor    %edx,%edx
    18ac:	0f 1f 40 00          	nopl   0x0(%rax)
              data->data[data->end].complete[n] = 0;
    18b0:	48 63 85 00 01 00 00 	movslq 0x100(%rbp),%rax
    18b7:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    18bb:	48 c1 e0 07          	shl    $0x7,%rax
    18bf:	48 8b 84 01 00 01 00 00 	mov    0x100(%rcx,%rax,1),%rax
    18c7:	48 8d 04 90          	lea    (%rax,%rdx,4),%rax
            for (int n = 0 ; n < data->readers_count ; n++) { 
    18cb:	48 83 c2 01          	add    $0x1,%rdx
              data->data[data->end].complete[n] = 0;
    18cf:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
            for (int n = 0 ; n < data->readers_count ; n++) { 
    18d5:	39 95 88 01 00 00    	cmp    %edx,0x188(%rbp)
    18db:	7f d3                	jg     18b0 <disruptor_thread+0xb0>
            int changed = data->end;
    18dd:	8b b5 00 01 00 00    	mov    0x100(%rbp),%esi
            data->end = (data->end + 1) % data->size;
    18e3:	8b 85 00 01 00 00    	mov    0x100(%rbp),%eax
    18e9:	48 8b bd 08 01 00 00 	mov    0x108(%rbp),%rdi
    18f0:	83 c0 01             	add    $0x1,%eax
    18f3:	48 98                	cltq
    18f5:	48 99                	cqto
    18f7:	48 f7 ff             	idiv   %rdi
    18fa:	89 95 00 01 00 00    	mov    %edx,0x100(%rbp)
            next = (data->end + 1) % data->size;
    1900:	8b 85 00 01 00 00    	mov    0x100(%rbp),%eax
    1906:	83 c0 01             	add    $0x1,%eax
    1909:	48 98                	cltq
    190b:	48 99                	cqto
    190d:	48 f7 ff             	idiv   %rdi
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[changed].start);
    1910:	48 63 c6             	movslq %esi,%rax
    1913:	bf 04 00 00 00       	mov    $0x4,%edi
    1918:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    191c:	48 c1 e0 07          	shl    $0x7,%rax
    1920:	48 8d 34 01          	lea    (%rcx,%rax,1),%rsi
            next = (data->end + 1) % data->size;
    1924:	89 d3                	mov    %edx,%ebx
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[changed].start);
    1926:	e8 f5 f7 ff ff       	call   1120 <clock_gettime@plt>
    while (data->running == 1) {
    192b:	8b 85 10 01 00 00    	mov    0x110(%rbp),%eax
    1931:	83 f8 01             	cmp    $0x1,%eax
    1934:	0f 84 35 ff ff ff    	je     186f <disruptor_thread+0x6f>
    193a:	48 8d 3d 46 07 00 00 	lea    0x746(%rip),%rdi        # 2087 <_IO_stdin_used+0x87>
    1941:	e8 ca f7 ff ff       	call   1110 <puts@plt>
}
    1946:	48 83 c4 18          	add    $0x18,%rsp
    194a:	31 c0                	xor    %eax,%eax
    194c:	5b                   	pop    %rbx
    194d:	5d                   	pop    %rbp
    194e:	41 5c                	pop    %r12
    1950:	41 5d                	pop    %r13
    1952:	41 5e                	pop    %r14
    1954:	41 5f                	pop    %r15
    1956:	c3                   	ret
  else if (data->mode == READER) {
    1957:	8b 85 04 01 00 00    	mov    0x104(%rbp),%eax
    195d:	83 f8 01             	cmp    $0x1,%eax
    1960:	75 d8                	jne    193a <disruptor_thread+0x13a>
    struct Thread *sender = data->sender;
    1962:	4c 8b 7d 08          	mov    0x8(%rbp),%r15
    int index = data->reader_index;
    1966:	4c 63 ad 8c 01 00 00 	movslq 0x18c(%rbp),%r13
    struct Snapshot * rdata = sender->data;
    196d:	49 8b 47 10          	mov    0x10(%r15),%rax
    1971:	48 89 04 24          	mov    %rax,(%rsp)
    int cachedEnd = sender->end;
    1975:	41 8b 87 00 01 00 00 	mov    0x100(%r15),%eax
    int cachedStart = data->start;
    197c:	44 8b b5 80 00 00 00 	mov    0x80(%rbp),%r14d
    while (data->running == 1) {
    1983:	8b b5 10 01 00 00    	mov    0x110(%rbp),%esi
    1989:	83 fe 01             	cmp    $0x1,%esi
    198c:	75 ac                	jne    193a <disruptor_thread+0x13a>
          clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[cachedStart].end[index]);
    198e:	4c 89 ef             	mov    %r13,%rdi
          rdata[cachedStart].complete[index] = 1;
    1991:	49 c1 e5 02          	shl    $0x2,%r13
          clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[cachedStart].end[index]);
    1995:	48 c1 e7 04          	shl    $0x4,%rdi
    1999:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    199e:	66 90                	xchg   %ax,%ax
      if (cachedEnd == cachedStart) {
    19a0:	44 39 f0             	cmp    %r14d,%eax
    19a3:	74 49                	je     19ee <disruptor_thread+0x1ee>
          clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[cachedStart].end[index]);
    19a5:	49 63 c6             	movslq %r14d,%rax
    19a8:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    19ad:	bf 04 00 00 00       	mov    $0x4,%edi
    19b2:	48 8d 1c 40          	lea    (%rax,%rax,2),%rbx
    19b6:	48 8b 04 24          	mov    (%rsp),%rax
    19ba:	48 c1 e3 07          	shl    $0x7,%rbx
    19be:	48 01 c3             	add    %rax,%rbx
    19c1:	48 03 b3 80 00 00 00 	add    0x80(%rbx),%rsi
    19c8:	e8 53 f7 ff ff       	call   1120 <clock_gettime@plt>
          rdata[cachedStart].complete[index] = 1;
    19cd:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
    19d4:	4c 01 e8             	add    %r13,%rax
    19d7:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
          cachedStart = (cachedStart + 1) % size;
    19dd:	41 8d 46 01          	lea    0x1(%r14),%eax
    19e1:	99                   	cltd
    19e2:	41 f7 fc             	idiv   %r12d
          data->start = cachedStart;
    19e5:	89 95 80 00 00 00    	mov    %edx,0x80(%rbp)
          cachedStart = (cachedStart + 1) % size;
    19eb:	41 89 d6             	mov    %edx,%r14d
          cachedEnd = sender->end;
    19ee:	41 8b 87 00 01 00 00 	mov    0x100(%r15),%eax
    while (data->running == 1) {
    19f5:	8b b5 10 01 00 00    	mov    0x110(%rbp),%esi
    19fb:	83 fe 01             	cmp    $0x1,%esi
    19fe:	74 a0                	je     19a0 <disruptor_thread+0x1a0>
    1a00:	e9 35 ff ff ff       	jmp    193a <disruptor_thread+0x13a>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[changed].start);
    1a05:	48 8b 4d 10          	mov    0x10(%rbp),%rcx
    1a09:	e9 cf fe ff ff       	jmp    18dd <disruptor_thread+0xdd>
    1a0e:	66 90                	xchg   %ax,%ax

0000000000001a10 <min>:
int min(long a, long b) {
    1a10:	f3 0f 1e fa          	endbr64
  if (a < b) return a;
    1a14:	48 39 f7             	cmp    %rsi,%rdi
    1a17:	7c 02                	jl     1a1b <min+0xb>
  if (b < a) return b;
    1a19:	7f 05                	jg     1a20 <min+0x10>
  if (a < b) return a;
    1a1b:	89 f8                	mov    %edi,%eax
    1a1d:	c3                   	ret
    1a1e:	66 90                	xchg   %ax,%ax
  if (b < a) return b;
    1a20:	89 f0                	mov    %esi,%eax
}
    1a22:	c3                   	ret

Disassembly of section .fini:

0000000000001a24 <_fini>:
    1a24:	f3 0f 1e fa          	endbr64
    1a28:	48 83 ec 08          	sub    $0x8,%rsp
    1a2c:	48 83 c4 08          	add    $0x8,%rsp
    1a30:	c3                   	ret
