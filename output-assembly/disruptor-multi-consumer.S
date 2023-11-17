
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
    int seq[] = {1, 2, 5};
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    135c:	4c 8d a3 00 02 00 00 	lea    0x200(%rbx),%r12
    thread_data[sender].other_count = other_count;
    1363:	b8 01 00 00 00       	mov    $0x1,%eax
    1368:	8d 50 ff             	lea    -0x1(%rax),%edx
      thread_data[j].thread_index = j;
    136b:	41 89 04 24          	mov    %eax,(%r12)
    136f:	89 c6                	mov    %eax,%esi
      thread_data[j].reader_index = receiver_index;
      thread_data[j].multiple = receiver_index % other_count;
      thread_data[j].other_count = other_count;
     
      thread_data[j].cpu_set = receivercpu;
      thread_data[j].running = 1;
    1371:	41 c7 84 24 10 01 00 00 01 00 00 00 	movl   $0x1,0x110(%r12)
      thread_data[j].reader_index = receiver_index;
    137d:	41 89 94 24 8c 01 00 00 	mov    %edx,0x18c(%r12)
      thread_data[j].multiple = receiver_index % other_count;
    1385:	41 89 94 24 90 01 00 00 	mov    %edx,0x190(%r12)
      thread_data[j].other_count = other_count;
    138d:	41 c7 84 24 88 01 00 00 02 00 00 00 	movl   $0x2,0x188(%r12)
      thread_data[j].cpu_set = receivercpu;
    1399:	4d 89 b4 24 18 01 00 00 	mov    %r14,0x118(%r12)
      thread_data[j].mode = READER;
    13a1:	41 c7 84 24 04 01 00 00 01 00 00 00 	movl   $0x1,0x104(%r12)
      if (j == receiver) {
    13ad:	48 83 f8 01          	cmp    $0x1,%rax
    13b1:	0f 84 a2 02 00 00    	je     1659 <main+0x499>
        for (int n = 0 ; n < buffer_size ; n++) {
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
        }
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
    13b7:	66 0f 6f 1c 24       	movdqa (%rsp),%xmm3
    13bc:	45 31 c0             	xor    %r8d,%r8d
    13bf:	b9 01 00 00 00       	mov    $0x1,%ecx
    13c4:	89 f2                	mov    %esi,%edx
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    13c6:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    13cd:	48 8d 35 84 0c 00 00 	lea    0xc84(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
    13d4:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].size = buffer_size;
    13d9:	49 c7 84 24 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%r12)
      thread_data[j].sender = &thread_data[sender];
    13e5:	41 0f 11 5c 24 08    	movups %xmm3,0x8(%r12)
      thread_data[j].readers = thread_data[sender].readers;
    13eb:	49 89 84 24 80 01 00 00 	mov    %rax,0x180(%r12)
      thread_data[j].start = 0;
    13f3:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    13ff:	4c 89 60 08          	mov    %r12,0x8(%rax)
    1403:	31 c0                	xor    %eax,%eax
    1405:	e8 66 fd ff ff       	call   1170 <__printf_chk@plt>
    140a:	31 d2                	xor    %edx,%edx
    140c:	48 8d 35 d0 0c 00 00 	lea    0xcd0(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    1413:	31 c0                	xor    %eax,%eax
    1415:	bf 01 00 00 00       	mov    $0x1,%edi
    141a:	e8 51 fd ff ff       	call   1170 <__printf_chk@plt>
      printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
    }
    printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    141f:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    1422:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    1427:	c7 44 24 2c 00 00 00 00 	movl   $0x0,0x2c(%rsp)
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1; 
    
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    142f:	4d 8d 65 08          	lea    0x8(%r13),%r12
  param.sched_priority = 0;
    1433:	41 be 01 00 00 00    	mov    $0x1,%r14d
    1439:	48 8d 68 38          	lea    0x38(%rax),%rbp
    143d:	48 8d 35 9f 0c 00 00 	lea    0xc9f(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    1444:	bf 01 00 00 00       	mov    $0x1,%edi
    1449:	31 c0                	xor    %eax,%eax
    144b:	44 89 f2             	mov    %r14d,%edx
    144e:	e8 1d fd ff ff       	call   1170 <__printf_chk@plt>
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    1453:	31 f6                	xor    %esi,%esi
    1455:	48 89 ef             	mov    %rbp,%rdi
    1458:	e8 f3 fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    145d:	85 c0                	test   %eax,%eax
    145f:	0f 85 a0 02 00 00    	jne    1705 <main+0x545>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    1465:	48 8d 74 24 2c       	lea    0x2c(%rsp),%rsi
    146a:	48 89 ef             	mov    %rbp,%rdi
    146d:	e8 1e fd ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1472:	85 c0                	test   %eax,%eax
    1474:	0f 85 a6 02 00 00    	jne    1720 <main+0x560>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    147a:	4c 89 f1             	mov    %r14,%rcx
    147d:	48 89 ee             	mov    %rbp,%rsi
    1480:	4c 89 e7             	mov    %r12,%rdi
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    1483:	48 83 c5 38          	add    $0x38,%rbp
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1487:	48 c1 e1 09          	shl    $0x9,%rcx
    148b:	48 8d 15 9e 03 00 00 	lea    0x39e(%rip),%rdx        # 1830 <disruptor_thread>
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    1492:	49 83 c4 08          	add    $0x8,%r12
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1496:	48 01 d9             	add    %rbx,%rcx
    1499:	e8 e2 fc ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    149e:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
    14a3:	be 08 00 00 00       	mov    $0x8,%esi
    14a8:	48 8b 93 18 03 00 00 	mov    0x318(%rbx),%rdx
    14af:	e8 4c fc ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    14b4:	49 83 fe 01          	cmp    $0x1,%r14
    14b8:	75 0b                	jne    14c5 <main+0x305>
    14ba:	41 be 02 00 00 00    	mov    $0x2,%r14d
    14c0:	e9 78 ff ff ff       	jmp    143d <main+0x27d>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    14c5:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    14ca:	31 f6                	xor    %esi,%esi
    14cc:	4c 89 f7             	mov    %r14,%rdi
    14cf:	e8 7c fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    14d4:	85 c0                	test   %eax,%eax
    14d6:	0f 85 29 02 00 00    	jne    1705 <main+0x545>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    14dc:	48 8d 74 24 28       	lea    0x28(%rsp),%rsi
    14e1:	4c 89 f7             	mov    %r14,%rdi
      param2.sched_priority = 0;
    14e4:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    14ec:	e8 9f fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    14f1:	85 c0                	test   %eax,%eax
    14f3:	0f 85 27 02 00 00    	jne    1720 <main+0x560>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    14f9:	48 89 d9             	mov    %rbx,%rcx
    14fc:	48 8d 15 2d 03 00 00 	lea    0x32d(%rip),%rdx        # 1830 <disruptor_thread>
    1503:	4c 89 f6             	mov    %r14,%rsi
    1506:	4c 89 ef             	mov    %r13,%rdi
    1509:	e8 72 fc ff ff       	call   1180 <pthread_create@plt>
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    150e:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    1512:	be 08 00 00 00       	mov    $0x8,%esi
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + 1; 
    pthread_join(thread[sender], res1);
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    1517:	31 ed                	xor    %ebp,%ebp
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    1519:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
    1520:	4c 8d 25 43 0c 00 00 	lea    0xc43(%rip),%r12        # 216a <_IO_stdin_used+0x16a>
    1527:	e8 d4 fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
  struct timespec preempt = {
    152c:	66 0f 6f 05 5c 0c 00 00 	movdqa 0xc5c(%rip),%xmm0        # 2190 <_IO_stdin_used+0x190>
    1534:	ba 0a 00 00 00       	mov    $0xa,%edx
    1539:	31 c0                	xor    %eax,%eax
    153b:	48 8d 35 f9 0b 00 00 	lea    0xbf9(%rip),%rsi        # 213b <_IO_stdin_used+0x13b>
    1542:	bf 01 00 00 00       	mov    $0x1,%edi
    1547:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    154c:	e8 1f fc ff ff       	call   1170 <__printf_chk@plt>
  nanosleep(&preempt , &rem2);
    1551:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    1556:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    155b:	e8 e0 fb ff ff       	call   1140 <nanosleep@plt>
    pthread_join(thread[sender], res1);
    1560:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    1564:	31 f6                	xor    %esi,%esi
    thread_data[sender].running = 0;
    1566:	c7 83 10 01 00 00 00 00 00 00 	movl   $0x0,0x110(%rbx)
      thread_data[j].running = 0;
    1570:	c7 83 10 03 00 00 00 00 00 00 	movl   $0x0,0x310(%rbx)
    157a:	c7 83 10 05 00 00 00 00 00 00 	movl   $0x0,0x510(%rbx)
    pthread_join(thread[sender], res1);
    1584:	e8 27 fc ff ff       	call   11b0 <pthread_join@plt>
      pthread_join(thread[j], res2);
    1589:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    158d:	48 89 ee             	mov    %rbp,%rsi
    1590:	e8 1b fc ff ff       	call   11b0 <pthread_join@plt>
    1595:	49 8b 7d 10          	mov    0x10(%r13),%rdi
    1599:	48 89 ee             	mov    %rbp,%rsi
    159c:	e8 0f fc ff ff       	call   11b0 <pthread_join@plt>
    15a1:	ba 01 00 00 00       	mov    $0x1,%edx
    15a6:	48 8d 35 a7 0b 00 00 	lea    0xba7(%rip),%rsi        # 2154 <_IO_stdin_used+0x154>
    15ad:	31 c0                	xor    %eax,%eax
    15af:	bf 01 00 00 00       	mov    $0x1,%edi
    15b4:	e8 b7 fb ff ff       	call   1170 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1;
    int incompletes = 0;
    printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    15b9:	eb 15                	jmp    15d0 <main+0x410>
    15bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    15c0:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    15c7:	48 81 fd 00 00 00 18 	cmp    $0x18000000,%rbp
    15ce:	74 4f                	je     161f <main+0x45f>
      int compcount = 0;
      for (int n = 0 ; n < 2 ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    15d0:	48 8b 43 18          	mov    0x18(%rbx),%rax
    15d4:	48 01 e8             	add    %rbp,%rax
    15d7:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
    15de:	83 3a 01             	cmpl   $0x1,(%rdx)
    15e1:	75 dd                	jne    15c0 <main+0x400>
    15e3:	83 7a 04 01          	cmpl   $0x1,0x4(%rdx)
    15e7:	75 d7                	jne    15c0 <main+0x400>
      if (compcount == 2) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
          struct timespec end = thread_data[sender].data[y].end;
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    15e9:	4c 8b 80 88 00 00 00 	mov    0x88(%rax),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    15f0:	48 8b 88 80 00 00 00 	mov    0x80(%rax),%rcx
    15f7:	31 d2                	xor    %edx,%edx
    15f9:	4c 89 e6             	mov    %r12,%rsi
    15fc:	48 2b 08             	sub    (%rax),%rcx
    15ff:	4c 2b 40 08          	sub    0x8(%rax),%r8
    1603:	31 c0                	xor    %eax,%eax
    1605:	bf 01 00 00 00       	mov    $0x1,%edi
    160a:	e8 61 fb ff ff       	call   1170 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    160f:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    1616:	48 81 fd 00 00 00 18 	cmp    $0x18000000,%rbp
    161d:	75 b1                	jne    15d0 <main+0x410>
    161f:	31 d2                	xor    %edx,%edx
    1621:	31 c0                	xor    %eax,%eax
    1623:	48 8d 35 54 0b 00 00 	lea    0xb54(%rip),%rsi        # 217e <_IO_stdin_used+0x17e>
    162a:	bf 01 00 00 00       	mov    $0x1,%edi
    162f:	e8 3c fb ff ff       	call   1170 <__printf_chk@plt>
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    1634:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    1639:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1642:	0f 85 d3 00 00 00    	jne    171b <main+0x55b>
    1648:	48 83 c4 68          	add    $0x68,%rsp
    164c:	31 c0                	xor    %eax,%eax
    164e:	5b                   	pop    %rbx
    164f:	5d                   	pop    %rbp
    1650:	41 5c                	pop    %r12
    1652:	41 5d                	pop    %r13
    1654:	41 5e                	pop    %r14
    1656:	41 5f                	pop    %r15
    1658:	c3                   	ret
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    1659:	be 80 01 00 00       	mov    $0x180,%esi
    165e:	bf 00 00 10 00       	mov    $0x100000,%edi
    1663:	e8 f8 fa ff ff       	call   1160 <calloc@plt>
    1668:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    166d:	48 89 c5             	mov    %rax,%rbp
        for (int n = 0 ; n < buffer_size ; n++) {
    1670:	4c 8d b8 00 01 00 00 	lea    0x100(%rax),%r15
    1677:	48 81 c5 00 01 00 18 	add    $0x18000100,%rbp
    167e:	66 90                	xchg   %ax,%ax
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1680:	be 04 00 00 00       	mov    $0x4,%esi
    1685:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    168a:	49 81 c7 80 01 00 00 	add    $0x180,%r15
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1691:	e8 ca fa ff ff       	call   1160 <calloc@plt>
    1696:	49 89 87 80 fe ff ff 	mov    %rax,-0x180(%r15)
        for (int n = 0 ; n < buffer_size ; n++) {
    169d:	4c 39 fd             	cmp    %r15,%rbp
    16a0:	75 de                	jne    1680 <main+0x4c0>
      thread_data[j].sender = &thread_data[sender];
    16a2:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
    16a7:	45 31 c0             	xor    %r8d,%r8d
    16aa:	31 c9                	xor    %ecx,%ecx
    16ac:	ba 01 00 00 00       	mov    $0x1,%edx
      thread_data[j].readers = thread_data[sender].readers;
    16b1:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    16b8:	48 8d 35 99 09 00 00 	lea    0x999(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
      thread_data[j].size = buffer_size;
    16bf:	49 c7 84 24 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%r12)
    16cb:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].start = 0;
    16d0:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
      thread_data[j].readers = thread_data[sender].readers;
    16dc:	49 89 84 24 80 01 00 00 	mov    %rax,0x180(%r12)
      thread_data[j].sender = &thread_data[sender];
    16e4:	41 0f 11 54 24 08    	movups %xmm2,0x8(%r12)
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    16ea:	4c 89 20             	mov    %r12,(%rax)
    16ed:	31 c0                	xor    %eax,%eax
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    16ef:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    16f6:	e8 75 fa ff ff       	call   1170 <__printf_chk@plt>
    16fb:	b8 02 00 00 00       	mov    $0x2,%eax
    1700:	e9 63 fc ff ff       	jmp    1368 <main+0x1a8>
    1705:	48 8d 3d f4 09 00 00 	lea    0x9f4(%rip),%rdi        # 2100 <_IO_stdin_used+0x100>
    170c:	e8 ff f9 ff ff       	call   1110 <puts@plt>
               exit(1);
    1711:	bf 01 00 00 00       	mov    $0x1,%edi
    1716:	e8 85 fa ff ff       	call   11a0 <exit@plt>
}
    171b:	e8 10 fa ff ff       	call   1130 <__stack_chk_fail@plt>
    1720:	48 8d 3d f7 09 00 00 	lea    0x9f7(%rip),%rdi        # 211e <_IO_stdin_used+0x11e>
    1727:	e8 e4 f9 ff ff       	call   1110 <puts@plt>
              exit(1);
    172c:	bf 01 00 00 00       	mov    $0x1,%edi
    1731:	e8 6a fa ff ff       	call   11a0 <exit@plt>
    1736:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001740 <_start>:
    1740:	f3 0f 1e fa          	endbr64
    1744:	31 ed                	xor    %ebp,%ebp
    1746:	49 89 d1             	mov    %rdx,%r9
    1749:	5e                   	pop    %rsi
    174a:	48 89 e2             	mov    %rsp,%rdx
    174d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1751:	50                   	push   %rax
    1752:	54                   	push   %rsp
    1753:	45 31 c0             	xor    %r8d,%r8d
    1756:	31 c9                	xor    %ecx,%ecx
    1758:	48 8d 3d 61 fa ff ff 	lea    -0x59f(%rip),%rdi        # 11c0 <main>
    175f:	ff 15 73 28 00 00    	call   *0x2873(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1765:	f4                   	hlt
    1766:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001770 <deregister_tm_clones>:
    1770:	48 8d 3d 99 28 00 00 	lea    0x2899(%rip),%rdi        # 4010 <__TMC_END__>
    1777:	48 8d 05 92 28 00 00 	lea    0x2892(%rip),%rax        # 4010 <__TMC_END__>
    177e:	48 39 f8             	cmp    %rdi,%rax
    1781:	74 15                	je     1798 <deregister_tm_clones+0x28>
    1783:	48 8b 05 56 28 00 00 	mov    0x2856(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    178a:	48 85 c0             	test   %rax,%rax
    178d:	74 09                	je     1798 <deregister_tm_clones+0x28>
    178f:	ff e0                	jmp    *%rax
    1791:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1798:	c3                   	ret
    1799:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017a0 <register_tm_clones>:
    17a0:	48 8d 3d 69 28 00 00 	lea    0x2869(%rip),%rdi        # 4010 <__TMC_END__>
    17a7:	48 8d 35 62 28 00 00 	lea    0x2862(%rip),%rsi        # 4010 <__TMC_END__>
    17ae:	48 29 fe             	sub    %rdi,%rsi
    17b1:	48 89 f0             	mov    %rsi,%rax
    17b4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    17b8:	48 c1 f8 03          	sar    $0x3,%rax
    17bc:	48 01 c6             	add    %rax,%rsi
    17bf:	48 d1 fe             	sar    %rsi
    17c2:	74 14                	je     17d8 <register_tm_clones+0x38>
    17c4:	48 8b 05 25 28 00 00 	mov    0x2825(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    17cb:	48 85 c0             	test   %rax,%rax
    17ce:	74 08                	je     17d8 <register_tm_clones+0x38>
    17d0:	ff e0                	jmp    *%rax
    17d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    17d8:	c3                   	ret
    17d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017e0 <__do_global_dtors_aux>:
    17e0:	f3 0f 1e fa          	endbr64
    17e4:	80 3d 25 28 00 00 00 	cmpb   $0x0,0x2825(%rip)        # 4010 <__TMC_END__>
    17eb:	75 2b                	jne    1818 <__do_global_dtors_aux+0x38>
    17ed:	55                   	push   %rbp
    17ee:	48 83 3d 02 28 00 00 00 	cmpq   $0x0,0x2802(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    17f6:	48 89 e5             	mov    %rsp,%rbp
    17f9:	74 0c                	je     1807 <__do_global_dtors_aux+0x27>
    17fb:	48 8b 3d 06 28 00 00 	mov    0x2806(%rip),%rdi        # 4008 <__dso_handle>
    1802:	e8 e9 f8 ff ff       	call   10f0 <__cxa_finalize@plt>
    1807:	e8 64 ff ff ff       	call   1770 <deregister_tm_clones>
    180c:	c6 05 fd 27 00 00 01 	movb   $0x1,0x27fd(%rip)        # 4010 <__TMC_END__>
    1813:	5d                   	pop    %rbp
    1814:	c3                   	ret
    1815:	0f 1f 00             	nopl   (%rax)
    1818:	c3                   	ret
    1819:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001820 <frame_dummy>:
    1820:	f3 0f 1e fa          	endbr64
    1824:	e9 77 ff ff ff       	jmp    17a0 <register_tm_clones>
    1829:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001830 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    1830:	f3 0f 1e fa          	endbr64
    1834:	41 55                	push   %r13
    1836:	48 8d 35 cb 07 00 00 	lea    0x7cb(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    183d:	31 c0                	xor    %eax,%eax
    183f:	41 54                	push   %r12
    1841:	55                   	push   %rbp
    1842:	53                   	push   %rbx
    1843:	48 89 fb             	mov    %rdi,%rbx
    1846:	48 83 ec 08          	sub    $0x8,%rsp
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    184a:	8b 8f 04 01 00 00    	mov    0x104(%rdi),%ecx
    1850:	8b 17                	mov    (%rdi),%edx
    1852:	bf 01 00 00 00       	mov    $0x1,%edi
    1857:	e8 14 f9 ff ff       	call   1170 <__printf_chk@plt>
  if (data->mode == WRITER) {
    185c:	8b 83 04 01 00 00    	mov    0x104(%rbx),%eax
    1862:	85 c0                	test   %eax,%eax
    1864:	74 3a                	je     18a0 <disruptor_thread+0x70>
  } else if (data->mode == READER) {
    1866:	8b 83 04 01 00 00    	mov    0x104(%rbx),%eax
    186c:	83 f8 01             	cmp    $0x1,%eax
    186f:	0f 84 bb 00 00 00    	je     1930 <disruptor_thread+0x100>
  printf("Finished %d\n", data->mode);
    1875:	8b 93 04 01 00 00    	mov    0x104(%rbx),%edx
    187b:	48 8d 35 0f 08 00 00 	lea    0x80f(%rip),%rsi        # 2091 <_IO_stdin_used+0x91>
    1882:	bf 01 00 00 00       	mov    $0x1,%edi
    1887:	31 c0                	xor    %eax,%eax
    1889:	e8 e2 f8 ff ff       	call   1170 <__printf_chk@plt>
}
    188e:	48 83 c4 08          	add    $0x8,%rsp
    1892:	31 c0                	xor    %eax,%eax
    1894:	5b                   	pop    %rbx
    1895:	5d                   	pop    %rbp
    1896:	41 5c                	pop    %r12
    1898:	41 5d                	pop    %r13
    189a:	c3                   	ret
    189b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    18a0:	48 8d 3d de 07 00 00 	lea    0x7de(%rip),%rdi        # 2085 <_IO_stdin_used+0x85>
    18a7:	e8 64 f8 ff ff       	call   1110 <puts@plt>
    struct Thread *me = data->sender;
    18ac:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    while (data->running == 1) {
    18b0:	8b 83 10 01 00 00    	mov    0x110(%rbx),%eax
    18b6:	83 f8 01             	cmp    $0x1,%eax
    18b9:	75 ba                	jne    1875 <disruptor_thread+0x45>
      asm volatile ("sfence" ::: "memory");
    18bb:	0f ae f8             	sfence
        if ((data->end + 1) % me->size == me->start) {
    18be:	8b 83 00 01 00 00    	mov    0x100(%rbx),%eax
    18c4:	48 8b 8d 08 01 00 00 	mov    0x108(%rbp),%rcx
    18cb:	83 c0 01             	add    $0x1,%eax
    18ce:	48 98                	cltq
    18d0:	48 99                	cqto
    18d2:	48 f7 f9             	idiv   %rcx
    18d5:	48 63 85 80 00 00 00 	movslq 0x80(%rbp),%rax
    18dc:	48 39 c2             	cmp    %rax,%rdx
    18df:	74 cf                	je     18b0 <disruptor_thread+0x80>
            int changed = me->end;
    18e1:	48 63 b5 00 01 00 00 	movslq 0x100(%rbp),%rsi
            while (!__sync_bool_compare_and_swap(&me->end, changed, (changed + 1) % me->size)) {
    18e8:	8d 46 01             	lea    0x1(%rsi),%eax
    18eb:	48 98                	cltq
    18ed:	48 99                	cqto
    18ef:	48 f7 f9             	idiv   %rcx
    18f2:	89 f0                	mov    %esi,%eax
    18f4:	f0 0f b1 95 00 01 00 00 	lock cmpxchg %edx,0x100(%rbp)
    18fc:	0f 85 be 00 00 00    	jne    19c0 <disruptor_thread+0x190>
            clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1902:	4c 8d 24 76          	lea    (%rsi,%rsi,2),%r12
    1906:	48 8b 75 18          	mov    0x18(%rbp),%rsi
    190a:	bf 04 00 00 00       	mov    $0x4,%edi
    190f:	49 c1 e4 07          	shl    $0x7,%r12
    1913:	4c 01 e6             	add    %r12,%rsi
    1916:	e8 05 f8 ff ff       	call   1120 <clock_gettime@plt>
            me->data[changed].complete[1] = 1;
    191b:	48 8b 45 18          	mov    0x18(%rbp),%rax
    191f:	4a 8b 84 20 00 01 00 00 	mov    0x100(%rax,%r12,1),%rax
    1927:	c7 40 04 01 00 00 00 	movl   $0x1,0x4(%rax)
    192e:	eb 80                	jmp    18b0 <disruptor_thread+0x80>
    1930:	48 8d 3d 67 07 00 00 	lea    0x767(%rip),%rdi        # 209e <_IO_stdin_used+0x9e>
    1937:	e8 d4 f7 ff ff       	call   1110 <puts@plt>
    struct Thread *sender = data->sender;
    193c:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    struct Snapshot * rdata = sender->data;
    1940:	4c 8b 65 18          	mov    0x18(%rbp),%r12
    while (data->running == 1) {
    1944:	0f 1f 40 00          	nopl   0x0(%rax)
    1948:	8b 83 10 01 00 00    	mov    0x110(%rbx),%eax
    194e:	83 f8 01             	cmp    $0x1,%eax
    1951:	0f 85 1e ff ff ff    	jne    1875 <disruptor_thread+0x45>
      if (sender->end == sender->start) {
    1957:	48 63 8d 80 00 00 00 	movslq 0x80(%rbp),%rcx
    195e:	39 8d 00 01 00 00    	cmp    %ecx,0x100(%rbp)
    1964:	74 e2                	je     1948 <disruptor_thread+0x118>
          if (data->start % data->other_count == data->multiple) {
    1966:	8b 83 80 00 00 00    	mov    0x80(%rbx),%eax
    196c:	99                   	cltd
    196d:	f7 bb 88 01 00 00    	idivl  0x188(%rbx)
    1973:	3b 93 90 01 00 00    	cmp    0x190(%rbx),%edx
    1979:	75 cd                	jne    1948 <disruptor_thread+0x118>
            if (__sync_bool_compare_and_swap(&sender->start, changed, (changed + 1) % sender->size)) {
    197b:	8d 41 01             	lea    0x1(%rcx),%eax
    197e:	48 98                	cltq
    1980:	48 99                	cqto
    1982:	48 f7 bd 08 01 00 00 	idivq  0x108(%rbp)
    1989:	89 c8                	mov    %ecx,%eax
    198b:	f0 0f b1 95 80 00 00 00 	lock cmpxchg %edx,0x80(%rbp)
    1993:	75 b3                	jne    1948 <disruptor_thread+0x118>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end);
    1995:	4c 8d 2c 49          	lea    (%rcx,%rcx,2),%r13
    1999:	bf 04 00 00 00       	mov    $0x4,%edi
    199e:	49 c1 e5 07          	shl    $0x7,%r13
    19a2:	4d 01 e5             	add    %r12,%r13
    19a5:	49 8d b5 80 00 00 00 	lea    0x80(%r13),%rsi
    19ac:	e8 6f f7 ff ff       	call   1120 <clock_gettime@plt>
              rdata[changed].complete[0] = 1;
    19b1:	49 8b 85 00 01 00 00 	mov    0x100(%r13),%rax
    19b8:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
              cachedEnd = sender->end;
    19be:	eb 88                	jmp    1948 <disruptor_thread+0x118>
              changed = me->end;
    19c0:	48 63 b5 00 01 00 00 	movslq 0x100(%rbp),%rsi
            while (!__sync_bool_compare_and_swap(&me->end, changed, (changed + 1) % me->size)) {
    19c7:	48 8b 8d 08 01 00 00 	mov    0x108(%rbp),%rcx
    19ce:	e9 15 ff ff ff       	jmp    18e8 <disruptor_thread+0xb8>
    19d3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    19de:	66 90                	xchg   %ax,%ax

00000000000019e0 <min>:
int min(long a, long b) {
    19e0:	f3 0f 1e fa          	endbr64
  if (a < b) return a;
    19e4:	48 39 f7             	cmp    %rsi,%rdi
    19e7:	7c 02                	jl     19eb <min+0xb>
  if (b < a) return b;
    19e9:	7f 05                	jg     19f0 <min+0x10>
  if (a < b) return a;
    19eb:	89 f8                	mov    %edi,%eax
    19ed:	c3                   	ret
    19ee:	66 90                	xchg   %ax,%ax
  if (b < a) return b;
    19f0:	89 f0                	mov    %esi,%eax
}
    19f2:	c3                   	ret

Disassembly of section .fini:

00000000000019f4 <_fini>:
    19f4:	f3 0f 1e fa          	endbr64
    19f8:	48 83 ec 08          	sub    $0x8,%rsp
    19fc:	48 83 c4 08          	add    $0x8,%rsp
    1a00:	c3                   	ret
