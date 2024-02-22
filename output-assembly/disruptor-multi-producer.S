
disruptor-multi-producer:     file format elf64-x86-64


Disassembly of section .init:

0000000000001000 <_init>:
    1000:	f3 0f 1e fa          	endbr64
    1004:	48 83 ec 08          	sub    $0x8,%rsp
    1008:	48 8d 05 51 07 00 00 	lea    0x751(%rip),%rax        # 1760 <__gmon_start__>
    100f:	48 85 c0             	test   %rax,%rax
    1012:	74 02                	je     1016 <_init+0x16>
    1014:	ff d0                	call   *%rax
    1016:	48 83 c4 08          	add    $0x8,%rsp
    101a:	c3                   	ret

Disassembly of section .plt:

0000000000001020 <.plt>:
    1020:	ff 35 2a 2f 00 00    	push   0x2f2a(%rip)        # 3f50 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:	ff 25 2c 2f 00 00    	jmp    *0x2f2c(%rip)        # 3f58 <_GLOBAL_OFFSET_TABLE_+0x10>
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
    1100:	f3 0f 1e fa          	endbr64
    1104:	68 0d 00 00 00       	push   $0xd
    1109:	e9 12 ff ff ff       	jmp    1020 <_init+0x20>
    110e:	66 90                	xchg   %ax,%ax

Disassembly of section .plt.got:

0000000000001110 <__cxa_finalize@plt>:
    1110:	f3 0f 1e fa          	endbr64
    1114:	ff 25 de 2e 00 00    	jmp    *0x2ede(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    111a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000001120 <pthread_setaffinity_np@plt>:
    1120:	f3 0f 1e fa          	endbr64
    1124:	ff 25 36 2e 00 00    	jmp    *0x2e36(%rip)        # 3f60 <pthread_setaffinity_np@GLIBC_2.34>
    112a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001130 <puts@plt>:
    1130:	f3 0f 1e fa          	endbr64
    1134:	ff 25 2e 2e 00 00    	jmp    *0x2e2e(%rip)        # 3f68 <puts@GLIBC_2.2.5>
    113a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001140 <clock_gettime@plt>:
    1140:	f3 0f 1e fa          	endbr64
    1144:	ff 25 26 2e 00 00    	jmp    *0x2e26(%rip)        # 3f70 <clock_gettime@GLIBC_2.17>
    114a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001150 <__stack_chk_fail@plt>:
    1150:	f3 0f 1e fa          	endbr64
    1154:	ff 25 1e 2e 00 00    	jmp    *0x2e1e(%rip)        # 3f78 <__stack_chk_fail@GLIBC_2.4>
    115a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001160 <nanosleep@plt>:
    1160:	f3 0f 1e fa          	endbr64
    1164:	ff 25 16 2e 00 00    	jmp    *0x2e16(%rip)        # 3f80 <nanosleep@GLIBC_2.2.5>
    116a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001170 <pthread_attr_setschedpolicy@plt>:
    1170:	f3 0f 1e fa          	endbr64
    1174:	ff 25 0e 2e 00 00    	jmp    *0x2e0e(%rip)        # 3f88 <pthread_attr_setschedpolicy@GLIBC_2.2.5>
    117a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001180 <calloc@plt>:
    1180:	f3 0f 1e fa          	endbr64
    1184:	ff 25 06 2e 00 00    	jmp    *0x2e06(%rip)        # 3f90 <calloc@GLIBC_2.2.5>
    118a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001190 <__monstartup@plt>:
    1190:	f3 0f 1e fa          	endbr64
    1194:	ff 25 fe 2d 00 00    	jmp    *0x2dfe(%rip)        # 3f98 <__monstartup@GLIBC_2.2.5>
    119a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011a0 <__printf_chk@plt>:
    11a0:	f3 0f 1e fa          	endbr64
    11a4:	ff 25 f6 2d 00 00    	jmp    *0x2df6(%rip)        # 3fa0 <__printf_chk@GLIBC_2.3.4>
    11aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011b0 <pthread_create@plt>:
    11b0:	f3 0f 1e fa          	endbr64
    11b4:	ff 25 ee 2d 00 00    	jmp    *0x2dee(%rip)        # 3fa8 <pthread_create@GLIBC_2.34>
    11ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011c0 <pthread_attr_setschedparam@plt>:
    11c0:	f3 0f 1e fa          	endbr64
    11c4:	ff 25 e6 2d 00 00    	jmp    *0x2de6(%rip)        # 3fb0 <pthread_attr_setschedparam@GLIBC_2.2.5>
    11ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011d0 <__cxa_atexit@plt>:
    11d0:	f3 0f 1e fa          	endbr64
    11d4:	ff 25 de 2d 00 00    	jmp    *0x2dde(%rip)        # 3fb8 <__cxa_atexit@GLIBC_2.2.5>
    11da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011e0 <exit@plt>:
    11e0:	f3 0f 1e fa          	endbr64
    11e4:	ff 25 d6 2d 00 00    	jmp    *0x2dd6(%rip)        # 3fc0 <exit@GLIBC_2.2.5>
    11ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011f0 <pthread_join@plt>:
    11f0:	f3 0f 1e fa          	endbr64
    11f4:	ff 25 ce 2d 00 00    	jmp    *0x2dce(%rip)        # 3fc8 <pthread_join@GLIBC_2.34>
    11fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000001200 <main>:
  } 
  printf("Finished %d\n", data->mode);
  return 0;
}

int main() {
    1200:	f3 0f 1e fa          	endbr64
    1204:	55                   	push   %rbp
    1205:	48 89 e5             	mov    %rsp,%rbp
    1208:	41 57                	push   %r15
    120a:	41 56                	push   %r14
    120c:	41 55                	push   %r13
    120e:	41 54                	push   %r12
    1210:	53                   	push   %rbx
    1211:	48 83 ec 68          	sub    $0x68,%rsp
    1215:	ff 15 cd 2d 00 00    	call   *0x2dcd(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    121b:	b9 00 00 10 00       	mov    $0x100000,%ecx
    1220:	ba 14 00 00 00       	mov    $0x14,%edx
    1225:	bf 01 00 00 00       	mov    $0x1,%edi
    122a:	48 8d 35 ff 0d 00 00 	lea    0xdff(%rip),%rsi        # 2030 <_IO_stdin_used+0x30>
    1231:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    123a:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    123e:	31 c0                	xor    %eax,%eax
    1240:	e8 5b ff ff ff       	call   11a0 <__printf_chk@plt>
    1245:	ba 01 00 00 00       	mov    $0x1,%edx
    124a:	48 8d 35 59 0e 00 00 	lea    0xe59(%rip),%rsi        # 20aa <_IO_stdin_used+0xaa>
    1251:	31 c0                	xor    %eax,%eax
    1253:	bf 01 00 00 00       	mov    $0x1,%edi
    1258:	e8 43 ff ff ff       	call   11a0 <__printf_chk@plt>
    125d:	ba 02 00 00 00       	mov    $0x2,%edx
    1262:	48 8d 35 51 0e 00 00 	lea    0xe51(%rip),%rsi        # 20ba <_IO_stdin_used+0xba>
    1269:	31 c0                	xor    %eax,%eax
    126b:	bf 01 00 00 00       	mov    $0x1,%edi
    1270:	e8 2b ff ff ff       	call   11a0 <__printf_chk@plt>
    1275:	ba 03 00 00 00       	mov    $0x3,%edx
    127a:	48 8d 35 4b 0e 00 00 	lea    0xe4b(%rip),%rsi        # 20cc <_IO_stdin_used+0xcc>
    1281:	31 c0                	xor    %eax,%eax
    1283:	bf 01 00 00 00       	mov    $0x1,%edi
    1288:	e8 13 ff ff ff       	call   11a0 <__printf_chk@plt>
  int other_count = 2;
  int group_size = writers_count + other_count;
  printf("Readers count %d\n", other_count);
  int thread_count = groups * (other_count + writers_count);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    128d:	be 00 02 00 00       	mov    $0x200,%esi
    1292:	bf 03 00 00 00       	mov    $0x3,%edi
    1297:	e8 e4 fe ff ff       	call   1180 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    129c:	be 38 00 00 00       	mov    $0x38,%esi
    12a1:	bf 03 00 00 00       	mov    $0x3,%edi
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    12a6:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12a9:	e8 d2 fe ff ff       	call   1180 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12ae:	be 08 00 00 00       	mov    $0x8,%esi
    12b3:	bf 03 00 00 00       	mov    $0x3,%edi
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12b8:	48 89 45 88          	mov    %rax,-0x78(%rbp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12bc:	e8 bf fe ff ff       	call   1180 <calloc@plt>
  // 0, 3, 6
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1; 
    int receiver2 = receiver + 1; 
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12c1:	be 80 00 00 00       	mov    $0x80,%esi
    12c6:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12cb:	48 89 45 80          	mov    %rax,-0x80(%rbp)
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12cf:	e8 ac fe ff ff       	call   1180 <calloc@plt>
    CPU_ZERO(sendercpu);
    for (int j = 0 ; j < cores ; j++) {
      // printf("assigning sender %d to core %d\n", sender, j);
      CPU_SET(j, sendercpu);
    }
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12d4:	be 80 00 00 00       	mov    $0x80,%esi
    12d9:	bf 01 00 00 00       	mov    $0x1,%edi
      CPU_SET(j, sendercpu);
    12de:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12e5:	48 89 c3             	mov    %rax,%rbx
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12e8:	e8 93 fe ff ff       	call   1180 <calloc@plt>
    for (int j = 0; j < cores ; j++) {
      // printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    }
     
    thread_data[sender].thread_index = sender;
    12ed:	41 c7 45 00 00 00 00 00 	movl   $0x0,0x0(%r13)
      CPU_SET(j, receivercpu);
    12f5:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12fc:	48 89 85 78 ff ff ff 	mov    %rax,-0x88(%rbp)
    thread_data[sender].cpu_set = sendercpu;
    thread_data[sender].mode = READER;
    thread_data[sender].running = 1;
    thread_data[sender].size = buffer_size;
    thread_data[sender].end = 0;
    1303:	31 c0                	xor    %eax,%eax
    thread_data[sender].mode = READER;
    1305:	41 c7 85 04 01 00 00 01 00 00 00 	movl   $0x1,0x104(%r13)
    thread_data[sender].cpu_set = sendercpu;
    1310:	49 89 9d 18 01 00 00 	mov    %rbx,0x118(%r13)
    thread_data[sender].running = 1;
    1317:	41 c7 85 10 01 00 00 01 00 00 00 	movl   $0x1,0x110(%r13)
    thread_data[sender].size = buffer_size;
    1322:	49 c7 85 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%r13)
    thread_data[sender].end = 0;
    132d:	41 87 85 00 01 00 00 	xchg   %eax,0x100(%r13)
    thread_data[sender].sender = &thread_data[receiver];
    thread_data[sender].readers = calloc(other_count, sizeof(struct Thread*));
    1334:	be 08 00 00 00       	mov    $0x8,%esi
    1339:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[sender].sender = &thread_data[receiver];
    133e:	4d 8d b5 00 02 00 00 	lea    0x200(%r13),%r14
    1345:	4d 89 75 08          	mov    %r14,0x8(%r13)
    thread_data[sender].readers = calloc(other_count, sizeof(struct Thread*));
    1349:	4d 89 f7             	mov    %r14,%r15
    134c:	e8 2f fe ff ff       	call   1180 <calloc@plt>
    thread_data[sender].other_count = other_count;
    1351:	41 c7 85 88 01 00 00 02 00 00 00 	movl   $0x2,0x188(%r13)
    thread_data[sender].readers = calloc(other_count, sizeof(struct Thread*));
    135c:	49 89 85 80 01 00 00 	mov    %rax,0x180(%r13)
    thread_data[sender].other_count = other_count;
    1363:	b8 01 00 00 00       	mov    $0x1,%eax
    // printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
      thread_data[j].thread_index = j;
      thread_data[j].reader_index = receiver_index;
      thread_data[j].cpu_set = receivercpu;
    1368:	48 8b bd 78 ff ff ff 	mov    -0x88(%rbp),%rdi
      thread_data[j].reader_index = receiver_index;
    136f:	8d 50 ff             	lea    -0x1(%rax),%edx
      thread_data[j].thread_index = j;
    1372:	41 89 07             	mov    %eax,(%r15)
      thread_data[j].running = 1;
    1375:	41 c7 87 10 01 00 00 01 00 00 00 	movl   $0x1,0x110(%r15)
      thread_data[j].reader_index = receiver_index;
    1380:	41 89 97 8c 01 00 00 	mov    %edx,0x18c(%r15)
      thread_data[j].cpu_set = receivercpu;
    1387:	49 89 bf 18 01 00 00 	mov    %rdi,0x118(%r15)
      thread_data[j].mode = WRITER;
    138e:	41 c7 87 04 01 00 00 00 00 00 00 	movl   $0x0,0x104(%r15)
      if (j == receiver) {
    1399:	48 83 f8 01          	cmp    $0x1,%rax
    139d:	0f 84 a4 02 00 00    	je     1647 <main+0x447>
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[receiver];
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    13a3:	49 8b 85 80 01 00 00 	mov    0x180(%r13),%rax
      thread_data[j].sender = &thread_data[receiver];
    13aa:	4d 89 77 08          	mov    %r14,0x8(%r15)
    13ae:	45 31 c0             	xor    %r8d,%r8d
    13b1:	b9 01 00 00 00       	mov    $0x1,%ecx
      thread_data[j].reader = &thread_data[sender];
    13b6:	4d 89 6f 10          	mov    %r13,0x10(%r15)
    13ba:	ba 02 00 00 00       	mov    $0x2,%edx
    13bf:	bf 01 00 00 00       	mov    $0x1,%edi
    13c4:	48 8d 35 8d 0c 00 00 	lea    0xc8d(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
      thread_data[j].readers = thread_data[sender].readers;
    13cb:	49 89 87 80 01 00 00 	mov    %rax,0x180(%r15)
      thread_data[j].size = buffer_size;
    13d2:	49 c7 87 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%r15)
      thread_data[j].start = 0;
    13dd:	41 c7 87 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r15)
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    13e8:	4c 89 78 08          	mov    %r15,0x8(%rax)
    13ec:	31 c0                	xor    %eax,%eax
    13ee:	e8 ad fd ff ff       	call   11a0 <__printf_chk@plt>
    13f3:	31 d2                	xor    %edx,%edx
    13f5:	48 8d 35 e7 0c 00 00 	lea    0xce7(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    13fc:	31 c0                	xor    %eax,%eax
    13fe:	bf 01 00 00 00       	mov    $0x1,%edi
    1403:	e8 98 fd ff ff       	call   11a0 <__printf_chk@plt>
      printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
    }
    printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    1408:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    140b:	48 8b 45 88          	mov    -0x78(%rbp),%rax
    140f:	c7 45 9c 00 00 00 00 	movl   $0x0,-0x64(%rbp)
    1416:	41 be 01 00 00 00    	mov    $0x1,%r14d
    141c:	48 8d 58 38          	lea    0x38(%rax),%rbx
    1420:	48 8b 45 80          	mov    -0x80(%rbp),%rax
    1424:	4c 8d 60 08          	lea    0x8(%rax),%r12
    1428:	48 8d 35 b4 0c 00 00 	lea    0xcb4(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    142f:	bf 01 00 00 00       	mov    $0x1,%edi
    1434:	31 c0                	xor    %eax,%eax
    1436:	44 89 f2             	mov    %r14d,%edx
    1439:	e8 62 fd ff ff       	call   11a0 <__printf_chk@plt>
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    143e:	31 f6                	xor    %esi,%esi
    1440:	48 89 df             	mov    %rbx,%rdi
    1443:	e8 28 fd ff ff       	call   1170 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    1448:	85 c0                	test   %eax,%eax
    144a:	0f 85 a0 02 00 00    	jne    16f0 <main+0x4f0>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    1450:	48 8d 75 9c          	lea    -0x64(%rbp),%rsi
    1454:	48 89 df             	mov    %rbx,%rdi
    1457:	e8 64 fd ff ff       	call   11c0 <pthread_attr_setschedparam@plt>
      if (ret) {
    145c:	85 c0                	test   %eax,%eax
    145e:	0f 85 a7 02 00 00    	jne    170b <main+0x50b>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1464:	4c 89 f1             	mov    %r14,%rcx
    1467:	48 89 de             	mov    %rbx,%rsi
    146a:	4c 89 e7             	mov    %r12,%rdi
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    146d:	48 83 c3 38          	add    $0x38,%rbx
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1471:	48 c1 e1 09          	shl    $0x9,%rcx
    1475:	48 8d 15 04 04 00 00 	lea    0x404(%rip),%rdx        # 1880 <disruptor_thread>
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    147c:	49 83 c4 08          	add    $0x8,%r12
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1480:	4c 01 e9             	add    %r13,%rcx
    1483:	e8 28 fd ff ff       	call   11b0 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    1488:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
    148d:	be 08 00 00 00       	mov    $0x8,%esi
    1492:	49 8b 95 18 03 00 00 	mov    0x318(%r13),%rdx
    1499:	e8 82 fc ff ff       	call   1120 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    149e:	49 83 fe 01          	cmp    $0x1,%r14
    14a2:	75 0b                	jne    14af <main+0x2af>
    14a4:	41 be 02 00 00 00    	mov    $0x2,%r14d
    14aa:	e9 79 ff ff ff       	jmp    1428 <main+0x228>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    14af:	48 8b 5d 88          	mov    -0x78(%rbp),%rbx
    14b3:	31 f6                	xor    %esi,%esi
    14b5:	48 89 df             	mov    %rbx,%rdi
    14b8:	e8 b3 fc ff ff       	call   1170 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    14bd:	85 c0                	test   %eax,%eax
    14bf:	0f 85 2b 02 00 00    	jne    16f0 <main+0x4f0>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    14c5:	48 8d 75 98          	lea    -0x68(%rbp),%rsi
    14c9:	48 89 df             	mov    %rbx,%rdi
      param2.sched_priority = 0;
    14cc:	c7 45 98 00 00 00 00 	movl   $0x0,-0x68(%rbp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    14d3:	e8 e8 fc ff ff       	call   11c0 <pthread_attr_setschedparam@plt>
      if (ret) {
    14d8:	85 c0                	test   %eax,%eax
    14da:	0f 85 2b 02 00 00    	jne    170b <main+0x50b>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    14e0:	4c 8b 75 80          	mov    -0x80(%rbp),%r14
    14e4:	4c 89 e9             	mov    %r13,%rcx
    14e7:	48 89 de             	mov    %rbx,%rsi
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + 1; 
    pthread_join(thread[sender], res1);
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    14ea:	31 db                	xor    %ebx,%ebx
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    14ec:	48 8d 15 8d 03 00 00 	lea    0x38d(%rip),%rdx        # 1880 <disruptor_thread>
    14f3:	4c 8d 25 70 0c 00 00 	lea    0xc70(%rip),%r12        # 216a <_IO_stdin_used+0x16a>
    14fa:	4c 89 f7             	mov    %r14,%rdi
    14fd:	e8 ae fc ff ff       	call   11b0 <pthread_create@plt>
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    1502:	49 8b 95 18 01 00 00 	mov    0x118(%r13),%rdx
    1509:	49 8b 3e             	mov    (%r14),%rdi
    150c:	be 08 00 00 00       	mov    $0x8,%esi
    1511:	e8 0a fc ff ff       	call   1120 <pthread_setaffinity_np@plt>
  struct timespec preempt = {
    1516:	66 0f 6f 05 72 0c 00 00 	movdqa 0xc72(%rip),%xmm0        # 2190 <_IO_stdin_used+0x190>
    151e:	ba 0a 00 00 00       	mov    $0xa,%edx
    1523:	31 c0                	xor    %eax,%eax
    1525:	48 8d 35 0f 0c 00 00 	lea    0xc0f(%rip),%rsi        # 213b <_IO_stdin_used+0x13b>
    152c:	bf 01 00 00 00       	mov    $0x1,%edi
    1531:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
    1535:	e8 66 fc ff ff       	call   11a0 <__printf_chk@plt>
  nanosleep(&preempt , &rem2);
    153a:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    153e:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
    1542:	e8 19 fc ff ff       	call   1160 <nanosleep@plt>
    pthread_join(thread[sender], res1);
    1547:	49 8b 3e             	mov    (%r14),%rdi
    154a:	31 f6                	xor    %esi,%esi
    thread_data[sender].running = 0;
    154c:	41 c7 85 10 01 00 00 00 00 00 00 	movl   $0x0,0x110(%r13)
      thread_data[j].running = 0;
    1557:	41 c7 85 10 03 00 00 00 00 00 00 	movl   $0x0,0x310(%r13)
    1562:	41 c7 85 10 05 00 00 00 00 00 00 	movl   $0x0,0x510(%r13)
    pthread_join(thread[sender], res1);
    156d:	e8 7e fc ff ff       	call   11f0 <pthread_join@plt>
      pthread_join(thread[j], res2);
    1572:	49 8b 7e 08          	mov    0x8(%r14),%rdi
    1576:	48 89 de             	mov    %rbx,%rsi
    1579:	e8 72 fc ff ff       	call   11f0 <pthread_join@plt>
    157e:	49 8b 7e 10          	mov    0x10(%r14),%rdi
    1582:	48 89 de             	mov    %rbx,%rsi
    1585:	e8 66 fc ff ff       	call   11f0 <pthread_join@plt>
    158a:	ba 01 00 00 00       	mov    $0x1,%edx
    158f:	48 8d 35 be 0b 00 00 	lea    0xbbe(%rip),%rsi        # 2154 <_IO_stdin_used+0x154>
    1596:	31 c0                	xor    %eax,%eax
    1598:	bf 01 00 00 00       	mov    $0x1,%edi
    159d:	e8 fe fb ff ff       	call   11a0 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1;
    int incompletes = 0;
    printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    15a2:	eb 14                	jmp    15b8 <main+0x3b8>
    15a4:	0f 1f 40 00          	nopl   0x0(%rax)
    15a8:	48 81 c3 80 01 00 00 	add    $0x180,%rbx
    15af:	48 81 fb 00 00 00 18 	cmp    $0x18000000,%rbx
    15b6:	74 56                	je     160e <main+0x40e>
      int compcount = 0;
      for (int n = 0 ; n < other_count ; n++) {

        if (thread_data[receiver].data[y].complete[n] == 1) {
    15b8:	49 8b 95 18 02 00 00 	mov    0x218(%r13),%rdx
    15bf:	48 01 da             	add    %rbx,%rdx
    15c2:	48 8b 82 00 01 00 00 	mov    0x100(%rdx),%rax
    15c9:	8b 08                	mov    (%rax),%ecx
    15cb:	8b 40 04             	mov    0x4(%rax),%eax
    15ce:	83 f9 01             	cmp    $0x1,%ecx
    15d1:	75 d5                	jne    15a8 <main+0x3a8>
    15d3:	83 f8 01             	cmp    $0x1,%eax
    15d6:	75 d0                	jne    15a8 <main+0x3a8>
      if (compcount == other_count) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[receiver].data[y].start;
          struct timespec end = thread_data[receiver].data[y].end;
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    15d8:	4c 8b 82 88 00 00 00 	mov    0x88(%rdx),%r8
    15df:	4c 89 e6             	mov    %r12,%rsi
    15e2:	4c 2b 42 08          	sub    0x8(%rdx),%r8
    15e6:	31 c0                	xor    %eax,%eax
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    15e8:	48 8b 8a 80 00 00 00 	mov    0x80(%rdx),%rcx
    15ef:	bf 01 00 00 00       	mov    $0x1,%edi
    15f4:	48 2b 0a             	sub    (%rdx),%rcx
    15f7:	31 d2                	xor    %edx,%edx
    15f9:	e8 a2 fb ff ff       	call   11a0 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    15fe:	48 81 c3 80 01 00 00 	add    $0x180,%rbx
    1605:	48 81 fb 00 00 00 18 	cmp    $0x18000000,%rbx
    160c:	75 aa                	jne    15b8 <main+0x3b8>
    160e:	31 d2                	xor    %edx,%edx
    1610:	31 c0                	xor    %eax,%eax
    1612:	48 8d 35 65 0b 00 00 	lea    0xb65(%rip),%rsi        # 217e <_IO_stdin_used+0x17e>
    1619:	bf 01 00 00 00       	mov    $0x1,%edi
    161e:	e8 7d fb ff ff       	call   11a0 <__printf_chk@plt>
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    1623:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    1627:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1630:	0f 85 d0 00 00 00    	jne    1706 <main+0x506>
    1636:	48 83 c4 68          	add    $0x68,%rsp
    163a:	31 c0                	xor    %eax,%eax
    163c:	5b                   	pop    %rbx
    163d:	41 5c                	pop    %r12
    163f:	41 5d                	pop    %r13
    1641:	41 5e                	pop    %r14
    1643:	41 5f                	pop    %r15
    1645:	5d                   	pop    %rbp
    1646:	c3                   	ret
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    1647:	be 80 01 00 00       	mov    $0x180,%esi
    164c:	bf 00 00 10 00       	mov    $0x100000,%edi
    1651:	e8 2a fb ff ff       	call   1180 <calloc@plt>
    1656:	49 89 47 18          	mov    %rax,0x18(%r15)
    165a:	48 89 c3             	mov    %rax,%rbx
        for (int n = 0 ; n < buffer_size ; n++) {
    165d:	4c 8d a0 00 01 00 00 	lea    0x100(%rax),%r12
    1664:	48 81 c3 00 01 00 18 	add    $0x18000100,%rbx
    166b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1670:	be 04 00 00 00       	mov    $0x4,%esi
    1675:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    167a:	49 81 c4 80 01 00 00 	add    $0x180,%r12
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1681:	e8 fa fa ff ff       	call   1180 <calloc@plt>
    1686:	49 89 84 24 80 fe ff ff 	mov    %rax,-0x180(%r12)
        for (int n = 0 ; n < buffer_size ; n++) {
    168e:	49 39 dc             	cmp    %rbx,%r12
    1691:	75 dd                	jne    1670 <main+0x470>
      thread_data[j].readers = thread_data[sender].readers;
    1693:	49 8b 85 80 01 00 00 	mov    0x180(%r13),%rax
      thread_data[j].sender = &thread_data[receiver];
    169a:	4d 89 77 08          	mov    %r14,0x8(%r15)
    169e:	45 31 c0             	xor    %r8d,%r8d
    16a1:	31 c9                	xor    %ecx,%ecx
      thread_data[j].reader = &thread_data[sender];
    16a3:	4d 89 6f 10          	mov    %r13,0x10(%r15)
    16a7:	ba 01 00 00 00       	mov    $0x1,%edx
    16ac:	bf 01 00 00 00       	mov    $0x1,%edi
    16b1:	48 8d 35 a0 09 00 00 	lea    0x9a0(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
      thread_data[j].readers = thread_data[sender].readers;
    16b8:	49 89 87 80 01 00 00 	mov    %rax,0x180(%r15)
      thread_data[j].size = buffer_size;
    16bf:	49 c7 87 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%r15)
      thread_data[j].start = 0;
    16ca:	41 c7 87 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r15)
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    16d5:	4c 89 38             	mov    %r15,(%rax)
    16d8:	31 c0                	xor    %eax,%eax
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    16da:	49 81 c7 00 02 00 00 	add    $0x200,%r15
    16e1:	e8 ba fa ff ff       	call   11a0 <__printf_chk@plt>
    16e6:	b8 02 00 00 00       	mov    $0x2,%eax
    16eb:	e9 78 fc ff ff       	jmp    1368 <main+0x168>
    16f0:	48 8d 3d 09 0a 00 00 	lea    0xa09(%rip),%rdi        # 2100 <_IO_stdin_used+0x100>
    16f7:	e8 34 fa ff ff       	call   1130 <puts@plt>
               exit(1);
    16fc:	bf 01 00 00 00       	mov    $0x1,%edi
    1701:	e8 da fa ff ff       	call   11e0 <exit@plt>
}
    1706:	e8 45 fa ff ff       	call   1150 <__stack_chk_fail@plt>
    170b:	48 8d 3d 0c 0a 00 00 	lea    0xa0c(%rip),%rdi        # 211e <_IO_stdin_used+0x11e>
    1712:	e8 19 fa ff ff       	call   1130 <puts@plt>
              exit(1);
    1717:	bf 01 00 00 00       	mov    $0x1,%edi
    171c:	e8 bf fa ff ff       	call   11e0 <exit@plt>
    1721:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    172b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000001730 <_start>:
    1730:	f3 0f 1e fa          	endbr64
    1734:	31 ed                	xor    %ebp,%ebp
    1736:	49 89 d1             	mov    %rdx,%r9
    1739:	5e                   	pop    %rsi
    173a:	48 89 e2             	mov    %rsp,%rdx
    173d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1741:	50                   	push   %rax
    1742:	54                   	push   %rsp
    1743:	45 31 c0             	xor    %r8d,%r8d
    1746:	31 c9                	xor    %ecx,%ecx
    1748:	48 8d 3d b1 fa ff ff 	lea    -0x54f(%rip),%rdi        # 1200 <main>
    174f:	ff 15 7b 28 00 00    	call   *0x287b(%rip)        # 3fd0 <__libc_start_main@GLIBC_2.34>
    1755:	f4                   	hlt
    1756:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001760 <__gmon_start__>:
    1760:	f3 0f 1e fa          	endbr64
    1764:	8b 05 a6 28 00 00    	mov    0x28a6(%rip),%eax        # 4010 <__TMC_END__>
    176a:	85 c0                	test   %eax,%eax
    176c:	74 02                	je     1770 <__gmon_start__+0x10>
    176e:	c3                   	ret
    176f:	90                   	nop
    1770:	48 83 ec 08          	sub    $0x8,%rsp
    1774:	48 8d 35 72 03 00 00 	lea    0x372(%rip),%rsi        # 1aed <etext>
    177b:	48 8d 3d 7e e8 ff ff 	lea    -0x1782(%rip),%rdi        # 0 <__executable_start>
    1782:	c7 05 84 28 00 00 01 00 00 00 	movl   $0x1,0x2884(%rip)        # 4010 <__TMC_END__>
    178c:	e8 ff f9 ff ff       	call   1190 <__monstartup@plt>
    1791:	48 8b 3d 48 28 00 00 	mov    0x2848(%rip),%rdi        # 3fe0 <_mcleanup@GLIBC_2.2.5>
    1798:	48 83 c4 08          	add    $0x8,%rsp
    179c:	e9 0f 03 00 00       	jmp    1ab0 <atexit>
    17a1:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    17ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000017b0 <_dl_relocate_static_pie>:
    17b0:	f3 0f 1e fa          	endbr64
    17b4:	c3                   	ret
    17b5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    17bf:	90                   	nop

00000000000017c0 <deregister_tm_clones>:
    17c0:	48 8d 3d 49 28 00 00 	lea    0x2849(%rip),%rdi        # 4010 <__TMC_END__>
    17c7:	48 8d 05 42 28 00 00 	lea    0x2842(%rip),%rax        # 4010 <__TMC_END__>
    17ce:	48 39 f8             	cmp    %rdi,%rax
    17d1:	74 15                	je     17e8 <deregister_tm_clones+0x28>
    17d3:	48 8b 05 fe 27 00 00 	mov    0x27fe(%rip),%rax        # 3fd8 <_ITM_deregisterTMCloneTable@Base>
    17da:	48 85 c0             	test   %rax,%rax
    17dd:	74 09                	je     17e8 <deregister_tm_clones+0x28>
    17df:	ff e0                	jmp    *%rax
    17e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    17e8:	c3                   	ret
    17e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017f0 <register_tm_clones>:
    17f0:	48 8d 3d 19 28 00 00 	lea    0x2819(%rip),%rdi        # 4010 <__TMC_END__>
    17f7:	48 8d 35 12 28 00 00 	lea    0x2812(%rip),%rsi        # 4010 <__TMC_END__>
    17fe:	48 29 fe             	sub    %rdi,%rsi
    1801:	48 89 f0             	mov    %rsi,%rax
    1804:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1808:	48 c1 f8 03          	sar    $0x3,%rax
    180c:	48 01 c6             	add    %rax,%rsi
    180f:	48 d1 fe             	sar    %rsi
    1812:	74 14                	je     1828 <register_tm_clones+0x38>
    1814:	48 8b 05 d5 27 00 00 	mov    0x27d5(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    181b:	48 85 c0             	test   %rax,%rax
    181e:	74 08                	je     1828 <register_tm_clones+0x38>
    1820:	ff e0                	jmp    *%rax
    1822:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1828:	c3                   	ret
    1829:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001830 <__do_global_dtors_aux>:
    1830:	f3 0f 1e fa          	endbr64
    1834:	80 3d d9 27 00 00 00 	cmpb   $0x0,0x27d9(%rip)        # 4014 <completed.0>
    183b:	75 2b                	jne    1868 <__do_global_dtors_aux+0x38>
    183d:	55                   	push   %rbp
    183e:	48 83 3d b2 27 00 00 00 	cmpq   $0x0,0x27b2(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1846:	48 89 e5             	mov    %rsp,%rbp
    1849:	74 0c                	je     1857 <__do_global_dtors_aux+0x27>
    184b:	48 8b 3d b6 27 00 00 	mov    0x27b6(%rip),%rdi        # 4008 <__dso_handle>
    1852:	e8 b9 f8 ff ff       	call   1110 <__cxa_finalize@plt>
    1857:	e8 64 ff ff ff       	call   17c0 <deregister_tm_clones>
    185c:	c6 05 b1 27 00 00 01 	movb   $0x1,0x27b1(%rip)        # 4014 <completed.0>
    1863:	5d                   	pop    %rbp
    1864:	c3                   	ret
    1865:	0f 1f 00             	nopl   (%rax)
    1868:	c3                   	ret
    1869:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001870 <frame_dummy>:
    1870:	f3 0f 1e fa          	endbr64
    1874:	e9 77 ff ff ff       	jmp    17f0 <register_tm_clones>
    1879:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001880 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    1880:	f3 0f 1e fa          	endbr64
    1884:	55                   	push   %rbp
    1885:	48 89 e5             	mov    %rsp,%rbp
    1888:	41 57                	push   %r15
    188a:	41 56                	push   %r14
    188c:	41 55                	push   %r13
    188e:	41 54                	push   %r12
    1890:	53                   	push   %rbx
    1891:	48 83 ec 18          	sub    $0x18,%rsp
    1895:	ff 15 4d 27 00 00    	call   *0x274d(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
    189b:	48 8d 35 66 07 00 00 	lea    0x766(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    18a2:	31 c0                	xor    %eax,%eax
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    18a4:	8b 8f 04 01 00 00    	mov    0x104(%rdi),%ecx
    18aa:	8b 17                	mov    (%rdi),%edx
void * disruptor_thread(void * arg) {
    18ac:	48 89 fb             	mov    %rdi,%rbx
    18af:	bf 01 00 00 00       	mov    $0x1,%edi
    18b4:	e8 e7 f8 ff ff       	call   11a0 <__printf_chk@plt>
  int next = (data->end + 1) % data->size;
    18b9:	8b 83 00 01 00 00    	mov    0x100(%rbx),%eax
  if (data->mode == WRITER) {
    18bf:	8b 83 04 01 00 00    	mov    0x104(%rbx),%eax
    18c5:	85 c0                	test   %eax,%eax
    18c7:	74 3f                	je     1908 <disruptor_thread+0x88>
  } else if (data->mode == READER) {
    18c9:	8b 83 04 01 00 00    	mov    0x104(%rbx),%eax
    18cf:	83 f8 01             	cmp    $0x1,%eax
    18d2:	0f 84 e8 00 00 00    	je     19c0 <disruptor_thread+0x140>
  printf("Finished %d\n", data->mode);
    18d8:	8b 93 04 01 00 00    	mov    0x104(%rbx),%edx
    18de:	48 8d 35 b8 07 00 00 	lea    0x7b8(%rip),%rsi        # 209d <_IO_stdin_used+0x9d>
    18e5:	bf 01 00 00 00       	mov    $0x1,%edi
    18ea:	31 c0                	xor    %eax,%eax
    18ec:	e8 af f8 ff ff       	call   11a0 <__printf_chk@plt>
}
    18f1:	48 83 c4 18          	add    $0x18,%rsp
    18f5:	31 c0                	xor    %eax,%eax
    18f7:	5b                   	pop    %rbx
    18f8:	41 5c                	pop    %r12
    18fa:	41 5d                	pop    %r13
    18fc:	41 5e                	pop    %r14
    18fe:	41 5f                	pop    %r15
    1900:	5d                   	pop    %rbp
    1901:	c3                   	ret
    1902:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1908:	48 8d 3d 76 07 00 00 	lea    0x776(%rip),%rdi        # 2085 <_IO_stdin_used+0x85>
    190f:	e8 1c f8 ff ff       	call   1130 <puts@plt>
    struct Thread *me = data->sender;
    1914:	4c 8b 6b 08          	mov    0x8(%rbx),%r13
    next = (me->end + 1) % data->size;
    1918:	4d 8d b5 00 01 00 00 	lea    0x100(%r13),%r14
    191f:	41 8b 85 00 01 00 00 	mov    0x100(%r13),%eax
    1926:	83 c0 01             	add    $0x1,%eax
    1929:	48 98                	cltq
    192b:	48 99                	cqto
    192d:	48 f7 bb 08 01 00 00 	idivq  0x108(%rbx)
    while (data->running == 1) {
    1934:	0f 1f 40 00          	nopl   0x0(%rax)
    1938:	8b 83 10 01 00 00    	mov    0x110(%rbx),%eax
    193e:	83 f8 01             	cmp    $0x1,%eax
    1941:	75 95                	jne    18d8 <disruptor_thread+0x58>
      asm volatile ("sfence" ::: "memory");
    1943:	0f ae f8             	sfence
        if (next == data->reader->start) {
    1946:	48 8b 43 10          	mov    0x10(%rbx),%rax
    194a:	8b 80 80 00 00 00    	mov    0x80(%rax),%eax
    1950:	39 d0                	cmp    %edx,%eax
    1952:	74 e4                	je     1938 <disruptor_thread+0xb8>
            int claim = me->end;
    1954:	41 8b 06             	mov    (%r14),%eax
            int changed = me->end;
    1957:	45 8b 26             	mov    (%r14),%r12d
            int change = (changed + 1) % me->size;
    195a:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    195f:	48 98                	cltq
    1961:	48 99                	cqto
    1963:	49 f7 bd 08 01 00 00 	idivq  0x108(%r13)
            while (!__atomic_compare_exchange (&me->end, &changed, &change, 0, __ATOMIC_RELEASE, __ATOMIC_RELAXED)) {
    196a:	44 89 e0             	mov    %r12d,%eax
    196d:	f0 41 0f b1 16       	lock cmpxchg %edx,(%r14)
    1972:	41 89 c4             	mov    %eax,%r12d
    1975:	0f 85 dc 00 00 00    	jne    1a57 <disruptor_thread+0x1d7>
            clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    197b:	49 63 c4             	movslq %r12d,%rax
    197e:	49 8b 75 18          	mov    0x18(%r13),%rsi
    1982:	bf 04 00 00 00       	mov    $0x4,%edi
    1987:	4c 8d 3c 40          	lea    (%rax,%rax,2),%r15
    198b:	49 c1 e7 07          	shl    $0x7,%r15
    198f:	4c 01 fe             	add    %r15,%rsi
    1992:	e8 a9 f7 ff ff       	call   1140 <clock_gettime@plt>
            next = (changed + 1) % me->size;
    1997:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    199c:	48 98                	cltq
    199e:	48 99                	cqto
    19a0:	49 f7 bd 08 01 00 00 	idivq  0x108(%r13)
            me->data[changed].complete[1] = 1;
    19a7:	49 8b 45 18          	mov    0x18(%r13),%rax
    19ab:	4a 8b 84 38 00 01 00 00 	mov    0x100(%rax,%r15,1),%rax
    19b3:	c7 40 04 01 00 00 00 	movl   $0x1,0x4(%rax)
    19ba:	e9 79 ff ff ff       	jmp    1938 <disruptor_thread+0xb8>
    19bf:	90                   	nop
    19c0:	48 8d 3d ca 06 00 00 	lea    0x6ca(%rip),%rdi        # 2091 <_IO_stdin_used+0x91>
    19c7:	e8 64 f7 ff ff       	call   1130 <puts@plt>
    struct Thread *sender = data->sender;
    19cc:	48 8b 43 08          	mov    0x8(%rbx),%rax
    struct Snapshot * rdata = sender->data;
    19d0:	4c 8b 78 18          	mov    0x18(%rax),%r15
    int cachedEnd = sender->end;
    19d4:	4c 8d b0 00 01 00 00 	lea    0x100(%rax),%r14
    19db:	8b 88 00 01 00 00    	mov    0x100(%rax),%ecx
    int size = data->size;
    19e1:	8b 83 08 01 00 00    	mov    0x108(%rbx),%eax
    int cachedStart = data->start;
    19e7:	44 8b ab 80 00 00 00 	mov    0x80(%rbx),%r13d
    int size = data->size;
    19ee:	89 45 cc             	mov    %eax,-0x34(%rbp)
    while (data->running == 1) {
    19f1:	8b 83 10 01 00 00    	mov    0x110(%rbx),%eax
    19f7:	83 f8 01             	cmp    $0x1,%eax
    19fa:	0f 85 d8 fe ff ff    	jne    18d8 <disruptor_thread+0x58>
      if (cachedEnd == cachedStart) {
    1a00:	44 39 e9             	cmp    %r13d,%ecx
    1a03:	74 3f                	je     1a44 <disruptor_thread+0x1c4>
          clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[cachedStart].end);
    1a05:	49 63 c5             	movslq %r13d,%rax
    1a08:	bf 04 00 00 00       	mov    $0x4,%edi
    1a0d:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
    1a11:	49 c1 e4 07          	shl    $0x7,%r12
    1a15:	4d 01 fc             	add    %r15,%r12
    1a18:	49 8d b4 24 80 00 00 00 	lea    0x80(%r12),%rsi
    1a20:	e8 1b f7 ff ff       	call   1140 <clock_gettime@plt>
          rdata[cachedStart].complete[0] = 1;
    1a25:	49 8b 84 24 00 01 00 00 	mov    0x100(%r12),%rax
    1a2d:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
          cachedStart = (cachedStart + 1) % size;
    1a33:	41 8d 45 01          	lea    0x1(%r13),%eax
    1a37:	99                   	cltd
    1a38:	f7 7d cc             	idivl  -0x34(%rbp)
          data->start = cachedStart;
    1a3b:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
          cachedStart = (cachedStart + 1) % size;
    1a41:	41 89 d5             	mov    %edx,%r13d
          cachedEnd = sender->end;
    1a44:	41 8b 0e             	mov    (%r14),%ecx
    while (data->running == 1) {
    1a47:	8b 83 10 01 00 00    	mov    0x110(%rbx),%eax
    1a4d:	83 f8 01             	cmp    $0x1,%eax
    1a50:	74 ae                	je     1a00 <disruptor_thread+0x180>
    1a52:	e9 81 fe ff ff       	jmp    18d8 <disruptor_thread+0x58>
              changed = me->end;
    1a57:	41 8b 0e             	mov    (%r14),%ecx
              change = (changed + 1) % me->size;
    1a5a:	8d 41 01             	lea    0x1(%rcx),%eax
    1a5d:	48 98                	cltq
    1a5f:	48 99                	cqto
    1a61:	49 f7 bd 08 01 00 00 	idivq  0x108(%r13)
            while (!__atomic_compare_exchange (&me->end, &changed, &change, 0, __ATOMIC_RELEASE, __ATOMIC_RELAXED)) {
    1a68:	89 c8                	mov    %ecx,%eax
    1a6a:	f0 41 0f b1 16       	lock cmpxchg %edx,(%r14)
    1a6f:	75 e6                	jne    1a57 <disruptor_thread+0x1d7>
    1a71:	41 89 c4             	mov    %eax,%r12d
    1a74:	e9 02 ff ff ff       	jmp    197b <disruptor_thread+0xfb>
    1a79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001a80 <min>:
int min(long a, long b) {
    1a80:	f3 0f 1e fa          	endbr64
    1a84:	55                   	push   %rbp
    1a85:	48 89 e5             	mov    %rsp,%rbp
    1a88:	ff 15 5a 25 00 00    	call   *0x255a(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
  if (a < b) return a;
    1a8e:	48 39 f7             	cmp    %rsi,%rdi
    1a91:	7c 02                	jl     1a95 <min+0x15>
  if (b < a) return b;
    1a93:	7f 0b                	jg     1aa0 <min+0x20>
  if (a < b) return a;
    1a95:	89 f8                	mov    %edi,%eax
}
    1a97:	5d                   	pop    %rbp
    1a98:	c3                   	ret
    1a99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (b < a) return b;
    1aa0:	89 f0                	mov    %esi,%eax
}
    1aa2:	5d                   	pop    %rbp
    1aa3:	c3                   	ret
    1aa4:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    1aae:	66 90                	xchg   %ax,%ax

0000000000001ab0 <atexit>:
    1ab0:	f3 0f 1e fa          	endbr64
    1ab4:	48 8b 15 4d 25 00 00 	mov    0x254d(%rip),%rdx        # 4008 <__dso_handle>
    1abb:	31 f6                	xor    %esi,%esi
    1abd:	e9 0e f7 ff ff       	jmp    11d0 <__cxa_atexit@plt>
    1ac2:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    1acc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000001ad0 <__stack_chk_fail_local>:
    1ad0:	f3 0f 1e fa          	endbr64
    1ad4:	50                   	push   %rax
    1ad5:	58                   	pop    %rax
    1ad6:	48 83 ec 08          	sub    $0x8,%rsp
    1ada:	e8 71 f6 ff ff       	call   1150 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000001ae0 <_fini>:
    1ae0:	f3 0f 1e fa          	endbr64
    1ae4:	48 83 ec 08          	sub    $0x8,%rsp
    1ae8:	48 83 c4 08          	add    $0x8,%rsp
    1aec:	c3                   	ret
