
disruptor-realtime:     file format elf64-x86-64


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
    1020:	ff 35 32 2f 00 00    	push   0x2f32(%rip)        # 3f58 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:	ff 25 34 2f 00 00    	jmp    *0x2f34(%rip)        # 3f60 <_GLOBAL_OFFSET_TABLE_+0x10>
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
    1124:	ff 25 3e 2e 00 00    	jmp    *0x2e3e(%rip)        # 3f68 <pthread_setaffinity_np@GLIBC_2.34>
    112a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001130 <puts@plt>:
    1130:	f3 0f 1e fa          	endbr64
    1134:	ff 25 36 2e 00 00    	jmp    *0x2e36(%rip)        # 3f70 <puts@GLIBC_2.2.5>
    113a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001140 <clock_gettime@plt>:
    1140:	f3 0f 1e fa          	endbr64
    1144:	ff 25 2e 2e 00 00    	jmp    *0x2e2e(%rip)        # 3f78 <clock_gettime@GLIBC_2.17>
    114a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001150 <__stack_chk_fail@plt>:
    1150:	f3 0f 1e fa          	endbr64
    1154:	ff 25 26 2e 00 00    	jmp    *0x2e26(%rip)        # 3f80 <__stack_chk_fail@GLIBC_2.4>
    115a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001160 <nanosleep@plt>:
    1160:	f3 0f 1e fa          	endbr64
    1164:	ff 25 1e 2e 00 00    	jmp    *0x2e1e(%rip)        # 3f88 <nanosleep@GLIBC_2.2.5>
    116a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001170 <pthread_attr_setschedpolicy@plt>:
    1170:	f3 0f 1e fa          	endbr64
    1174:	ff 25 16 2e 00 00    	jmp    *0x2e16(%rip)        # 3f90 <pthread_attr_setschedpolicy@GLIBC_2.2.5>
    117a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001180 <calloc@plt>:
    1180:	f3 0f 1e fa          	endbr64
    1184:	ff 25 0e 2e 00 00    	jmp    *0x2e0e(%rip)        # 3f98 <calloc@GLIBC_2.2.5>
    118a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001190 <syscall@plt>:
    1190:	f3 0f 1e fa          	endbr64
    1194:	ff 25 06 2e 00 00    	jmp    *0x2e06(%rip)        # 3fa0 <syscall@GLIBC_2.2.5>
    119a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011a0 <__printf_chk@plt>:
    11a0:	f3 0f 1e fa          	endbr64
    11a4:	ff 25 fe 2d 00 00    	jmp    *0x2dfe(%rip)        # 3fa8 <__printf_chk@GLIBC_2.3.4>
    11aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011b0 <pthread_create@plt>:
    11b0:	f3 0f 1e fa          	endbr64
    11b4:	ff 25 f6 2d 00 00    	jmp    *0x2df6(%rip)        # 3fb0 <pthread_create@GLIBC_2.34>
    11ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011c0 <perror@plt>:
    11c0:	f3 0f 1e fa          	endbr64
    11c4:	ff 25 ee 2d 00 00    	jmp    *0x2dee(%rip)        # 3fb8 <perror@GLIBC_2.2.5>
    11ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011d0 <pthread_attr_setschedparam@plt>:
    11d0:	f3 0f 1e fa          	endbr64
    11d4:	ff 25 e6 2d 00 00    	jmp    *0x2de6(%rip)        # 3fc0 <pthread_attr_setschedparam@GLIBC_2.2.5>
    11da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011e0 <exit@plt>:
    11e0:	f3 0f 1e fa          	endbr64
    11e4:	ff 25 de 2d 00 00    	jmp    *0x2dde(%rip)        # 3fc8 <exit@GLIBC_2.2.5>
    11ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011f0 <pthread_join@plt>:
    11f0:	f3 0f 1e fa          	endbr64
    11f4:	ff 25 d6 2d 00 00    	jmp    *0x2dd6(%rip)        # 3fd0 <pthread_join@GLIBC_2.34>
    11fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000001200 <main>:
  } 
  printf("Finished\n");
  return 0;
}

int main() {
    1200:	f3 0f 1e fa          	endbr64
    1204:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    1206:	ba 00 00 04 00       	mov    $0x40000,%edx
    120b:	bf 01 00 00 00       	mov    $0x1,%edi
    1210:	48 8d 35 71 0e 00 00 	lea    0xe71(%rip),%rsi        # 2088 <_IO_stdin_used+0x88>
    1217:	41 56                	push   %r14
  printf("Readers count %d\n", readers_count);
  int thread_count = groups * (readers_count + 1);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1219:	41 bf 01 00 00 00    	mov    $0x1,%r15d
int main() {
    121f:	41 55                	push   %r13
    1221:	41 54                	push   %r12
    1223:	55                   	push   %rbp
    1224:	53                   	push   %rbx
    1225:	48 83 ec 68          	sub    $0x68,%rsp
    1229:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1232:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    1237:	31 c0                	xor    %eax,%eax
    1239:	e8 62 ff ff ff       	call   11a0 <__printf_chk@plt>
    123e:	ba 02 00 00 00       	mov    $0x2,%edx
    1243:	48 8d 35 5c 0e 00 00 	lea    0xe5c(%rip),%rsi        # 20a6 <_IO_stdin_used+0xa6>
    124a:	31 c0                	xor    %eax,%eax
    124c:	bf 01 00 00 00       	mov    $0x1,%edi
    1251:	e8 4a ff ff ff       	call   11a0 <__printf_chk@plt>
    1256:	ba 02 00 00 00       	mov    $0x2,%edx
    125b:	48 8d 35 54 0e 00 00 	lea    0xe54(%rip),%rsi        # 20b6 <_IO_stdin_used+0xb6>
    1262:	31 c0                	xor    %eax,%eax
    1264:	bf 01 00 00 00       	mov    $0x1,%edi
    1269:	e8 32 ff ff ff       	call   11a0 <__printf_chk@plt>
    126e:	ba 06 00 00 00       	mov    $0x6,%edx
    1273:	48 8d 35 4e 0e 00 00 	lea    0xe4e(%rip),%rsi        # 20c8 <_IO_stdin_used+0xc8>
    127a:	31 c0                	xor    %eax,%eax
    127c:	bf 01 00 00 00       	mov    $0x1,%edi
    1281:	e8 1a ff ff ff       	call   11a0 <__printf_chk@plt>
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1286:	be 50 00 00 00       	mov    $0x50,%esi
    128b:	bf 06 00 00 00       	mov    $0x6,%edi
    1290:	e8 eb fe ff ff       	call   1180 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1295:	be 38 00 00 00       	mov    $0x38,%esi
    129a:	bf 06 00 00 00       	mov    $0x6,%edi
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    129f:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12a2:	e8 d9 fe ff ff       	call   1180 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12a7:	be 08 00 00 00       	mov    $0x8,%esi
    12ac:	bf 06 00 00 00       	mov    $0x6,%edi
    12b1:	49 89 dd             	mov    %rbx,%r13
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12b4:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12b9:	e8 c2 fe ff ff       	call   1180 <calloc@plt>
    12be:	49 89 c4             	mov    %rax,%r12
   /* Set affinity mask to include CPUs 0 to 7. */
  int cores = 12;
  // 0, 3, 6
  int curcore = 0;
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 3; 
    12c1:	45 8d 77 ff          	lea    -0x1(%r15),%r14d
    int receiver = sender + 1; 
    int receiver2 = receiver + 1; 
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12c5:	be 80 00 00 00       	mov    $0x80,%esi
    12ca:	bf 01 00 00 00       	mov    $0x1,%edi
    int sender = x * 3; 
    12cf:	44 89 74 24 08       	mov    %r14d,0x8(%rsp)
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12d4:	e8 a7 fe ff ff       	call   1180 <calloc@plt>
    CPU_ZERO(sendercpu);
    for (int j = 0 ; j < cores; j++) {
      // printf("assigning sender %d to core %d\n", sender, j);
      CPU_SET(j, sendercpu);
    }
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12d9:	be 80 00 00 00       	mov    $0x80,%esi
    12de:	bf 01 00 00 00       	mov    $0x1,%edi
      CPU_SET(j, sendercpu);
    12e3:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12ea:	48 89 c5             	mov    %rax,%rbp
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12ed:	e8 8e fe ff ff       	call   1180 <calloc@plt>
    for (int j = 0 ; j < cores ; j++) {
      // printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    }
     
    thread_data[sender].thread_index = sender;
    12f2:	45 89 75 00          	mov    %r14d,0x0(%r13)
    thread_data[sender].cpu_set = sendercpu;
    thread_data[sender].mode = WRITER;
    thread_data[sender].running = 1;
    thread_data[sender].size = buffer_size;
    thread_data[sender].readers = calloc(readers_count, sizeof(struct Thread*));
    12f6:	be 08 00 00 00       	mov    $0x8,%esi
    12fb:	bf 02 00 00 00       	mov    $0x2,%edi
      CPU_SET(j, receivercpu);
    1300:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    thread_data[sender].cpu_set = sendercpu;
    1307:	49 89 6d 38          	mov    %rbp,0x38(%r13)
    thread_data[sender].mode = WRITER;
    130b:	41 c7 45 20 00 00 00 00 	movl   $0x0,0x20(%r13)
    thread_data[sender].size = buffer_size;
    1313:	49 c7 45 28 00 00 04 00 	movq   $0x40000,0x28(%r13)
    thread_data[sender].running = 1;
    131b:	41 c7 45 30 01 00 00 00 	movl   $0x1,0x30(%r13)
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1323:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    thread_data[sender].readers = calloc(readers_count, sizeof(struct Thread*));
    1328:	e8 53 fe ff ff       	call   1180 <calloc@plt>
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    132d:	be 20 00 00 00       	mov    $0x20,%esi
    1332:	bf 00 00 04 00       	mov    $0x40000,%edi
    thread_data[sender].readers = calloc(readers_count, sizeof(struct Thread*));
    1337:	49 89 45 40          	mov    %rax,0x40(%r13)
    133b:	48 89 04 24          	mov    %rax,(%rsp)
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    133f:	e8 3c fe ff ff       	call   1180 <calloc@plt>
    1344:	49 89 45 10          	mov    %rax,0x10(%r13)
    1348:	48 89 c5             	mov    %rax,%rbp
    for (int n = 0 ; n < buffer_size ; n++) {
    134b:	4c 8d 70 10          	lea    0x10(%rax),%r14
    134f:	48 81 c5 10 00 80 00 	add    $0x800010,%rbp
    1356:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      thread_data[sender].data[n].end = calloc(readers_count, sizeof(struct timespec));
    1360:	be 10 00 00 00       	mov    $0x10,%esi
    1365:	bf 02 00 00 00       	mov    $0x2,%edi
    for (int n = 0 ; n < buffer_size ; n++) {
    136a:	49 83 c6 20          	add    $0x20,%r14
      thread_data[sender].data[n].end = calloc(readers_count, sizeof(struct timespec));
    136e:	e8 0d fe ff ff       	call   1180 <calloc@plt>
      thread_data[sender].data[n].complete = calloc(readers_count, sizeof(int));
    1373:	be 04 00 00 00       	mov    $0x4,%esi
    1378:	bf 02 00 00 00       	mov    $0x2,%edi
      thread_data[sender].data[n].end = calloc(readers_count, sizeof(struct timespec));
    137d:	49 89 46 e0          	mov    %rax,-0x20(%r14)
      thread_data[sender].data[n].complete = calloc(readers_count, sizeof(int));
    1381:	e8 fa fd ff ff       	call   1180 <calloc@plt>
    1386:	49 89 46 e8          	mov    %rax,-0x18(%r14)
    for (int n = 0 ; n < buffer_size ; n++) {
    138a:	4c 39 f5             	cmp    %r14,%rbp
    138d:	75 d1                	jne    1360 <main+0x160>
    thread_data[sender].readers_count = readers_count;
    // printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
      thread_data[j].thread_index = j;
      thread_data[j].reader_index = receiver_index;
      thread_data[j].cpu_set = receivercpu;
    138f:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
      thread_data[j].running = 1;
      thread_data[j].mode = READER;
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    1394:	48 8b 34 24          	mov    (%rsp),%rsi
      thread_data[j].thread_index = j;
    1398:	49 8d 45 50          	lea    0x50(%r13),%rax
    139c:	31 c9                	xor    %ecx,%ecx
    thread_data[sender].readers_count = readers_count;
    139e:	41 c7 45 48 02 00 00 00 	movl   $0x2,0x48(%r13)
    13a6:	44 89 fa             	mov    %r15d,%edx
    13a9:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].running = 1;
    13ae:	41 c7 85 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r13)
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    13b9:	48 89 06             	mov    %rax,(%rsi)
    13bc:	48 8d 35 8d 0c 00 00 	lea    0xc8d(%rip),%rsi        # 2050 <_IO_stdin_used+0x50>
    13c3:	31 c0                	xor    %eax,%eax
      thread_data[j].thread_index = j;
    13c5:	45 89 7d 50          	mov    %r15d,0x50(%r13)
      thread_data[j].reader_index = receiver_index;
    13c9:	41 c7 85 9c 00 00 00 00 00 00 00 	movl   $0x0,0x9c(%r13)
      thread_data[j].cpu_set = receivercpu;
    13d4:	4d 89 b5 88 00 00 00 	mov    %r14,0x88(%r13)
      thread_data[j].mode = READER;
    13db:	41 c7 45 70 01 00 00 00 	movl   $0x1,0x70(%r13)
      thread_data[j].size = buffer_size;
    13e3:	49 c7 45 78 00 00 04 00 	movq   $0x40000,0x78(%r13)
      thread_data[j].sender = &thread_data[sender];
    13eb:	4d 89 6d 58          	mov    %r13,0x58(%r13)
    13ef:	e8 ac fd ff ff       	call   11a0 <__printf_chk@plt>
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    13f4:	49 8b 4d 40          	mov    0x40(%r13),%rcx
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
    13f8:	41 8d 57 01          	lea    0x1(%r15),%edx
      thread_data[j].thread_index = j;
    13fc:	49 8d 85 a0 00 00 00 	lea    0xa0(%r13),%rax
    1403:	41 89 95 a0 00 00 00 	mov    %edx,0xa0(%r13)
    140a:	48 8d 35 3f 0c 00 00 	lea    0xc3f(%rip),%rsi        # 2050 <_IO_stdin_used+0x50>
    1411:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].running = 1;
    1416:	41 c7 85 d0 00 00 00 01 00 00 00 	movl   $0x1,0xd0(%r13)
      thread_data[j].reader_index = receiver_index;
    1421:	41 c7 85 ec 00 00 00 01 00 00 00 	movl   $0x1,0xec(%r13)
      thread_data[j].cpu_set = receivercpu;
    142c:	4d 89 b5 d8 00 00 00 	mov    %r14,0xd8(%r13)
      thread_data[j].mode = READER;
    1433:	41 c7 85 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%r13)
      thread_data[j].size = buffer_size;
    143e:	49 c7 85 c8 00 00 00 00 00 04 00 	movq   $0x40000,0xc8(%r13)
      thread_data[j].sender = &thread_data[sender];
    1449:	4d 89 ad a8 00 00 00 	mov    %r13,0xa8(%r13)
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    1450:	48 89 41 08          	mov    %rax,0x8(%rcx)
    1454:	b9 01 00 00 00       	mov    $0x1,%ecx
    1459:	31 c0                	xor    %eax,%eax
    145b:	e8 40 fd ff ff       	call   11a0 <__printf_chk@plt>
    1460:	8b 54 24 08          	mov    0x8(%rsp),%edx
    1464:	bf 01 00 00 00       	mov    $0x1,%edi
    1469:	31 c0                	xor    %eax,%eax
    146b:	48 8d 35 6d 0c 00 00 	lea    0xc6d(%rip),%rsi        # 20df <_IO_stdin_used+0xdf>
    1472:	e8 29 fd ff ff       	call   11a0 <__printf_chk@plt>
      printf("Creating receiver thread %d %d\n", j, receiver_index);
    }
    printf("Creating sender thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    1477:	0f ae f0             	mfence
  for (int x = 0 ; x < groups ; x++) {
    147a:	49 81 c5 f0 00 00 00 	add    $0xf0,%r13
    1481:	41 83 ff 04          	cmp    $0x4,%r15d
    1485:	74 0b                	je     1492 <main+0x292>
    1487:	41 bf 04 00 00 00    	mov    $0x4,%r15d
    148d:	e9 2f fe ff ff       	jmp    12c1 <main+0xc1>
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 49;
    1492:	c7 44 24 2c 31 00 00 00 	movl   $0x31,0x2c(%rsp)
  for (int x = 0 ; x < groups ; x++) {
    149a:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
  param.sched_priority = 49;
    149f:	49 89 de             	mov    %rbx,%r14
    14a2:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
    14a7:	48 c7 04 24 03 00 00 00 	movq   $0x3,(%rsp)
    int sender = x * 3; 
    int receiver = sender + 1; 
    
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
    14af:	48 8b 04 24          	mov    (%rsp),%rax
    14b3:	49 8d 6d 38          	lea    0x38(%r13),%rbp
    14b7:	4c 8d 78 fe          	lea    -0x2(%rax),%r15
    14bb:	48 8d 35 38 0c 00 00 	lea    0xc38(%rip),%rsi        # 20fa <_IO_stdin_used+0xfa>
    14c2:	bf 01 00 00 00       	mov    $0x1,%edi
    14c7:	31 c0                	xor    %eax,%eax
    14c9:	44 89 fa             	mov    %r15d,%edx
    14cc:	e8 cf fc ff ff       	call   11a0 <__printf_chk@plt>
      printf("Creating receiver thread %d\n", j);
      
      int ret = pthread_attr_setschedpolicy(&attr[j], SCHED_RR);
    14d1:	be 02 00 00 00       	mov    $0x2,%esi
    14d6:	48 89 ef             	mov    %rbp,%rdi
    14d9:	e8 92 fc ff ff       	call   1170 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    14de:	85 c0                	test   %eax,%eax
    14e0:	0f 85 e2 02 00 00    	jne    17c8 <main+0x5c8>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    14e6:	48 8d 74 24 2c       	lea    0x2c(%rsp),%rsi
    14eb:	48 89 ef             	mov    %rbp,%rdi
    14ee:	e8 dd fc ff ff       	call   11d0 <pthread_attr_setschedparam@plt>
      if (ret) {
    14f3:	85 c0                	test   %eax,%eax
    14f5:	0f 85 e8 02 00 00    	jne    17e3 <main+0x5e3>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    14fb:	4b 8d 0c bf          	lea    (%r15,%r15,4),%rcx
    14ff:	4b 8d 3c fc          	lea    (%r12,%r15,8),%rdi
    1503:	48 89 ee             	mov    %rbp,%rsi
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
    1506:	48 83 c5 38          	add    $0x38,%rbp
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    150a:	48 c1 e1 04          	shl    $0x4,%rcx
    150e:	48 8d 15 db 03 00 00 	lea    0x3db(%rip),%rdx        # 18f0 <disruptor_thread>
    1515:	48 01 d9             	add    %rbx,%rcx
    1518:	e8 93 fc ff ff       	call   11b0 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    151d:	4b 8b 3c fc          	mov    (%r12,%r15,8),%rdi
    1521:	be 08 00 00 00       	mov    $0x8,%esi
    1526:	49 8b 96 88 00 00 00 	mov    0x88(%r14),%rdx
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
    152d:	49 83 c7 01          	add    $0x1,%r15
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    1531:	e8 ea fb ff ff       	call   1120 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
    1536:	4c 39 3c 24          	cmp    %r15,(%rsp)
    153a:	0f 85 7b ff ff ff    	jne    14bb <main+0x2bb>
    }
      
      int ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_RR);
    1540:	be 02 00 00 00       	mov    $0x2,%esi
    1545:	4c 89 ef             	mov    %r13,%rdi
    1548:	e8 23 fc ff ff       	call   1170 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    154d:	85 c0                	test   %eax,%eax
    154f:	0f 85 73 02 00 00    	jne    17c8 <main+0x5c8>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 49;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1555:	48 8d 74 24 28       	lea    0x28(%rsp),%rsi
    155a:	4c 89 ef             	mov    %r13,%rdi
      param2.sched_priority = 49;
    155d:	c7 44 24 28 31 00 00 00 	movl   $0x31,0x28(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1565:	e8 66 fc ff ff       	call   11d0 <pthread_attr_setschedparam@plt>
      if (ret) {
    156a:	85 c0                	test   %eax,%eax
    156c:	0f 85 71 02 00 00    	jne    17e3 <main+0x5e3>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    1572:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    1577:	4c 89 f1             	mov    %r14,%rcx
    157a:	4c 89 ee             	mov    %r13,%rsi
    157d:	48 8d 15 6c 03 00 00 	lea    0x36c(%rip),%rdx        # 18f0 <disruptor_thread>
  for (int x = 0 ; x < groups ; x++) {
    1584:	49 81 c5 a8 00 00 00 	add    $0xa8,%r13
    158b:	49 81 c6 f0 00 00 00 	add    $0xf0,%r14
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    1592:	4c 89 ff             	mov    %r15,%rdi
  for (int x = 0 ; x < groups ; x++) {
    1595:	49 83 c7 18          	add    $0x18,%r15
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    1599:	e8 12 fc ff ff       	call   11b0 <pthread_create@plt>
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    159e:	49 8b 7f e8          	mov    -0x18(%r15),%rdi
    15a2:	be 08 00 00 00       	mov    $0x8,%esi
    15a7:	49 8b 96 48 ff ff ff 	mov    -0xb8(%r14),%rdx
    15ae:	e8 6d fb ff ff       	call   1120 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < groups ; x++) {
    15b3:	48 83 3c 24 06       	cmpq   $0x6,(%rsp)
    15b8:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    15bd:	74 0d                	je     15cc <main+0x3cc>
    15bf:	48 c7 04 24 06 00 00 00 	movq   $0x6,(%rsp)
    15c7:	e9 e3 fe ff ff       	jmp    14af <main+0x2af>
    // printf("Waiting before starting next disruptor %ld ns\n", TICK);
    // nanosleep(&preempt , &rem2);
    }
  int seconds = 10;
  struct timespec rem2;
  struct timespec preempt = {
    15cc:	66 0f 6f 05 ec 0b 00 00 	movdqa 0xbec(%rip),%xmm0        # 21c0 <_IO_stdin_used+0x1c0>
    15d4:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < groups ; x++) {
    void * res1;
    void * res2;
    int sender = x * 3; 
    int receiver = sender + 1; 
    pthread_join(thread[sender], res1);
    15d6:	45 31 ed             	xor    %r13d,%r13d
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    15d9:	31 ed                	xor    %ebp,%ebp
    15db:	ba 0a 00 00 00       	mov    $0xa,%edx
    15e0:	48 8d 35 6b 0b 00 00 	lea    0xb6b(%rip),%rsi        # 2152 <_IO_stdin_used+0x152>
    15e7:	bf 01 00 00 00       	mov    $0x1,%edi
    15ec:	48 83 c3 10          	add    $0x10,%rbx
  struct timespec preempt = {
    15f0:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    15f5:	4c 8d 3d 6f 0b 00 00 	lea    0xb6f(%rip),%r15        # 216b <_IO_stdin_used+0x16b>
    15fc:	e8 9f fb ff ff       	call   11a0 <__printf_chk@plt>
  nanosleep(&preempt , &rem2);
    1601:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    1606:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    160b:	e8 50 fb ff ff       	call   1160 <nanosleep@plt>
    thread_data[sender].running = 0;
    1610:	c7 43 20 00 00 00 00 	movl   $0x0,0x20(%rbx)
    pthread_join(thread[sender], res1);
    1617:	49 8b 3c 24          	mov    (%r12),%rdi
    161b:	4c 89 ee             	mov    %r13,%rsi
      thread_data[j].running = 0;
    161e:	c7 43 70 00 00 00 00 	movl   $0x0,0x70(%rbx)
    1625:	c7 83 c0 00 00 00 00 00 00 00 	movl   $0x0,0xc0(%rbx)
    thread_data[sender].running = 0;
    162f:	c7 83 10 01 00 00 00 00 00 00 	movl   $0x0,0x110(%rbx)
      thread_data[j].running = 0;
    1639:	c7 83 60 01 00 00 00 00 00 00 	movl   $0x0,0x160(%rbx)
    1643:	c7 83 b0 01 00 00 00 00 00 00 	movl   $0x0,0x1b0(%rbx)
    pthread_join(thread[sender], res1);
    164d:	e8 9e fb ff ff       	call   11f0 <pthread_join@plt>
      pthread_join(thread[j], res2);
    1652:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    1657:	48 89 ee             	mov    %rbp,%rsi
    165a:	e8 91 fb ff ff       	call   11f0 <pthread_join@plt>
    165f:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    1664:	48 89 ee             	mov    %rbp,%rsi
    1667:	e8 84 fb ff ff       	call   11f0 <pthread_join@plt>
    pthread_join(thread[sender], res1);
    166c:	49 8b 7c 24 18       	mov    0x18(%r12),%rdi
    1671:	4c 89 ee             	mov    %r13,%rsi
    1674:	4c 8d 2d 06 0b 00 00 	lea    0xb06(%rip),%r13        # 2181 <_IO_stdin_used+0x181>
    167b:	e8 70 fb ff ff       	call   11f0 <pthread_join@plt>
      pthread_join(thread[j], res2);
    1680:	49 8b 7c 24 20       	mov    0x20(%r12),%rdi
    1685:	48 89 ee             	mov    %rbp,%rsi
    1688:	e8 63 fb ff ff       	call   11f0 <pthread_join@plt>
    168d:	49 8b 7c 24 28       	mov    0x28(%r12),%rdi
    1692:	48 89 ee             	mov    %rbp,%rsi
    1695:	45 31 e4             	xor    %r12d,%r12d
    1698:	e8 53 fb ff ff       	call   11f0 <pthread_join@plt>
    169d:	44 89 e2             	mov    %r12d,%edx
    16a0:	4c 89 fe             	mov    %r15,%rsi
    16a3:	bf 01 00 00 00       	mov    $0x1,%edi
    16a8:	31 c0                	xor    %eax,%eax
    16aa:	e8 f1 fa ff ff       	call   11a0 <__printf_chk@plt>
  }
  
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 3; 
    int receiver = sender + 1;
    int incompletes = 0;
    16af:	45 31 f6             	xor    %r14d,%r14d
    16b2:	31 ed                	xor    %ebp,%ebp
    16b4:	eb 1a                	jmp    16d0 <main+0x4d0>
    16b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    printf("Inspecting sender %d\n", sender);
    for (int y = 0 ; y < buffer_size; y++) {
      int compcount = 0;
      for (int n = 0 ; n < readers_count ; n++) {
	  if (thread_data[sender].data[y].complete[n] == 1) {
    16c0:	8b 40 04             	mov    0x4(%rax),%eax
    for (int y = 0 ; y < buffer_size; y++) {
    16c3:	48 83 c5 20          	add    $0x20,%rbp
    16c7:	48 81 fd 00 00 80 00 	cmp    $0x800000,%rbp
    16ce:	74 3d                	je     170d <main+0x50d>
	  if (thread_data[sender].data[y].complete[n] == 1) {
    16d0:	48 8b 13             	mov    (%rbx),%rdx
    16d3:	48 01 ea             	add    %rbp,%rdx
    16d6:	48 8b 42 18          	mov    0x18(%rdx),%rax
    16da:	8b 08                	mov    (%rax),%ecx
    16dc:	83 f9 01             	cmp    $0x1,%ecx
    16df:	75 df                	jne    16c0 <main+0x4c0>
    16e1:	8b 48 04             	mov    0x4(%rax),%ecx
    16e4:	83 f9 01             	cmp    $0x1,%ecx
    16e7:	75 da                	jne    16c3 <main+0x4c3>

      }
        if (compcount == readers_count) {
	  for (int n = 0 ; n < readers_count ; n++) {

	    if (thread_data[sender].data[y].complete[n] == 1) {
    16e9:	8b 08                	mov    (%rax),%ecx
    16eb:	83 f9 01             	cmp    $0x1,%ecx
    16ee:	74 50                	je     1740 <main+0x540>
    16f0:	8b 40 04             	mov    0x4(%rax),%eax
	      struct timespec end = thread_data[sender].data[y].end[n];
	      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
	      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
	      printf("rb %d %d Read %ld %ld\n", sender, n, seconds, seconds2);
	    } else {
	      incompletes++;
    16f3:	41 83 c6 01          	add    $0x1,%r14d
	    if (thread_data[sender].data[y].complete[n] == 1) {
    16f7:	83 f8 01             	cmp    $0x1,%eax
    16fa:	74 7c                	je     1778 <main+0x578>
    for (int y = 0 ; y < buffer_size; y++) {
    16fc:	48 83 c5 20          	add    $0x20,%rbp
	      incompletes++;
    1700:	41 83 c6 01          	add    $0x1,%r14d
    for (int y = 0 ; y < buffer_size; y++) {
    1704:	48 81 fd 00 00 80 00 	cmp    $0x800000,%rbp
    170b:	75 c3                	jne    16d0 <main+0x4d0>
    170d:	44 89 f2             	mov    %r14d,%edx
    1710:	48 8d 35 81 0a 00 00 	lea    0xa81(%rip),%rsi        # 2198 <_IO_stdin_used+0x198>
    1717:	bf 01 00 00 00       	mov    $0x1,%edi
    171c:	31 c0                	xor    %eax,%eax
    171e:	e8 7d fa ff ff       	call   11a0 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    1723:	48 81 c3 f0 00 00 00 	add    $0xf0,%rbx
    172a:	41 83 fc 03          	cmp    $0x3,%r12d
    172e:	74 77                	je     17a7 <main+0x5a7>
    1730:	41 bc 03 00 00 00    	mov    $0x3,%r12d
    1736:	e9 62 ff ff ff       	jmp    169d <main+0x49d>
    173b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	      struct timespec end = thread_data[sender].data[y].end[n];
    1740:	48 8b 42 10          	mov    0x10(%rdx),%rax
    1744:	31 c9                	xor    %ecx,%ecx
    1746:	4c 89 ee             	mov    %r13,%rsi
    1749:	bf 01 00 00 00       	mov    $0x1,%edi
	      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    174e:	4c 8b 48 08          	mov    0x8(%rax),%r9
	      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    1752:	4c 8b 00             	mov    (%rax),%r8
    1755:	31 c0                	xor    %eax,%eax
    1757:	4c 2b 4a 08          	sub    0x8(%rdx),%r9
    175b:	4c 2b 02             	sub    (%rdx),%r8
    175e:	44 89 e2             	mov    %r12d,%edx
    1761:	e8 3a fa ff ff       	call   11a0 <__printf_chk@plt>
	    if (thread_data[sender].data[y].complete[n] == 1) {
    1766:	48 8b 13             	mov    (%rbx),%rdx
    1769:	48 01 ea             	add    %rbp,%rdx
    176c:	48 8b 42 18          	mov    0x18(%rdx),%rax
    1770:	8b 40 04             	mov    0x4(%rax),%eax
    1773:	83 f8 01             	cmp    $0x1,%eax
    1776:	75 84                	jne    16fc <main+0x4fc>
	      struct timespec end = thread_data[sender].data[y].end[n];
    1778:	48 8b 42 10          	mov    0x10(%rdx),%rax
    177c:	b9 01 00 00 00       	mov    $0x1,%ecx
    1781:	4c 89 ee             	mov    %r13,%rsi
    1784:	bf 01 00 00 00       	mov    $0x1,%edi
	      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    1789:	4c 8b 48 18          	mov    0x18(%rax),%r9
	      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    178d:	4c 8b 40 10          	mov    0x10(%rax),%r8
    1791:	31 c0                	xor    %eax,%eax
    1793:	4c 2b 4a 08          	sub    0x8(%rdx),%r9
    1797:	4c 2b 02             	sub    (%rdx),%r8
    179a:	44 89 e2             	mov    %r12d,%edx
    179d:	e8 fe f9 ff ff       	call   11a0 <__printf_chk@plt>
    17a2:	e9 1c ff ff ff       	jmp    16c3 <main+0x4c3>

    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    17a7:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    17ac:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    17b5:	75 27                	jne    17de <main+0x5de>
    17b7:	48 83 c4 68          	add    $0x68,%rsp
    17bb:	31 c0                	xor    %eax,%eax
    17bd:	5b                   	pop    %rbx
    17be:	5d                   	pop    %rbp
    17bf:	41 5c                	pop    %r12
    17c1:	41 5d                	pop    %r13
    17c3:	41 5e                	pop    %r14
    17c5:	41 5f                	pop    %r15
    17c7:	c3                   	ret
    17c8:	48 8d 3d 48 09 00 00 	lea    0x948(%rip),%rdi        # 2117 <_IO_stdin_used+0x117>
    17cf:	e8 5c f9 ff ff       	call   1130 <puts@plt>
               exit(1);
    17d4:	bf 01 00 00 00       	mov    $0x1,%edi
    17d9:	e8 02 fa ff ff       	call   11e0 <exit@plt>
}
    17de:	e8 6d f9 ff ff       	call   1150 <__stack_chk_fail@plt>
    17e3:	48 8d 3d 4b 09 00 00 	lea    0x94b(%rip),%rdi        # 2135 <_IO_stdin_used+0x135>
    17ea:	e8 41 f9 ff ff       	call   1130 <puts@plt>
              exit(1);
    17ef:	bf 01 00 00 00       	mov    $0x1,%edi
    17f4:	e8 e7 f9 ff ff       	call   11e0 <exit@plt>
    17f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001800 <_start>:
    1800:	f3 0f 1e fa          	endbr64
    1804:	31 ed                	xor    %ebp,%ebp
    1806:	49 89 d1             	mov    %rdx,%r9
    1809:	5e                   	pop    %rsi
    180a:	48 89 e2             	mov    %rsp,%rdx
    180d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1811:	50                   	push   %rax
    1812:	54                   	push   %rsp
    1813:	45 31 c0             	xor    %r8d,%r8d
    1816:	31 c9                	xor    %ecx,%ecx
    1818:	48 8d 3d e1 f9 ff ff 	lea    -0x61f(%rip),%rdi        # 1200 <main>
    181f:	ff 15 b3 27 00 00    	call   *0x27b3(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1825:	f4                   	hlt
    1826:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001830 <deregister_tm_clones>:
    1830:	48 8d 3d d9 27 00 00 	lea    0x27d9(%rip),%rdi        # 4010 <__TMC_END__>
    1837:	48 8d 05 d2 27 00 00 	lea    0x27d2(%rip),%rax        # 4010 <__TMC_END__>
    183e:	48 39 f8             	cmp    %rdi,%rax
    1841:	74 15                	je     1858 <deregister_tm_clones+0x28>
    1843:	48 8b 05 96 27 00 00 	mov    0x2796(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    184a:	48 85 c0             	test   %rax,%rax
    184d:	74 09                	je     1858 <deregister_tm_clones+0x28>
    184f:	ff e0                	jmp    *%rax
    1851:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1858:	c3                   	ret
    1859:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001860 <register_tm_clones>:
    1860:	48 8d 3d a9 27 00 00 	lea    0x27a9(%rip),%rdi        # 4010 <__TMC_END__>
    1867:	48 8d 35 a2 27 00 00 	lea    0x27a2(%rip),%rsi        # 4010 <__TMC_END__>
    186e:	48 29 fe             	sub    %rdi,%rsi
    1871:	48 89 f0             	mov    %rsi,%rax
    1874:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1878:	48 c1 f8 03          	sar    $0x3,%rax
    187c:	48 01 c6             	add    %rax,%rsi
    187f:	48 d1 fe             	sar    %rsi
    1882:	74 14                	je     1898 <register_tm_clones+0x38>
    1884:	48 8b 05 65 27 00 00 	mov    0x2765(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    188b:	48 85 c0             	test   %rax,%rax
    188e:	74 08                	je     1898 <register_tm_clones+0x38>
    1890:	ff e0                	jmp    *%rax
    1892:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1898:	c3                   	ret
    1899:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018a0 <__do_global_dtors_aux>:
    18a0:	f3 0f 1e fa          	endbr64
    18a4:	80 3d 65 27 00 00 00 	cmpb   $0x0,0x2765(%rip)        # 4010 <__TMC_END__>
    18ab:	75 2b                	jne    18d8 <__do_global_dtors_aux+0x38>
    18ad:	55                   	push   %rbp
    18ae:	48 83 3d 42 27 00 00 00 	cmpq   $0x0,0x2742(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    18b6:	48 89 e5             	mov    %rsp,%rbp
    18b9:	74 0c                	je     18c7 <__do_global_dtors_aux+0x27>
    18bb:	48 8b 3d 46 27 00 00 	mov    0x2746(%rip),%rdi        # 4008 <__dso_handle>
    18c2:	e8 49 f8 ff ff       	call   1110 <__cxa_finalize@plt>
    18c7:	e8 64 ff ff ff       	call   1830 <deregister_tm_clones>
    18cc:	c6 05 3d 27 00 00 01 	movb   $0x1,0x273d(%rip)        # 4010 <__TMC_END__>
    18d3:	5d                   	pop    %rbp
    18d4:	c3                   	ret
    18d5:	0f 1f 00             	nopl   (%rax)
    18d8:	c3                   	ret
    18d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018e0 <frame_dummy>:
    18e0:	f3 0f 1e fa          	endbr64
    18e4:	e9 77 ff ff ff       	jmp    1860 <register_tm_clones>
    18e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018f0 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    18f0:	f3 0f 1e fa          	endbr64
    18f4:	55                   	push   %rbp
    18f5:	53                   	push   %rbx
    18f6:	48 89 fb             	mov    %rdi,%rbx
  printf("deadline thread started [%ld]\n", gettid());
    18f9:	bf ba 00 00 00       	mov    $0xba,%edi
void * disruptor_thread(void * arg) {
    18fe:	48 83 ec 48          	sub    $0x48,%rsp
  attr.sched_runtime = 200L * 1000L * 1000L;
    1902:	66 0f 6f 05 a6 08 00 00 	movdqa 0x8a6(%rip),%xmm0        # 21b0 <_IO_stdin_used+0x1b0>
void * disruptor_thread(void * arg) {
    190a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1913:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    1918:	31 c0                	xor    %eax,%eax
  attr.size = sizeof(attr);
    191a:	48 8b 05 87 08 00 00 	mov    0x887(%rip),%rax        # 21a8 <_IO_stdin_used+0x1a8>
  attr.sched_flags = 0;
    1921:	48 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%rsp)
  attr.sched_runtime = 200L * 1000L * 1000L;
    192a:	0f 11 44 24 18       	movups %xmm0,0x18(%rsp)
  attr.size = sizeof(attr);
    192f:	48 89 04 24          	mov    %rax,(%rsp)
  printf("deadline thread started [%ld]\n", gettid());
    1933:	31 c0                	xor    %eax,%eax
  attr.sched_nice = 0;
    1935:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
  attr.sched_period = 1000 * 1000 * 1000;
    193e:	48 c7 44 24 28 00 ca 9a 3b 	movq   $0x3b9aca00,0x28(%rsp)
  printf("deadline thread started [%ld]\n", gettid());
    1947:	e8 44 f8 ff ff       	call   1190 <syscall@plt>
    194c:	48 8d 35 b5 06 00 00 	lea    0x6b5(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    1953:	bf 01 00 00 00       	mov    $0x1,%edi
    1958:	48 89 c2             	mov    %rax,%rdx
    195b:	31 c0                	xor    %eax,%eax
    195d:	e8 3e f8 ff ff       	call   11a0 <__printf_chk@plt>
	return syscall(__NR_sched_setattr, pid, attr, flags);
    1962:	48 89 e2             	mov    %rsp,%rdx
    1965:	31 c9                	xor    %ecx,%ecx
    1967:	31 f6                	xor    %esi,%esi
    1969:	bf 3a 01 00 00       	mov    $0x13a,%edi
    196e:	31 c0                	xor    %eax,%eax
  attr.size = sizeof(attr);
    1970:	c7 04 24 30 00 00 00 	movl   $0x30,(%rsp)
  attr.sched_flags = 0;
    1977:	48 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%rsp)
  attr.sched_nice = 0;
    1980:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
	return syscall(__NR_sched_setattr, pid, attr, flags);
    1989:	e8 02 f8 ff ff       	call   1190 <syscall@plt>
  perror("deadline error");
    198e:	48 8d 3d db 06 00 00 	lea    0x6db(%rip),%rdi        # 2070 <_IO_stdin_used+0x70>
    1995:	e8 26 f8 ff ff       	call   11c0 <perror@plt>
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    199a:	8b 4b 20             	mov    0x20(%rbx),%ecx
    199d:	8b 13                	mov    (%rbx),%edx
    199f:	bf 01 00 00 00       	mov    $0x1,%edi
    19a4:	48 8d 35 7d 06 00 00 	lea    0x67d(%rip),%rsi        # 2028 <_IO_stdin_used+0x28>
    19ab:	31 c0                	xor    %eax,%eax
    19ad:	e8 ee f7 ff ff       	call   11a0 <__printf_chk@plt>
  if (data->mode == WRITER) {
    19b2:	8b 43 20             	mov    0x20(%rbx),%eax
    19b5:	85 c0                	test   %eax,%eax
    19b7:	0f 84 94 00 00 00    	je     1a51 <disruptor_thread+0x161>
  else if (data->mode == READER) {
    19bd:	8b 43 20             	mov    0x20(%rbx),%eax
    19c0:	83 f8 01             	cmp    $0x1,%eax
    19c3:	0f 84 cf 00 00 00    	je     1a98 <disruptor_thread+0x1a8>
    19c9:	48 8d 3d af 06 00 00 	lea    0x6af(%rip),%rdi        # 207f <_IO_stdin_used+0x7f>
    19d0:	e8 5b f7 ff ff       	call   1130 <puts@plt>
}
    19d5:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    19da:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    19e3:	0f 85 24 01 00 00    	jne    1b0d <disruptor_thread+0x21d>
    19e9:	48 83 c4 48          	add    $0x48,%rsp
    19ed:	31 c0                	xor    %eax,%eax
    19ef:	5b                   	pop    %rbx
    19f0:	5d                   	pop    %rbp
    19f1:	c3                   	ret
    19f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[data->end].start);
    19f8:	48 63 73 1c          	movslq 0x1c(%rbx),%rsi
    19fc:	bf 04 00 00 00       	mov    $0x4,%edi
    1a01:	48 c1 e6 05          	shl    $0x5,%rsi
    1a05:	48 03 73 10          	add    0x10(%rbx),%rsi
    1a09:	e8 32 f7 ff ff       	call   1140 <clock_gettime@plt>
        for (int n = 0 ; n < data->readers_count ; n++) { 
    1a0e:	8b 43 48             	mov    0x48(%rbx),%eax
    1a11:	85 c0                	test   %eax,%eax
    1a13:	7e 2b                	jle    1a40 <disruptor_thread+0x150>
          data->data[data->end].complete[n] = 0;
    1a15:	48 8b 4b 10          	mov    0x10(%rbx),%rcx
    1a19:	31 d2                	xor    %edx,%edx
    1a1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    1a20:	48 63 43 1c          	movslq 0x1c(%rbx),%rax
    1a24:	48 c1 e0 05          	shl    $0x5,%rax
    1a28:	48 8b 44 01 18       	mov    0x18(%rcx,%rax,1),%rax
    1a2d:	48 8d 04 90          	lea    (%rax,%rdx,4),%rax
        for (int n = 0 ; n < data->readers_count ; n++) { 
    1a31:	48 83 c2 01          	add    $0x1,%rdx
          data->data[data->end].complete[n] = 0;
    1a35:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
        for (int n = 0 ; n < data->readers_count ; n++) { 
    1a3b:	39 53 48             	cmp    %edx,0x48(%rbx)
    1a3e:	7f e0                	jg     1a20 <disruptor_thread+0x130>
        data->end = (data->end + 1) % data->size;
    1a40:	8b 43 1c             	mov    0x1c(%rbx),%eax
    1a43:	83 c0 01             	add    $0x1,%eax
    1a46:	48 98                	cltq
    1a48:	48 99                	cqto
    1a4a:	48 f7 7b 28          	idivq  0x28(%rbx)
    1a4e:	89 53 1c             	mov    %edx,0x1c(%rbx)
    while (data->running == 1) {
    1a51:	8b 43 30             	mov    0x30(%rbx),%eax
    1a54:	83 f8 01             	cmp    $0x1,%eax
    1a57:	0f 85 6c ff ff ff    	jne    19c9 <disruptor_thread+0xd9>
      asm volatile ("mfence" ::: "memory");
    1a5d:	0f ae f0             	mfence
      int next = (data->end + 1) % data->size;
    1a60:	8b 43 1c             	mov    0x1c(%rbx),%eax
      for (int x  = 0 ; x < data->readers_count; x++) {
    1a63:	48 63 4b 48          	movslq 0x48(%rbx),%rcx
      int next = (data->end + 1) % data->size;
    1a67:	83 c0 01             	add    $0x1,%eax
    1a6a:	48 98                	cltq
    1a6c:	48 99                	cqto
    1a6e:	48 f7 7b 28          	idivq  0x28(%rbx)
      for (int x  = 0 ; x < data->readers_count; x++) {
    1a72:	85 c9                	test   %ecx,%ecx
    1a74:	7e 82                	jle    19f8 <disruptor_thread+0x108>
    1a76:	48 8b 43 40          	mov    0x40(%rbx),%rax
    1a7a:	48 8d 34 c8          	lea    (%rax,%rcx,8),%rsi
    1a7e:	66 90                	xchg   %ax,%ax
        if (next == data->readers[x]->start) {
    1a80:	48 8b 08             	mov    (%rax),%rcx
    1a83:	8b 49 18             	mov    0x18(%rcx),%ecx
    1a86:	39 d1                	cmp    %edx,%ecx
    1a88:	74 c7                	je     1a51 <disruptor_thread+0x161>
      for (int x  = 0 ; x < data->readers_count; x++) {
    1a8a:	48 83 c0 08          	add    $0x8,%rax
    1a8e:	48 39 f0             	cmp    %rsi,%rax
    1a91:	75 ed                	jne    1a80 <disruptor_thread+0x190>
    1a93:	e9 60 ff ff ff       	jmp    19f8 <disruptor_thread+0x108>
    struct Thread *sender = data->sender;
    1a98:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    while (data->running == 1) {
    1a9c:	eb 0f                	jmp    1aad <disruptor_thread+0x1bd>
    1a9e:	66 90                	xchg   %ax,%ax
      asm volatile ("mfence" ::: "memory");
    1aa0:	0f ae f0             	mfence
      if (sender->end == data->start) {
    1aa3:	8b 55 1c             	mov    0x1c(%rbp),%edx
    1aa6:	8b 43 18             	mov    0x18(%rbx),%eax
    1aa9:	39 c2                	cmp    %eax,%edx
    1aab:	75 0d                	jne    1aba <disruptor_thread+0x1ca>
    while (data->running == 1) {
    1aad:	8b 43 30             	mov    0x30(%rbx),%eax
    1ab0:	83 f8 01             	cmp    $0x1,%eax
    1ab3:	74 eb                	je     1aa0 <disruptor_thread+0x1b0>
    1ab5:	e9 0f ff ff ff       	jmp    19c9 <disruptor_thread+0xd9>
        clock_gettime(CLOCK_MONOTONIC_RAW, &sender->data[data->start].end[data->reader_index]);
    1aba:	48 63 43 18          	movslq 0x18(%rbx),%rax
    1abe:	48 63 73 4c          	movslq 0x4c(%rbx),%rsi
    1ac2:	bf 04 00 00 00       	mov    $0x4,%edi
    1ac7:	48 c1 e0 05          	shl    $0x5,%rax
    1acb:	48 03 45 10          	add    0x10(%rbp),%rax
    1acf:	48 c1 e6 04          	shl    $0x4,%rsi
    1ad3:	48 03 70 10          	add    0x10(%rax),%rsi
    1ad7:	e8 64 f6 ff ff       	call   1140 <clock_gettime@plt>
        sender->data[data->start].complete[data->reader_index] = 1;
    1adc:	48 63 43 18          	movslq 0x18(%rbx),%rax
    1ae0:	48 63 53 4c          	movslq 0x4c(%rbx),%rdx
    1ae4:	48 c1 e0 05          	shl    $0x5,%rax
    1ae8:	48 03 45 10          	add    0x10(%rbp),%rax
    1aec:	48 8b 40 18          	mov    0x18(%rax),%rax
    1af0:	48 8d 04 90          	lea    (%rax,%rdx,4),%rax
    1af4:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
        data->start = (data->start + 1) % data->size;
    1afa:	8b 43 18             	mov    0x18(%rbx),%eax
    1afd:	83 c0 01             	add    $0x1,%eax
    1b00:	48 98                	cltq
    1b02:	48 99                	cqto
    1b04:	48 f7 7b 28          	idivq  0x28(%rbx)
    1b08:	89 53 18             	mov    %edx,0x18(%rbx)
    1b0b:	eb a0                	jmp    1aad <disruptor_thread+0x1bd>
}
    1b0d:	e8 3e f6 ff ff       	call   1150 <__stack_chk_fail@plt>
    1b12:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    1b1d:	0f 1f 00             	nopl   (%rax)

0000000000001b20 <sched_setattr>:
 {
    1b20:	f3 0f 1e fa          	endbr64
    1b24:	48 83 ec 08          	sub    $0x8,%rsp
    1b28:	89 d1                	mov    %edx,%ecx
	return syscall(__NR_sched_setattr, pid, attr, flags);
    1b2a:	31 c0                	xor    %eax,%eax
    1b2c:	48 89 f2             	mov    %rsi,%rdx
    1b2f:	89 fe                	mov    %edi,%esi
    1b31:	bf 3a 01 00 00       	mov    $0x13a,%edi
    1b36:	e8 55 f6 ff ff       	call   1190 <syscall@plt>
 }
    1b3b:	48 83 c4 08          	add    $0x8,%rsp
    1b3f:	c3                   	ret

0000000000001b40 <sched_getattr>:
 {
    1b40:	f3 0f 1e fa          	endbr64
    1b44:	48 83 ec 08          	sub    $0x8,%rsp
    1b48:	41 89 c8             	mov    %ecx,%r8d
	return syscall(__NR_sched_getattr, pid, attr, size, flags);
    1b4b:	31 c0                	xor    %eax,%eax
    1b4d:	89 d1                	mov    %edx,%ecx
    1b4f:	48 89 f2             	mov    %rsi,%rdx
    1b52:	89 fe                	mov    %edi,%esi
    1b54:	bf 3b 01 00 00       	mov    $0x13b,%edi
    1b59:	e8 32 f6 ff ff       	call   1190 <syscall@plt>
 }
    1b5e:	48 83 c4 08          	add    $0x8,%rsp
    1b62:	c3                   	ret

Disassembly of section .fini:

0000000000001b64 <_fini>:
    1b64:	f3 0f 1e fa          	endbr64
    1b68:	48 83 ec 08          	sub    $0x8,%rsp
    1b6c:	48 83 c4 08          	add    $0x8,%rsp
    1b70:	c3                   	ret
