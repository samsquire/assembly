
disruptor-multi:     file format elf64-x86-64


Disassembly of section .init:

0000000000001000 <_init>:
    1000:	f3 0f 1e fa          	endbr64
    1004:	48 83 ec 08          	sub    $0x8,%rsp
    1008:	48 8d 05 71 06 00 00 	lea    0x671(%rip),%rax        # 1680 <__gmon_start__>
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
  printf("Finished\n");
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
    1211:	48 83 ec 58          	sub    $0x58,%rsp
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
    124a:	48 8d 35 3f 0e 00 00 	lea    0xe3f(%rip),%rsi        # 2090 <_IO_stdin_used+0x90>
    1251:	31 c0                	xor    %eax,%eax
    1253:	bf 01 00 00 00       	mov    $0x1,%edi
    1258:	e8 43 ff ff ff       	call   11a0 <__printf_chk@plt>
    125d:	ba 01 00 00 00       	mov    $0x1,%edx
    1262:	48 8d 35 37 0e 00 00 	lea    0xe37(%rip),%rsi        # 20a0 <_IO_stdin_used+0xa0>
    1269:	31 c0                	xor    %eax,%eax
    126b:	bf 01 00 00 00       	mov    $0x1,%edi
    1270:	e8 2b ff ff ff       	call   11a0 <__printf_chk@plt>
    1275:	ba 02 00 00 00       	mov    $0x2,%edx
    127a:	48 8d 35 31 0e 00 00 	lea    0xe31(%rip),%rsi        # 20b2 <_IO_stdin_used+0xb2>
    1281:	31 c0                	xor    %eax,%eax
    1283:	bf 01 00 00 00       	mov    $0x1,%edi
    1288:	e8 13 ff ff ff       	call   11a0 <__printf_chk@plt>
  int readers_count = 1;
  int group_size = writers_count + readers_count;
  printf("Readers count %d\n", readers_count);
  int thread_count = groups * (readers_count + writers_count);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    128d:	be 00 02 00 00       	mov    $0x200,%esi
    1292:	bf 02 00 00 00       	mov    $0x2,%edi
    1297:	e8 e4 fe ff ff       	call   1180 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    129c:	be 38 00 00 00       	mov    $0x38,%esi
    12a1:	bf 02 00 00 00       	mov    $0x2,%edi
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    12a6:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12a9:	e8 d2 fe ff ff       	call   1180 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12ae:	be 08 00 00 00       	mov    $0x8,%esi
    12b3:	bf 02 00 00 00       	mov    $0x2,%edi
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
    12cb:	49 89 c5             	mov    %rax,%r13
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12ce:	e8 ad fe ff ff       	call   1180 <calloc@plt>
    CPU_ZERO(sendercpu);
    for (int j = 0 ; j < cores ; j++) {
      // printf("assigning sender %d to core %d\n", sender, j);
      CPU_SET(j, sendercpu);
    }
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12d3:	be 80 00 00 00       	mov    $0x80,%esi
    12d8:	bf 01 00 00 00       	mov    $0x1,%edi
      CPU_SET(j, sendercpu);
    12dd:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12e4:	49 89 c4             	mov    %rax,%r12
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12e7:	e8 94 fe ff ff       	call   1180 <calloc@plt>
    for (int j = 0; j < cores ; j++) {
      // printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    }
     
    thread_data[sender].thread_index = sender;
    12ec:	c7 03 00 00 00 00    	movl   $0x0,(%rbx)
    thread_data[sender].cpu_set = sendercpu;
    thread_data[sender].mode = WRITER;
    thread_data[sender].running = 1;
    thread_data[sender].size = buffer_size;
    thread_data[sender].end = 0;
    thread_data[sender].readers = calloc(readers_count, sizeof(struct Thread*));
    12f2:	be 08 00 00 00       	mov    $0x8,%esi
    12f7:	bf 01 00 00 00       	mov    $0x1,%edi
      CPU_SET(j, receivercpu);
    12fc:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1303:	49 89 c7             	mov    %rax,%r15
    thread_data[sender].mode = WRITER;
    1306:	c7 83 04 01 00 00 00 00 00 00 	movl   $0x0,0x104(%rbx)
    thread_data[sender].cpu_set = sendercpu;
    1310:	4c 89 a3 18 01 00 00 	mov    %r12,0x118(%rbx)
    thread_data[sender].running = 1;
    1317:	c7 83 10 01 00 00 01 00 00 00 	movl   $0x1,0x110(%rbx)
    thread_data[sender].size = buffer_size;
    1321:	48 c7 83 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%rbx)
    thread_data[sender].end = 0;
    132c:	c7 83 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbx)
    thread_data[sender].readers = calloc(readers_count, sizeof(struct Thread*));
    1336:	e8 45 fe ff ff       	call   1180 <calloc@plt>
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    133b:	be 80 01 00 00       	mov    $0x180,%esi
    1340:	bf 00 00 10 00       	mov    $0x100000,%edi
    thread_data[sender].readers = calloc(readers_count, sizeof(struct Thread*));
    1345:	48 89 83 80 01 00 00 	mov    %rax,0x180(%rbx)
    134c:	48 89 45 80          	mov    %rax,-0x80(%rbp)
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    1350:	e8 2b fe ff ff       	call   1180 <calloc@plt>
    1355:	48 89 43 10          	mov    %rax,0x10(%rbx)
    1359:	49 89 c4             	mov    %rax,%r12
    for (int n = 0 ; n < buffer_size ; n++) {
    135c:	4c 8d b0 80 00 00 00 	lea    0x80(%rax),%r14
    1363:	49 81 c4 80 00 00 18 	add    $0x18000080,%r12
    136a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      thread_data[sender].data[n].end = calloc(readers_count, sizeof(struct timespec));
    1370:	be 10 00 00 00       	mov    $0x10,%esi
    1375:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < buffer_size ; n++) {
    137a:	49 81 c6 80 01 00 00 	add    $0x180,%r14
      thread_data[sender].data[n].end = calloc(readers_count, sizeof(struct timespec));
    1381:	e8 fa fd ff ff       	call   1180 <calloc@plt>
      thread_data[sender].data[n].complete = calloc(readers_count, sizeof(int));
    1386:	be 04 00 00 00       	mov    $0x4,%esi
    138b:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[sender].data[n].end = calloc(readers_count, sizeof(struct timespec));
    1390:	49 89 86 80 fe ff ff 	mov    %rax,-0x180(%r14)
      thread_data[sender].data[n].complete = calloc(readers_count, sizeof(int));
    1397:	e8 e4 fd ff ff       	call   1180 <calloc@plt>
    139c:	49 89 86 00 ff ff ff 	mov    %rax,-0x100(%r14)
    for (int n = 0 ; n < buffer_size ; n++) {
    13a3:	4d 39 f4             	cmp    %r14,%r12
    13a6:	75 c8                	jne    1370 <main+0x170>
      thread_data[j].running = 1;
      thread_data[j].mode = READER;
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
      thread_data[j].start = 0;
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    13a8:	48 8b 45 80          	mov    -0x80(%rbp),%rax
      thread_data[j].thread_index = j;
    13ac:	4c 8d a3 00 02 00 00 	lea    0x200(%rbx),%r12
    13b3:	45 31 c0             	xor    %r8d,%r8d
    13b6:	31 c9                	xor    %ecx,%ecx
      thread_data[j].running = 1;
    13b8:	c7 83 10 03 00 00 01 00 00 00 	movl   $0x1,0x310(%rbx)
    13c2:	ba 01 00 00 00       	mov    $0x1,%edx
    13c7:	48 8d 35 8a 0c 00 00 	lea    0xc8a(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
    13ce:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].mode = READER;
    13d3:	c7 83 04 03 00 00 01 00 00 00 	movl   $0x1,0x304(%rbx)
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    13dd:	4c 89 20             	mov    %r12,(%rax)
    13e0:	31 c0                	xor    %eax,%eax
    thread_data[sender].readers_count = readers_count;
    13e2:	c7 83 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rbx)
      thread_data[j].thread_index = j;
    13ec:	c7 83 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rbx)
      thread_data[j].reader_index = receiver_index;
    13f6:	c7 83 8c 03 00 00 00 00 00 00 	movl   $0x0,0x38c(%rbx)
      thread_data[j].cpu_set = receivercpu;
    1400:	4c 89 bb 18 03 00 00 	mov    %r15,0x318(%rbx)
      thread_data[j].size = buffer_size;
    1407:	48 c7 83 08 03 00 00 00 00 10 00 	movq   $0x100000,0x308(%rbx)
      thread_data[j].sender = &thread_data[sender];
    1412:	48 89 9b 08 02 00 00 	mov    %rbx,0x208(%rbx)
      thread_data[j].start = 0;
    1419:	c7 83 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rbx)
    1423:	e8 78 fd ff ff       	call   11a0 <__printf_chk@plt>
    1428:	31 d2                	xor    %edx,%edx
    142a:	48 8d 35 98 0c 00 00 	lea    0xc98(%rip),%rsi        # 20c9 <_IO_stdin_used+0xc9>
    1431:	31 c0                	xor    %eax,%eax
    1433:	bf 01 00 00 00       	mov    $0x1,%edi
    1438:	e8 63 fd ff ff       	call   11a0 <__printf_chk@plt>
      printf("Setting up receiver thread %d %d to sender %d\n", j, receiver_index, sender);
    }
    printf("Creating sender thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    143d:	0f ae f0             	mfence
    1440:	48 8d 35 9d 0c 00 00 	lea    0xc9d(%rip),%rsi        # 20e4 <_IO_stdin_used+0xe4>
    1447:	bf 01 00 00 00       	mov    $0x1,%edi
    144c:	31 c0                	xor    %eax,%eax
    144e:	ba 01 00 00 00       	mov    $0x1,%edx
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    1453:	c7 45 9c 00 00 00 00 	movl   $0x0,-0x64(%rbp)
    145a:	e8 41 fd ff ff       	call   11a0 <__printf_chk@plt>
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    145f:	48 8b 45 88          	mov    -0x78(%rbp),%rax
    1463:	31 f6                	xor    %esi,%esi
    1465:	4c 8d 78 38          	lea    0x38(%rax),%r15
    1469:	4c 89 ff             	mov    %r15,%rdi
    146c:	e8 ff fc ff ff       	call   1170 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    1471:	85 c0                	test   %eax,%eax
    1473:	0f 85 9a 01 00 00    	jne    1613 <main+0x413>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    1479:	48 8d 75 9c          	lea    -0x64(%rbp),%rsi
    147d:	4c 89 ff             	mov    %r15,%rdi
    1480:	e8 3b fd ff ff       	call   11c0 <pthread_attr_setschedparam@plt>
      if (ret) {
    1485:	85 c0                	test   %eax,%eax
    1487:	0f 85 a1 01 00 00    	jne    162e <main+0x42e>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    148d:	4c 89 e1             	mov    %r12,%rcx
    1490:	4c 8d 25 09 03 00 00 	lea    0x309(%rip),%r12        # 17a0 <disruptor_thread>
    1497:	49 8d 7d 08          	lea    0x8(%r13),%rdi
    149b:	4c 89 fe             	mov    %r15,%rsi
    149e:	4c 89 e2             	mov    %r12,%rdx
    14a1:	e8 0a fd ff ff       	call   11b0 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    14a6:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    14aa:	be 08 00 00 00       	mov    $0x8,%esi
    14af:	48 8b 93 18 03 00 00 	mov    0x318(%rbx),%rdx
    14b6:	e8 65 fc ff ff       	call   1120 <pthread_setaffinity_np@plt>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    14bb:	4c 8b 7d 88          	mov    -0x78(%rbp),%r15
    14bf:	31 f6                	xor    %esi,%esi
    14c1:	4c 89 ff             	mov    %r15,%rdi
    14c4:	e8 a7 fc ff ff       	call   1170 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    14c9:	85 c0                	test   %eax,%eax
    14cb:	0f 85 42 01 00 00    	jne    1613 <main+0x413>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    14d1:	48 8d 75 98          	lea    -0x68(%rbp),%rsi
    14d5:	4c 89 ff             	mov    %r15,%rdi
      param2.sched_priority = 0;
    14d8:	c7 45 98 00 00 00 00 	movl   $0x0,-0x68(%rbp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    14df:	e8 dc fc ff ff       	call   11c0 <pthread_attr_setschedparam@plt>
      if (ret) {
    14e4:	85 c0                	test   %eax,%eax
    14e6:	0f 85 42 01 00 00    	jne    162e <main+0x42e>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    14ec:	48 89 d9             	mov    %rbx,%rcx
    14ef:	4c 89 e2             	mov    %r12,%rdx
    14f2:	4c 89 ef             	mov    %r13,%rdi
    14f5:	4c 89 fe             	mov    %r15,%rsi
    14f8:	e8 b3 fc ff ff       	call   11b0 <pthread_create@plt>
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    14fd:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    1501:	be 08 00 00 00       	mov    $0x8,%esi
    1506:	45 31 e4             	xor    %r12d,%r12d
    1509:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
    1510:	e8 0b fc ff ff       	call   1120 <pthread_setaffinity_np@plt>
    // printf("Waiting before starting next disruptor %ld ns\n", TICK);
    // nanosleep(&preempt , &rem2);
    }
  int seconds = 10;
  struct timespec rem2;
  struct timespec preempt = {
    1515:	66 0f 6f 05 83 0c 00 00 	movdqa 0xc83(%rip),%xmm0        # 21a0 <_IO_stdin_used+0x1a0>
    151d:	ba 0a 00 00 00       	mov    $0xa,%edx
    1522:	31 c0                	xor    %eax,%eax
    1524:	48 8d 35 11 0c 00 00 	lea    0xc11(%rip),%rsi        # 213c <_IO_stdin_used+0x13c>
    152b:	bf 01 00 00 00       	mov    $0x1,%edi
    1530:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
    1534:	e8 67 fc ff ff       	call   11a0 <__printf_chk@plt>
    seconds,
    0 };
  printf("Sleeping for %d seconds\n", seconds);
  nanosleep(&preempt , &rem2);
    1539:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    153d:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
    1541:	e8 1a fc ff ff       	call   1160 <nanosleep@plt>
  for (int x = 0 ; x < groups ; x++) {
    void * res1;
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + 1; 
    pthread_join(thread[sender], res1);
    1546:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    154a:	31 f6                	xor    %esi,%esi
    thread_data[sender].running = 0;
    154c:	c7 83 10 01 00 00 00 00 00 00 	movl   $0x0,0x110(%rbx)
      thread_data[j].running = 0;
    1556:	c7 83 10 03 00 00 00 00 00 00 	movl   $0x0,0x310(%rbx)
    pthread_join(thread[sender], res1);
    1560:	e8 8b fc ff ff       	call   11f0 <pthread_join@plt>
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    1565:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    1569:	31 f6                	xor    %esi,%esi
    156b:	4c 8d 2d f9 0b 00 00 	lea    0xbf9(%rip),%r13        # 216b <_IO_stdin_used+0x16b>
    1572:	e8 79 fc ff ff       	call   11f0 <pthread_join@plt>
    1577:	31 d2                	xor    %edx,%edx
    1579:	48 8d 35 d5 0b 00 00 	lea    0xbd5(%rip),%rsi        # 2155 <_IO_stdin_used+0x155>
    1580:	31 c0                	xor    %eax,%eax
    1582:	bf 01 00 00 00       	mov    $0x1,%edi
    1587:	e8 14 fc ff ff       	call   11a0 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1;
    int incompletes = 0;
    printf("Inspecting sender %d\n", sender);
    for (int y = 0 ; y < buffer_size; y++) {
    158c:	0f 1f 40 00          	nopl   0x0(%rax)
      int compcount = 0;
      for (int n = 0 ; n < readers_count ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    1590:	48 8b 43 10          	mov    0x10(%rbx),%rax
    1594:	4a 8b 94 20 00 01 00 00 	mov    0x100(%rax,%r12,1),%rdx
    159c:	8b 12                	mov    (%rdx),%edx
    159e:	83 fa 01             	cmp    $0x1,%edx
    15a1:	75 2b                	jne    15ce <main+0x3ce>
        }
      }
      if (compcount == readers_count) {
        for (int n = 0 ; n < readers_count ; n++) {
            // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
            struct timespec start = thread_data[sender].data[y].start;
    15a3:	4c 01 e0             	add    %r12,%rax
    15a6:	31 c9                	xor    %ecx,%ecx
    15a8:	4c 89 ee             	mov    %r13,%rsi
    15ab:	bf 01 00 00 00       	mov    $0x1,%edi
            struct timespec end = thread_data[sender].data[y].end[n];
    15b0:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
            const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
            const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    15b7:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
            const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    15bb:	4c 8b 02             	mov    (%rdx),%r8
    15be:	31 d2                	xor    %edx,%edx
    15c0:	4c 2b 48 08          	sub    0x8(%rax),%r9
    15c4:	4c 2b 00             	sub    (%rax),%r8
    15c7:	31 c0                	xor    %eax,%eax
    15c9:	e8 d2 fb ff ff       	call   11a0 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    15ce:	49 81 c4 80 01 00 00 	add    $0x180,%r12
    15d5:	49 81 fc 00 00 00 18 	cmp    $0x18000000,%r12
    15dc:	75 b2                	jne    1590 <main+0x390>
    15de:	31 d2                	xor    %edx,%edx
    15e0:	31 c0                	xor    %eax,%eax
    15e2:	48 8d 35 99 0b 00 00 	lea    0xb99(%rip),%rsi        # 2182 <_IO_stdin_used+0x182>
    15e9:	bf 01 00 00 00       	mov    $0x1,%edi
    15ee:	e8 ad fb ff ff       	call   11a0 <__printf_chk@plt>
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    15f3:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    15f7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1600:	75 27                	jne    1629 <main+0x429>
    1602:	48 83 c4 58          	add    $0x58,%rsp
    1606:	31 c0                	xor    %eax,%eax
    1608:	5b                   	pop    %rbx
    1609:	41 5c                	pop    %r12
    160b:	41 5d                	pop    %r13
    160d:	41 5e                	pop    %r14
    160f:	41 5f                	pop    %r15
    1611:	5d                   	pop    %rbp
    1612:	c3                   	ret
    1613:	48 8d 3d e7 0a 00 00 	lea    0xae7(%rip),%rdi        # 2101 <_IO_stdin_used+0x101>
    161a:	e8 11 fb ff ff       	call   1130 <puts@plt>
               exit(1);
    161f:	bf 01 00 00 00       	mov    $0x1,%edi
    1624:	e8 b7 fb ff ff       	call   11e0 <exit@plt>
}
    1629:	e8 22 fb ff ff       	call   1150 <__stack_chk_fail@plt>
    162e:	48 8d 3d ea 0a 00 00 	lea    0xaea(%rip),%rdi        # 211f <_IO_stdin_used+0x11f>
    1635:	e8 f6 fa ff ff       	call   1130 <puts@plt>
              exit(1);
    163a:	bf 01 00 00 00       	mov    $0x1,%edi
    163f:	e8 9c fb ff ff       	call   11e0 <exit@plt>
    1644:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    164e:	66 90                	xchg   %ax,%ax

0000000000001650 <_start>:
    1650:	f3 0f 1e fa          	endbr64
    1654:	31 ed                	xor    %ebp,%ebp
    1656:	49 89 d1             	mov    %rdx,%r9
    1659:	5e                   	pop    %rsi
    165a:	48 89 e2             	mov    %rsp,%rdx
    165d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1661:	50                   	push   %rax
    1662:	54                   	push   %rsp
    1663:	45 31 c0             	xor    %r8d,%r8d
    1666:	31 c9                	xor    %ecx,%ecx
    1668:	48 8d 3d 91 fb ff ff 	lea    -0x46f(%rip),%rdi        # 1200 <main>
    166f:	ff 15 5b 29 00 00    	call   *0x295b(%rip)        # 3fd0 <__libc_start_main@GLIBC_2.34>
    1675:	f4                   	hlt
    1676:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001680 <__gmon_start__>:
    1680:	f3 0f 1e fa          	endbr64
    1684:	8b 05 86 29 00 00    	mov    0x2986(%rip),%eax        # 4010 <__TMC_END__>
    168a:	85 c0                	test   %eax,%eax
    168c:	74 02                	je     1690 <__gmon_start__+0x10>
    168e:	c3                   	ret
    168f:	90                   	nop
    1690:	48 83 ec 08          	sub    $0x8,%rsp
    1694:	48 8d 35 b2 03 00 00 	lea    0x3b2(%rip),%rsi        # 1a4d <etext>
    169b:	48 8d 3d 5e e9 ff ff 	lea    -0x16a2(%rip),%rdi        # 0 <__executable_start>
    16a2:	c7 05 64 29 00 00 01 00 00 00 	movl   $0x1,0x2964(%rip)        # 4010 <__TMC_END__>
    16ac:	e8 df fa ff ff       	call   1190 <__monstartup@plt>
    16b1:	48 8b 3d 28 29 00 00 	mov    0x2928(%rip),%rdi        # 3fe0 <_mcleanup@GLIBC_2.2.5>
    16b8:	48 83 c4 08          	add    $0x8,%rsp
    16bc:	e9 4f 03 00 00       	jmp    1a10 <atexit>
    16c1:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    16cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000016d0 <_dl_relocate_static_pie>:
    16d0:	f3 0f 1e fa          	endbr64
    16d4:	c3                   	ret
    16d5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    16df:	90                   	nop

00000000000016e0 <deregister_tm_clones>:
    16e0:	48 8d 3d 29 29 00 00 	lea    0x2929(%rip),%rdi        # 4010 <__TMC_END__>
    16e7:	48 8d 05 22 29 00 00 	lea    0x2922(%rip),%rax        # 4010 <__TMC_END__>
    16ee:	48 39 f8             	cmp    %rdi,%rax
    16f1:	74 15                	je     1708 <deregister_tm_clones+0x28>
    16f3:	48 8b 05 de 28 00 00 	mov    0x28de(%rip),%rax        # 3fd8 <_ITM_deregisterTMCloneTable@Base>
    16fa:	48 85 c0             	test   %rax,%rax
    16fd:	74 09                	je     1708 <deregister_tm_clones+0x28>
    16ff:	ff e0                	jmp    *%rax
    1701:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1708:	c3                   	ret
    1709:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001710 <register_tm_clones>:
    1710:	48 8d 3d f9 28 00 00 	lea    0x28f9(%rip),%rdi        # 4010 <__TMC_END__>
    1717:	48 8d 35 f2 28 00 00 	lea    0x28f2(%rip),%rsi        # 4010 <__TMC_END__>
    171e:	48 29 fe             	sub    %rdi,%rsi
    1721:	48 89 f0             	mov    %rsi,%rax
    1724:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1728:	48 c1 f8 03          	sar    $0x3,%rax
    172c:	48 01 c6             	add    %rax,%rsi
    172f:	48 d1 fe             	sar    %rsi
    1732:	74 14                	je     1748 <register_tm_clones+0x38>
    1734:	48 8b 05 b5 28 00 00 	mov    0x28b5(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    173b:	48 85 c0             	test   %rax,%rax
    173e:	74 08                	je     1748 <register_tm_clones+0x38>
    1740:	ff e0                	jmp    *%rax
    1742:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1748:	c3                   	ret
    1749:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001750 <__do_global_dtors_aux>:
    1750:	f3 0f 1e fa          	endbr64
    1754:	80 3d b9 28 00 00 00 	cmpb   $0x0,0x28b9(%rip)        # 4014 <completed.0>
    175b:	75 2b                	jne    1788 <__do_global_dtors_aux+0x38>
    175d:	55                   	push   %rbp
    175e:	48 83 3d 92 28 00 00 00 	cmpq   $0x0,0x2892(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1766:	48 89 e5             	mov    %rsp,%rbp
    1769:	74 0c                	je     1777 <__do_global_dtors_aux+0x27>
    176b:	48 8b 3d 96 28 00 00 	mov    0x2896(%rip),%rdi        # 4008 <__dso_handle>
    1772:	e8 99 f9 ff ff       	call   1110 <__cxa_finalize@plt>
    1777:	e8 64 ff ff ff       	call   16e0 <deregister_tm_clones>
    177c:	c6 05 91 28 00 00 01 	movb   $0x1,0x2891(%rip)        # 4014 <completed.0>
    1783:	5d                   	pop    %rbp
    1784:	c3                   	ret
    1785:	0f 1f 00             	nopl   (%rax)
    1788:	c3                   	ret
    1789:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001790 <frame_dummy>:
    1790:	f3 0f 1e fa          	endbr64
    1794:	e9 77 ff ff ff       	jmp    1710 <register_tm_clones>
    1799:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017a0 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    17a0:	f3 0f 1e fa          	endbr64
    17a4:	55                   	push   %rbp
    17a5:	48 89 e5             	mov    %rsp,%rbp
    17a8:	41 57                	push   %r15
    17aa:	41 56                	push   %r14
    17ac:	41 55                	push   %r13
    17ae:	41 54                	push   %r12
    17b0:	53                   	push   %rbx
    17b1:	48 83 ec 28          	sub    $0x28,%rsp
    17b5:	ff 15 2d 28 00 00    	call   *0x282d(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
    17bb:	48 8d 35 46 08 00 00 	lea    0x846(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    17c2:	31 c0                	xor    %eax,%eax
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    17c4:	8b 8f 04 01 00 00    	mov    0x104(%rdi),%ecx
    17ca:	8b 17                	mov    (%rdi),%edx
void * disruptor_thread(void * arg) {
    17cc:	49 89 fc             	mov    %rdi,%r12
    17cf:	bf 01 00 00 00       	mov    $0x1,%edi
    17d4:	e8 c7 f9 ff ff       	call   11a0 <__printf_chk@plt>
  int next = (data->end + 1) % data->size;
    17d9:	41 8b 84 24 00 01 00 00 	mov    0x100(%r12),%eax
  if (data->mode == WRITER) {
    17e1:	41 8b 94 24 04 01 00 00 	mov    0x104(%r12),%edx
  int mina = data->size;
    17e9:	49 8b 8c 24 08 01 00 00 	mov    0x108(%r12),%rcx
  if (data->mode == WRITER) {
    17f1:	85 d2                	test   %edx,%edx
    17f3:	0f 85 1c 01 00 00    	jne    1915 <disruptor_thread+0x175>
  int next = (data->end + 1) % data->size;
    17f9:	83 c0 01             	add    $0x1,%eax
    17fc:	48 98                	cltq
    17fe:	48 99                	cqto
    1800:	48 f7 f9             	idiv   %rcx
    1803:	89 d3                	mov    %edx,%ebx
    1805:	0f 1f 00             	nopl   (%rax)
    while (data->running == 1) {
    1808:	41 8b 84 24 10 01 00 00 	mov    0x110(%r12),%eax
    1810:	83 f8 01             	cmp    $0x1,%eax
    1813:	0f 85 df 00 00 00    	jne    18f8 <disruptor_thread+0x158>
      asm volatile ("sfence" ::: "memory");
    1819:	0f ae f8             	sfence
      for (int x  = 0 ; x < data->readers_count; x++) {
    181c:	49 63 94 24 88 01 00 00 	movslq 0x188(%r12),%rdx
    1824:	85 d2                	test   %edx,%edx
    1826:	0f 8e a9 01 00 00    	jle    19d5 <disruptor_thread+0x235>
    182c:	49 8b 84 24 80 01 00 00 	mov    0x180(%r12),%rax
    1834:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    1838:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        if (next == data->readers[x]->start) {
    1840:	48 8b 08             	mov    (%rax),%rcx
    1843:	8b 89 80 00 00 00    	mov    0x80(%rcx),%ecx
    1849:	39 cb                	cmp    %ecx,%ebx
    184b:	74 bb                	je     1808 <disruptor_thread+0x68>
      for (int x  = 0 ; x < data->readers_count; x++) {
    184d:	48 83 c0 08          	add    $0x8,%rax
    1851:	48 39 c6             	cmp    %rax,%rsi
    1854:	75 ea                	jne    1840 <disruptor_thread+0xa0>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[changed].start);
    1856:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
    185b:	31 d2                	xor    %edx,%edx
    185d:	0f 1f 00             	nopl   (%rax)
              data->data[data->end].complete[n] = 0;
    1860:	49 63 84 24 00 01 00 00 	movslq 0x100(%r12),%rax
    1868:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    186c:	48 c1 e0 07          	shl    $0x7,%rax
    1870:	48 8b 84 01 00 01 00 00 	mov    0x100(%rcx,%rax,1),%rax
    1878:	48 8d 04 90          	lea    (%rax,%rdx,4),%rax
            for (int n = 0 ; n < data->readers_count ; n++) { 
    187c:	48 83 c2 01          	add    $0x1,%rdx
              data->data[data->end].complete[n] = 0;
    1880:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
            for (int n = 0 ; n < data->readers_count ; n++) { 
    1886:	41 39 94 24 88 01 00 00 	cmp    %edx,0x188(%r12)
    188e:	7f d0                	jg     1860 <disruptor_thread+0xc0>
            int changed = data->end;
    1890:	41 8b b4 24 00 01 00 00 	mov    0x100(%r12),%esi
            data->end = (data->end + 1) % data->size;
    1898:	41 8b 84 24 00 01 00 00 	mov    0x100(%r12),%eax
    18a0:	49 8b bc 24 08 01 00 00 	mov    0x108(%r12),%rdi
    18a8:	83 c0 01             	add    $0x1,%eax
    18ab:	48 98                	cltq
    18ad:	48 99                	cqto
    18af:	48 f7 ff             	idiv   %rdi
    18b2:	41 89 94 24 00 01 00 00 	mov    %edx,0x100(%r12)
            next = (data->end + 1) % data->size;
    18ba:	41 8b 84 24 00 01 00 00 	mov    0x100(%r12),%eax
    18c2:	83 c0 01             	add    $0x1,%eax
    18c5:	48 98                	cltq
    18c7:	48 99                	cqto
    18c9:	48 f7 ff             	idiv   %rdi
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[changed].start);
    18cc:	48 63 c6             	movslq %esi,%rax
    18cf:	bf 04 00 00 00       	mov    $0x4,%edi
    18d4:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    18d8:	48 c1 e0 07          	shl    $0x7,%rax
    18dc:	48 8d 34 01          	lea    (%rcx,%rax,1),%rsi
            next = (data->end + 1) % data->size;
    18e0:	89 d3                	mov    %edx,%ebx
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[changed].start);
    18e2:	e8 59 f8 ff ff       	call   1140 <clock_gettime@plt>
    while (data->running == 1) {
    18e7:	41 8b 84 24 10 01 00 00 	mov    0x110(%r12),%eax
    18ef:	83 f8 01             	cmp    $0x1,%eax
    18f2:	0f 84 21 ff ff ff    	je     1819 <disruptor_thread+0x79>
    18f8:	48 8d 3d 88 07 00 00 	lea    0x788(%rip),%rdi        # 2087 <_IO_stdin_used+0x87>
    18ff:	e8 2c f8 ff ff       	call   1130 <puts@plt>
}
    1904:	48 83 c4 28          	add    $0x28,%rsp
    1908:	31 c0                	xor    %eax,%eax
    190a:	5b                   	pop    %rbx
    190b:	41 5c                	pop    %r12
    190d:	41 5d                	pop    %r13
    190f:	41 5e                	pop    %r14
    1911:	41 5f                	pop    %r15
    1913:	5d                   	pop    %rbp
    1914:	c3                   	ret
  else if (data->mode == READER) {
    1915:	41 8b 84 24 04 01 00 00 	mov    0x104(%r12),%eax
    191d:	83 f8 01             	cmp    $0x1,%eax
    1920:	75 d6                	jne    18f8 <disruptor_thread+0x158>
    struct Thread *sender = data->sender;
    1922:	49 8b 5c 24 08       	mov    0x8(%r12),%rbx
    int index = data->reader_index;
    1927:	4d 63 ac 24 8c 01 00 00 	movslq 0x18c(%r12),%r13
    int size = data->size;
    192f:	89 4d cc             	mov    %ecx,-0x34(%rbp)
    int cachedEnd = sender->end;
    1932:	8b 83 00 01 00 00    	mov    0x100(%rbx),%eax
    int cachedStart = data->start;
    1938:	45 8b bc 24 80 00 00 00 	mov    0x80(%r12),%r15d
    while (data->running == 1) {
    1940:	41 8b 8c 24 10 01 00 00 	mov    0x110(%r12),%ecx
    struct Snapshot * rdata = sender->data;
    1948:	4c 8b 73 10          	mov    0x10(%rbx),%r14
    while (data->running == 1) {
    194c:	83 f9 01             	cmp    $0x1,%ecx
    194f:	75 a7                	jne    18f8 <disruptor_thread+0x158>
          clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[cachedStart].end[index]);
    1951:	4c 89 ef             	mov    %r13,%rdi
    1954:	48 c1 e7 04          	shl    $0x4,%rdi
    1958:	48 89 7d c0          	mov    %rdi,-0x40(%rbp)
          rdata[cachedStart].complete[index] = 1;
    195c:	4a 8d 3c ad 00 00 00 00 	lea    0x0(,%r13,4),%rdi
    1964:	48 89 7d b8          	mov    %rdi,-0x48(%rbp)
    1968:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      if (cachedEnd == cachedStart) {
    1970:	44 39 f8             	cmp    %r15d,%eax
    1973:	74 48                	je     19bd <disruptor_thread+0x21d>
          clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[cachedStart].end[index]);
    1975:	49 63 c7             	movslq %r15d,%rax
    1978:	48 8b 75 c0          	mov    -0x40(%rbp),%rsi
    197c:	bf 04 00 00 00       	mov    $0x4,%edi
    1981:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
    1985:	48 c1 e1 07          	shl    $0x7,%rcx
    1989:	4d 8d 2c 0e          	lea    (%r14,%rcx,1),%r13
    198d:	49 03 b5 80 00 00 00 	add    0x80(%r13),%rsi
    1994:	e8 a7 f7 ff ff       	call   1140 <clock_gettime@plt>
          rdata[cachedStart].complete[index] = 1;
    1999:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    199d:	49 03 85 00 01 00 00 	add    0x100(%r13),%rax
    19a4:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
          cachedStart = (cachedStart + 1) % size;
    19aa:	41 8d 47 01          	lea    0x1(%r15),%eax
    19ae:	99                   	cltd
    19af:	f7 7d cc             	idivl  -0x34(%rbp)
          data->start = cachedStart;
    19b2:	41 89 94 24 80 00 00 00 	mov    %edx,0x80(%r12)
          cachedStart = (cachedStart + 1) % size;
    19ba:	41 89 d7             	mov    %edx,%r15d
          cachedEnd = sender->end;
    19bd:	8b 83 00 01 00 00    	mov    0x100(%rbx),%eax
    while (data->running == 1) {
    19c3:	41 8b 8c 24 10 01 00 00 	mov    0x110(%r12),%ecx
    19cb:	83 f9 01             	cmp    $0x1,%ecx
    19ce:	74 a0                	je     1970 <disruptor_thread+0x1d0>
    19d0:	e9 23 ff ff ff       	jmp    18f8 <disruptor_thread+0x158>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[changed].start);
    19d5:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
    19da:	e9 b1 fe ff ff       	jmp    1890 <disruptor_thread+0xf0>
    19df:	90                   	nop

00000000000019e0 <min>:
int min(long a, long b) {
    19e0:	f3 0f 1e fa          	endbr64
    19e4:	55                   	push   %rbp
    19e5:	48 89 e5             	mov    %rsp,%rbp
    19e8:	ff 15 fa 25 00 00    	call   *0x25fa(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
  if (a < b) return a;
    19ee:	48 39 f7             	cmp    %rsi,%rdi
    19f1:	7c 02                	jl     19f5 <min+0x15>
  if (b < a) return b;
    19f3:	7f 0b                	jg     1a00 <min+0x20>
  if (a < b) return a;
    19f5:	89 f8                	mov    %edi,%eax
}
    19f7:	5d                   	pop    %rbp
    19f8:	c3                   	ret
    19f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (b < a) return b;
    1a00:	89 f0                	mov    %esi,%eax
}
    1a02:	5d                   	pop    %rbp
    1a03:	c3                   	ret
    1a04:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    1a0e:	66 90                	xchg   %ax,%ax

0000000000001a10 <atexit>:
    1a10:	f3 0f 1e fa          	endbr64
    1a14:	48 8b 15 ed 25 00 00 	mov    0x25ed(%rip),%rdx        # 4008 <__dso_handle>
    1a1b:	31 f6                	xor    %esi,%esi
    1a1d:	e9 ae f7 ff ff       	jmp    11d0 <__cxa_atexit@plt>
    1a22:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    1a2c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000001a30 <__stack_chk_fail_local>:
    1a30:	f3 0f 1e fa          	endbr64
    1a34:	50                   	push   %rax
    1a35:	58                   	pop    %rax
    1a36:	48 83 ec 08          	sub    $0x8,%rsp
    1a3a:	e8 11 f7 ff ff       	call   1150 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000001a40 <_fini>:
    1a40:	f3 0f 1e fa          	endbr64
    1a44:	48 83 ec 08          	sub    $0x8,%rsp
    1a48:	48 83 c4 08          	add    $0x8,%rsp
    1a4c:	c3                   	ret
