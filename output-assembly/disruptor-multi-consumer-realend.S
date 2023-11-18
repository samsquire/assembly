
disruptor-multi-consumer-realend:     file format elf64-x86-64


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
    11c6:	b9 00 04 00 00       	mov    $0x400,%ecx
    11cb:	ba 0a 00 00 00       	mov    $0xa,%edx
    11d0:	48 8d 35 59 0e 00 00 	lea    0xe59(%rip),%rsi        # 2030 <_IO_stdin_used+0x30>
    11d7:	41 56                	push   %r14
    11d9:	bf 01 00 00 00       	mov    $0x1,%edi
    CPU_ZERO(receivercpu);
    for (int j = 0; j < cores; j++) {
      // printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    }
    for (int n = sender; n < sender + writers_count; n++) {
    11de:	45 31 f6             	xor    %r14d,%r14d
int main() {
    11e1:	41 55                	push   %r13
    11e3:	41 54                	push   %r12
    11e5:	55                   	push   %rbp
    11e6:	53                   	push   %rbx
    11e7:	48 83 ec 68          	sub    $0x68,%rsp
    11eb:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    11f4:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    11f9:	31 c0                	xor    %eax,%eax
    11fb:	e8 70 ff ff ff       	call   1170 <__printf_chk@plt>
    1200:	ba 01 00 00 00       	mov    $0x1,%edx
    1205:	48 8d 35 9e 0e 00 00 	lea    0xe9e(%rip),%rsi        # 20aa <_IO_stdin_used+0xaa>
    120c:	31 c0                	xor    %eax,%eax
    120e:	bf 01 00 00 00       	mov    $0x1,%edi
    1213:	e8 58 ff ff ff       	call   1170 <__printf_chk@plt>
    1218:	ba 02 00 00 00       	mov    $0x2,%edx
    121d:	48 8d 35 96 0e 00 00 	lea    0xe96(%rip),%rsi        # 20ba <_IO_stdin_used+0xba>
    1224:	31 c0                	xor    %eax,%eax
    1226:	bf 01 00 00 00       	mov    $0x1,%edi
    122b:	e8 40 ff ff ff       	call   1170 <__printf_chk@plt>
    1230:	ba 04 00 00 00       	mov    $0x4,%edx
    1235:	48 8d 35 90 0e 00 00 	lea    0xe90(%rip),%rsi        # 20cc <_IO_stdin_used+0xcc>
    123c:	31 c0                	xor    %eax,%eax
    123e:	bf 01 00 00 00       	mov    $0x1,%edi
    1243:	e8 28 ff ff ff       	call   1170 <__printf_chk@plt>
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1248:	be 80 02 00 00       	mov    $0x280,%esi
    124d:	bf 04 00 00 00       	mov    $0x4,%edi
    1252:	e8 09 ff ff ff       	call   1160 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1257:	be 38 00 00 00       	mov    $0x38,%esi
    125c:	bf 04 00 00 00       	mov    $0x4,%edi
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1261:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1264:	e8 f7 fe ff ff       	call   1160 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1269:	be 08 00 00 00       	mov    $0x8,%esi
    126e:	bf 04 00 00 00       	mov    $0x4,%edi
    1273:	49 89 dd             	mov    %rbx,%r13
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1276:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    127b:	e8 e0 fe ff ff       	call   1160 <calloc@plt>
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1280:	be 80 00 00 00       	mov    $0x80,%esi
    1285:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    128a:	48 89 c5             	mov    %rax,%rbp
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    128d:	e8 ce fe ff ff       	call   1160 <calloc@plt>
      CPU_SET(j, receivercpu);
    1292:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1299:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    129e:	be 80 00 00 00       	mov    $0x80,%esi
    12a3:	bf 01 00 00 00       	mov    $0x1,%edi
    12a8:	e8 b3 fe ff ff       	call   1160 <calloc@plt>
      for (int j = 0 ; j < cores ; j++) {
        // printf("assigning sender %d to core %d\n", sender, j);
        CPU_SET(j, sendercpu);
      }
       
      thread_data[n].thread_index = n;
    12ad:	45 89 75 00          	mov    %r14d,0x0(%r13)
      thread_data[n].mode = WRITER;
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    12b1:	be 08 00 00 00       	mov    $0x8,%esi
    12b6:	bf 02 00 00 00       	mov    $0x2,%edi
        CPU_SET(j, sendercpu);
    12bb:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
      thread_data[n].mode = WRITER;
    12c2:	41 c7 85 84 01 00 00 00 00 00 00 	movl   $0x0,0x184(%r13)
      thread_data[n].cpu_set = sendercpu;
    12cd:	49 89 85 98 01 00 00 	mov    %rax,0x198(%r13)
      thread_data[n].running = 1;
    12d4:	41 c7 85 90 01 00 00 01 00 00 00 	movl   $0x1,0x190(%r13)
      thread_data[n].size = buffer_size;
    12df:	49 c7 85 88 01 00 00 00 04 00 00 	movq   $0x400,0x188(%r13)
      thread_data[n].end = 0;
    12ea:	41 c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r13)
      thread_data[n].sender = &thread_data[sender];
    12f5:	49 89 5d 08          	mov    %rbx,0x8(%r13)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    12f9:	e8 62 fe ff ff       	call   1160 <calloc@plt>
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    12fe:	be 80 01 00 00       	mov    $0x180,%esi
    1303:	bf 00 04 00 00       	mov    $0x400,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1308:	49 89 85 00 02 00 00 	mov    %rax,0x200(%r13)
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    130f:	e8 4c fe ff ff       	call   1160 <calloc@plt>
    1314:	49 89 45 18          	mov    %rax,0x18(%r13)
      for (int k = 0 ; k < buffer_size ; k++) {
    1318:	4c 8d b8 80 00 00 00 	lea    0x80(%rax),%r15
    131f:	4c 8d a0 80 00 06 00 	lea    0x60080(%rax),%r12
    1326:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1330:	be 04 00 00 00       	mov    $0x4,%esi
    1335:	bf 02 00 00 00       	mov    $0x2,%edi
      for (int k = 0 ; k < buffer_size ; k++) {
    133a:	49 81 c7 80 01 00 00 	add    $0x180,%r15
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1341:	e8 1a fe ff ff       	call   1160 <calloc@plt>
        thread_data[n].data[k].end = calloc(other_count, sizeof(int));
    1346:	be 04 00 00 00       	mov    $0x4,%esi
    134b:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1350:	49 89 87 00 ff ff ff 	mov    %rax,-0x100(%r15)
        thread_data[n].data[k].end = calloc(other_count, sizeof(int));
    1357:	e8 04 fe ff ff       	call   1160 <calloc@plt>
    135c:	49 89 87 80 fe ff ff 	mov    %rax,-0x180(%r15)
      for (int k = 0 ; k < buffer_size ; k++) {
    1363:	4d 39 e7             	cmp    %r12,%r15
    1366:	75 c8                	jne    1330 <main+0x170>
      }
      thread_data[n].other_count = other_count;
    1368:	41 c7 85 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%r13)
    for (int n = sender; n < sender + writers_count; n++) {
    1373:	49 81 c5 80 02 00 00 	add    $0x280,%r13
    137a:	45 85 f6             	test   %r14d,%r14d
    137d:	75 0b                	jne    138a <main+0x1ca>
    137f:	41 be 01 00 00 00    	mov    $0x1,%r14d
    1385:	e9 14 ff ff ff       	jmp    129e <main+0xde>
    138a:	66 48 0f 6e d3       	movq   %rbx,%xmm2
    138f:	4c 8d bb 00 05 00 00 	lea    0x500(%rbx),%r15
    1396:	31 c0                	xor    %eax,%eax
    1398:	66 0f 6c d2          	punpcklqdq %xmm2,%xmm2
    139c:	4d 89 fd             	mov    %r15,%r13
    139f:	0f 29 14 24          	movaps %xmm2,(%rsp)
    13a3:	8d 50 02             	lea    0x2(%rax),%edx
    }
    // printf("Created data for %d\n", sender);
    int seq[] = {1, 2, 5};
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      thread_data[j].thread_index = j;
      thread_data[j].reader_index = receiver_index;
    13a6:	41 89 85 0c 02 00 00 	mov    %eax,0x20c(%r13)
      thread_data[j].multiple = receiver_index % other_count;
    13ad:	41 89 85 10 02 00 00 	mov    %eax,0x210(%r13)
      thread_data[j].other_count = other_count;
     
      thread_data[j].cpu_set = receivercpu;
    13b4:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
      thread_data[j].running = 1;
    13b9:	41 c7 85 90 01 00 00 01 00 00 00 	movl   $0x1,0x190(%r13)
      thread_data[j].thread_index = j;
    13c4:	41 89 55 00          	mov    %edx,0x0(%r13)
      thread_data[j].other_count = other_count;
    13c8:	41 c7 85 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%r13)
      thread_data[j].cpu_set = receivercpu;
    13d3:	49 89 85 98 01 00 00 	mov    %rax,0x198(%r13)
      thread_data[j].mode = READER;
    13da:	41 c7 85 84 01 00 00 01 00 00 00 	movl   $0x1,0x184(%r13)
      if (j == receiver) {
    13e5:	83 fa 02             	cmp    $0x2,%edx
    13e8:	0f 84 48 03 00 00    	je     1736 <main+0x576>
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    13ee:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
      thread_data[j].sender = &thread_data[sender];
    13f5:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
      thread_data[j].size = buffer_size;
    13fa:	49 c7 85 88 01 00 00 00 04 00 00 	movq   $0x400,0x188(%r13)
    1405:	45 31 c0             	xor    %r8d,%r8d
    1408:	b9 01 00 00 00       	mov    $0x1,%ecx
    140d:	ba 03 00 00 00       	mov    $0x3,%edx
      thread_data[j].start = 0;
    1412:	41 c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r13)
    141d:	48 8d 35 34 0c 00 00 	lea    0xc34(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
      thread_data[j].readers = thread_data[sender].readers;
    1424:	49 89 85 00 02 00 00 	mov    %rax,0x200(%r13)
    142b:	bf 01 00 00 00       	mov    $0x1,%edi
    1430:	31 c0                	xor    %eax,%eax
      thread_data[j].sender = &thread_data[sender];
    1432:	41 0f 11 4d 08       	movups %xmm1,0x8(%r13)
    1437:	e8 34 fd ff ff       	call   1170 <__printf_chk@plt>
      printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        thread_data[n].readers[receiver_index] = &thread_data[j];
    143c:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    1443:	31 d2                	xor    %edx,%edx
    1445:	48 8d 35 97 0c 00 00 	lea    0xc97(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    144c:	bf 01 00 00 00       	mov    $0x1,%edi
    1451:	4c 89 68 08          	mov    %r13,0x8(%rax)
    1455:	48 8b 83 80 04 00 00 	mov    0x480(%rbx),%rax
    145c:	4c 89 68 08          	mov    %r13,0x8(%rax)
    1460:	31 c0                	xor    %eax,%eax
    1462:	e8 09 fd ff ff       	call   1170 <__printf_chk@plt>
      }
    }
    printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    1467:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    146a:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    146f:	c7 44 24 2c 00 00 00 00 	movl   $0x0,0x2c(%rsp)
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1477:	4c 8d 6d 10          	lea    0x10(%rbp),%r13
    147b:	41 be 02 00 00 00    	mov    $0x2,%r14d
    1481:	4c 8d 60 70          	lea    0x70(%rax),%r12
    1485:	48 8d 35 57 0c 00 00 	lea    0xc57(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    148c:	bf 01 00 00 00       	mov    $0x1,%edi
    1491:	31 c0                	xor    %eax,%eax
    1493:	44 89 f2             	mov    %r14d,%edx
    1496:	e8 d5 fc ff ff       	call   1170 <__printf_chk@plt>
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    149b:	31 f6                	xor    %esi,%esi
    149d:	4c 89 e7             	mov    %r12,%rdi
    14a0:	e8 ab fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    14a5:	85 c0                	test   %eax,%eax
    14a7:	0f 85 45 03 00 00    	jne    17f2 <main+0x632>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    14ad:	48 8d 74 24 2c       	lea    0x2c(%rsp),%rsi
    14b2:	4c 89 e7             	mov    %r12,%rdi
    14b5:	e8 d6 fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    14ba:	85 c0                	test   %eax,%eax
    14bc:	0f 85 4b 03 00 00    	jne    180d <main+0x64d>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    14c2:	4c 89 f9             	mov    %r15,%rcx
    14c5:	4c 89 e6             	mov    %r12,%rsi
    14c8:	4c 89 ef             	mov    %r13,%rdi
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    14cb:	49 83 c4 38          	add    $0x38,%r12
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    14cf:	48 8d 15 4a 04 00 00 	lea    0x44a(%rip),%rdx        # 1920 <disruptor_thread>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    14d6:	49 83 c5 08          	add    $0x8,%r13
    14da:	49 81 c7 80 02 00 00 	add    $0x280,%r15
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    14e1:	e8 9a fc ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    14e6:	49 8b 7d f8          	mov    -0x8(%r13),%rdi
    14ea:	be 08 00 00 00       	mov    $0x8,%esi
    14ef:	48 8b 93 98 06 00 00 	mov    0x698(%rbx),%rdx
    14f6:	e8 05 fc ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    14fb:	41 83 fe 02          	cmp    $0x2,%r14d
    14ff:	75 0b                	jne    150c <main+0x34c>
    1501:	41 be 03 00 00 00    	mov    $0x3,%r14d
    1507:	e9 79 ff ff ff       	jmp    1485 <main+0x2c5>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    150c:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    1511:	31 f6                	xor    %esi,%esi
    1513:	4c 89 f7             	mov    %r14,%rdi
    1516:	e8 35 fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    151b:	85 c0                	test   %eax,%eax
    151d:	0f 85 cf 02 00 00    	jne    17f2 <main+0x632>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1523:	48 8d 74 24 28       	lea    0x28(%rsp),%rsi
    1528:	4c 89 f7             	mov    %r14,%rdi
      param2.sched_priority = 0;
    152b:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1533:	e8 58 fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1538:	85 c0                	test   %eax,%eax
    153a:	0f 85 cd 02 00 00    	jne    180d <main+0x64d>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    1540:	48 89 d9             	mov    %rbx,%rcx
    1543:	48 89 ef             	mov    %rbp,%rdi
    1546:	48 8d 15 d3 03 00 00 	lea    0x3d3(%rip),%rdx        # 1920 <disruptor_thread>
    154d:	4c 89 f6             	mov    %r14,%rsi
    1550:	e8 2b fc ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    1555:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    1559:	be 08 00 00 00       	mov    $0x8,%esi
    void * res1;
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    155e:	45 31 e4             	xor    %r12d,%r12d
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    1561:	48 8b 93 98 01 00 00 	mov    0x198(%rbx),%rdx
    1568:	e8 93 fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    156d:	4c 89 f6             	mov    %r14,%rsi
    1570:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
    1574:	48 8d 8b 80 02 00 00 	lea    0x280(%rbx),%rcx
    157b:	48 83 c6 38          	add    $0x38,%rsi
    157f:	48 8d 15 9a 03 00 00 	lea    0x39a(%rip),%rdx        # 1920 <disruptor_thread>
    1586:	e8 f5 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    158b:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
    158f:	be 08 00 00 00       	mov    $0x8,%esi
    1594:	48 8b 93 18 04 00 00 	mov    0x418(%rbx),%rdx
    159b:	e8 60 fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
  struct timespec preempt = {
    15a0:	66 0f 6f 05 f8 0b 00 00 	movdqa 0xbf8(%rip),%xmm0        # 21a0 <_IO_stdin_used+0x1a0>
    15a8:	ba 14 00 00 00       	mov    $0x14,%edx
    15ad:	31 c0                	xor    %eax,%eax
    15af:	48 8d 35 85 0b 00 00 	lea    0xb85(%rip),%rsi        # 213b <_IO_stdin_used+0x13b>
    15b6:	bf 01 00 00 00       	mov    $0x1,%edi
    15bb:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    15c0:	e8 ab fb ff ff       	call   1170 <__printf_chk@plt>
  nanosleep(&preempt , &rem2);
    15c5:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    15ca:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    15cf:	e8 6c fb ff ff       	call   1140 <nanosleep@plt>
      pthread_join(thread[n], res1);
    15d4:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    15d8:	4c 89 e6             	mov    %r12,%rsi
    thread_data[sender].running = 0;
    15db:	c7 83 90 01 00 00 00 00 00 00 	movl   $0x0,0x190(%rbx)
      thread_data[j].running = 0;
    15e5:	c7 83 90 06 00 00 00 00 00 00 	movl   $0x0,0x690(%rbx)
    15ef:	c7 83 10 09 00 00 00 00 00 00 	movl   $0x0,0x910(%rbx)
      thread_data[n].running = 0;
    15f9:	c7 83 90 01 00 00 00 00 00 00 	movl   $0x0,0x190(%rbx)
    1603:	c7 83 10 04 00 00 00 00 00 00 	movl   $0x0,0x410(%rbx)
      pthread_join(thread[n], res1);
    160d:	e8 9e fb ff ff       	call   11b0 <pthread_join@plt>
    1612:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
    1616:	4c 89 e6             	mov    %r12,%rsi
    1619:	e8 92 fb ff ff       	call   11b0 <pthread_join@plt>
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    161e:	48 8b 7d 10          	mov    0x10(%rbp),%rdi
    1622:	4c 89 e6             	mov    %r12,%rsi
    1625:	e8 86 fb ff ff       	call   11b0 <pthread_join@plt>
    162a:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
    162e:	4c 89 e6             	mov    %r12,%rsi
    1631:	31 ed                	xor    %ebp,%ebp
    1633:	4c 8d 25 30 0b 00 00 	lea    0xb30(%rip),%r12        # 216a <_IO_stdin_used+0x16a>
    163a:	e8 71 fb ff ff       	call   11b0 <pthread_join@plt>
    163f:	ba 02 00 00 00       	mov    $0x2,%edx
    1644:	48 8d 35 09 0b 00 00 	lea    0xb09(%rip),%rsi        # 2154 <_IO_stdin_used+0x154>
    164b:	31 c0                	xor    %eax,%eax
    164d:	bf 01 00 00 00       	mov    $0x1,%edi
    1652:	e8 19 fb ff ff       	call   1170 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    1657:	eb 1b                	jmp    1674 <main+0x4b4>
    1659:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1660:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    1667:	48 81 fd 00 00 06 00 	cmp    $0x60000,%rbp
    166e:	0f 84 88 00 00 00    	je     16fc <main+0x53c>
      int compcount = 0;
      for (int n = 0 ; n < 2 ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    1674:	48 8b 43 18          	mov    0x18(%rbx),%rax
    1678:	48 01 e8             	add    %rbp,%rax
    167b:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
    1682:	83 3a 01             	cmpl   $0x1,(%rdx)
    1685:	75 d9                	jne    1660 <main+0x4a0>
    1687:	83 7a 04 01          	cmpl   $0x1,0x4(%rdx)
    168b:	75 d3                	jne    1660 <main+0x4a0>
      // printf("%d\n", compcount);
      if (compcount == other_count) {
      for (int n = 0 ; n < other_count ; n++) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
          struct timespec end = thread_data[sender].data[y].end[n];
    168d:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    1694:	31 c9                	xor    %ecx,%ecx
    1696:	4c 89 e6             	mov    %r12,%rsi
    1699:	bf 01 00 00 00       	mov    $0x1,%edi
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    169e:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    16a2:	4c 8b 02             	mov    (%rdx),%r8
    16a5:	31 d2                	xor    %edx,%edx
    16a7:	4c 2b 48 08          	sub    0x8(%rax),%r9
    16ab:	4c 2b 00             	sub    (%rax),%r8
    16ae:	31 c0                	xor    %eax,%eax
    16b0:	e8 bb fa ff ff       	call   1170 <__printf_chk@plt>
          struct timespec start = thread_data[sender].data[y].start;
    16b5:	48 8b 43 18          	mov    0x18(%rbx),%rax
    16b9:	31 c9                	xor    %ecx,%ecx
    16bb:	4c 89 e6             	mov    %r12,%rsi
    16be:	bf 01 00 00 00       	mov    $0x1,%edi
    16c3:	48 01 e8             	add    %rbp,%rax
    for (int y = 0 ; y < buffer_size; y++) {
    16c6:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
          struct timespec end = thread_data[sender].data[y].end[n];
    16cd:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    16d4:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    16d8:	4c 8b 42 10          	mov    0x10(%rdx),%r8
    16dc:	ba 01 00 00 00       	mov    $0x1,%edx
    16e1:	4c 2b 48 08          	sub    0x8(%rax),%r9
    16e5:	4c 2b 00             	sub    (%rax),%r8
    16e8:	31 c0                	xor    %eax,%eax
    16ea:	e8 81 fa ff ff       	call   1170 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    16ef:	48 81 fd 00 00 06 00 	cmp    $0x60000,%rbp
    16f6:	0f 85 78 ff ff ff    	jne    1674 <main+0x4b4>
    16fc:	31 d2                	xor    %edx,%edx
    16fe:	31 c0                	xor    %eax,%eax
    1700:	48 8d 35 7a 0a 00 00 	lea    0xa7a(%rip),%rsi        # 2181 <_IO_stdin_used+0x181>
    1707:	bf 01 00 00 00       	mov    $0x1,%edi
    170c:	e8 5f fa ff ff       	call   1170 <__printf_chk@plt>
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    1711:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    1716:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    171f:	0f 85 e3 00 00 00    	jne    1808 <main+0x648>
    1725:	48 83 c4 68          	add    $0x68,%rsp
    1729:	31 c0                	xor    %eax,%eax
    172b:	5b                   	pop    %rbx
    172c:	5d                   	pop    %rbp
    172d:	41 5c                	pop    %r12
    172f:	41 5d                	pop    %r13
    1731:	41 5e                	pop    %r14
    1733:	41 5f                	pop    %r15
    1735:	c3                   	ret
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    1736:	be 80 01 00 00       	mov    $0x180,%esi
    173b:	bf 00 04 00 00       	mov    $0x400,%edi
    1740:	e8 1b fa ff ff       	call   1160 <calloc@plt>
    1745:	49 89 45 18          	mov    %rax,0x18(%r13)
    1749:	49 89 c4             	mov    %rax,%r12
        for (int n = 0 ; n < buffer_size ; n++) {
    174c:	4c 8d b0 00 01 00 00 	lea    0x100(%rax),%r14
    1753:	49 81 c4 00 01 06 00 	add    $0x60100,%r12
    175a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1760:	be 04 00 00 00       	mov    $0x4,%esi
    1765:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    176a:	49 81 c6 80 01 00 00 	add    $0x180,%r14
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1771:	e8 ea f9 ff ff       	call   1160 <calloc@plt>
    1776:	49 89 86 80 fe ff ff 	mov    %rax,-0x180(%r14)
        for (int n = 0 ; n < buffer_size ; n++) {
    177d:	4d 39 f4             	cmp    %r14,%r12
    1780:	75 de                	jne    1760 <main+0x5a0>
      thread_data[j].sender = &thread_data[sender];
    1782:	66 0f 6f 1c 24       	movdqa (%rsp),%xmm3
    1787:	45 31 c0             	xor    %r8d,%r8d
    178a:	31 c9                	xor    %ecx,%ecx
    178c:	ba 02 00 00 00       	mov    $0x2,%edx
      thread_data[j].readers = thread_data[sender].readers;
    1791:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    1798:	48 8d 35 b9 08 00 00 	lea    0x8b9(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
      thread_data[j].size = buffer_size;
    179f:	49 c7 85 88 01 00 00 00 04 00 00 	movq   $0x400,0x188(%r13)
    17aa:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].start = 0;
    17af:	41 c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r13)
      thread_data[j].readers = thread_data[sender].readers;
    17ba:	49 89 85 00 02 00 00 	mov    %rax,0x200(%r13)
    17c1:	31 c0                	xor    %eax,%eax
      thread_data[j].sender = &thread_data[sender];
    17c3:	41 0f 11 5d 08       	movups %xmm3,0x8(%r13)
    17c8:	e8 a3 f9 ff ff       	call   1170 <__printf_chk@plt>
        thread_data[n].readers[receiver_index] = &thread_data[j];
    17cd:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    17d4:	4c 89 28             	mov    %r13,(%rax)
    17d7:	48 8b 83 80 04 00 00 	mov    0x480(%rbx),%rax
    17de:	4c 89 28             	mov    %r13,(%rax)
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    17e1:	49 81 c5 80 02 00 00 	add    $0x280,%r13
    17e8:	b8 01 00 00 00       	mov    $0x1,%eax
    17ed:	e9 b1 fb ff ff       	jmp    13a3 <main+0x1e3>
    17f2:	48 8d 3d 07 09 00 00 	lea    0x907(%rip),%rdi        # 2100 <_IO_stdin_used+0x100>
    17f9:	e8 12 f9 ff ff       	call   1110 <puts@plt>
               exit(1);
    17fe:	bf 01 00 00 00       	mov    $0x1,%edi
    1803:	e8 98 f9 ff ff       	call   11a0 <exit@plt>
}
    1808:	e8 23 f9 ff ff       	call   1130 <__stack_chk_fail@plt>
    180d:	48 8d 3d 0a 09 00 00 	lea    0x90a(%rip),%rdi        # 211e <_IO_stdin_used+0x11e>
    1814:	e8 f7 f8 ff ff       	call   1110 <puts@plt>
              exit(1);
    1819:	bf 01 00 00 00       	mov    $0x1,%edi
    181e:	e8 7d f9 ff ff       	call   11a0 <exit@plt>
    1823:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    182d:	0f 1f 00             	nopl   (%rax)

0000000000001830 <_start>:
    1830:	f3 0f 1e fa          	endbr64
    1834:	31 ed                	xor    %ebp,%ebp
    1836:	49 89 d1             	mov    %rdx,%r9
    1839:	5e                   	pop    %rsi
    183a:	48 89 e2             	mov    %rsp,%rdx
    183d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1841:	50                   	push   %rax
    1842:	54                   	push   %rsp
    1843:	45 31 c0             	xor    %r8d,%r8d
    1846:	31 c9                	xor    %ecx,%ecx
    1848:	48 8d 3d 71 f9 ff ff 	lea    -0x68f(%rip),%rdi        # 11c0 <main>
    184f:	ff 15 83 27 00 00    	call   *0x2783(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1855:	f4                   	hlt
    1856:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001860 <deregister_tm_clones>:
    1860:	48 8d 3d a9 27 00 00 	lea    0x27a9(%rip),%rdi        # 4010 <__TMC_END__>
    1867:	48 8d 05 a2 27 00 00 	lea    0x27a2(%rip),%rax        # 4010 <__TMC_END__>
    186e:	48 39 f8             	cmp    %rdi,%rax
    1871:	74 15                	je     1888 <deregister_tm_clones+0x28>
    1873:	48 8b 05 66 27 00 00 	mov    0x2766(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    187a:	48 85 c0             	test   %rax,%rax
    187d:	74 09                	je     1888 <deregister_tm_clones+0x28>
    187f:	ff e0                	jmp    *%rax
    1881:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1888:	c3                   	ret
    1889:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001890 <register_tm_clones>:
    1890:	48 8d 3d 79 27 00 00 	lea    0x2779(%rip),%rdi        # 4010 <__TMC_END__>
    1897:	48 8d 35 72 27 00 00 	lea    0x2772(%rip),%rsi        # 4010 <__TMC_END__>
    189e:	48 29 fe             	sub    %rdi,%rsi
    18a1:	48 89 f0             	mov    %rsi,%rax
    18a4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    18a8:	48 c1 f8 03          	sar    $0x3,%rax
    18ac:	48 01 c6             	add    %rax,%rsi
    18af:	48 d1 fe             	sar    %rsi
    18b2:	74 14                	je     18c8 <register_tm_clones+0x38>
    18b4:	48 8b 05 35 27 00 00 	mov    0x2735(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    18bb:	48 85 c0             	test   %rax,%rax
    18be:	74 08                	je     18c8 <register_tm_clones+0x38>
    18c0:	ff e0                	jmp    *%rax
    18c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    18c8:	c3                   	ret
    18c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018d0 <__do_global_dtors_aux>:
    18d0:	f3 0f 1e fa          	endbr64
    18d4:	80 3d 35 27 00 00 00 	cmpb   $0x0,0x2735(%rip)        # 4010 <__TMC_END__>
    18db:	75 2b                	jne    1908 <__do_global_dtors_aux+0x38>
    18dd:	55                   	push   %rbp
    18de:	48 83 3d 12 27 00 00 00 	cmpq   $0x0,0x2712(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    18e6:	48 89 e5             	mov    %rsp,%rbp
    18e9:	74 0c                	je     18f7 <__do_global_dtors_aux+0x27>
    18eb:	48 8b 3d 16 27 00 00 	mov    0x2716(%rip),%rdi        # 4008 <__dso_handle>
    18f2:	e8 f9 f7 ff ff       	call   10f0 <__cxa_finalize@plt>
    18f7:	e8 64 ff ff ff       	call   1860 <deregister_tm_clones>
    18fc:	c6 05 0d 27 00 00 01 	movb   $0x1,0x270d(%rip)        # 4010 <__TMC_END__>
    1903:	5d                   	pop    %rbp
    1904:	c3                   	ret
    1905:	0f 1f 00             	nopl   (%rax)
    1908:	c3                   	ret
    1909:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001910 <frame_dummy>:
    1910:	f3 0f 1e fa          	endbr64
    1914:	e9 77 ff ff ff       	jmp    1890 <register_tm_clones>
    1919:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001920 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    1920:	f3 0f 1e fa          	endbr64
    1924:	41 56                	push   %r14
    1926:	48 8d 35 db 06 00 00 	lea    0x6db(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    192d:	31 c0                	xor    %eax,%eax
    192f:	41 55                	push   %r13
    1931:	41 54                	push   %r12
    1933:	55                   	push   %rbp
    1934:	53                   	push   %rbx
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    1935:	8b 8f 84 01 00 00    	mov    0x184(%rdi),%ecx
void * disruptor_thread(void * arg) {
    193b:	48 89 fb             	mov    %rdi,%rbx
    193e:	8b 17                	mov    (%rdi),%edx
    1940:	bf 01 00 00 00       	mov    $0x1,%edi
    1945:	e8 26 f8 ff ff       	call   1170 <__printf_chk@plt>
  if (data->mode == WRITER) {
    194a:	8b 83 84 01 00 00    	mov    0x184(%rbx),%eax
    1950:	85 c0                	test   %eax,%eax
    1952:	74 33                	je     1987 <disruptor_thread+0x67>
  } else if (data->mode == READER) {
    1954:	8b 83 84 01 00 00    	mov    0x184(%rbx),%eax
    195a:	83 f8 01             	cmp    $0x1,%eax
    195d:	0f 84 f3 00 00 00    	je     1a56 <disruptor_thread+0x136>
  printf("Finished %d\n", data->mode);
    1963:	8b 93 84 01 00 00    	mov    0x184(%rbx),%edx
    1969:	48 8d 35 21 07 00 00 	lea    0x721(%rip),%rsi        # 2091 <_IO_stdin_used+0x91>
    1970:	bf 01 00 00 00       	mov    $0x1,%edi
    1975:	31 c0                	xor    %eax,%eax
    1977:	e8 f4 f7 ff ff       	call   1170 <__printf_chk@plt>
}
    197c:	5b                   	pop    %rbx
    197d:	31 c0                	xor    %eax,%eax
    197f:	5d                   	pop    %rbp
    1980:	41 5c                	pop    %r12
    1982:	41 5d                	pop    %r13
    1984:	41 5e                	pop    %r14
    1986:	c3                   	ret
    1987:	48 8d 3d f7 06 00 00 	lea    0x6f7(%rip),%rdi        # 2085 <_IO_stdin_used+0x85>
    198e:	e8 7d f7 ff ff       	call   1110 <puts@plt>
    struct Thread *me = data->sender;
    1993:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    while (data->running == 1) {
    1997:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    19a0:	8b 83 90 01 00 00    	mov    0x190(%rbx),%eax
    19a6:	83 f8 01             	cmp    $0x1,%eax
    19a9:	75 b8                	jne    1963 <disruptor_thread+0x43>
      asm volatile ("sfence" ::: "memory");
    19ab:	0f ae f8             	sfence
      for (int x  = 0 ; x < data->other_count; x++) {
    19ae:	48 63 8b 08 02 00 00 	movslq 0x208(%rbx),%rcx
    19b5:	85 c9                	test   %ecx,%ecx
    19b7:	7e 3f                	jle    19f8 <disruptor_thread+0xd8>
        if ((me->end + 1) % data->size == data->readers[x]->start) {
    19b9:	8b 85 00 01 00 00    	mov    0x100(%rbp),%eax
    19bf:	83 c0 01             	add    $0x1,%eax
    19c2:	48 98                	cltq
    19c4:	48 99                	cqto
    19c6:	48 f7 bb 88 01 00 00 	idivq  0x188(%rbx)
    19cd:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    19d4:	48 8d 34 c8          	lea    (%rax,%rcx,8),%rsi
    19d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    19e0:	48 8b 08             	mov    (%rax),%rcx
    19e3:	48 63 89 80 00 00 00 	movslq 0x80(%rcx),%rcx
    19ea:	48 39 ca             	cmp    %rcx,%rdx
    19ed:	74 b1                	je     19a0 <disruptor_thread+0x80>
      for (int x  = 0 ; x < data->other_count; x++) {
    19ef:	48 83 c0 08          	add    $0x8,%rax
    19f3:	48 39 c6             	cmp    %rax,%rsi
    19f6:	75 e8                	jne    19e0 <disruptor_thread+0xc0>
            if (changed = __atomic_add_fetch(&me->end, 1, __ATOMIC_ACQUIRE)) {
    19f8:	b8 01 00 00 00       	mov    $0x1,%eax
    19fd:	f0 0f c1 85 00 01 00 00 	lock xadd %eax,0x100(%rbp)
    1a05:	83 c0 01             	add    $0x1,%eax
    1a08:	74 96                	je     19a0 <disruptor_thread+0x80>
              int dest = (changed) % me->size;
    1a0a:	48 98                	cltq
    1a0c:	48 99                	cqto
    1a0e:	48 f7 bd 88 01 00 00 	idivq  0x188(%rbp)
              for (int x = 0 ; x < data->other_count; x++) {
    1a15:	8b 83 08 02 00 00    	mov    0x208(%rbx),%eax
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[dest].start);
    1a1b:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
    1a1f:	48 c1 e6 07          	shl    $0x7,%rsi
    1a23:	48 03 75 18          	add    0x18(%rbp),%rsi
              for (int x = 0 ; x < data->other_count; x++) {
    1a27:	85 c0                	test   %eax,%eax
    1a29:	7e 1c                	jle    1a47 <disruptor_thread+0x127>
                me->data[dest].complete[x] = 0;
    1a2b:	48 8b 96 00 01 00 00 	mov    0x100(%rsi),%rdx
    1a32:	31 c0                	xor    %eax,%eax
    1a34:	c7 04 82 00 00 00 00 	movl   $0x0,(%rdx,%rax,4)
              for (int x = 0 ; x < data->other_count; x++) {
    1a3b:	48 83 c0 01          	add    $0x1,%rax
    1a3f:	39 83 08 02 00 00    	cmp    %eax,0x208(%rbx)
    1a45:	7f ed                	jg     1a34 <disruptor_thread+0x114>
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[dest].start);
    1a47:	bf 04 00 00 00       	mov    $0x4,%edi
    1a4c:	e8 cf f6 ff ff       	call   1120 <clock_gettime@plt>
    1a51:	e9 4a ff ff ff       	jmp    19a0 <disruptor_thread+0x80>
    1a56:	48 8d 3d 41 06 00 00 	lea    0x641(%rip),%rdi        # 209e <_IO_stdin_used+0x9e>
    1a5d:	e8 ae f6 ff ff       	call   1110 <puts@plt>
    struct Thread *sender = data->sender;
    1a62:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    struct Snapshot * rdata = sender->data;
    1a66:	4c 8b 6d 18          	mov    0x18(%rbp),%r13
    while (data->running == 1) {
    1a6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1a70:	8b 83 90 01 00 00    	mov    0x190(%rbx),%eax
    1a76:	83 f8 01             	cmp    $0x1,%eax
    1a79:	0f 85 e4 fe ff ff    	jne    1963 <disruptor_thread+0x43>
      if ((sender->end % sender->size) == data->start) {
    1a7f:	48 63 85 00 01 00 00 	movslq 0x100(%rbp),%rax
    1a86:	44 8b a3 80 00 00 00 	mov    0x80(%rbx),%r12d
    1a8d:	48 99                	cqto
    1a8f:	48 f7 bd 88 01 00 00 	idivq  0x188(%rbp)
    1a96:	49 63 c4             	movslq %r12d,%rax
    1a99:	48 39 c2             	cmp    %rax,%rdx
    1a9c:	74 d2                	je     1a70 <disruptor_thread+0x150>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1a9e:	4c 8d 34 40          	lea    (%rax,%rax,2),%r14
    1aa2:	48 63 b3 0c 02 00 00 	movslq 0x20c(%rbx),%rsi
    1aa9:	bf 04 00 00 00       	mov    $0x4,%edi
    1aae:	49 c1 e6 07          	shl    $0x7,%r14
    1ab2:	4d 01 ee             	add    %r13,%r14
    1ab5:	48 c1 e6 04          	shl    $0x4,%rsi
    1ab9:	49 03 b6 80 00 00 00 	add    0x80(%r14),%rsi
    1ac0:	e8 5b f6 ff ff       	call   1120 <clock_gettime@plt>
              rdata[changed].complete[data->reader_index] = 1;
    1ac5:	49 8b 86 00 01 00 00 	mov    0x100(%r14),%rax
    1acc:	48 63 93 0c 02 00 00 	movslq 0x20c(%rbx),%rdx
    1ad3:	c7 04 90 01 00 00 00 	movl   $0x1,(%rax,%rdx,4)
              data->start = (changed + 1) % data->size;
    1ada:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    1adf:	48 98                	cltq
    1ae1:	48 99                	cqto
    1ae3:	48 f7 bb 88 01 00 00 	idivq  0x188(%rbx)
    1aea:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
              asm volatile ("sfence" ::: "memory");
    1af0:	0f ae f8             	sfence
    1af3:	e9 78 ff ff ff       	jmp    1a70 <disruptor_thread+0x150>
    1af8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000001b00 <min>:
int min(long a, long b) {
    1b00:	f3 0f 1e fa          	endbr64
  if (a < b) return a;
    1b04:	48 39 f7             	cmp    %rsi,%rdi
    1b07:	7c 02                	jl     1b0b <min+0xb>
  if (b < a) return b;
    1b09:	7f 05                	jg     1b10 <min+0x10>
  if (a < b) return a;
    1b0b:	89 f8                	mov    %edi,%eax
    1b0d:	c3                   	ret
    1b0e:	66 90                	xchg   %ax,%ax
  if (b < a) return b;
    1b10:	89 f0                	mov    %esi,%eax
}
    1b12:	c3                   	ret

Disassembly of section .fini:

0000000000001b14 <_fini>:
    1b14:	f3 0f 1e fa          	endbr64
    1b18:	48 83 ec 08          	sub    $0x8,%rsp
    1b1c:	48 83 c4 08          	add    $0x8,%rsp
    1b20:	c3                   	ret
