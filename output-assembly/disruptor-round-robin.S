
disruptor-round-robin:     file format elf64-x86-64


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
    11c6:	ba 00 00 04 00       	mov    $0x40000,%edx
    11cb:	bf 01 00 00 00       	mov    $0x1,%edi
    11d0:	48 8d 35 82 0e 00 00 	lea    0xe82(%rip),%rsi        # 2059 <_IO_stdin_used+0x59>
    11d7:	41 56                	push   %r14
    11d9:	41 55                	push   %r13
    11db:	41 54                	push   %r12
    11dd:	55                   	push   %rbp
    11de:	53                   	push   %rbx
    11df:	48 83 ec 58          	sub    $0x58,%rsp
    11e3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    11ec:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    11f1:	31 c0                	xor    %eax,%eax
    11f3:	e8 78 ff ff ff       	call   1170 <__printf_chk@plt>
    11f8:	ba 01 00 00 00       	mov    $0x1,%edx
    11fd:	48 8d 35 73 0e 00 00 	lea    0xe73(%rip),%rsi        # 2077 <_IO_stdin_used+0x77>
    1204:	31 c0                	xor    %eax,%eax
    1206:	bf 01 00 00 00       	mov    $0x1,%edi
    120b:	e8 60 ff ff ff       	call   1170 <__printf_chk@plt>
    1210:	ba 02 00 00 00       	mov    $0x2,%edx
    1215:	48 8d 35 6b 0e 00 00 	lea    0xe6b(%rip),%rsi        # 2087 <_IO_stdin_used+0x87>
    121c:	31 c0                	xor    %eax,%eax
    121e:	bf 01 00 00 00       	mov    $0x1,%edi
    1223:	e8 48 ff ff ff       	call   1170 <__printf_chk@plt>
    1228:	ba 03 00 00 00       	mov    $0x3,%edx
    122d:	48 8d 35 65 0e 00 00 	lea    0xe65(%rip),%rsi        # 2099 <_IO_stdin_used+0x99>
    1234:	31 c0                	xor    %eax,%eax
    1236:	bf 01 00 00 00       	mov    $0x1,%edi
    123b:	e8 30 ff ff ff       	call   1170 <__printf_chk@plt>
  printf("Group count %d\n", groups);
  int readers_count = 2;
  printf("Readers count %d\n", readers_count);
  int thread_count = groups * (readers_count + 1);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1240:	be 50 00 00 00       	mov    $0x50,%esi
    1245:	bf 03 00 00 00       	mov    $0x3,%edi
    124a:	e8 11 ff ff ff       	call   1160 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    124f:	be 38 00 00 00       	mov    $0x38,%esi
    1254:	bf 03 00 00 00       	mov    $0x3,%edi
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1259:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    125c:	e8 ff fe ff ff       	call   1160 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1261:	be 08 00 00 00       	mov    $0x8,%esi
    1266:	bf 03 00 00 00       	mov    $0x3,%edi
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    126b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1270:	e8 eb fe ff ff       	call   1160 <calloc@plt>
  int curcore = 0;
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 3; 
    int receiver = sender + 1; 
    int receiver2 = receiver + 1; 
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1275:	be 80 00 00 00       	mov    $0x80,%esi
    127a:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    127f:	49 89 c5             	mov    %rax,%r13
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1282:	e8 d9 fe ff ff       	call   1160 <calloc@plt>
    CPU_ZERO(sendercpu);
    for (int j = 0 ; j < cores; j++) {
      // printf("assigning sender %d to core %d\n", sender, j);
      CPU_SET(j, sendercpu);
    }
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1287:	be 80 00 00 00       	mov    $0x80,%esi
    128c:	bf 01 00 00 00       	mov    $0x1,%edi
      CPU_SET(j, sendercpu);
    1291:	48 83 08 3f          	orq    $0x3f,(%rax)
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1295:	48 89 c5             	mov    %rax,%rbp
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1298:	e8 c3 fe ff ff       	call   1160 <calloc@plt>
      // printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    }
     
    thread_data[sender].thread_index = sender;
    thread_data[sender].cpu_set = sendercpu;
    129d:	48 89 6b 38          	mov    %rbp,0x38(%rbx)
    thread_data[sender].mode = WRITER;
    thread_data[sender].running = 1;
    thread_data[sender].size = buffer_size;
    thread_data[sender].readers = calloc(readers_count, sizeof(struct Thread*));
    12a1:	be 08 00 00 00       	mov    $0x8,%esi
    12a6:	bf 02 00 00 00       	mov    $0x2,%edi
      CPU_SET(j, receivercpu);
    12ab:	48 83 08 3f          	orq    $0x3f,(%rax)
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12af:	49 89 c6             	mov    %rax,%r14
    thread_data[sender].mode = WRITER;
    12b2:	c7 43 20 00 00 00 00 	movl   $0x0,0x20(%rbx)
    thread_data[sender].thread_index = sender;
    12b9:	c7 03 00 00 00 00    	movl   $0x0,(%rbx)
    thread_data[sender].running = 1;
    12bf:	c7 43 30 01 00 00 00 	movl   $0x1,0x30(%rbx)
    thread_data[sender].size = buffer_size;
    12c6:	48 c7 43 28 00 00 04 00 	movq   $0x40000,0x28(%rbx)
    thread_data[sender].readers = calloc(readers_count, sizeof(struct Thread*));
    12ce:	e8 8d fe ff ff       	call   1160 <calloc@plt>
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    12d3:	be 20 00 00 00       	mov    $0x20,%esi
    12d8:	bf 00 00 04 00       	mov    $0x40000,%edi
    thread_data[sender].readers = calloc(readers_count, sizeof(struct Thread*));
    12dd:	48 89 43 40          	mov    %rax,0x40(%rbx)
    12e1:	49 89 c7             	mov    %rax,%r15
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    12e4:	e8 77 fe ff ff       	call   1160 <calloc@plt>
    12e9:	48 89 43 10          	mov    %rax,0x10(%rbx)
    12ed:	48 89 c5             	mov    %rax,%rbp
    for (int n = 0 ; n < buffer_size ; n++) {
    12f0:	4c 8d 60 10          	lea    0x10(%rax),%r12
    12f4:	48 81 c5 10 00 80 00 	add    $0x800010,%rbp
    12fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      thread_data[sender].data[n].end = calloc(readers_count, sizeof(struct timespec));
    1300:	be 10 00 00 00       	mov    $0x10,%esi
    1305:	bf 02 00 00 00       	mov    $0x2,%edi
    for (int n = 0 ; n < buffer_size ; n++) {
    130a:	49 83 c4 20          	add    $0x20,%r12
      thread_data[sender].data[n].end = calloc(readers_count, sizeof(struct timespec));
    130e:	e8 4d fe ff ff       	call   1160 <calloc@plt>
      thread_data[sender].data[n].complete = calloc(readers_count, sizeof(int));
    1313:	be 04 00 00 00       	mov    $0x4,%esi
    1318:	bf 02 00 00 00       	mov    $0x2,%edi
      thread_data[sender].data[n].end = calloc(readers_count, sizeof(struct timespec));
    131d:	49 89 44 24 e0       	mov    %rax,-0x20(%r12)
      thread_data[sender].data[n].complete = calloc(readers_count, sizeof(int));
    1322:	e8 39 fe ff ff       	call   1160 <calloc@plt>
    1327:	49 89 44 24 e8       	mov    %rax,-0x18(%r12)
    for (int n = 0 ; n < buffer_size ; n++) {
    132c:	4c 39 e5             	cmp    %r12,%rbp
    132f:	75 cf                	jne    1300 <main+0x140>
    }
    thread_data[sender].readers_count = readers_count;
    // printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
      thread_data[j].thread_index = j;
    1331:	4c 8d 63 50          	lea    0x50(%rbx),%r12
    thread_data[sender].readers_count = readers_count;
    1335:	c7 43 48 02 00 00 00 	movl   $0x2,0x48(%rbx)
    133c:	31 c9                	xor    %ecx,%ecx
    133e:	31 c0                	xor    %eax,%eax
      thread_data[j].reader_index = receiver_index;
      thread_data[j].cpu_set = receivercpu;
      thread_data[j].running = 1;
    1340:	c7 83 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rbx)
    134a:	48 8d 2d df 0c 00 00 	lea    0xcdf(%rip),%rbp        # 2030 <_IO_stdin_used+0x30>
    1351:	ba 01 00 00 00       	mov    $0x1,%edx
    1356:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].thread_index = j;
    135b:	c7 43 50 01 00 00 00 	movl   $0x1,0x50(%rbx)
    1362:	48 89 ee             	mov    %rbp,%rsi
      thread_data[j].reader_index = receiver_index;
    1365:	c7 83 9c 00 00 00 00 00 00 00 	movl   $0x0,0x9c(%rbx)
      thread_data[j].cpu_set = receivercpu;
    136f:	4c 89 b3 88 00 00 00 	mov    %r14,0x88(%rbx)
      thread_data[j].mode = READER;
    1376:	c7 43 70 01 00 00 00 	movl   $0x1,0x70(%rbx)
      thread_data[j].size = buffer_size;
    137d:	48 c7 43 78 00 00 04 00 	movq   $0x40000,0x78(%rbx)
      thread_data[j].sender = &thread_data[sender];
    1385:	48 89 5b 58          	mov    %rbx,0x58(%rbx)
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    1389:	4d 89 27             	mov    %r12,(%r15)
    138c:	e8 df fd ff ff       	call   1170 <__printf_chk@plt>
    1391:	48 8b 43 40          	mov    0x40(%rbx),%rax
    1395:	48 89 ee             	mov    %rbp,%rsi
      thread_data[j].thread_index = j;
    1398:	48 8d 93 a0 00 00 00 	lea    0xa0(%rbx),%rdx
      thread_data[j].running = 1;
    139f:	c7 83 d0 00 00 00 01 00 00 00 	movl   $0x1,0xd0(%rbx)
    13a9:	b9 01 00 00 00       	mov    $0x1,%ecx
    13ae:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].thread_index = j;
    13b3:	c7 83 a0 00 00 00 02 00 00 00 	movl   $0x2,0xa0(%rbx)
      thread_data[j].reader_index = receiver_index;
    13bd:	c7 83 ec 00 00 00 01 00 00 00 	movl   $0x1,0xec(%rbx)
      thread_data[j].cpu_set = receivercpu;
    13c7:	4c 89 b3 d8 00 00 00 	mov    %r14,0xd8(%rbx)
      thread_data[j].mode = READER;
    13ce:	c7 83 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rbx)
      thread_data[j].size = buffer_size;
    13d8:	48 c7 83 c8 00 00 00 00 00 04 00 	movq   $0x40000,0xc8(%rbx)
      thread_data[j].sender = &thread_data[sender];
    13e3:	48 89 9b a8 00 00 00 	mov    %rbx,0xa8(%rbx)
      thread_data[j].thread_index = j;
    13ea:	48 89 50 08          	mov    %rdx,0x8(%rax)
    13ee:	ba 02 00 00 00       	mov    $0x2,%edx
    13f3:	31 c0                	xor    %eax,%eax
    13f5:	e8 76 fd ff ff       	call   1170 <__printf_chk@plt>
    13fa:	31 d2                	xor    %edx,%edx
    13fc:	48 8d 35 ad 0c 00 00 	lea    0xcad(%rip),%rsi        # 20b0 <_IO_stdin_used+0xb0>
    1403:	31 c0                	xor    %eax,%eax
    1405:	bf 01 00 00 00       	mov    $0x1,%edi
    140a:	e8 61 fd ff ff       	call   1170 <__printf_chk@plt>
      printf("Creating receiver thread %d %d\n", j, receiver_index);
    }
    printf("Creating sender thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    140f:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 49;
    1412:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    1417:	c7 44 24 1c 31 00 00 00 	movl   $0x31,0x1c(%rsp)
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 3; 
    int receiver = sender + 1; 
    
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
    141f:	4d 8d 75 08          	lea    0x8(%r13),%r14
    1423:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    1429:	48 8d 68 38          	lea    0x38(%rax),%rbp
    142d:	48 8d 35 97 0c 00 00 	lea    0xc97(%rip),%rsi        # 20cb <_IO_stdin_used+0xcb>
    1434:	bf 01 00 00 00       	mov    $0x1,%edi
    1439:	31 c0                	xor    %eax,%eax
    143b:	44 89 fa             	mov    %r15d,%edx
    143e:	e8 2d fd ff ff       	call   1170 <__printf_chk@plt>
      printf("Creating receiver thread %d\n", j);
      
      int ret = pthread_attr_setschedpolicy(&attr[j], SCHED_RR);
    1443:	be 02 00 00 00       	mov    $0x2,%esi
    1448:	48 89 ef             	mov    %rbp,%rdi
    144b:	e8 00 fd ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    1450:	85 c0                	test   %eax,%eax
    1452:	0f 85 52 02 00 00    	jne    16aa <main+0x4ea>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    1458:	48 8d 74 24 1c       	lea    0x1c(%rsp),%rsi
    145d:	48 89 ef             	mov    %rbp,%rdi
    1460:	e8 2b fd ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1465:	85 c0                	test   %eax,%eax
    1467:	0f 85 58 02 00 00    	jne    16c5 <main+0x505>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    146d:	4c 89 e1             	mov    %r12,%rcx
    1470:	48 89 ee             	mov    %rbp,%rsi
    1473:	4c 89 f7             	mov    %r14,%rdi
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
    1476:	48 83 c5 38          	add    $0x38,%rbp
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    147a:	48 8d 15 4f 03 00 00 	lea    0x34f(%rip),%rdx        # 17d0 <disruptor_thread>
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
    1481:	49 83 c6 08          	add    $0x8,%r14
    1485:	49 83 c4 50          	add    $0x50,%r12
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1489:	e8 f2 fc ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    148e:	49 8b 7e f8          	mov    -0x8(%r14),%rdi
    1492:	be 08 00 00 00       	mov    $0x8,%esi
    1497:	48 8b 93 88 00 00 00 	mov    0x88(%rbx),%rdx
    149e:	e8 5d fc ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
    14a3:	41 83 ff 01          	cmp    $0x1,%r15d
    14a7:	75 0b                	jne    14b4 <main+0x2f4>
    14a9:	41 bf 02 00 00 00    	mov    $0x2,%r15d
    14af:	e9 79 ff ff ff       	jmp    142d <main+0x26d>
    }
      
      int ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_RR);
    14b4:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    14b9:	be 02 00 00 00       	mov    $0x2,%esi
    14be:	4c 89 ff             	mov    %r15,%rdi
    14c1:	e8 8a fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    14c6:	85 c0                	test   %eax,%eax
    14c8:	0f 85 dc 01 00 00    	jne    16aa <main+0x4ea>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 49;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    14ce:	48 8d 74 24 18       	lea    0x18(%rsp),%rsi
    14d3:	4c 89 ff             	mov    %r15,%rdi
      param2.sched_priority = 49;
    14d6:	c7 44 24 18 31 00 00 00 	movl   $0x31,0x18(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    14de:	e8 ad fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
    14e3:	41 89 c4             	mov    %eax,%r12d
      if (ret) {
    14e6:	85 c0                	test   %eax,%eax
    14e8:	0f 85 d7 01 00 00    	jne    16c5 <main+0x505>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    14ee:	48 89 d9             	mov    %rbx,%rcx
    14f1:	4c 89 ef             	mov    %r13,%rdi
    14f4:	48 8d 15 d5 02 00 00 	lea    0x2d5(%rip),%rdx        # 17d0 <disruptor_thread>
    14fb:	4c 89 fe             	mov    %r15,%rsi
    14fe:	e8 7d fc ff ff       	call   1180 <pthread_create@plt>
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    1503:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    1507:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    void * res2;
    int sender = x * 3; 
    int receiver = sender + 1; 
    pthread_join(thread[sender], res1);
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    150b:	31 ed                	xor    %ebp,%ebp
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    150d:	be 08 00 00 00       	mov    $0x8,%esi
    1512:	e8 e9 fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
  struct timespec preempt = {
    1517:	66 0f 6f 05 61 0c 00 00 	movdqa 0xc61(%rip),%xmm0        # 2180 <_IO_stdin_used+0x180>
    151f:	ba 0a 00 00 00       	mov    $0xa,%edx
    1524:	31 c0                	xor    %eax,%eax
    1526:	48 8d 35 f6 0b 00 00 	lea    0xbf6(%rip),%rsi        # 2123 <_IO_stdin_used+0x123>
    152d:	bf 01 00 00 00       	mov    $0x1,%edi
    1532:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    1537:	e8 34 fc ff ff       	call   1170 <__printf_chk@plt>
  nanosleep(&preempt , &rem2);
    153c:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    1541:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    1546:	e8 f5 fb ff ff       	call   1140 <nanosleep@plt>
    thread_data[sender].running = 0;
    154b:	c7 43 30 00 00 00 00 	movl   $0x0,0x30(%rbx)
    pthread_join(thread[sender], res1);
    1552:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    1556:	31 f6                	xor    %esi,%esi
      thread_data[j].running = 0;
    1558:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
    1562:	c7 83 d0 00 00 00 00 00 00 00 	movl   $0x0,0xd0(%rbx)
    pthread_join(thread[sender], res1);
    156c:	e8 3f fc ff ff       	call   11b0 <pthread_join@plt>
      pthread_join(thread[j], res2);
    1571:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    1575:	48 89 ee             	mov    %rbp,%rsi
    1578:	e8 33 fc ff ff       	call   11b0 <pthread_join@plt>
    157d:	49 8b 7d 10          	mov    0x10(%r13),%rdi
    1581:	48 89 ee             	mov    %rbp,%rsi
    1584:	4c 8d 2d c7 0b 00 00 	lea    0xbc7(%rip),%r13        # 2152 <_IO_stdin_used+0x152>
    158b:	e8 20 fc ff ff       	call   11b0 <pthread_join@plt>
    1590:	31 d2                	xor    %edx,%edx
    1592:	48 8d 35 a3 0b 00 00 	lea    0xba3(%rip),%rsi        # 213c <_IO_stdin_used+0x13c>
    1599:	31 c0                	xor    %eax,%eax
    159b:	bf 01 00 00 00       	mov    $0x1,%edi
    15a0:	e8 cb fb ff ff       	call   1170 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 3; 
    int receiver = sender + 1;
    int incompletes = 0;
    printf("Inspecting sender %d\n", sender);
    for (int y = 0 ; y < buffer_size; y++) {
    15a5:	eb 19                	jmp    15c0 <main+0x400>
    15a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      int compcount = 0;
      for (int n = 0 ; n < readers_count ; n++) {
	  if (thread_data[sender].data[y].complete[n] == 1) {
    15b0:	8b 40 04             	mov    0x4(%rax),%eax
    for (int y = 0 ; y < buffer_size; y++) {
    15b3:	48 83 c5 20          	add    $0x20,%rbp
    15b7:	48 81 fd 00 00 80 00 	cmp    $0x800000,%rbp
    15be:	74 42                	je     1602 <main+0x442>
	  if (thread_data[sender].data[y].complete[n] == 1) {
    15c0:	48 8b 53 10          	mov    0x10(%rbx),%rdx
    15c4:	48 01 ea             	add    %rbp,%rdx
    15c7:	48 8b 42 18          	mov    0x18(%rdx),%rax
    15cb:	8b 08                	mov    (%rax),%ecx
    15cd:	83 f9 01             	cmp    $0x1,%ecx
    15d0:	75 de                	jne    15b0 <main+0x3f0>
    15d2:	8b 48 04             	mov    0x4(%rax),%ecx
    15d5:	83 f9 01             	cmp    $0x1,%ecx
    15d8:	75 d9                	jne    15b3 <main+0x3f3>

      }
        if (compcount == readers_count) {
	  for (int n = 0 ; n < readers_count ; n++) {

	    if (thread_data[sender].data[y].complete[n] == 1) {
    15da:	8b 08                	mov    (%rax),%ecx
    15dc:	83 f9 01             	cmp    $0x1,%ecx
    15df:	74 5f                	je     1640 <main+0x480>
    15e1:	8b 40 04             	mov    0x4(%rax),%eax
	      struct timespec end = thread_data[sender].data[y].end[n];
	      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
	      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
	      printf("rb %d %d Read %ld %ld\n", sender, n, seconds, seconds2);
	    } else {
	      incompletes++;
    15e4:	41 83 c4 01          	add    $0x1,%r12d
	    if (thread_data[sender].data[y].complete[n] == 1) {
    15e8:	83 f8 01             	cmp    $0x1,%eax
    15eb:	0f 84 8b 00 00 00    	je     167c <main+0x4bc>
    for (int y = 0 ; y < buffer_size; y++) {
    15f1:	48 83 c5 20          	add    $0x20,%rbp
	      incompletes++;
    15f5:	41 83 c4 01          	add    $0x1,%r12d
    for (int y = 0 ; y < buffer_size; y++) {
    15f9:	48 81 fd 00 00 80 00 	cmp    $0x800000,%rbp
    1600:	75 be                	jne    15c0 <main+0x400>
    1602:	31 c0                	xor    %eax,%eax
    1604:	44 89 e2             	mov    %r12d,%edx
    1607:	bf 01 00 00 00       	mov    $0x1,%edi
    160c:	48 8d 35 56 0b 00 00 	lea    0xb56(%rip),%rsi        # 2169 <_IO_stdin_used+0x169>
    1613:	e8 58 fb ff ff       	call   1170 <__printf_chk@plt>

    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    1618:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    161d:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1626:	0f 85 94 00 00 00    	jne    16c0 <main+0x500>
    162c:	48 83 c4 58          	add    $0x58,%rsp
    1630:	31 c0                	xor    %eax,%eax
    1632:	5b                   	pop    %rbx
    1633:	5d                   	pop    %rbp
    1634:	41 5c                	pop    %r12
    1636:	41 5d                	pop    %r13
    1638:	41 5e                	pop    %r14
    163a:	41 5f                	pop    %r15
    163c:	c3                   	ret
    163d:	0f 1f 00             	nopl   (%rax)
	      struct timespec end = thread_data[sender].data[y].end[n];
    1640:	48 8b 42 10          	mov    0x10(%rdx),%rax
    1644:	31 c9                	xor    %ecx,%ecx
    1646:	4c 89 ee             	mov    %r13,%rsi
    1649:	bf 01 00 00 00       	mov    $0x1,%edi
	      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    164e:	4c 8b 48 08          	mov    0x8(%rax),%r9
	      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    1652:	4c 8b 00             	mov    (%rax),%r8
    1655:	31 c0                	xor    %eax,%eax
    1657:	4c 2b 4a 08          	sub    0x8(%rdx),%r9
    165b:	4c 2b 02             	sub    (%rdx),%r8
    165e:	31 d2                	xor    %edx,%edx
    1660:	e8 0b fb ff ff       	call   1170 <__printf_chk@plt>
	    if (thread_data[sender].data[y].complete[n] == 1) {
    1665:	48 8b 53 10          	mov    0x10(%rbx),%rdx
    1669:	48 01 ea             	add    %rbp,%rdx
    166c:	48 8b 42 18          	mov    0x18(%rdx),%rax
    1670:	8b 40 04             	mov    0x4(%rax),%eax
    1673:	83 f8 01             	cmp    $0x1,%eax
    1676:	0f 85 75 ff ff ff    	jne    15f1 <main+0x431>
	      struct timespec end = thread_data[sender].data[y].end[n];
    167c:	48 8b 42 10          	mov    0x10(%rdx),%rax
    1680:	b9 01 00 00 00       	mov    $0x1,%ecx
    1685:	4c 89 ee             	mov    %r13,%rsi
    1688:	bf 01 00 00 00       	mov    $0x1,%edi
	      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    168d:	4c 8b 48 18          	mov    0x18(%rax),%r9
	      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    1691:	4c 8b 40 10          	mov    0x10(%rax),%r8
    1695:	31 c0                	xor    %eax,%eax
    1697:	4c 2b 4a 08          	sub    0x8(%rdx),%r9
    169b:	4c 2b 02             	sub    (%rdx),%r8
    169e:	31 d2                	xor    %edx,%edx
    16a0:	e8 cb fa ff ff       	call   1170 <__printf_chk@plt>
    16a5:	e9 09 ff ff ff       	jmp    15b3 <main+0x3f3>
    16aa:	48 8d 3d 37 0a 00 00 	lea    0xa37(%rip),%rdi        # 20e8 <_IO_stdin_used+0xe8>
    16b1:	e8 5a fa ff ff       	call   1110 <puts@plt>
               exit(1);
    16b6:	bf 01 00 00 00       	mov    $0x1,%edi
    16bb:	e8 e0 fa ff ff       	call   11a0 <exit@plt>
}
    16c0:	e8 6b fa ff ff       	call   1130 <__stack_chk_fail@plt>
    16c5:	48 8d 3d 3a 0a 00 00 	lea    0xa3a(%rip),%rdi        # 2106 <_IO_stdin_used+0x106>
    16cc:	e8 3f fa ff ff       	call   1110 <puts@plt>
              exit(1);
    16d1:	bf 01 00 00 00       	mov    $0x1,%edi
    16d6:	e8 c5 fa ff ff       	call   11a0 <exit@plt>
    16db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000016e0 <_start>:
    16e0:	f3 0f 1e fa          	endbr64
    16e4:	31 ed                	xor    %ebp,%ebp
    16e6:	49 89 d1             	mov    %rdx,%r9
    16e9:	5e                   	pop    %rsi
    16ea:	48 89 e2             	mov    %rsp,%rdx
    16ed:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    16f1:	50                   	push   %rax
    16f2:	54                   	push   %rsp
    16f3:	45 31 c0             	xor    %r8d,%r8d
    16f6:	31 c9                	xor    %ecx,%ecx
    16f8:	48 8d 3d c1 fa ff ff 	lea    -0x53f(%rip),%rdi        # 11c0 <main>
    16ff:	ff 15 d3 28 00 00    	call   *0x28d3(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1705:	f4                   	hlt
    1706:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001710 <deregister_tm_clones>:
    1710:	48 8d 3d f9 28 00 00 	lea    0x28f9(%rip),%rdi        # 4010 <__TMC_END__>
    1717:	48 8d 05 f2 28 00 00 	lea    0x28f2(%rip),%rax        # 4010 <__TMC_END__>
    171e:	48 39 f8             	cmp    %rdi,%rax
    1721:	74 15                	je     1738 <deregister_tm_clones+0x28>
    1723:	48 8b 05 b6 28 00 00 	mov    0x28b6(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    172a:	48 85 c0             	test   %rax,%rax
    172d:	74 09                	je     1738 <deregister_tm_clones+0x28>
    172f:	ff e0                	jmp    *%rax
    1731:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1738:	c3                   	ret
    1739:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001740 <register_tm_clones>:
    1740:	48 8d 3d c9 28 00 00 	lea    0x28c9(%rip),%rdi        # 4010 <__TMC_END__>
    1747:	48 8d 35 c2 28 00 00 	lea    0x28c2(%rip),%rsi        # 4010 <__TMC_END__>
    174e:	48 29 fe             	sub    %rdi,%rsi
    1751:	48 89 f0             	mov    %rsi,%rax
    1754:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1758:	48 c1 f8 03          	sar    $0x3,%rax
    175c:	48 01 c6             	add    %rax,%rsi
    175f:	48 d1 fe             	sar    %rsi
    1762:	74 14                	je     1778 <register_tm_clones+0x38>
    1764:	48 8b 05 85 28 00 00 	mov    0x2885(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    176b:	48 85 c0             	test   %rax,%rax
    176e:	74 08                	je     1778 <register_tm_clones+0x38>
    1770:	ff e0                	jmp    *%rax
    1772:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1778:	c3                   	ret
    1779:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001780 <__do_global_dtors_aux>:
    1780:	f3 0f 1e fa          	endbr64
    1784:	80 3d 85 28 00 00 00 	cmpb   $0x0,0x2885(%rip)        # 4010 <__TMC_END__>
    178b:	75 2b                	jne    17b8 <__do_global_dtors_aux+0x38>
    178d:	55                   	push   %rbp
    178e:	48 83 3d 62 28 00 00 00 	cmpq   $0x0,0x2862(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1796:	48 89 e5             	mov    %rsp,%rbp
    1799:	74 0c                	je     17a7 <__do_global_dtors_aux+0x27>
    179b:	48 8b 3d 66 28 00 00 	mov    0x2866(%rip),%rdi        # 4008 <__dso_handle>
    17a2:	e8 49 f9 ff ff       	call   10f0 <__cxa_finalize@plt>
    17a7:	e8 64 ff ff ff       	call   1710 <deregister_tm_clones>
    17ac:	c6 05 5d 28 00 00 01 	movb   $0x1,0x285d(%rip)        # 4010 <__TMC_END__>
    17b3:	5d                   	pop    %rbp
    17b4:	c3                   	ret
    17b5:	0f 1f 00             	nopl   (%rax)
    17b8:	c3                   	ret
    17b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017c0 <frame_dummy>:
    17c0:	f3 0f 1e fa          	endbr64
    17c4:	e9 77 ff ff ff       	jmp    1740 <register_tm_clones>
    17c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017d0 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    17d0:	f3 0f 1e fa          	endbr64
    17d4:	55                   	push   %rbp
    17d5:	48 8d 35 2c 08 00 00 	lea    0x82c(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    17dc:	31 c0                	xor    %eax,%eax
    17de:	53                   	push   %rbx
    17df:	48 89 fb             	mov    %rdi,%rbx
    17e2:	48 83 ec 08          	sub    $0x8,%rsp
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    17e6:	8b 4f 20             	mov    0x20(%rdi),%ecx
    17e9:	8b 17                	mov    (%rdi),%edx
    17eb:	bf 01 00 00 00       	mov    $0x1,%edi
    17f0:	e8 7b f9 ff ff       	call   1170 <__printf_chk@plt>
  if (data->mode == WRITER) {
    17f5:	8b 43 20             	mov    0x20(%rbx),%eax
    17f8:	85 c0                	test   %eax,%eax
    17fa:	74 7d                	je     1879 <disruptor_thread+0xa9>
  else if (data->mode == READER) {
    17fc:	8b 43 20             	mov    0x20(%rbx),%eax
    17ff:	83 f8 01             	cmp    $0x1,%eax
    1802:	0f 84 b8 00 00 00    	je     18c0 <disruptor_thread+0xf0>
    1808:	48 8d 3d 41 08 00 00 	lea    0x841(%rip),%rdi        # 2050 <_IO_stdin_used+0x50>
    180f:	e8 fc f8 ff ff       	call   1110 <puts@plt>
}
    1814:	48 83 c4 08          	add    $0x8,%rsp
    1818:	31 c0                	xor    %eax,%eax
    181a:	5b                   	pop    %rbx
    181b:	5d                   	pop    %rbp
    181c:	c3                   	ret
    181d:	0f 1f 00             	nopl   (%rax)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[data->end].start);
    1820:	48 63 73 1c          	movslq 0x1c(%rbx),%rsi
    1824:	bf 04 00 00 00       	mov    $0x4,%edi
    1829:	48 c1 e6 05          	shl    $0x5,%rsi
    182d:	48 03 73 10          	add    0x10(%rbx),%rsi
    1831:	e8 ea f8 ff ff       	call   1120 <clock_gettime@plt>
        for (int n = 0 ; n < data->readers_count ; n++) { 
    1836:	8b 43 48             	mov    0x48(%rbx),%eax
    1839:	85 c0                	test   %eax,%eax
    183b:	7e 2b                	jle    1868 <disruptor_thread+0x98>
          data->data[data->end].complete[n] = 0;
    183d:	48 8b 4b 10          	mov    0x10(%rbx),%rcx
    1841:	31 d2                	xor    %edx,%edx
    1843:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    1848:	48 63 43 1c          	movslq 0x1c(%rbx),%rax
    184c:	48 c1 e0 05          	shl    $0x5,%rax
    1850:	48 8b 44 01 18       	mov    0x18(%rcx,%rax,1),%rax
    1855:	48 8d 04 90          	lea    (%rax,%rdx,4),%rax
        for (int n = 0 ; n < data->readers_count ; n++) { 
    1859:	48 83 c2 01          	add    $0x1,%rdx
          data->data[data->end].complete[n] = 0;
    185d:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
        for (int n = 0 ; n < data->readers_count ; n++) { 
    1863:	39 53 48             	cmp    %edx,0x48(%rbx)
    1866:	7f e0                	jg     1848 <disruptor_thread+0x78>
        data->end = (data->end + 1) % data->size;
    1868:	8b 43 1c             	mov    0x1c(%rbx),%eax
    186b:	83 c0 01             	add    $0x1,%eax
    186e:	48 98                	cltq
    1870:	48 99                	cqto
    1872:	48 f7 7b 28          	idivq  0x28(%rbx)
    1876:	89 53 1c             	mov    %edx,0x1c(%rbx)
    while (data->running == 1) {
    1879:	8b 43 30             	mov    0x30(%rbx),%eax
    187c:	83 f8 01             	cmp    $0x1,%eax
    187f:	75 87                	jne    1808 <disruptor_thread+0x38>
      asm volatile ("mfence" ::: "memory");
    1881:	0f ae f0             	mfence
      int next = (data->end + 1) % data->size;
    1884:	8b 43 1c             	mov    0x1c(%rbx),%eax
      for (int x  = 0 ; x < data->readers_count; x++) {
    1887:	48 63 4b 48          	movslq 0x48(%rbx),%rcx
      int next = (data->end + 1) % data->size;
    188b:	83 c0 01             	add    $0x1,%eax
    188e:	48 98                	cltq
    1890:	48 99                	cqto
    1892:	48 f7 7b 28          	idivq  0x28(%rbx)
      for (int x  = 0 ; x < data->readers_count; x++) {
    1896:	85 c9                	test   %ecx,%ecx
    1898:	7e 86                	jle    1820 <disruptor_thread+0x50>
    189a:	48 8b 43 40          	mov    0x40(%rbx),%rax
    189e:	48 8d 34 c8          	lea    (%rax,%rcx,8),%rsi
    18a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (next == data->readers[x]->start) {
    18a8:	48 8b 08             	mov    (%rax),%rcx
    18ab:	8b 49 18             	mov    0x18(%rcx),%ecx
    18ae:	39 d1                	cmp    %edx,%ecx
    18b0:	74 c7                	je     1879 <disruptor_thread+0xa9>
      for (int x  = 0 ; x < data->readers_count; x++) {
    18b2:	48 83 c0 08          	add    $0x8,%rax
    18b6:	48 39 c6             	cmp    %rax,%rsi
    18b9:	75 ed                	jne    18a8 <disruptor_thread+0xd8>
    18bb:	e9 60 ff ff ff       	jmp    1820 <disruptor_thread+0x50>
    struct Thread *sender = data->sender;
    18c0:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    while (data->running == 1) {
    18c4:	eb 17                	jmp    18dd <disruptor_thread+0x10d>
    18c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      asm volatile ("mfence" ::: "memory");
    18d0:	0f ae f0             	mfence
      if (sender->end == data->start) {
    18d3:	8b 55 1c             	mov    0x1c(%rbp),%edx
    18d6:	8b 43 18             	mov    0x18(%rbx),%eax
    18d9:	39 c2                	cmp    %eax,%edx
    18db:	75 0d                	jne    18ea <disruptor_thread+0x11a>
    while (data->running == 1) {
    18dd:	8b 43 30             	mov    0x30(%rbx),%eax
    18e0:	83 f8 01             	cmp    $0x1,%eax
    18e3:	74 eb                	je     18d0 <disruptor_thread+0x100>
    18e5:	e9 1e ff ff ff       	jmp    1808 <disruptor_thread+0x38>
        clock_gettime(CLOCK_MONOTONIC_RAW, &sender->data[data->start].end[data->reader_index]);
    18ea:	48 63 43 18          	movslq 0x18(%rbx),%rax
    18ee:	48 63 73 4c          	movslq 0x4c(%rbx),%rsi
    18f2:	bf 04 00 00 00       	mov    $0x4,%edi
    18f7:	48 c1 e0 05          	shl    $0x5,%rax
    18fb:	48 03 45 10          	add    0x10(%rbp),%rax
    18ff:	48 c1 e6 04          	shl    $0x4,%rsi
    1903:	48 03 70 10          	add    0x10(%rax),%rsi
    1907:	e8 14 f8 ff ff       	call   1120 <clock_gettime@plt>
        sender->data[data->start].complete[data->reader_index] = 1;
    190c:	48 63 43 18          	movslq 0x18(%rbx),%rax
    1910:	48 63 53 4c          	movslq 0x4c(%rbx),%rdx
    1914:	48 c1 e0 05          	shl    $0x5,%rax
    1918:	48 03 45 10          	add    0x10(%rbp),%rax
    191c:	48 8b 40 18          	mov    0x18(%rax),%rax
    1920:	48 8d 04 90          	lea    (%rax,%rdx,4),%rax
    1924:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
        data->start = (data->start + 1) % data->size;
    192a:	8b 43 18             	mov    0x18(%rbx),%eax
    192d:	83 c0 01             	add    $0x1,%eax
    1930:	48 98                	cltq
    1932:	48 99                	cqto
    1934:	48 f7 7b 28          	idivq  0x28(%rbx)
    1938:	89 53 18             	mov    %edx,0x18(%rbx)
    193b:	eb a0                	jmp    18dd <disruptor_thread+0x10d>

Disassembly of section .fini:

0000000000001940 <_fini>:
    1940:	f3 0f 1e fa          	endbr64
    1944:	48 83 ec 08          	sub    $0x8,%rsp
    1948:	48 83 c4 08          	add    $0x8,%rsp
    194c:	c3                   	ret
