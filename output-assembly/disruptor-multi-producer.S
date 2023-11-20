
disruptor-multi-producer:     file format elf64-x86-64


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
    11e4:	48 83 ec 58          	sub    $0x58,%rsp
    11e8:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    11f1:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
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
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    125e:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1261:	e8 fa fe ff ff       	call   1160 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1266:	be 08 00 00 00       	mov    $0x8,%esi
    126b:	bf 03 00 00 00       	mov    $0x3,%edi
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1270:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1274:	e8 e7 fe ff ff       	call   1160 <calloc@plt>
  // 0, 3, 6
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1; 
    int receiver2 = receiver + 1; 
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1279:	be 80 00 00 00       	mov    $0x80,%esi
    127e:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1283:	49 89 c4             	mov    %rax,%r12
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1286:	e8 d5 fe ff ff       	call   1160 <calloc@plt>
    CPU_ZERO(sendercpu);
    for (int j = 0 ; j < cores ; j++) {
      // printf("assigning sender %d to core %d\n", sender, j);
      CPU_SET(j, sendercpu);
    }
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    128b:	be 80 00 00 00       	mov    $0x80,%esi
    1290:	bf 01 00 00 00       	mov    $0x1,%edi
      CPU_SET(j, sendercpu);
    1295:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    129c:	48 89 c3             	mov    %rax,%rbx
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    129f:	e8 bc fe ff ff       	call   1160 <calloc@plt>
    for (int j = 0; j < cores ; j++) {
      // printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    }
     
    thread_data[sender].thread_index = sender;
    12a4:	41 c7 06 00 00 00 00 	movl   $0x0,(%r14)
      CPU_SET(j, receivercpu);
    12ab:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12b2:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    thread_data[sender].cpu_set = sendercpu;
    thread_data[sender].mode = READER;
    thread_data[sender].running = 1;
    thread_data[sender].size = buffer_size;
    thread_data[sender].end = 0;
    12b7:	31 c0                	xor    %eax,%eax
    thread_data[sender].mode = READER;
    12b9:	41 c7 86 04 01 00 00 01 00 00 00 	movl   $0x1,0x104(%r14)
    thread_data[sender].cpu_set = sendercpu;
    12c4:	49 89 9e 18 01 00 00 	mov    %rbx,0x118(%r14)
    thread_data[sender].running = 1;
    12cb:	41 c7 86 10 01 00 00 01 00 00 00 	movl   $0x1,0x110(%r14)
    thread_data[sender].size = buffer_size;
    12d6:	49 c7 86 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%r14)
    thread_data[sender].end = 0;
    12e1:	41 87 86 00 01 00 00 	xchg   %eax,0x100(%r14)
    thread_data[sender].sender = &thread_data[receiver];
    thread_data[sender].readers = calloc(other_count, sizeof(struct Thread*));
    12e8:	be 08 00 00 00       	mov    $0x8,%esi
    12ed:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[sender].sender = &thread_data[receiver];
    12f2:	4d 8d ae 00 02 00 00 	lea    0x200(%r14),%r13
    12f9:	4d 89 6e 08          	mov    %r13,0x8(%r14)
    thread_data[sender].readers = calloc(other_count, sizeof(struct Thread*));
    12fd:	4d 89 ef             	mov    %r13,%r15
    1300:	e8 5b fe ff ff       	call   1160 <calloc@plt>
    thread_data[sender].other_count = other_count;
    1305:	41 c7 86 88 01 00 00 02 00 00 00 	movl   $0x2,0x188(%r14)
    thread_data[sender].readers = calloc(other_count, sizeof(struct Thread*));
    1310:	49 89 86 80 01 00 00 	mov    %rax,0x180(%r14)
    thread_data[sender].other_count = other_count;
    1317:	b8 01 00 00 00       	mov    $0x1,%eax
    // printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
      thread_data[j].thread_index = j;
      thread_data[j].reader_index = receiver_index;
      thread_data[j].cpu_set = receivercpu;
    131c:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
      thread_data[j].reader_index = receiver_index;
    1321:	8d 50 ff             	lea    -0x1(%rax),%edx
      thread_data[j].thread_index = j;
    1324:	41 89 07             	mov    %eax,(%r15)
      thread_data[j].running = 1;
    1327:	41 c7 87 10 01 00 00 01 00 00 00 	movl   $0x1,0x110(%r15)
      thread_data[j].reader_index = receiver_index;
    1332:	41 89 97 8c 01 00 00 	mov    %edx,0x18c(%r15)
      thread_data[j].cpu_set = receivercpu;
    1339:	49 89 bf 18 01 00 00 	mov    %rdi,0x118(%r15)
      thread_data[j].mode = WRITER;
    1340:	41 c7 87 04 01 00 00 00 00 00 00 	movl   $0x0,0x104(%r15)
      if (j == receiver) {
    134b:	48 83 f8 01          	cmp    $0x1,%rax
    134f:	0f 84 a3 02 00 00    	je     15f8 <main+0x438>
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[receiver];
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    1355:	49 8b 86 80 01 00 00 	mov    0x180(%r14),%rax
      thread_data[j].sender = &thread_data[receiver];
    135c:	4d 89 6f 08          	mov    %r13,0x8(%r15)
    1360:	45 31 c0             	xor    %r8d,%r8d
    1363:	b9 01 00 00 00       	mov    $0x1,%ecx
      thread_data[j].reader = &thread_data[sender];
    1368:	4d 89 77 10          	mov    %r14,0x10(%r15)
    136c:	ba 02 00 00 00       	mov    $0x2,%edx
    1371:	bf 01 00 00 00       	mov    $0x1,%edi
    1376:	48 8d 35 db 0c 00 00 	lea    0xcdb(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
      thread_data[j].readers = thread_data[sender].readers;
    137d:	49 89 87 80 01 00 00 	mov    %rax,0x180(%r15)
      thread_data[j].size = buffer_size;
    1384:	49 c7 87 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%r15)
      thread_data[j].start = 0;
    138f:	41 c7 87 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r15)
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    139a:	4c 89 78 08          	mov    %r15,0x8(%rax)
    139e:	31 c0                	xor    %eax,%eax
    13a0:	e8 cb fd ff ff       	call   1170 <__printf_chk@plt>
    13a5:	31 d2                	xor    %edx,%edx
    13a7:	48 8d 35 35 0d 00 00 	lea    0xd35(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    13ae:	31 c0                	xor    %eax,%eax
    13b0:	bf 01 00 00 00       	mov    $0x1,%edi
    13b5:	e8 b6 fd ff ff       	call   1170 <__printf_chk@plt>
      printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
    }
    printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    13ba:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    13bd:	48 8b 04 24          	mov    (%rsp),%rax
    13c1:	c7 44 24 1c 00 00 00 00 	movl   $0x0,0x1c(%rsp)
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1; 
    
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    13c9:	49 8d 6c 24 08       	lea    0x8(%r12),%rbp
  param.sched_priority = 0;
    13ce:	41 bd 01 00 00 00    	mov    $0x1,%r13d
      if (ret) {
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    13d4:	4c 8d 3d e5 03 00 00 	lea    0x3e5(%rip),%r15        # 17c0 <disruptor_thread>
    13db:	48 8d 58 38          	lea    0x38(%rax),%rbx
    13df:	48 8d 35 fd 0c 00 00 	lea    0xcfd(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    13e6:	bf 01 00 00 00       	mov    $0x1,%edi
    13eb:	31 c0                	xor    %eax,%eax
    13ed:	44 89 ea             	mov    %r13d,%edx
    13f0:	e8 7b fd ff ff       	call   1170 <__printf_chk@plt>
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    13f5:	31 f6                	xor    %esi,%esi
    13f7:	48 89 df             	mov    %rbx,%rdi
    13fa:	e8 51 fd ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    13ff:	85 c0                	test   %eax,%eax
    1401:	0f 85 98 02 00 00    	jne    169f <main+0x4df>
      ret = pthread_attr_setschedparam(&attr[j], &param);
    1407:	48 8d 74 24 1c       	lea    0x1c(%rsp),%rsi
    140c:	48 89 df             	mov    %rbx,%rdi
    140f:	e8 7c fd ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1414:	85 c0                	test   %eax,%eax
    1416:	0f 85 9e 02 00 00    	jne    16ba <main+0x4fa>
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    141c:	4c 89 e9             	mov    %r13,%rcx
    141f:	48 89 de             	mov    %rbx,%rsi
    1422:	48 89 ef             	mov    %rbp,%rdi
    1425:	4c 89 fa             	mov    %r15,%rdx
    1428:	48 c1 e1 09          	shl    $0x9,%rcx
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    142c:	48 83 c3 38          	add    $0x38,%rbx
    1430:	48 83 c5 08          	add    $0x8,%rbp
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1434:	4c 01 f1             	add    %r14,%rcx
    1437:	e8 44 fd ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    143c:	48 8b 7d f8          	mov    -0x8(%rbp),%rdi
    1440:	be 08 00 00 00       	mov    $0x8,%esi
    1445:	49 8b 96 18 03 00 00 	mov    0x318(%r14),%rdx
    144c:	e8 af fc ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    1451:	49 83 fd 01          	cmp    $0x1,%r13
    1455:	75 08                	jne    145f <main+0x29f>
    1457:	41 bd 02 00 00 00    	mov    $0x2,%r13d
    145d:	eb 80                	jmp    13df <main+0x21f>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    145f:	48 8b 1c 24          	mov    (%rsp),%rbx
    1463:	31 f6                	xor    %esi,%esi
    1465:	48 89 df             	mov    %rbx,%rdi
    1468:	e8 e3 fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    146d:	85 c0                	test   %eax,%eax
    146f:	0f 85 2a 02 00 00    	jne    169f <main+0x4df>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1475:	48 8d 74 24 18       	lea    0x18(%rsp),%rsi
    147a:	48 89 df             	mov    %rbx,%rdi
      param2.sched_priority = 0;
    147d:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1485:	e8 06 fd ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    148a:	85 c0                	test   %eax,%eax
    148c:	0f 85 28 02 00 00    	jne    16ba <main+0x4fa>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    1492:	4c 89 f1             	mov    %r14,%rcx
    1495:	48 89 de             	mov    %rbx,%rsi
    1498:	4c 89 fa             	mov    %r15,%rdx
    149b:	4c 89 e7             	mov    %r12,%rdi
    149e:	e8 dd fc ff ff       	call   1180 <pthread_create@plt>
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    14a3:	49 8b 3c 24          	mov    (%r12),%rdi
    14a7:	be 08 00 00 00       	mov    $0x8,%esi
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + 1; 
    pthread_join(thread[sender], res1);
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    14ac:	31 db                	xor    %ebx,%ebx
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    14ae:	49 8b 96 18 01 00 00 	mov    0x118(%r14),%rdx
    14b5:	48 8d 2d ae 0c 00 00 	lea    0xcae(%rip),%rbp        # 216a <_IO_stdin_used+0x16a>
    14bc:	e8 3f fc ff ff       	call   1100 <pthread_setaffinity_np@plt>
  struct timespec preempt = {
    14c1:	66 0f 6f 05 c7 0c 00 00 	movdqa 0xcc7(%rip),%xmm0        # 2190 <_IO_stdin_used+0x190>
    14c9:	ba 0a 00 00 00       	mov    $0xa,%edx
    14ce:	31 c0                	xor    %eax,%eax
    14d0:	48 8d 35 64 0c 00 00 	lea    0xc64(%rip),%rsi        # 213b <_IO_stdin_used+0x13b>
    14d7:	bf 01 00 00 00       	mov    $0x1,%edi
    14dc:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    14e1:	e8 8a fc ff ff       	call   1170 <__printf_chk@plt>
  nanosleep(&preempt , &rem2);
    14e6:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    14eb:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    14f0:	e8 4b fc ff ff       	call   1140 <nanosleep@plt>
    pthread_join(thread[sender], res1);
    14f5:	49 8b 3c 24          	mov    (%r12),%rdi
    14f9:	31 f6                	xor    %esi,%esi
    thread_data[sender].running = 0;
    14fb:	41 c7 86 10 01 00 00 00 00 00 00 	movl   $0x0,0x110(%r14)
      thread_data[j].running = 0;
    1506:	41 c7 86 10 03 00 00 00 00 00 00 	movl   $0x0,0x310(%r14)
    1511:	41 c7 86 10 05 00 00 00 00 00 00 	movl   $0x0,0x510(%r14)
    pthread_join(thread[sender], res1);
    151c:	e8 8f fc ff ff       	call   11b0 <pthread_join@plt>
      pthread_join(thread[j], res2);
    1521:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    1526:	48 89 de             	mov    %rbx,%rsi
    1529:	e8 82 fc ff ff       	call   11b0 <pthread_join@plt>
    152e:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    1533:	48 89 de             	mov    %rbx,%rsi
    1536:	e8 75 fc ff ff       	call   11b0 <pthread_join@plt>
    153b:	ba 01 00 00 00       	mov    $0x1,%edx
    1540:	48 8d 35 0d 0c 00 00 	lea    0xc0d(%rip),%rsi        # 2154 <_IO_stdin_used+0x154>
    1547:	31 c0                	xor    %eax,%eax
    1549:	bf 01 00 00 00       	mov    $0x1,%edi
    154e:	e8 1d fc ff ff       	call   1170 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1;
    int incompletes = 0;
    printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    1553:	eb 13                	jmp    1568 <main+0x3a8>
    1555:	0f 1f 00             	nopl   (%rax)
    1558:	48 81 c3 80 01 00 00 	add    $0x180,%rbx
    155f:	48 81 fb 00 00 00 18 	cmp    $0x18000000,%rbx
    1566:	74 56                	je     15be <main+0x3fe>
      int compcount = 0;
      for (int n = 0 ; n < other_count ; n++) {

        if (thread_data[receiver].data[y].complete[n] == 1) {
    1568:	49 8b 96 18 02 00 00 	mov    0x218(%r14),%rdx
    156f:	48 01 da             	add    %rbx,%rdx
    1572:	48 8b 82 00 01 00 00 	mov    0x100(%rdx),%rax
    1579:	8b 08                	mov    (%rax),%ecx
    157b:	8b 40 04             	mov    0x4(%rax),%eax
    157e:	83 f9 01             	cmp    $0x1,%ecx
    1581:	75 d5                	jne    1558 <main+0x398>
    1583:	83 f8 01             	cmp    $0x1,%eax
    1586:	75 d0                	jne    1558 <main+0x398>
      if (compcount == other_count) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[receiver].data[y].start;
          struct timespec end = thread_data[receiver].data[y].end;
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    1588:	4c 8b 82 88 00 00 00 	mov    0x88(%rdx),%r8
    158f:	48 89 ee             	mov    %rbp,%rsi
    1592:	4c 2b 42 08          	sub    0x8(%rdx),%r8
    1596:	31 c0                	xor    %eax,%eax
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    1598:	48 8b 8a 80 00 00 00 	mov    0x80(%rdx),%rcx
    159f:	bf 01 00 00 00       	mov    $0x1,%edi
    15a4:	48 2b 0a             	sub    (%rdx),%rcx
    15a7:	31 d2                	xor    %edx,%edx
    15a9:	e8 c2 fb ff ff       	call   1170 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    15ae:	48 81 c3 80 01 00 00 	add    $0x180,%rbx
    15b5:	48 81 fb 00 00 00 18 	cmp    $0x18000000,%rbx
    15bc:	75 aa                	jne    1568 <main+0x3a8>
    15be:	31 d2                	xor    %edx,%edx
    15c0:	31 c0                	xor    %eax,%eax
    15c2:	48 8d 35 b5 0b 00 00 	lea    0xbb5(%rip),%rsi        # 217e <_IO_stdin_used+0x17e>
    15c9:	bf 01 00 00 00       	mov    $0x1,%edi
    15ce:	e8 9d fb ff ff       	call   1170 <__printf_chk@plt>
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    15d3:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    15d8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    15e1:	0f 85 ce 00 00 00    	jne    16b5 <main+0x4f5>
    15e7:	48 83 c4 58          	add    $0x58,%rsp
    15eb:	31 c0                	xor    %eax,%eax
    15ed:	5b                   	pop    %rbx
    15ee:	5d                   	pop    %rbp
    15ef:	41 5c                	pop    %r12
    15f1:	41 5d                	pop    %r13
    15f3:	41 5e                	pop    %r14
    15f5:	41 5f                	pop    %r15
    15f7:	c3                   	ret
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    15f8:	be 80 01 00 00       	mov    $0x180,%esi
    15fd:	bf 00 00 10 00       	mov    $0x100000,%edi
    1602:	e8 59 fb ff ff       	call   1160 <calloc@plt>
    1607:	49 89 47 18          	mov    %rax,0x18(%r15)
    160b:	48 89 c3             	mov    %rax,%rbx
        for (int n = 0 ; n < buffer_size ; n++) {
    160e:	48 8d a8 00 01 00 00 	lea    0x100(%rax),%rbp
    1615:	48 81 c3 00 01 00 18 	add    $0x18000100,%rbx
    161c:	0f 1f 40 00          	nopl   0x0(%rax)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1620:	be 04 00 00 00       	mov    $0x4,%esi
    1625:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    162a:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1631:	e8 2a fb ff ff       	call   1160 <calloc@plt>
    1636:	48 89 85 80 fe ff ff 	mov    %rax,-0x180(%rbp)
        for (int n = 0 ; n < buffer_size ; n++) {
    163d:	48 39 dd             	cmp    %rbx,%rbp
    1640:	75 de                	jne    1620 <main+0x460>
      thread_data[j].readers = thread_data[sender].readers;
    1642:	49 8b 86 80 01 00 00 	mov    0x180(%r14),%rax
      thread_data[j].sender = &thread_data[receiver];
    1649:	4d 89 6f 08          	mov    %r13,0x8(%r15)
    164d:	45 31 c0             	xor    %r8d,%r8d
    1650:	31 c9                	xor    %ecx,%ecx
      thread_data[j].reader = &thread_data[sender];
    1652:	4d 89 77 10          	mov    %r14,0x10(%r15)
    1656:	ba 01 00 00 00       	mov    $0x1,%edx
    165b:	bf 01 00 00 00       	mov    $0x1,%edi
    1660:	48 8d 35 f1 09 00 00 	lea    0x9f1(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
      thread_data[j].readers = thread_data[sender].readers;
    1667:	49 89 87 80 01 00 00 	mov    %rax,0x180(%r15)
      thread_data[j].size = buffer_size;
    166e:	49 c7 87 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%r15)
      thread_data[j].start = 0;
    1679:	41 c7 87 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r15)
      thread_data[sender].readers[receiver_index] = &thread_data[j];
    1684:	4c 89 38             	mov    %r15,(%rax)
    1687:	31 c0                	xor    %eax,%eax
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
    1689:	49 81 c7 00 02 00 00 	add    $0x200,%r15
    1690:	e8 db fa ff ff       	call   1170 <__printf_chk@plt>
    1695:	b8 02 00 00 00       	mov    $0x2,%eax
    169a:	e9 7d fc ff ff       	jmp    131c <main+0x15c>
    169f:	48 8d 3d 5a 0a 00 00 	lea    0xa5a(%rip),%rdi        # 2100 <_IO_stdin_used+0x100>
    16a6:	e8 65 fa ff ff       	call   1110 <puts@plt>
               exit(1);
    16ab:	bf 01 00 00 00       	mov    $0x1,%edi
    16b0:	e8 eb fa ff ff       	call   11a0 <exit@plt>
}
    16b5:	e8 76 fa ff ff       	call   1130 <__stack_chk_fail@plt>
    16ba:	48 8d 3d 5d 0a 00 00 	lea    0xa5d(%rip),%rdi        # 211e <_IO_stdin_used+0x11e>
    16c1:	e8 4a fa ff ff       	call   1110 <puts@plt>
              exit(1);
    16c6:	bf 01 00 00 00       	mov    $0x1,%edi
    16cb:	e8 d0 fa ff ff       	call   11a0 <exit@plt>

00000000000016d0 <_start>:
    16d0:	f3 0f 1e fa          	endbr64
    16d4:	31 ed                	xor    %ebp,%ebp
    16d6:	49 89 d1             	mov    %rdx,%r9
    16d9:	5e                   	pop    %rsi
    16da:	48 89 e2             	mov    %rsp,%rdx
    16dd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    16e1:	50                   	push   %rax
    16e2:	54                   	push   %rsp
    16e3:	45 31 c0             	xor    %r8d,%r8d
    16e6:	31 c9                	xor    %ecx,%ecx
    16e8:	48 8d 3d d1 fa ff ff 	lea    -0x52f(%rip),%rdi        # 11c0 <main>
    16ef:	ff 15 e3 28 00 00    	call   *0x28e3(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    16f5:	f4                   	hlt
    16f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001700 <deregister_tm_clones>:
    1700:	48 8d 3d 09 29 00 00 	lea    0x2909(%rip),%rdi        # 4010 <__TMC_END__>
    1707:	48 8d 05 02 29 00 00 	lea    0x2902(%rip),%rax        # 4010 <__TMC_END__>
    170e:	48 39 f8             	cmp    %rdi,%rax
    1711:	74 15                	je     1728 <deregister_tm_clones+0x28>
    1713:	48 8b 05 c6 28 00 00 	mov    0x28c6(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    171a:	48 85 c0             	test   %rax,%rax
    171d:	74 09                	je     1728 <deregister_tm_clones+0x28>
    171f:	ff e0                	jmp    *%rax
    1721:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1728:	c3                   	ret
    1729:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001730 <register_tm_clones>:
    1730:	48 8d 3d d9 28 00 00 	lea    0x28d9(%rip),%rdi        # 4010 <__TMC_END__>
    1737:	48 8d 35 d2 28 00 00 	lea    0x28d2(%rip),%rsi        # 4010 <__TMC_END__>
    173e:	48 29 fe             	sub    %rdi,%rsi
    1741:	48 89 f0             	mov    %rsi,%rax
    1744:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1748:	48 c1 f8 03          	sar    $0x3,%rax
    174c:	48 01 c6             	add    %rax,%rsi
    174f:	48 d1 fe             	sar    %rsi
    1752:	74 14                	je     1768 <register_tm_clones+0x38>
    1754:	48 8b 05 95 28 00 00 	mov    0x2895(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    175b:	48 85 c0             	test   %rax,%rax
    175e:	74 08                	je     1768 <register_tm_clones+0x38>
    1760:	ff e0                	jmp    *%rax
    1762:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1768:	c3                   	ret
    1769:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001770 <__do_global_dtors_aux>:
    1770:	f3 0f 1e fa          	endbr64
    1774:	80 3d 95 28 00 00 00 	cmpb   $0x0,0x2895(%rip)        # 4010 <__TMC_END__>
    177b:	75 2b                	jne    17a8 <__do_global_dtors_aux+0x38>
    177d:	55                   	push   %rbp
    177e:	48 83 3d 72 28 00 00 00 	cmpq   $0x0,0x2872(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1786:	48 89 e5             	mov    %rsp,%rbp
    1789:	74 0c                	je     1797 <__do_global_dtors_aux+0x27>
    178b:	48 8b 3d 76 28 00 00 	mov    0x2876(%rip),%rdi        # 4008 <__dso_handle>
    1792:	e8 59 f9 ff ff       	call   10f0 <__cxa_finalize@plt>
    1797:	e8 64 ff ff ff       	call   1700 <deregister_tm_clones>
    179c:	c6 05 6d 28 00 00 01 	movb   $0x1,0x286d(%rip)        # 4010 <__TMC_END__>
    17a3:	5d                   	pop    %rbp
    17a4:	c3                   	ret
    17a5:	0f 1f 00             	nopl   (%rax)
    17a8:	c3                   	ret
    17a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017b0 <frame_dummy>:
    17b0:	f3 0f 1e fa          	endbr64
    17b4:	e9 77 ff ff ff       	jmp    1730 <register_tm_clones>
    17b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017c0 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    17c0:	f3 0f 1e fa          	endbr64
    17c4:	41 57                	push   %r15
    17c6:	48 8d 35 3b 08 00 00 	lea    0x83b(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    17cd:	31 c0                	xor    %eax,%eax
    17cf:	41 56                	push   %r14
    17d1:	41 55                	push   %r13
    17d3:	41 54                	push   %r12
    17d5:	55                   	push   %rbp
    17d6:	53                   	push   %rbx
    17d7:	48 89 fb             	mov    %rdi,%rbx
    17da:	48 83 ec 08          	sub    $0x8,%rsp
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    17de:	8b 8f 04 01 00 00    	mov    0x104(%rdi),%ecx
    17e4:	8b 17                	mov    (%rdi),%edx
    17e6:	bf 01 00 00 00       	mov    $0x1,%edi
    17eb:	e8 80 f9 ff ff       	call   1170 <__printf_chk@plt>
  int next = (data->end + 1) % data->size;
    17f0:	8b 83 00 01 00 00    	mov    0x100(%rbx),%eax
  if (data->mode == WRITER) {
    17f6:	8b 83 04 01 00 00    	mov    0x104(%rbx),%eax
    17fc:	85 c0                	test   %eax,%eax
    17fe:	74 40                	je     1840 <disruptor_thread+0x80>
  } else if (data->mode == READER) {
    1800:	8b 83 04 01 00 00    	mov    0x104(%rbx),%eax
    1806:	83 f8 01             	cmp    $0x1,%eax
    1809:	0f 84 f1 00 00 00    	je     1900 <disruptor_thread+0x140>
  printf("Finished %d\n", data->mode);
    180f:	8b 93 04 01 00 00    	mov    0x104(%rbx),%edx
    1815:	48 8d 35 81 08 00 00 	lea    0x881(%rip),%rsi        # 209d <_IO_stdin_used+0x9d>
    181c:	bf 01 00 00 00       	mov    $0x1,%edi
    1821:	31 c0                	xor    %eax,%eax
    1823:	e8 48 f9 ff ff       	call   1170 <__printf_chk@plt>
}
    1828:	48 83 c4 08          	add    $0x8,%rsp
    182c:	31 c0                	xor    %eax,%eax
    182e:	5b                   	pop    %rbx
    182f:	5d                   	pop    %rbp
    1830:	41 5c                	pop    %r12
    1832:	41 5d                	pop    %r13
    1834:	41 5e                	pop    %r14
    1836:	41 5f                	pop    %r15
    1838:	c3                   	ret
    1839:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1840:	48 8d 3d 3e 08 00 00 	lea    0x83e(%rip),%rdi        # 2085 <_IO_stdin_used+0x85>
    1847:	e8 c4 f8 ff ff       	call   1110 <puts@plt>
    struct Thread *me = data->sender;
    184c:	4c 8b 63 08          	mov    0x8(%rbx),%r12
    next = (me->end + 1) % data->size;
    1850:	4d 8d ac 24 00 01 00 00 	lea    0x100(%r12),%r13
    1858:	41 8b 84 24 00 01 00 00 	mov    0x100(%r12),%eax
    1860:	83 c0 01             	add    $0x1,%eax
    1863:	48 98                	cltq
    1865:	48 99                	cqto
    1867:	48 f7 bb 08 01 00 00 	idivq  0x108(%rbx)
    while (data->running == 1) {
    186e:	66 90                	xchg   %ax,%ax
    1870:	8b 83 10 01 00 00    	mov    0x110(%rbx),%eax
    1876:	83 f8 01             	cmp    $0x1,%eax
    1879:	75 94                	jne    180f <disruptor_thread+0x4f>
      asm volatile ("sfence" ::: "memory");
    187b:	0f ae f8             	sfence
        if (next == data->reader->start) {
    187e:	48 8b 43 10          	mov    0x10(%rbx),%rax
    1882:	8b 80 80 00 00 00    	mov    0x80(%rax),%eax
    1888:	39 d0                	cmp    %edx,%eax
    188a:	74 e4                	je     1870 <disruptor_thread+0xb0>
            int claim = me->end;
    188c:	41 8b 45 00          	mov    0x0(%r13),%eax
            int changed = me->end;
    1890:	41 8b 6d 00          	mov    0x0(%r13),%ebp
            int change = (changed + 1) % me->size;
    1894:	8d 45 01             	lea    0x1(%rbp),%eax
    1897:	48 98                	cltq
    1899:	48 99                	cqto
    189b:	49 f7 bc 24 08 01 00 00 	idivq  0x108(%r12)
            while (!__atomic_compare_exchange (&me->end, &changed, &change, 0, __ATOMIC_RELEASE, __ATOMIC_RELAXED)) {
    18a3:	89 e8                	mov    %ebp,%eax
    18a5:	f0 41 0f b1 55 00    	lock cmpxchg %edx,0x0(%r13)
    18ab:	89 c5                	mov    %eax,%ebp
    18ad:	0f 85 e3 00 00 00    	jne    1996 <disruptor_thread+0x1d6>
            clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    18b3:	48 63 c5             	movslq %ebp,%rax
    18b6:	49 8b 74 24 18       	mov    0x18(%r12),%rsi
    18bb:	bf 04 00 00 00       	mov    $0x4,%edi
    18c0:	4c 8d 34 40          	lea    (%rax,%rax,2),%r14
    18c4:	49 c1 e6 07          	shl    $0x7,%r14
    18c8:	4c 01 f6             	add    %r14,%rsi
    18cb:	e8 50 f8 ff ff       	call   1120 <clock_gettime@plt>
            next = (changed + 1) % me->size;
    18d0:	8d 45 01             	lea    0x1(%rbp),%eax
    18d3:	48 98                	cltq
    18d5:	48 99                	cqto
    18d7:	49 f7 bc 24 08 01 00 00 	idivq  0x108(%r12)
            me->data[changed].complete[1] = 1;
    18df:	49 8b 44 24 18       	mov    0x18(%r12),%rax
    18e4:	4a 8b 84 30 00 01 00 00 	mov    0x100(%rax,%r14,1),%rax
    18ec:	c7 40 04 01 00 00 00 	movl   $0x1,0x4(%rax)
    18f3:	e9 78 ff ff ff       	jmp    1870 <disruptor_thread+0xb0>
    18f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    1900:	48 8d 3d 8a 07 00 00 	lea    0x78a(%rip),%rdi        # 2091 <_IO_stdin_used+0x91>
    1907:	e8 04 f8 ff ff       	call   1110 <puts@plt>
    struct Thread *sender = data->sender;
    190c:	48 8b 43 08          	mov    0x8(%rbx),%rax
    struct Snapshot * rdata = sender->data;
    1910:	4c 8b 70 18          	mov    0x18(%rax),%r14
    int cachedEnd = sender->end;
    1914:	4c 8d a8 00 01 00 00 	lea    0x100(%rax),%r13
    191b:	8b 88 00 01 00 00    	mov    0x100(%rax),%ecx
    int cachedStart = data->start;
    1921:	44 8b bb 80 00 00 00 	mov    0x80(%rbx),%r15d
    while (data->running == 1) {
    1928:	8b 83 10 01 00 00    	mov    0x110(%rbx),%eax
    int size = data->size;
    192e:	44 8b a3 08 01 00 00 	mov    0x108(%rbx),%r12d
    while (data->running == 1) {
    1935:	83 f8 01             	cmp    $0x1,%eax
    1938:	0f 85 d1 fe ff ff    	jne    180f <disruptor_thread+0x4f>
    193e:	66 90                	xchg   %ax,%ax
      if (cachedEnd == cachedStart) {
    1940:	44 39 f9             	cmp    %r15d,%ecx
    1943:	74 3d                	je     1982 <disruptor_thread+0x1c2>
          clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[cachedStart].end);
    1945:	49 63 c7             	movslq %r15d,%rax
    1948:	bf 04 00 00 00       	mov    $0x4,%edi
    194d:	48 8d 2c 40          	lea    (%rax,%rax,2),%rbp
    1951:	48 c1 e5 07          	shl    $0x7,%rbp
    1955:	4c 01 f5             	add    %r14,%rbp
    1958:	48 8d b5 80 00 00 00 	lea    0x80(%rbp),%rsi
    195f:	e8 bc f7 ff ff       	call   1120 <clock_gettime@plt>
          rdata[cachedStart].complete[0] = 1;
    1964:	48 8b 85 00 01 00 00 	mov    0x100(%rbp),%rax
    196b:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
          cachedStart = (cachedStart + 1) % size;
    1971:	41 8d 47 01          	lea    0x1(%r15),%eax
    1975:	99                   	cltd
    1976:	41 f7 fc             	idiv   %r12d
          data->start = cachedStart;
    1979:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
          cachedStart = (cachedStart + 1) % size;
    197f:	41 89 d7             	mov    %edx,%r15d
          cachedEnd = sender->end;
    1982:	41 8b 4d 00          	mov    0x0(%r13),%ecx
    while (data->running == 1) {
    1986:	8b 83 10 01 00 00    	mov    0x110(%rbx),%eax
    198c:	83 f8 01             	cmp    $0x1,%eax
    198f:	74 af                	je     1940 <disruptor_thread+0x180>
    1991:	e9 79 fe ff ff       	jmp    180f <disruptor_thread+0x4f>
              changed = me->end;
    1996:	41 8b 4d 00          	mov    0x0(%r13),%ecx
              change = (changed + 1) % me->size;
    199a:	8d 41 01             	lea    0x1(%rcx),%eax
    199d:	48 98                	cltq
    199f:	48 99                	cqto
    19a1:	49 f7 bc 24 08 01 00 00 	idivq  0x108(%r12)
            while (!__atomic_compare_exchange (&me->end, &changed, &change, 0, __ATOMIC_RELEASE, __ATOMIC_RELAXED)) {
    19a9:	89 c8                	mov    %ecx,%eax
    19ab:	f0 41 0f b1 55 00    	lock cmpxchg %edx,0x0(%r13)
    19b1:	75 e3                	jne    1996 <disruptor_thread+0x1d6>
    19b3:	89 c5                	mov    %eax,%ebp
    19b5:	e9 f9 fe ff ff       	jmp    18b3 <disruptor_thread+0xf3>
    19ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000019c0 <min>:
int min(long a, long b) {
    19c0:	f3 0f 1e fa          	endbr64
  if (a < b) return a;
    19c4:	48 39 f7             	cmp    %rsi,%rdi
    19c7:	7c 02                	jl     19cb <min+0xb>
  if (b < a) return b;
    19c9:	7f 05                	jg     19d0 <min+0x10>
  if (a < b) return a;
    19cb:	89 f8                	mov    %edi,%eax
    19cd:	c3                   	ret
    19ce:	66 90                	xchg   %ax,%ax
  if (b < a) return b;
    19d0:	89 f0                	mov    %esi,%eax
}
    19d2:	c3                   	ret

Disassembly of section .fini:

00000000000019d4 <_fini>:
    19d4:	f3 0f 1e fa          	endbr64
    19d8:	48 83 ec 08          	sub    $0x8,%rsp
    19dc:	48 83 c4 08          	add    $0x8,%rsp
    19e0:	c3                   	ret
