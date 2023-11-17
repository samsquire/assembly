
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
    CPU_ZERO(receivercpu);
    for (int j = 0; j < cores ; j++) {
      // printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    }
    for (int n = sender; n < sender + writers_count; n++) {
    11cb:	45 31 ff             	xor    %r15d,%r15d
    11ce:	ba 14 00 00 00       	mov    $0x14,%edx
int main() {
    11d3:	41 56                	push   %r14
    11d5:	48 8d 35 54 0e 00 00 	lea    0xe54(%rip),%rsi        # 2030 <_IO_stdin_used+0x30>
    11dc:	bf 01 00 00 00       	mov    $0x1,%edi
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
    1248:	be 00 02 00 00       	mov    $0x200,%esi
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
      CPU_SET(j, receivercpu);
    1273:	49 89 de             	mov    %rbx,%r14
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
    12ad:	45 89 3e             	mov    %r15d,(%r14)
      thread_data[n].mode = WRITER;
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    12b0:	be 08 00 00 00       	mov    $0x8,%esi
    12b5:	bf 02 00 00 00       	mov    $0x2,%edi
        CPU_SET(j, sendercpu);
    12ba:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
      thread_data[n].mode = WRITER;
    12c1:	41 c7 86 04 01 00 00 00 00 00 00 	movl   $0x0,0x104(%r14)
      thread_data[n].cpu_set = sendercpu;
    12cc:	49 89 86 18 01 00 00 	mov    %rax,0x118(%r14)
      thread_data[n].running = 1;
    12d3:	41 c7 86 10 01 00 00 01 00 00 00 	movl   $0x1,0x110(%r14)
      thread_data[n].size = buffer_size;
    12de:	49 c7 86 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%r14)
      thread_data[n].end = 0;
    12e9:	41 c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r14)
      thread_data[n].sender = &thread_data[sender];
    12f4:	49 89 5e 08          	mov    %rbx,0x8(%r14)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    12f8:	e8 63 fe ff ff       	call   1160 <calloc@plt>
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    12fd:	be 80 01 00 00       	mov    $0x180,%esi
    1302:	bf 00 00 10 00       	mov    $0x100000,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1307:	49 89 86 80 01 00 00 	mov    %rax,0x180(%r14)
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    130e:	e8 4d fe ff ff       	call   1160 <calloc@plt>
    1313:	49 89 46 18          	mov    %rax,0x18(%r14)
      for (int k = 0 ; k < buffer_size ; k++) {
    1317:	4c 8d a8 00 01 00 00 	lea    0x100(%rax),%r13
    131e:	4c 8d a0 00 01 00 18 	lea    0x18000100(%rax),%r12
    1325:	0f 1f 00             	nopl   (%rax)
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1328:	be 04 00 00 00       	mov    $0x4,%esi
    132d:	bf 02 00 00 00       	mov    $0x2,%edi
      for (int k = 0 ; k < buffer_size ; k++) {
    1332:	49 81 c5 80 01 00 00 	add    $0x180,%r13
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1339:	e8 22 fe ff ff       	call   1160 <calloc@plt>
    133e:	49 89 85 80 fe ff ff 	mov    %rax,-0x180(%r13)
      for (int k = 0 ; k < buffer_size ; k++) {
    1345:	4d 39 e5             	cmp    %r12,%r13
    1348:	75 de                	jne    1328 <main+0x168>
      }
      thread_data[n].other_count = other_count;
    134a:	41 c7 86 88 01 00 00 02 00 00 00 	movl   $0x2,0x188(%r14)
    for (int n = sender; n < sender + writers_count; n++) {
    1355:	49 81 c6 00 02 00 00 	add    $0x200,%r14
    135c:	45 85 ff             	test   %r15d,%r15d
    135f:	75 0b                	jne    136c <main+0x1ac>
    1361:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    1367:	e9 32 ff ff ff       	jmp    129e <main+0xde>
    136c:	66 48 0f 6e d3       	movq   %rbx,%xmm2
    1371:	4c 8d b3 00 04 00 00 	lea    0x400(%rbx),%r14
    1378:	31 c0                	xor    %eax,%eax
    137a:	66 0f 6c d2          	punpcklqdq %xmm2,%xmm2
    137e:	4c 8d 2d d3 0c 00 00 	lea    0xcd3(%rip),%r13        # 2058 <_IO_stdin_used+0x58>
    1385:	0f 29 14 24          	movaps %xmm2,(%rsp)
    1389:	8d 50 02             	lea    0x2(%rax),%edx
    }
    // printf("Created data for %d\n", sender);
    int seq[] = {1, 2, 5};
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      thread_data[j].thread_index = j;
      thread_data[j].reader_index = receiver_index;
    138c:	41 89 86 8c 01 00 00 	mov    %eax,0x18c(%r14)
      thread_data[j].multiple = receiver_index % other_count;
    1393:	41 89 86 90 01 00 00 	mov    %eax,0x190(%r14)
      thread_data[j].other_count = other_count;
     
      thread_data[j].cpu_set = receivercpu;
    139a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
      thread_data[j].running = 1;
    139f:	41 c7 86 10 01 00 00 01 00 00 00 	movl   $0x1,0x110(%r14)
      thread_data[j].thread_index = j;
    13aa:	41 89 16             	mov    %edx,(%r14)
      thread_data[j].other_count = other_count;
    13ad:	41 c7 86 88 01 00 00 02 00 00 00 	movl   $0x2,0x188(%r14)
      thread_data[j].cpu_set = receivercpu;
    13b8:	49 89 86 18 01 00 00 	mov    %rax,0x118(%r14)
      thread_data[j].mode = READER;
    13bf:	41 c7 86 04 01 00 00 01 00 00 00 	movl   $0x1,0x104(%r14)
      if (j == receiver) {
    13ca:	83 fa 02             	cmp    $0x2,%edx
    13cd:	0f 84 06 03 00 00    	je     16d9 <main+0x519>
        for (int n = 0 ; n < buffer_size ; n++) {
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
        }
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
    13d3:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
    13d8:	45 31 c0             	xor    %r8d,%r8d
    13db:	b9 01 00 00 00       	mov    $0x1,%ecx
    13e0:	4c 89 ee             	mov    %r13,%rsi
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    13e3:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    13ea:	ba 03 00 00 00       	mov    $0x3,%edx
    13ef:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].size = buffer_size;
    13f4:	49 c7 86 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%r14)
      thread_data[j].start = 0;
    13ff:	41 c7 86 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r14)
      thread_data[j].readers = thread_data[sender].readers;
    140a:	49 89 86 80 01 00 00 	mov    %rax,0x180(%r14)
    1411:	31 c0                	xor    %eax,%eax
      thread_data[j].sender = &thread_data[sender];
    1413:	41 0f 11 4e 08       	movups %xmm1,0x8(%r14)
    1418:	e8 53 fd ff ff       	call   1170 <__printf_chk@plt>
      printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        thread_data[n].readers[receiver_index] = &thread_data[j];
    141d:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    1424:	31 d2                	xor    %edx,%edx
    1426:	48 8d 35 b6 0c 00 00 	lea    0xcb6(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    142d:	bf 01 00 00 00       	mov    $0x1,%edi
    1432:	4c 89 70 08          	mov    %r14,0x8(%rax)
    1436:	48 8b 83 80 03 00 00 	mov    0x380(%rbx),%rax
    143d:	4c 89 70 08          	mov    %r14,0x8(%rax)
    1441:	31 c0                	xor    %eax,%eax
    1443:	e8 28 fd ff ff       	call   1170 <__printf_chk@plt>
      }
    }
    printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    1448:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    144b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    1450:	c7 44 24 2c 00 00 00 00 	movl   $0x0,0x2c(%rsp)
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1458:	4c 8d 75 10          	lea    0x10(%rbp),%r14
  param.sched_priority = 0;
    145c:	41 bf 02 00 00 00    	mov    $0x2,%r15d
    1462:	4c 8d 60 70          	lea    0x70(%rax),%r12
    1466:	48 8d 35 76 0c 00 00 	lea    0xc76(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    146d:	bf 01 00 00 00       	mov    $0x1,%edi
    1472:	31 c0                	xor    %eax,%eax
    1474:	44 89 fa             	mov    %r15d,%edx
    1477:	e8 f4 fc ff ff       	call   1170 <__printf_chk@plt>
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    147c:	31 f6                	xor    %esi,%esi
    147e:	4c 89 e7             	mov    %r12,%rdi
    1481:	e8 ca fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    1486:	85 c0                	test   %eax,%eax
    1488:	0f 85 00 03 00 00    	jne    178e <main+0x5ce>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    148e:	48 8d 74 24 2c       	lea    0x2c(%rsp),%rsi
    1493:	4c 89 e7             	mov    %r12,%rdi
    1496:	e8 f5 fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    149b:	85 c0                	test   %eax,%eax
    149d:	0f 85 06 03 00 00    	jne    17a9 <main+0x5e9>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    14a3:	4c 89 f9             	mov    %r15,%rcx
    14a6:	4c 89 e6             	mov    %r12,%rsi
    14a9:	4c 89 f7             	mov    %r14,%rdi
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    14ac:	49 83 c4 38          	add    $0x38,%r12
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    14b0:	48 c1 e1 09          	shl    $0x9,%rcx
    14b4:	48 8d 15 f5 03 00 00 	lea    0x3f5(%rip),%rdx        # 18b0 <disruptor_thread>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    14bb:	49 83 c6 08          	add    $0x8,%r14
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    14bf:	48 01 d9             	add    %rbx,%rcx
    14c2:	e8 b9 fc ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    14c7:	49 8b 7e f8          	mov    -0x8(%r14),%rdi
    14cb:	be 08 00 00 00       	mov    $0x8,%esi
    14d0:	48 8b 93 18 05 00 00 	mov    0x518(%rbx),%rdx
    14d7:	e8 24 fc ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    14dc:	49 83 ff 02          	cmp    $0x2,%r15
    14e0:	75 0b                	jne    14ed <main+0x32d>
    14e2:	41 bf 03 00 00 00    	mov    $0x3,%r15d
    14e8:	e9 79 ff ff ff       	jmp    1466 <main+0x2a6>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    14ed:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    14f2:	31 f6                	xor    %esi,%esi
    14f4:	4c 89 ff             	mov    %r15,%rdi
    14f7:	e8 54 fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    14fc:	85 c0                	test   %eax,%eax
    14fe:	0f 85 8a 02 00 00    	jne    178e <main+0x5ce>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1504:	48 8d 74 24 28       	lea    0x28(%rsp),%rsi
    1509:	4c 89 ff             	mov    %r15,%rdi
      param2.sched_priority = 0;
    150c:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1514:	e8 77 fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1519:	85 c0                	test   %eax,%eax
    151b:	0f 85 88 02 00 00    	jne    17a9 <main+0x5e9>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    1521:	48 89 d9             	mov    %rbx,%rcx
    1524:	48 89 ef             	mov    %rbp,%rdi
    1527:	48 8d 15 82 03 00 00 	lea    0x382(%rip),%rdx        # 18b0 <disruptor_thread>
    152e:	4c 89 fe             	mov    %r15,%rsi
    1531:	e8 4a fc ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    1536:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    153a:	be 08 00 00 00       	mov    $0x8,%esi
    void * res1;
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    153f:	45 31 e4             	xor    %r12d,%r12d
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    1542:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
    1549:	e8 b2 fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    154e:	4c 89 fe             	mov    %r15,%rsi
    1551:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
    1555:	48 8d 8b 00 02 00 00 	lea    0x200(%rbx),%rcx
    155c:	48 83 c6 38          	add    $0x38,%rsi
    1560:	48 8d 15 49 03 00 00 	lea    0x349(%rip),%rdx        # 18b0 <disruptor_thread>
    1567:	e8 14 fc ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    156c:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
    1570:	be 08 00 00 00       	mov    $0x8,%esi
    1575:	48 8b 93 18 03 00 00 	mov    0x318(%rbx),%rdx
    157c:	e8 7f fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
  struct timespec preempt = {
    1581:	66 0f 6f 05 07 0c 00 00 	movdqa 0xc07(%rip),%xmm0        # 2190 <_IO_stdin_used+0x190>
    1589:	ba 0a 00 00 00       	mov    $0xa,%edx
    158e:	31 c0                	xor    %eax,%eax
    1590:	48 8d 35 a4 0b 00 00 	lea    0xba4(%rip),%rsi        # 213b <_IO_stdin_used+0x13b>
    1597:	bf 01 00 00 00       	mov    $0x1,%edi
    159c:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    15a1:	e8 ca fb ff ff       	call   1170 <__printf_chk@plt>
  nanosleep(&preempt , &rem2);
    15a6:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    15ab:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    15b0:	e8 8b fb ff ff       	call   1140 <nanosleep@plt>
      pthread_join(thread[n], res1);
    15b5:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    15b9:	4c 89 e6             	mov    %r12,%rsi
    thread_data[sender].running = 0;
    15bc:	c7 83 10 01 00 00 00 00 00 00 	movl   $0x0,0x110(%rbx)
      thread_data[j].running = 0;
    15c6:	c7 83 10 05 00 00 00 00 00 00 	movl   $0x0,0x510(%rbx)
    15d0:	c7 83 10 07 00 00 00 00 00 00 	movl   $0x0,0x710(%rbx)
      thread_data[n].running = 0;
    15da:	c7 83 10 01 00 00 00 00 00 00 	movl   $0x0,0x110(%rbx)
    15e4:	c7 83 10 03 00 00 00 00 00 00 	movl   $0x0,0x310(%rbx)
      pthread_join(thread[n], res1);
    15ee:	e8 bd fb ff ff       	call   11b0 <pthread_join@plt>
    15f3:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
    15f7:	4c 89 e6             	mov    %r12,%rsi
    15fa:	e8 b1 fb ff ff       	call   11b0 <pthread_join@plt>
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    15ff:	48 8b 7d 10          	mov    0x10(%rbp),%rdi
    1603:	4c 89 e6             	mov    %r12,%rsi
    1606:	e8 a5 fb ff ff       	call   11b0 <pthread_join@plt>
    160b:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
    160f:	4c 89 e6             	mov    %r12,%rsi
    1612:	31 ed                	xor    %ebp,%ebp
    1614:	4c 8d 25 4f 0b 00 00 	lea    0xb4f(%rip),%r12        # 216a <_IO_stdin_used+0x16a>
    161b:	e8 90 fb ff ff       	call   11b0 <pthread_join@plt>
    1620:	ba 02 00 00 00       	mov    $0x2,%edx
    1625:	48 8d 35 28 0b 00 00 	lea    0xb28(%rip),%rsi        # 2154 <_IO_stdin_used+0x154>
    162c:	31 c0                	xor    %eax,%eax
    162e:	bf 01 00 00 00       	mov    $0x1,%edi
    1633:	e8 38 fb ff ff       	call   1170 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    1638:	eb 16                	jmp    1650 <main+0x490>
    163a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1640:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    1647:	48 81 fd 00 00 00 18 	cmp    $0x18000000,%rbp
    164e:	74 4f                	je     169f <main+0x4df>
      int compcount = 0;
      for (int n = 0 ; n < 2 ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    1650:	48 8b 43 18          	mov    0x18(%rbx),%rax
    1654:	48 01 e8             	add    %rbp,%rax
    1657:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
    165e:	83 3a 01             	cmpl   $0x1,(%rdx)
    1661:	75 dd                	jne    1640 <main+0x480>
    1663:	83 7a 04 01          	cmpl   $0x1,0x4(%rdx)
    1667:	75 d7                	jne    1640 <main+0x480>
      if (compcount == 2) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
          struct timespec end = thread_data[sender].data[y].end;
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    1669:	4c 8b 80 88 00 00 00 	mov    0x88(%rax),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    1670:	48 8b 88 80 00 00 00 	mov    0x80(%rax),%rcx
    1677:	31 d2                	xor    %edx,%edx
    1679:	4c 89 e6             	mov    %r12,%rsi
    167c:	48 2b 08             	sub    (%rax),%rcx
    167f:	4c 2b 40 08          	sub    0x8(%rax),%r8
    1683:	31 c0                	xor    %eax,%eax
    1685:	bf 01 00 00 00       	mov    $0x1,%edi
    168a:	e8 e1 fa ff ff       	call   1170 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    168f:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    1696:	48 81 fd 00 00 00 18 	cmp    $0x18000000,%rbp
    169d:	75 b1                	jne    1650 <main+0x490>
    169f:	31 d2                	xor    %edx,%edx
    16a1:	31 c0                	xor    %eax,%eax
    16a3:	48 8d 35 d4 0a 00 00 	lea    0xad4(%rip),%rsi        # 217e <_IO_stdin_used+0x17e>
    16aa:	bf 01 00 00 00       	mov    $0x1,%edi
    16af:	e8 bc fa ff ff       	call   1170 <__printf_chk@plt>
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    16b4:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    16b9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    16c2:	0f 85 dc 00 00 00    	jne    17a4 <main+0x5e4>
    16c8:	48 83 c4 68          	add    $0x68,%rsp
    16cc:	31 c0                	xor    %eax,%eax
    16ce:	5b                   	pop    %rbx
    16cf:	5d                   	pop    %rbp
    16d0:	41 5c                	pop    %r12
    16d2:	41 5d                	pop    %r13
    16d4:	41 5e                	pop    %r14
    16d6:	41 5f                	pop    %r15
    16d8:	c3                   	ret
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    16d9:	be 80 01 00 00       	mov    $0x180,%esi
    16de:	bf 00 00 10 00       	mov    $0x100000,%edi
    16e3:	e8 78 fa ff ff       	call   1160 <calloc@plt>
    16e8:	49 89 46 18          	mov    %rax,0x18(%r14)
    16ec:	49 89 c4             	mov    %rax,%r12
        for (int n = 0 ; n < buffer_size ; n++) {
    16ef:	4c 8d b8 00 01 00 00 	lea    0x100(%rax),%r15
    16f6:	49 81 c4 00 01 00 18 	add    $0x18000100,%r12
    16fd:	0f 1f 00             	nopl   (%rax)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1700:	be 04 00 00 00       	mov    $0x4,%esi
    1705:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    170a:	49 81 c7 80 01 00 00 	add    $0x180,%r15
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1711:	e8 4a fa ff ff       	call   1160 <calloc@plt>
    1716:	49 89 87 80 fe ff ff 	mov    %rax,-0x180(%r15)
        for (int n = 0 ; n < buffer_size ; n++) {
    171d:	4d 39 e7             	cmp    %r12,%r15
    1720:	75 de                	jne    1700 <main+0x540>
      thread_data[j].readers = thread_data[sender].readers;
    1722:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    1729:	45 31 c0             	xor    %r8d,%r8d
    172c:	31 c9                	xor    %ecx,%ecx
    172e:	4c 89 ee             	mov    %r13,%rsi
      thread_data[j].sender = &thread_data[sender];
    1731:	66 0f 6f 1c 24       	movdqa (%rsp),%xmm3
    1736:	ba 02 00 00 00       	mov    $0x2,%edx
    173b:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].size = buffer_size;
    1740:	49 c7 86 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%r14)
      thread_data[j].readers = thread_data[sender].readers;
    174b:	49 89 86 80 01 00 00 	mov    %rax,0x180(%r14)
    1752:	31 c0                	xor    %eax,%eax
      thread_data[j].start = 0;
    1754:	41 c7 86 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r14)
      thread_data[j].sender = &thread_data[sender];
    175f:	41 0f 11 5e 08       	movups %xmm3,0x8(%r14)
    1764:	e8 07 fa ff ff       	call   1170 <__printf_chk@plt>
        thread_data[n].readers[receiver_index] = &thread_data[j];
    1769:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    1770:	4c 89 30             	mov    %r14,(%rax)
    1773:	48 8b 83 80 03 00 00 	mov    0x380(%rbx),%rax
    177a:	4c 89 30             	mov    %r14,(%rax)
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    177d:	49 81 c6 00 02 00 00 	add    $0x200,%r14
    1784:	b8 01 00 00 00       	mov    $0x1,%eax
    1789:	e9 fb fb ff ff       	jmp    1389 <main+0x1c9>
    178e:	48 8d 3d 6b 09 00 00 	lea    0x96b(%rip),%rdi        # 2100 <_IO_stdin_used+0x100>
    1795:	e8 76 f9 ff ff       	call   1110 <puts@plt>
               exit(1);
    179a:	bf 01 00 00 00       	mov    $0x1,%edi
    179f:	e8 fc f9 ff ff       	call   11a0 <exit@plt>
}
    17a4:	e8 87 f9 ff ff       	call   1130 <__stack_chk_fail@plt>
    17a9:	48 8d 3d 6e 09 00 00 	lea    0x96e(%rip),%rdi        # 211e <_IO_stdin_used+0x11e>
    17b0:	e8 5b f9 ff ff       	call   1110 <puts@plt>
              exit(1);
    17b5:	bf 01 00 00 00       	mov    $0x1,%edi
    17ba:	e8 e1 f9 ff ff       	call   11a0 <exit@plt>
    17bf:	90                   	nop

00000000000017c0 <_start>:
    17c0:	f3 0f 1e fa          	endbr64
    17c4:	31 ed                	xor    %ebp,%ebp
    17c6:	49 89 d1             	mov    %rdx,%r9
    17c9:	5e                   	pop    %rsi
    17ca:	48 89 e2             	mov    %rsp,%rdx
    17cd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    17d1:	50                   	push   %rax
    17d2:	54                   	push   %rsp
    17d3:	45 31 c0             	xor    %r8d,%r8d
    17d6:	31 c9                	xor    %ecx,%ecx
    17d8:	48 8d 3d e1 f9 ff ff 	lea    -0x61f(%rip),%rdi        # 11c0 <main>
    17df:	ff 15 f3 27 00 00    	call   *0x27f3(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    17e5:	f4                   	hlt
    17e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000017f0 <deregister_tm_clones>:
    17f0:	48 8d 3d 19 28 00 00 	lea    0x2819(%rip),%rdi        # 4010 <__TMC_END__>
    17f7:	48 8d 05 12 28 00 00 	lea    0x2812(%rip),%rax        # 4010 <__TMC_END__>
    17fe:	48 39 f8             	cmp    %rdi,%rax
    1801:	74 15                	je     1818 <deregister_tm_clones+0x28>
    1803:	48 8b 05 d6 27 00 00 	mov    0x27d6(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    180a:	48 85 c0             	test   %rax,%rax
    180d:	74 09                	je     1818 <deregister_tm_clones+0x28>
    180f:	ff e0                	jmp    *%rax
    1811:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1818:	c3                   	ret
    1819:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001820 <register_tm_clones>:
    1820:	48 8d 3d e9 27 00 00 	lea    0x27e9(%rip),%rdi        # 4010 <__TMC_END__>
    1827:	48 8d 35 e2 27 00 00 	lea    0x27e2(%rip),%rsi        # 4010 <__TMC_END__>
    182e:	48 29 fe             	sub    %rdi,%rsi
    1831:	48 89 f0             	mov    %rsi,%rax
    1834:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1838:	48 c1 f8 03          	sar    $0x3,%rax
    183c:	48 01 c6             	add    %rax,%rsi
    183f:	48 d1 fe             	sar    %rsi
    1842:	74 14                	je     1858 <register_tm_clones+0x38>
    1844:	48 8b 05 a5 27 00 00 	mov    0x27a5(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    184b:	48 85 c0             	test   %rax,%rax
    184e:	74 08                	je     1858 <register_tm_clones+0x38>
    1850:	ff e0                	jmp    *%rax
    1852:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1858:	c3                   	ret
    1859:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001860 <__do_global_dtors_aux>:
    1860:	f3 0f 1e fa          	endbr64
    1864:	80 3d a5 27 00 00 00 	cmpb   $0x0,0x27a5(%rip)        # 4010 <__TMC_END__>
    186b:	75 2b                	jne    1898 <__do_global_dtors_aux+0x38>
    186d:	55                   	push   %rbp
    186e:	48 83 3d 82 27 00 00 00 	cmpq   $0x0,0x2782(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1876:	48 89 e5             	mov    %rsp,%rbp
    1879:	74 0c                	je     1887 <__do_global_dtors_aux+0x27>
    187b:	48 8b 3d 86 27 00 00 	mov    0x2786(%rip),%rdi        # 4008 <__dso_handle>
    1882:	e8 69 f8 ff ff       	call   10f0 <__cxa_finalize@plt>
    1887:	e8 64 ff ff ff       	call   17f0 <deregister_tm_clones>
    188c:	c6 05 7d 27 00 00 01 	movb   $0x1,0x277d(%rip)        # 4010 <__TMC_END__>
    1893:	5d                   	pop    %rbp
    1894:	c3                   	ret
    1895:	0f 1f 00             	nopl   (%rax)
    1898:	c3                   	ret
    1899:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018a0 <frame_dummy>:
    18a0:	f3 0f 1e fa          	endbr64
    18a4:	e9 77 ff ff ff       	jmp    1820 <register_tm_clones>
    18a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018b0 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    18b0:	f3 0f 1e fa          	endbr64
    18b4:	41 55                	push   %r13
    18b6:	48 8d 35 4b 07 00 00 	lea    0x74b(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    18bd:	31 c0                	xor    %eax,%eax
    18bf:	41 54                	push   %r12
    18c1:	55                   	push   %rbp
    18c2:	53                   	push   %rbx
    18c3:	48 89 fb             	mov    %rdi,%rbx
    18c6:	48 83 ec 08          	sub    $0x8,%rsp
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    18ca:	8b 8f 04 01 00 00    	mov    0x104(%rdi),%ecx
    18d0:	8b 17                	mov    (%rdi),%edx
    18d2:	bf 01 00 00 00       	mov    $0x1,%edi
    18d7:	e8 94 f8 ff ff       	call   1170 <__printf_chk@plt>
  if (data->mode == WRITER) {
    18dc:	8b 83 04 01 00 00    	mov    0x104(%rbx),%eax
    18e2:	85 c0                	test   %eax,%eax
    18e4:	74 35                	je     191b <disruptor_thread+0x6b>
  } else if (data->mode == READER) {
    18e6:	8b 83 04 01 00 00    	mov    0x104(%rbx),%eax
    18ec:	83 f8 01             	cmp    $0x1,%eax
    18ef:	0f 84 e1 00 00 00    	je     19d6 <disruptor_thread+0x126>
  printf("Finished %d\n", data->mode);
    18f5:	8b 93 04 01 00 00    	mov    0x104(%rbx),%edx
    18fb:	48 8d 35 8f 07 00 00 	lea    0x78f(%rip),%rsi        # 2091 <_IO_stdin_used+0x91>
    1902:	bf 01 00 00 00       	mov    $0x1,%edi
    1907:	31 c0                	xor    %eax,%eax
    1909:	e8 62 f8 ff ff       	call   1170 <__printf_chk@plt>
}
    190e:	48 83 c4 08          	add    $0x8,%rsp
    1912:	31 c0                	xor    %eax,%eax
    1914:	5b                   	pop    %rbx
    1915:	5d                   	pop    %rbp
    1916:	41 5c                	pop    %r12
    1918:	41 5d                	pop    %r13
    191a:	c3                   	ret
    191b:	48 8d 3d 63 07 00 00 	lea    0x763(%rip),%rdi        # 2085 <_IO_stdin_used+0x85>
    1922:	e8 e9 f7 ff ff       	call   1110 <puts@plt>
    struct Thread *me = data->sender;
    1927:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    while (data->running == 1) {
    192b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    1930:	8b 83 10 01 00 00    	mov    0x110(%rbx),%eax
    1936:	83 f8 01             	cmp    $0x1,%eax
    1939:	75 ba                	jne    18f5 <disruptor_thread+0x45>
      asm volatile ("sfence" ::: "memory");
    193b:	0f ae f8             	sfence
      for (int x  = 0 ; x < data->other_count; x++) {
    193e:	48 63 8b 88 01 00 00 	movslq 0x188(%rbx),%rcx
    1945:	85 c9                	test   %ecx,%ecx
    1947:	7e 3f                	jle    1988 <disruptor_thread+0xd8>
        if ((me->end + 1) % data->size == data->readers[x]->start) {
    1949:	8b 85 00 01 00 00    	mov    0x100(%rbp),%eax
    194f:	83 c0 01             	add    $0x1,%eax
    1952:	48 98                	cltq
    1954:	48 99                	cqto
    1956:	48 f7 bb 08 01 00 00 	idivq  0x108(%rbx)
    195d:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    1964:	48 8d 34 c8          	lea    (%rax,%rcx,8),%rsi
    1968:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    1970:	48 8b 08             	mov    (%rax),%rcx
    1973:	48 63 89 80 00 00 00 	movslq 0x80(%rcx),%rcx
    197a:	48 39 ca             	cmp    %rcx,%rdx
    197d:	74 b1                	je     1930 <disruptor_thread+0x80>
      for (int x  = 0 ; x < data->other_count; x++) {
    197f:	48 83 c0 08          	add    $0x8,%rax
    1983:	48 39 c6             	cmp    %rax,%rsi
    1986:	75 e8                	jne    1970 <disruptor_thread+0xc0>
            if (changed = __atomic_add_fetch(&me->end, 1, __ATOMIC_RELEASE)) {
    1988:	b8 01 00 00 00       	mov    $0x1,%eax
    198d:	f0 0f c1 85 00 01 00 00 	lock xadd %eax,0x100(%rbp)
    1995:	83 c0 01             	add    $0x1,%eax
    1998:	74 96                	je     1930 <disruptor_thread+0x80>
              changed = changed % me->size;
    199a:	48 98                	cltq
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    199c:	48 8b 75 18          	mov    0x18(%rbp),%rsi
    19a0:	bf 04 00 00 00       	mov    $0x4,%edi
              changed = changed % me->size;
    19a5:	48 99                	cqto
    19a7:	48 f7 bd 08 01 00 00 	idivq  0x108(%rbp)
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    19ae:	4c 8d 24 52          	lea    (%rdx,%rdx,2),%r12
    19b2:	49 c1 e4 07          	shl    $0x7,%r12
    19b6:	4c 01 e6             	add    %r12,%rsi
    19b9:	e8 62 f7 ff ff       	call   1120 <clock_gettime@plt>
              me->data[changed].complete[1] = 1;
    19be:	48 8b 45 18          	mov    0x18(%rbp),%rax
    19c2:	4a 8b 84 20 00 01 00 00 	mov    0x100(%rax,%r12,1),%rax
    19ca:	c7 40 04 01 00 00 00 	movl   $0x1,0x4(%rax)
              next = (changed + 1) % data->size;
    19d1:	e9 5a ff ff ff       	jmp    1930 <disruptor_thread+0x80>
    19d6:	48 8d 3d c1 06 00 00 	lea    0x6c1(%rip),%rdi        # 209e <_IO_stdin_used+0x9e>
    19dd:	e8 2e f7 ff ff       	call   1110 <puts@plt>
    struct Thread *sender = data->sender;
    19e2:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    struct Snapshot * rdata = sender->data;
    19e6:	4c 8b 6d 18          	mov    0x18(%rbp),%r13
    while (data->running == 1) {
    19ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    19f0:	8b 83 10 01 00 00    	mov    0x110(%rbx),%eax
    19f6:	83 f8 01             	cmp    $0x1,%eax
    19f9:	0f 85 f6 fe ff ff    	jne    18f5 <disruptor_thread+0x45>
      asm volatile ("sfence" ::: "memory");
    19ff:	0f ae f8             	sfence
      if (sender->end % sender->size == sender->start) {
    1a02:	48 63 85 00 01 00 00 	movslq 0x100(%rbp),%rax
    1a09:	48 99                	cqto
    1a0b:	48 f7 bd 08 01 00 00 	idivq  0x108(%rbp)
    1a12:	48 63 85 80 00 00 00 	movslq 0x80(%rbp),%rax
    1a19:	48 39 c2             	cmp    %rax,%rdx
    1a1c:	74 d2                	je     19f0 <disruptor_thread+0x140>
          int changed = data->start;
    1a1e:	48 63 8b 80 00 00 00 	movslq 0x80(%rbx),%rcx
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end);
    1a25:	bf 04 00 00 00       	mov    $0x4,%edi
              data->start = (data->start + 1) % data->size;
    1a2a:	8d 41 01             	lea    0x1(%rcx),%eax
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end);
    1a2d:	4c 8d 24 49          	lea    (%rcx,%rcx,2),%r12
              data->start = (data->start + 1) % data->size;
    1a31:	48 98                	cltq
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end);
    1a33:	49 c1 e4 07          	shl    $0x7,%r12
              data->start = (data->start + 1) % data->size;
    1a37:	48 99                	cqto
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end);
    1a39:	4d 01 ec             	add    %r13,%r12
              data->start = (data->start + 1) % data->size;
    1a3c:	48 f7 bb 08 01 00 00 	idivq  0x108(%rbx)
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end);
    1a43:	49 8d b4 24 80 00 00 00 	lea    0x80(%r12),%rsi
              data->start = (data->start + 1) % data->size;
    1a4b:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end);
    1a51:	e8 ca f6 ff ff       	call   1120 <clock_gettime@plt>
              rdata[changed].complete[0] = 1;
    1a56:	49 8b 84 24 00 01 00 00 	mov    0x100(%r12),%rax
    1a5e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    1a64:	eb 8a                	jmp    19f0 <disruptor_thread+0x140>
    1a66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001a70 <min>:
int min(long a, long b) {
    1a70:	f3 0f 1e fa          	endbr64
  if (a < b) return a;
    1a74:	48 39 f7             	cmp    %rsi,%rdi
    1a77:	7c 02                	jl     1a7b <min+0xb>
  if (b < a) return b;
    1a79:	7f 05                	jg     1a80 <min+0x10>
  if (a < b) return a;
    1a7b:	89 f8                	mov    %edi,%eax
    1a7d:	c3                   	ret
    1a7e:	66 90                	xchg   %ax,%ax
  if (b < a) return b;
    1a80:	89 f0                	mov    %esi,%eax
}
    1a82:	c3                   	ret

Disassembly of section .fini:

0000000000001a84 <_fini>:
    1a84:	f3 0f 1e fa          	endbr64
    1a88:	48 83 ec 08          	sub    $0x8,%rsp
    1a8c:	48 83 c4 08          	add    $0x8,%rsp
    1a90:	c3                   	ret
