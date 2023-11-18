
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
    for (int j = 0; j < cores / 2 ; j++) {
      // printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(2 * j, receivercpu);
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
      CPU_SET(2 * j, receivercpu);
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
      CPU_SET(2 * j, receivercpu);
    1292:	48 81 08 55 05 00 00 	orq    $0x555,(%rax)
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
    1317:	4c 8d a8 80 00 00 00 	lea    0x80(%rax),%r13
    131e:	4c 8d a0 80 00 00 18 	lea    0x18000080(%rax),%r12
    1325:	0f 1f 00             	nopl   (%rax)
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1328:	be 04 00 00 00       	mov    $0x4,%esi
    132d:	bf 02 00 00 00       	mov    $0x2,%edi
      for (int k = 0 ; k < buffer_size ; k++) {
    1332:	49 81 c5 80 01 00 00 	add    $0x180,%r13
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1339:	e8 22 fe ff ff       	call   1160 <calloc@plt>
        thread_data[n].data[k].end = calloc(other_count, sizeof(int));
    133e:	be 04 00 00 00       	mov    $0x4,%esi
    1343:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1348:	49 89 85 00 ff ff ff 	mov    %rax,-0x100(%r13)
        thread_data[n].data[k].end = calloc(other_count, sizeof(int));
    134f:	e8 0c fe ff ff       	call   1160 <calloc@plt>
    1354:	49 89 85 80 fe ff ff 	mov    %rax,-0x180(%r13)
      for (int k = 0 ; k < buffer_size ; k++) {
    135b:	4d 39 ec             	cmp    %r13,%r12
    135e:	75 c8                	jne    1328 <main+0x168>
      }
      thread_data[n].other_count = other_count;
    1360:	41 c7 86 88 01 00 00 02 00 00 00 	movl   $0x2,0x188(%r14)
    for (int n = sender; n < sender + writers_count; n++) {
    136b:	49 81 c6 00 02 00 00 	add    $0x200,%r14
    1372:	45 85 ff             	test   %r15d,%r15d
    1375:	75 0b                	jne    1382 <main+0x1c2>
    1377:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    137d:	e9 1c ff ff ff       	jmp    129e <main+0xde>
    1382:	66 48 0f 6e d3       	movq   %rbx,%xmm2
    1387:	4c 8d b3 00 04 00 00 	lea    0x400(%rbx),%r14
    138e:	31 c0                	xor    %eax,%eax
    1390:	66 0f 6c d2          	punpcklqdq %xmm2,%xmm2
    1394:	4c 8d 2d bd 0c 00 00 	lea    0xcbd(%rip),%r13        # 2058 <_IO_stdin_used+0x58>
    139b:	0f 29 14 24          	movaps %xmm2,(%rsp)
    139f:	8d 50 02             	lea    0x2(%rax),%edx
    }
    // printf("Created data for %d\n", sender);
    int seq[] = {1, 2, 5};
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      thread_data[j].thread_index = j;
      thread_data[j].reader_index = receiver_index;
    13a2:	41 89 86 8c 01 00 00 	mov    %eax,0x18c(%r14)
      thread_data[j].multiple = receiver_index % other_count;
    13a9:	41 89 86 90 01 00 00 	mov    %eax,0x190(%r14)
      thread_data[j].other_count = other_count;
     
      thread_data[j].cpu_set = receivercpu;
    13b0:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
      thread_data[j].running = 1;
    13b5:	41 c7 86 10 01 00 00 01 00 00 00 	movl   $0x1,0x110(%r14)
      thread_data[j].thread_index = j;
    13c0:	41 89 16             	mov    %edx,(%r14)
      thread_data[j].other_count = other_count;
    13c3:	41 c7 86 88 01 00 00 02 00 00 00 	movl   $0x2,0x188(%r14)
      thread_data[j].cpu_set = receivercpu;
    13ce:	49 89 86 18 01 00 00 	mov    %rax,0x118(%r14)
      thread_data[j].mode = READER;
    13d5:	41 c7 86 04 01 00 00 01 00 00 00 	movl   $0x1,0x104(%r14)
      if (j == receiver) {
    13e0:	83 fa 02             	cmp    $0x2,%edx
    13e3:	0f 84 2e 03 00 00    	je     1717 <main+0x557>
        for (int n = 0 ; n < buffer_size ; n++) {
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
        }
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
    13e9:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
    13ee:	45 31 c0             	xor    %r8d,%r8d
    13f1:	b9 01 00 00 00       	mov    $0x1,%ecx
    13f6:	4c 89 ee             	mov    %r13,%rsi
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    13f9:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    1400:	ba 03 00 00 00       	mov    $0x3,%edx
    1405:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].size = buffer_size;
    140a:	49 c7 86 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%r14)
      thread_data[j].start = 0;
    1415:	41 c7 86 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r14)
      thread_data[j].readers = thread_data[sender].readers;
    1420:	49 89 86 80 01 00 00 	mov    %rax,0x180(%r14)
    1427:	31 c0                	xor    %eax,%eax
      thread_data[j].sender = &thread_data[sender];
    1429:	41 0f 11 4e 08       	movups %xmm1,0x8(%r14)
    142e:	e8 3d fd ff ff       	call   1170 <__printf_chk@plt>
      printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        thread_data[n].readers[receiver_index] = &thread_data[j];
    1433:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    143a:	31 d2                	xor    %edx,%edx
    143c:	48 8d 35 a0 0c 00 00 	lea    0xca0(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    1443:	bf 01 00 00 00       	mov    $0x1,%edi
    1448:	4c 89 70 08          	mov    %r14,0x8(%rax)
    144c:	48 8b 83 80 03 00 00 	mov    0x380(%rbx),%rax
    1453:	4c 89 70 08          	mov    %r14,0x8(%rax)
    1457:	31 c0                	xor    %eax,%eax
    1459:	e8 12 fd ff ff       	call   1170 <__printf_chk@plt>
      }
    }
    printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    145e:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    1461:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    1466:	c7 44 24 2c 00 00 00 00 	movl   $0x0,0x2c(%rsp)
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    146e:	4c 8d 75 10          	lea    0x10(%rbp),%r14
  param.sched_priority = 0;
    1472:	41 bf 02 00 00 00    	mov    $0x2,%r15d
    1478:	4c 8d 60 70          	lea    0x70(%rax),%r12
    147c:	48 8d 35 60 0c 00 00 	lea    0xc60(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    1483:	bf 01 00 00 00       	mov    $0x1,%edi
    1488:	31 c0                	xor    %eax,%eax
    148a:	44 89 fa             	mov    %r15d,%edx
    148d:	e8 de fc ff ff       	call   1170 <__printf_chk@plt>
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    1492:	31 f6                	xor    %esi,%esi
    1494:	4c 89 e7             	mov    %r12,%rdi
    1497:	e8 b4 fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    149c:	85 c0                	test   %eax,%eax
    149e:	0f 85 2a 03 00 00    	jne    17ce <main+0x60e>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    14a4:	48 8d 74 24 2c       	lea    0x2c(%rsp),%rsi
    14a9:	4c 89 e7             	mov    %r12,%rdi
    14ac:	e8 df fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    14b1:	85 c0                	test   %eax,%eax
    14b3:	0f 85 30 03 00 00    	jne    17e9 <main+0x629>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    14b9:	4c 89 f9             	mov    %r15,%rcx
    14bc:	4c 89 e6             	mov    %r12,%rsi
    14bf:	4c 89 f7             	mov    %r14,%rdi
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    14c2:	49 83 c4 38          	add    $0x38,%r12
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    14c6:	48 c1 e1 09          	shl    $0x9,%rcx
    14ca:	48 8d 15 1f 04 00 00 	lea    0x41f(%rip),%rdx        # 18f0 <disruptor_thread>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    14d1:	49 83 c6 08          	add    $0x8,%r14
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    14d5:	48 01 d9             	add    %rbx,%rcx
    14d8:	e8 a3 fc ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    14dd:	49 8b 7e f8          	mov    -0x8(%r14),%rdi
    14e1:	be 08 00 00 00       	mov    $0x8,%esi
    14e6:	48 8b 93 18 05 00 00 	mov    0x518(%rbx),%rdx
    14ed:	e8 0e fc ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    14f2:	49 83 ff 02          	cmp    $0x2,%r15
    14f6:	75 0b                	jne    1503 <main+0x343>
    14f8:	41 bf 03 00 00 00    	mov    $0x3,%r15d
    14fe:	e9 79 ff ff ff       	jmp    147c <main+0x2bc>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    1503:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    1508:	31 f6                	xor    %esi,%esi
    150a:	4c 89 ff             	mov    %r15,%rdi
    150d:	e8 3e fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    1512:	85 c0                	test   %eax,%eax
    1514:	0f 85 b4 02 00 00    	jne    17ce <main+0x60e>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    151a:	48 8d 74 24 28       	lea    0x28(%rsp),%rsi
    151f:	4c 89 ff             	mov    %r15,%rdi
      param2.sched_priority = 0;
    1522:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    152a:	e8 61 fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    152f:	85 c0                	test   %eax,%eax
    1531:	0f 85 b2 02 00 00    	jne    17e9 <main+0x629>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    1537:	48 89 d9             	mov    %rbx,%rcx
    153a:	48 89 ef             	mov    %rbp,%rdi
    153d:	48 8d 15 ac 03 00 00 	lea    0x3ac(%rip),%rdx        # 18f0 <disruptor_thread>
    1544:	4c 89 fe             	mov    %r15,%rsi
    1547:	e8 34 fc ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    154c:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    1550:	be 08 00 00 00       	mov    $0x8,%esi
    void * res1;
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    1555:	45 31 e4             	xor    %r12d,%r12d
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    1558:	48 8b 93 18 01 00 00 	mov    0x118(%rbx),%rdx
    155f:	e8 9c fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    1564:	4c 89 fe             	mov    %r15,%rsi
    1567:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
    156b:	48 8d 8b 00 02 00 00 	lea    0x200(%rbx),%rcx
    1572:	48 83 c6 38          	add    $0x38,%rsi
    1576:	48 8d 15 73 03 00 00 	lea    0x373(%rip),%rdx        # 18f0 <disruptor_thread>
    157d:	e8 fe fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    1582:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
    1586:	be 08 00 00 00       	mov    $0x8,%esi
    158b:	48 8b 93 18 03 00 00 	mov    0x318(%rbx),%rdx
    1592:	e8 69 fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
  struct timespec preempt = {
    1597:	66 0f 6f 05 f1 0b 00 00 	movdqa 0xbf1(%rip),%xmm0        # 2190 <_IO_stdin_used+0x190>
    159f:	ba 0a 00 00 00       	mov    $0xa,%edx
    15a4:	31 c0                	xor    %eax,%eax
    15a6:	48 8d 35 8e 0b 00 00 	lea    0xb8e(%rip),%rsi        # 213b <_IO_stdin_used+0x13b>
    15ad:	bf 01 00 00 00       	mov    $0x1,%edi
    15b2:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    15b7:	e8 b4 fb ff ff       	call   1170 <__printf_chk@plt>
  nanosleep(&preempt , &rem2);
    15bc:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    15c1:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    15c6:	e8 75 fb ff ff       	call   1140 <nanosleep@plt>
      pthread_join(thread[n], res1);
    15cb:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    15cf:	4c 89 e6             	mov    %r12,%rsi
    thread_data[sender].running = 0;
    15d2:	c7 83 10 01 00 00 00 00 00 00 	movl   $0x0,0x110(%rbx)
      thread_data[j].running = 0;
    15dc:	c7 83 10 05 00 00 00 00 00 00 	movl   $0x0,0x510(%rbx)
    15e6:	c7 83 10 07 00 00 00 00 00 00 	movl   $0x0,0x710(%rbx)
      thread_data[n].running = 0;
    15f0:	c7 83 10 01 00 00 00 00 00 00 	movl   $0x0,0x110(%rbx)
    15fa:	c7 83 10 03 00 00 00 00 00 00 	movl   $0x0,0x310(%rbx)
      pthread_join(thread[n], res1);
    1604:	e8 a7 fb ff ff       	call   11b0 <pthread_join@plt>
    1609:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
    160d:	4c 89 e6             	mov    %r12,%rsi
    1610:	e8 9b fb ff ff       	call   11b0 <pthread_join@plt>
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    1615:	48 8b 7d 10          	mov    0x10(%rbp),%rdi
    1619:	4c 89 e6             	mov    %r12,%rsi
    161c:	e8 8f fb ff ff       	call   11b0 <pthread_join@plt>
    1621:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
    1625:	4c 89 e6             	mov    %r12,%rsi
    1628:	31 ed                	xor    %ebp,%ebp
    162a:	4c 8d 25 39 0b 00 00 	lea    0xb39(%rip),%r12        # 216a <_IO_stdin_used+0x16a>
    1631:	e8 7a fb ff ff       	call   11b0 <pthread_join@plt>
    1636:	ba 02 00 00 00       	mov    $0x2,%edx
    163b:	48 8d 35 12 0b 00 00 	lea    0xb12(%rip),%rsi        # 2154 <_IO_stdin_used+0x154>
    1642:	31 c0                	xor    %eax,%eax
    1644:	bf 01 00 00 00       	mov    $0x1,%edi
    1649:	e8 22 fb ff ff       	call   1170 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    164e:	eb 10                	jmp    1660 <main+0x4a0>
    1650:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    1657:	48 81 fd 00 00 00 18 	cmp    $0x18000000,%rbp
    165e:	74 7d                	je     16dd <main+0x51d>
      int compcount = 0;
      for (int n = 0 ; n < 2 ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    1660:	48 8b 43 18          	mov    0x18(%rbx),%rax
    1664:	48 01 e8             	add    %rbp,%rax
    1667:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
    166e:	83 3a 01             	cmpl   $0x1,(%rdx)
    1671:	75 dd                	jne    1650 <main+0x490>
    1673:	83 7a 04 01          	cmpl   $0x1,0x4(%rdx)
    1677:	75 d7                	jne    1650 <main+0x490>
      // printf("%d\n", compcount);
      if (compcount == 2) {
      for (int n = 0 ; n < other_count ; n++) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
          struct timespec end = thread_data[sender].data[y].end[n];
    1679:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    1680:	4c 89 e6             	mov    %r12,%rsi
    1683:	bf 01 00 00 00       	mov    $0x1,%edi
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    1688:	4c 8b 42 08          	mov    0x8(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    168c:	48 8b 0a             	mov    (%rdx),%rcx
    168f:	31 d2                	xor    %edx,%edx
    1691:	48 2b 08             	sub    (%rax),%rcx
    1694:	4c 2b 40 08          	sub    0x8(%rax),%r8
    1698:	31 c0                	xor    %eax,%eax
    169a:	e8 d1 fa ff ff       	call   1170 <__printf_chk@plt>
          struct timespec start = thread_data[sender].data[y].start;
    169f:	48 8b 43 18          	mov    0x18(%rbx),%rax
    16a3:	4c 89 e6             	mov    %r12,%rsi
    16a6:	bf 01 00 00 00       	mov    $0x1,%edi
    16ab:	48 01 e8             	add    %rbp,%rax
    for (int y = 0 ; y < buffer_size; y++) {
    16ae:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
          struct timespec end = thread_data[sender].data[y].end[n];
    16b5:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    16bc:	4c 8b 42 18          	mov    0x18(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    16c0:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    16c4:	31 d2                	xor    %edx,%edx
    16c6:	48 2b 08             	sub    (%rax),%rcx
    16c9:	4c 2b 40 08          	sub    0x8(%rax),%r8
    16cd:	31 c0                	xor    %eax,%eax
    16cf:	e8 9c fa ff ff       	call   1170 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    16d4:	48 81 fd 00 00 00 18 	cmp    $0x18000000,%rbp
    16db:	75 83                	jne    1660 <main+0x4a0>
    16dd:	31 d2                	xor    %edx,%edx
    16df:	31 c0                	xor    %eax,%eax
    16e1:	48 8d 35 96 0a 00 00 	lea    0xa96(%rip),%rsi        # 217e <_IO_stdin_used+0x17e>
    16e8:	bf 01 00 00 00       	mov    $0x1,%edi
    16ed:	e8 7e fa ff ff       	call   1170 <__printf_chk@plt>
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    16f2:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    16f7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1700:	0f 85 de 00 00 00    	jne    17e4 <main+0x624>
    1706:	48 83 c4 68          	add    $0x68,%rsp
    170a:	31 c0                	xor    %eax,%eax
    170c:	5b                   	pop    %rbx
    170d:	5d                   	pop    %rbp
    170e:	41 5c                	pop    %r12
    1710:	41 5d                	pop    %r13
    1712:	41 5e                	pop    %r14
    1714:	41 5f                	pop    %r15
    1716:	c3                   	ret
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    1717:	be 80 01 00 00       	mov    $0x180,%esi
    171c:	bf 00 00 10 00       	mov    $0x100000,%edi
    1721:	e8 3a fa ff ff       	call   1160 <calloc@plt>
    1726:	49 89 46 18          	mov    %rax,0x18(%r14)
    172a:	49 89 c4             	mov    %rax,%r12
        for (int n = 0 ; n < buffer_size ; n++) {
    172d:	4c 8d b8 00 01 00 00 	lea    0x100(%rax),%r15
    1734:	49 81 c4 00 01 00 18 	add    $0x18000100,%r12
    173b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1740:	be 04 00 00 00       	mov    $0x4,%esi
    1745:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    174a:	49 81 c7 80 01 00 00 	add    $0x180,%r15
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1751:	e8 0a fa ff ff       	call   1160 <calloc@plt>
    1756:	49 89 87 80 fe ff ff 	mov    %rax,-0x180(%r15)
        for (int n = 0 ; n < buffer_size ; n++) {
    175d:	4d 39 fc             	cmp    %r15,%r12
    1760:	75 de                	jne    1740 <main+0x580>
      thread_data[j].readers = thread_data[sender].readers;
    1762:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    1769:	45 31 c0             	xor    %r8d,%r8d
    176c:	31 c9                	xor    %ecx,%ecx
    176e:	4c 89 ee             	mov    %r13,%rsi
      thread_data[j].sender = &thread_data[sender];
    1771:	66 0f 6f 1c 24       	movdqa (%rsp),%xmm3
    1776:	ba 02 00 00 00       	mov    $0x2,%edx
    177b:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].size = buffer_size;
    1780:	49 c7 86 08 01 00 00 00 00 10 00 	movq   $0x100000,0x108(%r14)
      thread_data[j].readers = thread_data[sender].readers;
    178b:	49 89 86 80 01 00 00 	mov    %rax,0x180(%r14)
    1792:	31 c0                	xor    %eax,%eax
      thread_data[j].start = 0;
    1794:	41 c7 86 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r14)
      thread_data[j].sender = &thread_data[sender];
    179f:	41 0f 11 5e 08       	movups %xmm3,0x8(%r14)
    17a4:	e8 c7 f9 ff ff       	call   1170 <__printf_chk@plt>
        thread_data[n].readers[receiver_index] = &thread_data[j];
    17a9:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    17b0:	4c 89 30             	mov    %r14,(%rax)
    17b3:	48 8b 83 80 03 00 00 	mov    0x380(%rbx),%rax
    17ba:	4c 89 30             	mov    %r14,(%rax)
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    17bd:	49 81 c6 00 02 00 00 	add    $0x200,%r14
    17c4:	b8 01 00 00 00       	mov    $0x1,%eax
    17c9:	e9 d1 fb ff ff       	jmp    139f <main+0x1df>
    17ce:	48 8d 3d 2b 09 00 00 	lea    0x92b(%rip),%rdi        # 2100 <_IO_stdin_used+0x100>
    17d5:	e8 36 f9 ff ff       	call   1110 <puts@plt>
               exit(1);
    17da:	bf 01 00 00 00       	mov    $0x1,%edi
    17df:	e8 bc f9 ff ff       	call   11a0 <exit@plt>
}
    17e4:	e8 47 f9 ff ff       	call   1130 <__stack_chk_fail@plt>
    17e9:	48 8d 3d 2e 09 00 00 	lea    0x92e(%rip),%rdi        # 211e <_IO_stdin_used+0x11e>
    17f0:	e8 1b f9 ff ff       	call   1110 <puts@plt>
              exit(1);
    17f5:	bf 01 00 00 00       	mov    $0x1,%edi
    17fa:	e8 a1 f9 ff ff       	call   11a0 <exit@plt>
    17ff:	90                   	nop

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
    1818:	48 8d 3d a1 f9 ff ff 	lea    -0x65f(%rip),%rdi        # 11c0 <main>
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
    18c2:	e8 29 f8 ff ff       	call   10f0 <__cxa_finalize@plt>
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
    18f4:	41 55                	push   %r13
    18f6:	48 8d 35 0b 07 00 00 	lea    0x70b(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    18fd:	31 c0                	xor    %eax,%eax
    18ff:	41 54                	push   %r12
    1901:	55                   	push   %rbp
    1902:	53                   	push   %rbx
    1903:	48 89 fb             	mov    %rdi,%rbx
    1906:	48 83 ec 08          	sub    $0x8,%rsp
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    190a:	8b 8f 04 01 00 00    	mov    0x104(%rdi),%ecx
    1910:	8b 17                	mov    (%rdi),%edx
    1912:	bf 01 00 00 00       	mov    $0x1,%edi
    1917:	e8 54 f8 ff ff       	call   1170 <__printf_chk@plt>
  if (data->mode == WRITER) {
    191c:	8b 83 04 01 00 00    	mov    0x104(%rbx),%eax
    1922:	85 c0                	test   %eax,%eax
    1924:	74 35                	je     195b <disruptor_thread+0x6b>
  } else if (data->mode == READER) {
    1926:	8b 83 04 01 00 00    	mov    0x104(%rbx),%eax
    192c:	83 f8 01             	cmp    $0x1,%eax
    192f:	0f 84 39 01 00 00    	je     1a6e <disruptor_thread+0x17e>
  printf("Finished %d\n", data->mode);
    1935:	8b 93 04 01 00 00    	mov    0x104(%rbx),%edx
    193b:	48 8d 35 4f 07 00 00 	lea    0x74f(%rip),%rsi        # 2091 <_IO_stdin_used+0x91>
    1942:	bf 01 00 00 00       	mov    $0x1,%edi
    1947:	31 c0                	xor    %eax,%eax
    1949:	e8 22 f8 ff ff       	call   1170 <__printf_chk@plt>
}
    194e:	48 83 c4 08          	add    $0x8,%rsp
    1952:	31 c0                	xor    %eax,%eax
    1954:	5b                   	pop    %rbx
    1955:	5d                   	pop    %rbp
    1956:	41 5c                	pop    %r12
    1958:	41 5d                	pop    %r13
    195a:	c3                   	ret
    195b:	48 8d 3d 23 07 00 00 	lea    0x723(%rip),%rdi        # 2085 <_IO_stdin_used+0x85>
    1962:	e8 a9 f7 ff ff       	call   1110 <puts@plt>
    struct Thread *me = data->sender;
    1967:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    while (data->running == 1) {
    196b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    1970:	8b bb 10 01 00 00    	mov    0x110(%rbx),%edi
    1976:	83 ff 01             	cmp    $0x1,%edi
    1979:	75 ba                	jne    1935 <disruptor_thread+0x45>
      asm volatile ("sfence" ::: "memory");
    197b:	0f ae f8             	sfence
      for (int x  = 0 ; x < data->other_count; x++) {
    197e:	48 63 8b 88 01 00 00 	movslq 0x188(%rbx),%rcx
    1985:	85 c9                	test   %ecx,%ecx
    1987:	0f 8e a5 00 00 00    	jle    1a32 <disruptor_thread+0x142>
        if ((me->end + 1) % data->size == data->readers[x]->start) {
    198d:	44 8b 85 00 01 00 00 	mov    0x100(%rbp),%r8d
    1994:	41 8d 40 01          	lea    0x1(%r8),%eax
    1998:	48 98                	cltq
    199a:	48 99                	cqto
    199c:	48 f7 bb 08 01 00 00 	idivq  0x108(%rbx)
    19a3:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    19aa:	48 8d 34 c8          	lea    (%rax,%rcx,8),%rsi
    19ae:	66 90                	xchg   %ax,%ax
    19b0:	48 8b 08             	mov    (%rax),%rcx
    19b3:	48 63 89 80 00 00 00 	movslq 0x80(%rcx),%rcx
    19ba:	48 39 ca             	cmp    %rcx,%rdx
    19bd:	74 b1                	je     1970 <disruptor_thread+0x80>
      for (int x  = 0 ; x < data->other_count; x++) {
    19bf:	48 83 c0 08          	add    $0x8,%rax
    19c3:	48 39 c6             	cmp    %rax,%rsi
    19c6:	75 e8                	jne    19b0 <disruptor_thread+0xc0>
              me->data[me->end % me->size].complete[x] = 0;
    19c8:	48 8b b5 08 01 00 00 	mov    0x108(%rbp),%rsi
    19cf:	49 63 c0             	movslq %r8d,%rax
    19d2:	4c 8b 4d 18          	mov    0x18(%rbp),%r9
            for (int x = 0 ; x < data->other_count; x++) {
    19d6:	b9 04 00 00 00       	mov    $0x4,%ecx
              me->data[me->end % me->size].complete[x] = 0;
    19db:	48 99                	cqto
    19dd:	48 f7 fe             	idiv   %rsi
    19e0:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
    19e4:	48 c1 e0 07          	shl    $0x7,%rax
    19e8:	49 8b 84 01 00 01 00 00 	mov    0x100(%r9,%rax,1),%rax
    19f0:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
            for (int x = 0 ; x < data->other_count; x++) {
    19f6:	83 bb 88 01 00 00 01 	cmpl   $0x1,0x188(%rbx)
    19fd:	7e 33                	jle    1a32 <disruptor_thread+0x142>
    19ff:	90                   	nop
              me->data[me->end % me->size].complete[x] = 0;
    1a00:	48 63 85 00 01 00 00 	movslq 0x100(%rbp),%rax
            for (int x = 0 ; x < data->other_count; x++) {
    1a07:	83 c7 01             	add    $0x1,%edi
              me->data[me->end % me->size].complete[x] = 0;
    1a0a:	48 99                	cqto
    1a0c:	48 f7 fe             	idiv   %rsi
    1a0f:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
    1a13:	48 c1 e0 07          	shl    $0x7,%rax
    1a17:	49 8b 84 01 00 01 00 00 	mov    0x100(%r9,%rax,1),%rax
    1a1f:	c7 04 08 00 00 00 00 	movl   $0x0,(%rax,%rcx,1)
            for (int x = 0 ; x < data->other_count; x++) {
    1a26:	48 83 c1 04          	add    $0x4,%rcx
    1a2a:	39 bb 88 01 00 00    	cmp    %edi,0x188(%rbx)
    1a30:	7f ce                	jg     1a00 <disruptor_thread+0x110>
            if (changed = __atomic_add_fetch(&me->end, 1, __ATOMIC_ACQUIRE)) {
    1a32:	b8 01 00 00 00       	mov    $0x1,%eax
    1a37:	f0 0f c1 85 00 01 00 00 	lock xadd %eax,0x100(%rbp)
    1a3f:	83 c0 01             	add    $0x1,%eax
    1a42:	0f 84 28 ff ff ff    	je     1970 <disruptor_thread+0x80>
              changed = changed % me->size;
    1a48:	48 98                	cltq
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1a4a:	bf 04 00 00 00       	mov    $0x4,%edi
              changed = changed % me->size;
    1a4f:	48 99                	cqto
    1a51:	48 f7 bd 08 01 00 00 	idivq  0x108(%rbp)
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1a58:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
    1a5c:	48 c1 e6 07          	shl    $0x7,%rsi
    1a60:	48 03 75 18          	add    0x18(%rbp),%rsi
    1a64:	e8 b7 f6 ff ff       	call   1120 <clock_gettime@plt>
    1a69:	e9 02 ff ff ff       	jmp    1970 <disruptor_thread+0x80>
    1a6e:	48 8d 3d 29 06 00 00 	lea    0x629(%rip),%rdi        # 209e <_IO_stdin_used+0x9e>
    1a75:	e8 96 f6 ff ff       	call   1110 <puts@plt>
    struct Thread *sender = data->sender;
    1a7a:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    struct Snapshot * rdata = sender->data;
    1a7e:	4c 8b 65 18          	mov    0x18(%rbp),%r12
    while (data->running == 1) {
    1a82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1a88:	8b 83 10 01 00 00    	mov    0x110(%rbx),%eax
    1a8e:	83 f8 01             	cmp    $0x1,%eax
    1a91:	0f 85 9e fe ff ff    	jne    1935 <disruptor_thread+0x45>
      asm volatile ("sfence" ::: "memory");
    1a97:	0f ae f8             	sfence
      if (sender->end % sender->size == data->start) {
    1a9a:	48 63 85 00 01 00 00 	movslq 0x100(%rbp),%rax
    1aa1:	48 63 b3 80 00 00 00 	movslq 0x80(%rbx),%rsi
    1aa8:	48 99                	cqto
    1aaa:	48 f7 bd 08 01 00 00 	idivq  0x108(%rbp)
    1ab1:	48 39 f2             	cmp    %rsi,%rdx
    1ab4:	74 d2                	je     1a88 <disruptor_thread+0x198>
              data->start = (changed + 1) % data->size;
    1ab6:	8d 46 01             	lea    0x1(%rsi),%eax
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1ab9:	4c 8d 2c 76          	lea    (%rsi,%rsi,2),%r13
    1abd:	48 63 b3 8c 01 00 00 	movslq 0x18c(%rbx),%rsi
    1ac4:	bf 04 00 00 00       	mov    $0x4,%edi
              data->start = (changed + 1) % data->size;
    1ac9:	48 98                	cltq
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1acb:	49 c1 e5 07          	shl    $0x7,%r13
              data->start = (changed + 1) % data->size;
    1acf:	48 99                	cqto
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1ad1:	4d 01 e5             	add    %r12,%r13
    1ad4:	48 c1 e6 04          	shl    $0x4,%rsi
              data->start = (changed + 1) % data->size;
    1ad8:	48 f7 bb 08 01 00 00 	idivq  0x108(%rbx)
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1adf:	49 03 b5 80 00 00 00 	add    0x80(%r13),%rsi
              data->start = (changed + 1) % data->size;
    1ae6:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1aec:	e8 2f f6 ff ff       	call   1120 <clock_gettime@plt>
              rdata[changed].complete[data->reader_index] = 1;
    1af1:	48 63 93 8c 01 00 00 	movslq 0x18c(%rbx),%rdx
    1af8:	49 8b 85 00 01 00 00 	mov    0x100(%r13),%rax
    1aff:	c7 04 90 01 00 00 00 	movl   $0x1,(%rax,%rdx,4)
    1b06:	eb 80                	jmp    1a88 <disruptor_thread+0x198>
    1b08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000001b10 <min>:
int min(long a, long b) {
    1b10:	f3 0f 1e fa          	endbr64
  if (a < b) return a;
    1b14:	48 39 f7             	cmp    %rsi,%rdi
    1b17:	7c 02                	jl     1b1b <min+0xb>
  if (b < a) return b;
    1b19:	7f 05                	jg     1b20 <min+0x10>
  if (a < b) return a;
    1b1b:	89 f8                	mov    %edi,%eax
    1b1d:	c3                   	ret
    1b1e:	66 90                	xchg   %ax,%ax
  if (b < a) return b;
    1b20:	89 f0                	mov    %esi,%eax
}
    1b22:	c3                   	ret

Disassembly of section .fini:

0000000000001b24 <_fini>:
    1b24:	f3 0f 1e fa          	endbr64
    1b28:	48 83 ec 08          	sub    $0x8,%rsp
    1b2c:	48 83 c4 08          	add    $0x8,%rsp
    1b30:	c3                   	ret
