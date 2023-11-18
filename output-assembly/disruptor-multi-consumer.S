
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
  // printf("Finished %d\n", data->mode);
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
    11c6:	b9 00 80 00 00       	mov    $0x8000,%ecx
  // 0, 3, 6
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int receiver2 = receiver + 1; 
    for (int n = sender; n < sender + writers_count; n++) {
    11cb:	45 31 ff             	xor    %r15d,%r15d
    11ce:	ba 0f 00 00 00       	mov    $0xf,%edx
int main() {
    11d3:	41 56                	push   %r14
    11d5:	48 8d 35 2c 0e 00 00 	lea    0xe2c(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
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
    1205:	48 8d 35 1d 0e 00 00 	lea    0xe1d(%rip),%rsi        # 2029 <_IO_stdin_used+0x29>
    120c:	31 c0                	xor    %eax,%eax
    120e:	bf 01 00 00 00       	mov    $0x1,%edi
    1213:	e8 58 ff ff ff       	call   1170 <__printf_chk@plt>
    1218:	ba 02 00 00 00       	mov    $0x2,%edx
    121d:	48 8d 35 15 0e 00 00 	lea    0xe15(%rip),%rsi        # 2039 <_IO_stdin_used+0x39>
    1224:	31 c0                	xor    %eax,%eax
    1226:	bf 01 00 00 00       	mov    $0x1,%edi
    122b:	e8 40 ff ff ff       	call   1170 <__printf_chk@plt>
    1230:	ba 02 00 00 00       	mov    $0x2,%edx
    1235:	48 8d 35 0f 0e 00 00 	lea    0xe0f(%rip),%rsi        # 204b <_IO_stdin_used+0x4b>
    123c:	31 c0                	xor    %eax,%eax
    123e:	bf 01 00 00 00       	mov    $0x1,%edi
    1243:	e8 28 ff ff ff       	call   1170 <__printf_chk@plt>
    1248:	ba 04 00 00 00       	mov    $0x4,%edx
    124d:	48 8d 35 09 0e 00 00 	lea    0xe09(%rip),%rsi        # 205d <_IO_stdin_used+0x5d>
    1254:	31 c0                	xor    %eax,%eax
    1256:	bf 01 00 00 00       	mov    $0x1,%edi
    125b:	e8 10 ff ff ff       	call   1170 <__printf_chk@plt>
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1260:	be 80 02 00 00       	mov    $0x280,%esi
    1265:	bf 04 00 00 00       	mov    $0x4,%edi
    126a:	e8 f1 fe ff ff       	call   1160 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    126f:	be 38 00 00 00       	mov    $0x38,%esi
    1274:	bf 04 00 00 00       	mov    $0x4,%edi
    1279:	66 48 0f 6e c8       	movq   %rax,%xmm1
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    127e:	48 89 c3             	mov    %rax,%rbx
    1281:	66 0f 6c c9          	punpcklqdq %xmm1,%xmm1
    1285:	49 89 dc             	mov    %rbx,%r12
    1288:	0f 29 0c 24          	movaps %xmm1,(%rsp)
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    128c:	e8 cf fe ff ff       	call   1160 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1291:	be 08 00 00 00       	mov    $0x8,%esi
    1296:	bf 04 00 00 00       	mov    $0x4,%edi
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    129b:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12a0:	e8 bb fe ff ff       	call   1160 <calloc@plt>
    12a5:	49 89 c5             	mov    %rax,%r13
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12a8:	be 80 00 00 00       	mov    $0x80,%esi
    12ad:	bf 01 00 00 00       	mov    $0x1,%edi
    12b2:	e8 a9 fe ff ff       	call   1160 <calloc@plt>
      CPU_ZERO(sendercpu);
      CPU_SET(curcpu, sendercpu);
    12b7:	43 8d 0c 3f          	lea    (%r15,%r15,1),%ecx
    12bb:	ba 01 00 00 00       	mov    $0x1,%edx
      curcpu += 2;
      // printf("assigning sender %d to core %d\n", n, curcpu);
       
      thread_data[n].thread_index = n;
      thread_data[n].cpu_set = sendercpu;
      thread_data[n].mode = WRITER;
    12c0:	41 c7 84 24 84 01 00 00 00 00 00 00 	movl   $0x0,0x184(%r12)
      CPU_SET(curcpu, sendercpu);
    12cc:	48 d3 e2             	shl    %cl,%rdx
    12cf:	48 09 10             	or     %rdx,(%rax)
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    12d2:	be 08 00 00 00       	mov    $0x8,%esi
    12d7:	bf 02 00 00 00       	mov    $0x2,%edi
      thread_data[n].thread_index = n;
    12dc:	45 89 3c 24          	mov    %r15d,(%r12)
      thread_data[n].cpu_set = sendercpu;
    12e0:	49 89 84 24 98 01 00 00 	mov    %rax,0x198(%r12)
      thread_data[n].running = 1;
    12e8:	41 c7 84 24 90 01 00 00 01 00 00 00 	movl   $0x1,0x190(%r12)
      thread_data[n].size = buffer_size;
    12f4:	49 c7 84 24 88 01 00 00 00 80 00 00 	movq   $0x8000,0x188(%r12)
      thread_data[n].end = 0;
    1300:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
      thread_data[n].sender = &thread_data[sender];
    130c:	49 89 5c 24 08       	mov    %rbx,0x8(%r12)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1311:	e8 4a fe ff ff       	call   1160 <calloc@plt>
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    1316:	be 80 01 00 00       	mov    $0x180,%esi
    131b:	bf 00 80 00 00       	mov    $0x8000,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1320:	49 89 84 24 00 02 00 00 	mov    %rax,0x200(%r12)
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    1328:	e8 33 fe ff ff       	call   1160 <calloc@plt>
    132d:	49 89 44 24 18       	mov    %rax,0x18(%r12)
      for (int k = 0 ; k < buffer_size ; k++) {
    1332:	4c 8d b0 80 00 00 00 	lea    0x80(%rax),%r14
    1339:	48 8d a8 80 00 c0 00 	lea    0xc00080(%rax),%rbp
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1340:	be 04 00 00 00       	mov    $0x4,%esi
    1345:	bf 02 00 00 00       	mov    $0x2,%edi
      for (int k = 0 ; k < buffer_size ; k++) {
    134a:	49 81 c6 80 01 00 00 	add    $0x180,%r14
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1351:	e8 0a fe ff ff       	call   1160 <calloc@plt>
        thread_data[n].data[k].end = calloc(other_count, sizeof(int));
    1356:	be 04 00 00 00       	mov    $0x4,%esi
    135b:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1360:	49 89 86 00 ff ff ff 	mov    %rax,-0x100(%r14)
        thread_data[n].data[k].end = calloc(other_count, sizeof(int));
    1367:	e8 f4 fd ff ff       	call   1160 <calloc@plt>
    136c:	49 89 86 80 fe ff ff 	mov    %rax,-0x180(%r14)
      for (int k = 0 ; k < buffer_size ; k++) {
    1373:	4c 39 f5             	cmp    %r14,%rbp
    1376:	75 c8                	jne    1340 <main+0x180>
      }
      thread_data[n].other_count = other_count;
    1378:	41 c7 84 24 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%r12)
    for (int n = sender; n < sender + writers_count; n++) {
    1384:	49 81 c4 80 02 00 00 	add    $0x280,%r12
    138b:	45 85 ff             	test   %r15d,%r15d
    138e:	75 0b                	jne    139b <main+0x1db>
    1390:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    1396:	e9 0d ff ff ff       	jmp    12a8 <main+0xe8>
    }

    // printf("Created data for %d\n", sender);
    int seq[] = {1, 2, 5};
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      thread_data[j].thread_index = j;
    139b:	c7 83 00 05 00 00 02 00 00 00 	movl   $0x2,0x500(%rbx)
      thread_data[j].reader_index = receiver_index;
      thread_data[j].multiple = receiver_index % other_count;
      thread_data[j].other_count = other_count;
     
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    13a5:	be 80 00 00 00       	mov    $0x80,%esi
    13aa:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].thread_index = j;
    13af:	48 8d ab 00 05 00 00 	lea    0x500(%rbx),%rbp
      thread_data[j].multiple = receiver_index % other_count;
    13b6:	c7 83 10 07 00 00 00 00 00 00 	movl   $0x0,0x710(%rbx)
      thread_data[j].other_count = other_count;
    13c0:	48 c7 83 08 07 00 00 02 00 00 00 	movq   $0x2,0x708(%rbx)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    13cb:	e8 90 fd ff ff       	call   1160 <calloc@plt>
      // printf("assigning receiver %d to core %d\n", j, curcpu);
      thread_data[j].cpu_set = receivercpu;
      thread_data[j].running = 1;
      thread_data[j].mode = READER;
      if (j == receiver) {
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    13d0:	be 80 01 00 00       	mov    $0x180,%esi
    13d5:	bf 00 80 00 00       	mov    $0x8000,%edi
      thread_data[j].running = 1;
    13da:	c7 83 90 06 00 00 01 00 00 00 	movl   $0x1,0x690(%rbx)
      CPU_SET(curcpu, receivercpu);
    13e4:	48 83 08 10          	orq    $0x10,(%rax)
      thread_data[j].cpu_set = receivercpu;
    13e8:	48 89 83 98 06 00 00 	mov    %rax,0x698(%rbx)
      thread_data[j].mode = READER;
    13ef:	c7 83 84 06 00 00 01 00 00 00 	movl   $0x1,0x684(%rbx)
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    13f9:	e8 62 fd ff ff       	call   1160 <calloc@plt>
    13fe:	48 89 83 18 05 00 00 	mov    %rax,0x518(%rbx)
    1405:	49 89 c7             	mov    %rax,%r15
        for (int n = 0 ; n < buffer_size ; n++) {
    1408:	4c 8d a0 00 01 00 00 	lea    0x100(%rax),%r12
    140f:	49 81 c7 00 01 c0 00 	add    $0xc00100,%r15
    1416:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1420:	be 04 00 00 00       	mov    $0x4,%esi
    1425:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    142a:	49 81 c4 80 01 00 00 	add    $0x180,%r12
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1431:	e8 2a fd ff ff       	call   1160 <calloc@plt>
    1436:	49 89 84 24 80 fe ff ff 	mov    %rax,-0x180(%r12)
        for (int n = 0 ; n < buffer_size ; n++) {
    143e:	4d 39 e7             	cmp    %r12,%r15
    1441:	75 dd                	jne    1420 <main+0x260>
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    1443:	4c 8b a3 00 02 00 00 	mov    0x200(%rbx),%r12
      thread_data[j].sender = &thread_data[sender];
    144a:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
      thread_data[j].size = buffer_size;
    144f:	48 c7 83 88 06 00 00 00 80 00 00 	movq   $0x8000,0x688(%rbx)
      thread_data[j].thread_index = j;
    145a:	48 8d 93 80 07 00 00 	lea    0x780(%rbx),%rdx
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1461:	be 80 00 00 00       	mov    $0x80,%esi
    1466:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].thread_index = j;
    146b:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
      // printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        thread_data[n].readers[receiver_index] = &thread_data[j];
    1470:	4c 8b bb 80 04 00 00 	mov    0x480(%rbx),%r15
      thread_data[j].other_count = other_count;
    1477:	48 8b 05 4a 0c 00 00 	mov    0xc4a(%rip),%rax        # 20c8 <_IO_stdin_used+0xc8>
      thread_data[j].sender = &thread_data[sender];
    147e:	0f 11 93 08 05 00 00 	movups %xmm2,0x508(%rbx)
      thread_data[j].start = 0;
    1485:	c7 83 80 05 00 00 00 00 00 00 	movl   $0x0,0x580(%rbx)
      thread_data[j].readers = thread_data[sender].readers;
    148f:	4c 89 a3 00 07 00 00 	mov    %r12,0x700(%rbx)
        thread_data[n].readers[receiver_index] = &thread_data[j];
    1496:	49 89 2c 24          	mov    %rbp,(%r12)
    149a:	49 89 2f             	mov    %rbp,(%r15)
      thread_data[j].thread_index = j;
    149d:	c7 83 80 07 00 00 03 00 00 00 	movl   $0x3,0x780(%rbx)
      thread_data[j].multiple = receiver_index % other_count;
    14a7:	c7 83 90 09 00 00 01 00 00 00 	movl   $0x1,0x990(%rbx)
      thread_data[j].other_count = other_count;
    14b1:	48 89 83 88 09 00 00 	mov    %rax,0x988(%rbx)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    14b8:	e8 a3 fc ff ff       	call   1160 <calloc@plt>
        thread_data[n].readers[receiver_index] = &thread_data[j];
    14bd:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
      thread_data[j].sender = &thread_data[sender];
    14c2:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
      thread_data[j].running = 1;
    14c7:	c7 83 10 09 00 00 01 00 00 00 	movl   $0x1,0x910(%rbx)
      CPU_SET(curcpu, receivercpu);
    14d1:	48 83 08 40          	orq    $0x40,(%rax)
      thread_data[j].cpu_set = receivercpu;
    14d5:	48 89 83 18 09 00 00 	mov    %rax,0x918(%rbx)
      thread_data[j].mode = READER;
    14dc:	c7 83 04 09 00 00 01 00 00 00 	movl   $0x1,0x904(%rbx)
      thread_data[j].size = buffer_size;
    14e6:	48 c7 83 08 09 00 00 00 80 00 00 	movq   $0x8000,0x908(%rbx)
      thread_data[j].start = 0;
    14f1:	c7 83 00 08 00 00 00 00 00 00 	movl   $0x0,0x800(%rbx)
      thread_data[j].readers = thread_data[sender].readers;
    14fb:	4c 89 a3 80 09 00 00 	mov    %r12,0x980(%rbx)
      thread_data[j].sender = &thread_data[sender];
    1502:	0f 11 93 88 07 00 00 	movups %xmm2,0x788(%rbx)
        thread_data[n].readers[receiver_index] = &thread_data[j];
    1509:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
    150e:	49 89 57 08          	mov    %rdx,0x8(%r15)
      }
    }
    curcpu = 0;
    // printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    1512:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    1515:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    151a:	c7 44 24 2c 00 00 00 00 	movl   $0x0,0x2c(%rsp)
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1522:	4d 8d 7d 10          	lea    0x10(%r13),%r15
    1526:	4c 8d 60 70          	lea    0x70(%rax),%r12
    152a:	48 05 e0 00 00 00    	add    $0xe0,%rax
    1530:	49 89 c6             	mov    %rax,%r14
      // printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    1533:	31 f6                	xor    %esi,%esi
    1535:	4c 89 e7             	mov    %r12,%rdi
    1538:	e8 13 fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    153d:	85 c0                	test   %eax,%eax
    153f:	0f 85 21 02 00 00    	jne    1766 <main+0x5a6>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    1545:	48 8d 74 24 2c       	lea    0x2c(%rsp),%rsi
    154a:	4c 89 e7             	mov    %r12,%rdi
    154d:	e8 3e fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1552:	85 c0                	test   %eax,%eax
    1554:	0f 85 27 02 00 00    	jne    1781 <main+0x5c1>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    155a:	48 89 e9             	mov    %rbp,%rcx
    155d:	4c 89 e6             	mov    %r12,%rsi
    1560:	4c 89 ff             	mov    %r15,%rdi
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1563:	49 83 c4 38          	add    $0x38,%r12
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1567:	48 8d 15 22 03 00 00 	lea    0x322(%rip),%rdx        # 1890 <disruptor_thread>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    156e:	49 83 c7 08          	add    $0x8,%r15
    1572:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1579:	e8 02 fc ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    157e:	48 8b 95 18 ff ff ff 	mov    -0xe8(%rbp),%rdx
    1585:	49 8b 7f f8          	mov    -0x8(%r15),%rdi
    1589:	be 08 00 00 00       	mov    $0x8,%esi
    158e:	e8 6d fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1593:	4d 39 f4             	cmp    %r14,%r12
    1596:	75 9b                	jne    1533 <main+0x373>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    1598:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    159d:	31 f6                	xor    %esi,%esi
    159f:	4c 89 ff             	mov    %r15,%rdi
    15a2:	e8 a9 fb ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    15a7:	85 c0                	test   %eax,%eax
    15a9:	0f 85 b7 01 00 00    	jne    1766 <main+0x5a6>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    15af:	48 8d 74 24 28       	lea    0x28(%rsp),%rsi
    15b4:	4c 89 ff             	mov    %r15,%rdi
      param2.sched_priority = 0;
    15b7:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    15bf:	e8 cc fb ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    15c4:	85 c0                	test   %eax,%eax
    15c6:	0f 85 b5 01 00 00    	jne    1781 <main+0x5c1>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    15cc:	48 89 d9             	mov    %rbx,%rcx
    15cf:	48 8d 15 ba 02 00 00 	lea    0x2ba(%rip),%rdx        # 1890 <disruptor_thread>
    15d6:	4c 89 fe             	mov    %r15,%rsi
    15d9:	4c 89 ef             	mov    %r13,%rdi
    15dc:	e8 9f fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    15e1:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    15e5:	be 08 00 00 00       	mov    $0x8,%esi
    void * res1;
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    15ea:	31 ed                	xor    %ebp,%ebp
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    15ec:	48 8b 93 98 01 00 00 	mov    0x198(%rbx),%rdx
    15f3:	4c 8d 25 b5 0a 00 00 	lea    0xab5(%rip),%r12        # 20af <_IO_stdin_used+0xaf>
    15fa:	e8 01 fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    15ff:	4c 89 fe             	mov    %r15,%rsi
    1602:	49 8d 7d 08          	lea    0x8(%r13),%rdi
    1606:	48 8d 8b 80 02 00 00 	lea    0x280(%rbx),%rcx
    160d:	48 83 c6 38          	add    $0x38,%rsi
    1611:	48 8d 15 78 02 00 00 	lea    0x278(%rip),%rdx        # 1890 <disruptor_thread>
    1618:	e8 63 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    161d:	48 8b 93 18 04 00 00 	mov    0x418(%rbx),%rdx
    1624:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    1628:	be 08 00 00 00       	mov    $0x8,%esi
    162d:	e8 ce fa ff ff       	call   1100 <pthread_setaffinity_np@plt>
  nanosleep(&preempt , &rem2);
    1632:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    1637:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec preempt = {
    163c:	66 0f 6f 05 8c 0a 00 00 	movdqa 0xa8c(%rip),%xmm0        # 20d0 <_IO_stdin_used+0xd0>
    1644:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  nanosleep(&preempt , &rem2);
    1649:	e8 f2 fa ff ff       	call   1140 <nanosleep@plt>
      pthread_join(thread[n], res1);
    164e:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    1652:	48 89 ee             	mov    %rbp,%rsi
    thread_data[sender].running = 0;
    1655:	c7 83 90 01 00 00 00 00 00 00 	movl   $0x0,0x190(%rbx)
      thread_data[j].running = 0;
    165f:	c7 83 90 06 00 00 00 00 00 00 	movl   $0x0,0x690(%rbx)
    1669:	c7 83 10 09 00 00 00 00 00 00 	movl   $0x0,0x910(%rbx)
      thread_data[n].running = 0;
    1673:	c7 83 90 01 00 00 00 00 00 00 	movl   $0x0,0x190(%rbx)
    167d:	c7 83 10 04 00 00 00 00 00 00 	movl   $0x0,0x410(%rbx)
      pthread_join(thread[n], res1);
    1687:	e8 24 fb ff ff       	call   11b0 <pthread_join@plt>
    168c:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    1690:	48 89 ee             	mov    %rbp,%rsi
    1693:	e8 18 fb ff ff       	call   11b0 <pthread_join@plt>
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    1698:	49 8b 7d 10          	mov    0x10(%r13),%rdi
    169c:	48 89 ee             	mov    %rbp,%rsi
    169f:	e8 0c fb ff ff       	call   11b0 <pthread_join@plt>
    16a4:	49 8b 7d 18          	mov    0x18(%r13),%rdi
    16a8:	48 89 ee             	mov    %rbp,%rsi
    16ab:	e8 00 fb ff ff       	call   11b0 <pthread_join@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    // printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    16b0:	eb 16                	jmp    16c8 <main+0x508>
    16b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    16b8:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    16bf:	48 81 fd 00 00 c0 00 	cmp    $0xc00000,%rbp
    16c6:	74 7d                	je     1745 <main+0x585>
      int compcount = 0;
      for (int n = 0 ; n < 2 ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    16c8:	48 8b 43 18          	mov    0x18(%rbx),%rax
    16cc:	48 01 e8             	add    %rbp,%rax
    16cf:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
    16d6:	83 3a 01             	cmpl   $0x1,(%rdx)
    16d9:	75 dd                	jne    16b8 <main+0x4f8>
    16db:	83 7a 04 01          	cmpl   $0x1,0x4(%rdx)
    16df:	75 d7                	jne    16b8 <main+0x4f8>
      // printf("%d\n", compcount);
      if (compcount == other_count) {
      for (int n = 0 ; n < other_count ; n++) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
          struct timespec end = thread_data[sender].data[y].end[n];
    16e1:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    16e8:	4c 89 e6             	mov    %r12,%rsi
    16eb:	bf 01 00 00 00       	mov    $0x1,%edi
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    16f0:	4c 8b 42 08          	mov    0x8(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    16f4:	48 8b 0a             	mov    (%rdx),%rcx
    16f7:	31 d2                	xor    %edx,%edx
    16f9:	48 2b 08             	sub    (%rax),%rcx
    16fc:	4c 2b 40 08          	sub    0x8(%rax),%r8
    1700:	31 c0                	xor    %eax,%eax
    1702:	e8 69 fa ff ff       	call   1170 <__printf_chk@plt>
          struct timespec start = thread_data[sender].data[y].start;
    1707:	48 8b 43 18          	mov    0x18(%rbx),%rax
    170b:	4c 89 e6             	mov    %r12,%rsi
    170e:	bf 01 00 00 00       	mov    $0x1,%edi
    1713:	48 01 e8             	add    %rbp,%rax
    for (int y = 0 ; y < buffer_size; y++) {
    1716:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
          struct timespec end = thread_data[sender].data[y].end[n];
    171d:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    1724:	4c 8b 42 18          	mov    0x18(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    1728:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    172c:	31 d2                	xor    %edx,%edx
    172e:	48 2b 08             	sub    (%rax),%rcx
    1731:	4c 2b 40 08          	sub    0x8(%rax),%r8
    1735:	31 c0                	xor    %eax,%eax
    1737:	e8 34 fa ff ff       	call   1170 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    173c:	48 81 fd 00 00 c0 00 	cmp    $0xc00000,%rbp
    1743:	75 83                	jne    16c8 <main+0x508>
    }
    // printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    1745:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    174a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1753:	75 27                	jne    177c <main+0x5bc>
    1755:	48 83 c4 68          	add    $0x68,%rsp
    1759:	31 c0                	xor    %eax,%eax
    175b:	5b                   	pop    %rbx
    175c:	5d                   	pop    %rbp
    175d:	41 5c                	pop    %r12
    175f:	41 5d                	pop    %r13
    1761:	41 5e                	pop    %r14
    1763:	41 5f                	pop    %r15
    1765:	c3                   	ret
    1766:	48 8d 3d 07 09 00 00 	lea    0x907(%rip),%rdi        # 2074 <_IO_stdin_used+0x74>
    176d:	e8 9e f9 ff ff       	call   1110 <puts@plt>
               exit(1);
    1772:	bf 01 00 00 00       	mov    $0x1,%edi
    1777:	e8 24 fa ff ff       	call   11a0 <exit@plt>
}
    177c:	e8 af f9 ff ff       	call   1130 <__stack_chk_fail@plt>
    1781:	48 8d 3d 0a 09 00 00 	lea    0x90a(%rip),%rdi        # 2092 <_IO_stdin_used+0x92>
    1788:	e8 83 f9 ff ff       	call   1110 <puts@plt>
              exit(1);
    178d:	bf 01 00 00 00       	mov    $0x1,%edi
    1792:	e8 09 fa ff ff       	call   11a0 <exit@plt>
    1797:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000017a0 <_start>:
    17a0:	f3 0f 1e fa          	endbr64
    17a4:	31 ed                	xor    %ebp,%ebp
    17a6:	49 89 d1             	mov    %rdx,%r9
    17a9:	5e                   	pop    %rsi
    17aa:	48 89 e2             	mov    %rsp,%rdx
    17ad:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    17b1:	50                   	push   %rax
    17b2:	54                   	push   %rsp
    17b3:	45 31 c0             	xor    %r8d,%r8d
    17b6:	31 c9                	xor    %ecx,%ecx
    17b8:	48 8d 3d 01 fa ff ff 	lea    -0x5ff(%rip),%rdi        # 11c0 <main>
    17bf:	ff 15 13 28 00 00    	call   *0x2813(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    17c5:	f4                   	hlt
    17c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000017d0 <deregister_tm_clones>:
    17d0:	48 8d 3d 39 28 00 00 	lea    0x2839(%rip),%rdi        # 4010 <__TMC_END__>
    17d7:	48 8d 05 32 28 00 00 	lea    0x2832(%rip),%rax        # 4010 <__TMC_END__>
    17de:	48 39 f8             	cmp    %rdi,%rax
    17e1:	74 15                	je     17f8 <deregister_tm_clones+0x28>
    17e3:	48 8b 05 f6 27 00 00 	mov    0x27f6(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    17ea:	48 85 c0             	test   %rax,%rax
    17ed:	74 09                	je     17f8 <deregister_tm_clones+0x28>
    17ef:	ff e0                	jmp    *%rax
    17f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    17f8:	c3                   	ret
    17f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001800 <register_tm_clones>:
    1800:	48 8d 3d 09 28 00 00 	lea    0x2809(%rip),%rdi        # 4010 <__TMC_END__>
    1807:	48 8d 35 02 28 00 00 	lea    0x2802(%rip),%rsi        # 4010 <__TMC_END__>
    180e:	48 29 fe             	sub    %rdi,%rsi
    1811:	48 89 f0             	mov    %rsi,%rax
    1814:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1818:	48 c1 f8 03          	sar    $0x3,%rax
    181c:	48 01 c6             	add    %rax,%rsi
    181f:	48 d1 fe             	sar    %rsi
    1822:	74 14                	je     1838 <register_tm_clones+0x38>
    1824:	48 8b 05 c5 27 00 00 	mov    0x27c5(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    182b:	48 85 c0             	test   %rax,%rax
    182e:	74 08                	je     1838 <register_tm_clones+0x38>
    1830:	ff e0                	jmp    *%rax
    1832:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1838:	c3                   	ret
    1839:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001840 <__do_global_dtors_aux>:
    1840:	f3 0f 1e fa          	endbr64
    1844:	80 3d c5 27 00 00 00 	cmpb   $0x0,0x27c5(%rip)        # 4010 <__TMC_END__>
    184b:	75 2b                	jne    1878 <__do_global_dtors_aux+0x38>
    184d:	55                   	push   %rbp
    184e:	48 83 3d a2 27 00 00 00 	cmpq   $0x0,0x27a2(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1856:	48 89 e5             	mov    %rsp,%rbp
    1859:	74 0c                	je     1867 <__do_global_dtors_aux+0x27>
    185b:	48 8b 3d a6 27 00 00 	mov    0x27a6(%rip),%rdi        # 4008 <__dso_handle>
    1862:	e8 89 f8 ff ff       	call   10f0 <__cxa_finalize@plt>
    1867:	e8 64 ff ff ff       	call   17d0 <deregister_tm_clones>
    186c:	c6 05 9d 27 00 00 01 	movb   $0x1,0x279d(%rip)        # 4010 <__TMC_END__>
    1873:	5d                   	pop    %rbp
    1874:	c3                   	ret
    1875:	0f 1f 00             	nopl   (%rax)
    1878:	c3                   	ret
    1879:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001880 <frame_dummy>:
    1880:	f3 0f 1e fa          	endbr64
    1884:	e9 77 ff ff ff       	jmp    1800 <register_tm_clones>
    1889:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001890 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    1890:	f3 0f 1e fa          	endbr64
    1894:	41 56                	push   %r14
    1896:	41 55                	push   %r13
    1898:	41 54                	push   %r12
    189a:	55                   	push   %rbp
    189b:	53                   	push   %rbx
  if (data->mode == WRITER) {
    189c:	8b 87 84 01 00 00    	mov    0x184(%rdi),%eax
void * disruptor_thread(void * arg) {
    18a2:	48 89 fb             	mov    %rdi,%rbx
  if (data->mode == WRITER) {
    18a5:	85 c0                	test   %eax,%eax
    18a7:	0f 85 d3 00 00 00    	jne    1980 <disruptor_thread+0xf0>
    struct Thread *me = data->sender;
    18ad:	48 8b 6f 08          	mov    0x8(%rdi),%rbp
    while (data->running == 1) {
    18b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    18b8:	8b 83 90 01 00 00    	mov    0x190(%rbx),%eax
    18be:	83 f8 01             	cmp    $0x1,%eax
    18c1:	0f 85 c4 00 00 00    	jne    198b <disruptor_thread+0xfb>
      asm volatile ("sfence" ::: "memory");
    18c7:	0f ae f8             	sfence
      for (int x  = 0 ; x < data->other_count; x++) {
    18ca:	48 63 8b 08 02 00 00 	movslq 0x208(%rbx),%rcx
    18d1:	85 c9                	test   %ecx,%ecx
    18d3:	7e 3b                	jle    1910 <disruptor_thread+0x80>
        if ((me->realend + 1) % data->size == data->readers[x]->start) {
    18d5:	8b 85 80 01 00 00    	mov    0x180(%rbp),%eax
    18db:	83 c0 01             	add    $0x1,%eax
    18de:	48 98                	cltq
    18e0:	48 99                	cqto
    18e2:	48 f7 bb 88 01 00 00 	idivq  0x188(%rbx)
    18e9:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    18f0:	48 8d 34 c8          	lea    (%rax,%rcx,8),%rsi
    18f4:	0f 1f 40 00          	nopl   0x0(%rax)
    18f8:	48 8b 08             	mov    (%rax),%rcx
    18fb:	48 63 89 80 00 00 00 	movslq 0x80(%rcx),%rcx
    1902:	48 39 ca             	cmp    %rcx,%rdx
    1905:	74 b1                	je     18b8 <disruptor_thread+0x28>
      for (int x  = 0 ; x < data->other_count; x++) {
    1907:	48 83 c0 08          	add    $0x8,%rax
    190b:	48 39 f0             	cmp    %rsi,%rax
    190e:	75 e8                	jne    18f8 <disruptor_thread+0x68>
            if (changed = __atomic_add_fetch(&me->end, 1, __ATOMIC_ACQUIRE)) {
    1910:	b8 01 00 00 00       	mov    $0x1,%eax
    1915:	f0 0f c1 85 00 01 00 00 	lock xadd %eax,0x100(%rbp)
    191d:	83 c0 01             	add    $0x1,%eax
    1920:	74 96                	je     18b8 <disruptor_thread+0x28>
              changed = (changed) % me->size;
    1922:	48 98                	cltq
    1924:	48 99                	cqto
    1926:	48 f7 bd 88 01 00 00 	idivq  0x188(%rbp)
              for (int x = 0 ; x < data->other_count; x++) {
    192d:	8b 83 08 02 00 00    	mov    0x208(%rbx),%eax
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1933:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
              changed = (changed) % me->size;
    1937:	49 89 d4             	mov    %rdx,%r12
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    193a:	48 c1 e6 07          	shl    $0x7,%rsi
    193e:	48 03 75 18          	add    0x18(%rbp),%rsi
              for (int x = 0 ; x < data->other_count; x++) {
    1942:	85 c0                	test   %eax,%eax
    1944:	7e 1c                	jle    1962 <disruptor_thread+0xd2>
                me->data[changed].complete[x] = 0;
    1946:	48 8b 96 00 01 00 00 	mov    0x100(%rsi),%rdx
    194d:	31 c0                	xor    %eax,%eax
    194f:	c7 04 82 00 00 00 00 	movl   $0x0,(%rdx,%rax,4)
              for (int x = 0 ; x < data->other_count; x++) {
    1956:	48 83 c0 01          	add    $0x1,%rax
    195a:	39 83 08 02 00 00    	cmp    %eax,0x208(%rbx)
    1960:	7f ed                	jg     194f <disruptor_thread+0xbf>
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1962:	bf 04 00 00 00       	mov    $0x4,%edi
    1967:	e8 b4 f7 ff ff       	call   1120 <clock_gettime@plt>
              me->realend = changed;
    196c:	44 89 a5 80 01 00 00 	mov    %r12d,0x180(%rbp)
    1973:	e9 40 ff ff ff       	jmp    18b8 <disruptor_thread+0x28>
    1978:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  } else if (data->mode == READER) {
    1980:	8b 87 84 01 00 00    	mov    0x184(%rdi),%eax
    1986:	83 f8 01             	cmp    $0x1,%eax
    1989:	74 0b                	je     1996 <disruptor_thread+0x106>
}
    198b:	5b                   	pop    %rbx
    198c:	31 c0                	xor    %eax,%eax
    198e:	5d                   	pop    %rbp
    198f:	41 5c                	pop    %r12
    1991:	41 5d                	pop    %r13
    1993:	41 5e                	pop    %r14
    1995:	c3                   	ret
    struct Thread *sender = data->sender;
    1996:	48 8b 6f 08          	mov    0x8(%rdi),%rbp
    struct Snapshot * rdata = sender->data;
    199a:	4c 8b 6d 18          	mov    0x18(%rbp),%r13
    while (data->running == 1) {
    199e:	eb 1f                	jmp    19bf <disruptor_thread+0x12f>
      if ((sender->realend % sender->size) == data->start) {
    19a0:	48 63 85 80 01 00 00 	movslq 0x180(%rbp),%rax
    19a7:	44 8b a3 80 00 00 00 	mov    0x80(%rbx),%r12d
    19ae:	48 99                	cqto
    19b0:	48 f7 bd 88 01 00 00 	idivq  0x188(%rbp)
    19b7:	49 63 c4             	movslq %r12d,%rax
    19ba:	48 39 c2             	cmp    %rax,%rdx
    19bd:	75 0d                	jne    19cc <disruptor_thread+0x13c>
    while (data->running == 1) {
    19bf:	8b 83 90 01 00 00    	mov    0x190(%rbx),%eax
    19c5:	83 f8 01             	cmp    $0x1,%eax
    19c8:	74 d6                	je     19a0 <disruptor_thread+0x110>
    19ca:	eb bf                	jmp    198b <disruptor_thread+0xfb>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    19cc:	4c 8d 34 40          	lea    (%rax,%rax,2),%r14
    19d0:	48 63 b3 0c 02 00 00 	movslq 0x20c(%rbx),%rsi
    19d7:	bf 04 00 00 00       	mov    $0x4,%edi
    19dc:	49 c1 e6 07          	shl    $0x7,%r14
    19e0:	4d 01 ee             	add    %r13,%r14
    19e3:	48 c1 e6 04          	shl    $0x4,%rsi
    19e7:	49 03 b6 80 00 00 00 	add    0x80(%r14),%rsi
    19ee:	e8 2d f7 ff ff       	call   1120 <clock_gettime@plt>
              rdata[changed].complete[data->reader_index] = 1;
    19f3:	49 8b 86 00 01 00 00 	mov    0x100(%r14),%rax
    19fa:	48 63 93 0c 02 00 00 	movslq 0x20c(%rbx),%rdx
    1a01:	c7 04 90 01 00 00 00 	movl   $0x1,(%rax,%rdx,4)
              data->start = (changed + 1) % data->size;
    1a08:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    1a0d:	48 98                	cltq
    1a0f:	48 99                	cqto
    1a11:	48 f7 bb 88 01 00 00 	idivq  0x188(%rbx)
    1a18:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
    1a1e:	eb 9f                	jmp    19bf <disruptor_thread+0x12f>

0000000000001a20 <min>:
int min(long a, long b) {
    1a20:	f3 0f 1e fa          	endbr64
  if (a < b) return a;
    1a24:	48 39 f7             	cmp    %rsi,%rdi
    1a27:	7c 02                	jl     1a2b <min+0xb>
  if (b < a) return b;
    1a29:	7f 05                	jg     1a30 <min+0x10>
  if (a < b) return a;
    1a2b:	89 f8                	mov    %edi,%eax
    1a2d:	c3                   	ret
    1a2e:	66 90                	xchg   %ax,%ax
  if (b < a) return b;
    1a30:	89 f0                	mov    %esi,%eax
}
    1a32:	c3                   	ret

Disassembly of section .fini:

0000000000001a34 <_fini>:
    1a34:	f3 0f 1e fa          	endbr64
    1a38:	48 83 ec 08          	sub    $0x8,%rsp
    1a3c:	48 83 c4 08          	add    $0x8,%rsp
    1a40:	c3                   	ret
