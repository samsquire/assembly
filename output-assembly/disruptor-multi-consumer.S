
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
  printf("Readers count %d\n", other_count);
  int thread_count = groups * (other_count + writers_count);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    11cb:	45 31 ff             	xor    %r15d,%r15d
    11ce:	ba 14 00 00 00       	mov    $0x14,%edx
int main() {
    11d3:	41 56                	push   %r14
    11d5:	48 8d 35 54 0e 00 00 	lea    0xe54(%rip),%rsi        # 2030 <_IO_stdin_used+0x30>
    11dc:	bf 01 00 00 00       	mov    $0x1,%edi
    11e1:	41 55                	push   %r13
  // 0, 3, 6
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int receiver2 = receiver + 1; 
    for (int n = sender; n < sender + writers_count; n++) {
    11e3:	45 31 ed             	xor    %r13d,%r13d
int main() {
    11e6:	41 54                	push   %r12
    11e8:	55                   	push   %rbp
    11e9:	53                   	push   %rbx
    11ea:	44 89 fb             	mov    %r15d,%ebx
    11ed:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
    11f4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    11fd:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    1202:	31 c0                	xor    %eax,%eax
    1204:	e8 67 ff ff ff       	call   1170 <__printf_chk@plt>
    1209:	ba 01 00 00 00       	mov    $0x1,%edx
    120e:	48 8d 35 dd 0e 00 00 	lea    0xedd(%rip),%rsi        # 20f2 <_IO_stdin_used+0xf2>
    1215:	31 c0                	xor    %eax,%eax
    1217:	bf 01 00 00 00       	mov    $0x1,%edi
    121c:	e8 4f ff ff ff       	call   1170 <__printf_chk@plt>
    1221:	ba 02 00 00 00       	mov    $0x2,%edx
    1226:	48 8d 35 d5 0e 00 00 	lea    0xed5(%rip),%rsi        # 2102 <_IO_stdin_used+0x102>
    122d:	31 c0                	xor    %eax,%eax
    122f:	bf 01 00 00 00       	mov    $0x1,%edi
    1234:	e8 37 ff ff ff       	call   1170 <__printf_chk@plt>
    1239:	ba 04 00 00 00       	mov    $0x4,%edx
    123e:	48 8d 35 cf 0e 00 00 	lea    0xecf(%rip),%rsi        # 2114 <_IO_stdin_used+0x114>
    1245:	31 c0                	xor    %eax,%eax
    1247:	bf 01 00 00 00       	mov    $0x1,%edi
    124c:	e8 1f ff ff ff       	call   1170 <__printf_chk@plt>
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1251:	be 80 02 00 00       	mov    $0x280,%esi
    1256:	bf 04 00 00 00       	mov    $0x4,%edi
    125b:	e8 00 ff ff ff       	call   1160 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1260:	be 38 00 00 00       	mov    $0x38,%esi
    1265:	bf 04 00 00 00       	mov    $0x4,%edi
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    126a:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    126d:	e8 ee fe ff ff       	call   1160 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1272:	be 08 00 00 00       	mov    $0x8,%esi
    1277:	bf 04 00 00 00       	mov    $0x4,%edi
    127c:	4d 89 f4             	mov    %r14,%r12
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    127f:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1284:	e8 d7 fe ff ff       	call   1160 <calloc@plt>
    for (int n = sender; n < sender + writers_count; n++) {
    1289:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    128e:	be 80 00 00 00       	mov    $0x80,%esi
    1293:	bf 01 00 00 00       	mov    $0x1,%edi
      CPU_ZERO(sendercpu);
      CPU_SET(curcpu, sendercpu);
      curcpu += 2;
    1298:	44 8d 7b 02          	lea    0x2(%rbx),%r15d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    129c:	e8 bf fe ff ff       	call   1160 <calloc@plt>
      CPU_SET(curcpu, sendercpu);
    12a1:	89 d9                	mov    %ebx,%ecx
    12a3:	44 89 ea             	mov    %r13d,%edx
    12a6:	bf 01 00 00 00       	mov    $0x1,%edi
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12ab:	48 89 c5             	mov    %rax,%rbp
      CPU_SET(curcpu, sendercpu);
    12ae:	b8 01 00 00 00       	mov    $0x1,%eax
    12b3:	48 8d 35 9e 0d 00 00 	lea    0xd9e(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
    12ba:	48 d3 e0             	shl    %cl,%rax
    12bd:	48 09 45 00          	or     %rax,0x0(%rbp)
    12c1:	44 89 f9             	mov    %r15d,%ecx
    12c4:	31 c0                	xor    %eax,%eax
    12c6:	e8 a5 fe ff ff       	call   1170 <__printf_chk@plt>
      printf("assigning sender %d to core %d\n", n, curcpu);
       
      thread_data[n].thread_index = n;
    12cb:	45 89 2c 24          	mov    %r13d,(%r12)
      thread_data[n].mode = WRITER;
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    12cf:	be 08 00 00 00       	mov    $0x8,%esi
    12d4:	bf 02 00 00 00       	mov    $0x2,%edi
      thread_data[n].cpu_set = sendercpu;
    12d9:	49 89 ac 24 98 01 00 00 	mov    %rbp,0x198(%r12)
      thread_data[n].mode = WRITER;
    12e1:	41 c7 84 24 84 01 00 00 00 00 00 00 	movl   $0x0,0x184(%r12)
      thread_data[n].size = buffer_size;
    12ed:	49 c7 84 24 88 01 00 00 00 00 10 00 	movq   $0x100000,0x188(%r12)
      thread_data[n].running = 1;
    12f9:	41 c7 84 24 90 01 00 00 01 00 00 00 	movl   $0x1,0x190(%r12)
      thread_data[n].end = 0;
    1305:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
      thread_data[n].sender = &thread_data[sender];
    1311:	4d 89 74 24 08       	mov    %r14,0x8(%r12)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1316:	e8 45 fe ff ff       	call   1160 <calloc@plt>
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    131b:	be 80 01 00 00       	mov    $0x180,%esi
    1320:	bf 00 00 10 00       	mov    $0x100000,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1325:	49 89 84 24 00 02 00 00 	mov    %rax,0x200(%r12)
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    132d:	e8 2e fe ff ff       	call   1160 <calloc@plt>
    1332:	49 89 44 24 18       	mov    %rax,0x18(%r12)
      for (int k = 0 ; k < buffer_size ; k++) {
    1337:	48 8d 98 80 00 00 00 	lea    0x80(%rax),%rbx
    133e:	48 8d a8 80 00 00 18 	lea    0x18000080(%rax),%rbp
    1345:	0f 1f 00             	nopl   (%rax)
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1348:	be 04 00 00 00       	mov    $0x4,%esi
    134d:	bf 02 00 00 00       	mov    $0x2,%edi
      for (int k = 0 ; k < buffer_size ; k++) {
    1352:	48 81 c3 80 01 00 00 	add    $0x180,%rbx
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1359:	e8 02 fe ff ff       	call   1160 <calloc@plt>
        thread_data[n].data[k].end = calloc(other_count, sizeof(int));
    135e:	be 04 00 00 00       	mov    $0x4,%esi
    1363:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1368:	48 89 83 00 ff ff ff 	mov    %rax,-0x100(%rbx)
        thread_data[n].data[k].end = calloc(other_count, sizeof(int));
    136f:	e8 ec fd ff ff       	call   1160 <calloc@plt>
    1374:	48 89 83 80 fe ff ff 	mov    %rax,-0x180(%rbx)
      for (int k = 0 ; k < buffer_size ; k++) {
    137b:	48 39 dd             	cmp    %rbx,%rbp
    137e:	75 c8                	jne    1348 <main+0x188>
    for (int n = sender; n < sender + writers_count; n++) {
    1380:	41 83 c5 01          	add    $0x1,%r13d
    1384:	49 81 c4 80 02 00 00 	add    $0x280,%r12
    138b:	bb 02 00 00 00       	mov    $0x2,%ebx
      }
      thread_data[n].other_count = other_count;
    1390:	41 c7 44 24 88 02 00 00 00 	movl   $0x2,-0x78(%r12)
    for (int n = sender; n < sender + writers_count; n++) {
    1399:	41 83 ff 04          	cmp    $0x4,%r15d
    139d:	0f 85 eb fe ff ff    	jne    128e <main+0xce>
    13a3:	49 8d 86 00 05 00 00 	lea    0x500(%r14),%rax
    13aa:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    13af:	66 49 0f 6e d6       	movq   %r14,%xmm2
    13b4:	45 31 ed             	xor    %r13d,%r13d
    13b7:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    13bc:	66 0f 6c d2          	punpcklqdq %xmm2,%xmm2
    13c0:	49 89 c4             	mov    %rax,%r12
    13c3:	48 89 5c 24 38       	mov    %rbx,0x38(%rsp)
    13c8:	4c 89 f3             	mov    %r14,%rbx
    13cb:	4d 89 ee             	mov    %r13,%r14
    13ce:	0f 29 54 24 20       	movaps %xmm2,0x20(%rsp)
    13d3:	45 8d 6e 02          	lea    0x2(%r14),%r13d

    // printf("Created data for %d\n", sender);
    int seq[] = {1, 2, 5};
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      thread_data[j].thread_index = j;
      thread_data[j].reader_index = receiver_index;
    13d7:	45 89 b4 24 0c 02 00 00 	mov    %r14d,0x20c(%r12)
      thread_data[j].multiple = receiver_index % other_count;
      thread_data[j].other_count = other_count;
     
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    13df:	be 80 00 00 00       	mov    $0x80,%esi
    13e4:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].thread_index = j;
    13e9:	45 89 2c 24          	mov    %r13d,(%r12)
      thread_data[j].multiple = receiver_index % other_count;
    13ed:	45 89 b4 24 10 02 00 00 	mov    %r14d,0x210(%r12)
      thread_data[j].other_count = other_count;
    13f5:	41 c7 84 24 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%r12)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1401:	44 89 74 24 08       	mov    %r14d,0x8(%rsp)
    1406:	e8 55 fd ff ff       	call   1160 <calloc@plt>
      CPU_ZERO(receivercpu);
      CPU_SET(curcpu, receivercpu);
    140b:	44 89 f9             	mov    %r15d,%ecx
    140e:	44 89 ea             	mov    %r13d,%edx
    1411:	bf 01 00 00 00       	mov    $0x1,%edi
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1416:	48 89 c5             	mov    %rax,%rbp
      CPU_SET(curcpu, receivercpu);
    1419:	b8 01 00 00 00       	mov    $0x1,%eax
    141e:	48 8d 35 53 0c 00 00 	lea    0xc53(%rip),%rsi        # 2078 <_IO_stdin_used+0x78>
    1425:	48 d3 e0             	shl    %cl,%rax
    1428:	48 09 45 00          	or     %rax,0x0(%rbp)
      curcpu += 2;
    142c:	41 8d 47 02          	lea    0x2(%r15),%eax
    1430:	89 44 24 14          	mov    %eax,0x14(%rsp)
    1434:	89 c1                	mov    %eax,%ecx
    1436:	31 c0                	xor    %eax,%eax
    1438:	e8 33 fd ff ff       	call   1170 <__printf_chk@plt>
      printf("assigning receiver %d to core %d\n", j, curcpu);
      thread_data[j].cpu_set = receivercpu;
    143d:	49 89 ac 24 98 01 00 00 	mov    %rbp,0x198(%r12)
      thread_data[j].running = 1;
    1445:	41 c7 84 24 90 01 00 00 01 00 00 00 	movl   $0x1,0x190(%r12)
      thread_data[j].mode = READER;
    1451:	41 c7 84 24 84 01 00 00 01 00 00 00 	movl   $0x1,0x184(%r12)
      if (j == receiver) {
    145d:	41 83 fd 02          	cmp    $0x2,%r13d
    1461:	0f 84 6f 03 00 00    	je     17d6 <main+0x616>
        for (int n = 0 ; n < buffer_size ; n++) {
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
        }
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
    1467:	66 0f 6f 4c 24 20    	movdqa 0x20(%rsp),%xmm1
    146d:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    1471:	45 31 c0             	xor    %r8d,%r8d
    1474:	44 89 ea             	mov    %r13d,%edx
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    1477:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    147e:	48 8d 35 1b 0c 00 00 	lea    0xc1b(%rip),%rsi        # 20a0 <_IO_stdin_used+0xa0>
      thread_data[j].size = buffer_size;
    1485:	49 c7 84 24 88 01 00 00 00 00 10 00 	movq   $0x100000,0x188(%r12)
    1491:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].sender = &thread_data[sender];
    1496:	41 0f 11 4c 24 08    	movups %xmm1,0x8(%r12)
    149c:	41 bf 06 00 00 00    	mov    $0x6,%r15d
      thread_data[j].readers = thread_data[sender].readers;
    14a2:	49 89 84 24 00 02 00 00 	mov    %rax,0x200(%r12)
    14aa:	31 c0                	xor    %eax,%eax
      thread_data[j].start = 0;
    14ac:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
    14b8:	e8 b3 fc ff ff       	call   1170 <__printf_chk@plt>
      printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        thread_data[n].readers[receiver_index] = &thread_data[j];
    14bd:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    14c4:	4e 89 24 f0          	mov    %r12,(%rax,%r14,8)
    14c8:	48 8b 83 80 04 00 00 	mov    0x480(%rbx),%rax
    14cf:	4e 89 24 f0          	mov    %r12,(%rax,%r14,8)
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    14d3:	49 83 c6 01          	add    $0x1,%r14
    14d7:	49 81 c4 80 02 00 00 	add    $0x280,%r12
    14de:	83 7c 24 14 08       	cmpl   $0x8,0x14(%rsp)
    14e3:	0f 85 ea fe ff ff    	jne    13d3 <main+0x213>
    14e9:	4c 8d 3d 3b 0c 00 00 	lea    0xc3b(%rip),%r15        # 212b <_IO_stdin_used+0x12b>
    14f0:	31 d2                	xor    %edx,%edx
    14f2:	bf 01 00 00 00       	mov    $0x1,%edi
    14f7:	31 c0                	xor    %eax,%eax
    14f9:	4c 89 fe             	mov    %r15,%rsi
    14fc:	49 89 de             	mov    %rbx,%r14
    14ff:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    1504:	e8 67 fc ff ff       	call   1170 <__printf_chk@plt>
      }
    }
    curcpu = 0;
    printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    1509:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    150c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    1511:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    1516:	4c 8d 63 10          	lea    0x10(%rbx),%r12
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    151a:	41 bd 02 00 00 00    	mov    $0x2,%r13d
  param.sched_priority = 0;
    1520:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1528:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    152d:	48 8d 68 70          	lea    0x70(%rax),%rbp
    1531:	4c 89 fe             	mov    %r15,%rsi
    1534:	bf 01 00 00 00       	mov    $0x1,%edi
    1539:	31 c0                	xor    %eax,%eax
    153b:	44 89 ea             	mov    %r13d,%edx
    153e:	e8 2d fc ff ff       	call   1170 <__printf_chk@plt>
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    1543:	31 f6                	xor    %esi,%esi
    1545:	48 89 ef             	mov    %rbp,%rdi
    1548:	e8 03 fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    154d:	85 c0                	test   %eax,%eax
    154f:	0f 85 d2 02 00 00    	jne    1827 <main+0x667>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    1555:	48 8d 74 24 4c       	lea    0x4c(%rsp),%rsi
    155a:	48 89 ef             	mov    %rbp,%rdi
    155d:	e8 2e fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1562:	85 c0                	test   %eax,%eax
    1564:	0f 85 d8 02 00 00    	jne    1842 <main+0x682>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    156a:	4c 89 f1             	mov    %r14,%rcx
    156d:	48 89 ee             	mov    %rbp,%rsi
    1570:	4c 89 e7             	mov    %r12,%rdi
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1573:	48 83 c5 38          	add    $0x38,%rbp
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1577:	48 8d 15 d2 03 00 00 	lea    0x3d2(%rip),%rdx        # 1950 <disruptor_thread>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    157e:	49 83 c4 08          	add    $0x8,%r12
    1582:	49 81 c6 80 02 00 00 	add    $0x280,%r14
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1589:	e8 f2 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    158e:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
    1593:	be 08 00 00 00       	mov    $0x8,%esi
    1598:	49 8b 96 18 ff ff ff 	mov    -0xe8(%r14),%rdx
    159f:	e8 5c fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15a4:	41 83 fd 02          	cmp    $0x2,%r13d
    15a8:	75 0b                	jne    15b5 <main+0x3f5>
    15aa:	41 bd 03 00 00 00    	mov    $0x3,%r13d
    15b0:	e9 7c ff ff ff       	jmp    1531 <main+0x371>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    15b5:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
    15ba:	31 f6                	xor    %esi,%esi
    15bc:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    15c1:	4c 89 ff             	mov    %r15,%rdi
    15c4:	e8 87 fb ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    15c9:	85 c0                	test   %eax,%eax
    15cb:	0f 85 56 02 00 00    	jne    1827 <main+0x667>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    15d1:	48 8d 74 24 48       	lea    0x48(%rsp),%rsi
    15d6:	4c 89 ff             	mov    %r15,%rdi
      param2.sched_priority = 0;
    15d9:	c7 44 24 48 00 00 00 00 	movl   $0x0,0x48(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    15e1:	e8 aa fb ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    15e6:	85 c0                	test   %eax,%eax
    15e8:	0f 85 54 02 00 00    	jne    1842 <main+0x682>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    15ee:	4c 89 f1             	mov    %r14,%rcx
    15f1:	48 89 df             	mov    %rbx,%rdi
    15f4:	48 8d 15 55 03 00 00 	lea    0x355(%rip),%rdx        # 1950 <disruptor_thread>
    15fb:	4c 89 fe             	mov    %r15,%rsi
    15fe:	e8 7d fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    1603:	48 8b 3b             	mov    (%rbx),%rdi
    1606:	be 08 00 00 00       	mov    $0x8,%esi
    void * res1;
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    160b:	31 ed                	xor    %ebp,%ebp
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    160d:	49 8b 96 98 01 00 00 	mov    0x198(%r14),%rdx
    1614:	e8 e7 fa ff ff       	call   1100 <pthread_setaffinity_np@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    1619:	4c 89 fe             	mov    %r15,%rsi
    161c:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    1620:	49 8d 8e 80 02 00 00 	lea    0x280(%r14),%rcx
    1627:	48 83 c6 38          	add    $0x38,%rsi
    162b:	48 8d 15 1e 03 00 00 	lea    0x31e(%rip),%rdx        # 1950 <disruptor_thread>
    1632:	e8 49 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    1637:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    163b:	be 08 00 00 00       	mov    $0x8,%esi
    1640:	49 8b 96 18 04 00 00 	mov    0x418(%r14),%rdx
    1647:	e8 b4 fa ff ff       	call   1100 <pthread_setaffinity_np@plt>
  struct timespec preempt = {
    164c:	66 0f 6f 05 8c 0b 00 00 	movdqa 0xb8c(%rip),%xmm0        # 21e0 <_IO_stdin_used+0x1e0>
    1654:	ba 0a 00 00 00       	mov    $0xa,%edx
    1659:	31 c0                	xor    %eax,%eax
    165b:	48 8d 35 21 0b 00 00 	lea    0xb21(%rip),%rsi        # 2183 <_IO_stdin_used+0x183>
    1662:	bf 01 00 00 00       	mov    $0x1,%edi
    1667:	0f 29 44 24 60       	movaps %xmm0,0x60(%rsp)
    166c:	e8 ff fa ff ff       	call   1170 <__printf_chk@plt>
  nanosleep(&preempt , &rem2);
    1671:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
    1676:	48 8d 7c 24 60       	lea    0x60(%rsp),%rdi
    167b:	e8 c0 fa ff ff       	call   1140 <nanosleep@plt>
      pthread_join(thread[n], res1);
    1680:	48 8b 3b             	mov    (%rbx),%rdi
    1683:	48 89 ee             	mov    %rbp,%rsi
    thread_data[sender].running = 0;
    1686:	41 c7 86 90 01 00 00 00 00 00 00 	movl   $0x0,0x190(%r14)
      thread_data[j].running = 0;
    1691:	41 c7 86 90 06 00 00 00 00 00 00 	movl   $0x0,0x690(%r14)
    169c:	41 c7 86 10 09 00 00 00 00 00 00 	movl   $0x0,0x910(%r14)
      thread_data[n].running = 0;
    16a7:	41 c7 86 90 01 00 00 00 00 00 00 	movl   $0x0,0x190(%r14)
    16b2:	41 c7 86 10 04 00 00 00 00 00 00 	movl   $0x0,0x410(%r14)
      pthread_join(thread[n], res1);
    16bd:	e8 ee fa ff ff       	call   11b0 <pthread_join@plt>
    16c2:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    16c6:	48 89 ee             	mov    %rbp,%rsi
    16c9:	e8 e2 fa ff ff       	call   11b0 <pthread_join@plt>
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    16ce:	48 8b 7b 10          	mov    0x10(%rbx),%rdi
    16d2:	48 89 ee             	mov    %rbp,%rsi
    16d5:	e8 d6 fa ff ff       	call   11b0 <pthread_join@plt>
    16da:	48 8b 7b 18          	mov    0x18(%rbx),%rdi
    16de:	48 89 ee             	mov    %rbp,%rsi
    16e1:	31 db                	xor    %ebx,%ebx
    16e3:	48 8d 2d c8 0a 00 00 	lea    0xac8(%rip),%rbp        # 21b2 <_IO_stdin_used+0x1b2>
    16ea:	e8 c1 fa ff ff       	call   11b0 <pthread_join@plt>
    16ef:	ba 02 00 00 00       	mov    $0x2,%edx
    16f4:	48 8d 35 a1 0a 00 00 	lea    0xaa1(%rip),%rsi        # 219c <_IO_stdin_used+0x19c>
    16fb:	31 c0                	xor    %eax,%eax
    16fd:	bf 01 00 00 00       	mov    $0x1,%edi
    1702:	e8 69 fa ff ff       	call   1170 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    1707:	eb 17                	jmp    1720 <main+0x560>
    1709:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1710:	48 81 c3 80 01 00 00 	add    $0x180,%rbx
    1717:	48 81 fb 00 00 00 18 	cmp    $0x18000000,%rbx
    171e:	74 7d                	je     179d <main+0x5dd>
      int compcount = 0;
      for (int n = 0 ; n < 2 ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    1720:	49 8b 46 18          	mov    0x18(%r14),%rax
    1724:	48 01 d8             	add    %rbx,%rax
    1727:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
    172e:	83 3a 01             	cmpl   $0x1,(%rdx)
    1731:	75 dd                	jne    1710 <main+0x550>
    1733:	83 7a 04 01          	cmpl   $0x1,0x4(%rdx)
    1737:	75 d7                	jne    1710 <main+0x550>
      // printf("%d\n", compcount);
      if (compcount == other_count) {
      for (int n = 0 ; n < other_count ; n++) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
          struct timespec end = thread_data[sender].data[y].end[n];
    1739:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    1740:	48 89 ee             	mov    %rbp,%rsi
    1743:	bf 01 00 00 00       	mov    $0x1,%edi
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    1748:	4c 8b 42 08          	mov    0x8(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    174c:	48 8b 0a             	mov    (%rdx),%rcx
    174f:	31 d2                	xor    %edx,%edx
    1751:	48 2b 08             	sub    (%rax),%rcx
    1754:	4c 2b 40 08          	sub    0x8(%rax),%r8
    1758:	31 c0                	xor    %eax,%eax
    175a:	e8 11 fa ff ff       	call   1170 <__printf_chk@plt>
          struct timespec start = thread_data[sender].data[y].start;
    175f:	49 8b 46 18          	mov    0x18(%r14),%rax
    1763:	48 89 ee             	mov    %rbp,%rsi
    1766:	bf 01 00 00 00       	mov    $0x1,%edi
    176b:	48 01 d8             	add    %rbx,%rax
    for (int y = 0 ; y < buffer_size; y++) {
    176e:	48 81 c3 80 01 00 00 	add    $0x180,%rbx
          struct timespec end = thread_data[sender].data[y].end[n];
    1775:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    177c:	4c 8b 42 18          	mov    0x18(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    1780:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    1784:	31 d2                	xor    %edx,%edx
    1786:	48 2b 08             	sub    (%rax),%rcx
    1789:	4c 2b 40 08          	sub    0x8(%rax),%r8
    178d:	31 c0                	xor    %eax,%eax
    178f:	e8 dc f9 ff ff       	call   1170 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    1794:	48 81 fb 00 00 00 18 	cmp    $0x18000000,%rbx
    179b:	75 83                	jne    1720 <main+0x560>
    179d:	31 d2                	xor    %edx,%edx
    179f:	31 c0                	xor    %eax,%eax
    17a1:	48 8d 35 1e 0a 00 00 	lea    0xa1e(%rip),%rsi        # 21c6 <_IO_stdin_used+0x1c6>
    17a8:	bf 01 00 00 00       	mov    $0x1,%edi
    17ad:	e8 be f9 ff ff       	call   1170 <__printf_chk@plt>
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    17b2:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    17b7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    17c0:	75 7b                	jne    183d <main+0x67d>
    17c2:	48 81 c4 88 00 00 00 	add    $0x88,%rsp
    17c9:	31 c0                	xor    %eax,%eax
    17cb:	5b                   	pop    %rbx
    17cc:	5d                   	pop    %rbp
    17cd:	41 5c                	pop    %r12
    17cf:	41 5d                	pop    %r13
    17d1:	41 5e                	pop    %r14
    17d3:	41 5f                	pop    %r15
    17d5:	c3                   	ret
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    17d6:	be 80 01 00 00       	mov    $0x180,%esi
    17db:	bf 00 00 10 00       	mov    $0x100000,%edi
    17e0:	e8 7b f9 ff ff       	call   1160 <calloc@plt>
    17e5:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    17ea:	49 89 c7             	mov    %rax,%r15
        for (int n = 0 ; n < buffer_size ; n++) {
    17ed:	48 8d a8 00 01 00 00 	lea    0x100(%rax),%rbp
    17f4:	49 81 c7 00 01 00 18 	add    $0x18000100,%r15
    17fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1800:	be 04 00 00 00       	mov    $0x4,%esi
    1805:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    180a:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1811:	e8 4a f9 ff ff       	call   1160 <calloc@plt>
    1816:	48 89 85 80 fe ff ff 	mov    %rax,-0x180(%rbp)
        for (int n = 0 ; n < buffer_size ; n++) {
    181d:	49 39 ef             	cmp    %rbp,%r15
    1820:	75 de                	jne    1800 <main+0x640>
    1822:	e9 40 fc ff ff       	jmp    1467 <main+0x2a7>
    1827:	48 8d 3d 1a 09 00 00 	lea    0x91a(%rip),%rdi        # 2148 <_IO_stdin_used+0x148>
    182e:	e8 dd f8 ff ff       	call   1110 <puts@plt>
               exit(1);
    1833:	bf 01 00 00 00       	mov    $0x1,%edi
    1838:	e8 63 f9 ff ff       	call   11a0 <exit@plt>
}
    183d:	e8 ee f8 ff ff       	call   1130 <__stack_chk_fail@plt>
    1842:	48 8d 3d 1d 09 00 00 	lea    0x91d(%rip),%rdi        # 2166 <_IO_stdin_used+0x166>
    1849:	e8 c2 f8 ff ff       	call   1110 <puts@plt>
              exit(1);
    184e:	bf 01 00 00 00       	mov    $0x1,%edi
    1853:	e8 48 f9 ff ff       	call   11a0 <exit@plt>
    1858:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000001860 <_start>:
    1860:	f3 0f 1e fa          	endbr64
    1864:	31 ed                	xor    %ebp,%ebp
    1866:	49 89 d1             	mov    %rdx,%r9
    1869:	5e                   	pop    %rsi
    186a:	48 89 e2             	mov    %rsp,%rdx
    186d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1871:	50                   	push   %rax
    1872:	54                   	push   %rsp
    1873:	45 31 c0             	xor    %r8d,%r8d
    1876:	31 c9                	xor    %ecx,%ecx
    1878:	48 8d 3d 41 f9 ff ff 	lea    -0x6bf(%rip),%rdi        # 11c0 <main>
    187f:	ff 15 53 27 00 00    	call   *0x2753(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1885:	f4                   	hlt
    1886:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001890 <deregister_tm_clones>:
    1890:	48 8d 3d 79 27 00 00 	lea    0x2779(%rip),%rdi        # 4010 <__TMC_END__>
    1897:	48 8d 05 72 27 00 00 	lea    0x2772(%rip),%rax        # 4010 <__TMC_END__>
    189e:	48 39 f8             	cmp    %rdi,%rax
    18a1:	74 15                	je     18b8 <deregister_tm_clones+0x28>
    18a3:	48 8b 05 36 27 00 00 	mov    0x2736(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    18aa:	48 85 c0             	test   %rax,%rax
    18ad:	74 09                	je     18b8 <deregister_tm_clones+0x28>
    18af:	ff e0                	jmp    *%rax
    18b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    18b8:	c3                   	ret
    18b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018c0 <register_tm_clones>:
    18c0:	48 8d 3d 49 27 00 00 	lea    0x2749(%rip),%rdi        # 4010 <__TMC_END__>
    18c7:	48 8d 35 42 27 00 00 	lea    0x2742(%rip),%rsi        # 4010 <__TMC_END__>
    18ce:	48 29 fe             	sub    %rdi,%rsi
    18d1:	48 89 f0             	mov    %rsi,%rax
    18d4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    18d8:	48 c1 f8 03          	sar    $0x3,%rax
    18dc:	48 01 c6             	add    %rax,%rsi
    18df:	48 d1 fe             	sar    %rsi
    18e2:	74 14                	je     18f8 <register_tm_clones+0x38>
    18e4:	48 8b 05 05 27 00 00 	mov    0x2705(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    18eb:	48 85 c0             	test   %rax,%rax
    18ee:	74 08                	je     18f8 <register_tm_clones+0x38>
    18f0:	ff e0                	jmp    *%rax
    18f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    18f8:	c3                   	ret
    18f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001900 <__do_global_dtors_aux>:
    1900:	f3 0f 1e fa          	endbr64
    1904:	80 3d 05 27 00 00 00 	cmpb   $0x0,0x2705(%rip)        # 4010 <__TMC_END__>
    190b:	75 2b                	jne    1938 <__do_global_dtors_aux+0x38>
    190d:	55                   	push   %rbp
    190e:	48 83 3d e2 26 00 00 00 	cmpq   $0x0,0x26e2(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1916:	48 89 e5             	mov    %rsp,%rbp
    1919:	74 0c                	je     1927 <__do_global_dtors_aux+0x27>
    191b:	48 8b 3d e6 26 00 00 	mov    0x26e6(%rip),%rdi        # 4008 <__dso_handle>
    1922:	e8 c9 f7 ff ff       	call   10f0 <__cxa_finalize@plt>
    1927:	e8 64 ff ff ff       	call   1890 <deregister_tm_clones>
    192c:	c6 05 dd 26 00 00 01 	movb   $0x1,0x26dd(%rip)        # 4010 <__TMC_END__>
    1933:	5d                   	pop    %rbp
    1934:	c3                   	ret
    1935:	0f 1f 00             	nopl   (%rax)
    1938:	c3                   	ret
    1939:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001940 <frame_dummy>:
    1940:	f3 0f 1e fa          	endbr64
    1944:	e9 77 ff ff ff       	jmp    18c0 <register_tm_clones>
    1949:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001950 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    1950:	f3 0f 1e fa          	endbr64
    1954:	41 56                	push   %r14
    1956:	48 8d 35 ab 06 00 00 	lea    0x6ab(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    195d:	31 c0                	xor    %eax,%eax
    195f:	41 55                	push   %r13
    1961:	41 54                	push   %r12
    1963:	55                   	push   %rbp
    1964:	53                   	push   %rbx
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    1965:	8b 8f 84 01 00 00    	mov    0x184(%rdi),%ecx
void * disruptor_thread(void * arg) {
    196b:	48 89 fb             	mov    %rdi,%rbx
    196e:	8b 17                	mov    (%rdi),%edx
    1970:	bf 01 00 00 00       	mov    $0x1,%edi
    1975:	e8 f6 f7 ff ff       	call   1170 <__printf_chk@plt>
  if (data->mode == WRITER) {
    197a:	8b 83 84 01 00 00    	mov    0x184(%rbx),%eax
    1980:	85 c0                	test   %eax,%eax
    1982:	74 33                	je     19b7 <disruptor_thread+0x67>
  } else if (data->mode == READER) {
    1984:	8b 83 84 01 00 00    	mov    0x184(%rbx),%eax
    198a:	83 f8 01             	cmp    $0x1,%eax
    198d:	0f 84 00 01 00 00    	je     1a93 <disruptor_thread+0x143>
  printf("Finished %d\n", data->mode);
    1993:	8b 93 84 01 00 00    	mov    0x184(%rbx),%edx
    1999:	48 8d 35 39 07 00 00 	lea    0x739(%rip),%rsi        # 20d9 <_IO_stdin_used+0xd9>
    19a0:	bf 01 00 00 00       	mov    $0x1,%edi
    19a5:	31 c0                	xor    %eax,%eax
    19a7:	e8 c4 f7 ff ff       	call   1170 <__printf_chk@plt>
}
    19ac:	5b                   	pop    %rbx
    19ad:	31 c0                	xor    %eax,%eax
    19af:	5d                   	pop    %rbp
    19b0:	41 5c                	pop    %r12
    19b2:	41 5d                	pop    %r13
    19b4:	41 5e                	pop    %r14
    19b6:	c3                   	ret
    19b7:	48 8d 3d 0f 07 00 00 	lea    0x70f(%rip),%rdi        # 20cd <_IO_stdin_used+0xcd>
    19be:	e8 4d f7 ff ff       	call   1110 <puts@plt>
    struct Thread *me = data->sender;
    19c3:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    while (data->running == 1) {
    19c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    19d0:	8b 83 90 01 00 00    	mov    0x190(%rbx),%eax
    19d6:	83 f8 01             	cmp    $0x1,%eax
    19d9:	75 b8                	jne    1993 <disruptor_thread+0x43>
      asm volatile ("sfence" ::: "memory");
    19db:	0f ae f8             	sfence
      for (int x  = 0 ; x < data->other_count; x++) {
    19de:	48 63 8b 08 02 00 00 	movslq 0x208(%rbx),%rcx
    19e5:	85 c9                	test   %ecx,%ecx
    19e7:	7e 3f                	jle    1a28 <disruptor_thread+0xd8>
        if ((me->realend + 1) % data->size == data->readers[x]->start) {
    19e9:	8b 85 80 01 00 00    	mov    0x180(%rbp),%eax
    19ef:	83 c0 01             	add    $0x1,%eax
    19f2:	48 98                	cltq
    19f4:	48 99                	cqto
    19f6:	48 f7 bb 88 01 00 00 	idivq  0x188(%rbx)
    19fd:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    1a04:	48 8d 34 c8          	lea    (%rax,%rcx,8),%rsi
    1a08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    1a10:	48 8b 08             	mov    (%rax),%rcx
    1a13:	48 63 89 80 00 00 00 	movslq 0x80(%rcx),%rcx
    1a1a:	48 39 ca             	cmp    %rcx,%rdx
    1a1d:	74 b1                	je     19d0 <disruptor_thread+0x80>
      for (int x  = 0 ; x < data->other_count; x++) {
    1a1f:	48 83 c0 08          	add    $0x8,%rax
    1a23:	48 39 c6             	cmp    %rax,%rsi
    1a26:	75 e8                	jne    1a10 <disruptor_thread+0xc0>
            if (changed = __atomic_add_fetch(&me->end, 1, __ATOMIC_RELAXED)) {
    1a28:	b8 01 00 00 00       	mov    $0x1,%eax
    1a2d:	f0 0f c1 85 00 01 00 00 	lock xadd %eax,0x100(%rbp)
    1a35:	83 c0 01             	add    $0x1,%eax
    1a38:	74 96                	je     19d0 <disruptor_thread+0x80>
              changed = (changed - 1) % me->size;
    1a3a:	83 e8 01             	sub    $0x1,%eax
    1a3d:	48 98                	cltq
    1a3f:	48 99                	cqto
    1a41:	48 f7 bd 88 01 00 00 	idivq  0x188(%rbp)
              for (int x = 0 ; x < data->other_count; x++) {
    1a48:	8b 83 08 02 00 00    	mov    0x208(%rbx),%eax
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1a4e:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
              changed = (changed - 1) % me->size;
    1a52:	49 89 d4             	mov    %rdx,%r12
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1a55:	48 c1 e6 07          	shl    $0x7,%rsi
    1a59:	48 03 75 18          	add    0x18(%rbp),%rsi
              for (int x = 0 ; x < data->other_count; x++) {
    1a5d:	85 c0                	test   %eax,%eax
    1a5f:	7e 1c                	jle    1a7d <disruptor_thread+0x12d>
                me->data[changed].complete[x] = 0;
    1a61:	48 8b 96 00 01 00 00 	mov    0x100(%rsi),%rdx
    1a68:	31 c0                	xor    %eax,%eax
    1a6a:	c7 04 82 00 00 00 00 	movl   $0x0,(%rdx,%rax,4)
              for (int x = 0 ; x < data->other_count; x++) {
    1a71:	48 83 c0 01          	add    $0x1,%rax
    1a75:	39 83 08 02 00 00    	cmp    %eax,0x208(%rbx)
    1a7b:	7f ed                	jg     1a6a <disruptor_thread+0x11a>
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1a7d:	bf 04 00 00 00       	mov    $0x4,%edi
    1a82:	e8 99 f6 ff ff       	call   1120 <clock_gettime@plt>
              me->realend = changed;
    1a87:	44 89 a5 80 01 00 00 	mov    %r12d,0x180(%rbp)
    1a8e:	e9 3d ff ff ff       	jmp    19d0 <disruptor_thread+0x80>
    1a93:	48 8d 3d 4c 06 00 00 	lea    0x64c(%rip),%rdi        # 20e6 <_IO_stdin_used+0xe6>
    1a9a:	e8 71 f6 ff ff       	call   1110 <puts@plt>
    struct Thread *sender = data->sender;
    1a9f:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    struct Snapshot * rdata = sender->data;
    1aa3:	4c 8b 6d 18          	mov    0x18(%rbp),%r13
    while (data->running == 1) {
    1aa7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    1ab0:	8b 83 90 01 00 00    	mov    0x190(%rbx),%eax
    1ab6:	83 f8 01             	cmp    $0x1,%eax
    1ab9:	0f 85 d4 fe ff ff    	jne    1993 <disruptor_thread+0x43>
      if ((sender->realend % sender->size) == data->start) {
    1abf:	48 63 85 80 01 00 00 	movslq 0x180(%rbp),%rax
    1ac6:	44 8b a3 80 00 00 00 	mov    0x80(%rbx),%r12d
    1acd:	48 99                	cqto
    1acf:	48 f7 bd 88 01 00 00 	idivq  0x188(%rbp)
    1ad6:	49 63 c4             	movslq %r12d,%rax
    1ad9:	48 39 c2             	cmp    %rax,%rdx
    1adc:	74 d2                	je     1ab0 <disruptor_thread+0x160>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1ade:	4c 8d 34 40          	lea    (%rax,%rax,2),%r14
    1ae2:	48 63 b3 0c 02 00 00 	movslq 0x20c(%rbx),%rsi
    1ae9:	bf 04 00 00 00       	mov    $0x4,%edi
    1aee:	49 c1 e6 07          	shl    $0x7,%r14
    1af2:	4d 01 ee             	add    %r13,%r14
    1af5:	48 c1 e6 04          	shl    $0x4,%rsi
    1af9:	49 03 b6 80 00 00 00 	add    0x80(%r14),%rsi
    1b00:	e8 1b f6 ff ff       	call   1120 <clock_gettime@plt>
              rdata[changed].complete[data->reader_index] = 1;
    1b05:	49 8b 86 00 01 00 00 	mov    0x100(%r14),%rax
    1b0c:	48 63 93 0c 02 00 00 	movslq 0x20c(%rbx),%rdx
    1b13:	c7 04 90 01 00 00 00 	movl   $0x1,(%rax,%rdx,4)
              data->start = (changed + 1) % data->size;
    1b1a:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    1b1f:	48 98                	cltq
    1b21:	48 99                	cqto
    1b23:	48 f7 bb 88 01 00 00 	idivq  0x188(%rbx)
    1b2a:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
    1b30:	e9 7b ff ff ff       	jmp    1ab0 <disruptor_thread+0x160>
    1b35:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000001b40 <min>:
int min(long a, long b) {
    1b40:	f3 0f 1e fa          	endbr64
  if (a < b) return a;
    1b44:	48 39 f7             	cmp    %rsi,%rdi
    1b47:	7c 02                	jl     1b4b <min+0xb>
  if (b < a) return b;
    1b49:	7f 05                	jg     1b50 <min+0x10>
  if (a < b) return a;
    1b4b:	89 f8                	mov    %edi,%eax
    1b4d:	c3                   	ret
    1b4e:	66 90                	xchg   %ax,%ax
  if (b < a) return b;
    1b50:	89 f0                	mov    %esi,%eax
}
    1b52:	c3                   	ret

Disassembly of section .fini:

0000000000001b54 <_fini>:
    1b54:	f3 0f 1e fa          	endbr64
    1b58:	48 83 ec 08          	sub    $0x8,%rsp
    1b5c:	48 83 c4 08          	add    $0x8,%rsp
    1b60:	c3                   	ret
