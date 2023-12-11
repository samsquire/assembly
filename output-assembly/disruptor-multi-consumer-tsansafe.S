
disruptor-multi-consumer-tsansafe:     file format elf64-x86-64


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
    11cb:	ba 0f 00 00 00       	mov    $0xf,%edx
    11d0:	48 8d 35 31 0e 00 00 	lea    0xe31(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    11d7:	41 56                	push   %r14
    11d9:	bf 01 00 00 00       	mov    $0x1,%edi
    11de:	41 55                	push   %r13
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int receiver2 = receiver + 1; 
    int seq[] = {1, 2, 5};
    int tag_index[] = {1, 5, 7};
    11e0:	45 31 ed             	xor    %r13d,%r13d
int main() {
    11e3:	41 54                	push   %r12
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    11e5:	45 31 e4             	xor    %r12d,%r12d
int main() {
    11e8:	55                   	push   %rbp
    11e9:	53                   	push   %rbx
    11ea:	48 81 ec 98 00 00 00 	sub    $0x98,%rsp
    11f1:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    11fa:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    1202:	31 c0                	xor    %eax,%eax
    1204:	e8 67 ff ff ff       	call   1170 <__printf_chk@plt>
    1209:	ba 01 00 00 00       	mov    $0x1,%edx
    120e:	48 8d 35 84 0e 00 00 	lea    0xe84(%rip),%rsi        # 2099 <_IO_stdin_used+0x99>
    1215:	31 c0                	xor    %eax,%eax
    1217:	bf 01 00 00 00       	mov    $0x1,%edi
    121c:	e8 4f ff ff ff       	call   1170 <__printf_chk@plt>
    1221:	ba 02 00 00 00       	mov    $0x2,%edx
    1226:	48 8d 35 7c 0e 00 00 	lea    0xe7c(%rip),%rsi        # 20a9 <_IO_stdin_used+0xa9>
    122d:	31 c0                	xor    %eax,%eax
    122f:	bf 01 00 00 00       	mov    $0x1,%edi
    1234:	e8 37 ff ff ff       	call   1170 <__printf_chk@plt>
    1239:	ba 02 00 00 00       	mov    $0x2,%edx
    123e:	48 8d 35 76 0e 00 00 	lea    0xe76(%rip),%rsi        # 20bb <_IO_stdin_used+0xbb>
    1245:	31 c0                	xor    %eax,%eax
    1247:	bf 01 00 00 00       	mov    $0x1,%edi
    124c:	e8 1f ff ff ff       	call   1170 <__printf_chk@plt>
    1251:	ba 04 00 00 00       	mov    $0x4,%edx
    1256:	48 8d 35 70 0e 00 00 	lea    0xe70(%rip),%rsi        # 20cd <_IO_stdin_used+0xcd>
    125d:	31 c0                	xor    %eax,%eax
    125f:	bf 01 00 00 00       	mov    $0x1,%edi
    1264:	e8 07 ff ff ff       	call   1170 <__printf_chk@plt>
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1269:	be 80 02 00 00       	mov    $0x280,%esi
    126e:	bf 04 00 00 00       	mov    $0x4,%edi
    1273:	e8 e8 fe ff ff       	call   1160 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1278:	be 38 00 00 00       	mov    $0x38,%esi
    127d:	bf 04 00 00 00       	mov    $0x4,%edi
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1282:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1285:	e8 d6 fe ff ff       	call   1160 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    128a:	be 08 00 00 00       	mov    $0x8,%esi
    128f:	bf 04 00 00 00       	mov    $0x4,%edi
    1294:	4c 89 f5             	mov    %r14,%rbp
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1297:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    129c:	e8 bf fe ff ff       	call   1160 <calloc@plt>
    12a1:	48 89 c3             	mov    %rax,%rbx
    int seq[] = {1, 2, 5};
    12a4:	48 8b 05 8d 0e 00 00 	mov    0xe8d(%rip),%rax        # 2138 <_IO_stdin_used+0x138>
    12ab:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    12b0:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    int tag_index[] = {1, 5, 7};
    12b5:	48 8b 05 84 0e 00 00 	mov    0xe84(%rip),%rax        # 2140 <_IO_stdin_used+0x140>
    12bc:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    12c1:	48 8d 44 24 68       	lea    0x68(%rsp),%rax
    12c6:	48 89 04 24          	mov    %rax,(%rsp)
    12ca:	48 8d 44 24 78       	lea    0x78(%rsp),%rax
    12cf:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12d4:	be 80 00 00 00       	mov    $0x80,%esi
    12d9:	bf 01 00 00 00       	mov    $0x1,%edi
    12de:	43 8d 1c 24          	lea    (%r12,%r12,1),%ebx
    12e2:	e8 79 fe ff ff       	call   1160 <calloc@plt>
      CPU_ZERO(sendercpu);
      CPU_SET(curcpu, sendercpu);
    12e7:	89 d9                	mov    %ebx,%ecx
    12e9:	44 89 e2             	mov    %r12d,%edx
    12ec:	bf 01 00 00 00       	mov    $0x1,%edi
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12f1:	49 89 c7             	mov    %rax,%r15
      CPU_SET(curcpu, sendercpu);
    12f4:	b8 01 00 00 00       	mov    $0x1,%eax
    12f9:	48 8d 35 30 0d 00 00 	lea    0xd30(%rip),%rsi        # 2030 <_IO_stdin_used+0x30>
    1300:	48 d3 e0             	shl    %cl,%rax
    1303:	49 09 07             	or     %rax,(%r15)
    1306:	89 d9                	mov    %ebx,%ecx
    1308:	31 c0                	xor    %eax,%eax
    130a:	e8 61 fe ff ff       	call   1170 <__printf_chk@plt>
      curcpu += coreinterval;
       
      thread_data[n].thread_index = n;
      thread_data[n].cpu_set = sendercpu;
      thread_data[n].mode = WRITER;
      thread_data[n].multiple = seq[sender_index % writers_count];
    130f:	48 8b 04 24          	mov    (%rsp),%rax
      thread_data[n].cpu_set = sendercpu;
    1313:	4c 89 bd a0 01 00 00 	mov    %r15,0x1a0(%rbp)
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].thread_tag = tag_index[sender_index];
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    131a:	be 08 00 00 00       	mov    $0x8,%esi
      thread_data[n].mode = WRITER;
    131f:	c7 85 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rbp)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1329:	bf 02 00 00 00       	mov    $0x2,%edi
      thread_data[n].multiple = seq[sender_index % writers_count];
    132e:	42 8b 04 28          	mov    (%rax,%r13,1),%eax
      thread_data[n].thread_index = n;
    1332:	44 89 65 00          	mov    %r12d,0x0(%rbp)
      thread_data[n].running = 1;
    1336:	c7 85 98 01 00 00 01 00 00 00 	movl   $0x1,0x198(%rbp)
      thread_data[n].multiple = seq[sender_index % writers_count];
    1340:	89 85 10 02 00 00    	mov    %eax,0x210(%rbp)
      thread_data[n].thread_tag = tag_index[sender_index];
    1346:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
      thread_data[n].size = buffer_size;
    134b:	48 c7 85 90 01 00 00 00 80 00 00 	movq   $0x8000,0x190(%rbp)
      thread_data[n].thread_tag = tag_index[sender_index];
    1356:	42 8b 04 28          	mov    (%rax,%r13,1),%eax
      thread_data[n].sender = &thread_data[sender];
    135a:	4c 89 75 08          	mov    %r14,0x8(%rbp)
      thread_data[n].end = 0;
    135e:	c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbp)
      thread_data[n].thread_tag = tag_index[sender_index];
    1368:	89 85 14 02 00 00    	mov    %eax,0x214(%rbp)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    136e:	e8 ed fd ff ff       	call   1160 <calloc@plt>
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    1373:	be 00 02 00 00       	mov    $0x200,%esi
    1378:	bf 00 80 00 00       	mov    $0x8000,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    137d:	48 89 85 00 02 00 00 	mov    %rax,0x200(%rbp)
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    1384:	e8 d7 fd ff ff       	call   1160 <calloc@plt>
    1389:	48 89 45 18          	mov    %rax,0x18(%rbp)
      for (int k = 0 ; k < buffer_size ; k++) {
    138d:	48 8d 98 80 00 00 00 	lea    0x80(%rax),%rbx
    1394:	4c 8d b8 80 00 00 01 	lea    0x1000080(%rax),%r15
    139b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13a0:	be 04 00 00 00       	mov    $0x4,%esi
    13a5:	bf 02 00 00 00       	mov    $0x2,%edi
      for (int k = 0 ; k < buffer_size ; k++) {
    13aa:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13b1:	e8 aa fd ff ff       	call   1160 <calloc@plt>
        thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    13b6:	be 10 00 00 00       	mov    $0x10,%esi
    13bb:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13c0:	48 89 83 80 fe ff ff 	mov    %rax,-0x180(%rbx)
        thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    13c7:	e8 94 fd ff ff       	call   1160 <calloc@plt>
    13cc:	48 89 83 00 fe ff ff 	mov    %rax,-0x200(%rbx)
      for (int k = 0 ; k < buffer_size ; k++) {
    13d3:	4c 39 fb             	cmp    %r15,%rbx
    13d6:	75 c8                	jne    13a0 <main+0x1e0>
      }
      thread_data[n].other_count = other_count;
    13d8:	c7 85 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%rbp)
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    13e2:	49 83 c5 04          	add    $0x4,%r13
    13e6:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    13ed:	45 85 e4             	test   %r12d,%r12d
    13f0:	75 0b                	jne    13fd <main+0x23d>
    13f2:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    13f8:	e9 d7 fe ff ff       	jmp    12d4 <main+0x114>
    13fd:	49 8d 86 00 05 00 00 	lea    0x500(%r14),%rax
    1404:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    1409:	66 49 0f 6e d6       	movq   %r14,%xmm2
    140e:	45 31 ff             	xor    %r15d,%r15d
    1411:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    1416:	66 0f 6c d2          	punpcklqdq %xmm2,%xmm2
    }

    // printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    141a:	41 bc 02 00 00 00    	mov    $0x2,%r12d
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    1420:	49 89 c5             	mov    %rax,%r13
    1423:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    1428:	4c 89 f3             	mov    %r14,%rbx
    142b:	4d 89 fe             	mov    %r15,%r14
    142e:	45 89 e7             	mov    %r12d,%r15d
    1431:	0f 29 54 24 10       	movaps %xmm2,0x10(%rsp)
      thread_data[j].thread_index = j;
    1436:	45 89 7d 00          	mov    %r15d,0x0(%r13)
      thread_data[j].reader_index = receiver_index;
      thread_data[j].multiple = receiver_index % other_count;
      thread_data[j].other_count = other_count;
     
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    143a:	be 80 00 00 00       	mov    $0x80,%esi
    143f:	bf 01 00 00 00       	mov    $0x1,%edi
    1444:	47 8d 24 3f          	lea    (%r15,%r15,1),%r12d
      thread_data[j].reader_index = receiver_index;
    1448:	45 89 b5 0c 02 00 00 	mov    %r14d,0x20c(%r13)
      thread_data[j].multiple = receiver_index % other_count;
    144f:	45 89 b5 10 02 00 00 	mov    %r14d,0x210(%r13)
      thread_data[j].other_count = other_count;
    1456:	41 c7 85 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%r13)
    1461:	44 89 34 24          	mov    %r14d,(%rsp)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1465:	e8 f6 fc ff ff       	call   1160 <calloc@plt>
      CPU_ZERO(receivercpu);
      CPU_SET(curcpu, receivercpu);
    146a:	44 89 e1             	mov    %r12d,%ecx
    146d:	44 89 fa             	mov    %r15d,%edx
    1470:	bf 01 00 00 00       	mov    $0x1,%edi
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1475:	48 89 c5             	mov    %rax,%rbp
      CPU_SET(curcpu, receivercpu);
    1478:	b8 01 00 00 00       	mov    $0x1,%eax
    147d:	48 8d 35 cc 0b 00 00 	lea    0xbcc(%rip),%rsi        # 2050 <_IO_stdin_used+0x50>
    1484:	48 d3 e0             	shl    %cl,%rax
    1487:	48 09 45 00          	or     %rax,0x0(%rbp)
    148b:	44 89 e1             	mov    %r12d,%ecx
    148e:	31 c0                	xor    %eax,%eax
    1490:	e8 db fc ff ff       	call   1170 <__printf_chk@plt>
      printf("assigning receiver %d to core %d\n", j, curcpu);
      curcpu += coreinterval;
      thread_data[j].cpu_set = receivercpu;
    1495:	49 89 ad a0 01 00 00 	mov    %rbp,0x1a0(%r13)
      thread_data[j].running = 1;
    149c:	41 c7 85 98 01 00 00 01 00 00 00 	movl   $0x1,0x198(%r13)
      thread_data[j].mode = READER;
    14a7:	41 c7 85 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%r13)
      if (j == receiver) {
    14b2:	41 83 ff 02          	cmp    $0x2,%r15d
    14b6:	0f 84 08 03 00 00    	je     17c4 <main+0x604>
        for (int n = 0 ; n < buffer_size ; n++) {
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
        }
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
    14bc:	66 0f 6f 4c 24 10    	movdqa 0x10(%rsp),%xmm1
    14c2:	8b 2c 24             	mov    (%rsp),%ebp
    14c5:	31 c9                	xor    %ecx,%ecx
    14c7:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    14cc:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    14d3:	48 8d 35 9e 0b 00 00 	lea    0xb9e(%rip),%rsi        # 2078 <_IO_stdin_used+0x78>
      thread_data[j].size = buffer_size;
    14da:	49 c7 85 90 01 00 00 00 80 00 00 	movq   $0x8000,0x190(%r13)
      thread_data[j].start = 0;
    14e5:	41 c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r13)
    14f0:	89 ea                	mov    %ebp,%edx
      thread_data[j].readers = thread_data[sender].readers;
    14f2:	49 89 85 00 02 00 00 	mov    %rax,0x200(%r13)
    14f9:	31 c0                	xor    %eax,%eax
      thread_data[j].other_count = other_count;
    14fb:	41 c7 85 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%r13)
      thread_data[j].sender = &thread_data[sender];
    1506:	41 0f 11 4d 08       	movups %xmm1,0x8(%r13)
    150b:	e8 60 fc ff ff       	call   1170 <__printf_chk@plt>
      // printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        printf("assigned reader %d to sender %d\n", receiver_index, n);
        thread_data[n].readers[receiver_index] = &thread_data[j];
    1510:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    1517:	89 ea                	mov    %ebp,%edx
    1519:	b9 01 00 00 00       	mov    $0x1,%ecx
    151e:	48 8d 35 53 0b 00 00 	lea    0xb53(%rip),%rsi        # 2078 <_IO_stdin_used+0x78>
    1525:	bf 01 00 00 00       	mov    $0x1,%edi
    152a:	4e 89 2c f0          	mov    %r13,(%rax,%r14,8)
    152e:	31 c0                	xor    %eax,%eax
    1530:	e8 3b fc ff ff       	call   1170 <__printf_chk@plt>
    1535:	48 8b 83 80 04 00 00 	mov    0x480(%rbx),%rax
    153c:	4e 89 2c f0          	mov    %r13,(%rax,%r14,8)
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1540:	49 83 c6 01          	add    $0x1,%r14
    1544:	49 81 c5 80 02 00 00 	add    $0x280,%r13
    154b:	41 83 ff 02          	cmp    $0x2,%r15d
    154f:	75 0b                	jne    155c <main+0x39c>
    1551:	41 bf 03 00 00 00    	mov    $0x3,%r15d
    1557:	e9 da fe ff ff       	jmp    1436 <main+0x276>
    155c:	49 89 de             	mov    %rbx,%r14
    155f:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
      }
    }
    curcpu = 0;
    // printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    1564:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    1567:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
      if (ret) {
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    156c:	4c 89 34 24          	mov    %r14,(%rsp)
    1570:	48 8d 6b 10          	lea    0x10(%rbx),%rbp
    1574:	4c 8d 25 c5 03 00 00 	lea    0x3c5(%rip),%r12        # 1940 <disruptor_thread>
  param.sched_priority = 0;
    157b:	c7 44 24 3c 00 00 00 00 	movl   $0x0,0x3c(%rsp)
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1583:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
    1588:	4c 8d 78 70          	lea    0x70(%rax),%r15
    158c:	4c 8d a8 e0 00 00 00 	lea    0xe0(%rax),%r13
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    1593:	31 f6                	xor    %esi,%esi
    1595:	4c 89 ff             	mov    %r15,%rdi
    1598:	e8 b3 fb ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    159d:	85 c0                	test   %eax,%eax
    159f:	0f 85 72 02 00 00    	jne    1817 <main+0x657>
      ret = pthread_attr_setschedparam(&attr[j], &param);
    15a5:	48 8d 74 24 3c       	lea    0x3c(%rsp),%rsi
    15aa:	4c 89 ff             	mov    %r15,%rdi
    15ad:	e8 de fb ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    15b2:	85 c0                	test   %eax,%eax
    15b4:	0f 85 78 02 00 00    	jne    1832 <main+0x672>
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    15ba:	4c 89 f1             	mov    %r14,%rcx
    15bd:	4c 89 fe             	mov    %r15,%rsi
    15c0:	48 89 ef             	mov    %rbp,%rdi
    15c3:	4c 89 e2             	mov    %r12,%rdx
    15c6:	e8 b5 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    15cb:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15cf:	49 83 c7 38          	add    $0x38,%r15
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    15d3:	49 8b 96 a0 01 00 00 	mov    0x1a0(%r14),%rdx
    15da:	be 08 00 00 00       	mov    $0x8,%esi
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15df:	48 83 c5 08          	add    $0x8,%rbp
    15e3:	49 81 c6 80 02 00 00 	add    $0x280,%r14
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    15ea:	e8 11 fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15ef:	4d 39 ef             	cmp    %r13,%r15
    15f2:	75 9f                	jne    1593 <main+0x3d3>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    15f4:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    15f9:	31 f6                	xor    %esi,%esi
    15fb:	4c 8b 34 24          	mov    (%rsp),%r14
    15ff:	4c 89 ff             	mov    %r15,%rdi
    1602:	e8 49 fb ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    1607:	85 c0                	test   %eax,%eax
    1609:	0f 85 08 02 00 00    	jne    1817 <main+0x657>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    160f:	48 8d 74 24 38       	lea    0x38(%rsp),%rsi
    1614:	4c 89 ff             	mov    %r15,%rdi
      param2.sched_priority = 0;
    1617:	c7 44 24 38 00 00 00 00 	movl   $0x0,0x38(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    161f:	e8 6c fb ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1624:	85 c0                	test   %eax,%eax
    1626:	0f 85 06 02 00 00    	jne    1832 <main+0x672>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    162c:	4c 89 f1             	mov    %r14,%rcx
    162f:	48 89 df             	mov    %rbx,%rdi
    1632:	4c 89 e2             	mov    %r12,%rdx
    1635:	4c 89 fe             	mov    %r15,%rsi
    1638:	e8 43 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    163d:	48 8b 3b             	mov    (%rbx),%rdi
    1640:	be 08 00 00 00       	mov    $0x8,%esi
    void * res1;
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    1645:	31 ed                	xor    %ebp,%ebp
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    1647:	49 8b 96 a0 01 00 00 	mov    0x1a0(%r14),%rdx
    164e:	e8 ad fa ff ff       	call   1100 <pthread_setaffinity_np@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    1653:	4c 89 fe             	mov    %r15,%rsi
    1656:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    165a:	4c 89 e2             	mov    %r12,%rdx
    165d:	49 8d 8e 80 02 00 00 	lea    0x280(%r14),%rcx
    1664:	48 83 c6 38          	add    $0x38,%rsi
    1668:	e8 13 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    166d:	49 8b 96 20 04 00 00 	mov    0x420(%r14),%rdx
    1674:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    1678:	be 08 00 00 00       	mov    $0x8,%esi
    167d:	e8 7e fa ff ff       	call   1100 <pthread_setaffinity_np@plt>
  nanosleep(&preempt , &rem2);
    1682:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    1687:	48 8d 7c 24 50       	lea    0x50(%rsp),%rdi
  struct timespec preempt = {
    168c:	66 0f 6f 05 bc 0a 00 00 	movdqa 0xabc(%rip),%xmm0        # 2150 <_IO_stdin_used+0x150>
    1694:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&preempt , &rem2);
    1699:	e8 a2 fa ff ff       	call   1140 <nanosleep@plt>
      pthread_join(thread[n], res1);
    169e:	48 8b 3b             	mov    (%rbx),%rdi
    16a1:	48 89 ee             	mov    %rbp,%rsi
    thread_data[sender].running = 0;
    16a4:	41 c7 86 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r14)
      thread_data[j].running = 0;
    16af:	41 c7 86 98 06 00 00 00 00 00 00 	movl   $0x0,0x698(%r14)
    16ba:	41 c7 86 18 09 00 00 00 00 00 00 	movl   $0x0,0x918(%r14)
      thread_data[n].running = 0;
    16c5:	41 c7 86 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r14)
    16d0:	41 c7 86 18 04 00 00 00 00 00 00 	movl   $0x0,0x418(%r14)
      pthread_join(thread[n], res1);
    16db:	e8 d0 fa ff ff       	call   11b0 <pthread_join@plt>
    16e0:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    16e4:	48 89 ee             	mov    %rbp,%rsi
    16e7:	e8 c4 fa ff ff       	call   11b0 <pthread_join@plt>
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    16ec:	48 8b 7b 10          	mov    0x10(%rbx),%rdi
    16f0:	48 89 ee             	mov    %rbp,%rsi
    16f3:	e8 b8 fa ff ff       	call   11b0 <pthread_join@plt>
    16f8:	48 8b 7b 18          	mov    0x18(%rbx),%rdi
    16fc:	48 89 ee             	mov    %rbp,%rsi
    16ff:	31 db                	xor    %ebx,%ebx
    1701:	48 8d 2d 17 0a 00 00 	lea    0xa17(%rip),%rbp        # 211f <_IO_stdin_used+0x11f>
    1708:	e8 a3 fa ff ff       	call   11b0 <pthread_join@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    // printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    170d:	eb 11                	jmp    1720 <main+0x560>
    170f:	90                   	nop
    1710:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
    1717:	48 81 fb 00 00 00 01 	cmp    $0x1000000,%rbx
    171e:	74 7d                	je     179d <main+0x5dd>
      int compcount = 0;
      for (int n = 0 ; n < other_count ; n++) {

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
    176e:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
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
    1794:	48 81 fb 00 00 00 01 	cmp    $0x1000000,%rbx
    179b:	75 83                	jne    1720 <main+0x560>
    }
    // printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    179d:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    17a5:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    17ae:	75 7d                	jne    182d <main+0x66d>
    17b0:	48 81 c4 98 00 00 00 	add    $0x98,%rsp
    17b7:	31 c0                	xor    %eax,%eax
    17b9:	5b                   	pop    %rbx
    17ba:	5d                   	pop    %rbp
    17bb:	41 5c                	pop    %r12
    17bd:	41 5d                	pop    %r13
    17bf:	41 5e                	pop    %r14
    17c1:	41 5f                	pop    %r15
    17c3:	c3                   	ret
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    17c4:	be 00 02 00 00       	mov    $0x200,%esi
    17c9:	bf 00 80 00 00       	mov    $0x8000,%edi
    17ce:	e8 8d f9 ff ff       	call   1160 <calloc@plt>
    17d3:	49 89 45 18          	mov    %rax,0x18(%r13)
    17d7:	49 89 c4             	mov    %rax,%r12
        for (int n = 0 ; n < buffer_size ; n++) {
    17da:	48 8d a8 00 01 00 00 	lea    0x100(%rax),%rbp
    17e1:	49 81 c4 00 01 00 01 	add    $0x1000100,%r12
    17e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    17f0:	be 04 00 00 00       	mov    $0x4,%esi
    17f5:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    17fa:	48 81 c5 00 02 00 00 	add    $0x200,%rbp
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1801:	e8 5a f9 ff ff       	call   1160 <calloc@plt>
    1806:	48 89 85 00 fe ff ff 	mov    %rax,-0x200(%rbp)
        for (int n = 0 ; n < buffer_size ; n++) {
    180d:	4c 39 e5             	cmp    %r12,%rbp
    1810:	75 de                	jne    17f0 <main+0x630>
    1812:	e9 a5 fc ff ff       	jmp    14bc <main+0x2fc>
    1817:	48 8d 3d c6 08 00 00 	lea    0x8c6(%rip),%rdi        # 20e4 <_IO_stdin_used+0xe4>
    181e:	e8 ed f8 ff ff       	call   1110 <puts@plt>
               exit(1);
    1823:	bf 01 00 00 00       	mov    $0x1,%edi
    1828:	e8 73 f9 ff ff       	call   11a0 <exit@plt>
}
    182d:	e8 fe f8 ff ff       	call   1130 <__stack_chk_fail@plt>
    1832:	48 8d 3d c9 08 00 00 	lea    0x8c9(%rip),%rdi        # 2102 <_IO_stdin_used+0x102>
    1839:	e8 d2 f8 ff ff       	call   1110 <puts@plt>
              exit(1);
    183e:	bf 01 00 00 00       	mov    $0x1,%edi
    1843:	e8 58 f9 ff ff       	call   11a0 <exit@plt>
    1848:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000001850 <_start>:
    1850:	f3 0f 1e fa          	endbr64
    1854:	31 ed                	xor    %ebp,%ebp
    1856:	49 89 d1             	mov    %rdx,%r9
    1859:	5e                   	pop    %rsi
    185a:	48 89 e2             	mov    %rsp,%rdx
    185d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1861:	50                   	push   %rax
    1862:	54                   	push   %rsp
    1863:	45 31 c0             	xor    %r8d,%r8d
    1866:	31 c9                	xor    %ecx,%ecx
    1868:	48 8d 3d 51 f9 ff ff 	lea    -0x6af(%rip),%rdi        # 11c0 <main>
    186f:	ff 15 63 27 00 00    	call   *0x2763(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1875:	f4                   	hlt
    1876:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001880 <deregister_tm_clones>:
    1880:	48 8d 3d 89 27 00 00 	lea    0x2789(%rip),%rdi        # 4010 <__TMC_END__>
    1887:	48 8d 05 82 27 00 00 	lea    0x2782(%rip),%rax        # 4010 <__TMC_END__>
    188e:	48 39 f8             	cmp    %rdi,%rax
    1891:	74 15                	je     18a8 <deregister_tm_clones+0x28>
    1893:	48 8b 05 46 27 00 00 	mov    0x2746(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    189a:	48 85 c0             	test   %rax,%rax
    189d:	74 09                	je     18a8 <deregister_tm_clones+0x28>
    189f:	ff e0                	jmp    *%rax
    18a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    18a8:	c3                   	ret
    18a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018b0 <register_tm_clones>:
    18b0:	48 8d 3d 59 27 00 00 	lea    0x2759(%rip),%rdi        # 4010 <__TMC_END__>
    18b7:	48 8d 35 52 27 00 00 	lea    0x2752(%rip),%rsi        # 4010 <__TMC_END__>
    18be:	48 29 fe             	sub    %rdi,%rsi
    18c1:	48 89 f0             	mov    %rsi,%rax
    18c4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    18c8:	48 c1 f8 03          	sar    $0x3,%rax
    18cc:	48 01 c6             	add    %rax,%rsi
    18cf:	48 d1 fe             	sar    %rsi
    18d2:	74 14                	je     18e8 <register_tm_clones+0x38>
    18d4:	48 8b 05 15 27 00 00 	mov    0x2715(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    18db:	48 85 c0             	test   %rax,%rax
    18de:	74 08                	je     18e8 <register_tm_clones+0x38>
    18e0:	ff e0                	jmp    *%rax
    18e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    18e8:	c3                   	ret
    18e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018f0 <__do_global_dtors_aux>:
    18f0:	f3 0f 1e fa          	endbr64
    18f4:	80 3d 15 27 00 00 00 	cmpb   $0x0,0x2715(%rip)        # 4010 <__TMC_END__>
    18fb:	75 2b                	jne    1928 <__do_global_dtors_aux+0x38>
    18fd:	55                   	push   %rbp
    18fe:	48 83 3d f2 26 00 00 00 	cmpq   $0x0,0x26f2(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1906:	48 89 e5             	mov    %rsp,%rbp
    1909:	74 0c                	je     1917 <__do_global_dtors_aux+0x27>
    190b:	48 8b 3d f6 26 00 00 	mov    0x26f6(%rip),%rdi        # 4008 <__dso_handle>
    1912:	e8 d9 f7 ff ff       	call   10f0 <__cxa_finalize@plt>
    1917:	e8 64 ff ff ff       	call   1880 <deregister_tm_clones>
    191c:	c6 05 ed 26 00 00 01 	movb   $0x1,0x26ed(%rip)        # 4010 <__TMC_END__>
    1923:	5d                   	pop    %rbp
    1924:	c3                   	ret
    1925:	0f 1f 00             	nopl   (%rax)
    1928:	c3                   	ret
    1929:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001930 <frame_dummy>:
    1930:	f3 0f 1e fa          	endbr64
    1934:	e9 77 ff ff ff       	jmp    18b0 <register_tm_clones>
    1939:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001940 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    1940:	f3 0f 1e fa          	endbr64
    1944:	41 57                	push   %r15
    1946:	41 56                	push   %r14
    1948:	41 55                	push   %r13
    194a:	41 54                	push   %r12
    194c:	55                   	push   %rbp
    194d:	53                   	push   %rbx
    194e:	48 89 fb             	mov    %rdi,%rbx
    1951:	48 83 ec 08          	sub    $0x8,%rsp
  if (data->mode == WRITER) {
    1955:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
    195b:	85 c0                	test   %eax,%eax
    195d:	0f 85 3a 01 00 00    	jne    1a9d <disruptor_thread+0x15d>
    struct Thread *me = data->sender;
    1963:	48 8b 6f 08          	mov    0x8(%rdi),%rbp
    while (data->running == 1) {
    1967:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    1970:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    1976:	83 f8 01             	cmp    $0x1,%eax
    1979:	0f 85 0d 01 00 00    	jne    1a8c <disruptor_thread+0x14c>
      asm volatile ("sfence" ::: "memory");
    197f:	0f ae f8             	sfence
      long pos = (((__atomic_load_n(&me->realend, __ATOMIC_SEQ_CST) & END_MASK) >> 32) + 1) % data->size;
    1982:	48 8d b5 80 01 00 00 	lea    0x180(%rbp),%rsi
    1989:	48 8b 85 80 01 00 00 	mov    0x180(%rbp),%rax
    1990:	48 c1 f8 20          	sar    $0x20,%rax
    1994:	25 ff ff ff 0f       	and    $0xfffffff,%eax
    1999:	48 83 c0 01          	add    $0x1,%rax
    199d:	48 99                	cqto
      for (int x  = 0 ; x < data->other_count; x++) {
    199f:	8b 8b 08 02 00 00    	mov    0x208(%rbx),%ecx
      long pos = (((__atomic_load_n(&me->realend, __ATOMIC_SEQ_CST) & END_MASK) >> 32) + 1) % data->size;
    19a5:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
      for (int x  = 0 ; x < data->other_count; x++) {
    19ac:	85 c9                	test   %ecx,%ecx
    19ae:	7e 2b                	jle    19db <disruptor_thread+0x9b>
    19b0:	31 c9                	xor    %ecx,%ecx
    19b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (pos == __atomic_load_n(&data->readers[x]->start, __ATOMIC_SEQ_CST)) {
    19b8:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    19bf:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    19c3:	48 63 80 80 00 00 00 	movslq 0x80(%rax),%rax
    19ca:	48 39 d0             	cmp    %rdx,%rax
    19cd:	74 a1                	je     1970 <disruptor_thread+0x30>
      for (int x  = 0 ; x < data->other_count; x++) {
    19cf:	48 83 c1 01          	add    $0x1,%rcx
    19d3:	39 8b 08 02 00 00    	cmp    %ecx,0x208(%rbx)
    19d9:	7f dd                	jg     19b8 <disruptor_thread+0x78>
            long original = __atomic_load_n(&me->realend, __ATOMIC_SEQ_CST);
    19db:	4c 8b 85 80 01 00 00 	mov    0x180(%rbp),%r8
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    19e2:	4c 89 c0             	mov    %r8,%rax
    19e5:	48 c1 f8 20          	sar    $0x20,%rax
    19e9:	25 ff ff ff 0f       	and    $0xfffffff,%eax
    19ee:	48 83 c0 01          	add    $0x1,%rax
    19f2:	48 99                	cqto
              long new = (data->thread_tag) | (changed << 32);
    19f4:	4c 63 93 14 02 00 00 	movslq 0x214(%rbx),%r10
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    19fb:	48 f7 bd 90 01 00 00 	idivq  0x190(%rbp)
              for (int x = 0 ; x < data->other_count; x++) {
    1a02:	8b 83 08 02 00 00    	mov    0x208(%rbx),%eax
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1a08:	49 89 d1             	mov    %rdx,%r9
              for (int x = 0 ; x < data->other_count; x++) {
    1a0b:	85 c0                	test   %eax,%eax
    1a0d:	7e 2f                	jle    1a3e <disruptor_thread+0xfe>
                __atomic_store_n(&me->data[changed].complete[x], 0, __ATOMIC_SEQ_CST);
    1a0f:	49 89 d4             	mov    %rdx,%r12
    1a12:	31 c9                	xor    %ecx,%ecx
    1a14:	45 31 db             	xor    %r11d,%r11d
    1a17:	49 c1 e4 09          	shl    $0x9,%r12
    1a1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    1a20:	48 8b 45 18          	mov    0x18(%rbp),%rax
    1a24:	4a 8b bc 20 00 01 00 00 	mov    0x100(%rax,%r12,1),%rdi
    1a2c:	44 89 d8             	mov    %r11d,%eax
    1a2f:	87 04 8f             	xchg   %eax,(%rdi,%rcx,4)
              for (int x = 0 ; x < data->other_count; x++) {
    1a32:	48 83 c1 01          	add    $0x1,%rcx
    1a36:	39 8b 08 02 00 00    	cmp    %ecx,0x208(%rbx)
    1a3c:	7f e2                	jg     1a20 <disruptor_thread+0xe0>
              long new = (data->thread_tag) | (changed << 32);
    1a3e:	48 c1 e2 20          	shl    $0x20,%rdx
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED))) {
    1a42:	4c 89 c0             	mov    %r8,%rax
              long new = (data->thread_tag) | (changed << 32);
    1a45:	4c 09 d2             	or     %r10,%rdx
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED))) {
    1a48:	f0 48 0f b1 16       	lock cmpxchg %rdx,(%rsi)
    1a4d:	0f 85 f0 00 00 00    	jne    1b43 <disruptor_thread+0x203>
                clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1a53:	48 8b 75 18          	mov    0x18(%rbp),%rsi
    1a57:	49 c1 e1 09          	shl    $0x9,%r9
    1a5b:	bf 04 00 00 00       	mov    $0x4,%edi
    1a60:	4d 89 cc             	mov    %r9,%r12
    1a63:	4c 01 ce             	add    %r9,%rsi
    1a66:	e8 b5 f6 ff ff       	call   1120 <clock_gettime@plt>
                __atomic_store_n(&me->data[changed].written, me->other_count, __ATOMIC_SEQ_CST);
    1a6b:	48 8b 55 18          	mov    0x18(%rbp),%rdx
    1a6f:	8b 85 08 02 00 00    	mov    0x208(%rbp),%eax
    1a75:	42 87 84 22 80 01 00 00 	xchg   %eax,0x180(%rdx,%r12,1)
    while (data->running == 1) {
    1a7d:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    1a83:	83 f8 01             	cmp    $0x1,%eax
    1a86:	0f 84 f3 fe ff ff    	je     197f <disruptor_thread+0x3f>
}
    1a8c:	48 83 c4 08          	add    $0x8,%rsp
    1a90:	31 c0                	xor    %eax,%eax
    1a92:	5b                   	pop    %rbx
    1a93:	5d                   	pop    %rbp
    1a94:	41 5c                	pop    %r12
    1a96:	41 5d                	pop    %r13
    1a98:	41 5e                	pop    %r14
    1a9a:	41 5f                	pop    %r15
    1a9c:	c3                   	ret
  } else if (data->mode == READER) {
    1a9d:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
    1aa3:	83 f8 01             	cmp    $0x1,%eax
    1aa6:	75 e4                	jne    1a8c <disruptor_thread+0x14c>
    struct Thread *sender = data->sender;
    1aa8:	4c 8b 6f 08          	mov    0x8(%rdi),%r13
    struct Snapshot * rdata = sender->data;
    1aac:	4d 8b 75 18          	mov    0x18(%r13),%r14
    while (data->running == 1) {
    1ab0:	eb 20                	jmp    1ad2 <disruptor_thread+0x192>
    1ab2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      int pos = ((__atomic_load_n(&sender->realend, __ATOMIC_SEQ_CST) & END_MASK) >> 32);
    1ab8:	49 8b 85 80 01 00 00 	mov    0x180(%r13),%rax
    1abf:	48 c1 f8 20          	sar    $0x20,%rax
    1ac3:	25 ff ff ff 0f       	and    $0xfffffff,%eax
      if (pos == data->start) {
    1ac8:	8b ab 80 00 00 00    	mov    0x80(%rbx),%ebp
    1ace:	39 c5                	cmp    %eax,%ebp
    1ad0:	75 0f                	jne    1ae1 <disruptor_thread+0x1a1>
    while (data->running == 1) {
    1ad2:	44 8b a3 98 01 00 00 	mov    0x198(%rbx),%r12d
    1ad9:	41 83 fc 01          	cmp    $0x1,%r12d
    1add:	74 d9                	je     1ab8 <disruptor_thread+0x178>
    1adf:	eb ab                	jmp    1a8c <disruptor_thread+0x14c>
          if (__atomic_load_n(&rdata[changed].written, __ATOMIC_SEQ_CST) > 0) {
    1ae1:	4c 63 fd             	movslq %ebp,%r15
    1ae4:	49 c1 e7 09          	shl    $0x9,%r15
    1ae8:	4d 01 f7             	add    %r14,%r15
    1aeb:	41 8b 87 80 01 00 00 	mov    0x180(%r15),%eax
    1af2:	85 c0                	test   %eax,%eax
    1af4:	7e dc                	jle    1ad2 <disruptor_thread+0x192>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1af6:	48 63 b3 0c 02 00 00 	movslq 0x20c(%rbx),%rsi
    1afd:	bf 04 00 00 00       	mov    $0x4,%edi
    1b02:	48 c1 e6 04          	shl    $0x4,%rsi
    1b06:	49 03 b7 80 00 00 00 	add    0x80(%r15),%rsi
    1b0d:	e8 0e f6 ff ff       	call   1120 <clock_gettime@plt>
              __atomic_store_n(&rdata[changed].complete[data->reader_index], 1, __ATOMIC_SEQ_CST);
    1b12:	48 63 93 0c 02 00 00 	movslq 0x20c(%rbx),%rdx
    1b19:	49 8b 87 00 01 00 00 	mov    0x100(%r15),%rax
    1b20:	44 87 24 90          	xchg   %r12d,(%rax,%rdx,4)
              __atomic_store_n(&data->start, (changed + 1) % data->size, __ATOMIC_SEQ_CST);
    1b24:	8d 45 01             	lea    0x1(%rbp),%eax
    1b27:	48 98                	cltq
    1b29:	48 99                	cqto
    1b2b:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
    1b32:	87 93 80 00 00 00    	xchg   %edx,0x80(%rbx)
              __atomic_sub_fetch(&rdata[changed].written, 1, __ATOMIC_SEQ_CST);
    1b38:	f0 41 83 af 80 01 00 00 01 	lock subl $0x1,0x180(%r15)
    1b41:	eb 8f                	jmp    1ad2 <disruptor_thread+0x192>
                original = __atomic_load_n(&me->realend, __ATOMIC_SEQ_CST);
    1b43:	48 8b 0e             	mov    (%rsi),%rcx
                changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1b46:	48 89 c8             	mov    %rcx,%rax
    1b49:	48 c1 f8 20          	sar    $0x20,%rax
    1b4d:	25 ff ff ff 0f       	and    $0xfffffff,%eax
    1b52:	48 83 c0 01          	add    $0x1,%rax
    1b56:	48 99                	cqto
    1b58:	48 f7 bd 90 01 00 00 	idivq  0x190(%rbp)
    1b5f:	49 89 d1             	mov    %rdx,%r9
                new = (data->thread_tag) | (changed << 32);
    1b62:	48 63 93 14 02 00 00 	movslq 0x214(%rbx),%rdx
    1b69:	4c 89 c8             	mov    %r9,%rax
    1b6c:	48 c1 e0 20          	shl    $0x20,%rax
    1b70:	48 09 c2             	or     %rax,%rdx
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED))) {
    1b73:	48 89 c8             	mov    %rcx,%rax
    1b76:	f0 48 0f b1 16       	lock cmpxchg %rdx,(%rsi)
    1b7b:	0f 84 d2 fe ff ff    	je     1a53 <disruptor_thread+0x113>
    1b81:	eb c0                	jmp    1b43 <disruptor_thread+0x203>
    1b83:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    1b8e:	66 90                	xchg   %ax,%ax

0000000000001b90 <min>:
int min(long a, long b) {
    1b90:	f3 0f 1e fa          	endbr64
  if (a < b) return a;
    1b94:	48 39 f7             	cmp    %rsi,%rdi
    1b97:	7c 02                	jl     1b9b <min+0xb>
  if (b < a) return b;
    1b99:	7f 05                	jg     1ba0 <min+0x10>
  if (a < b) return a;
    1b9b:	89 f8                	mov    %edi,%eax
    1b9d:	c3                   	ret
    1b9e:	66 90                	xchg   %ax,%ax
  if (b < a) return b;
    1ba0:	89 f0                	mov    %esi,%eax
}
    1ba2:	c3                   	ret

Disassembly of section .fini:

0000000000001ba4 <_fini>:
    1ba4:	f3 0f 1e fa          	endbr64
    1ba8:	48 83 ec 08          	sub    $0x8,%rsp
    1bac:	48 83 c4 08          	add    $0x8,%rsp
    1bb0:	c3                   	ret
