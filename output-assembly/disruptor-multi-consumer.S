
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
    11cb:	ba 0f 00 00 00       	mov    $0xf,%edx
    11d0:	48 8d 35 31 0e 00 00 	lea    0xe31(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    11d7:	41 56                	push   %r14
    11d9:	bf 01 00 00 00       	mov    $0x1,%edi
    11de:	41 55                	push   %r13
    11e0:	41 54                	push   %r12
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int receiver2 = receiver + 1; 
    int seq[] = {1, 2, 5};
    int tag_index[] = {1, 5, 7};
    11e2:	45 31 e4             	xor    %r12d,%r12d
int main() {
    11e5:	55                   	push   %rbp
    11e6:	53                   	push   %rbx
    11e7:	48 81 ec 98 00 00 00 	sub    $0x98,%rsp
    11ee:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    11f7:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    11ff:	31 c0                	xor    %eax,%eax
    1201:	4c 8d 74 24 78       	lea    0x78(%rsp),%r14
    1206:	e8 65 ff ff ff       	call   1170 <__printf_chk@plt>
    120b:	ba 01 00 00 00       	mov    $0x1,%edx
    1210:	48 8d 35 82 0e 00 00 	lea    0xe82(%rip),%rsi        # 2099 <_IO_stdin_used+0x99>
    1217:	31 c0                	xor    %eax,%eax
    1219:	bf 01 00 00 00       	mov    $0x1,%edi
    121e:	e8 4d ff ff ff       	call   1170 <__printf_chk@plt>
    1223:	ba 02 00 00 00       	mov    $0x2,%edx
    1228:	48 8d 35 7a 0e 00 00 	lea    0xe7a(%rip),%rsi        # 20a9 <_IO_stdin_used+0xa9>
    122f:	31 c0                	xor    %eax,%eax
    1231:	bf 01 00 00 00       	mov    $0x1,%edi
    1236:	e8 35 ff ff ff       	call   1170 <__printf_chk@plt>
    123b:	ba 02 00 00 00       	mov    $0x2,%edx
    1240:	48 8d 35 74 0e 00 00 	lea    0xe74(%rip),%rsi        # 20bb <_IO_stdin_used+0xbb>
    1247:	31 c0                	xor    %eax,%eax
    1249:	bf 01 00 00 00       	mov    $0x1,%edi
    124e:	e8 1d ff ff ff       	call   1170 <__printf_chk@plt>
    1253:	ba 04 00 00 00       	mov    $0x4,%edx
    1258:	48 8d 35 6e 0e 00 00 	lea    0xe6e(%rip),%rsi        # 20cd <_IO_stdin_used+0xcd>
    125f:	31 c0                	xor    %eax,%eax
    1261:	bf 01 00 00 00       	mov    $0x1,%edi
    1266:	e8 05 ff ff ff       	call   1170 <__printf_chk@plt>
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    126b:	be 80 02 00 00       	mov    $0x280,%esi
    1270:	bf 04 00 00 00       	mov    $0x4,%edi
    1275:	e8 e6 fe ff ff       	call   1160 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    127a:	be 38 00 00 00       	mov    $0x38,%esi
    127f:	bf 04 00 00 00       	mov    $0x4,%edi
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1284:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1287:	e8 d4 fe ff ff       	call   1160 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    128c:	be 08 00 00 00       	mov    $0x8,%esi
    1291:	bf 04 00 00 00       	mov    $0x4,%edi
    1296:	4c 89 fd             	mov    %r15,%rbp
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1299:	48 89 c3             	mov    %rax,%rbx
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    129c:	e8 bf fe ff ff       	call   1160 <calloc@plt>
    int tag_index[] = {1, 5, 7};
    12a1:	31 c9                	xor    %ecx,%ecx
    12a3:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12a8:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    int seq[] = {1, 2, 5};
    12ad:	48 8b 05 84 0e 00 00 	mov    0xe84(%rip),%rax        # 2138 <_IO_stdin_used+0x138>
    12b4:	89 cb                	mov    %ecx,%ebx
    12b6:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    int tag_index[] = {1, 5, 7};
    12bb:	48 8b 05 7e 0e 00 00 	mov    0xe7e(%rip),%rax        # 2140 <_IO_stdin_used+0x140>
    12c2:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    12c7:	48 8d 44 24 68       	lea    0x68(%rsp),%rax
    12cc:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12d1:	be 80 00 00 00       	mov    $0x80,%esi
    12d6:	bf 01 00 00 00       	mov    $0x1,%edi
    12db:	e8 80 fe ff ff       	call   1160 <calloc@plt>
      CPU_ZERO(sendercpu);
      CPU_SET(curcpu, sendercpu);
    12e0:	89 d9                	mov    %ebx,%ecx
    12e2:	44 89 e2             	mov    %r12d,%edx
    12e5:	bf 01 00 00 00       	mov    $0x1,%edi
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12ea:	49 89 c5             	mov    %rax,%r13
      CPU_SET(curcpu, sendercpu);
    12ed:	b8 01 00 00 00       	mov    $0x1,%eax
    12f2:	48 8d 35 37 0d 00 00 	lea    0xd37(%rip),%rsi        # 2030 <_IO_stdin_used+0x30>
    12f9:	48 d3 e0             	shl    %cl,%rax
    12fc:	49 09 45 00          	or     %rax,0x0(%r13)
      curcpu += coreinterval;
    1300:	8d 43 02             	lea    0x2(%rbx),%eax
    1303:	89 c1                	mov    %eax,%ecx
    1305:	89 04 24             	mov    %eax,(%rsp)
    1308:	31 c0                	xor    %eax,%eax
    130a:	e8 61 fe ff ff       	call   1170 <__printf_chk@plt>
      printf("assigning sender %d to core %d\n", n, curcpu);
       
      thread_data[n].thread_index = n;
      thread_data[n].cpu_set = sendercpu;
      thread_data[n].mode = WRITER;
      thread_data[n].multiple = seq[sender_index % writers_count];
    130f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
      thread_data[n].cpu_set = sendercpu;
    1314:	4c 89 ad a0 01 00 00 	mov    %r13,0x1a0(%rbp)
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].thread_tag = tag_index[sender_index];
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    131b:	be 08 00 00 00       	mov    $0x8,%esi
      thread_data[n].mode = WRITER;
    1320:	c7 85 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rbp)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    132a:	bf 02 00 00 00       	mov    $0x2,%edi
      thread_data[n].multiple = seq[sender_index % writers_count];
    132f:	42 8b 04 a0          	mov    (%rax,%r12,4),%eax
      thread_data[n].thread_index = n;
    1333:	44 89 65 00          	mov    %r12d,0x0(%rbp)
      thread_data[n].running = 1;
    1337:	c7 85 98 01 00 00 01 00 00 00 	movl   $0x1,0x198(%rbp)
      thread_data[n].multiple = seq[sender_index % writers_count];
    1341:	89 85 10 02 00 00    	mov    %eax,0x210(%rbp)
      thread_data[n].thread_tag = tag_index[sender_index];
    1347:	43 8b 04 a6          	mov    (%r14,%r12,4),%eax
      thread_data[n].size = buffer_size;
    134b:	48 c7 85 90 01 00 00 00 80 00 00 	movq   $0x8000,0x190(%rbp)
      thread_data[n].thread_tag = tag_index[sender_index];
    1356:	89 85 14 02 00 00    	mov    %eax,0x214(%rbp)
      thread_data[n].end = 0;
    135c:	c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbp)
      thread_data[n].sender = &thread_data[sender];
    1366:	4c 89 7d 08          	mov    %r15,0x8(%rbp)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    136a:	e8 f1 fd ff ff       	call   1160 <calloc@plt>
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    136f:	be 00 02 00 00       	mov    $0x200,%esi
    1374:	bf 00 80 00 00       	mov    $0x8000,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1379:	48 89 85 00 02 00 00 	mov    %rax,0x200(%rbp)
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    1380:	e8 db fd ff ff       	call   1160 <calloc@plt>
    1385:	48 89 45 18          	mov    %rax,0x18(%rbp)
      for (int k = 0 ; k < buffer_size ; k++) {
    1389:	48 8d 98 80 00 00 00 	lea    0x80(%rax),%rbx
    1390:	4c 8d a8 80 00 00 01 	lea    0x1000080(%rax),%r13
    1397:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
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
    13d3:	4c 39 eb             	cmp    %r13,%rbx
    13d6:	75 c8                	jne    13a0 <main+0x1e0>
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    13d8:	49 83 c4 01          	add    $0x1,%r12
    13dc:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    13e3:	bb 02 00 00 00       	mov    $0x2,%ebx
      }
      thread_data[n].other_count = other_count;
    13e8:	c7 45 88 02 00 00 00 	movl   $0x2,-0x78(%rbp)
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    13ef:	83 3c 24 04          	cmpl   $0x4,(%rsp)
    13f3:	0f 85 d8 fe ff ff    	jne    12d1 <main+0x111>
    13f9:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    13fe:	49 8d 87 00 05 00 00 	lea    0x500(%r15),%rax
    1405:	45 31 f6             	xor    %r14d,%r14d
    1408:	66 49 0f 6e d7       	movq   %r15,%xmm2
    140d:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    1412:	66 0f 6c d2          	punpcklqdq %xmm2,%xmm2
    1416:	49 89 c4             	mov    %rax,%r12
    1419:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    141e:	4c 89 f3             	mov    %r14,%rbx
    1421:	44 8b 34 24          	mov    (%rsp),%r14d
    1425:	0f 29 54 24 10       	movaps %xmm2,0x10(%rsp)
    142a:	8d 6b 02             	lea    0x2(%rbx),%ebp
      thread_data[j].thread_index = j;
      thread_data[j].reader_index = receiver_index;
      thread_data[j].multiple = receiver_index % other_count;
      thread_data[j].other_count = other_count;
     
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    142d:	be 80 00 00 00       	mov    $0x80,%esi
    1432:	bf 01 00 00 00       	mov    $0x1,%edi
    1437:	89 1c 24             	mov    %ebx,(%rsp)
      thread_data[j].thread_index = j;
    143a:	41 89 2c 24          	mov    %ebp,(%r12)
      thread_data[j].reader_index = receiver_index;
    143e:	41 89 9c 24 0c 02 00 00 	mov    %ebx,0x20c(%r12)
      thread_data[j].multiple = receiver_index % other_count;
    1446:	41 89 9c 24 10 02 00 00 	mov    %ebx,0x210(%r12)
      thread_data[j].other_count = other_count;
    144e:	41 c7 84 24 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%r12)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    145a:	e8 01 fd ff ff       	call   1160 <calloc@plt>
      CPU_ZERO(receivercpu);
      CPU_SET(curcpu, receivercpu);
    145f:	44 89 f1             	mov    %r14d,%ecx
      curcpu += coreinterval;
    1462:	41 83 c6 02          	add    $0x2,%r14d
    1466:	89 ea                	mov    %ebp,%edx
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1468:	49 89 c5             	mov    %rax,%r13
      CPU_SET(curcpu, receivercpu);
    146b:	b8 01 00 00 00       	mov    $0x1,%eax
    1470:	48 8d 35 d9 0b 00 00 	lea    0xbd9(%rip),%rsi        # 2050 <_IO_stdin_used+0x50>
    1477:	bf 01 00 00 00       	mov    $0x1,%edi
    147c:	48 d3 e0             	shl    %cl,%rax
    147f:	49 09 45 00          	or     %rax,0x0(%r13)
    1483:	44 89 f1             	mov    %r14d,%ecx
    1486:	31 c0                	xor    %eax,%eax
    1488:	e8 e3 fc ff ff       	call   1170 <__printf_chk@plt>
      printf("assigning receiver %d to core %d\n", j, curcpu);
      thread_data[j].cpu_set = receivercpu;
    148d:	4d 89 ac 24 a0 01 00 00 	mov    %r13,0x1a0(%r12)
      thread_data[j].running = 1;
    1495:	41 c7 84 24 98 01 00 00 01 00 00 00 	movl   $0x1,0x198(%r12)
      thread_data[j].mode = READER;
    14a1:	41 c7 84 24 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%r12)
      if (j == receiver) {
    14ad:	83 fd 02             	cmp    $0x2,%ebp
    14b0:	0f 84 fe 02 00 00    	je     17b4 <main+0x5f4>
        for (int n = 0 ; n < buffer_size ; n++) {
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
        }
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
    14b6:	66 0f 6f 4c 24 10    	movdqa 0x10(%rsp),%xmm1
    14bc:	8b 2c 24             	mov    (%rsp),%ebp
    14bf:	31 c9                	xor    %ecx,%ecx
    14c1:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    14c6:	49 8b 87 00 02 00 00 	mov    0x200(%r15),%rax
    14cd:	48 8d 35 a4 0b 00 00 	lea    0xba4(%rip),%rsi        # 2078 <_IO_stdin_used+0x78>
      thread_data[j].size = buffer_size;
    14d4:	49 c7 84 24 90 01 00 00 00 80 00 00 	movq   $0x8000,0x190(%r12)
      thread_data[j].start = 0;
    14e0:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
    14ec:	89 ea                	mov    %ebp,%edx
      thread_data[j].readers = thread_data[sender].readers;
    14ee:	49 89 84 24 00 02 00 00 	mov    %rax,0x200(%r12)
    14f6:	31 c0                	xor    %eax,%eax
      thread_data[j].other_count = other_count;
    14f8:	41 c7 84 24 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%r12)
      thread_data[j].sender = &thread_data[sender];
    1504:	41 0f 11 4c 24 08    	movups %xmm1,0x8(%r12)
    150a:	e8 61 fc ff ff       	call   1170 <__printf_chk@plt>
      // printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        printf("assigned reader %d to sender %d\n", receiver_index, n);
        thread_data[n].readers[receiver_index] = &thread_data[j];
    150f:	49 8b 87 00 02 00 00 	mov    0x200(%r15),%rax
    1516:	89 ea                	mov    %ebp,%edx
    1518:	b9 01 00 00 00       	mov    $0x1,%ecx
    151d:	48 8d 35 54 0b 00 00 	lea    0xb54(%rip),%rsi        # 2078 <_IO_stdin_used+0x78>
    1524:	bf 01 00 00 00       	mov    $0x1,%edi
    1529:	4c 89 24 d8          	mov    %r12,(%rax,%rbx,8)
    152d:	31 c0                	xor    %eax,%eax
    152f:	e8 3c fc ff ff       	call   1170 <__printf_chk@plt>
    1534:	49 8b 87 80 04 00 00 	mov    0x480(%r15),%rax
    153b:	4c 89 24 d8          	mov    %r12,(%rax,%rbx,8)
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    153f:	49 81 c4 80 02 00 00 	add    $0x280,%r12
    1546:	48 85 db             	test   %rbx,%rbx
    1549:	75 0a                	jne    1555 <main+0x395>
    154b:	bb 01 00 00 00       	mov    $0x1,%ebx
    1550:	e9 d5 fe ff ff       	jmp    142a <main+0x26a>
    1555:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
      }
    }
    curcpu = 0;
    // printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    155a:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    155d:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
      if (ret) {
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1562:	4c 89 3c 24          	mov    %r15,(%rsp)
    1566:	4c 8d 73 70          	lea    0x70(%rbx),%r14
    156a:	4c 8d a3 e0 00 00 00 	lea    0xe0(%rbx),%r12
  param.sched_priority = 0;
    1571:	c7 44 24 3c 00 00 00 00 	movl   $0x0,0x3c(%rsp)
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1579:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
    157e:	4c 8d 2d ab 03 00 00 	lea    0x3ab(%rip),%r13        # 1930 <disruptor_thread>
    1585:	48 8d 68 10          	lea    0x10(%rax),%rbp
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    1589:	31 f6                	xor    %esi,%esi
    158b:	4c 89 f7             	mov    %r14,%rdi
    158e:	e8 bd fb ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    1593:	85 c0                	test   %eax,%eax
    1595:	0f 85 6c 02 00 00    	jne    1807 <main+0x647>
      ret = pthread_attr_setschedparam(&attr[j], &param);
    159b:	48 8d 74 24 3c       	lea    0x3c(%rsp),%rsi
    15a0:	4c 89 f7             	mov    %r14,%rdi
    15a3:	e8 e8 fb ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    15a8:	85 c0                	test   %eax,%eax
    15aa:	0f 85 72 02 00 00    	jne    1822 <main+0x662>
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    15b0:	4c 89 f9             	mov    %r15,%rcx
    15b3:	4c 89 f6             	mov    %r14,%rsi
    15b6:	48 89 ef             	mov    %rbp,%rdi
    15b9:	4c 89 ea             	mov    %r13,%rdx
    15bc:	e8 bf fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    15c1:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15c5:	49 83 c6 38          	add    $0x38,%r14
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    15c9:	49 8b 97 a0 01 00 00 	mov    0x1a0(%r15),%rdx
    15d0:	be 08 00 00 00       	mov    $0x8,%esi
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15d5:	48 83 c5 08          	add    $0x8,%rbp
    15d9:	49 81 c7 80 02 00 00 	add    $0x280,%r15
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    15e0:	e8 1b fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15e5:	4d 39 e6             	cmp    %r12,%r14
    15e8:	75 9f                	jne    1589 <main+0x3c9>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    15ea:	31 f6                	xor    %esi,%esi
    15ec:	48 89 df             	mov    %rbx,%rdi
    15ef:	4c 8b 3c 24          	mov    (%rsp),%r15
    15f3:	e8 58 fb ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    15f8:	85 c0                	test   %eax,%eax
    15fa:	0f 85 07 02 00 00    	jne    1807 <main+0x647>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1600:	48 8d 74 24 38       	lea    0x38(%rsp),%rsi
    1605:	48 89 df             	mov    %rbx,%rdi
      param2.sched_priority = 0;
    1608:	c7 44 24 38 00 00 00 00 	movl   $0x0,0x38(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1610:	e8 7b fb ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1615:	85 c0                	test   %eax,%eax
    1617:	0f 85 05 02 00 00    	jne    1822 <main+0x662>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    161d:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    1622:	4c 89 f9             	mov    %r15,%rcx
    1625:	48 89 de             	mov    %rbx,%rsi
    1628:	4c 89 ea             	mov    %r13,%rdx
    162b:	48 8d 2d ed 0a 00 00 	lea    0xaed(%rip),%rbp        # 211f <_IO_stdin_used+0x11f>
    1632:	4c 89 f7             	mov    %r14,%rdi
    1635:	e8 46 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    163a:	49 8b 97 a0 01 00 00 	mov    0x1a0(%r15),%rdx
    1641:	49 8b 3e             	mov    (%r14),%rdi
    1644:	be 08 00 00 00       	mov    $0x8,%esi
    1649:	e8 b2 fa ff ff       	call   1100 <pthread_setaffinity_np@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    164e:	48 8d 73 38          	lea    0x38(%rbx),%rsi
    1652:	49 8d 7e 08          	lea    0x8(%r14),%rdi
    1656:	4c 89 ea             	mov    %r13,%rdx
    1659:	49 8d 8f 80 02 00 00 	lea    0x280(%r15),%rcx
    void * res1;
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    1660:	31 db                	xor    %ebx,%ebx
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    1662:	e8 19 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    1667:	49 8b 97 20 04 00 00 	mov    0x420(%r15),%rdx
    166e:	49 8b 7e 08          	mov    0x8(%r14),%rdi
    1672:	be 08 00 00 00       	mov    $0x8,%esi
    1677:	e8 84 fa ff ff       	call   1100 <pthread_setaffinity_np@plt>
  nanosleep(&preempt , &rem2);
    167c:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    1681:	48 8d 7c 24 50       	lea    0x50(%rsp),%rdi
  struct timespec preempt = {
    1686:	66 0f 6f 05 c2 0a 00 00 	movdqa 0xac2(%rip),%xmm0        # 2150 <_IO_stdin_used+0x150>
    168e:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&preempt , &rem2);
    1693:	e8 a8 fa ff ff       	call   1140 <nanosleep@plt>
      pthread_join(thread[n], res1);
    1698:	49 8b 3e             	mov    (%r14),%rdi
    169b:	48 89 de             	mov    %rbx,%rsi
    thread_data[sender].running = 0;
    169e:	41 c7 87 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r15)
      thread_data[j].running = 0;
    16a9:	41 c7 87 98 06 00 00 00 00 00 00 	movl   $0x0,0x698(%r15)
    16b4:	41 c7 87 18 09 00 00 00 00 00 00 	movl   $0x0,0x918(%r15)
      thread_data[n].running = 0;
    16bf:	41 c7 87 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r15)
    16ca:	41 c7 87 18 04 00 00 00 00 00 00 	movl   $0x0,0x418(%r15)
      pthread_join(thread[n], res1);
    16d5:	e8 d6 fa ff ff       	call   11b0 <pthread_join@plt>
    16da:	49 8b 7e 08          	mov    0x8(%r14),%rdi
    16de:	48 89 de             	mov    %rbx,%rsi
    16e1:	e8 ca fa ff ff       	call   11b0 <pthread_join@plt>
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    16e6:	49 8b 7e 10          	mov    0x10(%r14),%rdi
    16ea:	48 89 de             	mov    %rbx,%rsi
    16ed:	e8 be fa ff ff       	call   11b0 <pthread_join@plt>
    16f2:	49 8b 7e 18          	mov    0x18(%r14),%rdi
    16f6:	48 89 de             	mov    %rbx,%rsi
    16f9:	e8 b2 fa ff ff       	call   11b0 <pthread_join@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    // printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    16fe:	eb 10                	jmp    1710 <main+0x550>
    1700:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
    1707:	48 81 fb 00 00 00 01 	cmp    $0x1000000,%rbx
    170e:	74 7d                	je     178d <main+0x5cd>
      int compcount = 0;
      for (int n = 0 ; n < other_count ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    1710:	49 8b 47 18          	mov    0x18(%r15),%rax
    1714:	48 01 d8             	add    %rbx,%rax
    1717:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
    171e:	83 3a 01             	cmpl   $0x1,(%rdx)
    1721:	75 dd                	jne    1700 <main+0x540>
    1723:	83 7a 04 01          	cmpl   $0x1,0x4(%rdx)
    1727:	75 d7                	jne    1700 <main+0x540>
      // printf("%d\n", compcount);
      if (compcount == other_count) {
      for (int n = 0 ; n < other_count ; n++) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
          struct timespec end = thread_data[sender].data[y].end[n];
    1729:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    1730:	48 89 ee             	mov    %rbp,%rsi
    1733:	bf 01 00 00 00       	mov    $0x1,%edi
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    1738:	4c 8b 42 08          	mov    0x8(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    173c:	48 8b 0a             	mov    (%rdx),%rcx
    173f:	31 d2                	xor    %edx,%edx
    1741:	48 2b 08             	sub    (%rax),%rcx
    1744:	4c 2b 40 08          	sub    0x8(%rax),%r8
    1748:	31 c0                	xor    %eax,%eax
    174a:	e8 21 fa ff ff       	call   1170 <__printf_chk@plt>
          struct timespec start = thread_data[sender].data[y].start;
    174f:	49 8b 47 18          	mov    0x18(%r15),%rax
    1753:	48 89 ee             	mov    %rbp,%rsi
    1756:	bf 01 00 00 00       	mov    $0x1,%edi
    175b:	48 01 d8             	add    %rbx,%rax
    for (int y = 0 ; y < buffer_size; y++) {
    175e:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
          struct timespec end = thread_data[sender].data[y].end[n];
    1765:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    176c:	4c 8b 42 18          	mov    0x18(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    1770:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    1774:	31 d2                	xor    %edx,%edx
    1776:	48 2b 08             	sub    (%rax),%rcx
    1779:	4c 2b 40 08          	sub    0x8(%rax),%r8
    177d:	31 c0                	xor    %eax,%eax
    177f:	e8 ec f9 ff ff       	call   1170 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    1784:	48 81 fb 00 00 00 01 	cmp    $0x1000000,%rbx
    178b:	75 83                	jne    1710 <main+0x550>
    }
    // printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    178d:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    1795:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    179e:	75 7d                	jne    181d <main+0x65d>
    17a0:	48 81 c4 98 00 00 00 	add    $0x98,%rsp
    17a7:	31 c0                	xor    %eax,%eax
    17a9:	5b                   	pop    %rbx
    17aa:	5d                   	pop    %rbp
    17ab:	41 5c                	pop    %r12
    17ad:	41 5d                	pop    %r13
    17af:	41 5e                	pop    %r14
    17b1:	41 5f                	pop    %r15
    17b3:	c3                   	ret
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    17b4:	be 00 02 00 00       	mov    $0x200,%esi
    17b9:	bf 00 80 00 00       	mov    $0x8000,%edi
    17be:	e8 9d f9 ff ff       	call   1160 <calloc@plt>
    17c3:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    17c8:	49 89 c5             	mov    %rax,%r13
        for (int n = 0 ; n < buffer_size ; n++) {
    17cb:	48 8d a8 00 01 00 00 	lea    0x100(%rax),%rbp
    17d2:	49 81 c5 00 01 00 01 	add    $0x1000100,%r13
    17d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    17e0:	be 04 00 00 00       	mov    $0x4,%esi
    17e5:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    17ea:	48 81 c5 00 02 00 00 	add    $0x200,%rbp
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    17f1:	e8 6a f9 ff ff       	call   1160 <calloc@plt>
    17f6:	48 89 85 00 fe ff ff 	mov    %rax,-0x200(%rbp)
        for (int n = 0 ; n < buffer_size ; n++) {
    17fd:	4c 39 ed             	cmp    %r13,%rbp
    1800:	75 de                	jne    17e0 <main+0x620>
    1802:	e9 af fc ff ff       	jmp    14b6 <main+0x2f6>
    1807:	48 8d 3d d6 08 00 00 	lea    0x8d6(%rip),%rdi        # 20e4 <_IO_stdin_used+0xe4>
    180e:	e8 fd f8 ff ff       	call   1110 <puts@plt>
               exit(1);
    1813:	bf 01 00 00 00       	mov    $0x1,%edi
    1818:	e8 83 f9 ff ff       	call   11a0 <exit@plt>
}
    181d:	e8 0e f9 ff ff       	call   1130 <__stack_chk_fail@plt>
    1822:	48 8d 3d d9 08 00 00 	lea    0x8d9(%rip),%rdi        # 2102 <_IO_stdin_used+0x102>
    1829:	e8 e2 f8 ff ff       	call   1110 <puts@plt>
              exit(1);
    182e:	bf 01 00 00 00       	mov    $0x1,%edi
    1833:	e8 68 f9 ff ff       	call   11a0 <exit@plt>
    1838:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000001840 <_start>:
    1840:	f3 0f 1e fa          	endbr64
    1844:	31 ed                	xor    %ebp,%ebp
    1846:	49 89 d1             	mov    %rdx,%r9
    1849:	5e                   	pop    %rsi
    184a:	48 89 e2             	mov    %rsp,%rdx
    184d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1851:	50                   	push   %rax
    1852:	54                   	push   %rsp
    1853:	45 31 c0             	xor    %r8d,%r8d
    1856:	31 c9                	xor    %ecx,%ecx
    1858:	48 8d 3d 61 f9 ff ff 	lea    -0x69f(%rip),%rdi        # 11c0 <main>
    185f:	ff 15 73 27 00 00    	call   *0x2773(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1865:	f4                   	hlt
    1866:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001870 <deregister_tm_clones>:
    1870:	48 8d 3d 99 27 00 00 	lea    0x2799(%rip),%rdi        # 4010 <__TMC_END__>
    1877:	48 8d 05 92 27 00 00 	lea    0x2792(%rip),%rax        # 4010 <__TMC_END__>
    187e:	48 39 f8             	cmp    %rdi,%rax
    1881:	74 15                	je     1898 <deregister_tm_clones+0x28>
    1883:	48 8b 05 56 27 00 00 	mov    0x2756(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    188a:	48 85 c0             	test   %rax,%rax
    188d:	74 09                	je     1898 <deregister_tm_clones+0x28>
    188f:	ff e0                	jmp    *%rax
    1891:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1898:	c3                   	ret
    1899:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018a0 <register_tm_clones>:
    18a0:	48 8d 3d 69 27 00 00 	lea    0x2769(%rip),%rdi        # 4010 <__TMC_END__>
    18a7:	48 8d 35 62 27 00 00 	lea    0x2762(%rip),%rsi        # 4010 <__TMC_END__>
    18ae:	48 29 fe             	sub    %rdi,%rsi
    18b1:	48 89 f0             	mov    %rsi,%rax
    18b4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    18b8:	48 c1 f8 03          	sar    $0x3,%rax
    18bc:	48 01 c6             	add    %rax,%rsi
    18bf:	48 d1 fe             	sar    %rsi
    18c2:	74 14                	je     18d8 <register_tm_clones+0x38>
    18c4:	48 8b 05 25 27 00 00 	mov    0x2725(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    18cb:	48 85 c0             	test   %rax,%rax
    18ce:	74 08                	je     18d8 <register_tm_clones+0x38>
    18d0:	ff e0                	jmp    *%rax
    18d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    18d8:	c3                   	ret
    18d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018e0 <__do_global_dtors_aux>:
    18e0:	f3 0f 1e fa          	endbr64
    18e4:	80 3d 25 27 00 00 00 	cmpb   $0x0,0x2725(%rip)        # 4010 <__TMC_END__>
    18eb:	75 2b                	jne    1918 <__do_global_dtors_aux+0x38>
    18ed:	55                   	push   %rbp
    18ee:	48 83 3d 02 27 00 00 00 	cmpq   $0x0,0x2702(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    18f6:	48 89 e5             	mov    %rsp,%rbp
    18f9:	74 0c                	je     1907 <__do_global_dtors_aux+0x27>
    18fb:	48 8b 3d 06 27 00 00 	mov    0x2706(%rip),%rdi        # 4008 <__dso_handle>
    1902:	e8 e9 f7 ff ff       	call   10f0 <__cxa_finalize@plt>
    1907:	e8 64 ff ff ff       	call   1870 <deregister_tm_clones>
    190c:	c6 05 fd 26 00 00 01 	movb   $0x1,0x26fd(%rip)        # 4010 <__TMC_END__>
    1913:	5d                   	pop    %rbp
    1914:	c3                   	ret
    1915:	0f 1f 00             	nopl   (%rax)
    1918:	c3                   	ret
    1919:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001920 <frame_dummy>:
    1920:	f3 0f 1e fa          	endbr64
    1924:	e9 77 ff ff ff       	jmp    18a0 <register_tm_clones>
    1929:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001930 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    1930:	f3 0f 1e fa          	endbr64
    1934:	41 56                	push   %r14
    1936:	41 55                	push   %r13
    1938:	41 54                	push   %r12
    193a:	55                   	push   %rbp
    193b:	53                   	push   %rbx
  if (data->mode == WRITER) {
    193c:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
void * disruptor_thread(void * arg) {
    1942:	48 89 fb             	mov    %rdi,%rbx
  if (data->mode == WRITER) {
    1945:	85 c0                	test   %eax,%eax
    1947:	0f 85 15 01 00 00    	jne    1a62 <disruptor_thread+0x132>
    struct Thread *me = data->sender;
    194d:	4c 8b 67 08          	mov    0x8(%rdi),%r12
    while (data->running == 1) {
    1951:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1958:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    195e:	83 f8 01             	cmp    $0x1,%eax
    1961:	0f 85 f0 00 00 00    	jne    1a57 <disruptor_thread+0x127>
      asm volatile ("sfence" ::: "memory");
    1967:	0f ae f8             	sfence
      long pos = (((me->realend & END_MASK) >> 32) + 1) % data->size;
    196a:	49 8b ac 24 80 01 00 00 	mov    0x180(%r12),%rbp
    1972:	49 89 e8             	mov    %rbp,%r8
    1975:	49 c1 f8 20          	sar    $0x20,%r8
    1979:	41 81 e0 ff ff ff 0f 	and    $0xfffffff,%r8d
    1980:	49 83 c0 01          	add    $0x1,%r8
    1984:	4c 89 c0             	mov    %r8,%rax
    1987:	48 99                	cqto
    1989:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
      for (int x  = 0 ; x < data->other_count; x++) {
    1990:	48 63 83 08 02 00 00 	movslq 0x208(%rbx),%rax
    1997:	85 c0                	test   %eax,%eax
    1999:	0f 8e 05 01 00 00    	jle    1aa4 <disruptor_thread+0x174>
    199f:	48 8b 8b 00 02 00 00 	mov    0x200(%rbx),%rcx
    19a6:	48 8d 3c c1          	lea    (%rcx,%rax,8),%rdi
    19aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (pos == data->readers[x]->start) {
    19b0:	48 8b 31             	mov    (%rcx),%rsi
    19b3:	48 63 b6 80 00 00 00 	movslq 0x80(%rsi),%rsi
    19ba:	48 39 d6             	cmp    %rdx,%rsi
    19bd:	74 99                	je     1958 <disruptor_thread+0x28>
      for (int x  = 0 ; x < data->other_count; x++) {
    19bf:	48 83 c1 08          	add    $0x8,%rcx
    19c3:	48 39 cf             	cmp    %rcx,%rdi
    19c6:	75 e8                	jne    19b0 <disruptor_thread+0x80>
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    19c8:	4c 89 c0             	mov    %r8,%rax
                me->data[changed].complete[x] = 0;
    19cb:	49 8b 74 24 18       	mov    0x18(%r12),%rsi
              long new = (data->thread_tag) | (changed << 32);
    19d0:	4c 63 b3 14 02 00 00 	movslq 0x214(%rbx),%r14
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    19d7:	48 99                	cqto
    19d9:	49 f7 bc 24 90 01 00 00 	idivq  0x190(%r12)
              long new = (data->thread_tag) | (changed << 32);
    19e1:	48 89 d0             	mov    %rdx,%rax
                me->data[changed].complete[x] = 0;
    19e4:	48 c1 e2 09          	shl    $0x9,%rdx
    19e8:	48 01 d6             	add    %rdx,%rsi
              long new = (data->thread_tag) | (changed << 32);
    19eb:	48 c1 e0 20          	shl    $0x20,%rax
                me->data[changed].complete[x] = 0;
    19ef:	49 89 d5             	mov    %rdx,%r13
    19f2:	48 8b 96 00 01 00 00 	mov    0x100(%rsi),%rdx
              long new = (data->thread_tag) | (changed << 32);
    19f9:	49 09 c6             	or     %rax,%r14
                me->data[changed].complete[x] = 0;
    19fc:	31 c0                	xor    %eax,%eax
    19fe:	66 90                	xchg   %ax,%ax
    1a00:	c7 04 82 00 00 00 00 	movl   $0x0,(%rdx,%rax,4)
              for (int x = 0 ; x < data->other_count; x++) {
    1a07:	48 83 c0 01          	add    $0x1,%rax
    1a0b:	39 83 08 02 00 00    	cmp    %eax,0x208(%rbx)
    1a11:	7f ed                	jg     1a00 <disruptor_thread+0xd0>
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1a13:	bf 04 00 00 00       	mov    $0x4,%edi
    1a18:	e8 03 f7 ff ff       	call   1120 <clock_gettime@plt>
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED))) {
    1a1d:	49 8d 8c 24 80 01 00 00 	lea    0x180(%r12),%rcx
    1a25:	48 89 e8             	mov    %rbp,%rax
    1a28:	f0 4c 0f b1 31       	lock cmpxchg %r14,(%rcx)
    1a2d:	0f 85 0b 01 00 00    	jne    1b3e <disruptor_thread+0x20e>
                me->data[changed].written = me->other_count;
    1a33:	49 8b 44 24 18       	mov    0x18(%r12),%rax
    1a38:	41 8b 94 24 08 02 00 00 	mov    0x208(%r12),%edx
    1a40:	42 89 94 28 80 01 00 00 	mov    %edx,0x180(%rax,%r13,1)
    while (data->running == 1) {
    1a48:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    1a4e:	83 f8 01             	cmp    $0x1,%eax
    1a51:	0f 84 10 ff ff ff    	je     1967 <disruptor_thread+0x37>
}
    1a57:	5b                   	pop    %rbx
    1a58:	31 c0                	xor    %eax,%eax
    1a5a:	5d                   	pop    %rbp
    1a5b:	41 5c                	pop    %r12
    1a5d:	41 5d                	pop    %r13
    1a5f:	41 5e                	pop    %r14
    1a61:	c3                   	ret
  } else if (data->mode == READER) {
    1a62:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
    1a68:	83 f8 01             	cmp    $0x1,%eax
    1a6b:	75 ea                	jne    1a57 <disruptor_thread+0x127>
    struct Thread *sender = data->sender;
    1a6d:	4c 8b 67 08          	mov    0x8(%rdi),%r12
    struct Snapshot * rdata = sender->data;
    1a71:	4d 8b 74 24 18       	mov    0x18(%r12),%r14
    while (data->running == 1) {
    1a76:	eb 1f                	jmp    1a97 <disruptor_thread+0x167>
    1a78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      int pos = ((sender->realend & END_MASK) >> 32);
    1a80:	49 63 84 24 84 01 00 00 	movslq 0x184(%r12),%rax
      if (pos == data->start) {
    1a88:	8b ab 80 00 00 00    	mov    0x80(%rbx),%ebp
      int pos = ((sender->realend & END_MASK) >> 32);
    1a8e:	25 ff ff ff 0f       	and    $0xfffffff,%eax
      if (pos == data->start) {
    1a93:	39 c5                	cmp    %eax,%ebp
    1a95:	75 3f                	jne    1ad6 <disruptor_thread+0x1a6>
    while (data->running == 1) {
    1a97:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    1a9d:	83 f8 01             	cmp    $0x1,%eax
    1aa0:	74 de                	je     1a80 <disruptor_thread+0x150>
    1aa2:	eb b3                	jmp    1a57 <disruptor_thread+0x127>
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1aa4:	4c 89 c0             	mov    %r8,%rax
              long new = (data->thread_tag) | (changed << 32);
    1aa7:	4c 63 b3 14 02 00 00 	movslq 0x214(%rbx),%r14
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1aae:	49 8b 74 24 18       	mov    0x18(%r12),%rsi
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1ab3:	48 99                	cqto
    1ab5:	49 f7 bc 24 90 01 00 00 	idivq  0x190(%r12)
              long new = (data->thread_tag) | (changed << 32);
    1abd:	48 89 d0             	mov    %rdx,%rax
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1ac0:	48 c1 e2 09          	shl    $0x9,%rdx
              long new = (data->thread_tag) | (changed << 32);
    1ac4:	48 c1 e0 20          	shl    $0x20,%rax
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1ac8:	49 89 d5             	mov    %rdx,%r13
    1acb:	48 01 d6             	add    %rdx,%rsi
              long new = (data->thread_tag) | (changed << 32);
    1ace:	49 09 c6             	or     %rax,%r14
              for (int x = 0 ; x < data->other_count; x++) {
    1ad1:	e9 3d ff ff ff       	jmp    1a13 <disruptor_thread+0xe3>
          if (rdata[changed].written > 0) {
    1ad6:	4c 63 ed             	movslq %ebp,%r13
    1ad9:	49 c1 e5 09          	shl    $0x9,%r13
    1add:	4d 01 f5             	add    %r14,%r13
    1ae0:	41 8b 85 80 01 00 00 	mov    0x180(%r13),%eax
    1ae7:	85 c0                	test   %eax,%eax
    1ae9:	7e ac                	jle    1a97 <disruptor_thread+0x167>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1aeb:	48 63 b3 0c 02 00 00 	movslq 0x20c(%rbx),%rsi
    1af2:	bf 04 00 00 00       	mov    $0x4,%edi
    1af7:	48 c1 e6 04          	shl    $0x4,%rsi
    1afb:	49 03 b5 80 00 00 00 	add    0x80(%r13),%rsi
    1b02:	e8 19 f6 ff ff       	call   1120 <clock_gettime@plt>
              rdata[changed].complete[data->reader_index] = 1;
    1b07:	49 8b 85 00 01 00 00 	mov    0x100(%r13),%rax
    1b0e:	48 63 93 0c 02 00 00 	movslq 0x20c(%rbx),%rdx
    1b15:	c7 04 90 01 00 00 00 	movl   $0x1,(%rax,%rdx,4)
              data->start = (changed + 1) % data->size;
    1b1c:	8d 45 01             	lea    0x1(%rbp),%eax
    1b1f:	48 98                	cltq
    1b21:	48 99                	cqto
    1b23:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
    1b2a:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
              __atomic_sub_fetch(&rdata[changed].written, 1, __ATOMIC_RELAXED);
    1b30:	f0 41 83 ad 80 01 00 00 01 	lock subl $0x1,0x180(%r13)
    1b39:	e9 59 ff ff ff       	jmp    1a97 <disruptor_thread+0x167>
                original = me->realend;
    1b3e:	49 8b b4 24 80 01 00 00 	mov    0x180(%r12),%rsi
                new = (data->thread_tag) | (changed << 32);
    1b46:	48 63 bb 14 02 00 00 	movslq 0x214(%rbx),%rdi
                changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1b4d:	48 89 f0             	mov    %rsi,%rax
    1b50:	48 c1 f8 20          	sar    $0x20,%rax
    1b54:	25 ff ff ff 0f       	and    $0xfffffff,%eax
    1b59:	48 83 c0 01          	add    $0x1,%rax
    1b5d:	48 99                	cqto
    1b5f:	49 f7 bc 24 90 01 00 00 	idivq  0x190(%r12)
                new = (data->thread_tag) | (changed << 32);
    1b67:	48 89 d0             	mov    %rdx,%rax
    1b6a:	48 c1 e0 20          	shl    $0x20,%rax
    1b6e:	48 09 c7             	or     %rax,%rdi
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED))) {
    1b71:	48 89 f0             	mov    %rsi,%rax
    1b74:	f0 48 0f b1 39       	lock cmpxchg %rdi,(%rcx)
    1b79:	75 c3                	jne    1b3e <disruptor_thread+0x20e>
                me->data[changed].written = me->other_count;
    1b7b:	48 c1 e2 09          	shl    $0x9,%rdx
    1b7f:	49 89 d5             	mov    %rdx,%r13
    1b82:	e9 ac fe ff ff       	jmp    1a33 <disruptor_thread+0x103>
    1b87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

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
