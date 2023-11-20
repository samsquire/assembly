
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
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int receiver2 = receiver + 1; 
    int seq[] = {1, 2, 5};
    int tag_index[] = {1, 5, 5};
    11de:	45 31 f6             	xor    %r14d,%r14d
int main() {
    11e1:	41 55                	push   %r13
    11e3:	41 54                	push   %r12
    11e5:	55                   	push   %rbp
    11e6:	53                   	push   %rbx
    11e7:	48 81 ec 98 00 00 00 	sub    $0x98,%rsp
    11ee:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    11f7:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    11ff:	31 c0                	xor    %eax,%eax
    1201:	e8 6a ff ff ff       	call   1170 <__printf_chk@plt>
    1206:	ba 01 00 00 00       	mov    $0x1,%edx
    120b:	48 8d 35 17 0e 00 00 	lea    0xe17(%rip),%rsi        # 2029 <_IO_stdin_used+0x29>
    1212:	31 c0                	xor    %eax,%eax
    1214:	bf 01 00 00 00       	mov    $0x1,%edi
    1219:	e8 52 ff ff ff       	call   1170 <__printf_chk@plt>
    121e:	ba 02 00 00 00       	mov    $0x2,%edx
    1223:	48 8d 35 0f 0e 00 00 	lea    0xe0f(%rip),%rsi        # 2039 <_IO_stdin_used+0x39>
    122a:	31 c0                	xor    %eax,%eax
    122c:	bf 01 00 00 00       	mov    $0x1,%edi
    1231:	e8 3a ff ff ff       	call   1170 <__printf_chk@plt>
    1236:	ba 02 00 00 00       	mov    $0x2,%edx
    123b:	48 8d 35 09 0e 00 00 	lea    0xe09(%rip),%rsi        # 204b <_IO_stdin_used+0x4b>
    1242:	31 c0                	xor    %eax,%eax
    1244:	bf 01 00 00 00       	mov    $0x1,%edi
    1249:	e8 22 ff ff ff       	call   1170 <__printf_chk@plt>
    124e:	ba 04 00 00 00       	mov    $0x4,%edx
    1253:	48 8d 35 03 0e 00 00 	lea    0xe03(%rip),%rsi        # 205d <_IO_stdin_used+0x5d>
    125a:	31 c0                	xor    %eax,%eax
    125c:	bf 01 00 00 00       	mov    $0x1,%edi
    1261:	e8 0a ff ff ff       	call   1170 <__printf_chk@plt>
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1266:	be 80 02 00 00       	mov    $0x280,%esi
    126b:	bf 04 00 00 00       	mov    $0x4,%edi
    1270:	e8 eb fe ff ff       	call   1160 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1275:	be 38 00 00 00       	mov    $0x38,%esi
    127a:	bf 04 00 00 00       	mov    $0x4,%edi
    127f:	66 48 0f 6e c8       	movq   %rax,%xmm1
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1284:	48 89 c5             	mov    %rax,%rbp
    1287:	66 0f 6c c9          	punpcklqdq %xmm1,%xmm1
    128b:	49 89 ec             	mov    %rbp,%r12
    128e:	0f 29 0c 24          	movaps %xmm1,(%rsp)
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1292:	e8 c9 fe ff ff       	call   1160 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1297:	be 08 00 00 00       	mov    $0x8,%esi
    129c:	bf 04 00 00 00       	mov    $0x4,%edi
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12a1:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12a6:	e8 b5 fe ff ff       	call   1160 <calloc@plt>
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    12ab:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12b3:	49 89 c5             	mov    %rax,%r13
    int seq[] = {1, 2, 5};
    12b6:	48 8b 05 0b 0e 00 00 	mov    0xe0b(%rip),%rax        # 20c8 <_IO_stdin_used+0xc8>
    12bd:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    int tag_index[] = {1, 5, 5};
    12c2:	48 8b 05 07 0e 00 00 	mov    0xe07(%rip),%rax        # 20d0 <_IO_stdin_used+0xd0>
    12c9:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    12ce:	48 8d 44 24 68       	lea    0x68(%rsp),%rax
    12d3:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    12d8:	48 8d 44 24 78       	lea    0x78(%rsp),%rax
    12dd:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12e2:	be 80 00 00 00       	mov    $0x80,%esi
    12e7:	bf 01 00 00 00       	mov    $0x1,%edi
    12ec:	e8 6f fe ff ff       	call   1160 <calloc@plt>
      CPU_ZERO(sendercpu);
      CPU_SET(curcpu, sendercpu);
    12f1:	8b 74 24 10          	mov    0x10(%rsp),%esi
    12f5:	ba 01 00 00 00       	mov    $0x1,%edx
      curcpu += 2;
      // printf("assigning sender %d to core %d\n", n, curcpu);
       
      thread_data[n].thread_index = n;
      thread_data[n].cpu_set = sendercpu;
      thread_data[n].mode = WRITER;
    12fa:	41 c7 84 24 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%r12)
      thread_data[n].cpu_set = sendercpu;
    1306:	49 89 84 24 a0 01 00 00 	mov    %rax,0x1a0(%r12)
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].thread_tag = tag_index[sender_index];
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    130e:	bf 02 00 00 00       	mov    $0x2,%edi
      CPU_SET(curcpu, sendercpu);
    1313:	8d 0c 36             	lea    (%rsi,%rsi,1),%ecx
      thread_data[n].thread_index = n;
    1316:	41 89 34 24          	mov    %esi,(%r12)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    131a:	be 08 00 00 00       	mov    $0x8,%esi
      CPU_SET(curcpu, sendercpu);
    131f:	48 d3 e2             	shl    %cl,%rdx
    1322:	48 09 10             	or     %rdx,(%rax)
      thread_data[n].multiple = seq[sender_index % writers_count];
    1325:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
      thread_data[n].running = 1;
    132a:	41 c7 84 24 98 01 00 00 01 00 00 00 	movl   $0x1,0x198(%r12)
      thread_data[n].multiple = seq[sender_index % writers_count];
    1336:	42 8b 04 30          	mov    (%rax,%r14,1),%eax
      thread_data[n].sender = &thread_data[sender];
    133a:	49 89 6c 24 08       	mov    %rbp,0x8(%r12)
      thread_data[n].size = buffer_size;
    133f:	49 c7 84 24 90 01 00 00 00 80 00 00 	movq   $0x8000,0x190(%r12)
      thread_data[n].multiple = seq[sender_index % writers_count];
    134b:	41 89 84 24 10 02 00 00 	mov    %eax,0x210(%r12)
      thread_data[n].thread_tag = tag_index[sender_index];
    1353:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
      thread_data[n].end = 0;
    1358:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
      thread_data[n].thread_tag = tag_index[sender_index];
    1364:	42 8b 04 30          	mov    (%rax,%r14,1),%eax
    1368:	41 89 84 24 14 02 00 00 	mov    %eax,0x214(%r12)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1370:	e8 eb fd ff ff       	call   1160 <calloc@plt>
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    1375:	be 80 01 00 00       	mov    $0x180,%esi
    137a:	bf 00 80 00 00       	mov    $0x8000,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    137f:	49 89 84 24 00 02 00 00 	mov    %rax,0x200(%r12)
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    1387:	e8 d4 fd ff ff       	call   1160 <calloc@plt>
    138c:	49 89 44 24 18       	mov    %rax,0x18(%r12)
      for (int k = 0 ; k < buffer_size ; k++) {
    1391:	4c 8d b8 80 00 00 00 	lea    0x80(%rax),%r15
    1398:	48 8d 98 80 00 c0 00 	lea    0xc00080(%rax),%rbx
    139f:	90                   	nop
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13a0:	be 04 00 00 00       	mov    $0x4,%esi
    13a5:	bf 02 00 00 00       	mov    $0x2,%edi
      for (int k = 0 ; k < buffer_size ; k++) {
    13aa:	49 81 c7 80 01 00 00 	add    $0x180,%r15
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13b1:	e8 aa fd ff ff       	call   1160 <calloc@plt>
        thread_data[n].data[k].end = calloc(other_count, sizeof(int));
    13b6:	be 04 00 00 00       	mov    $0x4,%esi
    13bb:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13c0:	49 89 87 00 ff ff ff 	mov    %rax,-0x100(%r15)
        thread_data[n].data[k].end = calloc(other_count, sizeof(int));
    13c7:	e8 94 fd ff ff       	call   1160 <calloc@plt>
    13cc:	49 89 87 80 fe ff ff 	mov    %rax,-0x180(%r15)
      for (int k = 0 ; k < buffer_size ; k++) {
    13d3:	4c 39 fb             	cmp    %r15,%rbx
    13d6:	75 c8                	jne    13a0 <main+0x1e0>
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    13d8:	8b 44 24 10          	mov    0x10(%rsp),%eax
    13dc:	49 81 c4 80 02 00 00 	add    $0x280,%r12
    13e3:	49 83 c6 04          	add    $0x4,%r14
      }
      thread_data[n].other_count = other_count;
    13e7:	41 c7 44 24 88 02 00 00 00 	movl   $0x2,-0x78(%r12)
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    13f0:	85 c0                	test   %eax,%eax
    13f2:	75 0d                	jne    1401 <main+0x241>
    13f4:	c7 44 24 10 01 00 00 00 	movl   $0x1,0x10(%rsp)
    13fc:	e9 e1 fe ff ff       	jmp    12e2 <main+0x122>
    }

    // printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      thread_data[j].thread_index = j;
    1401:	c7 85 00 05 00 00 02 00 00 00 	movl   $0x2,0x500(%rbp)
      thread_data[j].reader_index = receiver_index;
      thread_data[j].multiple = receiver_index % other_count;
      thread_data[j].other_count = other_count;
     
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    140b:	be 80 00 00 00       	mov    $0x80,%esi
    1410:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].thread_index = j;
    1415:	48 8d 9d 00 05 00 00 	lea    0x500(%rbp),%rbx
      thread_data[j].multiple = receiver_index % other_count;
    141c:	c7 85 10 07 00 00 00 00 00 00 	movl   $0x0,0x710(%rbp)
      thread_data[j].other_count = other_count;
    1426:	48 c7 85 08 07 00 00 02 00 00 00 	movq   $0x2,0x708(%rbp)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1431:	e8 2a fd ff ff       	call   1160 <calloc@plt>
      // printf("assigning receiver %d to core %d\n", j, curcpu);
      thread_data[j].cpu_set = receivercpu;
      thread_data[j].running = 1;
      thread_data[j].mode = READER;
      if (j == receiver) {
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    1436:	be 80 01 00 00       	mov    $0x180,%esi
    143b:	bf 00 80 00 00       	mov    $0x8000,%edi
      thread_data[j].running = 1;
    1440:	c7 85 98 06 00 00 01 00 00 00 	movl   $0x1,0x698(%rbp)
      CPU_SET(curcpu, receivercpu);
    144a:	48 83 08 10          	orq    $0x10,(%rax)
      thread_data[j].cpu_set = receivercpu;
    144e:	48 89 85 a0 06 00 00 	mov    %rax,0x6a0(%rbp)
      thread_data[j].mode = READER;
    1455:	c7 85 88 06 00 00 01 00 00 00 	movl   $0x1,0x688(%rbp)
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    145f:	e8 fc fc ff ff       	call   1160 <calloc@plt>
    1464:	48 89 85 18 05 00 00 	mov    %rax,0x518(%rbp)
    146b:	49 89 c6             	mov    %rax,%r14
        for (int n = 0 ; n < buffer_size ; n++) {
    146e:	4c 8d a0 00 01 00 00 	lea    0x100(%rax),%r12
    1475:	49 81 c6 00 01 c0 00 	add    $0xc00100,%r14
    147c:	0f 1f 40 00          	nopl   0x0(%rax)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1480:	be 04 00 00 00       	mov    $0x4,%esi
    1485:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    148a:	49 81 c4 80 01 00 00 	add    $0x180,%r12
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    1491:	e8 ca fc ff ff       	call   1160 <calloc@plt>
    1496:	49 89 84 24 80 fe ff ff 	mov    %rax,-0x180(%r12)
        for (int n = 0 ; n < buffer_size ; n++) {
    149e:	4d 39 e6             	cmp    %r12,%r14
    14a1:	75 dd                	jne    1480 <main+0x2c0>
        }
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
    14a3:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    14a8:	4c 8b a5 00 02 00 00 	mov    0x200(%rbp),%r12
      thread_data[j].size = buffer_size;
    14af:	48 c7 85 90 06 00 00 00 80 00 00 	movq   $0x8000,0x690(%rbp)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    14ba:	be 80 00 00 00       	mov    $0x80,%esi
      // printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        thread_data[n].readers[receiver_index] = &thread_data[j];
    14bf:	4c 8b b5 80 04 00 00 	mov    0x480(%rbp),%r14
      thread_data[j].other_count = other_count;
    14c6:	48 8b 05 0b 0c 00 00 	mov    0xc0b(%rip),%rax        # 20d8 <_IO_stdin_used+0xd8>
      thread_data[j].start = 0;
    14cd:	c7 85 80 05 00 00 00 00 00 00 	movl   $0x0,0x580(%rbp)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    14d7:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].sender = &thread_data[sender];
    14dc:	0f 11 95 08 05 00 00 	movups %xmm2,0x508(%rbp)
      thread_data[j].thread_index = j;
    14e3:	4c 8d bd 80 07 00 00 	lea    0x780(%rbp),%r15
      thread_data[j].readers = thread_data[sender].readers;
    14ea:	4c 89 a5 00 07 00 00 	mov    %r12,0x700(%rbp)
        thread_data[n].readers[receiver_index] = &thread_data[j];
    14f1:	49 89 1c 24          	mov    %rbx,(%r12)
    14f5:	49 89 1e             	mov    %rbx,(%r14)
      thread_data[j].thread_index = j;
    14f8:	c7 85 80 07 00 00 03 00 00 00 	movl   $0x3,0x780(%rbp)
      thread_data[j].multiple = receiver_index % other_count;
    1502:	c7 85 90 09 00 00 01 00 00 00 	movl   $0x1,0x990(%rbp)
      thread_data[j].other_count = other_count;
    150c:	48 89 85 88 09 00 00 	mov    %rax,0x988(%rbp)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1513:	e8 48 fc ff ff       	call   1160 <calloc@plt>
      thread_data[j].sender = &thread_data[sender];
    1518:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
      thread_data[j].running = 1;
    151d:	c7 85 18 09 00 00 01 00 00 00 	movl   $0x1,0x918(%rbp)
      CPU_SET(curcpu, receivercpu);
    1527:	48 83 08 40          	orq    $0x40,(%rax)
      thread_data[j].cpu_set = receivercpu;
    152b:	48 89 85 20 09 00 00 	mov    %rax,0x920(%rbp)
      thread_data[j].mode = READER;
    1532:	c7 85 08 09 00 00 01 00 00 00 	movl   $0x1,0x908(%rbp)
      thread_data[j].size = buffer_size;
    153c:	48 c7 85 10 09 00 00 00 80 00 00 	movq   $0x8000,0x910(%rbp)
      thread_data[j].start = 0;
    1547:	c7 85 00 08 00 00 00 00 00 00 	movl   $0x0,0x800(%rbp)
      thread_data[j].readers = thread_data[sender].readers;
    1551:	4c 89 a5 80 09 00 00 	mov    %r12,0x980(%rbp)
      thread_data[j].sender = &thread_data[sender];
    1558:	0f 11 95 88 07 00 00 	movups %xmm2,0x788(%rbp)
        thread_data[n].readers[receiver_index] = &thread_data[j];
    155f:	4d 89 7c 24 08       	mov    %r15,0x8(%r12)
    1564:	4d 89 7e 08          	mov    %r15,0x8(%r14)
      }
    }
    curcpu = 0;
    // printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    1568:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    156b:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    1570:	c7 44 24 3c 00 00 00 00 	movl   $0x0,0x3c(%rsp)
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1578:	4d 8d 75 10          	lea    0x10(%r13),%r14
      if (ret) {
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    157c:	4c 8d 3d 6d 03 00 00 	lea    0x36d(%rip),%r15        # 18f0 <disruptor_thread>
    1583:	4c 8d 60 70          	lea    0x70(%rax),%r12
    1587:	48 05 e0 00 00 00    	add    $0xe0,%rax
    158d:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    1592:	31 f6                	xor    %esi,%esi
    1594:	4c 89 e7             	mov    %r12,%rdi
    1597:	e8 b4 fb ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    159c:	85 c0                	test   %eax,%eax
    159e:	0f 85 20 02 00 00    	jne    17c4 <main+0x604>
      ret = pthread_attr_setschedparam(&attr[j], &param);
    15a4:	48 8d 74 24 3c       	lea    0x3c(%rsp),%rsi
    15a9:	4c 89 e7             	mov    %r12,%rdi
    15ac:	e8 df fb ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    15b1:	85 c0                	test   %eax,%eax
    15b3:	0f 85 26 02 00 00    	jne    17df <main+0x61f>
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    15b9:	48 89 d9             	mov    %rbx,%rcx
    15bc:	4c 89 e6             	mov    %r12,%rsi
    15bf:	4c 89 f7             	mov    %r14,%rdi
    15c2:	4c 89 fa             	mov    %r15,%rdx
    15c5:	e8 b6 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    15ca:	49 8b 3e             	mov    (%r14),%rdi
    15cd:	be 08 00 00 00       	mov    $0x8,%esi
    15d2:	48 8b 93 a0 01 00 00 	mov    0x1a0(%rbx),%rdx
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15d9:	49 83 c4 38          	add    $0x38,%r12
    15dd:	49 83 c6 08          	add    $0x8,%r14
    15e1:	48 81 c3 80 02 00 00 	add    $0x280,%rbx
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    15e8:	e8 13 fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15ed:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    15f2:	49 39 c4             	cmp    %rax,%r12
    15f5:	75 9b                	jne    1592 <main+0x3d2>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    15f7:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    15fc:	31 f6                	xor    %esi,%esi
    15fe:	48 89 df             	mov    %rbx,%rdi
    1601:	e8 4a fb ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    1606:	85 c0                	test   %eax,%eax
    1608:	0f 85 b6 01 00 00    	jne    17c4 <main+0x604>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    160e:	48 8d 74 24 38       	lea    0x38(%rsp),%rsi
    1613:	48 89 df             	mov    %rbx,%rdi
      param2.sched_priority = 0;
    1616:	c7 44 24 38 00 00 00 00 	movl   $0x0,0x38(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    161e:	e8 6d fb ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1623:	85 c0                	test   %eax,%eax
    1625:	0f 85 b4 01 00 00    	jne    17df <main+0x61f>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    162b:	48 89 e9             	mov    %rbp,%rcx
    162e:	48 89 de             	mov    %rbx,%rsi
    1631:	4c 89 fa             	mov    %r15,%rdx
    1634:	4c 89 ef             	mov    %r13,%rdi
    1637:	e8 44 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    163c:	48 8b 95 a0 01 00 00 	mov    0x1a0(%rbp),%rdx
    1643:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    1647:	be 08 00 00 00       	mov    $0x8,%esi
    164c:	4c 8d 25 5c 0a 00 00 	lea    0xa5c(%rip),%r12        # 20af <_IO_stdin_used+0xaf>
    1653:	e8 a8 fa ff ff       	call   1100 <pthread_setaffinity_np@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    1658:	48 89 de             	mov    %rbx,%rsi
    165b:	49 8d 7d 08          	lea    0x8(%r13),%rdi
    165f:	4c 89 fa             	mov    %r15,%rdx
    1662:	48 8d 8d 80 02 00 00 	lea    0x280(%rbp),%rcx
    1669:	48 83 c6 38          	add    $0x38,%rsi
    void * res1;
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    166d:	31 db                	xor    %ebx,%ebx
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    166f:	e8 0c fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    1674:	48 8b 95 20 04 00 00 	mov    0x420(%rbp),%rdx
    167b:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    167f:	be 08 00 00 00       	mov    $0x8,%esi
    1684:	e8 77 fa ff ff       	call   1100 <pthread_setaffinity_np@plt>
  nanosleep(&preempt , &rem2);
    1689:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    168e:	48 8d 7c 24 50       	lea    0x50(%rsp),%rdi
  struct timespec preempt = {
    1693:	66 0f 6f 05 45 0a 00 00 	movdqa 0xa45(%rip),%xmm0        # 20e0 <_IO_stdin_used+0xe0>
    169b:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&preempt , &rem2);
    16a0:	e8 9b fa ff ff       	call   1140 <nanosleep@plt>
      pthread_join(thread[n], res1);
    16a5:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    16a9:	48 89 de             	mov    %rbx,%rsi
    thread_data[sender].running = 0;
    16ac:	c7 85 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%rbp)
      thread_data[j].running = 0;
    16b6:	c7 85 98 06 00 00 00 00 00 00 	movl   $0x0,0x698(%rbp)
    16c0:	c7 85 18 09 00 00 00 00 00 00 	movl   $0x0,0x918(%rbp)
      thread_data[n].running = 0;
    16ca:	c7 85 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%rbp)
    16d4:	c7 85 18 04 00 00 00 00 00 00 	movl   $0x0,0x418(%rbp)
      pthread_join(thread[n], res1);
    16de:	e8 cd fa ff ff       	call   11b0 <pthread_join@plt>
    16e3:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    16e7:	48 89 de             	mov    %rbx,%rsi
    16ea:	e8 c1 fa ff ff       	call   11b0 <pthread_join@plt>
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    16ef:	49 8b 7d 10          	mov    0x10(%r13),%rdi
    16f3:	48 89 de             	mov    %rbx,%rsi
    16f6:	e8 b5 fa ff ff       	call   11b0 <pthread_join@plt>
    16fb:	49 8b 7d 18          	mov    0x18(%r13),%rdi
    16ff:	48 89 de             	mov    %rbx,%rsi
    1702:	e8 a9 fa ff ff       	call   11b0 <pthread_join@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    // printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    1707:	eb 17                	jmp    1720 <main+0x560>
    1709:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1710:	48 81 c3 80 01 00 00 	add    $0x180,%rbx
    1717:	48 81 fb 00 00 c0 00 	cmp    $0xc00000,%rbx
    171e:	74 7d                	je     179d <main+0x5dd>
      int compcount = 0;
      for (int n = 0 ; n < 2 ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    1720:	48 8b 45 18          	mov    0x18(%rbp),%rax
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
    1740:	4c 89 e6             	mov    %r12,%rsi
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
    175f:	48 8b 45 18          	mov    0x18(%rbp),%rax
    1763:	4c 89 e6             	mov    %r12,%rsi
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
    1794:	48 81 fb 00 00 c0 00 	cmp    $0xc00000,%rbx
    179b:	75 83                	jne    1720 <main+0x560>
    }
    // printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    179d:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    17a5:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    17ae:	75 2a                	jne    17da <main+0x61a>
    17b0:	48 81 c4 98 00 00 00 	add    $0x98,%rsp
    17b7:	31 c0                	xor    %eax,%eax
    17b9:	5b                   	pop    %rbx
    17ba:	5d                   	pop    %rbp
    17bb:	41 5c                	pop    %r12
    17bd:	41 5d                	pop    %r13
    17bf:	41 5e                	pop    %r14
    17c1:	41 5f                	pop    %r15
    17c3:	c3                   	ret
    17c4:	48 8d 3d a9 08 00 00 	lea    0x8a9(%rip),%rdi        # 2074 <_IO_stdin_used+0x74>
    17cb:	e8 40 f9 ff ff       	call   1110 <puts@plt>
               exit(1);
    17d0:	bf 01 00 00 00       	mov    $0x1,%edi
    17d5:	e8 c6 f9 ff ff       	call   11a0 <exit@plt>
}
    17da:	e8 51 f9 ff ff       	call   1130 <__stack_chk_fail@plt>
    17df:	48 8d 3d ac 08 00 00 	lea    0x8ac(%rip),%rdi        # 2092 <_IO_stdin_used+0x92>
    17e6:	e8 25 f9 ff ff       	call   1110 <puts@plt>
              exit(1);
    17eb:	bf 01 00 00 00       	mov    $0x1,%edi
    17f0:	e8 ab f9 ff ff       	call   11a0 <exit@plt>
    17f5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
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
    18f4:	41 56                	push   %r14
    18f6:	41 55                	push   %r13
    18f8:	41 54                	push   %r12
    18fa:	55                   	push   %rbp
    18fb:	53                   	push   %rbx
  if (data->mode == WRITER) {
    18fc:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
void * disruptor_thread(void * arg) {
    1902:	48 89 fb             	mov    %rdi,%rbx
  if (data->mode == WRITER) {
    1905:	85 c0                	test   %eax,%eax
    1907:	0f 85 2b 01 00 00    	jne    1a38 <disruptor_thread+0x148>
    struct Thread *me = data->sender;
    190d:	4c 8b 67 08          	mov    0x8(%rdi),%r12
    while (data->running == 1) {
    1911:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1918:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    191e:	83 f8 01             	cmp    $0x1,%eax
    1921:	0f 85 1c 01 00 00    	jne    1a43 <disruptor_thread+0x153>
      asm volatile ("sfence" ::: "memory");
    1927:	0f ae f8             	sfence
      int pos = (((me->realend & END_MASK)>>32) + 1) % data->size;
    192a:	49 8b ac 24 80 01 00 00 	mov    0x180(%r12),%rbp
    1932:	49 89 e8             	mov    %rbp,%r8
    1935:	49 c1 f8 20          	sar    $0x20,%r8
    1939:	41 81 e0 ff ff ff 0f 	and    $0xfffffff,%r8d
    1940:	49 83 c0 01          	add    $0x1,%r8
    1944:	4c 89 c0             	mov    %r8,%rax
    1947:	48 99                	cqto
    1949:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
      for (int x  = 0 ; x < data->other_count; x++) {
    1950:	48 63 83 08 02 00 00 	movslq 0x208(%rbx),%rax
    1957:	85 c0                	test   %eax,%eax
    1959:	0f 8e ef 00 00 00    	jle    1a4e <disruptor_thread+0x15e>
    195f:	48 8b 8b 00 02 00 00 	mov    0x200(%rbx),%rcx
    1966:	48 8d 3c c1          	lea    (%rcx,%rax,8),%rdi
    196a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (pos == data->readers[x]->start) {
    1970:	48 8b 31             	mov    (%rcx),%rsi
    1973:	3b 96 80 00 00 00    	cmp    0x80(%rsi),%edx
    1979:	74 9d                	je     1918 <disruptor_thread+0x28>
      for (int x  = 0 ; x < data->other_count; x++) {
    197b:	48 83 c1 08          	add    $0x8,%rcx
    197f:	48 39 f9             	cmp    %rdi,%rcx
    1982:	75 ec                	jne    1970 <disruptor_thread+0x80>
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1984:	4c 89 c0             	mov    %r8,%rax
              long new = (data->thread_tag) | (changed << 32);
    1987:	4c 63 b3 14 02 00 00 	movslq 0x214(%rbx),%r14
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    198e:	48 99                	cqto
    1990:	49 f7 bc 24 90 01 00 00 	idivq  0x190(%r12)
              long new = (data->thread_tag) | (changed << 32);
    1998:	48 89 d0             	mov    %rdx,%rax
                me->data[changed].complete[x] = 0;
    199b:	4c 8d 2c 52          	lea    (%rdx,%rdx,2),%r13
              long new = (data->thread_tag) | (changed << 32);
    199f:	48 c1 e0 20          	shl    $0x20,%rax
                me->data[changed].complete[x] = 0;
    19a3:	49 c1 e5 07          	shl    $0x7,%r13
              long new = (data->thread_tag) | (changed << 32);
    19a7:	49 09 c6             	or     %rax,%r14
                me->data[changed].complete[x] = 0;
    19aa:	49 8b 44 24 18       	mov    0x18(%r12),%rax
    19af:	4a 8b 94 28 00 01 00 00 	mov    0x100(%rax,%r13,1),%rdx
    19b7:	31 c0                	xor    %eax,%eax
    19b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    19c0:	c7 04 82 00 00 00 00 	movl   $0x0,(%rdx,%rax,4)
              for (int x = 0 ; x < data->other_count; x++) {
    19c7:	48 83 c0 01          	add    $0x1,%rax
    19cb:	39 83 08 02 00 00    	cmp    %eax,0x208(%rbx)
    19d1:	7f ed                	jg     19c0 <disruptor_thread+0xd0>
              asm volatile ("sfence" ::: "memory");
    19d3:	0f ae f8             	sfence
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    19d6:	49 8b 74 24 18       	mov    0x18(%r12),%rsi
    19db:	bf 04 00 00 00       	mov    $0x4,%edi
    19e0:	4c 01 ee             	add    %r13,%rsi
    19e3:	e8 38 f7 ff ff       	call   1120 <clock_gettime@plt>
              if (!__atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED)) {
    19e8:	48 89 e8             	mov    %rbp,%rax
    19eb:	f0 4d 0f b1 b4 24 80 01 00 00 	lock cmpxchg %r14,0x180(%r12)
    19f5:	0f 94 c0             	sete   %al
    19f8:	0f b6 c0             	movzbl %al,%eax
    19fb:	0f 84 17 ff ff ff    	je     1918 <disruptor_thread+0x28>
                for (int x = 0 ; x < data->other_count; x++) {
    1a01:	83 bb 08 02 00 00 00 	cmpl   $0x0,0x208(%rbx)
    1a08:	0f 8e 0a ff ff ff    	jle    1918 <disruptor_thread+0x28>
                  me->data[changed].complete[x] = 0;
    1a0e:	49 8b 54 24 18       	mov    0x18(%r12),%rdx
    1a13:	4a 8b 94 2a 00 01 00 00 	mov    0x100(%rdx,%r13,1),%rdx
    1a1b:	c7 04 82 00 00 00 00 	movl   $0x0,(%rdx,%rax,4)
                for (int x = 0 ; x < data->other_count; x++) {
    1a22:	48 83 c0 01          	add    $0x1,%rax
    1a26:	39 83 08 02 00 00    	cmp    %eax,0x208(%rbx)
    1a2c:	7f ed                	jg     1a1b <disruptor_thread+0x12b>
    1a2e:	e9 e5 fe ff ff       	jmp    1918 <disruptor_thread+0x28>
    1a33:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  } else if (data->mode == READER) {
    1a38:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
    1a3e:	83 f8 01             	cmp    $0x1,%eax
    1a41:	74 36                	je     1a79 <disruptor_thread+0x189>
}
    1a43:	5b                   	pop    %rbx
    1a44:	31 c0                	xor    %eax,%eax
    1a46:	5d                   	pop    %rbp
    1a47:	41 5c                	pop    %r12
    1a49:	41 5d                	pop    %r13
    1a4b:	41 5e                	pop    %r14
    1a4d:	c3                   	ret
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1a4e:	4c 89 c0             	mov    %r8,%rax
              long new = (data->thread_tag) | (changed << 32);
    1a51:	4c 63 b3 14 02 00 00 	movslq 0x214(%rbx),%r14
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1a58:	48 99                	cqto
    1a5a:	49 f7 bc 24 90 01 00 00 	idivq  0x190(%r12)
              long new = (data->thread_tag) | (changed << 32);
    1a62:	48 89 d0             	mov    %rdx,%rax
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1a65:	4c 8d 2c 52          	lea    (%rdx,%rdx,2),%r13
              long new = (data->thread_tag) | (changed << 32);
    1a69:	48 c1 e0 20          	shl    $0x20,%rax
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1a6d:	49 c1 e5 07          	shl    $0x7,%r13
              long new = (data->thread_tag) | (changed << 32);
    1a71:	49 09 c6             	or     %rax,%r14
              for (int x = 0 ; x < data->other_count; x++) {
    1a74:	e9 5a ff ff ff       	jmp    19d3 <disruptor_thread+0xe3>
    struct Thread *sender = data->sender;
    1a79:	4c 8b 67 08          	mov    0x8(%rdi),%r12
    struct Snapshot * rdata = sender->data;
    1a7d:	4d 8b 74 24 18       	mov    0x18(%r12),%r14
    while (data->running == 1) {
    1a82:	eb 1b                	jmp    1a9f <disruptor_thread+0x1af>
    1a84:	0f 1f 40 00          	nopl   0x0(%rax)
      int pos = ((sender->realend & END_MASK) >> 32);
    1a88:	49 63 84 24 84 01 00 00 	movslq 0x184(%r12),%rax
      if (pos == data->start) {
    1a90:	8b ab 80 00 00 00    	mov    0x80(%rbx),%ebp
      int pos = ((sender->realend & END_MASK) >> 32);
    1a96:	25 ff ff ff 0f       	and    $0xfffffff,%eax
      if (pos == data->start) {
    1a9b:	39 c5                	cmp    %eax,%ebp
    1a9d:	75 0d                	jne    1aac <disruptor_thread+0x1bc>
    while (data->running == 1) {
    1a9f:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    1aa5:	83 f8 01             	cmp    $0x1,%eax
    1aa8:	74 de                	je     1a88 <disruptor_thread+0x198>
    1aaa:	eb 97                	jmp    1a43 <disruptor_thread+0x153>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1aac:	48 63 c5             	movslq %ebp,%rax
    1aaf:	48 63 b3 0c 02 00 00 	movslq 0x20c(%rbx),%rsi
    1ab6:	bf 04 00 00 00       	mov    $0x4,%edi
    1abb:	4c 8d 2c 40          	lea    (%rax,%rax,2),%r13
    1abf:	49 c1 e5 07          	shl    $0x7,%r13
    1ac3:	48 c1 e6 04          	shl    $0x4,%rsi
    1ac7:	4d 01 f5             	add    %r14,%r13
    1aca:	49 03 b5 80 00 00 00 	add    0x80(%r13),%rsi
    1ad1:	e8 4a f6 ff ff       	call   1120 <clock_gettime@plt>
              rdata[changed].complete[data->reader_index] = 1;
    1ad6:	49 8b 85 00 01 00 00 	mov    0x100(%r13),%rax
    1add:	48 63 93 0c 02 00 00 	movslq 0x20c(%rbx),%rdx
    1ae4:	c7 04 90 01 00 00 00 	movl   $0x1,(%rax,%rdx,4)
              data->start = (changed + 1) % data->size;
    1aeb:	8d 45 01             	lea    0x1(%rbp),%eax
    1aee:	48 98                	cltq
    1af0:	48 99                	cqto
    1af2:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
    1af9:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
    1aff:	eb 9e                	jmp    1a9f <disruptor_thread+0x1af>
    1b01:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    1b0c:	0f 1f 40 00          	nopl   0x0(%rax)

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
