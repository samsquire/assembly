
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
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int receiver2 = receiver + 1; 
    int seq[] = {1, 2, 5};
    int tag_index[] = {1, 5, 7};
    11cb:	45 31 ff             	xor    %r15d,%r15d
    11ce:	ba 0f 00 00 00       	mov    $0xf,%edx
int main() {
    11d3:	41 56                	push   %r14
    11d5:	48 8d 35 2c 0e 00 00 	lea    0xe2c(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    11dc:	bf 01 00 00 00       	mov    $0x1,%edi
    11e1:	41 55                	push   %r13
    11e3:	41 54                	push   %r12
    int tag_index[] = {1, 5, 7};
    11e5:	45 31 e4             	xor    %r12d,%r12d
int main() {
    11e8:	55                   	push   %rbp
    11e9:	4c 89 fd             	mov    %r15,%rbp
    11ec:	53                   	push   %rbx
    11ed:	48 81 ec 98 00 00 00 	sub    $0x98,%rsp
    11f4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    11fd:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    1205:	31 c0                	xor    %eax,%eax
    1207:	e8 64 ff ff ff       	call   1170 <__printf_chk@plt>
    120c:	ba 01 00 00 00       	mov    $0x1,%edx
    1211:	48 8d 35 81 0e 00 00 	lea    0xe81(%rip),%rsi        # 2099 <_IO_stdin_used+0x99>
    1218:	31 c0                	xor    %eax,%eax
    121a:	bf 01 00 00 00       	mov    $0x1,%edi
    121f:	e8 4c ff ff ff       	call   1170 <__printf_chk@plt>
    1224:	ba 03 00 00 00       	mov    $0x3,%edx
    1229:	48 8d 35 79 0e 00 00 	lea    0xe79(%rip),%rsi        # 20a9 <_IO_stdin_used+0xa9>
    1230:	31 c0                	xor    %eax,%eax
    1232:	bf 01 00 00 00       	mov    $0x1,%edi
    1237:	e8 34 ff ff ff       	call   1170 <__printf_chk@plt>
    123c:	ba 02 00 00 00       	mov    $0x2,%edx
    1241:	48 8d 35 73 0e 00 00 	lea    0xe73(%rip),%rsi        # 20bb <_IO_stdin_used+0xbb>
    1248:	31 c0                	xor    %eax,%eax
    124a:	bf 01 00 00 00       	mov    $0x1,%edi
    124f:	e8 1c ff ff ff       	call   1170 <__printf_chk@plt>
    1254:	ba 05 00 00 00       	mov    $0x5,%edx
    1259:	48 8d 35 6d 0e 00 00 	lea    0xe6d(%rip),%rsi        # 20cd <_IO_stdin_used+0xcd>
    1260:	31 c0                	xor    %eax,%eax
    1262:	bf 01 00 00 00       	mov    $0x1,%edi
    1267:	e8 04 ff ff ff       	call   1170 <__printf_chk@plt>
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    126c:	be 80 02 00 00       	mov    $0x280,%esi
    1271:	bf 05 00 00 00       	mov    $0x5,%edi
    1276:	e8 e5 fe ff ff       	call   1160 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    127b:	be 38 00 00 00       	mov    $0x38,%esi
    1280:	bf 05 00 00 00       	mov    $0x5,%edi
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1285:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1288:	e8 d3 fe ff ff       	call   1160 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    128d:	be 08 00 00 00       	mov    $0x8,%esi
    1292:	bf 05 00 00 00       	mov    $0x5,%edi
    1297:	4d 89 ef             	mov    %r13,%r15
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    129a:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    129f:	e8 bc fe ff ff       	call   1160 <calloc@plt>
    12a4:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    int seq[] = {1, 2, 5};
    12a9:	48 8b 05 88 0e 00 00 	mov    0xe88(%rip),%rax        # 2138 <_IO_stdin_used+0x138>
    12b0:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    int tag_index[] = {1, 5, 7};
    12b5:	48 8b 05 84 0e 00 00 	mov    0xe84(%rip),%rax        # 2140 <_IO_stdin_used+0x140>
    12bc:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    12c1:	48 8d 44 24 68       	lea    0x68(%rsp),%rax
    12c6:	48 89 04 24          	mov    %rax,(%rsp)
    12ca:	48 8d 44 24 78       	lea    0x78(%rsp),%rax
    12cf:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12d4:	be 80 00 00 00       	mov    $0x80,%esi
    12d9:	bf 01 00 00 00       	mov    $0x1,%edi
      CPU_ZERO(sendercpu);
      CPU_SET(curcpu, sendercpu);
      curcpu += 1;
    12de:	45 8d 74 24 01       	lea    0x1(%r12),%r14d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12e3:	e8 78 fe ff ff       	call   1160 <calloc@plt>
      CPU_SET(curcpu, sendercpu);
    12e8:	44 89 e1             	mov    %r12d,%ecx
    12eb:	44 89 e2             	mov    %r12d,%edx
    12ee:	bf 01 00 00 00       	mov    $0x1,%edi
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12f3:	48 89 c3             	mov    %rax,%rbx
      CPU_SET(curcpu, sendercpu);
    12f6:	b8 01 00 00 00       	mov    $0x1,%eax
    12fb:	48 8d 35 2e 0d 00 00 	lea    0xd2e(%rip),%rsi        # 2030 <_IO_stdin_used+0x30>
    1302:	48 d3 e0             	shl    %cl,%rax
    1305:	48 09 03             	or     %rax,(%rbx)
    1308:	44 89 f1             	mov    %r14d,%ecx
    130b:	31 c0                	xor    %eax,%eax
    130d:	e8 5e fe ff ff       	call   1170 <__printf_chk@plt>
      printf("assigning sender %d to core %d\n", n, curcpu);
       
      thread_data[n].thread_index = n;
      thread_data[n].cpu_set = sendercpu;
      thread_data[n].mode = WRITER;
      thread_data[n].multiple = seq[sender_index % writers_count];
    1312:	48 8b 04 24          	mov    (%rsp),%rax
      thread_data[n].thread_index = n;
    1316:	45 89 27             	mov    %r12d,(%r15)
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].thread_tag = tag_index[sender_index];
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1319:	be 08 00 00 00       	mov    $0x8,%esi
      thread_data[n].cpu_set = sendercpu;
    131e:	49 89 9f a0 01 00 00 	mov    %rbx,0x1a0(%r15)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1325:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[n].multiple = seq[sender_index % writers_count];
    132a:	8b 04 28             	mov    (%rax,%rbp,1),%eax
      thread_data[n].sender = &thread_data[sender];
    132d:	4d 89 6f 08          	mov    %r13,0x8(%r15)
      thread_data[n].mode = WRITER;
    1331:	41 c7 87 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%r15)
      thread_data[n].multiple = seq[sender_index % writers_count];
    133c:	41 89 87 10 02 00 00 	mov    %eax,0x210(%r15)
      thread_data[n].thread_tag = tag_index[sender_index];
    1343:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
      thread_data[n].running = 1;
    1348:	41 c7 87 98 01 00 00 01 00 00 00 	movl   $0x1,0x198(%r15)
      thread_data[n].size = buffer_size;
    1353:	49 c7 87 90 01 00 00 00 80 00 00 	movq   $0x8000,0x190(%r15)
      thread_data[n].thread_tag = tag_index[sender_index];
    135e:	8b 04 28             	mov    (%rax,%rbp,1),%eax
      thread_data[n].end = 0;
    1361:	41 c7 87 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r15)
      thread_data[n].thread_tag = tag_index[sender_index];
    136c:	41 89 87 14 02 00 00 	mov    %eax,0x214(%r15)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1373:	e8 e8 fd ff ff       	call   1160 <calloc@plt>
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    1378:	be 00 02 00 00       	mov    $0x200,%esi
    137d:	bf 00 80 00 00       	mov    $0x8000,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1382:	49 89 87 00 02 00 00 	mov    %rax,0x200(%r15)
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    1389:	e8 d2 fd ff ff       	call   1160 <calloc@plt>
    138e:	49 89 47 18          	mov    %rax,0x18(%r15)
      for (int k = 0 ; k < buffer_size ; k++) {
    1392:	48 8d 98 80 00 00 00 	lea    0x80(%rax),%rbx
    1399:	4c 8d a0 80 00 00 01 	lea    0x1000080(%rax),%r12
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13a0:	be 04 00 00 00       	mov    $0x4,%esi
    13a5:	bf 03 00 00 00       	mov    $0x3,%edi
      for (int k = 0 ; k < buffer_size ; k++) {
    13aa:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13b1:	e8 aa fd ff ff       	call   1160 <calloc@plt>
        thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    13b6:	be 10 00 00 00       	mov    $0x10,%esi
    13bb:	bf 03 00 00 00       	mov    $0x3,%edi
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13c0:	48 89 83 80 fe ff ff 	mov    %rax,-0x180(%rbx)
        thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    13c7:	e8 94 fd ff ff       	call   1160 <calloc@plt>
    13cc:	48 89 83 00 fe ff ff 	mov    %rax,-0x200(%rbx)
      for (int k = 0 ; k < buffer_size ; k++) {
    13d3:	4c 39 e3             	cmp    %r12,%rbx
    13d6:	75 c8                	jne    13a0 <main+0x1e0>
      }
      thread_data[n].other_count = other_count;
    13d8:	41 c7 87 08 02 00 00 03 00 00 00 	movl   $0x3,0x208(%r15)
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    13e3:	48 83 c5 04          	add    $0x4,%rbp
    13e7:	49 81 c7 80 02 00 00 	add    $0x280,%r15
    13ee:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    13f4:	41 83 fe 02          	cmp    $0x2,%r14d
    13f8:	0f 85 d6 fe ff ff    	jne    12d4 <main+0x114>
    13fe:	4d 8d a5 00 05 00 00 	lea    0x500(%r13),%r12
    1405:	66 49 0f 6e d5       	movq   %r13,%xmm2
    140a:	bd 02 00 00 00       	mov    $0x2,%ebp
    140f:	4c 89 64 24 18       	mov    %r12,0x18(%rsp)
    1414:	66 0f 6c d2          	punpcklqdq %xmm2,%xmm2
    1418:	4c 89 e3             	mov    %r12,%rbx
    141b:	0f 29 14 24          	movaps %xmm2,(%rsp)
    141f:	44 8d 7d fe          	lea    -0x2(%rbp),%r15d
    }

    // printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      thread_data[j].thread_index = j;
    1423:	89 2b                	mov    %ebp,(%rbx)
      thread_data[j].reader_index = receiver_index;
      thread_data[j].multiple = receiver_index % other_count;
      thread_data[j].other_count = other_count;
     
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1425:	be 80 00 00 00       	mov    $0x80,%esi
    142a:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].reader_index = receiver_index;
    142f:	44 89 bb 0c 02 00 00 	mov    %r15d,0x20c(%rbx)
      thread_data[j].multiple = receiver_index % other_count;
    1436:	44 89 bb 10 02 00 00 	mov    %r15d,0x210(%rbx)
      thread_data[j].other_count = other_count;
    143d:	c7 83 08 02 00 00 03 00 00 00 	movl   $0x3,0x208(%rbx)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1447:	e8 14 fd ff ff       	call   1160 <calloc@plt>
      CPU_ZERO(receivercpu);
      CPU_SET(curcpu, receivercpu);
    144c:	89 e9                	mov    %ebp,%ecx
    144e:	89 ea                	mov    %ebp,%edx
    1450:	48 8d 35 f9 0b 00 00 	lea    0xbf9(%rip),%rsi        # 2050 <_IO_stdin_used+0x50>
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1457:	49 89 c4             	mov    %rax,%r12
      CPU_SET(curcpu, receivercpu);
    145a:	b8 01 00 00 00       	mov    $0x1,%eax
    145f:	bf 01 00 00 00       	mov    $0x1,%edi
    1464:	48 d3 e0             	shl    %cl,%rax
    1467:	49 09 04 24          	or     %rax,(%r12)
      curcpu += 1;
    146b:	8d 4d 01             	lea    0x1(%rbp),%ecx
    146e:	31 c0                	xor    %eax,%eax
    1470:	e8 fb fc ff ff       	call   1170 <__printf_chk@plt>
      printf("assigning receiver %d to core %d\n", j, curcpu);
      thread_data[j].cpu_set = receivercpu;
    1475:	4c 89 a3 a0 01 00 00 	mov    %r12,0x1a0(%rbx)
      thread_data[j].running = 1;
    147c:	c7 83 98 01 00 00 01 00 00 00 	movl   $0x1,0x198(%rbx)
      thread_data[j].mode = READER;
    1486:	c7 83 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rbx)
      if (j == receiver) {
    1490:	48 83 fd 02          	cmp    $0x2,%rbp
    1494:	0f 84 f9 02 00 00    	je     1793 <main+0x5d3>
        for (int n = 0 ; n < buffer_size ; n++) {
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
        }
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
    149a:	66 0f 6f 0c 24       	movdqa (%rsp),%xmm1
    149f:	31 c9                	xor    %ecx,%ecx
    14a1:	44 89 fa             	mov    %r15d,%edx
    14a4:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    14a9:	49 8b 85 00 02 00 00 	mov    0x200(%r13),%rax
    14b0:	48 8d 35 c1 0b 00 00 	lea    0xbc1(%rip),%rsi        # 2078 <_IO_stdin_used+0x78>
      thread_data[j].size = buffer_size;
    14b7:	48 c7 83 90 01 00 00 00 80 00 00 	movq   $0x8000,0x190(%rbx)
      thread_data[j].other_count = other_count;
      // printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        printf("assigned reader %d to sender %d\n", receiver_index, n);
        thread_data[n].readers[receiver_index] = &thread_data[j];
    14c2:	4c 8d 34 ed 00 00 00 00 	lea    0x0(,%rbp,8),%r14
      thread_data[j].start = 0;
    14ca:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    14d4:	48 83 c5 01          	add    $0x1,%rbp
      thread_data[j].readers = thread_data[sender].readers;
    14d8:	48 89 83 00 02 00 00 	mov    %rax,0x200(%rbx)
    14df:	31 c0                	xor    %eax,%eax
      thread_data[j].other_count = other_count;
    14e1:	c7 83 08 02 00 00 03 00 00 00 	movl   $0x3,0x208(%rbx)
      thread_data[j].sender = &thread_data[sender];
    14eb:	0f 11 4b 08          	movups %xmm1,0x8(%rbx)
    14ef:	e8 7c fc ff ff       	call   1170 <__printf_chk@plt>
        thread_data[n].readers[receiver_index] = &thread_data[j];
    14f4:	49 8b 85 00 02 00 00 	mov    0x200(%r13),%rax
    14fb:	44 89 fa             	mov    %r15d,%edx
    14fe:	b9 01 00 00 00       	mov    $0x1,%ecx
    1503:	48 8d 35 6e 0b 00 00 	lea    0xb6e(%rip),%rsi        # 2078 <_IO_stdin_used+0x78>
    150a:	bf 01 00 00 00       	mov    $0x1,%edi
    150f:	4a 89 5c 30 f0       	mov    %rbx,-0x10(%rax,%r14,1)
    1514:	31 c0                	xor    %eax,%eax
    1516:	e8 55 fc ff ff       	call   1170 <__printf_chk@plt>
    151b:	49 8b 85 80 04 00 00 	mov    0x480(%r13),%rax
    1522:	4a 89 5c 30 f0       	mov    %rbx,-0x10(%rax,%r14,1)
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1527:	48 81 c3 80 02 00 00 	add    $0x280,%rbx
    152e:	48 83 fd 05          	cmp    $0x5,%rbp
    1532:	0f 85 e7 fe ff ff    	jne    141f <main+0x25f>
    1538:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
      }
    }
    curcpu = 0;
    // printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    153d:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    1540:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    1545:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    154a:	c7 44 24 3c 00 00 00 00 	movl   $0x0,0x3c(%rsp)
      if (ret) {
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1552:	4c 8d 3d b7 03 00 00 	lea    0x3b7(%rip),%r15        # 1910 <disruptor_thread>
    1559:	48 8d 58 70          	lea    0x70(%rax),%rbx
    155d:	48 8d 69 10          	lea    0x10(%rcx),%rbp
    1561:	4c 8d b0 18 01 00 00 	lea    0x118(%rax),%r14
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    1568:	31 f6                	xor    %esi,%esi
    156a:	48 89 df             	mov    %rbx,%rdi
    156d:	e8 de fb ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    1572:	85 c0                	test   %eax,%eax
    1574:	0f 85 6e 02 00 00    	jne    17e8 <main+0x628>
      ret = pthread_attr_setschedparam(&attr[j], &param);
    157a:	48 8d 74 24 3c       	lea    0x3c(%rsp),%rsi
    157f:	48 89 df             	mov    %rbx,%rdi
    1582:	e8 09 fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1587:	85 c0                	test   %eax,%eax
    1589:	0f 85 74 02 00 00    	jne    1803 <main+0x643>
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    158f:	4c 89 e1             	mov    %r12,%rcx
    1592:	48 89 de             	mov    %rbx,%rsi
    1595:	48 89 ef             	mov    %rbp,%rdi
    1598:	4c 89 fa             	mov    %r15,%rdx
    159b:	e8 e0 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    15a0:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15a4:	48 83 c3 38          	add    $0x38,%rbx
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    15a8:	49 8b 94 24 a0 01 00 00 	mov    0x1a0(%r12),%rdx
    15b0:	be 08 00 00 00       	mov    $0x8,%esi
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15b5:	48 83 c5 08          	add    $0x8,%rbp
    15b9:	49 81 c4 80 02 00 00 	add    $0x280,%r12
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    15c0:	e8 3b fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15c5:	4c 39 f3             	cmp    %r14,%rbx
    15c8:	75 9e                	jne    1568 <main+0x3a8>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    15ca:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
    15cf:	31 f6                	xor    %esi,%esi
    15d1:	4c 89 f7             	mov    %r14,%rdi
    15d4:	e8 77 fb ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    15d9:	85 c0                	test   %eax,%eax
    15db:	0f 85 07 02 00 00    	jne    17e8 <main+0x628>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    15e1:	48 8d 74 24 38       	lea    0x38(%rsp),%rsi
    15e6:	4c 89 f7             	mov    %r14,%rdi
      param2.sched_priority = 0;
    15e9:	c7 44 24 38 00 00 00 00 	movl   $0x0,0x38(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    15f1:	e8 9a fb ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    15f6:	85 c0                	test   %eax,%eax
    15f8:	0f 85 05 02 00 00    	jne    1803 <main+0x643>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    15fe:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    1603:	4c 89 e9             	mov    %r13,%rcx
    1606:	4c 89 f6             	mov    %r14,%rsi
    1609:	4c 89 fa             	mov    %r15,%rdx
    160c:	48 8d 2d 0c 0b 00 00 	lea    0xb0c(%rip),%rbp        # 211f <_IO_stdin_used+0x11f>
    1613:	48 89 df             	mov    %rbx,%rdi
    1616:	e8 65 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    161b:	48 8b 3b             	mov    (%rbx),%rdi
    161e:	be 08 00 00 00       	mov    $0x8,%esi
    1623:	49 8b 95 a0 01 00 00 	mov    0x1a0(%r13),%rdx
    162a:	e8 d1 fa ff ff       	call   1100 <pthread_setaffinity_np@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    162f:	4c 89 f6             	mov    %r14,%rsi
    1632:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    1636:	4c 89 fa             	mov    %r15,%rdx
    1639:	49 8d 8d 80 02 00 00 	lea    0x280(%r13),%rcx
    1640:	48 83 c6 38          	add    $0x38,%rsi
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    1644:	49 89 de             	mov    %rbx,%r14
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    1647:	e8 34 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    164c:	49 8b 95 20 04 00 00 	mov    0x420(%r13),%rdx
    1653:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    1657:	be 08 00 00 00       	mov    $0x8,%esi
    165c:	e8 9f fa ff ff       	call   1100 <pthread_setaffinity_np@plt>
  struct timespec rem2;
  struct timespec preempt = {
    seconds,
    0 };
  // printf("Sleeping for %d seconds\n", seconds);
  nanosleep(&preempt , &rem2);
    1661:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    1666:	48 8d 7c 24 50       	lea    0x50(%rsp),%rdi
  struct timespec preempt = {
    166b:	66 0f 6f 05 dd 0a 00 00 	movdqa 0xadd(%rip),%xmm0        # 2150 <_IO_stdin_used+0x150>
    1673:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  nanosleep(&preempt , &rem2);
    1678:	e8 c3 fa ff ff       	call   1140 <nanosleep@plt>
    void * res1;
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    167d:	48 8b 3b             	mov    (%rbx),%rdi
    1680:	31 db                	xor    %ebx,%ebx
    thread_data[sender].running = 0;
    1682:	41 c7 85 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r13)
      thread_data[j].running = 0;
    168d:	41 c7 85 98 06 00 00 00 00 00 00 	movl   $0x0,0x698(%r13)
      pthread_join(thread[n], res1);
    1698:	48 89 de             	mov    %rbx,%rsi
      thread_data[j].running = 0;
    169b:	41 c7 85 18 09 00 00 00 00 00 00 	movl   $0x0,0x918(%r13)
    16a6:	41 c7 85 98 0b 00 00 00 00 00 00 	movl   $0x0,0xb98(%r13)
      thread_data[n].running = 0;
    16b1:	41 c7 85 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r13)
    16bc:	41 c7 85 18 04 00 00 00 00 00 00 	movl   $0x0,0x418(%r13)
      pthread_join(thread[n], res1);
    16c7:	e8 e4 fa ff ff       	call   11b0 <pthread_join@plt>
    16cc:	49 8b 7e 08          	mov    0x8(%r14),%rdi
    16d0:	48 89 de             	mov    %rbx,%rsi
    16d3:	e8 d8 fa ff ff       	call   11b0 <pthread_join@plt>
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    16d8:	49 8b 7e 10          	mov    0x10(%r14),%rdi
    16dc:	48 89 de             	mov    %rbx,%rsi
    16df:	e8 cc fa ff ff       	call   11b0 <pthread_join@plt>
    16e4:	49 8b 7e 18          	mov    0x18(%r14),%rdi
    16e8:	48 89 de             	mov    %rbx,%rsi
    16eb:	e8 c0 fa ff ff       	call   11b0 <pthread_join@plt>
    16f0:	49 8b 7e 20          	mov    0x20(%r14),%rdi
    16f4:	48 89 de             	mov    %rbx,%rsi
    16f7:	e8 b4 fa ff ff       	call   11b0 <pthread_join@plt>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    16fc:	eb 12                	jmp    1710 <main+0x550>
    16fe:	66 90                	xchg   %ax,%ax
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    // printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    1700:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
    1707:	48 81 fb 00 00 00 01 	cmp    $0x1000000,%rbx
    170e:	74 5c                	je     176c <main+0x5ac>
      int compcount = 0;
      for (int n = 0 ; n < other_count ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    1710:	49 8b 45 18          	mov    0x18(%r13),%rax
    1714:	48 8b 94 18 00 01 00 00 	mov    0x100(%rax,%rbx,1),%rdx
    171c:	83 7a 04 01          	cmpl   $0x1,0x4(%rdx)
    1720:	75 de                	jne    1700 <main+0x540>
    1722:	83 7a 08 01          	cmpl   $0x1,0x8(%rdx)
    1726:	75 d8                	jne    1700 <main+0x540>
          compcount++;
        }
      }
      // printf("%d\n", compcount);
      if (compcount == other_count) {
    1728:	45 31 e4             	xor    %r12d,%r12d
    172b:	83 3a 01             	cmpl   $0x1,(%rdx)
    172e:	75 d0                	jne    1700 <main+0x540>
      for (int n = 0 ; n < other_count ; n++) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
    1730:	48 01 d8             	add    %rbx,%rax
    1733:	48 89 ee             	mov    %rbp,%rsi
    1736:	bf 01 00 00 00       	mov    $0x1,%edi
          struct timespec end = thread_data[sender].data[y].end[n];
    173b:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    1742:	4c 01 e2             	add    %r12,%rdx
      for (int n = 0 ; n < other_count ; n++) {
    1745:	49 83 c4 10          	add    $0x10,%r12
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    1749:	4c 8b 42 08          	mov    0x8(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    174d:	48 8b 0a             	mov    (%rdx),%rcx
    1750:	31 d2                	xor    %edx,%edx
    1752:	48 2b 08             	sub    (%rax),%rcx
    1755:	4c 2b 40 08          	sub    0x8(%rax),%r8
    1759:	31 c0                	xor    %eax,%eax
    175b:	e8 10 fa ff ff       	call   1170 <__printf_chk@plt>
      for (int n = 0 ; n < other_count ; n++) {
    1760:	49 83 fc 30          	cmp    $0x30,%r12
    1764:	74 9a                	je     1700 <main+0x540>
          struct timespec start = thread_data[sender].data[y].start;
    1766:	49 8b 45 18          	mov    0x18(%r13),%rax
    176a:	eb c4                	jmp    1730 <main+0x570>
    }
    // printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    176c:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    1774:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    177d:	75 7f                	jne    17fe <main+0x63e>
    177f:	48 81 c4 98 00 00 00 	add    $0x98,%rsp
    1786:	31 c0                	xor    %eax,%eax
    1788:	5b                   	pop    %rbx
    1789:	5d                   	pop    %rbp
    178a:	41 5c                	pop    %r12
    178c:	41 5d                	pop    %r13
    178e:	41 5e                	pop    %r14
    1790:	41 5f                	pop    %r15
    1792:	c3                   	ret
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    1793:	be 00 02 00 00       	mov    $0x200,%esi
    1798:	bf 00 80 00 00       	mov    $0x8000,%edi
    179d:	e8 be f9 ff ff       	call   1160 <calloc@plt>
    17a2:	48 89 43 18          	mov    %rax,0x18(%rbx)
    17a6:	49 89 c6             	mov    %rax,%r14
        for (int n = 0 ; n < buffer_size ; n++) {
    17a9:	4c 8d a0 00 01 00 00 	lea    0x100(%rax),%r12
    17b0:	49 81 c6 00 01 00 01 	add    $0x1000100,%r14
    17b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    17c0:	be 04 00 00 00       	mov    $0x4,%esi
    17c5:	bf 03 00 00 00       	mov    $0x3,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    17ca:	49 81 c4 00 02 00 00 	add    $0x200,%r12
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    17d1:	e8 8a f9 ff ff       	call   1160 <calloc@plt>
    17d6:	49 89 84 24 00 fe ff ff 	mov    %rax,-0x200(%r12)
        for (int n = 0 ; n < buffer_size ; n++) {
    17de:	4d 39 e6             	cmp    %r12,%r14
    17e1:	75 dd                	jne    17c0 <main+0x600>
    17e3:	e9 b2 fc ff ff       	jmp    149a <main+0x2da>
    17e8:	48 8d 3d f5 08 00 00 	lea    0x8f5(%rip),%rdi        # 20e4 <_IO_stdin_used+0xe4>
    17ef:	e8 1c f9 ff ff       	call   1110 <puts@plt>
               exit(1);
    17f4:	bf 01 00 00 00       	mov    $0x1,%edi
    17f9:	e8 a2 f9 ff ff       	call   11a0 <exit@plt>
}
    17fe:	e8 2d f9 ff ff       	call   1130 <__stack_chk_fail@plt>
    1803:	48 8d 3d f8 08 00 00 	lea    0x8f8(%rip),%rdi        # 2102 <_IO_stdin_used+0x102>
    180a:	e8 01 f9 ff ff       	call   1110 <puts@plt>
              exit(1);
    180f:	bf 01 00 00 00       	mov    $0x1,%edi
    1814:	e8 87 f9 ff ff       	call   11a0 <exit@plt>
    1819:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001820 <_start>:
    1820:	f3 0f 1e fa          	endbr64
    1824:	31 ed                	xor    %ebp,%ebp
    1826:	49 89 d1             	mov    %rdx,%r9
    1829:	5e                   	pop    %rsi
    182a:	48 89 e2             	mov    %rsp,%rdx
    182d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1831:	50                   	push   %rax
    1832:	54                   	push   %rsp
    1833:	45 31 c0             	xor    %r8d,%r8d
    1836:	31 c9                	xor    %ecx,%ecx
    1838:	48 8d 3d 81 f9 ff ff 	lea    -0x67f(%rip),%rdi        # 11c0 <main>
    183f:	ff 15 93 27 00 00    	call   *0x2793(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1845:	f4                   	hlt
    1846:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001850 <deregister_tm_clones>:
    1850:	48 8d 3d b9 27 00 00 	lea    0x27b9(%rip),%rdi        # 4010 <__TMC_END__>
    1857:	48 8d 05 b2 27 00 00 	lea    0x27b2(%rip),%rax        # 4010 <__TMC_END__>
    185e:	48 39 f8             	cmp    %rdi,%rax
    1861:	74 15                	je     1878 <deregister_tm_clones+0x28>
    1863:	48 8b 05 76 27 00 00 	mov    0x2776(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    186a:	48 85 c0             	test   %rax,%rax
    186d:	74 09                	je     1878 <deregister_tm_clones+0x28>
    186f:	ff e0                	jmp    *%rax
    1871:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1878:	c3                   	ret
    1879:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001880 <register_tm_clones>:
    1880:	48 8d 3d 89 27 00 00 	lea    0x2789(%rip),%rdi        # 4010 <__TMC_END__>
    1887:	48 8d 35 82 27 00 00 	lea    0x2782(%rip),%rsi        # 4010 <__TMC_END__>
    188e:	48 29 fe             	sub    %rdi,%rsi
    1891:	48 89 f0             	mov    %rsi,%rax
    1894:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1898:	48 c1 f8 03          	sar    $0x3,%rax
    189c:	48 01 c6             	add    %rax,%rsi
    189f:	48 d1 fe             	sar    %rsi
    18a2:	74 14                	je     18b8 <register_tm_clones+0x38>
    18a4:	48 8b 05 45 27 00 00 	mov    0x2745(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    18ab:	48 85 c0             	test   %rax,%rax
    18ae:	74 08                	je     18b8 <register_tm_clones+0x38>
    18b0:	ff e0                	jmp    *%rax
    18b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    18b8:	c3                   	ret
    18b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018c0 <__do_global_dtors_aux>:
    18c0:	f3 0f 1e fa          	endbr64
    18c4:	80 3d 45 27 00 00 00 	cmpb   $0x0,0x2745(%rip)        # 4010 <__TMC_END__>
    18cb:	75 2b                	jne    18f8 <__do_global_dtors_aux+0x38>
    18cd:	55                   	push   %rbp
    18ce:	48 83 3d 22 27 00 00 00 	cmpq   $0x0,0x2722(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    18d6:	48 89 e5             	mov    %rsp,%rbp
    18d9:	74 0c                	je     18e7 <__do_global_dtors_aux+0x27>
    18db:	48 8b 3d 26 27 00 00 	mov    0x2726(%rip),%rdi        # 4008 <__dso_handle>
    18e2:	e8 09 f8 ff ff       	call   10f0 <__cxa_finalize@plt>
    18e7:	e8 64 ff ff ff       	call   1850 <deregister_tm_clones>
    18ec:	c6 05 1d 27 00 00 01 	movb   $0x1,0x271d(%rip)        # 4010 <__TMC_END__>
    18f3:	5d                   	pop    %rbp
    18f4:	c3                   	ret
    18f5:	0f 1f 00             	nopl   (%rax)
    18f8:	c3                   	ret
    18f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001900 <frame_dummy>:
    1900:	f3 0f 1e fa          	endbr64
    1904:	e9 77 ff ff ff       	jmp    1880 <register_tm_clones>
    1909:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001910 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    1910:	f3 0f 1e fa          	endbr64
    1914:	41 56                	push   %r14
    1916:	41 55                	push   %r13
    1918:	41 54                	push   %r12
    191a:	55                   	push   %rbp
    191b:	53                   	push   %rbx
  if (data->mode == WRITER) {
    191c:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
void * disruptor_thread(void * arg) {
    1922:	48 89 fb             	mov    %rdi,%rbx
  if (data->mode == WRITER) {
    1925:	85 c0                	test   %eax,%eax
    1927:	0f 85 15 01 00 00    	jne    1a42 <disruptor_thread+0x132>
    struct Thread *me = data->sender;
    192d:	4c 8b 67 08          	mov    0x8(%rdi),%r12
    while (data->running == 1) {
    1931:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1938:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    193e:	83 f8 01             	cmp    $0x1,%eax
    1941:	0f 85 f0 00 00 00    	jne    1a37 <disruptor_thread+0x127>
      asm volatile ("sfence" ::: "memory");
    1947:	0f ae f8             	sfence
      long pos = (((me->realend & END_MASK) >> 32) + 1) % data->size;
    194a:	49 8b ac 24 80 01 00 00 	mov    0x180(%r12),%rbp
    1952:	49 89 e8             	mov    %rbp,%r8
    1955:	49 c1 f8 20          	sar    $0x20,%r8
    1959:	41 81 e0 ff ff ff 0f 	and    $0xfffffff,%r8d
    1960:	49 83 c0 01          	add    $0x1,%r8
    1964:	4c 89 c0             	mov    %r8,%rax
    1967:	48 99                	cqto
    1969:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
      for (int x  = 0 ; x < data->other_count; x++) {
    1970:	48 63 83 08 02 00 00 	movslq 0x208(%rbx),%rax
    1977:	85 c0                	test   %eax,%eax
    1979:	0f 8e 05 01 00 00    	jle    1a84 <disruptor_thread+0x174>
    197f:	48 8b 8b 00 02 00 00 	mov    0x200(%rbx),%rcx
    1986:	48 8d 3c c1          	lea    (%rcx,%rax,8),%rdi
    198a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (pos == data->readers[x]->start) {
    1990:	48 8b 31             	mov    (%rcx),%rsi
    1993:	48 63 b6 80 00 00 00 	movslq 0x80(%rsi),%rsi
    199a:	48 39 d6             	cmp    %rdx,%rsi
    199d:	74 99                	je     1938 <disruptor_thread+0x28>
      for (int x  = 0 ; x < data->other_count; x++) {
    199f:	48 83 c1 08          	add    $0x8,%rcx
    19a3:	48 39 cf             	cmp    %rcx,%rdi
    19a6:	75 e8                	jne    1990 <disruptor_thread+0x80>
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    19a8:	4c 89 c0             	mov    %r8,%rax
                me->data[changed].complete[x] = 0;
    19ab:	49 8b 74 24 18       	mov    0x18(%r12),%rsi
              long new = (data->thread_tag) | (changed << 32);
    19b0:	4c 63 b3 14 02 00 00 	movslq 0x214(%rbx),%r14
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    19b7:	48 99                	cqto
    19b9:	49 f7 bc 24 90 01 00 00 	idivq  0x190(%r12)
              long new = (data->thread_tag) | (changed << 32);
    19c1:	48 89 d0             	mov    %rdx,%rax
                me->data[changed].complete[x] = 0;
    19c4:	48 c1 e2 09          	shl    $0x9,%rdx
    19c8:	48 01 d6             	add    %rdx,%rsi
              long new = (data->thread_tag) | (changed << 32);
    19cb:	48 c1 e0 20          	shl    $0x20,%rax
                me->data[changed].complete[x] = 0;
    19cf:	49 89 d5             	mov    %rdx,%r13
    19d2:	48 8b 96 00 01 00 00 	mov    0x100(%rsi),%rdx
              long new = (data->thread_tag) | (changed << 32);
    19d9:	49 09 c6             	or     %rax,%r14
                me->data[changed].complete[x] = 0;
    19dc:	31 c0                	xor    %eax,%eax
    19de:	66 90                	xchg   %ax,%ax
    19e0:	c7 04 82 00 00 00 00 	movl   $0x0,(%rdx,%rax,4)
              for (int x = 0 ; x < data->other_count; x++) {
    19e7:	48 83 c0 01          	add    $0x1,%rax
    19eb:	39 83 08 02 00 00    	cmp    %eax,0x208(%rbx)
    19f1:	7f ed                	jg     19e0 <disruptor_thread+0xd0>
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    19f3:	bf 04 00 00 00       	mov    $0x4,%edi
    19f8:	e8 23 f7 ff ff       	call   1120 <clock_gettime@plt>
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED))) {
    19fd:	49 8d 8c 24 80 01 00 00 	lea    0x180(%r12),%rcx
    1a05:	48 89 e8             	mov    %rbp,%rax
    1a08:	f0 4c 0f b1 31       	lock cmpxchg %r14,(%rcx)
    1a0d:	0f 85 0b 01 00 00    	jne    1b1e <disruptor_thread+0x20e>
                me->data[changed].written = me->other_count;
    1a13:	49 8b 44 24 18       	mov    0x18(%r12),%rax
    1a18:	41 8b 94 24 08 02 00 00 	mov    0x208(%r12),%edx
    1a20:	42 89 94 28 80 01 00 00 	mov    %edx,0x180(%rax,%r13,1)
    while (data->running == 1) {
    1a28:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    1a2e:	83 f8 01             	cmp    $0x1,%eax
    1a31:	0f 84 10 ff ff ff    	je     1947 <disruptor_thread+0x37>
}
    1a37:	5b                   	pop    %rbx
    1a38:	31 c0                	xor    %eax,%eax
    1a3a:	5d                   	pop    %rbp
    1a3b:	41 5c                	pop    %r12
    1a3d:	41 5d                	pop    %r13
    1a3f:	41 5e                	pop    %r14
    1a41:	c3                   	ret
  } else if (data->mode == READER) {
    1a42:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
    1a48:	83 f8 01             	cmp    $0x1,%eax
    1a4b:	75 ea                	jne    1a37 <disruptor_thread+0x127>
    struct Thread *sender = data->sender;
    1a4d:	4c 8b 67 08          	mov    0x8(%rdi),%r12
    struct Snapshot * rdata = sender->data;
    1a51:	4d 8b 74 24 18       	mov    0x18(%r12),%r14
    while (data->running == 1) {
    1a56:	eb 1f                	jmp    1a77 <disruptor_thread+0x167>
    1a58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      int pos = ((sender->realend & END_MASK) >> 32);
    1a60:	49 63 84 24 84 01 00 00 	movslq 0x184(%r12),%rax
      if (pos == data->start) {
    1a68:	8b ab 80 00 00 00    	mov    0x80(%rbx),%ebp
      int pos = ((sender->realend & END_MASK) >> 32);
    1a6e:	25 ff ff ff 0f       	and    $0xfffffff,%eax
      if (pos == data->start) {
    1a73:	39 c5                	cmp    %eax,%ebp
    1a75:	75 3f                	jne    1ab6 <disruptor_thread+0x1a6>
    while (data->running == 1) {
    1a77:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    1a7d:	83 f8 01             	cmp    $0x1,%eax
    1a80:	74 de                	je     1a60 <disruptor_thread+0x150>
    1a82:	eb b3                	jmp    1a37 <disruptor_thread+0x127>
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1a84:	4c 89 c0             	mov    %r8,%rax
              long new = (data->thread_tag) | (changed << 32);
    1a87:	4c 63 b3 14 02 00 00 	movslq 0x214(%rbx),%r14
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1a8e:	49 8b 74 24 18       	mov    0x18(%r12),%rsi
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1a93:	48 99                	cqto
    1a95:	49 f7 bc 24 90 01 00 00 	idivq  0x190(%r12)
              long new = (data->thread_tag) | (changed << 32);
    1a9d:	48 89 d0             	mov    %rdx,%rax
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1aa0:	48 c1 e2 09          	shl    $0x9,%rdx
              long new = (data->thread_tag) | (changed << 32);
    1aa4:	48 c1 e0 20          	shl    $0x20,%rax
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1aa8:	49 89 d5             	mov    %rdx,%r13
    1aab:	48 01 d6             	add    %rdx,%rsi
              long new = (data->thread_tag) | (changed << 32);
    1aae:	49 09 c6             	or     %rax,%r14
              for (int x = 0 ; x < data->other_count; x++) {
    1ab1:	e9 3d ff ff ff       	jmp    19f3 <disruptor_thread+0xe3>
          if (rdata[changed].written > 0) {
    1ab6:	4c 63 ed             	movslq %ebp,%r13
    1ab9:	49 c1 e5 09          	shl    $0x9,%r13
    1abd:	4d 01 f5             	add    %r14,%r13
    1ac0:	41 8b 85 80 01 00 00 	mov    0x180(%r13),%eax
    1ac7:	85 c0                	test   %eax,%eax
    1ac9:	7e ac                	jle    1a77 <disruptor_thread+0x167>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1acb:	48 63 b3 0c 02 00 00 	movslq 0x20c(%rbx),%rsi
    1ad2:	bf 04 00 00 00       	mov    $0x4,%edi
    1ad7:	48 c1 e6 04          	shl    $0x4,%rsi
    1adb:	49 03 b5 80 00 00 00 	add    0x80(%r13),%rsi
    1ae2:	e8 39 f6 ff ff       	call   1120 <clock_gettime@plt>
              rdata[changed].complete[data->reader_index] = 1;
    1ae7:	49 8b 85 00 01 00 00 	mov    0x100(%r13),%rax
    1aee:	48 63 93 0c 02 00 00 	movslq 0x20c(%rbx),%rdx
    1af5:	c7 04 90 01 00 00 00 	movl   $0x1,(%rax,%rdx,4)
              data->start = (changed + 1) % data->size;
    1afc:	8d 45 01             	lea    0x1(%rbp),%eax
    1aff:	48 98                	cltq
    1b01:	48 99                	cqto
    1b03:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
    1b0a:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
              __atomic_sub_fetch(&rdata[changed].written, 1, __ATOMIC_RELAXED);
    1b10:	f0 41 83 ad 80 01 00 00 01 	lock subl $0x1,0x180(%r13)
    1b19:	e9 59 ff ff ff       	jmp    1a77 <disruptor_thread+0x167>
                original = me->realend;
    1b1e:	49 8b b4 24 80 01 00 00 	mov    0x180(%r12),%rsi
                new = (data->thread_tag) | (changed << 32);
    1b26:	48 63 bb 14 02 00 00 	movslq 0x214(%rbx),%rdi
                changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1b2d:	48 89 f0             	mov    %rsi,%rax
    1b30:	48 c1 f8 20          	sar    $0x20,%rax
    1b34:	25 ff ff ff 0f       	and    $0xfffffff,%eax
    1b39:	48 83 c0 01          	add    $0x1,%rax
    1b3d:	48 99                	cqto
    1b3f:	49 f7 bc 24 90 01 00 00 	idivq  0x190(%r12)
                new = (data->thread_tag) | (changed << 32);
    1b47:	48 89 d0             	mov    %rdx,%rax
    1b4a:	48 c1 e0 20          	shl    $0x20,%rax
    1b4e:	48 09 c7             	or     %rax,%rdi
                asm volatile ("sfence" ::: "memory");
    1b51:	0f ae f8             	sfence
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED))) {
    1b54:	48 89 f0             	mov    %rsi,%rax
    1b57:	f0 48 0f b1 39       	lock cmpxchg %rdi,(%rcx)
    1b5c:	75 c0                	jne    1b1e <disruptor_thread+0x20e>
                me->data[changed].written = me->other_count;
    1b5e:	48 c1 e2 09          	shl    $0x9,%rdx
    1b62:	49 89 d5             	mov    %rdx,%r13
    1b65:	e9 a9 fe ff ff       	jmp    1a13 <disruptor_thread+0x103>
    1b6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001b70 <min>:
int min(long a, long b) {
    1b70:	f3 0f 1e fa          	endbr64
  if (a < b) return a;
    1b74:	48 39 f7             	cmp    %rsi,%rdi
    1b77:	7c 02                	jl     1b7b <min+0xb>
  if (b < a) return b;
    1b79:	7f 05                	jg     1b80 <min+0x10>
  if (a < b) return a;
    1b7b:	89 f8                	mov    %edi,%eax
    1b7d:	c3                   	ret
    1b7e:	66 90                	xchg   %ax,%ax
  if (b < a) return b;
    1b80:	89 f0                	mov    %esi,%eax
}
    1b82:	c3                   	ret

Disassembly of section .fini:

0000000000001b84 <_fini>:
    1b84:	f3 0f 1e fa          	endbr64
    1b88:	48 83 ec 08          	sub    $0x8,%rsp
    1b8c:	48 83 c4 08          	add    $0x8,%rsp
    1b90:	c3                   	ret
