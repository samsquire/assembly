
disruptor-multi-consumer-tsansafe:     file format elf64-x86-64


Disassembly of section .init:

0000000000001000 <_init>:
    1000:	f3 0f 1e fa          	endbr64
    1004:	48 83 ec 08          	sub    $0x8,%rsp
    1008:	48 8d 05 31 09 00 00 	lea    0x931(%rip),%rax        # 1940 <__gmon_start__>
    100f:	48 85 c0             	test   %rax,%rax
    1012:	74 02                	je     1016 <_init+0x16>
    1014:	ff d0                	call   *%rax
    1016:	48 83 c4 08          	add    $0x8,%rsp
    101a:	c3                   	ret

Disassembly of section .plt:

0000000000001020 <.plt>:
    1020:	ff 35 2a 2f 00 00    	push   0x2f2a(%rip)        # 3f50 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:	ff 25 2c 2f 00 00    	jmp    *0x2f2c(%rip)        # 3f58 <_GLOBAL_OFFSET_TABLE_+0x10>
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
    10f0:	f3 0f 1e fa          	endbr64
    10f4:	68 0c 00 00 00       	push   $0xc
    10f9:	e9 22 ff ff ff       	jmp    1020 <_init+0x20>
    10fe:	66 90                	xchg   %ax,%ax
    1100:	f3 0f 1e fa          	endbr64
    1104:	68 0d 00 00 00       	push   $0xd
    1109:	e9 12 ff ff ff       	jmp    1020 <_init+0x20>
    110e:	66 90                	xchg   %ax,%ax

Disassembly of section .plt.got:

0000000000001110 <__cxa_finalize@plt>:
    1110:	f3 0f 1e fa          	endbr64
    1114:	ff 25 de 2e 00 00    	jmp    *0x2ede(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    111a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000001120 <pthread_setaffinity_np@plt>:
    1120:	f3 0f 1e fa          	endbr64
    1124:	ff 25 36 2e 00 00    	jmp    *0x2e36(%rip)        # 3f60 <pthread_setaffinity_np@GLIBC_2.34>
    112a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001130 <puts@plt>:
    1130:	f3 0f 1e fa          	endbr64
    1134:	ff 25 2e 2e 00 00    	jmp    *0x2e2e(%rip)        # 3f68 <puts@GLIBC_2.2.5>
    113a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001140 <clock_gettime@plt>:
    1140:	f3 0f 1e fa          	endbr64
    1144:	ff 25 26 2e 00 00    	jmp    *0x2e26(%rip)        # 3f70 <clock_gettime@GLIBC_2.17>
    114a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001150 <__stack_chk_fail@plt>:
    1150:	f3 0f 1e fa          	endbr64
    1154:	ff 25 1e 2e 00 00    	jmp    *0x2e1e(%rip)        # 3f78 <__stack_chk_fail@GLIBC_2.4>
    115a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001160 <nanosleep@plt>:
    1160:	f3 0f 1e fa          	endbr64
    1164:	ff 25 16 2e 00 00    	jmp    *0x2e16(%rip)        # 3f80 <nanosleep@GLIBC_2.2.5>
    116a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001170 <pthread_attr_setschedpolicy@plt>:
    1170:	f3 0f 1e fa          	endbr64
    1174:	ff 25 0e 2e 00 00    	jmp    *0x2e0e(%rip)        # 3f88 <pthread_attr_setschedpolicy@GLIBC_2.2.5>
    117a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001180 <calloc@plt>:
    1180:	f3 0f 1e fa          	endbr64
    1184:	ff 25 06 2e 00 00    	jmp    *0x2e06(%rip)        # 3f90 <calloc@GLIBC_2.2.5>
    118a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001190 <__monstartup@plt>:
    1190:	f3 0f 1e fa          	endbr64
    1194:	ff 25 fe 2d 00 00    	jmp    *0x2dfe(%rip)        # 3f98 <__monstartup@GLIBC_2.2.5>
    119a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011a0 <__printf_chk@plt>:
    11a0:	f3 0f 1e fa          	endbr64
    11a4:	ff 25 f6 2d 00 00    	jmp    *0x2df6(%rip)        # 3fa0 <__printf_chk@GLIBC_2.3.4>
    11aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011b0 <pthread_create@plt>:
    11b0:	f3 0f 1e fa          	endbr64
    11b4:	ff 25 ee 2d 00 00    	jmp    *0x2dee(%rip)        # 3fa8 <pthread_create@GLIBC_2.34>
    11ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011c0 <pthread_attr_setschedparam@plt>:
    11c0:	f3 0f 1e fa          	endbr64
    11c4:	ff 25 e6 2d 00 00    	jmp    *0x2de6(%rip)        # 3fb0 <pthread_attr_setschedparam@GLIBC_2.2.5>
    11ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011d0 <__cxa_atexit@plt>:
    11d0:	f3 0f 1e fa          	endbr64
    11d4:	ff 25 de 2d 00 00    	jmp    *0x2dde(%rip)        # 3fb8 <__cxa_atexit@GLIBC_2.2.5>
    11da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011e0 <exit@plt>:
    11e0:	f3 0f 1e fa          	endbr64
    11e4:	ff 25 d6 2d 00 00    	jmp    *0x2dd6(%rip)        # 3fc0 <exit@GLIBC_2.2.5>
    11ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000011f0 <pthread_join@plt>:
    11f0:	f3 0f 1e fa          	endbr64
    11f4:	ff 25 ce 2d 00 00    	jmp    *0x2dce(%rip)        # 3fc8 <pthread_join@GLIBC_2.34>
    11fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000001200 <main>:
  } 
  // printf("Finished %d\n", data->mode);
  return 0;
}

int main() {
    1200:	f3 0f 1e fa          	endbr64
    1204:	55                   	push   %rbp
    1205:	48 89 e5             	mov    %rsp,%rbp
    1208:	41 57                	push   %r15
    120a:	41 56                	push   %r14
    120c:	41 55                	push   %r13
    120e:	41 54                	push   %r12
    1210:	53                   	push   %rbx
    1211:	48 81 ec a8 00 00 00 	sub    $0xa8,%rsp
    1218:	ff 15 ca 2d 00 00    	call   *0x2dca(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    121e:	b9 00 80 00 00       	mov    $0x8000,%ecx
    1223:	ba 0f 00 00 00       	mov    $0xf,%edx
    1228:	bf 01 00 00 00       	mov    $0x1,%edi
    122d:	48 8d 35 d4 0d 00 00 	lea    0xdd4(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int receiver2 = receiver + 1; 
    int seq[] = {1, 2, 5};
    int tag_index[] = {1, 5, 7};
    1234:	45 31 f6             	xor    %r14d,%r14d
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    1237:	45 31 ed             	xor    %r13d,%r13d
int main() {
    123a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1243:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    1247:	31 c0                	xor    %eax,%eax
    1249:	e8 52 ff ff ff       	call   11a0 <__printf_chk@plt>
    124e:	ba 01 00 00 00       	mov    $0x1,%edx
    1253:	48 8d 35 3f 0e 00 00 	lea    0xe3f(%rip),%rsi        # 2099 <_IO_stdin_used+0x99>
    125a:	31 c0                	xor    %eax,%eax
    125c:	bf 01 00 00 00       	mov    $0x1,%edi
    1261:	e8 3a ff ff ff       	call   11a0 <__printf_chk@plt>
    1266:	ba 02 00 00 00       	mov    $0x2,%edx
    126b:	48 8d 35 37 0e 00 00 	lea    0xe37(%rip),%rsi        # 20a9 <_IO_stdin_used+0xa9>
    1272:	31 c0                	xor    %eax,%eax
    1274:	bf 01 00 00 00       	mov    $0x1,%edi
    1279:	e8 22 ff ff ff       	call   11a0 <__printf_chk@plt>
    127e:	ba 02 00 00 00       	mov    $0x2,%edx
    1283:	48 8d 35 31 0e 00 00 	lea    0xe31(%rip),%rsi        # 20bb <_IO_stdin_used+0xbb>
    128a:	31 c0                	xor    %eax,%eax
    128c:	bf 01 00 00 00       	mov    $0x1,%edi
    1291:	e8 0a ff ff ff       	call   11a0 <__printf_chk@plt>
    1296:	ba 04 00 00 00       	mov    $0x4,%edx
    129b:	48 8d 35 2b 0e 00 00 	lea    0xe2b(%rip),%rsi        # 20cd <_IO_stdin_used+0xcd>
    12a2:	31 c0                	xor    %eax,%eax
    12a4:	bf 01 00 00 00       	mov    $0x1,%edi
    12a9:	e8 f2 fe ff ff       	call   11a0 <__printf_chk@plt>
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    12ae:	be 80 02 00 00       	mov    $0x280,%esi
    12b3:	bf 04 00 00 00       	mov    $0x4,%edi
    12b8:	e8 c3 fe ff ff       	call   1180 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12bd:	be 38 00 00 00       	mov    $0x38,%esi
    12c2:	bf 04 00 00 00       	mov    $0x4,%edi
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    12c7:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12ca:	e8 b1 fe ff ff       	call   1180 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12cf:	be 08 00 00 00       	mov    $0x8,%esi
    12d4:	bf 04 00 00 00       	mov    $0x4,%edi
    12d9:	4d 89 fc             	mov    %r15,%r12
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12dc:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12e3:	e8 98 fe ff ff       	call   1180 <calloc@plt>
    12e8:	4c 89 bd 68 ff ff ff 	mov    %r15,-0x98(%rbp)
    12ef:	48 89 c3             	mov    %rax,%rbx
    int seq[] = {1, 2, 5};
    12f2:	48 8b 05 3f 0e 00 00 	mov    0xe3f(%rip),%rax        # 2138 <_IO_stdin_used+0x138>
    12f9:	48 89 9d 50 ff ff ff 	mov    %rbx,-0xb0(%rbp)
    1300:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
    int tag_index[] = {1, 5, 7};
    1304:	48 8b 05 35 0e 00 00 	mov    0xe35(%rip),%rax        # 2140 <_IO_stdin_used+0x140>
    130b:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    130f:	48 8d 45 a8          	lea    -0x58(%rbp),%rax
    1313:	48 89 85 60 ff ff ff 	mov    %rax,-0xa0(%rbp)
    131a:	48 8d 45 b8          	lea    -0x48(%rbp),%rax
    131e:	48 89 85 40 ff ff ff 	mov    %rax,-0xc0(%rbp)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1325:	be 80 00 00 00       	mov    $0x80,%esi
    132a:	bf 01 00 00 00       	mov    $0x1,%edi
    132f:	47 8d 7c 2d 00       	lea    0x0(%r13,%r13,1),%r15d
    1334:	e8 47 fe ff ff       	call   1180 <calloc@plt>
      CPU_ZERO(sendercpu);
      CPU_SET(curcpu, sendercpu);
    1339:	44 89 f9             	mov    %r15d,%ecx
    133c:	44 89 ea             	mov    %r13d,%edx
    133f:	bf 01 00 00 00       	mov    $0x1,%edi
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1344:	48 89 c3             	mov    %rax,%rbx
      CPU_SET(curcpu, sendercpu);
    1347:	b8 01 00 00 00       	mov    $0x1,%eax
    134c:	48 8d 35 dd 0c 00 00 	lea    0xcdd(%rip),%rsi        # 2030 <_IO_stdin_used+0x30>
    1353:	48 d3 e0             	shl    %cl,%rax
    1356:	48 09 03             	or     %rax,(%rbx)
    1359:	44 89 f9             	mov    %r15d,%ecx
    135c:	31 c0                	xor    %eax,%eax
    135e:	e8 3d fe ff ff       	call   11a0 <__printf_chk@plt>
      curcpu += coreinterval;
       
      thread_data[n].thread_index = n;
      thread_data[n].cpu_set = sendercpu;
      thread_data[n].mode = WRITER;
      thread_data[n].multiple = seq[sender_index % writers_count];
    1363:	48 8b 85 60 ff ff ff 	mov    -0xa0(%rbp),%rax
      thread_data[n].thread_index = n;
    136a:	45 89 2c 24          	mov    %r13d,(%r12)
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].thread_tag = tag_index[sender_index];
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    136e:	be 08 00 00 00       	mov    $0x8,%esi
      thread_data[n].cpu_set = sendercpu;
    1373:	49 89 9c 24 a0 01 00 00 	mov    %rbx,0x1a0(%r12)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    137b:	bf 02 00 00 00       	mov    $0x2,%edi
      thread_data[n].mode = WRITER;
    1380:	41 c7 84 24 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%r12)
      thread_data[n].multiple = seq[sender_index % writers_count];
    138c:	42 8b 04 30          	mov    (%rax,%r14,1),%eax
      thread_data[n].running = 1;
    1390:	41 c7 84 24 98 01 00 00 01 00 00 00 	movl   $0x1,0x198(%r12)
      thread_data[n].multiple = seq[sender_index % writers_count];
    139c:	41 89 84 24 10 02 00 00 	mov    %eax,0x210(%r12)
      thread_data[n].thread_tag = tag_index[sender_index];
    13a4:	48 8b 85 40 ff ff ff 	mov    -0xc0(%rbp),%rax
      thread_data[n].size = buffer_size;
    13ab:	49 c7 84 24 90 01 00 00 00 80 00 00 	movq   $0x8000,0x190(%r12)
      thread_data[n].end = 0;
    13b7:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
      thread_data[n].thread_tag = tag_index[sender_index];
    13c3:	42 8b 04 30          	mov    (%rax,%r14,1),%eax
    13c7:	41 89 84 24 14 02 00 00 	mov    %eax,0x214(%r12)
      thread_data[n].sender = &thread_data[sender];
    13cf:	48 8b 85 68 ff ff ff 	mov    -0x98(%rbp),%rax
    13d6:	49 89 44 24 08       	mov    %rax,0x8(%r12)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    13db:	e8 a0 fd ff ff       	call   1180 <calloc@plt>
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    13e0:	be 00 02 00 00       	mov    $0x200,%esi
    13e5:	bf 00 80 00 00       	mov    $0x8000,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    13ea:	49 89 84 24 00 02 00 00 	mov    %rax,0x200(%r12)
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    13f2:	e8 89 fd ff ff       	call   1180 <calloc@plt>
    13f7:	49 89 44 24 18       	mov    %rax,0x18(%r12)
      for (int k = 0 ; k < buffer_size ; k++) {
    13fc:	4c 8d b8 80 00 00 00 	lea    0x80(%rax),%r15
    1403:	48 8d 98 80 00 00 01 	lea    0x1000080(%rax),%rbx
    140a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1410:	be 04 00 00 00       	mov    $0x4,%esi
    1415:	bf 02 00 00 00       	mov    $0x2,%edi
      for (int k = 0 ; k < buffer_size ; k++) {
    141a:	49 81 c7 00 02 00 00 	add    $0x200,%r15
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1421:	e8 5a fd ff ff       	call   1180 <calloc@plt>
        thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    1426:	be 10 00 00 00       	mov    $0x10,%esi
    142b:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1430:	49 89 87 80 fe ff ff 	mov    %rax,-0x180(%r15)
        thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    1437:	e8 44 fd ff ff       	call   1180 <calloc@plt>
    143c:	49 89 87 00 fe ff ff 	mov    %rax,-0x200(%r15)
      for (int k = 0 ; k < buffer_size ; k++) {
    1443:	49 39 df             	cmp    %rbx,%r15
    1446:	75 c8                	jne    1410 <main+0x210>
      }
      thread_data[n].other_count = other_count;
    1448:	41 c7 84 24 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%r12)
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
    1454:	49 83 c6 04          	add    $0x4,%r14
    1458:	49 81 c4 80 02 00 00 	add    $0x280,%r12
    145f:	45 85 ed             	test   %r13d,%r13d
    1462:	75 0b                	jne    146f <main+0x26f>
    1464:	41 bd 01 00 00 00    	mov    $0x1,%r13d
    146a:	e9 b6 fe ff ff       	jmp    1325 <main+0x125>
    146f:	4c 8b bd 68 ff ff ff 	mov    -0x98(%rbp),%r15
    1476:	48 8b 9d 50 ff ff ff 	mov    -0xb0(%rbp),%rbx
    147d:	45 31 f6             	xor    %r14d,%r14d
    }

    // printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1480:	c7 85 68 ff ff ff 02 00 00 00 	movl   $0x2,-0x98(%rbp)
    148a:	49 8d 87 00 05 00 00 	lea    0x500(%r15),%rax
    1491:	66 49 0f 6e d7       	movq   %r15,%xmm2
    1496:	48 89 9d 38 ff ff ff 	mov    %rbx,-0xc8(%rbp)
    149d:	4c 89 f3             	mov    %r14,%rbx
    14a0:	48 89 85 50 ff ff ff 	mov    %rax,-0xb0(%rbp)
    14a7:	66 0f 6c d2          	punpcklqdq %xmm2,%xmm2
    14ab:	4d 89 fe             	mov    %r15,%r14
    14ae:	49 89 c7             	mov    %rax,%r15
    14b1:	0f 29 95 40 ff ff ff 	movaps %xmm2,-0xc0(%rbp)
    14b8:	8b 85 68 ff ff ff    	mov    -0x98(%rbp),%eax
      thread_data[j].thread_index = j;
      thread_data[j].reader_index = receiver_index;
      thread_data[j].multiple = receiver_index % other_count;
      thread_data[j].other_count = other_count;
     
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    14be:	be 80 00 00 00       	mov    $0x80,%esi
      thread_data[j].reader_index = receiver_index;
    14c3:	41 89 9f 0c 02 00 00 	mov    %ebx,0x20c(%r15)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    14ca:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].multiple = receiver_index % other_count;
    14cf:	41 89 9f 10 02 00 00 	mov    %ebx,0x210(%r15)
      thread_data[j].thread_index = j;
    14d6:	41 89 07             	mov    %eax,(%r15)
    14d9:	44 8d 2c 00          	lea    (%rax,%rax,1),%r13d
      thread_data[j].other_count = other_count;
    14dd:	41 c7 87 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%r15)
    14e8:	89 9d 60 ff ff ff    	mov    %ebx,-0xa0(%rbp)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    14ee:	e8 8d fc ff ff       	call   1180 <calloc@plt>
      CPU_ZERO(receivercpu);
      CPU_SET(curcpu, receivercpu);
    14f3:	44 89 e9             	mov    %r13d,%ecx
    14f6:	bf 01 00 00 00       	mov    $0x1,%edi
    14fb:	48 8d 35 4e 0b 00 00 	lea    0xb4e(%rip),%rsi        # 2050 <_IO_stdin_used+0x50>
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1502:	49 89 c4             	mov    %rax,%r12
      CPU_SET(curcpu, receivercpu);
    1505:	b8 01 00 00 00       	mov    $0x1,%eax
    150a:	48 d3 e0             	shl    %cl,%rax
    150d:	49 09 04 24          	or     %rax,(%r12)
    1511:	44 89 e9             	mov    %r13d,%ecx
    1514:	31 c0                	xor    %eax,%eax
    1516:	44 8b ad 68 ff ff ff 	mov    -0x98(%rbp),%r13d
    151d:	44 89 ea             	mov    %r13d,%edx
    1520:	e8 7b fc ff ff       	call   11a0 <__printf_chk@plt>
      printf("assigning receiver %d to core %d\n", j, curcpu);
      curcpu += coreinterval;
      thread_data[j].cpu_set = receivercpu;
    1525:	4d 89 a7 a0 01 00 00 	mov    %r12,0x1a0(%r15)
      thread_data[j].running = 1;
    152c:	41 c7 87 98 01 00 00 01 00 00 00 	movl   $0x1,0x198(%r15)
      thread_data[j].mode = READER;
    1537:	41 c7 87 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%r15)
      if (j == receiver) {
    1542:	41 83 fd 02          	cmp    $0x2,%r13d
    1546:	0f 84 34 03 00 00    	je     1880 <main+0x680>
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    154c:	49 8b 86 00 02 00 00 	mov    0x200(%r14),%rax
    1553:	31 c9                	xor    %ecx,%ecx
      thread_data[j].size = buffer_size;
    1555:	49 c7 87 90 01 00 00 00 80 00 00 	movq   $0x8000,0x190(%r15)
    1560:	48 8d 35 11 0b 00 00 	lea    0xb11(%rip),%rsi        # 2078 <_IO_stdin_used+0x78>
      thread_data[j].start = 0;
    1567:	41 c7 87 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r15)
      thread_data[j].sender = &thread_data[sender];
    1572:	66 0f 6f 8d 40 ff ff ff 	movdqa -0xc0(%rbp),%xmm1
    157a:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].readers = thread_data[sender].readers;
    157f:	49 89 87 00 02 00 00 	mov    %rax,0x200(%r15)
    1586:	44 8b ad 60 ff ff ff 	mov    -0xa0(%rbp),%r13d
    158d:	31 c0                	xor    %eax,%eax
      thread_data[j].other_count = other_count;
    158f:	41 c7 87 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%r15)
      thread_data[j].sender = &thread_data[sender];
    159a:	41 0f 11 4f 08       	movups %xmm1,0x8(%r15)
    159f:	44 89 ea             	mov    %r13d,%edx
    15a2:	e8 f9 fb ff ff       	call   11a0 <__printf_chk@plt>
      // printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        printf("assigned reader %d to sender %d\n", receiver_index, n);
        thread_data[n].readers[receiver_index] = &thread_data[j];
    15a7:	49 8b 86 00 02 00 00 	mov    0x200(%r14),%rax
    15ae:	44 89 ea             	mov    %r13d,%edx
    15b1:	b9 01 00 00 00       	mov    $0x1,%ecx
    15b6:	48 8d 35 bb 0a 00 00 	lea    0xabb(%rip),%rsi        # 2078 <_IO_stdin_used+0x78>
    15bd:	bf 01 00 00 00       	mov    $0x1,%edi
    15c2:	4c 89 3c d8          	mov    %r15,(%rax,%rbx,8)
    15c6:	31 c0                	xor    %eax,%eax
    15c8:	e8 d3 fb ff ff       	call   11a0 <__printf_chk@plt>
    15cd:	49 8b 86 80 04 00 00 	mov    0x480(%r14),%rax
    15d4:	4c 89 3c d8          	mov    %r15,(%rax,%rbx,8)
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15d8:	48 83 c3 01          	add    $0x1,%rbx
    15dc:	49 81 c7 80 02 00 00 	add    $0x280,%r15
    15e3:	83 bd 68 ff ff ff 02 	cmpl   $0x2,-0x98(%rbp)
    15ea:	75 0f                	jne    15fb <main+0x3fb>
    15ec:	c7 85 68 ff ff ff 03 00 00 00 	movl   $0x3,-0x98(%rbp)
    15f6:	e9 bd fe ff ff       	jmp    14b8 <main+0x2b8>
    15fb:	4d 89 f7             	mov    %r14,%r15
    15fe:	48 8b 9d 38 ff ff ff 	mov    -0xc8(%rbp),%rbx
      }
    }
    curcpu = 0;
    // printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    1605:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    1608:	48 8b 85 58 ff ff ff 	mov    -0xa8(%rbp),%rax
      if (ret) {
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    160f:	4c 89 bd 68 ff ff ff 	mov    %r15,-0x98(%rbp)
    1616:	4c 8d 63 10          	lea    0x10(%rbx),%r12
  param.sched_priority = 0;
    161a:	c7 85 7c ff ff ff 00 00 00 00 	movl   $0x0,-0x84(%rbp)
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1624:	4c 8b bd 50 ff ff ff 	mov    -0xb0(%rbp),%r15
    162b:	4c 8d 68 70          	lea    0x70(%rax),%r13
    162f:	4c 8d b0 e0 00 00 00 	lea    0xe0(%rax),%r14
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    1636:	31 f6                	xor    %esi,%esi
    1638:	4c 89 ef             	mov    %r13,%rdi
    163b:	e8 30 fb ff ff       	call   1170 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    1640:	85 c0                	test   %eax,%eax
    1642:	0f 85 88 02 00 00    	jne    18d0 <main+0x6d0>
      ret = pthread_attr_setschedparam(&attr[j], &param);
    1648:	48 8d b5 7c ff ff ff 	lea    -0x84(%rbp),%rsi
    164f:	4c 89 ef             	mov    %r13,%rdi
    1652:	e8 69 fb ff ff       	call   11c0 <pthread_attr_setschedparam@plt>
      if (ret) {
    1657:	85 c0                	test   %eax,%eax
    1659:	0f 85 8c 02 00 00    	jne    18eb <main+0x6eb>
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    165f:	4c 89 f9             	mov    %r15,%rcx
    1662:	4c 89 ee             	mov    %r13,%rsi
    1665:	4c 89 e7             	mov    %r12,%rdi
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1668:	49 83 c5 38          	add    $0x38,%r13
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    166c:	48 8d 15 ed 03 00 00 	lea    0x3ed(%rip),%rdx        # 1a60 <disruptor_thread>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1673:	49 83 c4 08          	add    $0x8,%r12
    1677:	49 81 c7 80 02 00 00 	add    $0x280,%r15
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    167e:	e8 2d fb ff ff       	call   11b0 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    1683:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
    1688:	be 08 00 00 00       	mov    $0x8,%esi
    168d:	49 8b 97 20 ff ff ff 	mov    -0xe0(%r15),%rdx
    1694:	e8 87 fa ff ff       	call   1120 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1699:	4d 39 f5             	cmp    %r14,%r13
    169c:	75 98                	jne    1636 <main+0x436>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    169e:	4c 8b b5 58 ff ff ff 	mov    -0xa8(%rbp),%r14
    16a5:	31 f6                	xor    %esi,%esi
    16a7:	4c 8b bd 68 ff ff ff 	mov    -0x98(%rbp),%r15
    16ae:	4c 89 f7             	mov    %r14,%rdi
    16b1:	e8 ba fa ff ff       	call   1170 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    16b6:	85 c0                	test   %eax,%eax
    16b8:	0f 85 12 02 00 00    	jne    18d0 <main+0x6d0>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    16be:	48 8d b5 78 ff ff ff 	lea    -0x88(%rbp),%rsi
    16c5:	4c 89 f7             	mov    %r14,%rdi
      param2.sched_priority = 0;
    16c8:	c7 85 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rbp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    16d2:	e8 e9 fa ff ff       	call   11c0 <pthread_attr_setschedparam@plt>
      if (ret) {
    16d7:	85 c0                	test   %eax,%eax
    16d9:	0f 85 0c 02 00 00    	jne    18eb <main+0x6eb>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    16df:	4c 89 f9             	mov    %r15,%rcx
    16e2:	48 89 df             	mov    %rbx,%rdi
    16e5:	48 8d 15 74 03 00 00 	lea    0x374(%rip),%rdx        # 1a60 <disruptor_thread>
    16ec:	4c 89 f6             	mov    %r14,%rsi
    16ef:	e8 bc fa ff ff       	call   11b0 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    16f4:	48 8b 3b             	mov    (%rbx),%rdi
    16f7:	be 08 00 00 00       	mov    $0x8,%esi
    void * res1;
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    16fc:	45 31 e4             	xor    %r12d,%r12d
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    16ff:	49 8b 97 a0 01 00 00 	mov    0x1a0(%r15),%rdx
    1706:	e8 15 fa ff ff       	call   1120 <pthread_setaffinity_np@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    170b:	4c 89 f6             	mov    %r14,%rsi
    170e:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    1712:	49 8d 8f 80 02 00 00 	lea    0x280(%r15),%rcx
    1719:	48 83 c6 38          	add    $0x38,%rsi
    171d:	48 8d 15 3c 03 00 00 	lea    0x33c(%rip),%rdx        # 1a60 <disruptor_thread>
    1724:	e8 87 fa ff ff       	call   11b0 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    1729:	49 8b 97 20 04 00 00 	mov    0x420(%r15),%rdx
    1730:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    1734:	be 08 00 00 00       	mov    $0x8,%esi
    1739:	e8 e2 f9 ff ff       	call   1120 <pthread_setaffinity_np@plt>
  nanosleep(&preempt , &rem2);
    173e:	48 8d 75 80          	lea    -0x80(%rbp),%rsi
    1742:	48 8d 7d 90          	lea    -0x70(%rbp),%rdi
  struct timespec preempt = {
    1746:	66 0f 6f 05 02 0a 00 00 	movdqa 0xa02(%rip),%xmm0        # 2150 <_IO_stdin_used+0x150>
    174e:	0f 29 45 90          	movaps %xmm0,-0x70(%rbp)
  nanosleep(&preempt , &rem2);
    1752:	e8 09 fa ff ff       	call   1160 <nanosleep@plt>
      pthread_join(thread[n], res1);
    1757:	48 8b 3b             	mov    (%rbx),%rdi
    175a:	4c 89 e6             	mov    %r12,%rsi
    thread_data[sender].running = 0;
    175d:	41 c7 87 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r15)
      thread_data[j].running = 0;
    1768:	41 c7 87 98 06 00 00 00 00 00 00 	movl   $0x0,0x698(%r15)
    1773:	41 c7 87 18 09 00 00 00 00 00 00 	movl   $0x0,0x918(%r15)
      thread_data[n].running = 0;
    177e:	41 c7 87 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r15)
    1789:	41 c7 87 18 04 00 00 00 00 00 00 	movl   $0x0,0x418(%r15)
      pthread_join(thread[n], res1);
    1794:	e8 57 fa ff ff       	call   11f0 <pthread_join@plt>
    1799:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    179d:	4c 89 e6             	mov    %r12,%rsi
    17a0:	e8 4b fa ff ff       	call   11f0 <pthread_join@plt>
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    17a5:	48 8b 7b 10          	mov    0x10(%rbx),%rdi
    17a9:	4c 89 e6             	mov    %r12,%rsi
    17ac:	e8 3f fa ff ff       	call   11f0 <pthread_join@plt>
    17b1:	48 8b 7b 18          	mov    0x18(%rbx),%rdi
    17b5:	4c 89 e6             	mov    %r12,%rsi
    17b8:	31 db                	xor    %ebx,%ebx
    17ba:	4c 8d 25 5e 09 00 00 	lea    0x95e(%rip),%r12        # 211f <_IO_stdin_used+0x11f>
    17c1:	e8 2a fa ff ff       	call   11f0 <pthread_join@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    // printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    17c6:	eb 18                	jmp    17e0 <main+0x5e0>
    17c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    17d0:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
    17d7:	48 81 fb 00 00 00 01 	cmp    $0x1000000,%rbx
    17de:	74 7d                	je     185d <main+0x65d>
      int compcount = 0;
      for (int n = 0 ; n < other_count ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    17e0:	49 8b 47 18          	mov    0x18(%r15),%rax
    17e4:	48 01 d8             	add    %rbx,%rax
    17e7:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
    17ee:	83 3a 01             	cmpl   $0x1,(%rdx)
    17f1:	75 dd                	jne    17d0 <main+0x5d0>
    17f3:	83 7a 04 01          	cmpl   $0x1,0x4(%rdx)
    17f7:	75 d7                	jne    17d0 <main+0x5d0>
      // printf("%d\n", compcount);
      if (compcount == other_count) {
      for (int n = 0 ; n < other_count ; n++) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
          struct timespec end = thread_data[sender].data[y].end[n];
    17f9:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    1800:	4c 89 e6             	mov    %r12,%rsi
    1803:	bf 01 00 00 00       	mov    $0x1,%edi
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    1808:	4c 8b 42 08          	mov    0x8(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    180c:	48 8b 0a             	mov    (%rdx),%rcx
    180f:	31 d2                	xor    %edx,%edx
    1811:	48 2b 08             	sub    (%rax),%rcx
    1814:	4c 2b 40 08          	sub    0x8(%rax),%r8
    1818:	31 c0                	xor    %eax,%eax
    181a:	e8 81 f9 ff ff       	call   11a0 <__printf_chk@plt>
          struct timespec start = thread_data[sender].data[y].start;
    181f:	49 8b 47 18          	mov    0x18(%r15),%rax
    1823:	4c 89 e6             	mov    %r12,%rsi
    1826:	bf 01 00 00 00       	mov    $0x1,%edi
    182b:	48 01 d8             	add    %rbx,%rax
    for (int y = 0 ; y < buffer_size; y++) {
    182e:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
          struct timespec end = thread_data[sender].data[y].end[n];
    1835:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    183c:	4c 8b 42 18          	mov    0x18(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    1840:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    1844:	31 d2                	xor    %edx,%edx
    1846:	48 2b 08             	sub    (%rax),%rcx
    1849:	4c 2b 40 08          	sub    0x8(%rax),%r8
    184d:	31 c0                	xor    %eax,%eax
    184f:	e8 4c f9 ff ff       	call   11a0 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    1854:	48 81 fb 00 00 00 01 	cmp    $0x1000000,%rbx
    185b:	75 83                	jne    17e0 <main+0x5e0>
    }
    // printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    185d:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    1861:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    186a:	75 7a                	jne    18e6 <main+0x6e6>
    186c:	48 81 c4 a8 00 00 00 	add    $0xa8,%rsp
    1873:	31 c0                	xor    %eax,%eax
    1875:	5b                   	pop    %rbx
    1876:	41 5c                	pop    %r12
    1878:	41 5d                	pop    %r13
    187a:	41 5e                	pop    %r14
    187c:	41 5f                	pop    %r15
    187e:	5d                   	pop    %rbp
    187f:	c3                   	ret
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    1880:	be 00 02 00 00       	mov    $0x200,%esi
    1885:	bf 00 80 00 00       	mov    $0x8000,%edi
    188a:	e8 f1 f8 ff ff       	call   1180 <calloc@plt>
    188f:	49 89 47 18          	mov    %rax,0x18(%r15)
    1893:	49 89 c5             	mov    %rax,%r13
        for (int n = 0 ; n < buffer_size ; n++) {
    1896:	4c 8d a0 00 01 00 00 	lea    0x100(%rax),%r12
    189d:	49 81 c5 00 01 00 01 	add    $0x1000100,%r13
    18a4:	0f 1f 40 00          	nopl   0x0(%rax)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    18a8:	be 04 00 00 00       	mov    $0x4,%esi
    18ad:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    18b2:	49 81 c4 00 02 00 00 	add    $0x200,%r12
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    18b9:	e8 c2 f8 ff ff       	call   1180 <calloc@plt>
    18be:	49 89 84 24 00 fe ff ff 	mov    %rax,-0x200(%r12)
        for (int n = 0 ; n < buffer_size ; n++) {
    18c6:	4d 39 ec             	cmp    %r13,%r12
    18c9:	75 dd                	jne    18a8 <main+0x6a8>
    18cb:	e9 7c fc ff ff       	jmp    154c <main+0x34c>
    18d0:	48 8d 3d 0d 08 00 00 	lea    0x80d(%rip),%rdi        # 20e4 <_IO_stdin_used+0xe4>
    18d7:	e8 54 f8 ff ff       	call   1130 <puts@plt>
               exit(1);
    18dc:	bf 01 00 00 00       	mov    $0x1,%edi
    18e1:	e8 fa f8 ff ff       	call   11e0 <exit@plt>
}
    18e6:	e8 65 f8 ff ff       	call   1150 <__stack_chk_fail@plt>
    18eb:	48 8d 3d 10 08 00 00 	lea    0x810(%rip),%rdi        # 2102 <_IO_stdin_used+0x102>
    18f2:	e8 39 f8 ff ff       	call   1130 <puts@plt>
              exit(1);
    18f7:	bf 01 00 00 00       	mov    $0x1,%edi
    18fc:	e8 df f8 ff ff       	call   11e0 <exit@plt>
    1901:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    190b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000001910 <_start>:
    1910:	f3 0f 1e fa          	endbr64
    1914:	31 ed                	xor    %ebp,%ebp
    1916:	49 89 d1             	mov    %rdx,%r9
    1919:	5e                   	pop    %rsi
    191a:	48 89 e2             	mov    %rsp,%rdx
    191d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1921:	50                   	push   %rax
    1922:	54                   	push   %rsp
    1923:	45 31 c0             	xor    %r8d,%r8d
    1926:	31 c9                	xor    %ecx,%ecx
    1928:	48 8d 3d d1 f8 ff ff 	lea    -0x72f(%rip),%rdi        # 1200 <main>
    192f:	ff 15 9b 26 00 00    	call   *0x269b(%rip)        # 3fd0 <__libc_start_main@GLIBC_2.34>
    1935:	f4                   	hlt
    1936:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001940 <__gmon_start__>:
    1940:	f3 0f 1e fa          	endbr64
    1944:	8b 05 c6 26 00 00    	mov    0x26c6(%rip),%eax        # 4010 <__TMC_END__>
    194a:	85 c0                	test   %eax,%eax
    194c:	74 02                	je     1950 <__gmon_start__+0x10>
    194e:	c3                   	ret
    194f:	90                   	nop
    1950:	48 83 ec 08          	sub    $0x8,%rsp
    1954:	48 8d 35 d2 03 00 00 	lea    0x3d2(%rip),%rsi        # 1d2d <etext>
    195b:	48 8d 3d 9e e6 ff ff 	lea    -0x1962(%rip),%rdi        # 0 <__executable_start>
    1962:	c7 05 a4 26 00 00 01 00 00 00 	movl   $0x1,0x26a4(%rip)        # 4010 <__TMC_END__>
    196c:	e8 1f f8 ff ff       	call   1190 <__monstartup@plt>
    1971:	48 8b 3d 68 26 00 00 	mov    0x2668(%rip),%rdi        # 3fe0 <_mcleanup@GLIBC_2.2.5>
    1978:	48 83 c4 08          	add    $0x8,%rsp
    197c:	e9 6f 03 00 00       	jmp    1cf0 <atexit>
    1981:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    198b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000001990 <_dl_relocate_static_pie>:
    1990:	f3 0f 1e fa          	endbr64
    1994:	c3                   	ret
    1995:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    199f:	90                   	nop

00000000000019a0 <deregister_tm_clones>:
    19a0:	48 8d 3d 69 26 00 00 	lea    0x2669(%rip),%rdi        # 4010 <__TMC_END__>
    19a7:	48 8d 05 62 26 00 00 	lea    0x2662(%rip),%rax        # 4010 <__TMC_END__>
    19ae:	48 39 f8             	cmp    %rdi,%rax
    19b1:	74 15                	je     19c8 <deregister_tm_clones+0x28>
    19b3:	48 8b 05 1e 26 00 00 	mov    0x261e(%rip),%rax        # 3fd8 <_ITM_deregisterTMCloneTable@Base>
    19ba:	48 85 c0             	test   %rax,%rax
    19bd:	74 09                	je     19c8 <deregister_tm_clones+0x28>
    19bf:	ff e0                	jmp    *%rax
    19c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    19c8:	c3                   	ret
    19c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000019d0 <register_tm_clones>:
    19d0:	48 8d 3d 39 26 00 00 	lea    0x2639(%rip),%rdi        # 4010 <__TMC_END__>
    19d7:	48 8d 35 32 26 00 00 	lea    0x2632(%rip),%rsi        # 4010 <__TMC_END__>
    19de:	48 29 fe             	sub    %rdi,%rsi
    19e1:	48 89 f0             	mov    %rsi,%rax
    19e4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    19e8:	48 c1 f8 03          	sar    $0x3,%rax
    19ec:	48 01 c6             	add    %rax,%rsi
    19ef:	48 d1 fe             	sar    %rsi
    19f2:	74 14                	je     1a08 <register_tm_clones+0x38>
    19f4:	48 8b 05 f5 25 00 00 	mov    0x25f5(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    19fb:	48 85 c0             	test   %rax,%rax
    19fe:	74 08                	je     1a08 <register_tm_clones+0x38>
    1a00:	ff e0                	jmp    *%rax
    1a02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1a08:	c3                   	ret
    1a09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001a10 <__do_global_dtors_aux>:
    1a10:	f3 0f 1e fa          	endbr64
    1a14:	80 3d f9 25 00 00 00 	cmpb   $0x0,0x25f9(%rip)        # 4014 <completed.0>
    1a1b:	75 2b                	jne    1a48 <__do_global_dtors_aux+0x38>
    1a1d:	55                   	push   %rbp
    1a1e:	48 83 3d d2 25 00 00 00 	cmpq   $0x0,0x25d2(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1a26:	48 89 e5             	mov    %rsp,%rbp
    1a29:	74 0c                	je     1a37 <__do_global_dtors_aux+0x27>
    1a2b:	48 8b 3d d6 25 00 00 	mov    0x25d6(%rip),%rdi        # 4008 <__dso_handle>
    1a32:	e8 d9 f6 ff ff       	call   1110 <__cxa_finalize@plt>
    1a37:	e8 64 ff ff ff       	call   19a0 <deregister_tm_clones>
    1a3c:	c6 05 d1 25 00 00 01 	movb   $0x1,0x25d1(%rip)        # 4014 <completed.0>
    1a43:	5d                   	pop    %rbp
    1a44:	c3                   	ret
    1a45:	0f 1f 00             	nopl   (%rax)
    1a48:	c3                   	ret
    1a49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001a50 <frame_dummy>:
    1a50:	f3 0f 1e fa          	endbr64
    1a54:	e9 77 ff ff ff       	jmp    19d0 <register_tm_clones>
    1a59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001a60 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    1a60:	f3 0f 1e fa          	endbr64
    1a64:	55                   	push   %rbp
    1a65:	48 89 e5             	mov    %rsp,%rbp
    1a68:	41 57                	push   %r15
    1a6a:	41 56                	push   %r14
    1a6c:	41 55                	push   %r13
    1a6e:	41 54                	push   %r12
    1a70:	53                   	push   %rbx
    1a71:	48 83 ec 18          	sub    $0x18,%rsp
    1a75:	ff 15 6d 25 00 00    	call   *0x256d(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
  if (data->mode == WRITER) {
    1a7b:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
void * disruptor_thread(void * arg) {
    1a81:	48 89 fb             	mov    %rdi,%rbx
  if (data->mode == WRITER) {
    1a84:	85 c0                	test   %eax,%eax
    1a86:	0f 85 39 01 00 00    	jne    1bc5 <disruptor_thread+0x165>
    struct Thread *me = data->sender;
    1a8c:	4c 8b 67 08          	mov    0x8(%rdi),%r12
    while (data->running == 1) {
    1a90:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    1a96:	83 f8 01             	cmp    $0x1,%eax
    1a99:	0f 85 15 01 00 00    	jne    1bb4 <disruptor_thread+0x154>
      asm volatile ("sfence" ::: "memory");
    1a9f:	0f ae f8             	sfence
      long pos = (((__atomic_load_n(&me->realend, __ATOMIC_SEQ_CST) & END_MASK) >> 32) + 1) % data->size;
    1aa2:	49 8d b4 24 80 01 00 00 	lea    0x180(%r12),%rsi
    1aaa:	49 8b 84 24 80 01 00 00 	mov    0x180(%r12),%rax
    1ab2:	48 c1 f8 20          	sar    $0x20,%rax
    1ab6:	25 ff ff ff 0f       	and    $0xfffffff,%eax
    1abb:	48 83 c0 01          	add    $0x1,%rax
    1abf:	48 99                	cqto
      for (int x  = 0 ; x < data->other_count; x++) {
    1ac1:	8b 8b 08 02 00 00    	mov    0x208(%rbx),%ecx
      long pos = (((__atomic_load_n(&me->realend, __ATOMIC_SEQ_CST) & END_MASK) >> 32) + 1) % data->size;
    1ac7:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
      for (int x  = 0 ; x < data->other_count; x++) {
    1ace:	85 c9                	test   %ecx,%ecx
    1ad0:	7e 29                	jle    1afb <disruptor_thread+0x9b>
    1ad2:	31 c9                	xor    %ecx,%ecx
    1ad4:	0f 1f 40 00          	nopl   0x0(%rax)
        if (pos == __atomic_load_n(&data->readers[x]->start, __ATOMIC_SEQ_CST)) {
    1ad8:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    1adf:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    1ae3:	48 63 80 80 00 00 00 	movslq 0x80(%rax),%rax
    1aea:	48 39 d0             	cmp    %rdx,%rax
    1aed:	74 a1                	je     1a90 <disruptor_thread+0x30>
      for (int x  = 0 ; x < data->other_count; x++) {
    1aef:	48 83 c1 01          	add    $0x1,%rcx
    1af3:	39 8b 08 02 00 00    	cmp    %ecx,0x208(%rbx)
    1af9:	7f dd                	jg     1ad8 <disruptor_thread+0x78>
            long original = __atomic_load_n(&me->realend, __ATOMIC_SEQ_CST);
    1afb:	4d 8b 84 24 80 01 00 00 	mov    0x180(%r12),%r8
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1b03:	4c 89 c0             	mov    %r8,%rax
    1b06:	48 c1 f8 20          	sar    $0x20,%rax
    1b0a:	25 ff ff ff 0f       	and    $0xfffffff,%eax
    1b0f:	48 83 c0 01          	add    $0x1,%rax
    1b13:	48 99                	cqto
              long new = (data->thread_tag) | (changed << 32);
    1b15:	4c 63 93 14 02 00 00 	movslq 0x214(%rbx),%r10
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1b1c:	49 f7 bc 24 90 01 00 00 	idivq  0x190(%r12)
              for (int x = 0 ; x < data->other_count; x++) {
    1b24:	8b 83 08 02 00 00    	mov    0x208(%rbx),%eax
              changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1b2a:	49 89 d1             	mov    %rdx,%r9
              for (int x = 0 ; x < data->other_count; x++) {
    1b2d:	85 c0                	test   %eax,%eax
    1b2f:	7e 2e                	jle    1b5f <disruptor_thread+0xff>
                __atomic_store_n(&me->data[changed].complete[x], 0, __ATOMIC_SEQ_CST);
    1b31:	49 89 d5             	mov    %rdx,%r13
    1b34:	31 c9                	xor    %ecx,%ecx
    1b36:	45 31 db             	xor    %r11d,%r11d
    1b39:	49 c1 e5 09          	shl    $0x9,%r13
    1b3d:	0f 1f 00             	nopl   (%rax)
    1b40:	49 8b 44 24 18       	mov    0x18(%r12),%rax
    1b45:	4a 8b bc 28 00 01 00 00 	mov    0x100(%rax,%r13,1),%rdi
    1b4d:	44 89 d8             	mov    %r11d,%eax
    1b50:	87 04 8f             	xchg   %eax,(%rdi,%rcx,4)
              for (int x = 0 ; x < data->other_count; x++) {
    1b53:	48 83 c1 01          	add    $0x1,%rcx
    1b57:	39 8b 08 02 00 00    	cmp    %ecx,0x208(%rbx)
    1b5d:	7f e1                	jg     1b40 <disruptor_thread+0xe0>
              long new = (data->thread_tag) | (changed << 32);
    1b5f:	48 c1 e2 20          	shl    $0x20,%rdx
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED))) {
    1b63:	4c 89 c0             	mov    %r8,%rax
              long new = (data->thread_tag) | (changed << 32);
    1b66:	48 89 d1             	mov    %rdx,%rcx
    1b69:	4c 09 d1             	or     %r10,%rcx
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED))) {
    1b6c:	f0 48 0f b1 0e       	lock cmpxchg %rcx,(%rsi)
    1b71:	0f 85 fe 00 00 00    	jne    1c75 <disruptor_thread+0x215>
                clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1b77:	49 8b 74 24 18       	mov    0x18(%r12),%rsi
    1b7c:	49 c1 e1 09          	shl    $0x9,%r9
    1b80:	bf 04 00 00 00       	mov    $0x4,%edi
    1b85:	4d 89 cd             	mov    %r9,%r13
    1b88:	4c 01 ce             	add    %r9,%rsi
    1b8b:	e8 b0 f5 ff ff       	call   1140 <clock_gettime@plt>
                __atomic_store_n(&me->data[changed].written, me->other_count, __ATOMIC_SEQ_CST);
    1b90:	49 8b 54 24 18       	mov    0x18(%r12),%rdx
    1b95:	41 8b 84 24 08 02 00 00 	mov    0x208(%r12),%eax
    1b9d:	42 87 84 2a 80 01 00 00 	xchg   %eax,0x180(%rdx,%r13,1)
    while (data->running == 1) {
    1ba5:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    1bab:	83 f8 01             	cmp    $0x1,%eax
    1bae:	0f 84 eb fe ff ff    	je     1a9f <disruptor_thread+0x3f>
}
    1bb4:	48 83 c4 18          	add    $0x18,%rsp
    1bb8:	31 c0                	xor    %eax,%eax
    1bba:	5b                   	pop    %rbx
    1bbb:	41 5c                	pop    %r12
    1bbd:	41 5d                	pop    %r13
    1bbf:	41 5e                	pop    %r14
    1bc1:	41 5f                	pop    %r15
    1bc3:	5d                   	pop    %rbp
    1bc4:	c3                   	ret
  } else if (data->mode == READER) {
    1bc5:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
    1bcb:	83 f8 01             	cmp    $0x1,%eax
    1bce:	75 e4                	jne    1bb4 <disruptor_thread+0x154>
    struct Thread *sender = data->sender;
    1bd0:	4c 8b 6f 08          	mov    0x8(%rdi),%r13
    struct Snapshot * rdata = sender->data;
    1bd4:	4d 8b 75 18          	mov    0x18(%r13),%r14
    while (data->running == 1) {
    1bd8:	eb 22                	jmp    1bfc <disruptor_thread+0x19c>
    1bda:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      int pos = ((__atomic_load_n(&sender->realend, __ATOMIC_SEQ_CST) & END_MASK) >> 32);
    1be0:	49 8b 85 80 01 00 00 	mov    0x180(%r13),%rax
    1be7:	48 c1 f8 20          	sar    $0x20,%rax
    1beb:	25 ff ff ff 0f       	and    $0xfffffff,%eax
      if (pos == data->start) {
    1bf0:	44 8b a3 80 00 00 00 	mov    0x80(%rbx),%r12d
    1bf7:	41 39 c4             	cmp    %eax,%r12d
    1bfa:	75 0f                	jne    1c0b <disruptor_thread+0x1ab>
    while (data->running == 1) {
    1bfc:	44 8b bb 98 01 00 00 	mov    0x198(%rbx),%r15d
    1c03:	41 83 ff 01          	cmp    $0x1,%r15d
    1c07:	74 d7                	je     1be0 <disruptor_thread+0x180>
    1c09:	eb a9                	jmp    1bb4 <disruptor_thread+0x154>
          if (__atomic_load_n(&rdata[changed].written, __ATOMIC_SEQ_CST) > 0) {
    1c0b:	49 63 cc             	movslq %r12d,%rcx
    1c0e:	48 c1 e1 09          	shl    $0x9,%rcx
    1c12:	4c 01 f1             	add    %r14,%rcx
    1c15:	8b 81 80 01 00 00    	mov    0x180(%rcx),%eax
    1c1b:	85 c0                	test   %eax,%eax
    1c1d:	7e dd                	jle    1bfc <disruptor_thread+0x19c>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1c1f:	48 63 b3 0c 02 00 00 	movslq 0x20c(%rbx),%rsi
    1c26:	bf 04 00 00 00       	mov    $0x4,%edi
    1c2b:	48 89 4d c8          	mov    %rcx,-0x38(%rbp)
    1c2f:	48 c1 e6 04          	shl    $0x4,%rsi
    1c33:	48 03 b1 80 00 00 00 	add    0x80(%rcx),%rsi
    1c3a:	e8 01 f5 ff ff       	call   1140 <clock_gettime@plt>
              __atomic_store_n(&rdata[changed].complete[data->reader_index], 1, __ATOMIC_SEQ_CST);
    1c3f:	48 8b 4d c8          	mov    -0x38(%rbp),%rcx
    1c43:	48 63 93 0c 02 00 00 	movslq 0x20c(%rbx),%rdx
    1c4a:	48 8b 81 00 01 00 00 	mov    0x100(%rcx),%rax
    1c51:	44 87 3c 90          	xchg   %r15d,(%rax,%rdx,4)
              __atomic_store_n(&data->start, (changed + 1) % data->size, __ATOMIC_SEQ_CST);
    1c55:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    1c5a:	48 98                	cltq
    1c5c:	48 99                	cqto
    1c5e:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
    1c65:	87 93 80 00 00 00    	xchg   %edx,0x80(%rbx)
              __atomic_sub_fetch(&rdata[changed].written, 1, __ATOMIC_SEQ_CST);
    1c6b:	f0 83 a9 80 01 00 00 01 	lock subl $0x1,0x180(%rcx)
    1c73:	eb 87                	jmp    1bfc <disruptor_thread+0x19c>
                original = __atomic_load_n(&me->realend, __ATOMIC_SEQ_CST);
    1c75:	48 8b 0e             	mov    (%rsi),%rcx
                changed = (((original & END_MASK) >> 32) + 1) % me->size;
    1c78:	48 89 c8             	mov    %rcx,%rax
    1c7b:	48 c1 f8 20          	sar    $0x20,%rax
    1c7f:	25 ff ff ff 0f       	and    $0xfffffff,%eax
    1c84:	48 83 c0 01          	add    $0x1,%rax
    1c88:	48 99                	cqto
    1c8a:	49 f7 bc 24 90 01 00 00 	idivq  0x190(%r12)
    1c92:	49 89 d1             	mov    %rdx,%r9
                new = (data->thread_tag) | (changed << 32);
    1c95:	48 63 93 14 02 00 00 	movslq 0x214(%rbx),%rdx
    1c9c:	4c 89 c8             	mov    %r9,%rax
    1c9f:	48 c1 e0 20          	shl    $0x20,%rax
    1ca3:	48 09 c2             	or     %rax,%rdx
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED))) {
    1ca6:	48 89 c8             	mov    %rcx,%rax
    1ca9:	f0 48 0f b1 16       	lock cmpxchg %rdx,(%rsi)
    1cae:	0f 84 c3 fe ff ff    	je     1b77 <disruptor_thread+0x117>
    1cb4:	eb bf                	jmp    1c75 <disruptor_thread+0x215>
    1cb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001cc0 <min>:
int min(long a, long b) {
    1cc0:	f3 0f 1e fa          	endbr64
    1cc4:	55                   	push   %rbp
    1cc5:	48 89 e5             	mov    %rsp,%rbp
    1cc8:	ff 15 1a 23 00 00    	call   *0x231a(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
  if (a < b) return a;
    1cce:	48 39 f7             	cmp    %rsi,%rdi
    1cd1:	7c 02                	jl     1cd5 <min+0x15>
  if (b < a) return b;
    1cd3:	7f 0b                	jg     1ce0 <min+0x20>
  if (a < b) return a;
    1cd5:	89 f8                	mov    %edi,%eax
}
    1cd7:	5d                   	pop    %rbp
    1cd8:	c3                   	ret
    1cd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (b < a) return b;
    1ce0:	89 f0                	mov    %esi,%eax
}
    1ce2:	5d                   	pop    %rbp
    1ce3:	c3                   	ret
    1ce4:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    1cee:	66 90                	xchg   %ax,%ax

0000000000001cf0 <atexit>:
    1cf0:	f3 0f 1e fa          	endbr64
    1cf4:	48 8b 15 0d 23 00 00 	mov    0x230d(%rip),%rdx        # 4008 <__dso_handle>
    1cfb:	31 f6                	xor    %esi,%esi
    1cfd:	e9 ce f4 ff ff       	jmp    11d0 <__cxa_atexit@plt>
    1d02:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    1d0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000001d10 <__stack_chk_fail_local>:
    1d10:	f3 0f 1e fa          	endbr64
    1d14:	50                   	push   %rax
    1d15:	58                   	pop    %rax
    1d16:	48 83 ec 08          	sub    $0x8,%rsp
    1d1a:	e8 31 f4 ff ff       	call   1150 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000001d20 <_fini>:
    1d20:	f3 0f 1e fa          	endbr64
    1d24:	48 83 ec 08          	sub    $0x8,%rsp
    1d28:	48 83 c4 08          	add    $0x8,%rsp
    1d2c:	c3                   	ret
