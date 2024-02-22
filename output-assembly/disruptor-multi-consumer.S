
disruptor-multi-consumer:     file format elf64-x86-64


Disassembly of section .init:

0000000000001000 <_init>:
    1000:	f3 0f 1e fa          	endbr64
    1004:	48 83 ec 08          	sub    $0x8,%rsp
    1008:	48 8d 05 01 07 00 00 	lea    0x701(%rip),%rax        # 1710 <__gmon_start__>
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
    1211:	48 83 ec 58          	sub    $0x58,%rsp
    1215:	ff 15 cd 2d 00 00    	call   *0x2dcd(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    121b:	b9 00 80 00 00       	mov    $0x8000,%ecx
    1220:	ba 0f 00 00 00       	mov    $0xf,%edx
    1225:	bf 01 00 00 00       	mov    $0x1,%edi
    122a:	48 8d 35 37 0f 00 00 	lea    0xf37(%rip),%rsi        # 2168 <_IO_stdin_used+0x168>
    1231:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    123a:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    123e:	31 c0                	xor    %eax,%eax
    1240:	e8 5b ff ff ff       	call   11a0 <__printf_chk@plt>
    1245:	ba 01 00 00 00       	mov    $0x1,%edx
    124a:	48 8d 35 0b 0e 00 00 	lea    0xe0b(%rip),%rsi        # 205c <_IO_stdin_used+0x5c>
    1251:	31 c0                	xor    %eax,%eax
    1253:	bf 01 00 00 00       	mov    $0x1,%edi
    1258:	e8 43 ff ff ff       	call   11a0 <__printf_chk@plt>
    125d:	ba 01 00 00 00       	mov    $0x1,%edx
    1262:	48 8d 35 03 0e 00 00 	lea    0xe03(%rip),%rsi        # 206c <_IO_stdin_used+0x6c>
    1269:	31 c0                	xor    %eax,%eax
    126b:	bf 01 00 00 00       	mov    $0x1,%edi
    1270:	e8 2b ff ff ff       	call   11a0 <__printf_chk@plt>
    1275:	ba 01 00 00 00       	mov    $0x1,%edx
    127a:	48 8d 35 fd 0d 00 00 	lea    0xdfd(%rip),%rsi        # 207e <_IO_stdin_used+0x7e>
    1281:	31 c0                	xor    %eax,%eax
    1283:	bf 01 00 00 00       	mov    $0x1,%edi
    1288:	e8 13 ff ff ff       	call   11a0 <__printf_chk@plt>
    128d:	ba 02 00 00 00       	mov    $0x2,%edx
    1292:	48 8d 35 f7 0d 00 00 	lea    0xdf7(%rip),%rsi        # 2090 <_IO_stdin_used+0x90>
    1299:	31 c0                	xor    %eax,%eax
    129b:	bf 01 00 00 00       	mov    $0x1,%edi
    12a0:	e8 fb fe ff ff       	call   11a0 <__printf_chk@plt>
  int group_size = writers_count + other_count;
  printf("Readers count %d\n", other_count);
  printf("Writers count %d\n", writers_count);
  int thread_count = groups * (other_count + writers_count);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    12a5:	be 80 02 00 00       	mov    $0x280,%esi
    12aa:	bf 02 00 00 00       	mov    $0x2,%edi
    12af:	e8 cc fe ff ff       	call   1180 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12b4:	be 38 00 00 00       	mov    $0x38,%esi
    12b9:	bf 02 00 00 00       	mov    $0x2,%edi
    12be:	66 48 0f 6e c8       	movq   %rax,%xmm1
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    12c3:	49 89 c5             	mov    %rax,%r13
    12c6:	66 0f 6c c9          	punpcklqdq %xmm1,%xmm1
    12ca:	0f 29 4d 80          	movaps %xmm1,-0x80(%rbp)
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12ce:	e8 ad fe ff ff       	call   1180 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12d3:	be 08 00 00 00       	mov    $0x8,%esi
    12d8:	bf 02 00 00 00       	mov    $0x2,%edi
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12dd:	49 89 c7             	mov    %rax,%r15
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12e0:	e8 9b fe ff ff       	call   1180 <calloc@plt>
    12e5:	31 d2                	xor    %edx,%edx
    12e7:	bf 01 00 00 00       	mov    $0x1,%edi
    12ec:	48 8d 35 b4 0d 00 00 	lea    0xdb4(%rip),%rsi        # 20a7 <_IO_stdin_used+0xa7>
    12f3:	49 89 c6             	mov    %rax,%r14
    12f6:	31 c0                	xor    %eax,%eax
    12f8:	e8 a3 fe ff ff       	call   11a0 <__printf_chk@plt>
    12fd:	48 8d 3d ae 0d 00 00 	lea    0xdae(%rip),%rdi        # 20b2 <_IO_stdin_used+0xb2>
    1304:	e8 27 fe ff ff       	call   1130 <puts@plt>
    int receiver2 = receiver + 1; 
    int seq[] = {1, 2, 5};
    int tag_index[] = {1, 5, 7};
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
      printf("CREATE SENDER THREAD\n");
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1309:	be 80 00 00 00       	mov    $0x80,%esi
    130e:	bf 01 00 00 00       	mov    $0x1,%edi
    1313:	e8 68 fe ff ff       	call   1180 <calloc@plt>
    1318:	31 c9                	xor    %ecx,%ecx
    131a:	31 d2                	xor    %edx,%edx
    131c:	48 8d 35 6d 0e 00 00 	lea    0xe6d(%rip),%rsi        # 2190 <_IO_stdin_used+0x190>
      CPU_ZERO(sendercpu);
      CPU_SET(curcpu, sendercpu);
    1323:	48 83 08 01          	orq    $0x1,(%rax)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    1327:	48 89 c3             	mov    %rax,%rbx
    132a:	bf 01 00 00 00       	mov    $0x1,%edi
    132f:	31 c0                	xor    %eax,%eax
    1331:	e8 6a fe ff ff       	call   11a0 <__printf_chk@plt>
      thread_data[n].multiple = seq[sender_index % writers_count];
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].thread_tag = tag_index[sender_index];
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
    1336:	4d 89 6d 08          	mov    %r13,0x8(%r13)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    133a:	be 08 00 00 00       	mov    $0x8,%esi
    133f:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[n].cpu_set = sendercpu;
    1344:	49 89 9d a0 01 00 00 	mov    %rbx,0x1a0(%r13)
      thread_data[n].mode = WRITER;
    134b:	41 c7 85 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%r13)
      thread_data[n].thread_index = n;
    1356:	41 c7 45 00 00 00 00 00 	movl   $0x0,0x0(%r13)
      thread_data[n].multiple = seq[sender_index % writers_count];
    135e:	41 c7 85 10 02 00 00 01 00 00 00 	movl   $0x1,0x210(%r13)
      thread_data[n].running = 1;
    1369:	41 c7 85 98 01 00 00 01 00 00 00 	movl   $0x1,0x198(%r13)
      thread_data[n].size = buffer_size;
    1374:	49 c7 85 90 01 00 00 00 80 00 00 	movq   $0x8000,0x190(%r13)
      thread_data[n].thread_tag = tag_index[sender_index];
    137f:	41 c7 85 14 02 00 00 01 00 00 00 	movl   $0x1,0x214(%r13)
      thread_data[n].end = 0;
    138a:	41 c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r13)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1395:	e8 e6 fd ff ff       	call   1180 <calloc@plt>
      if (n == sender) {
        thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    139a:	be 00 02 00 00       	mov    $0x200,%esi
    139f:	bf 00 80 00 00       	mov    $0x8000,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    13a4:	49 89 85 00 02 00 00 	mov    %rax,0x200(%r13)
        thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    13ab:	e8 d0 fd ff ff       	call   1180 <calloc@plt>
    13b0:	49 89 45 18          	mov    %rax,0x18(%r13)
    13b4:	49 89 c4             	mov    %rax,%r12
        for (int k = 0 ; k < buffer_size ; k++) {
    13b7:	48 8d 98 80 00 00 00 	lea    0x80(%rax),%rbx
    13be:	49 81 c4 80 00 00 01 	add    $0x1000080,%r12
    13c5:	0f 1f 00             	nopl   (%rax)
          thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13c8:	be 04 00 00 00       	mov    $0x4,%esi
    13cd:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int k = 0 ; k < buffer_size ; k++) {
    13d2:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
          thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13d9:	e8 a2 fd ff ff       	call   1180 <calloc@plt>
          thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    13de:	be 10 00 00 00       	mov    $0x10,%esi
    13e3:	bf 01 00 00 00       	mov    $0x1,%edi
          thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13e8:	48 89 83 80 fe ff ff 	mov    %rax,-0x180(%rbx)
          thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    13ef:	e8 8c fd ff ff       	call   1180 <calloc@plt>
          thread_data[n].data[k].written = 0;
    13f4:	c7 83 00 ff ff ff 00 00 00 00 	movl   $0x0,-0x100(%rbx)
          thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    13fe:	48 89 83 00 fe ff ff 	mov    %rax,-0x200(%rbx)
        for (int k = 0 ; k < buffer_size ; k++) {
    1405:	4c 39 e3             	cmp    %r12,%rbx
    1408:	75 be                	jne    13c8 <main+0x1c8>
    140a:	31 d2                	xor    %edx,%edx
    140c:	48 8d 35 b4 0c 00 00 	lea    0xcb4(%rip),%rsi        # 20c7 <_IO_stdin_used+0xc7>
    1413:	bf 01 00 00 00       	mov    $0x1,%edi
    1418:	31 c0                	xor    %eax,%eax
        }
      }
      thread_data[n].other_count = other_count;
    141a:	41 c7 85 08 02 00 00 01 00 00 00 	movl   $0x1,0x208(%r13)
    }

    printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      thread_data[j].thread_index = j;
    1425:	4d 8d a5 80 02 00 00 	lea    0x280(%r13),%r12
    142c:	e8 6f fd ff ff       	call   11a0 <__printf_chk@plt>
      thread_data[j].reader_index = receiver_index;
      thread_data[j].multiple = receiver_index % other_count;
      thread_data[j].other_count = other_count;
     
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1431:	be 80 00 00 00       	mov    $0x80,%esi
    1436:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].thread_index = j;
    143b:	41 c7 85 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%r13)
      thread_data[j].multiple = receiver_index % other_count;
    1446:	41 c7 85 90 04 00 00 00 00 00 00 	movl   $0x0,0x490(%r13)
      thread_data[j].other_count = other_count;
    1451:	49 c7 85 88 04 00 00 01 00 00 00 	movq   $0x1,0x488(%r13)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    145c:	e8 1f fd ff ff       	call   1180 <calloc@plt>
    1461:	b9 02 00 00 00       	mov    $0x2,%ecx
    1466:	ba 01 00 00 00       	mov    $0x1,%edx
    146b:	48 8d 35 3e 0d 00 00 	lea    0xd3e(%rip),%rsi        # 21b0 <_IO_stdin_used+0x1b0>
      CPU_ZERO(receivercpu);
      CPU_SET(curcpu, receivercpu);
    1472:	48 83 08 04          	orq    $0x4,(%rax)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1476:	48 89 c3             	mov    %rax,%rbx
    1479:	bf 01 00 00 00       	mov    $0x1,%edi
    147e:	31 c0                	xor    %eax,%eax
    1480:	e8 1b fd ff ff       	call   11a0 <__printf_chk@plt>
      } */
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    1485:	49 8b 85 00 02 00 00 	mov    0x200(%r13),%rax
    148c:	31 c9                	xor    %ecx,%ecx
    148e:	31 d2                	xor    %edx,%edx
      thread_data[j].running = 1;
    1490:	41 c7 85 18 04 00 00 01 00 00 00 	movl   $0x1,0x418(%r13)
      thread_data[j].sender = &thread_data[sender];
    149b:	66 0f 6f 55 80       	movdqa -0x80(%rbp),%xmm2
    14a0:	48 8d 35 31 0d 00 00 	lea    0xd31(%rip),%rsi        # 21d8 <_IO_stdin_used+0x1d8>
    14a7:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].readers = thread_data[sender].readers;
    14ac:	49 89 85 80 04 00 00 	mov    %rax,0x480(%r13)
    14b3:	31 c0                	xor    %eax,%eax
      thread_data[j].cpu_set = receivercpu;
    14b5:	49 89 9d 20 04 00 00 	mov    %rbx,0x420(%r13)
      thread_data[j].mode = READER;
    14bc:	41 c7 85 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%r13)
      thread_data[j].size = buffer_size;
    14c7:	49 c7 85 10 04 00 00 00 80 00 00 	movq   $0x8000,0x410(%r13)
      thread_data[j].start = 0;
    14d2:	41 c7 85 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%r13)
      thread_data[j].other_count = other_count;
    14dd:	41 c7 85 88 04 00 00 01 00 00 00 	movl   $0x1,0x488(%r13)
      thread_data[j].sender = &thread_data[sender];
    14e8:	41 0f 11 95 88 02 00 00 	movups %xmm2,0x288(%r13)
    14f0:	e8 ab fc ff ff       	call   11a0 <__printf_chk@plt>
      // printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        printf("assigned reader %d to sender %d\n", receiver_index, n);
        thread_data[n].readers[receiver_index] = &thread_data[j];
    14f5:	49 8b 85 00 02 00 00 	mov    0x200(%r13),%rax
    14fc:	4c 89 20             	mov    %r12,(%rax)
      }
    }
    curcpu = 0;
    // printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    14ff:	0f ae f0             	mfence
    1502:	bf 01 00 00 00       	mov    $0x1,%edi
    1507:	31 c0                	xor    %eax,%eax
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    1509:	49 8d 5f 38          	lea    0x38(%r15),%rbx
    150d:	ba 01 00 00 00       	mov    $0x1,%edx
    1512:	48 8d 35 c3 0b 00 00 	lea    0xbc3(%rip),%rsi        # 20dc <_IO_stdin_used+0xdc>
  param.sched_priority = 0;
    1519:	c7 45 9c 00 00 00 00 	movl   $0x0,-0x64(%rbp)
    1520:	e8 7b fc ff ff       	call   11a0 <__printf_chk@plt>
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    1525:	31 f6                	xor    %esi,%esi
    1527:	48 89 df             	mov    %rbx,%rdi
    152a:	e8 41 fc ff ff       	call   1170 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    152f:	85 c0                	test   %eax,%eax
    1531:	0f 85 73 01 00 00    	jne    16aa <main+0x4aa>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    1537:	48 8d 75 9c          	lea    -0x64(%rbp),%rsi
    153b:	48 89 df             	mov    %rbx,%rdi
    153e:	e8 7d fc ff ff       	call   11c0 <pthread_attr_setschedparam@plt>
      if (ret) {
    1543:	85 c0                	test   %eax,%eax
    1545:	0f 85 7a 01 00 00    	jne    16c5 <main+0x4c5>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    154b:	4c 89 e1             	mov    %r12,%rcx
    154e:	4c 8d 25 db 02 00 00 	lea    0x2db(%rip),%r12        # 1830 <disruptor_thread>
    1555:	49 8d 7e 08          	lea    0x8(%r14),%rdi
    1559:	48 89 de             	mov    %rbx,%rsi
    155c:	4c 89 e2             	mov    %r12,%rdx
    155f:	e8 4c fc ff ff       	call   11b0 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    1564:	49 8b 7e 08          	mov    0x8(%r14),%rdi
    1568:	be 08 00 00 00       	mov    $0x8,%esi
    156d:	49 8b 95 20 04 00 00 	mov    0x420(%r13),%rdx
    1574:	e8 a7 fb ff ff       	call   1120 <pthread_setaffinity_np@plt>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    1579:	31 f6                	xor    %esi,%esi
    157b:	4c 89 ff             	mov    %r15,%rdi
    157e:	e8 ed fb ff ff       	call   1170 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    1583:	85 c0                	test   %eax,%eax
    1585:	0f 85 1f 01 00 00    	jne    16aa <main+0x4aa>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    158b:	48 8d 75 98          	lea    -0x68(%rbp),%rsi
    158f:	4c 89 ff             	mov    %r15,%rdi
      param2.sched_priority = 0;
    1592:	c7 45 98 00 00 00 00 	movl   $0x0,-0x68(%rbp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1599:	e8 22 fc ff ff       	call   11c0 <pthread_attr_setschedparam@plt>
      if (ret) {
    159e:	85 c0                	test   %eax,%eax
    15a0:	0f 85 1f 01 00 00    	jne    16c5 <main+0x4c5>
    15a6:	31 d2                	xor    %edx,%edx
    15a8:	48 8d 35 85 0b 00 00 	lea    0xb85(%rip),%rsi        # 2134 <_IO_stdin_used+0x134>
    15af:	bf 01 00 00 00       	mov    $0x1,%edi
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    15b4:	31 db                	xor    %ebx,%ebx
    15b6:	e8 e5 fb ff ff       	call   11a0 <__printf_chk@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    15bb:	4c 89 e9             	mov    %r13,%rcx
    15be:	4c 89 e2             	mov    %r12,%rdx
    15c1:	4c 89 fe             	mov    %r15,%rsi
    15c4:	4c 89 f7             	mov    %r14,%rdi
    15c7:	4c 8d 25 82 0b 00 00 	lea    0xb82(%rip),%r12        # 2150 <_IO_stdin_used+0x150>
    15ce:	e8 dd fb ff ff       	call   11b0 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    15d3:	49 8b 95 a0 01 00 00 	mov    0x1a0(%r13),%rdx
    15da:	49 8b 3e             	mov    (%r14),%rdi
    15dd:	be 08 00 00 00       	mov    $0x8,%esi
    15e2:	e8 39 fb ff ff       	call   1120 <pthread_setaffinity_np@plt>
  nanosleep(&preempt , &rem2);
    15e7:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    15eb:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
  struct timespec preempt = {
    15ef:	66 0f 6f 05 09 0c 00 00 	movdqa 0xc09(%rip),%xmm0        # 2200 <_IO_stdin_used+0x200>
    15f7:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
  nanosleep(&preempt , &rem2);
    15fb:	e8 60 fb ff ff       	call   1160 <nanosleep@plt>
      pthread_join(thread[n], res1);
    1600:	49 8b 3e             	mov    (%r14),%rdi
    1603:	31 f6                	xor    %esi,%esi
    thread_data[sender].running = 0;
    1605:	41 c7 85 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r13)
      thread_data[j].running = 0;
    1610:	41 c7 85 18 04 00 00 00 00 00 00 	movl   $0x0,0x418(%r13)
      thread_data[n].running = 0;
    161b:	41 c7 85 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r13)
      pthread_join(thread[n], res1);
    1626:	e8 c5 fb ff ff       	call   11f0 <pthread_join@plt>
      pthread_join(thread[j], res2);
    162b:	49 8b 7e 08          	mov    0x8(%r14),%rdi
    162f:	31 f6                	xor    %esi,%esi
    1631:	e8 ba fb ff ff       	call   11f0 <pthread_join@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    // printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    1636:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      int compcount = 0;
      for (int n = 0 ; n < other_count ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    1640:	49 8b 45 18          	mov    0x18(%r13),%rax
    1644:	48 8b 94 18 00 01 00 00 	mov    0x100(%rax,%rbx,1),%rdx
    164c:	83 3a 01             	cmpl   $0x1,(%rdx)
    164f:	75 29                	jne    167a <main+0x47a>
      }
      // printf("%d\n", compcount);
      if (compcount == other_count) {
      for (int n = 0 ; n < other_count ; n++) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
    1651:	48 01 d8             	add    %rbx,%rax
    1654:	4c 89 e6             	mov    %r12,%rsi
    1657:	bf 01 00 00 00       	mov    $0x1,%edi
          struct timespec end = thread_data[sender].data[y].end[n];
    165c:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    1663:	4c 8b 42 08          	mov    0x8(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    1667:	48 8b 0a             	mov    (%rdx),%rcx
    166a:	31 d2                	xor    %edx,%edx
    166c:	48 2b 08             	sub    (%rax),%rcx
    166f:	4c 2b 40 08          	sub    0x8(%rax),%r8
    1673:	31 c0                	xor    %eax,%eax
    1675:	e8 26 fb ff ff       	call   11a0 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    167a:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
    1681:	48 81 fb 00 00 00 01 	cmp    $0x1000000,%rbx
    1688:	75 b6                	jne    1640 <main+0x440>
    }
    // printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    168a:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    168e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1697:	75 27                	jne    16c0 <main+0x4c0>
    1699:	48 83 c4 58          	add    $0x58,%rsp
    169d:	31 c0                	xor    %eax,%eax
    169f:	5b                   	pop    %rbx
    16a0:	41 5c                	pop    %r12
    16a2:	41 5d                	pop    %r13
    16a4:	41 5e                	pop    %r14
    16a6:	41 5f                	pop    %r15
    16a8:	5d                   	pop    %rbp
    16a9:	c3                   	ret
    16aa:	48 8d 3d 48 0a 00 00 	lea    0xa48(%rip),%rdi        # 20f9 <_IO_stdin_used+0xf9>
    16b1:	e8 7a fa ff ff       	call   1130 <puts@plt>
               exit(1);
    16b6:	bf 01 00 00 00       	mov    $0x1,%edi
    16bb:	e8 20 fb ff ff       	call   11e0 <exit@plt>
}
    16c0:	e8 8b fa ff ff       	call   1150 <__stack_chk_fail@plt>
    16c5:	48 8d 3d 4b 0a 00 00 	lea    0xa4b(%rip),%rdi        # 2117 <_IO_stdin_used+0x117>
    16cc:	e8 5f fa ff ff       	call   1130 <puts@plt>
              exit(1);
    16d1:	bf 01 00 00 00       	mov    $0x1,%edi
    16d6:	e8 05 fb ff ff       	call   11e0 <exit@plt>
    16db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000016e0 <_start>:
    16e0:	f3 0f 1e fa          	endbr64
    16e4:	31 ed                	xor    %ebp,%ebp
    16e6:	49 89 d1             	mov    %rdx,%r9
    16e9:	5e                   	pop    %rsi
    16ea:	48 89 e2             	mov    %rsp,%rdx
    16ed:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    16f1:	50                   	push   %rax
    16f2:	54                   	push   %rsp
    16f3:	45 31 c0             	xor    %r8d,%r8d
    16f6:	31 c9                	xor    %ecx,%ecx
    16f8:	48 8d 3d 01 fb ff ff 	lea    -0x4ff(%rip),%rdi        # 1200 <main>
    16ff:	ff 15 cb 28 00 00    	call   *0x28cb(%rip)        # 3fd0 <__libc_start_main@GLIBC_2.34>
    1705:	f4                   	hlt
    1706:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001710 <__gmon_start__>:
    1710:	f3 0f 1e fa          	endbr64
    1714:	8b 05 f6 28 00 00    	mov    0x28f6(%rip),%eax        # 4010 <__TMC_END__>
    171a:	85 c0                	test   %eax,%eax
    171c:	74 02                	je     1720 <__gmon_start__+0x10>
    171e:	c3                   	ret
    171f:	90                   	nop
    1720:	48 83 ec 08          	sub    $0x8,%rsp
    1724:	48 8d 35 62 04 00 00 	lea    0x462(%rip),%rsi        # 1b8d <etext>
    172b:	48 8d 3d ce e8 ff ff 	lea    -0x1732(%rip),%rdi        # 0 <__executable_start>
    1732:	c7 05 d4 28 00 00 01 00 00 00 	movl   $0x1,0x28d4(%rip)        # 4010 <__TMC_END__>
    173c:	e8 4f fa ff ff       	call   1190 <__monstartup@plt>
    1741:	48 8b 3d 98 28 00 00 	mov    0x2898(%rip),%rdi        # 3fe0 <_mcleanup@GLIBC_2.2.5>
    1748:	48 83 c4 08          	add    $0x8,%rsp
    174c:	e9 ff 03 00 00       	jmp    1b50 <atexit>
    1751:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    175b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000001760 <_dl_relocate_static_pie>:
    1760:	f3 0f 1e fa          	endbr64
    1764:	c3                   	ret
    1765:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    176f:	90                   	nop

0000000000001770 <deregister_tm_clones>:
    1770:	48 8d 3d 99 28 00 00 	lea    0x2899(%rip),%rdi        # 4010 <__TMC_END__>
    1777:	48 8d 05 92 28 00 00 	lea    0x2892(%rip),%rax        # 4010 <__TMC_END__>
    177e:	48 39 f8             	cmp    %rdi,%rax
    1781:	74 15                	je     1798 <deregister_tm_clones+0x28>
    1783:	48 8b 05 4e 28 00 00 	mov    0x284e(%rip),%rax        # 3fd8 <_ITM_deregisterTMCloneTable@Base>
    178a:	48 85 c0             	test   %rax,%rax
    178d:	74 09                	je     1798 <deregister_tm_clones+0x28>
    178f:	ff e0                	jmp    *%rax
    1791:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1798:	c3                   	ret
    1799:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017a0 <register_tm_clones>:
    17a0:	48 8d 3d 69 28 00 00 	lea    0x2869(%rip),%rdi        # 4010 <__TMC_END__>
    17a7:	48 8d 35 62 28 00 00 	lea    0x2862(%rip),%rsi        # 4010 <__TMC_END__>
    17ae:	48 29 fe             	sub    %rdi,%rsi
    17b1:	48 89 f0             	mov    %rsi,%rax
    17b4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    17b8:	48 c1 f8 03          	sar    $0x3,%rax
    17bc:	48 01 c6             	add    %rax,%rsi
    17bf:	48 d1 fe             	sar    %rsi
    17c2:	74 14                	je     17d8 <register_tm_clones+0x38>
    17c4:	48 8b 05 25 28 00 00 	mov    0x2825(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    17cb:	48 85 c0             	test   %rax,%rax
    17ce:	74 08                	je     17d8 <register_tm_clones+0x38>
    17d0:	ff e0                	jmp    *%rax
    17d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    17d8:	c3                   	ret
    17d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017e0 <__do_global_dtors_aux>:
    17e0:	f3 0f 1e fa          	endbr64
    17e4:	80 3d 29 28 00 00 00 	cmpb   $0x0,0x2829(%rip)        # 4014 <completed.0>
    17eb:	75 2b                	jne    1818 <__do_global_dtors_aux+0x38>
    17ed:	55                   	push   %rbp
    17ee:	48 83 3d 02 28 00 00 00 	cmpq   $0x0,0x2802(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    17f6:	48 89 e5             	mov    %rsp,%rbp
    17f9:	74 0c                	je     1807 <__do_global_dtors_aux+0x27>
    17fb:	48 8b 3d 06 28 00 00 	mov    0x2806(%rip),%rdi        # 4008 <__dso_handle>
    1802:	e8 09 f9 ff ff       	call   1110 <__cxa_finalize@plt>
    1807:	e8 64 ff ff ff       	call   1770 <deregister_tm_clones>
    180c:	c6 05 01 28 00 00 01 	movb   $0x1,0x2801(%rip)        # 4014 <completed.0>
    1813:	5d                   	pop    %rbp
    1814:	c3                   	ret
    1815:	0f 1f 00             	nopl   (%rax)
    1818:	c3                   	ret
    1819:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001820 <frame_dummy>:
    1820:	f3 0f 1e fa          	endbr64
    1824:	e9 77 ff ff ff       	jmp    17a0 <register_tm_clones>
    1829:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001830 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    1830:	f3 0f 1e fa          	endbr64
    1834:	55                   	push   %rbp
    1835:	48 89 e5             	mov    %rsp,%rbp
    1838:	41 57                	push   %r15
    183a:	41 56                	push   %r14
    183c:	41 55                	push   %r13
    183e:	41 54                	push   %r12
    1840:	53                   	push   %rbx
    1841:	48 83 ec 08          	sub    $0x8,%rsp
    1845:	ff 15 9d 27 00 00    	call   *0x279d(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
  if (data->mode == WRITER) {
    184b:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
void * disruptor_thread(void * arg) {
    1851:	48 89 fb             	mov    %rdi,%rbx
  if (data->mode == WRITER) {
    1854:	85 c0                	test   %eax,%eax
    1856:	74 20                	je     1878 <disruptor_thread+0x48>
  } else if (data->mode == READER) {
    1858:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
    185e:	83 f8 01             	cmp    $0x1,%eax
    1861:	0f 84 6a 01 00 00    	je     19d1 <disruptor_thread+0x1a1>
}
    1867:	48 83 c4 08          	add    $0x8,%rsp
    186b:	31 c0                	xor    %eax,%eax
    186d:	5b                   	pop    %rbx
    186e:	41 5c                	pop    %r12
    1870:	41 5d                	pop    %r13
    1872:	41 5e                	pop    %r14
    1874:	41 5f                	pop    %r15
    1876:	5d                   	pop    %rbp
    1877:	c3                   	ret
    1878:	8b 17                	mov    (%rdi),%edx
    187a:	48 8d 35 83 07 00 00 	lea    0x783(%rip),%rsi        # 2004 <_IO_stdin_used+0x4>
    1881:	bf 01 00 00 00       	mov    $0x1,%edi
    1886:	e8 15 f9 ff ff       	call   11a0 <__printf_chk@plt>
    struct Thread *me = data->sender;
    188b:	4c 8b 63 08          	mov    0x8(%rbx),%r12
    188f:	bf 01 00 00 00       	mov    $0x1,%edi
    1894:	31 c0                	xor    %eax,%eax
    1896:	48 8d 35 77 07 00 00 	lea    0x777(%rip),%rsi        # 2014 <_IO_stdin_used+0x14>
    189d:	49 8b 54 24 18       	mov    0x18(%r12),%rdx
    18a2:	e8 f9 f8 ff ff       	call   11a0 <__printf_chk@plt>
    while (data->running == 1) {
    18a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    18b0:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    18b6:	83 f8 01             	cmp    $0x1,%eax
    18b9:	75 ac                	jne    1867 <disruptor_thread+0x37>
      asm volatile ("sfence" ::: "memory");
    18bb:	0f ae f8             	sfence
      long pos = (((me->realend & END_MASK) >> 32) + 1) % data->size;
    18be:	4d 8b 8c 24 80 01 00 00 	mov    0x180(%r12),%r9
      for (int x  = 0 ; x < data->other_count; x++) {
    18c6:	48 63 b3 08 02 00 00 	movslq 0x208(%rbx),%rsi
      long pos = (((me->realend & END_MASK) >> 32) + 1) % data->size;
    18cd:	4d 89 c8             	mov    %r9,%r8
    18d0:	49 c1 f8 20          	sar    $0x20,%r8
    18d4:	41 81 e0 ff ff ff 0f 	and    $0xfffffff,%r8d
    18db:	49 8d 40 01          	lea    0x1(%r8),%rax
    18df:	48 99                	cqto
    18e1:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
      for (int x  = 0 ; x < data->other_count; x++) {
    18e8:	85 f6                	test   %esi,%esi
    18ea:	0f 8e c0 00 00 00    	jle    19b0 <disruptor_thread+0x180>
    18f0:	48 8b 8b 00 02 00 00 	mov    0x200(%rbx),%rcx
    18f7:	48 8d 3c f1          	lea    (%rcx,%rsi,8),%rdi
    18fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        if (pos == data->readers[x]->start) {
    1900:	48 8b 31             	mov    (%rcx),%rsi
    1903:	48 63 b6 80 00 00 00 	movslq 0x80(%rsi),%rsi
    190a:	48 39 d6             	cmp    %rdx,%rsi
    190d:	74 a1                	je     18b0 <disruptor_thread+0x80>
      for (int x  = 0 ; x < data->other_count; x++) {
    190f:	48 83 c1 08          	add    $0x8,%rcx
    1913:	48 39 cf             	cmp    %rcx,%rdi
    1916:	75 e8                	jne    1900 <disruptor_thread+0xd0>
              changed = (((original & END_MASK) >> 32)) % me->size;
    1918:	4c 89 c0             	mov    %r8,%rax
    191b:	48 99                	cqto
    191d:	49 f7 bc 24 90 01 00 00 	idivq  0x190(%r12)
              long new = (data->thread_tag) | ((changed + 1) << 32);
    1925:	48 63 83 14 02 00 00 	movslq 0x214(%rbx),%rax
    192c:	48 8d 4a 01          	lea    0x1(%rdx),%rcx
    1930:	48 c1 e1 20          	shl    $0x20,%rcx
    1934:	48 09 c1             	or     %rax,%rcx
                me->data[changed].complete[x] = 0;
    1937:	48 89 d0             	mov    %rdx,%rax
    193a:	48 c1 e0 09          	shl    $0x9,%rax
    193e:	49 03 44 24 18       	add    0x18(%r12),%rax
    1943:	48 8b b0 00 01 00 00 	mov    0x100(%rax),%rsi
    194a:	31 c0                	xor    %eax,%eax
    194c:	0f 1f 40 00          	nopl   0x0(%rax)
    1950:	c7 04 86 00 00 00 00 	movl   $0x0,(%rsi,%rax,4)
              for (int x = 0 ; x < data->other_count; x++) {
    1957:	48 83 c0 01          	add    $0x1,%rax
    195b:	39 83 08 02 00 00    	cmp    %eax,0x208(%rbx)
    1961:	7f ed                	jg     1950 <disruptor_thread+0x120>
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED))) {
    1963:	49 8d b4 24 80 01 00 00 	lea    0x180(%r12),%rsi
    196b:	4c 89 c8             	mov    %r9,%rax
    196e:	f0 48 0f b1 0e       	lock cmpxchg %rcx,(%rsi)
    1973:	0f 85 39 01 00 00    	jne    1ab2 <disruptor_thread+0x282>
                clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1979:	49 8b 74 24 18       	mov    0x18(%r12),%rsi
    197e:	48 c1 e2 09          	shl    $0x9,%rdx
    1982:	bf 04 00 00 00       	mov    $0x4,%edi
    1987:	49 89 d5             	mov    %rdx,%r13
    198a:	48 01 d6             	add    %rdx,%rsi
    198d:	e8 ae f7 ff ff       	call   1140 <clock_gettime@plt>
                __atomic_store_n(&me->sender->data[changed].written, me->other_count, __ATOMIC_SEQ_CST);
    1992:	49 8b 44 24 08       	mov    0x8(%r12),%rax
    1997:	48 8b 50 18          	mov    0x18(%rax),%rdx
    199b:	41 8b 84 24 08 02 00 00 	mov    0x208(%r12),%eax
    19a3:	42 87 84 2a 80 01 00 00 	xchg   %eax,0x180(%rdx,%r13,1)
    19ab:	e9 00 ff ff ff       	jmp    18b0 <disruptor_thread+0x80>
              changed = (((original & END_MASK) >> 32)) % me->size;
    19b0:	4c 89 c0             	mov    %r8,%rax
    19b3:	48 99                	cqto
    19b5:	49 f7 bc 24 90 01 00 00 	idivq  0x190(%r12)
              long new = (data->thread_tag) | ((changed + 1) << 32);
    19bd:	48 63 83 14 02 00 00 	movslq 0x214(%rbx),%rax
    19c4:	48 8d 4a 01          	lea    0x1(%rdx),%rcx
    19c8:	48 c1 e1 20          	shl    $0x20,%rcx
    19cc:	48 09 c1             	or     %rax,%rcx
              for (int x = 0 ; x < data->other_count; x++) {
    19cf:	eb 92                	jmp    1963 <disruptor_thread+0x133>
    19d1:	8b 97 0c 02 00 00    	mov    0x20c(%rdi),%edx
    19d7:	48 8d 35 52 06 00 00 	lea    0x652(%rip),%rsi        # 2030 <_IO_stdin_used+0x30>
    19de:	bf 01 00 00 00       	mov    $0x1,%edi
    19e3:	31 c0                	xor    %eax,%eax
    19e5:	e8 b6 f7 ff ff       	call   11a0 <__printf_chk@plt>
    struct Thread *sender = data->sender;
    19ea:	4c 8b 73 08          	mov    0x8(%rbx),%r14
    19ee:	bf 01 00 00 00       	mov    $0x1,%edi
    19f3:	31 c0                	xor    %eax,%eax
    19f5:	48 8d 35 44 06 00 00 	lea    0x644(%rip),%rsi        # 2040 <_IO_stdin_used+0x40>
    struct Snapshot * rdata = sender->data;
    19fc:	4d 8b 66 18          	mov    0x18(%r14),%r12
    1a00:	4c 89 e2             	mov    %r12,%rdx
    1a03:	e8 98 f7 ff ff       	call   11a0 <__printf_chk@plt>
    while (data->running == 1) {
    1a08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    1a10:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    1a16:	83 f8 01             	cmp    $0x1,%eax
    1a19:	0f 85 48 fe ff ff    	jne    1867 <disruptor_thread+0x37>
      int pos = ((__atomic_load_n(&sender->realend, __ATOMIC_SEQ_CST) & END_MASK) >> 32);
    1a1f:	49 8b 86 80 01 00 00 	mov    0x180(%r14),%rax
    1a26:	48 c1 f8 20          	sar    $0x20,%rax
    1a2a:	25 ff ff ff 0f       	and    $0xfffffff,%eax
      if (pos == data->start) {
    1a2f:	44 8b ab 80 00 00 00 	mov    0x80(%rbx),%r13d
    1a36:	41 39 c5             	cmp    %eax,%r13d
    1a39:	74 d5                	je     1a10 <disruptor_thread+0x1e0>
          int written = __atomic_load_n(&rdata[changed].written, __ATOMIC_SEQ_CST);
    1a3b:	4d 63 fd             	movslq %r13d,%r15
    1a3e:	49 c1 e7 09          	shl    $0x9,%r15
    1a42:	4d 01 e7             	add    %r12,%r15
    1a45:	41 8b 87 80 01 00 00 	mov    0x180(%r15),%eax
          if (written > 0) {
    1a4c:	85 c0                	test   %eax,%eax
    1a4e:	7e c0                	jle    1a10 <disruptor_thread+0x1e0>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1a50:	48 63 b3 0c 02 00 00 	movslq 0x20c(%rbx),%rsi
    1a57:	bf 04 00 00 00       	mov    $0x4,%edi
    1a5c:	48 c1 e6 04          	shl    $0x4,%rsi
    1a60:	49 03 b7 80 00 00 00 	add    0x80(%r15),%rsi
    1a67:	e8 d4 f6 ff ff       	call   1140 <clock_gettime@plt>
              rdata[changed].complete[data->reader_index] = 1;
    1a6c:	49 8b 87 00 01 00 00 	mov    0x100(%r15),%rax
    1a73:	48 63 93 0c 02 00 00 	movslq 0x20c(%rbx),%rdx
    1a7a:	c7 04 90 01 00 00 00 	movl   $0x1,(%rax,%rdx,4)
              data->start = (changed + 1) % data->size;
    1a81:	41 8d 45 01          	lea    0x1(%r13),%eax
    1a85:	48 98                	cltq
    1a87:	48 99                	cqto
    1a89:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
    1a90:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
              __atomic_sub_fetch(&rdata[changed].written, 1, __ATOMIC_SEQ_CST);
    1a96:	f0 41 83 af 80 01 00 00 01 	lock subl $0x1,0x180(%r15)
    1a9f:	e9 6c ff ff ff       	jmp    1a10 <disruptor_thread+0x1e0>
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED))) {
    1aa4:	4c 89 c0             	mov    %r8,%rax
    1aa7:	f0 48 0f b1 0e       	lock cmpxchg %rcx,(%rsi)
    1aac:	0f 84 c7 fe ff ff    	je     1979 <disruptor_thread+0x149>
                original = me->realend;
    1ab2:	4d 8b 84 24 80 01 00 00 	mov    0x180(%r12),%r8
                changed = (((original & END_MASK) >> 32)) % me->size;
    1aba:	4c 89 c0             	mov    %r8,%rax
    1abd:	48 c1 f8 20          	sar    $0x20,%rax
    1ac1:	25 ff ff ff 0f       	and    $0xfffffff,%eax
    1ac6:	48 99                	cqto
    1ac8:	49 f7 bc 24 90 01 00 00 	idivq  0x190(%r12)
                new = (data->thread_tag) | ((changed + 1) << 32);
    1ad0:	48 63 83 14 02 00 00 	movslq 0x214(%rbx),%rax
    1ad7:	48 8d 4a 01          	lea    0x1(%rdx),%rcx
    1adb:	48 c1 e1 20          	shl    $0x20,%rcx
    1adf:	48 09 c1             	or     %rax,%rcx
                for (int x = 0 ; x < data->other_count; x++) {
    1ae2:	83 bb 08 02 00 00 00 	cmpl   $0x0,0x208(%rbx)
    1ae9:	7e b9                	jle    1aa4 <disruptor_thread+0x274>
                  me->data[changed].complete[x] = 0;
    1aeb:	48 89 d0             	mov    %rdx,%rax
    1aee:	31 ff                	xor    %edi,%edi
    1af0:	48 c1 e0 09          	shl    $0x9,%rax
    1af4:	49 03 44 24 18       	add    0x18(%r12),%rax
    1af9:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
    1b00:	c7 04 b8 00 00 00 00 	movl   $0x0,(%rax,%rdi,4)
                for (int x = 0 ; x < data->other_count; x++) {
    1b07:	48 83 c7 01          	add    $0x1,%rdi
    1b0b:	39 bb 08 02 00 00    	cmp    %edi,0x208(%rbx)
    1b11:	7f ed                	jg     1b00 <disruptor_thread+0x2d0>
    1b13:	eb 8f                	jmp    1aa4 <disruptor_thread+0x274>
    1b15:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000001b20 <min>:
int min(long a, long b) {
    1b20:	f3 0f 1e fa          	endbr64
    1b24:	55                   	push   %rbp
    1b25:	48 89 e5             	mov    %rsp,%rbp
    1b28:	ff 15 ba 24 00 00    	call   *0x24ba(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
  if (a < b) return a;
    1b2e:	48 39 f7             	cmp    %rsi,%rdi
    1b31:	7c 02                	jl     1b35 <min+0x15>
  if (b < a) return b;
    1b33:	7f 0b                	jg     1b40 <min+0x20>
  if (a < b) return a;
    1b35:	89 f8                	mov    %edi,%eax
}
    1b37:	5d                   	pop    %rbp
    1b38:	c3                   	ret
    1b39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (b < a) return b;
    1b40:	89 f0                	mov    %esi,%eax
}
    1b42:	5d                   	pop    %rbp
    1b43:	c3                   	ret
    1b44:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    1b4e:	66 90                	xchg   %ax,%ax

0000000000001b50 <atexit>:
    1b50:	f3 0f 1e fa          	endbr64
    1b54:	48 8b 15 ad 24 00 00 	mov    0x24ad(%rip),%rdx        # 4008 <__dso_handle>
    1b5b:	31 f6                	xor    %esi,%esi
    1b5d:	e9 6e f6 ff ff       	jmp    11d0 <__cxa_atexit@plt>
    1b62:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    1b6c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000001b70 <__stack_chk_fail_local>:
    1b70:	f3 0f 1e fa          	endbr64
    1b74:	50                   	push   %rax
    1b75:	58                   	pop    %rax
    1b76:	48 83 ec 08          	sub    $0x8,%rsp
    1b7a:	e8 d1 f5 ff ff       	call   1150 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000001b80 <_fini>:
    1b80:	f3 0f 1e fa          	endbr64
    1b84:	48 83 ec 08          	sub    $0x8,%rsp
    1b88:	48 83 c4 08          	add    $0x8,%rsp
    1b8c:	c3                   	ret
