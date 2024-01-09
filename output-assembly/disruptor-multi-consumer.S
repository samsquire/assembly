
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
    11c4:	41 56                	push   %r14
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    11c6:	b9 00 80 00 00       	mov    $0x8000,%ecx
    11cb:	ba 0f 00 00 00       	mov    $0xf,%edx
    11d0:	48 8d 35 91 0f 00 00 	lea    0xf91(%rip),%rsi        # 2168 <_IO_stdin_used+0x168>
    11d7:	41 55                	push   %r13
    11d9:	bf 01 00 00 00       	mov    $0x1,%edi
    11de:	41 54                	push   %r12
    11e0:	55                   	push   %rbp
    11e1:	53                   	push   %rbx
    11e2:	48 83 ec 50          	sub    $0x50,%rsp
    11e6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    11ef:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    11f4:	31 c0                	xor    %eax,%eax
    11f6:	e8 75 ff ff ff       	call   1170 <__printf_chk@plt>
    11fb:	ba 01 00 00 00       	mov    $0x1,%edx
    1200:	48 8d 35 55 0e 00 00 	lea    0xe55(%rip),%rsi        # 205c <_IO_stdin_used+0x5c>
    1207:	31 c0                	xor    %eax,%eax
    1209:	bf 01 00 00 00       	mov    $0x1,%edi
    120e:	e8 5d ff ff ff       	call   1170 <__printf_chk@plt>
    1213:	ba 01 00 00 00       	mov    $0x1,%edx
    1218:	48 8d 35 4d 0e 00 00 	lea    0xe4d(%rip),%rsi        # 206c <_IO_stdin_used+0x6c>
    121f:	31 c0                	xor    %eax,%eax
    1221:	bf 01 00 00 00       	mov    $0x1,%edi
    1226:	e8 45 ff ff ff       	call   1170 <__printf_chk@plt>
    122b:	ba 01 00 00 00       	mov    $0x1,%edx
    1230:	48 8d 35 47 0e 00 00 	lea    0xe47(%rip),%rsi        # 207e <_IO_stdin_used+0x7e>
    1237:	31 c0                	xor    %eax,%eax
    1239:	bf 01 00 00 00       	mov    $0x1,%edi
    123e:	e8 2d ff ff ff       	call   1170 <__printf_chk@plt>
    1243:	ba 02 00 00 00       	mov    $0x2,%edx
    1248:	48 8d 35 41 0e 00 00 	lea    0xe41(%rip),%rsi        # 2090 <_IO_stdin_used+0x90>
    124f:	31 c0                	xor    %eax,%eax
    1251:	bf 01 00 00 00       	mov    $0x1,%edi
    1256:	e8 15 ff ff ff       	call   1170 <__printf_chk@plt>
  int group_size = writers_count + other_count;
  printf("Readers count %d\n", other_count);
  printf("Writers count %d\n", writers_count);
  int thread_count = groups * (other_count + writers_count);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    125b:	be 80 02 00 00       	mov    $0x280,%esi
    1260:	bf 02 00 00 00       	mov    $0x2,%edi
    1265:	e8 f6 fe ff ff       	call   1160 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    126a:	be 38 00 00 00       	mov    $0x38,%esi
    126f:	bf 02 00 00 00       	mov    $0x2,%edi
    1274:	66 48 0f 6e c8       	movq   %rax,%xmm1
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    1279:	49 89 c4             	mov    %rax,%r12
    127c:	66 0f 6c c9          	punpcklqdq %xmm1,%xmm1
    1280:	0f 29 0c 24          	movaps %xmm1,(%rsp)
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1284:	e8 d7 fe ff ff       	call   1160 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1289:	be 08 00 00 00       	mov    $0x8,%esi
    128e:	bf 02 00 00 00       	mov    $0x2,%edi
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1293:	49 89 c6             	mov    %rax,%r14
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    1296:	e8 c5 fe ff ff       	call   1160 <calloc@plt>
    129b:	31 d2                	xor    %edx,%edx
    129d:	bf 01 00 00 00       	mov    $0x1,%edi
    12a2:	48 8d 35 fe 0d 00 00 	lea    0xdfe(%rip),%rsi        # 20a7 <_IO_stdin_used+0xa7>
    12a9:	49 89 c5             	mov    %rax,%r13
    12ac:	31 c0                	xor    %eax,%eax
    12ae:	e8 bd fe ff ff       	call   1170 <__printf_chk@plt>
    12b3:	48 8d 3d f8 0d 00 00 	lea    0xdf8(%rip),%rdi        # 20b2 <_IO_stdin_used+0xb2>
    12ba:	e8 51 fe ff ff       	call   1110 <puts@plt>
    int receiver2 = receiver + 1; 
    int seq[] = {1, 2, 5};
    int tag_index[] = {1, 5, 7};
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
      printf("CREATE SENDER THREAD\n");
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12bf:	be 80 00 00 00       	mov    $0x80,%esi
    12c4:	bf 01 00 00 00       	mov    $0x1,%edi
    12c9:	e8 92 fe ff ff       	call   1160 <calloc@plt>
    12ce:	31 c9                	xor    %ecx,%ecx
    12d0:	31 d2                	xor    %edx,%edx
    12d2:	48 8d 35 b7 0e 00 00 	lea    0xeb7(%rip),%rsi        # 2190 <_IO_stdin_used+0x190>
      CPU_ZERO(sendercpu);
      CPU_SET(curcpu, sendercpu);
    12d9:	48 83 08 01          	orq    $0x1,(%rax)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12dd:	48 89 c3             	mov    %rax,%rbx
    12e0:	bf 01 00 00 00       	mov    $0x1,%edi
    12e5:	31 c0                	xor    %eax,%eax
    12e7:	e8 84 fe ff ff       	call   1170 <__printf_chk@plt>
      thread_data[n].multiple = seq[sender_index % writers_count];
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].thread_tag = tag_index[sender_index];
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
    12ec:	4d 89 64 24 08       	mov    %r12,0x8(%r12)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    12f1:	be 08 00 00 00       	mov    $0x8,%esi
    12f6:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[n].cpu_set = sendercpu;
    12fb:	49 89 9c 24 a0 01 00 00 	mov    %rbx,0x1a0(%r12)
      thread_data[n].mode = WRITER;
    1303:	41 c7 84 24 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%r12)
      thread_data[n].thread_index = n;
    130f:	41 c7 04 24 00 00 00 00 	movl   $0x0,(%r12)
      thread_data[n].multiple = seq[sender_index % writers_count];
    1317:	41 c7 84 24 10 02 00 00 01 00 00 00 	movl   $0x1,0x210(%r12)
      thread_data[n].running = 1;
    1323:	41 c7 84 24 98 01 00 00 01 00 00 00 	movl   $0x1,0x198(%r12)
      thread_data[n].size = buffer_size;
    132f:	49 c7 84 24 90 01 00 00 00 80 00 00 	movq   $0x8000,0x190(%r12)
      thread_data[n].thread_tag = tag_index[sender_index];
    133b:	41 c7 84 24 14 02 00 00 01 00 00 00 	movl   $0x1,0x214(%r12)
      thread_data[n].end = 0;
    1347:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1353:	e8 08 fe ff ff       	call   1160 <calloc@plt>
      if (n == sender) {
        thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    1358:	be 00 02 00 00       	mov    $0x200,%esi
    135d:	bf 00 80 00 00       	mov    $0x8000,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1362:	49 89 84 24 00 02 00 00 	mov    %rax,0x200(%r12)
        thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    136a:	e8 f1 fd ff ff       	call   1160 <calloc@plt>
    136f:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    1374:	48 89 c5             	mov    %rax,%rbp
        for (int k = 0 ; k < buffer_size ; k++) {
    1377:	48 8d 98 80 00 00 00 	lea    0x80(%rax),%rbx
    137e:	48 81 c5 80 00 00 01 	add    $0x1000080,%rbp
    1385:	0f 1f 00             	nopl   (%rax)
          thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1388:	be 04 00 00 00       	mov    $0x4,%esi
    138d:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int k = 0 ; k < buffer_size ; k++) {
    1392:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
          thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1399:	e8 c2 fd ff ff       	call   1160 <calloc@plt>
          thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    139e:	be 10 00 00 00       	mov    $0x10,%esi
    13a3:	bf 01 00 00 00       	mov    $0x1,%edi
          thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13a8:	48 89 83 80 fe ff ff 	mov    %rax,-0x180(%rbx)
          thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    13af:	e8 ac fd ff ff       	call   1160 <calloc@plt>
          thread_data[n].data[k].written = 0;
    13b4:	c7 83 00 ff ff ff 00 00 00 00 	movl   $0x0,-0x100(%rbx)
          thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    13be:	48 89 83 00 fe ff ff 	mov    %rax,-0x200(%rbx)
        for (int k = 0 ; k < buffer_size ; k++) {
    13c5:	48 39 eb             	cmp    %rbp,%rbx
    13c8:	75 be                	jne    1388 <main+0x1c8>
    13ca:	31 d2                	xor    %edx,%edx
    13cc:	48 8d 35 f4 0c 00 00 	lea    0xcf4(%rip),%rsi        # 20c7 <_IO_stdin_used+0xc7>
    13d3:	bf 01 00 00 00       	mov    $0x1,%edi
    13d8:	31 c0                	xor    %eax,%eax
        }
      }
      thread_data[n].other_count = other_count;
    13da:	41 c7 84 24 08 02 00 00 01 00 00 00 	movl   $0x1,0x208(%r12)
    }

    printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      thread_data[j].thread_index = j;
    13e6:	49 8d ac 24 80 02 00 00 	lea    0x280(%r12),%rbp
    13ee:	e8 7d fd ff ff       	call   1170 <__printf_chk@plt>
      thread_data[j].reader_index = receiver_index;
      thread_data[j].multiple = receiver_index % other_count;
      thread_data[j].other_count = other_count;
     
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    13f3:	be 80 00 00 00       	mov    $0x80,%esi
    13f8:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].thread_index = j;
    13fd:	41 c7 84 24 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%r12)
      thread_data[j].multiple = receiver_index % other_count;
    1409:	41 c7 84 24 90 04 00 00 00 00 00 00 	movl   $0x0,0x490(%r12)
      thread_data[j].other_count = other_count;
    1415:	49 c7 84 24 88 04 00 00 01 00 00 00 	movq   $0x1,0x488(%r12)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1421:	e8 3a fd ff ff       	call   1160 <calloc@plt>
    1426:	b9 02 00 00 00       	mov    $0x2,%ecx
    142b:	ba 01 00 00 00       	mov    $0x1,%edx
    1430:	48 8d 35 79 0d 00 00 	lea    0xd79(%rip),%rsi        # 21b0 <_IO_stdin_used+0x1b0>
      CPU_ZERO(receivercpu);
      CPU_SET(curcpu, receivercpu);
    1437:	48 83 08 04          	orq    $0x4,(%rax)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    143b:	48 89 c3             	mov    %rax,%rbx
    143e:	bf 01 00 00 00       	mov    $0x1,%edi
    1443:	31 c0                	xor    %eax,%eax
    1445:	e8 26 fd ff ff       	call   1170 <__printf_chk@plt>
        for (int n = 0 ; n < buffer_size ; n++) {
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
        }
      } */
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
    144a:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
    144f:	31 c9                	xor    %ecx,%ecx
    1451:	31 d2                	xor    %edx,%edx
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    1453:	49 8b 84 24 00 02 00 00 	mov    0x200(%r12),%rax
      thread_data[j].running = 1;
    145b:	41 c7 84 24 18 04 00 00 01 00 00 00 	movl   $0x1,0x418(%r12)
    1467:	48 8d 35 6a 0d 00 00 	lea    0xd6a(%rip),%rsi        # 21d8 <_IO_stdin_used+0x1d8>
    146e:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].cpu_set = receivercpu;
    1473:	49 89 9c 24 20 04 00 00 	mov    %rbx,0x420(%r12)
      thread_data[j].readers = thread_data[sender].readers;
    147b:	49 89 84 24 80 04 00 00 	mov    %rax,0x480(%r12)
    1483:	31 c0                	xor    %eax,%eax
      thread_data[j].mode = READER;
    1485:	41 c7 84 24 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%r12)
      thread_data[j].size = buffer_size;
    1491:	49 c7 84 24 10 04 00 00 00 80 00 00 	movq   $0x8000,0x410(%r12)
      thread_data[j].start = 0;
    149d:	41 c7 84 24 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%r12)
      thread_data[j].other_count = other_count;
    14a9:	41 c7 84 24 88 04 00 00 01 00 00 00 	movl   $0x1,0x488(%r12)
      thread_data[j].sender = &thread_data[sender];
    14b5:	41 0f 11 94 24 88 02 00 00 	movups %xmm2,0x288(%r12)
    14be:	e8 ad fc ff ff       	call   1170 <__printf_chk@plt>
      // printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        printf("assigned reader %d to sender %d\n", receiver_index, n);
        thread_data[n].readers[receiver_index] = &thread_data[j];
    14c3:	49 8b 84 24 00 02 00 00 	mov    0x200(%r12),%rax
    14cb:	48 89 28             	mov    %rbp,(%rax)
      }
    }
    curcpu = 0;
    // printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    14ce:	0f ae f0             	mfence
    14d1:	bf 01 00 00 00       	mov    $0x1,%edi
    14d6:	31 c0                	xor    %eax,%eax
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    14d8:	49 8d 5e 38          	lea    0x38(%r14),%rbx
    14dc:	ba 01 00 00 00       	mov    $0x1,%edx
    14e1:	48 8d 35 f4 0b 00 00 	lea    0xbf4(%rip),%rsi        # 20dc <_IO_stdin_used+0xdc>
  param.sched_priority = 0;
    14e8:	c7 44 24 1c 00 00 00 00 	movl   $0x0,0x1c(%rsp)
    14f0:	e8 7b fc ff ff       	call   1170 <__printf_chk@plt>
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    14f5:	31 f6                	xor    %esi,%esi
    14f7:	48 89 df             	mov    %rbx,%rdi
    14fa:	e8 51 fc ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    14ff:	85 c0                	test   %eax,%eax
    1501:	0f 85 7b 01 00 00    	jne    1682 <main+0x4c2>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    1507:	48 8d 74 24 1c       	lea    0x1c(%rsp),%rsi
    150c:	48 89 df             	mov    %rbx,%rdi
    150f:	e8 7c fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1514:	85 c0                	test   %eax,%eax
    1516:	0f 85 81 01 00 00    	jne    169d <main+0x4dd>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    151c:	48 89 e9             	mov    %rbp,%rcx
    151f:	48 8d 2d 8a 02 00 00 	lea    0x28a(%rip),%rbp        # 17b0 <disruptor_thread>
    1526:	49 8d 7d 08          	lea    0x8(%r13),%rdi
    152a:	48 89 de             	mov    %rbx,%rsi
    152d:	48 89 ea             	mov    %rbp,%rdx
    1530:	e8 4b fc ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    1535:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    1539:	be 08 00 00 00       	mov    $0x8,%esi
    153e:	49 8b 94 24 20 04 00 00 	mov    0x420(%r12),%rdx
    1546:	e8 b5 fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    154b:	31 f6                	xor    %esi,%esi
    154d:	4c 89 f7             	mov    %r14,%rdi
    1550:	e8 fb fb ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    1555:	85 c0                	test   %eax,%eax
    1557:	0f 85 25 01 00 00    	jne    1682 <main+0x4c2>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    155d:	48 8d 74 24 18       	lea    0x18(%rsp),%rsi
    1562:	4c 89 f7             	mov    %r14,%rdi
      param2.sched_priority = 0;
    1565:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    156d:	e8 1e fc ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1572:	85 c0                	test   %eax,%eax
    1574:	0f 85 23 01 00 00    	jne    169d <main+0x4dd>
    157a:	31 d2                	xor    %edx,%edx
    157c:	48 8d 35 b1 0b 00 00 	lea    0xbb1(%rip),%rsi        # 2134 <_IO_stdin_used+0x134>
    1583:	bf 01 00 00 00       	mov    $0x1,%edi
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    1588:	31 db                	xor    %ebx,%ebx
    158a:	e8 e1 fb ff ff       	call   1170 <__printf_chk@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    158f:	4c 89 e1             	mov    %r12,%rcx
    1592:	48 89 ea             	mov    %rbp,%rdx
    1595:	4c 89 f6             	mov    %r14,%rsi
    1598:	4c 89 ef             	mov    %r13,%rdi
    159b:	48 8d 2d ae 0b 00 00 	lea    0xbae(%rip),%rbp        # 2150 <_IO_stdin_used+0x150>
    15a2:	e8 d9 fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    15a7:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    15ab:	be 08 00 00 00       	mov    $0x8,%esi
    15b0:	49 8b 94 24 a0 01 00 00 	mov    0x1a0(%r12),%rdx
    15b8:	e8 43 fb ff ff       	call   1100 <pthread_setaffinity_np@plt>
  nanosleep(&preempt , &rem2);
    15bd:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    15c2:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
  struct timespec preempt = {
    15c7:	66 0f 6f 05 31 0c 00 00 	movdqa 0xc31(%rip),%xmm0        # 2200 <_IO_stdin_used+0x200>
    15cf:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  nanosleep(&preempt , &rem2);
    15d4:	e8 67 fb ff ff       	call   1140 <nanosleep@plt>
      pthread_join(thread[n], res1);
    15d9:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    15dd:	31 f6                	xor    %esi,%esi
    thread_data[sender].running = 0;
    15df:	41 c7 84 24 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r12)
      thread_data[j].running = 0;
    15eb:	41 c7 84 24 18 04 00 00 00 00 00 00 	movl   $0x0,0x418(%r12)
      thread_data[n].running = 0;
    15f7:	41 c7 84 24 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r12)
      pthread_join(thread[n], res1);
    1603:	e8 a8 fb ff ff       	call   11b0 <pthread_join@plt>
      pthread_join(thread[j], res2);
    1608:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    160c:	31 f6                	xor    %esi,%esi
    160e:	e8 9d fb ff ff       	call   11b0 <pthread_join@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    // printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    1613:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      int compcount = 0;
      for (int n = 0 ; n < other_count ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    1618:	49 8b 44 24 18       	mov    0x18(%r12),%rax
    161d:	48 8b 94 18 00 01 00 00 	mov    0x100(%rax,%rbx,1),%rdx
    1625:	83 3a 01             	cmpl   $0x1,(%rdx)
    1628:	75 29                	jne    1653 <main+0x493>
      }
      // printf("%d\n", compcount);
      if (compcount == other_count) {
      for (int n = 0 ; n < other_count ; n++) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
    162a:	48 01 d8             	add    %rbx,%rax
    162d:	48 89 ee             	mov    %rbp,%rsi
    1630:	bf 01 00 00 00       	mov    $0x1,%edi
          struct timespec end = thread_data[sender].data[y].end[n];
    1635:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    163c:	4c 8b 42 08          	mov    0x8(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    1640:	48 8b 0a             	mov    (%rdx),%rcx
    1643:	31 d2                	xor    %edx,%edx
    1645:	48 2b 08             	sub    (%rax),%rcx
    1648:	4c 2b 40 08          	sub    0x8(%rax),%r8
    164c:	31 c0                	xor    %eax,%eax
    164e:	e8 1d fb ff ff       	call   1170 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    1653:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
    165a:	48 81 fb 00 00 00 01 	cmp    $0x1000000,%rbx
    1661:	75 b5                	jne    1618 <main+0x458>
    }
    // printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    1663:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    1668:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1671:	75 25                	jne    1698 <main+0x4d8>
    1673:	48 83 c4 50          	add    $0x50,%rsp
    1677:	31 c0                	xor    %eax,%eax
    1679:	5b                   	pop    %rbx
    167a:	5d                   	pop    %rbp
    167b:	41 5c                	pop    %r12
    167d:	41 5d                	pop    %r13
    167f:	41 5e                	pop    %r14
    1681:	c3                   	ret
    1682:	48 8d 3d 70 0a 00 00 	lea    0xa70(%rip),%rdi        # 20f9 <_IO_stdin_used+0xf9>
    1689:	e8 82 fa ff ff       	call   1110 <puts@plt>
               exit(1);
    168e:	bf 01 00 00 00       	mov    $0x1,%edi
    1693:	e8 08 fb ff ff       	call   11a0 <exit@plt>
}
    1698:	e8 93 fa ff ff       	call   1130 <__stack_chk_fail@plt>
    169d:	48 8d 3d 73 0a 00 00 	lea    0xa73(%rip),%rdi        # 2117 <_IO_stdin_used+0x117>
    16a4:	e8 67 fa ff ff       	call   1110 <puts@plt>
              exit(1);
    16a9:	bf 01 00 00 00       	mov    $0x1,%edi
    16ae:	e8 ed fa ff ff       	call   11a0 <exit@plt>
    16b3:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    16bd:	0f 1f 00             	nopl   (%rax)

00000000000016c0 <_start>:
    16c0:	f3 0f 1e fa          	endbr64
    16c4:	31 ed                	xor    %ebp,%ebp
    16c6:	49 89 d1             	mov    %rdx,%r9
    16c9:	5e                   	pop    %rsi
    16ca:	48 89 e2             	mov    %rsp,%rdx
    16cd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    16d1:	50                   	push   %rax
    16d2:	54                   	push   %rsp
    16d3:	45 31 c0             	xor    %r8d,%r8d
    16d6:	31 c9                	xor    %ecx,%ecx
    16d8:	48 8d 3d e1 fa ff ff 	lea    -0x51f(%rip),%rdi        # 11c0 <main>
    16df:	ff 15 f3 28 00 00    	call   *0x28f3(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    16e5:	f4                   	hlt
    16e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000016f0 <deregister_tm_clones>:
    16f0:	48 8d 3d 19 29 00 00 	lea    0x2919(%rip),%rdi        # 4010 <__TMC_END__>
    16f7:	48 8d 05 12 29 00 00 	lea    0x2912(%rip),%rax        # 4010 <__TMC_END__>
    16fe:	48 39 f8             	cmp    %rdi,%rax
    1701:	74 15                	je     1718 <deregister_tm_clones+0x28>
    1703:	48 8b 05 d6 28 00 00 	mov    0x28d6(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    170a:	48 85 c0             	test   %rax,%rax
    170d:	74 09                	je     1718 <deregister_tm_clones+0x28>
    170f:	ff e0                	jmp    *%rax
    1711:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1718:	c3                   	ret
    1719:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001720 <register_tm_clones>:
    1720:	48 8d 3d e9 28 00 00 	lea    0x28e9(%rip),%rdi        # 4010 <__TMC_END__>
    1727:	48 8d 35 e2 28 00 00 	lea    0x28e2(%rip),%rsi        # 4010 <__TMC_END__>
    172e:	48 29 fe             	sub    %rdi,%rsi
    1731:	48 89 f0             	mov    %rsi,%rax
    1734:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1738:	48 c1 f8 03          	sar    $0x3,%rax
    173c:	48 01 c6             	add    %rax,%rsi
    173f:	48 d1 fe             	sar    %rsi
    1742:	74 14                	je     1758 <register_tm_clones+0x38>
    1744:	48 8b 05 a5 28 00 00 	mov    0x28a5(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    174b:	48 85 c0             	test   %rax,%rax
    174e:	74 08                	je     1758 <register_tm_clones+0x38>
    1750:	ff e0                	jmp    *%rax
    1752:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1758:	c3                   	ret
    1759:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001760 <__do_global_dtors_aux>:
    1760:	f3 0f 1e fa          	endbr64
    1764:	80 3d a5 28 00 00 00 	cmpb   $0x0,0x28a5(%rip)        # 4010 <__TMC_END__>
    176b:	75 2b                	jne    1798 <__do_global_dtors_aux+0x38>
    176d:	55                   	push   %rbp
    176e:	48 83 3d 82 28 00 00 00 	cmpq   $0x0,0x2882(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1776:	48 89 e5             	mov    %rsp,%rbp
    1779:	74 0c                	je     1787 <__do_global_dtors_aux+0x27>
    177b:	48 8b 3d 86 28 00 00 	mov    0x2886(%rip),%rdi        # 4008 <__dso_handle>
    1782:	e8 69 f9 ff ff       	call   10f0 <__cxa_finalize@plt>
    1787:	e8 64 ff ff ff       	call   16f0 <deregister_tm_clones>
    178c:	c6 05 7d 28 00 00 01 	movb   $0x1,0x287d(%rip)        # 4010 <__TMC_END__>
    1793:	5d                   	pop    %rbp
    1794:	c3                   	ret
    1795:	0f 1f 00             	nopl   (%rax)
    1798:	c3                   	ret
    1799:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017a0 <frame_dummy>:
    17a0:	f3 0f 1e fa          	endbr64
    17a4:	e9 77 ff ff ff       	jmp    1720 <register_tm_clones>
    17a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000017b0 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    17b0:	f3 0f 1e fa          	endbr64
    17b4:	41 56                	push   %r14
    17b6:	41 55                	push   %r13
    17b8:	41 54                	push   %r12
    17ba:	55                   	push   %rbp
    17bb:	53                   	push   %rbx
  if (data->mode == WRITER) {
    17bc:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
void * disruptor_thread(void * arg) {
    17c2:	48 89 fb             	mov    %rdi,%rbx
  if (data->mode == WRITER) {
    17c5:	85 c0                	test   %eax,%eax
    17c7:	74 1a                	je     17e3 <disruptor_thread+0x33>
  } else if (data->mode == READER) {
    17c9:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
    17cf:	83 f8 01             	cmp    $0x1,%eax
    17d2:	0f 84 5b 01 00 00    	je     1933 <disruptor_thread+0x183>
}
    17d8:	5b                   	pop    %rbx
    17d9:	31 c0                	xor    %eax,%eax
    17db:	5d                   	pop    %rbp
    17dc:	41 5c                	pop    %r12
    17de:	41 5d                	pop    %r13
    17e0:	41 5e                	pop    %r14
    17e2:	c3                   	ret
    17e3:	8b 17                	mov    (%rdi),%edx
    17e5:	48 8d 35 18 08 00 00 	lea    0x818(%rip),%rsi        # 2004 <_IO_stdin_used+0x4>
    17ec:	bf 01 00 00 00       	mov    $0x1,%edi
    17f1:	e8 7a f9 ff ff       	call   1170 <__printf_chk@plt>
    struct Thread *me = data->sender;
    17f6:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    17fa:	bf 01 00 00 00       	mov    $0x1,%edi
    17ff:	31 c0                	xor    %eax,%eax
    1801:	48 8d 35 0c 08 00 00 	lea    0x80c(%rip),%rsi        # 2014 <_IO_stdin_used+0x14>
    1808:	48 8b 55 18          	mov    0x18(%rbp),%rdx
    180c:	e8 5f f9 ff ff       	call   1170 <__printf_chk@plt>
    while (data->running == 1) {
    1811:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1818:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    181e:	83 f8 01             	cmp    $0x1,%eax
    1821:	75 b5                	jne    17d8 <disruptor_thread+0x28>
      asm volatile ("sfence" ::: "memory");
    1823:	0f ae f8             	sfence
      long pos = (((me->realend & END_MASK) >> 32) + 1) % data->size;
    1826:	4c 8b 8d 80 01 00 00 	mov    0x180(%rbp),%r9
      for (int x  = 0 ; x < data->other_count; x++) {
    182d:	48 63 b3 08 02 00 00 	movslq 0x208(%rbx),%rsi
      long pos = (((me->realend & END_MASK) >> 32) + 1) % data->size;
    1834:	4d 89 c8             	mov    %r9,%r8
    1837:	49 c1 f8 20          	sar    $0x20,%r8
    183b:	41 81 e0 ff ff ff 0f 	and    $0xfffffff,%r8d
    1842:	49 8d 40 01          	lea    0x1(%r8),%rax
    1846:	48 99                	cqto
    1848:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
      for (int x  = 0 ; x < data->other_count; x++) {
    184f:	85 f6                	test   %esi,%esi
    1851:	0f 8e bc 00 00 00    	jle    1913 <disruptor_thread+0x163>
    1857:	48 8b 8b 00 02 00 00 	mov    0x200(%rbx),%rcx
    185e:	48 8d 3c f1          	lea    (%rcx,%rsi,8),%rdi
    1862:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (pos == data->readers[x]->start) {
    1868:	48 8b 31             	mov    (%rcx),%rsi
    186b:	48 63 b6 80 00 00 00 	movslq 0x80(%rsi),%rsi
    1872:	48 39 d6             	cmp    %rdx,%rsi
    1875:	74 a1                	je     1818 <disruptor_thread+0x68>
      for (int x  = 0 ; x < data->other_count; x++) {
    1877:	48 83 c1 08          	add    $0x8,%rcx
    187b:	48 39 cf             	cmp    %rcx,%rdi
    187e:	75 e8                	jne    1868 <disruptor_thread+0xb8>
              changed = (((original & END_MASK) >> 32)) % me->size;
    1880:	4c 89 c0             	mov    %r8,%rax
    1883:	48 99                	cqto
    1885:	48 f7 bd 90 01 00 00 	idivq  0x190(%rbp)
              long new = (data->thread_tag) | ((changed + 1) << 32);
    188c:	48 63 83 14 02 00 00 	movslq 0x214(%rbx),%rax
    1893:	48 8d 4a 01          	lea    0x1(%rdx),%rcx
    1897:	48 c1 e1 20          	shl    $0x20,%rcx
    189b:	48 09 c1             	or     %rax,%rcx
                me->data[changed].complete[x] = 0;
    189e:	48 89 d0             	mov    %rdx,%rax
    18a1:	48 c1 e0 09          	shl    $0x9,%rax
    18a5:	48 03 45 18          	add    0x18(%rbp),%rax
    18a9:	48 8b b0 00 01 00 00 	mov    0x100(%rax),%rsi
    18b0:	31 c0                	xor    %eax,%eax
    18b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    18b8:	c7 04 86 00 00 00 00 	movl   $0x0,(%rsi,%rax,4)
              for (int x = 0 ; x < data->other_count; x++) {
    18bf:	48 83 c0 01          	add    $0x1,%rax
    18c3:	39 83 08 02 00 00    	cmp    %eax,0x208(%rbx)
    18c9:	7f ed                	jg     18b8 <disruptor_thread+0x108>
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED))) {
    18cb:	48 8d b5 80 01 00 00 	lea    0x180(%rbp),%rsi
    18d2:	4c 89 c8             	mov    %r9,%rax
    18d5:	f0 48 0f b1 0e       	lock cmpxchg %rcx,(%rsi)
    18da:	0f 85 2f 01 00 00    	jne    1a0f <disruptor_thread+0x25f>
                clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    18e0:	48 8b 75 18          	mov    0x18(%rbp),%rsi
    18e4:	48 c1 e2 09          	shl    $0x9,%rdx
    18e8:	bf 04 00 00 00       	mov    $0x4,%edi
    18ed:	49 89 d4             	mov    %rdx,%r12
    18f0:	48 01 d6             	add    %rdx,%rsi
    18f3:	e8 28 f8 ff ff       	call   1120 <clock_gettime@plt>
                __atomic_store_n(&me->sender->data[changed].written, me->other_count, __ATOMIC_SEQ_CST);
    18f8:	48 8b 45 08          	mov    0x8(%rbp),%rax
    18fc:	48 8b 50 18          	mov    0x18(%rax),%rdx
    1900:	8b 85 08 02 00 00    	mov    0x208(%rbp),%eax
    1906:	42 87 84 22 80 01 00 00 	xchg   %eax,0x180(%rdx,%r12,1)
    190e:	e9 05 ff ff ff       	jmp    1818 <disruptor_thread+0x68>
              changed = (((original & END_MASK) >> 32)) % me->size;
    1913:	4c 89 c0             	mov    %r8,%rax
    1916:	48 99                	cqto
    1918:	48 f7 bd 90 01 00 00 	idivq  0x190(%rbp)
              long new = (data->thread_tag) | ((changed + 1) << 32);
    191f:	48 63 83 14 02 00 00 	movslq 0x214(%rbx),%rax
    1926:	48 8d 4a 01          	lea    0x1(%rdx),%rcx
    192a:	48 c1 e1 20          	shl    $0x20,%rcx
    192e:	48 09 c1             	or     %rax,%rcx
              for (int x = 0 ; x < data->other_count; x++) {
    1931:	eb 98                	jmp    18cb <disruptor_thread+0x11b>
    1933:	8b 97 0c 02 00 00    	mov    0x20c(%rdi),%edx
    1939:	48 8d 35 f0 06 00 00 	lea    0x6f0(%rip),%rsi        # 2030 <_IO_stdin_used+0x30>
    1940:	bf 01 00 00 00       	mov    $0x1,%edi
    1945:	31 c0                	xor    %eax,%eax
    1947:	e8 24 f8 ff ff       	call   1170 <__printf_chk@plt>
    struct Thread *sender = data->sender;
    194c:	4c 8b 6b 08          	mov    0x8(%rbx),%r13
    1950:	bf 01 00 00 00       	mov    $0x1,%edi
    1955:	31 c0                	xor    %eax,%eax
    1957:	48 8d 35 e2 06 00 00 	lea    0x6e2(%rip),%rsi        # 2040 <_IO_stdin_used+0x40>
    struct Snapshot * rdata = sender->data;
    195e:	4d 8b 65 18          	mov    0x18(%r13),%r12
    1962:	4c 89 e2             	mov    %r12,%rdx
    1965:	e8 06 f8 ff ff       	call   1170 <__printf_chk@plt>
    while (data->running == 1) {
    196a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1970:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    1976:	83 f8 01             	cmp    $0x1,%eax
    1979:	0f 85 59 fe ff ff    	jne    17d8 <disruptor_thread+0x28>
      int pos = ((__atomic_load_n(&sender->realend, __ATOMIC_SEQ_CST) & END_MASK) >> 32);
    197f:	49 8b 85 80 01 00 00 	mov    0x180(%r13),%rax
    1986:	48 c1 f8 20          	sar    $0x20,%rax
    198a:	25 ff ff ff 0f       	and    $0xfffffff,%eax
      if (pos == data->start) {
    198f:	8b ab 80 00 00 00    	mov    0x80(%rbx),%ebp
    1995:	39 c5                	cmp    %eax,%ebp
    1997:	74 d7                	je     1970 <disruptor_thread+0x1c0>
          int written = __atomic_load_n(&rdata[changed].written, __ATOMIC_SEQ_CST);
    1999:	4c 63 f5             	movslq %ebp,%r14
    199c:	49 c1 e6 09          	shl    $0x9,%r14
    19a0:	4d 01 e6             	add    %r12,%r14
    19a3:	41 8b 86 80 01 00 00 	mov    0x180(%r14),%eax
          if (written > 0) {
    19aa:	85 c0                	test   %eax,%eax
    19ac:	7e c2                	jle    1970 <disruptor_thread+0x1c0>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    19ae:	48 63 b3 0c 02 00 00 	movslq 0x20c(%rbx),%rsi
    19b5:	bf 04 00 00 00       	mov    $0x4,%edi
    19ba:	48 c1 e6 04          	shl    $0x4,%rsi
    19be:	49 03 b6 80 00 00 00 	add    0x80(%r14),%rsi
    19c5:	e8 56 f7 ff ff       	call   1120 <clock_gettime@plt>
              rdata[changed].complete[data->reader_index] = 1;
    19ca:	49 8b 86 00 01 00 00 	mov    0x100(%r14),%rax
    19d1:	48 63 93 0c 02 00 00 	movslq 0x20c(%rbx),%rdx
    19d8:	c7 04 90 01 00 00 00 	movl   $0x1,(%rax,%rdx,4)
              data->start = (changed + 1) % data->size;
    19df:	8d 45 01             	lea    0x1(%rbp),%eax
    19e2:	48 98                	cltq
    19e4:	48 99                	cqto
    19e6:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
    19ed:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
              __atomic_sub_fetch(&rdata[changed].written, 1, __ATOMIC_SEQ_CST);
    19f3:	f0 41 83 ae 80 01 00 00 01 	lock subl $0x1,0x180(%r14)
    19fc:	e9 6f ff ff ff       	jmp    1970 <disruptor_thread+0x1c0>
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED))) {
    1a01:	4c 89 c0             	mov    %r8,%rax
    1a04:	f0 48 0f b1 0e       	lock cmpxchg %rcx,(%rsi)
    1a09:	0f 84 d1 fe ff ff    	je     18e0 <disruptor_thread+0x130>
                original = me->realend;
    1a0f:	4c 8b 85 80 01 00 00 	mov    0x180(%rbp),%r8
                changed = (((original & END_MASK) >> 32)) % me->size;
    1a16:	4c 89 c0             	mov    %r8,%rax
    1a19:	48 c1 f8 20          	sar    $0x20,%rax
    1a1d:	25 ff ff ff 0f       	and    $0xfffffff,%eax
    1a22:	48 99                	cqto
    1a24:	48 f7 bd 90 01 00 00 	idivq  0x190(%rbp)
                new = (data->thread_tag) | ((changed + 1) << 32);
    1a2b:	48 63 83 14 02 00 00 	movslq 0x214(%rbx),%rax
    1a32:	48 8d 4a 01          	lea    0x1(%rdx),%rcx
    1a36:	48 c1 e1 20          	shl    $0x20,%rcx
    1a3a:	48 09 c1             	or     %rax,%rcx
                for (int x = 0 ; x < data->other_count; x++) {
    1a3d:	83 bb 08 02 00 00 00 	cmpl   $0x0,0x208(%rbx)
    1a44:	7e bb                	jle    1a01 <disruptor_thread+0x251>
                  me->data[changed].complete[x] = 0;
    1a46:	48 89 d0             	mov    %rdx,%rax
    1a49:	31 ff                	xor    %edi,%edi
    1a4b:	48 c1 e0 09          	shl    $0x9,%rax
    1a4f:	48 03 45 18          	add    0x18(%rbp),%rax
    1a53:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
    1a5a:	c7 04 b8 00 00 00 00 	movl   $0x0,(%rax,%rdi,4)
                for (int x = 0 ; x < data->other_count; x++) {
    1a61:	48 83 c7 01          	add    $0x1,%rdi
    1a65:	39 bb 08 02 00 00    	cmp    %edi,0x208(%rbx)
    1a6b:	7f ed                	jg     1a5a <disruptor_thread+0x2aa>
    1a6d:	eb 92                	jmp    1a01 <disruptor_thread+0x251>
    1a6f:	90                   	nop

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
