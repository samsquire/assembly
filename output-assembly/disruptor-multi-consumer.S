
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
    11d0:	48 8d 35 91 0f 00 00 	lea    0xf91(%rip),%rsi        # 2168 <_IO_stdin_used+0x168>
    11d7:	41 56                	push   %r14
    11d9:	bf 01 00 00 00       	mov    $0x1,%edi
    11de:	41 55                	push   %r13
    11e0:	41 54                	push   %r12
    11e2:	55                   	push   %rbp
    11e3:	53                   	push   %rbx
    11e4:	48 83 ec 68          	sub    $0x68,%rsp
    11e8:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    11f1:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    11f6:	31 c0                	xor    %eax,%eax
    11f8:	e8 73 ff ff ff       	call   1170 <__printf_chk@plt>
    11fd:	ba 01 00 00 00       	mov    $0x1,%edx
    1202:	48 8d 35 53 0e 00 00 	lea    0xe53(%rip),%rsi        # 205c <_IO_stdin_used+0x5c>
    1209:	31 c0                	xor    %eax,%eax
    120b:	bf 01 00 00 00       	mov    $0x1,%edi
    1210:	e8 5b ff ff ff       	call   1170 <__printf_chk@plt>
    1215:	ba 02 00 00 00       	mov    $0x2,%edx
    121a:	48 8d 35 4b 0e 00 00 	lea    0xe4b(%rip),%rsi        # 206c <_IO_stdin_used+0x6c>
    1221:	31 c0                	xor    %eax,%eax
    1223:	bf 01 00 00 00       	mov    $0x1,%edi
    1228:	e8 43 ff ff ff       	call   1170 <__printf_chk@plt>
    122d:	ba 01 00 00 00       	mov    $0x1,%edx
    1232:	48 8d 35 45 0e 00 00 	lea    0xe45(%rip),%rsi        # 207e <_IO_stdin_used+0x7e>
    1239:	31 c0                	xor    %eax,%eax
    123b:	bf 01 00 00 00       	mov    $0x1,%edi
    1240:	e8 2b ff ff ff       	call   1170 <__printf_chk@plt>
    1245:	ba 03 00 00 00       	mov    $0x3,%edx
    124a:	48 8d 35 3f 0e 00 00 	lea    0xe3f(%rip),%rsi        # 2090 <_IO_stdin_used+0x90>
    1251:	31 c0                	xor    %eax,%eax
    1253:	bf 01 00 00 00       	mov    $0x1,%edi
    1258:	e8 13 ff ff ff       	call   1170 <__printf_chk@plt>
  int group_size = writers_count + other_count;
  printf("Readers count %d\n", other_count);
  printf("Writers count %d\n", writers_count);
  int thread_count = groups * (other_count + writers_count);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    125d:	be 80 02 00 00       	mov    $0x280,%esi
    1262:	bf 03 00 00 00       	mov    $0x3,%edi
    1267:	e8 f4 fe ff ff       	call   1160 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    126c:	be 38 00 00 00       	mov    $0x38,%esi
    1271:	bf 03 00 00 00       	mov    $0x3,%edi
    1276:	66 48 0f 6e c8       	movq   %rax,%xmm1
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    127b:	48 89 c3             	mov    %rax,%rbx
    127e:	66 0f 6c c9          	punpcklqdq %xmm1,%xmm1
    1282:	0f 29 0c 24          	movaps %xmm1,(%rsp)
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1286:	e8 d5 fe ff ff       	call   1160 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    128b:	be 08 00 00 00       	mov    $0x8,%esi
    1290:	bf 03 00 00 00       	mov    $0x3,%edi
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    1295:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    129a:	e8 c1 fe ff ff       	call   1160 <calloc@plt>
    129f:	31 d2                	xor    %edx,%edx
    12a1:	bf 01 00 00 00       	mov    $0x1,%edi
    12a6:	48 8d 35 fa 0d 00 00 	lea    0xdfa(%rip),%rsi        # 20a7 <_IO_stdin_used+0xa7>
    12ad:	49 89 c5             	mov    %rax,%r13
    12b0:	31 c0                	xor    %eax,%eax
    12b2:	e8 b9 fe ff ff       	call   1170 <__printf_chk@plt>
    12b7:	48 8d 3d f4 0d 00 00 	lea    0xdf4(%rip),%rdi        # 20b2 <_IO_stdin_used+0xb2>
    12be:	e8 4d fe ff ff       	call   1110 <puts@plt>
    int receiver2 = receiver + 1; 
    int seq[] = {1, 2, 5};
    int tag_index[] = {1, 5, 7};
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
      printf("CREATE SENDER THREAD\n");
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12c3:	be 80 00 00 00       	mov    $0x80,%esi
    12c8:	bf 01 00 00 00       	mov    $0x1,%edi
    12cd:	e8 8e fe ff ff       	call   1160 <calloc@plt>
    12d2:	31 c9                	xor    %ecx,%ecx
    12d4:	31 d2                	xor    %edx,%edx
    12d6:	48 8d 35 b3 0e 00 00 	lea    0xeb3(%rip),%rsi        # 2190 <_IO_stdin_used+0x190>
      CPU_ZERO(sendercpu);
      CPU_SET(curcpu, sendercpu);
    12dd:	48 83 08 01          	orq    $0x1,(%rax)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12e1:	48 89 c5             	mov    %rax,%rbp
    12e4:	bf 01 00 00 00       	mov    $0x1,%edi
    12e9:	31 c0                	xor    %eax,%eax
    12eb:	e8 80 fe ff ff       	call   1170 <__printf_chk@plt>
      printf("assigning sender %d to core %d\n", n, curcpu);
      curcpu += coreinterval;
       
      thread_data[n].thread_index = n;
    12f0:	c7 03 00 00 00 00    	movl   $0x0,(%rbx)
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].thread_tag = tag_index[sender_index];
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    12f6:	be 08 00 00 00       	mov    $0x8,%esi
    12fb:	bf 02 00 00 00       	mov    $0x2,%edi
      thread_data[n].cpu_set = sendercpu;
    1300:	48 89 ab a0 01 00 00 	mov    %rbp,0x1a0(%rbx)
      thread_data[n].mode = WRITER;
    1307:	c7 83 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rbx)
      thread_data[n].multiple = seq[sender_index % writers_count];
    1311:	c7 83 10 02 00 00 01 00 00 00 	movl   $0x1,0x210(%rbx)
      thread_data[n].running = 1;
    131b:	c7 83 98 01 00 00 01 00 00 00 	movl   $0x1,0x198(%rbx)
      thread_data[n].size = buffer_size;
    1325:	48 c7 83 90 01 00 00 00 80 00 00 	movq   $0x8000,0x190(%rbx)
      thread_data[n].thread_tag = tag_index[sender_index];
    1330:	c7 83 14 02 00 00 01 00 00 00 	movl   $0x1,0x214(%rbx)
      thread_data[n].end = 0;
    133a:	c7 83 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbx)
      thread_data[n].sender = &thread_data[sender];
    1344:	48 89 5b 08          	mov    %rbx,0x8(%rbx)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1348:	e8 13 fe ff ff       	call   1160 <calloc@plt>
      if (n == sender) {
        thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    134d:	be 00 02 00 00       	mov    $0x200,%esi
    1352:	bf 00 80 00 00       	mov    $0x8000,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1357:	48 89 83 00 02 00 00 	mov    %rax,0x200(%rbx)
        thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    135e:	e8 fd fd ff ff       	call   1160 <calloc@plt>
    1363:	48 89 43 18          	mov    %rax,0x18(%rbx)
    1367:	49 89 c4             	mov    %rax,%r12
        for (int k = 0 ; k < buffer_size ; k++) {
    136a:	48 8d a8 80 00 00 00 	lea    0x80(%rax),%rbp
    1371:	49 81 c4 80 00 00 01 	add    $0x1000080,%r12
    1378:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1380:	be 04 00 00 00       	mov    $0x4,%esi
    1385:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int k = 0 ; k < buffer_size ; k++) {
    138a:	48 81 c5 00 02 00 00 	add    $0x200,%rbp
          thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1391:	e8 ca fd ff ff       	call   1160 <calloc@plt>
          thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    1396:	be 10 00 00 00       	mov    $0x10,%esi
    139b:	bf 02 00 00 00       	mov    $0x2,%edi
          thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    13a0:	48 89 85 80 fe ff ff 	mov    %rax,-0x180(%rbp)
          thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    13a7:	e8 b4 fd ff ff       	call   1160 <calloc@plt>
          thread_data[n].data[k].written = 0;
    13ac:	c7 85 00 ff ff ff 00 00 00 00 	movl   $0x0,-0x100(%rbp)
          thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
    13b6:	48 89 85 00 fe ff ff 	mov    %rax,-0x200(%rbp)
        for (int k = 0 ; k < buffer_size ; k++) {
    13bd:	49 39 ec             	cmp    %rbp,%r12
    13c0:	75 be                	jne    1380 <main+0x1c0>
    13c2:	31 d2                	xor    %edx,%edx
    13c4:	48 8d 35 fc 0c 00 00 	lea    0xcfc(%rip),%rsi        # 20c7 <_IO_stdin_used+0xc7>
    13cb:	bf 01 00 00 00       	mov    $0x1,%edi
    13d0:	31 c0                	xor    %eax,%eax
    13d2:	4c 8d 3d d7 0d 00 00 	lea    0xdd7(%rip),%r15        # 21b0 <_IO_stdin_used+0x1b0>
    13d9:	4c 8d 35 f8 0d 00 00 	lea    0xdf8(%rip),%r14        # 21d8 <_IO_stdin_used+0x1d8>
        }
      }
      thread_data[n].other_count = other_count;
    13e0:	c7 83 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%rbx)
    }

    printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      thread_data[j].thread_index = j;
    13ea:	48 8d ab 80 02 00 00 	lea    0x280(%rbx),%rbp
    13f1:	e8 7a fd ff ff       	call   1170 <__printf_chk@plt>
      thread_data[j].reader_index = receiver_index;
      thread_data[j].multiple = receiver_index % other_count;
      thread_data[j].other_count = other_count;
     
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    13f6:	be 80 00 00 00       	mov    $0x80,%esi
    13fb:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].thread_index = j;
    1400:	c7 83 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rbx)
      thread_data[j].multiple = receiver_index % other_count;
    140a:	c7 83 90 04 00 00 00 00 00 00 	movl   $0x0,0x490(%rbx)
      thread_data[j].other_count = other_count;
    1414:	48 c7 83 88 04 00 00 02 00 00 00 	movq   $0x2,0x488(%rbx)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    141f:	e8 3c fd ff ff       	call   1160 <calloc@plt>
    1424:	4c 89 fe             	mov    %r15,%rsi
    1427:	b9 02 00 00 00       	mov    $0x2,%ecx
    142c:	ba 01 00 00 00       	mov    $0x1,%edx
      CPU_ZERO(receivercpu);
      CPU_SET(curcpu, receivercpu);
    1431:	48 83 08 04          	orq    $0x4,(%rax)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    1435:	49 89 c4             	mov    %rax,%r12
    1438:	bf 01 00 00 00       	mov    $0x1,%edi
    143d:	31 c0                	xor    %eax,%eax
    143f:	e8 2c fd ff ff       	call   1170 <__printf_chk@plt>
      } */
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    1444:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    144b:	31 c9                	xor    %ecx,%ecx
    144d:	31 d2                	xor    %edx,%edx
      thread_data[j].sender = &thread_data[sender];
    144f:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
    1454:	4c 89 f6             	mov    %r14,%rsi
      thread_data[j].cpu_set = receivercpu;
    1457:	4c 89 a3 20 04 00 00 	mov    %r12,0x420(%rbx)
    145e:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].running = 1;
    1463:	c7 83 18 04 00 00 01 00 00 00 	movl   $0x1,0x418(%rbx)
      thread_data[j].readers = thread_data[sender].readers;
    146d:	48 89 83 80 04 00 00 	mov    %rax,0x480(%rbx)
    1474:	31 c0                	xor    %eax,%eax
      thread_data[j].mode = READER;
    1476:	c7 83 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rbx)
      thread_data[j].size = buffer_size;
    1480:	48 c7 83 10 04 00 00 00 80 00 00 	movq   $0x8000,0x410(%rbx)
      thread_data[j].start = 0;
    148b:	c7 83 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rbx)
      thread_data[j].other_count = other_count;
    1495:	c7 83 88 04 00 00 02 00 00 00 	movl   $0x2,0x488(%rbx)
      thread_data[j].sender = &thread_data[sender];
    149f:	0f 11 93 88 02 00 00 	movups %xmm2,0x288(%rbx)
    14a6:	e8 c5 fc ff ff       	call   1170 <__printf_chk@plt>
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    14ab:	be 80 00 00 00       	mov    $0x80,%esi
    14b0:	bf 01 00 00 00       	mov    $0x1,%edi
      // printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        printf("assigned reader %d to sender %d\n", receiver_index, n);
        thread_data[n].readers[receiver_index] = &thread_data[j];
    14b5:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    14bc:	48 89 28             	mov    %rbp,(%rax)
      thread_data[j].other_count = other_count;
    14bf:	48 8b 05 3a 0d 00 00 	mov    0xd3a(%rip),%rax        # 2200 <_IO_stdin_used+0x200>
      thread_data[j].thread_index = j;
    14c6:	c7 83 00 05 00 00 02 00 00 00 	movl   $0x2,0x500(%rbx)
      thread_data[j].multiple = receiver_index % other_count;
    14d0:	c7 83 10 07 00 00 01 00 00 00 	movl   $0x1,0x710(%rbx)
      thread_data[j].other_count = other_count;
    14da:	48 89 83 08 07 00 00 	mov    %rax,0x708(%rbx)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    14e1:	e8 7a fc ff ff       	call   1160 <calloc@plt>
    14e6:	4c 89 fe             	mov    %r15,%rsi
    14e9:	b9 04 00 00 00       	mov    $0x4,%ecx
    14ee:	ba 02 00 00 00       	mov    $0x2,%edx
      CPU_SET(curcpu, receivercpu);
    14f3:	48 83 08 10          	orq    $0x10,(%rax)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    14f7:	49 89 c4             	mov    %rax,%r12
    14fa:	bf 01 00 00 00       	mov    $0x1,%edi
    14ff:	31 c0                	xor    %eax,%eax
    1501:	e8 6a fc ff ff       	call   1170 <__printf_chk@plt>
      thread_data[j].sender = &thread_data[sender];
    1506:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
    150b:	31 c9                	xor    %ecx,%ecx
    150d:	4c 89 f6             	mov    %r14,%rsi
      thread_data[j].readers = thread_data[sender].readers;
    1510:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    1517:	ba 01 00 00 00       	mov    $0x1,%edx
      thread_data[j].running = 1;
    151c:	c7 83 98 06 00 00 01 00 00 00 	movl   $0x1,0x698(%rbx)
    1526:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].cpu_set = receivercpu;
    152b:	4c 89 a3 a0 06 00 00 	mov    %r12,0x6a0(%rbx)
      thread_data[j].readers = thread_data[sender].readers;
    1532:	48 89 83 00 07 00 00 	mov    %rax,0x700(%rbx)
    1539:	31 c0                	xor    %eax,%eax
      thread_data[j].mode = READER;
    153b:	c7 83 88 06 00 00 01 00 00 00 	movl   $0x1,0x688(%rbx)
      thread_data[j].size = buffer_size;
    1545:	48 c7 83 90 06 00 00 00 80 00 00 	movq   $0x8000,0x690(%rbx)
      thread_data[j].start = 0;
    1550:	c7 83 80 05 00 00 00 00 00 00 	movl   $0x0,0x580(%rbx)
      thread_data[j].other_count = other_count;
    155a:	c7 83 08 07 00 00 02 00 00 00 	movl   $0x2,0x708(%rbx)
      thread_data[j].sender = &thread_data[sender];
    1564:	0f 11 93 08 05 00 00 	movups %xmm2,0x508(%rbx)
    156b:	e8 00 fc ff ff       	call   1170 <__printf_chk@plt>
        thread_data[n].readers[receiver_index] = &thread_data[j];
    1570:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
      thread_data[j].thread_index = j;
    1577:	48 8d 93 00 05 00 00 	lea    0x500(%rbx),%rdx
    157e:	48 89 50 08          	mov    %rdx,0x8(%rax)
      }
    }
    curcpu = 0;
    // printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    1582:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    1585:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    158a:	c7 44 24 2c 00 00 00 00 	movl   $0x0,0x2c(%rsp)
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1592:	4d 8d 75 08          	lea    0x8(%r13),%r14
    1596:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    159c:	4c 8d 60 38          	lea    0x38(%rax),%r12
    15a0:	48 8d 35 35 0b 00 00 	lea    0xb35(%rip),%rsi        # 20dc <_IO_stdin_used+0xdc>
    15a7:	bf 01 00 00 00       	mov    $0x1,%edi
    15ac:	31 c0                	xor    %eax,%eax
    15ae:	44 89 fa             	mov    %r15d,%edx
    15b1:	e8 ba fb ff ff       	call   1170 <__printf_chk@plt>
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    15b6:	31 f6                	xor    %esi,%esi
    15b8:	4c 89 e7             	mov    %r12,%rdi
    15bb:	e8 90 fb ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    15c0:	85 c0                	test   %eax,%eax
    15c2:	0f 85 f6 01 00 00    	jne    17be <main+0x5fe>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    15c8:	48 8d 74 24 2c       	lea    0x2c(%rsp),%rsi
    15cd:	4c 89 e7             	mov    %r12,%rdi
    15d0:	e8 bb fb ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    15d5:	85 c0                	test   %eax,%eax
    15d7:	0f 85 fc 01 00 00    	jne    17d9 <main+0x619>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    15dd:	48 89 e9             	mov    %rbp,%rcx
    15e0:	4c 89 e6             	mov    %r12,%rsi
    15e3:	4c 89 f7             	mov    %r14,%rdi
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15e6:	49 83 c4 38          	add    $0x38,%r12
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    15ea:	48 8d 15 ef 02 00 00 	lea    0x2ef(%rip),%rdx        # 18e0 <disruptor_thread>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    15f1:	49 83 c6 08          	add    $0x8,%r14
    15f5:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    15fc:	e8 7f fb ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
    1601:	48 8b 95 20 ff ff ff 	mov    -0xe0(%rbp),%rdx
    1608:	49 8b 7e f8          	mov    -0x8(%r14),%rdi
    160c:	be 08 00 00 00       	mov    $0x8,%esi
    1611:	e8 ea fa ff ff       	call   1100 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1616:	41 83 ff 01          	cmp    $0x1,%r15d
    161a:	75 0b                	jne    1627 <main+0x467>
    161c:	41 bf 02 00 00 00    	mov    $0x2,%r15d
    1622:	e9 79 ff ff ff       	jmp    15a0 <main+0x3e0>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    1627:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
    162c:	31 f6                	xor    %esi,%esi
    162e:	4c 89 ff             	mov    %r15,%rdi
    1631:	e8 1a fb ff ff       	call   1150 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    1636:	85 c0                	test   %eax,%eax
    1638:	0f 85 80 01 00 00    	jne    17be <main+0x5fe>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    163e:	48 8d 74 24 28       	lea    0x28(%rsp),%rsi
    1643:	4c 89 ff             	mov    %r15,%rdi
      param2.sched_priority = 0;
    1646:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    164e:	e8 3d fb ff ff       	call   1190 <pthread_attr_setschedparam@plt>
      if (ret) {
    1653:	85 c0                	test   %eax,%eax
    1655:	0f 85 7e 01 00 00    	jne    17d9 <main+0x619>
    165b:	31 d2                	xor    %edx,%edx
    165d:	48 8d 35 d0 0a 00 00 	lea    0xad0(%rip),%rsi        # 2134 <_IO_stdin_used+0x134>
    1664:	bf 01 00 00 00       	mov    $0x1,%edi
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    1669:	31 ed                	xor    %ebp,%ebp
    166b:	e8 00 fb ff ff       	call   1170 <__printf_chk@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    1670:	48 89 d9             	mov    %rbx,%rcx
    1673:	4c 89 fe             	mov    %r15,%rsi
    1676:	4c 89 ef             	mov    %r13,%rdi
    1679:	48 8d 15 60 02 00 00 	lea    0x260(%rip),%rdx        # 18e0 <disruptor_thread>
    1680:	4c 8d 25 c9 0a 00 00 	lea    0xac9(%rip),%r12        # 2150 <_IO_stdin_used+0x150>
    1687:	e8 f4 fa ff ff       	call   1180 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    168c:	48 8b 93 a0 01 00 00 	mov    0x1a0(%rbx),%rdx
    1693:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    1697:	be 08 00 00 00       	mov    $0x8,%esi
    169c:	e8 5f fa ff ff       	call   1100 <pthread_setaffinity_np@plt>
  nanosleep(&preempt , &rem2);
    16a1:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    16a6:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  struct timespec preempt = {
    16ab:	66 0f 6f 05 5d 0b 00 00 	movdqa 0xb5d(%rip),%xmm0        # 2210 <_IO_stdin_used+0x210>
    16b3:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  nanosleep(&preempt , &rem2);
    16b8:	e8 83 fa ff ff       	call   1140 <nanosleep@plt>
      pthread_join(thread[n], res1);
    16bd:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    16c1:	31 f6                	xor    %esi,%esi
    thread_data[sender].running = 0;
    16c3:	c7 83 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%rbx)
      thread_data[j].running = 0;
    16cd:	c7 83 18 04 00 00 00 00 00 00 	movl   $0x0,0x418(%rbx)
    16d7:	c7 83 98 06 00 00 00 00 00 00 	movl   $0x0,0x698(%rbx)
      thread_data[n].running = 0;
    16e1:	c7 83 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%rbx)
      pthread_join(thread[n], res1);
    16eb:	e8 c0 fa ff ff       	call   11b0 <pthread_join@plt>
      pthread_join(thread[j], res2);
    16f0:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    16f4:	48 89 ee             	mov    %rbp,%rsi
    16f7:	e8 b4 fa ff ff       	call   11b0 <pthread_join@plt>
    16fc:	49 8b 7d 10          	mov    0x10(%r13),%rdi
    1700:	48 89 ee             	mov    %rbp,%rsi
    1703:	e8 a8 fa ff ff       	call   11b0 <pthread_join@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    // printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    1708:	eb 16                	jmp    1720 <main+0x560>
    170a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1710:	48 81 c5 00 02 00 00 	add    $0x200,%rbp
    1717:	48 81 fd 00 00 00 01 	cmp    $0x1000000,%rbp
    171e:	74 7d                	je     179d <main+0x5dd>
      int compcount = 0;
      for (int n = 0 ; n < other_count ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    1720:	48 8b 43 18          	mov    0x18(%rbx),%rax
    1724:	48 01 e8             	add    %rbp,%rax
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
    175f:	48 8b 43 18          	mov    0x18(%rbx),%rax
    1763:	4c 89 e6             	mov    %r12,%rsi
    1766:	bf 01 00 00 00       	mov    $0x1,%edi
    176b:	48 01 e8             	add    %rbp,%rax
    for (int y = 0 ; y < buffer_size; y++) {
    176e:	48 81 c5 00 02 00 00 	add    $0x200,%rbp
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
    1794:	48 81 fd 00 00 00 01 	cmp    $0x1000000,%rbp
    179b:	75 83                	jne    1720 <main+0x560>
    }
    // printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    179d:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    17a2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    17ab:	75 27                	jne    17d4 <main+0x614>
    17ad:	48 83 c4 68          	add    $0x68,%rsp
    17b1:	31 c0                	xor    %eax,%eax
    17b3:	5b                   	pop    %rbx
    17b4:	5d                   	pop    %rbp
    17b5:	41 5c                	pop    %r12
    17b7:	41 5d                	pop    %r13
    17b9:	41 5e                	pop    %r14
    17bb:	41 5f                	pop    %r15
    17bd:	c3                   	ret
    17be:	48 8d 3d 34 09 00 00 	lea    0x934(%rip),%rdi        # 20f9 <_IO_stdin_used+0xf9>
    17c5:	e8 46 f9 ff ff       	call   1110 <puts@plt>
               exit(1);
    17ca:	bf 01 00 00 00       	mov    $0x1,%edi
    17cf:	e8 cc f9 ff ff       	call   11a0 <exit@plt>
}
    17d4:	e8 57 f9 ff ff       	call   1130 <__stack_chk_fail@plt>
    17d9:	48 8d 3d 37 09 00 00 	lea    0x937(%rip),%rdi        # 2117 <_IO_stdin_used+0x117>
    17e0:	e8 2b f9 ff ff       	call   1110 <puts@plt>
              exit(1);
    17e5:	bf 01 00 00 00       	mov    $0x1,%edi
    17ea:	e8 b1 f9 ff ff       	call   11a0 <exit@plt>
    17ef:	90                   	nop

00000000000017f0 <_start>:
    17f0:	f3 0f 1e fa          	endbr64
    17f4:	31 ed                	xor    %ebp,%ebp
    17f6:	49 89 d1             	mov    %rdx,%r9
    17f9:	5e                   	pop    %rsi
    17fa:	48 89 e2             	mov    %rsp,%rdx
    17fd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1801:	50                   	push   %rax
    1802:	54                   	push   %rsp
    1803:	45 31 c0             	xor    %r8d,%r8d
    1806:	31 c9                	xor    %ecx,%ecx
    1808:	48 8d 3d b1 f9 ff ff 	lea    -0x64f(%rip),%rdi        # 11c0 <main>
    180f:	ff 15 c3 27 00 00    	call   *0x27c3(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1815:	f4                   	hlt
    1816:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001820 <deregister_tm_clones>:
    1820:	48 8d 3d e9 27 00 00 	lea    0x27e9(%rip),%rdi        # 4010 <__TMC_END__>
    1827:	48 8d 05 e2 27 00 00 	lea    0x27e2(%rip),%rax        # 4010 <__TMC_END__>
    182e:	48 39 f8             	cmp    %rdi,%rax
    1831:	74 15                	je     1848 <deregister_tm_clones+0x28>
    1833:	48 8b 05 a6 27 00 00 	mov    0x27a6(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    183a:	48 85 c0             	test   %rax,%rax
    183d:	74 09                	je     1848 <deregister_tm_clones+0x28>
    183f:	ff e0                	jmp    *%rax
    1841:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1848:	c3                   	ret
    1849:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001850 <register_tm_clones>:
    1850:	48 8d 3d b9 27 00 00 	lea    0x27b9(%rip),%rdi        # 4010 <__TMC_END__>
    1857:	48 8d 35 b2 27 00 00 	lea    0x27b2(%rip),%rsi        # 4010 <__TMC_END__>
    185e:	48 29 fe             	sub    %rdi,%rsi
    1861:	48 89 f0             	mov    %rsi,%rax
    1864:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1868:	48 c1 f8 03          	sar    $0x3,%rax
    186c:	48 01 c6             	add    %rax,%rsi
    186f:	48 d1 fe             	sar    %rsi
    1872:	74 14                	je     1888 <register_tm_clones+0x38>
    1874:	48 8b 05 75 27 00 00 	mov    0x2775(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    187b:	48 85 c0             	test   %rax,%rax
    187e:	74 08                	je     1888 <register_tm_clones+0x38>
    1880:	ff e0                	jmp    *%rax
    1882:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1888:	c3                   	ret
    1889:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001890 <__do_global_dtors_aux>:
    1890:	f3 0f 1e fa          	endbr64
    1894:	80 3d 75 27 00 00 00 	cmpb   $0x0,0x2775(%rip)        # 4010 <__TMC_END__>
    189b:	75 2b                	jne    18c8 <__do_global_dtors_aux+0x38>
    189d:	55                   	push   %rbp
    189e:	48 83 3d 52 27 00 00 00 	cmpq   $0x0,0x2752(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    18a6:	48 89 e5             	mov    %rsp,%rbp
    18a9:	74 0c                	je     18b7 <__do_global_dtors_aux+0x27>
    18ab:	48 8b 3d 56 27 00 00 	mov    0x2756(%rip),%rdi        # 4008 <__dso_handle>
    18b2:	e8 39 f8 ff ff       	call   10f0 <__cxa_finalize@plt>
    18b7:	e8 64 ff ff ff       	call   1820 <deregister_tm_clones>
    18bc:	c6 05 4d 27 00 00 01 	movb   $0x1,0x274d(%rip)        # 4010 <__TMC_END__>
    18c3:	5d                   	pop    %rbp
    18c4:	c3                   	ret
    18c5:	0f 1f 00             	nopl   (%rax)
    18c8:	c3                   	ret
    18c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018d0 <frame_dummy>:
    18d0:	f3 0f 1e fa          	endbr64
    18d4:	e9 77 ff ff ff       	jmp    1850 <register_tm_clones>
    18d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000018e0 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    18e0:	f3 0f 1e fa          	endbr64
    18e4:	41 56                	push   %r14
    18e6:	41 55                	push   %r13
    18e8:	41 54                	push   %r12
    18ea:	55                   	push   %rbp
    18eb:	53                   	push   %rbx
  if (data->mode == WRITER) {
    18ec:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
void * disruptor_thread(void * arg) {
    18f2:	48 89 fb             	mov    %rdi,%rbx
  if (data->mode == WRITER) {
    18f5:	85 c0                	test   %eax,%eax
    18f7:	74 1a                	je     1913 <disruptor_thread+0x33>
  } else if (data->mode == READER) {
    18f9:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
    18ff:	83 f8 01             	cmp    $0x1,%eax
    1902:	0f 84 5b 01 00 00    	je     1a63 <disruptor_thread+0x183>
}
    1908:	5b                   	pop    %rbx
    1909:	31 c0                	xor    %eax,%eax
    190b:	5d                   	pop    %rbp
    190c:	41 5c                	pop    %r12
    190e:	41 5d                	pop    %r13
    1910:	41 5e                	pop    %r14
    1912:	c3                   	ret
    1913:	8b 17                	mov    (%rdi),%edx
    1915:	48 8d 35 e8 06 00 00 	lea    0x6e8(%rip),%rsi        # 2004 <_IO_stdin_used+0x4>
    191c:	bf 01 00 00 00       	mov    $0x1,%edi
    1921:	e8 4a f8 ff ff       	call   1170 <__printf_chk@plt>
    struct Thread *me = data->sender;
    1926:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
    192a:	bf 01 00 00 00       	mov    $0x1,%edi
    192f:	31 c0                	xor    %eax,%eax
    1931:	48 8d 35 dc 06 00 00 	lea    0x6dc(%rip),%rsi        # 2014 <_IO_stdin_used+0x14>
    1938:	48 8b 55 18          	mov    0x18(%rbp),%rdx
    193c:	e8 2f f8 ff ff       	call   1170 <__printf_chk@plt>
    while (data->running == 1) {
    1941:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1948:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    194e:	83 f8 01             	cmp    $0x1,%eax
    1951:	75 b5                	jne    1908 <disruptor_thread+0x28>
      asm volatile ("sfence" ::: "memory");
    1953:	0f ae f8             	sfence
      long pos = (((me->realend & END_MASK) >> 32) + 1) % data->size;
    1956:	4c 8b 8d 80 01 00 00 	mov    0x180(%rbp),%r9
      for (int x  = 0 ; x < data->other_count; x++) {
    195d:	48 63 b3 08 02 00 00 	movslq 0x208(%rbx),%rsi
      long pos = (((me->realend & END_MASK) >> 32) + 1) % data->size;
    1964:	4d 89 c8             	mov    %r9,%r8
    1967:	49 c1 f8 20          	sar    $0x20,%r8
    196b:	41 81 e0 ff ff ff 0f 	and    $0xfffffff,%r8d
    1972:	49 8d 40 01          	lea    0x1(%r8),%rax
    1976:	48 99                	cqto
    1978:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
      for (int x  = 0 ; x < data->other_count; x++) {
    197f:	85 f6                	test   %esi,%esi
    1981:	0f 8e bc 00 00 00    	jle    1a43 <disruptor_thread+0x163>
    1987:	48 8b 8b 00 02 00 00 	mov    0x200(%rbx),%rcx
    198e:	48 8d 3c f1          	lea    (%rcx,%rsi,8),%rdi
    1992:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (pos == data->readers[x]->start) {
    1998:	48 8b 31             	mov    (%rcx),%rsi
    199b:	48 63 b6 80 00 00 00 	movslq 0x80(%rsi),%rsi
    19a2:	48 39 d6             	cmp    %rdx,%rsi
    19a5:	74 a1                	je     1948 <disruptor_thread+0x68>
      for (int x  = 0 ; x < data->other_count; x++) {
    19a7:	48 83 c1 08          	add    $0x8,%rcx
    19ab:	48 39 cf             	cmp    %rcx,%rdi
    19ae:	75 e8                	jne    1998 <disruptor_thread+0xb8>
              changed = (((original & END_MASK) >> 32)) % me->size;
    19b0:	4c 89 c0             	mov    %r8,%rax
    19b3:	48 99                	cqto
    19b5:	48 f7 bd 90 01 00 00 	idivq  0x190(%rbp)
              long new = (data->thread_tag) | ((changed + 1) << 32);
    19bc:	48 63 83 14 02 00 00 	movslq 0x214(%rbx),%rax
    19c3:	48 8d 4a 01          	lea    0x1(%rdx),%rcx
    19c7:	48 c1 e1 20          	shl    $0x20,%rcx
    19cb:	48 09 c1             	or     %rax,%rcx
                me->data[changed].complete[x] = 0;
    19ce:	48 89 d0             	mov    %rdx,%rax
    19d1:	48 c1 e0 09          	shl    $0x9,%rax
    19d5:	48 03 45 18          	add    0x18(%rbp),%rax
    19d9:	48 8b b0 00 01 00 00 	mov    0x100(%rax),%rsi
    19e0:	31 c0                	xor    %eax,%eax
    19e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    19e8:	c7 04 86 00 00 00 00 	movl   $0x0,(%rsi,%rax,4)
              for (int x = 0 ; x < data->other_count; x++) {
    19ef:	48 83 c0 01          	add    $0x1,%rax
    19f3:	39 83 08 02 00 00    	cmp    %eax,0x208(%rbx)
    19f9:	7f ed                	jg     19e8 <disruptor_thread+0x108>
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED))) {
    19fb:	48 8d b5 80 01 00 00 	lea    0x180(%rbp),%rsi
    1a02:	4c 89 c8             	mov    %r9,%rax
    1a05:	f0 48 0f b1 0e       	lock cmpxchg %rcx,(%rsi)
    1a0a:	0f 85 2f 01 00 00    	jne    1b3f <disruptor_thread+0x25f>
                clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
    1a10:	48 8b 75 18          	mov    0x18(%rbp),%rsi
    1a14:	48 c1 e2 09          	shl    $0x9,%rdx
    1a18:	bf 04 00 00 00       	mov    $0x4,%edi
    1a1d:	49 89 d4             	mov    %rdx,%r12
    1a20:	48 01 d6             	add    %rdx,%rsi
    1a23:	e8 f8 f6 ff ff       	call   1120 <clock_gettime@plt>
                __atomic_store_n(&me->sender->data[changed].written, me->other_count, __ATOMIC_SEQ_CST);
    1a28:	48 8b 45 08          	mov    0x8(%rbp),%rax
    1a2c:	48 8b 50 18          	mov    0x18(%rax),%rdx
    1a30:	8b 85 08 02 00 00    	mov    0x208(%rbp),%eax
    1a36:	42 87 84 22 80 01 00 00 	xchg   %eax,0x180(%rdx,%r12,1)
    1a3e:	e9 05 ff ff ff       	jmp    1948 <disruptor_thread+0x68>
              changed = (((original & END_MASK) >> 32)) % me->size;
    1a43:	4c 89 c0             	mov    %r8,%rax
    1a46:	48 99                	cqto
    1a48:	48 f7 bd 90 01 00 00 	idivq  0x190(%rbp)
              long new = (data->thread_tag) | ((changed + 1) << 32);
    1a4f:	48 63 83 14 02 00 00 	movslq 0x214(%rbx),%rax
    1a56:	48 8d 4a 01          	lea    0x1(%rdx),%rcx
    1a5a:	48 c1 e1 20          	shl    $0x20,%rcx
    1a5e:	48 09 c1             	or     %rax,%rcx
              for (int x = 0 ; x < data->other_count; x++) {
    1a61:	eb 98                	jmp    19fb <disruptor_thread+0x11b>
    1a63:	8b 97 0c 02 00 00    	mov    0x20c(%rdi),%edx
    1a69:	48 8d 35 c0 05 00 00 	lea    0x5c0(%rip),%rsi        # 2030 <_IO_stdin_used+0x30>
    1a70:	bf 01 00 00 00       	mov    $0x1,%edi
    1a75:	31 c0                	xor    %eax,%eax
    1a77:	e8 f4 f6 ff ff       	call   1170 <__printf_chk@plt>
    struct Thread *sender = data->sender;
    1a7c:	4c 8b 6b 08          	mov    0x8(%rbx),%r13
    1a80:	bf 01 00 00 00       	mov    $0x1,%edi
    1a85:	31 c0                	xor    %eax,%eax
    1a87:	48 8d 35 b2 05 00 00 	lea    0x5b2(%rip),%rsi        # 2040 <_IO_stdin_used+0x40>
    struct Snapshot * rdata = sender->data;
    1a8e:	4d 8b 65 18          	mov    0x18(%r13),%r12
    1a92:	4c 89 e2             	mov    %r12,%rdx
    1a95:	e8 d6 f6 ff ff       	call   1170 <__printf_chk@plt>
    while (data->running == 1) {
    1a9a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1aa0:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    1aa6:	83 f8 01             	cmp    $0x1,%eax
    1aa9:	0f 85 59 fe ff ff    	jne    1908 <disruptor_thread+0x28>
      int pos = ((__atomic_load_n(&sender->realend, __ATOMIC_SEQ_CST) & END_MASK) >> 32);
    1aaf:	49 8b 85 80 01 00 00 	mov    0x180(%r13),%rax
    1ab6:	48 c1 f8 20          	sar    $0x20,%rax
    1aba:	25 ff ff ff 0f       	and    $0xfffffff,%eax
      if (pos == data->start) {
    1abf:	8b ab 80 00 00 00    	mov    0x80(%rbx),%ebp
    1ac5:	39 c5                	cmp    %eax,%ebp
    1ac7:	74 d7                	je     1aa0 <disruptor_thread+0x1c0>
          int written = __atomic_load_n(&rdata[changed].written, __ATOMIC_SEQ_CST);
    1ac9:	4c 63 f5             	movslq %ebp,%r14
    1acc:	49 c1 e6 09          	shl    $0x9,%r14
    1ad0:	4d 01 e6             	add    %r12,%r14
    1ad3:	41 8b 86 80 01 00 00 	mov    0x180(%r14),%eax
          if (written > 0) {
    1ada:	85 c0                	test   %eax,%eax
    1adc:	7e c2                	jle    1aa0 <disruptor_thread+0x1c0>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1ade:	48 63 b3 0c 02 00 00 	movslq 0x20c(%rbx),%rsi
    1ae5:	bf 04 00 00 00       	mov    $0x4,%edi
    1aea:	48 c1 e6 04          	shl    $0x4,%rsi
    1aee:	49 03 b6 80 00 00 00 	add    0x80(%r14),%rsi
    1af5:	e8 26 f6 ff ff       	call   1120 <clock_gettime@plt>
              rdata[changed].complete[data->reader_index] = 1;
    1afa:	49 8b 86 00 01 00 00 	mov    0x100(%r14),%rax
    1b01:	48 63 93 0c 02 00 00 	movslq 0x20c(%rbx),%rdx
    1b08:	c7 04 90 01 00 00 00 	movl   $0x1,(%rax,%rdx,4)
              data->start = (changed + 1) % data->size;
    1b0f:	8d 45 01             	lea    0x1(%rbp),%eax
    1b12:	48 98                	cltq
    1b14:	48 99                	cqto
    1b16:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
    1b1d:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
              __atomic_sub_fetch(&rdata[changed].written, 1, __ATOMIC_SEQ_CST);
    1b23:	f0 41 83 ae 80 01 00 00 01 	lock subl $0x1,0x180(%r14)
    1b2c:	e9 6f ff ff ff       	jmp    1aa0 <disruptor_thread+0x1c0>
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED))) {
    1b31:	4c 89 c0             	mov    %r8,%rax
    1b34:	f0 48 0f b1 0e       	lock cmpxchg %rcx,(%rsi)
    1b39:	0f 84 d1 fe ff ff    	je     1a10 <disruptor_thread+0x130>
                original = me->realend;
    1b3f:	4c 8b 85 80 01 00 00 	mov    0x180(%rbp),%r8
                changed = (((original & END_MASK) >> 32)) % me->size;
    1b46:	4c 89 c0             	mov    %r8,%rax
    1b49:	48 c1 f8 20          	sar    $0x20,%rax
    1b4d:	25 ff ff ff 0f       	and    $0xfffffff,%eax
    1b52:	48 99                	cqto
    1b54:	48 f7 bd 90 01 00 00 	idivq  0x190(%rbp)
                new = (data->thread_tag) | ((changed + 1) << 32);
    1b5b:	48 63 83 14 02 00 00 	movslq 0x214(%rbx),%rax
    1b62:	48 8d 4a 01          	lea    0x1(%rdx),%rcx
    1b66:	48 c1 e1 20          	shl    $0x20,%rcx
    1b6a:	48 09 c1             	or     %rax,%rcx
                for (int x = 0 ; x < data->other_count; x++) {
    1b6d:	83 bb 08 02 00 00 00 	cmpl   $0x0,0x208(%rbx)
    1b74:	7e bb                	jle    1b31 <disruptor_thread+0x251>
                  me->data[changed].complete[x] = 0;
    1b76:	48 89 d0             	mov    %rdx,%rax
    1b79:	31 ff                	xor    %edi,%edi
    1b7b:	48 c1 e0 09          	shl    $0x9,%rax
    1b7f:	48 03 45 18          	add    0x18(%rbp),%rax
    1b83:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
    1b8a:	c7 04 b8 00 00 00 00 	movl   $0x0,(%rax,%rdi,4)
                for (int x = 0 ; x < data->other_count; x++) {
    1b91:	48 83 c7 01          	add    $0x1,%rdi
    1b95:	39 bb 08 02 00 00    	cmp    %edi,0x208(%rbx)
    1b9b:	7f ed                	jg     1b8a <disruptor_thread+0x2aa>
    1b9d:	eb 92                	jmp    1b31 <disruptor_thread+0x251>
    1b9f:	90                   	nop

0000000000001ba0 <min>:
int min(long a, long b) {
    1ba0:	f3 0f 1e fa          	endbr64
  if (a < b) return a;
    1ba4:	48 39 f7             	cmp    %rsi,%rdi
    1ba7:	7c 02                	jl     1bab <min+0xb>
  if (b < a) return b;
    1ba9:	7f 05                	jg     1bb0 <min+0x10>
  if (a < b) return a;
    1bab:	89 f8                	mov    %edi,%eax
    1bad:	c3                   	ret
    1bae:	66 90                	xchg   %ax,%ax
  if (b < a) return b;
    1bb0:	89 f0                	mov    %esi,%eax
}
    1bb2:	c3                   	ret

Disassembly of section .fini:

0000000000001bb4 <_fini>:
    1bb4:	f3 0f 1e fa          	endbr64
    1bb8:	48 83 ec 08          	sub    $0x8,%rsp
    1bbc:	48 83 c4 08          	add    $0x8,%rsp
    1bc0:	c3                   	ret
