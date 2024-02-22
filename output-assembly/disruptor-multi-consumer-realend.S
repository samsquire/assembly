
disruptor-multi-consumer-realend:     file format elf64-x86-64


Disassembly of section .init:

0000000000001000 <_init>:
    1000:	f3 0f 1e fa          	endbr64
    1004:	48 83 ec 08          	sub    $0x8,%rsp
    1008:	48 8d 05 a1 08 00 00 	lea    0x8a1(%rip),%rax        # 18b0 <__gmon_start__>
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
  printf("Finished %d\n", data->mode);
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
    1211:	48 83 ec 78          	sub    $0x78,%rsp
    1215:	ff 15 cd 2d 00 00    	call   *0x2dcd(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    121b:	b9 00 04 00 00       	mov    $0x400,%ecx
    1220:	ba 0a 00 00 00       	mov    $0xa,%edx
    1225:	bf 01 00 00 00       	mov    $0x1,%edi
    122a:	48 8d 35 ff 0d 00 00 	lea    0xdff(%rip),%rsi        # 2030 <_IO_stdin_used+0x30>
    1231:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    123a:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    123e:	31 c0                	xor    %eax,%eax
    1240:	e8 5b ff ff ff       	call   11a0 <__printf_chk@plt>
    1245:	ba 01 00 00 00       	mov    $0x1,%edx
    124a:	48 8d 35 59 0e 00 00 	lea    0xe59(%rip),%rsi        # 20aa <_IO_stdin_used+0xaa>
    1251:	31 c0                	xor    %eax,%eax
    1253:	bf 01 00 00 00       	mov    $0x1,%edi
    1258:	e8 43 ff ff ff       	call   11a0 <__printf_chk@plt>
    125d:	ba 02 00 00 00       	mov    $0x2,%edx
    1262:	48 8d 35 51 0e 00 00 	lea    0xe51(%rip),%rsi        # 20ba <_IO_stdin_used+0xba>
    1269:	31 c0                	xor    %eax,%eax
    126b:	bf 01 00 00 00       	mov    $0x1,%edi
    1270:	e8 2b ff ff ff       	call   11a0 <__printf_chk@plt>
    1275:	ba 04 00 00 00       	mov    $0x4,%edx
    127a:	48 8d 35 4b 0e 00 00 	lea    0xe4b(%rip),%rsi        # 20cc <_IO_stdin_used+0xcc>
    1281:	31 c0                	xor    %eax,%eax
    1283:	bf 01 00 00 00       	mov    $0x1,%edi
    1288:	e8 13 ff ff ff       	call   11a0 <__printf_chk@plt>
  int other_count = 2;
  int group_size = writers_count + other_count;
  printf("Readers count %d\n", other_count);
  int thread_count = groups * (other_count + writers_count);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    128d:	be 80 02 00 00       	mov    $0x280,%esi
    1292:	bf 04 00 00 00       	mov    $0x4,%edi
    1297:	e8 e4 fe ff ff       	call   1180 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    129c:	be 38 00 00 00       	mov    $0x38,%esi
    12a1:	bf 04 00 00 00       	mov    $0x4,%edi
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
    12a6:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12a9:	e8 d2 fe ff ff       	call   1180 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12ae:	be 08 00 00 00       	mov    $0x8,%esi
    12b3:	bf 04 00 00 00       	mov    $0x4,%edi
    12b8:	49 89 de             	mov    %rbx,%r14
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
    12bb:	48 89 45 80          	mov    %rax,-0x80(%rbp)
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12bf:	e8 bc fe ff ff       	call   1180 <calloc@plt>
  // 0, 3, 6
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int receiver2 = receiver + 1; 
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12c4:	be 80 00 00 00       	mov    $0x80,%esi
    12c9:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
    12ce:	49 89 c4             	mov    %rax,%r12
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12d1:	e8 aa fe ff ff       	call   1180 <calloc@plt>
    CPU_ZERO(receivercpu);
    for (int j = 0; j < cores; j++) {
      // printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    }
    for (int n = sender; n < sender + writers_count; n++) {
    12d6:	c7 45 88 00 00 00 00 	movl   $0x0,-0x78(%rbp)
      CPU_SET(j, receivercpu);
    12dd:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    12e4:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    12eb:	be 80 00 00 00       	mov    $0x80,%esi
    12f0:	bf 01 00 00 00       	mov    $0x1,%edi
    12f5:	e8 86 fe ff ff       	call   1180 <calloc@plt>
      for (int j = 0 ; j < cores ; j++) {
        // printf("assigning sender %d to core %d\n", sender, j);
        CPU_SET(j, sendercpu);
      }
       
      thread_data[n].thread_index = n;
    12fa:	8b 4d 88             	mov    -0x78(%rbp),%ecx
      thread_data[n].cpu_set = sendercpu;
      thread_data[n].mode = WRITER;
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
    12fd:	49 89 5e 08          	mov    %rbx,0x8(%r14)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1301:	be 08 00 00 00       	mov    $0x8,%esi
        CPU_SET(j, sendercpu);
    1306:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    130d:	bf 02 00 00 00       	mov    $0x2,%edi
      thread_data[n].thread_index = n;
    1312:	41 89 0e             	mov    %ecx,(%r14)
      thread_data[n].mode = WRITER;
    1315:	41 c7 86 84 01 00 00 00 00 00 00 	movl   $0x0,0x184(%r14)
      thread_data[n].cpu_set = sendercpu;
    1320:	49 89 86 98 01 00 00 	mov    %rax,0x198(%r14)
      thread_data[n].running = 1;
    1327:	41 c7 86 90 01 00 00 01 00 00 00 	movl   $0x1,0x190(%r14)
      thread_data[n].size = buffer_size;
    1332:	49 c7 86 88 01 00 00 00 04 00 00 	movq   $0x400,0x188(%r14)
      thread_data[n].end = 0;
    133d:	41 c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r14)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1348:	e8 33 fe ff ff       	call   1180 <calloc@plt>
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    134d:	be 80 01 00 00       	mov    $0x180,%esi
    1352:	bf 00 04 00 00       	mov    $0x400,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
    1357:	49 89 86 00 02 00 00 	mov    %rax,0x200(%r14)
      thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
    135e:	e8 1d fe ff ff       	call   1180 <calloc@plt>
    1363:	49 89 46 18          	mov    %rax,0x18(%r14)
      for (int k = 0 ; k < buffer_size ; k++) {
    1367:	4c 8d b8 80 00 00 00 	lea    0x80(%rax),%r15
    136e:	4c 8d a8 80 00 06 00 	lea    0x60080(%rax),%r13
    1375:	0f 1f 00             	nopl   (%rax)
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1378:	be 04 00 00 00       	mov    $0x4,%esi
    137d:	bf 02 00 00 00       	mov    $0x2,%edi
      for (int k = 0 ; k < buffer_size ; k++) {
    1382:	49 81 c7 80 01 00 00 	add    $0x180,%r15
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1389:	e8 f2 fd ff ff       	call   1180 <calloc@plt>
        thread_data[n].data[k].end = calloc(other_count, sizeof(int));
    138e:	be 04 00 00 00       	mov    $0x4,%esi
    1393:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
    1398:	49 89 87 00 ff ff ff 	mov    %rax,-0x100(%r15)
        thread_data[n].data[k].end = calloc(other_count, sizeof(int));
    139f:	e8 dc fd ff ff       	call   1180 <calloc@plt>
    13a4:	49 89 87 80 fe ff ff 	mov    %rax,-0x180(%r15)
      for (int k = 0 ; k < buffer_size ; k++) {
    13ab:	4d 39 ef             	cmp    %r13,%r15
    13ae:	75 c8                	jne    1378 <main+0x178>
    for (int n = sender; n < sender + writers_count; n++) {
    13b0:	8b 45 88             	mov    -0x78(%rbp),%eax
    13b3:	49 81 c6 80 02 00 00 	add    $0x280,%r14
      }
      thread_data[n].other_count = other_count;
    13ba:	41 c7 46 88 02 00 00 00 	movl   $0x2,-0x78(%r14)
    for (int n = sender; n < sender + writers_count; n++) {
    13c2:	85 c0                	test   %eax,%eax
    13c4:	75 0c                	jne    13d2 <main+0x1d2>
    13c6:	c7 45 88 01 00 00 00 	movl   $0x1,-0x78(%rbp)
    13cd:	e9 19 ff ff ff       	jmp    12eb <main+0xeb>
    13d2:	66 48 0f 6e d3       	movq   %rbx,%xmm2
    13d7:	48 8d 83 00 05 00 00 	lea    0x500(%rbx),%rax
    13de:	66 0f 6c d2          	punpcklqdq %xmm2,%xmm2
    13e2:	48 89 45 88          	mov    %rax,-0x78(%rbp)
    13e6:	49 89 c6             	mov    %rax,%r14
    13e9:	31 c0                	xor    %eax,%eax
    13eb:	0f 29 95 70 ff ff ff 	movaps %xmm2,-0x90(%rbp)
    13f2:	8d 50 02             	lea    0x2(%rax),%edx
    }
    // printf("Created data for %d\n", sender);
    int seq[] = {1, 2, 5};
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      thread_data[j].thread_index = j;
      thread_data[j].reader_index = receiver_index;
    13f5:	41 89 86 0c 02 00 00 	mov    %eax,0x20c(%r14)
      thread_data[j].multiple = receiver_index % other_count;
    13fc:	41 89 86 10 02 00 00 	mov    %eax,0x210(%r14)
      thread_data[j].other_count = other_count;
     
      thread_data[j].cpu_set = receivercpu;
    1403:	48 8b 85 68 ff ff ff 	mov    -0x98(%rbp),%rax
      thread_data[j].running = 1;
    140a:	41 c7 86 90 01 00 00 01 00 00 00 	movl   $0x1,0x190(%r14)
      thread_data[j].thread_index = j;
    1415:	41 89 16             	mov    %edx,(%r14)
      thread_data[j].other_count = other_count;
    1418:	41 c7 86 08 02 00 00 02 00 00 00 	movl   $0x2,0x208(%r14)
      thread_data[j].cpu_set = receivercpu;
    1423:	49 89 86 98 01 00 00 	mov    %rax,0x198(%r14)
      thread_data[j].mode = READER;
    142a:	41 c7 86 84 01 00 00 01 00 00 00 	movl   $0x1,0x184(%r14)
      if (j == receiver) {
    1435:	83 fa 02             	cmp    $0x2,%edx
    1438:	0f 84 47 03 00 00    	je     1785 <main+0x585>
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
    143e:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    1445:	45 31 c0             	xor    %r8d,%r8d
      thread_data[j].sender = &thread_data[sender];
    1448:	66 0f 6f 8d 70 ff ff ff 	movdqa -0x90(%rbp),%xmm1
      thread_data[j].size = buffer_size;
    1450:	49 c7 86 88 01 00 00 00 04 00 00 	movq   $0x400,0x188(%r14)
    145b:	b9 01 00 00 00       	mov    $0x1,%ecx
    1460:	ba 03 00 00 00       	mov    $0x3,%edx
      thread_data[j].start = 0;
    1465:	41 c7 86 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r14)
    1470:	48 8d 35 e1 0b 00 00 	lea    0xbe1(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
      thread_data[j].readers = thread_data[sender].readers;
    1477:	49 89 86 00 02 00 00 	mov    %rax,0x200(%r14)
    147e:	bf 01 00 00 00       	mov    $0x1,%edi
    1483:	31 c0                	xor    %eax,%eax
      thread_data[j].sender = &thread_data[sender];
    1485:	41 0f 11 4e 08       	movups %xmm1,0x8(%r14)
    148a:	e8 11 fd ff ff       	call   11a0 <__printf_chk@plt>
      printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        thread_data[n].readers[receiver_index] = &thread_data[j];
    148f:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    1496:	31 d2                	xor    %edx,%edx
    1498:	48 8d 35 44 0c 00 00 	lea    0xc44(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    149f:	bf 01 00 00 00       	mov    $0x1,%edi
    14a4:	4c 89 70 08          	mov    %r14,0x8(%rax)
    14a8:	48 8b 83 80 04 00 00 	mov    0x480(%rbx),%rax
    14af:	4c 89 70 08          	mov    %r14,0x8(%rax)
    14b3:	31 c0                	xor    %eax,%eax
    14b5:	e8 e6 fc ff ff       	call   11a0 <__printf_chk@plt>
      }
    }
    printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
    14ba:	0f ae f0             	mfence
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
    14bd:	48 8b 45 80          	mov    -0x80(%rbp),%rax
    14c1:	4d 8d 74 24 10       	lea    0x10(%r12),%r14
    14c6:	c7 45 9c 00 00 00 00 	movl   $0x0,-0x64(%rbp)
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    14cd:	41 bf 02 00 00 00    	mov    $0x2,%r15d
    14d3:	4c 8d 68 70          	lea    0x70(%rax),%r13
    14d7:	48 8d 35 05 0c 00 00 	lea    0xc05(%rip),%rsi        # 20e3 <_IO_stdin_used+0xe3>
    14de:	bf 01 00 00 00       	mov    $0x1,%edi
    14e3:	31 c0                	xor    %eax,%eax
    14e5:	44 89 fa             	mov    %r15d,%edx
    14e8:	e8 b3 fc ff ff       	call   11a0 <__printf_chk@plt>
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
    14ed:	31 f6                	xor    %esi,%esi
    14ef:	4c 89 ef             	mov    %r13,%rdi
    14f2:	e8 79 fc ff ff       	call   1170 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    14f7:	85 c0                	test   %eax,%eax
    14f9:	0f 85 46 03 00 00    	jne    1845 <main+0x645>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
    14ff:	48 8d 75 9c          	lea    -0x64(%rbp),%rsi
    1503:	4c 89 ef             	mov    %r13,%rdi
    1506:	e8 b5 fc ff ff       	call   11c0 <pthread_attr_setschedparam@plt>
      if (ret) {
    150b:	85 c0                	test   %eax,%eax
    150d:	0f 85 4d 03 00 00    	jne    1860 <main+0x660>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    1513:	48 8b 4d 88          	mov    -0x78(%rbp),%rcx
    1517:	4c 89 ee             	mov    %r13,%rsi
    151a:	4c 89 f7             	mov    %r14,%rdi
    151d:	48 8d 15 ac 04 00 00 	lea    0x4ac(%rip),%rdx        # 19d0 <disruptor_thread>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1524:	49 83 c5 38          	add    $0x38,%r13
    1528:	49 83 c6 08          	add    $0x8,%r14
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
    152c:	e8 7f fc ff ff       	call   11b0 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    1531:	49 8b 7e f8          	mov    -0x8(%r14),%rdi
    1535:	be 08 00 00 00       	mov    $0x8,%esi
    153a:	48 8b 93 98 06 00 00 	mov    0x698(%rbx),%rdx
    1541:	e8 da fb ff ff       	call   1120 <pthread_setaffinity_np@plt>
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1546:	48 81 45 88 80 02 00 00 	addq   $0x280,-0x78(%rbp)
    154e:	41 83 ff 02          	cmp    $0x2,%r15d
    1552:	75 0b                	jne    155f <main+0x35f>
    1554:	41 bf 03 00 00 00    	mov    $0x3,%r15d
    155a:	e9 78 ff ff ff       	jmp    14d7 <main+0x2d7>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
    155f:	4c 8b 75 80          	mov    -0x80(%rbp),%r14
    1563:	31 f6                	xor    %esi,%esi
    1565:	4c 89 f7             	mov    %r14,%rdi
    1568:	e8 03 fc ff ff       	call   1170 <pthread_attr_setschedpolicy@plt>
      if (ret) {
    156d:	85 c0                	test   %eax,%eax
    156f:	0f 85 d0 02 00 00    	jne    1845 <main+0x645>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1575:	48 8d 75 98          	lea    -0x68(%rbp),%rsi
    1579:	4c 89 f7             	mov    %r14,%rdi
      param2.sched_priority = 0;
    157c:	c7 45 98 00 00 00 00 	movl   $0x0,-0x68(%rbp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
    1583:	e8 38 fc ff ff       	call   11c0 <pthread_attr_setschedparam@plt>
      if (ret) {
    1588:	85 c0                	test   %eax,%eax
    158a:	0f 85 d0 02 00 00    	jne    1860 <main+0x660>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    1590:	48 89 d9             	mov    %rbx,%rcx
    1593:	4c 89 e7             	mov    %r12,%rdi
    1596:	48 8d 15 33 04 00 00 	lea    0x433(%rip),%rdx        # 19d0 <disruptor_thread>
    159d:	4c 89 f6             	mov    %r14,%rsi
    15a0:	e8 0b fc ff ff       	call   11b0 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    15a5:	49 8b 3c 24          	mov    (%r12),%rdi
    15a9:	be 08 00 00 00       	mov    $0x8,%esi
    void * res1;
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    15ae:	45 31 ed             	xor    %r13d,%r13d
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    15b1:	48 8b 93 98 01 00 00 	mov    0x198(%rbx),%rdx
    15b8:	e8 63 fb ff ff       	call   1120 <pthread_setaffinity_np@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
    15bd:	4c 89 f6             	mov    %r14,%rsi
    15c0:	48 8d 8b 80 02 00 00 	lea    0x280(%rbx),%rcx
    15c7:	49 8d 7c 24 08       	lea    0x8(%r12),%rdi
    15cc:	48 83 c6 38          	add    $0x38,%rsi
    15d0:	48 8d 15 f9 03 00 00 	lea    0x3f9(%rip),%rdx        # 19d0 <disruptor_thread>
    15d7:	e8 d4 fb ff ff       	call   11b0 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
    15dc:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    15e1:	be 08 00 00 00       	mov    $0x8,%esi
    15e6:	48 8b 93 18 04 00 00 	mov    0x418(%rbx),%rdx
    15ed:	e8 2e fb ff ff       	call   1120 <pthread_setaffinity_np@plt>
  struct timespec preempt = {
    15f2:	66 0f 6f 05 a6 0b 00 00 	movdqa 0xba6(%rip),%xmm0        # 21a0 <_IO_stdin_used+0x1a0>
    15fa:	ba 14 00 00 00       	mov    $0x14,%edx
    15ff:	31 c0                	xor    %eax,%eax
    1601:	48 8d 35 33 0b 00 00 	lea    0xb33(%rip),%rsi        # 213b <_IO_stdin_used+0x13b>
    1608:	bf 01 00 00 00       	mov    $0x1,%edi
    160d:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
    1611:	e8 8a fb ff ff       	call   11a0 <__printf_chk@plt>
  nanosleep(&preempt , &rem2);
    1616:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    161a:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
    161e:	e8 3d fb ff ff       	call   1160 <nanosleep@plt>
      pthread_join(thread[n], res1);
    1623:	49 8b 3c 24          	mov    (%r12),%rdi
    1627:	4c 89 ee             	mov    %r13,%rsi
    thread_data[sender].running = 0;
    162a:	c7 83 90 01 00 00 00 00 00 00 	movl   $0x0,0x190(%rbx)
      thread_data[j].running = 0;
    1634:	c7 83 90 06 00 00 00 00 00 00 	movl   $0x0,0x690(%rbx)
    163e:	c7 83 10 09 00 00 00 00 00 00 	movl   $0x0,0x910(%rbx)
      thread_data[n].running = 0;
    1648:	c7 83 90 01 00 00 00 00 00 00 	movl   $0x0,0x190(%rbx)
    1652:	c7 83 10 04 00 00 00 00 00 00 	movl   $0x0,0x410(%rbx)
      pthread_join(thread[n], res1);
    165c:	e8 8f fb ff ff       	call   11f0 <pthread_join@plt>
    1661:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    1666:	4c 89 ee             	mov    %r13,%rsi
    1669:	e8 82 fb ff ff       	call   11f0 <pthread_join@plt>
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    166e:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    1673:	4c 89 ee             	mov    %r13,%rsi
    1676:	e8 75 fb ff ff       	call   11f0 <pthread_join@plt>
    167b:	49 8b 7c 24 18       	mov    0x18(%r12),%rdi
    1680:	4c 89 ee             	mov    %r13,%rsi
    1683:	45 31 e4             	xor    %r12d,%r12d
    1686:	4c 8d 2d dd 0a 00 00 	lea    0xadd(%rip),%r13        # 216a <_IO_stdin_used+0x16a>
    168d:	e8 5e fb ff ff       	call   11f0 <pthread_join@plt>
    1692:	ba 02 00 00 00       	mov    $0x2,%edx
    1697:	48 8d 35 b6 0a 00 00 	lea    0xab6(%rip),%rsi        # 2154 <_IO_stdin_used+0x154>
    169e:	31 c0                	xor    %eax,%eax
    16a0:	bf 01 00 00 00       	mov    $0x1,%edi
    16a5:	e8 f6 fa ff ff       	call   11a0 <__printf_chk@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
    16aa:	eb 18                	jmp    16c4 <main+0x4c4>
    16ac:	0f 1f 40 00          	nopl   0x0(%rax)
    16b0:	49 81 c4 80 01 00 00 	add    $0x180,%r12
    16b7:	49 81 fc 00 00 06 00 	cmp    $0x60000,%r12
    16be:	0f 84 88 00 00 00    	je     174c <main+0x54c>
      int compcount = 0;
      for (int n = 0 ; n < 2 ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
    16c4:	48 8b 43 18          	mov    0x18(%rbx),%rax
    16c8:	4c 01 e0             	add    %r12,%rax
    16cb:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
    16d2:	83 3a 01             	cmpl   $0x1,(%rdx)
    16d5:	75 d9                	jne    16b0 <main+0x4b0>
    16d7:	83 7a 04 01          	cmpl   $0x1,0x4(%rdx)
    16db:	75 d3                	jne    16b0 <main+0x4b0>
      // printf("%d\n", compcount);
      if (compcount == other_count) {
      for (int n = 0 ; n < other_count ; n++) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
          struct timespec end = thread_data[sender].data[y].end[n];
    16dd:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    16e4:	31 c9                	xor    %ecx,%ecx
    16e6:	4c 89 ee             	mov    %r13,%rsi
    16e9:	bf 01 00 00 00       	mov    $0x1,%edi
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    16ee:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    16f2:	4c 8b 02             	mov    (%rdx),%r8
    16f5:	31 d2                	xor    %edx,%edx
    16f7:	4c 2b 48 08          	sub    0x8(%rax),%r9
    16fb:	4c 2b 00             	sub    (%rax),%r8
    16fe:	31 c0                	xor    %eax,%eax
    1700:	e8 9b fa ff ff       	call   11a0 <__printf_chk@plt>
          struct timespec start = thread_data[sender].data[y].start;
    1705:	48 8b 43 18          	mov    0x18(%rbx),%rax
    1709:	31 c9                	xor    %ecx,%ecx
    170b:	4c 89 ee             	mov    %r13,%rsi
    170e:	bf 01 00 00 00       	mov    $0x1,%edi
    1713:	4c 01 e0             	add    %r12,%rax
    for (int y = 0 ; y < buffer_size; y++) {
    1716:	49 81 c4 80 01 00 00 	add    $0x180,%r12
          struct timespec end = thread_data[sender].data[y].end[n];
    171d:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    1724:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    1728:	4c 8b 42 10          	mov    0x10(%rdx),%r8
    172c:	ba 01 00 00 00       	mov    $0x1,%edx
    1731:	4c 2b 48 08          	sub    0x8(%rax),%r9
    1735:	4c 2b 00             	sub    (%rax),%r8
    1738:	31 c0                	xor    %eax,%eax
    173a:	e8 61 fa ff ff       	call   11a0 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
    173f:	49 81 fc 00 00 06 00 	cmp    $0x60000,%r12
    1746:	0f 85 78 ff ff ff    	jne    16c4 <main+0x4c4>
    174c:	31 d2                	xor    %edx,%edx
    174e:	31 c0                	xor    %eax,%eax
    1750:	48 8d 35 2a 0a 00 00 	lea    0xa2a(%rip),%rsi        # 2181 <_IO_stdin_used+0x181>
    1757:	bf 01 00 00 00       	mov    $0x1,%edi
    175c:	e8 3f fa ff ff       	call   11a0 <__printf_chk@plt>
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
    1761:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    1765:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    176e:	0f 85 e7 00 00 00    	jne    185b <main+0x65b>
    1774:	48 83 c4 78          	add    $0x78,%rsp
    1778:	31 c0                	xor    %eax,%eax
    177a:	5b                   	pop    %rbx
    177b:	41 5c                	pop    %r12
    177d:	41 5d                	pop    %r13
    177f:	41 5e                	pop    %r14
    1781:	41 5f                	pop    %r15
    1783:	5d                   	pop    %rbp
    1784:	c3                   	ret
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
    1785:	be 80 01 00 00       	mov    $0x180,%esi
    178a:	bf 00 04 00 00       	mov    $0x400,%edi
    178f:	e8 ec f9 ff ff       	call   1180 <calloc@plt>
    1794:	49 89 46 18          	mov    %rax,0x18(%r14)
    1798:	49 89 c5             	mov    %rax,%r13
        for (int n = 0 ; n < buffer_size ; n++) {
    179b:	4c 8d b8 00 01 00 00 	lea    0x100(%rax),%r15
    17a2:	49 81 c5 00 01 06 00 	add    $0x60100,%r13
    17a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    17b0:	be 04 00 00 00       	mov    $0x4,%esi
    17b5:	bf 02 00 00 00       	mov    $0x2,%edi
        for (int n = 0 ; n < buffer_size ; n++) {
    17ba:	49 81 c7 80 01 00 00 	add    $0x180,%r15
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
    17c1:	e8 ba f9 ff ff       	call   1180 <calloc@plt>
    17c6:	49 89 87 80 fe ff ff 	mov    %rax,-0x180(%r15)
        for (int n = 0 ; n < buffer_size ; n++) {
    17cd:	4d 39 fd             	cmp    %r15,%r13
    17d0:	75 de                	jne    17b0 <main+0x5b0>
      thread_data[j].readers = thread_data[sender].readers;
    17d2:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    17d9:	45 31 c0             	xor    %r8d,%r8d
    17dc:	31 c9                	xor    %ecx,%ecx
      thread_data[j].size = buffer_size;
    17de:	49 c7 86 88 01 00 00 00 04 00 00 	movq   $0x400,0x188(%r14)
      thread_data[j].start = 0;
    17e9:	41 c7 86 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r14)
      thread_data[j].sender = &thread_data[sender];
    17f4:	66 0f 6f 9d 70 ff ff ff 	movdqa -0x90(%rbp),%xmm3
    17fc:	ba 02 00 00 00       	mov    $0x2,%edx
    1801:	48 8d 35 50 08 00 00 	lea    0x850(%rip),%rsi        # 2058 <_IO_stdin_used+0x58>
      thread_data[j].readers = thread_data[sender].readers;
    1808:	49 89 86 00 02 00 00 	mov    %rax,0x200(%r14)
    180f:	bf 01 00 00 00       	mov    $0x1,%edi
    1814:	31 c0                	xor    %eax,%eax
      thread_data[j].sender = &thread_data[sender];
    1816:	41 0f 11 5e 08       	movups %xmm3,0x8(%r14)
    181b:	e8 80 f9 ff ff       	call   11a0 <__printf_chk@plt>
        thread_data[n].readers[receiver_index] = &thread_data[j];
    1820:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    1827:	4c 89 30             	mov    %r14,(%rax)
    182a:	48 8b 83 80 04 00 00 	mov    0x480(%rbx),%rax
    1831:	4c 89 30             	mov    %r14,(%rax)
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
    1834:	49 81 c6 80 02 00 00 	add    $0x280,%r14
    183b:	b8 01 00 00 00       	mov    $0x1,%eax
    1840:	e9 ad fb ff ff       	jmp    13f2 <main+0x1f2>
    1845:	48 8d 3d b4 08 00 00 	lea    0x8b4(%rip),%rdi        # 2100 <_IO_stdin_used+0x100>
    184c:	e8 df f8 ff ff       	call   1130 <puts@plt>
               exit(1);
    1851:	bf 01 00 00 00       	mov    $0x1,%edi
    1856:	e8 85 f9 ff ff       	call   11e0 <exit@plt>
}
    185b:	e8 f0 f8 ff ff       	call   1150 <__stack_chk_fail@plt>
    1860:	48 8d 3d b7 08 00 00 	lea    0x8b7(%rip),%rdi        # 211e <_IO_stdin_used+0x11e>
    1867:	e8 c4 f8 ff ff       	call   1130 <puts@plt>
              exit(1);
    186c:	bf 01 00 00 00       	mov    $0x1,%edi
    1871:	e8 6a f9 ff ff       	call   11e0 <exit@plt>
    1876:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001880 <_start>:
    1880:	f3 0f 1e fa          	endbr64
    1884:	31 ed                	xor    %ebp,%ebp
    1886:	49 89 d1             	mov    %rdx,%r9
    1889:	5e                   	pop    %rsi
    188a:	48 89 e2             	mov    %rsp,%rdx
    188d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1891:	50                   	push   %rax
    1892:	54                   	push   %rsp
    1893:	45 31 c0             	xor    %r8d,%r8d
    1896:	31 c9                	xor    %ecx,%ecx
    1898:	48 8d 3d 61 f9 ff ff 	lea    -0x69f(%rip),%rdi        # 1200 <main>
    189f:	ff 15 2b 27 00 00    	call   *0x272b(%rip)        # 3fd0 <__libc_start_main@GLIBC_2.34>
    18a5:	f4                   	hlt
    18a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000018b0 <__gmon_start__>:
    18b0:	f3 0f 1e fa          	endbr64
    18b4:	8b 05 56 27 00 00    	mov    0x2756(%rip),%eax        # 4010 <__TMC_END__>
    18ba:	85 c0                	test   %eax,%eax
    18bc:	74 02                	je     18c0 <__gmon_start__+0x10>
    18be:	c3                   	ret
    18bf:	90                   	nop
    18c0:	48 83 ec 08          	sub    $0x8,%rsp
    18c4:	48 8d 35 62 03 00 00 	lea    0x362(%rip),%rsi        # 1c2d <etext>
    18cb:	48 8d 3d 2e e7 ff ff 	lea    -0x18d2(%rip),%rdi        # 0 <__executable_start>
    18d2:	c7 05 34 27 00 00 01 00 00 00 	movl   $0x1,0x2734(%rip)        # 4010 <__TMC_END__>
    18dc:	e8 af f8 ff ff       	call   1190 <__monstartup@plt>
    18e1:	48 8b 3d f8 26 00 00 	mov    0x26f8(%rip),%rdi        # 3fe0 <_mcleanup@GLIBC_2.2.5>
    18e8:	48 83 c4 08          	add    $0x8,%rsp
    18ec:	e9 ff 02 00 00       	jmp    1bf0 <atexit>
    18f1:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    18fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000001900 <_dl_relocate_static_pie>:
    1900:	f3 0f 1e fa          	endbr64
    1904:	c3                   	ret
    1905:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    190f:	90                   	nop

0000000000001910 <deregister_tm_clones>:
    1910:	48 8d 3d f9 26 00 00 	lea    0x26f9(%rip),%rdi        # 4010 <__TMC_END__>
    1917:	48 8d 05 f2 26 00 00 	lea    0x26f2(%rip),%rax        # 4010 <__TMC_END__>
    191e:	48 39 f8             	cmp    %rdi,%rax
    1921:	74 15                	je     1938 <deregister_tm_clones+0x28>
    1923:	48 8b 05 ae 26 00 00 	mov    0x26ae(%rip),%rax        # 3fd8 <_ITM_deregisterTMCloneTable@Base>
    192a:	48 85 c0             	test   %rax,%rax
    192d:	74 09                	je     1938 <deregister_tm_clones+0x28>
    192f:	ff e0                	jmp    *%rax
    1931:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1938:	c3                   	ret
    1939:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001940 <register_tm_clones>:
    1940:	48 8d 3d c9 26 00 00 	lea    0x26c9(%rip),%rdi        # 4010 <__TMC_END__>
    1947:	48 8d 35 c2 26 00 00 	lea    0x26c2(%rip),%rsi        # 4010 <__TMC_END__>
    194e:	48 29 fe             	sub    %rdi,%rsi
    1951:	48 89 f0             	mov    %rsi,%rax
    1954:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1958:	48 c1 f8 03          	sar    $0x3,%rax
    195c:	48 01 c6             	add    %rax,%rsi
    195f:	48 d1 fe             	sar    %rsi
    1962:	74 14                	je     1978 <register_tm_clones+0x38>
    1964:	48 8b 05 85 26 00 00 	mov    0x2685(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    196b:	48 85 c0             	test   %rax,%rax
    196e:	74 08                	je     1978 <register_tm_clones+0x38>
    1970:	ff e0                	jmp    *%rax
    1972:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1978:	c3                   	ret
    1979:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001980 <__do_global_dtors_aux>:
    1980:	f3 0f 1e fa          	endbr64
    1984:	80 3d 89 26 00 00 00 	cmpb   $0x0,0x2689(%rip)        # 4014 <completed.0>
    198b:	75 2b                	jne    19b8 <__do_global_dtors_aux+0x38>
    198d:	55                   	push   %rbp
    198e:	48 83 3d 62 26 00 00 00 	cmpq   $0x0,0x2662(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1996:	48 89 e5             	mov    %rsp,%rbp
    1999:	74 0c                	je     19a7 <__do_global_dtors_aux+0x27>
    199b:	48 8b 3d 66 26 00 00 	mov    0x2666(%rip),%rdi        # 4008 <__dso_handle>
    19a2:	e8 69 f7 ff ff       	call   1110 <__cxa_finalize@plt>
    19a7:	e8 64 ff ff ff       	call   1910 <deregister_tm_clones>
    19ac:	c6 05 61 26 00 00 01 	movb   $0x1,0x2661(%rip)        # 4014 <completed.0>
    19b3:	5d                   	pop    %rbp
    19b4:	c3                   	ret
    19b5:	0f 1f 00             	nopl   (%rax)
    19b8:	c3                   	ret
    19b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000019c0 <frame_dummy>:
    19c0:	f3 0f 1e fa          	endbr64
    19c4:	e9 77 ff ff ff       	jmp    1940 <register_tm_clones>
    19c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000019d0 <disruptor_thread>:
void * disruptor_thread(void * arg) {
    19d0:	f3 0f 1e fa          	endbr64
    19d4:	55                   	push   %rbp
    19d5:	48 89 e5             	mov    %rsp,%rbp
    19d8:	41 57                	push   %r15
    19da:	41 56                	push   %r14
    19dc:	41 55                	push   %r13
    19de:	41 54                	push   %r12
    19e0:	53                   	push   %rbx
    19e1:	48 83 ec 08          	sub    $0x8,%rsp
    19e5:	ff 15 fd 25 00 00    	call   *0x25fd(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
    19eb:	48 8d 35 16 06 00 00 	lea    0x616(%rip),%rsi        # 2008 <_IO_stdin_used+0x8>
    19f2:	31 c0                	xor    %eax,%eax
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
    19f4:	8b 8f 84 01 00 00    	mov    0x184(%rdi),%ecx
    19fa:	8b 17                	mov    (%rdi),%edx
void * disruptor_thread(void * arg) {
    19fc:	48 89 fb             	mov    %rdi,%rbx
    19ff:	bf 01 00 00 00       	mov    $0x1,%edi
    1a04:	e8 97 f7 ff ff       	call   11a0 <__printf_chk@plt>
  if (data->mode == WRITER) {
    1a09:	8b 83 84 01 00 00    	mov    0x184(%rbx),%eax
    1a0f:	85 c0                	test   %eax,%eax
    1a11:	74 39                	je     1a4c <disruptor_thread+0x7c>
  } else if (data->mode == READER) {
    1a13:	8b 83 84 01 00 00    	mov    0x184(%rbx),%eax
    1a19:	83 f8 01             	cmp    $0x1,%eax
    1a1c:	0f 84 f8 00 00 00    	je     1b1a <disruptor_thread+0x14a>
  printf("Finished %d\n", data->mode);
    1a22:	8b 93 84 01 00 00    	mov    0x184(%rbx),%edx
    1a28:	48 8d 35 62 06 00 00 	lea    0x662(%rip),%rsi        # 2091 <_IO_stdin_used+0x91>
    1a2f:	bf 01 00 00 00       	mov    $0x1,%edi
    1a34:	31 c0                	xor    %eax,%eax
    1a36:	e8 65 f7 ff ff       	call   11a0 <__printf_chk@plt>
}
    1a3b:	48 83 c4 08          	add    $0x8,%rsp
    1a3f:	31 c0                	xor    %eax,%eax
    1a41:	5b                   	pop    %rbx
    1a42:	41 5c                	pop    %r12
    1a44:	41 5d                	pop    %r13
    1a46:	41 5e                	pop    %r14
    1a48:	41 5f                	pop    %r15
    1a4a:	5d                   	pop    %rbp
    1a4b:	c3                   	ret
    1a4c:	48 8d 3d 32 06 00 00 	lea    0x632(%rip),%rdi        # 2085 <_IO_stdin_used+0x85>
    1a53:	e8 d8 f6 ff ff       	call   1130 <puts@plt>
    struct Thread *me = data->sender;
    1a58:	4c 8b 63 08          	mov    0x8(%rbx),%r12
    while (data->running == 1) {
    1a5c:	0f 1f 40 00          	nopl   0x0(%rax)
    1a60:	8b 83 90 01 00 00    	mov    0x190(%rbx),%eax
    1a66:	83 f8 01             	cmp    $0x1,%eax
    1a69:	75 b7                	jne    1a22 <disruptor_thread+0x52>
      asm volatile ("sfence" ::: "memory");
    1a6b:	0f ae f8             	sfence
      for (int x  = 0 ; x < data->other_count; x++) {
    1a6e:	48 63 8b 08 02 00 00 	movslq 0x208(%rbx),%rcx
    1a75:	85 c9                	test   %ecx,%ecx
    1a77:	7e 3f                	jle    1ab8 <disruptor_thread+0xe8>
        if ((me->end + 1) % data->size == data->readers[x]->start) {
    1a79:	41 8b 84 24 00 01 00 00 	mov    0x100(%r12),%eax
    1a81:	83 c0 01             	add    $0x1,%eax
    1a84:	48 98                	cltq
    1a86:	48 99                	cqto
    1a88:	48 f7 bb 88 01 00 00 	idivq  0x188(%rbx)
    1a8f:	48 8b 83 00 02 00 00 	mov    0x200(%rbx),%rax
    1a96:	48 8d 34 c8          	lea    (%rax,%rcx,8),%rsi
    1a9a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1aa0:	48 8b 08             	mov    (%rax),%rcx
    1aa3:	48 63 89 80 00 00 00 	movslq 0x80(%rcx),%rcx
    1aaa:	48 39 ca             	cmp    %rcx,%rdx
    1aad:	74 b1                	je     1a60 <disruptor_thread+0x90>
      for (int x  = 0 ; x < data->other_count; x++) {
    1aaf:	48 83 c0 08          	add    $0x8,%rax
    1ab3:	48 39 c6             	cmp    %rax,%rsi
    1ab6:	75 e8                	jne    1aa0 <disruptor_thread+0xd0>
            if (changed = __atomic_add_fetch(&me->end, 1, __ATOMIC_ACQUIRE)) {
    1ab8:	b8 01 00 00 00       	mov    $0x1,%eax
    1abd:	f0 41 0f c1 84 24 00 01 00 00 	lock xadd %eax,0x100(%r12)
    1ac7:	83 c0 01             	add    $0x1,%eax
    1aca:	74 94                	je     1a60 <disruptor_thread+0x90>
              int dest = (changed) % me->size;
    1acc:	48 98                	cltq
    1ace:	48 99                	cqto
    1ad0:	49 f7 bc 24 88 01 00 00 	idivq  0x188(%r12)
              for (int x = 0 ; x < data->other_count; x++) {
    1ad8:	8b 83 08 02 00 00    	mov    0x208(%rbx),%eax
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[dest].start);
    1ade:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
    1ae2:	48 c1 e6 07          	shl    $0x7,%rsi
    1ae6:	49 03 74 24 18       	add    0x18(%r12),%rsi
              for (int x = 0 ; x < data->other_count; x++) {
    1aeb:	85 c0                	test   %eax,%eax
    1aed:	7e 1c                	jle    1b0b <disruptor_thread+0x13b>
                me->data[dest].complete[x] = 0;
    1aef:	48 8b 96 00 01 00 00 	mov    0x100(%rsi),%rdx
    1af6:	31 c0                	xor    %eax,%eax
    1af8:	c7 04 82 00 00 00 00 	movl   $0x0,(%rdx,%rax,4)
              for (int x = 0 ; x < data->other_count; x++) {
    1aff:	48 83 c0 01          	add    $0x1,%rax
    1b03:	39 83 08 02 00 00    	cmp    %eax,0x208(%rbx)
    1b09:	7f ed                	jg     1af8 <disruptor_thread+0x128>
              clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[dest].start);
    1b0b:	bf 04 00 00 00       	mov    $0x4,%edi
    1b10:	e8 2b f6 ff ff       	call   1140 <clock_gettime@plt>
    1b15:	e9 46 ff ff ff       	jmp    1a60 <disruptor_thread+0x90>
    1b1a:	48 8d 3d 7d 05 00 00 	lea    0x57d(%rip),%rdi        # 209e <_IO_stdin_used+0x9e>
    1b21:	e8 0a f6 ff ff       	call   1130 <puts@plt>
    struct Thread *sender = data->sender;
    1b26:	4c 8b 63 08          	mov    0x8(%rbx),%r12
    struct Snapshot * rdata = sender->data;
    1b2a:	4d 8b 74 24 18       	mov    0x18(%r12),%r14
    while (data->running == 1) {
    1b2f:	90                   	nop
    1b30:	8b 83 90 01 00 00    	mov    0x190(%rbx),%eax
    1b36:	83 f8 01             	cmp    $0x1,%eax
    1b39:	0f 85 e3 fe ff ff    	jne    1a22 <disruptor_thread+0x52>
      if ((sender->end % sender->size) == data->start) {
    1b3f:	49 63 84 24 00 01 00 00 	movslq 0x100(%r12),%rax
    1b47:	44 8b ab 80 00 00 00 	mov    0x80(%rbx),%r13d
    1b4e:	48 99                	cqto
    1b50:	49 f7 bc 24 88 01 00 00 	idivq  0x188(%r12)
    1b58:	49 63 c5             	movslq %r13d,%rax
    1b5b:	48 39 c2             	cmp    %rax,%rdx
    1b5e:	74 d0                	je     1b30 <disruptor_thread+0x160>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
    1b60:	4c 8d 3c 40          	lea    (%rax,%rax,2),%r15
    1b64:	48 63 b3 0c 02 00 00 	movslq 0x20c(%rbx),%rsi
    1b6b:	bf 04 00 00 00       	mov    $0x4,%edi
    1b70:	49 c1 e7 07          	shl    $0x7,%r15
    1b74:	4d 01 f7             	add    %r14,%r15
    1b77:	48 c1 e6 04          	shl    $0x4,%rsi
    1b7b:	49 03 b7 80 00 00 00 	add    0x80(%r15),%rsi
    1b82:	e8 b9 f5 ff ff       	call   1140 <clock_gettime@plt>
              rdata[changed].complete[data->reader_index] = 1;
    1b87:	49 8b 87 00 01 00 00 	mov    0x100(%r15),%rax
    1b8e:	48 63 93 0c 02 00 00 	movslq 0x20c(%rbx),%rdx
    1b95:	c7 04 90 01 00 00 00 	movl   $0x1,(%rax,%rdx,4)
              data->start = (changed + 1) % data->size;
    1b9c:	41 8d 45 01          	lea    0x1(%r13),%eax
    1ba0:	48 98                	cltq
    1ba2:	48 99                	cqto
    1ba4:	48 f7 bb 88 01 00 00 	idivq  0x188(%rbx)
    1bab:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
              asm volatile ("sfence" ::: "memory");
    1bb1:	0f ae f8             	sfence
    1bb4:	e9 77 ff ff ff       	jmp    1b30 <disruptor_thread+0x160>
    1bb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001bc0 <min>:
int min(long a, long b) {
    1bc0:	f3 0f 1e fa          	endbr64
    1bc4:	55                   	push   %rbp
    1bc5:	48 89 e5             	mov    %rsp,%rbp
    1bc8:	ff 15 1a 24 00 00    	call   *0x241a(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
  if (a < b) return a;
    1bce:	48 39 f7             	cmp    %rsi,%rdi
    1bd1:	7c 02                	jl     1bd5 <min+0x15>
  if (b < a) return b;
    1bd3:	7f 0b                	jg     1be0 <min+0x20>
  if (a < b) return a;
    1bd5:	89 f8                	mov    %edi,%eax
}
    1bd7:	5d                   	pop    %rbp
    1bd8:	c3                   	ret
    1bd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (b < a) return b;
    1be0:	89 f0                	mov    %esi,%eax
}
    1be2:	5d                   	pop    %rbp
    1be3:	c3                   	ret
    1be4:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    1bee:	66 90                	xchg   %ax,%ax

0000000000001bf0 <atexit>:
    1bf0:	f3 0f 1e fa          	endbr64
    1bf4:	48 8b 15 0d 24 00 00 	mov    0x240d(%rip),%rdx        # 4008 <__dso_handle>
    1bfb:	31 f6                	xor    %esi,%esi
    1bfd:	e9 ce f5 ff ff       	jmp    11d0 <__cxa_atexit@plt>
    1c02:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    1c0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000001c10 <__stack_chk_fail_local>:
    1c10:	f3 0f 1e fa          	endbr64
    1c14:	50                   	push   %rax
    1c15:	58                   	pop    %rax
    1c16:	48 83 ec 08          	sub    $0x8,%rsp
    1c1a:	e8 31 f5 ff ff       	call   1150 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000001c20 <_fini>:
    1c20:	f3 0f 1e fa          	endbr64
    1c24:	48 83 ec 08          	sub    $0x8,%rsp
    1c28:	48 83 c4 08          	add    $0x8,%rsp
    1c2c:	c3                   	ret
