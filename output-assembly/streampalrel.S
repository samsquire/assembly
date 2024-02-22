
streampalrel:     file format elf64-x86-64


Disassembly of section .init:

0000000000001000 <_init>:
    1000:	f3 0f 1e fa          	endbr64
    1004:	48 83 ec 08          	sub    $0x8,%rsp
    1008:	48 8d 05 71 04 00 00 	lea    0x471(%rip),%rax        # 1480 <__gmon_start__>
    100f:	48 85 c0             	test   %rax,%rax
    1012:	74 02                	je     1016 <_init+0x16>
    1014:	ff d0                	call   *%rax
    1016:	48 83 c4 08          	add    $0x8,%rsp
    101a:	c3                   	ret

Disassembly of section .plt:

0000000000001020 <.plt>:
    1020:	ff 35 52 2f 00 00    	push   0x2f52(%rip)        # 3f78 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:	ff 25 54 2f 00 00    	jmp    *0x2f54(%rip)        # 3f80 <_GLOBAL_OFFSET_TABLE_+0x10>
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

Disassembly of section .plt.got:

00000000000010c0 <__cxa_finalize@plt>:
    10c0:	f3 0f 1e fa          	endbr64
    10c4:	ff 25 2e 2f 00 00    	jmp    *0x2f2e(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    10ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

00000000000010d0 <puts@plt>:
    10d0:	f3 0f 1e fa          	endbr64
    10d4:	ff 25 ae 2e 00 00    	jmp    *0x2eae(%rip)        # 3f88 <puts@GLIBC_2.2.5>
    10da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010e0 <__stack_chk_fail@plt>:
    10e0:	f3 0f 1e fa          	endbr64
    10e4:	ff 25 a6 2e 00 00    	jmp    *0x2ea6(%rip)        # 3f90 <__stack_chk_fail@GLIBC_2.4>
    10ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010f0 <nanosleep@plt>:
    10f0:	f3 0f 1e fa          	endbr64
    10f4:	ff 25 9e 2e 00 00    	jmp    *0x2e9e(%rip)        # 3f98 <nanosleep@GLIBC_2.2.5>
    10fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001100 <calloc@plt>:
    1100:	f3 0f 1e fa          	endbr64
    1104:	ff 25 96 2e 00 00    	jmp    *0x2e96(%rip)        # 3fa0 <calloc@GLIBC_2.2.5>
    110a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001110 <__monstartup@plt>:
    1110:	f3 0f 1e fa          	endbr64
    1114:	ff 25 8e 2e 00 00    	jmp    *0x2e8e(%rip)        # 3fa8 <__monstartup@GLIBC_2.2.5>
    111a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001120 <__printf_chk@plt>:
    1120:	f3 0f 1e fa          	endbr64
    1124:	ff 25 86 2e 00 00    	jmp    *0x2e86(%rip)        # 3fb0 <__printf_chk@GLIBC_2.3.4>
    112a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001130 <pthread_create@plt>:
    1130:	f3 0f 1e fa          	endbr64
    1134:	ff 25 7e 2e 00 00    	jmp    *0x2e7e(%rip)        # 3fb8 <pthread_create@GLIBC_2.34>
    113a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001140 <__cxa_atexit@plt>:
    1140:	f3 0f 1e fa          	endbr64
    1144:	ff 25 76 2e 00 00    	jmp    *0x2e76(%rip)        # 3fc0 <__cxa_atexit@GLIBC_2.2.5>
    114a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001150 <pthread_join@plt>:
    1150:	f3 0f 1e fa          	endbr64
    1154:	ff 25 6e 2e 00 00    	jmp    *0x2e6e(%rip)        # 3fc8 <pthread_join@GLIBC_2.34>
    115a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000001160 <main>:
  }
  
  return (void*)log->result;
}

int main() {
    1160:	f3 0f 1e fa          	endbr64
    1164:	55                   	push   %rbp
    1165:	48 89 e5             	mov    %rsp,%rbp
    1168:	41 57                	push   %r15
    116a:	41 56                	push   %r14
    116c:	41 55                	push   %r13
    116e:	41 54                	push   %r12
    1170:	53                   	push   %rbx
    1171:	48 83 ec 58          	sub    $0x58,%rsp
    1175:	ff 15 6d 2e 00 00    	call   *0x2e6d(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
  int thread_count = 12; 
  int total_threads = thread_count;
  int data_size = 1000000;

  struct Log * logs = calloc(thread_count, sizeof(struct Log));
    117b:	be 40 00 00 00       	mov    $0x40,%esi
    1180:	bf 0c 00 00 00       	mov    $0xc,%edi
  struct Log ** logptrs = calloc(thread_count, sizeof(struct Log*));
    1185:	45 31 ed             	xor    %r13d,%r13d
int main() {
    1188:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1191:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    1195:	31 c0                	xor    %eax,%eax
  struct Log * logs = calloc(thread_count, sizeof(struct Log));
    1197:	e8 64 ff ff ff       	call   1100 <calloc@plt>
  struct Log ** logptrs = calloc(thread_count, sizeof(struct Log*));
    119c:	be 08 00 00 00       	mov    $0x8,%esi
    11a1:	bf 0c 00 00 00       	mov    $0xc,%edi
  struct Log * logs = calloc(thread_count, sizeof(struct Log));
    11a6:	48 89 45 80          	mov    %rax,-0x80(%rbp)
    11aa:	49 89 c4             	mov    %rax,%r12
  struct Log ** logptrs = calloc(thread_count, sizeof(struct Log*));
    11ad:	e8 4e ff ff ff       	call   1100 <calloc@plt>
    11b2:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < thread_count ; x++) {
    11b5:	0f 1f 00             	nopl   (%rax)
    logs[x].running = 1;
    logs[x].thread_index = x;
    11b8:	45 89 2c 24          	mov    %r13d,(%r12)
    logs[x].data_size = data_size;
    logs[x].thread_count = thread_count;
    logs[x].data = calloc(data_size, sizeof(int));
    11bc:	be 04 00 00 00       	mov    $0x4,%esi
    11c1:	bf 40 42 0f 00       	mov    $0xf4240,%edi
    logs[x].running = 1;
    11c6:	41 c7 44 24 28 01 00 00 00 	movl   $0x1,0x28(%r12)
    logs[x].data_size = data_size;
    11cf:	41 c7 44 24 18 40 42 0f 00 	movl   $0xf4240,0x18(%r12)
    logs[x].thread_count = thread_count;
    11d8:	41 c7 44 24 04 0c 00 00 00 	movl   $0xc,0x4(%r12)
    logs[x].data = calloc(data_size, sizeof(int));
    11e1:	e8 1a ff ff ff       	call   1100 <calloc@plt>
    logs[x].data[0] = 1;
    logs[x].mine = 1;
    logs[x].others = logptrs;
    logptrs[x] = &logs[x];
    11e6:	4f 89 24 ee          	mov    %r12,(%r14,%r13,8)
  for (int x = 0 ; x < thread_count ; x++) {
    11ea:	49 83 c5 01          	add    $0x1,%r13
    11ee:	49 83 c4 40          	add    $0x40,%r12
    logs[x].data = calloc(data_size, sizeof(int));
    11f2:	49 89 44 24 d0       	mov    %rax,-0x30(%r12)
    logs[x].mine = 1;
    11f7:	49 c7 44 24 f8 01 00 00 00 	movq   $0x1,-0x8(%r12)
    logs[x].others = logptrs;
    1200:	4d 89 74 24 c8       	mov    %r14,-0x38(%r12)
    logs[x].data[0] = 1;
    1205:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  for (int x = 0 ; x < thread_count ; x++) {
    120b:	49 83 fd 0c          	cmp    $0xc,%r13
    120f:	75 a7                	jne    11b8 <main+0x58>
  }
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    1211:	be 08 00 00 00       	mov    $0x8,%esi
    1216:	bf 0c 00 00 00       	mov    $0xc,%edi
    121b:	e8 e0 fe ff ff       	call   1100 <calloc@plt>
  pthread_attr_t      *attr = calloc(total_threads, sizeof(pthread_attr_t));
    1220:	be 38 00 00 00       	mov    $0x38,%esi
    1225:	bf 0c 00 00 00       	mov    $0xc,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    122a:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *attr = calloc(total_threads, sizeof(pthread_attr_t));
    122d:	e8 ce fe ff ff       	call   1100 <calloc@plt>
    1232:	48 8b 5d 80          	mov    -0x80(%rbp),%rbx
    1236:	4d 8d 6c 24 60       	lea    0x60(%r12),%r13
    123b:	4d 89 e7             	mov    %r12,%r15
    123e:	48 89 c6             	mov    %rax,%rsi
    1241:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

  for (int x = 0 ; x < thread_count ; x++) {
    pthread_create(&thread[x], &attr[x], &stream, &logs[x]);
    1248:	48 89 d9             	mov    %rbx,%rcx
    124b:	4c 89 ff             	mov    %r15,%rdi
    124e:	48 89 75 88          	mov    %rsi,-0x78(%rbp)
  for (int x = 0 ; x < thread_count ; x++) {
    1252:	49 83 c7 08          	add    $0x8,%r15
    pthread_create(&thread[x], &attr[x], &stream, &logs[x]);
    1256:	48 8d 15 43 03 00 00 	lea    0x343(%rip),%rdx        # 15a0 <stream>
  for (int x = 0 ; x < thread_count ; x++) {
    125d:	48 83 c3 40          	add    $0x40,%rbx
    pthread_create(&thread[x], &attr[x], &stream, &logs[x]);
    1261:	e8 ca fe ff ff       	call   1130 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    1266:	48 8b 75 88          	mov    -0x78(%rbp),%rsi
    126a:	48 83 c6 38          	add    $0x38,%rsi
    126e:	4d 39 ef             	cmp    %r13,%r15
    1271:	75 d5                	jne    1248 <main+0xe8>
  }
  struct Reader *reader_data = calloc(1, sizeof(pthread_t));
    1273:	be 08 00 00 00       	mov    $0x8,%esi
    1278:	bf 01 00 00 00       	mov    $0x1,%edi
    127d:	e8 7e fe ff ff       	call   1100 <calloc@plt>
  reader_data->others = logptrs;
  reader_data->running = 1;
  reader_data->thread_count = thread_count;
  pthread_t *reader_thread = calloc(1, sizeof(pthread_t));
    1282:	be 08 00 00 00       	mov    $0x8,%esi
    1287:	bf 01 00 00 00       	mov    $0x1,%edi
  struct Reader *reader_data = calloc(1, sizeof(pthread_t));
    128c:	49 89 c7             	mov    %rax,%r15
  reader_data->others = logptrs;
    128f:	4c 89 30             	mov    %r14,(%rax)
  reader_data->running = 1;
    1292:	48 8b 05 e7 0d 00 00 	mov    0xde7(%rip),%rax        # 2080 <_IO_stdin_used+0x80>
    1299:	49 89 47 10          	mov    %rax,0x10(%r15)
  pthread_t *reader_thread = calloc(1, sizeof(pthread_t));
    129d:	e8 5e fe ff ff       	call   1100 <calloc@plt>
  pthread_attr_t      *reader_attr = calloc(1, sizeof(pthread_attr_t));
    12a2:	be 38 00 00 00       	mov    $0x38,%esi
    12a7:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_t *reader_thread = calloc(1, sizeof(pthread_t));
    12ac:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *reader_attr = calloc(1, sizeof(pthread_attr_t));
    12af:	e8 4c fe ff ff       	call   1100 <calloc@plt>
  pthread_create(reader_thread, reader_attr, &reader, reader_data);
    12b4:	4c 89 f9             	mov    %r15,%rcx
    12b7:	48 8d 15 22 04 00 00 	lea    0x422(%rip),%rdx        # 16e0 <reader>
    12be:	4c 89 f7             	mov    %r14,%rdi
  pthread_attr_t      *reader_attr = calloc(1, sizeof(pthread_attr_t));
    12c1:	48 89 c6             	mov    %rax,%rsi
  pthread_create(reader_thread, reader_attr, &reader, reader_data);
    12c4:	e8 67 fe ff ff       	call   1130 <pthread_create@plt>
  
  struct timespec rem2;
  struct timespec preempt = {
    5,
    0 };
  nanosleep(&preempt , &rem2);
    12c9:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    12cd:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
  struct timespec preempt = {
    12d1:	66 0f 6f 05 97 0d 00 00 	movdqa 0xd97(%rip),%xmm0        # 2070 <_IO_stdin_used+0x70>
    12d9:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
  nanosleep(&preempt , &rem2);
    12dd:	e8 0e fe ff ff       	call   10f0 <nanosleep@plt>
  reader_data->running = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    logs[x].running = 0;
    12e2:	48 8b 45 80          	mov    -0x80(%rbp),%rax
  reader_data->running = 0;
    12e6:	41 c7 47 10 00 00 00 00 	movl   $0x0,0x10(%r15)
    logs[x].running = 0;
    12ee:	c7 40 28 00 00 00 00 	movl   $0x0,0x28(%rax)
    12f5:	c7 40 68 00 00 00 00 	movl   $0x0,0x68(%rax)
    12fc:	c7 80 a8 00 00 00 00 00 00 00 	movl   $0x0,0xa8(%rax)
    1306:	c7 80 e8 00 00 00 00 00 00 00 	movl   $0x0,0xe8(%rax)
    1310:	c7 80 28 01 00 00 00 00 00 00 	movl   $0x0,0x128(%rax)
    131a:	c7 80 68 01 00 00 00 00 00 00 	movl   $0x0,0x168(%rax)
    1324:	c7 80 a8 01 00 00 00 00 00 00 	movl   $0x0,0x1a8(%rax)
    132e:	c7 80 e8 01 00 00 00 00 00 00 	movl   $0x0,0x1e8(%rax)
    1338:	c7 80 28 02 00 00 00 00 00 00 	movl   $0x0,0x228(%rax)
    1342:	c7 80 68 02 00 00 00 00 00 00 	movl   $0x0,0x268(%rax)
    134c:	c7 80 a8 02 00 00 00 00 00 00 	movl   $0x0,0x2a8(%rax)
    1356:	c7 80 e8 02 00 00 00 00 00 00 	movl   $0x0,0x2e8(%rax)
  }
  asm volatile ("sfence":::"memory");
    1360:	0f ae f8             	sfence

  void * reader_result; 
  pthread_join(*reader_thread, &reader_result);
    1363:	49 8b 3e             	mov    (%r14),%rdi
    1366:	48 8d 75 90          	lea    -0x70(%rbp),%rsi
    136a:	4c 8d 75 98          	lea    -0x68(%rbp),%r14
    136e:	e8 dd fd ff ff       	call   1150 <pthread_join@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    1373:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    void * result; 
    pthread_join(thread[x], &result);
    1378:	49 8b 3c 24          	mov    (%r12),%rdi
    137c:	4c 89 f6             	mov    %r14,%rsi
  for (int x = 0 ; x < thread_count ; x++) {
    137f:	49 83 c4 08          	add    $0x8,%r12
    pthread_join(thread[x], &result);
    1383:	e8 c8 fd ff ff       	call   1150 <pthread_join@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    1388:	4d 39 ec             	cmp    %r13,%r12
    138b:	75 eb                	jne    1378 <main+0x218>
    138d:	48 8b 45 80          	mov    -0x80(%rbp),%rax
  }
  long mine = 0;
    1391:	45 31 f6             	xor    %r14d,%r14d
    1394:	4c 8d 25 9a 0c 00 00 	lea    0xc9a(%rip),%r12        # 2035 <_IO_stdin_used+0x35>
    139b:	4c 8d 68 04          	lea    0x4(%rax),%r13
    139f:	48 8d 98 04 03 00 00 	lea    0x304(%rax),%rbx
    13a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  for (int x = 0 ; x < thread_count ; x++) {
    long start = 0;
    for (int y  = 0 ; y < logs[x].thread_count ; y++) {
    13b0:	49 63 45 00          	movslq 0x0(%r13),%rax
    long start = 0;
    13b4:	31 ff                	xor    %edi,%edi
    for (int y  = 0 ; y < logs[x].thread_count ; y++) {
    13b6:	85 c0                	test   %eax,%eax
    13b8:	7e 36                	jle    13f0 <main+0x290>
    13ba:	49 8b 4d 04          	mov    0x4(%r13),%rcx
      start += logs[x].others[y]->data[logs[x].others[y]->index % logs[x].data_size];
    13be:	4d 63 45 14          	movslq 0x14(%r13),%r8
    long start = 0;
    13c2:	31 ff                	xor    %edi,%edi
    13c4:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    13c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      start += logs[x].others[y]->data[logs[x].others[y]->index % logs[x].data_size];
    13d0:	48 8b 31             	mov    (%rcx),%rsi
    for (int y  = 0 ; y < logs[x].thread_count ; y++) {
    13d3:	48 83 c1 08          	add    $0x8,%rcx
      start += logs[x].others[y]->data[logs[x].others[y]->index % logs[x].data_size];
    13d7:	48 8b 46 20          	mov    0x20(%rsi),%rax
    13db:	48 99                	cqto
    13dd:	49 f7 f8             	idiv   %r8
    13e0:	48 8b 46 10          	mov    0x10(%rsi),%rax
    13e4:	48 63 04 90          	movslq (%rax,%rdx,4),%rax
    13e8:	48 01 c7             	add    %rax,%rdi
    for (int y  = 0 ; y < logs[x].thread_count ; y++) {
    13eb:	4c 39 c9             	cmp    %r9,%rcx
    13ee:	75 e0                	jne    13d0 <main+0x270>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    13f0:	48 89 fa             	mov    %rdi,%rdx
    13f3:	4c 89 e6             	mov    %r12,%rsi
    13f6:	bf 01 00 00 00       	mov    $0x1,%edi
    13fb:	31 c0                	xor    %eax,%eax
    13fd:	e8 1e fd ff ff       	call   1120 <__printf_chk@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    1402:	49 83 c5 40          	add    $0x40,%r13
    }
    printf("start %ld result\n", start);
    mine += logs[x].mine;
    1406:	4d 03 75 f4          	add    -0xc(%r13),%r14
  for (int x = 0 ; x < thread_count ; x++) {
    140a:	4c 39 eb             	cmp    %r13,%rbx
    140d:	75 a1                	jne    13b0 <main+0x250>
    140f:	31 c0                	xor    %eax,%eax
    1411:	4c 89 f2             	mov    %r14,%rdx
    1414:	bf 01 00 00 00       	mov    $0x1,%edi
    1419:	48 8d 35 27 0c 00 00 	lea    0xc27(%rip),%rsi        # 2047 <_IO_stdin_used+0x47>
    1420:	e8 fb fc ff ff       	call   1120 <__printf_chk@plt>
  }
  printf("mine %ld result\n", mine);
}
    1425:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    1429:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    1432:	75 11                	jne    1445 <main+0x2e5>
    1434:	48 83 c4 58          	add    $0x58,%rsp
    1438:	31 c0                	xor    %eax,%eax
    143a:	5b                   	pop    %rbx
    143b:	41 5c                	pop    %r12
    143d:	41 5d                	pop    %r13
    143f:	41 5e                	pop    %r14
    1441:	41 5f                	pop    %r15
    1443:	5d                   	pop    %rbp
    1444:	c3                   	ret
    1445:	e8 96 fc ff ff       	call   10e0 <__stack_chk_fail@plt>
    144a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001450 <_start>:
    1450:	f3 0f 1e fa          	endbr64
    1454:	31 ed                	xor    %ebp,%ebp
    1456:	49 89 d1             	mov    %rdx,%r9
    1459:	5e                   	pop    %rsi
    145a:	48 89 e2             	mov    %rsp,%rdx
    145d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1461:	50                   	push   %rax
    1462:	54                   	push   %rsp
    1463:	45 31 c0             	xor    %r8d,%r8d
    1466:	31 c9                	xor    %ecx,%ecx
    1468:	48 8d 3d f1 fc ff ff 	lea    -0x30f(%rip),%rdi        # 1160 <main>
    146f:	ff 15 5b 2b 00 00    	call   *0x2b5b(%rip)        # 3fd0 <__libc_start_main@GLIBC_2.34>
    1475:	f4                   	hlt
    1476:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001480 <__gmon_start__>:
    1480:	f3 0f 1e fa          	endbr64
    1484:	8b 05 86 2b 00 00    	mov    0x2b86(%rip),%eax        # 4010 <__TMC_END__>
    148a:	85 c0                	test   %eax,%eax
    148c:	74 02                	je     1490 <__gmon_start__+0x10>
    148e:	c3                   	ret
    148f:	90                   	nop
    1490:	48 83 ec 08          	sub    $0x8,%rsp
    1494:	48 8d 35 82 03 00 00 	lea    0x382(%rip),%rsi        # 181d <etext>
    149b:	48 8d 3d 5e eb ff ff 	lea    -0x14a2(%rip),%rdi        # 0 <__executable_start>
    14a2:	c7 05 64 2b 00 00 01 00 00 00 	movl   $0x1,0x2b64(%rip)        # 4010 <__TMC_END__>
    14ac:	e8 5f fc ff ff       	call   1110 <__monstartup@plt>
    14b1:	48 8b 3d 28 2b 00 00 	mov    0x2b28(%rip),%rdi        # 3fe0 <_mcleanup@GLIBC_2.2.5>
    14b8:	48 83 c4 08          	add    $0x8,%rsp
    14bc:	e9 1f 03 00 00       	jmp    17e0 <atexit>
    14c1:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    14cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000014d0 <_dl_relocate_static_pie>:
    14d0:	f3 0f 1e fa          	endbr64
    14d4:	c3                   	ret
    14d5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    14df:	90                   	nop

00000000000014e0 <deregister_tm_clones>:
    14e0:	48 8d 3d 29 2b 00 00 	lea    0x2b29(%rip),%rdi        # 4010 <__TMC_END__>
    14e7:	48 8d 05 22 2b 00 00 	lea    0x2b22(%rip),%rax        # 4010 <__TMC_END__>
    14ee:	48 39 f8             	cmp    %rdi,%rax
    14f1:	74 15                	je     1508 <deregister_tm_clones+0x28>
    14f3:	48 8b 05 de 2a 00 00 	mov    0x2ade(%rip),%rax        # 3fd8 <_ITM_deregisterTMCloneTable@Base>
    14fa:	48 85 c0             	test   %rax,%rax
    14fd:	74 09                	je     1508 <deregister_tm_clones+0x28>
    14ff:	ff e0                	jmp    *%rax
    1501:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1508:	c3                   	ret
    1509:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001510 <register_tm_clones>:
    1510:	48 8d 3d f9 2a 00 00 	lea    0x2af9(%rip),%rdi        # 4010 <__TMC_END__>
    1517:	48 8d 35 f2 2a 00 00 	lea    0x2af2(%rip),%rsi        # 4010 <__TMC_END__>
    151e:	48 29 fe             	sub    %rdi,%rsi
    1521:	48 89 f0             	mov    %rsi,%rax
    1524:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1528:	48 c1 f8 03          	sar    $0x3,%rax
    152c:	48 01 c6             	add    %rax,%rsi
    152f:	48 d1 fe             	sar    %rsi
    1532:	74 14                	je     1548 <register_tm_clones+0x38>
    1534:	48 8b 05 b5 2a 00 00 	mov    0x2ab5(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    153b:	48 85 c0             	test   %rax,%rax
    153e:	74 08                	je     1548 <register_tm_clones+0x38>
    1540:	ff e0                	jmp    *%rax
    1542:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1548:	c3                   	ret
    1549:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001550 <__do_global_dtors_aux>:
    1550:	f3 0f 1e fa          	endbr64
    1554:	80 3d b9 2a 00 00 00 	cmpb   $0x0,0x2ab9(%rip)        # 4014 <completed.0>
    155b:	75 2b                	jne    1588 <__do_global_dtors_aux+0x38>
    155d:	55                   	push   %rbp
    155e:	48 83 3d 92 2a 00 00 00 	cmpq   $0x0,0x2a92(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1566:	48 89 e5             	mov    %rsp,%rbp
    1569:	74 0c                	je     1577 <__do_global_dtors_aux+0x27>
    156b:	48 8b 3d 96 2a 00 00 	mov    0x2a96(%rip),%rdi        # 4008 <__dso_handle>
    1572:	e8 49 fb ff ff       	call   10c0 <__cxa_finalize@plt>
    1577:	e8 64 ff ff ff       	call   14e0 <deregister_tm_clones>
    157c:	c6 05 91 2a 00 00 01 	movb   $0x1,0x2a91(%rip)        # 4014 <completed.0>
    1583:	5d                   	pop    %rbp
    1584:	c3                   	ret
    1585:	0f 1f 00             	nopl   (%rax)
    1588:	c3                   	ret
    1589:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001590 <frame_dummy>:
    1590:	f3 0f 1e fa          	endbr64
    1594:	e9 77 ff ff ff       	jmp    1510 <register_tm_clones>
    1599:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000015a0 <stream>:
void* stream(void * arg) {
    15a0:	f3 0f 1e fa          	endbr64
    15a4:	55                   	push   %rbp
    15a5:	48 89 e5             	mov    %rsp,%rbp
    15a8:	41 55                	push   %r13
    15aa:	41 54                	push   %r12
    15ac:	53                   	push   %rbx
    15ad:	48 83 ec 08          	sub    $0x8,%rsp
    15b1:	ff 15 31 2a 00 00    	call   *0x2a31(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
    15b7:	48 8d 35 46 0a 00 00 	lea    0xa46(%rip),%rsi        # 2004 <_IO_stdin_used+0x4>
    15be:	31 c0                	xor    %eax,%eax
    15c0:	8b 17                	mov    (%rdi),%edx
    15c2:	48 89 fb             	mov    %rdi,%rbx
    15c5:	bf 01 00 00 00       	mov    $0x1,%edi
    15ca:	e8 51 fb ff ff       	call   1120 <__printf_chk@plt>
  while (log->running) {
    15cf:	8b 4b 28             	mov    0x28(%rbx),%ecx
    15d2:	85 c9                	test   %ecx,%ecx
    15d4:	0f 84 f6 00 00 00    	je     16d0 <stream+0x130>
    for (int x = 0 ; x < log->data_size; x++) {
    15da:	48 63 4b 18          	movslq 0x18(%rbx),%rcx
    log->result = start + log->data[log->index % log->data_size];
    15de:	4c 8b 4b 10          	mov    0x10(%rbx),%r9
    15e2:	4c 8b 5b 20          	mov    0x20(%rbx),%r11
    for (int x = 0 ; x < log->data_size; x++) {
    15e6:	48 89 cf             	mov    %rcx,%rdi
    15e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x  = 0 ; x < log->thread_count ; x++) {
    15f0:	44 8b 6b 04          	mov    0x4(%rbx),%r13d
    long start = 0;
    15f4:	45 31 d2             	xor    %r10d,%r10d
    for (int x  = 0 ; x < log->thread_count ; x++) {
    15f7:	45 85 ed             	test   %r13d,%r13d
    15fa:	7e 34                	jle    1630 <stream+0x90>
    15fc:	48 8b 73 08          	mov    0x8(%rbx),%rsi
    1600:	49 63 c5             	movslq %r13d,%rax
    long start = 0;
    1603:	45 31 d2             	xor    %r10d,%r10d
    1606:	4c 8d 24 c6          	lea    (%rsi,%rax,8),%r12
    160a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      start += log->others[x]->data[log->others[x]->index % log->data_size];
    1610:	4c 8b 06             	mov    (%rsi),%r8
    for (int x  = 0 ; x < log->thread_count ; x++) {
    1613:	48 83 c6 08          	add    $0x8,%rsi
      start += log->others[x]->data[log->others[x]->index % log->data_size];
    1617:	49 8b 40 20          	mov    0x20(%r8),%rax
    161b:	48 99                	cqto
    161d:	48 f7 f9             	idiv   %rcx
    1620:	49 8b 40 10          	mov    0x10(%r8),%rax
    1624:	48 63 04 90          	movslq (%rax,%rdx,4),%rax
    1628:	49 01 c2             	add    %rax,%r10
    for (int x  = 0 ; x < log->thread_count ; x++) {
    162b:	49 39 f4             	cmp    %rsi,%r12
    162e:	75 e0                	jne    1610 <stream+0x70>
    for (int x = 0 ; x < log->data_size; x++) {
    1630:	85 ff                	test   %edi,%edi
    1632:	0f 8e 88 00 00 00    	jle    16c0 <stream+0x120>
    1638:	4c 8b 63 38          	mov    0x38(%rbx),%r12
    163c:	4c 89 de             	mov    %r11,%rsi
    163f:	45 31 c0             	xor    %r8d,%r8d
    1642:	eb 07                	jmp    164b <stream+0xab>
    1644:	0f 1f 40 00          	nopl   0x0(%rax)
    1648:	48 63 cf             	movslq %edi,%rcx
      log->data[(log->index + 1) % log->data_size] = log->data[log->index % log->data_size] + 1;    
    164b:	48 89 f0             	mov    %rsi,%rax
    164e:	48 83 c6 01          	add    $0x1,%rsi
    for (int x = 0 ; x < log->data_size; x++) {
    1652:	41 83 c0 01          	add    $0x1,%r8d
      log->data[(log->index + 1) % log->data_size] = log->data[log->index % log->data_size] + 1;    
    1656:	48 99                	cqto
    1658:	48 f7 f9             	idiv   %rcx
    165b:	48 89 f0             	mov    %rsi,%rax
    165e:	41 8b 3c 91          	mov    (%r9,%rdx,4),%edi
    1662:	48 99                	cqto
    1664:	48 f7 f9             	idiv   %rcx
    1667:	83 c7 01             	add    $0x1,%edi
    166a:	41 89 3c 91          	mov    %edi,(%r9,%rdx,4)
    for (int x = 0 ; x < log->data_size; x++) {
    166e:	8b 7b 18             	mov    0x18(%rbx),%edi
    1671:	44 39 c7             	cmp    %r8d,%edi
    1674:	7f d2                	jg     1648 <stream+0xa8>
    log->result = start + log->data[log->index % log->data_size];
    1676:	48 89 f0             	mov    %rsi,%rax
    1679:	48 63 cf             	movslq %edi,%rcx
      log->mine++;
    167c:	4d 29 dc             	sub    %r11,%r12
    167f:	48 89 73 20          	mov    %rsi,0x20(%rbx)
    log->result = start + log->data[log->index % log->data_size];
    1683:	48 99                	cqto
      log->mine++;
    1685:	49 01 f4             	add    %rsi,%r12
    log->result = start + log->data[log->index % log->data_size];
    1688:	48 f7 f9             	idiv   %rcx
      log->mine++;
    168b:	4c 89 63 38          	mov    %r12,0x38(%rbx)
    log->result = start + log->data[log->index % log->data_size];
    168f:	49 63 04 91          	movslq (%r9,%rdx,4),%rax
  while (log->running) {
    1693:	8b 53 28             	mov    0x28(%rbx),%edx
    1696:	85 d2                	test   %edx,%edx
    1698:	74 14                	je     16ae <stream+0x10e>
    169a:	49 89 f3             	mov    %rsi,%r11
    169d:	e9 4e ff ff ff       	jmp    15f0 <stream+0x50>
    log->result = start + log->data[log->index % log->data_size];
    16a2:	4c 89 d8             	mov    %r11,%rax
    16a5:	48 99                	cqto
    16a7:	48 f7 f9             	idiv   %rcx
    16aa:	49 63 04 91          	movslq (%r9,%rdx,4),%rax
    16ae:	4c 01 d0             	add    %r10,%rax
    16b1:	48 89 43 30          	mov    %rax,0x30(%rbx)
}
    16b5:	48 83 c4 08          	add    $0x8,%rsp
    16b9:	5b                   	pop    %rbx
    16ba:	41 5c                	pop    %r12
    16bc:	41 5d                	pop    %r13
    16be:	5d                   	pop    %rbp
    16bf:	c3                   	ret
  while (log->running) {
    16c0:	8b 43 28             	mov    0x28(%rbx),%eax
    16c3:	85 c0                	test   %eax,%eax
    16c5:	74 db                	je     16a2 <stream+0x102>
    for (int x  = 0 ; x < log->thread_count ; x++) {
    16c7:	45 85 ed             	test   %r13d,%r13d
    16ca:	7e fb                	jle    16c7 <stream+0x127>
    16cc:	eb fe                	jmp    16cc <stream+0x12c>
    16ce:	66 90                	xchg   %ax,%ax
  return (void*)log->result;
    16d0:	48 8b 43 30          	mov    0x30(%rbx),%rax
}
    16d4:	48 83 c4 08          	add    $0x8,%rsp
    16d8:	5b                   	pop    %rbx
    16d9:	41 5c                	pop    %r12
    16db:	41 5d                	pop    %r13
    16dd:	5d                   	pop    %rbp
    16de:	c3                   	ret
    16df:	90                   	nop

00000000000016e0 <reader>:
void* reader(void * arg) {
    16e0:	f3 0f 1e fa          	endbr64
    16e4:	55                   	push   %rbp
    16e5:	48 89 e5             	mov    %rsp,%rbp
    16e8:	41 57                	push   %r15
    16ea:	41 56                	push   %r14
    16ec:	41 55                	push   %r13
    16ee:	41 54                	push   %r12
    16f0:	53                   	push   %rbx
    16f1:	48 83 ec 38          	sub    $0x38,%rsp
    16f5:	ff 15 ed 28 00 00    	call   *0x28ed(%rip)        # 3fe8 <mcount@GLIBC_2.2.5>
  struct Log ** logptrs = reader->others;
    16fb:	48 8b 1f             	mov    (%rdi),%rbx
void* reader(void * arg) {
    16fe:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1707:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    170b:	31 c0                	xor    %eax,%eax
    170d:	49 89 ff             	mov    %rdi,%r15
    1710:	48 8d 3d 04 09 00 00 	lea    0x904(%rip),%rdi        # 201b <_IO_stdin_used+0x1b>
    1717:	e8 b4 f9 ff ff       	call   10d0 <puts@plt>
  while (reader->running == 1) {
    171c:	41 83 7f 10 01       	cmpl   $0x1,0x10(%r15)
    1721:	0f 85 89 00 00 00    	jne    17b0 <reader+0xd0>
    1727:	4c 8d 35 fc 08 00 00 	lea    0x8fc(%rip),%r14        # 202a <_IO_stdin_used+0x2a>
    172e:	4c 8d 6d a0          	lea    -0x60(%rbp),%r13
    1732:	4c 8d 65 b0          	lea    -0x50(%rbp),%r12
    1736:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int x = 0 ; x < reader->thread_count ; x++) {
    1740:	49 63 47 14          	movslq 0x14(%r15),%rax
    long start = 0;
    1744:	45 31 c0             	xor    %r8d,%r8d
    for (int x = 0 ; x < reader->thread_count ; x++) {
    1747:	85 c0                	test   %eax,%eax
    1749:	7e 31                	jle    177c <reader+0x9c>
    174b:	48 89 d9             	mov    %rbx,%rcx
    174e:	4c 8d 0c c3          	lea    (%rbx,%rax,8),%r9
    long start = 0;
    1752:	45 31 c0             	xor    %r8d,%r8d
    1755:	0f 1f 00             	nopl   (%rax)
      start += logptrs[x]->data[logptrs[x]->index % logptrs[x]->data_size];
    1758:	48 8b 31             	mov    (%rcx),%rsi
    for (int x = 0 ; x < reader->thread_count ; x++) {
    175b:	48 83 c1 08          	add    $0x8,%rcx
      start += logptrs[x]->data[logptrs[x]->index % logptrs[x]->data_size];
    175f:	48 8b 46 20          	mov    0x20(%rsi),%rax
    1763:	48 63 7e 18          	movslq 0x18(%rsi),%rdi
    1767:	48 99                	cqto
    1769:	48 f7 ff             	idiv   %rdi
    176c:	48 8b 46 10          	mov    0x10(%rsi),%rax
    1770:	48 63 04 90          	movslq (%rax,%rdx,4),%rax
    1774:	49 01 c0             	add    %rax,%r8
    for (int x = 0 ; x < reader->thread_count ; x++) {
    1777:	49 39 c9             	cmp    %rcx,%r9
    177a:	75 dc                	jne    1758 <reader+0x78>
    reader->value = start;
    177c:	4d 89 47 08          	mov    %r8,0x8(%r15)
    1780:	4c 89 c2             	mov    %r8,%rdx
    1783:	4c 89 f6             	mov    %r14,%rsi
    1786:	bf 01 00 00 00       	mov    $0x1,%edi
    178b:	31 c0                	xor    %eax,%eax
    178d:	e8 8e f9 ff ff       	call   1120 <__printf_chk@plt>
    struct timespec preempt = {
    1792:	66 0f 6f 05 c6 08 00 00 	movdqa 0x8c6(%rip),%xmm0        # 2060 <_IO_stdin_used+0x60>
    nanosleep(&preempt , &rem2);
    179a:	4c 89 ee             	mov    %r13,%rsi
    179d:	4c 89 e7             	mov    %r12,%rdi
    struct timespec preempt = {
    17a0:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
    nanosleep(&preempt , &rem2);
    17a4:	e8 47 f9 ff ff       	call   10f0 <nanosleep@plt>
  while (reader->running == 1) {
    17a9:	41 83 7f 10 01       	cmpl   $0x1,0x10(%r15)
    17ae:	74 90                	je     1740 <reader+0x60>
}
    17b0:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    17b4:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    17bd:	75 11                	jne    17d0 <reader+0xf0>
    17bf:	48 83 c4 38          	add    $0x38,%rsp
    17c3:	31 c0                	xor    %eax,%eax
    17c5:	5b                   	pop    %rbx
    17c6:	41 5c                	pop    %r12
    17c8:	41 5d                	pop    %r13
    17ca:	41 5e                	pop    %r14
    17cc:	41 5f                	pop    %r15
    17ce:	5d                   	pop    %rbp
    17cf:	c3                   	ret
    17d0:	e8 0b f9 ff ff       	call   10e0 <__stack_chk_fail@plt>
    17d5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    17df:	90                   	nop

00000000000017e0 <atexit>:
    17e0:	f3 0f 1e fa          	endbr64
    17e4:	48 8b 15 1d 28 00 00 	mov    0x281d(%rip),%rdx        # 4008 <__dso_handle>
    17eb:	31 f6                	xor    %esi,%esi
    17ed:	e9 4e f9 ff ff       	jmp    1140 <__cxa_atexit@plt>
    17f2:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    17fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000001800 <__stack_chk_fail_local>:
    1800:	f3 0f 1e fa          	endbr64
    1804:	50                   	push   %rax
    1805:	58                   	pop    %rax
    1806:	48 83 ec 08          	sub    $0x8,%rsp
    180a:	e8 d1 f8 ff ff       	call   10e0 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000001810 <_fini>:
    1810:	f3 0f 1e fa          	endbr64
    1814:	48 83 ec 08          	sub    $0x8,%rsp
    1818:	48 83 c4 08          	add    $0x8,%rsp
    181c:	c3                   	ret
