
streampalrel:     file format elf64-x86-64


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
    1020:	ff 35 6a 2f 00 00    	push   0x2f6a(%rip)        # 3f90 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:	ff 25 6c 2f 00 00    	jmp    *0x2f6c(%rip)        # 3f98 <_GLOBAL_OFFSET_TABLE_+0x10>
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

Disassembly of section .plt.got:

00000000000010a0 <__cxa_finalize@plt>:
    10a0:	f3 0f 1e fa          	endbr64
    10a4:	ff 25 4e 2f 00 00    	jmp    *0x2f4e(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    10aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

00000000000010b0 <puts@plt>:
    10b0:	f3 0f 1e fa          	endbr64
    10b4:	ff 25 e6 2e 00 00    	jmp    *0x2ee6(%rip)        # 3fa0 <puts@GLIBC_2.2.5>
    10ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010c0 <__stack_chk_fail@plt>:
    10c0:	f3 0f 1e fa          	endbr64
    10c4:	ff 25 de 2e 00 00    	jmp    *0x2ede(%rip)        # 3fa8 <__stack_chk_fail@GLIBC_2.4>
    10ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010d0 <nanosleep@plt>:
    10d0:	f3 0f 1e fa          	endbr64
    10d4:	ff 25 d6 2e 00 00    	jmp    *0x2ed6(%rip)        # 3fb0 <nanosleep@GLIBC_2.2.5>
    10da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010e0 <calloc@plt>:
    10e0:	f3 0f 1e fa          	endbr64
    10e4:	ff 25 ce 2e 00 00    	jmp    *0x2ece(%rip)        # 3fb8 <calloc@GLIBC_2.2.5>
    10ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000010f0 <__printf_chk@plt>:
    10f0:	f3 0f 1e fa          	endbr64
    10f4:	ff 25 c6 2e 00 00    	jmp    *0x2ec6(%rip)        # 3fc0 <__printf_chk@GLIBC_2.3.4>
    10fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001100 <pthread_create@plt>:
    1100:	f3 0f 1e fa          	endbr64
    1104:	ff 25 be 2e 00 00    	jmp    *0x2ebe(%rip)        # 3fc8 <pthread_create@GLIBC_2.34>
    110a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000001110 <pthread_join@plt>:
    1110:	f3 0f 1e fa          	endbr64
    1114:	ff 25 b6 2e 00 00    	jmp    *0x2eb6(%rip)        # 3fd0 <pthread_join@GLIBC_2.34>
    111a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000001120 <main>:
  }
  
  return (void*)log->result;
}

int main() {
    1120:	f3 0f 1e fa          	endbr64
    1124:	41 57                	push   %r15
  int thread_count = 12; 
  int total_threads = thread_count;
  int data_size = 1000000;

  struct Log * logs = calloc(thread_count, sizeof(struct Log));
    1126:	be 40 00 00 00       	mov    $0x40,%esi
    112b:	bf 0c 00 00 00       	mov    $0xc,%edi
int main() {
    1130:	41 56                	push   %r14
    1132:	41 55                	push   %r13
    1134:	41 54                	push   %r12
  struct Log ** logptrs = calloc(thread_count, sizeof(struct Log*));
    1136:	45 31 e4             	xor    %r12d,%r12d
int main() {
    1139:	55                   	push   %rbp
    113a:	53                   	push   %rbx
    113b:	48 83 ec 58          	sub    $0x58,%rsp
    113f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1148:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    114d:	31 c0                	xor    %eax,%eax
  struct Log * logs = calloc(thread_count, sizeof(struct Log));
    114f:	e8 8c ff ff ff       	call   10e0 <calloc@plt>
  struct Log ** logptrs = calloc(thread_count, sizeof(struct Log*));
    1154:	be 08 00 00 00       	mov    $0x8,%esi
    1159:	bf 0c 00 00 00       	mov    $0xc,%edi
  struct Log * logs = calloc(thread_count, sizeof(struct Log));
    115e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    1163:	48 89 c5             	mov    %rax,%rbp
  struct Log ** logptrs = calloc(thread_count, sizeof(struct Log*));
    1166:	e8 75 ff ff ff       	call   10e0 <calloc@plt>
    116b:	49 89 c5             	mov    %rax,%r13
  for (int x = 0 ; x < thread_count ; x++) {
    116e:	66 90                	xchg   %ax,%ax
    logs[x].running = 1;
    logs[x].thread_index = x;
    1170:	44 89 65 00          	mov    %r12d,0x0(%rbp)
    logs[x].data_size = data_size;
    logs[x].thread_count = thread_count;
    logs[x].data = calloc(data_size, sizeof(int));
    1174:	be 04 00 00 00       	mov    $0x4,%esi
    1179:	bf 40 42 0f 00       	mov    $0xf4240,%edi
    logs[x].running = 1;
    117e:	c7 45 28 01 00 00 00 	movl   $0x1,0x28(%rbp)
    logs[x].data_size = data_size;
    1185:	c7 45 18 40 42 0f 00 	movl   $0xf4240,0x18(%rbp)
    logs[x].thread_count = thread_count;
    118c:	c7 45 04 0c 00 00 00 	movl   $0xc,0x4(%rbp)
    logs[x].data = calloc(data_size, sizeof(int));
    1193:	e8 48 ff ff ff       	call   10e0 <calloc@plt>
    logs[x].data[0] = 1;
    logs[x].mine = 1;
    logs[x].others = logptrs;
    logptrs[x] = &logs[x];
    1198:	4b 89 6c e5 00       	mov    %rbp,0x0(%r13,%r12,8)
  for (int x = 0 ; x < thread_count ; x++) {
    119d:	49 83 c4 01          	add    $0x1,%r12
    11a1:	48 83 c5 40          	add    $0x40,%rbp
    logs[x].data = calloc(data_size, sizeof(int));
    11a5:	48 89 45 d0          	mov    %rax,-0x30(%rbp)
    logs[x].mine = 1;
    11a9:	48 c7 45 f8 01 00 00 00 	movq   $0x1,-0x8(%rbp)
    logs[x].others = logptrs;
    11b1:	4c 89 6d c8          	mov    %r13,-0x38(%rbp)
    logs[x].data[0] = 1;
    11b5:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  for (int x = 0 ; x < thread_count ; x++) {
    11bb:	49 83 fc 0c          	cmp    $0xc,%r12
    11bf:	75 af                	jne    1170 <main+0x50>
  }
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    11c1:	be 08 00 00 00       	mov    $0x8,%esi
    11c6:	bf 0c 00 00 00       	mov    $0xc,%edi
    11cb:	e8 10 ff ff ff       	call   10e0 <calloc@plt>
  pthread_attr_t      *attr = calloc(total_threads, sizeof(pthread_attr_t));
    11d0:	be 38 00 00 00       	mov    $0x38,%esi
    11d5:	bf 0c 00 00 00       	mov    $0xc,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    11da:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *attr = calloc(total_threads, sizeof(pthread_attr_t));
    11dd:	e8 fe fe ff ff       	call   10e0 <calloc@plt>
    11e2:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    11e7:	4c 8d 75 60          	lea    0x60(%rbp),%r14
    11eb:	49 89 ec             	mov    %rbp,%r12
    11ee:	48 89 c3             	mov    %rax,%rbx
    11f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

  for (int x = 0 ; x < thread_count ; x++) {
    pthread_create(&thread[x], &attr[x], &stream, &logs[x]);
    11f8:	4c 89 f9             	mov    %r15,%rcx
    11fb:	48 89 de             	mov    %rbx,%rsi
    11fe:	4c 89 e7             	mov    %r12,%rdi
  for (int x = 0 ; x < thread_count ; x++) {
    1201:	49 83 c4 08          	add    $0x8,%r12
    pthread_create(&thread[x], &attr[x], &stream, &logs[x]);
    1205:	48 8d 15 e4 02 00 00 	lea    0x2e4(%rip),%rdx        # 14f0 <stream>
  for (int x = 0 ; x < thread_count ; x++) {
    120c:	48 83 c3 38          	add    $0x38,%rbx
    1210:	49 83 c7 40          	add    $0x40,%r15
    pthread_create(&thread[x], &attr[x], &stream, &logs[x]);
    1214:	e8 e7 fe ff ff       	call   1100 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    1219:	4d 39 f4             	cmp    %r14,%r12
    121c:	75 da                	jne    11f8 <main+0xd8>
  }
  struct Reader *reader_data = calloc(1, sizeof(pthread_t));
    121e:	be 08 00 00 00       	mov    $0x8,%esi
    1223:	bf 01 00 00 00       	mov    $0x1,%edi
    1228:	e8 b3 fe ff ff       	call   10e0 <calloc@plt>
  reader_data->others = logptrs;
  reader_data->running = 1;
  reader_data->thread_count = thread_count;
  pthread_t *reader_thread = calloc(1, sizeof(pthread_t));
    122d:	be 08 00 00 00       	mov    $0x8,%esi
    1232:	bf 01 00 00 00       	mov    $0x1,%edi
  struct Reader *reader_data = calloc(1, sizeof(pthread_t));
    1237:	49 89 c4             	mov    %rax,%r12
  reader_data->others = logptrs;
    123a:	4c 89 28             	mov    %r13,(%rax)
  reader_data->running = 1;
    123d:	48 8b 05 3c 0e 00 00 	mov    0xe3c(%rip),%rax        # 2080 <_IO_stdin_used+0x80>
    1244:	49 89 44 24 10       	mov    %rax,0x10(%r12)
  pthread_t *reader_thread = calloc(1, sizeof(pthread_t));
    1249:	e8 92 fe ff ff       	call   10e0 <calloc@plt>
  pthread_attr_t      *reader_attr = calloc(1, sizeof(pthread_attr_t));
    124e:	be 38 00 00 00       	mov    $0x38,%esi
    1253:	bf 01 00 00 00       	mov    $0x1,%edi
  pthread_t *reader_thread = calloc(1, sizeof(pthread_t));
    1258:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *reader_attr = calloc(1, sizeof(pthread_attr_t));
    125b:	e8 80 fe ff ff       	call   10e0 <calloc@plt>
  pthread_create(reader_thread, reader_attr, &reader, reader_data);
    1260:	4c 89 e1             	mov    %r12,%rcx
    1263:	48 8d 15 b6 03 00 00 	lea    0x3b6(%rip),%rdx        # 1620 <reader>
    126a:	4c 89 ef             	mov    %r13,%rdi
  pthread_attr_t      *reader_attr = calloc(1, sizeof(pthread_attr_t));
    126d:	48 89 c6             	mov    %rax,%rsi
  pthread_create(reader_thread, reader_attr, &reader, reader_data);
    1270:	e8 8b fe ff ff       	call   1100 <pthread_create@plt>
  
  struct timespec rem2;
  struct timespec preempt = {
    5,
    0 };
  nanosleep(&preempt , &rem2);
    1275:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    127a:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
  struct timespec preempt = {
    127f:	66 0f 6f 05 e9 0d 00 00 	movdqa 0xde9(%rip),%xmm0        # 2070 <_IO_stdin_used+0x70>
    1287:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  nanosleep(&preempt , &rem2);
    128c:	e8 3f fe ff ff       	call   10d0 <nanosleep@plt>
  reader_data->running = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    logs[x].running = 0;
    1291:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  reader_data->running = 0;
    1296:	41 c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%r12)
    logs[x].running = 0;
    129f:	c7 40 28 00 00 00 00 	movl   $0x0,0x28(%rax)
    12a6:	c7 40 68 00 00 00 00 	movl   $0x0,0x68(%rax)
    12ad:	c7 80 a8 00 00 00 00 00 00 00 	movl   $0x0,0xa8(%rax)
    12b7:	c7 80 e8 00 00 00 00 00 00 00 	movl   $0x0,0xe8(%rax)
    12c1:	c7 80 28 01 00 00 00 00 00 00 	movl   $0x0,0x128(%rax)
    12cb:	c7 80 68 01 00 00 00 00 00 00 	movl   $0x0,0x168(%rax)
    12d5:	c7 80 a8 01 00 00 00 00 00 00 	movl   $0x0,0x1a8(%rax)
    12df:	c7 80 e8 01 00 00 00 00 00 00 	movl   $0x0,0x1e8(%rax)
    12e9:	c7 80 28 02 00 00 00 00 00 00 	movl   $0x0,0x228(%rax)
    12f3:	c7 80 68 02 00 00 00 00 00 00 	movl   $0x0,0x268(%rax)
    12fd:	c7 80 a8 02 00 00 00 00 00 00 	movl   $0x0,0x2a8(%rax)
    1307:	c7 80 e8 02 00 00 00 00 00 00 	movl   $0x0,0x2e8(%rax)
  }
  asm volatile ("sfence":::"memory");
    1311:	0f ae f8             	sfence

  void * reader_result; 
  pthread_join(*reader_thread, &reader_result);
    1314:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    1318:	48 8d 74 24 10       	lea    0x10(%rsp),%rsi
    131d:	4c 8d 64 24 18       	lea    0x18(%rsp),%r12
    1322:	e8 e9 fd ff ff       	call   1110 <pthread_join@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    1327:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    void * result; 
    pthread_join(thread[x], &result);
    1330:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    1334:	4c 89 e6             	mov    %r12,%rsi
  for (int x = 0 ; x < thread_count ; x++) {
    1337:	48 83 c5 08          	add    $0x8,%rbp
    pthread_join(thread[x], &result);
    133b:	e8 d0 fd ff ff       	call   1110 <pthread_join@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    1340:	4c 39 f5             	cmp    %r14,%rbp
    1343:	75 eb                	jne    1330 <main+0x210>
    1345:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  }
  long mine = 0;
    134a:	45 31 ed             	xor    %r13d,%r13d
    134d:	48 8d 2d e1 0c 00 00 	lea    0xce1(%rip),%rbp        # 2035 <_IO_stdin_used+0x35>
    1354:	4c 8d 60 04          	lea    0x4(%rax),%r12
    1358:	48 8d 98 04 03 00 00 	lea    0x304(%rax),%rbx
    135f:	90                   	nop
  for (int x = 0 ; x < thread_count ; x++) {
    long start = 0;
    for (int y  = 0 ; y < logs[x].thread_count ; y++) {
    1360:	49 63 04 24          	movslq (%r12),%rax
    long start = 0;
    1364:	31 ff                	xor    %edi,%edi
    for (int y  = 0 ; y < logs[x].thread_count ; y++) {
    1366:	85 c0                	test   %eax,%eax
    1368:	7e 36                	jle    13a0 <main+0x280>
    136a:	49 8b 4c 24 04       	mov    0x4(%r12),%rcx
      start += logs[x].others[y]->data[logs[x].others[y]->index % logs[x].data_size];
    136f:	4d 63 44 24 14       	movslq 0x14(%r12),%r8
    long start = 0;
    1374:	31 ff                	xor    %edi,%edi
    1376:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    137a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      start += logs[x].others[y]->data[logs[x].others[y]->index % logs[x].data_size];
    1380:	48 8b 31             	mov    (%rcx),%rsi
    for (int y  = 0 ; y < logs[x].thread_count ; y++) {
    1383:	48 83 c1 08          	add    $0x8,%rcx
      start += logs[x].others[y]->data[logs[x].others[y]->index % logs[x].data_size];
    1387:	48 8b 46 20          	mov    0x20(%rsi),%rax
    138b:	48 99                	cqto
    138d:	49 f7 f8             	idiv   %r8
    1390:	48 8b 46 10          	mov    0x10(%rsi),%rax
    1394:	48 63 04 90          	movslq (%rax,%rdx,4),%rax
    1398:	48 01 c7             	add    %rax,%rdi
    for (int y  = 0 ; y < logs[x].thread_count ; y++) {
    139b:	4c 39 c9             	cmp    %r9,%rcx
    139e:	75 e0                	jne    1380 <main+0x260>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    13a0:	48 89 fa             	mov    %rdi,%rdx
    13a3:	48 89 ee             	mov    %rbp,%rsi
    13a6:	bf 01 00 00 00       	mov    $0x1,%edi
    13ab:	31 c0                	xor    %eax,%eax
    13ad:	e8 3e fd ff ff       	call   10f0 <__printf_chk@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    13b2:	49 83 c4 40          	add    $0x40,%r12
    }
    printf("start %ld result\n", start);
    mine += logs[x].mine;
    13b6:	4d 03 6c 24 f4       	add    -0xc(%r12),%r13
  for (int x = 0 ; x < thread_count ; x++) {
    13bb:	4c 39 e3             	cmp    %r12,%rbx
    13be:	75 a0                	jne    1360 <main+0x240>
    13c0:	31 c0                	xor    %eax,%eax
    13c2:	4c 89 ea             	mov    %r13,%rdx
    13c5:	bf 01 00 00 00       	mov    $0x1,%edi
    13ca:	48 8d 35 76 0c 00 00 	lea    0xc76(%rip),%rsi        # 2047 <_IO_stdin_used+0x47>
    13d1:	e8 1a fd ff ff       	call   10f0 <__printf_chk@plt>
  }
  printf("mine %ld result\n", mine);
}
    13d6:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    13db:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    13e4:	75 11                	jne    13f7 <main+0x2d7>
    13e6:	48 83 c4 58          	add    $0x58,%rsp
    13ea:	31 c0                	xor    %eax,%eax
    13ec:	5b                   	pop    %rbx
    13ed:	5d                   	pop    %rbp
    13ee:	41 5c                	pop    %r12
    13f0:	41 5d                	pop    %r13
    13f2:	41 5e                	pop    %r14
    13f4:	41 5f                	pop    %r15
    13f6:	c3                   	ret
    13f7:	e8 c4 fc ff ff       	call   10c0 <__stack_chk_fail@plt>
    13fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000001400 <_start>:
    1400:	f3 0f 1e fa          	endbr64
    1404:	31 ed                	xor    %ebp,%ebp
    1406:	49 89 d1             	mov    %rdx,%r9
    1409:	5e                   	pop    %rsi
    140a:	48 89 e2             	mov    %rsp,%rdx
    140d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    1411:	50                   	push   %rax
    1412:	54                   	push   %rsp
    1413:	45 31 c0             	xor    %r8d,%r8d
    1416:	31 c9                	xor    %ecx,%ecx
    1418:	48 8d 3d 01 fd ff ff 	lea    -0x2ff(%rip),%rdi        # 1120 <main>
    141f:	ff 15 b3 2b 00 00    	call   *0x2bb3(%rip)        # 3fd8 <__libc_start_main@GLIBC_2.34>
    1425:	f4                   	hlt
    1426:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000001430 <deregister_tm_clones>:
    1430:	48 8d 3d d9 2b 00 00 	lea    0x2bd9(%rip),%rdi        # 4010 <__TMC_END__>
    1437:	48 8d 05 d2 2b 00 00 	lea    0x2bd2(%rip),%rax        # 4010 <__TMC_END__>
    143e:	48 39 f8             	cmp    %rdi,%rax
    1441:	74 15                	je     1458 <deregister_tm_clones+0x28>
    1443:	48 8b 05 96 2b 00 00 	mov    0x2b96(%rip),%rax        # 3fe0 <_ITM_deregisterTMCloneTable@Base>
    144a:	48 85 c0             	test   %rax,%rax
    144d:	74 09                	je     1458 <deregister_tm_clones+0x28>
    144f:	ff e0                	jmp    *%rax
    1451:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    1458:	c3                   	ret
    1459:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001460 <register_tm_clones>:
    1460:	48 8d 3d a9 2b 00 00 	lea    0x2ba9(%rip),%rdi        # 4010 <__TMC_END__>
    1467:	48 8d 35 a2 2b 00 00 	lea    0x2ba2(%rip),%rsi        # 4010 <__TMC_END__>
    146e:	48 29 fe             	sub    %rdi,%rsi
    1471:	48 89 f0             	mov    %rsi,%rax
    1474:	48 c1 ee 3f          	shr    $0x3f,%rsi
    1478:	48 c1 f8 03          	sar    $0x3,%rax
    147c:	48 01 c6             	add    %rax,%rsi
    147f:	48 d1 fe             	sar    %rsi
    1482:	74 14                	je     1498 <register_tm_clones+0x38>
    1484:	48 8b 05 65 2b 00 00 	mov    0x2b65(%rip),%rax        # 3ff0 <_ITM_registerTMCloneTable@Base>
    148b:	48 85 c0             	test   %rax,%rax
    148e:	74 08                	je     1498 <register_tm_clones+0x38>
    1490:	ff e0                	jmp    *%rax
    1492:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    1498:	c3                   	ret
    1499:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000014a0 <__do_global_dtors_aux>:
    14a0:	f3 0f 1e fa          	endbr64
    14a4:	80 3d 65 2b 00 00 00 	cmpb   $0x0,0x2b65(%rip)        # 4010 <__TMC_END__>
    14ab:	75 2b                	jne    14d8 <__do_global_dtors_aux+0x38>
    14ad:	55                   	push   %rbp
    14ae:	48 83 3d 42 2b 00 00 00 	cmpq   $0x0,0x2b42(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    14b6:	48 89 e5             	mov    %rsp,%rbp
    14b9:	74 0c                	je     14c7 <__do_global_dtors_aux+0x27>
    14bb:	48 8b 3d 46 2b 00 00 	mov    0x2b46(%rip),%rdi        # 4008 <__dso_handle>
    14c2:	e8 d9 fb ff ff       	call   10a0 <__cxa_finalize@plt>
    14c7:	e8 64 ff ff ff       	call   1430 <deregister_tm_clones>
    14cc:	c6 05 3d 2b 00 00 01 	movb   $0x1,0x2b3d(%rip)        # 4010 <__TMC_END__>
    14d3:	5d                   	pop    %rbp
    14d4:	c3                   	ret
    14d5:	0f 1f 00             	nopl   (%rax)
    14d8:	c3                   	ret
    14d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000014e0 <frame_dummy>:
    14e0:	f3 0f 1e fa          	endbr64
    14e4:	e9 77 ff ff ff       	jmp    1460 <register_tm_clones>
    14e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000014f0 <stream>:
void* stream(void * arg) {
    14f0:	f3 0f 1e fa          	endbr64
    14f4:	41 54                	push   %r12
    14f6:	48 8d 35 07 0b 00 00 	lea    0xb07(%rip),%rsi        # 2004 <_IO_stdin_used+0x4>
    14fd:	31 c0                	xor    %eax,%eax
    14ff:	55                   	push   %rbp
    1500:	53                   	push   %rbx
    1501:	8b 17                	mov    (%rdi),%edx
    1503:	48 89 fb             	mov    %rdi,%rbx
    1506:	bf 01 00 00 00       	mov    $0x1,%edi
    150b:	e8 e0 fb ff ff       	call   10f0 <__printf_chk@plt>
  while (log->running) {
    1510:	8b 4b 28             	mov    0x28(%rbx),%ecx
    1513:	85 c9                	test   %ecx,%ecx
    1515:	0f 84 f5 00 00 00    	je     1610 <stream+0x120>
    for (int x = 0 ; x < log->data_size; x++) {
    151b:	48 63 4b 18          	movslq 0x18(%rbx),%rcx
    log->result = start + log->data[log->index % log->data_size];
    151f:	4c 8b 4b 10          	mov    0x10(%rbx),%r9
    1523:	4c 8b 5b 20          	mov    0x20(%rbx),%r11
    for (int x = 0 ; x < log->data_size; x++) {
    1527:	48 89 cf             	mov    %rcx,%rdi
    152a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x  = 0 ; x < log->thread_count ; x++) {
    1530:	44 8b 63 04          	mov    0x4(%rbx),%r12d
    long start = 0;
    1534:	45 31 d2             	xor    %r10d,%r10d
    for (int x  = 0 ; x < log->thread_count ; x++) {
    1537:	45 85 e4             	test   %r12d,%r12d
    153a:	7e 34                	jle    1570 <stream+0x80>
    153c:	48 8b 73 08          	mov    0x8(%rbx),%rsi
    1540:	49 63 c4             	movslq %r12d,%rax
    long start = 0;
    1543:	45 31 d2             	xor    %r10d,%r10d
    1546:	48 8d 2c c6          	lea    (%rsi,%rax,8),%rbp
    154a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      start += log->others[x]->data[log->others[x]->index % log->data_size];
    1550:	4c 8b 06             	mov    (%rsi),%r8
    for (int x  = 0 ; x < log->thread_count ; x++) {
    1553:	48 83 c6 08          	add    $0x8,%rsi
      start += log->others[x]->data[log->others[x]->index % log->data_size];
    1557:	49 8b 40 20          	mov    0x20(%r8),%rax
    155b:	48 99                	cqto
    155d:	48 f7 f9             	idiv   %rcx
    1560:	49 8b 40 10          	mov    0x10(%r8),%rax
    1564:	48 63 04 90          	movslq (%rax,%rdx,4),%rax
    1568:	49 01 c2             	add    %rax,%r10
    for (int x  = 0 ; x < log->thread_count ; x++) {
    156b:	48 39 f5             	cmp    %rsi,%rbp
    156e:	75 e0                	jne    1550 <stream+0x60>
    for (int x = 0 ; x < log->data_size; x++) {
    1570:	85 ff                	test   %edi,%edi
    1572:	0f 8e 88 00 00 00    	jle    1600 <stream+0x110>
    1578:	48 8b 6b 38          	mov    0x38(%rbx),%rbp
    157c:	4c 89 de             	mov    %r11,%rsi
    157f:	45 31 c0             	xor    %r8d,%r8d
    1582:	eb 07                	jmp    158b <stream+0x9b>
    1584:	0f 1f 40 00          	nopl   0x0(%rax)
    1588:	48 63 cf             	movslq %edi,%rcx
      log->data[(log->index + 1) % log->data_size] = log->data[log->index % log->data_size] + 1;    
    158b:	48 89 f0             	mov    %rsi,%rax
    158e:	48 83 c6 01          	add    $0x1,%rsi
    for (int x = 0 ; x < log->data_size; x++) {
    1592:	41 83 c0 01          	add    $0x1,%r8d
      log->data[(log->index + 1) % log->data_size] = log->data[log->index % log->data_size] + 1;    
    1596:	48 99                	cqto
    1598:	48 f7 f9             	idiv   %rcx
    159b:	48 89 f0             	mov    %rsi,%rax
    159e:	41 8b 3c 91          	mov    (%r9,%rdx,4),%edi
    15a2:	48 99                	cqto
    15a4:	48 f7 f9             	idiv   %rcx
    15a7:	83 c7 01             	add    $0x1,%edi
    15aa:	41 89 3c 91          	mov    %edi,(%r9,%rdx,4)
    for (int x = 0 ; x < log->data_size; x++) {
    15ae:	8b 7b 18             	mov    0x18(%rbx),%edi
    15b1:	44 39 c7             	cmp    %r8d,%edi
    15b4:	7f d2                	jg     1588 <stream+0x98>
    log->result = start + log->data[log->index % log->data_size];
    15b6:	48 89 f0             	mov    %rsi,%rax
    15b9:	48 63 cf             	movslq %edi,%rcx
      log->mine++;
    15bc:	4c 29 dd             	sub    %r11,%rbp
    15bf:	48 89 73 20          	mov    %rsi,0x20(%rbx)
    log->result = start + log->data[log->index % log->data_size];
    15c3:	48 99                	cqto
      log->mine++;
    15c5:	48 01 f5             	add    %rsi,%rbp
    log->result = start + log->data[log->index % log->data_size];
    15c8:	48 f7 f9             	idiv   %rcx
      log->mine++;
    15cb:	48 89 6b 38          	mov    %rbp,0x38(%rbx)
    log->result = start + log->data[log->index % log->data_size];
    15cf:	49 63 04 91          	movslq (%r9,%rdx,4),%rax
  while (log->running) {
    15d3:	8b 53 28             	mov    0x28(%rbx),%edx
    15d6:	85 d2                	test   %edx,%edx
    15d8:	74 14                	je     15ee <stream+0xfe>
    15da:	49 89 f3             	mov    %rsi,%r11
    15dd:	e9 4e ff ff ff       	jmp    1530 <stream+0x40>
    log->result = start + log->data[log->index % log->data_size];
    15e2:	4c 89 d8             	mov    %r11,%rax
    15e5:	48 99                	cqto
    15e7:	48 f7 f9             	idiv   %rcx
    15ea:	49 63 04 91          	movslq (%r9,%rdx,4),%rax
    15ee:	4c 01 d0             	add    %r10,%rax
    15f1:	48 89 43 30          	mov    %rax,0x30(%rbx)
}
    15f5:	5b                   	pop    %rbx
    15f6:	5d                   	pop    %rbp
    15f7:	41 5c                	pop    %r12
    15f9:	c3                   	ret
    15fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  while (log->running) {
    1600:	8b 43 28             	mov    0x28(%rbx),%eax
    1603:	85 c0                	test   %eax,%eax
    1605:	74 db                	je     15e2 <stream+0xf2>
    for (int x  = 0 ; x < log->thread_count ; x++) {
    1607:	45 85 e4             	test   %r12d,%r12d
    160a:	7e fb                	jle    1607 <stream+0x117>
    160c:	eb fe                	jmp    160c <stream+0x11c>
    160e:	66 90                	xchg   %ax,%ax
  return (void*)log->result;
    1610:	48 8b 43 30          	mov    0x30(%rbx),%rax
}
    1614:	5b                   	pop    %rbx
    1615:	5d                   	pop    %rbp
    1616:	41 5c                	pop    %r12
    1618:	c3                   	ret
    1619:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000001620 <reader>:
void* reader(void * arg) {
    1620:	f3 0f 1e fa          	endbr64
    1624:	41 56                	push   %r14
    1626:	49 89 fe             	mov    %rdi,%r14
    1629:	41 55                	push   %r13
    162b:	41 54                	push   %r12
    162d:	55                   	push   %rbp
    162e:	53                   	push   %rbx
    162f:	48 83 ec 30          	sub    $0x30,%rsp
  struct Log ** logptrs = reader->others;
    1633:	48 8b 1f             	mov    (%rdi),%rbx
    1636:	48 8d 3d de 09 00 00 	lea    0x9de(%rip),%rdi        # 201b <_IO_stdin_used+0x1b>
void* reader(void * arg) {
    163d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    1646:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    164b:	31 c0                	xor    %eax,%eax
    164d:	e8 5e fa ff ff       	call   10b0 <puts@plt>
  while (reader->running == 1) {
    1652:	41 83 7e 10 01       	cmpl   $0x1,0x10(%r14)
    1657:	0f 85 84 00 00 00    	jne    16e1 <reader+0xc1>
    165d:	4c 8d 2d c6 09 00 00 	lea    0x9c6(%rip),%r13        # 202a <_IO_stdin_used+0x2a>
    1664:	49 89 e4             	mov    %rsp,%r12
    1667:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    166c:	0f 1f 40 00          	nopl   0x0(%rax)
    for (int x = 0 ; x < reader->thread_count ; x++) {
    1670:	49 63 46 14          	movslq 0x14(%r14),%rax
    long start = 0;
    1674:	45 31 c0             	xor    %r8d,%r8d
    for (int x = 0 ; x < reader->thread_count ; x++) {
    1677:	85 c0                	test   %eax,%eax
    1679:	7e 31                	jle    16ac <reader+0x8c>
    167b:	48 89 d9             	mov    %rbx,%rcx
    167e:	4c 8d 0c c3          	lea    (%rbx,%rax,8),%r9
    long start = 0;
    1682:	45 31 c0             	xor    %r8d,%r8d
    1685:	0f 1f 00             	nopl   (%rax)
      start += logptrs[x]->data[logptrs[x]->index % logptrs[x]->data_size];
    1688:	48 8b 31             	mov    (%rcx),%rsi
    for (int x = 0 ; x < reader->thread_count ; x++) {
    168b:	48 83 c1 08          	add    $0x8,%rcx
      start += logptrs[x]->data[logptrs[x]->index % logptrs[x]->data_size];
    168f:	48 8b 46 20          	mov    0x20(%rsi),%rax
    1693:	48 63 7e 18          	movslq 0x18(%rsi),%rdi
    1697:	48 99                	cqto
    1699:	48 f7 ff             	idiv   %rdi
    169c:	48 8b 46 10          	mov    0x10(%rsi),%rax
    16a0:	48 63 04 90          	movslq (%rax,%rdx,4),%rax
    16a4:	49 01 c0             	add    %rax,%r8
    for (int x = 0 ; x < reader->thread_count ; x++) {
    16a7:	49 39 c9             	cmp    %rcx,%r9
    16aa:	75 dc                	jne    1688 <reader+0x68>
    reader->value = start;
    16ac:	4d 89 46 08          	mov    %r8,0x8(%r14)
    16b0:	4c 89 c2             	mov    %r8,%rdx
    16b3:	4c 89 ee             	mov    %r13,%rsi
    16b6:	bf 01 00 00 00       	mov    $0x1,%edi
    16bb:	31 c0                	xor    %eax,%eax
    16bd:	e8 2e fa ff ff       	call   10f0 <__printf_chk@plt>
    struct timespec preempt = {
    16c2:	66 0f 6f 05 96 09 00 00 	movdqa 0x996(%rip),%xmm0        # 2060 <_IO_stdin_used+0x60>
    nanosleep(&preempt , &rem2);
    16ca:	4c 89 e6             	mov    %r12,%rsi
    16cd:	48 89 ef             	mov    %rbp,%rdi
    struct timespec preempt = {
    16d0:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    nanosleep(&preempt , &rem2);
    16d5:	e8 f6 f9 ff ff       	call   10d0 <nanosleep@plt>
  while (reader->running == 1) {
    16da:	41 83 7e 10 01       	cmpl   $0x1,0x10(%r14)
    16df:	74 8f                	je     1670 <reader+0x50>
}
    16e1:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    16e6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    16ef:	75 0f                	jne    1700 <reader+0xe0>
    16f1:	48 83 c4 30          	add    $0x30,%rsp
    16f5:	31 c0                	xor    %eax,%eax
    16f7:	5b                   	pop    %rbx
    16f8:	5d                   	pop    %rbp
    16f9:	41 5c                	pop    %r12
    16fb:	41 5d                	pop    %r13
    16fd:	41 5e                	pop    %r14
    16ff:	c3                   	ret
    1700:	e8 bb f9 ff ff       	call   10c0 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000001708 <_fini>:
    1708:	f3 0f 1e fa          	endbr64
    170c:	48 83 ec 08          	sub    $0x8,%rsp
    1710:	48 83 c4 08          	add    $0x8,%rsp
    1714:	c3                   	ret
