
disruptor-multi-consumer:     file format elf64-x86-64


Disassembly of section .init:

0000000000401000 <_init>:
  401000:	f3 0f 1e fa          	endbr64
  401004:	48 83 ec 08          	sub    $0x8,%rsp
  401008:	48 8b 05 e9 2f 00 00 	mov    0x2fe9(%rip),%rax        # 403ff8 <__gmon_start__@Base>
  40100f:	48 85 c0             	test   %rax,%rax
  401012:	74 02                	je     401016 <_init+0x16>
  401014:	ff d0                	call   *%rax
  401016:	48 83 c4 08          	add    $0x8,%rsp
  40101a:	c3                   	ret

Disassembly of section .plt:

0000000000401020 <pthread_setaffinity_np@plt-0x10>:
  401020:	ff 35 5a 2f 00 00    	push   0x2f5a(%rip)        # 403f80 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 5c 2f 00 00    	jmp    *0x2f5c(%rip)        # 403f88 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401030 <pthread_setaffinity_np@plt>:
  401030:	ff 25 5a 2f 00 00    	jmp    *0x2f5a(%rip)        # 403f90 <pthread_setaffinity_np@GLIBC_2.34>
  401036:	68 00 00 00 00       	push   $0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401040 <puts@plt>:
  401040:	ff 25 52 2f 00 00    	jmp    *0x2f52(%rip)        # 403f98 <puts@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   $0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401050 <clock_gettime@plt>:
  401050:	ff 25 4a 2f 00 00    	jmp    *0x2f4a(%rip)        # 403fa0 <clock_gettime@GLIBC_2.17>
  401056:	68 02 00 00 00       	push   $0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401060 <__stack_chk_fail@plt>:
  401060:	ff 25 42 2f 00 00    	jmp    *0x2f42(%rip)        # 403fa8 <__stack_chk_fail@GLIBC_2.4>
  401066:	68 03 00 00 00       	push   $0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401070 <nanosleep@plt>:
  401070:	ff 25 3a 2f 00 00    	jmp    *0x2f3a(%rip)        # 403fb0 <nanosleep@GLIBC_2.2.5>
  401076:	68 04 00 00 00       	push   $0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401080 <pthread_attr_setschedpolicy@plt>:
  401080:	ff 25 32 2f 00 00    	jmp    *0x2f32(%rip)        # 403fb8 <pthread_attr_setschedpolicy@GLIBC_2.2.5>
  401086:	68 05 00 00 00       	push   $0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <_init+0x20>

0000000000401090 <calloc@plt>:
  401090:	ff 25 2a 2f 00 00    	jmp    *0x2f2a(%rip)        # 403fc0 <calloc@GLIBC_2.2.5>
  401096:	68 06 00 00 00       	push   $0x6
  40109b:	e9 80 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010a0 <__printf_chk@plt>:
  4010a0:	ff 25 22 2f 00 00    	jmp    *0x2f22(%rip)        # 403fc8 <__printf_chk@GLIBC_2.3.4>
  4010a6:	68 07 00 00 00       	push   $0x7
  4010ab:	e9 70 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010b0 <pthread_create@plt>:
  4010b0:	ff 25 1a 2f 00 00    	jmp    *0x2f1a(%rip)        # 403fd0 <pthread_create@GLIBC_2.34>
  4010b6:	68 08 00 00 00       	push   $0x8
  4010bb:	e9 60 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010c0 <pthread_attr_setschedparam@plt>:
  4010c0:	ff 25 12 2f 00 00    	jmp    *0x2f12(%rip)        # 403fd8 <pthread_attr_setschedparam@GLIBC_2.2.5>
  4010c6:	68 09 00 00 00       	push   $0x9
  4010cb:	e9 50 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010d0 <exit@plt>:
  4010d0:	ff 25 0a 2f 00 00    	jmp    *0x2f0a(%rip)        # 403fe0 <exit@GLIBC_2.2.5>
  4010d6:	68 0a 00 00 00       	push   $0xa
  4010db:	e9 40 ff ff ff       	jmp    401020 <_init+0x20>

00000000004010e0 <pthread_join@plt>:
  4010e0:	ff 25 02 2f 00 00    	jmp    *0x2f02(%rip)        # 403fe8 <pthread_join@GLIBC_2.34>
  4010e6:	68 0b 00 00 00       	push   $0xb
  4010eb:	e9 30 ff ff ff       	jmp    401020 <_init+0x20>

Disassembly of section .text:

00000000004010f0 <main>:
  } 
  // printf("Finished %d\n", data->mode);
  return 0;
}

int main() {
  4010f0:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4010f2:	b9 00 80 00 00       	mov    $0x8000,%ecx
  4010f7:	ba 0f 00 00 00       	mov    $0xf,%edx
  4010fc:	48 8d 35 65 10 00 00 	lea    0x1065(%rip),%rsi        # 402168 <_IO_stdin_used+0x168>
  401103:	41 56                	push   %r14
  401105:	bf 01 00 00 00       	mov    $0x1,%edi
  40110a:	41 55                	push   %r13
  40110c:	41 54                	push   %r12
  40110e:	55                   	push   %rbp
  40110f:	53                   	push   %rbx
  401110:	48 83 ec 58          	sub    $0x58,%rsp
  401114:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40111d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  401122:	31 c0                	xor    %eax,%eax
  401124:	e8 77 ff ff ff       	call   4010a0 <__printf_chk@plt>
  401129:	ba 01 00 00 00       	mov    $0x1,%edx
  40112e:	48 8d 35 27 0f 00 00 	lea    0xf27(%rip),%rsi        # 40205c <_IO_stdin_used+0x5c>
  401135:	31 c0                	xor    %eax,%eax
  401137:	bf 01 00 00 00       	mov    $0x1,%edi
  40113c:	e8 5f ff ff ff       	call   4010a0 <__printf_chk@plt>
  401141:	ba 01 00 00 00       	mov    $0x1,%edx
  401146:	48 8d 35 1f 0f 00 00 	lea    0xf1f(%rip),%rsi        # 40206c <_IO_stdin_used+0x6c>
  40114d:	31 c0                	xor    %eax,%eax
  40114f:	bf 01 00 00 00       	mov    $0x1,%edi
  401154:	e8 47 ff ff ff       	call   4010a0 <__printf_chk@plt>
  401159:	ba 01 00 00 00       	mov    $0x1,%edx
  40115e:	48 8d 35 19 0f 00 00 	lea    0xf19(%rip),%rsi        # 40207e <_IO_stdin_used+0x7e>
  401165:	31 c0                	xor    %eax,%eax
  401167:	bf 01 00 00 00       	mov    $0x1,%edi
  40116c:	e8 2f ff ff ff       	call   4010a0 <__printf_chk@plt>
  401171:	ba 02 00 00 00       	mov    $0x2,%edx
  401176:	48 8d 35 13 0f 00 00 	lea    0xf13(%rip),%rsi        # 402090 <_IO_stdin_used+0x90>
  40117d:	31 c0                	xor    %eax,%eax
  40117f:	bf 01 00 00 00       	mov    $0x1,%edi
  401184:	e8 17 ff ff ff       	call   4010a0 <__printf_chk@plt>
  int group_size = writers_count + other_count;
  printf("Readers count %d\n", other_count);
  printf("Writers count %d\n", writers_count);
  int thread_count = groups * (other_count + writers_count);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
  401189:	be 80 02 00 00       	mov    $0x280,%esi
  40118e:	bf 02 00 00 00       	mov    $0x2,%edi
  401193:	e8 f8 fe ff ff       	call   401090 <calloc@plt>
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
  401198:	be 38 00 00 00       	mov    $0x38,%esi
  40119d:	bf 02 00 00 00       	mov    $0x2,%edi
  4011a2:	66 48 0f 6e c8       	movq   %rax,%xmm1
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
  4011a7:	48 89 c5             	mov    %rax,%rbp
  4011aa:	66 0f 6c c9          	punpcklqdq %xmm1,%xmm1
  4011ae:	0f 29 0c 24          	movaps %xmm1,(%rsp)
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
  4011b2:	e8 d9 fe ff ff       	call   401090 <calloc@plt>
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
  4011b7:	be 08 00 00 00       	mov    $0x8,%esi
  4011bc:	bf 02 00 00 00       	mov    $0x2,%edi
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
  4011c1:	49 89 c6             	mov    %rax,%r14
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
  4011c4:	e8 c7 fe ff ff       	call   401090 <calloc@plt>
  4011c9:	31 d2                	xor    %edx,%edx
  4011cb:	bf 01 00 00 00       	mov    $0x1,%edi
  4011d0:	48 8d 35 d0 0e 00 00 	lea    0xed0(%rip),%rsi        # 4020a7 <_IO_stdin_used+0xa7>
  4011d7:	49 89 c5             	mov    %rax,%r13
  4011da:	31 c0                	xor    %eax,%eax
  4011dc:	e8 bf fe ff ff       	call   4010a0 <__printf_chk@plt>
  4011e1:	48 8d 3d ca 0e 00 00 	lea    0xeca(%rip),%rdi        # 4020b2 <_IO_stdin_used+0xb2>
  4011e8:	e8 53 fe ff ff       	call   401040 <puts@plt>
    int receiver2 = receiver + 1; 
    int seq[] = {1, 2, 5};
    int tag_index[] = {1, 5, 7};
    for (int n = sender, sender_index = 0; n < sender + writers_count, sender_index < writers_count; n++, sender_index++) {
      printf("CREATE SENDER THREAD\n");
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
  4011ed:	be 80 00 00 00       	mov    $0x80,%esi
  4011f2:	bf 01 00 00 00       	mov    $0x1,%edi
  4011f7:	e8 94 fe ff ff       	call   401090 <calloc@plt>
  4011fc:	31 c9                	xor    %ecx,%ecx
  4011fe:	31 d2                	xor    %edx,%edx
  401200:	48 8d 35 89 0f 00 00 	lea    0xf89(%rip),%rsi        # 402190 <_IO_stdin_used+0x190>
      CPU_ZERO(sendercpu);
      CPU_SET(curcpu, sendercpu);
  401207:	48 83 08 01          	orq    $0x1,(%rax)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
  40120b:	48 89 c3             	mov    %rax,%rbx
  40120e:	bf 01 00 00 00       	mov    $0x1,%edi
  401213:	31 c0                	xor    %eax,%eax
  401215:	e8 86 fe ff ff       	call   4010a0 <__printf_chk@plt>
      thread_data[n].running = 1;
      thread_data[n].size = buffer_size;
      thread_data[n].thread_tag = tag_index[sender_index];
      thread_data[n].end = 0;
      thread_data[n].sender = &thread_data[sender];
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
  40121a:	be 08 00 00 00       	mov    $0x8,%esi
      thread_data[n].sender = &thread_data[sender];
  40121f:	48 89 6d 08          	mov    %rbp,0x8(%rbp)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
  401223:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[n].cpu_set = sendercpu;
  401228:	48 89 9d a0 01 00 00 	mov    %rbx,0x1a0(%rbp)
      thread_data[n].mode = WRITER;
  40122f:	c7 85 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rbp)
      thread_data[n].thread_index = n;
  401239:	c7 45 00 00 00 00 00 	movl   $0x0,0x0(%rbp)
      thread_data[n].multiple = seq[sender_index % writers_count];
  401240:	c7 85 10 02 00 00 01 00 00 00 	movl   $0x1,0x210(%rbp)
      thread_data[n].running = 1;
  40124a:	c7 85 98 01 00 00 01 00 00 00 	movl   $0x1,0x198(%rbp)
      thread_data[n].size = buffer_size;
  401254:	48 c7 85 90 01 00 00 00 80 00 00 	movq   $0x8000,0x190(%rbp)
      thread_data[n].thread_tag = tag_index[sender_index];
  40125f:	c7 85 14 02 00 00 01 00 00 00 	movl   $0x1,0x214(%rbp)
      thread_data[n].end = 0;
  401269:	c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbp)
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
  401273:	e8 18 fe ff ff       	call   401090 <calloc@plt>
      if (n == sender) {
        thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
  401278:	be 00 02 00 00       	mov    $0x200,%esi
  40127d:	bf 00 80 00 00       	mov    $0x8000,%edi
      thread_data[n].readers = calloc(other_count, sizeof(struct Thread*));
  401282:	48 89 85 00 02 00 00 	mov    %rax,0x200(%rbp)
        thread_data[n].data = calloc(buffer_size, sizeof(struct Snapshot));
  401289:	e8 02 fe ff ff       	call   401090 <calloc@plt>
  40128e:	48 89 45 18          	mov    %rax,0x18(%rbp)
  401292:	49 89 c4             	mov    %rax,%r12
        for (int k = 0 ; k < buffer_size ; k++) {
  401295:	48 8d 98 80 00 00 00 	lea    0x80(%rax),%rbx
  40129c:	49 81 c4 80 00 00 01 	add    $0x1000080,%r12
  4012a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
  4012a8:	be 04 00 00 00       	mov    $0x4,%esi
  4012ad:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int k = 0 ; k < buffer_size ; k++) {
  4012b2:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
          thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
  4012b9:	e8 d2 fd ff ff       	call   401090 <calloc@plt>
          thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
  4012be:	be 10 00 00 00       	mov    $0x10,%esi
  4012c3:	bf 01 00 00 00       	mov    $0x1,%edi
          thread_data[n].data[k].complete = calloc(other_count, sizeof(int));
  4012c8:	48 89 83 80 fe ff ff 	mov    %rax,-0x180(%rbx)
          thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
  4012cf:	e8 bc fd ff ff       	call   401090 <calloc@plt>
          thread_data[n].data[k].written = 0;
  4012d4:	c7 83 00 ff ff ff 00 00 00 00 	movl   $0x0,-0x100(%rbx)
          thread_data[n].data[k].end = calloc(other_count, sizeof(struct timespec));
  4012de:	48 89 83 00 fe ff ff 	mov    %rax,-0x200(%rbx)
        for (int k = 0 ; k < buffer_size ; k++) {
  4012e5:	49 39 dc             	cmp    %rbx,%r12
  4012e8:	75 be                	jne    4012a8 <main+0x1b8>
  4012ea:	31 d2                	xor    %edx,%edx
  4012ec:	48 8d 35 d4 0d 00 00 	lea    0xdd4(%rip),%rsi        # 4020c7 <_IO_stdin_used+0xc7>
  4012f3:	bf 01 00 00 00       	mov    $0x1,%edi
  4012f8:	31 c0                	xor    %eax,%eax
        }
      }
      thread_data[n].other_count = other_count;
  4012fa:	c7 85 08 02 00 00 01 00 00 00 	movl   $0x1,0x208(%rbp)
    }

    printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      thread_data[j].thread_index = j;
  401304:	4c 8d a5 80 02 00 00 	lea    0x280(%rbp),%r12
  40130b:	e8 90 fd ff ff       	call   4010a0 <__printf_chk@plt>
      thread_data[j].reader_index = receiver_index;
      thread_data[j].multiple = receiver_index % other_count;
      thread_data[j].other_count = other_count;
     
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
  401310:	be 80 00 00 00       	mov    $0x80,%esi
  401315:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[j].other_count = other_count;
  40131a:	48 8b 05 df 0e 00 00 	mov    0xedf(%rip),%rax        # 402200 <_IO_stdin_used+0x200>
      thread_data[j].thread_index = j;
  401321:	c7 85 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rbp)
      thread_data[j].multiple = receiver_index % other_count;
  40132b:	c7 85 90 04 00 00 00 00 00 00 	movl   $0x0,0x490(%rbp)
      thread_data[j].other_count = other_count;
  401335:	48 89 85 88 04 00 00 	mov    %rax,0x488(%rbp)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
  40133c:	e8 4f fd ff ff       	call   401090 <calloc@plt>
  401341:	b9 02 00 00 00       	mov    $0x2,%ecx
  401346:	ba 01 00 00 00       	mov    $0x1,%edx
  40134b:	48 8d 35 5e 0e 00 00 	lea    0xe5e(%rip),%rsi        # 4021b0 <_IO_stdin_used+0x1b0>
      CPU_ZERO(receivercpu);
      CPU_SET(curcpu, receivercpu);
  401352:	48 83 08 04          	orq    $0x4,(%rax)
      cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
  401356:	48 89 c3             	mov    %rax,%rbx
  401359:	bf 01 00 00 00       	mov    $0x1,%edi
  40135e:	31 c0                	xor    %eax,%eax
  401360:	e8 3b fd ff ff       	call   4010a0 <__printf_chk@plt>
      } */
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
  401365:	48 8b 85 00 02 00 00 	mov    0x200(%rbp),%rax
  40136c:	31 c9                	xor    %ecx,%ecx
  40136e:	31 d2                	xor    %edx,%edx
      thread_data[j].sender = &thread_data[sender];
  401370:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
  401375:	bf 01 00 00 00       	mov    $0x1,%edi
  40137a:	48 8d 35 57 0e 00 00 	lea    0xe57(%rip),%rsi        # 4021d8 <_IO_stdin_used+0x1d8>
      thread_data[j].running = 1;
  401381:	c7 85 18 04 00 00 01 00 00 00 	movl   $0x1,0x418(%rbp)
      thread_data[j].readers = thread_data[sender].readers;
  40138b:	48 89 85 80 04 00 00 	mov    %rax,0x480(%rbp)
  401392:	31 c0                	xor    %eax,%eax
      thread_data[j].cpu_set = receivercpu;
  401394:	48 89 9d 20 04 00 00 	mov    %rbx,0x420(%rbp)
      thread_data[j].mode = READER;
  40139b:	c7 85 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rbp)
      thread_data[j].size = buffer_size;
  4013a5:	48 c7 85 10 04 00 00 00 80 00 00 	movq   $0x8000,0x410(%rbp)
      thread_data[j].start = 0;
  4013b0:	c7 85 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rbp)
      thread_data[j].other_count = other_count;
  4013ba:	c7 85 88 04 00 00 01 00 00 00 	movl   $0x1,0x488(%rbp)
      thread_data[j].sender = &thread_data[sender];
  4013c4:	0f 11 95 88 02 00 00 	movups %xmm2,0x288(%rbp)
  4013cb:	e8 d0 fc ff ff       	call   4010a0 <__printf_chk@plt>
      // printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
      for (int n = sender; n < sender + writers_count; n++) {
        printf("assigned reader %d to sender %d\n", receiver_index, n);
        thread_data[n].readers[receiver_index] = &thread_data[j];
  4013d0:	48 8b 85 00 02 00 00 	mov    0x200(%rbp),%rax
  4013d7:	4c 89 20             	mov    %r12,(%rax)
      }
    }
    curcpu = 0;
    // printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
  4013da:	0f ae f0             	mfence
  4013dd:	bf 01 00 00 00       	mov    $0x1,%edi
  4013e2:	31 c0                	xor    %eax,%eax
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
  4013e4:	4d 8d 7e 38          	lea    0x38(%r14),%r15
  4013e8:	ba 01 00 00 00       	mov    $0x1,%edx
  4013ed:	48 8d 35 e8 0c 00 00 	lea    0xce8(%rip),%rsi        # 4020dc <_IO_stdin_used+0xdc>
  param.sched_priority = 0;
  4013f4:	c7 44 24 1c 00 00 00 00 	movl   $0x0,0x1c(%rsp)
  4013fc:	e8 9f fc ff ff       	call   4010a0 <__printf_chk@plt>
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
  401401:	31 f6                	xor    %esi,%esi
  401403:	4c 89 ff             	mov    %r15,%rdi
  401406:	e8 75 fc ff ff       	call   401080 <pthread_attr_setschedpolicy@plt>
      if (ret) {
  40140b:	85 c0                	test   %eax,%eax
  40140d:	0f 85 87 01 00 00    	jne    40159a <main+0x4aa>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
  401413:	48 8d 74 24 1c       	lea    0x1c(%rsp),%rsi
  401418:	4c 89 ff             	mov    %r15,%rdi
  40141b:	e8 a0 fc ff ff       	call   4010c0 <pthread_attr_setschedparam@plt>
      if (ret) {
  401420:	85 c0                	test   %eax,%eax
  401422:	0f 85 8d 01 00 00    	jne    4015b5 <main+0x4c5>
              printf("pthread setschedparam failed\n");
              exit(1);
      }
       
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
  401428:	4c 89 e1             	mov    %r12,%rcx
  40142b:	49 c7 c4 c0 16 40 00 	mov    $0x4016c0,%r12
  401432:	49 8d 7d 08          	lea    0x8(%r13),%rdi
  401436:	4c 89 fe             	mov    %r15,%rsi
  401439:	4c 89 e2             	mov    %r12,%rdx
  40143c:	e8 6f fc ff ff       	call   4010b0 <pthread_create@plt>
      pthread_setaffinity_np(thread[j], sizeof(thread_data[j].cpu_set), thread_data[j].cpu_set);
  401441:	49 8b 7d 08          	mov    0x8(%r13),%rdi
  401445:	be 08 00 00 00       	mov    $0x8,%esi
  40144a:	48 8b 95 20 04 00 00 	mov    0x420(%rbp),%rdx
  401451:	e8 da fb ff ff       	call   401030 <pthread_setaffinity_np@plt>
    }
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
  401456:	31 f6                	xor    %esi,%esi
  401458:	4c 89 f7             	mov    %r14,%rdi
  40145b:	e8 20 fc ff ff       	call   401080 <pthread_attr_setschedpolicy@plt>
      if (ret) {
  401460:	85 c0                	test   %eax,%eax
  401462:	0f 85 32 01 00 00    	jne    40159a <main+0x4aa>
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
  401468:	48 8d 74 24 18       	lea    0x18(%rsp),%rsi
  40146d:	4c 89 f7             	mov    %r14,%rdi
      param2.sched_priority = 0;
  401470:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
  401478:	e8 43 fc ff ff       	call   4010c0 <pthread_attr_setschedparam@plt>
      if (ret) {
  40147d:	85 c0                	test   %eax,%eax
  40147f:	0f 85 30 01 00 00    	jne    4015b5 <main+0x4c5>
  401485:	31 d2                	xor    %edx,%edx
  401487:	48 8d 35 a6 0c 00 00 	lea    0xca6(%rip),%rsi        # 402134 <_IO_stdin_used+0x134>
  40148e:	bf 01 00 00 00       	mov    $0x1,%edi
    int receiver = sender + writers_count; 
    for (int n = sender; n < sender + writers_count; n++) {
      pthread_join(thread[n], res1);
    }
    for (int j = receiver, receiver_index = 0; j < receiver + other_count; j++, receiver_index++) {
      pthread_join(thread[j], res2);
  401493:	31 db                	xor    %ebx,%ebx
  401495:	e8 06 fc ff ff       	call   4010a0 <__printf_chk@plt>
      pthread_create(&thread[n], &attr[n], &disruptor_thread, &thread_data[n]);
  40149a:	48 89 e9             	mov    %rbp,%rcx
  40149d:	4c 89 e2             	mov    %r12,%rdx
  4014a0:	4c 89 f6             	mov    %r14,%rsi
  4014a3:	4c 89 ef             	mov    %r13,%rdi
  4014a6:	4c 8d 25 a3 0c 00 00 	lea    0xca3(%rip),%r12        # 402150 <_IO_stdin_used+0x150>
  4014ad:	e8 fe fb ff ff       	call   4010b0 <pthread_create@plt>
      pthread_setaffinity_np(thread[n], sizeof(thread_data[n].cpu_set), thread_data[n].cpu_set);
  4014b2:	48 8b 95 a0 01 00 00 	mov    0x1a0(%rbp),%rdx
  4014b9:	49 8b 7d 00          	mov    0x0(%r13),%rdi
  4014bd:	be 08 00 00 00       	mov    $0x8,%esi
  4014c2:	e8 69 fb ff ff       	call   401030 <pthread_setaffinity_np@plt>
  nanosleep(&preempt , &rem2);
  4014c7:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
  4014cc:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
  struct timespec preempt = {
  4014d1:	66 0f 6f 05 37 0d 00 00 	movdqa 0xd37(%rip),%xmm0        # 402210 <_IO_stdin_used+0x210>
  4014d9:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
  nanosleep(&preempt , &rem2);
  4014de:	e8 8d fb ff ff       	call   401070 <nanosleep@plt>
      pthread_join(thread[n], res1);
  4014e3:	49 8b 7d 00          	mov    0x0(%r13),%rdi
  4014e7:	31 f6                	xor    %esi,%esi
    thread_data[sender].running = 0;
  4014e9:	c7 85 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%rbp)
      thread_data[j].running = 0;
  4014f3:	c7 85 18 04 00 00 00 00 00 00 	movl   $0x0,0x418(%rbp)
      thread_data[n].running = 0;
  4014fd:	c7 85 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%rbp)
      pthread_join(thread[n], res1);
  401507:	e8 d4 fb ff ff       	call   4010e0 <pthread_join@plt>
      pthread_join(thread[j], res2);
  40150c:	49 8b 7d 08          	mov    0x8(%r13),%rdi
  401510:	31 f6                	xor    %esi,%esi
  401512:	e8 c9 fb ff ff       	call   4010e0 <pthread_join@plt>
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + writers_count; 
    int incompletes = 0;
    // printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
  401517:	eb 17                	jmp    401530 <main+0x440>
  401519:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  401520:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
  401527:	48 81 fb 00 00 00 01 	cmp    $0x1000000,%rbx
  40152e:	74 49                	je     401579 <main+0x489>
      int compcount = 0;
      for (int n = 0 ; n < other_count ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
  401530:	48 8b 45 18          	mov    0x18(%rbp),%rax
  401534:	48 01 d8             	add    %rbx,%rax
  401537:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
          compcount++;
        }
      }
      // printf("%d\n", compcount);
      if (compcount == other_count) {
  40153e:	83 3a 01             	cmpl   $0x1,(%rdx)
  401541:	75 dd                	jne    401520 <main+0x430>
      for (int n = 0 ; n < other_count ; n++) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
          struct timespec end = thread_data[sender].data[y].end[n];
  401543:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
  40154a:	4c 89 e6             	mov    %r12,%rsi
  40154d:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int y = 0 ; y < buffer_size; y++) {
  401552:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
  401559:	4c 8b 42 08          	mov    0x8(%rdx),%r8
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
  40155d:	48 8b 0a             	mov    (%rdx),%rcx
  401560:	31 d2                	xor    %edx,%edx
  401562:	48 2b 08             	sub    (%rax),%rcx
  401565:	4c 2b 40 08          	sub    0x8(%rax),%r8
  401569:	31 c0                	xor    %eax,%eax
  40156b:	e8 30 fb ff ff       	call   4010a0 <__printf_chk@plt>
    for (int y = 0 ; y < buffer_size; y++) {
  401570:	48 81 fb 00 00 00 01 	cmp    $0x1000000,%rbx
  401577:	75 b7                	jne    401530 <main+0x440>
    }
    // printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
  401579:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
  40157e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  401587:	75 27                	jne    4015b0 <main+0x4c0>
  401589:	48 83 c4 58          	add    $0x58,%rsp
  40158d:	31 c0                	xor    %eax,%eax
  40158f:	5b                   	pop    %rbx
  401590:	5d                   	pop    %rbp
  401591:	41 5c                	pop    %r12
  401593:	41 5d                	pop    %r13
  401595:	41 5e                	pop    %r14
  401597:	41 5f                	pop    %r15
  401599:	c3                   	ret
  40159a:	48 8d 3d 58 0b 00 00 	lea    0xb58(%rip),%rdi        # 4020f9 <_IO_stdin_used+0xf9>
  4015a1:	e8 9a fa ff ff       	call   401040 <puts@plt>
               exit(1);
  4015a6:	bf 01 00 00 00       	mov    $0x1,%edi
  4015ab:	e8 20 fb ff ff       	call   4010d0 <exit@plt>
}
  4015b0:	e8 ab fa ff ff       	call   401060 <__stack_chk_fail@plt>
  4015b5:	48 8d 3d 5b 0b 00 00 	lea    0xb5b(%rip),%rdi        # 402117 <_IO_stdin_used+0x117>
  4015bc:	e8 7f fa ff ff       	call   401040 <puts@plt>
              exit(1);
  4015c1:	bf 01 00 00 00       	mov    $0x1,%edi
  4015c6:	e8 05 fb ff ff       	call   4010d0 <exit@plt>
  4015cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000004015d0 <_start>:
  4015d0:	f3 0f 1e fa          	endbr64
  4015d4:	31 ed                	xor    %ebp,%ebp
  4015d6:	49 89 d1             	mov    %rdx,%r9
  4015d9:	5e                   	pop    %rsi
  4015da:	48 89 e2             	mov    %rsp,%rdx
  4015dd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4015e1:	50                   	push   %rax
  4015e2:	54                   	push   %rsp
  4015e3:	45 31 c0             	xor    %r8d,%r8d
  4015e6:	31 c9                	xor    %ecx,%ecx
  4015e8:	48 c7 c7 f0 10 40 00 	mov    $0x4010f0,%rdi
  4015ef:	ff 15 fb 29 00 00    	call   *0x29fb(%rip)        # 403ff0 <__libc_start_main@GLIBC_2.34>
  4015f5:	f4                   	hlt
  4015f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000401600 <_dl_relocate_static_pie>:
  401600:	f3 0f 1e fa          	endbr64
  401604:	c3                   	ret
  401605:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40160f:	90                   	nop

0000000000401610 <deregister_tm_clones>:
  401610:	b8 10 40 40 00       	mov    $0x404010,%eax
  401615:	48 3d 10 40 40 00    	cmp    $0x404010,%rax
  40161b:	74 13                	je     401630 <deregister_tm_clones+0x20>
  40161d:	b8 00 00 00 00       	mov    $0x0,%eax
  401622:	48 85 c0             	test   %rax,%rax
  401625:	74 09                	je     401630 <deregister_tm_clones+0x20>
  401627:	bf 10 40 40 00       	mov    $0x404010,%edi
  40162c:	ff e0                	jmp    *%rax
  40162e:	66 90                	xchg   %ax,%ax
  401630:	c3                   	ret
  401631:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40163c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401640 <register_tm_clones>:
  401640:	be 10 40 40 00       	mov    $0x404010,%esi
  401645:	48 81 ee 10 40 40 00 	sub    $0x404010,%rsi
  40164c:	48 89 f0             	mov    %rsi,%rax
  40164f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  401653:	48 c1 f8 03          	sar    $0x3,%rax
  401657:	48 01 c6             	add    %rax,%rsi
  40165a:	48 d1 fe             	sar    %rsi
  40165d:	74 11                	je     401670 <register_tm_clones+0x30>
  40165f:	b8 00 00 00 00       	mov    $0x0,%eax
  401664:	48 85 c0             	test   %rax,%rax
  401667:	74 07                	je     401670 <register_tm_clones+0x30>
  401669:	bf 10 40 40 00       	mov    $0x404010,%edi
  40166e:	ff e0                	jmp    *%rax
  401670:	c3                   	ret
  401671:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40167c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000401680 <__do_global_dtors_aux>:
  401680:	f3 0f 1e fa          	endbr64
  401684:	80 3d 85 29 00 00 00 	cmpb   $0x0,0x2985(%rip)        # 404010 <__TMC_END__>
  40168b:	75 13                	jne    4016a0 <__do_global_dtors_aux+0x20>
  40168d:	55                   	push   %rbp
  40168e:	48 89 e5             	mov    %rsp,%rbp
  401691:	e8 7a ff ff ff       	call   401610 <deregister_tm_clones>
  401696:	c6 05 73 29 00 00 01 	movb   $0x1,0x2973(%rip)        # 404010 <__TMC_END__>
  40169d:	5d                   	pop    %rbp
  40169e:	c3                   	ret
  40169f:	90                   	nop
  4016a0:	c3                   	ret
  4016a1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4016ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004016b0 <frame_dummy>:
  4016b0:	f3 0f 1e fa          	endbr64
  4016b4:	eb 8a                	jmp    401640 <register_tm_clones>
  4016b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004016c0 <disruptor_thread>:
void * disruptor_thread(void * arg) {
  4016c0:	41 56                	push   %r14
  4016c2:	41 55                	push   %r13
  4016c4:	41 54                	push   %r12
  4016c6:	55                   	push   %rbp
  4016c7:	53                   	push   %rbx
  if (data->mode == WRITER) {
  4016c8:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
void * disruptor_thread(void * arg) {
  4016ce:	48 89 fb             	mov    %rdi,%rbx
  if (data->mode == WRITER) {
  4016d1:	85 c0                	test   %eax,%eax
  4016d3:	74 1a                	je     4016ef <disruptor_thread+0x2f>
  } else if (data->mode == READER) {
  4016d5:	8b 87 88 01 00 00    	mov    0x188(%rdi),%eax
  4016db:	83 f8 01             	cmp    $0x1,%eax
  4016de:	0f 84 3b 01 00 00    	je     40181f <disruptor_thread+0x15f>
}
  4016e4:	5b                   	pop    %rbx
  4016e5:	31 c0                	xor    %eax,%eax
  4016e7:	5d                   	pop    %rbp
  4016e8:	41 5c                	pop    %r12
  4016ea:	41 5d                	pop    %r13
  4016ec:	41 5e                	pop    %r14
  4016ee:	c3                   	ret
  4016ef:	8b 17                	mov    (%rdi),%edx
  4016f1:	48 8d 35 0c 09 00 00 	lea    0x90c(%rip),%rsi        # 402004 <_IO_stdin_used+0x4>
  4016f8:	bf 01 00 00 00       	mov    $0x1,%edi
  4016fd:	e8 9e f9 ff ff       	call   4010a0 <__printf_chk@plt>
    struct Thread *me = data->sender;
  401702:	48 8b 6b 08          	mov    0x8(%rbx),%rbp
  401706:	bf 01 00 00 00       	mov    $0x1,%edi
  40170b:	31 c0                	xor    %eax,%eax
  40170d:	48 8d 35 00 09 00 00 	lea    0x900(%rip),%rsi        # 402014 <_IO_stdin_used+0x14>
  401714:	48 8b 55 18          	mov    0x18(%rbp),%rdx
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED))) {
  401718:	4c 8d a5 80 01 00 00 	lea    0x180(%rbp),%r12
  40171f:	e8 7c f9 ff ff       	call   4010a0 <__printf_chk@plt>
    while (data->running == 1) {
  401724:	0f 1f 40 00          	nopl   0x0(%rax)
  401728:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
  40172e:	83 f8 01             	cmp    $0x1,%eax
  401731:	75 b1                	jne    4016e4 <disruptor_thread+0x24>
      asm volatile ("sfence" ::: "memory");
  401733:	0f ae f8             	sfence
      long pos = (((me->realend & END_MASK) >> 32) + 1) % data->size;
  401736:	4c 8b 8d 80 01 00 00 	mov    0x180(%rbp),%r9
      for (int x  = 0 ; x < data->other_count; x++) {
  40173d:	8b b3 08 02 00 00    	mov    0x208(%rbx),%esi
      long pos = (((me->realend & END_MASK) >> 32) + 1) % data->size;
  401743:	4d 89 c8             	mov    %r9,%r8
  401746:	49 c1 f8 20          	sar    $0x20,%r8
  40174a:	41 81 e0 ff ff ff 0f 	and    $0xfffffff,%r8d
  401751:	49 8d 40 01          	lea    0x1(%r8),%rax
  401755:	48 99                	cqto
  401757:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
      for (int x  = 0 ; x < data->other_count; x++) {
  40175e:	85 f6                	test   %esi,%esi
  401760:	0f 8e 8c 01 00 00    	jle    4018f2 <disruptor_thread+0x232>
  401766:	48 8b 8b 00 02 00 00 	mov    0x200(%rbx),%rcx
  40176d:	8d 46 ff             	lea    -0x1(%rsi),%eax
  401770:	48 8d 7c c1 08       	lea    0x8(%rcx,%rax,8),%rdi
  401775:	0f 1f 00             	nopl   (%rax)
        if (pos == data->readers[x]->start) {
  401778:	48 8b 31             	mov    (%rcx),%rsi
  40177b:	48 63 b6 80 00 00 00 	movslq 0x80(%rsi),%rsi
  401782:	48 39 d6             	cmp    %rdx,%rsi
  401785:	74 a1                	je     401728 <disruptor_thread+0x68>
      for (int x  = 0 ; x < data->other_count; x++) {
  401787:	48 83 c1 08          	add    $0x8,%rcx
  40178b:	48 39 cf             	cmp    %rcx,%rdi
  40178e:	75 e8                	jne    401778 <disruptor_thread+0xb8>
              changed = (((original & END_MASK) >> 32)) % me->size;
  401790:	4c 89 c0             	mov    %r8,%rax
  401793:	48 99                	cqto
  401795:	48 f7 bd 90 01 00 00 	idivq  0x190(%rbp)
              long new = (data->thread_tag) | ((changed + 1) << 32);
  40179c:	48 63 83 14 02 00 00 	movslq 0x214(%rbx),%rax
  4017a3:	48 8d 7a 01          	lea    0x1(%rdx),%rdi
  4017a7:	48 c1 e7 20          	shl    $0x20,%rdi
  4017ab:	48 09 c7             	or     %rax,%rdi
                me->data[changed].complete[x] = 0;
  4017ae:	48 89 d0             	mov    %rdx,%rax
  4017b1:	48 c1 e0 09          	shl    $0x9,%rax
  4017b5:	48 03 45 18          	add    0x18(%rbp),%rax
  4017b9:	48 8b b0 00 01 00 00 	mov    0x100(%rax),%rsi
  4017c0:	31 c0                	xor    %eax,%eax
  4017c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  4017c8:	48 63 c8             	movslq %eax,%rcx
              for (int x = 0 ; x < data->other_count; x++) {
  4017cb:	83 c0 01             	add    $0x1,%eax
                me->data[changed].complete[x] = 0;
  4017ce:	c7 04 8e 00 00 00 00 	movl   $0x0,(%rsi,%rcx,4)
              for (int x = 0 ; x < data->other_count; x++) {
  4017d5:	39 83 08 02 00 00    	cmp    %eax,0x208(%rbx)
  4017db:	7f eb                	jg     4017c8 <disruptor_thread+0x108>
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED))) {
  4017dd:	4c 89 c8             	mov    %r9,%rax
  4017e0:	f0 49 0f b1 3c 24    	lock cmpxchg %rdi,(%r12)
  4017e6:	0f 85 38 01 00 00    	jne    401924 <disruptor_thread+0x264>
                clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
  4017ec:	48 8b 75 18          	mov    0x18(%rbp),%rsi
  4017f0:	48 c1 e2 09          	shl    $0x9,%rdx
  4017f4:	bf 04 00 00 00       	mov    $0x4,%edi
  4017f9:	49 89 d5             	mov    %rdx,%r13
  4017fc:	48 01 d6             	add    %rdx,%rsi
  4017ff:	e8 4c f8 ff ff       	call   401050 <clock_gettime@plt>
                __atomic_store_n(&me->sender->data[changed].written, me->other_count, __ATOMIC_SEQ_CST);
  401804:	48 8b 45 08          	mov    0x8(%rbp),%rax
  401808:	48 8b 50 18          	mov    0x18(%rax),%rdx
  40180c:	8b 85 08 02 00 00    	mov    0x208(%rbp),%eax
  401812:	42 87 84 2a 80 01 00 00 	xchg   %eax,0x180(%rdx,%r13,1)
    while (data->running == 1) {
  40181a:	e9 09 ff ff ff       	jmp    401728 <disruptor_thread+0x68>
  40181f:	8b 97 0c 02 00 00    	mov    0x20c(%rdi),%edx
  401825:	48 8d 35 04 08 00 00 	lea    0x804(%rip),%rsi        # 402030 <_IO_stdin_used+0x30>
  40182c:	bf 01 00 00 00       	mov    $0x1,%edi
  401831:	31 c0                	xor    %eax,%eax
  401833:	e8 68 f8 ff ff       	call   4010a0 <__printf_chk@plt>
    struct Thread *sender = data->sender;
  401838:	4c 8b 63 08          	mov    0x8(%rbx),%r12
  40183c:	bf 01 00 00 00       	mov    $0x1,%edi
  401841:	31 c0                	xor    %eax,%eax
  401843:	48 8d 35 f6 07 00 00 	lea    0x7f6(%rip),%rsi        # 402040 <_IO_stdin_used+0x40>
    struct Snapshot * rdata = sender->data;
  40184a:	4d 8b 6c 24 18       	mov    0x18(%r12),%r13
  40184f:	4c 89 ea             	mov    %r13,%rdx
  401852:	e8 49 f8 ff ff       	call   4010a0 <__printf_chk@plt>
    while (data->running == 1) {
  401857:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  401860:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
  401866:	83 f8 01             	cmp    $0x1,%eax
  401869:	0f 85 75 fe ff ff    	jne    4016e4 <disruptor_thread+0x24>
      int pos = ((__atomic_load_n(&sender->realend, __ATOMIC_SEQ_CST) & END_MASK) >> 32);
  40186f:	49 8b 84 24 80 01 00 00 	mov    0x180(%r12),%rax
  401877:	48 c1 f8 20          	sar    $0x20,%rax
  40187b:	25 ff ff ff 0f       	and    $0xfffffff,%eax
      if (pos == data->start) {
  401880:	8b ab 80 00 00 00    	mov    0x80(%rbx),%ebp
  401886:	39 c5                	cmp    %eax,%ebp
  401888:	74 d6                	je     401860 <disruptor_thread+0x1a0>
          int written = __atomic_load_n(&rdata[changed].written, __ATOMIC_SEQ_CST);
  40188a:	4c 63 f5             	movslq %ebp,%r14
  40188d:	49 c1 e6 09          	shl    $0x9,%r14
  401891:	4d 01 ee             	add    %r13,%r14
  401894:	41 8b 86 80 01 00 00 	mov    0x180(%r14),%eax
          if (written > 0) {
  40189b:	85 c0                	test   %eax,%eax
  40189d:	7e c1                	jle    401860 <disruptor_thread+0x1a0>
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end[data->reader_index]);
  40189f:	48 63 b3 0c 02 00 00 	movslq 0x20c(%rbx),%rsi
  4018a6:	bf 04 00 00 00       	mov    $0x4,%edi
  4018ab:	48 c1 e6 04          	shl    $0x4,%rsi
  4018af:	49 03 b6 80 00 00 00 	add    0x80(%r14),%rsi
  4018b6:	e8 95 f7 ff ff       	call   401050 <clock_gettime@plt>
              rdata[changed].complete[data->reader_index] = 1;
  4018bb:	49 8b 86 00 01 00 00 	mov    0x100(%r14),%rax
  4018c2:	48 63 93 0c 02 00 00 	movslq 0x20c(%rbx),%rdx
  4018c9:	c7 04 90 01 00 00 00 	movl   $0x1,(%rax,%rdx,4)
              data->start = (changed + 1) % data->size;
  4018d0:	8d 45 01             	lea    0x1(%rbp),%eax
  4018d3:	48 98                	cltq
  4018d5:	48 99                	cqto
  4018d7:	48 f7 bb 90 01 00 00 	idivq  0x190(%rbx)
  4018de:	89 93 80 00 00 00    	mov    %edx,0x80(%rbx)
              __atomic_sub_fetch(&rdata[changed].written, 1, __ATOMIC_SEQ_CST);
  4018e4:	f0 41 83 ae 80 01 00 00 01 	lock subl $0x1,0x180(%r14)
  4018ed:	e9 6e ff ff ff       	jmp    401860 <disruptor_thread+0x1a0>
              changed = (((original & END_MASK) >> 32)) % me->size;
  4018f2:	4c 89 c0             	mov    %r8,%rax
  4018f5:	48 99                	cqto
  4018f7:	48 f7 bd 90 01 00 00 	idivq  0x190(%rbp)
              long new = (data->thread_tag) | ((changed + 1) << 32);
  4018fe:	48 63 83 14 02 00 00 	movslq 0x214(%rbx),%rax
  401905:	48 8d 7a 01          	lea    0x1(%rdx),%rdi
  401909:	48 c1 e7 20          	shl    $0x20,%rdi
  40190d:	48 09 c7             	or     %rax,%rdi
              for (int x = 0 ; x < data->other_count; x++) {
  401910:	e9 c8 fe ff ff       	jmp    4017dd <disruptor_thread+0x11d>
              while (!(result = __atomic_compare_exchange (&me->realend, &original, &new, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED))) {
  401915:	48 89 f8             	mov    %rdi,%rax
  401918:	f0 49 0f b1 0c 24    	lock cmpxchg %rcx,(%r12)
  40191e:	0f 84 c8 fe ff ff    	je     4017ec <disruptor_thread+0x12c>
                original = me->realend;
  401924:	48 8b bd 80 01 00 00 	mov    0x180(%rbp),%rdi
                changed = (((original & END_MASK) >> 32)) % me->size;
  40192b:	48 89 f8             	mov    %rdi,%rax
  40192e:	48 c1 f8 20          	sar    $0x20,%rax
  401932:	25 ff ff ff 0f       	and    $0xfffffff,%eax
  401937:	48 99                	cqto
  401939:	48 f7 bd 90 01 00 00 	idivq  0x190(%rbp)
                new = (data->thread_tag) | ((changed + 1) << 32);
  401940:	48 63 83 14 02 00 00 	movslq 0x214(%rbx),%rax
  401947:	48 8d 4a 01          	lea    0x1(%rdx),%rcx
  40194b:	48 c1 e1 20          	shl    $0x20,%rcx
  40194f:	48 09 c1             	or     %rax,%rcx
                for (int x = 0 ; x < data->other_count; x++) {
  401952:	83 bb 08 02 00 00 00 	cmpl   $0x0,0x208(%rbx)
  401959:	7e ba                	jle    401915 <disruptor_thread+0x255>
                  me->data[changed].complete[x] = 0;
  40195b:	48 89 d0             	mov    %rdx,%rax
                for (int x = 0 ; x < data->other_count; x++) {
  40195e:	31 f6                	xor    %esi,%esi
                  me->data[changed].complete[x] = 0;
  401960:	48 c1 e0 09          	shl    $0x9,%rax
  401964:	48 03 45 18          	add    0x18(%rbp),%rax
  401968:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
  40196f:	4c 63 c6             	movslq %esi,%r8
                for (int x = 0 ; x < data->other_count; x++) {
  401972:	83 c6 01             	add    $0x1,%esi
                  me->data[changed].complete[x] = 0;
  401975:	42 c7 04 80 00 00 00 00 	movl   $0x0,(%rax,%r8,4)
                for (int x = 0 ; x < data->other_count; x++) {
  40197d:	39 b3 08 02 00 00    	cmp    %esi,0x208(%rbx)
  401983:	7f ea                	jg     40196f <disruptor_thread+0x2af>
  401985:	eb 8e                	jmp    401915 <disruptor_thread+0x255>
  401987:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000401990 <min>:
  if (a < b) return a;
  401990:	48 39 f7             	cmp    %rsi,%rdi
  401993:	7c 02                	jl     401997 <min+0x7>
  if (b < a) return b;
  401995:	7f 09                	jg     4019a0 <min+0x10>
  if (a < b) return a;
  401997:	89 f8                	mov    %edi,%eax
  401999:	c3                   	ret
  40199a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (b < a) return b;
  4019a0:	89 f0                	mov    %esi,%eax
}
  4019a2:	c3                   	ret

Disassembly of section .fini:

00000000004019a4 <_fini>:
  4019a4:	f3 0f 1e fa          	endbr64
  4019a8:	48 83 ec 08          	sub    $0x8,%rsp
  4019ac:	48 83 c4 08          	add    $0x8,%rsp
  4019b0:	c3                   	ret
