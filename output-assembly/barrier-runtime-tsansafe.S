
barrier-runtime-tsansafe:     file format elf64-x86-64


Disassembly of section .init:

0000000000402000 <_init>:
  402000:	f3 0f 1e fa          	endbr64
  402004:	48 83 ec 08          	sub    $0x8,%rsp
  402008:	48 8b 05 e1 6f 00 00 	mov    0x6fe1(%rip),%rax        # 408ff0 <__gmon_start__@Base>
  40200f:	48 85 c0             	test   %rax,%rax
  402012:	74 02                	je     402016 <_init+0x16>
  402014:	ff d0                	call   *%rax
  402016:	48 83 c4 08          	add    $0x8,%rsp
  40201a:	c3                   	ret

Disassembly of section .plt:

0000000000402020 <free@plt-0x10>:
  402020:	ff 35 7a 6e 00 00    	push   0x6e7a(%rip)        # 408ea0 <_GLOBAL_OFFSET_TABLE_+0x8>
  402026:	ff 25 7c 6e 00 00    	jmp    *0x6e7c(%rip)        # 408ea8 <_GLOBAL_OFFSET_TABLE_+0x10>
  40202c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000402030 <free@plt>:
  402030:	ff 25 7a 6e 00 00    	jmp    *0x6e7a(%rip)        # 408eb0 <free@GLIBC_2.2.5>
  402036:	68 00 00 00 00       	push   $0x0
  40203b:	e9 e0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402040 <putchar@plt>:
  402040:	ff 25 72 6e 00 00    	jmp    *0x6e72(%rip)        # 408eb8 <putchar@GLIBC_2.2.5>
  402046:	68 01 00 00 00       	push   $0x1
  40204b:	e9 d0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402050 <puts@plt>:
  402050:	ff 25 6a 6e 00 00    	jmp    *0x6e6a(%rip)        # 408ec0 <puts@GLIBC_2.2.5>
  402056:	68 02 00 00 00       	push   $0x2
  40205b:	e9 c0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402060 <setsockopt@plt>:
  402060:	ff 25 62 6e 00 00    	jmp    *0x6e62(%rip)        # 408ec8 <setsockopt@GLIBC_2.2.5>
  402066:	68 03 00 00 00       	push   $0x3
  40206b:	e9 b0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402070 <clock_gettime@plt>:
  402070:	ff 25 5a 6e 00 00    	jmp    *0x6e5a(%rip)        # 408ed0 <clock_gettime@GLIBC_2.17>
  402076:	68 04 00 00 00       	push   $0x4
  40207b:	e9 a0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402080 <strlen@plt>:
  402080:	ff 25 52 6e 00 00    	jmp    *0x6e52(%rip)        # 408ed8 <strlen@GLIBC_2.2.5>
  402086:	68 05 00 00 00       	push   $0x5
  40208b:	e9 90 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402090 <__stack_chk_fail@plt>:
  402090:	ff 25 4a 6e 00 00    	jmp    *0x6e4a(%rip)        # 408ee0 <__stack_chk_fail@GLIBC_2.4>
  402096:	68 06 00 00 00       	push   $0x6
  40209b:	e9 80 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020a0 <io_uring_submit@plt>:
  4020a0:	ff 25 42 6e 00 00    	jmp    *0x6e42(%rip)        # 408ee8 <io_uring_submit@LIBURING_2.0>
  4020a6:	68 07 00 00 00       	push   $0x7
  4020ab:	e9 70 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020b0 <nanosleep@plt>:
  4020b0:	ff 25 3a 6e 00 00    	jmp    *0x6e3a(%rip)        # 408ef0 <nanosleep@GLIBC_2.2.5>
  4020b6:	68 08 00 00 00       	push   $0x8
  4020bb:	e9 60 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020c0 <strrchr@plt>:
  4020c0:	ff 25 32 6e 00 00    	jmp    *0x6e32(%rip)        # 408ef8 <strrchr@GLIBC_2.2.5>
  4020c6:	68 09 00 00 00       	push   $0x9
  4020cb:	e9 50 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020d0 <close@plt>:
  4020d0:	ff 25 2a 6e 00 00    	jmp    *0x6e2a(%rip)        # 408f00 <close@GLIBC_2.2.5>
  4020d6:	68 0a 00 00 00       	push   $0xa
  4020db:	e9 40 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020e0 <strtok_r@plt>:
  4020e0:	ff 25 22 6e 00 00    	jmp    *0x6e22(%rip)        # 408f08 <strtok_r@GLIBC_2.2.5>
  4020e6:	68 0b 00 00 00       	push   $0xb
  4020eb:	e9 30 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020f0 <read@plt>:
  4020f0:	ff 25 1a 6e 00 00    	jmp    *0x6e1a(%rip)        # 408f10 <read@GLIBC_2.2.5>
  4020f6:	68 0c 00 00 00       	push   $0xc
  4020fb:	e9 20 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402100 <calloc@plt>:
  402100:	ff 25 12 6e 00 00    	jmp    *0x6e12(%rip)        # 408f18 <calloc@GLIBC_2.2.5>
  402106:	68 0d 00 00 00       	push   $0xd
  40210b:	e9 10 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402110 <strcmp@plt>:
  402110:	ff 25 0a 6e 00 00    	jmp    *0x6e0a(%rip)        # 408f20 <strcmp@GLIBC_2.2.5>
  402116:	68 0e 00 00 00       	push   $0xe
  40211b:	e9 00 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402120 <__memcpy_chk@plt>:
  402120:	ff 25 02 6e 00 00    	jmp    *0x6e02(%rip)        # 408f28 <__memcpy_chk@GLIBC_2.3.4>
  402126:	68 0f 00 00 00       	push   $0xf
  40212b:	e9 f0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402130 <stat@plt>:
  402130:	ff 25 fa 6d 00 00    	jmp    *0x6dfa(%rip)        # 408f30 <stat@GLIBC_2.33>
  402136:	68 10 00 00 00       	push   $0x10
  40213b:	e9 e0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402140 <memcpy@plt>:
  402140:	ff 25 f2 6d 00 00    	jmp    *0x6df2(%rip)        # 408f38 <memcpy@GLIBC_2.14>
  402146:	68 11 00 00 00       	push   $0x11
  40214b:	e9 d0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402150 <io_uring_queue_init@plt>:
  402150:	ff 25 ea 6d 00 00    	jmp    *0x6dea(%rip)        # 408f40 <io_uring_queue_init@LIBURING_2.0>
  402156:	68 12 00 00 00       	push   $0x12
  40215b:	e9 c0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402160 <eventfd_write@plt>:
  402160:	ff 25 e2 6d 00 00    	jmp    *0x6de2(%rip)        # 408f48 <eventfd_write@GLIBC_2.7>
  402166:	68 13 00 00 00       	push   $0x13
  40216b:	e9 b0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402170 <malloc@plt>:
  402170:	ff 25 da 6d 00 00    	jmp    *0x6dda(%rip)        # 408f50 <malloc@GLIBC_2.2.5>
  402176:	68 14 00 00 00       	push   $0x14
  40217b:	e9 a0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402180 <listen@plt>:
  402180:	ff 25 d2 6d 00 00    	jmp    *0x6dd2(%rip)        # 408f58 <listen@GLIBC_2.2.5>
  402186:	68 15 00 00 00       	push   $0x15
  40218b:	e9 90 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402190 <__strcpy_chk@plt>:
  402190:	ff 25 ca 6d 00 00    	jmp    *0x6dca(%rip)        # 408f60 <__strcpy_chk@GLIBC_2.3.4>
  402196:	68 16 00 00 00       	push   $0x16
  40219b:	e9 80 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021a0 <__io_uring_get_cqe@plt>:
  4021a0:	ff 25 c2 6d 00 00    	jmp    *0x6dc2(%rip)        # 408f68 <__io_uring_get_cqe@LIBURING_2.0>
  4021a6:	68 17 00 00 00       	push   $0x17
  4021ab:	e9 70 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021b0 <__printf_chk@plt>:
  4021b0:	ff 25 ba 6d 00 00    	jmp    *0x6dba(%rip)        # 408f70 <__printf_chk@GLIBC_2.3.4>
  4021b6:	68 18 00 00 00       	push   $0x18
  4021bb:	e9 60 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021c0 <bind@plt>:
  4021c0:	ff 25 b2 6d 00 00    	jmp    *0x6db2(%rip)        # 408f78 <bind@GLIBC_2.2.5>
  4021c6:	68 19 00 00 00       	push   $0x19
  4021cb:	e9 50 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021d0 <pthread_create@plt>:
  4021d0:	ff 25 aa 6d 00 00    	jmp    *0x6daa(%rip)        # 408f80 <pthread_create@GLIBC_2.34>
  4021d6:	68 1a 00 00 00       	push   $0x1a
  4021db:	e9 40 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021e0 <open@plt>:
  4021e0:	ff 25 a2 6d 00 00    	jmp    *0x6da2(%rip)        # 408f88 <open@GLIBC_2.2.5>
  4021e6:	68 1b 00 00 00       	push   $0x1b
  4021eb:	e9 30 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021f0 <perror@plt>:
  4021f0:	ff 25 9a 6d 00 00    	jmp    *0x6d9a(%rip)        # 408f90 <perror@GLIBC_2.2.5>
  4021f6:	68 1c 00 00 00       	push   $0x1c
  4021fb:	e9 20 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402200 <exit@plt>:
  402200:	ff 25 92 6d 00 00    	jmp    *0x6d92(%rip)        # 408f98 <exit@GLIBC_2.2.5>
  402206:	68 1d 00 00 00       	push   $0x1d
  40220b:	e9 10 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402210 <eventfd@plt>:
  402210:	ff 25 8a 6d 00 00    	jmp    *0x6d8a(%rip)        # 408fa0 <eventfd@GLIBC_2.7>
  402216:	68 1e 00 00 00       	push   $0x1e
  40221b:	e9 00 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402220 <fwrite@plt>:
  402220:	ff 25 82 6d 00 00    	jmp    *0x6d82(%rip)        # 408fa8 <fwrite@GLIBC_2.2.5>
  402226:	68 1f 00 00 00       	push   $0x1f
  40222b:	e9 f0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402230 <__fprintf_chk@plt>:
  402230:	ff 25 7a 6d 00 00    	jmp    *0x6d7a(%rip)        # 408fb0 <__fprintf_chk@GLIBC_2.3.4>
  402236:	68 20 00 00 00       	push   $0x20
  40223b:	e9 e0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402240 <io_uring_register_eventfd@plt>:
  402240:	ff 25 72 6d 00 00    	jmp    *0x6d72(%rip)        # 408fb8 <io_uring_register_eventfd@LIBURING_2.0>
  402246:	68 21 00 00 00       	push   $0x21
  40224b:	e9 d0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402250 <pthread_join@plt>:
  402250:	ff 25 6a 6d 00 00    	jmp    *0x6d6a(%rip)        # 408fc0 <pthread_join@GLIBC_2.34>
  402256:	68 22 00 00 00       	push   $0x22
  40225b:	e9 c0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402260 <strerror@plt>:
  402260:	ff 25 62 6d 00 00    	jmp    *0x6d62(%rip)        # 408fc8 <strerror@GLIBC_2.2.5>
  402266:	68 23 00 00 00       	push   $0x23
  40226b:	e9 b0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402270 <__ctype_tolower_loc@plt>:
  402270:	ff 25 5a 6d 00 00    	jmp    *0x6d5a(%rip)        # 408fd0 <__ctype_tolower_loc@GLIBC_2.3>
  402276:	68 24 00 00 00       	push   $0x24
  40227b:	e9 a0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402280 <__sprintf_chk@plt>:
  402280:	ff 25 52 6d 00 00    	jmp    *0x6d52(%rip)        # 408fd8 <__sprintf_chk@GLIBC_2.3.4>
  402286:	68 25 00 00 00       	push   $0x25
  40228b:	e9 90 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402290 <socket@plt>:
  402290:	ff 25 4a 6d 00 00    	jmp    *0x6d4a(%rip)        # 408fe0 <socket@GLIBC_2.2.5>
  402296:	68 26 00 00 00       	push   $0x26
  40229b:	e9 80 fd ff ff       	jmp    402020 <_init+0x20>

Disassembly of section .text:

00000000004022a0 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
  4022a0:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

static inline void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
  4022a6:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  4022ae:	0f 0b                	ud2

00000000004022b0 <add_read_request.cold>:
  4022b0:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  4022b8:	0f 0b                	ud2

00000000004022ba <add_accept_request.cold>:
  4022ba:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  4022c2:	0f 0b                	ud2

00000000004022c4 <io_thread.cold>:
  4022c4:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  4022cc:	0f 0b                	ud2
  4022ce:	66 90                	xchg   %ax,%ax

00000000004022d0 <main>:
    }


  return 0;
}
int main() {
  4022d0:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4022d2:	48 8d 3d ef 41 00 00 	lea    0x41ef(%rip),%rdi        # 4064c8 <_IO_stdin_used+0x4c8>
  4022d9:	41 56                	push   %r14
  4022db:	41 55                	push   %r13
  4022dd:	41 54                	push   %r12
  4022df:	55                   	push   %rbp
  4022e0:	53                   	push   %rbx
  4022e1:	48 83 ec 68          	sub    $0x68,%rsp
  4022e5:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4022ee:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  4022f3:	31 c0                	xor    %eax,%eax
  4022f5:	e8 56 fd ff ff       	call   402050 <puts@plt>
  4022fa:	bf 0a 00 00 00       	mov    $0xa,%edi
  4022ff:	e8 3c fd ff ff       	call   402040 <putchar@plt>
  402304:	48 8d 3d 27 3f 00 00 	lea    0x3f27(%rip),%rdi        # 406232 <_IO_stdin_used+0x232>
  40230b:	e8 40 fd ff ff       	call   402050 <puts@plt>
  402310:	ba 06 00 00 00       	mov    $0x6,%edx
  402315:	48 8d 35 32 3f 00 00 	lea    0x3f32(%rip),%rsi        # 40624e <_IO_stdin_used+0x24e>
  40231c:	31 c0                	xor    %eax,%eax
  40231e:	bf 01 00 00 00       	mov    $0x1,%edi
  402323:	e8 88 fe ff ff       	call   4021b0 <__printf_chk@plt>
  402328:	ba 09 00 00 00       	mov    $0x9,%edx
  40232d:	48 8d 35 34 3f 00 00 	lea    0x3f34(%rip),%rsi        # 406268 <_IO_stdin_used+0x268>
  402334:	31 c0                	xor    %eax,%eax
  402336:	bf 01 00 00 00       	mov    $0x1,%edi
  40233b:	e8 70 fe ff ff       	call   4021b0 <__printf_chk@plt>
  402340:	ba 01 00 00 00       	mov    $0x1,%edx
  402345:	48 8d 35 30 3f 00 00 	lea    0x3f30(%rip),%rsi        # 40627c <_IO_stdin_used+0x27c>
  40234c:	31 c0                	xor    %eax,%eax
  40234e:	bf 01 00 00 00       	mov    $0x1,%edi
  402353:	e8 58 fe ff ff       	call   4021b0 <__printf_chk@plt>
  402358:	ba 01 00 00 00       	mov    $0x1,%edx
  40235d:	48 8d 35 29 3f 00 00 	lea    0x3f29(%rip),%rsi        # 40628d <_IO_stdin_used+0x28d>
  402364:	31 c0                	xor    %eax,%eax
  402366:	bf 01 00 00 00       	mov    $0x1,%edi
  40236b:	e8 40 fe ff ff       	call   4021b0 <__printf_chk@plt>
  402370:	ba 01 00 00 00       	mov    $0x1,%edx
  402375:	48 8d 35 29 3f 00 00 	lea    0x3f29(%rip),%rsi        # 4062a5 <_IO_stdin_used+0x2a5>
  40237c:	31 c0                	xor    %eax,%eax
  40237e:	bf 01 00 00 00       	mov    $0x1,%edi
  402383:	e8 28 fe ff ff       	call   4021b0 <__printf_chk@plt>
  402388:	ba 01 00 00 00       	mov    $0x1,%edx
  40238d:	48 8d 35 94 41 00 00 	lea    0x4194(%rip),%rsi        # 406528 <_IO_stdin_used+0x528>
  402394:	31 c0                	xor    %eax,%eax
  402396:	bf 01 00 00 00       	mov    $0x1,%edi
  40239b:	e8 10 fe ff ff       	call   4021b0 <__printf_chk@plt>
  4023a0:	ba 01 00 00 00       	mov    $0x1,%edx
  4023a5:	48 8d 35 ac 41 00 00 	lea    0x41ac(%rip),%rsi        # 406558 <_IO_stdin_used+0x558>
  4023ac:	31 c0                	xor    %eax,%eax
  4023ae:	bf 01 00 00 00       	mov    $0x1,%edi
  4023b3:	e8 f8 fd ff ff       	call   4021b0 <__printf_chk@plt>
  4023b8:	ba 40 42 0f 00       	mov    $0xf4240,%edx
  4023bd:	48 8d 35 fd 3e 00 00 	lea    0x3efd(%rip),%rsi        # 4062c1 <_IO_stdin_used+0x2c1>
  4023c4:	31 c0                	xor    %eax,%eax
  4023c6:	bf 01 00 00 00       	mov    $0x1,%edi
  4023cb:	e8 e0 fd ff ff       	call   4021b0 <__printf_chk@plt>
  4023d0:	ba 1e 00 00 00       	mov    $0x1e,%edx
  4023d5:	48 8d 35 ff 3e 00 00 	lea    0x3eff(%rip),%rsi        # 4062db <_IO_stdin_used+0x2db>
  4023dc:	31 c0                	xor    %eax,%eax
  4023de:	bf 01 00 00 00       	mov    $0x1,%edi
  4023e3:	e8 c8 fd ff ff       	call   4021b0 <__printf_chk@plt>
  4023e8:	48 8d 3d df 3c 00 00 	lea    0x3cdf(%rip),%rdi        # 4060ce <_IO_stdin_used+0xce>
  4023ef:	e8 5c fc ff ff       	call   402050 <puts@plt>
  printf("intrathread message buffer size = %ld\n", messages_limit);
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  struct ProtectedState *protected_state = calloc(1, sizeof(struct ProtectedState));
  4023f4:	be 18 00 00 00       	mov    $0x18,%esi
  4023f9:	bf 01 00 00 00       	mov    $0x1,%edi
  4023fe:	e8 fd fc ff ff       	call   402100 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  402403:	be 98 00 00 00       	mov    $0x98,%esi
  402408:	bf 09 00 00 00       	mov    $0x9,%edi
  struct ProtectedState *protected_state = calloc(1, sizeof(struct ProtectedState));
  40240d:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  402412:	e8 e9 fc ff ff       	call   402100 <calloc@plt>
  int barrier_count = thread_count;
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
  402417:	be 10 00 00 00       	mov    $0x10,%esi
  40241c:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  402421:	49 89 c7             	mov    %rax,%r15
  402424:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
  402429:	e8 d2 fc ff ff       	call   402100 <calloc@plt>
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  40242e:	be 10 00 00 00       	mov    $0x10,%esi
  402433:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
  402438:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
  40243e:	48 89 c3             	mov    %rax,%rbx
  402441:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  402446:	e8 b5 fc ff ff       	call   402100 <calloc@plt>
  40244b:	4c 89 7c 24 48       	mov    %r15,0x48(%rsp)
  402450:	48 89 43 08          	mov    %rax,0x8(%rbx)
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
  402454:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  40245b:	48 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%rsp)
    }
  }
  int external_thread_index = 0;
  402464:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
  40246c:	0f 1f 40 00          	nopl   0x0(%rax)
  int timestamp_limit = 100;
  for (int x = 0 ; x < total_threads ; x++) {
    thread_data[x].threads = thread_data;
  402470:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  402475:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    thread_data[x].task_count = total_barrier_count;
    thread_data[x].protected_state = protected_state;
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  40247a:	be 10 00 00 00       	mov    $0x10,%esi
    thread_data[x].task_timestamp_limit = timestamp_limit;

      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
      thread_data[x].tasks = barriers;

      for (int y = 0 ; y < total_barrier_count ; y++) {
  40247f:	31 db                	xor    %ebx,%ebx
    thread_data[x].task_count = total_barrier_count;
  402481:	41 c7 47 28 07 00 00 00 	movl   $0x7,0x28(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  402489:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].threads = thread_data;
  40248e:	49 89 47 10          	mov    %rax,0x10(%r15)
    thread_data[x].thread_count = thread_count;
  402492:	48 8b 05 f7 44 00 00 	mov    0x44f7(%rip),%rax        # 406990 <_IO_stdin_used+0x990>
    thread_data[x].thread_index = x;
  402499:	45 89 37             	mov    %r14d,(%r15)
    thread_data[x].thread_count = thread_count;
  40249c:	49 89 47 18          	mov    %rax,0x18(%r15)
    thread_data[x].protected_state = protected_state;
  4024a0:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
  4024a5:	44 89 74 24 20       	mov    %r14d,0x20(%rsp)
  4024aa:	49 89 47 30          	mov    %rax,0x30(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  4024ae:	e8 4d fc ff ff       	call   402100 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  4024b3:	be 10 00 00 00       	mov    $0x10,%esi
  4024b8:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  4024bd:	49 89 47 50          	mov    %rax,0x50(%r15)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  4024c1:	e8 3a fc ff ff       	call   402100 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  4024c6:	be 28 00 00 00       	mov    $0x28,%esi
  4024cb:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
  4024d0:	66 0f 6f 25 98 44 00 00 	movdqa 0x4498(%rip),%xmm4        # 406970 <_IO_stdin_used+0x970>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  4024d8:	49 89 47 58          	mov    %rax,0x58(%r15)
    thread_data[x].timestamp_count = 0;
  4024dc:	41 0f 11 67 68       	movups %xmm4,0x68(%r15)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  4024e1:	e8 1a fc ff ff       	call   402100 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  4024e6:	be 80 02 00 00       	mov    $0x280,%esi
  4024eb:	bf 07 00 00 00       	mov    $0x7,%edi
    thread_data[x].task_timestamp_count = 0;
  4024f0:	66 0f 6f 2d 78 44 00 00 	movdqa 0x4478(%rip),%xmm5        # 406970 <_IO_stdin_used+0x970>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  4024f8:	49 89 47 78          	mov    %rax,0x78(%r15)
    thread_data[x].task_timestamp_count = 0;
  4024fc:	41 0f 11 af 80 00 00 00 	movups %xmm5,0x80(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  402504:	e8 f7 fb ff ff       	call   402100 <calloc@plt>
      thread_data[x].tasks = barriers;
  402509:	44 89 74 24 2c       	mov    %r14d,0x2c(%rsp)
  40250e:	49 89 47 20          	mov    %rax,0x20(%r15)
      for (int y = 0 ; y < total_barrier_count ; y++) {
  402512:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              a       x
              s         x
              k           x
        */
        if (x == y) {
            thread_data[x].tasks[y].protected = do_protected_write; 
  402518:	48 63 c3             	movslq %ebx,%rax
  40251b:	4c 8d 24 80          	lea    (%rax,%rax,4),%r12
  40251f:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  402524:	49 c1 e4 07          	shl    $0x7,%r12
  402528:	4c 89 24 24          	mov    %r12,(%rsp)
        if (x == y) {
  40252c:	3b 5c 24 08          	cmp    0x8(%rsp),%ebx
  402530:	0f 84 7a 09 00 00    	je     402eb0 <main+0xbe0>
        }
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
  402536:	bf 06 00 00 00       	mov    $0x6,%edi
  40253b:	be 20 00 00 00       	mov    $0x20,%esi
  402540:	e8 bb fb ff ff       	call   402100 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
  402545:	48 8b 3c 24          	mov    (%rsp),%rdi
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
  402549:	48 89 c1             	mov    %rax,%rcx
        thread_data[x].tasks[y].mailboxes = mailboxes;
  40254c:	49 8b 47 20          	mov    0x20(%r15),%rax
  402550:	49 89 cd             	mov    %rcx,%r13
  402553:	48 8d a9 c0 00 00 00 	lea    0xc0(%rcx),%rbp
  40255a:	48 89 8c 38 28 02 00 00 	mov    %rcx,0x228(%rax,%rdi,1)
        // long messages_limit = 20;/*9999999;*/
        for (int b = 0 ; b < thread_count ; b++) {
  402562:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402568:	be 08 00 00 00       	mov    $0x8,%esi
  40256d:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < thread_count ; b++) {
  402572:	49 83 c5 20          	add    $0x20,%r13
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402576:	e8 85 fb ff ff       	call   402100 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  40257b:	be 08 00 00 00       	mov    $0x8,%esi
  402580:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402585:	49 89 c6             	mov    %rax,%r14
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402588:	e8 73 fb ff ff       	call   402100 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
  40258d:	be 00 01 00 00       	mov    $0x100,%esi
  402592:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402597:	49 89 c4             	mov    %rax,%r12
          struct Data *data = calloc(2, sizeof(struct Data));
  40259a:	e8 61 fb ff ff       	call   402100 <calloc@plt>
          mailboxes[b].lower = &data[0];
          mailboxes[b].higher = &data[1];
          data[0].messages = messages;
          data[1].messages = messages2;
          data[0].messages_limit = messages_limit;
          data[0].messages_count = 0;
  40259f:	66 0f 6f 15 d9 43 00 00 	movdqa 0x43d9(%rip),%xmm2        # 406980 <_IO_stdin_used+0x980>
          mailboxes[b].higher = &data[1];
  4025a7:	48 8d 90 00 01 00 00 	lea    0x100(%rax),%rdx
          mailboxes[b].lower = &data[0];
  4025ae:	66 48 0f 6e c0       	movq   %rax,%xmm0
          data[0].messages = messages;
  4025b3:	4c 89 30             	mov    %r14,(%rax)
          mailboxes[b].lower = &data[0];
  4025b6:	66 48 0f 6e ca       	movq   %rdx,%xmm1
          data[1].messages = messages2;
  4025bb:	4c 89 a0 00 01 00 00 	mov    %r12,0x100(%rax)
          mailboxes[b].lower = &data[0];
  4025c2:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
          data[0].messages_count = 0;
  4025c6:	0f 29 90 80 00 00 00 	movaps %xmm2,0x80(%rax)
          mailboxes[b].lower = &data[0];
  4025cd:	41 0f 11 45 e0       	movups %xmm0,-0x20(%r13)
          data[1].messages_count = 0;
  4025d2:	0f 29 90 80 01 00 00 	movaps %xmm2,0x180(%rax)
        for (int b = 0 ; b < thread_count ; b++) {
  4025d9:	49 39 ed             	cmp    %rbp,%r13
  4025dc:	75 8a                	jne    402568 <main+0x298>
          data[1].messages_limit = messages_limit;
        }

        char *message = malloc(sizeof(char) * 256);
  4025de:	be 01 00 00 00       	mov    $0x1,%esi
  4025e3:	bf 00 01 00 00       	mov    $0x100,%edi
        memset(message, '\0', 256);
        sprintf(message, "Sending message from thread %d task %d", x, y);
        messaged->message = message;
        messaged->task_index = y;
        messaged->thread_index = x;
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  4025e8:	44 8d 6b 01          	lea    0x1(%rbx),%r13d
        char *message = malloc(sizeof(char) * 256);
  4025ec:	e8 0f fb ff ff       	call   402100 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
  4025f1:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
  4025f6:	48 89 c5             	mov    %rax,%rbp
        struct Message *messaged = malloc(sizeof(struct Message));
  4025f9:	e8 72 fb ff ff       	call   402170 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  4025fe:	44 8b 74 24 20       	mov    0x20(%rsp),%r14d
  402603:	48 89 ef             	mov    %rbp,%rdi
  402606:	41 89 d9             	mov    %ebx,%r9d
  402609:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  40260e:	48 8d 0d 6b 3f 00 00 	lea    0x3f6b(%rip),%rcx        # 406580 <_IO_stdin_used+0x580>
  402615:	ba 00 01 00 00       	mov    $0x100,%edx
  40261a:	31 c0                	xor    %eax,%eax
  40261c:	45 89 f0             	mov    %r14d,%r8d
  40261f:	be 01 00 00 00       	mov    $0x1,%esi
  402624:	e8 57 fc ff ff       	call   402280 <__sprintf_chk@plt>
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402629:	49 8b 57 20          	mov    0x20(%r15),%rdx
        messaged->message = message;
  40262d:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402632:	b9 ab aa aa aa       	mov    $0xaaaaaaab,%ecx
  402637:	48 8b 04 24          	mov    (%rsp),%rax
        thread_data[x].tasks[y].message = messaged;
        thread_data[x].tasks[y].sending = 1;
        thread_data[x].tasks[y].snapshot_count = 999999;
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  40263b:	be 20 00 00 00       	mov    $0x20,%esi
  402640:	bf 3f 42 0f 00       	mov    $0xf423f,%edi
        messaged->thread_index = x;
  402645:	f3 0f 7e 44 24 08    	movq   0x8(%rsp),%xmm0
        messaged->message = message;
  40264b:	49 89 2a             	mov    %rbp,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  40264e:	48 8d 2c 02          	lea    (%rdx,%rax,1),%rbp
  402652:	44 89 e8             	mov    %r13d,%eax
        messaged->thread_index = x;
  402655:	0f 16 44 24 10       	movhps 0x10(%rsp),%xmm0
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  40265a:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
  40265f:	48 0f af c1          	imul   %rcx,%rax
  402663:	44 89 e9             	mov    %r13d,%ecx
        messaged->thread_index = x;
  402666:	41 0f 11 42 08       	movups %xmm0,0x8(%r10)
        thread_data[x].tasks[y].message = messaged;
  40266b:	4c 89 95 40 02 00 00 	mov    %r10,0x240(%rbp)
        thread_data[x].tasks[y].snapshot_count = 999999;
  402672:	48 c7 85 10 02 00 00 3f 42 0f 00 	movq   $0xf423f,0x210(%rbp)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  40267d:	48 c1 e8 22          	shr    $0x22,%rax
  402681:	8d 04 40             	lea    (%rax,%rax,2),%eax
  402684:	01 c0                	add    %eax,%eax
  402686:	29 c1                	sub    %eax,%ecx
  402688:	89 8d 48 02 00 00    	mov    %ecx,0x248(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  40268e:	e8 6d fa ff ff       	call   402100 <calloc@plt>
            thread_data[x].tasks[y].run = barriered_nulltask; 
          }
          */
          thread_data[x].tasks[y].run = barriered_work; 
        } else {
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
  402693:	8b 74 24 28          	mov    0x28(%rsp),%esi
        if (y == barrier_count - 1) {
  402697:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
        thread_data[x].tasks[y].task_index = y;
  40269c:	89 5d 00             	mov    %ebx,0x0(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  40269f:	48 89 85 08 02 00 00 	mov    %rax,0x208(%rbp)
        thread_data[x].tasks[y].available = 1;
  4026a6:	48 8b 05 eb 42 00 00 	mov    0x42eb(%rip),%rax        # 406998 <_IO_stdin_used+0x998>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
  4026ad:	85 f6                	test   %esi,%esi
        thread_data[x].tasks[y].thread_index = x;
  4026af:	44 89 b5 30 01 00 00 	mov    %r14d,0x130(%rbp)
        thread_data[x].tasks[y].available = 1;
  4026b6:	48 89 85 80 01 00 00 	mov    %rax,0x180(%rbp)
        thread_data[x].tasks[y].sending = 1;
  4026bd:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
  4026c7:	48 89 85 38 02 00 00 	mov    %rax,0x238(%rbp)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
  4026ce:	0f 9e c0             	setle  %al
        if (y == barrier_count - 1) {
  4026d1:	83 fb 05             	cmp    $0x5,%ebx
        thread_data[x].tasks[y].current_snapshot = 0;
  4026d4:	48 c7 85 18 02 00 00 00 00 00 00 	movq   $0x0,0x218(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
  4026df:	4c 89 bd 28 01 00 00 	mov    %r15,0x128(%rbp)
        thread_data[x].tasks[y].arrived = 0;
  4026e6:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        thread_data[x].tasks[y].thread_count = thread_count;
  4026f0:	c7 85 34 01 00 00 06 00 00 00 	movl   $0x6,0x134(%rbp)
        if (y == barrier_count - 1) {
  4026fa:	0f 84 90 07 00 00    	je     402e90 <main+0xbc0>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
  402700:	3b 5c 24 2c          	cmp    0x2c(%rsp),%ebx
  402704:	75 5a                	jne    402760 <main+0x490>
  402706:	84 c0                	test   %al,%al
  402708:	74 56                	je     402760 <main+0x490>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  40270a:	8b 54 24 20          	mov    0x20(%rsp),%edx
  40270e:	48 8d 35 93 3e 00 00 	lea    0x3e93(%rip),%rsi        # 4065a8 <_IO_stdin_used+0x5a8>
  402715:	bf 01 00 00 00       	mov    $0x1,%edi
  40271a:	31 c0                	xor    %eax,%eax
  40271c:	e8 8f fa ff ff       	call   4021b0 <__printf_chk@plt>
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
  402721:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
  402726:	49 8b 57 20          	mov    0x20(%r15),%rdx
            thread_data[x].buffers = &buffers[external_thread_index++];
  40272a:	c7 44 24 28 01 00 00 00 	movl   $0x1,0x28(%rsp)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
  402732:	48 8b 1c 24          	mov    (%rsp),%rbx
            thread_data[x].buffers = &buffers[external_thread_index++];
  402736:	49 89 47 38          	mov    %rax,0x38(%r15)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
  40273a:	48 c7 c0 70 50 40 00 	mov    $0x405070,%rax
  402741:	48 89 84 1a 18 01 00 00 	mov    %rax,0x118(%rdx,%rbx,1)
      for (int y = 0 ; y < total_barrier_count ; y++) {
  402749:	41 83 fd 07          	cmp    $0x7,%r13d
  40274d:	74 25                	je     402774 <main+0x4a4>
  int external_thread_index = 0;
  40274f:	44 89 eb             	mov    %r13d,%ebx
  402752:	e9 c1 fd ff ff       	jmp    402518 <main+0x248>
  402757:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
  402760:	48 c7 c0 40 4d 40 00 	mov    $0x404d40,%rax
  402767:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
  40276e:	41 83 fd 07          	cmp    $0x7,%r13d
  402772:	75 db                	jne    40274f <main+0x47f>

          }
        }
      }
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
  402774:	48 c7 c0 00 30 40 00 	mov    $0x403000,%rax
  for (int x = 0 ; x < total_threads ; x++) {
  40277b:	48 83 44 24 08 01    	addq   $0x1,0x8(%rsp)
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
  402781:	4c 89 ba 28 10 00 00 	mov    %r15,0x1028(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
  402788:	49 81 c7 98 00 00 00 	add    $0x98,%r15
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
  40278f:	48 89 82 18 10 00 00 	mov    %rax,0x1018(%rdx)
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
      thread_data[x].tasks[barrier_count].thread_index = x; 
  402796:	8b 44 24 20          	mov    0x20(%rsp),%eax
      thread_data[x].tasks[barrier_count].arrived = 0; 
  40279a:	c7 82 80 0f 00 00 00 00 00 00 	movl   $0x0,0xf80(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = x; 
  4027a4:	89 82 30 10 00 00    	mov    %eax,0x1030(%rdx)
      thread_data[x].tasks[barrier_count].available = 1; 
  4027aa:	48 8b 05 e7 41 00 00 	mov    0x41e7(%rip),%rax        # 406998 <_IO_stdin_used+0x998>
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
  4027b1:	c7 82 00 0f 00 00 06 00 00 00 	movl   $0x6,0xf00(%rdx)
      thread_data[x].tasks[barrier_count].available = 1; 
  4027bb:	48 89 82 80 10 00 00 	mov    %rax,0x1080(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
  4027c2:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
  4027c7:	c7 82 34 10 00 00 06 00 00 00 	movl   $0x6,0x1034(%rdx)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
  4027d1:	c7 82 3c 11 00 00 06 00 00 00 	movl   $0x6,0x113c(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
  4027db:	48 83 f8 09          	cmp    $0x9,%rax
  4027df:	0f 85 8b fc ff ff    	jne    402470 <main+0x1a0>
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].threads = thread_data;
  4027e5:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    thread_data[x].thread_index = x;
    thread_data[x].task_count = total_barrier_count;
  }
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  4027ea:	b9 01 00 00 00       	mov    $0x1,%ecx
    thread_data[x].threads = thread_data;
  4027ef:	48 8d 98 28 04 00 00 	lea    0x428(%rax),%rbx
  4027f6:	4c 8d 78 20          	lea    0x20(%rax),%r15
    thread_data[x].thread_count = thread_count;
  4027fa:	c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%rax)
    thread_data[x].threads = thread_data;
  402804:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    thread_data[x].thread_index = x;
  402809:	c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%rax)
    thread_data[x].task_count = total_barrier_count;
  402813:	c7 80 50 04 00 00 07 00 00 00 	movl   $0x7,0x450(%rax)
    thread_data[x].threads = thread_data;
  40281d:	48 89 80 38 04 00 00 	mov    %rax,0x438(%rax)
  for (int n = 0 ; n < thread_count ; n++) {
  402824:	48 05 b0 03 00 00    	add    $0x3b0,%rax
  40282a:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  40282f:	48 89 c6             	mov    %rax,%rsi
    thread_data[x].task_count = total_barrier_count;
  402832:	4c 89 f8             	mov    %r15,%rax
  402835:	0f 1f 00             	nopl   (%rax)
    thread_data[n].tasks[0].scheduled = 1;
  402838:	48 8b 10             	mov    (%rax),%rdx
  40283b:	89 cb                	mov    %ecx,%ebx
  40283d:	87 9a 00 02 00 00    	xchg   %ebx,0x200(%rdx)
  for (int n = 0 ; n < thread_count ; n++) {
  402843:	48 05 98 00 00 00    	add    $0x98,%rax
  402849:	48 39 c6             	cmp    %rax,%rsi
  40284c:	75 ea                	jne    402838 <main+0x568>
  }

  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40284e:	be 38 00 00 00       	mov    $0x38,%esi
  402853:	bf 09 00 00 00       	mov    $0x9,%edi
  thread_data[thread_count].thread_count = thread_count;
  thread_data[thread_count].thread_index = 0;

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
  for (int x = 0 ; x < thread_count ; x++) {
  402858:	45 31 ed             	xor    %r13d,%r13d
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40285b:	e8 a0 f8 ff ff       	call   402100 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402860:	be 38 00 00 00       	mov    $0x38,%esi
  402865:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40286a:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40286d:	e8 8e f8 ff ff       	call   402100 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402872:	be 38 00 00 00       	mov    $0x38,%esi
  402877:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40287c:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402880:	e8 7b f8 ff ff       	call   402100 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  402885:	be 08 00 00 00       	mov    $0x8,%esi
  40288a:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40288f:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  402894:	e8 67 f8 ff ff       	call   402100 <calloc@plt>
  thread_data[thread_count].task_count = total_barrier_count;
  402899:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
  40289e:	ba 06 00 00 00       	mov    $0x6,%edx
  4028a3:	48 8d 35 45 3a 00 00 	lea    0x3a45(%rip),%rsi        # 4062ef <_IO_stdin_used+0x2ef>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  4028aa:	49 89 c4             	mov    %rax,%r12
  thread_data[thread_count].task_count = total_barrier_count;
  4028ad:	48 8b 05 ec 40 00 00 	mov    0x40ec(%rip),%rax        # 4069a0 <_IO_stdin_used+0x9a0>
  4028b4:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].threads = thread_data;
  4028b9:	4d 89 b6 a0 03 00 00 	mov    %r14,0x3a0(%r14)
  4028c0:	4c 89 e5             	mov    %r12,%rbp
  thread_data[thread_count].task_count = total_barrier_count;
  4028c3:	49 89 86 b8 03 00 00 	mov    %rax,0x3b8(%r14)
  4028ca:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
  4028cc:	41 c7 86 a8 03 00 00 06 00 00 00 	movl   $0x6,0x3a8(%r14)
  thread_data[thread_count].thread_index = 0;
  4028d7:	49 c7 86 90 03 00 00 00 00 00 00 	movq   $0x0,0x390(%r14)
  4028e2:	e8 c9 f8 ff ff       	call   4021b0 <__printf_chk@plt>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
  4028e7:	48 c7 c2 10 34 40 00 	mov    $0x403410,%rdx
  4028ee:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
  4028f3:	49 8d 8e 90 03 00 00 	lea    0x390(%r14),%rcx
  4028fa:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
  402901:	4c 8d 35 c0 3c 00 00 	lea    0x3cc0(%rip),%r14        # 4065c8 <_IO_stdin_used+0x5c8>
  402908:	e8 c3 f8 ff ff       	call   4021d0 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
  40290d:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
  402912:	45 89 ec             	mov    %r13d,%r12d
  402915:	49 89 dd             	mov    %rbx,%r13
  402918:	48 8b 5c 24 48       	mov    0x48(%rsp),%rbx
  40291d:	0f 1f 00             	nopl   (%rax)
    thread_data[x].type = WORKER;
  402920:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
  402927:	44 89 e2             	mov    %r12d,%edx
  40292a:	4c 89 f6             	mov    %r14,%rsi
  40292d:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
  40292f:	c7 43 2c 01 00 00 00 	movl   $0x1,0x2c(%rbx)
  402936:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < thread_count ; x++) {
  40293b:	41 83 c4 01          	add    $0x1,%r12d
  40293f:	e8 6c f8 ff ff       	call   4021b0 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
  402944:	48 89 d9             	mov    %rbx,%rcx
  402947:	4c 89 ee             	mov    %r13,%rsi
  40294a:	48 89 ef             	mov    %rbp,%rdi
  40294d:	48 c7 c2 70 30 40 00 	mov    $0x403070,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
  402954:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
  40295b:	48 83 c5 08          	add    $0x8,%rbp
  40295f:	49 83 c5 38          	add    $0x38,%r13
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
  402963:	e8 68 f8 ff ff       	call   4021d0 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
  402968:	41 83 fc 06          	cmp    $0x6,%r12d
  40296c:	75 b2                	jne    402920 <main+0x650>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
  40296e:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
  402973:	48 8b 1d 2e 40 00 00 	mov    0x402e(%rip),%rbx        # 4069a8 <_IO_stdin_used+0x9a8>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  40297a:	be d8 00 00 00       	mov    $0xd8,%esi
  40297f:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
  402984:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
  402989:	45 31 ed             	xor    %r13d,%r13d
  40298c:	48 8d 6c 24 50       	lea    0x50(%rsp),%rbp
    thread_data[x].task_count = 0;
  402991:	49 89 9e 50 04 00 00 	mov    %rbx,0x450(%r14)
    thread_data[x].type = IO;
  402998:	41 c7 86 2c 04 00 00 02 00 00 00 	movl   $0x2,0x42c(%r14)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  4029a3:	e8 58 f7 ff ff       	call   402100 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
  4029a8:	be 00 08 00 00       	mov    $0x800,%esi
  4029ad:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  4029af:	49 89 86 68 04 00 00 	mov    %rax,0x468(%r14)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
  4029b6:	e8 55 f8 ff ff       	call   402210 <eventfd@plt>
  4029bb:	ba 07 00 00 00       	mov    $0x7,%edx
  4029c0:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].threads = thread_data;
  4029c5:	4d 89 b6 38 04 00 00 	mov    %r14,0x438(%r14)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
  4029cc:	41 89 86 70 04 00 00 	mov    %eax,0x470(%r14)
  4029d3:	48 8d 35 33 39 00 00 	lea    0x3933(%rip),%rsi        # 40630d <_IO_stdin_used+0x30d>
  4029da:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_count = thread_count;
  4029dc:	41 c7 86 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r14)
    thread_data[x].thread_index = x;
  4029e7:	41 c7 86 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r14)
  4029f2:	e8 b9 f7 ff ff       	call   4021b0 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  4029f7:	48 8b 34 24          	mov    (%rsp),%rsi
  4029fb:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
  402a00:	49 8d 7c 24 38       	lea    0x38(%r12),%rdi
  402a05:	48 c7 c2 b0 45 40 00 	mov    $0x4045b0,%rdx
  402a0c:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
  402a13:	e8 b8 f7 ff ff       	call   4021d0 <pthread_create@plt>
  402a18:	ba 08 00 00 00       	mov    $0x8,%edx
  402a1d:	48 8d 35 00 39 00 00 	lea    0x3900(%rip),%rsi        # 406324 <_IO_stdin_used+0x324>
  402a24:	31 c0                	xor    %eax,%eax
  402a26:	bf 01 00 00 00       	mov    $0x1,%edi
  402a2b:	e8 80 f7 ff ff       	call   4021b0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
  402a30:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    thread_data[x].task_count = 0;
  402a35:	49 89 9e e8 04 00 00 	mov    %rbx,0x4e8(%r14)
    thread_data[x].type = EXTERNAL;
  402a3c:	49 8d 8e c0 04 00 00 	lea    0x4c0(%r14),%rcx

    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  402a43:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    thread_data[x].threads = thread_data;
  402a48:	4d 89 b6 d0 04 00 00 	mov    %r14,0x4d0(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  402a4f:	49 8d 7c 24 40       	lea    0x40(%r12),%rdi
  402a54:	48 8d 1d 04 39 00 00 	lea    0x3904(%rip),%rbx        # 40635f <_IO_stdin_used+0x35f>
    thread_data[x].buffers = &buffers[buffer_index];
  402a5b:	49 89 86 f8 04 00 00 	mov    %rax,0x4f8(%r14)
    thread_data[x].thread_count = thread_count;
  402a62:	48 8b 05 27 3f 00 00 	mov    0x3f27(%rip),%rax        # 406990 <_IO_stdin_used+0x990>
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  402a69:	48 c7 c2 50 33 40 00 	mov    $0x403350,%rdx
  402a70:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    thread_data[x].thread_count = thread_count;
  402a77:	49 89 86 d8 04 00 00 	mov    %rax,0x4d8(%r14)
    thread_data[x].thread_index = x;
  402a7e:	48 8b 05 2b 3f 00 00 	mov    0x3f2b(%rip),%rax        # 4069b0 <_IO_stdin_used+0x9b0>
  402a85:	49 89 86 c0 04 00 00 	mov    %rax,0x4c0(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  402a8c:	e8 3f f7 ff ff       	call   4021d0 <pthread_create@plt>
  402a91:	48 8d 3d a9 38 00 00 	lea    0x38a9(%rip),%rdi        # 406341 <_IO_stdin_used+0x341>
  402a98:	e8 b3 f5 ff ff       	call   402050 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
  402a9d:	0f 1f 00             	nopl   (%rax)
    void * result; 
    pthread_join(thread[x], &result);
  402aa0:	4b 8b 3c ec          	mov    (%r12,%r13,8),%rdi
  402aa4:	48 89 ee             	mov    %rbp,%rsi
  402aa7:	e8 a4 f7 ff ff       	call   402250 <pthread_join@plt>
  402aac:	44 89 ea             	mov    %r13d,%edx
  402aaf:	48 89 de             	mov    %rbx,%rsi
  402ab2:	bf 01 00 00 00       	mov    $0x1,%edi
  402ab7:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
  402ab9:	49 83 c5 01          	add    $0x1,%r13
  402abd:	e8 ee f6 ff ff       	call   4021b0 <__printf_chk@plt>
  402ac2:	49 83 fd 09          	cmp    $0x9,%r13
  402ac6:	75 d8                	jne    402aa0 <main+0x7d0>
  }
  long total = 0;
  long v = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  402ac8:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
  long sends = 0;
  402ad0:	45 31 ed             	xor    %r13d,%r13d
  long ingests = 0;
  402ad3:	45 31 e4             	xor    %r12d,%r12d
  long total = 0;
  402ad6:	31 ed                	xor    %ebp,%ebp
  long received = 0;
  402ad8:	48 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%rsp)
  long v = 0;
  402ae1:	45 31 f6             	xor    %r14d,%r14d
  402ae4:	0f 1f 40 00          	nopl   0x0(%rax)
  for (int x = 0 ; x < thread_count ; x++) {

    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402ae8:	41 8b 47 08          	mov    0x8(%r15),%eax
  402aec:	85 c0                	test   %eax,%eax
  402aee:	0f 8e a2 00 00 00    	jle    402b96 <main+0x8c6>
  402af4:	83 e8 01             	sub    $0x1,%eax
      total += thread_data[x].tasks[n].n;
  402af7:	49 8b 17             	mov    (%r15),%rdx
  402afa:	48 8b 3c 24          	mov    (%rsp),%rdi
  402afe:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  402b02:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
  402b07:	48 c1 e0 07          	shl    $0x7,%rax
  402b0b:	48 8d 8a 08 01 00 00 	lea    0x108(%rdx),%rcx
  402b12:	48 8d b4 02 88 03 00 00 	lea    0x388(%rdx,%rax,1),%rsi
  402b1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  402b20:	48 03 29             	add    (%rcx),%rbp
      v += thread_data[x].tasks[n].v;
      ingests += thread_data[x].tasks[n].ingest_count;
      sends += thread_data[x].tasks[n].sends;
      for (int k = 0 ; k < thread_count ; k++) {
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
  402b23:	48 8b 81 20 01 00 00 	mov    0x120(%rcx),%rax
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402b2a:	48 81 c1 80 02 00 00 	add    $0x280,%rcx
      v += thread_data[x].tasks[n].v;
  402b31:	4c 03 b1 88 fd ff ff 	add    -0x278(%rcx),%r14
      ingests += thread_data[x].tasks[n].ingest_count;
  402b38:	4c 03 a1 98 fe ff ff 	add    -0x168(%rcx),%r12
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
  402b3f:	48 8b 50 30          	mov    0x30(%rax),%rdx
  402b43:	48 03 50 10          	add    0x10(%rax),%rdx
  402b47:	48 03 50 50          	add    0x50(%rax),%rdx
  402b4b:	48 03 50 70          	add    0x70(%rax),%rdx
  402b4f:	48 03 90 90 00 00 00 	add    0x90(%rax),%rdx
  402b56:	48 03 90 b0 00 00 00 	add    0xb0(%rax),%rdx
  402b5d:	48 01 d7             	add    %rdx,%rdi
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
  402b60:	48 8b 50 38          	mov    0x38(%rax),%rdx
  402b64:	48 03 50 18          	add    0x18(%rax),%rdx
  402b68:	48 03 50 58          	add    0x58(%rax),%rdx
  402b6c:	48 03 50 78          	add    0x78(%rax),%rdx
  402b70:	48 03 90 98 00 00 00 	add    0x98(%rax),%rdx
  402b77:	48 03 90 b8 00 00 00 	add    0xb8(%rax),%rdx
      sends += thread_data[x].tasks[n].sends;
  402b7e:	4c 03 a9 a8 fe ff ff 	add    -0x158(%rcx),%r13
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
  402b85:	49 01 d0             	add    %rdx,%r8
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402b88:	48 39 f1             	cmp    %rsi,%rcx
  402b8b:	75 93                	jne    402b20 <main+0x850>
  402b8d:	48 89 3c 24          	mov    %rdi,(%rsp)
  402b91:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
      }
    }
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
  402b96:	31 c9                	xor    %ecx,%ecx
  402b98:	31 db                	xor    %ebx,%ebx
  402b9a:	49 83 7f 50 00       	cmpq   $0x0,0x50(%r15)
  402b9f:	48 89 ce             	mov    %rcx,%rsi
  402ba2:	7e 6b                	jle    402c0f <main+0x93f>
  402ba4:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec start = thread_data[x].start[n];
  402ba8:	49 8b 7f 30          	mov    0x30(%r15),%rdi
  402bac:	48 c1 e6 04          	shl    $0x4,%rsi
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
  402bb0:	83 c3 01             	add    $0x1,%ebx
      struct timespec end = thread_data[x].end[n];
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
  402bb3:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      struct timespec start = thread_data[x].start[n];
  402bbd:	48 01 f7             	add    %rsi,%rdi
      struct timespec end = thread_data[x].end[n];
  402bc0:	49 03 77 38          	add    0x38(%r15),%rsi
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
  402bc4:	48 8b 56 08          	mov    0x8(%rsi),%rdx
  402bc8:	48 2b 57 08          	sub    0x8(%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
  402bcc:	48 f7 e2             	mul    %rdx
  402bcf:	31 c0                	xor    %eax,%eax
  402bd1:	48 89 d1             	mov    %rdx,%rcx
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
  402bd4:	48 8b 16             	mov    (%rsi),%rdx
  402bd7:	48 8d 35 95 37 00 00 	lea    0x3795(%rip),%rsi        # 406373 <_IO_stdin_used+0x373>
  402bde:	48 2b 17             	sub    (%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
  402be1:	48 c1 e9 12          	shr    $0x12,%rcx
  402be5:	bf 01 00 00 00       	mov    $0x1,%edi
  402bea:	e8 c1 f5 ff ff       	call   4021b0 <__printf_chk@plt>
  402bef:	49 8b 57 40          	mov    0x40(%r15),%rdx
  402bf3:	bf 01 00 00 00       	mov    $0x1,%edi
  402bf8:	31 c0                	xor    %eax,%eax
  402bfa:	48 8d 35 90 37 00 00 	lea    0x3790(%rip),%rsi        # 406391 <_IO_stdin_used+0x391>
  402c01:	e8 aa f5 ff ff       	call   4021b0 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
  402c06:	48 63 f3             	movslq %ebx,%rsi
  402c09:	49 3b 77 50          	cmp    0x50(%r15),%rsi
  402c0d:	7c 99                	jl     402ba8 <main+0x8d8>
      printf("%ld iterations\n", thread_data[x].iteration_count);
    }
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  402c0f:	45 31 db             	xor    %r11d,%r11d
  402c12:	31 c0                	xor    %eax,%eax
  402c14:	49 83 7f 68 00       	cmpq   $0x0,0x68(%r15)
  402c19:	0f 8e 9f 00 00 00    	jle    402cbe <main+0x9ee>
  402c1f:	48 89 6c 24 10       	mov    %rbp,0x10(%rsp)
  402c24:	4c 89 fd             	mov    %r15,%rbp
  402c27:	45 89 df             	mov    %r11d,%r15d
  402c2a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
  402c30:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  402c34:	48 8b 45 58          	mov    0x58(%rbp),%rax
  402c38:	48 83 ec 08          	sub    $0x8,%rsp
  402c3c:	48 8d 35 ad 39 00 00 	lea    0x39ad(%rip),%rsi        # 4065f0 <_IO_stdin_used+0x5f0>
  402c43:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  402c48:	41 83 c7 01          	add    $0x1,%r15d
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
  402c4c:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
  402c50:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
  402c5a:	48 8b 59 18          	mov    0x18(%rcx),%rbx
  402c5e:	48 2b 59 08          	sub    0x8(%rcx),%rbx
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
  402c62:	48 f7 e3             	mul    %rbx
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
  402c65:	4c 8b 41 10          	mov    0x10(%rcx),%r8
  402c69:	4c 2b 01             	sub    (%rcx),%r8
  402c6c:	31 c0                	xor    %eax,%eax
  402c6e:	8b 49 20             	mov    0x20(%rcx),%ecx
  402c71:	53                   	push   %rbx
  402c72:	48 c1 ea 12          	shr    $0x12,%rdx
  402c76:	49 89 d1             	mov    %rdx,%r9
  402c79:	ba 06 00 00 00       	mov    $0x6,%edx
  402c7e:	e8 2d f5 ff ff       	call   4021b0 <__printf_chk@plt>
  402c83:	48 8d 35 23 37 00 00 	lea    0x3723(%rip),%rsi        # 4063ad <_IO_stdin_used+0x3ad>
  402c8a:	bf 01 00 00 00       	mov    $0x1,%edi
      printf("%ldns per thread\n", (seconds2 / thread_count));
  402c8f:	48 b8 ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%rax
  402c99:	48 f7 e3             	mul    %rbx
  402c9c:	31 c0                	xor    %eax,%eax
  402c9e:	48 c1 ea 02          	shr    $0x2,%rdx
  402ca2:	e8 09 f5 ff ff       	call   4021b0 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  402ca7:	5a                   	pop    %rdx
  402ca8:	49 63 c7             	movslq %r15d,%rax
  402cab:	59                   	pop    %rcx
  402cac:	48 3b 45 68          	cmp    0x68(%rbp),%rax
  402cb0:	0f 8c 7a ff ff ff    	jl     402c30 <main+0x960>
  402cb6:	49 89 ef             	mov    %rbp,%r15
  402cb9:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
  402cbe:	49 8b 57 70          	mov    0x70(%r15),%rdx
  402cc2:	48 8d 35 d8 36 00 00 	lea    0x36d8(%rip),%rsi        # 4063a1 <_IO_stdin_used+0x3a1>
  402cc9:	bf 01 00 00 00       	mov    $0x1,%edi
  402cce:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < thread_count ; x++) {
  402cd0:	49 81 c7 98 00 00 00 	add    $0x98,%r15
  402cd7:	e8 d4 f4 ff ff       	call   4021b0 <__printf_chk@plt>
  402cdc:	4c 39 7c 24 18       	cmp    %r15,0x18(%rsp)
  402ce1:	0f 85 01 fe ff ff    	jne    402ae8 <main+0x818>
  402ce7:	48 89 ea             	mov    %rbp,%rdx
  402cea:	48 8d 35 ce 36 00 00 	lea    0x36ce(%rip),%rsi        # 4063bf <_IO_stdin_used+0x3bf>
  402cf1:	bf 01 00 00 00       	mov    $0x1,%edi
  402cf6:	31 c0                	xor    %eax,%eax
  402cf8:	e8 b3 f4 ff ff       	call   4021b0 <__printf_chk@plt>
  402cfd:	bf 0a 00 00 00       	mov    $0xa,%edi
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total Protected %ld\n", protected_state->protected);
  printf("Total V %ld\n", v);
  printf("\n");
  printf("Total Protected per second %ld\n", protected_state->protected / DURATION);
  402d02:	48 bb 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%rbx
  402d0c:	e8 2f f3 ff ff       	call   402040 <putchar@plt>
  402d11:	4c 8b 7c 24 40       	mov    0x40(%rsp),%r15
  402d16:	48 8d 35 b6 36 00 00 	lea    0x36b6(%rip),%rsi        # 4063d3 <_IO_stdin_used+0x3d3>
  402d1d:	31 c0                	xor    %eax,%eax
  402d1f:	bf 01 00 00 00       	mov    $0x1,%edi
  402d24:	49 8b 17             	mov    (%r15),%rdx
  402d27:	e8 84 f4 ff ff       	call   4021b0 <__printf_chk@plt>
  402d2c:	4c 89 f2             	mov    %r14,%rdx
  402d2f:	bf 01 00 00 00       	mov    $0x1,%edi
  402d34:	31 c0                	xor    %eax,%eax
  402d36:	48 8d 35 ab 36 00 00 	lea    0x36ab(%rip),%rsi        # 4063e8 <_IO_stdin_used+0x3e8>
  402d3d:	e8 6e f4 ff ff       	call   4021b0 <__printf_chk@plt>
  402d42:	bf 0a 00 00 00       	mov    $0xa,%edi
  402d47:	e8 f4 f2 ff ff       	call   402040 <putchar@plt>
  402d4c:	49 8b 0f             	mov    (%r15),%rcx
  402d4f:	bf 01 00 00 00       	mov    $0x1,%edi
  402d54:	48 8d 35 cd 38 00 00 	lea    0x38cd(%rip),%rsi        # 406628 <_IO_stdin_used+0x628>
  402d5b:	48 89 c8             	mov    %rcx,%rax
  402d5e:	48 f7 eb             	imul   %rbx
  402d61:	31 c0                	xor    %eax,%eax
  402d63:	48 01 ca             	add    %rcx,%rdx
  402d66:	48 c1 f9 3f          	sar    $0x3f,%rcx
  402d6a:	48 c1 fa 04          	sar    $0x4,%rdx
  402d6e:	48 29 ca             	sub    %rcx,%rdx
  402d71:	e8 3a f4 ff ff       	call   4021b0 <__printf_chk@plt>
  402d76:	49 8b 57 08          	mov    0x8(%r15),%rdx
  402d7a:	bf 01 00 00 00       	mov    $0x1,%edi
  402d7f:	31 c0                	xor    %eax,%eax
  402d81:	48 8d 35 c0 38 00 00 	lea    0x38c0(%rip),%rsi        # 406648 <_IO_stdin_used+0x648>
  402d88:	e8 23 f4 ff ff       	call   4021b0 <__printf_chk@plt>
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
  402d8d:	4c 89 e0             	mov    %r12,%rax
  402d90:	bf 01 00 00 00       	mov    $0x1,%edi
  402d95:	48 8d 35 d4 38 00 00 	lea    0x38d4(%rip),%rsi        # 406670 <_IO_stdin_used+0x670>
  402d9c:	48 f7 eb             	imul   %rbx
  402d9f:	31 c0                	xor    %eax,%eax
  402da1:	4c 01 e2             	add    %r12,%rdx
  402da4:	49 c1 fc 3f          	sar    $0x3f,%r12
  402da8:	48 c1 fa 04          	sar    $0x4,%rdx
  402dac:	4c 29 e2             	sub    %r12,%rdx
  402daf:	e8 fc f3 ff ff       	call   4021b0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
  402db4:	4c 89 e8             	mov    %r13,%rax
  402db7:	bf 01 00 00 00       	mov    $0x1,%edi
  402dbc:	48 8d 35 dd 38 00 00 	lea    0x38dd(%rip),%rsi        # 4066a0 <_IO_stdin_used+0x6a0>
  402dc3:	48 f7 eb             	imul   %rbx
  402dc6:	4c 89 e8             	mov    %r13,%rax
  402dc9:	48 c1 f8 3f          	sar    $0x3f,%rax
  402dcd:	4c 01 ea             	add    %r13,%rdx
  402dd0:	48 c1 fa 04          	sar    $0x4,%rdx
  402dd4:	48 29 c2             	sub    %rax,%rdx
  402dd7:	31 c0                	xor    %eax,%eax
  402dd9:	e8 d2 f3 ff ff       	call   4021b0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
  402dde:	48 89 e8             	mov    %rbp,%rax
  402de1:	bf 01 00 00 00       	mov    $0x1,%edi
  402de6:	48 8d 35 e3 38 00 00 	lea    0x38e3(%rip),%rsi        # 4066d0 <_IO_stdin_used+0x6d0>
  402ded:	48 f7 eb             	imul   %rbx
  402df0:	48 01 ea             	add    %rbp,%rdx
  402df3:	48 c1 fd 3f          	sar    $0x3f,%rbp
  402df7:	31 c0                	xor    %eax,%eax
  402df9:	48 c1 fa 04          	sar    $0x4,%rdx
  402dfd:	48 29 ea             	sub    %rbp,%rdx
  402e00:	e8 ab f3 ff ff       	call   4021b0 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
  402e05:	48 8b 04 24          	mov    (%rsp),%rax
  402e09:	bf 01 00 00 00       	mov    $0x1,%edi
  402e0e:	48 8d 35 e0 35 00 00 	lea    0x35e0(%rip),%rsi        # 4063f5 <_IO_stdin_used+0x3f5>
  402e15:	48 f7 eb             	imul   %rbx
  402e18:	48 8b 04 24          	mov    (%rsp),%rax
  402e1c:	48 01 c2             	add    %rax,%rdx
  402e1f:	48 c1 f8 3f          	sar    $0x3f,%rax
  402e23:	48 c1 fa 04          	sar    $0x4,%rdx
  402e27:	48 29 c2             	sub    %rax,%rdx
  402e2a:	31 c0                	xor    %eax,%eax
  402e2c:	e8 7f f3 ff ff       	call   4021b0 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
  402e31:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  402e36:	bf 01 00 00 00       	mov    $0x1,%edi
  402e3b:	48 8d 35 c4 35 00 00 	lea    0x35c4(%rip),%rsi        # 406406 <_IO_stdin_used+0x406>
  402e42:	48 f7 eb             	imul   %rbx
  402e45:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  402e4a:	48 01 c2             	add    %rax,%rdx
  402e4d:	48 c1 f8 3f          	sar    $0x3f,%rax
  402e51:	48 c1 fa 04          	sar    $0x4,%rdx
  402e55:	48 29 c2             	sub    %rax,%rdx
  402e58:	31 c0                	xor    %eax,%eax
  402e5a:	e8 51 f3 ff ff       	call   4021b0 <__printf_chk@plt>
  verify(thread_data, thread_count);
  402e5f:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
  402e64:	be 06 00 00 00       	mov    $0x6,%esi
  402e69:	e8 c2 23 00 00       	call   405230 <verify>
  return 0;

}
  402e6e:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  402e73:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  402e7c:	75 4a                	jne    402ec8 <main+0xbf8>
  402e7e:	48 83 c4 68          	add    $0x68,%rsp
  402e82:	31 c0                	xor    %eax,%eax
  402e84:	5b                   	pop    %rbx
  402e85:	5d                   	pop    %rbp
  402e86:	41 5c                	pop    %r12
  402e88:	41 5d                	pop    %r13
  402e8a:	41 5e                	pop    %r14
  402e8c:	41 5f                	pop    %r15
  402e8e:	c3                   	ret
  402e8f:	90                   	nop
          thread_data[x].tasks[y].run = barriered_work; 
  402e90:	48 c7 c0 40 4d 40 00 	mov    $0x404d40,%rax
  402e97:	41 bd 06 00 00 00    	mov    $0x6,%r13d
  402e9d:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
  402ea4:	e9 a6 f8 ff ff       	jmp    40274f <main+0x47f>
  402ea9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            thread_data[x].tasks[y].protected = do_protected_write; 
  402eb0:	49 8b 47 20          	mov    0x20(%r15),%rax
  402eb4:	48 c7 c2 c0 2f 40 00 	mov    $0x402fc0,%rdx
  402ebb:	4a 89 94 20 20 01 00 00 	mov    %rdx,0x120(%rax,%r12,1)
  402ec3:	e9 6e f6 ff ff       	jmp    402536 <main+0x266>
}
  402ec8:	e8 c3 f1 ff ff       	call   402090 <__stack_chk_fail@plt>
  402ecd:	0f 1f 00             	nopl   (%rax)

0000000000402ed0 <_start>:
  402ed0:	f3 0f 1e fa          	endbr64
  402ed4:	31 ed                	xor    %ebp,%ebp
  402ed6:	49 89 d1             	mov    %rdx,%r9
  402ed9:	5e                   	pop    %rsi
  402eda:	48 89 e2             	mov    %rsp,%rdx
  402edd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  402ee1:	50                   	push   %rax
  402ee2:	54                   	push   %rsp
  402ee3:	45 31 c0             	xor    %r8d,%r8d
  402ee6:	31 c9                	xor    %ecx,%ecx
  402ee8:	48 c7 c7 d0 22 40 00 	mov    $0x4022d0,%rdi
  402eef:	ff 15 f3 60 00 00    	call   *0x60f3(%rip)        # 408fe8 <__libc_start_main@GLIBC_2.34>
  402ef5:	f4                   	hlt
  402ef6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000402f00 <_dl_relocate_static_pie>:
  402f00:	f3 0f 1e fa          	endbr64
  402f04:	c3                   	ret
  402f05:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  402f0f:	90                   	nop

0000000000402f10 <deregister_tm_clones>:
  402f10:	b8 20 90 40 00       	mov    $0x409020,%eax
  402f15:	48 3d 20 90 40 00    	cmp    $0x409020,%rax
  402f1b:	74 13                	je     402f30 <deregister_tm_clones+0x20>
  402f1d:	b8 00 00 00 00       	mov    $0x0,%eax
  402f22:	48 85 c0             	test   %rax,%rax
  402f25:	74 09                	je     402f30 <deregister_tm_clones+0x20>
  402f27:	bf 20 90 40 00       	mov    $0x409020,%edi
  402f2c:	ff e0                	jmp    *%rax
  402f2e:	66 90                	xchg   %ax,%ax
  402f30:	c3                   	ret
  402f31:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  402f3c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000402f40 <register_tm_clones>:
  402f40:	be 20 90 40 00       	mov    $0x409020,%esi
  402f45:	48 81 ee 20 90 40 00 	sub    $0x409020,%rsi
  402f4c:	48 89 f0             	mov    %rsi,%rax
  402f4f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  402f53:	48 c1 f8 03          	sar    $0x3,%rax
  402f57:	48 01 c6             	add    %rax,%rsi
  402f5a:	48 d1 fe             	sar    %rsi
  402f5d:	74 11                	je     402f70 <register_tm_clones+0x30>
  402f5f:	b8 00 00 00 00       	mov    $0x0,%eax
  402f64:	48 85 c0             	test   %rax,%rax
  402f67:	74 07                	je     402f70 <register_tm_clones+0x30>
  402f69:	bf 20 90 40 00       	mov    $0x409020,%edi
  402f6e:	ff e0                	jmp    *%rax
  402f70:	c3                   	ret
  402f71:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  402f7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000402f80 <__do_global_dtors_aux>:
  402f80:	f3 0f 1e fa          	endbr64
  402f84:	80 3d 95 60 00 00 00 	cmpb   $0x0,0x6095(%rip)        # 409020 <__TMC_END__>
  402f8b:	75 13                	jne    402fa0 <__do_global_dtors_aux+0x20>
  402f8d:	55                   	push   %rbp
  402f8e:	48 89 e5             	mov    %rsp,%rbp
  402f91:	e8 7a ff ff ff       	call   402f10 <deregister_tm_clones>
  402f96:	c6 05 83 60 00 00 01 	movb   $0x1,0x6083(%rip)        # 409020 <__TMC_END__>
  402f9d:	5d                   	pop    %rbp
  402f9e:	c3                   	ret
  402f9f:	90                   	nop
  402fa0:	c3                   	ret
  402fa1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  402fac:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000402fb0 <frame_dummy>:
  402fb0:	f3 0f 1e fa          	endbr64
  402fb4:	eb 8a                	jmp    402f40 <register_tm_clones>
  402fb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000402fc0 <do_protected_write>:
  struct ProtectedState *protected = data->thread->protected_state;
  402fc0:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  402fc7:	48 8b 40 30          	mov    0x30(%rax),%rax
  data->v++; // thread local
  402fcb:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
  402fd3:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
  402fd7:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
  402fdb:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
  402fe2:	48 85 c9             	test   %rcx,%rcx
  402fe5:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
  402fec:	48 0f 4f d6          	cmovg  %rsi,%rdx
  402ff0:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
  402ff4:	31 c0                	xor    %eax,%eax
  402ff6:	c3                   	ret
  402ff7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000403000 <barriered_reset>:
    for (int x = 0 ; x < data->task_count ; x++) {
  403000:	48 63 87 84 01 00 00 	movslq 0x184(%rdi),%rax
  403007:	85 c0                	test   %eax,%eax
  403009:	7e 5b                	jle    403066 <barriered_reset+0x66>
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
  40300b:	48 63 97 30 01 00 00 	movslq 0x130(%rdi),%rdx
  403012:	48 8b 8f 28 01 00 00 	mov    0x128(%rdi),%rcx
  403019:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
  40301d:	48 8d 14 72          	lea    (%rdx,%rsi,2),%rdx
  403021:	48 8b 71 10          	mov    0x10(%rcx),%rsi
  403025:	48 8d 14 d6          	lea    (%rsi,%rdx,8),%rdx
      data->thread->tasks[x].available = 1; 
  403029:	48 8b 71 20          	mov    0x20(%rcx),%rsi
  40302d:	48 8d 0c 80          	lea    (%rax,%rax,4),%rcx
  403031:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
  403033:	48 8b 52 20          	mov    0x20(%rdx),%rdx
  403037:	48 c1 e1 07          	shl    $0x7,%rcx
  40303b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  403040:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index].tasks[x].prearrive++; 
  403048:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
  403050:	c7 84 06 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
  40305b:	48 05 80 02 00 00    	add    $0x280,%rax
  403061:	48 39 c1             	cmp    %rax,%rcx
  403064:	75 da                	jne    403040 <barriered_reset+0x40>
  asm volatile ("mfence" ::: "memory");
  403066:	0f ae f0             	mfence
}
  403069:	31 c0                	xor    %eax,%eax
  40306b:	c3                   	ret
  40306c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000403070 <barriered_thread>:
  while (data->running == 1) {
  403070:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
  403074:	0f 85 c8 02 00 00    	jne    403342 <barriered_thread+0x2d2>
void* barriered_thread(void *arg) {
  40307a:	41 57                	push   %r15
  40307c:	45 31 ff             	xor    %r15d,%r15d
  40307f:	41 56                	push   %r14
  403081:	41 55                	push   %r13
  403083:	45 31 ed             	xor    %r13d,%r13d
  403086:	41 54                	push   %r12
  403088:	49 89 fc             	mov    %rdi,%r12
  40308b:	55                   	push   %rbp
  40308c:	31 ed                	xor    %ebp,%ebp
  40308e:	53                   	push   %rbx
  40308f:	48 83 ec 08          	sub    $0x8,%rsp
  403093:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (t >= data->task_count) {
  403098:	41 8b 54 24 28       	mov    0x28(%r12),%edx
  40309d:	39 ea                	cmp    %ebp,%edx
  40309f:	7f 22                	jg     4030c3 <barriered_thread+0x53>
      data->cycles++;
  4030a1:	49 83 84 24 90 00 00 00 01 	addq   $0x1,0x90(%r12)
      t = 0;
  4030aa:	31 ed                	xor    %ebp,%ebp
    for (; t < data->task_count; t++) {
  4030ac:	85 d2                	test   %edx,%edx
  4030ae:	7f 13                	jg     4030c3 <barriered_thread+0x53>
  4030b0:	e9 6b 01 00 00       	jmp    403220 <barriered_thread+0x1b0>
  4030b5:	0f 1f 00             	nopl   (%rax)
  4030b8:	83 c5 01             	add    $0x1,%ebp
  4030bb:	39 d5                	cmp    %edx,%ebp
  4030bd:	0f 8d 5d 01 00 00    	jge    403220 <barriered_thread+0x1b0>
      if (data->tasks[t].available == 1) {
  4030c3:	48 63 c5             	movslq %ebp,%rax
  4030c6:	48 8d 1c 80          	lea    (%rax,%rax,4),%rbx
  4030ca:	49 8b 44 24 20       	mov    0x20(%r12),%rax
  4030cf:	48 c1 e3 07          	shl    $0x7,%rbx
  4030d3:	48 8d 0c 18          	lea    (%rax,%rbx,1),%rcx
  4030d7:	83 b9 80 01 00 00 01 	cmpl   $0x1,0x180(%rcx)
  4030de:	75 d8                	jne    4030b8 <barriered_thread+0x48>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
  4030e0:	45 8b 4c 24 18       	mov    0x18(%r12),%r9d
  4030e5:	83 ea 01             	sub    $0x1,%edx
  4030e8:	8d 75 ff             	lea    -0x1(%rbp),%esi
  4030eb:	85 ed                	test   %ebp,%ebp
  4030ed:	0f 4f d6             	cmovg  %esi,%edx
  4030f0:	45 85 c9             	test   %r9d,%r9d
  4030f3:	0f 8e 37 02 00 00    	jle    403330 <barriered_thread+0x2c0>
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
  4030f9:	48 63 d2             	movslq %edx,%rdx
  4030fc:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
        int arrived = 0; 
  403101:	45 31 f6             	xor    %r14d,%r14d
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
  403104:	44 8b 91 80 00 00 00 	mov    0x80(%rcx),%r10d
  40310b:	48 8d 34 92          	lea    (%rdx,%rdx,4),%rsi
  40310f:	41 8d 51 ff          	lea    -0x1(%r9),%edx
          if (data->threads[thread].tasks[previous].prearrive == data->tasks[t].prearrive) {
  403113:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
  40311a:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
  40311e:	48 8d 47 20          	lea    0x20(%rdi),%rax
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
  403122:	48 c1 e6 07          	shl    $0x7,%rsi
  403126:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
        int prearrive = 0; 
  40312a:	31 c9                	xor    %ecx,%ecx
  40312c:	48 8d bc d7 b8 00 00 00 	lea    0xb8(%rdi,%rdx,8),%rdi
  403134:	0f 1f 40 00          	nopl   0x0(%rax)
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
  403138:	48 8b 10             	mov    (%rax),%rdx
            arrived++;
  40313b:	45 31 db             	xor    %r11d,%r11d
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
  40313e:	48 01 f2             	add    %rsi,%rdx
            arrived++;
  403141:	44 3b 92 80 00 00 00 	cmp    0x80(%rdx),%r10d
  403148:	41 0f 94 c3          	sete   %r11b
  40314c:	45 01 de             	add    %r11d,%r14d
            prearrive++;
  40314f:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
  403156:	0f 94 c2             	sete   %dl
        for (int thread = 0 ; thread < data->thread_count; thread++) {
  403159:	48 05 98 00 00 00    	add    $0x98,%rax
            prearrive++;
  40315f:	0f b6 d2             	movzbl %dl,%edx
  403162:	01 d1                	add    %edx,%ecx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
  403164:	48 39 c7             	cmp    %rax,%rdi
  403167:	75 cf                	jne    403138 <barriered_thread+0xc8>
        if (prearrive == 0 || prearrive == data->thread_count) {
  403169:	41 39 c9             	cmp    %ecx,%r9d
  40316c:	0f 84 ce 00 00 00    	je     403240 <barriered_thread+0x1d0>
  403172:	85 c9                	test   %ecx,%ecx
  403174:	0f 84 c6 00 00 00    	je     403240 <barriered_thread+0x1d0>
        if (arrived == 0 || arrived == data->thread_count) {
  40317a:	45 85 f6             	test   %r14d,%r14d
  40317d:	74 0b                	je     40318a <barriered_thread+0x11a>
  40317f:	45 39 74 24 18       	cmp    %r14d,0x18(%r12)
  403184:	0f 85 96 00 00 00    	jne    403220 <barriered_thread+0x1b0>
  40318a:	49 8b 44 24 20       	mov    0x20(%r12),%rax
          data->tasks[t].prearrive++;
  40318f:	48 01 d8             	add    %rbx,%rax
  403192:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
  403199:	85 ed                	test   %ebp,%ebp
  40319b:	75 10                	jne    4031ad <barriered_thread+0x13d>
  40319d:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
  4031a2:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
  4031a7:	0f 8c 5b 01 00 00    	jl     403308 <barriered_thread+0x298>
          data->tasks[t].available = 0;
  4031ad:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
          data->tasks[t].run(&data->threads[data->thread_index].tasks[t]);
  4031b7:	49 63 14 24          	movslq (%r12),%rdx
  4031bb:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
  4031bf:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
  4031c3:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
  4031c8:	48 8d 14 d1          	lea    (%rcx,%rdx,8),%rdx
  4031cc:	48 8b 7a 20          	mov    0x20(%rdx),%rdi
  4031d0:	48 01 df             	add    %rbx,%rdi
  4031d3:	ff 90 18 01 00 00    	call   *0x118(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  4031d9:	41 8b 44 24 28       	mov    0x28(%r12),%eax
          data->tasks[t].arrived++;
  4031de:	49 03 5c 24 20       	add    0x20(%r12),%rbx
  4031e3:	83 83 80 00 00 00 01 	addl   $0x1,0x80(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  4031ea:	83 e8 01             	sub    $0x1,%eax
          data->iteration_count++;
  4031ed:	49 83 44 24 60 01    	addq   $0x1,0x60(%r12)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  4031f3:	39 e8                	cmp    %ebp,%eax
  4031f5:	0f 84 9d 00 00 00    	je     403298 <barriered_thread+0x228>
          asm volatile ("mfence" ::: "memory");
  4031fb:	0f ae f0             	mfence
          if (waiting == 0) {
  4031fe:	45 85 ff             	test   %r15d,%r15d
  403201:	0f 84 c9 00 00 00    	je     4032d0 <barriered_thread+0x260>
            waiting = 0;
  403207:	41 83 ff 03          	cmp    $0x3,%r15d
    for (; t < data->task_count; t++) {
  40320b:	41 8b 54 24 28       	mov    0x28(%r12),%edx
            waiting = 0;
  403210:	45 0f 44 fd          	cmove  %r13d,%r15d
    for (; t < data->task_count; t++) {
  403214:	83 c5 01             	add    $0x1,%ebp
  403217:	39 d5                	cmp    %edx,%ebp
  403219:	0f 8c a4 fe ff ff    	jl     4030c3 <barriered_thread+0x53>
  40321f:	90                   	nop
  while (data->running == 1) {
  403220:	41 83 7c 24 2c 01    	cmpl   $0x1,0x2c(%r12)
  403226:	0f 84 6c fe ff ff    	je     403098 <barriered_thread+0x28>
}
  40322c:	48 83 c4 08          	add    $0x8,%rsp
  403230:	31 c0                	xor    %eax,%eax
  403232:	5b                   	pop    %rbx
  403233:	5d                   	pop    %rbp
  403234:	41 5c                	pop    %r12
  403236:	41 5d                	pop    %r13
  403238:	41 5e                	pop    %r14
  40323a:	41 5f                	pop    %r15
  40323c:	c3                   	ret
  40323d:	0f 1f 00             	nopl   (%rax)
          if (waiting == 1) {
  403240:	41 83 ff 01          	cmp    $0x1,%r15d
  403244:	0f 85 30 ff ff ff    	jne    40317a <barriered_thread+0x10a>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
  40324a:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
  403252:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 3;
  403257:	41 bf 03 00 00 00    	mov    $0x3,%r15d
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
  40325d:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  403261:	49 8b 44 24 78       	mov    0x78(%r12),%rax
  403266:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
  40326b:	e8 00 ee ff ff       	call   402070 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
  403270:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
  403278:	48 83 c0 01          	add    $0x1,%rax
  40327c:	48 99                	cqto
  40327e:	49 f7 bc 24 88 00 00 00 	idivq  0x88(%r12)
  403286:	49 89 94 24 80 00 00 00 	mov    %rdx,0x80(%r12)
            waiting = 3;
  40328e:	e9 e7 fe ff ff       	jmp    40317a <barriered_thread+0x10a>
  403293:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  403298:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
  40329d:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
  4032a2:	0f 8d 53 ff ff ff    	jge    4031fb <barriered_thread+0x18b>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
  4032a8:	48 c1 e6 04          	shl    $0x4,%rsi
  4032ac:	bf 04 00 00 00       	mov    $0x4,%edi
  4032b1:	49 03 74 24 58       	add    0x58(%r12),%rsi
  4032b6:	e8 b5 ed ff ff       	call   402070 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
  4032bb:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
  4032c1:	e9 35 ff ff ff       	jmp    4031fb <barriered_thread+0x18b>
  4032c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
  4032d0:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
  4032d8:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
  4032dd:	41 bf 01 00 00 00    	mov    $0x1,%r15d
            data->task_snapshot[data->task_timestamp_count].task = t;
  4032e3:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  4032e7:	49 8b 44 24 78       	mov    0x78(%r12),%rax
  4032ec:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
  4032f0:	89 6e 20             	mov    %ebp,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
  4032f3:	e8 78 ed ff ff       	call   402070 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
  4032f8:	41 8b 54 24 28       	mov    0x28(%r12),%edx
  4032fd:	e9 b6 fd ff ff       	jmp    4030b8 <barriered_thread+0x48>
  403302:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
  403308:	48 c1 e6 04          	shl    $0x4,%rsi
  40330c:	bf 04 00 00 00       	mov    $0x4,%edi
  403311:	49 03 74 24 50       	add    0x50(%r12),%rsi
  403316:	e8 55 ed ff ff       	call   402070 <clock_gettime@plt>
          data->tasks[t].available = 0;
  40331b:	49 8b 44 24 20       	mov    0x20(%r12),%rax
  403320:	48 01 d8             	add    %rbx,%rax
  403323:	e9 85 fe ff ff       	jmp    4031ad <barriered_thread+0x13d>
  403328:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (waiting == 1) {
  403330:	41 83 ff 01          	cmp    $0x1,%r15d
  403334:	0f 85 55 fe ff ff    	jne    40318f <barriered_thread+0x11f>
        int arrived = 0; 
  40333a:	45 31 f6             	xor    %r14d,%r14d
  40333d:	e9 08 ff ff ff       	jmp    40324a <barriered_thread+0x1da>
}
  403342:	31 c0                	xor    %eax,%eax
  403344:	c3                   	ret
  403345:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000403350 <external_thread>:
void * external_thread(void *arg) {
  403350:	41 55                	push   %r13
  403352:	41 54                	push   %r12
  403354:	55                   	push   %rbp
  403355:	53                   	push   %rbx
  403356:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
  40335a:	66 0f 6f 05 8e 35 00 00 	movdqa 0x358e(%rip),%xmm0        # 4068f0 <_IO_stdin_used+0x8f0>
void * external_thread(void *arg) {
  403362:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40336b:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  403370:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
  403372:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
  struct timespec req = {
  403376:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
  40337a:	75 67                	jne    4033e3 <external_thread+0x93>
  40337c:	49 89 fd             	mov    %rdi,%r13
  40337f:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
  403384:	48 89 e5             	mov    %rsp,%rbp
        data->buffers->buffer[x].data = "Hello world";
  403387:	48 8d 1d 76 2c 00 00 	lea    0x2c76(%rip),%rbx        # 406004 <_IO_stdin_used+0x4>
  40338e:	66 90                	xchg   %ax,%ax
    nanosleep(&req , &rem);
  403390:	4c 89 e6             	mov    %r12,%rsi
  403393:	48 89 ef             	mov    %rbp,%rdi
  403396:	e8 15 ed ff ff       	call   4020b0 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
  40339b:	49 8b 45 38          	mov    0x38(%r13),%rax
  40339f:	8b 10                	mov    (%rax),%edx
  4033a1:	85 d2                	test   %edx,%edx
  4033a3:	7e 34                	jle    4033d9 <external_thread+0x89>
      if (data->buffers->buffer[x].available == 0) {
  4033a5:	48 8b 48 08          	mov    0x8(%rax),%rcx
  4033a9:	83 ea 01             	sub    $0x1,%edx
  4033ac:	48 c1 e2 04          	shl    $0x4,%rdx
  4033b0:	48 8d 41 08          	lea    0x8(%rcx),%rax
  4033b4:	48 8d 54 11 18       	lea    0x18(%rcx,%rdx,1),%rdx
  4033b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  4033c0:	8b 08                	mov    (%rax),%ecx
  4033c2:	85 c9                	test   %ecx,%ecx
  4033c4:	75 0a                	jne    4033d0 <external_thread+0x80>
        data->buffers->buffer[x].data = "Hello world";
  4033c6:	48 89 58 f8          	mov    %rbx,-0x8(%rax)
        data->buffers->buffer[x].available = 1;
  4033ca:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
  4033d0:	48 83 c0 10          	add    $0x10,%rax
  4033d4:	48 39 d0             	cmp    %rdx,%rax
  4033d7:	75 e7                	jne    4033c0 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
  4033d9:	0f ae f0             	mfence
  while (data->running == 1) {
  4033dc:	41 83 7d 2c 01       	cmpl   $0x1,0x2c(%r13)
  4033e1:	74 ad                	je     403390 <external_thread+0x40>
}
  4033e3:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
  4033e8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4033f1:	75 0d                	jne    403400 <external_thread+0xb0>
  4033f3:	48 83 c4 38          	add    $0x38,%rsp
  4033f7:	31 c0                	xor    %eax,%eax
  4033f9:	5b                   	pop    %rbx
  4033fa:	5d                   	pop    %rbp
  4033fb:	41 5c                	pop    %r12
  4033fd:	41 5d                	pop    %r13
  4033ff:	c3                   	ret
  403400:	e8 8b ec ff ff       	call   402090 <__stack_chk_fail@plt>
  403405:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000403410 <timer_thread>:
void* timer_thread(void *arg) {
  403410:	41 57                	push   %r15
  403412:	48 8d 35 f7 2b 00 00 	lea    0x2bf7(%rip),%rsi        # 406010 <_IO_stdin_used+0x10>
  403419:	49 89 ff             	mov    %rdi,%r15
  40341c:	41 56                	push   %r14
  40341e:	41 55                	push   %r13
  403420:	41 54                	push   %r12
  403422:	55                   	push   %rbp
  403423:	53                   	push   %rbx
  403424:	48 83 ec 68          	sub    $0x68,%rsp
  403428:	8b 17                	mov    (%rdi),%edx
  40342a:	bf 01 00 00 00       	mov    $0x1,%edi
  40342f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  403438:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  40343d:	31 c0                	xor    %eax,%eax
  40343f:	e8 6c ed ff ff       	call   4021b0 <__printf_chk@plt>
  struct timespec preempt = {
  403444:	66 0f 6f 05 a4 34 00 00 	movdqa 0x34a4(%rip),%xmm0        # 4068f0 <_IO_stdin_used+0x8f0>
  40344c:	ba 30 75 00 00       	mov    $0x7530,%edx
  403451:	31 c0                	xor    %eax,%eax
  403453:	48 8d 35 c8 2b 00 00 	lea    0x2bc8(%rip),%rsi        # 406022 <_IO_stdin_used+0x22>
  40345a:	bf 01 00 00 00       	mov    $0x1,%edi
  40345f:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
  403464:	e8 47 ed ff ff       	call   4021b0 <__printf_chk@plt>
  while (data->running && n < times) {
  403469:	45 8b 67 2c          	mov    0x2c(%r15),%r12d
  40346d:	45 85 e4             	test   %r12d,%r12d
  403470:	0f 84 c1 00 00 00    	je     403537 <timer_thread+0x127>
  int n = 0;
  403476:	31 ed                	xor    %ebp,%ebp
  int y = 0;
  403478:	45 31 e4             	xor    %r12d,%r12d
  40347b:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
        data->threads[x].tasks[y].scheduled = 0;
  403480:	31 db                	xor    %ebx,%ebx
  403482:	4c 8d 74 24 20       	lea    0x20(%rsp),%r14
    nanosleep(&preempt , &rem2);
  403487:	4c 89 f7             	mov    %r14,%rdi
  40348a:	4c 89 ee             	mov    %r13,%rsi
    n++;
  40348d:	83 c5 01             	add    $0x1,%ebp
    nanosleep(&preempt , &rem2);
  403490:	e8 1b ec ff ff       	call   4020b0 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
  403495:	45 8b 47 18          	mov    0x18(%r15),%r8d
    y++;
  403499:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
  40349e:	45 85 c0             	test   %r8d,%r8d
  4034a1:	7e 70                	jle    403513 <timer_thread+0x103>
        data->threads[x].tasks[y].scheduled = 0;
  4034a3:	49 63 d4             	movslq %r12d,%rdx
    for (int x = 0 ; x < data->thread_count ; x++) {
  4034a6:	31 f6                	xor    %esi,%esi
        data->threads[x].tasks[next].scheduled = 1;
  4034a8:	41 ba 01 00 00 00    	mov    $0x1,%r10d
        data->threads[x].tasks[y].scheduled = 0;
  4034ae:	4c 8d 04 92          	lea    (%rdx,%rdx,4),%r8
  4034b2:	49 c1 e0 07          	shl    $0x7,%r8
  4034b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x].task_count;
  4034c0:	48 63 c6             	movslq %esi,%rax
  4034c3:	4d 8b 5f 10          	mov    0x10(%r15),%r11
  4034c7:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
  4034cb:	48 8d 0c 50          	lea    (%rax,%rdx,2),%rcx
  4034cf:	89 f8                	mov    %edi,%eax
  4034d1:	48 c1 e1 03          	shl    $0x3,%rcx
  4034d5:	99                   	cltd
  4034d6:	49 01 cb             	add    %rcx,%r11
  4034d9:	41 f7 7b 28          	idivl  0x28(%r11)
        data->threads[x].tasks[next].scheduled = 1;
  4034dd:	48 63 d2             	movslq %edx,%rdx
  4034e0:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
  4034e4:	44 89 d2             	mov    %r10d,%edx
  4034e7:	48 c1 e0 07          	shl    $0x7,%rax
  4034eb:	49 03 43 20          	add    0x20(%r11),%rax
  4034ef:	48 05 00 02 00 00    	add    $0x200,%rax
  4034f5:	87 10                	xchg   %edx,(%rax)
        data->threads[x].tasks[y].scheduled = 0;
  4034f7:	49 8b 47 10          	mov    0x10(%r15),%rax
  4034fb:	48 8b 44 08 20       	mov    0x20(%rax,%rcx,1),%rax
  403500:	89 da                	mov    %ebx,%edx
  403502:	42 87 94 00 00 02 00 00 	xchg   %edx,0x200(%rax,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
  40350a:	83 c6 01             	add    $0x1,%esi
  40350d:	41 39 77 18          	cmp    %esi,0x18(%r15)
  403511:	7f ad                	jg     4034c0 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
  403513:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
  403516:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
  40351a:	41 8b 77 2c          	mov    0x2c(%r15),%esi
      y = 0;
  40351e:	39 78 28             	cmp    %edi,0x28(%rax)
  403521:	0f 4e fb             	cmovle %ebx,%edi
  403524:	41 89 fc             	mov    %edi,%r12d
  while (data->running && n < times) {
  403527:	85 f6                	test   %esi,%esi
  403529:	74 0c                	je     403537 <timer_thread+0x127>
  40352b:	81 fd 30 75 00 00    	cmp    $0x7530,%ebp
  403531:	0f 85 50 ff ff ff    	jne    403487 <timer_thread+0x77>
  403537:	48 8d 3d fa 2a 00 00 	lea    0x2afa(%rip),%rdi        # 406038 <_IO_stdin_used+0x38>
  40353e:	e8 0d eb ff ff       	call   402050 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
  403543:	49 63 47 1c          	movslq 0x1c(%r15),%rax
  403547:	85 c0                	test   %eax,%eax
  403549:	7e 62                	jle    4035ad <timer_thread+0x19d>
    for (int y = 0 ; y < data->task_count ; y++) {
  40354b:	41 8b 4f 28          	mov    0x28(%r15),%ecx
  40354f:	85 c9                	test   %ecx,%ecx
  403551:	7e 5a                	jle    4035ad <timer_thread+0x19d>
  403553:	48 8d 34 c0          	lea    (%rax,%rax,8),%rsi
      data->threads[x].tasks[y].sending = 0;
  403557:	4d 8b 57 10          	mov    0x10(%r15),%r10
  40355b:	48 8d 3c 70          	lea    (%rax,%rsi,2),%rdi
  40355f:	8d 41 ff             	lea    -0x1(%rcx),%eax
  403562:	31 f6                	xor    %esi,%esi
  403564:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  403568:	48 c1 e7 03          	shl    $0x3,%rdi
  40356c:	48 c1 e0 07          	shl    $0x7,%rax
  403570:	4c 8d 80 b8 04 00 00 	lea    0x4b8(%rax),%r8
  403577:	49 8b 4c 32 20       	mov    0x20(%r10,%rsi,1),%rcx
  40357c:	48 8d 81 38 02 00 00 	lea    0x238(%rcx),%rax
  403583:	4c 01 c1             	add    %r8,%rcx
  403586:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  403590:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
  403596:	48 05 80 02 00 00    	add    $0x280,%rax
  40359c:	48 39 c8             	cmp    %rcx,%rax
  40359f:	75 ef                	jne    403590 <timer_thread+0x180>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
  4035a1:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
  4035a8:	48 39 fe             	cmp    %rdi,%rsi
  4035ab:	75 ca                	jne    403577 <timer_thread+0x167>
  asm volatile ("mfence" ::: "memory");
  4035ad:	0f ae f0             	mfence
  struct timespec drain = {
  4035b0:	66 0f 6f 05 48 33 00 00 	movdqa 0x3348(%rip),%xmm0        # 406900 <_IO_stdin_used+0x900>
        data->threads[x].tasks[y].scheduled = 0;
  4035b8:	45 31 f6             	xor    %r14d,%r14d
  4035bb:	48 8d 2d 9b 2a 00 00 	lea    0x2a9b(%rip),%rbp        # 40605d <_IO_stdin_used+0x5d>
  struct timespec drain = {
  4035c2:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
  4035c7:	41 8b 57 18          	mov    0x18(%r15),%edx
    y++;
  4035cb:	41 8d 44 24 01       	lea    0x1(%r12),%eax
  4035d0:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
  4035d4:	85 d2                	test   %edx,%edx
  4035d6:	7e 67                	jle    40363f <timer_thread+0x22f>
        data->threads[x].tasks[y].scheduled = 0;
  4035d8:	49 63 d4             	movslq %r12d,%rdx
    for (int x = 0 ; x < data->thread_count ; x++) {
  4035db:	31 f6                	xor    %esi,%esi
        data->threads[x].tasks[y].scheduled = 0;
  4035dd:	48 8d 3c 92          	lea    (%rdx,%rdx,4),%rdi
  4035e1:	48 c1 e7 07          	shl    $0x7,%rdi
  4035e5:	0f 1f 00             	nopl   (%rax)
        int next = (y + 1) % data->threads[x].task_count;
  4035e8:	48 63 c6             	movslq %esi,%rax
  4035eb:	4d 8b 47 10          	mov    0x10(%r15),%r8
        data->threads[x].tasks[next].scheduled = 1;
  4035ef:	bb 01 00 00 00       	mov    $0x1,%ebx
        int next = (y + 1) % data->threads[x].task_count;
  4035f4:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
  4035f8:	48 8d 0c 50          	lea    (%rax,%rdx,2),%rcx
  4035fc:	8b 44 24 0c          	mov    0xc(%rsp),%eax
  403600:	48 c1 e1 03          	shl    $0x3,%rcx
  403604:	49 01 c8             	add    %rcx,%r8
  403607:	99                   	cltd
  403608:	41 f7 78 28          	idivl  0x28(%r8)
        data->threads[x].tasks[next].scheduled = 1;
  40360c:	48 63 c2             	movslq %edx,%rax
  40360f:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  403613:	48 c1 e0 07          	shl    $0x7,%rax
  403617:	49 03 40 20          	add    0x20(%r8),%rax
  40361b:	48 05 00 02 00 00    	add    $0x200,%rax
  403621:	87 18                	xchg   %ebx,(%rax)
        data->threads[x].tasks[y].scheduled = 0;
  403623:	49 8b 47 10          	mov    0x10(%r15),%rax
  403627:	48 8b 44 08 20       	mov    0x20(%rax,%rcx,1),%rax
  40362c:	44 89 f3             	mov    %r14d,%ebx
  40362f:	87 9c 38 00 02 00 00 	xchg   %ebx,0x200(%rax,%rdi,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
  403636:	83 c6 01             	add    $0x1,%esi
  403639:	41 39 77 18          	cmp    %esi,0x18(%r15)
  40363d:	7f a9                	jg     4035e8 <timer_thread+0x1d8>
    asm volatile ("mfence" ::: "memory");
  40363f:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
  403642:	49 8b 57 10          	mov    0x10(%r15),%rdx
      y = 0;
  403646:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
  40364a:	41 8b 7f 18          	mov    0x18(%r15),%edi
      y = 0;
  40364e:	39 42 28             	cmp    %eax,0x28(%rdx)
  403651:	41 0f 4e c6          	cmovle %r14d,%eax
  403655:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
  403659:	85 ff                	test   %edi,%edi
  40365b:	0f 8e d7 00 00 00    	jle    403738 <timer_thread+0x328>
  403661:	45 31 e4             	xor    %r12d,%r12d
    int all_empty = 1;
  403664:	41 bb 01 00 00 00    	mov    $0x1,%r11d
  40366a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
  403670:	49 63 c4             	movslq %r12d,%rax
      for (int y = 0 ; y < data->thread_count ; y++) {
  403673:	45 31 ed             	xor    %r13d,%r13d
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
  403676:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
  40367a:	48 8d 1c 48          	lea    (%rax,%rcx,2),%rbx
  40367e:	48 c1 e3 03          	shl    $0x3,%rbx
  403682:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  403688:	49 63 c5             	movslq %r13d,%rax
  40368b:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  40368f:	48 c1 e0 07          	shl    $0x7,%rax
  403693:	48 03 44 1a 20       	add    0x20(%rdx,%rbx,1),%rax
        for (int k = 0 ; k < data->thread_count; k++) {
  403698:	31 d2                	xor    %edx,%edx
  40369a:	48 8b 80 28 02 00 00 	mov    0x228(%rax),%rax
  4036a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
  4036a8:	48 8b 08             	mov    (%rax),%rcx
  4036ab:	48 8b 70 08          	mov    0x8(%rax),%rsi
  4036af:	48 8b 89 80 00 00 00 	mov    0x80(%rcx),%rcx
  4036b6:	4c 8b 86 80 00 00 00 	mov    0x80(%rsi),%r8
  4036bd:	48 85 c9             	test   %rcx,%rcx
  4036c0:	7f 26                	jg     4036e8 <timer_thread+0x2d8>
  4036c2:	4d 85 c0             	test   %r8,%r8
  4036c5:	7f 21                	jg     4036e8 <timer_thread+0x2d8>
        for (int k = 0 ; k < data->thread_count; k++) {
  4036c7:	83 c2 01             	add    $0x1,%edx
  4036ca:	48 83 c0 20          	add    $0x20,%rax
  4036ce:	39 fa                	cmp    %edi,%edx
  4036d0:	7c d6                	jl     4036a8 <timer_thread+0x298>
      for (int y = 0 ; y < data->thread_count ; y++) {
  4036d2:	41 83 c5 01          	add    $0x1,%r13d
  4036d6:	44 39 ef             	cmp    %r13d,%edi
  4036d9:	7e 2c                	jle    403707 <timer_thread+0x2f7>
  4036db:	49 8b 57 10          	mov    0x10(%r15),%rdx
  4036df:	eb a7                	jmp    403688 <timer_thread+0x278>
  4036e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  4036e8:	bf 01 00 00 00       	mov    $0x1,%edi
  4036ed:	48 89 ee             	mov    %rbp,%rsi
  4036f0:	31 c0                	xor    %eax,%eax
  4036f2:	41 83 c5 01          	add    $0x1,%r13d
  4036f6:	e8 b5 ea ff ff       	call   4021b0 <__printf_chk@plt>
  4036fb:	41 8b 7f 18          	mov    0x18(%r15),%edi
            all_empty = 0;
  4036ff:	45 31 db             	xor    %r11d,%r11d
      for (int y = 0 ; y < data->thread_count ; y++) {
  403702:	44 39 ef             	cmp    %r13d,%edi
  403705:	7f d4                	jg     4036db <timer_thread+0x2cb>
    for (int x = 0 ; x < data->thread_count ; x++) {
  403707:	41 83 c4 01          	add    $0x1,%r12d
  40370b:	44 39 e7             	cmp    %r12d,%edi
  40370e:	7e 09                	jle    403719 <timer_thread+0x309>
  403710:	49 8b 57 10          	mov    0x10(%r15),%rdx
  403714:	e9 57 ff ff ff       	jmp    403670 <timer_thread+0x260>
    if (all_empty == 1) {
  403719:	41 83 fb 01          	cmp    $0x1,%r11d
  40371d:	74 19                	je     403738 <timer_thread+0x328>
      nanosleep(&drain , &drainrem);
  40371f:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
  403724:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  403729:	e8 82 e9 ff ff       	call   4020b0 <nanosleep@plt>
  40372e:	44 8b 64 24 0c       	mov    0xc(%rsp),%r12d
  403733:	e9 8f fe ff ff       	jmp    4035c7 <timer_thread+0x1b7>
  403738:	48 8d 3d 15 29 00 00 	lea    0x2915(%rip),%rdi        # 406054 <_IO_stdin_used+0x54>
  40373f:	e8 0c e9 ff ff       	call   402050 <puts@plt>
  while (data->running) {
  403744:	41 8b 4f 2c          	mov    0x2c(%r15),%ecx
  403748:	85 c9                	test   %ecx,%ecx
  40374a:	0f 84 ba 00 00 00    	je     40380a <timer_thread+0x3fa>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  403750:	41 8b 77 1c          	mov    0x1c(%r15),%esi
  403754:	85 f6                	test   %esi,%esi
  403756:	7e 3b                	jle    403793 <timer_thread+0x383>
  403758:	49 8b 57 10          	mov    0x10(%r15),%rdx
  40375c:	31 ed                	xor    %ebp,%ebp
  40375e:	4c 8d 25 09 29 00 00 	lea    0x2909(%rip),%r12        # 40606e <_IO_stdin_used+0x6e>
  403765:	0f 1f 00             	nopl   (%rax)
      data->threads[x].running = 0;
  403768:	48 63 c5             	movslq %ebp,%rax
  40376b:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
  40376f:	48 8d 1c 48          	lea    (%rax,%rcx,2),%rbx
  403773:	48 c1 e3 03          	shl    $0x3,%rbx
  403777:	48 8d 04 1a          	lea    (%rdx,%rbx,1),%rax
      if (data->threads[x].type == IO) {
  40377b:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
      data->threads[x].running = 0;
  40377f:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
      if (data->threads[x].type == IO) {
  403786:	0f 84 ab 00 00 00    	je     403837 <timer_thread+0x427>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  40378c:	83 c5 01             	add    $0x1,%ebp
  40378f:	39 f5                	cmp    %esi,%ebp
  403791:	7c d5                	jl     403768 <timer_thread+0x358>
    for (int x = 0 ; x < data->thread_count ; x++) {
  403793:	41 8b 47 18          	mov    0x18(%r15),%eax
  403797:	85 c0                	test   %eax,%eax
  403799:	7e 58                	jle    4037f3 <timer_thread+0x3e3>
      for (int y = 0 ; y < data->task_count ; y++) {
  40379b:	41 8b 47 28          	mov    0x28(%r15),%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
  40379f:	45 31 c0             	xor    %r8d,%r8d
        data->threads[x].tasks[y].scheduled = 0;
  4037a2:	31 ff                	xor    %edi,%edi
  4037a4:	0f 1f 40 00          	nopl   0x0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
  4037a8:	85 c0                	test   %eax,%eax
  4037aa:	7e 47                	jle    4037f3 <timer_thread+0x3e3>
        data->threads[x].tasks[y].scheduled = 0;
  4037ac:	49 63 c0             	movslq %r8d,%rax
  4037af:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
  4037b3:	48 8d 34 50          	lea    (%rax,%rdx,2),%rsi
      for (int y = 0 ; y < data->task_count ; y++) {
  4037b7:	31 d2                	xor    %edx,%edx
        data->threads[x].tasks[y].scheduled = 0;
  4037b9:	48 c1 e6 03          	shl    $0x3,%rsi
  4037bd:	0f 1f 00             	nopl   (%rax)
  4037c0:	49 8b 4f 10          	mov    0x10(%r15),%rcx
  4037c4:	48 63 c2             	movslq %edx,%rax
  4037c7:	89 fb                	mov    %edi,%ebx
  4037c9:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  4037cd:	48 c1 e0 07          	shl    $0x7,%rax
  4037d1:	48 03 44 31 20       	add    0x20(%rcx,%rsi,1),%rax
  4037d6:	48 05 00 02 00 00    	add    $0x200,%rax
  4037dc:	87 18                	xchg   %ebx,(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
  4037de:	41 8b 47 28          	mov    0x28(%r15),%eax
  4037e2:	83 c2 01             	add    $0x1,%edx
  4037e5:	39 d0                	cmp    %edx,%eax
  4037e7:	7f d7                	jg     4037c0 <timer_thread+0x3b0>
    for (int x = 0 ; x < data->thread_count ; x++) {
  4037e9:	41 83 c0 01          	add    $0x1,%r8d
  4037ed:	45 3b 47 18          	cmp    0x18(%r15),%r8d
  4037f1:	7c b5                	jl     4037a8 <timer_thread+0x398>
    asm volatile ("mfence" ::: "memory");
  4037f3:	0f ae f0             	mfence
  4037f6:	48 8d 3d 83 28 00 00 	lea    0x2883(%rip),%rdi        # 406080 <_IO_stdin_used+0x80>
  4037fd:	e8 4e e8 ff ff       	call   402050 <puts@plt>
    data->running = 0;
  403802:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
  40380a:	48 8d 3d 76 28 00 00 	lea    0x2876(%rip),%rdi        # 406087 <_IO_stdin_used+0x87>
  403811:	e8 3a e8 ff ff       	call   402050 <puts@plt>
}
  403816:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  40381b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  403824:	75 43                	jne    403869 <timer_thread+0x459>
  403826:	48 83 c4 68          	add    $0x68,%rsp
  40382a:	31 c0                	xor    %eax,%eax
  40382c:	5b                   	pop    %rbx
  40382d:	5d                   	pop    %rbp
  40382e:	41 5c                	pop    %r12
  403830:	41 5d                	pop    %r13
  403832:	41 5e                	pop    %r14
  403834:	41 5f                	pop    %r15
  403836:	c3                   	ret
  403837:	4c 89 e7             	mov    %r12,%rdi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  40383a:	83 c5 01             	add    $0x1,%ebp
  40383d:	e8 0e e8 ff ff       	call   402050 <puts@plt>
        eventfd_write(data->threads[x]._eventfd, 1);
  403842:	49 8b 47 10          	mov    0x10(%r15),%rax
  403846:	be 01 00 00 00       	mov    $0x1,%esi
  40384b:	8b 7c 18 48          	mov    0x48(%rax,%rbx,1),%edi
  40384f:	e8 0c e9 ff ff       	call   402160 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  403854:	41 8b 77 1c          	mov    0x1c(%r15),%esi
  403858:	39 f5                	cmp    %esi,%ebp
  40385a:	0f 8d 33 ff ff ff    	jge    403793 <timer_thread+0x383>
  403860:	49 8b 57 10          	mov    0x10(%r15),%rdx
  403864:	e9 ff fe ff ff       	jmp    403768 <timer_thread+0x358>
}
  403869:	e8 22 e8 ff ff       	call   402090 <__stack_chk_fail@plt>
  40386e:	66 90                	xchg   %ax,%ax

0000000000403870 <fatal_error>:
void fatal_error(const char *syscall) {
  403870:	48 83 ec 08          	sub    $0x8,%rsp
    perror(syscall);
  403874:	e8 77 e9 ff ff       	call   4021f0 <perror@plt>
    exit(1);
  403879:	bf 01 00 00 00       	mov    $0x1,%edi
  40387e:	e8 7d e9 ff ff       	call   402200 <exit@plt>
  403883:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40388e:	66 90                	xchg   %ax,%ax

0000000000403890 <strtolower>:
void strtolower(char *str) {
  403890:	55                   	push   %rbp
  403891:	53                   	push   %rbx
  403892:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
  403896:	48 0f be 1f          	movsbq (%rdi),%rbx
  40389a:	84 db                	test   %bl,%bl
  40389c:	74 28                	je     4038c6 <strtolower+0x36>
  40389e:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
  4038a1:	e8 ca e9 ff ff       	call   402270 <__ctype_tolower_loc@plt>
  4038a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4038b0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
  4038b3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
  4038b7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
  4038ba:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
  4038bd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
  4038c2:	84 db                	test   %bl,%bl
  4038c4:	75 ea                	jne    4038b0 <strtolower+0x20>
}
  4038c6:	48 83 c4 08          	add    $0x8,%rsp
  4038ca:	5b                   	pop    %rbx
  4038cb:	5d                   	pop    %rbp
  4038cc:	c3                   	ret
  4038cd:	0f 1f 00             	nopl   (%rax)

00000000004038d0 <zh_malloc>:
void *zh_malloc(size_t size) {
  4038d0:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
  4038d4:	e8 97 e8 ff ff       	call   402170 <malloc@plt>
    if (!buf) {
  4038d9:	48 85 c0             	test   %rax,%rax
  4038dc:	74 05                	je     4038e3 <zh_malloc+0x13>
}
  4038de:	48 83 c4 08          	add    $0x8,%rsp
  4038e2:	c3                   	ret
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
  4038e3:	48 8b 05 0e 57 00 00 	mov    0x570e(%rip),%rax        # 408ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  4038ea:	ba 28 00 00 00       	mov    $0x28,%edx
  4038ef:	be 01 00 00 00       	mov    $0x1,%esi
  4038f4:	48 8d 3d 25 2b 00 00 	lea    0x2b25(%rip),%rdi        # 406420 <_IO_stdin_used+0x420>
  4038fb:	48 8b 08             	mov    (%rax),%rcx
  4038fe:	e8 1d e9 ff ff       	call   402220 <fwrite@plt>
        exit(1);
  403903:	bf 01 00 00 00       	mov    $0x1,%edi
  403908:	e8 f3 e8 ff ff       	call   402200 <exit@plt>
  40390d:	0f 1f 00             	nopl   (%rax)

0000000000403910 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
  403910:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
  403911:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
  403916:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
  403919:	e8 a2 e7 ff ff       	call   4020c0 <strrchr@plt>
    if (!dot || dot == filename)
  40391e:	48 85 c0             	test   %rax,%rax
  403921:	74 0d                	je     403930 <get_filename_ext+0x20>
  403923:	48 39 c3             	cmp    %rax,%rbx
  403926:	74 08                	je     403930 <get_filename_ext+0x20>
    return dot + 1;
  403928:	48 83 c0 01          	add    $0x1,%rax
}
  40392c:	5b                   	pop    %rbx
  40392d:	c3                   	ret
  40392e:	66 90                	xchg   %ax,%ax
        return "";
  403930:	48 8d 05 98 27 00 00 	lea    0x2798(%rip),%rax        # 4060cf <_IO_stdin_used+0xcf>
}
  403937:	5b                   	pop    %rbx
  403938:	c3                   	ret
  403939:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000403940 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
  403940:	41 55                	push   %r13
  403942:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  403945:	48 89 fe             	mov    %rdi,%rsi
  403948:	41 54                	push   %r12
  return __builtin___memcpy_chk (__dest, __src, __len,
  40394a:	41 bc 31 0d 00 00    	mov    $0xd31,%r12d
  403950:	55                   	push   %rbp
  403951:	53                   	push   %rbx
  403952:	48 89 d3             	mov    %rdx,%rbx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  403955:	ba 00 04 00 00       	mov    $0x400,%edx
  40395a:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
  403961:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40396a:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
  403972:	31 c0                	xor    %eax,%eax
  403974:	48 89 e5             	mov    %rsp,%rbp
  403977:	48 89 ef             	mov    %rbp,%rdi
  40397a:	e8 11 e8 ff ff       	call   402190 <__strcpy_chk@plt>
    strtolower(small_case_path);
  40397f:	48 89 ef             	mov    %rbp,%rdi
  403982:	e8 09 ff ff ff       	call   403890 <strtolower>
    iov[0].iov_base = zh_malloc(slen);
  403987:	bf 11 00 00 00       	mov    $0x11,%edi
  40398c:	e8 3f ff ff ff       	call   4038d0 <zh_malloc>
    iov[0].iov_len = slen;
  403991:	48 c7 43 08 11 00 00 00 	movq   $0x11,0x8(%rbx)
    iov[1].iov_base = zh_malloc(slen);
  403999:	bf 17 00 00 00       	mov    $0x17,%edi
  return __builtin___memcpy_chk (__dest, __src, __len,
  40399e:	66 0f 6f 05 6a 2f 00 00 	movdqa 0x2f6a(%rip),%xmm0        # 406910 <_IO_stdin_used+0x910>
    iov[0].iov_base = zh_malloc(slen);
  4039a6:	48 89 03             	mov    %rax,(%rbx)
  4039a9:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
  4039ad:	0f 11 00             	movups %xmm0,(%rax)
    iov[1].iov_base = zh_malloc(slen);
  4039b0:	e8 1b ff ff ff       	call   4038d0 <zh_malloc>
    iov[1].iov_len = slen;
  4039b5:	48 c7 43 18 17 00 00 00 	movq   $0x17,0x18(%rbx)
  4039bd:	66 0f 6f 05 5b 2f 00 00 	movdqa 0x2f5b(%rip),%xmm0        # 406920 <_IO_stdin_used+0x920>
    const char *file_ext = get_filename_ext(small_case_path);
  4039c5:	48 89 ef             	mov    %rbp,%rdi
    iov[1].iov_base = zh_malloc(slen);
  4039c8:	48 89 43 10          	mov    %rax,0x10(%rbx)
  4039cc:	c7 40 10 64 2f 30 2e 	movl   $0x2e302f64,0x10(%rax)
  4039d3:	66 44 89 60 14       	mov    %r12w,0x14(%rax)
  4039d8:	c6 40 16 0a          	movb   $0xa,0x16(%rax)
  4039dc:	0f 11 00             	movups %xmm0,(%rax)
    const char *file_ext = get_filename_ext(small_case_path);
  4039df:	e8 2c ff ff ff       	call   403910 <get_filename_ext>
    if (strcmp("jpg", file_ext) == 0)
  4039e4:	48 8d 3d b2 26 00 00 	lea    0x26b2(%rip),%rdi        # 40609d <_IO_stdin_used+0x9d>
  4039eb:	48 89 c6             	mov    %rax,%rsi
    const char *file_ext = get_filename_ext(small_case_path);
  4039ee:	48 89 c5             	mov    %rax,%rbp
    if (strcmp("jpg", file_ext) == 0)
  4039f1:	e8 1a e7 ff ff       	call   402110 <strcmp@plt>
  4039f6:	85 c0                	test   %eax,%eax
  4039f8:	0f 84 42 03 00 00    	je     403d40 <send_headers+0x400>
    if (strcmp("jpeg", file_ext) == 0)
  4039fe:	48 89 ee             	mov    %rbp,%rsi
  403a01:	48 8d 3d 99 26 00 00 	lea    0x2699(%rip),%rdi        # 4060a1 <_IO_stdin_used+0xa1>
  403a08:	e8 03 e7 ff ff       	call   402110 <strcmp@plt>
  403a0d:	85 c0                	test   %eax,%eax
  403a0f:	0f 84 eb 02 00 00    	je     403d00 <send_headers+0x3c0>
    if (strcmp("png", file_ext) == 0)
  403a15:	48 89 ee             	mov    %rbp,%rsi
  403a18:	48 8d 3d 87 26 00 00 	lea    0x2687(%rip),%rdi        # 4060a6 <_IO_stdin_used+0xa6>
  403a1f:	e8 ec e6 ff ff       	call   402110 <strcmp@plt>
  403a24:	85 c0                	test   %eax,%eax
  403a26:	0f 84 04 04 00 00    	je     403e30 <send_headers+0x4f0>
    if (strcmp("gif", file_ext) == 0)
  403a2c:	48 89 ee             	mov    %rbp,%rsi
  403a2f:	48 8d 3d 74 26 00 00 	lea    0x2674(%rip),%rdi        # 4060aa <_IO_stdin_used+0xaa>
  403a36:	e8 d5 e6 ff ff       	call   402110 <strcmp@plt>
  403a3b:	85 c0                	test   %eax,%eax
  403a3d:	0f 84 ad 03 00 00    	je     403df0 <send_headers+0x4b0>
    if (strcmp("htm", file_ext) == 0)
  403a43:	48 89 ee             	mov    %rbp,%rsi
  403a46:	48 8d 3d 61 26 00 00 	lea    0x2661(%rip),%rdi        # 4060ae <_IO_stdin_used+0xae>
  403a4d:	e8 be e6 ff ff       	call   402110 <strcmp@plt>
  403a52:	85 c0                	test   %eax,%eax
  403a54:	0f 84 5e 03 00 00    	je     403db8 <send_headers+0x478>
    if (strcmp("html", file_ext) == 0)
  403a5a:	48 89 ee             	mov    %rbp,%rsi
  403a5d:	48 8d 3d 8d 26 00 00 	lea    0x268d(%rip),%rdi        # 4060f1 <_IO_stdin_used+0xf1>
  403a64:	e8 a7 e6 ff ff       	call   402110 <strcmp@plt>
  403a69:	85 c0                	test   %eax,%eax
  403a6b:	0f 84 0f 03 00 00    	je     403d80 <send_headers+0x440>
    if (strcmp("js", file_ext) == 0)
  403a71:	80 7d 00 6a          	cmpb   $0x6a,0x0(%rbp)
  403a75:	75 0a                	jne    403a81 <send_headers+0x141>
  403a77:	80 7d 01 73          	cmpb   $0x73,0x1(%rbp)
  403a7b:	0f 84 b7 01 00 00    	je     403c38 <send_headers+0x2f8>
    if (strcmp("css", file_ext) == 0)
  403a81:	48 89 ee             	mov    %rbp,%rsi
  403a84:	48 8d 3d 27 26 00 00 	lea    0x2627(%rip),%rdi        # 4060b2 <_IO_stdin_used+0xb2>
  403a8b:	e8 80 e6 ff ff       	call   402110 <strcmp@plt>
  403a90:	85 c0                	test   %eax,%eax
  403a92:	0f 84 f8 01 00 00    	je     403c90 <send_headers+0x350>
    if (strcmp("txt", file_ext) == 0)
  403a98:	48 89 ee             	mov    %rbp,%rsi
  403a9b:	48 8d 3d 14 26 00 00 	lea    0x2614(%rip),%rdi        # 4060b6 <_IO_stdin_used+0xb6>
  403aa2:	e8 69 e6 ff ff       	call   402110 <strcmp@plt>
  403aa7:	85 c0                	test   %eax,%eax
  403aa9:	0f 84 11 02 00 00    	je     403cc0 <send_headers+0x380>
    slen = strlen(send_buffer);
  403aaf:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
  403ab7:	4c 89 e7             	mov    %r12,%rdi
  403aba:	e8 c1 e5 ff ff       	call   402080 <strlen@plt>
    iov[2].iov_base = zh_malloc(slen);
  403abf:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
  403ac2:	48 89 c5             	mov    %rax,%rbp
    iov[2].iov_base = zh_malloc(slen);
  403ac5:	e8 06 fe ff ff       	call   4038d0 <zh_malloc>
    iov[2].iov_len = slen;
  403aca:	48 89 6b 28          	mov    %rbp,0x28(%rbx)
    iov[2].iov_base = zh_malloc(slen);
  403ace:	48 89 43 20          	mov    %rax,0x20(%rbx)
  403ad2:	83 fd 08             	cmp    $0x8,%ebp
  403ad5:	73 31                	jae    403b08 <send_headers+0x1c8>
  403ad7:	40 f6 c5 04          	test   $0x4,%bpl
  403adb:	0f 85 8f 03 00 00    	jne    403e70 <send_headers+0x530>
  403ae1:	85 ed                	test   %ebp,%ebp
  403ae3:	74 55                	je     403b3a <send_headers+0x1fa>
  403ae5:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
  403aed:	88 10                	mov    %dl,(%rax)
  403aef:	40 f6 c5 02          	test   $0x2,%bpl
  403af3:	74 45                	je     403b3a <send_headers+0x1fa>
  403af5:	89 ed                	mov    %ebp,%ebp
  403af7:	41 0f b7 54 2c fe    	movzwl -0x2(%r12,%rbp,1),%edx
  403afd:	66 89 54 28 fe       	mov    %dx,-0x2(%rax,%rbp,1)
  403b02:	eb 36                	jmp    403b3a <send_headers+0x1fa>
  403b04:	0f 1f 40 00          	nopl   0x0(%rax)
  403b08:	48 8b 94 24 00 04 00 00 	mov    0x400(%rsp),%rdx
  403b10:	48 8d 78 08          	lea    0x8(%rax),%rdi
  403b14:	4c 89 e6             	mov    %r12,%rsi
  403b17:	48 83 e7 f8          	and    $0xfffffffffffffff8,%rdi
  403b1b:	48 89 10             	mov    %rdx,(%rax)
  403b1e:	89 ea                	mov    %ebp,%edx
  403b20:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
  403b25:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
  403b2a:	48 29 f8             	sub    %rdi,%rax
  403b2d:	8d 4c 05 00          	lea    0x0(%rbp,%rax,1),%ecx
  403b31:	48 29 c6             	sub    %rax,%rsi
  403b34:	c1 e9 03             	shr    $0x3,%ecx
  403b37:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  403b3a:	4d 89 e8             	mov    %r13,%r8
  403b3d:	48 8d 0d 76 25 00 00 	lea    0x2576(%rip),%rcx        # 4060ba <_IO_stdin_used+0xba>
  403b44:	4c 89 e7             	mov    %r12,%rdi
  403b47:	31 c0                	xor    %eax,%eax
  403b49:	ba 00 04 00 00       	mov    $0x400,%edx
  403b4e:	be 01 00 00 00       	mov    $0x1,%esi
  403b53:	e8 28 e7 ff ff       	call   402280 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
  403b58:	4c 89 e7             	mov    %r12,%rdi
  403b5b:	e8 20 e5 ff ff       	call   402080 <strlen@plt>
    iov[3].iov_base = zh_malloc(slen);
  403b60:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
  403b63:	48 89 c5             	mov    %rax,%rbp
    iov[3].iov_base = zh_malloc(slen);
  403b66:	e8 65 fd ff ff       	call   4038d0 <zh_malloc>
    iov[3].iov_len = slen;
  403b6b:	48 89 6b 38          	mov    %rbp,0x38(%rbx)
    iov[3].iov_base = zh_malloc(slen);
  403b6f:	48 89 43 30          	mov    %rax,0x30(%rbx)
  403b73:	83 fd 08             	cmp    $0x8,%ebp
  403b76:	73 30                	jae    403ba8 <send_headers+0x268>
  403b78:	40 f6 c5 04          	test   $0x4,%bpl
  403b7c:	0f 85 0e 03 00 00    	jne    403e90 <send_headers+0x550>
  403b82:	85 ed                	test   %ebp,%ebp
  403b84:	74 54                	je     403bda <send_headers+0x29a>
  403b86:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
  403b8e:	88 10                	mov    %dl,(%rax)
  403b90:	40 f6 c5 02          	test   $0x2,%bpl
  403b94:	74 44                	je     403bda <send_headers+0x29a>
  403b96:	89 ed                	mov    %ebp,%ebp
  403b98:	41 0f b7 54 2c fe    	movzwl -0x2(%r12,%rbp,1),%edx
  403b9e:	66 89 54 28 fe       	mov    %dx,-0x2(%rax,%rbp,1)
  403ba3:	eb 35                	jmp    403bda <send_headers+0x29a>
  403ba5:	0f 1f 00             	nopl   (%rax)
  403ba8:	48 8b 94 24 00 04 00 00 	mov    0x400(%rsp),%rdx
  403bb0:	48 8d 78 08          	lea    0x8(%rax),%rdi
  403bb4:	4c 89 e6             	mov    %r12,%rsi
  403bb7:	48 83 e7 f8          	and    $0xfffffffffffffff8,%rdi
  403bbb:	48 89 10             	mov    %rdx,(%rax)
  403bbe:	89 ea                	mov    %ebp,%edx
  403bc0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
  403bc5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
  403bca:	48 29 f8             	sub    %rdi,%rax
  403bcd:	8d 4c 05 00          	lea    0x0(%rbp,%rax,1),%ecx
  403bd1:	48 29 c6             	sub    %rax,%rsi
  403bd4:	c1 e9 03             	shr    $0x3,%ecx
  403bd7:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  403bda:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    iov[4].iov_base = zh_malloc(slen);
  403bdf:	bf 02 00 00 00       	mov    $0x2,%edi
  403be4:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
  403bec:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
  403bf4:	e8 d7 fc ff ff       	call   4038d0 <zh_malloc>
  403bf9:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_len = slen;
  403c01:	48 c7 43 48 02 00 00 00 	movq   $0x2,0x48(%rbx)
    iov[4].iov_base = zh_malloc(slen);
  403c09:	48 89 43 40          	mov    %rax,0x40(%rbx)
  return __builtin___memcpy_chk (__dest, __src, __len,
  403c0d:	66 89 10             	mov    %dx,(%rax)
}
  403c10:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
  403c18:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  403c21:	0f 85 82 02 00 00    	jne    403ea9 <send_headers+0x569>
  403c27:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
  403c2e:	5b                   	pop    %rbx
  403c2f:	5d                   	pop    %rbp
  403c30:	41 5c                	pop    %r12
  403c32:	41 5d                	pop    %r13
  403c34:	c3                   	ret
  403c35:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
  403c38:	80 7d 02 00          	cmpb   $0x0,0x2(%rbp)
  403c3c:	0f 85 3f fe ff ff    	jne    403a81 <send_headers+0x141>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  403c42:	66 0f 6f 05 06 2d 00 00 	movdqa 0x2d06(%rip),%xmm0        # 406950 <_IO_stdin_used+0x950>
  403c4a:	b9 0d 0a 00 00       	mov    $0xa0d,%ecx
  403c4f:	c7 84 24 20 04 00 00 72 69 70 74 	movl   $0x74706972,0x420(%rsp)
  403c5a:	66 89 8c 24 24 04 00 00 	mov    %cx,0x424(%rsp)
  403c62:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403c6a:	66 0f 6f 05 ee 2c 00 00 	movdqa 0x2cee(%rip),%xmm0        # 406960 <_IO_stdin_used+0x960>
  403c72:	c6 84 24 26 04 00 00 00 	movb   $0x0,0x426(%rsp)
  403c7a:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
  403c82:	e9 fa fd ff ff       	jmp    403a81 <send_headers+0x141>
  403c87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  403c90:	66 0f 6f 05 a8 2c 00 00 	movdqa 0x2ca8(%rip),%xmm0        # 406940 <_IO_stdin_used+0x940>
  403c98:	c6 84 24 18 04 00 00 00 	movb   $0x0,0x418(%rsp)
  403ca0:	48 b8 78 74 2f 63 73 73 0d 0a 	movabs $0xa0d7373632f7478,%rax
  403caa:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403cb2:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403cba:	e9 d9 fd ff ff       	jmp    403a98 <send_headers+0x158>
  403cbf:	90                   	nop
  403cc0:	66 0f 6f 05 78 2c 00 00 	movdqa 0x2c78(%rip),%xmm0        # 406940 <_IO_stdin_used+0x940>
  403cc8:	ba 0d 0a 00 00       	mov    $0xa0d,%edx
  403ccd:	48 b8 78 74 2f 70 6c 61 69 6e 	movabs $0x6e69616c702f7478,%rax
  403cd7:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  403cdf:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403ce7:	66 89 94 24 18 04 00 00 	mov    %dx,0x418(%rsp)
  403cef:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403cf7:	e9 b3 fd ff ff       	jmp    403aaf <send_headers+0x16f>
  403cfc:	0f 1f 40 00          	nopl   0x0(%rax)
  403d00:	66 0f 6f 05 28 2c 00 00 	movdqa 0x2c28(%rip),%xmm0        # 406930 <_IO_stdin_used+0x930>
  403d08:	41 ba 0d 0a 00 00    	mov    $0xa0d,%r10d
  403d0e:	48 b8 61 67 65 2f 6a 70 65 67 	movabs $0x6765706a2f656761,%rax
  403d18:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  403d20:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403d28:	66 44 89 94 24 18 04 00 00 	mov    %r10w,0x418(%rsp)
  403d31:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403d39:	e9 d7 fc ff ff       	jmp    403a15 <send_headers+0xd5>
  403d3e:	66 90                	xchg   %ax,%ax
  403d40:	66 0f 6f 05 e8 2b 00 00 	movdqa 0x2be8(%rip),%xmm0        # 406930 <_IO_stdin_used+0x930>
  403d48:	41 bb 0d 0a 00 00    	mov    $0xa0d,%r11d
  403d4e:	48 b8 61 67 65 2f 6a 70 65 67 	movabs $0x6765706a2f656761,%rax
  403d58:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  403d60:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403d68:	66 44 89 9c 24 18 04 00 00 	mov    %r11w,0x418(%rsp)
  403d71:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403d79:	e9 80 fc ff ff       	jmp    4039fe <send_headers+0xbe>
  403d7e:	66 90                	xchg   %ax,%ax
  403d80:	66 0f 6f 05 b8 2b 00 00 	movdqa 0x2bb8(%rip),%xmm0        # 406940 <_IO_stdin_used+0x940>
  403d88:	be 0a 00 00 00       	mov    $0xa,%esi
  403d8d:	48 b8 78 74 2f 68 74 6d 6c 0d 	movabs $0xd6c6d74682f7478,%rax
  403d97:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403d9f:	66 89 b4 24 18 04 00 00 	mov    %si,0x418(%rsp)
  403da7:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403daf:	e9 bd fc ff ff       	jmp    403a71 <send_headers+0x131>
  403db4:	0f 1f 40 00          	nopl   0x0(%rax)
  403db8:	66 0f 6f 05 80 2b 00 00 	movdqa 0x2b80(%rip),%xmm0        # 406940 <_IO_stdin_used+0x940>
  403dc0:	bf 0a 00 00 00       	mov    $0xa,%edi
  403dc5:	48 b8 78 74 2f 68 74 6d 6c 0d 	movabs $0xd6c6d74682f7478,%rax
  403dcf:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403dd7:	66 89 bc 24 18 04 00 00 	mov    %di,0x418(%rsp)
  403ddf:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403de7:	e9 6e fc ff ff       	jmp    403a5a <send_headers+0x11a>
  403dec:	0f 1f 40 00          	nopl   0x0(%rax)
  403df0:	66 0f 6f 05 38 2b 00 00 	movdqa 0x2b38(%rip),%xmm0        # 406930 <_IO_stdin_used+0x930>
  403df8:	41 b8 0a 00 00 00    	mov    $0xa,%r8d
  403dfe:	48 b8 61 67 65 2f 67 69 66 0d 	movabs $0xd6669672f656761,%rax
  403e08:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403e10:	66 44 89 84 24 18 04 00 00 	mov    %r8w,0x418(%rsp)
  403e19:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403e21:	e9 1d fc ff ff       	jmp    403a43 <send_headers+0x103>
  403e26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  403e30:	66 0f 6f 05 f8 2a 00 00 	movdqa 0x2af8(%rip),%xmm0        # 406930 <_IO_stdin_used+0x930>
  403e38:	41 b9 0a 00 00 00    	mov    $0xa,%r9d
  403e3e:	48 b8 61 67 65 2f 70 6e 67 0d 	movabs $0xd676e702f656761,%rax
  403e48:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403e50:	66 44 89 8c 24 18 04 00 00 	mov    %r9w,0x418(%rsp)
  403e59:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403e61:	e9 c6 fb ff ff       	jmp    403a2c <send_headers+0xec>
  403e66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
  403e70:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
  403e77:	89 ed                	mov    %ebp,%ebp
  403e79:	89 10                	mov    %edx,(%rax)
  403e7b:	41 8b 54 2c fc       	mov    -0x4(%r12,%rbp,1),%edx
  403e80:	89 54 28 fc          	mov    %edx,-0x4(%rax,%rbp,1)
  403e84:	e9 b1 fc ff ff       	jmp    403b3a <send_headers+0x1fa>
  403e89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  403e90:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
  403e97:	89 ed                	mov    %ebp,%ebp
  403e99:	89 10                	mov    %edx,(%rax)
  403e9b:	41 8b 54 2c fc       	mov    -0x4(%r12,%rbp,1),%edx
  403ea0:	89 54 28 fc          	mov    %edx,-0x4(%rax,%rbp,1)
  403ea4:	e9 31 fd ff ff       	jmp    403bda <send_headers+0x29a>
}
  403ea9:	e8 e2 e1 ff ff       	call   402090 <__stack_chk_fail@plt>
  403eae:	66 90                	xchg   %ax,%ax

0000000000403eb0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
  403eb0:	41 55                	push   %r13
  403eb2:	41 54                	push   %r12
  403eb4:	49 89 d4             	mov    %rdx,%r12
  403eb7:	55                   	push   %rbp
  403eb8:	48 89 fd             	mov    %rdi,%rbp
    char *buf = zh_malloc(file_size);
  403ebb:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
  403ebe:	53                   	push   %rbx
  403ebf:	48 89 f3             	mov    %rsi,%rbx
  403ec2:	48 83 ec 08          	sub    $0x8,%rsp
    char *buf = zh_malloc(file_size);
  403ec6:	e8 05 fa ff ff       	call   4038d0 <zh_malloc>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
  403ecb:	48 89 ef             	mov    %rbp,%rdi
  403ece:	31 f6                	xor    %esi,%esi
  403ed0:	49 89 c5             	mov    %rax,%r13
  403ed3:	31 c0                	xor    %eax,%eax
  403ed5:	e8 06 e3 ff ff       	call   4021e0 <open@plt>
  403eda:	89 c5                	mov    %eax,%ebp
    if (fd < 0)
  403edc:	85 c0                	test   %eax,%eax
  403ede:	78 58                	js     403f38 <copy_file_contents+0x88>
		       "the destination buffer");

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
  403ee0:	48 89 da             	mov    %rbx,%rdx
  403ee3:	4c 89 ee             	mov    %r13,%rsi
  403ee6:	89 ef                	mov    %ebp,%edi
  403ee8:	e8 03 e2 ff ff       	call   4020f0 <read@plt>
    if (ret < file_size) {
  403eed:	48 98                	cltq
  403eef:	48 39 d8             	cmp    %rbx,%rax
  403ef2:	7c 1c                	jl     403f10 <copy_file_contents+0x60>
    close(fd);
  403ef4:	89 ef                	mov    %ebp,%edi
  403ef6:	e8 d5 e1 ff ff       	call   4020d0 <close@plt>
    iov->iov_base = buf;
  403efb:	4d 89 2c 24          	mov    %r13,(%r12)
    iov->iov_len = file_size;
  403eff:	49 89 5c 24 08       	mov    %rbx,0x8(%r12)
}
  403f04:	48 83 c4 08          	add    $0x8,%rsp
  403f08:	5b                   	pop    %rbx
  403f09:	5d                   	pop    %rbp
  403f0a:	41 5c                	pop    %r12
  403f0c:	41 5d                	pop    %r13
  403f0e:	c3                   	ret
  403f0f:	90                   	nop
        fprintf(stderr, "Encountered a short read.\n");
  403f10:	48 8b 05 e1 50 00 00 	mov    0x50e1(%rip),%rax        # 408ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  403f17:	ba 1a 00 00 00       	mov    $0x1a,%edx
  403f1c:	be 01 00 00 00       	mov    $0x1,%esi
  403f21:	48 8d 3d a8 21 00 00 	lea    0x21a8(%rip),%rdi        # 4060d0 <_IO_stdin_used+0xd0>
  403f28:	48 8b 08             	mov    (%rax),%rcx
  403f2b:	e8 f0 e2 ff ff       	call   402220 <fwrite@plt>
  403f30:	eb c2                	jmp    403ef4 <copy_file_contents+0x44>
  403f32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        fatal_error("read");
  403f38:	48 8d 3d c0 22 00 00 	lea    0x22c0(%rip),%rdi        # 4061ff <_IO_stdin_used+0x1ff>
  403f3f:	e8 2c f9 ff ff       	call   403870 <fatal_error>
  403f44:	eb 9a                	jmp    403ee0 <copy_file_contents+0x30>
  403f46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000403f50 <add_write_request>:
 * Returns a vacant sqe, or NULL if we're full.
 */
static inline struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  403f50:	48 8b 06             	mov    (%rsi),%rax
int add_write_request(struct Request *req, struct io_uring *ring) {
  403f53:	48 89 fa             	mov    %rdi,%rdx
  403f56:	48 89 f7             	mov    %rsi,%rdi
  403f59:	44 8b 00             	mov    (%rax),%r8d
	unsigned int next = sq->sqe_tail + 1;
  403f5c:	8b 46 44             	mov    0x44(%rsi),%eax
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
  403f5f:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int next = sq->sqe_tail + 1;
  403f65:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;

	if (next - head <= *sq->kring_entries) {
  403f68:	41 89 f1             	mov    %esi,%r9d
  403f6b:	45 29 c1             	sub    %r8d,%r9d
  403f6e:	4c 8b 47 18          	mov    0x18(%rdi),%r8
  403f72:	45 3b 08             	cmp    (%r8),%r9d
  403f75:	0f 87 25 e3 ff ff    	ja     4022a0 <add_write_request.cold>
  403f7b:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  403f7f:	4c 8b 47 10          	mov    0x10(%rdi),%r8
	if (ring->flags & IORING_SETUP_SQE128)
  403f83:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  403f86:	66 0f ef c0          	pxor   %xmm0,%xmm0
	if (ring->flags & IORING_SETUP_SQE128)
  403f8a:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  403f8d:	41 23 00             	and    (%r8),%eax
		sq->sqe_tail = next;
  403f90:	89 77 44             	mov    %esi,0x44(%rdi)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  403f93:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
  403f95:	8b 72 08             	mov    0x8(%rdx),%esi
  403f98:	8b 4a 04             	mov    0x4(%rdx),%ecx
  403f9b:	48 c1 e0 06          	shl    $0x6,%rax
  403f9f:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
  403fa3:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
  403fa9:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
  403fac:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
  403fb0:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
  403fb6:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
  403fbe:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
  403fc2:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
  403fc5:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
  403fcc:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  403fd4:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
  403fd8:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
  403fdc:	e8 bf e0 ff ff       	call   4020a0 <io_uring_submit@plt>
}
  403fe1:	31 c0                	xor    %eax,%eax
  403fe3:	48 83 c4 08          	add    $0x8,%rsp
  403fe7:	c3                   	ret
  403fe8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000403ff0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
  403ff0:	41 55                	push   %r13
  403ff2:	41 54                	push   %r12
  403ff4:	55                   	push   %rbp
  403ff5:	48 89 f5             	mov    %rsi,%rbp
  403ff8:	53                   	push   %rbx
  403ff9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  403ffd:	48 8b 06             	mov    (%rsi),%rax
  404000:	8b 10                	mov    (%rax),%edx
	unsigned int next = sq->sqe_tail + 1;
  404002:	8b 5e 44             	mov    0x44(%rsi),%ebx
	if (ring->flags & IORING_SETUP_SQE128)
  404005:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
	unsigned int next = sq->sqe_tail + 1;
  40400b:	8d 43 01             	lea    0x1(%rbx),%eax
	if (next - head <= *sq->kring_entries) {
  40400e:	89 c6                	mov    %eax,%esi
  404010:	29 d6                	sub    %edx,%esi
  404012:	48 8b 55 18          	mov    0x18(%rbp),%rdx
  404016:	3b 32                	cmp    (%rdx),%esi
  404018:	0f 87 92 e2 ff ff    	ja     4022b0 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40401e:	48 8b 55 10          	mov    0x10(%rbp),%rdx
	if (ring->flags & IORING_SETUP_SQE128)
  404022:	c1 e9 0a             	shr    $0xa,%ecx
  404025:	41 89 fd             	mov    %edi,%r13d
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
  404028:	bf 20 00 00 00       	mov    $0x20,%edi
  40402d:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404030:	23 1a                	and    (%rdx),%ebx
		sq->sqe_tail = next;
  404032:	89 45 44             	mov    %eax,0x44(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404035:	d3 e3                	shl    %cl,%ebx
  404037:	48 c1 e3 06          	shl    $0x6,%rbx
  40403b:	48 03 5d 38          	add    0x38(%rbp),%rbx
  40403f:	e8 2c e1 ff ff       	call   402170 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
  404044:	be 01 00 00 00       	mov    $0x1,%esi
  404049:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
  40404e:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
  404051:	e8 aa e0 ff ff       	call   402100 <calloc@plt>
    req->client_socket = client_socket;
  404056:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
  40405b:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
  40405f:	48 89 ef             	mov    %rbp,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
  404062:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
  404067:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
  40406c:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
  404075:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
  40407d:	44 89 6b 04          	mov    %r13d,0x4(%rbx)
	sqe->user_data = (unsigned long) data;
  404081:	4c 89 63 20          	mov    %r12,0x20(%rbx)
	sqe->opcode = (__u8) op;
  404085:	c7 03 01 00 00 00    	movl   $0x1,(%rbx)
	sqe->off = offset;
  40408b:	48 c7 43 08 00 00 00 00 	movq   $0x0,0x8(%rbx)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
  404093:	48 89 43 10          	mov    %rax,0x10(%rbx)
	sqe->len = len;
  404097:	48 c7 43 18 01 00 00 00 	movq   $0x1,0x18(%rbx)
	sqe->buf_index = 0;
  40409f:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->addr3 = 0;
  4040a7:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
    io_uring_submit(ring);
  4040ab:	e8 f0 df ff ff       	call   4020a0 <io_uring_submit@plt>
}
  4040b0:	48 83 c4 08          	add    $0x8,%rsp
  4040b4:	31 c0                	xor    %eax,%eax
  4040b6:	5b                   	pop    %rbx
  4040b7:	5d                   	pop    %rbp
  4040b8:	41 5c                	pop    %r12
  4040ba:	41 5d                	pop    %r13
  4040bc:	c3                   	ret
  4040bd:	0f 1f 00             	nopl   (%rax)

00000000004040c0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
  4040c0:	41 56                	push   %r14
  4040c2:	49 89 d6             	mov    %rdx,%r14
  4040c5:	41 55                	push   %r13
  4040c7:	49 89 fd             	mov    %rdi,%r13
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  4040ca:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
  4040cf:	41 54                	push   %r12
  4040d1:	55                   	push   %rbp
  4040d2:	53                   	push   %rbx
  4040d3:	89 f3                	mov    %esi,%ebx
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  4040d5:	e8 f6 f7 ff ff       	call   4038d0 <zh_malloc>
    unsigned long slen = strlen(str);
  4040da:	4c 89 ef             	mov    %r13,%rdi
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  4040dd:	48 89 c5             	mov    %rax,%rbp
    unsigned long slen = strlen(str);
  4040e0:	e8 9b df ff ff       	call   402080 <strlen@plt>
    req->client_socket = client_socket;
  4040e5:	89 5d 08             	mov    %ebx,0x8(%rbp)
    req->iovec_count = 1;
  4040e8:	c7 45 04 01 00 00 00 	movl   $0x1,0x4(%rbp)
    req->iov[0].iov_base = zh_malloc(slen);
  4040ef:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
  4040f2:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = zh_malloc(slen);
  4040f5:	e8 d6 f7 ff ff       	call   4038d0 <zh_malloc>
    req->iov[0].iov_len = slen;
  4040fa:	4c 89 65 18          	mov    %r12,0x18(%rbp)
  4040fe:	4c 89 ee             	mov    %r13,%rsi
  404101:	4c 89 e2             	mov    %r12,%rdx
    req->iov[0].iov_base = zh_malloc(slen);
  404104:	48 89 45 10          	mov    %rax,0x10(%rbp)
  404108:	48 89 c7             	mov    %rax,%rdi
  40410b:	e8 30 e0 ff ff       	call   402140 <memcpy@plt>
}
  404110:	5b                   	pop    %rbx
    add_write_request(req, ring);
  404111:	4c 89 f6             	mov    %r14,%rsi
  404114:	48 89 ef             	mov    %rbp,%rdi
}
  404117:	5d                   	pop    %rbp
  404118:	41 5c                	pop    %r12
  40411a:	41 5d                	pop    %r13
  40411c:	41 5e                	pop    %r14
    add_write_request(req, ring);
  40411e:	e9 2d fe ff ff       	jmp    403f50 <add_write_request>
  404123:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40412e:	66 90                	xchg   %ax,%ax

0000000000404130 <handle_unimplemented_method>:
    _send_static_string_content(unimplemented_content, client_socket, ring);
  404130:	48 c7 c0 18 90 40 00 	mov    $0x409018,%rax
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
  404137:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
  40413a:	89 fe                	mov    %edi,%esi
  40413c:	48 8b 38             	mov    (%rax),%rdi
  40413f:	e9 7c ff ff ff       	jmp    4040c0 <_send_static_string_content>
  404144:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40414f:	90                   	nop

0000000000404150 <handle_http_404>:
    _send_static_string_content(http_404_content, client_socket, ring);
  404150:	48 c7 c0 10 90 40 00 	mov    $0x409010,%rax
void handle_http_404(int client_socket, struct io_uring *ring) {
  404157:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
  40415a:	89 fe                	mov    %edi,%esi
  40415c:	48 8b 38             	mov    (%rax),%rdi
  40415f:	e9 5c ff ff ff       	jmp    4040c0 <_send_static_string_content>
  404164:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40416f:	90                   	nop

0000000000404170 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
  404170:	41 56                	push   %r14
  404172:	41 55                	push   %r13
  404174:	49 89 d5             	mov    %rdx,%r13
  404177:	41 54                	push   %r12
  404179:	49 89 fc             	mov    %rdi,%r12
  40417c:	55                   	push   %rbp
  40417d:	89 f5                	mov    %esi,%ebp
  40417f:	53                   	push   %rbx
  404180:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
  404187:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  404190:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
  404198:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
  40419a:	e8 e1 de ff ff       	call   402080 <strlen@plt>
  40419f:	41 80 7c 04 ff 2f    	cmpb   $0x2f,-0x1(%r12,%rax,1)
  4041a5:	48 89 c3             	mov    %rax,%rbx
  4041a8:	0f 84 b2 00 00 00    	je     404260 <handle_get_method+0xf0>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  4041ae:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  4041b3:	4c 89 e6             	mov    %r12,%rsi
  4041b6:	48 8d 53 01          	lea    0x1(%rbx),%rdx
  4041ba:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  4041bf:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
  4041c7:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  4041cf:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  4041da:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  4041e2:	e8 39 df ff ff       	call   402120 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
  4041e7:	48 89 e6             	mov    %rsp,%rsi
  4041ea:	4c 89 f7             	mov    %r14,%rdi
  4041ed:	e8 3e df ff ff       	call   402130 <stat@plt>
  4041f2:	83 f8 ff             	cmp    $0xffffffff,%eax
  4041f5:	0f 84 cf 00 00 00    	je     4042ca <handle_get_method+0x15a>
        if (S_ISREG(path_stat.st_mode)) {
  4041fb:	8b 44 24 18          	mov    0x18(%rsp),%eax
  4041ff:	25 00 f0 00 00       	and    $0xf000,%eax
  404204:	3d 00 80 00 00       	cmp    $0x8000,%eax
  404209:	0f 84 e9 00 00 00    	je     4042f8 <handle_get_method+0x188>
            handle_http_404(client_socket, ring);
  40420f:	4c 89 ee             	mov    %r13,%rsi
  404212:	89 ef                	mov    %ebp,%edi
  404214:	e8 37 ff ff ff       	call   404150 <handle_http_404>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  404219:	4c 89 f2             	mov    %r14,%rdx
  40421c:	bf 01 00 00 00       	mov    $0x1,%edi
  404221:	31 c0                	xor    %eax,%eax
  404223:	48 8d 35 f6 1e 00 00 	lea    0x1ef6(%rip),%rsi        # 406120 <_IO_stdin_used+0x120>
  40422a:	e8 81 df ff ff       	call   4021b0 <__printf_chk@plt>
}
  40422f:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
  404237:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  404240:	0f 85 17 01 00 00    	jne    40435d <handle_get_method+0x1ed>
  404246:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
  40424d:	5b                   	pop    %rbx
  40424e:	5d                   	pop    %rbp
  40424f:	41 5c                	pop    %r12
  404251:	41 5d                	pop    %r13
  404253:	41 5e                	pop    %r14
  404255:	c3                   	ret
  404256:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404260:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  404265:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
  40426d:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  404272:	4c 89 e6             	mov    %r12,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404275:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  40427d:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404280:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  404288:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  404293:	e8 88 de ff ff       	call   402120 <__memcpy_chk@plt>
  404298:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  40429d:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
  4042a2:	48 8d 35 42 1e 00 00 	lea    0x1e42(%rip),%rsi        # 4060eb <_IO_stdin_used+0xeb>
  4042a9:	48 29 d9             	sub    %rbx,%rcx
  4042ac:	ba 0b 00 00 00       	mov    $0xb,%edx
  4042b1:	e8 6a de ff ff       	call   402120 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
  4042b6:	48 89 e6             	mov    %rsp,%rsi
  4042b9:	4c 89 f7             	mov    %r14,%rdi
  4042bc:	e8 6f de ff ff       	call   402130 <stat@plt>
  4042c1:	83 f8 ff             	cmp    $0xffffffff,%eax
  4042c4:	0f 85 31 ff ff ff    	jne    4041fb <handle_get_method+0x8b>
  4042ca:	4c 89 e1             	mov    %r12,%rcx
  4042cd:	4c 89 f2             	mov    %r14,%rdx
  4042d0:	48 8d 35 1f 1e 00 00 	lea    0x1e1f(%rip),%rsi        # 4060f6 <_IO_stdin_used+0xf6>
  4042d7:	31 c0                	xor    %eax,%eax
  4042d9:	bf 01 00 00 00       	mov    $0x1,%edi
  4042de:	e8 cd de ff ff       	call   4021b0 <__printf_chk@plt>
        handle_http_404(client_socket, ring);
  4042e3:	4c 89 ee             	mov    %r13,%rsi
  4042e6:	89 ef                	mov    %ebp,%edi
  4042e8:	e8 63 fe ff ff       	call   404150 <handle_http_404>
  4042ed:	e9 3d ff ff ff       	jmp    40422f <handle_get_method+0xbf>
  4042f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            struct Request *req = zh_malloc(sizeof(*req) + (sizeof(struct iovec) * 6));
  4042f8:	bf 70 00 00 00       	mov    $0x70,%edi
  4042fd:	e8 ce f5 ff ff       	call   4038d0 <zh_malloc>
            send_headers(final_path, path_stat.st_size, req->iov);
  404302:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
  404307:	4c 89 f7             	mov    %r14,%rdi
            req->client_socket = client_socket;
  40430a:	89 68 08             	mov    %ebp,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
  40430d:	48 8d 50 10          	lea    0x10(%rax),%rdx
            struct Request *req = zh_malloc(sizeof(*req) + (sizeof(struct iovec) * 6));
  404311:	49 89 c4             	mov    %rax,%r12
            req->iovec_count = 6;
  404314:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
  40431b:	e8 20 f6 ff ff       	call   403940 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
  404320:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
  404325:	49 8d 54 24 60       	lea    0x60(%r12),%rdx
  40432a:	4c 89 f7             	mov    %r14,%rdi
  40432d:	e8 7e fb ff ff       	call   403eb0 <copy_file_contents>
  404332:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
  404337:	4c 89 f2             	mov    %r14,%rdx
  40433a:	31 c0                	xor    %eax,%eax
  40433c:	48 8d 35 cb 1d 00 00 	lea    0x1dcb(%rip),%rsi        # 40610e <_IO_stdin_used+0x10e>
  404343:	bf 01 00 00 00       	mov    $0x1,%edi
  404348:	e8 63 de ff ff       	call   4021b0 <__printf_chk@plt>
            add_write_request(req, ring);
  40434d:	4c 89 ee             	mov    %r13,%rsi
  404350:	4c 89 e7             	mov    %r12,%rdi
  404353:	e8 f8 fb ff ff       	call   403f50 <add_write_request>
  404358:	e9 d2 fe ff ff       	jmp    40422f <handle_get_method+0xbf>
}
  40435d:	e8 2e dd ff ff       	call   402090 <__stack_chk_fail@plt>
  404362:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40436d:	0f 1f 00             	nopl   (%rax)

0000000000404370 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
  404370:	41 57                	push   %r15
  404372:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
  404374:	4c 8d 35 0a 1d 00 00 	lea    0x1d0a(%rip),%r14        # 406085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
  40437b:	41 55                	push   %r13
  40437d:	49 89 d5             	mov    %rdx,%r13
  404380:	41 54                	push   %r12
  404382:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
  404385:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
  404388:	55                   	push   %rbp
  404389:	48 83 ec 10          	sub    $0x10,%rsp
  40438d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  404396:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  40439b:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
  40439d:	49 89 e7             	mov    %rsp,%r15
  4043a0:	4c 89 fa             	mov    %r15,%rdx
  4043a3:	e8 38 dd ff ff       	call   4020e0 <strtok_r@plt>
    strtolower(method);
  4043a8:	48 89 c7             	mov    %rax,%rdi
    method = strtok_r(method_buffer, " ", &saveptr);
  4043ab:	48 89 c5             	mov    %rax,%rbp
    strtolower(method);
  4043ae:	e8 dd f4 ff ff       	call   403890 <strtolower>
    path = strtok_r(NULL, " ", &saveptr);
  4043b3:	4c 89 f6             	mov    %r14,%rsi
  4043b6:	31 ff                	xor    %edi,%edi
  4043b8:	4c 89 fa             	mov    %r15,%rdx
  4043bb:	e8 20 dd ff ff       	call   4020e0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
  4043c0:	48 8d 35 6c 1d 00 00 	lea    0x1d6c(%rip),%rsi        # 406133 <_IO_stdin_used+0x133>
  4043c7:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
  4043ca:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
  4043cd:	e8 3e dd ff ff       	call   402110 <strcmp@plt>
  4043d2:	85 c0                	test   %eax,%eax
  4043d4:	75 32                	jne    404408 <handle_http_method+0x98>
        handle_get_method(path, client_socket, ring);
  4043d6:	4c 89 ea             	mov    %r13,%rdx
  4043d9:	44 89 e6             	mov    %r12d,%esi
  4043dc:	4c 89 f7             	mov    %r14,%rdi
  4043df:	e8 8c fd ff ff       	call   404170 <handle_get_method>
}
  4043e4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  4043e9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4043f2:	75 21                	jne    404415 <handle_http_method+0xa5>
  4043f4:	48 83 c4 10          	add    $0x10,%rsp
  4043f8:	5d                   	pop    %rbp
  4043f9:	41 5c                	pop    %r12
  4043fb:	41 5d                	pop    %r13
  4043fd:	41 5e                	pop    %r14
  4043ff:	41 5f                	pop    %r15
  404401:	c3                   	ret
  404402:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        handle_unimplemented_method(client_socket, ring);
  404408:	4c 89 ee             	mov    %r13,%rsi
  40440b:	44 89 e7             	mov    %r12d,%edi
  40440e:	e8 1d fd ff ff       	call   404130 <handle_unimplemented_method>
}
  404413:	eb cf                	jmp    4043e4 <handle_http_method+0x74>
  404415:	e8 76 dc ff ff       	call   402090 <__stack_chk_fail@plt>
  40441a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000404420 <get_line>:
    for (int i = 0; i < dest_sz; i++) {
  404420:	85 d2                	test   %edx,%edx
  404422:	7e 3c                	jle    404460 <get_line+0x40>
  404424:	8d 42 ff             	lea    -0x1(%rdx),%eax
  404427:	48 83 c7 01          	add    $0x1,%rdi
  40442b:	48 8d 54 06 01       	lea    0x1(%rsi,%rax,1),%rdx
  404430:	eb 13                	jmp    404445 <get_line+0x25>
  404432:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  404438:	48 83 c6 01          	add    $0x1,%rsi
  40443c:	48 83 c7 01          	add    $0x1,%rdi
  404440:	48 39 d6             	cmp    %rdx,%rsi
  404443:	74 1b                	je     404460 <get_line+0x40>
        dest[i] = src[i];
  404445:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
  404449:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
  40444b:	3c 0d                	cmp    $0xd,%al
  40444d:	75 e9                	jne    404438 <get_line+0x18>
  40444f:	80 3f 0a             	cmpb   $0xa,(%rdi)
  404452:	75 e4                	jne    404438 <get_line+0x18>
            dest[i] = '\0';
  404454:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
  404457:	31 c0                	xor    %eax,%eax
}
  404459:	c3                   	ret
  40445a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
  404460:	b8 01 00 00 00       	mov    $0x1,%eax
  404465:	c3                   	ret
  404466:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000404470 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
  404470:	41 54                	push   %r12
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  404472:	ba 00 04 00 00       	mov    $0x400,%edx
int handle_client_request(struct Request *req, struct io_uring *ring) {
  404477:	49 89 f4             	mov    %rsi,%r12
  40447a:	55                   	push   %rbp
  40447b:	53                   	push   %rbx
  40447c:	48 89 fb             	mov    %rdi,%rbx
  40447f:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  404486:	48 8b 7f 10          	mov    0x10(%rdi),%rdi
int handle_client_request(struct Request *req, struct io_uring *ring) {
  40448a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  404493:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
  40449b:	31 c0                	xor    %eax,%eax
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  40449d:	48 89 e5             	mov    %rsp,%rbp
  4044a0:	48 89 ee             	mov    %rbp,%rsi
  4044a3:	e8 78 ff ff ff       	call   404420 <get_line>
  4044a8:	85 c0                	test   %eax,%eax
  4044aa:	75 2f                	jne    4044db <handle_client_request+0x6b>
    handle_http_method(http_request, req->client_socket, ring);
  4044ac:	8b 73 08             	mov    0x8(%rbx),%esi
  4044af:	4c 89 e2             	mov    %r12,%rdx
  4044b2:	48 89 ef             	mov    %rbp,%rdi
  4044b5:	e8 b6 fe ff ff       	call   404370 <handle_http_method>
}
  4044ba:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
  4044c2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4044cb:	75 38                	jne    404505 <handle_client_request+0x95>
  4044cd:	48 81 c4 10 04 00 00 	add    $0x410,%rsp
  4044d4:	31 c0                	xor    %eax,%eax
  4044d6:	5b                   	pop    %rbx
  4044d7:	5d                   	pop    %rbp
  4044d8:	41 5c                	pop    %r12
  4044da:	c3                   	ret
        fprintf(stderr, "Malformed request\n");
  4044db:	48 8b 05 16 4b 00 00 	mov    0x4b16(%rip),%rax        # 408ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  4044e2:	ba 12 00 00 00       	mov    $0x12,%edx
  4044e7:	be 01 00 00 00       	mov    $0x1,%esi
  4044ec:	48 8d 3d 44 1c 00 00 	lea    0x1c44(%rip),%rdi        # 406137 <_IO_stdin_used+0x137>
  4044f3:	48 8b 08             	mov    (%rax),%rcx
  4044f6:	e8 25 dd ff ff       	call   402220 <fwrite@plt>
        exit(1);
  4044fb:	bf 01 00 00 00       	mov    $0x1,%edi
  404500:	e8 fb dc ff ff       	call   402200 <exit@plt>
}
  404505:	e8 86 db ff ff       	call   402090 <__stack_chk_fail@plt>
  40450a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000404510 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
  404510:	55                   	push   %rbp
  404511:	66 48 0f 6e c2       	movq   %rdx,%xmm0
  404516:	66 48 0f 6e ce       	movq   %rsi,%xmm1
  40451b:	48 89 cd             	mov    %rcx,%rbp
  40451e:	53                   	push   %rbx
  40451f:	89 f8                	mov    %edi,%eax
  404521:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
  404525:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  404529:	48 8b 11             	mov    (%rcx),%rdx
  40452c:	8b 32                	mov    (%rdx),%esi
	unsigned int next = sq->sqe_tail + 1;
  40452e:	8b 59 44             	mov    0x44(%rcx),%ebx
	if (ring->flags & IORING_SETUP_SQE128)
  404531:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int next = sq->sqe_tail + 1;
  404537:	8d 53 01             	lea    0x1(%rbx),%edx
	if (next - head <= *sq->kring_entries) {
  40453a:	89 d7                	mov    %edx,%edi
  40453c:	29 f7                	sub    %esi,%edi
  40453e:	48 8b 75 18          	mov    0x18(%rbp),%rsi
  404542:	3b 3e                	cmp    (%rsi),%edi
  404544:	0f 87 70 dd ff ff    	ja     4022ba <add_accept_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40454a:	48 8b 75 10          	mov    0x10(%rbp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  40454e:	c1 e9 0a             	shr    $0xa,%ecx
  struct Request *req = malloc(sizeof(*req));
  404551:	bf 10 00 00 00       	mov    $0x10,%edi
  404556:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404559:	23 1e                	and    (%rsi),%ebx
		sq->sqe_tail = next;
  40455b:	89 55 44             	mov    %edx,0x44(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40455e:	d3 e3                	shl    %cl,%ebx
  404560:	48 c1 e3 06          	shl    $0x6,%rbx
  404564:	48 03 5d 38          	add    0x38(%rbp),%rbx
	sqe->opcode = (__u8) op;
  404568:	c7 03 0d 00 00 00    	movl   $0xd,(%rbx)
	sqe->fd = fd;
  40456e:	89 43 04             	mov    %eax,0x4(%rbx)
	sqe->buf_index = 0;
  404571:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->len = len;
  404579:	48 c7 43 18 00 00 00 00 	movq   $0x0,0x18(%rbx)
	sqe->off = offset;
  404581:	0f 11 43 08          	movups %xmm0,0x8(%rbx)
	sqe->addr3 = 0;
  404585:	66 0f ef c0          	pxor   %xmm0,%xmm0
  404589:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
  40458d:	e8 de db ff ff       	call   402170 <malloc@plt>
  io_uring_submit(ring);
  404592:	48 89 ef             	mov    %rbp,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
  404595:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
  40459b:	48 89 43 20          	mov    %rax,0x20(%rbx)
}
  40459f:	48 83 c4 08          	add    $0x8,%rsp
  4045a3:	5b                   	pop    %rbx
  4045a4:	5d                   	pop    %rbp
  io_uring_submit(ring);
  4045a5:	e9 f6 da ff ff       	jmp    4020a0 <io_uring_submit@plt>
  4045aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000004045b0 <io_thread>:
void* io_thread(void *arg) {
  4045b0:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  4045b2:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
  4045b4:	41 56                	push   %r14
  4045b6:	41 55                	push   %r13
  4045b8:	41 54                	push   %r12
  4045ba:	55                   	push   %rbp
  4045bb:	48 89 fd             	mov    %rdi,%rbp
  4045be:	53                   	push   %rbx
  4045bf:	48 81 ec 48 01 00 00 	sub    $0x148,%rsp
  struct io_uring ring = *data->ring;
  4045c6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4045cf:	48 89 84 24 38 01 00 00 	mov    %rax,0x138(%rsp)
  4045d7:	48 8b 47 40          	mov    0x40(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  4045db:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
  4045e0:	bf 00 01 00 00       	mov    $0x100,%edi
  4045e5:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
  4045e8:	f3 0f 6f 08          	movdqu (%rax),%xmm1
  4045ec:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
  4045f1:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
  4045f6:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
  4045fb:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
  404600:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
  404608:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
  40460d:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
  404615:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
  40461a:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
  404622:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
  404627:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
  40462f:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
  404634:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
  40463c:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
  404641:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
  404649:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
  404651:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
  404659:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
  404661:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
  404669:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
  404671:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
  404679:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
  404681:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
  404689:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
  404691:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
  404699:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
  4046a0:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  4046a8:	e8 a3 da ff ff       	call   402150 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
  4046ad:	48 8b 7d 40          	mov    0x40(%rbp),%rdi
  4046b1:	31 f6                	xor    %esi,%esi
  4046b3:	e8 88 db ff ff       	call   402240 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
  4046b8:	31 d2                	xor    %edx,%edx
  4046ba:	be 01 00 00 00       	mov    $0x1,%esi
  4046bf:	bf 02 00 00 00       	mov    $0x2,%edi
  4046c4:	e8 c7 db ff ff       	call   402290 <socket@plt>
  4046c9:	89 44 24 0c          	mov    %eax,0xc(%rsp)
  if (sock == -1)
  4046cd:	83 f8 ff             	cmp    $0xffffffff,%eax
  4046d0:	0f 84 09 05 00 00    	je     404bdf <io_thread+0x62f>
  if (setsockopt(sock,
  4046d6:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  4046da:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
  4046df:	41 b8 04 00 00 00    	mov    $0x4,%r8d
  4046e5:	ba 02 00 00 00       	mov    $0x2,%edx
  4046ea:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
  4046ef:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
  4046f7:	e8 64 d9 ff ff       	call   402060 <setsockopt@plt>
  4046fc:	85 c0                	test   %eax,%eax
  4046fe:	0f 88 ca 04 00 00    	js     404bce <io_thread+0x61e>
  if (bind(sock,
  404704:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  return __builtin___memset_chk (__dest, __ch, __len,
  404708:	66 0f ef c0          	pxor   %xmm0,%xmm0
  40470c:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  404711:	ba 10 00 00 00       	mov    $0x10,%edx
  404716:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  srv_addr.sin_family = AF_INET;
  40471b:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
  404723:	e8 98 da ff ff       	call   4021c0 <bind@plt>
  404728:	85 c0                	test   %eax,%eax
  40472a:	0f 88 8d 04 00 00    	js     404bbd <io_thread+0x60d>
  if (listen(sock, 10) < 0) {
  404730:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  404734:	be 0a 00 00 00       	mov    $0xa,%esi
  404739:	e8 42 da ff ff       	call   402180 <listen@plt>
  40473e:	85 c0                	test   %eax,%eax
  404740:	0f 88 66 04 00 00    	js     404bac <io_thread+0x5fc>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  404746:	ba db 18 00 00       	mov    $0x18db,%edx
  40474b:	48 8d 35 2a 1a 00 00 	lea    0x1a2a(%rip),%rsi        # 40617c <_IO_stdin_used+0x17c>
  404752:	bf 01 00 00 00       	mov    $0x1,%edi
  404757:	31 c0                	xor    %eax,%eax
  404759:	e8 52 da ff ff       	call   4021b0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  40475e:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
  404763:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  404767:	48 89 d9             	mov    %rbx,%rcx
  40476a:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
  40476f:	48 89 c6             	mov    %rax,%rsi
  404772:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  404777:	48 89 54 24 20       	mov    %rdx,0x20(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
  40477c:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  404784:	e8 87 fd ff ff       	call   404510 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
  404789:	be 10 00 00 00       	mov    $0x10,%esi
  40478e:	bf 01 00 00 00       	mov    $0x1,%edi
  404793:	e8 68 d9 ff ff       	call   402100 <calloc@plt>
  iov->iov_base = zh_malloc(10);
  404798:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
  40479d:	49 89 c6             	mov    %rax,%r14
  4047a0:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  iov->iov_base = zh_malloc(10);
  4047a5:	e8 26 f1 ff ff       	call   4038d0 <zh_malloc>
  iov->iov_len = 10;
  4047aa:	49 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%r14)
  iov->iov_base = zh_malloc(10);
  4047b2:	49 89 06             	mov    %rax,(%r14)
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  4047b5:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
  4047ba:	8b 30                	mov    (%rax),%esi
	unsigned int next = sq->sqe_tail + 1;
  4047bc:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  4047c3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  4047ca:	8d 50 01             	lea    0x1(%rax),%edx
	if (next - head <= *sq->kring_entries) {
  4047cd:	89 d7                	mov    %edx,%edi
  4047cf:	29 f7                	sub    %esi,%edi
  4047d1:	48 8b 74 24 78       	mov    0x78(%rsp),%rsi
  4047d6:	3b 3e                	cmp    (%rsi),%edi
  4047d8:	0f 87 e6 da ff ff    	ja     4022c4 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4047de:	48 8b 74 24 70       	mov    0x70(%rsp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  4047e3:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  4047e6:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
  4047ea:	48 89 df             	mov    %rbx,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
  4047ed:	83 e1 01             	and    $0x1,%ecx
  4047f0:	4c 8d 25 9b 19 00 00 	lea    0x199b(%rip),%r12        # 406192 <_IO_stdin_used+0x192>
  4047f7:	4c 8d 2d ba 19 00 00 	lea    0x19ba(%rip),%r13        # 4061b8 <_IO_stdin_used+0x1b8>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4047fe:	23 06                	and    (%rsi),%eax
		sq->sqe_tail = next;
  404800:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
  404807:	48 8d 75 48          	lea    0x48(%rbp),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
  40480b:	8b 55 48             	mov    0x48(%rbp),%edx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40480e:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
  404810:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
  404815:	48 c1 e0 06          	shl    $0x6,%rax
  404819:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
  404821:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
  404827:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
  40482a:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
  404832:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
  404836:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
  40483e:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  404846:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
  40484a:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
  40484e:	e8 4d d8 ff ff       	call   4020a0 <io_uring_submit@plt>
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
  404853:	48 8d 44 24 38       	lea    0x38(%rsp),%rax
  while (data->running == 1) {
  404858:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
  40485c:	48 89 04 24          	mov    %rax,(%rsp)
  404860:	0f 85 a6 01 00 00    	jne    404a0c <io_thread+0x45c>
  404866:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  404870:	4c 89 e7             	mov    %r12,%rdi
  404873:	e8 d8 d7 ff ff       	call   402050 <puts@plt>
	unsigned mask = *ring->cq.kring_mask;
  404878:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
	if (ring->flags & IORING_SETUP_CQE32)
  404880:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = *ring->cq.kring_mask;
  404887:	8b 30                	mov    (%rax),%esi
	if (ring->flags & IORING_SETUP_CQE32)
  404889:	c1 e9 0b             	shr    $0xb,%ecx
  40488c:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
  40488f:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
  404897:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
  404899:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
  4048a1:	8b 17                	mov    (%rdi),%edx
		if (!available)
  4048a3:	39 d0                	cmp    %edx,%eax
  4048a5:	74 39                	je     4048e0 <io_thread+0x330>
		cqe = &ring->cq.cqes[(head & mask) << shift];
  4048a7:	89 f0                	mov    %esi,%eax
  4048a9:	21 d0                	and    %edx,%eax
  4048ab:	d3 e0                	shl    %cl,%eax
  4048ad:	48 c1 e0 04          	shl    $0x4,%rax
  4048b1:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
  4048b9:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
  4048c1:	0f 85 81 01 00 00    	jne    404a48 <io_thread+0x498>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
  4048c7:	4c 8b 00             	mov    (%rax),%r8
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
  4048ca:	49 83 f8 ff          	cmp    $0xffffffffffffffff,%r8
  4048ce:	0f 85 9c 02 00 00    	jne    404b70 <io_thread+0x5c0>
			if (cqe->res < 0)
  4048d4:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  4048d7:	83 c2 01             	add    $0x1,%edx
  4048da:	89 17                	mov    %edx,(%rdi)
			if (!err)
  4048dc:	85 c0                	test   %eax,%eax
  4048de:	79 af                	jns    40488f <io_thread+0x2df>
	*cqe_ptr = cqe;
  4048e0:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
  4048e9:	48 8b 34 24          	mov    (%rsp),%rsi
  4048ed:	45 31 c0             	xor    %r8d,%r8d
  4048f0:	31 d2                	xor    %edx,%edx
  4048f2:	b9 01 00 00 00       	mov    $0x1,%ecx
  4048f7:	48 89 df             	mov    %rbx,%rdi
  4048fa:	e8 a1 d8 ff ff       	call   4021a0 <__io_uring_get_cqe@plt>
  4048ff:	41 89 c6             	mov    %eax,%r14d
      if (cqe->user_data == 1) {
  404902:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  404907:	48 83 38 01          	cmpq   $0x1,(%rax)
  40490b:	0f 84 8f 02 00 00    	je     404ba0 <io_thread+0x5f0>
  404911:	4c 89 ef             	mov    %r13,%rdi
  404914:	e8 37 d7 ff ff       	call   402050 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
  404919:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
  40491e:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
  404921:	45 85 f6             	test   %r14d,%r14d
  404924:	79 11                	jns    404937 <io_thread+0x387>
          fatal_error("io_uring_wait_cqe");
  404926:	48 8d 3d a2 18 00 00 	lea    0x18a2(%rip),%rdi        # 4061cf <_IO_stdin_used+0x1cf>
  40492d:	e8 3e ef ff ff       	call   403870 <fatal_error>
      if (cqe->res < 0) {
  404932:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
  404937:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
  40493a:	45 8b 07             	mov    (%r15),%r8d
      if (cqe->res < 0) {
  40493d:	85 c0                	test   %eax,%eax
  40493f:	0f 88 ab 02 00 00    	js     404bf0 <io_thread+0x640>
      switch (req->event_type) {
  404945:	41 83 f8 01          	cmp    $0x1,%r8d
  404949:	0f 84 31 01 00 00    	je     404a80 <io_thread+0x4d0>
  40494f:	41 83 f8 02          	cmp    $0x2,%r8d
  404953:	0f 84 9f 01 00 00    	je     404af8 <io_thread+0x548>
  404959:	45 85 c0             	test   %r8d,%r8d
  40495c:	0f 84 5e 01 00 00    	je     404ac0 <io_thread+0x510>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  404962:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  40496a:	8b 02                	mov    (%rdx),%eax
  40496c:	83 c0 01             	add    $0x1,%eax
  40496f:	89 02                	mov    %eax,(%rdx)
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  404971:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
  404976:	8b 30                	mov    (%rax),%esi
	unsigned int next = sq->sqe_tail + 1;
  404978:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  40497f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  404986:	8d 50 01             	lea    0x1(%rax),%edx
	if (next - head <= *sq->kring_entries) {
  404989:	89 d7                	mov    %edx,%edi
  40498b:	29 f7                	sub    %esi,%edi
  40498d:	48 8b 74 24 78       	mov    0x78(%rsp),%rsi
  404992:	3b 3e                	cmp    (%rsi),%edi
  404994:	0f 87 2a d9 ff ff    	ja     4022c4 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40499a:	48 8b 74 24 70       	mov    0x70(%rsp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  40499f:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  4049a2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
  4049a6:	48 89 df             	mov    %rbx,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
  4049a9:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4049ac:	23 06                	and    (%rsi),%eax
	sqe->addr = (unsigned long) addr;
  4049ae:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
		sq->sqe_tail = next;
  4049b3:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4049ba:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
  4049bc:	8b 55 48             	mov    0x48(%rbp),%edx
  4049bf:	48 c1 e0 06          	shl    $0x6,%rax
  4049c3:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->addr = (unsigned long) addr;
  4049cb:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->user_data = (unsigned long) data;
  4049cf:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
	sqe->opcode = (__u8) op;
  4049d4:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
  4049da:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
  4049dd:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->len = len;
  4049e5:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
  4049ed:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  4049f5:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
  4049f9:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
  4049fd:	e8 9e d6 ff ff       	call   4020a0 <io_uring_submit@plt>
  while (data->running == 1) {
  404a02:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
  404a06:	0f 84 64 fe ff ff    	je     404870 <io_thread+0x2c0>
  404a0c:	48 8d 3d de 17 00 00 	lea    0x17de(%rip),%rdi        # 4061f1 <_IO_stdin_used+0x1f1>
  404a13:	e8 38 d6 ff ff       	call   402050 <puts@plt>
}
  404a18:	48 8b 84 24 38 01 00 00 	mov    0x138(%rsp),%rax
  404a20:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  404a29:	0f 85 fc 01 00 00    	jne    404c2b <io_thread+0x67b>
  404a2f:	48 81 c4 48 01 00 00 	add    $0x148,%rsp
  404a36:	31 c0                	xor    %eax,%eax
  404a38:	5b                   	pop    %rbx
  404a39:	5d                   	pop    %rbp
  404a3a:	41 5c                	pop    %r12
  404a3c:	41 5d                	pop    %r13
  404a3e:	41 5e                	pop    %r14
  404a40:	41 5f                	pop    %r15
  404a42:	c3                   	ret
  404a43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
  404a48:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
  404a4d:	48 85 c0             	test   %rax,%rax
  404a50:	0f 84 93 fe ff ff    	je     4048e9 <io_thread+0x339>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
  404a56:	4c 8b 00             	mov    (%rax),%r8
      if (cqe->user_data == 1) {
  404a59:	49 83 f8 01          	cmp    $0x1,%r8
  404a5d:	0f 84 1d 01 00 00    	je     404b80 <io_thread+0x5d0>
  404a63:	4c 89 ef             	mov    %r13,%rdi
  404a66:	e8 e5 d5 ff ff       	call   402050 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
  404a6b:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
  404a70:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
  404a73:	e9 bf fe ff ff       	jmp    404937 <io_thread+0x387>
  404a78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
              if (!cqe->res) {
  404a80:	85 c0                	test   %eax,%eax
  404a82:	0f 85 b8 00 00 00    	jne    404b40 <io_thread+0x590>
                  fprintf(stderr, "Empty request!\n");
  404a88:	48 8b 05 69 45 00 00 	mov    0x4569(%rip),%rax        # 408ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  404a8f:	ba 0f 00 00 00       	mov    $0xf,%edx
  404a94:	be 01 00 00 00       	mov    $0x1,%esi
  404a99:	48 8d 3d 41 17 00 00 	lea    0x1741(%rip),%rdi        # 4061e1 <_IO_stdin_used+0x1e1>
  404aa0:	48 8b 08             	mov    (%rax),%rcx
  404aa3:	e8 78 d7 ff ff       	call   402220 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
  404aa8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  404aad:	0f 1f 00             	nopl   (%rax)
	if (cqe)
  404ab0:	48 85 c0             	test   %rax,%rax
  404ab3:	0f 84 b8 fe ff ff    	je     404971 <io_thread+0x3c1>
  404ab9:	e9 a4 fe ff ff       	jmp    404962 <io_thread+0x3b2>
  404abe:	66 90                	xchg   %ax,%ax
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  404ac0:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  404ac5:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  404aca:	48 89 d9             	mov    %rbx,%rcx
  404acd:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  404ad1:	e8 3a fa ff ff       	call   404510 <add_accept_request>
              add_read_request(cqe->res, &ring);
  404ad6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  404adb:	48 89 de             	mov    %rbx,%rsi
  404ade:	8b 78 08             	mov    0x8(%rax),%edi
  404ae1:	e8 0a f5 ff ff       	call   403ff0 <add_read_request>
              free(req);
  404ae6:	4c 89 ff             	mov    %r15,%rdi
  404ae9:	e8 42 d5 ff ff       	call   402030 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
  404aee:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
  404af3:	eb bb                	jmp    404ab0 <io_thread+0x500>
  404af5:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
  404af8:	41 8b 47 04          	mov    0x4(%r15),%eax
  404afc:	45 31 f6             	xor    %r14d,%r14d
  404aff:	85 c0                	test   %eax,%eax
  404b01:	7e 20                	jle    404b23 <io_thread+0x573>
  404b03:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  free(req->iov[i].iov_base);
  404b08:	49 63 c6             	movslq %r14d,%rax
              for (int i = 0; i < req->iovec_count; i++) {
  404b0b:	41 83 c6 01          	add    $0x1,%r14d
                  free(req->iov[i].iov_base);
  404b0f:	48 c1 e0 04          	shl    $0x4,%rax
  404b13:	4a 8b 7c 38 10       	mov    0x10(%rax,%r15,1),%rdi
  404b18:	e8 13 d5 ff ff       	call   402030 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
  404b1d:	45 39 77 04          	cmp    %r14d,0x4(%r15)
  404b21:	7f e5                	jg     404b08 <io_thread+0x558>
              close(req->client_socket);
  404b23:	41 8b 7f 08          	mov    0x8(%r15),%edi
  404b27:	e8 a4 d5 ff ff       	call   4020d0 <close@plt>
              free(req);
  404b2c:	4c 89 ff             	mov    %r15,%rdi
  404b2f:	e8 fc d4 ff ff       	call   402030 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
  404b34:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
  404b39:	e9 72 ff ff ff       	jmp    404ab0 <io_thread+0x500>
  404b3e:	66 90                	xchg   %ax,%ax
              handle_client_request(req, &ring);
  404b40:	48 89 de             	mov    %rbx,%rsi
  404b43:	4c 89 ff             	mov    %r15,%rdi
  404b46:	e8 25 f9 ff ff       	call   404470 <handle_client_request>
              free(req->iov[0].iov_base);
  404b4b:	49 8b 7f 10          	mov    0x10(%r15),%rdi
  404b4f:	e8 dc d4 ff ff       	call   402030 <free@plt>
              free(req);
  404b54:	4c 89 ff             	mov    %r15,%rdi
  404b57:	e8 d4 d4 ff ff       	call   402030 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
  404b5c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
  404b61:	e9 4a ff ff ff       	jmp    404ab0 <io_thread+0x500>
  404b66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
  404b70:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
      if (cqe->user_data == 1) {
  404b75:	49 83 f8 01          	cmp    $0x1,%r8
  404b79:	0f 85 e4 fe ff ff    	jne    404a63 <io_thread+0x4b3>
  404b7f:	90                   	nop
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  404b80:	83 c2 01             	add    $0x1,%edx
  404b83:	89 17                	mov    %edx,(%rdi)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  404b85:	48 8d 3d 18 16 00 00 	lea    0x1618(%rip),%rdi        # 4061a4 <_IO_stdin_used+0x1a4>
  404b8c:	e8 bf d4 ff ff       	call   402050 <puts@plt>
  404b91:	e9 76 fe ff ff       	jmp    404a0c <io_thread+0x45c>
  404b96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  404ba0:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
  404ba8:	8b 17                	mov    (%rdi),%edx
  404baa:	eb d4                	jmp    404b80 <io_thread+0x5d0>
    fatal_error("listen()");
  404bac:	48 8d 3d c0 15 00 00 	lea    0x15c0(%rip),%rdi        # 406173 <_IO_stdin_used+0x173>
  404bb3:	e8 b8 ec ff ff       	call   403870 <fatal_error>
  404bb8:	e9 89 fb ff ff       	jmp    404746 <io_thread+0x196>
      fatal_error("bind()");
  404bbd:	48 8d 3d a8 15 00 00 	lea    0x15a8(%rip),%rdi        # 40616c <_IO_stdin_used+0x16c>
  404bc4:	e8 a7 ec ff ff       	call   403870 <fatal_error>
  404bc9:	e9 62 fb ff ff       	jmp    404730 <io_thread+0x180>
      fatal_error("setsockopt(SO_REUSEADDR)");
  404bce:	48 8d 3d 7e 15 00 00 	lea    0x157e(%rip),%rdi        # 406153 <_IO_stdin_used+0x153>
  404bd5:	e8 96 ec ff ff       	call   403870 <fatal_error>
  404bda:	e9 25 fb ff ff       	jmp    404704 <io_thread+0x154>
      fatal_error("socket()");
  404bdf:	48 8d 3d 64 15 00 00 	lea    0x1564(%rip),%rdi        # 40614a <_IO_stdin_used+0x14a>
  404be6:	e8 85 ec ff ff       	call   403870 <fatal_error>
  404beb:	e9 e6 fa ff ff       	jmp    4046d6 <io_thread+0x126>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
  404bf0:	f7 d8                	neg    %eax
  404bf2:	44 89 04 24          	mov    %r8d,(%rsp)
  404bf6:	89 c7                	mov    %eax,%edi
  404bf8:	e8 63 d6 ff ff       	call   402260 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  404bfd:	44 8b 04 24          	mov    (%rsp),%r8d
  404c01:	be 01 00 00 00       	mov    $0x1,%esi
  404c06:	48 8d 15 43 18 00 00 	lea    0x1843(%rip),%rdx        # 406450 <_IO_stdin_used+0x450>
  404c0d:	48 89 c1             	mov    %rax,%rcx
  404c10:	48 8b 05 e1 43 00 00 	mov    0x43e1(%rip),%rax        # 408ff8 <stderr@GLIBC_2.2.5>
  404c17:	48 8b 38             	mov    (%rax),%rdi
  404c1a:	31 c0                	xor    %eax,%eax
  404c1c:	e8 0f d6 ff ff       	call   402230 <__fprintf_chk@plt>
          exit(1);
  404c21:	bf 01 00 00 00       	mov    $0x1,%edi
  404c26:	e8 d5 d5 ff ff       	call   402200 <exit@plt>
}
  404c2b:	e8 60 d4 ff ff       	call   402090 <__stack_chk_fail@plt>

0000000000404c30 <receive>:
  for (int n = 0 ; n < data->thread_count; n++) {
  404c30:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
  404c36:	85 c0                	test   %eax,%eax
  404c38:	0f 8e f8 00 00 00    	jle    404d36 <receive+0x106>
int receive(struct BarrierTask *data) {
  404c3e:	41 55                	push   %r13
  404c40:	83 e8 01             	sub    $0x1,%eax
  404c43:	48 89 fe             	mov    %rdi,%rsi
  404c46:	41 54                	push   %r12
  404c48:	48 c1 e0 05          	shl    $0x5,%rax
  404c4c:	55                   	push   %rbp
  404c4d:	53                   	push   %rbx
  404c4e:	48 83 ec 08          	sub    $0x8,%rsp
    struct Data *me = data->mailboxes[n].lower;
  404c52:	48 8b 97 28 02 00 00 	mov    0x228(%rdi),%rdx
  404c59:	4c 8d 42 18          	lea    0x18(%rdx),%r8
  404c5d:	4c 8d 6c 02 38       	lea    0x38(%rdx,%rax,1),%r13
  404c62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  404c68:	4d 8b 60 e8          	mov    -0x18(%r8),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
  404c6c:	4d 8b 9c 24 80 00 00 00 	mov    0x80(%r12),%r11
  404c74:	4d 85 db             	test   %r11,%r11
  404c77:	0f 8e 93 00 00 00    	jle    404d10 <receive+0xe0>
      data->sends++;
  404c7d:	48 8b be 30 02 00 00 	mov    0x230(%rsi),%rdi
      data->mailboxes[n].received++;
  404c84:	4d 8b 08             	mov    (%r8),%r9
    for (int x = 0 ; x < me->messages_count ; x++) {
  404c87:	31 c9                	xor    %ecx,%ecx
  404c89:	31 d2                	xor    %edx,%edx
      data->n++;
  404c8b:	4c 8b 96 08 01 00 00 	mov    0x108(%rsi),%r10
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
  404c92:	49 8b 2c 24          	mov    (%r12),%rbp
  404c96:	48 63 1e             	movslq (%rsi),%rbx
  404c99:	48 8d 47 01          	lea    0x1(%rdi),%rax
      data->mailboxes[n].received++;
  404c9d:	49 29 f9             	sub    %rdi,%r9
      data->n++;
  404ca0:	49 29 fa             	sub    %rdi,%r10
  404ca3:	eb 12                	jmp    404cb7 <receive+0x87>
  404ca5:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
  404ca8:	83 c1 01             	add    $0x1,%ecx
  404cab:	48 83 c0 01          	add    $0x1,%rax
  404caf:	48 63 d1             	movslq %ecx,%rdx
  404cb2:	4c 39 da             	cmp    %r11,%rdx
  404cb5:	7d 59                	jge    404d10 <receive+0xe0>
      data->n++;
  404cb7:	49 8d 3c 02          	lea    (%r10,%rax,1),%rdi
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
  404cbb:	48 8b 54 d5 00       	mov    0x0(%rbp,%rdx,8),%rdx
      data->sends++;
  404cc0:	48 89 86 30 02 00 00 	mov    %rax,0x230(%rsi)
      data->n++;
  404cc7:	48 89 be 08 01 00 00 	mov    %rdi,0x108(%rsi)
      data->mailboxes[n].received++;
  404cce:	49 8d 3c 01          	lea    (%r9,%rax,1),%rdi
  404cd2:	49 89 38             	mov    %rdi,(%r8)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
  404cd5:	48 39 5a 10          	cmp    %rbx,0x10(%rdx)
  404cd9:	75 cd                	jne    404ca8 <receive+0x78>
  404cdb:	48 63 be 30 01 00 00 	movslq 0x130(%rsi),%rdi
  404ce2:	48 39 7a 08          	cmp    %rdi,0x8(%rdx)
  404ce6:	75 c0                	jne    404ca8 <receive+0x78>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  404ce8:	bf 01 00 00 00       	mov    $0x1,%edi
  404ced:	b9 01 00 00 00       	mov    $0x1,%ecx
  404cf2:	ba 01 00 00 00       	mov    $0x1,%edx
  404cf7:	31 c0                	xor    %eax,%eax
  404cf9:	48 8d 35 78 17 00 00 	lea    0x1778(%rip),%rsi        # 406478 <_IO_stdin_used+0x478>
  404d00:	e8 ab d4 ff ff       	call   4021b0 <__printf_chk@plt>
        exit(1);
  404d05:	bf 01 00 00 00       	mov    $0x1,%edi
  404d0a:	e8 f1 d4 ff ff       	call   402200 <exit@plt>
  404d0f:	90                   	nop
    me->messages_count = 0;
  404d10:	49 c7 84 24 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%r12)
  for (int n = 0 ; n < data->thread_count; n++) {
  404d1c:	49 83 c0 20          	add    $0x20,%r8
  404d20:	4d 39 c5             	cmp    %r8,%r13
  404d23:	0f 85 3f ff ff ff    	jne    404c68 <receive+0x38>
}
  404d29:	48 83 c4 08          	add    $0x8,%rsp
  404d2d:	31 c0                	xor    %eax,%eax
  404d2f:	5b                   	pop    %rbx
  404d30:	5d                   	pop    %rbp
  404d31:	41 5c                	pop    %r12
  404d33:	41 5d                	pop    %r13
  404d35:	c3                   	ret
  404d36:	31 c0                	xor    %eax,%eax
  404d38:	c3                   	ret
  404d39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000404d40 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
  404d40:	41 57                	push   %r15
  404d42:	41 56                	push   %r14
  404d44:	41 55                	push   %r13
  404d46:	41 54                	push   %r12
  404d48:	55                   	push   %rbp
    while (data->scheduled == 1) {
  404d49:	48 8d af 00 02 00 00 	lea    0x200(%rdi),%rbp
int barriered_work(struct BarrierTask *data) {
  404d50:	53                   	push   %rbx
  404d51:	48 89 fb             	mov    %rdi,%rbx
  404d54:	48 83 ec 28          	sub    $0x28,%rsp
  if (data->thread_index == data->task_index) {
  404d58:	8b 07                	mov    (%rdi),%eax
  404d5a:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
  404d60:	0f 84 6a 01 00 00    	je     404ed0 <barriered_work+0x190>
    receive(data);
  404d66:	e8 c5 fe ff ff       	call   404c30 <receive>
    while (data->scheduled == 1) {
  404d6b:	eb 0e                	jmp    404d7b <barriered_work+0x3b>
  404d6d:	0f 1f 00             	nopl   (%rax)
      data->n++;
  404d70:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
  404d78:	0f ae f8             	sfence
    while (data->scheduled == 1) {
  404d7b:	8b 45 00             	mov    0x0(%rbp),%eax
  404d7e:	83 f8 01             	cmp    $0x1,%eax
  404d81:	74 ed                	je     404d70 <barriered_work+0x30>
    if (data->sending == 1) {
  404d83:	83 bb 38 02 00 00 01 	cmpl   $0x1,0x238(%rbx)
  404d8a:	74 14                	je     404da0 <barriered_work+0x60>
  asm volatile ("mfence" ::: "memory");
  404d8c:	0f ae f0             	mfence
}
  404d8f:	48 83 c4 28          	add    $0x28,%rsp
  404d93:	31 c0                	xor    %eax,%eax
  404d95:	5b                   	pop    %rbx
  404d96:	5d                   	pop    %rbp
  404d97:	41 5c                	pop    %r12
  404d99:	41 5d                	pop    %r13
  404d9b:	41 5e                	pop    %r14
  404d9d:	41 5f                	pop    %r15
  404d9f:	c3                   	ret
        for (int n = 0 ; n < data->thread_count; n++) {
  404da0:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
  404da6:	85 c0                	test   %eax,%eax
  404da8:	7e e2                	jle    404d8c <barriered_work+0x4c>
  404daa:	4c 63 f8             	movslq %eax,%r15
  404dad:	48 8d 83 40 02 00 00 	lea    0x240(%rbx),%rax
          if (n == data->thread_index) { continue; }
  404db4:	44 8b b3 30 01 00 00 	mov    0x130(%rbx),%r14d
  404dbb:	31 c9                	xor    %ecx,%ecx
  404dbd:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  404dc2:	48 8d 83 48 02 00 00 	lea    0x248(%rbx),%rax
  404dc9:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  404dce:	66 90                	xchg   %ax,%ax
  404dd0:	41 39 ce             	cmp    %ecx,%r14d
  404dd3:	0f 84 dc 00 00 00    	je     404eb5 <barriered_work+0x175>
          struct Data *them = data->mailboxes[n].higher;
  404dd9:	48 89 cf             	mov    %rcx,%rdi
  404ddc:	48 c1 e7 05          	shl    $0x5,%rdi
  404de0:	48 03 bb 28 02 00 00 	add    0x228(%rbx),%rdi
  404de7:	4c 8b 57 08          	mov    0x8(%rdi),%r10
          for (; them->messages_count < min;) {
  404deb:	49 8b 92 80 00 00 00 	mov    0x80(%r10),%rdx
  404df2:	4d 63 82 88 00 00 00 	movslq 0x88(%r10),%r8
  404df9:	4c 39 c2             	cmp    %r8,%rdx
  404dfc:	0f 8d b3 00 00 00    	jge    404eb5 <barriered_work+0x175>
            them->messages[them->messages_count++] = data->message; 
  404e02:	49 8b 32             	mov    (%r10),%rsi
  404e05:	4d 89 c1             	mov    %r8,%r9
  404e08:	4c 8b 9b 08 01 00 00 	mov    0x108(%rbx),%r11
  404e0f:	49 29 d1             	sub    %rdx,%r9
  404e12:	4c 8b 6f 10          	mov    0x10(%rdi),%r13
  404e16:	4a 8d 2c c6          	lea    (%rsi,%r8,8),%rbp
  404e1a:	48 39 6c 24 10       	cmp    %rbp,0x10(%rsp)
  404e1f:	48 8d 04 d6          	lea    (%rsi,%rdx,8),%rax
  404e23:	0f 93 44 24 0f       	setae  0xf(%rsp)
  404e28:	48 3b 44 24 18       	cmp    0x18(%rsp),%rax
  404e2d:	41 0f 93 c4          	setae  %r12b
  404e31:	44 0a 64 24 0f       	or     0xf(%rsp),%r12b
  404e36:	0f 84 0c 02 00 00    	je     405048 <barriered_work+0x308>
  404e3c:	4d 8d 61 ff          	lea    -0x1(%r9),%r12
  404e40:	49 83 fc 02          	cmp    $0x2,%r12
  404e44:	0f 86 fe 01 00 00    	jbe    405048 <barriered_work+0x308>
  404e4a:	4c 8b a3 40 02 00 00 	mov    0x240(%rbx),%r12
  404e51:	4c 89 cd             	mov    %r9,%rbp
  404e54:	48 d1 ed             	shr    %rbp
  404e57:	66 49 0f 6e c4       	movq   %r12,%xmm0
  404e5c:	48 c1 e5 04          	shl    $0x4,%rbp
  404e60:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
  404e64:	48 01 c5             	add    %rax,%rbp
  404e67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  404e70:	0f 11 00             	movups %xmm0,(%rax)
          for (; them->messages_count < min;) {
  404e73:	48 83 c0 10          	add    $0x10,%rax
  404e77:	48 39 e8             	cmp    %rbp,%rax
  404e7a:	75 f4                	jne    404e70 <barriered_work+0x130>
  404e7c:	4c 89 c8             	mov    %r9,%rax
  404e7f:	48 83 e0 fe          	and    $0xfffffffffffffffe,%rax
  404e83:	48 01 c2             	add    %rax,%rdx
  404e86:	49 39 c1             	cmp    %rax,%r9
  404e89:	74 0b                	je     404e96 <barriered_work+0x156>
            them->messages[them->messages_count++] = data->message; 
  404e8b:	4c 8b a3 40 02 00 00 	mov    0x240(%rbx),%r12
  404e92:	4c 89 24 d6          	mov    %r12,(%rsi,%rdx,8)
            data->n++;
  404e96:	4d 01 cb             	add    %r9,%r11
            data->mailboxes[n].sent++;
  404e99:	4b 8d 44 0d 00       	lea    0x0(%r13,%r9,1),%rax
            data->n++;
  404e9e:	4c 89 9b 08 01 00 00 	mov    %r11,0x108(%rbx)
            data->mailboxes[n].sent++;
  404ea5:	48 89 47 10          	mov    %rax,0x10(%rdi)
  404ea9:	4d 89 82 80 00 00 00 	mov    %r8,0x80(%r10)
  404eb0:	4e 89 64 c6 f8       	mov    %r12,-0x8(%rsi,%r8,8)
        for (int n = 0 ; n < data->thread_count; n++) {
  404eb5:	48 83 c1 01          	add    $0x1,%rcx
  404eb9:	4c 39 f9             	cmp    %r15,%rcx
  404ebc:	0f 85 0e ff ff ff    	jne    404dd0 <barriered_work+0x90>
  404ec2:	e9 c5 fe ff ff       	jmp    404d8c <barriered_work+0x4c>
  404ec7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      receive(data);
  404ed0:	e8 5b fd ff ff       	call   404c30 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
  404ed5:	8b 8b 34 01 00 00    	mov    0x134(%rbx),%ecx
        int t = data->task_index;
  404edb:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
  404edd:	85 c9                	test   %ecx,%ecx
  404edf:	0f 8e 95 00 00 00    	jle    404f7a <barriered_work+0x23a>
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
  404ee5:	48 63 d0             	movslq %eax,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
  404ee8:	83 c0 01             	add    $0x1,%eax
  404eeb:	41 89 cd             	mov    %ecx,%r13d
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
  404eee:	4c 8d 24 92          	lea    (%rdx,%rdx,4),%r12
              int next_task = abs((t + 1) % (data->thread_count));
  404ef2:	99                   	cltd
  404ef3:	f7 f9                	idiv   %ecx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
  404ef5:	49 c1 e4 07          	shl    $0x7,%r12
              int next_task = abs((t + 1) % (data->thread_count));
  404ef9:	89 d0                	mov    %edx,%eax
  404efb:	f7 d8                	neg    %eax
  404efd:	0f 48 c2             	cmovs  %edx,%eax
  404f00:	49 c1 e5 05          	shl    $0x5,%r13
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
  404f04:	45 31 c0             	xor    %r8d,%r8d
  404f07:	48 98                	cltq
  404f09:	4c 8d 0c 80          	lea    (%rax,%rax,4),%r9
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
  404f0d:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
  404f14:	49 c1 e1 07          	shl    $0x7,%r9
  404f18:	4c 8b 58 10          	mov    0x10(%rax),%r11
  404f1c:	8d 41 ff             	lea    -0x1(%rcx),%eax
  404f1f:	48 c1 e0 05          	shl    $0x5,%rax
  404f23:	49 83 c3 20          	add    $0x20,%r11
  404f27:	4c 8d 70 28          	lea    0x28(%rax),%r14
  404f2b:	4d 89 da             	mov    %r11,%r10
  404f2e:	66 90                	xchg   %ax,%ax
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
  404f30:	49 8b 02             	mov    (%r10),%rax
  404f33:	4c 89 da             	mov    %r11,%rdx
  404f36:	4a 8b bc 20 28 02 00 00 	mov    0x228(%rax,%r12,1),%rdi
  404f3e:	48 8d 47 08          	lea    0x8(%rdi),%rax
  404f42:	4c 01 f7             	add    %r14,%rdi
  404f45:	0f 1f 00             	nopl   (%rax)
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
  404f48:	48 8b 0a             	mov    (%rdx),%rcx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
  404f4b:	48 8b 30             	mov    (%rax),%rsi
          for (int b = 0; b < data->thread_count ; b++) {
  404f4e:	48 83 c0 20          	add    $0x20,%rax
  404f52:	48 81 c2 98 00 00 00 	add    $0x98,%rdx
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
  404f59:	4a 8b 8c 09 28 02 00 00 	mov    0x228(%rcx,%r9,1),%rcx
  404f61:	4a 89 34 01          	mov    %rsi,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
  404f65:	48 39 c7             	cmp    %rax,%rdi
  404f68:	75 de                	jne    404f48 <barriered_work+0x208>
        for (int y = 0; y < data->thread_count ; y++) {
  404f6a:	49 83 c0 20          	add    $0x20,%r8
  404f6e:	49 81 c2 98 00 00 00 	add    $0x98,%r10
  404f75:	4d 39 c5             	cmp    %r8,%r13
  404f78:	75 b6                	jne    404f30 <barriered_work+0x1f0>
      asm volatile ("mfence" ::: "memory");
  404f7a:	0f ae f0             	mfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
  404f7d:	48 8b b3 18 02 00 00 	mov    0x218(%rbx),%rsi
  404f84:	31 ff                	xor    %edi,%edi
  404f86:	48 c1 e6 05          	shl    $0x5,%rsi
  404f8a:	48 03 b3 08 02 00 00 	add    0x208(%rbx),%rsi
  404f91:	e8 da d0 ff ff       	call   402070 <clock_gettime@plt>
    int modcount = data->thread->protected_state->modcount + 1;
  404f96:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
  404f9d:	48 8b 40 30          	mov    0x30(%rax),%rax
  404fa1:	8b 70 10             	mov    0x10(%rax),%esi
  404fa4:	44 8d 66 01          	lea    0x1(%rsi),%r12d
    data->thread->protected_state->modcount = modcount;
  404fa8:	44 89 60 10          	mov    %r12d,0x10(%rax)
    while (data->scheduled == 1) {
  404fac:	eb 40                	jmp    404fee <barriered_work+0x2ae>
  404fae:	66 90                	xchg   %ax,%ax
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
  404fb0:	48 63 83 30 01 00 00 	movslq 0x130(%rbx),%rax
  404fb7:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
      data->n++;
  404fbe:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
  404fc6:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
  404fca:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
  404fce:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
  404fd2:	48 63 13             	movslq (%rbx),%rdx
  404fd5:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
  404fd9:	48 8d 3c 92          	lea    (%rdx,%rdx,4),%rdi
  404fdd:	48 c1 e7 07          	shl    $0x7,%rdi
  404fe1:	48 03 78 20          	add    0x20(%rax),%rdi
  404fe5:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
  404feb:	0f ae f8             	sfence
    while (data->scheduled == 1) {
  404fee:	8b 45 00             	mov    0x0(%rbp),%eax
  404ff1:	83 f8 01             	cmp    $0x1,%eax
  404ff4:	74 ba                	je     404fb0 <barriered_work+0x270>
    if (modcount != data->thread->protected_state->modcount) {
  404ff6:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
  404ffd:	48 8b 40 30          	mov    0x30(%rax),%rax
  405001:	44 39 60 10          	cmp    %r12d,0x10(%rax)
  405005:	75 5a                	jne    405061 <barriered_work+0x321>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
  405007:	48 8b b3 18 02 00 00 	mov    0x218(%rbx),%rsi
  40500e:	31 ff                	xor    %edi,%edi
  405010:	48 c1 e6 05          	shl    $0x5,%rsi
  405014:	48 03 b3 08 02 00 00 	add    0x208(%rbx),%rsi
  40501b:	48 83 c6 10          	add    $0x10,%rsi
  40501f:	e8 4c d0 ff ff       	call   402070 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
  405024:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
  40502b:	48 83 c0 01          	add    $0x1,%rax
  40502f:	48 99                	cqto
  405031:	48 f7 bb 10 02 00 00 	idivq  0x210(%rbx)
  405038:	48 89 93 18 02 00 00 	mov    %rdx,0x218(%rbx)
  40503f:	e9 48 fd ff ff       	jmp    404d8c <barriered_work+0x4c>
  405044:	0f 1f 40 00          	nopl   0x0(%rax)
            them->messages[them->messages_count++] = data->message; 
  405048:	4c 8b a3 40 02 00 00 	mov    0x240(%rbx),%r12
          for (; them->messages_count < min;) {
  40504f:	48 83 c0 08          	add    $0x8,%rax
            them->messages[them->messages_count++] = data->message; 
  405053:	4c 89 60 f8          	mov    %r12,-0x8(%rax)
          for (; them->messages_count < min;) {
  405057:	48 39 c5             	cmp    %rax,%rbp
  40505a:	75 ec                	jne    405048 <barriered_work+0x308>
  40505c:	e9 35 fe ff ff       	jmp    404e96 <barriered_work+0x156>
  405061:	48 8d 3d 9c 11 00 00 	lea    0x119c(%rip),%rdi        # 406204 <_IO_stdin_used+0x204>
  405068:	e8 e3 cf ff ff       	call   402050 <puts@plt>
  40506d:	eb 98                	jmp    405007 <barriered_work+0x2c7>
  40506f:	90                   	nop

0000000000405070 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
  405070:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
  405074:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  40507b:	48 8b 40 38          	mov    0x38(%rax),%rax
  40507f:	8b 10                	mov    (%rax),%edx
  405081:	85 d2                	test   %edx,%edx
  405083:	7e 37                	jle    4050bc <barriered_work_ingest+0x4c>
    if (data->thread->buffers->buffer[x].available == 1) {
  405085:	48 8b 48 08          	mov    0x8(%rax),%rcx
  405089:	83 ea 01             	sub    $0x1,%edx
  40508c:	48 c1 e2 04          	shl    $0x4,%rdx
  405090:	48 8d 41 08          	lea    0x8(%rcx),%rax
  405094:	48 8d 54 11 18       	lea    0x18(%rcx,%rdx,1),%rdx
  405099:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  4050a0:	83 38 01             	cmpl   $0x1,(%rax)
  4050a3:	75 0e                	jne    4050b3 <barriered_work_ingest+0x43>
      data->ingest_count++;
  4050a5:	48 83 87 20 02 00 00 01 	addq   $0x1,0x220(%rdi)
      data->thread->buffers->buffer[x].available = 0;
  4050ad:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
  4050b3:	48 83 c0 10          	add    $0x10,%rax
  4050b7:	48 39 d0             	cmp    %rdx,%rax
  4050ba:	75 e4                	jne    4050a0 <barriered_work_ingest+0x30>
  asm volatile ("mfence" ::: "memory");
  4050bc:	0f ae f0             	mfence
  barriered_work(data);
  4050bf:	e8 7c fc ff ff       	call   404d40 <barriered_work>
}
  4050c4:	31 c0                	xor    %eax,%eax
  4050c6:	48 83 c4 08          	add    $0x8,%rsp
  4050ca:	c3                   	ret
  4050cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000004050d0 <barriered_nulltask>:
}
  4050d0:	31 c0                	xor    %eax,%eax
  4050d2:	c3                   	ret
  4050d3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4050de:	66 90                	xchg   %ax,%ax

00000000004050e0 <barriered_steal>:
  4050e0:	31 c0                	xor    %eax,%eax
  4050e2:	c3                   	ret
  4050e3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4050ee:	66 90                	xchg   %ax,%ax

00000000004050f0 <after>:
  return left.tv_sec > right.tv_sec &&
  4050f0:	31 c0                	xor    %eax,%eax
  4050f2:	48 39 d7             	cmp    %rdx,%rdi
  4050f5:	7e 08                	jle    4050ff <after+0xf>
  4050f7:	31 c0                	xor    %eax,%eax
  4050f9:	48 39 ce             	cmp    %rcx,%rsi
  4050fc:	0f 9f c0             	setg   %al
}
  4050ff:	c3                   	ret

0000000000405100 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
  405100:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
  405105:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
  40510a:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
  40510c:	48 39 d7             	cmp    %rdx,%rdi
  40510f:	7f 18                	jg     405129 <within+0x29>
  405111:	4d 39 d8             	cmp    %r11,%r8
  405114:	0f 9e c2             	setle  %dl
  405117:	48 39 ce             	cmp    %rcx,%rsi
  40511a:	0f 9e c0             	setle  %al
  40511d:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
  40511f:	31 c0                	xor    %eax,%eax
  405121:	4d 39 d1             	cmp    %r10,%r9
  405124:	0f 9e c0             	setle  %al
    return 1;
  405127:	21 d0                	and    %edx,%eax
}
  405129:	c3                   	ret
  40512a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000405130 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
  405130:	48 83 ec 08          	sub    $0x8,%rsp
  if (after(left.start, right.start) && after(right.end, left.end)) {
  405134:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  405139:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
  40513e:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
  405143:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  405148:	e8 a3 ff ff ff       	call   4050f0 <after>
  40514d:	85 c0                	test   %eax,%eax
  40514f:	74 21                	je     405172 <overlap+0x42>
  405151:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  405156:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
  40515b:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
  405160:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
  405165:	e8 86 ff ff ff       	call   4050f0 <after>
  40516a:	85 c0                	test   %eax,%eax
  40516c:	0f 85 ae 00 00 00    	jne    405220 <overlap+0xf0>
  if (after(right.start, left.start) && after(left.end, right.end)) {
  405172:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
  405177:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
  40517c:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
  405181:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
  405186:	e8 65 ff ff ff       	call   4050f0 <after>
  40518b:	85 c0                	test   %eax,%eax
  40518d:	74 1d                	je     4051ac <overlap+0x7c>
  40518f:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
  405194:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
  405199:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
  40519e:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  4051a3:	e8 48 ff ff ff       	call   4050f0 <after>
  4051a8:	85 c0                	test   %eax,%eax
  4051aa:	75 74                	jne    405220 <overlap+0xf0>
  if (within(left.start, right.start, right.end, left.end) == 1) {
  4051ac:	ff 74 24 28          	push   0x28(%rsp)
  4051b0:	ff 74 24 28          	push   0x28(%rsp)
  4051b4:	4c 8b 44 24 50       	mov    0x50(%rsp),%r8
  4051b9:	4c 8b 4c 24 58       	mov    0x58(%rsp),%r9
  4051be:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
  4051c3:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
  4051c8:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
  4051cd:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  4051d2:	e8 29 ff ff ff       	call   405100 <within>
  4051d7:	5e                   	pop    %rsi
  4051d8:	5f                   	pop    %rdi
  4051d9:	83 f8 01             	cmp    $0x1,%eax
  4051dc:	74 42                	je     405220 <overlap+0xf0>
  if (within(right.start, left.start, left.end, right.end) == 1) {
  4051de:	ff 74 24 48          	push   0x48(%rsp)
  4051e2:	ff 74 24 48          	push   0x48(%rsp)
  4051e6:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
  4051eb:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
  4051f0:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  4051f5:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
  4051fa:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
  4051ff:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
  405204:	e8 f7 fe ff ff       	call   405100 <within>
  405209:	5a                   	pop    %rdx
  40520a:	59                   	pop    %rcx
  40520b:	83 f8 01             	cmp    $0x1,%eax
  40520e:	0f 94 c0             	sete   %al
}
  405211:	48 83 c4 08          	add    $0x8,%rsp
  if (within(right.start, left.start, left.end, right.end) == 1) {
  405215:	0f b6 c0             	movzbl %al,%eax
}
  405218:	c3                   	ret
  405219:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    return 1;
  405220:	b8 01 00 00 00       	mov    $0x1,%eax
}
  405225:	48 83 c4 08          	add    $0x8,%rsp
  405229:	c3                   	ret
  40522a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000405230 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
  405230:	41 57                	push   %r15
  405232:	48 89 f8             	mov    %rdi,%rax
  405235:	41 56                	push   %r14
  405237:	41 55                	push   %r13
  405239:	41 54                	push   %r12
  40523b:	55                   	push   %rbp
  40523c:	53                   	push   %rbx
  40523d:	48 83 ec 38          	sub    $0x38,%rsp
  405241:	89 74 24 2c          	mov    %esi,0x2c(%rsp)
  for (int x = 0 ; x < thread_count; x++) {
  405245:	85 f6                	test   %esi,%esi
  405247:	0f 8e 7f 02 00 00    	jle    4054cc <verify+0x29c>
  40524d:	48 83 c0 20          	add    $0x20,%rax
  405251:	c7 44 24 1c 00 00 00 00 	movl   $0x0,0x1c(%rsp)
  405259:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  40525e:	49 89 c7             	mov    %rax,%r15
    for (int z = 0 ; z < thread_count; z++) {
  405261:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
  405269:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
  40526e:	8b 7c 24 28          	mov    0x28(%rsp),%edi
      if (z != x)  {
  405272:	39 7c 24 1c          	cmp    %edi,0x1c(%rsp)
  405276:	0f 84 79 01 00 00    	je     4053f5 <verify+0x1c5>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
  40527c:	41 8b 57 08          	mov    0x8(%r15),%edx
  405280:	85 d2                	test   %edx,%edx
  405282:	0f 8e 6d 01 00 00    	jle    4053f5 <verify+0x1c5>
  405288:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
  405290:	8b 54 24 1c          	mov    0x1c(%rsp),%edx
  405294:	48 8d 35 79 0f 00 00 	lea    0xf79(%rip),%rsi        # 406214 <_IO_stdin_used+0x214>
  40529b:	bf 01 00 00 00       	mov    $0x1,%edi
  4052a0:	31 c0                	xor    %eax,%eax
  4052a2:	e8 09 cf ff ff       	call   4021b0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  4052a7:	41 8b 46 08          	mov    0x8(%r14),%eax
  4052ab:	85 c0                	test   %eax,%eax
  4052ad:	0f 8e 2f 01 00 00    	jle    4053e2 <verify+0x1b2>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
  4052b3:	48 63 44 24 18       	movslq 0x18(%rsp),%rax
  4052b8:	49 8b 0f             	mov    (%r15),%rcx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  4052bb:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
  4052c3:	48 8d 2c 80          	lea    (%rax,%rax,4),%rbp
  4052c7:	48 c1 e5 07          	shl    $0x7,%rbp
  4052cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4052d0:	48 63 44 24 14       	movslq 0x14(%rsp),%rax
  4052d5:	48 8b 8c 29 18 02 00 00 	mov    0x218(%rcx,%rbp,1),%rcx
  4052dd:	bf 01 00 00 00       	mov    $0x1,%edi
  4052e2:	48 8d 35 40 0f 00 00 	lea    0xf40(%rip),%rsi        # 406229 <_IO_stdin_used+0x229>
  4052e9:	4c 8d 24 80          	lea    (%rax,%rax,4),%r12
  4052ed:	49 8b 06             	mov    (%r14),%rax
  4052f0:	4c 89 e3             	mov    %r12,%rbx
  4052f3:	48 c1 e3 07          	shl    $0x7,%rbx
  4052f7:	48 8b 94 18 18 02 00 00 	mov    0x218(%rax,%rbx,1),%rdx
  4052ff:	31 c0                	xor    %eax,%eax
  405301:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  405306:	e8 a5 ce ff ff       	call   4021b0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  40530b:	49 8b 0f             	mov    (%r15),%rcx
  40530e:	48 8b 94 29 18 02 00 00 	mov    0x218(%rcx,%rbp,1),%rdx
  405316:	48 85 d2             	test   %rdx,%rdx
  405319:	0f 8e b0 00 00 00    	jle    4053cf <verify+0x19f>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  40531f:	49 8b 06             	mov    (%r14),%rax
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  405322:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  40532a:	48 8b b4 18 18 02 00 00 	mov    0x218(%rax,%rbx,1),%rsi
  405332:	48 01 d8             	add    %rbx,%rax
  405335:	0f 1f 00             	nopl   (%rax)
  405338:	48 85 f6             	test   %rsi,%rsi
  40533b:	0f 8e 4f 01 00 00    	jle    405490 <verify+0x260>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
  405341:	48 63 5c 24 10       	movslq 0x10(%rsp),%rbx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  405346:	45 31 ed             	xor    %r13d,%r13d
  405349:	31 d2                	xor    %edx,%edx
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
  40534b:	48 c1 e3 05          	shl    $0x5,%rbx
  40534f:	90                   	nop
  405350:	48 8b 80 08 02 00 00 	mov    0x208(%rax),%rax
  405357:	48 c1 e2 05          	shl    $0x5,%rdx
  40535b:	49 89 d4             	mov    %rdx,%r12
  40535e:	ff 74 10 18          	push   0x18(%rax,%rdx,1)
  405362:	ff 74 10 10          	push   0x10(%rax,%rdx,1)
  405366:	ff 74 10 08          	push   0x8(%rax,%rdx,1)
  40536a:	ff 34 10             	push   (%rax,%rdx,1)
  40536d:	48 8b 84 29 08 02 00 00 	mov    0x208(%rcx,%rbp,1),%rax
  405375:	ff 74 18 18          	push   0x18(%rax,%rbx,1)
  405379:	ff 74 18 10          	push   0x10(%rax,%rbx,1)
  40537d:	ff 74 18 08          	push   0x8(%rax,%rbx,1)
  405381:	ff 34 18             	push   (%rax,%rbx,1)
  405384:	e8 a7 fd ff ff       	call   405130 <overlap>
  405389:	48 83 c4 40          	add    $0x40,%rsp
  40538d:	83 f8 01             	cmp    $0x1,%eax
  405390:	0f 84 8a 00 00 00    	je     405420 <verify+0x1f0>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  405396:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  40539b:	49 03 06             	add    (%r14),%rax
  40539e:	41 83 c5 01          	add    $0x1,%r13d
  4053a2:	48 8b b0 18 02 00 00 	mov    0x218(%rax),%rsi
  4053a9:	49 63 d5             	movslq %r13d,%rdx
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  4053ac:	49 8b 0f             	mov    (%r15),%rcx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  4053af:	48 39 f2             	cmp    %rsi,%rdx
  4053b2:	7c 9c                	jl     405350 <verify+0x120>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  4053b4:	83 44 24 10 01       	addl   $0x1,0x10(%rsp)
  4053b9:	48 8b 94 29 18 02 00 00 	mov    0x218(%rcx,%rbp,1),%rdx
  4053c1:	48 63 7c 24 10       	movslq 0x10(%rsp),%rdi
  4053c6:	48 39 d7             	cmp    %rdx,%rdi
  4053c9:	0f 8c 69 ff ff ff    	jl     405338 <verify+0x108>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  4053cf:	83 44 24 14 01       	addl   $0x1,0x14(%rsp)
  4053d4:	8b 44 24 14          	mov    0x14(%rsp),%eax
  4053d8:	41 39 46 08          	cmp    %eax,0x8(%r14)
  4053dc:	0f 8f ee fe ff ff    	jg     4052d0 <verify+0xa0>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
  4053e2:	83 44 24 18 01       	addl   $0x1,0x18(%rsp)
  4053e7:	8b 44 24 18          	mov    0x18(%rsp),%eax
  4053eb:	41 39 47 08          	cmp    %eax,0x8(%r15)
  4053ef:	0f 8f 9b fe ff ff    	jg     405290 <verify+0x60>
    for (int z = 0 ; z < thread_count; z++) {
  4053f5:	8b 44 24 28          	mov    0x28(%rsp),%eax
  4053f9:	49 81 c6 98 00 00 00 	add    $0x98,%r14
  405400:	83 c0 01             	add    $0x1,%eax
  405403:	39 44 24 2c          	cmp    %eax,0x2c(%rsp)
  405407:	0f 84 d0 00 00 00    	je     4054dd <verify+0x2ad>
  40540d:	89 44 24 28          	mov    %eax,0x28(%rsp)
  405411:	89 c7                	mov    %eax,%edi
  405413:	e9 5a fe ff ff       	jmp    405272 <verify+0x42>
  405418:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
  405420:	49 8b 06             	mov    (%r14),%rax
  405423:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  405428:	41 83 c5 01          	add    $0x1,%r13d
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
  40542c:	4c 03 a4 38 08 02 00 00 	add    0x208(%rax,%rdi,1),%r12
  405434:	49 8b 07             	mov    (%r15),%rax
  405437:	bf 01 00 00 00       	mov    $0x1,%edi
  40543c:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
  405441:	4d 8b 4c 24 18       	mov    0x18(%r12),%r9
  405446:	48 8b b4 28 08 02 00 00 	mov    0x208(%rax,%rbp,1),%rsi
  40544e:	31 c0                	xor    %eax,%eax
  405450:	48 01 de             	add    %rbx,%rsi
  405453:	48 8b 16             	mov    (%rsi),%rdx
  405456:	4c 8b 46 08          	mov    0x8(%rsi),%r8
  40545a:	48 8d 35 3f 10 00 00 	lea    0x103f(%rip),%rsi        # 4064a0 <_IO_stdin_used+0x4a0>
  405461:	e8 4a cd ff ff       	call   4021b0 <__printf_chk@plt>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  405466:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  40546b:	49 03 06             	add    (%r14),%rax
  40546e:	49 63 d5             	movslq %r13d,%rdx
  405471:	48 8b b0 18 02 00 00 	mov    0x218(%rax),%rsi
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  405478:	49 8b 0f             	mov    (%r15),%rcx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  40547b:	48 39 d6             	cmp    %rdx,%rsi
  40547e:	0f 8f cc fe ff ff    	jg     405350 <verify+0x120>
  405484:	e9 2b ff ff ff       	jmp    4053b4 <verify+0x184>
  405489:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  405490:	44 8b 6c 24 10       	mov    0x10(%rsp),%r13d
  405495:	41 83 c5 01          	add    $0x1,%r13d
  405499:	49 63 c5             	movslq %r13d,%rax
  40549c:	48 39 d0             	cmp    %rdx,%rax
  40549f:	0f 8d 2a ff ff ff    	jge    4053cf <verify+0x19f>
  4054a5:	0f 1f 00             	nopl   (%rax)
  4054a8:	41 83 c5 01          	add    $0x1,%r13d
  4054ac:	49 63 c5             	movslq %r13d,%rax
  4054af:	48 39 c2             	cmp    %rax,%rdx
  4054b2:	7f f4                	jg     4054a8 <verify+0x278>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  4054b4:	83 44 24 14 01       	addl   $0x1,0x14(%rsp)
  4054b9:	8b 44 24 14          	mov    0x14(%rsp),%eax
  4054bd:	41 39 46 08          	cmp    %eax,0x8(%r14)
  4054c1:	0f 8f 09 fe ff ff    	jg     4052d0 <verify+0xa0>
  4054c7:	e9 16 ff ff ff       	jmp    4053e2 <verify+0x1b2>
}
  4054cc:	48 83 c4 38          	add    $0x38,%rsp
  4054d0:	31 c0                	xor    %eax,%eax
  4054d2:	5b                   	pop    %rbx
  4054d3:	5d                   	pop    %rbp
  4054d4:	41 5c                	pop    %r12
  4054d6:	41 5d                	pop    %r13
  4054d8:	41 5e                	pop    %r14
  4054da:	41 5f                	pop    %r15
  4054dc:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
  4054dd:	8b 7c 24 1c          	mov    0x1c(%rsp),%edi
  4054e1:	49 81 c7 98 00 00 00 	add    $0x98,%r15
  4054e8:	8d 47 01             	lea    0x1(%rdi),%eax
  4054eb:	3b 7c 24 28          	cmp    0x28(%rsp),%edi
  4054ef:	74 db                	je     4054cc <verify+0x29c>
  4054f1:	89 44 24 1c          	mov    %eax,0x1c(%rsp)
  4054f5:	e9 67 fd ff ff       	jmp    405261 <verify+0x31>

Disassembly of section .fini:

00000000004054fc <_fini>:
  4054fc:	f3 0f 1e fa          	endbr64
  405500:	48 83 ec 08          	sub    $0x8,%rsp
  405504:	48 83 c4 08          	add    $0x8,%rsp
  405508:	c3                   	ret
