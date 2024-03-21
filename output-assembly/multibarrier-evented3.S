
multibarrier-evented3:     file format elf64-x86-64


Disassembly of section .init:

0000000000402000 <_init>:
  402000:	f3 0f 1e fa          	endbr64
  402004:	48 83 ec 08          	sub    $0x8,%rsp
  402008:	48 8b 05 d9 7f 00 00 	mov    0x7fd9(%rip),%rax        # 409fe8 <__gmon_start__@Base>
  40200f:	48 85 c0             	test   %rax,%rax
  402012:	74 02                	je     402016 <_init+0x16>
  402014:	ff d0                	call   *%rax
  402016:	48 83 c4 08          	add    $0x8,%rsp
  40201a:	c3                   	ret

Disassembly of section .plt:

0000000000402020 <free@plt-0x10>:
  402020:	ff 35 42 7e 00 00    	push   0x7e42(%rip)        # 409e68 <_GLOBAL_OFFSET_TABLE_+0x8>
  402026:	ff 25 44 7e 00 00    	jmp    *0x7e44(%rip)        # 409e70 <_GLOBAL_OFFSET_TABLE_+0x10>
  40202c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000402030 <free@plt>:
  402030:	ff 25 42 7e 00 00    	jmp    *0x7e42(%rip)        # 409e78 <free@GLIBC_2.2.5>
  402036:	68 00 00 00 00       	push   $0x0
  40203b:	e9 e0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402040 <putchar@plt>:
  402040:	ff 25 3a 7e 00 00    	jmp    *0x7e3a(%rip)        # 409e80 <putchar@GLIBC_2.2.5>
  402046:	68 01 00 00 00       	push   $0x1
  40204b:	e9 d0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402050 <pthread_setaffinity_np@plt>:
  402050:	ff 25 32 7e 00 00    	jmp    *0x7e32(%rip)        # 409e88 <pthread_setaffinity_np@GLIBC_2.34>
  402056:	68 02 00 00 00       	push   $0x2
  40205b:	e9 c0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402060 <puts@plt>:
  402060:	ff 25 2a 7e 00 00    	jmp    *0x7e2a(%rip)        # 409e90 <puts@GLIBC_2.2.5>
  402066:	68 03 00 00 00       	push   $0x3
  40206b:	e9 b0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402070 <setsockopt@plt>:
  402070:	ff 25 22 7e 00 00    	jmp    *0x7e22(%rip)        # 409e98 <setsockopt@GLIBC_2.2.5>
  402076:	68 04 00 00 00       	push   $0x4
  40207b:	e9 a0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402080 <clock_gettime@plt>:
  402080:	ff 25 1a 7e 00 00    	jmp    *0x7e1a(%rip)        # 409ea0 <clock_gettime@GLIBC_2.17>
  402086:	68 05 00 00 00       	push   $0x5
  40208b:	e9 90 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402090 <fclose@plt>:
  402090:	ff 25 12 7e 00 00    	jmp    *0x7e12(%rip)        # 409ea8 <fclose@GLIBC_2.2.5>
  402096:	68 06 00 00 00       	push   $0x6
  40209b:	e9 80 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020a0 <strlen@plt>:
  4020a0:	ff 25 0a 7e 00 00    	jmp    *0x7e0a(%rip)        # 409eb0 <strlen@GLIBC_2.2.5>
  4020a6:	68 07 00 00 00       	push   $0x7
  4020ab:	e9 70 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020b0 <__stack_chk_fail@plt>:
  4020b0:	ff 25 02 7e 00 00    	jmp    *0x7e02(%rip)        # 409eb8 <__stack_chk_fail@GLIBC_2.4>
  4020b6:	68 08 00 00 00       	push   $0x8
  4020bb:	e9 60 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020c0 <io_uring_submit@plt>:
  4020c0:	ff 25 fa 7d 00 00    	jmp    *0x7dfa(%rip)        # 409ec0 <io_uring_submit@LIBURING_2.0>
  4020c6:	68 09 00 00 00       	push   $0x9
  4020cb:	e9 50 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020d0 <nanosleep@plt>:
  4020d0:	ff 25 f2 7d 00 00    	jmp    *0x7df2(%rip)        # 409ec8 <nanosleep@GLIBC_2.2.5>
  4020d6:	68 0a 00 00 00       	push   $0xa
  4020db:	e9 40 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020e0 <strrchr@plt>:
  4020e0:	ff 25 ea 7d 00 00    	jmp    *0x7dea(%rip)        # 409ed0 <strrchr@GLIBC_2.2.5>
  4020e6:	68 0b 00 00 00       	push   $0xb
  4020eb:	e9 30 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020f0 <fputs@plt>:
  4020f0:	ff 25 e2 7d 00 00    	jmp    *0x7de2(%rip)        # 409ed8 <fputs@GLIBC_2.2.5>
  4020f6:	68 0c 00 00 00       	push   $0xc
  4020fb:	e9 20 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402100 <close@plt>:
  402100:	ff 25 da 7d 00 00    	jmp    *0x7dda(%rip)        # 409ee0 <close@GLIBC_2.2.5>
  402106:	68 0d 00 00 00       	push   $0xd
  40210b:	e9 10 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402110 <strtok_r@plt>:
  402110:	ff 25 d2 7d 00 00    	jmp    *0x7dd2(%rip)        # 409ee8 <strtok_r@GLIBC_2.2.5>
  402116:	68 0e 00 00 00       	push   $0xe
  40211b:	e9 00 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402120 <read@plt>:
  402120:	ff 25 ca 7d 00 00    	jmp    *0x7dca(%rip)        # 409ef0 <read@GLIBC_2.2.5>
  402126:	68 0f 00 00 00       	push   $0xf
  40212b:	e9 f0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402130 <calloc@plt>:
  402130:	ff 25 c2 7d 00 00    	jmp    *0x7dc2(%rip)        # 409ef8 <calloc@GLIBC_2.2.5>
  402136:	68 10 00 00 00       	push   $0x10
  40213b:	e9 e0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402140 <strcmp@plt>:
  402140:	ff 25 ba 7d 00 00    	jmp    *0x7dba(%rip)        # 409f00 <strcmp@GLIBC_2.2.5>
  402146:	68 11 00 00 00       	push   $0x11
  40214b:	e9 d0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402150 <__memcpy_chk@plt>:
  402150:	ff 25 b2 7d 00 00    	jmp    *0x7db2(%rip)        # 409f08 <__memcpy_chk@GLIBC_2.3.4>
  402156:	68 12 00 00 00       	push   $0x12
  40215b:	e9 c0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402160 <stat@plt>:
  402160:	ff 25 aa 7d 00 00    	jmp    *0x7daa(%rip)        # 409f10 <stat@GLIBC_2.33>
  402166:	68 13 00 00 00       	push   $0x13
  40216b:	e9 b0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402170 <memcpy@plt>:
  402170:	ff 25 a2 7d 00 00    	jmp    *0x7da2(%rip)        # 409f18 <memcpy@GLIBC_2.14>
  402176:	68 14 00 00 00       	push   $0x14
  40217b:	e9 a0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402180 <io_uring_queue_init@plt>:
  402180:	ff 25 9a 7d 00 00    	jmp    *0x7d9a(%rip)        # 409f20 <io_uring_queue_init@LIBURING_2.0>
  402186:	68 15 00 00 00       	push   $0x15
  40218b:	e9 90 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402190 <eventfd_write@plt>:
  402190:	ff 25 92 7d 00 00    	jmp    *0x7d92(%rip)        # 409f28 <eventfd_write@GLIBC_2.7>
  402196:	68 16 00 00 00       	push   $0x16
  40219b:	e9 80 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021a0 <malloc@plt>:
  4021a0:	ff 25 8a 7d 00 00    	jmp    *0x7d8a(%rip)        # 409f30 <malloc@GLIBC_2.2.5>
  4021a6:	68 17 00 00 00       	push   $0x17
  4021ab:	e9 70 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021b0 <listen@plt>:
  4021b0:	ff 25 82 7d 00 00    	jmp    *0x7d82(%rip)        # 409f38 <listen@GLIBC_2.2.5>
  4021b6:	68 18 00 00 00       	push   $0x18
  4021bb:	e9 60 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021c0 <__strcpy_chk@plt>:
  4021c0:	ff 25 7a 7d 00 00    	jmp    *0x7d7a(%rip)        # 409f40 <__strcpy_chk@GLIBC_2.3.4>
  4021c6:	68 19 00 00 00       	push   $0x19
  4021cb:	e9 50 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021d0 <__io_uring_get_cqe@plt>:
  4021d0:	ff 25 72 7d 00 00    	jmp    *0x7d72(%rip)        # 409f48 <__io_uring_get_cqe@LIBURING_2.0>
  4021d6:	68 1a 00 00 00       	push   $0x1a
  4021db:	e9 40 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021e0 <__printf_chk@plt>:
  4021e0:	ff 25 6a 7d 00 00    	jmp    *0x7d6a(%rip)        # 409f50 <__printf_chk@GLIBC_2.3.4>
  4021e6:	68 1b 00 00 00       	push   $0x1b
  4021eb:	e9 30 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021f0 <bind@plt>:
  4021f0:	ff 25 62 7d 00 00    	jmp    *0x7d62(%rip)        # 409f58 <bind@GLIBC_2.2.5>
  4021f6:	68 1c 00 00 00       	push   $0x1c
  4021fb:	e9 20 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402200 <pthread_create@plt>:
  402200:	ff 25 5a 7d 00 00    	jmp    *0x7d5a(%rip)        # 409f60 <pthread_create@GLIBC_2.34>
  402206:	68 1d 00 00 00       	push   $0x1d
  40220b:	e9 10 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402210 <open@plt>:
  402210:	ff 25 52 7d 00 00    	jmp    *0x7d52(%rip)        # 409f68 <open@GLIBC_2.2.5>
  402216:	68 1e 00 00 00       	push   $0x1e
  40221b:	e9 00 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402220 <fopen@plt>:
  402220:	ff 25 4a 7d 00 00    	jmp    *0x7d4a(%rip)        # 409f70 <fopen@GLIBC_2.2.5>
  402226:	68 1f 00 00 00       	push   $0x1f
  40222b:	e9 f0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402230 <perror@plt>:
  402230:	ff 25 42 7d 00 00    	jmp    *0x7d42(%rip)        # 409f78 <perror@GLIBC_2.2.5>
  402236:	68 20 00 00 00       	push   $0x20
  40223b:	e9 e0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402240 <exit@plt>:
  402240:	ff 25 3a 7d 00 00    	jmp    *0x7d3a(%rip)        # 409f80 <exit@GLIBC_2.2.5>
  402246:	68 21 00 00 00       	push   $0x21
  40224b:	e9 d0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402250 <eventfd@plt>:
  402250:	ff 25 32 7d 00 00    	jmp    *0x7d32(%rip)        # 409f88 <eventfd@GLIBC_2.7>
  402256:	68 22 00 00 00       	push   $0x22
  40225b:	e9 c0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402260 <fwrite@plt>:
  402260:	ff 25 2a 7d 00 00    	jmp    *0x7d2a(%rip)        # 409f90 <fwrite@GLIBC_2.2.5>
  402266:	68 23 00 00 00       	push   $0x23
  40226b:	e9 b0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402270 <__fprintf_chk@plt>:
  402270:	ff 25 22 7d 00 00    	jmp    *0x7d22(%rip)        # 409f98 <__fprintf_chk@GLIBC_2.3.4>
  402276:	68 24 00 00 00       	push   $0x24
  40227b:	e9 a0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402280 <io_uring_register_eventfd@plt>:
  402280:	ff 25 1a 7d 00 00    	jmp    *0x7d1a(%rip)        # 409fa0 <io_uring_register_eventfd@LIBURING_2.0>
  402286:	68 25 00 00 00       	push   $0x25
  40228b:	e9 90 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402290 <pthread_join@plt>:
  402290:	ff 25 12 7d 00 00    	jmp    *0x7d12(%rip)        # 409fa8 <pthread_join@GLIBC_2.34>
  402296:	68 26 00 00 00       	push   $0x26
  40229b:	e9 80 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022a0 <strerror@plt>:
  4022a0:	ff 25 0a 7d 00 00    	jmp    *0x7d0a(%rip)        # 409fb0 <strerror@GLIBC_2.2.5>
  4022a6:	68 27 00 00 00       	push   $0x27
  4022ab:	e9 70 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022b0 <pthread_mutex_init@plt>:
  4022b0:	ff 25 02 7d 00 00    	jmp    *0x7d02(%rip)        # 409fb8 <pthread_mutex_init@GLIBC_2.2.5>
  4022b6:	68 28 00 00 00       	push   $0x28
  4022bb:	e9 60 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022c0 <__ctype_tolower_loc@plt>:
  4022c0:	ff 25 fa 7c 00 00    	jmp    *0x7cfa(%rip)        # 409fc0 <__ctype_tolower_loc@GLIBC_2.3>
  4022c6:	68 29 00 00 00       	push   $0x29
  4022cb:	e9 50 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022d0 <__sprintf_chk@plt>:
  4022d0:	ff 25 f2 7c 00 00    	jmp    *0x7cf2(%rip)        # 409fc8 <__sprintf_chk@GLIBC_2.3.4>
  4022d6:	68 2a 00 00 00       	push   $0x2a
  4022db:	e9 40 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022e0 <socket@plt>:
  4022e0:	ff 25 ea 7c 00 00    	jmp    *0x7cea(%rip)        # 409fd0 <socket@GLIBC_2.2.5>
  4022e6:	68 2b 00 00 00       	push   $0x2b
  4022eb:	e9 30 fd ff ff       	jmp    402020 <_init+0x20>

Disassembly of section .text:

00000000004022f0 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
  4022f0:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

static inline void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
  4022f6:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  4022fe:	0f 0b                	ud2

0000000000402300 <add_read_request.cold>:
  402300:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  402308:	0f 0b                	ud2

000000000040230a <add_accept_request.cold>:
  40230a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  402312:	0f 0b                	ud2

0000000000402314 <io_thread.cold>:
  402314:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  40231c:	0f 0b                	ud2
  40231e:	66 90                	xchg   %ax,%ax

0000000000402320 <main>:
    }


  return 0;
}
int main() {
  402320:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  402322:	48 8d 3d 37 53 00 00 	lea    0x5337(%rip),%rdi        # 407660 <_IO_stdin_used+0x660>
  402329:	41 56                	push   %r14
  40232b:	41 55                	push   %r13
  40232d:	4c 8d 2d 48 50 00 00 	lea    0x5048(%rip),%r13        # 40737c <_IO_stdin_used+0x37c>
  402334:	41 54                	push   %r12
  402336:	55                   	push   %rbp
  402337:	53                   	push   %rbx
  402338:	48 81 ec f8 00 00 00 	sub    $0xf8,%rsp
  40233f:	f3 0f 7e 2d a9 7c 00 00 	movq   0x7ca9(%rip),%xmm5        # 409ff0 <_GLOBAL_OFFSET_TABLE_+0x190>
  402347:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  402350:	48 89 84 24 e8 00 00 00 	mov    %rax,0xe8(%rsp)
  402358:	31 c0                	xor    %eax,%eax
  40235a:	0f 16 2d 7f 7c 00 00 	movhps 0x7c7f(%rip),%xmm5        # 409fe0 <_GLOBAL_OFFSET_TABLE_+0x180>
  402361:	0f 29 ac 24 c0 00 00 00 	movaps %xmm5,0xc0(%rsp)
  402369:	e8 f2 fc ff ff       	call   402060 <puts@plt>
  40236e:	bf 0a 00 00 00       	mov    $0xa,%edi
  402373:	e8 c8 fc ff ff       	call   402040 <putchar@plt>
  402378:	ba 01 00 00 00       	mov    $0x1,%edx
  40237d:	48 8d 35 f0 4e 00 00 	lea    0x4ef0(%rip),%rsi        # 407274 <_IO_stdin_used+0x274>
  402384:	31 c0                	xor    %eax,%eax
  402386:	bf 01 00 00 00       	mov    $0x1,%edi
  40238b:	e8 50 fe ff ff       	call   4021e0 <__printf_chk@plt>
  402390:	ba 06 00 00 00       	mov    $0x6,%edx
  402395:	48 8d 35 e8 4e 00 00 	lea    0x4ee8(%rip),%rsi        # 407284 <_IO_stdin_used+0x284>
  40239c:	31 c0                	xor    %eax,%eax
  40239e:	bf 01 00 00 00       	mov    $0x1,%edi
  4023a3:	e8 38 fe ff ff       	call   4021e0 <__printf_chk@plt>
  4023a8:	ba 03 00 00 00       	mov    $0x3,%edx
  4023ad:	48 8d 35 e5 4e 00 00 	lea    0x4ee5(%rip),%rsi        # 407299 <_IO_stdin_used+0x299>
  4023b4:	31 c0                	xor    %eax,%eax
  4023b6:	bf 01 00 00 00       	mov    $0x1,%edi
  4023bb:	e8 20 fe ff ff       	call   4021e0 <__printf_chk@plt>
  4023c0:	ba 02 00 00 00       	mov    $0x2,%edx
  4023c5:	48 8d 35 dd 4e 00 00 	lea    0x4edd(%rip),%rsi        # 4072a9 <_IO_stdin_used+0x2a9>
  4023cc:	31 c0                	xor    %eax,%eax
  4023ce:	bf 01 00 00 00       	mov    $0x1,%edi
  4023d3:	e8 08 fe ff ff       	call   4021e0 <__printf_chk@plt>
  4023d8:	48 8d 3d e0 4e 00 00 	lea    0x4ee0(%rip),%rdi        # 4072bf <_IO_stdin_used+0x2bf>
  4023df:	e8 7c fc ff ff       	call   402060 <puts@plt>
  4023e4:	ba 02 00 00 00       	mov    $0x2,%edx
  4023e9:	48 8d 35 eb 4e 00 00 	lea    0x4eeb(%rip),%rsi        # 4072db <_IO_stdin_used+0x2db>
  4023f0:	31 c0                	xor    %eax,%eax
  4023f2:	bf 01 00 00 00       	mov    $0x1,%edi
  4023f7:	e8 e4 fd ff ff       	call   4021e0 <__printf_chk@plt>
  4023fc:	ba 0a 00 00 00       	mov    $0xa,%edx
  402401:	48 8d 35 ed 4e 00 00 	lea    0x4eed(%rip),%rsi        # 4072f5 <_IO_stdin_used+0x2f5>
  402408:	31 c0                	xor    %eax,%eax
  40240a:	bf 01 00 00 00       	mov    $0x1,%edi
  40240f:	e8 cc fd ff ff       	call   4021e0 <__printf_chk@plt>
  402414:	ba 01 00 00 00       	mov    $0x1,%edx
  402419:	48 8d 35 e9 4e 00 00 	lea    0x4ee9(%rip),%rsi        # 407309 <_IO_stdin_used+0x309>
  402420:	31 c0                	xor    %eax,%eax
  402422:	bf 01 00 00 00       	mov    $0x1,%edi
  402427:	e8 b4 fd ff ff       	call   4021e0 <__printf_chk@plt>
  40242c:	ba 01 00 00 00       	mov    $0x1,%edx
  402431:	48 8d 35 e2 4e 00 00 	lea    0x4ee2(%rip),%rsi        # 40731a <_IO_stdin_used+0x31a>
  402438:	31 c0                	xor    %eax,%eax
  40243a:	bf 01 00 00 00       	mov    $0x1,%edi
  40243f:	e8 9c fd ff ff       	call   4021e0 <__printf_chk@plt>
  402444:	ba 02 00 00 00       	mov    $0x2,%edx
  402449:	48 8d 35 e2 4e 00 00 	lea    0x4ee2(%rip),%rsi        # 407332 <_IO_stdin_used+0x332>
  402450:	31 c0                	xor    %eax,%eax
  402452:	bf 01 00 00 00       	mov    $0x1,%edi
  402457:	e8 84 fd ff ff       	call   4021e0 <__printf_chk@plt>
  40245c:	ba 01 00 00 00       	mov    $0x1,%edx
  402461:	48 8d 35 60 52 00 00 	lea    0x5260(%rip),%rsi        # 4076c8 <_IO_stdin_used+0x6c8>
  402468:	31 c0                	xor    %eax,%eax
  40246a:	bf 01 00 00 00       	mov    $0x1,%edi
  40246f:	e8 6c fd ff ff       	call   4021e0 <__printf_chk@plt>
  402474:	ba 01 00 00 00       	mov    $0x1,%edx
  402479:	48 8d 35 78 52 00 00 	lea    0x5278(%rip),%rsi        # 4076f8 <_IO_stdin_used+0x6f8>
  402480:	31 c0                	xor    %eax,%eax
  402482:	bf 01 00 00 00       	mov    $0x1,%edi
  402487:	e8 54 fd ff ff       	call   4021e0 <__printf_chk@plt>
  40248c:	ba 40 42 0f 00       	mov    $0xf4240,%edx
  402491:	48 8d 35 b6 4e 00 00 	lea    0x4eb6(%rip),%rsi        # 40734e <_IO_stdin_used+0x34e>
  402498:	31 c0                	xor    %eax,%eax
  40249a:	bf 01 00 00 00       	mov    $0x1,%edi
  40249f:	e8 3c fd ff ff       	call   4021e0 <__printf_chk@plt>
  4024a4:	ba 05 00 00 00       	mov    $0x5,%edx
  4024a9:	48 8d 35 b8 4e 00 00 	lea    0x4eb8(%rip),%rsi        # 407368 <_IO_stdin_used+0x368>
  4024b0:	31 c0                	xor    %eax,%eax
  4024b2:	bf 01 00 00 00       	mov    $0x1,%edi
  4024b7:	e8 24 fd ff ff       	call   4021e0 <__printf_chk@plt>
  4024bc:	48 8d 3d 32 4c 00 00 	lea    0x4c32(%rip),%rdi        # 4070f5 <_IO_stdin_used+0xf5>
  4024c3:	e8 98 fb ff ff       	call   402060 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
  4024c8:	be 18 00 00 00       	mov    $0x18,%esi
  4024cd:	bf 03 00 00 00       	mov    $0x3,%edi
  4024d2:	e8 59 fc ff ff       	call   402130 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  4024d7:	be d8 00 00 00       	mov    $0xd8,%esi
  
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  int cc = 0; 
  for (int x = 0 ; x < total_threads; x++) {
  4024dc:	31 ed                	xor    %ebp,%ebp
  int cc = 0; 
  4024de:	31 db                	xor    %ebx,%ebx
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  4024e0:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
  4024e5:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  4024ed:	e8 3e fc ff ff       	call   402130 <calloc@plt>
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  4024f2:	be 28 00 00 00       	mov    $0x28,%esi
  4024f7:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  4024fc:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  402501:	e8 2a fc ff ff       	call   402130 <calloc@plt>
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  402506:	be 28 00 00 00       	mov    $0x28,%esi
  40250b:	bf 64 00 00 00       	mov    $0x64,%edi
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  402510:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  402515:	e8 16 fc ff ff       	call   402130 <calloc@plt>
  40251a:	66 48 0f 6e f0       	movq   %rax,%xmm6
  40251f:	49 89 c4             	mov    %rax,%r12
  402522:	0f 16 74 24 10       	movhps 0x10(%rsp),%xmm6
  402527:	0f 29 b4 24 d0 00 00 00 	movaps %xmm6,0xd0(%rsp)
    for (int y = 0 ; y < total_threads; y++) {
  40252f:	45 31 ff             	xor    %r15d,%r15d
  402532:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  402538:	46 8d 34 3b          	lea    (%rbx,%r15,1),%r14d
  40253c:	45 89 f8             	mov    %r15d,%r8d
  40253f:	89 e9                	mov    %ebp,%ecx
  402541:	4c 89 ee             	mov    %r13,%rsi
  402544:	44 89 f2             	mov    %r14d,%edx
  402547:	bf 01 00 00 00       	mov    $0x1,%edi
  40254c:	31 c0                	xor    %eax,%eax
  40254e:	41 83 c7 01          	add    $0x1,%r15d
  402552:	e8 89 fc ff ff       	call   4021e0 <__printf_chk@plt>
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
  402557:	4b 8d 04 b6          	lea    (%r14,%r14,4),%rax
  40255b:	31 f6                	xor    %esi,%esi
  40255d:	49 8d 3c c4          	lea    (%r12,%rax,8),%rdi
  402561:	e8 4a fd ff ff       	call   4022b0 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
  402566:	41 83 ff 0a          	cmp    $0xa,%r15d
  40256a:	75 cc                	jne    402538 <main+0x218>
      pthread_mutex_init(&swapmutex[cc++], NULL);
  40256c:	83 c3 0a             	add    $0xa,%ebx
  for (int x = 0 ; x < total_threads; x++) {
  40256f:	83 c5 01             	add    $0x1,%ebp
  402572:	83 fb 64             	cmp    $0x64,%ebx
  402575:	75 b8                	jne    40252f <main+0x20f>
  402577:	ba 06 00 00 00       	mov    $0x6,%edx
  40257c:	48 8d 35 09 4e 00 00 	lea    0x4e09(%rip),%rsi        # 40738c <_IO_stdin_used+0x38c>
  402583:	bf 01 00 00 00       	mov    $0x1,%edi
  402588:	31 c0                	xor    %eax,%eax
  40258a:	e8 51 fc ff ff       	call   4021e0 <__printf_chk@plt>
  40258f:	ba 0c 00 00 00       	mov    $0xc,%edx
  402594:	48 8d 35 07 4e 00 00 	lea    0x4e07(%rip),%rsi        # 4073a2 <_IO_stdin_used+0x3a2>
  40259b:	31 c0                	xor    %eax,%eax
  40259d:	bf 01 00 00 00       	mov    $0x1,%edi
  4025a2:	e8 39 fc ff ff       	call   4021e0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
  4025a7:	be 10 00 00 00       	mov    $0x10,%esi
  4025ac:	bf 0c 00 00 00       	mov    $0xc,%edi
  4025b1:	e8 7a fb ff ff       	call   402130 <calloc@plt>
  4025b6:	48 89 84 24 b8 00 00 00 	mov    %rax,0xb8(%rsp)
  4025be:	49 89 c4             	mov    %rax,%r12
  4025c1:	48 8d 98 c0 00 00 00 	lea    0xc0(%rax),%rbx
  4025c8:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  4025d0:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
  4025d5:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  4025dd:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
  4025e2:	49 83 c4 10          	add    $0x10,%r12
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  4025e6:	e8 45 fb ff ff       	call   402130 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  4025eb:	be 20 00 00 00       	mov    $0x20,%esi
  4025f0:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  4025f5:	49 89 44 24 f8       	mov    %rax,-0x8(%r12)
  4025fa:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
  4025fd:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
  402607:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  402611:	e8 1a fb ff ff       	call   402130 <calloc@plt>
  402616:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
  40261d:	4c 39 e3             	cmp    %r12,%rbx
  402620:	75 ae                	jne    4025d0 <main+0x2b0>
  402622:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
  40262a:	48 8b 5c 24 40       	mov    0x40(%rsp),%rbx
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
  int swap = 0;
  for (int k = 0 ; k < group_count ; k++) {
  40262f:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  402637:	45 31 ff             	xor    %r15d,%r15d
  int swap = 0;
  40263a:	c7 44 24 30 00 00 00 00 	movl   $0x0,0x30(%rsp)
  402642:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
  40264a:	48 89 9c 24 a0 00 00 00 	mov    %rbx,0xa0(%rsp)
  for (int x = 0 ; x < buffers_required; x++) {
  402652:	48 89 9c 24 80 00 00 00 	mov    %rbx,0x80(%rsp)
  40265a:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
  int cur_buffer = 0;
  402662:	c7 44 24 50 00 00 00 00 	movl   $0x0,0x50(%rsp)
  int curcpu = 0;
  40266a:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
  402672:	8b 44 24 10          	mov    0x10(%rsp),%eax
  402676:	01 c0                	add    %eax,%eax
  402678:	89 44 24 20          	mov    %eax,0x20(%rsp)
  40267c:	8b 44 24 50          	mov    0x50(%rsp),%eax
  402680:	8d 58 02             	lea    0x2(%rax),%ebx
        other = (x + 1) % total_threads;
        my_thread_data[0] = &thread_data[x]; 
        me_thread = 0;
        my_thread_data[1] = &thread_data[other]; 
        // printf("even %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
        thread_data[x].protected_state = &protected_state[k];
  402683:	89 84 24 b0 00 00 00 	mov    %eax,0xb0(%rsp)
  40268a:	89 9c 24 b4 00 00 00 	mov    %ebx,0xb4(%rsp)
  402691:	48 8b 9c 24 80 00 00 00 	mov    0x80(%rsp),%rbx
  402699:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
  40269e:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
  4026a2:	8b 54 24 10          	mov    0x10(%rsp),%edx
  4026a6:	bf 01 00 00 00       	mov    $0x1,%edi
  4026ab:	31 c0                	xor    %eax,%eax
  4026ad:	48 8d 35 6c 50 00 00 	lea    0x506c(%rip),%rsi        # 407720 <_IO_stdin_used+0x720>
  4026b4:	89 d9                	mov    %ebx,%ecx
  4026b6:	e8 25 fb ff ff       	call   4021e0 <__printf_chk@plt>
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  4026bb:	be 08 00 00 00       	mov    $0x8,%esi
  4026c0:	bf 02 00 00 00       	mov    $0x2,%edi
  4026c5:	e8 66 fa ff ff       	call   402130 <calloc@plt>
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
  4026ca:	bf 01 00 00 00       	mov    $0x1,%edi
  4026cf:	be 80 00 00 00       	mov    $0x80,%esi
  4026d4:	66 48 0f 6e f8       	movq   %rax,%xmm7
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  4026d9:	49 89 c5             	mov    %rax,%r13
  4026dc:	0f 16 7c 24 40       	movhps 0x40(%rsp),%xmm7
  4026e1:	0f 29 3c 24          	movaps %xmm7,(%rsp)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
  4026e5:	e8 46 fa ff ff       	call   402130 <calloc@plt>
  4026ea:	48 89 c5             	mov    %rax,%rbp
      if (x % 2 == 1) {
  4026ed:	89 d8                	mov    %ebx,%eax
  4026ef:	8d 5b ff             	lea    -0x1(%rbx),%ebx
  4026f2:	8d 78 01             	lea    0x1(%rax),%edi
  4026f5:	41 89 c0             	mov    %eax,%r8d
  4026f8:	89 7c 24 74          	mov    %edi,0x74(%rsp)
  4026fc:	41 83 e0 01          	and    $0x1,%r8d
  402700:	0f 85 67 17 00 00    	jne    403e6d <main+0x1b4d>
  402706:	4c 63 e7             	movslq %edi,%r12
        my_thread_data[1] = &thread_data[other]; 
  402709:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  40270e:	4c 89 6c 24 58       	mov    %r13,0x58(%rsp)
        my_thread_data[1] = &thread_data[other]; 
  402713:	4b 8d 04 64          	lea    (%r12,%r12,2),%rax
  402717:	4d 89 e6             	mov    %r12,%r14
  40271a:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
  40271e:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
        thread_data[x].thread_index = 1;
  402722:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
  402727:	48 89 c7             	mov    %rax,%rdi
        thread_data[x].protected_state = &protected_state[k];
  40272a:	48 8b b4 24 88 00 00 00 	mov    0x88(%rsp),%rsi
  402732:	49 89 55 08          	mov    %rdx,0x8(%r13)
  402736:	44 89 f1             	mov    %r14d,%ecx
  402739:	49 89 45 00          	mov    %rax,0x0(%r13)
  40273d:	44 8b 6c 24 20       	mov    0x20(%rsp),%r13d
  402742:	31 c0                	xor    %eax,%eax
  402744:	48 89 77 48          	mov    %rsi,0x48(%rdi)
  402748:	48 8d 35 01 50 00 00 	lea    0x5001(%rip),%rsi        # 407750 <_IO_stdin_used+0x750>
        thread_data[x].thread_index = 1;
  40274f:	44 89 47 04          	mov    %r8d,0x4(%rdi)
  402753:	44 89 ea             	mov    %r13d,%edx
  402756:	bf 01 00 00 00       	mov    $0x1,%edi
  40275b:	e8 80 fa ff ff       	call   4021e0 <__printf_chk@plt>
      }
      printf("i am %d, other is %d my thread index is %d\n", x, other, thread_data[x].thread_index);
      thread_data[x].other = other;
  402760:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
  402765:	8b 4c 24 7c          	mov    0x7c(%rsp),%ecx
  402769:	31 c0                	xor    %eax,%eax
  40276b:	44 89 ea             	mov    %r13d,%edx
  40276e:	48 8d 35 0b 50 00 00 	lea    0x500b(%rip),%rsi        # 407780 <_IO_stdin_used+0x780>
  402775:	44 89 b7 b8 00 00 00 	mov    %r14d,0xb8(%rdi)
  40277c:	bf 01 00 00 00       	mov    $0x1,%edi
  402781:	e8 5a fa ff ff       	call   4021e0 <__printf_chk@plt>
      // for (int j = 0 ; j < cores ; j++) {
        printf("assigning thread %d to core %d\n", x, curcpu);
        if (x < thread_count) {
  402786:	41 83 fd 01          	cmp    $0x1,%r13d
  40278a:	0f 8f d0 16 00 00    	jg     403e60 <main+0x1b40>
          CPU_SET(curcpu, sendercpu);
  402790:	48 63 44 24 7c       	movslq 0x7c(%rsp),%rax
  402795:	48 89 c7             	mov    %rax,%rdi
  402798:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
  40279e:	77 13                	ja     4027b3 <main+0x493>
  4027a0:	48 c1 e8 06          	shr    $0x6,%rax
  4027a4:	ba 01 00 00 00       	mov    $0x1,%edx
  4027a9:	89 f9                	mov    %edi,%ecx
  4027ab:	48 d3 e2             	shl    %cl,%rdx
  4027ae:	48 09 54 c5 00       	or     %rdx,0x0(%rbp,%rax,8)
          curcpu += 2;
  4027b3:	83 44 24 7c 02       	addl   $0x2,0x7c(%rsp)
            CPU_SET(j, sendercpu);
          }
        }
        
      // }
      thread_data[x].swapmutex = swapmutex;
  4027b8:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
      thread_data[x].cpu_set = sendercpu;
      thread_data[x].real_thread_index = x;
      thread_data[x].threads = my_thread_data;
      thread_data[x].all_threads = thread_data;
      thread_data[x].thread_count = 2;
      thread_data[x].group_count = group_count;
  4027bd:	48 8b 05 fc 54 00 00 	mov    0x54fc(%rip),%rax        # 407cc0 <_IO_stdin_used+0xcc0>
      thread_data[x].threads_per_group = threads_per_group;
      thread_data[x].total_thread_count = total_threads;
      thread_data[x].task_count = total_barrier_count;
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  4027c4:	be 10 00 00 00       	mov    $0x10,%esi
  4027c9:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].real_thread_index = x;
  4027ce:	44 8b 6c 24 20       	mov    0x20(%rsp),%r13d
      thread_data[x].threads = my_thread_data;
  4027d3:	66 0f 6f 34 24       	movdqa (%rsp),%xmm6
      thread_data[x].swapmutex = swapmutex;
  4027d8:	66 0f 6f ac 24 d0 00 00 00 	movdqa 0xd0(%rsp),%xmm5
      thread_data[x].group_count = group_count;
  4027e1:	49 89 86 c0 00 00 00 	mov    %rax,0xc0(%r14)
      thread_data[x].thread_count = 2;
  4027e8:	48 8b 05 d9 54 00 00 	mov    0x54d9(%rip),%rax        # 407cc8 <_IO_stdin_used+0xcc8>
      thread_data[x].cpu_set = sendercpu;
  4027ef:	49 89 ae b0 00 00 00 	mov    %rbp,0xb0(%r14)
      thread_data[x].real_thread_index = x;
  4027f6:	45 89 6e 08          	mov    %r13d,0x8(%r14)
      thread_data[x].kind = KERNEL_THREAD;
  4027fa:	41 c7 06 5f 00 00 00 	movl   $0x5f,(%r14)
      thread_data[x].thread_count = 2;
  402801:	49 89 46 28          	mov    %rax,0x28(%r14)
      thread_data[x].task_count = total_barrier_count;
  402805:	41 c7 46 40 03 00 00 00 	movl   $0x3,0x40(%r14)
      thread_data[x].swapmutex = swapmutex;
  40280d:	41 0f 11 ae c8 00 00 00 	movups %xmm5,0xc8(%r14)
      thread_data[x].threads = my_thread_data;
  402815:	41 0f 11 76 18       	movups %xmm6,0x18(%r14)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  40281a:	e8 11 f9 ff ff       	call   402130 <calloc@plt>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  40281f:	be 10 00 00 00       	mov    $0x10,%esi
  402824:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  402829:	49 89 46 68          	mov    %rax,0x68(%r14)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  40282d:	e8 fe f8 ff ff       	call   402130 <calloc@plt>
      thread_data[x].timestamp_count = 0;
      thread_data[x].timestamp_limit = timestamp_limit;
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  402832:	be 28 00 00 00       	mov    $0x28,%esi
  402837:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].timestamp_count = 0;
  40283c:	66 0f 6f 3d 0c 54 00 00 	movdqa 0x540c(%rip),%xmm7        # 407c50 <_IO_stdin_used+0xc50>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  402844:	49 89 46 70          	mov    %rax,0x70(%r14)
      thread_data[x].timestamp_count = 0;
  402848:	41 0f 11 be 80 00 00 00 	movups %xmm7,0x80(%r14)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  402850:	e8 db f8 ff ff       	call   402130 <calloc@plt>
      thread_data[x].task_timestamp_count = 0;
      thread_data[x].task_timestamp_limit = timestamp_limit;

        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  402855:	bf 03 00 00 00       	mov    $0x3,%edi
  40285a:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_timestamp_count = 0;
  40285f:	66 0f 6f 25 e9 53 00 00 	movdqa 0x53e9(%rip),%xmm4        # 407c50 <_IO_stdin_used+0xc50>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  402867:	49 89 86 90 00 00 00 	mov    %rax,0x90(%r14)
      thread_data[x].task_timestamp_count = 0;
  40286e:	41 0f 11 a6 98 00 00 00 	movups %xmm4,0x98(%r14)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  402876:	e8 b5 f8 ff ff       	call   402130 <calloc@plt>
              mailboxes[b].pending_higher = NULL;
              data[0].finished_reading = 1;
              data[1].finished_reading = 1;
              mailboxes[b].kind = MAILBOX_FRIEND;
              if (x % 2 == 0) { 
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
  40287b:	8b 7c 24 74          	mov    0x74(%rsp),%edi
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  40287f:	48 89 c5             	mov    %rax,%rbp
        thread_data[x].tasks = barriers;
  402882:	49 89 46 38          	mov    %rax,0x38(%r14)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
  402886:	49 69 c4 ab aa aa 2a 	imul   $0x2aaaaaab,%r12,%rax
  40288d:	89 fa                	mov    %edi,%edx
  40288f:	c1 fa 1f             	sar    $0x1f,%edx
  402892:	48 c1 e8 20          	shr    $0x20,%rax
  402896:	29 d0                	sub    %edx,%eax
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
  402898:	48 89 ea             	mov    %rbp,%rdx
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
  40289b:	8d 04 40             	lea    (%rax,%rax,2),%eax
  40289e:	01 c0                	add    %eax,%eax
  4028a0:	29 c7                	sub    %eax,%edi
  4028a2:	41 83 e5 01          	and    $0x1,%r13d
  4028a6:	0f 44 df             	cmove  %edi,%ebx
        for (int y = 0 ; y < total_barrier_count ; y++) {
  4028a9:	45 31 e4             	xor    %r12d,%r12d
  4028ac:	89 5c 24 78          	mov    %ebx,0x78(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
  4028b0:	49 63 c4             	movslq %r12d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
  4028b3:	be 40 00 00 00       	mov    $0x40,%esi
  4028b8:	bf 06 00 00 00       	mov    $0x6,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  4028bd:	45 31 f6             	xor    %r14d,%r14d
          thread_data[x].tasks[y].protected = do_protected_write; 
  4028c0:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
  4028c5:	48 c1 e0 09          	shl    $0x9,%rax
  4028c9:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  4028cd:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  4028d2:	48 c7 c0 c0 3f 40 00 	mov    $0x403fc0,%rax
  4028d9:	48 89 83 20 01 00 00 	mov    %rax,0x120(%rbx)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
  4028e0:	e8 4b f8 ff ff       	call   402130 <calloc@plt>
  4028e5:	44 8b 6c 24 10       	mov    0x10(%rsp),%r13d
          thread_data[x].tasks[y].mailboxes = mailboxes;
  4028ea:	48 89 83 70 01 00 00 	mov    %rax,0x170(%rbx)
  4028f1:	48 89 c3             	mov    %rax,%rbx
  4028f4:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  4028f9:	eb 17                	jmp    402912 <main+0x5f2>
  4028fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  402900:	41 83 c6 01          	add    $0x1,%r14d
  402904:	48 83 c3 40          	add    $0x40,%rbx
  402908:	41 83 fe 06          	cmp    $0x6,%r14d
  40290c:	0f 84 47 01 00 00    	je     402a59 <main+0x739>
            int group_of = b / threads_per_group;
  402912:	44 89 f5             	mov    %r14d,%ebp
  402915:	31 c0                	xor    %eax,%eax
  402917:	44 89 f2             	mov    %r14d,%edx
  40291a:	bf 01 00 00 00       	mov    $0x1,%edi
  40291f:	d1 fd                	sar    %ebp
  402921:	48 8d 35 94 4a 00 00 	lea    0x4a94(%rip),%rsi        # 4073bc <_IO_stdin_used+0x3bc>
  402928:	89 e9                	mov    %ebp,%ecx
  40292a:	e8 b1 f8 ff ff       	call   4021e0 <__printf_chk@plt>
            if (k == group_of) {
  40292f:	44 39 ed             	cmp    %r13d,%ebp
  402932:	75 cc                	jne    402900 <main+0x5e0>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402934:	be 08 00 00 00       	mov    $0x8,%esi
  402939:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  40293e:	48 83 c3 40          	add    $0x40,%rbx
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402942:	e8 e9 f7 ff ff       	call   402130 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402947:	be 08 00 00 00       	mov    $0x8,%esi
  40294c:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402951:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402956:	e8 d5 f7 ff ff       	call   402130 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
  40295b:	be 80 03 00 00       	mov    $0x380,%esi
  402960:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402965:	48 89 04 24          	mov    %rax,(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
  402969:	e8 c2 f7 ff ff       	call   402130 <calloc@plt>
              data[0].a = x;
  40296e:	8b 7c 24 20          	mov    0x20(%rsp),%edi
              mailboxes[b].pending_lower = NULL;
  402972:	66 0f ef ed          	pxor   %xmm5,%xmm5
  402976:	44 89 f2             	mov    %r14d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
  402979:	48 89 c5             	mov    %rax,%rbp
              data[0].c = b;
  40297c:	44 89 b0 24 03 00 00 	mov    %r14d,0x324(%rax)
  402983:	48 8d 35 16 4e 00 00 	lea    0x4e16(%rip),%rsi        # 4077a0 <_IO_stdin_used+0x7a0>
              data[0].a = x;
  40298a:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              mailboxes[b].lower = &data[0];
  402990:	66 48 0f 6e c5       	movq   %rbp,%xmm0
              data[0].kind = MAILBOX_LOWER;
  402995:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].b = y;
  40299f:	44 89 a0 20 03 00 00 	mov    %r12d,0x320(%rax)
              data[0].id = dataid++;
  4029a6:	41 8d 47 01          	lea    0x1(%r15),%eax
              data[1].id = dataid++;
  4029aa:	89 85 a8 06 00 00    	mov    %eax,0x6a8(%rbp)
              mailboxes[b].higher = &data[1];
  4029b0:	48 8d 85 80 03 00 00 	lea    0x380(%rbp),%rax
              mailboxes[b].lower = &data[0];
  4029b7:	66 48 0f 6e e0       	movq   %rax,%xmm4
  4029bc:	8b 44 24 78          	mov    0x78(%rsp),%eax
              data[0].id = dataid++;
  4029c0:	44 89 bd 28 03 00 00 	mov    %r15d,0x328(%rbp)
              data[1].id = dataid++;
  4029c7:	41 83 c7 02          	add    $0x2,%r15d
              data[1].a = x;
  4029cb:	89 bd 9c 06 00 00    	mov    %edi,0x69c(%rbp)
              mailboxes[b].lower = &data[0];
  4029d1:	66 0f 6c c4          	punpcklqdq %xmm4,%xmm0
  4029d5:	bf 01 00 00 00       	mov    $0x1,%edi
  4029da:	89 43 fc             	mov    %eax,-0x4(%rbx)
  4029dd:	89 c1                	mov    %eax,%ecx
  4029df:	31 c0                	xor    %eax,%eax
              data[1].c = b;
  4029e1:	44 89 b5 a4 06 00 00 	mov    %r14d,0x6a4(%rbp)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  4029e8:	41 83 c6 01          	add    $0x1,%r14d
              mailboxes[b].kind = MAILBOX_FRIEND;
  4029ec:	c7 43 f8 01 00 00 00 	movl   $0x1,-0x8(%rbx)
              data[1].kind = MAILBOX_HIGHER;
  4029f3:	c7 85 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%rbp)
              data[1].b = y;
  4029fd:	44 89 a5 a0 06 00 00 	mov    %r12d,0x6a0(%rbp)
              data[0].finished_reading = 1;
  402a04:	c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rbp)
              data[1].finished_reading = 1;
  402a0e:	c7 85 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%rbp)
              mailboxes[b].lower = &data[0];
  402a18:	0f 11 43 c0          	movups %xmm0,-0x40(%rbx)
              mailboxes[b].pending_lower = NULL;
  402a1c:	0f 11 6b d0          	movups %xmm5,-0x30(%rbx)
  402a20:	e8 bb f7 ff ff       	call   4021e0 <__printf_chk@plt>
              data[0].messages = messages;
  402a25:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
              data[1].messages = messages2;
  402a2a:	4c 8b 0c 24          	mov    (%rsp),%r9
              data[0].messages_count = 0;
  402a2e:	66 0f 6f 35 2a 52 00 00 	movdqa 0x522a(%rip),%xmm6        # 407c60 <_IO_stdin_used+0xc60>
              data[0].messages = messages;
  402a36:	4c 89 55 00          	mov    %r10,0x0(%rbp)
              data[1].messages = messages2;
  402a3a:	4c 89 8d 80 03 00 00 	mov    %r9,0x380(%rbp)
              data[0].messages_count = 0;
  402a41:	0f 29 b5 80 00 00 00 	movaps %xmm6,0x80(%rbp)
              data[1].messages_count = 0;
  402a48:	0f 29 b5 00 04 00 00 	movaps %xmm6,0x400(%rbp)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  402a4f:	41 83 fe 06          	cmp    $0x6,%r14d
  402a53:	0f 85 b9 fe ff ff    	jne    402912 <main+0x5f2>
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  402a59:	48 8b 6c 24 68       	mov    0x68(%rsp),%rbp
  402a5e:	31 db                	xor    %ebx,%ebx
  402a60:	4c 8d 2d 65 49 00 00 	lea    0x4965(%rip),%r13        # 4073cc <_IO_stdin_used+0x3cc>
  402a67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
            int group_of = b / threads_per_group;
  402a70:	89 d8                	mov    %ebx,%eax
  402a72:	d1 f8                	sar    %eax
            if (k == group_of) {
  402a74:	3b 44 24 10          	cmp    0x10(%rsp),%eax
  402a78:	0f 84 65 01 00 00    	je     402be3 <main+0x8c3>
  402a7e:	89 da                	mov    %ebx,%edx
  402a80:	4c 89 ee             	mov    %r13,%rsi
  402a83:	bf 01 00 00 00       	mov    $0x1,%edi
  402a88:	31 c0                	xor    %eax,%eax
  402a8a:	e8 51 f7 ff ff       	call   4021e0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402a8f:	be 08 00 00 00       	mov    $0x8,%esi
  402a94:	bf 01 00 00 00       	mov    $0x1,%edi
  402a99:	e8 92 f6 ff ff       	call   402130 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402a9e:	be 08 00 00 00       	mov    $0x8,%esi
  402aa3:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402aa8:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402aad:	e8 7e f6 ff ff       	call   402130 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
  402ab2:	be 80 03 00 00       	mov    $0x380,%esi
  402ab7:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402abc:	48 89 04 24          	mov    %rax,(%rsp)
            struct Data *data = calloc(3, sizeof(struct Data));
  402ac0:	e8 6b f6 ff ff       	call   402130 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
  402ac5:	be 80 03 00 00       	mov    $0x380,%esi
  402aca:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
  402acf:	49 89 c6             	mov    %rax,%r14
            struct Data **stack = calloc(3, sizeof(struct Data));
  402ad2:	e8 59 f6 ff ff       	call   402130 <calloc@plt>
            data[0].id = dataid++;
  402ad7:	41 8d 77 01          	lea    0x1(%r15),%esi
            data[0].a = x;
  402adb:	8b 7c 24 20          	mov    0x20(%rsp),%edi
            data[0].messages = messages;
  402adf:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
            data[1].id = dataid++;
  402ae4:	41 89 b6 a8 06 00 00 	mov    %esi,0x6a8(%r14)
            data[1].messages = messages2;
  402aeb:	48 8b 14 24          	mov    (%rsp),%rdx
            mailboxes[b].higher = &data[1];
  402aef:	49 8d b6 80 03 00 00 	lea    0x380(%r14),%rsi
            mailboxes[b].lower = &data[0];
  402af6:	66 49 0f 6e c6       	movq   %r14,%xmm0
  402afb:	66 48 0f 6e d6       	movq   %rsi,%xmm2
            mailboxes[b].stack = (void**)stack;
  402b00:	66 49 0f 6e e6       	movq   %r14,%xmm4
            data[0].messages_count = 0;
  402b05:	66 0f 6f 2d 53 51 00 00 	movdqa 0x5153(%rip),%xmm5        # 407c60 <_IO_stdin_used+0xc60>
            data[0].kind = MAILBOX_LOWER;
  402b0d:	41 c7 86 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r14)
            mailboxes[b].lower = &data[0];
  402b18:	66 0f 6c c2          	punpcklqdq %xmm2,%xmm0
            data[0].a = x;
  402b1c:	41 89 be 1c 03 00 00 	mov    %edi,0x31c(%r14)
            mailboxes[b].pending_lower = NULL;
  402b23:	66 0f ef db          	pxor   %xmm3,%xmm3
            mailboxes[b].lower = &data[0];
  402b27:	0f 11 45 00          	movups %xmm0,0x0(%rbp)
            mailboxes[b].stack = (void**)stack;
  402b2b:	66 48 0f 6e c0       	movq   %rax,%xmm0
            data[0].b = y;
  402b30:	45 89 a6 20 03 00 00 	mov    %r12d,0x320(%r14)
            mailboxes[b].stack = (void**)stack;
  402b37:	66 0f 6c c4          	punpcklqdq %xmm4,%xmm0
            data[0].c = b;
  402b3b:	41 89 9e 24 03 00 00 	mov    %ebx,0x324(%r14)
            data[1].kind = MAILBOX_HIGHER;
  402b42:	41 c7 86 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r14)
            data[1].a = x;
  402b4d:	41 89 be 9c 06 00 00 	mov    %edi,0x69c(%r14)
            data[1].b = y;
  402b54:	45 89 a6 a0 06 00 00 	mov    %r12d,0x6a0(%r14)
            data[1].c = b;
  402b5b:	41 89 9e a4 06 00 00 	mov    %ebx,0x6a4(%r14)
            data[0].finished_reading = 1;
  402b62:	41 c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r14)
            data[1].finished_reading = 1;
  402b6d:	41 c7 86 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r14)
            mailboxes[b].my_higher = &data[1];
  402b78:	48 89 75 30          	mov    %rsi,0x30(%rbp)
            mailboxes[b].kind = MAILBOX_FOREIGN;
  402b7c:	c7 45 38 02 00 00 00 	movl   $0x2,0x38(%rbp)
            stack[0] = mailboxes[b].lower;
  402b83:	4c 89 30             	mov    %r14,(%rax)
            stack[1] = mailboxes[b].higher;
  402b86:	48 89 70 08          	mov    %rsi,0x8(%rax)
            data[0].available_sending = 0;
  402b8a:	41 c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r14)
            data[0].available_receiving = 0;
  402b95:	41 c7 86 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r14)
            data[0].messages = messages;
  402ba0:	4d 89 0e             	mov    %r9,(%r14)
            data[1].messages = messages2;
  402ba3:	49 89 96 80 03 00 00 	mov    %rdx,0x380(%r14)
            data[1].available_sending = 1;
  402baa:	41 c7 86 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r14)
            data[1].available_receiving = 0;
  402bb5:	41 c7 86 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r14)
            data[0].id = dataid++;
  402bc0:	45 89 be 28 03 00 00 	mov    %r15d,0x328(%r14)
            data[1].id = dataid++;
  402bc7:	41 83 c7 02          	add    $0x2,%r15d
            mailboxes[b].pending_lower = NULL;
  402bcb:	0f 11 5d 10          	movups %xmm3,0x10(%rbp)
            mailboxes[b].stack = (void**)stack;
  402bcf:	0f 11 45 20          	movups %xmm0,0x20(%rbp)
            data[0].messages_count = 0;
  402bd3:	41 0f 29 ae 80 00 00 00 	movaps %xmm5,0x80(%r14)
            data[1].messages_count = 0;
  402bdb:	41 0f 29 ae 00 04 00 00 	movaps %xmm5,0x400(%r14)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  402be3:	83 c3 01             	add    $0x1,%ebx
  402be6:	48 83 c5 40          	add    $0x40,%rbp
  402bea:	83 fb 06             	cmp    $0x6,%ebx
  402bed:	0f 85 7d fe ff ff    	jne    402a70 <main+0x750>
          char *message = malloc(sizeof(char) * 256);
  402bf3:	be 01 00 00 00       	mov    $0x1,%esi
  402bf8:	bf 00 01 00 00       	mov    $0x100,%edi
  402bfd:	e8 2e f5 ff ff       	call   402130 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
  402c02:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
  402c07:	48 89 c3             	mov    %rax,%rbx
          struct Message *messaged = malloc(sizeof(struct Message));
  402c0a:	e8 91 f5 ff ff       	call   4021a0 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  402c0f:	48 83 ec 08          	sub    $0x8,%rsp
  402c13:	45 89 e1             	mov    %r12d,%r9d
  402c16:	48 89 df             	mov    %rbx,%rdi
  402c19:	8b 6c 24 18          	mov    0x18(%rsp),%ebp
  402c1d:	49 89 c6             	mov    %rax,%r14
  402c20:	ba 00 01 00 00       	mov    $0x100,%edx
  402c25:	31 c0                	xor    %eax,%eax
  402c27:	48 8d 0d 9a 4b 00 00 	lea    0x4b9a(%rip),%rcx        # 4077c8 <_IO_stdin_used+0x7c8>
  402c2e:	be 01 00 00 00       	mov    $0x1,%esi
  402c33:	55                   	push   %rbp
  402c34:	44 8b 44 24 30       	mov    0x30(%rsp),%r8d
  402c39:	e8 92 f6 ff ff       	call   4022d0 <__sprintf_chk@plt>
          messaged->group = k;
  402c3e:	41 89 6e 18          	mov    %ebp,0x18(%r14)
  402c42:	89 e8                	mov    %ebp,%eax
          messaged->thread_index = thread_data[x].real_thread_index;
  402c44:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
          messaged->message = message;
  402c49:	49 89 1e             	mov    %rbx,(%r14)
          thread_data[x].tasks[y].swap = swap;
  402c4c:	8b 7c 24 40          	mov    0x40(%rsp),%edi
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402c50:	41 8d 4c 24 01       	lea    0x1(%r12),%ecx
  402c55:	66 0f 6e c8          	movd   %eax,%xmm1
          messaged->thread_index = thread_data[x].real_thread_index;
  402c59:	48 63 5d 08          	movslq 0x8(%rbp),%rbx
          thread_data[x].tasks[y].swap = swap;
  402c5d:	48 8b 55 38          	mov    0x38(%rbp),%rdx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402c61:	be 20 00 00 00       	mov    $0x20,%esi
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402c66:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
          messaged->thread_index = thread_data[x].real_thread_index;
  402c6a:	66 48 0f 6e c3       	movq   %rbx,%xmm0
          thread_data[x].tasks[y].swap = swap;
  402c6f:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
  402c74:	48 89 54 24 28       	mov    %rdx,0x28(%rsp)
          messaged->thread_index = thread_data[x].real_thread_index;
  402c79:	0f 16 44 24 70       	movhps 0x70(%rsp),%xmm0
          thread_data[x].tasks[y].swap = swap;
  402c7e:	48 01 d3             	add    %rdx,%rbx
          messaged->thread_index = thread_data[x].real_thread_index;
  402c81:	41 0f 11 46 08       	movups %xmm0,0x8(%r14)
          thread_data[x].tasks[y].swap = swap;
  402c86:	89 bb 98 01 00 00    	mov    %edi,0x198(%rbx)
          swap += 1;
  402c8c:	83 c7 01             	add    $0x1,%edi
  402c8f:	89 7c 24 40          	mov    %edi,0x40(%rsp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402c93:	89 cf                	mov    %ecx,%edi
  402c95:	83 e7 01             	and    $0x1,%edi
          thread_data[x].tasks[y].kind = BARRIER_TASK;
  402c98:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402c9e:	66 0f 6e c7          	movd   %edi,%xmm0
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402ca2:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].message = messaged;
  402ca7:	4c 89 b3 88 01 00 00 	mov    %r14,0x188(%rbx)
          thread_data[x].tasks[y].sending = 1;
  402cae:	c7 83 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402cb8:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
          thread_data[x].tasks[y].snapshot_count = 99;
  402cbc:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402cc7:	66 0f d6 83 90 01 00 00 	movq   %xmm0,0x190(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402ccf:	e8 5c f4 ff ff       	call   402130 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
  402cd4:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402cdf:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
  402ce6:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  402ceb:	48 8b 00             	mov    (%rax),%rax
  402cee:	8b 70 04             	mov    0x4(%rax),%esi
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
  402cf1:	48 39 e8             	cmp    %rbp,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
  402cf4:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
  402cfb:	89 b3 30 01 00 00    	mov    %esi,0x130(%rbx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
  402d01:	41 59                	pop    %r9
  402d03:	41 5a                	pop    %r10
  402d05:	8b 0c 24             	mov    (%rsp),%ecx
  402d08:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  402d0d:	0f 85 a9 11 00 00    	jne    403ebc <main+0x1b9c>
          thread_data[x].tasks[y].thread_count = 2;
  402d13:	66 0f 6f 25 55 4f 00 00 	movdqa 0x4f55(%rip),%xmm4        # 407c70 <_IO_stdin_used+0xc70>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
  402d1b:	44 89 63 04          	mov    %r12d,0x4(%rbx)
          thread_data[x].tasks[y].available = 1;
  402d1f:	4c 8b 35 aa 4f 00 00 	mov    0x4faa(%rip),%r14        # 407cd0 <_IO_stdin_used+0xcd0>
          thread_data[x].tasks[y].arrived = 0;
  402d26:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
          thread_data[x].tasks[y].worker_count = thread_count;
  402d30:	c7 83 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rbx)
          thread_data[x].tasks[y].available = 1;
  402d3a:	4c 89 b3 44 01 00 00 	mov    %r14,0x144(%rbx)
          thread_data[x].tasks[y].thread_count = 2;
  402d41:	0f 11 a3 34 01 00 00 	movups %xmm4,0x134(%rbx)
          if (y == barrier_count - 1) {
  402d48:	41 83 fc 01          	cmp    $0x1,%r12d
  402d4c:	0f 84 bd 10 00 00    	je     403e0f <main+0x1aef>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
  402d52:	45 85 e4             	test   %r12d,%r12d
  402d55:	0f 84 9b 10 00 00    	je     403df6 <main+0x1ad6>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
  402d5b:	48 c7 c0 00 62 40 00 	mov    $0x406200,%rax
  402d62:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
  402d69:	83 f9 03             	cmp    $0x3,%ecx
  402d6c:	0f 85 3f 11 00 00    	jne    403eb1 <main+0x1b91>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
  402d72:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
  402d77:	bf 01 00 00 00       	mov    $0x1,%edi
  402d7c:	be 08 00 00 00       	mov    $0x8,%esi
        thread_data[x].buffers_count = buffers_per_thread;
  402d81:	48 89 d5             	mov    %rdx,%rbp
  402d84:	c7 83 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%rbx)
    for (int d = 0 ; d < threads_per_group ; d++) {
  402d8e:	48 81 c3 d8 00 00 00 	add    $0xd8,%rbx
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
  402d95:	e8 96 f3 ff ff       	call   402130 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
  402d9a:	83 44 24 50 01       	addl   $0x1,0x50(%rsp)
  402d9f:	8b 7c 24 50          	mov    0x50(%rsp),%edi
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
  402da3:	48 89 83 78 ff ff ff 	mov    %rax,-0x88(%rbx)
  402daa:	48 89 c2             	mov    %rax,%rdx
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
  402dad:	48 63 84 24 b0 00 00 00 	movslq 0xb0(%rsp),%rax
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
  402db5:	66 0f 6f ac 24 c0 00 00 00 	movdqa 0xc0(%rsp),%xmm5
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
  402dbe:	48 c1 e0 04          	shl    $0x4,%rax
  402dc2:	48 03 84 24 b8 00 00 00 	add    0xb8(%rsp),%rax
  402dca:	48 89 02             	mov    %rax,(%rdx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
  402dcd:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
  402dd2:	0f 11 ad 18 05 00 00 	movups %xmm5,0x518(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
  402dd9:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
  402ddc:	c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rbp)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
  402de6:	c7 85 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
  402df0:	48 89 85 28 05 00 00 	mov    %rax,0x528(%rbp)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
  402df7:	c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
  402e01:	8b 83 2c ff ff ff    	mov    -0xd4(%rbx),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
  402e07:	c7 85 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
  402e11:	89 85 30 05 00 00    	mov    %eax,0x530(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
  402e17:	4c 89 b5 44 05 00 00 	mov    %r14,0x544(%rbp)
    for (int d = 0 ; d < threads_per_group ; d++) {
  402e1e:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
  402e23:	39 bc 24 b4 00 00 00 	cmp    %edi,0xb4(%rsp)
  402e2a:	0f 85 18 10 00 00    	jne    403e48 <main+0x1b28>
  for (int k = 0 ; k < group_count ; k++) {
  402e30:	83 44 24 10 01       	addl   $0x1,0x10(%rsp)
  402e35:	8b 44 24 10          	mov    0x10(%rsp),%eax
  402e39:	48 83 84 24 88 00 00 00 18 	addq   $0x18,0x88(%rsp)
  402e42:	48 81 84 24 80 00 00 00 b0 01 00 00 	addq   $0x1b0,0x80(%rsp)
  402e4e:	83 f8 03             	cmp    $0x3,%eax
  402e51:	0f 85 1b f8 ff ff    	jne    402672 <main+0x352>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
  402e57:	be 08 00 00 00       	mov    $0x8,%esi
  402e5c:	bf 00 04 00 00       	mov    $0x400,%edi
  402e61:	45 31 ed             	xor    %r13d,%r13d
  int datas_size = 0; 
  402e64:	31 ed                	xor    %ebp,%ebp
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
  402e66:	e8 c5 f2 ff ff       	call   402130 <calloc@plt>
  402e6b:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  402e70:	49 89 c7             	mov    %rax,%r15
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
  402e73:	4d 89 d9             	mov    %r11,%r9
  402e76:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402e78:	45 8b 51 40          	mov    0x40(%r9),%r10d
  402e7c:	45 85 d2             	test   %r10d,%r10d
  402e7f:	0f 8e e2 00 00 00    	jle    402f67 <main+0xc47>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402e85:	49 8b 51 38          	mov    0x38(%r9),%rdx
  402e89:	41 8d 42 ff          	lea    -0x1(%r10),%eax
  402e8d:	48 c1 e0 09          	shl    $0x9,%rax
  402e91:	4c 8d 84 02 70 03 00 00 	lea    0x370(%rdx,%rax,1),%r8
  402e99:	48 8d b2 70 01 00 00 	lea    0x170(%rdx),%rsi
  402ea0:	89 e8                	mov    %ebp,%eax
  402ea2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  402ea8:	48 8b 16             	mov    (%rsi),%rdx
  402eab:	48 63 f8             	movslq %eax,%rdi
  402eae:	89 c1                	mov    %eax,%ecx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402eb0:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402eb7:	49 8d 3c ff          	lea    (%r15,%rdi,8),%rdi
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402ebb:	83 c1 0b             	add    $0xb,%ecx
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402ebe:	f3 0f 6f 3a          	movdqu (%rdx),%xmm7
  402ec2:	f3 0f 6f 4a 40       	movdqu 0x40(%rdx),%xmm1
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402ec7:	48 63 c9             	movslq %ecx,%rcx
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402eca:	4c 8b a2 80 00 00 00 	mov    0x80(%rdx),%r12
  402ed1:	0f 11 3f             	movups %xmm7,(%rdi)
  402ed4:	0f 11 4f 10          	movups %xmm1,0x10(%rdi)
  402ed8:	8d 78 04             	lea    0x4(%rax),%edi
  402edb:	48 63 ff             	movslq %edi,%rdi
  402ede:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402ee2:	4c 8b a2 88 00 00 00 	mov    0x88(%rdx),%r12
  402ee9:	8d 78 05             	lea    0x5(%rax),%edi
  402eec:	48 63 ff             	movslq %edi,%rdi
  402eef:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402ef3:	4c 8b a2 c0 00 00 00 	mov    0xc0(%rdx),%r12
  402efa:	8d 78 06             	lea    0x6(%rax),%edi
  402efd:	48 63 ff             	movslq %edi,%rdi
  402f00:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402f04:	4c 8b a2 c8 00 00 00 	mov    0xc8(%rdx),%r12
  402f0b:	8d 78 07             	lea    0x7(%rax),%edi
  402f0e:	48 63 ff             	movslq %edi,%rdi
  402f11:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402f15:	4c 8b a2 00 01 00 00 	mov    0x100(%rdx),%r12
  402f1c:	8d 78 08             	lea    0x8(%rax),%edi
  402f1f:	48 63 ff             	movslq %edi,%rdi
  402f22:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402f26:	4c 8b a2 08 01 00 00 	mov    0x108(%rdx),%r12
  402f2d:	8d 78 09             	lea    0x9(%rax),%edi
  402f30:	48 63 ff             	movslq %edi,%rdi
  402f33:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402f37:	4c 8b a2 40 01 00 00 	mov    0x140(%rdx),%r12
  402f3e:	8d 78 0a             	lea    0xa(%rax),%edi
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402f41:	83 c0 0c             	add    $0xc,%eax
  402f44:	48 8b 92 48 01 00 00 	mov    0x148(%rdx),%rdx
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402f4b:	48 63 ff             	movslq %edi,%rdi
  402f4e:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402f52:	49 89 14 cf          	mov    %rdx,(%r15,%rcx,8)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402f56:	49 39 f0             	cmp    %rsi,%r8
  402f59:	0f 85 49 ff ff ff    	jne    402ea8 <main+0xb88>
  402f5f:	43 8d 04 52          	lea    (%r10,%r10,2),%eax
  402f63:	8d 6c 85 00          	lea    0x0(%rbp,%rax,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
  402f67:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
  402f6e:	83 fb 01             	cmp    $0x1,%ebx
  402f71:	0f 85 c7 0e 00 00    	jne    403e3e <main+0x1b1e>
  for (int k = 0 ; k < group_count ; k++) {
  402f77:	41 83 c5 02          	add    $0x2,%r13d
  402f7b:	49 81 c3 b0 01 00 00 	add    $0x1b0,%r11
  402f82:	41 83 fd 06          	cmp    $0x6,%r13d
  402f86:	0f 85 e7 fe ff ff    	jne    402e73 <main+0xb53>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  402f8c:	48 8d 3d 57 44 00 00 	lea    0x4457(%rip),%rdi        # 4073ea <_IO_stdin_used+0x3ea>
  402f93:	e8 c8 f0 ff ff       	call   402060 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
  402f98:	48 8d 35 60 44 00 00 	lea    0x4460(%rip),%rsi        # 4073ff <_IO_stdin_used+0x3ff>
  402f9f:	48 8d 3d 5b 44 00 00 	lea    0x445b(%rip),%rdi        # 407401 <_IO_stdin_used+0x401>
  402fa6:	e8 75 f2 ff ff       	call   402220 <fopen@plt>
  402fab:	49 89 c4             	mov    %rax,%r12
  for (int x = 0 ; x < datas_size; x++) {
  402fae:	85 ed                	test   %ebp,%ebp
  402fb0:	7e 70                	jle    403022 <main+0xd02>
  402fb2:	8d 45 ff             	lea    -0x1(%rbp),%eax
  402fb5:	48 8d 1d 66 44 00 00 	lea    0x4466(%rip),%rbx        # 407422 <_IO_stdin_used+0x422>
  402fbc:	4d 8d 6c c7 08       	lea    0x8(%r15,%rax,8),%r13
  402fc1:	48 8d 2d 16 44 00 00 	lea    0x4416(%rip),%rbp        # 4073de <_IO_stdin_used+0x3de>
    char * c = calloc(250, sizeof(char));
  402fc8:	be 01 00 00 00       	mov    $0x1,%esi
  402fcd:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
  402fd2:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
  402fd6:	e8 55 f1 ff ff       	call   402130 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  402fdb:	48 89 e9             	mov    %rbp,%rcx
  402fde:	ba fa 00 00 00       	mov    $0xfa,%edx
  402fe3:	be 01 00 00 00       	mov    $0x1,%esi
  402fe8:	49 89 c6             	mov    %rax,%r14
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
  402feb:	49 8b 47 f8          	mov    -0x8(%r15),%rax
  402fef:	4c 89 f7             	mov    %r14,%rdi
  402ff2:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
  402ff9:	31 c0                	xor    %eax,%eax
  402ffb:	e8 d0 f2 ff ff       	call   4022d0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  403000:	4c 89 f2             	mov    %r14,%rdx
  403003:	48 89 de             	mov    %rbx,%rsi
  403006:	bf 01 00 00 00       	mov    $0x1,%edi
  40300b:	31 c0                	xor    %eax,%eax
  40300d:	e8 ce f1 ff ff       	call   4021e0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  403012:	4c 89 e6             	mov    %r12,%rsi
  403015:	4c 89 f7             	mov    %r14,%rdi
  403018:	e8 d3 f0 ff ff       	call   4020f0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
  40301d:	4d 39 fd             	cmp    %r15,%r13
  403020:	75 a6                	jne    402fc8 <main+0xca8>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
  403022:	4c 89 e7             	mov    %r12,%rdi
  403025:	4c 8d 25 20 44 00 00 	lea    0x4420(%rip),%r12        # 40744c <_IO_stdin_used+0x44c>
  40302c:	e8 5f f0 ff ff       	call   402090 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  403031:	48 8d 3d d2 43 00 00 	lea    0x43d2(%rip),%rdi        # 40740a <_IO_stdin_used+0x40a>
  403038:	e8 23 f0 ff ff       	call   402060 <puts@plt>
  40303d:	48 8b 44 24 40       	mov    0x40(%rsp),%rax

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
  403042:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  40304a:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  40304f:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
  403053:	48 8d 35 cb 43 00 00 	lea    0x43cb(%rip),%rsi        # 407425 <_IO_stdin_used+0x425>
  40305a:	bf 01 00 00 00       	mov    $0x1,%edi
  40305f:	31 c0                	xor    %eax,%eax
  403061:	89 da                	mov    %ebx,%edx
  403063:	e8 78 f1 ff ff       	call   4021e0 <__printf_chk@plt>
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
  403068:	89 d8                	mov    %ebx,%eax
  40306a:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
  40306f:	c7 04 24 00 00 00 00 	movl   $0x0,(%rsp)
  403076:	01 c0                	add    %eax,%eax
  403078:	89 44 24 20          	mov    %eax,0x20(%rsp)
  40307c:	8b 14 24             	mov    (%rsp),%edx
  40307f:	8b 4c 24 20          	mov    0x20(%rsp),%ecx
  403083:	48 8d 35 a5 43 00 00 	lea    0x43a5(%rip),%rsi        # 40742f <_IO_stdin_used+0x42f>
  40308a:	31 c0                	xor    %eax,%eax
  40308c:	bf 01 00 00 00       	mov    $0x1,%edi
  403091:	45 31 f6             	xor    %r14d,%r14d
  403094:	01 d1                	add    %edx,%ecx
  403096:	e8 45 f1 ff ff       	call   4021e0 <__printf_chk@plt>
  40309b:	44 89 f2             	mov    %r14d,%edx
  40309e:	48 8d 35 9c 43 00 00 	lea    0x439c(%rip),%rsi        # 407441 <_IO_stdin_used+0x441>
  4030a5:	31 c0                	xor    %eax,%eax
  4030a7:	4d 89 f5             	mov    %r14,%r13
  4030aa:	bf 01 00 00 00       	mov    $0x1,%edi
  4030af:	49 c1 e5 09          	shl    $0x9,%r13
  4030b3:	31 db                	xor    %ebx,%ebx
  4030b5:	e8 26 f1 ff ff       	call   4021e0 <__printf_chk@plt>
      int x = (k * threads_per_group) + d;
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
  4030ba:	eb 2d                	jmp    4030e9 <main+0xdc9>
  4030bc:	0f 1f 40 00          	nopl   0x0(%rax)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
  4030c0:	83 fa 01             	cmp    $0x1,%edx
  4030c3:	0f 84 08 0d 00 00    	je     403dd1 <main+0x1ab1>
  4030c9:	44 8b 40 3c          	mov    0x3c(%rax),%r8d
  4030cd:	44 89 fa             	mov    %r15d,%edx
  4030d0:	4c 89 e6             	mov    %r12,%rsi
  4030d3:	bf 01 00 00 00       	mov    $0x1,%edi
  4030d8:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
  4030da:	48 83 c3 01          	add    $0x1,%rbx
  4030de:	e8 fd f0 ff ff       	call   4021e0 <__printf_chk@plt>
  4030e3:	48 83 fb 06          	cmp    $0x6,%rbx
  4030e7:	74 4d                	je     403136 <main+0xe16>
          char * mailbox_kind = calloc(100, sizeof(char));
  4030e9:	be 01 00 00 00       	mov    $0x1,%esi
  4030ee:	bf 64 00 00 00       	mov    $0x64,%edi
  4030f3:	41 89 df             	mov    %ebx,%r15d
  4030f6:	e8 35 f0 ff ff       	call   402130 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
  4030fb:	48 8b 7d 38          	mov    0x38(%rbp),%rdi
  4030ff:	48 89 de             	mov    %rbx,%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
  403102:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
  403105:	48 c1 e6 06          	shl    $0x6,%rsi
  403109:	4a 8b 84 2f 70 01 00 00 	mov    0x170(%rdi,%r13,1),%rax
  403111:	48 01 f0             	add    %rsi,%rax
  403114:	8b 50 38             	mov    0x38(%rax),%edx
  403117:	83 fa 02             	cmp    $0x2,%edx
  40311a:	75 a4                	jne    4030c0 <main+0xda0>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  40311c:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
  403126:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
  403129:	4a 8b 84 2f 70 01 00 00 	mov    0x170(%rdi,%r13,1),%rax
  403131:	48 01 f0             	add    %rsi,%rax
  403134:	eb 93                	jmp    4030c9 <main+0xda9>
      for (int y = 0 ; y < total_barrier_count ; y++) {
  403136:	49 83 c6 01          	add    $0x1,%r14
  40313a:	49 83 fe 03          	cmp    $0x3,%r14
  40313e:	0f 85 57 ff ff ff    	jne    40309b <main+0xd7b>
    for (int d = 0 ; d < threads_per_group ; d++) {
  403144:	48 81 c5 d8 00 00 00 	add    $0xd8,%rbp
  40314b:	83 3c 24 01          	cmpl   $0x1,(%rsp)
  40314f:	0f 85 dd 0c 00 00    	jne    403e32 <main+0x1b12>
  for (int k = 0 ; k < group_count ; k++) {
  403155:	83 44 24 10 01       	addl   $0x1,0x10(%rsp)
  40315a:	8b 44 24 10          	mov    0x10(%rsp),%eax
  40315e:	48 81 44 24 18 b0 01 00 00 	addq   $0x1b0,0x18(%rsp)
  403167:	83 f8 03             	cmp    $0x3,%eax
  40316a:	0f 85 df fe ff ff    	jne    40304f <main+0xd2f>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  403170:	ba 07 00 00 00       	mov    $0x7,%edx
  403175:	bf 01 00 00 00       	mov    $0x1,%edi
  40317a:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
  thread_data[timer_threadi].thread_index = 0;

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
  for (int k = 0 ; k < group_count ; k++) {
  40317c:	45 31 ed             	xor    %r13d,%r13d
  40317f:	48 8d 35 e1 42 00 00 	lea    0x42e1(%rip),%rsi        # 407467 <_IO_stdin_used+0x467>
  403186:	e8 55 f0 ff ff       	call   4021e0 <__printf_chk@plt>
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  40318b:	be 08 00 00 00       	mov    $0x8,%esi
  403190:	bf 02 00 00 00       	mov    $0x2,%edi
  403195:	e8 96 ef ff ff       	call   402130 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
  40319a:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40319f:	be 38 00 00 00       	mov    $0x38,%esi
    my_thread_data[0] = &thread_data[x]; 
  4031a4:	49 8d be e8 05 00 00 	lea    0x5e8(%r14),%rdi
  4031ab:	66 49 0f 6e fe       	movq   %r14,%xmm7
    thread_data[x].threads = my_thread_data;
  4031b0:	49 89 86 00 06 00 00 	mov    %rax,0x600(%r14)
  4031b7:	66 49 0f 6e ce       	movq   %r14,%xmm1
    my_thread_data[0] = &thread_data[x]; 
  4031bc:	66 48 0f 6e c7       	movq   %rdi,%xmm0
  4031c1:	48 89 3c 24          	mov    %rdi,(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  4031c5:	bf 0a 00 00 00       	mov    $0xa,%edi
    thread_data[x].thread_count = 2;
  4031ca:	41 c7 86 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%r14)
    my_thread_data[0] = &thread_data[x]; 
  4031d5:	66 0f 6c c7          	punpcklqdq %xmm7,%xmm0
  4031d9:	0f 11 00             	movups %xmm0,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
  4031dc:	49 8b 46 38          	mov    0x38(%r14),%rax
    thread_data[x].thread_index = 0;
  4031e0:	41 c7 86 ec 05 00 00 00 00 00 00 	movl   $0x0,0x5ec(%r14)
    thread_data[x].task_count = total_barrier_count;
  4031eb:	41 c7 86 28 06 00 00 03 00 00 00 	movl   $0x3,0x628(%r14)
    thread_data[n].tasks[0].scheduled = 1;
  4031f6:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  403200:	49 8d 86 d8 00 00 00 	lea    0xd8(%r14),%rax
  403207:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  40320c:	49 8b 86 10 01 00 00 	mov    0x110(%r14),%rax
  403213:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40321d:	0f 16 4c 24 10       	movhps 0x10(%rsp),%xmm1
  403222:	0f 29 4c 24 30       	movaps %xmm1,0x30(%rsp)
  403227:	e8 04 ef ff ff       	call   402130 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40322c:	be 38 00 00 00       	mov    $0x38,%esi
  403231:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403236:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403239:	e8 f2 ee ff ff       	call   402130 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40323e:	be 38 00 00 00       	mov    $0x38,%esi
  403243:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403248:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40324b:	e8 e0 ee ff ff       	call   402130 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403250:	be 38 00 00 00       	mov    $0x38,%esi
  403255:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40325a:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40325f:	e8 cc ee ff ff       	call   402130 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  403264:	be 08 00 00 00       	mov    $0x8,%esi
  403269:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40326e:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  403273:	e8 b8 ee ff ff       	call   402130 <calloc@plt>
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
  403278:	be 08 00 00 00       	mov    $0x8,%esi
  40327d:	bf 0a 00 00 00       	mov    $0xa,%edi
  thread_data[timer_threadi].type = TIMER;
  403282:	41 c7 86 1c 05 00 00 00 00 00 00 	movl   $0x0,0x51c(%r14)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  40328d:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
  403290:	48 8b 05 41 4a 00 00 	mov    0x4a41(%rip),%rax        # 407cd8 <_IO_stdin_used+0xcd8>
  403297:	49 89 86 50 05 00 00 	mov    %rax,0x550(%r14)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
  40329e:	e8 8d ee ff ff       	call   402130 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
  4032a3:	66 49 0f 6e c6       	movq   %r14,%xmm0
    my_thread_data[n] = &thread_data[n]; 
  4032a8:	66 0f 6f 0d d0 49 00 00 	movdqa 0x49d0(%rip),%xmm1        # 407c80 <_IO_stdin_used+0xc80>
  4032b0:	49 8d b6 c0 06 00 00 	lea    0x6c0(%r14),%rsi
  4032b7:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
  4032bb:	48 89 70 40          	mov    %rsi,0x40(%rax)
  4032bf:	49 8d 96 98 07 00 00 	lea    0x798(%r14),%rdx
  4032c6:	bf 01 00 00 00       	mov    $0x1,%edi
  4032cb:	66 0f d4 c8          	paddq  %xmm0,%xmm1
  4032cf:	48 89 50 48          	mov    %rdx,0x48(%rax)
  4032d3:	ba 06 00 00 00       	mov    $0x6,%edx
  4032d8:	0f 11 08             	movups %xmm1,(%rax)
  4032db:	66 0f 6f 0d ad 49 00 00 	movdqa 0x49ad(%rip),%xmm1        # 407c90 <_IO_stdin_used+0xc90>
  thread_data[timer_threadi].threads = my_thread_data;
  4032e3:	49 89 86 28 05 00 00 	mov    %rax,0x528(%r14)
    my_thread_data[n] = &thread_data[n]; 
  4032ea:	66 0f d4 c8          	paddq  %xmm0,%xmm1
  4032ee:	48 89 74 24 28       	mov    %rsi,0x28(%rsp)
  4032f3:	48 8d 35 7c 41 00 00 	lea    0x417c(%rip),%rsi        # 407476 <_IO_stdin_used+0x476>
  4032fa:	0f 11 48 10          	movups %xmm1,0x10(%rax)
  4032fe:	66 0f 6f 0d 9a 49 00 00 	movdqa 0x499a(%rip),%xmm1        # 407ca0 <_IO_stdin_used+0xca0>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
  403306:	41 c7 86 40 05 00 00 06 00 00 00 	movl   $0x6,0x540(%r14)
  thread_data[timer_threadi].thread_index = 0;
  403311:	41 c7 86 14 05 00 00 00 00 00 00 	movl   $0x0,0x514(%r14)
    my_thread_data[n] = &thread_data[n]; 
  40331c:	66 0f d4 c8          	paddq  %xmm0,%xmm1
  403320:	66 0f d4 05 88 49 00 00 	paddq  0x4988(%rip),%xmm0        # 407cb0 <_IO_stdin_used+0xcb0>
  403328:	0f 11 48 20          	movups %xmm1,0x20(%rax)
  40332c:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
  403330:	48 8b 05 a9 49 00 00 	mov    0x49a9(%rip),%rax        # 407ce0 <_IO_stdin_used+0xce0>
  403337:	49 89 86 38 05 00 00 	mov    %rax,0x538(%r14)
  40333e:	31 c0                	xor    %eax,%eax
  403340:	e8 9b ee ff ff       	call   4021e0 <__printf_chk@plt>
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
  403345:	48 c7 c2 90 41 40 00 	mov    $0x404190,%rdx
  40334c:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
  403350:	49 8d 8e 10 05 00 00 	lea    0x510(%r14),%rcx
  403357:	48 8d b5 50 01 00 00 	lea    0x150(%rbp),%rsi
  40335e:	e8 9d ee ff ff       	call   402200 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
  403363:	49 89 d8             	mov    %rbx,%r8
  403366:	4d 89 e1             	mov    %r12,%r9
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
  403369:	4d 89 f2             	mov    %r14,%r10
  40336c:	41 bb 02 00 00 00    	mov    $0x2,%r11d
  403372:	44 89 d8             	mov    %r11d,%eax
  403375:	49 89 db             	mov    %rbx,%r11
  403378:	89 c3                	mov    %eax,%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
  40337a:	47 8d 74 2d 00       	lea    0x0(%r13,%r13,1),%r14d
  40337f:	4d 89 cf             	mov    %r9,%r15
  403382:	4d 89 c4             	mov    %r8,%r12
  403385:	4c 89 d5             	mov    %r10,%rbp
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
  403388:	c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%rbp)
  40338f:	44 89 f2             	mov    %r14d,%edx
  403392:	44 89 e9             	mov    %r13d,%ecx
  403395:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
  403397:	c7 45 44 01 00 00 00 	movl   $0x1,0x44(%rbp)
  40339e:	48 8d 35 53 44 00 00 	lea    0x4453(%rip),%rsi        # 4077f8 <_IO_stdin_used+0x7f8>
  4033a5:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
  4033aa:	41 83 c6 01          	add    $0x1,%r14d
  4033ae:	4c 89 54 24 60       	mov    %r10,0x60(%rsp)
  4033b3:	4c 89 44 24 58       	mov    %r8,0x58(%rsp)
  4033b8:	4c 89 4c 24 50       	mov    %r9,0x50(%rsp)
  4033bd:	4c 89 5c 24 48       	mov    %r11,0x48(%rsp)
  4033c2:	e8 19 ee ff ff       	call   4021e0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
  4033c7:	48 89 e9             	mov    %rbp,%rcx
  4033ca:	4c 89 fe             	mov    %r15,%rsi
  4033cd:	4c 89 e7             	mov    %r12,%rdi
  4033d0:	48 c7 c2 b0 5b 40 00 	mov    $0x405bb0,%rdx
    for (int d = 0 ; d < threads_per_group ; d++) {
  4033d7:	48 81 c5 d8 00 00 00 	add    $0xd8,%rbp
  4033de:	49 83 c4 08          	add    $0x8,%r12
  4033e2:	49 83 c7 38          	add    $0x38,%r15
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
  4033e6:	e8 15 ee ff ff       	call   402200 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
  4033eb:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  4033ef:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
  4033f4:	be 08 00 00 00       	mov    $0x8,%esi
  4033f9:	e8 52 ec ff ff       	call   402050 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
  4033fe:	44 39 f3             	cmp    %r14d,%ebx
  403401:	4c 8b 5c 24 48       	mov    0x48(%rsp),%r11
  403406:	4c 8b 4c 24 50       	mov    0x50(%rsp),%r9
  40340b:	4c 8b 44 24 58       	mov    0x58(%rsp),%r8
  403410:	4c 8b 54 24 60       	mov    0x60(%rsp),%r10
  403415:	0f 85 6d ff ff ff    	jne    403388 <main+0x1068>
  for (int k = 0 ; k < group_count ; k++) {
  40341b:	41 83 c5 01          	add    $0x1,%r13d
  40341f:	49 83 c0 10          	add    $0x10,%r8
  403423:	49 83 c1 70          	add    $0x70,%r9
  403427:	83 c3 02             	add    $0x2,%ebx
  40342a:	49 81 c2 b0 01 00 00 	add    $0x1b0,%r10
  403431:	41 83 fd 03          	cmp    $0x3,%r13d
  403435:	0f 85 3f ff ff ff    	jne    40337a <main+0x105a>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
  40343b:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
  403440:	48 8b 2d a1 48 00 00 	mov    0x48a1(%rip),%rbp        # 407ce8 <_IO_stdin_used+0xce8>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  403447:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
  40344c:	4c 89 db             	mov    %r11,%rbx
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  40344f:	bf 01 00 00 00       	mov    $0x1,%edi
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  403454:	41 bc 08 00 00 00    	mov    $0x8,%r12d
    thread_data[x].type = IO;
  40345a:	41 c7 86 f4 05 00 00 02 00 00 00 	movl   $0x2,0x5f4(%r14)
    thread_data[x].task_count = 0;
  403465:	49 89 ae 28 06 00 00 	mov    %rbp,0x628(%r14)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  40346c:	e8 bf ec ff ff       	call   402130 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
  403471:	be 00 08 00 00       	mov    $0x800,%esi
  403476:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  403478:	49 89 86 40 06 00 00 	mov    %rax,0x640(%r14)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
  40347f:	e8 cc ed ff ff       	call   402250 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  403484:	be 08 00 00 00       	mov    $0x8,%esi
  403489:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
  40348e:	41 89 86 48 06 00 00 	mov    %eax,0x648(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  403495:	e8 96 ec ff ff       	call   402130 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
  40349a:	66 0f 6f 74 24 30    	movdqa 0x30(%rsp),%xmm6
  4034a0:	ba 07 00 00 00       	mov    $0x7,%edx
    thread_data[x].thread_count = thread_count;
  4034a5:	41 c7 86 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%r14)
    thread_data[x].threads = my_thread_data;
  4034b0:	49 89 86 00 06 00 00 	mov    %rax,0x600(%r14)
  4034b7:	48 8d 35 d6 3f 00 00 	lea    0x3fd6(%rip),%rsi        # 407494 <_IO_stdin_used+0x494>
  4034be:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].thread_index = x;
  4034c3:	41 c7 86 ec 05 00 00 07 00 00 00 	movl   $0x7,0x5ec(%r14)
  4034ce:	4c 8d 73 40          	lea    0x40(%rbx),%r14
      my_thread_data[n] = &thread_data[n]; 
  4034d2:	0f 11 30             	movups %xmm6,(%rax)
  4034d5:	31 c0                	xor    %eax,%eax
  4034d7:	e8 04 ed ff ff       	call   4021e0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  4034dc:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  4034e1:	48 8b 0c 24          	mov    (%rsp),%rcx
  4034e5:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
  4034e9:	48 c7 c2 20 54 40 00 	mov    $0x405420,%rdx
  4034f0:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
  4034f7:	e8 04 ed ff ff       	call   402200 <pthread_create@plt>
  4034fc:	ba 08 00 00 00       	mov    $0x8,%edx
  403501:	48 8d 35 a3 3f 00 00 	lea    0x3fa3(%rip),%rsi        # 4074ab <_IO_stdin_used+0x4ab>
  403508:	31 c0                	xor    %eax,%eax
  40350a:	bf 01 00 00 00       	mov    $0x1,%edi
  40350f:	e8 cc ec ff ff       	call   4021e0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  403514:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
  403519:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
  40351e:	4c 8d 05 9c 3f 00 00 	lea    0x3f9c(%rip),%r8        # 4074c1 <_IO_stdin_used+0x4c1>
  403525:	49 81 c5 c0 01 00 00 	add    $0x1c0,%r13
  40352c:	4c 89 c6             	mov    %r8,%rsi
  40352f:	44 89 e2             	mov    %r12d,%edx
  403532:	bf 01 00 00 00       	mov    $0x1,%edi
  403537:	31 c0                	xor    %eax,%eax
  403539:	e8 a2 ec ff ff       	call   4021e0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
  40353e:	49 89 6f 40          	mov    %rbp,0x40(%r15)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
  403542:	be 08 00 00 00       	mov    $0x8,%esi
  403547:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = EXTERNAL;
  40354c:	41 c7 47 0c 03 00 00 00 	movl   $0x3,0xc(%r15)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
  403554:	e8 d7 eb ff ff       	call   402130 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
  403559:	48 8b bc 24 98 00 00 00 	mov    0x98(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  403561:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
  403566:	41 c7 87 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r15)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
  403571:	49 89 47 50          	mov    %rax,0x50(%r15)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
  403575:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  403578:	bf 02 00 00 00       	mov    $0x2,%edi
  40357d:	e8 ae eb ff ff       	call   402130 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
  403582:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  403587:	4c 89 f9             	mov    %r15,%rcx
  40358a:	4c 89 f7             	mov    %r14,%rdi
      my_thread_data[n] = &thread_data[n]; 
  40358d:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    thread_data[x].threads = my_thread_data;
  403592:	49 89 47 18          	mov    %rax,0x18(%r15)
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  403596:	49 83 c6 08          	add    $0x8,%r14
  40359a:	49 81 c7 d8 00 00 00 	add    $0xd8,%r15
      my_thread_data[n] = &thread_data[n]; 
  4035a1:	48 89 50 08          	mov    %rdx,0x8(%rax)
    thread_data[x].thread_count = thread_count;
  4035a5:	48 8b 15 1c 47 00 00 	mov    0x471c(%rip),%rdx        # 407cc8 <_IO_stdin_used+0xcc8>
    thread_data[x].thread_index = x;
  4035ac:	45 89 a7 2c ff ff ff 	mov    %r12d,-0xd4(%r15)
    thread_data[x].thread_count = thread_count;
  4035b3:	49 89 97 50 ff ff ff 	mov    %rdx,-0xb0(%r15)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  4035ba:	48 c7 c2 80 40 40 00 	mov    $0x404080,%rdx
      my_thread_data[n] = &thread_data[n]; 
  4035c1:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  4035c4:	4c 89 ee             	mov    %r13,%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  4035c7:	49 83 c5 38          	add    $0x38,%r13
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  4035cb:	e8 30 ec ff ff       	call   402200 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  4035d0:	4c 8d 05 ea 3e 00 00 	lea    0x3eea(%rip),%r8        # 4074c1 <_IO_stdin_used+0x4c1>
  4035d7:	48 83 84 24 98 00 00 00 10 	addq   $0x10,0x98(%rsp)
  4035e0:	41 83 fc 09          	cmp    $0x9,%r12d
  4035e4:	0f 85 b5 08 00 00    	jne    403e9f <main+0x1b7f>
  4035ea:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
  4035ef:	4c 8d 2d e8 3e 00 00 	lea    0x3ee8(%rip),%r13        # 4074de <_IO_stdin_used+0x4de>
  4035f6:	4c 8d 60 04          	lea    0x4(%rax),%r12
  4035fa:	48 8d a8 74 08 00 00 	lea    0x874(%rax),%rbp
  403601:	41 8b 4c 24 04       	mov    0x4(%r12),%ecx
  403606:	41 8b 14 24          	mov    (%r12),%edx
  40360a:	4c 89 ee             	mov    %r13,%rsi
  40360d:	31 c0                	xor    %eax,%eax
  40360f:	bf 01 00 00 00       	mov    $0x1,%edi
  }

  for (int x = 0 ; x < total_threads ; x++) {
  403614:	49 81 c4 d8 00 00 00 	add    $0xd8,%r12
  40361b:	e8 c0 eb ff ff       	call   4021e0 <__printf_chk@plt>
  403620:	49 39 ec             	cmp    %rbp,%r12
  403623:	75 dc                	jne    403601 <main+0x12e1>
  403625:	48 8d 3d c5 3e 00 00 	lea    0x3ec5(%rip),%rdi        # 4074f1 <_IO_stdin_used+0x4f1>
  40362c:	45 31 e4             	xor    %r12d,%r12d
  40362f:	4c 8d ac 24 e0 00 00 00 	lea    0xe0(%rsp),%r13
  403637:	e8 24 ea ff ff       	call   402060 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
  40363c:	48 8d 2d cc 3e 00 00 	lea    0x3ecc(%rip),%rbp        # 40750f <_IO_stdin_used+0x50f>
    void * result; 
    pthread_join(thread[x], &result);
  403643:	4a 8b 3c e3          	mov    (%rbx,%r12,8),%rdi
  403647:	4c 89 ee             	mov    %r13,%rsi
  40364a:	e8 41 ec ff ff       	call   402290 <pthread_join@plt>
  40364f:	44 89 e2             	mov    %r12d,%edx
  403652:	48 89 ee             	mov    %rbp,%rsi
  403655:	bf 01 00 00 00       	mov    $0x1,%edi
  40365a:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
  40365c:	49 83 c4 01          	add    $0x1,%r12
  403660:	e8 7b eb ff ff       	call   4021e0 <__printf_chk@plt>
  403665:	49 83 fc 0a          	cmp    $0xa,%r12
  403669:	75 d8                	jne    403643 <main+0x1323>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
  40366b:	be 08 00 00 00       	mov    $0x8,%esi
  403670:	bf 00 04 00 00       	mov    $0x400,%edi
  403675:	45 31 ed             	xor    %r13d,%r13d
  int datas2_size = 0; 
  403678:	31 ed                	xor    %ebp,%ebp
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
  40367a:	e8 b1 ea ff ff       	call   402130 <calloc@plt>
  40367f:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  403684:	49 89 c7             	mov    %rax,%r15
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
  403687:	4d 89 d9             	mov    %r11,%r9
  40368a:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  40368c:	45 8b 51 40          	mov    0x40(%r9),%r10d
  403690:	45 85 d2             	test   %r10d,%r10d
  403693:	0f 8e e6 00 00 00    	jle    40377f <main+0x145f>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  403699:	49 8b 51 38          	mov    0x38(%r9),%rdx
  40369d:	41 8d 42 ff          	lea    -0x1(%r10),%eax
  4036a1:	48 c1 e0 09          	shl    $0x9,%rax
  4036a5:	4c 8d 84 02 70 03 00 00 	lea    0x370(%rdx,%rax,1),%r8
  4036ad:	48 8d b2 70 01 00 00 	lea    0x170(%rdx),%rsi
  4036b4:	89 e8                	mov    %ebp,%eax
  4036b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4036c0:	48 8b 16             	mov    (%rsi),%rdx
  4036c3:	48 63 f8             	movslq %eax,%rdi
  4036c6:	89 c1                	mov    %eax,%ecx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  4036c8:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  4036cf:	49 8d 3c ff          	lea    (%r15,%rdi,8),%rdi
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  4036d3:	83 c1 0b             	add    $0xb,%ecx
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  4036d6:	f3 0f 6f 12          	movdqu (%rdx),%xmm2
  4036da:	f3 0f 6f 5a 40       	movdqu 0x40(%rdx),%xmm3
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  4036df:	48 63 c9             	movslq %ecx,%rcx
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  4036e2:	4c 8b a2 80 00 00 00 	mov    0x80(%rdx),%r12
  4036e9:	0f 11 17             	movups %xmm2,(%rdi)
  4036ec:	0f 11 5f 10          	movups %xmm3,0x10(%rdi)
  4036f0:	8d 78 04             	lea    0x4(%rax),%edi
  4036f3:	48 63 ff             	movslq %edi,%rdi
  4036f6:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  4036fa:	4c 8b a2 88 00 00 00 	mov    0x88(%rdx),%r12
  403701:	8d 78 05             	lea    0x5(%rax),%edi
  403704:	48 63 ff             	movslq %edi,%rdi
  403707:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  40370b:	4c 8b a2 c0 00 00 00 	mov    0xc0(%rdx),%r12
  403712:	8d 78 06             	lea    0x6(%rax),%edi
  403715:	48 63 ff             	movslq %edi,%rdi
  403718:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  40371c:	4c 8b a2 c8 00 00 00 	mov    0xc8(%rdx),%r12
  403723:	8d 78 07             	lea    0x7(%rax),%edi
  403726:	48 63 ff             	movslq %edi,%rdi
  403729:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  40372d:	4c 8b a2 00 01 00 00 	mov    0x100(%rdx),%r12
  403734:	8d 78 08             	lea    0x8(%rax),%edi
  403737:	48 63 ff             	movslq %edi,%rdi
  40373a:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  40373e:	4c 8b a2 08 01 00 00 	mov    0x108(%rdx),%r12
  403745:	8d 78 09             	lea    0x9(%rax),%edi
  403748:	48 63 ff             	movslq %edi,%rdi
  40374b:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  40374f:	4c 8b a2 40 01 00 00 	mov    0x140(%rdx),%r12
  403756:	8d 78 0a             	lea    0xa(%rax),%edi
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  403759:	83 c0 0c             	add    $0xc,%eax
  40375c:	48 8b 92 48 01 00 00 	mov    0x148(%rdx),%rdx
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  403763:	48 63 ff             	movslq %edi,%rdi
  403766:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  40376a:	49 89 14 cf          	mov    %rdx,(%r15,%rcx,8)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  40376e:	4c 39 c6             	cmp    %r8,%rsi
  403771:	0f 85 49 ff ff ff    	jne    4036c0 <main+0x13a0>
  403777:	43 8d 04 52          	lea    (%r10,%r10,2),%eax
  40377b:	8d 6c 85 00          	lea    0x0(%rbp,%rax,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
  40377f:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
  403786:	83 fb 01             	cmp    $0x1,%ebx
  403789:	0f 85 99 06 00 00    	jne    403e28 <main+0x1b08>
  for (int k = 0 ; k < group_count ; k++) {
  40378f:	41 83 c5 02          	add    $0x2,%r13d
  403793:	49 81 c3 b0 01 00 00 	add    $0x1b0,%r11
  40379a:	41 83 fd 06          	cmp    $0x6,%r13d
  40379e:	0f 85 e3 fe ff ff    	jne    403687 <main+0x1367>
  4037a4:	48 8d 3d 78 3d 00 00 	lea    0x3d78(%rip),%rdi        # 407523 <_IO_stdin_used+0x523>
  4037ab:	e8 b0 e8 ff ff       	call   402060 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
  4037b0:	48 8d 35 48 3c 00 00 	lea    0x3c48(%rip),%rsi        # 4073ff <_IO_stdin_used+0x3ff>
  4037b7:	48 8d 3d 7d 3d 00 00 	lea    0x3d7d(%rip),%rdi        # 40753b <_IO_stdin_used+0x53b>
  4037be:	e8 5d ea ff ff       	call   402220 <fopen@plt>
  4037c3:	49 89 c4             	mov    %rax,%r12
  for (int x = 0 ; x < datas2_size; x++) {
  4037c6:	85 ed                	test   %ebp,%ebp
  4037c8:	7e 70                	jle    40383a <main+0x151a>
  4037ca:	8d 45 ff             	lea    -0x1(%rbp),%eax
  4037cd:	48 8d 1d 4e 3c 00 00 	lea    0x3c4e(%rip),%rbx        # 407422 <_IO_stdin_used+0x422>
  4037d4:	4d 8d 6c c7 08       	lea    0x8(%r15,%rax,8),%r13
  4037d9:	48 8d 2d fe 3b 00 00 	lea    0x3bfe(%rip),%rbp        # 4073de <_IO_stdin_used+0x3de>
    char * c = calloc(250, sizeof(char));
  4037e0:	be 01 00 00 00       	mov    $0x1,%esi
  4037e5:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
  4037ea:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
  4037ee:	e8 3d e9 ff ff       	call   402130 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  4037f3:	48 89 e9             	mov    %rbp,%rcx
  4037f6:	ba fa 00 00 00       	mov    $0xfa,%edx
  4037fb:	be 01 00 00 00       	mov    $0x1,%esi
  403800:	49 89 c6             	mov    %rax,%r14
    sprintf(c, "mailbox %d\n", datas[x]->id);
  403803:	49 8b 47 f8          	mov    -0x8(%r15),%rax
  403807:	4c 89 f7             	mov    %r14,%rdi
  40380a:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
  403811:	31 c0                	xor    %eax,%eax
  403813:	e8 b8 ea ff ff       	call   4022d0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  403818:	4c 89 f2             	mov    %r14,%rdx
  40381b:	48 89 de             	mov    %rbx,%rsi
  40381e:	bf 01 00 00 00       	mov    $0x1,%edi
  403823:	31 c0                	xor    %eax,%eax
  403825:	e8 b6 e9 ff ff       	call   4021e0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  40382a:	4c 89 e6             	mov    %r12,%rsi
  40382d:	4c 89 f7             	mov    %r14,%rdi
  403830:	e8 bb e8 ff ff       	call   4020f0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
  403835:	4d 39 ef             	cmp    %r13,%r15
  403838:	75 a6                	jne    4037e0 <main+0x14c0>
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
  40383a:	4c 89 e7             	mov    %r12,%rdi
  40383d:	45 31 e4             	xor    %r12d,%r12d
  403840:	e8 4b e8 ff ff       	call   402090 <fclose@plt>
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  403845:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
  long received = 0;
  40384d:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
  long sends = 0;
  403856:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  long ingests = 0;
  40385f:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  long total = 0;
  403868:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  int datas2_size = 0; 
  403871:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
  403879:	48 8b ac 24 a0 00 00 00 	mov    0xa0(%rsp),%rbp
  403881:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  403886:	41 8d 44 24 02       	lea    0x2(%r12),%eax
  40388b:	89 44 24 58          	mov    %eax,0x58(%rsp)
      int x = (k * threads_per_group) + d;
      long v = 0;
      
      int other = -1;
      int me = x;
      if (x % 2 == 1) {
  40388f:	41 8d 44 24 01       	lea    0x1(%r12),%eax
  403894:	89 44 24 50          	mov    %eax,0x50(%rsp)
  403898:	89 c3                	mov    %eax,%ebx
  40389a:	41 f6 c4 01          	test   $0x1,%r12b
  40389e:	74 05                	je     4038a5 <main+0x1585>
        other = abs(x - 1) % total_threads;
  4038a0:	41 8d 5c 24 ff       	lea    -0x1(%r12),%ebx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4038a5:	bf 0a 00 00 00       	mov    $0xa,%edi
  4038aa:	e8 91 e7 ff ff       	call   402040 <putchar@plt>
  4038af:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
  4038b4:	bf 01 00 00 00       	mov    $0x1,%edi
  4038b9:	48 8d 35 84 3c 00 00 	lea    0x3c84(%rip),%rsi        # 407544 <_IO_stdin_used+0x544>
  4038c0:	48 8b 10             	mov    (%rax),%rdx
  4038c3:	31 c0                	xor    %eax,%eax
  4038c5:	e8 16 e9 ff ff       	call   4021e0 <__printf_chk@plt>
        other = (x + 1) % total_threads;
      }
      printf("\n");
      printf("Total Protected %ld\n", protected_state[me].protected);

      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
  4038ca:	8b 55 40             	mov    0x40(%rbp),%edx
  4038cd:	85 d2                	test   %edx,%edx
  4038cf:	0f 8e d5 05 00 00    	jle    403eaa <main+0x1b8a>
        v += thread_data[me].tasks[n].v;
  4038d5:	48 8b 4d 38          	mov    0x38(%rbp),%rcx
  4038d9:	83 ea 01             	sub    $0x1,%edx
  4038dc:	48 c1 e2 09          	shl    $0x9,%rdx
  4038e0:	48 8d 81 10 01 00 00 	lea    0x110(%rcx),%rax
  4038e7:	48 8d 8c 11 10 03 00 00 	lea    0x310(%rcx,%rdx,1),%rcx
      long v = 0;
  4038ef:	31 d2                	xor    %edx,%edx
  4038f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        v += thread_data[me].tasks[n].v;
  4038f8:	48 03 10             	add    (%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
  4038fb:	48 05 00 02 00 00    	add    $0x200,%rax
  403901:	48 39 c8             	cmp    %rcx,%rax
  403904:	75 f2                	jne    4038f8 <main+0x15d8>
      }
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
  403906:	48 63 db             	movslq %ebx,%rbx
  403909:	48 8d 04 5b          	lea    (%rbx,%rbx,2),%rax
  40390d:	48 8b 5c 24 40       	mov    0x40(%rsp),%rbx
  403912:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
  403916:	48 8d 04 c3          	lea    (%rbx,%rax,8),%rax
  40391a:	8b 48 40             	mov    0x40(%rax),%ecx
  40391d:	85 c9                	test   %ecx,%ecx
  40391f:	7e 2d                	jle    40394e <main+0x162e>
        v += thread_data[other].tasks[n].v;
  403921:	48 8b 70 38          	mov    0x38(%rax),%rsi
  403925:	83 e9 01             	sub    $0x1,%ecx
  403928:	48 c1 e1 09          	shl    $0x9,%rcx
  40392c:	48 8d 86 10 01 00 00 	lea    0x110(%rsi),%rax
  403933:	48 8d 8c 0e 10 03 00 00 	lea    0x310(%rsi,%rcx,1),%rcx
  40393b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  403940:	48 03 10             	add    (%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
  403943:	48 05 00 02 00 00    	add    $0x200,%rax
  403949:	48 39 c8             	cmp    %rcx,%rax
  40394c:	75 f2                	jne    403940 <main+0x1620>
  40394e:	48 8d 35 04 3c 00 00 	lea    0x3c04(%rip),%rsi        # 407559 <_IO_stdin_used+0x559>
  403955:	bf 01 00 00 00       	mov    $0x1,%edi
  40395a:	31 c0                	xor    %eax,%eax
  40395c:	e8 7f e8 ff ff       	call   4021e0 <__printf_chk@plt>
      }
      printf("Total V %ld\n", v);
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
  403961:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
  403966:	bf 01 00 00 00       	mov    $0x1,%edi
  40396b:	48 8d 35 b6 3e 00 00 	lea    0x3eb6(%rip),%rsi        # 407828 <_IO_stdin_used+0x828>
  403972:	48 8b 08             	mov    (%rax),%rcx
  403975:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
  40397f:	48 f7 e9             	imul   %rcx
  403982:	48 c1 f9 3f          	sar    $0x3f,%rcx
  403986:	31 c0                	xor    %eax,%eax
  403988:	48 d1 fa             	sar    %rdx
  40398b:	48 29 ca             	sub    %rcx,%rdx
  40398e:	e8 4d e8 ff ff       	call   4021e0 <__printf_chk@plt>
  403993:	bf 0a 00 00 00       	mov    $0xa,%edi
  403998:	e8 a3 e6 ff ff       	call   402040 <putchar@plt>
      printf("\n");
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  40399d:	8b 4d 40             	mov    0x40(%rbp),%ecx
  4039a0:	85 c9                	test   %ecx,%ecx
  4039a2:	0f 8e eb 00 00 00    	jle    403a93 <main+0x1773>
  4039a8:	31 db                	xor    %ebx,%ebx
  4039aa:	4c 8d 3d b5 3b 00 00 	lea    0x3bb5(%rip),%r15        # 407566 <_IO_stdin_used+0x566>
  4039b1:	4c 8d 35 90 3e 00 00 	lea    0x3e90(%rip),%r14        # 407848 <_IO_stdin_used+0x848>
  4039b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        total += thread_data[x].tasks[n].n;
  4039c0:	4c 63 eb             	movslq %ebx,%r13
  4039c3:	49 c1 e5 09          	shl    $0x9,%r13
  4039c7:	4c 89 e8             	mov    %r13,%rax
  4039ca:	48 03 45 38          	add    0x38(%rbp),%rax
  4039ce:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
        ingests += thread_data[x].tasks[n].ingest_count;
        sends += thread_data[x].tasks[n].sends;
  4039d3:	45 31 ed             	xor    %r13d,%r13d
        total += thread_data[x].tasks[n].n;
  4039d6:	48 8b b0 08 01 00 00 	mov    0x108(%rax),%rsi
  4039dd:	48 01 74 24 30       	add    %rsi,0x30(%rsp)
        ingests += thread_data[x].tasks[n].ingest_count;
  4039e2:	48 8b b0 68 01 00 00 	mov    0x168(%rax),%rsi
        sends += thread_data[x].tasks[n].sends;
  4039e9:	48 8b 80 78 01 00 00 	mov    0x178(%rax),%rax
        ingests += thread_data[x].tasks[n].ingest_count;
  4039f0:	48 01 74 24 20       	add    %rsi,0x20(%rsp)
        sends += thread_data[x].tasks[n].sends;
  4039f5:	48 01 44 24 28       	add    %rax,0x28(%rsp)
  4039fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  403a00:	45 89 e8             	mov    %r13d,%r8d
  403a03:	89 d9                	mov    %ebx,%ecx
  403a05:	44 89 e2             	mov    %r12d,%edx
  403a08:	4c 89 fe             	mov    %r15,%rsi
  403a0b:	bf 01 00 00 00       	mov    $0x1,%edi
  403a10:	31 c0                	xor    %eax,%eax
  403a12:	e8 c9 e7 ff ff       	call   4021e0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          printf("combo %d %d %d\n", x, n, kk);
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
  403a17:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
  403a1c:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  403a20:	89 d9                	mov    %ebx,%ecx
  403a22:	4c 89 e8             	mov    %r13,%rax
  403a25:	45 89 e8             	mov    %r13d,%r8d
  403a28:	4c 89 f6             	mov    %r14,%rsi
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
  403a2b:	49 83 c5 01          	add    $0x1,%r13
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
  403a2f:	48 c1 e0 06          	shl    $0x6,%rax
  403a33:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
  403a3b:	bf 01 00 00 00       	mov    $0x1,%edi
  403a40:	48 8b 10             	mov    (%rax),%rdx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
  403a43:	48 8b 40 08          	mov    0x8(%rax),%rax
  403a47:	4c 8b 88 08 03 00 00 	mov    0x308(%rax),%r9

          long tempsent = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
  403a4e:	48 8b 80 10 03 00 00 	mov    0x310(%rax),%rax
  403a55:	4c 03 8a 08 03 00 00 	add    0x308(%rdx),%r9
  403a5c:	48 03 82 10 03 00 00 	add    0x310(%rdx),%rax
  403a63:	44 89 e2             	mov    %r12d,%edx
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
  403a66:	48 01 44 24 18       	add    %rax,0x18(%rsp)
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
  403a6b:	4c 01 0c 24          	add    %r9,(%rsp)
  403a6f:	48 83 ec 08          	sub    $0x8,%rsp
  403a73:	50                   	push   %rax
  403a74:	31 c0                	xor    %eax,%eax
  403a76:	e8 65 e7 ff ff       	call   4021e0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
  403a7b:	58                   	pop    %rax
  403a7c:	5a                   	pop    %rdx
  403a7d:	49 83 fd 06          	cmp    $0x6,%r13
  403a81:	0f 85 79 ff ff ff    	jne    403a00 <main+0x16e0>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  403a87:	83 c3 01             	add    $0x1,%ebx
  403a8a:	39 5d 40             	cmp    %ebx,0x40(%rbp)
  403a8d:	0f 8f 2d ff ff ff    	jg     4039c0 <main+0x16a0>
          printf("ttotal td%d tsk%d %dmb %ld %ld\n", x, n, kk, tempsent, temprec);
        }
      }
      for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
  403a93:	48 8b 8d 88 00 00 00 	mov    0x88(%rbp),%rcx
  403a9a:	48 85 c9             	test   %rcx,%rcx
  403a9d:	7e 14                	jle    403ab3 <main+0x1793>
  403a9f:	31 c0                	xor    %eax,%eax
  403aa1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  403aa8:	83 c0 01             	add    $0x1,%eax
  403aab:	48 63 d0             	movslq %eax,%rdx
  403aae:	48 39 ca             	cmp    %rcx,%rdx
  403ab1:	7c f5                	jl     403aa8 <main+0x1788>
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        // printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
        // printf("%ld iterations\n", thread_data[x].iteration_count);
      }
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  403ab3:	45 31 e4             	xor    %r12d,%r12d
  403ab6:	31 c0                	xor    %eax,%eax
  403ab8:	48 83 bd a0 00 00 00 00 	cmpq   $0x0,0xa0(%rbp)
  403ac0:	48 8d 1d a1 3d 00 00 	lea    0x3da1(%rip),%rbx        # 407868 <_IO_stdin_used+0x868>
  403ac7:	7e 69                	jle    403b32 <main+0x1812>
  403ac9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
  403ad0:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  403ad4:	48 8b 85 90 00 00 00 	mov    0x90(%rbp),%rax
  403adb:	48 83 ec 08          	sub    $0x8,%rsp
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  403adf:	41 83 c4 01          	add    $0x1,%r12d
  403ae3:	bf 01 00 00 00       	mov    $0x1,%edi
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
  403ae8:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
  403aec:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
  403af6:	48 8b 71 18          	mov    0x18(%rcx),%rsi
  403afa:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
  403afe:	48 f7 e6             	mul    %rsi
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
  403b01:	4c 8b 41 10          	mov    0x10(%rcx),%r8
  403b05:	4c 2b 01             	sub    (%rcx),%r8
  403b08:	31 c0                	xor    %eax,%eax
  403b0a:	8b 49 20             	mov    0x20(%rcx),%ecx
  403b0d:	56                   	push   %rsi
  403b0e:	48 89 de             	mov    %rbx,%rsi
  403b11:	48 c1 ea 12          	shr    $0x12,%rdx
  403b15:	49 89 d1             	mov    %rdx,%r9
  403b18:	ba 02 00 00 00       	mov    $0x2,%edx
  403b1d:	e8 be e6 ff ff       	call   4021e0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  403b22:	41 5a                	pop    %r10
  403b24:	49 63 c4             	movslq %r12d,%rax
  403b27:	41 5b                	pop    %r11
  403b29:	48 3b 85 a0 00 00 00 	cmp    0xa0(%rbp),%rax
  403b30:	7c 9e                	jl     403ad0 <main+0x17b0>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
  403b32:	8b 95 bc 00 00 00    	mov    0xbc(%rbp),%edx
  403b38:	85 d2                	test   %edx,%edx
  403b3a:	0f 8e ec 00 00 00    	jle    403c2c <main+0x190c>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
  403b40:	48 8b 75 50          	mov    0x50(%rbp),%rsi
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
  403b44:	45 31 e4             	xor    %r12d,%r12d
  403b47:	4c 8d 35 6a 3d 00 00 	lea    0x3d6a(%rip),%r14        # 4078b8 <_IO_stdin_used+0x8b8>
  403b4e:	66 90                	xchg   %ax,%ax
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
  403b50:	49 63 c4             	movslq %r12d,%rax
  403b53:	4c 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%r13
  403b5b:	48 8b 04 c6          	mov    (%rsi,%rax,8),%rax
  403b5f:	8b 08                	mov    (%rax),%ecx
  403b61:	85 c9                	test   %ecx,%ecx
  403b63:	0f 8e b6 00 00 00    	jle    403c1f <main+0x18ff>
  403b69:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
  403b71:	48 8b 50 08          	mov    0x8(%rax),%rdx
  403b75:	0f 1f 00             	nopl   (%rax)
  403b78:	48 63 5c 24 10       	movslq 0x10(%rsp),%rbx
  403b7d:	45 31 ff             	xor    %r15d,%r15d
  403b80:	48 c1 e3 08          	shl    $0x8,%rbx
  403b84:	48 8d 04 1a          	lea    (%rdx,%rbx,1),%rax
  403b88:	8b b8 94 00 00 00    	mov    0x94(%rax),%edi
  403b8e:	85 ff                	test   %edi,%edi
  403b90:	7e 76                	jle    403c08 <main+0x18e8>
  403b92:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
  403b98:	49 63 cf             	movslq %r15d,%rcx
  403b9b:	48 83 ec 08          	sub    $0x8,%rsp
  403b9f:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
  403ba4:	41 83 c7 01          	add    $0x1,%r15d
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
  403ba8:	48 c1 e1 05          	shl    $0x5,%rcx
  403bac:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
  403bb3:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
  403bbd:	48 8b 71 18          	mov    0x18(%rcx),%rsi
  403bc1:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
  403bc5:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
  403bc8:	4c 8b 41 10          	mov    0x10(%rcx),%r8
  403bcc:	4c 2b 01             	sub    (%rcx),%r8
  403bcf:	56                   	push   %rsi
  403bd0:	44 89 e1             	mov    %r12d,%ecx
  403bd3:	4c 89 f6             	mov    %r14,%rsi
  403bd6:	31 c0                	xor    %eax,%eax
  403bd8:	48 c1 ea 12          	shr    $0x12,%rdx
  403bdc:	49 89 d1             	mov    %rdx,%r9
  403bdf:	ba 02 00 00 00       	mov    $0x2,%edx
  403be4:	e8 f7 e5 ff ff       	call   4021e0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
  403be9:	48 8b 75 50          	mov    0x50(%rbp),%rsi
  403bed:	41 58                	pop    %r8
  403bef:	41 59                	pop    %r9
  403bf1:	4a 8b 0c 2e          	mov    (%rsi,%r13,1),%rcx
  403bf5:	48 8b 51 08          	mov    0x8(%rcx),%rdx
  403bf9:	48 8d 04 1a          	lea    (%rdx,%rbx,1),%rax
  403bfd:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
  403c04:	7f 92                	jg     403b98 <main+0x1878>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
  403c06:	8b 09                	mov    (%rcx),%ecx
  403c08:	83 44 24 10 01       	addl   $0x1,0x10(%rsp)
  403c0d:	8b 44 24 10          	mov    0x10(%rsp),%eax
  403c11:	39 c8                	cmp    %ecx,%eax
  403c13:	0f 8c 5f ff ff ff    	jl     403b78 <main+0x1858>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
  403c19:	8b 95 bc 00 00 00    	mov    0xbc(%rbp),%edx
  403c1f:	41 83 c4 01          	add    $0x1,%r12d
  403c23:	41 39 d4             	cmp    %edx,%r12d
  403c26:	0f 8c 24 ff ff ff    	jl     403b50 <main+0x1830>
    for (int d = 0 ; d < threads_per_group ; d++) {
  403c2c:	8b 44 24 50          	mov    0x50(%rsp),%eax
  403c30:	8b 5c 24 58          	mov    0x58(%rsp),%ebx
  403c34:	48 81 c5 d8 00 00 00 	add    $0xd8,%rbp
  403c3b:	48 83 44 24 48 18    	addq   $0x18,0x48(%rsp)
  403c41:	41 89 c4             	mov    %eax,%r12d
  403c44:	39 d8                	cmp    %ebx,%eax
  403c46:	0f 85 43 fc ff ff    	jne    40388f <main+0x156f>
  for (int k = 0 ; k < group_count ; k++) {
  403c4c:	48 81 84 24 a0 00 00 00 b0 01 00 00 	addq   $0x1b0,0xa0(%rsp)
  403c58:	48 83 84 24 a8 00 00 00 30 	addq   $0x30,0xa8(%rsp)
  403c61:	83 f8 06             	cmp    $0x6,%eax
  403c64:	0f 85 07 fc ff ff    	jne    403871 <main+0x1551>
  403c6a:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
  403c6f:	48 8d 35 00 39 00 00 	lea    0x3900(%rip),%rsi        # 407576 <_IO_stdin_used+0x576>
  403c76:	bf 01 00 00 00       	mov    $0x1,%edi
  403c7b:	31 c0                	xor    %eax,%eax
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
  403c7d:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
  403c87:	4c 89 f2             	mov    %r14,%rdx
  403c8a:	e8 51 e5 ff ff       	call   4021e0 <__printf_chk@plt>
  403c8f:	bf 0a 00 00 00       	mov    $0xa,%edi
  403c94:	e8 a7 e3 ff ff       	call   402040 <putchar@plt>
  403c99:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
  403ca1:	bf 01 00 00 00       	mov    $0x1,%edi
  403ca6:	48 8d 35 63 3c 00 00 	lea    0x3c63(%rip),%rsi        # 407910 <_IO_stdin_used+0x910>
  403cad:	48 8b 50 08          	mov    0x8(%rax),%rdx
  403cb1:	31 c0                	xor    %eax,%eax
  403cb3:	e8 28 e5 ff ff       	call   4021e0 <__printf_chk@plt>
  403cb8:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
  403cbd:	bf 01 00 00 00       	mov    $0x1,%edi
  403cc2:	48 8d 35 6f 3c 00 00 	lea    0x3c6f(%rip),%rsi        # 407938 <_IO_stdin_used+0x938>
  403cc9:	48 f7 eb             	imul   %rbx
  403ccc:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
  403cd1:	48 c1 f8 3f          	sar    $0x3f,%rax
  403cd5:	48 d1 fa             	sar    %rdx
  403cd8:	48 29 c2             	sub    %rax,%rdx
  403cdb:	31 c0                	xor    %eax,%eax
  403cdd:	e8 fe e4 ff ff       	call   4021e0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
  403ce2:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
  403ce7:	bf 01 00 00 00       	mov    $0x1,%edi
  403cec:	48 8d 35 75 3c 00 00 	lea    0x3c75(%rip),%rsi        # 407968 <_IO_stdin_used+0x968>
  403cf3:	48 f7 eb             	imul   %rbx
  403cf6:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
  403cfb:	48 c1 f8 3f          	sar    $0x3f,%rax
  403cff:	48 d1 fa             	sar    %rdx
  403d02:	48 29 c2             	sub    %rax,%rdx
  403d05:	31 c0                	xor    %eax,%eax
  403d07:	e8 d4 e4 ff ff       	call   4021e0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
  403d0c:	4c 89 f0             	mov    %r14,%rax
  403d0f:	bf 01 00 00 00       	mov    $0x1,%edi
  403d14:	48 8d 35 7d 3c 00 00 	lea    0x3c7d(%rip),%rsi        # 407998 <_IO_stdin_used+0x998>
  403d1b:	48 f7 eb             	imul   %rbx
  403d1e:	4c 89 f0             	mov    %r14,%rax
  403d21:	48 c1 f8 3f          	sar    $0x3f,%rax
  403d25:	48 d1 fa             	sar    %rdx
  403d28:	48 29 c2             	sub    %rax,%rdx
  403d2b:	31 c0                	xor    %eax,%eax
  403d2d:	e8 ae e4 ff ff       	call   4021e0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
  403d32:	48 8b 04 24          	mov    (%rsp),%rax
  403d36:	bf 01 00 00 00       	mov    $0x1,%edi
  403d3b:	48 8d 35 48 38 00 00 	lea    0x3848(%rip),%rsi        # 40758a <_IO_stdin_used+0x58a>
  403d42:	48 f7 eb             	imul   %rbx
  403d45:	48 8b 04 24          	mov    (%rsp),%rax
  403d49:	48 c1 f8 3f          	sar    $0x3f,%rax
  403d4d:	48 d1 fa             	sar    %rdx
  403d50:	48 29 c2             	sub    %rax,%rdx
  403d53:	31 c0                	xor    %eax,%eax
  403d55:	48 89 d5             	mov    %rdx,%rbp
  403d58:	e8 83 e4 ff ff       	call   4021e0 <__printf_chk@plt>
  printf("Total sents per second %ld\n", sentdur);
  long recdur = received / DURATION;
  403d5d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  403d62:	bf 01 00 00 00       	mov    $0x1,%edi
  403d67:	48 8d 35 4a 3c 00 00 	lea    0x3c4a(%rip),%rsi        # 4079b8 <_IO_stdin_used+0x9b8>
  403d6e:	48 f7 eb             	imul   %rbx
  403d71:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  403d76:	48 c1 f8 3f          	sar    $0x3f,%rax
  403d7a:	48 89 d3             	mov    %rdx,%rbx
  403d7d:	48 d1 fb             	sar    %rbx
  403d80:	48 29 c3             	sub    %rax,%rbx
  403d83:	31 c0                	xor    %eax,%eax
  403d85:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives per second %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
  403d88:	48 29 eb             	sub    %rbp,%rbx
  403d8b:	e8 50 e4 ff ff       	call   4021e0 <__printf_chk@plt>
  403d90:	31 c0                	xor    %eax,%eax
  403d92:	48 89 da             	mov    %rbx,%rdx
  403d95:	bf 01 00 00 00       	mov    $0x1,%edi
  403d9a:	48 8d 35 05 38 00 00 	lea    0x3805(%rip),%rsi        # 4075a6 <_IO_stdin_used+0x5a6>
  403da1:	e8 3a e4 ff ff       	call   4021e0 <__printf_chk@plt>
  return 0;

}
  403da6:	48 8b 84 24 e8 00 00 00 	mov    0xe8(%rsp),%rax
  403dae:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  403db7:	0f 85 09 01 00 00    	jne    403ec6 <main+0x1ba6>
  403dbd:	48 81 c4 f8 00 00 00 	add    $0xf8,%rsp
  403dc4:	31 c0                	xor    %eax,%eax
  403dc6:	5b                   	pop    %rbx
  403dc7:	5d                   	pop    %rbp
  403dc8:	41 5c                	pop    %r12
  403dca:	41 5d                	pop    %r13
  403dcc:	41 5e                	pop    %r14
  403dce:	41 5f                	pop    %r15
  403dd0:	c3                   	ret
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  403dd1:	41 b8 6e 64 00 00    	mov    $0x646e,%r8d
  403dd7:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
  403ddd:	66 44 89 41 04       	mov    %r8w,0x4(%rcx)
  403de2:	c6 41 06 00          	movb   $0x0,0x6(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
  403de6:	4a 8b 84 2f 70 01 00 00 	mov    0x170(%rdi,%r13,1),%rax
  403dee:	48 01 f0             	add    %rsi,%rax
  403df1:	e9 d3 f2 ff ff       	jmp    4030c9 <main+0xda9>
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
  403df6:	48 c7 c0 90 6a 40 00 	mov    $0x406a90,%rax
  403dfd:	41 bc 01 00 00 00    	mov    $0x1,%r12d
  403e03:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
  403e0a:	e9 a1 ea ff ff       	jmp    4028b0 <main+0x590>
            thread_data[x].tasks[y].run = barriered_work; 
  403e0f:	48 c7 c0 00 62 40 00 	mov    $0x406200,%rax
  403e16:	41 bc 02 00 00 00    	mov    $0x2,%r12d
  403e1c:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
  403e23:	e9 88 ea ff ff       	jmp    4028b0 <main+0x590>
  403e28:	bb 01 00 00 00       	mov    $0x1,%ebx
  403e2d:	e9 5a f8 ff ff       	jmp    40368c <main+0x136c>
  403e32:	c7 04 24 01 00 00 00 	movl   $0x1,(%rsp)
  403e39:	e9 3e f2 ff ff       	jmp    40307c <main+0xd5c>
  403e3e:	bb 01 00 00 00       	mov    $0x1,%ebx
  403e43:	e9 30 f0 ff ff       	jmp    402e78 <main+0xb58>
  403e48:	8b 44 24 74          	mov    0x74(%rsp),%eax
  403e4c:	89 44 24 20          	mov    %eax,0x20(%rsp)
  403e50:	8b 44 24 50          	mov    0x50(%rsp),%eax
  403e54:	89 84 24 b0 00 00 00 	mov    %eax,0xb0(%rsp)
  403e5b:	e9 3e e8 ff ff       	jmp    40269e <main+0x37e>
            CPU_SET(j, sendercpu);
  403e60:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
          for (int j = 0 ; j < cores ; j++) {
  403e68:	e9 4b e9 ff ff       	jmp    4027b8 <main+0x498>
        my_thread_data[0] = &thread_data[other]; 
  403e6d:	48 63 c3             	movslq %ebx,%rax
  403e70:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
        thread_data[x].thread_index = 1;
  403e75:	48 8b 54 24 28       	mov    0x28(%rsp),%rdx
        other = abs(x - 1) % total_threads;
  403e7a:	41 89 de             	mov    %ebx,%r14d
        my_thread_data[0] = &thread_data[other]; 
  403e7d:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
  403e81:	4c 63 64 24 74       	movslq 0x74(%rsp),%r12
  403e86:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
  403e8a:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
  403e8e:	49 8d 7d 08          	lea    0x8(%r13),%rdi
  403e92:	48 89 7c 24 58       	mov    %rdi,0x58(%rsp)
  403e97:	48 89 d7             	mov    %rdx,%rdi
  403e9a:	e9 8b e8 ff ff       	jmp    40272a <main+0x40a>
  403e9f:	41 bc 09 00 00 00    	mov    $0x9,%r12d
  403ea5:	e9 82 f6 ff ff       	jmp    40352c <main+0x120c>
      long v = 0;
  403eaa:	31 d2                	xor    %edx,%edx
  403eac:	e9 55 fa ff ff       	jmp    403906 <main+0x15e6>
  403eb1:	41 bc 02 00 00 00    	mov    $0x2,%r12d
  403eb7:	e9 f4 e9 ff ff       	jmp    4028b0 <main+0x590>
            exit(1);
  403ebc:	bf 01 00 00 00       	mov    $0x1,%edi
  403ec1:	e8 7a e3 ff ff       	call   402240 <exit@plt>
}
  403ec6:	e8 e5 e1 ff ff       	call   4020b0 <__stack_chk_fail@plt>
  403ecb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000403ed0 <_start>:
  403ed0:	f3 0f 1e fa          	endbr64
  403ed4:	31 ed                	xor    %ebp,%ebp
  403ed6:	49 89 d1             	mov    %rdx,%r9
  403ed9:	5e                   	pop    %rsi
  403eda:	48 89 e2             	mov    %rsp,%rdx
  403edd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  403ee1:	50                   	push   %rax
  403ee2:	54                   	push   %rsp
  403ee3:	45 31 c0             	xor    %r8d,%r8d
  403ee6:	31 c9                	xor    %ecx,%ecx
  403ee8:	48 c7 c7 20 23 40 00 	mov    $0x402320,%rdi
  403eef:	ff 15 e3 60 00 00    	call   *0x60e3(%rip)        # 409fd8 <__libc_start_main@GLIBC_2.34>
  403ef5:	f4                   	hlt
  403ef6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000403f00 <_dl_relocate_static_pie>:
  403f00:	f3 0f 1e fa          	endbr64
  403f04:	c3                   	ret
  403f05:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  403f0f:	90                   	nop

0000000000403f10 <deregister_tm_clones>:
  403f10:	b8 20 a0 40 00       	mov    $0x40a020,%eax
  403f15:	48 3d 20 a0 40 00    	cmp    $0x40a020,%rax
  403f1b:	74 13                	je     403f30 <deregister_tm_clones+0x20>
  403f1d:	b8 00 00 00 00       	mov    $0x0,%eax
  403f22:	48 85 c0             	test   %rax,%rax
  403f25:	74 09                	je     403f30 <deregister_tm_clones+0x20>
  403f27:	bf 20 a0 40 00       	mov    $0x40a020,%edi
  403f2c:	ff e0                	jmp    *%rax
  403f2e:	66 90                	xchg   %ax,%ax
  403f30:	c3                   	ret
  403f31:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  403f3c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000403f40 <register_tm_clones>:
  403f40:	be 20 a0 40 00       	mov    $0x40a020,%esi
  403f45:	48 81 ee 20 a0 40 00 	sub    $0x40a020,%rsi
  403f4c:	48 89 f0             	mov    %rsi,%rax
  403f4f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  403f53:	48 c1 f8 03          	sar    $0x3,%rax
  403f57:	48 01 c6             	add    %rax,%rsi
  403f5a:	48 d1 fe             	sar    %rsi
  403f5d:	74 11                	je     403f70 <register_tm_clones+0x30>
  403f5f:	b8 00 00 00 00       	mov    $0x0,%eax
  403f64:	48 85 c0             	test   %rax,%rax
  403f67:	74 07                	je     403f70 <register_tm_clones+0x30>
  403f69:	bf 20 a0 40 00       	mov    $0x40a020,%edi
  403f6e:	ff e0                	jmp    *%rax
  403f70:	c3                   	ret
  403f71:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  403f7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000403f80 <__do_global_dtors_aux>:
  403f80:	f3 0f 1e fa          	endbr64
  403f84:	80 3d 95 60 00 00 00 	cmpb   $0x0,0x6095(%rip)        # 40a020 <__TMC_END__>
  403f8b:	75 13                	jne    403fa0 <__do_global_dtors_aux+0x20>
  403f8d:	55                   	push   %rbp
  403f8e:	48 89 e5             	mov    %rsp,%rbp
  403f91:	e8 7a ff ff ff       	call   403f10 <deregister_tm_clones>
  403f96:	c6 05 83 60 00 00 01 	movb   $0x1,0x6083(%rip)        # 40a020 <__TMC_END__>
  403f9d:	5d                   	pop    %rbp
  403f9e:	c3                   	ret
  403f9f:	90                   	nop
  403fa0:	c3                   	ret
  403fa1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  403fac:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000403fb0 <frame_dummy>:
  403fb0:	f3 0f 1e fa          	endbr64
  403fb4:	eb 8a                	jmp    403f40 <register_tm_clones>
  403fb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000403fc0 <do_protected_write>:
  struct ProtectedState *protected = data->thread->protected_state;
  403fc0:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  403fc7:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
  403fcb:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
  403fd3:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
  403fd7:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
  403fdb:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
  403fe2:	48 85 c9             	test   %rcx,%rcx
  403fe5:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
  403fec:	48 0f 4f d6          	cmovg  %rsi,%rdx
  403ff0:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
  403ff4:	31 c0                	xor    %eax,%eax
  403ff6:	c3                   	ret
  403ff7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000404000 <barriered_reset>:
    for (int x = 0 ; x < data->task_count ; x++) {
  404000:	8b 8f 48 01 00 00    	mov    0x148(%rdi),%ecx
  404006:	85 c9                	test   %ecx,%ecx
  404008:	7e 61                	jle    40406b <barriered_reset+0x6b>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
  40400a:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  404011:	48 63 bf 30 01 00 00 	movslq 0x130(%rdi),%rdi
  404018:	83 e9 01             	sub    $0x1,%ecx
  40401b:	48 c1 e1 09          	shl    $0x9,%rcx
      data->thread->tasks[x].available = 1; 
  40401f:	48 8b 70 38          	mov    0x38(%rax),%rsi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
  404023:	48 8b 40 18          	mov    0x18(%rax),%rax
  404027:	48 8b 04 f8          	mov    (%rax,%rdi,8),%rax
  40402b:	48 8d 96 44 01 00 00 	lea    0x144(%rsi),%rdx
  404032:	48 8d 8c 0e 44 03 00 00 	lea    0x344(%rsi,%rcx,1),%rcx
  40403a:	48 8b 40 38          	mov    0x38(%rax),%rax
  40403e:	48 05 00 01 00 00    	add    $0x100,%rax
  404044:	0f 1f 40 00          	nopl   0x0(%rax)
  404048:	83 40 80 01          	addl   $0x1,-0x80(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
  40404c:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
  404053:	83 00 01             	addl   $0x1,(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
  404056:	48 05 00 02 00 00    	add    $0x200,%rax
      data->thread->tasks[x].available = 1; 
  40405c:	c7 82 00 fe ff ff 01 00 00 00 	movl   $0x1,-0x200(%rdx)
    for (int x = 0 ; x < data->task_count ; x++) {
  404066:	48 39 ca             	cmp    %rcx,%rdx
  404069:	75 dd                	jne    404048 <barriered_reset+0x48>
  asm volatile ("sfence" ::: "memory");
  40406b:	0f ae f8             	sfence
}
  40406e:	31 c0                	xor    %eax,%eax
  404070:	c3                   	ret
  404071:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40407c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000404080 <external_thread>:
  while (data->running == 1) {
  404080:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
  404084:	0f 85 f4 00 00 00    	jne    40417e <external_thread+0xfe>
void * external_thread(void *arg) {
  40408a:	41 57                	push   %r15
  40408c:	49 89 ff             	mov    %rdi,%r15
  40408f:	41 56                	push   %r14
  404091:	41 55                	push   %r13
  404093:	41 54                	push   %r12
  404095:	55                   	push   %rbp
  404096:	53                   	push   %rbx
  404097:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
  40409b:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
  4040a1:	85 c9                	test   %ecx,%ecx
  4040a3:	7e 66                	jle    40410b <external_thread+0x8b>
  4040a5:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
					data->buffers[b]->buffer[x].data = "Hello world";
  4040a9:	4c 8d 2d 54 2f 00 00 	lea    0x2f54(%rip),%r13        # 407004 <_IO_stdin_used+0x4>
    for (int b = 0; b < data->buffers_count; b++) {
  4040b0:	45 31 e4             	xor    %r12d,%r12d
  4040b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int x = 0; x < data->buffers[b]->count; x++) {
  4040b8:	4d 63 f4             	movslq %r12d,%r14
  4040bb:	31 ed                	xor    %ebp,%ebp
  4040bd:	49 c1 e6 03          	shl    $0x3,%r14
  4040c1:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
  4040c5:	48 8b 06             	mov    (%rsi),%rax
  4040c8:	8b 10                	mov    (%rax),%edx
  4040ca:	85 d2                	test   %edx,%edx
  4040cc:	7e 29                	jle    4040f7 <external_thread+0x77>
  4040ce:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
  4040d2:	48 63 dd             	movslq %ebp,%rbx
  4040d5:	48 c1 e3 08          	shl    $0x8,%rbx
  4040d9:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
  4040dd:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
  4040e4:	45 85 c0             	test   %r8d,%r8d
  4040e7:	74 27                	je     404110 <external_thread+0x90>
      for (int x = 0; x < data->buffers[b]->count; x++) {
  4040e9:	83 c5 01             	add    $0x1,%ebp
  4040ec:	39 ea                	cmp    %ebp,%edx
  4040ee:	7f e2                	jg     4040d2 <external_thread+0x52>
    for (int b = 0; b < data->buffers_count; b++) {
  4040f0:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
  4040f7:	41 83 c4 01          	add    $0x1,%r12d
  4040fb:	41 39 cc             	cmp    %ecx,%r12d
  4040fe:	7c b8                	jl     4040b8 <external_thread+0x38>
  while (data->running == 1) {
  404100:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
  404105:	75 66                	jne    40416d <external_thread+0xed>
    for (int b = 0; b < data->buffers_count; b++) {
  404107:	85 c9                	test   %ecx,%ecx
  404109:	7f a5                	jg     4040b0 <external_thread+0x30>
  while (data->running == 1) {
  40410b:	eb fe                	jmp    40410b <external_thread+0x8b>
  40410d:	0f 1f 00             	nopl   (%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
  404110:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
  404113:	48 8b 06             	mov    (%rsi),%rax
  404116:	48 8b 78 08          	mov    0x8(%rax),%rdi
  40411a:	48 01 df             	add    %rbx,%rdi
  40411d:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
  404124:	48 c1 e6 05          	shl    $0x5,%rsi
  404128:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
  40412f:	bf 04 00 00 00       	mov    $0x4,%edi
  404134:	e8 47 df ff ff       	call   402080 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
  404139:	49 8b 47 50          	mov    0x50(%r15),%rax
  40413d:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
  404141:	48 8b 40 08          	mov    0x8(%rax),%rax
  404145:	c7 84 18 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbx,1)
          asm volatile ("sfence" ::: "memory");
  404150:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
  404153:	49 8b 7f 50          	mov    0x50(%r15),%rdi
  404157:	83 c5 01             	add    $0x1,%ebp
  40415a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
  40415e:	48 8b 06             	mov    (%rsi),%rax
  404161:	8b 10                	mov    (%rax),%edx
  404163:	39 d5                	cmp    %edx,%ebp
  404165:	0f 8c 63 ff ff ff    	jl     4040ce <external_thread+0x4e>
  40416b:	eb 83                	jmp    4040f0 <external_thread+0x70>
}
  40416d:	48 83 c4 08          	add    $0x8,%rsp
  404171:	31 c0                	xor    %eax,%eax
  404173:	5b                   	pop    %rbx
  404174:	5d                   	pop    %rbp
  404175:	41 5c                	pop    %r12
  404177:	41 5d                	pop    %r13
  404179:	41 5e                	pop    %r14
  40417b:	41 5f                	pop    %r15
  40417d:	c3                   	ret
  40417e:	31 c0                	xor    %eax,%eax
  404180:	c3                   	ret
  404181:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40418c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000404190 <timer_thread>:
void* timer_thread(void *arg) {
  404190:	41 57                	push   %r15
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  404192:	48 8d 35 77 2e 00 00 	lea    0x2e77(%rip),%rsi        # 407010 <_IO_stdin_used+0x10>
  404199:	49 89 ff             	mov    %rdi,%r15
  40419c:	41 56                	push   %r14
  40419e:	41 55                	push   %r13
  4041a0:	41 54                	push   %r12
  4041a2:	55                   	push   %rbp
  4041a3:	53                   	push   %rbx
  4041a4:	48 83 ec 68          	sub    $0x68,%rsp
  4041a8:	8b 57 04             	mov    0x4(%rdi),%edx
  4041ab:	bf 01 00 00 00       	mov    $0x1,%edi
  4041b0:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4041b9:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  4041be:	31 c0                	xor    %eax,%eax
  4041c0:	e8 1b e0 ff ff       	call   4021e0 <__printf_chk@plt>
  struct timespec preempt = {
  4041c5:	66 0f 6f 05 03 3a 00 00 	movdqa 0x3a03(%rip),%xmm0        # 407bd0 <_IO_stdin_used+0xbd0>
  4041cd:	ba 88 13 00 00       	mov    $0x1388,%edx
  4041d2:	31 c0                	xor    %eax,%eax
  4041d4:	48 8d 35 47 2e 00 00 	lea    0x2e47(%rip),%rsi        # 407022 <_IO_stdin_used+0x22>
  4041db:	bf 01 00 00 00       	mov    $0x1,%edi
  4041e0:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
  4041e5:	e8 f6 df ff ff       	call   4021e0 <__printf_chk@plt>
  while (data->running && n < times) {
  4041ea:	45 8b 77 44          	mov    0x44(%r15),%r14d
  4041ee:	45 85 f6             	test   %r14d,%r14d
  4041f1:	0f 84 ac 00 00 00    	je     4042a3 <timer_thread+0x113>
  int n = 0;
  4041f7:	45 31 ed             	xor    %r13d,%r13d
  int y = 0;
  4041fa:	45 31 f6             	xor    %r14d,%r14d
  4041fd:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
      y = 0;
  404202:	31 db                	xor    %ebx,%ebx
  404204:	48 8d 6c 24 20       	lea    0x20(%rsp),%rbp
    nanosleep(&preempt , &rem2);
  404209:	48 89 ef             	mov    %rbp,%rdi
  40420c:	4c 89 e6             	mov    %r12,%rsi
    n++;
  40420f:	41 83 c5 01          	add    $0x1,%r13d
    nanosleep(&preempt , &rem2);
  404213:	e8 b8 de ff ff       	call   4020d0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404218:	41 8b 57 30          	mov    0x30(%r15),%edx
    y++;
  40421c:	41 8d 7e 01          	lea    0x1(%r14),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404220:	85 d2                	test   %edx,%edx
  404222:	7e 57                	jle    40427b <timer_thread+0xeb>
  404224:	49 8b 47 18          	mov    0x18(%r15),%rax
        data->threads[x]->tasks[y].scheduled = 0;
  404228:	4d 63 c6             	movslq %r14d,%r8
  40422b:	83 ea 01             	sub    $0x1,%edx
  40422e:	49 c1 e0 09          	shl    $0x9,%r8
  404232:	48 8d 48 08          	lea    0x8(%rax),%rcx
  404236:	4c 8d 0c d1          	lea    (%rcx,%rdx,8),%r9
  40423a:	eb 08                	jmp    404244 <timer_thread+0xb4>
  40423c:	0f 1f 40 00          	nopl   0x0(%rax)
  404240:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
  404244:	4c 8b 10             	mov    (%rax),%r10
  404247:	89 f8                	mov    %edi,%eax
  404249:	99                   	cltd
  40424a:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
  40424e:	49 8b 72 38          	mov    0x38(%r10),%rsi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404252:	48 89 c8             	mov    %rcx,%rax
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
  404255:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
  404258:	48 63 d2             	movslq %edx,%rdx
  40425b:	48 c1 e2 09          	shl    $0x9,%rdx
  40425f:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
  40426a:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404276:	49 39 c9             	cmp    %rcx,%r9
  404279:	75 c5                	jne    404240 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
  40427b:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
  40427e:	49 8b 47 18          	mov    0x18(%r15),%rax
  while (data->running && n < times) {
  404282:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    if (y >= data->threads[0]->task_count) {
  404286:	48 8b 00             	mov    (%rax),%rax
      y = 0;
  404289:	39 78 40             	cmp    %edi,0x40(%rax)
  40428c:	0f 4e fb             	cmovle %ebx,%edi
  40428f:	41 89 fe             	mov    %edi,%r14d
  while (data->running && n < times) {
  404292:	85 c9                	test   %ecx,%ecx
  404294:	74 0d                	je     4042a3 <timer_thread+0x113>
  404296:	41 81 fd 88 13 00 00 	cmp    $0x1388,%r13d
  40429d:	0f 85 66 ff ff ff    	jne    404209 <timer_thread+0x79>
  4042a3:	48 8d 3d 8e 2d 00 00 	lea    0x2d8e(%rip),%rdi        # 407038 <_IO_stdin_used+0x38>
  4042aa:	e8 b1 dd ff ff       	call   402060 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
  4042af:	49 63 47 30          	movslq 0x30(%r15),%rax
  4042b3:	85 c0                	test   %eax,%eax
  4042b5:	7e 53                	jle    40430a <timer_thread+0x17a>
    for (int y = 0 ; y < data->task_count ; y++) {
  4042b7:	41 8b 57 40          	mov    0x40(%r15),%edx
  4042bb:	85 d2                	test   %edx,%edx
  4042bd:	7e 4b                	jle    40430a <timer_thread+0x17a>
  4042bf:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
  4042c7:	8d 42 ff             	lea    -0x1(%rdx),%eax
      data->threads[x]->tasks[y].sending = 0;
  4042ca:	4d 8b 47 18          	mov    0x18(%r15),%r8
  4042ce:	31 c9                	xor    %ecx,%ecx
  4042d0:	48 c1 e0 09          	shl    $0x9,%rax
  4042d4:	48 8d b8 80 03 00 00 	lea    0x380(%rax),%rdi
  4042db:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
  4042df:	48 8b 50 38          	mov    0x38(%rax),%rdx
  4042e3:	48 8d 82 80 01 00 00 	lea    0x180(%rdx),%rax
  4042ea:	48 01 fa             	add    %rdi,%rdx
  4042ed:	0f 1f 00             	nopl   (%rax)
  4042f0:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
  4042f6:	48 05 00 02 00 00    	add    $0x200,%rax
  4042fc:	48 39 c2             	cmp    %rax,%rdx
  4042ff:	75 ef                	jne    4042f0 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
  404301:	48 83 c1 08          	add    $0x8,%rcx
  404305:	48 39 ce             	cmp    %rcx,%rsi
  404308:	75 d1                	jne    4042db <timer_thread+0x14b>
  asm volatile ("mfence" ::: "memory");
  40430a:	0f ae f0             	mfence
  struct timespec drain = {
  40430d:	66 0f 6f 05 cb 38 00 00 	movdqa 0x38cb(%rip),%xmm0        # 407be0 <_IO_stdin_used+0xbe0>
  404315:	48 8d 1d 38 2d 00 00 	lea    0x2d38(%rip),%rbx        # 407054 <_IO_stdin_used+0x54>
  40431c:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
  404321:	41 8b 57 28          	mov    0x28(%r15),%edx
    y++;
  404325:	41 8d 46 01          	lea    0x1(%r14),%eax
  404329:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
  40432d:	85 d2                	test   %edx,%edx
  40432f:	7e 5a                	jle    40438b <timer_thread+0x1fb>
  404331:	41 89 c1             	mov    %eax,%r9d
  404334:	49 8b 47 18          	mov    0x18(%r15),%rax
        data->threads[x]->tasks[y].scheduled = 0;
  404338:	49 63 fe             	movslq %r14d,%rdi
  40433b:	83 ea 01             	sub    $0x1,%edx
  40433e:	48 c1 e7 09          	shl    $0x9,%rdi
  404342:	48 8d 48 08          	lea    0x8(%rax),%rcx
  404346:	4c 8d 04 d1          	lea    (%rcx,%rdx,8),%r8
  40434a:	eb 08                	jmp    404354 <timer_thread+0x1c4>
  40434c:	0f 1f 40 00          	nopl   0x0(%rax)
  404350:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
  404354:	4c 8b 10             	mov    (%rax),%r10
  404357:	44 89 c8             	mov    %r9d,%eax
  40435a:	99                   	cltd
  40435b:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
  40435f:	49 8b 72 38          	mov    0x38(%r10),%rsi
    for (int x = 0 ; x < data->thread_count ; x++) {
  404363:	48 89 c8             	mov    %rcx,%rax
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
  404366:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
  404369:	48 63 d2             	movslq %edx,%rdx
  40436c:	48 c1 e2 09          	shl    $0x9,%rdx
  404370:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
  40437b:	c7 84 3e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rdi,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
  404386:	4c 39 c1             	cmp    %r8,%rcx
  404389:	75 c5                	jne    404350 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
  40438b:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
  40438e:	49 8b 4f 18          	mov    0x18(%r15),%rcx
      y = 0;
  404392:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404396:	45 8b 77 30          	mov    0x30(%r15),%r14d
    if (y >= data->threads[0]->task_count) {
  40439a:	48 8b 01             	mov    (%rcx),%rax
      y = 0;
  40439d:	39 78 40             	cmp    %edi,0x40(%rax)
  4043a0:	b8 00 00 00 00       	mov    $0x0,%eax
  4043a5:	0f 4f c7             	cmovg  %edi,%eax
  4043a8:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  4043ac:	45 85 f6             	test   %r14d,%r14d
  4043af:	0f 8e b8 01 00 00    	jle    40456d <timer_thread+0x3dd>
    int all_empty = 1;
  4043b5:	c7 44 24 08 01 00 00 00 	movl   $0x1,0x8(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  4043bd:	45 31 ed             	xor    %r13d,%r13d
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
  4043c0:	49 63 ed             	movslq %r13d,%rbp
  4043c3:	45 31 e4             	xor    %r12d,%r12d
  4043c6:	48 c1 e5 03          	shl    $0x3,%rbp
  4043ca:	45 89 e2             	mov    %r12d,%r10d
        for (int k = 0 ; k < data->my_thread_count; k++) {
  4043cd:	45 85 f6             	test   %r14d,%r14d
  4043d0:	7e 7e                	jle    404450 <timer_thread+0x2c0>
  4043d2:	4c 89 e7             	mov    %r12,%rdi
  4043d5:	49 63 f6             	movslq %r14d,%rsi
  4043d8:	31 c0                	xor    %eax,%eax
  4043da:	48 c1 e7 09          	shl    $0x9,%rdi
  4043de:	66 90                	xchg   %ax,%ax
  4043e0:	41 89 c0             	mov    %eax,%r8d
          if (x == k) { continue; }
  4043e3:	41 39 c5             	cmp    %eax,%r13d
  4043e6:	74 42                	je     40442a <timer_thread+0x29a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
  4043e8:	49 8b 57 18          	mov    0x18(%r15),%rdx
  4043ec:	48 8b 14 2a          	mov    (%rdx,%rbp,1),%rdx
  4043f0:	48 8b 4a 38          	mov    0x38(%rdx),%rcx
  4043f4:	48 89 c2             	mov    %rax,%rdx
  4043f7:	48 c1 e2 06          	shl    $0x6,%rdx
  4043fb:	48 03 94 39 70 01 00 00 	add    0x170(%rcx,%rdi,1),%rdx
  404403:	48 8b 0a             	mov    (%rdx),%rcx
  404406:	48 8b 52 08          	mov    0x8(%rdx),%rdx
  40440a:	4c 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9
  404411:	4c 8b 9a 80 00 00 00 	mov    0x80(%rdx),%r11
  404418:	4d 85 c9             	test   %r9,%r9
  40441b:	0f 8f af 00 00 00    	jg     4044d0 <timer_thread+0x340>
  404421:	4d 85 db             	test   %r11,%r11
  404424:	0f 8f a6 00 00 00    	jg     4044d0 <timer_thread+0x340>
        for (int k = 0 ; k < data->my_thread_count; k++) {
  40442a:	48 83 c0 01          	add    $0x1,%rax
  40442e:	48 39 c6             	cmp    %rax,%rsi
  404431:	75 ad                	jne    4043e0 <timer_thread+0x250>
      for (int y = 0 ; y < 2 ; y++) {
  404433:	49 83 fc 01          	cmp    $0x1,%r12
  404437:	74 17                	je     404450 <timer_thread+0x2c0>
  404439:	41 bc 01 00 00 00    	mov    $0x1,%r12d
  40443f:	45 89 e2             	mov    %r12d,%r10d
        for (int k = 0 ; k < data->my_thread_count; k++) {
  404442:	45 85 f6             	test   %r14d,%r14d
  404445:	7f 8b                	jg     4043d2 <timer_thread+0x242>
  404447:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404450:	41 83 c5 01          	add    $0x1,%r13d
  404454:	45 39 f5             	cmp    %r14d,%r13d
  404457:	0f 8c 63 ff ff ff    	jl     4043c0 <timer_thread+0x230>
    if (all_empty == 1 && all_waited == 1) {
  40445d:	44 0f b6 64 24 08    	movzbl 0x8(%rsp),%r12d
    for (int k = 0 ; k < data->my_thread_count; k++) {
  404463:	45 85 f6             	test   %r14d,%r14d
  404466:	7e 42                	jle    4044aa <timer_thread+0x31a>
  404468:	31 ed                	xor    %ebp,%ebp
    int all_waited = 1;
  40446a:	be 01 00 00 00       	mov    $0x1,%esi
  40446f:	49 8b 4f 18          	mov    0x18(%r15),%rcx
  404473:	41 8b 57 40          	mov    0x40(%r15),%edx
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
  404477:	4c 63 ed             	movslq %ebp,%r13
  40447a:	4a 8b 04 e9          	mov    (%rcx,%r13,8),%rax
  40447e:	48 8b 40 38          	mov    0x38(%rax),%rax
  404482:	44 8b 80 9c 01 00 00 	mov    0x19c(%rax),%r8d
  404489:	41 39 d0             	cmp    %edx,%r8d
  40448c:	0f 8c ae 00 00 00    	jl     404540 <timer_thread+0x3b0>
  404492:	44 8b 80 9c 03 00 00 	mov    0x39c(%rax),%r8d
  404499:	41 39 d0             	cmp    %edx,%r8d
  40449c:	7c 72                	jl     404510 <timer_thread+0x380>
    for (int k = 0 ; k < data->my_thread_count; k++) {
  40449e:	83 c5 01             	add    $0x1,%ebp
  4044a1:	41 39 6f 30          	cmp    %ebp,0x30(%r15)
  4044a5:	7f d0                	jg     404477 <timer_thread+0x2e7>
    if (all_empty == 1 && all_waited == 1) {
  4044a7:	41 21 f4             	and    %esi,%r12d
  4044aa:	45 84 e4             	test   %r12b,%r12b
  4044ad:	0f 85 ba 00 00 00    	jne    40456d <timer_thread+0x3dd>
      nanosleep(&drain , &drainrem);
  4044b3:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
  4044b8:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  4044bd:	e8 0e dc ff ff       	call   4020d0 <nanosleep@plt>
  4044c2:	44 8b 74 24 0c       	mov    0xc(%rsp),%r14d
  4044c7:	e9 55 fe ff ff       	jmp    404321 <timer_thread+0x191>
  4044cc:	0f 1f 40 00          	nopl   0x0(%rax)
  4044d0:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
  4044d6:	48 83 ec 08          	sub    $0x8,%rsp
  4044da:	44 89 ea             	mov    %r13d,%edx
  4044dd:	48 89 de             	mov    %rbx,%rsi
  4044e0:	bf 01 00 00 00       	mov    $0x1,%edi
  4044e5:	50                   	push   %rax
  4044e6:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
  4044ec:	44 89 d1             	mov    %r10d,%ecx
  4044ef:	50                   	push   %rax
  4044f0:	31 c0                	xor    %eax,%eax
  4044f2:	41 53                	push   %r11
  4044f4:	e8 e7 dc ff ff       	call   4021e0 <__printf_chk@plt>
  4044f9:	48 83 c4 20          	add    $0x20,%rsp
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  4044fd:	45 8b 77 30          	mov    0x30(%r15),%r14d
            all_empty = 0;
  404501:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
  404509:	e9 25 ff ff ff       	jmp    404433 <timer_thread+0x2a3>
  40450e:	66 90                	xchg   %ax,%ax
  404510:	48 8d 35 ee 2d 00 00 	lea    0x2dee(%rip),%rsi        # 407305 <_IO_stdin_used+0x305>
  404517:	44 89 c2             	mov    %r8d,%edx
  40451a:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
  40451c:	83 c5 01             	add    $0x1,%ebp
  40451f:	bf 01 00 00 00       	mov    $0x1,%edi
  404524:	e8 b7 dc ff ff       	call   4021e0 <__printf_chk@plt>
          all_waited = 0; 
  404529:	31 f6                	xor    %esi,%esi
    for (int k = 0 ; k < data->my_thread_count; k++) {
  40452b:	41 39 6f 30          	cmp    %ebp,0x30(%r15)
  40452f:	0f 8f 3a ff ff ff    	jg     40446f <timer_thread+0x2df>
  404535:	e9 6d ff ff ff       	jmp    4044a7 <timer_thread+0x317>
  40453a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  404540:	44 89 c2             	mov    %r8d,%edx
  404543:	48 8d 35 bb 2d 00 00 	lea    0x2dbb(%rip),%rsi        # 407305 <_IO_stdin_used+0x305>
  40454a:	bf 01 00 00 00       	mov    $0x1,%edi
  40454f:	31 c0                	xor    %eax,%eax
  404551:	e8 8a dc ff ff       	call   4021e0 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
  404556:	49 8b 4f 18          	mov    0x18(%r15),%rcx
  40455a:	41 8b 57 40          	mov    0x40(%r15),%edx
          all_waited = 0; 
  40455e:	31 f6                	xor    %esi,%esi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
  404560:	4a 8b 04 e9          	mov    (%rcx,%r13,8),%rax
  404564:	48 8b 40 38          	mov    0x38(%rax),%rax
  404568:	e9 25 ff ff ff       	jmp    404492 <timer_thread+0x302>
  40456d:	48 8d 3d fd 2a 00 00 	lea    0x2afd(%rip),%rdi        # 407071 <_IO_stdin_used+0x71>
  404574:	e8 e7 da ff ff       	call   402060 <puts@plt>
  while (data->running) {
  404579:	41 8b 57 44          	mov    0x44(%r15),%edx
  40457d:	85 d2                	test   %edx,%edx
  40457f:	0f 84 cc 00 00 00    	je     404651 <timer_thread+0x4c1>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  404585:	41 8b 47 2c          	mov    0x2c(%r15),%eax
  404589:	31 db                	xor    %ebx,%ebx
  40458b:	4c 8d 25 e8 2a 00 00 	lea    0x2ae8(%rip),%r12        # 40707a <_IO_stdin_used+0x7a>
  404592:	4c 8d 2d fc 2a 00 00 	lea    0x2afc(%rip),%r13        # 407095 <_IO_stdin_used+0x95>
  404599:	85 c0                	test   %eax,%eax
  40459b:	7e 39                	jle    4045d6 <timer_thread+0x446>
  40459d:	0f 1f 00             	nopl   (%rax)
  4045a0:	31 c0                	xor    %eax,%eax
  4045a2:	89 da                	mov    %ebx,%edx
  4045a4:	4c 89 e6             	mov    %r12,%rsi
  4045a7:	bf 01 00 00 00       	mov    $0x1,%edi
  4045ac:	e8 2f dc ff ff       	call   4021e0 <__printf_chk@plt>
      data->threads[x]->running = 0;
  4045b1:	49 8b 47 18          	mov    0x18(%r15),%rax
  4045b5:	48 63 eb             	movslq %ebx,%rbp
  4045b8:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
      if (data->threads[x]->type == IO) {
  4045bc:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
  4045c0:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
  4045c7:	0f 84 b1 00 00 00    	je     40467e <timer_thread+0x4ee>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  4045cd:	83 c3 01             	add    $0x1,%ebx
  4045d0:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
  4045d4:	7f ca                	jg     4045a0 <timer_thread+0x410>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  4045d6:	49 63 47 30          	movslq 0x30(%r15),%rax
  4045da:	85 c0                	test   %eax,%eax
  4045dc:	7e 5c                	jle    40463a <timer_thread+0x4aa>
      for (int y = 0 ; y < data->task_count ; y++) {
  4045de:	41 8b 57 40          	mov    0x40(%r15),%edx
  4045e2:	85 d2                	test   %edx,%edx
  4045e4:	7e 54                	jle    40463a <timer_thread+0x4aa>
  4045e6:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
  4045ee:	8d 42 ff             	lea    -0x1(%rdx),%eax
        data->threads[x]->tasks[y].scheduled = 0;
  4045f1:	4d 8b 47 18          	mov    0x18(%r15),%r8
  4045f5:	31 c9                	xor    %ecx,%ecx
  4045f7:	48 c1 e0 09          	shl    $0x9,%rax
  4045fb:	48 8d b8 4c 03 00 00 	lea    0x34c(%rax),%rdi
  404602:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  404608:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
  40460c:	48 8b 50 38          	mov    0x38(%rax),%rdx
  404610:	48 8d 82 4c 01 00 00 	lea    0x14c(%rdx),%rax
  404617:	48 01 fa             	add    %rdi,%rdx
  40461a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  404620:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
  404626:	48 05 00 02 00 00    	add    $0x200,%rax
  40462c:	48 39 c2             	cmp    %rax,%rdx
  40462f:	75 ef                	jne    404620 <timer_thread+0x490>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404631:	48 83 c1 08          	add    $0x8,%rcx
  404635:	48 39 ce             	cmp    %rcx,%rsi
  404638:	75 ce                	jne    404608 <timer_thread+0x478>
    asm volatile ("mfence" ::: "memory");
  40463a:	0f ae f0             	mfence
  40463d:	48 8d 3d 63 2a 00 00 	lea    0x2a63(%rip),%rdi        # 4070a7 <_IO_stdin_used+0xa7>
  404644:	e8 17 da ff ff       	call   402060 <puts@plt>
    data->running = 0;
  404649:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
  404651:	48 8d 3d 56 2a 00 00 	lea    0x2a56(%rip),%rdi        # 4070ae <_IO_stdin_used+0xae>
  404658:	e8 03 da ff ff       	call   402060 <puts@plt>
}
  40465d:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  404662:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40466b:	75 40                	jne    4046ad <timer_thread+0x51d>
  40466d:	48 83 c4 68          	add    $0x68,%rsp
  404671:	31 c0                	xor    %eax,%eax
  404673:	5b                   	pop    %rbx
  404674:	5d                   	pop    %rbp
  404675:	41 5c                	pop    %r12
  404677:	41 5d                	pop    %r13
  404679:	41 5e                	pop    %r14
  40467b:	41 5f                	pop    %r15
  40467d:	c3                   	ret
  40467e:	4c 89 ef             	mov    %r13,%rdi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  404681:	83 c3 01             	add    $0x1,%ebx
  404684:	e8 d7 d9 ff ff       	call   402060 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
  404689:	49 8b 47 18          	mov    0x18(%r15),%rax
  40468d:	be 01 00 00 00       	mov    $0x1,%esi
  404692:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
  404696:	8b 78 60             	mov    0x60(%rax),%edi
  404699:	e8 f2 da ff ff       	call   402190 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  40469e:	41 3b 5f 2c          	cmp    0x2c(%r15),%ebx
  4046a2:	0f 8c f8 fe ff ff    	jl     4045a0 <timer_thread+0x410>
  4046a8:	e9 29 ff ff ff       	jmp    4045d6 <timer_thread+0x446>
}
  4046ad:	e8 fe d9 ff ff       	call   4020b0 <__stack_chk_fail@plt>
  4046b2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4046bd:	0f 1f 00             	nopl   (%rax)

00000000004046c0 <minf>:
}
  4046c0:	39 f7                	cmp    %esi,%edi
  4046c2:	89 f0                	mov    %esi,%eax
  4046c4:	0f 4e c7             	cmovle %edi,%eax
  4046c7:	c3                   	ret
  4046c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

00000000004046d0 <maxf>:
}
  4046d0:	39 f7                	cmp    %esi,%edi
  4046d2:	89 f0                	mov    %esi,%eax
  4046d4:	0f 4d c7             	cmovge %edi,%eax
  4046d7:	c3                   	ret
  4046d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

00000000004046e0 <fatal_error>:
void fatal_error(const char *syscall) {
  4046e0:	48 83 ec 08          	sub    $0x8,%rsp
    perror(syscall);
  4046e4:	e8 47 db ff ff       	call   402230 <perror@plt>
    exit(1);
  4046e9:	bf 01 00 00 00       	mov    $0x1,%edi
  4046ee:	e8 4d db ff ff       	call   402240 <exit@plt>
  4046f3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4046fe:	66 90                	xchg   %ax,%ax

0000000000404700 <strtolower>:
void strtolower(char *str) {
  404700:	55                   	push   %rbp
  404701:	53                   	push   %rbx
  404702:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
  404706:	48 0f be 1f          	movsbq (%rdi),%rbx
  40470a:	84 db                	test   %bl,%bl
  40470c:	74 28                	je     404736 <strtolower+0x36>
  40470e:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
  404711:	e8 aa db ff ff       	call   4022c0 <__ctype_tolower_loc@plt>
  404716:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  404720:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
  404723:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
  404727:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
  40472a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
  40472d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
  404732:	84 db                	test   %bl,%bl
  404734:	75 ea                	jne    404720 <strtolower+0x20>
}
  404736:	48 83 c4 08          	add    $0x8,%rsp
  40473a:	5b                   	pop    %rbx
  40473b:	5d                   	pop    %rbp
  40473c:	c3                   	ret
  40473d:	0f 1f 00             	nopl   (%rax)

0000000000404740 <zh_malloc>:
void *zh_malloc(size_t size) {
  404740:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
  404744:	e8 57 da ff ff       	call   4021a0 <malloc@plt>
    if (!buf) {
  404749:	48 85 c0             	test   %rax,%rax
  40474c:	74 05                	je     404753 <zh_malloc+0x13>
}
  40474e:	48 83 c4 08          	add    $0x8,%rsp
  404752:	c3                   	ret
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
  404753:	48 8b 05 9e 58 00 00 	mov    0x589e(%rip),%rax        # 409ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  40475a:	ba 28 00 00 00       	mov    $0x28,%edx
  40475f:	be 01 00 00 00       	mov    $0x1,%esi
  404764:	48 8d 3d 4d 2e 00 00 	lea    0x2e4d(%rip),%rdi        # 4075b8 <_IO_stdin_used+0x5b8>
  40476b:	48 8b 08             	mov    (%rax),%rcx
  40476e:	e8 ed da ff ff       	call   402260 <fwrite@plt>
        exit(1);
  404773:	bf 01 00 00 00       	mov    $0x1,%edi
  404778:	e8 c3 da ff ff       	call   402240 <exit@plt>
  40477d:	0f 1f 00             	nopl   (%rax)

0000000000404780 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
  404780:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
  404781:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
  404786:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
  404789:	e8 52 d9 ff ff       	call   4020e0 <strrchr@plt>
    if (!dot || dot == filename)
  40478e:	48 85 c0             	test   %rax,%rax
  404791:	74 0d                	je     4047a0 <get_filename_ext+0x20>
  404793:	48 39 c3             	cmp    %rax,%rbx
  404796:	74 08                	je     4047a0 <get_filename_ext+0x20>
    return dot + 1;
  404798:	48 83 c0 01          	add    $0x1,%rax
}
  40479c:	5b                   	pop    %rbx
  40479d:	c3                   	ret
  40479e:	66 90                	xchg   %ax,%ax
        return "";
  4047a0:	48 8d 05 4f 29 00 00 	lea    0x294f(%rip),%rax        # 4070f6 <_IO_stdin_used+0xf6>
}
  4047a7:	5b                   	pop    %rbx
  4047a8:	c3                   	ret
  4047a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000004047b0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
  4047b0:	41 55                	push   %r13
  4047b2:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  4047b5:	48 89 fe             	mov    %rdi,%rsi
  4047b8:	41 54                	push   %r12
  return __builtin___memcpy_chk (__dest, __src, __len,
  4047ba:	41 bc 31 0d 00 00    	mov    $0xd31,%r12d
  4047c0:	55                   	push   %rbp
  4047c1:	53                   	push   %rbx
  4047c2:	48 89 d3             	mov    %rdx,%rbx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  4047c5:	ba 00 04 00 00       	mov    $0x400,%edx
  4047ca:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
  4047d1:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4047da:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
  4047e2:	31 c0                	xor    %eax,%eax
  4047e4:	48 89 e5             	mov    %rsp,%rbp
  4047e7:	48 89 ef             	mov    %rbp,%rdi
  4047ea:	e8 d1 d9 ff ff       	call   4021c0 <__strcpy_chk@plt>
    strtolower(small_case_path);
  4047ef:	48 89 ef             	mov    %rbp,%rdi
  4047f2:	e8 09 ff ff ff       	call   404700 <strtolower>
    iov[0].iov_base = zh_malloc(slen);
  4047f7:	bf 11 00 00 00       	mov    $0x11,%edi
  4047fc:	e8 3f ff ff ff       	call   404740 <zh_malloc>
    iov[0].iov_len = slen;
  404801:	48 c7 43 08 11 00 00 00 	movq   $0x11,0x8(%rbx)
    iov[1].iov_base = zh_malloc(slen);
  404809:	bf 17 00 00 00       	mov    $0x17,%edi
  return __builtin___memcpy_chk (__dest, __src, __len,
  40480e:	66 0f 6f 05 da 33 00 00 	movdqa 0x33da(%rip),%xmm0        # 407bf0 <_IO_stdin_used+0xbf0>
    iov[0].iov_base = zh_malloc(slen);
  404816:	48 89 03             	mov    %rax,(%rbx)
  404819:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
  40481d:	0f 11 00             	movups %xmm0,(%rax)
    iov[1].iov_base = zh_malloc(slen);
  404820:	e8 1b ff ff ff       	call   404740 <zh_malloc>
    iov[1].iov_len = slen;
  404825:	48 c7 43 18 17 00 00 00 	movq   $0x17,0x18(%rbx)
  40482d:	66 0f 6f 05 cb 33 00 00 	movdqa 0x33cb(%rip),%xmm0        # 407c00 <_IO_stdin_used+0xc00>
    const char *file_ext = get_filename_ext(small_case_path);
  404835:	48 89 ef             	mov    %rbp,%rdi
    iov[1].iov_base = zh_malloc(slen);
  404838:	48 89 43 10          	mov    %rax,0x10(%rbx)
  40483c:	c7 40 10 64 2f 30 2e 	movl   $0x2e302f64,0x10(%rax)
  404843:	66 44 89 60 14       	mov    %r12w,0x14(%rax)
  404848:	c6 40 16 0a          	movb   $0xa,0x16(%rax)
  40484c:	0f 11 00             	movups %xmm0,(%rax)
    const char *file_ext = get_filename_ext(small_case_path);
  40484f:	e8 2c ff ff ff       	call   404780 <get_filename_ext>
    if (strcmp("jpg", file_ext) == 0)
  404854:	48 8d 3d 69 28 00 00 	lea    0x2869(%rip),%rdi        # 4070c4 <_IO_stdin_used+0xc4>
  40485b:	48 89 c6             	mov    %rax,%rsi
    const char *file_ext = get_filename_ext(small_case_path);
  40485e:	48 89 c5             	mov    %rax,%rbp
    if (strcmp("jpg", file_ext) == 0)
  404861:	e8 da d8 ff ff       	call   402140 <strcmp@plt>
  404866:	85 c0                	test   %eax,%eax
  404868:	0f 84 42 03 00 00    	je     404bb0 <send_headers+0x400>
    if (strcmp("jpeg", file_ext) == 0)
  40486e:	48 89 ee             	mov    %rbp,%rsi
  404871:	48 8d 3d 50 28 00 00 	lea    0x2850(%rip),%rdi        # 4070c8 <_IO_stdin_used+0xc8>
  404878:	e8 c3 d8 ff ff       	call   402140 <strcmp@plt>
  40487d:	85 c0                	test   %eax,%eax
  40487f:	0f 84 eb 02 00 00    	je     404b70 <send_headers+0x3c0>
    if (strcmp("png", file_ext) == 0)
  404885:	48 89 ee             	mov    %rbp,%rsi
  404888:	48 8d 3d 3e 28 00 00 	lea    0x283e(%rip),%rdi        # 4070cd <_IO_stdin_used+0xcd>
  40488f:	e8 ac d8 ff ff       	call   402140 <strcmp@plt>
  404894:	85 c0                	test   %eax,%eax
  404896:	0f 84 04 04 00 00    	je     404ca0 <send_headers+0x4f0>
    if (strcmp("gif", file_ext) == 0)
  40489c:	48 89 ee             	mov    %rbp,%rsi
  40489f:	48 8d 3d 2b 28 00 00 	lea    0x282b(%rip),%rdi        # 4070d1 <_IO_stdin_used+0xd1>
  4048a6:	e8 95 d8 ff ff       	call   402140 <strcmp@plt>
  4048ab:	85 c0                	test   %eax,%eax
  4048ad:	0f 84 ad 03 00 00    	je     404c60 <send_headers+0x4b0>
    if (strcmp("htm", file_ext) == 0)
  4048b3:	48 89 ee             	mov    %rbp,%rsi
  4048b6:	48 8d 3d 18 28 00 00 	lea    0x2818(%rip),%rdi        # 4070d5 <_IO_stdin_used+0xd5>
  4048bd:	e8 7e d8 ff ff       	call   402140 <strcmp@plt>
  4048c2:	85 c0                	test   %eax,%eax
  4048c4:	0f 84 5e 03 00 00    	je     404c28 <send_headers+0x478>
    if (strcmp("html", file_ext) == 0)
  4048ca:	48 89 ee             	mov    %rbp,%rsi
  4048cd:	48 8d 3d 44 28 00 00 	lea    0x2844(%rip),%rdi        # 407118 <_IO_stdin_used+0x118>
  4048d4:	e8 67 d8 ff ff       	call   402140 <strcmp@plt>
  4048d9:	85 c0                	test   %eax,%eax
  4048db:	0f 84 0f 03 00 00    	je     404bf0 <send_headers+0x440>
    if (strcmp("js", file_ext) == 0)
  4048e1:	80 7d 00 6a          	cmpb   $0x6a,0x0(%rbp)
  4048e5:	75 0a                	jne    4048f1 <send_headers+0x141>
  4048e7:	80 7d 01 73          	cmpb   $0x73,0x1(%rbp)
  4048eb:	0f 84 b7 01 00 00    	je     404aa8 <send_headers+0x2f8>
    if (strcmp("css", file_ext) == 0)
  4048f1:	48 89 ee             	mov    %rbp,%rsi
  4048f4:	48 8d 3d de 27 00 00 	lea    0x27de(%rip),%rdi        # 4070d9 <_IO_stdin_used+0xd9>
  4048fb:	e8 40 d8 ff ff       	call   402140 <strcmp@plt>
  404900:	85 c0                	test   %eax,%eax
  404902:	0f 84 f8 01 00 00    	je     404b00 <send_headers+0x350>
    if (strcmp("txt", file_ext) == 0)
  404908:	48 89 ee             	mov    %rbp,%rsi
  40490b:	48 8d 3d cb 27 00 00 	lea    0x27cb(%rip),%rdi        # 4070dd <_IO_stdin_used+0xdd>
  404912:	e8 29 d8 ff ff       	call   402140 <strcmp@plt>
  404917:	85 c0                	test   %eax,%eax
  404919:	0f 84 11 02 00 00    	je     404b30 <send_headers+0x380>
    slen = strlen(send_buffer);
  40491f:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
  404927:	4c 89 e7             	mov    %r12,%rdi
  40492a:	e8 71 d7 ff ff       	call   4020a0 <strlen@plt>
    iov[2].iov_base = zh_malloc(slen);
  40492f:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
  404932:	48 89 c5             	mov    %rax,%rbp
    iov[2].iov_base = zh_malloc(slen);
  404935:	e8 06 fe ff ff       	call   404740 <zh_malloc>
    iov[2].iov_len = slen;
  40493a:	48 89 6b 28          	mov    %rbp,0x28(%rbx)
    iov[2].iov_base = zh_malloc(slen);
  40493e:	48 89 43 20          	mov    %rax,0x20(%rbx)
  404942:	83 fd 08             	cmp    $0x8,%ebp
  404945:	73 31                	jae    404978 <send_headers+0x1c8>
  404947:	40 f6 c5 04          	test   $0x4,%bpl
  40494b:	0f 85 8f 03 00 00    	jne    404ce0 <send_headers+0x530>
  404951:	85 ed                	test   %ebp,%ebp
  404953:	74 55                	je     4049aa <send_headers+0x1fa>
  404955:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
  40495d:	88 10                	mov    %dl,(%rax)
  40495f:	40 f6 c5 02          	test   $0x2,%bpl
  404963:	74 45                	je     4049aa <send_headers+0x1fa>
  404965:	89 ed                	mov    %ebp,%ebp
  404967:	41 0f b7 54 2c fe    	movzwl -0x2(%r12,%rbp,1),%edx
  40496d:	66 89 54 28 fe       	mov    %dx,-0x2(%rax,%rbp,1)
  404972:	eb 36                	jmp    4049aa <send_headers+0x1fa>
  404974:	0f 1f 40 00          	nopl   0x0(%rax)
  404978:	48 8b 94 24 00 04 00 00 	mov    0x400(%rsp),%rdx
  404980:	48 8d 78 08          	lea    0x8(%rax),%rdi
  404984:	4c 89 e6             	mov    %r12,%rsi
  404987:	48 83 e7 f8          	and    $0xfffffffffffffff8,%rdi
  40498b:	48 89 10             	mov    %rdx,(%rax)
  40498e:	89 ea                	mov    %ebp,%edx
  404990:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
  404995:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
  40499a:	48 29 f8             	sub    %rdi,%rax
  40499d:	8d 4c 05 00          	lea    0x0(%rbp,%rax,1),%ecx
  4049a1:	48 29 c6             	sub    %rax,%rsi
  4049a4:	c1 e9 03             	shr    $0x3,%ecx
  4049a7:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  4049aa:	4d 89 e8             	mov    %r13,%r8
  4049ad:	48 8d 0d 2d 27 00 00 	lea    0x272d(%rip),%rcx        # 4070e1 <_IO_stdin_used+0xe1>
  4049b4:	4c 89 e7             	mov    %r12,%rdi
  4049b7:	31 c0                	xor    %eax,%eax
  4049b9:	ba 00 04 00 00       	mov    $0x400,%edx
  4049be:	be 01 00 00 00       	mov    $0x1,%esi
  4049c3:	e8 08 d9 ff ff       	call   4022d0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
  4049c8:	4c 89 e7             	mov    %r12,%rdi
  4049cb:	e8 d0 d6 ff ff       	call   4020a0 <strlen@plt>
    iov[3].iov_base = zh_malloc(slen);
  4049d0:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
  4049d3:	48 89 c5             	mov    %rax,%rbp
    iov[3].iov_base = zh_malloc(slen);
  4049d6:	e8 65 fd ff ff       	call   404740 <zh_malloc>
    iov[3].iov_len = slen;
  4049db:	48 89 6b 38          	mov    %rbp,0x38(%rbx)
    iov[3].iov_base = zh_malloc(slen);
  4049df:	48 89 43 30          	mov    %rax,0x30(%rbx)
  4049e3:	83 fd 08             	cmp    $0x8,%ebp
  4049e6:	73 30                	jae    404a18 <send_headers+0x268>
  4049e8:	40 f6 c5 04          	test   $0x4,%bpl
  4049ec:	0f 85 0e 03 00 00    	jne    404d00 <send_headers+0x550>
  4049f2:	85 ed                	test   %ebp,%ebp
  4049f4:	74 54                	je     404a4a <send_headers+0x29a>
  4049f6:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
  4049fe:	88 10                	mov    %dl,(%rax)
  404a00:	40 f6 c5 02          	test   $0x2,%bpl
  404a04:	74 44                	je     404a4a <send_headers+0x29a>
  404a06:	89 ed                	mov    %ebp,%ebp
  404a08:	41 0f b7 54 2c fe    	movzwl -0x2(%r12,%rbp,1),%edx
  404a0e:	66 89 54 28 fe       	mov    %dx,-0x2(%rax,%rbp,1)
  404a13:	eb 35                	jmp    404a4a <send_headers+0x29a>
  404a15:	0f 1f 00             	nopl   (%rax)
  404a18:	48 8b 94 24 00 04 00 00 	mov    0x400(%rsp),%rdx
  404a20:	48 8d 78 08          	lea    0x8(%rax),%rdi
  404a24:	4c 89 e6             	mov    %r12,%rsi
  404a27:	48 83 e7 f8          	and    $0xfffffffffffffff8,%rdi
  404a2b:	48 89 10             	mov    %rdx,(%rax)
  404a2e:	89 ea                	mov    %ebp,%edx
  404a30:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
  404a35:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
  404a3a:	48 29 f8             	sub    %rdi,%rax
  404a3d:	8d 4c 05 00          	lea    0x0(%rbp,%rax,1),%ecx
  404a41:	48 29 c6             	sub    %rax,%rsi
  404a44:	c1 e9 03             	shr    $0x3,%ecx
  404a47:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404a4a:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    iov[4].iov_base = zh_malloc(slen);
  404a4f:	bf 02 00 00 00       	mov    $0x2,%edi
  404a54:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
  404a5c:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
  404a64:	e8 d7 fc ff ff       	call   404740 <zh_malloc>
  404a69:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_len = slen;
  404a71:	48 c7 43 48 02 00 00 00 	movq   $0x2,0x48(%rbx)
    iov[4].iov_base = zh_malloc(slen);
  404a79:	48 89 43 40          	mov    %rax,0x40(%rbx)
  return __builtin___memcpy_chk (__dest, __src, __len,
  404a7d:	66 89 10             	mov    %dx,(%rax)
}
  404a80:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
  404a88:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  404a91:	0f 85 82 02 00 00    	jne    404d19 <send_headers+0x569>
  404a97:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
  404a9e:	5b                   	pop    %rbx
  404a9f:	5d                   	pop    %rbp
  404aa0:	41 5c                	pop    %r12
  404aa2:	41 5d                	pop    %r13
  404aa4:	c3                   	ret
  404aa5:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
  404aa8:	80 7d 02 00          	cmpb   $0x0,0x2(%rbp)
  404aac:	0f 85 3f fe ff ff    	jne    4048f1 <send_headers+0x141>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404ab2:	66 0f 6f 05 76 31 00 00 	movdqa 0x3176(%rip),%xmm0        # 407c30 <_IO_stdin_used+0xc30>
  404aba:	b9 0d 0a 00 00       	mov    $0xa0d,%ecx
  404abf:	c7 84 24 20 04 00 00 72 69 70 74 	movl   $0x74706972,0x420(%rsp)
  404aca:	66 89 8c 24 24 04 00 00 	mov    %cx,0x424(%rsp)
  404ad2:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404ada:	66 0f 6f 05 5e 31 00 00 	movdqa 0x315e(%rip),%xmm0        # 407c40 <_IO_stdin_used+0xc40>
  404ae2:	c6 84 24 26 04 00 00 00 	movb   $0x0,0x426(%rsp)
  404aea:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
  404af2:	e9 fa fd ff ff       	jmp    4048f1 <send_headers+0x141>
  404af7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  404b00:	66 0f 6f 05 18 31 00 00 	movdqa 0x3118(%rip),%xmm0        # 407c20 <_IO_stdin_used+0xc20>
  404b08:	c6 84 24 18 04 00 00 00 	movb   $0x0,0x418(%rsp)
  404b10:	48 b8 78 74 2f 63 73 73 0d 0a 	movabs $0xa0d7373632f7478,%rax
  404b1a:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404b22:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404b2a:	e9 d9 fd ff ff       	jmp    404908 <send_headers+0x158>
  404b2f:	90                   	nop
  404b30:	66 0f 6f 05 e8 30 00 00 	movdqa 0x30e8(%rip),%xmm0        # 407c20 <_IO_stdin_used+0xc20>
  404b38:	ba 0d 0a 00 00       	mov    $0xa0d,%edx
  404b3d:	48 b8 78 74 2f 70 6c 61 69 6e 	movabs $0x6e69616c702f7478,%rax
  404b47:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  404b4f:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404b57:	66 89 94 24 18 04 00 00 	mov    %dx,0x418(%rsp)
  404b5f:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404b67:	e9 b3 fd ff ff       	jmp    40491f <send_headers+0x16f>
  404b6c:	0f 1f 40 00          	nopl   0x0(%rax)
  404b70:	66 0f 6f 05 98 30 00 00 	movdqa 0x3098(%rip),%xmm0        # 407c10 <_IO_stdin_used+0xc10>
  404b78:	41 ba 0d 0a 00 00    	mov    $0xa0d,%r10d
  404b7e:	48 b8 61 67 65 2f 6a 70 65 67 	movabs $0x6765706a2f656761,%rax
  404b88:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  404b90:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404b98:	66 44 89 94 24 18 04 00 00 	mov    %r10w,0x418(%rsp)
  404ba1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404ba9:	e9 d7 fc ff ff       	jmp    404885 <send_headers+0xd5>
  404bae:	66 90                	xchg   %ax,%ax
  404bb0:	66 0f 6f 05 58 30 00 00 	movdqa 0x3058(%rip),%xmm0        # 407c10 <_IO_stdin_used+0xc10>
  404bb8:	41 bb 0d 0a 00 00    	mov    $0xa0d,%r11d
  404bbe:	48 b8 61 67 65 2f 6a 70 65 67 	movabs $0x6765706a2f656761,%rax
  404bc8:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  404bd0:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404bd8:	66 44 89 9c 24 18 04 00 00 	mov    %r11w,0x418(%rsp)
  404be1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404be9:	e9 80 fc ff ff       	jmp    40486e <send_headers+0xbe>
  404bee:	66 90                	xchg   %ax,%ax
  404bf0:	66 0f 6f 05 28 30 00 00 	movdqa 0x3028(%rip),%xmm0        # 407c20 <_IO_stdin_used+0xc20>
  404bf8:	be 0a 00 00 00       	mov    $0xa,%esi
  404bfd:	48 b8 78 74 2f 68 74 6d 6c 0d 	movabs $0xd6c6d74682f7478,%rax
  404c07:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404c0f:	66 89 b4 24 18 04 00 00 	mov    %si,0x418(%rsp)
  404c17:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404c1f:	e9 bd fc ff ff       	jmp    4048e1 <send_headers+0x131>
  404c24:	0f 1f 40 00          	nopl   0x0(%rax)
  404c28:	66 0f 6f 05 f0 2f 00 00 	movdqa 0x2ff0(%rip),%xmm0        # 407c20 <_IO_stdin_used+0xc20>
  404c30:	bf 0a 00 00 00       	mov    $0xa,%edi
  404c35:	48 b8 78 74 2f 68 74 6d 6c 0d 	movabs $0xd6c6d74682f7478,%rax
  404c3f:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404c47:	66 89 bc 24 18 04 00 00 	mov    %di,0x418(%rsp)
  404c4f:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404c57:	e9 6e fc ff ff       	jmp    4048ca <send_headers+0x11a>
  404c5c:	0f 1f 40 00          	nopl   0x0(%rax)
  404c60:	66 0f 6f 05 a8 2f 00 00 	movdqa 0x2fa8(%rip),%xmm0        # 407c10 <_IO_stdin_used+0xc10>
  404c68:	41 b8 0a 00 00 00    	mov    $0xa,%r8d
  404c6e:	48 b8 61 67 65 2f 67 69 66 0d 	movabs $0xd6669672f656761,%rax
  404c78:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404c80:	66 44 89 84 24 18 04 00 00 	mov    %r8w,0x418(%rsp)
  404c89:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404c91:	e9 1d fc ff ff       	jmp    4048b3 <send_headers+0x103>
  404c96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  404ca0:	66 0f 6f 05 68 2f 00 00 	movdqa 0x2f68(%rip),%xmm0        # 407c10 <_IO_stdin_used+0xc10>
  404ca8:	41 b9 0a 00 00 00    	mov    $0xa,%r9d
  404cae:	48 b8 61 67 65 2f 70 6e 67 0d 	movabs $0xd676e702f656761,%rax
  404cb8:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404cc0:	66 44 89 8c 24 18 04 00 00 	mov    %r9w,0x418(%rsp)
  404cc9:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404cd1:	e9 c6 fb ff ff       	jmp    40489c <send_headers+0xec>
  404cd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
  404ce0:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
  404ce7:	89 ed                	mov    %ebp,%ebp
  404ce9:	89 10                	mov    %edx,(%rax)
  404ceb:	41 8b 54 2c fc       	mov    -0x4(%r12,%rbp,1),%edx
  404cf0:	89 54 28 fc          	mov    %edx,-0x4(%rax,%rbp,1)
  404cf4:	e9 b1 fc ff ff       	jmp    4049aa <send_headers+0x1fa>
  404cf9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  404d00:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
  404d07:	89 ed                	mov    %ebp,%ebp
  404d09:	89 10                	mov    %edx,(%rax)
  404d0b:	41 8b 54 2c fc       	mov    -0x4(%r12,%rbp,1),%edx
  404d10:	89 54 28 fc          	mov    %edx,-0x4(%rax,%rbp,1)
  404d14:	e9 31 fd ff ff       	jmp    404a4a <send_headers+0x29a>
}
  404d19:	e8 92 d3 ff ff       	call   4020b0 <__stack_chk_fail@plt>
  404d1e:	66 90                	xchg   %ax,%ax

0000000000404d20 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
  404d20:	41 55                	push   %r13
  404d22:	41 54                	push   %r12
  404d24:	49 89 d4             	mov    %rdx,%r12
  404d27:	55                   	push   %rbp
  404d28:	48 89 fd             	mov    %rdi,%rbp
    char *buf = zh_malloc(file_size);
  404d2b:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
  404d2e:	53                   	push   %rbx
  404d2f:	48 89 f3             	mov    %rsi,%rbx
  404d32:	48 83 ec 08          	sub    $0x8,%rsp
    char *buf = zh_malloc(file_size);
  404d36:	e8 05 fa ff ff       	call   404740 <zh_malloc>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
  404d3b:	48 89 ef             	mov    %rbp,%rdi
  404d3e:	31 f6                	xor    %esi,%esi
  404d40:	49 89 c5             	mov    %rax,%r13
  404d43:	31 c0                	xor    %eax,%eax
  404d45:	e8 c6 d4 ff ff       	call   402210 <open@plt>
  404d4a:	89 c5                	mov    %eax,%ebp
    if (fd < 0)
  404d4c:	85 c0                	test   %eax,%eax
  404d4e:	78 58                	js     404da8 <copy_file_contents+0x88>
		       "the destination buffer");

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
  404d50:	48 89 da             	mov    %rbx,%rdx
  404d53:	4c 89 ee             	mov    %r13,%rsi
  404d56:	89 ef                	mov    %ebp,%edi
  404d58:	e8 c3 d3 ff ff       	call   402120 <read@plt>
    if (ret < file_size) {
  404d5d:	48 98                	cltq
  404d5f:	48 39 d8             	cmp    %rbx,%rax
  404d62:	7c 1c                	jl     404d80 <copy_file_contents+0x60>
    close(fd);
  404d64:	89 ef                	mov    %ebp,%edi
  404d66:	e8 95 d3 ff ff       	call   402100 <close@plt>
    iov->iov_base = buf;
  404d6b:	4d 89 2c 24          	mov    %r13,(%r12)
    iov->iov_len = file_size;
  404d6f:	49 89 5c 24 08       	mov    %rbx,0x8(%r12)
}
  404d74:	48 83 c4 08          	add    $0x8,%rsp
  404d78:	5b                   	pop    %rbx
  404d79:	5d                   	pop    %rbp
  404d7a:	41 5c                	pop    %r12
  404d7c:	41 5d                	pop    %r13
  404d7e:	c3                   	ret
  404d7f:	90                   	nop
        fprintf(stderr, "Encountered a short read.\n");
  404d80:	48 8b 05 71 52 00 00 	mov    0x5271(%rip),%rax        # 409ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  404d87:	ba 1a 00 00 00       	mov    $0x1a,%edx
  404d8c:	be 01 00 00 00       	mov    $0x1,%esi
  404d91:	48 8d 3d 5f 23 00 00 	lea    0x235f(%rip),%rdi        # 4070f7 <_IO_stdin_used+0xf7>
  404d98:	48 8b 08             	mov    (%rax),%rcx
  404d9b:	e8 c0 d4 ff ff       	call   402260 <fwrite@plt>
  404da0:	eb c2                	jmp    404d64 <copy_file_contents+0x44>
  404da2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        fatal_error("read");
  404da8:	48 8d 3d 77 24 00 00 	lea    0x2477(%rip),%rdi        # 407226 <_IO_stdin_used+0x226>
  404daf:	e8 2c f9 ff ff       	call   4046e0 <fatal_error>
  404db4:	eb 9a                	jmp    404d50 <copy_file_contents+0x30>
  404db6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000404dc0 <add_write_request>:
 * Returns a vacant sqe, or NULL if we're full.
 */
static inline struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  404dc0:	48 8b 06             	mov    (%rsi),%rax
int add_write_request(struct Request *req, struct io_uring *ring) {
  404dc3:	48 89 fa             	mov    %rdi,%rdx
  404dc6:	48 89 f7             	mov    %rsi,%rdi
  404dc9:	44 8b 00             	mov    (%rax),%r8d
	unsigned int next = sq->sqe_tail + 1;
  404dcc:	8b 46 44             	mov    0x44(%rsi),%eax
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
  404dcf:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int next = sq->sqe_tail + 1;
  404dd5:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;

	if (next - head <= *sq->kring_entries) {
  404dd8:	41 89 f1             	mov    %esi,%r9d
  404ddb:	45 29 c1             	sub    %r8d,%r9d
  404dde:	4c 8b 47 18          	mov    0x18(%rdi),%r8
  404de2:	45 3b 08             	cmp    (%r8),%r9d
  404de5:	0f 87 05 d5 ff ff    	ja     4022f0 <add_write_request.cold>
  404deb:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404def:	4c 8b 47 10          	mov    0x10(%rdi),%r8
	if (ring->flags & IORING_SETUP_SQE128)
  404df3:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  404df6:	66 0f ef c0          	pxor   %xmm0,%xmm0
	if (ring->flags & IORING_SETUP_SQE128)
  404dfa:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404dfd:	41 23 00             	and    (%r8),%eax
		sq->sqe_tail = next;
  404e00:	89 77 44             	mov    %esi,0x44(%rdi)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404e03:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
  404e05:	8b 72 08             	mov    0x8(%rdx),%esi
  404e08:	8b 4a 04             	mov    0x4(%rdx),%ecx
  404e0b:	48 c1 e0 06          	shl    $0x6,%rax
  404e0f:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
  404e13:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
  404e19:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
  404e1c:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
  404e20:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
  404e26:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
  404e2e:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
  404e32:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
  404e35:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
  404e3c:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  404e44:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
  404e48:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
  404e4c:	e8 6f d2 ff ff       	call   4020c0 <io_uring_submit@plt>
}
  404e51:	31 c0                	xor    %eax,%eax
  404e53:	48 83 c4 08          	add    $0x8,%rsp
  404e57:	c3                   	ret
  404e58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000404e60 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
  404e60:	41 55                	push   %r13
  404e62:	41 54                	push   %r12
  404e64:	55                   	push   %rbp
  404e65:	48 89 f5             	mov    %rsi,%rbp
  404e68:	53                   	push   %rbx
  404e69:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  404e6d:	48 8b 06             	mov    (%rsi),%rax
  404e70:	8b 10                	mov    (%rax),%edx
	unsigned int next = sq->sqe_tail + 1;
  404e72:	8b 5e 44             	mov    0x44(%rsi),%ebx
	if (ring->flags & IORING_SETUP_SQE128)
  404e75:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
	unsigned int next = sq->sqe_tail + 1;
  404e7b:	8d 43 01             	lea    0x1(%rbx),%eax
	if (next - head <= *sq->kring_entries) {
  404e7e:	89 c6                	mov    %eax,%esi
  404e80:	29 d6                	sub    %edx,%esi
  404e82:	48 8b 55 18          	mov    0x18(%rbp),%rdx
  404e86:	3b 32                	cmp    (%rdx),%esi
  404e88:	0f 87 72 d4 ff ff    	ja     402300 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404e8e:	48 8b 55 10          	mov    0x10(%rbp),%rdx
	if (ring->flags & IORING_SETUP_SQE128)
  404e92:	c1 e9 0a             	shr    $0xa,%ecx
  404e95:	41 89 fd             	mov    %edi,%r13d
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
  404e98:	bf 20 00 00 00       	mov    $0x20,%edi
  404e9d:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404ea0:	23 1a                	and    (%rdx),%ebx
		sq->sqe_tail = next;
  404ea2:	89 45 44             	mov    %eax,0x44(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404ea5:	d3 e3                	shl    %cl,%ebx
  404ea7:	48 c1 e3 06          	shl    $0x6,%rbx
  404eab:	48 03 5d 38          	add    0x38(%rbp),%rbx
  404eaf:	e8 ec d2 ff ff       	call   4021a0 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
  404eb4:	be 01 00 00 00       	mov    $0x1,%esi
  404eb9:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
  404ebe:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
  404ec1:	e8 6a d2 ff ff       	call   402130 <calloc@plt>
    req->client_socket = client_socket;
  404ec6:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
  404ecb:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
  404ecf:	48 89 ef             	mov    %rbp,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
  404ed2:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
  404ed7:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
  404edc:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
  404ee5:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
  404eed:	44 89 6b 04          	mov    %r13d,0x4(%rbx)
	sqe->user_data = (unsigned long) data;
  404ef1:	4c 89 63 20          	mov    %r12,0x20(%rbx)
	sqe->opcode = (__u8) op;
  404ef5:	c7 03 01 00 00 00    	movl   $0x1,(%rbx)
	sqe->off = offset;
  404efb:	48 c7 43 08 00 00 00 00 	movq   $0x0,0x8(%rbx)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
  404f03:	48 89 43 10          	mov    %rax,0x10(%rbx)
	sqe->len = len;
  404f07:	48 c7 43 18 01 00 00 00 	movq   $0x1,0x18(%rbx)
	sqe->buf_index = 0;
  404f0f:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->addr3 = 0;
  404f17:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
    io_uring_submit(ring);
  404f1b:	e8 a0 d1 ff ff       	call   4020c0 <io_uring_submit@plt>
}
  404f20:	48 83 c4 08          	add    $0x8,%rsp
  404f24:	31 c0                	xor    %eax,%eax
  404f26:	5b                   	pop    %rbx
  404f27:	5d                   	pop    %rbp
  404f28:	41 5c                	pop    %r12
  404f2a:	41 5d                	pop    %r13
  404f2c:	c3                   	ret
  404f2d:	0f 1f 00             	nopl   (%rax)

0000000000404f30 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
  404f30:	41 56                	push   %r14
  404f32:	49 89 d6             	mov    %rdx,%r14
  404f35:	41 55                	push   %r13
  404f37:	49 89 fd             	mov    %rdi,%r13
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  404f3a:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
  404f3f:	41 54                	push   %r12
  404f41:	55                   	push   %rbp
  404f42:	53                   	push   %rbx
  404f43:	89 f3                	mov    %esi,%ebx
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  404f45:	e8 f6 f7 ff ff       	call   404740 <zh_malloc>
    unsigned long slen = strlen(str);
  404f4a:	4c 89 ef             	mov    %r13,%rdi
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  404f4d:	48 89 c5             	mov    %rax,%rbp
    unsigned long slen = strlen(str);
  404f50:	e8 4b d1 ff ff       	call   4020a0 <strlen@plt>
    req->client_socket = client_socket;
  404f55:	89 5d 08             	mov    %ebx,0x8(%rbp)
    req->iovec_count = 1;
  404f58:	c7 45 04 01 00 00 00 	movl   $0x1,0x4(%rbp)
    req->iov[0].iov_base = zh_malloc(slen);
  404f5f:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
  404f62:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = zh_malloc(slen);
  404f65:	e8 d6 f7 ff ff       	call   404740 <zh_malloc>
    req->iov[0].iov_len = slen;
  404f6a:	4c 89 65 18          	mov    %r12,0x18(%rbp)
  404f6e:	4c 89 ee             	mov    %r13,%rsi
  404f71:	4c 89 e2             	mov    %r12,%rdx
    req->iov[0].iov_base = zh_malloc(slen);
  404f74:	48 89 45 10          	mov    %rax,0x10(%rbp)
  404f78:	48 89 c7             	mov    %rax,%rdi
  404f7b:	e8 f0 d1 ff ff       	call   402170 <memcpy@plt>
}
  404f80:	5b                   	pop    %rbx
    add_write_request(req, ring);
  404f81:	4c 89 f6             	mov    %r14,%rsi
  404f84:	48 89 ef             	mov    %rbp,%rdi
}
  404f87:	5d                   	pop    %rbp
  404f88:	41 5c                	pop    %r12
  404f8a:	41 5d                	pop    %r13
  404f8c:	41 5e                	pop    %r14
    add_write_request(req, ring);
  404f8e:	e9 2d fe ff ff       	jmp    404dc0 <add_write_request>
  404f93:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  404f9e:	66 90                	xchg   %ax,%ax

0000000000404fa0 <handle_unimplemented_method>:
    _send_static_string_content(unimplemented_content, client_socket, ring);
  404fa0:	48 c7 c0 18 a0 40 00 	mov    $0x40a018,%rax
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
  404fa7:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
  404faa:	89 fe                	mov    %edi,%esi
  404fac:	48 8b 38             	mov    (%rax),%rdi
  404faf:	e9 7c ff ff ff       	jmp    404f30 <_send_static_string_content>
  404fb4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  404fbf:	90                   	nop

0000000000404fc0 <handle_http_404>:
    _send_static_string_content(http_404_content, client_socket, ring);
  404fc0:	48 c7 c0 10 a0 40 00 	mov    $0x40a010,%rax
void handle_http_404(int client_socket, struct io_uring *ring) {
  404fc7:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
  404fca:	89 fe                	mov    %edi,%esi
  404fcc:	48 8b 38             	mov    (%rax),%rdi
  404fcf:	e9 5c ff ff ff       	jmp    404f30 <_send_static_string_content>
  404fd4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  404fdf:	90                   	nop

0000000000404fe0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
  404fe0:	41 56                	push   %r14
  404fe2:	41 55                	push   %r13
  404fe4:	49 89 d5             	mov    %rdx,%r13
  404fe7:	41 54                	push   %r12
  404fe9:	49 89 fc             	mov    %rdi,%r12
  404fec:	55                   	push   %rbp
  404fed:	89 f5                	mov    %esi,%ebp
  404fef:	53                   	push   %rbx
  404ff0:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
  404ff7:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  405000:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
  405008:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
  40500a:	e8 91 d0 ff ff       	call   4020a0 <strlen@plt>
  40500f:	41 80 7c 04 ff 2f    	cmpb   $0x2f,-0x1(%r12,%rax,1)
  405015:	48 89 c3             	mov    %rax,%rbx
  405018:	0f 84 b2 00 00 00    	je     4050d0 <handle_get_method+0xf0>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  40501e:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  405023:	4c 89 e6             	mov    %r12,%rsi
  405026:	48 8d 53 01          	lea    0x1(%rbx),%rdx
  40502a:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  40502f:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
  405037:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  40503f:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  40504a:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  405052:	e8 f9 d0 ff ff       	call   402150 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
  405057:	48 89 e6             	mov    %rsp,%rsi
  40505a:	4c 89 f7             	mov    %r14,%rdi
  40505d:	e8 fe d0 ff ff       	call   402160 <stat@plt>
  405062:	83 f8 ff             	cmp    $0xffffffff,%eax
  405065:	0f 84 cf 00 00 00    	je     40513a <handle_get_method+0x15a>
        if (S_ISREG(path_stat.st_mode)) {
  40506b:	8b 44 24 18          	mov    0x18(%rsp),%eax
  40506f:	25 00 f0 00 00       	and    $0xf000,%eax
  405074:	3d 00 80 00 00       	cmp    $0x8000,%eax
  405079:	0f 84 e9 00 00 00    	je     405168 <handle_get_method+0x188>
            handle_http_404(client_socket, ring);
  40507f:	4c 89 ee             	mov    %r13,%rsi
  405082:	89 ef                	mov    %ebp,%edi
  405084:	e8 37 ff ff ff       	call   404fc0 <handle_http_404>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  405089:	4c 89 f2             	mov    %r14,%rdx
  40508c:	bf 01 00 00 00       	mov    $0x1,%edi
  405091:	31 c0                	xor    %eax,%eax
  405093:	48 8d 35 ad 20 00 00 	lea    0x20ad(%rip),%rsi        # 407147 <_IO_stdin_used+0x147>
  40509a:	e8 41 d1 ff ff       	call   4021e0 <__printf_chk@plt>
}
  40509f:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
  4050a7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4050b0:	0f 85 17 01 00 00    	jne    4051cd <handle_get_method+0x1ed>
  4050b6:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
  4050bd:	5b                   	pop    %rbx
  4050be:	5d                   	pop    %rbp
  4050bf:	41 5c                	pop    %r12
  4050c1:	41 5d                	pop    %r13
  4050c3:	41 5e                	pop    %r14
  4050c5:	c3                   	ret
  4050c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  4050d0:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  4050d5:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
  4050dd:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  4050e2:	4c 89 e6             	mov    %r12,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  4050e5:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  4050ed:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  4050f0:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  4050f8:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  405103:	e8 48 d0 ff ff       	call   402150 <__memcpy_chk@plt>
  405108:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  40510d:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
  405112:	48 8d 35 f9 1f 00 00 	lea    0x1ff9(%rip),%rsi        # 407112 <_IO_stdin_used+0x112>
  405119:	48 29 d9             	sub    %rbx,%rcx
  40511c:	ba 0b 00 00 00       	mov    $0xb,%edx
  405121:	e8 2a d0 ff ff       	call   402150 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
  405126:	48 89 e6             	mov    %rsp,%rsi
  405129:	4c 89 f7             	mov    %r14,%rdi
  40512c:	e8 2f d0 ff ff       	call   402160 <stat@plt>
  405131:	83 f8 ff             	cmp    $0xffffffff,%eax
  405134:	0f 85 31 ff ff ff    	jne    40506b <handle_get_method+0x8b>
  40513a:	4c 89 e1             	mov    %r12,%rcx
  40513d:	4c 89 f2             	mov    %r14,%rdx
  405140:	48 8d 35 d6 1f 00 00 	lea    0x1fd6(%rip),%rsi        # 40711d <_IO_stdin_used+0x11d>
  405147:	31 c0                	xor    %eax,%eax
  405149:	bf 01 00 00 00       	mov    $0x1,%edi
  40514e:	e8 8d d0 ff ff       	call   4021e0 <__printf_chk@plt>
        handle_http_404(client_socket, ring);
  405153:	4c 89 ee             	mov    %r13,%rsi
  405156:	89 ef                	mov    %ebp,%edi
  405158:	e8 63 fe ff ff       	call   404fc0 <handle_http_404>
  40515d:	e9 3d ff ff ff       	jmp    40509f <handle_get_method+0xbf>
  405162:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            struct Request *req = zh_malloc(sizeof(*req) + (sizeof(struct iovec) * 6));
  405168:	bf 70 00 00 00       	mov    $0x70,%edi
  40516d:	e8 ce f5 ff ff       	call   404740 <zh_malloc>
            send_headers(final_path, path_stat.st_size, req->iov);
  405172:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
  405177:	4c 89 f7             	mov    %r14,%rdi
            req->client_socket = client_socket;
  40517a:	89 68 08             	mov    %ebp,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
  40517d:	48 8d 50 10          	lea    0x10(%rax),%rdx
            struct Request *req = zh_malloc(sizeof(*req) + (sizeof(struct iovec) * 6));
  405181:	49 89 c4             	mov    %rax,%r12
            req->iovec_count = 6;
  405184:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
  40518b:	e8 20 f6 ff ff       	call   4047b0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
  405190:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
  405195:	49 8d 54 24 60       	lea    0x60(%r12),%rdx
  40519a:	4c 89 f7             	mov    %r14,%rdi
  40519d:	e8 7e fb ff ff       	call   404d20 <copy_file_contents>
  4051a2:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
  4051a7:	4c 89 f2             	mov    %r14,%rdx
  4051aa:	31 c0                	xor    %eax,%eax
  4051ac:	48 8d 35 82 1f 00 00 	lea    0x1f82(%rip),%rsi        # 407135 <_IO_stdin_used+0x135>
  4051b3:	bf 01 00 00 00       	mov    $0x1,%edi
  4051b8:	e8 23 d0 ff ff       	call   4021e0 <__printf_chk@plt>
            add_write_request(req, ring);
  4051bd:	4c 89 ee             	mov    %r13,%rsi
  4051c0:	4c 89 e7             	mov    %r12,%rdi
  4051c3:	e8 f8 fb ff ff       	call   404dc0 <add_write_request>
  4051c8:	e9 d2 fe ff ff       	jmp    40509f <handle_get_method+0xbf>
}
  4051cd:	e8 de ce ff ff       	call   4020b0 <__stack_chk_fail@plt>
  4051d2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4051dd:	0f 1f 00             	nopl   (%rax)

00000000004051e0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
  4051e0:	41 57                	push   %r15
  4051e2:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
  4051e4:	4c 8d 35 c1 1e 00 00 	lea    0x1ec1(%rip),%r14        # 4070ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
  4051eb:	41 55                	push   %r13
  4051ed:	49 89 d5             	mov    %rdx,%r13
  4051f0:	41 54                	push   %r12
  4051f2:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
  4051f5:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
  4051f8:	55                   	push   %rbp
  4051f9:	48 83 ec 10          	sub    $0x10,%rsp
  4051fd:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  405206:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  40520b:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
  40520d:	49 89 e7             	mov    %rsp,%r15
  405210:	4c 89 fa             	mov    %r15,%rdx
  405213:	e8 f8 ce ff ff       	call   402110 <strtok_r@plt>
    strtolower(method);
  405218:	48 89 c7             	mov    %rax,%rdi
    method = strtok_r(method_buffer, " ", &saveptr);
  40521b:	48 89 c5             	mov    %rax,%rbp
    strtolower(method);
  40521e:	e8 dd f4 ff ff       	call   404700 <strtolower>
    path = strtok_r(NULL, " ", &saveptr);
  405223:	4c 89 f6             	mov    %r14,%rsi
  405226:	31 ff                	xor    %edi,%edi
  405228:	4c 89 fa             	mov    %r15,%rdx
  40522b:	e8 e0 ce ff ff       	call   402110 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
  405230:	48 8d 35 23 1f 00 00 	lea    0x1f23(%rip),%rsi        # 40715a <_IO_stdin_used+0x15a>
  405237:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
  40523a:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
  40523d:	e8 fe ce ff ff       	call   402140 <strcmp@plt>
  405242:	85 c0                	test   %eax,%eax
  405244:	75 32                	jne    405278 <handle_http_method+0x98>
        handle_get_method(path, client_socket, ring);
  405246:	4c 89 ea             	mov    %r13,%rdx
  405249:	44 89 e6             	mov    %r12d,%esi
  40524c:	4c 89 f7             	mov    %r14,%rdi
  40524f:	e8 8c fd ff ff       	call   404fe0 <handle_get_method>
}
  405254:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  405259:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  405262:	75 21                	jne    405285 <handle_http_method+0xa5>
  405264:	48 83 c4 10          	add    $0x10,%rsp
  405268:	5d                   	pop    %rbp
  405269:	41 5c                	pop    %r12
  40526b:	41 5d                	pop    %r13
  40526d:	41 5e                	pop    %r14
  40526f:	41 5f                	pop    %r15
  405271:	c3                   	ret
  405272:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        handle_unimplemented_method(client_socket, ring);
  405278:	4c 89 ee             	mov    %r13,%rsi
  40527b:	44 89 e7             	mov    %r12d,%edi
  40527e:	e8 1d fd ff ff       	call   404fa0 <handle_unimplemented_method>
}
  405283:	eb cf                	jmp    405254 <handle_http_method+0x74>
  405285:	e8 26 ce ff ff       	call   4020b0 <__stack_chk_fail@plt>
  40528a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000405290 <get_line>:
    for (int i = 0; i < dest_sz; i++) {
  405290:	85 d2                	test   %edx,%edx
  405292:	7e 3c                	jle    4052d0 <get_line+0x40>
  405294:	8d 42 ff             	lea    -0x1(%rdx),%eax
  405297:	48 83 c7 01          	add    $0x1,%rdi
  40529b:	48 8d 54 06 01       	lea    0x1(%rsi,%rax,1),%rdx
  4052a0:	eb 13                	jmp    4052b5 <get_line+0x25>
  4052a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  4052a8:	48 83 c6 01          	add    $0x1,%rsi
  4052ac:	48 83 c7 01          	add    $0x1,%rdi
  4052b0:	48 39 d6             	cmp    %rdx,%rsi
  4052b3:	74 1b                	je     4052d0 <get_line+0x40>
        dest[i] = src[i];
  4052b5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
  4052b9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
  4052bb:	3c 0d                	cmp    $0xd,%al
  4052bd:	75 e9                	jne    4052a8 <get_line+0x18>
  4052bf:	80 3f 0a             	cmpb   $0xa,(%rdi)
  4052c2:	75 e4                	jne    4052a8 <get_line+0x18>
            dest[i] = '\0';
  4052c4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
  4052c7:	31 c0                	xor    %eax,%eax
}
  4052c9:	c3                   	ret
  4052ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
  4052d0:	b8 01 00 00 00       	mov    $0x1,%eax
  4052d5:	c3                   	ret
  4052d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004052e0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
  4052e0:	41 54                	push   %r12
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  4052e2:	ba 00 04 00 00       	mov    $0x400,%edx
int handle_client_request(struct Request *req, struct io_uring *ring) {
  4052e7:	49 89 f4             	mov    %rsi,%r12
  4052ea:	55                   	push   %rbp
  4052eb:	53                   	push   %rbx
  4052ec:	48 89 fb             	mov    %rdi,%rbx
  4052ef:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  4052f6:	48 8b 7f 10          	mov    0x10(%rdi),%rdi
int handle_client_request(struct Request *req, struct io_uring *ring) {
  4052fa:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  405303:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
  40530b:	31 c0                	xor    %eax,%eax
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  40530d:	48 89 e5             	mov    %rsp,%rbp
  405310:	48 89 ee             	mov    %rbp,%rsi
  405313:	e8 78 ff ff ff       	call   405290 <get_line>
  405318:	85 c0                	test   %eax,%eax
  40531a:	75 2f                	jne    40534b <handle_client_request+0x6b>
    handle_http_method(http_request, req->client_socket, ring);
  40531c:	8b 73 08             	mov    0x8(%rbx),%esi
  40531f:	4c 89 e2             	mov    %r12,%rdx
  405322:	48 89 ef             	mov    %rbp,%rdi
  405325:	e8 b6 fe ff ff       	call   4051e0 <handle_http_method>
}
  40532a:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
  405332:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40533b:	75 38                	jne    405375 <handle_client_request+0x95>
  40533d:	48 81 c4 10 04 00 00 	add    $0x410,%rsp
  405344:	31 c0                	xor    %eax,%eax
  405346:	5b                   	pop    %rbx
  405347:	5d                   	pop    %rbp
  405348:	41 5c                	pop    %r12
  40534a:	c3                   	ret
        fprintf(stderr, "Malformed request\n");
  40534b:	48 8b 05 a6 4c 00 00 	mov    0x4ca6(%rip),%rax        # 409ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  405352:	ba 12 00 00 00       	mov    $0x12,%edx
  405357:	be 01 00 00 00       	mov    $0x1,%esi
  40535c:	48 8d 3d fb 1d 00 00 	lea    0x1dfb(%rip),%rdi        # 40715e <_IO_stdin_used+0x15e>
  405363:	48 8b 08             	mov    (%rax),%rcx
  405366:	e8 f5 ce ff ff       	call   402260 <fwrite@plt>
        exit(1);
  40536b:	bf 01 00 00 00       	mov    $0x1,%edi
  405370:	e8 cb ce ff ff       	call   402240 <exit@plt>
}
  405375:	e8 36 cd ff ff       	call   4020b0 <__stack_chk_fail@plt>
  40537a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000405380 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
  405380:	55                   	push   %rbp
  405381:	66 48 0f 6e c2       	movq   %rdx,%xmm0
  405386:	66 48 0f 6e ce       	movq   %rsi,%xmm1
  40538b:	48 89 cd             	mov    %rcx,%rbp
  40538e:	53                   	push   %rbx
  40538f:	89 f8                	mov    %edi,%eax
  405391:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
  405395:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  405399:	48 8b 11             	mov    (%rcx),%rdx
  40539c:	8b 32                	mov    (%rdx),%esi
	unsigned int next = sq->sqe_tail + 1;
  40539e:	8b 59 44             	mov    0x44(%rcx),%ebx
	if (ring->flags & IORING_SETUP_SQE128)
  4053a1:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int next = sq->sqe_tail + 1;
  4053a7:	8d 53 01             	lea    0x1(%rbx),%edx
	if (next - head <= *sq->kring_entries) {
  4053aa:	89 d7                	mov    %edx,%edi
  4053ac:	29 f7                	sub    %esi,%edi
  4053ae:	48 8b 75 18          	mov    0x18(%rbp),%rsi
  4053b2:	3b 3e                	cmp    (%rsi),%edi
  4053b4:	0f 87 50 cf ff ff    	ja     40230a <add_accept_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4053ba:	48 8b 75 10          	mov    0x10(%rbp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  4053be:	c1 e9 0a             	shr    $0xa,%ecx
  struct Request *req = malloc(sizeof(*req));
  4053c1:	bf 10 00 00 00       	mov    $0x10,%edi
  4053c6:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4053c9:	23 1e                	and    (%rsi),%ebx
		sq->sqe_tail = next;
  4053cb:	89 55 44             	mov    %edx,0x44(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4053ce:	d3 e3                	shl    %cl,%ebx
  4053d0:	48 c1 e3 06          	shl    $0x6,%rbx
  4053d4:	48 03 5d 38          	add    0x38(%rbp),%rbx
	sqe->opcode = (__u8) op;
  4053d8:	c7 03 0d 00 00 00    	movl   $0xd,(%rbx)
	sqe->fd = fd;
  4053de:	89 43 04             	mov    %eax,0x4(%rbx)
	sqe->buf_index = 0;
  4053e1:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->len = len;
  4053e9:	48 c7 43 18 00 00 00 00 	movq   $0x0,0x18(%rbx)
	sqe->off = offset;
  4053f1:	0f 11 43 08          	movups %xmm0,0x8(%rbx)
	sqe->addr3 = 0;
  4053f5:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4053f9:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
  4053fd:	e8 9e cd ff ff       	call   4021a0 <malloc@plt>
  io_uring_submit(ring);
  405402:	48 89 ef             	mov    %rbp,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
  405405:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
  40540b:	48 89 43 20          	mov    %rax,0x20(%rbx)
}
  40540f:	48 83 c4 08          	add    $0x8,%rsp
  405413:	5b                   	pop    %rbx
  405414:	5d                   	pop    %rbp
  io_uring_submit(ring);
  405415:	e9 a6 cc ff ff       	jmp    4020c0 <io_uring_submit@plt>
  40541a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000405420 <io_thread>:
void* io_thread(void *arg) {
  405420:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  405422:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
  405424:	41 56                	push   %r14
  405426:	41 55                	push   %r13
  405428:	41 54                	push   %r12
  40542a:	55                   	push   %rbp
  40542b:	48 89 fd             	mov    %rdi,%rbp
  40542e:	53                   	push   %rbx
  40542f:	48 81 ec 48 01 00 00 	sub    $0x148,%rsp
  struct io_uring ring = *data->ring;
  405436:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40543f:	48 89 84 24 38 01 00 00 	mov    %rax,0x138(%rsp)
  405447:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  40544b:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
  405450:	bf 00 01 00 00       	mov    $0x100,%edi
  405455:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
  405458:	f3 0f 6f 08          	movdqu (%rax),%xmm1
  40545c:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
  405461:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
  405466:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
  40546b:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
  405470:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
  405478:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
  40547d:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
  405485:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
  40548a:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
  405492:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
  405497:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
  40549f:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
  4054a4:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
  4054ac:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
  4054b1:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
  4054b9:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
  4054c1:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
  4054c9:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
  4054d1:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
  4054d9:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
  4054e1:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
  4054e9:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
  4054f1:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
  4054f9:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
  405501:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
  405509:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
  405510:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  405518:	e8 63 cc ff ff       	call   402180 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
  40551d:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
  405521:	31 f6                	xor    %esi,%esi
  405523:	e8 58 cd ff ff       	call   402280 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
  405528:	31 d2                	xor    %edx,%edx
  40552a:	be 01 00 00 00       	mov    $0x1,%esi
  40552f:	bf 02 00 00 00       	mov    $0x2,%edi
  405534:	e8 a7 cd ff ff       	call   4022e0 <socket@plt>
  405539:	89 44 24 0c          	mov    %eax,0xc(%rsp)
  if (sock == -1)
  40553d:	83 f8 ff             	cmp    $0xffffffff,%eax
  405540:	0f 84 09 05 00 00    	je     405a4f <io_thread+0x62f>
  if (setsockopt(sock,
  405546:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  40554a:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
  40554f:	41 b8 04 00 00 00    	mov    $0x4,%r8d
  405555:	ba 02 00 00 00       	mov    $0x2,%edx
  40555a:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
  40555f:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
  405567:	e8 04 cb ff ff       	call   402070 <setsockopt@plt>
  40556c:	85 c0                	test   %eax,%eax
  40556e:	0f 88 ca 04 00 00    	js     405a3e <io_thread+0x61e>
  if (bind(sock,
  405574:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  return __builtin___memset_chk (__dest, __ch, __len,
  405578:	66 0f ef c0          	pxor   %xmm0,%xmm0
  40557c:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  405581:	ba 10 00 00 00       	mov    $0x10,%edx
  405586:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  srv_addr.sin_family = AF_INET;
  40558b:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
  405593:	e8 58 cc ff ff       	call   4021f0 <bind@plt>
  405598:	85 c0                	test   %eax,%eax
  40559a:	0f 88 8d 04 00 00    	js     405a2d <io_thread+0x60d>
  if (listen(sock, 10) < 0) {
  4055a0:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  4055a4:	be 0a 00 00 00       	mov    $0xa,%esi
  4055a9:	e8 02 cc ff ff       	call   4021b0 <listen@plt>
  4055ae:	85 c0                	test   %eax,%eax
  4055b0:	0f 88 66 04 00 00    	js     405a1c <io_thread+0x5fc>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4055b6:	ba db 18 00 00       	mov    $0x18db,%edx
  4055bb:	48 8d 35 e1 1b 00 00 	lea    0x1be1(%rip),%rsi        # 4071a3 <_IO_stdin_used+0x1a3>
  4055c2:	bf 01 00 00 00       	mov    $0x1,%edi
  4055c7:	31 c0                	xor    %eax,%eax
  4055c9:	e8 12 cc ff ff       	call   4021e0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  4055ce:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
  4055d3:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  4055d7:	48 89 d9             	mov    %rbx,%rcx
  4055da:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
  4055df:	48 89 c6             	mov    %rax,%rsi
  4055e2:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  4055e7:	48 89 54 24 20       	mov    %rdx,0x20(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
  4055ec:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  4055f4:	e8 87 fd ff ff       	call   405380 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
  4055f9:	be 10 00 00 00       	mov    $0x10,%esi
  4055fe:	bf 01 00 00 00       	mov    $0x1,%edi
  405603:	e8 28 cb ff ff       	call   402130 <calloc@plt>
  iov->iov_base = zh_malloc(10);
  405608:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
  40560d:	49 89 c6             	mov    %rax,%r14
  405610:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  iov->iov_base = zh_malloc(10);
  405615:	e8 26 f1 ff ff       	call   404740 <zh_malloc>
  iov->iov_len = 10;
  40561a:	49 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%r14)
  iov->iov_base = zh_malloc(10);
  405622:	49 89 06             	mov    %rax,(%r14)
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  405625:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
  40562a:	8b 30                	mov    (%rax),%esi
	unsigned int next = sq->sqe_tail + 1;
  40562c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  405633:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  40563a:	8d 50 01             	lea    0x1(%rax),%edx
	if (next - head <= *sq->kring_entries) {
  40563d:	89 d7                	mov    %edx,%edi
  40563f:	29 f7                	sub    %esi,%edi
  405641:	48 8b 74 24 78       	mov    0x78(%rsp),%rsi
  405646:	3b 3e                	cmp    (%rsi),%edi
  405648:	0f 87 c6 cc ff ff    	ja     402314 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40564e:	48 8b 74 24 70       	mov    0x70(%rsp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  405653:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  405656:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
  40565a:	48 89 df             	mov    %rbx,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
  40565d:	83 e1 01             	and    $0x1,%ecx
  405660:	4c 8d 25 52 1b 00 00 	lea    0x1b52(%rip),%r12        # 4071b9 <_IO_stdin_used+0x1b9>
  405667:	4c 8d 2d 71 1b 00 00 	lea    0x1b71(%rip),%r13        # 4071df <_IO_stdin_used+0x1df>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40566e:	23 06                	and    (%rsi),%eax
		sq->sqe_tail = next;
  405670:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
  405677:	48 8d 75 60          	lea    0x60(%rbp),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
  40567b:	8b 55 60             	mov    0x60(%rbp),%edx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40567e:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
  405680:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
  405685:	48 c1 e0 06          	shl    $0x6,%rax
  405689:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
  405691:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
  405697:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
  40569a:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
  4056a2:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
  4056a6:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
  4056ae:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  4056b6:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
  4056ba:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
  4056be:	e8 fd c9 ff ff       	call   4020c0 <io_uring_submit@plt>
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
  4056c3:	48 8d 44 24 38       	lea    0x38(%rsp),%rax
  while (data->running == 1) {
  4056c8:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
  4056cc:	48 89 04 24          	mov    %rax,(%rsp)
  4056d0:	0f 85 a6 01 00 00    	jne    40587c <io_thread+0x45c>
  4056d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4056e0:	4c 89 e7             	mov    %r12,%rdi
  4056e3:	e8 78 c9 ff ff       	call   402060 <puts@plt>
	unsigned mask = *ring->cq.kring_mask;
  4056e8:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
	if (ring->flags & IORING_SETUP_CQE32)
  4056f0:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = *ring->cq.kring_mask;
  4056f7:	8b 30                	mov    (%rax),%esi
	if (ring->flags & IORING_SETUP_CQE32)
  4056f9:	c1 e9 0b             	shr    $0xb,%ecx
  4056fc:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
  4056ff:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
  405707:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
  405709:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
  405711:	8b 17                	mov    (%rdi),%edx
		if (!available)
  405713:	39 d0                	cmp    %edx,%eax
  405715:	74 39                	je     405750 <io_thread+0x330>
		cqe = &ring->cq.cqes[(head & mask) << shift];
  405717:	89 f0                	mov    %esi,%eax
  405719:	21 d0                	and    %edx,%eax
  40571b:	d3 e0                	shl    %cl,%eax
  40571d:	48 c1 e0 04          	shl    $0x4,%rax
  405721:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
  405729:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
  405731:	0f 85 81 01 00 00    	jne    4058b8 <io_thread+0x498>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
  405737:	4c 8b 00             	mov    (%rax),%r8
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
  40573a:	49 83 f8 ff          	cmp    $0xffffffffffffffff,%r8
  40573e:	0f 85 9c 02 00 00    	jne    4059e0 <io_thread+0x5c0>
			if (cqe->res < 0)
  405744:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  405747:	83 c2 01             	add    $0x1,%edx
  40574a:	89 17                	mov    %edx,(%rdi)
			if (!err)
  40574c:	85 c0                	test   %eax,%eax
  40574e:	79 af                	jns    4056ff <io_thread+0x2df>
	*cqe_ptr = cqe;
  405750:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
  405759:	48 8b 34 24          	mov    (%rsp),%rsi
  40575d:	45 31 c0             	xor    %r8d,%r8d
  405760:	31 d2                	xor    %edx,%edx
  405762:	b9 01 00 00 00       	mov    $0x1,%ecx
  405767:	48 89 df             	mov    %rbx,%rdi
  40576a:	e8 61 ca ff ff       	call   4021d0 <__io_uring_get_cqe@plt>
  40576f:	41 89 c6             	mov    %eax,%r14d
      if (cqe->user_data == 1) {
  405772:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  405777:	48 83 38 01          	cmpq   $0x1,(%rax)
  40577b:	0f 84 8f 02 00 00    	je     405a10 <io_thread+0x5f0>
  405781:	4c 89 ef             	mov    %r13,%rdi
  405784:	e8 d7 c8 ff ff       	call   402060 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
  405789:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
  40578e:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
  405791:	45 85 f6             	test   %r14d,%r14d
  405794:	79 11                	jns    4057a7 <io_thread+0x387>
          fatal_error("io_uring_wait_cqe");
  405796:	48 8d 3d 59 1a 00 00 	lea    0x1a59(%rip),%rdi        # 4071f6 <_IO_stdin_used+0x1f6>
  40579d:	e8 3e ef ff ff       	call   4046e0 <fatal_error>
      if (cqe->res < 0) {
  4057a2:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
  4057a7:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
  4057aa:	45 8b 07             	mov    (%r15),%r8d
      if (cqe->res < 0) {
  4057ad:	85 c0                	test   %eax,%eax
  4057af:	0f 88 ab 02 00 00    	js     405a60 <io_thread+0x640>
      switch (req->event_type) {
  4057b5:	41 83 f8 01          	cmp    $0x1,%r8d
  4057b9:	0f 84 31 01 00 00    	je     4058f0 <io_thread+0x4d0>
  4057bf:	41 83 f8 02          	cmp    $0x2,%r8d
  4057c3:	0f 84 9f 01 00 00    	je     405968 <io_thread+0x548>
  4057c9:	45 85 c0             	test   %r8d,%r8d
  4057cc:	0f 84 5e 01 00 00    	je     405930 <io_thread+0x510>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  4057d2:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  4057da:	8b 02                	mov    (%rdx),%eax
  4057dc:	83 c0 01             	add    $0x1,%eax
  4057df:	89 02                	mov    %eax,(%rdx)
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  4057e1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
  4057e6:	8b 30                	mov    (%rax),%esi
	unsigned int next = sq->sqe_tail + 1;
  4057e8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  4057ef:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  4057f6:	8d 50 01             	lea    0x1(%rax),%edx
	if (next - head <= *sq->kring_entries) {
  4057f9:	89 d7                	mov    %edx,%edi
  4057fb:	29 f7                	sub    %esi,%edi
  4057fd:	48 8b 74 24 78       	mov    0x78(%rsp),%rsi
  405802:	3b 3e                	cmp    (%rsi),%edi
  405804:	0f 87 0a cb ff ff    	ja     402314 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40580a:	48 8b 74 24 70       	mov    0x70(%rsp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  40580f:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  405812:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
  405816:	48 89 df             	mov    %rbx,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
  405819:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40581c:	23 06                	and    (%rsi),%eax
	sqe->addr = (unsigned long) addr;
  40581e:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
		sq->sqe_tail = next;
  405823:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40582a:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
  40582c:	8b 55 60             	mov    0x60(%rbp),%edx
  40582f:	48 c1 e0 06          	shl    $0x6,%rax
  405833:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->addr = (unsigned long) addr;
  40583b:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->user_data = (unsigned long) data;
  40583f:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
	sqe->opcode = (__u8) op;
  405844:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
  40584a:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
  40584d:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->len = len;
  405855:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
  40585d:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  405865:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
  405869:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
  40586d:	e8 4e c8 ff ff       	call   4020c0 <io_uring_submit@plt>
  while (data->running == 1) {
  405872:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
  405876:	0f 84 64 fe ff ff    	je     4056e0 <io_thread+0x2c0>
  40587c:	48 8d 3d 95 19 00 00 	lea    0x1995(%rip),%rdi        # 407218 <_IO_stdin_used+0x218>
  405883:	e8 d8 c7 ff ff       	call   402060 <puts@plt>
}
  405888:	48 8b 84 24 38 01 00 00 	mov    0x138(%rsp),%rax
  405890:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  405899:	0f 85 fc 01 00 00    	jne    405a9b <io_thread+0x67b>
  40589f:	48 81 c4 48 01 00 00 	add    $0x148,%rsp
  4058a6:	31 c0                	xor    %eax,%eax
  4058a8:	5b                   	pop    %rbx
  4058a9:	5d                   	pop    %rbp
  4058aa:	41 5c                	pop    %r12
  4058ac:	41 5d                	pop    %r13
  4058ae:	41 5e                	pop    %r14
  4058b0:	41 5f                	pop    %r15
  4058b2:	c3                   	ret
  4058b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
  4058b8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
  4058bd:	48 85 c0             	test   %rax,%rax
  4058c0:	0f 84 93 fe ff ff    	je     405759 <io_thread+0x339>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
  4058c6:	4c 8b 00             	mov    (%rax),%r8
      if (cqe->user_data == 1) {
  4058c9:	49 83 f8 01          	cmp    $0x1,%r8
  4058cd:	0f 84 1d 01 00 00    	je     4059f0 <io_thread+0x5d0>
  4058d3:	4c 89 ef             	mov    %r13,%rdi
  4058d6:	e8 85 c7 ff ff       	call   402060 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
  4058db:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
  4058e0:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
  4058e3:	e9 bf fe ff ff       	jmp    4057a7 <io_thread+0x387>
  4058e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
              if (!cqe->res) {
  4058f0:	85 c0                	test   %eax,%eax
  4058f2:	0f 85 b8 00 00 00    	jne    4059b0 <io_thread+0x590>
                  fprintf(stderr, "Empty request!\n");
  4058f8:	48 8b 05 f9 46 00 00 	mov    0x46f9(%rip),%rax        # 409ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  4058ff:	ba 0f 00 00 00       	mov    $0xf,%edx
  405904:	be 01 00 00 00       	mov    $0x1,%esi
  405909:	48 8d 3d f8 18 00 00 	lea    0x18f8(%rip),%rdi        # 407208 <_IO_stdin_used+0x208>
  405910:	48 8b 08             	mov    (%rax),%rcx
  405913:	e8 48 c9 ff ff       	call   402260 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
  405918:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  40591d:	0f 1f 00             	nopl   (%rax)
	if (cqe)
  405920:	48 85 c0             	test   %rax,%rax
  405923:	0f 84 b8 fe ff ff    	je     4057e1 <io_thread+0x3c1>
  405929:	e9 a4 fe ff ff       	jmp    4057d2 <io_thread+0x3b2>
  40592e:	66 90                	xchg   %ax,%ax
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  405930:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  405935:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  40593a:	48 89 d9             	mov    %rbx,%rcx
  40593d:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  405941:	e8 3a fa ff ff       	call   405380 <add_accept_request>
              add_read_request(cqe->res, &ring);
  405946:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  40594b:	48 89 de             	mov    %rbx,%rsi
  40594e:	8b 78 08             	mov    0x8(%rax),%edi
  405951:	e8 0a f5 ff ff       	call   404e60 <add_read_request>
              free(req);
  405956:	4c 89 ff             	mov    %r15,%rdi
  405959:	e8 d2 c6 ff ff       	call   402030 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
  40595e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
  405963:	eb bb                	jmp    405920 <io_thread+0x500>
  405965:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
  405968:	41 8b 47 04          	mov    0x4(%r15),%eax
  40596c:	45 31 f6             	xor    %r14d,%r14d
  40596f:	85 c0                	test   %eax,%eax
  405971:	7e 20                	jle    405993 <io_thread+0x573>
  405973:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  free(req->iov[i].iov_base);
  405978:	49 63 c6             	movslq %r14d,%rax
              for (int i = 0; i < req->iovec_count; i++) {
  40597b:	41 83 c6 01          	add    $0x1,%r14d
                  free(req->iov[i].iov_base);
  40597f:	48 c1 e0 04          	shl    $0x4,%rax
  405983:	4a 8b 7c 38 10       	mov    0x10(%rax,%r15,1),%rdi
  405988:	e8 a3 c6 ff ff       	call   402030 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
  40598d:	45 39 77 04          	cmp    %r14d,0x4(%r15)
  405991:	7f e5                	jg     405978 <io_thread+0x558>
              close(req->client_socket);
  405993:	41 8b 7f 08          	mov    0x8(%r15),%edi
  405997:	e8 64 c7 ff ff       	call   402100 <close@plt>
              free(req);
  40599c:	4c 89 ff             	mov    %r15,%rdi
  40599f:	e8 8c c6 ff ff       	call   402030 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
  4059a4:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
  4059a9:	e9 72 ff ff ff       	jmp    405920 <io_thread+0x500>
  4059ae:	66 90                	xchg   %ax,%ax
              handle_client_request(req, &ring);
  4059b0:	48 89 de             	mov    %rbx,%rsi
  4059b3:	4c 89 ff             	mov    %r15,%rdi
  4059b6:	e8 25 f9 ff ff       	call   4052e0 <handle_client_request>
              free(req->iov[0].iov_base);
  4059bb:	49 8b 7f 10          	mov    0x10(%r15),%rdi
  4059bf:	e8 6c c6 ff ff       	call   402030 <free@plt>
              free(req);
  4059c4:	4c 89 ff             	mov    %r15,%rdi
  4059c7:	e8 64 c6 ff ff       	call   402030 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
  4059cc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
  4059d1:	e9 4a ff ff ff       	jmp    405920 <io_thread+0x500>
  4059d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
  4059e0:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
      if (cqe->user_data == 1) {
  4059e5:	49 83 f8 01          	cmp    $0x1,%r8
  4059e9:	0f 85 e4 fe ff ff    	jne    4058d3 <io_thread+0x4b3>
  4059ef:	90                   	nop
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  4059f0:	83 c2 01             	add    $0x1,%edx
  4059f3:	89 17                	mov    %edx,(%rdi)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4059f5:	48 8d 3d cf 17 00 00 	lea    0x17cf(%rip),%rdi        # 4071cb <_IO_stdin_used+0x1cb>
  4059fc:	e8 5f c6 ff ff       	call   402060 <puts@plt>
  405a01:	e9 76 fe ff ff       	jmp    40587c <io_thread+0x45c>
  405a06:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  405a10:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
  405a18:	8b 17                	mov    (%rdi),%edx
  405a1a:	eb d4                	jmp    4059f0 <io_thread+0x5d0>
    fatal_error("listen()");
  405a1c:	48 8d 3d 77 17 00 00 	lea    0x1777(%rip),%rdi        # 40719a <_IO_stdin_used+0x19a>
  405a23:	e8 b8 ec ff ff       	call   4046e0 <fatal_error>
  405a28:	e9 89 fb ff ff       	jmp    4055b6 <io_thread+0x196>
      fatal_error("bind()");
  405a2d:	48 8d 3d 5f 17 00 00 	lea    0x175f(%rip),%rdi        # 407193 <_IO_stdin_used+0x193>
  405a34:	e8 a7 ec ff ff       	call   4046e0 <fatal_error>
  405a39:	e9 62 fb ff ff       	jmp    4055a0 <io_thread+0x180>
      fatal_error("setsockopt(SO_REUSEADDR)");
  405a3e:	48 8d 3d 35 17 00 00 	lea    0x1735(%rip),%rdi        # 40717a <_IO_stdin_used+0x17a>
  405a45:	e8 96 ec ff ff       	call   4046e0 <fatal_error>
  405a4a:	e9 25 fb ff ff       	jmp    405574 <io_thread+0x154>
      fatal_error("socket()");
  405a4f:	48 8d 3d 1b 17 00 00 	lea    0x171b(%rip),%rdi        # 407171 <_IO_stdin_used+0x171>
  405a56:	e8 85 ec ff ff       	call   4046e0 <fatal_error>
  405a5b:	e9 e6 fa ff ff       	jmp    405546 <io_thread+0x126>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
  405a60:	f7 d8                	neg    %eax
  405a62:	44 89 04 24          	mov    %r8d,(%rsp)
  405a66:	89 c7                	mov    %eax,%edi
  405a68:	e8 33 c8 ff ff       	call   4022a0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  405a6d:	44 8b 04 24          	mov    (%rsp),%r8d
  405a71:	be 01 00 00 00       	mov    $0x1,%esi
  405a76:	48 8d 15 6b 1b 00 00 	lea    0x1b6b(%rip),%rdx        # 4075e8 <_IO_stdin_used+0x5e8>
  405a7d:	48 89 c1             	mov    %rax,%rcx
  405a80:	48 8b 05 71 45 00 00 	mov    0x4571(%rip),%rax        # 409ff8 <stderr@GLIBC_2.2.5>
  405a87:	48 8b 38             	mov    (%rax),%rdi
  405a8a:	31 c0                	xor    %eax,%eax
  405a8c:	e8 df c7 ff ff       	call   402270 <__fprintf_chk@plt>
          exit(1);
  405a91:	bf 01 00 00 00       	mov    $0x1,%edi
  405a96:	e8 a5 c7 ff ff       	call   402240 <exit@plt>
}
  405a9b:	e8 10 c6 ff ff       	call   4020b0 <__stack_chk_fail@plt>

0000000000405aa0 <barriered_work_ingest>:
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
  405aa0:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
  405aa7:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
  405aad:	85 c9                	test   %ecx,%ecx
  405aaf:	0f 8e ed 00 00 00    	jle    405ba2 <barriered_work_ingest+0x102>
int barriered_work_ingest(struct BarrierTask *data) {
  405ab5:	41 56                	push   %r14
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
  405ab7:	45 31 f6             	xor    %r14d,%r14d
int barriered_work_ingest(struct BarrierTask *data) {
  405aba:	41 55                	push   %r13
  405abc:	41 54                	push   %r12
  405abe:	49 89 fc             	mov    %rdi,%r12
  405ac1:	55                   	push   %rbp
  405ac2:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
  405ac3:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
  405ac7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  405ad0:	49 63 c6             	movslq %r14d,%rax
  405ad3:	31 ed                	xor    %ebp,%ebp
  405ad5:	4c 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%r13
  405add:	48 8b 04 c7          	mov    (%rdi,%rax,8),%rax
  405ae1:	8b 10                	mov    (%rax),%edx
  405ae3:	85 d2                	test   %edx,%edx
  405ae5:	7e 25                	jle    405b0c <barriered_work_ingest+0x6c>
  405ae7:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
  405aeb:	48 63 dd             	movslq %ebp,%rbx
  405aee:	48 c1 e3 08          	shl    $0x8,%rbx
  405af2:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
  405af6:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
  405afd:	74 21                	je     405b20 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
  405aff:	83 c5 01             	add    $0x1,%ebp
  405b02:	39 d5                	cmp    %edx,%ebp
  405b04:	7c e5                	jl     405aeb <barriered_work_ingest+0x4b>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
  405b06:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
  405b0c:	41 83 c6 01          	add    $0x1,%r14d
  405b10:	41 39 ce             	cmp    %ecx,%r14d
  405b13:	7c bb                	jl     405ad0 <barriered_work_ingest+0x30>
}
  405b15:	5b                   	pop    %rbx
  405b16:	31 c0                	xor    %eax,%eax
  405b18:	5d                   	pop    %rbp
  405b19:	41 5c                	pop    %r12
  405b1b:	41 5d                	pop    %r13
  405b1d:	41 5e                	pop    %r14
  405b1f:	c3                   	ret
        data->ingest_count++;
  405b20:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
  405b29:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
  405b30:	bf 04 00 00 00       	mov    $0x4,%edi
  405b35:	48 c1 e6 05          	shl    $0x5,%rsi
  405b39:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
  405b40:	48 83 c6 10          	add    $0x10,%rsi
  405b44:	e8 37 c5 ff ff       	call   402080 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
  405b49:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
  405b51:	48 8b 40 50          	mov    0x50(%rax),%rax
  405b55:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
  405b59:	48 03 58 08          	add    0x8(%rax),%rbx
        data->thread->buffers[b]->buffer[x].available = 0;
  405b5d:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
  405b67:	8b 83 94 00 00 00    	mov    0x94(%rbx),%eax
  405b6d:	83 c0 01             	add    $0x1,%eax
  405b70:	99                   	cltd
  405b71:	f7 bb 90 00 00 00    	idivl  0x90(%rbx)
  405b77:	89 93 94 00 00 00    	mov    %edx,0x94(%rbx)
        asm volatile ("sfence" ::: "memory");
  405b7d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
  405b80:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
  405b88:	83 c5 01             	add    $0x1,%ebp
  405b8b:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
  405b8f:	4a 8b 04 2f          	mov    (%rdi,%r13,1),%rax
  405b93:	8b 10                	mov    (%rax),%edx
  405b95:	39 d5                	cmp    %edx,%ebp
  405b97:	0f 8c 4a ff ff ff    	jl     405ae7 <barriered_work_ingest+0x47>
  405b9d:	e9 64 ff ff ff       	jmp    405b06 <barriered_work_ingest+0x66>
}
  405ba2:	31 c0                	xor    %eax,%eax
  405ba4:	c3                   	ret
  405ba5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000405bb0 <barriered_thread>:
void* barriered_thread(void *arg) {
  405bb0:	41 56                	push   %r14
  405bb2:	41 55                	push   %r13
  int t = 0;
  405bb4:	45 31 ed             	xor    %r13d,%r13d
void* barriered_thread(void *arg) {
  405bb7:	41 54                	push   %r12
  int waiting = 0;
  405bb9:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
  405bbc:	55                   	push   %rbp
  405bbd:	48 89 fd             	mov    %rdi,%rbp
  405bc0:	53                   	push   %rbx
  while (data->running == 1) {
  405bc1:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
  405bc5:	0f 85 cf 01 00 00    	jne    405d9a <barriered_thread+0x1ea>
    if (t >= data->task_count) {
  405bcb:	8b 45 40             	mov    0x40(%rbp),%eax
  405bce:	66 90                	xchg   %ax,%ax
  405bd0:	41 39 c5             	cmp    %eax,%r13d
  405bd3:	7c 43                	jl     405c18 <barriered_thread+0x68>
      data->cycles++;
  405bd5:	48 83 85 a8 00 00 00 01 	addq   $0x1,0xa8(%rbp)
      t = 0;
  405bdd:	45 31 ed             	xor    %r13d,%r13d
    for (; t < data->task_count; t++) {
  405be0:	85 c0                	test   %eax,%eax
  405be2:	7f 34                	jg     405c18 <barriered_thread+0x68>
  405be4:	e9 a7 01 00 00       	jmp    405d90 <barriered_thread+0x1e0>
  405be9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
  405bf0:	48 63 55 04          	movslq 0x4(%rbp),%rdx
  405bf4:	48 8b 45 18          	mov    0x18(%rbp),%rax
  405bf8:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
  405bfc:	48 8b 78 38          	mov    0x38(%rax),%rdi
  405c00:	48 01 df             	add    %rbx,%rdi
  405c03:	e8 98 fe ff ff       	call   405aa0 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
  405c08:	8b 45 40             	mov    0x40(%rbp),%eax
  405c0b:	41 83 c5 01          	add    $0x1,%r13d
  405c0f:	44 39 e8             	cmp    %r13d,%eax
  405c12:	0f 8e 78 01 00 00    	jle    405d90 <barriered_thread+0x1e0>
      if (data->tasks[t].available == 1) {
  405c18:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  405c1c:	49 63 dd             	movslq %r13d,%rbx
  405c1f:	48 c1 e3 09          	shl    $0x9,%rbx
  405c23:	48 8d 34 1a          	lea    (%rdx,%rbx,1),%rsi
  405c27:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
  405c2e:	75 c0                	jne    405bf0 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
  405c30:	44 8b 55 28          	mov    0x28(%rbp),%r10d
  405c34:	83 e8 01             	sub    $0x1,%eax
  405c37:	41 8d 4d ff          	lea    -0x1(%r13),%ecx
  405c3b:	45 85 ed             	test   %r13d,%r13d
  405c3e:	0f 4f c1             	cmovg  %ecx,%eax
  405c41:	45 85 d2             	test   %r10d,%r10d
  405c44:	0f 8e 16 02 00 00    	jle    405e60 <barriered_thread+0x2b0>
  405c4a:	48 8b 55 18          	mov    0x18(%rbp),%rdx
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  405c4e:	48 63 c8             	movslq %eax,%rcx
        int arrived = 0; 
  405c51:	45 31 f6             	xor    %r14d,%r14d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  405c54:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
  405c5b:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
  405c62:	41 8d 72 ff          	lea    -0x1(%r10),%esi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  405c66:	48 c1 e1 09          	shl    $0x9,%rcx
  405c6a:	48 8d 42 08          	lea    0x8(%rdx),%rax
  405c6e:	48 8d 3c f0          	lea    (%rax,%rsi,8),%rdi
        int prearrive = 0; 
  405c72:	31 f6                	xor    %esi,%esi
  405c74:	eb 0e                	jmp    405c84 <barriered_thread+0xd4>
  405c76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  405c80:	48 83 c0 08          	add    $0x8,%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  405c84:	48 8b 12             	mov    (%rdx),%rdx
  405c87:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
  405c8b:	49 01 cb             	add    %rcx,%r11
  405c8e:	4c 89 da             	mov    %r11,%rdx
            arrived++;
  405c91:	45 31 db             	xor    %r11d,%r11d
  405c94:	44 3b 8a 80 00 00 00 	cmp    0x80(%rdx),%r9d
  405c9b:	41 0f 94 c3          	sete   %r11b
  405c9f:	45 01 de             	add    %r11d,%r14d
            prearrive++;
  405ca2:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
  405ca9:	0f 94 c2             	sete   %dl
  405cac:	0f b6 d2             	movzbl %dl,%edx
  405caf:	01 d6                	add    %edx,%esi
        for (int thread = 0 ; thread < data->thread_count; thread++) {
  405cb1:	48 89 c2             	mov    %rax,%rdx
  405cb4:	48 39 c7             	cmp    %rax,%rdi
  405cb7:	75 c7                	jne    405c80 <barriered_thread+0xd0>
        if (prearrive == 0 || prearrive == data->thread_count) {
  405cb9:	85 f6                	test   %esi,%esi
  405cbb:	0f 84 e7 00 00 00    	je     405da8 <barriered_thread+0x1f8>
  405cc1:	41 39 f2             	cmp    %esi,%r10d
  405cc4:	0f 84 de 00 00 00    	je     405da8 <barriered_thread+0x1f8>
        if (arrived == 0 || arrived == data->thread_count) {
  405cca:	45 85 f6             	test   %r14d,%r14d
  405ccd:	74 0a                	je     405cd9 <barriered_thread+0x129>
  405ccf:	44 39 75 28          	cmp    %r14d,0x28(%rbp)
  405cd3:	0f 85 99 01 00 00    	jne    405e72 <barriered_thread+0x2c2>
  405cd9:	48 8b 55 38          	mov    0x38(%rbp),%rdx
          data->tasks[t].prearrive++;
  405cdd:	48 01 da             	add    %rbx,%rdx
  405ce0:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
  405ce7:	45 85 ed             	test   %r13d,%r13d
  405cea:	75 14                	jne    405d00 <barriered_thread+0x150>
  405cec:	48 8b b5 80 00 00 00 	mov    0x80(%rbp),%rsi
  405cf3:	48 3b b5 88 00 00 00 	cmp    0x88(%rbp),%rsi
  405cfa:	0f 8c 38 01 00 00    	jl     405e38 <barriered_thread+0x288>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
  405d00:	48 63 4d 04          	movslq 0x4(%rbp),%rcx
  405d04:	48 8b 45 18          	mov    0x18(%rbp),%rax
          data->tasks[t].available = 0;
  405d08:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
  405d12:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
  405d16:	48 8b 78 38          	mov    0x38(%rax),%rdi
  405d1a:	48 01 df             	add    %rbx,%rdi
  405d1d:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  405d23:	8b 45 40             	mov    0x40(%rbp),%eax
          data->tasks[t].arrived++;
  405d26:	48 03 5d 38          	add    0x38(%rbp),%rbx
  405d2a:	83 83 80 00 00 00 01 	addl   $0x1,0x80(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  405d31:	83 e8 01             	sub    $0x1,%eax
          data->iteration_count++;
  405d34:	48 83 45 78 01       	addq   $0x1,0x78(%rbp)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  405d39:	44 39 e8             	cmp    %r13d,%eax
  405d3c:	0f 84 be 00 00 00    	je     405e00 <barriered_thread+0x250>
          asm volatile ("sfence" ::: "memory");
  405d42:	0f ae f8             	sfence
          if (waiting == 0) {
  405d45:	45 85 e4             	test   %r12d,%r12d
  405d48:	0f 85 ba fe ff ff    	jne    405c08 <barriered_thread+0x58>
            data->task_snapshot[data->task_timestamp_count].task = t;
  405d4e:	48 8b 85 98 00 00 00 	mov    0x98(%rbp),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
  405d55:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
  405d5a:	41 bc 01 00 00 00    	mov    $0x1,%r12d
            data->task_snapshot[data->task_timestamp_count].task = t;
  405d60:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  405d64:	48 8b 85 90 00 00 00 	mov    0x90(%rbp),%rax
  405d6b:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
  405d6f:	44 89 6e 20          	mov    %r13d,0x20(%rsi)
    for (; t < data->task_count; t++) {
  405d73:	41 83 c5 01          	add    $0x1,%r13d
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
  405d77:	e8 04 c3 ff ff       	call   402080 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
  405d7c:	8b 45 40             	mov    0x40(%rbp),%eax
  405d7f:	44 39 e8             	cmp    %r13d,%eax
  405d82:	0f 8f 90 fe ff ff    	jg     405c18 <barriered_thread+0x68>
  405d88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  while (data->running == 1) {
  405d90:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
  405d94:	0f 84 36 fe ff ff    	je     405bd0 <barriered_thread+0x20>
}
  405d9a:	5b                   	pop    %rbx
  405d9b:	31 c0                	xor    %eax,%eax
  405d9d:	5d                   	pop    %rbp
  405d9e:	41 5c                	pop    %r12
  405da0:	41 5d                	pop    %r13
  405da2:	41 5e                	pop    %r14
  405da4:	c3                   	ret
  405da5:	0f 1f 00             	nopl   (%rax)
          if (waiting == 1) {
  405da8:	41 83 fc 01          	cmp    $0x1,%r12d
  405dac:	0f 85 18 ff ff ff    	jne    405cca <barriered_thread+0x11a>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
  405db2:	48 8b 85 98 00 00 00 	mov    0x98(%rbp),%rax
  405db9:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 0; 
  405dbe:	45 31 e4             	xor    %r12d,%r12d
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
  405dc1:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  405dc5:	48 8b 85 90 00 00 00 	mov    0x90(%rbp),%rax
  405dcc:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
  405dd1:	e8 aa c2 ff ff       	call   402080 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
  405dd6:	48 8b 85 98 00 00 00 	mov    0x98(%rbp),%rax
  405ddd:	48 83 c0 01          	add    $0x1,%rax
  405de1:	48 99                	cqto
  405de3:	48 f7 bd a0 00 00 00 	idivq  0xa0(%rbp)
  405dea:	48 89 95 98 00 00 00 	mov    %rdx,0x98(%rbp)
            waiting = 0; 
  405df1:	e9 d4 fe ff ff       	jmp    405cca <barriered_thread+0x11a>
  405df6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  405e00:	48 8b b5 80 00 00 00 	mov    0x80(%rbp),%rsi
  405e07:	48 3b b5 88 00 00 00 	cmp    0x88(%rbp),%rsi
  405e0e:	0f 8d 2e ff ff ff    	jge    405d42 <barriered_thread+0x192>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
  405e14:	48 c1 e6 04          	shl    $0x4,%rsi
  405e18:	bf 04 00 00 00       	mov    $0x4,%edi
  405e1d:	48 03 75 70          	add    0x70(%rbp),%rsi
  405e21:	e8 5a c2 ff ff       	call   402080 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
  405e26:	48 83 85 80 00 00 00 01 	addq   $0x1,0x80(%rbp)
  405e2e:	e9 0f ff ff ff       	jmp    405d42 <barriered_thread+0x192>
  405e33:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
  405e38:	48 c1 e6 04          	shl    $0x4,%rsi
  405e3c:	bf 04 00 00 00       	mov    $0x4,%edi
  405e41:	48 03 75 68          	add    0x68(%rbp),%rsi
  405e45:	e8 36 c2 ff ff       	call   402080 <clock_gettime@plt>
          data->tasks[t].available = 0;
  405e4a:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  405e4e:	48 01 da             	add    %rbx,%rdx
  405e51:	e9 aa fe ff ff       	jmp    405d00 <barriered_thread+0x150>
  405e56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
  405e60:	41 83 fc 01          	cmp    $0x1,%r12d
  405e64:	0f 85 73 fe ff ff    	jne    405cdd <barriered_thread+0x12d>
        int arrived = 0; 
  405e6a:	45 31 f6             	xor    %r14d,%r14d
  405e6d:	e9 40 ff ff ff       	jmp    405db2 <barriered_thread+0x202>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
  405e72:	48 63 55 04          	movslq 0x4(%rbp),%rdx
  405e76:	48 8b 45 18          	mov    0x18(%rbp),%rax
  405e7a:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
  405e7e:	48 03 58 38          	add    0x38(%rax),%rbx
  405e82:	48 89 df             	mov    %rbx,%rdi
  405e85:	e8 16 fc ff ff       	call   405aa0 <barriered_work_ingest>
          break;
  405e8a:	e9 32 fd ff ff       	jmp    405bc1 <barriered_thread+0x11>
  405e8f:	90                   	nop

0000000000405e90 <receive>:
int receive(struct BarrierTask *data) {
  405e90:	41 56                	push   %r14
  405e92:	41 55                	push   %r13
  405e94:	41 54                	push   %r12
  405e96:	55                   	push   %rbp
  405e97:	53                   	push   %rbx
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  405e98:	4c 63 a7 40 01 00 00 	movslq 0x140(%rdi),%r12
  405e9f:	45 85 e4             	test   %r12d,%r12d
  405ea2:	0f 8e 2b 01 00 00    	jle    405fd3 <receive+0x143>
    if (n == data->thread->real_thread_index) { continue; }
  405ea8:	4c 8b b7 28 01 00 00 	mov    0x128(%rdi),%r14
  405eaf:	48 89 fe             	mov    %rdi,%rsi
  405eb2:	31 db                	xor    %ebx,%ebx
  405eb4:	49 63 6e 08          	movslq 0x8(%r14),%rbp
  405eb8:	49 89 ed             	mov    %rbp,%r13
  405ebb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  405ec0:	41 39 dd             	cmp    %ebx,%r13d
  405ec3:	0f 84 fd 00 00 00    	je     405fc6 <receive+0x136>
    struct Data *me = data->mailboxes[n].lower;
  405ec9:	48 89 d8             	mov    %rbx,%rax
  405ecc:	48 c1 e0 06          	shl    $0x6,%rax
  405ed0:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
  405ed7:	48 8b 10             	mov    (%rax),%rdx
    if (me->available_reading == 1) {
  405eda:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
  405ee0:	83 f8 01             	cmp    $0x1,%eax
  405ee3:	74 11                	je     405ef6 <receive+0x66>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
  405ee5:	83 ba 18 03 00 00 02 	cmpl   $0x2,0x318(%rdx)
  405eec:	75 08                	jne    405ef6 <receive+0x66>
  405eee:	85 c0                	test   %eax,%eax
  405ef0:	0f 84 d0 00 00 00    	je     405fc6 <receive+0x136>
    for (; me->messages_count > 0 ; ) {
  405ef6:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
  405efd:	48 85 ff             	test   %rdi,%rdi
  405f00:	0f 8e a2 00 00 00    	jle    405fa8 <receive+0x118>
  405f06:	4c 8b 8e 78 01 00 00 	mov    0x178(%rsi),%r9
  405f0d:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
  405f14:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
      if (me->messages[x]->group == data->group) {
  405f18:	4c 8b 1a             	mov    (%rdx),%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
  405f1b:	4c 63 56 04          	movslq 0x4(%rsi),%r10
  405f1f:	49 01 f9             	add    %rdi,%r9
  405f22:	49 01 f8             	add    %rdi,%r8
  405f25:	48 03 ba 10 03 00 00 	add    0x310(%rdx),%rdi
  405f2c:	eb 08                	jmp    405f36 <receive+0xa6>
  405f2e:	66 90                	xchg   %ax,%ax
    for (; me->messages_count > 0 ; ) {
  405f30:	48 83 e8 01          	sub    $0x1,%rax
  405f34:	72 72                	jb     405fa8 <receive+0x118>
      data->sends++;
  405f36:	4c 89 c9             	mov    %r9,%rcx
      me->messages_count--;
  405f39:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
      data->sends++;
  405f40:	48 29 c1             	sub    %rax,%rcx
  405f43:	48 89 8e 78 01 00 00 	mov    %rcx,0x178(%rsi)
      data->n++;
  405f4a:	4c 89 c1             	mov    %r8,%rcx
  405f4d:	48 29 c1             	sub    %rax,%rcx
  405f50:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
      me->received++;
  405f57:	48 89 f9             	mov    %rdi,%rcx
  405f5a:	48 29 c1             	sub    %rax,%rcx
  405f5d:	48 89 8a 10 03 00 00 	mov    %rcx,0x310(%rdx)
      if (me->messages[x]->group == data->group) {
  405f64:	48 63 c8             	movslq %eax,%rcx
  405f67:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
  405f6b:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
  405f6f:	75 bf                	jne    405f30 <receive+0xa0>
  405f71:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
  405f75:	75 b9                	jne    405f30 <receive+0xa0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
  405f77:	49 63 46 04          	movslq 0x4(%r14),%rax
  405f7b:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  405f7d:	bf 01 00 00 00       	mov    $0x1,%edi
  405f82:	ba 01 00 00 00       	mov    $0x1,%edx
  405f87:	48 8d 35 82 16 00 00 	lea    0x1682(%rip),%rsi        # 407610 <_IO_stdin_used+0x610>
  405f8e:	48 39 e8             	cmp    %rbp,%rax
  405f91:	0f 94 c1             	sete   %cl
  405f94:	31 c0                	xor    %eax,%eax
  405f96:	e8 45 c2 ff ff       	call   4021e0 <__printf_chk@plt>
        exit(1);
  405f9b:	bf 01 00 00 00       	mov    $0x1,%edi
  405fa0:	e8 9b c2 ff ff       	call   402240 <exit@plt>
  405fa5:	0f 1f 00             	nopl   (%rax)
      me->available_reading = 0;
  405fa8:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
  405fb2:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
      me->available_sending = 1;
  405fbc:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  405fc6:	48 83 c3 01          	add    $0x1,%rbx
  405fca:	49 39 dc             	cmp    %rbx,%r12
  405fcd:	0f 85 ed fe ff ff    	jne    405ec0 <receive+0x30>
  asm volatile ("sfence" ::: "memory");
  405fd3:	0f ae f8             	sfence
}
  405fd6:	31 c0                	xor    %eax,%eax
  405fd8:	5b                   	pop    %rbx
  405fd9:	5d                   	pop    %rbp
  405fda:	41 5c                	pop    %r12
  405fdc:	41 5d                	pop    %r13
  405fde:	41 5e                	pop    %r14
  405fe0:	c3                   	ret
  405fe1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  405fec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000405ff0 <sendm>:
int sendm(struct BarrierTask *data) {
  405ff0:	41 57                	push   %r15
  405ff2:	41 56                	push   %r14
  405ff4:	41 55                	push   %r13
  405ff6:	41 54                	push   %r12
  405ff8:	55                   	push   %rbp
  405ff9:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  405ffa:	4c 63 87 40 01 00 00 	movslq 0x140(%rdi),%r8
  406001:	45 85 c0             	test   %r8d,%r8d
  406004:	7e 77                	jle    40607d <sendm+0x8d>
  406006:	48 8d 9f 88 01 00 00 	lea    0x188(%rdi),%rbx
        if (n == data->thread->real_thread_index) { continue; }
  40600d:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  406014:	48 89 f9             	mov    %rdi,%rcx
  406017:	4c 8d bf 90 01 00 00 	lea    0x190(%rdi),%r15
  40601e:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
  406023:	44 8b 48 08          	mov    0x8(%rax),%r9d
  406027:	31 c0                	xor    %eax,%eax
  406029:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  406030:	41 39 c1             	cmp    %eax,%r9d
  406033:	74 3f                	je     406074 <sendm+0x84>
        struct Data *them = data->mailboxes[n].higher;
  406035:	48 89 c2             	mov    %rax,%rdx
  406038:	48 c1 e2 06          	shl    $0x6,%rdx
  40603c:	48 03 91 70 01 00 00 	add    0x170(%rcx),%rdx
  406043:	48 8b 52 08          	mov    0x8(%rdx),%rdx
        if (them->messages_count > 0) {
  406047:	48 8b b2 80 00 00 00 	mov    0x80(%rdx),%rsi
  40604e:	48 85 f6             	test   %rsi,%rsi
  406051:	7f 21                	jg     406074 <sendm+0x84>
        if (them->available_sending == 1) {
  406053:	8b ba 00 01 00 00    	mov    0x100(%rdx),%edi
  406059:	83 ff 01             	cmp    $0x1,%edi
  40605c:	74 0d                	je     40606b <sendm+0x7b>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
  40605e:	83 ba 18 03 00 00 02 	cmpl   $0x2,0x318(%rdx)
  406065:	75 04                	jne    40606b <sendm+0x7b>
  406067:	85 ff                	test   %edi,%edi
  406069:	74 09                	je     406074 <sendm+0x84>
        if (data->sending == 1) {
  40606b:	83 b9 80 01 00 00 01 	cmpl   $0x1,0x180(%rcx)
  406072:	74 1c                	je     406090 <sendm+0xa0>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  406074:	48 83 c0 01          	add    $0x1,%rax
  406078:	49 39 c0             	cmp    %rax,%r8
  40607b:	75 b3                	jne    406030 <sendm+0x40>
      asm volatile ("sfence" ::: "memory");
  40607d:	0f ae f8             	sfence
}
  406080:	31 c0                	xor    %eax,%eax
  406082:	5b                   	pop    %rbx
  406083:	5d                   	pop    %rbp
  406084:	41 5c                	pop    %r12
  406086:	41 5d                	pop    %r13
  406088:	41 5e                	pop    %r14
  40608a:	41 5f                	pop    %r15
  40608c:	c3                   	ret
  40608d:	0f 1f 00             	nopl   (%rax)
          for (; them->messages_count < min;) {
  406090:	48 63 9a 88 00 00 00 	movslq 0x88(%rdx),%rbx
  406097:	48 39 de             	cmp    %rbx,%rsi
  40609a:	0f 8d b7 00 00 00    	jge    406157 <sendm+0x167>
            them->messages[them->messages_count++] = data->message; 
  4060a0:	4c 8b 12             	mov    (%rdx),%r10
  4060a3:	49 89 db             	mov    %rbx,%r11
  4060a6:	48 8b a9 08 01 00 00 	mov    0x108(%rcx),%rbp
  4060ad:	49 29 f3             	sub    %rsi,%r11
  4060b0:	4c 8b b2 08 03 00 00 	mov    0x308(%rdx),%r14
  4060b7:	49 8d 3c f2          	lea    (%r10,%rsi,8),%rdi
  4060bb:	4d 8d 24 da          	lea    (%r10,%rbx,8),%r12
  4060bf:	4c 3b 64 24 e8       	cmp    -0x18(%rsp),%r12
  4060c4:	0f 96 44 24 f7       	setbe  -0x9(%rsp)
  4060c9:	4c 39 ff             	cmp    %r15,%rdi
  4060cc:	41 0f 93 c5          	setae  %r13b
  4060d0:	44 0a 6c 24 f7       	or     -0x9(%rsp),%r13b
  4060d5:	0f 84 a5 00 00 00    	je     406180 <sendm+0x190>
  4060db:	4d 8d 6b ff          	lea    -0x1(%r11),%r13
  4060df:	49 83 fd 02          	cmp    $0x2,%r13
  4060e3:	0f 86 97 00 00 00    	jbe    406180 <sendm+0x190>
  4060e9:	4c 8b a9 88 01 00 00 	mov    0x188(%rcx),%r13
  4060f0:	4d 89 dc             	mov    %r11,%r12
  4060f3:	49 d1 ec             	shr    %r12
  4060f6:	66 49 0f 6e c5       	movq   %r13,%xmm0
  4060fb:	49 c1 e4 04          	shl    $0x4,%r12
  4060ff:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
  406103:	49 01 fc             	add    %rdi,%r12
  406106:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  406110:	0f 11 07             	movups %xmm0,(%rdi)
          for (; them->messages_count < min;) {
  406113:	48 83 c7 10          	add    $0x10,%rdi
  406117:	49 39 fc             	cmp    %rdi,%r12
  40611a:	75 f4                	jne    406110 <sendm+0x120>
  40611c:	4c 89 df             	mov    %r11,%rdi
  40611f:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
  406123:	48 01 fe             	add    %rdi,%rsi
  406126:	49 39 fb             	cmp    %rdi,%r11
  406129:	74 0b                	je     406136 <sendm+0x146>
            them->messages[them->messages_count++] = data->message; 
  40612b:	4c 8b a9 88 01 00 00 	mov    0x188(%rcx),%r13
  406132:	4d 89 2c f2          	mov    %r13,(%r10,%rsi,8)
            data->n++;
  406136:	4c 01 dd             	add    %r11,%rbp
            them->sent++;
  406139:	4b 8d 34 1e          	lea    (%r14,%r11,1),%rsi
            data->n++;
  40613d:	48 89 a9 08 01 00 00 	mov    %rbp,0x108(%rcx)
            them->sent++;
  406144:	48 89 b2 08 03 00 00 	mov    %rsi,0x308(%rdx)
  40614b:	48 89 9a 80 00 00 00 	mov    %rbx,0x80(%rdx)
  406152:	4d 89 6c da f8       	mov    %r13,-0x8(%r10,%rbx,8)
          them->available_sending = 0;
  406157:	c7 82 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdx)
          them->available_reading = 1;
  406161:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
          them->available_receiving = 1;
  40616b:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
  406175:	e9 fa fe ff ff       	jmp    406074 <sendm+0x84>
  40617a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
  406180:	4c 8b a9 88 01 00 00 	mov    0x188(%rcx),%r13
          for (; them->messages_count < min;) {
  406187:	48 83 c7 08          	add    $0x8,%rdi
            them->messages[them->messages_count++] = data->message; 
  40618b:	4c 89 6f f8          	mov    %r13,-0x8(%rdi)
          for (; them->messages_count < min;) {
  40618f:	4c 39 e7             	cmp    %r12,%rdi
  406192:	75 ec                	jne    406180 <sendm+0x190>
  406194:	eb a0                	jmp    406136 <sendm+0x146>
  406196:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004061a0 <mailboxkind>:
  if (kind == 0) {
  4061a0:	85 f6                	test   %esi,%esi
  4061a2:	74 14                	je     4061b8 <mailboxkind+0x18>
  return NULL;
  4061a4:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
  4061a6:	83 fe 01             	cmp    $0x1,%esi
  4061a9:	74 05                	je     4061b0 <mailboxkind+0x10>
}
  4061ab:	c3                   	ret
  4061ac:	0f 1f 40 00          	nopl   0x0(%rax)
    return mailbox->higher;
  4061b0:	48 8b 47 08          	mov    0x8(%rdi),%rax
}
  4061b4:	c3                   	ret
  4061b5:	0f 1f 00             	nopl   (%rax)
    return mailbox->lower;
  4061b8:	48 8b 07             	mov    (%rdi),%rax
  4061bb:	c3                   	ret
  4061bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004061c0 <setmailboxkind>:
  if (kind == 0) {
  4061c0:	85 d2                	test   %edx,%edx
  4061c2:	75 0c                	jne    4061d0 <setmailboxkind+0x10>
    mailbox->lower = data;
  4061c4:	48 89 37             	mov    %rsi,(%rdi)
}
  4061c7:	31 c0                	xor    %eax,%eax
  4061c9:	c3                   	ret
  4061ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (kind == 1) {
  4061d0:	83 fa 01             	cmp    $0x1,%edx
  4061d3:	75 0b                	jne    4061e0 <setmailboxkind+0x20>
    mailbox->higher = data;
  4061d5:	48 89 77 08          	mov    %rsi,0x8(%rdi)
}
  4061d9:	31 c0                	xor    %eax,%eax
  4061db:	c3                   	ret
  4061dc:	0f 1f 40 00          	nopl   0x0(%rax)
  if (kind == 2) {
  4061e0:	83 fa 02             	cmp    $0x2,%edx
  4061e3:	75 07                	jne    4061ec <setmailboxkind+0x2c>
    mailbox->pending_lower = data;
  4061e5:	48 89 77 10          	mov    %rsi,0x10(%rdi)
}
  4061e9:	31 c0                	xor    %eax,%eax
  4061eb:	c3                   	ret
  if (kind == 3) {
  4061ec:	83 fa 03             	cmp    $0x3,%edx
  4061ef:	75 d6                	jne    4061c7 <setmailboxkind+0x7>
    mailbox->pending_higher = data;
  4061f1:	48 89 77 18          	mov    %rsi,0x18(%rdi)
}
  4061f5:	31 c0                	xor    %eax,%eax
  4061f7:	c3                   	ret
  4061f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000406200 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
  406200:	41 57                	push   %r15
  406202:	41 56                	push   %r14
  406204:	49 89 fe             	mov    %rdi,%r14
  406207:	41 55                	push   %r13
  406209:	41 54                	push   %r12
  40620b:	55                   	push   %rbp
  40620c:	53                   	push   %rbx
  40620d:	48 83 ec 58          	sub    $0x58,%rsp
        int t = data->task_index;
  406211:	8b 47 04             	mov    0x4(%rdi),%eax
  406214:	89 44 24 4c          	mov    %eax,0x4c(%rsp)
  if (data->thread_index == data->task_index) {
  406218:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
  40621e:	74 60                	je     406280 <barriered_work+0x80>
    receive(data);
  406220:	e8 6b fc ff ff       	call   405e90 <receive>
    while (data->scheduled == 1) {
  406225:	41 83 be 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r14)
  40622d:	75 16                	jne    406245 <barriered_work+0x45>
  40622f:	90                   	nop
      data->n++;
  406230:	49 83 86 08 01 00 00 01 	addq   $0x1,0x108(%r14)
      asm volatile ("sfence" ::: "memory");
  406238:	0f ae f8             	sfence
    while (data->scheduled == 1) {
  40623b:	41 83 be 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r14)
  406243:	74 eb                	je     406230 <barriered_work+0x30>
    sendm(data);
  406245:	4c 89 f7             	mov    %r14,%rdi
  406248:	e8 a3 fd ff ff       	call   405ff0 <sendm>
  if (t == data->thread_count - 1) {
  40624d:	41 8b 86 34 01 00 00 	mov    0x134(%r14),%eax
  406254:	83 e8 01             	sub    $0x1,%eax
  406257:	3b 44 24 4c          	cmp    0x4c(%rsp),%eax
  40625b:	0f 84 cf 03 00 00    	je     406630 <barriered_work+0x430>
  data->swap = 0;
  406261:	41 c7 86 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r14)
  asm volatile ("sfence" ::: "memory");
  40626c:	0f ae f8             	sfence
}
  40626f:	48 83 c4 58          	add    $0x58,%rsp
  406273:	31 c0                	xor    %eax,%eax
  406275:	5b                   	pop    %rbx
  406276:	5d                   	pop    %rbp
  406277:	41 5c                	pop    %r12
  406279:	41 5d                	pop    %r13
  40627b:	41 5e                	pop    %r14
  40627d:	41 5f                	pop    %r15
  40627f:	c3                   	ret
    receive(data);
  406280:	e8 0b fc ff ff       	call   405e90 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
  406285:	41 8b 96 40 01 00 00 	mov    0x140(%r14),%edx
  40628c:	85 d2                	test   %edx,%edx
  40628e:	0f 8e b1 07 00 00    	jle    406a45 <barriered_work+0x845>
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
  406294:	48 63 44 24 4c       	movslq 0x4c(%rsp),%rax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
  406299:	31 c9                	xor    %ecx,%ecx
            int y = (k * data->thread->threads_per_group) + data->thread_index;
  40629b:	49 8b b6 28 01 00 00 	mov    0x128(%r14),%rsi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
  4062a2:	4d 89 f7             	mov    %r14,%r15
  4062a5:	89 cb                	mov    %ecx,%ebx
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
  4062a7:	48 c1 e0 09          	shl    $0x9,%rax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
  4062ab:	48 89 c5             	mov    %rax,%rbp
  4062ae:	eb 0b                	jmp    4062bb <barriered_work+0xbb>
  4062b0:	83 c3 01             	add    $0x1,%ebx
  4062b3:	39 d3                	cmp    %edx,%ebx
  4062b5:	0f 8d d5 03 00 00    	jge    406690 <barriered_work+0x490>
        int b = data->thread->real_thread_index;
  4062bb:	44 8b 76 08          	mov    0x8(%rsi),%r14d
              if (y == b) { continue; }
  4062bf:	41 39 de             	cmp    %ebx,%r14d
  4062c2:	74 ec                	je     4062b0 <barriered_work+0xb0>
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
  4062c4:	48 63 c3             	movslq %ebx,%rax
  4062c7:	4c 8b 46 20          	mov    0x20(%rsi),%r8
  4062cb:	48 8d 3c 40          	lea    (%rax,%rax,2),%rdi
  4062cf:	48 8d 3c ff          	lea    (%rdi,%rdi,8),%rdi
  4062d3:	49 8b 4c f8 38       	mov    0x38(%r8,%rdi,8),%rcx
  4062d8:	4c 8d 2c fd 00 00 00 00 	lea    0x0(,%rdi,8),%r13
  4062e0:	48 01 e9             	add    %rbp,%rcx
  4062e3:	44 8b 89 98 01 00 00 	mov    0x198(%rcx),%r9d
  4062ea:	48 89 cf             	mov    %rcx,%rdi
  4062ed:	45 85 c9             	test   %r9d,%r9d
  4062f0:	75 be                	jne    4062b0 <barriered_work+0xb0>
  4062f2:	4d 63 ce             	movslq %r14d,%r9
  4062f5:	4f 8d 14 49          	lea    (%r9,%r9,2),%r10
  4062f9:	4f 8d 14 d2          	lea    (%r10,%r10,8),%r10
  4062fd:	4b 8b 4c d0 38       	mov    0x38(%r8,%r10,8),%rcx
  406302:	4e 8d 1c d5 00 00 00 00 	lea    0x0(,%r10,8),%r11
  40630a:	48 01 e9             	add    %rbp,%rcx
  40630d:	44 8b a1 98 01 00 00 	mov    0x198(%rcx),%r12d
  406314:	49 89 c8             	mov    %rcx,%r8
  406317:	45 85 e4             	test   %r12d,%r12d
  40631a:	75 94                	jne    4062b0 <barriered_work+0xb0>
  40631c:	48 c1 e0 06          	shl    $0x6,%rax
  406320:	48 89 c1             	mov    %rax,%rcx
  406323:	49 8b 80 70 01 00 00 	mov    0x170(%r8),%rax
  40632a:	83 7c 08 38 02       	cmpl   $0x2,0x38(%rax,%rcx,1)
  40632f:	0f 85 7b ff ff ff    	jne    4062b0 <barriered_work+0xb0>
  406335:	48 8b 87 70 01 00 00 	mov    0x170(%rdi),%rax
  40633c:	4d 89 ca             	mov    %r9,%r10
  40633f:	49 c1 e2 06          	shl    $0x6,%r10
  406343:	42 83 7c 10 38 02    	cmpl   $0x2,0x38(%rax,%r10,1)
  406349:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
  40634e:	0f 85 5c ff ff ff    	jne    4062b0 <barriered_work+0xb0>
                    int min = minf(b, y); 
  406354:	89 de                	mov    %ebx,%esi
  406356:	44 89 f7             	mov    %r14d,%edi
  406359:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
  40635e:	48 89 0c 24          	mov    %rcx,(%rsp)
  406362:	e8 59 e3 ff ff       	call   4046c0 <minf>
                    int max = maxf(b, y); 
  406367:	89 de                	mov    %ebx,%esi
  406369:	44 89 f7             	mov    %r14d,%edi
  40636c:	e8 5f e3 ff ff       	call   4046d0 <maxf>
                    for (int nn = 0; nn < data->thread_count; nn++) {
  406371:	45 8b 8f 34 01 00 00 	mov    0x134(%r15),%r9d
  406378:	48 8b 0c 24          	mov    (%rsp),%rcx
  40637c:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
  406381:	45 85 c9             	test   %r9d,%r9d
  406384:	0f 8e c7 06 00 00    	jle    406a51 <barriered_work+0x851>
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  40638a:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  406391:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
  406396:	48 89 6c 24 38       	mov    %rbp,0x38(%rsp)
  40639b:	89 5c 24 40          	mov    %ebx,0x40(%rsp)
  40639f:	48 8b 40 20          	mov    0x20(%rax),%rax
  4063a3:	4c 89 1c 24          	mov    %r11,(%rsp)
  4063a7:	4a 8b 7c 18 38       	mov    0x38(%rax,%r11,1),%rdi
  4063ac:	44 89 e0             	mov    %r12d,%eax
  4063af:	49 89 cc             	mov    %rcx,%r12
  4063b2:	89 c1                	mov    %eax,%ecx
  4063b4:	0f 1f 40 00          	nopl   0x0(%rax)
                      int next_task = abs((nn + 1) % data->thread_count);
  4063b8:	48 63 d9             	movslq %ecx,%rbx
  4063bb:	83 c1 01             	add    $0x1,%ecx
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4063be:	be 01 00 00 00       	mov    $0x1,%esi
                      int next_task = abs((nn + 1) % data->thread_count);
  4063c3:	89 c8                	mov    %ecx,%eax
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4063c5:	48 c1 e3 09          	shl    $0x9,%rbx
                      int next_task = abs((nn + 1) % data->thread_count);
  4063c9:	89 4c 24 28          	mov    %ecx,0x28(%rsp)
  4063cd:	99                   	cltd
  4063ce:	41 f7 f9             	idiv   %r9d
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4063d1:	48 8b 84 1f 70 01 00 00 	mov    0x170(%rdi,%rbx,1),%rax
  4063d9:	4c 01 e0             	add    %r12,%rax
  4063dc:	48 89 c7             	mov    %rax,%rdi
                      int next_task = abs((nn + 1) % data->thread_count);
  4063df:	48 63 ea             	movslq %edx,%rbp
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4063e2:	e8 b9 fd ff ff       	call   4061a0 <mailboxkind>
                      struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  4063e7:	48 8b 0c 24          	mov    (%rsp),%rcx
  4063eb:	31 f6                	xor    %esi,%esi
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  4063ed:	48 c1 e5 09          	shl    $0x9,%rbp
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4063f1:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
                      struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  4063f6:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  4063fd:	48 8b 40 20          	mov    0x20(%rax),%rax
  406401:	48 8b 44 08 38       	mov    0x38(%rax,%rcx,1),%rax
  406406:	48 8b bc 18 70 01 00 00 	mov    0x170(%rax,%rbx,1),%rdi
  40640e:	4c 01 e7             	add    %r12,%rdi
  406411:	e8 8a fd ff ff       	call   4061a0 <mailboxkind>
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  406416:	31 f6                	xor    %esi,%esi
                      struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  406418:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
                      struct Mailbox* __a = &data->thread->all_threads[l2].tasks[l3].mailboxes[l4];
  40641d:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  406424:	48 8b 40 20          	mov    0x20(%rax),%rax
  406428:	4a 8b 44 28 38       	mov    0x38(%rax,%r13,1),%rax
  40642d:	48 8b bc 28 70 01 00 00 	mov    0x170(%rax,%rbp,1),%rdi
  406435:	4c 01 f7             	add    %r14,%rdi
  406438:	e8 63 fd ff ff       	call   4061a0 <mailboxkind>
                      struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  40643d:	be 01 00 00 00       	mov    $0x1,%esi
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  406442:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
                      struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  406447:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  40644e:	48 8b 40 20          	mov    0x20(%rax),%rax
  406452:	4a 8b 44 28 38       	mov    0x38(%rax,%r13,1),%rax
  406457:	48 8b bc 28 70 01 00 00 	mov    0x170(%rax,%rbp,1),%rdi
  40645f:	4c 01 f7             	add    %r14,%rdi
  406462:	e8 39 fd ff ff       	call   4061a0 <mailboxkind>
                        setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
  406467:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
  40646c:	31 d2                	xor    %edx,%edx
                      struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  40646e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
                        setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
  406473:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  40647a:	48 8b 40 20          	mov    0x20(%rax),%rax
  40647e:	4a 8b 44 28 38       	mov    0x38(%rax,%r13,1),%rax
  406483:	48 8b bc 28 70 01 00 00 	mov    0x170(%rax,%rbp,1),%rdi
  40648b:	4c 01 f7             	add    %r14,%rdi
  40648e:	e8 2d fd ff ff       	call   4061c0 <setmailboxkind>
                        setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source2, HIGHER);
  406493:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  406498:	ba 01 00 00 00       	mov    $0x1,%edx
  40649d:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  4064a4:	48 8b 40 20          	mov    0x20(%rax),%rax
  4064a8:	4a 8b 44 28 38       	mov    0x38(%rax,%r13,1),%rax
  4064ad:	48 8b bc 28 70 01 00 00 	mov    0x170(%rax,%rbp,1),%rdi
  4064b5:	4c 01 f7             	add    %r14,%rdi
  4064b8:	e8 03 fd ff ff       	call   4061c0 <setmailboxkind>
                        setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest2, LOWER);
  4064bd:	48 8b 0c 24          	mov    (%rsp),%rcx
  4064c1:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
  4064c6:	31 d2                	xor    %edx,%edx
  4064c8:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  4064cf:	48 8b 40 20          	mov    0x20(%rax),%rax
  4064d3:	48 8b 44 08 38       	mov    0x38(%rax,%rcx,1),%rax
  4064d8:	48 8b bc 18 70 01 00 00 	mov    0x170(%rax,%rbx,1),%rdi
  4064e0:	4c 01 e7             	add    %r12,%rdi
  4064e3:	e8 d8 fc ff ff       	call   4061c0 <setmailboxkind>
                        setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest, HIGHER);
  4064e8:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  4064ef:	48 8b 0c 24          	mov    (%rsp),%rcx
  4064f3:	ba 01 00 00 00       	mov    $0x1,%edx
  4064f8:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
  4064fd:	48 8b 40 20          	mov    0x20(%rax),%rax
  406501:	48 8b 44 08 38       	mov    0x38(%rax,%rcx,1),%rax
  406506:	48 8b bc 18 70 01 00 00 	mov    0x170(%rax,%rbx,1),%rdi
  40650e:	4c 01 e7             	add    %r12,%rdi
  406511:	e8 aa fc ff ff       	call   4061c0 <setmailboxkind>
                        data->thread->all_threads[l2].tasks[jj].swap = 1;
  406516:	49 8b b7 28 01 00 00 	mov    0x128(%r15),%rsi
                      for (int jj = 0 ; jj < data->thread_count; jj++) {
  40651d:	45 8b 8f 34 01 00 00 	mov    0x134(%r15),%r9d
                        data->thread->all_threads[l2].tasks[jj].swap = 1;
  406524:	48 8b 14 24          	mov    (%rsp),%rdx
                      for (int jj = 0 ; jj < data->thread_count; jj++) {
  406528:	8b 4c 24 28          	mov    0x28(%rsp),%ecx
                        data->thread->all_threads[l2].tasks[jj].swap = 1;
  40652c:	48 8b 46 20          	mov    0x20(%rsi),%rax
                      for (int jj = 0 ; jj < data->thread_count; jj++) {
  406530:	45 85 c9             	test   %r9d,%r9d
                        data->thread->all_threads[l2].tasks[jj].swap = 1;
  406533:	48 8b 7c 10 38       	mov    0x38(%rax,%rdx,1),%rdi
                        data->thread->all_threads[t2].tasks[jj].swap = 1;
  406538:	4a 8b 54 28 38       	mov    0x38(%rax,%r13,1),%rdx
                      for (int jj = 0 ; jj < data->thread_count; jj++) {
  40653d:	7e 32                	jle    406571 <barriered_work+0x371>
  40653f:	45 8d 41 ff          	lea    -0x1(%r9),%r8d
                        data->thread->all_threads[t2].tasks[jj].swap = 1;
  406543:	b8 98 01 00 00       	mov    $0x198,%eax
  406548:	49 c1 e0 09          	shl    $0x9,%r8
  40654c:	49 81 c0 98 03 00 00 	add    $0x398,%r8
  406553:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                        data->thread->all_threads[l2].tasks[jj].swap = 1;
  406558:	c7 04 07 01 00 00 00 	movl   $0x1,(%rdi,%rax,1)
                        data->thread->all_threads[t2].tasks[jj].swap = 1;
  40655f:	c7 04 02 01 00 00 00 	movl   $0x1,(%rdx,%rax,1)
                      for (int jj = 0 ; jj < data->thread_count; jj++) {
  406566:	48 05 00 02 00 00    	add    $0x200,%rax
  40656c:	49 39 c0             	cmp    %rax,%r8
  40656f:	75 e7                	jne    406558 <barriered_work+0x358>
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
  406571:	48 8b 84 1f 70 01 00 00 	mov    0x170(%rdi,%rbx,1),%rax
  406579:	4c 01 e0             	add    %r12,%rax
  40657c:	4c 8b 40 08          	mov    0x8(%rax),%r8
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
  406580:	48 8b 00             	mov    (%rax),%rax
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
  406583:	41 c7 80 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r8)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
  40658e:	4c 8b 84 1a 70 01 00 00 	mov    0x170(%rdx,%rbx,1),%r8
  406596:	4f 8b 44 30 08       	mov    0x8(%r8,%r14,1),%r8
  40659b:	41 c7 80 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r8)
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
  4065a6:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
  4065b0:	48 8b 84 2a 70 01 00 00 	mov    0x170(%rdx,%rbp,1),%rax
  4065b8:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
  4065bc:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                    for (int nn = 0; nn < data->thread_count; nn++) {
  4065c6:	44 39 c9             	cmp    %r9d,%ecx
  4065c9:	0f 8c e9 fd ff ff    	jl     4063b8 <barriered_work+0x1b8>
                      for (int nn = 0; nn < data->thread_count; nn++) {
  4065cf:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
  4065d4:	8b 5c 24 40          	mov    0x40(%rsp),%ebx
  4065d8:	4c 89 e1             	mov    %r12,%rcx
  4065db:	45 85 c9             	test   %r9d,%r9d
  4065de:	7e 41                	jle    406621 <barriered_work+0x421>
  4065e0:	45 8d 51 ff          	lea    -0x1(%r9),%r10d
  4065e4:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
  4065e9:	b8 70 01 00 00       	mov    $0x170,%eax
  4065ee:	49 c1 e2 09          	shl    $0x9,%r10
  4065f2:	49 81 c2 70 03 00 00 	add    $0x370,%r10
  4065f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
  406600:	4c 8b 04 02          	mov    (%rdx,%rax,1),%r8
  406604:	4c 8b 0c 07          	mov    (%rdi,%rax,1),%r9
  406608:	4f 8b 04 18          	mov    (%r8,%r11,1),%r8
  40660c:	4d 39 04 09          	cmp    %r8,(%r9,%rcx,1)
  406610:	0f 84 4e 04 00 00    	je     406a64 <barriered_work+0x864>
                      for (int nn = 0; nn < data->thread_count; nn++) {
  406616:	48 05 00 02 00 00    	add    $0x200,%rax
  40661c:	49 39 c2             	cmp    %rax,%r10
  40661f:	75 df                	jne    406600 <barriered_work+0x400>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
  406621:	41 8b 97 40 01 00 00 	mov    0x140(%r15),%edx
  406628:	e9 83 fc ff ff       	jmp    4062b0 <barriered_work+0xb0>
  40662d:	0f 1f 00             	nopl   (%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
  406630:	41 8b 96 48 01 00 00 	mov    0x148(%r14),%edx
  406637:	85 d2                	test   %edx,%edx
  406639:	0f 8e 22 fc ff ff    	jle    406261 <barriered_work+0x61>
        data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
  40663f:	49 8b b6 28 01 00 00 	mov    0x128(%r14),%rsi
  406646:	83 ea 01             	sub    $0x1,%edx
  406649:	48 c1 e2 09          	shl    $0x9,%rdx
  40664d:	48 63 46 08          	movslq 0x8(%rsi),%rax
  406651:	48 8b 4e 20          	mov    0x20(%rsi),%rcx
  406655:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
  406659:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
  40665d:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
  406661:	48 8b 70 38          	mov    0x38(%rax),%rsi
  406665:	48 8d 86 9c 01 00 00 	lea    0x19c(%rsi),%rax
  40666c:	48 8d 94 16 9c 03 00 00 	lea    0x39c(%rsi,%rdx,1),%rdx
  406674:	0f 1f 40 00          	nopl   0x0(%rax)
  406678:	83 00 01             	addl   $0x1,(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
  40667b:	48 05 00 02 00 00    	add    $0x200,%rax
  406681:	48 39 c2             	cmp    %rax,%rdx
  406684:	75 f2                	jne    406678 <barriered_work+0x478>
  406686:	e9 d6 fb ff ff       	jmp    406261 <barriered_work+0x61>
  40668b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  406690:	4d 89 fe             	mov    %r15,%r14
          int k = data->group;
  406693:	41 8b 86 94 01 00 00 	mov    0x194(%r14),%eax
            int y = (k * data->thread->threads_per_group) + data->thread_index;
  40669a:	8b be c4 00 00 00    	mov    0xc4(%rsi),%edi
          int k = data->group;
  4066a0:	89 44 24 38          	mov    %eax,0x38(%rsp)
            int y = (k * data->thread->threads_per_group) + data->thread_index;
  4066a4:	0f af c7             	imul   %edi,%eax
  4066a7:	41 03 86 30 01 00 00 	add    0x130(%r14),%eax
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  4066ae:	85 ff                	test   %edi,%edi
  4066b0:	0f 8e 9d 02 00 00    	jle    406953 <barriered_work+0x753>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  4066b6:	48 98                	cltq
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  4066b8:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
  4066c0:	4d 89 f5             	mov    %r14,%r13
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  4066c3:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
  4066c7:	48 c1 e0 06          	shl    $0x6,%rax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  4066cb:	48 8d 14 d2          	lea    (%rdx,%rdx,8),%rdx
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
  4066cf:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  4066d4:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
  4066dc:	48 63 54 24 4c       	movslq 0x4c(%rsp),%rdx
  4066e1:	48 89 0c 24          	mov    %rcx,(%rsp)
  4066e5:	48 c1 e2 09          	shl    $0x9,%rdx
  4066e9:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
  4066ee:	eb 11                	jmp    406701 <barriered_work+0x501>
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  4066f0:	83 44 24 08 01       	addl   $0x1,0x8(%rsp)
  4066f5:	8b 44 24 08          	mov    0x8(%rsp),%eax
  4066f9:	39 f8                	cmp    %edi,%eax
  4066fb:	0f 8d 4f 02 00 00    	jge    406950 <barriered_work+0x750>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  406701:	48 8b 0c 24          	mov    (%rsp),%rcx
              int b = (g * data->thread->threads_per_group) + m;
  406705:	8b 44 24 38          	mov    0x38(%rsp),%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  406709:	48 8b 56 20          	mov    0x20(%rsi),%rdx
              int b = (g * data->thread->threads_per_group) + m;
  40670d:	0f af c7             	imul   %edi,%eax
  406710:	03 44 24 08          	add    0x8(%rsp),%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  406714:	48 8b 54 0a 38       	mov    0x38(%rdx,%rcx,1),%rdx
  406719:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
  40671e:	48 98                	cltq
  406720:	49 89 c7             	mov    %rax,%r15
  406723:	48 8b 94 0a 70 01 00 00 	mov    0x170(%rdx,%rcx,1),%rdx
  40672b:	49 c1 e7 06          	shl    $0x6,%r15
              if (kind == MAILBOX_FRIEND) {
  40672f:	42 83 7c 3a 38 01    	cmpl   $0x1,0x38(%rdx,%r15,1)
  406735:	75 b9                	jne    4066f0 <barriered_work+0x4f0>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
  406737:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
  40673b:	41 8b 95 34 01 00 00 	mov    0x134(%r13),%edx
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
  406742:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
  406746:	4c 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%r14
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
  40674e:	85 d2                	test   %edx,%edx
  406750:	7e 9e                	jle    4066f0 <barriered_work+0x4f0>
  406752:	4c 89 f0             	mov    %r14,%rax
  406755:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
  40675a:	4d 89 ee             	mov    %r13,%r14
  40675d:	31 db                	xor    %ebx,%ebx
  40675f:	89 d1                	mov    %edx,%ecx
  406761:	49 89 c5             	mov    %rax,%r13
  406764:	e9 07 01 00 00       	jmp    406870 <barriered_work+0x670>
  406769:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                    struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  406770:	49 8b 86 28 01 00 00 	mov    0x128(%r14),%rax
  406777:	48 8b 0c 24          	mov    (%rsp),%rcx
  40677b:	be 01 00 00 00       	mov    $0x1,%esi
  406780:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
  406785:	48 8b 40 20          	mov    0x20(%rax),%rax
  406789:	48 8b 44 08 38       	mov    0x38(%rax,%rcx,1),%rax
  40678e:	48 03 bc 28 70 01 00 00 	add    0x170(%rax,%rbp,1),%rdi
  406796:	e8 05 fa ff ff       	call   4061a0 <mailboxkind>
                    setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
  40679b:	48 8b 0c 24          	mov    (%rsp),%rcx
  40679f:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
  4067a4:	31 d2                	xor    %edx,%edx
                    struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  4067a6:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
                    setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
  4067ab:	49 8b 86 28 01 00 00 	mov    0x128(%r14),%rax
  4067b2:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
  4067b7:	48 8b 40 20          	mov    0x20(%rax),%rax
  4067bb:	48 8b 44 08 38       	mov    0x38(%rax,%rcx,1),%rax
  4067c0:	48 03 bc 28 70 01 00 00 	add    0x170(%rax,%rbp,1),%rdi
  4067c8:	e8 f3 f9 ff ff       	call   4061c0 <setmailboxkind>
                    setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest2, LOWER);
  4067cd:	49 8b 86 28 01 00 00 	mov    0x128(%r14),%rax
  4067d4:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  4067d9:	31 d2                	xor    %edx,%edx
  4067db:	48 8b 40 20          	mov    0x20(%rax),%rax
  4067df:	4a 8b 44 28 38       	mov    0x38(%rax,%r13,1),%rax
  4067e4:	48 03 b4 18 70 01 00 00 	add    0x170(%rax,%rbx,1),%rsi
  4067ec:	48 89 f7             	mov    %rsi,%rdi
  4067ef:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
  4067f4:	e8 c7 f9 ff ff       	call   4061c0 <setmailboxkind>
                    setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest, HIGHER);
  4067f9:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  4067fe:	ba 01 00 00 00       	mov    $0x1,%edx
  406803:	49 8b 86 28 01 00 00 	mov    0x128(%r14),%rax
  40680a:	48 8b 40 20          	mov    0x20(%rax),%rax
  40680e:	4a 8b 44 28 38       	mov    0x38(%rax,%r13,1),%rax
  406813:	48 03 b4 18 70 01 00 00 	add    0x170(%rax,%rbx,1),%rsi
  40681b:	48 89 f7             	mov    %rsi,%rdi
  40681e:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  406823:	e8 98 f9 ff ff       	call   4061c0 <setmailboxkind>
                    setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source2, HIGHER);
  406828:	49 8b 86 28 01 00 00 	mov    0x128(%r14),%rax
  40682f:	48 8b 0c 24          	mov    (%rsp),%rcx
  406833:	4c 89 fe             	mov    %r15,%rsi
  406836:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
  40683b:	ba 01 00 00 00       	mov    $0x1,%edx
  406840:	48 8b 40 20          	mov    0x20(%rax),%rax
  406844:	48 8b 44 08 38       	mov    0x38(%rax,%rcx,1),%rax
  406849:	48 03 bc 28 70 01 00 00 	add    0x170(%rax,%rbp,1),%rdi
  406851:	e8 6a f9 ff ff       	call   4061c0 <setmailboxkind>
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
  406856:	41 8b 8e 34 01 00 00 	mov    0x134(%r14),%ecx
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  40685d:	49 8b b6 28 01 00 00 	mov    0x128(%r14),%rsi
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
  406864:	44 39 e1             	cmp    %r12d,%ecx
  406867:	0f 8e c5 00 00 00    	jle    406932 <barriered_work+0x732>
                    int next_task = abs((nn + 1) % (data->thread_count));
  40686d:	49 63 dc             	movslq %r12d,%rbx
  406870:	44 8d 63 01          	lea    0x1(%rbx),%r12d
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  406874:	48 c1 e3 09          	shl    $0x9,%rbx
  406878:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
                    int next_task = abs((nn + 1) % (data->thread_count));
  40687d:	44 89 e0             	mov    %r12d,%eax
  406880:	99                   	cltd
  406881:	f7 f9                	idiv   %ecx
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  406883:	48 8b 46 20          	mov    0x20(%rsi),%rax
  406887:	4a 8b 44 28 38       	mov    0x38(%rax,%r13,1),%rax
  40688c:	48 8b bc 18 70 01 00 00 	mov    0x170(%rax,%rbx,1),%rdi
  406894:	be 01 00 00 00       	mov    $0x1,%esi
  406899:	4c 01 ff             	add    %r15,%rdi
                    int next_task = abs((nn + 1) % (data->thread_count));
  40689c:	48 63 ea             	movslq %edx,%rbp
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  40689f:	e8 fc f8 ff ff       	call   4061a0 <mailboxkind>
                    struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  4068a4:	31 f6                	xor    %esi,%esi
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4068a6:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
                    struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  4068ab:	49 8b 86 28 01 00 00 	mov    0x128(%r14),%rax
  4068b2:	48 8b 40 20          	mov    0x20(%rax),%rax
  4068b6:	4a 8b 44 28 38       	mov    0x38(%rax,%r13,1),%rax
  4068bb:	48 8b bc 18 70 01 00 00 	mov    0x170(%rax,%rbx,1),%rdi
  4068c3:	4c 01 ff             	add    %r15,%rdi
  4068c6:	e8 d5 f8 ff ff       	call   4061a0 <mailboxkind>
                      if (source2->messages_count != 0) { 
  4068cb:	48 83 b8 80 00 00 00 00 	cmpq   $0x0,0x80(%rax)
                    struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  4068d3:	49 89 c7             	mov    %rax,%r15
                      if (source2->messages_count != 0) { 
  4068d6:	0f 85 54 01 00 00    	jne    406a30 <barriered_work+0x830>
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  4068dc:	48 8b 0c 24          	mov    (%rsp),%rcx
  4068e0:	48 c1 e5 09          	shl    $0x9,%rbp
  4068e4:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
  4068e9:	31 f6                	xor    %esi,%esi
                    struct Mailbox* __a = &data->thread->all_threads[l2].tasks[l3].mailboxes[l4];
  4068eb:	49 8b 86 28 01 00 00 	mov    0x128(%r14),%rax
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  4068f2:	48 8b 40 20          	mov    0x20(%rax),%rax
  4068f6:	48 8b 44 08 38       	mov    0x38(%rax,%rcx,1),%rax
  4068fb:	48 03 bc 28 70 01 00 00 	add    0x170(%rax,%rbp,1),%rdi
  406903:	e8 98 f8 ff ff       	call   4061a0 <mailboxkind>
                      if (dest->messages_count != 0) { 
  406908:	48 83 b8 80 00 00 00 00 	cmpq   $0x0,0x80(%rax)
  406910:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  406915:	0f 84 55 fe ff ff    	je     406770 <barriered_work+0x570>
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
  40691b:	41 8b 8e 34 01 00 00 	mov    0x134(%r14),%ecx
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  406922:	49 8b b6 28 01 00 00 	mov    0x128(%r14),%rsi
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
  406929:	41 39 cc             	cmp    %ecx,%r12d
  40692c:	0f 8c 3b ff ff ff    	jl     40686d <barriered_work+0x66d>
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  406932:	8b be c4 00 00 00    	mov    0xc4(%rsi),%edi
  406938:	83 44 24 08 01       	addl   $0x1,0x8(%rsp)
  40693d:	4d 89 f5             	mov    %r14,%r13
  406940:	8b 44 24 08          	mov    0x8(%rsp),%eax
  406944:	39 f8                	cmp    %edi,%eax
  406946:	0f 8c b5 fd ff ff    	jl     406701 <barriered_work+0x501>
  40694c:	0f 1f 40 00          	nopl   0x0(%rax)
  406950:	4d 89 ee             	mov    %r13,%r14
      receive(data);
  406953:	4c 89 f7             	mov    %r14,%rdi
  406956:	e8 35 f5 ff ff       	call   405e90 <receive>
      asm volatile ("sfence" ::: "memory");
  40695b:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
  40695e:	49 8b b6 60 01 00 00 	mov    0x160(%r14),%rsi
  406965:	31 ff                	xor    %edi,%edi
  406967:	48 c1 e6 05          	shl    $0x5,%rsi
  40696b:	49 03 b6 50 01 00 00 	add    0x150(%r14),%rsi
  406972:	e8 09 b7 ff ff       	call   402080 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
  406977:	49 8b 86 28 01 00 00 	mov    0x128(%r14),%rax
    while (data->scheduled == 1) {
  40697e:	41 83 be 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r14)
    int modcount = ++data->thread->protected_state->modcount;
  406986:	48 8b 50 48          	mov    0x48(%rax),%rdx
  40698a:	8b 4a 10             	mov    0x10(%rdx),%ecx
  40698d:	8d 59 01             	lea    0x1(%rcx),%ebx
  406990:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
  406993:	75 56                	jne    4069eb <barriered_work+0x7eb>
  406995:	0f 1f 00             	nopl   (%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
  406998:	49 63 96 30 01 00 00 	movslq 0x130(%r14),%rdx
  40699f:	48 8b 40 18          	mov    0x18(%rax),%rax
  4069a3:	49 63 7e 04          	movslq 0x4(%r14),%rdi
      data->n++;
  4069a7:	49 83 86 08 01 00 00 01 	addq   $0x1,0x108(%r14)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
  4069af:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
  4069b3:	48 c1 e7 09          	shl    $0x9,%rdi
  4069b7:	48 03 78 38          	add    0x38(%rax),%rdi
  4069bb:	41 ff 96 20 01 00 00 	call   *0x120(%r14)
      asm volatile ("sfence" ::: "memory");
  4069c2:	0f ae f8             	sfence
    while (data->scheduled == 1) {
  4069c5:	41 83 be 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r14)
    if (modcount != data->thread->protected_state->modcount) {
  4069cd:	49 8b 86 28 01 00 00 	mov    0x128(%r14),%rax
    while (data->scheduled == 1) {
  4069d4:	74 c2                	je     406998 <barriered_work+0x798>
    if (modcount != data->thread->protected_state->modcount) {
  4069d6:	48 8b 40 48          	mov    0x48(%rax),%rax
  4069da:	3b 58 10             	cmp    0x10(%rax),%ebx
  4069dd:	74 0c                	je     4069eb <barriered_work+0x7eb>
  4069df:	48 8d 3d 60 08 00 00 	lea    0x860(%rip),%rdi        # 407246 <_IO_stdin_used+0x246>
  4069e6:	e8 75 b6 ff ff       	call   402060 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
  4069eb:	49 8b b6 60 01 00 00 	mov    0x160(%r14),%rsi
  4069f2:	31 ff                	xor    %edi,%edi
  4069f4:	48 c1 e6 05          	shl    $0x5,%rsi
  4069f8:	49 03 b6 50 01 00 00 	add    0x150(%r14),%rsi
  4069ff:	48 83 c6 10          	add    $0x10,%rsi
  406a03:	e8 78 b6 ff ff       	call   402080 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
  406a08:	49 8b 86 60 01 00 00 	mov    0x160(%r14),%rax
  406a0f:	48 83 c0 01          	add    $0x1,%rax
  406a13:	48 99                	cqto
  406a15:	49 f7 be 58 01 00 00 	idivq  0x158(%r14)
  406a1c:	49 89 96 60 01 00 00 	mov    %rdx,0x160(%r14)
  406a23:	e9 25 f8 ff ff       	jmp    40624d <barriered_work+0x4d>
  406a28:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                    struct Mailbox* __a = &data->thread->all_threads[l2].tasks[l3].mailboxes[l4];
  406a30:	49 8b b6 28 01 00 00 	mov    0x128(%r14),%rsi
  406a37:	4d 89 f5             	mov    %r14,%r13
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  406a3a:	8b be c4 00 00 00    	mov    0xc4(%rsi),%edi
  406a40:	e9 ab fc ff ff       	jmp    4066f0 <barriered_work+0x4f0>
            int y = (k * data->thread->threads_per_group) + data->thread_index;
  406a45:	49 8b b6 28 01 00 00 	mov    0x128(%r14),%rsi
  406a4c:	e9 42 fc ff ff       	jmp    406693 <barriered_work+0x493>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
  406a51:	41 8b 97 40 01 00 00 	mov    0x140(%r15),%edx
            int y = (k * data->thread->threads_per_group) + data->thread_index;
  406a58:	49 8b b7 28 01 00 00 	mov    0x128(%r15),%rsi
  406a5f:	e9 4c f8 ff ff       	jmp    4062b0 <barriered_work+0xb0>
  406a64:	bf 01 00 00 00       	mov    $0x1,%edi
  406a69:	48 8d 35 bb 07 00 00 	lea    0x7bb(%rip),%rsi        # 40722b <_IO_stdin_used+0x22b>
  406a70:	31 c0                	xor    %eax,%eax
  406a72:	e8 69 b7 ff ff       	call   4021e0 <__printf_chk@plt>
                          exit(1);
  406a77:	bf 01 00 00 00       	mov    $0x1,%edi
  406a7c:	e8 bf b7 ff ff       	call   402240 <exit@plt>
  406a81:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  406a8c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000406a90 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
  406a90:	55                   	push   %rbp
  406a91:	48 89 fd             	mov    %rdi,%rbp
  barriered_work_ingest(data);
  406a94:	e8 07 f0 ff ff       	call   405aa0 <barriered_work_ingest>
  barriered_work(data);
  406a99:	48 89 ef             	mov    %rbp,%rdi
}
  406a9c:	5d                   	pop    %rbp
  barriered_work(data);
  406a9d:	e9 5e f7 ff ff       	jmp    406200 <barriered_work>
  406aa2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  406aad:	0f 1f 00             	nopl   (%rax)

0000000000406ab0 <barriered_nulltask>:
}
  406ab0:	31 c0                	xor    %eax,%eax
  406ab2:	c3                   	ret
  406ab3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  406abe:	66 90                	xchg   %ax,%ax

0000000000406ac0 <barriered_steal>:
  406ac0:	31 c0                	xor    %eax,%eax
  406ac2:	c3                   	ret
  406ac3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  406ace:	66 90                	xchg   %ax,%ax

0000000000406ad0 <after>:
  return left.tv_sec > right.tv_sec &&
  406ad0:	31 c0                	xor    %eax,%eax
  406ad2:	48 39 d7             	cmp    %rdx,%rdi
  406ad5:	7e 08                	jle    406adf <after+0xf>
  406ad7:	31 c0                	xor    %eax,%eax
  406ad9:	48 39 ce             	cmp    %rcx,%rsi
  406adc:	0f 9f c0             	setg   %al
}
  406adf:	c3                   	ret

0000000000406ae0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
  406ae0:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
  406ae5:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
  406aea:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
  406aec:	48 39 d7             	cmp    %rdx,%rdi
  406aef:	7f 18                	jg     406b09 <within+0x29>
  406af1:	4d 39 d8             	cmp    %r11,%r8
  406af4:	0f 9e c2             	setle  %dl
  406af7:	48 39 ce             	cmp    %rcx,%rsi
  406afa:	0f 9e c0             	setle  %al
  406afd:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
  406aff:	31 c0                	xor    %eax,%eax
  406b01:	4d 39 d1             	cmp    %r10,%r9
  406b04:	0f 9e c0             	setle  %al
    return 1;
  406b07:	21 d0                	and    %edx,%eax
}
  406b09:	c3                   	ret
  406b0a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000406b10 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
  406b10:	48 83 ec 08          	sub    $0x8,%rsp
  if (after(left.start, right.start) && after(right.end, left.end)) {
  406b14:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  406b19:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
  406b1e:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
  406b23:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  406b28:	e8 a3 ff ff ff       	call   406ad0 <after>
  406b2d:	85 c0                	test   %eax,%eax
  406b2f:	74 21                	je     406b52 <overlap+0x42>
  406b31:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  406b36:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
  406b3b:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
  406b40:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
  406b45:	e8 86 ff ff ff       	call   406ad0 <after>
  406b4a:	85 c0                	test   %eax,%eax
  406b4c:	0f 85 ae 00 00 00    	jne    406c00 <overlap+0xf0>
  if (after(right.start, left.start) && after(left.end, right.end)) {
  406b52:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
  406b57:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
  406b5c:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
  406b61:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
  406b66:	e8 65 ff ff ff       	call   406ad0 <after>
  406b6b:	85 c0                	test   %eax,%eax
  406b6d:	74 1d                	je     406b8c <overlap+0x7c>
  406b6f:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
  406b74:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
  406b79:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
  406b7e:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  406b83:	e8 48 ff ff ff       	call   406ad0 <after>
  406b88:	85 c0                	test   %eax,%eax
  406b8a:	75 74                	jne    406c00 <overlap+0xf0>
  if (within(left.start, right.start, right.end, left.end) == 1) {
  406b8c:	ff 74 24 28          	push   0x28(%rsp)
  406b90:	ff 74 24 28          	push   0x28(%rsp)
  406b94:	4c 8b 44 24 50       	mov    0x50(%rsp),%r8
  406b99:	4c 8b 4c 24 58       	mov    0x58(%rsp),%r9
  406b9e:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
  406ba3:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
  406ba8:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
  406bad:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  406bb2:	e8 29 ff ff ff       	call   406ae0 <within>
  406bb7:	5e                   	pop    %rsi
  406bb8:	5f                   	pop    %rdi
  406bb9:	83 f8 01             	cmp    $0x1,%eax
  406bbc:	74 42                	je     406c00 <overlap+0xf0>
  if (within(right.start, left.start, left.end, right.end) == 1) {
  406bbe:	ff 74 24 48          	push   0x48(%rsp)
  406bc2:	ff 74 24 48          	push   0x48(%rsp)
  406bc6:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
  406bcb:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
  406bd0:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  406bd5:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
  406bda:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
  406bdf:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
  406be4:	e8 f7 fe ff ff       	call   406ae0 <within>
  406be9:	5a                   	pop    %rdx
  406bea:	59                   	pop    %rcx
  406beb:	83 f8 01             	cmp    $0x1,%eax
  406bee:	0f 94 c0             	sete   %al
}
  406bf1:	48 83 c4 08          	add    $0x8,%rsp
  if (within(right.start, left.start, left.end, right.end) == 1) {
  406bf5:	0f b6 c0             	movzbl %al,%eax
}
  406bf8:	c3                   	ret
  406bf9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    return 1;
  406c00:	b8 01 00 00 00       	mov    $0x1,%eax
}
  406c05:	48 83 c4 08          	add    $0x8,%rsp
  406c09:	c3                   	ret
  406c0a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000406c10 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
  406c10:	41 57                	push   %r15
  406c12:	48 89 f8             	mov    %rdi,%rax
  406c15:	41 56                	push   %r14
  406c17:	41 55                	push   %r13
  406c19:	41 54                	push   %r12
  406c1b:	55                   	push   %rbp
  406c1c:	53                   	push   %rbx
  406c1d:	48 83 ec 38          	sub    $0x38,%rsp
  406c21:	89 74 24 2c          	mov    %esi,0x2c(%rsp)
  for (int x = 0 ; x < thread_count; x++) {
  406c25:	85 f6                	test   %esi,%esi
  406c27:	0f 8e 7f 02 00 00    	jle    406eac <verify+0x29c>
  406c2d:	48 83 c0 38          	add    $0x38,%rax
  406c31:	c7 44 24 1c 00 00 00 00 	movl   $0x0,0x1c(%rsp)
  406c39:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  406c3e:	49 89 c7             	mov    %rax,%r15
    for (int z = 0 ; z < thread_count; z++) {
  406c41:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
  406c49:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
  406c4e:	8b 7c 24 28          	mov    0x28(%rsp),%edi
      if (z != x)  {
  406c52:	39 7c 24 1c          	cmp    %edi,0x1c(%rsp)
  406c56:	0f 84 79 01 00 00    	je     406dd5 <verify+0x1c5>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
  406c5c:	41 8b 57 08          	mov    0x8(%r15),%edx
  406c60:	85 d2                	test   %edx,%edx
  406c62:	0f 8e 6d 01 00 00    	jle    406dd5 <verify+0x1c5>
  406c68:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
  406c70:	8b 54 24 1c          	mov    0x1c(%rsp),%edx
  406c74:	48 8d 35 db 05 00 00 	lea    0x5db(%rip),%rsi        # 407256 <_IO_stdin_used+0x256>
  406c7b:	bf 01 00 00 00       	mov    $0x1,%edi
  406c80:	31 c0                	xor    %eax,%eax
  406c82:	e8 59 b5 ff ff       	call   4021e0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  406c87:	41 8b 46 08          	mov    0x8(%r14),%eax
  406c8b:	85 c0                	test   %eax,%eax
  406c8d:	0f 8e 2f 01 00 00    	jle    406dc2 <verify+0x1b2>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
  406c93:	48 63 6c 24 18       	movslq 0x18(%rsp),%rbp
  406c98:	49 8b 0f             	mov    (%r15),%rcx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  406c9b:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
  406ca3:	48 c1 e5 09          	shl    $0x9,%rbp
  406ca7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  406cb0:	4c 63 64 24 14       	movslq 0x14(%rsp),%r12
  406cb5:	49 8b 06             	mov    (%r14),%rax
  406cb8:	48 8d 35 ac 05 00 00 	lea    0x5ac(%rip),%rsi        # 40726b <_IO_stdin_used+0x26b>
  406cbf:	bf 01 00 00 00       	mov    $0x1,%edi
  406cc4:	48 8b 8c 29 60 01 00 00 	mov    0x160(%rcx,%rbp,1),%rcx
  406ccc:	4c 89 e3             	mov    %r12,%rbx
  406ccf:	48 c1 e3 09          	shl    $0x9,%rbx
  406cd3:	48 8b 94 18 60 01 00 00 	mov    0x160(%rax,%rbx,1),%rdx
  406cdb:	31 c0                	xor    %eax,%eax
  406cdd:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  406ce2:	e8 f9 b4 ff ff       	call   4021e0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  406ce7:	49 8b 0f             	mov    (%r15),%rcx
  406cea:	48 8b 94 29 60 01 00 00 	mov    0x160(%rcx,%rbp,1),%rdx
  406cf2:	48 85 d2             	test   %rdx,%rdx
  406cf5:	0f 8e b4 00 00 00    	jle    406daf <verify+0x19f>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406cfb:	49 8b 06             	mov    (%r14),%rax
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  406cfe:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406d06:	48 8b b4 18 60 01 00 00 	mov    0x160(%rax,%rbx,1),%rsi
  406d0e:	48 01 d8             	add    %rbx,%rax
  406d11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  406d18:	48 85 f6             	test   %rsi,%rsi
  406d1b:	0f 8e 4f 01 00 00    	jle    406e70 <verify+0x260>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
  406d21:	48 63 5c 24 10       	movslq 0x10(%rsp),%rbx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406d26:	45 31 ed             	xor    %r13d,%r13d
  406d29:	31 d2                	xor    %edx,%edx
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
  406d2b:	48 c1 e3 05          	shl    $0x5,%rbx
  406d2f:	90                   	nop
  406d30:	48 8b 80 50 01 00 00 	mov    0x150(%rax),%rax
  406d37:	48 c1 e2 05          	shl    $0x5,%rdx
  406d3b:	49 89 d4             	mov    %rdx,%r12
  406d3e:	ff 74 10 18          	push   0x18(%rax,%rdx,1)
  406d42:	ff 74 10 10          	push   0x10(%rax,%rdx,1)
  406d46:	ff 74 10 08          	push   0x8(%rax,%rdx,1)
  406d4a:	ff 34 10             	push   (%rax,%rdx,1)
  406d4d:	48 8b 84 29 50 01 00 00 	mov    0x150(%rcx,%rbp,1),%rax
  406d55:	ff 74 18 18          	push   0x18(%rax,%rbx,1)
  406d59:	ff 74 18 10          	push   0x10(%rax,%rbx,1)
  406d5d:	ff 74 18 08          	push   0x8(%rax,%rbx,1)
  406d61:	ff 34 18             	push   (%rax,%rbx,1)
  406d64:	e8 a7 fd ff ff       	call   406b10 <overlap>
  406d69:	48 83 c4 40          	add    $0x40,%rsp
  406d6d:	83 f8 01             	cmp    $0x1,%eax
  406d70:	0f 84 8a 00 00 00    	je     406e00 <verify+0x1f0>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406d76:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  406d7b:	49 03 06             	add    (%r14),%rax
  406d7e:	41 83 c5 01          	add    $0x1,%r13d
  406d82:	48 8b b0 60 01 00 00 	mov    0x160(%rax),%rsi
  406d89:	49 63 d5             	movslq %r13d,%rdx
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  406d8c:	49 8b 0f             	mov    (%r15),%rcx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406d8f:	48 39 f2             	cmp    %rsi,%rdx
  406d92:	7c 9c                	jl     406d30 <verify+0x120>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  406d94:	83 44 24 10 01       	addl   $0x1,0x10(%rsp)
  406d99:	48 8b 94 29 60 01 00 00 	mov    0x160(%rcx,%rbp,1),%rdx
  406da1:	48 63 7c 24 10       	movslq 0x10(%rsp),%rdi
  406da6:	48 39 d7             	cmp    %rdx,%rdi
  406da9:	0f 8c 69 ff ff ff    	jl     406d18 <verify+0x108>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  406daf:	83 44 24 14 01       	addl   $0x1,0x14(%rsp)
  406db4:	8b 44 24 14          	mov    0x14(%rsp),%eax
  406db8:	41 39 46 08          	cmp    %eax,0x8(%r14)
  406dbc:	0f 8f ee fe ff ff    	jg     406cb0 <verify+0xa0>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
  406dc2:	83 44 24 18 01       	addl   $0x1,0x18(%rsp)
  406dc7:	8b 44 24 18          	mov    0x18(%rsp),%eax
  406dcb:	41 39 47 08          	cmp    %eax,0x8(%r15)
  406dcf:	0f 8f 9b fe ff ff    	jg     406c70 <verify+0x60>
    for (int z = 0 ; z < thread_count; z++) {
  406dd5:	8b 44 24 28          	mov    0x28(%rsp),%eax
  406dd9:	49 81 c6 d8 00 00 00 	add    $0xd8,%r14
  406de0:	83 c0 01             	add    $0x1,%eax
  406de3:	39 44 24 2c          	cmp    %eax,0x2c(%rsp)
  406de7:	0f 84 d0 00 00 00    	je     406ebd <verify+0x2ad>
  406ded:	89 44 24 28          	mov    %eax,0x28(%rsp)
  406df1:	89 c7                	mov    %eax,%edi
  406df3:	e9 5a fe ff ff       	jmp    406c52 <verify+0x42>
  406df8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
  406e00:	49 8b 06             	mov    (%r14),%rax
  406e03:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406e08:	41 83 c5 01          	add    $0x1,%r13d
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
  406e0c:	4c 03 a4 38 50 01 00 00 	add    0x150(%rax,%rdi,1),%r12
  406e14:	49 8b 07             	mov    (%r15),%rax
  406e17:	bf 01 00 00 00       	mov    $0x1,%edi
  406e1c:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
  406e21:	4d 8b 4c 24 18       	mov    0x18(%r12),%r9
  406e26:	48 8b b4 28 50 01 00 00 	mov    0x150(%rax,%rbp,1),%rsi
  406e2e:	31 c0                	xor    %eax,%eax
  406e30:	48 01 de             	add    %rbx,%rsi
  406e33:	48 8b 16             	mov    (%rsi),%rdx
  406e36:	4c 8b 46 08          	mov    0x8(%rsi),%r8
  406e3a:	48 8d 35 f7 07 00 00 	lea    0x7f7(%rip),%rsi        # 407638 <_IO_stdin_used+0x638>
  406e41:	e8 9a b3 ff ff       	call   4021e0 <__printf_chk@plt>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406e46:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  406e4b:	49 03 06             	add    (%r14),%rax
  406e4e:	49 63 d5             	movslq %r13d,%rdx
  406e51:	48 8b b0 60 01 00 00 	mov    0x160(%rax),%rsi
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  406e58:	49 8b 0f             	mov    (%r15),%rcx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406e5b:	48 39 d6             	cmp    %rdx,%rsi
  406e5e:	0f 8f cc fe ff ff    	jg     406d30 <verify+0x120>
  406e64:	e9 2b ff ff ff       	jmp    406d94 <verify+0x184>
  406e69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  406e70:	44 8b 6c 24 10       	mov    0x10(%rsp),%r13d
  406e75:	41 83 c5 01          	add    $0x1,%r13d
  406e79:	49 63 c5             	movslq %r13d,%rax
  406e7c:	48 39 d0             	cmp    %rdx,%rax
  406e7f:	0f 8d 2a ff ff ff    	jge    406daf <verify+0x19f>
  406e85:	0f 1f 00             	nopl   (%rax)
  406e88:	41 83 c5 01          	add    $0x1,%r13d
  406e8c:	49 63 c5             	movslq %r13d,%rax
  406e8f:	48 39 c2             	cmp    %rax,%rdx
  406e92:	7f f4                	jg     406e88 <verify+0x278>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  406e94:	83 44 24 14 01       	addl   $0x1,0x14(%rsp)
  406e99:	8b 44 24 14          	mov    0x14(%rsp),%eax
  406e9d:	41 39 46 08          	cmp    %eax,0x8(%r14)
  406ea1:	0f 8f 09 fe ff ff    	jg     406cb0 <verify+0xa0>
  406ea7:	e9 16 ff ff ff       	jmp    406dc2 <verify+0x1b2>
}
  406eac:	48 83 c4 38          	add    $0x38,%rsp
  406eb0:	31 c0                	xor    %eax,%eax
  406eb2:	5b                   	pop    %rbx
  406eb3:	5d                   	pop    %rbp
  406eb4:	41 5c                	pop    %r12
  406eb6:	41 5d                	pop    %r13
  406eb8:	41 5e                	pop    %r14
  406eba:	41 5f                	pop    %r15
  406ebc:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
  406ebd:	8b 7c 24 1c          	mov    0x1c(%rsp),%edi
  406ec1:	49 81 c7 d8 00 00 00 	add    $0xd8,%r15
  406ec8:	8d 47 01             	lea    0x1(%rdi),%eax
  406ecb:	3b 7c 24 28          	cmp    0x28(%rsp),%edi
  406ecf:	74 db                	je     406eac <verify+0x29c>
  406ed1:	89 44 24 1c          	mov    %eax,0x1c(%rsp)
  406ed5:	e9 67 fd ff ff       	jmp    406c41 <verify+0x31>

Disassembly of section .fini:

0000000000406edc <_fini>:
  406edc:	f3 0f 1e fa          	endbr64
  406ee0:	48 83 ec 08          	sub    $0x8,%rsp
  406ee4:	48 83 c4 08          	add    $0x8,%rsp
  406ee8:	c3                   	ret
