
multibarrier-evented:     file format elf64-x86-64


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
  402020:	ff 35 32 7e 00 00    	push   0x7e32(%rip)        # 409e58 <_GLOBAL_OFFSET_TABLE_+0x8>
  402026:	ff 25 34 7e 00 00    	jmp    *0x7e34(%rip)        # 409e60 <_GLOBAL_OFFSET_TABLE_+0x10>
  40202c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000402030 <free@plt>:
  402030:	ff 25 32 7e 00 00    	jmp    *0x7e32(%rip)        # 409e68 <free@GLIBC_2.2.5>
  402036:	68 00 00 00 00       	push   $0x0
  40203b:	e9 e0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402040 <putchar@plt>:
  402040:	ff 25 2a 7e 00 00    	jmp    *0x7e2a(%rip)        # 409e70 <putchar@GLIBC_2.2.5>
  402046:	68 01 00 00 00       	push   $0x1
  40204b:	e9 d0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402050 <pthread_setaffinity_np@plt>:
  402050:	ff 25 22 7e 00 00    	jmp    *0x7e22(%rip)        # 409e78 <pthread_setaffinity_np@GLIBC_2.34>
  402056:	68 02 00 00 00       	push   $0x2
  40205b:	e9 c0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402060 <puts@plt>:
  402060:	ff 25 1a 7e 00 00    	jmp    *0x7e1a(%rip)        # 409e80 <puts@GLIBC_2.2.5>
  402066:	68 03 00 00 00       	push   $0x3
  40206b:	e9 b0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402070 <setsockopt@plt>:
  402070:	ff 25 12 7e 00 00    	jmp    *0x7e12(%rip)        # 409e88 <setsockopt@GLIBC_2.2.5>
  402076:	68 04 00 00 00       	push   $0x4
  40207b:	e9 a0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402080 <clock_gettime@plt>:
  402080:	ff 25 0a 7e 00 00    	jmp    *0x7e0a(%rip)        # 409e90 <clock_gettime@GLIBC_2.17>
  402086:	68 05 00 00 00       	push   $0x5
  40208b:	e9 90 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402090 <fclose@plt>:
  402090:	ff 25 02 7e 00 00    	jmp    *0x7e02(%rip)        # 409e98 <fclose@GLIBC_2.2.5>
  402096:	68 06 00 00 00       	push   $0x6
  40209b:	e9 80 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020a0 <strlen@plt>:
  4020a0:	ff 25 fa 7d 00 00    	jmp    *0x7dfa(%rip)        # 409ea0 <strlen@GLIBC_2.2.5>
  4020a6:	68 07 00 00 00       	push   $0x7
  4020ab:	e9 70 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020b0 <__stack_chk_fail@plt>:
  4020b0:	ff 25 f2 7d 00 00    	jmp    *0x7df2(%rip)        # 409ea8 <__stack_chk_fail@GLIBC_2.4>
  4020b6:	68 08 00 00 00       	push   $0x8
  4020bb:	e9 60 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020c0 <io_uring_submit@plt>:
  4020c0:	ff 25 ea 7d 00 00    	jmp    *0x7dea(%rip)        # 409eb0 <io_uring_submit@LIBURING_2.0>
  4020c6:	68 09 00 00 00       	push   $0x9
  4020cb:	e9 50 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020d0 <nanosleep@plt>:
  4020d0:	ff 25 e2 7d 00 00    	jmp    *0x7de2(%rip)        # 409eb8 <nanosleep@GLIBC_2.2.5>
  4020d6:	68 0a 00 00 00       	push   $0xa
  4020db:	e9 40 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020e0 <strrchr@plt>:
  4020e0:	ff 25 da 7d 00 00    	jmp    *0x7dda(%rip)        # 409ec0 <strrchr@GLIBC_2.2.5>
  4020e6:	68 0b 00 00 00       	push   $0xb
  4020eb:	e9 30 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020f0 <fputs@plt>:
  4020f0:	ff 25 d2 7d 00 00    	jmp    *0x7dd2(%rip)        # 409ec8 <fputs@GLIBC_2.2.5>
  4020f6:	68 0c 00 00 00       	push   $0xc
  4020fb:	e9 20 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402100 <close@plt>:
  402100:	ff 25 ca 7d 00 00    	jmp    *0x7dca(%rip)        # 409ed0 <close@GLIBC_2.2.5>
  402106:	68 0d 00 00 00       	push   $0xd
  40210b:	e9 10 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402110 <strtok_r@plt>:
  402110:	ff 25 c2 7d 00 00    	jmp    *0x7dc2(%rip)        # 409ed8 <strtok_r@GLIBC_2.2.5>
  402116:	68 0e 00 00 00       	push   $0xe
  40211b:	e9 00 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402120 <read@plt>:
  402120:	ff 25 ba 7d 00 00    	jmp    *0x7dba(%rip)        # 409ee0 <read@GLIBC_2.2.5>
  402126:	68 0f 00 00 00       	push   $0xf
  40212b:	e9 f0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402130 <calloc@plt>:
  402130:	ff 25 b2 7d 00 00    	jmp    *0x7db2(%rip)        # 409ee8 <calloc@GLIBC_2.2.5>
  402136:	68 10 00 00 00       	push   $0x10
  40213b:	e9 e0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402140 <strcmp@plt>:
  402140:	ff 25 aa 7d 00 00    	jmp    *0x7daa(%rip)        # 409ef0 <strcmp@GLIBC_2.2.5>
  402146:	68 11 00 00 00       	push   $0x11
  40214b:	e9 d0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402150 <__memcpy_chk@plt>:
  402150:	ff 25 a2 7d 00 00    	jmp    *0x7da2(%rip)        # 409ef8 <__memcpy_chk@GLIBC_2.3.4>
  402156:	68 12 00 00 00       	push   $0x12
  40215b:	e9 c0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402160 <stat@plt>:
  402160:	ff 25 9a 7d 00 00    	jmp    *0x7d9a(%rip)        # 409f00 <stat@GLIBC_2.33>
  402166:	68 13 00 00 00       	push   $0x13
  40216b:	e9 b0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402170 <memcpy@plt>:
  402170:	ff 25 92 7d 00 00    	jmp    *0x7d92(%rip)        # 409f08 <memcpy@GLIBC_2.14>
  402176:	68 14 00 00 00       	push   $0x14
  40217b:	e9 a0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402180 <io_uring_queue_init@plt>:
  402180:	ff 25 8a 7d 00 00    	jmp    *0x7d8a(%rip)        # 409f10 <io_uring_queue_init@LIBURING_2.0>
  402186:	68 15 00 00 00       	push   $0x15
  40218b:	e9 90 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402190 <eventfd_write@plt>:
  402190:	ff 25 82 7d 00 00    	jmp    *0x7d82(%rip)        # 409f18 <eventfd_write@GLIBC_2.7>
  402196:	68 16 00 00 00       	push   $0x16
  40219b:	e9 80 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021a0 <pthread_mutex_unlock@plt>:
  4021a0:	ff 25 7a 7d 00 00    	jmp    *0x7d7a(%rip)        # 409f20 <pthread_mutex_unlock@GLIBC_2.2.5>
  4021a6:	68 17 00 00 00       	push   $0x17
  4021ab:	e9 70 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021b0 <malloc@plt>:
  4021b0:	ff 25 72 7d 00 00    	jmp    *0x7d72(%rip)        # 409f28 <malloc@GLIBC_2.2.5>
  4021b6:	68 18 00 00 00       	push   $0x18
  4021bb:	e9 60 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021c0 <listen@plt>:
  4021c0:	ff 25 6a 7d 00 00    	jmp    *0x7d6a(%rip)        # 409f30 <listen@GLIBC_2.2.5>
  4021c6:	68 19 00 00 00       	push   $0x19
  4021cb:	e9 50 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021d0 <__strcpy_chk@plt>:
  4021d0:	ff 25 62 7d 00 00    	jmp    *0x7d62(%rip)        # 409f38 <__strcpy_chk@GLIBC_2.3.4>
  4021d6:	68 1a 00 00 00       	push   $0x1a
  4021db:	e9 40 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021e0 <__io_uring_get_cqe@plt>:
  4021e0:	ff 25 5a 7d 00 00    	jmp    *0x7d5a(%rip)        # 409f40 <__io_uring_get_cqe@LIBURING_2.0>
  4021e6:	68 1b 00 00 00       	push   $0x1b
  4021eb:	e9 30 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021f0 <__printf_chk@plt>:
  4021f0:	ff 25 52 7d 00 00    	jmp    *0x7d52(%rip)        # 409f48 <__printf_chk@GLIBC_2.3.4>
  4021f6:	68 1c 00 00 00       	push   $0x1c
  4021fb:	e9 20 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402200 <bind@plt>:
  402200:	ff 25 4a 7d 00 00    	jmp    *0x7d4a(%rip)        # 409f50 <bind@GLIBC_2.2.5>
  402206:	68 1d 00 00 00       	push   $0x1d
  40220b:	e9 10 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402210 <pthread_create@plt>:
  402210:	ff 25 42 7d 00 00    	jmp    *0x7d42(%rip)        # 409f58 <pthread_create@GLIBC_2.34>
  402216:	68 1e 00 00 00       	push   $0x1e
  40221b:	e9 00 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402220 <open@plt>:
  402220:	ff 25 3a 7d 00 00    	jmp    *0x7d3a(%rip)        # 409f60 <open@GLIBC_2.2.5>
  402226:	68 1f 00 00 00       	push   $0x1f
  40222b:	e9 f0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402230 <fopen@plt>:
  402230:	ff 25 32 7d 00 00    	jmp    *0x7d32(%rip)        # 409f68 <fopen@GLIBC_2.2.5>
  402236:	68 20 00 00 00       	push   $0x20
  40223b:	e9 e0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402240 <perror@plt>:
  402240:	ff 25 2a 7d 00 00    	jmp    *0x7d2a(%rip)        # 409f70 <perror@GLIBC_2.2.5>
  402246:	68 21 00 00 00       	push   $0x21
  40224b:	e9 d0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402250 <exit@plt>:
  402250:	ff 25 22 7d 00 00    	jmp    *0x7d22(%rip)        # 409f78 <exit@GLIBC_2.2.5>
  402256:	68 22 00 00 00       	push   $0x22
  40225b:	e9 c0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402260 <eventfd@plt>:
  402260:	ff 25 1a 7d 00 00    	jmp    *0x7d1a(%rip)        # 409f80 <eventfd@GLIBC_2.7>
  402266:	68 23 00 00 00       	push   $0x23
  40226b:	e9 b0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402270 <fwrite@plt>:
  402270:	ff 25 12 7d 00 00    	jmp    *0x7d12(%rip)        # 409f88 <fwrite@GLIBC_2.2.5>
  402276:	68 24 00 00 00       	push   $0x24
  40227b:	e9 a0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402280 <__fprintf_chk@plt>:
  402280:	ff 25 0a 7d 00 00    	jmp    *0x7d0a(%rip)        # 409f90 <__fprintf_chk@GLIBC_2.3.4>
  402286:	68 25 00 00 00       	push   $0x25
  40228b:	e9 90 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402290 <io_uring_register_eventfd@plt>:
  402290:	ff 25 02 7d 00 00    	jmp    *0x7d02(%rip)        # 409f98 <io_uring_register_eventfd@LIBURING_2.0>
  402296:	68 26 00 00 00       	push   $0x26
  40229b:	e9 80 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022a0 <pthread_join@plt>:
  4022a0:	ff 25 fa 7c 00 00    	jmp    *0x7cfa(%rip)        # 409fa0 <pthread_join@GLIBC_2.34>
  4022a6:	68 27 00 00 00       	push   $0x27
  4022ab:	e9 70 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022b0 <strerror@plt>:
  4022b0:	ff 25 f2 7c 00 00    	jmp    *0x7cf2(%rip)        # 409fa8 <strerror@GLIBC_2.2.5>
  4022b6:	68 28 00 00 00       	push   $0x28
  4022bb:	e9 60 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022c0 <pthread_mutex_init@plt>:
  4022c0:	ff 25 ea 7c 00 00    	jmp    *0x7cea(%rip)        # 409fb0 <pthread_mutex_init@GLIBC_2.2.5>
  4022c6:	68 29 00 00 00       	push   $0x29
  4022cb:	e9 50 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022d0 <pthread_mutex_lock@plt>:
  4022d0:	ff 25 e2 7c 00 00    	jmp    *0x7ce2(%rip)        # 409fb8 <pthread_mutex_lock@GLIBC_2.2.5>
  4022d6:	68 2a 00 00 00       	push   $0x2a
  4022db:	e9 40 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022e0 <__ctype_tolower_loc@plt>:
  4022e0:	ff 25 da 7c 00 00    	jmp    *0x7cda(%rip)        # 409fc0 <__ctype_tolower_loc@GLIBC_2.3>
  4022e6:	68 2b 00 00 00       	push   $0x2b
  4022eb:	e9 30 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022f0 <__sprintf_chk@plt>:
  4022f0:	ff 25 d2 7c 00 00    	jmp    *0x7cd2(%rip)        # 409fc8 <__sprintf_chk@GLIBC_2.3.4>
  4022f6:	68 2c 00 00 00       	push   $0x2c
  4022fb:	e9 20 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402300 <socket@plt>:
  402300:	ff 25 ca 7c 00 00    	jmp    *0x7cca(%rip)        # 409fd0 <socket@GLIBC_2.2.5>
  402306:	68 2d 00 00 00       	push   $0x2d
  40230b:	e9 10 fd ff ff       	jmp    402020 <_init+0x20>

Disassembly of section .text:

0000000000402310 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
  402310:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

static inline void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
  402316:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  40231e:	0f 0b                	ud2

0000000000402320 <add_read_request.cold>:
  402320:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  402328:	0f 0b                	ud2

000000000040232a <add_accept_request.cold>:
  40232a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  402332:	0f 0b                	ud2

0000000000402334 <io_thread.cold>:
  402334:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  40233c:	0f 0b                	ud2
  40233e:	66 90                	xchg   %ax,%ax

0000000000402340 <main>:
    }


  return 0;
}
int main() {
  402340:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  402342:	48 8d 3d 1f 53 00 00 	lea    0x531f(%rip),%rdi        # 407668 <_IO_stdin_used+0x668>
  402349:	41 56                	push   %r14
  40234b:	41 55                	push   %r13
  40234d:	4c 8d 2d 28 50 00 00 	lea    0x5028(%rip),%r13        # 40737c <_IO_stdin_used+0x37c>
  402354:	41 54                	push   %r12
  402356:	55                   	push   %rbp
  402357:	53                   	push   %rbx
  402358:	48 81 ec f8 00 00 00 	sub    $0xf8,%rsp
  40235f:	f3 0f 7e 3d 89 7c 00 00 	movq   0x7c89(%rip),%xmm7        # 409ff0 <_GLOBAL_OFFSET_TABLE_+0x1a0>
  402367:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  402370:	48 89 84 24 e8 00 00 00 	mov    %rax,0xe8(%rsp)
  402378:	31 c0                	xor    %eax,%eax
  40237a:	0f 16 3d 5f 7c 00 00 	movhps 0x7c5f(%rip),%xmm7        # 409fe0 <_GLOBAL_OFFSET_TABLE_+0x190>
  402381:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
  402389:	e8 d2 fc ff ff       	call   402060 <puts@plt>
  40238e:	bf 0a 00 00 00       	mov    $0xa,%edi
  402393:	e8 a8 fc ff ff       	call   402040 <putchar@plt>
  402398:	ba 01 00 00 00       	mov    $0x1,%edx
  40239d:	48 8d 35 d0 4e 00 00 	lea    0x4ed0(%rip),%rsi        # 407274 <_IO_stdin_used+0x274>
  4023a4:	31 c0                	xor    %eax,%eax
  4023a6:	bf 01 00 00 00       	mov    $0x1,%edi
  4023ab:	e8 40 fe ff ff       	call   4021f0 <__printf_chk@plt>
  4023b0:	ba 06 00 00 00       	mov    $0x6,%edx
  4023b5:	48 8d 35 c8 4e 00 00 	lea    0x4ec8(%rip),%rsi        # 407284 <_IO_stdin_used+0x284>
  4023bc:	31 c0                	xor    %eax,%eax
  4023be:	bf 01 00 00 00       	mov    $0x1,%edi
  4023c3:	e8 28 fe ff ff       	call   4021f0 <__printf_chk@plt>
  4023c8:	ba 03 00 00 00       	mov    $0x3,%edx
  4023cd:	48 8d 35 c5 4e 00 00 	lea    0x4ec5(%rip),%rsi        # 407299 <_IO_stdin_used+0x299>
  4023d4:	31 c0                	xor    %eax,%eax
  4023d6:	bf 01 00 00 00       	mov    $0x1,%edi
  4023db:	e8 10 fe ff ff       	call   4021f0 <__printf_chk@plt>
  4023e0:	ba 02 00 00 00       	mov    $0x2,%edx
  4023e5:	48 8d 35 bd 4e 00 00 	lea    0x4ebd(%rip),%rsi        # 4072a9 <_IO_stdin_used+0x2a9>
  4023ec:	31 c0                	xor    %eax,%eax
  4023ee:	bf 01 00 00 00       	mov    $0x1,%edi
  4023f3:	e8 f8 fd ff ff       	call   4021f0 <__printf_chk@plt>
  4023f8:	48 8d 3d c0 4e 00 00 	lea    0x4ec0(%rip),%rdi        # 4072bf <_IO_stdin_used+0x2bf>
  4023ff:	e8 5c fc ff ff       	call   402060 <puts@plt>
  402404:	ba 02 00 00 00       	mov    $0x2,%edx
  402409:	48 8d 35 cb 4e 00 00 	lea    0x4ecb(%rip),%rsi        # 4072db <_IO_stdin_used+0x2db>
  402410:	31 c0                	xor    %eax,%eax
  402412:	bf 01 00 00 00       	mov    $0x1,%edi
  402417:	e8 d4 fd ff ff       	call   4021f0 <__printf_chk@plt>
  40241c:	ba 0a 00 00 00       	mov    $0xa,%edx
  402421:	48 8d 35 cd 4e 00 00 	lea    0x4ecd(%rip),%rsi        # 4072f5 <_IO_stdin_used+0x2f5>
  402428:	31 c0                	xor    %eax,%eax
  40242a:	bf 01 00 00 00       	mov    $0x1,%edi
  40242f:	e8 bc fd ff ff       	call   4021f0 <__printf_chk@plt>
  402434:	ba 01 00 00 00       	mov    $0x1,%edx
  402439:	48 8d 35 c9 4e 00 00 	lea    0x4ec9(%rip),%rsi        # 407309 <_IO_stdin_used+0x309>
  402440:	31 c0                	xor    %eax,%eax
  402442:	bf 01 00 00 00       	mov    $0x1,%edi
  402447:	e8 a4 fd ff ff       	call   4021f0 <__printf_chk@plt>
  40244c:	ba 01 00 00 00       	mov    $0x1,%edx
  402451:	48 8d 35 c2 4e 00 00 	lea    0x4ec2(%rip),%rsi        # 40731a <_IO_stdin_used+0x31a>
  402458:	31 c0                	xor    %eax,%eax
  40245a:	bf 01 00 00 00       	mov    $0x1,%edi
  40245f:	e8 8c fd ff ff       	call   4021f0 <__printf_chk@plt>
  402464:	ba 02 00 00 00       	mov    $0x2,%edx
  402469:	48 8d 35 c2 4e 00 00 	lea    0x4ec2(%rip),%rsi        # 407332 <_IO_stdin_used+0x332>
  402470:	31 c0                	xor    %eax,%eax
  402472:	bf 01 00 00 00       	mov    $0x1,%edi
  402477:	e8 74 fd ff ff       	call   4021f0 <__printf_chk@plt>
  40247c:	ba 01 00 00 00       	mov    $0x1,%edx
  402481:	48 8d 35 48 52 00 00 	lea    0x5248(%rip),%rsi        # 4076d0 <_IO_stdin_used+0x6d0>
  402488:	31 c0                	xor    %eax,%eax
  40248a:	bf 01 00 00 00       	mov    $0x1,%edi
  40248f:	e8 5c fd ff ff       	call   4021f0 <__printf_chk@plt>
  402494:	ba 01 00 00 00       	mov    $0x1,%edx
  402499:	48 8d 35 60 52 00 00 	lea    0x5260(%rip),%rsi        # 407700 <_IO_stdin_used+0x700>
  4024a0:	31 c0                	xor    %eax,%eax
  4024a2:	bf 01 00 00 00       	mov    $0x1,%edi
  4024a7:	e8 44 fd ff ff       	call   4021f0 <__printf_chk@plt>
  4024ac:	ba 40 42 0f 00       	mov    $0xf4240,%edx
  4024b1:	48 8d 35 96 4e 00 00 	lea    0x4e96(%rip),%rsi        # 40734e <_IO_stdin_used+0x34e>
  4024b8:	31 c0                	xor    %eax,%eax
  4024ba:	bf 01 00 00 00       	mov    $0x1,%edi
  4024bf:	e8 2c fd ff ff       	call   4021f0 <__printf_chk@plt>
  4024c4:	ba 05 00 00 00       	mov    $0x5,%edx
  4024c9:	48 8d 35 98 4e 00 00 	lea    0x4e98(%rip),%rsi        # 407368 <_IO_stdin_used+0x368>
  4024d0:	31 c0                	xor    %eax,%eax
  4024d2:	bf 01 00 00 00       	mov    $0x1,%edi
  4024d7:	e8 14 fd ff ff       	call   4021f0 <__printf_chk@plt>
  4024dc:	48 8d 3d 12 4c 00 00 	lea    0x4c12(%rip),%rdi        # 4070f5 <_IO_stdin_used+0xf5>
  4024e3:	e8 78 fb ff ff       	call   402060 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
  4024e8:	be 18 00 00 00       	mov    $0x18,%esi
  4024ed:	bf 03 00 00 00       	mov    $0x3,%edi
  4024f2:	e8 39 fc ff ff       	call   402130 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  4024f7:	be d8 00 00 00       	mov    $0xd8,%esi
  
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  int cc = 0; 
  for (int x = 0 ; x < total_threads; x++) {
  4024fc:	31 ed                	xor    %ebp,%ebp
  int cc = 0; 
  4024fe:	31 db                	xor    %ebx,%ebx
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  402500:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
  402505:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  40250d:	e8 1e fc ff ff       	call   402130 <calloc@plt>
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  402512:	be 28 00 00 00       	mov    $0x28,%esi
  402517:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  40251c:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  402521:	e8 0a fc ff ff       	call   402130 <calloc@plt>
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  402526:	be 28 00 00 00       	mov    $0x28,%esi
  40252b:	bf 64 00 00 00       	mov    $0x64,%edi
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  402530:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  402535:	e8 f6 fb ff ff       	call   402130 <calloc@plt>
  40253a:	66 48 0f 6e f8       	movq   %rax,%xmm7
  40253f:	49 89 c4             	mov    %rax,%r12
  402542:	0f 16 7c 24 10       	movhps 0x10(%rsp),%xmm7
  402547:	0f 29 bc 24 d0 00 00 00 	movaps %xmm7,0xd0(%rsp)
    for (int y = 0 ; y < total_threads; y++) {
  40254f:	45 31 ff             	xor    %r15d,%r15d
  402552:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  402558:	46 8d 34 3b          	lea    (%rbx,%r15,1),%r14d
  40255c:	45 89 f8             	mov    %r15d,%r8d
  40255f:	89 e9                	mov    %ebp,%ecx
  402561:	4c 89 ee             	mov    %r13,%rsi
  402564:	44 89 f2             	mov    %r14d,%edx
  402567:	bf 01 00 00 00       	mov    $0x1,%edi
  40256c:	31 c0                	xor    %eax,%eax
  40256e:	41 83 c7 01          	add    $0x1,%r15d
  402572:	e8 79 fc ff ff       	call   4021f0 <__printf_chk@plt>
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
  402577:	4b 8d 04 b6          	lea    (%r14,%r14,4),%rax
  40257b:	31 f6                	xor    %esi,%esi
  40257d:	49 8d 3c c4          	lea    (%r12,%rax,8),%rdi
  402581:	e8 3a fd ff ff       	call   4022c0 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
  402586:	41 83 ff 0a          	cmp    $0xa,%r15d
  40258a:	75 cc                	jne    402558 <main+0x218>
      pthread_mutex_init(&swapmutex[cc++], NULL);
  40258c:	83 c3 0a             	add    $0xa,%ebx
  for (int x = 0 ; x < total_threads; x++) {
  40258f:	83 c5 01             	add    $0x1,%ebp
  402592:	83 fb 64             	cmp    $0x64,%ebx
  402595:	75 b8                	jne    40254f <main+0x20f>
  402597:	ba 06 00 00 00       	mov    $0x6,%edx
  40259c:	48 8d 35 e9 4d 00 00 	lea    0x4de9(%rip),%rsi        # 40738c <_IO_stdin_used+0x38c>
  4025a3:	bf 01 00 00 00       	mov    $0x1,%edi
  4025a8:	31 c0                	xor    %eax,%eax
  4025aa:	e8 41 fc ff ff       	call   4021f0 <__printf_chk@plt>
  4025af:	ba 0c 00 00 00       	mov    $0xc,%edx
  4025b4:	48 8d 35 e7 4d 00 00 	lea    0x4de7(%rip),%rsi        # 4073a2 <_IO_stdin_used+0x3a2>
  4025bb:	31 c0                	xor    %eax,%eax
  4025bd:	bf 01 00 00 00       	mov    $0x1,%edi
  4025c2:	e8 29 fc ff ff       	call   4021f0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
  4025c7:	be 10 00 00 00       	mov    $0x10,%esi
  4025cc:	bf 0c 00 00 00       	mov    $0xc,%edi
  4025d1:	e8 5a fb ff ff       	call   402130 <calloc@plt>
  4025d6:	48 89 84 24 b8 00 00 00 	mov    %rax,0xb8(%rsp)
  4025de:	49 89 c4             	mov    %rax,%r12
  4025e1:	48 8d 98 c0 00 00 00 	lea    0xc0(%rax),%rbx
  4025e8:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  4025f0:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
  4025f5:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  4025fd:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
  402602:	49 83 c4 10          	add    $0x10,%r12
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  402606:	e8 25 fb ff ff       	call   402130 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  40260b:	be 20 00 00 00       	mov    $0x20,%esi
  402610:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  402615:	49 89 44 24 f8       	mov    %rax,-0x8(%r12)
  40261a:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
  40261d:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
  402627:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  402631:	e8 fa fa ff ff       	call   402130 <calloc@plt>
  402636:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
  40263d:	4c 39 e3             	cmp    %r12,%rbx
  402640:	75 ae                	jne    4025f0 <main+0x2b0>
  402642:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
  40264a:	48 8b 5c 24 40       	mov    0x40(%rsp),%rbx
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
  int swap = 0;
  for (int k = 0 ; k < group_count ; k++) {
  40264f:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  402657:	45 31 ff             	xor    %r15d,%r15d
  int swap = 0;
  40265a:	c7 44 24 30 00 00 00 00 	movl   $0x0,0x30(%rsp)
  402662:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
  40266a:	48 89 9c 24 a0 00 00 00 	mov    %rbx,0xa0(%rsp)
  for (int x = 0 ; x < buffers_required; x++) {
  402672:	48 89 9c 24 80 00 00 00 	mov    %rbx,0x80(%rsp)
  40267a:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
  int cur_buffer = 0;
  402682:	c7 44 24 50 00 00 00 00 	movl   $0x0,0x50(%rsp)
  int curcpu = 0;
  40268a:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
  402692:	8b 44 24 10          	mov    0x10(%rsp),%eax
  402696:	01 c0                	add    %eax,%eax
  402698:	89 44 24 20          	mov    %eax,0x20(%rsp)
  40269c:	8b 44 24 50          	mov    0x50(%rsp),%eax
  4026a0:	8d 58 02             	lea    0x2(%rax),%ebx
        other = (x + 1) % total_threads;
        my_thread_data[0] = &thread_data[x]; 
        me_thread = 0;
        my_thread_data[1] = &thread_data[other]; 
        // printf("even %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
        thread_data[x].protected_state = &protected_state[k];
  4026a3:	89 84 24 b0 00 00 00 	mov    %eax,0xb0(%rsp)
  4026aa:	89 9c 24 b4 00 00 00 	mov    %ebx,0xb4(%rsp)
  4026b1:	48 8b 9c 24 80 00 00 00 	mov    0x80(%rsp),%rbx
  4026b9:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
  4026be:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
  4026c2:	8b 54 24 10          	mov    0x10(%rsp),%edx
  4026c6:	bf 01 00 00 00       	mov    $0x1,%edi
  4026cb:	31 c0                	xor    %eax,%eax
  4026cd:	48 8d 35 54 50 00 00 	lea    0x5054(%rip),%rsi        # 407728 <_IO_stdin_used+0x728>
  4026d4:	89 d9                	mov    %ebx,%ecx
  4026d6:	e8 15 fb ff ff       	call   4021f0 <__printf_chk@plt>
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  4026db:	be 08 00 00 00       	mov    $0x8,%esi
  4026e0:	bf 02 00 00 00       	mov    $0x2,%edi
  4026e5:	e8 46 fa ff ff       	call   402130 <calloc@plt>
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
  4026ea:	bf 01 00 00 00       	mov    $0x1,%edi
  4026ef:	be 80 00 00 00       	mov    $0x80,%esi
  4026f4:	66 48 0f 6e c8       	movq   %rax,%xmm1
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  4026f9:	49 89 c5             	mov    %rax,%r13
  4026fc:	0f 16 4c 24 40       	movhps 0x40(%rsp),%xmm1
  402701:	0f 29 0c 24          	movaps %xmm1,(%rsp)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
  402705:	e8 26 fa ff ff       	call   402130 <calloc@plt>
  40270a:	48 89 c5             	mov    %rax,%rbp
      if (x % 2 == 1) {
  40270d:	89 d8                	mov    %ebx,%eax
  40270f:	8d 5b ff             	lea    -0x1(%rbx),%ebx
  402712:	8d 78 01             	lea    0x1(%rax),%edi
  402715:	41 89 c0             	mov    %eax,%r8d
  402718:	89 7c 24 74          	mov    %edi,0x74(%rsp)
  40271c:	41 83 e0 01          	and    $0x1,%r8d
  402720:	0f 85 54 17 00 00    	jne    403e7a <main+0x1b3a>
  402726:	4c 63 e7             	movslq %edi,%r12
        my_thread_data[1] = &thread_data[other]; 
  402729:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  40272e:	4c 89 6c 24 58       	mov    %r13,0x58(%rsp)
        my_thread_data[1] = &thread_data[other]; 
  402733:	4b 8d 04 64          	lea    (%r12,%r12,2),%rax
  402737:	4d 89 e6             	mov    %r12,%r14
  40273a:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
  40273e:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
        thread_data[x].thread_index = 1;
  402742:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
  402747:	48 89 c7             	mov    %rax,%rdi
        thread_data[x].protected_state = &protected_state[k];
  40274a:	48 8b b4 24 88 00 00 00 	mov    0x88(%rsp),%rsi
  402752:	49 89 55 08          	mov    %rdx,0x8(%r13)
  402756:	44 89 f1             	mov    %r14d,%ecx
  402759:	49 89 45 00          	mov    %rax,0x0(%r13)
  40275d:	44 8b 6c 24 20       	mov    0x20(%rsp),%r13d
  402762:	31 c0                	xor    %eax,%eax
  402764:	48 89 77 48          	mov    %rsi,0x48(%rdi)
  402768:	48 8d 35 e9 4f 00 00 	lea    0x4fe9(%rip),%rsi        # 407758 <_IO_stdin_used+0x758>
        thread_data[x].thread_index = 1;
  40276f:	44 89 47 04          	mov    %r8d,0x4(%rdi)
  402773:	44 89 ea             	mov    %r13d,%edx
  402776:	bf 01 00 00 00       	mov    $0x1,%edi
  40277b:	e8 70 fa ff ff       	call   4021f0 <__printf_chk@plt>
      }
      printf("i am %d, other is %d my thread index is %d\n", x, other, thread_data[x].thread_index);
      thread_data[x].other = other;
  402780:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
  402785:	8b 4c 24 7c          	mov    0x7c(%rsp),%ecx
  402789:	31 c0                	xor    %eax,%eax
  40278b:	44 89 ea             	mov    %r13d,%edx
  40278e:	48 8d 35 f3 4f 00 00 	lea    0x4ff3(%rip),%rsi        # 407788 <_IO_stdin_used+0x788>
  402795:	44 89 b7 b8 00 00 00 	mov    %r14d,0xb8(%rdi)
  40279c:	bf 01 00 00 00       	mov    $0x1,%edi
  4027a1:	e8 4a fa ff ff       	call   4021f0 <__printf_chk@plt>
      // for (int j = 0 ; j < cores ; j++) {
        printf("assigning thread %d to core %d\n", x, curcpu);
        if (x < thread_count) {
  4027a6:	41 83 fd 01          	cmp    $0x1,%r13d
  4027aa:	0f 8f bd 16 00 00    	jg     403e6d <main+0x1b2d>
          CPU_SET(curcpu, sendercpu);
  4027b0:	48 63 44 24 7c       	movslq 0x7c(%rsp),%rax
  4027b5:	48 89 c7             	mov    %rax,%rdi
  4027b8:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
  4027be:	77 13                	ja     4027d3 <main+0x493>
  4027c0:	48 c1 e8 06          	shr    $0x6,%rax
  4027c4:	ba 01 00 00 00       	mov    $0x1,%edx
  4027c9:	89 f9                	mov    %edi,%ecx
  4027cb:	48 d3 e2             	shl    %cl,%rdx
  4027ce:	48 09 54 c5 00       	or     %rdx,0x0(%rbp,%rax,8)
          curcpu += 2;
  4027d3:	83 44 24 7c 02       	addl   $0x2,0x7c(%rsp)
            CPU_SET(j, sendercpu);
          }
        }
        
      // }
      thread_data[x].swapmutex = swapmutex;
  4027d8:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
      thread_data[x].cpu_set = sendercpu;
      thread_data[x].real_thread_index = x;
      thread_data[x].threads = my_thread_data;
      thread_data[x].all_threads = thread_data;
      thread_data[x].thread_count = 2;
      thread_data[x].group_count = group_count;
  4027dd:	48 8b 05 ac 54 00 00 	mov    0x54ac(%rip),%rax        # 407c90 <_IO_stdin_used+0xc90>
      thread_data[x].threads_per_group = threads_per_group;
      thread_data[x].total_thread_count = total_threads;
      thread_data[x].task_count = total_barrier_count;
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  4027e4:	be 10 00 00 00       	mov    $0x10,%esi
  4027e9:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].real_thread_index = x;
  4027ee:	44 8b 6c 24 20       	mov    0x20(%rsp),%r13d
      thread_data[x].threads = my_thread_data;
  4027f3:	66 0f 6f 14 24       	movdqa (%rsp),%xmm2
      thread_data[x].swapmutex = swapmutex;
  4027f8:	66 0f 6f b4 24 d0 00 00 00 	movdqa 0xd0(%rsp),%xmm6
      thread_data[x].group_count = group_count;
  402801:	49 89 86 c0 00 00 00 	mov    %rax,0xc0(%r14)
      thread_data[x].thread_count = 2;
  402808:	48 8b 05 89 54 00 00 	mov    0x5489(%rip),%rax        # 407c98 <_IO_stdin_used+0xc98>
      thread_data[x].cpu_set = sendercpu;
  40280f:	49 89 ae b0 00 00 00 	mov    %rbp,0xb0(%r14)
      thread_data[x].real_thread_index = x;
  402816:	45 89 6e 08          	mov    %r13d,0x8(%r14)
      thread_data[x].kind = KERNEL_THREAD;
  40281a:	41 c7 06 5f 00 00 00 	movl   $0x5f,(%r14)
      thread_data[x].thread_count = 2;
  402821:	49 89 46 28          	mov    %rax,0x28(%r14)
      thread_data[x].task_count = total_barrier_count;
  402825:	41 c7 46 40 03 00 00 00 	movl   $0x3,0x40(%r14)
      thread_data[x].swapmutex = swapmutex;
  40282d:	41 0f 11 b6 c8 00 00 00 	movups %xmm6,0xc8(%r14)
      thread_data[x].threads = my_thread_data;
  402835:	41 0f 11 56 18       	movups %xmm2,0x18(%r14)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  40283a:	e8 f1 f8 ff ff       	call   402130 <calloc@plt>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  40283f:	be 10 00 00 00       	mov    $0x10,%esi
  402844:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  402849:	49 89 46 68          	mov    %rax,0x68(%r14)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  40284d:	e8 de f8 ff ff       	call   402130 <calloc@plt>
      thread_data[x].timestamp_count = 0;
      thread_data[x].timestamp_limit = timestamp_limit;
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  402852:	be 28 00 00 00       	mov    $0x28,%esi
  402857:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].timestamp_count = 0;
  40285c:	66 0f 6f 1d bc 53 00 00 	movdqa 0x53bc(%rip),%xmm3        # 407c20 <_IO_stdin_used+0xc20>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  402864:	49 89 46 70          	mov    %rax,0x70(%r14)
      thread_data[x].timestamp_count = 0;
  402868:	41 0f 11 9e 80 00 00 00 	movups %xmm3,0x80(%r14)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  402870:	e8 bb f8 ff ff       	call   402130 <calloc@plt>
      thread_data[x].task_timestamp_count = 0;
      thread_data[x].task_timestamp_limit = timestamp_limit;

        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  402875:	bf 03 00 00 00       	mov    $0x3,%edi
  40287a:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_timestamp_count = 0;
  40287f:	66 0f 6f 25 99 53 00 00 	movdqa 0x5399(%rip),%xmm4        # 407c20 <_IO_stdin_used+0xc20>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  402887:	49 89 86 90 00 00 00 	mov    %rax,0x90(%r14)
      thread_data[x].task_timestamp_count = 0;
  40288e:	41 0f 11 a6 98 00 00 00 	movups %xmm4,0x98(%r14)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  402896:	e8 95 f8 ff ff       	call   402130 <calloc@plt>
              mailboxes[b].pending = NULL;
              data[0].finished_reading = 1;
              data[1].finished_reading = 1;
              mailboxes[b].kind = MAILBOX_FRIEND;
              if (x % 2 == 0) { 
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
  40289b:	8b 7c 24 74          	mov    0x74(%rsp),%edi
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  40289f:	48 89 c5             	mov    %rax,%rbp
        thread_data[x].tasks = barriers;
  4028a2:	49 89 46 38          	mov    %rax,0x38(%r14)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
  4028a6:	49 69 c4 ab aa aa 2a 	imul   $0x2aaaaaab,%r12,%rax
  4028ad:	89 fa                	mov    %edi,%edx
  4028af:	c1 fa 1f             	sar    $0x1f,%edx
  4028b2:	48 c1 e8 20          	shr    $0x20,%rax
  4028b6:	29 d0                	sub    %edx,%eax
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
  4028b8:	48 89 ea             	mov    %rbp,%rdx
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
  4028bb:	8d 04 40             	lea    (%rax,%rax,2),%eax
  4028be:	01 c0                	add    %eax,%eax
  4028c0:	29 c7                	sub    %eax,%edi
  4028c2:	41 83 e5 01          	and    $0x1,%r13d
  4028c6:	0f 44 df             	cmove  %edi,%ebx
        for (int y = 0 ; y < total_barrier_count ; y++) {
  4028c9:	45 31 e4             	xor    %r12d,%r12d
  4028cc:	89 5c 24 78          	mov    %ebx,0x78(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
  4028d0:	49 63 c4             	movslq %r12d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
  4028d3:	be 38 00 00 00       	mov    $0x38,%esi
  4028d8:	bf 06 00 00 00       	mov    $0x6,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  4028dd:	45 31 f6             	xor    %r14d,%r14d
          thread_data[x].tasks[y].protected = do_protected_write; 
  4028e0:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
  4028e5:	48 c1 e0 09          	shl    $0x9,%rax
  4028e9:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
  4028ed:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  4028f2:	48 c7 c0 d0 3f 40 00 	mov    $0x403fd0,%rax
  4028f9:	48 89 83 20 01 00 00 	mov    %rax,0x120(%rbx)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
  402900:	e8 2b f8 ff ff       	call   402130 <calloc@plt>
  402905:	44 8b 6c 24 10       	mov    0x10(%rsp),%r13d
          thread_data[x].tasks[y].mailboxes = mailboxes;
  40290a:	48 89 83 70 01 00 00 	mov    %rax,0x170(%rbx)
  402911:	48 89 c3             	mov    %rax,%rbx
  402914:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  402919:	eb 17                	jmp    402932 <main+0x5f2>
  40291b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  402920:	41 83 c6 01          	add    $0x1,%r14d
  402924:	48 83 c3 38          	add    $0x38,%rbx
  402928:	41 83 fe 06          	cmp    $0x6,%r14d
  40292c:	0f 84 47 01 00 00    	je     402a79 <main+0x739>
            int group_of = b / threads_per_group;
  402932:	44 89 f5             	mov    %r14d,%ebp
  402935:	31 c0                	xor    %eax,%eax
  402937:	44 89 f2             	mov    %r14d,%edx
  40293a:	bf 01 00 00 00       	mov    $0x1,%edi
  40293f:	d1 fd                	sar    %ebp
  402941:	48 8d 35 74 4a 00 00 	lea    0x4a74(%rip),%rsi        # 4073bc <_IO_stdin_used+0x3bc>
  402948:	89 e9                	mov    %ebp,%ecx
  40294a:	e8 a1 f8 ff ff       	call   4021f0 <__printf_chk@plt>
            if (k == group_of) {
  40294f:	44 39 ed             	cmp    %r13d,%ebp
  402952:	75 cc                	jne    402920 <main+0x5e0>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402954:	be 08 00 00 00       	mov    $0x8,%esi
  402959:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  40295e:	48 83 c3 38          	add    $0x38,%rbx
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402962:	e8 c9 f7 ff ff       	call   402130 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402967:	be 08 00 00 00       	mov    $0x8,%esi
  40296c:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402971:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402976:	e8 b5 f7 ff ff       	call   402130 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
  40297b:	be 80 03 00 00       	mov    $0x380,%esi
  402980:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402985:	48 89 04 24          	mov    %rax,(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
  402989:	e8 a2 f7 ff ff       	call   402130 <calloc@plt>
              data[0].a = x;
  40298e:	8b 7c 24 20          	mov    0x20(%rsp),%edi
              mailboxes[b].pending = NULL;
  402992:	48 c7 43 d8 00 00 00 00 	movq   $0x0,-0x28(%rbx)
  40299a:	44 89 f2             	mov    %r14d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
  40299d:	48 89 c5             	mov    %rax,%rbp
              data[0].c = b;
  4029a0:	44 89 b0 24 03 00 00 	mov    %r14d,0x324(%rax)
  4029a7:	48 8d 35 fa 4d 00 00 	lea    0x4dfa(%rip),%rsi        # 4077a8 <_IO_stdin_used+0x7a8>
              data[0].a = x;
  4029ae:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              mailboxes[b].lower = &data[0];
  4029b4:	66 48 0f 6e c5       	movq   %rbp,%xmm0
              data[0].kind = MAILBOX_LOWER;
  4029b9:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].b = y;
  4029c3:	44 89 a0 20 03 00 00 	mov    %r12d,0x320(%rax)
              data[0].id = dataid++;
  4029ca:	41 8d 47 01          	lea    0x1(%r15),%eax
              data[1].id = dataid++;
  4029ce:	89 85 a8 06 00 00    	mov    %eax,0x6a8(%rbp)
              mailboxes[b].higher = &data[1];
  4029d4:	48 8d 85 80 03 00 00 	lea    0x380(%rbp),%rax
              mailboxes[b].lower = &data[0];
  4029db:	66 48 0f 6e d0       	movq   %rax,%xmm2
  4029e0:	8b 44 24 78          	mov    0x78(%rsp),%eax
              data[0].id = dataid++;
  4029e4:	44 89 bd 28 03 00 00 	mov    %r15d,0x328(%rbp)
              data[1].id = dataid++;
  4029eb:	41 83 c7 02          	add    $0x2,%r15d
              data[1].a = x;
  4029ef:	89 bd 9c 06 00 00    	mov    %edi,0x69c(%rbp)
              mailboxes[b].lower = &data[0];
  4029f5:	66 0f 6c c2          	punpcklqdq %xmm2,%xmm0
  4029f9:	bf 01 00 00 00       	mov    $0x1,%edi
  4029fe:	89 43 fc             	mov    %eax,-0x4(%rbx)
  402a01:	89 c1                	mov    %eax,%ecx
  402a03:	31 c0                	xor    %eax,%eax
              data[1].c = b;
  402a05:	44 89 b5 a4 06 00 00 	mov    %r14d,0x6a4(%rbp)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  402a0c:	41 83 c6 01          	add    $0x1,%r14d
              mailboxes[b].kind = MAILBOX_FRIEND;
  402a10:	c7 43 f8 01 00 00 00 	movl   $0x1,-0x8(%rbx)
              data[1].kind = MAILBOX_HIGHER;
  402a17:	c7 85 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%rbp)
              data[1].b = y;
  402a21:	44 89 a5 a0 06 00 00 	mov    %r12d,0x6a0(%rbp)
              data[0].finished_reading = 1;
  402a28:	c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rbp)
              data[1].finished_reading = 1;
  402a32:	c7 85 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%rbp)
              mailboxes[b].lower = &data[0];
  402a3c:	0f 11 43 c8          	movups %xmm0,-0x38(%rbx)
  402a40:	e8 ab f7 ff ff       	call   4021f0 <__printf_chk@plt>
              data[0].messages = messages;
  402a45:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
              data[1].messages = messages2;
  402a4a:	4c 8b 0c 24          	mov    (%rsp),%r9
              data[0].messages_count = 0;
  402a4e:	66 0f 6f 1d da 51 00 00 	movdqa 0x51da(%rip),%xmm3        # 407c30 <_IO_stdin_used+0xc30>
              data[0].messages = messages;
  402a56:	4c 89 55 00          	mov    %r10,0x0(%rbp)
              data[1].messages = messages2;
  402a5a:	4c 89 8d 80 03 00 00 	mov    %r9,0x380(%rbp)
              data[0].messages_count = 0;
  402a61:	0f 29 9d 80 00 00 00 	movaps %xmm3,0x80(%rbp)
              data[1].messages_count = 0;
  402a68:	0f 29 9d 00 04 00 00 	movaps %xmm3,0x400(%rbp)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  402a6f:	41 83 fe 06          	cmp    $0x6,%r14d
  402a73:	0f 85 b9 fe ff ff    	jne    402932 <main+0x5f2>
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  402a79:	48 8b 6c 24 68       	mov    0x68(%rsp),%rbp
  402a7e:	31 db                	xor    %ebx,%ebx
  402a80:	4c 8d 2d 45 49 00 00 	lea    0x4945(%rip),%r13        # 4073cc <_IO_stdin_used+0x3cc>
  402a87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
            int group_of = b / threads_per_group;
  402a90:	89 d8                	mov    %ebx,%eax
  402a92:	d1 f8                	sar    %eax
            if (k == group_of) {
  402a94:	3b 44 24 10          	cmp    0x10(%rsp),%eax
  402a98:	0f 84 5b 01 00 00    	je     402bf9 <main+0x8b9>
  402a9e:	89 da                	mov    %ebx,%edx
  402aa0:	4c 89 ee             	mov    %r13,%rsi
  402aa3:	bf 01 00 00 00       	mov    $0x1,%edi
  402aa8:	31 c0                	xor    %eax,%eax
  402aaa:	e8 41 f7 ff ff       	call   4021f0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402aaf:	be 08 00 00 00       	mov    $0x8,%esi
  402ab4:	bf 01 00 00 00       	mov    $0x1,%edi
  402ab9:	e8 72 f6 ff ff       	call   402130 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402abe:	be 08 00 00 00       	mov    $0x8,%esi
  402ac3:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402ac8:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402acd:	e8 5e f6 ff ff       	call   402130 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
  402ad2:	be 80 03 00 00       	mov    $0x380,%esi
  402ad7:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402adc:	48 89 04 24          	mov    %rax,(%rsp)
            struct Data *data = calloc(3, sizeof(struct Data));
  402ae0:	e8 4b f6 ff ff       	call   402130 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
  402ae5:	be 80 03 00 00       	mov    $0x380,%esi
  402aea:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
  402aef:	49 89 c6             	mov    %rax,%r14
            struct Data **stack = calloc(3, sizeof(struct Data));
  402af2:	e8 39 f6 ff ff       	call   402130 <calloc@plt>
            data[0].id = dataid++;
  402af7:	41 8d 77 01          	lea    0x1(%r15),%esi
            data[0].a = x;
  402afb:	8b 7c 24 20          	mov    0x20(%rsp),%edi
            data[0].messages = messages;
  402aff:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
            data[1].messages = messages2;
  402b04:	48 8b 14 24          	mov    (%rsp),%rdx
            data[0].messages_count = 0;
  402b08:	66 0f 6f 1d 20 51 00 00 	movdqa 0x5120(%rip),%xmm3        # 407c30 <_IO_stdin_used+0xc30>
            mailboxes[b].my_lower = &data[0];
  402b10:	4c 89 75 20          	mov    %r14,0x20(%rbp)
            mailboxes[b].lower = &data[0];
  402b14:	66 49 0f 6e c6       	movq   %r14,%xmm0
            data[1].id = dataid++;
  402b19:	41 89 b6 a8 06 00 00 	mov    %esi,0x6a8(%r14)
            mailboxes[b].higher = &data[1];
  402b20:	49 8d b6 80 03 00 00 	lea    0x380(%r14),%rsi
            mailboxes[b].lower = &data[0];
  402b27:	66 48 0f 6e d6       	movq   %rsi,%xmm2
            data[0].a = x;
  402b2c:	41 89 be 1c 03 00 00 	mov    %edi,0x31c(%r14)
            data[0].kind = MAILBOX_LOWER;
  402b33:	41 c7 86 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r14)
            mailboxes[b].lower = &data[0];
  402b3e:	66 0f 6c c2          	punpcklqdq %xmm2,%xmm0
            data[0].b = y;
  402b42:	45 89 a6 20 03 00 00 	mov    %r12d,0x320(%r14)
            data[0].c = b;
  402b49:	41 89 9e 24 03 00 00 	mov    %ebx,0x324(%r14)
            data[1].kind = MAILBOX_HIGHER;
  402b50:	41 c7 86 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r14)
            data[1].a = x;
  402b5b:	41 89 be 9c 06 00 00 	mov    %edi,0x69c(%r14)
            data[1].b = y;
  402b62:	45 89 a6 a0 06 00 00 	mov    %r12d,0x6a0(%r14)
            data[1].c = b;
  402b69:	41 89 9e a4 06 00 00 	mov    %ebx,0x6a4(%r14)
            mailboxes[b].pending = NULL;
  402b70:	48 c7 45 10 00 00 00 00 	movq   $0x0,0x10(%rbp)
            data[0].finished_reading = 1;
  402b78:	41 c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r14)
            data[1].finished_reading = 1;
  402b83:	41 c7 86 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r14)
            mailboxes[b].my_higher = &data[1];
  402b8e:	48 89 75 28          	mov    %rsi,0x28(%rbp)
            mailboxes[b].kind = MAILBOX_FOREIGN;
  402b92:	c7 45 30 02 00 00 00 	movl   $0x2,0x30(%rbp)
            stack[0] = mailboxes[b].lower;
  402b99:	4c 89 30             	mov    %r14,(%rax)
            stack[1] = mailboxes[b].higher;
  402b9c:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
  402ba0:	48 89 45 18          	mov    %rax,0x18(%rbp)
            data[0].available_sending = 0;
  402ba4:	41 c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r14)
            data[0].available_receiving = 0;
  402baf:	41 c7 86 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r14)
            data[0].messages = messages;
  402bba:	4d 89 0e             	mov    %r9,(%r14)
            data[1].messages = messages2;
  402bbd:	49 89 96 80 03 00 00 	mov    %rdx,0x380(%r14)
            data[1].available_sending = 1;
  402bc4:	41 c7 86 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r14)
            data[1].available_receiving = 0;
  402bcf:	41 c7 86 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r14)
            data[0].id = dataid++;
  402bda:	45 89 be 28 03 00 00 	mov    %r15d,0x328(%r14)
            data[1].id = dataid++;
  402be1:	41 83 c7 02          	add    $0x2,%r15d
            mailboxes[b].lower = &data[0];
  402be5:	0f 11 45 00          	movups %xmm0,0x0(%rbp)
            data[0].messages_count = 0;
  402be9:	41 0f 29 9e 80 00 00 00 	movaps %xmm3,0x80(%r14)
            data[1].messages_count = 0;
  402bf1:	41 0f 29 9e 00 04 00 00 	movaps %xmm3,0x400(%r14)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  402bf9:	83 c3 01             	add    $0x1,%ebx
  402bfc:	48 83 c5 38          	add    $0x38,%rbp
  402c00:	83 fb 06             	cmp    $0x6,%ebx
  402c03:	0f 85 87 fe ff ff    	jne    402a90 <main+0x750>
          char *message = malloc(sizeof(char) * 256);
  402c09:	be 01 00 00 00       	mov    $0x1,%esi
  402c0e:	bf 00 01 00 00       	mov    $0x100,%edi
  402c13:	e8 18 f5 ff ff       	call   402130 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
  402c18:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
  402c1d:	48 89 c3             	mov    %rax,%rbx
          struct Message *messaged = malloc(sizeof(struct Message));
  402c20:	e8 8b f5 ff ff       	call   4021b0 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  402c25:	48 83 ec 08          	sub    $0x8,%rsp
  402c29:	48 89 df             	mov    %rbx,%rdi
  402c2c:	45 89 e1             	mov    %r12d,%r9d
  402c2f:	8b 6c 24 18          	mov    0x18(%rsp),%ebp
  402c33:	49 89 c6             	mov    %rax,%r14
  402c36:	ba 00 01 00 00       	mov    $0x100,%edx
  402c3b:	31 c0                	xor    %eax,%eax
  402c3d:	48 8d 0d 8c 4b 00 00 	lea    0x4b8c(%rip),%rcx        # 4077d0 <_IO_stdin_used+0x7d0>
  402c44:	be 01 00 00 00       	mov    $0x1,%esi
  402c49:	55                   	push   %rbp
  402c4a:	44 8b 44 24 30       	mov    0x30(%rsp),%r8d
  402c4f:	e8 9c f6 ff ff       	call   4022f0 <__sprintf_chk@plt>
          messaged->group = k;
  402c54:	41 89 6e 18          	mov    %ebp,0x18(%r14)
  402c58:	89 e8                	mov    %ebp,%eax
          messaged->thread_index = thread_data[x].real_thread_index;
  402c5a:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
          messaged->message = message;
  402c5f:	49 89 1e             	mov    %rbx,(%r14)
          thread_data[x].tasks[y].swap = swap;
  402c62:	8b 7c 24 40          	mov    0x40(%rsp),%edi
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402c66:	41 8d 4c 24 01       	lea    0x1(%r12),%ecx
  402c6b:	66 0f 6e e8          	movd   %eax,%xmm5
          messaged->thread_index = thread_data[x].real_thread_index;
  402c6f:	48 63 5d 08          	movslq 0x8(%rbp),%rbx
          thread_data[x].tasks[y].swap = swap;
  402c73:	48 8b 55 38          	mov    0x38(%rbp),%rdx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402c77:	be 20 00 00 00       	mov    $0x20,%esi
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402c7c:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
          messaged->thread_index = thread_data[x].real_thread_index;
  402c80:	66 48 0f 6e c3       	movq   %rbx,%xmm0
          thread_data[x].tasks[y].swap = swap;
  402c85:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
  402c8a:	48 89 54 24 28       	mov    %rdx,0x28(%rsp)
          messaged->thread_index = thread_data[x].real_thread_index;
  402c8f:	0f 16 44 24 70       	movhps 0x70(%rsp),%xmm0
          thread_data[x].tasks[y].swap = swap;
  402c94:	48 01 d3             	add    %rdx,%rbx
          messaged->thread_index = thread_data[x].real_thread_index;
  402c97:	41 0f 11 46 08       	movups %xmm0,0x8(%r14)
          thread_data[x].tasks[y].swap = swap;
  402c9c:	89 bb 98 01 00 00    	mov    %edi,0x198(%rbx)
          swap += 1;
  402ca2:	83 c7 01             	add    $0x1,%edi
  402ca5:	89 7c 24 40          	mov    %edi,0x40(%rsp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402ca9:	89 cf                	mov    %ecx,%edi
  402cab:	83 e7 01             	and    $0x1,%edi
          thread_data[x].tasks[y].kind = BARRIER_TASK;
  402cae:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402cb4:	66 0f 6e c7          	movd   %edi,%xmm0
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402cb8:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].message = messaged;
  402cbd:	4c 89 b3 88 01 00 00 	mov    %r14,0x188(%rbx)
          thread_data[x].tasks[y].sending = 1;
  402cc4:	c7 83 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402cce:	66 0f 62 c5          	punpckldq %xmm5,%xmm0
          thread_data[x].tasks[y].snapshot_count = 99;
  402cd2:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402cdd:	66 0f d6 83 90 01 00 00 	movq   %xmm0,0x190(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402ce5:	e8 46 f4 ff ff       	call   402130 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
  402cea:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402cf5:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
  402cfc:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  402d01:	48 8b 00             	mov    (%rax),%rax
  402d04:	8b 70 04             	mov    0x4(%rax),%esi
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
  402d07:	48 39 e8             	cmp    %rbp,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
  402d0a:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
  402d11:	89 b3 30 01 00 00    	mov    %esi,0x130(%rbx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
  402d17:	5a                   	pop    %rdx
  402d18:	59                   	pop    %rcx
  402d19:	8b 0c 24             	mov    (%rsp),%ecx
  402d1c:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
  402d21:	0f 85 a2 11 00 00    	jne    403ec9 <main+0x1b89>
          thread_data[x].tasks[y].thread_count = 2;
  402d27:	66 0f 6f 35 11 4f 00 00 	movdqa 0x4f11(%rip),%xmm6        # 407c40 <_IO_stdin_used+0xc40>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
  402d2f:	44 89 63 04          	mov    %r12d,0x4(%rbx)
          thread_data[x].tasks[y].available = 1;
  402d33:	4c 8b 35 66 4f 00 00 	mov    0x4f66(%rip),%r14        # 407ca0 <_IO_stdin_used+0xca0>
          thread_data[x].tasks[y].arrived = 0;
  402d3a:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
          thread_data[x].tasks[y].worker_count = thread_count;
  402d44:	c7 83 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rbx)
          thread_data[x].tasks[y].available = 1;
  402d4e:	4c 89 b3 44 01 00 00 	mov    %r14,0x144(%rbx)
          thread_data[x].tasks[y].thread_count = 2;
  402d55:	0f 11 b3 34 01 00 00 	movups %xmm6,0x134(%rbx)
          if (y == barrier_count - 1) {
  402d5c:	41 83 fc 01          	cmp    $0x1,%r12d
  402d60:	0f 84 b6 10 00 00    	je     403e1c <main+0x1adc>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
  402d66:	45 85 e4             	test   %r12d,%r12d
  402d69:	0f 84 94 10 00 00    	je     403e03 <main+0x1ac3>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
  402d6f:	48 c7 c0 90 61 40 00 	mov    $0x406190,%rax
  402d76:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
  402d7d:	83 f9 03             	cmp    $0x3,%ecx
  402d80:	0f 85 38 11 00 00    	jne    403ebe <main+0x1b7e>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
  402d86:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
  402d8b:	bf 01 00 00 00       	mov    $0x1,%edi
  402d90:	be 08 00 00 00       	mov    $0x8,%esi
        thread_data[x].buffers_count = buffers_per_thread;
  402d95:	48 89 d5             	mov    %rdx,%rbp
  402d98:	c7 83 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%rbx)
    for (int d = 0 ; d < threads_per_group ; d++) {
  402da2:	48 81 c3 d8 00 00 00 	add    $0xd8,%rbx
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
  402da9:	e8 82 f3 ff ff       	call   402130 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
  402dae:	83 44 24 50 01       	addl   $0x1,0x50(%rsp)
  402db3:	8b 7c 24 50          	mov    0x50(%rsp),%edi
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
  402db7:	48 89 83 78 ff ff ff 	mov    %rax,-0x88(%rbx)
  402dbe:	48 89 c2             	mov    %rax,%rdx
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
  402dc1:	48 63 84 24 b0 00 00 00 	movslq 0xb0(%rsp),%rax
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
  402dc9:	66 0f 6f b4 24 c0 00 00 00 	movdqa 0xc0(%rsp),%xmm6
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
  402dd2:	48 c1 e0 04          	shl    $0x4,%rax
  402dd6:	48 03 84 24 b8 00 00 00 	add    0xb8(%rsp),%rax
  402dde:	48 89 02             	mov    %rax,(%rdx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
  402de1:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
  402de6:	0f 11 b5 18 05 00 00 	movups %xmm6,0x518(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
  402ded:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
  402df0:	c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rbp)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
  402dfa:	c7 85 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
  402e04:	48 89 85 28 05 00 00 	mov    %rax,0x528(%rbp)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
  402e0b:	c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
  402e15:	8b 83 2c ff ff ff    	mov    -0xd4(%rbx),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
  402e1b:	c7 85 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
  402e25:	89 85 30 05 00 00    	mov    %eax,0x530(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
  402e2b:	4c 89 b5 44 05 00 00 	mov    %r14,0x544(%rbp)
    for (int d = 0 ; d < threads_per_group ; d++) {
  402e32:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
  402e37:	39 bc 24 b4 00 00 00 	cmp    %edi,0xb4(%rsp)
  402e3e:	0f 85 11 10 00 00    	jne    403e55 <main+0x1b15>
  for (int k = 0 ; k < group_count ; k++) {
  402e44:	83 44 24 10 01       	addl   $0x1,0x10(%rsp)
  402e49:	8b 44 24 10          	mov    0x10(%rsp),%eax
  402e4d:	48 83 84 24 88 00 00 00 18 	addq   $0x18,0x88(%rsp)
  402e56:	48 81 84 24 80 00 00 00 b0 01 00 00 	addq   $0x1b0,0x80(%rsp)
  402e62:	83 f8 03             	cmp    $0x3,%eax
  402e65:	0f 85 27 f8 ff ff    	jne    402692 <main+0x352>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
  402e6b:	be 08 00 00 00       	mov    $0x8,%esi
  402e70:	bf 00 04 00 00       	mov    $0x400,%edi
  402e75:	45 31 ed             	xor    %r13d,%r13d
  int datas_size = 0; 
  402e78:	31 ed                	xor    %ebp,%ebp
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
  402e7a:	e8 b1 f2 ff ff       	call   402130 <calloc@plt>
  402e7f:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  402e84:	49 89 c7             	mov    %rax,%r15
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
  402e87:	4d 89 d9             	mov    %r11,%r9
  402e8a:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402e8c:	45 8b 51 40          	mov    0x40(%r9),%r10d
  402e90:	45 85 d2             	test   %r10d,%r10d
  402e93:	0f 8e ea 00 00 00    	jle    402f83 <main+0xc43>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402e99:	49 8b 51 38          	mov    0x38(%r9),%rdx
  402e9d:	41 8d 42 ff          	lea    -0x1(%r10),%eax
  402ea1:	48 c1 e0 09          	shl    $0x9,%rax
  402ea5:	48 8d b2 70 01 00 00 	lea    0x170(%rdx),%rsi
  402eac:	4c 8d 84 02 70 03 00 00 	lea    0x370(%rdx,%rax,1),%r8
  402eb4:	89 ea                	mov    %ebp,%edx
  402eb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  402ec0:	48 8b 06             	mov    (%rsi),%rax
  402ec3:	48 63 fa             	movslq %edx,%rdi
  402ec6:	89 d1                	mov    %edx,%ecx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402ec8:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402ecf:	49 8d 3c ff          	lea    (%r15,%rdi,8),%rdi
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402ed3:	83 c1 0b             	add    $0xb,%ecx
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402ed6:	f3 0f 6f 40 30       	movdqu 0x30(%rax),%xmm0
  402edb:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402ee0:	48 63 c9             	movslq %ecx,%rcx
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402ee3:	f3 0f 6f 30          	movdqu (%rax),%xmm6
  402ee7:	4c 8b 60 70          	mov    0x70(%rax),%r12
  402eeb:	66 0f c6 c5 01       	shufpd $0x1,%xmm5,%xmm0
  402ef0:	0f 11 47 10          	movups %xmm0,0x10(%rdi)
  402ef4:	0f 11 37             	movups %xmm6,(%rdi)
  402ef7:	8d 7a 04             	lea    0x4(%rdx),%edi
  402efa:	48 63 ff             	movslq %edi,%rdi
  402efd:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402f01:	4c 8b 60 78          	mov    0x78(%rax),%r12
  402f05:	8d 7a 05             	lea    0x5(%rdx),%edi
  402f08:	48 63 ff             	movslq %edi,%rdi
  402f0b:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402f0f:	4c 8b a0 a8 00 00 00 	mov    0xa8(%rax),%r12
  402f16:	8d 7a 06             	lea    0x6(%rdx),%edi
  402f19:	48 63 ff             	movslq %edi,%rdi
  402f1c:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402f20:	4c 8b a0 b0 00 00 00 	mov    0xb0(%rax),%r12
  402f27:	8d 7a 07             	lea    0x7(%rdx),%edi
  402f2a:	48 63 ff             	movslq %edi,%rdi
  402f2d:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402f31:	4c 8b a0 e0 00 00 00 	mov    0xe0(%rax),%r12
  402f38:	8d 7a 08             	lea    0x8(%rdx),%edi
  402f3b:	48 63 ff             	movslq %edi,%rdi
  402f3e:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402f42:	4c 8b a0 e8 00 00 00 	mov    0xe8(%rax),%r12
  402f49:	8d 7a 09             	lea    0x9(%rdx),%edi
  402f4c:	48 63 ff             	movslq %edi,%rdi
  402f4f:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402f53:	4c 8b a0 18 01 00 00 	mov    0x118(%rax),%r12
  402f5a:	8d 7a 0a             	lea    0xa(%rdx),%edi
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402f5d:	83 c2 0c             	add    $0xc,%edx
  402f60:	48 8b 80 20 01 00 00 	mov    0x120(%rax),%rax
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402f67:	48 63 ff             	movslq %edi,%rdi
  402f6a:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402f6e:	49 89 04 cf          	mov    %rax,(%r15,%rcx,8)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402f72:	49 39 f0             	cmp    %rsi,%r8
  402f75:	0f 85 45 ff ff ff    	jne    402ec0 <main+0xb80>
  402f7b:	43 8d 04 52          	lea    (%r10,%r10,2),%eax
  402f7f:	8d 6c 85 00          	lea    0x0(%rbp,%rax,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
  402f83:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
  402f8a:	83 fb 01             	cmp    $0x1,%ebx
  402f8d:	0f 85 b8 0e 00 00    	jne    403e4b <main+0x1b0b>
  for (int k = 0 ; k < group_count ; k++) {
  402f93:	41 83 c5 02          	add    $0x2,%r13d
  402f97:	49 81 c3 b0 01 00 00 	add    $0x1b0,%r11
  402f9e:	41 83 fd 06          	cmp    $0x6,%r13d
  402fa2:	0f 85 df fe ff ff    	jne    402e87 <main+0xb47>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  402fa8:	48 8d 3d 3b 44 00 00 	lea    0x443b(%rip),%rdi        # 4073ea <_IO_stdin_used+0x3ea>
  402faf:	e8 ac f0 ff ff       	call   402060 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
  402fb4:	48 8d 35 44 44 00 00 	lea    0x4444(%rip),%rsi        # 4073ff <_IO_stdin_used+0x3ff>
  402fbb:	48 8d 3d 3f 44 00 00 	lea    0x443f(%rip),%rdi        # 407401 <_IO_stdin_used+0x401>
  402fc2:	e8 69 f2 ff ff       	call   402230 <fopen@plt>
  402fc7:	49 89 c4             	mov    %rax,%r12
  for (int x = 0 ; x < datas_size; x++) {
  402fca:	85 ed                	test   %ebp,%ebp
  402fcc:	7e 70                	jle    40303e <main+0xcfe>
  402fce:	8d 45 ff             	lea    -0x1(%rbp),%eax
  402fd1:	48 8d 1d 4a 44 00 00 	lea    0x444a(%rip),%rbx        # 407422 <_IO_stdin_used+0x422>
  402fd8:	4d 8d 6c c7 08       	lea    0x8(%r15,%rax,8),%r13
  402fdd:	48 8d 2d fa 43 00 00 	lea    0x43fa(%rip),%rbp        # 4073de <_IO_stdin_used+0x3de>
    char * c = calloc(250, sizeof(char));
  402fe4:	be 01 00 00 00       	mov    $0x1,%esi
  402fe9:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
  402fee:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
  402ff2:	e8 39 f1 ff ff       	call   402130 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  402ff7:	48 89 e9             	mov    %rbp,%rcx
  402ffa:	ba fa 00 00 00       	mov    $0xfa,%edx
  402fff:	be 01 00 00 00       	mov    $0x1,%esi
  403004:	49 89 c6             	mov    %rax,%r14
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
  403007:	49 8b 47 f8          	mov    -0x8(%r15),%rax
  40300b:	4c 89 f7             	mov    %r14,%rdi
  40300e:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
  403015:	31 c0                	xor    %eax,%eax
  403017:	e8 d4 f2 ff ff       	call   4022f0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  40301c:	4c 89 f2             	mov    %r14,%rdx
  40301f:	48 89 de             	mov    %rbx,%rsi
  403022:	bf 01 00 00 00       	mov    $0x1,%edi
  403027:	31 c0                	xor    %eax,%eax
  403029:	e8 c2 f1 ff ff       	call   4021f0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  40302e:	4c 89 e6             	mov    %r12,%rsi
  403031:	4c 89 f7             	mov    %r14,%rdi
  403034:	e8 b7 f0 ff ff       	call   4020f0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
  403039:	4d 39 fd             	cmp    %r15,%r13
  40303c:	75 a6                	jne    402fe4 <main+0xca4>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
  40303e:	4c 89 e7             	mov    %r12,%rdi
  403041:	4c 8d 35 04 44 00 00 	lea    0x4404(%rip),%r14        # 40744c <_IO_stdin_used+0x44c>
  403048:	e8 43 f0 ff ff       	call   402090 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  40304d:	48 8d 3d b6 43 00 00 	lea    0x43b6(%rip),%rdi        # 40740a <_IO_stdin_used+0x40a>
  403054:	e8 07 f0 ff ff       	call   402060 <puts@plt>
  403059:	48 8b 44 24 40       	mov    0x40(%rsp),%rax

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
  40305e:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  403066:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  40306b:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
  40306f:	48 8d 35 af 43 00 00 	lea    0x43af(%rip),%rsi        # 407425 <_IO_stdin_used+0x425>
  403076:	bf 01 00 00 00       	mov    $0x1,%edi
  40307b:	31 c0                	xor    %eax,%eax
  40307d:	89 da                	mov    %ebx,%edx
  40307f:	e8 6c f1 ff ff       	call   4021f0 <__printf_chk@plt>
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
  403084:	89 d8                	mov    %ebx,%eax
  403086:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
  40308b:	c7 04 24 00 00 00 00 	movl   $0x0,(%rsp)
  403092:	01 c0                	add    %eax,%eax
  403094:	89 44 24 20          	mov    %eax,0x20(%rsp)
  403098:	8b 14 24             	mov    (%rsp),%edx
  40309b:	8b 4c 24 20          	mov    0x20(%rsp),%ecx
  40309f:	48 8d 35 89 43 00 00 	lea    0x4389(%rip),%rsi        # 40742f <_IO_stdin_used+0x42f>
  4030a6:	31 c0                	xor    %eax,%eax
  4030a8:	bf 01 00 00 00       	mov    $0x1,%edi
  4030ad:	45 31 ed             	xor    %r13d,%r13d
  4030b0:	01 d1                	add    %edx,%ecx
  4030b2:	e8 39 f1 ff ff       	call   4021f0 <__printf_chk@plt>
  4030b7:	44 89 ea             	mov    %r13d,%edx
  4030ba:	48 8d 35 80 43 00 00 	lea    0x4380(%rip),%rsi        # 407441 <_IO_stdin_used+0x441>
  4030c1:	31 c0                	xor    %eax,%eax
  4030c3:	4c 89 ed             	mov    %r13,%rbp
  4030c6:	bf 01 00 00 00       	mov    $0x1,%edi
  4030cb:	48 c1 e5 09          	shl    $0x9,%rbp
  4030cf:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
  4030d1:	45 31 ff             	xor    %r15d,%r15d
  4030d4:	e8 17 f1 ff ff       	call   4021f0 <__printf_chk@plt>
  4030d9:	eb 32                	jmp    40310d <main+0xdcd>
  4030db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
  4030e0:	83 fa 01             	cmp    $0x1,%edx
  4030e3:	0f 84 f7 0c 00 00    	je     403de0 <main+0x1aa0>
  4030e9:	44 8b 40 34          	mov    0x34(%rax),%r8d
  4030ed:	44 89 fa             	mov    %r15d,%edx
  4030f0:	4c 89 f6             	mov    %r14,%rsi
  4030f3:	bf 01 00 00 00       	mov    $0x1,%edi
  4030f8:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
  4030fa:	41 83 c7 01          	add    $0x1,%r15d
  4030fe:	48 83 c3 38          	add    $0x38,%rbx
  403102:	e8 e9 f0 ff ff       	call   4021f0 <__printf_chk@plt>
  403107:	41 83 ff 06          	cmp    $0x6,%r15d
  40310b:	74 44                	je     403151 <main+0xe11>
          char * mailbox_kind = calloc(100, sizeof(char));
  40310d:	be 01 00 00 00       	mov    $0x1,%esi
  403112:	bf 64 00 00 00       	mov    $0x64,%edi
  403117:	e8 14 f0 ff ff       	call   402130 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
  40311c:	49 8b 74 24 38       	mov    0x38(%r12),%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
  403121:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
  403124:	48 8b 84 2e 70 01 00 00 	mov    0x170(%rsi,%rbp,1),%rax
  40312c:	48 01 d8             	add    %rbx,%rax
  40312f:	8b 50 30             	mov    0x30(%rax),%edx
  403132:	83 fa 02             	cmp    $0x2,%edx
  403135:	75 a9                	jne    4030e0 <main+0xda0>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  403137:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
  403141:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
  403144:	48 8b 84 2e 70 01 00 00 	mov    0x170(%rsi,%rbp,1),%rax
  40314c:	48 01 d8             	add    %rbx,%rax
  40314f:	eb 98                	jmp    4030e9 <main+0xda9>
      for (int y = 0 ; y < total_barrier_count ; y++) {
  403151:	49 83 c5 01          	add    $0x1,%r13
  403155:	49 83 fd 03          	cmp    $0x3,%r13
  403159:	0f 85 58 ff ff ff    	jne    4030b7 <main+0xd77>
    for (int d = 0 ; d < threads_per_group ; d++) {
  40315f:	49 81 c4 d8 00 00 00 	add    $0xd8,%r12
  403166:	83 3c 24 01          	cmpl   $0x1,(%rsp)
  40316a:	0f 85 cf 0c 00 00    	jne    403e3f <main+0x1aff>
  for (int k = 0 ; k < group_count ; k++) {
  403170:	83 44 24 10 01       	addl   $0x1,0x10(%rsp)
  403175:	8b 44 24 10          	mov    0x10(%rsp),%eax
  403179:	48 81 44 24 18 b0 01 00 00 	addq   $0x1b0,0x18(%rsp)
  403182:	83 f8 03             	cmp    $0x3,%eax
  403185:	0f 85 e0 fe ff ff    	jne    40306b <main+0xd2b>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  40318b:	ba 07 00 00 00       	mov    $0x7,%edx
  403190:	bf 01 00 00 00       	mov    $0x1,%edi
  403195:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
  thread_data[timer_threadi].thread_index = 0;

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
  for (int k = 0 ; k < group_count ; k++) {
  403197:	45 31 ed             	xor    %r13d,%r13d
  40319a:	48 8d 35 c6 42 00 00 	lea    0x42c6(%rip),%rsi        # 407467 <_IO_stdin_used+0x467>
  4031a1:	e8 4a f0 ff ff       	call   4021f0 <__printf_chk@plt>
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  4031a6:	be 08 00 00 00       	mov    $0x8,%esi
  4031ab:	bf 02 00 00 00       	mov    $0x2,%edi
  4031b0:	e8 7b ef ff ff       	call   402130 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
  4031b5:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  4031ba:	be 38 00 00 00       	mov    $0x38,%esi
    my_thread_data[0] = &thread_data[x]; 
  4031bf:	49 8d be e8 05 00 00 	lea    0x5e8(%r14),%rdi
  4031c6:	66 49 0f 6e de       	movq   %r14,%xmm3
    thread_data[x].threads = my_thread_data;
  4031cb:	49 89 86 00 06 00 00 	mov    %rax,0x600(%r14)
  4031d2:	66 49 0f 6e ee       	movq   %r14,%xmm5
    my_thread_data[0] = &thread_data[x]; 
  4031d7:	66 48 0f 6e c7       	movq   %rdi,%xmm0
  4031dc:	48 89 3c 24          	mov    %rdi,(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  4031e0:	bf 0a 00 00 00       	mov    $0xa,%edi
    thread_data[x].thread_count = 2;
  4031e5:	41 c7 86 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%r14)
    my_thread_data[0] = &thread_data[x]; 
  4031f0:	66 0f 6c c3          	punpcklqdq %xmm3,%xmm0
  4031f4:	0f 11 00             	movups %xmm0,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
  4031f7:	49 8b 46 38          	mov    0x38(%r14),%rax
    thread_data[x].thread_index = 0;
  4031fb:	41 c7 86 ec 05 00 00 00 00 00 00 	movl   $0x0,0x5ec(%r14)
    thread_data[x].task_count = total_barrier_count;
  403206:	41 c7 86 28 06 00 00 03 00 00 00 	movl   $0x3,0x628(%r14)
    thread_data[n].tasks[0].scheduled = 1;
  403211:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  40321b:	49 8d 86 d8 00 00 00 	lea    0xd8(%r14),%rax
  403222:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  403227:	49 8b 86 10 01 00 00 	mov    0x110(%r14),%rax
  40322e:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403238:	0f 16 6c 24 10       	movhps 0x10(%rsp),%xmm5
  40323d:	0f 29 6c 24 30       	movaps %xmm5,0x30(%rsp)
  403242:	e8 e9 ee ff ff       	call   402130 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403247:	be 38 00 00 00       	mov    $0x38,%esi
  40324c:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403251:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403254:	e8 d7 ee ff ff       	call   402130 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403259:	be 38 00 00 00       	mov    $0x38,%esi
  40325e:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403263:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403266:	e8 c5 ee ff ff       	call   402130 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40326b:	be 38 00 00 00       	mov    $0x38,%esi
  403270:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403275:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40327a:	e8 b1 ee ff ff       	call   402130 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  40327f:	be 08 00 00 00       	mov    $0x8,%esi
  403284:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403289:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  40328e:	e8 9d ee ff ff       	call   402130 <calloc@plt>
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
  403293:	be 08 00 00 00       	mov    $0x8,%esi
  403298:	bf 0a 00 00 00       	mov    $0xa,%edi
  thread_data[timer_threadi].type = TIMER;
  40329d:	41 c7 86 1c 05 00 00 00 00 00 00 	movl   $0x0,0x51c(%r14)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  4032a8:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
  4032ab:	48 8b 05 f6 49 00 00 	mov    0x49f6(%rip),%rax        # 407ca8 <_IO_stdin_used+0xca8>
  4032b2:	49 89 86 50 05 00 00 	mov    %rax,0x550(%r14)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
  4032b9:	e8 72 ee ff ff       	call   402130 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
  4032be:	66 49 0f 6e c6       	movq   %r14,%xmm0
    my_thread_data[n] = &thread_data[n]; 
  4032c3:	66 0f 6f 0d 85 49 00 00 	movdqa 0x4985(%rip),%xmm1        # 407c50 <_IO_stdin_used+0xc50>
  4032cb:	49 8d b6 c0 06 00 00 	lea    0x6c0(%r14),%rsi
  4032d2:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
  4032d6:	48 89 70 40          	mov    %rsi,0x40(%rax)
  4032da:	49 8d 96 98 07 00 00 	lea    0x798(%r14),%rdx
  4032e1:	bf 01 00 00 00       	mov    $0x1,%edi
  4032e6:	66 0f d4 c8          	paddq  %xmm0,%xmm1
  4032ea:	48 89 50 48          	mov    %rdx,0x48(%rax)
  4032ee:	ba 06 00 00 00       	mov    $0x6,%edx
  4032f3:	0f 11 08             	movups %xmm1,(%rax)
  4032f6:	66 0f 6f 0d 62 49 00 00 	movdqa 0x4962(%rip),%xmm1        # 407c60 <_IO_stdin_used+0xc60>
  thread_data[timer_threadi].threads = my_thread_data;
  4032fe:	49 89 86 28 05 00 00 	mov    %rax,0x528(%r14)
    my_thread_data[n] = &thread_data[n]; 
  403305:	66 0f d4 c8          	paddq  %xmm0,%xmm1
  403309:	48 89 74 24 28       	mov    %rsi,0x28(%rsp)
  40330e:	48 8d 35 61 41 00 00 	lea    0x4161(%rip),%rsi        # 407476 <_IO_stdin_used+0x476>
  403315:	0f 11 48 10          	movups %xmm1,0x10(%rax)
  403319:	66 0f 6f 0d 4f 49 00 00 	movdqa 0x494f(%rip),%xmm1        # 407c70 <_IO_stdin_used+0xc70>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
  403321:	41 c7 86 40 05 00 00 06 00 00 00 	movl   $0x6,0x540(%r14)
  thread_data[timer_threadi].thread_index = 0;
  40332c:	41 c7 86 14 05 00 00 00 00 00 00 	movl   $0x0,0x514(%r14)
    my_thread_data[n] = &thread_data[n]; 
  403337:	66 0f d4 c8          	paddq  %xmm0,%xmm1
  40333b:	66 0f d4 05 3d 49 00 00 	paddq  0x493d(%rip),%xmm0        # 407c80 <_IO_stdin_used+0xc80>
  403343:	0f 11 48 20          	movups %xmm1,0x20(%rax)
  403347:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
  40334b:	48 8b 05 5e 49 00 00 	mov    0x495e(%rip),%rax        # 407cb0 <_IO_stdin_used+0xcb0>
  403352:	49 89 86 38 05 00 00 	mov    %rax,0x538(%r14)
  403359:	31 c0                	xor    %eax,%eax
  40335b:	e8 90 ee ff ff       	call   4021f0 <__printf_chk@plt>
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
  403360:	48 c7 c2 a0 41 40 00 	mov    $0x4041a0,%rdx
  403367:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
  40336b:	49 8d 8e 10 05 00 00 	lea    0x510(%r14),%rcx
  403372:	48 8d b5 50 01 00 00 	lea    0x150(%rbp),%rsi
  403379:	e8 92 ee ff ff       	call   402210 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
  40337e:	49 89 d8             	mov    %rbx,%r8
  403381:	4d 89 e1             	mov    %r12,%r9
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
  403384:	4d 89 f2             	mov    %r14,%r10
  403387:	41 bb 02 00 00 00    	mov    $0x2,%r11d
  40338d:	44 89 d8             	mov    %r11d,%eax
  403390:	49 89 db             	mov    %rbx,%r11
  403393:	89 c3                	mov    %eax,%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
  403395:	47 8d 74 2d 00       	lea    0x0(%r13,%r13,1),%r14d
        for (int m = 0 ; m < mailboxes_needed ; m++) {
  40339a:	4d 89 cf             	mov    %r9,%r15
  40339d:	4d 89 c4             	mov    %r8,%r12
  4033a0:	4c 89 d5             	mov    %r10,%rbp
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
  4033a3:	c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%rbp)
  4033aa:	44 89 f2             	mov    %r14d,%edx
  4033ad:	44 89 e9             	mov    %r13d,%ecx
  4033b0:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
  4033b2:	c7 45 44 01 00 00 00 	movl   $0x1,0x44(%rbp)
  4033b9:	48 8d 35 40 44 00 00 	lea    0x4440(%rip),%rsi        # 407800 <_IO_stdin_used+0x800>
  4033c0:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
  4033c5:	41 83 c6 01          	add    $0x1,%r14d
  4033c9:	4c 89 54 24 60       	mov    %r10,0x60(%rsp)
  4033ce:	4c 89 44 24 58       	mov    %r8,0x58(%rsp)
  4033d3:	4c 89 4c 24 50       	mov    %r9,0x50(%rsp)
  4033d8:	4c 89 5c 24 48       	mov    %r11,0x48(%rsp)
  4033dd:	e8 0e ee ff ff       	call   4021f0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
  4033e2:	48 89 e9             	mov    %rbp,%rcx
  4033e5:	4c 89 fe             	mov    %r15,%rsi
  4033e8:	4c 89 e7             	mov    %r12,%rdi
  4033eb:	48 c7 c2 f0 5a 40 00 	mov    $0x405af0,%rdx
    for (int d = 0 ; d < threads_per_group ; d++) {
  4033f2:	48 81 c5 d8 00 00 00 	add    $0xd8,%rbp
  4033f9:	49 83 c4 08          	add    $0x8,%r12
  4033fd:	49 83 c7 38          	add    $0x38,%r15
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
  403401:	e8 0a ee ff ff       	call   402210 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
  403406:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
  40340a:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
  40340f:	be 08 00 00 00       	mov    $0x8,%esi
  403414:	e8 37 ec ff ff       	call   402050 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
  403419:	44 39 f3             	cmp    %r14d,%ebx
  40341c:	4c 8b 5c 24 48       	mov    0x48(%rsp),%r11
  403421:	4c 8b 4c 24 50       	mov    0x50(%rsp),%r9
  403426:	4c 8b 44 24 58       	mov    0x58(%rsp),%r8
  40342b:	4c 8b 54 24 60       	mov    0x60(%rsp),%r10
  403430:	0f 85 6d ff ff ff    	jne    4033a3 <main+0x1063>
  for (int k = 0 ; k < group_count ; k++) {
  403436:	41 83 c5 01          	add    $0x1,%r13d
  40343a:	49 83 c0 10          	add    $0x10,%r8
  40343e:	49 83 c1 70          	add    $0x70,%r9
  403442:	83 c3 02             	add    $0x2,%ebx
  403445:	49 81 c2 b0 01 00 00 	add    $0x1b0,%r10
  40344c:	41 83 fd 03          	cmp    $0x3,%r13d
  403450:	0f 85 3f ff ff ff    	jne    403395 <main+0x1055>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
  403456:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
  40345b:	48 8b 2d 56 48 00 00 	mov    0x4856(%rip),%rbp        # 407cb8 <_IO_stdin_used+0xcb8>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  403462:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
  403467:	4c 89 db             	mov    %r11,%rbx
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  40346a:	bf 01 00 00 00       	mov    $0x1,%edi
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  40346f:	41 bc 08 00 00 00    	mov    $0x8,%r12d
    thread_data[x].type = IO;
  403475:	41 c7 86 f4 05 00 00 02 00 00 00 	movl   $0x2,0x5f4(%r14)
    thread_data[x].task_count = 0;
  403480:	49 89 ae 28 06 00 00 	mov    %rbp,0x628(%r14)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  403487:	e8 a4 ec ff ff       	call   402130 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
  40348c:	be 00 08 00 00       	mov    $0x800,%esi
  403491:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  403493:	49 89 86 40 06 00 00 	mov    %rax,0x640(%r14)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
  40349a:	e8 c1 ed ff ff       	call   402260 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  40349f:	be 08 00 00 00       	mov    $0x8,%esi
  4034a4:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
  4034a9:	41 89 86 48 06 00 00 	mov    %eax,0x648(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  4034b0:	e8 7b ec ff ff       	call   402130 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
  4034b5:	66 0f 6f 54 24 30    	movdqa 0x30(%rsp),%xmm2
  4034bb:	ba 07 00 00 00       	mov    $0x7,%edx
    thread_data[x].thread_count = thread_count;
  4034c0:	41 c7 86 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%r14)
    thread_data[x].threads = my_thread_data;
  4034cb:	49 89 86 00 06 00 00 	mov    %rax,0x600(%r14)
  4034d2:	48 8d 35 bb 3f 00 00 	lea    0x3fbb(%rip),%rsi        # 407494 <_IO_stdin_used+0x494>
  4034d9:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].thread_index = x;
  4034de:	41 c7 86 ec 05 00 00 07 00 00 00 	movl   $0x7,0x5ec(%r14)
  4034e9:	4c 8d 73 40          	lea    0x40(%rbx),%r14
      my_thread_data[n] = &thread_data[n]; 
  4034ed:	0f 11 10             	movups %xmm2,(%rax)
  4034f0:	31 c0                	xor    %eax,%eax
  4034f2:	e8 f9 ec ff ff       	call   4021f0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  4034f7:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  4034fc:	48 8b 0c 24          	mov    (%rsp),%rcx
  403500:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
  403504:	48 c7 c2 60 53 40 00 	mov    $0x405360,%rdx
  40350b:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
  403512:	e8 f9 ec ff ff       	call   402210 <pthread_create@plt>
  403517:	ba 08 00 00 00       	mov    $0x8,%edx
  40351c:	48 8d 35 88 3f 00 00 	lea    0x3f88(%rip),%rsi        # 4074ab <_IO_stdin_used+0x4ab>
  403523:	31 c0                	xor    %eax,%eax
  403525:	bf 01 00 00 00       	mov    $0x1,%edi
  40352a:	e8 c1 ec ff ff       	call   4021f0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  40352f:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
  403534:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
  403539:	4c 8d 05 81 3f 00 00 	lea    0x3f81(%rip),%r8        # 4074c1 <_IO_stdin_used+0x4c1>
  403540:	49 81 c5 c0 01 00 00 	add    $0x1c0,%r13
  403547:	4c 89 c6             	mov    %r8,%rsi
  40354a:	44 89 e2             	mov    %r12d,%edx
  40354d:	bf 01 00 00 00       	mov    $0x1,%edi
  403552:	31 c0                	xor    %eax,%eax
  403554:	e8 97 ec ff ff       	call   4021f0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
  403559:	49 89 6f 40          	mov    %rbp,0x40(%r15)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
  40355d:	be 08 00 00 00       	mov    $0x8,%esi
  403562:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = EXTERNAL;
  403567:	41 c7 47 0c 03 00 00 00 	movl   $0x3,0xc(%r15)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
  40356f:	e8 bc eb ff ff       	call   402130 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
  403574:	48 8b bc 24 98 00 00 00 	mov    0x98(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  40357c:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
  403581:	41 c7 87 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r15)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
  40358c:	49 89 47 50          	mov    %rax,0x50(%r15)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
  403590:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  403593:	bf 02 00 00 00       	mov    $0x2,%edi
  403598:	e8 93 eb ff ff       	call   402130 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
  40359d:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  4035a2:	4c 89 f9             	mov    %r15,%rcx
  4035a5:	4c 89 f7             	mov    %r14,%rdi
      my_thread_data[n] = &thread_data[n]; 
  4035a8:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    thread_data[x].threads = my_thread_data;
  4035ad:	49 89 47 18          	mov    %rax,0x18(%r15)
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  4035b1:	49 83 c6 08          	add    $0x8,%r14
  4035b5:	49 81 c7 d8 00 00 00 	add    $0xd8,%r15
      my_thread_data[n] = &thread_data[n]; 
  4035bc:	48 89 50 08          	mov    %rdx,0x8(%rax)
    thread_data[x].thread_count = thread_count;
  4035c0:	48 8b 15 d1 46 00 00 	mov    0x46d1(%rip),%rdx        # 407c98 <_IO_stdin_used+0xc98>
    thread_data[x].thread_index = x;
  4035c7:	45 89 a7 2c ff ff ff 	mov    %r12d,-0xd4(%r15)
    thread_data[x].thread_count = thread_count;
  4035ce:	49 89 97 50 ff ff ff 	mov    %rdx,-0xb0(%r15)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  4035d5:	48 c7 c2 90 40 40 00 	mov    $0x404090,%rdx
      my_thread_data[n] = &thread_data[n]; 
  4035dc:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  4035df:	4c 89 ee             	mov    %r13,%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  4035e2:	49 83 c5 38          	add    $0x38,%r13
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  4035e6:	e8 25 ec ff ff       	call   402210 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  4035eb:	4c 8d 05 cf 3e 00 00 	lea    0x3ecf(%rip),%r8        # 4074c1 <_IO_stdin_used+0x4c1>
  4035f2:	48 83 84 24 98 00 00 00 10 	addq   $0x10,0x98(%rsp)
  4035fb:	41 83 fc 09          	cmp    $0x9,%r12d
  4035ff:	0f 85 a7 08 00 00    	jne    403eac <main+0x1b6c>
  403605:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
  40360a:	4c 8d 2d cd 3e 00 00 	lea    0x3ecd(%rip),%r13        # 4074de <_IO_stdin_used+0x4de>
  403611:	4c 8d 60 04          	lea    0x4(%rax),%r12
  403615:	48 8d a8 74 08 00 00 	lea    0x874(%rax),%rbp
  40361c:	41 8b 4c 24 04       	mov    0x4(%r12),%ecx
  403621:	41 8b 14 24          	mov    (%r12),%edx
  403625:	4c 89 ee             	mov    %r13,%rsi
  403628:	31 c0                	xor    %eax,%eax
  40362a:	bf 01 00 00 00       	mov    $0x1,%edi
  }

  for (int x = 0 ; x < total_threads ; x++) {
  40362f:	49 81 c4 d8 00 00 00 	add    $0xd8,%r12
  403636:	e8 b5 eb ff ff       	call   4021f0 <__printf_chk@plt>
  40363b:	49 39 ec             	cmp    %rbp,%r12
  40363e:	75 dc                	jne    40361c <main+0x12dc>
  403640:	48 8d 3d aa 3e 00 00 	lea    0x3eaa(%rip),%rdi        # 4074f1 <_IO_stdin_used+0x4f1>
  403647:	45 31 e4             	xor    %r12d,%r12d
  40364a:	4c 8d ac 24 e0 00 00 00 	lea    0xe0(%rsp),%r13
  403652:	e8 09 ea ff ff       	call   402060 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
  403657:	48 8d 2d b1 3e 00 00 	lea    0x3eb1(%rip),%rbp        # 40750f <_IO_stdin_used+0x50f>
    void * result; 
    pthread_join(thread[x], &result);
  40365e:	4a 8b 3c e3          	mov    (%rbx,%r12,8),%rdi
  403662:	4c 89 ee             	mov    %r13,%rsi
  403665:	e8 36 ec ff ff       	call   4022a0 <pthread_join@plt>
  40366a:	44 89 e2             	mov    %r12d,%edx
  40366d:	48 89 ee             	mov    %rbp,%rsi
  403670:	bf 01 00 00 00       	mov    $0x1,%edi
  403675:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
  403677:	49 83 c4 01          	add    $0x1,%r12
  40367b:	e8 70 eb ff ff       	call   4021f0 <__printf_chk@plt>
  403680:	49 83 fc 0a          	cmp    $0xa,%r12
  403684:	75 d8                	jne    40365e <main+0x131e>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
  403686:	be 08 00 00 00       	mov    $0x8,%esi
  40368b:	bf 00 04 00 00       	mov    $0x400,%edi
  403690:	45 31 ed             	xor    %r13d,%r13d
  int datas2_size = 0; 
  403693:	31 ed                	xor    %ebp,%ebp
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
  403695:	e8 96 ea ff ff       	call   402130 <calloc@plt>
  40369a:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  40369f:	49 89 c7             	mov    %rax,%r15
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
  4036a2:	4d 89 d9             	mov    %r11,%r9
  4036a5:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  4036a7:	45 8b 51 40          	mov    0x40(%r9),%r10d
  4036ab:	45 85 d2             	test   %r10d,%r10d
  4036ae:	0f 8e e7 00 00 00    	jle    40379b <main+0x145b>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  4036b4:	49 8b 51 38          	mov    0x38(%r9),%rdx
  4036b8:	41 8d 42 ff          	lea    -0x1(%r10),%eax
  4036bc:	48 c1 e0 09          	shl    $0x9,%rax
  4036c0:	48 8d b2 70 01 00 00 	lea    0x170(%rdx),%rsi
  4036c7:	4c 8d 84 02 70 03 00 00 	lea    0x370(%rdx,%rax,1),%r8
  4036cf:	89 ea                	mov    %ebp,%edx
  4036d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  4036d8:	48 8b 06             	mov    (%rsi),%rax
  4036db:	48 63 fa             	movslq %edx,%rdi
  4036de:	89 d1                	mov    %edx,%ecx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  4036e0:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  4036e7:	49 8d 3c ff          	lea    (%r15,%rdi,8),%rdi
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  4036eb:	83 c1 0b             	add    $0xb,%ecx
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  4036ee:	f3 0f 6f 40 30       	movdqu 0x30(%rax),%xmm0
  4036f3:	f3 0f 6f 78 40       	movdqu 0x40(%rax),%xmm7
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  4036f8:	48 63 c9             	movslq %ecx,%rcx
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  4036fb:	f3 0f 6f 08          	movdqu (%rax),%xmm1
  4036ff:	4c 8b 60 70          	mov    0x70(%rax),%r12
  403703:	66 0f c6 c7 01       	shufpd $0x1,%xmm7,%xmm0
  403708:	0f 11 47 10          	movups %xmm0,0x10(%rdi)
  40370c:	0f 11 0f             	movups %xmm1,(%rdi)
  40370f:	8d 7a 04             	lea    0x4(%rdx),%edi
  403712:	48 63 ff             	movslq %edi,%rdi
  403715:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  403719:	4c 8b 60 78          	mov    0x78(%rax),%r12
  40371d:	8d 7a 05             	lea    0x5(%rdx),%edi
  403720:	48 63 ff             	movslq %edi,%rdi
  403723:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  403727:	4c 8b a0 a8 00 00 00 	mov    0xa8(%rax),%r12
  40372e:	8d 7a 06             	lea    0x6(%rdx),%edi
  403731:	48 63 ff             	movslq %edi,%rdi
  403734:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  403738:	4c 8b a0 b0 00 00 00 	mov    0xb0(%rax),%r12
  40373f:	8d 7a 07             	lea    0x7(%rdx),%edi
  403742:	48 63 ff             	movslq %edi,%rdi
  403745:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  403749:	4c 8b a0 e0 00 00 00 	mov    0xe0(%rax),%r12
  403750:	8d 7a 08             	lea    0x8(%rdx),%edi
  403753:	48 63 ff             	movslq %edi,%rdi
  403756:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  40375a:	4c 8b a0 e8 00 00 00 	mov    0xe8(%rax),%r12
  403761:	8d 7a 09             	lea    0x9(%rdx),%edi
  403764:	48 63 ff             	movslq %edi,%rdi
  403767:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  40376b:	4c 8b a0 18 01 00 00 	mov    0x118(%rax),%r12
  403772:	8d 7a 0a             	lea    0xa(%rdx),%edi
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  403775:	83 c2 0c             	add    $0xc,%edx
  403778:	48 8b 80 20 01 00 00 	mov    0x120(%rax),%rax
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  40377f:	48 63 ff             	movslq %edi,%rdi
  403782:	4d 89 24 ff          	mov    %r12,(%r15,%rdi,8)
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  403786:	49 89 04 cf          	mov    %rax,(%r15,%rcx,8)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  40378a:	4c 39 c6             	cmp    %r8,%rsi
  40378d:	0f 85 45 ff ff ff    	jne    4036d8 <main+0x1398>
  403793:	43 8d 04 52          	lea    (%r10,%r10,2),%eax
  403797:	8d 6c 85 00          	lea    0x0(%rbp,%rax,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
  40379b:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
  4037a2:	83 fb 01             	cmp    $0x1,%ebx
  4037a5:	0f 85 8a 06 00 00    	jne    403e35 <main+0x1af5>
  for (int k = 0 ; k < group_count ; k++) {
  4037ab:	41 83 c5 02          	add    $0x2,%r13d
  4037af:	49 81 c3 b0 01 00 00 	add    $0x1b0,%r11
  4037b6:	41 83 fd 06          	cmp    $0x6,%r13d
  4037ba:	0f 85 e2 fe ff ff    	jne    4036a2 <main+0x1362>
  4037c0:	48 8d 3d 5c 3d 00 00 	lea    0x3d5c(%rip),%rdi        # 407523 <_IO_stdin_used+0x523>
  4037c7:	e8 94 e8 ff ff       	call   402060 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
  4037cc:	48 8d 35 2c 3c 00 00 	lea    0x3c2c(%rip),%rsi        # 4073ff <_IO_stdin_used+0x3ff>
  4037d3:	48 8d 3d 61 3d 00 00 	lea    0x3d61(%rip),%rdi        # 40753b <_IO_stdin_used+0x53b>
  4037da:	e8 51 ea ff ff       	call   402230 <fopen@plt>
  4037df:	49 89 c4             	mov    %rax,%r12
  for (int x = 0 ; x < datas2_size; x++) {
  4037e2:	85 ed                	test   %ebp,%ebp
  4037e4:	7e 70                	jle    403856 <main+0x1516>
  4037e6:	8d 45 ff             	lea    -0x1(%rbp),%eax
  4037e9:	48 8d 1d 32 3c 00 00 	lea    0x3c32(%rip),%rbx        # 407422 <_IO_stdin_used+0x422>
  4037f0:	4d 8d 6c c7 08       	lea    0x8(%r15,%rax,8),%r13
  4037f5:	48 8d 2d e2 3b 00 00 	lea    0x3be2(%rip),%rbp        # 4073de <_IO_stdin_used+0x3de>
    char * c = calloc(250, sizeof(char));
  4037fc:	be 01 00 00 00       	mov    $0x1,%esi
  403801:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
  403806:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
  40380a:	e8 21 e9 ff ff       	call   402130 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  40380f:	48 89 e9             	mov    %rbp,%rcx
  403812:	ba fa 00 00 00       	mov    $0xfa,%edx
  403817:	be 01 00 00 00       	mov    $0x1,%esi
  40381c:	49 89 c6             	mov    %rax,%r14
    sprintf(c, "mailbox %d\n", datas[x]->id);
  40381f:	49 8b 47 f8          	mov    -0x8(%r15),%rax
  403823:	4c 89 f7             	mov    %r14,%rdi
  403826:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
  40382d:	31 c0                	xor    %eax,%eax
  40382f:	e8 bc ea ff ff       	call   4022f0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  403834:	4c 89 f2             	mov    %r14,%rdx
  403837:	48 89 de             	mov    %rbx,%rsi
  40383a:	bf 01 00 00 00       	mov    $0x1,%edi
  40383f:	31 c0                	xor    %eax,%eax
  403841:	e8 aa e9 ff ff       	call   4021f0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  403846:	4c 89 e6             	mov    %r12,%rsi
  403849:	4c 89 f7             	mov    %r14,%rdi
  40384c:	e8 9f e8 ff ff       	call   4020f0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
  403851:	4d 39 ef             	cmp    %r13,%r15
  403854:	75 a6                	jne    4037fc <main+0x14bc>
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
  403856:	4c 89 e7             	mov    %r12,%rdi
  403859:	31 db                	xor    %ebx,%ebx
  40385b:	e8 30 e8 ff ff       	call   402090 <fclose@plt>
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  403860:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
  long received = 0;
  403868:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  long sends = 0;
  403871:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  long ingests = 0;
  40387a:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
  long total = 0;
  403883:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  int datas2_size = 0; 
  40388c:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
  403894:	48 8b ac 24 a0 00 00 00 	mov    0xa0(%rsp),%rbp
  40389c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  4038a1:	8d 43 02             	lea    0x2(%rbx),%eax
  4038a4:	89 44 24 58          	mov    %eax,0x58(%rsp)
      int x = (k * threads_per_group) + d;
      long v = 0;
      
      int other = -1;
      int me = x;
      if (x % 2 == 1) {
  4038a8:	8d 43 01             	lea    0x1(%rbx),%eax
  4038ab:	89 44 24 50          	mov    %eax,0x50(%rsp)
  4038af:	41 89 c4             	mov    %eax,%r12d
  4038b2:	f6 c3 01             	test   $0x1,%bl
  4038b5:	74 04                	je     4038bb <main+0x157b>
        other = abs(x - 1) % total_threads;
  4038b7:	44 8d 63 ff          	lea    -0x1(%rbx),%r12d
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4038bb:	bf 0a 00 00 00       	mov    $0xa,%edi
  4038c0:	e8 7b e7 ff ff       	call   402040 <putchar@plt>
  4038c5:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
  4038ca:	bf 01 00 00 00       	mov    $0x1,%edi
  4038cf:	48 8d 35 6e 3c 00 00 	lea    0x3c6e(%rip),%rsi        # 407544 <_IO_stdin_used+0x544>
  4038d6:	48 8b 10             	mov    (%rax),%rdx
  4038d9:	31 c0                	xor    %eax,%eax
  4038db:	e8 10 e9 ff ff       	call   4021f0 <__printf_chk@plt>
        other = (x + 1) % total_threads;
      }
      printf("\n");
      printf("Total Protected %ld\n", protected_state[me].protected);

      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
  4038e0:	8b 55 40             	mov    0x40(%rbp),%edx
  4038e3:	85 d2                	test   %edx,%edx
  4038e5:	0f 8e cc 05 00 00    	jle    403eb7 <main+0x1b77>
        v += thread_data[me].tasks[n].v;
  4038eb:	48 8b 4d 38          	mov    0x38(%rbp),%rcx
  4038ef:	83 ea 01             	sub    $0x1,%edx
  4038f2:	48 c1 e2 09          	shl    $0x9,%rdx
  4038f6:	48 8d 81 10 01 00 00 	lea    0x110(%rcx),%rax
  4038fd:	48 8d 8c 11 10 03 00 00 	lea    0x310(%rcx,%rdx,1),%rcx
      long v = 0;
  403905:	31 d2                	xor    %edx,%edx
  403907:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
  403910:	48 03 10             	add    (%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
  403913:	48 05 00 02 00 00    	add    $0x200,%rax
  403919:	48 39 c8             	cmp    %rcx,%rax
  40391c:	75 f2                	jne    403910 <main+0x15d0>
      }
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
  40391e:	4d 63 e4             	movslq %r12d,%r12
  403921:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
  403926:	4b 8d 04 64          	lea    (%r12,%r12,2),%rax
  40392a:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
  40392e:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
  403932:	8b 48 40             	mov    0x40(%rax),%ecx
  403935:	85 c9                	test   %ecx,%ecx
  403937:	7e 2d                	jle    403966 <main+0x1626>
        v += thread_data[other].tasks[n].v;
  403939:	48 8b 70 38          	mov    0x38(%rax),%rsi
  40393d:	83 e9 01             	sub    $0x1,%ecx
  403940:	48 c1 e1 09          	shl    $0x9,%rcx
  403944:	48 8d 86 10 01 00 00 	lea    0x110(%rsi),%rax
  40394b:	48 8d 8c 0e 10 03 00 00 	lea    0x310(%rsi,%rcx,1),%rcx
  403953:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  403958:	48 03 10             	add    (%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
  40395b:	48 05 00 02 00 00    	add    $0x200,%rax
  403961:	48 39 c8             	cmp    %rcx,%rax
  403964:	75 f2                	jne    403958 <main+0x1618>
  403966:	48 8d 35 ec 3b 00 00 	lea    0x3bec(%rip),%rsi        # 407559 <_IO_stdin_used+0x559>
  40396d:	bf 01 00 00 00       	mov    $0x1,%edi
  403972:	31 c0                	xor    %eax,%eax
  403974:	e8 77 e8 ff ff       	call   4021f0 <__printf_chk@plt>
      }
      printf("Total V %ld\n", v);
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
  403979:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
  40397e:	bf 01 00 00 00       	mov    $0x1,%edi
  403983:	48 8d 35 a6 3e 00 00 	lea    0x3ea6(%rip),%rsi        # 407830 <_IO_stdin_used+0x830>
  40398a:	48 8b 08             	mov    (%rax),%rcx
  40398d:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
  403997:	48 f7 e9             	imul   %rcx
  40399a:	48 c1 f9 3f          	sar    $0x3f,%rcx
  40399e:	31 c0                	xor    %eax,%eax
  4039a0:	48 d1 fa             	sar    %rdx
  4039a3:	48 29 ca             	sub    %rcx,%rdx
  4039a6:	e8 45 e8 ff ff       	call   4021f0 <__printf_chk@plt>
  4039ab:	bf 0a 00 00 00       	mov    $0xa,%edi
  4039b0:	e8 8b e6 ff ff       	call   402040 <putchar@plt>
      printf("\n");
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  4039b5:	44 8b 65 40          	mov    0x40(%rbp),%r12d
  4039b9:	45 85 e4             	test   %r12d,%r12d
  4039bc:	0f 8e dc 00 00 00    	jle    403a9e <main+0x175e>
  4039c2:	48 89 6c 24 10       	mov    %rbp,0x10(%rsp)
        total += thread_data[x].tasks[n].n;
  4039c7:	48 8b 55 38          	mov    0x38(%rbp),%rdx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  4039cb:	45 31 ff             	xor    %r15d,%r15d
  4039ce:	4c 8d 25 91 3b 00 00 	lea    0x3b91(%rip),%r12        # 407566 <_IO_stdin_used+0x566>
  4039d5:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
  4039da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        total += thread_data[x].tasks[n].n;
  4039e0:	4d 63 d7             	movslq %r15d,%r10
        ingests += thread_data[x].tasks[n].ingest_count;
        sends += thread_data[x].tasks[n].sends;
  4039e3:	31 ed                	xor    %ebp,%ebp
        total += thread_data[x].tasks[n].n;
  4039e5:	49 c1 e2 09          	shl    $0x9,%r10
  4039e9:	4c 01 d2             	add    %r10,%rdx
  4039ec:	4d 89 d5             	mov    %r10,%r13
  4039ef:	48 8b ba 08 01 00 00 	mov    0x108(%rdx),%rdi
  4039f6:	48 01 7c 24 28       	add    %rdi,0x28(%rsp)
        ingests += thread_data[x].tasks[n].ingest_count;
  4039fb:	48 8b ba 68 01 00 00 	mov    0x168(%rdx),%rdi
  403a02:	48 01 7c 24 18       	add    %rdi,0x18(%rsp)
        sends += thread_data[x].tasks[n].sends;
  403a07:	48 8b ba 78 01 00 00 	mov    0x178(%rdx),%rdi
  403a0e:	48 01 7c 24 20       	add    %rdi,0x20(%rsp)
  403a13:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  403a18:	41 89 e8             	mov    %ebp,%r8d
  403a1b:	44 89 f9             	mov    %r15d,%ecx
  403a1e:	89 da                	mov    %ebx,%edx
  403a20:	4c 89 e6             	mov    %r12,%rsi
  403a23:	bf 01 00 00 00       	mov    $0x1,%edi
  403a28:	31 c0                	xor    %eax,%eax
  403a2a:	e8 c1 e7 ff ff       	call   4021f0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          printf("combo %d %d %d\n", x, n, kk);
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
  403a2f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  403a34:	48 8b 50 38          	mov    0x38(%rax),%rdx
  403a38:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
  403a40:	48 29 e8             	sub    %rbp,%rax
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
  403a43:	48 83 c5 01          	add    $0x1,%rbp
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
  403a47:	4a 8b 8c 2a 70 01 00 00 	mov    0x170(%rdx,%r13,1),%rcx
  403a4f:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
  403a53:	48 8b 08             	mov    (%rax),%rcx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
  403a56:	48 8b 70 08          	mov    0x8(%rax),%rsi
  403a5a:	48 8b 86 08 03 00 00 	mov    0x308(%rsi),%rax
  403a61:	48 03 81 08 03 00 00 	add    0x308(%rcx),%rax
  403a68:	48 01 04 24          	add    %rax,(%rsp)

          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
  403a6c:	48 8b 86 10 03 00 00 	mov    0x310(%rsi),%rax
  403a73:	48 03 81 10 03 00 00 	add    0x310(%rcx),%rax
  403a7a:	49 01 c6             	add    %rax,%r14
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
  403a7d:	48 83 fd 06          	cmp    $0x6,%rbp
  403a81:	75 95                	jne    403a18 <main+0x16d8>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  403a83:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  403a88:	41 83 c7 01          	add    $0x1,%r15d
  403a8c:	44 39 78 40          	cmp    %r15d,0x40(%rax)
  403a90:	0f 8f 4a ff ff ff    	jg     4039e0 <main+0x16a0>
  403a96:	4c 89 74 24 30       	mov    %r14,0x30(%rsp)
  403a9b:	48 89 c5             	mov    %rax,%rbp
        }
      }
      for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
  403a9e:	48 8b 8d 88 00 00 00 	mov    0x88(%rbp),%rcx
  403aa5:	48 85 c9             	test   %rcx,%rcx
  403aa8:	7e 11                	jle    403abb <main+0x177b>
  403aaa:	31 c0                	xor    %eax,%eax
  403aac:	0f 1f 40 00          	nopl   0x0(%rax)
  403ab0:	83 c0 01             	add    $0x1,%eax
  403ab3:	48 63 d0             	movslq %eax,%rdx
  403ab6:	48 39 ca             	cmp    %rcx,%rdx
  403ab9:	7c f5                	jl     403ab0 <main+0x1770>
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        // printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
        // printf("%ld iterations\n", thread_data[x].iteration_count);
      }
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  403abb:	45 31 e4             	xor    %r12d,%r12d
  403abe:	31 c0                	xor    %eax,%eax
  403ac0:	48 83 bd a0 00 00 00 00 	cmpq   $0x0,0xa0(%rbp)
  403ac8:	48 8d 1d 81 3d 00 00 	lea    0x3d81(%rip),%rbx        # 407850 <_IO_stdin_used+0x850>
  403acf:	7e 69                	jle    403b3a <main+0x17fa>
  403ad1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
  403ad8:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  403adc:	48 8b 85 90 00 00 00 	mov    0x90(%rbp),%rax
  403ae3:	48 83 ec 08          	sub    $0x8,%rsp
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  403ae7:	41 83 c4 01          	add    $0x1,%r12d
  403aeb:	bf 01 00 00 00       	mov    $0x1,%edi
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
  403af0:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
  403af4:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
  403afe:	48 8b 71 18          	mov    0x18(%rcx),%rsi
  403b02:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
  403b06:	48 f7 e6             	mul    %rsi
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
  403b09:	4c 8b 41 10          	mov    0x10(%rcx),%r8
  403b0d:	4c 2b 01             	sub    (%rcx),%r8
  403b10:	31 c0                	xor    %eax,%eax
  403b12:	8b 49 20             	mov    0x20(%rcx),%ecx
  403b15:	56                   	push   %rsi
  403b16:	48 89 de             	mov    %rbx,%rsi
  403b19:	48 c1 ea 12          	shr    $0x12,%rdx
  403b1d:	49 89 d1             	mov    %rdx,%r9
  403b20:	ba 02 00 00 00       	mov    $0x2,%edx
  403b25:	e8 c6 e6 ff ff       	call   4021f0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  403b2a:	41 5a                	pop    %r10
  403b2c:	49 63 c4             	movslq %r12d,%rax
  403b2f:	41 5b                	pop    %r11
  403b31:	48 3b 85 a0 00 00 00 	cmp    0xa0(%rbp),%rax
  403b38:	7c 9e                	jl     403ad8 <main+0x1798>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
  403b3a:	8b 95 bc 00 00 00    	mov    0xbc(%rbp),%edx
  403b40:	85 d2                	test   %edx,%edx
  403b42:	0f 8e f4 00 00 00    	jle    403c3c <main+0x18fc>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
  403b48:	48 8b 75 50          	mov    0x50(%rbp),%rsi
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
  403b4c:	45 31 e4             	xor    %r12d,%r12d
  403b4f:	4c 8d 35 4a 3d 00 00 	lea    0x3d4a(%rip),%r14        # 4078a0 <_IO_stdin_used+0x8a0>
  403b56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
  403b60:	49 63 c4             	movslq %r12d,%rax
  403b63:	4c 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%r13
  403b6b:	48 8b 04 c6          	mov    (%rsi,%rax,8),%rax
  403b6f:	8b 08                	mov    (%rax),%ecx
  403b71:	85 c9                	test   %ecx,%ecx
  403b73:	0f 8e b6 00 00 00    	jle    403c2f <main+0x18ef>
  403b79:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
  403b81:	48 8b 50 08          	mov    0x8(%rax),%rdx
  403b85:	0f 1f 00             	nopl   (%rax)
  403b88:	48 63 5c 24 10       	movslq 0x10(%rsp),%rbx
  403b8d:	45 31 ff             	xor    %r15d,%r15d
  403b90:	48 c1 e3 08          	shl    $0x8,%rbx
  403b94:	48 8d 04 1a          	lea    (%rdx,%rbx,1),%rax
  403b98:	8b b8 94 00 00 00    	mov    0x94(%rax),%edi
  403b9e:	85 ff                	test   %edi,%edi
  403ba0:	7e 76                	jle    403c18 <main+0x18d8>
  403ba2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
  403ba8:	49 63 cf             	movslq %r15d,%rcx
  403bab:	48 83 ec 08          	sub    $0x8,%rsp
  403baf:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
  403bb4:	41 83 c7 01          	add    $0x1,%r15d
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
  403bb8:	48 c1 e1 05          	shl    $0x5,%rcx
  403bbc:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
  403bc3:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
  403bcd:	48 8b 71 18          	mov    0x18(%rcx),%rsi
  403bd1:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
  403bd5:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
  403bd8:	4c 8b 41 10          	mov    0x10(%rcx),%r8
  403bdc:	4c 2b 01             	sub    (%rcx),%r8
  403bdf:	56                   	push   %rsi
  403be0:	44 89 e1             	mov    %r12d,%ecx
  403be3:	4c 89 f6             	mov    %r14,%rsi
  403be6:	31 c0                	xor    %eax,%eax
  403be8:	48 c1 ea 12          	shr    $0x12,%rdx
  403bec:	49 89 d1             	mov    %rdx,%r9
  403bef:	ba 02 00 00 00       	mov    $0x2,%edx
  403bf4:	e8 f7 e5 ff ff       	call   4021f0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
  403bf9:	48 8b 75 50          	mov    0x50(%rbp),%rsi
  403bfd:	41 58                	pop    %r8
  403bff:	41 59                	pop    %r9
  403c01:	4a 8b 0c 2e          	mov    (%rsi,%r13,1),%rcx
  403c05:	48 8b 51 08          	mov    0x8(%rcx),%rdx
  403c09:	48 8d 04 1a          	lea    (%rdx,%rbx,1),%rax
  403c0d:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
  403c14:	7f 92                	jg     403ba8 <main+0x1868>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
  403c16:	8b 09                	mov    (%rcx),%ecx
  403c18:	83 44 24 10 01       	addl   $0x1,0x10(%rsp)
  403c1d:	8b 44 24 10          	mov    0x10(%rsp),%eax
  403c21:	39 c8                	cmp    %ecx,%eax
  403c23:	0f 8c 5f ff ff ff    	jl     403b88 <main+0x1848>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
  403c29:	8b 95 bc 00 00 00    	mov    0xbc(%rbp),%edx
  403c2f:	41 83 c4 01          	add    $0x1,%r12d
  403c33:	41 39 d4             	cmp    %edx,%r12d
  403c36:	0f 8c 24 ff ff ff    	jl     403b60 <main+0x1820>
    for (int d = 0 ; d < threads_per_group ; d++) {
  403c3c:	8b 44 24 50          	mov    0x50(%rsp),%eax
  403c40:	8b 7c 24 58          	mov    0x58(%rsp),%edi
  403c44:	48 81 c5 d8 00 00 00 	add    $0xd8,%rbp
  403c4b:	48 83 44 24 48 18    	addq   $0x18,0x48(%rsp)
  403c51:	89 c3                	mov    %eax,%ebx
  403c53:	39 f8                	cmp    %edi,%eax
  403c55:	0f 85 4d fc ff ff    	jne    4038a8 <main+0x1568>
  for (int k = 0 ; k < group_count ; k++) {
  403c5b:	48 81 84 24 a0 00 00 00 b0 01 00 00 	addq   $0x1b0,0xa0(%rsp)
  403c67:	48 83 84 24 a8 00 00 00 30 	addq   $0x30,0xa8(%rsp)
  403c70:	83 f8 06             	cmp    $0x6,%eax
  403c73:	0f 85 13 fc ff ff    	jne    40388c <main+0x154c>
  403c79:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
  403c7e:	48 8d 35 f1 38 00 00 	lea    0x38f1(%rip),%rsi        # 407576 <_IO_stdin_used+0x576>
  403c85:	bf 01 00 00 00       	mov    $0x1,%edi
  403c8a:	31 c0                	xor    %eax,%eax
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
  403c8c:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
  403c96:	4c 89 f2             	mov    %r14,%rdx
  403c99:	e8 52 e5 ff ff       	call   4021f0 <__printf_chk@plt>
  403c9e:	bf 0a 00 00 00       	mov    $0xa,%edi
  403ca3:	e8 98 e3 ff ff       	call   402040 <putchar@plt>
  403ca8:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
  403cb0:	bf 01 00 00 00       	mov    $0x1,%edi
  403cb5:	48 8d 35 3c 3c 00 00 	lea    0x3c3c(%rip),%rsi        # 4078f8 <_IO_stdin_used+0x8f8>
  403cbc:	48 8b 50 08          	mov    0x8(%rax),%rdx
  403cc0:	31 c0                	xor    %eax,%eax
  403cc2:	e8 29 e5 ff ff       	call   4021f0 <__printf_chk@plt>
  403cc7:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  403ccc:	bf 01 00 00 00       	mov    $0x1,%edi
  403cd1:	48 8d 35 48 3c 00 00 	lea    0x3c48(%rip),%rsi        # 407920 <_IO_stdin_used+0x920>
  403cd8:	48 f7 eb             	imul   %rbx
  403cdb:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  403ce0:	48 c1 f8 3f          	sar    $0x3f,%rax
  403ce4:	48 d1 fa             	sar    %rdx
  403ce7:	48 29 c2             	sub    %rax,%rdx
  403cea:	31 c0                	xor    %eax,%eax
  403cec:	e8 ff e4 ff ff       	call   4021f0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
  403cf1:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
  403cf6:	bf 01 00 00 00       	mov    $0x1,%edi
  403cfb:	48 8d 35 4e 3c 00 00 	lea    0x3c4e(%rip),%rsi        # 407950 <_IO_stdin_used+0x950>
  403d02:	48 f7 eb             	imul   %rbx
  403d05:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
  403d0a:	48 c1 f8 3f          	sar    $0x3f,%rax
  403d0e:	48 d1 fa             	sar    %rdx
  403d11:	48 29 c2             	sub    %rax,%rdx
  403d14:	31 c0                	xor    %eax,%eax
  403d16:	e8 d5 e4 ff ff       	call   4021f0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
  403d1b:	4c 89 f0             	mov    %r14,%rax
  403d1e:	bf 01 00 00 00       	mov    $0x1,%edi
  403d23:	48 8d 35 56 3c 00 00 	lea    0x3c56(%rip),%rsi        # 407980 <_IO_stdin_used+0x980>
  403d2a:	48 f7 eb             	imul   %rbx
  403d2d:	4c 89 f0             	mov    %r14,%rax
  403d30:	48 c1 f8 3f          	sar    $0x3f,%rax
  403d34:	48 d1 fa             	sar    %rdx
  403d37:	48 29 c2             	sub    %rax,%rdx
  403d3a:	31 c0                	xor    %eax,%eax
  403d3c:	e8 af e4 ff ff       	call   4021f0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
  403d41:	48 8b 04 24          	mov    (%rsp),%rax
  403d45:	bf 01 00 00 00       	mov    $0x1,%edi
  403d4a:	48 8d 35 39 38 00 00 	lea    0x3839(%rip),%rsi        # 40758a <_IO_stdin_used+0x58a>
  403d51:	48 f7 eb             	imul   %rbx
  403d54:	48 8b 04 24          	mov    (%rsp),%rax
  403d58:	48 c1 f8 3f          	sar    $0x3f,%rax
  403d5c:	48 d1 fa             	sar    %rdx
  403d5f:	48 29 c2             	sub    %rax,%rdx
  403d62:	31 c0                	xor    %eax,%eax
  403d64:	48 89 d5             	mov    %rdx,%rbp
  403d67:	e8 84 e4 ff ff       	call   4021f0 <__printf_chk@plt>
  printf("Total sents %ld\n", sentdur);
  long recdur = received / DURATION;
  403d6c:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
  403d71:	bf 01 00 00 00       	mov    $0x1,%edi
  403d76:	48 8d 35 1e 38 00 00 	lea    0x381e(%rip),%rsi        # 40759b <_IO_stdin_used+0x59b>
  403d7d:	48 f7 eb             	imul   %rbx
  403d80:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
  403d85:	48 c1 f8 3f          	sar    $0x3f,%rax
  403d89:	48 89 d3             	mov    %rdx,%rbx
  403d8c:	48 d1 fb             	sar    %rbx
  403d8f:	48 29 c3             	sub    %rax,%rbx
  403d92:	31 c0                	xor    %eax,%eax
  403d94:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
  403d97:	48 29 eb             	sub    %rbp,%rbx
  403d9a:	e8 51 e4 ff ff       	call   4021f0 <__printf_chk@plt>
  403d9f:	31 c0                	xor    %eax,%eax
  403da1:	48 89 da             	mov    %rbx,%rdx
  403da4:	bf 01 00 00 00       	mov    $0x1,%edi
  403da9:	48 8d 35 ff 37 00 00 	lea    0x37ff(%rip),%rsi        # 4075af <_IO_stdin_used+0x5af>
  403db0:	e8 3b e4 ff ff       	call   4021f0 <__printf_chk@plt>
  return 0;

}
  403db5:	48 8b 84 24 e8 00 00 00 	mov    0xe8(%rsp),%rax
  403dbd:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  403dc6:	0f 85 07 01 00 00    	jne    403ed3 <main+0x1b93>
  403dcc:	48 81 c4 f8 00 00 00 	add    $0xf8,%rsp
  403dd3:	31 c0                	xor    %eax,%eax
  403dd5:	5b                   	pop    %rbx
  403dd6:	5d                   	pop    %rbp
  403dd7:	41 5c                	pop    %r12
  403dd9:	41 5d                	pop    %r13
  403ddb:	41 5e                	pop    %r14
  403ddd:	41 5f                	pop    %r15
  403ddf:	c3                   	ret
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  403de0:	b8 6e 64 00 00       	mov    $0x646e,%eax
  403de5:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
  403deb:	66 89 41 04          	mov    %ax,0x4(%rcx)
  403def:	c6 41 06 00          	movb   $0x0,0x6(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
  403df3:	48 8b 84 2e 70 01 00 00 	mov    0x170(%rsi,%rbp,1),%rax
  403dfb:	48 01 d8             	add    %rbx,%rax
  403dfe:	e9 e6 f2 ff ff       	jmp    4030e9 <main+0xda9>
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
  403e03:	48 c7 c0 20 6a 40 00 	mov    $0x406a20,%rax
  403e0a:	41 bc 01 00 00 00    	mov    $0x1,%r12d
  403e10:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
  403e17:	e9 b4 ea ff ff       	jmp    4028d0 <main+0x590>
            thread_data[x].tasks[y].run = barriered_work; 
  403e1c:	48 c7 c0 90 61 40 00 	mov    $0x406190,%rax
  403e23:	41 bc 02 00 00 00    	mov    $0x2,%r12d
  403e29:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
  403e30:	e9 9b ea ff ff       	jmp    4028d0 <main+0x590>
  403e35:	bb 01 00 00 00       	mov    $0x1,%ebx
  403e3a:	e9 68 f8 ff ff       	jmp    4036a7 <main+0x1367>
  403e3f:	c7 04 24 01 00 00 00 	movl   $0x1,(%rsp)
  403e46:	e9 4d f2 ff ff       	jmp    403098 <main+0xd58>
  403e4b:	bb 01 00 00 00       	mov    $0x1,%ebx
  403e50:	e9 37 f0 ff ff       	jmp    402e8c <main+0xb4c>
  403e55:	8b 44 24 74          	mov    0x74(%rsp),%eax
  403e59:	89 44 24 20          	mov    %eax,0x20(%rsp)
  403e5d:	8b 44 24 50          	mov    0x50(%rsp),%eax
  403e61:	89 84 24 b0 00 00 00 	mov    %eax,0xb0(%rsp)
  403e68:	e9 51 e8 ff ff       	jmp    4026be <main+0x37e>
            CPU_SET(j, sendercpu);
  403e6d:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
          for (int j = 0 ; j < cores ; j++) {
  403e75:	e9 5e e9 ff ff       	jmp    4027d8 <main+0x498>
        my_thread_data[0] = &thread_data[other]; 
  403e7a:	48 63 c3             	movslq %ebx,%rax
  403e7d:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
        thread_data[x].thread_index = 1;
  403e82:	48 8b 54 24 28       	mov    0x28(%rsp),%rdx
        other = abs(x - 1) % total_threads;
  403e87:	41 89 de             	mov    %ebx,%r14d
        my_thread_data[0] = &thread_data[other]; 
  403e8a:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
  403e8e:	4c 63 64 24 74       	movslq 0x74(%rsp),%r12
  403e93:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
  403e97:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
  403e9b:	49 8d 7d 08          	lea    0x8(%r13),%rdi
  403e9f:	48 89 7c 24 58       	mov    %rdi,0x58(%rsp)
  403ea4:	48 89 d7             	mov    %rdx,%rdi
  403ea7:	e9 9e e8 ff ff       	jmp    40274a <main+0x40a>
  403eac:	41 bc 09 00 00 00    	mov    $0x9,%r12d
  403eb2:	e9 90 f6 ff ff       	jmp    403547 <main+0x1207>
      long v = 0;
  403eb7:	31 d2                	xor    %edx,%edx
  403eb9:	e9 60 fa ff ff       	jmp    40391e <main+0x15de>
  403ebe:	41 bc 02 00 00 00    	mov    $0x2,%r12d
  403ec4:	e9 07 ea ff ff       	jmp    4028d0 <main+0x590>
            exit(1);
  403ec9:	bf 01 00 00 00       	mov    $0x1,%edi
  403ece:	e8 7d e3 ff ff       	call   402250 <exit@plt>
}
  403ed3:	e8 d8 e1 ff ff       	call   4020b0 <__stack_chk_fail@plt>
  403ed8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000403ee0 <_start>:
  403ee0:	f3 0f 1e fa          	endbr64
  403ee4:	31 ed                	xor    %ebp,%ebp
  403ee6:	49 89 d1             	mov    %rdx,%r9
  403ee9:	5e                   	pop    %rsi
  403eea:	48 89 e2             	mov    %rsp,%rdx
  403eed:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  403ef1:	50                   	push   %rax
  403ef2:	54                   	push   %rsp
  403ef3:	45 31 c0             	xor    %r8d,%r8d
  403ef6:	31 c9                	xor    %ecx,%ecx
  403ef8:	48 c7 c7 40 23 40 00 	mov    $0x402340,%rdi
  403eff:	ff 15 d3 60 00 00    	call   *0x60d3(%rip)        # 409fd8 <__libc_start_main@GLIBC_2.34>
  403f05:	f4                   	hlt
  403f06:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000403f10 <_dl_relocate_static_pie>:
  403f10:	f3 0f 1e fa          	endbr64
  403f14:	c3                   	ret
  403f15:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  403f1f:	90                   	nop

0000000000403f20 <deregister_tm_clones>:
  403f20:	b8 20 a0 40 00       	mov    $0x40a020,%eax
  403f25:	48 3d 20 a0 40 00    	cmp    $0x40a020,%rax
  403f2b:	74 13                	je     403f40 <deregister_tm_clones+0x20>
  403f2d:	b8 00 00 00 00       	mov    $0x0,%eax
  403f32:	48 85 c0             	test   %rax,%rax
  403f35:	74 09                	je     403f40 <deregister_tm_clones+0x20>
  403f37:	bf 20 a0 40 00       	mov    $0x40a020,%edi
  403f3c:	ff e0                	jmp    *%rax
  403f3e:	66 90                	xchg   %ax,%ax
  403f40:	c3                   	ret
  403f41:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  403f4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000403f50 <register_tm_clones>:
  403f50:	be 20 a0 40 00       	mov    $0x40a020,%esi
  403f55:	48 81 ee 20 a0 40 00 	sub    $0x40a020,%rsi
  403f5c:	48 89 f0             	mov    %rsi,%rax
  403f5f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  403f63:	48 c1 f8 03          	sar    $0x3,%rax
  403f67:	48 01 c6             	add    %rax,%rsi
  403f6a:	48 d1 fe             	sar    %rsi
  403f6d:	74 11                	je     403f80 <register_tm_clones+0x30>
  403f6f:	b8 00 00 00 00       	mov    $0x0,%eax
  403f74:	48 85 c0             	test   %rax,%rax
  403f77:	74 07                	je     403f80 <register_tm_clones+0x30>
  403f79:	bf 20 a0 40 00       	mov    $0x40a020,%edi
  403f7e:	ff e0                	jmp    *%rax
  403f80:	c3                   	ret
  403f81:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  403f8c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000403f90 <__do_global_dtors_aux>:
  403f90:	f3 0f 1e fa          	endbr64
  403f94:	80 3d 85 60 00 00 00 	cmpb   $0x0,0x6085(%rip)        # 40a020 <__TMC_END__>
  403f9b:	75 13                	jne    403fb0 <__do_global_dtors_aux+0x20>
  403f9d:	55                   	push   %rbp
  403f9e:	48 89 e5             	mov    %rsp,%rbp
  403fa1:	e8 7a ff ff ff       	call   403f20 <deregister_tm_clones>
  403fa6:	c6 05 73 60 00 00 01 	movb   $0x1,0x6073(%rip)        # 40a020 <__TMC_END__>
  403fad:	5d                   	pop    %rbp
  403fae:	c3                   	ret
  403faf:	90                   	nop
  403fb0:	c3                   	ret
  403fb1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  403fbc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000403fc0 <frame_dummy>:
  403fc0:	f3 0f 1e fa          	endbr64
  403fc4:	eb 8a                	jmp    403f50 <register_tm_clones>
  403fc6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000403fd0 <do_protected_write>:
  struct ProtectedState *protected = data->thread->protected_state;
  403fd0:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  403fd7:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
  403fdb:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
  403fe3:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
  403fe7:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
  403feb:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
  403ff2:	48 85 c9             	test   %rcx,%rcx
  403ff5:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
  403ffc:	48 0f 4f d6          	cmovg  %rsi,%rdx
  404000:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
  404004:	31 c0                	xor    %eax,%eax
  404006:	c3                   	ret
  404007:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000404010 <barriered_reset>:
    for (int x = 0 ; x < data->task_count ; x++) {
  404010:	8b 8f 48 01 00 00    	mov    0x148(%rdi),%ecx
  404016:	85 c9                	test   %ecx,%ecx
  404018:	7e 61                	jle    40407b <barriered_reset+0x6b>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
  40401a:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  404021:	48 63 bf 30 01 00 00 	movslq 0x130(%rdi),%rdi
  404028:	83 e9 01             	sub    $0x1,%ecx
  40402b:	48 c1 e1 09          	shl    $0x9,%rcx
      data->thread->tasks[x].available = 1; 
  40402f:	48 8b 70 38          	mov    0x38(%rax),%rsi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
  404033:	48 8b 40 18          	mov    0x18(%rax),%rax
  404037:	48 8b 04 f8          	mov    (%rax,%rdi,8),%rax
  40403b:	48 8d 96 44 01 00 00 	lea    0x144(%rsi),%rdx
  404042:	48 8d 8c 0e 44 03 00 00 	lea    0x344(%rsi,%rcx,1),%rcx
  40404a:	48 8b 40 38          	mov    0x38(%rax),%rax
  40404e:	48 05 00 01 00 00    	add    $0x100,%rax
  404054:	0f 1f 40 00          	nopl   0x0(%rax)
  404058:	83 40 80 01          	addl   $0x1,-0x80(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
  40405c:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
  404063:	83 00 01             	addl   $0x1,(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
  404066:	48 05 00 02 00 00    	add    $0x200,%rax
      data->thread->tasks[x].available = 1; 
  40406c:	c7 82 00 fe ff ff 01 00 00 00 	movl   $0x1,-0x200(%rdx)
    for (int x = 0 ; x < data->task_count ; x++) {
  404076:	48 39 ca             	cmp    %rcx,%rdx
  404079:	75 dd                	jne    404058 <barriered_reset+0x48>
  asm volatile ("sfence" ::: "memory");
  40407b:	0f ae f8             	sfence
}
  40407e:	31 c0                	xor    %eax,%eax
  404080:	c3                   	ret
  404081:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40408c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000404090 <external_thread>:
  while (data->running == 1) {
  404090:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
  404094:	0f 85 f4 00 00 00    	jne    40418e <external_thread+0xfe>
void * external_thread(void *arg) {
  40409a:	41 57                	push   %r15
  40409c:	49 89 ff             	mov    %rdi,%r15
  40409f:	41 56                	push   %r14
  4040a1:	41 55                	push   %r13
  4040a3:	41 54                	push   %r12
  4040a5:	55                   	push   %rbp
  4040a6:	53                   	push   %rbx
  4040a7:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
  4040ab:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
  4040b1:	85 c9                	test   %ecx,%ecx
  4040b3:	7e 66                	jle    40411b <external_thread+0x8b>
  4040b5:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
					data->buffers[b]->buffer[x].data = "Hello world";
  4040b9:	4c 8d 2d 44 2f 00 00 	lea    0x2f44(%rip),%r13        # 407004 <_IO_stdin_used+0x4>
    for (int b = 0; b < data->buffers_count; b++) {
  4040c0:	45 31 e4             	xor    %r12d,%r12d
  4040c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int x = 0; x < data->buffers[b]->count; x++) {
  4040c8:	4d 63 f4             	movslq %r12d,%r14
  4040cb:	31 ed                	xor    %ebp,%ebp
  4040cd:	49 c1 e6 03          	shl    $0x3,%r14
  4040d1:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
  4040d5:	48 8b 06             	mov    (%rsi),%rax
  4040d8:	8b 10                	mov    (%rax),%edx
  4040da:	85 d2                	test   %edx,%edx
  4040dc:	7e 29                	jle    404107 <external_thread+0x77>
  4040de:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
  4040e2:	48 63 dd             	movslq %ebp,%rbx
  4040e5:	48 c1 e3 08          	shl    $0x8,%rbx
  4040e9:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
  4040ed:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
  4040f4:	45 85 c0             	test   %r8d,%r8d
  4040f7:	74 27                	je     404120 <external_thread+0x90>
      for (int x = 0; x < data->buffers[b]->count; x++) {
  4040f9:	83 c5 01             	add    $0x1,%ebp
  4040fc:	39 ea                	cmp    %ebp,%edx
  4040fe:	7f e2                	jg     4040e2 <external_thread+0x52>
    for (int b = 0; b < data->buffers_count; b++) {
  404100:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
  404107:	41 83 c4 01          	add    $0x1,%r12d
  40410b:	41 39 cc             	cmp    %ecx,%r12d
  40410e:	7c b8                	jl     4040c8 <external_thread+0x38>
  while (data->running == 1) {
  404110:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
  404115:	75 66                	jne    40417d <external_thread+0xed>
    for (int b = 0; b < data->buffers_count; b++) {
  404117:	85 c9                	test   %ecx,%ecx
  404119:	7f a5                	jg     4040c0 <external_thread+0x30>
  while (data->running == 1) {
  40411b:	eb fe                	jmp    40411b <external_thread+0x8b>
  40411d:	0f 1f 00             	nopl   (%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
  404120:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
  404123:	48 8b 06             	mov    (%rsi),%rax
  404126:	48 8b 78 08          	mov    0x8(%rax),%rdi
  40412a:	48 01 df             	add    %rbx,%rdi
  40412d:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
  404134:	48 c1 e6 05          	shl    $0x5,%rsi
  404138:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
  40413f:	bf 04 00 00 00       	mov    $0x4,%edi
  404144:	e8 37 df ff ff       	call   402080 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
  404149:	49 8b 47 50          	mov    0x50(%r15),%rax
  40414d:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
  404151:	48 8b 40 08          	mov    0x8(%rax),%rax
  404155:	c7 84 18 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbx,1)
          asm volatile ("sfence" ::: "memory");
  404160:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
  404163:	49 8b 7f 50          	mov    0x50(%r15),%rdi
  404167:	83 c5 01             	add    $0x1,%ebp
  40416a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
  40416e:	48 8b 06             	mov    (%rsi),%rax
  404171:	8b 10                	mov    (%rax),%edx
  404173:	39 d5                	cmp    %edx,%ebp
  404175:	0f 8c 63 ff ff ff    	jl     4040de <external_thread+0x4e>
  40417b:	eb 83                	jmp    404100 <external_thread+0x70>
}
  40417d:	48 83 c4 08          	add    $0x8,%rsp
  404181:	31 c0                	xor    %eax,%eax
  404183:	5b                   	pop    %rbx
  404184:	5d                   	pop    %rbp
  404185:	41 5c                	pop    %r12
  404187:	41 5d                	pop    %r13
  404189:	41 5e                	pop    %r14
  40418b:	41 5f                	pop    %r15
  40418d:	c3                   	ret
  40418e:	31 c0                	xor    %eax,%eax
  404190:	c3                   	ret
  404191:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40419c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004041a0 <timer_thread>:
void* timer_thread(void *arg) {
  4041a0:	41 57                	push   %r15
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4041a2:	48 8d 35 67 2e 00 00 	lea    0x2e67(%rip),%rsi        # 407010 <_IO_stdin_used+0x10>
  4041a9:	41 56                	push   %r14
  4041ab:	41 55                	push   %r13
  4041ad:	41 54                	push   %r12
  4041af:	55                   	push   %rbp
  4041b0:	53                   	push   %rbx
  4041b1:	48 89 fb             	mov    %rdi,%rbx
  4041b4:	48 83 ec 68          	sub    $0x68,%rsp
  4041b8:	8b 57 04             	mov    0x4(%rdi),%edx
  4041bb:	bf 01 00 00 00       	mov    $0x1,%edi
  4041c0:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4041c9:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  4041ce:	31 c0                	xor    %eax,%eax
  4041d0:	e8 1b e0 ff ff       	call   4021f0 <__printf_chk@plt>
  struct timespec preempt = {
  4041d5:	66 0f 6f 05 c3 39 00 00 	movdqa 0x39c3(%rip),%xmm0        # 407ba0 <_IO_stdin_used+0xba0>
  4041dd:	ba 88 13 00 00       	mov    $0x1388,%edx
  4041e2:	31 c0                	xor    %eax,%eax
  4041e4:	48 8d 35 37 2e 00 00 	lea    0x2e37(%rip),%rsi        # 407022 <_IO_stdin_used+0x22>
  4041eb:	bf 01 00 00 00       	mov    $0x1,%edi
  4041f0:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
  4041f5:	e8 f6 df ff ff       	call   4021f0 <__printf_chk@plt>
  while (data->running && n < times) {
  4041fa:	44 8b 7b 44          	mov    0x44(%rbx),%r15d
  4041fe:	45 85 ff             	test   %r15d,%r15d
  404201:	0f 84 a8 00 00 00    	je     4042af <timer_thread+0x10f>
  int n = 0;
  404207:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
  40420a:	45 31 ff             	xor    %r15d,%r15d
  40420d:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
      y = 0;
  404212:	31 ed                	xor    %ebp,%ebp
  404214:	4c 8d 64 24 20       	lea    0x20(%rsp),%r12
    nanosleep(&preempt , &rem2);
  404219:	4c 89 e7             	mov    %r12,%rdi
  40421c:	4c 89 ee             	mov    %r13,%rsi
    n++;
  40421f:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
  404223:	e8 a8 de ff ff       	call   4020d0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404228:	8b 53 30             	mov    0x30(%rbx),%edx
    y++;
  40422b:	41 8d 7f 01          	lea    0x1(%r15),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  40422f:	85 d2                	test   %edx,%edx
  404231:	7e 55                	jle    404288 <timer_thread+0xe8>
  404233:	48 8b 43 18          	mov    0x18(%rbx),%rax
        data->threads[x]->tasks[y].scheduled = 0;
  404237:	4d 63 c7             	movslq %r15d,%r8
  40423a:	83 ea 01             	sub    $0x1,%edx
  40423d:	49 c1 e0 09          	shl    $0x9,%r8
  404241:	48 8d 48 08          	lea    0x8(%rax),%rcx
  404245:	4c 8d 0c d1          	lea    (%rcx,%rdx,8),%r9
  404249:	eb 09                	jmp    404254 <timer_thread+0xb4>
  40424b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  404250:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
  404254:	4c 8b 10             	mov    (%rax),%r10
  404257:	89 f8                	mov    %edi,%eax
  404259:	99                   	cltd
  40425a:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
  40425e:	49 8b 72 38          	mov    0x38(%r10),%rsi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404262:	48 89 c8             	mov    %rcx,%rax
        data->threads[x]->tasks[next].scheduled = 1;
  404265:	48 63 d2             	movslq %edx,%rdx
  404268:	48 c1 e2 09          	shl    $0x9,%rdx
  40426c:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
  404277:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404283:	49 39 c9             	cmp    %rcx,%r9
  404286:	75 c8                	jne    404250 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
  404288:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
  40428b:	48 8b 43 18          	mov    0x18(%rbx),%rax
  while (data->running && n < times) {
  40428f:	8b 4b 44             	mov    0x44(%rbx),%ecx
    if (y >= data->threads[0]->task_count) {
  404292:	48 8b 00             	mov    (%rax),%rax
      y = 0;
  404295:	39 78 40             	cmp    %edi,0x40(%rax)
  404298:	0f 4e fd             	cmovle %ebp,%edi
  40429b:	41 89 ff             	mov    %edi,%r15d
  while (data->running && n < times) {
  40429e:	85 c9                	test   %ecx,%ecx
  4042a0:	74 0d                	je     4042af <timer_thread+0x10f>
  4042a2:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
  4042a9:	0f 85 6a ff ff ff    	jne    404219 <timer_thread+0x79>
  4042af:	48 8d 3d 82 2d 00 00 	lea    0x2d82(%rip),%rdi        # 407038 <_IO_stdin_used+0x38>
  4042b6:	e8 a5 dd ff ff       	call   402060 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
  4042bb:	48 63 43 30          	movslq 0x30(%rbx),%rax
  4042bf:	85 c0                	test   %eax,%eax
  4042c1:	7e 57                	jle    40431a <timer_thread+0x17a>
    for (int y = 0 ; y < data->task_count ; y++) {
  4042c3:	8b 53 40             	mov    0x40(%rbx),%edx
  4042c6:	85 d2                	test   %edx,%edx
  4042c8:	7e 50                	jle    40431a <timer_thread+0x17a>
  4042ca:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
  4042d2:	8d 42 ff             	lea    -0x1(%rdx),%eax
      data->threads[x]->tasks[y].sending = 0;
  4042d5:	4c 8b 43 18          	mov    0x18(%rbx),%r8
  4042d9:	31 c9                	xor    %ecx,%ecx
  4042db:	48 c1 e0 09          	shl    $0x9,%rax
  4042df:	48 8d b8 80 03 00 00 	lea    0x380(%rax),%rdi
  4042e6:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
  4042ea:	48 8b 50 38          	mov    0x38(%rax),%rdx
  4042ee:	48 8d 82 80 01 00 00 	lea    0x180(%rdx),%rax
  4042f5:	48 01 fa             	add    %rdi,%rdx
  4042f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  404300:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
  404306:	48 05 00 02 00 00    	add    $0x200,%rax
  40430c:	48 39 c2             	cmp    %rax,%rdx
  40430f:	75 ef                	jne    404300 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
  404311:	48 83 c1 08          	add    $0x8,%rcx
  404315:	48 39 ce             	cmp    %rcx,%rsi
  404318:	75 cc                	jne    4042e6 <timer_thread+0x146>
  asm volatile ("mfence" ::: "memory");
  40431a:	0f ae f0             	mfence
  struct timespec drain = {
  40431d:	66 0f 6f 05 8b 38 00 00 	movdqa 0x388b(%rip),%xmm0        # 407bb0 <_IO_stdin_used+0xbb0>
  404325:	48 8d 2d 31 2d 00 00 	lea    0x2d31(%rip),%rbp        # 40705d <_IO_stdin_used+0x5d>
  40432c:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
  404331:	8b 53 28             	mov    0x28(%rbx),%edx
    y++;
  404334:	41 8d 47 01          	lea    0x1(%r15),%eax
  404338:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
  40433c:	85 d2                	test   %edx,%edx
  40433e:	7e 58                	jle    404398 <timer_thread+0x1f8>
  404340:	41 89 c1             	mov    %eax,%r9d
  404343:	48 8b 43 18          	mov    0x18(%rbx),%rax
        data->threads[x]->tasks[y].scheduled = 0;
  404347:	49 63 ff             	movslq %r15d,%rdi
  40434a:	83 ea 01             	sub    $0x1,%edx
  40434d:	48 c1 e7 09          	shl    $0x9,%rdi
  404351:	48 8d 48 08          	lea    0x8(%rax),%rcx
  404355:	4c 8d 04 d1          	lea    (%rcx,%rdx,8),%r8
  404359:	eb 09                	jmp    404364 <timer_thread+0x1c4>
  40435b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  404360:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
  404364:	4c 8b 38             	mov    (%rax),%r15
  404367:	44 89 c8             	mov    %r9d,%eax
  40436a:	99                   	cltd
  40436b:	41 f7 7f 40          	idivl  0x40(%r15)
        data->threads[x]->tasks[next].scheduled = 1;
  40436f:	49 8b 77 38          	mov    0x38(%r15),%rsi
    for (int x = 0 ; x < data->thread_count ; x++) {
  404373:	48 89 c8             	mov    %rcx,%rax
        data->threads[x]->tasks[next].scheduled = 1;
  404376:	48 63 d2             	movslq %edx,%rdx
  404379:	48 c1 e2 09          	shl    $0x9,%rdx
  40437d:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
  404388:	c7 84 3e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rdi,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
  404393:	4c 39 c1             	cmp    %r8,%rcx
  404396:	75 c8                	jne    404360 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
  404398:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
  40439b:	48 8b 43 18          	mov    0x18(%rbx),%rax
      y = 0;
  40439f:	8b 74 24 0c          	mov    0xc(%rsp),%esi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  4043a3:	8b 7b 30             	mov    0x30(%rbx),%edi
    if (y >= data->threads[0]->task_count) {
  4043a6:	48 8b 00             	mov    (%rax),%rax
      y = 0;
  4043a9:	39 70 40             	cmp    %esi,0x40(%rax)
  4043ac:	b8 00 00 00 00       	mov    $0x0,%eax
  4043b1:	0f 4f c6             	cmovg  %esi,%eax
  4043b4:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  4043b8:	85 ff                	test   %edi,%edi
  4043ba:	0f 8e fc 00 00 00    	jle    4044bc <timer_thread+0x31c>
  4043c0:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
  4043c3:	41 bf 01 00 00 00    	mov    $0x1,%r15d
  4043c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
  4043d0:	4d 63 e6             	movslq %r14d,%r12
  4043d3:	45 31 ed             	xor    %r13d,%r13d
  4043d6:	49 c1 e4 03          	shl    $0x3,%r12
  4043da:	45 89 ea             	mov    %r13d,%r10d
        for (int k = 0 ; k < data->my_thread_count; k++) {
  4043dd:	85 ff                	test   %edi,%edi
  4043df:	7e 6d                	jle    40444e <timer_thread+0x2ae>
  4043e1:	4c 89 ee             	mov    %r13,%rsi
  4043e4:	31 c0                	xor    %eax,%eax
  4043e6:	45 31 c0             	xor    %r8d,%r8d
  4043e9:	48 c1 e6 09          	shl    $0x9,%rsi
  4043ed:	0f 1f 00             	nopl   (%rax)
          if (x == k) { continue; }
  4043f0:	45 39 c6             	cmp    %r8d,%r14d
  4043f3:	74 39                	je     40442e <timer_thread+0x28e>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
  4043f5:	48 8b 53 18          	mov    0x18(%rbx),%rdx
  4043f9:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
  4043fd:	48 8b 52 38          	mov    0x38(%rdx),%rdx
  404401:	48 8b 8c 32 70 01 00 00 	mov    0x170(%rdx,%rsi,1),%rcx
  404409:	48 01 c1             	add    %rax,%rcx
  40440c:	48 89 ca             	mov    %rcx,%rdx
  40440f:	48 8b 09             	mov    (%rcx),%rcx
  404412:	48 8b 52 08          	mov    0x8(%rdx),%rdx
  404416:	4c 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9
  40441d:	4c 8b 9a 80 00 00 00 	mov    0x80(%rdx),%r11
  404424:	4d 85 c9             	test   %r9,%r9
  404427:	7f 47                	jg     404470 <timer_thread+0x2d0>
  404429:	4d 85 db             	test   %r11,%r11
  40442c:	7f 42                	jg     404470 <timer_thread+0x2d0>
        for (int k = 0 ; k < data->my_thread_count; k++) {
  40442e:	41 83 c0 01          	add    $0x1,%r8d
  404432:	48 83 c0 38          	add    $0x38,%rax
  404436:	41 39 f8             	cmp    %edi,%r8d
  404439:	75 b5                	jne    4043f0 <timer_thread+0x250>
      for (int y = 0 ; y < 2 ; y++) {
  40443b:	49 83 fd 01          	cmp    $0x1,%r13
  40443f:	74 68                	je     4044a9 <timer_thread+0x309>
  404441:	41 bd 01 00 00 00    	mov    $0x1,%r13d
  404447:	45 89 ea             	mov    %r13d,%r10d
        for (int k = 0 ; k < data->my_thread_count; k++) {
  40444a:	85 ff                	test   %edi,%edi
  40444c:	7f 93                	jg     4043e1 <timer_thread+0x241>
    if (all_empty == 1) {
  40444e:	41 83 ff 01          	cmp    $0x1,%r15d
  404452:	74 68                	je     4044bc <timer_thread+0x31c>
      nanosleep(&drain , &drainrem);
  404454:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
  404459:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  40445e:	e8 6d dc ff ff       	call   4020d0 <nanosleep@plt>
  404463:	44 8b 7c 24 0c       	mov    0xc(%rsp),%r15d
  404468:	e9 c4 fe ff ff       	jmp    404331 <timer_thread+0x191>
  40446d:	0f 1f 00             	nopl   (%rax)
  404470:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
  404476:	48 83 ec 08          	sub    $0x8,%rsp
  40447a:	44 89 f2             	mov    %r14d,%edx
  40447d:	48 89 ee             	mov    %rbp,%rsi
  404480:	bf 01 00 00 00       	mov    $0x1,%edi
            all_empty = 0;
  404485:	45 31 ff             	xor    %r15d,%r15d
  404488:	50                   	push   %rax
  404489:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
  40448f:	44 89 d1             	mov    %r10d,%ecx
  404492:	50                   	push   %rax
  404493:	31 c0                	xor    %eax,%eax
  404495:	41 53                	push   %r11
  404497:	e8 54 dd ff ff       	call   4021f0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  40449c:	8b 7b 30             	mov    0x30(%rbx),%edi
  40449f:	48 83 c4 20          	add    $0x20,%rsp
      for (int y = 0 ; y < 2 ; y++) {
  4044a3:	49 83 fd 01          	cmp    $0x1,%r13
  4044a7:	75 98                	jne    404441 <timer_thread+0x2a1>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  4044a9:	41 83 c6 01          	add    $0x1,%r14d
  4044ad:	41 39 fe             	cmp    %edi,%r14d
  4044b0:	0f 8c 1a ff ff ff    	jl     4043d0 <timer_thread+0x230>
    if (all_empty == 1) {
  4044b6:	41 83 ff 01          	cmp    $0x1,%r15d
  4044ba:	75 98                	jne    404454 <timer_thread+0x2b4>
  4044bc:	48 8d 3d 91 2b 00 00 	lea    0x2b91(%rip),%rdi        # 407054 <_IO_stdin_used+0x54>
  4044c3:	e8 98 db ff ff       	call   402060 <puts@plt>
  while (data->running) {
  4044c8:	8b 53 44             	mov    0x44(%rbx),%edx
  4044cb:	85 d2                	test   %edx,%edx
  4044cd:	0f 84 c5 00 00 00    	je     404598 <timer_thread+0x3f8>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  4044d3:	8b 43 2c             	mov    0x2c(%rbx),%eax
  4044d6:	31 ed                	xor    %ebp,%ebp
  4044d8:	4c 8d 2d 9b 2b 00 00 	lea    0x2b9b(%rip),%r13        # 40707a <_IO_stdin_used+0x7a>
  4044df:	4c 8d 35 af 2b 00 00 	lea    0x2baf(%rip),%r14        # 407095 <_IO_stdin_used+0x95>
  4044e6:	85 c0                	test   %eax,%eax
  4044e8:	7e 3b                	jle    404525 <timer_thread+0x385>
  4044ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  4044f0:	31 c0                	xor    %eax,%eax
  4044f2:	89 ea                	mov    %ebp,%edx
  4044f4:	4c 89 ee             	mov    %r13,%rsi
  4044f7:	bf 01 00 00 00       	mov    $0x1,%edi
  4044fc:	e8 ef dc ff ff       	call   4021f0 <__printf_chk@plt>
      data->threads[x]->running = 0;
  404501:	48 8b 43 18          	mov    0x18(%rbx),%rax
  404505:	4c 63 e5             	movslq %ebp,%r12
  404508:	4a 8b 04 e0          	mov    (%rax,%r12,8),%rax
      if (data->threads[x]->type == IO) {
  40450c:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
  404510:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
  404517:	0f 84 a8 00 00 00    	je     4045c5 <timer_thread+0x425>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  40451d:	83 c5 01             	add    $0x1,%ebp
  404520:	39 6b 2c             	cmp    %ebp,0x2c(%rbx)
  404523:	7f cb                	jg     4044f0 <timer_thread+0x350>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404525:	48 63 43 30          	movslq 0x30(%rbx),%rax
  404529:	85 c0                	test   %eax,%eax
  40452b:	7e 55                	jle    404582 <timer_thread+0x3e2>
      for (int y = 0 ; y < data->task_count ; y++) {
  40452d:	8b 53 40             	mov    0x40(%rbx),%edx
  404530:	85 d2                	test   %edx,%edx
  404532:	7e 4e                	jle    404582 <timer_thread+0x3e2>
  404534:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
  40453c:	8d 42 ff             	lea    -0x1(%rdx),%eax
        data->threads[x]->tasks[y].scheduled = 0;
  40453f:	4c 8b 43 18          	mov    0x18(%rbx),%r8
  404543:	31 c9                	xor    %ecx,%ecx
  404545:	48 c1 e0 09          	shl    $0x9,%rax
  404549:	48 8d b8 4c 03 00 00 	lea    0x34c(%rax),%rdi
  404550:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
  404554:	48 8b 50 38          	mov    0x38(%rax),%rdx
  404558:	48 8d 82 4c 01 00 00 	lea    0x14c(%rdx),%rax
  40455f:	48 01 fa             	add    %rdi,%rdx
  404562:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  404568:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
  40456e:	48 05 00 02 00 00    	add    $0x200,%rax
  404574:	48 39 c2             	cmp    %rax,%rdx
  404577:	75 ef                	jne    404568 <timer_thread+0x3c8>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404579:	48 83 c1 08          	add    $0x8,%rcx
  40457d:	48 39 ce             	cmp    %rcx,%rsi
  404580:	75 ce                	jne    404550 <timer_thread+0x3b0>
    asm volatile ("mfence" ::: "memory");
  404582:	0f ae f0             	mfence
  404585:	48 8d 3d 1b 2b 00 00 	lea    0x2b1b(%rip),%rdi        # 4070a7 <_IO_stdin_used+0xa7>
  40458c:	e8 cf da ff ff       	call   402060 <puts@plt>
    data->running = 0;
  404591:	c7 43 44 00 00 00 00 	movl   $0x0,0x44(%rbx)
  404598:	48 8d 3d 0f 2b 00 00 	lea    0x2b0f(%rip),%rdi        # 4070ae <_IO_stdin_used+0xae>
  40459f:	e8 bc da ff ff       	call   402060 <puts@plt>
}
  4045a4:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  4045a9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4045b2:	75 3f                	jne    4045f3 <timer_thread+0x453>
  4045b4:	48 83 c4 68          	add    $0x68,%rsp
  4045b8:	31 c0                	xor    %eax,%eax
  4045ba:	5b                   	pop    %rbx
  4045bb:	5d                   	pop    %rbp
  4045bc:	41 5c                	pop    %r12
  4045be:	41 5d                	pop    %r13
  4045c0:	41 5e                	pop    %r14
  4045c2:	41 5f                	pop    %r15
  4045c4:	c3                   	ret
  4045c5:	4c 89 f7             	mov    %r14,%rdi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  4045c8:	83 c5 01             	add    $0x1,%ebp
  4045cb:	e8 90 da ff ff       	call   402060 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
  4045d0:	48 8b 43 18          	mov    0x18(%rbx),%rax
  4045d4:	be 01 00 00 00       	mov    $0x1,%esi
  4045d9:	4a 8b 04 e0          	mov    (%rax,%r12,8),%rax
  4045dd:	8b 78 60             	mov    0x60(%rax),%edi
  4045e0:	e8 ab db ff ff       	call   402190 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  4045e5:	3b 6b 2c             	cmp    0x2c(%rbx),%ebp
  4045e8:	0f 8c 02 ff ff ff    	jl     4044f0 <timer_thread+0x350>
  4045ee:	e9 32 ff ff ff       	jmp    404525 <timer_thread+0x385>
}
  4045f3:	e8 b8 da ff ff       	call   4020b0 <__stack_chk_fail@plt>
  4045f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000404600 <minf>:
}
  404600:	39 f7                	cmp    %esi,%edi
  404602:	89 f0                	mov    %esi,%eax
  404604:	0f 4e c7             	cmovle %edi,%eax
  404607:	c3                   	ret
  404608:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000404610 <maxf>:
}
  404610:	39 f7                	cmp    %esi,%edi
  404612:	89 f0                	mov    %esi,%eax
  404614:	0f 4d c7             	cmovge %edi,%eax
  404617:	c3                   	ret
  404618:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000404620 <fatal_error>:
void fatal_error(const char *syscall) {
  404620:	48 83 ec 08          	sub    $0x8,%rsp
    perror(syscall);
  404624:	e8 17 dc ff ff       	call   402240 <perror@plt>
    exit(1);
  404629:	bf 01 00 00 00       	mov    $0x1,%edi
  40462e:	e8 1d dc ff ff       	call   402250 <exit@plt>
  404633:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40463e:	66 90                	xchg   %ax,%ax

0000000000404640 <strtolower>:
void strtolower(char *str) {
  404640:	55                   	push   %rbp
  404641:	53                   	push   %rbx
  404642:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
  404646:	48 0f be 1f          	movsbq (%rdi),%rbx
  40464a:	84 db                	test   %bl,%bl
  40464c:	74 28                	je     404676 <strtolower+0x36>
  40464e:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
  404651:	e8 8a dc ff ff       	call   4022e0 <__ctype_tolower_loc@plt>
  404656:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  404660:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
  404663:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
  404667:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
  40466a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
  40466d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
  404672:	84 db                	test   %bl,%bl
  404674:	75 ea                	jne    404660 <strtolower+0x20>
}
  404676:	48 83 c4 08          	add    $0x8,%rsp
  40467a:	5b                   	pop    %rbx
  40467b:	5d                   	pop    %rbp
  40467c:	c3                   	ret
  40467d:	0f 1f 00             	nopl   (%rax)

0000000000404680 <zh_malloc>:
void *zh_malloc(size_t size) {
  404680:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
  404684:	e8 27 db ff ff       	call   4021b0 <malloc@plt>
    if (!buf) {
  404689:	48 85 c0             	test   %rax,%rax
  40468c:	74 05                	je     404693 <zh_malloc+0x13>
}
  40468e:	48 83 c4 08          	add    $0x8,%rsp
  404692:	c3                   	ret
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
  404693:	48 8b 05 5e 59 00 00 	mov    0x595e(%rip),%rax        # 409ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  40469a:	ba 28 00 00 00       	mov    $0x28,%edx
  40469f:	be 01 00 00 00       	mov    $0x1,%esi
  4046a4:	48 8d 3d 15 2f 00 00 	lea    0x2f15(%rip),%rdi        # 4075c0 <_IO_stdin_used+0x5c0>
  4046ab:	48 8b 08             	mov    (%rax),%rcx
  4046ae:	e8 bd db ff ff       	call   402270 <fwrite@plt>
        exit(1);
  4046b3:	bf 01 00 00 00       	mov    $0x1,%edi
  4046b8:	e8 93 db ff ff       	call   402250 <exit@plt>
  4046bd:	0f 1f 00             	nopl   (%rax)

00000000004046c0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
  4046c0:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
  4046c1:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
  4046c6:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
  4046c9:	e8 12 da ff ff       	call   4020e0 <strrchr@plt>
    if (!dot || dot == filename)
  4046ce:	48 85 c0             	test   %rax,%rax
  4046d1:	74 0d                	je     4046e0 <get_filename_ext+0x20>
  4046d3:	48 39 c3             	cmp    %rax,%rbx
  4046d6:	74 08                	je     4046e0 <get_filename_ext+0x20>
    return dot + 1;
  4046d8:	48 83 c0 01          	add    $0x1,%rax
}
  4046dc:	5b                   	pop    %rbx
  4046dd:	c3                   	ret
  4046de:	66 90                	xchg   %ax,%ax
        return "";
  4046e0:	48 8d 05 0f 2a 00 00 	lea    0x2a0f(%rip),%rax        # 4070f6 <_IO_stdin_used+0xf6>
}
  4046e7:	5b                   	pop    %rbx
  4046e8:	c3                   	ret
  4046e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000004046f0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
  4046f0:	41 55                	push   %r13
  4046f2:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  4046f5:	48 89 fe             	mov    %rdi,%rsi
  4046f8:	41 54                	push   %r12
  return __builtin___memcpy_chk (__dest, __src, __len,
  4046fa:	41 bc 31 0d 00 00    	mov    $0xd31,%r12d
  404700:	55                   	push   %rbp
  404701:	53                   	push   %rbx
  404702:	48 89 d3             	mov    %rdx,%rbx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404705:	ba 00 04 00 00       	mov    $0x400,%edx
  40470a:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
  404711:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40471a:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
  404722:	31 c0                	xor    %eax,%eax
  404724:	48 89 e5             	mov    %rsp,%rbp
  404727:	48 89 ef             	mov    %rbp,%rdi
  40472a:	e8 a1 da ff ff       	call   4021d0 <__strcpy_chk@plt>
    strtolower(small_case_path);
  40472f:	48 89 ef             	mov    %rbp,%rdi
  404732:	e8 09 ff ff ff       	call   404640 <strtolower>
    iov[0].iov_base = zh_malloc(slen);
  404737:	bf 11 00 00 00       	mov    $0x11,%edi
  40473c:	e8 3f ff ff ff       	call   404680 <zh_malloc>
    iov[0].iov_len = slen;
  404741:	48 c7 43 08 11 00 00 00 	movq   $0x11,0x8(%rbx)
    iov[1].iov_base = zh_malloc(slen);
  404749:	bf 17 00 00 00       	mov    $0x17,%edi
  return __builtin___memcpy_chk (__dest, __src, __len,
  40474e:	66 0f 6f 05 6a 34 00 00 	movdqa 0x346a(%rip),%xmm0        # 407bc0 <_IO_stdin_used+0xbc0>
    iov[0].iov_base = zh_malloc(slen);
  404756:	48 89 03             	mov    %rax,(%rbx)
  404759:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
  40475d:	0f 11 00             	movups %xmm0,(%rax)
    iov[1].iov_base = zh_malloc(slen);
  404760:	e8 1b ff ff ff       	call   404680 <zh_malloc>
    iov[1].iov_len = slen;
  404765:	48 c7 43 18 17 00 00 00 	movq   $0x17,0x18(%rbx)
  40476d:	66 0f 6f 05 5b 34 00 00 	movdqa 0x345b(%rip),%xmm0        # 407bd0 <_IO_stdin_used+0xbd0>
    const char *file_ext = get_filename_ext(small_case_path);
  404775:	48 89 ef             	mov    %rbp,%rdi
    iov[1].iov_base = zh_malloc(slen);
  404778:	48 89 43 10          	mov    %rax,0x10(%rbx)
  40477c:	c7 40 10 64 2f 30 2e 	movl   $0x2e302f64,0x10(%rax)
  404783:	66 44 89 60 14       	mov    %r12w,0x14(%rax)
  404788:	c6 40 16 0a          	movb   $0xa,0x16(%rax)
  40478c:	0f 11 00             	movups %xmm0,(%rax)
    const char *file_ext = get_filename_ext(small_case_path);
  40478f:	e8 2c ff ff ff       	call   4046c0 <get_filename_ext>
    if (strcmp("jpg", file_ext) == 0)
  404794:	48 8d 3d 29 29 00 00 	lea    0x2929(%rip),%rdi        # 4070c4 <_IO_stdin_used+0xc4>
  40479b:	48 89 c6             	mov    %rax,%rsi
    const char *file_ext = get_filename_ext(small_case_path);
  40479e:	48 89 c5             	mov    %rax,%rbp
    if (strcmp("jpg", file_ext) == 0)
  4047a1:	e8 9a d9 ff ff       	call   402140 <strcmp@plt>
  4047a6:	85 c0                	test   %eax,%eax
  4047a8:	0f 84 42 03 00 00    	je     404af0 <send_headers+0x400>
    if (strcmp("jpeg", file_ext) == 0)
  4047ae:	48 89 ee             	mov    %rbp,%rsi
  4047b1:	48 8d 3d 10 29 00 00 	lea    0x2910(%rip),%rdi        # 4070c8 <_IO_stdin_used+0xc8>
  4047b8:	e8 83 d9 ff ff       	call   402140 <strcmp@plt>
  4047bd:	85 c0                	test   %eax,%eax
  4047bf:	0f 84 eb 02 00 00    	je     404ab0 <send_headers+0x3c0>
    if (strcmp("png", file_ext) == 0)
  4047c5:	48 89 ee             	mov    %rbp,%rsi
  4047c8:	48 8d 3d fe 28 00 00 	lea    0x28fe(%rip),%rdi        # 4070cd <_IO_stdin_used+0xcd>
  4047cf:	e8 6c d9 ff ff       	call   402140 <strcmp@plt>
  4047d4:	85 c0                	test   %eax,%eax
  4047d6:	0f 84 04 04 00 00    	je     404be0 <send_headers+0x4f0>
    if (strcmp("gif", file_ext) == 0)
  4047dc:	48 89 ee             	mov    %rbp,%rsi
  4047df:	48 8d 3d eb 28 00 00 	lea    0x28eb(%rip),%rdi        # 4070d1 <_IO_stdin_used+0xd1>
  4047e6:	e8 55 d9 ff ff       	call   402140 <strcmp@plt>
  4047eb:	85 c0                	test   %eax,%eax
  4047ed:	0f 84 ad 03 00 00    	je     404ba0 <send_headers+0x4b0>
    if (strcmp("htm", file_ext) == 0)
  4047f3:	48 89 ee             	mov    %rbp,%rsi
  4047f6:	48 8d 3d d8 28 00 00 	lea    0x28d8(%rip),%rdi        # 4070d5 <_IO_stdin_used+0xd5>
  4047fd:	e8 3e d9 ff ff       	call   402140 <strcmp@plt>
  404802:	85 c0                	test   %eax,%eax
  404804:	0f 84 5e 03 00 00    	je     404b68 <send_headers+0x478>
    if (strcmp("html", file_ext) == 0)
  40480a:	48 89 ee             	mov    %rbp,%rsi
  40480d:	48 8d 3d 04 29 00 00 	lea    0x2904(%rip),%rdi        # 407118 <_IO_stdin_used+0x118>
  404814:	e8 27 d9 ff ff       	call   402140 <strcmp@plt>
  404819:	85 c0                	test   %eax,%eax
  40481b:	0f 84 0f 03 00 00    	je     404b30 <send_headers+0x440>
    if (strcmp("js", file_ext) == 0)
  404821:	80 7d 00 6a          	cmpb   $0x6a,0x0(%rbp)
  404825:	75 0a                	jne    404831 <send_headers+0x141>
  404827:	80 7d 01 73          	cmpb   $0x73,0x1(%rbp)
  40482b:	0f 84 b7 01 00 00    	je     4049e8 <send_headers+0x2f8>
    if (strcmp("css", file_ext) == 0)
  404831:	48 89 ee             	mov    %rbp,%rsi
  404834:	48 8d 3d 9e 28 00 00 	lea    0x289e(%rip),%rdi        # 4070d9 <_IO_stdin_used+0xd9>
  40483b:	e8 00 d9 ff ff       	call   402140 <strcmp@plt>
  404840:	85 c0                	test   %eax,%eax
  404842:	0f 84 f8 01 00 00    	je     404a40 <send_headers+0x350>
    if (strcmp("txt", file_ext) == 0)
  404848:	48 89 ee             	mov    %rbp,%rsi
  40484b:	48 8d 3d 8b 28 00 00 	lea    0x288b(%rip),%rdi        # 4070dd <_IO_stdin_used+0xdd>
  404852:	e8 e9 d8 ff ff       	call   402140 <strcmp@plt>
  404857:	85 c0                	test   %eax,%eax
  404859:	0f 84 11 02 00 00    	je     404a70 <send_headers+0x380>
    slen = strlen(send_buffer);
  40485f:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
  404867:	4c 89 e7             	mov    %r12,%rdi
  40486a:	e8 31 d8 ff ff       	call   4020a0 <strlen@plt>
    iov[2].iov_base = zh_malloc(slen);
  40486f:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
  404872:	48 89 c5             	mov    %rax,%rbp
    iov[2].iov_base = zh_malloc(slen);
  404875:	e8 06 fe ff ff       	call   404680 <zh_malloc>
    iov[2].iov_len = slen;
  40487a:	48 89 6b 28          	mov    %rbp,0x28(%rbx)
    iov[2].iov_base = zh_malloc(slen);
  40487e:	48 89 43 20          	mov    %rax,0x20(%rbx)
  404882:	83 fd 08             	cmp    $0x8,%ebp
  404885:	73 31                	jae    4048b8 <send_headers+0x1c8>
  404887:	40 f6 c5 04          	test   $0x4,%bpl
  40488b:	0f 85 8f 03 00 00    	jne    404c20 <send_headers+0x530>
  404891:	85 ed                	test   %ebp,%ebp
  404893:	74 55                	je     4048ea <send_headers+0x1fa>
  404895:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
  40489d:	88 10                	mov    %dl,(%rax)
  40489f:	40 f6 c5 02          	test   $0x2,%bpl
  4048a3:	74 45                	je     4048ea <send_headers+0x1fa>
  4048a5:	89 ed                	mov    %ebp,%ebp
  4048a7:	41 0f b7 54 2c fe    	movzwl -0x2(%r12,%rbp,1),%edx
  4048ad:	66 89 54 28 fe       	mov    %dx,-0x2(%rax,%rbp,1)
  4048b2:	eb 36                	jmp    4048ea <send_headers+0x1fa>
  4048b4:	0f 1f 40 00          	nopl   0x0(%rax)
  4048b8:	48 8b 94 24 00 04 00 00 	mov    0x400(%rsp),%rdx
  4048c0:	48 8d 78 08          	lea    0x8(%rax),%rdi
  4048c4:	4c 89 e6             	mov    %r12,%rsi
  4048c7:	48 83 e7 f8          	and    $0xfffffffffffffff8,%rdi
  4048cb:	48 89 10             	mov    %rdx,(%rax)
  4048ce:	89 ea                	mov    %ebp,%edx
  4048d0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
  4048d5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
  4048da:	48 29 f8             	sub    %rdi,%rax
  4048dd:	8d 4c 05 00          	lea    0x0(%rbp,%rax,1),%ecx
  4048e1:	48 29 c6             	sub    %rax,%rsi
  4048e4:	c1 e9 03             	shr    $0x3,%ecx
  4048e7:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  4048ea:	4d 89 e8             	mov    %r13,%r8
  4048ed:	48 8d 0d ed 27 00 00 	lea    0x27ed(%rip),%rcx        # 4070e1 <_IO_stdin_used+0xe1>
  4048f4:	4c 89 e7             	mov    %r12,%rdi
  4048f7:	31 c0                	xor    %eax,%eax
  4048f9:	ba 00 04 00 00       	mov    $0x400,%edx
  4048fe:	be 01 00 00 00       	mov    $0x1,%esi
  404903:	e8 e8 d9 ff ff       	call   4022f0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
  404908:	4c 89 e7             	mov    %r12,%rdi
  40490b:	e8 90 d7 ff ff       	call   4020a0 <strlen@plt>
    iov[3].iov_base = zh_malloc(slen);
  404910:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
  404913:	48 89 c5             	mov    %rax,%rbp
    iov[3].iov_base = zh_malloc(slen);
  404916:	e8 65 fd ff ff       	call   404680 <zh_malloc>
    iov[3].iov_len = slen;
  40491b:	48 89 6b 38          	mov    %rbp,0x38(%rbx)
    iov[3].iov_base = zh_malloc(slen);
  40491f:	48 89 43 30          	mov    %rax,0x30(%rbx)
  404923:	83 fd 08             	cmp    $0x8,%ebp
  404926:	73 30                	jae    404958 <send_headers+0x268>
  404928:	40 f6 c5 04          	test   $0x4,%bpl
  40492c:	0f 85 0e 03 00 00    	jne    404c40 <send_headers+0x550>
  404932:	85 ed                	test   %ebp,%ebp
  404934:	74 54                	je     40498a <send_headers+0x29a>
  404936:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
  40493e:	88 10                	mov    %dl,(%rax)
  404940:	40 f6 c5 02          	test   $0x2,%bpl
  404944:	74 44                	je     40498a <send_headers+0x29a>
  404946:	89 ed                	mov    %ebp,%ebp
  404948:	41 0f b7 54 2c fe    	movzwl -0x2(%r12,%rbp,1),%edx
  40494e:	66 89 54 28 fe       	mov    %dx,-0x2(%rax,%rbp,1)
  404953:	eb 35                	jmp    40498a <send_headers+0x29a>
  404955:	0f 1f 00             	nopl   (%rax)
  404958:	48 8b 94 24 00 04 00 00 	mov    0x400(%rsp),%rdx
  404960:	48 8d 78 08          	lea    0x8(%rax),%rdi
  404964:	4c 89 e6             	mov    %r12,%rsi
  404967:	48 83 e7 f8          	and    $0xfffffffffffffff8,%rdi
  40496b:	48 89 10             	mov    %rdx,(%rax)
  40496e:	89 ea                	mov    %ebp,%edx
  404970:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
  404975:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
  40497a:	48 29 f8             	sub    %rdi,%rax
  40497d:	8d 4c 05 00          	lea    0x0(%rbp,%rax,1),%ecx
  404981:	48 29 c6             	sub    %rax,%rsi
  404984:	c1 e9 03             	shr    $0x3,%ecx
  404987:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  40498a:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    iov[4].iov_base = zh_malloc(slen);
  40498f:	bf 02 00 00 00       	mov    $0x2,%edi
  404994:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
  40499c:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
  4049a4:	e8 d7 fc ff ff       	call   404680 <zh_malloc>
  4049a9:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_len = slen;
  4049b1:	48 c7 43 48 02 00 00 00 	movq   $0x2,0x48(%rbx)
    iov[4].iov_base = zh_malloc(slen);
  4049b9:	48 89 43 40          	mov    %rax,0x40(%rbx)
  return __builtin___memcpy_chk (__dest, __src, __len,
  4049bd:	66 89 10             	mov    %dx,(%rax)
}
  4049c0:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
  4049c8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4049d1:	0f 85 82 02 00 00    	jne    404c59 <send_headers+0x569>
  4049d7:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
  4049de:	5b                   	pop    %rbx
  4049df:	5d                   	pop    %rbp
  4049e0:	41 5c                	pop    %r12
  4049e2:	41 5d                	pop    %r13
  4049e4:	c3                   	ret
  4049e5:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
  4049e8:	80 7d 02 00          	cmpb   $0x0,0x2(%rbp)
  4049ec:	0f 85 3f fe ff ff    	jne    404831 <send_headers+0x141>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  4049f2:	66 0f 6f 05 06 32 00 00 	movdqa 0x3206(%rip),%xmm0        # 407c00 <_IO_stdin_used+0xc00>
  4049fa:	b9 0d 0a 00 00       	mov    $0xa0d,%ecx
  4049ff:	c7 84 24 20 04 00 00 72 69 70 74 	movl   $0x74706972,0x420(%rsp)
  404a0a:	66 89 8c 24 24 04 00 00 	mov    %cx,0x424(%rsp)
  404a12:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404a1a:	66 0f 6f 05 ee 31 00 00 	movdqa 0x31ee(%rip),%xmm0        # 407c10 <_IO_stdin_used+0xc10>
  404a22:	c6 84 24 26 04 00 00 00 	movb   $0x0,0x426(%rsp)
  404a2a:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
  404a32:	e9 fa fd ff ff       	jmp    404831 <send_headers+0x141>
  404a37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  404a40:	66 0f 6f 05 a8 31 00 00 	movdqa 0x31a8(%rip),%xmm0        # 407bf0 <_IO_stdin_used+0xbf0>
  404a48:	c6 84 24 18 04 00 00 00 	movb   $0x0,0x418(%rsp)
  404a50:	48 b8 78 74 2f 63 73 73 0d 0a 	movabs $0xa0d7373632f7478,%rax
  404a5a:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404a62:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404a6a:	e9 d9 fd ff ff       	jmp    404848 <send_headers+0x158>
  404a6f:	90                   	nop
  404a70:	66 0f 6f 05 78 31 00 00 	movdqa 0x3178(%rip),%xmm0        # 407bf0 <_IO_stdin_used+0xbf0>
  404a78:	ba 0d 0a 00 00       	mov    $0xa0d,%edx
  404a7d:	48 b8 78 74 2f 70 6c 61 69 6e 	movabs $0x6e69616c702f7478,%rax
  404a87:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  404a8f:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404a97:	66 89 94 24 18 04 00 00 	mov    %dx,0x418(%rsp)
  404a9f:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404aa7:	e9 b3 fd ff ff       	jmp    40485f <send_headers+0x16f>
  404aac:	0f 1f 40 00          	nopl   0x0(%rax)
  404ab0:	66 0f 6f 05 28 31 00 00 	movdqa 0x3128(%rip),%xmm0        # 407be0 <_IO_stdin_used+0xbe0>
  404ab8:	41 ba 0d 0a 00 00    	mov    $0xa0d,%r10d
  404abe:	48 b8 61 67 65 2f 6a 70 65 67 	movabs $0x6765706a2f656761,%rax
  404ac8:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  404ad0:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404ad8:	66 44 89 94 24 18 04 00 00 	mov    %r10w,0x418(%rsp)
  404ae1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404ae9:	e9 d7 fc ff ff       	jmp    4047c5 <send_headers+0xd5>
  404aee:	66 90                	xchg   %ax,%ax
  404af0:	66 0f 6f 05 e8 30 00 00 	movdqa 0x30e8(%rip),%xmm0        # 407be0 <_IO_stdin_used+0xbe0>
  404af8:	41 bb 0d 0a 00 00    	mov    $0xa0d,%r11d
  404afe:	48 b8 61 67 65 2f 6a 70 65 67 	movabs $0x6765706a2f656761,%rax
  404b08:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  404b10:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404b18:	66 44 89 9c 24 18 04 00 00 	mov    %r11w,0x418(%rsp)
  404b21:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404b29:	e9 80 fc ff ff       	jmp    4047ae <send_headers+0xbe>
  404b2e:	66 90                	xchg   %ax,%ax
  404b30:	66 0f 6f 05 b8 30 00 00 	movdqa 0x30b8(%rip),%xmm0        # 407bf0 <_IO_stdin_used+0xbf0>
  404b38:	be 0a 00 00 00       	mov    $0xa,%esi
  404b3d:	48 b8 78 74 2f 68 74 6d 6c 0d 	movabs $0xd6c6d74682f7478,%rax
  404b47:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404b4f:	66 89 b4 24 18 04 00 00 	mov    %si,0x418(%rsp)
  404b57:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404b5f:	e9 bd fc ff ff       	jmp    404821 <send_headers+0x131>
  404b64:	0f 1f 40 00          	nopl   0x0(%rax)
  404b68:	66 0f 6f 05 80 30 00 00 	movdqa 0x3080(%rip),%xmm0        # 407bf0 <_IO_stdin_used+0xbf0>
  404b70:	bf 0a 00 00 00       	mov    $0xa,%edi
  404b75:	48 b8 78 74 2f 68 74 6d 6c 0d 	movabs $0xd6c6d74682f7478,%rax
  404b7f:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404b87:	66 89 bc 24 18 04 00 00 	mov    %di,0x418(%rsp)
  404b8f:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404b97:	e9 6e fc ff ff       	jmp    40480a <send_headers+0x11a>
  404b9c:	0f 1f 40 00          	nopl   0x0(%rax)
  404ba0:	66 0f 6f 05 38 30 00 00 	movdqa 0x3038(%rip),%xmm0        # 407be0 <_IO_stdin_used+0xbe0>
  404ba8:	41 b8 0a 00 00 00    	mov    $0xa,%r8d
  404bae:	48 b8 61 67 65 2f 67 69 66 0d 	movabs $0xd6669672f656761,%rax
  404bb8:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404bc0:	66 44 89 84 24 18 04 00 00 	mov    %r8w,0x418(%rsp)
  404bc9:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404bd1:	e9 1d fc ff ff       	jmp    4047f3 <send_headers+0x103>
  404bd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  404be0:	66 0f 6f 05 f8 2f 00 00 	movdqa 0x2ff8(%rip),%xmm0        # 407be0 <_IO_stdin_used+0xbe0>
  404be8:	41 b9 0a 00 00 00    	mov    $0xa,%r9d
  404bee:	48 b8 61 67 65 2f 70 6e 67 0d 	movabs $0xd676e702f656761,%rax
  404bf8:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404c00:	66 44 89 8c 24 18 04 00 00 	mov    %r9w,0x418(%rsp)
  404c09:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404c11:	e9 c6 fb ff ff       	jmp    4047dc <send_headers+0xec>
  404c16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
  404c20:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
  404c27:	89 ed                	mov    %ebp,%ebp
  404c29:	89 10                	mov    %edx,(%rax)
  404c2b:	41 8b 54 2c fc       	mov    -0x4(%r12,%rbp,1),%edx
  404c30:	89 54 28 fc          	mov    %edx,-0x4(%rax,%rbp,1)
  404c34:	e9 b1 fc ff ff       	jmp    4048ea <send_headers+0x1fa>
  404c39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  404c40:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
  404c47:	89 ed                	mov    %ebp,%ebp
  404c49:	89 10                	mov    %edx,(%rax)
  404c4b:	41 8b 54 2c fc       	mov    -0x4(%r12,%rbp,1),%edx
  404c50:	89 54 28 fc          	mov    %edx,-0x4(%rax,%rbp,1)
  404c54:	e9 31 fd ff ff       	jmp    40498a <send_headers+0x29a>
}
  404c59:	e8 52 d4 ff ff       	call   4020b0 <__stack_chk_fail@plt>
  404c5e:	66 90                	xchg   %ax,%ax

0000000000404c60 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
  404c60:	41 55                	push   %r13
  404c62:	41 54                	push   %r12
  404c64:	49 89 d4             	mov    %rdx,%r12
  404c67:	55                   	push   %rbp
  404c68:	48 89 fd             	mov    %rdi,%rbp
    char *buf = zh_malloc(file_size);
  404c6b:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
  404c6e:	53                   	push   %rbx
  404c6f:	48 89 f3             	mov    %rsi,%rbx
  404c72:	48 83 ec 08          	sub    $0x8,%rsp
    char *buf = zh_malloc(file_size);
  404c76:	e8 05 fa ff ff       	call   404680 <zh_malloc>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
  404c7b:	48 89 ef             	mov    %rbp,%rdi
  404c7e:	31 f6                	xor    %esi,%esi
  404c80:	49 89 c5             	mov    %rax,%r13
  404c83:	31 c0                	xor    %eax,%eax
  404c85:	e8 96 d5 ff ff       	call   402220 <open@plt>
  404c8a:	89 c5                	mov    %eax,%ebp
    if (fd < 0)
  404c8c:	85 c0                	test   %eax,%eax
  404c8e:	78 58                	js     404ce8 <copy_file_contents+0x88>
		       "the destination buffer");

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
  404c90:	48 89 da             	mov    %rbx,%rdx
  404c93:	4c 89 ee             	mov    %r13,%rsi
  404c96:	89 ef                	mov    %ebp,%edi
  404c98:	e8 83 d4 ff ff       	call   402120 <read@plt>
    if (ret < file_size) {
  404c9d:	48 98                	cltq
  404c9f:	48 39 d8             	cmp    %rbx,%rax
  404ca2:	7c 1c                	jl     404cc0 <copy_file_contents+0x60>
    close(fd);
  404ca4:	89 ef                	mov    %ebp,%edi
  404ca6:	e8 55 d4 ff ff       	call   402100 <close@plt>
    iov->iov_base = buf;
  404cab:	4d 89 2c 24          	mov    %r13,(%r12)
    iov->iov_len = file_size;
  404caf:	49 89 5c 24 08       	mov    %rbx,0x8(%r12)
}
  404cb4:	48 83 c4 08          	add    $0x8,%rsp
  404cb8:	5b                   	pop    %rbx
  404cb9:	5d                   	pop    %rbp
  404cba:	41 5c                	pop    %r12
  404cbc:	41 5d                	pop    %r13
  404cbe:	c3                   	ret
  404cbf:	90                   	nop
        fprintf(stderr, "Encountered a short read.\n");
  404cc0:	48 8b 05 31 53 00 00 	mov    0x5331(%rip),%rax        # 409ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  404cc7:	ba 1a 00 00 00       	mov    $0x1a,%edx
  404ccc:	be 01 00 00 00       	mov    $0x1,%esi
  404cd1:	48 8d 3d 1f 24 00 00 	lea    0x241f(%rip),%rdi        # 4070f7 <_IO_stdin_used+0xf7>
  404cd8:	48 8b 08             	mov    (%rax),%rcx
  404cdb:	e8 90 d5 ff ff       	call   402270 <fwrite@plt>
  404ce0:	eb c2                	jmp    404ca4 <copy_file_contents+0x44>
  404ce2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        fatal_error("read");
  404ce8:	48 8d 3d 37 25 00 00 	lea    0x2537(%rip),%rdi        # 407226 <_IO_stdin_used+0x226>
  404cef:	e8 2c f9 ff ff       	call   404620 <fatal_error>
  404cf4:	eb 9a                	jmp    404c90 <copy_file_contents+0x30>
  404cf6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000404d00 <add_write_request>:
 * Returns a vacant sqe, or NULL if we're full.
 */
static inline struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  404d00:	48 8b 06             	mov    (%rsi),%rax
int add_write_request(struct Request *req, struct io_uring *ring) {
  404d03:	48 89 fa             	mov    %rdi,%rdx
  404d06:	48 89 f7             	mov    %rsi,%rdi
  404d09:	44 8b 00             	mov    (%rax),%r8d
	unsigned int next = sq->sqe_tail + 1;
  404d0c:	8b 46 44             	mov    0x44(%rsi),%eax
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
  404d0f:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int next = sq->sqe_tail + 1;
  404d15:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;

	if (next - head <= *sq->kring_entries) {
  404d18:	41 89 f1             	mov    %esi,%r9d
  404d1b:	45 29 c1             	sub    %r8d,%r9d
  404d1e:	4c 8b 47 18          	mov    0x18(%rdi),%r8
  404d22:	45 3b 08             	cmp    (%r8),%r9d
  404d25:	0f 87 e5 d5 ff ff    	ja     402310 <add_write_request.cold>
  404d2b:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404d2f:	4c 8b 47 10          	mov    0x10(%rdi),%r8
	if (ring->flags & IORING_SETUP_SQE128)
  404d33:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  404d36:	66 0f ef c0          	pxor   %xmm0,%xmm0
	if (ring->flags & IORING_SETUP_SQE128)
  404d3a:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404d3d:	41 23 00             	and    (%r8),%eax
		sq->sqe_tail = next;
  404d40:	89 77 44             	mov    %esi,0x44(%rdi)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404d43:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
  404d45:	8b 72 08             	mov    0x8(%rdx),%esi
  404d48:	8b 4a 04             	mov    0x4(%rdx),%ecx
  404d4b:	48 c1 e0 06          	shl    $0x6,%rax
  404d4f:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
  404d53:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
  404d59:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
  404d5c:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
  404d60:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
  404d66:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
  404d6e:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
  404d72:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
  404d75:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
  404d7c:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  404d84:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
  404d88:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
  404d8c:	e8 2f d3 ff ff       	call   4020c0 <io_uring_submit@plt>
}
  404d91:	31 c0                	xor    %eax,%eax
  404d93:	48 83 c4 08          	add    $0x8,%rsp
  404d97:	c3                   	ret
  404d98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000404da0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
  404da0:	41 55                	push   %r13
  404da2:	41 54                	push   %r12
  404da4:	55                   	push   %rbp
  404da5:	48 89 f5             	mov    %rsi,%rbp
  404da8:	53                   	push   %rbx
  404da9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  404dad:	48 8b 06             	mov    (%rsi),%rax
  404db0:	8b 10                	mov    (%rax),%edx
	unsigned int next = sq->sqe_tail + 1;
  404db2:	8b 5e 44             	mov    0x44(%rsi),%ebx
	if (ring->flags & IORING_SETUP_SQE128)
  404db5:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
	unsigned int next = sq->sqe_tail + 1;
  404dbb:	8d 43 01             	lea    0x1(%rbx),%eax
	if (next - head <= *sq->kring_entries) {
  404dbe:	89 c6                	mov    %eax,%esi
  404dc0:	29 d6                	sub    %edx,%esi
  404dc2:	48 8b 55 18          	mov    0x18(%rbp),%rdx
  404dc6:	3b 32                	cmp    (%rdx),%esi
  404dc8:	0f 87 52 d5 ff ff    	ja     402320 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404dce:	48 8b 55 10          	mov    0x10(%rbp),%rdx
	if (ring->flags & IORING_SETUP_SQE128)
  404dd2:	c1 e9 0a             	shr    $0xa,%ecx
  404dd5:	41 89 fd             	mov    %edi,%r13d
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
  404dd8:	bf 20 00 00 00       	mov    $0x20,%edi
  404ddd:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404de0:	23 1a                	and    (%rdx),%ebx
		sq->sqe_tail = next;
  404de2:	89 45 44             	mov    %eax,0x44(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404de5:	d3 e3                	shl    %cl,%ebx
  404de7:	48 c1 e3 06          	shl    $0x6,%rbx
  404deb:	48 03 5d 38          	add    0x38(%rbp),%rbx
  404def:	e8 bc d3 ff ff       	call   4021b0 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
  404df4:	be 01 00 00 00       	mov    $0x1,%esi
  404df9:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
  404dfe:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
  404e01:	e8 2a d3 ff ff       	call   402130 <calloc@plt>
    req->client_socket = client_socket;
  404e06:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
  404e0b:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
  404e0f:	48 89 ef             	mov    %rbp,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
  404e12:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
  404e17:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
  404e1c:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
  404e25:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
  404e2d:	44 89 6b 04          	mov    %r13d,0x4(%rbx)
	sqe->user_data = (unsigned long) data;
  404e31:	4c 89 63 20          	mov    %r12,0x20(%rbx)
	sqe->opcode = (__u8) op;
  404e35:	c7 03 01 00 00 00    	movl   $0x1,(%rbx)
	sqe->off = offset;
  404e3b:	48 c7 43 08 00 00 00 00 	movq   $0x0,0x8(%rbx)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
  404e43:	48 89 43 10          	mov    %rax,0x10(%rbx)
	sqe->len = len;
  404e47:	48 c7 43 18 01 00 00 00 	movq   $0x1,0x18(%rbx)
	sqe->buf_index = 0;
  404e4f:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->addr3 = 0;
  404e57:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
    io_uring_submit(ring);
  404e5b:	e8 60 d2 ff ff       	call   4020c0 <io_uring_submit@plt>
}
  404e60:	48 83 c4 08          	add    $0x8,%rsp
  404e64:	31 c0                	xor    %eax,%eax
  404e66:	5b                   	pop    %rbx
  404e67:	5d                   	pop    %rbp
  404e68:	41 5c                	pop    %r12
  404e6a:	41 5d                	pop    %r13
  404e6c:	c3                   	ret
  404e6d:	0f 1f 00             	nopl   (%rax)

0000000000404e70 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
  404e70:	41 56                	push   %r14
  404e72:	49 89 d6             	mov    %rdx,%r14
  404e75:	41 55                	push   %r13
  404e77:	49 89 fd             	mov    %rdi,%r13
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  404e7a:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
  404e7f:	41 54                	push   %r12
  404e81:	55                   	push   %rbp
  404e82:	53                   	push   %rbx
  404e83:	89 f3                	mov    %esi,%ebx
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  404e85:	e8 f6 f7 ff ff       	call   404680 <zh_malloc>
    unsigned long slen = strlen(str);
  404e8a:	4c 89 ef             	mov    %r13,%rdi
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  404e8d:	48 89 c5             	mov    %rax,%rbp
    unsigned long slen = strlen(str);
  404e90:	e8 0b d2 ff ff       	call   4020a0 <strlen@plt>
    req->client_socket = client_socket;
  404e95:	89 5d 08             	mov    %ebx,0x8(%rbp)
    req->iovec_count = 1;
  404e98:	c7 45 04 01 00 00 00 	movl   $0x1,0x4(%rbp)
    req->iov[0].iov_base = zh_malloc(slen);
  404e9f:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
  404ea2:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = zh_malloc(slen);
  404ea5:	e8 d6 f7 ff ff       	call   404680 <zh_malloc>
    req->iov[0].iov_len = slen;
  404eaa:	4c 89 65 18          	mov    %r12,0x18(%rbp)
  404eae:	4c 89 ee             	mov    %r13,%rsi
  404eb1:	4c 89 e2             	mov    %r12,%rdx
    req->iov[0].iov_base = zh_malloc(slen);
  404eb4:	48 89 45 10          	mov    %rax,0x10(%rbp)
  404eb8:	48 89 c7             	mov    %rax,%rdi
  404ebb:	e8 b0 d2 ff ff       	call   402170 <memcpy@plt>
}
  404ec0:	5b                   	pop    %rbx
    add_write_request(req, ring);
  404ec1:	4c 89 f6             	mov    %r14,%rsi
  404ec4:	48 89 ef             	mov    %rbp,%rdi
}
  404ec7:	5d                   	pop    %rbp
  404ec8:	41 5c                	pop    %r12
  404eca:	41 5d                	pop    %r13
  404ecc:	41 5e                	pop    %r14
    add_write_request(req, ring);
  404ece:	e9 2d fe ff ff       	jmp    404d00 <add_write_request>
  404ed3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  404ede:	66 90                	xchg   %ax,%ax

0000000000404ee0 <handle_unimplemented_method>:
    _send_static_string_content(unimplemented_content, client_socket, ring);
  404ee0:	48 c7 c0 18 a0 40 00 	mov    $0x40a018,%rax
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
  404ee7:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
  404eea:	89 fe                	mov    %edi,%esi
  404eec:	48 8b 38             	mov    (%rax),%rdi
  404eef:	e9 7c ff ff ff       	jmp    404e70 <_send_static_string_content>
  404ef4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  404eff:	90                   	nop

0000000000404f00 <handle_http_404>:
    _send_static_string_content(http_404_content, client_socket, ring);
  404f00:	48 c7 c0 10 a0 40 00 	mov    $0x40a010,%rax
void handle_http_404(int client_socket, struct io_uring *ring) {
  404f07:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
  404f0a:	89 fe                	mov    %edi,%esi
  404f0c:	48 8b 38             	mov    (%rax),%rdi
  404f0f:	e9 5c ff ff ff       	jmp    404e70 <_send_static_string_content>
  404f14:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  404f1f:	90                   	nop

0000000000404f20 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
  404f20:	41 56                	push   %r14
  404f22:	41 55                	push   %r13
  404f24:	49 89 d5             	mov    %rdx,%r13
  404f27:	41 54                	push   %r12
  404f29:	49 89 fc             	mov    %rdi,%r12
  404f2c:	55                   	push   %rbp
  404f2d:	89 f5                	mov    %esi,%ebp
  404f2f:	53                   	push   %rbx
  404f30:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
  404f37:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  404f40:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
  404f48:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
  404f4a:	e8 51 d1 ff ff       	call   4020a0 <strlen@plt>
  404f4f:	41 80 7c 04 ff 2f    	cmpb   $0x2f,-0x1(%r12,%rax,1)
  404f55:	48 89 c3             	mov    %rax,%rbx
  404f58:	0f 84 b2 00 00 00    	je     405010 <handle_get_method+0xf0>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404f5e:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  404f63:	4c 89 e6             	mov    %r12,%rsi
  404f66:	48 8d 53 01          	lea    0x1(%rbx),%rdx
  404f6a:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  404f6f:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
  404f77:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404f7f:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  404f8a:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  404f92:	e8 b9 d1 ff ff       	call   402150 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
  404f97:	48 89 e6             	mov    %rsp,%rsi
  404f9a:	4c 89 f7             	mov    %r14,%rdi
  404f9d:	e8 be d1 ff ff       	call   402160 <stat@plt>
  404fa2:	83 f8 ff             	cmp    $0xffffffff,%eax
  404fa5:	0f 84 cf 00 00 00    	je     40507a <handle_get_method+0x15a>
        if (S_ISREG(path_stat.st_mode)) {
  404fab:	8b 44 24 18          	mov    0x18(%rsp),%eax
  404faf:	25 00 f0 00 00       	and    $0xf000,%eax
  404fb4:	3d 00 80 00 00       	cmp    $0x8000,%eax
  404fb9:	0f 84 e9 00 00 00    	je     4050a8 <handle_get_method+0x188>
            handle_http_404(client_socket, ring);
  404fbf:	4c 89 ee             	mov    %r13,%rsi
  404fc2:	89 ef                	mov    %ebp,%edi
  404fc4:	e8 37 ff ff ff       	call   404f00 <handle_http_404>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  404fc9:	4c 89 f2             	mov    %r14,%rdx
  404fcc:	bf 01 00 00 00       	mov    $0x1,%edi
  404fd1:	31 c0                	xor    %eax,%eax
  404fd3:	48 8d 35 6d 21 00 00 	lea    0x216d(%rip),%rsi        # 407147 <_IO_stdin_used+0x147>
  404fda:	e8 11 d2 ff ff       	call   4021f0 <__printf_chk@plt>
}
  404fdf:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
  404fe7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  404ff0:	0f 85 17 01 00 00    	jne    40510d <handle_get_method+0x1ed>
  404ff6:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
  404ffd:	5b                   	pop    %rbx
  404ffe:	5d                   	pop    %rbp
  404fff:	41 5c                	pop    %r12
  405001:	41 5d                	pop    %r13
  405003:	41 5e                	pop    %r14
  405005:	c3                   	ret
  405006:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  405010:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  405015:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
  40501d:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  405022:	4c 89 e6             	mov    %r12,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  405025:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  40502d:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  405030:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  405038:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  405043:	e8 08 d1 ff ff       	call   402150 <__memcpy_chk@plt>
  405048:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  40504d:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
  405052:	48 8d 35 b9 20 00 00 	lea    0x20b9(%rip),%rsi        # 407112 <_IO_stdin_used+0x112>
  405059:	48 29 d9             	sub    %rbx,%rcx
  40505c:	ba 0b 00 00 00       	mov    $0xb,%edx
  405061:	e8 ea d0 ff ff       	call   402150 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
  405066:	48 89 e6             	mov    %rsp,%rsi
  405069:	4c 89 f7             	mov    %r14,%rdi
  40506c:	e8 ef d0 ff ff       	call   402160 <stat@plt>
  405071:	83 f8 ff             	cmp    $0xffffffff,%eax
  405074:	0f 85 31 ff ff ff    	jne    404fab <handle_get_method+0x8b>
  40507a:	4c 89 e1             	mov    %r12,%rcx
  40507d:	4c 89 f2             	mov    %r14,%rdx
  405080:	48 8d 35 96 20 00 00 	lea    0x2096(%rip),%rsi        # 40711d <_IO_stdin_used+0x11d>
  405087:	31 c0                	xor    %eax,%eax
  405089:	bf 01 00 00 00       	mov    $0x1,%edi
  40508e:	e8 5d d1 ff ff       	call   4021f0 <__printf_chk@plt>
        handle_http_404(client_socket, ring);
  405093:	4c 89 ee             	mov    %r13,%rsi
  405096:	89 ef                	mov    %ebp,%edi
  405098:	e8 63 fe ff ff       	call   404f00 <handle_http_404>
  40509d:	e9 3d ff ff ff       	jmp    404fdf <handle_get_method+0xbf>
  4050a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            struct Request *req = zh_malloc(sizeof(*req) + (sizeof(struct iovec) * 6));
  4050a8:	bf 70 00 00 00       	mov    $0x70,%edi
  4050ad:	e8 ce f5 ff ff       	call   404680 <zh_malloc>
            send_headers(final_path, path_stat.st_size, req->iov);
  4050b2:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
  4050b7:	4c 89 f7             	mov    %r14,%rdi
            req->client_socket = client_socket;
  4050ba:	89 68 08             	mov    %ebp,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
  4050bd:	48 8d 50 10          	lea    0x10(%rax),%rdx
            struct Request *req = zh_malloc(sizeof(*req) + (sizeof(struct iovec) * 6));
  4050c1:	49 89 c4             	mov    %rax,%r12
            req->iovec_count = 6;
  4050c4:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
  4050cb:	e8 20 f6 ff ff       	call   4046f0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
  4050d0:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
  4050d5:	49 8d 54 24 60       	lea    0x60(%r12),%rdx
  4050da:	4c 89 f7             	mov    %r14,%rdi
  4050dd:	e8 7e fb ff ff       	call   404c60 <copy_file_contents>
  4050e2:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
  4050e7:	4c 89 f2             	mov    %r14,%rdx
  4050ea:	31 c0                	xor    %eax,%eax
  4050ec:	48 8d 35 42 20 00 00 	lea    0x2042(%rip),%rsi        # 407135 <_IO_stdin_used+0x135>
  4050f3:	bf 01 00 00 00       	mov    $0x1,%edi
  4050f8:	e8 f3 d0 ff ff       	call   4021f0 <__printf_chk@plt>
            add_write_request(req, ring);
  4050fd:	4c 89 ee             	mov    %r13,%rsi
  405100:	4c 89 e7             	mov    %r12,%rdi
  405103:	e8 f8 fb ff ff       	call   404d00 <add_write_request>
  405108:	e9 d2 fe ff ff       	jmp    404fdf <handle_get_method+0xbf>
}
  40510d:	e8 9e cf ff ff       	call   4020b0 <__stack_chk_fail@plt>
  405112:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40511d:	0f 1f 00             	nopl   (%rax)

0000000000405120 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
  405120:	41 57                	push   %r15
  405122:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
  405124:	4c 8d 35 81 1f 00 00 	lea    0x1f81(%rip),%r14        # 4070ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
  40512b:	41 55                	push   %r13
  40512d:	49 89 d5             	mov    %rdx,%r13
  405130:	41 54                	push   %r12
  405132:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
  405135:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
  405138:	55                   	push   %rbp
  405139:	48 83 ec 10          	sub    $0x10,%rsp
  40513d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  405146:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  40514b:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
  40514d:	49 89 e7             	mov    %rsp,%r15
  405150:	4c 89 fa             	mov    %r15,%rdx
  405153:	e8 b8 cf ff ff       	call   402110 <strtok_r@plt>
    strtolower(method);
  405158:	48 89 c7             	mov    %rax,%rdi
    method = strtok_r(method_buffer, " ", &saveptr);
  40515b:	48 89 c5             	mov    %rax,%rbp
    strtolower(method);
  40515e:	e8 dd f4 ff ff       	call   404640 <strtolower>
    path = strtok_r(NULL, " ", &saveptr);
  405163:	4c 89 f6             	mov    %r14,%rsi
  405166:	31 ff                	xor    %edi,%edi
  405168:	4c 89 fa             	mov    %r15,%rdx
  40516b:	e8 a0 cf ff ff       	call   402110 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
  405170:	48 8d 35 e3 1f 00 00 	lea    0x1fe3(%rip),%rsi        # 40715a <_IO_stdin_used+0x15a>
  405177:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
  40517a:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
  40517d:	e8 be cf ff ff       	call   402140 <strcmp@plt>
  405182:	85 c0                	test   %eax,%eax
  405184:	75 32                	jne    4051b8 <handle_http_method+0x98>
        handle_get_method(path, client_socket, ring);
  405186:	4c 89 ea             	mov    %r13,%rdx
  405189:	44 89 e6             	mov    %r12d,%esi
  40518c:	4c 89 f7             	mov    %r14,%rdi
  40518f:	e8 8c fd ff ff       	call   404f20 <handle_get_method>
}
  405194:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  405199:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4051a2:	75 21                	jne    4051c5 <handle_http_method+0xa5>
  4051a4:	48 83 c4 10          	add    $0x10,%rsp
  4051a8:	5d                   	pop    %rbp
  4051a9:	41 5c                	pop    %r12
  4051ab:	41 5d                	pop    %r13
  4051ad:	41 5e                	pop    %r14
  4051af:	41 5f                	pop    %r15
  4051b1:	c3                   	ret
  4051b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        handle_unimplemented_method(client_socket, ring);
  4051b8:	4c 89 ee             	mov    %r13,%rsi
  4051bb:	44 89 e7             	mov    %r12d,%edi
  4051be:	e8 1d fd ff ff       	call   404ee0 <handle_unimplemented_method>
}
  4051c3:	eb cf                	jmp    405194 <handle_http_method+0x74>
  4051c5:	e8 e6 ce ff ff       	call   4020b0 <__stack_chk_fail@plt>
  4051ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000004051d0 <get_line>:
    for (int i = 0; i < dest_sz; i++) {
  4051d0:	85 d2                	test   %edx,%edx
  4051d2:	7e 3c                	jle    405210 <get_line+0x40>
  4051d4:	8d 42 ff             	lea    -0x1(%rdx),%eax
  4051d7:	48 83 c7 01          	add    $0x1,%rdi
  4051db:	48 8d 54 06 01       	lea    0x1(%rsi,%rax,1),%rdx
  4051e0:	eb 13                	jmp    4051f5 <get_line+0x25>
  4051e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  4051e8:	48 83 c6 01          	add    $0x1,%rsi
  4051ec:	48 83 c7 01          	add    $0x1,%rdi
  4051f0:	48 39 d6             	cmp    %rdx,%rsi
  4051f3:	74 1b                	je     405210 <get_line+0x40>
        dest[i] = src[i];
  4051f5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
  4051f9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
  4051fb:	3c 0d                	cmp    $0xd,%al
  4051fd:	75 e9                	jne    4051e8 <get_line+0x18>
  4051ff:	80 3f 0a             	cmpb   $0xa,(%rdi)
  405202:	75 e4                	jne    4051e8 <get_line+0x18>
            dest[i] = '\0';
  405204:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
  405207:	31 c0                	xor    %eax,%eax
}
  405209:	c3                   	ret
  40520a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
  405210:	b8 01 00 00 00       	mov    $0x1,%eax
  405215:	c3                   	ret
  405216:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000405220 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
  405220:	41 54                	push   %r12
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  405222:	ba 00 04 00 00       	mov    $0x400,%edx
int handle_client_request(struct Request *req, struct io_uring *ring) {
  405227:	49 89 f4             	mov    %rsi,%r12
  40522a:	55                   	push   %rbp
  40522b:	53                   	push   %rbx
  40522c:	48 89 fb             	mov    %rdi,%rbx
  40522f:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  405236:	48 8b 7f 10          	mov    0x10(%rdi),%rdi
int handle_client_request(struct Request *req, struct io_uring *ring) {
  40523a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  405243:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
  40524b:	31 c0                	xor    %eax,%eax
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  40524d:	48 89 e5             	mov    %rsp,%rbp
  405250:	48 89 ee             	mov    %rbp,%rsi
  405253:	e8 78 ff ff ff       	call   4051d0 <get_line>
  405258:	85 c0                	test   %eax,%eax
  40525a:	75 2f                	jne    40528b <handle_client_request+0x6b>
    handle_http_method(http_request, req->client_socket, ring);
  40525c:	8b 73 08             	mov    0x8(%rbx),%esi
  40525f:	4c 89 e2             	mov    %r12,%rdx
  405262:	48 89 ef             	mov    %rbp,%rdi
  405265:	e8 b6 fe ff ff       	call   405120 <handle_http_method>
}
  40526a:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
  405272:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40527b:	75 38                	jne    4052b5 <handle_client_request+0x95>
  40527d:	48 81 c4 10 04 00 00 	add    $0x410,%rsp
  405284:	31 c0                	xor    %eax,%eax
  405286:	5b                   	pop    %rbx
  405287:	5d                   	pop    %rbp
  405288:	41 5c                	pop    %r12
  40528a:	c3                   	ret
        fprintf(stderr, "Malformed request\n");
  40528b:	48 8b 05 66 4d 00 00 	mov    0x4d66(%rip),%rax        # 409ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  405292:	ba 12 00 00 00       	mov    $0x12,%edx
  405297:	be 01 00 00 00       	mov    $0x1,%esi
  40529c:	48 8d 3d bb 1e 00 00 	lea    0x1ebb(%rip),%rdi        # 40715e <_IO_stdin_used+0x15e>
  4052a3:	48 8b 08             	mov    (%rax),%rcx
  4052a6:	e8 c5 cf ff ff       	call   402270 <fwrite@plt>
        exit(1);
  4052ab:	bf 01 00 00 00       	mov    $0x1,%edi
  4052b0:	e8 9b cf ff ff       	call   402250 <exit@plt>
}
  4052b5:	e8 f6 cd ff ff       	call   4020b0 <__stack_chk_fail@plt>
  4052ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000004052c0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
  4052c0:	55                   	push   %rbp
  4052c1:	66 48 0f 6e c2       	movq   %rdx,%xmm0
  4052c6:	66 48 0f 6e ce       	movq   %rsi,%xmm1
  4052cb:	48 89 cd             	mov    %rcx,%rbp
  4052ce:	53                   	push   %rbx
  4052cf:	89 f8                	mov    %edi,%eax
  4052d1:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
  4052d5:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  4052d9:	48 8b 11             	mov    (%rcx),%rdx
  4052dc:	8b 32                	mov    (%rdx),%esi
	unsigned int next = sq->sqe_tail + 1;
  4052de:	8b 59 44             	mov    0x44(%rcx),%ebx
	if (ring->flags & IORING_SETUP_SQE128)
  4052e1:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int next = sq->sqe_tail + 1;
  4052e7:	8d 53 01             	lea    0x1(%rbx),%edx
	if (next - head <= *sq->kring_entries) {
  4052ea:	89 d7                	mov    %edx,%edi
  4052ec:	29 f7                	sub    %esi,%edi
  4052ee:	48 8b 75 18          	mov    0x18(%rbp),%rsi
  4052f2:	3b 3e                	cmp    (%rsi),%edi
  4052f4:	0f 87 30 d0 ff ff    	ja     40232a <add_accept_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4052fa:	48 8b 75 10          	mov    0x10(%rbp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  4052fe:	c1 e9 0a             	shr    $0xa,%ecx
  struct Request *req = malloc(sizeof(*req));
  405301:	bf 10 00 00 00       	mov    $0x10,%edi
  405306:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405309:	23 1e                	and    (%rsi),%ebx
		sq->sqe_tail = next;
  40530b:	89 55 44             	mov    %edx,0x44(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40530e:	d3 e3                	shl    %cl,%ebx
  405310:	48 c1 e3 06          	shl    $0x6,%rbx
  405314:	48 03 5d 38          	add    0x38(%rbp),%rbx
	sqe->opcode = (__u8) op;
  405318:	c7 03 0d 00 00 00    	movl   $0xd,(%rbx)
	sqe->fd = fd;
  40531e:	89 43 04             	mov    %eax,0x4(%rbx)
	sqe->buf_index = 0;
  405321:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->len = len;
  405329:	48 c7 43 18 00 00 00 00 	movq   $0x0,0x18(%rbx)
	sqe->off = offset;
  405331:	0f 11 43 08          	movups %xmm0,0x8(%rbx)
	sqe->addr3 = 0;
  405335:	66 0f ef c0          	pxor   %xmm0,%xmm0
  405339:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
  40533d:	e8 6e ce ff ff       	call   4021b0 <malloc@plt>
  io_uring_submit(ring);
  405342:	48 89 ef             	mov    %rbp,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
  405345:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
  40534b:	48 89 43 20          	mov    %rax,0x20(%rbx)
}
  40534f:	48 83 c4 08          	add    $0x8,%rsp
  405353:	5b                   	pop    %rbx
  405354:	5d                   	pop    %rbp
  io_uring_submit(ring);
  405355:	e9 66 cd ff ff       	jmp    4020c0 <io_uring_submit@plt>
  40535a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000405360 <io_thread>:
void* io_thread(void *arg) {
  405360:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  405362:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
  405364:	41 56                	push   %r14
  405366:	41 55                	push   %r13
  405368:	41 54                	push   %r12
  40536a:	55                   	push   %rbp
  40536b:	48 89 fd             	mov    %rdi,%rbp
  40536e:	53                   	push   %rbx
  40536f:	48 81 ec 48 01 00 00 	sub    $0x148,%rsp
  struct io_uring ring = *data->ring;
  405376:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40537f:	48 89 84 24 38 01 00 00 	mov    %rax,0x138(%rsp)
  405387:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  40538b:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
  405390:	bf 00 01 00 00       	mov    $0x100,%edi
  405395:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
  405398:	f3 0f 6f 08          	movdqu (%rax),%xmm1
  40539c:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
  4053a1:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
  4053a6:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
  4053ab:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
  4053b0:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
  4053b8:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
  4053bd:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
  4053c5:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
  4053ca:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
  4053d2:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
  4053d7:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
  4053df:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
  4053e4:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
  4053ec:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
  4053f1:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
  4053f9:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
  405401:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
  405409:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
  405411:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
  405419:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
  405421:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
  405429:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
  405431:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
  405439:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
  405441:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
  405449:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
  405450:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  405458:	e8 23 cd ff ff       	call   402180 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
  40545d:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
  405461:	31 f6                	xor    %esi,%esi
  405463:	e8 28 ce ff ff       	call   402290 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
  405468:	31 d2                	xor    %edx,%edx
  40546a:	be 01 00 00 00       	mov    $0x1,%esi
  40546f:	bf 02 00 00 00       	mov    $0x2,%edi
  405474:	e8 87 ce ff ff       	call   402300 <socket@plt>
  405479:	89 44 24 0c          	mov    %eax,0xc(%rsp)
  if (sock == -1)
  40547d:	83 f8 ff             	cmp    $0xffffffff,%eax
  405480:	0f 84 09 05 00 00    	je     40598f <io_thread+0x62f>
  if (setsockopt(sock,
  405486:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  40548a:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
  40548f:	41 b8 04 00 00 00    	mov    $0x4,%r8d
  405495:	ba 02 00 00 00       	mov    $0x2,%edx
  40549a:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
  40549f:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
  4054a7:	e8 c4 cb ff ff       	call   402070 <setsockopt@plt>
  4054ac:	85 c0                	test   %eax,%eax
  4054ae:	0f 88 ca 04 00 00    	js     40597e <io_thread+0x61e>
  if (bind(sock,
  4054b4:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  return __builtin___memset_chk (__dest, __ch, __len,
  4054b8:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4054bc:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  4054c1:	ba 10 00 00 00       	mov    $0x10,%edx
  4054c6:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  srv_addr.sin_family = AF_INET;
  4054cb:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
  4054d3:	e8 28 cd ff ff       	call   402200 <bind@plt>
  4054d8:	85 c0                	test   %eax,%eax
  4054da:	0f 88 8d 04 00 00    	js     40596d <io_thread+0x60d>
  if (listen(sock, 10) < 0) {
  4054e0:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  4054e4:	be 0a 00 00 00       	mov    $0xa,%esi
  4054e9:	e8 d2 cc ff ff       	call   4021c0 <listen@plt>
  4054ee:	85 c0                	test   %eax,%eax
  4054f0:	0f 88 66 04 00 00    	js     40595c <io_thread+0x5fc>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4054f6:	ba db 18 00 00       	mov    $0x18db,%edx
  4054fb:	48 8d 35 a1 1c 00 00 	lea    0x1ca1(%rip),%rsi        # 4071a3 <_IO_stdin_used+0x1a3>
  405502:	bf 01 00 00 00       	mov    $0x1,%edi
  405507:	31 c0                	xor    %eax,%eax
  405509:	e8 e2 cc ff ff       	call   4021f0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  40550e:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
  405513:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  405517:	48 89 d9             	mov    %rbx,%rcx
  40551a:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
  40551f:	48 89 c6             	mov    %rax,%rsi
  405522:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  405527:	48 89 54 24 20       	mov    %rdx,0x20(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
  40552c:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  405534:	e8 87 fd ff ff       	call   4052c0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
  405539:	be 10 00 00 00       	mov    $0x10,%esi
  40553e:	bf 01 00 00 00       	mov    $0x1,%edi
  405543:	e8 e8 cb ff ff       	call   402130 <calloc@plt>
  iov->iov_base = zh_malloc(10);
  405548:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
  40554d:	49 89 c6             	mov    %rax,%r14
  405550:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  iov->iov_base = zh_malloc(10);
  405555:	e8 26 f1 ff ff       	call   404680 <zh_malloc>
  iov->iov_len = 10;
  40555a:	49 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%r14)
  iov->iov_base = zh_malloc(10);
  405562:	49 89 06             	mov    %rax,(%r14)
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  405565:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
  40556a:	8b 30                	mov    (%rax),%esi
	unsigned int next = sq->sqe_tail + 1;
  40556c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  405573:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  40557a:	8d 50 01             	lea    0x1(%rax),%edx
	if (next - head <= *sq->kring_entries) {
  40557d:	89 d7                	mov    %edx,%edi
  40557f:	29 f7                	sub    %esi,%edi
  405581:	48 8b 74 24 78       	mov    0x78(%rsp),%rsi
  405586:	3b 3e                	cmp    (%rsi),%edi
  405588:	0f 87 a6 cd ff ff    	ja     402334 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40558e:	48 8b 74 24 70       	mov    0x70(%rsp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  405593:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  405596:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
  40559a:	48 89 df             	mov    %rbx,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
  40559d:	83 e1 01             	and    $0x1,%ecx
  4055a0:	4c 8d 25 12 1c 00 00 	lea    0x1c12(%rip),%r12        # 4071b9 <_IO_stdin_used+0x1b9>
  4055a7:	4c 8d 2d 31 1c 00 00 	lea    0x1c31(%rip),%r13        # 4071df <_IO_stdin_used+0x1df>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4055ae:	23 06                	and    (%rsi),%eax
		sq->sqe_tail = next;
  4055b0:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
  4055b7:	48 8d 75 60          	lea    0x60(%rbp),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
  4055bb:	8b 55 60             	mov    0x60(%rbp),%edx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4055be:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
  4055c0:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
  4055c5:	48 c1 e0 06          	shl    $0x6,%rax
  4055c9:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
  4055d1:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
  4055d7:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
  4055da:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
  4055e2:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
  4055e6:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
  4055ee:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  4055f6:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
  4055fa:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
  4055fe:	e8 bd ca ff ff       	call   4020c0 <io_uring_submit@plt>
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
  405603:	48 8d 44 24 38       	lea    0x38(%rsp),%rax
  while (data->running == 1) {
  405608:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
  40560c:	48 89 04 24          	mov    %rax,(%rsp)
  405610:	0f 85 a6 01 00 00    	jne    4057bc <io_thread+0x45c>
  405616:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  405620:	4c 89 e7             	mov    %r12,%rdi
  405623:	e8 38 ca ff ff       	call   402060 <puts@plt>
	unsigned mask = *ring->cq.kring_mask;
  405628:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
	if (ring->flags & IORING_SETUP_CQE32)
  405630:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = *ring->cq.kring_mask;
  405637:	8b 30                	mov    (%rax),%esi
	if (ring->flags & IORING_SETUP_CQE32)
  405639:	c1 e9 0b             	shr    $0xb,%ecx
  40563c:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
  40563f:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
  405647:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
  405649:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
  405651:	8b 17                	mov    (%rdi),%edx
		if (!available)
  405653:	39 d0                	cmp    %edx,%eax
  405655:	74 39                	je     405690 <io_thread+0x330>
		cqe = &ring->cq.cqes[(head & mask) << shift];
  405657:	89 f0                	mov    %esi,%eax
  405659:	21 d0                	and    %edx,%eax
  40565b:	d3 e0                	shl    %cl,%eax
  40565d:	48 c1 e0 04          	shl    $0x4,%rax
  405661:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
  405669:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
  405671:	0f 85 81 01 00 00    	jne    4057f8 <io_thread+0x498>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
  405677:	4c 8b 00             	mov    (%rax),%r8
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
  40567a:	49 83 f8 ff          	cmp    $0xffffffffffffffff,%r8
  40567e:	0f 85 9c 02 00 00    	jne    405920 <io_thread+0x5c0>
			if (cqe->res < 0)
  405684:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  405687:	83 c2 01             	add    $0x1,%edx
  40568a:	89 17                	mov    %edx,(%rdi)
			if (!err)
  40568c:	85 c0                	test   %eax,%eax
  40568e:	79 af                	jns    40563f <io_thread+0x2df>
	*cqe_ptr = cqe;
  405690:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
  405699:	48 8b 34 24          	mov    (%rsp),%rsi
  40569d:	45 31 c0             	xor    %r8d,%r8d
  4056a0:	31 d2                	xor    %edx,%edx
  4056a2:	b9 01 00 00 00       	mov    $0x1,%ecx
  4056a7:	48 89 df             	mov    %rbx,%rdi
  4056aa:	e8 31 cb ff ff       	call   4021e0 <__io_uring_get_cqe@plt>
  4056af:	41 89 c6             	mov    %eax,%r14d
      if (cqe->user_data == 1) {
  4056b2:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  4056b7:	48 83 38 01          	cmpq   $0x1,(%rax)
  4056bb:	0f 84 8f 02 00 00    	je     405950 <io_thread+0x5f0>
  4056c1:	4c 89 ef             	mov    %r13,%rdi
  4056c4:	e8 97 c9 ff ff       	call   402060 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
  4056c9:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
  4056ce:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
  4056d1:	45 85 f6             	test   %r14d,%r14d
  4056d4:	79 11                	jns    4056e7 <io_thread+0x387>
          fatal_error("io_uring_wait_cqe");
  4056d6:	48 8d 3d 19 1b 00 00 	lea    0x1b19(%rip),%rdi        # 4071f6 <_IO_stdin_used+0x1f6>
  4056dd:	e8 3e ef ff ff       	call   404620 <fatal_error>
      if (cqe->res < 0) {
  4056e2:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
  4056e7:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
  4056ea:	45 8b 07             	mov    (%r15),%r8d
      if (cqe->res < 0) {
  4056ed:	85 c0                	test   %eax,%eax
  4056ef:	0f 88 ab 02 00 00    	js     4059a0 <io_thread+0x640>
      switch (req->event_type) {
  4056f5:	41 83 f8 01          	cmp    $0x1,%r8d
  4056f9:	0f 84 31 01 00 00    	je     405830 <io_thread+0x4d0>
  4056ff:	41 83 f8 02          	cmp    $0x2,%r8d
  405703:	0f 84 9f 01 00 00    	je     4058a8 <io_thread+0x548>
  405709:	45 85 c0             	test   %r8d,%r8d
  40570c:	0f 84 5e 01 00 00    	je     405870 <io_thread+0x510>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  405712:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  40571a:	8b 02                	mov    (%rdx),%eax
  40571c:	83 c0 01             	add    $0x1,%eax
  40571f:	89 02                	mov    %eax,(%rdx)
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  405721:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
  405726:	8b 30                	mov    (%rax),%esi
	unsigned int next = sq->sqe_tail + 1;
  405728:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  40572f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  405736:	8d 50 01             	lea    0x1(%rax),%edx
	if (next - head <= *sq->kring_entries) {
  405739:	89 d7                	mov    %edx,%edi
  40573b:	29 f7                	sub    %esi,%edi
  40573d:	48 8b 74 24 78       	mov    0x78(%rsp),%rsi
  405742:	3b 3e                	cmp    (%rsi),%edi
  405744:	0f 87 ea cb ff ff    	ja     402334 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40574a:	48 8b 74 24 70       	mov    0x70(%rsp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  40574f:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  405752:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
  405756:	48 89 df             	mov    %rbx,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
  405759:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40575c:	23 06                	and    (%rsi),%eax
	sqe->addr = (unsigned long) addr;
  40575e:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
		sq->sqe_tail = next;
  405763:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40576a:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
  40576c:	8b 55 60             	mov    0x60(%rbp),%edx
  40576f:	48 c1 e0 06          	shl    $0x6,%rax
  405773:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->addr = (unsigned long) addr;
  40577b:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->user_data = (unsigned long) data;
  40577f:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
	sqe->opcode = (__u8) op;
  405784:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
  40578a:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
  40578d:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->len = len;
  405795:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
  40579d:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  4057a5:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
  4057a9:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
  4057ad:	e8 0e c9 ff ff       	call   4020c0 <io_uring_submit@plt>
  while (data->running == 1) {
  4057b2:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
  4057b6:	0f 84 64 fe ff ff    	je     405620 <io_thread+0x2c0>
  4057bc:	48 8d 3d 55 1a 00 00 	lea    0x1a55(%rip),%rdi        # 407218 <_IO_stdin_used+0x218>
  4057c3:	e8 98 c8 ff ff       	call   402060 <puts@plt>
}
  4057c8:	48 8b 84 24 38 01 00 00 	mov    0x138(%rsp),%rax
  4057d0:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4057d9:	0f 85 fc 01 00 00    	jne    4059db <io_thread+0x67b>
  4057df:	48 81 c4 48 01 00 00 	add    $0x148,%rsp
  4057e6:	31 c0                	xor    %eax,%eax
  4057e8:	5b                   	pop    %rbx
  4057e9:	5d                   	pop    %rbp
  4057ea:	41 5c                	pop    %r12
  4057ec:	41 5d                	pop    %r13
  4057ee:	41 5e                	pop    %r14
  4057f0:	41 5f                	pop    %r15
  4057f2:	c3                   	ret
  4057f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
  4057f8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
  4057fd:	48 85 c0             	test   %rax,%rax
  405800:	0f 84 93 fe ff ff    	je     405699 <io_thread+0x339>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
  405806:	4c 8b 00             	mov    (%rax),%r8
      if (cqe->user_data == 1) {
  405809:	49 83 f8 01          	cmp    $0x1,%r8
  40580d:	0f 84 1d 01 00 00    	je     405930 <io_thread+0x5d0>
  405813:	4c 89 ef             	mov    %r13,%rdi
  405816:	e8 45 c8 ff ff       	call   402060 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
  40581b:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
  405820:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
  405823:	e9 bf fe ff ff       	jmp    4056e7 <io_thread+0x387>
  405828:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
              if (!cqe->res) {
  405830:	85 c0                	test   %eax,%eax
  405832:	0f 85 b8 00 00 00    	jne    4058f0 <io_thread+0x590>
                  fprintf(stderr, "Empty request!\n");
  405838:	48 8b 05 b9 47 00 00 	mov    0x47b9(%rip),%rax        # 409ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  40583f:	ba 0f 00 00 00       	mov    $0xf,%edx
  405844:	be 01 00 00 00       	mov    $0x1,%esi
  405849:	48 8d 3d b8 19 00 00 	lea    0x19b8(%rip),%rdi        # 407208 <_IO_stdin_used+0x208>
  405850:	48 8b 08             	mov    (%rax),%rcx
  405853:	e8 18 ca ff ff       	call   402270 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
  405858:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  40585d:	0f 1f 00             	nopl   (%rax)
	if (cqe)
  405860:	48 85 c0             	test   %rax,%rax
  405863:	0f 84 b8 fe ff ff    	je     405721 <io_thread+0x3c1>
  405869:	e9 a4 fe ff ff       	jmp    405712 <io_thread+0x3b2>
  40586e:	66 90                	xchg   %ax,%ax
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  405870:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  405875:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  40587a:	48 89 d9             	mov    %rbx,%rcx
  40587d:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  405881:	e8 3a fa ff ff       	call   4052c0 <add_accept_request>
              add_read_request(cqe->res, &ring);
  405886:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  40588b:	48 89 de             	mov    %rbx,%rsi
  40588e:	8b 78 08             	mov    0x8(%rax),%edi
  405891:	e8 0a f5 ff ff       	call   404da0 <add_read_request>
              free(req);
  405896:	4c 89 ff             	mov    %r15,%rdi
  405899:	e8 92 c7 ff ff       	call   402030 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
  40589e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
  4058a3:	eb bb                	jmp    405860 <io_thread+0x500>
  4058a5:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
  4058a8:	41 8b 47 04          	mov    0x4(%r15),%eax
  4058ac:	45 31 f6             	xor    %r14d,%r14d
  4058af:	85 c0                	test   %eax,%eax
  4058b1:	7e 20                	jle    4058d3 <io_thread+0x573>
  4058b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  free(req->iov[i].iov_base);
  4058b8:	49 63 c6             	movslq %r14d,%rax
              for (int i = 0; i < req->iovec_count; i++) {
  4058bb:	41 83 c6 01          	add    $0x1,%r14d
                  free(req->iov[i].iov_base);
  4058bf:	48 c1 e0 04          	shl    $0x4,%rax
  4058c3:	4a 8b 7c 38 10       	mov    0x10(%rax,%r15,1),%rdi
  4058c8:	e8 63 c7 ff ff       	call   402030 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
  4058cd:	45 39 77 04          	cmp    %r14d,0x4(%r15)
  4058d1:	7f e5                	jg     4058b8 <io_thread+0x558>
              close(req->client_socket);
  4058d3:	41 8b 7f 08          	mov    0x8(%r15),%edi
  4058d7:	e8 24 c8 ff ff       	call   402100 <close@plt>
              free(req);
  4058dc:	4c 89 ff             	mov    %r15,%rdi
  4058df:	e8 4c c7 ff ff       	call   402030 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
  4058e4:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
  4058e9:	e9 72 ff ff ff       	jmp    405860 <io_thread+0x500>
  4058ee:	66 90                	xchg   %ax,%ax
              handle_client_request(req, &ring);
  4058f0:	48 89 de             	mov    %rbx,%rsi
  4058f3:	4c 89 ff             	mov    %r15,%rdi
  4058f6:	e8 25 f9 ff ff       	call   405220 <handle_client_request>
              free(req->iov[0].iov_base);
  4058fb:	49 8b 7f 10          	mov    0x10(%r15),%rdi
  4058ff:	e8 2c c7 ff ff       	call   402030 <free@plt>
              free(req);
  405904:	4c 89 ff             	mov    %r15,%rdi
  405907:	e8 24 c7 ff ff       	call   402030 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
  40590c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
  405911:	e9 4a ff ff ff       	jmp    405860 <io_thread+0x500>
  405916:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
  405920:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
      if (cqe->user_data == 1) {
  405925:	49 83 f8 01          	cmp    $0x1,%r8
  405929:	0f 85 e4 fe ff ff    	jne    405813 <io_thread+0x4b3>
  40592f:	90                   	nop
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  405930:	83 c2 01             	add    $0x1,%edx
  405933:	89 17                	mov    %edx,(%rdi)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  405935:	48 8d 3d 8f 18 00 00 	lea    0x188f(%rip),%rdi        # 4071cb <_IO_stdin_used+0x1cb>
  40593c:	e8 1f c7 ff ff       	call   402060 <puts@plt>
  405941:	e9 76 fe ff ff       	jmp    4057bc <io_thread+0x45c>
  405946:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  405950:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
  405958:	8b 17                	mov    (%rdi),%edx
  40595a:	eb d4                	jmp    405930 <io_thread+0x5d0>
    fatal_error("listen()");
  40595c:	48 8d 3d 37 18 00 00 	lea    0x1837(%rip),%rdi        # 40719a <_IO_stdin_used+0x19a>
  405963:	e8 b8 ec ff ff       	call   404620 <fatal_error>
  405968:	e9 89 fb ff ff       	jmp    4054f6 <io_thread+0x196>
      fatal_error("bind()");
  40596d:	48 8d 3d 1f 18 00 00 	lea    0x181f(%rip),%rdi        # 407193 <_IO_stdin_used+0x193>
  405974:	e8 a7 ec ff ff       	call   404620 <fatal_error>
  405979:	e9 62 fb ff ff       	jmp    4054e0 <io_thread+0x180>
      fatal_error("setsockopt(SO_REUSEADDR)");
  40597e:	48 8d 3d f5 17 00 00 	lea    0x17f5(%rip),%rdi        # 40717a <_IO_stdin_used+0x17a>
  405985:	e8 96 ec ff ff       	call   404620 <fatal_error>
  40598a:	e9 25 fb ff ff       	jmp    4054b4 <io_thread+0x154>
      fatal_error("socket()");
  40598f:	48 8d 3d db 17 00 00 	lea    0x17db(%rip),%rdi        # 407171 <_IO_stdin_used+0x171>
  405996:	e8 85 ec ff ff       	call   404620 <fatal_error>
  40599b:	e9 e6 fa ff ff       	jmp    405486 <io_thread+0x126>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
  4059a0:	f7 d8                	neg    %eax
  4059a2:	44 89 04 24          	mov    %r8d,(%rsp)
  4059a6:	89 c7                	mov    %eax,%edi
  4059a8:	e8 03 c9 ff ff       	call   4022b0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  4059ad:	44 8b 04 24          	mov    (%rsp),%r8d
  4059b1:	be 01 00 00 00       	mov    $0x1,%esi
  4059b6:	48 8d 15 33 1c 00 00 	lea    0x1c33(%rip),%rdx        # 4075f0 <_IO_stdin_used+0x5f0>
  4059bd:	48 89 c1             	mov    %rax,%rcx
  4059c0:	48 8b 05 31 46 00 00 	mov    0x4631(%rip),%rax        # 409ff8 <stderr@GLIBC_2.2.5>
  4059c7:	48 8b 38             	mov    (%rax),%rdi
  4059ca:	31 c0                	xor    %eax,%eax
  4059cc:	e8 af c8 ff ff       	call   402280 <__fprintf_chk@plt>
          exit(1);
  4059d1:	bf 01 00 00 00       	mov    $0x1,%edi
  4059d6:	e8 75 c8 ff ff       	call   402250 <exit@plt>
}
  4059db:	e8 d0 c6 ff ff       	call   4020b0 <__stack_chk_fail@plt>

00000000004059e0 <barriered_work_ingest>:
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
  4059e0:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
  4059e7:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
  4059ed:	85 c9                	test   %ecx,%ecx
  4059ef:	0f 8e ed 00 00 00    	jle    405ae2 <barriered_work_ingest+0x102>
int barriered_work_ingest(struct BarrierTask *data) {
  4059f5:	41 56                	push   %r14
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
  4059f7:	45 31 f6             	xor    %r14d,%r14d
int barriered_work_ingest(struct BarrierTask *data) {
  4059fa:	41 55                	push   %r13
  4059fc:	41 54                	push   %r12
  4059fe:	49 89 fc             	mov    %rdi,%r12
  405a01:	55                   	push   %rbp
  405a02:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
  405a03:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
  405a07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  405a10:	49 63 c6             	movslq %r14d,%rax
  405a13:	31 ed                	xor    %ebp,%ebp
  405a15:	4c 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%r13
  405a1d:	48 8b 04 c7          	mov    (%rdi,%rax,8),%rax
  405a21:	8b 10                	mov    (%rax),%edx
  405a23:	85 d2                	test   %edx,%edx
  405a25:	7e 25                	jle    405a4c <barriered_work_ingest+0x6c>
  405a27:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
  405a2b:	48 63 dd             	movslq %ebp,%rbx
  405a2e:	48 c1 e3 08          	shl    $0x8,%rbx
  405a32:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
  405a36:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
  405a3d:	74 21                	je     405a60 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
  405a3f:	83 c5 01             	add    $0x1,%ebp
  405a42:	39 d5                	cmp    %edx,%ebp
  405a44:	7c e5                	jl     405a2b <barriered_work_ingest+0x4b>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
  405a46:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
  405a4c:	41 83 c6 01          	add    $0x1,%r14d
  405a50:	41 39 ce             	cmp    %ecx,%r14d
  405a53:	7c bb                	jl     405a10 <barriered_work_ingest+0x30>
}
  405a55:	5b                   	pop    %rbx
  405a56:	31 c0                	xor    %eax,%eax
  405a58:	5d                   	pop    %rbp
  405a59:	41 5c                	pop    %r12
  405a5b:	41 5d                	pop    %r13
  405a5d:	41 5e                	pop    %r14
  405a5f:	c3                   	ret
        data->ingest_count++;
  405a60:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
  405a69:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
  405a70:	bf 04 00 00 00       	mov    $0x4,%edi
  405a75:	48 c1 e6 05          	shl    $0x5,%rsi
  405a79:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
  405a80:	48 83 c6 10          	add    $0x10,%rsi
  405a84:	e8 f7 c5 ff ff       	call   402080 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
  405a89:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
  405a91:	48 8b 40 50          	mov    0x50(%rax),%rax
  405a95:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
  405a99:	48 03 58 08          	add    0x8(%rax),%rbx
        data->thread->buffers[b]->buffer[x].available = 0;
  405a9d:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
  405aa7:	8b 83 94 00 00 00    	mov    0x94(%rbx),%eax
  405aad:	83 c0 01             	add    $0x1,%eax
  405ab0:	99                   	cltd
  405ab1:	f7 bb 90 00 00 00    	idivl  0x90(%rbx)
  405ab7:	89 93 94 00 00 00    	mov    %edx,0x94(%rbx)
        asm volatile ("sfence" ::: "memory");
  405abd:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
  405ac0:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
  405ac8:	83 c5 01             	add    $0x1,%ebp
  405acb:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
  405acf:	4a 8b 04 2f          	mov    (%rdi,%r13,1),%rax
  405ad3:	8b 10                	mov    (%rax),%edx
  405ad5:	39 d5                	cmp    %edx,%ebp
  405ad7:	0f 8c 4a ff ff ff    	jl     405a27 <barriered_work_ingest+0x47>
  405add:	e9 64 ff ff ff       	jmp    405a46 <barriered_work_ingest+0x66>
}
  405ae2:	31 c0                	xor    %eax,%eax
  405ae4:	c3                   	ret
  405ae5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000405af0 <barriered_thread>:
void* barriered_thread(void *arg) {
  405af0:	41 56                	push   %r14
  405af2:	41 55                	push   %r13
  int t = 0;
  405af4:	45 31 ed             	xor    %r13d,%r13d
void* barriered_thread(void *arg) {
  405af7:	41 54                	push   %r12
  int waiting = 0;
  405af9:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
  405afc:	55                   	push   %rbp
  405afd:	48 89 fd             	mov    %rdi,%rbp
  405b00:	53                   	push   %rbx
  while (data->running == 1) {
  405b01:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
  405b05:	0f 85 cf 01 00 00    	jne    405cda <barriered_thread+0x1ea>
    if (t >= data->task_count) {
  405b0b:	8b 45 40             	mov    0x40(%rbp),%eax
  405b0e:	66 90                	xchg   %ax,%ax
  405b10:	41 39 c5             	cmp    %eax,%r13d
  405b13:	7c 43                	jl     405b58 <barriered_thread+0x68>
      data->cycles++;
  405b15:	48 83 85 a8 00 00 00 01 	addq   $0x1,0xa8(%rbp)
      t = 0;
  405b1d:	45 31 ed             	xor    %r13d,%r13d
    for (; t < data->task_count; t++) {
  405b20:	85 c0                	test   %eax,%eax
  405b22:	7f 34                	jg     405b58 <barriered_thread+0x68>
  405b24:	e9 a7 01 00 00       	jmp    405cd0 <barriered_thread+0x1e0>
  405b29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
  405b30:	48 63 55 04          	movslq 0x4(%rbp),%rdx
  405b34:	48 8b 45 18          	mov    0x18(%rbp),%rax
  405b38:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
  405b3c:	48 8b 78 38          	mov    0x38(%rax),%rdi
  405b40:	48 01 df             	add    %rbx,%rdi
  405b43:	e8 98 fe ff ff       	call   4059e0 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
  405b48:	8b 45 40             	mov    0x40(%rbp),%eax
  405b4b:	41 83 c5 01          	add    $0x1,%r13d
  405b4f:	44 39 e8             	cmp    %r13d,%eax
  405b52:	0f 8e 78 01 00 00    	jle    405cd0 <barriered_thread+0x1e0>
      if (data->tasks[t].available == 1) {
  405b58:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  405b5c:	49 63 dd             	movslq %r13d,%rbx
  405b5f:	48 c1 e3 09          	shl    $0x9,%rbx
  405b63:	48 8d 34 1a          	lea    (%rdx,%rbx,1),%rsi
  405b67:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
  405b6e:	75 c0                	jne    405b30 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
  405b70:	44 8b 55 28          	mov    0x28(%rbp),%r10d
  405b74:	83 e8 01             	sub    $0x1,%eax
  405b77:	41 8d 4d ff          	lea    -0x1(%r13),%ecx
  405b7b:	45 85 ed             	test   %r13d,%r13d
  405b7e:	0f 4f c1             	cmovg  %ecx,%eax
  405b81:	45 85 d2             	test   %r10d,%r10d
  405b84:	0f 8e 16 02 00 00    	jle    405da0 <barriered_thread+0x2b0>
  405b8a:	48 8b 55 18          	mov    0x18(%rbp),%rdx
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  405b8e:	48 63 c8             	movslq %eax,%rcx
        int arrived = 0; 
  405b91:	45 31 f6             	xor    %r14d,%r14d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  405b94:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
  405b9b:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
  405ba2:	41 8d 72 ff          	lea    -0x1(%r10),%esi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  405ba6:	48 c1 e1 09          	shl    $0x9,%rcx
  405baa:	48 8d 42 08          	lea    0x8(%rdx),%rax
  405bae:	48 8d 3c f0          	lea    (%rax,%rsi,8),%rdi
        int prearrive = 0; 
  405bb2:	31 f6                	xor    %esi,%esi
  405bb4:	eb 0e                	jmp    405bc4 <barriered_thread+0xd4>
  405bb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  405bc0:	48 83 c0 08          	add    $0x8,%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  405bc4:	48 8b 12             	mov    (%rdx),%rdx
  405bc7:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
  405bcb:	49 01 cb             	add    %rcx,%r11
  405bce:	4c 89 da             	mov    %r11,%rdx
            arrived++;
  405bd1:	45 31 db             	xor    %r11d,%r11d
  405bd4:	44 3b 8a 80 00 00 00 	cmp    0x80(%rdx),%r9d
  405bdb:	41 0f 94 c3          	sete   %r11b
  405bdf:	45 01 de             	add    %r11d,%r14d
            prearrive++;
  405be2:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
  405be9:	0f 94 c2             	sete   %dl
  405bec:	0f b6 d2             	movzbl %dl,%edx
  405bef:	01 d6                	add    %edx,%esi
        for (int thread = 0 ; thread < data->thread_count; thread++) {
  405bf1:	48 89 c2             	mov    %rax,%rdx
  405bf4:	48 39 c7             	cmp    %rax,%rdi
  405bf7:	75 c7                	jne    405bc0 <barriered_thread+0xd0>
        if (prearrive == 0 || prearrive == data->thread_count) {
  405bf9:	85 f6                	test   %esi,%esi
  405bfb:	0f 84 e7 00 00 00    	je     405ce8 <barriered_thread+0x1f8>
  405c01:	41 39 f2             	cmp    %esi,%r10d
  405c04:	0f 84 de 00 00 00    	je     405ce8 <barriered_thread+0x1f8>
        if (arrived == 0 || arrived == data->thread_count) {
  405c0a:	45 85 f6             	test   %r14d,%r14d
  405c0d:	74 0a                	je     405c19 <barriered_thread+0x129>
  405c0f:	44 39 75 28          	cmp    %r14d,0x28(%rbp)
  405c13:	0f 85 99 01 00 00    	jne    405db2 <barriered_thread+0x2c2>
  405c19:	48 8b 55 38          	mov    0x38(%rbp),%rdx
          data->tasks[t].prearrive++;
  405c1d:	48 01 da             	add    %rbx,%rdx
  405c20:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
  405c27:	45 85 ed             	test   %r13d,%r13d
  405c2a:	75 14                	jne    405c40 <barriered_thread+0x150>
  405c2c:	48 8b b5 80 00 00 00 	mov    0x80(%rbp),%rsi
  405c33:	48 3b b5 88 00 00 00 	cmp    0x88(%rbp),%rsi
  405c3a:	0f 8c 38 01 00 00    	jl     405d78 <barriered_thread+0x288>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
  405c40:	48 63 4d 04          	movslq 0x4(%rbp),%rcx
  405c44:	48 8b 45 18          	mov    0x18(%rbp),%rax
          data->tasks[t].available = 0;
  405c48:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
  405c52:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
  405c56:	48 8b 78 38          	mov    0x38(%rax),%rdi
  405c5a:	48 01 df             	add    %rbx,%rdi
  405c5d:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  405c63:	8b 45 40             	mov    0x40(%rbp),%eax
          data->tasks[t].arrived++;
  405c66:	48 03 5d 38          	add    0x38(%rbp),%rbx
  405c6a:	83 83 80 00 00 00 01 	addl   $0x1,0x80(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  405c71:	83 e8 01             	sub    $0x1,%eax
          data->iteration_count++;
  405c74:	48 83 45 78 01       	addq   $0x1,0x78(%rbp)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  405c79:	44 39 e8             	cmp    %r13d,%eax
  405c7c:	0f 84 be 00 00 00    	je     405d40 <barriered_thread+0x250>
          asm volatile ("sfence" ::: "memory");
  405c82:	0f ae f8             	sfence
          if (waiting == 0) {
  405c85:	45 85 e4             	test   %r12d,%r12d
  405c88:	0f 85 ba fe ff ff    	jne    405b48 <barriered_thread+0x58>
            data->task_snapshot[data->task_timestamp_count].task = t;
  405c8e:	48 8b 85 98 00 00 00 	mov    0x98(%rbp),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
  405c95:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
  405c9a:	41 bc 01 00 00 00    	mov    $0x1,%r12d
            data->task_snapshot[data->task_timestamp_count].task = t;
  405ca0:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  405ca4:	48 8b 85 90 00 00 00 	mov    0x90(%rbp),%rax
  405cab:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
  405caf:	44 89 6e 20          	mov    %r13d,0x20(%rsi)
    for (; t < data->task_count; t++) {
  405cb3:	41 83 c5 01          	add    $0x1,%r13d
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
  405cb7:	e8 c4 c3 ff ff       	call   402080 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
  405cbc:	8b 45 40             	mov    0x40(%rbp),%eax
  405cbf:	44 39 e8             	cmp    %r13d,%eax
  405cc2:	0f 8f 90 fe ff ff    	jg     405b58 <barriered_thread+0x68>
  405cc8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  while (data->running == 1) {
  405cd0:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
  405cd4:	0f 84 36 fe ff ff    	je     405b10 <barriered_thread+0x20>
}
  405cda:	5b                   	pop    %rbx
  405cdb:	31 c0                	xor    %eax,%eax
  405cdd:	5d                   	pop    %rbp
  405cde:	41 5c                	pop    %r12
  405ce0:	41 5d                	pop    %r13
  405ce2:	41 5e                	pop    %r14
  405ce4:	c3                   	ret
  405ce5:	0f 1f 00             	nopl   (%rax)
          if (waiting == 1) {
  405ce8:	41 83 fc 01          	cmp    $0x1,%r12d
  405cec:	0f 85 18 ff ff ff    	jne    405c0a <barriered_thread+0x11a>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
  405cf2:	48 8b 85 98 00 00 00 	mov    0x98(%rbp),%rax
  405cf9:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 0; 
  405cfe:	45 31 e4             	xor    %r12d,%r12d
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
  405d01:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  405d05:	48 8b 85 90 00 00 00 	mov    0x90(%rbp),%rax
  405d0c:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
  405d11:	e8 6a c3 ff ff       	call   402080 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
  405d16:	48 8b 85 98 00 00 00 	mov    0x98(%rbp),%rax
  405d1d:	48 83 c0 01          	add    $0x1,%rax
  405d21:	48 99                	cqto
  405d23:	48 f7 bd a0 00 00 00 	idivq  0xa0(%rbp)
  405d2a:	48 89 95 98 00 00 00 	mov    %rdx,0x98(%rbp)
            waiting = 0; 
  405d31:	e9 d4 fe ff ff       	jmp    405c0a <barriered_thread+0x11a>
  405d36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  405d40:	48 8b b5 80 00 00 00 	mov    0x80(%rbp),%rsi
  405d47:	48 3b b5 88 00 00 00 	cmp    0x88(%rbp),%rsi
  405d4e:	0f 8d 2e ff ff ff    	jge    405c82 <barriered_thread+0x192>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
  405d54:	48 c1 e6 04          	shl    $0x4,%rsi
  405d58:	bf 04 00 00 00       	mov    $0x4,%edi
  405d5d:	48 03 75 70          	add    0x70(%rbp),%rsi
  405d61:	e8 1a c3 ff ff       	call   402080 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
  405d66:	48 83 85 80 00 00 00 01 	addq   $0x1,0x80(%rbp)
  405d6e:	e9 0f ff ff ff       	jmp    405c82 <barriered_thread+0x192>
  405d73:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
  405d78:	48 c1 e6 04          	shl    $0x4,%rsi
  405d7c:	bf 04 00 00 00       	mov    $0x4,%edi
  405d81:	48 03 75 68          	add    0x68(%rbp),%rsi
  405d85:	e8 f6 c2 ff ff       	call   402080 <clock_gettime@plt>
          data->tasks[t].available = 0;
  405d8a:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  405d8e:	48 01 da             	add    %rbx,%rdx
  405d91:	e9 aa fe ff ff       	jmp    405c40 <barriered_thread+0x150>
  405d96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
  405da0:	41 83 fc 01          	cmp    $0x1,%r12d
  405da4:	0f 85 73 fe ff ff    	jne    405c1d <barriered_thread+0x12d>
        int arrived = 0; 
  405daa:	45 31 f6             	xor    %r14d,%r14d
  405dad:	e9 40 ff ff ff       	jmp    405cf2 <barriered_thread+0x202>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
  405db2:	48 63 55 04          	movslq 0x4(%rbp),%rdx
  405db6:	48 8b 45 18          	mov    0x18(%rbp),%rax
  405dba:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
  405dbe:	48 03 58 38          	add    0x38(%rax),%rbx
  405dc2:	48 89 df             	mov    %rbx,%rdi
  405dc5:	e8 16 fc ff ff       	call   4059e0 <barriered_work_ingest>
          break;
  405dca:	e9 32 fd ff ff       	jmp    405b01 <barriered_thread+0x11>
  405dcf:	90                   	nop

0000000000405dd0 <receive>:
int receive(struct BarrierTask *data) {
  405dd0:	41 57                	push   %r15
  405dd2:	41 56                	push   %r14
  405dd4:	41 55                	push   %r13
  405dd6:	41 54                	push   %r12
  405dd8:	55                   	push   %rbp
  405dd9:	53                   	push   %rbx
  405dda:	48 83 ec 18          	sub    $0x18,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  405dde:	44 8b bf 40 01 00 00 	mov    0x140(%rdi),%r15d
  405de5:	45 85 ff             	test   %r15d,%r15d
  405de8:	0f 8e 3f 01 00 00    	jle    405f2d <receive+0x15d>
    if (n == data->thread->real_thread_index) { continue; }
  405dee:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  405df5:	48 89 fe             	mov    %rdi,%rsi
  405df8:	45 31 f6             	xor    %r14d,%r14d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  405dfb:	45 31 e4             	xor    %r12d,%r12d
    if (n == data->thread->real_thread_index) { continue; }
  405dfe:	4c 63 68 08          	movslq 0x8(%rax),%r13
  405e02:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  405e07:	44 89 6c 24 04       	mov    %r13d,0x4(%rsp)
  405e0c:	0f 1f 40 00          	nopl   0x0(%rax)
  405e10:	44 39 64 24 04       	cmp    %r12d,0x4(%rsp)
  405e15:	0f 84 01 01 00 00    	je     405f1c <receive+0x14c>
    struct Data *me = data->mailboxes[n].lower;
  405e1b:	48 8b 86 70 01 00 00 	mov    0x170(%rsi),%rax
  405e22:	4e 8b 04 30          	mov    (%rax,%r14,1),%r8
    if (me->available_reading == 1) {
  405e26:	41 8b 80 00 02 00 00 	mov    0x200(%r8),%eax
  405e2d:	83 f8 01             	cmp    $0x1,%eax
  405e30:	74 12                	je     405e44 <receive+0x74>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
  405e32:	41 83 b8 18 03 00 00 02 	cmpl   $0x2,0x318(%r8)
  405e3a:	75 08                	jne    405e44 <receive+0x74>
  405e3c:	85 c0                	test   %eax,%eax
  405e3e:	0f 84 d8 00 00 00    	je     405f1c <receive+0x14c>
    for (int x = 0 ; x < me->messages_count ; x++) {
  405e44:	4d 8b 98 80 00 00 00 	mov    0x80(%r8),%r11
  405e4b:	4d 85 db             	test   %r11,%r11
  405e4e:	0f 8e 9c 00 00 00    	jle    405ef0 <receive+0x120>
      data->sends++;
  405e54:	48 8b be 78 01 00 00 	mov    0x178(%rsi),%rdi
      if (me->messages[x]->group == data->group) {
  405e5b:	49 8b 28             	mov    (%r8),%rbp
      me->received++;
  405e5e:	31 c9                	xor    %ecx,%ecx
  405e60:	31 d2                	xor    %edx,%edx
      data->n++;
  405e62:	4c 8b 96 08 01 00 00 	mov    0x108(%rsi),%r10
      me->received++;
  405e69:	4d 8b 88 10 03 00 00 	mov    0x310(%r8),%r9
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
  405e70:	48 63 5e 04          	movslq 0x4(%rsi),%rbx
  405e74:	48 8d 47 01          	lea    0x1(%rdi),%rax
      data->n++;
  405e78:	49 29 fa             	sub    %rdi,%r10
      me->received++;
  405e7b:	49 29 f9             	sub    %rdi,%r9
  405e7e:	eb 0f                	jmp    405e8f <receive+0xbf>
    for (int x = 0 ; x < me->messages_count ; x++) {
  405e80:	83 c1 01             	add    $0x1,%ecx
  405e83:	48 83 c0 01          	add    $0x1,%rax
  405e87:	48 63 d1             	movslq %ecx,%rdx
  405e8a:	4c 39 da             	cmp    %r11,%rdx
  405e8d:	7d 61                	jge    405ef0 <receive+0x120>
      data->n++;
  405e8f:	49 8d 3c 02          	lea    (%r10,%rax,1),%rdi
      if (me->messages[x]->group == data->group) {
  405e93:	48 8b 54 d5 00       	mov    0x0(%rbp,%rdx,8),%rdx
      data->sends++;
  405e98:	48 89 86 78 01 00 00 	mov    %rax,0x178(%rsi)
      data->n++;
  405e9f:	48 89 be 08 01 00 00 	mov    %rdi,0x108(%rsi)
      me->received++;
  405ea6:	49 8d 3c 01          	lea    (%r9,%rax,1),%rdi
  405eaa:	49 89 b8 10 03 00 00 	mov    %rdi,0x310(%r8)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
  405eb1:	48 39 5a 10          	cmp    %rbx,0x10(%rdx)
  405eb5:	75 c9                	jne    405e80 <receive+0xb0>
  405eb7:	4c 39 6a 08          	cmp    %r13,0x8(%rdx)
  405ebb:	75 c3                	jne    405e80 <receive+0xb0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
  405ebd:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  405ec2:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  405ec4:	bf 01 00 00 00       	mov    $0x1,%edi
  405ec9:	ba 01 00 00 00       	mov    $0x1,%edx
  405ece:	48 8d 35 43 17 00 00 	lea    0x1743(%rip),%rsi        # 407618 <_IO_stdin_used+0x618>
  405ed5:	48 63 40 04          	movslq 0x4(%rax),%rax
  405ed9:	4c 39 e8             	cmp    %r13,%rax
  405edc:	0f 94 c1             	sete   %cl
  405edf:	31 c0                	xor    %eax,%eax
  405ee1:	e8 0a c3 ff ff       	call   4021f0 <__printf_chk@plt>
        exit(1);
  405ee6:	bf 01 00 00 00       	mov    $0x1,%edi
  405eeb:	e8 60 c3 ff ff       	call   402250 <exit@plt>
    me->messages_count = 0;
  405ef0:	49 c7 80 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%r8)
      me->available_reading = 0;
  405efb:	41 c7 80 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%r8)
      me->finished_reading = 1;
  405f06:	41 c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r8)
      me->available_sending = 1;
  405f11:	41 c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r8)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  405f1c:	41 83 c4 01          	add    $0x1,%r12d
  405f20:	49 83 c6 38          	add    $0x38,%r14
  405f24:	45 39 fc             	cmp    %r15d,%r12d
  405f27:	0f 85 e3 fe ff ff    	jne    405e10 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
  405f2d:	0f ae f8             	sfence
}
  405f30:	48 83 c4 18          	add    $0x18,%rsp
  405f34:	31 c0                	xor    %eax,%eax
  405f36:	5b                   	pop    %rbx
  405f37:	5d                   	pop    %rbp
  405f38:	41 5c                	pop    %r12
  405f3a:	41 5d                	pop    %r13
  405f3c:	41 5e                	pop    %r14
  405f3e:	41 5f                	pop    %r15
  405f40:	c3                   	ret
  405f41:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  405f4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000405f50 <sendm>:
int sendm(struct BarrierTask *data) {
  405f50:	41 57                	push   %r15
  405f52:	41 56                	push   %r14
  405f54:	41 55                	push   %r13
  405f56:	41 54                	push   %r12
  405f58:	55                   	push   %rbp
  405f59:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  405f5a:	44 8b 8f 40 01 00 00 	mov    0x140(%rdi),%r9d
  405f61:	45 85 c9             	test   %r9d,%r9d
  405f64:	0f 8e ca 00 00 00    	jle    406034 <sendm+0xe4>
        if (n == data->thread->real_thread_index) { continue; }
  405f6a:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  405f71:	48 8d 9f 88 01 00 00 	lea    0x188(%rdi),%rbx
  405f78:	48 89 f9             	mov    %rdi,%rcx
  405f7b:	31 d2                	xor    %edx,%edx
  405f7d:	48 89 5c 24 e0       	mov    %rbx,-0x20(%rsp)
  405f82:	48 8d 9f 90 01 00 00 	lea    0x190(%rdi),%rbx
  405f89:	44 8b 78 08          	mov    0x8(%rax),%r15d
  405f8d:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  405f92:	31 c0                	xor    %eax,%eax
  405f94:	eb 3c                	jmp    405fd2 <sendm+0x82>
  405f96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          data->mailboxes[n].higher = them;
  405fa0:	4c 89 47 08          	mov    %r8,0x8(%rdi)
        if (them->messages_count > 0) {
  405fa4:	4c 89 c6             	mov    %r8,%rsi
          data->mailboxes[n].pending = NULL;
  405fa7:	48 c7 47 10 00 00 00 00 	movq   $0x0,0x10(%rdi)
        if (them->messages_count > 0) {
  405faf:	49 8b b8 80 00 00 00 	mov    0x80(%r8),%rdi
          them->available_sending = 1;
  405fb6:	41 c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r8)
        if (them->messages_count > 0) {
  405fc1:	48 85 ff             	test   %rdi,%rdi
  405fc4:	7e 4f                	jle    406015 <sendm+0xc5>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  405fc6:	83 c0 01             	add    $0x1,%eax
  405fc9:	48 83 c2 38          	add    $0x38,%rdx
  405fcd:	44 39 c8             	cmp    %r9d,%eax
  405fd0:	74 62                	je     406034 <sendm+0xe4>
        if (n == data->thread->real_thread_index) { continue; }
  405fd2:	41 39 c7             	cmp    %eax,%r15d
  405fd5:	74 ef                	je     405fc6 <sendm+0x76>
        struct Data *them = data->mailboxes[n].higher;
  405fd7:	48 8b b9 70 01 00 00 	mov    0x170(%rcx),%rdi
  405fde:	48 01 d7             	add    %rdx,%rdi
        if (data->mailboxes[n].pending != NULL) {
  405fe1:	4c 8b 47 10          	mov    0x10(%rdi),%r8
        struct Data *them = data->mailboxes[n].higher;
  405fe5:	48 8b 77 08          	mov    0x8(%rdi),%rsi
        if (data->mailboxes[n].pending != NULL) {
  405fe9:	4d 85 c0             	test   %r8,%r8
  405fec:	75 b2                	jne    405fa0 <sendm+0x50>
        if (them->messages_count > 0) {
  405fee:	48 8b be 80 00 00 00 	mov    0x80(%rsi),%rdi
  405ff5:	48 85 ff             	test   %rdi,%rdi
  405ff8:	7f cc                	jg     405fc6 <sendm+0x76>
        if (them->available_sending == 1) {
  405ffa:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
  406001:	41 83 f8 01          	cmp    $0x1,%r8d
  406005:	74 0e                	je     406015 <sendm+0xc5>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
  406007:	83 be 18 03 00 00 02 	cmpl   $0x2,0x318(%rsi)
  40600e:	75 05                	jne    406015 <sendm+0xc5>
  406010:	45 85 c0             	test   %r8d,%r8d
  406013:	74 b1                	je     405fc6 <sendm+0x76>
        if (data->sending == 1) {
  406015:	83 b9 80 01 00 00 01 	cmpl   $0x1,0x180(%rcx)
  40601c:	74 2a                	je     406048 <sendm+0xf8>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  40601e:	83 c0 01             	add    $0x1,%eax
  406021:	48 83 c2 38          	add    $0x38,%rdx
          them->available_receiving = 1;
  406025:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  40602f:	44 39 c8             	cmp    %r9d,%eax
  406032:	75 9e                	jne    405fd2 <sendm+0x82>
      asm volatile ("sfence" ::: "memory");
  406034:	0f ae f8             	sfence
}
  406037:	31 c0                	xor    %eax,%eax
  406039:	5b                   	pop    %rbx
  40603a:	5d                   	pop    %rbp
  40603b:	41 5c                	pop    %r12
  40603d:	41 5d                	pop    %r13
  40603f:	41 5e                	pop    %r14
  406041:	41 5f                	pop    %r15
  406043:	c3                   	ret
  406044:	0f 1f 40 00          	nopl   0x0(%rax)
          for (; them->messages_count < min;) {
  406048:	48 63 9e 88 00 00 00 	movslq 0x88(%rsi),%rbx
  40604f:	48 39 fb             	cmp    %rdi,%rbx
  406052:	0f 8e b0 00 00 00    	jle    406108 <sendm+0x1b8>
            them->messages[them->messages_count++] = data->message; 
  406058:	4c 8b 16             	mov    (%rsi),%r10
  40605b:	49 89 db             	mov    %rbx,%r11
  40605e:	48 8b a9 08 01 00 00 	mov    0x108(%rcx),%rbp
  406065:	49 29 fb             	sub    %rdi,%r11
  406068:	4c 8b b6 08 03 00 00 	mov    0x308(%rsi),%r14
  40606f:	4d 8d 24 da          	lea    (%r10,%rbx,8),%r12
  406073:	4c 3b 64 24 e0       	cmp    -0x20(%rsp),%r12
  406078:	4d 8d 04 fa          	lea    (%r10,%rdi,8),%r8
  40607c:	0f 96 44 24 f7       	setbe  -0x9(%rsp)
  406081:	4c 3b 44 24 e8       	cmp    -0x18(%rsp),%r8
  406086:	41 0f 93 c5          	setae  %r13b
  40608a:	44 0a 6c 24 f7       	or     -0x9(%rsp),%r13b
  40608f:	0f 84 8b 00 00 00    	je     406120 <sendm+0x1d0>
  406095:	4d 8d 6b ff          	lea    -0x1(%r11),%r13
  406099:	49 83 fd 02          	cmp    $0x2,%r13
  40609d:	0f 86 7d 00 00 00    	jbe    406120 <sendm+0x1d0>
  4060a3:	4c 8b a9 88 01 00 00 	mov    0x188(%rcx),%r13
  4060aa:	4d 89 dc             	mov    %r11,%r12
  4060ad:	49 d1 ec             	shr    %r12
  4060b0:	66 49 0f 6e c5       	movq   %r13,%xmm0
  4060b5:	49 c1 e4 04          	shl    $0x4,%r12
  4060b9:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
  4060bd:	4d 01 c4             	add    %r8,%r12
  4060c0:	41 0f 11 00          	movups %xmm0,(%r8)
          for (; them->messages_count < min;) {
  4060c4:	49 83 c0 10          	add    $0x10,%r8
  4060c8:	4d 39 c4             	cmp    %r8,%r12
  4060cb:	75 f3                	jne    4060c0 <sendm+0x170>
  4060cd:	4d 89 d8             	mov    %r11,%r8
  4060d0:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
  4060d4:	4c 01 c7             	add    %r8,%rdi
  4060d7:	4d 39 c3             	cmp    %r8,%r11
  4060da:	74 0b                	je     4060e7 <sendm+0x197>
            them->messages[them->messages_count++] = data->message; 
  4060dc:	4c 8b a9 88 01 00 00 	mov    0x188(%rcx),%r13
  4060e3:	4d 89 2c fa          	mov    %r13,(%r10,%rdi,8)
            data->n++;
  4060e7:	4c 01 dd             	add    %r11,%rbp
            them->sent++;
  4060ea:	4b 8d 3c 1e          	lea    (%r14,%r11,1),%rdi
            data->n++;
  4060ee:	48 89 a9 08 01 00 00 	mov    %rbp,0x108(%rcx)
            them->sent++;
  4060f5:	48 89 be 08 03 00 00 	mov    %rdi,0x308(%rsi)
  4060fc:	48 89 9e 80 00 00 00 	mov    %rbx,0x80(%rsi)
  406103:	4d 89 6c da f8       	mov    %r13,-0x8(%r10,%rbx,8)
          them->available_sending = 0;
  406108:	c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rsi)
  406112:	e9 07 ff ff ff       	jmp    40601e <sendm+0xce>
  406117:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
  406120:	4c 8b a9 88 01 00 00 	mov    0x188(%rcx),%r13
          for (; them->messages_count < min;) {
  406127:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
  40612b:	4d 89 68 f8          	mov    %r13,-0x8(%r8)
          for (; them->messages_count < min;) {
  40612f:	4d 39 c4             	cmp    %r8,%r12
  406132:	75 ec                	jne    406120 <sendm+0x1d0>
  406134:	eb b1                	jmp    4060e7 <sendm+0x197>
  406136:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000406140 <mailboxkind>:
  if (kind == 0) {
  406140:	85 f6                	test   %esi,%esi
  406142:	74 14                	je     406158 <mailboxkind+0x18>
  return NULL;
  406144:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
  406146:	83 fe 01             	cmp    $0x1,%esi
  406149:	74 05                	je     406150 <mailboxkind+0x10>
}
  40614b:	c3                   	ret
  40614c:	0f 1f 40 00          	nopl   0x0(%rax)
    return mailbox->higher;
  406150:	48 8b 47 08          	mov    0x8(%rdi),%rax
}
  406154:	c3                   	ret
  406155:	0f 1f 00             	nopl   (%rax)
    return mailbox->lower;
  406158:	48 8b 07             	mov    (%rdi),%rax
  40615b:	c3                   	ret
  40615c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000406160 <setmailboxkind>:
  if (kind == 0) {
  406160:	85 d2                	test   %edx,%edx
  406162:	75 0c                	jne    406170 <setmailboxkind+0x10>
    mailbox->lower = data;
  406164:	48 89 37             	mov    %rsi,(%rdi)
}
  406167:	31 c0                	xor    %eax,%eax
  406169:	c3                   	ret
  40616a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (kind == 1) {
  406170:	83 fa 01             	cmp    $0x1,%edx
  406173:	75 0b                	jne    406180 <setmailboxkind+0x20>
    mailbox->higher = data;
  406175:	48 89 77 08          	mov    %rsi,0x8(%rdi)
}
  406179:	31 c0                	xor    %eax,%eax
  40617b:	c3                   	ret
  40617c:	0f 1f 40 00          	nopl   0x0(%rax)
  if (kind == 2) {
  406180:	83 fa 02             	cmp    $0x2,%edx
  406183:	75 e2                	jne    406167 <setmailboxkind+0x7>
    mailbox->pending = data;
  406185:	48 89 77 10          	mov    %rsi,0x10(%rdi)
}
  406189:	31 c0                	xor    %eax,%eax
  40618b:	c3                   	ret
  40618c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000406190 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
  406190:	41 57                	push   %r15
  406192:	49 89 ff             	mov    %rdi,%r15
  406195:	41 56                	push   %r14
  406197:	41 55                	push   %r13
  406199:	41 54                	push   %r12
  40619b:	55                   	push   %rbp
  40619c:	53                   	push   %rbx
  40619d:	48 83 ec 68          	sub    $0x68,%rsp
        int t = data->task_index;
  4061a1:	8b 47 04             	mov    0x4(%rdi),%eax
  4061a4:	89 44 24 30          	mov    %eax,0x30(%rsp)
  if (data->thread_index == data->task_index) {
  4061a8:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
  4061ae:	74 48                	je     4061f8 <barriered_work+0x68>
    receive(data);
  4061b0:	e8 1b fc ff ff       	call   405dd0 <receive>
    while (data->scheduled == 1) {
  4061b5:	41 83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r15)
  4061bd:	75 16                	jne    4061d5 <barriered_work+0x45>
  4061bf:	90                   	nop
      data->n++;
  4061c0:	49 83 87 08 01 00 00 01 	addq   $0x1,0x108(%r15)
      asm volatile ("sfence" ::: "memory");
  4061c8:	0f ae f8             	sfence
    while (data->scheduled == 1) {
  4061cb:	41 83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r15)
  4061d3:	74 eb                	je     4061c0 <barriered_work+0x30>
    sendm(data);
  4061d5:	4c 89 ff             	mov    %r15,%rdi
  4061d8:	e8 73 fd ff ff       	call   405f50 <sendm>
  asm volatile ("sfence" ::: "memory");
  4061dd:	0f ae f8             	sfence
}
  4061e0:	48 83 c4 68          	add    $0x68,%rsp
  4061e4:	31 c0                	xor    %eax,%eax
  4061e6:	5b                   	pop    %rbx
  4061e7:	5d                   	pop    %rbp
  4061e8:	41 5c                	pop    %r12
  4061ea:	41 5d                	pop    %r13
  4061ec:	41 5e                	pop    %r14
  4061ee:	41 5f                	pop    %r15
  4061f0:	c3                   	ret
  4061f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      receive(data);
  4061f8:	e8 d3 fb ff ff       	call   405dd0 <receive>
      data->swap++;
  4061fd:	41 8b 87 98 01 00 00 	mov    0x198(%r15),%eax
  406204:	83 c0 01             	add    $0x1,%eax
  406207:	41 89 87 98 01 00 00 	mov    %eax,0x198(%r15)
        if (data->swap % 2 == 0) {
  40620e:	a8 01                	test   $0x1,%al
  406210:	0f 84 b3 02 00 00    	je     4064c9 <barriered_work+0x339>
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
  406216:	49 8b b7 28 01 00 00 	mov    0x128(%r15),%rsi
          int k = data->group;
  40621d:	41 8b 9f 94 01 00 00 	mov    0x194(%r15),%ebx
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
  406224:	8b 8e c4 00 00 00    	mov    0xc4(%rsi),%ecx
          int k = data->group;
  40622a:	89 5c 24 48          	mov    %ebx,0x48(%rsp)
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
  40622e:	85 c9                	test   %ecx,%ecx
  406230:	0f 8e bf 06 00 00    	jle    4068f5 <barriered_work+0x765>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  406236:	48 63 44 24 30       	movslq 0x30(%rsp),%rax
  40623b:	89 5c 24 28          	mov    %ebx,0x28(%rsp)
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
  40623f:	c7 44 24 38 00 00 00 00 	movl   $0x0,0x38(%rsp)
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  406247:	48 c1 e0 09          	shl    $0x9,%rax
  40624b:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
            int y = (k * data->thread->threads_per_group) + d;
  406250:	8b 44 24 48          	mov    0x48(%rsp),%eax
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  406254:	45 31 c0             	xor    %r8d,%r8d
            int y = (k * data->thread->threads_per_group) + d;
  406257:	0f af c1             	imul   %ecx,%eax
  40625a:	03 44 24 38          	add    0x38(%rsp),%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  40625e:	48 98                	cltq
  406260:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
  406264:	4c 8d 24 d2          	lea    (%rdx,%rdx,8),%r12
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
  406268:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  406270:	48 29 c2             	sub    %rax,%rdx
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  406273:	49 c1 e4 03          	shl    $0x3,%r12
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
  406277:	48 8d 04 d5 00 00 00 00 	lea    0x0(,%rdx,8),%rax
  40627f:	48 89 04 24          	mov    %rax,(%rsp)
  406283:	eb 10                	jmp    406295 <barriered_work+0x105>
  406285:	0f 1f 00             	nopl   (%rax)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  406288:	41 83 c0 01          	add    $0x1,%r8d
  40628c:	41 39 c8             	cmp    %ecx,%r8d
  40628f:	0f 8d 13 02 00 00    	jge    4064a8 <barriered_work+0x318>
              int b = (g * data->thread->threads_per_group) + m;
  406295:	8b 44 24 28          	mov    0x28(%rsp),%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  406299:	48 8b 7e 20          	mov    0x20(%rsi),%rdi
  40629d:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
              int b = (g * data->thread->threads_per_group) + m;
  4062a2:	0f af c1             	imul   %ecx,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  4062a5:	4a 8b 7c 27 38       	mov    0x38(%rdi,%r12,1),%rdi
  4062aa:	48 8b bc 1f 70 01 00 00 	mov    0x170(%rdi,%rbx,1),%rdi
              int b = (g * data->thread->threads_per_group) + m;
  4062b2:	44 01 c0             	add    %r8d,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  4062b5:	48 98                	cltq
  4062b7:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
  4062bf:	48 29 c2             	sub    %rax,%rdx
              if (kind == MAILBOX_FRIEND) {
  4062c2:	83 7c d7 30 01       	cmpl   $0x1,0x30(%rdi,%rdx,8)
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  4062c7:	4c 8d 2c d5 00 00 00 00 	lea    0x0(,%rdx,8),%r13
              if (kind == MAILBOX_FRIEND) {
  4062cf:	75 b7                	jne    406288 <barriered_work+0xf8>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
  4062d1:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
  4062d5:	41 8b 97 34 01 00 00 	mov    0x134(%r15),%edx
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
  4062dc:	4c 8d 34 c0          	lea    (%rax,%rax,8),%r14
  4062e0:	49 c1 e6 03          	shl    $0x3,%r14
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
  4062e4:	85 d2                	test   %edx,%edx
  4062e6:	7e a0                	jle    406288 <barriered_work+0xf8>
  4062e8:	4c 89 f0             	mov    %r14,%rax
  4062eb:	44 89 44 24 40       	mov    %r8d,0x40(%rsp)
  4062f0:	4d 89 ee             	mov    %r13,%r14
  4062f3:	31 db                	xor    %ebx,%ebx
  4062f5:	4d 89 fd             	mov    %r15,%r13
  4062f8:	89 d1                	mov    %edx,%ecx
  4062fa:	49 89 c7             	mov    %rax,%r15
  4062fd:	eb 0b                	jmp    40630a <barriered_work+0x17a>
  4062ff:	90                   	nop
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  406300:	49 8b b5 28 01 00 00 	mov    0x128(%r13),%rsi
  406307:	49 63 d8             	movslq %r8d,%rbx
                    int next_task = abs((nn + 1) % (data->thread_count));
  40630a:	44 8d 43 01          	lea    0x1(%rbx),%r8d
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  40630e:	48 c1 e3 09          	shl    $0x9,%rbx
  406312:	48 8b 3c 24          	mov    (%rsp),%rdi
                    int next_task = abs((nn + 1) % (data->thread_count));
  406316:	44 89 c0             	mov    %r8d,%eax
  406319:	44 89 44 24 58       	mov    %r8d,0x58(%rsp)
  40631e:	99                   	cltd
  40631f:	f7 f9                	idiv   %ecx
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  406321:	48 8b 46 20          	mov    0x20(%rsi),%rax
  406325:	4a 8b 44 38 38       	mov    0x38(%rax,%r15,1),%rax
  40632a:	be 01 00 00 00       	mov    $0x1,%esi
  40632f:	48 03 bc 18 70 01 00 00 	add    0x170(%rax,%rbx,1),%rdi
                    int next_task = abs((nn + 1) % (data->thread_count));
  406337:	48 63 ea             	movslq %edx,%rbp
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  40633a:	e8 01 fe ff ff       	call   406140 <mailboxkind>
                    struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  40633f:	48 8b 3c 24          	mov    (%rsp),%rdi
  406343:	31 f6                	xor    %esi,%esi
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  406345:	48 c1 e5 09          	shl    $0x9,%rbp
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  406349:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
                    struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  40634e:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
  406355:	48 8b 40 20          	mov    0x20(%rax),%rax
  406359:	4a 8b 44 38 38       	mov    0x38(%rax,%r15,1),%rax
  40635e:	48 03 bc 18 70 01 00 00 	add    0x170(%rax,%rbx,1),%rdi
  406366:	e8 d5 fd ff ff       	call   406140 <mailboxkind>
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  40636b:	31 f6                	xor    %esi,%esi
                    struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  40636d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
                    struct Mailbox* __a = &data->thread->all_threads[l2].tasks[l3].mailboxes[l4];
  406372:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  406379:	48 8b 40 20          	mov    0x20(%rax),%rax
  40637d:	4a 8b 44 20 38       	mov    0x38(%rax,%r12,1),%rax
  406382:	48 8b 8c 28 70 01 00 00 	mov    0x170(%rax,%rbp,1),%rcx
  40638a:	4c 01 f1             	add    %r14,%rcx
  40638d:	48 89 cf             	mov    %rcx,%rdi
  406390:	e8 ab fd ff ff       	call   406140 <mailboxkind>
                    struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  406395:	be 01 00 00 00       	mov    $0x1,%esi
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  40639a:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
                    struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  40639f:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
  4063a6:	48 8b 40 20          	mov    0x20(%rax),%rax
  4063aa:	4a 8b 44 20 38       	mov    0x38(%rax,%r12,1),%rax
  4063af:	48 8b 8c 28 70 01 00 00 	mov    0x170(%rax,%rbp,1),%rcx
  4063b7:	4c 01 f1             	add    %r14,%rcx
  4063ba:	48 89 cf             	mov    %rcx,%rdi
  4063bd:	e8 7e fd ff ff       	call   406140 <mailboxkind>
                    setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
  4063c2:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
                    struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  4063c7:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
                    setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
  4063cc:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
  4063d3:	48 8b 40 20          	mov    0x20(%rax),%rax
  4063d7:	4a 8b 44 20 38       	mov    0x38(%rax,%r12,1),%rax
  4063dc:	48 8b 94 28 70 01 00 00 	mov    0x170(%rax,%rbp,1),%rdx
  4063e4:	4c 01 f2             	add    %r14,%rdx
  4063e7:	48 89 d7             	mov    %rdx,%rdi
  4063ea:	31 d2                	xor    %edx,%edx
  4063ec:	e8 6f fd ff ff       	call   406160 <setmailboxkind>
                    setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest2, LOWER);
  4063f1:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
  4063f6:	48 8b 3c 24          	mov    (%rsp),%rdi
  4063fa:	31 d2                	xor    %edx,%edx
  4063fc:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
  406403:	48 8b 40 20          	mov    0x20(%rax),%rax
  406407:	4a 8b 44 38 38       	mov    0x38(%rax,%r15,1),%rax
  40640c:	48 03 bc 18 70 01 00 00 	add    0x170(%rax,%rbx,1),%rdi
  406414:	e8 47 fd ff ff       	call   406160 <setmailboxkind>
                    setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest, HIGHER);
  406419:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
  406420:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
  406425:	ba 01 00 00 00       	mov    $0x1,%edx
  40642a:	48 8b 3c 24          	mov    (%rsp),%rdi
  40642e:	48 8b 40 20          	mov    0x20(%rax),%rax
  406432:	4a 8b 44 38 38       	mov    0x38(%rax,%r15,1),%rax
  406437:	48 03 bc 18 70 01 00 00 	add    0x170(%rax,%rbx,1),%rdi
  40643f:	e8 1c fd ff ff       	call   406160 <setmailboxkind>
                    setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source2, HIGHER);
  406444:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  406449:	ba 01 00 00 00       	mov    $0x1,%edx
  40644e:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
  406455:	48 8b 40 20          	mov    0x20(%rax),%rax
  406459:	4a 8b 44 20 38       	mov    0x38(%rax,%r12,1),%rax
  40645e:	48 8b bc 28 70 01 00 00 	mov    0x170(%rax,%rbp,1),%rdi
  406466:	4c 01 f7             	add    %r14,%rdi
  406469:	e8 f2 fc ff ff       	call   406160 <setmailboxkind>
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
  40646e:	41 8b 8d 34 01 00 00 	mov    0x134(%r13),%ecx
  406475:	44 8b 44 24 58       	mov    0x58(%rsp),%r8d
  40647a:	41 39 c8             	cmp    %ecx,%r8d
  40647d:	0f 8c 7d fe ff ff    	jl     406300 <barriered_work+0x170>
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  406483:	49 8b b5 28 01 00 00 	mov    0x128(%r13),%rsi
  40648a:	44 8b 44 24 40       	mov    0x40(%rsp),%r8d
  40648f:	4d 89 ef             	mov    %r13,%r15
  406492:	8b 8e c4 00 00 00    	mov    0xc4(%rsi),%ecx
  406498:	41 83 c0 01          	add    $0x1,%r8d
  40649c:	41 39 c8             	cmp    %ecx,%r8d
  40649f:	0f 8c f0 fd ff ff    	jl     406295 <barriered_work+0x105>
  4064a5:	0f 1f 00             	nopl   (%rax)
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
  4064a8:	83 44 24 38 01       	addl   $0x1,0x38(%rsp)
  4064ad:	8b 44 24 38          	mov    0x38(%rsp),%eax
  4064b1:	39 c1                	cmp    %eax,%ecx
  4064b3:	0f 8e 3c 04 00 00    	jle    4068f5 <barriered_work+0x765>
            int g = data->group;
  4064b9:	41 8b 87 94 01 00 00 	mov    0x194(%r15),%eax
  4064c0:	89 44 24 28          	mov    %eax,0x28(%rsp)
  4064c4:	e9 87 fd ff ff       	jmp    406250 <barriered_work+0xc0>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
  4064c9:	41 8b 8f 40 01 00 00 	mov    0x140(%r15),%ecx
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
  4064d0:	49 8b b7 28 01 00 00 	mov    0x128(%r15),%rsi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
  4064d7:	85 c9                	test   %ecx,%ecx
  4064d9:	0f 8e 3e fd ff ff    	jle    40621d <barriered_work+0x8d>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
  4064df:	48 63 44 24 30       	movslq 0x30(%rsp),%rax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
  4064e4:	45 31 f6             	xor    %r14d,%r14d
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
  4064e7:	48 c1 e0 09          	shl    $0x9,%rax
  4064eb:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  4064f0:	eb 13                	jmp    406505 <barriered_work+0x375>
  4064f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
  4064f8:	41 83 c6 01          	add    $0x1,%r14d
  4064fc:	41 39 ce             	cmp    %ecx,%r14d
  4064ff:	0f 8d 18 fd ff ff    	jge    40621d <barriered_work+0x8d>
              int b = data->thread->real_thread_index;
  406505:	44 8b 66 08          	mov    0x8(%rsi),%r12d
              if (y == b) { continue; }
  406509:	45 39 f4             	cmp    %r14d,%r12d
  40650c:	74 ea                	je     4064f8 <barriered_work+0x368>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
  40650e:	4d 63 c4             	movslq %r12d,%r8
  406511:	48 8b 56 20          	mov    0x20(%rsi),%rdx
  406515:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
  40651a:	4d 63 de             	movslq %r14d,%r11
  40651d:	4b 8d 04 40          	lea    (%r8,%r8,2),%rax
  406521:	48 8d 2c c0          	lea    (%rax,%rax,8),%rbp
  406525:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
  40652d:	48 c1 e5 03          	shl    $0x3,%rbp
  406531:	4c 29 d8             	sub    %r11,%rax
  406534:	48 8b 54 2a 38       	mov    0x38(%rdx,%rbp,1),%rdx
  406539:	4c 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%r13
  406541:	48 8b 94 1a 70 01 00 00 	mov    0x170(%rdx,%rbx,1),%rdx
  406549:	83 7c c2 30 02       	cmpl   $0x2,0x30(%rdx,%rax,8)
  40654e:	75 a8                	jne    4064f8 <barriered_work+0x368>
                    int min = minf(b, y); 
  406550:	44 89 f6             	mov    %r14d,%esi
  406553:	44 89 e7             	mov    %r12d,%edi
  406556:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
  40655b:	4c 89 04 24          	mov    %r8,(%rsp)
  40655f:	e8 9c e0 ff ff       	call   404600 <minf>
                    int max = maxf(b, y); 
  406564:	44 89 f6             	mov    %r14d,%esi
  406567:	44 89 e7             	mov    %r12d,%edi
                    int min = minf(b, y); 
  40656a:	48 63 d8             	movslq %eax,%rbx
                    int max = maxf(b, y); 
  40656d:	e8 9e e0 ff ff       	call   404610 <maxf>
                    pthread_mutex_lock(&data->thread->swapmutex[max]);   
  406572:	48 98                	cltq
  406574:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  406578:	48 c1 e0 03          	shl    $0x3,%rax
  40657c:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  406581:	48 89 c7             	mov    %rax,%rdi
  406584:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  40658b:	48 03 b8 c8 00 00 00 	add    0xc8(%rax),%rdi
  406592:	e8 39 bd ff ff       	call   4022d0 <pthread_mutex_lock@plt>
                    pthread_mutex_lock(&data->thread->swapmutex[min]);   
  406597:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
  40659b:	48 c1 e0 03          	shl    $0x3,%rax
  40659f:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  4065a4:	48 89 c7             	mov    %rax,%rdi
  4065a7:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  4065ae:	48 03 b8 c8 00 00 00 	add    0xc8(%rax),%rdi
  4065b5:	e8 16 bd ff ff       	call   4022d0 <pthread_mutex_lock@plt>
                    for (int nn = 0; nn < data->thread_count; nn++) {
  4065ba:	41 8b 97 34 01 00 00 	mov    0x134(%r15),%edx
  4065c1:	4c 8b 04 24          	mov    (%rsp),%r8
  4065c5:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
  4065ca:	85 d2                	test   %edx,%edx
  4065cc:	0f 8e 06 04 00 00    	jle    4069d8 <barriered_work+0x848>
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  4065d2:	4b 8d 04 5b          	lea    (%r11,%r11,2),%rax
                    for (int nn = 0; nn < data->thread_count; nn++) {
  4065d6:	4c 89 5c 24 50       	mov    %r11,0x50(%rsp)
  4065db:	45 31 d2             	xor    %r10d,%r10d
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  4065de:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
                    for (int nn = 0; nn < data->thread_count; nn++) {
  4065e2:	4c 89 44 24 48       	mov    %r8,0x48(%rsp)
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  4065e7:	48 8d 1c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbx
  4065ef:	4a 8d 04 c5 00 00 00 00 	lea    0x0(,%r8,8),%rax
                    for (int nn = 0; nn < data->thread_count; nn++) {
  4065f7:	44 89 74 24 5c       	mov    %r14d,0x5c(%rsp)
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  4065fc:	4c 29 c0             	sub    %r8,%rax
                    for (int nn = 0; nn < data->thread_count; nn++) {
  4065ff:	48 89 2c 24          	mov    %rbp,(%rsp)
  406603:	45 89 d0             	mov    %r10d,%r8d
  406606:	41 89 d2             	mov    %edx,%r10d
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  406609:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  406611:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
                    for (int nn = 0; nn < data->thread_count; nn++) {
  406618:	49 89 f6             	mov    %rsi,%r14
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  40661b:	48 8b 40 20          	mov    0x20(%rax),%rax
  40661f:	48 8b 4c 28 38       	mov    0x38(%rax,%rbp,1),%rcx
                    for (int nn = 0; nn < data->thread_count; nn++) {
  406624:	48 89 dd             	mov    %rbx,%rbp
  406627:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
                      int next_task = abs((nn + 1) % data->thread_count);
  406630:	49 63 d8             	movslq %r8d,%rbx
  406633:	41 83 c0 01          	add    $0x1,%r8d
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  406637:	be 01 00 00 00       	mov    $0x1,%esi
                      int next_task = abs((nn + 1) % data->thread_count);
  40663c:	44 89 c0             	mov    %r8d,%eax
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  40663f:	48 c1 e3 09          	shl    $0x9,%rbx
                      int next_task = abs((nn + 1) % data->thread_count);
  406643:	44 89 44 24 58       	mov    %r8d,0x58(%rsp)
  406648:	99                   	cltd
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  406649:	48 8b bc 19 70 01 00 00 	mov    0x170(%rcx,%rbx,1),%rdi
                      int next_task = abs((nn + 1) % data->thread_count);
  406651:	41 f7 fa             	idiv   %r10d
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  406654:	4c 01 ef             	add    %r13,%rdi
                      int next_task = abs((nn + 1) % data->thread_count);
  406657:	4c 63 e2             	movslq %edx,%r12
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  40665a:	e8 e1 fa ff ff       	call   406140 <mailboxkind>
                      struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  40665f:	48 8b 34 24          	mov    (%rsp),%rsi
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  406663:	49 c1 e4 09          	shl    $0x9,%r12
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  406667:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
                      struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  40666c:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  406673:	48 8b 40 20          	mov    0x20(%rax),%rax
  406677:	48 8b 44 30 38       	mov    0x38(%rax,%rsi,1),%rax
  40667c:	31 f6                	xor    %esi,%esi
  40667e:	48 8b bc 18 70 01 00 00 	mov    0x170(%rax,%rbx,1),%rdi
  406686:	4c 01 ef             	add    %r13,%rdi
  406689:	e8 b2 fa ff ff       	call   406140 <mailboxkind>
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  40668e:	31 f6                	xor    %esi,%esi
                      struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  406690:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
                      struct Mailbox* __a = &data->thread->all_threads[l2].tasks[l3].mailboxes[l4];
  406695:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  40669c:	48 8b 40 20          	mov    0x20(%rax),%rax
  4066a0:	48 8b 44 28 38       	mov    0x38(%rax,%rbp,1),%rax
  4066a5:	4a 8b bc 20 70 01 00 00 	mov    0x170(%rax,%r12,1),%rdi
  4066ad:	4c 01 f7             	add    %r14,%rdi
  4066b0:	e8 8b fa ff ff       	call   406140 <mailboxkind>
                      struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  4066b5:	be 01 00 00 00       	mov    $0x1,%esi
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  4066ba:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
                      struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  4066bf:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  4066c6:	48 8b 40 20          	mov    0x20(%rax),%rax
  4066ca:	48 8b 44 28 38       	mov    0x38(%rax,%rbp,1),%rax
  4066cf:	4a 8b bc 20 70 01 00 00 	mov    0x170(%rax,%r12,1),%rdi
  4066d7:	4c 01 f7             	add    %r14,%rdi
  4066da:	e8 61 fa ff ff       	call   406140 <mailboxkind>
                      setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
  4066df:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
  4066e4:	31 d2                	xor    %edx,%edx
                      struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  4066e6:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
                      setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
  4066eb:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  4066f2:	48 8b 40 20          	mov    0x20(%rax),%rax
  4066f6:	48 8b 44 28 38       	mov    0x38(%rax,%rbp,1),%rax
  4066fb:	4a 8b bc 20 70 01 00 00 	mov    0x170(%rax,%r12,1),%rdi
  406703:	4c 01 f7             	add    %r14,%rdi
  406706:	e8 55 fa ff ff       	call   406160 <setmailboxkind>
                      setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest2, LOWER);
  40670b:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  406712:	48 8b 34 24          	mov    (%rsp),%rsi
  406716:	31 d2                	xor    %edx,%edx
  406718:	48 8b 40 20          	mov    0x20(%rax),%rax
  40671c:	48 8b 44 30 38       	mov    0x38(%rax,%rsi,1),%rax
  406721:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
  406726:	48 8b bc 18 70 01 00 00 	mov    0x170(%rax,%rbx,1),%rdi
  40672e:	4c 01 ef             	add    %r13,%rdi
  406731:	e8 2a fa ff ff       	call   406160 <setmailboxkind>
                      setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest, HIGHER);
  406736:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  40673d:	48 8b 34 24          	mov    (%rsp),%rsi
  406741:	ba 01 00 00 00       	mov    $0x1,%edx
  406746:	48 8b 40 20          	mov    0x20(%rax),%rax
  40674a:	48 8b 44 30 38       	mov    0x38(%rax,%rsi,1),%rax
  40674f:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
  406754:	48 8b bc 18 70 01 00 00 	mov    0x170(%rax,%rbx,1),%rdi
  40675c:	4c 01 ef             	add    %r13,%rdi
  40675f:	e8 fc f9 ff ff       	call   406160 <setmailboxkind>
                      setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source2, HIGHER);
  406764:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  406769:	ba 01 00 00 00       	mov    $0x1,%edx
  40676e:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  406775:	48 8b 40 20          	mov    0x20(%rax),%rax
  406779:	48 8b 44 28 38       	mov    0x38(%rax,%rbp,1),%rax
  40677e:	4a 8b bc 20 70 01 00 00 	mov    0x170(%rax,%r12,1),%rdi
  406786:	4c 01 f7             	add    %r14,%rdi
  406789:	e8 d2 f9 ff ff       	call   406160 <setmailboxkind>
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
  40678e:	49 8b bf 28 01 00 00 	mov    0x128(%r15),%rdi
  406795:	48 8b 34 24          	mov    (%rsp),%rsi
                    for (int nn = 0; nn < data->thread_count; nn++) {
  406799:	45 8b 97 34 01 00 00 	mov    0x134(%r15),%r10d
  4067a0:	44 8b 44 24 58       	mov    0x58(%rsp),%r8d
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
  4067a5:	48 8b 47 20          	mov    0x20(%rdi),%rax
  4067a9:	48 8b 4c 30 38       	mov    0x38(%rax,%rsi,1),%rcx
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
  4067ae:	48 8b 44 28 38       	mov    0x38(%rax,%rbp,1),%rax
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
  4067b3:	48 8b 94 19 70 01 00 00 	mov    0x170(%rcx,%rbx,1),%rdx
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
  4067bb:	48 8b b4 18 70 01 00 00 	mov    0x170(%rax,%rbx,1),%rsi
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
  4067c3:	4a 8b 84 20 70 01 00 00 	mov    0x170(%rax,%r12,1),%rax
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
  4067cb:	4c 01 ea             	add    %r13,%rdx
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
  4067ce:	4a 8b 74 36 08       	mov    0x8(%rsi,%r14,1),%rsi
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
  4067d3:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
  4067d7:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
  4067db:	48 8b 12             	mov    (%rdx),%rdx
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
  4067de:	41 c7 81 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%r9)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
  4067e9:	c7 86 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi)
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
  4067f3:	41 c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r9)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
  4067fe:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
  406808:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
  406812:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                    for (int nn = 0; nn < data->thread_count; nn++) {
  40681c:	45 39 d0             	cmp    %r10d,%r8d
  40681f:	0f 8c 0b fe ff ff    	jl     406630 <barriered_work+0x4a0>
  406825:	4c 8b 44 24 48       	mov    0x48(%rsp),%r8
  40682a:	4c 8b 5c 24 50       	mov    0x50(%rsp),%r11
  40682f:	44 8b 74 24 5c       	mov    0x5c(%rsp),%r14d
  406834:	48 8b 2c 24          	mov    (%rsp),%rbp
                    pthread_mutex_unlock(&data->thread->swapmutex[min]);
  406838:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
  40683d:	48 03 87 c8 00 00 00 	add    0xc8(%rdi),%rax
  406844:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
  406849:	48 89 c7             	mov    %rax,%rdi
  40684c:	4c 89 04 24          	mov    %r8,(%rsp)
  406850:	e8 4b b9 ff ff       	call   4021a0 <pthread_mutex_unlock@plt>
                    pthread_mutex_unlock(&data->thread->swapmutex[max]);
  406855:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  40685c:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
  406861:	48 03 b8 c8 00 00 00 	add    0xc8(%rax),%rdi
  406868:	e8 33 b9 ff ff       	call   4021a0 <pthread_mutex_unlock@plt>
                      for (int nn = 0; nn < data->thread_count; nn++) {
  40686d:	41 8b 87 34 01 00 00 	mov    0x134(%r15),%eax
  406874:	4c 8b 04 24          	mov    (%rsp),%r8
  406878:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
  40687d:	85 c0                	test   %eax,%eax
  40687f:	0f 8e 5f 01 00 00    	jle    4069e4 <barriered_work+0x854>
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
  406885:	49 8b b7 28 01 00 00 	mov    0x128(%r15),%rsi
  40688c:	4b 8d 0c 5b          	lea    (%r11,%r11,2),%rcx
  406890:	8d 78 ff             	lea    -0x1(%rax),%edi
  406893:	b8 70 01 00 00       	mov    $0x170,%eax
  406898:	48 8d 0c c9          	lea    (%rcx,%rcx,8),%rcx
  40689c:	4e 8d 0c c5 00 00 00 00 	lea    0x0(,%r8,8),%r9
  4068a4:	48 c1 e7 09          	shl    $0x9,%rdi
  4068a8:	48 8b 56 20          	mov    0x20(%rsi),%rdx
  4068ac:	4d 29 c1             	sub    %r8,%r9
  4068af:	48 81 c7 70 03 00 00 	add    $0x370,%rdi
  4068b6:	49 c1 e1 03          	shl    $0x3,%r9
  4068ba:	4c 8b 54 2a 38       	mov    0x38(%rdx,%rbp,1),%r10
  4068bf:	4c 8b 5c ca 38       	mov    0x38(%rdx,%rcx,8),%r11
  4068c4:	0f 1f 40 00          	nopl   0x0(%rax)
  4068c8:	49 8b 14 03          	mov    (%r11,%rax,1),%rdx
  4068cc:	49 8b 0c 02          	mov    (%r10,%rax,1),%rcx
  4068d0:	4a 8b 1c 0a          	mov    (%rdx,%r9,1),%rbx
  4068d4:	4a 39 1c 29          	cmp    %rbx,(%rcx,%r13,1)
  4068d8:	0f 84 19 01 00 00    	je     4069f7 <barriered_work+0x867>
                      for (int nn = 0; nn < data->thread_count; nn++) {
  4068de:	48 05 00 02 00 00    	add    $0x200,%rax
  4068e4:	48 39 f8             	cmp    %rdi,%rax
  4068e7:	75 df                	jne    4068c8 <barriered_work+0x738>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
  4068e9:	41 8b 8f 40 01 00 00 	mov    0x140(%r15),%ecx
  4068f0:	e9 03 fc ff ff       	jmp    4064f8 <barriered_work+0x368>
      receive(data);
  4068f5:	4c 89 ff             	mov    %r15,%rdi
  4068f8:	e8 d3 f4 ff ff       	call   405dd0 <receive>
      asm volatile ("sfence" ::: "memory");
  4068fd:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
  406900:	49 8b b7 60 01 00 00 	mov    0x160(%r15),%rsi
  406907:	31 ff                	xor    %edi,%edi
  406909:	48 c1 e6 05          	shl    $0x5,%rsi
  40690d:	49 03 b7 50 01 00 00 	add    0x150(%r15),%rsi
  406914:	e8 67 b7 ff ff       	call   402080 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
  406919:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
  406920:	48 8b 50 48          	mov    0x48(%rax),%rdx
  406924:	8b 5a 10             	mov    0x10(%rdx),%ebx
  406927:	83 c3 01             	add    $0x1,%ebx
    while (data->scheduled == 1) {
  40692a:	41 83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r15)
    int modcount = ++data->thread->protected_state->modcount;
  406932:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
  406935:	75 5c                	jne    406993 <barriered_work+0x803>
  406937:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
  406940:	49 63 97 30 01 00 00 	movslq 0x130(%r15),%rdx
  406947:	48 8b 40 18          	mov    0x18(%rax),%rax
  40694b:	49 63 7f 04          	movslq 0x4(%r15),%rdi
      data->n++;
  40694f:	49 83 87 08 01 00 00 01 	addq   $0x1,0x108(%r15)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
  406957:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
  40695b:	48 c1 e7 09          	shl    $0x9,%rdi
  40695f:	48 03 78 38          	add    0x38(%rax),%rdi
  406963:	41 ff 97 20 01 00 00 	call   *0x120(%r15)
      asm volatile ("sfence" ::: "memory");
  40696a:	0f ae f8             	sfence
    while (data->scheduled == 1) {
  40696d:	41 83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r15)
    if (modcount != data->thread->protected_state->modcount) {
  406975:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    while (data->scheduled == 1) {
  40697c:	74 c2                	je     406940 <barriered_work+0x7b0>
    if (modcount != data->thread->protected_state->modcount) {
  40697e:	48 8b 40 48          	mov    0x48(%rax),%rax
  406982:	3b 58 10             	cmp    0x10(%rax),%ebx
  406985:	74 0c                	je     406993 <barriered_work+0x803>
  406987:	48 8d 3d b8 08 00 00 	lea    0x8b8(%rip),%rdi        # 407246 <_IO_stdin_used+0x246>
  40698e:	e8 cd b6 ff ff       	call   402060 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
  406993:	49 8b b7 60 01 00 00 	mov    0x160(%r15),%rsi
  40699a:	31 ff                	xor    %edi,%edi
  40699c:	48 c1 e6 05          	shl    $0x5,%rsi
  4069a0:	49 03 b7 50 01 00 00 	add    0x150(%r15),%rsi
  4069a7:	48 83 c6 10          	add    $0x10,%rsi
  4069ab:	e8 d0 b6 ff ff       	call   402080 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
  4069b0:	49 8b 87 60 01 00 00 	mov    0x160(%r15),%rax
    sendm(data);
  4069b7:	4c 89 ff             	mov    %r15,%rdi
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
  4069ba:	48 83 c0 01          	add    $0x1,%rax
  4069be:	48 99                	cqto
  4069c0:	49 f7 bf 58 01 00 00 	idivq  0x158(%r15)
  4069c7:	49 89 97 60 01 00 00 	mov    %rdx,0x160(%r15)
    sendm(data);
  4069ce:	e8 7d f5 ff ff       	call   405f50 <sendm>
  4069d3:	e9 05 f8 ff ff       	jmp    4061dd <barriered_work+0x4d>
                    pthread_mutex_unlock(&data->thread->swapmutex[min]);
  4069d8:	49 8b bf 28 01 00 00 	mov    0x128(%r15),%rdi
  4069df:	e9 54 fe ff ff       	jmp    406838 <barriered_work+0x6a8>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
  4069e4:	41 8b 8f 40 01 00 00 	mov    0x140(%r15),%ecx
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
  4069eb:	49 8b b7 28 01 00 00 	mov    0x128(%r15),%rsi
  4069f2:	e9 01 fb ff ff       	jmp    4064f8 <barriered_work+0x368>
  4069f7:	bf 01 00 00 00       	mov    $0x1,%edi
  4069fc:	48 8d 35 28 08 00 00 	lea    0x828(%rip),%rsi        # 40722b <_IO_stdin_used+0x22b>
  406a03:	31 c0                	xor    %eax,%eax
  406a05:	e8 e6 b7 ff ff       	call   4021f0 <__printf_chk@plt>
                          exit(1);
  406a0a:	bf 01 00 00 00       	mov    $0x1,%edi
  406a0f:	e8 3c b8 ff ff       	call   402250 <exit@plt>
  406a14:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  406a1f:	90                   	nop

0000000000406a20 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
  406a20:	55                   	push   %rbp
  406a21:	48 89 fd             	mov    %rdi,%rbp
  barriered_work_ingest(data);
  406a24:	e8 b7 ef ff ff       	call   4059e0 <barriered_work_ingest>
  barriered_work(data);
  406a29:	48 89 ef             	mov    %rbp,%rdi
}
  406a2c:	5d                   	pop    %rbp
  barriered_work(data);
  406a2d:	e9 5e f7 ff ff       	jmp    406190 <barriered_work>
  406a32:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  406a3d:	0f 1f 00             	nopl   (%rax)

0000000000406a40 <barriered_nulltask>:
}
  406a40:	31 c0                	xor    %eax,%eax
  406a42:	c3                   	ret
  406a43:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  406a4e:	66 90                	xchg   %ax,%ax

0000000000406a50 <barriered_steal>:
  406a50:	31 c0                	xor    %eax,%eax
  406a52:	c3                   	ret
  406a53:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  406a5e:	66 90                	xchg   %ax,%ax

0000000000406a60 <after>:
  return left.tv_sec > right.tv_sec &&
  406a60:	31 c0                	xor    %eax,%eax
  406a62:	48 39 d7             	cmp    %rdx,%rdi
  406a65:	7e 08                	jle    406a6f <after+0xf>
  406a67:	31 c0                	xor    %eax,%eax
  406a69:	48 39 ce             	cmp    %rcx,%rsi
  406a6c:	0f 9f c0             	setg   %al
}
  406a6f:	c3                   	ret

0000000000406a70 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
  406a70:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
  406a75:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
  406a7a:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
  406a7c:	48 39 d7             	cmp    %rdx,%rdi
  406a7f:	7f 18                	jg     406a99 <within+0x29>
  406a81:	4d 39 d8             	cmp    %r11,%r8
  406a84:	0f 9e c2             	setle  %dl
  406a87:	48 39 ce             	cmp    %rcx,%rsi
  406a8a:	0f 9e c0             	setle  %al
  406a8d:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
  406a8f:	31 c0                	xor    %eax,%eax
  406a91:	4d 39 d1             	cmp    %r10,%r9
  406a94:	0f 9e c0             	setle  %al
    return 1;
  406a97:	21 d0                	and    %edx,%eax
}
  406a99:	c3                   	ret
  406a9a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000406aa0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
  406aa0:	48 83 ec 08          	sub    $0x8,%rsp
  if (after(left.start, right.start) && after(right.end, left.end)) {
  406aa4:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  406aa9:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
  406aae:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
  406ab3:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  406ab8:	e8 a3 ff ff ff       	call   406a60 <after>
  406abd:	85 c0                	test   %eax,%eax
  406abf:	74 21                	je     406ae2 <overlap+0x42>
  406ac1:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  406ac6:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
  406acb:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
  406ad0:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
  406ad5:	e8 86 ff ff ff       	call   406a60 <after>
  406ada:	85 c0                	test   %eax,%eax
  406adc:	0f 85 ae 00 00 00    	jne    406b90 <overlap+0xf0>
  if (after(right.start, left.start) && after(left.end, right.end)) {
  406ae2:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
  406ae7:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
  406aec:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
  406af1:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
  406af6:	e8 65 ff ff ff       	call   406a60 <after>
  406afb:	85 c0                	test   %eax,%eax
  406afd:	74 1d                	je     406b1c <overlap+0x7c>
  406aff:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
  406b04:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
  406b09:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
  406b0e:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  406b13:	e8 48 ff ff ff       	call   406a60 <after>
  406b18:	85 c0                	test   %eax,%eax
  406b1a:	75 74                	jne    406b90 <overlap+0xf0>
  if (within(left.start, right.start, right.end, left.end) == 1) {
  406b1c:	ff 74 24 28          	push   0x28(%rsp)
  406b20:	ff 74 24 28          	push   0x28(%rsp)
  406b24:	4c 8b 44 24 50       	mov    0x50(%rsp),%r8
  406b29:	4c 8b 4c 24 58       	mov    0x58(%rsp),%r9
  406b2e:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
  406b33:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
  406b38:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
  406b3d:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  406b42:	e8 29 ff ff ff       	call   406a70 <within>
  406b47:	5e                   	pop    %rsi
  406b48:	5f                   	pop    %rdi
  406b49:	83 f8 01             	cmp    $0x1,%eax
  406b4c:	74 42                	je     406b90 <overlap+0xf0>
  if (within(right.start, left.start, left.end, right.end) == 1) {
  406b4e:	ff 74 24 48          	push   0x48(%rsp)
  406b52:	ff 74 24 48          	push   0x48(%rsp)
  406b56:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
  406b5b:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
  406b60:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  406b65:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
  406b6a:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
  406b6f:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
  406b74:	e8 f7 fe ff ff       	call   406a70 <within>
  406b79:	5a                   	pop    %rdx
  406b7a:	59                   	pop    %rcx
  406b7b:	83 f8 01             	cmp    $0x1,%eax
  406b7e:	0f 94 c0             	sete   %al
}
  406b81:	48 83 c4 08          	add    $0x8,%rsp
  if (within(right.start, left.start, left.end, right.end) == 1) {
  406b85:	0f b6 c0             	movzbl %al,%eax
}
  406b88:	c3                   	ret
  406b89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    return 1;
  406b90:	b8 01 00 00 00       	mov    $0x1,%eax
}
  406b95:	48 83 c4 08          	add    $0x8,%rsp
  406b99:	c3                   	ret
  406b9a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000406ba0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
  406ba0:	41 57                	push   %r15
  406ba2:	48 89 f8             	mov    %rdi,%rax
  406ba5:	41 56                	push   %r14
  406ba7:	41 55                	push   %r13
  406ba9:	41 54                	push   %r12
  406bab:	55                   	push   %rbp
  406bac:	53                   	push   %rbx
  406bad:	48 83 ec 38          	sub    $0x38,%rsp
  406bb1:	89 74 24 2c          	mov    %esi,0x2c(%rsp)
  for (int x = 0 ; x < thread_count; x++) {
  406bb5:	85 f6                	test   %esi,%esi
  406bb7:	0f 8e 7f 02 00 00    	jle    406e3c <verify+0x29c>
  406bbd:	48 83 c0 38          	add    $0x38,%rax
  406bc1:	c7 44 24 1c 00 00 00 00 	movl   $0x0,0x1c(%rsp)
  406bc9:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  406bce:	49 89 c7             	mov    %rax,%r15
    for (int z = 0 ; z < thread_count; z++) {
  406bd1:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
  406bd9:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
  406bde:	8b 7c 24 28          	mov    0x28(%rsp),%edi
      if (z != x)  {
  406be2:	39 7c 24 1c          	cmp    %edi,0x1c(%rsp)
  406be6:	0f 84 79 01 00 00    	je     406d65 <verify+0x1c5>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
  406bec:	41 8b 57 08          	mov    0x8(%r15),%edx
  406bf0:	85 d2                	test   %edx,%edx
  406bf2:	0f 8e 6d 01 00 00    	jle    406d65 <verify+0x1c5>
  406bf8:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
  406c00:	8b 54 24 1c          	mov    0x1c(%rsp),%edx
  406c04:	48 8d 35 4b 06 00 00 	lea    0x64b(%rip),%rsi        # 407256 <_IO_stdin_used+0x256>
  406c0b:	bf 01 00 00 00       	mov    $0x1,%edi
  406c10:	31 c0                	xor    %eax,%eax
  406c12:	e8 d9 b5 ff ff       	call   4021f0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  406c17:	41 8b 46 08          	mov    0x8(%r14),%eax
  406c1b:	85 c0                	test   %eax,%eax
  406c1d:	0f 8e 2f 01 00 00    	jle    406d52 <verify+0x1b2>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
  406c23:	48 63 6c 24 18       	movslq 0x18(%rsp),%rbp
  406c28:	49 8b 0f             	mov    (%r15),%rcx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  406c2b:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
  406c33:	48 c1 e5 09          	shl    $0x9,%rbp
  406c37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  406c40:	4c 63 64 24 14       	movslq 0x14(%rsp),%r12
  406c45:	49 8b 06             	mov    (%r14),%rax
  406c48:	48 8d 35 1c 06 00 00 	lea    0x61c(%rip),%rsi        # 40726b <_IO_stdin_used+0x26b>
  406c4f:	bf 01 00 00 00       	mov    $0x1,%edi
  406c54:	48 8b 8c 29 60 01 00 00 	mov    0x160(%rcx,%rbp,1),%rcx
  406c5c:	4c 89 e3             	mov    %r12,%rbx
  406c5f:	48 c1 e3 09          	shl    $0x9,%rbx
  406c63:	48 8b 94 18 60 01 00 00 	mov    0x160(%rax,%rbx,1),%rdx
  406c6b:	31 c0                	xor    %eax,%eax
  406c6d:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  406c72:	e8 79 b5 ff ff       	call   4021f0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  406c77:	49 8b 0f             	mov    (%r15),%rcx
  406c7a:	48 8b 94 29 60 01 00 00 	mov    0x160(%rcx,%rbp,1),%rdx
  406c82:	48 85 d2             	test   %rdx,%rdx
  406c85:	0f 8e b4 00 00 00    	jle    406d3f <verify+0x19f>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406c8b:	49 8b 06             	mov    (%r14),%rax
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  406c8e:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406c96:	48 8b b4 18 60 01 00 00 	mov    0x160(%rax,%rbx,1),%rsi
  406c9e:	48 01 d8             	add    %rbx,%rax
  406ca1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  406ca8:	48 85 f6             	test   %rsi,%rsi
  406cab:	0f 8e 4f 01 00 00    	jle    406e00 <verify+0x260>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
  406cb1:	48 63 5c 24 10       	movslq 0x10(%rsp),%rbx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406cb6:	45 31 ed             	xor    %r13d,%r13d
  406cb9:	31 d2                	xor    %edx,%edx
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
  406cbb:	48 c1 e3 05          	shl    $0x5,%rbx
  406cbf:	90                   	nop
  406cc0:	48 8b 80 50 01 00 00 	mov    0x150(%rax),%rax
  406cc7:	48 c1 e2 05          	shl    $0x5,%rdx
  406ccb:	49 89 d4             	mov    %rdx,%r12
  406cce:	ff 74 10 18          	push   0x18(%rax,%rdx,1)
  406cd2:	ff 74 10 10          	push   0x10(%rax,%rdx,1)
  406cd6:	ff 74 10 08          	push   0x8(%rax,%rdx,1)
  406cda:	ff 34 10             	push   (%rax,%rdx,1)
  406cdd:	48 8b 84 29 50 01 00 00 	mov    0x150(%rcx,%rbp,1),%rax
  406ce5:	ff 74 18 18          	push   0x18(%rax,%rbx,1)
  406ce9:	ff 74 18 10          	push   0x10(%rax,%rbx,1)
  406ced:	ff 74 18 08          	push   0x8(%rax,%rbx,1)
  406cf1:	ff 34 18             	push   (%rax,%rbx,1)
  406cf4:	e8 a7 fd ff ff       	call   406aa0 <overlap>
  406cf9:	48 83 c4 40          	add    $0x40,%rsp
  406cfd:	83 f8 01             	cmp    $0x1,%eax
  406d00:	0f 84 8a 00 00 00    	je     406d90 <verify+0x1f0>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406d06:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  406d0b:	49 03 06             	add    (%r14),%rax
  406d0e:	41 83 c5 01          	add    $0x1,%r13d
  406d12:	48 8b b0 60 01 00 00 	mov    0x160(%rax),%rsi
  406d19:	49 63 d5             	movslq %r13d,%rdx
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  406d1c:	49 8b 0f             	mov    (%r15),%rcx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406d1f:	48 39 f2             	cmp    %rsi,%rdx
  406d22:	7c 9c                	jl     406cc0 <verify+0x120>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  406d24:	83 44 24 10 01       	addl   $0x1,0x10(%rsp)
  406d29:	48 8b 94 29 60 01 00 00 	mov    0x160(%rcx,%rbp,1),%rdx
  406d31:	48 63 7c 24 10       	movslq 0x10(%rsp),%rdi
  406d36:	48 39 d7             	cmp    %rdx,%rdi
  406d39:	0f 8c 69 ff ff ff    	jl     406ca8 <verify+0x108>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  406d3f:	83 44 24 14 01       	addl   $0x1,0x14(%rsp)
  406d44:	8b 44 24 14          	mov    0x14(%rsp),%eax
  406d48:	41 39 46 08          	cmp    %eax,0x8(%r14)
  406d4c:	0f 8f ee fe ff ff    	jg     406c40 <verify+0xa0>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
  406d52:	83 44 24 18 01       	addl   $0x1,0x18(%rsp)
  406d57:	8b 44 24 18          	mov    0x18(%rsp),%eax
  406d5b:	41 39 47 08          	cmp    %eax,0x8(%r15)
  406d5f:	0f 8f 9b fe ff ff    	jg     406c00 <verify+0x60>
    for (int z = 0 ; z < thread_count; z++) {
  406d65:	8b 44 24 28          	mov    0x28(%rsp),%eax
  406d69:	49 81 c6 d8 00 00 00 	add    $0xd8,%r14
  406d70:	83 c0 01             	add    $0x1,%eax
  406d73:	39 44 24 2c          	cmp    %eax,0x2c(%rsp)
  406d77:	0f 84 d0 00 00 00    	je     406e4d <verify+0x2ad>
  406d7d:	89 44 24 28          	mov    %eax,0x28(%rsp)
  406d81:	89 c7                	mov    %eax,%edi
  406d83:	e9 5a fe ff ff       	jmp    406be2 <verify+0x42>
  406d88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
  406d90:	49 8b 06             	mov    (%r14),%rax
  406d93:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406d98:	41 83 c5 01          	add    $0x1,%r13d
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
  406d9c:	4c 03 a4 38 50 01 00 00 	add    0x150(%rax,%rdi,1),%r12
  406da4:	49 8b 07             	mov    (%r15),%rax
  406da7:	bf 01 00 00 00       	mov    $0x1,%edi
  406dac:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
  406db1:	4d 8b 4c 24 18       	mov    0x18(%r12),%r9
  406db6:	48 8b b4 28 50 01 00 00 	mov    0x150(%rax,%rbp,1),%rsi
  406dbe:	31 c0                	xor    %eax,%eax
  406dc0:	48 01 de             	add    %rbx,%rsi
  406dc3:	48 8b 16             	mov    (%rsi),%rdx
  406dc6:	4c 8b 46 08          	mov    0x8(%rsi),%r8
  406dca:	48 8d 35 6f 08 00 00 	lea    0x86f(%rip),%rsi        # 407640 <_IO_stdin_used+0x640>
  406dd1:	e8 1a b4 ff ff       	call   4021f0 <__printf_chk@plt>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406dd6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  406ddb:	49 03 06             	add    (%r14),%rax
  406dde:	49 63 d5             	movslq %r13d,%rdx
  406de1:	48 8b b0 60 01 00 00 	mov    0x160(%rax),%rsi
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  406de8:	49 8b 0f             	mov    (%r15),%rcx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  406deb:	48 39 d6             	cmp    %rdx,%rsi
  406dee:	0f 8f cc fe ff ff    	jg     406cc0 <verify+0x120>
  406df4:	e9 2b ff ff ff       	jmp    406d24 <verify+0x184>
  406df9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  406e00:	44 8b 6c 24 10       	mov    0x10(%rsp),%r13d
  406e05:	41 83 c5 01          	add    $0x1,%r13d
  406e09:	49 63 c5             	movslq %r13d,%rax
  406e0c:	48 39 d0             	cmp    %rdx,%rax
  406e0f:	0f 8d 2a ff ff ff    	jge    406d3f <verify+0x19f>
  406e15:	0f 1f 00             	nopl   (%rax)
  406e18:	41 83 c5 01          	add    $0x1,%r13d
  406e1c:	49 63 c5             	movslq %r13d,%rax
  406e1f:	48 39 c2             	cmp    %rax,%rdx
  406e22:	7f f4                	jg     406e18 <verify+0x278>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  406e24:	83 44 24 14 01       	addl   $0x1,0x14(%rsp)
  406e29:	8b 44 24 14          	mov    0x14(%rsp),%eax
  406e2d:	41 39 46 08          	cmp    %eax,0x8(%r14)
  406e31:	0f 8f 09 fe ff ff    	jg     406c40 <verify+0xa0>
  406e37:	e9 16 ff ff ff       	jmp    406d52 <verify+0x1b2>
}
  406e3c:	48 83 c4 38          	add    $0x38,%rsp
  406e40:	31 c0                	xor    %eax,%eax
  406e42:	5b                   	pop    %rbx
  406e43:	5d                   	pop    %rbp
  406e44:	41 5c                	pop    %r12
  406e46:	41 5d                	pop    %r13
  406e48:	41 5e                	pop    %r14
  406e4a:	41 5f                	pop    %r15
  406e4c:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
  406e4d:	8b 7c 24 1c          	mov    0x1c(%rsp),%edi
  406e51:	49 81 c7 d8 00 00 00 	add    $0xd8,%r15
  406e58:	8d 47 01             	lea    0x1(%rdi),%eax
  406e5b:	3b 7c 24 28          	cmp    0x28(%rsp),%edi
  406e5f:	74 db                	je     406e3c <verify+0x29c>
  406e61:	89 44 24 1c          	mov    %eax,0x1c(%rsp)
  406e65:	e9 67 fd ff ff       	jmp    406bd1 <verify+0x31>

Disassembly of section .fini:

0000000000406e6c <_fini>:
  406e6c:	f3 0f 1e fa          	endbr64
  406e70:	48 83 ec 08          	sub    $0x8,%rsp
  406e74:	48 83 c4 08          	add    $0x8,%rsp
  406e78:	c3                   	ret
