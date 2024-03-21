
multibarrier:     file format elf64-x86-64


Disassembly of section .init:

0000000000402000 <_init>:
  402000:	f3 0f 1e fa          	endbr64
  402004:	48 83 ec 08          	sub    $0x8,%rsp
  402008:	48 8b 05 d9 6f 00 00 	mov    0x6fd9(%rip),%rax        # 408fe8 <__gmon_start__@Base>
  40200f:	48 85 c0             	test   %rax,%rax
  402012:	74 02                	je     402016 <_init+0x16>
  402014:	ff d0                	call   *%rax
  402016:	48 83 c4 08          	add    $0x8,%rsp
  40201a:	c3                   	ret

Disassembly of section .plt:

0000000000402020 <free@plt-0x10>:
  402020:	ff 35 62 6e 00 00    	push   0x6e62(%rip)        # 408e88 <_GLOBAL_OFFSET_TABLE_+0x8>
  402026:	ff 25 64 6e 00 00    	jmp    *0x6e64(%rip)        # 408e90 <_GLOBAL_OFFSET_TABLE_+0x10>
  40202c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000402030 <free@plt>:
  402030:	ff 25 62 6e 00 00    	jmp    *0x6e62(%rip)        # 408e98 <free@GLIBC_2.2.5>
  402036:	68 00 00 00 00       	push   $0x0
  40203b:	e9 e0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402040 <putchar@plt>:
  402040:	ff 25 5a 6e 00 00    	jmp    *0x6e5a(%rip)        # 408ea0 <putchar@GLIBC_2.2.5>
  402046:	68 01 00 00 00       	push   $0x1
  40204b:	e9 d0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402050 <pthread_setaffinity_np@plt>:
  402050:	ff 25 52 6e 00 00    	jmp    *0x6e52(%rip)        # 408ea8 <pthread_setaffinity_np@GLIBC_2.34>
  402056:	68 02 00 00 00       	push   $0x2
  40205b:	e9 c0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402060 <puts@plt>:
  402060:	ff 25 4a 6e 00 00    	jmp    *0x6e4a(%rip)        # 408eb0 <puts@GLIBC_2.2.5>
  402066:	68 03 00 00 00       	push   $0x3
  40206b:	e9 b0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402070 <setsockopt@plt>:
  402070:	ff 25 42 6e 00 00    	jmp    *0x6e42(%rip)        # 408eb8 <setsockopt@GLIBC_2.2.5>
  402076:	68 04 00 00 00       	push   $0x4
  40207b:	e9 a0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402080 <clock_gettime@plt>:
  402080:	ff 25 3a 6e 00 00    	jmp    *0x6e3a(%rip)        # 408ec0 <clock_gettime@GLIBC_2.17>
  402086:	68 05 00 00 00       	push   $0x5
  40208b:	e9 90 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402090 <strlen@plt>:
  402090:	ff 25 32 6e 00 00    	jmp    *0x6e32(%rip)        # 408ec8 <strlen@GLIBC_2.2.5>
  402096:	68 06 00 00 00       	push   $0x6
  40209b:	e9 80 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020a0 <__stack_chk_fail@plt>:
  4020a0:	ff 25 2a 6e 00 00    	jmp    *0x6e2a(%rip)        # 408ed0 <__stack_chk_fail@GLIBC_2.4>
  4020a6:	68 07 00 00 00       	push   $0x7
  4020ab:	e9 70 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020b0 <io_uring_submit@plt>:
  4020b0:	ff 25 22 6e 00 00    	jmp    *0x6e22(%rip)        # 408ed8 <io_uring_submit@LIBURING_2.0>
  4020b6:	68 08 00 00 00       	push   $0x8
  4020bb:	e9 60 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020c0 <nanosleep@plt>:
  4020c0:	ff 25 1a 6e 00 00    	jmp    *0x6e1a(%rip)        # 408ee0 <nanosleep@GLIBC_2.2.5>
  4020c6:	68 09 00 00 00       	push   $0x9
  4020cb:	e9 50 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020d0 <strrchr@plt>:
  4020d0:	ff 25 12 6e 00 00    	jmp    *0x6e12(%rip)        # 408ee8 <strrchr@GLIBC_2.2.5>
  4020d6:	68 0a 00 00 00       	push   $0xa
  4020db:	e9 40 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020e0 <close@plt>:
  4020e0:	ff 25 0a 6e 00 00    	jmp    *0x6e0a(%rip)        # 408ef0 <close@GLIBC_2.2.5>
  4020e6:	68 0b 00 00 00       	push   $0xb
  4020eb:	e9 30 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020f0 <strtok_r@plt>:
  4020f0:	ff 25 02 6e 00 00    	jmp    *0x6e02(%rip)        # 408ef8 <strtok_r@GLIBC_2.2.5>
  4020f6:	68 0c 00 00 00       	push   $0xc
  4020fb:	e9 20 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402100 <read@plt>:
  402100:	ff 25 fa 6d 00 00    	jmp    *0x6dfa(%rip)        # 408f00 <read@GLIBC_2.2.5>
  402106:	68 0d 00 00 00       	push   $0xd
  40210b:	e9 10 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402110 <calloc@plt>:
  402110:	ff 25 f2 6d 00 00    	jmp    *0x6df2(%rip)        # 408f08 <calloc@GLIBC_2.2.5>
  402116:	68 0e 00 00 00       	push   $0xe
  40211b:	e9 00 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402120 <strcmp@plt>:
  402120:	ff 25 ea 6d 00 00    	jmp    *0x6dea(%rip)        # 408f10 <strcmp@GLIBC_2.2.5>
  402126:	68 0f 00 00 00       	push   $0xf
  40212b:	e9 f0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402130 <__memcpy_chk@plt>:
  402130:	ff 25 e2 6d 00 00    	jmp    *0x6de2(%rip)        # 408f18 <__memcpy_chk@GLIBC_2.3.4>
  402136:	68 10 00 00 00       	push   $0x10
  40213b:	e9 e0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402140 <stat@plt>:
  402140:	ff 25 da 6d 00 00    	jmp    *0x6dda(%rip)        # 408f20 <stat@GLIBC_2.33>
  402146:	68 11 00 00 00       	push   $0x11
  40214b:	e9 d0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402150 <memcpy@plt>:
  402150:	ff 25 d2 6d 00 00    	jmp    *0x6dd2(%rip)        # 408f28 <memcpy@GLIBC_2.14>
  402156:	68 12 00 00 00       	push   $0x12
  40215b:	e9 c0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402160 <io_uring_queue_init@plt>:
  402160:	ff 25 ca 6d 00 00    	jmp    *0x6dca(%rip)        # 408f30 <io_uring_queue_init@LIBURING_2.0>
  402166:	68 13 00 00 00       	push   $0x13
  40216b:	e9 b0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402170 <eventfd_write@plt>:
  402170:	ff 25 c2 6d 00 00    	jmp    *0x6dc2(%rip)        # 408f38 <eventfd_write@GLIBC_2.7>
  402176:	68 14 00 00 00       	push   $0x14
  40217b:	e9 a0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402180 <malloc@plt>:
  402180:	ff 25 ba 6d 00 00    	jmp    *0x6dba(%rip)        # 408f40 <malloc@GLIBC_2.2.5>
  402186:	68 15 00 00 00       	push   $0x15
  40218b:	e9 90 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402190 <listen@plt>:
  402190:	ff 25 b2 6d 00 00    	jmp    *0x6db2(%rip)        # 408f48 <listen@GLIBC_2.2.5>
  402196:	68 16 00 00 00       	push   $0x16
  40219b:	e9 80 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021a0 <__strcpy_chk@plt>:
  4021a0:	ff 25 aa 6d 00 00    	jmp    *0x6daa(%rip)        # 408f50 <__strcpy_chk@GLIBC_2.3.4>
  4021a6:	68 17 00 00 00       	push   $0x17
  4021ab:	e9 70 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021b0 <__io_uring_get_cqe@plt>:
  4021b0:	ff 25 a2 6d 00 00    	jmp    *0x6da2(%rip)        # 408f58 <__io_uring_get_cqe@LIBURING_2.0>
  4021b6:	68 18 00 00 00       	push   $0x18
  4021bb:	e9 60 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021c0 <__printf_chk@plt>:
  4021c0:	ff 25 9a 6d 00 00    	jmp    *0x6d9a(%rip)        # 408f60 <__printf_chk@GLIBC_2.3.4>
  4021c6:	68 19 00 00 00       	push   $0x19
  4021cb:	e9 50 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021d0 <bind@plt>:
  4021d0:	ff 25 92 6d 00 00    	jmp    *0x6d92(%rip)        # 408f68 <bind@GLIBC_2.2.5>
  4021d6:	68 1a 00 00 00       	push   $0x1a
  4021db:	e9 40 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021e0 <pthread_create@plt>:
  4021e0:	ff 25 8a 6d 00 00    	jmp    *0x6d8a(%rip)        # 408f70 <pthread_create@GLIBC_2.34>
  4021e6:	68 1b 00 00 00       	push   $0x1b
  4021eb:	e9 30 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021f0 <open@plt>:
  4021f0:	ff 25 82 6d 00 00    	jmp    *0x6d82(%rip)        # 408f78 <open@GLIBC_2.2.5>
  4021f6:	68 1c 00 00 00       	push   $0x1c
  4021fb:	e9 20 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402200 <perror@plt>:
  402200:	ff 25 7a 6d 00 00    	jmp    *0x6d7a(%rip)        # 408f80 <perror@GLIBC_2.2.5>
  402206:	68 1d 00 00 00       	push   $0x1d
  40220b:	e9 10 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402210 <exit@plt>:
  402210:	ff 25 72 6d 00 00    	jmp    *0x6d72(%rip)        # 408f88 <exit@GLIBC_2.2.5>
  402216:	68 1e 00 00 00       	push   $0x1e
  40221b:	e9 00 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402220 <eventfd@plt>:
  402220:	ff 25 6a 6d 00 00    	jmp    *0x6d6a(%rip)        # 408f90 <eventfd@GLIBC_2.7>
  402226:	68 1f 00 00 00       	push   $0x1f
  40222b:	e9 f0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402230 <fwrite@plt>:
  402230:	ff 25 62 6d 00 00    	jmp    *0x6d62(%rip)        # 408f98 <fwrite@GLIBC_2.2.5>
  402236:	68 20 00 00 00       	push   $0x20
  40223b:	e9 e0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402240 <__fprintf_chk@plt>:
  402240:	ff 25 5a 6d 00 00    	jmp    *0x6d5a(%rip)        # 408fa0 <__fprintf_chk@GLIBC_2.3.4>
  402246:	68 21 00 00 00       	push   $0x21
  40224b:	e9 d0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402250 <io_uring_register_eventfd@plt>:
  402250:	ff 25 52 6d 00 00    	jmp    *0x6d52(%rip)        # 408fa8 <io_uring_register_eventfd@LIBURING_2.0>
  402256:	68 22 00 00 00       	push   $0x22
  40225b:	e9 c0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402260 <pthread_join@plt>:
  402260:	ff 25 4a 6d 00 00    	jmp    *0x6d4a(%rip)        # 408fb0 <pthread_join@GLIBC_2.34>
  402266:	68 23 00 00 00       	push   $0x23
  40226b:	e9 b0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402270 <strerror@plt>:
  402270:	ff 25 42 6d 00 00    	jmp    *0x6d42(%rip)        # 408fb8 <strerror@GLIBC_2.2.5>
  402276:	68 24 00 00 00       	push   $0x24
  40227b:	e9 a0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402280 <__ctype_tolower_loc@plt>:
  402280:	ff 25 3a 6d 00 00    	jmp    *0x6d3a(%rip)        # 408fc0 <__ctype_tolower_loc@GLIBC_2.3>
  402286:	68 25 00 00 00       	push   $0x25
  40228b:	e9 90 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402290 <__sprintf_chk@plt>:
  402290:	ff 25 32 6d 00 00    	jmp    *0x6d32(%rip)        # 408fc8 <__sprintf_chk@GLIBC_2.3.4>
  402296:	68 26 00 00 00       	push   $0x26
  40229b:	e9 80 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022a0 <socket@plt>:
  4022a0:	ff 25 2a 6d 00 00    	jmp    *0x6d2a(%rip)        # 408fd0 <socket@GLIBC_2.2.5>
  4022a6:	68 27 00 00 00       	push   $0x27
  4022ab:	e9 70 fd ff ff       	jmp    402020 <_init+0x20>

Disassembly of section .text:

00000000004022b0 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
  4022b0:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

static inline void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
  4022b6:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  4022be:	0f 0b                	ud2

00000000004022c0 <add_read_request.cold>:
  4022c0:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  4022c8:	0f 0b                	ud2

00000000004022ca <add_accept_request.cold>:
  4022ca:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  4022d2:	0f 0b                	ud2

00000000004022d4 <io_thread.cold>:
  4022d4:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  4022dc:	0f 0b                	ud2
  4022de:	66 90                	xchg   %ax,%ax

00000000004022e0 <main>:
    }


  return 0;
}
int main() {
  4022e0:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4022e2:	48 8d 3d c7 41 00 00 	lea    0x41c7(%rip),%rdi        # 4064b0 <_IO_stdin_used+0x4b0>
  4022e9:	41 56                	push   %r14
  4022eb:	41 55                	push   %r13
  4022ed:	41 54                	push   %r12
  4022ef:	55                   	push   %rbp
  4022f0:	53                   	push   %rbx
  4022f1:	48 81 ec a8 00 00 00 	sub    $0xa8,%rsp
  4022f8:	f3 0f 7e 2d f0 6c 00 00 	movq   0x6cf0(%rip),%xmm5        # 408ff0 <_GLOBAL_OFFSET_TABLE_+0x170>
  402300:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  402309:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  402311:	31 c0                	xor    %eax,%eax
  402313:	0f 16 2d c6 6c 00 00 	movhps 0x6cc6(%rip),%xmm5        # 408fe0 <_GLOBAL_OFFSET_TABLE_+0x160>
  40231a:	0f 29 6c 24 50       	movaps %xmm5,0x50(%rsp)
  40231f:	e8 3c fd ff ff       	call   402060 <puts@plt>
  402324:	bf 0a 00 00 00       	mov    $0xa,%edi
  402329:	e8 12 fd ff ff       	call   402040 <putchar@plt>
  40232e:	48 8d 3d 09 3f 00 00 	lea    0x3f09(%rip),%rdi        # 40623e <_IO_stdin_used+0x23e>
  402335:	e8 26 fd ff ff       	call   402060 <puts@plt>
  40233a:	ba 06 00 00 00       	mov    $0x6,%edx
  40233f:	48 8d 35 14 3f 00 00 	lea    0x3f14(%rip),%rsi        # 40625a <_IO_stdin_used+0x25a>
  402346:	31 c0                	xor    %eax,%eax
  402348:	bf 01 00 00 00       	mov    $0x1,%edi
  40234d:	e8 6e fe ff ff       	call   4021c0 <__printf_chk@plt>
  402352:	ba 09 00 00 00       	mov    $0x9,%edx
  402357:	48 8d 35 16 3f 00 00 	lea    0x3f16(%rip),%rsi        # 406274 <_IO_stdin_used+0x274>
  40235e:	31 c0                	xor    %eax,%eax
  402360:	bf 01 00 00 00       	mov    $0x1,%edi
  402365:	e8 56 fe ff ff       	call   4021c0 <__printf_chk@plt>
  40236a:	ba 01 00 00 00       	mov    $0x1,%edx
  40236f:	48 8d 35 12 3f 00 00 	lea    0x3f12(%rip),%rsi        # 406288 <_IO_stdin_used+0x288>
  402376:	31 c0                	xor    %eax,%eax
  402378:	bf 01 00 00 00       	mov    $0x1,%edi
  40237d:	e8 3e fe ff ff       	call   4021c0 <__printf_chk@plt>
  402382:	ba 01 00 00 00       	mov    $0x1,%edx
  402387:	48 8d 35 0b 3f 00 00 	lea    0x3f0b(%rip),%rsi        # 406299 <_IO_stdin_used+0x299>
  40238e:	31 c0                	xor    %eax,%eax
  402390:	bf 01 00 00 00       	mov    $0x1,%edi
  402395:	e8 26 fe ff ff       	call   4021c0 <__printf_chk@plt>
  40239a:	ba 01 00 00 00       	mov    $0x1,%edx
  40239f:	48 8d 35 0b 3f 00 00 	lea    0x3f0b(%rip),%rsi        # 4062b1 <_IO_stdin_used+0x2b1>
  4023a6:	31 c0                	xor    %eax,%eax
  4023a8:	bf 01 00 00 00       	mov    $0x1,%edi
  4023ad:	e8 0e fe ff ff       	call   4021c0 <__printf_chk@plt>
  4023b2:	ba 01 00 00 00       	mov    $0x1,%edx
  4023b7:	48 8d 35 5a 41 00 00 	lea    0x415a(%rip),%rsi        # 406518 <_IO_stdin_used+0x518>
  4023be:	31 c0                	xor    %eax,%eax
  4023c0:	bf 01 00 00 00       	mov    $0x1,%edi
  4023c5:	e8 f6 fd ff ff       	call   4021c0 <__printf_chk@plt>
  4023ca:	ba 01 00 00 00       	mov    $0x1,%edx
  4023cf:	48 8d 35 72 41 00 00 	lea    0x4172(%rip),%rsi        # 406548 <_IO_stdin_used+0x548>
  4023d6:	31 c0                	xor    %eax,%eax
  4023d8:	bf 01 00 00 00       	mov    $0x1,%edi
  4023dd:	e8 de fd ff ff       	call   4021c0 <__printf_chk@plt>
  4023e2:	ba 40 42 0f 00       	mov    $0xf4240,%edx
  4023e7:	48 8d 35 df 3e 00 00 	lea    0x3edf(%rip),%rsi        # 4062cd <_IO_stdin_used+0x2cd>
  4023ee:	31 c0                	xor    %eax,%eax
  4023f0:	bf 01 00 00 00       	mov    $0x1,%edi
  4023f5:	e8 c6 fd ff ff       	call   4021c0 <__printf_chk@plt>
  4023fa:	ba 05 00 00 00       	mov    $0x5,%edx
  4023ff:	48 8d 35 e1 3e 00 00 	lea    0x3ee1(%rip),%rsi        # 4062e7 <_IO_stdin_used+0x2e7>
  402406:	31 c0                	xor    %eax,%eax
  402408:	bf 01 00 00 00       	mov    $0x1,%edi
  40240d:	e8 ae fd ff ff       	call   4021c0 <__printf_chk@plt>
  402412:	48 8d 3d b5 3c 00 00 	lea    0x3cb5(%rip),%rdi        # 4060ce <_IO_stdin_used+0xce>
  402419:	e8 42 fc ff ff       	call   402060 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
  40241e:	be 18 00 00 00       	mov    $0x18,%esi
  402423:	bf 06 00 00 00       	mov    $0x6,%edi
  402428:	e8 e3 fc ff ff       	call   402110 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  40242d:	be b0 00 00 00       	mov    $0xb0,%esi
  402432:	bf 09 00 00 00       	mov    $0x9,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
  402437:	49 89 c6             	mov    %rax,%r14
  40243a:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  402442:	e8 c9 fc ff ff       	call   402110 <calloc@plt>
  int barrier_count = 2;
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
  402447:	be 10 00 00 00       	mov    $0x10,%esi
  40244c:	bf 01 00 00 00       	mov    $0x1,%edi
  402451:	49 8d 6e e8          	lea    -0x18(%r14),%rbp
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  402455:	49 89 c7             	mov    %rax,%r15
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
  402458:	e8 b3 fc ff ff       	call   402110 <calloc@plt>
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  40245d:	be 10 00 00 00       	mov    $0x10,%esi
  402462:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
  402467:	4d 89 fd             	mov    %r15,%r13
    buffers[x].count = buffer_size;
  40246a:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
  402470:	48 89 c3             	mov    %rax,%rbx
  402473:	48 89 84 24 80 00 00 00 	mov    %rax,0x80(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  40247b:	e8 90 fc ff ff       	call   402110 <calloc@plt>
  402480:	4c 89 7c 24 48       	mov    %r15,0x48(%rsp)
  402485:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
  402489:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  402490:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
    }
  }
  int external_thread_index = 0;
  402498:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
  4024a0:	4c 89 7c 24 40       	mov    %r15,0x40(%rsp)
  4024a5:	0f 1f 00             	nopl   (%rax)
  4024a8:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  for (int x = 0 ; x < total_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  4024ad:	be 08 00 00 00       	mov    $0x8,%esi
  4024b2:	bf 02 00 00 00       	mov    $0x2,%edi
  4024b7:	43 8d 04 3f          	lea    (%r15,%r15,1),%eax
  4024bb:	45 89 fe             	mov    %r15d,%r14d
  4024be:	41 83 c7 01          	add    $0x1,%r15d
  4024c2:	89 04 24             	mov    %eax,(%rsp)
  4024c5:	e8 46 fc ff ff       	call   402110 <calloc@plt>
    int other = -1;
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
  4024ca:	be 80 00 00 00       	mov    $0x80,%esi
  4024cf:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  4024d4:	48 89 c3             	mov    %rax,%rbx
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
  4024d7:	e8 34 fc ff ff       	call   402110 <calloc@plt>
  4024dc:	44 89 7c 24 28       	mov    %r15d,0x28(%rsp)
  4024e1:	49 89 c4             	mov    %rax,%r12
    CPU_ZERO(sendercpu);
    if (x % 2 == 1) {
  4024e4:	41 f6 c6 01          	test   $0x1,%r14b
  4024e8:	0f 85 84 0c 00 00    	jne    403172 <main+0xe92>
  4024ee:	45 89 ff             	mov    %r15d,%r15d
      printf("odd %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
      thread_data[x].protected_state = &protected_state[other];
    } else {
      thread_data[x].thread_index = 0;
      other = (x + 1) % total_threads;
      my_thread_data[0] = &thread_data[x]; 
  4024f1:	4c 89 2b             	mov    %r13,(%rbx)
  4024f4:	4c 89 e9             	mov    %r13,%rcx
  4024f7:	48 8d 35 0b 3e 00 00 	lea    0x3e0b(%rip),%rsi        # 406309 <_IO_stdin_used+0x309>
  4024fe:	4c 89 ff             	mov    %r15,%rdi
      other = (x + 1) % total_threads;
  402501:	4d 69 ff 39 8e e3 38 	imul   $0x38e38e39,%r15,%r15
      thread_data[x].thread_index = 0;
  402508:	41 c7 45 00 00 00 00 00 	movl   $0x0,0x0(%r13)
      other = (x + 1) % total_threads;
  402510:	49 c1 ef 21          	shr    $0x21,%r15
  402514:	43 8d 04 ff          	lea    (%r15,%r15,8),%eax
  402518:	29 c7                	sub    %eax,%edi
  40251a:	48 63 c7             	movslq %edi,%rax
  40251d:	bf 01 00 00 00       	mov    $0x1,%edi
      my_thread_data[1] = &thread_data[other]; 
  402522:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
      other = (x + 1) % total_threads;
  402526:	49 89 c7             	mov    %rax,%r15
      my_thread_data[1] = &thread_data[other]; 
  402529:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
  40252d:	44 89 f2             	mov    %r14d,%edx
  402530:	31 c0                	xor    %eax,%eax
  402532:	49 c1 e0 04          	shl    $0x4,%r8
  402536:	4c 03 44 24 40       	add    0x40(%rsp),%r8
  40253b:	4c 89 43 08          	mov    %r8,0x8(%rbx)
  40253f:	e8 7c fc ff ff       	call   4021c0 <__printf_chk@plt>
      printf("even %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
      thread_data[x].protected_state = &protected_state[x];
  402544:	48 8d 45 18          	lea    0x18(%rbp),%rax
  402548:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  40254d:	48 89 c5             	mov    %rax,%rbp
      thread_data[x].protected_state = &protected_state[other];
  402550:	49 89 6d 38          	mov    %rbp,0x38(%r13)
  402554:	45 8b 45 00          	mov    0x0(%r13),%r8d
  402558:	44 89 f9             	mov    %r15d,%ecx
  40255b:	44 89 f2             	mov    %r14d,%edx
  40255e:	48 8d 35 0b 40 00 00 	lea    0x400b(%rip),%rsi        # 406570 <_IO_stdin_used+0x570>
  402565:	bf 01 00 00 00       	mov    $0x1,%edi
  40256a:	31 c0                	xor    %eax,%eax
  40256c:	e8 4f fc ff ff       	call   4021c0 <__printf_chk@plt>
  402571:	44 89 f2             	mov    %r14d,%edx
  402574:	bf 01 00 00 00       	mov    $0x1,%edi
  402579:	31 c0                	xor    %eax,%eax
    }
    printf("i am %d, other is %d my thread index is %d\n", x, other, thread_data[x].thread_index);
    thread_data[x].other = other;
  40257b:	45 89 bd a8 00 00 00 	mov    %r15d,0xa8(%r13)
  402582:	44 8b 3c 24          	mov    (%rsp),%r15d
  402586:	48 8d 35 13 40 00 00 	lea    0x4013(%rip),%rsi        # 4065a0 <_IO_stdin_used+0x5a0>
  40258d:	44 89 f9             	mov    %r15d,%ecx
  402590:	e8 2b fc ff ff       	call   4021c0 <__printf_chk@plt>
    // for (int j = 0 ; j < core ; j++) {
      printf("assigning thread %d to core %d\n", x, curcpu);
      CPU_SET(curcpu, sendercpu);
  402595:	44 89 f9             	mov    %r15d,%ecx
    // }
    curcpu += 2;
    thread_data[x].cpu_set = sendercpu;
    thread_data[x].real_thread_index = x;
    thread_data[x].threads = my_thread_data;
  402598:	49 89 5d 10          	mov    %rbx,0x10(%r13)
      CPU_SET(curcpu, sendercpu);
  40259c:	b8 01 00 00 00       	mov    $0x1,%eax
  4025a1:	48 d3 e0             	shl    %cl,%rax
  4025a4:	49 09 04 24          	or     %rax,(%r12)
    thread_data[x].thread_count = 2;
  4025a8:	48 8b 05 71 44 00 00 	mov    0x4471(%rip),%rax        # 406a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_timestamp_limit = timestamp_limit;

      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
      thread_data[x].tasks = barriers;

      for (int y = 0 ; y < total_barrier_count ; y++) {
  4025af:	31 db                	xor    %ebx,%ebx
    thread_data[x].real_thread_index = x;
  4025b1:	45 89 75 04          	mov    %r14d,0x4(%r13)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  4025b5:	be 10 00 00 00       	mov    $0x10,%esi
  4025ba:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].cpu_set = sendercpu;
  4025bf:	4d 89 a5 a0 00 00 00 	mov    %r12,0xa0(%r13)
    thread_data[x].thread_count = 2;
  4025c6:	49 89 45 18          	mov    %rax,0x18(%r13)
    thread_data[x].task_count = total_barrier_count;
  4025ca:	41 c7 45 30 03 00 00 00 	movl   $0x3,0x30(%r13)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  4025d2:	e8 39 fb ff ff       	call   402110 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  4025d7:	be 10 00 00 00       	mov    $0x10,%esi
  4025dc:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  4025e1:	49 89 45 58          	mov    %rax,0x58(%r13)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  4025e5:	e8 26 fb ff ff       	call   402110 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  4025ea:	be 28 00 00 00       	mov    $0x28,%esi
  4025ef:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
  4025f4:	66 0f 6f 2d c4 43 00 00 	movdqa 0x43c4(%rip),%xmm5        # 4069c0 <_IO_stdin_used+0x9c0>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  4025fc:	49 89 45 60          	mov    %rax,0x60(%r13)
    thread_data[x].timestamp_count = 0;
  402600:	41 0f 11 6d 70       	movups %xmm5,0x70(%r13)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  402605:	e8 06 fb ff ff       	call   402110 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  40260a:	be 80 01 00 00       	mov    $0x180,%esi
  40260f:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
  402614:	66 0f 6f 35 a4 43 00 00 	movdqa 0x43a4(%rip),%xmm6        # 4069c0 <_IO_stdin_used+0x9c0>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  40261c:	49 89 85 80 00 00 00 	mov    %rax,0x80(%r13)
    thread_data[x].task_timestamp_count = 0;
  402623:	41 0f 11 b5 88 00 00 00 	movups %xmm6,0x88(%r13)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  40262b:	e8 e0 fa ff ff       	call   402110 <calloc@plt>
        messaged->message = message;
        messaged->task_index = y;
        messaged->thread_index = thread_data[x].thread_index;
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
        thread_data[x].tasks[y].message = messaged;
        thread_data[x].tasks[y].sending = 1;
  402630:	44 89 74 24 08       	mov    %r14d,0x8(%rsp)
      thread_data[x].tasks = barriers;
  402635:	49 89 45 28          	mov    %rax,0x28(%r13)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  402639:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks[y].protected = do_protected_write; 
  40263c:	48 63 c3             	movslq %ebx,%rax
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
  40263f:	be 20 00 00 00       	mov    $0x20,%esi
  402644:	bf 06 00 00 00       	mov    $0x6,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
  402649:	48 8d 2c 40          	lea    (%rax,%rax,2),%rbp
  40264d:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  402652:	48 c7 c0 b0 32 40 00 	mov    $0x4032b0,%rax
  402659:	48 c1 e5 07          	shl    $0x7,%rbp
  40265d:	4c 8d 24 2a          	lea    (%rdx,%rbp,1),%r12
  402661:	49 89 84 24 a0 00 00 00 	mov    %rax,0xa0(%r12)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
  402669:	e8 a2 fa ff ff       	call   402110 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
  40266e:	49 89 84 24 e8 00 00 00 	mov    %rax,0xe8(%r12)
        for (int b = 0 ; b < 2 ; b++) {
  402676:	49 89 c7             	mov    %rax,%r15
  402679:	48 8d 40 40          	lea    0x40(%rax),%rax
  40267d:	48 89 04 24          	mov    %rax,(%rsp)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402681:	be 08 00 00 00       	mov    $0x8,%esi
  402686:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
  40268b:	49 83 c7 20          	add    $0x20,%r15
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  40268f:	e8 7c fa ff ff       	call   402110 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402694:	be 08 00 00 00       	mov    $0x8,%esi
  402699:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  40269e:	49 89 c4             	mov    %rax,%r12
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  4026a1:	e8 6a fa ff ff       	call   402110 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
  4026a6:	be 18 00 00 00       	mov    $0x18,%esi
  4026ab:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  4026b0:	49 89 c6             	mov    %rax,%r14
          struct Data *data = calloc(2, sizeof(struct Data));
  4026b3:	e8 58 fa ff ff       	call   402110 <calloc@plt>
          data[0].messages_count = 0;
  4026b8:	66 0f 6f 1d 10 43 00 00 	movdqa 0x4310(%rip),%xmm3        # 4069d0 <_IO_stdin_used+0x9d0>
          mailboxes[b].higher = &data[1];
  4026c0:	48 8d 48 18          	lea    0x18(%rax),%rcx
          mailboxes[b].lower = &data[0];
  4026c4:	66 48 0f 6e c0       	movq   %rax,%xmm0
          data[0].messages = messages;
  4026c9:	4c 89 20             	mov    %r12,(%rax)
          mailboxes[b].lower = &data[0];
  4026cc:	66 48 0f 6e d1       	movq   %rcx,%xmm2
          data[1].messages = messages2;
  4026d1:	4c 89 70 18          	mov    %r14,0x18(%rax)
          mailboxes[b].lower = &data[0];
  4026d5:	66 0f 6c c2          	punpcklqdq %xmm2,%xmm0
          data[0].messages_count = 0;
  4026d9:	0f 11 58 08          	movups %xmm3,0x8(%rax)
          mailboxes[b].lower = &data[0];
  4026dd:	41 0f 11 47 e0       	movups %xmm0,-0x20(%r15)
          data[1].messages_count = 0;
  4026e2:	0f 11 58 20          	movups %xmm3,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
  4026e6:	4c 39 3c 24          	cmp    %r15,(%rsp)
  4026ea:	75 95                	jne    402681 <main+0x3a1>
        char *message = malloc(sizeof(char) * 256);
  4026ec:	be 01 00 00 00       	mov    $0x1,%esi
  4026f1:	bf 00 01 00 00       	mov    $0x100,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  4026f6:	44 8d 7b 01          	lea    0x1(%rbx),%r15d
        char *message = malloc(sizeof(char) * 256);
  4026fa:	e8 11 fa ff ff       	call   402110 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
  4026ff:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
  402704:	49 89 c4             	mov    %rax,%r12
        struct Message *messaged = malloc(sizeof(struct Message));
  402707:	e8 74 fa ff ff       	call   402180 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  40270c:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
  402711:	4c 89 e7             	mov    %r12,%rdi
  402714:	41 89 d9             	mov    %ebx,%r9d
  402717:	48 8d 0d a2 3e 00 00 	lea    0x3ea2(%rip),%rcx        # 4065c0 <_IO_stdin_used+0x5c0>
  40271e:	48 89 04 24          	mov    %rax,(%rsp)
  402722:	ba 00 01 00 00       	mov    $0x100,%edx
  402727:	31 c0                	xor    %eax,%eax
  402729:	be 01 00 00 00       	mov    $0x1,%esi
  40272e:	e8 5d fb ff ff       	call   402290 <__sprintf_chk@plt>
        messaged->thread_index = thread_data[x].thread_index;
  402733:	49 63 45 00          	movslq 0x0(%r13),%rax
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402737:	49 8b 55 28          	mov    0x28(%r13),%rdx
        thread_data[x].tasks[y].snapshot_count = 99;
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  40273b:	be 20 00 00 00       	mov    $0x20,%esi
        messaged->message = message;
  402740:	4c 8b 14 24          	mov    (%rsp),%r10
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402744:	bf 63 00 00 00       	mov    $0x63,%edi
        messaged->thread_index = thread_data[x].thread_index;
  402749:	66 48 0f 6e c0       	movq   %rax,%xmm0
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  40274e:	48 89 14 24          	mov    %rdx,(%rsp)
        messaged->message = message;
  402752:	4d 89 22             	mov    %r12,(%r10)
        messaged->thread_index = thread_data[x].thread_index;
  402755:	0f 16 44 24 10       	movhps 0x10(%rsp),%xmm0
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  40275a:	4c 8d 24 2a          	lea    (%rdx,%rbp,1),%r12
        messaged->thread_index = thread_data[x].thread_index;
  40275e:	41 0f 11 42 08       	movups %xmm0,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402763:	45 89 bc 24 08 01 00 00 	mov    %r15d,0x108(%r12)
        thread_data[x].tasks[y].message = messaged;
  40276b:	4d 89 94 24 00 01 00 00 	mov    %r10,0x100(%r12)
        thread_data[x].tasks[y].snapshot_count = 99;
  402773:	49 c7 84 24 d0 00 00 00 63 00 00 00 	movq   $0x63,0xd0(%r12)
        messaged->thread_index = thread_data[x].thread_index;
  40277f:	89 44 24 18          	mov    %eax,0x18(%rsp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402783:	e8 88 f9 ff ff       	call   402110 <calloc@plt>
            thread_data[x].tasks[y].run = barriered_nulltask; 
          }
          */
          thread_data[x].tasks[y].run = barriered_work; 
        } else {
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
  402788:	8b 74 24 20          	mov    0x20(%rsp),%esi
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
  40278c:	8b 4c 24 18          	mov    0x18(%rsp),%ecx
        thread_data[x].tasks[y].current_snapshot = 0;
  402790:	49 c7 84 24 d8 00 00 00 00 00 00 00 	movq   $0x0,0xd8(%r12)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  40279c:	49 89 84 24 c8 00 00 00 	mov    %rax,0xc8(%r12)
        if (y == barrier_count - 1) {
  4027a4:	48 8b 14 24          	mov    (%rsp),%rdx
        thread_data[x].tasks[y].available = 1;
  4027a8:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
  4027b2:	85 f6                	test   %esi,%esi
        thread_data[x].tasks[y].available = 1;
  4027b4:	49 89 84 24 b8 00 00 00 	mov    %rax,0xb8(%r12)
        thread_data[x].tasks[y].sending = 1;
  4027bc:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
  4027c6:	49 89 84 24 f8 00 00 00 	mov    %rax,0xf8(%r12)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
  4027ce:	0f 9e c0             	setle  %al
        if (y == barrier_count - 1) {
  4027d1:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
  4027d4:	41 89 8c 24 b0 00 00 00 	mov    %ecx,0xb0(%r12)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
  4027dc:	4d 89 ac 24 a8 00 00 00 	mov    %r13,0xa8(%r12)
        thread_data[x].tasks[y].arrived = 0;
  4027e4:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
        thread_data[x].tasks[y].thread_count = 2;
  4027f0:	41 c7 84 24 b4 00 00 00 02 00 00 00 	movl   $0x2,0xb4(%r12)
        thread_data[x].tasks[y].task_index = y;
  4027fc:	41 89 1c 24          	mov    %ebx,(%r12)
        if (y == barrier_count - 1) {
  402800:	0f 84 52 09 00 00    	je     403158 <main+0xe78>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
  402806:	8b 7c 24 08          	mov    0x8(%rsp),%edi
  40280a:	39 df                	cmp    %ebx,%edi
  40280c:	75 52                	jne    402860 <main+0x580>
  40280e:	84 c0                	test   %al,%al
  402810:	74 4e                	je     402860 <main+0x580>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  402812:	89 fa                	mov    %edi,%edx
  402814:	48 8d 35 cd 3d 00 00 	lea    0x3dcd(%rip),%rsi        # 4065e8 <_IO_stdin_used+0x5e8>
  40281b:	bf 01 00 00 00       	mov    $0x1,%edi
  402820:	31 c0                	xor    %eax,%eax
  402822:	e8 99 f9 ff ff       	call   4021c0 <__printf_chk@plt>
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
  402827:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
  40282f:	49 8b 55 28          	mov    0x28(%r13),%rdx
            thread_data[x].buffers = &buffers[external_thread_index++];
  402833:	c7 44 24 20 01 00 00 00 	movl   $0x1,0x20(%rsp)
  40283b:	49 89 45 40          	mov    %rax,0x40(%r13)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
  40283f:	48 c7 c0 70 52 40 00 	mov    $0x405270,%rax
  402846:	48 89 84 2a 98 00 00 00 	mov    %rax,0x98(%rdx,%rbp,1)
      for (int y = 0 ; y < total_barrier_count ; y++) {
  40284e:	41 83 ff 03          	cmp    $0x3,%r15d
  402852:	74 21                	je     402875 <main+0x595>
  int external_thread_index = 0;
  402854:	44 89 fb             	mov    %r15d,%ebx
  402857:	e9 e0 fd ff ff       	jmp    40263c <main+0x35c>
  40285c:	0f 1f 40 00          	nopl   0x0(%rax)
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
  402860:	48 c7 c0 a0 50 40 00 	mov    $0x4050a0,%rax
  402867:	49 89 84 24 98 00 00 00 	mov    %rax,0x98(%r12)
      for (int y = 0 ; y < total_barrier_count ; y++) {
  40286f:	41 83 ff 03          	cmp    $0x3,%r15d
  402873:	75 df                	jne    402854 <main+0x574>
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
  402875:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
  40287f:	66 0f 6f 7c 24 50    	movdqa 0x50(%rsp),%xmm7
  for (int x = 0 ; x < total_threads ; x++) {
  402885:	48 8b 6c 24 30       	mov    0x30(%rsp),%rbp
      thread_data[x].tasks[barrier_count].arrived = 0; 
  40288a:	c7 82 80 03 00 00 00 00 00 00 	movl   $0x0,0x380(%rdx)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
  402894:	c7 82 00 03 00 00 02 00 00 00 	movl   $0x2,0x300(%rdx)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
  40289e:	48 89 82 b4 03 00 00 	mov    %rax,0x3b4(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
  4028a5:	41 8b 45 00          	mov    0x0(%r13),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
  4028a9:	4c 89 aa a8 03 00 00 	mov    %r13,0x3a8(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
  4028b0:	49 81 c5 b0 00 00 00 	add    $0xb0,%r13
  4028b7:	83 7c 24 28 09       	cmpl   $0x9,0x28(%rsp)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
  4028bc:	89 82 b0 03 00 00    	mov    %eax,0x3b0(%rdx)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
  4028c2:	c7 82 fc 03 00 00 06 00 00 00 	movl   $0x6,0x3fc(%rdx)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  4028cc:	c7 82 bc 03 00 00 03 00 00 00 	movl   $0x3,0x3bc(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
  4028d6:	0f 11 ba 98 03 00 00 	movups %xmm7,0x398(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
  4028dd:	0f 85 c5 fb ff ff    	jne    4024a8 <main+0x1c8>
  4028e3:	4c 8b 7c 24 40       	mov    0x40(%rsp),%r15
  4028e8:	ba 07 00 00 00       	mov    $0x7,%edx
  4028ed:	48 8d 35 24 3a 00 00 	lea    0x3a24(%rip),%rsi        # 406318 <_IO_stdin_used+0x318>
  4028f4:	31 c0                	xor    %eax,%eax
  4028f6:	bf 01 00 00 00       	mov    $0x1,%edi
  4028fb:	e8 c0 f8 ff ff       	call   4021c0 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  402900:	be 08 00 00 00       	mov    $0x8,%esi
  402905:	bf 02 00 00 00       	mov    $0x2,%edi
    my_thread_data[0] = &thread_data[x]; 
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
  40290a:	49 8d 9f 60 01 00 00 	lea    0x160(%r15),%rbx
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  402911:	e8 fa f7 ff ff       	call   402110 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
  402916:	4d 8d b7 d0 04 00 00 	lea    0x4d0(%r15),%r14

    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = 2;
  40291d:	41 c7 87 e8 04 00 00 02 00 00 00 	movl   $0x2,0x4e8(%r15)
  402928:	66 48 0f 6e f3       	movq   %rbx,%xmm6
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
  40292d:	48 89 58 08          	mov    %rbx,0x8(%rax)
  402931:	66 49 0f 6e ef       	movq   %r15,%xmm5
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402936:	be 38 00 00 00       	mov    $0x38,%esi
  40293b:	bf 09 00 00 00       	mov    $0x9,%edi
    thread_data[x].threads = my_thread_data;
  402940:	49 89 87 e0 04 00 00 	mov    %rax,0x4e0(%r15)
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
  402947:	4d 8d af 80 05 00 00 	lea    0x580(%r15),%r13
    my_thread_data[0] = &thread_data[x]; 
  40294e:	4c 89 30             	mov    %r14,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
  402951:	49 8b 47 28          	mov    0x28(%r15),%rax
    thread_data[x].thread_index = 0;
  402955:	41 c7 87 d0 04 00 00 00 00 00 00 	movl   $0x0,0x4d0(%r15)
    thread_data[x].task_count = total_barrier_count;
  402960:	41 c7 87 00 05 00 00 03 00 00 00 	movl   $0x3,0x500(%r15)
    thread_data[n].tasks[0].scheduled = 1;
  40296b:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
  402975:	49 8d 87 b0 00 00 00 	lea    0xb0(%r15),%rax
  40297c:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  402981:	49 8b 87 d8 00 00 00 	mov    0xd8(%r15),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
  402988:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
  40298d:	49 8d 9f c0 02 00 00 	lea    0x2c0(%r15),%rbx
  402994:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
  40299e:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
  4029a5:	66 48 0f 6e fb       	movq   %rbx,%xmm7
  4029aa:	0f 16 6c 24 10       	movhps 0x10(%rsp),%xmm5
  4029af:	48 89 5c 24 40       	mov    %rbx,0x40(%rsp)
  4029b4:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
  4029be:	49 8d 87 10 02 00 00 	lea    0x210(%r15),%rax
  4029c5:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  4029ca:	49 8b 87 38 02 00 00 	mov    0x238(%r15),%rax
  4029d1:	0f 29 6c 24 30       	movaps %xmm5,0x30(%rsp)
  4029d6:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
  4029e0:	49 8b 87 e8 02 00 00 	mov    0x2e8(%r15),%rax
  4029e7:	0f 16 74 24 08       	movhps 0x8(%rsp),%xmm6
  4029ec:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
  4029f6:	49 8d 87 70 03 00 00 	lea    0x370(%r15),%rax
  4029fd:	48 89 04 24          	mov    %rax,(%rsp)
  402a01:	49 8b 87 98 03 00 00 	mov    0x398(%r15),%rax
  402a08:	0f 29 74 24 60       	movaps %xmm6,0x60(%rsp)
  402a0d:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402a17:	0f 16 3c 24          	movhps (%rsp),%xmm7
  402a1b:	0f 29 7c 24 50       	movaps %xmm7,0x50(%rsp)
  402a20:	e8 eb f6 ff ff       	call   402110 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402a25:	be 38 00 00 00       	mov    $0x38,%esi
  402a2a:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402a2f:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402a32:	e8 d9 f6 ff ff       	call   402110 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402a37:	be 38 00 00 00       	mov    $0x38,%esi
  402a3c:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402a41:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402a44:	e8 c7 f6 ff ff       	call   402110 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402a49:	be 38 00 00 00       	mov    $0x38,%esi
  402a4e:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402a53:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402a58:	e8 b3 f6 ff ff       	call   402110 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  402a5d:	be 08 00 00 00       	mov    $0x8,%esi
  402a62:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  402a67:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  402a6c:	e8 9f f6 ff ff       	call   402110 <calloc@plt>
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
  402a71:	be 08 00 00 00       	mov    $0x8,%esi
  402a76:	bf 09 00 00 00       	mov    $0x9,%edi
  thread_data[thread_count].type = TIMER;
  402a7b:	41 c7 87 28 04 00 00 00 00 00 00 	movl   $0x0,0x428(%r15)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  402a86:	48 89 c5             	mov    %rax,%rbp
  thread_data[thread_count].task_count = total_barrier_count;
  402a89:	48 8b 05 98 3f 00 00 	mov    0x3f98(%rip),%rax        # 406a28 <_IO_stdin_used+0xa28>
  402a90:	49 89 87 50 04 00 00 	mov    %rax,0x450(%r15)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
  402a97:	e8 74 f6 ff ff       	call   402110 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
  402a9c:	66 49 0f 6e c7       	movq   %r15,%xmm0
    my_thread_data[n] = &thread_data[n]; 
  402aa1:	66 0f 6f 0d 37 3f 00 00 	movdqa 0x3f37(%rip),%xmm1        # 4069e0 <_IO_stdin_used+0x9e0>
  }
  thread_data[thread_count].threads = my_thread_data;
  thread_data[thread_count].thread_count = thread_count;
  402aa9:	41 c7 87 38 04 00 00 06 00 00 00 	movl   $0x6,0x438(%r15)
  402ab4:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    my_thread_data[n] = &thread_data[n]; 
  402ab8:	4c 89 68 40          	mov    %r13,0x40(%rax)
  402abc:	ba 06 00 00 00       	mov    $0x6,%edx
  402ac1:	48 8d 35 5f 38 00 00 	lea    0x385f(%rip),%rsi        # 406327 <_IO_stdin_used+0x327>
  402ac8:	66 0f d4 c8          	paddq  %xmm0,%xmm1
  402acc:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].threads = my_thread_data;
  402ad1:	49 89 87 30 04 00 00 	mov    %rax,0x430(%r15)
    my_thread_data[n] = &thread_data[n]; 
  402ad8:	0f 11 08             	movups %xmm1,(%rax)
  402adb:	66 0f 6f 0d 0d 3f 00 00 	movdqa 0x3f0d(%rip),%xmm1        # 4069f0 <_IO_stdin_used+0x9f0>
  thread_data[thread_count].my_thread_count = 2;
  402ae3:	41 c7 87 40 04 00 00 02 00 00 00 	movl   $0x2,0x440(%r15)
  thread_data[thread_count].thread_index = 0;
  402aee:	41 c7 87 20 04 00 00 00 00 00 00 	movl   $0x0,0x420(%r15)
    my_thread_data[n] = &thread_data[n]; 
  402af9:	66 0f d4 c8          	paddq  %xmm0,%xmm1
  402afd:	0f 11 48 10          	movups %xmm1,0x10(%rax)
  402b01:	66 0f 6f 0d f7 3e 00 00 	movdqa 0x3ef7(%rip),%xmm1        # 406a00 <_IO_stdin_used+0xa00>
  402b09:	66 0f d4 c8          	paddq  %xmm0,%xmm1
  402b0d:	66 0f d4 05 fb 3e 00 00 	paddq  0x3efb(%rip),%xmm0        # 406a10 <_IO_stdin_used+0xa10>
  402b15:	0f 11 48 20          	movups %xmm1,0x20(%rax)
  402b19:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  402b1d:	31 c0                	xor    %eax,%eax
  402b1f:	e8 9c f6 ff ff       	call   4021c0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
  402b24:	48 c7 c2 40 36 40 00 	mov    $0x403640,%rdx
  402b2b:	48 8d 7d 30          	lea    0x30(%rbp),%rdi
  402b2f:	49 8d b4 24 50 01 00 00 	lea    0x150(%r12),%rsi
  402b37:	49 8d 8f 20 04 00 00 	lea    0x420(%r15),%rcx
  402b3e:	49 89 ec             	mov    %rbp,%r12
  402b41:	e8 9a f6 ff ff       	call   4021e0 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
  402b46:	4c 89 6c 24 78       	mov    %r13,0x78(%rsp)
  402b4b:	45 31 c0             	xor    %r8d,%r8d
  402b4e:	49 89 dd             	mov    %rbx,%r13
  402b51:	48 8b 5c 24 48       	mov    0x48(%rsp),%rbx
  402b56:	48 89 6c 24 70       	mov    %rbp,0x70(%rsp)
  402b5b:	4c 8d 0d a6 3a 00 00 	lea    0x3aa6(%rip),%r9        # 406608 <_IO_stdin_used+0x608>
  402b62:	44 89 c5             	mov    %r8d,%ebp
    thread_data[x].type = WORKER;
  402b65:	c7 43 08 01 00 00 00 	movl   $0x1,0x8(%rbx)
  402b6c:	4c 89 ce             	mov    %r9,%rsi
  402b6f:	89 ea                	mov    %ebp,%edx
  402b71:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
  402b73:	c7 43 34 01 00 00 00 	movl   $0x1,0x34(%rbx)
  402b7a:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < thread_count ; x++) {
  402b7f:	83 c5 01             	add    $0x1,%ebp
  402b82:	e8 39 f6 ff ff       	call   4021c0 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
  402b87:	48 89 d9             	mov    %rbx,%rcx
  402b8a:	4c 89 ee             	mov    %r13,%rsi
  402b8d:	4c 89 e7             	mov    %r12,%rdi
  402b90:	48 c7 c2 50 33 40 00 	mov    $0x403350,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
  402b97:	48 81 c3 b0 00 00 00 	add    $0xb0,%rbx
  402b9e:	49 83 c4 08          	add    $0x8,%r12
  402ba2:	49 83 c5 38          	add    $0x38,%r13
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
  402ba6:	e8 35 f6 ff ff       	call   4021e0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
  402bab:	48 8b 53 f0          	mov    -0x10(%rbx),%rdx
  402baf:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
  402bb4:	be 08 00 00 00       	mov    $0x8,%esi
  402bb9:	e8 92 f4 ff ff       	call   402050 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < thread_count ; x++) {
  402bbe:	83 fd 06             	cmp    $0x6,%ebp
  402bc1:	4c 8d 0d 40 3a 00 00 	lea    0x3a40(%rip),%r9        # 406608 <_IO_stdin_used+0x608>
  402bc8:	75 9b                	jne    402b65 <main+0x885>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  402bca:	be d8 00 00 00       	mov    $0xd8,%esi
  402bcf:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
  402bd4:	48 8b 6c 24 70       	mov    0x70(%rsp),%rbp
    thread_data[x].task_count = 0;
  402bd9:	48 8b 1d 50 3e 00 00 	mov    0x3e50(%rip),%rbx        # 406a30 <_IO_stdin_used+0xa30>
    thread_data[x].type = IO;
  402be0:	41 c7 87 d8 04 00 00 02 00 00 00 	movl   $0x2,0x4d8(%r15)
  402beb:	4c 8b 6c 24 78       	mov    0x78(%rsp),%r13
    thread_data[x].task_count = 0;
  402bf0:	4c 8d 25 a0 37 00 00 	lea    0x37a0(%rip),%r12        # 406397 <_IO_stdin_used+0x397>
  402bf7:	49 89 9f 00 05 00 00 	mov    %rbx,0x500(%r15)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  402bfe:	e8 0d f5 ff ff       	call   402110 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
  402c03:	be 00 08 00 00       	mov    $0x800,%esi
  402c08:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
  402c0a:	49 89 87 18 05 00 00 	mov    %rax,0x518(%r15)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
  402c11:	e8 0a f6 ff ff       	call   402220 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  402c16:	be 08 00 00 00       	mov    $0x8,%esi
  402c1b:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
  402c20:	41 89 87 20 05 00 00 	mov    %eax,0x520(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  402c27:	e8 e4 f4 ff ff       	call   402110 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
  402c2c:	66 0f 6f 74 24 30    	movdqa 0x30(%rsp),%xmm6
  402c32:	66 0f 6f 7c 24 60    	movdqa 0x60(%rsp),%xmm7
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
  402c38:	41 c7 87 e8 04 00 00 06 00 00 00 	movl   $0x6,0x4e8(%r15)
    thread_data[x].threads = my_thread_data;
  402c43:	49 89 87 e0 04 00 00 	mov    %rax,0x4e0(%r15)
  402c4a:	ba 07 00 00 00       	mov    $0x7,%edx
  402c4f:	48 8d 35 ef 36 00 00 	lea    0x36ef(%rip),%rsi        # 406345 <_IO_stdin_used+0x345>
  402c56:	bf 01 00 00 00       	mov    $0x1,%edi
      my_thread_data[n] = &thread_data[n]; 
  402c5b:	0f 11 30             	movups %xmm6,(%rax)
  402c5e:	66 0f 6f 74 24 50    	movdqa 0x50(%rsp),%xmm6
    thread_data[x].thread_index = x;
  402c64:	41 c7 87 d0 04 00 00 07 00 00 00 	movl   $0x7,0x4d0(%r15)
      my_thread_data[n] = &thread_data[n]; 
  402c6f:	0f 11 78 10          	movups %xmm7,0x10(%rax)
  402c73:	0f 11 70 20          	movups %xmm6,0x20(%rax)
  402c77:	31 c0                	xor    %eax,%eax
  402c79:	e8 42 f5 ff ff       	call   4021c0 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  402c7e:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
  402c83:	4c 89 f1             	mov    %r14,%rcx
  402c86:	48 8d 7d 38          	lea    0x38(%rbp),%rdi
  402c8a:	48 c7 c2 a0 47 40 00 	mov    $0x4047a0,%rdx
  402c91:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
  402c98:	e8 43 f5 ff ff       	call   4021e0 <pthread_create@plt>
  402c9d:	ba 08 00 00 00       	mov    $0x8,%edx
  402ca2:	48 8d 35 b3 36 00 00 	lea    0x36b3(%rip),%rsi        # 40635c <_IO_stdin_used+0x35c>
  402ca9:	31 c0                	xor    %eax,%eax
  402cab:	bf 01 00 00 00       	mov    $0x1,%edi
  402cb0:	e8 0b f5 ff ff       	call   4021c0 <__printf_chk@plt>
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  402cb5:	be 08 00 00 00       	mov    $0x8,%esi
  402cba:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[x].buffers = &buffers[buffer_index];
  402cbf:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    thread_data[x].task_count = 0;
  402cc7:	49 89 9f b0 05 00 00 	mov    %rbx,0x5b0(%r15)
    thread_data[x].type = EXTERNAL;
  402cce:	41 c7 87 88 05 00 00 03 00 00 00 	movl   $0x3,0x588(%r15)
    thread_data[x].buffers = &buffers[buffer_index];
  402cd9:	49 89 87 c0 05 00 00 	mov    %rax,0x5c0(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  402ce0:	e8 2b f4 ff ff       	call   402110 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
  402ce5:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  402cea:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  402cef:	4c 89 e9             	mov    %r13,%rcx
      my_thread_data[n] = &thread_data[n]; 
  402cf2:	4c 89 38             	mov    %r15,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  402cf5:	48 c7 c2 80 35 40 00 	mov    $0x403580,%rdx
  402cfc:	48 8d 7d 40          	lea    0x40(%rbp),%rdi
  402d00:	4c 8d ac 24 90 00 00 00 	lea    0x90(%rsp),%r13
      my_thread_data[n] = &thread_data[n]; 
  402d08:	48 89 58 08          	mov    %rbx,0x8(%rax)
  402d0c:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  402d11:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    thread_data[x].threads = my_thread_data;
  402d18:	49 89 87 90 05 00 00 	mov    %rax,0x590(%r15)
      my_thread_data[n] = &thread_data[n]; 
  402d1f:	48 89 58 10          	mov    %rbx,0x10(%rax)
  402d23:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    thread_data[x].thread_index = x;
  402d28:	41 c7 87 80 05 00 00 08 00 00 00 	movl   $0x8,0x580(%r15)
      my_thread_data[n] = &thread_data[n]; 
  402d33:	48 89 58 18          	mov    %rbx,0x18(%rax)
  402d37:	48 8b 5c 24 40       	mov    0x40(%rsp),%rbx
  402d3c:	48 89 58 20          	mov    %rbx,0x20(%rax)
  402d40:	48 8b 1c 24          	mov    (%rsp),%rbx
  402d44:	48 89 58 28          	mov    %rbx,0x28(%rax)
    thread_data[x].thread_count = thread_count;
  402d48:	48 8b 05 e9 3c 00 00 	mov    0x3ce9(%rip),%rax        # 406a38 <_IO_stdin_used+0xa38>
  402d4f:	31 db                	xor    %ebx,%ebx
  402d51:	49 89 87 98 05 00 00 	mov    %rax,0x598(%r15)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  402d58:	e8 83 f4 ff ff       	call   4021e0 <pthread_create@plt>
  402d5d:	48 8d 3d 15 36 00 00 	lea    0x3615(%rip),%rdi        # 406379 <_IO_stdin_used+0x379>
  402d64:	e8 f7 f2 ff ff       	call   402060 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
  402d69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    void * result; 
    pthread_join(thread[x], &result);
  402d70:	48 8b 7c dd 00       	mov    0x0(%rbp,%rbx,8),%rdi
  402d75:	4c 89 ee             	mov    %r13,%rsi
  402d78:	e8 e3 f4 ff ff       	call   402260 <pthread_join@plt>
  402d7d:	89 da                	mov    %ebx,%edx
  402d7f:	4c 89 e6             	mov    %r12,%rsi
  402d82:	bf 01 00 00 00       	mov    $0x1,%edi
  402d87:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
  402d89:	48 83 c3 01          	add    $0x1,%rbx
  402d8d:	e8 2e f4 ff ff       	call   4021c0 <__printf_chk@plt>
  402d92:	48 83 fb 09          	cmp    $0x9,%rbx
  402d96:	75 d8                	jne    402d70 <main+0xa90>
  402d98:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  402da0:	45 31 e4             	xor    %r12d,%r12d
  long ingests = 0;
  402da3:	45 31 ed             	xor    %r13d,%r13d
  long total = 0;
  402da6:	31 db                	xor    %ebx,%ebx
  long sents = 0;
  long received = 0;
  for (int x = 0 ; x < thread_count ; x++) {
  402da8:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
  402db0:	49 8d 6f 28          	lea    0x28(%r15),%rbp
  long sents = 0;
  402db4:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
  402dbd:	49 89 ee             	mov    %rbp,%r14
  402dc0:	48 89 04 24          	mov    %rax,(%rsp)
  long received = 0;
  402dc4:	31 c0                	xor    %eax,%eax
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
  402dc6:	4c 89 7c 24 18       	mov    %r15,0x18(%rsp)
  402dcb:	49 89 c7             	mov    %rax,%r15
  402dce:	66 90                	xchg   %ax,%ax
    if (x % 2 == 1) {
  402dd0:	8b 7c 24 08          	mov    0x8(%rsp),%edi
  402dd4:	89 f8                	mov    %edi,%eax
  402dd6:	89 fd                	mov    %edi,%ebp
      other = (x + 1) % total_threads;
  402dd8:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
  402ddb:	83 e0 01             	and    $0x1,%eax
  402dde:	83 ed 01             	sub    $0x1,%ebp
      other = (x + 1) % total_threads;
  402de1:	89 7c 24 08          	mov    %edi,0x8(%rsp)
  402de5:	85 c0                	test   %eax,%eax
  402de7:	0f 44 ef             	cmove  %edi,%ebp
  402dea:	bf 0a 00 00 00       	mov    $0xa,%edi
  402def:	e8 4c f2 ff ff       	call   402040 <putchar@plt>
  402df4:	48 8b 04 24          	mov    (%rsp),%rax
  402df8:	bf 01 00 00 00       	mov    $0x1,%edi
  402dfd:	48 8d 35 a7 35 00 00 	lea    0x35a7(%rip),%rsi        # 4063ab <_IO_stdin_used+0x3ab>
  402e04:	48 8b 10             	mov    (%rax),%rdx
  402e07:	31 c0                	xor    %eax,%eax
  402e09:	e8 b2 f3 ff ff       	call   4021c0 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
  402e0e:	41 8b 56 08          	mov    0x8(%r14),%edx
  402e12:	85 d2                	test   %edx,%edx
  402e14:	0f 8e 99 03 00 00    	jle    4031b3 <main+0xed3>
  402e1a:	83 ea 01             	sub    $0x1,%edx
      v += thread_data[me].tasks[n].v;
  402e1d:	49 8b 0e             	mov    (%r14),%rcx
  402e20:	48 8d 14 52          	lea    (%rdx,%rdx,2),%rdx
  402e24:	48 c1 e2 07          	shl    $0x7,%rdx
  402e28:	48 8d 81 90 00 00 00 	lea    0x90(%rcx),%rax
  402e2f:	48 8d 8c 11 10 02 00 00 	lea    0x210(%rcx,%rdx,1),%rcx
    long v = 0;
  402e37:	31 d2                	xor    %edx,%edx
  402e39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      v += thread_data[me].tasks[n].v;
  402e40:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
  402e43:	48 05 80 01 00 00    	add    $0x180,%rax
  402e49:	48 39 c8             	cmp    %rcx,%rax
  402e4c:	75 f2                	jne    402e40 <main+0xb60>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
  402e4e:	48 63 ed             	movslq %ebp,%rbp
  402e51:	48 8d 44 ad 00       	lea    0x0(%rbp,%rbp,4),%rax
  402e56:	48 8d 44 45 00       	lea    0x0(%rbp,%rax,2),%rax
  402e5b:	48 c1 e0 04          	shl    $0x4,%rax
  402e5f:	48 03 44 24 18       	add    0x18(%rsp),%rax
  402e64:	8b 48 30             	mov    0x30(%rax),%ecx
  402e67:	85 c9                	test   %ecx,%ecx
  402e69:	7e 33                	jle    402e9e <main+0xbbe>
  402e6b:	83 e9 01             	sub    $0x1,%ecx
      v += thread_data[other].tasks[n].v;
  402e6e:	48 8b 70 28          	mov    0x28(%rax),%rsi
  402e72:	48 8d 0c 49          	lea    (%rcx,%rcx,2),%rcx
  402e76:	48 c1 e1 07          	shl    $0x7,%rcx
  402e7a:	48 8d 86 90 00 00 00 	lea    0x90(%rsi),%rax
  402e81:	48 8d 8c 0e 10 02 00 00 	lea    0x210(%rsi,%rcx,1),%rcx
  402e89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  402e90:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
  402e93:	48 05 80 01 00 00    	add    $0x180,%rax
  402e99:	48 39 c1             	cmp    %rax,%rcx
  402e9c:	75 f2                	jne    402e90 <main+0xbb0>
  402e9e:	48 8d 35 1b 35 00 00 	lea    0x351b(%rip),%rsi        # 4063c0 <_IO_stdin_used+0x3c0>
  402ea5:	bf 01 00 00 00       	mov    $0x1,%edi
  402eaa:	31 c0                	xor    %eax,%eax
  402eac:	e8 0f f3 ff ff       	call   4021c0 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
  402eb1:	48 8b 04 24          	mov    (%rsp),%rax
  402eb5:	bf 01 00 00 00       	mov    $0x1,%edi
  402eba:	48 8d 35 6f 37 00 00 	lea    0x376f(%rip),%rsi        # 406630 <_IO_stdin_used+0x630>
  402ec1:	48 8b 08             	mov    (%rax),%rcx
  402ec4:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
  402ece:	48 f7 e9             	imul   %rcx
  402ed1:	48 c1 f9 3f          	sar    $0x3f,%rcx
  402ed5:	31 c0                	xor    %eax,%eax
  402ed7:	48 d1 fa             	sar    %rdx
  402eda:	48 29 ca             	sub    %rcx,%rdx
  402edd:	e8 de f2 ff ff       	call   4021c0 <__printf_chk@plt>
  402ee2:	bf 0a 00 00 00       	mov    $0xa,%edi
  402ee7:	e8 54 f1 ff ff       	call   402040 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402eec:	41 8b 46 08          	mov    0x8(%r14),%eax
  402ef0:	85 c0                	test   %eax,%eax
  402ef2:	0f 8e 90 00 00 00    	jle    402f88 <main+0xca8>
  402ef8:	83 e8 01             	sub    $0x1,%eax
      total += thread_data[x].tasks[n].n;
  402efb:	49 8b 16             	mov    (%r14),%rdx
  402efe:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
  402f03:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
  402f07:	48 c1 e0 07          	shl    $0x7,%rax
  402f0b:	48 8d 8a 88 00 00 00 	lea    0x88(%rdx),%rcx
  402f12:	48 8d b4 02 08 02 00 00 	lea    0x208(%rdx,%rax,1),%rsi
  402f1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
  402f20:	48 8b 41 60          	mov    0x60(%rcx),%rax
      total += thread_data[x].tasks[n].n;
  402f24:	48 03 19             	add    (%rcx),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402f27:	48 81 c1 80 01 00 00 	add    $0x180,%rcx
      ingests += thread_data[x].tasks[n].ingest_count;
  402f2e:	4c 03 a9 d8 fe ff ff 	add    -0x128(%rcx),%r13
      sends += thread_data[x].tasks[n].sends;
  402f35:	4c 03 a1 e8 fe ff ff 	add    -0x118(%rcx),%r12
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
  402f3c:	48 8b 50 30          	mov    0x30(%rax),%rdx
  402f40:	48 03 50 10          	add    0x10(%rax),%rdx
  402f44:	48 03 50 50          	add    0x50(%rax),%rdx
  402f48:	48 03 50 70          	add    0x70(%rax),%rdx
  402f4c:	48 03 90 90 00 00 00 	add    0x90(%rax),%rdx
  402f53:	48 03 90 b0 00 00 00 	add    0xb0(%rax),%rdx
  402f5a:	48 01 d7             	add    %rdx,%rdi
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
  402f5d:	48 8b 50 38          	mov    0x38(%rax),%rdx
  402f61:	48 03 50 18          	add    0x18(%rax),%rdx
  402f65:	48 03 50 58          	add    0x58(%rax),%rdx
  402f69:	48 03 50 78          	add    0x78(%rax),%rdx
  402f6d:	48 03 90 98 00 00 00 	add    0x98(%rax),%rdx
  402f74:	48 03 90 b8 00 00 00 	add    0xb8(%rax),%rdx
  402f7b:	49 01 d7             	add    %rdx,%r15
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402f7e:	48 39 ce             	cmp    %rcx,%rsi
  402f81:	75 9d                	jne    402f20 <main+0xc40>
  402f83:	48 89 7c 24 10       	mov    %rdi,0x10(%rsp)
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
  402f88:	49 8b 4e 50          	mov    0x50(%r14),%rcx
  402f8c:	48 85 c9             	test   %rcx,%rcx
  402f8f:	7e 12                	jle    402fa3 <main+0xcc3>
  402f91:	31 c0                	xor    %eax,%eax
  402f93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  402f98:	83 c0 01             	add    $0x1,%eax
  402f9b:	48 63 d0             	movslq %eax,%rdx
  402f9e:	48 39 d1             	cmp    %rdx,%rcx
  402fa1:	7f f5                	jg     402f98 <main+0xcb8>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  402fa3:	31 ed                	xor    %ebp,%ebp
  402fa5:	31 c0                	xor    %eax,%eax
  402fa7:	49 83 7e 68 00       	cmpq   $0x0,0x68(%r14)
  402fac:	7e 5f                	jle    40300d <main+0xd2d>
  402fae:	66 90                	xchg   %ax,%ax
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
  402fb0:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  402fb4:	49 8b 46 58          	mov    0x58(%r14),%rax
  402fb8:	48 83 ec 08          	sub    $0x8,%rsp
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  402fbc:	83 c5 01             	add    $0x1,%ebp
  402fbf:	bf 01 00 00 00       	mov    $0x1,%edi
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
  402fc4:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
  402fc8:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
  402fd2:	48 8b 71 18          	mov    0x18(%rcx),%rsi
  402fd6:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
  402fda:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
  402fdd:	4c 8b 41 10          	mov    0x10(%rcx),%r8
  402fe1:	4c 2b 01             	sub    (%rcx),%r8
  402fe4:	31 c0                	xor    %eax,%eax
  402fe6:	8b 49 20             	mov    0x20(%rcx),%ecx
  402fe9:	56                   	push   %rsi
  402fea:	48 8d 35 5f 36 00 00 	lea    0x365f(%rip),%rsi        # 406650 <_IO_stdin_used+0x650>
  402ff1:	48 c1 ea 12          	shr    $0x12,%rdx
  402ff5:	49 89 d1             	mov    %rdx,%r9
  402ff8:	ba 02 00 00 00       	mov    $0x2,%edx
  402ffd:	e8 be f1 ff ff       	call   4021c0 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  403002:	5a                   	pop    %rdx
  403003:	48 63 c5             	movslq %ebp,%rax
  403006:	59                   	pop    %rcx
  403007:	49 3b 46 68          	cmp    0x68(%r14),%rax
  40300b:	7c a3                	jl     402fb0 <main+0xcd0>
  for (int x = 0 ; x < thread_count ; x++) {
  40300d:	48 83 04 24 18       	addq   $0x18,(%rsp)
  403012:	49 81 c6 b0 00 00 00 	add    $0xb0,%r14
  403019:	83 7c 24 08 06       	cmpl   $0x6,0x8(%rsp)
  40301e:	0f 85 ac fd ff ff    	jne    402dd0 <main+0xaf0>
  403024:	48 89 da             	mov    %rbx,%rdx
  403027:	48 8d 35 9f 33 00 00 	lea    0x339f(%rip),%rsi        # 4063cd <_IO_stdin_used+0x3cd>
  40302e:	31 c0                	xor    %eax,%eax
  403030:	4c 89 3c 24          	mov    %r15,(%rsp)
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
  403034:	49 be 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r14
  40303e:	bf 01 00 00 00       	mov    $0x1,%edi
  403043:	e8 78 f1 ff ff       	call   4021c0 <__printf_chk@plt>
  403048:	bf 0a 00 00 00       	mov    $0xa,%edi
  40304d:	e8 ee ef ff ff       	call   402040 <putchar@plt>
  403052:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
  40305a:	bf 01 00 00 00       	mov    $0x1,%edi
  40305f:	48 8d 35 3a 36 00 00 	lea    0x363a(%rip),%rsi        # 4066a0 <_IO_stdin_used+0x6a0>
  403066:	48 8b 50 08          	mov    0x8(%rax),%rdx
  40306a:	31 c0                	xor    %eax,%eax
  40306c:	e8 4f f1 ff ff       	call   4021c0 <__printf_chk@plt>
  403071:	4c 89 e8             	mov    %r13,%rax
  403074:	49 c1 fd 3f          	sar    $0x3f,%r13
  403078:	48 8d 35 49 36 00 00 	lea    0x3649(%rip),%rsi        # 4066c8 <_IO_stdin_used+0x6c8>
  40307f:	49 f7 ee             	imul   %r14
  403082:	bf 01 00 00 00       	mov    $0x1,%edi
  403087:	31 c0                	xor    %eax,%eax
  403089:	48 d1 fa             	sar    %rdx
  40308c:	4c 29 ea             	sub    %r13,%rdx
  40308f:	e8 2c f1 ff ff       	call   4021c0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
  403094:	4c 89 e0             	mov    %r12,%rax
  403097:	49 c1 fc 3f          	sar    $0x3f,%r12
  40309b:	48 8d 35 56 36 00 00 	lea    0x3656(%rip),%rsi        # 4066f8 <_IO_stdin_used+0x6f8>
  4030a2:	49 f7 ee             	imul   %r14
  4030a5:	bf 01 00 00 00       	mov    $0x1,%edi
  4030aa:	31 c0                	xor    %eax,%eax
  4030ac:	48 d1 fa             	sar    %rdx
  4030af:	4c 29 e2             	sub    %r12,%rdx
  4030b2:	e8 09 f1 ff ff       	call   4021c0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
  4030b7:	48 89 d8             	mov    %rbx,%rax
  4030ba:	48 c1 fb 3f          	sar    $0x3f,%rbx
  4030be:	48 8d 35 63 36 00 00 	lea    0x3663(%rip),%rsi        # 406728 <_IO_stdin_used+0x728>
  4030c5:	49 f7 ee             	imul   %r14
  4030c8:	bf 01 00 00 00       	mov    $0x1,%edi
  4030cd:	31 c0                	xor    %eax,%eax
  4030cf:	48 d1 fa             	sar    %rdx
  4030d2:	48 29 da             	sub    %rbx,%rdx
  4030d5:	e8 e6 f0 ff ff       	call   4021c0 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
  4030da:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  4030df:	bf 01 00 00 00       	mov    $0x1,%edi
  4030e4:	48 8d 35 f6 32 00 00 	lea    0x32f6(%rip),%rsi        # 4063e1 <_IO_stdin_used+0x3e1>
  4030eb:	49 f7 ee             	imul   %r14
  4030ee:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  4030f3:	48 c1 f8 3f          	sar    $0x3f,%rax
  4030f7:	48 d1 fa             	sar    %rdx
  4030fa:	48 29 c2             	sub    %rax,%rdx
  4030fd:	31 c0                	xor    %eax,%eax
  4030ff:	e8 bc f0 ff ff       	call   4021c0 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
  403104:	48 8b 04 24          	mov    (%rsp),%rax
  403108:	bf 01 00 00 00       	mov    $0x1,%edi
  40310d:	48 8d 35 de 32 00 00 	lea    0x32de(%rip),%rsi        # 4063f2 <_IO_stdin_used+0x3f2>
  403114:	49 f7 ee             	imul   %r14
  403117:	48 8b 04 24          	mov    (%rsp),%rax
  40311b:	48 c1 f8 3f          	sar    $0x3f,%rax
  40311f:	48 d1 fa             	sar    %rdx
  403122:	48 29 c2             	sub    %rax,%rdx
  403125:	31 c0                	xor    %eax,%eax
  403127:	e8 94 f0 ff ff       	call   4021c0 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
  40312c:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
  403134:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  40313d:	75 7b                	jne    4031ba <main+0xeda>
  40313f:	48 81 c4 a8 00 00 00 	add    $0xa8,%rsp
  403146:	31 c0                	xor    %eax,%eax
  403148:	5b                   	pop    %rbx
  403149:	5d                   	pop    %rbp
  40314a:	41 5c                	pop    %r12
  40314c:	41 5d                	pop    %r13
  40314e:	41 5e                	pop    %r14
  403150:	41 5f                	pop    %r15
  403152:	c3                   	ret
  403153:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          thread_data[x].tasks[y].run = barriered_work; 
  403158:	48 c7 c0 a0 50 40 00 	mov    $0x4050a0,%rax
  40315f:	41 bf 02 00 00 00    	mov    $0x2,%r15d
  403165:	49 89 84 24 98 00 00 00 	mov    %rax,0x98(%r12)
      for (int y = 0 ; y < total_barrier_count ; y++) {
  40316d:	e9 e2 f6 ff ff       	jmp    402854 <main+0x574>
      other = abs(x - 1) % total_threads;
  403172:	49 8d 8d 50 ff ff ff 	lea    -0xb0(%r13),%rcx
      my_thread_data[1] = &thread_data[x]; 
  403179:	4c 89 6b 08          	mov    %r13,0x8(%rbx)
  40317d:	4d 89 e8             	mov    %r13,%r8
  403180:	31 c0                	xor    %eax,%eax
      my_thread_data[0] = &thread_data[other]; 
  403182:	48 89 0b             	mov    %rcx,(%rbx)
  403185:	44 89 f2             	mov    %r14d,%edx
  403188:	bf 01 00 00 00       	mov    $0x1,%edi
  40318d:	45 8d 7e ff          	lea    -0x1(%r14),%r15d
      thread_data[x].thread_index = 1;
  403191:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
  403199:	48 8d 35 5b 31 00 00 	lea    0x315b(%rip),%rsi        # 4062fb <_IO_stdin_used+0x2fb>
  4031a0:	e8 1b f0 ff ff       	call   4021c0 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
  4031a5:	48 8d 45 18          	lea    0x18(%rbp),%rax
  4031a9:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  4031ae:	e9 9d f3 ff ff       	jmp    402550 <main+0x270>
    long v = 0;
  4031b3:	31 d2                	xor    %edx,%edx
  4031b5:	e9 94 fc ff ff       	jmp    402e4e <main+0xb6e>
}
  4031ba:	e8 e1 ee ff ff       	call   4020a0 <__stack_chk_fail@plt>
  4031bf:	90                   	nop

00000000004031c0 <_start>:
  4031c0:	f3 0f 1e fa          	endbr64
  4031c4:	31 ed                	xor    %ebp,%ebp
  4031c6:	49 89 d1             	mov    %rdx,%r9
  4031c9:	5e                   	pop    %rsi
  4031ca:	48 89 e2             	mov    %rsp,%rdx
  4031cd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  4031d1:	50                   	push   %rax
  4031d2:	54                   	push   %rsp
  4031d3:	45 31 c0             	xor    %r8d,%r8d
  4031d6:	31 c9                	xor    %ecx,%ecx
  4031d8:	48 c7 c7 e0 22 40 00 	mov    $0x4022e0,%rdi
  4031df:	ff 15 f3 5d 00 00    	call   *0x5df3(%rip)        # 408fd8 <__libc_start_main@GLIBC_2.34>
  4031e5:	f4                   	hlt
  4031e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004031f0 <_dl_relocate_static_pie>:
  4031f0:	f3 0f 1e fa          	endbr64
  4031f4:	c3                   	ret
  4031f5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4031ff:	90                   	nop

0000000000403200 <deregister_tm_clones>:
  403200:	b8 20 90 40 00       	mov    $0x409020,%eax
  403205:	48 3d 20 90 40 00    	cmp    $0x409020,%rax
  40320b:	74 13                	je     403220 <deregister_tm_clones+0x20>
  40320d:	b8 00 00 00 00       	mov    $0x0,%eax
  403212:	48 85 c0             	test   %rax,%rax
  403215:	74 09                	je     403220 <deregister_tm_clones+0x20>
  403217:	bf 20 90 40 00       	mov    $0x409020,%edi
  40321c:	ff e0                	jmp    *%rax
  40321e:	66 90                	xchg   %ax,%ax
  403220:	c3                   	ret
  403221:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40322c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000403230 <register_tm_clones>:
  403230:	be 20 90 40 00       	mov    $0x409020,%esi
  403235:	48 81 ee 20 90 40 00 	sub    $0x409020,%rsi
  40323c:	48 89 f0             	mov    %rsi,%rax
  40323f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  403243:	48 c1 f8 03          	sar    $0x3,%rax
  403247:	48 01 c6             	add    %rax,%rsi
  40324a:	48 d1 fe             	sar    %rsi
  40324d:	74 11                	je     403260 <register_tm_clones+0x30>
  40324f:	b8 00 00 00 00       	mov    $0x0,%eax
  403254:	48 85 c0             	test   %rax,%rax
  403257:	74 07                	je     403260 <register_tm_clones+0x30>
  403259:	bf 20 90 40 00       	mov    $0x409020,%edi
  40325e:	ff e0                	jmp    *%rax
  403260:	c3                   	ret
  403261:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40326c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000403270 <__do_global_dtors_aux>:
  403270:	f3 0f 1e fa          	endbr64
  403274:	80 3d a5 5d 00 00 00 	cmpb   $0x0,0x5da5(%rip)        # 409020 <__TMC_END__>
  40327b:	75 13                	jne    403290 <__do_global_dtors_aux+0x20>
  40327d:	55                   	push   %rbp
  40327e:	48 89 e5             	mov    %rsp,%rbp
  403281:	e8 7a ff ff ff       	call   403200 <deregister_tm_clones>
  403286:	c6 05 93 5d 00 00 01 	movb   $0x1,0x5d93(%rip)        # 409020 <__TMC_END__>
  40328d:	5d                   	pop    %rbp
  40328e:	c3                   	ret
  40328f:	90                   	nop
  403290:	c3                   	ret
  403291:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40329c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004032a0 <frame_dummy>:
  4032a0:	f3 0f 1e fa          	endbr64
  4032a4:	eb 8a                	jmp    403230 <register_tm_clones>
  4032a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000004032b0 <do_protected_write>:
  struct ProtectedState *protected = data->thread->protected_state;
  4032b0:	48 8b 87 a8 00 00 00 	mov    0xa8(%rdi),%rax
  4032b7:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
  4032bb:	48 83 87 90 00 00 00 01 	addq   $0x1,0x90(%rdi)
  if (protected->balance > 0) {
  4032c3:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
  4032c7:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
  4032cb:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
  4032d2:	48 85 c9             	test   %rcx,%rcx
  4032d5:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
  4032dc:	48 0f 4f d6          	cmovg  %rsi,%rdx
  4032e0:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
  4032e4:	31 c0                	xor    %eax,%eax
  4032e6:	c3                   	ret
  4032e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000004032f0 <barriered_reset>:
    for (int x = 0 ; x < data->task_count ; x++) {
  4032f0:	48 63 87 bc 00 00 00 	movslq 0xbc(%rdi),%rax
  4032f7:	85 c0                	test   %eax,%eax
  4032f9:	7e 4b                	jle    403346 <barriered_reset+0x56>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
  4032fb:	48 8b 8f a8 00 00 00 	mov    0xa8(%rdi),%rcx
  403302:	48 63 b7 b0 00 00 00 	movslq 0xb0(%rdi),%rsi
  403309:	48 8b 51 10          	mov    0x10(%rcx),%rdx
  40330d:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
  403311:	48 8b 71 28          	mov    0x28(%rcx),%rsi
  403315:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
  403319:	31 c0                	xor    %eax,%eax
  40331b:	48 c1 e1 07          	shl    $0x7,%rcx
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
  40331f:	48 8b 52 28          	mov    0x28(%rdx),%rdx
  403323:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  403328:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
  403330:	c7 84 06 b8 00 00 00 01 00 00 00 	movl   $0x1,0xb8(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
  40333b:	48 05 80 01 00 00    	add    $0x180,%rax
  403341:	48 39 c1             	cmp    %rax,%rcx
  403344:	75 e2                	jne    403328 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
  403346:	0f ae f8             	sfence
}
  403349:	31 c0                	xor    %eax,%eax
  40334b:	c3                   	ret
  40334c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000403350 <barriered_thread>:
  while (data->running == 1) {
  403350:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
  403354:	0f 85 1e 02 00 00    	jne    403578 <barriered_thread+0x228>
void* barriered_thread(void *arg) {
  40335a:	41 54                	push   %r12
  int waiting = 0;
  40335c:	45 31 c9             	xor    %r9d,%r9d
  40335f:	49 89 fc             	mov    %rdi,%r12
void* barriered_thread(void *arg) {
  403362:	55                   	push   %rbp
  int t = 0;
  403363:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
  403365:	53                   	push   %rbx
    if (t >= data->task_count) {
  403366:	44 8b 47 30          	mov    0x30(%rdi),%r8d
  40336a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  403370:	44 39 c5             	cmp    %r8d,%ebp
  403373:	7c 27                	jl     40339c <barriered_thread+0x4c>
      data->cycles++;
  403375:	49 83 84 24 98 00 00 00 01 	addq   $0x1,0x98(%r12)
      t = 0;
  40337e:	31 ed                	xor    %ebp,%ebp
    for (; t < data->task_count; t++) {
  403380:	45 85 c0             	test   %r8d,%r8d
  403383:	7f 17                	jg     40339c <barriered_thread+0x4c>
  403385:	e9 46 01 00 00       	jmp    4034d0 <barriered_thread+0x180>
  40338a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  403390:	83 c5 01             	add    $0x1,%ebp
  403393:	44 39 c5             	cmp    %r8d,%ebp
  403396:	0f 8d 34 01 00 00    	jge    4034d0 <barriered_thread+0x180>
      if (data->tasks[t].available == 1) {
  40339c:	48 63 c5             	movslq %ebp,%rax
  40339f:	48 8d 1c 40          	lea    (%rax,%rax,2),%rbx
  4033a3:	49 8b 44 24 28       	mov    0x28(%r12),%rax
  4033a8:	48 c1 e3 07          	shl    $0x7,%rbx
  4033ac:	48 01 d8             	add    %rbx,%rax
  4033af:	83 b8 b8 00 00 00 01 	cmpl   $0x1,0xb8(%rax)
  4033b6:	75 d8                	jne    403390 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
  4033b8:	45 8b 5c 24 18       	mov    0x18(%r12),%r11d
  4033bd:	8d 4d ff             	lea    -0x1(%rbp),%ecx
  4033c0:	41 8d 50 ff          	lea    -0x1(%r8),%edx
  4033c4:	85 ed                	test   %ebp,%ebp
  4033c6:	0f 4f d1             	cmovg  %ecx,%edx
  4033c9:	45 85 db             	test   %r11d,%r11d
  4033cc:	7e 58                	jle    403426 <barriered_thread+0xd6>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  4033ce:	48 63 d2             	movslq %edx,%rdx
  4033d1:	8b b8 80 00 00 00    	mov    0x80(%rax),%edi
  4033d7:	41 8d 73 ff          	lea    -0x1(%r11),%esi
        int arrived = 0; 
  4033db:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  4033de:	48 8d 0c 52          	lea    (%rdx,%rdx,2),%rcx
  4033e2:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
  4033e7:	48 c1 e1 07          	shl    $0x7,%rcx
  4033eb:	48 8d 42 08          	lea    0x8(%rdx),%rax
  4033ef:	48 8d 34 f0          	lea    (%rax,%rsi,8),%rsi
  4033f3:	eb 07                	jmp    4033fc <barriered_thread+0xac>
  4033f5:	0f 1f 00             	nopl   (%rax)
  4033f8:	48 83 c0 08          	add    $0x8,%rax
  4033fc:	48 8b 12             	mov    (%rdx),%rdx
  4033ff:	48 8b 52 28          	mov    0x28(%rdx),%rdx
  403403:	3b bc 0a 80 00 00 00 	cmp    0x80(%rdx,%rcx,1),%edi
  40340a:	75 04                	jne    403410 <barriered_thread+0xc0>
            arrived++;
  40340c:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
  403410:	48 89 c2             	mov    %rax,%rdx
  403413:	48 39 f0             	cmp    %rsi,%rax
  403416:	75 e0                	jne    4033f8 <barriered_thread+0xa8>
        if (arrived == 0 || arrived == data->thread_count) {
  403418:	45 85 d2             	test   %r10d,%r10d
  40341b:	74 09                	je     403426 <barriered_thread+0xd6>
  40341d:	45 39 d3             	cmp    %r10d,%r11d
  403420:	0f 85 aa 00 00 00    	jne    4034d0 <barriered_thread+0x180>
          if (waiting == 1) {
  403426:	41 83 f9 01          	cmp    $0x1,%r9d
  40342a:	0f 84 e8 00 00 00    	je     403518 <barriered_thread+0x1c8>
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
  403430:	85 ed                	test   %ebp,%ebp
  403432:	75 10                	jne    403444 <barriered_thread+0xf4>
  403434:	49 8b 74 24 70       	mov    0x70(%r12),%rsi
  403439:	49 3b 74 24 78       	cmp    0x78(%r12),%rsi
  40343e:	0f 8c 1c 01 00 00    	jl     403560 <barriered_thread+0x210>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
  403444:	49 63 0c 24          	movslq (%r12),%rcx
  403448:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
          data->tasks[t].available = 0;
  40344d:	49 8b 44 24 28       	mov    0x28(%r12),%rax
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
  403452:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
          data->tasks[t].available = 0;
  403456:	48 01 d8             	add    %rbx,%rax
  403459:	c7 80 b8 00 00 00 00 00 00 00 	movl   $0x0,0xb8(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
  403463:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
  403467:	48 01 df             	add    %rbx,%rdi
  40346a:	ff 90 98 00 00 00    	call   *0x98(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  403470:	41 8b 44 24 30       	mov    0x30(%r12),%eax
          data->tasks[t].arrived++;
  403475:	49 03 5c 24 28       	add    0x28(%r12),%rbx
  40347a:	83 83 80 00 00 00 01 	addl   $0x1,0x80(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  403481:	83 e8 01             	sub    $0x1,%eax
          data->iteration_count++;
  403484:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  40348a:	39 e8                	cmp    %ebp,%eax
  40348c:	74 5a                	je     4034e8 <barriered_thread+0x198>
          asm volatile ("sfence" ::: "memory");
  40348e:	0f ae f8             	sfence
            data->task_snapshot[data->task_timestamp_count].task = t;
  403491:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
  403499:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
  40349e:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  4034a2:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
  4034aa:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
  4034ae:	89 6e 20             	mov    %ebp,0x20(%rsi)
    for (; t < data->task_count; t++) {
  4034b1:	83 c5 01             	add    $0x1,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
  4034b4:	e8 c7 eb ff ff       	call   402080 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
  4034b9:	45 8b 44 24 30       	mov    0x30(%r12),%r8d
            waiting = 1;
  4034be:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    for (; t < data->task_count; t++) {
  4034c4:	44 39 c5             	cmp    %r8d,%ebp
  4034c7:	0f 8c cf fe ff ff    	jl     40339c <barriered_thread+0x4c>
  4034cd:	0f 1f 00             	nopl   (%rax)
  while (data->running == 1) {
  4034d0:	41 83 7c 24 34 01    	cmpl   $0x1,0x34(%r12)
  4034d6:	0f 84 94 fe ff ff    	je     403370 <barriered_thread+0x20>
}
  4034dc:	5b                   	pop    %rbx
  4034dd:	31 c0                	xor    %eax,%eax
  4034df:	5d                   	pop    %rbp
  4034e0:	41 5c                	pop    %r12
  4034e2:	c3                   	ret
  4034e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  4034e8:	49 8b 74 24 70       	mov    0x70(%r12),%rsi
  4034ed:	49 3b 74 24 78       	cmp    0x78(%r12),%rsi
  4034f2:	7d 9a                	jge    40348e <barriered_thread+0x13e>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
  4034f4:	48 c1 e6 04          	shl    $0x4,%rsi
  4034f8:	bf 04 00 00 00       	mov    $0x4,%edi
  4034fd:	49 03 74 24 60       	add    0x60(%r12),%rsi
  403502:	e8 79 eb ff ff       	call   402080 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
  403507:	49 83 44 24 70 01    	addq   $0x1,0x70(%r12)
  40350d:	e9 7c ff ff ff       	jmp    40348e <barriered_thread+0x13e>
  403512:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
  403518:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
  403520:	bf 04 00 00 00       	mov    $0x4,%edi
  403525:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  403529:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
  403531:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
  403536:	e8 45 eb ff ff       	call   402080 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
  40353b:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
  403543:	48 83 c0 01          	add    $0x1,%rax
  403547:	48 99                	cqto
  403549:	49 f7 bc 24 90 00 00 00 	idivq  0x90(%r12)
  403551:	49 89 94 24 88 00 00 00 	mov    %rdx,0x88(%r12)
            waiting = 0; 
  403559:	e9 d2 fe ff ff       	jmp    403430 <barriered_thread+0xe0>
  40355e:	66 90                	xchg   %ax,%ax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
  403560:	48 c1 e6 04          	shl    $0x4,%rsi
  403564:	bf 04 00 00 00       	mov    $0x4,%edi
  403569:	49 03 74 24 58       	add    0x58(%r12),%rsi
  40356e:	e8 0d eb ff ff       	call   402080 <clock_gettime@plt>
  403573:	e9 cc fe ff ff       	jmp    403444 <barriered_thread+0xf4>
}
  403578:	31 c0                	xor    %eax,%eax
  40357a:	c3                   	ret
  40357b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000403580 <external_thread>:
void * external_thread(void *arg) {
  403580:	41 55                	push   %r13
  403582:	41 54                	push   %r12
  403584:	55                   	push   %rbp
  403585:	53                   	push   %rbx
  403586:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
  40358a:	66 0f 6f 05 ae 33 00 00 	movdqa 0x33ae(%rip),%xmm0        # 406940 <_IO_stdin_used+0x940>
void * external_thread(void *arg) {
  403592:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40359b:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  4035a0:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
  4035a2:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
  struct timespec req = {
  4035a6:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
  4035aa:	75 67                	jne    403613 <external_thread+0x93>
  4035ac:	49 89 fd             	mov    %rdi,%r13
  4035af:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
  4035b4:	48 89 e5             	mov    %rsp,%rbp
        data->buffers->buffer[x].data = "Hello world";
  4035b7:	48 8d 1d 46 2a 00 00 	lea    0x2a46(%rip),%rbx        # 406004 <_IO_stdin_used+0x4>
  4035be:	66 90                	xchg   %ax,%ax
    nanosleep(&req , &rem);
  4035c0:	4c 89 e6             	mov    %r12,%rsi
  4035c3:	48 89 ef             	mov    %rbp,%rdi
  4035c6:	e8 f5 ea ff ff       	call   4020c0 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
  4035cb:	49 8b 45 40          	mov    0x40(%r13),%rax
  4035cf:	8b 10                	mov    (%rax),%edx
  4035d1:	85 d2                	test   %edx,%edx
  4035d3:	7e 34                	jle    403609 <external_thread+0x89>
      if (data->buffers->buffer[x].available == 0) {
  4035d5:	48 8b 48 08          	mov    0x8(%rax),%rcx
  4035d9:	83 ea 01             	sub    $0x1,%edx
  4035dc:	48 c1 e2 04          	shl    $0x4,%rdx
  4035e0:	48 8d 41 08          	lea    0x8(%rcx),%rax
  4035e4:	48 8d 54 11 18       	lea    0x18(%rcx,%rdx,1),%rdx
  4035e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  4035f0:	8b 08                	mov    (%rax),%ecx
  4035f2:	85 c9                	test   %ecx,%ecx
  4035f4:	75 0a                	jne    403600 <external_thread+0x80>
        data->buffers->buffer[x].data = "Hello world";
  4035f6:	48 89 58 f8          	mov    %rbx,-0x8(%rax)
        data->buffers->buffer[x].available = 1;
  4035fa:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
  403600:	48 83 c0 10          	add    $0x10,%rax
  403604:	48 39 d0             	cmp    %rdx,%rax
  403607:	75 e7                	jne    4035f0 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
  403609:	0f ae f0             	mfence
  while (data->running == 1) {
  40360c:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
  403611:	74 ad                	je     4035c0 <external_thread+0x40>
}
  403613:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
  403618:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  403621:	75 0d                	jne    403630 <external_thread+0xb0>
  403623:	48 83 c4 38          	add    $0x38,%rsp
  403627:	31 c0                	xor    %eax,%eax
  403629:	5b                   	pop    %rbx
  40362a:	5d                   	pop    %rbp
  40362b:	41 5c                	pop    %r12
  40362d:	41 5d                	pop    %r13
  40362f:	c3                   	ret
  403630:	e8 6b ea ff ff       	call   4020a0 <__stack_chk_fail@plt>
  403635:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000403640 <timer_thread>:
void* timer_thread(void *arg) {
  403640:	41 57                	push   %r15
  403642:	48 8d 35 c7 29 00 00 	lea    0x29c7(%rip),%rsi        # 406010 <_IO_stdin_used+0x10>
  403649:	49 89 ff             	mov    %rdi,%r15
  40364c:	41 56                	push   %r14
  40364e:	41 55                	push   %r13
  403650:	41 54                	push   %r12
  403652:	55                   	push   %rbp
  403653:	53                   	push   %rbx
  403654:	48 83 ec 58          	sub    $0x58,%rsp
  403658:	8b 17                	mov    (%rdi),%edx
  40365a:	bf 01 00 00 00       	mov    $0x1,%edi
  40365f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  403668:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  40366d:	31 c0                	xor    %eax,%eax
  40366f:	e8 4c eb ff ff       	call   4021c0 <__printf_chk@plt>
  struct timespec preempt = {
  403674:	66 0f 6f 05 c4 32 00 00 	movdqa 0x32c4(%rip),%xmm0        # 406940 <_IO_stdin_used+0x940>
  40367c:	ba 88 13 00 00       	mov    $0x1388,%edx
  403681:	31 c0                	xor    %eax,%eax
  403683:	48 8d 35 98 29 00 00 	lea    0x2998(%rip),%rsi        # 406022 <_IO_stdin_used+0x22>
  40368a:	bf 01 00 00 00       	mov    $0x1,%edi
  40368f:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
  403694:	e8 27 eb ff ff       	call   4021c0 <__printf_chk@plt>
  while (data->running && n < times) {
  403699:	4d 63 77 34          	movslq 0x34(%r15),%r14
  40369d:	45 85 f6             	test   %r14d,%r14d
  4036a0:	0f 84 ad 00 00 00    	je     403753 <timer_thread+0x113>
  int n = 0;
  4036a6:	31 ed                	xor    %ebp,%ebp
  int y = 0;
  4036a8:	45 31 f6             	xor    %r14d,%r14d
  4036ab:	49 89 e5             	mov    %rsp,%r13
      y = 0;
  4036ae:	31 db                	xor    %ebx,%ebx
  4036b0:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
    nanosleep(&preempt , &rem2);
  4036b5:	4c 89 e7             	mov    %r12,%rdi
  4036b8:	4c 89 ee             	mov    %r13,%rsi
    n++;
  4036bb:	83 c5 01             	add    $0x1,%ebp
    nanosleep(&preempt , &rem2);
  4036be:	e8 fd e9 ff ff       	call   4020c0 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
  4036c3:	41 8b 57 18          	mov    0x18(%r15),%edx
    y++;
  4036c7:	41 8d 7e 01          	lea    0x1(%r14),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
  4036cb:	85 d2                	test   %edx,%edx
  4036cd:	7e 5d                	jle    40372c <timer_thread+0xec>
  4036cf:	49 8b 47 10          	mov    0x10(%r15),%rax
        data->threads[x]->tasks[y].scheduled = 0;
  4036d3:	4f 8d 04 76          	lea    (%r14,%r14,2),%r8
  4036d7:	83 ea 01             	sub    $0x1,%edx
  4036da:	49 c1 e0 07          	shl    $0x7,%r8
  4036de:	48 8d 48 08          	lea    0x8(%rax),%rcx
  4036e2:	4c 8d 0c d1          	lea    (%rcx,%rdx,8),%r9
  4036e6:	eb 0c                	jmp    4036f4 <timer_thread+0xb4>
  4036e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  4036f0:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
  4036f4:	4c 8b 10             	mov    (%rax),%r10
  4036f7:	89 f8                	mov    %edi,%eax
  4036f9:	99                   	cltd
  4036fa:	41 f7 7a 30          	idivl  0x30(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
  4036fe:	49 8b 72 28          	mov    0x28(%r10),%rsi
  403702:	48 63 d2             	movslq %edx,%rdx
  403705:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
  403709:	48 c1 e0 07          	shl    $0x7,%rax
  40370d:	c7 84 06 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rsi,%rax,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
  403718:	48 89 c8             	mov    %rcx,%rax
        data->threads[x]->tasks[y].scheduled = 0;
  40371b:	42 c7 84 06 c0 00 00 00 00 00 00 00 	movl   $0x0,0xc0(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
  403727:	49 39 c9             	cmp    %rcx,%r9
  40372a:	75 c4                	jne    4036f0 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
  40372c:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
  40372f:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
  403733:	41 8b 57 34          	mov    0x34(%r15),%edx
    if (y >= data->threads[0]->task_count) {
  403737:	48 8b 00             	mov    (%rax),%rax
      y = 0;
  40373a:	39 78 30             	cmp    %edi,0x30(%rax)
  40373d:	0f 4e fb             	cmovle %ebx,%edi
  403740:	4c 63 f7             	movslq %edi,%r14
  while (data->running && n < times) {
  403743:	85 d2                	test   %edx,%edx
  403745:	74 0c                	je     403753 <timer_thread+0x113>
  403747:	81 fd 88 13 00 00    	cmp    $0x1388,%ebp
  40374d:	0f 85 62 ff ff ff    	jne    4036b5 <timer_thread+0x75>
  403753:	48 8d 3d de 28 00 00 	lea    0x28de(%rip),%rdi        # 406038 <_IO_stdin_used+0x38>
  40375a:	e8 01 e9 ff ff       	call   402060 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
  40375f:	49 63 47 1c          	movslq 0x1c(%r15),%rax
  403763:	85 c0                	test   %eax,%eax
  403765:	7e 5b                	jle    4037c2 <timer_thread+0x182>
    for (int y = 0 ; y < data->task_count ; y++) {
  403767:	41 8b 57 30          	mov    0x30(%r15),%edx
  40376b:	85 d2                	test   %edx,%edx
  40376d:	7e 53                	jle    4037c2 <timer_thread+0x182>
  40376f:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
  403777:	8d 42 ff             	lea    -0x1(%rdx),%eax
      data->threads[x]->tasks[y].sending = 0;
  40377a:	4d 8b 47 10          	mov    0x10(%r15),%r8
  40377e:	31 f6                	xor    %esi,%esi
  403780:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
  403784:	48 c1 e0 07          	shl    $0x7,%rax
  403788:	48 8d b8 78 02 00 00 	lea    0x278(%rax),%rdi
  40378f:	49 8b 04 30          	mov    (%r8,%rsi,1),%rax
  403793:	48 8b 50 28          	mov    0x28(%rax),%rdx
  403797:	48 8d 82 f8 00 00 00 	lea    0xf8(%rdx),%rax
  40379e:	48 01 fa             	add    %rdi,%rdx
  4037a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  4037a8:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
  4037ae:	48 05 80 01 00 00    	add    $0x180,%rax
  4037b4:	48 39 d0             	cmp    %rdx,%rax
  4037b7:	75 ef                	jne    4037a8 <timer_thread+0x168>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
  4037b9:	48 83 c6 08          	add    $0x8,%rsi
  4037bd:	48 39 f1             	cmp    %rsi,%rcx
  4037c0:	75 cd                	jne    40378f <timer_thread+0x14f>
  asm volatile ("mfence" ::: "memory");
  4037c2:	0f ae f0             	mfence
  struct timespec drain = {
  4037c5:	66 0f 6f 05 83 31 00 00 	movdqa 0x3183(%rip),%xmm0        # 406950 <_IO_stdin_used+0x950>
  4037cd:	48 8d 2d 89 28 00 00 	lea    0x2889(%rip),%rbp        # 40605d <_IO_stdin_used+0x5d>
  4037d4:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
  4037d9:	41 8b 57 18          	mov    0x18(%r15),%edx
    y++;
  4037dd:	45 8d 6e 01          	lea    0x1(%r14),%r13d
    for (int x = 0 ; x < data->thread_count ; x++) {
  4037e1:	85 d2                	test   %edx,%edx
  4037e3:	7e 56                	jle    40383b <timer_thread+0x1fb>
  4037e5:	49 8b 47 10          	mov    0x10(%r15),%rax
        data->threads[x]->tasks[y].scheduled = 0;
  4037e9:	4b 8d 3c 76          	lea    (%r14,%r14,2),%rdi
  4037ed:	83 ea 01             	sub    $0x1,%edx
  4037f0:	48 c1 e7 07          	shl    $0x7,%rdi
  4037f4:	48 8d 48 08          	lea    0x8(%rax),%rcx
  4037f8:	4c 8d 04 d1          	lea    (%rcx,%rdx,8),%r8
  4037fc:	eb 06                	jmp    403804 <timer_thread+0x1c4>
  4037fe:	66 90                	xchg   %ax,%ax
  403800:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
  403804:	48 8b 18             	mov    (%rax),%rbx
  403807:	44 89 e8             	mov    %r13d,%eax
  40380a:	99                   	cltd
  40380b:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
  40380e:	48 8b 73 28          	mov    0x28(%rbx),%rsi
  403812:	48 63 c2             	movslq %edx,%rax
  403815:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
  403819:	48 c1 e0 07          	shl    $0x7,%rax
  40381d:	c7 84 06 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rsi,%rax,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
  403828:	48 89 c8             	mov    %rcx,%rax
        data->threads[x]->tasks[y].scheduled = 0;
  40382b:	c7 84 3e c0 00 00 00 00 00 00 00 	movl   $0x0,0xc0(%rsi,%rdi,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
  403836:	49 39 c8             	cmp    %rcx,%r8
  403839:	75 c5                	jne    403800 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
  40383b:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
  40383e:	49 8b 47 10          	mov    0x10(%r15),%rax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  403842:	41 8b 7f 20          	mov    0x20(%r15),%edi
    if (y >= data->threads[0]->task_count) {
  403846:	48 8b 10             	mov    (%rax),%rdx
      y = 0;
  403849:	44 39 6a 30          	cmp    %r13d,0x30(%rdx)
  40384d:	ba 00 00 00 00       	mov    $0x0,%edx
  403852:	44 0f 4e ea          	cmovle %edx,%r13d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  403856:	85 ff                	test   %edi,%edi
  403858:	0f 8e c8 00 00 00    	jle    403926 <timer_thread+0x2e6>
  40385e:	45 31 e4             	xor    %r12d,%r12d
    int all_empty = 1;
  403861:	41 b9 01 00 00 00    	mov    $0x1,%r9d
  403867:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
  403870:	49 63 dc             	movslq %r12d,%rbx
      for (int y = 0 ; y < data->my_thread_count ; y++) {
  403873:	45 31 f6             	xor    %r14d,%r14d
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
  403876:	48 c1 e3 03          	shl    $0x3,%rbx
  40387a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  403880:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
  403884:	49 63 c6             	movslq %r14d,%rax
  403887:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
  40388b:	48 c1 e0 07          	shl    $0x7,%rax
  40388f:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
  403893:	31 d2                	xor    %edx,%edx
  403895:	48 8b 80 e8 00 00 00 	mov    0xe8(%rax),%rax
  40389c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
  4038a0:	48 8b 08             	mov    (%rax),%rcx
  4038a3:	48 8b 70 08          	mov    0x8(%rax),%rsi
  4038a7:	48 8b 49 08          	mov    0x8(%rcx),%rcx
  4038ab:	4c 8b 46 08          	mov    0x8(%rsi),%r8
  4038af:	48 85 c9             	test   %rcx,%rcx
  4038b2:	7f 24                	jg     4038d8 <timer_thread+0x298>
  4038b4:	4d 85 c0             	test   %r8,%r8
  4038b7:	7f 1f                	jg     4038d8 <timer_thread+0x298>
        for (int k = 0 ; k < data->my_thread_count; k++) {
  4038b9:	83 c2 01             	add    $0x1,%edx
  4038bc:	48 83 c0 20          	add    $0x20,%rax
  4038c0:	39 fa                	cmp    %edi,%edx
  4038c2:	7c dc                	jl     4038a0 <timer_thread+0x260>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
  4038c4:	41 83 c6 01          	add    $0x1,%r14d
  4038c8:	44 39 f7             	cmp    %r14d,%edi
  4038cb:	7e 2a                	jle    4038f7 <timer_thread+0x2b7>
  4038cd:	49 8b 47 10          	mov    0x10(%r15),%rax
  4038d1:	eb ad                	jmp    403880 <timer_thread+0x240>
  4038d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4038d8:	bf 01 00 00 00       	mov    $0x1,%edi
  4038dd:	48 89 ee             	mov    %rbp,%rsi
  4038e0:	31 c0                	xor    %eax,%eax
  4038e2:	41 83 c6 01          	add    $0x1,%r14d
  4038e6:	e8 d5 e8 ff ff       	call   4021c0 <__printf_chk@plt>
  4038eb:	41 8b 7f 20          	mov    0x20(%r15),%edi
            all_empty = 0;
  4038ef:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
  4038f2:	44 39 f7             	cmp    %r14d,%edi
  4038f5:	7f d6                	jg     4038cd <timer_thread+0x28d>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  4038f7:	41 83 c4 01          	add    $0x1,%r12d
  4038fb:	44 39 e7             	cmp    %r12d,%edi
  4038fe:	7e 09                	jle    403909 <timer_thread+0x2c9>
  403900:	49 8b 47 10          	mov    0x10(%r15),%rax
  403904:	e9 67 ff ff ff       	jmp    403870 <timer_thread+0x230>
    if (all_empty == 1) {
  403909:	41 83 f9 01          	cmp    $0x1,%r9d
  40390d:	74 17                	je     403926 <timer_thread+0x2e6>
      nanosleep(&drain , &drainrem);
  40390f:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
  403914:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
  403919:	4d 63 f5             	movslq %r13d,%r14
  40391c:	e8 9f e7 ff ff       	call   4020c0 <nanosleep@plt>
  403921:	e9 b3 fe ff ff       	jmp    4037d9 <timer_thread+0x199>
  403926:	48 8d 3d 27 27 00 00 	lea    0x2727(%rip),%rdi        # 406054 <_IO_stdin_used+0x54>
  40392d:	e8 2e e7 ff ff       	call   402060 <puts@plt>
  while (data->running) {
  403932:	41 8b 47 34          	mov    0x34(%r15),%eax
  403936:	85 c0                	test   %eax,%eax
  403938:	0f 84 bb 00 00 00    	je     4039f9 <timer_thread+0x3b9>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  40393e:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
  403942:	85 c9                	test   %ecx,%ecx
  403944:	7e 31                	jle    403977 <timer_thread+0x337>
  403946:	49 8b 47 10          	mov    0x10(%r15),%rax
  40394a:	31 db                	xor    %ebx,%ebx
  40394c:	4c 8d 25 1b 27 00 00 	lea    0x271b(%rip),%r12        # 40606e <_IO_stdin_used+0x6e>
  403953:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->threads[x]->running = 0;
  403958:	48 63 eb             	movslq %ebx,%rbp
  40395b:	48 8b 14 e8          	mov    (%rax,%rbp,8),%rdx
      if (data->threads[x]->type == IO) {
  40395f:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
  403963:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
  40396a:	0f 84 b6 00 00 00    	je     403a26 <timer_thread+0x3e6>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  403970:	83 c3 01             	add    $0x1,%ebx
  403973:	39 cb                	cmp    %ecx,%ebx
  403975:	7c e1                	jl     403958 <timer_thread+0x318>
    for (int x = 0 ; x < data->thread_count ; x++) {
  403977:	49 63 47 18          	movslq 0x18(%r15),%rax
  40397b:	85 c0                	test   %eax,%eax
  40397d:	7e 63                	jle    4039e2 <timer_thread+0x3a2>
      for (int y = 0 ; y < data->task_count ; y++) {
  40397f:	41 8b 57 30          	mov    0x30(%r15),%edx
  403983:	85 d2                	test   %edx,%edx
  403985:	7e 5b                	jle    4039e2 <timer_thread+0x3a2>
  403987:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
  40398f:	8d 42 ff             	lea    -0x1(%rdx),%eax
        data->threads[x]->tasks[y].scheduled = 0;
  403992:	4d 8b 47 10          	mov    0x10(%r15),%r8
  403996:	31 c9                	xor    %ecx,%ecx
  403998:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
  40399c:	48 c1 e0 07          	shl    $0x7,%rax
  4039a0:	48 8d b8 40 02 00 00 	lea    0x240(%rax),%rdi
  4039a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  4039b0:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
  4039b4:	48 8b 50 28          	mov    0x28(%rax),%rdx
  4039b8:	48 8d 82 c0 00 00 00 	lea    0xc0(%rdx),%rax
  4039bf:	48 01 fa             	add    %rdi,%rdx
  4039c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  4039c8:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
  4039ce:	48 05 80 01 00 00    	add    $0x180,%rax
  4039d4:	48 39 c2             	cmp    %rax,%rdx
  4039d7:	75 ef                	jne    4039c8 <timer_thread+0x388>
    for (int x = 0 ; x < data->thread_count ; x++) {
  4039d9:	48 83 c1 08          	add    $0x8,%rcx
  4039dd:	48 39 ce             	cmp    %rcx,%rsi
  4039e0:	75 ce                	jne    4039b0 <timer_thread+0x370>
    asm volatile ("mfence" ::: "memory");
  4039e2:	0f ae f0             	mfence
  4039e5:	48 8d 3d 94 26 00 00 	lea    0x2694(%rip),%rdi        # 406080 <_IO_stdin_used+0x80>
  4039ec:	e8 6f e6 ff ff       	call   402060 <puts@plt>
    data->running = 0;
  4039f1:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
  4039f9:	48 8d 3d 87 26 00 00 	lea    0x2687(%rip),%rdi        # 406087 <_IO_stdin_used+0x87>
  403a00:	e8 5b e6 ff ff       	call   402060 <puts@plt>
}
  403a05:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
  403a0a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  403a13:	75 46                	jne    403a5b <timer_thread+0x41b>
  403a15:	48 83 c4 58          	add    $0x58,%rsp
  403a19:	31 c0                	xor    %eax,%eax
  403a1b:	5b                   	pop    %rbx
  403a1c:	5d                   	pop    %rbp
  403a1d:	41 5c                	pop    %r12
  403a1f:	41 5d                	pop    %r13
  403a21:	41 5e                	pop    %r14
  403a23:	41 5f                	pop    %r15
  403a25:	c3                   	ret
  403a26:	4c 89 e7             	mov    %r12,%rdi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  403a29:	83 c3 01             	add    $0x1,%ebx
  403a2c:	e8 2f e6 ff ff       	call   402060 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
  403a31:	49 8b 47 10          	mov    0x10(%r15),%rax
  403a35:	be 01 00 00 00       	mov    $0x1,%esi
  403a3a:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
  403a3e:	8b 78 50             	mov    0x50(%rax),%edi
  403a41:	e8 2a e7 ff ff       	call   402170 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  403a46:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
  403a4a:	39 cb                	cmp    %ecx,%ebx
  403a4c:	0f 8d 25 ff ff ff    	jge    403977 <timer_thread+0x337>
  403a52:	49 8b 47 10          	mov    0x10(%r15),%rax
  403a56:	e9 fd fe ff ff       	jmp    403958 <timer_thread+0x318>
}
  403a5b:	e8 40 e6 ff ff       	call   4020a0 <__stack_chk_fail@plt>

0000000000403a60 <fatal_error>:
void fatal_error(const char *syscall) {
  403a60:	48 83 ec 08          	sub    $0x8,%rsp
    perror(syscall);
  403a64:	e8 97 e7 ff ff       	call   402200 <perror@plt>
    exit(1);
  403a69:	bf 01 00 00 00       	mov    $0x1,%edi
  403a6e:	e8 9d e7 ff ff       	call   402210 <exit@plt>
  403a73:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  403a7e:	66 90                	xchg   %ax,%ax

0000000000403a80 <strtolower>:
void strtolower(char *str) {
  403a80:	55                   	push   %rbp
  403a81:	53                   	push   %rbx
  403a82:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
  403a86:	48 0f be 1f          	movsbq (%rdi),%rbx
  403a8a:	84 db                	test   %bl,%bl
  403a8c:	74 28                	je     403ab6 <strtolower+0x36>
  403a8e:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
  403a91:	e8 ea e7 ff ff       	call   402280 <__ctype_tolower_loc@plt>
  403a96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  403aa0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
  403aa3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
  403aa7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
  403aaa:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
  403aad:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
  403ab2:	84 db                	test   %bl,%bl
  403ab4:	75 ea                	jne    403aa0 <strtolower+0x20>
}
  403ab6:	48 83 c4 08          	add    $0x8,%rsp
  403aba:	5b                   	pop    %rbx
  403abb:	5d                   	pop    %rbp
  403abc:	c3                   	ret
  403abd:	0f 1f 00             	nopl   (%rax)

0000000000403ac0 <zh_malloc>:
void *zh_malloc(size_t size) {
  403ac0:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
  403ac4:	e8 b7 e6 ff ff       	call   402180 <malloc@plt>
    if (!buf) {
  403ac9:	48 85 c0             	test   %rax,%rax
  403acc:	74 05                	je     403ad3 <zh_malloc+0x13>
}
  403ace:	48 83 c4 08          	add    $0x8,%rsp
  403ad2:	c3                   	ret
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
  403ad3:	48 8b 05 1e 55 00 00 	mov    0x551e(%rip),%rax        # 408ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  403ada:	ba 28 00 00 00       	mov    $0x28,%edx
  403adf:	be 01 00 00 00       	mov    $0x1,%esi
  403ae4:	48 8d 3d 1d 29 00 00 	lea    0x291d(%rip),%rdi        # 406408 <_IO_stdin_used+0x408>
  403aeb:	48 8b 08             	mov    (%rax),%rcx
  403aee:	e8 3d e7 ff ff       	call   402230 <fwrite@plt>
        exit(1);
  403af3:	bf 01 00 00 00       	mov    $0x1,%edi
  403af8:	e8 13 e7 ff ff       	call   402210 <exit@plt>
  403afd:	0f 1f 00             	nopl   (%rax)

0000000000403b00 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
  403b00:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
  403b01:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
  403b06:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
  403b09:	e8 c2 e5 ff ff       	call   4020d0 <strrchr@plt>
    if (!dot || dot == filename)
  403b0e:	48 85 c0             	test   %rax,%rax
  403b11:	74 0d                	je     403b20 <get_filename_ext+0x20>
  403b13:	48 39 c3             	cmp    %rax,%rbx
  403b16:	74 08                	je     403b20 <get_filename_ext+0x20>
    return dot + 1;
  403b18:	48 83 c0 01          	add    $0x1,%rax
}
  403b1c:	5b                   	pop    %rbx
  403b1d:	c3                   	ret
  403b1e:	66 90                	xchg   %ax,%ax
        return "";
  403b20:	48 8d 05 a8 25 00 00 	lea    0x25a8(%rip),%rax        # 4060cf <_IO_stdin_used+0xcf>
}
  403b27:	5b                   	pop    %rbx
  403b28:	c3                   	ret
  403b29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000403b30 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
  403b30:	41 55                	push   %r13
  403b32:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  403b35:	48 89 fe             	mov    %rdi,%rsi
  403b38:	41 54                	push   %r12
  return __builtin___memcpy_chk (__dest, __src, __len,
  403b3a:	41 bc 31 0d 00 00    	mov    $0xd31,%r12d
  403b40:	55                   	push   %rbp
  403b41:	53                   	push   %rbx
  403b42:	48 89 d3             	mov    %rdx,%rbx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  403b45:	ba 00 04 00 00       	mov    $0x400,%edx
  403b4a:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
  403b51:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  403b5a:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
  403b62:	31 c0                	xor    %eax,%eax
  403b64:	48 89 e5             	mov    %rsp,%rbp
  403b67:	48 89 ef             	mov    %rbp,%rdi
  403b6a:	e8 31 e6 ff ff       	call   4021a0 <__strcpy_chk@plt>
    strtolower(small_case_path);
  403b6f:	48 89 ef             	mov    %rbp,%rdi
  403b72:	e8 09 ff ff ff       	call   403a80 <strtolower>
    iov[0].iov_base = zh_malloc(slen);
  403b77:	bf 11 00 00 00       	mov    $0x11,%edi
  403b7c:	e8 3f ff ff ff       	call   403ac0 <zh_malloc>
    iov[0].iov_len = slen;
  403b81:	48 c7 43 08 11 00 00 00 	movq   $0x11,0x8(%rbx)
    iov[1].iov_base = zh_malloc(slen);
  403b89:	bf 17 00 00 00       	mov    $0x17,%edi
  return __builtin___memcpy_chk (__dest, __src, __len,
  403b8e:	66 0f 6f 05 ca 2d 00 00 	movdqa 0x2dca(%rip),%xmm0        # 406960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
  403b96:	48 89 03             	mov    %rax,(%rbx)
  403b99:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
  403b9d:	0f 11 00             	movups %xmm0,(%rax)
    iov[1].iov_base = zh_malloc(slen);
  403ba0:	e8 1b ff ff ff       	call   403ac0 <zh_malloc>
    iov[1].iov_len = slen;
  403ba5:	48 c7 43 18 17 00 00 00 	movq   $0x17,0x18(%rbx)
  403bad:	66 0f 6f 05 bb 2d 00 00 	movdqa 0x2dbb(%rip),%xmm0        # 406970 <_IO_stdin_used+0x970>
    const char *file_ext = get_filename_ext(small_case_path);
  403bb5:	48 89 ef             	mov    %rbp,%rdi
    iov[1].iov_base = zh_malloc(slen);
  403bb8:	48 89 43 10          	mov    %rax,0x10(%rbx)
  403bbc:	c7 40 10 64 2f 30 2e 	movl   $0x2e302f64,0x10(%rax)
  403bc3:	66 44 89 60 14       	mov    %r12w,0x14(%rax)
  403bc8:	c6 40 16 0a          	movb   $0xa,0x16(%rax)
  403bcc:	0f 11 00             	movups %xmm0,(%rax)
    const char *file_ext = get_filename_ext(small_case_path);
  403bcf:	e8 2c ff ff ff       	call   403b00 <get_filename_ext>
    if (strcmp("jpg", file_ext) == 0)
  403bd4:	48 8d 3d c2 24 00 00 	lea    0x24c2(%rip),%rdi        # 40609d <_IO_stdin_used+0x9d>
  403bdb:	48 89 c6             	mov    %rax,%rsi
    const char *file_ext = get_filename_ext(small_case_path);
  403bde:	48 89 c5             	mov    %rax,%rbp
    if (strcmp("jpg", file_ext) == 0)
  403be1:	e8 3a e5 ff ff       	call   402120 <strcmp@plt>
  403be6:	85 c0                	test   %eax,%eax
  403be8:	0f 84 42 03 00 00    	je     403f30 <send_headers+0x400>
    if (strcmp("jpeg", file_ext) == 0)
  403bee:	48 89 ee             	mov    %rbp,%rsi
  403bf1:	48 8d 3d a9 24 00 00 	lea    0x24a9(%rip),%rdi        # 4060a1 <_IO_stdin_used+0xa1>
  403bf8:	e8 23 e5 ff ff       	call   402120 <strcmp@plt>
  403bfd:	85 c0                	test   %eax,%eax
  403bff:	0f 84 eb 02 00 00    	je     403ef0 <send_headers+0x3c0>
    if (strcmp("png", file_ext) == 0)
  403c05:	48 89 ee             	mov    %rbp,%rsi
  403c08:	48 8d 3d 97 24 00 00 	lea    0x2497(%rip),%rdi        # 4060a6 <_IO_stdin_used+0xa6>
  403c0f:	e8 0c e5 ff ff       	call   402120 <strcmp@plt>
  403c14:	85 c0                	test   %eax,%eax
  403c16:	0f 84 04 04 00 00    	je     404020 <send_headers+0x4f0>
    if (strcmp("gif", file_ext) == 0)
  403c1c:	48 89 ee             	mov    %rbp,%rsi
  403c1f:	48 8d 3d 84 24 00 00 	lea    0x2484(%rip),%rdi        # 4060aa <_IO_stdin_used+0xaa>
  403c26:	e8 f5 e4 ff ff       	call   402120 <strcmp@plt>
  403c2b:	85 c0                	test   %eax,%eax
  403c2d:	0f 84 ad 03 00 00    	je     403fe0 <send_headers+0x4b0>
    if (strcmp("htm", file_ext) == 0)
  403c33:	48 89 ee             	mov    %rbp,%rsi
  403c36:	48 8d 3d 71 24 00 00 	lea    0x2471(%rip),%rdi        # 4060ae <_IO_stdin_used+0xae>
  403c3d:	e8 de e4 ff ff       	call   402120 <strcmp@plt>
  403c42:	85 c0                	test   %eax,%eax
  403c44:	0f 84 5e 03 00 00    	je     403fa8 <send_headers+0x478>
    if (strcmp("html", file_ext) == 0)
  403c4a:	48 89 ee             	mov    %rbp,%rsi
  403c4d:	48 8d 3d 9d 24 00 00 	lea    0x249d(%rip),%rdi        # 4060f1 <_IO_stdin_used+0xf1>
  403c54:	e8 c7 e4 ff ff       	call   402120 <strcmp@plt>
  403c59:	85 c0                	test   %eax,%eax
  403c5b:	0f 84 0f 03 00 00    	je     403f70 <send_headers+0x440>
    if (strcmp("js", file_ext) == 0)
  403c61:	80 7d 00 6a          	cmpb   $0x6a,0x0(%rbp)
  403c65:	75 0a                	jne    403c71 <send_headers+0x141>
  403c67:	80 7d 01 73          	cmpb   $0x73,0x1(%rbp)
  403c6b:	0f 84 b7 01 00 00    	je     403e28 <send_headers+0x2f8>
    if (strcmp("css", file_ext) == 0)
  403c71:	48 89 ee             	mov    %rbp,%rsi
  403c74:	48 8d 3d 37 24 00 00 	lea    0x2437(%rip),%rdi        # 4060b2 <_IO_stdin_used+0xb2>
  403c7b:	e8 a0 e4 ff ff       	call   402120 <strcmp@plt>
  403c80:	85 c0                	test   %eax,%eax
  403c82:	0f 84 f8 01 00 00    	je     403e80 <send_headers+0x350>
    if (strcmp("txt", file_ext) == 0)
  403c88:	48 89 ee             	mov    %rbp,%rsi
  403c8b:	48 8d 3d 24 24 00 00 	lea    0x2424(%rip),%rdi        # 4060b6 <_IO_stdin_used+0xb6>
  403c92:	e8 89 e4 ff ff       	call   402120 <strcmp@plt>
  403c97:	85 c0                	test   %eax,%eax
  403c99:	0f 84 11 02 00 00    	je     403eb0 <send_headers+0x380>
    slen = strlen(send_buffer);
  403c9f:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
  403ca7:	4c 89 e7             	mov    %r12,%rdi
  403caa:	e8 e1 e3 ff ff       	call   402090 <strlen@plt>
    iov[2].iov_base = zh_malloc(slen);
  403caf:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
  403cb2:	48 89 c5             	mov    %rax,%rbp
    iov[2].iov_base = zh_malloc(slen);
  403cb5:	e8 06 fe ff ff       	call   403ac0 <zh_malloc>
    iov[2].iov_len = slen;
  403cba:	48 89 6b 28          	mov    %rbp,0x28(%rbx)
    iov[2].iov_base = zh_malloc(slen);
  403cbe:	48 89 43 20          	mov    %rax,0x20(%rbx)
  403cc2:	83 fd 08             	cmp    $0x8,%ebp
  403cc5:	73 31                	jae    403cf8 <send_headers+0x1c8>
  403cc7:	40 f6 c5 04          	test   $0x4,%bpl
  403ccb:	0f 85 8f 03 00 00    	jne    404060 <send_headers+0x530>
  403cd1:	85 ed                	test   %ebp,%ebp
  403cd3:	74 55                	je     403d2a <send_headers+0x1fa>
  403cd5:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
  403cdd:	88 10                	mov    %dl,(%rax)
  403cdf:	40 f6 c5 02          	test   $0x2,%bpl
  403ce3:	74 45                	je     403d2a <send_headers+0x1fa>
  403ce5:	89 ed                	mov    %ebp,%ebp
  403ce7:	41 0f b7 54 2c fe    	movzwl -0x2(%r12,%rbp,1),%edx
  403ced:	66 89 54 28 fe       	mov    %dx,-0x2(%rax,%rbp,1)
  403cf2:	eb 36                	jmp    403d2a <send_headers+0x1fa>
  403cf4:	0f 1f 40 00          	nopl   0x0(%rax)
  403cf8:	48 8b 94 24 00 04 00 00 	mov    0x400(%rsp),%rdx
  403d00:	48 8d 78 08          	lea    0x8(%rax),%rdi
  403d04:	4c 89 e6             	mov    %r12,%rsi
  403d07:	48 83 e7 f8          	and    $0xfffffffffffffff8,%rdi
  403d0b:	48 89 10             	mov    %rdx,(%rax)
  403d0e:	89 ea                	mov    %ebp,%edx
  403d10:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
  403d15:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
  403d1a:	48 29 f8             	sub    %rdi,%rax
  403d1d:	8d 4c 05 00          	lea    0x0(%rbp,%rax,1),%ecx
  403d21:	48 29 c6             	sub    %rax,%rsi
  403d24:	c1 e9 03             	shr    $0x3,%ecx
  403d27:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  403d2a:	4d 89 e8             	mov    %r13,%r8
  403d2d:	48 8d 0d 86 23 00 00 	lea    0x2386(%rip),%rcx        # 4060ba <_IO_stdin_used+0xba>
  403d34:	4c 89 e7             	mov    %r12,%rdi
  403d37:	31 c0                	xor    %eax,%eax
  403d39:	ba 00 04 00 00       	mov    $0x400,%edx
  403d3e:	be 01 00 00 00       	mov    $0x1,%esi
  403d43:	e8 48 e5 ff ff       	call   402290 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
  403d48:	4c 89 e7             	mov    %r12,%rdi
  403d4b:	e8 40 e3 ff ff       	call   402090 <strlen@plt>
    iov[3].iov_base = zh_malloc(slen);
  403d50:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
  403d53:	48 89 c5             	mov    %rax,%rbp
    iov[3].iov_base = zh_malloc(slen);
  403d56:	e8 65 fd ff ff       	call   403ac0 <zh_malloc>
    iov[3].iov_len = slen;
  403d5b:	48 89 6b 38          	mov    %rbp,0x38(%rbx)
    iov[3].iov_base = zh_malloc(slen);
  403d5f:	48 89 43 30          	mov    %rax,0x30(%rbx)
  403d63:	83 fd 08             	cmp    $0x8,%ebp
  403d66:	73 30                	jae    403d98 <send_headers+0x268>
  403d68:	40 f6 c5 04          	test   $0x4,%bpl
  403d6c:	0f 85 0e 03 00 00    	jne    404080 <send_headers+0x550>
  403d72:	85 ed                	test   %ebp,%ebp
  403d74:	74 54                	je     403dca <send_headers+0x29a>
  403d76:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
  403d7e:	88 10                	mov    %dl,(%rax)
  403d80:	40 f6 c5 02          	test   $0x2,%bpl
  403d84:	74 44                	je     403dca <send_headers+0x29a>
  403d86:	89 ed                	mov    %ebp,%ebp
  403d88:	41 0f b7 54 2c fe    	movzwl -0x2(%r12,%rbp,1),%edx
  403d8e:	66 89 54 28 fe       	mov    %dx,-0x2(%rax,%rbp,1)
  403d93:	eb 35                	jmp    403dca <send_headers+0x29a>
  403d95:	0f 1f 00             	nopl   (%rax)
  403d98:	48 8b 94 24 00 04 00 00 	mov    0x400(%rsp),%rdx
  403da0:	48 8d 78 08          	lea    0x8(%rax),%rdi
  403da4:	4c 89 e6             	mov    %r12,%rsi
  403da7:	48 83 e7 f8          	and    $0xfffffffffffffff8,%rdi
  403dab:	48 89 10             	mov    %rdx,(%rax)
  403dae:	89 ea                	mov    %ebp,%edx
  403db0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
  403db5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
  403dba:	48 29 f8             	sub    %rdi,%rax
  403dbd:	8d 4c 05 00          	lea    0x0(%rbp,%rax,1),%ecx
  403dc1:	48 29 c6             	sub    %rax,%rsi
  403dc4:	c1 e9 03             	shr    $0x3,%ecx
  403dc7:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  403dca:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    iov[4].iov_base = zh_malloc(slen);
  403dcf:	bf 02 00 00 00       	mov    $0x2,%edi
  403dd4:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
  403ddc:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
  403de4:	e8 d7 fc ff ff       	call   403ac0 <zh_malloc>
  403de9:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_len = slen;
  403df1:	48 c7 43 48 02 00 00 00 	movq   $0x2,0x48(%rbx)
    iov[4].iov_base = zh_malloc(slen);
  403df9:	48 89 43 40          	mov    %rax,0x40(%rbx)
  return __builtin___memcpy_chk (__dest, __src, __len,
  403dfd:	66 89 10             	mov    %dx,(%rax)
}
  403e00:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
  403e08:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  403e11:	0f 85 82 02 00 00    	jne    404099 <send_headers+0x569>
  403e17:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
  403e1e:	5b                   	pop    %rbx
  403e1f:	5d                   	pop    %rbp
  403e20:	41 5c                	pop    %r12
  403e22:	41 5d                	pop    %r13
  403e24:	c3                   	ret
  403e25:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
  403e28:	80 7d 02 00          	cmpb   $0x0,0x2(%rbp)
  403e2c:	0f 85 3f fe ff ff    	jne    403c71 <send_headers+0x141>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  403e32:	66 0f 6f 05 66 2b 00 00 	movdqa 0x2b66(%rip),%xmm0        # 4069a0 <_IO_stdin_used+0x9a0>
  403e3a:	b9 0d 0a 00 00       	mov    $0xa0d,%ecx
  403e3f:	c7 84 24 20 04 00 00 72 69 70 74 	movl   $0x74706972,0x420(%rsp)
  403e4a:	66 89 8c 24 24 04 00 00 	mov    %cx,0x424(%rsp)
  403e52:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403e5a:	66 0f 6f 05 4e 2b 00 00 	movdqa 0x2b4e(%rip),%xmm0        # 4069b0 <_IO_stdin_used+0x9b0>
  403e62:	c6 84 24 26 04 00 00 00 	movb   $0x0,0x426(%rsp)
  403e6a:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
  403e72:	e9 fa fd ff ff       	jmp    403c71 <send_headers+0x141>
  403e77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  403e80:	66 0f 6f 05 08 2b 00 00 	movdqa 0x2b08(%rip),%xmm0        # 406990 <_IO_stdin_used+0x990>
  403e88:	c6 84 24 18 04 00 00 00 	movb   $0x0,0x418(%rsp)
  403e90:	48 b8 78 74 2f 63 73 73 0d 0a 	movabs $0xa0d7373632f7478,%rax
  403e9a:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403ea2:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403eaa:	e9 d9 fd ff ff       	jmp    403c88 <send_headers+0x158>
  403eaf:	90                   	nop
  403eb0:	66 0f 6f 05 d8 2a 00 00 	movdqa 0x2ad8(%rip),%xmm0        # 406990 <_IO_stdin_used+0x990>
  403eb8:	ba 0d 0a 00 00       	mov    $0xa0d,%edx
  403ebd:	48 b8 78 74 2f 70 6c 61 69 6e 	movabs $0x6e69616c702f7478,%rax
  403ec7:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  403ecf:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403ed7:	66 89 94 24 18 04 00 00 	mov    %dx,0x418(%rsp)
  403edf:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403ee7:	e9 b3 fd ff ff       	jmp    403c9f <send_headers+0x16f>
  403eec:	0f 1f 40 00          	nopl   0x0(%rax)
  403ef0:	66 0f 6f 05 88 2a 00 00 	movdqa 0x2a88(%rip),%xmm0        # 406980 <_IO_stdin_used+0x980>
  403ef8:	41 ba 0d 0a 00 00    	mov    $0xa0d,%r10d
  403efe:	48 b8 61 67 65 2f 6a 70 65 67 	movabs $0x6765706a2f656761,%rax
  403f08:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  403f10:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403f18:	66 44 89 94 24 18 04 00 00 	mov    %r10w,0x418(%rsp)
  403f21:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403f29:	e9 d7 fc ff ff       	jmp    403c05 <send_headers+0xd5>
  403f2e:	66 90                	xchg   %ax,%ax
  403f30:	66 0f 6f 05 48 2a 00 00 	movdqa 0x2a48(%rip),%xmm0        # 406980 <_IO_stdin_used+0x980>
  403f38:	41 bb 0d 0a 00 00    	mov    $0xa0d,%r11d
  403f3e:	48 b8 61 67 65 2f 6a 70 65 67 	movabs $0x6765706a2f656761,%rax
  403f48:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  403f50:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403f58:	66 44 89 9c 24 18 04 00 00 	mov    %r11w,0x418(%rsp)
  403f61:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403f69:	e9 80 fc ff ff       	jmp    403bee <send_headers+0xbe>
  403f6e:	66 90                	xchg   %ax,%ax
  403f70:	66 0f 6f 05 18 2a 00 00 	movdqa 0x2a18(%rip),%xmm0        # 406990 <_IO_stdin_used+0x990>
  403f78:	be 0a 00 00 00       	mov    $0xa,%esi
  403f7d:	48 b8 78 74 2f 68 74 6d 6c 0d 	movabs $0xd6c6d74682f7478,%rax
  403f87:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403f8f:	66 89 b4 24 18 04 00 00 	mov    %si,0x418(%rsp)
  403f97:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403f9f:	e9 bd fc ff ff       	jmp    403c61 <send_headers+0x131>
  403fa4:	0f 1f 40 00          	nopl   0x0(%rax)
  403fa8:	66 0f 6f 05 e0 29 00 00 	movdqa 0x29e0(%rip),%xmm0        # 406990 <_IO_stdin_used+0x990>
  403fb0:	bf 0a 00 00 00       	mov    $0xa,%edi
  403fb5:	48 b8 78 74 2f 68 74 6d 6c 0d 	movabs $0xd6c6d74682f7478,%rax
  403fbf:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  403fc7:	66 89 bc 24 18 04 00 00 	mov    %di,0x418(%rsp)
  403fcf:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  403fd7:	e9 6e fc ff ff       	jmp    403c4a <send_headers+0x11a>
  403fdc:	0f 1f 40 00          	nopl   0x0(%rax)
  403fe0:	66 0f 6f 05 98 29 00 00 	movdqa 0x2998(%rip),%xmm0        # 406980 <_IO_stdin_used+0x980>
  403fe8:	41 b8 0a 00 00 00    	mov    $0xa,%r8d
  403fee:	48 b8 61 67 65 2f 67 69 66 0d 	movabs $0xd6669672f656761,%rax
  403ff8:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404000:	66 44 89 84 24 18 04 00 00 	mov    %r8w,0x418(%rsp)
  404009:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404011:	e9 1d fc ff ff       	jmp    403c33 <send_headers+0x103>
  404016:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  404020:	66 0f 6f 05 58 29 00 00 	movdqa 0x2958(%rip),%xmm0        # 406980 <_IO_stdin_used+0x980>
  404028:	41 b9 0a 00 00 00    	mov    $0xa,%r9d
  40402e:	48 b8 61 67 65 2f 70 6e 67 0d 	movabs $0xd676e702f656761,%rax
  404038:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404040:	66 44 89 8c 24 18 04 00 00 	mov    %r9w,0x418(%rsp)
  404049:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404051:	e9 c6 fb ff ff       	jmp    403c1c <send_headers+0xec>
  404056:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
  404060:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
  404067:	89 ed                	mov    %ebp,%ebp
  404069:	89 10                	mov    %edx,(%rax)
  40406b:	41 8b 54 2c fc       	mov    -0x4(%r12,%rbp,1),%edx
  404070:	89 54 28 fc          	mov    %edx,-0x4(%rax,%rbp,1)
  404074:	e9 b1 fc ff ff       	jmp    403d2a <send_headers+0x1fa>
  404079:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  404080:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
  404087:	89 ed                	mov    %ebp,%ebp
  404089:	89 10                	mov    %edx,(%rax)
  40408b:	41 8b 54 2c fc       	mov    -0x4(%r12,%rbp,1),%edx
  404090:	89 54 28 fc          	mov    %edx,-0x4(%rax,%rbp,1)
  404094:	e9 31 fd ff ff       	jmp    403dca <send_headers+0x29a>
}
  404099:	e8 02 e0 ff ff       	call   4020a0 <__stack_chk_fail@plt>
  40409e:	66 90                	xchg   %ax,%ax

00000000004040a0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
  4040a0:	41 55                	push   %r13
  4040a2:	41 54                	push   %r12
  4040a4:	49 89 d4             	mov    %rdx,%r12
  4040a7:	55                   	push   %rbp
  4040a8:	48 89 fd             	mov    %rdi,%rbp
    char *buf = zh_malloc(file_size);
  4040ab:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
  4040ae:	53                   	push   %rbx
  4040af:	48 89 f3             	mov    %rsi,%rbx
  4040b2:	48 83 ec 08          	sub    $0x8,%rsp
    char *buf = zh_malloc(file_size);
  4040b6:	e8 05 fa ff ff       	call   403ac0 <zh_malloc>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
  4040bb:	48 89 ef             	mov    %rbp,%rdi
  4040be:	31 f6                	xor    %esi,%esi
  4040c0:	49 89 c5             	mov    %rax,%r13
  4040c3:	31 c0                	xor    %eax,%eax
  4040c5:	e8 26 e1 ff ff       	call   4021f0 <open@plt>
  4040ca:	89 c5                	mov    %eax,%ebp
    if (fd < 0)
  4040cc:	85 c0                	test   %eax,%eax
  4040ce:	78 58                	js     404128 <copy_file_contents+0x88>
		       "the destination buffer");

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
  4040d0:	48 89 da             	mov    %rbx,%rdx
  4040d3:	4c 89 ee             	mov    %r13,%rsi
  4040d6:	89 ef                	mov    %ebp,%edi
  4040d8:	e8 23 e0 ff ff       	call   402100 <read@plt>
    if (ret < file_size) {
  4040dd:	48 98                	cltq
  4040df:	48 39 d8             	cmp    %rbx,%rax
  4040e2:	7c 1c                	jl     404100 <copy_file_contents+0x60>
    close(fd);
  4040e4:	89 ef                	mov    %ebp,%edi
  4040e6:	e8 f5 df ff ff       	call   4020e0 <close@plt>
    iov->iov_base = buf;
  4040eb:	4d 89 2c 24          	mov    %r13,(%r12)
    iov->iov_len = file_size;
  4040ef:	49 89 5c 24 08       	mov    %rbx,0x8(%r12)
}
  4040f4:	48 83 c4 08          	add    $0x8,%rsp
  4040f8:	5b                   	pop    %rbx
  4040f9:	5d                   	pop    %rbp
  4040fa:	41 5c                	pop    %r12
  4040fc:	41 5d                	pop    %r13
  4040fe:	c3                   	ret
  4040ff:	90                   	nop
        fprintf(stderr, "Encountered a short read.\n");
  404100:	48 8b 05 f1 4e 00 00 	mov    0x4ef1(%rip),%rax        # 408ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  404107:	ba 1a 00 00 00       	mov    $0x1a,%edx
  40410c:	be 01 00 00 00       	mov    $0x1,%esi
  404111:	48 8d 3d b8 1f 00 00 	lea    0x1fb8(%rip),%rdi        # 4060d0 <_IO_stdin_used+0xd0>
  404118:	48 8b 08             	mov    (%rax),%rcx
  40411b:	e8 10 e1 ff ff       	call   402230 <fwrite@plt>
  404120:	eb c2                	jmp    4040e4 <copy_file_contents+0x44>
  404122:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        fatal_error("read");
  404128:	48 8d 3d d0 20 00 00 	lea    0x20d0(%rip),%rdi        # 4061ff <_IO_stdin_used+0x1ff>
  40412f:	e8 2c f9 ff ff       	call   403a60 <fatal_error>
  404134:	eb 9a                	jmp    4040d0 <copy_file_contents+0x30>
  404136:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000404140 <add_write_request>:
 * Returns a vacant sqe, or NULL if we're full.
 */
static inline struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  404140:	48 8b 06             	mov    (%rsi),%rax
int add_write_request(struct Request *req, struct io_uring *ring) {
  404143:	48 89 fa             	mov    %rdi,%rdx
  404146:	48 89 f7             	mov    %rsi,%rdi
  404149:	44 8b 00             	mov    (%rax),%r8d
	unsigned int next = sq->sqe_tail + 1;
  40414c:	8b 46 44             	mov    0x44(%rsi),%eax
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
  40414f:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int next = sq->sqe_tail + 1;
  404155:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;

	if (next - head <= *sq->kring_entries) {
  404158:	41 89 f1             	mov    %esi,%r9d
  40415b:	45 29 c1             	sub    %r8d,%r9d
  40415e:	4c 8b 47 18          	mov    0x18(%rdi),%r8
  404162:	45 3b 08             	cmp    (%r8),%r9d
  404165:	0f 87 45 e1 ff ff    	ja     4022b0 <add_write_request.cold>
  40416b:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40416f:	4c 8b 47 10          	mov    0x10(%rdi),%r8
	if (ring->flags & IORING_SETUP_SQE128)
  404173:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  404176:	66 0f ef c0          	pxor   %xmm0,%xmm0
	if (ring->flags & IORING_SETUP_SQE128)
  40417a:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40417d:	41 23 00             	and    (%r8),%eax
		sq->sqe_tail = next;
  404180:	89 77 44             	mov    %esi,0x44(%rdi)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404183:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
  404185:	8b 72 08             	mov    0x8(%rdx),%esi
  404188:	8b 4a 04             	mov    0x4(%rdx),%ecx
  40418b:	48 c1 e0 06          	shl    $0x6,%rax
  40418f:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
  404193:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
  404199:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
  40419c:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
  4041a0:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
  4041a6:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
  4041ae:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
  4041b2:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
  4041b5:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
  4041bc:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  4041c4:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
  4041c8:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
  4041cc:	e8 df de ff ff       	call   4020b0 <io_uring_submit@plt>
}
  4041d1:	31 c0                	xor    %eax,%eax
  4041d3:	48 83 c4 08          	add    $0x8,%rsp
  4041d7:	c3                   	ret
  4041d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

00000000004041e0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
  4041e0:	41 55                	push   %r13
  4041e2:	41 54                	push   %r12
  4041e4:	55                   	push   %rbp
  4041e5:	48 89 f5             	mov    %rsi,%rbp
  4041e8:	53                   	push   %rbx
  4041e9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  4041ed:	48 8b 06             	mov    (%rsi),%rax
  4041f0:	8b 10                	mov    (%rax),%edx
	unsigned int next = sq->sqe_tail + 1;
  4041f2:	8b 5e 44             	mov    0x44(%rsi),%ebx
	if (ring->flags & IORING_SETUP_SQE128)
  4041f5:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
	unsigned int next = sq->sqe_tail + 1;
  4041fb:	8d 43 01             	lea    0x1(%rbx),%eax
	if (next - head <= *sq->kring_entries) {
  4041fe:	89 c6                	mov    %eax,%esi
  404200:	29 d6                	sub    %edx,%esi
  404202:	48 8b 55 18          	mov    0x18(%rbp),%rdx
  404206:	3b 32                	cmp    (%rdx),%esi
  404208:	0f 87 b2 e0 ff ff    	ja     4022c0 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40420e:	48 8b 55 10          	mov    0x10(%rbp),%rdx
	if (ring->flags & IORING_SETUP_SQE128)
  404212:	c1 e9 0a             	shr    $0xa,%ecx
  404215:	41 89 fd             	mov    %edi,%r13d
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
  404218:	bf 20 00 00 00       	mov    $0x20,%edi
  40421d:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404220:	23 1a                	and    (%rdx),%ebx
		sq->sqe_tail = next;
  404222:	89 45 44             	mov    %eax,0x44(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404225:	d3 e3                	shl    %cl,%ebx
  404227:	48 c1 e3 06          	shl    $0x6,%rbx
  40422b:	48 03 5d 38          	add    0x38(%rbp),%rbx
  40422f:	e8 4c df ff ff       	call   402180 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
  404234:	be 01 00 00 00       	mov    $0x1,%esi
  404239:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
  40423e:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
  404241:	e8 ca de ff ff       	call   402110 <calloc@plt>
    req->client_socket = client_socket;
  404246:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
  40424b:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
  40424f:	48 89 ef             	mov    %rbp,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
  404252:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
  404257:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
  40425c:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
  404265:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
  40426d:	44 89 6b 04          	mov    %r13d,0x4(%rbx)
	sqe->user_data = (unsigned long) data;
  404271:	4c 89 63 20          	mov    %r12,0x20(%rbx)
	sqe->opcode = (__u8) op;
  404275:	c7 03 01 00 00 00    	movl   $0x1,(%rbx)
	sqe->off = offset;
  40427b:	48 c7 43 08 00 00 00 00 	movq   $0x0,0x8(%rbx)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
  404283:	48 89 43 10          	mov    %rax,0x10(%rbx)
	sqe->len = len;
  404287:	48 c7 43 18 01 00 00 00 	movq   $0x1,0x18(%rbx)
	sqe->buf_index = 0;
  40428f:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->addr3 = 0;
  404297:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
    io_uring_submit(ring);
  40429b:	e8 10 de ff ff       	call   4020b0 <io_uring_submit@plt>
}
  4042a0:	48 83 c4 08          	add    $0x8,%rsp
  4042a4:	31 c0                	xor    %eax,%eax
  4042a6:	5b                   	pop    %rbx
  4042a7:	5d                   	pop    %rbp
  4042a8:	41 5c                	pop    %r12
  4042aa:	41 5d                	pop    %r13
  4042ac:	c3                   	ret
  4042ad:	0f 1f 00             	nopl   (%rax)

00000000004042b0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
  4042b0:	41 56                	push   %r14
  4042b2:	49 89 d6             	mov    %rdx,%r14
  4042b5:	41 55                	push   %r13
  4042b7:	49 89 fd             	mov    %rdi,%r13
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  4042ba:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
  4042bf:	41 54                	push   %r12
  4042c1:	55                   	push   %rbp
  4042c2:	53                   	push   %rbx
  4042c3:	89 f3                	mov    %esi,%ebx
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  4042c5:	e8 f6 f7 ff ff       	call   403ac0 <zh_malloc>
    unsigned long slen = strlen(str);
  4042ca:	4c 89 ef             	mov    %r13,%rdi
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  4042cd:	48 89 c5             	mov    %rax,%rbp
    unsigned long slen = strlen(str);
  4042d0:	e8 bb dd ff ff       	call   402090 <strlen@plt>
    req->client_socket = client_socket;
  4042d5:	89 5d 08             	mov    %ebx,0x8(%rbp)
    req->iovec_count = 1;
  4042d8:	c7 45 04 01 00 00 00 	movl   $0x1,0x4(%rbp)
    req->iov[0].iov_base = zh_malloc(slen);
  4042df:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
  4042e2:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = zh_malloc(slen);
  4042e5:	e8 d6 f7 ff ff       	call   403ac0 <zh_malloc>
    req->iov[0].iov_len = slen;
  4042ea:	4c 89 65 18          	mov    %r12,0x18(%rbp)
  4042ee:	4c 89 ee             	mov    %r13,%rsi
  4042f1:	4c 89 e2             	mov    %r12,%rdx
    req->iov[0].iov_base = zh_malloc(slen);
  4042f4:	48 89 45 10          	mov    %rax,0x10(%rbp)
  4042f8:	48 89 c7             	mov    %rax,%rdi
  4042fb:	e8 50 de ff ff       	call   402150 <memcpy@plt>
}
  404300:	5b                   	pop    %rbx
    add_write_request(req, ring);
  404301:	4c 89 f6             	mov    %r14,%rsi
  404304:	48 89 ef             	mov    %rbp,%rdi
}
  404307:	5d                   	pop    %rbp
  404308:	41 5c                	pop    %r12
  40430a:	41 5d                	pop    %r13
  40430c:	41 5e                	pop    %r14
    add_write_request(req, ring);
  40430e:	e9 2d fe ff ff       	jmp    404140 <add_write_request>
  404313:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40431e:	66 90                	xchg   %ax,%ax

0000000000404320 <handle_unimplemented_method>:
    _send_static_string_content(unimplemented_content, client_socket, ring);
  404320:	48 c7 c0 18 90 40 00 	mov    $0x409018,%rax
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
  404327:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
  40432a:	89 fe                	mov    %edi,%esi
  40432c:	48 8b 38             	mov    (%rax),%rdi
  40432f:	e9 7c ff ff ff       	jmp    4042b0 <_send_static_string_content>
  404334:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40433f:	90                   	nop

0000000000404340 <handle_http_404>:
    _send_static_string_content(http_404_content, client_socket, ring);
  404340:	48 c7 c0 10 90 40 00 	mov    $0x409010,%rax
void handle_http_404(int client_socket, struct io_uring *ring) {
  404347:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
  40434a:	89 fe                	mov    %edi,%esi
  40434c:	48 8b 38             	mov    (%rax),%rdi
  40434f:	e9 5c ff ff ff       	jmp    4042b0 <_send_static_string_content>
  404354:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40435f:	90                   	nop

0000000000404360 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
  404360:	41 56                	push   %r14
  404362:	41 55                	push   %r13
  404364:	49 89 d5             	mov    %rdx,%r13
  404367:	41 54                	push   %r12
  404369:	49 89 fc             	mov    %rdi,%r12
  40436c:	55                   	push   %rbp
  40436d:	89 f5                	mov    %esi,%ebp
  40436f:	53                   	push   %rbx
  404370:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
  404377:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  404380:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
  404388:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
  40438a:	e8 01 dd ff ff       	call   402090 <strlen@plt>
  40438f:	41 80 7c 04 ff 2f    	cmpb   $0x2f,-0x1(%r12,%rax,1)
  404395:	48 89 c3             	mov    %rax,%rbx
  404398:	0f 84 b2 00 00 00    	je     404450 <handle_get_method+0xf0>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  40439e:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  4043a3:	4c 89 e6             	mov    %r12,%rsi
  4043a6:	48 8d 53 01          	lea    0x1(%rbx),%rdx
  4043aa:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  4043af:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
  4043b7:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  4043bf:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  4043ca:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  4043d2:	e8 59 dd ff ff       	call   402130 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
  4043d7:	48 89 e6             	mov    %rsp,%rsi
  4043da:	4c 89 f7             	mov    %r14,%rdi
  4043dd:	e8 5e dd ff ff       	call   402140 <stat@plt>
  4043e2:	83 f8 ff             	cmp    $0xffffffff,%eax
  4043e5:	0f 84 cf 00 00 00    	je     4044ba <handle_get_method+0x15a>
        if (S_ISREG(path_stat.st_mode)) {
  4043eb:	8b 44 24 18          	mov    0x18(%rsp),%eax
  4043ef:	25 00 f0 00 00       	and    $0xf000,%eax
  4043f4:	3d 00 80 00 00       	cmp    $0x8000,%eax
  4043f9:	0f 84 e9 00 00 00    	je     4044e8 <handle_get_method+0x188>
            handle_http_404(client_socket, ring);
  4043ff:	4c 89 ee             	mov    %r13,%rsi
  404402:	89 ef                	mov    %ebp,%edi
  404404:	e8 37 ff ff ff       	call   404340 <handle_http_404>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  404409:	4c 89 f2             	mov    %r14,%rdx
  40440c:	bf 01 00 00 00       	mov    $0x1,%edi
  404411:	31 c0                	xor    %eax,%eax
  404413:	48 8d 35 06 1d 00 00 	lea    0x1d06(%rip),%rsi        # 406120 <_IO_stdin_used+0x120>
  40441a:	e8 a1 dd ff ff       	call   4021c0 <__printf_chk@plt>
}
  40441f:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
  404427:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  404430:	0f 85 17 01 00 00    	jne    40454d <handle_get_method+0x1ed>
  404436:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
  40443d:	5b                   	pop    %rbx
  40443e:	5d                   	pop    %rbp
  40443f:	41 5c                	pop    %r12
  404441:	41 5d                	pop    %r13
  404443:	41 5e                	pop    %r14
  404445:	c3                   	ret
  404446:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404450:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  404455:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
  40445d:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  404462:	4c 89 e6             	mov    %r12,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404465:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  40446d:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404470:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  404478:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  404483:	e8 a8 dc ff ff       	call   402130 <__memcpy_chk@plt>
  404488:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  40448d:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
  404492:	48 8d 35 52 1c 00 00 	lea    0x1c52(%rip),%rsi        # 4060eb <_IO_stdin_used+0xeb>
  404499:	48 29 d9             	sub    %rbx,%rcx
  40449c:	ba 0b 00 00 00       	mov    $0xb,%edx
  4044a1:	e8 8a dc ff ff       	call   402130 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
  4044a6:	48 89 e6             	mov    %rsp,%rsi
  4044a9:	4c 89 f7             	mov    %r14,%rdi
  4044ac:	e8 8f dc ff ff       	call   402140 <stat@plt>
  4044b1:	83 f8 ff             	cmp    $0xffffffff,%eax
  4044b4:	0f 85 31 ff ff ff    	jne    4043eb <handle_get_method+0x8b>
  4044ba:	4c 89 e1             	mov    %r12,%rcx
  4044bd:	4c 89 f2             	mov    %r14,%rdx
  4044c0:	48 8d 35 2f 1c 00 00 	lea    0x1c2f(%rip),%rsi        # 4060f6 <_IO_stdin_used+0xf6>
  4044c7:	31 c0                	xor    %eax,%eax
  4044c9:	bf 01 00 00 00       	mov    $0x1,%edi
  4044ce:	e8 ed dc ff ff       	call   4021c0 <__printf_chk@plt>
        handle_http_404(client_socket, ring);
  4044d3:	4c 89 ee             	mov    %r13,%rsi
  4044d6:	89 ef                	mov    %ebp,%edi
  4044d8:	e8 63 fe ff ff       	call   404340 <handle_http_404>
  4044dd:	e9 3d ff ff ff       	jmp    40441f <handle_get_method+0xbf>
  4044e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            struct Request *req = zh_malloc(sizeof(*req) + (sizeof(struct iovec) * 6));
  4044e8:	bf 70 00 00 00       	mov    $0x70,%edi
  4044ed:	e8 ce f5 ff ff       	call   403ac0 <zh_malloc>
            send_headers(final_path, path_stat.st_size, req->iov);
  4044f2:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
  4044f7:	4c 89 f7             	mov    %r14,%rdi
            req->client_socket = client_socket;
  4044fa:	89 68 08             	mov    %ebp,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
  4044fd:	48 8d 50 10          	lea    0x10(%rax),%rdx
            struct Request *req = zh_malloc(sizeof(*req) + (sizeof(struct iovec) * 6));
  404501:	49 89 c4             	mov    %rax,%r12
            req->iovec_count = 6;
  404504:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
  40450b:	e8 20 f6 ff ff       	call   403b30 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
  404510:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
  404515:	49 8d 54 24 60       	lea    0x60(%r12),%rdx
  40451a:	4c 89 f7             	mov    %r14,%rdi
  40451d:	e8 7e fb ff ff       	call   4040a0 <copy_file_contents>
  404522:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
  404527:	4c 89 f2             	mov    %r14,%rdx
  40452a:	31 c0                	xor    %eax,%eax
  40452c:	48 8d 35 db 1b 00 00 	lea    0x1bdb(%rip),%rsi        # 40610e <_IO_stdin_used+0x10e>
  404533:	bf 01 00 00 00       	mov    $0x1,%edi
  404538:	e8 83 dc ff ff       	call   4021c0 <__printf_chk@plt>
            add_write_request(req, ring);
  40453d:	4c 89 ee             	mov    %r13,%rsi
  404540:	4c 89 e7             	mov    %r12,%rdi
  404543:	e8 f8 fb ff ff       	call   404140 <add_write_request>
  404548:	e9 d2 fe ff ff       	jmp    40441f <handle_get_method+0xbf>
}
  40454d:	e8 4e db ff ff       	call   4020a0 <__stack_chk_fail@plt>
  404552:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40455d:	0f 1f 00             	nopl   (%rax)

0000000000404560 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
  404560:	41 57                	push   %r15
  404562:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
  404564:	4c 8d 35 1a 1b 00 00 	lea    0x1b1a(%rip),%r14        # 406085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
  40456b:	41 55                	push   %r13
  40456d:	49 89 d5             	mov    %rdx,%r13
  404570:	41 54                	push   %r12
  404572:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
  404575:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
  404578:	55                   	push   %rbp
  404579:	48 83 ec 10          	sub    $0x10,%rsp
  40457d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  404586:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  40458b:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
  40458d:	49 89 e7             	mov    %rsp,%r15
  404590:	4c 89 fa             	mov    %r15,%rdx
  404593:	e8 58 db ff ff       	call   4020f0 <strtok_r@plt>
    strtolower(method);
  404598:	48 89 c7             	mov    %rax,%rdi
    method = strtok_r(method_buffer, " ", &saveptr);
  40459b:	48 89 c5             	mov    %rax,%rbp
    strtolower(method);
  40459e:	e8 dd f4 ff ff       	call   403a80 <strtolower>
    path = strtok_r(NULL, " ", &saveptr);
  4045a3:	4c 89 f6             	mov    %r14,%rsi
  4045a6:	31 ff                	xor    %edi,%edi
  4045a8:	4c 89 fa             	mov    %r15,%rdx
  4045ab:	e8 40 db ff ff       	call   4020f0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
  4045b0:	48 8d 35 7c 1b 00 00 	lea    0x1b7c(%rip),%rsi        # 406133 <_IO_stdin_used+0x133>
  4045b7:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
  4045ba:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
  4045bd:	e8 5e db ff ff       	call   402120 <strcmp@plt>
  4045c2:	85 c0                	test   %eax,%eax
  4045c4:	75 32                	jne    4045f8 <handle_http_method+0x98>
        handle_get_method(path, client_socket, ring);
  4045c6:	4c 89 ea             	mov    %r13,%rdx
  4045c9:	44 89 e6             	mov    %r12d,%esi
  4045cc:	4c 89 f7             	mov    %r14,%rdi
  4045cf:	e8 8c fd ff ff       	call   404360 <handle_get_method>
}
  4045d4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  4045d9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4045e2:	75 21                	jne    404605 <handle_http_method+0xa5>
  4045e4:	48 83 c4 10          	add    $0x10,%rsp
  4045e8:	5d                   	pop    %rbp
  4045e9:	41 5c                	pop    %r12
  4045eb:	41 5d                	pop    %r13
  4045ed:	41 5e                	pop    %r14
  4045ef:	41 5f                	pop    %r15
  4045f1:	c3                   	ret
  4045f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        handle_unimplemented_method(client_socket, ring);
  4045f8:	4c 89 ee             	mov    %r13,%rsi
  4045fb:	44 89 e7             	mov    %r12d,%edi
  4045fe:	e8 1d fd ff ff       	call   404320 <handle_unimplemented_method>
}
  404603:	eb cf                	jmp    4045d4 <handle_http_method+0x74>
  404605:	e8 96 da ff ff       	call   4020a0 <__stack_chk_fail@plt>
  40460a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000404610 <get_line>:
    for (int i = 0; i < dest_sz; i++) {
  404610:	85 d2                	test   %edx,%edx
  404612:	7e 3c                	jle    404650 <get_line+0x40>
  404614:	8d 42 ff             	lea    -0x1(%rdx),%eax
  404617:	48 83 c7 01          	add    $0x1,%rdi
  40461b:	48 8d 54 06 01       	lea    0x1(%rsi,%rax,1),%rdx
  404620:	eb 13                	jmp    404635 <get_line+0x25>
  404622:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  404628:	48 83 c6 01          	add    $0x1,%rsi
  40462c:	48 83 c7 01          	add    $0x1,%rdi
  404630:	48 39 d6             	cmp    %rdx,%rsi
  404633:	74 1b                	je     404650 <get_line+0x40>
        dest[i] = src[i];
  404635:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
  404639:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
  40463b:	3c 0d                	cmp    $0xd,%al
  40463d:	75 e9                	jne    404628 <get_line+0x18>
  40463f:	80 3f 0a             	cmpb   $0xa,(%rdi)
  404642:	75 e4                	jne    404628 <get_line+0x18>
            dest[i] = '\0';
  404644:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
  404647:	31 c0                	xor    %eax,%eax
}
  404649:	c3                   	ret
  40464a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
  404650:	b8 01 00 00 00       	mov    $0x1,%eax
  404655:	c3                   	ret
  404656:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000404660 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
  404660:	41 54                	push   %r12
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  404662:	ba 00 04 00 00       	mov    $0x400,%edx
int handle_client_request(struct Request *req, struct io_uring *ring) {
  404667:	49 89 f4             	mov    %rsi,%r12
  40466a:	55                   	push   %rbp
  40466b:	53                   	push   %rbx
  40466c:	48 89 fb             	mov    %rdi,%rbx
  40466f:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  404676:	48 8b 7f 10          	mov    0x10(%rdi),%rdi
int handle_client_request(struct Request *req, struct io_uring *ring) {
  40467a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  404683:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
  40468b:	31 c0                	xor    %eax,%eax
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  40468d:	48 89 e5             	mov    %rsp,%rbp
  404690:	48 89 ee             	mov    %rbp,%rsi
  404693:	e8 78 ff ff ff       	call   404610 <get_line>
  404698:	85 c0                	test   %eax,%eax
  40469a:	75 2f                	jne    4046cb <handle_client_request+0x6b>
    handle_http_method(http_request, req->client_socket, ring);
  40469c:	8b 73 08             	mov    0x8(%rbx),%esi
  40469f:	4c 89 e2             	mov    %r12,%rdx
  4046a2:	48 89 ef             	mov    %rbp,%rdi
  4046a5:	e8 b6 fe ff ff       	call   404560 <handle_http_method>
}
  4046aa:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
  4046b2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4046bb:	75 38                	jne    4046f5 <handle_client_request+0x95>
  4046bd:	48 81 c4 10 04 00 00 	add    $0x410,%rsp
  4046c4:	31 c0                	xor    %eax,%eax
  4046c6:	5b                   	pop    %rbx
  4046c7:	5d                   	pop    %rbp
  4046c8:	41 5c                	pop    %r12
  4046ca:	c3                   	ret
        fprintf(stderr, "Malformed request\n");
  4046cb:	48 8b 05 26 49 00 00 	mov    0x4926(%rip),%rax        # 408ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  4046d2:	ba 12 00 00 00       	mov    $0x12,%edx
  4046d7:	be 01 00 00 00       	mov    $0x1,%esi
  4046dc:	48 8d 3d 54 1a 00 00 	lea    0x1a54(%rip),%rdi        # 406137 <_IO_stdin_used+0x137>
  4046e3:	48 8b 08             	mov    (%rax),%rcx
  4046e6:	e8 45 db ff ff       	call   402230 <fwrite@plt>
        exit(1);
  4046eb:	bf 01 00 00 00       	mov    $0x1,%edi
  4046f0:	e8 1b db ff ff       	call   402210 <exit@plt>
}
  4046f5:	e8 a6 d9 ff ff       	call   4020a0 <__stack_chk_fail@plt>
  4046fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000404700 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
  404700:	55                   	push   %rbp
  404701:	66 48 0f 6e c2       	movq   %rdx,%xmm0
  404706:	66 48 0f 6e ce       	movq   %rsi,%xmm1
  40470b:	48 89 cd             	mov    %rcx,%rbp
  40470e:	53                   	push   %rbx
  40470f:	89 f8                	mov    %edi,%eax
  404711:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
  404715:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  404719:	48 8b 11             	mov    (%rcx),%rdx
  40471c:	8b 32                	mov    (%rdx),%esi
	unsigned int next = sq->sqe_tail + 1;
  40471e:	8b 59 44             	mov    0x44(%rcx),%ebx
	if (ring->flags & IORING_SETUP_SQE128)
  404721:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int next = sq->sqe_tail + 1;
  404727:	8d 53 01             	lea    0x1(%rbx),%edx
	if (next - head <= *sq->kring_entries) {
  40472a:	89 d7                	mov    %edx,%edi
  40472c:	29 f7                	sub    %esi,%edi
  40472e:	48 8b 75 18          	mov    0x18(%rbp),%rsi
  404732:	3b 3e                	cmp    (%rsi),%edi
  404734:	0f 87 90 db ff ff    	ja     4022ca <add_accept_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40473a:	48 8b 75 10          	mov    0x10(%rbp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  40473e:	c1 e9 0a             	shr    $0xa,%ecx
  struct Request *req = malloc(sizeof(*req));
  404741:	bf 10 00 00 00       	mov    $0x10,%edi
  404746:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404749:	23 1e                	and    (%rsi),%ebx
		sq->sqe_tail = next;
  40474b:	89 55 44             	mov    %edx,0x44(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40474e:	d3 e3                	shl    %cl,%ebx
  404750:	48 c1 e3 06          	shl    $0x6,%rbx
  404754:	48 03 5d 38          	add    0x38(%rbp),%rbx
	sqe->opcode = (__u8) op;
  404758:	c7 03 0d 00 00 00    	movl   $0xd,(%rbx)
	sqe->fd = fd;
  40475e:	89 43 04             	mov    %eax,0x4(%rbx)
	sqe->buf_index = 0;
  404761:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->len = len;
  404769:	48 c7 43 18 00 00 00 00 	movq   $0x0,0x18(%rbx)
	sqe->off = offset;
  404771:	0f 11 43 08          	movups %xmm0,0x8(%rbx)
	sqe->addr3 = 0;
  404775:	66 0f ef c0          	pxor   %xmm0,%xmm0
  404779:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
  40477d:	e8 fe d9 ff ff       	call   402180 <malloc@plt>
  io_uring_submit(ring);
  404782:	48 89 ef             	mov    %rbp,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
  404785:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
  40478b:	48 89 43 20          	mov    %rax,0x20(%rbx)
}
  40478f:	48 83 c4 08          	add    $0x8,%rsp
  404793:	5b                   	pop    %rbx
  404794:	5d                   	pop    %rbp
  io_uring_submit(ring);
  404795:	e9 16 d9 ff ff       	jmp    4020b0 <io_uring_submit@plt>
  40479a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000004047a0 <io_thread>:
void* io_thread(void *arg) {
  4047a0:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  4047a2:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
  4047a4:	41 56                	push   %r14
  4047a6:	41 55                	push   %r13
  4047a8:	41 54                	push   %r12
  4047aa:	55                   	push   %rbp
  4047ab:	48 89 fd             	mov    %rdi,%rbp
  4047ae:	53                   	push   %rbx
  4047af:	48 81 ec 48 01 00 00 	sub    $0x148,%rsp
  struct io_uring ring = *data->ring;
  4047b6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4047bf:	48 89 84 24 38 01 00 00 	mov    %rax,0x138(%rsp)
  4047c7:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  4047cb:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
  4047d0:	bf 00 01 00 00       	mov    $0x100,%edi
  4047d5:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
  4047d8:	f3 0f 6f 08          	movdqu (%rax),%xmm1
  4047dc:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
  4047e1:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
  4047e6:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
  4047eb:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
  4047f0:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
  4047f8:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
  4047fd:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
  404805:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
  40480a:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
  404812:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
  404817:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
  40481f:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
  404824:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
  40482c:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
  404831:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
  404839:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
  404841:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
  404849:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
  404851:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
  404859:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
  404861:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
  404869:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
  404871:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
  404879:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
  404881:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
  404889:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
  404890:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  404898:	e8 c3 d8 ff ff       	call   402160 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
  40489d:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
  4048a1:	31 f6                	xor    %esi,%esi
  4048a3:	e8 a8 d9 ff ff       	call   402250 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
  4048a8:	31 d2                	xor    %edx,%edx
  4048aa:	be 01 00 00 00       	mov    $0x1,%esi
  4048af:	bf 02 00 00 00       	mov    $0x2,%edi
  4048b4:	e8 e7 d9 ff ff       	call   4022a0 <socket@plt>
  4048b9:	89 44 24 0c          	mov    %eax,0xc(%rsp)
  if (sock == -1)
  4048bd:	83 f8 ff             	cmp    $0xffffffff,%eax
  4048c0:	0f 84 09 05 00 00    	je     404dcf <io_thread+0x62f>
  if (setsockopt(sock,
  4048c6:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  4048ca:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
  4048cf:	41 b8 04 00 00 00    	mov    $0x4,%r8d
  4048d5:	ba 02 00 00 00       	mov    $0x2,%edx
  4048da:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
  4048df:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
  4048e7:	e8 84 d7 ff ff       	call   402070 <setsockopt@plt>
  4048ec:	85 c0                	test   %eax,%eax
  4048ee:	0f 88 ca 04 00 00    	js     404dbe <io_thread+0x61e>
  if (bind(sock,
  4048f4:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  return __builtin___memset_chk (__dest, __ch, __len,
  4048f8:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4048fc:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  404901:	ba 10 00 00 00       	mov    $0x10,%edx
  404906:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  srv_addr.sin_family = AF_INET;
  40490b:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
  404913:	e8 b8 d8 ff ff       	call   4021d0 <bind@plt>
  404918:	85 c0                	test   %eax,%eax
  40491a:	0f 88 8d 04 00 00    	js     404dad <io_thread+0x60d>
  if (listen(sock, 10) < 0) {
  404920:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  404924:	be 0a 00 00 00       	mov    $0xa,%esi
  404929:	e8 62 d8 ff ff       	call   402190 <listen@plt>
  40492e:	85 c0                	test   %eax,%eax
  404930:	0f 88 66 04 00 00    	js     404d9c <io_thread+0x5fc>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  404936:	ba db 18 00 00       	mov    $0x18db,%edx
  40493b:	48 8d 35 3a 18 00 00 	lea    0x183a(%rip),%rsi        # 40617c <_IO_stdin_used+0x17c>
  404942:	bf 01 00 00 00       	mov    $0x1,%edi
  404947:	31 c0                	xor    %eax,%eax
  404949:	e8 72 d8 ff ff       	call   4021c0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  40494e:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
  404953:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  404957:	48 89 d9             	mov    %rbx,%rcx
  40495a:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
  40495f:	48 89 c6             	mov    %rax,%rsi
  404962:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  404967:	48 89 54 24 20       	mov    %rdx,0x20(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
  40496c:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  404974:	e8 87 fd ff ff       	call   404700 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
  404979:	be 10 00 00 00       	mov    $0x10,%esi
  40497e:	bf 01 00 00 00       	mov    $0x1,%edi
  404983:	e8 88 d7 ff ff       	call   402110 <calloc@plt>
  iov->iov_base = zh_malloc(10);
  404988:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
  40498d:	49 89 c6             	mov    %rax,%r14
  404990:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  iov->iov_base = zh_malloc(10);
  404995:	e8 26 f1 ff ff       	call   403ac0 <zh_malloc>
  iov->iov_len = 10;
  40499a:	49 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%r14)
  iov->iov_base = zh_malloc(10);
  4049a2:	49 89 06             	mov    %rax,(%r14)
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  4049a5:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
  4049aa:	8b 30                	mov    (%rax),%esi
	unsigned int next = sq->sqe_tail + 1;
  4049ac:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  4049b3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  4049ba:	8d 50 01             	lea    0x1(%rax),%edx
	if (next - head <= *sq->kring_entries) {
  4049bd:	89 d7                	mov    %edx,%edi
  4049bf:	29 f7                	sub    %esi,%edi
  4049c1:	48 8b 74 24 78       	mov    0x78(%rsp),%rsi
  4049c6:	3b 3e                	cmp    (%rsi),%edi
  4049c8:	0f 87 06 d9 ff ff    	ja     4022d4 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4049ce:	48 8b 74 24 70       	mov    0x70(%rsp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  4049d3:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  4049d6:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
  4049da:	48 89 df             	mov    %rbx,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
  4049dd:	83 e1 01             	and    $0x1,%ecx
  4049e0:	4c 8d 25 ab 17 00 00 	lea    0x17ab(%rip),%r12        # 406192 <_IO_stdin_used+0x192>
  4049e7:	4c 8d 2d ca 17 00 00 	lea    0x17ca(%rip),%r13        # 4061b8 <_IO_stdin_used+0x1b8>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4049ee:	23 06                	and    (%rsi),%eax
		sq->sqe_tail = next;
  4049f0:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
  4049f7:	48 8d 75 50          	lea    0x50(%rbp),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
  4049fb:	8b 55 50             	mov    0x50(%rbp),%edx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4049fe:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
  404a00:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
  404a05:	48 c1 e0 06          	shl    $0x6,%rax
  404a09:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
  404a11:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
  404a17:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
  404a1a:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
  404a22:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
  404a26:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
  404a2e:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  404a36:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
  404a3a:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
  404a3e:	e8 6d d6 ff ff       	call   4020b0 <io_uring_submit@plt>
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
  404a43:	48 8d 44 24 38       	lea    0x38(%rsp),%rax
  while (data->running == 1) {
  404a48:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
  404a4c:	48 89 04 24          	mov    %rax,(%rsp)
  404a50:	0f 85 a6 01 00 00    	jne    404bfc <io_thread+0x45c>
  404a56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  404a60:	4c 89 e7             	mov    %r12,%rdi
  404a63:	e8 f8 d5 ff ff       	call   402060 <puts@plt>
	unsigned mask = *ring->cq.kring_mask;
  404a68:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
	if (ring->flags & IORING_SETUP_CQE32)
  404a70:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = *ring->cq.kring_mask;
  404a77:	8b 30                	mov    (%rax),%esi
	if (ring->flags & IORING_SETUP_CQE32)
  404a79:	c1 e9 0b             	shr    $0xb,%ecx
  404a7c:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
  404a7f:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
  404a87:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
  404a89:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
  404a91:	8b 17                	mov    (%rdi),%edx
		if (!available)
  404a93:	39 d0                	cmp    %edx,%eax
  404a95:	74 39                	je     404ad0 <io_thread+0x330>
		cqe = &ring->cq.cqes[(head & mask) << shift];
  404a97:	89 f0                	mov    %esi,%eax
  404a99:	21 d0                	and    %edx,%eax
  404a9b:	d3 e0                	shl    %cl,%eax
  404a9d:	48 c1 e0 04          	shl    $0x4,%rax
  404aa1:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
  404aa9:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
  404ab1:	0f 85 81 01 00 00    	jne    404c38 <io_thread+0x498>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
  404ab7:	4c 8b 00             	mov    (%rax),%r8
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
  404aba:	49 83 f8 ff          	cmp    $0xffffffffffffffff,%r8
  404abe:	0f 85 9c 02 00 00    	jne    404d60 <io_thread+0x5c0>
			if (cqe->res < 0)
  404ac4:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  404ac7:	83 c2 01             	add    $0x1,%edx
  404aca:	89 17                	mov    %edx,(%rdi)
			if (!err)
  404acc:	85 c0                	test   %eax,%eax
  404ace:	79 af                	jns    404a7f <io_thread+0x2df>
	*cqe_ptr = cqe;
  404ad0:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
  404ad9:	48 8b 34 24          	mov    (%rsp),%rsi
  404add:	45 31 c0             	xor    %r8d,%r8d
  404ae0:	31 d2                	xor    %edx,%edx
  404ae2:	b9 01 00 00 00       	mov    $0x1,%ecx
  404ae7:	48 89 df             	mov    %rbx,%rdi
  404aea:	e8 c1 d6 ff ff       	call   4021b0 <__io_uring_get_cqe@plt>
  404aef:	41 89 c6             	mov    %eax,%r14d
      if (cqe->user_data == 1) {
  404af2:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  404af7:	48 83 38 01          	cmpq   $0x1,(%rax)
  404afb:	0f 84 8f 02 00 00    	je     404d90 <io_thread+0x5f0>
  404b01:	4c 89 ef             	mov    %r13,%rdi
  404b04:	e8 57 d5 ff ff       	call   402060 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
  404b09:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
  404b0e:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
  404b11:	45 85 f6             	test   %r14d,%r14d
  404b14:	79 11                	jns    404b27 <io_thread+0x387>
          fatal_error("io_uring_wait_cqe");
  404b16:	48 8d 3d b2 16 00 00 	lea    0x16b2(%rip),%rdi        # 4061cf <_IO_stdin_used+0x1cf>
  404b1d:	e8 3e ef ff ff       	call   403a60 <fatal_error>
      if (cqe->res < 0) {
  404b22:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
  404b27:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
  404b2a:	45 8b 07             	mov    (%r15),%r8d
      if (cqe->res < 0) {
  404b2d:	85 c0                	test   %eax,%eax
  404b2f:	0f 88 ab 02 00 00    	js     404de0 <io_thread+0x640>
      switch (req->event_type) {
  404b35:	41 83 f8 01          	cmp    $0x1,%r8d
  404b39:	0f 84 31 01 00 00    	je     404c70 <io_thread+0x4d0>
  404b3f:	41 83 f8 02          	cmp    $0x2,%r8d
  404b43:	0f 84 9f 01 00 00    	je     404ce8 <io_thread+0x548>
  404b49:	45 85 c0             	test   %r8d,%r8d
  404b4c:	0f 84 5e 01 00 00    	je     404cb0 <io_thread+0x510>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  404b52:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  404b5a:	8b 02                	mov    (%rdx),%eax
  404b5c:	83 c0 01             	add    $0x1,%eax
  404b5f:	89 02                	mov    %eax,(%rdx)
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  404b61:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
  404b66:	8b 30                	mov    (%rax),%esi
	unsigned int next = sq->sqe_tail + 1;
  404b68:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  404b6f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  404b76:	8d 50 01             	lea    0x1(%rax),%edx
	if (next - head <= *sq->kring_entries) {
  404b79:	89 d7                	mov    %edx,%edi
  404b7b:	29 f7                	sub    %esi,%edi
  404b7d:	48 8b 74 24 78       	mov    0x78(%rsp),%rsi
  404b82:	3b 3e                	cmp    (%rsi),%edi
  404b84:	0f 87 4a d7 ff ff    	ja     4022d4 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404b8a:	48 8b 74 24 70       	mov    0x70(%rsp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  404b8f:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  404b92:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
  404b96:	48 89 df             	mov    %rbx,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
  404b99:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404b9c:	23 06                	and    (%rsi),%eax
	sqe->addr = (unsigned long) addr;
  404b9e:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
		sq->sqe_tail = next;
  404ba3:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404baa:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
  404bac:	8b 55 50             	mov    0x50(%rbp),%edx
  404baf:	48 c1 e0 06          	shl    $0x6,%rax
  404bb3:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->addr = (unsigned long) addr;
  404bbb:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->user_data = (unsigned long) data;
  404bbf:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
	sqe->opcode = (__u8) op;
  404bc4:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
  404bca:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
  404bcd:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->len = len;
  404bd5:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
  404bdd:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  404be5:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
  404be9:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
  404bed:	e8 be d4 ff ff       	call   4020b0 <io_uring_submit@plt>
  while (data->running == 1) {
  404bf2:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
  404bf6:	0f 84 64 fe ff ff    	je     404a60 <io_thread+0x2c0>
  404bfc:	48 8d 3d ee 15 00 00 	lea    0x15ee(%rip),%rdi        # 4061f1 <_IO_stdin_used+0x1f1>
  404c03:	e8 58 d4 ff ff       	call   402060 <puts@plt>
}
  404c08:	48 8b 84 24 38 01 00 00 	mov    0x138(%rsp),%rax
  404c10:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  404c19:	0f 85 fc 01 00 00    	jne    404e1b <io_thread+0x67b>
  404c1f:	48 81 c4 48 01 00 00 	add    $0x148,%rsp
  404c26:	31 c0                	xor    %eax,%eax
  404c28:	5b                   	pop    %rbx
  404c29:	5d                   	pop    %rbp
  404c2a:	41 5c                	pop    %r12
  404c2c:	41 5d                	pop    %r13
  404c2e:	41 5e                	pop    %r14
  404c30:	41 5f                	pop    %r15
  404c32:	c3                   	ret
  404c33:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
  404c38:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
  404c3d:	48 85 c0             	test   %rax,%rax
  404c40:	0f 84 93 fe ff ff    	je     404ad9 <io_thread+0x339>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
  404c46:	4c 8b 00             	mov    (%rax),%r8
      if (cqe->user_data == 1) {
  404c49:	49 83 f8 01          	cmp    $0x1,%r8
  404c4d:	0f 84 1d 01 00 00    	je     404d70 <io_thread+0x5d0>
  404c53:	4c 89 ef             	mov    %r13,%rdi
  404c56:	e8 05 d4 ff ff       	call   402060 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
  404c5b:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
  404c60:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
  404c63:	e9 bf fe ff ff       	jmp    404b27 <io_thread+0x387>
  404c68:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
              if (!cqe->res) {
  404c70:	85 c0                	test   %eax,%eax
  404c72:	0f 85 b8 00 00 00    	jne    404d30 <io_thread+0x590>
                  fprintf(stderr, "Empty request!\n");
  404c78:	48 8b 05 79 43 00 00 	mov    0x4379(%rip),%rax        # 408ff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  404c7f:	ba 0f 00 00 00       	mov    $0xf,%edx
  404c84:	be 01 00 00 00       	mov    $0x1,%esi
  404c89:	48 8d 3d 51 15 00 00 	lea    0x1551(%rip),%rdi        # 4061e1 <_IO_stdin_used+0x1e1>
  404c90:	48 8b 08             	mov    (%rax),%rcx
  404c93:	e8 98 d5 ff ff       	call   402230 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
  404c98:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  404c9d:	0f 1f 00             	nopl   (%rax)
	if (cqe)
  404ca0:	48 85 c0             	test   %rax,%rax
  404ca3:	0f 84 b8 fe ff ff    	je     404b61 <io_thread+0x3c1>
  404ca9:	e9 a4 fe ff ff       	jmp    404b52 <io_thread+0x3b2>
  404cae:	66 90                	xchg   %ax,%ax
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  404cb0:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  404cb5:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  404cba:	48 89 d9             	mov    %rbx,%rcx
  404cbd:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
  404cc1:	e8 3a fa ff ff       	call   404700 <add_accept_request>
              add_read_request(cqe->res, &ring);
  404cc6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
  404ccb:	48 89 de             	mov    %rbx,%rsi
  404cce:	8b 78 08             	mov    0x8(%rax),%edi
  404cd1:	e8 0a f5 ff ff       	call   4041e0 <add_read_request>
              free(req);
  404cd6:	4c 89 ff             	mov    %r15,%rdi
  404cd9:	e8 52 d3 ff ff       	call   402030 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
  404cde:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
  404ce3:	eb bb                	jmp    404ca0 <io_thread+0x500>
  404ce5:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
  404ce8:	41 8b 47 04          	mov    0x4(%r15),%eax
  404cec:	45 31 f6             	xor    %r14d,%r14d
  404cef:	85 c0                	test   %eax,%eax
  404cf1:	7e 20                	jle    404d13 <io_thread+0x573>
  404cf3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  free(req->iov[i].iov_base);
  404cf8:	49 63 c6             	movslq %r14d,%rax
              for (int i = 0; i < req->iovec_count; i++) {
  404cfb:	41 83 c6 01          	add    $0x1,%r14d
                  free(req->iov[i].iov_base);
  404cff:	48 c1 e0 04          	shl    $0x4,%rax
  404d03:	4a 8b 7c 38 10       	mov    0x10(%rax,%r15,1),%rdi
  404d08:	e8 23 d3 ff ff       	call   402030 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
  404d0d:	45 39 77 04          	cmp    %r14d,0x4(%r15)
  404d11:	7f e5                	jg     404cf8 <io_thread+0x558>
              close(req->client_socket);
  404d13:	41 8b 7f 08          	mov    0x8(%r15),%edi
  404d17:	e8 c4 d3 ff ff       	call   4020e0 <close@plt>
              free(req);
  404d1c:	4c 89 ff             	mov    %r15,%rdi
  404d1f:	e8 0c d3 ff ff       	call   402030 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
  404d24:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
  404d29:	e9 72 ff ff ff       	jmp    404ca0 <io_thread+0x500>
  404d2e:	66 90                	xchg   %ax,%ax
              handle_client_request(req, &ring);
  404d30:	48 89 de             	mov    %rbx,%rsi
  404d33:	4c 89 ff             	mov    %r15,%rdi
  404d36:	e8 25 f9 ff ff       	call   404660 <handle_client_request>
              free(req->iov[0].iov_base);
  404d3b:	49 8b 7f 10          	mov    0x10(%r15),%rdi
  404d3f:	e8 ec d2 ff ff       	call   402030 <free@plt>
              free(req);
  404d44:	4c 89 ff             	mov    %r15,%rdi
  404d47:	e8 e4 d2 ff ff       	call   402030 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
  404d4c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
  404d51:	e9 4a ff ff ff       	jmp    404ca0 <io_thread+0x500>
  404d56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
  404d60:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
      if (cqe->user_data == 1) {
  404d65:	49 83 f8 01          	cmp    $0x1,%r8
  404d69:	0f 85 e4 fe ff ff    	jne    404c53 <io_thread+0x4b3>
  404d6f:	90                   	nop
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  404d70:	83 c2 01             	add    $0x1,%edx
  404d73:	89 17                	mov    %edx,(%rdi)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  404d75:	48 8d 3d 28 14 00 00 	lea    0x1428(%rip),%rdi        # 4061a4 <_IO_stdin_used+0x1a4>
  404d7c:	e8 df d2 ff ff       	call   402060 <puts@plt>
  404d81:	e9 76 fe ff ff       	jmp    404bfc <io_thread+0x45c>
  404d86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  404d90:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
  404d98:	8b 17                	mov    (%rdi),%edx
  404d9a:	eb d4                	jmp    404d70 <io_thread+0x5d0>
    fatal_error("listen()");
  404d9c:	48 8d 3d d0 13 00 00 	lea    0x13d0(%rip),%rdi        # 406173 <_IO_stdin_used+0x173>
  404da3:	e8 b8 ec ff ff       	call   403a60 <fatal_error>
  404da8:	e9 89 fb ff ff       	jmp    404936 <io_thread+0x196>
      fatal_error("bind()");
  404dad:	48 8d 3d b8 13 00 00 	lea    0x13b8(%rip),%rdi        # 40616c <_IO_stdin_used+0x16c>
  404db4:	e8 a7 ec ff ff       	call   403a60 <fatal_error>
  404db9:	e9 62 fb ff ff       	jmp    404920 <io_thread+0x180>
      fatal_error("setsockopt(SO_REUSEADDR)");
  404dbe:	48 8d 3d 8e 13 00 00 	lea    0x138e(%rip),%rdi        # 406153 <_IO_stdin_used+0x153>
  404dc5:	e8 96 ec ff ff       	call   403a60 <fatal_error>
  404dca:	e9 25 fb ff ff       	jmp    4048f4 <io_thread+0x154>
      fatal_error("socket()");
  404dcf:	48 8d 3d 74 13 00 00 	lea    0x1374(%rip),%rdi        # 40614a <_IO_stdin_used+0x14a>
  404dd6:	e8 85 ec ff ff       	call   403a60 <fatal_error>
  404ddb:	e9 e6 fa ff ff       	jmp    4048c6 <io_thread+0x126>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
  404de0:	f7 d8                	neg    %eax
  404de2:	44 89 04 24          	mov    %r8d,(%rsp)
  404de6:	89 c7                	mov    %eax,%edi
  404de8:	e8 83 d4 ff ff       	call   402270 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  404ded:	44 8b 04 24          	mov    (%rsp),%r8d
  404df1:	be 01 00 00 00       	mov    $0x1,%esi
  404df6:	48 8d 15 3b 16 00 00 	lea    0x163b(%rip),%rdx        # 406438 <_IO_stdin_used+0x438>
  404dfd:	48 89 c1             	mov    %rax,%rcx
  404e00:	48 8b 05 f1 41 00 00 	mov    0x41f1(%rip),%rax        # 408ff8 <stderr@GLIBC_2.2.5>
  404e07:	48 8b 38             	mov    (%rax),%rdi
  404e0a:	31 c0                	xor    %eax,%eax
  404e0c:	e8 2f d4 ff ff       	call   402240 <__fprintf_chk@plt>
          exit(1);
  404e11:	bf 01 00 00 00       	mov    $0x1,%edi
  404e16:	e8 f5 d3 ff ff       	call   402210 <exit@plt>
}
  404e1b:	e8 80 d2 ff ff       	call   4020a0 <__stack_chk_fail@plt>

0000000000404e20 <sendm>:
int sendm(struct BarrierTask *data) {
  404e20:	41 57                	push   %r15
  404e22:	41 56                	push   %r14
  404e24:	41 55                	push   %r13
  404e26:	41 54                	push   %r12
  404e28:	55                   	push   %rbp
  404e29:	53                   	push   %rbx
  404e2a:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
  404e2e:	83 bf f8 00 00 00 01 	cmpl   $0x1,0xf8(%rdi)
  404e35:	0f 85 45 01 00 00    	jne    404f80 <sendm+0x160>
      for (int n = 0 ; n < data->thread_count; n++) {
  404e3b:	8b 87 b4 00 00 00    	mov    0xb4(%rdi),%eax
  404e41:	48 8d 9f 08 01 00 00 	lea    0x108(%rdi),%rbx
  404e48:	48 89 fa             	mov    %rdi,%rdx
  404e4b:	31 f6                	xor    %esi,%esi
  404e4d:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  404e52:	4c 8d bf 00 01 00 00 	lea    0x100(%rdi),%r15
  404e59:	85 c0                	test   %eax,%eax
  404e5b:	0f 8e f3 00 00 00    	jle    404f54 <sendm+0x134>
  404e61:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
  404e68:	39 b2 b0 00 00 00    	cmp    %esi,0xb0(%rdx)
  404e6e:	0f 84 d5 00 00 00    	je     404f49 <sendm+0x129>
        struct Data *them = data->mailboxes[n].higher;
  404e74:	4c 63 c6             	movslq %esi,%r8
  404e77:	49 c1 e0 05          	shl    $0x5,%r8
  404e7b:	4c 03 82 e8 00 00 00 	add    0xe8(%rdx),%r8
  404e82:	4d 8b 58 08          	mov    0x8(%r8),%r11
        for (; them->messages_count < min;) {
  404e86:	49 8b 4b 08          	mov    0x8(%r11),%rcx
  404e8a:	4d 63 53 10          	movslq 0x10(%r11),%r10
  404e8e:	49 39 ca             	cmp    %rcx,%r10
  404e91:	0f 8e a9 00 00 00    	jle    404f40 <sendm+0x120>
          them->messages[them->messages_count++] = data->message; 
  404e97:	49 8b 3b             	mov    (%r11),%rdi
  404e9a:	4d 89 d1             	mov    %r10,%r9
  404e9d:	48 8b aa 88 00 00 00 	mov    0x88(%rdx),%rbp
  404ea4:	49 29 c9             	sub    %rcx,%r9
  404ea7:	49 8b 58 10          	mov    0x10(%r8),%rbx
  404eab:	4e 8d 24 d7          	lea    (%rdi,%r10,8),%r12
  404eaf:	48 8d 04 cf          	lea    (%rdi,%rcx,8),%rax
  404eb3:	4d 39 fc             	cmp    %r15,%r12
  404eb6:	41 0f 96 c6          	setbe  %r14b
  404eba:	48 3b 44 24 08       	cmp    0x8(%rsp),%rax
  404ebf:	41 0f 93 c5          	setae  %r13b
  404ec3:	45 08 f5             	or     %r14b,%r13b
  404ec6:	0f 84 9c 00 00 00    	je     404f68 <sendm+0x148>
  404ecc:	4d 8d 69 ff          	lea    -0x1(%r9),%r13
  404ed0:	49 83 fd 02          	cmp    $0x2,%r13
  404ed4:	0f 86 8e 00 00 00    	jbe    404f68 <sendm+0x148>
  404eda:	4c 8b aa 00 01 00 00 	mov    0x100(%rdx),%r13
  404ee1:	4d 89 cc             	mov    %r9,%r12
  404ee4:	49 d1 ec             	shr    %r12
  404ee7:	66 49 0f 6e c5       	movq   %r13,%xmm0
  404eec:	49 c1 e4 04          	shl    $0x4,%r12
  404ef0:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
  404ef4:	49 01 c4             	add    %rax,%r12
  404ef7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  404f00:	0f 11 00             	movups %xmm0,(%rax)
        for (; them->messages_count < min;) {
  404f03:	48 83 c0 10          	add    $0x10,%rax
  404f07:	49 39 c4             	cmp    %rax,%r12
  404f0a:	75 f4                	jne    404f00 <sendm+0xe0>
  404f0c:	4c 89 c8             	mov    %r9,%rax
  404f0f:	48 83 e0 fe          	and    $0xfffffffffffffffe,%rax
  404f13:	48 01 c1             	add    %rax,%rcx
  404f16:	49 39 c1             	cmp    %rax,%r9
  404f19:	74 0b                	je     404f26 <sendm+0x106>
          them->messages[them->messages_count++] = data->message; 
  404f1b:	4c 8b aa 00 01 00 00 	mov    0x100(%rdx),%r13
  404f22:	4c 89 2c cf          	mov    %r13,(%rdi,%rcx,8)
          data->n++;
  404f26:	4c 01 cd             	add    %r9,%rbp
          data->mailboxes[n].sent++;
  404f29:	4c 01 cb             	add    %r9,%rbx
          data->n++;
  404f2c:	48 89 aa 88 00 00 00 	mov    %rbp,0x88(%rdx)
          data->mailboxes[n].sent++;
  404f33:	49 89 58 10          	mov    %rbx,0x10(%r8)
  404f37:	4d 89 53 08          	mov    %r10,0x8(%r11)
  404f3b:	4e 89 6c d7 f8       	mov    %r13,-0x8(%rdi,%r10,8)
        asm volatile ("sfence" ::: "memory");
  404f40:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
  404f43:	8b 82 b4 00 00 00    	mov    0xb4(%rdx),%eax
  404f49:	83 c6 01             	add    $0x1,%esi
  404f4c:	39 c6                	cmp    %eax,%esi
  404f4e:	0f 8c 14 ff ff ff    	jl     404e68 <sendm+0x48>
}
  404f54:	48 83 c4 18          	add    $0x18,%rsp
  404f58:	31 c0                	xor    %eax,%eax
  404f5a:	5b                   	pop    %rbx
  404f5b:	5d                   	pop    %rbp
  404f5c:	41 5c                	pop    %r12
  404f5e:	41 5d                	pop    %r13
  404f60:	41 5e                	pop    %r14
  404f62:	41 5f                	pop    %r15
  404f64:	c3                   	ret
  404f65:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
  404f68:	4c 8b aa 00 01 00 00 	mov    0x100(%rdx),%r13
        for (; them->messages_count < min;) {
  404f6f:	48 83 c0 08          	add    $0x8,%rax
          them->messages[them->messages_count++] = data->message; 
  404f73:	4c 89 68 f8          	mov    %r13,-0x8(%rax)
        for (; them->messages_count < min;) {
  404f77:	4c 39 e0             	cmp    %r12,%rax
  404f7a:	75 ec                	jne    404f68 <sendm+0x148>
  404f7c:	eb a8                	jmp    404f26 <sendm+0x106>
  404f7e:	66 90                	xchg   %ax,%ax
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  404f80:	48 8d 3d 7d 12 00 00 	lea    0x127d(%rip),%rdi        # 406204 <_IO_stdin_used+0x204>
  404f87:	e8 d4 d0 ff ff       	call   402060 <puts@plt>
  404f8c:	eb c6                	jmp    404f54 <sendm+0x134>
  404f8e:	66 90                	xchg   %ax,%ax

0000000000404f90 <receive>:
  for (int n = 0 ; n < data->thread_count; n++) {
  404f90:	8b 87 b4 00 00 00    	mov    0xb4(%rdi),%eax
  404f96:	85 c0                	test   %eax,%eax
  404f98:	0f 8e fb 00 00 00    	jle    405099 <receive+0x109>
int receive(struct BarrierTask *data) {
  404f9e:	41 55                	push   %r13
  404fa0:	48 89 fe             	mov    %rdi,%rsi
  404fa3:	41 54                	push   %r12
  404fa5:	45 31 e4             	xor    %r12d,%r12d
  404fa8:	55                   	push   %rbp
  404fa9:	53                   	push   %rbx
  404faa:	48 83 ec 08          	sub    $0x8,%rsp
  404fae:	66 90                	xchg   %ax,%ax
    struct Data *me = data->mailboxes[n].lower;
  404fb0:	4d 63 c4             	movslq %r12d,%r8
  404fb3:	49 c1 e0 05          	shl    $0x5,%r8
  404fb7:	4c 03 86 e8 00 00 00 	add    0xe8(%rsi),%r8
  404fbe:	4d 8b 28             	mov    (%r8),%r13
    for (int x = 0 ; x < me->messages_count ; x++) {
  404fc1:	4d 8b 5d 08          	mov    0x8(%r13),%r11
  404fc5:	4d 85 db             	test   %r11,%r11
  404fc8:	0f 8e a2 00 00 00    	jle    405070 <receive+0xe0>
      data->sends++;
  404fce:	48 8b be f0 00 00 00 	mov    0xf0(%rsi),%rdi
      data->mailboxes[n].received++;
  404fd5:	4d 8b 48 18          	mov    0x18(%r8),%r9
    for (int x = 0 ; x < me->messages_count ; x++) {
  404fd9:	31 c9                	xor    %ecx,%ecx
  404fdb:	31 d2                	xor    %edx,%edx
      data->n++;
  404fdd:	4c 8b 96 88 00 00 00 	mov    0x88(%rsi),%r10
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
  404fe4:	49 8b 6d 00          	mov    0x0(%r13),%rbp
  404fe8:	48 63 1e             	movslq (%rsi),%rbx
  404feb:	48 8d 47 01          	lea    0x1(%rdi),%rax
      data->mailboxes[n].received++;
  404fef:	49 29 f9             	sub    %rdi,%r9
      data->n++;
  404ff2:	49 29 fa             	sub    %rdi,%r10
  404ff5:	eb 18                	jmp    40500f <receive+0x7f>
  404ff7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
  405000:	83 c1 01             	add    $0x1,%ecx
  405003:	48 83 c0 01          	add    $0x1,%rax
  405007:	48 63 d1             	movslq %ecx,%rdx
  40500a:	4c 39 da             	cmp    %r11,%rdx
  40500d:	7d 61                	jge    405070 <receive+0xe0>
      data->n++;
  40500f:	49 8d 3c 02          	lea    (%r10,%rax,1),%rdi
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
  405013:	48 8b 54 d5 00       	mov    0x0(%rbp,%rdx,8),%rdx
      data->sends++;
  405018:	48 89 86 f0 00 00 00 	mov    %rax,0xf0(%rsi)
      data->n++;
  40501f:	48 89 be 88 00 00 00 	mov    %rdi,0x88(%rsi)
      data->mailboxes[n].received++;
  405026:	49 8d 3c 01          	lea    (%r9,%rax,1),%rdi
  40502a:	49 89 78 18          	mov    %rdi,0x18(%r8)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
  40502e:	48 39 5a 10          	cmp    %rbx,0x10(%rdx)
  405032:	75 cc                	jne    405000 <receive+0x70>
  405034:	48 63 be b0 00 00 00 	movslq 0xb0(%rsi),%rdi
  40503b:	48 39 7a 08          	cmp    %rdi,0x8(%rdx)
  40503f:	75 bf                	jne    405000 <receive+0x70>
  405041:	bf 01 00 00 00       	mov    $0x1,%edi
  405046:	b9 01 00 00 00       	mov    $0x1,%ecx
  40504b:	ba 01 00 00 00       	mov    $0x1,%edx
  405050:	31 c0                	xor    %eax,%eax
  405052:	48 8d 35 07 14 00 00 	lea    0x1407(%rip),%rsi        # 406460 <_IO_stdin_used+0x460>
  405059:	e8 62 d1 ff ff       	call   4021c0 <__printf_chk@plt>
        exit(1);
  40505e:	bf 01 00 00 00       	mov    $0x1,%edi
  405063:	e8 a8 d1 ff ff       	call   402210 <exit@plt>
  405068:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    me->messages_count = 0;
  405070:	49 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%r13)
    asm volatile ("sfence" ::: "memory");
  405078:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
  40507b:	41 83 c4 01          	add    $0x1,%r12d
  40507f:	44 39 a6 b4 00 00 00 	cmp    %r12d,0xb4(%rsi)
  405086:	0f 8f 24 ff ff ff    	jg     404fb0 <receive+0x20>
}
  40508c:	48 83 c4 08          	add    $0x8,%rsp
  405090:	31 c0                	xor    %eax,%eax
  405092:	5b                   	pop    %rbx
  405093:	5d                   	pop    %rbp
  405094:	41 5c                	pop    %r12
  405096:	41 5d                	pop    %r13
  405098:	c3                   	ret
  405099:	31 c0                	xor    %eax,%eax
  40509b:	c3                   	ret
  40509c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004050a0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
  4050a0:	41 54                	push   %r12
  4050a2:	55                   	push   %rbp
  4050a3:	48 89 fd             	mov    %rdi,%rbp
  4050a6:	53                   	push   %rbx
  if (data->thread_index == data->task_index) {
  4050a7:	8b 07                	mov    (%rdi),%eax
  4050a9:	39 87 b0 00 00 00    	cmp    %eax,0xb0(%rdi)
  4050af:	74 3f                	je     4050f0 <barriered_work+0x50>
    receive(data);
  4050b1:	e8 da fe ff ff       	call   404f90 <receive>
    while (data->scheduled == 1) {
  4050b6:	83 bd c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbp)
  4050bd:	75 15                	jne    4050d4 <barriered_work+0x34>
  4050bf:	90                   	nop
      data->n++;
  4050c0:	48 83 85 88 00 00 00 01 	addq   $0x1,0x88(%rbp)
      asm volatile ("sfence" ::: "memory");
  4050c8:	0f ae f8             	sfence
    while (data->scheduled == 1) {
  4050cb:	83 bd c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbp)
  4050d2:	74 ec                	je     4050c0 <barriered_work+0x20>
    sendm(data);
  4050d4:	48 89 ef             	mov    %rbp,%rdi
  4050d7:	e8 44 fd ff ff       	call   404e20 <sendm>
  asm volatile ("sfence" ::: "memory");
  4050dc:	0f ae f8             	sfence
}
  4050df:	31 c0                	xor    %eax,%eax
  4050e1:	5b                   	pop    %rbx
  4050e2:	5d                   	pop    %rbp
  4050e3:	41 5c                	pop    %r12
  4050e5:	c3                   	ret
  4050e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      receive(data);
  4050f0:	e8 9b fe ff ff       	call   404f90 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
  4050f5:	44 8b 8d b4 00 00 00 	mov    0xb4(%rbp),%r9d
        int t = data->task_index;
  4050fc:	8b 45 00             	mov    0x0(%rbp),%eax
        for (int y = 0; y < data->thread_count ; y++) {
  4050ff:	45 85 c9             	test   %r9d,%r9d
  405102:	0f 8e 8c 00 00 00    	jle    405194 <barriered_work+0xf4>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
  405108:	48 8b 95 a8 00 00 00 	mov    0xa8(%rbp),%rdx
  40510f:	4c 8b 52 10          	mov    0x10(%rdx),%r10
  405113:	48 63 d0             	movslq %eax,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
  405116:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
  405119:	4c 8d 1c 52          	lea    (%rdx,%rdx,2),%r11
              int next_task = abs((t + 1) % (data->thread_count));
  40511d:	99                   	cltd
  40511e:	41 f7 f9             	idiv   %r9d
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
  405121:	49 c1 e3 07          	shl    $0x7,%r11
  405125:	4c 89 d7             	mov    %r10,%rdi
              int next_task = abs((t + 1) % (data->thread_count));
  405128:	89 d0                	mov    %edx,%eax
  40512a:	f7 d8                	neg    %eax
  40512c:	0f 48 c2             	cmovs  %edx,%eax
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
  40512f:	45 31 c0             	xor    %r8d,%r8d
  405132:	48 98                	cltq
  405134:	48 8d 1c 40          	lea    (%rax,%rax,2),%rbx
  405138:	41 8d 41 ff          	lea    -0x1(%r9),%eax
  40513c:	48 c1 e3 07          	shl    $0x7,%rbx
  405140:	4d 8d 64 c2 08       	lea    0x8(%r10,%rax,8),%r12
  405145:	0f 1f 00             	nopl   (%rax)
  405148:	31 c0                	xor    %eax,%eax
  40514a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  405150:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
  405154:	48 8b 52 28          	mov    0x28(%rdx),%rdx
  405158:	48 8b 8c 1a e8 00 00 00 	mov    0xe8(%rdx,%rbx,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
  405160:	48 8b 17             	mov    (%rdi),%rdx
  405163:	48 8b 72 28          	mov    0x28(%rdx),%rsi
  405167:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
  40516a:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
  40516e:	48 c1 e2 05          	shl    $0x5,%rdx
  405172:	4a 03 94 1e e8 00 00 00 	add    0xe8(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
  40517a:	48 8b 52 08          	mov    0x8(%rdx),%rdx
  40517e:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
  405182:	4c 39 c8             	cmp    %r9,%rax
  405185:	75 c9                	jne    405150 <barriered_work+0xb0>
        for (int y = 0; y < data->thread_count ; y++) {
  405187:	48 83 c7 08          	add    $0x8,%rdi
  40518b:	49 83 c0 20          	add    $0x20,%r8
  40518f:	49 39 fc             	cmp    %rdi,%r12
  405192:	75 b4                	jne    405148 <barriered_work+0xa8>
      asm volatile ("sfence" ::: "memory");
  405194:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
  405197:	48 8b b5 d8 00 00 00 	mov    0xd8(%rbp),%rsi
  40519e:	31 ff                	xor    %edi,%edi
  4051a0:	48 c1 e6 05          	shl    $0x5,%rsi
  4051a4:	48 03 b5 c8 00 00 00 	add    0xc8(%rbp),%rsi
  4051ab:	e8 d0 ce ff ff       	call   402080 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
  4051b0:	48 8b 85 a8 00 00 00 	mov    0xa8(%rbp),%rax
  4051b7:	48 8b 50 38          	mov    0x38(%rax),%rdx
  4051bb:	8b 5a 10             	mov    0x10(%rdx),%ebx
  4051be:	83 c3 01             	add    $0x1,%ebx
    while (data->scheduled == 1) {
  4051c1:	83 bd c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbp)
    int modcount = ++data->thread->protected_state->modcount;
  4051c8:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
  4051cb:	75 58                	jne    405225 <barriered_work+0x185>
  4051cd:	0f 1f 00             	nopl   (%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
  4051d0:	48 63 95 b0 00 00 00 	movslq 0xb0(%rbp),%rdx
  4051d7:	48 8b 40 10          	mov    0x10(%rax),%rax
      data->n++;
  4051db:	48 83 85 88 00 00 00 01 	addq   $0x1,0x88(%rbp)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
  4051e3:	48 8b 14 d0          	mov    (%rax,%rdx,8),%rdx
  4051e7:	48 63 45 00          	movslq 0x0(%rbp),%rax
  4051eb:	48 8d 3c 40          	lea    (%rax,%rax,2),%rdi
  4051ef:	48 c1 e7 07          	shl    $0x7,%rdi
  4051f3:	48 03 7a 28          	add    0x28(%rdx),%rdi
  4051f7:	ff 95 a0 00 00 00    	call   *0xa0(%rbp)
      asm volatile ("sfence" ::: "memory");
  4051fd:	0f ae f8             	sfence
    while (data->scheduled == 1) {
  405200:	83 bd c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbp)
    if (modcount != data->thread->protected_state->modcount) {
  405207:	48 8b 85 a8 00 00 00 	mov    0xa8(%rbp),%rax
    while (data->scheduled == 1) {
  40520e:	74 c0                	je     4051d0 <barriered_work+0x130>
    if (modcount != data->thread->protected_state->modcount) {
  405210:	48 8b 40 38          	mov    0x38(%rax),%rax
  405214:	3b 58 10             	cmp    0x10(%rax),%ebx
  405217:	74 0c                	je     405225 <barriered_work+0x185>
  405219:	48 8d 3d f0 0f 00 00 	lea    0xff0(%rip),%rdi        # 406210 <_IO_stdin_used+0x210>
  405220:	e8 3b ce ff ff       	call   402060 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
  405225:	48 8b b5 d8 00 00 00 	mov    0xd8(%rbp),%rsi
  40522c:	31 ff                	xor    %edi,%edi
  40522e:	48 c1 e6 05          	shl    $0x5,%rsi
  405232:	48 03 b5 c8 00 00 00 	add    0xc8(%rbp),%rsi
  405239:	48 83 c6 10          	add    $0x10,%rsi
  40523d:	e8 3e ce ff ff       	call   402080 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
  405242:	48 8b 85 d8 00 00 00 	mov    0xd8(%rbp),%rax
    sendm(data);
  405249:	48 89 ef             	mov    %rbp,%rdi
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
  40524c:	48 83 c0 01          	add    $0x1,%rax
  405250:	48 99                	cqto
  405252:	48 f7 bd d0 00 00 00 	idivq  0xd0(%rbp)
  405259:	48 89 95 d8 00 00 00 	mov    %rdx,0xd8(%rbp)
    sendm(data);
  405260:	e8 bb fb ff ff       	call   404e20 <sendm>
  405265:	e9 72 fe ff ff       	jmp    4050dc <barriered_work+0x3c>
  40526a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000405270 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
  405270:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
  405274:	48 8b 87 a8 00 00 00 	mov    0xa8(%rdi),%rax
  40527b:	48 8b 40 40          	mov    0x40(%rax),%rax
  40527f:	8b 10                	mov    (%rax),%edx
  405281:	85 d2                	test   %edx,%edx
  405283:	7e 37                	jle    4052bc <barriered_work_ingest+0x4c>
    if (data->thread->buffers->buffer[x].available == 1) {
  405285:	48 8b 48 08          	mov    0x8(%rax),%rcx
  405289:	83 ea 01             	sub    $0x1,%edx
  40528c:	48 c1 e2 04          	shl    $0x4,%rdx
  405290:	48 8d 41 08          	lea    0x8(%rcx),%rax
  405294:	48 8d 54 11 18       	lea    0x18(%rcx,%rdx,1),%rdx
  405299:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  4052a0:	83 38 01             	cmpl   $0x1,(%rax)
  4052a3:	75 0e                	jne    4052b3 <barriered_work_ingest+0x43>
      data->ingest_count++;
  4052a5:	48 83 87 e0 00 00 00 01 	addq   $0x1,0xe0(%rdi)
      data->thread->buffers->buffer[x].available = 0;
  4052ad:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
  4052b3:	48 83 c0 10          	add    $0x10,%rax
  4052b7:	48 39 d0             	cmp    %rdx,%rax
  4052ba:	75 e4                	jne    4052a0 <barriered_work_ingest+0x30>
  asm volatile ("sfence" ::: "memory");
  4052bc:	0f ae f8             	sfence
  barriered_work(data);
  4052bf:	e8 dc fd ff ff       	call   4050a0 <barriered_work>
}
  4052c4:	31 c0                	xor    %eax,%eax
  4052c6:	48 83 c4 08          	add    $0x8,%rsp
  4052ca:	c3                   	ret
  4052cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000004052d0 <barriered_nulltask>:
}
  4052d0:	31 c0                	xor    %eax,%eax
  4052d2:	c3                   	ret
  4052d3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4052de:	66 90                	xchg   %ax,%ax

00000000004052e0 <barriered_steal>:
  4052e0:	31 c0                	xor    %eax,%eax
  4052e2:	c3                   	ret
  4052e3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4052ee:	66 90                	xchg   %ax,%ax

00000000004052f0 <after>:
  return left.tv_sec > right.tv_sec &&
  4052f0:	31 c0                	xor    %eax,%eax
  4052f2:	48 39 d7             	cmp    %rdx,%rdi
  4052f5:	7e 08                	jle    4052ff <after+0xf>
  4052f7:	31 c0                	xor    %eax,%eax
  4052f9:	48 39 ce             	cmp    %rcx,%rsi
  4052fc:	0f 9f c0             	setg   %al
}
  4052ff:	c3                   	ret

0000000000405300 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
  405300:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
  405305:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
  40530a:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
  40530c:	48 39 d7             	cmp    %rdx,%rdi
  40530f:	7f 18                	jg     405329 <within+0x29>
  405311:	4d 39 d8             	cmp    %r11,%r8
  405314:	0f 9e c2             	setle  %dl
  405317:	48 39 ce             	cmp    %rcx,%rsi
  40531a:	0f 9e c0             	setle  %al
  40531d:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
  40531f:	31 c0                	xor    %eax,%eax
  405321:	4d 39 d1             	cmp    %r10,%r9
  405324:	0f 9e c0             	setle  %al
    return 1;
  405327:	21 d0                	and    %edx,%eax
}
  405329:	c3                   	ret
  40532a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000405330 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
  405330:	48 83 ec 08          	sub    $0x8,%rsp
  if (after(left.start, right.start) && after(right.end, left.end)) {
  405334:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  405339:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
  40533e:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
  405343:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  405348:	e8 a3 ff ff ff       	call   4052f0 <after>
  40534d:	85 c0                	test   %eax,%eax
  40534f:	74 21                	je     405372 <overlap+0x42>
  405351:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  405356:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
  40535b:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
  405360:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
  405365:	e8 86 ff ff ff       	call   4052f0 <after>
  40536a:	85 c0                	test   %eax,%eax
  40536c:	0f 85 ae 00 00 00    	jne    405420 <overlap+0xf0>
  if (after(right.start, left.start) && after(left.end, right.end)) {
  405372:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
  405377:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
  40537c:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
  405381:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
  405386:	e8 65 ff ff ff       	call   4052f0 <after>
  40538b:	85 c0                	test   %eax,%eax
  40538d:	74 1d                	je     4053ac <overlap+0x7c>
  40538f:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
  405394:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
  405399:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
  40539e:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  4053a3:	e8 48 ff ff ff       	call   4052f0 <after>
  4053a8:	85 c0                	test   %eax,%eax
  4053aa:	75 74                	jne    405420 <overlap+0xf0>
  if (within(left.start, right.start, right.end, left.end) == 1) {
  4053ac:	ff 74 24 28          	push   0x28(%rsp)
  4053b0:	ff 74 24 28          	push   0x28(%rsp)
  4053b4:	4c 8b 44 24 50       	mov    0x50(%rsp),%r8
  4053b9:	4c 8b 4c 24 58       	mov    0x58(%rsp),%r9
  4053be:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
  4053c3:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
  4053c8:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
  4053cd:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  4053d2:	e8 29 ff ff ff       	call   405300 <within>
  4053d7:	5e                   	pop    %rsi
  4053d8:	5f                   	pop    %rdi
  4053d9:	83 f8 01             	cmp    $0x1,%eax
  4053dc:	74 42                	je     405420 <overlap+0xf0>
  if (within(right.start, left.start, left.end, right.end) == 1) {
  4053de:	ff 74 24 48          	push   0x48(%rsp)
  4053e2:	ff 74 24 48          	push   0x48(%rsp)
  4053e6:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
  4053eb:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
  4053f0:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  4053f5:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
  4053fa:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
  4053ff:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
  405404:	e8 f7 fe ff ff       	call   405300 <within>
  405409:	5a                   	pop    %rdx
  40540a:	59                   	pop    %rcx
  40540b:	83 f8 01             	cmp    $0x1,%eax
  40540e:	0f 94 c0             	sete   %al
}
  405411:	48 83 c4 08          	add    $0x8,%rsp
  if (within(right.start, left.start, left.end, right.end) == 1) {
  405415:	0f b6 c0             	movzbl %al,%eax
}
  405418:	c3                   	ret
  405419:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    return 1;
  405420:	b8 01 00 00 00       	mov    $0x1,%eax
}
  405425:	48 83 c4 08          	add    $0x8,%rsp
  405429:	c3                   	ret
  40542a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000405430 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
  405430:	41 57                	push   %r15
  405432:	48 89 f8             	mov    %rdi,%rax
  405435:	41 56                	push   %r14
  405437:	41 55                	push   %r13
  405439:	41 54                	push   %r12
  40543b:	55                   	push   %rbp
  40543c:	53                   	push   %rbx
  40543d:	48 83 ec 38          	sub    $0x38,%rsp
  405441:	89 74 24 2c          	mov    %esi,0x2c(%rsp)
  for (int x = 0 ; x < thread_count; x++) {
  405445:	85 f6                	test   %esi,%esi
  405447:	0f 8e 7f 02 00 00    	jle    4056cc <verify+0x29c>
  40544d:	48 83 c0 28          	add    $0x28,%rax
  405451:	c7 44 24 1c 00 00 00 00 	movl   $0x0,0x1c(%rsp)
  405459:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  40545e:	49 89 c7             	mov    %rax,%r15
    for (int z = 0 ; z < thread_count; z++) {
  405461:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
  405469:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
  40546e:	8b 7c 24 28          	mov    0x28(%rsp),%edi
      if (z != x)  {
  405472:	39 7c 24 1c          	cmp    %edi,0x1c(%rsp)
  405476:	0f 84 79 01 00 00    	je     4055f5 <verify+0x1c5>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
  40547c:	41 8b 57 08          	mov    0x8(%r15),%edx
  405480:	85 d2                	test   %edx,%edx
  405482:	0f 8e 6d 01 00 00    	jle    4055f5 <verify+0x1c5>
  405488:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
  405490:	8b 54 24 1c          	mov    0x1c(%rsp),%edx
  405494:	48 8d 35 85 0d 00 00 	lea    0xd85(%rip),%rsi        # 406220 <_IO_stdin_used+0x220>
  40549b:	bf 01 00 00 00       	mov    $0x1,%edi
  4054a0:	31 c0                	xor    %eax,%eax
  4054a2:	e8 19 cd ff ff       	call   4021c0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  4054a7:	41 8b 46 08          	mov    0x8(%r14),%eax
  4054ab:	85 c0                	test   %eax,%eax
  4054ad:	0f 8e 2f 01 00 00    	jle    4055e2 <verify+0x1b2>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
  4054b3:	48 63 44 24 18       	movslq 0x18(%rsp),%rax
  4054b8:	49 8b 0f             	mov    (%r15),%rcx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  4054bb:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
  4054c3:	48 8d 2c 40          	lea    (%rax,%rax,2),%rbp
  4054c7:	48 c1 e5 07          	shl    $0x7,%rbp
  4054cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4054d0:	48 63 44 24 14       	movslq 0x14(%rsp),%rax
  4054d5:	48 8b 8c 29 d8 00 00 00 	mov    0xd8(%rcx,%rbp,1),%rcx
  4054dd:	bf 01 00 00 00       	mov    $0x1,%edi
  4054e2:	48 8d 35 4c 0d 00 00 	lea    0xd4c(%rip),%rsi        # 406235 <_IO_stdin_used+0x235>
  4054e9:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
  4054ed:	49 8b 06             	mov    (%r14),%rax
  4054f0:	4c 89 e3             	mov    %r12,%rbx
  4054f3:	48 c1 e3 07          	shl    $0x7,%rbx
  4054f7:	48 8b 94 18 d8 00 00 00 	mov    0xd8(%rax,%rbx,1),%rdx
  4054ff:	31 c0                	xor    %eax,%eax
  405501:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  405506:	e8 b5 cc ff ff       	call   4021c0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  40550b:	49 8b 0f             	mov    (%r15),%rcx
  40550e:	48 8b 94 29 d8 00 00 00 	mov    0xd8(%rcx,%rbp,1),%rdx
  405516:	48 85 d2             	test   %rdx,%rdx
  405519:	0f 8e b0 00 00 00    	jle    4055cf <verify+0x19f>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  40551f:	49 8b 06             	mov    (%r14),%rax
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  405522:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  40552a:	48 8b b4 18 d8 00 00 00 	mov    0xd8(%rax,%rbx,1),%rsi
  405532:	48 01 d8             	add    %rbx,%rax
  405535:	0f 1f 00             	nopl   (%rax)
  405538:	48 85 f6             	test   %rsi,%rsi
  40553b:	0f 8e 4f 01 00 00    	jle    405690 <verify+0x260>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
  405541:	48 63 5c 24 10       	movslq 0x10(%rsp),%rbx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  405546:	45 31 ed             	xor    %r13d,%r13d
  405549:	31 d2                	xor    %edx,%edx
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
  40554b:	48 c1 e3 05          	shl    $0x5,%rbx
  40554f:	90                   	nop
  405550:	48 8b 80 c8 00 00 00 	mov    0xc8(%rax),%rax
  405557:	48 c1 e2 05          	shl    $0x5,%rdx
  40555b:	49 89 d4             	mov    %rdx,%r12
  40555e:	ff 74 10 18          	push   0x18(%rax,%rdx,1)
  405562:	ff 74 10 10          	push   0x10(%rax,%rdx,1)
  405566:	ff 74 10 08          	push   0x8(%rax,%rdx,1)
  40556a:	ff 34 10             	push   (%rax,%rdx,1)
  40556d:	48 8b 84 29 c8 00 00 00 	mov    0xc8(%rcx,%rbp,1),%rax
  405575:	ff 74 18 18          	push   0x18(%rax,%rbx,1)
  405579:	ff 74 18 10          	push   0x10(%rax,%rbx,1)
  40557d:	ff 74 18 08          	push   0x8(%rax,%rbx,1)
  405581:	ff 34 18             	push   (%rax,%rbx,1)
  405584:	e8 a7 fd ff ff       	call   405330 <overlap>
  405589:	48 83 c4 40          	add    $0x40,%rsp
  40558d:	83 f8 01             	cmp    $0x1,%eax
  405590:	0f 84 8a 00 00 00    	je     405620 <verify+0x1f0>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  405596:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  40559b:	49 03 06             	add    (%r14),%rax
  40559e:	41 83 c5 01          	add    $0x1,%r13d
  4055a2:	48 8b b0 d8 00 00 00 	mov    0xd8(%rax),%rsi
  4055a9:	49 63 d5             	movslq %r13d,%rdx
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  4055ac:	49 8b 0f             	mov    (%r15),%rcx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  4055af:	48 39 f2             	cmp    %rsi,%rdx
  4055b2:	7c 9c                	jl     405550 <verify+0x120>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  4055b4:	83 44 24 10 01       	addl   $0x1,0x10(%rsp)
  4055b9:	48 8b 94 29 d8 00 00 00 	mov    0xd8(%rcx,%rbp,1),%rdx
  4055c1:	48 63 7c 24 10       	movslq 0x10(%rsp),%rdi
  4055c6:	48 39 d7             	cmp    %rdx,%rdi
  4055c9:	0f 8c 69 ff ff ff    	jl     405538 <verify+0x108>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  4055cf:	83 44 24 14 01       	addl   $0x1,0x14(%rsp)
  4055d4:	8b 44 24 14          	mov    0x14(%rsp),%eax
  4055d8:	41 39 46 08          	cmp    %eax,0x8(%r14)
  4055dc:	0f 8f ee fe ff ff    	jg     4054d0 <verify+0xa0>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
  4055e2:	83 44 24 18 01       	addl   $0x1,0x18(%rsp)
  4055e7:	8b 44 24 18          	mov    0x18(%rsp),%eax
  4055eb:	41 39 47 08          	cmp    %eax,0x8(%r15)
  4055ef:	0f 8f 9b fe ff ff    	jg     405490 <verify+0x60>
    for (int z = 0 ; z < thread_count; z++) {
  4055f5:	8b 44 24 28          	mov    0x28(%rsp),%eax
  4055f9:	49 81 c6 b0 00 00 00 	add    $0xb0,%r14
  405600:	83 c0 01             	add    $0x1,%eax
  405603:	39 44 24 2c          	cmp    %eax,0x2c(%rsp)
  405607:	0f 84 d0 00 00 00    	je     4056dd <verify+0x2ad>
  40560d:	89 44 24 28          	mov    %eax,0x28(%rsp)
  405611:	89 c7                	mov    %eax,%edi
  405613:	e9 5a fe ff ff       	jmp    405472 <verify+0x42>
  405618:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
  405620:	49 8b 06             	mov    (%r14),%rax
  405623:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  405628:	41 83 c5 01          	add    $0x1,%r13d
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
  40562c:	4c 03 a4 38 c8 00 00 00 	add    0xc8(%rax,%rdi,1),%r12
  405634:	49 8b 07             	mov    (%r15),%rax
  405637:	bf 01 00 00 00       	mov    $0x1,%edi
  40563c:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
  405641:	4d 8b 4c 24 18       	mov    0x18(%r12),%r9
  405646:	48 8b b4 28 c8 00 00 00 	mov    0xc8(%rax,%rbp,1),%rsi
  40564e:	31 c0                	xor    %eax,%eax
  405650:	48 01 de             	add    %rbx,%rsi
  405653:	48 8b 16             	mov    (%rsi),%rdx
  405656:	4c 8b 46 08          	mov    0x8(%rsi),%r8
  40565a:	48 8d 35 27 0e 00 00 	lea    0xe27(%rip),%rsi        # 406488 <_IO_stdin_used+0x488>
  405661:	e8 5a cb ff ff       	call   4021c0 <__printf_chk@plt>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  405666:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  40566b:	49 03 06             	add    (%r14),%rax
  40566e:	49 63 d5             	movslq %r13d,%rdx
  405671:	48 8b b0 d8 00 00 00 	mov    0xd8(%rax),%rsi
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  405678:	49 8b 0f             	mov    (%r15),%rcx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  40567b:	48 39 d6             	cmp    %rdx,%rsi
  40567e:	0f 8f cc fe ff ff    	jg     405550 <verify+0x120>
  405684:	e9 2b ff ff ff       	jmp    4055b4 <verify+0x184>
  405689:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  405690:	44 8b 6c 24 10       	mov    0x10(%rsp),%r13d
  405695:	41 83 c5 01          	add    $0x1,%r13d
  405699:	49 63 c5             	movslq %r13d,%rax
  40569c:	48 39 d0             	cmp    %rdx,%rax
  40569f:	0f 8d 2a ff ff ff    	jge    4055cf <verify+0x19f>
  4056a5:	0f 1f 00             	nopl   (%rax)
  4056a8:	41 83 c5 01          	add    $0x1,%r13d
  4056ac:	49 63 c5             	movslq %r13d,%rax
  4056af:	48 39 c2             	cmp    %rax,%rdx
  4056b2:	7f f4                	jg     4056a8 <verify+0x278>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  4056b4:	83 44 24 14 01       	addl   $0x1,0x14(%rsp)
  4056b9:	8b 44 24 14          	mov    0x14(%rsp),%eax
  4056bd:	41 39 46 08          	cmp    %eax,0x8(%r14)
  4056c1:	0f 8f 09 fe ff ff    	jg     4054d0 <verify+0xa0>
  4056c7:	e9 16 ff ff ff       	jmp    4055e2 <verify+0x1b2>
}
  4056cc:	48 83 c4 38          	add    $0x38,%rsp
  4056d0:	31 c0                	xor    %eax,%eax
  4056d2:	5b                   	pop    %rbx
  4056d3:	5d                   	pop    %rbp
  4056d4:	41 5c                	pop    %r12
  4056d6:	41 5d                	pop    %r13
  4056d8:	41 5e                	pop    %r14
  4056da:	41 5f                	pop    %r15
  4056dc:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
  4056dd:	8b 7c 24 1c          	mov    0x1c(%rsp),%edi
  4056e1:	49 81 c7 b0 00 00 00 	add    $0xb0,%r15
  4056e8:	8d 47 01             	lea    0x1(%rdi),%eax
  4056eb:	3b 7c 24 28          	cmp    0x28(%rsp),%edi
  4056ef:	74 db                	je     4056cc <verify+0x29c>
  4056f1:	89 44 24 1c          	mov    %eax,0x1c(%rsp)
  4056f5:	e9 67 fd ff ff       	jmp    405461 <verify+0x31>

Disassembly of section .fini:

00000000004056fc <_fini>:
  4056fc:	f3 0f 1e fa          	endbr64
  405700:	48 83 ec 08          	sub    $0x8,%rsp
  405704:	48 83 c4 08          	add    $0x8,%rsp
  405708:	c3                   	ret
