
multibarrier-split-io:     file format elf64-x86-64


Disassembly of section .init:

0000000000402000 <_init>:
  402000:	f3 0f 1e fa          	endbr64
  402004:	48 83 ec 08          	sub    $0x8,%rsp
  402008:	48 8b 05 d9 8f 00 00 	mov    0x8fd9(%rip),%rax        # 40afe8 <__gmon_start__@Base>
  40200f:	48 85 c0             	test   %rax,%rax
  402012:	74 02                	je     402016 <_init+0x16>
  402014:	ff d0                	call   *%rax
  402016:	48 83 c4 08          	add    $0x8,%rsp
  40201a:	c3                   	ret

Disassembly of section .plt:

0000000000402020 <putchar@plt-0x10>:
  402020:	ff 35 3a 8e 00 00    	push   0x8e3a(%rip)        # 40ae60 <_GLOBAL_OFFSET_TABLE_+0x8>
  402026:	ff 25 3c 8e 00 00    	jmp    *0x8e3c(%rip)        # 40ae68 <_GLOBAL_OFFSET_TABLE_+0x10>
  40202c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000402030 <putchar@plt>:
  402030:	ff 25 3a 8e 00 00    	jmp    *0x8e3a(%rip)        # 40ae70 <putchar@GLIBC_2.2.5>
  402036:	68 00 00 00 00       	push   $0x0
  40203b:	e9 e0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402040 <pthread_setaffinity_np@plt>:
  402040:	ff 25 32 8e 00 00    	jmp    *0x8e32(%rip)        # 40ae78 <pthread_setaffinity_np@GLIBC_2.34>
  402046:	68 01 00 00 00       	push   $0x1
  40204b:	e9 d0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402050 <puts@plt>:
  402050:	ff 25 2a 8e 00 00    	jmp    *0x8e2a(%rip)        # 40ae80 <puts@GLIBC_2.2.5>
  402056:	68 02 00 00 00       	push   $0x2
  40205b:	e9 c0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402060 <setsockopt@plt>:
  402060:	ff 25 22 8e 00 00    	jmp    *0x8e22(%rip)        # 40ae88 <setsockopt@GLIBC_2.2.5>
  402066:	68 03 00 00 00       	push   $0x3
  40206b:	e9 b0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402070 <clock_gettime@plt>:
  402070:	ff 25 1a 8e 00 00    	jmp    *0x8e1a(%rip)        # 40ae90 <clock_gettime@GLIBC_2.17>
  402076:	68 04 00 00 00       	push   $0x4
  40207b:	e9 a0 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402080 <fclose@plt>:
  402080:	ff 25 12 8e 00 00    	jmp    *0x8e12(%rip)        # 40ae98 <fclose@GLIBC_2.2.5>
  402086:	68 05 00 00 00       	push   $0x5
  40208b:	e9 90 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402090 <strlen@plt>:
  402090:	ff 25 0a 8e 00 00    	jmp    *0x8e0a(%rip)        # 40aea0 <strlen@GLIBC_2.2.5>
  402096:	68 06 00 00 00       	push   $0x6
  40209b:	e9 80 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020a0 <__stack_chk_fail@plt>:
  4020a0:	ff 25 02 8e 00 00    	jmp    *0x8e02(%rip)        # 40aea8 <__stack_chk_fail@GLIBC_2.4>
  4020a6:	68 07 00 00 00       	push   $0x7
  4020ab:	e9 70 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020b0 <io_uring_submit@plt>:
  4020b0:	ff 25 fa 8d 00 00    	jmp    *0x8dfa(%rip)        # 40aeb0 <io_uring_submit@LIBURING_2.0>
  4020b6:	68 08 00 00 00       	push   $0x8
  4020bb:	e9 60 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020c0 <nanosleep@plt>:
  4020c0:	ff 25 f2 8d 00 00    	jmp    *0x8df2(%rip)        # 40aeb8 <nanosleep@GLIBC_2.2.5>
  4020c6:	68 09 00 00 00       	push   $0x9
  4020cb:	e9 50 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020d0 <strrchr@plt>:
  4020d0:	ff 25 ea 8d 00 00    	jmp    *0x8dea(%rip)        # 40aec0 <strrchr@GLIBC_2.2.5>
  4020d6:	68 0a 00 00 00       	push   $0xa
  4020db:	e9 40 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020e0 <fputs@plt>:
  4020e0:	ff 25 e2 8d 00 00    	jmp    *0x8de2(%rip)        # 40aec8 <fputs@GLIBC_2.2.5>
  4020e6:	68 0b 00 00 00       	push   $0xb
  4020eb:	e9 30 ff ff ff       	jmp    402020 <_init+0x20>

00000000004020f0 <close@plt>:
  4020f0:	ff 25 da 8d 00 00    	jmp    *0x8dda(%rip)        # 40aed0 <close@GLIBC_2.2.5>
  4020f6:	68 0c 00 00 00       	push   $0xc
  4020fb:	e9 20 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402100 <strtok_r@plt>:
  402100:	ff 25 d2 8d 00 00    	jmp    *0x8dd2(%rip)        # 40aed8 <strtok_r@GLIBC_2.2.5>
  402106:	68 0d 00 00 00       	push   $0xd
  40210b:	e9 10 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402110 <read@plt>:
  402110:	ff 25 ca 8d 00 00    	jmp    *0x8dca(%rip)        # 40aee0 <read@GLIBC_2.2.5>
  402116:	68 0e 00 00 00       	push   $0xe
  40211b:	e9 00 ff ff ff       	jmp    402020 <_init+0x20>

0000000000402120 <calloc@plt>:
  402120:	ff 25 c2 8d 00 00    	jmp    *0x8dc2(%rip)        # 40aee8 <calloc@GLIBC_2.2.5>
  402126:	68 0f 00 00 00       	push   $0xf
  40212b:	e9 f0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402130 <strcmp@plt>:
  402130:	ff 25 ba 8d 00 00    	jmp    *0x8dba(%rip)        # 40aef0 <strcmp@GLIBC_2.2.5>
  402136:	68 10 00 00 00       	push   $0x10
  40213b:	e9 e0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402140 <__memcpy_chk@plt>:
  402140:	ff 25 b2 8d 00 00    	jmp    *0x8db2(%rip)        # 40aef8 <__memcpy_chk@GLIBC_2.3.4>
  402146:	68 11 00 00 00       	push   $0x11
  40214b:	e9 d0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402150 <stat@plt>:
  402150:	ff 25 aa 8d 00 00    	jmp    *0x8daa(%rip)        # 40af00 <stat@GLIBC_2.33>
  402156:	68 12 00 00 00       	push   $0x12
  40215b:	e9 c0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402160 <memcpy@plt>:
  402160:	ff 25 a2 8d 00 00    	jmp    *0x8da2(%rip)        # 40af08 <memcpy@GLIBC_2.14>
  402166:	68 13 00 00 00       	push   $0x13
  40216b:	e9 b0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402170 <io_uring_queue_init@plt>:
  402170:	ff 25 9a 8d 00 00    	jmp    *0x8d9a(%rip)        # 40af10 <io_uring_queue_init@LIBURING_2.0>
  402176:	68 14 00 00 00       	push   $0x14
  40217b:	e9 a0 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402180 <eventfd_write@plt>:
  402180:	ff 25 92 8d 00 00    	jmp    *0x8d92(%rip)        # 40af18 <eventfd_write@GLIBC_2.7>
  402186:	68 15 00 00 00       	push   $0x15
  40218b:	e9 90 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402190 <malloc@plt>:
  402190:	ff 25 8a 8d 00 00    	jmp    *0x8d8a(%rip)        # 40af20 <malloc@GLIBC_2.2.5>
  402196:	68 16 00 00 00       	push   $0x16
  40219b:	e9 80 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021a0 <listen@plt>:
  4021a0:	ff 25 82 8d 00 00    	jmp    *0x8d82(%rip)        # 40af28 <listen@GLIBC_2.2.5>
  4021a6:	68 17 00 00 00       	push   $0x17
  4021ab:	e9 70 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021b0 <__strcpy_chk@plt>:
  4021b0:	ff 25 7a 8d 00 00    	jmp    *0x8d7a(%rip)        # 40af30 <__strcpy_chk@GLIBC_2.3.4>
  4021b6:	68 18 00 00 00       	push   $0x18
  4021bb:	e9 60 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021c0 <__io_uring_get_cqe@plt>:
  4021c0:	ff 25 72 8d 00 00    	jmp    *0x8d72(%rip)        # 40af38 <__io_uring_get_cqe@LIBURING_2.0>
  4021c6:	68 19 00 00 00       	push   $0x19
  4021cb:	e9 50 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021d0 <__printf_chk@plt>:
  4021d0:	ff 25 6a 8d 00 00    	jmp    *0x8d6a(%rip)        # 40af40 <__printf_chk@GLIBC_2.3.4>
  4021d6:	68 1a 00 00 00       	push   $0x1a
  4021db:	e9 40 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021e0 <bind@plt>:
  4021e0:	ff 25 62 8d 00 00    	jmp    *0x8d62(%rip)        # 40af48 <bind@GLIBC_2.2.5>
  4021e6:	68 1b 00 00 00       	push   $0x1b
  4021eb:	e9 30 fe ff ff       	jmp    402020 <_init+0x20>

00000000004021f0 <pthread_create@plt>:
  4021f0:	ff 25 5a 8d 00 00    	jmp    *0x8d5a(%rip)        # 40af50 <pthread_create@GLIBC_2.34>
  4021f6:	68 1c 00 00 00       	push   $0x1c
  4021fb:	e9 20 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402200 <io_uring_wait_cqe_timeout@plt>:
  402200:	ff 25 52 8d 00 00    	jmp    *0x8d52(%rip)        # 40af58 <io_uring_wait_cqe_timeout@LIBURING_2.0>
  402206:	68 1d 00 00 00       	push   $0x1d
  40220b:	e9 10 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402210 <open@plt>:
  402210:	ff 25 4a 8d 00 00    	jmp    *0x8d4a(%rip)        # 40af60 <open@GLIBC_2.2.5>
  402216:	68 1e 00 00 00       	push   $0x1e
  40221b:	e9 00 fe ff ff       	jmp    402020 <_init+0x20>

0000000000402220 <fopen@plt>:
  402220:	ff 25 42 8d 00 00    	jmp    *0x8d42(%rip)        # 40af68 <fopen@GLIBC_2.2.5>
  402226:	68 1f 00 00 00       	push   $0x1f
  40222b:	e9 f0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402230 <perror@plt>:
  402230:	ff 25 3a 8d 00 00    	jmp    *0x8d3a(%rip)        # 40af70 <perror@GLIBC_2.2.5>
  402236:	68 20 00 00 00       	push   $0x20
  40223b:	e9 e0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402240 <exit@plt>:
  402240:	ff 25 32 8d 00 00    	jmp    *0x8d32(%rip)        # 40af78 <exit@GLIBC_2.2.5>
  402246:	68 21 00 00 00       	push   $0x21
  40224b:	e9 d0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402250 <eventfd@plt>:
  402250:	ff 25 2a 8d 00 00    	jmp    *0x8d2a(%rip)        # 40af80 <eventfd@GLIBC_2.7>
  402256:	68 22 00 00 00       	push   $0x22
  40225b:	e9 c0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402260 <fwrite@plt>:
  402260:	ff 25 22 8d 00 00    	jmp    *0x8d22(%rip)        # 40af88 <fwrite@GLIBC_2.2.5>
  402266:	68 23 00 00 00       	push   $0x23
  40226b:	e9 b0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402270 <__fprintf_chk@plt>:
  402270:	ff 25 1a 8d 00 00    	jmp    *0x8d1a(%rip)        # 40af90 <__fprintf_chk@GLIBC_2.3.4>
  402276:	68 24 00 00 00       	push   $0x24
  40227b:	e9 a0 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402280 <io_uring_register_eventfd@plt>:
  402280:	ff 25 12 8d 00 00    	jmp    *0x8d12(%rip)        # 40af98 <io_uring_register_eventfd@LIBURING_2.0>
  402286:	68 25 00 00 00       	push   $0x25
  40228b:	e9 90 fd ff ff       	jmp    402020 <_init+0x20>

0000000000402290 <pthread_join@plt>:
  402290:	ff 25 0a 8d 00 00    	jmp    *0x8d0a(%rip)        # 40afa0 <pthread_join@GLIBC_2.34>
  402296:	68 26 00 00 00       	push   $0x26
  40229b:	e9 80 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022a0 <strerror@plt>:
  4022a0:	ff 25 02 8d 00 00    	jmp    *0x8d02(%rip)        # 40afa8 <strerror@GLIBC_2.2.5>
  4022a6:	68 27 00 00 00       	push   $0x27
  4022ab:	e9 70 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022b0 <pthread_mutex_init@plt>:
  4022b0:	ff 25 fa 8c 00 00    	jmp    *0x8cfa(%rip)        # 40afb0 <pthread_mutex_init@GLIBC_2.2.5>
  4022b6:	68 28 00 00 00       	push   $0x28
  4022bb:	e9 60 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022c0 <epoll_create1@plt>:
  4022c0:	ff 25 f2 8c 00 00    	jmp    *0x8cf2(%rip)        # 40afb8 <epoll_create1@GLIBC_2.9>
  4022c6:	68 29 00 00 00       	push   $0x29
  4022cb:	e9 50 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022d0 <__ctype_tolower_loc@plt>:
  4022d0:	ff 25 ea 8c 00 00    	jmp    *0x8cea(%rip)        # 40afc0 <__ctype_tolower_loc@GLIBC_2.3>
  4022d6:	68 2a 00 00 00       	push   $0x2a
  4022db:	e9 40 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022e0 <__sprintf_chk@plt>:
  4022e0:	ff 25 e2 8c 00 00    	jmp    *0x8ce2(%rip)        # 40afc8 <__sprintf_chk@GLIBC_2.3.4>
  4022e6:	68 2b 00 00 00       	push   $0x2b
  4022eb:	e9 30 fd ff ff       	jmp    402020 <_init+0x20>

00000000004022f0 <socket@plt>:
  4022f0:	ff 25 da 8c 00 00    	jmp    *0x8cda(%rip)        # 40afd0 <socket@GLIBC_2.2.5>
  4022f6:	68 2c 00 00 00       	push   $0x2c
  4022fb:	e9 20 fd ff ff       	jmp    402020 <_init+0x20>

Disassembly of section .text:

0000000000402300 <add_read_request.cold>:

static inline void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
  402300:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  402308:	0f 0b                	ud2

000000000040230a <add_accept_request.cold>:
  40230a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  402312:	0f 0b                	ud2

0000000000402314 <io_thread.cold>:
  402314:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  40231c:	0f 0b                	ud2
            int client_socket = write->client_socket; 
            // printf("%p write\n", write);
            struct io_uring_sqe *sqe = io_uring_get_sqe(&ring);
            struct Request *req = write->request;
            // printf("req %p\n", req);
            req->event_type = EVENT_TYPE_WRITE;
  40231e:	48 8b 06             	mov    (%rsi),%rax
  402321:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
  402327:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
  40232f:	0f 0b                	ud2
  402331:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  40233b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

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
  402342:	48 8d 3d 27 65 00 00 	lea    0x6527(%rip),%rdi        # 408870 <_IO_stdin_used+0x870>
  402349:	41 56                	push   %r14
  40234b:	4c 8d 35 93 60 00 00 	lea    0x6093(%rip),%r14        # 4083e5 <_IO_stdin_used+0x3e5>
  402352:	41 55                	push   %r13
  402354:	41 54                	push   %r12
  402356:	55                   	push   %rbp
  402357:	53                   	push   %rbx
  402358:	48 81 ec f8 00 00 00 	sub    $0xf8,%rsp
  40235f:	f3 0f 7e 35 89 8c 00 00 	movq   0x8c89(%rip),%xmm6        # 40aff0 <_GLOBAL_OFFSET_TABLE_+0x198>
  402367:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  402370:	48 89 84 24 e8 00 00 00 	mov    %rax,0xe8(%rsp)
  402378:	31 c0                	xor    %eax,%eax
  40237a:	0f 16 35 5f 8c 00 00 	movhps 0x8c5f(%rip),%xmm6        # 40afe0 <_GLOBAL_OFFSET_TABLE_+0x188>
  402381:	0f 29 b4 24 80 00 00 00 	movaps %xmm6,0x80(%rsp)
  402389:	e8 c2 fc ff ff       	call   402050 <puts@plt>
  40238e:	bf 0a 00 00 00       	mov    $0xa,%edi
  402393:	e8 98 fc ff ff       	call   402030 <putchar@plt>
  402398:	ba 01 00 00 00       	mov    $0x1,%edx
  40239d:	48 8d 35 39 5f 00 00 	lea    0x5f39(%rip),%rsi        # 4082dd <_IO_stdin_used+0x2dd>
  4023a4:	31 c0                	xor    %eax,%eax
  4023a6:	bf 01 00 00 00       	mov    $0x1,%edi
  4023ab:	e8 20 fe ff ff       	call   4021d0 <__printf_chk@plt>
  4023b0:	ba 02 00 00 00       	mov    $0x2,%edx
  4023b5:	48 8d 35 31 5f 00 00 	lea    0x5f31(%rip),%rsi        # 4082ed <_IO_stdin_used+0x2ed>
  4023bc:	31 c0                	xor    %eax,%eax
  4023be:	bf 01 00 00 00       	mov    $0x1,%edi
  4023c3:	e8 08 fe ff ff       	call   4021d0 <__printf_chk@plt>
  4023c8:	ba 01 00 00 00       	mov    $0x1,%edx
  4023cd:	48 8d 35 2e 5f 00 00 	lea    0x5f2e(%rip),%rsi        # 408302 <_IO_stdin_used+0x302>
  4023d4:	31 c0                	xor    %eax,%eax
  4023d6:	bf 01 00 00 00       	mov    $0x1,%edi
  4023db:	e8 f0 fd ff ff       	call   4021d0 <__printf_chk@plt>
  4023e0:	ba 02 00 00 00       	mov    $0x2,%edx
  4023e5:	48 8d 35 26 5f 00 00 	lea    0x5f26(%rip),%rsi        # 408312 <_IO_stdin_used+0x312>
  4023ec:	31 c0                	xor    %eax,%eax
  4023ee:	bf 01 00 00 00       	mov    $0x1,%edi
  4023f3:	e8 d8 fd ff ff       	call   4021d0 <__printf_chk@plt>
  4023f8:	48 8d 3d 29 5f 00 00 	lea    0x5f29(%rip),%rdi        # 408328 <_IO_stdin_used+0x328>
  4023ff:	e8 4c fc ff ff       	call   402050 <puts@plt>
  402404:	ba 02 00 00 00       	mov    $0x2,%edx
  402409:	48 8d 35 34 5f 00 00 	lea    0x5f34(%rip),%rsi        # 408344 <_IO_stdin_used+0x344>
  402410:	31 c0                	xor    %eax,%eax
  402412:	bf 01 00 00 00       	mov    $0x1,%edi
  402417:	e8 b4 fd ff ff       	call   4021d0 <__printf_chk@plt>
  40241c:	ba 07 00 00 00       	mov    $0x7,%edx
  402421:	48 8d 35 36 5f 00 00 	lea    0x5f36(%rip),%rsi        # 40835e <_IO_stdin_used+0x35e>
  402428:	31 c0                	xor    %eax,%eax
  40242a:	bf 01 00 00 00       	mov    $0x1,%edi
  40242f:	e8 9c fd ff ff       	call   4021d0 <__printf_chk@plt>
  402434:	ba 02 00 00 00       	mov    $0x2,%edx
  402439:	48 8d 35 32 5f 00 00 	lea    0x5f32(%rip),%rsi        # 408372 <_IO_stdin_used+0x372>
  402440:	31 c0                	xor    %eax,%eax
  402442:	bf 01 00 00 00       	mov    $0x1,%edi
  402447:	e8 84 fd ff ff       	call   4021d0 <__printf_chk@plt>
  40244c:	ba 01 00 00 00       	mov    $0x1,%edx
  402451:	48 8d 35 2b 5f 00 00 	lea    0x5f2b(%rip),%rsi        # 408383 <_IO_stdin_used+0x383>
  402458:	31 c0                	xor    %eax,%eax
  40245a:	bf 01 00 00 00       	mov    $0x1,%edi
  40245f:	e8 6c fd ff ff       	call   4021d0 <__printf_chk@plt>
  402464:	ba 02 00 00 00       	mov    $0x2,%edx
  402469:	48 8d 35 2b 5f 00 00 	lea    0x5f2b(%rip),%rsi        # 40839b <_IO_stdin_used+0x39b>
  402470:	31 c0                	xor    %eax,%eax
  402472:	bf 01 00 00 00       	mov    $0x1,%edi
  402477:	e8 54 fd ff ff       	call   4021d0 <__printf_chk@plt>
  40247c:	ba 01 00 00 00       	mov    $0x1,%edx
  402481:	48 8d 35 50 64 00 00 	lea    0x6450(%rip),%rsi        # 4088d8 <_IO_stdin_used+0x8d8>
  402488:	31 c0                	xor    %eax,%eax
  40248a:	bf 01 00 00 00       	mov    $0x1,%edi
  40248f:	e8 3c fd ff ff       	call   4021d0 <__printf_chk@plt>
  402494:	ba 01 00 00 00       	mov    $0x1,%edx
  402499:	48 8d 35 68 64 00 00 	lea    0x6468(%rip),%rsi        # 408908 <_IO_stdin_used+0x908>
  4024a0:	31 c0                	xor    %eax,%eax
  4024a2:	bf 01 00 00 00       	mov    $0x1,%edi
  4024a7:	e8 24 fd ff ff       	call   4021d0 <__printf_chk@plt>
  4024ac:	ba 40 42 0f 00       	mov    $0xf4240,%edx
  4024b1:	48 8d 35 ff 5e 00 00 	lea    0x5eff(%rip),%rsi        # 4083b7 <_IO_stdin_used+0x3b7>
  4024b8:	31 c0                	xor    %eax,%eax
  4024ba:	bf 01 00 00 00       	mov    $0x1,%edi
  4024bf:	e8 0c fd ff ff       	call   4021d0 <__printf_chk@plt>
  4024c4:	ba 0a 00 00 00       	mov    $0xa,%edx
  4024c9:	48 8d 35 01 5f 00 00 	lea    0x5f01(%rip),%rsi        # 4083d1 <_IO_stdin_used+0x3d1>
  4024d0:	31 c0                	xor    %eax,%eax
  4024d2:	bf 01 00 00 00       	mov    $0x1,%edi
  4024d7:	e8 f4 fc ff ff       	call   4021d0 <__printf_chk@plt>
  4024dc:	48 8d 3d 12 5c 00 00 	lea    0x5c12(%rip),%rdi        # 4080f5 <_IO_stdin_used+0xf5>
  4024e3:	e8 68 fb ff ff       	call   402050 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *global_protected_state = calloc(1, sizeof(struct ProtectedState));
  4024e8:	be 18 00 00 00       	mov    $0x18,%esi
  4024ed:	bf 01 00 00 00       	mov    $0x1,%edi
  4024f2:	e8 29 fc ff ff       	call   402120 <calloc@plt>
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
  4024f7:	be 18 00 00 00       	mov    $0x18,%esi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  int cc = 0; 
  for (int x = 0 ; x < total_threads; x++) {
  4024fc:	31 ed                	xor    %ebp,%ebp
  int cc = 0; 
  4024fe:	31 db                	xor    %ebx,%ebx
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
  402500:	bf 01 00 00 00       	mov    $0x1,%edi
  struct ProtectedState *global_protected_state = calloc(1, sizeof(struct ProtectedState));
  402505:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
  40250a:	e8 11 fc ff ff       	call   402120 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  40250f:	be 30 01 00 00       	mov    $0x130,%esi
  402514:	bf 07 00 00 00       	mov    $0x7,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
  402519:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  40251e:	e8 fd fb ff ff       	call   402120 <calloc@plt>
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  402523:	be 28 00 00 00       	mov    $0x28,%esi
  402528:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  40252d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  402532:	e8 e9 fb ff ff       	call   402120 <calloc@plt>
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  402537:	be 28 00 00 00       	mov    $0x28,%esi
  40253c:	bf 31 00 00 00       	mov    $0x31,%edi
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  402541:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  402546:	e8 d5 fb ff ff       	call   402120 <calloc@plt>
  40254b:	66 48 0f 6e f8       	movq   %rax,%xmm7
  402550:	49 89 c5             	mov    %rax,%r13
  402553:	0f 16 7c 24 10       	movhps 0x10(%rsp),%xmm7
  402558:	0f 29 bc 24 a0 00 00 00 	movaps %xmm7,0xa0(%rsp)
    for (int y = 0 ; y < total_threads; y++) {
  402560:	45 31 ff             	xor    %r15d,%r15d
  402563:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  402568:	46 8d 24 3b          	lea    (%rbx,%r15,1),%r12d
  40256c:	45 89 f8             	mov    %r15d,%r8d
  40256f:	89 e9                	mov    %ebp,%ecx
  402571:	4c 89 f6             	mov    %r14,%rsi
  402574:	44 89 e2             	mov    %r12d,%edx
  402577:	bf 01 00 00 00       	mov    $0x1,%edi
  40257c:	31 c0                	xor    %eax,%eax
  40257e:	41 83 c7 01          	add    $0x1,%r15d
  402582:	e8 49 fc ff ff       	call   4021d0 <__printf_chk@plt>
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
  402587:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
  40258b:	31 f6                	xor    %esi,%esi
  40258d:	49 8d 7c c5 00       	lea    0x0(%r13,%rax,8),%rdi
  402592:	e8 19 fd ff ff       	call   4022b0 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
  402597:	41 83 ff 07          	cmp    $0x7,%r15d
  40259b:	75 cb                	jne    402568 <main+0x228>
      pthread_mutex_init(&swapmutex[cc++], NULL);
  40259d:	83 c3 07             	add    $0x7,%ebx
  for (int x = 0 ; x < total_threads; x++) {
  4025a0:	83 c5 01             	add    $0x1,%ebp
  4025a3:	83 fb 31             	cmp    $0x31,%ebx
  4025a6:	75 b8                	jne    402560 <main+0x220>
  4025a8:	ba 02 00 00 00       	mov    $0x2,%edx
  4025ad:	48 8d 35 41 5e 00 00 	lea    0x5e41(%rip),%rsi        # 4083f5 <_IO_stdin_used+0x3f5>
  4025b4:	bf 01 00 00 00       	mov    $0x1,%edi
  4025b9:	31 c0                	xor    %eax,%eax
  4025bb:	e8 10 fc ff ff       	call   4021d0 <__printf_chk@plt>
  4025c0:	ba 04 00 00 00       	mov    $0x4,%edx
  4025c5:	48 8d 35 3f 5e 00 00 	lea    0x5e3f(%rip),%rsi        # 40840b <_IO_stdin_used+0x40b>
  4025cc:	31 c0                	xor    %eax,%eax
  4025ce:	bf 01 00 00 00       	mov    $0x1,%edi
  4025d3:	e8 f8 fb ff ff       	call   4021d0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
  4025d8:	be 10 00 00 00       	mov    $0x10,%esi
  4025dd:	bf 04 00 00 00       	mov    $0x4,%edi
  4025e2:	e8 39 fb ff ff       	call   402120 <calloc@plt>
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
  4025e7:	be 10 00 00 00       	mov    $0x10,%esi
  4025ec:	bf 02 00 00 00       	mov    $0x2,%edi
  4025f1:	66 48 0f 6e f0       	movq   %rax,%xmm6
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
  4025f6:	49 89 c7             	mov    %rax,%r15
  4025f9:	48 89 84 24 d0 00 00 00 	mov    %rax,0xd0(%rsp)
  402601:	66 0f 6c f6          	punpcklqdq %xmm6,%xmm6
    iobuffers[x].count = buffer_size;
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    for (int y = 0 ; y < buffer_size; y++) {
      iobuffers[x].buffer[y].available = 0;
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  402605:	4d 89 fd             	mov    %r15,%r13
  402608:	0f 29 b4 24 90 00 00 00 	movaps %xmm6,0x90(%rsp)
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
  402610:	e8 0b fb ff ff       	call   402120 <calloc@plt>
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  402615:	be 28 00 00 00       	mov    $0x28,%esi
  40261a:	bf 01 00 00 00       	mov    $0x1,%edi
    iobuffers[x].count = buffer_size;
  40261f:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
  402625:	48 89 c3             	mov    %rax,%rbx
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  402628:	e8 f3 fa ff ff       	call   402120 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  40262d:	be 20 00 00 00       	mov    $0x20,%esi
  402632:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  402637:	48 89 43 08          	mov    %rax,0x8(%rbx)
  40263b:	48 89 c5             	mov    %rax,%rbp
      iobuffers[x].buffer[y].available = 0;
  40263e:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
  402645:	c7 40 18 64 00 00 00 	movl   $0x64,0x18(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  40264c:	e8 cf fa ff ff       	call   402120 <calloc@plt>
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  402651:	be 28 00 00 00       	mov    $0x28,%esi
  402656:	bf 01 00 00 00       	mov    $0x1,%edi
    iobuffers[x].count = buffer_size;
  40265b:	c7 43 10 01 00 00 00 	movl   $0x1,0x10(%rbx)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  402662:	48 89 45 10          	mov    %rax,0x10(%rbp)
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  402666:	e8 b5 fa ff ff       	call   402120 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  40266b:	be 20 00 00 00       	mov    $0x20,%esi
  402670:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  402675:	48 89 43 18          	mov    %rax,0x18(%rbx)
  402679:	48 89 c5             	mov    %rax,%rbp
  40267c:	49 8d 5f 40          	lea    0x40(%r15),%rbx
      iobuffers[x].buffer[y].available = 0;
  402680:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
  402687:	c7 40 18 64 00 00 00 	movl   $0x64,0x18(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  40268e:	e8 8d fa ff ff       	call   402120 <calloc@plt>
  402693:	4c 89 7c 24 78       	mov    %r15,0x78(%rsp)
  402698:	48 89 45 10          	mov    %rax,0x10(%rbp)
    }
  }
  for (int x = 0 ; x < buffers_required; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  40269c:	be 28 00 00 00       	mov    $0x28,%esi
    buffers[x].count = buffer_size;
  4026a1:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  4026a9:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
  4026ae:	49 83 c5 10          	add    $0x10,%r13
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  4026b2:	e8 69 fa ff ff       	call   402120 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  4026b7:	be 20 00 00 00       	mov    $0x20,%esi
  4026bc:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
  4026c1:	49 89 45 f8          	mov    %rax,-0x8(%r13)
  4026c5:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
  4026c8:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
  4026cf:	c7 40 18 64 00 00 00 	movl   $0x64,0x18(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  4026d6:	e8 45 fa ff ff       	call   402120 <calloc@plt>
  4026db:	48 89 45 10          	mov    %rax,0x10(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
  4026df:	49 39 dd             	cmp    %rbx,%r13
  4026e2:	75 b8                	jne    40269c <main+0x35c>
  int iocur_buffer = 0;
  int swap = 0;
  int groupcount = 0;
  int seq = 0;
  int seqs[] = {1, 3, 6};
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
  4026e4:	be 08 00 00 00       	mov    $0x8,%esi
  4026e9:	bf 64 00 00 00       	mov    $0x64,%edi
  4026ee:	e8 2d fa ff ff       	call   402120 <calloc@plt>
  struct Global *global = calloc(1, sizeof(struct Global));
  4026f3:	be 10 00 00 00       	mov    $0x10,%esi
  4026f8:	bf 01 00 00 00       	mov    $0x1,%edi
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
  4026fd:	48 89 c3             	mov    %rax,%rbx
  struct Global *global = calloc(1, sizeof(struct Global));
  402700:	e8 1b fa ff ff       	call   402120 <calloc@plt>
  global->request_group_sync = -1;
  global->protected_state = global_protected_state;
  for (int k = 0 ; k < group_count ; k++) {
    struct Group * group_data = calloc(1, sizeof(struct Group));
  402705:	be 00 01 00 00       	mov    $0x100,%esi
  40270a:	bf 01 00 00 00       	mov    $0x1,%edi
  global->request_group_sync = -1;
  40270f:	c7 00 ff ff ff ff    	movl   $0xffffffff,(%rax)
  struct Global *global = calloc(1, sizeof(struct Global));
  402715:	49 89 c6             	mov    %rax,%r14
  402718:	48 89 84 24 c0 00 00 00 	mov    %rax,0xc0(%rsp)
  global->protected_state = global_protected_state;
  402720:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  402725:	49 89 46 08          	mov    %rax,0x8(%r14)
    struct Group * group_data = calloc(1, sizeof(struct Group));
  402729:	e8 f2 f9 ff ff       	call   402120 <calloc@plt>
  40272e:	66 48 0f 6e eb       	movq   %rbx,%xmm5
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
  402733:	be 08 00 00 00       	mov    $0x8,%esi
  402738:	bf 64 00 00 00       	mov    $0x64,%edi
  40273d:	66 48 0f 6e f8       	movq   %rax,%xmm7
    struct Group * group_data = calloc(1, sizeof(struct Group));
  402742:	49 89 c7             	mov    %rax,%r15
  402745:	48 89 84 24 c8 00 00 00 	mov    %rax,0xc8(%rsp)
  40274d:	66 0f 6c fd          	punpcklqdq %xmm5,%xmm7
  402751:	0f 29 bc 24 b0 00 00 00 	movaps %xmm7,0xb0(%rsp)
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
  402759:	e8 c2 f9 ff ff       	call   402120 <calloc@plt>
    all_groups[groupcount++] = group_data;
  40275e:	4c 89 3b             	mov    %r15,(%rbx)
    group_data->thread_count = threads_per_group * group_count;
    group_data->threads = group_threads;
  402761:	49 89 87 88 00 00 00 	mov    %rax,0x88(%r15)
    group_data->global = global;
    group_data->seq = seqs[seq++ % 3];
  402768:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    group_data->thread_count = threads_per_group * group_count;
  40276d:	41 c7 87 90 00 00 00 02 00 00 00 	movl   $0x2,0x90(%r15)
    group_data->global = global;
  402778:	4d 89 b7 98 00 00 00 	mov    %r14,0x98(%r15)
    group_data->seq = seqs[seq++ % 3];
  40277f:	41 c7 87 a0 00 00 00 01 00 00 00 	movl   $0x1,0xa0(%r15)
  40278a:	49 89 c7             	mov    %rax,%r15
      } else {
        thread_data[x].thread_index = 0;
        other = (x + 1) % total_threads;
        my_thread_data[0] = &thread_data[x]; 
        me_thread = 0;
        my_thread_data[1] = &thread_data[other]; 
  40278d:	48 05 30 01 00 00    	add    $0x130,%rax
    group_data->seq = seqs[seq++ % 3];
  402793:	48 c7 44 24 68 00 00 00 00 	movq   $0x0,0x68(%rsp)
  int swap = 0;
  40279c:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
  int dataid = 0;
  4027a4:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
        my_thread_data[1] = &thread_data[other]; 
  4027ac:	48 89 84 24 d8 00 00 00 	mov    %rax,0xd8(%rsp)
      thread_data[x].global = global;
  4027b4:	48 8b 84 24 c0 00 00 00 	mov    0xc0(%rsp),%rax
  4027bc:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
      thread_data[x].group = k;
  4027c1:	41 c7 87 f8 00 00 00 00 00 00 00 	movl   $0x0,0xf8(%r15)
  4027cc:	31 d2                	xor    %edx,%edx
      thread_data[x].group_data = group_data;
  4027ce:	66 0f 6f ac 24 b0 00 00 00 	movdqa 0xb0(%rsp),%xmm5
  4027d7:	48 8d 35 52 61 00 00 	lea    0x6152(%rip),%rsi        # 408930 <_IO_stdin_used+0x930>
  4027de:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].global = global;
  4027e3:	49 89 87 00 01 00 00 	mov    %rax,0x100(%r15)
  4027ea:	89 d9                	mov    %ebx,%ecx
  4027ec:	31 c0                	xor    %eax,%eax
  4027ee:	44 8d 24 1b          	lea    (%rbx,%rbx,1),%r12d
      thread_data[x].group_data = group_data;
  4027f2:	41 0f 11 af e8 00 00 00 	movups %xmm5,0xe8(%r15)
  4027fa:	41 89 dd             	mov    %ebx,%r13d
  4027fd:	e8 ce f9 ff ff       	call   4021d0 <__printf_chk@plt>
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  402802:	be 08 00 00 00       	mov    $0x8,%esi
  402807:	bf 02 00 00 00       	mov    $0x2,%edi
  40280c:	e8 0f f9 ff ff       	call   402120 <calloc@plt>
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
  402811:	be 80 00 00 00       	mov    $0x80,%esi
  402816:	bf 01 00 00 00       	mov    $0x1,%edi
  40281b:	66 48 0f 6e e0       	movq   %rax,%xmm4
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  402820:	48 89 c5             	mov    %rax,%rbp
      group_data->threads[group_thread_count++] = &thread_data[x];  
  402823:	48 8b 84 24 c8 00 00 00 	mov    0xc8(%rsp),%rax
  40282b:	0f 16 64 24 48       	movhps 0x48(%rsp),%xmm4
  402830:	48 8b 80 88 00 00 00 	mov    0x88(%rax),%rax
  402837:	0f 29 64 24 10       	movaps %xmm4,0x10(%rsp)
  40283c:	4c 89 3c d8          	mov    %r15,(%rax,%rbx,8)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
  402840:	e8 db f8 ff ff       	call   402120 <calloc@plt>
  402845:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
  402849:	49 89 c6             	mov    %rax,%r14
      if (x % 2 == 1) {
  40284c:	48 85 db             	test   %rbx,%rbx
  40284f:	0f 85 00 16 00 00    	jne    403e55 <main+0x1b15>
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  402855:	48 89 6c 24 50       	mov    %rbp,0x50(%rsp)
        my_thread_data[1] = &thread_data[other]; 
  40285a:	4c 89 fa             	mov    %r15,%rdx
  40285d:	45 31 c0             	xor    %r8d,%r8d
  402860:	bb 01 00 00 00       	mov    $0x1,%ebx
  402865:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
  40286d:	48 89 45 08          	mov    %rax,0x8(%rbp)
        // printf("even %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
        thread_data[x].protected_state = &protected_state[k];
  402871:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
  402876:	89 d9                	mov    %ebx,%ecx
  402878:	48 8d 35 41 63 00 00 	lea    0x6341(%rip),%rsi        # 408bc0 <_IO_stdin_used+0xbc0>
        thread_data[x].thread_index = 0;
  40287f:	45 89 47 04          	mov    %r8d,0x4(%r15)
  402883:	bf 01 00 00 00       	mov    $0x1,%edi
        my_thread_data[0] = &thread_data[x]; 
  402888:	48 89 55 00          	mov    %rdx,0x0(%rbp)
  40288c:	44 89 ea             	mov    %r13d,%edx
        thread_data[x].protected_state = &protected_state[k];
  40288f:	49 89 47 48          	mov    %rax,0x48(%r15)
  402893:	31 c0                	xor    %eax,%eax
  402895:	e8 36 f9 ff ff       	call   4021d0 <__printf_chk@plt>
  40289a:	44 89 ea             	mov    %r13d,%edx
  40289d:	44 89 e1             	mov    %r12d,%ecx
  4028a0:	bf 01 00 00 00       	mov    $0x1,%edi
      }
      printf("i am %d, other is %d my thread index is %d\n", x, other, thread_data[x].thread_index);
      thread_data[x].other = other;
  4028a5:	41 89 9f c8 00 00 00 	mov    %ebx,0xc8(%r15)
  4028ac:	48 8d 35 3d 63 00 00 	lea    0x633d(%rip),%rsi        # 408bf0 <_IO_stdin_used+0xbf0>
  4028b3:	31 c0                	xor    %eax,%eax
  4028b5:	e8 16 f9 ff ff       	call   4021d0 <__printf_chk@plt>
      // for (int j = 0 ; j < cores ; j++) {
        printf("assigning thread %d to core %d\n", x, curcpu);
        if (x < thread_count) {
          CPU_SET(curcpu, sendercpu);
  4028ba:	44 89 e1             	mov    %r12d,%ecx
      // setthread
      thread_data[x].swapmutex = swapmutex;
      thread_data[x].mswapmutex = mswapmutex;
      thread_data[x].kind = KERNEL_THREAD;
      thread_data[x].cpu_set = sendercpu;
      thread_data[x].real_thread_index = x;
  4028bd:	45 89 6f 08          	mov    %r13d,0x8(%r15)
          CPU_SET(curcpu, sendercpu);
  4028c1:	b8 01 00 00 00       	mov    $0x1,%eax
  4028c6:	48 d3 e0             	shl    %cl,%rax
  4028c9:	49 09 06             	or     %rax,(%r14)
      thread_data[x].threads = my_thread_data;
      thread_data[x].all_threads = thread_data;
      thread_data[x].thread_count = 2;
      thread_data[x].group_count = group_count;
  4028cc:	48 8b 05 0d 66 00 00 	mov    0x660d(%rip),%rax        # 408ee0 <_IO_stdin_used+0xee0>
      thread_data[x].threads_per_group = threads_per_group;
      thread_data[x].total_thread_count = total_threads;
      thread_data[x].task_count = total_barrier_count;
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  4028d3:	be 10 00 00 00       	mov    $0x10,%esi
      thread_data[x].threads = my_thread_data;
  4028d8:	66 0f 6f 74 24 10    	movdqa 0x10(%rsp),%xmm6
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  4028de:	bf 64 00 00 00       	mov    $0x64,%edi

        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
        thread_data[x].tasks = barriers;
        int assigned = 0;
        // external_thread_index = 0;
        for (int y = 0 ; y < total_barrier_count ; y++) {
  4028e3:	45 31 e4             	xor    %r12d,%r12d
      thread_data[x].swapmutex = swapmutex;
  4028e6:	66 0f 6f 9c 24 a0 00 00 00 	movdqa 0xa0(%rsp),%xmm3
      thread_data[x].group_count = group_count;
  4028ef:	49 89 87 d0 00 00 00 	mov    %rax,0xd0(%r15)
      thread_data[x].thread_count = 2;
  4028f6:	48 8b 05 d3 65 00 00 	mov    0x65d3(%rip),%rax        # 408ed0 <_IO_stdin_used+0xed0>
      thread_data[x].kind = KERNEL_THREAD;
  4028fd:	41 c7 07 5f 00 00 00 	movl   $0x5f,(%r15)
      thread_data[x].cpu_set = sendercpu;
  402904:	4d 89 b7 c0 00 00 00 	mov    %r14,0xc0(%r15)
      thread_data[x].thread_count = 2;
  40290b:	49 89 47 28          	mov    %rax,0x28(%r15)
      thread_data[x].task_count = total_barrier_count;
  40290f:	41 c7 47 40 03 00 00 00 	movl   $0x3,0x40(%r15)
      thread_data[x].swapmutex = swapmutex;
  402917:	41 0f 11 9f d8 00 00 00 	movups %xmm3,0xd8(%r15)
      thread_data[x].threads = my_thread_data;
  40291f:	41 0f 11 77 18       	movups %xmm6,0x18(%r15)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  402924:	e8 f7 f7 ff ff       	call   402120 <calloc@plt>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  402929:	be 10 00 00 00       	mov    $0x10,%esi
  40292e:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
  402933:	49 89 47 78          	mov    %rax,0x78(%r15)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  402937:	e8 e4 f7 ff ff       	call   402120 <calloc@plt>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  40293c:	be 28 00 00 00       	mov    $0x28,%esi
  402941:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].timestamp_count = 0;
  402946:	66 0f 6f 3d 62 65 00 00 	movdqa 0x6562(%rip),%xmm7        # 408eb0 <_IO_stdin_used+0xeb0>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
  40294e:	49 89 87 80 00 00 00 	mov    %rax,0x80(%r15)
      thread_data[x].timestamp_count = 0;
  402955:	41 0f 11 bf 90 00 00 00 	movups %xmm7,0x90(%r15)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  40295d:	e8 be f7 ff ff       	call   402120 <calloc@plt>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  402962:	be 00 02 00 00       	mov    $0x200,%esi
  402967:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
  40296c:	66 0f 6f 25 3c 65 00 00 	movdqa 0x653c(%rip),%xmm4        # 408eb0 <_IO_stdin_used+0xeb0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
  402974:	49 89 87 a0 00 00 00 	mov    %rax,0xa0(%r15)
      thread_data[x].task_timestamp_count = 0;
  40297b:	41 0f 11 a7 a8 00 00 00 	movups %xmm4,0xa8(%r15)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  402983:	e8 98 f7 ff ff       	call   402120 <calloc@plt>
  402988:	4c 89 7c 24 60       	mov    %r15,0x60(%rsp)
        thread_data[x].tasks = barriers;
  40298d:	49 89 47 38          	mov    %rax,0x38(%r15)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
  402991:	48 89 c3             	mov    %rax,%rbx
        for (int y = 0 ; y < total_barrier_count ; y++) {
  402994:	8b 44 24 08          	mov    0x8(%rsp),%eax
  402998:	83 f0 01             	xor    $0x1,%eax
  40299b:	89 44 24 30          	mov    %eax,0x30(%rsp)
                t     x
                a       x
                s         x
                k           x
          */
          thread_data[x].tasks[y].protected = do_protected_write; 
  40299f:	49 63 c4             	movslq %r12d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
  4029a2:	be 00 01 00 00       	mov    $0x100,%esi
  4029a7:	bf 02 00 00 00       	mov    $0x2,%edi
          thread_data[x].tasks[y].mailboxes = mailboxes;
          // long messages_limit = 20;/*9999999;*/
          
          // mailbox-create
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  4029ac:	31 ed                	xor    %ebp,%ebp
          thread_data[x].tasks[y].protected = do_protected_write; 
  4029ae:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  4029b3:	48 c1 e0 09          	shl    $0x9,%rax
  4029b7:	48 01 c3             	add    %rax,%rbx
  4029ba:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  4029bf:	48 c7 c0 90 3f 40 00 	mov    $0x403f90,%rax
  4029c6:	48 89 83 20 01 00 00 	mov    %rax,0x120(%rbx)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
  4029cd:	e8 4e f7 ff ff       	call   402120 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
  4029d2:	44 8b 74 24 20       	mov    0x20(%rsp),%r14d
  4029d7:	48 89 83 70 01 00 00 	mov    %rax,0x170(%rbx)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  4029de:	49 89 c7             	mov    %rax,%r15
  4029e1:	31 c9                	xor    %ecx,%ecx
  4029e3:	89 ea                	mov    %ebp,%edx
  4029e5:	48 8d 35 39 5a 00 00 	lea    0x5a39(%rip),%rsi        # 408425 <_IO_stdin_used+0x425>
  4029ec:	bf 01 00 00 00       	mov    $0x1,%edi
  4029f1:	31 c0                	xor    %eax,%eax
  4029f3:	49 81 c7 00 01 00 00 	add    $0x100,%r15
  4029fa:	e8 d1 f7 ff ff       	call   4021d0 <__printf_chk@plt>
            // k is group
            int group_of = b / threads_per_group;
            printf("group of %d %d\n", b, group_of);
            if (k == group_of) {
              // printf("Creating friend mailbox %d\n", b);
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  4029ff:	be 08 00 00 00       	mov    $0x8,%esi
  402a04:	bf 01 00 00 00       	mov    $0x1,%edi
  402a09:	e8 12 f7 ff ff       	call   402120 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402a0e:	be 08 00 00 00       	mov    $0x8,%esi
  402a13:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
  402a18:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402a1d:	e8 fe f6 ff ff       	call   402120 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
  402a22:	be 80 04 00 00       	mov    $0x480,%esi
  402a27:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
  402a2c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
  402a31:	e8 ea f6 ff ff       	call   402120 <calloc@plt>
              data[1].c = b;
              data[1].id = dataid++;

              mailboxes[b].lower = &data[0];
              mailboxes[b].higher = &data[1];
              mailboxes[b].pending_lower = NULL;
  402a36:	49 c7 47 88 00 00 00 00 	movq   $0x0,-0x78(%r15)
  402a3e:	89 ea                	mov    %ebp,%edx
  402a40:	48 8d 35 19 5f 00 00 	lea    0x5f19(%rip),%rsi        # 408960 <_IO_stdin_used+0x960>
              struct Data *data = calloc(3, sizeof(struct Data));
  402a47:	48 89 c3             	mov    %rax,%rbx
              data[0].a = x;
  402a4a:	44 89 a8 0c 04 00 00 	mov    %r13d,0x40c(%rax)
  402a51:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].kind = MAILBOX_LOWER;
  402a56:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
              data[0].b = y;
  402a60:	44 89 a0 10 04 00 00 	mov    %r12d,0x410(%rax)
              data[0].c = b;
  402a67:	89 a8 14 04 00 00    	mov    %ebp,0x414(%rax)
              data[0].id = dataid++;
  402a6d:	41 8d 46 01          	lea    0x1(%r14),%eax
              data[1].id = dataid++;
  402a71:	89 83 98 08 00 00    	mov    %eax,0x898(%rbx)
              mailboxes[b].higher = &data[1];
  402a77:	48 8d 83 80 04 00 00 	lea    0x480(%rbx),%rax
  402a7e:	49 89 47 80          	mov    %rax,-0x80(%r15)
  402a82:	8b 44 24 30          	mov    0x30(%rsp),%eax
              data[0].id = dataid++;
  402a86:	44 89 b3 18 04 00 00 	mov    %r14d,0x418(%rbx)
              data[1].id = dataid++;
  402a8d:	41 83 c6 02          	add    $0x2,%r14d
  402a91:	41 89 47 b4          	mov    %eax,-0x4c(%r15)
  402a95:	89 c1                	mov    %eax,%ecx
  402a97:	31 c0                	xor    %eax,%eax
              mailboxes[b].lower = &data[0];
  402a99:	49 89 9f 00 ff ff ff 	mov    %rbx,-0x100(%r15)
              mailboxes[b].pending_higher = NULL;
  402aa0:	49 c7 47 90 00 00 00 00 	movq   $0x0,-0x70(%r15)
              data[0].finished_reading = 1;
              data[1].finished_reading = 1;
              mailboxes[b].kind = MAILBOX_FRIEND;
  402aa8:	41 c7 47 b0 01 00 00 00 	movl   $0x1,-0x50(%r15)
              data[1].kind = MAILBOX_HIGHER;
  402ab0:	c7 83 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%rbx)
              data[1].a = x;
  402aba:	44 89 ab 8c 08 00 00 	mov    %r13d,0x88c(%rbx)
              data[1].b = y;
  402ac1:	44 89 a3 90 08 00 00 	mov    %r12d,0x890(%rbx)
              data[1].c = b;
  402ac8:	89 ab 94 08 00 00    	mov    %ebp,0x894(%rbx)
              data[0].finished_reading = 1;
  402ace:	c7 83 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rbx)
              data[1].finished_reading = 1;
  402ad8:	c7 83 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%rbx)
  402ae2:	e8 e9 f6 ff ff       	call   4021d0 <__printf_chk@plt>
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
              } else {
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
              }
              printf("Creating friend mailbox %d other is %d\n", b, mailboxes[b].other);
              data[0].messages = messages;
  402ae7:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
              data[1].messages = messages2;
  402aec:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
              data[0].messages_limit = messages_limit;
              data[0].messages_count = 0;
  402af1:	66 0f 6f 15 97 63 00 00 	movdqa 0x6397(%rip),%xmm2        # 408e90 <_IO_stdin_used+0xe90>
              data[0].messages = messages;
  402af9:	4c 89 13             	mov    %r10,(%rbx)
              data[1].messages = messages2;
  402afc:	4c 89 8b 80 04 00 00 	mov    %r9,0x480(%rbx)
              data[0].messages_count = 0;
  402b03:	0f 29 93 80 00 00 00 	movaps %xmm2,0x80(%rbx)
              data[1].messages_count = 0;
  402b0a:	0f 29 93 00 05 00 00 	movaps %xmm2,0x500(%rbx)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
  402b11:	83 fd 01             	cmp    $0x1,%ebp
  402b14:	0f 85 12 0f 00 00    	jne    403a2c <main+0x16ec>
            data[0].messages_count = 0;
            data[1].messages_count = 0;
            data[1].messages_limit = messages_limit;
          }

          char *message = malloc(sizeof(char) * 256);
  402b1a:	be 01 00 00 00       	mov    $0x1,%esi
  402b1f:	bf 00 01 00 00       	mov    $0x100,%edi
              data[1].id = dataid++;
  402b24:	83 44 24 20 04       	addl   $0x4,0x20(%rsp)
          char *message = malloc(sizeof(char) * 256);
  402b29:	e8 f2 f5 ff ff       	call   402120 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
  402b2e:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
  402b33:	48 89 c3             	mov    %rax,%rbx
          struct Message *messaged = malloc(sizeof(struct Message));
  402b36:	e8 55 f6 ff ff       	call   402190 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  402b3b:	48 83 ec 08          	sub    $0x8,%rsp
  402b3f:	45 89 e1             	mov    %r12d,%r9d
  402b42:	48 89 df             	mov    %rbx,%rdi
  402b45:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  402b4a:	45 89 e8             	mov    %r13d,%r8d
  402b4d:	ba 00 01 00 00       	mov    $0x100,%edx
  402b52:	31 c0                	xor    %eax,%eax
  402b54:	6a 00                	push   $0x0
  402b56:	48 8d 0d 2b 5e 00 00 	lea    0x5e2b(%rip),%rcx        # 408988 <_IO_stdin_used+0x988>
  402b5d:	be 01 00 00 00       	mov    $0x1,%esi
  402b62:	e8 79 f7 ff ff       	call   4022e0 <__sprintf_chk@plt>
          memset(message, '\0', 256);
          sprintf(message, "Sending message from thread %d task %d group %d", x, y, k);
          messaged->message = message;
          messaged->task_index = y;
          messaged->group = k;
          messaged->thread_index = thread_data[x].real_thread_index;
  402b67:	4c 8b 7c 24 70       	mov    0x70(%rsp),%r15
          messaged->message = message;
  402b6c:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
          thread_data[x].tasks[y].kind = BARRIER_TASK;
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402b71:	be 20 00 00 00       	mov    $0x20,%esi
          thread_data[x].tasks[y].swap = swap;
  402b76:	48 8b 6c 24 50       	mov    0x50(%rsp),%rbp
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402b7b:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->thread_index = thread_data[x].real_thread_index;
  402b80:	49 63 47 08          	movslq 0x8(%r15),%rax
          messaged->message = message;
  402b84:	49 89 1a             	mov    %rbx,(%r10)
          thread_data[x].tasks[y].swap = swap;
  402b87:	49 8b 5f 38          	mov    0x38(%r15),%rbx
          messaged->group = k;
  402b8b:	41 c7 42 18 00 00 00 00 	movl   $0x0,0x18(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
  402b93:	66 48 0f 6e c0       	movq   %rax,%xmm0
          thread_data[x].tasks[y].swap = swap;
  402b98:	8b 44 24 38          	mov    0x38(%rsp),%eax
  402b9c:	48 01 dd             	add    %rbx,%rbp
          messaged->thread_index = thread_data[x].real_thread_index;
  402b9f:	0f 16 44 24 68       	movhps 0x68(%rsp),%xmm0
  402ba4:	41 0f 11 42 08       	movups %xmm0,0x8(%r10)
          thread_data[x].tasks[y].swap = swap;
  402ba9:	89 85 a0 01 00 00    	mov    %eax,0x1a0(%rbp)
          swap += 1;
  402baf:	83 c0 01             	add    $0x1,%eax
  402bb2:	89 44 24 38          	mov    %eax,0x38(%rsp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402bb6:	41 8d 44 24 01       	lea    0x1(%r12),%eax
  402bbb:	89 44 24 18          	mov    %eax,0x18(%rsp)
  402bbf:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].message = messaged;
  402bc2:	4c 89 95 90 01 00 00 	mov    %r10,0x190(%rbp)
          thread_data[x].tasks[y].group = k;
  402bc9:	c7 85 9c 01 00 00 00 00 00 00 	movl   $0x0,0x19c(%rbp)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
  402bd3:	c7 45 00 41 00 00 00 	movl   $0x41,0x0(%rbp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
  402bda:	89 85 98 01 00 00    	mov    %eax,0x198(%rbp)
          thread_data[x].tasks[y].sending = 1;
  402be0:	c7 85 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rbp)
          thread_data[x].tasks[y].snapshot_count = 99;
  402bea:	48 c7 85 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402bf5:	e8 26 f5 ff ff       	call   402120 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
  402bfa:	48 c7 85 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
  402c05:	48 89 85 50 01 00 00 	mov    %rax,0x150(%rbp)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
  402c0c:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
  402c11:	48 8b 00             	mov    (%rax),%rax
  402c14:	8b 48 04             	mov    0x4(%rax),%ecx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
  402c17:	48 89 85 28 01 00 00 	mov    %rax,0x128(%rbp)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
  402c1e:	89 8d 30 01 00 00    	mov    %ecx,0x130(%rbp)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
  402c24:	41 59                	pop    %r9
  402c26:	41 5a                	pop    %r10
  402c28:	49 39 c7             	cmp    %rax,%r15
  402c2b:	0f 85 59 12 00 00    	jne    403e8a <main+0x1b4a>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
  402c31:	66 0f 6f 25 67 62 00 00 	movdqa 0x6267(%rip),%xmm4        # 408ea0 <_IO_stdin_used+0xea0>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
  402c39:	44 89 65 04          	mov    %r12d,0x4(%rbp)
          thread_data[x].tasks[y].available = 1;
  402c3d:	48 8b 05 7c 62 00 00 	mov    0x627c(%rip),%rax        # 408ec0 <_IO_stdin_used+0xec0>
          thread_data[x].tasks[y].arrived = 0;
  402c44:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
          thread_data[x].tasks[y].worker_count = thread_count;
  402c4e:	c7 85 8c 01 00 00 02 00 00 00 	movl   $0x2,0x18c(%rbp)
          thread_data[x].tasks[y].available = 1;
  402c58:	48 89 85 44 01 00 00 	mov    %rax,0x144(%rbp)
          thread_data[x].tasks[y].thread_count = 2;
  402c5f:	0f 11 a5 34 01 00 00 	movups %xmm4,0x134(%rbp)
          if (y == barrier_count - 1) {
  402c66:	41 83 fc 01          	cmp    $0x1,%r12d
  402c6a:	0f 84 32 11 00 00    	je     403da2 <main+0x1a62>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
  402c70:	45 85 e4             	test   %r12d,%r12d
  402c73:	0f 84 03 11 00 00    	je     403d7c <main+0x1a3c>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
  402c79:	48 c7 c0 d0 72 40 00 	mov    $0x4072d0,%rax
        for (int y = 0 ; y < total_barrier_count ; y++) {
  402c80:	83 7c 24 08 03       	cmpl   $0x3,0x8(%rsp)
               thread_data[x].tasks[y].run = barriered_work; 
  402c85:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
        for (int y = 0 ; y < total_barrier_count ; y++) {
  402c8c:	0f 85 e8 11 00 00    	jne    403e7a <main+0x1b3a>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
  402c92:	4c 8b 7c 24 60       	mov    0x60(%rsp),%r15
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
  402c97:	be 08 00 00 00       	mov    $0x8,%esi
  402c9c:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].buffers_count = buffers_per_thread;
  402ca1:	41 c7 87 cc 00 00 00 01 00 00 00 	movl   $0x1,0xcc(%r15)
    for (int d = 0 ; d < threads_per_group ; d++) {
  402cac:	49 81 c7 30 01 00 00 	add    $0x130,%r15
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
  402cb3:	e8 68 f4 ff ff       	call   402120 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
  402cb8:	4c 8b 74 24 68       	mov    0x68(%rsp),%r14
        }
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
  402cbd:	be 08 00 00 00       	mov    $0x8,%esi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
  402cc2:	48 8b 8c 24 d0 00 00 00 	mov    0xd0(%rsp),%rcx
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
  402cca:	49 89 87 20 ff ff ff 	mov    %rax,-0xe0(%r15)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
  402cd1:	4c 89 f7             	mov    %r14,%rdi
  402cd4:	48 c1 e7 04          	shl    $0x4,%rdi
  402cd8:	48 01 f9             	add    %rdi,%rcx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
  402cdb:	bf 02 00 00 00       	mov    $0x2,%edi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
  402ce0:	48 89 08             	mov    %rcx,(%rax)
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
  402ce3:	e8 38 f4 ff ff       	call   402120 <calloc@plt>
  402ce8:	4c 89 f1             	mov    %r14,%rcx
        for (int b = 0 ; b < io_threads; b++) {	
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
  402ceb:	66 0f 6f a4 24 80 00 00 00 	movdqa 0x80(%rsp),%xmm4
  402cf4:	48 c1 e1 05          	shl    $0x5,%rcx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
  402cf8:	49 89 87 28 ff ff ff 	mov    %rax,-0xd8(%r15)
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
  402cff:	48 8d 71 10          	lea    0x10(%rcx),%rsi
  402d03:	66 48 0f 6e c1       	movq   %rcx,%xmm0
  402d08:	66 48 0f 6e f6       	movq   %rsi,%xmm6
  402d0d:	66 0f 6c c6          	punpcklqdq %xmm6,%xmm0
  402d11:	66 0f d4 84 24 90 00 00 00 	paddq  0x90(%rsp),%xmm0
  402d1a:	0f 11 00             	movups %xmm0,(%rax)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
  402d1d:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
  402d22:	0f 11 a3 18 05 00 00 	movups %xmm4,0x518(%rbx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
  402d29:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
  402d2c:	c7 83 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rbx)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
  402d36:	c7 83 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rbx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
  402d40:	48 89 83 28 05 00 00 	mov    %rax,0x528(%rbx)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
  402d47:	c7 83 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rbx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
  402d51:	41 8b 87 d4 fe ff ff 	mov    -0x12c(%r15),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
  402d58:	c7 83 8c 05 00 00 02 00 00 00 	movl   $0x2,0x58c(%rbx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
  402d62:	89 83 30 05 00 00    	mov    %eax,0x530(%rbx)
        thread_data[x].tasks[barrier_count].available = 1; 
  402d68:	48 8b 05 51 61 00 00 	mov    0x6151(%rip),%rax        # 408ec0 <_IO_stdin_used+0xec0>
  402d6f:	48 89 83 44 05 00 00 	mov    %rax,0x544(%rbx)
    for (int d = 0 ; d < threads_per_group ; d++) {
  402d76:	49 83 fe 01          	cmp    $0x1,%r14
  402d7a:	0f 85 3b 10 00 00    	jne    403dbb <main+0x1a7b>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
  402d80:	be 08 00 00 00       	mov    $0x8,%esi
  402d85:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
  402d8a:	31 db                	xor    %ebx,%ebx
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
  402d8c:	e8 8f f3 ff ff       	call   402120 <calloc@plt>
  402d91:	48 89 c5             	mov    %rax,%rbp
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
  402d94:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
  402d99:	4c 8d 78 38          	lea    0x38(%rax),%r15
  402d9d:	48 05 98 02 00 00    	add    $0x298,%rax
  402da3:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
  402da8:	4d 89 f8             	mov    %r15,%r8
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402dab:	41 8b 40 08          	mov    0x8(%r8),%eax
  402daf:	85 c0                	test   %eax,%eax
  402db1:	7e 65                	jle    402e18 <main+0xad8>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402db3:	49 8b 08             	mov    (%r8),%rcx
  402db6:	83 e8 01             	sub    $0x1,%eax
  402db9:	49 89 c1             	mov    %rax,%r9
  402dbc:	48 c1 e0 09          	shl    $0x9,%rax
  402dc0:	48 8d 91 70 01 00 00 	lea    0x170(%rcx),%rdx
  402dc7:	48 8d bc 01 70 03 00 00 	lea    0x370(%rcx,%rax,1),%rdi
  402dcf:	89 d9                	mov    %ebx,%ecx
  402dd1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  402dd8:	48 8b 02             	mov    (%rdx),%rax
  402ddb:	48 63 f1             	movslq %ecx,%rsi
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402dde:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402de5:	83 c1 04             	add    $0x4,%ecx
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402de8:	48 8d 74 f5 00       	lea    0x0(%rbp,%rsi,8),%rsi
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  402ded:	f3 0f 7e 80 00 01 00 00 	movq   0x100(%rax),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  402df5:	f3 0f 7e 08          	movq   (%rax),%xmm1
  402df9:	0f 16 80 80 01 00 00 	movhps 0x180(%rax),%xmm0
  402e00:	0f 16 88 80 00 00 00 	movhps 0x80(%rax),%xmm1
  402e07:	0f 11 0e             	movups %xmm1,(%rsi)
  402e0a:	0f 11 46 10          	movups %xmm0,0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  402e0e:	48 39 d7             	cmp    %rdx,%rdi
  402e11:	75 c5                	jne    402dd8 <main+0xa98>
  402e13:	42 8d 5c 8b 04       	lea    0x4(%rbx,%r9,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
  402e18:	49 81 c0 30 01 00 00 	add    $0x130,%r8
  402e1f:	4c 39 44 24 20       	cmp    %r8,0x20(%rsp)
  402e24:	75 85                	jne    402dab <main+0xa6b>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  402e26:	48 8d 3d 08 56 00 00 	lea    0x5608(%rip),%rdi        # 408435 <_IO_stdin_used+0x435>
  402e2d:	e8 1e f2 ff ff       	call   402050 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
  402e32:	48 8d 35 11 56 00 00 	lea    0x5611(%rip),%rsi        # 40844a <_IO_stdin_used+0x44a>
  402e39:	48 8d 3d 0c 56 00 00 	lea    0x560c(%rip),%rdi        # 40844c <_IO_stdin_used+0x44c>
  402e40:	e8 db f3 ff ff       	call   402220 <fopen@plt>
  402e45:	49 89 c4             	mov    %rax,%r12
  for (int x = 0 ; x < datas_size; x++) {
  402e48:	85 db                	test   %ebx,%ebx
  402e4a:	0f 8e 86 00 00 00    	jle    402ed6 <main+0xb96>
  402e50:	8d 43 ff             	lea    -0x1(%rbx),%eax
  402e53:	49 89 ed             	mov    %rbp,%r13
  402e56:	48 8d 1d 26 56 00 00 	lea    0x5626(%rip),%rbx        # 408483 <_IO_stdin_used+0x483>
  402e5d:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
  402e62:	48 8d 44 c5 08       	lea    0x8(%rbp,%rax,8),%rax
  402e67:	4d 89 ef             	mov    %r13,%r15
  402e6a:	48 8d 2d 06 56 00 00 	lea    0x5606(%rip),%rbp        # 408477 <_IO_stdin_used+0x477>
  402e71:	49 89 dd             	mov    %rbx,%r13
  402e74:	48 89 c3             	mov    %rax,%rbx
    char * c = calloc(250, sizeof(char));
  402e77:	be 01 00 00 00       	mov    $0x1,%esi
  402e7c:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
  402e81:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
  402e85:	e8 96 f2 ff ff       	call   402120 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  402e8a:	48 89 e9             	mov    %rbp,%rcx
  402e8d:	ba fa 00 00 00       	mov    $0xfa,%edx
  402e92:	be 01 00 00 00       	mov    $0x1,%esi
  402e97:	49 89 c6             	mov    %rax,%r14
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
  402e9a:	49 8b 47 f8          	mov    -0x8(%r15),%rax
  402e9e:	4c 89 f7             	mov    %r14,%rdi
  402ea1:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
  402ea8:	31 c0                	xor    %eax,%eax
  402eaa:	e8 31 f4 ff ff       	call   4022e0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  402eaf:	4c 89 f2             	mov    %r14,%rdx
  402eb2:	4c 89 ee             	mov    %r13,%rsi
  402eb5:	bf 01 00 00 00       	mov    $0x1,%edi
  402eba:	31 c0                	xor    %eax,%eax
  402ebc:	e8 0f f3 ff ff       	call   4021d0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  402ec1:	4c 89 e6             	mov    %r12,%rsi
  402ec4:	4c 89 f7             	mov    %r14,%rdi
  402ec7:	e8 14 f2 ff ff       	call   4020e0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
  402ecc:	4c 39 fb             	cmp    %r15,%rbx
  402ecf:	75 a6                	jne    402e77 <main+0xb37>
  402ed1:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
  402ed6:	4c 89 e7             	mov    %r12,%rdi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  402ed9:	4d 89 fe             	mov    %r15,%r14
  402edc:	4c 8d 2d c0 55 00 00 	lea    0x55c0(%rip),%r13        # 4084a3 <_IO_stdin_used+0x4a3>
  402ee3:	e8 98 f1 ff ff       	call   402080 <fclose@plt>
  402ee8:	48 8d 3d 66 55 00 00 	lea    0x5566(%rip),%rdi        # 408455 <_IO_stdin_used+0x455>
  402eef:	e8 5c f1 ff ff       	call   402050 <puts@plt>
  402ef4:	31 d2                	xor    %edx,%edx
  402ef6:	48 8d 35 70 55 00 00 	lea    0x5570(%rip),%rsi        # 40846d <_IO_stdin_used+0x46d>
  402efd:	31 c0                	xor    %eax,%eax
  402eff:	bf 01 00 00 00       	mov    $0x1,%edi
  402f04:	e8 c7 f2 ff ff       	call   4021d0 <__printf_chk@plt>

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
  402f09:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  402f11:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
  402f16:	8b 54 24 10          	mov    0x10(%rsp),%edx
  402f1a:	48 8d 35 65 55 00 00 	lea    0x5565(%rip),%rsi        # 408486 <_IO_stdin_used+0x486>
  402f21:	31 c0                	xor    %eax,%eax
  402f23:	31 ed                	xor    %ebp,%ebp
  402f25:	bf 01 00 00 00       	mov    $0x1,%edi
  402f2a:	89 d1                	mov    %edx,%ecx
  402f2c:	e8 9f f2 ff ff       	call   4021d0 <__printf_chk@plt>
  402f31:	89 ea                	mov    %ebp,%edx
  402f33:	48 8d 35 5e 55 00 00 	lea    0x555e(%rip),%rsi        # 408498 <_IO_stdin_used+0x498>
  402f3a:	bf 01 00 00 00       	mov    $0x1,%edi
  402f3f:	31 c0                	xor    %eax,%eax
  402f41:	e8 8a f2 ff ff       	call   4021d0 <__printf_chk@plt>
      int x = (k * threads_per_group) + d;
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
  402f46:	49 89 ec             	mov    %rbp,%r12
  402f49:	31 db                	xor    %ebx,%ebx
  402f4b:	49 c1 e4 09          	shl    $0x9,%r12
          char * mailbox_kind = calloc(100, sizeof(char));
  402f4f:	be 01 00 00 00       	mov    $0x1,%esi
  402f54:	bf 64 00 00 00       	mov    $0x64,%edi
  402f59:	41 89 df             	mov    %ebx,%r15d
  402f5c:	e8 bf f1 ff ff       	call   402120 <calloc@plt>
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
  402f61:	49 8b 3e             	mov    (%r14),%rdi
  402f64:	48 89 de             	mov    %rbx,%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
  402f67:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
  402f6a:	48 c1 e6 08          	shl    $0x8,%rsi
  402f6e:	4a 8b 84 27 70 01 00 00 	mov    0x170(%rdi,%r12,1),%rax
  402f76:	48 01 f0             	add    %rsi,%rax
  402f79:	8b 90 b0 00 00 00    	mov    0xb0(%rax),%edx
  402f7f:	83 fa 02             	cmp    $0x2,%edx
  402f82:	0f 84 ae 0a 00 00    	je     403a36 <main+0x16f6>
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
  402f88:	83 fa 01             	cmp    $0x1,%edx
  402f8b:	0f 84 c6 0d 00 00    	je     403d57 <main+0x1a17>
  402f91:	44 8b 80 b4 00 00 00 	mov    0xb4(%rax),%r8d
  402f98:	44 89 fa             	mov    %r15d,%edx
  402f9b:	31 c0                	xor    %eax,%eax
  402f9d:	4c 89 ee             	mov    %r13,%rsi
  402fa0:	bf 01 00 00 00       	mov    $0x1,%edi
  402fa5:	e8 26 f2 ff ff       	call   4021d0 <__printf_chk@plt>
        for (int m = 0 ; m < mailboxes_needed ; m++) {
  402faa:	48 83 fb 01          	cmp    $0x1,%rbx
  402fae:	0f 85 6e 0a 00 00    	jne    403a22 <main+0x16e2>
      for (int y = 0 ; y < total_barrier_count ; y++) {
  402fb4:	48 83 c5 01          	add    $0x1,%rbp
  402fb8:	48 83 fd 03          	cmp    $0x3,%rbp
  402fbc:	0f 85 6f ff ff ff    	jne    402f31 <main+0xbf1>
    for (int d = 0 ; d < threads_per_group ; d++) {
  402fc2:	49 81 c6 30 01 00 00 	add    $0x130,%r14
  402fc9:	83 7c 24 10 01       	cmpl   $0x1,0x10(%rsp)
  402fce:	0f 85 74 0e 00 00    	jne    403e48 <main+0x1b08>
  402fd4:	ba 03 00 00 00       	mov    $0x3,%edx
  402fd9:	48 8d 35 de 54 00 00 	lea    0x54de(%rip),%rsi        # 4084be <_IO_stdin_used+0x4be>
  402fe0:	bf 01 00 00 00       	mov    $0x1,%edi
  402fe5:	31 c0                	xor    %eax,%eax
  402fe7:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
  402fec:	e8 df f1 ff ff       	call   4021d0 <__printf_chk@plt>
  

  printf("io index = %d\n", io_index);
  int io_mode = 0;
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  402ff1:	be 08 00 00 00       	mov    $0x8,%esi
  402ff6:	bf 02 00 00 00       	mov    $0x2,%edi
  402ffb:	e8 20 f1 ff ff       	call   402120 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
  403000:	4c 8b 74 24 48       	mov    0x48(%rsp),%r14
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  403005:	be 08 00 00 00       	mov    $0x8,%esi
    my_thread_data[0] = &thread_data[x]; 
  40300a:	49 8d be 90 03 00 00 	lea    0x390(%r14),%rdi
  403011:	66 49 0f 6e ee       	movq   %r14,%xmm5
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 

    io_mode = (io_mode + 1) % 2;
    thread_data[x].threads = my_thread_data;
  403016:	49 89 86 a8 03 00 00 	mov    %rax,0x3a8(%r14)
    my_thread_data[0] = &thread_data[x]; 
  40301d:	4d 8d ae c0 04 00 00 	lea    0x4c0(%r14),%r13
    thread_data[x].thread_count = 2;
  403024:	41 c7 86 b8 03 00 00 02 00 00 00 	movl   $0x2,0x3b8(%r14)
    my_thread_data[0] = &thread_data[x]; 
  40302f:	66 48 0f 6e c7       	movq   %rdi,%xmm0
    thread_data[x].thread_index = 0;
  403034:	41 c7 86 94 03 00 00 00 00 00 00 	movl   $0x0,0x394(%r14)
    my_thread_data[0] = &thread_data[x]; 
  40303f:	66 0f 6c c5          	punpcklqdq %xmm5,%xmm0
    thread_data[x].task_count = total_barrier_count;
  403043:	41 c7 86 d0 03 00 00 03 00 00 00 	movl   $0x3,0x3d0(%r14)
    my_thread_data[0] = &thread_data[x]; 
  40304e:	0f 11 00             	movups %xmm0,(%rax)
  403051:	48 89 7c 24 50       	mov    %rdi,0x50(%rsp)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
  403056:	bf 02 00 00 00       	mov    $0x2,%edi
  40305b:	e8 c0 f0 ff ff       	call   402120 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
  403060:	66 49 0f 6e ee       	movq   %r14,%xmm5
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403065:	be 38 00 00 00       	mov    $0x38,%esi
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
  40306a:	49 8d be 30 01 00 00 	lea    0x130(%r14),%rdi
    thread_data[x].threads = my_thread_data;
  403071:	49 89 86 d8 04 00 00 	mov    %rax,0x4d8(%r14)
  403078:	66 48 0f 6e ff       	movq   %rdi,%xmm7
    my_thread_data[0] = &thread_data[x]; 
  40307d:	4c 89 28             	mov    %r13,(%rax)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
  403080:	66 0f 6c ef          	punpcklqdq %xmm7,%xmm5
  403084:	48 89 78 08          	mov    %rdi,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
  403088:	49 8b 46 38          	mov    0x38(%r14),%rax
    thread_data[x].thread_count = 2;
  40308c:	41 c7 86 e8 04 00 00 02 00 00 00 	movl   $0x2,0x4e8(%r14)
    thread_data[x].thread_index = 0;
  403097:	41 c7 86 c4 04 00 00 00 00 00 00 	movl   $0x0,0x4c4(%r14)
    thread_data[x].task_count = total_barrier_count;
  4030a2:	41 c7 86 00 05 00 00 03 00 00 00 	movl   $0x3,0x500(%r14)
    thread_data[n].tasks[0].scheduled = 1;
  4030ad:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  4030b7:	49 8b 86 68 01 00 00 	mov    0x168(%r14),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
  4030be:	48 89 7c 24 60       	mov    %rdi,0x60(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  4030c3:	bf 07 00 00 00       	mov    $0x7,%edi
    thread_data[n].tasks[0].scheduled = 1;
  4030c8:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  4030d2:	0f 29 6c 24 30       	movaps %xmm5,0x30(%rsp)
  4030d7:	e8 44 f0 ff ff       	call   402120 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  4030dc:	be 38 00 00 00       	mov    $0x38,%esi
  4030e1:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  4030e6:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  4030e9:	e8 32 f0 ff ff       	call   402120 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  4030ee:	be 38 00 00 00       	mov    $0x38,%esi
  4030f3:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  4030f8:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  4030fb:	e8 20 f0 ff ff       	call   402120 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  403100:	be 38 00 00 00       	mov    $0x38,%esi
  403105:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40310a:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40310f:	e8 0c f0 ff ff       	call   402120 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  403114:	be 08 00 00 00       	mov    $0x8,%esi
  403119:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  40311e:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  403123:	e8 f8 ef ff ff       	call   402120 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
  403128:	be 08 00 00 00       	mov    $0x8,%esi
  40312d:	bf 07 00 00 00       	mov    $0x7,%edi
  thread_data[timer_threadi].type = TIMER;
  403132:	41 c7 86 6c 02 00 00 00 00 00 00 	movl   $0x0,0x26c(%r14)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  40313d:	48 89 c5             	mov    %rax,%rbp
  thread_data[timer_threadi].task_count = total_barrier_count;
  403140:	48 8b 05 81 5d 00 00 	mov    0x5d81(%rip),%rax        # 408ec8 <_IO_stdin_used+0xec8>
  403147:	49 89 86 a0 02 00 00 	mov    %rax,0x2a0(%r14)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
  40314e:	e8 cd ef ff ff       	call   402120 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
  403153:	4c 89 f7             	mov    %r14,%rdi
  403156:	4d 8d b6 60 02 00 00 	lea    0x260(%r14),%r14
  40315d:	66 0f 6f 6c 24 30    	movdqa 0x30(%rsp),%xmm5
  403163:	48 8d 97 f0 05 00 00 	lea    0x5f0(%rdi),%rdx
  40316a:	66 49 0f 6e c6       	movq   %r14,%xmm0
  }
  thread_data[timer_threadi].threads = my_thread_data;
  40316f:	48 89 87 78 02 00 00 	mov    %rax,0x278(%rdi)
  403176:	48 8d 35 50 53 00 00 	lea    0x5350(%rip),%rsi        # 4084cd <_IO_stdin_used+0x4cd>
    my_thread_data[n] = &thread_data[n]; 
  40317d:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
  403182:	0f 16 44 24 50       	movhps 0x50(%rsp),%xmm0
  403187:	48 8d 97 20 07 00 00 	lea    0x720(%rdi),%rdx
  40318e:	0f 11 40 10          	movups %xmm0,0x10(%rax)
  403192:	66 49 0f 6e c5       	movq   %r13,%xmm0
  thread_data[timer_threadi].threads = my_thread_data;
  403197:	49 89 fd             	mov    %rdi,%r13
    my_thread_data[n] = &thread_data[n]; 
  40319a:	0f 11 28             	movups %xmm5,(%rax)
  40319d:	0f 16 44 24 40       	movhps 0x40(%rsp),%xmm0
  4031a2:	48 89 50 30          	mov    %rdx,0x30(%rax)
  4031a6:	ba 02 00 00 00       	mov    $0x2,%edx
  4031ab:	0f 11 40 20          	movups %xmm0,0x20(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
  4031af:	48 8b 05 1a 5d 00 00 	mov    0x5d1a(%rip),%rax        # 408ed0 <_IO_stdin_used+0xed0>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
  4031b6:	c7 87 90 02 00 00 02 00 00 00 	movl   $0x2,0x290(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
  4031c0:	48 89 87 88 02 00 00 	mov    %rax,0x288(%rdi)
  4031c7:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
  4031c9:	c7 87 64 02 00 00 00 00 00 00 	movl   $0x0,0x264(%rdi)
  4031d3:	bf 01 00 00 00       	mov    $0x1,%edi
  4031d8:	e8 f3 ef ff ff       	call   4021d0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
  4031dd:	48 c7 c2 80 41 40 00 	mov    $0x404180,%rdx
  4031e4:	4c 89 f1             	mov    %r14,%rcx
  4031e7:	48 8d 7d 10          	lea    0x10(%rbp),%rdi
  4031eb:	49 8d 74 24 70       	lea    0x70(%r12),%rsi
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
  4031f0:	4d 89 ee             	mov    %r13,%r14
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
  4031f3:	e8 f8 ef ff ff       	call   4021f0 <pthread_create@plt>
  4031f8:	31 c9                	xor    %ecx,%ecx
  4031fa:	31 d2                	xor    %edx,%edx
  4031fc:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].type = WORKER;
  403201:	41 c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%r13)
  403209:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
  40320b:	41 c7 45 44 01 00 00 00 	movl   $0x1,0x44(%r13)
  403213:	4c 8d 2d 9e 57 00 00 	lea    0x579e(%rip),%r13        # 4089b8 <_IO_stdin_used+0x9b8>
  40321a:	4c 89 ee             	mov    %r13,%rsi
  40321d:	e8 ae ef ff ff       	call   4021d0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
  403222:	4c 89 f1             	mov    %r14,%rcx
  403225:	48 89 de             	mov    %rbx,%rsi
  403228:	48 89 ef             	mov    %rbp,%rdi
  40322b:	49 c7 c4 20 69 40 00 	mov    $0x406920,%r12
  403232:	4c 89 e2             	mov    %r12,%rdx
  403235:	e8 b6 ef ff ff       	call   4021f0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
  40323a:	49 8b 96 c0 00 00 00 	mov    0xc0(%r14),%rdx
  403241:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
  403245:	be 08 00 00 00       	mov    $0x8,%esi
  40324a:	e8 f1 ed ff ff       	call   402040 <pthread_setaffinity_np@plt>
  40324f:	4c 89 ee             	mov    %r13,%rsi
  403252:	31 c9                	xor    %ecx,%ecx
  403254:	ba 01 00 00 00       	mov    $0x1,%edx
      thread_data[x].type = WORKER;
  403259:	41 c7 86 3c 01 00 00 01 00 00 00 	movl   $0x1,0x13c(%r14)
  403264:	bf 01 00 00 00       	mov    $0x1,%edi
  403269:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
  40326b:	41 c7 86 74 01 00 00 01 00 00 00 	movl   $0x1,0x174(%r14)
  403276:	e8 55 ef ff ff       	call   4021d0 <__printf_chk@plt>
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
  40327b:	48 8d 73 38          	lea    0x38(%rbx),%rsi
  40327f:	4c 89 e2             	mov    %r12,%rdx
  403282:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
  403286:	48 8b 4c 24 60       	mov    0x60(%rsp),%rcx
  40328b:	e8 60 ef ff ff       	call   4021f0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
  403290:	49 8b 96 f0 01 00 00 	mov    0x1f0(%r14),%rdx
  403297:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
  40329b:	be 08 00 00 00       	mov    $0x8,%esi
  4032a0:	e8 9b ed ff ff       	call   402040 <pthread_setaffinity_np@plt>
    }
  }
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
  4032a5:	be 08 00 00 00       	mov    $0x8,%esi
  4032aa:	bf 02 00 00 00       	mov    $0x2,%edi
  4032af:	e8 6c ee ff ff       	call   402120 <calloc@plt>

  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
  4032b4:	be d8 00 00 00       	mov    $0xd8,%esi
  4032b9:	bf 01 00 00 00       	mov    $0x1,%edi
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
  4032be:	48 89 c3             	mov    %rax,%rbx
  4032c1:	48 89 84 24 80 00 00 00 	mov    %rax,0x80(%rsp)
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
  4032c9:	e8 52 ee ff ff       	call   402120 <calloc@plt>
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
  4032ce:	be d8 00 00 00       	mov    $0xd8,%esi
  4032d3:	bf 01 00 00 00       	mov    $0x1,%edi
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
  4032d8:	48 89 03             	mov    %rax,(%rbx)
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
  4032db:	e8 40 ee ff ff       	call   402120 <calloc@plt>

  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
  4032e0:	be 10 00 00 00       	mov    $0x10,%esi
  4032e5:	bf 02 00 00 00       	mov    $0x2,%edi
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
  4032ea:	48 89 43 08          	mov    %rax,0x8(%rbx)
  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
  4032ee:	e8 2d ee ff ff       	call   402120 <calloc@plt>
  4032f3:	49 89 c5             	mov    %rax,%r13
  long iomailboxes_size = 10000;
  for (int x = 0 ; x < io_threads; x++) {
  4032f6:	49 89 c4             	mov    %rax,%r12
  4032f9:	48 8d 40 20          	lea    0x20(%rax),%rax
  4032fd:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    iomailboxes[x].count = iomailboxes_size;
  403302:	41 c7 04 24 10 27 00 00 	movl   $0x2710,(%r12)
    iomailboxes[x].buffer = calloc(iomailboxes_size, sizeof(struct Buffer));
  40330a:	be 28 00 00 00       	mov    $0x28,%esi
  40330f:	bf 10 27 00 00       	mov    $0x2710,%edi
  403314:	e8 07 ee ff ff       	call   402120 <calloc@plt>
  403319:	49 89 44 24 08       	mov    %rax,0x8(%r12)
  40331e:	49 89 c6             	mov    %rax,%r14
    for (int y = 0 ; y < iomailboxes_size; y++) {
  403321:	48 8d 58 08          	lea    0x8(%rax),%rbx
  403325:	49 81 c6 88 1a 06 00 	add    $0x61a88,%r14
  40332c:	0f 1f 40 00          	nopl   0x0(%rax)
      iomailboxes[x].buffer[y].available = 0;
  403330:	c7 03 00 00 00 00    	movl   $0x0,(%rbx)
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  403336:	be 20 00 00 00       	mov    $0x20,%esi
  40333b:	bf 64 00 00 00       	mov    $0x64,%edi
    for (int y = 0 ; y < iomailboxes_size; y++) {
  403340:	48 83 c3 28          	add    $0x28,%rbx
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
  403344:	c7 43 e8 64 00 00 00 	movl   $0x64,-0x18(%rbx)
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
  40334b:	e8 d0 ed ff ff       	call   402120 <calloc@plt>
  403350:	48 89 43 e0          	mov    %rax,-0x20(%rbx)
    for (int y = 0 ; y < iomailboxes_size; y++) {
  403354:	49 39 de             	cmp    %rbx,%r14
  403357:	75 d7                	jne    403330 <main+0xff0>
  for (int x = 0 ; x < io_threads; x++) {
  403359:	49 83 c4 10          	add    $0x10,%r12
  40335d:	4c 39 64 24 10       	cmp    %r12,0x10(%rsp)
  403362:	75 9e                	jne    403302 <main+0xfc2>
  char * recv_identity = "recv-thread";
  char * unknown_identity = "unknown-thread";
  int counter = 0;

  int dataeventfds[2];
  dataeventfds[0] = eventfd(0, EFD_NONBLOCK);
  403364:	be 00 08 00 00       	mov    $0x800,%esi
  403369:	31 ff                	xor    %edi,%edi
  40336b:	48 8d 5d 18          	lea    0x18(%rbp),%rbx
  40336f:	e8 dc ee ff ff       	call   402250 <eventfd@plt>
  dataeventfds[1] = eventfd(0, EFD_NONBLOCK);
  403374:	be 00 08 00 00       	mov    $0x800,%esi
  403379:	31 ff                	xor    %edi,%edi
  40337b:	4c 8d 25 75 51 00 00 	lea    0x5175(%rip),%r12        # 4084f7 <_IO_stdin_used+0x4f7>
  dataeventfds[0] = eventfd(0, EFD_NONBLOCK);
  403382:	89 44 24 10          	mov    %eax,0x10(%rsp)
  dataeventfds[1] = eventfd(0, EFD_NONBLOCK);
  403386:	e8 c5 ee ff ff       	call   402250 <eventfd@plt>
  40338b:	4c 8b 74 24 50       	mov    0x50(%rsp),%r14
  403390:	48 89 6c 24 50       	mov    %rbp,0x50(%rsp)
  403395:	48 89 dd             	mov    %rbx,%rbp
  403398:	89 44 24 28          	mov    %eax,0x28(%rsp)

  for (int x = io_index ; x < io_index + io_threads ; x++) {
  40339c:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  4033a1:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
  4033a5:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
  4033aa:	48 05 a8 00 00 00    	add    $0xa8,%rax
  4033b0:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
  4033b5:	48 8b 05 1c 5b 00 00 	mov    0x5b1c(%rip),%rax        # 408ed8 <_IO_stdin_used+0xed8>
    int myring = x % 2;
  4033bc:	89 d9                	mov    %ebx,%ecx
    thread_data[x].io_mode = myring;
    thread_data[x].my_io = myring;
    thread_data[x].other_io = otherring;
    thread_data[x].iomailboxes = iomailboxes; 
    printf("%d myring %d other is %d\n", x, myring, otherring);
    thread_data[x].ring = rings[myring]; 
  4033be:	48 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%rdi
    thread_data[x].type = IO;
  4033c6:	41 c7 46 0c 02 00 00 00 	movl   $0x2,0xc(%r14)
    int myring = x % 2;
  4033ce:	83 e1 01             	and    $0x1,%ecx
    thread_data[x].task_count = 0;
  4033d1:	49 89 46 40          	mov    %rax,0x40(%r14)
    int otherring = (myring + 1) % 2;
  4033d5:	41 89 c8             	mov    %ecx,%r8d
    thread_data[x].ring = rings[myring]; 
  4033d8:	48 63 c1             	movslq %ecx,%rax
    int otherring = (myring + 1) % 2;
  4033db:	41 83 f0 01          	xor    $0x1,%r8d
    thread_data[x].ring = rings[myring]; 
  4033df:	4c 8d 3c c7          	lea    (%rdi,%rax,8),%r15
    if (myring == IO_MODE_SEND) {
  4033e3:	83 fb 03             	cmp    $0x3,%ebx
  4033e6:	0f 84 f1 09 00 00    	je     403ddd <main+0x1a9d>
      thread_data[x].identity = send_identity; 
  4033ec:	48 8d 05 f8 50 00 00 	lea    0x50f8(%rip),%rax        # 4084eb <_IO_stdin_used+0x4eb>
    thread_data[x].io_mode = myring;
  4033f3:	41 89 8e 0c 01 00 00 	mov    %ecx,0x10c(%r14)
  4033fa:	89 da                	mov    %ebx,%edx
  4033fc:	4c 89 e6             	mov    %r12,%rsi
    thread_data[x].my_io = myring;
  4033ff:	41 89 8e 1c 01 00 00 	mov    %ecx,0x11c(%r14)
  403406:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].identity = send_identity; 
  40340b:	49 89 86 20 01 00 00 	mov    %rax,0x120(%r14)
  403412:	31 c0                	xor    %eax,%eax
    thread_data[x].other_io = otherring;
  403414:	45 89 86 18 01 00 00 	mov    %r8d,0x118(%r14)
    thread_data[x].iomailboxes = iomailboxes; 
  40341b:	4d 89 ae 10 01 00 00 	mov    %r13,0x110(%r14)
  403422:	e8 a9 ed ff ff       	call   4021d0 <__printf_chk@plt>
    thread_data[x].ring = rings[myring]; 
  403427:	49 8b 07             	mov    (%r15),%rax
    int myeventfd = eventfd(0, EFD_NONBLOCK);
  40342a:	be 00 08 00 00       	mov    $0x800,%esi
  40342f:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = rings[myring]; 
  403431:	49 89 46 60          	mov    %rax,0x60(%r14)
    int myeventfd = eventfd(0, EFD_NONBLOCK);
  403435:	e8 16 ee ff ff       	call   402250 <eventfd@plt>
    thread_data[x]._eventfd = myeventfd; 
    int otherdataeventfd = 0;
    int datafd = 0;
    if (x % 2 == 0) {
      otherdataeventfd = dataeventfds[0];
      datafd = dataeventfds[1];
  40343a:	8b 54 24 28          	mov    0x28(%rsp),%edx
      otherdataeventfd = dataeventfds[0];
  40343e:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
    thread_data[x]._eventfd = myeventfd; 
  403442:	41 89 46 68          	mov    %eax,0x68(%r14)
  403446:	48 8d 35 9b 55 00 00 	lea    0x559b(%rip),%rsi        # 4089e8 <_IO_stdin_used+0x9e8>
  40344d:	bf 01 00 00 00       	mov    $0x1,%edi
  403452:	31 c0                	xor    %eax,%eax
  403454:	89 8c 24 a0 00 00 00 	mov    %ecx,0xa0(%rsp)
  40345b:	89 94 24 90 00 00 00 	mov    %edx,0x90(%rsp)
  403462:	e8 69 ed ff ff       	call   4021d0 <__printf_chk@plt>
      datafd = dataeventfds[0];
    }
    printf("my data event fd is %d other is %d\n", datafd, otherdataeventfd);
    thread_data[x].dataeventfd = datafd; 
    thread_data[x].otherdataeventfd = otherdataeventfd; 
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  403467:	be 08 00 00 00       	mov    $0x8,%esi
  40346c:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x].dataeventfd = datafd; 
  403471:	8b 8c 24 a0 00 00 00 	mov    0xa0(%rsp),%ecx
  403478:	8b 94 24 90 00 00 00 	mov    0x90(%rsp),%edx
  40347f:	66 0f 6e e9          	movd   %ecx,%xmm5
  403483:	66 0f 6e c2          	movd   %edx,%xmm0
  403487:	66 0f 62 c5          	punpckldq %xmm5,%xmm0
  40348b:	66 41 0f d6 46 6c    	movq   %xmm0,0x6c(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  403491:	e8 8a ec ff ff       	call   402120 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].thread_index = x;
  403496:	41 89 5e 04          	mov    %ebx,0x4(%r14)
  40349a:	89 da                	mov    %ebx,%edx
  40349c:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].threads = my_thread_data;
  4034a1:	49 89 46 18          	mov    %rax,0x18(%r14)
      my_thread_data[n] = &thread_data[n]; 
  4034a5:	66 0f 6f 54 24 30    	movdqa 0x30(%rsp),%xmm2
  4034ab:	48 8d 35 5f 50 00 00 	lea    0x505f(%rip),%rsi        # 408511 <_IO_stdin_used+0x511>
    thread_data[x].thread_count = thread_count;
  4034b2:	41 c7 46 28 02 00 00 00 	movl   $0x2,0x28(%r14)
      my_thread_data[n] = &thread_data[n]; 
  4034ba:	0f 11 10             	movups %xmm2,(%rax)
  4034bd:	31 c0                	xor    %eax,%eax
  4034bf:	e8 0c ed ff ff       	call   4021d0 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  4034c4:	4c 8b 7c 24 58       	mov    0x58(%rsp),%r15
  4034c9:	4c 89 f1             	mov    %r14,%rcx
  4034cc:	48 89 ef             	mov    %rbp,%rdi
  4034cf:	48 c7 c2 a0 56 40 00 	mov    $0x4056a0,%rdx
  for (int x = io_index ; x < io_index + io_threads ; x++) {
  4034d6:	48 83 c5 08          	add    $0x8,%rbp
  4034da:	49 81 c6 30 01 00 00 	add    $0x130,%r14
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  4034e1:	4c 89 fe             	mov    %r15,%rsi
  4034e4:	e8 07 ed ff ff       	call   4021f0 <pthread_create@plt>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
  4034e9:	4c 89 f8             	mov    %r15,%rax
  4034ec:	48 83 c0 38          	add    $0x38,%rax
  4034f0:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  4034f5:	83 fb 04             	cmp    $0x4,%ebx
  4034f8:	0f 85 d5 08 00 00    	jne    403dd3 <main+0x1a93>
  4034fe:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
  403503:	ba 05 00 00 00       	mov    $0x5,%edx
  403508:	48 8d 35 19 50 00 00 	lea    0x5019(%rip),%rsi        # 408528 <_IO_stdin_used+0x528>
  40350f:	31 c0                	xor    %eax,%eax
  403511:	bf 01 00 00 00       	mov    $0x1,%edi
  403516:	48 8b 6c 24 50       	mov    0x50(%rsp),%rbp
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  40351b:	bb 05 00 00 00       	mov    $0x5,%ebx
  403520:	e8 ab ec ff ff       	call   4021d0 <__printf_chk@plt>
  403525:	4c 8b 64 24 68       	mov    0x68(%rsp),%r12
  40352a:	4c 89 f8             	mov    %r15,%rax
  40352d:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
  403532:	4c 8d 6d 28          	lea    0x28(%rbp),%r13
  403536:	49 89 ef             	mov    %rbp,%r15
  403539:	4c 8d 05 fe 4f 00 00 	lea    0x4ffe(%rip),%r8        # 40853e <_IO_stdin_used+0x53e>
  403540:	48 89 c5             	mov    %rax,%rbp
  403543:	49 81 c4 18 01 00 00 	add    $0x118,%r12
  40354a:	4c 89 c6             	mov    %r8,%rsi
  40354d:	89 da                	mov    %ebx,%edx
  40354f:	bf 01 00 00 00       	mov    $0x1,%edi
  403554:	31 c0                	xor    %eax,%eax
  403556:	e8 75 ec ff ff       	call   4021d0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
  40355b:	be 08 00 00 00       	mov    $0x8,%esi
  403560:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
  403565:	48 8b 05 6c 59 00 00 	mov    0x596c(%rip),%rax        # 408ed8 <_IO_stdin_used+0xed8>
    thread_data[x].type = EXTERNAL;
  40356c:	41 c7 46 0c 03 00 00 00 	movl   $0x3,0xc(%r14)
    thread_data[x].task_count = 0;
  403574:	49 89 46 40          	mov    %rax,0x40(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
  403578:	e8 a3 eb ff ff       	call   402120 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
  40357d:	48 8b 7c 24 78       	mov    0x78(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  403582:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
  403587:	41 c7 86 cc 00 00 00 01 00 00 00 	movl   $0x1,0xcc(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
  403592:	49 89 46 50          	mov    %rax,0x50(%r14)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
  403596:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
  403599:	bf 02 00 00 00       	mov    $0x2,%edi
  40359e:	e8 7d eb ff ff       	call   402120 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
  4035a3:	48 8b 74 24 60       	mov    0x60(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  4035a8:	4c 89 f1             	mov    %r14,%rcx
  4035ab:	4c 89 ef             	mov    %r13,%rdi
      my_thread_data[n] = &thread_data[n]; 
  4035ae:	48 8b 54 24 48       	mov    0x48(%rsp),%rdx
    thread_data[x].threads = my_thread_data;
  4035b3:	49 89 46 18          	mov    %rax,0x18(%r14)
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  4035b7:	49 83 c5 08          	add    $0x8,%r13
  4035bb:	49 81 c6 30 01 00 00 	add    $0x130,%r14
      my_thread_data[n] = &thread_data[n]; 
  4035c2:	48 89 70 08          	mov    %rsi,0x8(%rax)
    thread_data[x].thread_count = thread_count;
  4035c6:	48 8b 35 03 59 00 00 	mov    0x5903(%rip),%rsi        # 408ed0 <_IO_stdin_used+0xed0>
    thread_data[x].thread_index = x;
  4035cd:	41 89 9e d4 fe ff ff 	mov    %ebx,-0x12c(%r14)
    thread_data[x].thread_count = thread_count;
  4035d4:	49 89 b6 f8 fe ff ff 	mov    %rsi,-0x108(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  4035db:	4c 89 e6             	mov    %r12,%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  4035de:	49 83 c4 38          	add    $0x38,%r12
      my_thread_data[n] = &thread_data[n]; 
  4035e2:	48 89 10             	mov    %rdx,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  4035e5:	48 c7 c2 80 40 40 00 	mov    $0x404080,%rdx
  4035ec:	e8 ff eb ff ff       	call   4021f0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
  4035f1:	48 83 44 24 78 10    	addq   $0x10,0x78(%rsp)
  4035f7:	83 fb 06             	cmp    $0x6,%ebx
  4035fa:	4c 8d 05 3d 4f 00 00 	lea    0x4f3d(%rip),%r8        # 40853e <_IO_stdin_used+0x53e>
  403601:	0f 85 c2 07 00 00    	jne    403dc9 <main+0x1a89>
  403607:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
  40360c:	48 89 ef             	mov    %rbp,%rdi
  40360f:	48 8d 1d 45 4f 00 00 	lea    0x4f45(%rip),%rbx        # 40855b <_IO_stdin_used+0x55b>
  403616:	4c 89 fd             	mov    %r15,%rbp
  403619:	49 89 ff             	mov    %rdi,%r15
  40361c:	4c 8d 68 04          	lea    0x4(%rax),%r13
  403620:	4c 8d a0 54 08 00 00 	lea    0x854(%rax),%r12
  403627:	41 8b 4d 04          	mov    0x4(%r13),%ecx
  40362b:	41 8b 55 00          	mov    0x0(%r13),%edx
  40362f:	48 89 de             	mov    %rbx,%rsi
  403632:	bf 01 00 00 00       	mov    $0x1,%edi
  403637:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
  403639:	49 81 c5 30 01 00 00 	add    $0x130,%r13
  403640:	e8 8b eb ff ff       	call   4021d0 <__printf_chk@plt>
  403645:	4d 39 ec             	cmp    %r13,%r12
  403648:	75 dd                	jne    403627 <main+0x12e7>
  40364a:	48 8d 3d 1d 4f 00 00 	lea    0x4f1d(%rip),%rdi        # 40856e <_IO_stdin_used+0x56e>
  403651:	45 31 ed             	xor    %r13d,%r13d
  403654:	4c 8d a4 24 e0 00 00 00 	lea    0xe0(%rsp),%r12
  40365c:	e8 ef e9 ff ff       	call   402050 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
  403661:	48 8d 1d 24 4f 00 00 	lea    0x4f24(%rip),%rbx        # 40858c <_IO_stdin_used+0x58c>
    void * result; 
    pthread_join(thread[x], &result);
  403668:	4a 8b 7c ed 00       	mov    0x0(%rbp,%r13,8),%rdi
  40366d:	4c 89 e6             	mov    %r12,%rsi
  403670:	e8 1b ec ff ff       	call   402290 <pthread_join@plt>
  403675:	44 89 ea             	mov    %r13d,%edx
  403678:	48 89 de             	mov    %rbx,%rsi
  40367b:	bf 01 00 00 00       	mov    $0x1,%edi
  403680:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
  403682:	49 83 c5 01          	add    $0x1,%r13
  403686:	e8 45 eb ff ff       	call   4021d0 <__printf_chk@plt>
  40368b:	49 83 fd 07          	cmp    $0x7,%r13
  40368f:	75 d7                	jne    403668 <main+0x1328>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
  403691:	be 08 00 00 00       	mov    $0x8,%esi
  403696:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
  40369b:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
  40369d:	e8 7e ea ff ff       	call   402120 <calloc@plt>
  4036a2:	4d 89 f8             	mov    %r15,%r8
  4036a5:	49 89 c6             	mov    %rax,%r14
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  4036a8:	41 8b 40 08          	mov    0x8(%r8),%eax
  4036ac:	85 c0                	test   %eax,%eax
  4036ae:	7e 5f                	jle    40370f <main+0x13cf>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  4036b0:	49 8b 08             	mov    (%r8),%rcx
  4036b3:	83 e8 01             	sub    $0x1,%eax
  4036b6:	49 89 c1             	mov    %rax,%r9
  4036b9:	48 c1 e0 09          	shl    $0x9,%rax
  4036bd:	48 8d 91 70 01 00 00 	lea    0x170(%rcx),%rdx
  4036c4:	48 8d bc 01 70 03 00 00 	lea    0x370(%rcx,%rax,1),%rdi
  4036cc:	89 d9                	mov    %ebx,%ecx
  4036ce:	66 90                	xchg   %ax,%ax
  4036d0:	48 8b 02             	mov    (%rdx),%rax
  4036d3:	48 63 f1             	movslq %ecx,%rsi
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  4036d6:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  4036dd:	83 c1 04             	add    $0x4,%ecx
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  4036e0:	49 8d 34 f6          	lea    (%r14,%rsi,8),%rsi
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
  4036e4:	f3 0f 7e 80 00 01 00 00 	movq   0x100(%rax),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
  4036ec:	f3 0f 7e 08          	movq   (%rax),%xmm1
  4036f0:	0f 16 80 80 01 00 00 	movhps 0x180(%rax),%xmm0
  4036f7:	0f 16 88 80 00 00 00 	movhps 0x80(%rax),%xmm1
  4036fe:	0f 11 0e             	movups %xmm1,(%rsi)
  403701:	0f 11 46 10          	movups %xmm0,0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  403705:	48 39 fa             	cmp    %rdi,%rdx
  403708:	75 c6                	jne    4036d0 <main+0x1390>
  40370a:	42 8d 5c 8b 04       	lea    0x4(%rbx,%r9,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
  40370f:	49 81 c0 30 01 00 00 	add    $0x130,%r8
  403716:	4c 39 44 24 20       	cmp    %r8,0x20(%rsp)
  40371b:	75 8b                	jne    4036a8 <main+0x1368>
  40371d:	48 8d 3d 7c 4e 00 00 	lea    0x4e7c(%rip),%rdi        # 4085a0 <_IO_stdin_used+0x5a0>
  403724:	e8 27 e9 ff ff       	call   402050 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
  403729:	48 8d 35 1a 4d 00 00 	lea    0x4d1a(%rip),%rsi        # 40844a <_IO_stdin_used+0x44a>
  403730:	48 8d 3d 81 4e 00 00 	lea    0x4e81(%rip),%rdi        # 4085b8 <_IO_stdin_used+0x5b8>
  403737:	e8 e4 ea ff ff       	call   402220 <fopen@plt>
  40373c:	49 89 c4             	mov    %rax,%r12
  for (int x = 0 ; x < datas2_size; x++) {
  40373f:	85 db                	test   %ebx,%ebx
  403741:	0f 8e 83 00 00 00    	jle    4037ca <main+0x148a>
  403747:	8d 43 ff             	lea    -0x1(%rbx),%eax
  40374a:	48 8d 1d 32 4d 00 00 	lea    0x4d32(%rip),%rbx        # 408483 <_IO_stdin_used+0x483>
  403751:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
  403756:	4d 89 f7             	mov    %r14,%r15
  403759:	49 8d 44 c6 08       	lea    0x8(%r14,%rax,8),%rax
  40375e:	48 8d 2d 12 4d 00 00 	lea    0x4d12(%rip),%rbp        # 408477 <_IO_stdin_used+0x477>
  403765:	49 89 de             	mov    %rbx,%r14
  403768:	48 89 c3             	mov    %rax,%rbx
    char * c = calloc(250, sizeof(char));
  40376b:	be 01 00 00 00       	mov    $0x1,%esi
  403770:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
  403775:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
  403779:	e8 a2 e9 ff ff       	call   402120 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  40377e:	48 89 e9             	mov    %rbp,%rcx
  403781:	ba fa 00 00 00       	mov    $0xfa,%edx
  403786:	be 01 00 00 00       	mov    $0x1,%esi
  40378b:	49 89 c5             	mov    %rax,%r13
    sprintf(c, "mailbox %d\n", datas[x]->id);
  40378e:	49 8b 47 f8          	mov    -0x8(%r15),%rax
  403792:	4c 89 ef             	mov    %r13,%rdi
  403795:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
  40379c:	31 c0                	xor    %eax,%eax
  40379e:	e8 3d eb ff ff       	call   4022e0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4037a3:	4c 89 ea             	mov    %r13,%rdx
  4037a6:	4c 89 f6             	mov    %r14,%rsi
  4037a9:	bf 01 00 00 00       	mov    $0x1,%edi
  4037ae:	31 c0                	xor    %eax,%eax
  4037b0:	e8 1b ea ff ff       	call   4021d0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  4037b5:	4c 89 e6             	mov    %r12,%rsi
  4037b8:	4c 89 ef             	mov    %r13,%rdi
  4037bb:	e8 20 e9 ff ff       	call   4020e0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
  4037c0:	49 39 df             	cmp    %rbx,%r15
  4037c3:	75 a6                	jne    40376b <main+0x142b>
  4037c5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
  4037ca:	4c 89 e7             	mov    %r12,%rdi
  4037cd:	e8 ae e8 ff ff       	call   402080 <fclose@plt>
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
  4037d2:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
  4037d7:	c7 44 24 50 00 00 00 00 	movl   $0x0,0x50(%rsp)
  long received = 0;
  4037df:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  4037e8:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  long sents = 0;
  4037ed:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
  long sends = 0;
  4037f6:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  long ingests = 0;
  4037ff:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  long total = 0;
  403808:	48 c7 44 24 40 00 00 00 00 	movq   $0x0,0x40(%rsp)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  403811:	bf 0a 00 00 00       	mov    $0xa,%edi
  403816:	8b 5c 24 50          	mov    0x50(%rsp),%ebx
  40381a:	e8 11 e8 ff ff       	call   402030 <putchar@plt>
  40381f:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  403824:	bf 01 00 00 00       	mov    $0x1,%edi
  403829:	48 8d 35 91 4d 00 00 	lea    0x4d91(%rip),%rsi        # 4085c1 <_IO_stdin_used+0x5c1>
  403830:	83 f3 01             	xor    $0x1,%ebx
  403833:	48 8b 10             	mov    (%rax),%rdx
  403836:	31 c0                	xor    %eax,%eax
  403838:	e8 93 e9 ff ff       	call   4021d0 <__printf_chk@plt>
        other = (x + 1) % total_threads;
      }
      printf("\n");
      printf("Total Protected %ld\n", protected_state[me].protected);

      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
  40383d:	41 8b 57 08          	mov    0x8(%r15),%edx
  403841:	85 d2                	test   %edx,%edx
  403843:	0f 8e 2a 06 00 00    	jle    403e73 <main+0x1b33>
        v += thread_data[me].tasks[n].v;
  403849:	49 8b 0f             	mov    (%r15),%rcx
  40384c:	83 ea 01             	sub    $0x1,%edx
  40384f:	48 c1 e2 09          	shl    $0x9,%rdx
  403853:	48 8d 81 10 01 00 00 	lea    0x110(%rcx),%rax
  40385a:	48 8d 8c 11 10 03 00 00 	lea    0x310(%rcx,%rdx,1),%rcx
      long v = 0;
  403862:	31 d2                	xor    %edx,%edx
  403864:	0f 1f 40 00          	nopl   0x0(%rax)
        v += thread_data[me].tasks[n].v;
  403868:	48 03 10             	add    (%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
  40386b:	48 05 00 02 00 00    	add    $0x200,%rax
  403871:	48 39 c1             	cmp    %rax,%rcx
  403874:	75 f2                	jne    403868 <main+0x1528>
      }
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
  403876:	48 63 db             	movslq %ebx,%rbx
  403879:	48 8d 04 db          	lea    (%rbx,%rbx,8),%rax
  40387d:	48 8d 04 43          	lea    (%rbx,%rax,2),%rax
  403881:	48 c1 e0 04          	shl    $0x4,%rax
  403885:	48 03 44 24 48       	add    0x48(%rsp),%rax
  40388a:	8b 48 40             	mov    0x40(%rax),%ecx
  40388d:	85 c9                	test   %ecx,%ecx
  40388f:	7e 2d                	jle    4038be <main+0x157e>
        v += thread_data[other].tasks[n].v;
  403891:	48 8b 70 38          	mov    0x38(%rax),%rsi
  403895:	83 e9 01             	sub    $0x1,%ecx
  403898:	48 c1 e1 09          	shl    $0x9,%rcx
  40389c:	48 8d 86 10 01 00 00 	lea    0x110(%rsi),%rax
  4038a3:	48 8d 8c 0e 10 03 00 00 	lea    0x310(%rsi,%rcx,1),%rcx
  4038ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4038b0:	48 03 10             	add    (%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
  4038b3:	48 05 00 02 00 00    	add    $0x200,%rax
  4038b9:	48 39 c8             	cmp    %rcx,%rax
  4038bc:	75 f2                	jne    4038b0 <main+0x1570>
  4038be:	48 8d 35 11 4d 00 00 	lea    0x4d11(%rip),%rsi        # 4085d6 <_IO_stdin_used+0x5d6>
  4038c5:	bf 01 00 00 00       	mov    $0x1,%edi
  4038ca:	31 c0                	xor    %eax,%eax
  4038cc:	e8 ff e8 ff ff       	call   4021d0 <__printf_chk@plt>
      }
      printf("Total V %ld\n", v);
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
  4038d1:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  4038d6:	bf 01 00 00 00       	mov    $0x1,%edi
  4038db:	48 8d 35 2e 51 00 00 	lea    0x512e(%rip),%rsi        # 408a10 <_IO_stdin_used+0xa10>
  4038e2:	48 8b 08             	mov    (%rax),%rcx
  4038e5:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
  4038ef:	48 f7 e9             	imul   %rcx
  4038f2:	48 c1 f9 3f          	sar    $0x3f,%rcx
  4038f6:	31 c0                	xor    %eax,%eax
  4038f8:	48 c1 fa 02          	sar    $0x2,%rdx
  4038fc:	48 29 ca             	sub    %rcx,%rdx
  4038ff:	e8 cc e8 ff ff       	call   4021d0 <__printf_chk@plt>
  403904:	bf 0a 00 00 00       	mov    $0xa,%edi
  403909:	e8 22 e7 ff ff       	call   402030 <putchar@plt>
      printf("\n");
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
  40390e:	41 8b 4f 08          	mov    0x8(%r15),%ecx
  403912:	85 c9                	test   %ecx,%ecx
  403914:	0f 8e 39 01 00 00    	jle    403a53 <main+0x1713>
  40391a:	45 31 f6             	xor    %r14d,%r14d
  40391d:	4c 8d 25 bf 4c 00 00 	lea    0x4cbf(%rip),%r12        # 4085e3 <_IO_stdin_used+0x5e3>
  403924:	48 8d 2d 05 51 00 00 	lea    0x5105(%rip),%rbp        # 408a30 <_IO_stdin_used+0xa30>
  40392b:	45 89 f5             	mov    %r14d,%r13d
  40392e:	44 8b 74 24 50       	mov    0x50(%rsp),%r14d
  403933:	eb 1a                	jmp    40394f <main+0x160f>
  403935:	0f 1f 00             	nopl   (%rax)
  403938:	44 89 e8             	mov    %r13d,%eax
  40393b:	45 89 f5             	mov    %r14d,%r13d
  40393e:	41 83 c5 01          	add    $0x1,%r13d
  403942:	41 89 c6             	mov    %eax,%r14d
  403945:	45 39 6f 08          	cmp    %r13d,0x8(%r15)
  403949:	0f 8e 04 01 00 00    	jle    403a53 <main+0x1713>
        total += thread_data[x].tasks[n].n;
  40394f:	49 63 dd             	movslq %r13d,%rbx
  403952:	48 c1 e3 09          	shl    $0x9,%rbx
  403956:	48 89 d8             	mov    %rbx,%rax
  403959:	49 03 07             	add    (%r15),%rax
  40395c:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  403961:	48 8b 98 08 01 00 00 	mov    0x108(%rax),%rbx
  403968:	48 01 5c 24 40       	add    %rbx,0x40(%rsp)
        ingests += thread_data[x].tasks[n].ingest_count;
  40396d:	48 8b 98 68 01 00 00 	mov    0x168(%rax),%rbx
        sends += thread_data[x].tasks[n].sends;
  403974:	48 8b 80 80 01 00 00 	mov    0x180(%rax),%rax
  40397b:	48 01 44 24 30       	add    %rax,0x30(%rsp)
  403980:	44 89 f0             	mov    %r14d,%eax
  403983:	45 89 ee             	mov    %r13d,%r14d
        ingests += thread_data[x].tasks[n].ingest_count;
  403986:	48 01 5c 24 28       	add    %rbx,0x28(%rsp)
  40398b:	41 89 c5             	mov    %eax,%r13d
        sends += thread_data[x].tasks[n].sends;
  40398e:	31 db                	xor    %ebx,%ebx
  403990:	41 89 d8             	mov    %ebx,%r8d
  403993:	44 89 f1             	mov    %r14d,%ecx
  403996:	44 89 ea             	mov    %r13d,%edx
  403999:	4c 89 e6             	mov    %r12,%rsi
  40399c:	bf 01 00 00 00       	mov    $0x1,%edi
  4039a1:	31 c0                	xor    %eax,%eax
  4039a3:	e8 28 e8 ff ff       	call   4021d0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          printf("combo %d %d %d\n", x, n, kk);
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
  4039a8:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
  4039ad:	49 8b 37             	mov    (%r15),%rsi
  4039b0:	48 89 d8             	mov    %rbx,%rax
  4039b3:	48 c1 e0 08          	shl    $0x8,%rax
  4039b7:	44 89 ea             	mov    %r13d,%edx
  4039ba:	41 89 d8             	mov    %ebx,%r8d
  4039bd:	44 89 f1             	mov    %r14d,%ecx
  4039c0:	48 03 84 3e 70 01 00 00 	add    0x170(%rsi,%rdi,1),%rax
  4039c8:	bf 01 00 00 00       	mov    $0x1,%edi
  4039cd:	48 8b 30             	mov    (%rax),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
  4039d0:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
  4039d7:	4c 8b 88 80 03 00 00 	mov    0x380(%rax),%r9

          long tempsent = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
  4039de:	48 8b 80 00 04 00 00 	mov    0x400(%rax),%rax
  4039e5:	4c 03 8e 80 03 00 00 	add    0x380(%rsi),%r9
  4039ec:	48 03 86 00 04 00 00 	add    0x400(%rsi),%rax
  4039f3:	48 89 ee             	mov    %rbp,%rsi
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
  4039f6:	48 01 44 24 20       	add    %rax,0x20(%rsp)
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
  4039fb:	4c 01 4c 24 10       	add    %r9,0x10(%rsp)
  403a00:	48 83 ec 08          	sub    $0x8,%rsp
  403a04:	50                   	push   %rax
  403a05:	31 c0                	xor    %eax,%eax
  403a07:	e8 c4 e7 ff ff       	call   4021d0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
  403a0c:	58                   	pop    %rax
  403a0d:	5a                   	pop    %rdx
  403a0e:	48 83 fb 01          	cmp    $0x1,%rbx
  403a12:	0f 84 20 ff ff ff    	je     403938 <main+0x15f8>
  403a18:	bb 01 00 00 00       	mov    $0x1,%ebx
  403a1d:	e9 6e ff ff ff       	jmp    403990 <main+0x1650>
  403a22:	bb 01 00 00 00       	mov    $0x1,%ebx
  403a27:	e9 23 f5 ff ff       	jmp    402f4f <main+0xc0f>
  403a2c:	bd 01 00 00 00       	mov    $0x1,%ebp
  403a31:	e9 ab ef ff ff       	jmp    4029e1 <main+0x6a1>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  403a36:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
  403a40:	48 89 01             	mov    %rax,(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
  403a43:	4a 8b 84 27 70 01 00 00 	mov    0x170(%rdi,%r12,1),%rax
  403a4b:	48 01 f0             	add    %rsi,%rax
  403a4e:	e9 3e f5 ff ff       	jmp    402f91 <main+0xc51>
          printf("ttotal td%d tsk%d %dmb %ld %ld\n", x, n, kk, tempsent, temprec);
        }
      }
      for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
  403a53:	49 8b 4f 60          	mov    0x60(%r15),%rcx
  403a57:	48 85 c9             	test   %rcx,%rcx
  403a5a:	7e 0f                	jle    403a6b <main+0x172b>
  403a5c:	31 c0                	xor    %eax,%eax
  403a5e:	66 90                	xchg   %ax,%ax
  403a60:	83 c0 01             	add    $0x1,%eax
  403a63:	48 63 d0             	movslq %eax,%rdx
  403a66:	48 39 ca             	cmp    %rcx,%rdx
  403a69:	7c f5                	jl     403a60 <main+0x1720>
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        // printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
        // printf("%ld iterations\n", thread_data[x].iteration_count);
      }
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  403a6b:	31 ed                	xor    %ebp,%ebp
  403a6d:	31 c0                	xor    %eax,%eax
  403a6f:	48 8d 1d da 4f 00 00 	lea    0x4fda(%rip),%rbx        # 408a50 <_IO_stdin_used+0xa50>
  403a76:	49 83 7f 78 00       	cmpq   $0x0,0x78(%r15)
  403a7b:	7e 5e                	jle    403adb <main+0x179b>
  403a7d:	0f 1f 00             	nopl   (%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
  403a80:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  403a84:	49 8b 47 68          	mov    0x68(%r15),%rax
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  403a88:	48 83 ec 08          	sub    $0x8,%rsp
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  403a8c:	83 c5 01             	add    $0x1,%ebp
  403a8f:	bf 01 00 00 00       	mov    $0x1,%edi
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
  403a94:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
  403a98:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
  403aa2:	48 8b 71 18          	mov    0x18(%rcx),%rsi
  403aa6:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
  403aaa:	48 f7 e6             	mul    %rsi
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
  403aad:	4c 8b 41 10          	mov    0x10(%rcx),%r8
  403ab1:	4c 2b 01             	sub    (%rcx),%r8
  403ab4:	31 c0                	xor    %eax,%eax
  403ab6:	8b 49 20             	mov    0x20(%rcx),%ecx
  403ab9:	56                   	push   %rsi
  403aba:	48 89 de             	mov    %rbx,%rsi
  403abd:	48 c1 ea 12          	shr    $0x12,%rdx
  403ac1:	49 89 d1             	mov    %rdx,%r9
  403ac4:	ba 02 00 00 00       	mov    $0x2,%edx
  403ac9:	e8 02 e7 ff ff       	call   4021d0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
  403ace:	41 5a                	pop    %r10
  403ad0:	48 63 c5             	movslq %ebp,%rax
  403ad3:	41 5b                	pop    %r11
  403ad5:	49 3b 47 78          	cmp    0x78(%r15),%rax
  403ad9:	7c a5                	jl     403a80 <main+0x1740>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
  403adb:	41 8b 97 94 00 00 00 	mov    0x94(%r15),%edx
  403ae2:	85 d2                	test   %edx,%edx
  403ae4:	0f 8e ea 00 00 00    	jle    403bd4 <main+0x1894>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
  403aea:	49 8b 77 18          	mov    0x18(%r15),%rsi
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
  403aee:	31 ed                	xor    %ebp,%ebp
  403af0:	4c 8d 2d a9 4f 00 00 	lea    0x4fa9(%rip),%r13        # 408aa0 <_IO_stdin_used+0xaa0>
  403af7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
  403b00:	48 63 c5             	movslq %ebp,%rax
  403b03:	4c 8d 24 c5 00 00 00 00 	lea    0x0(,%rax,8),%r12
  403b0b:	48 8b 04 c6          	mov    (%rsi,%rax,8),%rax
  403b0f:	8b 08                	mov    (%rax),%ecx
  403b11:	85 c9                	test   %ecx,%ecx
  403b13:	0f 8e b0 00 00 00    	jle    403bc9 <main+0x1889>
  403b19:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
  403b21:	48 8b 50 08          	mov    0x8(%rax),%rdx
  403b25:	0f 1f 00             	nopl   (%rax)
  403b28:	48 63 44 24 08       	movslq 0x8(%rsp),%rax
  403b2d:	45 31 f6             	xor    %r14d,%r14d
  403b30:	48 8d 1c 80          	lea    (%rax,%rax,4),%rbx
  403b34:	48 c1 e3 03          	shl    $0x3,%rbx
  403b38:	48 8d 04 1a          	lea    (%rdx,%rbx,1),%rax
  403b3c:	8b 78 1c             	mov    0x1c(%rax),%edi
  403b3f:	85 ff                	test   %edi,%edi
  403b41:	7e 6e                	jle    403bb1 <main+0x1871>
  403b43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
  403b48:	49 63 ce             	movslq %r14d,%rcx
  403b4b:	48 83 ec 08          	sub    $0x8,%rsp
  403b4f:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
  403b54:	41 83 c6 01          	add    $0x1,%r14d
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
  403b58:	48 c1 e1 05          	shl    $0x5,%rcx
  403b5c:	48 03 48 10          	add    0x10(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
  403b60:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
  403b6a:	48 8b 71 18          	mov    0x18(%rcx),%rsi
  403b6e:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
  403b72:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
  403b75:	4c 8b 41 10          	mov    0x10(%rcx),%r8
  403b79:	4c 2b 01             	sub    (%rcx),%r8
  403b7c:	56                   	push   %rsi
  403b7d:	89 e9                	mov    %ebp,%ecx
  403b7f:	4c 89 ee             	mov    %r13,%rsi
  403b82:	31 c0                	xor    %eax,%eax
  403b84:	48 c1 ea 12          	shr    $0x12,%rdx
  403b88:	49 89 d1             	mov    %rdx,%r9
  403b8b:	ba 02 00 00 00       	mov    $0x2,%edx
  403b90:	e8 3b e6 ff ff       	call   4021d0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
  403b95:	49 8b 77 18          	mov    0x18(%r15),%rsi
  403b99:	41 58                	pop    %r8
  403b9b:	41 59                	pop    %r9
  403b9d:	4a 8b 0c 26          	mov    (%rsi,%r12,1),%rcx
  403ba1:	48 8b 51 08          	mov    0x8(%rcx),%rdx
  403ba5:	48 8d 04 1a          	lea    (%rdx,%rbx,1),%rax
  403ba9:	44 39 70 1c          	cmp    %r14d,0x1c(%rax)
  403bad:	7f 99                	jg     403b48 <main+0x1808>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
  403baf:	8b 09                	mov    (%rcx),%ecx
  403bb1:	83 44 24 08 01       	addl   $0x1,0x8(%rsp)
  403bb6:	8b 44 24 08          	mov    0x8(%rsp),%eax
  403bba:	39 c8                	cmp    %ecx,%eax
  403bbc:	0f 8c 66 ff ff ff    	jl     403b28 <main+0x17e8>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
  403bc2:	41 8b 97 94 00 00 00 	mov    0x94(%r15),%edx
  403bc9:	83 c5 01             	add    $0x1,%ebp
  403bcc:	39 d5                	cmp    %edx,%ebp
  403bce:	0f 8c 2c ff ff ff    	jl     403b00 <main+0x17c0>
    for (int d = 0 ; d < threads_per_group ; d++) {
  403bd4:	48 83 44 24 58 18    	addq   $0x18,0x58(%rsp)
  403bda:	49 81 c7 30 01 00 00 	add    $0x130,%r15
  403be1:	83 7c 24 50 01       	cmpl   $0x1,0x50(%rsp)
  403be6:	0f 85 a9 01 00 00    	jne    403d95 <main+0x1a55>
  403bec:	4c 8b 7c 24 40       	mov    0x40(%rsp),%r15
  403bf1:	48 8d 35 fb 49 00 00 	lea    0x49fb(%rip),%rsi        # 4085f3 <_IO_stdin_used+0x5f3>
  403bf8:	bf 01 00 00 00       	mov    $0x1,%edi
  403bfd:	31 c0                	xor    %eax,%eax
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
  403bff:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
  403c09:	4c 89 fa             	mov    %r15,%rdx
  403c0c:	e8 bf e5 ff ff       	call   4021d0 <__printf_chk@plt>
  403c11:	bf 0a 00 00 00       	mov    $0xa,%edi
  403c16:	e8 15 e4 ff ff       	call   402030 <putchar@plt>
  403c1b:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
  403c20:	bf 01 00 00 00       	mov    $0x1,%edi
  403c25:	48 8d 35 cc 4e 00 00 	lea    0x4ecc(%rip),%rsi        # 408af8 <_IO_stdin_used+0xaf8>
  403c2c:	48 8b 50 08          	mov    0x8(%rax),%rdx
  403c30:	31 c0                	xor    %eax,%eax
  403c32:	e8 99 e5 ff ff       	call   4021d0 <__printf_chk@plt>
  403c37:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
  403c3c:	bf 01 00 00 00       	mov    $0x1,%edi
  403c41:	48 8d 35 d8 4e 00 00 	lea    0x4ed8(%rip),%rsi        # 408b20 <_IO_stdin_used+0xb20>
  403c48:	48 f7 eb             	imul   %rbx
  403c4b:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
  403c50:	48 c1 f8 3f          	sar    $0x3f,%rax
  403c54:	48 c1 fa 02          	sar    $0x2,%rdx
  403c58:	48 29 c2             	sub    %rax,%rdx
  403c5b:	31 c0                	xor    %eax,%eax
  403c5d:	e8 6e e5 ff ff       	call   4021d0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
  403c62:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
  403c67:	bf 01 00 00 00       	mov    $0x1,%edi
  403c6c:	48 8d 35 dd 4e 00 00 	lea    0x4edd(%rip),%rsi        # 408b50 <_IO_stdin_used+0xb50>
  403c73:	48 f7 eb             	imul   %rbx
  403c76:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
  403c7b:	48 c1 f8 3f          	sar    $0x3f,%rax
  403c7f:	48 c1 fa 02          	sar    $0x2,%rdx
  403c83:	48 29 c2             	sub    %rax,%rdx
  403c86:	31 c0                	xor    %eax,%eax
  403c88:	e8 43 e5 ff ff       	call   4021d0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
  403c8d:	4c 89 f8             	mov    %r15,%rax
  403c90:	bf 01 00 00 00       	mov    $0x1,%edi
  403c95:	48 8d 35 e4 4e 00 00 	lea    0x4ee4(%rip),%rsi        # 408b80 <_IO_stdin_used+0xb80>
  403c9c:	48 f7 eb             	imul   %rbx
  403c9f:	4c 89 f8             	mov    %r15,%rax
  403ca2:	48 c1 f8 3f          	sar    $0x3f,%rax
  403ca6:	48 c1 fa 02          	sar    $0x2,%rdx
  403caa:	48 29 c2             	sub    %rax,%rdx
  403cad:	31 c0                	xor    %eax,%eax
  403caf:	e8 1c e5 ff ff       	call   4021d0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
  403cb4:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  403cb9:	bf 01 00 00 00       	mov    $0x1,%edi
  403cbe:	48 8d 35 42 49 00 00 	lea    0x4942(%rip),%rsi        # 408607 <_IO_stdin_used+0x607>
  403cc5:	48 f7 eb             	imul   %rbx
  403cc8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  403ccd:	48 c1 f8 3f          	sar    $0x3f,%rax
  403cd1:	48 c1 fa 02          	sar    $0x2,%rdx
  403cd5:	48 29 c2             	sub    %rax,%rdx
  403cd8:	31 c0                	xor    %eax,%eax
  403cda:	48 89 d5             	mov    %rdx,%rbp
  403cdd:	e8 ee e4 ff ff       	call   4021d0 <__printf_chk@plt>
  printf("Total sents per second %ld\n", sentdur);
  long recdur = received / DURATION;
  403ce2:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
  403ce7:	bf 01 00 00 00       	mov    $0x1,%edi
  403cec:	48 8d 35 ad 4e 00 00 	lea    0x4ead(%rip),%rsi        # 408ba0 <_IO_stdin_used+0xba0>
  403cf3:	48 f7 eb             	imul   %rbx
  403cf6:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
  403cfb:	48 c1 f8 3f          	sar    $0x3f,%rax
  403cff:	48 89 d3             	mov    %rdx,%rbx
  403d02:	48 c1 fb 02          	sar    $0x2,%rbx
  403d06:	48 29 c3             	sub    %rax,%rbx
  403d09:	31 c0                	xor    %eax,%eax
  403d0b:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives per second %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
  403d0e:	48 29 eb             	sub    %rbp,%rbx
  403d11:	e8 ba e4 ff ff       	call   4021d0 <__printf_chk@plt>
  403d16:	31 c0                	xor    %eax,%eax
  403d18:	48 89 da             	mov    %rbx,%rdx
  403d1b:	bf 01 00 00 00       	mov    $0x1,%edi
  403d20:	48 8d 35 fc 48 00 00 	lea    0x48fc(%rip),%rsi        # 408623 <_IO_stdin_used+0x623>
  403d27:	e8 a4 e4 ff ff       	call   4021d0 <__printf_chk@plt>
  return 0;

}
  403d2c:	48 8b 84 24 e8 00 00 00 	mov    0xe8(%rsp),%rax
  403d34:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  403d3d:	0f 85 42 01 00 00    	jne    403e85 <main+0x1b45>
  403d43:	48 81 c4 f8 00 00 00 	add    $0xf8,%rsp
  403d4a:	31 c0                	xor    %eax,%eax
  403d4c:	5b                   	pop    %rbx
  403d4d:	5d                   	pop    %rbp
  403d4e:	41 5c                	pop    %r12
  403d50:	41 5d                	pop    %r13
  403d52:	41 5e                	pop    %r14
  403d54:	41 5f                	pop    %r15
  403d56:	c3                   	ret
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  403d57:	41 b8 6e 64 00 00    	mov    $0x646e,%r8d
  403d5d:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
  403d63:	66 44 89 41 04       	mov    %r8w,0x4(%rcx)
  403d68:	c6 41 06 00          	movb   $0x0,0x6(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
  403d6c:	4a 8b 84 27 70 01 00 00 	mov    0x170(%rdi,%r12,1),%rax
  403d74:	48 01 f0             	add    %rsi,%rax
  403d77:	e9 15 f2 ff ff       	jmp    402f91 <main+0xc51>
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
  403d7c:	48 c7 c0 c0 79 40 00 	mov    $0x4079c0,%rax
  403d83:	41 bc 01 00 00 00    	mov    $0x1,%r12d
  403d89:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
        for (int y = 0 ; y < total_barrier_count ; y++) {
  403d90:	e9 0a ec ff ff       	jmp    40299f <main+0x65f>
  403d95:	c7 44 24 50 01 00 00 00 	movl   $0x1,0x50(%rsp)
  403d9d:	e9 6f fa ff ff       	jmp    403811 <main+0x14d1>
            thread_data[x].tasks[y].run = barriered_work; 
  403da2:	48 c7 c0 d0 72 40 00 	mov    $0x4072d0,%rax
  403da9:	41 bc 02 00 00 00    	mov    $0x2,%r12d
  403daf:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
        for (int y = 0 ; y < total_barrier_count ; y++) {
  403db6:	e9 e4 eb ff ff       	jmp    40299f <main+0x65f>
  403dbb:	48 c7 44 24 68 01 00 00 00 	movq   $0x1,0x68(%rsp)
  403dc4:	e9 eb e9 ff ff       	jmp    4027b4 <main+0x474>
  403dc9:	bb 06 00 00 00       	mov    $0x6,%ebx
  403dce:	e9 77 f7 ff ff       	jmp    40354a <main+0x120a>
  403dd3:	bb 04 00 00 00       	mov    $0x4,%ebx
  403dd8:	e9 d8 f5 ff ff       	jmp    4033b5 <main+0x1075>
      thread_data[x].identity = unknown_identity;
  403ddd:	85 c9                	test   %ecx,%ecx
  403ddf:	48 8d 3d eb 44 00 00 	lea    0x44eb(%rip),%rdi        # 4082d1 <_IO_stdin_used+0x2d1>
  403de6:	48 8d 05 d5 44 00 00 	lea    0x44d5(%rip),%rax        # 4082c2 <_IO_stdin_used+0x2c2>
    thread_data[x].io_mode = myring;
  403ded:	41 89 8e 0c 01 00 00 	mov    %ecx,0x10c(%r14)
      thread_data[x].identity = unknown_identity;
  403df4:	48 0f 45 c7          	cmovne %rdi,%rax
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  403df8:	ba 03 00 00 00       	mov    $0x3,%edx
  403dfd:	4c 89 e6             	mov    %r12,%rsi
    thread_data[x].my_io = myring;
  403e00:	41 89 8e 1c 01 00 00 	mov    %ecx,0x11c(%r14)
    thread_data[x].other_io = otherring;
  403e07:	45 89 86 18 01 00 00 	mov    %r8d,0x118(%r14)
  403e0e:	bf 01 00 00 00       	mov    $0x1,%edi
  403e13:	49 89 86 20 01 00 00 	mov    %rax,0x120(%r14)
  403e1a:	31 c0                	xor    %eax,%eax
    thread_data[x].iomailboxes = iomailboxes; 
  403e1c:	4d 89 ae 10 01 00 00 	mov    %r13,0x110(%r14)
  403e23:	e8 a8 e3 ff ff       	call   4021d0 <__printf_chk@plt>
    thread_data[x].ring = rings[myring]; 
  403e28:	49 8b 07             	mov    (%r15),%rax
    int myeventfd = eventfd(0, EFD_NONBLOCK);
  403e2b:	be 00 08 00 00       	mov    $0x800,%esi
  403e30:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = rings[myring]; 
  403e32:	49 89 46 60          	mov    %rax,0x60(%r14)
    int myeventfd = eventfd(0, EFD_NONBLOCK);
  403e36:	e8 15 e4 ff ff       	call   402250 <eventfd@plt>
      datafd = dataeventfds[0];
  403e3b:	8b 54 24 10          	mov    0x10(%rsp),%edx
      otherdataeventfd = dataeventfds[1];
  403e3f:	8b 4c 24 28          	mov    0x28(%rsp),%ecx
  403e43:	e9 fa f5 ff ff       	jmp    403442 <main+0x1102>
  403e48:	c7 44 24 10 01 00 00 00 	movl   $0x1,0x10(%rsp)
  403e50:	e9 c1 f0 ff ff       	jmp    402f16 <main+0xbd6>
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
  403e55:	48 8d 45 08          	lea    0x8(%rbp),%rax
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  403e59:	48 8b 54 24 48       	mov    0x48(%rsp),%rdx
  403e5e:	41 b8 01 00 00 00    	mov    $0x1,%r8d
        other = abs(x - 1) % total_threads;
  403e64:	31 db                	xor    %ebx,%ebx
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
  403e66:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
  403e6b:	4c 89 f8             	mov    %r15,%rax
  403e6e:	e9 fa e9 ff ff       	jmp    40286d <main+0x52d>
      long v = 0;
  403e73:	31 d2                	xor    %edx,%edx
  403e75:	e9 fc f9 ff ff       	jmp    403876 <main+0x1536>
  403e7a:	41 bc 02 00 00 00    	mov    $0x2,%r12d
  403e80:	e9 1a eb ff ff       	jmp    40299f <main+0x65f>
}
  403e85:	e8 16 e2 ff ff       	call   4020a0 <__stack_chk_fail@plt>
            exit(1);
  403e8a:	bf 01 00 00 00       	mov    $0x1,%edi
  403e8f:	e8 ac e3 ff ff       	call   402240 <exit@plt>
  403e94:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  403e9e:	66 90                	xchg   %ax,%ax

0000000000403ea0 <_start>:
  403ea0:	f3 0f 1e fa          	endbr64
  403ea4:	31 ed                	xor    %ebp,%ebp
  403ea6:	49 89 d1             	mov    %rdx,%r9
  403ea9:	5e                   	pop    %rsi
  403eaa:	48 89 e2             	mov    %rsp,%rdx
  403ead:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  403eb1:	50                   	push   %rax
  403eb2:	54                   	push   %rsp
  403eb3:	45 31 c0             	xor    %r8d,%r8d
  403eb6:	31 c9                	xor    %ecx,%ecx
  403eb8:	48 c7 c7 40 23 40 00 	mov    $0x402340,%rdi
  403ebf:	ff 15 13 71 00 00    	call   *0x7113(%rip)        # 40afd8 <__libc_start_main@GLIBC_2.34>
  403ec5:	f4                   	hlt
  403ec6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000403ed0 <_dl_relocate_static_pie>:
  403ed0:	f3 0f 1e fa          	endbr64
  403ed4:	c3                   	ret
  403ed5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  403edf:	90                   	nop

0000000000403ee0 <deregister_tm_clones>:
  403ee0:	b8 20 b0 40 00       	mov    $0x40b020,%eax
  403ee5:	48 3d 20 b0 40 00    	cmp    $0x40b020,%rax
  403eeb:	74 13                	je     403f00 <deregister_tm_clones+0x20>
  403eed:	b8 00 00 00 00       	mov    $0x0,%eax
  403ef2:	48 85 c0             	test   %rax,%rax
  403ef5:	74 09                	je     403f00 <deregister_tm_clones+0x20>
  403ef7:	bf 20 b0 40 00       	mov    $0x40b020,%edi
  403efc:	ff e0                	jmp    *%rax
  403efe:	66 90                	xchg   %ax,%ax
  403f00:	c3                   	ret
  403f01:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  403f0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000403f10 <register_tm_clones>:
  403f10:	be 20 b0 40 00       	mov    $0x40b020,%esi
  403f15:	48 81 ee 20 b0 40 00 	sub    $0x40b020,%rsi
  403f1c:	48 89 f0             	mov    %rsi,%rax
  403f1f:	48 c1 ee 3f          	shr    $0x3f,%rsi
  403f23:	48 c1 f8 03          	sar    $0x3,%rax
  403f27:	48 01 c6             	add    %rax,%rsi
  403f2a:	48 d1 fe             	sar    %rsi
  403f2d:	74 11                	je     403f40 <register_tm_clones+0x30>
  403f2f:	b8 00 00 00 00       	mov    $0x0,%eax
  403f34:	48 85 c0             	test   %rax,%rax
  403f37:	74 07                	je     403f40 <register_tm_clones+0x30>
  403f39:	bf 20 b0 40 00       	mov    $0x40b020,%edi
  403f3e:	ff e0                	jmp    *%rax
  403f40:	c3                   	ret
  403f41:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  403f4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000403f50 <__do_global_dtors_aux>:
  403f50:	f3 0f 1e fa          	endbr64
  403f54:	80 3d c5 70 00 00 00 	cmpb   $0x0,0x70c5(%rip)        # 40b020 <__TMC_END__>
  403f5b:	75 13                	jne    403f70 <__do_global_dtors_aux+0x20>
  403f5d:	55                   	push   %rbp
  403f5e:	48 89 e5             	mov    %rsp,%rbp
  403f61:	e8 7a ff ff ff       	call   403ee0 <deregister_tm_clones>
  403f66:	c6 05 b3 70 00 00 01 	movb   $0x1,0x70b3(%rip)        # 40b020 <__TMC_END__>
  403f6d:	5d                   	pop    %rbp
  403f6e:	c3                   	ret
  403f6f:	90                   	nop
  403f70:	c3                   	ret
  403f71:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  403f7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000403f80 <frame_dummy>:
  403f80:	f3 0f 1e fa          	endbr64
  403f84:	eb 8a                	jmp    403f10 <register_tm_clones>
  403f86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000403f90 <do_protected_write>:
  struct ProtectedState *protected = data->thread->protected_state;
  403f90:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  403f97:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
  403f9b:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
  403fa3:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
  403fa7:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
  403fab:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
  403fb2:	48 85 c9             	test   %rcx,%rcx
  403fb5:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
  403fbc:	48 0f 4f d6          	cmovg  %rsi,%rdx
  403fc0:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
  403fc4:	31 c0                	xor    %eax,%eax
  403fc6:	c3                   	ret
  403fc7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000403fd0 <barriered_reset>:
    for (int x = 0 ; x < data->task_count ; x++) {
  403fd0:	8b 8f 48 01 00 00    	mov    0x148(%rdi),%ecx
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
  403fd6:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    for (int x = 0 ; x < data->task_count ; x++) {
  403fdd:	85 c9                	test   %ecx,%ecx
  403fdf:	7e 5a                	jle    40403b <barriered_reset+0x6b>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
  403fe1:	48 63 bf 30 01 00 00 	movslq 0x130(%rdi),%rdi
  403fe8:	48 8b 46 18          	mov    0x18(%rsi),%rax
  403fec:	83 e9 01             	sub    $0x1,%ecx
      data->thread->tasks[x].available = 1; 
  403fef:	4c 8b 46 38          	mov    0x38(%rsi),%r8
  403ff3:	48 c1 e1 09          	shl    $0x9,%rcx
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
  403ff7:	48 8b 04 f8          	mov    (%rax,%rdi,8),%rax
  403ffb:	49 8d 90 44 01 00 00 	lea    0x144(%r8),%rdx
  404002:	49 8d 8c 08 44 03 00 00 	lea    0x344(%r8,%rcx,1),%rcx
  40400a:	48 8b 40 38          	mov    0x38(%rax),%rax
  40400e:	48 05 00 01 00 00    	add    $0x100,%rax
  404014:	0f 1f 40 00          	nopl   0x0(%rax)
  404018:	83 40 80 01          	addl   $0x1,-0x80(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
  40401c:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
  404023:	83 00 01             	addl   $0x1,(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
  404026:	48 05 00 02 00 00    	add    $0x200,%rax
      data->thread->tasks[x].available = 1; 
  40402c:	c7 82 00 fe ff ff 01 00 00 00 	movl   $0x1,-0x200(%rdx)
    for (int x = 0 ; x < data->task_count ; x++) {
  404036:	48 39 ca             	cmp    %rcx,%rdx
  404039:	75 dd                	jne    404018 <barriered_reset+0x48>
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
  40403b:	48 8b 8e 00 01 00 00 	mov    0x100(%rsi),%rcx
  404042:	8b 01                	mov    (%rcx),%eax
  404044:	83 f8 ff             	cmp    $0xffffffff,%eax
  404047:	74 0d                	je     404056 <barriered_reset+0x86>
  404049:	8b be d0 00 00 00    	mov    0xd0(%rsi),%edi
  40404f:	8d 57 ff             	lea    -0x1(%rdi),%edx
  404052:	39 d0                	cmp    %edx,%eax
  404054:	74 0a                	je     404060 <barriered_reset+0x90>
}
  404056:	31 c0                	xor    %eax,%eax
  404058:	c3                   	ret
  404059:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
  404060:	83 7e 04 01          	cmpl   $0x1,0x4(%rsi)
  404064:	75 f0                	jne    404056 <barriered_reset+0x86>
    data->thread->group_data->arrived++;
  404066:	48 8b 86 e8 00 00 00 	mov    0xe8(%rsi),%rax
  40406d:	83 00 01             	addl   $0x1,(%rax)
    data->thread->global->request_group_sync = -1;
  404070:	c7 01 ff ff ff ff    	movl   $0xffffffff,(%rcx)
  404076:	eb de                	jmp    404056 <barriered_reset+0x86>
  404078:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000404080 <external_thread>:
  while (data->running == 1) {
  404080:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
  404084:	0f 85 e9 00 00 00    	jne    404173 <external_thread+0xf3>
void * external_thread(void *arg) {
  40408a:	41 57                	push   %r15
  40408c:	41 56                	push   %r14
  40408e:	4c 8d 35 6f 3f 00 00 	lea    0x3f6f(%rip),%r14        # 408004 <_IO_stdin_used+0x4>
  404095:	41 55                	push   %r13
  404097:	49 89 fd             	mov    %rdi,%r13
  40409a:	41 54                	push   %r12
  40409c:	55                   	push   %rbp
  40409d:	53                   	push   %rbx
  40409e:	48 83 ec 08          	sub    $0x8,%rsp
  4040a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int b = 0; b < data->buffers_count; b++) {
  4040a8:	41 8b 8d cc 00 00 00 	mov    0xcc(%r13),%ecx
  4040af:	85 c9                	test   %ecx,%ecx
  4040b1:	7e 59                	jle    40410c <external_thread+0x8c>
      for (int x = 0; x < data->buffers[b]->count; x++) {
  4040b3:	49 8b 7d 50          	mov    0x50(%r13),%rdi
    for (int b = 0; b < data->buffers_count; b++) {
  4040b7:	45 31 e4             	xor    %r12d,%r12d
  4040ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      for (int x = 0; x < data->buffers[b]->count; x++) {
  4040c0:	49 63 ec             	movslq %r12d,%rbp
  4040c3:	45 31 ff             	xor    %r15d,%r15d
  4040c6:	48 c1 e5 03          	shl    $0x3,%rbp
  4040ca:	48 8d 34 2f          	lea    (%rdi,%rbp,1),%rsi
  4040ce:	48 8b 06             	mov    (%rsi),%rax
  4040d1:	8b 10                	mov    (%rax),%edx
  4040d3:	85 d2                	test   %edx,%edx
  4040d5:	7e 2c                	jle    404103 <external_thread+0x83>
  4040d7:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
  4040db:	49 63 c7             	movslq %r15d,%rax
  4040de:	48 8d 1c 80          	lea    (%rax,%rax,4),%rbx
  4040e2:	48 c1 e3 03          	shl    $0x3,%rbx
  4040e6:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
  4040ea:	44 8b 40 08          	mov    0x8(%rax),%r8d
  4040ee:	45 85 c0             	test   %r8d,%r8d
  4040f1:	74 35                	je     404128 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
  4040f3:	41 83 c7 01          	add    $0x1,%r15d
  4040f7:	44 39 fa             	cmp    %r15d,%edx
  4040fa:	7f df                	jg     4040db <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
  4040fc:	41 8b 8d cc 00 00 00 	mov    0xcc(%r13),%ecx
  404103:	41 83 c4 01          	add    $0x1,%r12d
  404107:	41 39 cc             	cmp    %ecx,%r12d
  40410a:	7c b4                	jl     4040c0 <external_thread+0x40>
  while (data->running == 1) {
  40410c:	41 83 7d 44 01       	cmpl   $0x1,0x44(%r13)
  404111:	74 95                	je     4040a8 <external_thread+0x28>
}
  404113:	48 83 c4 08          	add    $0x8,%rsp
  404117:	31 c0                	xor    %eax,%eax
  404119:	5b                   	pop    %rbx
  40411a:	5d                   	pop    %rbp
  40411b:	41 5c                	pop    %r12
  40411d:	41 5d                	pop    %r13
  40411f:	41 5e                	pop    %r14
  404121:	41 5f                	pop    %r15
  404123:	c3                   	ret
  404124:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
  404128:	4c 89 30             	mov    %r14,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
  40412b:	48 8b 06             	mov    (%rsi),%rax
      for (int x = 0; x < data->buffers[b]->count; x++) {
  40412e:	41 83 c7 01          	add    $0x1,%r15d
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
  404132:	48 8b 78 08          	mov    0x8(%rax),%rdi
  404136:	48 01 df             	add    %rbx,%rdi
  404139:	48 63 77 1c          	movslq 0x1c(%rdi),%rsi
  40413d:	48 c1 e6 05          	shl    $0x5,%rsi
  404141:	48 03 77 10          	add    0x10(%rdi),%rsi
  404145:	bf 04 00 00 00       	mov    $0x4,%edi
  40414a:	e8 21 df ff ff       	call   402070 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
  40414f:	49 8b 7d 50          	mov    0x50(%r13),%rdi
  404153:	48 8d 34 2f          	lea    (%rdi,%rbp,1),%rsi
  404157:	48 8b 06             	mov    (%rsi),%rax
  40415a:	48 8b 50 08          	mov    0x8(%rax),%rdx
  40415e:	c7 44 1a 08 01 00 00 00 	movl   $0x1,0x8(%rdx,%rbx,1)
      for (int x = 0; x < data->buffers[b]->count; x++) {
  404166:	8b 10                	mov    (%rax),%edx
  404168:	41 39 d7             	cmp    %edx,%r15d
  40416b:	0f 8c 66 ff ff ff    	jl     4040d7 <external_thread+0x57>
  404171:	eb 89                	jmp    4040fc <external_thread+0x7c>
}
  404173:	31 c0                	xor    %eax,%eax
  404175:	c3                   	ret
  404176:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000404180 <timer_thread>:
void* timer_thread(void *arg) {
  404180:	41 57                	push   %r15
  404182:	48 8d 35 87 3e 00 00 	lea    0x3e87(%rip),%rsi        # 408010 <_IO_stdin_used+0x10>
  404189:	49 89 ff             	mov    %rdi,%r15
  40418c:	41 56                	push   %r14
  40418e:	41 55                	push   %r13
  404190:	41 54                	push   %r12
  404192:	55                   	push   %rbp
  404193:	53                   	push   %rbx
  404194:	48 83 ec 68          	sub    $0x68,%rsp
  404198:	8b 57 04             	mov    0x4(%rdi),%edx
  40419b:	bf 01 00 00 00       	mov    $0x1,%edi
  4041a0:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4041a9:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  4041ae:	31 c0                	xor    %eax,%eax
  4041b0:	e8 1b e0 ff ff       	call   4021d0 <__printf_chk@plt>
  struct timespec preempt = {
  4041b5:	66 0f 6f 05 53 4c 00 00 	movdqa 0x4c53(%rip),%xmm0        # 408e10 <_IO_stdin_used+0xe10>
  4041bd:	ba 10 27 00 00       	mov    $0x2710,%edx
  4041c2:	31 c0                	xor    %eax,%eax
  4041c4:	48 8d 35 57 3e 00 00 	lea    0x3e57(%rip),%rsi        # 408022 <_IO_stdin_used+0x22>
  4041cb:	bf 01 00 00 00       	mov    $0x1,%edi
  4041d0:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
  4041d5:	e8 f6 df ff ff       	call   4021d0 <__printf_chk@plt>
  while (data->running && n < times) {
  4041da:	45 8b 77 44          	mov    0x44(%r15),%r14d
  4041de:	45 85 f6             	test   %r14d,%r14d
  4041e1:	0f 84 a9 00 00 00    	je     404290 <timer_thread+0x110>
  int n = 0;
  4041e7:	45 31 ed             	xor    %r13d,%r13d
  int y = 0;
  4041ea:	45 31 f6             	xor    %r14d,%r14d
  4041ed:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
      y = 0;
  4041f2:	31 db                	xor    %ebx,%ebx
  4041f4:	48 8d 6c 24 20       	lea    0x20(%rsp),%rbp
    nanosleep(&preempt , &rem2);
  4041f9:	48 89 ef             	mov    %rbp,%rdi
  4041fc:	4c 89 e6             	mov    %r12,%rsi
    n++;
  4041ff:	41 83 c5 01          	add    $0x1,%r13d
    nanosleep(&preempt , &rem2);
  404203:	e8 b8 de ff ff       	call   4020c0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404208:	41 8b 57 30          	mov    0x30(%r15),%edx
    y++;
  40420c:	41 8d 7e 01          	lea    0x1(%r14),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404210:	85 d2                	test   %edx,%edx
  404212:	7e 57                	jle    40426b <timer_thread+0xeb>
  404214:	49 8b 47 18          	mov    0x18(%r15),%rax
        data->threads[x]->tasks[y].scheduled = 0;
  404218:	4d 63 c6             	movslq %r14d,%r8
  40421b:	83 ea 01             	sub    $0x1,%edx
  40421e:	49 c1 e0 09          	shl    $0x9,%r8
  404222:	48 8d 48 08          	lea    0x8(%rax),%rcx
  404226:	4c 8d 0c d1          	lea    (%rcx,%rdx,8),%r9
  40422a:	eb 08                	jmp    404234 <timer_thread+0xb4>
  40422c:	0f 1f 40 00          	nopl   0x0(%rax)
  404230:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
  404234:	4c 8b 10             	mov    (%rax),%r10
  404237:	89 f8                	mov    %edi,%eax
  404239:	99                   	cltd
  40423a:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
  40423e:	49 8b 72 38          	mov    0x38(%r10),%rsi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404242:	48 89 c8             	mov    %rcx,%rax
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
  404245:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
  404248:	48 63 d2             	movslq %edx,%rdx
  40424b:	48 c1 e2 09          	shl    $0x9,%rdx
  40424f:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
  40425a:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404266:	49 39 c9             	cmp    %rcx,%r9
  404269:	75 c5                	jne    404230 <timer_thread+0xb0>
    if (y >= data->threads[0]->task_count) {
  40426b:	49 8b 47 18          	mov    0x18(%r15),%rax
  while (data->running && n < times) {
  40426f:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    if (y >= data->threads[0]->task_count) {
  404273:	48 8b 00             	mov    (%rax),%rax
      y = 0;
  404276:	39 78 40             	cmp    %edi,0x40(%rax)
  404279:	0f 4e fb             	cmovle %ebx,%edi
  40427c:	41 89 fe             	mov    %edi,%r14d
  while (data->running && n < times) {
  40427f:	85 c9                	test   %ecx,%ecx
  404281:	74 0d                	je     404290 <timer_thread+0x110>
  404283:	41 81 fd 10 27 00 00 	cmp    $0x2710,%r13d
  40428a:	0f 85 69 ff ff ff    	jne    4041f9 <timer_thread+0x79>
  404290:	48 8d 3d a1 3d 00 00 	lea    0x3da1(%rip),%rdi        # 408038 <_IO_stdin_used+0x38>
  404297:	e8 b4 dd ff ff       	call   402050 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
  40429c:	49 63 47 30          	movslq 0x30(%r15),%rax
  4042a0:	85 c0                	test   %eax,%eax
  4042a2:	7e 56                	jle    4042fa <timer_thread+0x17a>
    for (int y = 0 ; y < data->task_count ; y++) {
  4042a4:	41 8b 57 40          	mov    0x40(%r15),%edx
  4042a8:	85 d2                	test   %edx,%edx
  4042aa:	7e 4e                	jle    4042fa <timer_thread+0x17a>
  4042ac:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
  4042b4:	8d 42 ff             	lea    -0x1(%rdx),%eax
      data->threads[x]->tasks[y].sending = 0;
  4042b7:	4d 8b 47 18          	mov    0x18(%r15),%r8
  4042bb:	31 c9                	xor    %ecx,%ecx
  4042bd:	48 c1 e0 09          	shl    $0x9,%rax
  4042c1:	48 8d b8 88 03 00 00 	lea    0x388(%rax),%rdi
  4042c8:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
  4042cc:	48 8b 50 38          	mov    0x38(%rax),%rdx
  4042d0:	48 8d 82 88 01 00 00 	lea    0x188(%rdx),%rax
  4042d7:	48 01 fa             	add    %rdi,%rdx
  4042da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  4042e0:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
  4042e6:	48 05 00 02 00 00    	add    $0x200,%rax
  4042ec:	48 39 c2             	cmp    %rax,%rdx
  4042ef:	75 ef                	jne    4042e0 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
  4042f1:	48 83 c1 08          	add    $0x8,%rcx
  4042f5:	48 39 ce             	cmp    %rcx,%rsi
  4042f8:	75 ce                	jne    4042c8 <timer_thread+0x148>
  struct timespec drain = {
  4042fa:	66 0f 6f 05 1e 4b 00 00 	movdqa 0x4b1e(%rip),%xmm0        # 408e20 <_IO_stdin_used+0xe20>
  404302:	48 8d 1d 4b 3d 00 00 	lea    0x3d4b(%rip),%rbx        # 408054 <_IO_stdin_used+0x54>
  404309:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
  40430e:	41 8b 57 28          	mov    0x28(%r15),%edx
    y++;
  404312:	41 8d 46 01          	lea    0x1(%r14),%eax
  404316:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
  40431a:	85 d2                	test   %edx,%edx
  40431c:	7e 5a                	jle    404378 <timer_thread+0x1f8>
  40431e:	41 89 c1             	mov    %eax,%r9d
  404321:	49 8b 47 18          	mov    0x18(%r15),%rax
        data->threads[x]->tasks[y].scheduled = 0;
  404325:	49 63 fe             	movslq %r14d,%rdi
  404328:	83 ea 01             	sub    $0x1,%edx
  40432b:	48 c1 e7 09          	shl    $0x9,%rdi
  40432f:	48 8d 48 08          	lea    0x8(%rax),%rcx
  404333:	4c 8d 04 d1          	lea    (%rcx,%rdx,8),%r8
  404337:	eb 0b                	jmp    404344 <timer_thread+0x1c4>
  404339:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  404340:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
  404344:	4c 8b 10             	mov    (%rax),%r10
  404347:	44 89 c8             	mov    %r9d,%eax
  40434a:	99                   	cltd
  40434b:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
  40434f:	49 8b 72 38          	mov    0x38(%r10),%rsi
    for (int x = 0 ; x < data->thread_count ; x++) {
  404353:	48 89 c8             	mov    %rcx,%rax
        data->threads[x]->tasks[next].scheduled = 1;
  404356:	48 63 d2             	movslq %edx,%rdx
  404359:	48 c1 e2 09          	shl    $0x9,%rdx
  40435d:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
  404368:	c7 84 3e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rdi,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
  404373:	4c 39 c1             	cmp    %r8,%rcx
  404376:	75 c8                	jne    404340 <timer_thread+0x1c0>
    if (y >= data->threads[0]->task_count) {
  404378:	49 8b 4f 18          	mov    0x18(%r15),%rcx
      y = 0;
  40437c:	8b 7c 24 0c          	mov    0xc(%rsp),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404380:	45 8b 77 30          	mov    0x30(%r15),%r14d
    if (y >= data->threads[0]->task_count) {
  404384:	48 8b 01             	mov    (%rcx),%rax
      y = 0;
  404387:	39 78 40             	cmp    %edi,0x40(%rax)
  40438a:	b8 00 00 00 00       	mov    $0x0,%eax
  40438f:	0f 4f c7             	cmovg  %edi,%eax
  404392:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404396:	45 85 f6             	test   %r14d,%r14d
  404399:	0f 8e be 01 00 00    	jle    40455d <timer_thread+0x3dd>
    int all_empty = 1;
  40439f:	c7 44 24 08 01 00 00 00 	movl   $0x1,0x8(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  4043a7:	45 31 ed             	xor    %r13d,%r13d
  4043aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
  4043b0:	49 63 ed             	movslq %r13d,%rbp
  4043b3:	45 31 e4             	xor    %r12d,%r12d
  4043b6:	48 c1 e5 03          	shl    $0x3,%rbp
  4043ba:	45 89 e2             	mov    %r12d,%r10d
        for (int k = 0 ; k < data->my_thread_count; k++) {
  4043bd:	45 85 f6             	test   %r14d,%r14d
  4043c0:	7e 7e                	jle    404440 <timer_thread+0x2c0>
  4043c2:	4c 89 e7             	mov    %r12,%rdi
  4043c5:	49 63 f6             	movslq %r14d,%rsi
  4043c8:	31 c0                	xor    %eax,%eax
  4043ca:	48 c1 e7 09          	shl    $0x9,%rdi
  4043ce:	66 90                	xchg   %ax,%ax
  4043d0:	41 89 c0             	mov    %eax,%r8d
          if (x == k) { continue; }
  4043d3:	41 39 c5             	cmp    %eax,%r13d
  4043d6:	74 45                	je     40441d <timer_thread+0x29d>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
  4043d8:	49 8b 57 18          	mov    0x18(%r15),%rdx
  4043dc:	48 8b 14 2a          	mov    (%rdx,%rbp,1),%rdx
  4043e0:	48 8b 4a 38          	mov    0x38(%rdx),%rcx
  4043e4:	48 89 c2             	mov    %rax,%rdx
  4043e7:	48 c1 e2 08          	shl    $0x8,%rdx
  4043eb:	48 03 94 39 70 01 00 00 	add    0x170(%rcx,%rdi,1),%rdx
  4043f3:	48 8b 0a             	mov    (%rdx),%rcx
  4043f6:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
  4043fd:	4c 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9
  404404:	4c 8b 9a 80 00 00 00 	mov    0x80(%rdx),%r11
  40440b:	4d 85 c9             	test   %r9,%r9
  40440e:	0f 8f ac 00 00 00    	jg     4044c0 <timer_thread+0x340>
  404414:	4d 85 db             	test   %r11,%r11
  404417:	0f 8f a3 00 00 00    	jg     4044c0 <timer_thread+0x340>
        for (int k = 0 ; k < data->my_thread_count; k++) {
  40441d:	48 83 c0 01          	add    $0x1,%rax
  404421:	48 39 c6             	cmp    %rax,%rsi
  404424:	75 aa                	jne    4043d0 <timer_thread+0x250>
      for (int y = 0 ; y < 2 ; y++) {
  404426:	49 83 fc 01          	cmp    $0x1,%r12
  40442a:	74 14                	je     404440 <timer_thread+0x2c0>
  40442c:	41 bc 01 00 00 00    	mov    $0x1,%r12d
  404432:	45 89 e2             	mov    %r12d,%r10d
        for (int k = 0 ; k < data->my_thread_count; k++) {
  404435:	45 85 f6             	test   %r14d,%r14d
  404438:	7f 88                	jg     4043c2 <timer_thread+0x242>
  40443a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404440:	41 83 c5 01          	add    $0x1,%r13d
  404444:	45 39 f5             	cmp    %r14d,%r13d
  404447:	0f 8c 63 ff ff ff    	jl     4043b0 <timer_thread+0x230>
    if (all_empty == 1 && all_waited == 1) {
  40444d:	44 0f b6 64 24 08    	movzbl 0x8(%rsp),%r12d
    for (int k = 0 ; k < data->my_thread_count; k++) {
  404453:	45 85 f6             	test   %r14d,%r14d
  404456:	7e 42                	jle    40449a <timer_thread+0x31a>
  404458:	31 ed                	xor    %ebp,%ebp
    int all_waited = 1;
  40445a:	be 01 00 00 00       	mov    $0x1,%esi
  40445f:	49 8b 4f 18          	mov    0x18(%r15),%rcx
  404463:	41 8b 57 40          	mov    0x40(%r15),%edx
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
  404467:	4c 63 ed             	movslq %ebp,%r13
  40446a:	4a 8b 04 e9          	mov    (%rcx,%r13,8),%rax
  40446e:	48 8b 40 38          	mov    0x38(%rax),%rax
  404472:	44 8b 80 a4 01 00 00 	mov    0x1a4(%rax),%r8d
  404479:	41 39 d0             	cmp    %edx,%r8d
  40447c:	0f 8c ae 00 00 00    	jl     404530 <timer_thread+0x3b0>
  404482:	44 8b 80 a4 03 00 00 	mov    0x3a4(%rax),%r8d
  404489:	41 39 d0             	cmp    %edx,%r8d
  40448c:	7c 72                	jl     404500 <timer_thread+0x380>
    for (int k = 0 ; k < data->my_thread_count; k++) {
  40448e:	83 c5 01             	add    $0x1,%ebp
  404491:	41 39 6f 30          	cmp    %ebp,0x30(%r15)
  404495:	7f d0                	jg     404467 <timer_thread+0x2e7>
    if (all_empty == 1 && all_waited == 1) {
  404497:	41 21 f4             	and    %esi,%r12d
  40449a:	45 84 e4             	test   %r12b,%r12b
  40449d:	0f 85 ba 00 00 00    	jne    40455d <timer_thread+0x3dd>
      nanosleep(&drain , &drainrem);
  4044a3:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
  4044a8:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  4044ad:	e8 0e dc ff ff       	call   4020c0 <nanosleep@plt>
  4044b2:	44 8b 74 24 0c       	mov    0xc(%rsp),%r14d
  4044b7:	e9 52 fe ff ff       	jmp    40430e <timer_thread+0x18e>
  4044bc:	0f 1f 40 00          	nopl   0x0(%rax)
  4044c0:	8b 82 18 04 00 00    	mov    0x418(%rdx),%eax
  4044c6:	48 83 ec 08          	sub    $0x8,%rsp
  4044ca:	44 89 ea             	mov    %r13d,%edx
  4044cd:	48 89 de             	mov    %rbx,%rsi
  4044d0:	bf 01 00 00 00       	mov    $0x1,%edi
  4044d5:	50                   	push   %rax
  4044d6:	8b 81 18 04 00 00    	mov    0x418(%rcx),%eax
  4044dc:	44 89 d1             	mov    %r10d,%ecx
  4044df:	50                   	push   %rax
  4044e0:	31 c0                	xor    %eax,%eax
  4044e2:	41 53                	push   %r11
  4044e4:	e8 e7 dc ff ff       	call   4021d0 <__printf_chk@plt>
  4044e9:	48 83 c4 20          	add    $0x20,%rsp
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  4044ed:	45 8b 77 30          	mov    0x30(%r15),%r14d
            all_empty = 0;
  4044f1:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
  4044f9:	e9 28 ff ff ff       	jmp    404426 <timer_thread+0x2a6>
  4044fe:	66 90                	xchg   %ax,%ax
  404500:	48 8d 35 67 3e 00 00 	lea    0x3e67(%rip),%rsi        # 40836e <_IO_stdin_used+0x36e>
  404507:	44 89 c2             	mov    %r8d,%edx
  40450a:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
  40450c:	83 c5 01             	add    $0x1,%ebp
  40450f:	bf 01 00 00 00       	mov    $0x1,%edi
  404514:	e8 b7 dc ff ff       	call   4021d0 <__printf_chk@plt>
          all_waited = 0; 
  404519:	31 f6                	xor    %esi,%esi
    for (int k = 0 ; k < data->my_thread_count; k++) {
  40451b:	41 39 6f 30          	cmp    %ebp,0x30(%r15)
  40451f:	0f 8f 3a ff ff ff    	jg     40445f <timer_thread+0x2df>
  404525:	e9 6d ff ff ff       	jmp    404497 <timer_thread+0x317>
  40452a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  404530:	44 89 c2             	mov    %r8d,%edx
  404533:	48 8d 35 34 3e 00 00 	lea    0x3e34(%rip),%rsi        # 40836e <_IO_stdin_used+0x36e>
  40453a:	bf 01 00 00 00       	mov    $0x1,%edi
  40453f:	31 c0                	xor    %eax,%eax
  404541:	e8 8a dc ff ff       	call   4021d0 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
  404546:	49 8b 4f 18          	mov    0x18(%r15),%rcx
  40454a:	41 8b 57 40          	mov    0x40(%r15),%edx
          all_waited = 0; 
  40454e:	31 f6                	xor    %esi,%esi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
  404550:	4a 8b 04 e9          	mov    (%rcx,%r13,8),%rax
  404554:	48 8b 40 38          	mov    0x38(%rax),%rax
  404558:	e9 25 ff ff ff       	jmp    404482 <timer_thread+0x302>
  40455d:	48 8d 3d 0d 3b 00 00 	lea    0x3b0d(%rip),%rdi        # 408071 <_IO_stdin_used+0x71>
  404564:	e8 e7 da ff ff       	call   402050 <puts@plt>
  while (data->running) {
  404569:	41 8b 57 44          	mov    0x44(%r15),%edx
  40456d:	85 d2                	test   %edx,%edx
  40456f:	0f 84 c9 00 00 00    	je     40463e <timer_thread+0x4be>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  404575:	41 8b 47 2c          	mov    0x2c(%r15),%eax
  404579:	31 db                	xor    %ebx,%ebx
  40457b:	4c 8d 25 f8 3a 00 00 	lea    0x3af8(%rip),%r12        # 40807a <_IO_stdin_used+0x7a>
  404582:	4c 8d 2d 0c 3b 00 00 	lea    0x3b0c(%rip),%r13        # 408095 <_IO_stdin_used+0x95>
  404589:	85 c0                	test   %eax,%eax
  40458b:	7e 39                	jle    4045c6 <timer_thread+0x446>
  40458d:	0f 1f 00             	nopl   (%rax)
  404590:	31 c0                	xor    %eax,%eax
  404592:	89 da                	mov    %ebx,%edx
  404594:	4c 89 e6             	mov    %r12,%rsi
  404597:	bf 01 00 00 00       	mov    $0x1,%edi
  40459c:	e8 2f dc ff ff       	call   4021d0 <__printf_chk@plt>
      data->threads[x]->running = 0;
  4045a1:	49 8b 47 18          	mov    0x18(%r15),%rax
  4045a5:	48 63 eb             	movslq %ebx,%rbp
  4045a8:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
      if (data->threads[x]->type == IO) {
  4045ac:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
  4045b0:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
  4045b7:	0f 84 ae 00 00 00    	je     40466b <timer_thread+0x4eb>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  4045bd:	83 c3 01             	add    $0x1,%ebx
  4045c0:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
  4045c4:	7f ca                	jg     404590 <timer_thread+0x410>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  4045c6:	49 63 47 30          	movslq 0x30(%r15),%rax
  4045ca:	85 c0                	test   %eax,%eax
  4045cc:	7e 5c                	jle    40462a <timer_thread+0x4aa>
      for (int y = 0 ; y < data->task_count ; y++) {
  4045ce:	41 8b 57 40          	mov    0x40(%r15),%edx
  4045d2:	85 d2                	test   %edx,%edx
  4045d4:	7e 54                	jle    40462a <timer_thread+0x4aa>
  4045d6:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
  4045de:	8d 42 ff             	lea    -0x1(%rdx),%eax
        data->threads[x]->tasks[y].scheduled = 0;
  4045e1:	4d 8b 47 18          	mov    0x18(%r15),%r8
  4045e5:	31 c9                	xor    %ecx,%ecx
  4045e7:	48 c1 e0 09          	shl    $0x9,%rax
  4045eb:	48 8d b8 4c 03 00 00 	lea    0x34c(%rax),%rdi
  4045f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  4045f8:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
  4045fc:	48 8b 50 38          	mov    0x38(%rax),%rdx
  404600:	48 8d 82 4c 01 00 00 	lea    0x14c(%rdx),%rax
  404607:	48 01 fa             	add    %rdi,%rdx
  40460a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  404610:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
  404616:	48 05 00 02 00 00    	add    $0x200,%rax
  40461c:	48 39 c2             	cmp    %rax,%rdx
  40461f:	75 ef                	jne    404610 <timer_thread+0x490>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
  404621:	48 83 c1 08          	add    $0x8,%rcx
  404625:	48 39 ce             	cmp    %rcx,%rsi
  404628:	75 ce                	jne    4045f8 <timer_thread+0x478>
  40462a:	48 8d 3d 76 3a 00 00 	lea    0x3a76(%rip),%rdi        # 4080a7 <_IO_stdin_used+0xa7>
  404631:	e8 1a da ff ff       	call   402050 <puts@plt>
    data->running = 0;
  404636:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
  40463e:	48 8d 3d 69 3a 00 00 	lea    0x3a69(%rip),%rdi        # 4080ae <_IO_stdin_used+0xae>
  404645:	e8 06 da ff ff       	call   402050 <puts@plt>
}
  40464a:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  40464f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  404658:	75 40                	jne    40469a <timer_thread+0x51a>
  40465a:	48 83 c4 68          	add    $0x68,%rsp
  40465e:	31 c0                	xor    %eax,%eax
  404660:	5b                   	pop    %rbx
  404661:	5d                   	pop    %rbp
  404662:	41 5c                	pop    %r12
  404664:	41 5d                	pop    %r13
  404666:	41 5e                	pop    %r14
  404668:	41 5f                	pop    %r15
  40466a:	c3                   	ret
  40466b:	4c 89 ef             	mov    %r13,%rdi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  40466e:	83 c3 01             	add    $0x1,%ebx
  404671:	e8 da d9 ff ff       	call   402050 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
  404676:	49 8b 47 18          	mov    0x18(%r15),%rax
  40467a:	be 01 00 00 00       	mov    $0x1,%esi
  40467f:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
  404683:	8b 78 68             	mov    0x68(%rax),%edi
  404686:	e8 f5 da ff ff       	call   402180 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
  40468b:	41 3b 5f 2c          	cmp    0x2c(%r15),%ebx
  40468f:	0f 8c fb fe ff ff    	jl     404590 <timer_thread+0x410>
  404695:	e9 2c ff ff ff       	jmp    4045c6 <timer_thread+0x446>
}
  40469a:	e8 01 da ff ff       	call   4020a0 <__stack_chk_fail@plt>
  40469f:	90                   	nop

00000000004046a0 <minf>:
}
  4046a0:	39 f7                	cmp    %esi,%edi
  4046a2:	89 f0                	mov    %esi,%eax
  4046a4:	0f 4e c7             	cmovle %edi,%eax
  4046a7:	c3                   	ret
  4046a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

00000000004046b0 <maxf>:
}
  4046b0:	39 f7                	cmp    %esi,%edi
  4046b2:	89 f0                	mov    %esi,%eax
  4046b4:	0f 4d c7             	cmovge %edi,%eax
  4046b7:	c3                   	ret
  4046b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

00000000004046c0 <fatal_error>:
void fatal_error(const char *syscall) {
  4046c0:	48 83 ec 08          	sub    $0x8,%rsp
    perror(syscall);
  4046c4:	e8 67 db ff ff       	call   402230 <perror@plt>
    exit(1);
  4046c9:	bf 01 00 00 00       	mov    $0x1,%edi
  4046ce:	e8 6d db ff ff       	call   402240 <exit@plt>
  4046d3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4046de:	66 90                	xchg   %ax,%ax

00000000004046e0 <strtolower>:
void strtolower(char *str) {
  4046e0:	55                   	push   %rbp
  4046e1:	53                   	push   %rbx
  4046e2:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
  4046e6:	48 0f be 1f          	movsbq (%rdi),%rbx
  4046ea:	84 db                	test   %bl,%bl
  4046ec:	74 28                	je     404716 <strtolower+0x36>
  4046ee:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
  4046f1:	e8 da db ff ff       	call   4022d0 <__ctype_tolower_loc@plt>
  4046f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  404700:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
  404703:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
  404707:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
  40470a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
  40470d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
  404712:	84 db                	test   %bl,%bl
  404714:	75 ea                	jne    404700 <strtolower+0x20>
}
  404716:	48 83 c4 08          	add    $0x8,%rsp
  40471a:	5b                   	pop    %rbx
  40471b:	5d                   	pop    %rbp
  40471c:	c3                   	ret
  40471d:	0f 1f 00             	nopl   (%rax)

0000000000404720 <zh_malloc>:
void *zh_malloc(size_t size) {
  404720:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
  404724:	e8 67 da ff ff       	call   402190 <malloc@plt>
    if (!buf) {
  404729:	48 85 c0             	test   %rax,%rax
  40472c:	74 05                	je     404733 <zh_malloc+0x13>
}
  40472e:	48 83 c4 08          	add    $0x8,%rsp
  404732:	c3                   	ret
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
  404733:	48 8b 05 be 68 00 00 	mov    0x68be(%rip),%rax        # 40aff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  40473a:	ba 28 00 00 00       	mov    $0x28,%edx
  40473f:	be 01 00 00 00       	mov    $0x1,%esi
  404744:	48 8d 3d ed 3e 00 00 	lea    0x3eed(%rip),%rdi        # 408638 <_IO_stdin_used+0x638>
  40474b:	48 8b 08             	mov    (%rax),%rcx
  40474e:	e8 0d db ff ff       	call   402260 <fwrite@plt>
        exit(1);
  404753:	bf 01 00 00 00       	mov    $0x1,%edi
  404758:	e8 e3 da ff ff       	call   402240 <exit@plt>
  40475d:	0f 1f 00             	nopl   (%rax)

0000000000404760 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
  404760:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
  404761:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
  404766:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
  404769:	e8 62 d9 ff ff       	call   4020d0 <strrchr@plt>
    if (!dot || dot == filename)
  40476e:	48 85 c0             	test   %rax,%rax
  404771:	74 0d                	je     404780 <get_filename_ext+0x20>
  404773:	48 39 c3             	cmp    %rax,%rbx
  404776:	74 08                	je     404780 <get_filename_ext+0x20>
    return dot + 1;
  404778:	48 83 c0 01          	add    $0x1,%rax
}
  40477c:	5b                   	pop    %rbx
  40477d:	c3                   	ret
  40477e:	66 90                	xchg   %ax,%ax
        return "";
  404780:	48 8d 05 6f 39 00 00 	lea    0x396f(%rip),%rax        # 4080f6 <_IO_stdin_used+0xf6>
}
  404787:	5b                   	pop    %rbx
  404788:	c3                   	ret
  404789:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000404790 <send_headers>:
void send_headers(struct KernelThread *data, struct Buffers *buffers, const char *path, off_t len, struct iovec *iov) {
  404790:	41 55                	push   %r13
  404792:	48 89 d6             	mov    %rdx,%rsi
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404795:	ba 00 04 00 00       	mov    $0x400,%edx
  40479a:	49 89 cd             	mov    %rcx,%r13
  40479d:	41 54                	push   %r12
  return __builtin___memcpy_chk (__dest, __src, __len,
  40479f:	41 bc 31 0d 00 00    	mov    $0xd31,%r12d
  4047a5:	55                   	push   %rbp
  4047a6:	53                   	push   %rbx
  4047a7:	4c 89 c3             	mov    %r8,%rbx
  4047aa:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
  4047b1:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4047ba:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
  4047c2:	31 c0                	xor    %eax,%eax
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  4047c4:	48 89 e5             	mov    %rsp,%rbp
  4047c7:	48 89 ef             	mov    %rbp,%rdi
  4047ca:	e8 e1 d9 ff ff       	call   4021b0 <__strcpy_chk@plt>
    strtolower(small_case_path);
  4047cf:	48 89 ef             	mov    %rbp,%rdi
  4047d2:	e8 09 ff ff ff       	call   4046e0 <strtolower>
    iov[0].iov_base = zh_malloc(slen);
  4047d7:	bf 11 00 00 00       	mov    $0x11,%edi
  4047dc:	e8 3f ff ff ff       	call   404720 <zh_malloc>
    iov[0].iov_len = slen;
  4047e1:	48 c7 43 08 11 00 00 00 	movq   $0x11,0x8(%rbx)
    iov[1].iov_base = zh_malloc(slen);
  4047e9:	bf 17 00 00 00       	mov    $0x17,%edi
  return __builtin___memcpy_chk (__dest, __src, __len,
  4047ee:	66 0f 6f 05 3a 46 00 00 	movdqa 0x463a(%rip),%xmm0        # 408e30 <_IO_stdin_used+0xe30>
    iov[0].iov_base = zh_malloc(slen);
  4047f6:	48 89 03             	mov    %rax,(%rbx)
  4047f9:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
  4047fd:	0f 11 00             	movups %xmm0,(%rax)
    iov[1].iov_base = zh_malloc(slen);
  404800:	e8 1b ff ff ff       	call   404720 <zh_malloc>
    iov[1].iov_len = slen;
  404805:	48 c7 43 18 17 00 00 00 	movq   $0x17,0x18(%rbx)
  40480d:	66 0f 6f 05 2b 46 00 00 	movdqa 0x462b(%rip),%xmm0        # 408e40 <_IO_stdin_used+0xe40>
    const char *file_ext = get_filename_ext(small_case_path);
  404815:	48 89 ef             	mov    %rbp,%rdi
    iov[1].iov_base = zh_malloc(slen);
  404818:	48 89 43 10          	mov    %rax,0x10(%rbx)
  40481c:	c7 40 10 64 2f 30 2e 	movl   $0x2e302f64,0x10(%rax)
  404823:	66 44 89 60 14       	mov    %r12w,0x14(%rax)
  404828:	c6 40 16 0a          	movb   $0xa,0x16(%rax)
  40482c:	0f 11 00             	movups %xmm0,(%rax)
    const char *file_ext = get_filename_ext(small_case_path);
  40482f:	e8 2c ff ff ff       	call   404760 <get_filename_ext>
    if (strcmp("jpg", file_ext) == 0)
  404834:	48 8d 3d 89 38 00 00 	lea    0x3889(%rip),%rdi        # 4080c4 <_IO_stdin_used+0xc4>
  40483b:	48 89 c6             	mov    %rax,%rsi
    const char *file_ext = get_filename_ext(small_case_path);
  40483e:	48 89 c5             	mov    %rax,%rbp
    if (strcmp("jpg", file_ext) == 0)
  404841:	e8 ea d8 ff ff       	call   402130 <strcmp@plt>
  404846:	85 c0                	test   %eax,%eax
  404848:	0f 84 42 03 00 00    	je     404b90 <send_headers+0x400>
    if (strcmp("jpeg", file_ext) == 0)
  40484e:	48 89 ee             	mov    %rbp,%rsi
  404851:	48 8d 3d 70 38 00 00 	lea    0x3870(%rip),%rdi        # 4080c8 <_IO_stdin_used+0xc8>
  404858:	e8 d3 d8 ff ff       	call   402130 <strcmp@plt>
  40485d:	85 c0                	test   %eax,%eax
  40485f:	0f 84 eb 02 00 00    	je     404b50 <send_headers+0x3c0>
    if (strcmp("png", file_ext) == 0)
  404865:	48 89 ee             	mov    %rbp,%rsi
  404868:	48 8d 3d 5e 38 00 00 	lea    0x385e(%rip),%rdi        # 4080cd <_IO_stdin_used+0xcd>
  40486f:	e8 bc d8 ff ff       	call   402130 <strcmp@plt>
  404874:	85 c0                	test   %eax,%eax
  404876:	0f 84 04 04 00 00    	je     404c80 <send_headers+0x4f0>
    if (strcmp("gif", file_ext) == 0)
  40487c:	48 89 ee             	mov    %rbp,%rsi
  40487f:	48 8d 3d 4b 38 00 00 	lea    0x384b(%rip),%rdi        # 4080d1 <_IO_stdin_used+0xd1>
  404886:	e8 a5 d8 ff ff       	call   402130 <strcmp@plt>
  40488b:	85 c0                	test   %eax,%eax
  40488d:	0f 84 ad 03 00 00    	je     404c40 <send_headers+0x4b0>
    if (strcmp("htm", file_ext) == 0)
  404893:	48 89 ee             	mov    %rbp,%rsi
  404896:	48 8d 3d 38 38 00 00 	lea    0x3838(%rip),%rdi        # 4080d5 <_IO_stdin_used+0xd5>
  40489d:	e8 8e d8 ff ff       	call   402130 <strcmp@plt>
  4048a2:	85 c0                	test   %eax,%eax
  4048a4:	0f 84 5e 03 00 00    	je     404c08 <send_headers+0x478>
    if (strcmp("html", file_ext) == 0)
  4048aa:	48 89 ee             	mov    %rbp,%rsi
  4048ad:	48 8d 3d 81 38 00 00 	lea    0x3881(%rip),%rdi        # 408135 <_IO_stdin_used+0x135>
  4048b4:	e8 77 d8 ff ff       	call   402130 <strcmp@plt>
  4048b9:	85 c0                	test   %eax,%eax
  4048bb:	0f 84 0f 03 00 00    	je     404bd0 <send_headers+0x440>
    if (strcmp("js", file_ext) == 0)
  4048c1:	80 7d 00 6a          	cmpb   $0x6a,0x0(%rbp)
  4048c5:	75 0a                	jne    4048d1 <send_headers+0x141>
  4048c7:	80 7d 01 73          	cmpb   $0x73,0x1(%rbp)
  4048cb:	0f 84 b7 01 00 00    	je     404a88 <send_headers+0x2f8>
    if (strcmp("css", file_ext) == 0)
  4048d1:	48 89 ee             	mov    %rbp,%rsi
  4048d4:	48 8d 3d fe 37 00 00 	lea    0x37fe(%rip),%rdi        # 4080d9 <_IO_stdin_used+0xd9>
  4048db:	e8 50 d8 ff ff       	call   402130 <strcmp@plt>
  4048e0:	85 c0                	test   %eax,%eax
  4048e2:	0f 84 f8 01 00 00    	je     404ae0 <send_headers+0x350>
    if (strcmp("txt", file_ext) == 0)
  4048e8:	48 89 ee             	mov    %rbp,%rsi
  4048eb:	48 8d 3d eb 37 00 00 	lea    0x37eb(%rip),%rdi        # 4080dd <_IO_stdin_used+0xdd>
  4048f2:	e8 39 d8 ff ff       	call   402130 <strcmp@plt>
  4048f7:	85 c0                	test   %eax,%eax
  4048f9:	0f 84 11 02 00 00    	je     404b10 <send_headers+0x380>
    slen = strlen(send_buffer);
  4048ff:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
  404907:	4c 89 e7             	mov    %r12,%rdi
  40490a:	e8 81 d7 ff ff       	call   402090 <strlen@plt>
    iov[2].iov_base = zh_malloc(slen);
  40490f:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
  404912:	48 89 c5             	mov    %rax,%rbp
    iov[2].iov_base = zh_malloc(slen);
  404915:	e8 06 fe ff ff       	call   404720 <zh_malloc>
    iov[2].iov_len = slen;
  40491a:	48 89 6b 28          	mov    %rbp,0x28(%rbx)
    iov[2].iov_base = zh_malloc(slen);
  40491e:	48 89 43 20          	mov    %rax,0x20(%rbx)
  404922:	83 fd 08             	cmp    $0x8,%ebp
  404925:	73 31                	jae    404958 <send_headers+0x1c8>
  404927:	40 f6 c5 04          	test   $0x4,%bpl
  40492b:	0f 85 8f 03 00 00    	jne    404cc0 <send_headers+0x530>
  404931:	85 ed                	test   %ebp,%ebp
  404933:	74 55                	je     40498a <send_headers+0x1fa>
  404935:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
  40493d:	88 10                	mov    %dl,(%rax)
  40493f:	40 f6 c5 02          	test   $0x2,%bpl
  404943:	74 45                	je     40498a <send_headers+0x1fa>
  404945:	89 ed                	mov    %ebp,%ebp
  404947:	41 0f b7 54 2c fe    	movzwl -0x2(%r12,%rbp,1),%edx
  40494d:	66 89 54 28 fe       	mov    %dx,-0x2(%rax,%rbp,1)
  404952:	eb 36                	jmp    40498a <send_headers+0x1fa>
  404954:	0f 1f 40 00          	nopl   0x0(%rax)
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
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
  40498a:	4d 89 e8             	mov    %r13,%r8
  40498d:	48 8d 0d 4d 37 00 00 	lea    0x374d(%rip),%rcx        # 4080e1 <_IO_stdin_used+0xe1>
  404994:	4c 89 e7             	mov    %r12,%rdi
  404997:	31 c0                	xor    %eax,%eax
  404999:	ba 00 04 00 00       	mov    $0x400,%edx
  40499e:	be 01 00 00 00       	mov    $0x1,%esi
  4049a3:	e8 38 d9 ff ff       	call   4022e0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
  4049a8:	4c 89 e7             	mov    %r12,%rdi
  4049ab:	e8 e0 d6 ff ff       	call   402090 <strlen@plt>
    iov[3].iov_base = zh_malloc(slen);
  4049b0:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
  4049b3:	48 89 c5             	mov    %rax,%rbp
    iov[3].iov_base = zh_malloc(slen);
  4049b6:	e8 65 fd ff ff       	call   404720 <zh_malloc>
    iov[3].iov_len = slen;
  4049bb:	48 89 6b 38          	mov    %rbp,0x38(%rbx)
    iov[3].iov_base = zh_malloc(slen);
  4049bf:	48 89 43 30          	mov    %rax,0x30(%rbx)
  4049c3:	83 fd 08             	cmp    $0x8,%ebp
  4049c6:	73 30                	jae    4049f8 <send_headers+0x268>
  4049c8:	40 f6 c5 04          	test   $0x4,%bpl
  4049cc:	0f 85 0e 03 00 00    	jne    404ce0 <send_headers+0x550>
  4049d2:	85 ed                	test   %ebp,%ebp
  4049d4:	74 54                	je     404a2a <send_headers+0x29a>
  4049d6:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
  4049de:	88 10                	mov    %dl,(%rax)
  4049e0:	40 f6 c5 02          	test   $0x2,%bpl
  4049e4:	74 44                	je     404a2a <send_headers+0x29a>
  4049e6:	89 ed                	mov    %ebp,%ebp
  4049e8:	41 0f b7 54 2c fe    	movzwl -0x2(%r12,%rbp,1),%edx
  4049ee:	66 89 54 28 fe       	mov    %dx,-0x2(%rax,%rbp,1)
  4049f3:	eb 35                	jmp    404a2a <send_headers+0x29a>
  4049f5:	0f 1f 00             	nopl   (%rax)
  4049f8:	48 8b 94 24 00 04 00 00 	mov    0x400(%rsp),%rdx
  404a00:	48 8d 78 08          	lea    0x8(%rax),%rdi
  404a04:	4c 89 e6             	mov    %r12,%rsi
  404a07:	48 83 e7 f8          	and    $0xfffffffffffffff8,%rdi
  404a0b:	48 89 10             	mov    %rdx,(%rax)
  404a0e:	89 ea                	mov    %ebp,%edx
  404a10:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
  404a15:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
  404a1a:	48 29 f8             	sub    %rdi,%rax
  404a1d:	8d 4c 05 00          	lea    0x0(%rbp,%rax,1),%ecx
  404a21:	48 29 c6             	sub    %rax,%rsi
  404a24:	c1 e9 03             	shr    $0x3,%ecx
  404a27:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404a2a:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    iov[4].iov_base = zh_malloc(slen);
  404a2f:	bf 02 00 00 00       	mov    $0x2,%edi
  404a34:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
  404a3c:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
  404a44:	e8 d7 fc ff ff       	call   404720 <zh_malloc>
  404a49:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_len = slen;
  404a51:	48 c7 43 48 02 00 00 00 	movq   $0x2,0x48(%rbx)
    iov[4].iov_base = zh_malloc(slen);
  404a59:	48 89 43 40          	mov    %rax,0x40(%rbx)
  return __builtin___memcpy_chk (__dest, __src, __len,
  404a5d:	66 89 10             	mov    %dx,(%rax)
}
  404a60:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
  404a68:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  404a71:	0f 85 82 02 00 00    	jne    404cf9 <send_headers+0x569>
  404a77:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
  404a7e:	5b                   	pop    %rbx
  404a7f:	5d                   	pop    %rbp
  404a80:	41 5c                	pop    %r12
  404a82:	41 5d                	pop    %r13
  404a84:	c3                   	ret
  404a85:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
  404a88:	80 7d 02 00          	cmpb   $0x0,0x2(%rbp)
  404a8c:	0f 85 3f fe ff ff    	jne    4048d1 <send_headers+0x141>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  404a92:	66 0f 6f 05 d6 43 00 00 	movdqa 0x43d6(%rip),%xmm0        # 408e70 <_IO_stdin_used+0xe70>
  404a9a:	b9 0d 0a 00 00       	mov    $0xa0d,%ecx
  404a9f:	c7 84 24 20 04 00 00 72 69 70 74 	movl   $0x74706972,0x420(%rsp)
  404aaa:	66 89 8c 24 24 04 00 00 	mov    %cx,0x424(%rsp)
  404ab2:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404aba:	66 0f 6f 05 be 43 00 00 	movdqa 0x43be(%rip),%xmm0        # 408e80 <_IO_stdin_used+0xe80>
  404ac2:	c6 84 24 26 04 00 00 00 	movb   $0x0,0x426(%rsp)
  404aca:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
  404ad2:	e9 fa fd ff ff       	jmp    4048d1 <send_headers+0x141>
  404ad7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  404ae0:	66 0f 6f 05 78 43 00 00 	movdqa 0x4378(%rip),%xmm0        # 408e60 <_IO_stdin_used+0xe60>
  404ae8:	c6 84 24 18 04 00 00 00 	movb   $0x0,0x418(%rsp)
  404af0:	48 b8 78 74 2f 63 73 73 0d 0a 	movabs $0xa0d7373632f7478,%rax
  404afa:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404b02:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404b0a:	e9 d9 fd ff ff       	jmp    4048e8 <send_headers+0x158>
  404b0f:	90                   	nop
  404b10:	66 0f 6f 05 48 43 00 00 	movdqa 0x4348(%rip),%xmm0        # 408e60 <_IO_stdin_used+0xe60>
  404b18:	ba 0d 0a 00 00       	mov    $0xa0d,%edx
  404b1d:	48 b8 78 74 2f 70 6c 61 69 6e 	movabs $0x6e69616c702f7478,%rax
  404b27:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  404b2f:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404b37:	66 89 94 24 18 04 00 00 	mov    %dx,0x418(%rsp)
  404b3f:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404b47:	e9 b3 fd ff ff       	jmp    4048ff <send_headers+0x16f>
  404b4c:	0f 1f 40 00          	nopl   0x0(%rax)
  404b50:	66 0f 6f 05 f8 42 00 00 	movdqa 0x42f8(%rip),%xmm0        # 408e50 <_IO_stdin_used+0xe50>
  404b58:	41 ba 0d 0a 00 00    	mov    $0xa0d,%r10d
  404b5e:	48 b8 61 67 65 2f 6a 70 65 67 	movabs $0x6765706a2f656761,%rax
  404b68:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  404b70:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404b78:	66 44 89 94 24 18 04 00 00 	mov    %r10w,0x418(%rsp)
  404b81:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404b89:	e9 d7 fc ff ff       	jmp    404865 <send_headers+0xd5>
  404b8e:	66 90                	xchg   %ax,%ax
  404b90:	66 0f 6f 05 b8 42 00 00 	movdqa 0x42b8(%rip),%xmm0        # 408e50 <_IO_stdin_used+0xe50>
  404b98:	41 bb 0d 0a 00 00    	mov    $0xa0d,%r11d
  404b9e:	48 b8 61 67 65 2f 6a 70 65 67 	movabs $0x6765706a2f656761,%rax
  404ba8:	c6 84 24 1a 04 00 00 00 	movb   $0x0,0x41a(%rsp)
  404bb0:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404bb8:	66 44 89 9c 24 18 04 00 00 	mov    %r11w,0x418(%rsp)
  404bc1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404bc9:	e9 80 fc ff ff       	jmp    40484e <send_headers+0xbe>
  404bce:	66 90                	xchg   %ax,%ax
  404bd0:	66 0f 6f 05 88 42 00 00 	movdqa 0x4288(%rip),%xmm0        # 408e60 <_IO_stdin_used+0xe60>
  404bd8:	be 0a 00 00 00       	mov    $0xa,%esi
  404bdd:	48 b8 78 74 2f 68 74 6d 6c 0d 	movabs $0xd6c6d74682f7478,%rax
  404be7:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404bef:	66 89 b4 24 18 04 00 00 	mov    %si,0x418(%rsp)
  404bf7:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404bff:	e9 bd fc ff ff       	jmp    4048c1 <send_headers+0x131>
  404c04:	0f 1f 40 00          	nopl   0x0(%rax)
  404c08:	66 0f 6f 05 50 42 00 00 	movdqa 0x4250(%rip),%xmm0        # 408e60 <_IO_stdin_used+0xe60>
  404c10:	bf 0a 00 00 00       	mov    $0xa,%edi
  404c15:	48 b8 78 74 2f 68 74 6d 6c 0d 	movabs $0xd6c6d74682f7478,%rax
  404c1f:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404c27:	66 89 bc 24 18 04 00 00 	mov    %di,0x418(%rsp)
  404c2f:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404c37:	e9 6e fc ff ff       	jmp    4048aa <send_headers+0x11a>
  404c3c:	0f 1f 40 00          	nopl   0x0(%rax)
  404c40:	66 0f 6f 05 08 42 00 00 	movdqa 0x4208(%rip),%xmm0        # 408e50 <_IO_stdin_used+0xe50>
  404c48:	41 b8 0a 00 00 00    	mov    $0xa,%r8d
  404c4e:	48 b8 61 67 65 2f 67 69 66 0d 	movabs $0xd6669672f656761,%rax
  404c58:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404c60:	66 44 89 84 24 18 04 00 00 	mov    %r8w,0x418(%rsp)
  404c69:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404c71:	e9 1d fc ff ff       	jmp    404893 <send_headers+0x103>
  404c76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  404c80:	66 0f 6f 05 c8 41 00 00 	movdqa 0x41c8(%rip),%xmm0        # 408e50 <_IO_stdin_used+0xe50>
  404c88:	41 b9 0a 00 00 00    	mov    $0xa,%r9d
  404c8e:	48 b8 61 67 65 2f 70 6e 67 0d 	movabs $0xd676e702f656761,%rax
  404c98:	48 89 84 24 10 04 00 00 	mov    %rax,0x410(%rsp)
  404ca0:	66 44 89 8c 24 18 04 00 00 	mov    %r9w,0x418(%rsp)
  404ca9:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
  404cb1:	e9 c6 fb ff ff       	jmp    40487c <send_headers+0xec>
  404cb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
  404cc0:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
  404cc7:	89 ed                	mov    %ebp,%ebp
  404cc9:	89 10                	mov    %edx,(%rax)
  404ccb:	41 8b 54 2c fc       	mov    -0x4(%r12,%rbp,1),%edx
  404cd0:	89 54 28 fc          	mov    %edx,-0x4(%rax,%rbp,1)
  404cd4:	e9 b1 fc ff ff       	jmp    40498a <send_headers+0x1fa>
  404cd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  404ce0:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
  404ce7:	89 ed                	mov    %ebp,%ebp
  404ce9:	89 10                	mov    %edx,(%rax)
  404ceb:	41 8b 54 2c fc       	mov    -0x4(%r12,%rbp,1),%edx
  404cf0:	89 54 28 fc          	mov    %edx,-0x4(%rax,%rbp,1)
  404cf4:	e9 31 fd ff ff       	jmp    404a2a <send_headers+0x29a>
}
  404cf9:	e8 a2 d3 ff ff       	call   4020a0 <__stack_chk_fail@plt>
  404cfe:	66 90                	xchg   %ax,%ax

0000000000404d00 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
  404d00:	41 55                	push   %r13
  404d02:	41 54                	push   %r12
  404d04:	49 89 d4             	mov    %rdx,%r12
  404d07:	55                   	push   %rbp
  404d08:	48 89 fd             	mov    %rdi,%rbp
    char *buf = zh_malloc(file_size);
  404d0b:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
  404d0e:	53                   	push   %rbx
  404d0f:	48 89 f3             	mov    %rsi,%rbx
  404d12:	48 83 ec 08          	sub    $0x8,%rsp
    char *buf = zh_malloc(file_size);
  404d16:	e8 05 fa ff ff       	call   404720 <zh_malloc>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
  404d1b:	48 89 ef             	mov    %rbp,%rdi
  404d1e:	31 f6                	xor    %esi,%esi
  404d20:	49 89 c5             	mov    %rax,%r13
  404d23:	31 c0                	xor    %eax,%eax
  404d25:	e8 e6 d4 ff ff       	call   402210 <open@plt>
  404d2a:	89 c5                	mov    %eax,%ebp
    if (fd < 0)
  404d2c:	85 c0                	test   %eax,%eax
  404d2e:	78 58                	js     404d88 <copy_file_contents+0x88>
		       "the destination buffer");

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
  404d30:	48 89 da             	mov    %rbx,%rdx
  404d33:	4c 89 ee             	mov    %r13,%rsi
  404d36:	89 ef                	mov    %ebp,%edi
  404d38:	e8 d3 d3 ff ff       	call   402110 <read@plt>
    if (ret < file_size) {
  404d3d:	48 98                	cltq
  404d3f:	48 39 d8             	cmp    %rbx,%rax
  404d42:	7c 1c                	jl     404d60 <copy_file_contents+0x60>
    close(fd);
  404d44:	89 ef                	mov    %ebp,%edi
  404d46:	e8 a5 d3 ff ff       	call   4020f0 <close@plt>
    iov->iov_base = buf;
  404d4b:	4d 89 2c 24          	mov    %r13,(%r12)
    iov->iov_len = file_size;
  404d4f:	49 89 5c 24 08       	mov    %rbx,0x8(%r12)
}
  404d54:	48 83 c4 08          	add    $0x8,%rsp
  404d58:	5b                   	pop    %rbx
  404d59:	5d                   	pop    %rbp
  404d5a:	41 5c                	pop    %r12
  404d5c:	41 5d                	pop    %r13
  404d5e:	c3                   	ret
  404d5f:	90                   	nop
        fprintf(stderr, "Encountered a short read.\n");
  404d60:	48 8b 05 91 62 00 00 	mov    0x6291(%rip),%rax        # 40aff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  404d67:	ba 1a 00 00 00       	mov    $0x1a,%edx
  404d6c:	be 01 00 00 00       	mov    $0x1,%esi
  404d71:	48 8d 3d 7f 33 00 00 	lea    0x337f(%rip),%rdi        # 4080f7 <_IO_stdin_used+0xf7>
  404d78:	48 8b 08             	mov    (%rax),%rcx
  404d7b:	e8 e0 d4 ff ff       	call   402260 <fwrite@plt>
  404d80:	eb c2                	jmp    404d44 <copy_file_contents+0x44>
  404d82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        fatal_error("read");
  404d88:	48 8d 3d c8 34 00 00 	lea    0x34c8(%rip),%rdi        # 408257 <_IO_stdin_used+0x257>
  404d8f:	e8 2c f9 ff ff       	call   4046c0 <fatal_error>
  404d94:	eb 9a                	jmp    404d30 <copy_file_contents+0x30>
  404d96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000404da0 <add_read_request>:
int add_read_request(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
  404da0:	41 55                	push   %r13
  404da2:	66 0f 6e c2          	movd   %edx,%xmm0
  404da6:	66 0f 6e c9          	movd   %ecx,%xmm1
  404daa:	41 89 d5             	mov    %edx,%r13d
  404dad:	41 54                	push   %r12
  404daf:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
  404db3:	55                   	push   %rbp
  404db4:	53                   	push   %rbx
  404db5:	48 83 ec 18          	sub    $0x18,%rsp
 * Returns a vacant sqe, or NULL if we're full.
 */
static inline struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  404db9:	49 8b 00             	mov    (%r8),%rax
  404dbc:	66 0f d6 44 24 08    	movq   %xmm0,0x8(%rsp)
  404dc2:	8b 10                	mov    (%rax),%edx
	unsigned int next = sq->sqe_tail + 1;
  404dc4:	41 8b 58 44          	mov    0x44(%r8),%ebx
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
  404dc8:	41 8b 88 c0 00 00 00 	mov    0xc0(%r8),%ecx
	unsigned int next = sq->sqe_tail + 1;
  404dcf:	8d 43 01             	lea    0x1(%rbx),%eax
		shift = 1;

	if (next - head <= *sq->kring_entries) {
  404dd2:	89 c6                	mov    %eax,%esi
  404dd4:	29 d6                	sub    %edx,%esi
  404dd6:	49 8b 50 18          	mov    0x18(%r8),%rdx
  404dda:	3b 32                	cmp    (%rdx),%esi
  404ddc:	0f 87 1e d5 ff ff    	ja     402300 <add_read_request.cold>
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404de2:	49 8b 50 10          	mov    0x10(%r8),%rdx
	if (ring->flags & IORING_SETUP_SQE128)
  404de6:	c1 e9 0a             	shr    $0xa,%ecx
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
  404de9:	bf 20 00 00 00       	mov    $0x20,%edi
  404dee:	4c 89 c5             	mov    %r8,%rbp
  404df1:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404df4:	23 1a                	and    (%rdx),%ebx
		sq->sqe_tail = next;
  404df6:	41 89 40 44          	mov    %eax,0x44(%r8)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404dfa:	d3 e3                	shl    %cl,%ebx
  404dfc:	48 c1 e3 06          	shl    $0x6,%rbx
  404e00:	49 03 58 38          	add    0x38(%r8),%rbx
  404e04:	e8 87 d3 ff ff       	call   402190 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
  404e09:	be 01 00 00 00       	mov    $0x1,%esi
  404e0e:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
  404e13:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
  404e16:	e8 05 d3 ff ff       	call   402120 <calloc@plt>
    req->client_socket = client_socket;
  404e1b:	f3 0f 7e 44 24 08    	movq   0x8(%rsp),%xmm0
    req->event_type = EVENT_TYPE_READ;
  404e21:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    io_uring_submit(ring);
  404e29:	48 89 ef             	mov    %rbp,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
  404e2c:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
  404e31:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->client_socket = client_socket;
  404e36:	66 41 0f d6 44 24 08 	movq   %xmm0,0x8(%r12)
	sqe->addr3 = 0;
  404e3d:	66 0f ef c0          	pxor   %xmm0,%xmm0
    req->iov[0].iov_len = READ_SZ;
  404e41:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
	sqe->fd = fd;
  404e4a:	44 89 6b 04          	mov    %r13d,0x4(%rbx)
	sqe->user_data = (unsigned long) data;
  404e4e:	4c 89 63 20          	mov    %r12,0x20(%rbx)
	sqe->opcode = (__u8) op;
  404e52:	c7 03 01 00 00 00    	movl   $0x1,(%rbx)
	sqe->off = offset;
  404e58:	48 c7 43 08 00 00 00 00 	movq   $0x0,0x8(%rbx)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
  404e60:	48 89 43 10          	mov    %rax,0x10(%rbx)
	sqe->len = len;
  404e64:	48 c7 43 18 01 00 00 00 	movq   $0x1,0x18(%rbx)
	sqe->buf_index = 0;
  404e6c:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->addr3 = 0;
  404e74:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
    io_uring_submit(ring);
  404e78:	e8 33 d2 ff ff       	call   4020b0 <io_uring_submit@plt>
}
  404e7d:	48 83 c4 18          	add    $0x18,%rsp
  404e81:	31 c0                	xor    %eax,%eax
  404e83:	5b                   	pop    %rbx
  404e84:	5d                   	pop    %rbp
  404e85:	41 5c                	pop    %r12
  404e87:	41 5d                	pop    %r13
  404e89:	c3                   	ret
  404e8a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000404e90 <get_line>:
    for (int i = 0; i < dest_sz; i++) {
  404e90:	85 d2                	test   %edx,%edx
  404e92:	7e 3c                	jle    404ed0 <get_line+0x40>
  404e94:	8d 42 ff             	lea    -0x1(%rdx),%eax
  404e97:	48 83 c7 01          	add    $0x1,%rdi
  404e9b:	48 8d 54 06 01       	lea    0x1(%rsi,%rax,1),%rdx
  404ea0:	eb 13                	jmp    404eb5 <get_line+0x25>
  404ea2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  404ea8:	48 83 c6 01          	add    $0x1,%rsi
  404eac:	48 83 c7 01          	add    $0x1,%rdi
  404eb0:	48 39 d6             	cmp    %rdx,%rsi
  404eb3:	74 1b                	je     404ed0 <get_line+0x40>
        dest[i] = src[i];
  404eb5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
  404eb9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
  404ebb:	3c 0d                	cmp    $0xd,%al
  404ebd:	75 e9                	jne    404ea8 <get_line+0x18>
  404ebf:	80 3f 0a             	cmpb   $0xa,(%rdi)
  404ec2:	75 e4                	jne    404ea8 <get_line+0x18>
            dest[i] = '\0';
  404ec4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
  404ec7:	31 c0                	xor    %eax,%eax
}
  404ec9:	c3                   	ret
  404eca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
  404ed0:	b8 01 00 00 00       	mov    $0x1,%eax
  404ed5:	c3                   	ret
  404ed6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000404ee0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
  404ee0:	55                   	push   %rbp
  404ee1:	66 48 0f 6e c2       	movq   %rdx,%xmm0
  404ee6:	66 48 0f 6e ce       	movq   %rsi,%xmm1
  404eeb:	48 89 cd             	mov    %rcx,%rbp
  404eee:	53                   	push   %rbx
  404eef:	89 f8                	mov    %edi,%eax
  404ef1:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
  404ef5:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  404ef9:	48 8b 11             	mov    (%rcx),%rdx
  404efc:	8b 32                	mov    (%rdx),%esi
	unsigned int next = sq->sqe_tail + 1;
  404efe:	8b 59 44             	mov    0x44(%rcx),%ebx
	if (ring->flags & IORING_SETUP_SQE128)
  404f01:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int next = sq->sqe_tail + 1;
  404f07:	8d 53 01             	lea    0x1(%rbx),%edx
	if (next - head <= *sq->kring_entries) {
  404f0a:	89 d7                	mov    %edx,%edi
  404f0c:	29 f7                	sub    %esi,%edi
  404f0e:	48 8b 75 18          	mov    0x18(%rbp),%rsi
  404f12:	3b 3e                	cmp    (%rsi),%edi
  404f14:	0f 87 f0 d3 ff ff    	ja     40230a <add_accept_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404f1a:	48 8b 75 10          	mov    0x10(%rbp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  404f1e:	c1 e9 0a             	shr    $0xa,%ecx
  struct Request *req = malloc(sizeof(*req));
  404f21:	bf 10 00 00 00       	mov    $0x10,%edi
  404f26:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404f29:	23 1e                	and    (%rsi),%ebx
		sq->sqe_tail = next;
  404f2b:	89 55 44             	mov    %edx,0x44(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  404f2e:	d3 e3                	shl    %cl,%ebx
  404f30:	48 c1 e3 06          	shl    $0x6,%rbx
  404f34:	48 03 5d 38          	add    0x38(%rbp),%rbx
	sqe->opcode = (__u8) op;
  404f38:	c7 03 0d 00 00 00    	movl   $0xd,(%rbx)
	sqe->fd = fd;
  404f3e:	89 43 04             	mov    %eax,0x4(%rbx)
	sqe->buf_index = 0;
  404f41:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->len = len;
  404f49:	48 c7 43 18 00 00 00 00 	movq   $0x0,0x18(%rbx)
	sqe->off = offset;
  404f51:	0f 11 43 08          	movups %xmm0,0x8(%rbx)
	sqe->addr3 = 0;
  404f55:	66 0f ef c0          	pxor   %xmm0,%xmm0
  404f59:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
  404f5d:	e8 2e d2 ff ff       	call   402190 <malloc@plt>
  io_uring_submit(ring);
  404f62:	48 89 ef             	mov    %rbp,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
  404f65:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
  404f6b:	48 89 43 20          	mov    %rax,0x20(%rbx)
}
  404f6f:	48 83 c4 08          	add    $0x8,%rsp
  404f73:	5b                   	pop    %rbx
  404f74:	5d                   	pop    %rbp
  io_uring_submit(ring);
  404f75:	e9 36 d1 ff ff       	jmp    4020b0 <io_uring_submit@plt>
  404f7a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000404f80 <buffersend>:
  while (data->running == 1) {
  404f80:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
  404f84:	75 41                	jne    404fc7 <buffersend+0x47>
      for (int x = 0 ; x < buffers->count ; x++) {
  404f86:	44 8b 06             	mov    (%rsi),%r8d
  404f89:	45 85 c0             	test   %r8d,%r8d
  404f8c:	7e f2                	jle    404f80 <buffersend>
  404f8e:	48 8b 46 08          	mov    0x8(%rsi),%rax
  404f92:	41 83 e8 01          	sub    $0x1,%r8d
  404f96:	4f 8d 04 80          	lea    (%r8,%r8,4),%r8
  404f9a:	4e 8d 44 c0 28       	lea    0x28(%rax,%r8,8),%r8
  404f9f:	eb 10                	jmp    404fb1 <buffersend+0x31>
  404fa1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  404fa8:	48 83 c0 28          	add    $0x28,%rax
  404fac:	4c 39 c0             	cmp    %r8,%rax
  404faf:	74 cf                	je     404f80 <buffersend>
        if (buffers->buffer[x].available == 0) {
  404fb1:	44 8b 48 08          	mov    0x8(%rax),%r9d
  404fb5:	45 85 c9             	test   %r9d,%r9d
  404fb8:	75 ee                	jne    404fa8 <buffersend+0x28>
          buffers->buffer[x].data = send;
  404fba:	48 89 08             	mov    %rcx,(%rax)
          buffers->buffer[x].kind = kind;
  404fbd:	89 50 20             	mov    %edx,0x20(%rax)
          buffers->buffer[x].available = 1;
  404fc0:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
}
  404fc7:	31 c0                	xor    %eax,%eax
  404fc9:	c3                   	ret
  404fca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000404fd0 <buffersend_filter>:
int buffersend_filter(struct KernelThread *data, struct Buffers *buffers, int kind, void * send, int filter) {
  404fd0:	66 0f 6e c2          	movd   %edx,%xmm0
  404fd4:	66 41 0f 6e c8       	movd   %r8d,%xmm1
  404fd9:	49 89 f9             	mov    %rdi,%r9
  404fdc:	66 0f 62 c1          	punpckldq %xmm1,%xmm0
  while (data->running == 1) {
  404fe0:	41 83 79 44 01       	cmpl   $0x1,0x44(%r9)
  404fe5:	75 38                	jne    40501f <buffersend_filter+0x4f>
      for (int x = 0 ; x < buffers->count ; x++) {
  404fe7:	8b 3e                	mov    (%rsi),%edi
  404fe9:	85 ff                	test   %edi,%edi
  404feb:	7e f3                	jle    404fe0 <buffersend_filter+0x10>
  404fed:	48 8b 46 08          	mov    0x8(%rsi),%rax
  404ff1:	83 ef 01             	sub    $0x1,%edi
  404ff4:	48 8d 3c bf          	lea    (%rdi,%rdi,4),%rdi
  404ff8:	48 8d 7c f8 28       	lea    0x28(%rax,%rdi,8),%rdi
  404ffd:	eb 0a                	jmp    405009 <buffersend_filter+0x39>
  404fff:	90                   	nop
  405000:	48 83 c0 28          	add    $0x28,%rax
  405004:	48 39 f8             	cmp    %rdi,%rax
  405007:	74 d7                	je     404fe0 <buffersend_filter+0x10>
        if (buffers->buffer[x].available == 0) {
  405009:	8b 50 08             	mov    0x8(%rax),%edx
  40500c:	85 d2                	test   %edx,%edx
  40500e:	75 f0                	jne    405000 <buffersend_filter+0x30>
          buffers->buffer[x].data = send;
  405010:	48 89 08             	mov    %rcx,(%rax)
          buffers->buffer[x].available = 1;
  405013:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
          buffers->buffer[x].kind = kind;
  40501a:	66 0f d6 40 20       	movq   %xmm0,0x20(%rax)
}
  40501f:	31 c0                	xor    %eax,%eax
  405021:	c3                   	ret
  405022:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40502d:	0f 1f 00             	nopl   (%rax)

0000000000405030 <add_write_request>:
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
  405030:	55                   	push   %rbp
    struct Write *write = calloc(1, sizeof(struct Write));
  405031:	be 10 00 00 00       	mov    $0x10,%esi
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
  405036:	48 89 fd             	mov    %rdi,%rbp
    struct Write *write = calloc(1, sizeof(struct Write));
  405039:	bf 01 00 00 00       	mov    $0x1,%edi
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
  40503e:	53                   	push   %rbx
  40503f:	48 89 d3             	mov    %rdx,%rbx
  405042:	48 83 ec 08          	sub    $0x8,%rsp
    struct Write *write = calloc(1, sizeof(struct Write));
  405046:	e8 d5 d0 ff ff       	call   402120 <calloc@plt>
    write->client_socket = req->client_socket;
  40504b:	f3 0f 7e 43 08       	movq   0x8(%rbx),%xmm0
    req->event_type = EVENT_TYPE_WRITE;
  405050:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    if (write->client_socket == -1) {
  405056:	66 0f 7e c6          	movd   %xmm0,%esi
    write->client_socket = req->client_socket;
  40505a:	66 0f d6 40 08       	movq   %xmm0,0x8(%rax)
  40505f:	66 0f 70 c8 e5       	pshufd $0xe5,%xmm0,%xmm1
    if (write->client_socket == -1) {
  405064:	83 fe ff             	cmp    $0xffffffff,%esi
  405067:	74 33                	je     40509c <add_write_request+0x6c>
    buffersend_filter(data, &data->iomailboxes[data->other_io], IO_WRITE, write, write->sockettoken);
  405069:	48 63 b5 18 01 00 00 	movslq 0x118(%rbp),%rsi
    write->request = req;
  405070:	48 89 18             	mov    %rbx,(%rax)
    buffersend_filter(data, &data->iomailboxes[data->other_io], IO_WRITE, write, write->sockettoken);
  405073:	48 89 ef             	mov    %rbp,%rdi
  405076:	48 89 c1             	mov    %rax,%rcx
  405079:	66 41 0f 7e c8       	movd   %xmm1,%r8d
  40507e:	ba 03 00 00 00       	mov    $0x3,%edx
  405083:	48 c1 e6 04          	shl    $0x4,%rsi
  405087:	48 03 b5 10 01 00 00 	add    0x110(%rbp),%rsi
  40508e:	e8 3d ff ff ff       	call   404fd0 <buffersend_filter>
}
  405093:	48 83 c4 08          	add    $0x8,%rsp
  405097:	31 c0                	xor    %eax,%eax
  405099:	5b                   	pop    %rbx
  40509a:	5d                   	pop    %rbp
  40509b:	c3                   	ret
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  40509c:	bf 01 00 00 00       	mov    $0x1,%edi
  4050a1:	48 8d 35 c0 35 00 00 	lea    0x35c0(%rip),%rsi        # 408668 <_IO_stdin_used+0x668>
  4050a8:	31 c0                	xor    %eax,%eax
  4050aa:	e8 21 d1 ff ff       	call   4021d0 <__printf_chk@plt>
      exit(1);
  4050af:	bf 01 00 00 00       	mov    $0x1,%edi
  4050b4:	e8 87 d1 ff ff       	call   402240 <exit@plt>
  4050b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000004050c0 <_send_static_string_content>:
void _send_static_string_content(struct KernelThread *data, struct Buffers *buffers, const char *str, int client_socket, int sockettoken, struct io_uring *ring) {
  4050c0:	41 57                	push   %r15
  4050c2:	49 89 f7             	mov    %rsi,%r15
  4050c5:	41 56                	push   %r14
  4050c7:	49 89 fe             	mov    %rdi,%r14
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  4050ca:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(struct KernelThread *data, struct Buffers *buffers, const char *str, int client_socket, int sockettoken, struct io_uring *ring) {
  4050cf:	41 55                	push   %r13
  4050d1:	41 54                	push   %r12
  4050d3:	55                   	push   %rbp
  4050d4:	48 89 d5             	mov    %rdx,%rbp
  4050d7:	53                   	push   %rbx
  4050d8:	4c 89 cb             	mov    %r9,%rbx
  4050db:	48 83 ec 18          	sub    $0x18,%rsp
  4050df:	89 4c 24 0c          	mov    %ecx,0xc(%rsp)
  4050e3:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  4050e8:	e8 33 f6 ff ff       	call   404720 <zh_malloc>
    unsigned long slen = strlen(str);
  4050ed:	48 89 ef             	mov    %rbp,%rdi
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
  4050f0:	49 89 c4             	mov    %rax,%r12
    unsigned long slen = strlen(str);
  4050f3:	e8 98 cf ff ff       	call   402090 <strlen@plt>
    req->client_socket = client_socket;
  4050f8:	8b 4c 24 0c          	mov    0xc(%rsp),%ecx
    req->sockettoken = sockettoken;
  4050fc:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    req->iovec_count = 1;
  405101:	41 c7 44 24 04 01 00 00 00 	movl   $0x1,0x4(%r12)
    req->client_socket = client_socket;
  40510a:	41 89 4c 24 08       	mov    %ecx,0x8(%r12)
    req->sockettoken = sockettoken;
  40510f:	45 89 44 24 0c       	mov    %r8d,0xc(%r12)
    if (req->client_socket == -1) {
  405114:	83 f9 ff             	cmp    $0xffffffff,%ecx
  405117:	74 42                	je     40515b <_send_static_string_content+0x9b>
    req->iov[0].iov_base = zh_malloc(slen);
  405119:	48 89 c7             	mov    %rax,%rdi
  40511c:	49 89 c5             	mov    %rax,%r13
  40511f:	e8 fc f5 ff ff       	call   404720 <zh_malloc>
    req->iov[0].iov_len = slen;
  405124:	4d 89 6c 24 18       	mov    %r13,0x18(%r12)
  405129:	4c 89 ea             	mov    %r13,%rdx
  40512c:	48 89 ee             	mov    %rbp,%rsi
    req->iov[0].iov_base = zh_malloc(slen);
  40512f:	49 89 44 24 10       	mov    %rax,0x10(%r12)
  405134:	48 89 c7             	mov    %rax,%rdi
  405137:	e8 24 d0 ff ff       	call   402160 <memcpy@plt>
}
  40513c:	48 83 c4 18          	add    $0x18,%rsp
    add_write_request(data, buffers, req, ring);
  405140:	48 89 d9             	mov    %rbx,%rcx
  405143:	4c 89 e2             	mov    %r12,%rdx
}
  405146:	5b                   	pop    %rbx
    add_write_request(data, buffers, req, ring);
  405147:	4c 89 fe             	mov    %r15,%rsi
}
  40514a:	5d                   	pop    %rbp
    add_write_request(data, buffers, req, ring);
  40514b:	4c 89 f7             	mov    %r14,%rdi
}
  40514e:	41 5c                	pop    %r12
  405150:	41 5d                	pop    %r13
  405152:	41 5e                	pop    %r14
  405154:	41 5f                	pop    %r15
    add_write_request(data, buffers, req, ring);
  405156:	e9 d5 fe ff ff       	jmp    405030 <add_write_request>
  40515b:	48 8d 3d b0 2f 00 00 	lea    0x2fb0(%rip),%rdi        # 408112 <_IO_stdin_used+0x112>
  405162:	e8 e9 ce ff ff       	call   402050 <puts@plt>
      exit(1);
  405167:	bf 01 00 00 00       	mov    $0x1,%edi
  40516c:	e8 cf d0 ff ff       	call   402240 <exit@plt>
  405171:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40517c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000405180 <handle_unimplemented_method>:
    _send_static_string_content(data, buffers, unimplemented_content, client_socket, sockettoken, ring);
  405180:	48 c7 c0 18 b0 40 00 	mov    $0x40b018,%rax
  405187:	4d 89 c1             	mov    %r8,%r9
  40518a:	41 89 c8             	mov    %ecx,%r8d
  40518d:	89 d1                	mov    %edx,%ecx
  40518f:	48 8b 10             	mov    (%rax),%rdx
  405192:	e9 29 ff ff ff       	jmp    4050c0 <_send_static_string_content>
  405197:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000004051a0 <handle_http_404>:
    _send_static_string_content(data, buffers, http_404_content, client_socket, sockettoken, ring);
  4051a0:	48 c7 c0 10 b0 40 00 	mov    $0x40b010,%rax
  4051a7:	4d 89 c1             	mov    %r8,%r9
  4051aa:	41 89 c8             	mov    %ecx,%r8d
  4051ad:	89 d1                	mov    %edx,%ecx
  4051af:	48 8b 10             	mov    (%rax),%rdx
  4051b2:	e9 09 ff ff ff       	jmp    4050c0 <_send_static_string_content>
  4051b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000004051c0 <handle_get_method>:
void handle_get_method(struct KernelThread *data, struct Buffers *buffers, char *path, int client_socket, int sockettoken, struct io_uring *ring) {
  4051c0:	41 57                	push   %r15
  4051c2:	41 89 cf             	mov    %ecx,%r15d
  4051c5:	41 56                	push   %r14
  4051c7:	45 89 c6             	mov    %r8d,%r14d
  4051ca:	41 55                	push   %r13
  4051cc:	4d 89 cd             	mov    %r9,%r13
  4051cf:	41 54                	push   %r12
  4051d1:	49 89 f4             	mov    %rsi,%r12
  4051d4:	55                   	push   %rbp
  4051d5:	48 89 fd             	mov    %rdi,%rbp
    if (path[strlen(path) - 1] == '/') {
  4051d8:	48 89 d7             	mov    %rdx,%rdi
void handle_get_method(struct KernelThread *data, struct Buffers *buffers, char *path, int client_socket, int sockettoken, struct io_uring *ring) {
  4051db:	53                   	push   %rbx
  4051dc:	48 81 ec b8 04 00 00 	sub    $0x4b8,%rsp
  4051e3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4051ec:	48 89 84 24 a8 04 00 00 	mov    %rax,0x4a8(%rsp)
  4051f4:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
  4051f6:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
  4051fb:	e8 90 ce ff ff       	call   402090 <strlen@plt>
  405200:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
  405205:	48 89 c2             	mov    %rax,%rdx
  405208:	80 7c 06 ff 2f       	cmpb   $0x2f,-0x1(%rsi,%rax,1)
  40520d:	0f 84 9d 00 00 00    	je     4052b0 <handle_get_method+0xf0>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  405213:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  405218:	48 83 c2 01          	add    $0x1,%rdx
  40521c:	48 8d bc 24 a6 00 00 00 	lea    0xa6(%rsp),%rdi
  405224:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  405229:	66 89 84 24 a4 00 00 00 	mov    %ax,0xa4(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  405231:	48 8d 9c 24 a0 00 00 00 	lea    0xa0(%rsp),%rbx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  405239:	c7 84 24 a0 00 00 00 70 75 62 6c 	movl   $0x6c627570,0xa0(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  405244:	e8 f7 ce ff ff       	call   402140 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
  405249:	48 8d 74 24 10       	lea    0x10(%rsp),%rsi
  40524e:	48 89 df             	mov    %rbx,%rdi
  405251:	e8 fa ce ff ff       	call   402150 <stat@plt>
  405256:	83 f8 ff             	cmp    $0xffffffff,%eax
  405259:	74 14                	je     40526f <handle_get_method+0xaf>
        if (S_ISREG(path_stat.st_mode)) {
  40525b:	8b 44 24 28          	mov    0x28(%rsp),%eax
  40525f:	25 00 f0 00 00       	and    $0xf000,%eax
  405264:	3d 00 80 00 00       	cmp    $0x8000,%eax
  405269:	0f 84 a1 00 00 00    	je     405310 <handle_get_method+0x150>
        handle_http_404(data, buffers, client_socket, sockettoken, ring);
  40526f:	4d 89 e8             	mov    %r13,%r8
  405272:	44 89 f1             	mov    %r14d,%ecx
  405275:	44 89 fa             	mov    %r15d,%edx
  405278:	4c 89 e6             	mov    %r12,%rsi
  40527b:	48 89 ef             	mov    %rbp,%rdi
  40527e:	e8 1d ff ff ff       	call   4051a0 <handle_http_404>
}
  405283:	48 8b 84 24 a8 04 00 00 	mov    0x4a8(%rsp),%rax
  40528b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  405294:	0f 85 d9 00 00 00    	jne    405373 <handle_get_method+0x1b3>
  40529a:	48 81 c4 b8 04 00 00 	add    $0x4b8,%rsp
  4052a1:	5b                   	pop    %rbx
  4052a2:	5d                   	pop    %rbp
  4052a3:	41 5c                	pop    %r12
  4052a5:	41 5d                	pop    %r13
  4052a7:	41 5e                	pop    %r14
  4052a9:	41 5f                	pop    %r15
  4052ab:	c3                   	ret
  4052ac:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  4052b0:	b9 69 63 00 00       	mov    $0x6369,%ecx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  4052b5:	48 8d bc 24 a6 00 00 00 	lea    0xa6(%rsp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
  4052bd:	c7 84 24 a0 00 00 00 70 75 62 6c 	movl   $0x6c627570,0xa0(%rsp)
  4052c8:	48 8d 9c 24 a0 00 00 00 	lea    0xa0(%rsp),%rbx
  4052d0:	66 89 8c 24 a4 00 00 00 	mov    %cx,0xa4(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
  4052d8:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  4052dd:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  4052e2:	e8 59 ce ff ff       	call   402140 <__memcpy_chk@plt>
  4052e7:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
  4052ec:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  4052f1:	48 8d 35 37 2e 00 00 	lea    0x2e37(%rip),%rsi        # 40812f <_IO_stdin_used+0x12f>
  4052f8:	48 29 d1             	sub    %rdx,%rcx
  4052fb:	48 8d 7c 13 06       	lea    0x6(%rbx,%rdx,1),%rdi
  405300:	ba 0b 00 00 00       	mov    $0xb,%edx
  405305:	e8 36 ce ff ff       	call   402140 <__memcpy_chk@plt>
  40530a:	e9 3a ff ff ff       	jmp    405249 <handle_get_method+0x89>
  40530f:	90                   	nop
            struct Request *req = zh_malloc(sizeof(*req) + (sizeof(struct iovec) * 6));
  405310:	bf 70 00 00 00       	mov    $0x70,%edi
  405315:	e8 06 f4 ff ff       	call   404720 <zh_malloc>
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
  40531a:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
  40531f:	48 89 da             	mov    %rbx,%rdx
  405322:	4c 89 e6             	mov    %r12,%rsi
            req->client_socket = client_socket;
  405325:	44 89 78 08          	mov    %r15d,0x8(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
  405329:	4c 8d 40 10          	lea    0x10(%rax),%r8
  40532d:	48 89 ef             	mov    %rbp,%rdi
            req->sockettoken = sockettoken;
  405330:	44 89 70 0c          	mov    %r14d,0xc(%rax)
            req->iovec_count = 6;
  405334:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
  40533b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  405340:	e8 4b f4 ff ff       	call   404790 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
  405345:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
  40534a:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
  40534f:	48 89 df             	mov    %rbx,%rdi
  405352:	49 8d 51 60          	lea    0x60(%r9),%rdx
  405356:	e8 a5 f9 ff ff       	call   404d00 <copy_file_contents>
            add_write_request(data, buffers, req, ring);
  40535b:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
  405360:	4c 89 e9             	mov    %r13,%rcx
  405363:	4c 89 e6             	mov    %r12,%rsi
  405366:	48 89 ef             	mov    %rbp,%rdi
  405369:	e8 c2 fc ff ff       	call   405030 <add_write_request>
}
  40536e:	e9 10 ff ff ff       	jmp    405283 <handle_get_method+0xc3>
  405373:	e8 28 cd ff ff       	call   4020a0 <__stack_chk_fail@plt>
  405378:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000405380 <handle_http_method>:
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
  405380:	41 57                	push   %r15
  405382:	45 89 c7             	mov    %r8d,%r15d
  405385:	41 56                	push   %r14
  405387:	41 89 ce             	mov    %ecx,%r14d
  40538a:	41 55                	push   %r13
  40538c:	49 89 f5             	mov    %rsi,%r13
    method = strtok_r(method_buffer, " ", &saveptr);
  40538f:	48 8d 35 16 2d 00 00 	lea    0x2d16(%rip),%rsi        # 4080ac <_IO_stdin_used+0xac>
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
  405396:	41 54                	push   %r12
  405398:	49 89 fc             	mov    %rdi,%r12
  40539b:	48 89 d7             	mov    %rdx,%rdi
  40539e:	55                   	push   %rbp
  40539f:	53                   	push   %rbx
  4053a0:	4c 89 cb             	mov    %r9,%rbx
  4053a3:	48 83 ec 28          	sub    $0x28,%rsp
  4053a7:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4053b0:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  4053b5:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
  4053b7:	48 8d 54 24 10       	lea    0x10(%rsp),%rdx
  4053bc:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
  4053c1:	e8 3a cd ff ff       	call   402100 <strtok_r@plt>
    strtolower(method);
  4053c6:	48 89 c7             	mov    %rax,%rdi
    method = strtok_r(method_buffer, " ", &saveptr);
  4053c9:	48 89 c5             	mov    %rax,%rbp
    strtolower(method);
  4053cc:	e8 0f f3 ff ff       	call   4046e0 <strtolower>
    path = strtok_r(NULL, " ", &saveptr);
  4053d1:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
  4053d6:	31 ff                	xor    %edi,%edi
  4053d8:	48 8d 35 cd 2c 00 00 	lea    0x2ccd(%rip),%rsi        # 4080ac <_IO_stdin_used+0xac>
  4053df:	e8 1c cd ff ff       	call   402100 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
  4053e4:	48 8d 35 4f 2d 00 00 	lea    0x2d4f(%rip),%rsi        # 40813a <_IO_stdin_used+0x13a>
  4053eb:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
  4053ee:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    if (strcmp(method, "get") == 0) {
  4053f3:	e8 38 cd ff ff       	call   402130 <strcmp@plt>
  4053f8:	85 c0                	test   %eax,%eax
  4053fa:	75 3c                	jne    405438 <handle_http_method+0xb8>
        handle_get_method(data, buffers, path, client_socket, sockettoken, ring);
  4053fc:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
  405401:	49 89 d9             	mov    %rbx,%r9
  405404:	45 89 f8             	mov    %r15d,%r8d
  405407:	44 89 f1             	mov    %r14d,%ecx
  40540a:	4c 89 ee             	mov    %r13,%rsi
  40540d:	4c 89 e7             	mov    %r12,%rdi
  405410:	e8 ab fd ff ff       	call   4051c0 <handle_get_method>
}
  405415:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  40541a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  405423:	75 29                	jne    40544e <handle_http_method+0xce>
  405425:	48 83 c4 28          	add    $0x28,%rsp
  405429:	5b                   	pop    %rbx
  40542a:	5d                   	pop    %rbp
  40542b:	41 5c                	pop    %r12
  40542d:	41 5d                	pop    %r13
  40542f:	41 5e                	pop    %r14
  405431:	41 5f                	pop    %r15
  405433:	c3                   	ret
  405434:	0f 1f 40 00          	nopl   0x0(%rax)
        handle_unimplemented_method(data, buffers, client_socket, sockettoken, ring);
  405438:	49 89 d8             	mov    %rbx,%r8
  40543b:	44 89 f9             	mov    %r15d,%ecx
  40543e:	44 89 f2             	mov    %r14d,%edx
  405441:	4c 89 ee             	mov    %r13,%rsi
  405444:	4c 89 e7             	mov    %r12,%rdi
  405447:	e8 34 fd ff ff       	call   405180 <handle_unimplemented_method>
}
  40544c:	eb c7                	jmp    405415 <handle_http_method+0x95>
  40544e:	e8 4d cc ff ff       	call   4020a0 <__stack_chk_fail@plt>
  405453:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40545e:	66 90                	xchg   %ax,%ax

0000000000405460 <handle_client_request>:
int handle_client_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
  405460:	41 56                	push   %r14
  405462:	41 55                	push   %r13
  405464:	49 89 cd             	mov    %rcx,%r13
  405467:	41 54                	push   %r12
  405469:	49 89 f4             	mov    %rsi,%r12
  40546c:	55                   	push   %rbp
  40546d:	48 89 fd             	mov    %rdi,%rbp
  405470:	53                   	push   %rbx
  405471:	48 89 d3             	mov    %rdx,%rbx
  405474:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  40547b:	48 8b 7a 10          	mov    0x10(%rdx),%rdi
  40547f:	ba 00 04 00 00       	mov    $0x400,%edx
int handle_client_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
  405484:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40548d:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
  405495:	31 c0                	xor    %eax,%eax
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
  405497:	49 89 e6             	mov    %rsp,%r14
  40549a:	4c 89 f6             	mov    %r14,%rsi
  40549d:	e8 ee f9 ff ff       	call   404e90 <get_line>
  4054a2:	85 c0                	test   %eax,%eax
  4054a4:	75 3d                	jne    4054e3 <handle_client_request+0x83>
    handle_http_method(data, buffers, http_request, req->client_socket, req->sockettoken, ring);
  4054a6:	8b 4b 08             	mov    0x8(%rbx),%ecx
  4054a9:	44 8b 43 0c          	mov    0xc(%rbx),%r8d
  4054ad:	4d 89 e9             	mov    %r13,%r9
  4054b0:	4c 89 f2             	mov    %r14,%rdx
  4054b3:	4c 89 e6             	mov    %r12,%rsi
  4054b6:	48 89 ef             	mov    %rbp,%rdi
  4054b9:	e8 c2 fe ff ff       	call   405380 <handle_http_method>
}
  4054be:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
  4054c6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  4054cf:	75 3c                	jne    40550d <handle_client_request+0xad>
  4054d1:	48 81 c4 10 04 00 00 	add    $0x410,%rsp
  4054d8:	31 c0                	xor    %eax,%eax
  4054da:	5b                   	pop    %rbx
  4054db:	5d                   	pop    %rbp
  4054dc:	41 5c                	pop    %r12
  4054de:	41 5d                	pop    %r13
  4054e0:	41 5e                	pop    %r14
  4054e2:	c3                   	ret
        fprintf(stderr, "Malformed request\n");
  4054e3:	48 8b 05 0e 5b 00 00 	mov    0x5b0e(%rip),%rax        # 40aff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  4054ea:	ba 12 00 00 00       	mov    $0x12,%edx
  4054ef:	be 01 00 00 00       	mov    $0x1,%esi
  4054f4:	48 8d 3d 43 2c 00 00 	lea    0x2c43(%rip),%rdi        # 40813e <_IO_stdin_used+0x13e>
  4054fb:	48 8b 08             	mov    (%rax),%rcx
  4054fe:	e8 5d cd ff ff       	call   402260 <fwrite@plt>
        exit(1);
  405503:	bf 01 00 00 00       	mov    $0x1,%edi
  405508:	e8 33 cd ff ff       	call   402240 <exit@plt>
}
  40550d:	e8 8e cb ff ff       	call   4020a0 <__stack_chk_fail@plt>
  405512:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40551d:	0f 1f 00             	nopl   (%rax)

0000000000405520 <bufferrecv_filter>:
void * bufferrecv_filter(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking, int filter) {
  405520:	55                   	push   %rbp
  405521:	89 cd                	mov    %ecx,%ebp
  405523:	53                   	push   %rbx
  405524:	48 83 ec 08          	sub    $0x8,%rsp
  405528:	8b 4c 24 20          	mov    0x20(%rsp),%ecx
  while (data->running == 1) {
  40552c:	0f 1f 40 00          	nopl   0x0(%rax)
  405530:	83 7e 44 01          	cmpl   $0x1,0x44(%rsi)
  405534:	75 68                	jne    40559e <bufferrecv_filter+0x7e>
      for (int x = 0 ; x < buffers->count ; x++) {
  405536:	8b 02                	mov    (%rdx),%eax
  405538:	85 c0                	test   %eax,%eax
  40553a:	7e 5c                	jle    405598 <bufferrecv_filter+0x78>
  40553c:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
  405540:	83 e8 01             	sub    $0x1,%eax
  405543:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  405547:	48 8d 44 c3 28       	lea    0x28(%rbx,%rax,8),%rax
  40554c:	eb 0b                	jmp    405559 <bufferrecv_filter+0x39>
  40554e:	66 90                	xchg   %ax,%ax
  405550:	48 83 c3 28          	add    $0x28,%rbx
  405554:	48 39 c3             	cmp    %rax,%rbx
  405557:	74 3f                	je     405598 <bufferrecv_filter+0x78>
        if (buffers->buffer[x].available == 1) {
  405559:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
  40555d:	75 f1                	jne    405550 <bufferrecv_filter+0x30>
          if (buffers->buffer[x].kind == kind && buffers->buffer[x].filter == filter) {
  40555f:	39 6b 20             	cmp    %ebp,0x20(%rbx)
  405562:	75 ec                	jne    405550 <bufferrecv_filter+0x30>
  405564:	39 4b 24             	cmp    %ecx,0x24(%rbx)
  405567:	75 e7                	jne    405550 <bufferrecv_filter+0x30>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
  405569:	be 28 00 00 00       	mov    $0x28,%esi
  40556e:	bf 01 00 00 00       	mov    $0x1,%edi
  405573:	e8 a8 cb ff ff       	call   402120 <calloc@plt>
            reply->data = buffers->buffer[x].data;
  405578:	48 8b 13             	mov    (%rbx),%rdx
            reply->kind = buffers->buffer[x].kind;
  40557b:	89 68 20             	mov    %ebp,0x20(%rax)
            reply->data = buffers->buffer[x].data;
  40557e:	48 89 10             	mov    %rdx,(%rax)
            buffers->buffer[x].available = 0;
  405581:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            asm volatile ("mfence" ::: "memory");
  405588:	0f ae f0             	mfence
}
  40558b:	48 83 c4 08          	add    $0x8,%rsp
  40558f:	5b                   	pop    %rbx
  405590:	5d                   	pop    %rbp
  405591:	c3                   	ret
  405592:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
     if (nonblocking == 1) { return NULL; }
  405598:	41 83 f9 01          	cmp    $0x1,%r9d
  40559c:	75 92                	jne    405530 <bufferrecv_filter+0x10>
}
  40559e:	48 83 c4 08          	add    $0x8,%rsp
     if (nonblocking == 1) { return NULL; }
  4055a2:	31 c0                	xor    %eax,%eax
}
  4055a4:	5b                   	pop    %rbx
  4055a5:	5d                   	pop    %rbp
  4055a6:	c3                   	ret
  4055a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000004055b0 <bufferrecv>:
void * bufferrecv(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking) {
  4055b0:	55                   	push   %rbp
  4055b1:	89 cd                	mov    %ecx,%ebp
  4055b3:	53                   	push   %rbx
  4055b4:	48 83 ec 08          	sub    $0x8,%rsp
  while (data->running == 1) {
  4055b8:	83 7e 44 01          	cmpl   $0x1,0x44(%rsi)
  4055bc:	75 68                	jne    405626 <bufferrecv+0x76>
      for (int x = 0 ; x < buffers->count ; x++) {
  4055be:	8b 02                	mov    (%rdx),%eax
  4055c0:	85 c0                	test   %eax,%eax
  4055c2:	7e 5c                	jle    405620 <bufferrecv+0x70>
  4055c4:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
  4055c8:	83 e8 01             	sub    $0x1,%eax
  4055cb:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
  4055cf:	48 8d 44 c3 28       	lea    0x28(%rbx,%rax,8),%rax
  4055d4:	eb 13                	jmp    4055e9 <bufferrecv+0x39>
  4055d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  4055e0:	48 83 c3 28          	add    $0x28,%rbx
  4055e4:	48 39 c3             	cmp    %rax,%rbx
  4055e7:	74 37                	je     405620 <bufferrecv+0x70>
        if (buffers->buffer[x].available == 1) {
  4055e9:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
  4055ed:	75 f1                	jne    4055e0 <bufferrecv+0x30>
          if (buffers->buffer[x].kind == kind) {
  4055ef:	39 6b 20             	cmp    %ebp,0x20(%rbx)
  4055f2:	75 ec                	jne    4055e0 <bufferrecv+0x30>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
  4055f4:	be 28 00 00 00       	mov    $0x28,%esi
  4055f9:	bf 01 00 00 00       	mov    $0x1,%edi
  4055fe:	e8 1d cb ff ff       	call   402120 <calloc@plt>
            reply->data = buffers->buffer[x].data;
  405603:	48 8b 13             	mov    (%rbx),%rdx
            reply->kind = buffers->buffer[x].kind;
  405606:	89 68 20             	mov    %ebp,0x20(%rax)
            reply->data = buffers->buffer[x].data;
  405609:	48 89 10             	mov    %rdx,(%rax)
            buffers->buffer[x].available = 0;
  40560c:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            asm volatile ("sfence" ::: "memory");
  405613:	0f ae f8             	sfence
}
  405616:	48 83 c4 08          	add    $0x8,%rsp
  40561a:	5b                   	pop    %rbx
  40561b:	5d                   	pop    %rbp
  40561c:	c3                   	ret
  40561d:	0f 1f 00             	nopl   (%rax)
     if (nonblocking == 1) { return NULL; }
  405620:	41 83 f9 01          	cmp    $0x1,%r9d
  405624:	75 92                	jne    4055b8 <bufferrecv+0x8>
}
  405626:	48 83 c4 08          	add    $0x8,%rsp
     if (nonblocking == 1) { return NULL; }
  40562a:	31 c0                	xor    %eax,%eax
}
  40562c:	5b                   	pop    %rbx
  40562d:	5d                   	pop    %rbp
  40562e:	c3                   	ret
  40562f:	90                   	nop

0000000000405630 <wait_for_new_client>:
struct NewClientMessage * wait_for_new_client(struct KernelThread *data, int nonblocking) {
  405630:	48 83 ec 18          	sub    $0x18,%rsp
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
  405634:	48 63 97 1c 01 00 00 	movslq 0x11c(%rdi),%rdx
struct NewClientMessage * wait_for_new_client(struct KernelThread *data, int nonblocking) {
  40563b:	41 89 f1             	mov    %esi,%r9d
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
  40563e:	b9 02 00 00 00       	mov    $0x2,%ecx
struct NewClientMessage * wait_for_new_client(struct KernelThread *data, int nonblocking) {
  405643:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  40564c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  405651:	31 c0                	xor    %eax,%eax
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
  405653:	48 89 fe             	mov    %rdi,%rsi
  405656:	49 89 e0             	mov    %rsp,%r8
  405659:	48 c1 e2 04          	shl    $0x4,%rdx
  40565d:	48 03 97 10 01 00 00 	add    0x110(%rdi),%rdx
  405664:	48 8d 3d e6 2a 00 00 	lea    0x2ae6(%rip),%rdi        # 408151 <_IO_stdin_used+0x151>
  40566b:	e8 40 ff ff ff       	call   4055b0 <bufferrecv>
  if (newclient == NULL) {
  405670:	48 85 c0             	test   %rax,%rax
  405673:	74 03                	je     405678 <wait_for_new_client+0x48>
  struct NewClientMessage *newclientmsg = newclient->data;
  405675:	48 8b 00             	mov    (%rax),%rax
}
  405678:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
  40567d:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
  405686:	75 05                	jne    40568d <wait_for_new_client+0x5d>
  405688:	48 83 c4 18          	add    $0x18,%rsp
  40568c:	c3                   	ret
  40568d:	e8 0e ca ff ff       	call   4020a0 <__stack_chk_fail@plt>
  405692:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  40569d:	0f 1f 00             	nopl   (%rax)

00000000004056a0 <io_thread>:
void* io_thread(void *arg) {
  4056a0:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  4056a2:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
  4056a4:	41 56                	push   %r14
  4056a6:	41 55                	push   %r13
  4056a8:	49 89 fd             	mov    %rdi,%r13
  4056ab:	41 54                	push   %r12
  4056ad:	55                   	push   %rbp
  4056ae:	53                   	push   %rbx
  4056af:	48 81 ec 78 01 00 00 	sub    $0x178,%rsp
  struct io_uring ring = *data->ring;
  4056b6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4056bf:	48 89 84 24 68 01 00 00 	mov    %rax,0x168(%rsp)
  4056c7:	48 8b 47 60          	mov    0x60(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  4056cb:	48 8d 9c 24 90 00 00 00 	lea    0x90(%rsp),%rbx
  4056d3:	bf 00 01 00 00       	mov    $0x100,%edi
  4056d8:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
  4056db:	f3 0f 6f 20          	movdqu (%rax),%xmm4
  4056df:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
  4056e7:	f3 0f 6f 68 10       	movdqu 0x10(%rax),%xmm5
  4056ec:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
  4056f4:	f3 0f 6f 70 20       	movdqu 0x20(%rax),%xmm6
  4056f9:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
  405701:	f3 0f 6f 78 30       	movdqu 0x30(%rax),%xmm7
  405706:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
  40570e:	f3 0f 6f 48 40       	movdqu 0x40(%rax),%xmm1
  405713:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
  40571b:	f3 0f 6f 60 50       	movdqu 0x50(%rax),%xmm4
  405720:	0f 29 a4 24 e0 00 00 00 	movaps %xmm4,0xe0(%rsp)
  405728:	f3 0f 6f 68 60       	movdqu 0x60(%rax),%xmm5
  40572d:	0f 29 ac 24 f0 00 00 00 	movaps %xmm5,0xf0(%rsp)
  405735:	f3 0f 6f 70 70       	movdqu 0x70(%rax),%xmm6
  40573a:	0f 29 b4 24 00 01 00 00 	movaps %xmm6,0x100(%rsp)
  405742:	f3 0f 6f b8 80 00 00 00 	movdqu 0x80(%rax),%xmm7
  40574a:	0f 29 bc 24 10 01 00 00 	movaps %xmm7,0x110(%rsp)
  405752:	f3 0f 6f 88 90 00 00 00 	movdqu 0x90(%rax),%xmm1
  40575a:	0f 29 8c 24 20 01 00 00 	movaps %xmm1,0x120(%rsp)
  405762:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
  40576a:	0f 29 a4 24 30 01 00 00 	movaps %xmm4,0x130(%rsp)
  405772:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
  40577a:	0f 29 ac 24 40 01 00 00 	movaps %xmm5,0x140(%rsp)
  405782:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
  40578a:	0f 29 b4 24 50 01 00 00 	movaps %xmm6,0x150(%rsp)
  405792:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
  405799:	48 89 84 24 60 01 00 00 	mov    %rax,0x160(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  4057a1:	e8 ca c9 ff ff       	call   402170 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, data->_eventfd);
  4057a6:	41 8b 75 68          	mov    0x68(%r13),%esi
  4057aa:	49 8b 7d 60          	mov    0x60(%r13),%rdi
  4057ae:	e8 cd ca ff ff       	call   402280 <io_uring_register_eventfd@plt>
  if (data->io_mode == IO_MODE_RECV) {
  4057b3:	41 8b 85 0c 01 00 00 	mov    0x10c(%r13),%eax
  4057ba:	83 f8 01             	cmp    $0x1,%eax
  4057bd:	0f 84 ad 09 00 00    	je     406170 <io_thread+0xad0>
  if (data->io_mode == IO_MODE_SEND) {
  4057c3:	85 c0                	test   %eax,%eax
  4057c5:	0f 85 fd 04 00 00    	jne    405cc8 <io_thread+0x628>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4057cb:	48 8d 3d 56 2f 00 00 	lea    0x2f56(%rip),%rdi        # 408728 <_IO_stdin_used+0x728>
  4057d2:	e8 79 c8 ff ff       	call   402050 <puts@plt>
    int epollfd = epoll_create1(0);
  4057d7:	31 ff                	xor    %edi,%edi
  4057d9:	e8 e2 ca ff ff       	call   4022c0 <epoll_create1@plt>
  4057de:	89 44 24 08          	mov    %eax,0x8(%rsp)
				if (epollfd == -1) {
  4057e2:	83 f8 ff             	cmp    $0xffffffff,%eax
  4057e5:	0f 84 0f 10 00 00    	je     4067fa <io_thread+0x115a>
  4057eb:	89 c2                	mov    %eax,%edx
  4057ed:	48 8d 35 f3 29 00 00 	lea    0x29f3(%rip),%rsi        # 4081e7 <_IO_stdin_used+0x1e7>
  4057f4:	bf 01 00 00 00       	mov    $0x1,%edi
  4057f9:	31 c0                	xor    %eax,%eax
  4057fb:	e8 d0 c9 ff ff       	call   4021d0 <__printf_chk@plt>
  405800:	48 8d 3d 59 2f 00 00 	lea    0x2f59(%rip),%rdi        # 408760 <_IO_stdin_used+0x760>
  405807:	e8 44 c8 ff ff       	call   402050 <puts@plt>
  40580c:	41 8b 8d 1c 01 00 00 	mov    0x11c(%r13),%ecx
  405813:	31 c0                	xor    %eax,%eax
  405815:	49 8b 95 20 01 00 00 	mov    0x120(%r13),%rdx
  40581c:	45 8b 85 18 01 00 00 	mov    0x118(%r13),%r8d
  405823:	48 8d 35 6e 2f 00 00 	lea    0x2f6e(%rip),%rsi        # 408798 <_IO_stdin_used+0x798>
  40582a:	bf 01 00 00 00       	mov    $0x1,%edi
  40582f:	e8 9c c9 ff ff       	call   4021d0 <__printf_chk@plt>
    void * _reply = bufferrecv("waitsocketreply", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET, &reply, 0); 
  405834:	45 31 c9             	xor    %r9d,%r9d
  405837:	4c 8d 44 24 48       	lea    0x48(%rsp),%r8
  40583c:	31 c9                	xor    %ecx,%ecx
  40583e:	49 63 95 1c 01 00 00 	movslq 0x11c(%r13),%rdx
  405845:	4c 89 ee             	mov    %r13,%rsi
  405848:	48 8d 3d ad 29 00 00 	lea    0x29ad(%rip),%rdi        # 4081fc <_IO_stdin_used+0x1fc>
  40584f:	48 c1 e2 04          	shl    $0x4,%rdx
  405853:	49 03 95 10 01 00 00 	add    0x110(%r13),%rdx
  40585a:	e8 51 fd ff ff       	call   4055b0 <bufferrecv>
  40585f:	49 8b 95 20 01 00 00 	mov    0x120(%r13),%rdx
  405866:	bf 01 00 00 00       	mov    $0x1,%edi
  40586b:	48 8d 35 66 2f 00 00 	lea    0x2f66(%rip),%rsi        # 4087d8 <_IO_stdin_used+0x7d8>
    struct NewSocketMessage *msg = bufferreply->data;
  405872:	48 8b 28             	mov    (%rax),%rbp
  405875:	31 c0                	xor    %eax,%eax
  405877:	8b 4d 00             	mov    0x0(%rbp),%ecx
  40587a:	e8 51 c9 ff ff       	call   4021d0 <__printf_chk@plt>
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
  40587f:	be 04 00 00 00       	mov    $0x4,%esi
  405884:	bf 01 00 00 00       	mov    $0x1,%edi
  405889:	e8 92 c8 ff ff       	call   402120 <calloc@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
  40588e:	49 63 b5 18 01 00 00 	movslq 0x118(%r13),%rsi
  405895:	ba 01 00 00 00       	mov    $0x1,%edx
  40589a:	4c 89 ef             	mov    %r13,%rdi
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
  40589d:	48 89 c1             	mov    %rax,%rcx
    ourreply->nothing = msg->socket;
  4058a0:	8b 45 00             	mov    0x0(%rbp),%eax
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
  4058a3:	48 c1 e6 04          	shl    $0x4,%rsi
  4058a7:	49 03 b5 10 01 00 00 	add    0x110(%r13),%rsi
    ourreply->nothing = msg->socket;
  4058ae:	89 01                	mov    %eax,(%rcx)
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
  4058b0:	e8 cb f6 ff ff       	call   404f80 <buffersend>
  4058b5:	49 8b 95 20 01 00 00 	mov    0x120(%r13),%rdx
  4058bc:	48 8d 35 4d 2f 00 00 	lea    0x2f4d(%rip),%rsi        # 408810 <_IO_stdin_used+0x810>
  4058c3:	31 c0                	xor    %eax,%eax
  4058c5:	bf 01 00 00 00       	mov    $0x1,%edi
  4058ca:	e8 01 c9 ff ff       	call   4021d0 <__printf_chk@plt>
    struct NewClientMessage *newclient_message = wait_for_new_client(data, 0);
  4058cf:	31 f6                	xor    %esi,%esi
  4058d1:	4c 89 ef             	mov    %r13,%rdi
  4058d4:	e8 57 fd ff ff       	call   405630 <wait_for_new_client>
  4058d9:	49 89 c7             	mov    %rax,%r15
    if (newclient_message == NULL) {
  4058dc:	48 85 c0             	test   %rax,%rax
  4058df:	0f 84 ef 03 00 00    	je     405cd4 <io_thread+0x634>
    int new_client_socket = newclient_message->socket;
  4058e5:	44 8b 30             	mov    (%rax),%r14d
    if (new_client_socket == -1) {
  4058e8:	41 83 fe ff          	cmp    $0xffffffff,%r14d
  4058ec:	0f 84 fe 0e 00 00    	je     4067f0 <io_thread+0x1150>
  4058f2:	44 89 f2             	mov    %r14d,%edx
  4058f5:	48 8d 35 10 29 00 00 	lea    0x2910(%rip),%rsi        # 40820c <_IO_stdin_used+0x20c>
  4058fc:	bf 01 00 00 00       	mov    $0x1,%edi
  405901:	31 c0                	xor    %eax,%eax
  405903:	e8 c8 c8 ff ff       	call   4021d0 <__printf_chk@plt>
    struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
  405908:	be 0c 00 00 00       	mov    $0xc,%esi
  40590d:	bf 01 00 00 00       	mov    $0x1,%edi
  405912:	e8 09 c8 ff ff       	call   402120 <calloc@plt>
    struct iovec *iov = calloc(1, sizeof(struct iovec));
  405917:	be 10 00 00 00       	mov    $0x10,%esi
  40591c:	bf 01 00 00 00       	mov    $0x1,%edi
    ev->events = EPOLLOUT;
  405921:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
    ev->data.fd = new_client_socket;
  405927:	44 89 70 04          	mov    %r14d,0x4(%rax)
    struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
  40592b:	48 89 04 24          	mov    %rax,(%rsp)
    struct iovec *iov = calloc(1, sizeof(struct iovec));
  40592f:	e8 ec c7 ff ff       	call   402120 <calloc@plt>
    iov->iov_base = zh_malloc(10);
  405934:	bf 0a 00 00 00       	mov    $0xa,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
  405939:	49 89 c4             	mov    %rax,%r12
    iov->iov_base = zh_malloc(10);
  40593c:	e8 df ed ff ff       	call   404720 <zh_malloc>
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
  405941:	be 20 00 00 00       	mov    $0x20,%esi
  405946:	bf 01 00 00 00       	mov    $0x1,%edi
    iov->iov_len = 10;
  40594b:	49 c7 44 24 08 0a 00 00 00 	movq   $0xa,0x8(%r12)
    iov->iov_base = zh_malloc(10);
  405954:	49 89 04 24          	mov    %rax,(%r12)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
  405958:	e8 c3 c7 ff ff       	call   402120 <calloc@plt>
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
  40595d:	be 20 00 00 00       	mov    $0x20,%esi
  405962:	bf 01 00 00 00       	mov    $0x1,%edi
    eventfdstop->kind = 3; 
  405967:	c7 00 03 00 00 00    	movl   $0x3,(%rax)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
  40596d:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
  405972:	e8 a9 c7 ff ff       	call   402120 <calloc@plt>
    io_uring_register_eventfd(data->ring, data->dataeventfd);
  405977:	41 8b 75 6c          	mov    0x6c(%r13),%esi
  40597b:	49 8b 7d 60          	mov    0x60(%r13),%rdi
    removed->kind = 7; 
  40597f:	c7 00 07 00 00 00    	movl   $0x7,(%rax)
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
  405985:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    io_uring_register_eventfd(data->ring, data->dataeventfd);
  40598a:	e8 f1 c8 ff ff       	call   402280 <io_uring_register_eventfd@plt>
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  40598f:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
  405997:	8b 38                	mov    (%rax),%edi
	unsigned int next = sq->sqe_tail + 1;
  405999:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  4059a0:	8b 8c 24 50 01 00 00 	mov    0x150(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  4059a7:	8d 70 01             	lea    0x1(%rax),%esi
	if (next - head <= *sq->kring_entries) {
  4059aa:	41 89 f0             	mov    %esi,%r8d
  4059ad:	41 29 f8             	sub    %edi,%r8d
  4059b0:	48 8b bc 24 a8 00 00 00 	mov    0xa8(%rsp),%rdi
  4059b8:	44 3b 07             	cmp    (%rdi),%r8d
  4059bb:	0f 87 53 c9 ff ff    	ja     402314 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4059c1:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
	if (ring->flags & IORING_SETUP_SQE128)
  4059c9:	c1 e9 0a             	shr    $0xa,%ecx
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
  4059cc:	66 41 0f 6e c6       	movd   %r14d,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4059d1:	48 8b ac 24 c8 00 00 00 	mov    0xc8(%rsp),%rbp
	if (ring->flags & IORING_SETUP_SQE128)
  4059d9:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
  4059dc:	66 0f ef c9          	pxor   %xmm1,%xmm1
	sqe->off = offset;
  4059e0:	0f 16 04 24          	movhps (%rsp),%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4059e4:	23 07                	and    (%rdi),%eax
		sq->sqe_tail = next;
  4059e6:	89 b4 24 d4 00 00 00 	mov    %esi,0xd4(%rsp)
          struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
  4059ed:	bf 01 00 00 00       	mov    $0x1,%edi
  4059f2:	be 20 00 00 00       	mov    $0x20,%esi
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4059f7:	d3 e0                	shl    %cl,%eax
  4059f9:	48 c1 e0 06          	shl    $0x6,%rax
  4059fd:	48 01 c5             	add    %rax,%rbp
	sqe->fd = fd;
  405a00:	8b 44 24 08          	mov    0x8(%rsp),%eax
	sqe->opcode = (__u8) op;
  405a04:	c7 45 00 1d 00 00 00 	movl   $0x1d,0x0(%rbp)
	sqe->fd = fd;
  405a0b:	89 45 04             	mov    %eax,0x4(%rbp)
	sqe->len = len;
  405a0e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
  405a16:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
  405a1e:	0f 11 4d 30          	movups %xmm1,0x30(%rbp)
	sqe->off = offset;
  405a22:	0f 11 45 08          	movups %xmm0,0x8(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405a26:	48 89 6c 24 28       	mov    %rbp,0x28(%rsp)
  405a2b:	e8 f0 c6 ff ff       	call   402120 <calloc@plt>
          struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
  405a30:	be 18 00 00 00       	mov    $0x18,%esi
  405a35:	bf 01 00 00 00       	mov    $0x1,%edi
          readywriting->kind = 4; 
  405a3a:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
  405a40:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
          struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
  405a45:	e8 d6 c6 ff ff       	call   402120 <calloc@plt>
          rr->sockettoken = newclient_message->sockettoken; 
  405a4a:	41 8b 57 04          	mov    0x4(%r15),%edx
          readywriting->data = rr; 
  405a4e:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
          io_uring_submit(&ring);
  405a53:	48 89 df             	mov    %rbx,%rdi
          readywriting->data = rr; 
  405a56:	66 48 0f 6e c0       	movq   %rax,%xmm0
          rr->client_socket = new_client_socket; 
  405a5b:	44 89 30             	mov    %r14d,(%rax)
          readywriting->data = rr; 
  405a5e:	0f 16 04 24          	movhps (%rsp),%xmm0
          rr->sockettoken = newclient_message->sockettoken; 
  405a62:	89 50 10             	mov    %edx,0x10(%rax)
          readywriting->data = rr; 
  405a65:	0f 11 41 08          	movups %xmm0,0x8(%rcx)
	sqe->user_data = (unsigned long) data;
  405a69:	48 89 4d 20          	mov    %rcx,0x20(%rbp)
          io_uring_submit(&ring);
  405a6d:	e8 3e c6 ff ff       	call   4020b0 <io_uring_submit@plt>
    struct SendUserData *dataavailable = calloc(1, sizeof(struct SendUserData));
  405a72:	be 20 00 00 00       	mov    $0x20,%esi
  405a77:	bf 01 00 00 00       	mov    $0x1,%edi
  405a7c:	e8 9f c6 ff ff       	call   402120 <calloc@plt>
  405a81:	41 8b 55 6c          	mov    0x6c(%r13),%edx
  405a85:	bf 01 00 00 00       	mov    $0x1,%edi
  405a8a:	48 8d 35 8e 27 00 00 	lea    0x278e(%rip),%rsi        # 40821f <_IO_stdin_used+0x21f>
    dataavailable->kind = 8; 
  405a91:	c7 00 08 00 00 00    	movl   $0x8,(%rax)
    struct SendUserData *dataavailable = calloc(1, sizeof(struct SendUserData));
  405a97:	49 89 c7             	mov    %rax,%r15
  405a9a:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  405a9f:	31 c0                	xor    %eax,%eax
  405aa1:	e8 2a c7 ff ff       	call   4021d0 <__printf_chk@plt>
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  405aa6:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
  405aae:	8b 30                	mov    (%rax),%esi
	unsigned int next = sq->sqe_tail + 1;
  405ab0:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  405ab7:	8b 8c 24 50 01 00 00 	mov    0x150(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  405abe:	8d 50 01             	lea    0x1(%rax),%edx
	if (ring->flags & IORING_SETUP_SQE128)
  405ac1:	c1 e9 0a             	shr    $0xa,%ecx
	if (next - head <= *sq->kring_entries) {
  405ac4:	89 d7                	mov    %edx,%edi
	if (ring->flags & IORING_SETUP_SQE128)
  405ac6:	83 e1 01             	and    $0x1,%ecx
	if (next - head <= *sq->kring_entries) {
  405ac9:	29 f7                	sub    %esi,%edi
  405acb:	48 8b b4 24 a8 00 00 00 	mov    0xa8(%rsp),%rsi
  405ad3:	3b 3e                	cmp    (%rsi),%edi
  405ad5:	0f 87 39 c8 ff ff    	ja     402314 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405adb:	48 8b b4 24 a0 00 00 00 	mov    0xa0(%rsp),%rsi
	sqe->addr3 = 0;
  405ae3:	66 0f ef c9          	pxor   %xmm1,%xmm1
    io_uring_submit(&ring);
  405ae7:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405aea:	23 06                	and    (%rsi),%eax
		sq->sqe_tail = next;
  405aec:	89 94 24 d4 00 00 00 	mov    %edx,0xd4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405af3:	d3 e0                	shl    %cl,%eax
    io_uring_prep_readv(sqe, data->dataeventfd, iov, 1, 0);
  405af5:	41 8b 55 6c          	mov    0x6c(%r13),%edx
  405af9:	48 c1 e0 06          	shl    $0x6,%rax
  405afd:	48 03 84 24 c8 00 00 00 	add    0xc8(%rsp),%rax
	sqe->opcode = (__u8) op;
  405b05:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
  405b0b:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
  405b0e:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
  405b16:	4c 89 60 10          	mov    %r12,0x10(%rax)
	sqe->len = len;
  405b1a:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
  405b22:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  405b2a:	4c 89 78 20          	mov    %r15,0x20(%rax)
	sqe->addr3 = 0;
  405b2e:	0f 11 48 30          	movups %xmm1,0x30(%rax)
    io_uring_submit(&ring);
  405b32:	e8 79 c5 ff ff       	call   4020b0 <io_uring_submit@plt>
    while (data->running == 1) {
  405b37:	41 83 7d 44 01       	cmpl   $0x1,0x44(%r13)
  405b3c:	0f 85 7a 01 00 00    	jne    405cbc <io_thread+0x61c>
        while (data->running == 1 && ((ncm = wait_for_new_client(data, 1)) != NULL) && (new_client_socket = ncm->socket)) {
  405b42:	eb 2b                	jmp    405b6f <io_thread+0x4cf>
  405b44:	0f 1f 40 00          	nopl   0x0(%rax)
  405b48:	be 01 00 00 00       	mov    $0x1,%esi
  405b4d:	4c 89 ef             	mov    %r13,%rdi
  405b50:	e8 db fa ff ff       	call   405630 <wait_for_new_client>
  405b55:	48 89 c5             	mov    %rax,%rbp
  405b58:	48 85 c0             	test   %rax,%rax
  405b5b:	74 19                	je     405b76 <io_thread+0x4d6>
  405b5d:	44 8b 30             	mov    (%rax),%r14d
  405b60:	45 85 f6             	test   %r14d,%r14d
  405b63:	74 11                	je     405b76 <io_thread+0x4d6>
          if (new_client_socket != -1) {
  405b65:	41 83 fe ff          	cmp    $0xffffffff,%r14d
  405b69:	0f 85 91 01 00 00    	jne    405d00 <io_thread+0x660>
        while (data->running == 1 && ((ncm = wait_for_new_client(data, 1)) != NULL) && (new_client_socket = ncm->socket)) {
  405b6f:	41 83 7d 44 01       	cmpl   $0x1,0x44(%r13)
  405b74:	74 d2                	je     405b48 <io_thread+0x4a8>
        struct __kernel_timespec delay = {
  405b76:	66 0f 6f 15 a2 32 00 00 	movdqa 0x32a2(%rip),%xmm2        # 408e20 <_IO_stdin_used+0xe20>
        int ret = io_uring_wait_cqe_timeout(&ring, &cqe, &delay);
  405b7e:	48 8d 54 24 60       	lea    0x60(%rsp),%rdx
  405b83:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  405b88:	48 89 df             	mov    %rbx,%rdi
        struct __kernel_timespec delay = {
  405b8b:	0f 29 54 24 60       	movaps %xmm2,0x60(%rsp)
        int ret = io_uring_wait_cqe_timeout(&ring, &cqe, &delay);
  405b90:	e8 6b c6 ff ff       	call   402200 <io_uring_wait_cqe_timeout@plt>
        if (ret < 0) { continue; }
  405b95:	85 c0                	test   %eax,%eax
  405b97:	78 9e                	js     405b37 <io_thread+0x497>
        if (((struct SendUserData*) cqe->user_data)->kind == 3) {
  405b99:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
  405b9e:	48 8b 2a             	mov    (%rdx),%rbp
  405ba1:	8b 45 00             	mov    0x0(%rbp),%eax
  405ba4:	48 89 e9             	mov    %rbp,%rcx
  405ba7:	83 f8 03             	cmp    $0x3,%eax
  405baa:	0f 84 9f 0b 00 00    	je     40674f <io_thread+0x10af>
        if (((struct SendUserData*) cqe->user_data)->kind == 8) {
  405bb0:	83 f8 08             	cmp    $0x8,%eax
  405bb3:	0f 84 ff 02 00 00    	je     405eb8 <io_thread+0x818>
        if (((struct SendUserData*) cqe->user_data)->kind == 4) {
  405bb9:	83 f8 04             	cmp    $0x4,%eax
  405bbc:	0f 84 1c 03 00 00    	je     405ede <io_thread+0x83e>
        if (((struct SendUserData*) cqe->user_data)->kind == 5) { 
  405bc2:	83 f8 05             	cmp    $0x5,%eax
  405bc5:	0f 84 35 02 00 00    	je     405e00 <io_thread+0x760>
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
  405bcb:	83 f8 07             	cmp    $0x7,%eax
  405bce:	0f 84 cc 02 00 00    	je     405ea0 <io_thread+0x800>
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  405bd4:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
  405bdc:	8b 30                	mov    (%rax),%esi
	unsigned int next = sq->sqe_tail + 1;
  405bde:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  405be5:	8b 8c 24 50 01 00 00 	mov    0x150(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  405bec:	8d 50 01             	lea    0x1(%rax),%edx
	if (next - head <= *sq->kring_entries) {
  405bef:	89 d7                	mov    %edx,%edi
  405bf1:	29 f7                	sub    %esi,%edi
  405bf3:	48 8b b4 24 a8 00 00 00 	mov    0xa8(%rsp),%rsi
  405bfb:	3b 3e                	cmp    (%rsi),%edi
  405bfd:	0f 87 11 c7 ff ff    	ja     402314 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405c03:	48 8b b4 24 a0 00 00 00 	mov    0xa0(%rsp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  405c0b:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  405c0e:	66 0f ef db          	pxor   %xmm3,%xmm3
          io_uring_submit(&ring);
  405c12:	48 89 df             	mov    %rbx,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
  405c15:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405c18:	48 8b ac 24 c8 00 00 00 	mov    0xc8(%rsp),%rbp
  405c20:	23 06                	and    (%rsi),%eax
		sq->sqe_tail = next;
  405c22:	89 94 24 d4 00 00 00 	mov    %edx,0xd4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405c29:	d3 e0                	shl    %cl,%eax
  405c2b:	48 c1 e0 06          	shl    $0x6,%rax
  405c2f:	48 01 c5             	add    %rax,%rbp
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
  405c32:	41 8b 45 68          	mov    0x68(%r13),%eax
	sqe->opcode = (__u8) op;
  405c36:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->fd = fd;
  405c3d:	89 45 04             	mov    %eax,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
  405c40:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
	sqe->off = offset;
  405c45:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
  405c4d:	4c 89 65 10          	mov    %r12,0x10(%rbp)
	sqe->len = len;
  405c51:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
  405c59:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->user_data = (unsigned long) data;
  405c61:	48 89 45 20          	mov    %rax,0x20(%rbp)
	sqe->addr3 = 0;
  405c65:	0f 11 5d 30          	movups %xmm3,0x30(%rbp)
          io_uring_submit(&ring);
  405c69:	e8 42 c4 ff ff       	call   4020b0 <io_uring_submit@plt>
          io_uring_prep_readv(sqe, data->dataeventfd, iov, 1, 0);
  405c6e:	41 8b 45 6c          	mov    0x6c(%r13),%eax
	sqe->addr = (unsigned long) addr;
  405c72:	4c 89 65 10          	mov    %r12,0x10(%rbp)
          io_uring_submit(&ring);
  405c76:	48 89 df             	mov    %rbx,%rdi
	sqe->opcode = (__u8) op;
  405c79:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->addr3 = 0;
  405c80:	66 0f ef db          	pxor   %xmm3,%xmm3
	sqe->fd = fd;
  405c84:	89 45 04             	mov    %eax,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
  405c87:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
	sqe->off = offset;
  405c8c:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
	sqe->len = len;
  405c94:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
  405c9c:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->user_data = (unsigned long) data;
  405ca4:	48 89 45 20          	mov    %rax,0x20(%rbp)
	sqe->addr3 = 0;
  405ca8:	0f 11 5d 30          	movups %xmm3,0x30(%rbp)
  405cac:	e8 ff c3 ff ff       	call   4020b0 <io_uring_submit@plt>
    while (data->running == 1) {
  405cb1:	41 83 7d 44 01       	cmpl   $0x1,0x44(%r13)
  405cb6:	0f 84 86 fe ff ff    	je     405b42 <io_thread+0x4a2>
  405cbc:	48 8d 3d 77 25 00 00 	lea    0x2577(%rip),%rdi        # 40823a <_IO_stdin_used+0x23a>
  405cc3:	e8 88 c3 ff ff       	call   402050 <puts@plt>
  405cc8:	48 8d 3d 7a 25 00 00 	lea    0x257a(%rip),%rdi        # 408249 <_IO_stdin_used+0x249>
  405ccf:	e8 7c c3 ff ff       	call   402050 <puts@plt>
}
  405cd4:	48 8b 84 24 68 01 00 00 	mov    0x168(%rsp),%rax
  405cdc:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  405ce5:	0f 85 25 0b 00 00    	jne    406810 <io_thread+0x1170>
  405ceb:	48 81 c4 78 01 00 00 	add    $0x178,%rsp
  405cf2:	31 c0                	xor    %eax,%eax
  405cf4:	5b                   	pop    %rbx
  405cf5:	5d                   	pop    %rbp
  405cf6:	41 5c                	pop    %r12
  405cf8:	41 5d                	pop    %r13
  405cfa:	41 5e                	pop    %r14
  405cfc:	41 5f                	pop    %r15
  405cfe:	c3                   	ret
  405cff:	90                   	nop
            struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
  405d00:	be 0c 00 00 00       	mov    $0xc,%esi
  405d05:	bf 01 00 00 00       	mov    $0x1,%edi
  405d0a:	e8 11 c4 ff ff       	call   402120 <calloc@plt>
            struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
  405d0f:	be 20 00 00 00       	mov    $0x20,%esi
  405d14:	bf 01 00 00 00       	mov    $0x1,%edi
            ev->events = EPOLLOUT;
  405d19:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
            struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
  405d1f:	49 89 c7             	mov    %rax,%r15
            ev->data.fd = new_client_socket;
  405d22:	44 89 70 04          	mov    %r14d,0x4(%rax)
            struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
  405d26:	e8 f5 c3 ff ff       	call   402120 <calloc@plt>
            readywriting->sockettoken = ncm->sockettoken;
  405d2b:	8b 6d 04             	mov    0x4(%rbp),%ebp
            struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
  405d2e:	be 18 00 00 00       	mov    $0x18,%esi
  405d33:	bf 01 00 00 00       	mov    $0x1,%edi
            readywriting->kind = 4; 
  405d38:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
            readywriting->event = ev;
  405d3e:	4c 89 78 10          	mov    %r15,0x10(%rax)
            readywriting->sockettoken = ncm->sockettoken;
  405d42:	89 68 18             	mov    %ebp,0x18(%rax)
  405d45:	48 89 04 24          	mov    %rax,(%rsp)
            struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
  405d49:	e8 d2 c3 ff ff       	call   402120 <calloc@plt>
            readywriting->data = rr; 
  405d4e:	48 8b 14 24          	mov    (%rsp),%rdx
            rr->client_socket = new_client_socket; 
  405d52:	44 89 30             	mov    %r14d,(%rax)
            rr->sockettoken = ncm->sockettoken; 
  405d55:	89 68 10             	mov    %ebp,0x10(%rax)
            readywriting->data = rr; 
  405d58:	48 89 42 08          	mov    %rax,0x8(%rdx)
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  405d5c:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
  405d64:	8b 38                	mov    (%rax),%edi
	unsigned int next = sq->sqe_tail + 1;
  405d66:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  405d6d:	8b 8c 24 50 01 00 00 	mov    0x150(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  405d74:	8d 70 01             	lea    0x1(%rax),%esi
	if (next - head <= *sq->kring_entries) {
  405d77:	41 89 f0             	mov    %esi,%r8d
  405d7a:	41 29 f8             	sub    %edi,%r8d
  405d7d:	48 8b bc 24 a8 00 00 00 	mov    0xa8(%rsp),%rdi
  405d85:	44 3b 07             	cmp    (%rdi),%r8d
  405d88:	0f 87 86 c5 ff ff    	ja     402314 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405d8e:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
	if (ring->flags & IORING_SETUP_SQE128)
  405d96:	c1 e9 0a             	shr    $0xa,%ecx
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
  405d99:	66 41 0f 6e c6       	movd   %r14d,%xmm0
	sqe->off = offset;
  405d9e:	66 49 0f 6e ff       	movq   %r15,%xmm7
	if (ring->flags & IORING_SETUP_SQE128)
  405da3:	83 e1 01             	and    $0x1,%ecx
	sqe->off = offset;
  405da6:	66 0f 6c c7          	punpcklqdq %xmm7,%xmm0
	sqe->addr3 = 0;
  405daa:	66 0f ef c9          	pxor   %xmm1,%xmm1
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405dae:	23 07                	and    (%rdi),%eax
		sq->sqe_tail = next;
  405db0:	89 b4 24 d4 00 00 00 	mov    %esi,0xd4(%rsp)
            io_uring_submit(&ring);
  405db7:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405dba:	d3 e0                	shl    %cl,%eax
	sqe->fd = fd;
  405dbc:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405dc0:	48 c1 e0 06          	shl    $0x6,%rax
  405dc4:	48 03 84 24 c8 00 00 00 	add    0xc8(%rsp),%rax
	sqe->fd = fd;
  405dcc:	89 48 04             	mov    %ecx,0x4(%rax)
	sqe->user_data = (unsigned long) data;
  405dcf:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->opcode = (__u8) op;
  405dd3:	c7 00 1d 00 00 00    	movl   $0x1d,(%rax)
	sqe->len = len;
  405dd9:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
  405de1:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->off = offset;
  405de9:	0f 11 40 08          	movups %xmm0,0x8(%rax)
	sqe->addr3 = 0;
  405ded:	0f 11 48 30          	movups %xmm1,0x30(%rax)
  405df1:	e8 ba c2 ff ff       	call   4020b0 <io_uring_submit@plt>
            clients++;
  405df6:	e9 74 fd ff ff       	jmp    405b6f <io_thread+0x4cf>
  405dfb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          struct Request *req = ((struct SendUserData *) cqe->user_data)->data;
  405e00:	4c 8b 79 08          	mov    0x8(%rcx),%r15
          if (cqe->res < 0) {
  405e04:	8b 7a 08             	mov    0x8(%rdx),%edi
              fprintf(stderr, "Async request failed: %s for event: %d\n",
  405e07:	41 8b 2f             	mov    (%r15),%ebp
          if (cqe->res < 0) {
  405e0a:	85 ff                	test   %edi,%edi
  405e0c:	0f 88 69 09 00 00    	js     40677b <io_thread+0x10db>
          switch (req->event_type) {
  405e12:	83 fd 01             	cmp    $0x1,%ebp
  405e15:	0f 84 2f 01 00 00    	je     405f4a <io_thread+0x8aa>
  405e1b:	83 fd 02             	cmp    $0x2,%ebp
  405e1e:	0f 85 2e 01 00 00    	jne    405f52 <io_thread+0x8b2>
                  io_uring_prep_epoll_ctl(sqe, epollfd, req->client_socket, EPOLL_CTL_DEL, ((struct SendUserData *) cqe->user_data)->event);
  405e24:	48 8b 41 10          	mov    0x10(%rcx),%rax
	sqe->fd = fd;
  405e28:	8b 54 24 08          	mov    0x8(%rsp),%edx
	sqe->addr3 = 0;
  405e2c:	66 0f ef ed          	pxor   %xmm5,%xmm5
                  io_uring_submit(&ring);
  405e30:	48 89 df             	mov    %rbx,%rdi
	sqe->opcode = (__u8) op;
  405e33:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
  405e38:	66 41 0f 6e 47 08    	movd   0x8(%r15),%xmm0
	sqe->off = offset;
  405e3e:	66 48 0f 6e e0       	movq   %rax,%xmm4
	sqe->user_data = (unsigned long) data;
  405e43:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
	sqe->opcode = (__u8) op;
  405e48:	c7 01 1d 00 00 00    	movl   $0x1d,(%rcx)
	sqe->off = offset;
  405e4e:	66 0f 6c c4          	punpcklqdq %xmm4,%xmm0
	sqe->fd = fd;
  405e52:	89 51 04             	mov    %edx,0x4(%rcx)
	sqe->len = len;
  405e55:	48 c7 41 18 02 00 00 00 	movq   $0x2,0x18(%rcx)
	sqe->buf_index = 0;
  405e5d:	48 c7 41 28 00 00 00 00 	movq   $0x0,0x28(%rcx)
	sqe->user_data = (unsigned long) data;
  405e65:	48 89 41 20          	mov    %rax,0x20(%rcx)
	sqe->off = offset;
  405e69:	0f 11 41 08          	movups %xmm0,0x8(%rcx)
	sqe->addr3 = 0;
  405e6d:	0f 11 69 30          	movups %xmm5,0x30(%rcx)
  405e71:	e8 3a c2 ff ff       	call   4020b0 <io_uring_submit@plt>
                  close(req->client_socket);
  405e76:	41 8b 7f 08          	mov    0x8(%r15),%edi
  405e7a:	e8 71 c2 ff ff       	call   4020f0 <close@plt>
            io_uring_cqe_seen(&ring, cqe);
  405e7f:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
	if (cqe)
  405e84:	48 85 c0             	test   %rax,%rax
  405e87:	0f 85 c5 00 00 00    	jne    405f52 <io_thread+0x8b2>
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
  405e8d:	48 8b 04 25 00 00 00 00 	mov    0x0,%rax
  405e95:	8b 00                	mov    (%rax),%eax
  405e97:	83 f8 07             	cmp    $0x7,%eax
  405e9a:	0f 85 34 fd ff ff    	jne    405bd4 <io_thread+0x534>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  405ea0:	48 8b 94 24 f8 00 00 00 	mov    0xf8(%rsp),%rdx
  405ea8:	8b 02                	mov    (%rdx),%eax
  405eaa:	83 c0 01             	add    $0x1,%eax
  405ead:	89 02                	mov    %eax,(%rdx)
}
  405eaf:	e9 20 fd ff ff       	jmp    405bd4 <io_thread+0x534>
  405eb4:	0f 1f 40 00          	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  405eb8:	48 8b 94 24 f8 00 00 00 	mov    0xf8(%rsp),%rdx
  405ec0:	8b 02                	mov    (%rdx),%eax
  405ec2:	83 c0 01             	add    $0x1,%eax
  405ec5:	89 02                	mov    %eax,(%rdx)
        if (((struct SendUserData*) cqe->user_data)->kind == 4) {
  405ec7:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
  405ecc:	48 8b 2a             	mov    (%rdx),%rbp
  405ecf:	8b 45 00             	mov    0x0(%rbp),%eax
  405ed2:	48 89 e9             	mov    %rbp,%rcx
  405ed5:	83 f8 04             	cmp    $0x4,%eax
  405ed8:	0f 85 e4 fc ff ff    	jne    405bc2 <io_thread+0x522>
          while (data->running == 1 && (send = bufferrecv_filter("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1, rr->sockettoken)) != NULL) {
  405ede:	41 83 7d 44 01       	cmpl   $0x1,0x44(%r13)
          struct ReadyWriting *rr = readywriting->data; 
  405ee3:	4c 8b 75 08          	mov    0x8(%rbp),%r14
          while (data->running == 1 && (send = bufferrecv_filter("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1, rr->sockettoken)) != NULL) {
  405ee7:	4c 8d 44 24 58       	lea    0x58(%rsp),%r8
  405eec:	4c 8d 3d 41 23 00 00 	lea    0x2341(%rip),%r15        # 408234 <_IO_stdin_used+0x234>
  405ef3:	0f 85 db fc ff ff    	jne    405bd4 <io_thread+0x534>
  405ef9:	48 89 2c 24          	mov    %rbp,(%rsp)
  405efd:	4c 89 c5             	mov    %r8,%rbp
  405f00:	41 8b 46 10          	mov    0x10(%r14),%eax
  405f04:	48 83 ec 08          	sub    $0x8,%rsp
  405f08:	b9 03 00 00 00       	mov    $0x3,%ecx
  405f0d:	49 89 e8             	mov    %rbp,%r8
  405f10:	49 63 95 1c 01 00 00 	movslq 0x11c(%r13),%rdx
  405f17:	41 b9 01 00 00 00    	mov    $0x1,%r9d
  405f1d:	4c 89 ee             	mov    %r13,%rsi
  405f20:	4c 89 ff             	mov    %r15,%rdi
  405f23:	48 c1 e2 04          	shl    $0x4,%rdx
  405f27:	49 03 95 10 01 00 00 	add    0x110(%r13),%rdx
  405f2e:	50                   	push   %rax
  405f2f:	e8 ec f5 ff ff       	call   405520 <bufferrecv_filter>
  405f34:	5a                   	pop    %rdx
  405f35:	59                   	pop    %rcx
  405f36:	48 85 c0             	test   %rax,%rax
  405f39:	75 35                	jne    405f70 <io_thread+0x8d0>
        if (((struct SendUserData*) cqe->user_data)->kind == 5) { 
  405f3b:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
  405f40:	48 8b 0a             	mov    (%rdx),%rcx
  405f43:	8b 01                	mov    (%rcx),%eax
          int ss = rr->client_socket;
  405f45:	e9 78 fc ff ff       	jmp    405bc2 <io_thread+0x522>
                  if (!cqe->res) {
  405f4a:	85 ff                	test   %edi,%edi
  405f4c:	0f 84 51 06 00 00    	je     4065a3 <io_thread+0xf03>
  405f52:	48 8b 94 24 f8 00 00 00 	mov    0xf8(%rsp),%rdx
  405f5a:	8b 02                	mov    (%rdx),%eax
  405f5c:	83 c0 01             	add    $0x1,%eax
  405f5f:	89 02                	mov    %eax,(%rdx)
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
  405f61:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
  405f66:	48 8b 00             	mov    (%rax),%rax
  405f69:	8b 00                	mov    (%rax),%eax
}
  405f6b:	e9 5b fc ff ff       	jmp    405bcb <io_thread+0x52b>
            struct Write *write = send->data;
  405f70:	48 8b 30             	mov    (%rax),%rsi
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  405f73:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
            int client_socket = write->client_socket; 
  405f7b:	44 8b 4e 08          	mov    0x8(%rsi),%r9d
  405f7f:	8b 08                	mov    (%rax),%ecx
	unsigned int next = sq->sqe_tail + 1;
  405f81:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  405f88:	8b 94 24 50 01 00 00 	mov    0x150(%rsp),%edx
	unsigned int next = sq->sqe_tail + 1;
  405f8f:	8d 78 01             	lea    0x1(%rax),%edi
	if (next - head <= *sq->kring_entries) {
  405f92:	41 89 fa             	mov    %edi,%r10d
  405f95:	41 29 ca             	sub    %ecx,%r10d
  405f98:	48 8b 8c 24 a8 00 00 00 	mov    0xa8(%rsp),%rcx
  405fa0:	44 3b 11             	cmp    (%rcx),%r10d
  405fa3:	0f 87 75 c3 ff ff    	ja     40231e <io_thread.cold+0xa>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405fa9:	48 8b 8c 24 a0 00 00 00 	mov    0xa0(%rsp),%rcx
	if (ring->flags & IORING_SETUP_SQE128)
  405fb1:	c1 ea 0a             	shr    $0xa,%edx
	sqe->addr3 = 0;
  405fb4:	66 0f ef ff          	pxor   %xmm7,%xmm7
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405fb8:	23 01                	and    (%rcx),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  405fba:	89 d1                	mov    %edx,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405fbc:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
		sq->sqe_tail = next;
  405fc4:	89 bc 24 d4 00 00 00 	mov    %edi,0xd4(%rsp)
	if (ring->flags & IORING_SETUP_SQE128)
  405fcb:	83 e1 01             	and    $0x1,%ecx
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
  405fce:	bf 01 00 00 00       	mov    $0x1,%edi
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  405fd3:	d3 e0                	shl    %cl,%eax
            struct Request *req = write->request;
  405fd5:	48 8b 0e             	mov    (%rsi),%rcx
  405fd8:	48 c1 e0 06          	shl    $0x6,%rax
  405fdc:	48 01 c2             	add    %rax,%rdx
            io_uring_prep_writev(sqe, client_socket, req->iov, req->iovec_count, 0);
  405fdf:	8b 41 04             	mov    0x4(%rcx),%eax
  405fe2:	48 8d 71 10          	lea    0x10(%rcx),%rsi
            req->event_type = EVENT_TYPE_WRITE;
  405fe6:	c7 01 02 00 00 00    	movl   $0x2,(%rcx)
	sqe->fd = fd;
  405fec:	44 89 4a 04          	mov    %r9d,0x4(%rdx)
            io_uring_prep_writev(sqe, client_socket, req->iov, req->iovec_count, 0);
  405ff0:	48 89 72 10          	mov    %rsi,0x10(%rdx)
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
  405ff4:	be 20 00 00 00       	mov    $0x20,%esi
	sqe->opcode = (__u8) op;
  405ff9:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->off = offset;
  405fff:	48 c7 42 08 00 00 00 00 	movq   $0x0,0x8(%rdx)
	sqe->len = len;
  406007:	89 42 18             	mov    %eax,0x18(%rdx)
	sqe->rw_flags = 0;
  40600a:	c7 42 1c 00 00 00 00 	movl   $0x0,0x1c(%rdx)
	sqe->buf_index = 0;
  406011:	48 c7 42 28 00 00 00 00 	movq   $0x0,0x28(%rdx)
	sqe->addr3 = 0;
  406019:	0f 11 7a 30          	movups %xmm7,0x30(%rdx)
            io_uring_prep_writev(sqe, client_socket, req->iov, req->iovec_count, 0);
  40601d:	48 89 4c 24 38       	mov    %rcx,0x38(%rsp)
  406022:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
  406027:	e8 f4 c0 ff ff       	call   402120 <calloc@plt>
            finishedwrite->data = req;
  40602c:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
  406031:	48 8b 14 24          	mov    (%rsp),%rdx
            io_uring_submit(&ring);
  406035:	48 89 df             	mov    %rbx,%rdi
            finishedwrite->kind = 5; 
  406038:	c7 00 05 00 00 00    	movl   $0x5,(%rax)
            finishedwrite->data = req;
  40603e:	66 48 0f 6e c1       	movq   %rcx,%xmm0
  406043:	0f 16 42 10          	movhps 0x10(%rdx),%xmm0
	sqe->user_data = (unsigned long) data;
  406047:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  40604c:	0f 11 40 08          	movups %xmm0,0x8(%rax)
  406050:	48 89 42 20          	mov    %rax,0x20(%rdx)
            io_uring_submit(&ring);
  406054:	e8 57 c0 ff ff       	call   4020b0 <io_uring_submit@plt>
	if (cqe)
  406059:	48 83 7c 24 50 00    	cmpq   $0x0,0x50(%rsp)
  40605f:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  406064:	74 0f                	je     406075 <io_thread+0x9d5>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  406066:	48 8b 8c 24 f8 00 00 00 	mov    0xf8(%rsp),%rcx
  40606e:	8b 01                	mov    (%rcx),%eax
  406070:	83 c0 01             	add    $0x1,%eax
  406073:	89 01                	mov    %eax,(%rcx)
  406075:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  40607a:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
  406082:	8b 38                	mov    (%rax),%edi
	unsigned int next = sq->sqe_tail + 1;
  406084:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  40608b:	8b 8c 24 50 01 00 00 	mov    0x150(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  406092:	8d 70 01             	lea    0x1(%rax),%esi
	if (next - head <= *sq->kring_entries) {
  406095:	41 89 f1             	mov    %esi,%r9d
  406098:	41 29 f9             	sub    %edi,%r9d
  40609b:	48 8b bc 24 a8 00 00 00 	mov    0xa8(%rsp),%rdi
  4060a3:	44 3b 0f             	cmp    (%rdi),%r9d
  4060a6:	0f 87 68 c2 ff ff    	ja     402314 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4060ac:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
	if (ring->flags & IORING_SETUP_SQE128)
  4060b4:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  4060b7:	66 0f ef f6          	pxor   %xmm6,%xmm6
	if (ring->flags & IORING_SETUP_SQE128)
  4060bb:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4060be:	23 07                	and    (%rdi),%eax
		sq->sqe_tail = next;
  4060c0:	89 b4 24 d4 00 00 00 	mov    %esi,0xd4(%rsp)
              io_uring_submit(&ring);
  4060c7:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  4060ca:	d3 e0                	shl    %cl,%eax
              io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
  4060cc:	41 8b 4d 68          	mov    0x68(%r13),%ecx
  4060d0:	48 c1 e0 06          	shl    $0x6,%rax
  4060d4:	48 03 84 24 c8 00 00 00 	add    0xc8(%rsp),%rax
	sqe->fd = fd;
  4060dc:	89 48 04             	mov    %ecx,0x4(%rax)
	sqe->user_data = (unsigned long) data;
  4060df:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
	sqe->opcode = (__u8) op;
  4060e4:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->user_data = (unsigned long) data;
  4060ea:	48 89 48 20          	mov    %rcx,0x20(%rax)
	sqe->off = offset;
  4060ee:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
  4060f6:	4c 89 60 10          	mov    %r12,0x10(%rax)
	sqe->len = len;
  4060fa:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
  406102:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->addr3 = 0;
  40610a:	0f 11 70 30          	movups %xmm6,0x30(%rax)
              io_uring_submit(&ring);
  40610e:	e8 9d bf ff ff       	call   4020b0 <io_uring_submit@plt>
	sqe->fd = fd;
  406113:	8b 44 24 08          	mov    0x8(%rsp),%eax
	sqe->addr3 = 0;
  406117:	66 0f ef f6          	pxor   %xmm6,%xmm6
          io_uring_submit(&ring);
  40611b:	48 89 df             	mov    %rbx,%rdi
	sqe->opcode = (__u8) op;
  40611e:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
	sqe->fd = fd;
  406123:	89 42 04             	mov    %eax,0x4(%rdx)
	sqe->user_data = (unsigned long) data;
  406126:	48 8b 04 24          	mov    (%rsp),%rax
	sqe->opcode = (__u8) op;
  40612a:	c7 02 01 00 00 00    	movl   $0x1,(%rdx)
	sqe->off = offset;
  406130:	48 c7 42 08 00 00 00 00 	movq   $0x0,0x8(%rdx)
	sqe->addr = (unsigned long) addr;
  406138:	4c 89 62 10          	mov    %r12,0x10(%rdx)
	sqe->len = len;
  40613c:	48 c7 42 18 01 00 00 00 	movq   $0x1,0x18(%rdx)
	sqe->buf_index = 0;
  406144:	48 c7 42 28 00 00 00 00 	movq   $0x0,0x28(%rdx)
	sqe->user_data = (unsigned long) data;
  40614c:	48 89 42 20          	mov    %rax,0x20(%rdx)
	sqe->addr3 = 0;
  406150:	0f 11 72 30          	movups %xmm6,0x30(%rdx)
  406154:	e8 57 bf ff ff       	call   4020b0 <io_uring_submit@plt>
          while (data->running == 1 && (send = bufferrecv_filter("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1, rr->sockettoken)) != NULL) {
  406159:	41 83 7d 44 01       	cmpl   $0x1,0x44(%r13)
  40615e:	0f 84 9c fd ff ff    	je     405f00 <io_thread+0x860>
  406164:	e9 d2 fd ff ff       	jmp    405f3b <io_thread+0x89b>
  406169:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    sock = socket(PF_INET, SOCK_STREAM, 0);
  406170:	31 d2                	xor    %edx,%edx
  406172:	be 01 00 00 00       	mov    $0x1,%esi
  406177:	bf 02 00 00 00       	mov    $0x2,%edi
  40617c:	e8 6f c1 ff ff       	call   4022f0 <socket@plt>
  406181:	89 c5                	mov    %eax,%ebp
    if (sock == -1)
  406183:	83 f8 ff             	cmp    $0xffffffff,%eax
  406186:	0f 84 4b 06 00 00    	je     4067d7 <io_thread+0x1137>
    if (setsockopt(sock,
  40618c:	48 8d 4c 24 48       	lea    0x48(%rsp),%rcx
  406191:	41 b8 04 00 00 00    	mov    $0x4,%r8d
  406197:	ba 02 00 00 00       	mov    $0x2,%edx
  40619c:	89 ef                	mov    %ebp,%edi
  40619e:	be 01 00 00 00       	mov    $0x1,%esi
    int enable = 1;
  4061a3:	c7 44 24 48 01 00 00 00 	movl   $0x1,0x48(%rsp)
    if (setsockopt(sock,
  4061ab:	e8 b0 be ff ff       	call   402060 <setsockopt@plt>
  4061b0:	85 c0                	test   %eax,%eax
  4061b2:	0f 88 26 04 00 00    	js     4065de <io_thread+0xf3e>
  return __builtin___memset_chk (__dest, __ch, __len,
  4061b8:	66 0f ef c0          	pxor   %xmm0,%xmm0
  4061bc:	48 8d 74 24 70       	lea    0x70(%rsp),%rsi
    if (bind(sock,
  4061c1:	ba 10 00 00 00       	mov    $0x10,%edx
  4061c6:	89 ef                	mov    %ebp,%edi
  4061c8:	0f 29 44 24 70       	movaps %xmm0,0x70(%rsp)
    srv_addr.sin_family = AF_INET;
  4061cd:	c7 44 24 70 02 00 18 db 	movl   $0xdb180002,0x70(%rsp)
    if (bind(sock,
  4061d5:	e8 06 c0 ff ff       	call   4021e0 <bind@plt>
  4061da:	85 c0                	test   %eax,%eax
  4061dc:	0f 88 eb 03 00 00    	js     4065cd <io_thread+0xf2d>
    if (listen(sock, 10) < 0) {
  4061e2:	be 0a 00 00 00       	mov    $0xa,%esi
  4061e7:	89 ef                	mov    %ebp,%edi
  4061e9:	e8 b2 bf ff ff       	call   4021a0 <listen@plt>
  4061ee:	85 c0                	test   %eax,%eax
  4061f0:	0f 88 f9 03 00 00    	js     4065ef <io_thread+0xf4f>
  4061f6:	89 e9                	mov    %ebp,%ecx
  4061f8:	ba db 18 00 00       	mov    $0x18db,%edx
  4061fd:	48 8d 35 8c 24 00 00 	lea    0x248c(%rip),%rsi        # 408690 <_IO_stdin_used+0x690>
  406204:	31 c0                	xor    %eax,%eax
  406206:	bf 01 00 00 00       	mov    $0x1,%edi
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  40620b:	4c 8d bc 24 80 00 00 00 	lea    0x80(%rsp),%r15
  406213:	e8 b8 bf ff ff       	call   4021d0 <__printf_chk@plt>
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
  406218:	be 04 00 00 00       	mov    $0x4,%esi
  40621d:	bf 01 00 00 00       	mov    $0x1,%edi
  406222:	e8 f9 be ff ff       	call   402120 <calloc@plt>
  406227:	49 8b 95 20 01 00 00 	mov    0x120(%r13),%rdx
  40622e:	bf 01 00 00 00       	mov    $0x1,%edi
  406233:	48 8d 35 76 24 00 00 	lea    0x2476(%rip),%rsi        # 4086b0 <_IO_stdin_used+0x6b0>
    msg->socket = sock;
  40623a:	89 28                	mov    %ebp,(%rax)
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
  40623c:	49 89 c4             	mov    %rax,%r12
  40623f:	31 c0                	xor    %eax,%eax
  406241:	e8 8a bf ff ff       	call   4021d0 <__printf_chk@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET, msg);
  406246:	4c 89 e1             	mov    %r12,%rcx
  406249:	31 d2                	xor    %edx,%edx
  40624b:	4c 89 ef             	mov    %r13,%rdi
  40624e:	49 63 b5 18 01 00 00 	movslq 0x118(%r13),%rsi
  406255:	48 c1 e6 04          	shl    $0x4,%rsi
  406259:	49 03 b5 10 01 00 00 	add    0x110(%r13),%rsi
  406260:	e8 1b ed ff ff       	call   404f80 <buffersend>
    bufferrecv("gotsocket", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply, 0);
  406265:	45 31 c9             	xor    %r9d,%r9d
  406268:	4c 8d 44 24 58       	lea    0x58(%rsp),%r8
  40626d:	4c 89 ee             	mov    %r13,%rsi
  406270:	49 63 95 1c 01 00 00 	movslq 0x11c(%r13),%rdx
  406277:	b9 01 00 00 00       	mov    $0x1,%ecx
  40627c:	48 8d 3d 0b 1f 00 00 	lea    0x1f0b(%rip),%rdi        # 40818e <_IO_stdin_used+0x18e>
  406283:	48 c1 e2 04          	shl    $0x4,%rdx
  406287:	49 03 95 10 01 00 00 	add    0x110(%r13),%rdx
  40628e:	e8 1d f3 ff ff       	call   4055b0 <bufferrecv>
  406293:	49 8b 95 20 01 00 00 	mov    0x120(%r13),%rdx
  40629a:	48 8d 35 37 24 00 00 	lea    0x2437(%rip),%rsi        # 4086d8 <_IO_stdin_used+0x6d8>
  4062a1:	31 c0                	xor    %eax,%eax
  4062a3:	bf 01 00 00 00       	mov    $0x1,%edi
  4062a8:	e8 23 bf ff ff       	call   4021d0 <__printf_chk@plt>
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  4062ad:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
  4062b2:	48 89 d9             	mov    %rbx,%rcx
  4062b5:	4c 89 fe             	mov    %r15,%rsi
  4062b8:	48 89 c2             	mov    %rax,%rdx
  4062bb:	89 ef                	mov    %ebp,%edi
  4062bd:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    socklen_t client_addr_len = sizeof(client_addr);
  4062c2:	c7 44 24 50 10 00 00 00 	movl   $0x10,0x50(%rsp)
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  4062ca:	e8 11 ec ff ff       	call   404ee0 <add_accept_request>
    struct iovec *iov = calloc(1, sizeof(struct iovec));
  4062cf:	be 10 00 00 00       	mov    $0x10,%esi
  4062d4:	bf 01 00 00 00       	mov    $0x1,%edi
  4062d9:	e8 42 be ff ff       	call   402120 <calloc@plt>
    iov->iov_base = zh_malloc(1000);
  4062de:	bf e8 03 00 00       	mov    $0x3e8,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
  4062e3:	49 89 c4             	mov    %rax,%r12
    iov->iov_base = zh_malloc(1000);
  4062e6:	e8 35 e4 ff ff       	call   404720 <zh_malloc>
    iov->iov_len = 1000;
  4062eb:	49 c7 44 24 08 e8 03 00 00 	movq   $0x3e8,0x8(%r12)
    iov->iov_base = zh_malloc(1000);
  4062f4:	49 89 04 24          	mov    %rax,(%r12)
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  4062f8:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
  406300:	8b 08                	mov    (%rax),%ecx
	unsigned int next = sq->sqe_tail + 1;
  406302:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  406309:	8b 94 24 50 01 00 00 	mov    0x150(%rsp),%edx
	unsigned int next = sq->sqe_tail + 1;
  406310:	8d 70 01             	lea    0x1(%rax),%esi
	if (next - head <= *sq->kring_entries) {
  406313:	89 f7                	mov    %esi,%edi
  406315:	29 cf                	sub    %ecx,%edi
  406317:	48 8b 8c 24 a8 00 00 00 	mov    0xa8(%rsp),%rcx
  40631f:	3b 39                	cmp    (%rcx),%edi
  406321:	0f 87 ed bf ff ff    	ja     402314 <io_thread.cold>
	if (ring->flags & IORING_SETUP_SQE128)
  406327:	c1 ea 0a             	shr    $0xa,%edx
	sqe->addr3 = 0;
  40632a:	66 0f ef c0          	pxor   %xmm0,%xmm0
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
  40632e:	4c 8d 74 24 60       	lea    0x60(%rsp),%r14
    io_uring_submit(&ring);
  406333:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  406336:	48 8b 8c 24 a0 00 00 00 	mov    0xa0(%rsp),%rcx
  40633e:	23 01                	and    (%rcx),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  406340:	89 d1                	mov    %edx,%ecx
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
  406342:	41 8b 55 68          	mov    0x68(%r13),%edx
		sq->sqe_tail = next;
  406346:	89 b4 24 d4 00 00 00 	mov    %esi,0xd4(%rsp)
	if (ring->flags & IORING_SETUP_SQE128)
  40634d:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  406350:	d3 e0                	shl    %cl,%eax
          io_uring_sqe_set_data(sqe, &data->_eventfd); 
  406352:	49 8d 4d 68          	lea    0x68(%r13),%rcx
  406356:	48 c1 e0 06          	shl    $0x6,%rax
  40635a:	48 03 84 24 c8 00 00 00 	add    0xc8(%rsp),%rax
  406362:	48 89 0c 24          	mov    %rcx,(%rsp)
	sqe->opcode = (__u8) op;
  406366:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
  40636c:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
  40636f:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
  406377:	4c 89 60 10          	mov    %r12,0x10(%rax)
	sqe->len = len;
  40637b:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
  406383:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  40638b:	48 89 48 20          	mov    %rcx,0x20(%rax)
	sqe->addr3 = 0;
  40638f:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(&ring);
  406393:	e8 18 bd ff ff       	call   4020b0 <io_uring_submit@plt>
    while (data->running == 1) {
  406398:	41 83 7d 44 01       	cmpl   $0x1,0x44(%r13)
  40639d:	0f 85 f4 01 00 00    	jne    406597 <io_thread+0xef7>
  4063a3:	4c 89 f8             	mov    %r15,%rax
  4063a6:	4d 89 ef             	mov    %r13,%r15
  4063a9:	49 89 c5             	mov    %rax,%r13
  4063ac:	e9 dd 00 00 00       	jmp    40648e <io_thread+0xdee>
  4063b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                if (!cqe->res) {
  4063b8:	85 ff                	test   %edi,%edi
  4063ba:	0f 85 5d 03 00 00    	jne    40671d <io_thread+0x107d>
                    fprintf(stderr, "Empty request!\n");
  4063c0:	48 8b 05 31 4c 00 00 	mov    0x4c31(%rip),%rax        # 40aff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  4063c7:	ba 0f 00 00 00       	mov    $0xf,%edx
  4063cc:	be 01 00 00 00       	mov    $0x1,%esi
  4063d1:	48 8d 3d e6 1d 00 00 	lea    0x1de6(%rip),%rdi        # 4081be <_IO_stdin_used+0x1be>
  4063d8:	48 8b 08             	mov    (%rax),%rcx
  4063db:	e8 80 be ff ff       	call   402260 <fwrite@plt>
          io_uring_cqe_seen(&ring, cqe);
  4063e0:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
	if (cqe)
  4063e5:	48 85 c0             	test   %rax,%rax
  4063e8:	0f 85 77 01 00 00    	jne    406565 <io_thread+0xec5>
	unsigned int head = io_uring_smp_load_acquire(sq->khead);
  4063ee:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
  4063f6:	8b 30                	mov    (%rax),%esi
	unsigned int next = sq->sqe_tail + 1;
  4063f8:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
  4063ff:	8b 8c 24 50 01 00 00 	mov    0x150(%rsp),%ecx
	unsigned int next = sq->sqe_tail + 1;
  406406:	8d 50 01             	lea    0x1(%rax),%edx
	if (next - head <= *sq->kring_entries) {
  406409:	89 d7                	mov    %edx,%edi
  40640b:	29 f7                	sub    %esi,%edi
  40640d:	48 8b b4 24 a8 00 00 00 	mov    0xa8(%rsp),%rsi
  406415:	3b 3e                	cmp    (%rsi),%edi
  406417:	0f 87 f7 be ff ff    	ja     402314 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40641d:	48 8b b4 24 a0 00 00 00 	mov    0xa0(%rsp),%rsi
	if (ring->flags & IORING_SETUP_SQE128)
  406425:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
  406428:	66 0f ef c0          	pxor   %xmm0,%xmm0
        io_uring_submit(&ring);
  40642c:	48 89 df             	mov    %rbx,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
  40642f:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  406432:	23 06                	and    (%rsi),%eax
		sq->sqe_tail = next;
  406434:	89 94 24 d4 00 00 00 	mov    %edx,0xd4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  40643b:	d3 e0                	shl    %cl,%eax
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
  40643d:	41 8b 57 68          	mov    0x68(%r15),%edx
	sqe->user_data = (unsigned long) data;
  406441:	48 8b 0c 24          	mov    (%rsp),%rcx
		sqe = &sq->sqes[(sq->sqe_tail & *sq->kring_mask) << shift];
  406445:	48 c1 e0 06          	shl    $0x6,%rax
  406449:	48 03 84 24 c8 00 00 00 	add    0xc8(%rsp),%rax
	sqe->opcode = (__u8) op;
  406451:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
  406457:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
  40645a:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
  406462:	4c 89 60 10          	mov    %r12,0x10(%rax)
	sqe->len = len;
  406466:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
  40646e:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
  406476:	48 89 48 20          	mov    %rcx,0x20(%rax)
	sqe->addr3 = 0;
  40647a:	0f 11 40 30          	movups %xmm0,0x30(%rax)
        io_uring_submit(&ring);
  40647e:	e8 2d bc ff ff       	call   4020b0 <io_uring_submit@plt>
    while (data->running == 1) {
  406483:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
  406488:	0f 85 37 03 00 00    	jne    4067c5 <io_thread+0x1125>
	unsigned mask = *ring->cq.kring_mask;
  40648e:	48 8b 84 24 08 01 00 00 	mov    0x108(%rsp),%rax
	if (ring->flags & IORING_SETUP_CQE32)
  406496:	8b 8c 24 50 01 00 00 	mov    0x150(%rsp),%ecx
	unsigned mask = *ring->cq.kring_mask;
  40649d:	8b 00                	mov    (%rax),%eax
	if (ring->flags & IORING_SETUP_CQE32)
  40649f:	c1 e9 0b             	shr    $0xb,%ecx
  4064a2:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
  4064a5:	48 8b 94 24 00 01 00 00 	mov    0x100(%rsp),%rdx
  4064ad:	8b 3a                	mov    (%rdx),%edi
		unsigned head = *ring->cq.khead;
  4064af:	48 8b b4 24 f8 00 00 00 	mov    0xf8(%rsp),%rsi
  4064b7:	8b 16                	mov    (%rsi),%edx
		if (!available)
  4064b9:	39 d7                	cmp    %edx,%edi
  4064bb:	74 39                	je     4064f6 <io_thread+0xe56>
		cqe = &ring->cq.cqes[(head & mask) << shift];
  4064bd:	89 c7                	mov    %eax,%edi
  4064bf:	21 d7                	and    %edx,%edi
  4064c1:	d3 e7                	shl    %cl,%edi
  4064c3:	48 c1 e7 04          	shl    $0x4,%rdi
  4064c7:	48 03 bc 24 28 01 00 00 	add    0x128(%rsp),%rdi
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
  4064cf:	f6 84 24 59 01 00 00 01 	testb  $0x1,0x159(%rsp)
  4064d7:	0f 85 23 01 00 00    	jne    406600 <io_thread+0xf60>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
  4064dd:	4c 8b 07             	mov    (%rdi),%r8
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
  4064e0:	49 83 f8 ff          	cmp    $0xffffffffffffffff,%r8
  4064e4:	0f 85 e3 02 00 00    	jne    4067cd <io_thread+0x112d>
			if (cqe->res < 0)
  4064ea:	8b 7f 08             	mov    0x8(%rdi),%edi
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  4064ed:	83 c2 01             	add    $0x1,%edx
  4064f0:	89 16                	mov    %edx,(%rsi)
			if (!err)
  4064f2:	85 ff                	test   %edi,%edi
  4064f4:	79 af                	jns    4064a5 <io_thread+0xe05>
	*cqe_ptr = cqe;
  4064f6:	48 c7 44 24 60 00 00 00 00 	movq   $0x0,0x60(%rsp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
  4064ff:	45 31 c0             	xor    %r8d,%r8d
  406502:	48 89 df             	mov    %rbx,%rdi
  406505:	b9 01 00 00 00       	mov    $0x1,%ecx
  40650a:	31 d2                	xor    %edx,%edx
  40650c:	4c 89 f6             	mov    %r14,%rsi
  40650f:	e8 ac bc ff ff       	call   4021c0 <__io_uring_get_cqe@plt>
        if (cqe->user_data == 1) {
  406514:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
  406519:	4c 8b 07             	mov    (%rdi),%r8
  40651c:	49 83 f8 01          	cmp    $0x1,%r8
  406520:	74 57                	je     406579 <io_thread+0xed9>
        struct Request *req = (struct Request *) cqe->user_data;
  406522:	4c 89 c2             	mov    %r8,%rdx
        if (ret < 0)
  406525:	85 c0                	test   %eax,%eax
  406527:	79 1b                	jns    406544 <io_thread+0xea4>
            fatal_error("io_uring_wait_cqe");
  406529:	48 8d 3d 7c 1c 00 00 	lea    0x1c7c(%rip),%rdi        # 4081ac <_IO_stdin_used+0x1ac>
  406530:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
  406535:	e8 86 e1 ff ff       	call   4046c0 <fatal_error>
        if (cqe->res < 0) {
  40653a:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
  40653f:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
  406544:	8b 7f 08             	mov    0x8(%rdi),%edi
            fprintf(stderr, "Async request failed: %s for event: %d\n",
  406547:	44 8b 02             	mov    (%rdx),%r8d
        if (cqe->res < 0) {
  40654a:	85 ff                	test   %edi,%edi
  40654c:	0f 88 da 00 00 00    	js     40662c <io_thread+0xf8c>
        switch (req->event_type) {
  406552:	45 85 c0             	test   %r8d,%r8d
  406555:	0f 84 22 01 00 00    	je     40667d <io_thread+0xfdd>
  40655b:	41 83 f8 01          	cmp    $0x1,%r8d
  40655f:	0f 84 53 fe ff ff    	je     4063b8 <io_thread+0xd18>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  406565:	48 8b 94 24 f8 00 00 00 	mov    0xf8(%rsp),%rdx
  40656d:	8b 02                	mov    (%rdx),%eax
  40656f:	83 c0 01             	add    $0x1,%eax
  406572:	89 02                	mov    %eax,(%rdx)
}
  406574:	e9 75 fe ff ff       	jmp    4063ee <io_thread+0xd4e>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  406579:	48 8b b4 24 f8 00 00 00 	mov    0xf8(%rsp),%rsi
  406581:	4d 89 fd             	mov    %r15,%r13
  406584:	8b 16                	mov    (%rsi),%edx
  406586:	83 c2 01             	add    $0x1,%edx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  406589:	48 8d 3d 08 1c 00 00 	lea    0x1c08(%rip),%rdi        # 408198 <_IO_stdin_used+0x198>
  406590:	89 16                	mov    %edx,(%rsi)
  406592:	e8 b9 ba ff ff       	call   402050 <puts@plt>
  if (data->io_mode == IO_MODE_SEND) {
  406597:	41 8b 85 0c 01 00 00 	mov    0x10c(%r13),%eax
  40659e:	e9 20 f2 ff ff       	jmp    4057c3 <io_thread+0x123>
                      fprintf(stderr, "Empty request!\n");
  4065a3:	48 8b 05 4e 4a 00 00 	mov    0x4a4e(%rip),%rax        # 40aff8 <stderr@GLIBC_2.2.5>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  4065aa:	ba 0f 00 00 00       	mov    $0xf,%edx
  4065af:	be 01 00 00 00       	mov    $0x1,%esi
  4065b4:	48 8d 3d 03 1c 00 00 	lea    0x1c03(%rip),%rdi        # 4081be <_IO_stdin_used+0x1be>
  4065bb:	48 8b 08             	mov    (%rax),%rcx
  4065be:	e8 9d bc ff ff       	call   402260 <fwrite@plt>
            io_uring_cqe_seen(&ring, cqe);
  4065c3:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
  4065c8:	e9 b7 f8 ff ff       	jmp    405e84 <io_thread+0x7e4>
        fatal_error("bind()");
  4065cd:	48 8d 3d aa 1b 00 00 	lea    0x1baa(%rip),%rdi        # 40817e <_IO_stdin_used+0x17e>
  4065d4:	e8 e7 e0 ff ff       	call   4046c0 <fatal_error>
  4065d9:	e9 04 fc ff ff       	jmp    4061e2 <io_thread+0xb42>
        fatal_error("setsockopt(SO_REUSEADDR)");
  4065de:	48 8d 3d 80 1b 00 00 	lea    0x1b80(%rip),%rdi        # 408165 <_IO_stdin_used+0x165>
  4065e5:	e8 d6 e0 ff ff       	call   4046c0 <fatal_error>
  4065ea:	e9 c9 fb ff ff       	jmp    4061b8 <io_thread+0xb18>
      fatal_error("listen()");
  4065ef:	48 8d 3d 8f 1b 00 00 	lea    0x1b8f(%rip),%rdi        # 408185 <_IO_stdin_used+0x185>
  4065f6:	e8 c5 e0 ff ff       	call   4046c0 <fatal_error>
  4065fb:	e9 f6 fb ff ff       	jmp    4061f6 <io_thread+0xb56>
	*cqe_ptr = cqe;
  406600:	48 89 7c 24 60       	mov    %rdi,0x60(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
  406605:	48 85 ff             	test   %rdi,%rdi
  406608:	0f 84 f1 fe ff ff    	je     4064ff <io_thread+0xe5f>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
  40660e:	4c 8b 07             	mov    (%rdi),%r8
        if (cqe->user_data == 1) {
  406611:	49 83 f8 01          	cmp    $0x1,%r8
  406615:	0f 84 cd 01 00 00    	je     4067e8 <io_thread+0x1148>
        if (cqe->res < 0) {
  40661b:	8b 7f 08             	mov    0x8(%rdi),%edi
        struct Request *req = (struct Request *) cqe->user_data;
  40661e:	4c 89 c2             	mov    %r8,%rdx
            fprintf(stderr, "Async request failed: %s for event: %d\n",
  406621:	44 8b 02             	mov    (%rdx),%r8d
        if (cqe->res < 0) {
  406624:	85 ff                	test   %edi,%edi
  406626:	0f 89 26 ff ff ff    	jns    406552 <io_thread+0xeb2>
            fprintf(stderr, "Async request failed: %s for event: %d\n",
  40662c:	f7 df                	neg    %edi
  40662e:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
  406633:	e8 68 bc ff ff       	call   4022a0 <strerror@plt>
  406638:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
  40663d:	be 01 00 00 00       	mov    $0x1,%esi
  406642:	48 8d 15 b7 20 00 00 	lea    0x20b7(%rip),%rdx        # 408700 <_IO_stdin_used+0x700>
  406649:	48 89 c1             	mov    %rax,%rcx
  40664c:	48 8b 05 a5 49 00 00 	mov    0x49a5(%rip),%rax        # 40aff8 <stderr@GLIBC_2.2.5>
  406653:	48 8b 38             	mov    (%rax),%rdi
  406656:	31 c0                	xor    %eax,%eax
  406658:	e8 13 bc ff ff       	call   402270 <__fprintf_chk@plt>
	if (cqe)
  40665d:	48 83 7c 24 60 00    	cmpq   $0x0,0x60(%rsp)
  406663:	0f 84 1a fe ff ff    	je     406483 <io_thread+0xde3>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  406669:	48 8b 94 24 f8 00 00 00 	mov    0xf8(%rsp),%rdx
  406671:	8b 02                	mov    (%rdx),%eax
  406673:	83 c0 01             	add    $0x1,%eax
  406676:	89 02                	mov    %eax,(%rdx)
}
  406678:	e9 06 fe ff ff       	jmp    406483 <io_thread+0xde3>
                add_accept_request(sock, &client_addr, &client_addr_len, &ring);
  40667d:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
  406682:	48 89 d9             	mov    %rbx,%rcx
  406685:	4c 89 ee             	mov    %r13,%rsi
  406688:	89 ef                	mov    %ebp,%edi
  40668a:	e8 51 e8 ff ff       	call   404ee0 <add_accept_request>
                struct NewClientMessage *newclientmsg = calloc(1, sizeof(struct NewClientMessage));
  40668f:	be 08 00 00 00       	mov    $0x8,%esi
  406694:	bf 01 00 00 00       	mov    $0x1,%edi
  406699:	e8 82 ba ff ff       	call   402120 <calloc@plt>
  40669e:	48 8b 54 24 60       	mov    0x60(%rsp),%rdx
                buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_CLIENT, newclientmsg);
  4066a3:	49 63 b7 18 01 00 00 	movslq 0x118(%r15),%rsi
  4066aa:	4c 89 ff             	mov    %r15,%rdi
                struct NewClientMessage *newclientmsg = calloc(1, sizeof(struct NewClientMessage));
  4066ad:	48 89 c1             	mov    %rax,%rcx
                data->sockettoken++;
  4066b0:	41 8b 87 28 01 00 00 	mov    0x128(%r15),%eax
  4066b7:	66 0f 6e 42 08       	movd   0x8(%rdx),%xmm0
                buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_CLIENT, newclientmsg);
  4066bc:	48 c1 e6 04          	shl    $0x4,%rsi
  4066c0:	ba 02 00 00 00       	mov    $0x2,%edx
  4066c5:	49 03 b7 10 01 00 00 	add    0x110(%r15),%rsi
                data->sockettoken++;
  4066cc:	83 c0 01             	add    $0x1,%eax
  4066cf:	66 0f 6e f8          	movd   %eax,%xmm7
  4066d3:	41 89 87 28 01 00 00 	mov    %eax,0x128(%r15)
                newclientmsg->sockettoken = data->sockettoken;
  4066da:	66 0f 62 c7          	punpckldq %xmm7,%xmm0
                newclientmsg->socket = cqe->res;
  4066de:	66 0f d6 01          	movq   %xmm0,(%rcx)
                buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_CLIENT, newclientmsg);
  4066e2:	e8 99 e8 ff ff       	call   404f80 <buffersend>
                add_read_request(data, &data->iomailboxes[data->other_io], cqe->res, data->sockettoken, &ring);
  4066e7:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
  4066ec:	49 89 d8             	mov    %rbx,%r8
  4066ef:	4c 89 ff             	mov    %r15,%rdi
  4066f2:	49 63 b7 18 01 00 00 	movslq 0x118(%r15),%rsi
  4066f9:	41 8b 8f 28 01 00 00 	mov    0x128(%r15),%ecx
  406700:	8b 50 08             	mov    0x8(%rax),%edx
  406703:	48 c1 e6 04          	shl    $0x4,%rsi
  406707:	49 03 b7 10 01 00 00 	add    0x110(%r15),%rsi
  40670e:	e8 8d e6 ff ff       	call   404da0 <add_read_request>
          io_uring_cqe_seen(&ring, cqe);
  406713:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
                break;
  406718:	e9 c8 fc ff ff       	jmp    4063e5 <io_thread+0xd45>
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
  40671d:	49 63 b7 18 01 00 00 	movslq 0x118(%r15),%rsi
  406724:	48 89 d9             	mov    %rbx,%rcx
  406727:	4c 89 ff             	mov    %r15,%rdi
  40672a:	48 c1 e6 04          	shl    $0x4,%rsi
  40672e:	49 03 b7 10 01 00 00 	add    0x110(%r15),%rsi
  406735:	e8 26 ed ff ff       	call   405460 <handle_client_request>
                eventfd_write(data->otherdataeventfd, 0);
  40673a:	41 8b 7f 70          	mov    0x70(%r15),%edi
  40673e:	31 f6                	xor    %esi,%esi
  406740:	e8 3b ba ff ff       	call   402180 <eventfd_write@plt>
          io_uring_cqe_seen(&ring, cqe);
  406745:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
                break;
  40674a:	e9 96 fc ff ff       	jmp    4063e5 <io_thread+0xd45>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  40674f:	48 8b 94 24 f8 00 00 00 	mov    0xf8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  406757:	48 8d 3d 3a 1a 00 00 	lea    0x1a3a(%rip),%rdi        # 408198 <_IO_stdin_used+0x198>
  40675e:	8b 02                	mov    (%rdx),%eax
  406760:	83 c0 01             	add    $0x1,%eax
  406763:	89 02                	mov    %eax,(%rdx)
  406765:	e8 e6 b8 ff ff       	call   402050 <puts@plt>
  40676a:	48 8d 3d c9 1a 00 00 	lea    0x1ac9(%rip),%rdi        # 40823a <_IO_stdin_used+0x23a>
  406771:	e8 da b8 ff ff       	call   402050 <puts@plt>
  406776:	e9 4d f5 ff ff       	jmp    405cc8 <io_thread+0x628>
              fprintf(stderr, "Async request failed: %s for event: %d\n",
  40677b:	f7 df                	neg    %edi
  40677d:	e8 1e bb ff ff       	call   4022a0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
  406782:	41 89 e8             	mov    %ebp,%r8d
  406785:	be 01 00 00 00       	mov    $0x1,%esi
  40678a:	48 8d 15 6f 1f 00 00 	lea    0x1f6f(%rip),%rdx        # 408700 <_IO_stdin_used+0x700>
  406791:	48 89 c1             	mov    %rax,%rcx
  406794:	48 8b 05 5d 48 00 00 	mov    0x485d(%rip),%rax        # 40aff8 <stderr@GLIBC_2.2.5>
  40679b:	48 8b 38             	mov    (%rax),%rdi
  40679e:	31 c0                	xor    %eax,%eax
  4067a0:	e8 cb ba ff ff       	call   402270 <__fprintf_chk@plt>
	if (cqe)
  4067a5:	48 83 7c 24 50 00    	cmpq   $0x0,0x50(%rsp)
  4067ab:	0f 84 86 f3 ff ff    	je     405b37 <io_thread+0x497>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
  4067b1:	48 8b 94 24 f8 00 00 00 	mov    0xf8(%rsp),%rdx
  4067b9:	8b 02                	mov    (%rdx),%eax
  4067bb:	83 c0 01             	add    $0x1,%eax
  4067be:	89 02                	mov    %eax,(%rdx)
}
  4067c0:	e9 72 f3 ff ff       	jmp    405b37 <io_thread+0x497>
  4067c5:	4d 89 fd             	mov    %r15,%r13
  4067c8:	e9 ca fd ff ff       	jmp    406597 <io_thread+0xef7>
	*cqe_ptr = cqe;
  4067cd:	48 89 7c 24 60       	mov    %rdi,0x60(%rsp)
	return err;
  4067d2:	e9 3a fe ff ff       	jmp    406611 <io_thread+0xf71>
        fatal_error("socket()");
  4067d7:	48 8d 3d 7e 19 00 00 	lea    0x197e(%rip),%rdi        # 40815c <_IO_stdin_used+0x15c>
  4067de:	e8 dd de ff ff       	call   4046c0 <fatal_error>
  4067e3:	e9 a4 f9 ff ff       	jmp    40618c <io_thread+0xaec>
  4067e8:	4d 89 fd             	mov    %r15,%r13
  4067eb:	e9 96 fd ff ff       	jmp    406586 <io_thread+0xee6>
      exit(1); 
  4067f0:	bf 01 00 00 00       	mov    $0x1,%edi
  4067f5:	e8 46 ba ff ff       	call   402240 <exit@plt>
				   perror("new client epoll_create1");
  4067fa:	48 8d 3d cd 19 00 00 	lea    0x19cd(%rip),%rdi        # 4081ce <_IO_stdin_used+0x1ce>
  406801:	e8 2a ba ff ff       	call   402230 <perror@plt>
				   exit(EXIT_FAILURE);
  406806:	bf 01 00 00 00       	mov    $0x1,%edi
  40680b:	e8 30 ba ff ff       	call   402240 <exit@plt>
}
  406810:	e8 8b b8 ff ff       	call   4020a0 <__stack_chk_fail@plt>
  406815:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000406820 <barriered_work_ingest>:
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
  406820:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
  406827:	8b 8e cc 00 00 00    	mov    0xcc(%rsi),%ecx
  40682d:	85 c9                	test   %ecx,%ecx
  40682f:	0f 8e e0 00 00 00    	jle    406915 <barriered_work_ingest+0xf5>
int barriered_work_ingest(struct BarrierTask *data) {
  406835:	41 56                	push   %r14
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
  406837:	45 31 f6             	xor    %r14d,%r14d
int barriered_work_ingest(struct BarrierTask *data) {
  40683a:	41 55                	push   %r13
  40683c:	41 54                	push   %r12
  40683e:	49 89 fc             	mov    %rdi,%r12
  406841:	55                   	push   %rbp
  406842:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
  406843:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
  406847:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  406850:	49 63 c6             	movslq %r14d,%rax
  406853:	31 ed                	xor    %ebp,%ebp
  406855:	4c 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%r13
  40685d:	48 8b 04 c7          	mov    (%rdi,%rax,8),%rax
  406861:	8b 10                	mov    (%rax),%edx
  406863:	85 d2                	test   %edx,%edx
  406865:	7e 26                	jle    40688d <barriered_work_ingest+0x6d>
  406867:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
  40686b:	48 63 c5             	movslq %ebp,%rax
  40686e:	48 8d 1c 80          	lea    (%rax,%rax,4),%rbx
  406872:	48 c1 e3 03          	shl    $0x3,%rbx
  406876:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
  40687a:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
  40687e:	74 28                	je     4068a8 <barriered_work_ingest+0x88>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
  406880:	83 c5 01             	add    $0x1,%ebp
  406883:	39 d5                	cmp    %edx,%ebp
  406885:	7c e4                	jl     40686b <barriered_work_ingest+0x4b>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
  406887:	8b 8e cc 00 00 00    	mov    0xcc(%rsi),%ecx
  40688d:	41 83 c6 01          	add    $0x1,%r14d
  406891:	41 39 ce             	cmp    %ecx,%r14d
  406894:	7c ba                	jl     406850 <barriered_work_ingest+0x30>
}
  406896:	5b                   	pop    %rbx
  406897:	31 c0                	xor    %eax,%eax
  406899:	5d                   	pop    %rbp
  40689a:	41 5c                	pop    %r12
  40689c:	41 5d                	pop    %r13
  40689e:	41 5e                	pop    %r14
  4068a0:	c3                   	ret
  4068a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->ingest_count++;
  4068a8:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
  4068b1:	48 63 70 1c          	movslq 0x1c(%rax),%rsi
  4068b5:	bf 04 00 00 00       	mov    $0x4,%edi
  4068ba:	48 c1 e6 05          	shl    $0x5,%rsi
  4068be:	48 03 70 10          	add    0x10(%rax),%rsi
  4068c2:	48 83 c6 10          	add    $0x10,%rsi
  4068c6:	e8 a5 b7 ff ff       	call   402070 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
  4068cb:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
  4068d3:	48 8b 40 50          	mov    0x50(%rax),%rax
  4068d7:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
  4068db:	48 03 58 08          	add    0x8(%rax),%rbx
  4068df:	8b 43 1c             	mov    0x1c(%rbx),%eax
        data->thread->buffers[b]->buffer[x].available = 0;
  4068e2:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
  4068e9:	83 c0 01             	add    $0x1,%eax
  4068ec:	99                   	cltd
  4068ed:	f7 7b 18             	idivl  0x18(%rbx)
  4068f0:	89 53 1c             	mov    %edx,0x1c(%rbx)
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
  4068f3:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
  4068fb:	83 c5 01             	add    $0x1,%ebp
  4068fe:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
  406902:	4a 8b 04 2f          	mov    (%rdi,%r13,1),%rax
  406906:	8b 10                	mov    (%rax),%edx
  406908:	39 d5                	cmp    %edx,%ebp
  40690a:	0f 8c 57 ff ff ff    	jl     406867 <barriered_work_ingest+0x47>
  406910:	e9 72 ff ff ff       	jmp    406887 <barriered_work_ingest+0x67>
}
  406915:	31 c0                	xor    %eax,%eax
  406917:	c3                   	ret
  406918:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000406920 <barriered_thread>:
void* barriered_thread(void *arg) {
  406920:	41 56                	push   %r14
  406922:	41 55                	push   %r13
  int t = 0;
  406924:	45 31 ed             	xor    %r13d,%r13d
void* barriered_thread(void *arg) {
  406927:	41 54                	push   %r12
  int waiting = 0;
  406929:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
  40692c:	55                   	push   %rbp
  40692d:	48 89 fd             	mov    %rdi,%rbp
  406930:	53                   	push   %rbx
  406931:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
  406938:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
  40693c:	0f 85 92 02 00 00    	jne    406bd4 <barriered_thread+0x2b4>
    if (t >= data->task_count) {
  406942:	8b 45 40             	mov    0x40(%rbp),%eax
  406945:	44 39 e8             	cmp    %r13d,%eax
  406948:	7f 3a                	jg     406984 <barriered_thread+0x64>
      data->cycles++;
  40694a:	48 83 85 b8 00 00 00 01 	addq   $0x1,0xb8(%rbp)
      t = 0;
  406952:	45 31 ed             	xor    %r13d,%r13d
    for (; t < data->task_count; t++) {
  406955:	85 c0                	test   %eax,%eax
  406957:	7f 2b                	jg     406984 <barriered_thread+0x64>
  406959:	eb dd                	jmp    406938 <barriered_thread+0x18>
  40695b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
  406960:	48 63 55 04          	movslq 0x4(%rbp),%rdx
  406964:	48 8b 45 18          	mov    0x18(%rbp),%rax
  406968:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
  40696c:	48 8b 78 38          	mov    0x38(%rax),%rdi
  406970:	48 01 df             	add    %rbx,%rdi
  406973:	e8 a8 fe ff ff       	call   406820 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
  406978:	8b 45 40             	mov    0x40(%rbp),%eax
  40697b:	41 83 c5 01          	add    $0x1,%r13d
  40697f:	44 39 e8             	cmp    %r13d,%eax
  406982:	7e b4                	jle    406938 <barriered_thread+0x18>
      if (data->tasks[t].available == 1) {
  406984:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  406988:	49 63 dd             	movslq %r13d,%rbx
  40698b:	48 c1 e3 09          	shl    $0x9,%rbx
  40698f:	48 8d 34 1a          	lea    (%rdx,%rbx,1),%rsi
  406993:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
  40699a:	75 c4                	jne    406960 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
  40699c:	44 8b 55 28          	mov    0x28(%rbp),%r10d
  4069a0:	83 e8 01             	sub    $0x1,%eax
  4069a3:	41 8d 4d ff          	lea    -0x1(%r13),%ecx
  4069a7:	45 85 ed             	test   %r13d,%r13d
  4069aa:	0f 4f c1             	cmovg  %ecx,%eax
  4069ad:	45 85 d2             	test   %r10d,%r10d
  4069b0:	0f 8e ea 01 00 00    	jle    406ba0 <barriered_thread+0x280>
  4069b6:	48 8b 55 18          	mov    0x18(%rbp),%rdx
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  4069ba:	48 63 c8             	movslq %eax,%rcx
        int arrived = 0; 
  4069bd:	45 31 f6             	xor    %r14d,%r14d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  4069c0:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
  4069c7:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
  4069ce:	41 8d 72 ff          	lea    -0x1(%r10),%esi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  4069d2:	48 c1 e1 09          	shl    $0x9,%rcx
  4069d6:	48 8d 42 08          	lea    0x8(%rdx),%rax
  4069da:	48 8d 3c f0          	lea    (%rax,%rsi,8),%rdi
        int prearrive = 0; 
  4069de:	31 f6                	xor    %esi,%esi
  4069e0:	eb 0a                	jmp    4069ec <barriered_thread+0xcc>
  4069e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  4069e8:	48 83 c0 08          	add    $0x8,%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
  4069ec:	48 8b 12             	mov    (%rdx),%rdx
  4069ef:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
  4069f3:	49 01 cb             	add    %rcx,%r11
  4069f6:	4c 89 da             	mov    %r11,%rdx
            arrived++;
  4069f9:	45 31 db             	xor    %r11d,%r11d
  4069fc:	44 3b 8a 80 00 00 00 	cmp    0x80(%rdx),%r9d
  406a03:	41 0f 94 c3          	sete   %r11b
  406a07:	45 01 de             	add    %r11d,%r14d
            prearrive++;
  406a0a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
  406a11:	0f 94 c2             	sete   %dl
  406a14:	0f b6 d2             	movzbl %dl,%edx
  406a17:	01 d6                	add    %edx,%esi
        for (int thread = 0 ; thread < data->thread_count; thread++) {
  406a19:	48 89 c2             	mov    %rax,%rdx
  406a1c:	48 39 c7             	cmp    %rax,%rdi
  406a1f:	75 c7                	jne    4069e8 <barriered_thread+0xc8>
        if (prearrive == 0 || prearrive == data->thread_count) {
  406a21:	85 f6                	test   %esi,%esi
  406a23:	0f 84 bf 00 00 00    	je     406ae8 <barriered_thread+0x1c8>
  406a29:	41 39 f2             	cmp    %esi,%r10d
  406a2c:	0f 84 b6 00 00 00    	je     406ae8 <barriered_thread+0x1c8>
        if (arrived == 0 || arrived == data->thread_count) {
  406a32:	45 85 f6             	test   %r14d,%r14d
  406a35:	74 0a                	je     406a41 <barriered_thread+0x121>
  406a37:	44 39 75 28          	cmp    %r14d,0x28(%rbp)
  406a3b:	0f 85 71 01 00 00    	jne    406bb2 <barriered_thread+0x292>
  406a41:	48 8b 55 38          	mov    0x38(%rbp),%rdx
          data->tasks[t].prearrive++;
  406a45:	48 01 da             	add    %rbx,%rdx
  406a48:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
  406a4f:	45 85 ed             	test   %r13d,%r13d
  406a52:	75 14                	jne    406a68 <barriered_thread+0x148>
  406a54:	48 8b b5 90 00 00 00 	mov    0x90(%rbp),%rsi
  406a5b:	48 3b b5 98 00 00 00 	cmp    0x98(%rbp),%rsi
  406a62:	0f 8c 18 01 00 00    	jl     406b80 <barriered_thread+0x260>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
  406a68:	48 63 4d 04          	movslq 0x4(%rbp),%rcx
  406a6c:	48 8b 45 18          	mov    0x18(%rbp),%rax
          data->tasks[t].available = 0;
  406a70:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
  406a7a:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
  406a7e:	48 8b 78 38          	mov    0x38(%rax),%rdi
  406a82:	48 01 df             	add    %rbx,%rdi
  406a85:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  406a8b:	8b 45 40             	mov    0x40(%rbp),%eax
          data->tasks[t].arrived++;
  406a8e:	48 03 5d 38          	add    0x38(%rbp),%rbx
  406a92:	83 83 80 00 00 00 01 	addl   $0x1,0x80(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  406a99:	83 e8 01             	sub    $0x1,%eax
          data->iteration_count++;
  406a9c:	48 83 85 88 00 00 00 01 	addq   $0x1,0x88(%rbp)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  406aa4:	44 39 e8             	cmp    %r13d,%eax
  406aa7:	0f 84 93 00 00 00    	je     406b40 <barriered_thread+0x220>
          if (waiting == 0) {
  406aad:	45 85 e4             	test   %r12d,%r12d
  406ab0:	0f 85 c2 fe ff ff    	jne    406978 <barriered_thread+0x58>
            data->task_snapshot[data->task_timestamp_count].task = t;
  406ab6:	48 8b 85 a8 00 00 00 	mov    0xa8(%rbp),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
  406abd:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
  406ac2:	41 bc 01 00 00 00    	mov    $0x1,%r12d
            data->task_snapshot[data->task_timestamp_count].task = t;
  406ac8:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  406acc:	48 8b 85 a0 00 00 00 	mov    0xa0(%rbp),%rax
  406ad3:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
  406ad7:	44 89 6e 20          	mov    %r13d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
  406adb:	e8 90 b5 ff ff       	call   402070 <clock_gettime@plt>
            waiting = 1;
  406ae0:	e9 93 fe ff ff       	jmp    406978 <barriered_thread+0x58>
  406ae5:	0f 1f 00             	nopl   (%rax)
          if (waiting == 1) {
  406ae8:	41 83 fc 01          	cmp    $0x1,%r12d
  406aec:	0f 85 40 ff ff ff    	jne    406a32 <barriered_thread+0x112>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
  406af2:	48 8b 85 a8 00 00 00 	mov    0xa8(%rbp),%rax
  406af9:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 0; 
  406afe:	45 31 e4             	xor    %r12d,%r12d
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
  406b01:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
  406b05:	48 8b 85 a0 00 00 00 	mov    0xa0(%rbp),%rax
  406b0c:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
  406b11:	e8 5a b5 ff ff       	call   402070 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
  406b16:	48 8b 85 a8 00 00 00 	mov    0xa8(%rbp),%rax
  406b1d:	48 83 c0 01          	add    $0x1,%rax
  406b21:	48 99                	cqto
  406b23:	48 f7 bd b0 00 00 00 	idivq  0xb0(%rbp)
  406b2a:	48 89 95 a8 00 00 00 	mov    %rdx,0xa8(%rbp)
            waiting = 0; 
  406b31:	e9 fc fe ff ff       	jmp    406a32 <barriered_thread+0x112>
  406b36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
  406b40:	48 8b b5 90 00 00 00 	mov    0x90(%rbp),%rsi
  406b47:	48 3b b5 98 00 00 00 	cmp    0x98(%rbp),%rsi
  406b4e:	0f 8d 59 ff ff ff    	jge    406aad <barriered_thread+0x18d>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
  406b54:	48 c1 e6 04          	shl    $0x4,%rsi
  406b58:	bf 04 00 00 00       	mov    $0x4,%edi
  406b5d:	48 03 b5 80 00 00 00 	add    0x80(%rbp),%rsi
  406b64:	e8 07 b5 ff ff       	call   402070 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
  406b69:	48 83 85 90 00 00 00 01 	addq   $0x1,0x90(%rbp)
  406b71:	e9 37 ff ff ff       	jmp    406aad <barriered_thread+0x18d>
  406b76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
  406b80:	48 c1 e6 04          	shl    $0x4,%rsi
  406b84:	bf 04 00 00 00       	mov    $0x4,%edi
  406b89:	48 03 75 78          	add    0x78(%rbp),%rsi
  406b8d:	e8 de b4 ff ff       	call   402070 <clock_gettime@plt>
          data->tasks[t].available = 0;
  406b92:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  406b96:	48 01 da             	add    %rbx,%rdx
  406b99:	e9 ca fe ff ff       	jmp    406a68 <barriered_thread+0x148>
  406b9e:	66 90                	xchg   %ax,%ax
          if (waiting == 1) {
  406ba0:	41 83 fc 01          	cmp    $0x1,%r12d
  406ba4:	0f 85 9b fe ff ff    	jne    406a45 <barriered_thread+0x125>
        int arrived = 0; 
  406baa:	45 31 f6             	xor    %r14d,%r14d
  406bad:	e9 40 ff ff ff       	jmp    406af2 <barriered_thread+0x1d2>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
  406bb2:	48 63 55 04          	movslq 0x4(%rbp),%rdx
  406bb6:	48 8b 45 18          	mov    0x18(%rbp),%rax
  406bba:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
  406bbe:	48 03 58 38          	add    0x38(%rax),%rbx
  406bc2:	48 89 df             	mov    %rbx,%rdi
  406bc5:	e8 56 fc ff ff       	call   406820 <barriered_work_ingest>
  while (data->running == 1) {
  406bca:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
  406bce:	0f 84 6e fd ff ff    	je     406942 <barriered_thread+0x22>
}
  406bd4:	5b                   	pop    %rbx
  406bd5:	31 c0                	xor    %eax,%eax
  406bd7:	5d                   	pop    %rbp
  406bd8:	41 5c                	pop    %r12
  406bda:	41 5d                	pop    %r13
  406bdc:	41 5e                	pop    %r14
  406bde:	c3                   	ret
  406bdf:	90                   	nop

0000000000406be0 <receive>:
int receive(struct BarrierTask *data) {
  406be0:	41 57                	push   %r15
  406be2:	41 56                	push   %r14
  406be4:	41 55                	push   %r13
  406be6:	41 54                	push   %r12
  406be8:	55                   	push   %rbp
  406be9:	53                   	push   %rbx
  406bea:	48 83 ec 08          	sub    $0x8,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  406bee:	4c 63 af 40 01 00 00 	movslq 0x140(%rdi),%r13
  406bf5:	45 85 ed             	test   %r13d,%r13d
  406bf8:	0f 8e 18 01 00 00    	jle    406d16 <receive+0x136>
    if (n == data->thread->real_thread_index) { continue; }
  406bfe:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  406c05:	48 89 fe             	mov    %rdi,%rsi
  406c08:	31 ed                	xor    %ebp,%ebp
  406c0a:	4c 63 60 08          	movslq 0x8(%rax),%r12
  406c0e:	4d 89 e6             	mov    %r12,%r14
  406c11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  406c18:	41 39 ee             	cmp    %ebp,%r14d
  406c1b:	0f 84 e8 00 00 00    	je     406d09 <receive+0x129>
    struct Data *me = data->mailboxes[n].lower;
  406c21:	48 89 e8             	mov    %rbp,%rax
  406c24:	48 c1 e0 08          	shl    $0x8,%rax
  406c28:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
  406c2f:	48 8b 38             	mov    (%rax),%rdi
    if (me->available_reading == 1) {
  406c32:	8b 87 00 02 00 00    	mov    0x200(%rdi),%eax
  406c38:	83 f8 01             	cmp    $0x1,%eax
  406c3b:	74 11                	je     406c4e <receive+0x6e>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
  406c3d:	83 bf 08 04 00 00 02 	cmpl   $0x2,0x408(%rdi)
  406c44:	75 08                	jne    406c4e <receive+0x6e>
  406c46:	85 c0                	test   %eax,%eax
  406c48:	0f 84 bb 00 00 00    	je     406d09 <receive+0x129>
    for (int x = 0; x < me->messages_count ; x++ ) {
  406c4e:	4c 8b 97 80 00 00 00 	mov    0x80(%rdi),%r10
  406c55:	4d 85 d2             	test   %r10,%r10
  406c58:	0f 8e 82 00 00 00    	jle    406ce0 <receive+0x100>
      data->sends++;
  406c5e:	4c 8b be 80 01 00 00 	mov    0x180(%rsi),%r15
      if (me->messages[x]->group == data->group) {
  406c65:	48 8b 1f             	mov    (%rdi),%rbx
      me->received++;
  406c68:	31 c9                	xor    %ecx,%ecx
  406c6a:	31 d2                	xor    %edx,%edx
      data->n++;
  406c6c:	4c 8b 8e 08 01 00 00 	mov    0x108(%rsi),%r9
      me->received++;
  406c73:	4c 8b 87 00 04 00 00 	mov    0x400(%rdi),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
  406c7a:	4c 63 5e 04          	movslq 0x4(%rsi),%r11
  406c7e:	49 8d 47 01          	lea    0x1(%r15),%rax
      data->n++;
  406c82:	4d 29 f9             	sub    %r15,%r9
      me->received++;
  406c85:	4d 29 f8             	sub    %r15,%r8
  406c88:	eb 15                	jmp    406c9f <receive+0xbf>
  406c8a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0; x < me->messages_count ; x++ ) {
  406c90:	83 c1 01             	add    $0x1,%ecx
  406c93:	48 83 c0 01          	add    $0x1,%rax
  406c97:	48 63 d1             	movslq %ecx,%rdx
  406c9a:	4c 39 d2             	cmp    %r10,%rdx
  406c9d:	7d 41                	jge    406ce0 <receive+0x100>
      data->n++;
  406c9f:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
      if (me->messages[x]->group == data->group) {
  406ca3:	48 8b 14 d3          	mov    (%rbx,%rdx,8),%rdx
      data->sends++;
  406ca7:	48 89 86 80 01 00 00 	mov    %rax,0x180(%rsi)
      data->n++;
  406cae:	4c 89 be 08 01 00 00 	mov    %r15,0x108(%rsi)
      me->received++;
  406cb5:	4d 8d 3c 00          	lea    (%r8,%rax,1),%r15
  406cb9:	4c 89 bf 00 04 00 00 	mov    %r15,0x400(%rdi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
  406cc0:	4c 39 5a 10          	cmp    %r11,0x10(%rdx)
  406cc4:	75 ca                	jne    406c90 <receive+0xb0>
  406cc6:	4c 39 62 08          	cmp    %r12,0x8(%rdx)
  406cca:	75 c4                	jne    406c90 <receive+0xb0>
        exit(1);
  406ccc:	bf 01 00 00 00       	mov    $0x1,%edi
  406cd1:	e8 6a b5 ff ff       	call   402240 <exit@plt>
  406cd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    me->messages_count = 0;
  406ce0:	48 c7 87 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rdi)
      me->available_reading = 0;
  406ceb:	c7 87 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdi)
      me->finished_reading = 1;
  406cf5:	c7 87 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdi)
      me->available_sending = 1;
  406cff:	c7 87 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdi)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  406d09:	48 83 c5 01          	add    $0x1,%rbp
  406d0d:	49 39 ed             	cmp    %rbp,%r13
  406d10:	0f 85 02 ff ff ff    	jne    406c18 <receive+0x38>
}
  406d16:	48 83 c4 08          	add    $0x8,%rsp
  406d1a:	31 c0                	xor    %eax,%eax
  406d1c:	5b                   	pop    %rbx
  406d1d:	5d                   	pop    %rbp
  406d1e:	41 5c                	pop    %r12
  406d20:	41 5d                	pop    %r13
  406d22:	41 5e                	pop    %r14
  406d24:	41 5f                	pop    %r15
  406d26:	c3                   	ret
  406d27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000406d30 <sendm>:
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  406d30:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
  406d36:	85 c0                	test   %eax,%eax
  406d38:	0f 8e 22 02 00 00    	jle    406f60 <sendm+0x230>
int sendm(struct BarrierTask *data) {
  406d3e:	41 57                	push   %r15
        if (n == data->thread->real_thread_index) { continue; }
  406d40:	31 d2                	xor    %edx,%edx
  406d42:	49 89 ff             	mov    %rdi,%r15
int sendm(struct BarrierTask *data) {
  406d45:	41 56                	push   %r14
  406d47:	41 55                	push   %r13
  406d49:	41 54                	push   %r12
  406d4b:	55                   	push   %rbp
  406d4c:	48 63 e8             	movslq %eax,%rbp
  406d4f:	48 8d 87 90 01 00 00 	lea    0x190(%rdi),%rax
  406d56:	53                   	push   %rbx
        if (n == data->thread->real_thread_index) { continue; }
  406d57:	48 8b 9f 28 01 00 00 	mov    0x128(%rdi),%rbx
  406d5e:	44 8b 63 08          	mov    0x8(%rbx),%r12d
  406d62:	48 89 44 24 d0       	mov    %rax,-0x30(%rsp)
  406d67:	48 8d 87 98 01 00 00 	lea    0x198(%rdi),%rax
  406d6e:	48 89 5c 24 c8       	mov    %rbx,-0x38(%rsp)
  406d73:	48 89 44 24 d8       	mov    %rax,-0x28(%rsp)
  406d78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  406d80:	41 39 d4             	cmp    %edx,%r12d
  406d83:	0f 84 97 00 00 00    	je     406e20 <sendm+0xf0>
        struct Data *them = data->mailboxes[n].higher;
  406d89:	48 89 d0             	mov    %rdx,%rax
  406d8c:	48 c1 e0 08          	shl    $0x8,%rax
  406d90:	49 03 87 70 01 00 00 	add    0x170(%r15),%rax
        data->mailboxes[n].counter++;
  406d97:	48 8b 98 b8 00 00 00 	mov    0xb8(%rax),%rbx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
  406d9e:	83 b8 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax)
        struct Data *them = data->mailboxes[n].higher;
  406da5:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
  406dac:	41 0f 94 c1          	sete   %r9b
        data->mailboxes[n].counter++;
  406db0:	48 8d 4b 01          	lea    0x1(%rbx),%rcx
  406db4:	48 89 88 b8 00 00 00 	mov    %rcx,0xb8(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
  406dbb:	48 85 c9             	test   %rcx,%rcx
  406dbe:	7f 05                	jg     406dc5 <sendm+0x95>
  406dc0:	45 84 c9             	test   %r9b,%r9b
  406dc3:	75 5b                	jne    406e20 <sendm+0xf0>
        if (them->messages_count > 0) {
  406dc5:	48 8b be 80 00 00 00 	mov    0x80(%rsi),%rdi
  406dcc:	48 85 ff             	test   %rdi,%rdi
  406dcf:	7f 4f                	jg     406e20 <sendm+0xf0>
        if (them->available_sending == 1) {
  406dd1:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
  406dd8:	41 83 f8 01          	cmp    $0x1,%r8d
  406ddc:	74 0e                	je     406dec <sendm+0xbc>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
  406dde:	83 be 08 04 00 00 02 	cmpl   $0x2,0x408(%rsi)
  406de5:	75 05                	jne    406dec <sendm+0xbc>
  406de7:	45 85 c0             	test   %r8d,%r8d
  406dea:	74 34                	je     406e20 <sendm+0xf0>
        if (data->sending == 1) {
  406dec:	41 83 bf 88 01 00 00 01 	cmpl   $0x1,0x188(%r15)
  406df4:	74 4a                	je     406e40 <sendm+0x110>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter >= limit) {
  406df6:	48 85 c9             	test   %rcx,%rcx
  406df9:	7e 25                	jle    406e20 <sendm+0xf0>
  406dfb:	45 84 c9             	test   %r9b,%r9b
  406dfe:	74 20                	je     406e20 <sendm+0xf0>
          data->mailboxes[n].counter = 0;
  406e00:	48 c7 80 b8 00 00 00 00 00 00 00 	movq   $0x0,0xb8(%rax)
          data->thread->have_foreign = 1;
  406e0b:	48 8b 44 24 c8       	mov    -0x38(%rsp),%rax
  406e10:	c7 80 08 01 00 00 01 00 00 00 	movl   $0x1,0x108(%rax)
  406e1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
  406e20:	48 83 c2 01          	add    $0x1,%rdx
  406e24:	48 39 d5             	cmp    %rdx,%rbp
  406e27:	0f 85 53 ff ff ff    	jne    406d80 <sendm+0x50>
}
  406e2d:	31 c0                	xor    %eax,%eax
  406e2f:	5b                   	pop    %rbx
  406e30:	5d                   	pop    %rbp
  406e31:	41 5c                	pop    %r12
  406e33:	41 5d                	pop    %r13
  406e35:	41 5e                	pop    %r14
  406e37:	41 5f                	pop    %r15
  406e39:	c3                   	ret
  406e3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          for (; them->messages_count < min;) {
  406e40:	4c 63 9e 88 00 00 00 	movslq 0x88(%rsi),%r11
  406e47:	4c 39 df             	cmp    %r11,%rdi
  406e4a:	0f 8d c9 00 00 00    	jge    406f19 <sendm+0x1e9>
  406e50:	49 8b 9f 08 01 00 00 	mov    0x108(%r15),%rbx
            them->messages[them->messages_count++] = data->message; 
  406e57:	4c 8b 16             	mov    (%rsi),%r10
  406e5a:	4d 89 de             	mov    %r11,%r14
  406e5d:	49 29 fe             	sub    %rdi,%r14
  406e60:	48 89 5c 24 e0       	mov    %rbx,-0x20(%rsp)
  406e65:	48 8b 9e 80 03 00 00 	mov    0x380(%rsi),%rbx
  406e6c:	4d 8d 04 fa          	lea    (%r10,%rdi,8),%r8
  406e70:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
  406e75:	4b 8d 1c da          	lea    (%r10,%r11,8),%rbx
  406e79:	48 3b 5c 24 d0       	cmp    -0x30(%rsp),%rbx
  406e7e:	0f 96 44 24 f7       	setbe  -0x9(%rsp)
  406e83:	4c 3b 44 24 d8       	cmp    -0x28(%rsp),%r8
  406e88:	41 0f 93 c5          	setae  %r13b
  406e8c:	44 0a 6c 24 f7       	or     -0x9(%rsp),%r13b
  406e91:	0f 84 a9 00 00 00    	je     406f40 <sendm+0x210>
  406e97:	4d 8d 6e ff          	lea    -0x1(%r14),%r13
  406e9b:	49 83 fd 02          	cmp    $0x2,%r13
  406e9f:	0f 86 9b 00 00 00    	jbe    406f40 <sendm+0x210>
  406ea5:	4d 8b af 90 01 00 00 	mov    0x190(%r15),%r13
  406eac:	4c 89 f3             	mov    %r14,%rbx
  406eaf:	48 d1 eb             	shr    %rbx
  406eb2:	66 49 0f 6e c5       	movq   %r13,%xmm0
  406eb7:	48 c1 e3 04          	shl    $0x4,%rbx
  406ebb:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
  406ebf:	4c 01 c3             	add    %r8,%rbx
  406ec2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  406ec8:	41 0f 11 00          	movups %xmm0,(%r8)
          for (; them->messages_count < min;) {
  406ecc:	49 83 c0 10          	add    $0x10,%r8
  406ed0:	4c 39 c3             	cmp    %r8,%rbx
  406ed3:	75 f3                	jne    406ec8 <sendm+0x198>
  406ed5:	4d 89 f0             	mov    %r14,%r8
  406ed8:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
  406edc:	4c 01 c7             	add    %r8,%rdi
  406edf:	4d 39 c6             	cmp    %r8,%r14
  406ee2:	74 0b                	je     406eef <sendm+0x1bf>
            them->messages[them->messages_count++] = data->message; 
  406ee4:	4d 8b af 90 01 00 00 	mov    0x190(%r15),%r13
  406eeb:	4d 89 2c fa          	mov    %r13,(%r10,%rdi,8)
            data->n++;
  406eef:	48 8b 7c 24 e0       	mov    -0x20(%rsp),%rdi
  406ef4:	4c 01 f7             	add    %r14,%rdi
  406ef7:	49 89 bf 08 01 00 00 	mov    %rdi,0x108(%r15)
            them->sent++;
  406efe:	48 8b 7c 24 e8       	mov    -0x18(%rsp),%rdi
  406f03:	4c 89 9e 80 00 00 00 	mov    %r11,0x80(%rsi)
  406f0a:	4c 01 f7             	add    %r14,%rdi
  406f0d:	48 89 be 80 03 00 00 	mov    %rdi,0x380(%rsi)
  406f14:	4f 89 6c da f8       	mov    %r13,-0x8(%r10,%r11,8)
          them->available_sending = 0;
  406f19:	c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rsi)
          them->available_reading = 1;
  406f23:	c7 86 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rsi)
          them->available_receiving = 1;
  406f2d:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
  406f37:	e9 ba fe ff ff       	jmp    406df6 <sendm+0xc6>
  406f3c:	0f 1f 40 00          	nopl   0x0(%rax)
            them->messages[them->messages_count++] = data->message; 
  406f40:	4d 8b af 90 01 00 00 	mov    0x190(%r15),%r13
          for (; them->messages_count < min;) {
  406f47:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
  406f4b:	4d 89 68 f8          	mov    %r13,-0x8(%r8)
          for (; them->messages_count < min;) {
  406f4f:	49 39 d8             	cmp    %rbx,%r8
  406f52:	75 ec                	jne    406f40 <sendm+0x210>
  406f54:	eb 99                	jmp    406eef <sendm+0x1bf>
  406f56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
}
  406f60:	31 c0                	xor    %eax,%eax
  406f62:	c3                   	ret
  406f63:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  406f6e:	66 90                	xchg   %ax,%ax

0000000000406f70 <mailboxkind>:
  if (kind == 0) {
  406f70:	85 f6                	test   %esi,%esi
  406f72:	74 1c                	je     406f90 <mailboxkind+0x20>
  return NULL;
  406f74:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
  406f76:	83 fe 01             	cmp    $0x1,%esi
  406f79:	74 05                	je     406f80 <mailboxkind+0x10>
}
  406f7b:	c3                   	ret
  406f7c:	0f 1f 40 00          	nopl   0x0(%rax)
    return mailbox->higher;
  406f80:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
}
  406f87:	c3                   	ret
  406f88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    return mailbox->lower;
  406f90:	48 8b 07             	mov    (%rdi),%rax
  406f93:	c3                   	ret
  406f94:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  406f9f:	90                   	nop

0000000000406fa0 <setmailboxkind>:
  if (kind == 0) {
  406fa0:	85 d2                	test   %edx,%edx
  406fa2:	75 0c                	jne    406fb0 <setmailboxkind+0x10>
    mailbox->lower = data;
  406fa4:	48 89 37             	mov    %rsi,(%rdi)
}
  406fa7:	31 c0                	xor    %eax,%eax
  406fa9:	c3                   	ret
  406faa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (kind == 1) {
  406fb0:	83 fa 01             	cmp    $0x1,%edx
  406fb3:	75 0b                	jne    406fc0 <setmailboxkind+0x20>
    mailbox->higher = data;
  406fb5:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
}
  406fbc:	31 c0                	xor    %eax,%eax
  406fbe:	c3                   	ret
  406fbf:	90                   	nop
  if (kind == 2) {
  406fc0:	83 fa 02             	cmp    $0x2,%edx
  406fc3:	75 0a                	jne    406fcf <setmailboxkind+0x2f>
    mailbox->pending_lower = data;
  406fc5:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
}
  406fcc:	31 c0                	xor    %eax,%eax
  406fce:	c3                   	ret
  if (kind == 3) {
  406fcf:	83 fa 03             	cmp    $0x3,%edx
  406fd2:	75 d3                	jne    406fa7 <setmailboxkind+0x7>
    mailbox->pending_higher = data;
  406fd4:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
}
  406fdb:	31 c0                	xor    %eax,%eax
  406fdd:	c3                   	ret
  406fde:	66 90                	xchg   %ax,%ax

0000000000406fe0 <fswap>:
int fswap(struct BarrierTask *data) {
  406fe0:	41 57                	push   %r15
  406fe2:	41 56                	push   %r14
  406fe4:	41 55                	push   %r13
  406fe6:	49 89 fd             	mov    %rdi,%r13
  406fe9:	41 54                	push   %r12
  406feb:	55                   	push   %rbp
  406fec:	53                   	push   %rbx
  406fed:	48 83 ec 48          	sub    $0x48,%rsp
      int y = (k * data->thread->threads_per_group) + data->thread_index;
  406ff1:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    int k = data->group;
  406ff8:	8b 87 9c 01 00 00    	mov    0x19c(%rdi),%eax
  int t = data->task_index;
  406ffe:	48 63 57 04          	movslq 0x4(%rdi),%rdx
      int y = (k * data->thread->threads_per_group) + data->thread_index;
  407002:	8b be d4 00 00 00    	mov    0xd4(%rsi),%edi
    int k = data->group;
  407008:	89 44 24 34          	mov    %eax,0x34(%rsp)
      int y = (k * data->thread->threads_per_group) + data->thread_index;
  40700c:	0f af c7             	imul   %edi,%eax
  40700f:	41 03 85 30 01 00 00 	add    0x130(%r13),%eax
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  407016:	85 ff                	test   %edi,%edi
  407018:	0f 8e 86 02 00 00    	jle    4072a4 <fswap+0x2c4>
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  40701e:	48 98                	cltq
  407020:	48 c1 e2 09          	shl    $0x9,%rdx
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  407024:	c7 44 24 30 00 00 00 00 	movl   $0x0,0x30(%rsp)
  40702c:	4d 89 ee             	mov    %r13,%r14
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  40702f:	4c 8d 04 c0          	lea    (%rax,%rax,8),%r8
  407033:	48 89 54 24 38       	mov    %rdx,0x38(%rsp)
  407038:	4e 8d 04 40          	lea    (%rax,%r8,2),%r8
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
  40703c:	48 c1 e0 08          	shl    $0x8,%rax
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  407040:	49 c1 e0 04          	shl    $0x4,%r8
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
  407044:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  407049:	4c 89 04 24          	mov    %r8,(%rsp)
  40704d:	eb 12                	jmp    407061 <fswap+0x81>
  40704f:	90                   	nop
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  407050:	83 44 24 30 01       	addl   $0x1,0x30(%rsp)
  407055:	8b 44 24 30          	mov    0x30(%rsp),%eax
  407059:	39 f8                	cmp    %edi,%eax
  40705b:	0f 8d 43 02 00 00    	jge    4072a4 <fswap+0x2c4>
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  407061:	48 8b 0c 24          	mov    (%rsp),%rcx
        int b = (g * data->thread->threads_per_group) + m;
  407065:	8b 44 24 34          	mov    0x34(%rsp),%eax
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  407069:	48 8b 56 20          	mov    0x20(%rsi),%rdx
        int b = (g * data->thread->threads_per_group) + m;
  40706d:	0f af c7             	imul   %edi,%eax
  407070:	03 44 24 30          	add    0x30(%rsp),%eax
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
  407074:	48 8b 54 0a 38       	mov    0x38(%rdx,%rcx,1),%rdx
  407079:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
  40707e:	48 98                	cltq
  407080:	49 89 c7             	mov    %rax,%r15
  407083:	48 8b 94 0a 70 01 00 00 	mov    0x170(%rdx,%rcx,1),%rdx
  40708b:	49 c1 e7 08          	shl    $0x8,%r15
        if (kind == MAILBOX_FRIEND) {
  40708f:	42 83 bc 3a b0 00 00 00 01 	cmpl   $0x1,0xb0(%rdx,%r15,1)
  407098:	75 b6                	jne    407050 <fswap+0x70>
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
  40709a:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
  40709e:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
             for (int nn = 0 ; nn < data->thread_count; nn++) {
  4070a2:	41 8b 96 34 01 00 00 	mov    0x134(%r14),%edx
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
  4070a9:	48 c1 e0 04          	shl    $0x4,%rax
             for (int nn = 0 ; nn < data->thread_count; nn++) {
  4070ad:	85 d2                	test   %edx,%edx
  4070af:	7e 9f                	jle    407050 <fswap+0x70>
  4070b1:	4d 89 f5             	mov    %r14,%r13
  4070b4:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
  4070b9:	31 db                	xor    %ebx,%ebx
  4070bb:	89 d1                	mov    %edx,%ecx
  4070bd:	49 89 c6             	mov    %rax,%r14
  4070c0:	e9 03 01 00 00       	jmp    4071c8 <fswap+0x1e8>
  4070c5:	0f 1f 00             	nopl   (%rax)
              struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  4070c8:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
  4070cf:	48 8b 0c 24          	mov    (%rsp),%rcx
  4070d3:	be 01 00 00 00       	mov    $0x1,%esi
  4070d8:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
  4070dd:	48 8b 40 20          	mov    0x20(%rax),%rax
  4070e1:	48 8b 44 08 38       	mov    0x38(%rax,%rcx,1),%rax
  4070e6:	48 03 bc 28 70 01 00 00 	add    0x170(%rax,%rbp,1),%rdi
  4070ee:	e8 7d fe ff ff       	call   406f70 <mailboxkind>
              setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
  4070f3:	48 8b 0c 24          	mov    (%rsp),%rcx
  4070f7:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  4070fc:	31 d2                	xor    %edx,%edx
              struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  4070fe:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
              setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
  407103:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
  40710a:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
  40710f:	48 8b 40 20          	mov    0x20(%rax),%rax
  407113:	48 8b 44 08 38       	mov    0x38(%rax,%rcx,1),%rax
  407118:	48 03 bc 28 70 01 00 00 	add    0x170(%rax,%rbp,1),%rdi
  407120:	e8 7b fe ff ff       	call   406fa0 <setmailboxkind>
              setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest2, LOWER);
  407125:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
  40712c:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
  407131:	31 d2                	xor    %edx,%edx
  407133:	48 8b 40 20          	mov    0x20(%rax),%rax
  407137:	4a 8b 44 30 38       	mov    0x38(%rax,%r14,1),%rax
  40713c:	48 03 b4 18 70 01 00 00 	add    0x170(%rax,%rbx,1),%rsi
  407144:	48 89 f7             	mov    %rsi,%rdi
  407147:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  40714c:	e8 4f fe ff ff       	call   406fa0 <setmailboxkind>
              setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest, HIGHER);
  407151:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
  407156:	ba 01 00 00 00       	mov    $0x1,%edx
  40715b:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
  407162:	48 8b 40 20          	mov    0x20(%rax),%rax
  407166:	4a 8b 44 30 38       	mov    0x38(%rax,%r14,1),%rax
  40716b:	48 03 b4 18 70 01 00 00 	add    0x170(%rax,%rbx,1),%rsi
  407173:	48 89 f7             	mov    %rsi,%rdi
  407176:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
  40717b:	e8 20 fe ff ff       	call   406fa0 <setmailboxkind>
              setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source2, HIGHER);
  407180:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
  407187:	48 8b 0c 24          	mov    (%rsp),%rcx
  40718b:	4c 89 fe             	mov    %r15,%rsi
  40718e:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
  407193:	ba 01 00 00 00       	mov    $0x1,%edx
  407198:	48 8b 40 20          	mov    0x20(%rax),%rax
  40719c:	48 8b 44 08 38       	mov    0x38(%rax,%rcx,1),%rax
  4071a1:	48 03 bc 28 70 01 00 00 	add    0x170(%rax,%rbp,1),%rdi
  4071a9:	e8 f2 fd ff ff       	call   406fa0 <setmailboxkind>
             for (int nn = 0 ; nn < data->thread_count; nn++) {
  4071ae:	41 8b 8d 34 01 00 00 	mov    0x134(%r13),%ecx
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  4071b5:	49 8b b5 28 01 00 00 	mov    0x128(%r13),%rsi
             for (int nn = 0 ; nn < data->thread_count; nn++) {
  4071bc:	41 39 cc             	cmp    %ecx,%r12d
  4071bf:	0f 8d c5 00 00 00    	jge    40728a <fswap+0x2aa>
              int next_task = abs((nn + 1) % (data->thread_count));
  4071c5:	49 63 dc             	movslq %r12d,%rbx
  4071c8:	44 8d 63 01          	lea    0x1(%rbx),%r12d
              struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4071cc:	48 c1 e3 09          	shl    $0x9,%rbx
  4071d0:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
              int next_task = abs((nn + 1) % (data->thread_count));
  4071d5:	44 89 e0             	mov    %r12d,%eax
  4071d8:	99                   	cltd
  4071d9:	f7 f9                	idiv   %ecx
              struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4071db:	48 8b 46 20          	mov    0x20(%rsi),%rax
  4071df:	4a 8b 44 30 38       	mov    0x38(%rax,%r14,1),%rax
  4071e4:	48 8b bc 18 70 01 00 00 	mov    0x170(%rax,%rbx,1),%rdi
  4071ec:	be 01 00 00 00       	mov    $0x1,%esi
  4071f1:	4c 01 ff             	add    %r15,%rdi
              int next_task = abs((nn + 1) % (data->thread_count));
  4071f4:	48 63 ea             	movslq %edx,%rbp
              struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4071f7:	e8 74 fd ff ff       	call   406f70 <mailboxkind>
              struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  4071fc:	31 f6                	xor    %esi,%esi
              struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4071fe:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  407203:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
  40720a:	48 8b 40 20          	mov    0x20(%rax),%rax
  40720e:	4a 8b 44 30 38       	mov    0x38(%rax,%r14,1),%rax
  407213:	48 8b bc 18 70 01 00 00 	mov    0x170(%rax,%rbx,1),%rdi
  40721b:	4c 01 ff             	add    %r15,%rdi
  40721e:	e8 4d fd ff ff       	call   406f70 <mailboxkind>
                if (source2->messages_count != 0) { 
  407223:	48 83 b8 80 00 00 00 00 	cmpq   $0x0,0x80(%rax)
              struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  40722b:	49 89 c7             	mov    %rax,%r15
                if (source2->messages_count != 0) { 
  40722e:	0f 85 84 00 00 00    	jne    4072b8 <fswap+0x2d8>
              struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  407234:	48 8b 0c 24          	mov    (%rsp),%rcx
  407238:	48 c1 e5 09          	shl    $0x9,%rbp
  40723c:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
  407241:	31 f6                	xor    %esi,%esi
              struct Mailbox* __a = &data->thread->all_threads[l2].tasks[l3].mailboxes[l4];
  407243:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
              struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  40724a:	48 8b 40 20          	mov    0x20(%rax),%rax
  40724e:	48 8b 44 08 38       	mov    0x38(%rax,%rcx,1),%rax
  407253:	48 03 bc 28 70 01 00 00 	add    0x170(%rax,%rbp,1),%rdi
  40725b:	e8 10 fd ff ff       	call   406f70 <mailboxkind>
                if (dest->messages_count != 0) { 
  407260:	48 83 b8 80 00 00 00 00 	cmpq   $0x0,0x80(%rax)
  407268:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  40726d:	0f 84 55 fe ff ff    	je     4070c8 <fswap+0xe8>
             for (int nn = 0 ; nn < data->thread_count; nn++) {
  407273:	41 8b 8d 34 01 00 00 	mov    0x134(%r13),%ecx
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  40727a:	49 8b b5 28 01 00 00 	mov    0x128(%r13),%rsi
             for (int nn = 0 ; nn < data->thread_count; nn++) {
  407281:	41 39 cc             	cmp    %ecx,%r12d
  407284:	0f 8c 3b ff ff ff    	jl     4071c5 <fswap+0x1e5>
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  40728a:	8b be d4 00 00 00    	mov    0xd4(%rsi),%edi
  407290:	83 44 24 30 01       	addl   $0x1,0x30(%rsp)
  407295:	4d 89 ee             	mov    %r13,%r14
  407298:	8b 44 24 30          	mov    0x30(%rsp),%eax
  40729c:	39 f8                	cmp    %edi,%eax
  40729e:	0f 8c bd fd ff ff    	jl     407061 <fswap+0x81>
}
  4072a4:	48 83 c4 48          	add    $0x48,%rsp
  4072a8:	31 c0                	xor    %eax,%eax
  4072aa:	5b                   	pop    %rbx
  4072ab:	5d                   	pop    %rbp
  4072ac:	41 5c                	pop    %r12
  4072ae:	41 5d                	pop    %r13
  4072b0:	41 5e                	pop    %r14
  4072b2:	41 5f                	pop    %r15
  4072b4:	c3                   	ret
  4072b5:	0f 1f 00             	nopl   (%rax)
              struct Mailbox* __a = &data->thread->all_threads[l2].tasks[l3].mailboxes[l4];
  4072b8:	49 8b b5 28 01 00 00 	mov    0x128(%r13),%rsi
  4072bf:	4d 89 ee             	mov    %r13,%r14
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
  4072c2:	8b be d4 00 00 00    	mov    0xd4(%rsi),%edi
  4072c8:	e9 83 fd ff ff       	jmp    407050 <fswap+0x70>
  4072cd:	0f 1f 00             	nopl   (%rax)

00000000004072d0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
  4072d0:	41 57                	push   %r15
  4072d2:	41 56                	push   %r14
  4072d4:	41 55                	push   %r13
  4072d6:	41 54                	push   %r12
  4072d8:	55                   	push   %rbp
  4072d9:	53                   	push   %rbx
  4072da:	48 89 fb             	mov    %rdi,%rbx
  4072dd:	48 83 ec 78          	sub    $0x78,%rsp
  struct timespec preempt = {
  4072e1:	66 0f 6f 05 27 1b 00 00 	movdqa 0x1b27(%rip),%xmm0        # 408e10 <_IO_stdin_used+0xe10>
int barriered_work(struct BarrierTask *data) {
  4072e9:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
  4072f2:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  4072f7:	31 c0                	xor    %eax,%eax
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
  4072f9:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  struct timespec preempt = {
  407300:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
  407305:	48 8b 88 00 01 00 00 	mov    0x100(%rax),%rcx
  struct timespec rem = {
  40730c:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
  407311:	8b 11                	mov    (%rcx),%edx
  407313:	83 fa ff             	cmp    $0xffffffff,%edx
  407316:	0f 84 04 05 00 00    	je     407820 <barriered_work+0x550>
  40731c:	3b 90 f8 00 00 00    	cmp    0xf8(%rax),%edx
  407322:	74 2c                	je     407350 <barriered_work+0x80>
}
  407324:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  407329:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
  407332:	0f 85 59 06 00 00    	jne    407991 <barriered_work+0x6c1>
  407338:	48 83 c4 78          	add    $0x78,%rsp
  40733c:	31 c0                	xor    %eax,%eax
  40733e:	5b                   	pop    %rbx
  40733f:	5d                   	pop    %rbp
  407340:	41 5c                	pop    %r12
  407342:	41 5d                	pop    %r13
  407344:	41 5e                	pop    %r14
  407346:	41 5f                	pop    %r15
  407348:	c3                   	ret
  407349:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
  407350:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
  407357:	39 69 04             	cmp    %ebp,0x4(%rcx)
  40735a:	0f 84 b3 05 00 00    	je     407913 <barriered_work+0x643>
          int t = data->task_index;
  407360:	44 8b 7b 04          	mov    0x4(%rbx),%r15d
      receive(data);
  407364:	48 89 df             	mov    %rbx,%rdi
    if (data->thread_index == data->task_index) {
  407367:	41 39 ef             	cmp    %ebp,%r15d
  40736a:	0f 85 08 05 00 00    	jne    407878 <barriered_work+0x5a8>
      receive(data);
  407370:	e8 6b f8 ff ff       	call   406be0 <receive>
        if (data->thread->have_foreign == 1) {
  407375:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
  40737c:	83 b8 08 01 00 00 01 	cmpl   $0x1,0x108(%rax)
  407383:	0f 85 a4 03 00 00    	jne    40772d <barriered_work+0x45d>
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
  407389:	8b b3 40 01 00 00    	mov    0x140(%rbx),%esi
  40738f:	85 f6                	test   %esi,%esi
  407391:	0f 8e 96 03 00 00    	jle    40772d <barriered_work+0x45d>
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
  407397:	49 89 eb             	mov    %rbp,%r11
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
  40739a:	45 31 d2             	xor    %r10d,%r10d
  40739d:	44 89 7c 24 0c       	mov    %r15d,0xc(%rsp)
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
  4073a2:	49 c1 e3 09          	shl    $0x9,%r11
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
  4073a6:	44 89 d5             	mov    %r10d,%ebp
  4073a9:	4d 89 dd             	mov    %r11,%r13
  4073ac:	eb 14                	jmp    4073c2 <barriered_work+0xf2>
  4073ae:	66 90                	xchg   %ax,%ax
  4073b0:	83 c5 01             	add    $0x1,%ebp
  4073b3:	39 f5                	cmp    %esi,%ebp
  4073b5:	0f 8d 6d 03 00 00    	jge    407728 <barriered_work+0x458>
          int b = data->thread->real_thread_index;
  4073bb:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
  4073c2:	44 8b 70 08          	mov    0x8(%rax),%r14d
                if (y == b) { continue; }
  4073c6:	41 39 ee             	cmp    %ebp,%r14d
  4073c9:	74 e5                	je     4073b0 <barriered_work+0xe0>
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
  4073cb:	48 8b 50 20          	mov    0x20(%rax),%rdx
  4073cf:	48 63 c5             	movslq %ebp,%rax
  4073d2:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
  4073d6:	4c 8d 24 48          	lea    (%rax,%rcx,2),%r12
  4073da:	49 c1 e4 04          	shl    $0x4,%r12
  4073de:	4a 8b 7c 22 38       	mov    0x38(%rdx,%r12,1),%rdi
  4073e3:	4c 01 ef             	add    %r13,%rdi
  4073e6:	8b 8f a0 01 00 00    	mov    0x1a0(%rdi),%ecx
  4073ec:	85 c9                	test   %ecx,%ecx
  4073ee:	75 c0                	jne    4073b0 <barriered_work+0xe0>
  4073f0:	4d 63 c6             	movslq %r14d,%r8
  4073f3:	4b 8d 0c c0          	lea    (%r8,%r8,8),%rcx
  4073f7:	49 8d 0c 48          	lea    (%r8,%rcx,2),%rcx
  4073fb:	48 c1 e1 04          	shl    $0x4,%rcx
  4073ff:	49 89 ca             	mov    %rcx,%r10
  407402:	48 8b 4c 0a 38       	mov    0x38(%rdx,%rcx,1),%rcx
  407407:	4c 01 e9             	add    %r13,%rcx
  40740a:	48 89 ca             	mov    %rcx,%rdx
  40740d:	8b 89 a0 01 00 00    	mov    0x1a0(%rcx),%ecx
  407413:	85 c9                	test   %ecx,%ecx
  407415:	75 99                	jne    4073b0 <barriered_work+0xe0>
  407417:	48 c1 e0 08          	shl    $0x8,%rax
  40741b:	49 89 c1             	mov    %rax,%r9
  40741e:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
  407425:	42 83 bc 08 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%r9,1)
  40742e:	75 80                	jne    4073b0 <barriered_work+0xe0>
  407430:	48 8b 87 70 01 00 00 	mov    0x170(%rdi),%rax
  407437:	49 c1 e0 08          	shl    $0x8,%r8
  40743b:	4d 89 c7             	mov    %r8,%r15
  40743e:	42 83 bc 00 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%r8,1)
  407447:	0f 85 63 ff ff ff    	jne    4073b0 <barriered_work+0xe0>
                      int min = minf(b, y); 
  40744d:	89 ee                	mov    %ebp,%esi
  40744f:	44 89 f7             	mov    %r14d,%edi
  407452:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
  407457:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
  40745b:	4c 89 0c 24          	mov    %r9,(%rsp)
  40745f:	e8 3c d2 ff ff       	call   4046a0 <minf>
                      int max = maxf(b, y); 
  407464:	89 ee                	mov    %ebp,%esi
  407466:	44 89 f7             	mov    %r14d,%edi
  407469:	e8 42 d2 ff ff       	call   4046b0 <maxf>
                      for (int nn = 0; nn < data->thread_count; nn++) {
  40746e:	8b 93 34 01 00 00    	mov    0x134(%rbx),%edx
  407474:	4c 8b 0c 24          	mov    (%rsp),%r9
  407478:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
  40747c:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
  407481:	85 d2                	test   %edx,%edx
  407483:	0f 8e 90 02 00 00    	jle    407719 <barriered_work+0x449>
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  407489:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
  407490:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
  407495:	4d 89 ce             	mov    %r9,%r14
  407498:	41 89 d3             	mov    %edx,%r11d
  40749b:	89 6c 24 3c          	mov    %ebp,0x3c(%rsp)
  40749f:	48 8b 40 20          	mov    0x20(%rax),%rax
  4074a3:	4c 89 14 24          	mov    %r10,(%rsp)
  4074a7:	4a 8b 74 10 38       	mov    0x38(%rax,%r10,1),%rsi
  4074ac:	0f 1f 40 00          	nopl   0x0(%rax)
                        int next_task = abs((nn + 1) % data->thread_count);
  4074b0:	48 63 e9             	movslq %ecx,%rbp
  4074b3:	83 c1 01             	add    $0x1,%ecx
  4074b6:	89 c8                	mov    %ecx,%eax
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4074b8:	48 c1 e5 09          	shl    $0x9,%rbp
                        int next_task = abs((nn + 1) % data->thread_count);
  4074bc:	89 4c 24 38          	mov    %ecx,0x38(%rsp)
  4074c0:	99                   	cltd
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4074c1:	48 8b bc 2e 70 01 00 00 	mov    0x170(%rsi,%rbp,1),%rdi
  4074c9:	be 01 00 00 00       	mov    $0x1,%esi
                        int next_task = abs((nn + 1) % data->thread_count);
  4074ce:	41 f7 fb             	idiv   %r11d
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4074d1:	4c 01 f7             	add    %r14,%rdi
                        int next_task = abs((nn + 1) % data->thread_count);
  4074d4:	4c 63 ea             	movslq %edx,%r13
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4074d7:	e8 94 fa ff ff       	call   406f70 <mailboxkind>
                        struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  4074dc:	48 8b 34 24          	mov    (%rsp),%rsi
                        struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  4074e0:	49 c1 e5 09          	shl    $0x9,%r13
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
  4074e4:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
                        struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  4074e9:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
  4074f0:	48 8b 40 20          	mov    0x20(%rax),%rax
  4074f4:	48 8b 44 30 38       	mov    0x38(%rax,%rsi,1),%rax
  4074f9:	31 f6                	xor    %esi,%esi
  4074fb:	48 8b bc 28 70 01 00 00 	mov    0x170(%rax,%rbp,1),%rdi
  407503:	4c 01 f7             	add    %r14,%rdi
  407506:	e8 65 fa ff ff       	call   406f70 <mailboxkind>
                        struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  40750b:	31 f6                	xor    %esi,%esi
                        struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
  40750d:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
                        struct Mailbox* __a = &data->thread->all_threads[l2].tasks[l3].mailboxes[l4];
  407512:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
                        struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  407519:	48 8b 40 20          	mov    0x20(%rax),%rax
  40751d:	4a 8b 44 20 38       	mov    0x38(%rax,%r12,1),%rax
  407522:	4a 8b bc 28 70 01 00 00 	mov    0x170(%rax,%r13,1),%rdi
  40752a:	4c 01 ff             	add    %r15,%rdi
  40752d:	e8 3e fa ff ff       	call   406f70 <mailboxkind>
                        struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  407532:	be 01 00 00 00       	mov    $0x1,%esi
                        struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
  407537:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
                        struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  40753c:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
  407543:	48 8b 40 20          	mov    0x20(%rax),%rax
  407547:	4a 8b 44 20 38       	mov    0x38(%rax,%r12,1),%rax
  40754c:	4a 8b bc 28 70 01 00 00 	mov    0x170(%rax,%r13,1),%rdi
  407554:	4c 01 ff             	add    %r15,%rdi
  407557:	e8 14 fa ff ff       	call   406f70 <mailboxkind>
                          setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
  40755c:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  407561:	31 d2                	xor    %edx,%edx
                        struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
  407563:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
                          setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
  407568:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
  40756f:	48 8b 40 20          	mov    0x20(%rax),%rax
  407573:	4a 8b 44 20 38       	mov    0x38(%rax,%r12,1),%rax
  407578:	4a 8b bc 28 70 01 00 00 	mov    0x170(%rax,%r13,1),%rdi
  407580:	4c 01 ff             	add    %r15,%rdi
  407583:	e8 18 fa ff ff       	call   406fa0 <setmailboxkind>
                          setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source2, HIGHER);
  407588:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
  40758d:	ba 01 00 00 00       	mov    $0x1,%edx
  407592:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
  407599:	48 8b 40 20          	mov    0x20(%rax),%rax
  40759d:	4a 8b 44 20 38       	mov    0x38(%rax,%r12,1),%rax
  4075a2:	4a 8b bc 28 70 01 00 00 	mov    0x170(%rax,%r13,1),%rdi
  4075aa:	4c 01 ff             	add    %r15,%rdi
  4075ad:	e8 ee f9 ff ff       	call   406fa0 <setmailboxkind>
                          setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest2, LOWER);
  4075b2:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
  4075b9:	48 8b 34 24          	mov    (%rsp),%rsi
  4075bd:	31 d2                	xor    %edx,%edx
  4075bf:	48 8b 40 20          	mov    0x20(%rax),%rax
  4075c3:	48 8b 44 30 38       	mov    0x38(%rax,%rsi,1),%rax
  4075c8:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
  4075cd:	48 8b bc 28 70 01 00 00 	mov    0x170(%rax,%rbp,1),%rdi
  4075d5:	4c 01 f7             	add    %r14,%rdi
  4075d8:	e8 c3 f9 ff ff       	call   406fa0 <setmailboxkind>
                          setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest, HIGHER);
  4075dd:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
  4075e4:	48 8b 34 24          	mov    (%rsp),%rsi
  4075e8:	ba 01 00 00 00       	mov    $0x1,%edx
  4075ed:	48 8b 40 20          	mov    0x20(%rax),%rax
  4075f1:	48 8b 44 30 38       	mov    0x38(%rax,%rsi,1),%rax
  4075f6:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  4075fb:	48 8b bc 28 70 01 00 00 	mov    0x170(%rax,%rbp,1),%rdi
  407603:	4c 01 f7             	add    %r14,%rdi
  407606:	e8 95 f9 ff ff       	call   406fa0 <setmailboxkind>
                          data->thread->all_threads[l2].tasks[jj].swap = 1;
  40760b:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
                        for (int jj = 0 ; jj < data->thread_count; jj++) {
  407612:	44 8b 9b 34 01 00 00 	mov    0x134(%rbx),%r11d
                          data->thread->all_threads[l2].tasks[jj].swap = 1;
  407619:	48 8b 34 24          	mov    (%rsp),%rsi
                        for (int jj = 0 ; jj < data->thread_count; jj++) {
  40761d:	8b 4c 24 38          	mov    0x38(%rsp),%ecx
                          data->thread->all_threads[l2].tasks[jj].swap = 1;
  407621:	48 8b 40 20          	mov    0x20(%rax),%rax
                        for (int jj = 0 ; jj < data->thread_count; jj++) {
  407625:	45 85 db             	test   %r11d,%r11d
                          data->thread->all_threads[l2].tasks[jj].swap = 1;
  407628:	48 8b 74 30 38       	mov    0x38(%rax,%rsi,1),%rsi
                          data->thread->all_threads[t2].tasks[jj].swap = 1;
  40762d:	4a 8b 7c 20 38       	mov    0x38(%rax,%r12,1),%rdi
                        for (int jj = 0 ; jj < data->thread_count; jj++) {
  407632:	7e 38                	jle    40766c <barriered_work+0x39c>
  407634:	45 8d 4b ff          	lea    -0x1(%r11),%r9d
                          data->thread->all_threads[t2].tasks[jj].swap = 1;
  407638:	b8 a0 01 00 00       	mov    $0x1a0,%eax
  40763d:	44 89 da             	mov    %r11d,%edx
  407640:	49 c1 e1 09          	shl    $0x9,%r9
  407644:	49 81 c1 a0 03 00 00 	add    $0x3a0,%r9
  40764b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                          data->thread->all_threads[l2].tasks[jj].swap = 1;
  407650:	c7 04 06 01 00 00 00 	movl   $0x1,(%rsi,%rax,1)
                          data->thread->all_threads[t2].tasks[jj].swap = 1;
  407657:	c7 04 07 01 00 00 00 	movl   $0x1,(%rdi,%rax,1)
                        for (int jj = 0 ; jj < data->thread_count; jj++) {
  40765e:	48 05 00 02 00 00    	add    $0x200,%rax
  407664:	4c 39 c8             	cmp    %r9,%rax
  407667:	75 e7                	jne    407650 <barriered_work+0x380>
  407669:	41 89 d3             	mov    %edx,%r11d
                             ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
  40766c:	48 8b 84 2e 70 01 00 00 	mov    0x170(%rsi,%rbp,1),%rax
  407674:	4c 01 f0             	add    %r14,%rax
  407677:	4c 8b 88 80 00 00 00 	mov    0x80(%rax),%r9
                            ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
  40767e:	48 8b 00             	mov    (%rax),%rax
                             ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
  407681:	41 c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r9)
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
  40768c:	4c 8b 8c 2f 70 01 00 00 	mov    0x170(%rdi,%rbp,1),%r9
  407694:	4f 8b 8c 39 80 00 00 00 	mov    0x80(%r9,%r15,1),%r9
  40769c:	41 c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r9)
                            ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
  4076a7:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
  4076b1:	4a 8b 84 2f 70 01 00 00 	mov    0x170(%rdi,%r13,1),%rax
  4076b9:	4a 8b 04 38          	mov    (%rax,%r15,1),%rax
  4076bd:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                      for (int nn = 0; nn < data->thread_count; nn++) {
  4076c7:	44 39 d9             	cmp    %r11d,%ecx
  4076ca:	0f 8c e0 fd ff ff    	jl     4074b0 <barriered_work+0x1e0>
                        for (int nn = 0; nn < data->thread_count; nn++) {
  4076d0:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
  4076d5:	8b 6c 24 3c          	mov    0x3c(%rsp),%ebp
  4076d9:	4d 89 f1             	mov    %r14,%r9
  4076dc:	45 85 db             	test   %r11d,%r11d
  4076df:	7e 38                	jle    407719 <barriered_work+0x449>
  4076e1:	45 8d 43 ff          	lea    -0x1(%r11),%r8d
  4076e5:	b8 70 01 00 00       	mov    $0x170,%eax
  4076ea:	49 c1 e0 09          	shl    $0x9,%r8
  4076ee:	49 81 c0 70 03 00 00 	add    $0x370,%r8
  4076f5:	0f 1f 00             	nopl   (%rax)
                          if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
  4076f8:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
  4076fc:	48 8b 0c 06          	mov    (%rsi,%rax,1),%rcx
  407700:	4a 8b 14 3a          	mov    (%rdx,%r15,1),%rdx
  407704:	4a 39 14 09          	cmp    %rdx,(%rcx,%r9,1)
  407708:	0f 84 88 02 00 00    	je     407996 <barriered_work+0x6c6>
                        for (int nn = 0; nn < data->thread_count; nn++) {
  40770e:	48 05 00 02 00 00    	add    $0x200,%rax
  407714:	4c 39 c0             	cmp    %r8,%rax
  407717:	75 df                	jne    4076f8 <barriered_work+0x428>
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
  407719:	8b b3 40 01 00 00    	mov    0x140(%rbx),%esi
  40771f:	e9 8c fc ff ff       	jmp    4073b0 <barriered_work+0xe0>
  407724:	0f 1f 40 00          	nopl   0x0(%rax)
  407728:	44 8b 7c 24 0c       	mov    0xc(%rsp),%r15d
        fswap(data); 
  40772d:	48 89 df             	mov    %rbx,%rdi
  407730:	e8 ab f8 ff ff       	call   406fe0 <fswap>
        receive(data);
  407735:	48 89 df             	mov    %rbx,%rdi
  407738:	e8 a3 f4 ff ff       	call   406be0 <receive>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
  40773d:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
  407744:	31 ff                	xor    %edi,%edi
  407746:	48 c1 e6 05          	shl    $0x5,%rsi
  40774a:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
  407751:	e8 1a a9 ff ff       	call   402070 <clock_gettime@plt>
      int modcount = ++data->thread->protected_state->modcount;
  407756:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
  40775d:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      int modcount = ++data->thread->protected_state->modcount;
  407764:	48 8b 50 48          	mov    0x48(%rax),%rdx
  407768:	8b 72 10             	mov    0x10(%rdx),%esi
  40776b:	8d 6e 01             	lea    0x1(%rsi),%ebp
  40776e:	89 6a 10             	mov    %ebp,0x10(%rdx)
      while (data->scheduled == 1) {
  407771:	75 53                	jne    4077c6 <barriered_work+0x4f6>
  407773:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
  407778:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
  40777f:	48 8b 40 18          	mov    0x18(%rax),%rax
  407783:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
        data->n++;
  407787:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
  40778f:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
  407793:	48 c1 e7 09          	shl    $0x9,%rdi
  407797:	48 03 78 38          	add    0x38(%rax),%rdi
  40779b:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      while (data->scheduled == 1) {
  4077a1:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      if (modcount != data->thread->protected_state->modcount) {
  4077a8:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
  4077af:	74 c7                	je     407778 <barriered_work+0x4a8>
      if (modcount != data->thread->protected_state->modcount) {
  4077b1:	48 8b 40 48          	mov    0x48(%rax),%rax
  4077b5:	3b 68 10             	cmp    0x10(%rax),%ebp
  4077b8:	74 0c                	je     4077c6 <barriered_work+0x4f6>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
  4077ba:	48 8d 3d d3 0a 00 00 	lea    0xad3(%rip),%rdi        # 408294 <_IO_stdin_used+0x294>
  4077c1:	e8 8a a8 ff ff       	call   402050 <puts@plt>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
  4077c6:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
  4077cd:	31 ff                	xor    %edi,%edi
  4077cf:	48 c1 e6 05          	shl    $0x5,%rsi
  4077d3:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
  4077da:	48 83 c6 10          	add    $0x10,%rsi
  4077de:	e8 8d a8 ff ff       	call   402070 <clock_gettime@plt>
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
  4077e3:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
  4077ea:	48 83 c0 01          	add    $0x1,%rax
  4077ee:	48 99                	cqto
  4077f0:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    if (t == data->thread_count - 1) {
  4077f7:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
  4077fd:	83 e8 01             	sub    $0x1,%eax
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
  407800:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    if (t == data->thread_count - 1) {
  407807:	44 39 f8             	cmp    %r15d,%eax
  40780a:	0f 84 ab 00 00 00    	je     4078bb <barriered_work+0x5eb>
    data->swap = 0;
  407810:	c7 83 a0 01 00 00 00 00 00 00 	movl   $0x0,0x1a0(%rbx)
    return 0;
  40781a:	e9 05 fb ff ff       	jmp    407324 <barriered_work+0x54>
  40781f:	90                   	nop
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
  407820:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
  407827:	85 ed                	test   %ebp,%ebp
  407829:	0f 85 31 fb ff ff    	jne    407360 <barriered_work+0x90>
  40782f:	8b b0 f8 00 00 00    	mov    0xf8(%rax),%esi
  407835:	85 f6                	test   %esi,%esi
  407837:	0f 85 23 fb ff ff    	jne    407360 <barriered_work+0x90>
  40783d:	48 63 ab 80 00 00 00 	movslq 0x80(%rbx),%rbp
  407844:	48 89 e8             	mov    %rbp,%rax
  407847:	48 69 ed 89 b5 f8 14 	imul   $0x14f8b589,%rbp,%rbp
  40784e:	99                   	cltd
  40784f:	48 c1 fd 2d          	sar    $0x2d,%rbp
  407853:	29 d5                	sub    %edx,%ebp
  407855:	69 d5 a0 86 01 00    	imul   $0x186a0,%ebp,%edx
  40785b:	29 d0                	sub    %edx,%eax
  40785d:	48 63 e8             	movslq %eax,%rbp
  407860:	0f 85 24 01 00 00    	jne    40798a <barriered_work+0x6ba>
      data->thread->global->request_group_sync = 0;
  407866:	48 c7 01 00 00 00 00 	movq   $0x0,(%rcx)
  40786d:	e9 ee fa ff ff       	jmp    407360 <barriered_work+0x90>
  407872:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      receive(data);
  407878:	e8 63 f3 ff ff       	call   406be0 <receive>
      while (data->scheduled == 1) {
  40787d:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
  407884:	75 1b                	jne    4078a1 <barriered_work+0x5d1>
  407886:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        data->n++;
  407890:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      while (data->scheduled == 1) {
  407898:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
  40789f:	74 ef                	je     407890 <barriered_work+0x5c0>
      sendm(data);
  4078a1:	48 89 df             	mov    %rbx,%rdi
  4078a4:	e8 87 f4 ff ff       	call   406d30 <sendm>
    if (t == data->thread_count - 1) {
  4078a9:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
  4078af:	83 e8 01             	sub    $0x1,%eax
  4078b2:	44 39 f8             	cmp    %r15d,%eax
  4078b5:	0f 85 55 ff ff ff    	jne    407810 <barriered_work+0x540>
        for (int tt = 0 ; tt < data->task_count ; tt++) {
  4078bb:	8b 93 48 01 00 00    	mov    0x148(%rbx),%edx
  4078c1:	85 d2                	test   %edx,%edx
  4078c3:	0f 8e 47 ff ff ff    	jle    407810 <barriered_work+0x540>
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
  4078c9:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
  4078d0:	83 ea 01             	sub    $0x1,%edx
  4078d3:	48 c1 e2 09          	shl    $0x9,%rdx
  4078d7:	48 63 41 08          	movslq 0x8(%rcx),%rax
  4078db:	48 8d 34 c0          	lea    (%rax,%rax,8),%rsi
  4078df:	48 8d 04 70          	lea    (%rax,%rsi,2),%rax
  4078e3:	48 c1 e0 04          	shl    $0x4,%rax
  4078e7:	48 03 41 20          	add    0x20(%rcx),%rax
  4078eb:	48 8b 48 38          	mov    0x38(%rax),%rcx
  4078ef:	48 8d 81 a4 01 00 00 	lea    0x1a4(%rcx),%rax
  4078f6:	48 8d 94 11 a4 03 00 00 	lea    0x3a4(%rcx,%rdx,1),%rdx
  4078fe:	66 90                	xchg   %ax,%ax
  407900:	83 00 01             	addl   $0x1,(%rax)
        for (int tt = 0 ; tt < data->task_count ; tt++) {
  407903:	48 05 00 02 00 00    	add    $0x200,%rax
  407909:	48 39 d0             	cmp    %rdx,%rax
  40790c:	75 f2                	jne    407900 <barriered_work+0x630>
  40790e:	e9 fd fe ff ff       	jmp    407810 <barriered_work+0x540>
      struct ProtectedState *protected = data->thread->global->protected_state;
  407913:	48 8b 69 08          	mov    0x8(%rcx),%rbp
      nanosleep(&preempt , &rem);
  407917:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
  40791c:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
      int modcount = ++protected->modcount;
  407921:	8b 45 10             	mov    0x10(%rbp),%eax
      protected->protected++;
  407924:	48 83 45 00 01       	addq   $0x1,0x0(%rbp)
      int modcount = ++protected->modcount;
  407929:	44 8d 60 01          	lea    0x1(%rax),%r12d
  40792d:	44 89 65 10          	mov    %r12d,0x10(%rbp)
      nanosleep(&preempt , &rem);
  407931:	e8 8a a7 ff ff       	call   4020c0 <nanosleep@plt>
      if (protected->modcount != modcount) {
  407936:	44 3b 65 10          	cmp    0x10(%rbp),%r12d
  40793a:	74 0c                	je     407948 <barriered_work+0x678>
  40793c:	48 8d 3d 19 09 00 00 	lea    0x919(%rip),%rdi        # 40825c <_IO_stdin_used+0x25c>
  407943:	e8 08 a7 ff ff       	call   402050 <puts@plt>
      data->thread->global->request_thread_sync = (data->thread_index + 1) % data->thread_count;
  407948:	48 63 ab 30 01 00 00 	movslq 0x130(%rbx),%rbp
  40794f:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
  407956:	8d 45 01             	lea    0x1(%rbp),%eax
  407959:	48 8b b1 00 01 00 00 	mov    0x100(%rcx),%rsi
  407960:	99                   	cltd
  407961:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
  407967:	89 56 04             	mov    %edx,0x4(%rsi)
      if (data->thread_index == 1) {
  40796a:	83 fd 01             	cmp    $0x1,%ebp
  40796d:	0f 85 ed f9 ff ff    	jne    407360 <barriered_work+0x90>
        data->thread->global->request_group_sync = (data->thread->group + 1) % data->thread->group_count;
  407973:	8b 81 f8 00 00 00    	mov    0xf8(%rcx),%eax
  407979:	83 c0 01             	add    $0x1,%eax
  40797c:	99                   	cltd
  40797d:	f7 b9 d0 00 00 00    	idivl  0xd0(%rcx)
  407983:	89 16                	mov    %edx,(%rsi)
  407985:	e9 d6 f9 ff ff       	jmp    407360 <barriered_work+0x90>
  40798a:	31 ed                	xor    %ebp,%ebp
  40798c:	e9 cf f9 ff ff       	jmp    407360 <barriered_work+0x90>
}
  407991:	e8 0a a7 ff ff       	call   4020a0 <__stack_chk_fail@plt>
  407996:	bf 01 00 00 00       	mov    $0x1,%edi
  40799b:	48 8d 35 d7 08 00 00 	lea    0x8d7(%rip),%rsi        # 408279 <_IO_stdin_used+0x279>
  4079a2:	31 c0                	xor    %eax,%eax
  4079a4:	e8 27 a8 ff ff       	call   4021d0 <__printf_chk@plt>
                            exit(1);
  4079a9:	bf 01 00 00 00       	mov    $0x1,%edi
  4079ae:	e8 8d a8 ff ff       	call   402240 <exit@plt>
  4079b3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4079be:	66 90                	xchg   %ax,%ax

00000000004079c0 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
  4079c0:	55                   	push   %rbp
  4079c1:	48 89 fd             	mov    %rdi,%rbp
  barriered_work_ingest(data);
  4079c4:	e8 57 ee ff ff       	call   406820 <barriered_work_ingest>
  barriered_work(data);
  4079c9:	48 89 ef             	mov    %rbp,%rdi
}
  4079cc:	5d                   	pop    %rbp
  barriered_work(data);
  4079cd:	e9 fe f8 ff ff       	jmp    4072d0 <barriered_work>
  4079d2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4079dd:	0f 1f 00             	nopl   (%rax)

00000000004079e0 <barriered_nulltask>:
}
  4079e0:	31 c0                	xor    %eax,%eax
  4079e2:	c3                   	ret
  4079e3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4079ee:	66 90                	xchg   %ax,%ax

00000000004079f0 <barriered_steal>:
  4079f0:	31 c0                	xor    %eax,%eax
  4079f2:	c3                   	ret
  4079f3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
  4079fe:	66 90                	xchg   %ax,%ax

0000000000407a00 <after>:
  return left.tv_sec > right.tv_sec &&
  407a00:	31 c0                	xor    %eax,%eax
  407a02:	48 39 d7             	cmp    %rdx,%rdi
  407a05:	7e 08                	jle    407a0f <after+0xf>
  407a07:	31 c0                	xor    %eax,%eax
  407a09:	48 39 ce             	cmp    %rcx,%rsi
  407a0c:	0f 9f c0             	setg   %al
}
  407a0f:	c3                   	ret

0000000000407a10 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
  407a10:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
  407a15:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
  407a1a:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
  407a1c:	48 39 d7             	cmp    %rdx,%rdi
  407a1f:	7f 18                	jg     407a39 <within+0x29>
  407a21:	4d 39 d8             	cmp    %r11,%r8
  407a24:	0f 9e c2             	setle  %dl
  407a27:	48 39 ce             	cmp    %rcx,%rsi
  407a2a:	0f 9e c0             	setle  %al
  407a2d:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
  407a2f:	31 c0                	xor    %eax,%eax
  407a31:	4d 39 d1             	cmp    %r10,%r9
  407a34:	0f 9e c0             	setle  %al
    return 1;
  407a37:	21 d0                	and    %edx,%eax
}
  407a39:	c3                   	ret
  407a3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000407a40 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
  407a40:	48 83 ec 08          	sub    $0x8,%rsp
  if (after(left.start, right.start) && after(right.end, left.end)) {
  407a44:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  407a49:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
  407a4e:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
  407a53:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
  407a58:	e8 a3 ff ff ff       	call   407a00 <after>
  407a5d:	85 c0                	test   %eax,%eax
  407a5f:	74 21                	je     407a82 <overlap+0x42>
  407a61:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  407a66:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
  407a6b:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
  407a70:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
  407a75:	e8 86 ff ff ff       	call   407a00 <after>
  407a7a:	85 c0                	test   %eax,%eax
  407a7c:	0f 85 ae 00 00 00    	jne    407b30 <overlap+0xf0>
  if (after(right.start, left.start) && after(left.end, right.end)) {
  407a82:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
  407a87:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
  407a8c:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
  407a91:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
  407a96:	e8 65 ff ff ff       	call   407a00 <after>
  407a9b:	85 c0                	test   %eax,%eax
  407a9d:	74 1d                	je     407abc <overlap+0x7c>
  407a9f:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
  407aa4:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
  407aa9:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
  407aae:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  407ab3:	e8 48 ff ff ff       	call   407a00 <after>
  407ab8:	85 c0                	test   %eax,%eax
  407aba:	75 74                	jne    407b30 <overlap+0xf0>
  if (within(left.start, right.start, right.end, left.end) == 1) {
  407abc:	ff 74 24 28          	push   0x28(%rsp)
  407ac0:	ff 74 24 28          	push   0x28(%rsp)
  407ac4:	4c 8b 44 24 50       	mov    0x50(%rsp),%r8
  407ac9:	4c 8b 4c 24 58       	mov    0x58(%rsp),%r9
  407ace:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
  407ad3:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
  407ad8:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
  407add:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  407ae2:	e8 29 ff ff ff       	call   407a10 <within>
  407ae7:	5e                   	pop    %rsi
  407ae8:	5f                   	pop    %rdi
  407ae9:	83 f8 01             	cmp    $0x1,%eax
  407aec:	74 42                	je     407b30 <overlap+0xf0>
  if (within(right.start, left.start, left.end, right.end) == 1) {
  407aee:	ff 74 24 48          	push   0x48(%rsp)
  407af2:	ff 74 24 48          	push   0x48(%rsp)
  407af6:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
  407afb:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
  407b00:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  407b05:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
  407b0a:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
  407b0f:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
  407b14:	e8 f7 fe ff ff       	call   407a10 <within>
  407b19:	5a                   	pop    %rdx
  407b1a:	59                   	pop    %rcx
  407b1b:	83 f8 01             	cmp    $0x1,%eax
  407b1e:	0f 94 c0             	sete   %al
}
  407b21:	48 83 c4 08          	add    $0x8,%rsp
  if (within(right.start, left.start, left.end, right.end) == 1) {
  407b25:	0f b6 c0             	movzbl %al,%eax
}
  407b28:	c3                   	ret
  407b29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    return 1;
  407b30:	b8 01 00 00 00       	mov    $0x1,%eax
}
  407b35:	48 83 c4 08          	add    $0x8,%rsp
  407b39:	c3                   	ret
  407b3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000407b40 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
  407b40:	41 57                	push   %r15
  407b42:	48 89 f8             	mov    %rdi,%rax
  407b45:	41 56                	push   %r14
  407b47:	41 55                	push   %r13
  407b49:	41 54                	push   %r12
  407b4b:	55                   	push   %rbp
  407b4c:	53                   	push   %rbx
  407b4d:	48 83 ec 38          	sub    $0x38,%rsp
  407b51:	89 74 24 2c          	mov    %esi,0x2c(%rsp)
  for (int x = 0 ; x < thread_count; x++) {
  407b55:	85 f6                	test   %esi,%esi
  407b57:	0f 8e 7f 02 00 00    	jle    407ddc <verify+0x29c>
  407b5d:	48 83 c0 38          	add    $0x38,%rax
  407b61:	c7 44 24 1c 00 00 00 00 	movl   $0x0,0x1c(%rsp)
  407b69:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  407b6e:	49 89 c7             	mov    %rax,%r15
    for (int z = 0 ; z < thread_count; z++) {
  407b71:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
  407b79:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
  407b7e:	8b 7c 24 28          	mov    0x28(%rsp),%edi
      if (z != x)  {
  407b82:	39 7c 24 1c          	cmp    %edi,0x1c(%rsp)
  407b86:	0f 84 79 01 00 00    	je     407d05 <verify+0x1c5>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
  407b8c:	41 8b 57 08          	mov    0x8(%r15),%edx
  407b90:	85 d2                	test   %edx,%edx
  407b92:	0f 8e 6d 01 00 00    	jle    407d05 <verify+0x1c5>
  407b98:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
  407ba0:	8b 54 24 1c          	mov    0x1c(%rsp),%edx
  407ba4:	48 8d 35 f9 06 00 00 	lea    0x6f9(%rip),%rsi        # 4082a4 <_IO_stdin_used+0x2a4>
  407bab:	bf 01 00 00 00       	mov    $0x1,%edi
  407bb0:	31 c0                	xor    %eax,%eax
  407bb2:	e8 19 a6 ff ff       	call   4021d0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  407bb7:	41 8b 46 08          	mov    0x8(%r14),%eax
  407bbb:	85 c0                	test   %eax,%eax
  407bbd:	0f 8e 2f 01 00 00    	jle    407cf2 <verify+0x1b2>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
  407bc3:	48 63 6c 24 18       	movslq 0x18(%rsp),%rbp
  407bc8:	49 8b 0f             	mov    (%r15),%rcx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  407bcb:	c7 44 24 14 00 00 00 00 	movl   $0x0,0x14(%rsp)
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
  407bd3:	48 c1 e5 09          	shl    $0x9,%rbp
  407bd7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  407be0:	4c 63 64 24 14       	movslq 0x14(%rsp),%r12
  407be5:	49 8b 06             	mov    (%r14),%rax
  407be8:	48 8d 35 ca 06 00 00 	lea    0x6ca(%rip),%rsi        # 4082b9 <_IO_stdin_used+0x2b9>
  407bef:	bf 01 00 00 00       	mov    $0x1,%edi
  407bf4:	48 8b 8c 29 60 01 00 00 	mov    0x160(%rcx,%rbp,1),%rcx
  407bfc:	4c 89 e3             	mov    %r12,%rbx
  407bff:	48 c1 e3 09          	shl    $0x9,%rbx
  407c03:	48 8b 94 18 60 01 00 00 	mov    0x160(%rax,%rbx,1),%rdx
  407c0b:	31 c0                	xor    %eax,%eax
  407c0d:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
  407c12:	e8 b9 a5 ff ff       	call   4021d0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  407c17:	49 8b 0f             	mov    (%r15),%rcx
  407c1a:	48 8b 94 29 60 01 00 00 	mov    0x160(%rcx,%rbp,1),%rdx
  407c22:	48 85 d2             	test   %rdx,%rdx
  407c25:	0f 8e b4 00 00 00    	jle    407cdf <verify+0x19f>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  407c2b:	49 8b 06             	mov    (%r14),%rax
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  407c2e:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  407c36:	48 8b b4 18 60 01 00 00 	mov    0x160(%rax,%rbx,1),%rsi
  407c3e:	48 01 d8             	add    %rbx,%rax
  407c41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  407c48:	48 85 f6             	test   %rsi,%rsi
  407c4b:	0f 8e 4f 01 00 00    	jle    407da0 <verify+0x260>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
  407c51:	48 63 5c 24 10       	movslq 0x10(%rsp),%rbx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  407c56:	45 31 ed             	xor    %r13d,%r13d
  407c59:	31 d2                	xor    %edx,%edx
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
  407c5b:	48 c1 e3 05          	shl    $0x5,%rbx
  407c5f:	90                   	nop
  407c60:	48 8b 80 50 01 00 00 	mov    0x150(%rax),%rax
  407c67:	48 c1 e2 05          	shl    $0x5,%rdx
  407c6b:	49 89 d4             	mov    %rdx,%r12
  407c6e:	ff 74 10 18          	push   0x18(%rax,%rdx,1)
  407c72:	ff 74 10 10          	push   0x10(%rax,%rdx,1)
  407c76:	ff 74 10 08          	push   0x8(%rax,%rdx,1)
  407c7a:	ff 34 10             	push   (%rax,%rdx,1)
  407c7d:	48 8b 84 29 50 01 00 00 	mov    0x150(%rcx,%rbp,1),%rax
  407c85:	ff 74 18 18          	push   0x18(%rax,%rbx,1)
  407c89:	ff 74 18 10          	push   0x10(%rax,%rbx,1)
  407c8d:	ff 74 18 08          	push   0x8(%rax,%rbx,1)
  407c91:	ff 34 18             	push   (%rax,%rbx,1)
  407c94:	e8 a7 fd ff ff       	call   407a40 <overlap>
  407c99:	48 83 c4 40          	add    $0x40,%rsp
  407c9d:	83 f8 01             	cmp    $0x1,%eax
  407ca0:	0f 84 8a 00 00 00    	je     407d30 <verify+0x1f0>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  407ca6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  407cab:	49 03 06             	add    (%r14),%rax
  407cae:	41 83 c5 01          	add    $0x1,%r13d
  407cb2:	48 8b b0 60 01 00 00 	mov    0x160(%rax),%rsi
  407cb9:	49 63 d5             	movslq %r13d,%rdx
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  407cbc:	49 8b 0f             	mov    (%r15),%rcx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  407cbf:	48 39 f2             	cmp    %rsi,%rdx
  407cc2:	7c 9c                	jl     407c60 <verify+0x120>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  407cc4:	83 44 24 10 01       	addl   $0x1,0x10(%rsp)
  407cc9:	48 8b 94 29 60 01 00 00 	mov    0x160(%rcx,%rbp,1),%rdx
  407cd1:	48 63 7c 24 10       	movslq 0x10(%rsp),%rdi
  407cd6:	48 39 d7             	cmp    %rdx,%rdi
  407cd9:	0f 8c 69 ff ff ff    	jl     407c48 <verify+0x108>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  407cdf:	83 44 24 14 01       	addl   $0x1,0x14(%rsp)
  407ce4:	8b 44 24 14          	mov    0x14(%rsp),%eax
  407ce8:	41 39 46 08          	cmp    %eax,0x8(%r14)
  407cec:	0f 8f ee fe ff ff    	jg     407be0 <verify+0xa0>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
  407cf2:	83 44 24 18 01       	addl   $0x1,0x18(%rsp)
  407cf7:	8b 44 24 18          	mov    0x18(%rsp),%eax
  407cfb:	41 39 47 08          	cmp    %eax,0x8(%r15)
  407cff:	0f 8f 9b fe ff ff    	jg     407ba0 <verify+0x60>
    for (int z = 0 ; z < thread_count; z++) {
  407d05:	8b 44 24 28          	mov    0x28(%rsp),%eax
  407d09:	49 81 c6 30 01 00 00 	add    $0x130,%r14
  407d10:	83 c0 01             	add    $0x1,%eax
  407d13:	39 44 24 2c          	cmp    %eax,0x2c(%rsp)
  407d17:	0f 84 d0 00 00 00    	je     407ded <verify+0x2ad>
  407d1d:	89 44 24 28          	mov    %eax,0x28(%rsp)
  407d21:	89 c7                	mov    %eax,%edi
  407d23:	e9 5a fe ff ff       	jmp    407b82 <verify+0x42>
  407d28:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
  407d30:	49 8b 06             	mov    (%r14),%rax
  407d33:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  407d38:	41 83 c5 01          	add    $0x1,%r13d
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
  407d3c:	4c 03 a4 38 50 01 00 00 	add    0x150(%rax,%rdi,1),%r12
  407d44:	49 8b 07             	mov    (%r15),%rax
  407d47:	bf 01 00 00 00       	mov    $0x1,%edi
  407d4c:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
  407d51:	4d 8b 4c 24 18       	mov    0x18(%r12),%r9
  407d56:	48 8b b4 28 50 01 00 00 	mov    0x150(%rax,%rbp,1),%rsi
  407d5e:	31 c0                	xor    %eax,%eax
  407d60:	48 01 de             	add    %rbx,%rsi
  407d63:	48 8b 16             	mov    (%rsi),%rdx
  407d66:	4c 8b 46 08          	mov    0x8(%rsi),%r8
  407d6a:	48 8d 35 d7 0a 00 00 	lea    0xad7(%rip),%rsi        # 408848 <_IO_stdin_used+0x848>
  407d71:	e8 5a a4 ff ff       	call   4021d0 <__printf_chk@plt>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  407d76:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  407d7b:	49 03 06             	add    (%r14),%rax
  407d7e:	49 63 d5             	movslq %r13d,%rdx
  407d81:	48 8b b0 60 01 00 00 	mov    0x160(%rax),%rsi
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  407d88:	49 8b 0f             	mov    (%r15),%rcx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
  407d8b:	48 39 d6             	cmp    %rdx,%rsi
  407d8e:	0f 8f cc fe ff ff    	jg     407c60 <verify+0x120>
  407d94:	e9 2b ff ff ff       	jmp    407cc4 <verify+0x184>
  407d99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
  407da0:	44 8b 6c 24 10       	mov    0x10(%rsp),%r13d
  407da5:	41 83 c5 01          	add    $0x1,%r13d
  407da9:	49 63 c5             	movslq %r13d,%rax
  407dac:	48 39 d0             	cmp    %rdx,%rax
  407daf:	0f 8d 2a ff ff ff    	jge    407cdf <verify+0x19f>
  407db5:	0f 1f 00             	nopl   (%rax)
  407db8:	41 83 c5 01          	add    $0x1,%r13d
  407dbc:	49 63 c5             	movslq %r13d,%rax
  407dbf:	48 39 c2             	cmp    %rax,%rdx
  407dc2:	7f f4                	jg     407db8 <verify+0x278>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
  407dc4:	83 44 24 14 01       	addl   $0x1,0x14(%rsp)
  407dc9:	8b 44 24 14          	mov    0x14(%rsp),%eax
  407dcd:	41 39 46 08          	cmp    %eax,0x8(%r14)
  407dd1:	0f 8f 09 fe ff ff    	jg     407be0 <verify+0xa0>
  407dd7:	e9 16 ff ff ff       	jmp    407cf2 <verify+0x1b2>
}
  407ddc:	48 83 c4 38          	add    $0x38,%rsp
  407de0:	31 c0                	xor    %eax,%eax
  407de2:	5b                   	pop    %rbx
  407de3:	5d                   	pop    %rbp
  407de4:	41 5c                	pop    %r12
  407de6:	41 5d                	pop    %r13
  407de8:	41 5e                	pop    %r14
  407dea:	41 5f                	pop    %r15
  407dec:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
  407ded:	8b 7c 24 1c          	mov    0x1c(%rsp),%edi
  407df1:	49 81 c7 30 01 00 00 	add    $0x130,%r15
  407df8:	8d 47 01             	lea    0x1(%rdi),%eax
  407dfb:	3b 7c 24 28          	cmp    0x28(%rsp),%edi
  407dff:	74 db                	je     407ddc <verify+0x29c>
  407e01:	89 44 24 1c          	mov    %eax,0x1c(%rsp)
  407e05:	e9 67 fd ff ff       	jmp    407b71 <verify+0x31>

Disassembly of section .fini:

0000000000407e0c <_fini>:
  407e0c:	f3 0f 1e fa          	endbr64
  407e10:	48 83 ec 08          	sub    $0x8,%rsp
  407e14:	48 83 c4 08          	add    $0x8,%rsp
  407e18:	c3                   	ret
