
multibarrier-nowork:     file format elf64-x86-64


Disassembly of section .init:

0000000000002000 <_init>:
    2000:	f3 0f 1e fa          	endbr64
    2004:	48 83 ec 08          	sub    $0x8,%rsp
    2008:	48 8d 05 b1 15 00 00 	lea    0x15b1(%rip),%rax        # 35c0 <__gmon_start__>
    200f:	48 85 c0             	test   %rax,%rax
    2012:	74 02                	je     2016 <_init+0x16>
    2014:	ff d0                	call   *%rax
    2016:	48 83 c4 08          	add    $0x8,%rsp
    201a:	c3                   	ret

Disassembly of section .plt:

0000000000002020 <.plt>:
    2020:	ff 35 4a 7e 00 00    	push   0x7e4a(%rip)        # 9e70 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 4c 7e 00 00    	jmp    *0x7e4c(%rip)        # 9e78 <_GLOBAL_OFFSET_TABLE_+0x10>
    202c:	0f 1f 40 00          	nopl   0x0(%rax)
    2030:	f3 0f 1e fa          	endbr64
    2034:	68 00 00 00 00       	push   $0x0
    2039:	e9 e2 ff ff ff       	jmp    2020 <_init+0x20>
    203e:	66 90                	xchg   %ax,%ax
    2040:	f3 0f 1e fa          	endbr64
    2044:	68 01 00 00 00       	push   $0x1
    2049:	e9 d2 ff ff ff       	jmp    2020 <_init+0x20>
    204e:	66 90                	xchg   %ax,%ax
    2050:	f3 0f 1e fa          	endbr64
    2054:	68 02 00 00 00       	push   $0x2
    2059:	e9 c2 ff ff ff       	jmp    2020 <_init+0x20>
    205e:	66 90                	xchg   %ax,%ax
    2060:	f3 0f 1e fa          	endbr64
    2064:	68 03 00 00 00       	push   $0x3
    2069:	e9 b2 ff ff ff       	jmp    2020 <_init+0x20>
    206e:	66 90                	xchg   %ax,%ax
    2070:	f3 0f 1e fa          	endbr64
    2074:	68 04 00 00 00       	push   $0x4
    2079:	e9 a2 ff ff ff       	jmp    2020 <_init+0x20>
    207e:	66 90                	xchg   %ax,%ax
    2080:	f3 0f 1e fa          	endbr64
    2084:	68 05 00 00 00       	push   $0x5
    2089:	e9 92 ff ff ff       	jmp    2020 <_init+0x20>
    208e:	66 90                	xchg   %ax,%ax
    2090:	f3 0f 1e fa          	endbr64
    2094:	68 06 00 00 00       	push   $0x6
    2099:	e9 82 ff ff ff       	jmp    2020 <_init+0x20>
    209e:	66 90                	xchg   %ax,%ax
    20a0:	f3 0f 1e fa          	endbr64
    20a4:	68 07 00 00 00       	push   $0x7
    20a9:	e9 72 ff ff ff       	jmp    2020 <_init+0x20>
    20ae:	66 90                	xchg   %ax,%ax
    20b0:	f3 0f 1e fa          	endbr64
    20b4:	68 08 00 00 00       	push   $0x8
    20b9:	e9 62 ff ff ff       	jmp    2020 <_init+0x20>
    20be:	66 90                	xchg   %ax,%ax
    20c0:	f3 0f 1e fa          	endbr64
    20c4:	68 09 00 00 00       	push   $0x9
    20c9:	e9 52 ff ff ff       	jmp    2020 <_init+0x20>
    20ce:	66 90                	xchg   %ax,%ax
    20d0:	f3 0f 1e fa          	endbr64
    20d4:	68 0a 00 00 00       	push   $0xa
    20d9:	e9 42 ff ff ff       	jmp    2020 <_init+0x20>
    20de:	66 90                	xchg   %ax,%ax
    20e0:	f3 0f 1e fa          	endbr64
    20e4:	68 0b 00 00 00       	push   $0xb
    20e9:	e9 32 ff ff ff       	jmp    2020 <_init+0x20>
    20ee:	66 90                	xchg   %ax,%ax
    20f0:	f3 0f 1e fa          	endbr64
    20f4:	68 0c 00 00 00       	push   $0xc
    20f9:	e9 22 ff ff ff       	jmp    2020 <_init+0x20>
    20fe:	66 90                	xchg   %ax,%ax
    2100:	f3 0f 1e fa          	endbr64
    2104:	68 0d 00 00 00       	push   $0xd
    2109:	e9 12 ff ff ff       	jmp    2020 <_init+0x20>
    210e:	66 90                	xchg   %ax,%ax
    2110:	f3 0f 1e fa          	endbr64
    2114:	68 0e 00 00 00       	push   $0xe
    2119:	e9 02 ff ff ff       	jmp    2020 <_init+0x20>
    211e:	66 90                	xchg   %ax,%ax
    2120:	f3 0f 1e fa          	endbr64
    2124:	68 0f 00 00 00       	push   $0xf
    2129:	e9 f2 fe ff ff       	jmp    2020 <_init+0x20>
    212e:	66 90                	xchg   %ax,%ax
    2130:	f3 0f 1e fa          	endbr64
    2134:	68 10 00 00 00       	push   $0x10
    2139:	e9 e2 fe ff ff       	jmp    2020 <_init+0x20>
    213e:	66 90                	xchg   %ax,%ax
    2140:	f3 0f 1e fa          	endbr64
    2144:	68 11 00 00 00       	push   $0x11
    2149:	e9 d2 fe ff ff       	jmp    2020 <_init+0x20>
    214e:	66 90                	xchg   %ax,%ax
    2150:	f3 0f 1e fa          	endbr64
    2154:	68 12 00 00 00       	push   $0x12
    2159:	e9 c2 fe ff ff       	jmp    2020 <_init+0x20>
    215e:	66 90                	xchg   %ax,%ax
    2160:	f3 0f 1e fa          	endbr64
    2164:	68 13 00 00 00       	push   $0x13
    2169:	e9 b2 fe ff ff       	jmp    2020 <_init+0x20>
    216e:	66 90                	xchg   %ax,%ax
    2170:	f3 0f 1e fa          	endbr64
    2174:	68 14 00 00 00       	push   $0x14
    2179:	e9 a2 fe ff ff       	jmp    2020 <_init+0x20>
    217e:	66 90                	xchg   %ax,%ax
    2180:	f3 0f 1e fa          	endbr64
    2184:	68 15 00 00 00       	push   $0x15
    2189:	e9 92 fe ff ff       	jmp    2020 <_init+0x20>
    218e:	66 90                	xchg   %ax,%ax
    2190:	f3 0f 1e fa          	endbr64
    2194:	68 16 00 00 00       	push   $0x16
    2199:	e9 82 fe ff ff       	jmp    2020 <_init+0x20>
    219e:	66 90                	xchg   %ax,%ax
    21a0:	f3 0f 1e fa          	endbr64
    21a4:	68 17 00 00 00       	push   $0x17
    21a9:	e9 72 fe ff ff       	jmp    2020 <_init+0x20>
    21ae:	66 90                	xchg   %ax,%ax
    21b0:	f3 0f 1e fa          	endbr64
    21b4:	68 18 00 00 00       	push   $0x18
    21b9:	e9 62 fe ff ff       	jmp    2020 <_init+0x20>
    21be:	66 90                	xchg   %ax,%ax
    21c0:	f3 0f 1e fa          	endbr64
    21c4:	68 19 00 00 00       	push   $0x19
    21c9:	e9 52 fe ff ff       	jmp    2020 <_init+0x20>
    21ce:	66 90                	xchg   %ax,%ax
    21d0:	f3 0f 1e fa          	endbr64
    21d4:	68 1a 00 00 00       	push   $0x1a
    21d9:	e9 42 fe ff ff       	jmp    2020 <_init+0x20>
    21de:	66 90                	xchg   %ax,%ax
    21e0:	f3 0f 1e fa          	endbr64
    21e4:	68 1b 00 00 00       	push   $0x1b
    21e9:	e9 32 fe ff ff       	jmp    2020 <_init+0x20>
    21ee:	66 90                	xchg   %ax,%ax
    21f0:	f3 0f 1e fa          	endbr64
    21f4:	68 1c 00 00 00       	push   $0x1c
    21f9:	e9 22 fe ff ff       	jmp    2020 <_init+0x20>
    21fe:	66 90                	xchg   %ax,%ax
    2200:	f3 0f 1e fa          	endbr64
    2204:	68 1d 00 00 00       	push   $0x1d
    2209:	e9 12 fe ff ff       	jmp    2020 <_init+0x20>
    220e:	66 90                	xchg   %ax,%ax
    2210:	f3 0f 1e fa          	endbr64
    2214:	68 1e 00 00 00       	push   $0x1e
    2219:	e9 02 fe ff ff       	jmp    2020 <_init+0x20>
    221e:	66 90                	xchg   %ax,%ax
    2220:	f3 0f 1e fa          	endbr64
    2224:	68 1f 00 00 00       	push   $0x1f
    2229:	e9 f2 fd ff ff       	jmp    2020 <_init+0x20>
    222e:	66 90                	xchg   %ax,%ax
    2230:	f3 0f 1e fa          	endbr64
    2234:	68 20 00 00 00       	push   $0x20
    2239:	e9 e2 fd ff ff       	jmp    2020 <_init+0x20>
    223e:	66 90                	xchg   %ax,%ax
    2240:	f3 0f 1e fa          	endbr64
    2244:	68 21 00 00 00       	push   $0x21
    2249:	e9 d2 fd ff ff       	jmp    2020 <_init+0x20>
    224e:	66 90                	xchg   %ax,%ax
    2250:	f3 0f 1e fa          	endbr64
    2254:	68 22 00 00 00       	push   $0x22
    2259:	e9 c2 fd ff ff       	jmp    2020 <_init+0x20>
    225e:	66 90                	xchg   %ax,%ax
    2260:	f3 0f 1e fa          	endbr64
    2264:	68 23 00 00 00       	push   $0x23
    2269:	e9 b2 fd ff ff       	jmp    2020 <_init+0x20>
    226e:	66 90                	xchg   %ax,%ax
    2270:	f3 0f 1e fa          	endbr64
    2274:	68 24 00 00 00       	push   $0x24
    2279:	e9 a2 fd ff ff       	jmp    2020 <_init+0x20>
    227e:	66 90                	xchg   %ax,%ax
    2280:	f3 0f 1e fa          	endbr64
    2284:	68 25 00 00 00       	push   $0x25
    2289:	e9 92 fd ff ff       	jmp    2020 <_init+0x20>
    228e:	66 90                	xchg   %ax,%ax
    2290:	f3 0f 1e fa          	endbr64
    2294:	68 26 00 00 00       	push   $0x26
    2299:	e9 82 fd ff ff       	jmp    2020 <_init+0x20>
    229e:	66 90                	xchg   %ax,%ax
    22a0:	f3 0f 1e fa          	endbr64
    22a4:	68 27 00 00 00       	push   $0x27
    22a9:	e9 72 fd ff ff       	jmp    2020 <_init+0x20>
    22ae:	66 90                	xchg   %ax,%ax
    22b0:	f3 0f 1e fa          	endbr64
    22b4:	68 28 00 00 00       	push   $0x28
    22b9:	e9 62 fd ff ff       	jmp    2020 <_init+0x20>
    22be:	66 90                	xchg   %ax,%ax
    22c0:	f3 0f 1e fa          	endbr64
    22c4:	68 29 00 00 00       	push   $0x29
    22c9:	e9 52 fd ff ff       	jmp    2020 <_init+0x20>
    22ce:	66 90                	xchg   %ax,%ax

Disassembly of section .plt.got:

00000000000022d0 <__cxa_finalize@plt>:
    22d0:	f3 0f 1e fa          	endbr64
    22d4:	ff 25 1e 7d 00 00    	jmp    *0x7d1e(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    22da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

00000000000022e0 <free@plt>:
    22e0:	f3 0f 1e fa          	endbr64
    22e4:	ff 25 96 7b 00 00    	jmp    *0x7b96(%rip)        # 9e80 <free@GLIBC_2.2.5>
    22ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000022f0 <putchar@plt>:
    22f0:	f3 0f 1e fa          	endbr64
    22f4:	ff 25 8e 7b 00 00    	jmp    *0x7b8e(%rip)        # 9e88 <putchar@GLIBC_2.2.5>
    22fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002300 <pthread_setaffinity_np@plt>:
    2300:	f3 0f 1e fa          	endbr64
    2304:	ff 25 86 7b 00 00    	jmp    *0x7b86(%rip)        # 9e90 <pthread_setaffinity_np@GLIBC_2.34>
    230a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002310 <puts@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 7e 7b 00 00    	jmp    *0x7b7e(%rip)        # 9e98 <puts@GLIBC_2.2.5>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002320 <setsockopt@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 76 7b 00 00    	jmp    *0x7b76(%rip)        # 9ea0 <setsockopt@GLIBC_2.2.5>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <clock_gettime@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 6e 7b 00 00    	jmp    *0x7b6e(%rip)        # 9ea8 <clock_gettime@GLIBC_2.17>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <strlen@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 66 7b 00 00    	jmp    *0x7b66(%rip)        # 9eb0 <strlen@GLIBC_2.2.5>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <__stack_chk_fail@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 5e 7b 00 00    	jmp    *0x7b5e(%rip)        # 9eb8 <__stack_chk_fail@GLIBC_2.4>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <io_uring_submit@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 56 7b 00 00    	jmp    *0x7b56(%rip)        # 9ec0 <io_uring_submit@LIBURING_2.0>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <nanosleep@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 4e 7b 00 00    	jmp    *0x7b4e(%rip)        # 9ec8 <nanosleep@GLIBC_2.2.5>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <strrchr@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 46 7b 00 00    	jmp    *0x7b46(%rip)        # 9ed0 <strrchr@GLIBC_2.2.5>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <close@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 3e 7b 00 00    	jmp    *0x7b3e(%rip)        # 9ed8 <close@GLIBC_2.2.5>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <strtok_r@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 36 7b 00 00    	jmp    *0x7b36(%rip)        # 9ee0 <strtok_r@GLIBC_2.2.5>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <read@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 2e 7b 00 00    	jmp    *0x7b2e(%rip)        # 9ee8 <read@GLIBC_2.2.5>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <calloc@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 26 7b 00 00    	jmp    *0x7b26(%rip)        # 9ef0 <calloc@GLIBC_2.2.5>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <strcmp@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 1e 7b 00 00    	jmp    *0x7b1e(%rip)        # 9ef8 <strcmp@GLIBC_2.2.5>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <__monstartup@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 16 7b 00 00    	jmp    *0x7b16(%rip)        # 9f00 <__monstartup@GLIBC_2.2.5>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <__memcpy_chk@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 0e 7b 00 00    	jmp    *0x7b0e(%rip)        # 9f08 <__memcpy_chk@GLIBC_2.3.4>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <stat@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 06 7b 00 00    	jmp    *0x7b06(%rip)        # 9f10 <stat@GLIBC_2.33>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <memcpy@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 fe 7a 00 00    	jmp    *0x7afe(%rip)        # 9f18 <memcpy@GLIBC_2.14>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <io_uring_queue_init@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 f6 7a 00 00    	jmp    *0x7af6(%rip)        # 9f20 <io_uring_queue_init@LIBURING_2.0>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <eventfd_write@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 ee 7a 00 00    	jmp    *0x7aee(%rip)        # 9f28 <eventfd_write@GLIBC_2.7>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <malloc@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 e6 7a 00 00    	jmp    *0x7ae6(%rip)        # 9f30 <malloc@GLIBC_2.2.5>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <listen@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 de 7a 00 00    	jmp    *0x7ade(%rip)        # 9f38 <listen@GLIBC_2.2.5>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <__strcpy_chk@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 d6 7a 00 00    	jmp    *0x7ad6(%rip)        # 9f40 <__strcpy_chk@GLIBC_2.3.4>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <__io_uring_get_cqe@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 ce 7a 00 00    	jmp    *0x7ace(%rip)        # 9f48 <__io_uring_get_cqe@LIBURING_2.0>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <__printf_chk@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 c6 7a 00 00    	jmp    *0x7ac6(%rip)        # 9f50 <__printf_chk@GLIBC_2.3.4>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <bind@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 be 7a 00 00    	jmp    *0x7abe(%rip)        # 9f58 <bind@GLIBC_2.2.5>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <pthread_create@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 b6 7a 00 00    	jmp    *0x7ab6(%rip)        # 9f60 <pthread_create@GLIBC_2.34>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <open@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 ae 7a 00 00    	jmp    *0x7aae(%rip)        # 9f68 <open@GLIBC_2.2.5>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <perror@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 a6 7a 00 00    	jmp    *0x7aa6(%rip)        # 9f70 <perror@GLIBC_2.2.5>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <__cxa_atexit@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 9e 7a 00 00    	jmp    *0x7a9e(%rip)        # 9f78 <__cxa_atexit@GLIBC_2.2.5>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <exit@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 96 7a 00 00    	jmp    *0x7a96(%rip)        # 9f80 <exit@GLIBC_2.2.5>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <eventfd@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 8e 7a 00 00    	jmp    *0x7a8e(%rip)        # 9f88 <eventfd@GLIBC_2.7>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <fwrite@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 86 7a 00 00    	jmp    *0x7a86(%rip)        # 9f90 <fwrite@GLIBC_2.2.5>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <__fprintf_chk@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 7e 7a 00 00    	jmp    *0x7a7e(%rip)        # 9f98 <__fprintf_chk@GLIBC_2.3.4>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <io_uring_register_eventfd@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 76 7a 00 00    	jmp    *0x7a76(%rip)        # 9fa0 <io_uring_register_eventfd@LIBURING_2.0>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <pthread_join@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 6e 7a 00 00    	jmp    *0x7a6e(%rip)        # 9fa8 <pthread_join@GLIBC_2.34>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002540 <strerror@plt>:
    2540:	f3 0f 1e fa          	endbr64
    2544:	ff 25 66 7a 00 00    	jmp    *0x7a66(%rip)        # 9fb0 <strerror@GLIBC_2.2.5>
    254a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002550 <__ctype_tolower_loc@plt>:
    2550:	f3 0f 1e fa          	endbr64
    2554:	ff 25 5e 7a 00 00    	jmp    *0x7a5e(%rip)        # 9fb8 <__ctype_tolower_loc@GLIBC_2.3>
    255a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002560 <__sprintf_chk@plt>:
    2560:	f3 0f 1e fa          	endbr64
    2564:	ff 25 56 7a 00 00    	jmp    *0x7a56(%rip)        # 9fc0 <__sprintf_chk@GLIBC_2.3.4>
    256a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002570 <socket@plt>:
    2570:	f3 0f 1e fa          	endbr64
    2574:	ff 25 4e 7a 00 00    	jmp    *0x7a4e(%rip)        # 9fc8 <socket@GLIBC_2.2.5>
    257a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000002580 <fatal_error>:
struct Snapshot {
  struct timespec start;
  struct timespec end;
};

void fatal_error(const char *syscall) {
    2580:	f3 0f 1e fa          	endbr64
    2584:	55                   	push   %rbp
    2585:	48 89 e5             	mov    %rsp,%rbp
    2588:	ff 15 5a 7a 00 00    	call   *0x7a5a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    perror(syscall);
    258e:	e8 2d ff ff ff       	call   24c0 <perror@plt>
    exit(1);
    2593:	bf 01 00 00 00       	mov    $0x1,%edi
    2598:	e8 43 ff ff ff       	call   24e0 <exit@plt>

000000000000259d <copy_file_contents.cold>:
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");
    259d:	48 8d 3d 5b 4c 00 00 	lea    0x4c5b(%rip),%rdi        # 71ff <_IO_stdin_used+0x1ff>
    25a4:	e8 d7 ff ff ff       	call   2580 <fatal_error>

00000000000025a9 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    25a9:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
    25af:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25b7:	0f 0b                	ud2

00000000000025b9 <add_read_request.cold>:
    25b9:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25c1:	0f 0b                	ud2

00000000000025c3 <_send_static_string_content.cold>:
    25c3:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    25c9:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25d1:	0f 0b                	ud2

00000000000025d3 <add_accept_request.cold>:
    25d3:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25db:	0f 0b                	ud2

00000000000025dd <io_thread.cold>:
        break;
      }
      printf("Received wait finished\n");
      struct Request *req = (struct Request *) cqe->user_data;
      if (ret < 0)
          fatal_error("io_uring_wait_cqe");
    25dd:	48 8d 3d eb 4b 00 00 	lea    0x4beb(%rip),%rdi        # 71cf <_IO_stdin_used+0x1cf>
    25e4:	e8 97 ff ff ff       	call   2580 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    25e9:	48 8d 3d 63 4b 00 00 	lea    0x4b63(%rip),%rdi        # 7153 <_IO_stdin_used+0x153>
    25f0:	e8 8b ff ff ff       	call   2580 <fatal_error>
    fatal_error("listen()");
    25f5:	48 8d 3d 77 4b 00 00 	lea    0x4b77(%rip),%rdi        # 7173 <_IO_stdin_used+0x173>
    25fc:	e8 7f ff ff ff       	call   2580 <fatal_error>
    2601:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2609:	0f 0b                	ud2
    260b:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2613:	0f 0b                	ud2
      fatal_error("socket()");
    2615:	48 8d 3d 2e 4b 00 00 	lea    0x4b2e(%rip),%rdi        # 714a <_IO_stdin_used+0x14a>
    261c:	e8 5f ff ff ff       	call   2580 <fatal_error>
      fatal_error("bind()");
    2621:	48 8d 3d 44 4b 00 00 	lea    0x4b44(%rip),%rdi        # 716c <_IO_stdin_used+0x16c>
    2628:	e8 53 ff ff ff       	call   2580 <fatal_error>
    262d:	0f 1f 00             	nopl   (%rax)

0000000000002630 <main>:
    }


  return 0;
}
int main() {
    2630:	f3 0f 1e fa          	endbr64
    2634:	55                   	push   %rbp
    2635:	48 89 e5             	mov    %rsp,%rbp
    2638:	41 57                	push   %r15
    263a:	41 56                	push   %r14
    263c:	41 55                	push   %r13
    263e:	41 54                	push   %r12
    2640:	53                   	push   %rbx
    2641:	48 81 ec 98 00 00 00 	sub    $0x98,%rsp
    2648:	ff 15 9a 79 00 00    	call   *0x799a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    264e:	48 8d 3d 4b 4e 00 00 	lea    0x4e4b(%rip),%rdi        # 74a0 <_IO_stdin_used+0x4a0>
    2655:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    265e:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    2662:	48 8d 05 c7 10 00 00 	lea    0x10c7(%rip),%rax        # 3730 <barriered_reset>
    2669:	66 48 0f 6e e8       	movq   %rax,%xmm5
    266e:	0f 16 2d eb 75 00 00 	movhps 0x75eb(%rip),%xmm5        # 9c60 <__do_global_dtors_aux_fini_array_entry+0x8>
    2675:	0f 29 ad 60 ff ff ff 	movaps %xmm5,-0xa0(%rbp)
    267c:	e8 8f fc ff ff       	call   2310 <puts@plt>
    2681:	bf 0a 00 00 00       	mov    $0xa,%edi
    2686:	e8 65 fc ff ff       	call   22f0 <putchar@plt>
    268b:	48 8d 3d 9c 4b 00 00 	lea    0x4b9c(%rip),%rdi        # 722e <_IO_stdin_used+0x22e>
    2692:	e8 79 fc ff ff       	call   2310 <puts@plt>
    2697:	ba 06 00 00 00       	mov    $0x6,%edx
    269c:	48 8d 35 a7 4b 00 00 	lea    0x4ba7(%rip),%rsi        # 724a <_IO_stdin_used+0x24a>
    26a3:	31 c0                	xor    %eax,%eax
    26a5:	bf 01 00 00 00       	mov    $0x1,%edi
    26aa:	e8 d1 fd ff ff       	call   2480 <__printf_chk@plt>
    26af:	ba 09 00 00 00       	mov    $0x9,%edx
    26b4:	48 8d 35 a9 4b 00 00 	lea    0x4ba9(%rip),%rsi        # 7264 <_IO_stdin_used+0x264>
    26bb:	31 c0                	xor    %eax,%eax
    26bd:	bf 01 00 00 00       	mov    $0x1,%edi
    26c2:	e8 b9 fd ff ff       	call   2480 <__printf_chk@plt>
    26c7:	ba 01 00 00 00       	mov    $0x1,%edx
    26cc:	48 8d 35 a5 4b 00 00 	lea    0x4ba5(%rip),%rsi        # 7278 <_IO_stdin_used+0x278>
    26d3:	31 c0                	xor    %eax,%eax
    26d5:	bf 01 00 00 00       	mov    $0x1,%edi
    26da:	e8 a1 fd ff ff       	call   2480 <__printf_chk@plt>
    26df:	ba 01 00 00 00       	mov    $0x1,%edx
    26e4:	48 8d 35 9e 4b 00 00 	lea    0x4b9e(%rip),%rsi        # 7289 <_IO_stdin_used+0x289>
    26eb:	31 c0                	xor    %eax,%eax
    26ed:	bf 01 00 00 00       	mov    $0x1,%edi
    26f2:	e8 89 fd ff ff       	call   2480 <__printf_chk@plt>
    26f7:	ba 01 00 00 00       	mov    $0x1,%edx
    26fc:	48 8d 35 9e 4b 00 00 	lea    0x4b9e(%rip),%rsi        # 72a1 <_IO_stdin_used+0x2a1>
    2703:	31 c0                	xor    %eax,%eax
    2705:	bf 01 00 00 00       	mov    $0x1,%edi
    270a:	e8 71 fd ff ff       	call   2480 <__printf_chk@plt>
    270f:	ba 01 00 00 00       	mov    $0x1,%edx
    2714:	48 8d 35 ed 4d 00 00 	lea    0x4ded(%rip),%rsi        # 7508 <_IO_stdin_used+0x508>
    271b:	31 c0                	xor    %eax,%eax
    271d:	bf 01 00 00 00       	mov    $0x1,%edi
    2722:	e8 59 fd ff ff       	call   2480 <__printf_chk@plt>
    2727:	ba 01 00 00 00       	mov    $0x1,%edx
    272c:	48 8d 35 05 4e 00 00 	lea    0x4e05(%rip),%rsi        # 7538 <_IO_stdin_used+0x538>
    2733:	31 c0                	xor    %eax,%eax
    2735:	bf 01 00 00 00       	mov    $0x1,%edi
    273a:	e8 41 fd ff ff       	call   2480 <__printf_chk@plt>
    273f:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2744:	48 8d 35 72 4b 00 00 	lea    0x4b72(%rip),%rsi        # 72bd <_IO_stdin_used+0x2bd>
    274b:	31 c0                	xor    %eax,%eax
    274d:	bf 01 00 00 00       	mov    $0x1,%edi
    2752:	e8 29 fd ff ff       	call   2480 <__printf_chk@plt>
    2757:	ba 05 00 00 00       	mov    $0x5,%edx
    275c:	48 8d 35 74 4b 00 00 	lea    0x4b74(%rip),%rsi        # 72d7 <_IO_stdin_used+0x2d7>
    2763:	31 c0                	xor    %eax,%eax
    2765:	bf 01 00 00 00       	mov    $0x1,%edi
    276a:	e8 11 fd ff ff       	call   2480 <__printf_chk@plt>
    276f:	48 8d 3d 58 49 00 00 	lea    0x4958(%rip),%rdi        # 70ce <_IO_stdin_used+0xce>
    2776:	e8 95 fb ff ff       	call   2310 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    277b:	be 18 00 00 00       	mov    $0x18,%esi
    2780:	bf 06 00 00 00       	mov    $0x6,%edi
    2785:	e8 36 fc ff ff       	call   23c0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    278a:	be b0 00 00 00       	mov    $0xb0,%esi
    278f:	bf 09 00 00 00       	mov    $0x9,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    2794:	49 89 c6             	mov    %rax,%r14
    2797:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    279e:	e8 1d fc ff ff       	call   23c0 <calloc@plt>
  int barrier_count = 2;
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    27a3:	be 10 00 00 00       	mov    $0x10,%esi
    27a8:	bf 01 00 00 00       	mov    $0x1,%edi
    27ad:	4d 8d 7e e8          	lea    -0x18(%r14),%r15
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27b1:	49 89 c4             	mov    %rax,%r12
    27b4:	48 89 85 78 ff ff ff 	mov    %rax,-0x88(%rbp)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    27bb:	e8 00 fc ff ff       	call   23c0 <calloc@plt>
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27c0:	be 10 00 00 00       	mov    $0x10,%esi
    27c5:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    27ca:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    27d0:	48 89 c3             	mov    %rax,%rbx
    27d3:	48 89 85 70 ff ff ff 	mov    %rax,-0x90(%rbp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27da:	e8 e1 fb ff ff       	call   23c0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    27df:	c7 45 98 00 00 00 00 	movl   $0x0,-0x68(%rbp)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    27e6:	4d 89 e1             	mov    %r12,%r9
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27e9:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
    27ed:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  int curcpu = 0;
    27f4:	c7 45 88 00 00 00 00 	movl   $0x0,-0x78(%rbp)
  int external_thread_index = 0;
    27fb:	c7 45 90 00 00 00 00 	movl   $0x0,-0x70(%rbp)
            thread_data[x].tasks[y].run = barriered_work; 
    2802:	4c 89 a5 50 ff ff ff 	mov    %r12,-0xb0(%rbp)
    2809:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2810:	be 08 00 00 00       	mov    $0x8,%esi
    2815:	bf 02 00 00 00       	mov    $0x2,%edi
    281a:	44 8b 6d 98          	mov    -0x68(%rbp),%r13d
    281e:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
    2822:	e8 99 fb ff ff       	call   23c0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2827:	be 80 00 00 00       	mov    $0x80,%esi
    282c:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2831:	48 89 c3             	mov    %rax,%rbx
    2834:	45 89 ee             	mov    %r13d,%r14d
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2837:	45 89 ec             	mov    %r13d,%r12d
    283a:	e8 81 fb ff ff       	call   23c0 <calloc@plt>
    if (x % 2 == 1) {
    283f:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2843:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    if (x % 2 == 1) {
    2847:	44 89 e8             	mov    %r13d,%eax
    284a:	41 83 c5 01          	add    $0x1,%r13d
    284e:	83 e0 01             	and    $0x1,%eax
    2851:	44 89 6d 98          	mov    %r13d,-0x68(%rbp)
    2855:	85 c0                	test   %eax,%eax
    2857:	0f 84 9b 0c 00 00    	je     34f8 <main+0xec8>
      my_thread_data[0] = &thread_data[other]; 
    285d:	49 8d 89 50 ff ff ff 	lea    -0xb0(%r9),%rcx
      my_thread_data[1] = &thread_data[x]; 
    2864:	4c 89 4b 08          	mov    %r9,0x8(%rbx)
    2868:	4d 89 c8             	mov    %r9,%r8
    286b:	31 c0                	xor    %eax,%eax
      my_thread_data[0] = &thread_data[other]; 
    286d:	48 89 0b             	mov    %rcx,(%rbx)
    2870:	44 89 f2             	mov    %r14d,%edx
    2873:	bf 01 00 00 00       	mov    $0x1,%edi
      other = abs(x - 1) % total_threads;
    2878:	45 8d 6e ff          	lea    -0x1(%r14),%r13d
      thread_data[x].thread_index = 1;
    287c:	41 c7 01 01 00 00 00 	movl   $0x1,(%r9)
    2883:	48 8d 35 61 4a 00 00 	lea    0x4a61(%rip),%rsi        # 72eb <_IO_stdin_used+0x2eb>
    288a:	e8 f1 fb ff ff       	call   2480 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    288f:	49 8d 47 18          	lea    0x18(%r15),%rax
    2893:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    2897:	48 89 45 80          	mov    %rax,-0x80(%rbp)
    289b:	4d 89 79 38          	mov    %r15,0x38(%r9)
    289f:	45 8b 01             	mov    (%r9),%r8d
    28a2:	44 89 e9             	mov    %r13d,%ecx
    28a5:	44 89 f2             	mov    %r14d,%edx
    28a8:	48 8d 35 b1 4c 00 00 	lea    0x4cb1(%rip),%rsi        # 7560 <_IO_stdin_used+0x560>
    28af:	bf 01 00 00 00       	mov    $0x1,%edi
    28b4:	31 c0                	xor    %eax,%eax
    28b6:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
    28ba:	e8 c1 fb ff ff       	call   2480 <__printf_chk@plt>
    thread_data[x].other = other;
    28bf:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    28c3:	8b 4d 88             	mov    -0x78(%rbp),%ecx
    28c6:	31 c0                	xor    %eax,%eax
    28c8:	44 89 f2             	mov    %r14d,%edx
    28cb:	48 8d 35 be 4c 00 00 	lea    0x4cbe(%rip),%rsi        # 7590 <_IO_stdin_used+0x590>
    28d2:	bf 01 00 00 00       	mov    $0x1,%edi
    28d7:	45 89 a9 a8 00 00 00 	mov    %r13d,0xa8(%r9)
    28de:	e8 9d fb ff ff       	call   2480 <__printf_chk@plt>
      if (x < thread_count) {
    28e3:	41 83 fc 05          	cmp    $0x5,%r12d
    28e7:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    28eb:	0f 87 79 0c 00 00    	ja     356a <main+0xf3a>
        CPU_SET(curcpu, sendercpu);
    28f1:	48 63 45 88          	movslq -0x78(%rbp),%rax
    28f5:	48 89 c7             	mov    %rax,%rdi
    28f8:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    28fe:	77 16                	ja     2916 <main+0x2e6>
    2900:	89 f9                	mov    %edi,%ecx
    2902:	48 8b 7d b8          	mov    -0x48(%rbp),%rdi
    2906:	48 c1 e8 06          	shr    $0x6,%rax
    290a:	ba 01 00 00 00       	mov    $0x1,%edx
    290f:	48 d3 e2             	shl    %cl,%rdx
    2912:	48 09 14 c7          	or     %rdx,(%rdi,%rax,8)
        curcpu += 2;
    2916:	83 45 88 02          	addl   $0x2,-0x78(%rbp)
    thread_data[x].cpu_set = sendercpu;
    291a:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    thread_data[x].threads = my_thread_data;
    291e:	49 89 59 10          	mov    %rbx,0x10(%r9)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2922:	be 10 00 00 00       	mov    $0x10,%esi
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2927:	31 db                	xor    %ebx,%ebx
    thread_data[x].real_thread_index = x;
    2929:	45 89 71 04          	mov    %r14d,0x4(%r9)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    292d:	bf 64 00 00 00       	mov    $0x64,%edi
        thread_data[x].tasks[y].sending = 1;
    2932:	45 89 f5             	mov    %r14d,%r13d
    thread_data[x].cpu_set = sendercpu;
    2935:	49 89 81 a0 00 00 00 	mov    %rax,0xa0(%r9)
    thread_data[x].thread_count = 2;
    293c:	48 8b 05 ed 50 00 00 	mov    0x50ed(%rip),%rax        # 7a30 <_IO_stdin_used+0xa30>
    thread_data[x].task_count = total_barrier_count;
    2943:	41 c7 41 30 03 00 00 00 	movl   $0x3,0x30(%r9)
    thread_data[x].thread_count = 2;
    294b:	49 89 41 18          	mov    %rax,0x18(%r9)
    thread_data[x].task_count = total_barrier_count;
    294f:	4c 89 4d b8          	mov    %r9,-0x48(%rbp)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2953:	e8 68 fa ff ff       	call   23c0 <calloc@plt>
    2958:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    295c:	be 10 00 00 00       	mov    $0x10,%esi
    2961:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2966:	49 89 41 58          	mov    %rax,0x58(%r9)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    296a:	e8 51 fa ff ff       	call   23c0 <calloc@plt>
    296f:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2973:	be 28 00 00 00       	mov    $0x28,%esi
    thread_data[x].timestamp_count = 0;
    2978:	66 0f 6f 15 90 50 00 00 	movdqa 0x5090(%rip),%xmm2        # 7a10 <_IO_stdin_used+0xa10>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2980:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2985:	49 89 41 60          	mov    %rax,0x60(%r9)
    thread_data[x].timestamp_count = 0;
    2989:	41 0f 11 51 70       	movups %xmm2,0x70(%r9)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    298e:	e8 2d fa ff ff       	call   23c0 <calloc@plt>
    2993:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2997:	be 00 02 00 00       	mov    $0x200,%esi
    thread_data[x].task_timestamp_count = 0;
    299c:	66 0f 6f 1d 6c 50 00 00 	movdqa 0x506c(%rip),%xmm3        # 7a10 <_IO_stdin_used+0xa10>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    29a4:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    29a9:	49 89 81 80 00 00 00 	mov    %rax,0x80(%r9)
    thread_data[x].task_timestamp_count = 0;
    29b0:	41 0f 11 99 88 00 00 00 	movups %xmm3,0x88(%r9)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    29b8:	e8 03 fa ff ff       	call   23c0 <calloc@plt>
      thread_data[x].tasks = barriers;
    29bd:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
        thread_data[x].tasks[y].sending = 1;
    29c1:	48 89 c2             	mov    %rax,%rdx
      thread_data[x].tasks = barriers;
    29c4:	49 89 41 28          	mov    %rax,0x28(%r9)
        thread_data[x].tasks[y].sending = 1;
    29c8:	4d 89 cf             	mov    %r9,%r15
        thread_data[x].tasks[y].protected = do_protected_write; 
    29cb:	4c 63 f3             	movslq %ebx,%r14
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    29ce:	be 20 00 00 00       	mov    $0x20,%esi
    29d3:	bf 06 00 00 00       	mov    $0x6,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    29d8:	4c 89 f0             	mov    %r14,%rax
    29db:	48 c1 e0 09          	shl    $0x9,%rax
    29df:	4c 8d 24 02          	lea    (%rdx,%rax,1),%r12
    29e3:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
    29e7:	48 8d 05 f2 0c 00 00 	lea    0xcf2(%rip),%rax        # 36e0 <do_protected_write>
    29ee:	49 89 84 24 20 01 00 00 	mov    %rax,0x120(%r12)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    29f6:	e8 c5 f9 ff ff       	call   23c0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    29fb:	44 89 6d a8          	mov    %r13d,-0x58(%rbp)
    29ff:	49 89 84 24 68 01 00 00 	mov    %rax,0x168(%r12)
        for (int b = 0 ; b < 2 ; b++) {
    2a07:	49 89 c4             	mov    %rax,%r12
    2a0a:	48 8d 40 40          	lea    0x40(%rax),%rax
    2a0e:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    2a12:	89 5d a0             	mov    %ebx,-0x60(%rbp)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2a15:	be 08 00 00 00       	mov    $0x8,%esi
    2a1a:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    2a1f:	49 83 c4 20          	add    $0x20,%r12
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2a23:	e8 98 f9 ff ff       	call   23c0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2a28:	be 08 00 00 00       	mov    $0x8,%esi
    2a2d:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2a32:	49 89 c5             	mov    %rax,%r13
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2a35:	e8 86 f9 ff ff       	call   23c0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    2a3a:	be 18 00 00 00       	mov    $0x18,%esi
    2a3f:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2a44:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    2a47:	e8 74 f9 ff ff       	call   23c0 <calloc@plt>
          data[0].messages_count = 0;
    2a4c:	66 0f 6f 05 cc 4f 00 00 	movdqa 0x4fcc(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
          mailboxes[b].higher = &data[1];
    2a54:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    2a58:	49 89 44 24 e0       	mov    %rax,-0x20(%r12)
          mailboxes[b].higher = &data[1];
    2a5d:	49 89 74 24 e8       	mov    %rsi,-0x18(%r12)
          data[0].messages = messages;
    2a62:	4c 89 28             	mov    %r13,(%rax)
          data[1].messages = messages2;
    2a65:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    2a69:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    2a6d:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    2a71:	4c 39 65 b8          	cmp    %r12,-0x48(%rbp)
    2a75:	75 9e                	jne    2a15 <main+0x3e5>
        char *message = malloc(sizeof(char) * 256);
    2a77:	be 01 00 00 00       	mov    $0x1,%esi
    2a7c:	bf 00 01 00 00       	mov    $0x100,%edi
    2a81:	8b 5d a0             	mov    -0x60(%rbp),%ebx
    2a84:	44 8b 6d a8          	mov    -0x58(%rbp),%r13d
    2a88:	e8 33 f9 ff ff       	call   23c0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a8d:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a92:	49 89 c4             	mov    %rax,%r12
        struct Message *messaged = malloc(sizeof(struct Message));
    2a95:	e8 a6 f9 ff ff       	call   2440 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a9a:	4c 89 e7             	mov    %r12,%rdi
    2a9d:	41 89 d9             	mov    %ebx,%r9d
    2aa0:	45 89 e8             	mov    %r13d,%r8d
    2aa3:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    2aa7:	48 8d 0d 02 4b 00 00 	lea    0x4b02(%rip),%rcx        # 75b0 <_IO_stdin_used+0x5b0>
    2aae:	ba 00 01 00 00       	mov    $0x100,%edx
    2ab3:	31 c0                	xor    %eax,%eax
    2ab5:	be 01 00 00 00       	mov    $0x1,%esi
    2aba:	e8 a1 fa ff ff       	call   2560 <__sprintf_chk@plt>
        messaged->thread_index = thread_data[x].thread_index;
    2abf:	49 63 07             	movslq (%r15),%rax
        messaged->message = message;
    2ac2:	4c 8b 55 b8          	mov    -0x48(%rbp),%r10
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2ac6:	8d 4b 01             	lea    0x1(%rbx),%ecx
    2ac9:	49 8b 57 28          	mov    0x28(%r15),%rdx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2acd:	be 20 00 00 00       	mov    $0x20,%esi
    2ad2:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2ad7:	89 4d b8             	mov    %ecx,-0x48(%rbp)
        messaged->task_index = y;
    2ada:	4d 89 72 10          	mov    %r14,0x10(%r10)
        messaged->thread_index = thread_data[x].thread_index;
    2ade:	49 89 c6             	mov    %rax,%r14
    2ae1:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2ae5:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
        messaged->message = message;
    2ae9:	4d 89 22             	mov    %r12,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2aec:	4c 8d 24 02          	lea    (%rdx,%rax,1),%r12
    2af0:	48 89 55 a8          	mov    %rdx,-0x58(%rbp)
    2af4:	41 89 8c 24 88 01 00 00 	mov    %ecx,0x188(%r12)
        thread_data[x].tasks[y].message = messaged;
    2afc:	4d 89 94 24 80 01 00 00 	mov    %r10,0x180(%r12)
        thread_data[x].tasks[y].snapshot_count = 99;
    2b04:	49 c7 84 24 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%r12)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2b10:	e8 ab f8 ff ff       	call   23c0 <calloc@plt>
        if (y == barrier_count - 1) {
    2b15:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2b18:	41 89 1c 24          	mov    %ebx,(%r12)
        if (y == barrier_count - 1) {
    2b1c:	8b 4d b8             	mov    -0x48(%rbp),%ecx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2b1f:	49 89 84 24 48 01 00 00 	mov    %rax,0x148(%r12)
        if (y == barrier_count - 1) {
    2b27:	48 8b 55 a8          	mov    -0x58(%rbp),%rdx
        thread_data[x].tasks[y].available = 1;
    2b2b:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2b35:	49 89 84 24 38 01 00 00 	mov    %rax,0x138(%r12)
        thread_data[x].tasks[y].sending = 1;
    2b3d:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2b47:	49 c7 84 24 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%r12)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2b53:	45 89 b4 24 30 01 00 00 	mov    %r14d,0x130(%r12)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2b5b:	4d 89 bc 24 28 01 00 00 	mov    %r15,0x128(%r12)
        thread_data[x].tasks[y].arrived = 0;
    2b63:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
        thread_data[x].tasks[y].thread_count = 2;
    2b6f:	41 c7 84 24 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%r12)
        thread_data[x].tasks[y].sending = 1;
    2b7b:	49 89 84 24 78 01 00 00 	mov    %rax,0x178(%r12)
        if (y == barrier_count - 1) {
    2b83:	0f 84 4f 09 00 00    	je     34d8 <main+0xea8>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2b89:	41 39 dd             	cmp    %ebx,%r13d
    2b8c:	75 6a                	jne    2bf8 <main+0x5c8>
    2b8e:	8b 5d 90             	mov    -0x70(%rbp),%ebx
    2b91:	85 db                	test   %ebx,%ebx
    2b93:	7f 63                	jg     2bf8 <main+0x5c8>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2b95:	44 89 ea             	mov    %r13d,%edx
    2b98:	bf 01 00 00 00       	mov    $0x1,%edi
    2b9d:	31 c0                	xor    %eax,%eax
    2b9f:	89 4d b8             	mov    %ecx,-0x48(%rbp)
    2ba2:	48 8d 35 2f 4a 00 00 	lea    0x4a2f(%rip),%rsi        # 75d8 <_IO_stdin_used+0x5d8>
    2ba9:	e8 d2 f8 ff ff       	call   2480 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2bae:	48 8b 8d 70 ff ff ff 	mov    -0x90(%rbp),%rcx
    2bb5:	48 63 c3             	movslq %ebx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2bb8:	49 8b 57 28          	mov    0x28(%r15),%rdx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2bbc:	48 89 c7             	mov    %rax,%rdi
    2bbf:	48 c1 e0 04          	shl    $0x4,%rax
    2bc3:	48 01 c8             	add    %rcx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2bc6:	48 8d 0d 23 31 00 00 	lea    0x3123(%rip),%rcx        # 5cf0 <barriered_work_ingest>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2bcd:	49 89 47 40          	mov    %rax,0x40(%r15)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2bd1:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
    2bd5:	48 89 8c 02 18 01 00 00 	mov    %rcx,0x118(%rdx,%rax,1)
    2bdd:	8b 4d b8             	mov    -0x48(%rbp),%ecx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2be0:	8d 47 01             	lea    0x1(%rdi),%eax
    2be3:	89 45 90             	mov    %eax,-0x70(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2be6:	83 f9 03             	cmp    $0x3,%ecx
    2be9:	74 21                	je     2c0c <main+0x5dc>
    2beb:	bb 01 00 00 00       	mov    $0x1,%ebx
    2bf0:	e9 d6 fd ff ff       	jmp    29cb <main+0x39b>
    2bf5:	0f 1f 00             	nopl   (%rax)
            thread_data[x].tasks[y].run = barriered_work; 
    2bf8:	48 8d 05 61 2c 00 00 	lea    0x2c61(%rip),%rax        # 5860 <barriered_work>
    2bff:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2c07:	83 f9 03             	cmp    $0x3,%ecx
    2c0a:	75 df                	jne    2beb <main+0x5bb>
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2c0c:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2c16:	4d 89 f9             	mov    %r15,%r9
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2c19:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2c23:	66 0f 6f a5 60 ff ff ff 	movdqa -0xa0(%rbp),%xmm4
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2c2b:	48 89 82 34 05 00 00 	mov    %rax,0x534(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2c32:	49 81 c1 b0 00 00 00 	add    $0xb0,%r9
    2c39:	83 7d 98 09          	cmpl   $0x9,-0x68(%rbp)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2c3d:	c7 82 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2c47:	41 8b 07             	mov    (%r15),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2c4a:	4c 89 ba 28 05 00 00 	mov    %r15,0x528(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2c51:	4c 8b 7d 80          	mov    -0x80(%rbp),%r15
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2c55:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2c5b:	c7 82 7c 05 00 00 06 00 00 00 	movl   $0x6,0x57c(%rdx)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2c65:	c7 82 3c 05 00 00 03 00 00 00 	movl   $0x3,0x53c(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2c6f:	0f 11 a2 18 05 00 00 	movups %xmm4,0x518(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2c76:	0f 85 94 fb ff ff    	jne    2810 <main+0x1e0>
    2c7c:	4c 8b 85 50 ff ff ff 	mov    -0xb0(%rbp),%r8
    2c83:	ba 07 00 00 00       	mov    $0x7,%edx
    2c88:	48 8d 35 79 46 00 00 	lea    0x4679(%rip),%rsi        # 7308 <_IO_stdin_used+0x308>
    2c8f:	31 c0                	xor    %eax,%eax
    2c91:	bf 01 00 00 00       	mov    $0x1,%edi
    2c96:	4c 89 85 48 ff ff ff 	mov    %r8,-0xb8(%rbp)
    2c9d:	e8 de f7 ff ff       	call   2480 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2ca2:	be 08 00 00 00       	mov    $0x8,%esi
    2ca7:	bf 02 00 00 00       	mov    $0x2,%edi
    2cac:	e8 0f f7 ff ff       	call   23c0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2cb1:	4c 8b bd 78 ff ff ff 	mov    -0x88(%rbp),%r15
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cb8:	bf 09 00 00 00       	mov    $0x9,%edi
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2cbd:	49 8d 8f 60 01 00 00 	lea    0x160(%r15),%rcx
    my_thread_data[0] = &thread_data[x]; 
    2cc4:	4d 8d af d0 04 00 00 	lea    0x4d0(%r15),%r13
    thread_data[x].threads = my_thread_data;
    2ccb:	49 89 87 e0 04 00 00 	mov    %rax,0x4e0(%r15)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2cd2:	48 89 48 08          	mov    %rcx,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2cd6:	49 8d b7 10 02 00 00 	lea    0x210(%r15),%rsi
    2cdd:	49 8d 97 70 03 00 00 	lea    0x370(%r15),%rdx
    my_thread_data[0] = &thread_data[x]; 
    2ce4:	4c 89 28             	mov    %r13,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2ce7:	49 8b 47 28          	mov    0x28(%r15),%rax
    2ceb:	49 8d 9f c0 02 00 00 	lea    0x2c0(%r15),%rbx
    thread_data[x].thread_count = 2;
    2cf2:	41 c7 87 e8 04 00 00 02 00 00 00 	movl   $0x2,0x4e8(%r15)
    thread_data[x].thread_index = 0;
    2cfd:	41 c7 87 d0 04 00 00 00 00 00 00 	movl   $0x0,0x4d0(%r15)
    thread_data[x].task_count = total_barrier_count;
    2d08:	41 c7 87 00 05 00 00 03 00 00 00 	movl   $0x3,0x500(%r15)
    thread_data[n].tasks[0].scheduled = 1;
    2d13:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d1d:	49 8d 87 b0 00 00 00 	lea    0xb0(%r15),%rax
    2d24:	48 89 45 98          	mov    %rax,-0x68(%rbp)
    2d28:	49 8b 87 d8 00 00 00 	mov    0xd8(%r15),%rax
    2d2f:	48 89 75 a8          	mov    %rsi,-0x58(%rbp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d33:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2d38:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d42:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2d49:	48 89 4d a0          	mov    %rcx,-0x60(%rbp)
    thread_data[n].tasks[0].scheduled = 1;
    2d4d:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d57:	49 8b 87 38 02 00 00 	mov    0x238(%r15),%rax
    2d5e:	48 89 55 b8          	mov    %rdx,-0x48(%rbp)
    2d62:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d6c:	49 8b 87 e8 02 00 00 	mov    0x2e8(%r15),%rax
    my_thread_data[0] = &thread_data[x]; 
    2d73:	4c 89 6d 90          	mov    %r13,-0x70(%rbp)
    thread_data[n].tasks[0].scheduled = 1;
    2d77:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d81:	49 8b 87 98 03 00 00 	mov    0x398(%r15),%rax
    2d88:	48 89 5d b0          	mov    %rbx,-0x50(%rbp)
    2d8c:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d96:	e8 25 f6 ff ff       	call   23c0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d9b:	be 38 00 00 00       	mov    $0x38,%esi
    2da0:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2da5:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2da8:	e8 13 f6 ff ff       	call   23c0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dad:	be 38 00 00 00       	mov    $0x38,%esi
    2db2:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2db7:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dba:	e8 01 f6 ff ff       	call   23c0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dbf:	be 38 00 00 00       	mov    $0x38,%esi
    2dc4:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dc9:	48 89 45 80          	mov    %rax,-0x80(%rbp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dcd:	e8 ee f5 ff ff       	call   23c0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2dd2:	be 08 00 00 00       	mov    $0x8,%esi
    2dd7:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ddc:	48 89 85 60 ff ff ff 	mov    %rax,-0xa0(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2de3:	e8 d8 f5 ff ff       	call   23c0 <calloc@plt>
  thread_data[thread_count].type = TIMER;
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2de8:	be 08 00 00 00       	mov    $0x8,%esi
    2ded:	bf 09 00 00 00       	mov    $0x9,%edi
  thread_data[thread_count].type = TIMER;
    2df2:	41 c7 87 28 04 00 00 00 00 00 00 	movl   $0x0,0x428(%r15)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2dfd:	49 89 c6             	mov    %rax,%r14
  thread_data[thread_count].task_count = total_barrier_count;
    2e00:	48 8b 05 31 4c 00 00 	mov    0x4c31(%rip),%rax        # 7a38 <_IO_stdin_used+0xa38>
    2e07:	49 89 87 50 04 00 00 	mov    %rax,0x450(%r15)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2e0e:	e8 ad f5 ff ff       	call   23c0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2e13:	48 8b 7d 98          	mov    -0x68(%rbp),%rdi
    2e17:	48 8b 4d a0          	mov    -0x60(%rbp),%rcx
    2e1b:	48 8b 75 a8          	mov    -0x58(%rbp),%rsi
    2e1f:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
    2e23:	4c 89 38             	mov    %r15,(%rax)
    2e26:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2e2a:	48 8b 7d b0          	mov    -0x50(%rbp),%rdi
    2e2e:	48 89 48 10          	mov    %rcx,0x10(%rax)
    2e32:	48 89 78 20          	mov    %rdi,0x20(%rax)
    2e36:	4c 89 ff             	mov    %r15,%rdi
    2e39:	4d 8d bf 20 04 00 00 	lea    0x420(%r15),%r15
    2e40:	48 8d 8f 80 05 00 00 	lea    0x580(%rdi),%rcx
    2e47:	48 89 70 18          	mov    %rsi,0x18(%rax)
    2e4b:	48 8d 35 c5 44 00 00 	lea    0x44c5(%rip),%rsi        # 7317 <_IO_stdin_used+0x317>
    2e52:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2e56:	ba 06 00 00 00       	mov    $0x6,%edx
    2e5b:	4c 89 78 30          	mov    %r15,0x30(%rax)
    2e5f:	4c 89 68 38          	mov    %r13,0x38(%rax)
    2e63:	4c 8d 2d 8e 47 00 00 	lea    0x478e(%rip),%r13        # 75f8 <_IO_stdin_used+0x5f8>
    2e6a:	48 89 48 40          	mov    %rcx,0x40(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2e6e:	48 89 87 30 04 00 00 	mov    %rax,0x430(%rdi)
    2e75:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2e77:	c7 87 38 04 00 00 06 00 00 00 	movl   $0x6,0x438(%rdi)
  thread_data[thread_count].my_thread_count = 2;
    2e81:	c7 87 40 04 00 00 02 00 00 00 	movl   $0x2,0x440(%rdi)
  thread_data[thread_count].thread_index = 0;
    2e8b:	c7 87 20 04 00 00 00 00 00 00 	movl   $0x0,0x420(%rdi)
    2e95:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    2e9a:	48 89 4d 88          	mov    %rcx,-0x78(%rbp)
    2e9e:	e8 dd f5 ff ff       	call   2480 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2ea3:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2eaa:	49 8d 7e 30          	lea    0x30(%r14),%rdi
    2eae:	4c 89 f3             	mov    %r14,%rbx
    2eb1:	4c 89 f9             	mov    %r15,%rcx
    2eb4:	48 8d 15 35 0c 00 00 	lea    0xc35(%rip),%rdx        # 3af0 <timer_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    2ebb:	45 31 ff             	xor    %r15d,%r15d
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2ebe:	e8 dd f5 ff ff       	call   24a0 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2ec3:	4c 89 b5 50 ff ff ff 	mov    %r14,-0xb0(%rbp)
    2eca:	45 89 fe             	mov    %r15d,%r14d
    2ecd:	4d 89 e7             	mov    %r12,%r15
    2ed0:	49 89 dc             	mov    %rbx,%r12
    2ed3:	48 8b 9d 48 ff ff ff 	mov    -0xb8(%rbp),%rbx
    2eda:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    thread_data[x].type = WORKER;
    2ee0:	c7 43 08 01 00 00 00 	movl   $0x1,0x8(%rbx)
    2ee7:	44 89 f2             	mov    %r14d,%edx
    2eea:	4c 89 ee             	mov    %r13,%rsi
    2eed:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2eef:	c7 43 34 01 00 00 00 	movl   $0x1,0x34(%rbx)
    2ef6:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < thread_count ; x++) {
    2efb:	41 83 c6 01          	add    $0x1,%r14d
    2eff:	e8 7c f5 ff ff       	call   2480 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2f04:	48 89 d9             	mov    %rbx,%rcx
    2f07:	4c 89 fe             	mov    %r15,%rsi
    2f0a:	4c 89 e7             	mov    %r12,%rdi
    2f0d:	48 8d 15 8c 08 00 00 	lea    0x88c(%rip),%rdx        # 37a0 <barriered_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    2f14:	48 81 c3 b0 00 00 00 	add    $0xb0,%rbx
    2f1b:	49 83 c4 08          	add    $0x8,%r12
    2f1f:	49 83 c7 38          	add    $0x38,%r15
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2f23:	e8 78 f5 ff ff       	call   24a0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2f28:	48 8b 53 f0          	mov    -0x10(%rbx),%rdx
    2f2c:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
    2f31:	be 08 00 00 00       	mov    $0x8,%esi
    2f36:	e8 c5 f3 ff ff       	call   2300 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2f3b:	41 83 fe 06          	cmp    $0x6,%r14d
    2f3f:	75 9f                	jne    2ee0 <main+0x8b0>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2f41:	4c 8b bd 78 ff ff ff 	mov    -0x88(%rbp),%r15
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f48:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].task_count = 0;
    2f4d:	48 8b 1d ec 4a 00 00 	mov    0x4aec(%rip),%rbx        # 7a40 <_IO_stdin_used+0xa40>
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f54:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    2f59:	4c 8b b5 50 ff ff ff 	mov    -0xb0(%rbp),%r14
    thread_data[x].task_count = 0;
    2f60:	49 89 9f 00 05 00 00 	mov    %rbx,0x500(%r15)
    thread_data[x].type = IO;
    2f67:	41 c7 87 d8 04 00 00 02 00 00 00 	movl   $0x2,0x4d8(%r15)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f72:	e8 49 f4 ff ff       	call   23c0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f77:	be 00 08 00 00       	mov    $0x800,%esi
    2f7c:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f7e:	49 89 87 18 05 00 00 	mov    %rax,0x518(%r15)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f85:	e8 66 f5 ff ff       	call   24f0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f8a:	be 08 00 00 00       	mov    $0x8,%esi
    2f8f:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f94:	41 89 87 20 05 00 00 	mov    %eax,0x520(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f9b:	e8 20 f4 ff ff       	call   23c0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    2fa0:	4c 8b 6d 98          	mov    -0x68(%rbp),%r13
    2fa4:	4c 8b 65 a0          	mov    -0x60(%rbp),%r12
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    2fa8:	41 c7 87 e8 04 00 00 06 00 00 00 	movl   $0x6,0x4e8(%r15)
      my_thread_data[n] = &thread_data[n]; 
    2fb3:	48 8b 7d a8          	mov    -0x58(%rbp),%rdi
    2fb7:	48 8b 75 b0          	mov    -0x50(%rbp),%rsi
    2fbb:	4c 89 38             	mov    %r15,(%rax)
    2fbe:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
    2fc2:	4c 89 68 08          	mov    %r13,0x8(%rax)
    2fc6:	4c 89 60 10          	mov    %r12,0x10(%rax)
    2fca:	48 89 78 18          	mov    %rdi,0x18(%rax)
    2fce:	bf 01 00 00 00       	mov    $0x1,%edi
    2fd3:	48 89 70 20          	mov    %rsi,0x20(%rax)
    2fd7:	48 8d 35 57 43 00 00 	lea    0x4357(%rip),%rsi        # 7335 <_IO_stdin_used+0x335>
    2fde:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2fe2:	ba 07 00 00 00       	mov    $0x7,%edx
    thread_data[x].threads = my_thread_data;
    2fe7:	49 89 87 e0 04 00 00 	mov    %rax,0x4e0(%r15)
    2fee:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    2ff0:	41 c7 87 d0 04 00 00 07 00 00 00 	movl   $0x7,0x4d0(%r15)
    2ffb:	e8 80 f4 ff ff       	call   2480 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3000:	48 8b 45 80          	mov    -0x80(%rbp),%rax
    3004:	48 8b 4d 90          	mov    -0x70(%rbp),%rcx
    3008:	49 8d 7e 38          	lea    0x38(%r14),%rdi
    300c:	48 8d 15 0d 1e 00 00 	lea    0x1e0d(%rip),%rdx        # 4e20 <io_thread>
    3013:	48 05 88 01 00 00    	add    $0x188,%rax
    3019:	48 89 c6             	mov    %rax,%rsi
    301c:	e8 7f f4 ff ff       	call   24a0 <pthread_create@plt>
    3021:	ba 08 00 00 00       	mov    $0x8,%edx
    3026:	48 8d 35 1f 43 00 00 	lea    0x431f(%rip),%rsi        # 734c <_IO_stdin_used+0x34c>
    302d:	31 c0                	xor    %eax,%eax
    302f:	bf 01 00 00 00       	mov    $0x1,%edi
    3034:	e8 47 f4 ff ff       	call   2480 <__printf_chk@plt>
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3039:	be 08 00 00 00       	mov    $0x8,%esi
    303e:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[x].buffers = &buffers[buffer_index];
    3043:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
    thread_data[x].task_count = 0;
    304a:	49 89 9f b0 05 00 00 	mov    %rbx,0x5b0(%r15)
    3051:	48 8d 1d 2f 43 00 00 	lea    0x432f(%rip),%rbx        # 7387 <_IO_stdin_used+0x387>
    thread_data[x].type = EXTERNAL;
    3058:	41 c7 87 88 05 00 00 03 00 00 00 	movl   $0x3,0x588(%r15)
    thread_data[x].buffers = &buffers[buffer_index];
    3063:	49 89 87 c0 05 00 00 	mov    %rax,0x5c0(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    306a:	e8 51 f3 ff ff       	call   23c0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    306f:	48 8b 4d a8          	mov    -0x58(%rbp),%rcx
    3073:	48 8b 75 b0          	mov    -0x50(%rbp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    3077:	41 c7 87 80 05 00 00 08 00 00 00 	movl   $0x8,0x580(%r15)
      my_thread_data[n] = &thread_data[n]; 
    3082:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
    3086:	4c 89 68 08          	mov    %r13,0x8(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    308a:	49 8d 7e 40          	lea    0x40(%r14),%rdi
    308e:	45 31 ed             	xor    %r13d,%r13d
      my_thread_data[n] = &thread_data[n]; 
    3091:	4c 89 60 10          	mov    %r12,0x10(%rax)
    3095:	4c 8d 65 c0          	lea    -0x40(%rbp),%r12
    3099:	48 89 48 18          	mov    %rcx,0x18(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    309d:	48 8b 4d 88          	mov    -0x78(%rbp),%rcx
      my_thread_data[n] = &thread_data[n]; 
    30a1:	48 89 70 20          	mov    %rsi,0x20(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    30a5:	48 8b b5 60 ff ff ff 	mov    -0xa0(%rbp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    30ac:	48 89 50 28          	mov    %rdx,0x28(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    30b0:	48 8d 15 79 09 00 00 	lea    0x979(%rip),%rdx        # 3a30 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    30b7:	4c 89 38             	mov    %r15,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    30ba:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    thread_data[x].threads = my_thread_data;
    30c1:	49 89 87 90 05 00 00 	mov    %rax,0x590(%r15)
    thread_data[x].thread_count = thread_count;
    30c8:	48 8b 05 79 49 00 00 	mov    0x4979(%rip),%rax        # 7a48 <_IO_stdin_used+0xa48>
    30cf:	49 89 87 98 05 00 00 	mov    %rax,0x598(%r15)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    30d6:	e8 c5 f3 ff ff       	call   24a0 <pthread_create@plt>
    30db:	48 8d 3d 87 42 00 00 	lea    0x4287(%rip),%rdi        # 7369 <_IO_stdin_used+0x369>
    30e2:	e8 29 f2 ff ff       	call   2310 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    30e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    void * result; 
    pthread_join(thread[x], &result);
    30f0:	4b 8b 3c ee          	mov    (%r14,%r13,8),%rdi
    30f4:	4c 89 e6             	mov    %r12,%rsi
    30f7:	e8 34 f4 ff ff       	call   2530 <pthread_join@plt>
    30fc:	44 89 ea             	mov    %r13d,%edx
    30ff:	48 89 de             	mov    %rbx,%rsi
    3102:	bf 01 00 00 00       	mov    $0x1,%edi
    3107:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3109:	49 83 c5 01          	add    $0x1,%r13
    310d:	e8 6e f3 ff ff       	call   2480 <__printf_chk@plt>
    3112:	49 83 fd 09          	cmp    $0x9,%r13
    3116:	75 d8                	jne    30f0 <main+0xac0>
    3118:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
    311f:	45 31 d2             	xor    %r10d,%r10d
  long ingests = 0;
    3122:	45 31 db             	xor    %r11d,%r11d
  long sents = 0;
  long received = 0;
    3125:	31 db                	xor    %ebx,%ebx
  for (int x = 0 ; x < thread_count ; x++) {
    3127:	c7 45 b0 00 00 00 00 	movl   $0x0,-0x50(%rbp)
  long sents = 0;
    312e:	45 31 e4             	xor    %r12d,%r12d
  long total = 0;
    3131:	31 c9                	xor    %ecx,%ecx
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3133:	49 bf db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r15
    313d:	4c 8d 70 28          	lea    0x28(%rax),%r14
    3141:	48 8b 85 58 ff ff ff 	mov    -0xa8(%rbp),%rax
    3148:	4c 89 5d a8          	mov    %r11,-0x58(%rbp)
    314c:	4c 89 55 a0          	mov    %r10,-0x60(%rbp)
    3150:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    3154:	0f 1f 40 00          	nopl   0x0(%rax)
    if (x % 2 == 1) {
    3158:	8b 7d b0             	mov    -0x50(%rbp),%edi
    315b:	48 89 4d 98          	mov    %rcx,-0x68(%rbp)
    315f:	89 f8                	mov    %edi,%eax
    3161:	41 89 fd             	mov    %edi,%r13d
      other = (x + 1) % total_threads;
    3164:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
    3167:	83 e0 01             	and    $0x1,%eax
      other = abs(x - 1) % total_threads;
    316a:	41 83 ed 01          	sub    $0x1,%r13d
      other = (x + 1) % total_threads;
    316e:	89 7d b0             	mov    %edi,-0x50(%rbp)
      other = abs(x - 1) % total_threads;
    3171:	85 c0                	test   %eax,%eax
    3173:	44 0f 44 ef          	cmove  %edi,%r13d
    3177:	bf 0a 00 00 00       	mov    $0xa,%edi
    317c:	e8 6f f1 ff ff       	call   22f0 <putchar@plt>
    3181:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    3185:	bf 01 00 00 00       	mov    $0x1,%edi
    318a:	48 8d 35 0a 42 00 00 	lea    0x420a(%rip),%rsi        # 739b <_IO_stdin_used+0x39b>
    3191:	48 8b 10             	mov    (%rax),%rdx
    3194:	31 c0                	xor    %eax,%eax
    3196:	e8 e5 f2 ff ff       	call   2480 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    319b:	49 63 56 08          	movslq 0x8(%r14),%rdx
    319f:	48 8b 4d 98          	mov    -0x68(%rbp),%rcx
    31a3:	85 d2                	test   %edx,%edx
    31a5:	0f 8e cf 03 00 00    	jle    357a <main+0xf4a>
    31ab:	49 8b 06             	mov    (%r14),%rax
    31ae:	48 c1 e2 09          	shl    $0x9,%rdx
    31b2:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    long v = 0;
    31b6:	31 d2                	xor    %edx,%edx
    31b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      v += thread_data[me].tasks[n].v;
    31c0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    31c7:	48 05 00 02 00 00    	add    $0x200,%rax
    31cd:	48 39 f0             	cmp    %rsi,%rax
    31d0:	75 ee                	jne    31c0 <main+0xb90>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    31d2:	4d 63 ed             	movslq %r13d,%r13
    31d5:	48 8b bd 78 ff ff ff 	mov    -0x88(%rbp),%rdi
    31dc:	4b 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%rax
    31e1:	49 8d 44 45 00       	lea    0x0(%r13,%rax,2),%rax
    31e6:	48 c1 e0 04          	shl    $0x4,%rax
    31ea:	48 01 f8             	add    %rdi,%rax
    31ed:	48 63 70 30          	movslq 0x30(%rax),%rsi
    31f1:	85 f6                	test   %esi,%esi
    31f3:	7e 1d                	jle    3212 <main+0xbe2>
    31f5:	48 8b 40 28          	mov    0x28(%rax),%rax
    31f9:	48 c1 e6 09          	shl    $0x9,%rsi
    31fd:	48 01 c6             	add    %rax,%rsi
      v += thread_data[other].tasks[n].v;
    3200:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3207:	48 05 00 02 00 00    	add    $0x200,%rax
    320d:	48 39 c6             	cmp    %rax,%rsi
    3210:	75 ee                	jne    3200 <main+0xbd0>
    3212:	48 8d 35 97 41 00 00 	lea    0x4197(%rip),%rsi        # 73b0 <_IO_stdin_used+0x3b0>
    3219:	bf 01 00 00 00       	mov    $0x1,%edi
    321e:	31 c0                	xor    %eax,%eax
    3220:	48 89 4d 98          	mov    %rcx,-0x68(%rbp)
    3224:	e8 57 f2 ff ff       	call   2480 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3229:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    322d:	bf 01 00 00 00       	mov    $0x1,%edi
    3232:	48 8b 30             	mov    (%rax),%rsi
    3235:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    323f:	48 f7 ee             	imul   %rsi
    3242:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3246:	31 c0                	xor    %eax,%eax
    3248:	48 d1 fa             	sar    %rdx
    324b:	48 29 f2             	sub    %rsi,%rdx
    324e:	48 8d 35 cb 43 00 00 	lea    0x43cb(%rip),%rsi        # 7620 <_IO_stdin_used+0x620>
    3255:	e8 26 f2 ff ff       	call   2480 <__printf_chk@plt>
    325a:	bf 0a 00 00 00       	mov    $0xa,%edi
    325f:	e8 8c f0 ff ff       	call   22f0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3264:	49 63 46 08          	movslq 0x8(%r14),%rax
    3268:	48 8b 4d 98          	mov    -0x68(%rbp),%rcx
    326c:	85 c0                	test   %eax,%eax
    326e:	0f 8e 88 00 00 00    	jle    32fc <main+0xccc>
    3274:	49 8b 16             	mov    (%r14),%rdx
    3277:	48 c1 e0 09          	shl    $0x9,%rax
    327b:	4c 8b 5d a8          	mov    -0x58(%rbp),%r11
    327f:	4c 8b 4d a0          	mov    -0x60(%rbp),%r9
    3283:	48 8d 34 10          	lea    (%rax,%rdx,1),%rsi
    3287:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3290:	48 8b 82 68 01 00 00 	mov    0x168(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    3297:	48 03 8a 08 01 00 00 	add    0x108(%rdx),%rcx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    329e:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
      ingests += thread_data[x].tasks[n].ingest_count;
    32a5:	4c 03 9a 60 ff ff ff 	add    -0xa0(%rdx),%r11
      sends += thread_data[x].tasks[n].sends;
    32ac:	4c 03 8a 70 ff ff ff 	add    -0x90(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    32b3:	4c 03 60 10          	add    0x10(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    32b7:	48 03 58 18          	add    0x18(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    32bb:	4c 03 60 30          	add    0x30(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    32bf:	48 03 58 38          	add    0x38(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    32c3:	4c 03 60 50          	add    0x50(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    32c7:	48 03 58 58          	add    0x58(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    32cb:	4c 03 60 70          	add    0x70(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    32cf:	48 03 58 78          	add    0x78(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    32d3:	4c 03 a0 90 00 00 00 	add    0x90(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    32da:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    32e1:	4c 03 a0 b0 00 00 00 	add    0xb0(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    32e8:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    32ef:	48 39 f2             	cmp    %rsi,%rdx
    32f2:	75 9c                	jne    3290 <main+0xc60>
    32f4:	4c 89 5d a8          	mov    %r11,-0x58(%rbp)
    32f8:	4c 89 4d a0          	mov    %r9,-0x60(%rbp)
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    32fc:	45 31 ed             	xor    %r13d,%r13d
    32ff:	49 83 7e 68 00       	cmpq   $0x0,0x68(%r14)
    3304:	7e 7e                	jle    3384 <main+0xd54>
    3306:	48 89 d8             	mov    %rbx,%rax
    3309:	4c 89 65 98          	mov    %r12,-0x68(%rbp)
    330d:	4c 89 f3             	mov    %r14,%rbx
    3310:	4d 89 ec             	mov    %r13,%r12
    3313:	49 89 c6             	mov    %rax,%r14
    3316:	49 89 cd             	mov    %rcx,%r13
    3319:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3320:	48 8b 43 58          	mov    0x58(%rbx),%rax
    3324:	4b 8d 14 a4          	lea    (%r12,%r12,4),%rdx
    3328:	48 83 ec 08          	sub    $0x8,%rsp
    332c:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3331:	49 83 c4 01          	add    $0x1,%r12
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3335:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3339:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    333d:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3341:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3344:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3348:	4c 2b 01             	sub    (%rcx),%r8
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    334b:	49 f7 e7             	mul    %r15
    334e:	8b 49 20             	mov    0x20(%rcx),%ecx
    3351:	56                   	push   %rsi
    3352:	31 c0                	xor    %eax,%eax
    3354:	48 8d 35 e5 42 00 00 	lea    0x42e5(%rip),%rsi        # 7640 <_IO_stdin_used+0x640>
    335b:	48 c1 ea 12          	shr    $0x12,%rdx
    335f:	49 89 d1             	mov    %rdx,%r9
    3362:	ba 02 00 00 00       	mov    $0x2,%edx
    3367:	e8 14 f1 ff ff       	call   2480 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    336c:	58                   	pop    %rax
    336d:	5a                   	pop    %rdx
    336e:	4c 39 63 68          	cmp    %r12,0x68(%rbx)
    3372:	7f ac                	jg     3320 <main+0xcf0>
    3374:	4c 89 f0             	mov    %r14,%rax
    3377:	4c 8b 65 98          	mov    -0x68(%rbp),%r12
    337b:	49 89 de             	mov    %rbx,%r14
    337e:	4c 89 e9             	mov    %r13,%rcx
    3381:	48 89 c3             	mov    %rax,%rbx
  for (int x = 0 ; x < thread_count ; x++) {
    3384:	48 83 45 b8 18       	addq   $0x18,-0x48(%rbp)
    3389:	49 81 c6 b0 00 00 00 	add    $0xb0,%r14
    3390:	83 7d b0 06          	cmpl   $0x6,-0x50(%rbp)
    3394:	0f 85 be fd ff ff    	jne    3158 <main+0xb28>
    339a:	4c 8b 5d a8          	mov    -0x58(%rbp),%r11
    339e:	4c 8b 55 a0          	mov    -0x60(%rbp),%r10
    33a2:	48 89 ca             	mov    %rcx,%rdx
    33a5:	bf 01 00 00 00       	mov    $0x1,%edi
    33aa:	48 8d 35 0c 40 00 00 	lea    0x400c(%rip),%rsi        # 73bd <_IO_stdin_used+0x3bd>
    33b1:	31 c0                	xor    %eax,%eax
    33b3:	48 89 4d b8          	mov    %rcx,-0x48(%rbp)
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    33b7:	49 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r13
    33c1:	4c 89 55 a8          	mov    %r10,-0x58(%rbp)
    33c5:	4c 89 5d b0          	mov    %r11,-0x50(%rbp)
    33c9:	e8 b2 f0 ff ff       	call   2480 <__printf_chk@plt>
    33ce:	bf 0a 00 00 00       	mov    $0xa,%edi
    33d3:	e8 18 ef ff ff       	call   22f0 <putchar@plt>
    33d8:	48 8b 85 58 ff ff ff 	mov    -0xa8(%rbp),%rax
    33df:	bf 01 00 00 00       	mov    $0x1,%edi
    33e4:	48 8d 35 a5 42 00 00 	lea    0x42a5(%rip),%rsi        # 7690 <_IO_stdin_used+0x690>
    33eb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    33ef:	31 c0                	xor    %eax,%eax
    33f1:	e8 8a f0 ff ff       	call   2480 <__printf_chk@plt>
    33f6:	4c 8b 5d b0          	mov    -0x50(%rbp),%r11
    33fa:	bf 01 00 00 00       	mov    $0x1,%edi
    33ff:	48 8d 35 b2 42 00 00 	lea    0x42b2(%rip),%rsi        # 76b8 <_IO_stdin_used+0x6b8>
    3406:	4c 89 d8             	mov    %r11,%rax
    3409:	49 c1 fb 3f          	sar    $0x3f,%r11
    340d:	49 f7 ed             	imul   %r13
    3410:	31 c0                	xor    %eax,%eax
    3412:	48 d1 fa             	sar    %rdx
    3415:	4c 29 da             	sub    %r11,%rdx
    3418:	e8 63 f0 ff ff       	call   2480 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    341d:	4c 8b 55 a8          	mov    -0x58(%rbp),%r10
    3421:	bf 01 00 00 00       	mov    $0x1,%edi
    3426:	48 8d 35 bb 42 00 00 	lea    0x42bb(%rip),%rsi        # 76e8 <_IO_stdin_used+0x6e8>
    342d:	4c 89 d0             	mov    %r10,%rax
    3430:	49 c1 fa 3f          	sar    $0x3f,%r10
    3434:	49 f7 ed             	imul   %r13
    3437:	31 c0                	xor    %eax,%eax
    3439:	48 d1 fa             	sar    %rdx
    343c:	4c 29 d2             	sub    %r10,%rdx
    343f:	e8 3c f0 ff ff       	call   2480 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3444:	48 8b 4d b8          	mov    -0x48(%rbp),%rcx
    3448:	bf 01 00 00 00       	mov    $0x1,%edi
    344d:	48 8d 35 c4 42 00 00 	lea    0x42c4(%rip),%rsi        # 7718 <_IO_stdin_used+0x718>
    3454:	48 89 c8             	mov    %rcx,%rax
    3457:	48 c1 f9 3f          	sar    $0x3f,%rcx
    345b:	49 f7 ed             	imul   %r13
    345e:	31 c0                	xor    %eax,%eax
    3460:	48 d1 fa             	sar    %rdx
    3463:	48 29 ca             	sub    %rcx,%rdx
    3466:	e8 15 f0 ff ff       	call   2480 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    346b:	4c 89 e0             	mov    %r12,%rax
    346e:	49 c1 fc 3f          	sar    $0x3f,%r12
    3472:	48 8d 35 58 3f 00 00 	lea    0x3f58(%rip),%rsi        # 73d1 <_IO_stdin_used+0x3d1>
    3479:	49 f7 ed             	imul   %r13
    347c:	bf 01 00 00 00       	mov    $0x1,%edi
    3481:	31 c0                	xor    %eax,%eax
    3483:	48 d1 fa             	sar    %rdx
    3486:	4c 29 e2             	sub    %r12,%rdx
    3489:	e8 f2 ef ff ff       	call   2480 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    348e:	48 89 d8             	mov    %rbx,%rax
    3491:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3495:	48 8d 35 46 3f 00 00 	lea    0x3f46(%rip),%rsi        # 73e2 <_IO_stdin_used+0x3e2>
    349c:	49 f7 ed             	imul   %r13
    349f:	bf 01 00 00 00       	mov    $0x1,%edi
    34a4:	48 d1 fa             	sar    %rdx
    34a7:	48 29 da             	sub    %rbx,%rdx
    34aa:	31 c0                	xor    %eax,%eax
    34ac:	e8 cf ef ff ff       	call   2480 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    34b1:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    34b5:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    34be:	0f 85 bd 00 00 00    	jne    3581 <main+0xf51>
    34c4:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
    34c8:	31 c0                	xor    %eax,%eax
    34ca:	5b                   	pop    %rbx
    34cb:	41 5c                	pop    %r12
    34cd:	41 5d                	pop    %r13
    34cf:	41 5e                	pop    %r14
    34d1:	41 5f                	pop    %r15
    34d3:	5d                   	pop    %rbp
    34d4:	c3                   	ret
    34d5:	0f 1f 00             	nopl   (%rax)
          thread_data[x].tasks[y].run = barriered_work; 
    34d8:	48 8d 05 81 23 00 00 	lea    0x2381(%rip),%rax        # 5860 <barriered_work>
    34df:	bb 02 00 00 00       	mov    $0x2,%ebx
    34e4:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    34ec:	e9 da f4 ff ff       	jmp    29cb <main+0x39b>
    34f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    34f8:	45 89 ea             	mov    %r13d,%r10d
      my_thread_data[0] = &thread_data[x]; 
    34fb:	4c 89 0b             	mov    %r9,(%rbx)
    34fe:	4c 89 c9             	mov    %r9,%rcx
    3501:	48 8d 35 f1 3d 00 00 	lea    0x3df1(%rip),%rsi        # 72f9 <_IO_stdin_used+0x2f9>
    3508:	4c 89 d7             	mov    %r10,%rdi
      other = (x + 1) % total_threads;
    350b:	4d 69 d2 39 8e e3 38 	imul   $0x38e38e39,%r10,%r10
      thread_data[x].thread_index = 0;
    3512:	41 c7 01 00 00 00 00 	movl   $0x0,(%r9)
    3519:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
      other = (x + 1) % total_threads;
    351d:	49 c1 ea 21          	shr    $0x21,%r10
    3521:	43 8d 04 d2          	lea    (%r10,%r10,8),%eax
    3525:	29 c7                	sub    %eax,%edi
    3527:	48 63 c7             	movslq %edi,%rax
    352a:	bf 01 00 00 00       	mov    $0x1,%edi
      my_thread_data[1] = &thread_data[other]; 
    352f:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
      other = (x + 1) % total_threads;
    3533:	49 89 c5             	mov    %rax,%r13
      my_thread_data[1] = &thread_data[other]; 
    3536:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    353a:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
    3541:	44 89 f2             	mov    %r14d,%edx
    3544:	49 c1 e0 04          	shl    $0x4,%r8
    3548:	49 01 c0             	add    %rax,%r8
    354b:	31 c0                	xor    %eax,%eax
    354d:	4c 89 43 08          	mov    %r8,0x8(%rbx)
    3551:	e8 2a ef ff ff       	call   2480 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    3556:	49 8d 47 18          	lea    0x18(%r15),%rax
    355a:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    355e:	48 89 45 80          	mov    %rax,-0x80(%rbp)
    3562:	49 89 c7             	mov    %rax,%r15
    3565:	e9 31 f3 ff ff       	jmp    289b <main+0x26b>
          CPU_SET(j, sendercpu);
    356a:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    356e:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
        for (int j = 0 ; j < cores ; j++) {
    3575:	e9 a0 f3 ff ff       	jmp    291a <main+0x2ea>
    long v = 0;
    357a:	31 d2                	xor    %edx,%edx
    357c:	e9 51 fc ff ff       	jmp    31d2 <main+0xba2>
}
    3581:	e8 ca ed ff ff       	call   2350 <__stack_chk_fail@plt>
    3586:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003590 <_start>:
    3590:	f3 0f 1e fa          	endbr64
    3594:	31 ed                	xor    %ebp,%ebp
    3596:	49 89 d1             	mov    %rdx,%r9
    3599:	5e                   	pop    %rsi
    359a:	48 89 e2             	mov    %rsp,%rdx
    359d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    35a1:	50                   	push   %rax
    35a2:	54                   	push   %rsp
    35a3:	45 31 c0             	xor    %r8d,%r8d
    35a6:	31 c9                	xor    %ecx,%ecx
    35a8:	48 8d 3d 81 f0 ff ff 	lea    -0xf7f(%rip),%rdi        # 2630 <main>
    35af:	ff 15 1b 6a 00 00    	call   *0x6a1b(%rip)        # 9fd0 <__libc_start_main@GLIBC_2.34>
    35b5:	f4                   	hlt
    35b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000035c0 <__gmon_start__>:
    35c0:	f3 0f 1e fa          	endbr64
    35c4:	8b 05 5e 6a 00 00    	mov    0x6a5e(%rip),%eax        # a028 <called.0>
    35ca:	85 c0                	test   %eax,%eax
    35cc:	74 02                	je     35d0 <__gmon_start__+0x10>
    35ce:	c3                   	ret
    35cf:	90                   	nop
    35d0:	48 83 ec 08          	sub    $0x8,%rsp
    35d4:	48 8d 35 62 2c 00 00 	lea    0x2c62(%rip),%rsi        # 623d <etext>
    35db:	48 8d 3d 1e ca ff ff 	lea    -0x35e2(%rip),%rdi        # 0 <__executable_start>
    35e2:	c7 05 3c 6a 00 00 01 00 00 00 	movl   $0x1,0x6a3c(%rip)        # a028 <called.0>
    35ec:	e8 ef ed ff ff       	call   23e0 <__monstartup@plt>
    35f1:	48 8b 3d e8 69 00 00 	mov    0x69e8(%rip),%rdi        # 9fe0 <_mcleanup@GLIBC_2.2.5>
    35f8:	48 83 c4 08          	add    $0x8,%rsp
    35fc:	e9 ff 2b 00 00       	jmp    6200 <atexit>
    3601:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    360b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003610 <_dl_relocate_static_pie>:
    3610:	f3 0f 1e fa          	endbr64
    3614:	c3                   	ret
    3615:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    361f:	90                   	nop

0000000000003620 <deregister_tm_clones>:
    3620:	48 8d 3d f9 69 00 00 	lea    0x69f9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3627:	48 8d 05 f2 69 00 00 	lea    0x69f2(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    362e:	48 39 f8             	cmp    %rdi,%rax
    3631:	74 15                	je     3648 <deregister_tm_clones+0x28>
    3633:	48 8b 05 9e 69 00 00 	mov    0x699e(%rip),%rax        # 9fd8 <_ITM_deregisterTMCloneTable@Base>
    363a:	48 85 c0             	test   %rax,%rax
    363d:	74 09                	je     3648 <deregister_tm_clones+0x28>
    363f:	ff e0                	jmp    *%rax
    3641:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3648:	c3                   	ret
    3649:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003650 <register_tm_clones>:
    3650:	48 8d 3d c9 69 00 00 	lea    0x69c9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3657:	48 8d 35 c2 69 00 00 	lea    0x69c2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    365e:	48 29 fe             	sub    %rdi,%rsi
    3661:	48 89 f0             	mov    %rsi,%rax
    3664:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3668:	48 c1 f8 03          	sar    $0x3,%rax
    366c:	48 01 c6             	add    %rax,%rsi
    366f:	48 d1 fe             	sar    %rsi
    3672:	74 14                	je     3688 <register_tm_clones+0x38>
    3674:	48 8b 05 75 69 00 00 	mov    0x6975(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    367b:	48 85 c0             	test   %rax,%rax
    367e:	74 08                	je     3688 <register_tm_clones+0x38>
    3680:	ff e0                	jmp    *%rax
    3682:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3688:	c3                   	ret
    3689:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003690 <__do_global_dtors_aux>:
    3690:	f3 0f 1e fa          	endbr64
    3694:	80 3d 91 69 00 00 00 	cmpb   $0x0,0x6991(%rip)        # a02c <completed.0>
    369b:	75 2b                	jne    36c8 <__do_global_dtors_aux+0x38>
    369d:	55                   	push   %rbp
    369e:	48 83 3d 52 69 00 00 00 	cmpq   $0x0,0x6952(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    36a6:	48 89 e5             	mov    %rsp,%rbp
    36a9:	74 0c                	je     36b7 <__do_global_dtors_aux+0x27>
    36ab:	48 8b 3d 56 69 00 00 	mov    0x6956(%rip),%rdi        # a008 <__dso_handle>
    36b2:	e8 19 ec ff ff       	call   22d0 <__cxa_finalize@plt>
    36b7:	e8 64 ff ff ff       	call   3620 <deregister_tm_clones>
    36bc:	c6 05 69 69 00 00 01 	movb   $0x1,0x6969(%rip)        # a02c <completed.0>
    36c3:	5d                   	pop    %rbp
    36c4:	c3                   	ret
    36c5:	0f 1f 00             	nopl   (%rax)
    36c8:	c3                   	ret
    36c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000036d0 <frame_dummy>:
    36d0:	f3 0f 1e fa          	endbr64
    36d4:	e9 77 ff ff ff       	jmp    3650 <register_tm_clones>
    36d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000036e0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    36e0:	f3 0f 1e fa          	endbr64
    36e4:	55                   	push   %rbp
    36e5:	48 89 e5             	mov    %rsp,%rbp
    36e8:	ff 15 fa 68 00 00    	call   *0x68fa(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  struct ProtectedState *protected = data->thread->protected_state;
    36ee:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    36f5:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    36f9:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3701:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    3705:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3709:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3710:	48 85 c9             	test   %rcx,%rcx
    3713:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    371a:	48 0f 4f d6          	cmovg  %rsi,%rdx
    371e:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3722:	31 c0                	xor    %eax,%eax
    3724:	5d                   	pop    %rbp
    3725:	c3                   	ret
    3726:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003730 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3730:	f3 0f 1e fa          	endbr64
    3734:	55                   	push   %rbp
    3735:	48 89 e5             	mov    %rsp,%rbp
    3738:	ff 15 aa 68 00 00    	call   *0x68aa(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    for (int x = 0 ; x < data->task_count ; x++) {
    373e:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    3745:	85 c9                	test   %ecx,%ecx
    3747:	7e 4d                	jle    3796 <barriered_reset+0x66>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3749:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3750:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    3757:	48 c1 e1 09          	shl    $0x9,%rcx
    375b:	48 8b 50 10          	mov    0x10(%rax),%rdx
    375f:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3763:	48 8b 70 28          	mov    0x28(%rax),%rsi
    3767:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3769:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    376d:	0f 1f 00             	nopl   (%rax)
    3770:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3778:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3780:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    378b:	48 05 00 02 00 00    	add    $0x200,%rax
    3791:	48 39 c1             	cmp    %rax,%rcx
    3794:	75 da                	jne    3770 <barriered_reset+0x40>
  asm volatile ("sfence" ::: "memory");
    3796:	0f ae f8             	sfence
}
    3799:	31 c0                	xor    %eax,%eax
    379b:	5d                   	pop    %rbp
    379c:	c3                   	ret
    379d:	0f 1f 00             	nopl   (%rax)

00000000000037a0 <barriered_thread>:
void* barriered_thread(void *arg) {
    37a0:	f3 0f 1e fa          	endbr64
    37a4:	55                   	push   %rbp
    37a5:	48 89 e5             	mov    %rsp,%rbp
    37a8:	41 57                	push   %r15
    37aa:	41 56                	push   %r14
    37ac:	41 55                	push   %r13
    37ae:	41 54                	push   %r12
    37b0:	53                   	push   %rbx
    37b1:	48 83 ec 08          	sub    $0x8,%rsp
    37b5:	ff 15 2d 68 00 00    	call   *0x682d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  int waiting = 0;
    37bb:	45 31 e4             	xor    %r12d,%r12d
  int t = 0;
    37be:	31 db                	xor    %ebx,%ebx
void* barriered_thread(void *arg) {
    37c0:	49 89 fe             	mov    %rdi,%r14
  while (data->running == 1) {
    37c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    37c8:	41 83 7e 34 01       	cmpl   $0x1,0x34(%r14)
    37cd:	0f 85 3e 02 00 00    	jne    3a11 <barriered_thread+0x271>
    if (t >= data->task_count) {
    37d3:	41 8b 56 30          	mov    0x30(%r14),%edx
    37d7:	39 da                	cmp    %ebx,%edx
    37d9:	7f 0e                	jg     37e9 <barriered_thread+0x49>
      data->cycles++;
    37db:	49 83 86 98 00 00 00 01 	addq   $0x1,0x98(%r14)
    for (; t < data->task_count; t++) {
    37e3:	31 db                	xor    %ebx,%ebx
    37e5:	85 d2                	test   %edx,%edx
    37e7:	7e df                	jle    37c8 <barriered_thread+0x28>
    37e9:	4c 63 eb             	movslq %ebx,%r13
    37ec:	49 c1 e5 09          	shl    $0x9,%r13
    37f0:	eb 14                	jmp    3806 <barriered_thread+0x66>
    37f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    37f8:	83 c3 01             	add    $0x1,%ebx
    37fb:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    3802:	39 d3                	cmp    %edx,%ebx
    3804:	7d c2                	jge    37c8 <barriered_thread+0x28>
      if (data->tasks[t].available == 1) {
    3806:	49 8b 46 28          	mov    0x28(%r14),%rax
    380a:	4a 8d 34 28          	lea    (%rax,%r13,1),%rsi
    380e:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    3815:	75 e1                	jne    37f8 <barriered_thread+0x58>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3817:	41 8b 7e 18          	mov    0x18(%r14),%edi
          previous = t - 1;
    381b:	83 ea 01             	sub    $0x1,%edx
    381e:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3821:	85 db                	test   %ebx,%ebx
    3823:	0f 4f d1             	cmovg  %ecx,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3826:	85 ff                	test   %edi,%edi
    3828:	0f 8e 92 01 00 00    	jle    39c0 <barriered_thread+0x220>
    382e:	49 8b 46 10          	mov    0x10(%r14),%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3832:	48 63 ca             	movslq %edx,%rcx
    3835:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    3838:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    383b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    3842:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3849:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    384d:	45 31 ff             	xor    %r15d,%r15d
    3850:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3854:	0f 1f 40 00          	nopl   0x0(%rax)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3858:	48 8b 10             	mov    (%rax),%rdx
    385b:	4c 8b 5a 28          	mov    0x28(%rdx),%r11
    385f:	49 01 cb             	add    %rcx,%r11
    3862:	4c 89 da             	mov    %r11,%rdx
    3865:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    386c:	75 04                	jne    3872 <barriered_thread+0xd2>
            arrived++;
    386e:	41 83 c7 01          	add    $0x1,%r15d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    3872:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    3879:	75 04                	jne    387f <barriered_thread+0xdf>
            prearrive++;
    387b:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    387f:	48 83 c0 08          	add    $0x8,%rax
    3883:	48 39 f0             	cmp    %rsi,%rax
    3886:	75 d0                	jne    3858 <barriered_thread+0xb8>
        if (prearrive == 0 || prearrive == data->thread_count) {
    3888:	44 39 d7             	cmp    %r10d,%edi
    388b:	0f 84 8f 00 00 00    	je     3920 <barriered_thread+0x180>
    3891:	45 85 d2             	test   %r10d,%r10d
    3894:	0f 84 86 00 00 00    	je     3920 <barriered_thread+0x180>
        if (arrived == 0 || arrived == data->thread_count) {
    389a:	45 85 ff             	test   %r15d,%r15d
    389d:	74 0a                	je     38a9 <barriered_thread+0x109>
    389f:	45 39 7e 18          	cmp    %r15d,0x18(%r14)
    38a3:	0f 85 1f ff ff ff    	jne    37c8 <barriered_thread+0x28>
    38a9:	49 8b 46 28          	mov    0x28(%r14),%rax
          data->tasks[t].prearrive++;
    38ad:	4c 01 e8             	add    %r13,%rax
    38b0:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    38b7:	85 db                	test   %ebx,%ebx
    38b9:	75 0e                	jne    38c9 <barriered_thread+0x129>
    38bb:	49 8b 76 70          	mov    0x70(%r14),%rsi
    38bf:	49 3b 76 78          	cmp    0x78(%r14),%rsi
    38c3:	0f 8c cf 00 00 00    	jl     3998 <barriered_thread+0x1f8>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    38c9:	49 63 0e             	movslq (%r14),%rcx
    38cc:	49 8b 56 10          	mov    0x10(%r14),%rdx
          data->tasks[t].available = 0;
    38d0:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    38da:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    38de:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
    38e2:	4c 01 ef             	add    %r13,%rdi
    38e5:	ff 90 18 01 00 00    	call   *0x118(%rax)
          data->tasks[t].arrived++;
    38eb:	49 8b 46 28          	mov    0x28(%r14),%rax
    38ef:	4c 01 e8             	add    %r13,%rax
    38f2:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    38f9:	41 8b 46 30          	mov    0x30(%r14),%eax
          data->iteration_count++;
    38fd:	49 83 46 68 01       	addq   $0x1,0x68(%r14)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3902:	83 e8 01             	sub    $0x1,%eax
    3905:	39 d8                	cmp    %ebx,%eax
    3907:	74 2f                	je     3938 <barriered_thread+0x198>
          asm volatile ("sfence" ::: "memory");
    3909:	0f ae f8             	sfence
          if (waiting == 0) {
    390c:	45 85 e4             	test   %r12d,%r12d
    390f:	74 4f                	je     3960 <barriered_thread+0x1c0>
    for (; t < data->task_count; t++) {
    3911:	41 8b 56 30          	mov    0x30(%r14),%edx
    3915:	e9 de fe ff ff       	jmp    37f8 <barriered_thread+0x58>
    391a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (waiting == 1) {
    3920:	41 83 fc 01          	cmp    $0x1,%r12d
    3924:	0f 84 a6 00 00 00    	je     39d0 <barriered_thread+0x230>
        int arrived = 0; 
    392a:	45 31 e4             	xor    %r12d,%r12d
    392d:	e9 68 ff ff ff       	jmp    389a <barriered_thread+0xfa>
    3932:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3938:	49 8b 76 70          	mov    0x70(%r14),%rsi
    393c:	49 3b 76 78          	cmp    0x78(%r14),%rsi
    3940:	7d c7                	jge    3909 <barriered_thread+0x169>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    3942:	48 c1 e6 04          	shl    $0x4,%rsi
    3946:	bf 04 00 00 00       	mov    $0x4,%edi
    394b:	49 03 76 60          	add    0x60(%r14),%rsi
    394f:	e8 dc e9 ff ff       	call   2330 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3954:	49 83 46 70 01       	addq   $0x1,0x70(%r14)
    3959:	eb ae                	jmp    3909 <barriered_thread+0x169>
    395b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    3960:	49 8b 86 88 00 00 00 	mov    0x88(%r14),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3967:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    396c:	41 bc 01 00 00 00    	mov    $0x1,%r12d
            data->task_snapshot[data->task_timestamp_count].task = t;
    3972:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3976:	49 8b 86 80 00 00 00 	mov    0x80(%r14),%rax
    397d:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3981:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3984:	e8 a7 e9 ff ff       	call   2330 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3989:	41 8b 56 30          	mov    0x30(%r14),%edx
    398d:	e9 66 fe ff ff       	jmp    37f8 <barriered_thread+0x58>
    3992:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3998:	48 c1 e6 04          	shl    $0x4,%rsi
    399c:	bf 04 00 00 00       	mov    $0x4,%edi
    39a1:	49 03 76 58          	add    0x58(%r14),%rsi
    39a5:	e8 86 e9 ff ff       	call   2330 <clock_gettime@plt>
          data->tasks[t].available = 0;
    39aa:	49 8b 46 28          	mov    0x28(%r14),%rax
    39ae:	4c 01 e8             	add    %r13,%rax
    39b1:	e9 13 ff ff ff       	jmp    38c9 <barriered_thread+0x129>
    39b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
    39c0:	41 83 fc 01          	cmp    $0x1,%r12d
    39c4:	0f 85 e3 fe ff ff    	jne    38ad <barriered_thread+0x10d>
        int arrived = 0; 
    39ca:	45 31 ff             	xor    %r15d,%r15d
    39cd:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    39d0:	49 8b 86 88 00 00 00 	mov    0x88(%r14),%rax
    39d7:	bf 04 00 00 00       	mov    $0x4,%edi
    39dc:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    39e0:	49 8b 86 80 00 00 00 	mov    0x80(%r14),%rax
    39e7:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    39ec:	e8 3f e9 ff ff       	call   2330 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    39f1:	49 8b 86 88 00 00 00 	mov    0x88(%r14),%rax
    39f8:	48 83 c0 01          	add    $0x1,%rax
    39fc:	48 99                	cqto
    39fe:	49 f7 be 90 00 00 00 	idivq  0x90(%r14)
    3a05:	49 89 96 88 00 00 00 	mov    %rdx,0x88(%r14)
            waiting = 0; 
    3a0c:	e9 19 ff ff ff       	jmp    392a <barriered_thread+0x18a>
}
    3a11:	48 83 c4 08          	add    $0x8,%rsp
    3a15:	31 c0                	xor    %eax,%eax
    3a17:	5b                   	pop    %rbx
    3a18:	41 5c                	pop    %r12
    3a1a:	41 5d                	pop    %r13
    3a1c:	41 5e                	pop    %r14
    3a1e:	41 5f                	pop    %r15
    3a20:	5d                   	pop    %rbp
    3a21:	c3                   	ret
    3a22:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3a2d:	0f 1f 00             	nopl   (%rax)

0000000000003a30 <external_thread>:
void * external_thread(void *arg) {
    3a30:	f3 0f 1e fa          	endbr64
    3a34:	55                   	push   %rbp
    3a35:	48 89 e5             	mov    %rsp,%rbp
    3a38:	41 56                	push   %r14
    3a3a:	41 55                	push   %r13
    3a3c:	41 54                	push   %r12
    3a3e:	53                   	push   %rbx
    3a3f:	48 83 ec 30          	sub    $0x30,%rsp
    3a43:	ff 15 9f 65 00 00    	call   *0x659f(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  struct timespec req = {
    3a49:	66 0f 6f 05 df 3e 00 00 	movdqa 0x3edf(%rip),%xmm0        # 7930 <_IO_stdin_used+0x930>
void * external_thread(void *arg) {
    3a51:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3a5a:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    3a5e:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3a60:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
void * external_thread(void *arg) {
    3a64:	49 89 fe             	mov    %rdi,%r14
  struct timespec req = {
    3a67:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
  while (data->running == 1) {
    3a6b:	75 5f                	jne    3acc <external_thread+0x9c>
    3a6d:	4c 8d 65 c0          	lea    -0x40(%rbp),%r12
    3a71:	48 8d 5d b0          	lea    -0x50(%rbp),%rbx
        data->buffers->buffer[x].data = "Hello world";
    3a75:	4c 8d 2d 88 35 00 00 	lea    0x3588(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
    3a7c:	0f 1f 40 00          	nopl   0x0(%rax)
    nanosleep(&req , &rem);
    3a80:	4c 89 e6             	mov    %r12,%rsi
    3a83:	48 89 df             	mov    %rbx,%rdi
    3a86:	e8 e5 e8 ff ff       	call   2370 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3a8b:	49 8b 46 40          	mov    0x40(%r14),%rax
    3a8f:	48 63 10             	movslq (%rax),%rdx
    3a92:	85 d2                	test   %edx,%edx
    3a94:	7e 2c                	jle    3ac2 <external_thread+0x92>
    3a96:	48 8b 40 08          	mov    0x8(%rax),%rax
    3a9a:	48 c1 e2 04          	shl    $0x4,%rdx
    3a9e:	48 01 c2             	add    %rax,%rdx
    3aa1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    3aa8:	8b 48 08             	mov    0x8(%rax),%ecx
    3aab:	85 c9                	test   %ecx,%ecx
    3aad:	75 0a                	jne    3ab9 <external_thread+0x89>
        data->buffers->buffer[x].data = "Hello world";
    3aaf:	4c 89 28             	mov    %r13,(%rax)
        data->buffers->buffer[x].available = 1;
    3ab2:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3ab9:	48 83 c0 10          	add    $0x10,%rax
    3abd:	48 39 c2             	cmp    %rax,%rdx
    3ac0:	75 e6                	jne    3aa8 <external_thread+0x78>
    asm volatile ("mfence" ::: "memory");
    3ac2:	0f ae f0             	mfence
  while (data->running == 1) {
    3ac5:	41 83 7e 34 01       	cmpl   $0x1,0x34(%r14)
    3aca:	74 b4                	je     3a80 <external_thread+0x50>
}
    3acc:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    3ad0:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3ad9:	75 0f                	jne    3aea <external_thread+0xba>
    3adb:	48 83 c4 30          	add    $0x30,%rsp
    3adf:	31 c0                	xor    %eax,%eax
    3ae1:	5b                   	pop    %rbx
    3ae2:	41 5c                	pop    %r12
    3ae4:	41 5d                	pop    %r13
    3ae6:	41 5e                	pop    %r14
    3ae8:	5d                   	pop    %rbp
    3ae9:	c3                   	ret
    3aea:	e8 61 e8 ff ff       	call   2350 <__stack_chk_fail@plt>
    3aef:	90                   	nop

0000000000003af0 <timer_thread>:
void* timer_thread(void *arg) {
    3af0:	f3 0f 1e fa          	endbr64
    3af4:	55                   	push   %rbp
    3af5:	48 89 e5             	mov    %rsp,%rbp
    3af8:	41 57                	push   %r15
    3afa:	41 56                	push   %r14
    3afc:	41 55                	push   %r13
    3afe:	41 54                	push   %r12
    3b00:	53                   	push   %rbx
    3b01:	48 83 ec 68          	sub    $0x68,%rsp
    3b05:	ff 15 dd 64 00 00    	call   *0x64dd(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    3b0b:	48 8d 35 fe 34 00 00 	lea    0x34fe(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3b12:	8b 17                	mov    (%rdi),%edx
    3b14:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3b1d:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    3b21:	31 c0                	xor    %eax,%eax
    3b23:	49 89 fd             	mov    %rdi,%r13
    3b26:	bf 01 00 00 00       	mov    $0x1,%edi
    3b2b:	e8 50 e9 ff ff       	call   2480 <__printf_chk@plt>
  struct timespec preempt = {
    3b30:	66 0f 6f 05 f8 3d 00 00 	movdqa 0x3df8(%rip),%xmm0        # 7930 <_IO_stdin_used+0x930>
    3b38:	ba 88 13 00 00       	mov    $0x1388,%edx
    3b3d:	31 c0                	xor    %eax,%eax
    3b3f:	48 8d 35 dc 34 00 00 	lea    0x34dc(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3b46:	bf 01 00 00 00       	mov    $0x1,%edi
    3b4b:	0f 29 45 90          	movaps %xmm0,-0x70(%rbp)
    3b4f:	e8 2c e9 ff ff       	call   2480 <__printf_chk@plt>
  while (data->running && n < times) {
    3b54:	41 8b 45 34          	mov    0x34(%r13),%eax
    3b58:	89 85 7c ff ff ff    	mov    %eax,-0x84(%rbp)
    3b5e:	85 c0                	test   %eax,%eax
    3b60:	0f 84 b2 00 00 00    	je     3c18 <timer_thread+0x128>
  int n = 0;
    3b66:	45 31 ff             	xor    %r15d,%r15d
    3b69:	4c 8d 75 80          	lea    -0x80(%rbp),%r14
    3b6d:	4c 8d 65 90          	lea    -0x70(%rbp),%r12
    y++;
    3b71:	31 db                	xor    %ebx,%ebx
  int y = 0;
    3b73:	c7 85 7c ff ff ff 00 00 00 00 	movl   $0x0,-0x84(%rbp)
    nanosleep(&preempt , &rem2);
    3b7d:	4c 89 e7             	mov    %r12,%rdi
    3b80:	4c 89 f6             	mov    %r14,%rsi
    n++;
    3b83:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3b87:	e8 e4 e7 ff ff       	call   2370 <nanosleep@plt>
    y++;
    3b8c:	8b bd 7c ff ff ff    	mov    -0x84(%rbp),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b92:	49 63 45 18          	movslq 0x18(%r13),%rax
    y++;
    3b96:	83 c7 01             	add    $0x1,%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b99:	85 c0                	test   %eax,%eax
    3b9b:	7e 50                	jle    3bed <timer_thread+0xfd>
        data->threads[x]->tasks[y].scheduled = 0;
    3b9d:	48 63 95 7c ff ff ff 	movslq -0x84(%rbp),%rdx
    3ba4:	49 8b 4d 10          	mov    0x10(%r13),%rcx
    3ba8:	48 c1 e2 09          	shl    $0x9,%rdx
    3bac:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3bb0:	49 89 d1             	mov    %rdx,%r9
    3bb3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3bb8:	4c 8b 19             	mov    (%rcx),%r11
    3bbb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bbd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3bc1:	99                   	cltd
    3bc2:	41 f7 7b 30          	idivl  0x30(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    3bc6:	49 8b 73 28          	mov    0x28(%r11),%rsi
    3bca:	48 63 d2             	movslq %edx,%rdx
    3bcd:	48 c1 e2 09          	shl    $0x9,%rdx
    3bd1:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3bdc:	42 c7 84 0e 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r9,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3be8:	49 39 c8             	cmp    %rcx,%r8
    3beb:	75 cb                	jne    3bb8 <timer_thread+0xc8>
    asm volatile ("mfence" ::: "memory");
    3bed:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3bf0:	49 8b 45 10          	mov    0x10(%r13),%rax
  while (data->running && n < times) {
    3bf4:	41 8b 55 34          	mov    0x34(%r13),%edx
    if (y >= data->threads[0]->task_count) {
    3bf8:	48 8b 00             	mov    (%rax),%rax
    y++;
    3bfb:	39 78 30             	cmp    %edi,0x30(%rax)
    3bfe:	0f 4e fb             	cmovle %ebx,%edi
    3c01:	89 bd 7c ff ff ff    	mov    %edi,-0x84(%rbp)
  while (data->running && n < times) {
    3c07:	85 d2                	test   %edx,%edx
    3c09:	74 0d                	je     3c18 <timer_thread+0x128>
    3c0b:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    3c12:	0f 85 65 ff ff ff    	jne    3b7d <timer_thread+0x8d>
    3c18:	48 8d 3d 19 34 00 00 	lea    0x3419(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3c1f:	e8 ec e6 ff ff       	call   2310 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c24:	49 63 55 1c          	movslq 0x1c(%r13),%rdx
    3c28:	85 d2                	test   %edx,%edx
    3c2a:	7e 6b                	jle    3c97 <timer_thread+0x1a7>
    for (int y = 0 ; y < data->task_count ; y++) {
    3c2c:	49 63 45 30          	movslq 0x30(%r13),%rax
    3c30:	85 c0                	test   %eax,%eax
    3c32:	7e 63                	jle    3c97 <timer_thread+0x1a7>
    3c34:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3c38:	4d 8b 45 10          	mov    0x10(%r13),%r8
    3c3c:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3c44:	31 ff                	xor    %edi,%edi
    3c46:	48 89 c2             	mov    %rax,%rdx
    3c49:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3c4d:	48 8b 40 28          	mov    0x28(%rax),%rax
    3c51:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3c55:	f6 c6 02             	test   $0x2,%dh
    3c58:	74 15                	je     3c6f <timer_thread+0x17f>
    3c5a:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3c64:	48 05 00 02 00 00    	add    $0x200,%rax
    3c6a:	48 39 c6             	cmp    %rax,%rsi
    3c6d:	74 1f                	je     3c8e <timer_thread+0x19e>
      data->threads[x]->tasks[y].sending = 0;
    3c6f:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3c79:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3c7f:	c7 80 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3c89:	48 39 c6             	cmp    %rax,%rsi
    3c8c:	75 e1                	jne    3c6f <timer_thread+0x17f>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c8e:	48 83 c7 08          	add    $0x8,%rdi
    3c92:	48 39 f9             	cmp    %rdi,%rcx
    3c95:	75 b2                	jne    3c49 <timer_thread+0x159>
  asm volatile ("mfence" ::: "memory");
    3c97:	0f ae f0             	mfence
  struct timespec drain = {
    3c9a:	66 0f 6f 05 9e 3c 00 00 	movdqa 0x3c9e(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3ca2:	4c 8d 25 b4 33 00 00 	lea    0x33b4(%rip),%r12        # 705d <_IO_stdin_used+0x5d>
    3ca9:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
    y++;
    3cad:	8b 9d 7c ff ff ff    	mov    -0x84(%rbp),%ebx
    for (int x = 0 ; x < data->thread_count ; x++) {
    3cb3:	49 63 45 18          	movslq 0x18(%r13),%rax
    y++;
    3cb7:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3cba:	85 c0                	test   %eax,%eax
    3cbc:	7e 4e                	jle    3d0c <timer_thread+0x21c>
        data->threads[x]->tasks[y].scheduled = 0;
    3cbe:	4c 63 85 7c ff ff ff 	movslq -0x84(%rbp),%r8
    3cc5:	49 8b 4d 10          	mov    0x10(%r13),%rcx
    3cc9:	49 c1 e0 09          	shl    $0x9,%r8
    3ccd:	4c 8d 14 c1          	lea    (%rcx,%rax,8),%r10
    3cd1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3cd8:	48 8b 19             	mov    (%rcx),%rbx
    3cdb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3cdd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3ce1:	99                   	cltd
    3ce2:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3ce5:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3ce9:	48 63 d2             	movslq %edx,%rdx
    3cec:	48 c1 e2 09          	shl    $0x9,%rdx
    3cf0:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3cfb:	42 c7 84 06 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d07:	4c 39 d1             	cmp    %r10,%rcx
    3d0a:	75 cc                	jne    3cd8 <timer_thread+0x1e8>
    asm volatile ("mfence" ::: "memory");
    3d0c:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3d0f:	49 8b 45 10          	mov    0x10(%r13),%rax
    3d13:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3d16:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3d19:	ba 00 00 00 00       	mov    $0x0,%edx
    3d1e:	0f 4f d7             	cmovg  %edi,%edx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3d21:	41 8b 7d 20          	mov    0x20(%r13),%edi
    y++;
    3d25:	89 95 7c ff ff ff    	mov    %edx,-0x84(%rbp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3d2b:	85 ff                	test   %edi,%edi
    3d2d:	0f 8e bb 00 00 00    	jle    3dee <timer_thread+0x2fe>
    3d33:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    3d36:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    3d3c:	0f 1f 40 00          	nopl   0x0(%rax)
    3d40:	4a 8d 1c f5 00 00 00 00 	lea    0x0(,%r14,8),%rbx
            all_empty = 0;
    3d48:	45 31 ff             	xor    %r15d,%r15d
    3d4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3d50:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3d54:	4c 89 f8             	mov    %r15,%rax
    3d57:	48 c1 e0 09          	shl    $0x9,%rax
    3d5b:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3d5f:	31 d2                	xor    %edx,%edx
    3d61:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3d68:	eb 16                	jmp    3d80 <timer_thread+0x290>
    3d6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3d70:	4d 85 c0             	test   %r8,%r8
    3d73:	7f 1f                	jg     3d94 <timer_thread+0x2a4>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3d75:	83 c2 01             	add    $0x1,%edx
    3d78:	48 83 c0 20          	add    $0x20,%rax
    3d7c:	39 fa                	cmp    %edi,%edx
    3d7e:	74 2a                	je     3daa <timer_thread+0x2ba>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3d80:	48 8b 08             	mov    (%rax),%rcx
    3d83:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3d87:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3d8b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3d8f:	48 85 c9             	test   %rcx,%rcx
    3d92:	7e dc                	jle    3d70 <timer_thread+0x280>
    3d94:	bf 01 00 00 00       	mov    $0x1,%edi
    3d99:	4c 89 e6             	mov    %r12,%rsi
    3d9c:	31 c0                	xor    %eax,%eax
    3d9e:	e8 dd e6 ff ff       	call   2480 <__printf_chk@plt>
            break;
    3da3:	41 8b 7d 20          	mov    0x20(%r13),%edi
            all_empty = 0;
    3da7:	45 31 d2             	xor    %r10d,%r10d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3daa:	49 83 c7 01          	add    $0x1,%r15
    3dae:	44 39 ff             	cmp    %r15d,%edi
    3db1:	7e 0d                	jle    3dc0 <timer_thread+0x2d0>
    3db3:	49 8b 45 10          	mov    0x10(%r13),%rax
    3db7:	eb 97                	jmp    3d50 <timer_thread+0x260>
    3db9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3dc0:	49 83 c6 01          	add    $0x1,%r14
    3dc4:	44 39 f7             	cmp    %r14d,%edi
    3dc7:	7e 0d                	jle    3dd6 <timer_thread+0x2e6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3dc9:	85 ff                	test   %edi,%edi
    3dcb:	7e 09                	jle    3dd6 <timer_thread+0x2e6>
    3dcd:	49 8b 45 10          	mov    0x10(%r13),%rax
    3dd1:	e9 6a ff ff ff       	jmp    3d40 <timer_thread+0x250>
    if (all_empty == 1) {
    3dd6:	41 83 fa 01          	cmp    $0x1,%r10d
    3dda:	74 12                	je     3dee <timer_thread+0x2fe>
      nanosleep(&drain , &drainrem);
    3ddc:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    3de0:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
    3de4:	e8 87 e5 ff ff       	call   2370 <nanosleep@plt>
    3de9:	e9 bf fe ff ff       	jmp    3cad <timer_thread+0x1bd>
    3dee:	48 8d 3d 5f 32 00 00 	lea    0x325f(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3df5:	e8 16 e5 ff ff       	call   2310 <puts@plt>
  while (data->running) {
    3dfa:	41 8b 45 34          	mov    0x34(%r13),%eax
    3dfe:	85 c0                	test   %eax,%eax
    3e00:	0f 84 d1 00 00 00    	je     3ed7 <timer_thread+0x3e7>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3e06:	41 8b 4d 1c          	mov    0x1c(%r13),%ecx
    3e0a:	85 c9                	test   %ecx,%ecx
    3e0c:	7e 2f                	jle    3e3d <timer_thread+0x34d>
    3e0e:	49 8b 45 10          	mov    0x10(%r13),%rax
    3e12:	31 db                	xor    %ebx,%ebx
    3e14:	4c 8d 25 53 32 00 00 	lea    0x3253(%rip),%r12        # 706e <_IO_stdin_used+0x6e>
    3e1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->threads[x]->running = 0;
    3e20:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3e24:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3e28:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3e2f:	0f 84 ce 00 00 00    	je     3f03 <timer_thread+0x413>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3e35:	48 83 c3 01          	add    $0x1,%rbx
    3e39:	39 d9                	cmp    %ebx,%ecx
    3e3b:	7f e3                	jg     3e20 <timer_thread+0x330>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3e3d:	49 63 55 18          	movslq 0x18(%r13),%rdx
    3e41:	85 d2                	test   %edx,%edx
    3e43:	7e 7b                	jle    3ec0 <timer_thread+0x3d0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3e45:	49 63 45 30          	movslq 0x30(%r13),%rax
    3e49:	85 c0                	test   %eax,%eax
    3e4b:	7e 73                	jle    3ec0 <timer_thread+0x3d0>
    3e4d:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3e51:	4d 8b 45 10          	mov    0x10(%r13),%r8
    3e55:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3e5d:	31 c9                	xor    %ecx,%ecx
    3e5f:	48 89 c6             	mov    %rax,%rsi
    3e62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3e68:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3e6c:	48 8b 40 28          	mov    0x28(%rax),%rax
    3e70:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3e74:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3e7a:	74 1c                	je     3e98 <timer_thread+0x3a8>
    3e7c:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3e86:	48 05 00 02 00 00    	add    $0x200,%rax
    3e8c:	48 39 d0             	cmp    %rdx,%rax
    3e8f:	74 26                	je     3eb7 <timer_thread+0x3c7>
    3e91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3e98:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3ea2:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3ea8:	c7 80 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3eb2:	48 39 d0             	cmp    %rdx,%rax
    3eb5:	75 e1                	jne    3e98 <timer_thread+0x3a8>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3eb7:	48 83 c1 08          	add    $0x8,%rcx
    3ebb:	48 39 f9             	cmp    %rdi,%rcx
    3ebe:	75 a8                	jne    3e68 <timer_thread+0x378>
    asm volatile ("mfence" ::: "memory");
    3ec0:	0f ae f0             	mfence
    3ec3:	48 8d 3d b6 31 00 00 	lea    0x31b6(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3eca:	e8 41 e4 ff ff       	call   2310 <puts@plt>
    data->running = 0;
    3ecf:	41 c7 45 34 00 00 00 00 	movl   $0x0,0x34(%r13)
    3ed7:	48 8d 3d a9 31 00 00 	lea    0x31a9(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3ede:	e8 2d e4 ff ff       	call   2310 <puts@plt>
}
    3ee3:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    3ee7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3ef0:	75 47                	jne    3f39 <timer_thread+0x449>
    3ef2:	48 83 c4 68          	add    $0x68,%rsp
    3ef6:	31 c0                	xor    %eax,%eax
    3ef8:	5b                   	pop    %rbx
    3ef9:	41 5c                	pop    %r12
    3efb:	41 5d                	pop    %r13
    3efd:	41 5e                	pop    %r14
    3eff:	41 5f                	pop    %r15
    3f01:	5d                   	pop    %rbp
    3f02:	c3                   	ret
    3f03:	4c 89 e7             	mov    %r12,%rdi
    3f06:	e8 05 e4 ff ff       	call   2310 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3f0b:	49 8b 45 10          	mov    0x10(%r13),%rax
    3f0f:	be 01 00 00 00       	mov    $0x1,%esi
    3f14:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3f18:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3f1c:	8b 78 50             	mov    0x50(%rax),%edi
    3f1f:	e8 0c e5 ff ff       	call   2430 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3f24:	41 8b 4d 1c          	mov    0x1c(%r13),%ecx
    3f28:	39 d9                	cmp    %ebx,%ecx
    3f2a:	0f 8e 0d ff ff ff    	jle    3e3d <timer_thread+0x34d>
    3f30:	49 8b 45 10          	mov    0x10(%r13),%rax
    3f34:	e9 e7 fe ff ff       	jmp    3e20 <timer_thread+0x330>
}
    3f39:	e8 12 e4 ff ff       	call   2350 <__stack_chk_fail@plt>
    3f3e:	66 90                	xchg   %ax,%ax

0000000000003f40 <strtolower>:
void strtolower(char *str) {
    3f40:	f3 0f 1e fa          	endbr64
    3f44:	55                   	push   %rbp
    3f45:	48 89 e5             	mov    %rsp,%rbp
    3f48:	41 54                	push   %r12
    3f4a:	53                   	push   %rbx
    3f4b:	ff 15 97 60 00 00    	call   *0x6097(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    for (; *str; ++str)
    3f51:	48 0f be 1f          	movsbq (%rdi),%rbx
void strtolower(char *str) {
    3f55:	49 89 fc             	mov    %rdi,%r12
    for (; *str; ++str)
    3f58:	84 db                	test   %bl,%bl
    3f5a:	74 24                	je     3f80 <strtolower+0x40>
        *str = (char)tolower(*str);
    3f5c:	e8 ef e5 ff ff       	call   2550 <__ctype_tolower_loc@plt>
    3f61:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3f68:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3f6b:	49 83 c4 01          	add    $0x1,%r12
        *str = (char)tolower(*str);
    3f6f:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3f72:	41 88 54 24 ff       	mov    %dl,-0x1(%r12)
    for (; *str; ++str)
    3f77:	49 0f be 1c 24       	movsbq (%r12),%rbx
    3f7c:	84 db                	test   %bl,%bl
    3f7e:	75 e8                	jne    3f68 <strtolower+0x28>
}
    3f80:	5b                   	pop    %rbx
    3f81:	41 5c                	pop    %r12
    3f83:	5d                   	pop    %rbp
    3f84:	c3                   	ret
    3f85:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003f90 <zh_malloc>:
void *zh_malloc(size_t size) {
    3f90:	f3 0f 1e fa          	endbr64
    3f94:	55                   	push   %rbp
    3f95:	48 89 e5             	mov    %rsp,%rbp
    3f98:	ff 15 4a 60 00 00    	call   *0x604a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    void *buf = malloc(size);
    3f9e:	e8 9d e4 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    3fa3:	48 85 c0             	test   %rax,%rax
    3fa6:	74 02                	je     3faa <zh_malloc+0x1a>
}
    3fa8:	5d                   	pop    %rbp
    3fa9:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3faa:	48 8b 0d 6f 60 00 00 	mov    0x606f(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    3fb1:	ba 28 00 00 00       	mov    $0x28,%edx
    3fb6:	be 01 00 00 00       	mov    $0x1,%esi
    3fbb:	48 8d 3d 36 34 00 00 	lea    0x3436(%rip),%rdi        # 73f8 <_IO_stdin_used+0x3f8>
    3fc2:	e8 39 e5 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    3fc7:	bf 01 00 00 00       	mov    $0x1,%edi
    3fcc:	e8 0f e5 ff ff       	call   24e0 <exit@plt>
    3fd1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3fdc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003fe0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3fe0:	f3 0f 1e fa          	endbr64
    3fe4:	55                   	push   %rbp
    3fe5:	48 89 e5             	mov    %rsp,%rbp
    3fe8:	53                   	push   %rbx
    3fe9:	48 83 ec 08          	sub    $0x8,%rsp
    3fed:	ff 15 f5 5f 00 00    	call   *0x5ff5(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    const char *dot = strrchr(filename, '.');
    3ff3:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3ff8:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3ffb:	e8 80 e3 ff ff       	call   2380 <strrchr@plt>
    if (!dot || dot == filename)
    4000:	48 85 c0             	test   %rax,%rax
    4003:	74 13                	je     4018 <get_filename_ext+0x38>
    4005:	48 39 c3             	cmp    %rax,%rbx
    4008:	74 0e                	je     4018 <get_filename_ext+0x38>
}
    400a:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    return dot + 1;
    400e:	48 83 c0 01          	add    $0x1,%rax
}
    4012:	c9                   	leave
    4013:	c3                   	ret
    4014:	0f 1f 40 00          	nopl   0x0(%rax)
    4018:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
        return "";
    401c:	48 8d 05 ac 30 00 00 	lea    0x30ac(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    4023:	c9                   	leave
    4024:	c3                   	ret
    4025:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004030 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4030:	f3 0f 1e fa          	endbr64
    4034:	55                   	push   %rbp
    4035:	48 89 e5             	mov    %rsp,%rbp
    4038:	41 56                	push   %r14
    403a:	41 55                	push   %r13
    403c:	41 54                	push   %r12
    403e:	53                   	push   %rbx
    403f:	48 81 ec 10 08 00 00 	sub    $0x810,%rsp
    4046:	ff 15 9c 5f 00 00    	call   *0x5f9c(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    404c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4055:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    4059:	31 c0                	xor    %eax,%eax
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    405b:	4c 8d ad d0 f7 ff ff 	lea    -0x830(%rbp),%r13
    4062:	49 89 f6             	mov    %rsi,%r14
    4065:	49 89 d4             	mov    %rdx,%r12
    4068:	48 89 fe             	mov    %rdi,%rsi
    406b:	ba 00 04 00 00       	mov    $0x400,%edx
    4070:	4c 89 ef             	mov    %r13,%rdi
    4073:	e8 e8 e3 ff ff       	call   2460 <__strcpy_chk@plt>
    for (; *str; ++str)
    4078:	48 0f be 9d d0 f7 ff ff 	movsbq -0x830(%rbp),%rbx
    4080:	84 db                	test   %bl,%bl
    4082:	74 1e                	je     40a2 <send_headers+0x72>
        *str = (char)tolower(*str);
    4084:	e8 c7 e4 ff ff       	call   2550 <__ctype_tolower_loc@plt>
    4089:	48 8b 08             	mov    (%rax),%rcx
    408c:	4c 89 e8             	mov    %r13,%rax
    408f:	90                   	nop
    4090:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4093:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4097:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    409a:	48 0f be 18          	movsbq (%rax),%rbx
    409e:	84 db                	test   %bl,%bl
    40a0:	75 ee                	jne    4090 <send_headers+0x60>
    void *buf = malloc(size);
    40a2:	bf 11 00 00 00       	mov    $0x11,%edi
    40a7:	e8 94 e3 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    40ac:	48 85 c0             	test   %rax,%rax
    40af:	0f 84 72 04 00 00    	je     4527 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    40b5:	66 0f 6f 05 93 38 00 00 	movdqa 0x3893(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    iov[0].iov_base = zh_malloc(slen);
    40bd:	49 89 04 24          	mov    %rax,(%r12)
    void *buf = malloc(size);
    40c1:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    40c6:	49 c7 44 24 08 11 00 00 00 	movq   $0x11,0x8(%r12)
    40cf:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    40d3:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    40d6:	e8 65 e3 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    40db:	48 85 c0             	test   %rax,%rax
    40de:	0f 84 43 04 00 00    	je     4527 <send_headers+0x4f7>
    40e4:	66 0f 6f 05 74 38 00 00 	movdqa 0x3874(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[1].iov_base = zh_malloc(slen);
    40ec:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    const char *dot = strrchr(filename, '.');
    40f1:	4c 89 ef             	mov    %r13,%rdi
    40f4:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    40fe:	49 c7 44 24 18 17 00 00 00 	movq   $0x17,0x18(%r12)
    4107:	0f 11 00             	movups %xmm0,(%rax)
    410a:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    410e:	be 2e 00 00 00       	mov    $0x2e,%esi
    4113:	e8 68 e2 ff ff       	call   2380 <strrchr@plt>
    if (!dot || dot == filename)
    4118:	48 85 c0             	test   %rax,%rax
    411b:	0f 84 df 02 00 00    	je     4400 <send_headers+0x3d0>
    4121:	4c 39 e8             	cmp    %r13,%rax
    4124:	0f 84 d6 02 00 00    	je     4400 <send_headers+0x3d0>
    return dot + 1;
    412a:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    412e:	48 8d 3d 68 2f 00 00 	lea    0x2f68(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    4135:	48 89 de             	mov    %rbx,%rsi
    4138:	e8 93 e2 ff ff       	call   23d0 <strcmp@plt>
    413d:	85 c0                	test   %eax,%eax
    413f:	75 1e                	jne    415f <send_headers+0x12f>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4141:	66 0f 6f 05 27 38 00 00 	movdqa 0x3827(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    4149:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4150:	66 0f 6f 05 28 38 00 00 	movdqa 0x3828(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4158:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("jpeg", file_ext) == 0)
    415f:	48 89 de             	mov    %rbx,%rsi
    4162:	48 8d 3d 38 2f 00 00 	lea    0x2f38(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    4169:	e8 62 e2 ff ff       	call   23d0 <strcmp@plt>
    416e:	85 c0                	test   %eax,%eax
    4170:	75 1e                	jne    4190 <send_headers+0x160>
    4172:	66 0f 6f 05 f6 37 00 00 	movdqa 0x37f6(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    417a:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4181:	66 0f 6f 05 f7 37 00 00 	movdqa 0x37f7(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4189:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("png", file_ext) == 0)
    4190:	48 89 de             	mov    %rbx,%rsi
    4193:	48 8d 3d 0c 2f 00 00 	lea    0x2f0c(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    419a:	e8 31 e2 ff ff       	call   23d0 <strcmp@plt>
    419f:	85 c0                	test   %eax,%eax
    41a1:	0f 84 09 02 00 00    	je     43b0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    41a7:	48 89 de             	mov    %rbx,%rsi
    41aa:	48 8d 3d f9 2e 00 00 	lea    0x2ef9(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    41b1:	e8 1a e2 ff ff       	call   23d0 <strcmp@plt>
    41b6:	85 c0                	test   %eax,%eax
    41b8:	0f 84 a2 02 00 00    	je     4460 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    41be:	48 89 de             	mov    %rbx,%rsi
    41c1:	48 8d 3d e6 2e 00 00 	lea    0x2ee6(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    41c8:	e8 03 e2 ff ff       	call   23d0 <strcmp@plt>
    41cd:	85 c0                	test   %eax,%eax
    41cf:	0f 84 63 02 00 00    	je     4438 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    41d5:	48 89 de             	mov    %rbx,%rsi
    41d8:	48 8d 3d 12 2f 00 00 	lea    0x2f12(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    41df:	e8 ec e1 ff ff       	call   23d0 <strcmp@plt>
    41e4:	85 c0                	test   %eax,%eax
    41e6:	0f 84 24 02 00 00    	je     4410 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    41ec:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    41ef:	0f 84 53 01 00 00    	je     4348 <send_headers+0x318>
    if (strcmp("css", file_ext) == 0)
    41f5:	48 89 de             	mov    %rbx,%rsi
    41f8:	48 8d 3d b3 2e 00 00 	lea    0x2eb3(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    41ff:	e8 cc e1 ff ff       	call   23d0 <strcmp@plt>
    4204:	85 c0                	test   %eax,%eax
    4206:	0f 84 a4 02 00 00    	je     44b0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    420c:	48 89 de             	mov    %rbx,%rsi
    420f:	48 8d 3d a0 2e 00 00 	lea    0x2ea0(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    4216:	e8 b5 e1 ff ff       	call   23d0 <strcmp@plt>
    421b:	85 c0                	test   %eax,%eax
    421d:	0f 84 65 02 00 00    	je     4488 <send_headers+0x458>
    slen = strlen(send_buffer);
    4223:	4c 8d ad d0 fb ff ff 	lea    -0x430(%rbp),%r13
    422a:	4c 89 ef             	mov    %r13,%rdi
    422d:	e8 0e e1 ff ff       	call   2340 <strlen@plt>
    void *buf = malloc(size);
    4232:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4235:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4238:	e8 03 e2 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    423d:	48 85 c0             	test   %rax,%rax
    4240:	0f 84 e1 02 00 00    	je     4527 <send_headers+0x4f7>
    iov[2].iov_base = zh_malloc(slen);
    4246:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    iov[2].iov_len = slen;
    424b:	49 89 5c 24 28       	mov    %rbx,0x28(%r12)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4250:	83 fb 08             	cmp    $0x8,%ebx
    4253:	0f 83 37 01 00 00    	jae    4390 <send_headers+0x360>
    4259:	f6 c3 04             	test   $0x4,%bl
    425c:	0f 85 71 02 00 00    	jne    44d3 <send_headers+0x4a3>
    4262:	85 db                	test   %ebx,%ebx
    4264:	74 12                	je     4278 <send_headers+0x248>
    4266:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    426d:	88 10                	mov    %dl,(%rax)
    426f:	f6 c3 02             	test   $0x2,%bl
    4272:	0f 85 8b 02 00 00    	jne    4503 <send_headers+0x4d3>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4278:	4d 89 f0             	mov    %r14,%r8
    427b:	48 8d 0d 38 2e 00 00 	lea    0x2e38(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    4282:	4c 89 ef             	mov    %r13,%rdi
    4285:	31 c0                	xor    %eax,%eax
    4287:	ba 00 04 00 00       	mov    $0x400,%edx
    428c:	be 01 00 00 00       	mov    $0x1,%esi
    4291:	e8 ca e2 ff ff       	call   2560 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4296:	4c 89 ef             	mov    %r13,%rdi
    4299:	e8 a2 e0 ff ff       	call   2340 <strlen@plt>
    void *buf = malloc(size);
    429e:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    42a1:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    42a4:	e8 97 e1 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    42a9:	48 85 c0             	test   %rax,%rax
    42ac:	0f 84 75 02 00 00    	je     4527 <send_headers+0x4f7>
    iov[3].iov_base = zh_malloc(slen);
    42b2:	49 89 44 24 30       	mov    %rax,0x30(%r12)
    iov[3].iov_len = slen;
    42b7:	49 89 5c 24 38       	mov    %rbx,0x38(%r12)
    42bc:	83 fb 08             	cmp    $0x8,%ebx
    42bf:	0f 83 13 01 00 00    	jae    43d8 <send_headers+0x3a8>
    42c5:	f6 c3 04             	test   $0x4,%bl
    42c8:	0f 85 1d 02 00 00    	jne    44eb <send_headers+0x4bb>
    42ce:	85 db                	test   %ebx,%ebx
    42d0:	74 12                	je     42e4 <send_headers+0x2b4>
    42d2:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    42d9:	88 10                	mov    %dl,(%rax)
    42db:	f6 c3 02             	test   $0x2,%bl
    42de:	0f 85 31 02 00 00    	jne    4515 <send_headers+0x4e5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    42e4:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    42e9:	bf 02 00 00 00       	mov    $0x2,%edi
    42ee:	c6 85 d2 fb ff ff 00 	movb   $0x0,-0x42e(%rbp)
    42f5:	66 89 85 d0 fb ff ff 	mov    %ax,-0x430(%rbp)
    42fc:	e8 3f e1 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    4301:	48 85 c0             	test   %rax,%rax
    4304:	0f 84 1d 02 00 00    	je     4527 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    430a:	0f b7 95 d0 fb ff ff 	movzwl -0x430(%rbp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4311:	49 89 44 24 40       	mov    %rax,0x40(%r12)
    iov[4].iov_len = slen;
    4316:	49 c7 44 24 48 02 00 00 00 	movq   $0x2,0x48(%r12)
    431f:	66 89 10             	mov    %dx,(%rax)
}
    4322:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    4326:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    432f:	0f 85 19 02 00 00    	jne    454e <send_headers+0x51e>
    4335:	48 81 c4 10 08 00 00 	add    $0x810,%rsp
    433c:	5b                   	pop    %rbx
    433d:	41 5c                	pop    %r12
    433f:	41 5d                	pop    %r13
    4341:	41 5e                	pop    %r14
    4343:	5d                   	pop    %rbp
    4344:	c3                   	ret
    4345:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
    4348:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    434c:	0f 85 a3 fe ff ff    	jne    41f5 <send_headers+0x1c5>
    4352:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4356:	0f 85 99 fe ff ff    	jne    41f5 <send_headers+0x1c5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    435c:	66 0f 6f 05 6c 36 00 00 	movdqa 0x366c(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4364:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    436e:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4375:	66 0f 6f 05 63 36 00 00 	movdqa 0x3663(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    437d:	0f 29 85 e0 fb ff ff 	movaps %xmm0,-0x420(%rbp)
    4384:	48 89 85 ef fb ff ff 	mov    %rax,-0x411(%rbp)
    438b:	e9 65 fe ff ff       	jmp    41f5 <send_headers+0x1c5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4390:	89 da                	mov    %ebx,%edx
    4392:	48 89 c7             	mov    %rax,%rdi
    4395:	4c 89 ee             	mov    %r13,%rsi
    4398:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    439d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    43a2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    43a5:	c1 e9 03             	shr    $0x3,%ecx
    43a8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    43ab:	e9 c8 fe ff ff       	jmp    4278 <send_headers+0x248>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    43b0:	66 0f 6f 05 b8 35 00 00 	movdqa 0x35b8(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    43b8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    43bf:	66 0f 6f 05 c9 35 00 00 	movdqa 0x35c9(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    43c7:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    43ce:	e9 d4 fd ff ff       	jmp    41a7 <send_headers+0x177>
    43d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    43d8:	89 da                	mov    %ebx,%edx
    43da:	48 89 c7             	mov    %rax,%rdi
    43dd:	4c 89 ee             	mov    %r13,%rsi
    43e0:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    43e5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    43ea:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    43ed:	c1 e9 03             	shr    $0x3,%ecx
    43f0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    43f3:	e9 ec fe ff ff       	jmp    42e4 <send_headers+0x2b4>
    43f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4400:	48 8d 1d c8 2c 00 00 	lea    0x2cc8(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4407:	e9 9b fd ff ff       	jmp    41a7 <send_headers+0x177>
    440c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4410:	66 0f 6f 05 98 35 00 00 	movdqa 0x3598(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    4418:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    441f:	66 0f 6f 05 99 35 00 00 	movdqa 0x3599(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4427:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    442e:	e9 b9 fd ff ff       	jmp    41ec <send_headers+0x1bc>
    4433:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4438:	66 0f 6f 05 70 35 00 00 	movdqa 0x3570(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    4440:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4447:	66 0f 6f 05 71 35 00 00 	movdqa 0x3571(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    444f:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    4456:	e9 7a fd ff ff       	jmp    41d5 <send_headers+0x1a5>
    445b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4460:	66 0f 6f 05 08 35 00 00 	movdqa 0x3508(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    4468:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    446f:	66 0f 6f 05 29 35 00 00 	movdqa 0x3529(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4477:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    447e:	e9 3b fd ff ff       	jmp    41be <send_headers+0x18e>
    4483:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4488:	66 0f 6f 05 20 35 00 00 	movdqa 0x3520(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    4490:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4497:	66 0f 6f 05 61 35 00 00 	movdqa 0x3561(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    449f:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    44a6:	e9 78 fd ff ff       	jmp    4223 <send_headers+0x1f3>
    44ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    44b0:	66 0f 6f 05 f8 34 00 00 	movdqa 0x34f8(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    44b8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    44bf:	66 0f 6f 05 29 35 00 00 	movdqa 0x3529(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    44c7:	0f 11 85 d9 fb ff ff 	movups %xmm0,-0x427(%rbp)
    44ce:	e9 39 fd ff ff       	jmp    420c <send_headers+0x1dc>
  return __builtin___memcpy_chk (__dest, __src, __len,
    44d3:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    44d9:	89 db                	mov    %ebx,%ebx
    44db:	89 10                	mov    %edx,(%rax)
    44dd:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    44e2:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    44e6:	e9 8d fd ff ff       	jmp    4278 <send_headers+0x248>
    44eb:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    44f1:	89 db                	mov    %ebx,%ebx
    44f3:	89 10                	mov    %edx,(%rax)
    44f5:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    44fa:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    44fe:	e9 e1 fd ff ff       	jmp    42e4 <send_headers+0x2b4>
    4503:	89 db                	mov    %ebx,%ebx
    4505:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    450b:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4510:	e9 63 fd ff ff       	jmp    4278 <send_headers+0x248>
    4515:	89 db                	mov    %ebx,%ebx
    4517:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    451d:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4522:	e9 bd fd ff ff       	jmp    42e4 <send_headers+0x2b4>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4527:	48 8b 0d f2 5a 00 00 	mov    0x5af2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    452e:	ba 28 00 00 00       	mov    $0x28,%edx
    4533:	be 01 00 00 00       	mov    $0x1,%esi
    4538:	48 8d 3d b9 2e 00 00 	lea    0x2eb9(%rip),%rdi        # 73f8 <_IO_stdin_used+0x3f8>
    453f:	e8 bc df ff ff       	call   2500 <fwrite@plt>
        exit(1);
    4544:	bf 01 00 00 00       	mov    $0x1,%edi
    4549:	e8 92 df ff ff       	call   24e0 <exit@plt>
}
    454e:	e8 fd dd ff ff       	call   2350 <__stack_chk_fail@plt>
    4553:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    455e:	66 90                	xchg   %ax,%ax

0000000000004560 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4560:	f3 0f 1e fa          	endbr64
    4564:	55                   	push   %rbp
    4565:	48 89 e5             	mov    %rsp,%rbp
    4568:	41 56                	push   %r14
    456a:	41 55                	push   %r13
    456c:	41 54                	push   %r12
    456e:	53                   	push   %rbx
    456f:	ff 15 73 5a 00 00    	call   *0x5a73(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    4575:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    4578:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    457b:	48 89 f3             	mov    %rsi,%rbx
    457e:	49 89 d6             	mov    %rdx,%r14
    void *buf = malloc(size);
    4581:	e8 ba de ff ff       	call   2440 <malloc@plt>
    4586:	49 89 c4             	mov    %rax,%r12
    if (!buf) {
    4589:	48 85 c0             	test   %rax,%rax
    458c:	74 69                	je     45f7 <copy_file_contents+0x97>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    458e:	4c 89 ef             	mov    %r13,%rdi
    4591:	31 f6                	xor    %esi,%esi
    4593:	31 c0                	xor    %eax,%eax
    4595:	e8 16 df ff ff       	call   24b0 <open@plt>
    459a:	41 89 c5             	mov    %eax,%r13d
    if (fd < 0)
    459d:	85 c0                	test   %eax,%eax
    459f:	0f 88 f8 df ff ff    	js     259d <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    45a5:	48 89 da             	mov    %rbx,%rdx
    45a8:	4c 89 e6             	mov    %r12,%rsi
    45ab:	89 c7                	mov    %eax,%edi
    45ad:	e8 fe dd ff ff       	call   23b0 <read@plt>
    if (ret < file_size) {
    45b2:	48 98                	cltq
    45b4:	48 39 d8             	cmp    %rbx,%rax
    45b7:	7c 1f                	jl     45d8 <copy_file_contents+0x78>
    close(fd);
    45b9:	44 89 ef             	mov    %r13d,%edi
    45bc:	e8 cf dd ff ff       	call   2390 <close@plt>
    iov->iov_base = buf;
    45c1:	4d 89 26             	mov    %r12,(%r14)
    iov->iov_len = file_size;
    45c4:	49 89 5e 08          	mov    %rbx,0x8(%r14)
}
    45c8:	5b                   	pop    %rbx
    45c9:	41 5c                	pop    %r12
    45cb:	41 5d                	pop    %r13
    45cd:	41 5e                	pop    %r14
    45cf:	5d                   	pop    %rbp
    45d0:	c3                   	ret
    45d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    45d8:	48 8b 0d 41 5a 00 00 	mov    0x5a41(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    45df:	ba 1a 00 00 00       	mov    $0x1a,%edx
    45e4:	be 01 00 00 00       	mov    $0x1,%esi
    45e9:	48 8d 3d e0 2a 00 00 	lea    0x2ae0(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    45f0:	e8 0b df ff ff       	call   2500 <fwrite@plt>
    45f5:	eb c2                	jmp    45b9 <copy_file_contents+0x59>
    45f7:	48 8b 0d 22 5a 00 00 	mov    0x5a22(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    45fe:	ba 28 00 00 00       	mov    $0x28,%edx
    4603:	be 01 00 00 00       	mov    $0x1,%esi
    4608:	48 8d 3d e9 2d 00 00 	lea    0x2de9(%rip),%rdi        # 73f8 <_IO_stdin_used+0x3f8>
    460f:	e8 ec de ff ff       	call   2500 <fwrite@plt>
        exit(1);
    4614:	bf 01 00 00 00       	mov    $0x1,%edi
    4619:	e8 c2 de ff ff       	call   24e0 <exit@plt>
    461e:	66 90                	xchg   %ax,%ax

0000000000004620 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4620:	f3 0f 1e fa          	endbr64
    4624:	55                   	push   %rbp
    4625:	48 89 e5             	mov    %rsp,%rbp
    4628:	ff 15 ba 59 00 00    	call   *0x59ba(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    462e:	8b 46 44             	mov    0x44(%rsi),%eax
    4631:	48 89 fa             	mov    %rdi,%rdx
    4634:	48 89 f7             	mov    %rsi,%rdi
    4637:	8d 70 01             	lea    0x1(%rax),%esi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    463a:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4640:	48 8b 07             	mov    (%rdi),%rax
    4643:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4646:	f6 c1 02             	test   $0x2,%cl
    4649:	74 00                	je     464b <add_write_request+0x2b>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    464b:	89 f0                	mov    %esi,%eax
    464d:	44 29 c0             	sub    %r8d,%eax
    4650:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4653:	0f 82 50 df ff ff    	jb     25a9 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4659:	c1 e9 0a             	shr    $0xa,%ecx
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    465c:	8b 47 44             	mov    0x44(%rdi),%eax
    465f:	23 47 58             	and    0x58(%rdi),%eax
		sq->sqe_tail = next;
    4662:	89 77 44             	mov    %esi,0x44(%rdi)
	if (ring->flags & IORING_SETUP_SQE128)
    4665:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4668:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    466b:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    466f:	d3 e0                	shl    %cl,%eax
    4671:	8b 4a 04             	mov    0x4(%rdx),%ecx
    4674:	48 c1 e0 06          	shl    $0x6,%rax
    4678:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    467c:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    4682:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4685:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4689:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    468f:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4697:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    469b:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    469e:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    46a5:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    46ad:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    46b1:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    46b5:	e8 a6 dc ff ff       	call   2360 <io_uring_submit@plt>
}
    46ba:	31 c0                	xor    %eax,%eax
    46bc:	5d                   	pop    %rbp
    46bd:	c3                   	ret
    46be:	66 90                	xchg   %ax,%ax

00000000000046c0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    46c0:	f3 0f 1e fa          	endbr64
    46c4:	55                   	push   %rbp
    46c5:	48 89 e5             	mov    %rsp,%rbp
    46c8:	41 56                	push   %r14
    46ca:	41 55                	push   %r13
    46cc:	41 54                	push   %r12
    46ce:	53                   	push   %rbx
    46cf:	ff 15 13 59 00 00    	call   *0x5913(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    46d5:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    46d8:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    46de:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    46e1:	83 c0 01             	add    $0x1,%eax
    46e4:	48 89 f3             	mov    %rsi,%rbx
    46e7:	41 89 fe             	mov    %edi,%r14d
		head = IO_URING_READ_ONCE(*sq->khead);
    46ea:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    46ec:	f6 c1 02             	test   $0x2,%cl
    46ef:	74 00                	je     46f1 <add_read_request+0x31>
	if (next - head <= sq->ring_entries) {
    46f1:	89 c2                	mov    %eax,%edx
    46f3:	29 f2                	sub    %esi,%edx
    46f5:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    46f8:	0f 82 bb de ff ff    	jb     25b9 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    46fe:	44 8b 63 44          	mov    0x44(%rbx),%r12d
	if (ring->flags & IORING_SETUP_SQE128)
    4702:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    4705:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4708:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    470d:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4710:	44 23 63 58          	and    0x58(%rbx),%r12d
    4714:	41 d3 e4             	shl    %cl,%r12d
    4717:	49 c1 e4 06          	shl    $0x6,%r12
    471b:	4c 03 63 38          	add    0x38(%rbx),%r12
    471f:	e8 1c dd ff ff       	call   2440 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    4724:	be 01 00 00 00       	mov    $0x1,%esi
    4729:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    472e:	49 89 c5             	mov    %rax,%r13
    req->iov[0].iov_base = malloc(READ_SZ);
    4731:	e8 8a dc ff ff       	call   23c0 <calloc@plt>
    req->client_socket = client_socket;
    4736:	45 89 75 08          	mov    %r14d,0x8(%r13)
	sqe->addr3 = 0;
    473a:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    473e:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4741:	49 89 45 10          	mov    %rax,0x10(%r13)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4745:	49 8d 45 10          	lea    0x10(%r13),%rax
    req->iov[0].iov_len = READ_SZ;
    4749:	49 c7 45 18 00 20 00 00 	movq   $0x2000,0x18(%r13)
    req->event_type = EVENT_TYPE_READ;
    4751:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
	sqe->fd = fd;
    4759:	45 89 74 24 04       	mov    %r14d,0x4(%r12)
	sqe->user_data = (unsigned long) data;
    475e:	4d 89 6c 24 20       	mov    %r13,0x20(%r12)
	sqe->opcode = (__u8) op;
    4763:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->off = offset;
    476b:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4774:	49 89 44 24 10       	mov    %rax,0x10(%r12)
	sqe->len = len;
    4779:	49 c7 44 24 18 01 00 00 00 	movq   $0x1,0x18(%r12)
	sqe->buf_index = 0;
    4782:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->addr3 = 0;
    478b:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    io_uring_submit(ring);
    4791:	e8 ca db ff ff       	call   2360 <io_uring_submit@plt>
}
    4796:	5b                   	pop    %rbx
    4797:	31 c0                	xor    %eax,%eax
    4799:	41 5c                	pop    %r12
    479b:	41 5d                	pop    %r13
    479d:	41 5e                	pop    %r14
    479f:	5d                   	pop    %rbp
    47a0:	c3                   	ret
    47a1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    47ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000047b0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    47b0:	f3 0f 1e fa          	endbr64
    47b4:	55                   	push   %rbp
    47b5:	48 89 e5             	mov    %rsp,%rbp
    47b8:	41 57                	push   %r15
    47ba:	41 56                	push   %r14
    47bc:	41 55                	push   %r13
    47be:	41 54                	push   %r12
    47c0:	53                   	push   %rbx
    47c1:	48 83 ec 08          	sub    $0x8,%rsp
    47c5:	ff 15 1d 58 00 00    	call   *0x581d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    47cb:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    47ce:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    47d3:	41 89 f7             	mov    %esi,%r15d
    47d6:	49 89 d4             	mov    %rdx,%r12
    void *buf = malloc(size);
    47d9:	e8 62 dc ff ff       	call   2440 <malloc@plt>
    47de:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    47e1:	48 85 c0             	test   %rax,%rax
    47e4:	0f 84 eb 00 00 00    	je     48d5 <_send_static_string_content+0x125>
    unsigned long slen = strlen(str);
    47ea:	4c 89 ef             	mov    %r13,%rdi
    47ed:	e8 4e db ff ff       	call   2340 <strlen@plt>
    req->iovec_count = 1;
    47f2:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    47f9:	44 89 7b 08          	mov    %r15d,0x8(%rbx)
    void *buf = malloc(size);
    47fd:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4800:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    4803:	e8 38 dc ff ff       	call   2440 <malloc@plt>
    4808:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    480b:	48 85 c0             	test   %rax,%rax
    480e:	0f 84 c1 00 00 00    	je     48d5 <_send_static_string_content+0x125>
    req->iov[0].iov_base = zh_malloc(slen);
    4814:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4818:	4c 89 f2             	mov    %r14,%rdx
    481b:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    481e:	4c 89 73 18          	mov    %r14,0x18(%rbx)
    4822:	e8 e9 db ff ff       	call   2410 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4827:	41 8b 44 24 44       	mov    0x44(%r12),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    482c:	41 8b 8c 24 c0 00 00 00 	mov    0xc0(%r12),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4834:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4837:	49 8b 04 24          	mov    (%r12),%rax
    483b:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    483d:	f6 c1 02             	test   $0x2,%cl
    4840:	0f 85 8a 00 00 00    	jne    48d0 <_send_static_string_content+0x120>
	if (next - head <= sq->ring_entries) {
    4846:	89 d0                	mov    %edx,%eax
    4848:	29 f0                	sub    %esi,%eax
    484a:	41 39 44 24 5c       	cmp    %eax,0x5c(%r12)
    484f:	0f 82 6e dd ff ff    	jb     25c3 <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4855:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4858:	41 8b 44 24 44       	mov    0x44(%r12),%eax
    485d:	41 23 44 24 58       	and    0x58(%r12),%eax
    io_uring_submit(ring);
    4862:	4c 89 e7             	mov    %r12,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    4865:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4868:	41 89 54 24 44       	mov    %edx,0x44(%r12)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    486d:	8b 53 04             	mov    0x4(%rbx),%edx
	sqe->addr3 = 0;
    4870:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4874:	d3 e0                	shl    %cl,%eax
    4876:	8b 4b 08             	mov    0x8(%rbx),%ecx
    req->event_type = EVENT_TYPE_WRITE;
    4879:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    487f:	48 c1 e0 06          	shl    $0x6,%rax
    4883:	49 03 44 24 38       	add    0x38(%r12),%rax
	sqe->fd = fd;
    4888:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    488b:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    488f:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4895:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    489d:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    48a1:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    48a4:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    48ab:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    48b3:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    48b7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    48bb:	48 83 c4 08          	add    $0x8,%rsp
    48bf:	5b                   	pop    %rbx
    48c0:	41 5c                	pop    %r12
    48c2:	41 5d                	pop    %r13
    48c4:	41 5e                	pop    %r14
    48c6:	41 5f                	pop    %r15
    48c8:	5d                   	pop    %rbp
    io_uring_submit(ring);
    48c9:	e9 92 da ff ff       	jmp    2360 <io_uring_submit@plt>
    48ce:	66 90                	xchg   %ax,%ax
		head = io_uring_smp_load_acquire(sq->khead);
    48d0:	e9 71 ff ff ff       	jmp    4846 <_send_static_string_content+0x96>
    48d5:	48 8b 0d 44 57 00 00 	mov    0x5744(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    48dc:	ba 28 00 00 00       	mov    $0x28,%edx
    48e1:	be 01 00 00 00       	mov    $0x1,%esi
    48e6:	48 8d 3d 0b 2b 00 00 	lea    0x2b0b(%rip),%rdi        # 73f8 <_IO_stdin_used+0x3f8>
    48ed:	e8 0e dc ff ff       	call   2500 <fwrite@plt>
        exit(1);
    48f2:	bf 01 00 00 00       	mov    $0x1,%edi
    48f7:	e8 e4 db ff ff       	call   24e0 <exit@plt>
    48fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004900 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4900:	f3 0f 1e fa          	endbr64
    4904:	55                   	push   %rbp
    4905:	48 89 e5             	mov    %rsp,%rbp
    4908:	ff 15 da 56 00 00    	call   *0x56da(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
}
    490e:	5d                   	pop    %rbp
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    490f:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4912:	89 fe                	mov    %edi,%esi
    4914:	48 8b 3d fd 56 00 00 	mov    0x56fd(%rip),%rdi        # a018 <unimplemented_content>
    491b:	e9 90 fe ff ff       	jmp    47b0 <_send_static_string_content>

0000000000004920 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4920:	f3 0f 1e fa          	endbr64
    4924:	55                   	push   %rbp
    4925:	48 89 e5             	mov    %rsp,%rbp
    4928:	ff 15 ba 56 00 00    	call   *0x56ba(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
}
    492e:	5d                   	pop    %rbp
void handle_http_404(int client_socket, struct io_uring *ring) {
    492f:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4932:	89 fe                	mov    %edi,%esi
    4934:	48 8b 3d d5 56 00 00 	mov    0x56d5(%rip),%rdi        # a010 <http_404_content>
    493b:	e9 70 fe ff ff       	jmp    47b0 <_send_static_string_content>

0000000000004940 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4940:	f3 0f 1e fa          	endbr64
    4944:	55                   	push   %rbp
    4945:	48 89 e5             	mov    %rsp,%rbp
    4948:	41 57                	push   %r15
    494a:	41 56                	push   %r14
    494c:	41 55                	push   %r13
    494e:	41 54                	push   %r12
    4950:	53                   	push   %rbx
    4951:	48 81 ec a8 04 00 00 	sub    $0x4a8,%rsp
    4958:	ff 15 8a 56 00 00    	call   *0x568a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    495e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4967:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    496b:	31 c0                	xor    %eax,%eax
    496d:	49 89 fc             	mov    %rdi,%r12
    4970:	41 89 f5             	mov    %esi,%r13d
    4973:	49 89 d6             	mov    %rdx,%r14
    if (path[strlen(path) - 1] == '/') {
    4976:	e8 c5 d9 ff ff       	call   2340 <strlen@plt>
    497b:	41 80 7c 04 ff 2f    	cmpb   $0x2f,-0x1(%r12,%rax,1)
    4981:	48 89 c3             	mov    %rax,%rbx
    4984:	0f 84 b6 00 00 00    	je     4a40 <handle_get_method+0x100>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    498a:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    498f:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4993:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4998:	4c 89 e6             	mov    %r12,%rsi
    499b:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    49a2:	66 89 85 c4 fb ff ff 	mov    %ax,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    49a9:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    49b0:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    49ba:	e8 31 da ff ff       	call   23f0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    49bf:	48 8d b5 30 fb ff ff 	lea    -0x4d0(%rbp),%rsi
    49c6:	4c 89 ff             	mov    %r15,%rdi
    49c9:	e8 32 da ff ff       	call   2400 <stat@plt>
    49ce:	83 f8 ff             	cmp    $0xffffffff,%eax
    49d1:	0f 84 41 01 00 00    	je     4b18 <handle_get_method+0x1d8>
        if (S_ISREG(path_stat.st_mode)) {
    49d7:	8b 85 48 fb ff ff    	mov    -0x4b8(%rbp),%eax
    49dd:	25 00 f0 00 00       	and    $0xf000,%eax
    49e2:	3d 00 80 00 00       	cmp    $0x8000,%eax
    49e7:	0f 84 b3 00 00 00    	je     4aa0 <handle_get_method+0x160>
    _send_static_string_content(http_404_content, client_socket, ring);
    49ed:	48 8b 3d 1c 56 00 00 	mov    0x561c(%rip),%rdi        # a010 <http_404_content>
    49f4:	4c 89 f2             	mov    %r14,%rdx
    49f7:	44 89 ee             	mov    %r13d,%esi
    49fa:	e8 b1 fd ff ff       	call   47b0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    49ff:	4c 89 fa             	mov    %r15,%rdx
    4a02:	bf 01 00 00 00       	mov    $0x1,%edi
    4a07:	31 c0                	xor    %eax,%eax
    4a09:	48 8d 35 10 27 00 00 	lea    0x2710(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    4a10:	e8 6b da ff ff       	call   2480 <__printf_chk@plt>
}
    4a15:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    4a19:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4a22:	0f 85 20 01 00 00    	jne    4b48 <handle_get_method+0x208>
    4a28:	48 81 c4 a8 04 00 00 	add    $0x4a8,%rsp
    4a2f:	5b                   	pop    %rbx
    4a30:	41 5c                	pop    %r12
    4a32:	41 5d                	pop    %r13
    4a34:	41 5e                	pop    %r14
    4a36:	41 5f                	pop    %r15
    4a38:	5d                   	pop    %rbp
    4a39:	c3                   	ret
    4a3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a40:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a45:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
    4a4c:	4c 89 e6             	mov    %r12,%rsi
    4a4f:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a54:	66 89 95 c4 fb ff ff 	mov    %dx,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a5b:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a5e:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
    4a65:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a6f:	e8 7c d9 ff ff       	call   23f0 <__memcpy_chk@plt>
    4a74:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4a79:	49 8d 7c 1f 06       	lea    0x6(%r15,%rbx,1),%rdi
    4a7e:	ba 0b 00 00 00       	mov    $0xb,%edx
    4a83:	48 29 d9             	sub    %rbx,%rcx
    4a86:	48 8d 35 5e 26 00 00 	lea    0x265e(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4a8d:	e8 5e d9 ff ff       	call   23f0 <__memcpy_chk@plt>
    4a92:	e9 28 ff ff ff       	jmp    49bf <handle_get_method+0x7f>
    4a97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4aa0:	bf 70 00 00 00       	mov    $0x70,%edi
    4aa5:	e8 96 d9 ff ff       	call   2440 <malloc@plt>
    4aaa:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4aad:	48 85 c0             	test   %rax,%rax
    4ab0:	0f 84 97 00 00 00    	je     4b4d <handle_get_method+0x20d>
            req->client_socket = client_socket;
    4ab6:	44 89 68 08          	mov    %r13d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4aba:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    4ac1:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4ac5:	4c 89 ff             	mov    %r15,%rdi
            req->iovec_count = 6;
    4ac8:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4acf:	e8 5c f5 ff ff       	call   4030 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4ad4:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    4adb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4adf:	4c 89 ff             	mov    %r15,%rdi
    4ae2:	e8 79 fa ff ff       	call   4560 <copy_file_contents>
    4ae7:	4c 89 fa             	mov    %r15,%rdx
    4aea:	bf 01 00 00 00       	mov    $0x1,%edi
    4aef:	31 c0                	xor    %eax,%eax
    4af1:	48 8b 8d 60 fb ff ff 	mov    -0x4a0(%rbp),%rcx
    4af8:	48 8d 35 0f 26 00 00 	lea    0x260f(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4aff:	e8 7c d9 ff ff       	call   2480 <__printf_chk@plt>
            add_write_request(req, ring);
    4b04:	4c 89 f6             	mov    %r14,%rsi
    4b07:	48 89 df             	mov    %rbx,%rdi
    4b0a:	e8 11 fb ff ff       	call   4620 <add_write_request>
    4b0f:	e9 01 ff ff ff       	jmp    4a15 <handle_get_method+0xd5>
    4b14:	0f 1f 40 00          	nopl   0x0(%rax)
    4b18:	4c 89 fa             	mov    %r15,%rdx
    4b1b:	4c 89 e1             	mov    %r12,%rcx
    4b1e:	48 8d 35 d1 25 00 00 	lea    0x25d1(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    4b25:	31 c0                	xor    %eax,%eax
    4b27:	bf 01 00 00 00       	mov    $0x1,%edi
    4b2c:	e8 4f d9 ff ff       	call   2480 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    4b31:	48 8b 3d d8 54 00 00 	mov    0x54d8(%rip),%rdi        # a010 <http_404_content>
    4b38:	4c 89 f2             	mov    %r14,%rdx
    4b3b:	44 89 ee             	mov    %r13d,%esi
    4b3e:	e8 6d fc ff ff       	call   47b0 <_send_static_string_content>
}
    4b43:	e9 cd fe ff ff       	jmp    4a15 <handle_get_method+0xd5>
}
    4b48:	e8 03 d8 ff ff       	call   2350 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4b4d:	48 8b 0d cc 54 00 00 	mov    0x54cc(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4b54:	ba 28 00 00 00       	mov    $0x28,%edx
    4b59:	be 01 00 00 00       	mov    $0x1,%esi
    4b5e:	48 8d 3d 93 28 00 00 	lea    0x2893(%rip),%rdi        # 73f8 <_IO_stdin_used+0x3f8>
    4b65:	e8 96 d9 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    4b6a:	bf 01 00 00 00       	mov    $0x1,%edi
    4b6f:	e8 6c d9 ff ff       	call   24e0 <exit@plt>
    4b74:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4b7f:	90                   	nop

0000000000004b80 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4b80:	f3 0f 1e fa          	endbr64
    4b84:	55                   	push   %rbp
    4b85:	48 89 e5             	mov    %rsp,%rbp
    4b88:	41 57                	push   %r15
    4b8a:	41 56                	push   %r14
    4b8c:	41 55                	push   %r13
    4b8e:	41 54                	push   %r12
    4b90:	53                   	push   %rbx
    4b91:	48 83 ec 28          	sub    $0x28,%rsp
    4b95:	ff 15 4d 54 00 00    	call   *0x544d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    method = strtok_r(method_buffer, " ", &saveptr);
    4b9b:	4c 8d 35 e3 24 00 00 	lea    0x24e3(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4ba2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4bab:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    4baf:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4bb1:	4c 8d 7d c0          	lea    -0x40(%rbp),%r15
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4bb5:	41 89 f4             	mov    %esi,%r12d
    4bb8:	49 89 d5             	mov    %rdx,%r13
    method = strtok_r(method_buffer, " ", &saveptr);
    4bbb:	4c 89 f6             	mov    %r14,%rsi
    4bbe:	4c 89 fa             	mov    %r15,%rdx
    4bc1:	e8 da d7 ff ff       	call   23a0 <strtok_r@plt>
    for (; *str; ++str)
    4bc6:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    4bc9:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    4bcc:	84 d2                	test   %dl,%dl
    4bce:	88 55 bf             	mov    %dl,-0x41(%rbp)
    4bd1:	74 22                	je     4bf5 <handle_http_method+0x75>
        *str = (char)tolower(*str);
    4bd3:	e8 78 d9 ff ff       	call   2550 <__ctype_tolower_loc@plt>
    4bd8:	48 0f be 55 bf       	movsbq -0x41(%rbp),%rdx
    4bdd:	48 89 d9             	mov    %rbx,%rcx
    4be0:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    4be3:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    4be7:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    4bea:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    4bed:	48 0f be 11          	movsbq (%rcx),%rdx
    4bf1:	84 d2                	test   %dl,%dl
    4bf3:	75 eb                	jne    4be0 <handle_http_method+0x60>
    path = strtok_r(NULL, " ", &saveptr);
    4bf5:	4c 89 fa             	mov    %r15,%rdx
    4bf8:	4c 89 f6             	mov    %r14,%rsi
    4bfb:	31 ff                	xor    %edi,%edi
    4bfd:	e8 9e d7 ff ff       	call   23a0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4c02:	48 8d 35 2a 25 00 00 	lea    0x252a(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4c09:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4c0c:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    4c0f:	e8 bc d7 ff ff       	call   23d0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4c14:	4c 89 ea             	mov    %r13,%rdx
    4c17:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4c1a:	85 c0                	test   %eax,%eax
    4c1c:	75 2a                	jne    4c48 <handle_http_method+0xc8>
        handle_get_method(path, client_socket, ring);
    4c1e:	4c 89 f7             	mov    %r14,%rdi
    4c21:	e8 1a fd ff ff       	call   4940 <handle_get_method>
}
    4c26:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    4c2a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4c33:	75 21                	jne    4c56 <handle_http_method+0xd6>
    4c35:	48 83 c4 28          	add    $0x28,%rsp
    4c39:	5b                   	pop    %rbx
    4c3a:	41 5c                	pop    %r12
    4c3c:	41 5d                	pop    %r13
    4c3e:	41 5e                	pop    %r14
    4c40:	41 5f                	pop    %r15
    4c42:	5d                   	pop    %rbp
    4c43:	c3                   	ret
    4c44:	0f 1f 40 00          	nopl   0x0(%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4c48:	48 8b 3d c9 53 00 00 	mov    0x53c9(%rip),%rdi        # a018 <unimplemented_content>
    4c4f:	e8 5c fb ff ff       	call   47b0 <_send_static_string_content>
}
    4c54:	eb d0                	jmp    4c26 <handle_http_method+0xa6>
    4c56:	e8 f5 d6 ff ff       	call   2350 <__stack_chk_fail@plt>
    4c5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004c60 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4c60:	f3 0f 1e fa          	endbr64
    4c64:	55                   	push   %rbp
    4c65:	48 89 e5             	mov    %rsp,%rbp
    4c68:	ff 15 7a 53 00 00    	call   *0x537a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    for (int i = 0; i < dest_sz; i++) {
    4c6e:	85 d2                	test   %edx,%edx
    4c70:	7e 36                	jle    4ca8 <get_line+0x48>
    4c72:	48 63 d2             	movslq %edx,%rdx
    4c75:	48 83 c7 01          	add    $0x1,%rdi
    4c79:	48 01 f2             	add    %rsi,%rdx
    4c7c:	eb 0f                	jmp    4c8d <get_line+0x2d>
    4c7e:	66 90                	xchg   %ax,%ax
    4c80:	48 83 c6 01          	add    $0x1,%rsi
    4c84:	48 83 c7 01          	add    $0x1,%rdi
    4c88:	48 39 d6             	cmp    %rdx,%rsi
    4c8b:	74 1b                	je     4ca8 <get_line+0x48>
        dest[i] = src[i];
    4c8d:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4c91:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4c93:	3c 0d                	cmp    $0xd,%al
    4c95:	75 e9                	jne    4c80 <get_line+0x20>
    4c97:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4c9a:	75 e4                	jne    4c80 <get_line+0x20>
            return 0;
    4c9c:	31 c0                	xor    %eax,%eax
            dest[i] = '\0';
    4c9e:	c6 06 00             	movb   $0x0,(%rsi)
}
    4ca1:	5d                   	pop    %rbp
    4ca2:	c3                   	ret
    4ca3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    return 1;
    4ca8:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4cad:	5d                   	pop    %rbp
    4cae:	c3                   	ret
    4caf:	90                   	nop

0000000000004cb0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4cb0:	f3 0f 1e fa          	endbr64
    4cb4:	55                   	push   %rbp
    4cb5:	48 89 e5             	mov    %rsp,%rbp
    4cb8:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    4cbf:	ff 15 23 53 00 00    	call   *0x5323(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    4cc5:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4cc9:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4cd2:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
    4cd6:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4cd8:	4c 8d 95 f0 fb ff ff 	lea    -0x410(%rbp),%r10
    4cdf:	4c 8d 4d f0          	lea    -0x10(%rbp),%r9
    4ce3:	4c 89 d0             	mov    %r10,%rax
    4ce6:	eb 15                	jmp    4cfd <handle_client_request+0x4d>
    4ce8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4cf0:	48 83 c0 01          	add    $0x1,%rax
    4cf4:	48 83 c1 01          	add    $0x1,%rcx
    4cf8:	4c 39 c8             	cmp    %r9,%rax
    4cfb:	74 43                	je     4d40 <handle_client_request+0x90>
        dest[i] = src[i];
    4cfd:	44 0f b6 01          	movzbl (%rcx),%r8d
    4d01:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4d04:	41 80 f8 0d          	cmp    $0xd,%r8b
    4d08:	75 e6                	jne    4cf0 <handle_client_request+0x40>
    4d0a:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4d0e:	75 e0                	jne    4cf0 <handle_client_request+0x40>
            dest[i] = '\0';
    4d10:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4d13:	8b 47 08             	mov    0x8(%rdi),%eax
    4d16:	48 89 f2             	mov    %rsi,%rdx
    4d19:	4c 89 d7             	mov    %r10,%rdi
    4d1c:	89 c6                	mov    %eax,%esi
    4d1e:	e8 5d fe ff ff       	call   4b80 <handle_http_method>
}
    4d23:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    4d27:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d30:	75 35                	jne    4d67 <handle_client_request+0xb7>
    4d32:	c9                   	leave
    4d33:	31 c0                	xor    %eax,%eax
    4d35:	c3                   	ret
    4d36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4d40:	48 8b 0d d9 52 00 00 	mov    0x52d9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4d47:	ba 12 00 00 00       	mov    $0x12,%edx
    4d4c:	be 01 00 00 00       	mov    $0x1,%esi
    4d51:	48 8d 3d df 23 00 00 	lea    0x23df(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4d58:	e8 a3 d7 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    4d5d:	bf 01 00 00 00       	mov    $0x1,%edi
    4d62:	e8 79 d7 ff ff       	call   24e0 <exit@plt>
}
    4d67:	e8 e4 d5 ff ff       	call   2350 <__stack_chk_fail@plt>
    4d6c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004d70 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4d70:	f3 0f 1e fa          	endbr64
    4d74:	55                   	push   %rbp
    4d75:	48 89 e5             	mov    %rsp,%rbp
    4d78:	41 54                	push   %r12
    4d7a:	53                   	push   %rbx
    4d7b:	ff 15 67 52 00 00    	call   *0x5267(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    4d81:	8b 41 44             	mov    0x44(%rcx),%eax
    4d84:	83 c0 01             	add    $0x1,%eax
    4d87:	48 89 cb             	mov    %rcx,%rbx
	if (ring->flags & IORING_SETUP_SQE128)
    4d8a:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    4d90:	4c 8b 03             	mov    (%rbx),%r8
    4d93:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4d96:	f6 c1 02             	test   $0x2,%cl
    4d99:	74 00                	je     4d9b <add_accept_request+0x2b>
	if (next - head <= sq->ring_entries) {
    4d9b:	41 89 c0             	mov    %eax,%r8d
    4d9e:	45 29 c8             	sub    %r9d,%r8d
    4da1:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4da5:	0f 82 28 d8 ff ff    	jb     25d3 <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4dab:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4dae:	44 8b 63 44          	mov    0x44(%rbx),%r12d
    4db2:	44 23 63 58          	and    0x58(%rbx),%r12d
		sq->sqe_tail = next;
    4db6:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4db9:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4dbc:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4dc0:	41 d3 e4             	shl    %cl,%r12d
    4dc3:	49 c1 e4 06          	shl    $0x6,%r12
    4dc7:	4c 03 63 38          	add    0x38(%rbx),%r12
	sqe->fd = fd;
    4dcb:	41 89 7c 24 04       	mov    %edi,0x4(%r12)
  struct Request *req = malloc(sizeof(*req));
    4dd0:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4dd5:	41 c7 04 24 0d 00 00 00 	movl   $0xd,(%r12)
	sqe->off = offset;
    4ddd:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
	sqe->addr = (unsigned long) addr;
    4de2:	49 89 74 24 10       	mov    %rsi,0x10(%r12)
	sqe->buf_index = 0;
    4de7:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->len = len;
    4df0:	49 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%r12)
	sqe->addr3 = 0;
    4df9:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    4dff:	e8 3c d6 ff ff       	call   2440 <malloc@plt>
  io_uring_submit(ring);
    4e04:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4e07:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4e0d:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
    4e12:	5b                   	pop    %rbx
    4e13:	41 5c                	pop    %r12
    4e15:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4e16:	e9 45 d5 ff ff       	jmp    2360 <io_uring_submit@plt>
    4e1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004e20 <io_thread>:
void* io_thread(void *arg) {
    4e20:	f3 0f 1e fa          	endbr64
    4e24:	55                   	push   %rbp
    4e25:	48 89 e5             	mov    %rsp,%rbp
    4e28:	41 57                	push   %r15
    4e2a:	41 56                	push   %r14
    4e2c:	41 55                	push   %r13
    4e2e:	41 54                	push   %r12
    4e30:	53                   	push   %rbx
    4e31:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4e38:	ff 15 aa 51 00 00    	call   *0x51aa(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e3e:	31 d2                	xor    %edx,%edx
  struct io_uring ring = *data->ring;
    4e40:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4e49:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    4e4d:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e51:	48 8d 9d e0 fa ff ff 	lea    -0x520(%rbp),%rbx
void* io_thread(void *arg) {
    4e58:	49 89 fc             	mov    %rdi,%r12
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e5b:	bf 00 01 00 00       	mov    $0x100,%edi
    4e60:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4e63:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4e67:	0f 29 8d e0 fa ff ff 	movaps %xmm1,-0x520(%rbp)
    4e6e:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4e73:	0f 29 95 f0 fa ff ff 	movaps %xmm2,-0x510(%rbp)
    4e7a:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4e7f:	0f 29 9d 00 fb ff ff 	movaps %xmm3,-0x500(%rbp)
    4e86:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4e8b:	0f 29 a5 10 fb ff ff 	movaps %xmm4,-0x4f0(%rbp)
    4e92:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4e97:	0f 29 ad 20 fb ff ff 	movaps %xmm5,-0x4e0(%rbp)
    4e9e:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4ea3:	0f 29 b5 30 fb ff ff 	movaps %xmm6,-0x4d0(%rbp)
    4eaa:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4eaf:	0f 29 bd 40 fb ff ff 	movaps %xmm7,-0x4c0(%rbp)
    4eb6:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4ebb:	0f 29 8d 50 fb ff ff 	movaps %xmm1,-0x4b0(%rbp)
    4ec2:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4eca:	0f 29 95 60 fb ff ff 	movaps %xmm2,-0x4a0(%rbp)
    4ed1:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4ed9:	0f 29 9d 70 fb ff ff 	movaps %xmm3,-0x490(%rbp)
    4ee0:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4ee8:	0f 29 a5 80 fb ff ff 	movaps %xmm4,-0x480(%rbp)
    4eef:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4ef7:	0f 29 ad 90 fb ff ff 	movaps %xmm5,-0x470(%rbp)
    4efe:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4f06:	0f 29 b5 a0 fb ff ff 	movaps %xmm6,-0x460(%rbp)
    4f0d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4f14:	48 89 85 b0 fb ff ff 	mov    %rax,-0x450(%rbp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4f1b:	e8 00 d5 ff ff       	call   2420 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4f20:	49 8b 7c 24 48       	mov    0x48(%r12),%rdi
    4f25:	31 f6                	xor    %esi,%esi
    4f27:	e8 f4 d5 ff ff       	call   2520 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4f2c:	31 d2                	xor    %edx,%edx
    4f2e:	be 01 00 00 00       	mov    $0x1,%esi
    4f33:	bf 02 00 00 00       	mov    $0x2,%edi
    4f38:	e8 33 d6 ff ff       	call   2570 <socket@plt>
    4f3d:	89 85 ac fa ff ff    	mov    %eax,-0x554(%rbp)
  if (sock == -1)
    4f43:	83 f8 ff             	cmp    $0xffffffff,%eax
    4f46:	0f 84 c9 d6 ff ff    	je     2615 <io_thread.cold+0x38>
    4f4c:	89 c7                	mov    %eax,%edi
  if (setsockopt(sock,
    4f4e:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4f54:	ba 02 00 00 00       	mov    $0x2,%edx
    4f59:	be 01 00 00 00       	mov    $0x1,%esi
    4f5e:	48 8d 8d b0 fa ff ff 	lea    -0x550(%rbp),%rcx
  int enable = 1;
    4f65:	c7 85 b0 fa ff ff 01 00 00 00 	movl   $0x1,-0x550(%rbp)
  if (setsockopt(sock,
    4f6f:	e8 ac d3 ff ff       	call   2320 <setsockopt@plt>
    4f74:	85 c0                	test   %eax,%eax
    4f76:	0f 88 6d d6 ff ff    	js     25e9 <io_thread.cold+0xc>
  if (bind(sock,
    4f7c:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4f82:	ba 10 00 00 00       	mov    $0x10,%edx
  return __builtin___memset_chk (__dest, __ch, __len,
    4f87:	48 8d b5 c0 fa ff ff 	lea    -0x540(%rbp),%rsi
    4f8e:	48 c7 85 c4 fa ff ff 00 00 00 00 	movq   $0x0,-0x53c(%rbp)
    4f99:	c7 85 cc fa ff ff 00 00 00 00 	movl   $0x0,-0x534(%rbp)
  srv_addr.sin_family = AF_INET;
    4fa3:	c7 85 c0 fa ff ff 02 00 18 db 	movl   $0xdb180002,-0x540(%rbp)
  if (bind(sock,
    4fad:	e8 de d4 ff ff       	call   2490 <bind@plt>
    4fb2:	85 c0                	test   %eax,%eax
    4fb4:	0f 88 67 d6 ff ff    	js     2621 <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4fba:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4fc0:	be 0a 00 00 00       	mov    $0xa,%esi
    4fc5:	e8 86 d4 ff ff       	call   2450 <listen@plt>
    4fca:	85 c0                	test   %eax,%eax
    4fcc:	0f 88 23 d6 ff ff    	js     25f5 <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4fd2:	ba db 18 00 00       	mov    $0x18db,%edx
    4fd7:	48 8d 35 9e 21 00 00 	lea    0x219e(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4fde:	bf 01 00 00 00       	mov    $0x1,%edi
    4fe3:	31 c0                	xor    %eax,%eax
    4fe5:	e8 96 d4 ff ff       	call   2480 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4fea:	48 8d 85 d0 fa ff ff 	lea    -0x530(%rbp),%rax
    4ff1:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4ff7:	48 89 d9             	mov    %rbx,%rcx
    4ffa:	48 8d 95 b4 fa ff ff 	lea    -0x54c(%rbp),%rdx
    5001:	48 89 c6             	mov    %rax,%rsi
  socklen_t client_addr_len = sizeof(client_addr);
    5004:	c7 85 b4 fa ff ff 10 00 00 00 	movl   $0x10,-0x54c(%rbp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    500e:	48 89 95 88 fa ff ff 	mov    %rdx,-0x578(%rbp)
    5015:	48 89 85 90 fa ff ff 	mov    %rax,-0x570(%rbp)
    501c:	e8 4f fd ff ff       	call   4d70 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5021:	bf 01 00 00 00       	mov    $0x1,%edi
    5026:	be 10 00 00 00       	mov    $0x10,%esi
    502b:	e8 90 d3 ff ff       	call   23c0 <calloc@plt>
    void *buf = malloc(size);
    5030:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5035:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    5038:	e8 03 d4 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    503d:	48 85 c0             	test   %rax,%rax
    5040:	0f 84 cf 04 00 00    	je     5515 <io_thread+0x6f5>
  iov->iov_base = zh_malloc(10);
    5046:	49 89 06             	mov    %rax,(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    5049:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    504f:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
  iov->iov_len = 10;
    5055:	49 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    505d:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5060:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    5067:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5069:	f6 c1 02             	test   $0x2,%cl
    506c:	0f 85 2e 04 00 00    	jne    54a0 <io_thread+0x680>
	if (next - head <= sq->ring_entries) {
    5072:	89 d0                	mov    %edx,%eax
    5074:	29 f0                	sub    %esi,%eax
    5076:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    507c:	0f 82 89 d5 ff ff    	jb     260b <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5082:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5085:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    508b:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    508f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5092:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5098:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    509b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    50a1:	49 8d 74 24 50       	lea    0x50(%r12),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    50a6:	41 8b 54 24 50       	mov    0x50(%r12),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50ab:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    50ad:	48 89 b5 98 fa ff ff 	mov    %rsi,-0x568(%rbp)
    50b4:	48 c1 e0 06          	shl    $0x6,%rax
    50b8:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    50bf:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    50c5:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    50c8:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    50d0:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    50d4:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    50dc:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    50e4:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    50e8:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    50ec:	e8 6f d2 ff ff       	call   2360 <io_uring_submit@plt>
  while (data->running == 1) {
    50f1:	41 83 7c 24 34 01    	cmpl   $0x1,0x34(%r12)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    50f7:	4c 8d 8d b8 fa ff ff 	lea    -0x548(%rbp),%r9
    50fe:	4c 8d 95 c0 fb ff ff 	lea    -0x440(%rbp),%r10
    5105:	0f 85 ed 01 00 00    	jne    52f8 <io_thread+0x4d8>
    510b:	4c 89 8d a0 fa ff ff 	mov    %r9,-0x560(%rbp)
    5112:	4c 89 95 80 fa ff ff 	mov    %r10,-0x580(%rbp)
    5119:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5120:	48 8d 3d 6b 20 00 00 	lea    0x206b(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    5127:	e8 e4 d1 ff ff       	call   2310 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    512c:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5132:	8b bd 90 fb ff ff    	mov    -0x470(%rbp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5138:	c1 e9 0b             	shr    $0xb,%ecx
    513b:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    513e:	48 8b 85 50 fb ff ff 	mov    -0x4b0(%rbp),%rax
    5145:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5147:	48 8b b5 48 fb ff ff 	mov    -0x4b8(%rbp),%rsi
    514e:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5150:	39 d0                	cmp    %edx,%eax
    5152:	74 34                	je     5188 <io_thread+0x368>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5154:	89 f8                	mov    %edi,%eax
    5156:	21 d0                	and    %edx,%eax
    5158:	d3 e0                	shl    %cl,%eax
    515a:	48 c1 e0 04          	shl    $0x4,%rax
    515e:	48 03 85 78 fb ff ff 	add    -0x488(%rbp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5165:	f6 85 a9 fb ff ff 01 	testb  $0x1,-0x457(%rbp)
    516c:	0f 85 be 01 00 00    	jne    5330 <io_thread+0x510>
    5172:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5176:	0f 85 2c 03 00 00    	jne    54a8 <io_thread+0x688>
			if (cqe->res < 0)
    517c:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    517f:	83 c2 01             	add    $0x1,%edx
    5182:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5184:	85 c0                	test   %eax,%eax
    5186:	79 b6                	jns    513e <io_thread+0x31e>
	*cqe_ptr = cqe;
    5188:	48 c7 85 b8 fa ff ff 00 00 00 00 	movq   $0x0,-0x548(%rbp)
	return err;
    5193:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5198:	48 8b b5 a0 fa ff ff 	mov    -0x560(%rbp),%rsi
    519f:	45 31 c0             	xor    %r8d,%r8d
    51a2:	31 d2                	xor    %edx,%edx
    51a4:	48 89 df             	mov    %rbx,%rdi
    51a7:	b9 01 00 00 00       	mov    $0x1,%ecx
    51ac:	e8 bf d2 ff ff       	call   2470 <__io_uring_get_cqe@plt>
    51b1:	41 89 c5             	mov    %eax,%r13d
      if (cqe->user_data == 1) {
    51b4:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    51bb:	48 83 38 01          	cmpq   $0x1,(%rax)
    51bf:	0f 84 f3 02 00 00    	je     54b8 <io_thread+0x698>
    51c5:	48 8d 3d ec 1f 00 00 	lea    0x1fec(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    51cc:	e8 3f d1 ff ff       	call   2310 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    51d1:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    51d8:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    51db:	45 85 ed             	test   %r13d,%r13d
    51de:	0f 88 f9 d3 ff ff    	js     25dd <io_thread.cold>
      if (cqe->res < 0) {
    51e4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    51e7:	45 8b 07             	mov    (%r15),%r8d
      if (cqe->res < 0) {
    51ea:	85 c0                	test   %eax,%eax
    51ec:	0f 88 e5 02 00 00    	js     54d7 <io_thread+0x6b7>
      switch (req->event_type) {
    51f2:	41 83 f8 01          	cmp    $0x1,%r8d
    51f6:	0f 84 84 01 00 00    	je     5380 <io_thread+0x560>
    51fc:	41 83 f8 02          	cmp    $0x2,%r8d
    5200:	0f 84 aa 01 00 00    	je     53b0 <io_thread+0x590>
    5206:	45 85 c0             	test   %r8d,%r8d
    5209:	0f 85 59 01 00 00    	jne    5368 <io_thread+0x548>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    520f:	48 8b 95 88 fa ff ff 	mov    -0x578(%rbp),%rdx
    5216:	48 8b b5 90 fa ff ff 	mov    -0x570(%rbp),%rsi
    521d:	48 89 d9             	mov    %rbx,%rcx
    5220:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    5226:	e8 45 fb ff ff       	call   4d70 <add_accept_request>
              add_read_request(cqe->res, &ring);
    522b:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    5232:	48 89 de             	mov    %rbx,%rsi
    5235:	8b 78 08             	mov    0x8(%rax),%edi
    5238:	e8 83 f4 ff ff       	call   46c0 <add_read_request>
              free(req);
    523d:	4c 89 ff             	mov    %r15,%rdi
    5240:	e8 9b d0 ff ff       	call   22e0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5245:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
	if (cqe)
    524c:	48 85 c0             	test   %rax,%rax
    524f:	0f 85 13 01 00 00    	jne    5368 <io_thread+0x548>
	unsigned int head, next = sq->sqe_tail + 1;
    5255:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    525b:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5261:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5264:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    526b:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    526d:	f6 c1 02             	test   $0x2,%cl
    5270:	74 00                	je     5272 <io_thread+0x452>
	if (next - head <= sq->ring_entries) {
    5272:	89 d0                	mov    %edx,%eax
    5274:	29 f0                	sub    %esi,%eax
    5276:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    527c:	0f 82 7f d3 ff ff    	jb     2601 <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5282:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5285:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    528b:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    528f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5292:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5298:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    529b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52a1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    52a3:	41 8b 54 24 50       	mov    0x50(%r12),%edx
	sqe->user_data = (unsigned long) data;
    52a8:	48 8b b5 98 fa ff ff 	mov    -0x568(%rbp),%rsi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52af:	48 c1 e0 06          	shl    $0x6,%rax
    52b3:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    52ba:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    52c0:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    52c3:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    52cb:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    52cf:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    52d7:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    52df:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    52e3:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    52e7:	e8 74 d0 ff ff       	call   2360 <io_uring_submit@plt>
  while (data->running == 1) {
    52ec:	41 83 7c 24 34 01    	cmpl   $0x1,0x34(%r12)
    52f2:	0f 84 28 fe ff ff    	je     5120 <io_thread+0x300>
    52f8:	48 8d 3d f2 1e 00 00 	lea    0x1ef2(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    52ff:	e8 0c d0 ff ff       	call   2310 <puts@plt>
}
    5304:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    5308:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5311:	0f 85 25 02 00 00    	jne    553c <io_thread+0x71c>
    5317:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    531e:	31 c0                	xor    %eax,%eax
    5320:	5b                   	pop    %rbx
    5321:	41 5c                	pop    %r12
    5323:	41 5d                	pop    %r13
    5325:	41 5e                	pop    %r14
    5327:	41 5f                	pop    %r15
    5329:	5d                   	pop    %rbp
    532a:	c3                   	ret
    532b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    5330:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5337:	48 85 c0             	test   %rax,%rax
    533a:	0f 84 58 fe ff ff    	je     5198 <io_thread+0x378>
      if (cqe->user_data == 1) {
    5340:	48 83 38 01          	cmpq   $0x1,(%rax)
    5344:	0f 84 6e 01 00 00    	je     54b8 <io_thread+0x698>
    534a:	48 8d 3d 67 1e 00 00 	lea    0x1e67(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    5351:	e8 ba cf ff ff       	call   2310 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5356:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    535d:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    5360:	e9 7f fe ff ff       	jmp    51e4 <io_thread+0x3c4>
    5365:	0f 1f 00             	nopl   (%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5368:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
    536f:	8b 02                	mov    (%rdx),%eax
    5371:	83 c0 01             	add    $0x1,%eax
    5374:	89 02                	mov    %eax,(%rdx)
}
    5376:	e9 da fe ff ff       	jmp    5255 <io_thread+0x435>
    537b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              if (!cqe->res) {
    5380:	85 c0                	test   %eax,%eax
    5382:	75 7c                	jne    5400 <io_thread+0x5e0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5384:	48 8b 0d 95 4c 00 00 	mov    0x4c95(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    538b:	ba 0f 00 00 00       	mov    $0xf,%edx
    5390:	be 01 00 00 00       	mov    $0x1,%esi
    5395:	48 8d 3d 45 1e 00 00 	lea    0x1e45(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    539c:	e8 5f d1 ff ff       	call   2500 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    53a1:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    53a8:	e9 9f fe ff ff       	jmp    524c <io_thread+0x42c>
    53ad:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    53b0:	41 8b 47 04          	mov    0x4(%r15),%eax
    53b4:	45 31 ed             	xor    %r13d,%r13d
    53b7:	85 c0                	test   %eax,%eax
    53b9:	7e 20                	jle    53db <io_thread+0x5bb>
    53bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  free(req->iov[i].iov_base);
    53c0:	4c 89 e8             	mov    %r13,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    53c3:	49 83 c5 01          	add    $0x1,%r13
                  free(req->iov[i].iov_base);
    53c7:	48 c1 e0 04          	shl    $0x4,%rax
    53cb:	49 8b 7c 07 10       	mov    0x10(%r15,%rax,1),%rdi
    53d0:	e8 0b cf ff ff       	call   22e0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    53d5:	45 39 6f 04          	cmp    %r13d,0x4(%r15)
    53d9:	7f e5                	jg     53c0 <io_thread+0x5a0>
              close(req->client_socket);
    53db:	41 8b 7f 08          	mov    0x8(%r15),%edi
    53df:	e8 ac cf ff ff       	call   2390 <close@plt>
              free(req);
    53e4:	4c 89 ff             	mov    %r15,%rdi
    53e7:	e8 f4 ce ff ff       	call   22e0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    53ec:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    53f3:	e9 54 fe ff ff       	jmp    524c <io_thread+0x42c>
    53f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int i = 0; i < dest_sz; i++) {
    5400:	49 8b 57 10          	mov    0x10(%r15),%rdx
    5404:	48 8b 85 80 fa ff ff 	mov    -0x580(%rbp),%rax
    540b:	48 8d 75 c0          	lea    -0x40(%rbp),%rsi
    540f:	eb 14                	jmp    5425 <io_thread+0x605>
    5411:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5418:	48 83 c0 01          	add    $0x1,%rax
    541c:	48 83 c2 01          	add    $0x1,%rdx
    5420:	48 39 c6             	cmp    %rax,%rsi
    5423:	74 4b                	je     5470 <io_thread+0x650>
        dest[i] = src[i];
    5425:	0f b6 0a             	movzbl (%rdx),%ecx
    5428:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    542a:	80 f9 0d             	cmp    $0xd,%cl
    542d:	75 e9                	jne    5418 <io_thread+0x5f8>
    542f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5433:	75 e3                	jne    5418 <io_thread+0x5f8>
            dest[i] = '\0';
    5435:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5438:	48 8b bd 80 fa ff ff 	mov    -0x580(%rbp),%rdi
    543f:	48 89 da             	mov    %rbx,%rdx
    5442:	41 8b 77 08          	mov    0x8(%r15),%esi
    5446:	e8 35 f7 ff ff       	call   4b80 <handle_http_method>
              free(req->iov[0].iov_base);
    544b:	49 8b 7f 10          	mov    0x10(%r15),%rdi
    544f:	e8 8c ce ff ff       	call   22e0 <free@plt>
              free(req);
    5454:	4c 89 ff             	mov    %r15,%rdi
    5457:	e8 84 ce ff ff       	call   22e0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    545c:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    5463:	e9 e4 fd ff ff       	jmp    524c <io_thread+0x42c>
    5468:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5470:	48 8b 0d a9 4b 00 00 	mov    0x4ba9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5477:	ba 12 00 00 00       	mov    $0x12,%edx
    547c:	be 01 00 00 00       	mov    $0x1,%esi
    5481:	48 8d 3d af 1c 00 00 	lea    0x1caf(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5488:	e8 73 d0 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    548d:	bf 01 00 00 00       	mov    $0x1,%edi
    5492:	e8 49 d0 ff ff       	call   24e0 <exit@plt>
    5497:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    54a0:	e9 cd fb ff ff       	jmp    5072 <io_thread+0x252>
    54a5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    54a8:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	return err;
    54af:	e9 8c fe ff ff       	jmp    5340 <io_thread+0x520>
    54b4:	0f 1f 40 00          	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    54b8:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    54bf:	48 8d 3d de 1c 00 00 	lea    0x1cde(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    54c6:	8b 02                	mov    (%rdx),%eax
    54c8:	83 c0 01             	add    $0x1,%eax
    54cb:	89 02                	mov    %eax,(%rdx)
    54cd:	e8 3e ce ff ff       	call   2310 <puts@plt>
    54d2:	e9 21 fe ff ff       	jmp    52f8 <io_thread+0x4d8>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    54d7:	f7 d8                	neg    %eax
    54d9:	44 89 85 ac fa ff ff 	mov    %r8d,-0x554(%rbp)
    54e0:	89 c7                	mov    %eax,%edi
    54e2:	e8 59 d0 ff ff       	call   2540 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    54e7:	48 8b 3d 32 4b 00 00 	mov    0x4b32(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    54ee:	be 01 00 00 00       	mov    $0x1,%esi
    54f3:	44 8b 85 ac fa ff ff 	mov    -0x554(%rbp),%r8d
    54fa:	48 89 c1             	mov    %rax,%rcx
    54fd:	48 8d 15 24 1f 00 00 	lea    0x1f24(%rip),%rdx        # 7428 <_IO_stdin_used+0x428>
    5504:	31 c0                	xor    %eax,%eax
    5506:	e8 05 d0 ff ff       	call   2510 <__fprintf_chk@plt>
          exit(1);
    550b:	bf 01 00 00 00       	mov    $0x1,%edi
    5510:	e8 cb cf ff ff       	call   24e0 <exit@plt>
    5515:	48 8b 0d 04 4b 00 00 	mov    0x4b04(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    551c:	ba 28 00 00 00       	mov    $0x28,%edx
    5521:	be 01 00 00 00       	mov    $0x1,%esi
    5526:	48 8d 3d cb 1e 00 00 	lea    0x1ecb(%rip),%rdi        # 73f8 <_IO_stdin_used+0x3f8>
    552d:	e8 ce cf ff ff       	call   2500 <fwrite@plt>
        exit(1);
    5532:	bf 01 00 00 00       	mov    $0x1,%edi
    5537:	e8 a4 cf ff ff       	call   24e0 <exit@plt>
}
    553c:	e8 0f ce ff ff       	call   2350 <__stack_chk_fail@plt>
    5541:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    554c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005550 <sendm>:
int sendm(struct BarrierTask *data) {
    5550:	f3 0f 1e fa          	endbr64
    5554:	55                   	push   %rbp
    5555:	48 89 e5             	mov    %rsp,%rbp
    5558:	41 57                	push   %r15
    555a:	41 56                	push   %r14
    555c:	41 55                	push   %r13
    555e:	41 54                	push   %r12
    5560:	53                   	push   %rbx
    5561:	48 83 ec 28          	sub    $0x28,%rsp
    5565:	ff 15 7d 4a 00 00    	call   *0x4a7d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  if (data->sending == 1) {
    556b:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
int sendm(struct BarrierTask *data) {
    5572:	48 89 fa             	mov    %rdi,%rdx
  if (data->sending == 1) {
    5575:	0f 85 a5 01 00 00    	jne    5720 <sendm+0x1d0>
      for (int n = 0 ; n < data->thread_count; n++) {
    557b:	48 8d 9f 80 01 00 00 	lea    0x180(%rdi),%rbx
    5582:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    5588:	45 31 ff             	xor    %r15d,%r15d
    558b:	48 89 5d c8          	mov    %rbx,-0x38(%rbp)
    558f:	48 8d 9f 88 01 00 00 	lea    0x188(%rdi),%rbx
    5596:	48 89 5d c0          	mov    %rbx,-0x40(%rbp)
    559a:	85 c0                	test   %eax,%eax
    559c:	0f 8e d6 00 00 00    	jle    5678 <sendm+0x128>
    55a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (n == data->thread_index) { continue; }
    55a8:	44 39 ba 30 01 00 00 	cmp    %r15d,0x130(%rdx)
    55af:	0f 84 b6 00 00 00    	je     566b <sendm+0x11b>
        struct Data *them = data->mailboxes[n].higher;
    55b5:	4d 89 f9             	mov    %r15,%r9
    55b8:	49 c1 e1 05          	shl    $0x5,%r9
    55bc:	4c 03 8a 68 01 00 00 	add    0x168(%rdx),%r9
    55c3:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    55c7:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    55cb:	4d 63 42 10          	movslq 0x10(%r10),%r8
    55cf:	4d 39 c3             	cmp    %r8,%r11
    55d2:	0f 8d 8a 00 00 00    	jge    5662 <sendm+0x112>
    55d8:	4c 89 c6             	mov    %r8,%rsi
    55db:	48 8b 9a 08 01 00 00 	mov    0x108(%rdx),%rbx
    55e2:	4d 8b 71 10          	mov    0x10(%r9),%r14
    55e6:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    55e9:	49 8b 0a             	mov    (%r10),%rcx
    55ec:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    55f0:	48 83 f8 02          	cmp    $0x2,%rax
    55f4:	0f 86 0e 01 00 00    	jbe    5708 <sendm+0x1b8>
    55fa:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5602:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    560a:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    560e:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5612:	4c 39 6d c8          	cmp    %r13,-0x38(%rbp)
    5616:	73 78                	jae    5690 <sendm+0x140>
    5618:	4c 8b 6d c0          	mov    -0x40(%rbp),%r13
    561c:	4d 39 ec             	cmp    %r13,%r12
    561f:	73 6f                	jae    5690 <sendm+0x140>
    5621:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5625:	48 01 cf             	add    %rcx,%rdi
    5628:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5630:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    5637:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    563b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    563f:	4c 39 df             	cmp    %r11,%rdi
    5642:	75 ec                	jne    5630 <sendm+0xe0>
    5644:	0f 1f 40 00          	nopl   0x0(%rax)
    5648:	48 01 f3             	add    %rsi,%rbx
    564b:	4c 01 f6             	add    %r14,%rsi
    564e:	48 89 9a 08 01 00 00 	mov    %rbx,0x108(%rdx)
    5655:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5659:	4d 89 42 08          	mov    %r8,0x8(%r10)
    565d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5662:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5665:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    566b:	49 83 c7 01          	add    $0x1,%r15
    566f:	44 39 f8             	cmp    %r15d,%eax
    5672:	0f 8f 30 ff ff ff    	jg     55a8 <sendm+0x58>
}
    5678:	48 83 c4 28          	add    $0x28,%rsp
    567c:	31 c0                	xor    %eax,%eax
    567e:	5b                   	pop    %rbx
    567f:	41 5c                	pop    %r12
    5681:	41 5d                	pop    %r13
    5683:	41 5e                	pop    %r14
    5685:	41 5f                	pop    %r15
    5687:	5d                   	pop    %rbp
    5688:	c3                   	ret
    5689:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5690:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    5697:	49 89 f5             	mov    %rsi,%r13
    569a:	4c 89 e7             	mov    %r12,%rdi
    569d:	49 d1 ed             	shr    %r13
    56a0:	49 c1 e5 04          	shl    $0x4,%r13
    56a4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    56a9:	4c 89 6d b8          	mov    %r13,-0x48(%rbp)
    56ad:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    56b1:	4d 01 e5             	add    %r12,%r13
    56b4:	f6 45 b8 10          	testb  $0x10,-0x48(%rbp)
    56b8:	74 16                	je     56d0 <sendm+0x180>
          them->messages[them->messages_count++] = data->message; 
    56ba:	48 83 c7 10          	add    $0x10,%rdi
    56be:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    56c3:	4c 39 ef             	cmp    %r13,%rdi
    56c6:	74 18                	je     56e0 <sendm+0x190>
    56c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          them->messages[them->messages_count++] = data->message; 
    56d0:	0f 11 07             	movups %xmm0,(%rdi)
    56d3:	48 83 c7 20          	add    $0x20,%rdi
    56d7:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    56db:	4c 39 ef             	cmp    %r13,%rdi
    56de:	75 f0                	jne    56d0 <sendm+0x180>
    56e0:	48 89 f7             	mov    %rsi,%rdi
    56e3:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    56e7:	4c 01 df             	add    %r11,%rdi
    56ea:	40 f6 c6 01          	test   $0x1,%sil
    56ee:	0f 84 54 ff ff ff    	je     5648 <sendm+0xf8>
          them->messages[them->messages_count++] = data->message; 
    56f4:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    56fb:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    56ff:	e9 44 ff ff ff       	jmp    5648 <sendm+0xf8>
    5704:	0f 1f 40 00          	nopl   0x0(%rax)
    5708:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5710:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5718:	e9 04 ff ff ff       	jmp    5621 <sendm+0xd1>
    571d:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5720:	48 8d 3d dd 1a 00 00 	lea    0x1add(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5727:	e8 e4 cb ff ff       	call   2310 <puts@plt>
    572c:	e9 47 ff ff ff       	jmp    5678 <sendm+0x128>
    5731:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    573c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005740 <receive>:
int receive(struct BarrierTask *data) {
    5740:	f3 0f 1e fa          	endbr64
    5744:	55                   	push   %rbp
    5745:	48 89 e5             	mov    %rsp,%rbp
    5748:	41 55                	push   %r13
    574a:	41 54                	push   %r12
    574c:	53                   	push   %rbx
    574d:	48 83 ec 08          	sub    $0x8,%rsp
    5751:	ff 15 91 48 00 00    	call   *0x4891(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  for (int n = 0 ; n < data->thread_count; n++) {
    5757:	45 31 e4             	xor    %r12d,%r12d
    575a:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
int receive(struct BarrierTask *data) {
    5760:	48 89 fa             	mov    %rdi,%rdx
  for (int n = 0 ; n < data->thread_count; n++) {
    5763:	85 c0                	test   %eax,%eax
    5765:	0f 8e d9 00 00 00    	jle    5844 <receive+0x104>
    576b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5770:	4c 89 e6             	mov    %r12,%rsi
    5773:	48 c1 e6 05          	shl    $0x5,%rsi
    5777:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    577e:	4c 8b 2e             	mov    (%rsi),%r13
    for (int x = 0 ; x < me->messages_count ; x++) {
    5781:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    5785:	48 85 ff             	test   %rdi,%rdi
    5788:	0f 8e 9a 00 00 00    	jle    5828 <receive+0xe8>
      data->sends++;
    578e:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    5795:	4d 8b 45 00          	mov    0x0(%r13),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5799:	4c 63 1a             	movslq (%rdx),%r11
    579c:	49 89 c9             	mov    %rcx,%r9
    579f:	48 8d 41 01          	lea    0x1(%rcx),%rax
    57a3:	49 f7 d9             	neg    %r9
    57a6:	48 01 c7             	add    %rax,%rdi
    57a9:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    57ad:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    57b4:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    57b8:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    57bb:	49 29 c8             	sub    %rcx,%r8
    57be:	eb 09                	jmp    57c9 <receive+0x89>
    for (int x = 0 ; x < me->messages_count ; x++) {
    57c0:	48 83 c0 01          	add    $0x1,%rax
    57c4:	48 39 c7             	cmp    %rax,%rdi
    57c7:	74 5f                	je     5828 <receive+0xe8>
      data->n++;
    57c9:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    57cd:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
      data->n++;
    57d4:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    57db:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    57df:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    57e3:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    57e8:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    57ec:	75 d2                	jne    57c0 <receive+0x80>
    57ee:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    57f5:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    57f9:	75 c5                	jne    57c0 <receive+0x80>
    57fb:	bf 01 00 00 00       	mov    $0x1,%edi
    5800:	b9 01 00 00 00       	mov    $0x1,%ecx
    5805:	ba 01 00 00 00       	mov    $0x1,%edx
    580a:	31 c0                	xor    %eax,%eax
    580c:	48 8d 35 3d 1c 00 00 	lea    0x1c3d(%rip),%rsi        # 7450 <_IO_stdin_used+0x450>
    5813:	e8 68 cc ff ff       	call   2480 <__printf_chk@plt>
        exit(1);
    5818:	bf 01 00 00 00       	mov    $0x1,%edi
    581d:	e8 be cc ff ff       	call   24e0 <exit@plt>
    5822:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5828:	49 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%r13)
    asm volatile ("sfence" ::: "memory");
    5830:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    5833:	49 83 c4 01          	add    $0x1,%r12
    5837:	44 39 a2 34 01 00 00 	cmp    %r12d,0x134(%rdx)
    583e:	0f 8f 2c ff ff ff    	jg     5770 <receive+0x30>
}
    5844:	48 83 c4 08          	add    $0x8,%rsp
    5848:	31 c0                	xor    %eax,%eax
    584a:	5b                   	pop    %rbx
    584b:	41 5c                	pop    %r12
    584d:	41 5d                	pop    %r13
    584f:	5d                   	pop    %rbp
    5850:	c3                   	ret
    5851:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    585c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005860 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5860:	f3 0f 1e fa          	endbr64
    5864:	55                   	push   %rbp
    5865:	48 89 e5             	mov    %rsp,%rbp
    5868:	41 57                	push   %r15
    586a:	41 56                	push   %r14
    586c:	41 55                	push   %r13
    586e:	41 54                	push   %r12
    5870:	53                   	push   %rbx
    5871:	48 83 ec 28          	sub    $0x28,%rsp
    5875:	ff 15 6d 47 00 00    	call   *0x476d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  if (data->thread_index == data->task_index) {
    587b:	8b 07                	mov    (%rdi),%eax
int barriered_work(struct BarrierTask *data) {
    587d:	48 89 fb             	mov    %rdi,%rbx
  if (data->thread_index == data->task_index) {
    5880:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    5886:	0f 84 14 01 00 00    	je     59a0 <barriered_work+0x140>
    receive(data);
    588c:	e8 af fe ff ff       	call   5740 <receive>
  if (data->sending == 1) {
    5891:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    5898:	0f 85 0e 02 00 00    	jne    5aac <barriered_work+0x24c>
      for (int n = 0 ; n < data->thread_count; n++) {
    589e:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    58a4:	85 c0                	test   %eax,%eax
    58a6:	0f 8e 0c 02 00 00    	jle    5ab8 <barriered_work+0x258>
    58ac:	48 8d bb 80 01 00 00 	lea    0x180(%rbx),%rdi
    58b3:	45 31 ff             	xor    %r15d,%r15d
    58b6:	48 89 7d c8          	mov    %rdi,-0x38(%rbp)
    58ba:	48 8d bb 88 01 00 00 	lea    0x188(%rbx),%rdi
    58c1:	48 89 7d c0          	mov    %rdi,-0x40(%rbp)
    58c5:	0f 1f 00             	nopl   (%rax)
        if (n == data->thread_index) { continue; }
    58c8:	44 39 bb 30 01 00 00 	cmp    %r15d,0x130(%rbx)
    58cf:	0f 84 b7 00 00 00    	je     598c <barriered_work+0x12c>
        struct Data *them = data->mailboxes[n].higher;
    58d5:	4c 89 ff             	mov    %r15,%rdi
    58d8:	48 c1 e7 05          	shl    $0x5,%rdi
    58dc:	48 03 bb 68 01 00 00 	add    0x168(%rbx),%rdi
    58e3:	4c 8b 47 08          	mov    0x8(%rdi),%r8
        for (; them->messages_count < min;) {
    58e7:	4d 8b 50 08          	mov    0x8(%r8),%r10
    58eb:	49 63 70 10          	movslq 0x10(%r8),%rsi
    58ef:	49 39 f2             	cmp    %rsi,%r10
    58f2:	0f 8d 8b 00 00 00    	jge    5983 <barriered_work+0x123>
    58f8:	49 89 f1             	mov    %rsi,%r9
    58fb:	4c 8b b3 08 01 00 00 	mov    0x108(%rbx),%r14
    5902:	4c 8b 5f 10          	mov    0x10(%rdi),%r11
    5906:	4d 29 d1             	sub    %r10,%r9
          them->messages[them->messages_count++] = data->message; 
    5909:	49 8b 10             	mov    (%r8),%rdx
    590c:	49 8d 41 ff          	lea    -0x1(%r9),%rax
    5910:	48 83 f8 02          	cmp    $0x2,%rax
    5914:	0f 86 2e 02 00 00    	jbe    5b48 <barriered_work+0x2e8>
    591a:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    5922:	48 8d 0c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rcx
    592a:	4c 8d 24 02          	lea    (%rdx,%rax,1),%r12
    592e:	4c 8d 2c 0a          	lea    (%rdx,%rcx,1),%r13
    5932:	4c 39 6d c8          	cmp    %r13,-0x38(%rbp)
    5936:	0f 83 94 01 00 00    	jae    5ad0 <barriered_work+0x270>
    593c:	4c 8b 6d c0          	mov    -0x40(%rbp),%r13
    5940:	4d 39 ec             	cmp    %r13,%r12
    5943:	0f 83 87 01 00 00    	jae    5ad0 <barriered_work+0x270>
    5949:	4c 8d 14 02          	lea    (%rdx,%rax,1),%r10
    594d:	48 01 d1             	add    %rdx,%rcx
    5950:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5957:	49 83 c2 08          	add    $0x8,%r10
          them->messages[them->messages_count++] = data->message; 
    595b:	49 89 42 f8          	mov    %rax,-0x8(%r10)
        for (; them->messages_count < min;) {
    595f:	4c 39 d1             	cmp    %r10,%rcx
    5962:	75 ec                	jne    5950 <barriered_work+0xf0>
    5964:	0f 1f 40 00          	nopl   0x0(%rax)
    5968:	4b 8d 0c 0e          	lea    (%r14,%r9,1),%rcx
    596c:	4d 01 cb             	add    %r9,%r11
    596f:	48 89 8b 08 01 00 00 	mov    %rcx,0x108(%rbx)
    5976:	4c 89 5f 10          	mov    %r11,0x10(%rdi)
    597a:	49 89 70 08          	mov    %rsi,0x8(%r8)
    597e:	48 89 44 f2 f8       	mov    %rax,-0x8(%rdx,%rsi,8)
        asm volatile ("sfence" ::: "memory");
    5983:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5986:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    598c:	49 83 c7 01          	add    $0x1,%r15
    5990:	44 39 f8             	cmp    %r15d,%eax
    5993:	0f 8f 2f ff ff ff    	jg     58c8 <barriered_work+0x68>
    5999:	e9 1a 01 00 00       	jmp    5ab8 <barriered_work+0x258>
    599e:	66 90                	xchg   %ax,%ax
      receive(data);
    59a0:	e8 9b fd ff ff       	call   5740 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    59a5:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    59ac:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    59ae:	45 85 c9             	test   %r9d,%r9d
    59b1:	0f 8e 85 00 00 00    	jle    5a3c <barriered_work+0x1dc>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59b7:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    59be:	4c 63 d8             	movslq %eax,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    59c1:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59c4:	49 c1 e3 09          	shl    $0x9,%r11
    59c8:	4c 8b 52 10          	mov    0x10(%rdx),%r10
              int next_task = abs((t + 1) % (data->thread_count));
    59cc:	99                   	cltd
    59cd:	41 f7 f9             	idiv   %r9d
    59d0:	4c 89 d7             	mov    %r10,%rdi
    59d3:	4f 8d 2c ca          	lea    (%r10,%r9,8),%r13
    59d7:	89 d0                	mov    %edx,%eax
    59d9:	f7 d8                	neg    %eax
    59db:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59de:	45 31 c0             	xor    %r8d,%r8d
              int next_task = abs((t + 1) % (data->thread_count));
    59e1:	4c 63 e2             	movslq %edx,%r12
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59e4:	49 c1 e4 09          	shl    $0x9,%r12
    59e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    59f0:	31 c0                	xor    %eax,%eax
    59f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59f8:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    59fc:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    5a00:	4a 8b 8c 22 68 01 00 00 	mov    0x168(%rdx,%r12,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5a08:	48 8b 17             	mov    (%rdi),%rdx
    5a0b:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    5a0f:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5a12:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5a16:	48 c1 e2 05          	shl    $0x5,%rdx
    5a1a:	4a 03 94 1e 68 01 00 00 	add    0x168(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5a22:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    5a26:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    5a2a:	49 39 c1             	cmp    %rax,%r9
    5a2d:	75 c9                	jne    59f8 <barriered_work+0x198>
        for (int y = 0; y < data->thread_count ; y++) {
    5a2f:	48 83 c7 08          	add    $0x8,%rdi
    5a33:	49 83 c0 20          	add    $0x20,%r8
    5a37:	49 39 fd             	cmp    %rdi,%r13
    5a3a:	75 b4                	jne    59f0 <barriered_work+0x190>
      asm volatile ("sfence" ::: "memory");
    5a3c:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5a3f:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5a46:	31 ff                	xor    %edi,%edi
    5a48:	48 c1 e6 05          	shl    $0x5,%rsi
    5a4c:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5a53:	e8 d8 c8 ff ff       	call   2330 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5a58:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5a5f:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5a66:	31 ff                	xor    %edi,%edi
    int modcount = ++data->thread->protected_state->modcount;
    5a68:	48 8b 40 38          	mov    0x38(%rax),%rax
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5a6c:	48 c1 e6 05          	shl    $0x5,%rsi
    5a70:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5a77:	48 83 c6 10          	add    $0x10,%rsi
    int modcount = ++data->thread->protected_state->modcount;
    5a7b:	83 40 10 01          	addl   $0x1,0x10(%rax)
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5a7f:	e8 ac c8 ff ff       	call   2330 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5a84:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    5a8b:	48 83 c0 01          	add    $0x1,%rax
    5a8f:	48 99                	cqto
    5a91:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    5a98:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5a9f:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    5aa6:	0f 84 b1 00 00 00    	je     5b5d <barriered_work+0x2fd>
    5aac:	48 8d 3d 51 17 00 00 	lea    0x1751(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5ab3:	e8 58 c8 ff ff       	call   2310 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5ab8:	0f ae f8             	sfence
}
    5abb:	48 83 c4 28          	add    $0x28,%rsp
    5abf:	31 c0                	xor    %eax,%eax
    5ac1:	5b                   	pop    %rbx
    5ac2:	41 5c                	pop    %r12
    5ac4:	41 5d                	pop    %r13
    5ac6:	41 5e                	pop    %r14
    5ac8:	41 5f                	pop    %r15
    5aca:	5d                   	pop    %rbp
    5acb:	c3                   	ret
    5acc:	0f 1f 40 00          	nopl   0x0(%rax)
    5ad0:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5ad7:	4d 89 cd             	mov    %r9,%r13
    5ada:	4c 89 e1             	mov    %r12,%rcx
    5add:	49 d1 ed             	shr    %r13
    5ae0:	49 c1 e5 04          	shl    $0x4,%r13
    5ae4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5ae9:	4c 89 6d b8          	mov    %r13,-0x48(%rbp)
    5aed:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5af1:	4d 01 e5             	add    %r12,%r13
    5af4:	f6 45 b8 10          	testb  $0x10,-0x48(%rbp)
    5af8:	74 16                	je     5b10 <barriered_work+0x2b0>
          them->messages[them->messages_count++] = data->message; 
    5afa:	48 83 c1 10          	add    $0x10,%rcx
    5afe:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5b03:	4c 39 e9             	cmp    %r13,%rcx
    5b06:	74 18                	je     5b20 <barriered_work+0x2c0>
    5b08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          them->messages[them->messages_count++] = data->message; 
    5b10:	0f 11 01             	movups %xmm0,(%rcx)
    5b13:	48 83 c1 20          	add    $0x20,%rcx
    5b17:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
        for (; them->messages_count < min;) {
    5b1b:	4c 39 e9             	cmp    %r13,%rcx
    5b1e:	75 f0                	jne    5b10 <barriered_work+0x2b0>
    5b20:	4c 89 c9             	mov    %r9,%rcx
    5b23:	48 83 e1 fe          	and    $0xfffffffffffffffe,%rcx
    5b27:	4c 01 d1             	add    %r10,%rcx
    5b2a:	41 f6 c1 01          	test   $0x1,%r9b
    5b2e:	0f 84 34 fe ff ff    	je     5968 <barriered_work+0x108>
          them->messages[them->messages_count++] = data->message; 
    5b34:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b3b:	48 89 04 ca          	mov    %rax,(%rdx,%rcx,8)
        for (; them->messages_count < min;) {
    5b3f:	e9 24 fe ff ff       	jmp    5968 <barriered_work+0x108>
    5b44:	0f 1f 40 00          	nopl   0x0(%rax)
    5b48:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    5b50:	48 8d 0c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rcx
    5b58:	e9 ec fd ff ff       	jmp    5949 <barriered_work+0xe9>
      for (int n = 0 ; n < data->thread_count; n++) {
    5b5d:	48 8d bb 80 01 00 00 	lea    0x180(%rbx),%rdi
    5b64:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5b6a:	45 31 ff             	xor    %r15d,%r15d
    5b6d:	48 89 7d c8          	mov    %rdi,-0x38(%rbp)
    5b71:	48 8d bb 88 01 00 00 	lea    0x188(%rbx),%rdi
    5b78:	48 89 7d c0          	mov    %rdi,-0x40(%rbp)
    5b7c:	85 c0                	test   %eax,%eax
    5b7e:	0f 8e 34 ff ff ff    	jle    5ab8 <barriered_work+0x258>
    5b84:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5b88:	44 39 bb 30 01 00 00 	cmp    %r15d,0x130(%rbx)
    5b8f:	0f 84 b7 00 00 00    	je     5c4c <barriered_work+0x3ec>
        struct Data *them = data->mailboxes[n].higher;
    5b95:	4c 89 ff             	mov    %r15,%rdi
    5b98:	48 c1 e7 05          	shl    $0x5,%rdi
    5b9c:	48 03 bb 68 01 00 00 	add    0x168(%rbx),%rdi
    5ba3:	4c 8b 47 08          	mov    0x8(%rdi),%r8
        for (; them->messages_count < min;) {
    5ba7:	4d 8b 50 08          	mov    0x8(%r8),%r10
    5bab:	49 63 70 10          	movslq 0x10(%r8),%rsi
    5baf:	49 39 f2             	cmp    %rsi,%r10
    5bb2:	0f 8d 8b 00 00 00    	jge    5c43 <barriered_work+0x3e3>
    5bb8:	49 89 f1             	mov    %rsi,%r9
    5bbb:	4c 8b b3 08 01 00 00 	mov    0x108(%rbx),%r14
    5bc2:	4c 8b 5f 10          	mov    0x10(%rdi),%r11
    5bc6:	4d 29 d1             	sub    %r10,%r9
          them->messages[them->messages_count++] = data->message; 
    5bc9:	49 8b 10             	mov    (%r8),%rdx
    5bcc:	49 8d 41 ff          	lea    -0x1(%r9),%rax
    5bd0:	48 83 f8 02          	cmp    $0x2,%rax
    5bd4:	0f 86 fe 00 00 00    	jbe    5cd8 <barriered_work+0x478>
    5bda:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    5be2:	48 8d 0c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rcx
    5bea:	4c 8d 24 02          	lea    (%rdx,%rax,1),%r12
    5bee:	4c 8d 2c 0a          	lea    (%rdx,%rcx,1),%r13
    5bf2:	4c 39 6d c8          	cmp    %r13,-0x38(%rbp)
    5bf6:	73 68                	jae    5c60 <barriered_work+0x400>
    5bf8:	4c 8b 6d c0          	mov    -0x40(%rbp),%r13
    5bfc:	4d 39 ec             	cmp    %r13,%r12
    5bff:	73 5f                	jae    5c60 <barriered_work+0x400>
    5c01:	4c 8d 14 02          	lea    (%rdx,%rax,1),%r10
    5c05:	48 01 d1             	add    %rdx,%rcx
    5c08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5c10:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5c17:	49 83 c2 08          	add    $0x8,%r10
          them->messages[them->messages_count++] = data->message; 
    5c1b:	49 89 42 f8          	mov    %rax,-0x8(%r10)
        for (; them->messages_count < min;) {
    5c1f:	49 39 ca             	cmp    %rcx,%r10
    5c22:	75 ec                	jne    5c10 <barriered_work+0x3b0>
    5c24:	0f 1f 40 00          	nopl   0x0(%rax)
    5c28:	4b 8d 0c 0e          	lea    (%r14,%r9,1),%rcx
    5c2c:	4d 01 cb             	add    %r9,%r11
    5c2f:	48 89 8b 08 01 00 00 	mov    %rcx,0x108(%rbx)
    5c36:	4c 89 5f 10          	mov    %r11,0x10(%rdi)
    5c3a:	49 89 70 08          	mov    %rsi,0x8(%r8)
    5c3e:	48 89 44 f2 f8       	mov    %rax,-0x8(%rdx,%rsi,8)
        asm volatile ("sfence" ::: "memory");
    5c43:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5c46:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5c4c:	49 83 c7 01          	add    $0x1,%r15
    5c50:	44 39 f8             	cmp    %r15d,%eax
    5c53:	0f 8f 2f ff ff ff    	jg     5b88 <barriered_work+0x328>
    5c59:	e9 5a fe ff ff       	jmp    5ab8 <barriered_work+0x258>
    5c5e:	66 90                	xchg   %ax,%ax
    5c60:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5c67:	4d 89 cd             	mov    %r9,%r13
    5c6a:	4c 89 e1             	mov    %r12,%rcx
    5c6d:	49 d1 ed             	shr    %r13
    5c70:	49 c1 e5 04          	shl    $0x4,%r13
    5c74:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5c79:	4c 89 6d b8          	mov    %r13,-0x48(%rbp)
    5c7d:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5c81:	4d 01 e5             	add    %r12,%r13
    5c84:	f6 45 b8 10          	testb  $0x10,-0x48(%rbp)
    5c88:	74 16                	je     5ca0 <barriered_work+0x440>
          them->messages[them->messages_count++] = data->message; 
    5c8a:	48 83 c1 10          	add    $0x10,%rcx
    5c8e:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5c93:	4c 39 e9             	cmp    %r13,%rcx
    5c96:	74 18                	je     5cb0 <barriered_work+0x450>
    5c98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          them->messages[them->messages_count++] = data->message; 
    5ca0:	0f 11 01             	movups %xmm0,(%rcx)
    5ca3:	48 83 c1 20          	add    $0x20,%rcx
    5ca7:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
        for (; them->messages_count < min;) {
    5cab:	4c 39 e9             	cmp    %r13,%rcx
    5cae:	75 f0                	jne    5ca0 <barriered_work+0x440>
    5cb0:	4c 89 c9             	mov    %r9,%rcx
    5cb3:	48 83 e1 fe          	and    $0xfffffffffffffffe,%rcx
    5cb7:	4c 01 d1             	add    %r10,%rcx
    5cba:	41 f6 c1 01          	test   $0x1,%r9b
    5cbe:	0f 84 64 ff ff ff    	je     5c28 <barriered_work+0x3c8>
          them->messages[them->messages_count++] = data->message; 
    5cc4:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5ccb:	48 89 04 ca          	mov    %rax,(%rdx,%rcx,8)
        for (; them->messages_count < min;) {
    5ccf:	e9 54 ff ff ff       	jmp    5c28 <barriered_work+0x3c8>
    5cd4:	0f 1f 40 00          	nopl   0x0(%rax)
    5cd8:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    5ce0:	48 8d 0c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rcx
    5ce8:	e9 14 ff ff ff       	jmp    5c01 <barriered_work+0x3a1>
    5ced:	0f 1f 00             	nopl   (%rax)

0000000000005cf0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5cf0:	f3 0f 1e fa          	endbr64
    5cf4:	55                   	push   %rbp
    5cf5:	48 89 e5             	mov    %rsp,%rbp
    5cf8:	ff 15 ea 42 00 00    	call   *0x42ea(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5cfe:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5d05:	48 8b 40 40          	mov    0x40(%rax),%rax
    5d09:	48 63 10             	movslq (%rax),%rdx
    5d0c:	85 d2                	test   %edx,%edx
    5d0e:	7e 2e                	jle    5d3e <barriered_work_ingest+0x4e>
    5d10:	48 8b 40 08          	mov    0x8(%rax),%rax
    5d14:	48 c1 e2 04          	shl    $0x4,%rdx
    5d18:	48 01 c2             	add    %rax,%rdx
    5d1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread->buffers->buffer[x].available == 1) {
    5d20:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5d24:	75 0f                	jne    5d35 <barriered_work_ingest+0x45>
      data->ingest_count++;
    5d26:	48 83 87 60 01 00 00 01 	addq   $0x1,0x160(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5d2e:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5d35:	48 83 c0 10          	add    $0x10,%rax
    5d39:	48 39 d0             	cmp    %rdx,%rax
    5d3c:	75 e2                	jne    5d20 <barriered_work_ingest+0x30>
  asm volatile ("sfence" ::: "memory");
    5d3e:	0f ae f8             	sfence
  barriered_work(data);
    5d41:	e8 1a fb ff ff       	call   5860 <barriered_work>
}
    5d46:	31 c0                	xor    %eax,%eax
    5d48:	5d                   	pop    %rbp
    5d49:	c3                   	ret
    5d4a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005d50 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5d50:	f3 0f 1e fa          	endbr64
    5d54:	55                   	push   %rbp
    5d55:	48 89 e5             	mov    %rsp,%rbp
    5d58:	ff 15 8a 42 00 00    	call   *0x428a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
}
    5d5e:	31 c0                	xor    %eax,%eax
    5d60:	5d                   	pop    %rbp
    5d61:	c3                   	ret
    5d62:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5d6d:	0f 1f 00             	nopl   (%rax)

0000000000005d70 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5d70:	f3 0f 1e fa          	endbr64
    5d74:	55                   	push   %rbp
    5d75:	48 89 e5             	mov    %rsp,%rbp
    5d78:	ff 15 6a 42 00 00    	call   *0x426a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    5d7e:	31 c0                	xor    %eax,%eax
    5d80:	5d                   	pop    %rbp
    5d81:	c3                   	ret
    5d82:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5d8d:	0f 1f 00             	nopl   (%rax)

0000000000005d90 <after>:
int after(struct timespec left, struct timespec right) {
    5d90:	f3 0f 1e fa          	endbr64
    5d94:	55                   	push   %rbp
    5d95:	48 89 e5             	mov    %rsp,%rbp
    5d98:	ff 15 4a 42 00 00    	call   *0x424a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  return left.tv_sec > right.tv_sec &&
    5d9e:	31 c0                	xor    %eax,%eax
    5da0:	48 39 d7             	cmp    %rdx,%rdi
    5da3:	7e 08                	jle    5dad <after+0x1d>
    5da5:	31 c0                	xor    %eax,%eax
    5da7:	48 39 ce             	cmp    %rcx,%rsi
    5daa:	0f 9f c0             	setg   %al
}
    5dad:	5d                   	pop    %rbp
    5dae:	c3                   	ret
    5daf:	90                   	nop

0000000000005db0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5db0:	f3 0f 1e fa          	endbr64
    5db4:	55                   	push   %rbp
    5db5:	48 89 e5             	mov    %rsp,%rbp
    5db8:	ff 15 2a 42 00 00    	call   *0x422a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  return 0;
    5dbe:	31 c0                	xor    %eax,%eax
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5dc0:	4c 8b 5d 10          	mov    0x10(%rbp),%r11
    5dc4:	4c 8b 55 18          	mov    0x18(%rbp),%r10
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5dc8:	48 39 d7             	cmp    %rdx,%rdi
    5dcb:	7f 18                	jg     5de5 <within+0x35>
    5dcd:	4d 39 d8             	cmp    %r11,%r8
    5dd0:	0f 9e c2             	setle  %dl
    5dd3:	48 39 ce             	cmp    %rcx,%rsi
    5dd6:	0f 9e c0             	setle  %al
    5dd9:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5ddb:	31 c0                	xor    %eax,%eax
    5ddd:	4d 39 d1             	cmp    %r10,%r9
    5de0:	0f 9e c0             	setle  %al
    5de3:	21 d0                	and    %edx,%eax
}
    5de5:	5d                   	pop    %rbp
    5de6:	c3                   	ret
    5de7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005df0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5df0:	f3 0f 1e fa          	endbr64
    5df4:	55                   	push   %rbp
    5df5:	48 89 e5             	mov    %rsp,%rbp
    5df8:	ff 15 ea 41 00 00    	call   *0x41ea(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    5dfe:	48 8b 7d 10          	mov    0x10(%rbp),%rdi
    5e02:	48 8b 75 30          	mov    0x30(%rbp),%rsi
    5e06:	4c 8b 4d 20          	mov    0x20(%rbp),%r9
    5e0a:	4c 8b 55 28          	mov    0x28(%rbp),%r10
    5e0e:	4c 8b 45 40          	mov    0x40(%rbp),%r8
    5e12:	4c 8b 5d 48          	mov    0x48(%rbp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5e16:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
    5e1a:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  return left.tv_sec > right.tv_sec &&
    5e1e:	48 39 fe             	cmp    %rdi,%rsi
    5e21:	7d 2d                	jge    5e50 <overlap+0x60>
    5e23:	48 39 ca             	cmp    %rcx,%rdx
    5e26:	7d 60                	jge    5e88 <overlap+0x98>
    5e28:	4d 39 da             	cmp    %r11,%r10
    5e2b:	7d 0a                	jge    5e37 <overlap+0x47>
    return 1;
    5e2d:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e32:	4d 39 c1             	cmp    %r8,%r9
    5e35:	7c 0f                	jl     5e46 <overlap+0x56>
  return 0;
    5e37:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e39:	4d 39 c1             	cmp    %r8,%r9
    5e3c:	7f 08                	jg     5e46 <overlap+0x56>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e3e:	31 c0                	xor    %eax,%eax
    5e40:	4d 39 da             	cmp    %r11,%r10
    5e43:	0f 9e c0             	setle  %al
}
    5e46:	5d                   	pop    %rbp
    5e47:	c3                   	ret
    5e48:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5e50:	7e 56                	jle    5ea8 <overlap+0xb8>
    5e52:	48 39 ca             	cmp    %rcx,%rdx
    5e55:	7f 39                	jg     5e90 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e57:	75 31                	jne    5e8a <overlap+0x9a>
    5e59:	4d 39 c1             	cmp    %r8,%r9
    5e5c:	7c 2c                	jl     5e8a <overlap+0x9a>
    return 1;
    5e5e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e63:	4d 39 da             	cmp    %r11,%r10
    5e66:	7d de                	jge    5e46 <overlap+0x56>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e68:	48 39 ca             	cmp    %rcx,%rdx
}
    5e6b:	5d                   	pop    %rbp
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e6c:	0f 94 c2             	sete   %dl
    5e6f:	48 39 fe             	cmp    %rdi,%rsi
    5e72:	0f 94 c0             	sete   %al
    5e75:	21 c2                	and    %eax,%edx
    5e77:	31 c0                	xor    %eax,%eax
    5e79:	4d 39 c1             	cmp    %r8,%r9
    5e7c:	0f 94 c0             	sete   %al
    5e7f:	21 d0                	and    %edx,%eax
}
    5e81:	c3                   	ret
    5e82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e88:	74 ad                	je     5e37 <overlap+0x47>
  return 0;
    5e8a:	31 c0                	xor    %eax,%eax
}
    5e8c:	5d                   	pop    %rbp
    5e8d:	c3                   	ret
    5e8e:	66 90                	xchg   %ax,%ax
  return left.tv_sec > right.tv_sec &&
    5e90:	4d 39 da             	cmp    %r11,%r10
    5e93:	7e c4                	jle    5e59 <overlap+0x69>
    return 1;
    5e95:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e9a:	4d 39 c1             	cmp    %r8,%r9
    5e9d:	7e ba                	jle    5e59 <overlap+0x69>
    5e9f:	eb a5                	jmp    5e46 <overlap+0x56>
    5ea1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ea8:	48 39 ca             	cmp    %rcx,%rdx
    5eab:	7c 8a                	jl     5e37 <overlap+0x47>
    5ead:	4d 39 c1             	cmp    %r8,%r9
    5eb0:	7d ac                	jge    5e5e <overlap+0x6e>
    5eb2:	48 39 ca             	cmp    %rcx,%rdx
    5eb5:	74 87                	je     5e3e <overlap+0x4e>
  return 0;
    5eb7:	31 c0                	xor    %eax,%eax
    5eb9:	eb d1                	jmp    5e8c <overlap+0x9c>
    5ebb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005ec0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5ec0:	f3 0f 1e fa          	endbr64
    5ec4:	55                   	push   %rbp
    5ec5:	48 89 e5             	mov    %rsp,%rbp
    5ec8:	41 57                	push   %r15
    5eca:	41 56                	push   %r14
    5ecc:	41 55                	push   %r13
    5ece:	41 54                	push   %r12
    5ed0:	53                   	push   %rbx
    5ed1:	48 83 ec 58          	sub    $0x58,%rsp
    5ed5:	ff 15 0d 41 00 00    	call   *0x410d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    5edb:	41 89 f4             	mov    %esi,%r12d
  for (int x = 0 ; x < thread_count; x++) {
    5ede:	85 f6                	test   %esi,%esi
    5ee0:	0f 8e df 02 00 00    	jle    61c5 <verify+0x305>
    5ee6:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5eea:	45 31 ff             	xor    %r15d,%r15d
    5eed:	48 89 5d b8          	mov    %rbx,-0x48(%rbp)
    for (int z = 0 ; z < thread_count; z++) {
    5ef1:	48 89 5d c0          	mov    %rbx,-0x40(%rbp)
    5ef5:	45 31 ed             	xor    %r13d,%r13d
    5ef8:	45 89 e6             	mov    %r12d,%r14d
      if (z != x)  {
    5efb:	45 39 ef             	cmp    %r13d,%r15d
    5efe:	0f 84 27 02 00 00    	je     612b <verify+0x26b>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5f04:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    5f08:	8b 50 08             	mov    0x8(%rax),%edx
    5f0b:	85 d2                	test   %edx,%edx
    5f0d:	0f 8e 18 02 00 00    	jle    612b <verify+0x26b>
    5f13:	48 89 5d 98          	mov    %rbx,-0x68(%rbp)
    5f17:	45 31 e4             	xor    %r12d,%r12d
    5f1a:	44 89 6d 94          	mov    %r13d,-0x6c(%rbp)
    5f1e:	44 89 75 90          	mov    %r14d,-0x70(%rbp)
    5f22:	4d 89 e6             	mov    %r12,%r14
    5f25:	44 89 fa             	mov    %r15d,%edx
    5f28:	48 8d 35 e1 12 00 00 	lea    0x12e1(%rip),%rsi        # 7210 <_IO_stdin_used+0x210>
    5f2f:	bf 01 00 00 00       	mov    $0x1,%edi
    5f34:	31 c0                	xor    %eax,%eax
    5f36:	e8 45 c5 ff ff       	call   2480 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5f3b:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    5f3f:	8b 40 08             	mov    0x8(%rax),%eax
    5f42:	85 c0                	test   %eax,%eax
    5f44:	0f 8e c3 01 00 00    	jle    610d <verify+0x24d>
    5f4a:	4c 89 f0             	mov    %r14,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5f4d:	4c 89 75 88          	mov    %r14,-0x78(%rbp)
    5f51:	31 db                	xor    %ebx,%ebx
    5f53:	48 c1 e0 09          	shl    $0x9,%rax
    5f57:	44 89 7d 84          	mov    %r15d,-0x7c(%rbp)
    5f5b:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    5f5f:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    5f63:	4c 8b 08             	mov    (%rax),%r9
    5f66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5f70:	4c 8b 65 c0          	mov    -0x40(%rbp),%r12
    5f74:	4c 8b 7d c8          	mov    -0x38(%rbp),%r15
    5f78:	49 89 de             	mov    %rbx,%r14
    5f7b:	bf 01 00 00 00       	mov    $0x1,%edi
    5f80:	49 c1 e6 09          	shl    $0x9,%r14
    5f84:	48 8d 35 9a 12 00 00 	lea    0x129a(%rip),%rsi        # 7225 <_IO_stdin_used+0x225>
    5f8b:	49 8b 04 24          	mov    (%r12),%rax
    5f8f:	4b 8b 8c 39 58 01 00 00 	mov    0x158(%r9,%r15,1),%rcx
    5f97:	4c 89 75 a8          	mov    %r14,-0x58(%rbp)
    5f9b:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    5fa3:	31 c0                	xor    %eax,%eax
    5fa5:	e8 d6 c4 ff ff       	call   2480 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5faa:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    5fae:	4c 8b 08             	mov    (%rax),%r9
    5fb1:	4b 83 bc 39 58 01 00 00 00 	cmpq   $0x0,0x158(%r9,%r15,1)
    5fba:	0f 8e 34 01 00 00    	jle    60f4 <verify+0x234>
    5fc0:	4d 03 34 24          	add    (%r12),%r14
    5fc4:	48 89 5d a0          	mov    %rbx,-0x60(%rbp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5fc8:	ba 01 00 00 00       	mov    $0x1,%edx
    5fcd:	4d 89 f5             	mov    %r14,%r13
    5fd0:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    5fd7:	4d 85 f6             	test   %r14,%r14
    5fda:	0f 8e 10 01 00 00    	jle    60f0 <verify+0x230>
    5fe0:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5fe4:	49 89 d4             	mov    %rdx,%r12
    5fe7:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
    5feb:	31 db                	xor    %ebx,%ebx
    5fed:	49 c1 e4 05          	shl    $0x5,%r12
    5ff1:	49 83 ec 20          	sub    $0x20,%r12
    5ff5:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
    5ff9:	eb 32                	jmp    602d <verify+0x16d>
    5ffb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6000:	4c 39 c1             	cmp    %r8,%rcx
    6003:	0f 8d 47 01 00 00    	jge    6150 <verify+0x290>
    6009:	4c 39 d7             	cmp    %r10,%rdi
    600c:	7e 05                	jle    6013 <verify+0x153>
    600e:	49 39 c3             	cmp    %rax,%r11
    6011:	7c 75                	jl     6088 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6013:	4c 39 d7             	cmp    %r10,%rdi
    6016:	0f 8d 9b 01 00 00    	jge    61b7 <verify+0x2f7>
    601c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6020:	48 83 c3 01          	add    $0x1,%rbx
    6024:	49 39 de             	cmp    %rbx,%r14
    6027:	0f 8e a2 00 00 00    	jle    60cf <verify+0x20f>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    602d:	49 8b 8f 48 01 00 00 	mov    0x148(%r15),%rcx
    6034:	48 89 d8             	mov    %rbx,%rax
    6037:	48 c1 e0 05          	shl    $0x5,%rax
    603b:	49 03 85 48 01 00 00 	add    0x148(%r13),%rax
    6042:	4c 01 e1             	add    %r12,%rcx
    6045:	48 8b 30             	mov    (%rax),%rsi
    6048:	48 8b 78 10          	mov    0x10(%rax),%rdi
    604c:	48 8b 11             	mov    (%rcx),%rdx
    604f:	4c 8b 41 08          	mov    0x8(%rcx),%r8
    6053:	4c 8b 51 10          	mov    0x10(%rcx),%r10
    6057:	4c 8b 59 18          	mov    0x18(%rcx),%r11
    605b:	48 8b 48 08          	mov    0x8(%rax),%rcx
    605f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6063:	48 39 d6             	cmp    %rdx,%rsi
    6066:	7c 98                	jl     6000 <verify+0x140>
    6068:	0f 8e 32 01 00 00    	jle    61a0 <verify+0x2e0>
    606e:	4c 39 c1             	cmp    %r8,%rcx
    6071:	0f 8f e9 00 00 00    	jg     6160 <verify+0x2a0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6077:	75 a7                	jne    6020 <verify+0x160>
    6079:	4c 39 d7             	cmp    %r10,%rdi
    607c:	7f a2                	jg     6020 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    607e:	49 39 c3             	cmp    %rax,%r11
    6081:	7c 9d                	jl     6020 <verify+0x160>
    6083:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6088:	49 89 c1             	mov    %rax,%r9
    608b:	48 89 f9             	mov    %rdi,%rcx
    608e:	48 8d 35 e3 13 00 00 	lea    0x13e3(%rip),%rsi        # 7478 <_IO_stdin_used+0x478>
    6095:	31 c0                	xor    %eax,%eax
    6097:	bf 01 00 00 00       	mov    $0x1,%edi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    609c:	48 83 c3 01          	add    $0x1,%rbx
    60a0:	e8 db c3 ff ff       	call   2480 <__printf_chk@plt>
    60a5:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    60a9:	4c 8b 6d a8          	mov    -0x58(%rbp),%r13
    60ad:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60b0:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60b4:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60bb:	4c 8b 08             	mov    (%rax),%r9
    60be:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    60c2:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60c6:	49 39 de             	cmp    %rbx,%r14
    60c9:	0f 8f 5e ff ff ff    	jg     602d <verify+0x16d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60cf:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    60d3:	49 3b 97 58 01 00 00 	cmp    0x158(%r15),%rdx
    60da:	7d 14                	jge    60f0 <verify+0x230>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60dc:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    60e3:	48 83 c2 01          	add    $0x1,%rdx
    60e7:	4d 85 f6             	test   %r14,%r14
    60ea:	0f 8f f0 fe ff ff    	jg     5fe0 <verify+0x120>
    60f0:	48 8b 5d a0          	mov    -0x60(%rbp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    60f4:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    60f8:	48 83 c3 01          	add    $0x1,%rbx
    60fc:	39 58 08             	cmp    %ebx,0x8(%rax)
    60ff:	0f 8f 6b fe ff ff    	jg     5f70 <verify+0xb0>
    6105:	4c 8b 75 88          	mov    -0x78(%rbp),%r14
    6109:	44 8b 7d 84          	mov    -0x7c(%rbp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    610d:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    6111:	49 83 c6 01          	add    $0x1,%r14
    6115:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    6119:	0f 8f 06 fe ff ff    	jg     5f25 <verify+0x65>
    611f:	48 8b 5d 98          	mov    -0x68(%rbp),%rbx
    6123:	44 8b 6d 94          	mov    -0x6c(%rbp),%r13d
    6127:	44 8b 75 90          	mov    -0x70(%rbp),%r14d
    for (int z = 0 ; z < thread_count; z++) {
    612b:	41 8d 45 01          	lea    0x1(%r13),%eax
    612f:	48 81 45 c0 b0 00 00 00 	addq   $0xb0,-0x40(%rbp)
    6137:	41 39 c6             	cmp    %eax,%r14d
    613a:	0f 84 96 00 00 00    	je     61d6 <verify+0x316>
    6140:	41 89 c5             	mov    %eax,%r13d
    6143:	e9 b3 fd ff ff       	jmp    5efb <verify+0x3b>
    6148:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6150:	0f 85 ca fe ff ff    	jne    6020 <verify+0x160>
    6156:	e9 b8 fe ff ff       	jmp    6013 <verify+0x153>
    615b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6160:	49 39 c3             	cmp    %rax,%r11
    6163:	7e 09                	jle    616e <verify+0x2ae>
    6165:	4c 39 d7             	cmp    %r10,%rdi
    6168:	0f 8c 1a ff ff ff    	jl     6088 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    616e:	4c 39 d7             	cmp    %r10,%rdi
    6171:	0f 8f a9 fe ff ff    	jg     6020 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6177:	49 39 c3             	cmp    %rax,%r11
    617a:	0f 8d 08 ff ff ff    	jge    6088 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6180:	48 39 d6             	cmp    %rdx,%rsi
    6183:	0f 85 97 fe ff ff    	jne    6020 <verify+0x160>
    6189:	4c 39 c1             	cmp    %r8,%rcx
    618c:	0f 85 8e fe ff ff    	jne    6020 <verify+0x160>
    6192:	4c 39 d7             	cmp    %r10,%rdi
    6195:	0f 84 ed fe ff ff    	je     6088 <verify+0x1c8>
    619b:	e9 80 fe ff ff       	jmp    6020 <verify+0x160>
    61a0:	4c 39 c1             	cmp    %r8,%rcx
    61a3:	0f 8c 6a fe ff ff    	jl     6013 <verify+0x153>
    61a9:	4c 39 d7             	cmp    %r10,%rdi
    61ac:	7e c9                	jle    6177 <verify+0x2b7>
    61ae:	4c 39 c1             	cmp    %r8,%rcx
    61b1:	0f 85 69 fe ff ff    	jne    6020 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    61b7:	49 39 c3             	cmp    %rax,%r11
    61ba:	0f 8f 60 fe ff ff    	jg     6020 <verify+0x160>
    61c0:	e9 c3 fe ff ff       	jmp    6088 <verify+0x1c8>
}
    61c5:	48 83 c4 58          	add    $0x58,%rsp
    61c9:	31 c0                	xor    %eax,%eax
    61cb:	5b                   	pop    %rbx
    61cc:	41 5c                	pop    %r12
    61ce:	41 5d                	pop    %r13
    61d0:	41 5e                	pop    %r14
    61d2:	41 5f                	pop    %r15
    61d4:	5d                   	pop    %rbp
    61d5:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
    61d6:	48 81 45 b8 b0 00 00 00 	addq   $0xb0,-0x48(%rbp)
    61de:	45 89 f4             	mov    %r14d,%r12d
    61e1:	41 8d 57 01          	lea    0x1(%r15),%edx
    61e5:	45 39 ef             	cmp    %r13d,%r15d
    61e8:	74 db                	je     61c5 <verify+0x305>
    61ea:	41 89 d7             	mov    %edx,%r15d
    61ed:	e9 ff fc ff ff       	jmp    5ef1 <verify+0x31>
    61f2:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    61fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006200 <atexit>:
    6200:	f3 0f 1e fa          	endbr64
    6204:	48 8b 15 fd 3d 00 00 	mov    0x3dfd(%rip),%rdx        # a008 <__dso_handle>
    620b:	31 f6                	xor    %esi,%esi
    620d:	e9 be c2 ff ff       	jmp    24d0 <__cxa_atexit@plt>
    6212:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    621c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006220 <__stack_chk_fail_local>:
    6220:	f3 0f 1e fa          	endbr64
    6224:	50                   	push   %rax
    6225:	58                   	pop    %rax
    6226:	48 83 ec 08          	sub    $0x8,%rsp
    622a:	e8 21 c1 ff ff       	call   2350 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000006230 <_fini>:
    6230:	f3 0f 1e fa          	endbr64
    6234:	48 83 ec 08          	sub    $0x8,%rsp
    6238:	48 83 c4 08          	add    $0x8,%rsp
    623c:	c3                   	ret
