
multibarrier:     file format elf64-x86-64


Disassembly of section .init:

0000000000002000 <_init>:
    2000:	f3 0f 1e fa          	endbr64
    2004:	48 83 ec 08          	sub    $0x8,%rsp
    2008:	48 8d 05 21 15 00 00 	lea    0x1521(%rip),%rax        # 3530 <__gmon_start__>
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
    264e:	48 8d 3d 5b 4e 00 00 	lea    0x4e5b(%rip),%rdi        # 74b0 <_IO_stdin_used+0x4b0>
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    2655:	45 31 ed             	xor    %r13d,%r13d
    2658:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2661:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    2665:	48 8d 05 34 10 00 00 	lea    0x1034(%rip),%rax        # 36a0 <barriered_reset>
    266c:	66 48 0f 6e e8       	movq   %rax,%xmm5
    2671:	0f 16 2d e8 75 00 00 	movhps 0x75e8(%rip),%xmm5        # 9c60 <__do_global_dtors_aux_fini_array_entry+0x8>
    2678:	0f 29 ad 70 ff ff ff 	movaps %xmm5,-0x90(%rbp)
    267f:	e8 8c fc ff ff       	call   2310 <puts@plt>
    2684:	bf 0a 00 00 00       	mov    $0xa,%edi
    2689:	e8 62 fc ff ff       	call   22f0 <putchar@plt>
    268e:	48 8d 3d a9 4b 00 00 	lea    0x4ba9(%rip),%rdi        # 723e <_IO_stdin_used+0x23e>
    2695:	e8 76 fc ff ff       	call   2310 <puts@plt>
    269a:	ba 06 00 00 00       	mov    $0x6,%edx
    269f:	48 8d 35 b4 4b 00 00 	lea    0x4bb4(%rip),%rsi        # 725a <_IO_stdin_used+0x25a>
    26a6:	31 c0                	xor    %eax,%eax
    26a8:	bf 01 00 00 00       	mov    $0x1,%edi
    26ad:	e8 ce fd ff ff       	call   2480 <__printf_chk@plt>
    26b2:	ba 09 00 00 00       	mov    $0x9,%edx
    26b7:	48 8d 35 b6 4b 00 00 	lea    0x4bb6(%rip),%rsi        # 7274 <_IO_stdin_used+0x274>
    26be:	31 c0                	xor    %eax,%eax
    26c0:	bf 01 00 00 00       	mov    $0x1,%edi
    26c5:	e8 b6 fd ff ff       	call   2480 <__printf_chk@plt>
    26ca:	ba 01 00 00 00       	mov    $0x1,%edx
    26cf:	48 8d 35 b2 4b 00 00 	lea    0x4bb2(%rip),%rsi        # 7288 <_IO_stdin_used+0x288>
    26d6:	31 c0                	xor    %eax,%eax
    26d8:	bf 01 00 00 00       	mov    $0x1,%edi
    26dd:	e8 9e fd ff ff       	call   2480 <__printf_chk@plt>
    26e2:	ba 01 00 00 00       	mov    $0x1,%edx
    26e7:	48 8d 35 ab 4b 00 00 	lea    0x4bab(%rip),%rsi        # 7299 <_IO_stdin_used+0x299>
    26ee:	31 c0                	xor    %eax,%eax
    26f0:	bf 01 00 00 00       	mov    $0x1,%edi
    26f5:	e8 86 fd ff ff       	call   2480 <__printf_chk@plt>
    26fa:	ba 01 00 00 00       	mov    $0x1,%edx
    26ff:	48 8d 35 ab 4b 00 00 	lea    0x4bab(%rip),%rsi        # 72b1 <_IO_stdin_used+0x2b1>
    2706:	31 c0                	xor    %eax,%eax
    2708:	bf 01 00 00 00       	mov    $0x1,%edi
    270d:	e8 6e fd ff ff       	call   2480 <__printf_chk@plt>
    2712:	ba 01 00 00 00       	mov    $0x1,%edx
    2717:	48 8d 35 fa 4d 00 00 	lea    0x4dfa(%rip),%rsi        # 7518 <_IO_stdin_used+0x518>
    271e:	31 c0                	xor    %eax,%eax
    2720:	bf 01 00 00 00       	mov    $0x1,%edi
    2725:	e8 56 fd ff ff       	call   2480 <__printf_chk@plt>
    272a:	ba 01 00 00 00       	mov    $0x1,%edx
    272f:	48 8d 35 12 4e 00 00 	lea    0x4e12(%rip),%rsi        # 7548 <_IO_stdin_used+0x548>
    2736:	31 c0                	xor    %eax,%eax
    2738:	bf 01 00 00 00       	mov    $0x1,%edi
    273d:	e8 3e fd ff ff       	call   2480 <__printf_chk@plt>
    2742:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2747:	48 8d 35 7f 4b 00 00 	lea    0x4b7f(%rip),%rsi        # 72cd <_IO_stdin_used+0x2cd>
    274e:	31 c0                	xor    %eax,%eax
    2750:	bf 01 00 00 00       	mov    $0x1,%edi
    2755:	e8 26 fd ff ff       	call   2480 <__printf_chk@plt>
    275a:	ba 05 00 00 00       	mov    $0x5,%edx
    275f:	48 8d 35 81 4b 00 00 	lea    0x4b81(%rip),%rsi        # 72e7 <_IO_stdin_used+0x2e7>
    2766:	31 c0                	xor    %eax,%eax
    2768:	bf 01 00 00 00       	mov    $0x1,%edi
    276d:	e8 0e fd ff ff       	call   2480 <__printf_chk@plt>
    2772:	48 8d 3d 55 49 00 00 	lea    0x4955(%rip),%rdi        # 70ce <_IO_stdin_used+0xce>
    2779:	e8 92 fb ff ff       	call   2310 <puts@plt>
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    277e:	be 18 00 00 00       	mov    $0x18,%esi
    2783:	bf 06 00 00 00       	mov    $0x6,%edi
    2788:	e8 33 fc ff ff       	call   23c0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    278d:	be b0 00 00 00       	mov    $0xb0,%esi
    2792:	bf 09 00 00 00       	mov    $0x9,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    2797:	49 89 c6             	mov    %rax,%r14
    279a:	48 89 85 60 ff ff ff 	mov    %rax,-0xa0(%rbp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27a1:	e8 1a fc ff ff       	call   23c0 <calloc@plt>
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    27a6:	be 10 00 00 00       	mov    $0x10,%esi
    27ab:	bf 01 00 00 00       	mov    $0x1,%edi
    27b0:	49 83 ee 18          	sub    $0x18,%r14
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27b4:	49 89 c7             	mov    %rax,%r15
    27b7:	48 89 45 80          	mov    %rax,-0x80(%rbp)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    27bb:	4d 89 f4             	mov    %r14,%r12
    27be:	45 89 ee             	mov    %r13d,%r14d
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    27c1:	e8 fa fb ff ff       	call   23c0 <calloc@plt>
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27c6:	be 10 00 00 00       	mov    $0x10,%esi
    27cb:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    27d0:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    27d6:	48 89 c3             	mov    %rax,%rbx
    27d9:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27e0:	e8 db fb ff ff       	call   23c0 <calloc@plt>
  int external_thread_index = 0;
    27e5:	c7 45 98 00 00 00 00 	movl   $0x0,-0x68(%rbp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27ec:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
    27f0:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
            thread_data[x].tasks[y].run = barriered_work; 
    27f7:	4c 89 bd 58 ff ff ff 	mov    %r15,-0xa8(%rbp)
    27fe:	66 90                	xchg   %ax,%ax
    2800:	43 8d 04 36          	lea    (%r14,%r14,1),%eax
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2804:	be 08 00 00 00       	mov    $0x8,%esi
    2809:	bf 02 00 00 00       	mov    $0x2,%edi
    280e:	44 89 75 b0          	mov    %r14d,-0x50(%rbp)
    2812:	89 45 b8             	mov    %eax,-0x48(%rbp)
    2815:	e8 a6 fb ff ff       	call   23c0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    281a:	be 80 00 00 00       	mov    $0x80,%esi
    281f:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2824:	48 89 c3             	mov    %rax,%rbx
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2827:	e8 94 fb ff ff       	call   23c0 <calloc@plt>
    282c:	49 89 c5             	mov    %rax,%r13
    if (x % 2 == 1) {
    282f:	44 89 f0             	mov    %r14d,%eax
    2832:	41 83 c6 01          	add    $0x1,%r14d
    2836:	83 e0 01             	and    $0x1,%eax
    2839:	85 c0                	test   %eax,%eax
    283b:	0f 84 3f 0c 00 00    	je     3480 <main+0xe50>
      my_thread_data[0] = &thread_data[other]; 
    2841:	49 8d 8f 50 ff ff ff 	lea    -0xb0(%r15),%rcx
      other = abs(x - 1) % total_threads;
    2848:	8b 55 b0             	mov    -0x50(%rbp),%edx
      my_thread_data[1] = &thread_data[x]; 
    284b:	4c 89 7b 08          	mov    %r15,0x8(%rbx)
    284f:	31 c0                	xor    %eax,%eax
      thread_data[x].thread_index = 1;
    2851:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
    2858:	4d 89 f8             	mov    %r15,%r8
    285b:	48 8d 35 99 4a 00 00 	lea    0x4a99(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
    2862:	bf 01 00 00 00       	mov    $0x1,%edi
      my_thread_data[0] = &thread_data[other]; 
    2867:	48 89 0b             	mov    %rcx,(%rbx)
      other = abs(x - 1) % total_threads;
    286a:	44 8d 52 ff          	lea    -0x1(%rdx),%r10d
    286e:	44 89 55 a8          	mov    %r10d,-0x58(%rbp)
    2872:	e8 09 fc ff ff       	call   2480 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    2877:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    287c:	44 8b 55 a8          	mov    -0x58(%rbp),%r10d
    2880:	48 89 45 90          	mov    %rax,-0x70(%rbp)
    2884:	4d 89 67 38          	mov    %r12,0x38(%r15)
    2888:	44 8b 65 b0          	mov    -0x50(%rbp),%r12d
    288c:	44 89 d1             	mov    %r10d,%ecx
    288f:	bf 01 00 00 00       	mov    $0x1,%edi
    2894:	45 8b 07             	mov    (%r15),%r8d
    2897:	48 8d 35 d2 4c 00 00 	lea    0x4cd2(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    289e:	31 c0                	xor    %eax,%eax
    28a0:	44 89 55 a8          	mov    %r10d,-0x58(%rbp)
    28a4:	44 89 e2             	mov    %r12d,%edx
    28a7:	e8 d4 fb ff ff       	call   2480 <__printf_chk@plt>
    thread_data[x].other = other;
    28ac:	44 8b 55 a8          	mov    -0x58(%rbp),%r10d
    28b0:	8b 4d b8             	mov    -0x48(%rbp),%ecx
    28b3:	44 89 e2             	mov    %r12d,%edx
    28b6:	48 8d 35 e3 4c 00 00 	lea    0x4ce3(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    28bd:	bf 01 00 00 00       	mov    $0x1,%edi
    28c2:	31 c0                	xor    %eax,%eax
    28c4:	45 89 97 a8 00 00 00 	mov    %r10d,0xa8(%r15)
    28cb:	e8 b0 fb ff ff       	call   2480 <__printf_chk@plt>
      CPU_SET(curcpu, sendercpu);
    28d0:	0f b6 4d b8          	movzbl -0x48(%rbp),%ecx
    thread_data[x].threads = my_thread_data;
    28d4:	49 89 5f 10          	mov    %rbx,0x10(%r15)
      CPU_SET(curcpu, sendercpu);
    28d8:	b8 01 00 00 00       	mov    $0x1,%eax
    thread_data[x].real_thread_index = x;
    28dd:	45 89 67 04          	mov    %r12d,0x4(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28e1:	be 10 00 00 00       	mov    $0x10,%esi
    28e6:	bf 64 00 00 00       	mov    $0x64,%edi
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28eb:	31 db                	xor    %ebx,%ebx
      CPU_SET(curcpu, sendercpu);
    28ed:	48 d3 e0             	shl    %cl,%rax
    28f0:	49 09 45 00          	or     %rax,0x0(%r13)
    thread_data[x].thread_count = 2;
    28f4:	48 8b 05 45 51 00 00 	mov    0x5145(%rip),%rax        # 7a40 <_IO_stdin_used+0xa40>
    thread_data[x].cpu_set = sendercpu;
    28fb:	4d 89 af a0 00 00 00 	mov    %r13,0xa0(%r15)
    thread_data[x].thread_count = 2;
    2902:	49 89 47 18          	mov    %rax,0x18(%r15)
    thread_data[x].task_count = total_barrier_count;
    2906:	41 c7 47 30 03 00 00 00 	movl   $0x3,0x30(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    290e:	e8 ad fa ff ff       	call   23c0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2913:	be 10 00 00 00       	mov    $0x10,%esi
    2918:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    291d:	49 89 47 58          	mov    %rax,0x58(%r15)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2921:	e8 9a fa ff ff       	call   23c0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2926:	be 28 00 00 00       	mov    $0x28,%esi
    292b:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    2930:	66 0f 6f 15 e8 50 00 00 	movdqa 0x50e8(%rip),%xmm2        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2938:	49 89 47 60          	mov    %rax,0x60(%r15)
    thread_data[x].timestamp_count = 0;
    293c:	41 0f 11 57 70       	movups %xmm2,0x70(%r15)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2941:	e8 7a fa ff ff       	call   23c0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2946:	be 80 01 00 00       	mov    $0x180,%esi
    294b:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
    2950:	66 0f 6f 1d c8 50 00 00 	movdqa 0x50c8(%rip),%xmm3        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2958:	49 89 87 80 00 00 00 	mov    %rax,0x80(%r15)
    thread_data[x].task_timestamp_count = 0;
    295f:	41 0f 11 9f 88 00 00 00 	movups %xmm3,0x88(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2967:	e8 54 fa ff ff       	call   23c0 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    296c:	44 89 75 88          	mov    %r14d,-0x78(%rbp)
      thread_data[x].tasks = barriers;
    2970:	49 89 47 28          	mov    %rax,0x28(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2974:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks[y].protected = do_protected_write; 
    2977:	4c 63 f3             	movslq %ebx,%r14
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    297a:	be 20 00 00 00       	mov    $0x20,%esi
    297f:	bf 06 00 00 00       	mov    $0x6,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    2984:	4f 8d 24 76          	lea    (%r14,%r14,2),%r12
    2988:	48 8d 05 c1 0c 00 00 	lea    0xcc1(%rip),%rax        # 3650 <do_protected_write>
    298f:	49 c1 e4 07          	shl    $0x7,%r12
    2993:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
    2997:	49 89 85 a0 00 00 00 	mov    %rax,0xa0(%r13)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    299e:	e8 1d fa ff ff       	call   23c0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    29a3:	89 5d a8             	mov    %ebx,-0x58(%rbp)
    29a6:	49 89 85 e8 00 00 00 	mov    %rax,0xe8(%r13)
        for (int b = 0 ; b < 2 ; b++) {
    29ad:	49 89 c5             	mov    %rax,%r13
    29b0:	48 8d 40 40          	lea    0x40(%rax),%rax
    29b4:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    29b8:	4c 89 65 a0          	mov    %r12,-0x60(%rbp)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29bc:	be 08 00 00 00       	mov    $0x8,%esi
    29c1:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    29c6:	49 83 c5 20          	add    $0x20,%r13
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29ca:	e8 f1 f9 ff ff       	call   23c0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29cf:	be 08 00 00 00       	mov    $0x8,%esi
    29d4:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29d9:	49 89 c4             	mov    %rax,%r12
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29dc:	e8 df f9 ff ff       	call   23c0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29e1:	be 18 00 00 00       	mov    $0x18,%esi
    29e6:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29eb:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29ee:	e8 cd f9 ff ff       	call   23c0 <calloc@plt>
          data[0].messages_count = 0;
    29f3:	66 0f 6f 05 35 50 00 00 	movdqa 0x5035(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
          mailboxes[b].higher = &data[1];
    29fb:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29ff:	49 89 45 e0          	mov    %rax,-0x20(%r13)
          data[0].messages = messages;
    2a03:	4c 89 20             	mov    %r12,(%rax)
          data[1].messages = messages2;
    2a06:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    2a0a:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    2a0e:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    2a12:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
          mailboxes[b].higher = &data[1];
    2a16:	49 89 75 e8          	mov    %rsi,-0x18(%r13)
        for (int b = 0 ; b < 2 ; b++) {
    2a1a:	49 39 c5             	cmp    %rax,%r13
    2a1d:	75 9d                	jne    29bc <main+0x38c>
        char *message = malloc(sizeof(char) * 256);
    2a1f:	be 01 00 00 00       	mov    $0x1,%esi
    2a24:	bf 00 01 00 00       	mov    $0x100,%edi
    2a29:	8b 5d a8             	mov    -0x58(%rbp),%ebx
    2a2c:	4c 8b 65 a0          	mov    -0x60(%rbp),%r12
    2a30:	e8 8b f9 ff ff       	call   23c0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a35:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a3a:	49 89 c5             	mov    %rax,%r13
        struct Message *messaged = malloc(sizeof(struct Message));
    2a3d:	e8 fe f9 ff ff       	call   2440 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a42:	44 8b 45 b0          	mov    -0x50(%rbp),%r8d
    2a46:	4c 89 ef             	mov    %r13,%rdi
    2a49:	41 89 d9             	mov    %ebx,%r9d
    2a4c:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    2a50:	48 8d 0d 69 4b 00 00 	lea    0x4b69(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a57:	ba 00 01 00 00       	mov    $0x100,%edx
    2a5c:	31 c0                	xor    %eax,%eax
    2a5e:	be 01 00 00 00       	mov    $0x1,%esi
    2a63:	e8 f8 fa ff ff       	call   2560 <__sprintf_chk@plt>
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a68:	49 8b 57 28          	mov    0x28(%r15),%rdx
        messaged->message = message;
    2a6c:	4c 8b 55 b8          	mov    -0x48(%rbp),%r10
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a70:	8d 4b 01             	lea    0x1(%rbx),%ecx
        messaged->thread_index = thread_data[x].thread_index;
    2a73:	49 63 07             	movslq (%r15),%rax
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a76:	be 20 00 00 00       	mov    $0x20,%esi
    2a7b:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a80:	89 4d b8             	mov    %ecx,-0x48(%rbp)
        messaged->message = message;
    2a83:	4d 89 2a             	mov    %r13,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a86:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
        messaged->task_index = y;
    2a8a:	4d 89 72 10          	mov    %r14,0x10(%r10)
        messaged->thread_index = thread_data[x].thread_index;
    2a8e:	49 89 c6             	mov    %rax,%r14
    2a91:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a95:	41 89 8d 08 01 00 00 	mov    %ecx,0x108(%r13)
        thread_data[x].tasks[y].message = messaged;
    2a9c:	4d 89 95 00 01 00 00 	mov    %r10,0x100(%r13)
        thread_data[x].tasks[y].snapshot_count = 99;
    2aa3:	49 c7 85 d0 00 00 00 63 00 00 00 	movq   $0x63,0xd0(%r13)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2aae:	48 89 55 a8          	mov    %rdx,-0x58(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2ab2:	e8 09 f9 ff ff       	call   23c0 <calloc@plt>
        if (y == barrier_count - 1) {
    2ab7:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2aba:	41 89 5d 00          	mov    %ebx,0x0(%r13)
        if (y == barrier_count - 1) {
    2abe:	8b 4d b8             	mov    -0x48(%rbp),%ecx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2ac1:	49 89 85 c8 00 00 00 	mov    %rax,0xc8(%r13)
        if (y == barrier_count - 1) {
    2ac8:	48 8b 55 a8          	mov    -0x58(%rbp),%rdx
        thread_data[x].tasks[y].available = 1;
    2acc:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2ad6:	49 89 85 b8 00 00 00 	mov    %rax,0xb8(%r13)
        thread_data[x].tasks[y].sending = 1;
    2add:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2ae7:	49 c7 85 d8 00 00 00 00 00 00 00 	movq   $0x0,0xd8(%r13)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2af2:	45 89 b5 b0 00 00 00 	mov    %r14d,0xb0(%r13)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2af9:	4d 89 bd a8 00 00 00 	mov    %r15,0xa8(%r13)
        thread_data[x].tasks[y].arrived = 0;
    2b00:	41 c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r13)
        thread_data[x].tasks[y].thread_count = 2;
    2b0b:	41 c7 85 b4 00 00 00 02 00 00 00 	movl   $0x2,0xb4(%r13)
        thread_data[x].tasks[y].sending = 1;
    2b16:	49 89 85 f8 00 00 00 	mov    %rax,0xf8(%r13)
        if (y == barrier_count - 1) {
    2b1d:	0f 84 45 09 00 00    	je     3468 <main+0xe38>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2b23:	8b 45 b0             	mov    -0x50(%rbp),%eax
    2b26:	39 c3                	cmp    %eax,%ebx
    2b28:	75 66                	jne    2b90 <main+0x560>
    2b2a:	8b 5d 98             	mov    -0x68(%rbp),%ebx
    2b2d:	85 db                	test   %ebx,%ebx
    2b2f:	7f 5f                	jg     2b90 <main+0x560>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2b31:	89 c2                	mov    %eax,%edx
    2b33:	bf 01 00 00 00       	mov    $0x1,%edi
    2b38:	31 c0                	xor    %eax,%eax
    2b3a:	89 4d b8             	mov    %ecx,-0x48(%rbp)
    2b3d:	48 8d 35 a4 4a 00 00 	lea    0x4aa4(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2b44:	e8 37 f9 ff ff       	call   2480 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b49:	48 8b 8d 68 ff ff ff 	mov    -0x98(%rbp),%rcx
    2b50:	48 63 c3             	movslq %ebx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b53:	49 8b 57 28          	mov    0x28(%r15),%rdx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b57:	48 89 c7             	mov    %rax,%rdi
    2b5a:	48 c1 e0 04          	shl    $0x4,%rax
    2b5e:	48 01 c8             	add    %rcx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b61:	8b 4d b8             	mov    -0x48(%rbp),%ecx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b64:	49 89 47 40          	mov    %rax,0x40(%r15)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b68:	48 8d 05 d1 31 00 00 	lea    0x31d1(%rip),%rax        # 5d40 <barriered_work_ingest>
    2b6f:	4a 89 84 22 98 00 00 00 	mov    %rax,0x98(%rdx,%r12,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b77:	8d 47 01             	lea    0x1(%rdi),%eax
    2b7a:	89 45 98             	mov    %eax,-0x68(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b7d:	83 f9 03             	cmp    $0x3,%ecx
    2b80:	74 21                	je     2ba3 <main+0x573>
    2b82:	bb 01 00 00 00       	mov    $0x1,%ebx
    2b87:	e9 eb fd ff ff       	jmp    2977 <main+0x347>
    2b8c:	0f 1f 40 00          	nopl   0x0(%rax)
            thread_data[x].tasks[y].run = barriered_work; 
    2b90:	48 8d 05 79 2c 00 00 	lea    0x2c79(%rip),%rax        # 5810 <barriered_work>
    2b97:	49 89 85 98 00 00 00 	mov    %rax,0x98(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b9e:	83 f9 03             	cmp    $0x3,%ecx
    2ba1:	75 df                	jne    2b82 <main+0x552>
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2ba3:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2bad:	44 8b 75 88          	mov    -0x78(%rbp),%r14d
  for (int x = 0 ; x < total_threads ; x++) {
    2bb1:	4c 8b 65 90          	mov    -0x70(%rbp),%r12
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2bb5:	c7 82 80 03 00 00 00 00 00 00 	movl   $0x0,0x380(%rdx)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2bbf:	48 89 82 b4 03 00 00 	mov    %rax,0x3b4(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2bc6:	66 0f 6f a5 70 ff ff ff 	movdqa -0x90(%rbp),%xmm4
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2bce:	c7 82 00 03 00 00 02 00 00 00 	movl   $0x2,0x300(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bd8:	41 8b 07             	mov    (%r15),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2bdb:	4c 89 ba a8 03 00 00 	mov    %r15,0x3a8(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2be2:	49 81 c7 b0 00 00 00 	add    $0xb0,%r15
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2be9:	89 82 b0 03 00 00    	mov    %eax,0x3b0(%rdx)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2bef:	c7 82 fc 03 00 00 06 00 00 00 	movl   $0x6,0x3fc(%rdx)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2bf9:	c7 82 bc 03 00 00 03 00 00 00 	movl   $0x3,0x3bc(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2c03:	0f 11 a2 98 03 00 00 	movups %xmm4,0x398(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2c0a:	41 83 fe 09          	cmp    $0x9,%r14d
    2c0e:	0f 85 ec fb ff ff    	jne    2800 <main+0x1d0>
    2c14:	4c 8b 85 58 ff ff ff 	mov    -0xa8(%rbp),%r8
    2c1b:	ba 07 00 00 00       	mov    $0x7,%edx
    2c20:	48 8d 35 f1 46 00 00 	lea    0x46f1(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2c27:	31 c0                	xor    %eax,%eax
    2c29:	bf 01 00 00 00       	mov    $0x1,%edi
    2c2e:	4c 89 85 48 ff ff ff 	mov    %r8,-0xb8(%rbp)
    2c35:	e8 46 f8 ff ff       	call   2480 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c3a:	be 08 00 00 00       	mov    $0x8,%esi
    2c3f:	bf 02 00 00 00       	mov    $0x2,%edi
    2c44:	e8 77 f7 ff ff       	call   23c0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2c49:	4c 8b 7d 80          	mov    -0x80(%rbp),%r15
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c4d:	bf 09 00 00 00       	mov    $0x9,%edi
    my_thread_data[0] = &thread_data[x]; 
    2c52:	49 8d 8f d0 04 00 00 	lea    0x4d0(%r15),%rcx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c59:	4d 8d b7 60 01 00 00 	lea    0x160(%r15),%r14
    thread_data[x].threads = my_thread_data;
    2c60:	49 89 87 e0 04 00 00 	mov    %rax,0x4e0(%r15)
    my_thread_data[0] = &thread_data[x]; 
    2c67:	48 89 08             	mov    %rcx,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c6a:	49 8d b7 10 02 00 00 	lea    0x210(%r15),%rsi
    2c71:	49 8d 97 70 03 00 00 	lea    0x370(%r15),%rdx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c78:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c7c:	49 8b 47 28          	mov    0x28(%r15),%rax
    2c80:	49 8d 9f c0 02 00 00 	lea    0x2c0(%r15),%rbx
    thread_data[x].thread_count = 2;
    2c87:	41 c7 87 e8 04 00 00 02 00 00 00 	movl   $0x2,0x4e8(%r15)
    thread_data[x].thread_index = 0;
    2c92:	41 c7 87 d0 04 00 00 00 00 00 00 	movl   $0x0,0x4d0(%r15)
    thread_data[x].task_count = total_barrier_count;
    2c9d:	41 c7 87 00 05 00 00 03 00 00 00 	movl   $0x3,0x500(%r15)
    thread_data[n].tasks[0].scheduled = 1;
    2ca8:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2cb2:	49 8d 87 b0 00 00 00 	lea    0xb0(%r15),%rax
    2cb9:	48 89 45 98          	mov    %rax,-0x68(%rbp)
    2cbd:	49 8b 87 d8 00 00 00 	mov    0xd8(%r15),%rax
    2cc4:	48 89 75 a8          	mov    %rsi,-0x58(%rbp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cc8:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2ccd:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2cd7:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    my_thread_data[0] = &thread_data[x]; 
    2cde:	48 89 4d a0          	mov    %rcx,-0x60(%rbp)
    thread_data[n].tasks[0].scheduled = 1;
    2ce2:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2cec:	49 8b 87 38 02 00 00 	mov    0x238(%r15),%rax
    2cf3:	48 89 55 b8          	mov    %rdx,-0x48(%rbp)
    2cf7:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2d01:	49 8b 87 e8 02 00 00 	mov    0x2e8(%r15),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2d08:	4c 89 75 90          	mov    %r14,-0x70(%rbp)
    thread_data[n].tasks[0].scheduled = 1;
    2d0c:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2d16:	49 8b 87 98 03 00 00 	mov    0x398(%r15),%rax
    2d1d:	48 89 5d b0          	mov    %rbx,-0x50(%rbp)
    2d21:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d2b:	e8 90 f6 ff ff       	call   23c0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d30:	be 38 00 00 00       	mov    $0x38,%esi
    2d35:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d3a:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d3d:	e8 7e f6 ff ff       	call   23c0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d42:	be 38 00 00 00       	mov    $0x38,%esi
    2d47:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d4c:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d4f:	e8 6c f6 ff ff       	call   23c0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d54:	be 38 00 00 00       	mov    $0x38,%esi
    2d59:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d5e:	48 89 85 70 ff ff ff 	mov    %rax,-0x90(%rbp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d65:	e8 56 f6 ff ff       	call   23c0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d6a:	be 08 00 00 00       	mov    $0x8,%esi
    2d6f:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d74:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d7b:	e8 40 f6 ff ff       	call   23c0 <calloc@plt>
  thread_data[thread_count].type = TIMER;
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2d80:	be 08 00 00 00       	mov    $0x8,%esi
    2d85:	bf 09 00 00 00       	mov    $0x9,%edi
  thread_data[thread_count].type = TIMER;
    2d8a:	41 c7 87 28 04 00 00 00 00 00 00 	movl   $0x0,0x428(%r15)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d95:	49 89 c5             	mov    %rax,%r13
  thread_data[thread_count].task_count = total_barrier_count;
    2d98:	48 8b 05 a9 4c 00 00 	mov    0x4ca9(%rip),%rax        # 7a48 <_IO_stdin_used+0xa48>
    2d9f:	49 89 87 50 04 00 00 	mov    %rax,0x450(%r15)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2da6:	e8 15 f6 ff ff       	call   23c0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2dab:	48 8b 7d 98          	mov    -0x68(%rbp),%rdi
    2daf:	48 8b 75 a8          	mov    -0x58(%rbp),%rsi
  }
  thread_data[thread_count].threads = my_thread_data;
  thread_data[thread_count].thread_count = thread_count;
    2db3:	41 c7 87 38 04 00 00 06 00 00 00 	movl   $0x6,0x438(%r15)
    my_thread_data[n] = &thread_data[n]; 
    2dbe:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
    2dc2:	48 8b 4d a0          	mov    -0x60(%rbp),%rcx
    2dc6:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2dca:	4d 8d b7 20 04 00 00 	lea    0x420(%r15),%r14
    2dd1:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2dd5:	48 8b 7d b0          	mov    -0x50(%rbp),%rdi
    2dd9:	4c 89 38             	mov    %r15,(%rax)
    2ddc:	48 89 78 20          	mov    %rdi,0x20(%rax)
    2de0:	49 8d bf 80 05 00 00 	lea    0x580(%r15),%rdi
    2de7:	48 89 70 18          	mov    %rsi,0x18(%rax)
    2deb:	48 8d 35 35 45 00 00 	lea    0x4535(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2df2:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2df6:	ba 06 00 00 00       	mov    $0x6,%edx
    2dfb:	4c 89 70 30          	mov    %r14,0x30(%rax)
    2dff:	48 89 48 38          	mov    %rcx,0x38(%rax)
    2e03:	48 89 78 40          	mov    %rdi,0x40(%rax)
  thread_data[thread_count].threads = my_thread_data;
    2e07:	49 89 87 30 04 00 00 	mov    %rax,0x430(%r15)
    2e0e:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].my_thread_count = 2;
    2e10:	41 c7 87 40 04 00 00 02 00 00 00 	movl   $0x2,0x440(%r15)
  thread_data[thread_count].thread_index = 0;
    2e1b:	41 c7 87 20 04 00 00 00 00 00 00 	movl   $0x0,0x420(%r15)
    2e26:	4c 8d 3d db 47 00 00 	lea    0x47db(%rip),%r15        # 7608 <_IO_stdin_used+0x608>
    my_thread_data[n] = &thread_data[n]; 
    2e2d:	48 89 7d 88          	mov    %rdi,-0x78(%rbp)
    2e31:	bf 01 00 00 00       	mov    $0x1,%edi
    2e36:	e8 45 f6 ff ff       	call   2480 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2e3b:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2e42:	49 8d 7d 30          	lea    0x30(%r13),%rdi
    2e46:	4c 89 eb             	mov    %r13,%rbx
    2e49:	4c 89 f1             	mov    %r14,%rcx
    2e4c:	48 8d 15 0d 0c 00 00 	lea    0xc0d(%rip),%rdx        # 3a60 <timer_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    2e53:	45 31 f6             	xor    %r14d,%r14d
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2e56:	e8 45 f6 ff ff       	call   24a0 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2e5b:	4c 89 ad 50 ff ff ff 	mov    %r13,-0xb0(%rbp)
    2e62:	45 89 f5             	mov    %r14d,%r13d
    2e65:	4d 89 e6             	mov    %r12,%r14
    2e68:	49 89 dc             	mov    %rbx,%r12
    2e6b:	48 8b 9d 48 ff ff ff 	mov    -0xb8(%rbp),%rbx
    2e72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    thread_data[x].type = WORKER;
    2e78:	c7 43 08 01 00 00 00 	movl   $0x1,0x8(%rbx)
    2e7f:	44 89 ea             	mov    %r13d,%edx
    2e82:	4c 89 fe             	mov    %r15,%rsi
    2e85:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2e87:	c7 43 34 01 00 00 00 	movl   $0x1,0x34(%rbx)
    2e8e:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < thread_count ; x++) {
    2e93:	41 83 c5 01          	add    $0x1,%r13d
    2e97:	e8 e4 f5 ff ff       	call   2480 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2e9c:	48 89 d9             	mov    %rbx,%rcx
    2e9f:	4c 89 f6             	mov    %r14,%rsi
    2ea2:	4c 89 e7             	mov    %r12,%rdi
    2ea5:	48 8d 15 64 08 00 00 	lea    0x864(%rip),%rdx        # 3710 <barriered_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    2eac:	48 81 c3 b0 00 00 00 	add    $0xb0,%rbx
    2eb3:	49 83 c4 08          	add    $0x8,%r12
    2eb7:	49 83 c6 38          	add    $0x38,%r14
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2ebb:	e8 e0 f5 ff ff       	call   24a0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2ec0:	48 8b 53 f0          	mov    -0x10(%rbx),%rdx
    2ec4:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
    2ec9:	be 08 00 00 00       	mov    $0x8,%esi
    2ece:	e8 2d f4 ff ff       	call   2300 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2ed3:	41 83 fd 06          	cmp    $0x6,%r13d
    2ed7:	75 9f                	jne    2e78 <main+0x848>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2ed9:	4c 8b 75 80          	mov    -0x80(%rbp),%r14
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2edd:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].task_count = 0;
    2ee2:	48 8b 1d 67 4b 00 00 	mov    0x4b67(%rip),%rbx        # 7a50 <_IO_stdin_used+0xa50>
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ee9:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    2eee:	4c 8b ad 50 ff ff ff 	mov    -0xb0(%rbp),%r13
    thread_data[x].task_count = 0;
    2ef5:	49 89 9e 00 05 00 00 	mov    %rbx,0x500(%r14)
    thread_data[x].type = IO;
    2efc:	41 c7 86 d8 04 00 00 02 00 00 00 	movl   $0x2,0x4d8(%r14)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f07:	e8 b4 f4 ff ff       	call   23c0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f0c:	be 00 08 00 00       	mov    $0x800,%esi
    2f11:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f13:	49 89 86 18 05 00 00 	mov    %rax,0x518(%r14)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f1a:	e8 d1 f5 ff ff       	call   24f0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f1f:	be 08 00 00 00       	mov    $0x8,%esi
    2f24:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f29:	41 89 86 20 05 00 00 	mov    %eax,0x520(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f30:	e8 8b f4 ff ff       	call   23c0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    2f35:	4c 8b 65 90          	mov    -0x70(%rbp),%r12
    2f39:	4c 8b 7d 98          	mov    -0x68(%rbp),%r15
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    2f3d:	41 c7 86 e8 04 00 00 06 00 00 00 	movl   $0x6,0x4e8(%r14)
      my_thread_data[n] = &thread_data[n]; 
    2f48:	48 8b 7d a8          	mov    -0x58(%rbp),%rdi
    2f4c:	48 8b 75 b0          	mov    -0x50(%rbp),%rsi
    2f50:	4c 89 30             	mov    %r14,(%rax)
    2f53:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
    2f57:	4c 89 60 10          	mov    %r12,0x10(%rax)
    2f5b:	48 89 78 18          	mov    %rdi,0x18(%rax)
    2f5f:	bf 01 00 00 00       	mov    $0x1,%edi
    2f64:	48 89 70 20          	mov    %rsi,0x20(%rax)
    2f68:	48 8d 35 d6 43 00 00 	lea    0x43d6(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    2f6f:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2f73:	ba 07 00 00 00       	mov    $0x7,%edx
    thread_data[x].threads = my_thread_data;
    2f78:	49 89 86 e0 04 00 00 	mov    %rax,0x4e0(%r14)
      my_thread_data[n] = &thread_data[n]; 
    2f7f:	4c 89 78 08          	mov    %r15,0x8(%rax)
    2f83:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    2f85:	41 c7 86 d0 04 00 00 07 00 00 00 	movl   $0x7,0x4d0(%r14)
    2f90:	e8 eb f4 ff ff       	call   2480 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2f95:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
    2f9c:	48 8b 4d a0          	mov    -0x60(%rbp),%rcx
    2fa0:	49 8d 7d 38          	lea    0x38(%r13),%rdi
    2fa4:	48 8d 15 25 1e 00 00 	lea    0x1e25(%rip),%rdx        # 4dd0 <io_thread>
    2fab:	48 05 88 01 00 00    	add    $0x188,%rax
    2fb1:	48 89 c6             	mov    %rax,%rsi
    2fb4:	e8 e7 f4 ff ff       	call   24a0 <pthread_create@plt>
    2fb9:	ba 08 00 00 00       	mov    $0x8,%edx
    2fbe:	48 8d 35 97 43 00 00 	lea    0x4397(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    2fc5:	31 c0                	xor    %eax,%eax
    2fc7:	bf 01 00 00 00       	mov    $0x1,%edi
    2fcc:	e8 af f4 ff ff       	call   2480 <__printf_chk@plt>
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2fd1:	be 08 00 00 00       	mov    $0x8,%esi
    2fd6:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[x].buffers = &buffers[buffer_index];
    2fdb:	48 8b 85 68 ff ff ff 	mov    -0x98(%rbp),%rax
    thread_data[x].task_count = 0;
    2fe2:	49 89 9e b0 05 00 00 	mov    %rbx,0x5b0(%r14)
    2fe9:	48 8d 1d a7 43 00 00 	lea    0x43a7(%rip),%rbx        # 7397 <_IO_stdin_used+0x397>
    thread_data[x].type = EXTERNAL;
    2ff0:	41 c7 86 88 05 00 00 03 00 00 00 	movl   $0x3,0x588(%r14)
    thread_data[x].buffers = &buffers[buffer_index];
    2ffb:	49 89 86 c0 05 00 00 	mov    %rax,0x5c0(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3002:	e8 b9 f3 ff ff       	call   23c0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3007:	48 8b 4d a8          	mov    -0x58(%rbp),%rcx
    300b:	48 8b 75 b0          	mov    -0x50(%rbp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    300f:	41 c7 86 80 05 00 00 08 00 00 00 	movl   $0x8,0x580(%r14)
      my_thread_data[n] = &thread_data[n]; 
    301a:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
    301e:	4c 89 30             	mov    %r14,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3021:	49 8d 7d 40          	lea    0x40(%r13),%rdi
      my_thread_data[n] = &thread_data[n]; 
    3025:	4c 89 60 10          	mov    %r12,0x10(%rax)
    3029:	4c 8d 65 c0          	lea    -0x40(%rbp),%r12
    302d:	48 89 48 18          	mov    %rcx,0x18(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3031:	48 8b 4d 88          	mov    -0x78(%rbp),%rcx
      my_thread_data[n] = &thread_data[n]; 
    3035:	48 89 70 20          	mov    %rsi,0x20(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3039:	48 8b b5 58 ff ff ff 	mov    -0xa8(%rbp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3040:	48 89 50 28          	mov    %rdx,0x28(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3044:	48 8d 15 55 09 00 00 	lea    0x955(%rip),%rdx        # 39a0 <external_thread>
    thread_data[x].threads = my_thread_data;
    304b:	49 89 86 90 05 00 00 	mov    %rax,0x590(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3052:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
      my_thread_data[n] = &thread_data[n]; 
    3059:	4c 89 78 08          	mov    %r15,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    305d:	48 8b 05 f4 49 00 00 	mov    0x49f4(%rip),%rax        # 7a58 <_IO_stdin_used+0xa58>
    3064:	49 89 86 98 05 00 00 	mov    %rax,0x598(%r14)
    306b:	45 31 f6             	xor    %r14d,%r14d
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    306e:	e8 2d f4 ff ff       	call   24a0 <pthread_create@plt>
    3073:	48 8d 3d ff 42 00 00 	lea    0x42ff(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    307a:	e8 91 f2 ff ff       	call   2310 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    307f:	90                   	nop
    void * result; 
    pthread_join(thread[x], &result);
    3080:	4b 8b 7c f5 00       	mov    0x0(%r13,%r14,8),%rdi
    3085:	4c 89 e6             	mov    %r12,%rsi
    3088:	e8 a3 f4 ff ff       	call   2530 <pthread_join@plt>
    308d:	44 89 f2             	mov    %r14d,%edx
    3090:	48 89 de             	mov    %rbx,%rsi
    3093:	bf 01 00 00 00       	mov    $0x1,%edi
    3098:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    309a:	49 83 c6 01          	add    $0x1,%r14
    309e:	e8 dd f3 ff ff       	call   2480 <__printf_chk@plt>
    30a3:	49 83 fe 09          	cmp    $0x9,%r14
    30a7:	75 d7                	jne    3080 <main+0xa50>
    30a9:	48 8b 45 80          	mov    -0x80(%rbp),%rax
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
    30ad:	45 31 db             	xor    %r11d,%r11d
  long total = 0;
    30b0:	31 c9                	xor    %ecx,%ecx
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    30b2:	c7 45 b8 00 00 00 00 	movl   $0x0,-0x48(%rbp)
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    30b9:	48 89 4d a8          	mov    %rcx,-0x58(%rbp)
  long sends = 0;
    30bd:	45 31 d2             	xor    %r10d,%r10d
  long received = 0;
    30c0:	31 db                	xor    %ebx,%ebx
  long sents = 0;
    30c2:	45 31 e4             	xor    %r12d,%r12d
    30c5:	4c 8d 70 28          	lea    0x28(%rax),%r14
    30c9:	48 8b 85 60 ff ff ff 	mov    -0xa0(%rbp),%rax
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    30d0:	4c 89 5d a0          	mov    %r11,-0x60(%rbp)
    30d4:	4d 89 d0             	mov    %r10,%r8
    30d7:	49 bf db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r15
    30e1:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
    30e5:	0f 1f 00             	nopl   (%rax)
    if (x % 2 == 1) {
    30e8:	8b 7d b8             	mov    -0x48(%rbp),%edi
    30eb:	4c 89 45 98          	mov    %r8,-0x68(%rbp)
    30ef:	89 f8                	mov    %edi,%eax
    30f1:	41 89 fd             	mov    %edi,%r13d
      other = (x + 1) % total_threads;
    30f4:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
    30f7:	83 e0 01             	and    $0x1,%eax
      other = abs(x - 1) % total_threads;
    30fa:	41 83 ed 01          	sub    $0x1,%r13d
      other = (x + 1) % total_threads;
    30fe:	89 7d b8             	mov    %edi,-0x48(%rbp)
      other = abs(x - 1) % total_threads;
    3101:	85 c0                	test   %eax,%eax
    3103:	44 0f 44 ef          	cmove  %edi,%r13d
    3107:	bf 0a 00 00 00       	mov    $0xa,%edi
    310c:	e8 df f1 ff ff       	call   22f0 <putchar@plt>
    3111:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
    3115:	bf 01 00 00 00       	mov    $0x1,%edi
    311a:	48 8d 35 8a 42 00 00 	lea    0x428a(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    3121:	48 8b 10             	mov    (%rax),%rdx
    3124:	31 c0                	xor    %eax,%eax
    3126:	e8 55 f3 ff ff       	call   2480 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    312b:	49 63 56 08          	movslq 0x8(%r14),%rdx
    312f:	4c 8b 45 98          	mov    -0x68(%rbp),%r8
    3133:	85 d2                	test   %edx,%edx
    3135:	0f 8e b3 03 00 00    	jle    34ee <main+0xebe>
    313b:	49 8b 06             	mov    (%r14),%rax
    313e:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
    long v = 0;
    3142:	31 d2                	xor    %edx,%edx
    3144:	48 c1 e6 07          	shl    $0x7,%rsi
    3148:	48 05 90 00 00 00    	add    $0x90,%rax
    314e:	48 01 c6             	add    %rax,%rsi
    3151:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      v += thread_data[me].tasks[n].v;
    3158:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    315b:	48 05 80 01 00 00    	add    $0x180,%rax
    3161:	48 39 f0             	cmp    %rsi,%rax
    3164:	75 f2                	jne    3158 <main+0xb28>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3166:	4d 63 ed             	movslq %r13d,%r13
    3169:	48 8b 7d 80          	mov    -0x80(%rbp),%rdi
    316d:	4b 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%rax
    3172:	49 8d 44 45 00       	lea    0x0(%r13,%rax,2),%rax
    3177:	48 c1 e0 04          	shl    $0x4,%rax
    317b:	48 01 f8             	add    %rdi,%rax
    317e:	48 63 70 30          	movslq 0x30(%rax),%rsi
    3182:	85 f6                	test   %esi,%esi
    3184:	7e 28                	jle    31ae <main+0xb7e>
      v += thread_data[other].tasks[n].v;
    3186:	48 8b 40 28          	mov    0x28(%rax),%rax
    318a:	48 8d 34 76          	lea    (%rsi,%rsi,2),%rsi
    318e:	48 c1 e6 07          	shl    $0x7,%rsi
    3192:	48 05 90 00 00 00    	add    $0x90,%rax
    3198:	48 01 c6             	add    %rax,%rsi
    319b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    31a0:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    31a3:	48 05 80 01 00 00    	add    $0x180,%rax
    31a9:	48 39 c6             	cmp    %rax,%rsi
    31ac:	75 f2                	jne    31a0 <main+0xb70>
    31ae:	48 8d 35 0b 42 00 00 	lea    0x420b(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    31b5:	bf 01 00 00 00       	mov    $0x1,%edi
    31ba:	31 c0                	xor    %eax,%eax
    31bc:	4c 89 45 98          	mov    %r8,-0x68(%rbp)
    31c0:	e8 bb f2 ff ff       	call   2480 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    31c5:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
    31c9:	bf 01 00 00 00       	mov    $0x1,%edi
    31ce:	48 8b 30             	mov    (%rax),%rsi
    31d1:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    31db:	48 f7 ee             	imul   %rsi
    31de:	48 c1 fe 3f          	sar    $0x3f,%rsi
    31e2:	31 c0                	xor    %eax,%eax
    31e4:	48 d1 fa             	sar    %rdx
    31e7:	48 29 f2             	sub    %rsi,%rdx
    31ea:	48 8d 35 3f 44 00 00 	lea    0x443f(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    31f1:	e8 8a f2 ff ff       	call   2480 <__printf_chk@plt>
    31f6:	bf 0a 00 00 00       	mov    $0xa,%edi
    31fb:	e8 f0 f0 ff ff       	call   22f0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3200:	49 63 46 08          	movslq 0x8(%r14),%rax
    3204:	4c 8b 45 98          	mov    -0x68(%rbp),%r8
    3208:	85 c0                	test   %eax,%eax
    320a:	0f 8e 85 00 00 00    	jle    3295 <main+0xc65>
    3210:	49 8b 3e             	mov    (%r14),%rdi
    3213:	48 8d 34 40          	lea    (%rax,%rax,2),%rsi
    3217:	4c 8b 5d a8          	mov    -0x58(%rbp),%r11
    321b:	48 c1 e6 07          	shl    $0x7,%rsi
    321f:	4c 8b 4d a0          	mov    -0x60(%rbp),%r9
    3223:	48 8d 97 88 00 00 00 	lea    0x88(%rdi),%rdx
    322a:	48 01 d6             	add    %rdx,%rsi
    322d:	0f 1f 00             	nopl   (%rax)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3230:	48 8b 42 60          	mov    0x60(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    3234:	4c 03 1a             	add    (%rdx),%r11
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3237:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
      ingests += thread_data[x].tasks[n].ingest_count;
    323e:	4c 03 8a d8 fe ff ff 	add    -0x128(%rdx),%r9
      sends += thread_data[x].tasks[n].sends;
    3245:	4c 03 82 e8 fe ff ff 	add    -0x118(%rdx),%r8
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    324c:	4c 03 60 10          	add    0x10(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3250:	48 03 58 18          	add    0x18(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3254:	4c 03 60 30          	add    0x30(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3258:	48 03 58 38          	add    0x38(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    325c:	4c 03 60 50          	add    0x50(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3260:	48 03 58 58          	add    0x58(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3264:	4c 03 60 70          	add    0x70(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3268:	48 03 58 78          	add    0x78(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    326c:	4c 03 a0 90 00 00 00 	add    0x90(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3273:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    327a:	4c 03 a0 b0 00 00 00 	add    0xb0(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3281:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3288:	48 39 f2             	cmp    %rsi,%rdx
    328b:	75 a3                	jne    3230 <main+0xc00>
    328d:	4c 89 5d a8          	mov    %r11,-0x58(%rbp)
    3291:	4c 89 4d a0          	mov    %r9,-0x60(%rbp)
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3295:	45 31 ed             	xor    %r13d,%r13d
    3298:	49 83 7e 68 00       	cmpq   $0x0,0x68(%r14)
    329d:	7e 72                	jle    3311 <main+0xce1>
    329f:	48 89 5d 98          	mov    %rbx,-0x68(%rbp)
    32a3:	4c 89 f3             	mov    %r14,%rbx
    32a6:	4d 89 e6             	mov    %r12,%r14
    32a9:	4d 89 ec             	mov    %r13,%r12
    32ac:	4d 89 c5             	mov    %r8,%r13
    32af:	90                   	nop
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    32b0:	48 8b 43 58          	mov    0x58(%rbx),%rax
    32b4:	4b 8d 14 a4          	lea    (%r12,%r12,4),%rdx
    32b8:	48 83 ec 08          	sub    $0x8,%rsp
    32bc:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    32c1:	49 83 c4 01          	add    $0x1,%r12
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    32c5:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    32c9:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    32cd:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32d1:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    32d4:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    32d8:	4c 2b 01             	sub    (%rcx),%r8
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32db:	49 f7 e7             	mul    %r15
    32de:	8b 49 20             	mov    0x20(%rcx),%ecx
    32e1:	56                   	push   %rsi
    32e2:	31 c0                	xor    %eax,%eax
    32e4:	48 8d 35 65 43 00 00 	lea    0x4365(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    32eb:	48 c1 ea 12          	shr    $0x12,%rdx
    32ef:	49 89 d1             	mov    %rdx,%r9
    32f2:	ba 02 00 00 00       	mov    $0x2,%edx
    32f7:	e8 84 f1 ff ff       	call   2480 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    32fc:	58                   	pop    %rax
    32fd:	5a                   	pop    %rdx
    32fe:	4c 39 63 68          	cmp    %r12,0x68(%rbx)
    3302:	7f ac                	jg     32b0 <main+0xc80>
    3304:	4d 89 f4             	mov    %r14,%r12
    3307:	49 89 de             	mov    %rbx,%r14
    330a:	48 8b 5d 98          	mov    -0x68(%rbp),%rbx
    330e:	4d 89 e8             	mov    %r13,%r8
  for (int x = 0 ; x < thread_count ; x++) {
    3311:	48 83 45 b0 18       	addq   $0x18,-0x50(%rbp)
    3316:	49 81 c6 b0 00 00 00 	add    $0xb0,%r14
    331d:	83 7d b8 06          	cmpl   $0x6,-0x48(%rbp)
    3321:	0f 85 c1 fd ff ff    	jne    30e8 <main+0xab8>
    3327:	48 8b 4d a8          	mov    -0x58(%rbp),%rcx
    332b:	4c 8b 5d a0          	mov    -0x60(%rbp),%r11
    332f:	bf 01 00 00 00       	mov    $0x1,%edi
    3334:	31 c0                	xor    %eax,%eax
    3336:	48 8d 35 90 40 00 00 	lea    0x4090(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    333d:	4c 89 45 b0          	mov    %r8,-0x50(%rbp)
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3341:	49 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r13
    334b:	48 89 ca             	mov    %rcx,%rdx
    334e:	48 89 4d b8          	mov    %rcx,-0x48(%rbp)
    3352:	4c 89 5d a8          	mov    %r11,-0x58(%rbp)
    3356:	e8 25 f1 ff ff       	call   2480 <__printf_chk@plt>
    335b:	bf 0a 00 00 00       	mov    $0xa,%edi
    3360:	e8 8b ef ff ff       	call   22f0 <putchar@plt>
    3365:	48 8b 85 60 ff ff ff 	mov    -0xa0(%rbp),%rax
    336c:	bf 01 00 00 00       	mov    $0x1,%edi
    3371:	48 8d 35 28 43 00 00 	lea    0x4328(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    3378:	48 8b 50 08          	mov    0x8(%rax),%rdx
    337c:	31 c0                	xor    %eax,%eax
    337e:	e8 fd f0 ff ff       	call   2480 <__printf_chk@plt>
    3383:	4c 8b 5d a8          	mov    -0x58(%rbp),%r11
    3387:	bf 01 00 00 00       	mov    $0x1,%edi
    338c:	48 8d 35 35 43 00 00 	lea    0x4335(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    3393:	4c 89 d8             	mov    %r11,%rax
    3396:	49 c1 fb 3f          	sar    $0x3f,%r11
    339a:	49 f7 ed             	imul   %r13
    339d:	31 c0                	xor    %eax,%eax
    339f:	48 d1 fa             	sar    %rdx
    33a2:	4c 29 da             	sub    %r11,%rdx
    33a5:	e8 d6 f0 ff ff       	call   2480 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    33aa:	4c 8b 55 b0          	mov    -0x50(%rbp),%r10
    33ae:	bf 01 00 00 00       	mov    $0x1,%edi
    33b3:	48 8d 35 3e 43 00 00 	lea    0x433e(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    33ba:	4c 89 d0             	mov    %r10,%rax
    33bd:	49 c1 fa 3f          	sar    $0x3f,%r10
    33c1:	49 f7 ed             	imul   %r13
    33c4:	31 c0                	xor    %eax,%eax
    33c6:	48 d1 fa             	sar    %rdx
    33c9:	4c 29 d2             	sub    %r10,%rdx
    33cc:	e8 af f0 ff ff       	call   2480 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    33d1:	48 8b 4d b8          	mov    -0x48(%rbp),%rcx
    33d5:	bf 01 00 00 00       	mov    $0x1,%edi
    33da:	48 8d 35 47 43 00 00 	lea    0x4347(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    33e1:	48 89 c8             	mov    %rcx,%rax
    33e4:	48 c1 f9 3f          	sar    $0x3f,%rcx
    33e8:	49 f7 ed             	imul   %r13
    33eb:	31 c0                	xor    %eax,%eax
    33ed:	48 d1 fa             	sar    %rdx
    33f0:	48 29 ca             	sub    %rcx,%rdx
    33f3:	e8 88 f0 ff ff       	call   2480 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    33f8:	4c 89 e0             	mov    %r12,%rax
    33fb:	49 c1 fc 3f          	sar    $0x3f,%r12
    33ff:	48 8d 35 db 3f 00 00 	lea    0x3fdb(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    3406:	49 f7 ed             	imul   %r13
    3409:	bf 01 00 00 00       	mov    $0x1,%edi
    340e:	31 c0                	xor    %eax,%eax
    3410:	48 d1 fa             	sar    %rdx
    3413:	4c 29 e2             	sub    %r12,%rdx
    3416:	e8 65 f0 ff ff       	call   2480 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    341b:	48 89 d8             	mov    %rbx,%rax
    341e:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3422:	48 8d 35 c9 3f 00 00 	lea    0x3fc9(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    3429:	49 f7 ed             	imul   %r13
    342c:	bf 01 00 00 00       	mov    $0x1,%edi
    3431:	48 d1 fa             	sar    %rdx
    3434:	48 29 da             	sub    %rbx,%rdx
    3437:	31 c0                	xor    %eax,%eax
    3439:	e8 42 f0 ff ff       	call   2480 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    343e:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    3442:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    344b:	0f 85 a4 00 00 00    	jne    34f5 <main+0xec5>
    3451:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
    3455:	31 c0                	xor    %eax,%eax
    3457:	5b                   	pop    %rbx
    3458:	41 5c                	pop    %r12
    345a:	41 5d                	pop    %r13
    345c:	41 5e                	pop    %r14
    345e:	41 5f                	pop    %r15
    3460:	5d                   	pop    %rbp
    3461:	c3                   	ret
    3462:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          thread_data[x].tasks[y].run = barriered_work; 
    3468:	48 8d 05 a1 23 00 00 	lea    0x23a1(%rip),%rax        # 5810 <barriered_work>
    346f:	bb 02 00 00 00       	mov    $0x2,%ebx
    3474:	49 89 85 98 00 00 00 	mov    %rax,0x98(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    347b:	e9 f7 f4 ff ff       	jmp    2977 <main+0x347>
      other = (x + 1) % total_threads;
    3480:	45 89 f2             	mov    %r14d,%r10d
      my_thread_data[0] = &thread_data[x]; 
    3483:	4c 89 3b             	mov    %r15,(%rbx)
    3486:	4c 89 f9             	mov    %r15,%rcx
    3489:	48 8d 35 79 3e 00 00 	lea    0x3e79(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      other = (x + 1) % total_threads;
    3490:	4d 69 d2 39 8e e3 38 	imul   $0x38e38e39,%r10,%r10
      thread_data[x].thread_index = 0;
    3497:	41 c7 07 00 00 00 00 	movl   $0x0,(%r15)
    349e:	bf 01 00 00 00       	mov    $0x1,%edi
      other = (x + 1) % total_threads;
    34a3:	49 c1 ea 21          	shr    $0x21,%r10
    34a7:	43 8d 04 d2          	lea    (%r10,%r10,8),%eax
    34ab:	45 89 f2             	mov    %r14d,%r10d
    34ae:	41 29 c2             	sub    %eax,%r10d
      my_thread_data[1] = &thread_data[other]; 
    34b1:	49 63 c2             	movslq %r10d,%rax
    34b4:	44 89 55 a8          	mov    %r10d,-0x58(%rbp)
    34b8:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    34bc:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    34c0:	48 8b 45 80          	mov    -0x80(%rbp),%rax
    34c4:	8b 55 b0             	mov    -0x50(%rbp),%edx
    34c7:	49 c1 e0 04          	shl    $0x4,%r8
    34cb:	49 01 c0             	add    %rax,%r8
    34ce:	31 c0                	xor    %eax,%eax
    34d0:	4c 89 43 08          	mov    %r8,0x8(%rbx)
    34d4:	e8 a7 ef ff ff       	call   2480 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    34d9:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    34de:	44 8b 55 a8          	mov    -0x58(%rbp),%r10d
    34e2:	48 89 45 90          	mov    %rax,-0x70(%rbp)
    34e6:	49 89 c4             	mov    %rax,%r12
    34e9:	e9 96 f3 ff ff       	jmp    2884 <main+0x254>
    long v = 0;
    34ee:	31 d2                	xor    %edx,%edx
    34f0:	e9 71 fc ff ff       	jmp    3166 <main+0xb36>
}
    34f5:	e8 56 ee ff ff       	call   2350 <__stack_chk_fail@plt>
    34fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000003500 <_start>:
    3500:	f3 0f 1e fa          	endbr64
    3504:	31 ed                	xor    %ebp,%ebp
    3506:	49 89 d1             	mov    %rdx,%r9
    3509:	5e                   	pop    %rsi
    350a:	48 89 e2             	mov    %rsp,%rdx
    350d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3511:	50                   	push   %rax
    3512:	54                   	push   %rsp
    3513:	45 31 c0             	xor    %r8d,%r8d
    3516:	31 c9                	xor    %ecx,%ecx
    3518:	48 8d 3d 11 f1 ff ff 	lea    -0xeef(%rip),%rdi        # 2630 <main>
    351f:	ff 15 ab 6a 00 00    	call   *0x6aab(%rip)        # 9fd0 <__libc_start_main@GLIBC_2.34>
    3525:	f4                   	hlt
    3526:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003530 <__gmon_start__>:
    3530:	f3 0f 1e fa          	endbr64
    3534:	8b 05 ee 6a 00 00    	mov    0x6aee(%rip),%eax        # a028 <called.0>
    353a:	85 c0                	test   %eax,%eax
    353c:	74 02                	je     3540 <__gmon_start__+0x10>
    353e:	c3                   	ret
    353f:	90                   	nop
    3540:	48 83 ec 08          	sub    $0x8,%rsp
    3544:	48 8d 35 52 2d 00 00 	lea    0x2d52(%rip),%rsi        # 629d <etext>
    354b:	48 8d 3d ae ca ff ff 	lea    -0x3552(%rip),%rdi        # 0 <__executable_start>
    3552:	c7 05 cc 6a 00 00 01 00 00 00 	movl   $0x1,0x6acc(%rip)        # a028 <called.0>
    355c:	e8 7f ee ff ff       	call   23e0 <__monstartup@plt>
    3561:	48 8b 3d 78 6a 00 00 	mov    0x6a78(%rip),%rdi        # 9fe0 <_mcleanup@GLIBC_2.2.5>
    3568:	48 83 c4 08          	add    $0x8,%rsp
    356c:	e9 ef 2c 00 00       	jmp    6260 <atexit>
    3571:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    357b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003580 <_dl_relocate_static_pie>:
    3580:	f3 0f 1e fa          	endbr64
    3584:	c3                   	ret
    3585:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    358f:	90                   	nop

0000000000003590 <deregister_tm_clones>:
    3590:	48 8d 3d 89 6a 00 00 	lea    0x6a89(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3597:	48 8d 05 82 6a 00 00 	lea    0x6a82(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    359e:	48 39 f8             	cmp    %rdi,%rax
    35a1:	74 15                	je     35b8 <deregister_tm_clones+0x28>
    35a3:	48 8b 05 2e 6a 00 00 	mov    0x6a2e(%rip),%rax        # 9fd8 <_ITM_deregisterTMCloneTable@Base>
    35aa:	48 85 c0             	test   %rax,%rax
    35ad:	74 09                	je     35b8 <deregister_tm_clones+0x28>
    35af:	ff e0                	jmp    *%rax
    35b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    35b8:	c3                   	ret
    35b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000035c0 <register_tm_clones>:
    35c0:	48 8d 3d 59 6a 00 00 	lea    0x6a59(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    35c7:	48 8d 35 52 6a 00 00 	lea    0x6a52(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    35ce:	48 29 fe             	sub    %rdi,%rsi
    35d1:	48 89 f0             	mov    %rsi,%rax
    35d4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    35d8:	48 c1 f8 03          	sar    $0x3,%rax
    35dc:	48 01 c6             	add    %rax,%rsi
    35df:	48 d1 fe             	sar    %rsi
    35e2:	74 14                	je     35f8 <register_tm_clones+0x38>
    35e4:	48 8b 05 05 6a 00 00 	mov    0x6a05(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    35eb:	48 85 c0             	test   %rax,%rax
    35ee:	74 08                	je     35f8 <register_tm_clones+0x38>
    35f0:	ff e0                	jmp    *%rax
    35f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    35f8:	c3                   	ret
    35f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003600 <__do_global_dtors_aux>:
    3600:	f3 0f 1e fa          	endbr64
    3604:	80 3d 21 6a 00 00 00 	cmpb   $0x0,0x6a21(%rip)        # a02c <completed.0>
    360b:	75 2b                	jne    3638 <__do_global_dtors_aux+0x38>
    360d:	55                   	push   %rbp
    360e:	48 83 3d e2 69 00 00 00 	cmpq   $0x0,0x69e2(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3616:	48 89 e5             	mov    %rsp,%rbp
    3619:	74 0c                	je     3627 <__do_global_dtors_aux+0x27>
    361b:	48 8b 3d e6 69 00 00 	mov    0x69e6(%rip),%rdi        # a008 <__dso_handle>
    3622:	e8 a9 ec ff ff       	call   22d0 <__cxa_finalize@plt>
    3627:	e8 64 ff ff ff       	call   3590 <deregister_tm_clones>
    362c:	c6 05 f9 69 00 00 01 	movb   $0x1,0x69f9(%rip)        # a02c <completed.0>
    3633:	5d                   	pop    %rbp
    3634:	c3                   	ret
    3635:	0f 1f 00             	nopl   (%rax)
    3638:	c3                   	ret
    3639:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003640 <frame_dummy>:
    3640:	f3 0f 1e fa          	endbr64
    3644:	e9 77 ff ff ff       	jmp    35c0 <register_tm_clones>
    3649:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003650 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3650:	f3 0f 1e fa          	endbr64
    3654:	55                   	push   %rbp
    3655:	48 89 e5             	mov    %rsp,%rbp
    3658:	ff 15 8a 69 00 00    	call   *0x698a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  struct ProtectedState *protected = data->thread->protected_state;
    365e:	48 8b 87 a8 00 00 00 	mov    0xa8(%rdi),%rax
    3665:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    3669:	48 83 87 90 00 00 00 01 	addq   $0x1,0x90(%rdi)
  if (protected->balance > 0) {
    3671:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    3675:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3679:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3680:	48 85 c9             	test   %rcx,%rcx
    3683:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    368a:	48 0f 4f d6          	cmovg  %rsi,%rdx
    368e:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3692:	31 c0                	xor    %eax,%eax
    3694:	5d                   	pop    %rbp
    3695:	c3                   	ret
    3696:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000036a0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    36a0:	f3 0f 1e fa          	endbr64
    36a4:	55                   	push   %rbp
    36a5:	48 89 e5             	mov    %rsp,%rbp
    36a8:	ff 15 3a 69 00 00    	call   *0x693a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    for (int x = 0 ; x < data->task_count ; x++) {
    36ae:	48 63 87 bc 00 00 00 	movslq 0xbc(%rdi),%rax
    36b5:	85 c0                	test   %eax,%eax
    36b7:	7e 4d                	jle    3706 <barriered_reset+0x66>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    36b9:	48 8b 8f a8 00 00 00 	mov    0xa8(%rdi),%rcx
    36c0:	48 63 b7 b0 00 00 00 	movslq 0xb0(%rdi),%rsi
    36c7:	48 8b 51 10          	mov    0x10(%rcx),%rdx
    36cb:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    36cf:	48 8b 71 28          	mov    0x28(%rcx),%rsi
    36d3:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
    36d7:	31 c0                	xor    %eax,%eax
    36d9:	48 c1 e1 07          	shl    $0x7,%rcx
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    36dd:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    36e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    36e8:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    36f0:	c7 84 06 b8 00 00 00 01 00 00 00 	movl   $0x1,0xb8(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    36fb:	48 05 80 01 00 00    	add    $0x180,%rax
    3701:	48 39 c1             	cmp    %rax,%rcx
    3704:	75 e2                	jne    36e8 <barriered_reset+0x48>
  asm volatile ("sfence" ::: "memory");
    3706:	0f ae f8             	sfence
}
    3709:	31 c0                	xor    %eax,%eax
    370b:	5d                   	pop    %rbp
    370c:	c3                   	ret
    370d:	0f 1f 00             	nopl   (%rax)

0000000000003710 <barriered_thread>:
void* barriered_thread(void *arg) {
    3710:	f3 0f 1e fa          	endbr64
    3714:	55                   	push   %rbp
    3715:	48 89 e5             	mov    %rsp,%rbp
    3718:	41 55                	push   %r13
    371a:	41 54                	push   %r12
    371c:	53                   	push   %rbx
    371d:	48 83 ec 08          	sub    $0x8,%rsp
    3721:	ff 15 c1 68 00 00    	call   *0x68c1(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  while (data->running == 1) {
    3727:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
void* barriered_thread(void *arg) {
    372b:	49 89 fd             	mov    %rdi,%r13
  while (data->running == 1) {
    372e:	0f 85 79 01 00 00    	jne    38ad <barriered_thread+0x19d>
    if (t >= data->task_count) {
    3734:	44 8b 47 30          	mov    0x30(%rdi),%r8d
  int waiting = 0;
    3738:	45 31 d2             	xor    %r10d,%r10d
  int t = 0;
    373b:	31 db                	xor    %ebx,%ebx
    373d:	0f 1f 00             	nopl   (%rax)
    if (t >= data->task_count) {
    3740:	44 39 c3             	cmp    %r8d,%ebx
    3743:	0f 8d 77 01 00 00    	jge    38c0 <barriered_thread+0x1b0>
    3749:	48 63 c3             	movslq %ebx,%rax
    374c:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
    3750:	49 c1 e4 07          	shl    $0x7,%r12
    3754:	eb 1d                	jmp    3773 <barriered_thread+0x63>
    3756:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (; t < data->task_count; t++) {
    3760:	83 c3 01             	add    $0x1,%ebx
    3763:	49 81 c4 80 01 00 00 	add    $0x180,%r12
    376a:	44 39 c3             	cmp    %r8d,%ebx
    376d:	0f 8d 2d 01 00 00    	jge    38a0 <barriered_thread+0x190>
      if (data->tasks[t].available == 1) {
    3773:	49 8b 45 28          	mov    0x28(%r13),%rax
    3777:	4a 8d 14 20          	lea    (%rax,%r12,1),%rdx
    377b:	83 ba b8 00 00 00 01 	cmpl   $0x1,0xb8(%rdx)
    3782:	75 dc                	jne    3760 <barriered_thread+0x50>
        if (t > 0) {
    3784:	85 db                	test   %ebx,%ebx
    3786:	0f 8e 4c 01 00 00    	jle    38d8 <barriered_thread+0x1c8>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    378c:	45 8b 4d 18          	mov    0x18(%r13),%r9d
          previous = t - 1;
    3790:	8d 4b ff             	lea    -0x1(%rbx),%ecx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3793:	45 85 c9             	test   %r9d,%r9d
    3796:	0f 8e eb 01 00 00    	jle    3987 <barriered_thread+0x277>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    379c:	48 63 c1             	movslq %ecx,%rax
    379f:	8b ba 80 00 00 00    	mov    0x80(%rdx),%edi
    37a5:	49 63 d1             	movslq %r9d,%rdx
        int arrived = 0; 
    37a8:	45 31 db             	xor    %r11d,%r11d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    37ab:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
    37af:	49 8b 45 10          	mov    0x10(%r13),%rax
    37b3:	48 c1 e1 07          	shl    $0x7,%rcx
    37b7:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    37bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    37c0:	48 8b 10             	mov    (%rax),%rdx
    37c3:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    37c7:	3b bc 0a 80 00 00 00 	cmp    0x80(%rdx,%rcx,1),%edi
    37ce:	75 04                	jne    37d4 <barriered_thread+0xc4>
            arrived++;
    37d0:	41 83 c3 01          	add    $0x1,%r11d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    37d4:	48 83 c0 08          	add    $0x8,%rax
    37d8:	48 39 f0             	cmp    %rsi,%rax
    37db:	75 e3                	jne    37c0 <barriered_thread+0xb0>
        if (arrived == 0 || arrived == data->thread_count) {
    37dd:	45 39 cb             	cmp    %r9d,%r11d
    37e0:	74 09                	je     37eb <barriered_thread+0xdb>
    37e2:	45 85 db             	test   %r11d,%r11d
    37e5:	0f 85 b5 00 00 00    	jne    38a0 <barriered_thread+0x190>
          if (waiting == 1) {
    37eb:	41 83 fa 01          	cmp    $0x1,%r10d
    37ef:	0f 84 03 01 00 00    	je     38f8 <barriered_thread+0x1e8>
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    37f5:	85 db                	test   %ebx,%ebx
    37f7:	75 0e                	jne    3807 <barriered_thread+0xf7>
    37f9:	49 8b 75 70          	mov    0x70(%r13),%rsi
    37fd:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    3801:	0f 8c 69 01 00 00    	jl     3970 <barriered_thread+0x260>
    3807:	49 8b 45 28          	mov    0x28(%r13),%rax
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    380b:	49 63 4d 00          	movslq 0x0(%r13),%rcx
    380f:	49 8b 55 10          	mov    0x10(%r13),%rdx
          data->tasks[t].available = 0;
    3813:	4c 01 e0             	add    %r12,%rax
    3816:	c7 80 b8 00 00 00 00 00 00 00 	movl   $0x0,0xb8(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3820:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    3824:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
    3828:	4c 01 e7             	add    %r12,%rdi
    382b:	ff 90 98 00 00 00    	call   *0x98(%rax)
          data->tasks[t].arrived++;
    3831:	49 8b 45 28          	mov    0x28(%r13),%rax
    3835:	4c 01 e0             	add    %r12,%rax
    3838:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    383f:	41 8b 45 30          	mov    0x30(%r13),%eax
          data->iteration_count++;
    3843:	49 83 45 68 01       	addq   $0x1,0x68(%r13)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3848:	83 e8 01             	sub    $0x1,%eax
    384b:	39 d8                	cmp    %ebx,%eax
    384d:	0f 84 ed 00 00 00    	je     3940 <barriered_thread+0x230>
          asm volatile ("sfence" ::: "memory");
    3853:	0f ae f8             	sfence
            data->task_snapshot[data->task_timestamp_count].task = t;
    3856:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    385d:	bf 04 00 00 00       	mov    $0x4,%edi
    for (; t < data->task_count; t++) {
    3862:	49 81 c4 80 01 00 00 	add    $0x180,%r12
            data->task_snapshot[data->task_timestamp_count].task = t;
    3869:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    386d:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    3874:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3878:	89 5e 20             	mov    %ebx,0x20(%rsi)
    for (; t < data->task_count; t++) {
    387b:	83 c3 01             	add    $0x1,%ebx
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    387e:	e8 ad ea ff ff       	call   2330 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3883:	45 8b 45 30          	mov    0x30(%r13),%r8d
            waiting = 1;
    3887:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    for (; t < data->task_count; t++) {
    388d:	44 39 c3             	cmp    %r8d,%ebx
    3890:	0f 8c dd fe ff ff    	jl     3773 <barriered_thread+0x63>
    3896:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  while (data->running == 1) {
    38a0:	41 8b 45 34          	mov    0x34(%r13),%eax
    38a4:	83 f8 01             	cmp    $0x1,%eax
    38a7:	0f 84 93 fe ff ff    	je     3740 <barriered_thread+0x30>
}
    38ad:	48 83 c4 08          	add    $0x8,%rsp
    38b1:	31 c0                	xor    %eax,%eax
    38b3:	5b                   	pop    %rbx
    38b4:	41 5c                	pop    %r12
    38b6:	41 5d                	pop    %r13
    38b8:	5d                   	pop    %rbp
    38b9:	c3                   	ret
    38ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->cycles++;
    38c0:	49 83 85 98 00 00 00 01 	addq   $0x1,0x98(%r13)
    for (; t < data->task_count; t++) {
    38c8:	45 85 c0             	test   %r8d,%r8d
    38cb:	7e f3                	jle    38c0 <barriered_thread+0x1b0>
    38cd:	31 db                	xor    %ebx,%ebx
    38cf:	e9 75 fe ff ff       	jmp    3749 <barriered_thread+0x39>
    38d4:	0f 1f 40 00          	nopl   0x0(%rax)
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    38d8:	45 8b 4d 18          	mov    0x18(%r13),%r9d
          previous = data->task_count - 1;
    38dc:	41 8d 48 ff          	lea    -0x1(%r8),%ecx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    38e0:	45 85 c9             	test   %r9d,%r9d
    38e3:	0f 8f b3 fe ff ff    	jg     379c <barriered_thread+0x8c>
          if (waiting == 1) {
    38e9:	41 83 fa 01          	cmp    $0x1,%r10d
    38ed:	0f 85 02 ff ff ff    	jne    37f5 <barriered_thread+0xe5>
    38f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    38f8:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    38ff:	bf 04 00 00 00       	mov    $0x4,%edi
    3904:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3908:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    390f:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3914:	e8 17 ea ff ff       	call   2330 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3919:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    3920:	48 83 c0 01          	add    $0x1,%rax
    3924:	48 99                	cqto
    3926:	49 f7 bd 90 00 00 00 	idivq  0x90(%r13)
    392d:	49 89 95 88 00 00 00 	mov    %rdx,0x88(%r13)
            waiting = 0; 
    3934:	e9 bc fe ff ff       	jmp    37f5 <barriered_thread+0xe5>
    3939:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3940:	49 8b 75 70          	mov    0x70(%r13),%rsi
    3944:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    3948:	0f 8d 05 ff ff ff    	jge    3853 <barriered_thread+0x143>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    394e:	48 c1 e6 04          	shl    $0x4,%rsi
    3952:	bf 04 00 00 00       	mov    $0x4,%edi
    3957:	49 03 75 60          	add    0x60(%r13),%rsi
    395b:	e8 d0 e9 ff ff       	call   2330 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3960:	49 83 45 70 01       	addq   $0x1,0x70(%r13)
    3965:	e9 e9 fe ff ff       	jmp    3853 <barriered_thread+0x143>
    396a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3970:	48 c1 e6 04          	shl    $0x4,%rsi
    3974:	bf 04 00 00 00       	mov    $0x4,%edi
    3979:	49 03 75 58          	add    0x58(%r13),%rsi
    397d:	e8 ae e9 ff ff       	call   2330 <clock_gettime@plt>
    3982:	e9 80 fe ff ff       	jmp    3807 <barriered_thread+0xf7>
          if (waiting == 1) {
    3987:	41 83 fa 01          	cmp    $0x1,%r10d
    398b:	0f 85 7a fe ff ff    	jne    380b <barriered_thread+0xfb>
    3991:	e9 62 ff ff ff       	jmp    38f8 <barriered_thread+0x1e8>
    3996:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000039a0 <external_thread>:
void * external_thread(void *arg) {
    39a0:	f3 0f 1e fa          	endbr64
    39a4:	55                   	push   %rbp
    39a5:	48 89 e5             	mov    %rsp,%rbp
    39a8:	41 56                	push   %r14
    39aa:	41 55                	push   %r13
    39ac:	41 54                	push   %r12
    39ae:	53                   	push   %rbx
    39af:	48 83 ec 30          	sub    $0x30,%rsp
    39b3:	ff 15 2f 66 00 00    	call   *0x662f(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  struct timespec req = {
    39b9:	66 0f 6f 05 7f 3f 00 00 	movdqa 0x3f7f(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
void * external_thread(void *arg) {
    39c1:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    39ca:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    39ce:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    39d0:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
void * external_thread(void *arg) {
    39d4:	49 89 fe             	mov    %rdi,%r14
  struct timespec req = {
    39d7:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
  while (data->running == 1) {
    39db:	75 5f                	jne    3a3c <external_thread+0x9c>
    39dd:	4c 8d 65 c0          	lea    -0x40(%rbp),%r12
    39e1:	48 8d 5d b0          	lea    -0x50(%rbp),%rbx
        data->buffers->buffer[x].data = "Hello world";
    39e5:	4c 8d 2d 18 36 00 00 	lea    0x3618(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
    39ec:	0f 1f 40 00          	nopl   0x0(%rax)
    nanosleep(&req , &rem);
    39f0:	4c 89 e6             	mov    %r12,%rsi
    39f3:	48 89 df             	mov    %rbx,%rdi
    39f6:	e8 75 e9 ff ff       	call   2370 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    39fb:	49 8b 46 40          	mov    0x40(%r14),%rax
    39ff:	48 63 10             	movslq (%rax),%rdx
    3a02:	85 d2                	test   %edx,%edx
    3a04:	7e 2c                	jle    3a32 <external_thread+0x92>
    3a06:	48 8b 40 08          	mov    0x8(%rax),%rax
    3a0a:	48 c1 e2 04          	shl    $0x4,%rdx
    3a0e:	48 01 c2             	add    %rax,%rdx
    3a11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    3a18:	8b 48 08             	mov    0x8(%rax),%ecx
    3a1b:	85 c9                	test   %ecx,%ecx
    3a1d:	75 0a                	jne    3a29 <external_thread+0x89>
        data->buffers->buffer[x].data = "Hello world";
    3a1f:	4c 89 28             	mov    %r13,(%rax)
        data->buffers->buffer[x].available = 1;
    3a22:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3a29:	48 83 c0 10          	add    $0x10,%rax
    3a2d:	48 39 c2             	cmp    %rax,%rdx
    3a30:	75 e6                	jne    3a18 <external_thread+0x78>
    asm volatile ("mfence" ::: "memory");
    3a32:	0f ae f0             	mfence
  while (data->running == 1) {
    3a35:	41 83 7e 34 01       	cmpl   $0x1,0x34(%r14)
    3a3a:	74 b4                	je     39f0 <external_thread+0x50>
}
    3a3c:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    3a40:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3a49:	75 0f                	jne    3a5a <external_thread+0xba>
    3a4b:	48 83 c4 30          	add    $0x30,%rsp
    3a4f:	31 c0                	xor    %eax,%eax
    3a51:	5b                   	pop    %rbx
    3a52:	41 5c                	pop    %r12
    3a54:	41 5d                	pop    %r13
    3a56:	41 5e                	pop    %r14
    3a58:	5d                   	pop    %rbp
    3a59:	c3                   	ret
    3a5a:	e8 f1 e8 ff ff       	call   2350 <__stack_chk_fail@plt>
    3a5f:	90                   	nop

0000000000003a60 <timer_thread>:
void* timer_thread(void *arg) {
    3a60:	f3 0f 1e fa          	endbr64
    3a64:	55                   	push   %rbp
    3a65:	48 89 e5             	mov    %rsp,%rbp
    3a68:	41 57                	push   %r15
    3a6a:	41 56                	push   %r14
    3a6c:	41 55                	push   %r13
    3a6e:	41 54                	push   %r12
    3a70:	53                   	push   %rbx
    3a71:	48 83 ec 68          	sub    $0x68,%rsp
    3a75:	ff 15 6d 65 00 00    	call   *0x656d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    3a7b:	48 8d 35 8e 35 00 00 	lea    0x358e(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3a82:	8b 17                	mov    (%rdi),%edx
    3a84:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3a8d:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    3a91:	31 c0                	xor    %eax,%eax
    3a93:	49 89 fe             	mov    %rdi,%r14
    3a96:	bf 01 00 00 00       	mov    $0x1,%edi
    3a9b:	e8 e0 e9 ff ff       	call   2480 <__printf_chk@plt>
  struct timespec preempt = {
    3aa0:	66 0f 6f 05 98 3e 00 00 	movdqa 0x3e98(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3aa8:	ba 88 13 00 00       	mov    $0x1388,%edx
    3aad:	31 c0                	xor    %eax,%eax
    3aaf:	48 8d 35 6c 35 00 00 	lea    0x356c(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3ab6:	bf 01 00 00 00       	mov    $0x1,%edi
    3abb:	0f 29 45 90          	movaps %xmm0,-0x70(%rbp)
    3abf:	e8 bc e9 ff ff       	call   2480 <__printf_chk@plt>
  while (data->running && n < times) {
    3ac4:	41 8b 46 34          	mov    0x34(%r14),%eax
    3ac8:	89 85 7c ff ff ff    	mov    %eax,-0x84(%rbp)
    3ace:	85 c0                	test   %eax,%eax
    3ad0:	0f 84 b6 00 00 00    	je     3b8c <timer_thread+0x12c>
  int n = 0;
    3ad6:	45 31 ff             	xor    %r15d,%r15d
    3ad9:	4c 8d 6d 80          	lea    -0x80(%rbp),%r13
    3add:	4c 8d 65 90          	lea    -0x70(%rbp),%r12
    y++;
    3ae1:	31 db                	xor    %ebx,%ebx
  int y = 0;
    3ae3:	c7 85 7c ff ff ff 00 00 00 00 	movl   $0x0,-0x84(%rbp)
    nanosleep(&preempt , &rem2);
    3aed:	4c 89 e7             	mov    %r12,%rdi
    3af0:	4c 89 ee             	mov    %r13,%rsi
    n++;
    3af3:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3af7:	e8 74 e8 ff ff       	call   2370 <nanosleep@plt>
    y++;
    3afc:	8b bd 7c ff ff ff    	mov    -0x84(%rbp),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b02:	49 63 46 18          	movslq 0x18(%r14),%rax
    y++;
    3b06:	83 c7 01             	add    $0x1,%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b09:	85 c0                	test   %eax,%eax
    3b0b:	7e 54                	jle    3b61 <timer_thread+0x101>
        data->threads[x]->tasks[y].scheduled = 0;
    3b0d:	48 63 95 7c ff ff ff 	movslq -0x84(%rbp),%rdx
    3b14:	49 8b 4e 10          	mov    0x10(%r14),%rcx
    3b18:	4c 8d 04 52          	lea    (%rdx,%rdx,2),%r8
    3b1c:	4c 8d 14 c1          	lea    (%rcx,%rax,8),%r10
    3b20:	49 c1 e0 07          	shl    $0x7,%r8
    3b24:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3b28:	4c 8b 09             	mov    (%rcx),%r9
    3b2b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b2d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3b31:	99                   	cltd
    3b32:	41 f7 79 30          	idivl  0x30(%r9)
        data->threads[x]->tasks[next].scheduled = 1;
    3b36:	49 8b 71 28          	mov    0x28(%r9),%rsi
    3b3a:	48 63 d2             	movslq %edx,%rdx
    3b3d:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
    3b41:	48 c1 e0 07          	shl    $0x7,%rax
    3b45:	c7 84 06 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rsi,%rax,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3b50:	42 c7 84 06 c0 00 00 00 00 00 00 00 	movl   $0x0,0xc0(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b5c:	49 39 ca             	cmp    %rcx,%r10
    3b5f:	75 c7                	jne    3b28 <timer_thread+0xc8>
    asm volatile ("mfence" ::: "memory");
    3b61:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3b64:	49 8b 46 10          	mov    0x10(%r14),%rax
  while (data->running && n < times) {
    3b68:	41 8b 56 34          	mov    0x34(%r14),%edx
    if (y >= data->threads[0]->task_count) {
    3b6c:	48 8b 00             	mov    (%rax),%rax
    y++;
    3b6f:	39 78 30             	cmp    %edi,0x30(%rax)
    3b72:	0f 4e fb             	cmovle %ebx,%edi
    3b75:	89 bd 7c ff ff ff    	mov    %edi,-0x84(%rbp)
  while (data->running && n < times) {
    3b7b:	85 d2                	test   %edx,%edx
    3b7d:	74 0d                	je     3b8c <timer_thread+0x12c>
    3b7f:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    3b86:	0f 85 61 ff ff ff    	jne    3aed <timer_thread+0x8d>
    3b8c:	48 8d 3d a5 34 00 00 	lea    0x34a5(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3b93:	e8 78 e7 ff ff       	call   2310 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b98:	49 63 56 1c          	movslq 0x1c(%r14),%rdx
    3b9c:	85 d2                	test   %edx,%edx
    3b9e:	0f 8e 81 00 00 00    	jle    3c25 <timer_thread+0x1c5>
    for (int y = 0 ; y < data->task_count ; y++) {
    3ba4:	49 63 46 30          	movslq 0x30(%r14),%rax
    3ba8:	85 c0                	test   %eax,%eax
    3baa:	7e 79                	jle    3c25 <timer_thread+0x1c5>
    3bac:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
      data->threads[x]->tasks[y].sending = 0;
    3bb0:	4d 8b 56 10          	mov    0x10(%r14),%r10
    3bb4:	48 8d 34 d5 00 00 00 00 	lea    0x0(,%rdx,8),%rsi
    3bbc:	31 c9                	xor    %ecx,%ecx
    3bbe:	48 c1 e0 07          	shl    $0x7,%rax
    3bc2:	4c 8d 80 f8 00 00 00 	lea    0xf8(%rax),%r8
    3bc9:	49 8b 04 0a          	mov    (%r10,%rcx,1),%rax
    3bcd:	48 8b 78 28          	mov    0x28(%rax),%rdi
    3bd1:	4a 8d 14 07          	lea    (%rdi,%r8,1),%rdx
    3bd5:	48 8d 87 f8 00 00 00 	lea    0xf8(%rdi),%rax
    3bdc:	49 89 d3             	mov    %rdx,%r11
    3bdf:	49 29 c3             	sub    %rax,%r11
    3be2:	41 81 e3 80 00 00 00 	and    $0x80,%r11d
    3be9:	74 16                	je     3c01 <timer_thread+0x1a1>
    for (int y = 0 ; y < data->task_count ; y++) {
    3beb:	48 8d 87 78 02 00 00 	lea    0x278(%rdi),%rax
      data->threads[x]->tasks[y].sending = 0;
    3bf2:	c7 87 f8 00 00 00 00 00 00 00 	movl   $0x0,0xf8(%rdi)
    for (int y = 0 ; y < data->task_count ; y++) {
    3bfc:	48 39 c2             	cmp    %rax,%rdx
    3bff:	74 1b                	je     3c1c <timer_thread+0x1bc>
      data->threads[x]->tasks[y].sending = 0;
    3c01:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3c07:	48 05 00 03 00 00    	add    $0x300,%rax
      data->threads[x]->tasks[y].sending = 0;
    3c0d:	c7 80 80 fe ff ff 00 00 00 00 	movl   $0x0,-0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3c17:	48 39 c2             	cmp    %rax,%rdx
    3c1a:	75 e5                	jne    3c01 <timer_thread+0x1a1>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c1c:	48 83 c1 08          	add    $0x8,%rcx
    3c20:	48 39 ce             	cmp    %rcx,%rsi
    3c23:	75 a4                	jne    3bc9 <timer_thread+0x169>
  asm volatile ("mfence" ::: "memory");
    3c25:	0f ae f0             	mfence
  struct timespec drain = {
    3c28:	66 0f 6f 05 20 3d 00 00 	movdqa 0x3d20(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3c30:	4c 8d 25 26 34 00 00 	lea    0x3426(%rip),%r12        # 705d <_IO_stdin_used+0x5d>
    3c37:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
    y++;
    3c3b:	8b 9d 7c ff ff ff    	mov    -0x84(%rbp),%ebx
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c41:	49 63 46 18          	movslq 0x18(%r14),%rax
    y++;
    3c45:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c48:	85 c0                	test   %eax,%eax
    3c4a:	7e 54                	jle    3ca0 <timer_thread+0x240>
        data->threads[x]->tasks[y].scheduled = 0;
    3c4c:	48 63 95 7c ff ff ff 	movslq -0x84(%rbp),%rdx
    3c53:	49 8b 4e 10          	mov    0x10(%r14),%rcx
    3c57:	4c 8d 04 52          	lea    (%rdx,%rdx,2),%r8
    3c5b:	4c 8d 14 c1          	lea    (%rcx,%rax,8),%r10
    3c5f:	49 c1 e0 07          	shl    $0x7,%r8
    3c63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3c68:	48 8b 19             	mov    (%rcx),%rbx
    3c6b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c6d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3c71:	99                   	cltd
    3c72:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3c75:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3c79:	48 63 c2             	movslq %edx,%rax
    3c7c:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    3c80:	48 c1 e0 07          	shl    $0x7,%rax
    3c84:	c7 84 06 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rsi,%rax,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3c8f:	42 c7 84 06 c0 00 00 00 00 00 00 00 	movl   $0x0,0xc0(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c9b:	49 39 ca             	cmp    %rcx,%r10
    3c9e:	75 c8                	jne    3c68 <timer_thread+0x208>
    asm volatile ("mfence" ::: "memory");
    3ca0:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3ca3:	49 8b 46 10          	mov    0x10(%r14),%rax
    3ca7:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3caa:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3cad:	ba 00 00 00 00       	mov    $0x0,%edx
    3cb2:	0f 4f d7             	cmovg  %edi,%edx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3cb5:	41 8b 7e 20          	mov    0x20(%r14),%edi
    y++;
    3cb9:	89 95 7c ff ff ff    	mov    %edx,-0x84(%rbp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3cbf:	85 ff                	test   %edi,%edi
    3cc1:	0f 8e b7 00 00 00    	jle    3d7e <timer_thread+0x31e>
    3cc7:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    3cca:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    3cd0:	4a 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbx
            all_empty = 0;
    3cd8:	45 31 ff             	xor    %r15d,%r15d
    3cdb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3ce0:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3ce4:	4b 8d 04 7f          	lea    (%r15,%r15,2),%rax
    3ce8:	48 c1 e0 07          	shl    $0x7,%rax
    3cec:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3cf0:	31 d2                	xor    %edx,%edx
    3cf2:	48 8b 80 e8 00 00 00 	mov    0xe8(%rax),%rax
    3cf9:	eb 15                	jmp    3d10 <timer_thread+0x2b0>
    3cfb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3d00:	4d 85 c0             	test   %r8,%r8
    3d03:	7f 1f                	jg     3d24 <timer_thread+0x2c4>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3d05:	83 c2 01             	add    $0x1,%edx
    3d08:	48 83 c0 20          	add    $0x20,%rax
    3d0c:	39 fa                	cmp    %edi,%edx
    3d0e:	74 2a                	je     3d3a <timer_thread+0x2da>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3d10:	48 8b 08             	mov    (%rax),%rcx
    3d13:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3d17:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3d1b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3d1f:	48 85 c9             	test   %rcx,%rcx
    3d22:	7e dc                	jle    3d00 <timer_thread+0x2a0>
    3d24:	bf 01 00 00 00       	mov    $0x1,%edi
    3d29:	4c 89 e6             	mov    %r12,%rsi
    3d2c:	31 c0                	xor    %eax,%eax
    3d2e:	e8 4d e7 ff ff       	call   2480 <__printf_chk@plt>
            break;
    3d33:	41 8b 7e 20          	mov    0x20(%r14),%edi
            all_empty = 0;
    3d37:	45 31 d2             	xor    %r10d,%r10d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3d3a:	49 83 c7 01          	add    $0x1,%r15
    3d3e:	44 39 ff             	cmp    %r15d,%edi
    3d41:	7e 0d                	jle    3d50 <timer_thread+0x2f0>
    3d43:	49 8b 46 10          	mov    0x10(%r14),%rax
    3d47:	eb 97                	jmp    3ce0 <timer_thread+0x280>
    3d49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3d50:	49 83 c5 01          	add    $0x1,%r13
    3d54:	44 39 ef             	cmp    %r13d,%edi
    3d57:	7e 0d                	jle    3d66 <timer_thread+0x306>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3d59:	85 ff                	test   %edi,%edi
    3d5b:	7e 09                	jle    3d66 <timer_thread+0x306>
    3d5d:	49 8b 46 10          	mov    0x10(%r14),%rax
    3d61:	e9 6a ff ff ff       	jmp    3cd0 <timer_thread+0x270>
    if (all_empty == 1) {
    3d66:	41 83 fa 01          	cmp    $0x1,%r10d
    3d6a:	74 12                	je     3d7e <timer_thread+0x31e>
      nanosleep(&drain , &drainrem);
    3d6c:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    3d70:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
    3d74:	e8 f7 e5 ff ff       	call   2370 <nanosleep@plt>
    3d79:	e9 bd fe ff ff       	jmp    3c3b <timer_thread+0x1db>
    3d7e:	48 8d 3d cf 32 00 00 	lea    0x32cf(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3d85:	e8 86 e5 ff ff       	call   2310 <puts@plt>
  while (data->running) {
    3d8a:	41 8b 46 34          	mov    0x34(%r14),%eax
    3d8e:	85 c0                	test   %eax,%eax
    3d90:	0f 84 e5 00 00 00    	je     3e7b <timer_thread+0x41b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d96:	41 8b 4e 1c          	mov    0x1c(%r14),%ecx
    3d9a:	85 c9                	test   %ecx,%ecx
    3d9c:	7e 2f                	jle    3dcd <timer_thread+0x36d>
    3d9e:	49 8b 46 10          	mov    0x10(%r14),%rax
    3da2:	31 db                	xor    %ebx,%ebx
    3da4:	4c 8d 25 c3 32 00 00 	lea    0x32c3(%rip),%r12        # 706e <_IO_stdin_used+0x6e>
    3dab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->threads[x]->running = 0;
    3db0:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3db4:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3db8:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3dbf:	0f 84 e2 00 00 00    	je     3ea7 <timer_thread+0x447>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3dc5:	48 83 c3 01          	add    $0x1,%rbx
    3dc9:	39 d9                	cmp    %ebx,%ecx
    3dcb:	7f e3                	jg     3db0 <timer_thread+0x350>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3dcd:	49 63 46 18          	movslq 0x18(%r14),%rax
    3dd1:	85 c0                	test   %eax,%eax
    3dd3:	0f 8e 8b 00 00 00    	jle    3e64 <timer_thread+0x404>
      for (int y = 0 ; y < data->task_count ; y++) {
    3dd9:	41 8b 56 30          	mov    0x30(%r14),%edx
    3ddd:	85 d2                	test   %edx,%edx
    3ddf:	0f 8e 7f 00 00 00    	jle    3e64 <timer_thread+0x404>
    3de5:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
    3ded:	48 63 c2             	movslq %edx,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3df0:	4d 8b 5e 10          	mov    0x10(%r14),%r11
    3df4:	31 c9                	xor    %ecx,%ecx
    3df6:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    3dfa:	48 c1 e0 07          	shl    $0x7,%rax
    3dfe:	4c 8d 90 c0 00 00 00 	lea    0xc0(%rax),%r10
    3e05:	0f 1f 00             	nopl   (%rax)
    3e08:	49 8b 04 0b          	mov    (%r11,%rcx,1),%rax
    3e0c:	48 8b 70 28          	mov    0x28(%rax),%rsi
    3e10:	4a 8d 14 16          	lea    (%rsi,%r10,1),%rdx
    3e14:	48 8d 86 c0 00 00 00 	lea    0xc0(%rsi),%rax
    3e1b:	48 89 d7             	mov    %rdx,%rdi
    3e1e:	48 29 c7             	sub    %rax,%rdi
    3e21:	81 e7 80 00 00 00    	and    $0x80,%edi
    3e27:	74 17                	je     3e40 <timer_thread+0x3e0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3e29:	48 8d 86 40 02 00 00 	lea    0x240(%rsi),%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3e30:	c7 86 c0 00 00 00 00 00 00 00 	movl   $0x0,0xc0(%rsi)
      for (int y = 0 ; y < data->task_count ; y++) {
    3e3a:	48 39 d0             	cmp    %rdx,%rax
    3e3d:	74 1c                	je     3e5b <timer_thread+0x3fb>
    3e3f:	90                   	nop
        data->threads[x]->tasks[y].scheduled = 0;
    3e40:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3e46:	48 05 00 03 00 00    	add    $0x300,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3e4c:	c7 80 80 fe ff ff 00 00 00 00 	movl   $0x0,-0x180(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3e56:	48 39 d0             	cmp    %rdx,%rax
    3e59:	75 e5                	jne    3e40 <timer_thread+0x3e0>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3e5b:	48 83 c1 08          	add    $0x8,%rcx
    3e5f:	4c 39 c1             	cmp    %r8,%rcx
    3e62:	75 a4                	jne    3e08 <timer_thread+0x3a8>
    asm volatile ("mfence" ::: "memory");
    3e64:	0f ae f0             	mfence
    3e67:	48 8d 3d 12 32 00 00 	lea    0x3212(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3e6e:	e8 9d e4 ff ff       	call   2310 <puts@plt>
    data->running = 0;
    3e73:	41 c7 46 34 00 00 00 00 	movl   $0x0,0x34(%r14)
    3e7b:	48 8d 3d 05 32 00 00 	lea    0x3205(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3e82:	e8 89 e4 ff ff       	call   2310 <puts@plt>
}
    3e87:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    3e8b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3e94:	75 47                	jne    3edd <timer_thread+0x47d>
    3e96:	48 83 c4 68          	add    $0x68,%rsp
    3e9a:	31 c0                	xor    %eax,%eax
    3e9c:	5b                   	pop    %rbx
    3e9d:	41 5c                	pop    %r12
    3e9f:	41 5d                	pop    %r13
    3ea1:	41 5e                	pop    %r14
    3ea3:	41 5f                	pop    %r15
    3ea5:	5d                   	pop    %rbp
    3ea6:	c3                   	ret
    3ea7:	4c 89 e7             	mov    %r12,%rdi
    3eaa:	e8 61 e4 ff ff       	call   2310 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3eaf:	49 8b 46 10          	mov    0x10(%r14),%rax
    3eb3:	be 01 00 00 00       	mov    $0x1,%esi
    3eb8:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ebc:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3ec0:	8b 78 50             	mov    0x50(%rax),%edi
    3ec3:	e8 68 e5 ff ff       	call   2430 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ec8:	41 8b 4e 1c          	mov    0x1c(%r14),%ecx
    3ecc:	39 d9                	cmp    %ebx,%ecx
    3ece:	0f 8e f9 fe ff ff    	jle    3dcd <timer_thread+0x36d>
    3ed4:	49 8b 46 10          	mov    0x10(%r14),%rax
    3ed8:	e9 d3 fe ff ff       	jmp    3db0 <timer_thread+0x350>
}
    3edd:	e8 6e e4 ff ff       	call   2350 <__stack_chk_fail@plt>
    3ee2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3eed:	0f 1f 00             	nopl   (%rax)

0000000000003ef0 <strtolower>:
void strtolower(char *str) {
    3ef0:	f3 0f 1e fa          	endbr64
    3ef4:	55                   	push   %rbp
    3ef5:	48 89 e5             	mov    %rsp,%rbp
    3ef8:	41 54                	push   %r12
    3efa:	53                   	push   %rbx
    3efb:	ff 15 e7 60 00 00    	call   *0x60e7(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    for (; *str; ++str)
    3f01:	48 0f be 1f          	movsbq (%rdi),%rbx
void strtolower(char *str) {
    3f05:	49 89 fc             	mov    %rdi,%r12
    for (; *str; ++str)
    3f08:	84 db                	test   %bl,%bl
    3f0a:	74 24                	je     3f30 <strtolower+0x40>
        *str = (char)tolower(*str);
    3f0c:	e8 3f e6 ff ff       	call   2550 <__ctype_tolower_loc@plt>
    3f11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3f18:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3f1b:	49 83 c4 01          	add    $0x1,%r12
        *str = (char)tolower(*str);
    3f1f:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3f22:	41 88 54 24 ff       	mov    %dl,-0x1(%r12)
    for (; *str; ++str)
    3f27:	49 0f be 1c 24       	movsbq (%r12),%rbx
    3f2c:	84 db                	test   %bl,%bl
    3f2e:	75 e8                	jne    3f18 <strtolower+0x28>
}
    3f30:	5b                   	pop    %rbx
    3f31:	41 5c                	pop    %r12
    3f33:	5d                   	pop    %rbp
    3f34:	c3                   	ret
    3f35:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003f40 <zh_malloc>:
void *zh_malloc(size_t size) {
    3f40:	f3 0f 1e fa          	endbr64
    3f44:	55                   	push   %rbp
    3f45:	48 89 e5             	mov    %rsp,%rbp
    3f48:	ff 15 9a 60 00 00    	call   *0x609a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    void *buf = malloc(size);
    3f4e:	e8 ed e4 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    3f53:	48 85 c0             	test   %rax,%rax
    3f56:	74 02                	je     3f5a <zh_malloc+0x1a>
}
    3f58:	5d                   	pop    %rbp
    3f59:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3f5a:	48 8b 0d bf 60 00 00 	mov    0x60bf(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    3f61:	ba 28 00 00 00       	mov    $0x28,%edx
    3f66:	be 01 00 00 00       	mov    $0x1,%esi
    3f6b:	48 8d 3d 96 34 00 00 	lea    0x3496(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    3f72:	e8 89 e5 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    3f77:	bf 01 00 00 00       	mov    $0x1,%edi
    3f7c:	e8 5f e5 ff ff       	call   24e0 <exit@plt>
    3f81:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3f8c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003f90 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3f90:	f3 0f 1e fa          	endbr64
    3f94:	55                   	push   %rbp
    3f95:	48 89 e5             	mov    %rsp,%rbp
    3f98:	53                   	push   %rbx
    3f99:	48 83 ec 08          	sub    $0x8,%rsp
    3f9d:	ff 15 45 60 00 00    	call   *0x6045(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    const char *dot = strrchr(filename, '.');
    3fa3:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3fa8:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3fab:	e8 d0 e3 ff ff       	call   2380 <strrchr@plt>
    if (!dot || dot == filename)
    3fb0:	48 85 c0             	test   %rax,%rax
    3fb3:	74 13                	je     3fc8 <get_filename_ext+0x38>
    3fb5:	48 39 c3             	cmp    %rax,%rbx
    3fb8:	74 0e                	je     3fc8 <get_filename_ext+0x38>
}
    3fba:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    return dot + 1;
    3fbe:	48 83 c0 01          	add    $0x1,%rax
}
    3fc2:	c9                   	leave
    3fc3:	c3                   	ret
    3fc4:	0f 1f 40 00          	nopl   0x0(%rax)
    3fc8:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
        return "";
    3fcc:	48 8d 05 fc 30 00 00 	lea    0x30fc(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    3fd3:	c9                   	leave
    3fd4:	c3                   	ret
    3fd5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003fe0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3fe0:	f3 0f 1e fa          	endbr64
    3fe4:	55                   	push   %rbp
    3fe5:	48 89 e5             	mov    %rsp,%rbp
    3fe8:	41 56                	push   %r14
    3fea:	41 55                	push   %r13
    3fec:	41 54                	push   %r12
    3fee:	53                   	push   %rbx
    3fef:	48 81 ec 10 08 00 00 	sub    $0x810,%rsp
    3ff6:	ff 15 ec 5f 00 00    	call   *0x5fec(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    3ffc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4005:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    4009:	31 c0                	xor    %eax,%eax
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    400b:	4c 8d ad d0 f7 ff ff 	lea    -0x830(%rbp),%r13
    4012:	49 89 f6             	mov    %rsi,%r14
    4015:	49 89 d4             	mov    %rdx,%r12
    4018:	48 89 fe             	mov    %rdi,%rsi
    401b:	ba 00 04 00 00       	mov    $0x400,%edx
    4020:	4c 89 ef             	mov    %r13,%rdi
    4023:	e8 38 e4 ff ff       	call   2460 <__strcpy_chk@plt>
    for (; *str; ++str)
    4028:	48 0f be 9d d0 f7 ff ff 	movsbq -0x830(%rbp),%rbx
    4030:	84 db                	test   %bl,%bl
    4032:	74 1e                	je     4052 <send_headers+0x72>
        *str = (char)tolower(*str);
    4034:	e8 17 e5 ff ff       	call   2550 <__ctype_tolower_loc@plt>
    4039:	48 8b 08             	mov    (%rax),%rcx
    403c:	4c 89 e8             	mov    %r13,%rax
    403f:	90                   	nop
    4040:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4043:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4047:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    404a:	48 0f be 18          	movsbq (%rax),%rbx
    404e:	84 db                	test   %bl,%bl
    4050:	75 ee                	jne    4040 <send_headers+0x60>
    void *buf = malloc(size);
    4052:	bf 11 00 00 00       	mov    $0x11,%edi
    4057:	e8 e4 e3 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    405c:	48 85 c0             	test   %rax,%rax
    405f:	0f 84 72 04 00 00    	je     44d7 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4065:	66 0f 6f 05 f3 38 00 00 	movdqa 0x38f3(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    406d:	49 89 04 24          	mov    %rax,(%r12)
    void *buf = malloc(size);
    4071:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4076:	49 c7 44 24 08 11 00 00 00 	movq   $0x11,0x8(%r12)
    407f:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4083:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4086:	e8 b5 e3 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    408b:	48 85 c0             	test   %rax,%rax
    408e:	0f 84 43 04 00 00    	je     44d7 <send_headers+0x4f7>
    4094:	66 0f 6f 05 d4 38 00 00 	movdqa 0x38d4(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    409c:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    const char *dot = strrchr(filename, '.');
    40a1:	4c 89 ef             	mov    %r13,%rdi
    40a4:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    40ae:	49 c7 44 24 18 17 00 00 00 	movq   $0x17,0x18(%r12)
    40b7:	0f 11 00             	movups %xmm0,(%rax)
    40ba:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    40be:	be 2e 00 00 00       	mov    $0x2e,%esi
    40c3:	e8 b8 e2 ff ff       	call   2380 <strrchr@plt>
    if (!dot || dot == filename)
    40c8:	48 85 c0             	test   %rax,%rax
    40cb:	0f 84 df 02 00 00    	je     43b0 <send_headers+0x3d0>
    40d1:	4c 39 e8             	cmp    %r13,%rax
    40d4:	0f 84 d6 02 00 00    	je     43b0 <send_headers+0x3d0>
    return dot + 1;
    40da:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    40de:	48 8d 3d b8 2f 00 00 	lea    0x2fb8(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    40e5:	48 89 de             	mov    %rbx,%rsi
    40e8:	e8 e3 e2 ff ff       	call   23d0 <strcmp@plt>
    40ed:	85 c0                	test   %eax,%eax
    40ef:	75 1e                	jne    410f <send_headers+0x12f>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40f1:	66 0f 6f 05 87 38 00 00 	movdqa 0x3887(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    40f9:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4100:	66 0f 6f 05 88 38 00 00 	movdqa 0x3888(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    4108:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("jpeg", file_ext) == 0)
    410f:	48 89 de             	mov    %rbx,%rsi
    4112:	48 8d 3d 88 2f 00 00 	lea    0x2f88(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    4119:	e8 b2 e2 ff ff       	call   23d0 <strcmp@plt>
    411e:	85 c0                	test   %eax,%eax
    4120:	75 1e                	jne    4140 <send_headers+0x160>
    4122:	66 0f 6f 05 56 38 00 00 	movdqa 0x3856(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    412a:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4131:	66 0f 6f 05 57 38 00 00 	movdqa 0x3857(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    4139:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("png", file_ext) == 0)
    4140:	48 89 de             	mov    %rbx,%rsi
    4143:	48 8d 3d 5c 2f 00 00 	lea    0x2f5c(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    414a:	e8 81 e2 ff ff       	call   23d0 <strcmp@plt>
    414f:	85 c0                	test   %eax,%eax
    4151:	0f 84 09 02 00 00    	je     4360 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4157:	48 89 de             	mov    %rbx,%rsi
    415a:	48 8d 3d 49 2f 00 00 	lea    0x2f49(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    4161:	e8 6a e2 ff ff       	call   23d0 <strcmp@plt>
    4166:	85 c0                	test   %eax,%eax
    4168:	0f 84 a2 02 00 00    	je     4410 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    416e:	48 89 de             	mov    %rbx,%rsi
    4171:	48 8d 3d 36 2f 00 00 	lea    0x2f36(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4178:	e8 53 e2 ff ff       	call   23d0 <strcmp@plt>
    417d:	85 c0                	test   %eax,%eax
    417f:	0f 84 63 02 00 00    	je     43e8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4185:	48 89 de             	mov    %rbx,%rsi
    4188:	48 8d 3d 62 2f 00 00 	lea    0x2f62(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    418f:	e8 3c e2 ff ff       	call   23d0 <strcmp@plt>
    4194:	85 c0                	test   %eax,%eax
    4196:	0f 84 24 02 00 00    	je     43c0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    419c:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    419f:	0f 84 53 01 00 00    	je     42f8 <send_headers+0x318>
    if (strcmp("css", file_ext) == 0)
    41a5:	48 89 de             	mov    %rbx,%rsi
    41a8:	48 8d 3d 03 2f 00 00 	lea    0x2f03(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    41af:	e8 1c e2 ff ff       	call   23d0 <strcmp@plt>
    41b4:	85 c0                	test   %eax,%eax
    41b6:	0f 84 a4 02 00 00    	je     4460 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    41bc:	48 89 de             	mov    %rbx,%rsi
    41bf:	48 8d 3d f0 2e 00 00 	lea    0x2ef0(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    41c6:	e8 05 e2 ff ff       	call   23d0 <strcmp@plt>
    41cb:	85 c0                	test   %eax,%eax
    41cd:	0f 84 65 02 00 00    	je     4438 <send_headers+0x458>
    slen = strlen(send_buffer);
    41d3:	4c 8d ad d0 fb ff ff 	lea    -0x430(%rbp),%r13
    41da:	4c 89 ef             	mov    %r13,%rdi
    41dd:	e8 5e e1 ff ff       	call   2340 <strlen@plt>
    void *buf = malloc(size);
    41e2:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    41e5:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    41e8:	e8 53 e2 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    41ed:	48 85 c0             	test   %rax,%rax
    41f0:	0f 84 e1 02 00 00    	je     44d7 <send_headers+0x4f7>
    iov[2].iov_base = zh_malloc(slen);
    41f6:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    iov[2].iov_len = slen;
    41fb:	49 89 5c 24 28       	mov    %rbx,0x28(%r12)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4200:	83 fb 08             	cmp    $0x8,%ebx
    4203:	0f 83 37 01 00 00    	jae    4340 <send_headers+0x360>
    4209:	f6 c3 04             	test   $0x4,%bl
    420c:	0f 85 71 02 00 00    	jne    4483 <send_headers+0x4a3>
    4212:	85 db                	test   %ebx,%ebx
    4214:	74 12                	je     4228 <send_headers+0x248>
    4216:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    421d:	88 10                	mov    %dl,(%rax)
    421f:	f6 c3 02             	test   $0x2,%bl
    4222:	0f 85 8b 02 00 00    	jne    44b3 <send_headers+0x4d3>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4228:	4d 89 f0             	mov    %r14,%r8
    422b:	48 8d 0d 88 2e 00 00 	lea    0x2e88(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    4232:	4c 89 ef             	mov    %r13,%rdi
    4235:	31 c0                	xor    %eax,%eax
    4237:	ba 00 04 00 00       	mov    $0x400,%edx
    423c:	be 01 00 00 00       	mov    $0x1,%esi
    4241:	e8 1a e3 ff ff       	call   2560 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4246:	4c 89 ef             	mov    %r13,%rdi
    4249:	e8 f2 e0 ff ff       	call   2340 <strlen@plt>
    void *buf = malloc(size);
    424e:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4251:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4254:	e8 e7 e1 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    4259:	48 85 c0             	test   %rax,%rax
    425c:	0f 84 75 02 00 00    	je     44d7 <send_headers+0x4f7>
    iov[3].iov_base = zh_malloc(slen);
    4262:	49 89 44 24 30       	mov    %rax,0x30(%r12)
    iov[3].iov_len = slen;
    4267:	49 89 5c 24 38       	mov    %rbx,0x38(%r12)
    426c:	83 fb 08             	cmp    $0x8,%ebx
    426f:	0f 83 13 01 00 00    	jae    4388 <send_headers+0x3a8>
    4275:	f6 c3 04             	test   $0x4,%bl
    4278:	0f 85 1d 02 00 00    	jne    449b <send_headers+0x4bb>
    427e:	85 db                	test   %ebx,%ebx
    4280:	74 12                	je     4294 <send_headers+0x2b4>
    4282:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    4289:	88 10                	mov    %dl,(%rax)
    428b:	f6 c3 02             	test   $0x2,%bl
    428e:	0f 85 31 02 00 00    	jne    44c5 <send_headers+0x4e5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4294:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4299:	bf 02 00 00 00       	mov    $0x2,%edi
    429e:	c6 85 d2 fb ff ff 00 	movb   $0x0,-0x42e(%rbp)
    42a5:	66 89 85 d0 fb ff ff 	mov    %ax,-0x430(%rbp)
    42ac:	e8 8f e1 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    42b1:	48 85 c0             	test   %rax,%rax
    42b4:	0f 84 1d 02 00 00    	je     44d7 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    42ba:	0f b7 95 d0 fb ff ff 	movzwl -0x430(%rbp),%edx
    iov[4].iov_base = zh_malloc(slen);
    42c1:	49 89 44 24 40       	mov    %rax,0x40(%r12)
    iov[4].iov_len = slen;
    42c6:	49 c7 44 24 48 02 00 00 00 	movq   $0x2,0x48(%r12)
    42cf:	66 89 10             	mov    %dx,(%rax)
}
    42d2:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    42d6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    42df:	0f 85 19 02 00 00    	jne    44fe <send_headers+0x51e>
    42e5:	48 81 c4 10 08 00 00 	add    $0x810,%rsp
    42ec:	5b                   	pop    %rbx
    42ed:	41 5c                	pop    %r12
    42ef:	41 5d                	pop    %r13
    42f1:	41 5e                	pop    %r14
    42f3:	5d                   	pop    %rbp
    42f4:	c3                   	ret
    42f5:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
    42f8:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    42fc:	0f 85 a3 fe ff ff    	jne    41a5 <send_headers+0x1c5>
    4302:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4306:	0f 85 99 fe ff ff    	jne    41a5 <send_headers+0x1c5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    430c:	66 0f 6f 05 cc 36 00 00 	movdqa 0x36cc(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    4314:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    431e:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4325:	66 0f 6f 05 c3 36 00 00 	movdqa 0x36c3(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    432d:	0f 29 85 e0 fb ff ff 	movaps %xmm0,-0x420(%rbp)
    4334:	48 89 85 ef fb ff ff 	mov    %rax,-0x411(%rbp)
    433b:	e9 65 fe ff ff       	jmp    41a5 <send_headers+0x1c5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4340:	89 da                	mov    %ebx,%edx
    4342:	48 89 c7             	mov    %rax,%rdi
    4345:	4c 89 ee             	mov    %r13,%rsi
    4348:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    434d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4352:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4355:	c1 e9 03             	shr    $0x3,%ecx
    4358:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    435b:	e9 c8 fe ff ff       	jmp    4228 <send_headers+0x248>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4360:	66 0f 6f 05 18 36 00 00 	movdqa 0x3618(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4368:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    436f:	66 0f 6f 05 29 36 00 00 	movdqa 0x3629(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4377:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    437e:	e9 d4 fd ff ff       	jmp    4157 <send_headers+0x177>
    4383:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4388:	89 da                	mov    %ebx,%edx
    438a:	48 89 c7             	mov    %rax,%rdi
    438d:	4c 89 ee             	mov    %r13,%rsi
    4390:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    4395:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    439a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    439d:	c1 e9 03             	shr    $0x3,%ecx
    43a0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    43a3:	e9 ec fe ff ff       	jmp    4294 <send_headers+0x2b4>
    43a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    43b0:	48 8d 1d 18 2d 00 00 	lea    0x2d18(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    43b7:	e9 9b fd ff ff       	jmp    4157 <send_headers+0x177>
    43bc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    43c0:	66 0f 6f 05 f8 35 00 00 	movdqa 0x35f8(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    43c8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    43cf:	66 0f 6f 05 f9 35 00 00 	movdqa 0x35f9(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    43d7:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    43de:	e9 b9 fd ff ff       	jmp    419c <send_headers+0x1bc>
    43e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    43e8:	66 0f 6f 05 d0 35 00 00 	movdqa 0x35d0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    43f0:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    43f7:	66 0f 6f 05 d1 35 00 00 	movdqa 0x35d1(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    43ff:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    4406:	e9 7a fd ff ff       	jmp    4185 <send_headers+0x1a5>
    440b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4410:	66 0f 6f 05 68 35 00 00 	movdqa 0x3568(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4418:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    441f:	66 0f 6f 05 89 35 00 00 	movdqa 0x3589(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    4427:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    442e:	e9 3b fd ff ff       	jmp    416e <send_headers+0x18e>
    4433:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4438:	66 0f 6f 05 80 35 00 00 	movdqa 0x3580(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4440:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4447:	66 0f 6f 05 c1 35 00 00 	movdqa 0x35c1(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    444f:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    4456:	e9 78 fd ff ff       	jmp    41d3 <send_headers+0x1f3>
    445b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4460:	66 0f 6f 05 58 35 00 00 	movdqa 0x3558(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4468:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    446f:	66 0f 6f 05 89 35 00 00 	movdqa 0x3589(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4477:	0f 11 85 d9 fb ff ff 	movups %xmm0,-0x427(%rbp)
    447e:	e9 39 fd ff ff       	jmp    41bc <send_headers+0x1dc>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4483:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    4489:	89 db                	mov    %ebx,%ebx
    448b:	89 10                	mov    %edx,(%rax)
    448d:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    4492:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4496:	e9 8d fd ff ff       	jmp    4228 <send_headers+0x248>
    449b:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    44a1:	89 db                	mov    %ebx,%ebx
    44a3:	89 10                	mov    %edx,(%rax)
    44a5:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    44aa:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    44ae:	e9 e1 fd ff ff       	jmp    4294 <send_headers+0x2b4>
    44b3:	89 db                	mov    %ebx,%ebx
    44b5:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    44bb:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    44c0:	e9 63 fd ff ff       	jmp    4228 <send_headers+0x248>
    44c5:	89 db                	mov    %ebx,%ebx
    44c7:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    44cd:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    44d2:	e9 bd fd ff ff       	jmp    4294 <send_headers+0x2b4>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    44d7:	48 8b 0d 42 5b 00 00 	mov    0x5b42(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    44de:	ba 28 00 00 00       	mov    $0x28,%edx
    44e3:	be 01 00 00 00       	mov    $0x1,%esi
    44e8:	48 8d 3d 19 2f 00 00 	lea    0x2f19(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    44ef:	e8 0c e0 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    44f4:	bf 01 00 00 00       	mov    $0x1,%edi
    44f9:	e8 e2 df ff ff       	call   24e0 <exit@plt>
}
    44fe:	e8 4d de ff ff       	call   2350 <__stack_chk_fail@plt>
    4503:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    450e:	66 90                	xchg   %ax,%ax

0000000000004510 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4510:	f3 0f 1e fa          	endbr64
    4514:	55                   	push   %rbp
    4515:	48 89 e5             	mov    %rsp,%rbp
    4518:	41 56                	push   %r14
    451a:	41 55                	push   %r13
    451c:	41 54                	push   %r12
    451e:	53                   	push   %rbx
    451f:	ff 15 c3 5a 00 00    	call   *0x5ac3(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    4525:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    4528:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    452b:	48 89 f3             	mov    %rsi,%rbx
    452e:	49 89 d6             	mov    %rdx,%r14
    void *buf = malloc(size);
    4531:	e8 0a df ff ff       	call   2440 <malloc@plt>
    4536:	49 89 c4             	mov    %rax,%r12
    if (!buf) {
    4539:	48 85 c0             	test   %rax,%rax
    453c:	74 69                	je     45a7 <copy_file_contents+0x97>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    453e:	4c 89 ef             	mov    %r13,%rdi
    4541:	31 f6                	xor    %esi,%esi
    4543:	31 c0                	xor    %eax,%eax
    4545:	e8 66 df ff ff       	call   24b0 <open@plt>
    454a:	41 89 c5             	mov    %eax,%r13d
    if (fd < 0)
    454d:	85 c0                	test   %eax,%eax
    454f:	0f 88 48 e0 ff ff    	js     259d <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4555:	48 89 da             	mov    %rbx,%rdx
    4558:	4c 89 e6             	mov    %r12,%rsi
    455b:	89 c7                	mov    %eax,%edi
    455d:	e8 4e de ff ff       	call   23b0 <read@plt>
    if (ret < file_size) {
    4562:	48 98                	cltq
    4564:	48 39 d8             	cmp    %rbx,%rax
    4567:	7c 1f                	jl     4588 <copy_file_contents+0x78>
    close(fd);
    4569:	44 89 ef             	mov    %r13d,%edi
    456c:	e8 1f de ff ff       	call   2390 <close@plt>
    iov->iov_base = buf;
    4571:	4d 89 26             	mov    %r12,(%r14)
    iov->iov_len = file_size;
    4574:	49 89 5e 08          	mov    %rbx,0x8(%r14)
}
    4578:	5b                   	pop    %rbx
    4579:	41 5c                	pop    %r12
    457b:	41 5d                	pop    %r13
    457d:	41 5e                	pop    %r14
    457f:	5d                   	pop    %rbp
    4580:	c3                   	ret
    4581:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4588:	48 8b 0d 91 5a 00 00 	mov    0x5a91(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    458f:	ba 1a 00 00 00       	mov    $0x1a,%edx
    4594:	be 01 00 00 00       	mov    $0x1,%esi
    4599:	48 8d 3d 30 2b 00 00 	lea    0x2b30(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    45a0:	e8 5b df ff ff       	call   2500 <fwrite@plt>
    45a5:	eb c2                	jmp    4569 <copy_file_contents+0x59>
    45a7:	48 8b 0d 72 5a 00 00 	mov    0x5a72(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    45ae:	ba 28 00 00 00       	mov    $0x28,%edx
    45b3:	be 01 00 00 00       	mov    $0x1,%esi
    45b8:	48 8d 3d 49 2e 00 00 	lea    0x2e49(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    45bf:	e8 3c df ff ff       	call   2500 <fwrite@plt>
        exit(1);
    45c4:	bf 01 00 00 00       	mov    $0x1,%edi
    45c9:	e8 12 df ff ff       	call   24e0 <exit@plt>
    45ce:	66 90                	xchg   %ax,%ax

00000000000045d0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    45d0:	f3 0f 1e fa          	endbr64
    45d4:	55                   	push   %rbp
    45d5:	48 89 e5             	mov    %rsp,%rbp
    45d8:	ff 15 0a 5a 00 00    	call   *0x5a0a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    45de:	8b 46 44             	mov    0x44(%rsi),%eax
    45e1:	48 89 fa             	mov    %rdi,%rdx
    45e4:	48 89 f7             	mov    %rsi,%rdi
    45e7:	8d 70 01             	lea    0x1(%rax),%esi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    45ea:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    45f0:	48 8b 07             	mov    (%rdi),%rax
    45f3:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    45f6:	f6 c1 02             	test   $0x2,%cl
    45f9:	74 00                	je     45fb <add_write_request+0x2b>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    45fb:	89 f0                	mov    %esi,%eax
    45fd:	44 29 c0             	sub    %r8d,%eax
    4600:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4603:	0f 82 a0 df ff ff    	jb     25a9 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4609:	c1 e9 0a             	shr    $0xa,%ecx
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    460c:	8b 47 44             	mov    0x44(%rdi),%eax
    460f:	23 47 58             	and    0x58(%rdi),%eax
		sq->sqe_tail = next;
    4612:	89 77 44             	mov    %esi,0x44(%rdi)
	if (ring->flags & IORING_SETUP_SQE128)
    4615:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4618:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    461b:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    461f:	d3 e0                	shl    %cl,%eax
    4621:	8b 4a 04             	mov    0x4(%rdx),%ecx
    4624:	48 c1 e0 06          	shl    $0x6,%rax
    4628:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    462c:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    4632:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4635:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4639:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    463f:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4647:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    464b:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    464e:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4655:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    465d:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    4661:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    4665:	e8 f6 dc ff ff       	call   2360 <io_uring_submit@plt>
}
    466a:	31 c0                	xor    %eax,%eax
    466c:	5d                   	pop    %rbp
    466d:	c3                   	ret
    466e:	66 90                	xchg   %ax,%ax

0000000000004670 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4670:	f3 0f 1e fa          	endbr64
    4674:	55                   	push   %rbp
    4675:	48 89 e5             	mov    %rsp,%rbp
    4678:	41 56                	push   %r14
    467a:	41 55                	push   %r13
    467c:	41 54                	push   %r12
    467e:	53                   	push   %rbx
    467f:	ff 15 63 59 00 00    	call   *0x5963(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    4685:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4688:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    468e:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4691:	83 c0 01             	add    $0x1,%eax
    4694:	48 89 f3             	mov    %rsi,%rbx
    4697:	41 89 fe             	mov    %edi,%r14d
		head = IO_URING_READ_ONCE(*sq->khead);
    469a:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    469c:	f6 c1 02             	test   $0x2,%cl
    469f:	74 00                	je     46a1 <add_read_request+0x31>
	if (next - head <= sq->ring_entries) {
    46a1:	89 c2                	mov    %eax,%edx
    46a3:	29 f2                	sub    %esi,%edx
    46a5:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    46a8:	0f 82 0b df ff ff    	jb     25b9 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    46ae:	44 8b 63 44          	mov    0x44(%rbx),%r12d
	if (ring->flags & IORING_SETUP_SQE128)
    46b2:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    46b5:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    46b8:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    46bd:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    46c0:	44 23 63 58          	and    0x58(%rbx),%r12d
    46c4:	41 d3 e4             	shl    %cl,%r12d
    46c7:	49 c1 e4 06          	shl    $0x6,%r12
    46cb:	4c 03 63 38          	add    0x38(%rbx),%r12
    46cf:	e8 6c dd ff ff       	call   2440 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    46d4:	be 01 00 00 00       	mov    $0x1,%esi
    46d9:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    46de:	49 89 c5             	mov    %rax,%r13
    req->iov[0].iov_base = malloc(READ_SZ);
    46e1:	e8 da dc ff ff       	call   23c0 <calloc@plt>
    req->client_socket = client_socket;
    46e6:	45 89 75 08          	mov    %r14d,0x8(%r13)
	sqe->addr3 = 0;
    46ea:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    46ee:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    46f1:	49 89 45 10          	mov    %rax,0x10(%r13)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    46f5:	49 8d 45 10          	lea    0x10(%r13),%rax
    req->iov[0].iov_len = READ_SZ;
    46f9:	49 c7 45 18 00 20 00 00 	movq   $0x2000,0x18(%r13)
    req->event_type = EVENT_TYPE_READ;
    4701:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
	sqe->fd = fd;
    4709:	45 89 74 24 04       	mov    %r14d,0x4(%r12)
	sqe->user_data = (unsigned long) data;
    470e:	4d 89 6c 24 20       	mov    %r13,0x20(%r12)
	sqe->opcode = (__u8) op;
    4713:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->off = offset;
    471b:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4724:	49 89 44 24 10       	mov    %rax,0x10(%r12)
	sqe->len = len;
    4729:	49 c7 44 24 18 01 00 00 00 	movq   $0x1,0x18(%r12)
	sqe->buf_index = 0;
    4732:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->addr3 = 0;
    473b:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    io_uring_submit(ring);
    4741:	e8 1a dc ff ff       	call   2360 <io_uring_submit@plt>
}
    4746:	5b                   	pop    %rbx
    4747:	31 c0                	xor    %eax,%eax
    4749:	41 5c                	pop    %r12
    474b:	41 5d                	pop    %r13
    474d:	41 5e                	pop    %r14
    474f:	5d                   	pop    %rbp
    4750:	c3                   	ret
    4751:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    475c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004760 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4760:	f3 0f 1e fa          	endbr64
    4764:	55                   	push   %rbp
    4765:	48 89 e5             	mov    %rsp,%rbp
    4768:	41 57                	push   %r15
    476a:	41 56                	push   %r14
    476c:	41 55                	push   %r13
    476e:	41 54                	push   %r12
    4770:	53                   	push   %rbx
    4771:	48 83 ec 08          	sub    $0x8,%rsp
    4775:	ff 15 6d 58 00 00    	call   *0x586d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    477b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    477e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4783:	41 89 f7             	mov    %esi,%r15d
    4786:	49 89 d4             	mov    %rdx,%r12
    void *buf = malloc(size);
    4789:	e8 b2 dc ff ff       	call   2440 <malloc@plt>
    478e:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4791:	48 85 c0             	test   %rax,%rax
    4794:	0f 84 eb 00 00 00    	je     4885 <_send_static_string_content+0x125>
    unsigned long slen = strlen(str);
    479a:	4c 89 ef             	mov    %r13,%rdi
    479d:	e8 9e db ff ff       	call   2340 <strlen@plt>
    req->iovec_count = 1;
    47a2:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    47a9:	44 89 7b 08          	mov    %r15d,0x8(%rbx)
    void *buf = malloc(size);
    47ad:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    47b0:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    47b3:	e8 88 dc ff ff       	call   2440 <malloc@plt>
    47b8:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    47bb:	48 85 c0             	test   %rax,%rax
    47be:	0f 84 c1 00 00 00    	je     4885 <_send_static_string_content+0x125>
    req->iov[0].iov_base = zh_malloc(slen);
    47c4:	48 89 43 10          	mov    %rax,0x10(%rbx)
    47c8:	4c 89 f2             	mov    %r14,%rdx
    47cb:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    47ce:	4c 89 73 18          	mov    %r14,0x18(%rbx)
    47d2:	e8 39 dc ff ff       	call   2410 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    47d7:	41 8b 44 24 44       	mov    0x44(%r12),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    47dc:	41 8b 8c 24 c0 00 00 00 	mov    0xc0(%r12),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    47e4:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    47e7:	49 8b 04 24          	mov    (%r12),%rax
    47eb:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    47ed:	f6 c1 02             	test   $0x2,%cl
    47f0:	0f 85 8a 00 00 00    	jne    4880 <_send_static_string_content+0x120>
	if (next - head <= sq->ring_entries) {
    47f6:	89 d0                	mov    %edx,%eax
    47f8:	29 f0                	sub    %esi,%eax
    47fa:	41 39 44 24 5c       	cmp    %eax,0x5c(%r12)
    47ff:	0f 82 be dd ff ff    	jb     25c3 <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4805:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4808:	41 8b 44 24 44       	mov    0x44(%r12),%eax
    480d:	41 23 44 24 58       	and    0x58(%r12),%eax
    io_uring_submit(ring);
    4812:	4c 89 e7             	mov    %r12,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    4815:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4818:	41 89 54 24 44       	mov    %edx,0x44(%r12)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    481d:	8b 53 04             	mov    0x4(%rbx),%edx
	sqe->addr3 = 0;
    4820:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4824:	d3 e0                	shl    %cl,%eax
    4826:	8b 4b 08             	mov    0x8(%rbx),%ecx
    req->event_type = EVENT_TYPE_WRITE;
    4829:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    482f:	48 c1 e0 06          	shl    $0x6,%rax
    4833:	49 03 44 24 38       	add    0x38(%r12),%rax
	sqe->fd = fd;
    4838:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    483b:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    483f:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4845:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    484d:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4851:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4854:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    485b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4863:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    4867:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    486b:	48 83 c4 08          	add    $0x8,%rsp
    486f:	5b                   	pop    %rbx
    4870:	41 5c                	pop    %r12
    4872:	41 5d                	pop    %r13
    4874:	41 5e                	pop    %r14
    4876:	41 5f                	pop    %r15
    4878:	5d                   	pop    %rbp
    io_uring_submit(ring);
    4879:	e9 e2 da ff ff       	jmp    2360 <io_uring_submit@plt>
    487e:	66 90                	xchg   %ax,%ax
		head = io_uring_smp_load_acquire(sq->khead);
    4880:	e9 71 ff ff ff       	jmp    47f6 <_send_static_string_content+0x96>
    4885:	48 8b 0d 94 57 00 00 	mov    0x5794(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    488c:	ba 28 00 00 00       	mov    $0x28,%edx
    4891:	be 01 00 00 00       	mov    $0x1,%esi
    4896:	48 8d 3d 6b 2b 00 00 	lea    0x2b6b(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    489d:	e8 5e dc ff ff       	call   2500 <fwrite@plt>
        exit(1);
    48a2:	bf 01 00 00 00       	mov    $0x1,%edi
    48a7:	e8 34 dc ff ff       	call   24e0 <exit@plt>
    48ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000048b0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    48b0:	f3 0f 1e fa          	endbr64
    48b4:	55                   	push   %rbp
    48b5:	48 89 e5             	mov    %rsp,%rbp
    48b8:	ff 15 2a 57 00 00    	call   *0x572a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
}
    48be:	5d                   	pop    %rbp
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    48bf:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    48c2:	89 fe                	mov    %edi,%esi
    48c4:	48 8b 3d 4d 57 00 00 	mov    0x574d(%rip),%rdi        # a018 <unimplemented_content>
    48cb:	e9 90 fe ff ff       	jmp    4760 <_send_static_string_content>

00000000000048d0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    48d0:	f3 0f 1e fa          	endbr64
    48d4:	55                   	push   %rbp
    48d5:	48 89 e5             	mov    %rsp,%rbp
    48d8:	ff 15 0a 57 00 00    	call   *0x570a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
}
    48de:	5d                   	pop    %rbp
void handle_http_404(int client_socket, struct io_uring *ring) {
    48df:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    48e2:	89 fe                	mov    %edi,%esi
    48e4:	48 8b 3d 25 57 00 00 	mov    0x5725(%rip),%rdi        # a010 <http_404_content>
    48eb:	e9 70 fe ff ff       	jmp    4760 <_send_static_string_content>

00000000000048f0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    48f0:	f3 0f 1e fa          	endbr64
    48f4:	55                   	push   %rbp
    48f5:	48 89 e5             	mov    %rsp,%rbp
    48f8:	41 57                	push   %r15
    48fa:	41 56                	push   %r14
    48fc:	41 55                	push   %r13
    48fe:	41 54                	push   %r12
    4900:	53                   	push   %rbx
    4901:	48 81 ec a8 04 00 00 	sub    $0x4a8,%rsp
    4908:	ff 15 da 56 00 00    	call   *0x56da(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    490e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4917:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    491b:	31 c0                	xor    %eax,%eax
    491d:	49 89 fc             	mov    %rdi,%r12
    4920:	41 89 f5             	mov    %esi,%r13d
    4923:	49 89 d6             	mov    %rdx,%r14
    if (path[strlen(path) - 1] == '/') {
    4926:	e8 15 da ff ff       	call   2340 <strlen@plt>
    492b:	41 80 7c 04 ff 2f    	cmpb   $0x2f,-0x1(%r12,%rax,1)
    4931:	48 89 c3             	mov    %rax,%rbx
    4934:	0f 84 b6 00 00 00    	je     49f0 <handle_get_method+0x100>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    493a:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    493f:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4943:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4948:	4c 89 e6             	mov    %r12,%rsi
    494b:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4952:	66 89 85 c4 fb ff ff 	mov    %ax,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4959:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4960:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    496a:	e8 81 da ff ff       	call   23f0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    496f:	48 8d b5 30 fb ff ff 	lea    -0x4d0(%rbp),%rsi
    4976:	4c 89 ff             	mov    %r15,%rdi
    4979:	e8 82 da ff ff       	call   2400 <stat@plt>
    497e:	83 f8 ff             	cmp    $0xffffffff,%eax
    4981:	0f 84 41 01 00 00    	je     4ac8 <handle_get_method+0x1d8>
        if (S_ISREG(path_stat.st_mode)) {
    4987:	8b 85 48 fb ff ff    	mov    -0x4b8(%rbp),%eax
    498d:	25 00 f0 00 00       	and    $0xf000,%eax
    4992:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4997:	0f 84 b3 00 00 00    	je     4a50 <handle_get_method+0x160>
    _send_static_string_content(http_404_content, client_socket, ring);
    499d:	48 8b 3d 6c 56 00 00 	mov    0x566c(%rip),%rdi        # a010 <http_404_content>
    49a4:	4c 89 f2             	mov    %r14,%rdx
    49a7:	44 89 ee             	mov    %r13d,%esi
    49aa:	e8 b1 fd ff ff       	call   4760 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    49af:	4c 89 fa             	mov    %r15,%rdx
    49b2:	bf 01 00 00 00       	mov    $0x1,%edi
    49b7:	31 c0                	xor    %eax,%eax
    49b9:	48 8d 35 60 27 00 00 	lea    0x2760(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    49c0:	e8 bb da ff ff       	call   2480 <__printf_chk@plt>
}
    49c5:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    49c9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    49d2:	0f 85 20 01 00 00    	jne    4af8 <handle_get_method+0x208>
    49d8:	48 81 c4 a8 04 00 00 	add    $0x4a8,%rsp
    49df:	5b                   	pop    %rbx
    49e0:	41 5c                	pop    %r12
    49e2:	41 5d                	pop    %r13
    49e4:	41 5e                	pop    %r14
    49e6:	41 5f                	pop    %r15
    49e8:	5d                   	pop    %rbp
    49e9:	c3                   	ret
    49ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    49f0:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    49f5:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
    49fc:	4c 89 e6             	mov    %r12,%rsi
    49ff:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a04:	66 89 95 c4 fb ff ff 	mov    %dx,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a0b:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a0e:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
    4a15:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a1f:	e8 cc d9 ff ff       	call   23f0 <__memcpy_chk@plt>
    4a24:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4a29:	49 8d 7c 1f 06       	lea    0x6(%r15,%rbx,1),%rdi
    4a2e:	ba 0b 00 00 00       	mov    $0xb,%edx
    4a33:	48 29 d9             	sub    %rbx,%rcx
    4a36:	48 8d 35 ae 26 00 00 	lea    0x26ae(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4a3d:	e8 ae d9 ff ff       	call   23f0 <__memcpy_chk@plt>
    4a42:	e9 28 ff ff ff       	jmp    496f <handle_get_method+0x7f>
    4a47:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4a50:	bf 70 00 00 00       	mov    $0x70,%edi
    4a55:	e8 e6 d9 ff ff       	call   2440 <malloc@plt>
    4a5a:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4a5d:	48 85 c0             	test   %rax,%rax
    4a60:	0f 84 97 00 00 00    	je     4afd <handle_get_method+0x20d>
            req->client_socket = client_socket;
    4a66:	44 89 68 08          	mov    %r13d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4a6a:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    4a71:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4a75:	4c 89 ff             	mov    %r15,%rdi
            req->iovec_count = 6;
    4a78:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4a7f:	e8 5c f5 ff ff       	call   3fe0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4a84:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    4a8b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4a8f:	4c 89 ff             	mov    %r15,%rdi
    4a92:	e8 79 fa ff ff       	call   4510 <copy_file_contents>
    4a97:	4c 89 fa             	mov    %r15,%rdx
    4a9a:	bf 01 00 00 00       	mov    $0x1,%edi
    4a9f:	31 c0                	xor    %eax,%eax
    4aa1:	48 8b 8d 60 fb ff ff 	mov    -0x4a0(%rbp),%rcx
    4aa8:	48 8d 35 5f 26 00 00 	lea    0x265f(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4aaf:	e8 cc d9 ff ff       	call   2480 <__printf_chk@plt>
            add_write_request(req, ring);
    4ab4:	4c 89 f6             	mov    %r14,%rsi
    4ab7:	48 89 df             	mov    %rbx,%rdi
    4aba:	e8 11 fb ff ff       	call   45d0 <add_write_request>
    4abf:	e9 01 ff ff ff       	jmp    49c5 <handle_get_method+0xd5>
    4ac4:	0f 1f 40 00          	nopl   0x0(%rax)
    4ac8:	4c 89 fa             	mov    %r15,%rdx
    4acb:	4c 89 e1             	mov    %r12,%rcx
    4ace:	48 8d 35 21 26 00 00 	lea    0x2621(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    4ad5:	31 c0                	xor    %eax,%eax
    4ad7:	bf 01 00 00 00       	mov    $0x1,%edi
    4adc:	e8 9f d9 ff ff       	call   2480 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    4ae1:	48 8b 3d 28 55 00 00 	mov    0x5528(%rip),%rdi        # a010 <http_404_content>
    4ae8:	4c 89 f2             	mov    %r14,%rdx
    4aeb:	44 89 ee             	mov    %r13d,%esi
    4aee:	e8 6d fc ff ff       	call   4760 <_send_static_string_content>
}
    4af3:	e9 cd fe ff ff       	jmp    49c5 <handle_get_method+0xd5>
}
    4af8:	e8 53 d8 ff ff       	call   2350 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4afd:	48 8b 0d 1c 55 00 00 	mov    0x551c(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4b04:	ba 28 00 00 00       	mov    $0x28,%edx
    4b09:	be 01 00 00 00       	mov    $0x1,%esi
    4b0e:	48 8d 3d f3 28 00 00 	lea    0x28f3(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4b15:	e8 e6 d9 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    4b1a:	bf 01 00 00 00       	mov    $0x1,%edi
    4b1f:	e8 bc d9 ff ff       	call   24e0 <exit@plt>
    4b24:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4b2f:	90                   	nop

0000000000004b30 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4b30:	f3 0f 1e fa          	endbr64
    4b34:	55                   	push   %rbp
    4b35:	48 89 e5             	mov    %rsp,%rbp
    4b38:	41 57                	push   %r15
    4b3a:	41 56                	push   %r14
    4b3c:	41 55                	push   %r13
    4b3e:	41 54                	push   %r12
    4b40:	53                   	push   %rbx
    4b41:	48 83 ec 28          	sub    $0x28,%rsp
    4b45:	ff 15 9d 54 00 00    	call   *0x549d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    method = strtok_r(method_buffer, " ", &saveptr);
    4b4b:	4c 8d 35 33 25 00 00 	lea    0x2533(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4b52:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b5b:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    4b5f:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4b61:	4c 8d 7d c0          	lea    -0x40(%rbp),%r15
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4b65:	41 89 f4             	mov    %esi,%r12d
    4b68:	49 89 d5             	mov    %rdx,%r13
    method = strtok_r(method_buffer, " ", &saveptr);
    4b6b:	4c 89 f6             	mov    %r14,%rsi
    4b6e:	4c 89 fa             	mov    %r15,%rdx
    4b71:	e8 2a d8 ff ff       	call   23a0 <strtok_r@plt>
    for (; *str; ++str)
    4b76:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    4b79:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    4b7c:	84 d2                	test   %dl,%dl
    4b7e:	88 55 bf             	mov    %dl,-0x41(%rbp)
    4b81:	74 22                	je     4ba5 <handle_http_method+0x75>
        *str = (char)tolower(*str);
    4b83:	e8 c8 d9 ff ff       	call   2550 <__ctype_tolower_loc@plt>
    4b88:	48 0f be 55 bf       	movsbq -0x41(%rbp),%rdx
    4b8d:	48 89 d9             	mov    %rbx,%rcx
    4b90:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    4b93:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    4b97:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    4b9a:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    4b9d:	48 0f be 11          	movsbq (%rcx),%rdx
    4ba1:	84 d2                	test   %dl,%dl
    4ba3:	75 eb                	jne    4b90 <handle_http_method+0x60>
    path = strtok_r(NULL, " ", &saveptr);
    4ba5:	4c 89 fa             	mov    %r15,%rdx
    4ba8:	4c 89 f6             	mov    %r14,%rsi
    4bab:	31 ff                	xor    %edi,%edi
    4bad:	e8 ee d7 ff ff       	call   23a0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4bb2:	48 8d 35 7a 25 00 00 	lea    0x257a(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4bb9:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4bbc:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    4bbf:	e8 0c d8 ff ff       	call   23d0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4bc4:	4c 89 ea             	mov    %r13,%rdx
    4bc7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4bca:	85 c0                	test   %eax,%eax
    4bcc:	75 2a                	jne    4bf8 <handle_http_method+0xc8>
        handle_get_method(path, client_socket, ring);
    4bce:	4c 89 f7             	mov    %r14,%rdi
    4bd1:	e8 1a fd ff ff       	call   48f0 <handle_get_method>
}
    4bd6:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    4bda:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4be3:	75 21                	jne    4c06 <handle_http_method+0xd6>
    4be5:	48 83 c4 28          	add    $0x28,%rsp
    4be9:	5b                   	pop    %rbx
    4bea:	41 5c                	pop    %r12
    4bec:	41 5d                	pop    %r13
    4bee:	41 5e                	pop    %r14
    4bf0:	41 5f                	pop    %r15
    4bf2:	5d                   	pop    %rbp
    4bf3:	c3                   	ret
    4bf4:	0f 1f 40 00          	nopl   0x0(%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4bf8:	48 8b 3d 19 54 00 00 	mov    0x5419(%rip),%rdi        # a018 <unimplemented_content>
    4bff:	e8 5c fb ff ff       	call   4760 <_send_static_string_content>
}
    4c04:	eb d0                	jmp    4bd6 <handle_http_method+0xa6>
    4c06:	e8 45 d7 ff ff       	call   2350 <__stack_chk_fail@plt>
    4c0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004c10 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4c10:	f3 0f 1e fa          	endbr64
    4c14:	55                   	push   %rbp
    4c15:	48 89 e5             	mov    %rsp,%rbp
    4c18:	ff 15 ca 53 00 00    	call   *0x53ca(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    for (int i = 0; i < dest_sz; i++) {
    4c1e:	85 d2                	test   %edx,%edx
    4c20:	7e 36                	jle    4c58 <get_line+0x48>
    4c22:	48 63 d2             	movslq %edx,%rdx
    4c25:	48 83 c7 01          	add    $0x1,%rdi
    4c29:	48 01 f2             	add    %rsi,%rdx
    4c2c:	eb 0f                	jmp    4c3d <get_line+0x2d>
    4c2e:	66 90                	xchg   %ax,%ax
    4c30:	48 83 c6 01          	add    $0x1,%rsi
    4c34:	48 83 c7 01          	add    $0x1,%rdi
    4c38:	48 39 d6             	cmp    %rdx,%rsi
    4c3b:	74 1b                	je     4c58 <get_line+0x48>
        dest[i] = src[i];
    4c3d:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4c41:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4c43:	3c 0d                	cmp    $0xd,%al
    4c45:	75 e9                	jne    4c30 <get_line+0x20>
    4c47:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4c4a:	75 e4                	jne    4c30 <get_line+0x20>
            return 0;
    4c4c:	31 c0                	xor    %eax,%eax
            dest[i] = '\0';
    4c4e:	c6 06 00             	movb   $0x0,(%rsi)
}
    4c51:	5d                   	pop    %rbp
    4c52:	c3                   	ret
    4c53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    return 1;
    4c58:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4c5d:	5d                   	pop    %rbp
    4c5e:	c3                   	ret
    4c5f:	90                   	nop

0000000000004c60 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4c60:	f3 0f 1e fa          	endbr64
    4c64:	55                   	push   %rbp
    4c65:	48 89 e5             	mov    %rsp,%rbp
    4c68:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    4c6f:	ff 15 73 53 00 00    	call   *0x5373(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    4c75:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4c79:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4c82:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
    4c86:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4c88:	4c 8d 95 f0 fb ff ff 	lea    -0x410(%rbp),%r10
    4c8f:	4c 8d 4d f0          	lea    -0x10(%rbp),%r9
    4c93:	4c 89 d0             	mov    %r10,%rax
    4c96:	eb 15                	jmp    4cad <handle_client_request+0x4d>
    4c98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4ca0:	48 83 c0 01          	add    $0x1,%rax
    4ca4:	48 83 c1 01          	add    $0x1,%rcx
    4ca8:	4c 39 c8             	cmp    %r9,%rax
    4cab:	74 43                	je     4cf0 <handle_client_request+0x90>
        dest[i] = src[i];
    4cad:	44 0f b6 01          	movzbl (%rcx),%r8d
    4cb1:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4cb4:	41 80 f8 0d          	cmp    $0xd,%r8b
    4cb8:	75 e6                	jne    4ca0 <handle_client_request+0x40>
    4cba:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4cbe:	75 e0                	jne    4ca0 <handle_client_request+0x40>
            dest[i] = '\0';
    4cc0:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4cc3:	8b 47 08             	mov    0x8(%rdi),%eax
    4cc6:	48 89 f2             	mov    %rsi,%rdx
    4cc9:	4c 89 d7             	mov    %r10,%rdi
    4ccc:	89 c6                	mov    %eax,%esi
    4cce:	e8 5d fe ff ff       	call   4b30 <handle_http_method>
}
    4cd3:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    4cd7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4ce0:	75 35                	jne    4d17 <handle_client_request+0xb7>
    4ce2:	c9                   	leave
    4ce3:	31 c0                	xor    %eax,%eax
    4ce5:	c3                   	ret
    4ce6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4cf0:	48 8b 0d 29 53 00 00 	mov    0x5329(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4cf7:	ba 12 00 00 00       	mov    $0x12,%edx
    4cfc:	be 01 00 00 00       	mov    $0x1,%esi
    4d01:	48 8d 3d 2f 24 00 00 	lea    0x242f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4d08:	e8 f3 d7 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    4d0d:	bf 01 00 00 00       	mov    $0x1,%edi
    4d12:	e8 c9 d7 ff ff       	call   24e0 <exit@plt>
}
    4d17:	e8 34 d6 ff ff       	call   2350 <__stack_chk_fail@plt>
    4d1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004d20 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4d20:	f3 0f 1e fa          	endbr64
    4d24:	55                   	push   %rbp
    4d25:	48 89 e5             	mov    %rsp,%rbp
    4d28:	41 54                	push   %r12
    4d2a:	53                   	push   %rbx
    4d2b:	ff 15 b7 52 00 00    	call   *0x52b7(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    4d31:	8b 41 44             	mov    0x44(%rcx),%eax
    4d34:	83 c0 01             	add    $0x1,%eax
    4d37:	48 89 cb             	mov    %rcx,%rbx
	if (ring->flags & IORING_SETUP_SQE128)
    4d3a:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    4d40:	4c 8b 03             	mov    (%rbx),%r8
    4d43:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4d46:	f6 c1 02             	test   $0x2,%cl
    4d49:	74 00                	je     4d4b <add_accept_request+0x2b>
	if (next - head <= sq->ring_entries) {
    4d4b:	41 89 c0             	mov    %eax,%r8d
    4d4e:	45 29 c8             	sub    %r9d,%r8d
    4d51:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4d55:	0f 82 78 d8 ff ff    	jb     25d3 <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4d5b:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d5e:	44 8b 63 44          	mov    0x44(%rbx),%r12d
    4d62:	44 23 63 58          	and    0x58(%rbx),%r12d
		sq->sqe_tail = next;
    4d66:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4d69:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4d6c:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d70:	41 d3 e4             	shl    %cl,%r12d
    4d73:	49 c1 e4 06          	shl    $0x6,%r12
    4d77:	4c 03 63 38          	add    0x38(%rbx),%r12
	sqe->fd = fd;
    4d7b:	41 89 7c 24 04       	mov    %edi,0x4(%r12)
  struct Request *req = malloc(sizeof(*req));
    4d80:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4d85:	41 c7 04 24 0d 00 00 00 	movl   $0xd,(%r12)
	sqe->off = offset;
    4d8d:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
	sqe->addr = (unsigned long) addr;
    4d92:	49 89 74 24 10       	mov    %rsi,0x10(%r12)
	sqe->buf_index = 0;
    4d97:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->len = len;
    4da0:	49 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%r12)
	sqe->addr3 = 0;
    4da9:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    4daf:	e8 8c d6 ff ff       	call   2440 <malloc@plt>
  io_uring_submit(ring);
    4db4:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4db7:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4dbd:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
    4dc2:	5b                   	pop    %rbx
    4dc3:	41 5c                	pop    %r12
    4dc5:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4dc6:	e9 95 d5 ff ff       	jmp    2360 <io_uring_submit@plt>
    4dcb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004dd0 <io_thread>:
void* io_thread(void *arg) {
    4dd0:	f3 0f 1e fa          	endbr64
    4dd4:	55                   	push   %rbp
    4dd5:	48 89 e5             	mov    %rsp,%rbp
    4dd8:	41 57                	push   %r15
    4dda:	41 56                	push   %r14
    4ddc:	41 55                	push   %r13
    4dde:	41 54                	push   %r12
    4de0:	53                   	push   %rbx
    4de1:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4de8:	ff 15 fa 51 00 00    	call   *0x51fa(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4dee:	31 d2                	xor    %edx,%edx
  struct io_uring ring = *data->ring;
    4df0:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4df9:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    4dfd:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e01:	48 8d 9d e0 fa ff ff 	lea    -0x520(%rbp),%rbx
void* io_thread(void *arg) {
    4e08:	49 89 fc             	mov    %rdi,%r12
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e0b:	bf 00 01 00 00       	mov    $0x100,%edi
    4e10:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4e13:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4e17:	0f 29 8d e0 fa ff ff 	movaps %xmm1,-0x520(%rbp)
    4e1e:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4e23:	0f 29 95 f0 fa ff ff 	movaps %xmm2,-0x510(%rbp)
    4e2a:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4e2f:	0f 29 9d 00 fb ff ff 	movaps %xmm3,-0x500(%rbp)
    4e36:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4e3b:	0f 29 a5 10 fb ff ff 	movaps %xmm4,-0x4f0(%rbp)
    4e42:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4e47:	0f 29 ad 20 fb ff ff 	movaps %xmm5,-0x4e0(%rbp)
    4e4e:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4e53:	0f 29 b5 30 fb ff ff 	movaps %xmm6,-0x4d0(%rbp)
    4e5a:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4e5f:	0f 29 bd 40 fb ff ff 	movaps %xmm7,-0x4c0(%rbp)
    4e66:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4e6b:	0f 29 8d 50 fb ff ff 	movaps %xmm1,-0x4b0(%rbp)
    4e72:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4e7a:	0f 29 95 60 fb ff ff 	movaps %xmm2,-0x4a0(%rbp)
    4e81:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4e89:	0f 29 9d 70 fb ff ff 	movaps %xmm3,-0x490(%rbp)
    4e90:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4e98:	0f 29 a5 80 fb ff ff 	movaps %xmm4,-0x480(%rbp)
    4e9f:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4ea7:	0f 29 ad 90 fb ff ff 	movaps %xmm5,-0x470(%rbp)
    4eae:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4eb6:	0f 29 b5 a0 fb ff ff 	movaps %xmm6,-0x460(%rbp)
    4ebd:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4ec4:	48 89 85 b0 fb ff ff 	mov    %rax,-0x450(%rbp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4ecb:	e8 50 d5 ff ff       	call   2420 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4ed0:	49 8b 7c 24 48       	mov    0x48(%r12),%rdi
    4ed5:	31 f6                	xor    %esi,%esi
    4ed7:	e8 44 d6 ff ff       	call   2520 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4edc:	31 d2                	xor    %edx,%edx
    4ede:	be 01 00 00 00       	mov    $0x1,%esi
    4ee3:	bf 02 00 00 00       	mov    $0x2,%edi
    4ee8:	e8 83 d6 ff ff       	call   2570 <socket@plt>
    4eed:	89 85 ac fa ff ff    	mov    %eax,-0x554(%rbp)
  if (sock == -1)
    4ef3:	83 f8 ff             	cmp    $0xffffffff,%eax
    4ef6:	0f 84 19 d7 ff ff    	je     2615 <io_thread.cold+0x38>
    4efc:	89 c7                	mov    %eax,%edi
  if (setsockopt(sock,
    4efe:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4f04:	ba 02 00 00 00       	mov    $0x2,%edx
    4f09:	be 01 00 00 00       	mov    $0x1,%esi
    4f0e:	48 8d 8d b0 fa ff ff 	lea    -0x550(%rbp),%rcx
  int enable = 1;
    4f15:	c7 85 b0 fa ff ff 01 00 00 00 	movl   $0x1,-0x550(%rbp)
  if (setsockopt(sock,
    4f1f:	e8 fc d3 ff ff       	call   2320 <setsockopt@plt>
    4f24:	85 c0                	test   %eax,%eax
    4f26:	0f 88 bd d6 ff ff    	js     25e9 <io_thread.cold+0xc>
  if (bind(sock,
    4f2c:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4f32:	ba 10 00 00 00       	mov    $0x10,%edx
  return __builtin___memset_chk (__dest, __ch, __len,
    4f37:	48 8d b5 c0 fa ff ff 	lea    -0x540(%rbp),%rsi
    4f3e:	48 c7 85 c4 fa ff ff 00 00 00 00 	movq   $0x0,-0x53c(%rbp)
    4f49:	c7 85 cc fa ff ff 00 00 00 00 	movl   $0x0,-0x534(%rbp)
  srv_addr.sin_family = AF_INET;
    4f53:	c7 85 c0 fa ff ff 02 00 18 db 	movl   $0xdb180002,-0x540(%rbp)
  if (bind(sock,
    4f5d:	e8 2e d5 ff ff       	call   2490 <bind@plt>
    4f62:	85 c0                	test   %eax,%eax
    4f64:	0f 88 b7 d6 ff ff    	js     2621 <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4f6a:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4f70:	be 0a 00 00 00       	mov    $0xa,%esi
    4f75:	e8 d6 d4 ff ff       	call   2450 <listen@plt>
    4f7a:	85 c0                	test   %eax,%eax
    4f7c:	0f 88 73 d6 ff ff    	js     25f5 <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4f82:	ba db 18 00 00       	mov    $0x18db,%edx
    4f87:	48 8d 35 ee 21 00 00 	lea    0x21ee(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4f8e:	bf 01 00 00 00       	mov    $0x1,%edi
    4f93:	31 c0                	xor    %eax,%eax
    4f95:	e8 e6 d4 ff ff       	call   2480 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4f9a:	48 8d 85 d0 fa ff ff 	lea    -0x530(%rbp),%rax
    4fa1:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4fa7:	48 89 d9             	mov    %rbx,%rcx
    4faa:	48 8d 95 b4 fa ff ff 	lea    -0x54c(%rbp),%rdx
    4fb1:	48 89 c6             	mov    %rax,%rsi
  socklen_t client_addr_len = sizeof(client_addr);
    4fb4:	c7 85 b4 fa ff ff 10 00 00 00 	movl   $0x10,-0x54c(%rbp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4fbe:	48 89 95 88 fa ff ff 	mov    %rdx,-0x578(%rbp)
    4fc5:	48 89 85 90 fa ff ff 	mov    %rax,-0x570(%rbp)
    4fcc:	e8 4f fd ff ff       	call   4d20 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4fd1:	bf 01 00 00 00       	mov    $0x1,%edi
    4fd6:	be 10 00 00 00       	mov    $0x10,%esi
    4fdb:	e8 e0 d3 ff ff       	call   23c0 <calloc@plt>
    void *buf = malloc(size);
    4fe0:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4fe5:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    4fe8:	e8 53 d4 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    4fed:	48 85 c0             	test   %rax,%rax
    4ff0:	0f 84 cf 04 00 00    	je     54c5 <io_thread+0x6f5>
  iov->iov_base = zh_malloc(10);
    4ff6:	49 89 06             	mov    %rax,(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    4ff9:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4fff:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
  iov->iov_len = 10;
    5005:	49 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    500d:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5010:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    5017:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5019:	f6 c1 02             	test   $0x2,%cl
    501c:	0f 85 2e 04 00 00    	jne    5450 <io_thread+0x680>
	if (next - head <= sq->ring_entries) {
    5022:	89 d0                	mov    %edx,%eax
    5024:	29 f0                	sub    %esi,%eax
    5026:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    502c:	0f 82 d9 d5 ff ff    	jb     260b <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5032:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5035:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    503b:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    503f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5042:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5048:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    504b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5051:	49 8d 74 24 50       	lea    0x50(%r12),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5056:	41 8b 54 24 50       	mov    0x50(%r12),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    505b:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    505d:	48 89 b5 98 fa ff ff 	mov    %rsi,-0x568(%rbp)
    5064:	48 c1 e0 06          	shl    $0x6,%rax
    5068:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    506f:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5075:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5078:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5080:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    5084:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    508c:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5094:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5098:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    509c:	e8 bf d2 ff ff       	call   2360 <io_uring_submit@plt>
  while (data->running == 1) {
    50a1:	41 83 7c 24 34 01    	cmpl   $0x1,0x34(%r12)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    50a7:	4c 8d 8d b8 fa ff ff 	lea    -0x548(%rbp),%r9
    50ae:	4c 8d 95 c0 fb ff ff 	lea    -0x440(%rbp),%r10
    50b5:	0f 85 ed 01 00 00    	jne    52a8 <io_thread+0x4d8>
    50bb:	4c 89 8d a0 fa ff ff 	mov    %r9,-0x560(%rbp)
    50c2:	4c 89 95 80 fa ff ff 	mov    %r10,-0x580(%rbp)
    50c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    50d0:	48 8d 3d bb 20 00 00 	lea    0x20bb(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    50d7:	e8 34 d2 ff ff       	call   2310 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    50dc:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned mask = ring->cq.ring_mask;
    50e2:	8b bd 90 fb ff ff    	mov    -0x470(%rbp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    50e8:	c1 e9 0b             	shr    $0xb,%ecx
    50eb:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    50ee:	48 8b 85 50 fb ff ff 	mov    -0x4b0(%rbp),%rax
    50f5:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    50f7:	48 8b b5 48 fb ff ff 	mov    -0x4b8(%rbp),%rsi
    50fe:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5100:	39 d0                	cmp    %edx,%eax
    5102:	74 34                	je     5138 <io_thread+0x368>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5104:	89 f8                	mov    %edi,%eax
    5106:	21 d0                	and    %edx,%eax
    5108:	d3 e0                	shl    %cl,%eax
    510a:	48 c1 e0 04          	shl    $0x4,%rax
    510e:	48 03 85 78 fb ff ff 	add    -0x488(%rbp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5115:	f6 85 a9 fb ff ff 01 	testb  $0x1,-0x457(%rbp)
    511c:	0f 85 be 01 00 00    	jne    52e0 <io_thread+0x510>
    5122:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5126:	0f 85 2c 03 00 00    	jne    5458 <io_thread+0x688>
			if (cqe->res < 0)
    512c:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    512f:	83 c2 01             	add    $0x1,%edx
    5132:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5134:	85 c0                	test   %eax,%eax
    5136:	79 b6                	jns    50ee <io_thread+0x31e>
	*cqe_ptr = cqe;
    5138:	48 c7 85 b8 fa ff ff 00 00 00 00 	movq   $0x0,-0x548(%rbp)
	return err;
    5143:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5148:	48 8b b5 a0 fa ff ff 	mov    -0x560(%rbp),%rsi
    514f:	45 31 c0             	xor    %r8d,%r8d
    5152:	31 d2                	xor    %edx,%edx
    5154:	48 89 df             	mov    %rbx,%rdi
    5157:	b9 01 00 00 00       	mov    $0x1,%ecx
    515c:	e8 0f d3 ff ff       	call   2470 <__io_uring_get_cqe@plt>
    5161:	41 89 c5             	mov    %eax,%r13d
      if (cqe->user_data == 1) {
    5164:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    516b:	48 83 38 01          	cmpq   $0x1,(%rax)
    516f:	0f 84 f3 02 00 00    	je     5468 <io_thread+0x698>
    5175:	48 8d 3d 3c 20 00 00 	lea    0x203c(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    517c:	e8 8f d1 ff ff       	call   2310 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5181:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    5188:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    518b:	45 85 ed             	test   %r13d,%r13d
    518e:	0f 88 49 d4 ff ff    	js     25dd <io_thread.cold>
      if (cqe->res < 0) {
    5194:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5197:	45 8b 07             	mov    (%r15),%r8d
      if (cqe->res < 0) {
    519a:	85 c0                	test   %eax,%eax
    519c:	0f 88 e5 02 00 00    	js     5487 <io_thread+0x6b7>
      switch (req->event_type) {
    51a2:	41 83 f8 01          	cmp    $0x1,%r8d
    51a6:	0f 84 84 01 00 00    	je     5330 <io_thread+0x560>
    51ac:	41 83 f8 02          	cmp    $0x2,%r8d
    51b0:	0f 84 aa 01 00 00    	je     5360 <io_thread+0x590>
    51b6:	45 85 c0             	test   %r8d,%r8d
    51b9:	0f 85 59 01 00 00    	jne    5318 <io_thread+0x548>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    51bf:	48 8b 95 88 fa ff ff 	mov    -0x578(%rbp),%rdx
    51c6:	48 8b b5 90 fa ff ff 	mov    -0x570(%rbp),%rsi
    51cd:	48 89 d9             	mov    %rbx,%rcx
    51d0:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    51d6:	e8 45 fb ff ff       	call   4d20 <add_accept_request>
              add_read_request(cqe->res, &ring);
    51db:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    51e2:	48 89 de             	mov    %rbx,%rsi
    51e5:	8b 78 08             	mov    0x8(%rax),%edi
    51e8:	e8 83 f4 ff ff       	call   4670 <add_read_request>
              free(req);
    51ed:	4c 89 ff             	mov    %r15,%rdi
    51f0:	e8 eb d0 ff ff       	call   22e0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    51f5:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
	if (cqe)
    51fc:	48 85 c0             	test   %rax,%rax
    51ff:	0f 85 13 01 00 00    	jne    5318 <io_thread+0x548>
	unsigned int head, next = sq->sqe_tail + 1;
    5205:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    520b:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5211:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5214:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    521b:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    521d:	f6 c1 02             	test   $0x2,%cl
    5220:	74 00                	je     5222 <io_thread+0x452>
	if (next - head <= sq->ring_entries) {
    5222:	89 d0                	mov    %edx,%eax
    5224:	29 f0                	sub    %esi,%eax
    5226:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    522c:	0f 82 cf d3 ff ff    	jb     2601 <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5232:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5235:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    523b:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    523f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5242:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5248:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    524b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5251:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5253:	41 8b 54 24 50       	mov    0x50(%r12),%edx
	sqe->user_data = (unsigned long) data;
    5258:	48 8b b5 98 fa ff ff 	mov    -0x568(%rbp),%rsi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    525f:	48 c1 e0 06          	shl    $0x6,%rax
    5263:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    526a:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5270:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5273:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    527b:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    527f:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5287:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    528f:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5293:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5297:	e8 c4 d0 ff ff       	call   2360 <io_uring_submit@plt>
  while (data->running == 1) {
    529c:	41 83 7c 24 34 01    	cmpl   $0x1,0x34(%r12)
    52a2:	0f 84 28 fe ff ff    	je     50d0 <io_thread+0x300>
    52a8:	48 8d 3d 42 1f 00 00 	lea    0x1f42(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    52af:	e8 5c d0 ff ff       	call   2310 <puts@plt>
}
    52b4:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    52b8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    52c1:	0f 85 25 02 00 00    	jne    54ec <io_thread+0x71c>
    52c7:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    52ce:	31 c0                	xor    %eax,%eax
    52d0:	5b                   	pop    %rbx
    52d1:	41 5c                	pop    %r12
    52d3:	41 5d                	pop    %r13
    52d5:	41 5e                	pop    %r14
    52d7:	41 5f                	pop    %r15
    52d9:	5d                   	pop    %rbp
    52da:	c3                   	ret
    52db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    52e0:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    52e7:	48 85 c0             	test   %rax,%rax
    52ea:	0f 84 58 fe ff ff    	je     5148 <io_thread+0x378>
      if (cqe->user_data == 1) {
    52f0:	48 83 38 01          	cmpq   $0x1,(%rax)
    52f4:	0f 84 6e 01 00 00    	je     5468 <io_thread+0x698>
    52fa:	48 8d 3d b7 1e 00 00 	lea    0x1eb7(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    5301:	e8 0a d0 ff ff       	call   2310 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5306:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    530d:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    5310:	e9 7f fe ff ff       	jmp    5194 <io_thread+0x3c4>
    5315:	0f 1f 00             	nopl   (%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5318:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
    531f:	8b 02                	mov    (%rdx),%eax
    5321:	83 c0 01             	add    $0x1,%eax
    5324:	89 02                	mov    %eax,(%rdx)
}
    5326:	e9 da fe ff ff       	jmp    5205 <io_thread+0x435>
    532b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              if (!cqe->res) {
    5330:	85 c0                	test   %eax,%eax
    5332:	75 7c                	jne    53b0 <io_thread+0x5e0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5334:	48 8b 0d e5 4c 00 00 	mov    0x4ce5(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    533b:	ba 0f 00 00 00       	mov    $0xf,%edx
    5340:	be 01 00 00 00       	mov    $0x1,%esi
    5345:	48 8d 3d 95 1e 00 00 	lea    0x1e95(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    534c:	e8 af d1 ff ff       	call   2500 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5351:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    5358:	e9 9f fe ff ff       	jmp    51fc <io_thread+0x42c>
    535d:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    5360:	41 8b 47 04          	mov    0x4(%r15),%eax
    5364:	45 31 ed             	xor    %r13d,%r13d
    5367:	85 c0                	test   %eax,%eax
    5369:	7e 20                	jle    538b <io_thread+0x5bb>
    536b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  free(req->iov[i].iov_base);
    5370:	4c 89 e8             	mov    %r13,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5373:	49 83 c5 01          	add    $0x1,%r13
                  free(req->iov[i].iov_base);
    5377:	48 c1 e0 04          	shl    $0x4,%rax
    537b:	49 8b 7c 07 10       	mov    0x10(%r15,%rax,1),%rdi
    5380:	e8 5b cf ff ff       	call   22e0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5385:	45 39 6f 04          	cmp    %r13d,0x4(%r15)
    5389:	7f e5                	jg     5370 <io_thread+0x5a0>
              close(req->client_socket);
    538b:	41 8b 7f 08          	mov    0x8(%r15),%edi
    538f:	e8 fc cf ff ff       	call   2390 <close@plt>
              free(req);
    5394:	4c 89 ff             	mov    %r15,%rdi
    5397:	e8 44 cf ff ff       	call   22e0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    539c:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    53a3:	e9 54 fe ff ff       	jmp    51fc <io_thread+0x42c>
    53a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int i = 0; i < dest_sz; i++) {
    53b0:	49 8b 57 10          	mov    0x10(%r15),%rdx
    53b4:	48 8b 85 80 fa ff ff 	mov    -0x580(%rbp),%rax
    53bb:	48 8d 75 c0          	lea    -0x40(%rbp),%rsi
    53bf:	eb 14                	jmp    53d5 <io_thread+0x605>
    53c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    53c8:	48 83 c0 01          	add    $0x1,%rax
    53cc:	48 83 c2 01          	add    $0x1,%rdx
    53d0:	48 39 c6             	cmp    %rax,%rsi
    53d3:	74 4b                	je     5420 <io_thread+0x650>
        dest[i] = src[i];
    53d5:	0f b6 0a             	movzbl (%rdx),%ecx
    53d8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    53da:	80 f9 0d             	cmp    $0xd,%cl
    53dd:	75 e9                	jne    53c8 <io_thread+0x5f8>
    53df:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    53e3:	75 e3                	jne    53c8 <io_thread+0x5f8>
            dest[i] = '\0';
    53e5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    53e8:	48 8b bd 80 fa ff ff 	mov    -0x580(%rbp),%rdi
    53ef:	48 89 da             	mov    %rbx,%rdx
    53f2:	41 8b 77 08          	mov    0x8(%r15),%esi
    53f6:	e8 35 f7 ff ff       	call   4b30 <handle_http_method>
              free(req->iov[0].iov_base);
    53fb:	49 8b 7f 10          	mov    0x10(%r15),%rdi
    53ff:	e8 dc ce ff ff       	call   22e0 <free@plt>
              free(req);
    5404:	4c 89 ff             	mov    %r15,%rdi
    5407:	e8 d4 ce ff ff       	call   22e0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    540c:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    5413:	e9 e4 fd ff ff       	jmp    51fc <io_thread+0x42c>
    5418:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5420:	48 8b 0d f9 4b 00 00 	mov    0x4bf9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5427:	ba 12 00 00 00       	mov    $0x12,%edx
    542c:	be 01 00 00 00       	mov    $0x1,%esi
    5431:	48 8d 3d ff 1c 00 00 	lea    0x1cff(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5438:	e8 c3 d0 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    543d:	bf 01 00 00 00       	mov    $0x1,%edi
    5442:	e8 99 d0 ff ff       	call   24e0 <exit@plt>
    5447:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5450:	e9 cd fb ff ff       	jmp    5022 <io_thread+0x252>
    5455:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5458:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	return err;
    545f:	e9 8c fe ff ff       	jmp    52f0 <io_thread+0x520>
    5464:	0f 1f 40 00          	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5468:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    546f:	48 8d 3d 2e 1d 00 00 	lea    0x1d2e(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    5476:	8b 02                	mov    (%rdx),%eax
    5478:	83 c0 01             	add    $0x1,%eax
    547b:	89 02                	mov    %eax,(%rdx)
    547d:	e8 8e ce ff ff       	call   2310 <puts@plt>
    5482:	e9 21 fe ff ff       	jmp    52a8 <io_thread+0x4d8>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5487:	f7 d8                	neg    %eax
    5489:	44 89 85 ac fa ff ff 	mov    %r8d,-0x554(%rbp)
    5490:	89 c7                	mov    %eax,%edi
    5492:	e8 a9 d0 ff ff       	call   2540 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5497:	48 8b 3d 82 4b 00 00 	mov    0x4b82(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    549e:	be 01 00 00 00       	mov    $0x1,%esi
    54a3:	44 8b 85 ac fa ff ff 	mov    -0x554(%rbp),%r8d
    54aa:	48 89 c1             	mov    %rax,%rcx
    54ad:	48 8d 15 84 1f 00 00 	lea    0x1f84(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    54b4:	31 c0                	xor    %eax,%eax
    54b6:	e8 55 d0 ff ff       	call   2510 <__fprintf_chk@plt>
          exit(1);
    54bb:	bf 01 00 00 00       	mov    $0x1,%edi
    54c0:	e8 1b d0 ff ff       	call   24e0 <exit@plt>
    54c5:	48 8b 0d 54 4b 00 00 	mov    0x4b54(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    54cc:	ba 28 00 00 00       	mov    $0x28,%edx
    54d1:	be 01 00 00 00       	mov    $0x1,%esi
    54d6:	48 8d 3d 2b 1f 00 00 	lea    0x1f2b(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    54dd:	e8 1e d0 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    54e2:	bf 01 00 00 00       	mov    $0x1,%edi
    54e7:	e8 f4 cf ff ff       	call   24e0 <exit@plt>
}
    54ec:	e8 5f ce ff ff       	call   2350 <__stack_chk_fail@plt>
    54f1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    54fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005500 <sendm>:
int sendm(struct BarrierTask *data) {
    5500:	f3 0f 1e fa          	endbr64
    5504:	55                   	push   %rbp
    5505:	48 89 e5             	mov    %rsp,%rbp
    5508:	41 57                	push   %r15
    550a:	41 56                	push   %r14
    550c:	41 55                	push   %r13
    550e:	41 54                	push   %r12
    5510:	53                   	push   %rbx
    5511:	48 83 ec 28          	sub    $0x28,%rsp
    5515:	ff 15 cd 4a 00 00    	call   *0x4acd(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  if (data->sending == 1) {
    551b:	83 bf f8 00 00 00 01 	cmpl   $0x1,0xf8(%rdi)
int sendm(struct BarrierTask *data) {
    5522:	48 89 fa             	mov    %rdi,%rdx
  if (data->sending == 1) {
    5525:	0f 85 a5 01 00 00    	jne    56d0 <sendm+0x1d0>
      for (int n = 0 ; n < data->thread_count; n++) {
    552b:	48 8d 9f 00 01 00 00 	lea    0x100(%rdi),%rbx
    5532:	8b 87 b4 00 00 00    	mov    0xb4(%rdi),%eax
    5538:	45 31 ff             	xor    %r15d,%r15d
    553b:	48 89 5d c8          	mov    %rbx,-0x38(%rbp)
    553f:	48 8d 9f 08 01 00 00 	lea    0x108(%rdi),%rbx
    5546:	48 89 5d c0          	mov    %rbx,-0x40(%rbp)
    554a:	85 c0                	test   %eax,%eax
    554c:	0f 8e d6 00 00 00    	jle    5628 <sendm+0x128>
    5552:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (n == data->thread_index) { continue; }
    5558:	44 39 ba b0 00 00 00 	cmp    %r15d,0xb0(%rdx)
    555f:	0f 84 b6 00 00 00    	je     561b <sendm+0x11b>
        struct Data *them = data->mailboxes[n].higher;
    5565:	4d 89 f9             	mov    %r15,%r9
    5568:	49 c1 e1 05          	shl    $0x5,%r9
    556c:	4c 03 8a e8 00 00 00 	add    0xe8(%rdx),%r9
    5573:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    5577:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    557b:	4d 63 42 10          	movslq 0x10(%r10),%r8
    557f:	4d 39 c3             	cmp    %r8,%r11
    5582:	0f 8d 8a 00 00 00    	jge    5612 <sendm+0x112>
    5588:	4c 89 c6             	mov    %r8,%rsi
    558b:	48 8b 9a 88 00 00 00 	mov    0x88(%rdx),%rbx
    5592:	4d 8b 71 10          	mov    0x10(%r9),%r14
    5596:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5599:	49 8b 0a             	mov    (%r10),%rcx
    559c:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    55a0:	48 83 f8 02          	cmp    $0x2,%rax
    55a4:	0f 86 0e 01 00 00    	jbe    56b8 <sendm+0x1b8>
    55aa:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    55b2:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    55ba:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    55be:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    55c2:	4c 39 6d c8          	cmp    %r13,-0x38(%rbp)
    55c6:	73 78                	jae    5640 <sendm+0x140>
    55c8:	4c 8b 6d c0          	mov    -0x40(%rbp),%r13
    55cc:	4d 39 ec             	cmp    %r13,%r12
    55cf:	73 6f                	jae    5640 <sendm+0x140>
    55d1:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    55d5:	48 01 cf             	add    %rcx,%rdi
    55d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    55e0:	48 8b 82 00 01 00 00 	mov    0x100(%rdx),%rax
        for (; them->messages_count < min;) {
    55e7:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    55eb:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    55ef:	4c 39 df             	cmp    %r11,%rdi
    55f2:	75 ec                	jne    55e0 <sendm+0xe0>
    55f4:	0f 1f 40 00          	nopl   0x0(%rax)
    55f8:	48 01 f3             	add    %rsi,%rbx
    55fb:	4c 01 f6             	add    %r14,%rsi
    55fe:	48 89 9a 88 00 00 00 	mov    %rbx,0x88(%rdx)
    5605:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5609:	4d 89 42 08          	mov    %r8,0x8(%r10)
    560d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5612:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5615:	8b 82 b4 00 00 00    	mov    0xb4(%rdx),%eax
    561b:	49 83 c7 01          	add    $0x1,%r15
    561f:	44 39 f8             	cmp    %r15d,%eax
    5622:	0f 8f 30 ff ff ff    	jg     5558 <sendm+0x58>
}
    5628:	48 83 c4 28          	add    $0x28,%rsp
    562c:	31 c0                	xor    %eax,%eax
    562e:	5b                   	pop    %rbx
    562f:	41 5c                	pop    %r12
    5631:	41 5d                	pop    %r13
    5633:	41 5e                	pop    %r14
    5635:	41 5f                	pop    %r15
    5637:	5d                   	pop    %rbp
    5638:	c3                   	ret
    5639:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5640:	48 8b 82 00 01 00 00 	mov    0x100(%rdx),%rax
    5647:	49 89 f5             	mov    %rsi,%r13
    564a:	4c 89 e7             	mov    %r12,%rdi
    564d:	49 d1 ed             	shr    %r13
    5650:	49 c1 e5 04          	shl    $0x4,%r13
    5654:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5659:	4c 89 6d b8          	mov    %r13,-0x48(%rbp)
    565d:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5661:	4d 01 e5             	add    %r12,%r13
    5664:	f6 45 b8 10          	testb  $0x10,-0x48(%rbp)
    5668:	74 16                	je     5680 <sendm+0x180>
          them->messages[them->messages_count++] = data->message; 
    566a:	48 83 c7 10          	add    $0x10,%rdi
    566e:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5673:	4c 39 ef             	cmp    %r13,%rdi
    5676:	74 18                	je     5690 <sendm+0x190>
    5678:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          them->messages[them->messages_count++] = data->message; 
    5680:	0f 11 07             	movups %xmm0,(%rdi)
    5683:	48 83 c7 20          	add    $0x20,%rdi
    5687:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    568b:	4c 39 ef             	cmp    %r13,%rdi
    568e:	75 f0                	jne    5680 <sendm+0x180>
    5690:	48 89 f7             	mov    %rsi,%rdi
    5693:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5697:	4c 01 df             	add    %r11,%rdi
    569a:	40 f6 c6 01          	test   $0x1,%sil
    569e:	0f 84 54 ff ff ff    	je     55f8 <sendm+0xf8>
          them->messages[them->messages_count++] = data->message; 
    56a4:	48 8b 82 00 01 00 00 	mov    0x100(%rdx),%rax
    56ab:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    56af:	e9 44 ff ff ff       	jmp    55f8 <sendm+0xf8>
    56b4:	0f 1f 40 00          	nopl   0x0(%rax)
    56b8:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    56c0:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    56c8:	e9 04 ff ff ff       	jmp    55d1 <sendm+0xd1>
    56cd:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    56d0:	48 8d 3d 2d 1b 00 00 	lea    0x1b2d(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    56d7:	e8 34 cc ff ff       	call   2310 <puts@plt>
    56dc:	e9 47 ff ff ff       	jmp    5628 <sendm+0x128>
    56e1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    56ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000056f0 <receive>:
int receive(struct BarrierTask *data) {
    56f0:	f3 0f 1e fa          	endbr64
    56f4:	55                   	push   %rbp
    56f5:	48 89 e5             	mov    %rsp,%rbp
    56f8:	41 55                	push   %r13
    56fa:	41 54                	push   %r12
    56fc:	53                   	push   %rbx
    56fd:	48 83 ec 08          	sub    $0x8,%rsp
    5701:	ff 15 e1 48 00 00    	call   *0x48e1(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  for (int n = 0 ; n < data->thread_count; n++) {
    5707:	45 31 e4             	xor    %r12d,%r12d
    570a:	8b 87 b4 00 00 00    	mov    0xb4(%rdi),%eax
int receive(struct BarrierTask *data) {
    5710:	48 89 fa             	mov    %rdi,%rdx
  for (int n = 0 ; n < data->thread_count; n++) {
    5713:	85 c0                	test   %eax,%eax
    5715:	0f 8e d9 00 00 00    	jle    57f4 <receive+0x104>
    571b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5720:	4c 89 e6             	mov    %r12,%rsi
    5723:	48 c1 e6 05          	shl    $0x5,%rsi
    5727:	48 03 b2 e8 00 00 00 	add    0xe8(%rdx),%rsi
    572e:	4c 8b 2e             	mov    (%rsi),%r13
    for (int x = 0 ; x < me->messages_count ; x++) {
    5731:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    5735:	48 85 ff             	test   %rdi,%rdi
    5738:	0f 8e 9a 00 00 00    	jle    57d8 <receive+0xe8>
      data->sends++;
    573e:	48 8b 8a f0 00 00 00 	mov    0xf0(%rdx),%rcx
    5745:	4d 8b 45 00          	mov    0x0(%r13),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5749:	4c 63 1a             	movslq (%rdx),%r11
    574c:	49 89 c9             	mov    %rcx,%r9
    574f:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5753:	49 f7 d9             	neg    %r9
    5756:	48 01 c7             	add    %rax,%rdi
    5759:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    575d:	4c 8b 8a 88 00 00 00 	mov    0x88(%rdx),%r9
      data->mailboxes[n].received++;
    5764:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    5768:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    576b:	49 29 c8             	sub    %rcx,%r8
    576e:	eb 09                	jmp    5779 <receive+0x89>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5770:	48 83 c0 01          	add    $0x1,%rax
    5774:	48 39 c7             	cmp    %rax,%rdi
    5777:	74 5f                	je     57d8 <receive+0xe8>
      data->n++;
    5779:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    577d:	48 89 82 f0 00 00 00 	mov    %rax,0xf0(%rdx)
      data->n++;
    5784:	48 89 8a 88 00 00 00 	mov    %rcx,0x88(%rdx)
      data->mailboxes[n].received++;
    578b:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    578f:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5793:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5798:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    579c:	75 d2                	jne    5770 <receive+0x80>
    579e:	48 63 9a b0 00 00 00 	movslq 0xb0(%rdx),%rbx
    57a5:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    57a9:	75 c5                	jne    5770 <receive+0x80>
    57ab:	bf 01 00 00 00       	mov    $0x1,%edi
    57b0:	b9 01 00 00 00       	mov    $0x1,%ecx
    57b5:	ba 01 00 00 00       	mov    $0x1,%edx
    57ba:	31 c0                	xor    %eax,%eax
    57bc:	48 8d 35 9d 1c 00 00 	lea    0x1c9d(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    57c3:	e8 b8 cc ff ff       	call   2480 <__printf_chk@plt>
        exit(1);
    57c8:	bf 01 00 00 00       	mov    $0x1,%edi
    57cd:	e8 0e cd ff ff       	call   24e0 <exit@plt>
    57d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    57d8:	49 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%r13)
    asm volatile ("sfence" ::: "memory");
    57e0:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    57e3:	49 83 c4 01          	add    $0x1,%r12
    57e7:	44 39 a2 b4 00 00 00 	cmp    %r12d,0xb4(%rdx)
    57ee:	0f 8f 2c ff ff ff    	jg     5720 <receive+0x30>
}
    57f4:	48 83 c4 08          	add    $0x8,%rsp
    57f8:	31 c0                	xor    %eax,%eax
    57fa:	5b                   	pop    %rbx
    57fb:	41 5c                	pop    %r12
    57fd:	41 5d                	pop    %r13
    57ff:	5d                   	pop    %rbp
    5800:	c3                   	ret
    5801:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    580c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005810 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5810:	f3 0f 1e fa          	endbr64
    5814:	55                   	push   %rbp
    5815:	48 89 e5             	mov    %rsp,%rbp
    5818:	41 57                	push   %r15
    581a:	41 56                	push   %r14
    581c:	41 55                	push   %r13
    581e:	41 54                	push   %r12
    5820:	53                   	push   %rbx
    5821:	48 83 ec 28          	sub    $0x28,%rsp
    5825:	ff 15 bd 47 00 00    	call   *0x47bd(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  if (data->thread_index == data->task_index) {
    582b:	8b 07                	mov    (%rdi),%eax
int barriered_work(struct BarrierTask *data) {
    582d:	48 89 fb             	mov    %rdi,%rbx
  if (data->thread_index == data->task_index) {
    5830:	39 87 b0 00 00 00    	cmp    %eax,0xb0(%rdi)
    5836:	0f 84 44 01 00 00    	je     5980 <barriered_work+0x170>
    receive(data);
    583c:	e8 af fe ff ff       	call   56f0 <receive>
    while (data->scheduled == 1) {
    5841:	83 bb c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbx)
    5848:	75 1a                	jne    5864 <barriered_work+0x54>
    584a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->n++;
    5850:	48 83 83 88 00 00 00 01 	addq   $0x1,0x88(%rbx)
      asm volatile ("sfence" ::: "memory");
    5858:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    585b:	83 bb c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbx)
    5862:	74 ec                	je     5850 <barriered_work+0x40>
  if (data->sending == 1) {
    5864:	83 bb f8 00 00 00 01 	cmpl   $0x1,0xf8(%rbx)
    586b:	0f 85 89 02 00 00    	jne    5afa <barriered_work+0x2ea>
      for (int n = 0 ; n < data->thread_count; n++) {
    5871:	8b 83 b4 00 00 00    	mov    0xb4(%rbx),%eax
    5877:	85 c0                	test   %eax,%eax
    5879:	0f 8e 87 02 00 00    	jle    5b06 <barriered_work+0x2f6>
    587f:	48 8d 8b 00 01 00 00 	lea    0x100(%rbx),%rcx
    5886:	45 31 ff             	xor    %r15d,%r15d
    5889:	48 89 4d c8          	mov    %rcx,-0x38(%rbp)
    588d:	48 8d 8b 08 01 00 00 	lea    0x108(%rbx),%rcx
    5894:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
    5898:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        if (n == data->thread_index) { continue; }
    58a0:	44 39 bb b0 00 00 00 	cmp    %r15d,0xb0(%rbx)
    58a7:	0f 84 bf 00 00 00    	je     596c <barriered_work+0x15c>
        struct Data *them = data->mailboxes[n].higher;
    58ad:	4d 89 f8             	mov    %r15,%r8
    58b0:	49 c1 e0 05          	shl    $0x5,%r8
    58b4:	4c 03 83 e8 00 00 00 	add    0xe8(%rbx),%r8
    58bb:	4d 8b 48 08          	mov    0x8(%r8),%r9
        for (; them->messages_count < min;) {
    58bf:	4d 8b 51 08          	mov    0x8(%r9),%r10
    58c3:	49 63 79 10          	movslq 0x10(%r9),%rdi
    58c7:	49 39 fa             	cmp    %rdi,%r10
    58ca:	0f 8d 93 00 00 00    	jge    5963 <barriered_work+0x153>
    58d0:	48 89 f9             	mov    %rdi,%rcx
    58d3:	4c 8b b3 88 00 00 00 	mov    0x88(%rbx),%r14
    58da:	4d 8b 68 10          	mov    0x10(%r8),%r13
    58de:	4c 29 d1             	sub    %r10,%rcx
          them->messages[them->messages_count++] = data->message; 
    58e1:	49 8b 11             	mov    (%r9),%rdx
    58e4:	48 8d 41 ff          	lea    -0x1(%rcx),%rax
    58e8:	48 83 f8 02          	cmp    $0x2,%rax
    58ec:	0f 86 a6 02 00 00    	jbe    5b98 <barriered_work+0x388>
    58f2:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    58fa:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    5902:	4c 8d 1c 02          	lea    (%rdx,%rax,1),%r11
    5906:	4c 8d 24 32          	lea    (%rdx,%rsi,1),%r12
    590a:	4c 39 65 c8          	cmp    %r12,-0x38(%rbp)
    590e:	0f 83 0c 02 00 00    	jae    5b20 <barriered_work+0x310>
    5914:	4c 8b 65 c0          	mov    -0x40(%rbp),%r12
    5918:	4d 39 e3             	cmp    %r12,%r11
    591b:	0f 83 ff 01 00 00    	jae    5b20 <barriered_work+0x310>
    5921:	4c 8d 14 02          	lea    (%rdx,%rax,1),%r10
    5925:	48 01 d6             	add    %rdx,%rsi
    5928:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5930:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
        for (; them->messages_count < min;) {
    5937:	49 83 c2 08          	add    $0x8,%r10
          them->messages[them->messages_count++] = data->message; 
    593b:	49 89 42 f8          	mov    %rax,-0x8(%r10)
        for (; them->messages_count < min;) {
    593f:	49 39 f2             	cmp    %rsi,%r10
    5942:	75 ec                	jne    5930 <barriered_work+0x120>
    5944:	0f 1f 40 00          	nopl   0x0(%rax)
    5948:	49 8d 34 0e          	lea    (%r14,%rcx,1),%rsi
    594c:	4c 01 e9             	add    %r13,%rcx
    594f:	48 89 b3 88 00 00 00 	mov    %rsi,0x88(%rbx)
    5956:	49 89 48 10          	mov    %rcx,0x10(%r8)
    595a:	49 89 79 08          	mov    %rdi,0x8(%r9)
    595e:	48 89 44 fa f8       	mov    %rax,-0x8(%rdx,%rdi,8)
        asm volatile ("sfence" ::: "memory");
    5963:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5966:	8b 83 b4 00 00 00    	mov    0xb4(%rbx),%eax
    596c:	49 83 c7 01          	add    $0x1,%r15
    5970:	44 39 f8             	cmp    %r15d,%eax
    5973:	0f 8f 27 ff ff ff    	jg     58a0 <barriered_work+0x90>
    5979:	e9 88 01 00 00       	jmp    5b06 <barriered_work+0x2f6>
    597e:	66 90                	xchg   %ax,%ax
      receive(data);
    5980:	e8 6b fd ff ff       	call   56f0 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    5985:	4c 63 8b b4 00 00 00 	movslq 0xb4(%rbx),%r9
        int t = data->task_index;
    598c:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    598e:	45 85 c9             	test   %r9d,%r9d
    5991:	0f 8e 85 00 00 00    	jle    5a1c <barriered_work+0x20c>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5997:	48 8b 93 a8 00 00 00 	mov    0xa8(%rbx),%rdx
    599e:	4c 8b 52 10          	mov    0x10(%rdx),%r10
    59a2:	48 63 d0             	movslq %eax,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
    59a5:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59a8:	4c 8d 1c 52          	lea    (%rdx,%rdx,2),%r11
              int next_task = abs((t + 1) % (data->thread_count));
    59ac:	99                   	cltd
    59ad:	41 f7 f9             	idiv   %r9d
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59b0:	49 c1 e3 07          	shl    $0x7,%r11
    59b4:	4c 89 d7             	mov    %r10,%rdi
    59b7:	4f 8d 2c ca          	lea    (%r10,%r9,8),%r13
              int next_task = abs((t + 1) % (data->thread_count));
    59bb:	89 d0                	mov    %edx,%eax
    59bd:	f7 d8                	neg    %eax
    59bf:	0f 48 c2             	cmovs  %edx,%eax
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59c2:	45 31 c0             	xor    %r8d,%r8d
    59c5:	48 98                	cltq
    59c7:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
    59cb:	49 c1 e4 07          	shl    $0x7,%r12
    59cf:	90                   	nop
int barriered_work(struct BarrierTask *data) {
    59d0:	31 c0                	xor    %eax,%eax
    59d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59d8:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    59dc:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    59e0:	4a 8b 8c 22 e8 00 00 00 	mov    0xe8(%rdx,%r12,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59e8:	48 8b 17             	mov    (%rdi),%rdx
    59eb:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    59ef:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    59f2:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59f6:	48 c1 e2 05          	shl    $0x5,%rdx
    59fa:	4a 03 94 1e e8 00 00 00 	add    0xe8(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5a02:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    5a06:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    5a0a:	49 39 c1             	cmp    %rax,%r9
    5a0d:	75 c9                	jne    59d8 <barriered_work+0x1c8>
        for (int y = 0; y < data->thread_count ; y++) {
    5a0f:	48 83 c7 08          	add    $0x8,%rdi
    5a13:	49 83 c0 20          	add    $0x20,%r8
    5a17:	49 39 fd             	cmp    %rdi,%r13
    5a1a:	75 b4                	jne    59d0 <barriered_work+0x1c0>
      asm volatile ("sfence" ::: "memory");
    5a1c:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5a1f:	48 8b b3 d8 00 00 00 	mov    0xd8(%rbx),%rsi
    5a26:	31 ff                	xor    %edi,%edi
    5a28:	48 c1 e6 05          	shl    $0x5,%rsi
    5a2c:	48 03 b3 c8 00 00 00 	add    0xc8(%rbx),%rsi
    5a33:	e8 f8 c8 ff ff       	call   2330 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5a38:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    while (data->scheduled == 1) {
    5a3f:	83 bb c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5a46:	48 8b 50 38          	mov    0x38(%rax),%rdx
    5a4a:	8b 4a 10             	mov    0x10(%rdx),%ecx
    5a4d:	44 8d 61 01          	lea    0x1(%rcx),%r12d
    5a51:	44 89 62 10          	mov    %r12d,0x10(%rdx)
    while (data->scheduled == 1) {
    5a55:	75 5e                	jne    5ab5 <barriered_work+0x2a5>
    5a57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a60:	48 63 93 b0 00 00 00 	movslq 0xb0(%rbx),%rdx
    5a67:	48 8b 40 10          	mov    0x10(%rax),%rax
      data->n++;
    5a6b:	48 83 83 88 00 00 00 01 	addq   $0x1,0x88(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a73:	48 8b 14 d0          	mov    (%rax,%rdx,8),%rdx
    5a77:	48 63 03             	movslq (%rbx),%rax
    5a7a:	48 8d 3c 40          	lea    (%rax,%rax,2),%rdi
    5a7e:	48 c1 e7 07          	shl    $0x7,%rdi
    5a82:	48 03 7a 28          	add    0x28(%rdx),%rdi
    5a86:	ff 93 a0 00 00 00    	call   *0xa0(%rbx)
      asm volatile ("sfence" ::: "memory");
    5a8c:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5a8f:	83 bb c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    5a96:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    while (data->scheduled == 1) {
    5a9d:	74 c1                	je     5a60 <barriered_work+0x250>
    if (modcount != data->thread->protected_state->modcount) {
    5a9f:	48 8b 40 38          	mov    0x38(%rax),%rax
    5aa3:	44 3b 60 10          	cmp    0x10(%rax),%r12d
    5aa7:	74 0c                	je     5ab5 <barriered_work+0x2a5>
    5aa9:	48 8d 3d 60 17 00 00 	lea    0x1760(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    5ab0:	e8 5b c8 ff ff       	call   2310 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5ab5:	48 8b b3 d8 00 00 00 	mov    0xd8(%rbx),%rsi
    5abc:	31 ff                	xor    %edi,%edi
    5abe:	48 c1 e6 05          	shl    $0x5,%rsi
    5ac2:	48 03 b3 c8 00 00 00 	add    0xc8(%rbx),%rsi
    5ac9:	48 83 c6 10          	add    $0x10,%rsi
    5acd:	e8 5e c8 ff ff       	call   2330 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5ad2:	48 8b 83 d8 00 00 00 	mov    0xd8(%rbx),%rax
    5ad9:	48 83 c0 01          	add    $0x1,%rax
    5add:	48 99                	cqto
    5adf:	48 f7 bb d0 00 00 00 	idivq  0xd0(%rbx)
  if (data->sending == 1) {
    5ae6:	83 bb f8 00 00 00 01 	cmpl   $0x1,0xf8(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5aed:	48 89 93 d8 00 00 00 	mov    %rdx,0xd8(%rbx)
  if (data->sending == 1) {
    5af4:	0f 84 b3 00 00 00    	je     5bad <barriered_work+0x39d>
    5afa:	48 8d 3d 03 17 00 00 	lea    0x1703(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5b01:	e8 0a c8 ff ff       	call   2310 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5b06:	0f ae f8             	sfence
}
    5b09:	48 83 c4 28          	add    $0x28,%rsp
    5b0d:	31 c0                	xor    %eax,%eax
    5b0f:	5b                   	pop    %rbx
    5b10:	41 5c                	pop    %r12
    5b12:	41 5d                	pop    %r13
    5b14:	41 5e                	pop    %r14
    5b16:	41 5f                	pop    %r15
    5b18:	5d                   	pop    %rbp
    5b19:	c3                   	ret
    5b1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5b20:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
    5b27:	49 89 cc             	mov    %rcx,%r12
    5b2a:	4c 89 de             	mov    %r11,%rsi
    5b2d:	49 d1 ec             	shr    %r12
    5b30:	49 c1 e4 04          	shl    $0x4,%r12
    5b34:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5b39:	4c 89 65 b8          	mov    %r12,-0x48(%rbp)
    5b3d:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5b41:	4d 01 dc             	add    %r11,%r12
    5b44:	f6 45 b8 10          	testb  $0x10,-0x48(%rbp)
    5b48:	74 16                	je     5b60 <barriered_work+0x350>
          them->messages[them->messages_count++] = data->message; 
    5b4a:	48 83 c6 10          	add    $0x10,%rsi
    5b4e:	41 0f 11 03          	movups %xmm0,(%r11)
        for (; them->messages_count < min;) {
    5b52:	49 39 f4             	cmp    %rsi,%r12
    5b55:	74 19                	je     5b70 <barriered_work+0x360>
    5b57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          them->messages[them->messages_count++] = data->message; 
    5b60:	0f 11 06             	movups %xmm0,(%rsi)
    5b63:	48 83 c6 20          	add    $0x20,%rsi
    5b67:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
        for (; them->messages_count < min;) {
    5b6b:	49 39 f4             	cmp    %rsi,%r12
    5b6e:	75 f0                	jne    5b60 <barriered_work+0x350>
    5b70:	48 89 ce             	mov    %rcx,%rsi
    5b73:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    5b77:	4c 01 d6             	add    %r10,%rsi
    5b7a:	f6 c1 01             	test   $0x1,%cl
    5b7d:	0f 84 c5 fd ff ff    	je     5948 <barriered_work+0x138>
          them->messages[them->messages_count++] = data->message; 
    5b83:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
    5b8a:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    5b8e:	e9 b5 fd ff ff       	jmp    5948 <barriered_work+0x138>
    5b93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5b98:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    5ba0:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    5ba8:	e9 74 fd ff ff       	jmp    5921 <barriered_work+0x111>
      for (int n = 0 ; n < data->thread_count; n++) {
    5bad:	8b 83 b4 00 00 00    	mov    0xb4(%rbx),%eax
    5bb3:	48 8d 8b 00 01 00 00 	lea    0x100(%rbx),%rcx
    5bba:	48 8d bb 08 01 00 00 	lea    0x108(%rbx),%rdi
    5bc1:	45 31 ff             	xor    %r15d,%r15d
    5bc4:	48 89 4d c8          	mov    %rcx,-0x38(%rbp)
    5bc8:	48 89 7d c0          	mov    %rdi,-0x40(%rbp)
    5bcc:	85 c0                	test   %eax,%eax
    5bce:	0f 8e 32 ff ff ff    	jle    5b06 <barriered_work+0x2f6>
    5bd4:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5bd8:	44 39 bb b0 00 00 00 	cmp    %r15d,0xb0(%rbx)
    5bdf:	0f 84 b6 00 00 00    	je     5c9b <barriered_work+0x48b>
        struct Data *them = data->mailboxes[n].higher;
    5be5:	4d 89 f8             	mov    %r15,%r8
    5be8:	49 c1 e0 05          	shl    $0x5,%r8
    5bec:	4c 03 83 e8 00 00 00 	add    0xe8(%rbx),%r8
    5bf3:	4d 8b 48 08          	mov    0x8(%r8),%r9
        for (; them->messages_count < min;) {
    5bf7:	4d 8b 51 08          	mov    0x8(%r9),%r10
    5bfb:	49 63 79 10          	movslq 0x10(%r9),%rdi
    5bff:	4c 39 d7             	cmp    %r10,%rdi
    5c02:	0f 8e 8a 00 00 00    	jle    5c92 <barriered_work+0x482>
    5c08:	48 89 f9             	mov    %rdi,%rcx
    5c0b:	4c 8b 9b 88 00 00 00 	mov    0x88(%rbx),%r11
    5c12:	4d 8b 70 10          	mov    0x10(%r8),%r14
    5c16:	4c 29 d1             	sub    %r10,%rcx
          them->messages[them->messages_count++] = data->message; 
    5c19:	49 8b 11             	mov    (%r9),%rdx
    5c1c:	48 8d 41 ff          	lea    -0x1(%rcx),%rax
    5c20:	48 83 f8 02          	cmp    $0x2,%rax
    5c24:	0f 86 fe 00 00 00    	jbe    5d28 <barriered_work+0x518>
    5c2a:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    5c32:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    5c3a:	4c 8d 24 02          	lea    (%rdx,%rax,1),%r12
    5c3e:	4c 8d 2c 32          	lea    (%rdx,%rsi,1),%r13
    5c42:	4c 39 6d c8          	cmp    %r13,-0x38(%rbp)
    5c46:	73 68                	jae    5cb0 <barriered_work+0x4a0>
    5c48:	4c 8b 6d c0          	mov    -0x40(%rbp),%r13
    5c4c:	4d 39 ec             	cmp    %r13,%r12
    5c4f:	73 5f                	jae    5cb0 <barriered_work+0x4a0>
    5c51:	4c 8d 14 02          	lea    (%rdx,%rax,1),%r10
    5c55:	48 01 d6             	add    %rdx,%rsi
    5c58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5c60:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
        for (; them->messages_count < min;) {
    5c67:	49 83 c2 08          	add    $0x8,%r10
          them->messages[them->messages_count++] = data->message; 
    5c6b:	49 89 42 f8          	mov    %rax,-0x8(%r10)
        for (; them->messages_count < min;) {
    5c6f:	49 39 f2             	cmp    %rsi,%r10
    5c72:	75 ec                	jne    5c60 <barriered_work+0x450>
    5c74:	0f 1f 40 00          	nopl   0x0(%rax)
    5c78:	49 01 cb             	add    %rcx,%r11
    5c7b:	4c 01 f1             	add    %r14,%rcx
    5c7e:	4c 89 9b 88 00 00 00 	mov    %r11,0x88(%rbx)
    5c85:	49 89 48 10          	mov    %rcx,0x10(%r8)
    5c89:	49 89 79 08          	mov    %rdi,0x8(%r9)
    5c8d:	48 89 44 fa f8       	mov    %rax,-0x8(%rdx,%rdi,8)
        asm volatile ("sfence" ::: "memory");
    5c92:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5c95:	8b 83 b4 00 00 00    	mov    0xb4(%rbx),%eax
    5c9b:	49 83 c7 01          	add    $0x1,%r15
    5c9f:	44 39 f8             	cmp    %r15d,%eax
    5ca2:	0f 8f 30 ff ff ff    	jg     5bd8 <barriered_work+0x3c8>
    5ca8:	e9 59 fe ff ff       	jmp    5b06 <barriered_work+0x2f6>
    5cad:	0f 1f 00             	nopl   (%rax)
    5cb0:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
    5cb7:	49 89 cd             	mov    %rcx,%r13
    5cba:	4c 89 e6             	mov    %r12,%rsi
    5cbd:	49 d1 ed             	shr    %r13
    5cc0:	49 c1 e5 04          	shl    $0x4,%r13
    5cc4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5cc9:	4c 89 6d b8          	mov    %r13,-0x48(%rbp)
    5ccd:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5cd1:	4d 01 e5             	add    %r12,%r13
    5cd4:	f6 45 b8 10          	testb  $0x10,-0x48(%rbp)
    5cd8:	74 16                	je     5cf0 <barriered_work+0x4e0>
          them->messages[them->messages_count++] = data->message; 
    5cda:	48 83 c6 10          	add    $0x10,%rsi
    5cde:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5ce3:	4c 39 ee             	cmp    %r13,%rsi
    5ce6:	74 18                	je     5d00 <barriered_work+0x4f0>
    5ce8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          them->messages[them->messages_count++] = data->message; 
    5cf0:	0f 11 06             	movups %xmm0,(%rsi)
    5cf3:	48 83 c6 20          	add    $0x20,%rsi
    5cf7:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
        for (; them->messages_count < min;) {
    5cfb:	4c 39 ee             	cmp    %r13,%rsi
    5cfe:	75 f0                	jne    5cf0 <barriered_work+0x4e0>
    5d00:	48 89 ce             	mov    %rcx,%rsi
    5d03:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    5d07:	4c 01 d6             	add    %r10,%rsi
    5d0a:	f6 c1 01             	test   $0x1,%cl
    5d0d:	0f 84 65 ff ff ff    	je     5c78 <barriered_work+0x468>
          them->messages[them->messages_count++] = data->message; 
    5d13:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
    5d1a:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    5d1e:	e9 55 ff ff ff       	jmp    5c78 <barriered_work+0x468>
    5d23:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5d28:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    5d30:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    5d38:	e9 14 ff ff ff       	jmp    5c51 <barriered_work+0x441>
    5d3d:	0f 1f 00             	nopl   (%rax)

0000000000005d40 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5d40:	f3 0f 1e fa          	endbr64
    5d44:	55                   	push   %rbp
    5d45:	48 89 e5             	mov    %rsp,%rbp
    5d48:	ff 15 9a 42 00 00    	call   *0x429a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5d4e:	48 8b 87 a8 00 00 00 	mov    0xa8(%rdi),%rax
    5d55:	48 8b 40 40          	mov    0x40(%rax),%rax
    5d59:	48 63 10             	movslq (%rax),%rdx
    5d5c:	85 d2                	test   %edx,%edx
    5d5e:	7e 2e                	jle    5d8e <barriered_work_ingest+0x4e>
    5d60:	48 8b 40 08          	mov    0x8(%rax),%rax
    5d64:	48 c1 e2 04          	shl    $0x4,%rdx
    5d68:	48 01 c2             	add    %rax,%rdx
    5d6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread->buffers->buffer[x].available == 1) {
    5d70:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5d74:	75 0f                	jne    5d85 <barriered_work_ingest+0x45>
      data->ingest_count++;
    5d76:	48 83 87 e0 00 00 00 01 	addq   $0x1,0xe0(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5d7e:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5d85:	48 83 c0 10          	add    $0x10,%rax
    5d89:	48 39 d0             	cmp    %rdx,%rax
    5d8c:	75 e2                	jne    5d70 <barriered_work_ingest+0x30>
  asm volatile ("sfence" ::: "memory");
    5d8e:	0f ae f8             	sfence
  barriered_work(data);
    5d91:	e8 7a fa ff ff       	call   5810 <barriered_work>
}
    5d96:	31 c0                	xor    %eax,%eax
    5d98:	5d                   	pop    %rbp
    5d99:	c3                   	ret
    5d9a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005da0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5da0:	f3 0f 1e fa          	endbr64
    5da4:	55                   	push   %rbp
    5da5:	48 89 e5             	mov    %rsp,%rbp
    5da8:	ff 15 3a 42 00 00    	call   *0x423a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
}
    5dae:	31 c0                	xor    %eax,%eax
    5db0:	5d                   	pop    %rbp
    5db1:	c3                   	ret
    5db2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5dbd:	0f 1f 00             	nopl   (%rax)

0000000000005dc0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5dc0:	f3 0f 1e fa          	endbr64
    5dc4:	55                   	push   %rbp
    5dc5:	48 89 e5             	mov    %rsp,%rbp
    5dc8:	ff 15 1a 42 00 00    	call   *0x421a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    5dce:	31 c0                	xor    %eax,%eax
    5dd0:	5d                   	pop    %rbp
    5dd1:	c3                   	ret
    5dd2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5ddd:	0f 1f 00             	nopl   (%rax)

0000000000005de0 <after>:
int after(struct timespec left, struct timespec right) {
    5de0:	f3 0f 1e fa          	endbr64
    5de4:	55                   	push   %rbp
    5de5:	48 89 e5             	mov    %rsp,%rbp
    5de8:	ff 15 fa 41 00 00    	call   *0x41fa(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  return left.tv_sec > right.tv_sec &&
    5dee:	31 c0                	xor    %eax,%eax
    5df0:	48 39 d7             	cmp    %rdx,%rdi
    5df3:	7e 08                	jle    5dfd <after+0x1d>
    5df5:	31 c0                	xor    %eax,%eax
    5df7:	48 39 ce             	cmp    %rcx,%rsi
    5dfa:	0f 9f c0             	setg   %al
}
    5dfd:	5d                   	pop    %rbp
    5dfe:	c3                   	ret
    5dff:	90                   	nop

0000000000005e00 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5e00:	f3 0f 1e fa          	endbr64
    5e04:	55                   	push   %rbp
    5e05:	48 89 e5             	mov    %rsp,%rbp
    5e08:	ff 15 da 41 00 00    	call   *0x41da(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  return 0;
    5e0e:	31 c0                	xor    %eax,%eax
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5e10:	4c 8b 5d 10          	mov    0x10(%rbp),%r11
    5e14:	4c 8b 55 18          	mov    0x18(%rbp),%r10
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e18:	48 39 d7             	cmp    %rdx,%rdi
    5e1b:	7f 18                	jg     5e35 <within+0x35>
    5e1d:	4d 39 d8             	cmp    %r11,%r8
    5e20:	0f 9e c2             	setle  %dl
    5e23:	48 39 ce             	cmp    %rcx,%rsi
    5e26:	0f 9e c0             	setle  %al
    5e29:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e2b:	31 c0                	xor    %eax,%eax
    5e2d:	4d 39 d1             	cmp    %r10,%r9
    5e30:	0f 9e c0             	setle  %al
    5e33:	21 d0                	and    %edx,%eax
}
    5e35:	5d                   	pop    %rbp
    5e36:	c3                   	ret
    5e37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005e40 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5e40:	f3 0f 1e fa          	endbr64
    5e44:	55                   	push   %rbp
    5e45:	48 89 e5             	mov    %rsp,%rbp
    5e48:	ff 15 9a 41 00 00    	call   *0x419a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    5e4e:	48 8b 7d 10          	mov    0x10(%rbp),%rdi
    5e52:	48 8b 75 30          	mov    0x30(%rbp),%rsi
    5e56:	4c 8b 4d 20          	mov    0x20(%rbp),%r9
    5e5a:	4c 8b 55 28          	mov    0x28(%rbp),%r10
    5e5e:	4c 8b 45 40          	mov    0x40(%rbp),%r8
    5e62:	4c 8b 5d 48          	mov    0x48(%rbp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5e66:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
    5e6a:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  return left.tv_sec > right.tv_sec &&
    5e6e:	48 39 fe             	cmp    %rdi,%rsi
    5e71:	7d 2d                	jge    5ea0 <overlap+0x60>
    5e73:	48 39 ca             	cmp    %rcx,%rdx
    5e76:	7d 60                	jge    5ed8 <overlap+0x98>
    5e78:	4d 39 da             	cmp    %r11,%r10
    5e7b:	7d 0a                	jge    5e87 <overlap+0x47>
    return 1;
    5e7d:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e82:	4d 39 c1             	cmp    %r8,%r9
    5e85:	7c 0f                	jl     5e96 <overlap+0x56>
  return 0;
    5e87:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e89:	4d 39 c1             	cmp    %r8,%r9
    5e8c:	7f 08                	jg     5e96 <overlap+0x56>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e8e:	31 c0                	xor    %eax,%eax
    5e90:	4d 39 da             	cmp    %r11,%r10
    5e93:	0f 9e c0             	setle  %al
}
    5e96:	5d                   	pop    %rbp
    5e97:	c3                   	ret
    5e98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5ea0:	7e 56                	jle    5ef8 <overlap+0xb8>
    5ea2:	48 39 ca             	cmp    %rcx,%rdx
    5ea5:	7f 39                	jg     5ee0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ea7:	75 31                	jne    5eda <overlap+0x9a>
    5ea9:	4d 39 c1             	cmp    %r8,%r9
    5eac:	7c 2c                	jl     5eda <overlap+0x9a>
    return 1;
    5eae:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5eb3:	4d 39 da             	cmp    %r11,%r10
    5eb6:	7d de                	jge    5e96 <overlap+0x56>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5eb8:	48 39 ca             	cmp    %rcx,%rdx
}
    5ebb:	5d                   	pop    %rbp
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ebc:	0f 94 c2             	sete   %dl
    5ebf:	48 39 fe             	cmp    %rdi,%rsi
    5ec2:	0f 94 c0             	sete   %al
    5ec5:	21 c2                	and    %eax,%edx
    5ec7:	31 c0                	xor    %eax,%eax
    5ec9:	4d 39 c1             	cmp    %r8,%r9
    5ecc:	0f 94 c0             	sete   %al
    5ecf:	21 d0                	and    %edx,%eax
}
    5ed1:	c3                   	ret
    5ed2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ed8:	74 ad                	je     5e87 <overlap+0x47>
  return 0;
    5eda:	31 c0                	xor    %eax,%eax
}
    5edc:	5d                   	pop    %rbp
    5edd:	c3                   	ret
    5ede:	66 90                	xchg   %ax,%ax
  return left.tv_sec > right.tv_sec &&
    5ee0:	4d 39 da             	cmp    %r11,%r10
    5ee3:	7e c4                	jle    5ea9 <overlap+0x69>
    return 1;
    5ee5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5eea:	4d 39 c1             	cmp    %r8,%r9
    5eed:	7e ba                	jle    5ea9 <overlap+0x69>
    5eef:	eb a5                	jmp    5e96 <overlap+0x56>
    5ef1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ef8:	48 39 ca             	cmp    %rcx,%rdx
    5efb:	7c 8a                	jl     5e87 <overlap+0x47>
    5efd:	4d 39 c1             	cmp    %r8,%r9
    5f00:	7d ac                	jge    5eae <overlap+0x6e>
    5f02:	48 39 ca             	cmp    %rcx,%rdx
    5f05:	74 87                	je     5e8e <overlap+0x4e>
  return 0;
    5f07:	31 c0                	xor    %eax,%eax
    5f09:	eb d1                	jmp    5edc <overlap+0x9c>
    5f0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005f10 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5f10:	f3 0f 1e fa          	endbr64
    5f14:	55                   	push   %rbp
    5f15:	48 89 e5             	mov    %rsp,%rbp
    5f18:	41 57                	push   %r15
    5f1a:	41 56                	push   %r14
    5f1c:	41 55                	push   %r13
    5f1e:	41 54                	push   %r12
    5f20:	53                   	push   %rbx
    5f21:	48 83 ec 58          	sub    $0x58,%rsp
    5f25:	ff 15 bd 40 00 00    	call   *0x40bd(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    5f2b:	41 89 f4             	mov    %esi,%r12d
  for (int x = 0 ; x < thread_count; x++) {
    5f2e:	85 f6                	test   %esi,%esi
    5f30:	0f 8e ef 02 00 00    	jle    6225 <verify+0x315>
    5f36:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5f3a:	45 31 ff             	xor    %r15d,%r15d
    5f3d:	48 89 5d b8          	mov    %rbx,-0x48(%rbp)
    for (int z = 0 ; z < thread_count; z++) {
    5f41:	48 89 5d c0          	mov    %rbx,-0x40(%rbp)
    5f45:	45 31 ed             	xor    %r13d,%r13d
    5f48:	45 89 e6             	mov    %r12d,%r14d
      if (z != x)  {
    5f4b:	45 39 ef             	cmp    %r13d,%r15d
    5f4e:	0f 84 37 02 00 00    	je     618b <verify+0x27b>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5f54:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    5f58:	8b 50 08             	mov    0x8(%rax),%edx
    5f5b:	85 d2                	test   %edx,%edx
    5f5d:	0f 8e 28 02 00 00    	jle    618b <verify+0x27b>
    5f63:	48 c7 45 c8 00 00 00 00 	movq   $0x0,-0x38(%rbp)
    5f6b:	45 31 e4             	xor    %r12d,%r12d
    5f6e:	48 89 5d 98          	mov    %rbx,-0x68(%rbp)
    5f72:	44 89 6d 94          	mov    %r13d,-0x6c(%rbp)
    5f76:	44 89 75 90          	mov    %r14d,-0x70(%rbp)
    5f7a:	45 89 e6             	mov    %r12d,%r14d
    5f7d:	44 89 fa             	mov    %r15d,%edx
    5f80:	48 8d 35 99 12 00 00 	lea    0x1299(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    5f87:	bf 01 00 00 00       	mov    $0x1,%edi
    5f8c:	31 c0                	xor    %eax,%eax
    5f8e:	e8 ed c4 ff ff       	call   2480 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5f93:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    5f97:	8b 40 08             	mov    0x8(%rax),%eax
    5f9a:	85 c0                	test   %eax,%eax
    5f9c:	0f 8e c3 01 00 00    	jle    6165 <verify+0x255>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5fa2:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    5fa6:	44 89 75 8c          	mov    %r14d,-0x74(%rbp)
    5faa:	31 db                	xor    %ebx,%ebx
    5fac:	44 89 7d 88          	mov    %r15d,-0x78(%rbp)
    5fb0:	48 8b 00             	mov    (%rax),%rax
    5fb3:	49 89 c1             	mov    %rax,%r9
    5fb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5fc0:	4c 8b 65 c0          	mov    -0x40(%rbp),%r12
    5fc4:	48 8d 04 5b          	lea    (%rbx,%rbx,2),%rax
    5fc8:	4c 8b 7d c8          	mov    -0x38(%rbp),%r15
    5fcc:	48 8d 35 62 12 00 00 	lea    0x1262(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5fd3:	49 89 c6             	mov    %rax,%r14
    5fd6:	bf 01 00 00 00       	mov    $0x1,%edi
    5fdb:	49 8b 04 24          	mov    (%r12),%rax
    5fdf:	49 c1 e6 07          	shl    $0x7,%r14
    5fe3:	4b 8b 8c 39 d8 00 00 00 	mov    0xd8(%r9,%r15,1),%rcx
    5feb:	4c 89 75 a8          	mov    %r14,-0x58(%rbp)
    5fef:	4a 8b 94 30 d8 00 00 00 	mov    0xd8(%rax,%r14,1),%rdx
    5ff7:	31 c0                	xor    %eax,%eax
    5ff9:	e8 82 c4 ff ff       	call   2480 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5ffe:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    6002:	4c 8b 08             	mov    (%rax),%r9
    6005:	4b 83 bc 39 d8 00 00 00 00 	cmpq   $0x0,0xd8(%r9,%r15,1)
    600e:	0f 8e 38 01 00 00    	jle    614c <verify+0x23c>
    6014:	4d 03 34 24          	add    (%r12),%r14
    6018:	48 89 5d a0          	mov    %rbx,-0x60(%rbp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    601c:	ba 01 00 00 00       	mov    $0x1,%edx
    6021:	4d 89 f5             	mov    %r14,%r13
    6024:	4d 8b b5 d8 00 00 00 	mov    0xd8(%r13),%r14
    602b:	4d 85 f6             	test   %r14,%r14
    602e:	0f 8e 14 01 00 00    	jle    6148 <verify+0x238>
    6034:	0f 1f 40 00          	nopl   0x0(%rax)
    6038:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    603c:	49 89 d4             	mov    %rdx,%r12
    603f:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
    6043:	31 db                	xor    %ebx,%ebx
    6045:	49 c1 e4 05          	shl    $0x5,%r12
    6049:	49 83 ec 20          	sub    $0x20,%r12
    604d:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
    6051:	eb 32                	jmp    6085 <verify+0x175>
    6053:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6058:	4c 39 c1             	cmp    %r8,%rcx
    605b:	0f 8d 4f 01 00 00    	jge    61b0 <verify+0x2a0>
    6061:	4c 39 d7             	cmp    %r10,%rdi
    6064:	7e 05                	jle    606b <verify+0x15b>
    6066:	49 39 c3             	cmp    %rax,%r11
    6069:	7c 75                	jl     60e0 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    606b:	4c 39 d7             	cmp    %r10,%rdi
    606e:	0f 8d a3 01 00 00    	jge    6217 <verify+0x307>
    6074:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6078:	48 83 c3 01          	add    $0x1,%rbx
    607c:	49 39 de             	cmp    %rbx,%r14
    607f:	0f 8e a2 00 00 00    	jle    6127 <verify+0x217>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6085:	49 8b 8f c8 00 00 00 	mov    0xc8(%r15),%rcx
    608c:	48 89 d8             	mov    %rbx,%rax
    608f:	48 c1 e0 05          	shl    $0x5,%rax
    6093:	49 03 85 c8 00 00 00 	add    0xc8(%r13),%rax
    609a:	4c 01 e1             	add    %r12,%rcx
    609d:	48 8b 30             	mov    (%rax),%rsi
    60a0:	48 8b 78 10          	mov    0x10(%rax),%rdi
    60a4:	48 8b 11             	mov    (%rcx),%rdx
    60a7:	4c 8b 41 08          	mov    0x8(%rcx),%r8
    60ab:	4c 8b 51 10          	mov    0x10(%rcx),%r10
    60af:	4c 8b 59 18          	mov    0x18(%rcx),%r11
    60b3:	48 8b 48 08          	mov    0x8(%rax),%rcx
    60b7:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    60bb:	48 39 d6             	cmp    %rdx,%rsi
    60be:	7c 98                	jl     6058 <verify+0x148>
    60c0:	0f 8e 3a 01 00 00    	jle    6200 <verify+0x2f0>
    60c6:	4c 39 c1             	cmp    %r8,%rcx
    60c9:	0f 8f f1 00 00 00    	jg     61c0 <verify+0x2b0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    60cf:	75 a7                	jne    6078 <verify+0x168>
    60d1:	4c 39 d7             	cmp    %r10,%rdi
    60d4:	7f a2                	jg     6078 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    60d6:	49 39 c3             	cmp    %rax,%r11
    60d9:	7c 9d                	jl     6078 <verify+0x168>
    60db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    60e0:	49 89 c1             	mov    %rax,%r9
    60e3:	48 89 f9             	mov    %rdi,%rcx
    60e6:	48 8d 35 9b 13 00 00 	lea    0x139b(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    60ed:	31 c0                	xor    %eax,%eax
    60ef:	bf 01 00 00 00       	mov    $0x1,%edi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60f4:	48 83 c3 01          	add    $0x1,%rbx
    60f8:	e8 83 c3 ff ff       	call   2480 <__printf_chk@plt>
    60fd:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    6101:	4c 8b 6d a8          	mov    -0x58(%rbp),%r13
    6105:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6108:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    610c:	4d 8b b5 d8 00 00 00 	mov    0xd8(%r13),%r14
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6113:	4c 8b 08             	mov    (%rax),%r9
    6116:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    611a:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    611e:	49 39 de             	cmp    %rbx,%r14
    6121:	0f 8f 5e ff ff ff    	jg     6085 <verify+0x175>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6127:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    612b:	49 3b 97 d8 00 00 00 	cmp    0xd8(%r15),%rdx
    6132:	7d 14                	jge    6148 <verify+0x238>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6134:	4d 8b b5 d8 00 00 00 	mov    0xd8(%r13),%r14
    613b:	48 83 c2 01          	add    $0x1,%rdx
    613f:	4d 85 f6             	test   %r14,%r14
    6142:	0f 8f f0 fe ff ff    	jg     6038 <verify+0x128>
    6148:	48 8b 5d a0          	mov    -0x60(%rbp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    614c:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    6150:	48 83 c3 01          	add    $0x1,%rbx
    6154:	39 58 08             	cmp    %ebx,0x8(%rax)
    6157:	0f 8f 63 fe ff ff    	jg     5fc0 <verify+0xb0>
    615d:	44 8b 75 8c          	mov    -0x74(%rbp),%r14d
    6161:	44 8b 7d 88          	mov    -0x78(%rbp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6165:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    6169:	48 81 45 c8 80 01 00 00 	addq   $0x180,-0x38(%rbp)
    6171:	41 83 c6 01          	add    $0x1,%r14d
    6175:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    6179:	0f 8f fe fd ff ff    	jg     5f7d <verify+0x6d>
    617f:	48 8b 5d 98          	mov    -0x68(%rbp),%rbx
    6183:	44 8b 6d 94          	mov    -0x6c(%rbp),%r13d
    6187:	44 8b 75 90          	mov    -0x70(%rbp),%r14d
    for (int z = 0 ; z < thread_count; z++) {
    618b:	41 8d 45 01          	lea    0x1(%r13),%eax
    618f:	48 81 45 c0 b0 00 00 00 	addq   $0xb0,-0x40(%rbp)
    6197:	41 39 c6             	cmp    %eax,%r14d
    619a:	0f 84 96 00 00 00    	je     6236 <verify+0x326>
    61a0:	41 89 c5             	mov    %eax,%r13d
    61a3:	e9 a3 fd ff ff       	jmp    5f4b <verify+0x3b>
    61a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    61b0:	0f 85 c2 fe ff ff    	jne    6078 <verify+0x168>
    61b6:	e9 b0 fe ff ff       	jmp    606b <verify+0x15b>
    61bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    61c0:	49 39 c3             	cmp    %rax,%r11
    61c3:	7e 09                	jle    61ce <verify+0x2be>
    61c5:	4c 39 d7             	cmp    %r10,%rdi
    61c8:	0f 8c 12 ff ff ff    	jl     60e0 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    61ce:	4c 39 d7             	cmp    %r10,%rdi
    61d1:	0f 8f a1 fe ff ff    	jg     6078 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    61d7:	49 39 c3             	cmp    %rax,%r11
    61da:	0f 8d 00 ff ff ff    	jge    60e0 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    61e0:	48 39 d6             	cmp    %rdx,%rsi
    61e3:	0f 85 8f fe ff ff    	jne    6078 <verify+0x168>
    61e9:	4c 39 c1             	cmp    %r8,%rcx
    61ec:	0f 85 86 fe ff ff    	jne    6078 <verify+0x168>
    61f2:	4c 39 d7             	cmp    %r10,%rdi
    61f5:	0f 84 e5 fe ff ff    	je     60e0 <verify+0x1d0>
    61fb:	e9 78 fe ff ff       	jmp    6078 <verify+0x168>
    6200:	4c 39 c1             	cmp    %r8,%rcx
    6203:	0f 8c 62 fe ff ff    	jl     606b <verify+0x15b>
    6209:	4c 39 d7             	cmp    %r10,%rdi
    620c:	7e c9                	jle    61d7 <verify+0x2c7>
    620e:	4c 39 c1             	cmp    %r8,%rcx
    6211:	0f 85 61 fe ff ff    	jne    6078 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6217:	49 39 c3             	cmp    %rax,%r11
    621a:	0f 8f 58 fe ff ff    	jg     6078 <verify+0x168>
    6220:	e9 bb fe ff ff       	jmp    60e0 <verify+0x1d0>
}
    6225:	48 83 c4 58          	add    $0x58,%rsp
    6229:	31 c0                	xor    %eax,%eax
    622b:	5b                   	pop    %rbx
    622c:	41 5c                	pop    %r12
    622e:	41 5d                	pop    %r13
    6230:	41 5e                	pop    %r14
    6232:	41 5f                	pop    %r15
    6234:	5d                   	pop    %rbp
    6235:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
    6236:	48 81 45 b8 b0 00 00 00 	addq   $0xb0,-0x48(%rbp)
    623e:	45 89 f4             	mov    %r14d,%r12d
    6241:	41 8d 57 01          	lea    0x1(%r15),%edx
    6245:	45 39 ef             	cmp    %r13d,%r15d
    6248:	74 db                	je     6225 <verify+0x315>
    624a:	41 89 d7             	mov    %edx,%r15d
    624d:	e9 ef fc ff ff       	jmp    5f41 <verify+0x31>
    6252:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    625c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006260 <atexit>:
    6260:	f3 0f 1e fa          	endbr64
    6264:	48 8b 15 9d 3d 00 00 	mov    0x3d9d(%rip),%rdx        # a008 <__dso_handle>
    626b:	31 f6                	xor    %esi,%esi
    626d:	e9 5e c2 ff ff       	jmp    24d0 <__cxa_atexit@plt>
    6272:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    627c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006280 <__stack_chk_fail_local>:
    6280:	f3 0f 1e fa          	endbr64
    6284:	50                   	push   %rax
    6285:	58                   	pop    %rax
    6286:	48 83 ec 08          	sub    $0x8,%rsp
    628a:	e8 c1 c0 ff ff       	call   2350 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000006290 <_fini>:
    6290:	f3 0f 1e fa          	endbr64
    6294:	48 83 ec 08          	sub    $0x8,%rsp
    6298:	48 83 c4 08          	add    $0x8,%rsp
    629c:	c3                   	ret
