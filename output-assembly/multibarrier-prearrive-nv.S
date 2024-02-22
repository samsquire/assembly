
multibarrier-prearrive-nv:     file format elf64-x86-64


Disassembly of section .init:

0000000000002000 <_init>:
    2000:	f3 0f 1e fa          	endbr64
    2004:	48 83 ec 08          	sub    $0x8,%rsp
    2008:	48 8d 05 a1 15 00 00 	lea    0x15a1(%rip),%rax        # 35b0 <__gmon_start__>
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
    2641:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
    2648:	ff 15 9a 79 00 00    	call   *0x799a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    264e:	48 8d 3d 5b 4e 00 00 	lea    0x4e5b(%rip),%rdi        # 74b0 <_IO_stdin_used+0x4b0>
    2655:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    265e:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    2662:	48 8d 05 b7 10 00 00 	lea    0x10b7(%rip),%rax        # 3720 <barriered_reset>
    2669:	66 48 0f 6e e8       	movq   %rax,%xmm5
    266e:	0f 16 2d eb 75 00 00 	movhps 0x75eb(%rip),%xmm5        # 9c60 <__do_global_dtors_aux_fini_array_entry+0x8>
    2675:	0f 29 ad 60 ff ff ff 	movaps %xmm5,-0xa0(%rbp)
    267c:	e8 8f fc ff ff       	call   2310 <puts@plt>
    2681:	bf 0a 00 00 00       	mov    $0xa,%edi
    2686:	e8 65 fc ff ff       	call   22f0 <putchar@plt>
    268b:	48 8d 3d ac 4b 00 00 	lea    0x4bac(%rip),%rdi        # 723e <_IO_stdin_used+0x23e>
    2692:	e8 79 fc ff ff       	call   2310 <puts@plt>
    2697:	ba 02 00 00 00       	mov    $0x2,%edx
    269c:	48 8d 35 b7 4b 00 00 	lea    0x4bb7(%rip),%rsi        # 725a <_IO_stdin_used+0x25a>
    26a3:	31 c0                	xor    %eax,%eax
    26a5:	bf 01 00 00 00       	mov    $0x1,%edi
    26aa:	e8 d1 fd ff ff       	call   2480 <__printf_chk@plt>
    26af:	ba 06 00 00 00       	mov    $0x6,%edx
    26b4:	48 8d 35 b9 4b 00 00 	lea    0x4bb9(%rip),%rsi        # 7274 <_IO_stdin_used+0x274>
    26bb:	31 c0                	xor    %eax,%eax
    26bd:	bf 01 00 00 00       	mov    $0x1,%edi
    26c2:	e8 b9 fd ff ff       	call   2480 <__printf_chk@plt>
    26c7:	ba 01 00 00 00       	mov    $0x1,%edx
    26cc:	48 8d 35 b5 4b 00 00 	lea    0x4bb5(%rip),%rsi        # 7288 <_IO_stdin_used+0x288>
    26d3:	31 c0                	xor    %eax,%eax
    26d5:	bf 01 00 00 00       	mov    $0x1,%edi
    26da:	e8 a1 fd ff ff       	call   2480 <__printf_chk@plt>
    26df:	ba 01 00 00 00       	mov    $0x1,%edx
    26e4:	48 8d 35 ae 4b 00 00 	lea    0x4bae(%rip),%rsi        # 7299 <_IO_stdin_used+0x299>
    26eb:	31 c0                	xor    %eax,%eax
    26ed:	bf 01 00 00 00       	mov    $0x1,%edi
    26f2:	e8 89 fd ff ff       	call   2480 <__printf_chk@plt>
    26f7:	ba 02 00 00 00       	mov    $0x2,%edx
    26fc:	48 8d 35 ae 4b 00 00 	lea    0x4bae(%rip),%rsi        # 72b1 <_IO_stdin_used+0x2b1>
    2703:	31 c0                	xor    %eax,%eax
    2705:	bf 01 00 00 00       	mov    $0x1,%edi
    270a:	e8 71 fd ff ff       	call   2480 <__printf_chk@plt>
    270f:	ba 01 00 00 00       	mov    $0x1,%edx
    2714:	48 8d 35 fd 4d 00 00 	lea    0x4dfd(%rip),%rsi        # 7518 <_IO_stdin_used+0x518>
    271b:	31 c0                	xor    %eax,%eax
    271d:	bf 01 00 00 00       	mov    $0x1,%edi
    2722:	e8 59 fd ff ff       	call   2480 <__printf_chk@plt>
    2727:	ba 01 00 00 00       	mov    $0x1,%edx
    272c:	48 8d 35 15 4e 00 00 	lea    0x4e15(%rip),%rsi        # 7548 <_IO_stdin_used+0x548>
    2733:	31 c0                	xor    %eax,%eax
    2735:	bf 01 00 00 00       	mov    $0x1,%edi
    273a:	e8 41 fd ff ff       	call   2480 <__printf_chk@plt>
    273f:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2744:	48 8d 35 82 4b 00 00 	lea    0x4b82(%rip),%rsi        # 72cd <_IO_stdin_used+0x2cd>
    274b:	31 c0                	xor    %eax,%eax
    274d:	bf 01 00 00 00       	mov    $0x1,%edi
    2752:	e8 29 fd ff ff       	call   2480 <__printf_chk@plt>
    2757:	ba 05 00 00 00       	mov    $0x5,%edx
    275c:	48 8d 35 84 4b 00 00 	lea    0x4b84(%rip),%rsi        # 72e7 <_IO_stdin_used+0x2e7>
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
    2780:	bf 02 00 00 00       	mov    $0x2,%edi
    2785:	e8 36 fc ff ff       	call   23c0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    278a:	be b0 00 00 00       	mov    $0xb0,%esi
    278f:	bf 06 00 00 00       	mov    $0x6,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    2794:	48 89 85 70 ff ff ff 	mov    %rax,-0x90(%rbp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    279b:	e8 20 fc ff ff       	call   23c0 <calloc@plt>
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  int buffers_required = thread_count * barrier_count;
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    27a0:	be 10 00 00 00       	mov    $0x10,%esi
    27a5:	bf 04 00 00 00       	mov    $0x4,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27aa:	48 89 45 90          	mov    %rax,-0x70(%rbp)
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    27ae:	e8 0d fc ff ff       	call   23c0 <calloc@plt>
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    27b3:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)
    27ba:	48 8d 58 40          	lea    0x40(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    27be:	49 89 c5             	mov    %rax,%r13
    27c1:	49 89 c6             	mov    %rax,%r14
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27c4:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    27c9:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27d1:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    27d6:	49 83 c5 10          	add    $0x10,%r13
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27da:	e8 e1 fb ff ff       	call   23c0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    27df:	be 20 00 00 00       	mov    $0x20,%esi
    27e4:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27e9:	49 89 45 f8          	mov    %rax,-0x8(%r13)
    27ed:	49 89 c4             	mov    %rax,%r12
      buffers[x].buffer[y].available = 0;
    27f0:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    27fa:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2804:	e8 b7 fb ff ff       	call   23c0 <calloc@plt>
    2809:	49 89 84 24 88 00 00 00 	mov    %rax,0x88(%r12)
  for (int x = 0 ; x < buffers_required; x++) {
    2811:	4c 39 eb             	cmp    %r13,%rbx
    2814:	75 ae                	jne    27c4 <main+0x194>
    2816:	4c 89 f0             	mov    %r14,%rax
    2819:	4c 8b 75 90          	mov    -0x70(%rbp),%r14
    281d:	48 8b bd 70 ff ff ff 	mov    -0x90(%rbp),%rdi
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
    2824:	c7 45 98 00 00 00 00 	movl   $0x0,-0x68(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    282b:	48 89 45 88          	mov    %rax,-0x78(%rbp)
  int curcpu = 0;
    282f:	c7 85 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rbp)
    2839:	4c 8d 7f e8          	lea    -0x18(%rdi),%r15
        thread_data[x].tasks[y].snapshot_count = 99;
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
        thread_data[x].tasks[y].current_snapshot = 0;
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
        thread_data[x].tasks[y].thread = &thread_data[x]; 
        thread_data[x].tasks[y].available = 1;
    283d:	4d 89 fc             	mov    %r15,%r12
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2840:	be 08 00 00 00       	mov    $0x8,%esi
    2845:	bf 02 00 00 00       	mov    $0x2,%edi
    284a:	e8 71 fb ff ff       	call   23c0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    284f:	be 80 00 00 00       	mov    $0x80,%esi
    2854:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2859:	48 89 c3             	mov    %rax,%rbx
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    285c:	e8 5f fb ff ff       	call   23c0 <calloc@plt>
    if (x % 2 == 1) {
    2861:	8b 75 98             	mov    -0x68(%rbp),%esi
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2864:	49 89 c5             	mov    %rax,%r13
    if (x % 2 == 1) {
    2867:	89 f0                	mov    %esi,%eax
    2869:	89 75 b0             	mov    %esi,-0x50(%rbp)
    286c:	89 f7                	mov    %esi,%edi
      other = (x + 1) % total_threads;
    286e:	83 c6 01             	add    $0x1,%esi
    if (x % 2 == 1) {
    2871:	83 e0 01             	and    $0x1,%eax
      other = (x + 1) % total_threads;
    2874:	89 75 98             	mov    %esi,-0x68(%rbp)
    if (x % 2 == 1) {
    2877:	85 c0                	test   %eax,%eax
    2879:	0f 84 8a 07 00 00    	je     3009 <main+0x9d9>
      my_thread_data[0] = &thread_data[other]; 
    287f:	49 8d 8e 50 ff ff ff 	lea    -0xb0(%r14),%rcx
      my_thread_data[1] = &thread_data[x]; 
    2886:	4c 89 73 08          	mov    %r14,0x8(%rbx)
    288a:	89 fa                	mov    %edi,%edx
    288c:	4d 89 f0             	mov    %r14,%r8
      my_thread_data[0] = &thread_data[other]; 
    288f:	48 89 0b             	mov    %rcx,(%rbx)
      other = abs(x - 1) % total_threads;
    2892:	44 8d 7f ff          	lea    -0x1(%rdi),%r15d
    2896:	48 8d 35 5e 4a 00 00 	lea    0x4a5e(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
    289d:	31 c0                	xor    %eax,%eax
      thread_data[x].thread_index = 1;
    289f:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
    28a6:	bf 01 00 00 00       	mov    $0x1,%edi
    28ab:	e8 d0 fb ff ff       	call   2480 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    28b0:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    28b5:	48 89 45 80          	mov    %rax,-0x80(%rbp)
    28b9:	4d 89 66 38          	mov    %r12,0x38(%r14)
    28bd:	44 8b 65 b0          	mov    -0x50(%rbp),%r12d
    28c1:	44 89 f9             	mov    %r15d,%ecx
    28c4:	bf 01 00 00 00       	mov    $0x1,%edi
    28c9:	45 8b 06             	mov    (%r14),%r8d
    28cc:	48 8d 35 9d 4c 00 00 	lea    0x4c9d(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    28d3:	31 c0                	xor    %eax,%eax
    28d5:	44 89 e2             	mov    %r12d,%edx
    28d8:	e8 a3 fb ff ff       	call   2480 <__printf_chk@plt>
    28dd:	8b 8d 78 ff ff ff    	mov    -0x88(%rbp),%ecx
    28e3:	31 c0                	xor    %eax,%eax
    28e5:	44 89 e2             	mov    %r12d,%edx
    thread_data[x].other = other;
    28e8:	45 89 be a8 00 00 00 	mov    %r15d,0xa8(%r14)
    28ef:	48 8d 35 aa 4c 00 00 	lea    0x4caa(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    28f6:	bf 01 00 00 00       	mov    $0x1,%edi
    28fb:	e8 80 fb ff ff       	call   2480 <__printf_chk@plt>
      if (x < thread_count) {
    2900:	41 83 fc 01          	cmp    $0x1,%r12d
    2904:	0f 86 6b 07 00 00    	jbe    3075 <main+0xa45>
          CPU_SET(j, sendercpu);
    290a:	49 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%r13)
    thread_data[x].real_thread_index = x;
    2912:	8b 45 b0             	mov    -0x50(%rbp),%eax
    thread_data[x].threads = my_thread_data;
    2915:	49 89 5e 10          	mov    %rbx,0x10(%r14)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2919:	be 10 00 00 00       	mov    $0x10,%esi
      for (int y = 0 ; y < total_barrier_count ; y++) {
    291e:	45 31 e4             	xor    %r12d,%r12d
    thread_data[x].cpu_set = sendercpu;
    2921:	4d 89 ae a0 00 00 00 	mov    %r13,0xa0(%r14)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2928:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].real_thread_index = x;
    292d:	41 89 46 04          	mov    %eax,0x4(%r14)
    thread_data[x].thread_count = 2;
    2931:	48 8b 05 48 51 00 00 	mov    0x5148(%rip),%rax        # 7a80 <_IO_stdin_used+0xa80>
    thread_data[x].task_count = total_barrier_count;
    2938:	41 c7 46 30 03 00 00 00 	movl   $0x3,0x30(%r14)
    thread_data[x].thread_count = 2;
    2940:	49 89 46 18          	mov    %rax,0x18(%r14)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2944:	e8 77 fa ff ff       	call   23c0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2949:	be 10 00 00 00       	mov    $0x10,%esi
    294e:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2953:	49 89 46 58          	mov    %rax,0x58(%r14)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2957:	e8 64 fa ff ff       	call   23c0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    295c:	be 28 00 00 00       	mov    $0x28,%esi
    2961:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    2966:	66 0f 6f 1d f2 50 00 00 	movdqa 0x50f2(%rip),%xmm3        # 7a60 <_IO_stdin_used+0xa60>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    296e:	49 89 46 60          	mov    %rax,0x60(%r14)
    thread_data[x].timestamp_count = 0;
    2972:	41 0f 11 5e 70       	movups %xmm3,0x70(%r14)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2977:	e8 44 fa ff ff       	call   23c0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    297c:	be 00 02 00 00       	mov    $0x200,%esi
    2981:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
    2986:	66 0f 6f 25 d2 50 00 00 	movdqa 0x50d2(%rip),%xmm4        # 7a60 <_IO_stdin_used+0xa60>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    298e:	49 89 86 80 00 00 00 	mov    %rax,0x80(%r14)
    thread_data[x].task_timestamp_count = 0;
    2995:	41 0f 11 a6 88 00 00 00 	movups %xmm4,0x88(%r14)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    299d:	e8 1e fa ff ff       	call   23c0 <calloc@plt>
      thread_data[x].tasks = barriers;
    29a2:	49 89 46 28          	mov    %rax,0x28(%r14)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    29a6:	49 89 c5             	mov    %rax,%r13
        thread_data[x].tasks[y].protected = do_protected_write; 
    29a9:	4d 63 fc             	movslq %r12d,%r15
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    29ac:	be 20 00 00 00       	mov    $0x20,%esi
    29b1:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    29b6:	4c 89 fb             	mov    %r15,%rbx
    29b9:	48 8d 05 10 0d 00 00 	lea    0xd10(%rip),%rax        # 36d0 <do_protected_write>
    29c0:	48 c1 e3 09          	shl    $0x9,%rbx
    29c4:	49 01 dd             	add    %rbx,%r13
    29c7:	49 89 85 20 01 00 00 	mov    %rax,0x120(%r13)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    29ce:	e8 ed f9 ff ff       	call   23c0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    29d3:	48 89 5d a8          	mov    %rbx,-0x58(%rbp)
    29d7:	49 89 85 68 01 00 00 	mov    %rax,0x168(%r13)
        for (int b = 0 ; b < 2 ; b++) {
    29de:	49 89 c5             	mov    %rax,%r13
    29e1:	48 8d 40 40          	lea    0x40(%rax),%rax
    29e5:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    29e9:	44 89 65 a0          	mov    %r12d,-0x60(%rbp)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29ed:	be 08 00 00 00       	mov    $0x8,%esi
    29f2:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    29f7:	49 83 c5 20          	add    $0x20,%r13
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29fb:	e8 c0 f9 ff ff       	call   23c0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2a00:	be 08 00 00 00       	mov    $0x8,%esi
    2a05:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2a0a:	49 89 c4             	mov    %rax,%r12
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2a0d:	e8 ae f9 ff ff       	call   23c0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    2a12:	be 18 00 00 00       	mov    $0x18,%esi
    2a17:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2a1c:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    2a1f:	e8 9c f9 ff ff       	call   23c0 <calloc@plt>
          data[0].messages_count = 0;
    2a24:	66 0f 6f 05 44 50 00 00 	movdqa 0x5044(%rip),%xmm0        # 7a70 <_IO_stdin_used+0xa70>
          mailboxes[b].higher = &data[1];
    2a2c:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    2a30:	49 89 45 e0          	mov    %rax,-0x20(%r13)
          mailboxes[b].higher = &data[1];
    2a34:	49 89 75 e8          	mov    %rsi,-0x18(%r13)
          data[0].messages = messages;
    2a38:	4c 89 20             	mov    %r12,(%rax)
          data[1].messages = messages2;
    2a3b:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    2a3f:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    2a43:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    2a47:	4c 39 6d b8          	cmp    %r13,-0x48(%rbp)
    2a4b:	75 a0                	jne    29ed <main+0x3bd>
        char *message = malloc(sizeof(char) * 256);
    2a4d:	be 01 00 00 00       	mov    $0x1,%esi
    2a52:	bf 00 01 00 00       	mov    $0x100,%edi
    2a57:	44 8b 65 a0          	mov    -0x60(%rbp),%r12d
    2a5b:	48 8b 5d a8          	mov    -0x58(%rbp),%rbx
    2a5f:	e8 5c f9 ff ff       	call   23c0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a64:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a69:	49 89 c5             	mov    %rax,%r13
        struct Message *messaged = malloc(sizeof(struct Message));
    2a6c:	e8 cf f9 ff ff       	call   2440 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a71:	44 8b 45 b0          	mov    -0x50(%rbp),%r8d
    2a75:	4c 89 ef             	mov    %r13,%rdi
    2a78:	45 89 e1             	mov    %r12d,%r9d
    2a7b:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    2a7f:	48 8d 0d 3a 4b 00 00 	lea    0x4b3a(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a86:	ba 00 01 00 00       	mov    $0x100,%edx
    2a8b:	31 c0                	xor    %eax,%eax
    2a8d:	be 01 00 00 00       	mov    $0x1,%esi
    2a92:	e8 c9 fa ff ff       	call   2560 <__sprintf_chk@plt>
        messaged->message = message;
    2a97:	4c 8b 55 b8          	mov    -0x48(%rbp),%r10
        messaged->thread_index = thread_data[x].thread_index;
    2a9b:	49 63 06             	movslq (%r14),%rax
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a9e:	bf 63 00 00 00       	mov    $0x63,%edi
    2aa3:	be 20 00 00 00       	mov    $0x20,%esi
        messaged->message = message;
    2aa8:	4d 89 2a             	mov    %r13,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2aab:	4d 8b 6e 28          	mov    0x28(%r14),%r13
        messaged->task_index = y;
    2aaf:	4d 89 7a 10          	mov    %r15,0x10(%r10)
        messaged->thread_index = thread_data[x].thread_index;
    2ab3:	49 89 c7             	mov    %rax,%r15
    2ab6:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2aba:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    2abf:	4c 01 eb             	add    %r13,%rbx
    2ac2:	83 e0 01             	and    $0x1,%eax
        thread_data[x].tasks[y].message = messaged;
    2ac5:	4c 89 93 80 01 00 00 	mov    %r10,0x180(%rbx)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2acc:	89 83 88 01 00 00    	mov    %eax,0x188(%rbx)
        thread_data[x].tasks[y].snapshot_count = 99;
    2ad2:	48 c7 83 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%rbx)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2add:	e8 de f8 ff ff       	call   23c0 <calloc@plt>
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2ae2:	44 89 bb 30 01 00 00 	mov    %r15d,0x130(%rbx)
        thread_data[x].tasks[y].sending = 1;
    2ae9:	48 bf 01 00 00 00 02 00 00 00 	movabs $0x200000001,%rdi
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2af3:	48 89 83 48 01 00 00 	mov    %rax,0x148(%rbx)
        thread_data[x].tasks[y].available = 1;
    2afa:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2b04:	48 c7 83 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%rbx)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2b0f:	4c 89 b3 28 01 00 00 	mov    %r14,0x128(%rbx)
        thread_data[x].tasks[y].arrived = 0;
    2b16:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
        thread_data[x].tasks[y].thread_count = 2;
    2b20:	c7 83 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%rbx)
        thread_data[x].tasks[y].available = 1;
    2b2a:	48 89 83 38 01 00 00 	mov    %rax,0x138(%rbx)
        thread_data[x].tasks[y].sending = 1;
    2b31:	48 89 bb 78 01 00 00 	mov    %rdi,0x178(%rbx)
        thread_data[x].tasks[y].task_count = total_barrier_count;
        thread_data[x].tasks[y].worker_count = thread_count;
        thread_data[x].tasks[y].task_index = y;
    2b38:	44 89 23             	mov    %r12d,(%rbx)
        if (y == barrier_count - 1) {
    2b3b:	41 83 fc 01          	cmp    $0x1,%r12d
    2b3f:	0f 84 b5 04 00 00    	je     2ffa <main+0x9ca>
            thread_data[x].tasks[y].run = barriered_nulltask; 
          }
          */
          thread_data[x].tasks[y].run = barriered_work; 
        } else {
          if (y == 0) {
    2b45:	45 85 e4             	test   %r12d,%r12d
    2b48:	0f 84 93 04 00 00    	je     2fe1 <main+0x9b1>
            // printf("Thread %d is an ingest thread\n", x);
            thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
            assigned = 1;
           } else {
             thread_data[x].tasks[y].run = barriered_work; 
    2b4e:	48 8d 3d db 2c 00 00 	lea    0x2cdb(%rip),%rdi        # 5830 <barriered_work>
           }
        }
      }
			thread_data[x].buffers_count = buffers_per_thread;
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2b55:	be 08 00 00 00       	mov    $0x8,%esi
             thread_data[x].tasks[y].run = barriered_work; 
    2b5a:	48 89 bb 18 01 00 00 	mov    %rdi,0x118(%rbx)
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2b61:	bf 01 00 00 00       	mov    $0x1,%edi
			thread_data[x].buffers_count = buffers_per_thread;
    2b66:	41 c7 86 ac 00 00 00 01 00 00 00 	movl   $0x1,0xac(%r14)
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2b71:	e8 4a f8 ff ff       	call   23c0 <calloc@plt>
      for (int b = 0 ; b < buffers_per_thread; b++) {	
        thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2b76:	48 8b 7d 88          	mov    -0x78(%rbp),%rdi
  for (int x = 0 ; x < total_threads ; x++) {
    2b7a:	4c 8b 65 80          	mov    -0x80(%rbp),%r12
      }
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b7e:	66 0f 6f 95 60 ff ff ff 	movdqa -0xa0(%rbp),%xmm2
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2b86:	49 89 46 40          	mov    %rax,0x40(%r14)
        thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2b8a:	48 89 38             	mov    %rdi,(%rax)
  for (int x = 0 ; x < total_threads ; x++) {
    2b8d:	48 83 c7 10          	add    $0x10,%rdi
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
    2b91:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2b9b:	4d 89 b5 28 05 00 00 	mov    %r14,0x528(%r13)
  for (int x = 0 ; x < total_threads ; x++) {
    2ba2:	49 81 c6 b0 00 00 00 	add    $0xb0,%r14
    2ba9:	83 7d 98 06          	cmpl   $0x6,-0x68(%rbp)
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2bad:	41 c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r13)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2bb8:	41 c7 85 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%r13)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bc3:	45 89 bd 30 05 00 00 	mov    %r15d,0x530(%r13)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2bca:	41 c7 85 7c 05 00 00 02 00 00 00 	movl   $0x2,0x57c(%r13)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2bd5:	41 c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r13)
      thread_data[x].tasks[barrier_count].available = 1; 
    2be0:	49 89 85 38 05 00 00 	mov    %rax,0x538(%r13)
  for (int x = 0 ; x < total_threads ; x++) {
    2be7:	48 89 7d 88          	mov    %rdi,-0x78(%rbp)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2beb:	41 0f 11 95 18 05 00 00 	movups %xmm2,0x518(%r13)
  for (int x = 0 ; x < total_threads ; x++) {
    2bf3:	0f 85 47 fc ff ff    	jne    2840 <main+0x210>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2bf9:	ba 03 00 00 00       	mov    $0x3,%edx
    2bfe:	48 8d 35 13 47 00 00 	lea    0x4713(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2c05:	bf 01 00 00 00       	mov    $0x1,%edi
    2c0a:	31 c0                	xor    %eax,%eax
    2c0c:	e8 6f f8 ff ff       	call   2480 <__printf_chk@plt>
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c11:	be 08 00 00 00       	mov    $0x8,%esi
    2c16:	bf 02 00 00 00       	mov    $0x2,%edi
    2c1b:	e8 a0 f7 ff ff       	call   23c0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2c20:	48 8b 7d 90          	mov    -0x70(%rbp),%rdi
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c24:	be 38 00 00 00       	mov    $0x38,%esi
    my_thread_data[0] = &thread_data[x]; 
    2c29:	4c 8d a7 10 02 00 00 	lea    0x210(%rdi),%r12
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c30:	48 89 78 08          	mov    %rdi,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c34:	4c 8d af b0 00 00 00 	lea    0xb0(%rdi),%r13
    thread_data[x].threads = my_thread_data;
    2c3b:	48 89 87 20 02 00 00 	mov    %rax,0x220(%rdi)
    my_thread_data[0] = &thread_data[x]; 
    2c42:	4c 89 20             	mov    %r12,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c45:	48 8b 47 28          	mov    0x28(%rdi),%rax
    thread_data[x].thread_count = 2;
    2c49:	c7 87 28 02 00 00 02 00 00 00 	movl   $0x2,0x228(%rdi)
    thread_data[x].thread_index = 0;
    2c53:	c7 87 10 02 00 00 00 00 00 00 	movl   $0x0,0x210(%rdi)
    thread_data[x].task_count = total_barrier_count;
    2c5d:	c7 87 40 02 00 00 03 00 00 00 	movl   $0x3,0x240(%rdi)
    thread_data[n].tasks[0].scheduled = 1;
    2c67:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2c71:	48 8b 87 d8 00 00 00 	mov    0xd8(%rdi),%rax
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c78:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[n].tasks[0].scheduled = 1;
    2c7d:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c87:	e8 34 f7 ff ff       	call   23c0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c8c:	be 38 00 00 00       	mov    $0x38,%esi
    2c91:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c96:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c99:	e8 22 f7 ff ff       	call   23c0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c9e:	be 38 00 00 00       	mov    $0x38,%esi
    2ca3:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ca8:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cab:	e8 10 f7 ff ff       	call   23c0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cb0:	be 38 00 00 00       	mov    $0x38,%esi
    2cb5:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cba:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cbe:	e8 fd f6 ff ff       	call   23c0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2cc3:	be 08 00 00 00       	mov    $0x8,%esi
    2cc8:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ccd:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2cd1:	e8 ea f6 ff ff       	call   23c0 <calloc@plt>

  thread_data[thread_count].type = TIMER;
    2cd6:	48 8b 7d 90          	mov    -0x70(%rbp),%rdi
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2cda:	be 08 00 00 00       	mov    $0x8,%esi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2cdf:	48 89 c3             	mov    %rax,%rbx
  thread_data[thread_count].task_count = total_barrier_count;
    2ce2:	48 8b 05 9f 4d 00 00 	mov    0x4d9f(%rip),%rax        # 7a88 <_IO_stdin_used+0xa88>
  thread_data[thread_count].type = TIMER;
    2ce9:	c7 87 68 01 00 00 00 00 00 00 	movl   $0x0,0x168(%rdi)
  thread_data[thread_count].task_count = total_barrier_count;
    2cf3:	48 89 87 90 01 00 00 	mov    %rax,0x190(%rdi)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2cfa:	bf 06 00 00 00       	mov    $0x6,%edi
    2cff:	e8 bc f6 ff ff       	call   23c0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2d04:	48 8b 7d 90          	mov    -0x70(%rbp),%rdi
    2d08:	48 8d 35 18 46 00 00 	lea    0x4618(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2d0f:	4c 89 60 18          	mov    %r12,0x18(%rax)
    2d13:	4c 8d 87 c0 02 00 00 	lea    0x2c0(%rdi),%r8
    2d1a:	48 8d 8f 60 01 00 00 	lea    0x160(%rdi),%rcx
    2d21:	48 89 38             	mov    %rdi,(%rax)
    2d24:	48 8d 97 70 03 00 00 	lea    0x370(%rdi),%rdx
    2d2b:	4c 89 40 20          	mov    %r8,0x20(%rax)
    2d2f:	48 89 48 10          	mov    %rcx,0x10(%rax)
    2d33:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2d37:	ba 02 00 00 00       	mov    $0x2,%edx
  }
  thread_data[thread_count].threads = my_thread_data;
    2d3c:	48 89 87 70 01 00 00 	mov    %rax,0x170(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    2d43:	4c 89 68 08          	mov    %r13,0x8(%rax)
    2d47:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2d49:	c7 87 78 01 00 00 02 00 00 00 	movl   $0x2,0x178(%rdi)
  thread_data[thread_count].my_thread_count = 2;
    2d53:	c7 87 80 01 00 00 02 00 00 00 	movl   $0x2,0x180(%rdi)
  thread_data[thread_count].thread_index = 0;
    2d5d:	c7 87 60 01 00 00 00 00 00 00 	movl   $0x0,0x160(%rdi)
    2d67:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    2d6c:	4c 89 45 a8          	mov    %r8,-0x58(%rbp)
    2d70:	48 89 4d a0          	mov    %rcx,-0x60(%rbp)
    2d74:	e8 07 f7 ff ff       	call   2480 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2d79:	48 8b 4d a0          	mov    -0x60(%rbp),%rcx
    2d7d:	49 8d 76 70          	lea    0x70(%r14),%rsi
    2d81:	48 8d 7b 10          	lea    0x10(%rbx),%rdi
    2d85:	48 8d 15 24 0b 00 00 	lea    0xb24(%rip),%rdx        # 38b0 <timer_thread>
    2d8c:	e8 0f f7 ff ff       	call   24a0 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    thread_data[x].type = WORKER;
    2d91:	4c 8b 75 90          	mov    -0x70(%rbp),%r14
    2d95:	31 d2                	xor    %edx,%edx
    2d97:	bf 01 00 00 00       	mov    $0x1,%edi
    2d9c:	4c 8d 0d 45 48 00 00 	lea    0x4845(%rip),%r9        # 75e8 <_IO_stdin_used+0x5e8>
    2da3:	31 c0                	xor    %eax,%eax
    2da5:	41 c7 46 08 01 00 00 00 	movl   $0x1,0x8(%r14)
    2dad:	4c 89 ce             	mov    %r9,%rsi
    thread_data[x].running = 1;
    2db0:	41 c7 46 34 01 00 00 00 	movl   $0x1,0x34(%r14)
    2db8:	e8 c3 f6 ff ff       	call   2480 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2dbd:	4c 89 f1             	mov    %r14,%rcx
    2dc0:	4c 89 75 90          	mov    %r14,-0x70(%rbp)
    2dc4:	4c 89 fe             	mov    %r15,%rsi
    2dc7:	4c 8d 35 62 26 00 00 	lea    0x2662(%rip),%r14        # 5430 <barriered_thread>
    2dce:	48 89 df             	mov    %rbx,%rdi
    2dd1:	4c 89 f2             	mov    %r14,%rdx
    2dd4:	e8 c7 f6 ff ff       	call   24a0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2dd9:	48 8b 7d 90          	mov    -0x70(%rbp),%rdi
    2ddd:	be 08 00 00 00       	mov    $0x8,%esi
    2de2:	48 8b 97 a0 00 00 00 	mov    0xa0(%rdi),%rdx
    2de9:	48 8b 3b             	mov    (%rbx),%rdi
    2dec:	e8 0f f5 ff ff       	call   2300 <pthread_setaffinity_np@plt>
    thread_data[x].type = WORKER;
    2df1:	48 8b 7d 90          	mov    -0x70(%rbp),%rdi
    2df5:	ba 01 00 00 00       	mov    $0x1,%edx
    2dfa:	31 c0                	xor    %eax,%eax
    2dfc:	4c 8d 0d e5 47 00 00 	lea    0x47e5(%rip),%r9        # 75e8 <_IO_stdin_used+0x5e8>
    2e03:	c7 87 b8 00 00 00 01 00 00 00 	movl   $0x1,0xb8(%rdi)
    2e0d:	4c 89 ce             	mov    %r9,%rsi
    thread_data[x].running = 1;
    2e10:	c7 87 e4 00 00 00 01 00 00 00 	movl   $0x1,0xe4(%rdi)
    2e1a:	bf 01 00 00 00       	mov    $0x1,%edi
    2e1f:	e8 5c f6 ff ff       	call   2480 <__printf_chk@plt>
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2e24:	4c 89 e9             	mov    %r13,%rcx
    2e27:	49 8d 77 38          	lea    0x38(%r15),%rsi
    2e2b:	4c 89 f2             	mov    %r14,%rdx
    2e2e:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    2e32:	4c 8d 73 20          	lea    0x20(%rbx),%r14
    2e36:	e8 65 f6 ff ff       	call   24a0 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2e3b:	4c 8b 7d 90          	mov    -0x70(%rbp),%r15
    2e3f:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    2e43:	be 08 00 00 00       	mov    $0x8,%esi
    2e48:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    2e4f:	e8 ac f4 ff ff       	call   2300 <pthread_setaffinity_np@plt>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2e54:	48 8b 3d 35 4c 00 00 	mov    0x4c35(%rip),%rdi        # 7a90 <_IO_stdin_used+0xa90>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e5b:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    2e60:	41 c7 87 18 02 00 00 02 00 00 00 	movl   $0x2,0x218(%r15)
    thread_data[x].task_count = 0;
    2e6b:	49 89 bf 40 02 00 00 	mov    %rdi,0x240(%r15)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e72:	bf 01 00 00 00       	mov    $0x1,%edi
    2e77:	e8 44 f5 ff ff       	call   23c0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e7c:	be 00 08 00 00       	mov    $0x800,%esi
    2e81:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e83:	49 89 87 58 02 00 00 	mov    %rax,0x258(%r15)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e8a:	e8 61 f6 ff ff       	call   24f0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2e8f:	be 08 00 00 00       	mov    $0x8,%esi
    2e94:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e99:	41 89 87 60 02 00 00 	mov    %eax,0x260(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2ea0:	e8 1b f5 ff ff       	call   23c0 <calloc@plt>
    2ea5:	ba 03 00 00 00       	mov    $0x3,%edx
    2eaa:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    2eaf:	41 c7 87 28 02 00 00 02 00 00 00 	movl   $0x2,0x228(%r15)
      my_thread_data[n] = &thread_data[n]; 
    2eba:	4c 89 38             	mov    %r15,(%rax)
    2ebd:	48 8d 35 81 44 00 00 	lea    0x4481(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    thread_data[x].threads = my_thread_data;
    2ec4:	49 89 87 20 02 00 00 	mov    %rax,0x220(%r15)
      my_thread_data[n] = &thread_data[n]; 
    2ecb:	4c 89 68 08          	mov    %r13,0x8(%rax)
    2ecf:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    2ed1:	41 c7 87 10 02 00 00 03 00 00 00 	movl   $0x3,0x210(%r15)
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2edc:	41 bf 04 00 00 00    	mov    $0x4,%r15d
    2ee2:	e8 99 f5 ff ff       	call   2480 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2ee7:	48 8b 75 b8          	mov    -0x48(%rbp),%rsi
    2eeb:	4c 89 e1             	mov    %r12,%rcx
    2eee:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    2ef2:	48 8d 15 e7 1c 00 00 	lea    0x1ce7(%rip),%rdx        # 4be0 <io_thread>
    2ef9:	48 81 c6 a8 00 00 00 	add    $0xa8,%rsi
    2f00:	e8 9b f5 ff ff       	call   24a0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2f05:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
    2f09:	4c 8b 65 a8          	mov    -0x58(%rbp),%r12
    2f0d:	48 05 e0 00 00 00    	add    $0xe0,%rax
    2f13:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    2f17:	44 89 fa             	mov    %r15d,%edx
    2f1a:	48 8d 35 3b 44 00 00 	lea    0x443b(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    2f21:	bf 01 00 00 00       	mov    $0x1,%edi
    2f26:	31 c0                	xor    %eax,%eax
    2f28:	e8 53 f5 ff ff       	call   2480 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    2f2d:	be 08 00 00 00       	mov    $0x8,%esi
    2f32:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    2f37:	48 8b 05 52 4b 00 00 	mov    0x4b52(%rip),%rax        # 7a90 <_IO_stdin_used+0xa90>
    thread_data[x].type = EXTERNAL;
    2f3e:	41 c7 44 24 08 03 00 00 00 	movl   $0x3,0x8(%r12)
    thread_data[x].task_count = 0;
    2f47:	49 89 44 24 30       	mov    %rax,0x30(%r12)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    2f4c:	e8 6f f4 ff ff       	call   23c0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    2f51:	48 8b bd 58 ff ff ff 	mov    -0xa8(%rbp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f58:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    2f5d:	41 c7 84 24 ac 00 00 00 01 00 00 00 	movl   $0x1,0xac(%r12)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    2f69:	49 89 44 24 40       	mov    %rax,0x40(%r12)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    2f6e:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f71:	bf 02 00 00 00       	mov    $0x2,%edi
    2f76:	e8 45 f4 ff ff       	call   23c0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    2f7b:	48 8b 75 90          	mov    -0x70(%rbp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    2f7f:	45 89 3c 24          	mov    %r15d,(%r12)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f83:	4c 89 e1             	mov    %r12,%rcx
    thread_data[x].threads = my_thread_data;
    2f86:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f8b:	4c 89 f7             	mov    %r14,%rdi
    2f8e:	48 8d 15 fb 07 00 00 	lea    0x7fb(%rip),%rdx        # 3790 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2f95:	49 81 c4 b0 00 00 00 	add    $0xb0,%r12
      my_thread_data[n] = &thread_data[n]; 
    2f9c:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f9f:	48 8b 75 b8          	mov    -0x48(%rbp),%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2fa3:	49 83 c6 08          	add    $0x8,%r14
      my_thread_data[n] = &thread_data[n]; 
    2fa7:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    2fab:	48 8b 05 ce 4a 00 00 	mov    0x4ace(%rip),%rax        # 7a80 <_IO_stdin_used+0xa80>
    2fb2:	49 89 84 24 68 ff ff ff 	mov    %rax,-0x98(%r12)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2fba:	e8 e1 f4 ff ff       	call   24a0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2fbf:	48 83 85 58 ff ff ff 10 	addq   $0x10,-0xa8(%rbp)
    2fc7:	48 83 45 b8 38       	addq   $0x38,-0x48(%rbp)
    2fcc:	41 83 ff 04          	cmp    $0x4,%r15d
    2fd0:	0f 85 d0 00 00 00    	jne    30a6 <main+0xa76>
    2fd6:	41 bf 05 00 00 00    	mov    $0x5,%r15d
    2fdc:	e9 36 ff ff ff       	jmp    2f17 <main+0x8e7>
    2fe1:	48 8d 05 78 2d 00 00 	lea    0x2d78(%rip),%rax        # 5d60 <barriered_work_ingest_andwork>
    2fe8:	41 bc 01 00 00 00    	mov    $0x1,%r12d
          thread_data[x].tasks[y].run = barriered_work; 
    2fee:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2ff5:	e9 af f9 ff ff       	jmp    29a9 <main+0x379>
    2ffa:	48 8d 05 2f 28 00 00 	lea    0x282f(%rip),%rax        # 5830 <barriered_work>
    3001:	41 bc 02 00 00 00    	mov    $0x2,%r12d
    3007:	eb e5                	jmp    2fee <main+0x9be>
    3009:	41 89 f2             	mov    %esi,%r10d
      other = (x + 1) % total_threads;
    300c:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
      my_thread_data[0] = &thread_data[x]; 
    3011:	4c 89 33             	mov    %r14,(%rbx)
    3014:	4c 89 f1             	mov    %r14,%rcx
    3017:	4c 89 d7             	mov    %r10,%rdi
      other = (x + 1) % total_threads;
    301a:	4c 0f af d0          	imul   %rax,%r10
      thread_data[x].thread_index = 0;
    301e:	41 c7 06 00 00 00 00 	movl   $0x0,(%r14)
    3025:	48 8d 35 dd 42 00 00 	lea    0x42dd(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      other = (x + 1) % total_threads;
    302c:	49 c1 ea 22          	shr    $0x22,%r10
    3030:	43 8d 04 52          	lea    (%r10,%r10,2),%eax
    3034:	01 c0                	add    %eax,%eax
    3036:	29 c7                	sub    %eax,%edi
    3038:	48 63 c7             	movslq %edi,%rax
    303b:	bf 01 00 00 00       	mov    $0x1,%edi
      my_thread_data[1] = &thread_data[other]; 
    3040:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
      other = (x + 1) % total_threads;
    3044:	49 89 c7             	mov    %rax,%r15
      my_thread_data[1] = &thread_data[other]; 
    3047:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    304b:	48 8b 45 90          	mov    -0x70(%rbp),%rax
    304f:	8b 55 b0             	mov    -0x50(%rbp),%edx
    3052:	49 c1 e0 04          	shl    $0x4,%r8
    3056:	49 01 c0             	add    %rax,%r8
    3059:	31 c0                	xor    %eax,%eax
    305b:	4c 89 43 08          	mov    %r8,0x8(%rbx)
    305f:	e8 1c f4 ff ff       	call   2480 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    3064:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    3069:	48 89 45 80          	mov    %rax,-0x80(%rbp)
    306d:	49 89 c4             	mov    %rax,%r12
    3070:	e9 44 f8 ff ff       	jmp    28b9 <main+0x289>
        CPU_SET(curcpu, sendercpu);
    3075:	48 63 85 78 ff ff ff 	movslq -0x88(%rbp),%rax
    307c:	48 89 c7             	mov    %rax,%rdi
    307f:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    3085:	77 13                	ja     309a <main+0xa6a>
    3087:	48 c1 e8 06          	shr    $0x6,%rax
    308b:	ba 01 00 00 00       	mov    $0x1,%edx
    3090:	89 f9                	mov    %edi,%ecx
    3092:	48 d3 e2             	shl    %cl,%rdx
    3095:	49 09 54 c5 00       	or     %rdx,0x0(%r13,%rax,8)
        curcpu += 2;
    309a:	83 85 78 ff ff ff 02 	addl   $0x2,-0x88(%rbp)
    30a1:	e9 6c f8 ff ff       	jmp    2912 <main+0x2e2>
    30a6:	48 8d 3d cc 42 00 00 	lea    0x42cc(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    30ad:	45 31 f6             	xor    %r14d,%r14d
    30b0:	4c 8d 6d c0          	lea    -0x40(%rbp),%r13
    30b4:	e8 57 f2 ff ff       	call   2310 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    30b9:	4c 8d 25 d7 42 00 00 	lea    0x42d7(%rip),%r12        # 7397 <_IO_stdin_used+0x397>
    void * result; 
    pthread_join(thread[x], &result);
    30c0:	4a 8b 3c f3          	mov    (%rbx,%r14,8),%rdi
    30c4:	4c 89 ee             	mov    %r13,%rsi
    30c7:	e8 64 f4 ff ff       	call   2530 <pthread_join@plt>
    30cc:	44 89 f2             	mov    %r14d,%edx
    30cf:	4c 89 e6             	mov    %r12,%rsi
    30d2:	bf 01 00 00 00       	mov    $0x1,%edi
    30d7:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    30d9:	49 83 c6 01          	add    $0x1,%r14
    30dd:	e8 9e f3 ff ff       	call   2480 <__printf_chk@plt>
    30e2:	49 83 fe 06          	cmp    $0x6,%r14
    30e6:	75 d8                	jne    30c0 <main+0xa90>
    30e8:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
    30ef:	31 c9                	xor    %ecx,%ecx
  long ingests = 0;
    30f1:	45 31 db             	xor    %r11d,%r11d
  long sents = 0;
  long received = 0;
    30f4:	45 31 d2             	xor    %r10d,%r10d
  for (int x = 0 ; x < thread_count ; x++) {
    30f7:	c7 45 a8 00 00 00 00 	movl   $0x0,-0x58(%rbp)
  long total = 0;
    30fe:	31 db                	xor    %ebx,%ebx
    3100:	4d 89 d4             	mov    %r10,%r12
    3103:	48 89 45 a0          	mov    %rax,-0x60(%rbp)
    3107:	48 8b 45 90          	mov    -0x70(%rbp),%rax
    310b:	49 89 df             	mov    %rbx,%r15
    310e:	4c 89 5d 98          	mov    %r11,-0x68(%rbp)
    3112:	48 89 4d 88          	mov    %rcx,-0x78(%rbp)
    3116:	4c 8d 70 28          	lea    0x28(%rax),%r14
    311a:	bf 0a 00 00 00       	mov    $0xa,%edi
    311f:	44 8b 6d a8          	mov    -0x58(%rbp),%r13d
    3123:	e8 c8 f1 ff ff       	call   22f0 <putchar@plt>
    3128:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
    312c:	bf 01 00 00 00       	mov    $0x1,%edi
    3131:	48 8d 35 73 42 00 00 	lea    0x4273(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    3138:	41 83 f5 01          	xor    $0x1,%r13d
    313c:	48 8b 10             	mov    (%rax),%rdx
    313f:	31 c0                	xor    %eax,%eax
    3141:	e8 3a f3 ff ff       	call   2480 <__printf_chk@plt>
      other = (x + 1) % total_threads;
    }
    printf("\n");
    printf("Total Protected %ld\n", protected_state[me].protected);

    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3146:	41 8b 56 08          	mov    0x8(%r14),%edx
    314a:	85 d2                	test   %edx,%edx
    314c:	0f 8e 21 04 00 00    	jle    3573 <main+0xf43>
    3152:	48 63 f2             	movslq %edx,%rsi
    3155:	49 8b 06             	mov    (%r14),%rax
    long v = 0;
    3158:	31 d2                	xor    %edx,%edx
    315a:	48 c1 e6 09          	shl    $0x9,%rsi
    315e:	48 01 c6             	add    %rax,%rsi
    3161:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      v += thread_data[me].tasks[n].v;
    3168:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    316f:	48 05 00 02 00 00    	add    $0x200,%rax
    3175:	48 39 f0             	cmp    %rsi,%rax
    3178:	75 ee                	jne    3168 <main+0xb38>
    }
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    317a:	49 63 c5             	movslq %r13d,%rax
    317d:	48 8b 7d 90          	mov    -0x70(%rbp),%rdi
    3181:	48 f7 d8             	neg    %rax
    3184:	25 b0 00 00 00       	and    $0xb0,%eax
    3189:	48 01 f8             	add    %rdi,%rax
    318c:	48 63 70 30          	movslq 0x30(%rax),%rsi
    3190:	85 f6                	test   %esi,%esi
    3192:	7e 1e                	jle    31b2 <main+0xb82>
    3194:	48 8b 40 28          	mov    0x28(%rax),%rax
    3198:	48 c1 e6 09          	shl    $0x9,%rsi
    319c:	48 01 c6             	add    %rax,%rsi
    319f:	90                   	nop
      v += thread_data[other].tasks[n].v;
    31a0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    31a7:	48 05 00 02 00 00    	add    $0x200,%rax
    31ad:	48 39 f0             	cmp    %rsi,%rax
    31b0:	75 ee                	jne    31a0 <main+0xb70>
    31b2:	48 8d 35 07 42 00 00 	lea    0x4207(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    31b9:	bf 01 00 00 00       	mov    $0x1,%edi
    31be:	31 c0                	xor    %eax,%eax
    31c0:	e8 bb f2 ff ff       	call   2480 <__printf_chk@plt>
    }
    printf("Total V %ld\n", v);
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    31c5:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
    31c9:	bf 01 00 00 00       	mov    $0x1,%edi
    31ce:	48 8b 30             	mov    (%rax),%rsi
    31d1:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    31db:	48 f7 ee             	imul   %rsi
    31de:	48 c1 fe 3f          	sar    $0x3f,%rsi
    31e2:	31 c0                	xor    %eax,%eax
    31e4:	48 d1 fa             	sar    %rdx
    31e7:	48 29 f2             	sub    %rsi,%rdx
    31ea:	48 8d 35 1f 44 00 00 	lea    0x441f(%rip),%rsi        # 7610 <_IO_stdin_used+0x610>
    31f1:	e8 8a f2 ff ff       	call   2480 <__printf_chk@plt>
    31f6:	bf 0a 00 00 00       	mov    $0xa,%edi
    31fb:	e8 f0 f0 ff ff       	call   22f0 <putchar@plt>
    printf("\n");
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3200:	41 8b 56 08          	mov    0x8(%r14),%edx
    3204:	85 d2                	test   %edx,%edx
    3206:	7e 57                	jle    325f <main+0xc2f>
    3208:	49 8b 06             	mov    (%r14),%rax
    320b:	48 63 fa             	movslq %edx,%rdi
    320e:	48 8b 4d 98          	mov    -0x68(%rbp),%rcx
    3212:	48 c1 e7 09          	shl    $0x9,%rdi
    3216:	4c 8b 55 88          	mov    -0x78(%rbp),%r10
    321a:	48 01 c7             	add    %rax,%rdi
    321d:	0f 1f 00             	nopl   (%rax)
      total += thread_data[x].tasks[n].n;
      ingests += thread_data[x].tasks[n].ingest_count;
      sends += thread_data[x].tasks[n].sends;
      for (int k = 0 ; k < thread_count ; k++) {
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3220:	48 8b 90 68 01 00 00 	mov    0x168(%rax),%rdx
      total += thread_data[x].tasks[n].n;
    3227:	4c 03 b8 08 01 00 00 	add    0x108(%rax),%r15
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    322e:	48 05 00 02 00 00    	add    $0x200,%rax
      ingests += thread_data[x].tasks[n].ingest_count;
    3234:	48 03 88 60 ff ff ff 	add    -0xa0(%rax),%rcx
      sends += thread_data[x].tasks[n].sends;
    323b:	4c 03 90 70 ff ff ff 	add    -0x90(%rax),%r10
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3242:	48 03 5a 10          	add    0x10(%rdx),%rbx
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3246:	4c 03 62 18          	add    0x18(%rdx),%r12
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    324a:	48 03 5a 30          	add    0x30(%rdx),%rbx
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    324e:	4c 03 62 38          	add    0x38(%rdx),%r12
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3252:	48 39 f8             	cmp    %rdi,%rax
    3255:	75 c9                	jne    3220 <main+0xbf0>
    3257:	48 89 4d 98          	mov    %rcx,-0x68(%rbp)
    325b:	4c 89 55 88          	mov    %r10,-0x78(%rbp)
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      // printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
      // printf("%ld iterations\n", thread_data[x].iteration_count);
    }
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    325f:	45 31 ed             	xor    %r13d,%r13d
    3262:	49 83 7e 68 00       	cmpq   $0x0,0x68(%r14)
    3267:	0f 8e 7d 00 00 00    	jle    32ea <main+0xcba>
    326d:	4c 89 ef             	mov    %r13,%rdi
    3270:	4c 89 f0             	mov    %r14,%rax
    3273:	49 89 dd             	mov    %rbx,%r13
    3276:	4d 89 e6             	mov    %r12,%r14
    3279:	48 89 fb             	mov    %rdi,%rbx
    327c:	49 89 c4             	mov    %rax,%r12
    327f:	90                   	nop
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3280:	49 8b 44 24 58       	mov    0x58(%r12),%rax
    3285:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    3289:	48 83 ec 08          	sub    $0x8,%rsp
    328d:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3292:	48 83 c3 01          	add    $0x1,%rbx
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3296:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    329a:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    32a4:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    32a8:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32ac:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    32af:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    32b3:	4c 2b 01             	sub    (%rcx),%r8
    32b6:	31 c0                	xor    %eax,%eax
    32b8:	8b 49 20             	mov    0x20(%rcx),%ecx
    32bb:	56                   	push   %rsi
    32bc:	48 8d 35 6d 43 00 00 	lea    0x436d(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    32c3:	48 c1 ea 12          	shr    $0x12,%rdx
    32c7:	49 89 d1             	mov    %rdx,%r9
    32ca:	ba 02 00 00 00       	mov    $0x2,%edx
    32cf:	e8 ac f1 ff ff       	call   2480 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    32d4:	41 5b                	pop    %r11
    32d6:	58                   	pop    %rax
    32d7:	49 39 5c 24 68       	cmp    %rbx,0x68(%r12)
    32dc:	7f a2                	jg     3280 <main+0xc50>
    32de:	4c 89 e0             	mov    %r12,%rax
    32e1:	4c 89 eb             	mov    %r13,%rbx
    32e4:	4d 89 f4             	mov    %r14,%r12
    32e7:	49 89 c6             	mov    %rax,%r14
      // printf("%ldns per thread\n", (seconds2 / 2));
    }
    // printf("cycles %ld\n", thread_data[x].cycles);

    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    32ea:	41 8b b6 84 00 00 00 	mov    0x84(%r14),%esi
    32f1:	85 f6                	test   %esi,%esi
    32f3:	0f 8e 16 01 00 00    	jle    340f <main+0xddf>
    32f9:	4c 89 7d 80          	mov    %r15,-0x80(%rbp)
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    32fd:	4d 8b 4e 18          	mov    0x18(%r14),%r9
    3301:	31 d2                	xor    %edx,%edx
    3303:	48 89 9d 78 ff ff ff 	mov    %rbx,-0x88(%rbp)
    330a:	4c 89 a5 60 ff ff ff 	mov    %r12,-0xa0(%rbp)
    3311:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3318:	49 8b 04 d1          	mov    (%r9,%rdx,8),%rax
    331c:	41 89 d7             	mov    %edx,%r15d
    331f:	48 8d 1c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rbx
    3327:	44 8b 00             	mov    (%rax),%r8d
    332a:	45 85 c0             	test   %r8d,%r8d
    332d:	0f 8e be 00 00 00    	jle    33f1 <main+0xdc1>
    3333:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3337:	48 8b 48 08          	mov    0x8(%rax),%rcx
    333b:	31 c0                	xor    %eax,%eax
    333d:	48 89 c6             	mov    %rax,%rsi
    3340:	49 89 f4             	mov    %rsi,%r12
    3343:	45 31 ed             	xor    %r13d,%r13d
    3346:	49 c1 e4 08          	shl    $0x8,%r12
    334a:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    334e:	8b ba 94 00 00 00    	mov    0x94(%rdx),%edi
    3354:	85 ff                	test   %edi,%edi
    3356:	0f 8e 7d 00 00 00    	jle    33d9 <main+0xda9>
    335c:	48 89 75 b8          	mov    %rsi,-0x48(%rbp)
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3360:	4c 89 e9             	mov    %r13,%rcx
    3363:	48 83 ec 08          	sub    $0x8,%rsp
    3367:	bf 01 00 00 00       	mov    $0x1,%edi
	  struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
	  const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
	  const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
	  printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    336c:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3376:	48 c1 e1 05          	shl    $0x5,%rcx
    337a:	48 03 8a 88 00 00 00 	add    0x88(%rdx),%rcx
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3381:	49 83 c5 01          	add    $0x1,%r13
	  const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3385:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3389:	48 2b 71 08          	sub    0x8(%rcx),%rsi
	  printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    338d:	48 f7 e6             	mul    %rsi
	  const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3390:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3394:	4c 2b 01             	sub    (%rcx),%r8
    3397:	56                   	push   %rsi
    3398:	44 89 f9             	mov    %r15d,%ecx
    339b:	48 8d 35 de 42 00 00 	lea    0x42de(%rip),%rsi        # 7680 <_IO_stdin_used+0x680>
    33a2:	31 c0                	xor    %eax,%eax
    33a4:	48 c1 ea 12          	shr    $0x12,%rdx
    33a8:	49 89 d1             	mov    %rdx,%r9
    33ab:	ba 02 00 00 00       	mov    $0x2,%edx
    33b0:	e8 cb f0 ff ff       	call   2480 <__printf_chk@plt>
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    33b5:	4d 8b 4e 18          	mov    0x18(%r14),%r9
    33b9:	41 58                	pop    %r8
    33bb:	41 5a                	pop    %r10
    33bd:	49 8b 04 19          	mov    (%r9,%rbx,1),%rax
    33c1:	48 8b 48 08          	mov    0x8(%rax),%rcx
    33c5:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    33c9:	44 39 aa 94 00 00 00 	cmp    %r13d,0x94(%rdx)
    33d0:	7f 8e                	jg     3360 <main+0xd30>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    33d2:	48 8b 75 b8          	mov    -0x48(%rbp),%rsi
    33d6:	44 8b 00             	mov    (%rax),%r8d
    33d9:	48 83 c6 01          	add    $0x1,%rsi
    33dd:	41 39 f0             	cmp    %esi,%r8d
    33e0:	0f 8f 5a ff ff ff    	jg     3340 <main+0xd10>
    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    33e6:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    33ea:	41 8b b6 84 00 00 00 	mov    0x84(%r14),%esi
    33f1:	48 83 c2 01          	add    $0x1,%rdx
    33f5:	39 d6                	cmp    %edx,%esi
    33f7:	0f 8f 1b ff ff ff    	jg     3318 <main+0xce8>
    33fd:	4c 8b 7d 80          	mov    -0x80(%rbp),%r15
    3401:	48 8b 9d 78 ff ff ff 	mov    -0x88(%rbp),%rbx
    3408:	4c 8b a5 60 ff ff ff 	mov    -0xa0(%rbp),%r12
  for (int x = 0 ; x < thread_count ; x++) {
    340f:	8b 45 a8             	mov    -0x58(%rbp),%eax
    3412:	48 83 45 a0 18       	addq   $0x18,-0x60(%rbp)
    3417:	49 81 c6 b0 00 00 00 	add    $0xb0,%r14
    341e:	85 c0                	test   %eax,%eax
    3420:	75 0c                	jne    342e <main+0xdfe>
    3422:	c7 45 a8 01 00 00 00 	movl   $0x1,-0x58(%rbp)
    3429:	e9 ec fc ff ff       	jmp    311a <main+0xaea>
    342e:	48 8b 4d 88          	mov    -0x78(%rbp),%rcx
    3432:	4c 8b 5d 98          	mov    -0x68(%rbp),%r11
    3436:	4c 89 fa             	mov    %r15,%rdx
    3439:	bf 01 00 00 00       	mov    $0x1,%edi
    343e:	48 8d 35 88 3f 00 00 	lea    0x3f88(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    3445:	31 c0                	xor    %eax,%eax
    3447:	48 89 5d b0          	mov    %rbx,-0x50(%rbp)
    344b:	4c 89 fb             	mov    %r15,%rbx
    344e:	48 89 4d a8          	mov    %rcx,-0x58(%rbp)
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
  printf("Total Requests per second %ld\n", total / DURATION);
    3452:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3456:	4c 89 5d a0          	mov    %r11,-0x60(%rbp)
    345a:	4c 89 65 b8          	mov    %r12,-0x48(%rbp)
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    345e:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    3468:	e8 13 f0 ff ff       	call   2480 <__printf_chk@plt>
    346d:	bf 0a 00 00 00       	mov    $0xa,%edi
    3472:	e8 79 ee ff ff       	call   22f0 <putchar@plt>
    3477:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
    347e:	bf 01 00 00 00       	mov    $0x1,%edi
    3483:	48 8d 35 4e 42 00 00 	lea    0x424e(%rip),%rsi        # 76d8 <_IO_stdin_used+0x6d8>
    348a:	48 8b 50 08          	mov    0x8(%rax),%rdx
    348e:	31 c0                	xor    %eax,%eax
    3490:	e8 eb ef ff ff       	call   2480 <__printf_chk@plt>
    3495:	4c 8b 5d a0          	mov    -0x60(%rbp),%r11
    3499:	bf 01 00 00 00       	mov    $0x1,%edi
    349e:	48 8d 35 5b 42 00 00 	lea    0x425b(%rip),%rsi        # 7700 <_IO_stdin_used+0x700>
    34a5:	4c 89 d8             	mov    %r11,%rax
    34a8:	49 c1 fb 3f          	sar    $0x3f,%r11
    34ac:	49 f7 ec             	imul   %r12
    34af:	31 c0                	xor    %eax,%eax
    34b1:	48 d1 fa             	sar    %rdx
    34b4:	4c 29 da             	sub    %r11,%rdx
    34b7:	e8 c4 ef ff ff       	call   2480 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    34bc:	48 8b 4d a8          	mov    -0x58(%rbp),%rcx
    34c0:	bf 01 00 00 00       	mov    $0x1,%edi
    34c5:	48 8d 35 64 42 00 00 	lea    0x4264(%rip),%rsi        # 7730 <_IO_stdin_used+0x730>
    34cc:	48 89 c8             	mov    %rcx,%rax
    34cf:	48 c1 f9 3f          	sar    $0x3f,%rcx
    34d3:	49 f7 ec             	imul   %r12
    34d6:	31 c0                	xor    %eax,%eax
    34d8:	48 d1 fa             	sar    %rdx
    34db:	48 29 ca             	sub    %rcx,%rdx
    34de:	e8 9d ef ff ff       	call   2480 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    34e3:	4c 89 f8             	mov    %r15,%rax
    34e6:	bf 01 00 00 00       	mov    $0x1,%edi
    34eb:	48 8d 35 6e 42 00 00 	lea    0x426e(%rip),%rsi        # 7760 <_IO_stdin_used+0x760>
    34f2:	49 f7 ec             	imul   %r12
    34f5:	31 c0                	xor    %eax,%eax
    34f7:	48 d1 fa             	sar    %rdx
    34fa:	48 29 da             	sub    %rbx,%rdx
    34fd:	e8 7e ef ff ff       	call   2480 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3502:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    3506:	bf 01 00 00 00       	mov    $0x1,%edi
    350b:	48 8d 35 cf 3e 00 00 	lea    0x3ecf(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    3512:	4c 89 c8             	mov    %r9,%rax
    3515:	49 c1 f9 3f          	sar    $0x3f,%r9
    3519:	49 f7 ec             	imul   %r12
    351c:	31 c0                	xor    %eax,%eax
    351e:	48 d1 fa             	sar    %rdx
    3521:	4c 29 ca             	sub    %r9,%rdx
    3524:	e8 57 ef ff ff       	call   2480 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3529:	4c 8b 55 b8          	mov    -0x48(%rbp),%r10
    352d:	bf 01 00 00 00       	mov    $0x1,%edi
    3532:	48 8d 35 b9 3e 00 00 	lea    0x3eb9(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    3539:	4c 89 d0             	mov    %r10,%rax
    353c:	49 f7 ec             	imul   %r12
    353f:	4c 89 d0             	mov    %r10,%rax
    3542:	48 c1 f8 3f          	sar    $0x3f,%rax
    3546:	48 d1 fa             	sar    %rdx
    3549:	48 29 c2             	sub    %rax,%rdx
    354c:	31 c0                	xor    %eax,%eax
    354e:	e8 2d ef ff ff       	call   2480 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3553:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    3557:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3560:	75 18                	jne    357a <main+0xf4a>
    3562:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
    3566:	31 c0                	xor    %eax,%eax
    3568:	5b                   	pop    %rbx
    3569:	41 5c                	pop    %r12
    356b:	41 5d                	pop    %r13
    356d:	41 5e                	pop    %r14
    356f:	41 5f                	pop    %r15
    3571:	5d                   	pop    %rbp
    3572:	c3                   	ret
    long v = 0;
    3573:	31 d2                	xor    %edx,%edx
    3575:	e9 00 fc ff ff       	jmp    317a <main+0xb4a>
}
    357a:	e8 d1 ed ff ff       	call   2350 <__stack_chk_fail@plt>
    357f:	90                   	nop

0000000000003580 <_start>:
    3580:	f3 0f 1e fa          	endbr64
    3584:	31 ed                	xor    %ebp,%ebp
    3586:	49 89 d1             	mov    %rdx,%r9
    3589:	5e                   	pop    %rsi
    358a:	48 89 e2             	mov    %rsp,%rdx
    358d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3591:	50                   	push   %rax
    3592:	54                   	push   %rsp
    3593:	45 31 c0             	xor    %r8d,%r8d
    3596:	31 c9                	xor    %ecx,%ecx
    3598:	48 8d 3d 91 f0 ff ff 	lea    -0xf6f(%rip),%rdi        # 2630 <main>
    359f:	ff 15 2b 6a 00 00    	call   *0x6a2b(%rip)        # 9fd0 <__libc_start_main@GLIBC_2.34>
    35a5:	f4                   	hlt
    35a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000035b0 <__gmon_start__>:
    35b0:	f3 0f 1e fa          	endbr64
    35b4:	8b 05 6e 6a 00 00    	mov    0x6a6e(%rip),%eax        # a028 <called.0>
    35ba:	85 c0                	test   %eax,%eax
    35bc:	74 02                	je     35c0 <__gmon_start__+0x10>
    35be:	c3                   	ret
    35bf:	90                   	nop
    35c0:	48 83 ec 08          	sub    $0x8,%rsp
    35c4:	48 8d 35 a2 2e 00 00 	lea    0x2ea2(%rip),%rsi        # 646d <etext>
    35cb:	48 8d 3d 2e ca ff ff 	lea    -0x35d2(%rip),%rdi        # 0 <__executable_start>
    35d2:	c7 05 4c 6a 00 00 01 00 00 00 	movl   $0x1,0x6a4c(%rip)        # a028 <called.0>
    35dc:	e8 ff ed ff ff       	call   23e0 <__monstartup@plt>
    35e1:	48 8b 3d f8 69 00 00 	mov    0x69f8(%rip),%rdi        # 9fe0 <_mcleanup@GLIBC_2.2.5>
    35e8:	48 83 c4 08          	add    $0x8,%rsp
    35ec:	e9 3f 2e 00 00       	jmp    6430 <atexit>
    35f1:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    35fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003600 <_dl_relocate_static_pie>:
    3600:	f3 0f 1e fa          	endbr64
    3604:	c3                   	ret
    3605:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    360f:	90                   	nop

0000000000003610 <deregister_tm_clones>:
    3610:	48 8d 3d 09 6a 00 00 	lea    0x6a09(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3617:	48 8d 05 02 6a 00 00 	lea    0x6a02(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    361e:	48 39 f8             	cmp    %rdi,%rax
    3621:	74 15                	je     3638 <deregister_tm_clones+0x28>
    3623:	48 8b 05 ae 69 00 00 	mov    0x69ae(%rip),%rax        # 9fd8 <_ITM_deregisterTMCloneTable@Base>
    362a:	48 85 c0             	test   %rax,%rax
    362d:	74 09                	je     3638 <deregister_tm_clones+0x28>
    362f:	ff e0                	jmp    *%rax
    3631:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3638:	c3                   	ret
    3639:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003640 <register_tm_clones>:
    3640:	48 8d 3d d9 69 00 00 	lea    0x69d9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3647:	48 8d 35 d2 69 00 00 	lea    0x69d2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    364e:	48 29 fe             	sub    %rdi,%rsi
    3651:	48 89 f0             	mov    %rsi,%rax
    3654:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3658:	48 c1 f8 03          	sar    $0x3,%rax
    365c:	48 01 c6             	add    %rax,%rsi
    365f:	48 d1 fe             	sar    %rsi
    3662:	74 14                	je     3678 <register_tm_clones+0x38>
    3664:	48 8b 05 85 69 00 00 	mov    0x6985(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    366b:	48 85 c0             	test   %rax,%rax
    366e:	74 08                	je     3678 <register_tm_clones+0x38>
    3670:	ff e0                	jmp    *%rax
    3672:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3678:	c3                   	ret
    3679:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003680 <__do_global_dtors_aux>:
    3680:	f3 0f 1e fa          	endbr64
    3684:	80 3d a1 69 00 00 00 	cmpb   $0x0,0x69a1(%rip)        # a02c <completed.0>
    368b:	75 2b                	jne    36b8 <__do_global_dtors_aux+0x38>
    368d:	55                   	push   %rbp
    368e:	48 83 3d 62 69 00 00 00 	cmpq   $0x0,0x6962(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3696:	48 89 e5             	mov    %rsp,%rbp
    3699:	74 0c                	je     36a7 <__do_global_dtors_aux+0x27>
    369b:	48 8b 3d 66 69 00 00 	mov    0x6966(%rip),%rdi        # a008 <__dso_handle>
    36a2:	e8 29 ec ff ff       	call   22d0 <__cxa_finalize@plt>
    36a7:	e8 64 ff ff ff       	call   3610 <deregister_tm_clones>
    36ac:	c6 05 79 69 00 00 01 	movb   $0x1,0x6979(%rip)        # a02c <completed.0>
    36b3:	5d                   	pop    %rbp
    36b4:	c3                   	ret
    36b5:	0f 1f 00             	nopl   (%rax)
    36b8:	c3                   	ret
    36b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000036c0 <frame_dummy>:
    36c0:	f3 0f 1e fa          	endbr64
    36c4:	e9 77 ff ff ff       	jmp    3640 <register_tm_clones>
    36c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000036d0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    36d0:	f3 0f 1e fa          	endbr64
    36d4:	55                   	push   %rbp
    36d5:	48 89 e5             	mov    %rsp,%rbp
    36d8:	ff 15 0a 69 00 00    	call   *0x690a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  struct ProtectedState *protected = data->thread->protected_state;
    36de:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    36e5:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    36e9:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    36f1:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    36f5:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    36f9:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3700:	48 85 c9             	test   %rcx,%rcx
    3703:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    370a:	48 0f 4f d6          	cmovg  %rsi,%rdx
    370e:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3712:	31 c0                	xor    %eax,%eax
    3714:	5d                   	pop    %rbp
    3715:	c3                   	ret
    3716:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003720 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3720:	f3 0f 1e fa          	endbr64
    3724:	55                   	push   %rbp
    3725:	48 89 e5             	mov    %rsp,%rbp
    3728:	ff 15 ba 68 00 00    	call   *0x68ba(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    for (int x = 0 ; x < data->task_count ; x++) {
    372e:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    3735:	85 c9                	test   %ecx,%ecx
    3737:	7e 4d                	jle    3786 <barriered_reset+0x66>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3739:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3740:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    3747:	48 c1 e1 09          	shl    $0x9,%rcx
    374b:	48 8b 50 10          	mov    0x10(%rax),%rdx
    374f:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3753:	48 8b 70 28          	mov    0x28(%rax),%rsi
    3757:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3759:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    375d:	0f 1f 00             	nopl   (%rax)
    3760:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3768:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3770:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    377b:	48 05 00 02 00 00    	add    $0x200,%rax
    3781:	48 39 c1             	cmp    %rax,%rcx
    3784:	75 da                	jne    3760 <barriered_reset+0x40>
  asm volatile ("sfence" ::: "memory");
    3786:	0f ae f8             	sfence
}
    3789:	31 c0                	xor    %eax,%eax
    378b:	5d                   	pop    %rbp
    378c:	c3                   	ret
    378d:	0f 1f 00             	nopl   (%rax)

0000000000003790 <external_thread>:
void * external_thread(void *arg) {
    3790:	f3 0f 1e fa          	endbr64
    3794:	55                   	push   %rbp
    3795:	48 89 e5             	mov    %rsp,%rbp
    3798:	41 57                	push   %r15
    379a:	41 56                	push   %r14
    379c:	41 55                	push   %r13
    379e:	41 54                	push   %r12
    37a0:	53                   	push   %rbx
    37a1:	48 83 ec 08          	sub    $0x8,%rsp
    37a5:	ff 15 3d 68 00 00    	call   *0x683d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  while (data->running == 1) {
    37ab:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
void * external_thread(void *arg) {
    37af:	49 89 fe             	mov    %rdi,%r14
  while (data->running == 1) {
    37b2:	75 6b                	jne    381f <external_thread+0x8f>
    for (int b = 0; b < data->buffers_count; b++) {
    37b4:	8b b7 ac 00 00 00    	mov    0xac(%rdi),%esi
    37ba:	4c 8b 47 40          	mov    0x40(%rdi),%r8
    37be:	66 90                	xchg   %ax,%ax
    37c0:	85 f6                	test   %esi,%esi
    37c2:	7e 6c                	jle    3830 <external_thread+0xa0>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    37c4:	45 31 ed             	xor    %r13d,%r13d
    37c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    37d0:	4e 8d 3c ed 00 00 00 00 	lea    0x0(,%r13,8),%r15
    37d8:	31 db                	xor    %ebx,%ebx
    37da:	4b 8d 3c 38          	lea    (%r8,%r15,1),%rdi
    37de:	48 8b 07             	mov    (%rdi),%rax
    37e1:	8b 10                	mov    (%rax),%edx
    37e3:	85 d2                	test   %edx,%edx
    37e5:	7e 28                	jle    380f <external_thread+0x7f>
    37e7:	48 8b 70 08          	mov    0x8(%rax),%rsi
				if (data->buffers[b]->buffer[x].available == 0) {
    37eb:	49 89 dc             	mov    %rbx,%r12
    37ee:	49 c1 e4 08          	shl    $0x8,%r12
    37f2:	4a 8d 04 26          	lea    (%rsi,%r12,1),%rax
    37f6:	8b 88 80 00 00 00    	mov    0x80(%rax),%ecx
    37fc:	85 c9                	test   %ecx,%ecx
    37fe:	74 38                	je     3838 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3800:	48 83 c3 01          	add    $0x1,%rbx
    3804:	39 da                	cmp    %ebx,%edx
    3806:	7f e3                	jg     37eb <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    3808:	41 8b b6 ac 00 00 00 	mov    0xac(%r14),%esi
    380f:	49 83 c5 01          	add    $0x1,%r13
    3813:	44 39 ee             	cmp    %r13d,%esi
    3816:	7f b8                	jg     37d0 <external_thread+0x40>
  while (data->running == 1) {
    3818:	41 83 7e 34 01       	cmpl   $0x1,0x34(%r14)
    381d:	74 a1                	je     37c0 <external_thread+0x30>
}
    381f:	48 83 c4 08          	add    $0x8,%rsp
    3823:	31 c0                	xor    %eax,%eax
    3825:	5b                   	pop    %rbx
    3826:	41 5c                	pop    %r12
    3828:	41 5d                	pop    %r13
    382a:	41 5e                	pop    %r14
    382c:	41 5f                	pop    %r15
    382e:	5d                   	pop    %rbp
    382f:	c3                   	ret
  while (data->running == 1) {
    3830:	eb fe                	jmp    3830 <external_thread+0xa0>
    3832:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
					data->buffers[b]->buffer[x].data = "Hello world";
    3838:	48 8d 0d c5 37 00 00 	lea    0x37c5(%rip),%rcx        # 7004 <_IO_stdin_used+0x4>
    383f:	48 89 08             	mov    %rcx,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    3842:	48 8b 07             	mov    (%rdi),%rax
    3845:	bf 04 00 00 00       	mov    $0x4,%edi
    384a:	48 8b 48 08          	mov    0x8(%rax),%rcx
    384e:	4c 01 e1             	add    %r12,%rcx
    3851:	48 63 b1 94 00 00 00 	movslq 0x94(%rcx),%rsi
    3858:	48 c1 e6 05          	shl    $0x5,%rsi
    385c:	48 03 b1 88 00 00 00 	add    0x88(%rcx),%rsi
    3863:	e8 c8 ea ff ff       	call   2330 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    3868:	49 8b 46 40          	mov    0x40(%r14),%rax
    386c:	4a 8b 04 38          	mov    (%rax,%r15,1),%rax
    3870:	48 8b 40 08          	mov    0x8(%rax),%rax
    3874:	42 c7 84 20 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%r12,1)
          asm volatile ("sfence" ::: "memory");
    3880:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3883:	4d 8b 46 40          	mov    0x40(%r14),%r8
    3887:	48 83 c3 01          	add    $0x1,%rbx
    388b:	4b 8d 3c 38          	lea    (%r8,%r15,1),%rdi
    388f:	48 8b 07             	mov    (%rdi),%rax
    3892:	8b 10                	mov    (%rax),%edx
    3894:	39 da                	cmp    %ebx,%edx
    3896:	0f 8f 4b ff ff ff    	jg     37e7 <external_thread+0x57>
    389c:	e9 67 ff ff ff       	jmp    3808 <external_thread+0x78>
    38a1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    38ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000038b0 <timer_thread>:
void* timer_thread(void *arg) {
    38b0:	f3 0f 1e fa          	endbr64
    38b4:	55                   	push   %rbp
    38b5:	48 89 e5             	mov    %rsp,%rbp
    38b8:	41 57                	push   %r15
    38ba:	41 56                	push   %r14
    38bc:	41 55                	push   %r13
    38be:	41 54                	push   %r12
    38c0:	53                   	push   %rbx
    38c1:	48 83 ec 68          	sub    $0x68,%rsp
    38c5:	ff 15 1d 67 00 00    	call   *0x671d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    38cb:	48 8d 35 3e 37 00 00 	lea    0x373e(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    38d2:	8b 17                	mov    (%rdi),%edx
    38d4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    38dd:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    38e1:	31 c0                	xor    %eax,%eax
    38e3:	49 89 fd             	mov    %rdi,%r13
    38e6:	bf 01 00 00 00       	mov    $0x1,%edi
    38eb:	e8 90 eb ff ff       	call   2480 <__printf_chk@plt>
  struct timespec preempt = {
    38f0:	66 0f 6f 05 88 40 00 00 	movdqa 0x4088(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    38f8:	ba 88 13 00 00       	mov    $0x1388,%edx
    38fd:	31 c0                	xor    %eax,%eax
    38ff:	48 8d 35 1c 37 00 00 	lea    0x371c(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3906:	bf 01 00 00 00       	mov    $0x1,%edi
    390b:	0f 29 45 90          	movaps %xmm0,-0x70(%rbp)
    390f:	e8 6c eb ff ff       	call   2480 <__printf_chk@plt>
  while (data->running && n < times) {
    3914:	41 8b 45 34          	mov    0x34(%r13),%eax
    3918:	89 85 7c ff ff ff    	mov    %eax,-0x84(%rbp)
    391e:	85 c0                	test   %eax,%eax
    3920:	0f 84 b2 00 00 00    	je     39d8 <timer_thread+0x128>
  int n = 0;
    3926:	45 31 ff             	xor    %r15d,%r15d
    3929:	4c 8d 75 80          	lea    -0x80(%rbp),%r14
    392d:	4c 8d 65 90          	lea    -0x70(%rbp),%r12
    y++;
    3931:	31 db                	xor    %ebx,%ebx
  int y = 0;
    3933:	c7 85 7c ff ff ff 00 00 00 00 	movl   $0x0,-0x84(%rbp)
    nanosleep(&preempt , &rem2);
    393d:	4c 89 e7             	mov    %r12,%rdi
    3940:	4c 89 f6             	mov    %r14,%rsi
    n++;
    3943:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3947:	e8 24 ea ff ff       	call   2370 <nanosleep@plt>
    y++;
    394c:	8b bd 7c ff ff ff    	mov    -0x84(%rbp),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3952:	49 63 45 18          	movslq 0x18(%r13),%rax
    y++;
    3956:	83 c7 01             	add    $0x1,%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3959:	85 c0                	test   %eax,%eax
    395b:	7e 50                	jle    39ad <timer_thread+0xfd>
        data->threads[x]->tasks[y].scheduled = 0;
    395d:	48 63 95 7c ff ff ff 	movslq -0x84(%rbp),%rdx
    3964:	49 8b 4d 10          	mov    0x10(%r13),%rcx
    3968:	48 c1 e2 09          	shl    $0x9,%rdx
    396c:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3970:	49 89 d1             	mov    %rdx,%r9
    3973:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3978:	4c 8b 19             	mov    (%rcx),%r11
    397b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    397d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3981:	99                   	cltd
    3982:	41 f7 7b 30          	idivl  0x30(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    3986:	49 8b 73 28          	mov    0x28(%r11),%rsi
    398a:	48 63 d2             	movslq %edx,%rdx
    398d:	48 c1 e2 09          	shl    $0x9,%rdx
    3991:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    399c:	42 c7 84 0e 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r9,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    39a8:	49 39 c8             	cmp    %rcx,%r8
    39ab:	75 cb                	jne    3978 <timer_thread+0xc8>
    asm volatile ("mfence" ::: "memory");
    39ad:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    39b0:	49 8b 45 10          	mov    0x10(%r13),%rax
  while (data->running && n < times) {
    39b4:	41 8b 55 34          	mov    0x34(%r13),%edx
    if (y >= data->threads[0]->task_count) {
    39b8:	48 8b 00             	mov    (%rax),%rax
    y++;
    39bb:	39 78 30             	cmp    %edi,0x30(%rax)
    39be:	0f 4e fb             	cmovle %ebx,%edi
    39c1:	89 bd 7c ff ff ff    	mov    %edi,-0x84(%rbp)
  while (data->running && n < times) {
    39c7:	85 d2                	test   %edx,%edx
    39c9:	74 0d                	je     39d8 <timer_thread+0x128>
    39cb:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    39d2:	0f 85 65 ff ff ff    	jne    393d <timer_thread+0x8d>
    39d8:	48 8d 3d 59 36 00 00 	lea    0x3659(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    39df:	e8 2c e9 ff ff       	call   2310 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    39e4:	49 63 55 1c          	movslq 0x1c(%r13),%rdx
    39e8:	85 d2                	test   %edx,%edx
    39ea:	7e 6b                	jle    3a57 <timer_thread+0x1a7>
    for (int y = 0 ; y < data->task_count ; y++) {
    39ec:	49 63 45 30          	movslq 0x30(%r13),%rax
    39f0:	85 c0                	test   %eax,%eax
    39f2:	7e 63                	jle    3a57 <timer_thread+0x1a7>
    39f4:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    39f8:	4d 8b 45 10          	mov    0x10(%r13),%r8
    39fc:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3a04:	31 ff                	xor    %edi,%edi
    3a06:	48 89 c2             	mov    %rax,%rdx
    3a09:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3a0d:	48 8b 40 28          	mov    0x28(%rax),%rax
    3a11:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3a15:	f6 c6 02             	test   $0x2,%dh
    3a18:	74 15                	je     3a2f <timer_thread+0x17f>
    3a1a:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3a24:	48 05 00 02 00 00    	add    $0x200,%rax
    3a2a:	48 39 c6             	cmp    %rax,%rsi
    3a2d:	74 1f                	je     3a4e <timer_thread+0x19e>
      data->threads[x]->tasks[y].sending = 0;
    3a2f:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3a39:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3a3f:	c7 80 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3a49:	48 39 c6             	cmp    %rax,%rsi
    3a4c:	75 e1                	jne    3a2f <timer_thread+0x17f>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3a4e:	48 83 c7 08          	add    $0x8,%rdi
    3a52:	48 39 f9             	cmp    %rdi,%rcx
    3a55:	75 b2                	jne    3a09 <timer_thread+0x159>
  asm volatile ("mfence" ::: "memory");
    3a57:	0f ae f0             	mfence
  struct timespec drain = {
    3a5a:	66 0f 6f 05 2e 3f 00 00 	movdqa 0x3f2e(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    3a62:	4c 8d 25 f4 35 00 00 	lea    0x35f4(%rip),%r12        # 705d <_IO_stdin_used+0x5d>
    3a69:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
    y++;
    3a6d:	8b 9d 7c ff ff ff    	mov    -0x84(%rbp),%ebx
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a73:	49 63 45 18          	movslq 0x18(%r13),%rax
    y++;
    3a77:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a7a:	85 c0                	test   %eax,%eax
    3a7c:	7e 4e                	jle    3acc <timer_thread+0x21c>
        data->threads[x]->tasks[y].scheduled = 0;
    3a7e:	4c 63 85 7c ff ff ff 	movslq -0x84(%rbp),%r8
    3a85:	49 8b 4d 10          	mov    0x10(%r13),%rcx
    3a89:	49 c1 e0 09          	shl    $0x9,%r8
    3a8d:	4c 8d 14 c1          	lea    (%rcx,%rax,8),%r10
    3a91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3a98:	48 8b 19             	mov    (%rcx),%rbx
    3a9b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a9d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3aa1:	99                   	cltd
    3aa2:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3aa5:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3aa9:	48 63 d2             	movslq %edx,%rdx
    3aac:	48 c1 e2 09          	shl    $0x9,%rdx
    3ab0:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3abb:	42 c7 84 06 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ac7:	4c 39 d1             	cmp    %r10,%rcx
    3aca:	75 cc                	jne    3a98 <timer_thread+0x1e8>
    asm volatile ("mfence" ::: "memory");
    3acc:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3acf:	49 8b 45 10          	mov    0x10(%r13),%rax
    3ad3:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3ad6:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3ad9:	ba 00 00 00 00       	mov    $0x0,%edx
    3ade:	0f 4f d7             	cmovg  %edi,%edx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3ae1:	41 8b 7d 20          	mov    0x20(%r13),%edi
    y++;
    3ae5:	89 95 7c ff ff ff    	mov    %edx,-0x84(%rbp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3aeb:	85 ff                	test   %edi,%edi
    3aed:	0f 8e bb 00 00 00    	jle    3bae <timer_thread+0x2fe>
    3af3:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    3af6:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    3afc:	0f 1f 40 00          	nopl   0x0(%rax)
    3b00:	4a 8d 1c f5 00 00 00 00 	lea    0x0(,%r14,8),%rbx
            all_empty = 0;
    3b08:	45 31 ff             	xor    %r15d,%r15d
    3b0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3b10:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3b14:	4c 89 f8             	mov    %r15,%rax
    3b17:	48 c1 e0 09          	shl    $0x9,%rax
    3b1b:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3b1f:	31 d2                	xor    %edx,%edx
    3b21:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3b28:	eb 16                	jmp    3b40 <timer_thread+0x290>
    3b2a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3b30:	4d 85 c0             	test   %r8,%r8
    3b33:	7f 1f                	jg     3b54 <timer_thread+0x2a4>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3b35:	83 c2 01             	add    $0x1,%edx
    3b38:	48 83 c0 20          	add    $0x20,%rax
    3b3c:	39 fa                	cmp    %edi,%edx
    3b3e:	74 2a                	je     3b6a <timer_thread+0x2ba>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3b40:	48 8b 08             	mov    (%rax),%rcx
    3b43:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3b47:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3b4b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3b4f:	48 85 c9             	test   %rcx,%rcx
    3b52:	7e dc                	jle    3b30 <timer_thread+0x280>
    3b54:	bf 01 00 00 00       	mov    $0x1,%edi
    3b59:	4c 89 e6             	mov    %r12,%rsi
    3b5c:	31 c0                	xor    %eax,%eax
    3b5e:	e8 1d e9 ff ff       	call   2480 <__printf_chk@plt>
            break;
    3b63:	41 8b 7d 20          	mov    0x20(%r13),%edi
            all_empty = 0;
    3b67:	45 31 d2             	xor    %r10d,%r10d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3b6a:	49 83 c7 01          	add    $0x1,%r15
    3b6e:	44 39 ff             	cmp    %r15d,%edi
    3b71:	7e 0d                	jle    3b80 <timer_thread+0x2d0>
    3b73:	49 8b 45 10          	mov    0x10(%r13),%rax
    3b77:	eb 97                	jmp    3b10 <timer_thread+0x260>
    3b79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3b80:	49 83 c6 01          	add    $0x1,%r14
    3b84:	44 39 f7             	cmp    %r14d,%edi
    3b87:	7e 0d                	jle    3b96 <timer_thread+0x2e6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3b89:	85 ff                	test   %edi,%edi
    3b8b:	7e 09                	jle    3b96 <timer_thread+0x2e6>
    3b8d:	49 8b 45 10          	mov    0x10(%r13),%rax
    3b91:	e9 6a ff ff ff       	jmp    3b00 <timer_thread+0x250>
    if (all_empty == 1) {
    3b96:	41 83 fa 01          	cmp    $0x1,%r10d
    3b9a:	74 12                	je     3bae <timer_thread+0x2fe>
      nanosleep(&drain , &drainrem);
    3b9c:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    3ba0:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
    3ba4:	e8 c7 e7 ff ff       	call   2370 <nanosleep@plt>
    3ba9:	e9 bf fe ff ff       	jmp    3a6d <timer_thread+0x1bd>
    3bae:	48 8d 3d 9f 34 00 00 	lea    0x349f(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3bb5:	e8 56 e7 ff ff       	call   2310 <puts@plt>
  while (data->running) {
    3bba:	41 8b 45 34          	mov    0x34(%r13),%eax
    3bbe:	85 c0                	test   %eax,%eax
    3bc0:	0f 84 d1 00 00 00    	je     3c97 <timer_thread+0x3e7>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3bc6:	41 8b 4d 1c          	mov    0x1c(%r13),%ecx
    3bca:	85 c9                	test   %ecx,%ecx
    3bcc:	7e 2f                	jle    3bfd <timer_thread+0x34d>
    3bce:	49 8b 45 10          	mov    0x10(%r13),%rax
    3bd2:	31 db                	xor    %ebx,%ebx
    3bd4:	4c 8d 25 93 34 00 00 	lea    0x3493(%rip),%r12        # 706e <_IO_stdin_used+0x6e>
    3bdb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->threads[x]->running = 0;
    3be0:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3be4:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3be8:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3bef:	0f 84 ce 00 00 00    	je     3cc3 <timer_thread+0x413>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3bf5:	48 83 c3 01          	add    $0x1,%rbx
    3bf9:	39 d9                	cmp    %ebx,%ecx
    3bfb:	7f e3                	jg     3be0 <timer_thread+0x330>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bfd:	49 63 55 18          	movslq 0x18(%r13),%rdx
    3c01:	85 d2                	test   %edx,%edx
    3c03:	7e 7b                	jle    3c80 <timer_thread+0x3d0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3c05:	49 63 45 30          	movslq 0x30(%r13),%rax
    3c09:	85 c0                	test   %eax,%eax
    3c0b:	7e 73                	jle    3c80 <timer_thread+0x3d0>
    3c0d:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3c11:	4d 8b 45 10          	mov    0x10(%r13),%r8
    3c15:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3c1d:	31 c9                	xor    %ecx,%ecx
    3c1f:	48 89 c6             	mov    %rax,%rsi
    3c22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c28:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3c2c:	48 8b 40 28          	mov    0x28(%rax),%rax
    3c30:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3c34:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3c3a:	74 1c                	je     3c58 <timer_thread+0x3a8>
    3c3c:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3c46:	48 05 00 02 00 00    	add    $0x200,%rax
    3c4c:	48 39 d0             	cmp    %rdx,%rax
    3c4f:	74 26                	je     3c77 <timer_thread+0x3c7>
    3c51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3c58:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3c62:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3c68:	c7 80 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3c72:	48 39 d0             	cmp    %rdx,%rax
    3c75:	75 e1                	jne    3c58 <timer_thread+0x3a8>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c77:	48 83 c1 08          	add    $0x8,%rcx
    3c7b:	48 39 f9             	cmp    %rdi,%rcx
    3c7e:	75 a8                	jne    3c28 <timer_thread+0x378>
    asm volatile ("mfence" ::: "memory");
    3c80:	0f ae f0             	mfence
    3c83:	48 8d 3d f6 33 00 00 	lea    0x33f6(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3c8a:	e8 81 e6 ff ff       	call   2310 <puts@plt>
    data->running = 0;
    3c8f:	41 c7 45 34 00 00 00 00 	movl   $0x0,0x34(%r13)
    3c97:	48 8d 3d e9 33 00 00 	lea    0x33e9(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3c9e:	e8 6d e6 ff ff       	call   2310 <puts@plt>
}
    3ca3:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    3ca7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3cb0:	75 47                	jne    3cf9 <timer_thread+0x449>
    3cb2:	48 83 c4 68          	add    $0x68,%rsp
    3cb6:	31 c0                	xor    %eax,%eax
    3cb8:	5b                   	pop    %rbx
    3cb9:	41 5c                	pop    %r12
    3cbb:	41 5d                	pop    %r13
    3cbd:	41 5e                	pop    %r14
    3cbf:	41 5f                	pop    %r15
    3cc1:	5d                   	pop    %rbp
    3cc2:	c3                   	ret
    3cc3:	4c 89 e7             	mov    %r12,%rdi
    3cc6:	e8 45 e6 ff ff       	call   2310 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3ccb:	49 8b 45 10          	mov    0x10(%r13),%rax
    3ccf:	be 01 00 00 00       	mov    $0x1,%esi
    3cd4:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3cd8:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3cdc:	8b 78 50             	mov    0x50(%rax),%edi
    3cdf:	e8 4c e7 ff ff       	call   2430 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ce4:	41 8b 4d 1c          	mov    0x1c(%r13),%ecx
    3ce8:	39 d9                	cmp    %ebx,%ecx
    3cea:	0f 8e 0d ff ff ff    	jle    3bfd <timer_thread+0x34d>
    3cf0:	49 8b 45 10          	mov    0x10(%r13),%rax
    3cf4:	e9 e7 fe ff ff       	jmp    3be0 <timer_thread+0x330>
}
    3cf9:	e8 52 e6 ff ff       	call   2350 <__stack_chk_fail@plt>
    3cfe:	66 90                	xchg   %ax,%ax

0000000000003d00 <strtolower>:
void strtolower(char *str) {
    3d00:	f3 0f 1e fa          	endbr64
    3d04:	55                   	push   %rbp
    3d05:	48 89 e5             	mov    %rsp,%rbp
    3d08:	41 54                	push   %r12
    3d0a:	53                   	push   %rbx
    3d0b:	ff 15 d7 62 00 00    	call   *0x62d7(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    for (; *str; ++str)
    3d11:	48 0f be 1f          	movsbq (%rdi),%rbx
void strtolower(char *str) {
    3d15:	49 89 fc             	mov    %rdi,%r12
    for (; *str; ++str)
    3d18:	84 db                	test   %bl,%bl
    3d1a:	74 24                	je     3d40 <strtolower+0x40>
        *str = (char)tolower(*str);
    3d1c:	e8 2f e8 ff ff       	call   2550 <__ctype_tolower_loc@plt>
    3d21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3d28:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3d2b:	49 83 c4 01          	add    $0x1,%r12
        *str = (char)tolower(*str);
    3d2f:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3d32:	41 88 54 24 ff       	mov    %dl,-0x1(%r12)
    for (; *str; ++str)
    3d37:	49 0f be 1c 24       	movsbq (%r12),%rbx
    3d3c:	84 db                	test   %bl,%bl
    3d3e:	75 e8                	jne    3d28 <strtolower+0x28>
}
    3d40:	5b                   	pop    %rbx
    3d41:	41 5c                	pop    %r12
    3d43:	5d                   	pop    %rbp
    3d44:	c3                   	ret
    3d45:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003d50 <zh_malloc>:
void *zh_malloc(size_t size) {
    3d50:	f3 0f 1e fa          	endbr64
    3d54:	55                   	push   %rbp
    3d55:	48 89 e5             	mov    %rsp,%rbp
    3d58:	ff 15 8a 62 00 00    	call   *0x628a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    void *buf = malloc(size);
    3d5e:	e8 dd e6 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    3d63:	48 85 c0             	test   %rax,%rax
    3d66:	74 02                	je     3d6a <zh_malloc+0x1a>
}
    3d68:	5d                   	pop    %rbp
    3d69:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3d6a:	48 8b 0d af 62 00 00 	mov    0x62af(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    3d71:	ba 28 00 00 00       	mov    $0x28,%edx
    3d76:	be 01 00 00 00       	mov    $0x1,%esi
    3d7b:	48 8d 3d 86 36 00 00 	lea    0x3686(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    3d82:	e8 79 e7 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    3d87:	bf 01 00 00 00       	mov    $0x1,%edi
    3d8c:	e8 4f e7 ff ff       	call   24e0 <exit@plt>
    3d91:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3d9c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003da0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3da0:	f3 0f 1e fa          	endbr64
    3da4:	55                   	push   %rbp
    3da5:	48 89 e5             	mov    %rsp,%rbp
    3da8:	53                   	push   %rbx
    3da9:	48 83 ec 08          	sub    $0x8,%rsp
    3dad:	ff 15 35 62 00 00    	call   *0x6235(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    const char *dot = strrchr(filename, '.');
    3db3:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3db8:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3dbb:	e8 c0 e5 ff ff       	call   2380 <strrchr@plt>
    if (!dot || dot == filename)
    3dc0:	48 85 c0             	test   %rax,%rax
    3dc3:	74 13                	je     3dd8 <get_filename_ext+0x38>
    3dc5:	48 39 c3             	cmp    %rax,%rbx
    3dc8:	74 0e                	je     3dd8 <get_filename_ext+0x38>
}
    3dca:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    return dot + 1;
    3dce:	48 83 c0 01          	add    $0x1,%rax
}
    3dd2:	c9                   	leave
    3dd3:	c3                   	ret
    3dd4:	0f 1f 40 00          	nopl   0x0(%rax)
    3dd8:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
        return "";
    3ddc:	48 8d 05 ec 32 00 00 	lea    0x32ec(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    3de3:	c9                   	leave
    3de4:	c3                   	ret
    3de5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003df0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3df0:	f3 0f 1e fa          	endbr64
    3df4:	55                   	push   %rbp
    3df5:	48 89 e5             	mov    %rsp,%rbp
    3df8:	41 56                	push   %r14
    3dfa:	41 55                	push   %r13
    3dfc:	41 54                	push   %r12
    3dfe:	53                   	push   %rbx
    3dff:	48 81 ec 10 08 00 00 	sub    $0x810,%rsp
    3e06:	ff 15 dc 61 00 00    	call   *0x61dc(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    3e0c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3e15:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    3e19:	31 c0                	xor    %eax,%eax
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3e1b:	4c 8d ad d0 f7 ff ff 	lea    -0x830(%rbp),%r13
    3e22:	49 89 f6             	mov    %rsi,%r14
    3e25:	49 89 d4             	mov    %rdx,%r12
    3e28:	48 89 fe             	mov    %rdi,%rsi
    3e2b:	ba 00 04 00 00       	mov    $0x400,%edx
    3e30:	4c 89 ef             	mov    %r13,%rdi
    3e33:	e8 28 e6 ff ff       	call   2460 <__strcpy_chk@plt>
    for (; *str; ++str)
    3e38:	48 0f be 9d d0 f7 ff ff 	movsbq -0x830(%rbp),%rbx
    3e40:	84 db                	test   %bl,%bl
    3e42:	74 1e                	je     3e62 <send_headers+0x72>
        *str = (char)tolower(*str);
    3e44:	e8 07 e7 ff ff       	call   2550 <__ctype_tolower_loc@plt>
    3e49:	48 8b 08             	mov    (%rax),%rcx
    3e4c:	4c 89 e8             	mov    %r13,%rax
    3e4f:	90                   	nop
    3e50:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3e53:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3e57:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3e5a:	48 0f be 18          	movsbq (%rax),%rbx
    3e5e:	84 db                	test   %bl,%bl
    3e60:	75 ee                	jne    3e50 <send_headers+0x60>
    void *buf = malloc(size);
    3e62:	bf 11 00 00 00       	mov    $0x11,%edi
    3e67:	e8 d4 e5 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    3e6c:	48 85 c0             	test   %rax,%rax
    3e6f:	0f 84 72 04 00 00    	je     42e7 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3e75:	66 0f 6f 05 23 3b 00 00 	movdqa 0x3b23(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    iov[0].iov_base = zh_malloc(slen);
    3e7d:	49 89 04 24          	mov    %rax,(%r12)
    void *buf = malloc(size);
    3e81:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3e86:	49 c7 44 24 08 11 00 00 00 	movq   $0x11,0x8(%r12)
    3e8f:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3e93:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3e96:	e8 a5 e5 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    3e9b:	48 85 c0             	test   %rax,%rax
    3e9e:	0f 84 43 04 00 00    	je     42e7 <send_headers+0x4f7>
    3ea4:	66 0f 6f 05 04 3b 00 00 	movdqa 0x3b04(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    iov[1].iov_base = zh_malloc(slen);
    3eac:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    const char *dot = strrchr(filename, '.');
    3eb1:	4c 89 ef             	mov    %r13,%rdi
    3eb4:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3ebe:	49 c7 44 24 18 17 00 00 00 	movq   $0x17,0x18(%r12)
    3ec7:	0f 11 00             	movups %xmm0,(%rax)
    3eca:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3ece:	be 2e 00 00 00       	mov    $0x2e,%esi
    3ed3:	e8 a8 e4 ff ff       	call   2380 <strrchr@plt>
    if (!dot || dot == filename)
    3ed8:	48 85 c0             	test   %rax,%rax
    3edb:	0f 84 df 02 00 00    	je     41c0 <send_headers+0x3d0>
    3ee1:	4c 39 e8             	cmp    %r13,%rax
    3ee4:	0f 84 d6 02 00 00    	je     41c0 <send_headers+0x3d0>
    return dot + 1;
    3eea:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3eee:	48 8d 3d a8 31 00 00 	lea    0x31a8(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    3ef5:	48 89 de             	mov    %rbx,%rsi
    3ef8:	e8 d3 e4 ff ff       	call   23d0 <strcmp@plt>
    3efd:	85 c0                	test   %eax,%eax
    3eff:	75 1e                	jne    3f1f <send_headers+0x12f>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3f01:	66 0f 6f 05 b7 3a 00 00 	movdqa 0x3ab7(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    3f09:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    3f10:	66 0f 6f 05 b8 3a 00 00 	movdqa 0x3ab8(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    3f18:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("jpeg", file_ext) == 0)
    3f1f:	48 89 de             	mov    %rbx,%rsi
    3f22:	48 8d 3d 78 31 00 00 	lea    0x3178(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    3f29:	e8 a2 e4 ff ff       	call   23d0 <strcmp@plt>
    3f2e:	85 c0                	test   %eax,%eax
    3f30:	75 1e                	jne    3f50 <send_headers+0x160>
    3f32:	66 0f 6f 05 86 3a 00 00 	movdqa 0x3a86(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    3f3a:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    3f41:	66 0f 6f 05 87 3a 00 00 	movdqa 0x3a87(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    3f49:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("png", file_ext) == 0)
    3f50:	48 89 de             	mov    %rbx,%rsi
    3f53:	48 8d 3d 4c 31 00 00 	lea    0x314c(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    3f5a:	e8 71 e4 ff ff       	call   23d0 <strcmp@plt>
    3f5f:	85 c0                	test   %eax,%eax
    3f61:	0f 84 09 02 00 00    	je     4170 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    3f67:	48 89 de             	mov    %rbx,%rsi
    3f6a:	48 8d 3d 39 31 00 00 	lea    0x3139(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    3f71:	e8 5a e4 ff ff       	call   23d0 <strcmp@plt>
    3f76:	85 c0                	test   %eax,%eax
    3f78:	0f 84 a2 02 00 00    	je     4220 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    3f7e:	48 89 de             	mov    %rbx,%rsi
    3f81:	48 8d 3d 26 31 00 00 	lea    0x3126(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    3f88:	e8 43 e4 ff ff       	call   23d0 <strcmp@plt>
    3f8d:	85 c0                	test   %eax,%eax
    3f8f:	0f 84 63 02 00 00    	je     41f8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    3f95:	48 89 de             	mov    %rbx,%rsi
    3f98:	48 8d 3d 52 31 00 00 	lea    0x3152(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    3f9f:	e8 2c e4 ff ff       	call   23d0 <strcmp@plt>
    3fa4:	85 c0                	test   %eax,%eax
    3fa6:	0f 84 24 02 00 00    	je     41d0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    3fac:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3faf:	0f 84 53 01 00 00    	je     4108 <send_headers+0x318>
    if (strcmp("css", file_ext) == 0)
    3fb5:	48 89 de             	mov    %rbx,%rsi
    3fb8:	48 8d 3d f3 30 00 00 	lea    0x30f3(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    3fbf:	e8 0c e4 ff ff       	call   23d0 <strcmp@plt>
    3fc4:	85 c0                	test   %eax,%eax
    3fc6:	0f 84 a4 02 00 00    	je     4270 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    3fcc:	48 89 de             	mov    %rbx,%rsi
    3fcf:	48 8d 3d e0 30 00 00 	lea    0x30e0(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    3fd6:	e8 f5 e3 ff ff       	call   23d0 <strcmp@plt>
    3fdb:	85 c0                	test   %eax,%eax
    3fdd:	0f 84 65 02 00 00    	je     4248 <send_headers+0x458>
    slen = strlen(send_buffer);
    3fe3:	4c 8d ad d0 fb ff ff 	lea    -0x430(%rbp),%r13
    3fea:	4c 89 ef             	mov    %r13,%rdi
    3fed:	e8 4e e3 ff ff       	call   2340 <strlen@plt>
    void *buf = malloc(size);
    3ff2:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3ff5:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3ff8:	e8 43 e4 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    3ffd:	48 85 c0             	test   %rax,%rax
    4000:	0f 84 e1 02 00 00    	je     42e7 <send_headers+0x4f7>
    iov[2].iov_base = zh_malloc(slen);
    4006:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    iov[2].iov_len = slen;
    400b:	49 89 5c 24 28       	mov    %rbx,0x28(%r12)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4010:	83 fb 08             	cmp    $0x8,%ebx
    4013:	0f 83 37 01 00 00    	jae    4150 <send_headers+0x360>
    4019:	f6 c3 04             	test   $0x4,%bl
    401c:	0f 85 71 02 00 00    	jne    4293 <send_headers+0x4a3>
    4022:	85 db                	test   %ebx,%ebx
    4024:	74 12                	je     4038 <send_headers+0x248>
    4026:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    402d:	88 10                	mov    %dl,(%rax)
    402f:	f6 c3 02             	test   $0x2,%bl
    4032:	0f 85 8b 02 00 00    	jne    42c3 <send_headers+0x4d3>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4038:	4d 89 f0             	mov    %r14,%r8
    403b:	48 8d 0d 78 30 00 00 	lea    0x3078(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    4042:	4c 89 ef             	mov    %r13,%rdi
    4045:	31 c0                	xor    %eax,%eax
    4047:	ba 00 04 00 00       	mov    $0x400,%edx
    404c:	be 01 00 00 00       	mov    $0x1,%esi
    4051:	e8 0a e5 ff ff       	call   2560 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4056:	4c 89 ef             	mov    %r13,%rdi
    4059:	e8 e2 e2 ff ff       	call   2340 <strlen@plt>
    void *buf = malloc(size);
    405e:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4061:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4064:	e8 d7 e3 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    4069:	48 85 c0             	test   %rax,%rax
    406c:	0f 84 75 02 00 00    	je     42e7 <send_headers+0x4f7>
    iov[3].iov_base = zh_malloc(slen);
    4072:	49 89 44 24 30       	mov    %rax,0x30(%r12)
    iov[3].iov_len = slen;
    4077:	49 89 5c 24 38       	mov    %rbx,0x38(%r12)
    407c:	83 fb 08             	cmp    $0x8,%ebx
    407f:	0f 83 13 01 00 00    	jae    4198 <send_headers+0x3a8>
    4085:	f6 c3 04             	test   $0x4,%bl
    4088:	0f 85 1d 02 00 00    	jne    42ab <send_headers+0x4bb>
    408e:	85 db                	test   %ebx,%ebx
    4090:	74 12                	je     40a4 <send_headers+0x2b4>
    4092:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    4099:	88 10                	mov    %dl,(%rax)
    409b:	f6 c3 02             	test   $0x2,%bl
    409e:	0f 85 31 02 00 00    	jne    42d5 <send_headers+0x4e5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40a4:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    40a9:	bf 02 00 00 00       	mov    $0x2,%edi
    40ae:	c6 85 d2 fb ff ff 00 	movb   $0x0,-0x42e(%rbp)
    40b5:	66 89 85 d0 fb ff ff 	mov    %ax,-0x430(%rbp)
    40bc:	e8 7f e3 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    40c1:	48 85 c0             	test   %rax,%rax
    40c4:	0f 84 1d 02 00 00    	je     42e7 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    40ca:	0f b7 95 d0 fb ff ff 	movzwl -0x430(%rbp),%edx
    iov[4].iov_base = zh_malloc(slen);
    40d1:	49 89 44 24 40       	mov    %rax,0x40(%r12)
    iov[4].iov_len = slen;
    40d6:	49 c7 44 24 48 02 00 00 00 	movq   $0x2,0x48(%r12)
    40df:	66 89 10             	mov    %dx,(%rax)
}
    40e2:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    40e6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    40ef:	0f 85 19 02 00 00    	jne    430e <send_headers+0x51e>
    40f5:	48 81 c4 10 08 00 00 	add    $0x810,%rsp
    40fc:	5b                   	pop    %rbx
    40fd:	41 5c                	pop    %r12
    40ff:	41 5d                	pop    %r13
    4101:	41 5e                	pop    %r14
    4103:	5d                   	pop    %rbp
    4104:	c3                   	ret
    4105:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
    4108:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    410c:	0f 85 a3 fe ff ff    	jne    3fb5 <send_headers+0x1c5>
    4112:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4116:	0f 85 99 fe ff ff    	jne    3fb5 <send_headers+0x1c5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    411c:	66 0f 6f 05 fc 38 00 00 	movdqa 0x38fc(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    4124:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    412e:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4135:	66 0f 6f 05 f3 38 00 00 	movdqa 0x38f3(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
    413d:	0f 29 85 e0 fb ff ff 	movaps %xmm0,-0x420(%rbp)
    4144:	48 89 85 ef fb ff ff 	mov    %rax,-0x411(%rbp)
    414b:	e9 65 fe ff ff       	jmp    3fb5 <send_headers+0x1c5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4150:	89 da                	mov    %ebx,%edx
    4152:	48 89 c7             	mov    %rax,%rdi
    4155:	4c 89 ee             	mov    %r13,%rsi
    4158:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    415d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4162:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4165:	c1 e9 03             	shr    $0x3,%ecx
    4168:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    416b:	e9 c8 fe ff ff       	jmp    4038 <send_headers+0x248>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4170:	66 0f 6f 05 48 38 00 00 	movdqa 0x3848(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4178:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    417f:	66 0f 6f 05 59 38 00 00 	movdqa 0x3859(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    4187:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    418e:	e9 d4 fd ff ff       	jmp    3f67 <send_headers+0x177>
    4193:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4198:	89 da                	mov    %ebx,%edx
    419a:	48 89 c7             	mov    %rax,%rdi
    419d:	4c 89 ee             	mov    %r13,%rsi
    41a0:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    41a5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    41aa:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    41ad:	c1 e9 03             	shr    $0x3,%ecx
    41b0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    41b3:	e9 ec fe ff ff       	jmp    40a4 <send_headers+0x2b4>
    41b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    41c0:	48 8d 1d 08 2f 00 00 	lea    0x2f08(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    41c7:	e9 9b fd ff ff       	jmp    3f67 <send_headers+0x177>
    41cc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    41d0:	66 0f 6f 05 28 38 00 00 	movdqa 0x3828(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    41d8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    41df:	66 0f 6f 05 29 38 00 00 	movdqa 0x3829(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    41e7:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    41ee:	e9 b9 fd ff ff       	jmp    3fac <send_headers+0x1bc>
    41f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    41f8:	66 0f 6f 05 00 38 00 00 	movdqa 0x3800(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4200:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4207:	66 0f 6f 05 01 38 00 00 	movdqa 0x3801(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    420f:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    4216:	e9 7a fd ff ff       	jmp    3f95 <send_headers+0x1a5>
    421b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4220:	66 0f 6f 05 98 37 00 00 	movdqa 0x3798(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4228:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    422f:	66 0f 6f 05 b9 37 00 00 	movdqa 0x37b9(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    4237:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    423e:	e9 3b fd ff ff       	jmp    3f7e <send_headers+0x18e>
    4243:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4248:	66 0f 6f 05 b0 37 00 00 	movdqa 0x37b0(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4250:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4257:	66 0f 6f 05 f1 37 00 00 	movdqa 0x37f1(%rip),%xmm0        # 7a50 <_IO_stdin_used+0xa50>
    425f:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    4266:	e9 78 fd ff ff       	jmp    3fe3 <send_headers+0x1f3>
    426b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4270:	66 0f 6f 05 88 37 00 00 	movdqa 0x3788(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4278:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    427f:	66 0f 6f 05 b9 37 00 00 	movdqa 0x37b9(%rip),%xmm0        # 7a40 <_IO_stdin_used+0xa40>
    4287:	0f 11 85 d9 fb ff ff 	movups %xmm0,-0x427(%rbp)
    428e:	e9 39 fd ff ff       	jmp    3fcc <send_headers+0x1dc>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4293:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    4299:	89 db                	mov    %ebx,%ebx
    429b:	89 10                	mov    %edx,(%rax)
    429d:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    42a2:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    42a6:	e9 8d fd ff ff       	jmp    4038 <send_headers+0x248>
    42ab:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    42b1:	89 db                	mov    %ebx,%ebx
    42b3:	89 10                	mov    %edx,(%rax)
    42b5:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    42ba:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    42be:	e9 e1 fd ff ff       	jmp    40a4 <send_headers+0x2b4>
    42c3:	89 db                	mov    %ebx,%ebx
    42c5:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    42cb:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    42d0:	e9 63 fd ff ff       	jmp    4038 <send_headers+0x248>
    42d5:	89 db                	mov    %ebx,%ebx
    42d7:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    42dd:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    42e2:	e9 bd fd ff ff       	jmp    40a4 <send_headers+0x2b4>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    42e7:	48 8b 0d 32 5d 00 00 	mov    0x5d32(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    42ee:	ba 28 00 00 00       	mov    $0x28,%edx
    42f3:	be 01 00 00 00       	mov    $0x1,%esi
    42f8:	48 8d 3d 09 31 00 00 	lea    0x3109(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    42ff:	e8 fc e1 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    4304:	bf 01 00 00 00       	mov    $0x1,%edi
    4309:	e8 d2 e1 ff ff       	call   24e0 <exit@plt>
}
    430e:	e8 3d e0 ff ff       	call   2350 <__stack_chk_fail@plt>
    4313:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    431e:	66 90                	xchg   %ax,%ax

0000000000004320 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4320:	f3 0f 1e fa          	endbr64
    4324:	55                   	push   %rbp
    4325:	48 89 e5             	mov    %rsp,%rbp
    4328:	41 56                	push   %r14
    432a:	41 55                	push   %r13
    432c:	41 54                	push   %r12
    432e:	53                   	push   %rbx
    432f:	ff 15 b3 5c 00 00    	call   *0x5cb3(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    4335:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    4338:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    433b:	48 89 f3             	mov    %rsi,%rbx
    433e:	49 89 d6             	mov    %rdx,%r14
    void *buf = malloc(size);
    4341:	e8 fa e0 ff ff       	call   2440 <malloc@plt>
    4346:	49 89 c4             	mov    %rax,%r12
    if (!buf) {
    4349:	48 85 c0             	test   %rax,%rax
    434c:	74 69                	je     43b7 <copy_file_contents+0x97>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    434e:	4c 89 ef             	mov    %r13,%rdi
    4351:	31 f6                	xor    %esi,%esi
    4353:	31 c0                	xor    %eax,%eax
    4355:	e8 56 e1 ff ff       	call   24b0 <open@plt>
    435a:	41 89 c5             	mov    %eax,%r13d
    if (fd < 0)
    435d:	85 c0                	test   %eax,%eax
    435f:	0f 88 38 e2 ff ff    	js     259d <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4365:	48 89 da             	mov    %rbx,%rdx
    4368:	4c 89 e6             	mov    %r12,%rsi
    436b:	89 c7                	mov    %eax,%edi
    436d:	e8 3e e0 ff ff       	call   23b0 <read@plt>
    if (ret < file_size) {
    4372:	48 98                	cltq
    4374:	48 39 d8             	cmp    %rbx,%rax
    4377:	7c 1f                	jl     4398 <copy_file_contents+0x78>
    close(fd);
    4379:	44 89 ef             	mov    %r13d,%edi
    437c:	e8 0f e0 ff ff       	call   2390 <close@plt>
    iov->iov_base = buf;
    4381:	4d 89 26             	mov    %r12,(%r14)
    iov->iov_len = file_size;
    4384:	49 89 5e 08          	mov    %rbx,0x8(%r14)
}
    4388:	5b                   	pop    %rbx
    4389:	41 5c                	pop    %r12
    438b:	41 5d                	pop    %r13
    438d:	41 5e                	pop    %r14
    438f:	5d                   	pop    %rbp
    4390:	c3                   	ret
    4391:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4398:	48 8b 0d 81 5c 00 00 	mov    0x5c81(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    439f:	ba 1a 00 00 00       	mov    $0x1a,%edx
    43a4:	be 01 00 00 00       	mov    $0x1,%esi
    43a9:	48 8d 3d 20 2d 00 00 	lea    0x2d20(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    43b0:	e8 4b e1 ff ff       	call   2500 <fwrite@plt>
    43b5:	eb c2                	jmp    4379 <copy_file_contents+0x59>
    43b7:	48 8b 0d 62 5c 00 00 	mov    0x5c62(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    43be:	ba 28 00 00 00       	mov    $0x28,%edx
    43c3:	be 01 00 00 00       	mov    $0x1,%esi
    43c8:	48 8d 3d 39 30 00 00 	lea    0x3039(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    43cf:	e8 2c e1 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    43d4:	bf 01 00 00 00       	mov    $0x1,%edi
    43d9:	e8 02 e1 ff ff       	call   24e0 <exit@plt>
    43de:	66 90                	xchg   %ax,%ax

00000000000043e0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    43e0:	f3 0f 1e fa          	endbr64
    43e4:	55                   	push   %rbp
    43e5:	48 89 e5             	mov    %rsp,%rbp
    43e8:	ff 15 fa 5b 00 00    	call   *0x5bfa(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    43ee:	8b 46 44             	mov    0x44(%rsi),%eax
    43f1:	48 89 fa             	mov    %rdi,%rdx
    43f4:	48 89 f7             	mov    %rsi,%rdi
    43f7:	8d 70 01             	lea    0x1(%rax),%esi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    43fa:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4400:	48 8b 07             	mov    (%rdi),%rax
    4403:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4406:	f6 c1 02             	test   $0x2,%cl
    4409:	74 00                	je     440b <add_write_request+0x2b>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    440b:	89 f0                	mov    %esi,%eax
    440d:	44 29 c0             	sub    %r8d,%eax
    4410:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4413:	0f 82 90 e1 ff ff    	jb     25a9 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4419:	c1 e9 0a             	shr    $0xa,%ecx
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    441c:	8b 47 44             	mov    0x44(%rdi),%eax
    441f:	23 47 58             	and    0x58(%rdi),%eax
		sq->sqe_tail = next;
    4422:	89 77 44             	mov    %esi,0x44(%rdi)
	if (ring->flags & IORING_SETUP_SQE128)
    4425:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4428:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    442b:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    442f:	d3 e0                	shl    %cl,%eax
    4431:	8b 4a 04             	mov    0x4(%rdx),%ecx
    4434:	48 c1 e0 06          	shl    $0x6,%rax
    4438:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    443c:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    4442:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4445:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4449:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    444f:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4457:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    445b:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    445e:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4465:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    446d:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    4471:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    4475:	e8 e6 de ff ff       	call   2360 <io_uring_submit@plt>
}
    447a:	31 c0                	xor    %eax,%eax
    447c:	5d                   	pop    %rbp
    447d:	c3                   	ret
    447e:	66 90                	xchg   %ax,%ax

0000000000004480 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4480:	f3 0f 1e fa          	endbr64
    4484:	55                   	push   %rbp
    4485:	48 89 e5             	mov    %rsp,%rbp
    4488:	41 56                	push   %r14
    448a:	41 55                	push   %r13
    448c:	41 54                	push   %r12
    448e:	53                   	push   %rbx
    448f:	ff 15 53 5b 00 00    	call   *0x5b53(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    4495:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4498:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    449e:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    44a1:	83 c0 01             	add    $0x1,%eax
    44a4:	48 89 f3             	mov    %rsi,%rbx
    44a7:	41 89 fe             	mov    %edi,%r14d
		head = IO_URING_READ_ONCE(*sq->khead);
    44aa:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    44ac:	f6 c1 02             	test   $0x2,%cl
    44af:	74 00                	je     44b1 <add_read_request+0x31>
	if (next - head <= sq->ring_entries) {
    44b1:	89 c2                	mov    %eax,%edx
    44b3:	29 f2                	sub    %esi,%edx
    44b5:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    44b8:	0f 82 fb e0 ff ff    	jb     25b9 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    44be:	44 8b 63 44          	mov    0x44(%rbx),%r12d
	if (ring->flags & IORING_SETUP_SQE128)
    44c2:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    44c5:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    44c8:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    44cd:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    44d0:	44 23 63 58          	and    0x58(%rbx),%r12d
    44d4:	41 d3 e4             	shl    %cl,%r12d
    44d7:	49 c1 e4 06          	shl    $0x6,%r12
    44db:	4c 03 63 38          	add    0x38(%rbx),%r12
    44df:	e8 5c df ff ff       	call   2440 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    44e4:	be 01 00 00 00       	mov    $0x1,%esi
    44e9:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    44ee:	49 89 c5             	mov    %rax,%r13
    req->iov[0].iov_base = malloc(READ_SZ);
    44f1:	e8 ca de ff ff       	call   23c0 <calloc@plt>
    req->client_socket = client_socket;
    44f6:	45 89 75 08          	mov    %r14d,0x8(%r13)
	sqe->addr3 = 0;
    44fa:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    44fe:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4501:	49 89 45 10          	mov    %rax,0x10(%r13)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4505:	49 8d 45 10          	lea    0x10(%r13),%rax
    req->iov[0].iov_len = READ_SZ;
    4509:	49 c7 45 18 00 20 00 00 	movq   $0x2000,0x18(%r13)
    req->event_type = EVENT_TYPE_READ;
    4511:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
	sqe->fd = fd;
    4519:	45 89 74 24 04       	mov    %r14d,0x4(%r12)
	sqe->user_data = (unsigned long) data;
    451e:	4d 89 6c 24 20       	mov    %r13,0x20(%r12)
	sqe->opcode = (__u8) op;
    4523:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->off = offset;
    452b:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4534:	49 89 44 24 10       	mov    %rax,0x10(%r12)
	sqe->len = len;
    4539:	49 c7 44 24 18 01 00 00 00 	movq   $0x1,0x18(%r12)
	sqe->buf_index = 0;
    4542:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->addr3 = 0;
    454b:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    io_uring_submit(ring);
    4551:	e8 0a de ff ff       	call   2360 <io_uring_submit@plt>
}
    4556:	5b                   	pop    %rbx
    4557:	31 c0                	xor    %eax,%eax
    4559:	41 5c                	pop    %r12
    455b:	41 5d                	pop    %r13
    455d:	41 5e                	pop    %r14
    455f:	5d                   	pop    %rbp
    4560:	c3                   	ret
    4561:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    456c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004570 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4570:	f3 0f 1e fa          	endbr64
    4574:	55                   	push   %rbp
    4575:	48 89 e5             	mov    %rsp,%rbp
    4578:	41 57                	push   %r15
    457a:	41 56                	push   %r14
    457c:	41 55                	push   %r13
    457e:	41 54                	push   %r12
    4580:	53                   	push   %rbx
    4581:	48 83 ec 08          	sub    $0x8,%rsp
    4585:	ff 15 5d 5a 00 00    	call   *0x5a5d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    458b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    458e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4593:	41 89 f7             	mov    %esi,%r15d
    4596:	49 89 d4             	mov    %rdx,%r12
    void *buf = malloc(size);
    4599:	e8 a2 de ff ff       	call   2440 <malloc@plt>
    459e:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    45a1:	48 85 c0             	test   %rax,%rax
    45a4:	0f 84 eb 00 00 00    	je     4695 <_send_static_string_content+0x125>
    unsigned long slen = strlen(str);
    45aa:	4c 89 ef             	mov    %r13,%rdi
    45ad:	e8 8e dd ff ff       	call   2340 <strlen@plt>
    req->iovec_count = 1;
    45b2:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    45b9:	44 89 7b 08          	mov    %r15d,0x8(%rbx)
    void *buf = malloc(size);
    45bd:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    45c0:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    45c3:	e8 78 de ff ff       	call   2440 <malloc@plt>
    45c8:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    45cb:	48 85 c0             	test   %rax,%rax
    45ce:	0f 84 c1 00 00 00    	je     4695 <_send_static_string_content+0x125>
    req->iov[0].iov_base = zh_malloc(slen);
    45d4:	48 89 43 10          	mov    %rax,0x10(%rbx)
    45d8:	4c 89 f2             	mov    %r14,%rdx
    45db:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    45de:	4c 89 73 18          	mov    %r14,0x18(%rbx)
    45e2:	e8 29 de ff ff       	call   2410 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    45e7:	41 8b 44 24 44       	mov    0x44(%r12),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    45ec:	41 8b 8c 24 c0 00 00 00 	mov    0xc0(%r12),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    45f4:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    45f7:	49 8b 04 24          	mov    (%r12),%rax
    45fb:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    45fd:	f6 c1 02             	test   $0x2,%cl
    4600:	0f 85 8a 00 00 00    	jne    4690 <_send_static_string_content+0x120>
	if (next - head <= sq->ring_entries) {
    4606:	89 d0                	mov    %edx,%eax
    4608:	29 f0                	sub    %esi,%eax
    460a:	41 39 44 24 5c       	cmp    %eax,0x5c(%r12)
    460f:	0f 82 ae df ff ff    	jb     25c3 <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4615:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4618:	41 8b 44 24 44       	mov    0x44(%r12),%eax
    461d:	41 23 44 24 58       	and    0x58(%r12),%eax
    io_uring_submit(ring);
    4622:	4c 89 e7             	mov    %r12,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    4625:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4628:	41 89 54 24 44       	mov    %edx,0x44(%r12)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    462d:	8b 53 04             	mov    0x4(%rbx),%edx
	sqe->addr3 = 0;
    4630:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4634:	d3 e0                	shl    %cl,%eax
    4636:	8b 4b 08             	mov    0x8(%rbx),%ecx
    req->event_type = EVENT_TYPE_WRITE;
    4639:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    463f:	48 c1 e0 06          	shl    $0x6,%rax
    4643:	49 03 44 24 38       	add    0x38(%r12),%rax
	sqe->fd = fd;
    4648:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    464b:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    464f:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4655:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    465d:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4661:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4664:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    466b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4673:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    4677:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    467b:	48 83 c4 08          	add    $0x8,%rsp
    467f:	5b                   	pop    %rbx
    4680:	41 5c                	pop    %r12
    4682:	41 5d                	pop    %r13
    4684:	41 5e                	pop    %r14
    4686:	41 5f                	pop    %r15
    4688:	5d                   	pop    %rbp
    io_uring_submit(ring);
    4689:	e9 d2 dc ff ff       	jmp    2360 <io_uring_submit@plt>
    468e:	66 90                	xchg   %ax,%ax
		head = io_uring_smp_load_acquire(sq->khead);
    4690:	e9 71 ff ff ff       	jmp    4606 <_send_static_string_content+0x96>
    4695:	48 8b 0d 84 59 00 00 	mov    0x5984(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    469c:	ba 28 00 00 00       	mov    $0x28,%edx
    46a1:	be 01 00 00 00       	mov    $0x1,%esi
    46a6:	48 8d 3d 5b 2d 00 00 	lea    0x2d5b(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    46ad:	e8 4e de ff ff       	call   2500 <fwrite@plt>
        exit(1);
    46b2:	bf 01 00 00 00       	mov    $0x1,%edi
    46b7:	e8 24 de ff ff       	call   24e0 <exit@plt>
    46bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000046c0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    46c0:	f3 0f 1e fa          	endbr64
    46c4:	55                   	push   %rbp
    46c5:	48 89 e5             	mov    %rsp,%rbp
    46c8:	ff 15 1a 59 00 00    	call   *0x591a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
}
    46ce:	5d                   	pop    %rbp
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    46cf:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    46d2:	89 fe                	mov    %edi,%esi
    46d4:	48 8b 3d 3d 59 00 00 	mov    0x593d(%rip),%rdi        # a018 <unimplemented_content>
    46db:	e9 90 fe ff ff       	jmp    4570 <_send_static_string_content>

00000000000046e0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    46e0:	f3 0f 1e fa          	endbr64
    46e4:	55                   	push   %rbp
    46e5:	48 89 e5             	mov    %rsp,%rbp
    46e8:	ff 15 fa 58 00 00    	call   *0x58fa(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
}
    46ee:	5d                   	pop    %rbp
void handle_http_404(int client_socket, struct io_uring *ring) {
    46ef:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    46f2:	89 fe                	mov    %edi,%esi
    46f4:	48 8b 3d 15 59 00 00 	mov    0x5915(%rip),%rdi        # a010 <http_404_content>
    46fb:	e9 70 fe ff ff       	jmp    4570 <_send_static_string_content>

0000000000004700 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4700:	f3 0f 1e fa          	endbr64
    4704:	55                   	push   %rbp
    4705:	48 89 e5             	mov    %rsp,%rbp
    4708:	41 57                	push   %r15
    470a:	41 56                	push   %r14
    470c:	41 55                	push   %r13
    470e:	41 54                	push   %r12
    4710:	53                   	push   %rbx
    4711:	48 81 ec a8 04 00 00 	sub    $0x4a8,%rsp
    4718:	ff 15 ca 58 00 00    	call   *0x58ca(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    471e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4727:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    472b:	31 c0                	xor    %eax,%eax
    472d:	49 89 fc             	mov    %rdi,%r12
    4730:	41 89 f5             	mov    %esi,%r13d
    4733:	49 89 d6             	mov    %rdx,%r14
    if (path[strlen(path) - 1] == '/') {
    4736:	e8 05 dc ff ff       	call   2340 <strlen@plt>
    473b:	41 80 7c 04 ff 2f    	cmpb   $0x2f,-0x1(%r12,%rax,1)
    4741:	48 89 c3             	mov    %rax,%rbx
    4744:	0f 84 b6 00 00 00    	je     4800 <handle_get_method+0x100>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    474a:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    474f:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4753:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4758:	4c 89 e6             	mov    %r12,%rsi
    475b:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4762:	66 89 85 c4 fb ff ff 	mov    %ax,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4769:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4770:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    477a:	e8 71 dc ff ff       	call   23f0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    477f:	48 8d b5 30 fb ff ff 	lea    -0x4d0(%rbp),%rsi
    4786:	4c 89 ff             	mov    %r15,%rdi
    4789:	e8 72 dc ff ff       	call   2400 <stat@plt>
    478e:	83 f8 ff             	cmp    $0xffffffff,%eax
    4791:	0f 84 41 01 00 00    	je     48d8 <handle_get_method+0x1d8>
        if (S_ISREG(path_stat.st_mode)) {
    4797:	8b 85 48 fb ff ff    	mov    -0x4b8(%rbp),%eax
    479d:	25 00 f0 00 00       	and    $0xf000,%eax
    47a2:	3d 00 80 00 00       	cmp    $0x8000,%eax
    47a7:	0f 84 b3 00 00 00    	je     4860 <handle_get_method+0x160>
    _send_static_string_content(http_404_content, client_socket, ring);
    47ad:	48 8b 3d 5c 58 00 00 	mov    0x585c(%rip),%rdi        # a010 <http_404_content>
    47b4:	4c 89 f2             	mov    %r14,%rdx
    47b7:	44 89 ee             	mov    %r13d,%esi
    47ba:	e8 b1 fd ff ff       	call   4570 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    47bf:	4c 89 fa             	mov    %r15,%rdx
    47c2:	bf 01 00 00 00       	mov    $0x1,%edi
    47c7:	31 c0                	xor    %eax,%eax
    47c9:	48 8d 35 50 29 00 00 	lea    0x2950(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    47d0:	e8 ab dc ff ff       	call   2480 <__printf_chk@plt>
}
    47d5:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    47d9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    47e2:	0f 85 20 01 00 00    	jne    4908 <handle_get_method+0x208>
    47e8:	48 81 c4 a8 04 00 00 	add    $0x4a8,%rsp
    47ef:	5b                   	pop    %rbx
    47f0:	41 5c                	pop    %r12
    47f2:	41 5d                	pop    %r13
    47f4:	41 5e                	pop    %r14
    47f6:	41 5f                	pop    %r15
    47f8:	5d                   	pop    %rbp
    47f9:	c3                   	ret
    47fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4800:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4805:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
    480c:	4c 89 e6             	mov    %r12,%rsi
    480f:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4814:	66 89 95 c4 fb ff ff 	mov    %dx,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    481b:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    481e:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
    4825:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    482f:	e8 bc db ff ff       	call   23f0 <__memcpy_chk@plt>
    4834:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4839:	49 8d 7c 1f 06       	lea    0x6(%r15,%rbx,1),%rdi
    483e:	ba 0b 00 00 00       	mov    $0xb,%edx
    4843:	48 29 d9             	sub    %rbx,%rcx
    4846:	48 8d 35 9e 28 00 00 	lea    0x289e(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    484d:	e8 9e db ff ff       	call   23f0 <__memcpy_chk@plt>
    4852:	e9 28 ff ff ff       	jmp    477f <handle_get_method+0x7f>
    4857:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4860:	bf 70 00 00 00       	mov    $0x70,%edi
    4865:	e8 d6 db ff ff       	call   2440 <malloc@plt>
    486a:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    486d:	48 85 c0             	test   %rax,%rax
    4870:	0f 84 97 00 00 00    	je     490d <handle_get_method+0x20d>
            req->client_socket = client_socket;
    4876:	44 89 68 08          	mov    %r13d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    487a:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    4881:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4885:	4c 89 ff             	mov    %r15,%rdi
            req->iovec_count = 6;
    4888:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    488f:	e8 5c f5 ff ff       	call   3df0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4894:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    489b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    489f:	4c 89 ff             	mov    %r15,%rdi
    48a2:	e8 79 fa ff ff       	call   4320 <copy_file_contents>
    48a7:	4c 89 fa             	mov    %r15,%rdx
    48aa:	bf 01 00 00 00       	mov    $0x1,%edi
    48af:	31 c0                	xor    %eax,%eax
    48b1:	48 8b 8d 60 fb ff ff 	mov    -0x4a0(%rbp),%rcx
    48b8:	48 8d 35 4f 28 00 00 	lea    0x284f(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    48bf:	e8 bc db ff ff       	call   2480 <__printf_chk@plt>
            add_write_request(req, ring);
    48c4:	4c 89 f6             	mov    %r14,%rsi
    48c7:	48 89 df             	mov    %rbx,%rdi
    48ca:	e8 11 fb ff ff       	call   43e0 <add_write_request>
    48cf:	e9 01 ff ff ff       	jmp    47d5 <handle_get_method+0xd5>
    48d4:	0f 1f 40 00          	nopl   0x0(%rax)
    48d8:	4c 89 fa             	mov    %r15,%rdx
    48db:	4c 89 e1             	mov    %r12,%rcx
    48de:	48 8d 35 11 28 00 00 	lea    0x2811(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    48e5:	31 c0                	xor    %eax,%eax
    48e7:	bf 01 00 00 00       	mov    $0x1,%edi
    48ec:	e8 8f db ff ff       	call   2480 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    48f1:	48 8b 3d 18 57 00 00 	mov    0x5718(%rip),%rdi        # a010 <http_404_content>
    48f8:	4c 89 f2             	mov    %r14,%rdx
    48fb:	44 89 ee             	mov    %r13d,%esi
    48fe:	e8 6d fc ff ff       	call   4570 <_send_static_string_content>
}
    4903:	e9 cd fe ff ff       	jmp    47d5 <handle_get_method+0xd5>
}
    4908:	e8 43 da ff ff       	call   2350 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    490d:	48 8b 0d 0c 57 00 00 	mov    0x570c(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4914:	ba 28 00 00 00       	mov    $0x28,%edx
    4919:	be 01 00 00 00       	mov    $0x1,%esi
    491e:	48 8d 3d e3 2a 00 00 	lea    0x2ae3(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4925:	e8 d6 db ff ff       	call   2500 <fwrite@plt>
        exit(1);
    492a:	bf 01 00 00 00       	mov    $0x1,%edi
    492f:	e8 ac db ff ff       	call   24e0 <exit@plt>
    4934:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    493f:	90                   	nop

0000000000004940 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4940:	f3 0f 1e fa          	endbr64
    4944:	55                   	push   %rbp
    4945:	48 89 e5             	mov    %rsp,%rbp
    4948:	41 57                	push   %r15
    494a:	41 56                	push   %r14
    494c:	41 55                	push   %r13
    494e:	41 54                	push   %r12
    4950:	53                   	push   %rbx
    4951:	48 83 ec 28          	sub    $0x28,%rsp
    4955:	ff 15 8d 56 00 00    	call   *0x568d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    method = strtok_r(method_buffer, " ", &saveptr);
    495b:	4c 8d 35 23 27 00 00 	lea    0x2723(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4962:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    496b:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    496f:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4971:	4c 8d 7d c0          	lea    -0x40(%rbp),%r15
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4975:	41 89 f4             	mov    %esi,%r12d
    4978:	49 89 d5             	mov    %rdx,%r13
    method = strtok_r(method_buffer, " ", &saveptr);
    497b:	4c 89 f6             	mov    %r14,%rsi
    497e:	4c 89 fa             	mov    %r15,%rdx
    4981:	e8 1a da ff ff       	call   23a0 <strtok_r@plt>
    for (; *str; ++str)
    4986:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    4989:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    498c:	84 d2                	test   %dl,%dl
    498e:	88 55 bf             	mov    %dl,-0x41(%rbp)
    4991:	74 22                	je     49b5 <handle_http_method+0x75>
        *str = (char)tolower(*str);
    4993:	e8 b8 db ff ff       	call   2550 <__ctype_tolower_loc@plt>
    4998:	48 0f be 55 bf       	movsbq -0x41(%rbp),%rdx
    499d:	48 89 d9             	mov    %rbx,%rcx
    49a0:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    49a3:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    49a7:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    49aa:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    49ad:	48 0f be 11          	movsbq (%rcx),%rdx
    49b1:	84 d2                	test   %dl,%dl
    49b3:	75 eb                	jne    49a0 <handle_http_method+0x60>
    path = strtok_r(NULL, " ", &saveptr);
    49b5:	4c 89 fa             	mov    %r15,%rdx
    49b8:	4c 89 f6             	mov    %r14,%rsi
    49bb:	31 ff                	xor    %edi,%edi
    49bd:	e8 de d9 ff ff       	call   23a0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    49c2:	48 8d 35 6a 27 00 00 	lea    0x276a(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    49c9:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    49cc:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    49cf:	e8 fc d9 ff ff       	call   23d0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    49d4:	4c 89 ea             	mov    %r13,%rdx
    49d7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    49da:	85 c0                	test   %eax,%eax
    49dc:	75 2a                	jne    4a08 <handle_http_method+0xc8>
        handle_get_method(path, client_socket, ring);
    49de:	4c 89 f7             	mov    %r14,%rdi
    49e1:	e8 1a fd ff ff       	call   4700 <handle_get_method>
}
    49e6:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    49ea:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    49f3:	75 21                	jne    4a16 <handle_http_method+0xd6>
    49f5:	48 83 c4 28          	add    $0x28,%rsp
    49f9:	5b                   	pop    %rbx
    49fa:	41 5c                	pop    %r12
    49fc:	41 5d                	pop    %r13
    49fe:	41 5e                	pop    %r14
    4a00:	41 5f                	pop    %r15
    4a02:	5d                   	pop    %rbp
    4a03:	c3                   	ret
    4a04:	0f 1f 40 00          	nopl   0x0(%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4a08:	48 8b 3d 09 56 00 00 	mov    0x5609(%rip),%rdi        # a018 <unimplemented_content>
    4a0f:	e8 5c fb ff ff       	call   4570 <_send_static_string_content>
}
    4a14:	eb d0                	jmp    49e6 <handle_http_method+0xa6>
    4a16:	e8 35 d9 ff ff       	call   2350 <__stack_chk_fail@plt>
    4a1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004a20 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4a20:	f3 0f 1e fa          	endbr64
    4a24:	55                   	push   %rbp
    4a25:	48 89 e5             	mov    %rsp,%rbp
    4a28:	ff 15 ba 55 00 00    	call   *0x55ba(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    for (int i = 0; i < dest_sz; i++) {
    4a2e:	85 d2                	test   %edx,%edx
    4a30:	7e 36                	jle    4a68 <get_line+0x48>
    4a32:	48 63 d2             	movslq %edx,%rdx
    4a35:	48 83 c7 01          	add    $0x1,%rdi
    4a39:	48 01 f2             	add    %rsi,%rdx
    4a3c:	eb 0f                	jmp    4a4d <get_line+0x2d>
    4a3e:	66 90                	xchg   %ax,%ax
    4a40:	48 83 c6 01          	add    $0x1,%rsi
    4a44:	48 83 c7 01          	add    $0x1,%rdi
    4a48:	48 39 d6             	cmp    %rdx,%rsi
    4a4b:	74 1b                	je     4a68 <get_line+0x48>
        dest[i] = src[i];
    4a4d:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4a51:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4a53:	3c 0d                	cmp    $0xd,%al
    4a55:	75 e9                	jne    4a40 <get_line+0x20>
    4a57:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4a5a:	75 e4                	jne    4a40 <get_line+0x20>
            return 0;
    4a5c:	31 c0                	xor    %eax,%eax
            dest[i] = '\0';
    4a5e:	c6 06 00             	movb   $0x0,(%rsi)
}
    4a61:	5d                   	pop    %rbp
    4a62:	c3                   	ret
    4a63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    return 1;
    4a68:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4a6d:	5d                   	pop    %rbp
    4a6e:	c3                   	ret
    4a6f:	90                   	nop

0000000000004a70 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4a70:	f3 0f 1e fa          	endbr64
    4a74:	55                   	push   %rbp
    4a75:	48 89 e5             	mov    %rsp,%rbp
    4a78:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    4a7f:	ff 15 63 55 00 00    	call   *0x5563(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    4a85:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4a89:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a92:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
    4a96:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4a98:	4c 8d 95 f0 fb ff ff 	lea    -0x410(%rbp),%r10
    4a9f:	4c 8d 4d f0          	lea    -0x10(%rbp),%r9
    4aa3:	4c 89 d0             	mov    %r10,%rax
    4aa6:	eb 15                	jmp    4abd <handle_client_request+0x4d>
    4aa8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4ab0:	48 83 c0 01          	add    $0x1,%rax
    4ab4:	48 83 c1 01          	add    $0x1,%rcx
    4ab8:	4c 39 c8             	cmp    %r9,%rax
    4abb:	74 43                	je     4b00 <handle_client_request+0x90>
        dest[i] = src[i];
    4abd:	44 0f b6 01          	movzbl (%rcx),%r8d
    4ac1:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4ac4:	41 80 f8 0d          	cmp    $0xd,%r8b
    4ac8:	75 e6                	jne    4ab0 <handle_client_request+0x40>
    4aca:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4ace:	75 e0                	jne    4ab0 <handle_client_request+0x40>
            dest[i] = '\0';
    4ad0:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4ad3:	8b 47 08             	mov    0x8(%rdi),%eax
    4ad6:	48 89 f2             	mov    %rsi,%rdx
    4ad9:	4c 89 d7             	mov    %r10,%rdi
    4adc:	89 c6                	mov    %eax,%esi
    4ade:	e8 5d fe ff ff       	call   4940 <handle_http_method>
}
    4ae3:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    4ae7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4af0:	75 35                	jne    4b27 <handle_client_request+0xb7>
    4af2:	c9                   	leave
    4af3:	31 c0                	xor    %eax,%eax
    4af5:	c3                   	ret
    4af6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4b00:	48 8b 0d 19 55 00 00 	mov    0x5519(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4b07:	ba 12 00 00 00       	mov    $0x12,%edx
    4b0c:	be 01 00 00 00       	mov    $0x1,%esi
    4b11:	48 8d 3d 1f 26 00 00 	lea    0x261f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4b18:	e8 e3 d9 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    4b1d:	bf 01 00 00 00       	mov    $0x1,%edi
    4b22:	e8 b9 d9 ff ff       	call   24e0 <exit@plt>
}
    4b27:	e8 24 d8 ff ff       	call   2350 <__stack_chk_fail@plt>
    4b2c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004b30 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4b30:	f3 0f 1e fa          	endbr64
    4b34:	55                   	push   %rbp
    4b35:	48 89 e5             	mov    %rsp,%rbp
    4b38:	41 54                	push   %r12
    4b3a:	53                   	push   %rbx
    4b3b:	ff 15 a7 54 00 00    	call   *0x54a7(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    4b41:	8b 41 44             	mov    0x44(%rcx),%eax
    4b44:	83 c0 01             	add    $0x1,%eax
    4b47:	48 89 cb             	mov    %rcx,%rbx
	if (ring->flags & IORING_SETUP_SQE128)
    4b4a:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    4b50:	4c 8b 03             	mov    (%rbx),%r8
    4b53:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4b56:	f6 c1 02             	test   $0x2,%cl
    4b59:	74 00                	je     4b5b <add_accept_request+0x2b>
	if (next - head <= sq->ring_entries) {
    4b5b:	41 89 c0             	mov    %eax,%r8d
    4b5e:	45 29 c8             	sub    %r9d,%r8d
    4b61:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4b65:	0f 82 68 da ff ff    	jb     25d3 <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4b6b:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4b6e:	44 8b 63 44          	mov    0x44(%rbx),%r12d
    4b72:	44 23 63 58          	and    0x58(%rbx),%r12d
		sq->sqe_tail = next;
    4b76:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4b79:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4b7c:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4b80:	41 d3 e4             	shl    %cl,%r12d
    4b83:	49 c1 e4 06          	shl    $0x6,%r12
    4b87:	4c 03 63 38          	add    0x38(%rbx),%r12
	sqe->fd = fd;
    4b8b:	41 89 7c 24 04       	mov    %edi,0x4(%r12)
  struct Request *req = malloc(sizeof(*req));
    4b90:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4b95:	41 c7 04 24 0d 00 00 00 	movl   $0xd,(%r12)
	sqe->off = offset;
    4b9d:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
	sqe->addr = (unsigned long) addr;
    4ba2:	49 89 74 24 10       	mov    %rsi,0x10(%r12)
	sqe->buf_index = 0;
    4ba7:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->len = len;
    4bb0:	49 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%r12)
	sqe->addr3 = 0;
    4bb9:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    4bbf:	e8 7c d8 ff ff       	call   2440 <malloc@plt>
  io_uring_submit(ring);
    4bc4:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4bc7:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4bcd:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
    4bd2:	5b                   	pop    %rbx
    4bd3:	41 5c                	pop    %r12
    4bd5:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4bd6:	e9 85 d7 ff ff       	jmp    2360 <io_uring_submit@plt>
    4bdb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004be0 <io_thread>:
void* io_thread(void *arg) {
    4be0:	f3 0f 1e fa          	endbr64
    4be4:	55                   	push   %rbp
    4be5:	48 89 e5             	mov    %rsp,%rbp
    4be8:	41 57                	push   %r15
    4bea:	41 56                	push   %r14
    4bec:	41 55                	push   %r13
    4bee:	41 54                	push   %r12
    4bf0:	53                   	push   %rbx
    4bf1:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4bf8:	ff 15 ea 53 00 00    	call   *0x53ea(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4bfe:	31 d2                	xor    %edx,%edx
  struct io_uring ring = *data->ring;
    4c00:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4c09:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    4c0d:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4c11:	48 8d 9d e0 fa ff ff 	lea    -0x520(%rbp),%rbx
void* io_thread(void *arg) {
    4c18:	49 89 fc             	mov    %rdi,%r12
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4c1b:	bf 00 01 00 00       	mov    $0x100,%edi
    4c20:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4c23:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4c27:	0f 29 8d e0 fa ff ff 	movaps %xmm1,-0x520(%rbp)
    4c2e:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4c33:	0f 29 95 f0 fa ff ff 	movaps %xmm2,-0x510(%rbp)
    4c3a:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4c3f:	0f 29 9d 00 fb ff ff 	movaps %xmm3,-0x500(%rbp)
    4c46:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4c4b:	0f 29 a5 10 fb ff ff 	movaps %xmm4,-0x4f0(%rbp)
    4c52:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4c57:	0f 29 ad 20 fb ff ff 	movaps %xmm5,-0x4e0(%rbp)
    4c5e:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4c63:	0f 29 b5 30 fb ff ff 	movaps %xmm6,-0x4d0(%rbp)
    4c6a:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4c6f:	0f 29 bd 40 fb ff ff 	movaps %xmm7,-0x4c0(%rbp)
    4c76:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4c7b:	0f 29 8d 50 fb ff ff 	movaps %xmm1,-0x4b0(%rbp)
    4c82:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4c8a:	0f 29 95 60 fb ff ff 	movaps %xmm2,-0x4a0(%rbp)
    4c91:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4c99:	0f 29 9d 70 fb ff ff 	movaps %xmm3,-0x490(%rbp)
    4ca0:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4ca8:	0f 29 a5 80 fb ff ff 	movaps %xmm4,-0x480(%rbp)
    4caf:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4cb7:	0f 29 ad 90 fb ff ff 	movaps %xmm5,-0x470(%rbp)
    4cbe:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4cc6:	0f 29 b5 a0 fb ff ff 	movaps %xmm6,-0x460(%rbp)
    4ccd:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4cd4:	48 89 85 b0 fb ff ff 	mov    %rax,-0x450(%rbp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4cdb:	e8 40 d7 ff ff       	call   2420 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4ce0:	49 8b 7c 24 48       	mov    0x48(%r12),%rdi
    4ce5:	31 f6                	xor    %esi,%esi
    4ce7:	e8 34 d8 ff ff       	call   2520 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4cec:	31 d2                	xor    %edx,%edx
    4cee:	be 01 00 00 00       	mov    $0x1,%esi
    4cf3:	bf 02 00 00 00       	mov    $0x2,%edi
    4cf8:	e8 73 d8 ff ff       	call   2570 <socket@plt>
    4cfd:	89 85 ac fa ff ff    	mov    %eax,-0x554(%rbp)
  if (sock == -1)
    4d03:	83 f8 ff             	cmp    $0xffffffff,%eax
    4d06:	0f 84 09 d9 ff ff    	je     2615 <io_thread.cold+0x38>
    4d0c:	89 c7                	mov    %eax,%edi
  if (setsockopt(sock,
    4d0e:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4d14:	ba 02 00 00 00       	mov    $0x2,%edx
    4d19:	be 01 00 00 00       	mov    $0x1,%esi
    4d1e:	48 8d 8d b0 fa ff ff 	lea    -0x550(%rbp),%rcx
  int enable = 1;
    4d25:	c7 85 b0 fa ff ff 01 00 00 00 	movl   $0x1,-0x550(%rbp)
  if (setsockopt(sock,
    4d2f:	e8 ec d5 ff ff       	call   2320 <setsockopt@plt>
    4d34:	85 c0                	test   %eax,%eax
    4d36:	0f 88 ad d8 ff ff    	js     25e9 <io_thread.cold+0xc>
  if (bind(sock,
    4d3c:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4d42:	ba 10 00 00 00       	mov    $0x10,%edx
  return __builtin___memset_chk (__dest, __ch, __len,
    4d47:	48 8d b5 c0 fa ff ff 	lea    -0x540(%rbp),%rsi
    4d4e:	48 c7 85 c4 fa ff ff 00 00 00 00 	movq   $0x0,-0x53c(%rbp)
    4d59:	c7 85 cc fa ff ff 00 00 00 00 	movl   $0x0,-0x534(%rbp)
  srv_addr.sin_family = AF_INET;
    4d63:	c7 85 c0 fa ff ff 02 00 18 db 	movl   $0xdb180002,-0x540(%rbp)
  if (bind(sock,
    4d6d:	e8 1e d7 ff ff       	call   2490 <bind@plt>
    4d72:	85 c0                	test   %eax,%eax
    4d74:	0f 88 a7 d8 ff ff    	js     2621 <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4d7a:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4d80:	be 0a 00 00 00       	mov    $0xa,%esi
    4d85:	e8 c6 d6 ff ff       	call   2450 <listen@plt>
    4d8a:	85 c0                	test   %eax,%eax
    4d8c:	0f 88 63 d8 ff ff    	js     25f5 <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4d92:	ba db 18 00 00       	mov    $0x18db,%edx
    4d97:	48 8d 35 de 23 00 00 	lea    0x23de(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4d9e:	bf 01 00 00 00       	mov    $0x1,%edi
    4da3:	31 c0                	xor    %eax,%eax
    4da5:	e8 d6 d6 ff ff       	call   2480 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4daa:	48 8d 85 d0 fa ff ff 	lea    -0x530(%rbp),%rax
    4db1:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4db7:	48 89 d9             	mov    %rbx,%rcx
    4dba:	48 8d 95 b4 fa ff ff 	lea    -0x54c(%rbp),%rdx
    4dc1:	48 89 c6             	mov    %rax,%rsi
  socklen_t client_addr_len = sizeof(client_addr);
    4dc4:	c7 85 b4 fa ff ff 10 00 00 00 	movl   $0x10,-0x54c(%rbp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4dce:	48 89 95 88 fa ff ff 	mov    %rdx,-0x578(%rbp)
    4dd5:	48 89 85 90 fa ff ff 	mov    %rax,-0x570(%rbp)
    4ddc:	e8 4f fd ff ff       	call   4b30 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4de1:	bf 01 00 00 00       	mov    $0x1,%edi
    4de6:	be 10 00 00 00       	mov    $0x10,%esi
    4deb:	e8 d0 d5 ff ff       	call   23c0 <calloc@plt>
    void *buf = malloc(size);
    4df0:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4df5:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    4df8:	e8 43 d6 ff ff       	call   2440 <malloc@plt>
    if (!buf) {
    4dfd:	48 85 c0             	test   %rax,%rax
    4e00:	0f 84 cf 04 00 00    	je     52d5 <io_thread+0x6f5>
  iov->iov_base = zh_malloc(10);
    4e06:	49 89 06             	mov    %rax,(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    4e09:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e0f:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
  iov->iov_len = 10;
    4e15:	49 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    4e1d:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4e20:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    4e27:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4e29:	f6 c1 02             	test   $0x2,%cl
    4e2c:	0f 85 2e 04 00 00    	jne    5260 <io_thread+0x680>
	if (next - head <= sq->ring_entries) {
    4e32:	89 d0                	mov    %edx,%eax
    4e34:	29 f0                	sub    %esi,%eax
    4e36:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    4e3c:	0f 82 c9 d7 ff ff    	jb     260b <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4e42:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e45:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    4e4b:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4e4f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e52:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e58:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4e5b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4e61:	49 8d 74 24 50       	lea    0x50(%r12),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4e66:	41 8b 54 24 50       	mov    0x50(%r12),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e6b:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4e6d:	48 89 b5 98 fa ff ff 	mov    %rsi,-0x568(%rbp)
    4e74:	48 c1 e0 06          	shl    $0x6,%rax
    4e78:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    4e7f:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4e85:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4e88:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4e90:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    4e94:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4e9c:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4ea4:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4ea8:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4eac:	e8 af d4 ff ff       	call   2360 <io_uring_submit@plt>
  while (data->running == 1) {
    4eb1:	41 83 7c 24 34 01    	cmpl   $0x1,0x34(%r12)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4eb7:	4c 8d 8d b8 fa ff ff 	lea    -0x548(%rbp),%r9
    4ebe:	4c 8d 95 c0 fb ff ff 	lea    -0x440(%rbp),%r10
    4ec5:	0f 85 ed 01 00 00    	jne    50b8 <io_thread+0x4d8>
    4ecb:	4c 89 8d a0 fa ff ff 	mov    %r9,-0x560(%rbp)
    4ed2:	4c 89 95 80 fa ff ff 	mov    %r10,-0x580(%rbp)
    4ed9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4ee0:	48 8d 3d ab 22 00 00 	lea    0x22ab(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    4ee7:	e8 24 d4 ff ff       	call   2310 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4eec:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4ef2:	8b bd 90 fb ff ff    	mov    -0x470(%rbp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4ef8:	c1 e9 0b             	shr    $0xb,%ecx
    4efb:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4efe:	48 8b 85 50 fb ff ff 	mov    -0x4b0(%rbp),%rax
    4f05:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4f07:	48 8b b5 48 fb ff ff 	mov    -0x4b8(%rbp),%rsi
    4f0e:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4f10:	39 d0                	cmp    %edx,%eax
    4f12:	74 34                	je     4f48 <io_thread+0x368>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4f14:	89 f8                	mov    %edi,%eax
    4f16:	21 d0                	and    %edx,%eax
    4f18:	d3 e0                	shl    %cl,%eax
    4f1a:	48 c1 e0 04          	shl    $0x4,%rax
    4f1e:	48 03 85 78 fb ff ff 	add    -0x488(%rbp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4f25:	f6 85 a9 fb ff ff 01 	testb  $0x1,-0x457(%rbp)
    4f2c:	0f 85 be 01 00 00    	jne    50f0 <io_thread+0x510>
    4f32:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4f36:	0f 85 2c 03 00 00    	jne    5268 <io_thread+0x688>
			if (cqe->res < 0)
    4f3c:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4f3f:	83 c2 01             	add    $0x1,%edx
    4f42:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4f44:	85 c0                	test   %eax,%eax
    4f46:	79 b6                	jns    4efe <io_thread+0x31e>
	*cqe_ptr = cqe;
    4f48:	48 c7 85 b8 fa ff ff 00 00 00 00 	movq   $0x0,-0x548(%rbp)
	return err;
    4f53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4f58:	48 8b b5 a0 fa ff ff 	mov    -0x560(%rbp),%rsi
    4f5f:	45 31 c0             	xor    %r8d,%r8d
    4f62:	31 d2                	xor    %edx,%edx
    4f64:	48 89 df             	mov    %rbx,%rdi
    4f67:	b9 01 00 00 00       	mov    $0x1,%ecx
    4f6c:	e8 ff d4 ff ff       	call   2470 <__io_uring_get_cqe@plt>
    4f71:	41 89 c5             	mov    %eax,%r13d
      if (cqe->user_data == 1) {
    4f74:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    4f7b:	48 83 38 01          	cmpq   $0x1,(%rax)
    4f7f:	0f 84 f3 02 00 00    	je     5278 <io_thread+0x698>
    4f85:	48 8d 3d 2c 22 00 00 	lea    0x222c(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    4f8c:	e8 7f d3 ff ff       	call   2310 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4f91:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    4f98:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    4f9b:	45 85 ed             	test   %r13d,%r13d
    4f9e:	0f 88 39 d6 ff ff    	js     25dd <io_thread.cold>
      if (cqe->res < 0) {
    4fa4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    4fa7:	45 8b 07             	mov    (%r15),%r8d
      if (cqe->res < 0) {
    4faa:	85 c0                	test   %eax,%eax
    4fac:	0f 88 e5 02 00 00    	js     5297 <io_thread+0x6b7>
      switch (req->event_type) {
    4fb2:	41 83 f8 01          	cmp    $0x1,%r8d
    4fb6:	0f 84 84 01 00 00    	je     5140 <io_thread+0x560>
    4fbc:	41 83 f8 02          	cmp    $0x2,%r8d
    4fc0:	0f 84 aa 01 00 00    	je     5170 <io_thread+0x590>
    4fc6:	45 85 c0             	test   %r8d,%r8d
    4fc9:	0f 85 59 01 00 00    	jne    5128 <io_thread+0x548>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4fcf:	48 8b 95 88 fa ff ff 	mov    -0x578(%rbp),%rdx
    4fd6:	48 8b b5 90 fa ff ff 	mov    -0x570(%rbp),%rsi
    4fdd:	48 89 d9             	mov    %rbx,%rcx
    4fe0:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4fe6:	e8 45 fb ff ff       	call   4b30 <add_accept_request>
              add_read_request(cqe->res, &ring);
    4feb:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    4ff2:	48 89 de             	mov    %rbx,%rsi
    4ff5:	8b 78 08             	mov    0x8(%rax),%edi
    4ff8:	e8 83 f4 ff ff       	call   4480 <add_read_request>
              free(req);
    4ffd:	4c 89 ff             	mov    %r15,%rdi
    5000:	e8 db d2 ff ff       	call   22e0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5005:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
	if (cqe)
    500c:	48 85 c0             	test   %rax,%rax
    500f:	0f 85 13 01 00 00    	jne    5128 <io_thread+0x548>
	unsigned int head, next = sq->sqe_tail + 1;
    5015:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    501b:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5021:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5024:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    502b:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    502d:	f6 c1 02             	test   $0x2,%cl
    5030:	74 00                	je     5032 <io_thread+0x452>
	if (next - head <= sq->ring_entries) {
    5032:	89 d0                	mov    %edx,%eax
    5034:	29 f0                	sub    %esi,%eax
    5036:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    503c:	0f 82 bf d5 ff ff    	jb     2601 <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5042:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5045:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    504b:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    504f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5052:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5058:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    505b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5061:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5063:	41 8b 54 24 50       	mov    0x50(%r12),%edx
	sqe->user_data = (unsigned long) data;
    5068:	48 8b b5 98 fa ff ff 	mov    -0x568(%rbp),%rsi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    506f:	48 c1 e0 06          	shl    $0x6,%rax
    5073:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    507a:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5080:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5083:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    508b:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    508f:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5097:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    509f:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    50a3:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    50a7:	e8 b4 d2 ff ff       	call   2360 <io_uring_submit@plt>
  while (data->running == 1) {
    50ac:	41 83 7c 24 34 01    	cmpl   $0x1,0x34(%r12)
    50b2:	0f 84 28 fe ff ff    	je     4ee0 <io_thread+0x300>
    50b8:	48 8d 3d 32 21 00 00 	lea    0x2132(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    50bf:	e8 4c d2 ff ff       	call   2310 <puts@plt>
}
    50c4:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    50c8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    50d1:	0f 85 25 02 00 00    	jne    52fc <io_thread+0x71c>
    50d7:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    50de:	31 c0                	xor    %eax,%eax
    50e0:	5b                   	pop    %rbx
    50e1:	41 5c                	pop    %r12
    50e3:	41 5d                	pop    %r13
    50e5:	41 5e                	pop    %r14
    50e7:	41 5f                	pop    %r15
    50e9:	5d                   	pop    %rbp
    50ea:	c3                   	ret
    50eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    50f0:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    50f7:	48 85 c0             	test   %rax,%rax
    50fa:	0f 84 58 fe ff ff    	je     4f58 <io_thread+0x378>
      if (cqe->user_data == 1) {
    5100:	48 83 38 01          	cmpq   $0x1,(%rax)
    5104:	0f 84 6e 01 00 00    	je     5278 <io_thread+0x698>
    510a:	48 8d 3d a7 20 00 00 	lea    0x20a7(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    5111:	e8 fa d1 ff ff       	call   2310 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5116:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    511d:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    5120:	e9 7f fe ff ff       	jmp    4fa4 <io_thread+0x3c4>
    5125:	0f 1f 00             	nopl   (%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5128:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
    512f:	8b 02                	mov    (%rdx),%eax
    5131:	83 c0 01             	add    $0x1,%eax
    5134:	89 02                	mov    %eax,(%rdx)
}
    5136:	e9 da fe ff ff       	jmp    5015 <io_thread+0x435>
    513b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              if (!cqe->res) {
    5140:	85 c0                	test   %eax,%eax
    5142:	75 7c                	jne    51c0 <io_thread+0x5e0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5144:	48 8b 0d d5 4e 00 00 	mov    0x4ed5(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    514b:	ba 0f 00 00 00       	mov    $0xf,%edx
    5150:	be 01 00 00 00       	mov    $0x1,%esi
    5155:	48 8d 3d 85 20 00 00 	lea    0x2085(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    515c:	e8 9f d3 ff ff       	call   2500 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5161:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    5168:	e9 9f fe ff ff       	jmp    500c <io_thread+0x42c>
    516d:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    5170:	41 8b 47 04          	mov    0x4(%r15),%eax
    5174:	45 31 ed             	xor    %r13d,%r13d
    5177:	85 c0                	test   %eax,%eax
    5179:	7e 20                	jle    519b <io_thread+0x5bb>
    517b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  free(req->iov[i].iov_base);
    5180:	4c 89 e8             	mov    %r13,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5183:	49 83 c5 01          	add    $0x1,%r13
                  free(req->iov[i].iov_base);
    5187:	48 c1 e0 04          	shl    $0x4,%rax
    518b:	49 8b 7c 07 10       	mov    0x10(%r15,%rax,1),%rdi
    5190:	e8 4b d1 ff ff       	call   22e0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5195:	45 39 6f 04          	cmp    %r13d,0x4(%r15)
    5199:	7f e5                	jg     5180 <io_thread+0x5a0>
              close(req->client_socket);
    519b:	41 8b 7f 08          	mov    0x8(%r15),%edi
    519f:	e8 ec d1 ff ff       	call   2390 <close@plt>
              free(req);
    51a4:	4c 89 ff             	mov    %r15,%rdi
    51a7:	e8 34 d1 ff ff       	call   22e0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    51ac:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    51b3:	e9 54 fe ff ff       	jmp    500c <io_thread+0x42c>
    51b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int i = 0; i < dest_sz; i++) {
    51c0:	49 8b 57 10          	mov    0x10(%r15),%rdx
    51c4:	48 8b 85 80 fa ff ff 	mov    -0x580(%rbp),%rax
    51cb:	48 8d 75 c0          	lea    -0x40(%rbp),%rsi
    51cf:	eb 14                	jmp    51e5 <io_thread+0x605>
    51d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    51d8:	48 83 c0 01          	add    $0x1,%rax
    51dc:	48 83 c2 01          	add    $0x1,%rdx
    51e0:	48 39 c6             	cmp    %rax,%rsi
    51e3:	74 4b                	je     5230 <io_thread+0x650>
        dest[i] = src[i];
    51e5:	0f b6 0a             	movzbl (%rdx),%ecx
    51e8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    51ea:	80 f9 0d             	cmp    $0xd,%cl
    51ed:	75 e9                	jne    51d8 <io_thread+0x5f8>
    51ef:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    51f3:	75 e3                	jne    51d8 <io_thread+0x5f8>
            dest[i] = '\0';
    51f5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    51f8:	48 8b bd 80 fa ff ff 	mov    -0x580(%rbp),%rdi
    51ff:	48 89 da             	mov    %rbx,%rdx
    5202:	41 8b 77 08          	mov    0x8(%r15),%esi
    5206:	e8 35 f7 ff ff       	call   4940 <handle_http_method>
              free(req->iov[0].iov_base);
    520b:	49 8b 7f 10          	mov    0x10(%r15),%rdi
    520f:	e8 cc d0 ff ff       	call   22e0 <free@plt>
              free(req);
    5214:	4c 89 ff             	mov    %r15,%rdi
    5217:	e8 c4 d0 ff ff       	call   22e0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    521c:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    5223:	e9 e4 fd ff ff       	jmp    500c <io_thread+0x42c>
    5228:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5230:	48 8b 0d e9 4d 00 00 	mov    0x4de9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5237:	ba 12 00 00 00       	mov    $0x12,%edx
    523c:	be 01 00 00 00       	mov    $0x1,%esi
    5241:	48 8d 3d ef 1e 00 00 	lea    0x1eef(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5248:	e8 b3 d2 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    524d:	bf 01 00 00 00       	mov    $0x1,%edi
    5252:	e8 89 d2 ff ff       	call   24e0 <exit@plt>
    5257:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5260:	e9 cd fb ff ff       	jmp    4e32 <io_thread+0x252>
    5265:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5268:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	return err;
    526f:	e9 8c fe ff ff       	jmp    5100 <io_thread+0x520>
    5274:	0f 1f 40 00          	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5278:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    527f:	48 8d 3d 1e 1f 00 00 	lea    0x1f1e(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    5286:	8b 02                	mov    (%rdx),%eax
    5288:	83 c0 01             	add    $0x1,%eax
    528b:	89 02                	mov    %eax,(%rdx)
    528d:	e8 7e d0 ff ff       	call   2310 <puts@plt>
    5292:	e9 21 fe ff ff       	jmp    50b8 <io_thread+0x4d8>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5297:	f7 d8                	neg    %eax
    5299:	44 89 85 ac fa ff ff 	mov    %r8d,-0x554(%rbp)
    52a0:	89 c7                	mov    %eax,%edi
    52a2:	e8 99 d2 ff ff       	call   2540 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    52a7:	48 8b 3d 72 4d 00 00 	mov    0x4d72(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    52ae:	be 01 00 00 00       	mov    $0x1,%esi
    52b3:	44 8b 85 ac fa ff ff 	mov    -0x554(%rbp),%r8d
    52ba:	48 89 c1             	mov    %rax,%rcx
    52bd:	48 8d 15 74 21 00 00 	lea    0x2174(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    52c4:	31 c0                	xor    %eax,%eax
    52c6:	e8 45 d2 ff ff       	call   2510 <__fprintf_chk@plt>
          exit(1);
    52cb:	bf 01 00 00 00       	mov    $0x1,%edi
    52d0:	e8 0b d2 ff ff       	call   24e0 <exit@plt>
    52d5:	48 8b 0d 44 4d 00 00 	mov    0x4d44(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    52dc:	ba 28 00 00 00       	mov    $0x28,%edx
    52e1:	be 01 00 00 00       	mov    $0x1,%esi
    52e6:	48 8d 3d 1b 21 00 00 	lea    0x211b(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    52ed:	e8 0e d2 ff ff       	call   2500 <fwrite@plt>
        exit(1);
    52f2:	bf 01 00 00 00       	mov    $0x1,%edi
    52f7:	e8 e4 d1 ff ff       	call   24e0 <exit@plt>
}
    52fc:	e8 4f d0 ff ff       	call   2350 <__stack_chk_fail@plt>
    5301:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    530c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005310 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5310:	f3 0f 1e fa          	endbr64
    5314:	55                   	push   %rbp
    5315:	48 89 e5             	mov    %rsp,%rbp
    5318:	41 57                	push   %r15
    531a:	41 56                	push   %r14
    531c:	41 55                	push   %r13
    531e:	41 54                	push   %r12
    5320:	53                   	push   %rbx
    5321:	48 83 ec 08          	sub    $0x8,%rsp
    5325:	ff 15 bd 4c 00 00    	call   *0x4cbd(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    532b:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5332:	8b 8e ac 00 00 00    	mov    0xac(%rsi),%ecx
int barriered_work_ingest(struct BarrierTask *data) {
    5338:	49 89 fd             	mov    %rdi,%r13
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    533b:	85 c9                	test   %ecx,%ecx
    533d:	7e 54                	jle    5393 <barriered_work_ingest+0x83>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    533f:	48 8b 7e 40          	mov    0x40(%rsi),%rdi
    5343:	45 31 f6             	xor    %r14d,%r14d
    5346:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5350:	4a 8b 04 f7          	mov    (%rdi,%r14,8),%rax
    5354:	4e 8d 3c f5 00 00 00 00 	lea    0x0(,%r14,8),%r15
    535c:	31 db                	xor    %ebx,%ebx
    535e:	8b 10                	mov    (%rax),%edx
    5360:	85 d2                	test   %edx,%edx
    5362:	7e 26                	jle    538a <barriered_work_ingest+0x7a>
    5364:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    5368:	49 89 dc             	mov    %rbx,%r12
    536b:	49 c1 e4 08          	shl    $0x8,%r12
    536f:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    5373:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    537a:	74 2c                	je     53a8 <barriered_work_ingest+0x98>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    537c:	48 83 c3 01          	add    $0x1,%rbx
    5380:	39 da                	cmp    %ebx,%edx
    5382:	7f e4                	jg     5368 <barriered_work_ingest+0x58>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5384:	8b 8e ac 00 00 00    	mov    0xac(%rsi),%ecx
    538a:	49 83 c6 01          	add    $0x1,%r14
    538e:	44 39 f1             	cmp    %r14d,%ecx
    5391:	7f bd                	jg     5350 <barriered_work_ingest+0x40>
}
    5393:	48 83 c4 08          	add    $0x8,%rsp
    5397:	31 c0                	xor    %eax,%eax
    5399:	5b                   	pop    %rbx
    539a:	41 5c                	pop    %r12
    539c:	41 5d                	pop    %r13
    539e:	41 5e                	pop    %r14
    53a0:	41 5f                	pop    %r15
    53a2:	5d                   	pop    %rbp
    53a3:	c3                   	ret
    53a4:	0f 1f 40 00          	nopl   0x0(%rax)
        data->ingest_count++;
    53a8:	49 83 85 60 01 00 00 01 	addq   $0x1,0x160(%r13)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    53b0:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    53b7:	bf 04 00 00 00       	mov    $0x4,%edi
    53bc:	48 c1 e6 05          	shl    $0x5,%rsi
    53c0:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    53c7:	48 83 c6 10          	add    $0x10,%rsi
    53cb:	e8 60 cf ff ff       	call   2330 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    53d0:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
    53d7:	48 8b 40 40          	mov    0x40(%rax),%rax
    53db:	4a 8b 04 38          	mov    (%rax,%r15,1),%rax
    53df:	4c 03 60 08          	add    0x8(%rax),%r12
    53e3:	41 8b 84 24 94 00 00 00 	mov    0x94(%r12),%eax
        data->thread->buffers[b]->buffer[x].available = 0;
    53eb:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    53f7:	83 c0 01             	add    $0x1,%eax
    53fa:	99                   	cltd
    53fb:	41 f7 bc 24 90 00 00 00 	idivl  0x90(%r12)
    5403:	41 89 94 24 94 00 00 00 	mov    %edx,0x94(%r12)
        asm volatile ("sfence" ::: "memory");
    540b:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    540e:	49 8b b5 28 01 00 00 	mov    0x128(%r13),%rsi
    5415:	48 83 c3 01          	add    $0x1,%rbx
    5419:	48 8b 7e 40          	mov    0x40(%rsi),%rdi
    541d:	4a 8b 04 3f          	mov    (%rdi,%r15,1),%rax
    5421:	8b 10                	mov    (%rax),%edx
    5423:	39 da                	cmp    %ebx,%edx
    5425:	0f 8f 39 ff ff ff    	jg     5364 <barriered_work_ingest+0x54>
    542b:	e9 54 ff ff ff       	jmp    5384 <barriered_work_ingest+0x74>

0000000000005430 <barriered_thread>:
void* barriered_thread(void *arg) {
    5430:	f3 0f 1e fa          	endbr64
    5434:	55                   	push   %rbp
    5435:	48 89 e5             	mov    %rsp,%rbp
    5438:	41 57                	push   %r15
    543a:	41 56                	push   %r14
    543c:	41 55                	push   %r13
    543e:	41 54                	push   %r12
    5440:	53                   	push   %rbx
    5441:	48 83 ec 08          	sub    $0x8,%rsp
    5445:	ff 15 9d 4b 00 00    	call   *0x4b9d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  int waiting = 0;
    544b:	45 31 e4             	xor    %r12d,%r12d
  int t = 0;
    544e:	45 31 ed             	xor    %r13d,%r13d
void* barriered_thread(void *arg) {
    5451:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    5454:	83 7b 34 01          	cmpl   $0x1,0x34(%rbx)
    5458:	0f 85 04 02 00 00    	jne    5662 <barriered_thread+0x232>
    if (t >= data->task_count) {
    545e:	8b 43 30             	mov    0x30(%rbx),%eax
    5461:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5468:	41 39 c5             	cmp    %eax,%r13d
    546b:	0f 8d 5f 01 00 00    	jge    55d0 <barriered_thread+0x1a0>
    5471:	49 63 fd             	movslq %r13d,%rdi
    5474:	48 c1 e7 09          	shl    $0x9,%rdi
    5478:	49 89 fe             	mov    %rdi,%r14
    547b:	eb 31                	jmp    54ae <barriered_thread+0x7e>
    547d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5480:	48 63 13             	movslq (%rbx),%rdx
    5483:	48 8b 43 10          	mov    0x10(%rbx),%rax
    5487:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    548b:	48 8b 78 28          	mov    0x28(%rax),%rdi
    548f:	4c 01 f7             	add    %r14,%rdi
    5492:	e8 79 fe ff ff       	call   5310 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    5497:	8b 43 30             	mov    0x30(%rbx),%eax
    549a:	41 83 c5 01          	add    $0x1,%r13d
    549e:	49 81 c6 00 02 00 00 	add    $0x200,%r14
    54a5:	44 39 e8             	cmp    %r13d,%eax
    54a8:	0f 8e aa 01 00 00    	jle    5658 <barriered_thread+0x228>
      if (data->tasks[t].available == 1) {
    54ae:	48 8b 53 28          	mov    0x28(%rbx),%rdx
    54b2:	4a 8d 34 32          	lea    (%rdx,%r14,1),%rsi
    54b6:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    54bd:	75 c1                	jne    5480 <barriered_thread+0x50>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    54bf:	8b 7b 18             	mov    0x18(%rbx),%edi
          previous = t - 1;
    54c2:	83 e8 01             	sub    $0x1,%eax
    54c5:	41 8d 4d ff          	lea    -0x1(%r13),%ecx
    54c9:	45 85 ed             	test   %r13d,%r13d
    54cc:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    54cf:	85 ff                	test   %edi,%edi
    54d1:	0f 8e c9 01 00 00    	jle    56a0 <barriered_thread+0x270>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    54d7:	48 63 c8             	movslq %eax,%rcx
    54da:	48 8b 43 10          	mov    0x10(%rbx),%rax
    54de:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    54e1:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    54e4:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    54eb:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    54f2:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    54f6:	45 31 ff             	xor    %r15d,%r15d
    54f9:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    54fd:	0f 1f 00             	nopl   (%rax)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5500:	48 8b 10             	mov    (%rax),%rdx
    5503:	4c 8b 5a 28          	mov    0x28(%rdx),%r11
    5507:	49 01 cb             	add    %rcx,%r11
    550a:	4c 89 da             	mov    %r11,%rdx
    550d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    5514:	75 04                	jne    551a <barriered_thread+0xea>
            arrived++;
    5516:	41 83 c7 01          	add    $0x1,%r15d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    551a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    5521:	75 04                	jne    5527 <barriered_thread+0xf7>
            prearrive++;
    5523:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5527:	48 83 c0 08          	add    $0x8,%rax
    552b:	48 39 c6             	cmp    %rax,%rsi
    552e:	75 d0                	jne    5500 <barriered_thread+0xd0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    5530:	45 85 d2             	test   %r10d,%r10d
    5533:	0f 84 af 00 00 00    	je     55e8 <barriered_thread+0x1b8>
    5539:	44 39 d7             	cmp    %r10d,%edi
    553c:	0f 84 a6 00 00 00    	je     55e8 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    5542:	45 85 ff             	test   %r15d,%r15d
    5545:	74 0a                	je     5551 <barriered_thread+0x121>
    5547:	44 39 7b 18          	cmp    %r15d,0x18(%rbx)
    554b:	0f 85 a0 01 00 00    	jne    56f1 <barriered_thread+0x2c1>
    5551:	48 8b 53 28          	mov    0x28(%rbx),%rdx
          data->tasks[t].prearrive++;
    5555:	4c 01 f2             	add    %r14,%rdx
    5558:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    555f:	45 85 ed             	test   %r13d,%r13d
    5562:	75 0e                	jne    5572 <barriered_thread+0x142>
    5564:	48 8b 73 70          	mov    0x70(%rbx),%rsi
    5568:	48 3b 73 78          	cmp    0x78(%rbx),%rsi
    556c:	0f 8c 06 01 00 00    	jl     5678 <barriered_thread+0x248>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5572:	48 63 0b             	movslq (%rbx),%rcx
    5575:	48 8b 43 10          	mov    0x10(%rbx),%rax
          data->tasks[t].available = 0;
    5579:	c7 82 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5583:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    5587:	48 8b 78 28          	mov    0x28(%rax),%rdi
    558b:	4c 01 f7             	add    %r14,%rdi
    558e:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    5594:	48 8b 43 28          	mov    0x28(%rbx),%rax
    5598:	4c 01 f0             	add    %r14,%rax
    559b:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    55a2:	8b 43 30             	mov    0x30(%rbx),%eax
          data->iteration_count++;
    55a5:	48 83 43 68 01       	addq   $0x1,0x68(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    55aa:	83 e8 01             	sub    $0x1,%eax
    55ad:	44 39 e8             	cmp    %r13d,%eax
    55b0:	74 4e                	je     5600 <barriered_thread+0x1d0>
          asm volatile ("sfence" ::: "memory");
    55b2:	0f ae f8             	sfence
          if (waiting == 0) {
    55b5:	45 85 e4             	test   %r12d,%r12d
    55b8:	74 6e                	je     5628 <barriered_thread+0x1f8>
        int arrived = 0; 
    55ba:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    55c0:	e9 d2 fe ff ff       	jmp    5497 <barriered_thread+0x67>
  while (data->running == 1) {
    55c5:	83 7b 34 01          	cmpl   $0x1,0x34(%rbx)
    55c9:	0f 85 93 00 00 00    	jne    5662 <barriered_thread+0x232>
    55cf:	90                   	nop
      data->cycles++;
    55d0:	48 83 83 98 00 00 00 01 	addq   $0x1,0x98(%rbx)
    for (; t < data->task_count; t++) {
    55d8:	85 c0                	test   %eax,%eax
    55da:	7e e9                	jle    55c5 <barriered_thread+0x195>
    55dc:	45 31 ed             	xor    %r13d,%r13d
    55df:	e9 8d fe ff ff       	jmp    5471 <barriered_thread+0x41>
    55e4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    55e8:	41 83 fc 01          	cmp    $0x1,%r12d
    55ec:	0f 84 be 00 00 00    	je     56b0 <barriered_thread+0x280>
        int arrived = 0; 
    55f2:	45 31 e4             	xor    %r12d,%r12d
    55f5:	e9 48 ff ff ff       	jmp    5542 <barriered_thread+0x112>
    55fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5600:	48 8b 73 70          	mov    0x70(%rbx),%rsi
    5604:	48 3b 73 78          	cmp    0x78(%rbx),%rsi
    5608:	7d a8                	jge    55b2 <barriered_thread+0x182>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    560a:	48 c1 e6 04          	shl    $0x4,%rsi
    560e:	bf 04 00 00 00       	mov    $0x4,%edi
    5613:	48 03 73 60          	add    0x60(%rbx),%rsi
    5617:	e8 14 cd ff ff       	call   2330 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    561c:	48 83 43 70 01       	addq   $0x1,0x70(%rbx)
    5621:	eb 8f                	jmp    55b2 <barriered_thread+0x182>
    5623:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    5628:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    562f:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    5634:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5638:	48 8b 83 80 00 00 00 	mov    0x80(%rbx),%rax
    563f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5643:	44 89 6e 20          	mov    %r13d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5647:	e8 e4 cc ff ff       	call   2330 <clock_gettime@plt>
            waiting = 1;
    564c:	e9 69 ff ff ff       	jmp    55ba <barriered_thread+0x18a>
    5651:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    5658:	83 7b 34 01          	cmpl   $0x1,0x34(%rbx)
    565c:	0f 84 06 fe ff ff    	je     5468 <barriered_thread+0x38>
}
    5662:	48 83 c4 08          	add    $0x8,%rsp
    5666:	31 c0                	xor    %eax,%eax
    5668:	5b                   	pop    %rbx
    5669:	41 5c                	pop    %r12
    566b:	41 5d                	pop    %r13
    566d:	41 5e                	pop    %r14
    566f:	41 5f                	pop    %r15
    5671:	5d                   	pop    %rbp
    5672:	c3                   	ret
    5673:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    5678:	48 c1 e6 04          	shl    $0x4,%rsi
    567c:	bf 04 00 00 00       	mov    $0x4,%edi
    5681:	48 03 73 58          	add    0x58(%rbx),%rsi
    5685:	e8 a6 cc ff ff       	call   2330 <clock_gettime@plt>
          data->tasks[t].available = 0;
    568a:	48 8b 53 28          	mov    0x28(%rbx),%rdx
    568e:	4c 01 f2             	add    %r14,%rdx
    5691:	e9 dc fe ff ff       	jmp    5572 <barriered_thread+0x142>
    5696:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
    56a0:	41 83 fc 01          	cmp    $0x1,%r12d
    56a4:	0f 85 ab fe ff ff    	jne    5555 <barriered_thread+0x125>
        int arrived = 0; 
    56aa:	45 31 ff             	xor    %r15d,%r15d
    56ad:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    56b0:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
    56b7:	bf 04 00 00 00       	mov    $0x4,%edi
    56bc:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    56c0:	48 8b 83 80 00 00 00 	mov    0x80(%rbx),%rax
    56c7:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    56cc:	e8 5f cc ff ff       	call   2330 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    56d1:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
    56d8:	48 83 c0 01          	add    $0x1,%rax
    56dc:	48 99                	cqto
    56de:	48 f7 bb 90 00 00 00 	idivq  0x90(%rbx)
    56e5:	48 89 93 88 00 00 00 	mov    %rdx,0x88(%rbx)
            waiting = 0; 
    56ec:	e9 01 ff ff ff       	jmp    55f2 <barriered_thread+0x1c2>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    56f1:	48 63 13             	movslq (%rbx),%rdx
    56f4:	48 8b 43 10          	mov    0x10(%rbx),%rax
    56f8:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    56fc:	48 8b 78 28          	mov    0x28(%rax),%rdi
    5700:	4c 01 f7             	add    %r14,%rdi
    5703:	e8 08 fc ff ff       	call   5310 <barriered_work_ingest>
          break;
    5708:	e9 47 fd ff ff       	jmp    5454 <barriered_thread+0x24>
    570d:	0f 1f 00             	nopl   (%rax)

0000000000005710 <receive>:
int receive(struct BarrierTask *data) {
    5710:	f3 0f 1e fa          	endbr64
    5714:	55                   	push   %rbp
    5715:	48 89 e5             	mov    %rsp,%rbp
    5718:	41 55                	push   %r13
    571a:	41 54                	push   %r12
    571c:	53                   	push   %rbx
    571d:	48 83 ec 08          	sub    $0x8,%rsp
    5721:	ff 15 c1 48 00 00    	call   *0x48c1(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  for (int n = 0 ; n < data->thread_count; n++) {
    5727:	45 31 e4             	xor    %r12d,%r12d
    572a:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
int receive(struct BarrierTask *data) {
    5730:	48 89 fa             	mov    %rdi,%rdx
  for (int n = 0 ; n < data->thread_count; n++) {
    5733:	85 c0                	test   %eax,%eax
    5735:	0f 8e d9 00 00 00    	jle    5814 <receive+0x104>
    573b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5740:	4c 89 e6             	mov    %r12,%rsi
    5743:	48 c1 e6 05          	shl    $0x5,%rsi
    5747:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    574e:	4c 8b 2e             	mov    (%rsi),%r13
    for (int x = 0 ; x < me->messages_count ; x++) {
    5751:	49 8b 7d 08          	mov    0x8(%r13),%rdi
    5755:	48 85 ff             	test   %rdi,%rdi
    5758:	0f 8e 9a 00 00 00    	jle    57f8 <receive+0xe8>
      data->sends++;
    575e:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    5765:	4d 8b 45 00          	mov    0x0(%r13),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5769:	4c 63 1a             	movslq (%rdx),%r11
    576c:	49 89 c9             	mov    %rcx,%r9
    576f:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5773:	49 f7 d9             	neg    %r9
    5776:	48 01 c7             	add    %rax,%rdi
    5779:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    577d:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    5784:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    5788:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    578b:	49 29 c8             	sub    %rcx,%r8
    578e:	eb 09                	jmp    5799 <receive+0x89>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5790:	48 83 c0 01          	add    $0x1,%rax
    5794:	48 39 c7             	cmp    %rax,%rdi
    5797:	74 5f                	je     57f8 <receive+0xe8>
      data->n++;
    5799:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    579d:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
      data->n++;
    57a4:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    57ab:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    57af:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    57b3:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    57b8:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    57bc:	75 d2                	jne    5790 <receive+0x80>
    57be:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    57c5:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    57c9:	75 c5                	jne    5790 <receive+0x80>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    57cb:	bf 01 00 00 00       	mov    $0x1,%edi
    57d0:	b9 01 00 00 00       	mov    $0x1,%ecx
    57d5:	ba 01 00 00 00       	mov    $0x1,%edx
    57da:	31 c0                	xor    %eax,%eax
    57dc:	48 8d 35 7d 1c 00 00 	lea    0x1c7d(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    57e3:	e8 98 cc ff ff       	call   2480 <__printf_chk@plt>
        exit(1);
    57e8:	bf 01 00 00 00       	mov    $0x1,%edi
    57ed:	e8 ee cc ff ff       	call   24e0 <exit@plt>
    57f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    57f8:	49 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%r13)
    asm volatile ("sfence" ::: "memory");
    5800:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    5803:	49 83 c4 01          	add    $0x1,%r12
    5807:	44 39 a2 34 01 00 00 	cmp    %r12d,0x134(%rdx)
    580e:	0f 8f 2c ff ff ff    	jg     5740 <receive+0x30>
}
    5814:	48 83 c4 08          	add    $0x8,%rsp
    5818:	31 c0                	xor    %eax,%eax
    581a:	5b                   	pop    %rbx
    581b:	41 5c                	pop    %r12
    581d:	41 5d                	pop    %r13
    581f:	5d                   	pop    %rbp
    5820:	c3                   	ret
    5821:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    582c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005830 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5830:	f3 0f 1e fa          	endbr64
    5834:	55                   	push   %rbp
    5835:	48 89 e5             	mov    %rsp,%rbp
    5838:	41 57                	push   %r15
    583a:	41 56                	push   %r14
    583c:	41 55                	push   %r13
    583e:	41 54                	push   %r12
    5840:	53                   	push   %rbx
    5841:	48 83 ec 28          	sub    $0x28,%rsp
    5845:	ff 15 9d 47 00 00    	call   *0x479d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  if (data->thread_index == data->task_index) {
    584b:	8b 07                	mov    (%rdi),%eax
int barriered_work(struct BarrierTask *data) {
    584d:	48 89 fb             	mov    %rdi,%rbx
  if (data->thread_index == data->task_index) {
    5850:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    5856:	0f 84 44 01 00 00    	je     59a0 <barriered_work+0x170>
    receive(data);
    585c:	e8 af fe ff ff       	call   5710 <receive>
    while (data->scheduled == 1) {
    5861:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    5868:	75 1a                	jne    5884 <barriered_work+0x54>
    586a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->n++;
    5870:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    5878:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    587b:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    5882:	74 ec                	je     5870 <barriered_work+0x40>
  if (data->sending == 1) {
    5884:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    588b:	0f 85 85 02 00 00    	jne    5b16 <barriered_work+0x2e6>
      for (int n = 0 ; n < data->thread_count; n++) {
    5891:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5897:	85 c0                	test   %eax,%eax
    5899:	0f 8e 83 02 00 00    	jle    5b22 <barriered_work+0x2f2>
    589f:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    58a6:	45 31 ff             	xor    %r15d,%r15d
    58a9:	48 89 4d c8          	mov    %rcx,-0x38(%rbp)
    58ad:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    58b4:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
    58b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        if (n == data->thread_index) { continue; }
    58c0:	44 39 bb 30 01 00 00 	cmp    %r15d,0x130(%rbx)
    58c7:	0f 84 bf 00 00 00    	je     598c <barriered_work+0x15c>
        struct Data *them = data->mailboxes[n].higher;
    58cd:	4d 89 f8             	mov    %r15,%r8
    58d0:	49 c1 e0 05          	shl    $0x5,%r8
    58d4:	4c 03 83 68 01 00 00 	add    0x168(%rbx),%r8
    58db:	4d 8b 48 08          	mov    0x8(%r8),%r9
        for (; them->messages_count < min;) {
    58df:	4d 8b 51 08          	mov    0x8(%r9),%r10
    58e3:	49 63 79 10          	movslq 0x10(%r9),%rdi
    58e7:	49 39 fa             	cmp    %rdi,%r10
    58ea:	0f 8d 93 00 00 00    	jge    5983 <barriered_work+0x153>
    58f0:	48 89 f9             	mov    %rdi,%rcx
    58f3:	4c 8b b3 08 01 00 00 	mov    0x108(%rbx),%r14
    58fa:	4d 8b 68 10          	mov    0x10(%r8),%r13
    58fe:	4c 29 d1             	sub    %r10,%rcx
          them->messages[them->messages_count++] = data->message; 
    5901:	49 8b 11             	mov    (%r9),%rdx
    5904:	48 8d 41 ff          	lea    -0x1(%rcx),%rax
    5908:	48 83 f8 02          	cmp    $0x2,%rax
    590c:	0f 86 a6 02 00 00    	jbe    5bb8 <barriered_work+0x388>
    5912:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    591a:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    5922:	4c 8d 1c 02          	lea    (%rdx,%rax,1),%r11
    5926:	4c 8d 24 32          	lea    (%rdx,%rsi,1),%r12
    592a:	4c 39 65 c8          	cmp    %r12,-0x38(%rbp)
    592e:	0f 83 0c 02 00 00    	jae    5b40 <barriered_work+0x310>
    5934:	4c 8b 65 c0          	mov    -0x40(%rbp),%r12
    5938:	4d 39 e3             	cmp    %r12,%r11
    593b:	0f 83 ff 01 00 00    	jae    5b40 <barriered_work+0x310>
    5941:	4c 8d 14 02          	lea    (%rdx,%rax,1),%r10
    5945:	48 01 d6             	add    %rdx,%rsi
    5948:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5950:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5957:	49 83 c2 08          	add    $0x8,%r10
          them->messages[them->messages_count++] = data->message; 
    595b:	49 89 42 f8          	mov    %rax,-0x8(%r10)
        for (; them->messages_count < min;) {
    595f:	49 39 f2             	cmp    %rsi,%r10
    5962:	75 ec                	jne    5950 <barriered_work+0x120>
    5964:	0f 1f 40 00          	nopl   0x0(%rax)
    5968:	49 8d 34 0e          	lea    (%r14,%rcx,1),%rsi
    596c:	4c 01 e9             	add    %r13,%rcx
    596f:	48 89 b3 08 01 00 00 	mov    %rsi,0x108(%rbx)
    5976:	49 89 48 10          	mov    %rcx,0x10(%r8)
    597a:	49 89 79 08          	mov    %rdi,0x8(%r9)
    597e:	48 89 44 fa f8       	mov    %rax,-0x8(%rdx,%rdi,8)
        asm volatile ("sfence" ::: "memory");
    5983:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5986:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    598c:	49 83 c7 01          	add    $0x1,%r15
    5990:	44 39 f8             	cmp    %r15d,%eax
    5993:	0f 8f 27 ff ff ff    	jg     58c0 <barriered_work+0x90>
    5999:	e9 84 01 00 00       	jmp    5b22 <barriered_work+0x2f2>
    599e:	66 90                	xchg   %ax,%ax
      receive(data);
    59a0:	e8 6b fd ff ff       	call   5710 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    59a5:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    59ac:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    59ae:	45 85 c9             	test   %r9d,%r9d
    59b1:	0f 8e 85 00 00 00    	jle    5a3c <barriered_work+0x20c>
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
    5a2d:	75 c9                	jne    59f8 <barriered_work+0x1c8>
        for (int y = 0; y < data->thread_count ; y++) {
    5a2f:	48 83 c7 08          	add    $0x8,%rdi
    5a33:	49 83 c0 20          	add    $0x20,%r8
    5a37:	49 39 fd             	cmp    %rdi,%r13
    5a3a:	75 b4                	jne    59f0 <barriered_work+0x1c0>
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
    while (data->scheduled == 1) {
    5a5f:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5a66:	48 8b 50 38          	mov    0x38(%rax),%rdx
    5a6a:	8b 4a 10             	mov    0x10(%rdx),%ecx
    5a6d:	44 8d 61 01          	lea    0x1(%rcx),%r12d
    5a71:	44 89 62 10          	mov    %r12d,0x10(%rdx)
    while (data->scheduled == 1) {
    5a75:	75 5a                	jne    5ad1 <barriered_work+0x2a1>
    5a77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a80:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    5a87:	48 8b 40 10          	mov    0x10(%rax),%rax
    5a8b:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    5a8e:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a96:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5a9a:	48 c1 e7 09          	shl    $0x9,%rdi
    5a9e:	48 03 78 28          	add    0x28(%rax),%rdi
    5aa2:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    5aa8:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5aab:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    5ab2:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5ab9:	74 c5                	je     5a80 <barriered_work+0x250>
    if (modcount != data->thread->protected_state->modcount) {
    5abb:	48 8b 40 38          	mov    0x38(%rax),%rax
    5abf:	44 3b 60 10          	cmp    0x10(%rax),%r12d
    5ac3:	74 0c                	je     5ad1 <barriered_work+0x2a1>
    5ac5:	48 8d 3d 38 17 00 00 	lea    0x1738(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5acc:	e8 3f c8 ff ff       	call   2310 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5ad1:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5ad8:	31 ff                	xor    %edi,%edi
    5ada:	48 c1 e6 05          	shl    $0x5,%rsi
    5ade:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5ae5:	48 83 c6 10          	add    $0x10,%rsi
    5ae9:	e8 42 c8 ff ff       	call   2330 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5aee:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    5af5:	48 83 c0 01          	add    $0x1,%rax
    5af9:	48 99                	cqto
    5afb:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    5b02:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5b09:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    5b10:	0f 84 b7 00 00 00    	je     5bcd <barriered_work+0x39d>
    5b16:	48 8d 3d f7 16 00 00 	lea    0x16f7(%rip),%rdi        # 7214 <_IO_stdin_used+0x214>
    5b1d:	e8 ee c7 ff ff       	call   2310 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5b22:	0f ae f8             	sfence
}
    5b25:	48 83 c4 28          	add    $0x28,%rsp
    5b29:	31 c0                	xor    %eax,%eax
    5b2b:	5b                   	pop    %rbx
    5b2c:	41 5c                	pop    %r12
    5b2e:	41 5d                	pop    %r13
    5b30:	41 5e                	pop    %r14
    5b32:	41 5f                	pop    %r15
    5b34:	5d                   	pop    %rbp
    5b35:	c3                   	ret
    5b36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5b40:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b47:	49 89 cc             	mov    %rcx,%r12
    5b4a:	4c 89 de             	mov    %r11,%rsi
    5b4d:	49 d1 ec             	shr    %r12
    5b50:	49 c1 e4 04          	shl    $0x4,%r12
    5b54:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5b59:	4c 89 65 b8          	mov    %r12,-0x48(%rbp)
    5b5d:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5b61:	4d 01 dc             	add    %r11,%r12
    5b64:	f6 45 b8 10          	testb  $0x10,-0x48(%rbp)
    5b68:	74 16                	je     5b80 <barriered_work+0x350>
          them->messages[them->messages_count++] = data->message; 
    5b6a:	48 83 c6 10          	add    $0x10,%rsi
    5b6e:	41 0f 11 03          	movups %xmm0,(%r11)
        for (; them->messages_count < min;) {
    5b72:	49 39 f4             	cmp    %rsi,%r12
    5b75:	74 19                	je     5b90 <barriered_work+0x360>
    5b77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          them->messages[them->messages_count++] = data->message; 
    5b80:	0f 11 06             	movups %xmm0,(%rsi)
    5b83:	48 83 c6 20          	add    $0x20,%rsi
    5b87:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
        for (; them->messages_count < min;) {
    5b8b:	49 39 f4             	cmp    %rsi,%r12
    5b8e:	75 f0                	jne    5b80 <barriered_work+0x350>
    5b90:	48 89 ce             	mov    %rcx,%rsi
    5b93:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    5b97:	4c 01 d6             	add    %r10,%rsi
    5b9a:	f6 c1 01             	test   $0x1,%cl
    5b9d:	0f 84 c5 fd ff ff    	je     5968 <barriered_work+0x138>
          them->messages[them->messages_count++] = data->message; 
    5ba3:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5baa:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    5bae:	e9 b5 fd ff ff       	jmp    5968 <barriered_work+0x138>
    5bb3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5bb8:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    5bc0:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    5bc8:	e9 74 fd ff ff       	jmp    5941 <barriered_work+0x111>
      for (int n = 0 ; n < data->thread_count; n++) {
    5bcd:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5bd3:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    5bda:	48 8d bb 88 01 00 00 	lea    0x188(%rbx),%rdi
    5be1:	45 31 ff             	xor    %r15d,%r15d
    5be4:	48 89 4d c8          	mov    %rcx,-0x38(%rbp)
    5be8:	48 89 7d c0          	mov    %rdi,-0x40(%rbp)
    5bec:	85 c0                	test   %eax,%eax
    5bee:	0f 8e 2e ff ff ff    	jle    5b22 <barriered_work+0x2f2>
    5bf4:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5bf8:	44 39 bb 30 01 00 00 	cmp    %r15d,0x130(%rbx)
    5bff:	0f 84 b6 00 00 00    	je     5cbb <barriered_work+0x48b>
        struct Data *them = data->mailboxes[n].higher;
    5c05:	4d 89 f8             	mov    %r15,%r8
    5c08:	49 c1 e0 05          	shl    $0x5,%r8
    5c0c:	4c 03 83 68 01 00 00 	add    0x168(%rbx),%r8
    5c13:	4d 8b 48 08          	mov    0x8(%r8),%r9
        for (; them->messages_count < min;) {
    5c17:	4d 8b 51 08          	mov    0x8(%r9),%r10
    5c1b:	49 63 79 10          	movslq 0x10(%r9),%rdi
    5c1f:	4c 39 d7             	cmp    %r10,%rdi
    5c22:	0f 8e 8a 00 00 00    	jle    5cb2 <barriered_work+0x482>
    5c28:	48 89 f9             	mov    %rdi,%rcx
    5c2b:	4c 8b 9b 08 01 00 00 	mov    0x108(%rbx),%r11
    5c32:	4d 8b 70 10          	mov    0x10(%r8),%r14
    5c36:	4c 29 d1             	sub    %r10,%rcx
          them->messages[them->messages_count++] = data->message; 
    5c39:	49 8b 11             	mov    (%r9),%rdx
    5c3c:	48 8d 41 ff          	lea    -0x1(%rcx),%rax
    5c40:	48 83 f8 02          	cmp    $0x2,%rax
    5c44:	0f 86 fe 00 00 00    	jbe    5d48 <barriered_work+0x518>
    5c4a:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    5c52:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    5c5a:	4c 8d 24 02          	lea    (%rdx,%rax,1),%r12
    5c5e:	4c 8d 2c 32          	lea    (%rdx,%rsi,1),%r13
    5c62:	4c 39 6d c8          	cmp    %r13,-0x38(%rbp)
    5c66:	73 68                	jae    5cd0 <barriered_work+0x4a0>
    5c68:	4c 8b 6d c0          	mov    -0x40(%rbp),%r13
    5c6c:	4d 39 ec             	cmp    %r13,%r12
    5c6f:	73 5f                	jae    5cd0 <barriered_work+0x4a0>
    5c71:	4c 8d 14 02          	lea    (%rdx,%rax,1),%r10
    5c75:	48 01 d6             	add    %rdx,%rsi
    5c78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5c80:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5c87:	49 83 c2 08          	add    $0x8,%r10
          them->messages[them->messages_count++] = data->message; 
    5c8b:	49 89 42 f8          	mov    %rax,-0x8(%r10)
        for (; them->messages_count < min;) {
    5c8f:	49 39 f2             	cmp    %rsi,%r10
    5c92:	75 ec                	jne    5c80 <barriered_work+0x450>
    5c94:	0f 1f 40 00          	nopl   0x0(%rax)
    5c98:	49 01 cb             	add    %rcx,%r11
    5c9b:	4c 01 f1             	add    %r14,%rcx
    5c9e:	4c 89 9b 08 01 00 00 	mov    %r11,0x108(%rbx)
    5ca5:	49 89 48 10          	mov    %rcx,0x10(%r8)
    5ca9:	49 89 79 08          	mov    %rdi,0x8(%r9)
    5cad:	48 89 44 fa f8       	mov    %rax,-0x8(%rdx,%rdi,8)
        asm volatile ("sfence" ::: "memory");
    5cb2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5cb5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5cbb:	49 83 c7 01          	add    $0x1,%r15
    5cbf:	44 39 f8             	cmp    %r15d,%eax
    5cc2:	0f 8f 30 ff ff ff    	jg     5bf8 <barriered_work+0x3c8>
    5cc8:	e9 55 fe ff ff       	jmp    5b22 <barriered_work+0x2f2>
    5ccd:	0f 1f 00             	nopl   (%rax)
    5cd0:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5cd7:	49 89 cd             	mov    %rcx,%r13
    5cda:	4c 89 e6             	mov    %r12,%rsi
    5cdd:	49 d1 ed             	shr    %r13
    5ce0:	49 c1 e5 04          	shl    $0x4,%r13
    5ce4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5ce9:	4c 89 6d b8          	mov    %r13,-0x48(%rbp)
    5ced:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5cf1:	4d 01 e5             	add    %r12,%r13
    5cf4:	f6 45 b8 10          	testb  $0x10,-0x48(%rbp)
    5cf8:	74 16                	je     5d10 <barriered_work+0x4e0>
          them->messages[them->messages_count++] = data->message; 
    5cfa:	48 83 c6 10          	add    $0x10,%rsi
    5cfe:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5d03:	4c 39 ee             	cmp    %r13,%rsi
    5d06:	74 18                	je     5d20 <barriered_work+0x4f0>
    5d08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          them->messages[them->messages_count++] = data->message; 
    5d10:	0f 11 06             	movups %xmm0,(%rsi)
    5d13:	48 83 c6 20          	add    $0x20,%rsi
    5d17:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
        for (; them->messages_count < min;) {
    5d1b:	4c 39 ee             	cmp    %r13,%rsi
    5d1e:	75 f0                	jne    5d10 <barriered_work+0x4e0>
    5d20:	48 89 ce             	mov    %rcx,%rsi
    5d23:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    5d27:	4c 01 d6             	add    %r10,%rsi
    5d2a:	f6 c1 01             	test   $0x1,%cl
    5d2d:	0f 84 65 ff ff ff    	je     5c98 <barriered_work+0x468>
          them->messages[them->messages_count++] = data->message; 
    5d33:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5d3a:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    5d3e:	e9 55 ff ff ff       	jmp    5c98 <barriered_work+0x468>
    5d43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5d48:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    5d50:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    5d58:	e9 14 ff ff ff       	jmp    5c71 <barriered_work+0x441>
    5d5d:	0f 1f 00             	nopl   (%rax)

0000000000005d60 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    5d60:	f3 0f 1e fa          	endbr64
    5d64:	55                   	push   %rbp
    5d65:	48 89 e5             	mov    %rsp,%rbp
    5d68:	53                   	push   %rbx
    5d69:	48 83 ec 08          	sub    $0x8,%rsp
    5d6d:	ff 15 75 42 00 00    	call   *0x4275(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    5d73:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    5d76:	e8 95 f5 ff ff       	call   5310 <barriered_work_ingest>
  barriered_work(data);
    5d7b:	48 89 df             	mov    %rbx,%rdi
}
    5d7e:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    5d82:	c9                   	leave
  barriered_work(data);
    5d83:	e9 a8 fa ff ff       	jmp    5830 <barriered_work>
    5d88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000005d90 <sendm>:
int sendm(struct BarrierTask *data) {
    5d90:	f3 0f 1e fa          	endbr64
    5d94:	55                   	push   %rbp
    5d95:	48 89 e5             	mov    %rsp,%rbp
    5d98:	41 57                	push   %r15
    5d9a:	41 56                	push   %r14
    5d9c:	41 55                	push   %r13
    5d9e:	41 54                	push   %r12
    5da0:	53                   	push   %rbx
    5da1:	48 83 ec 28          	sub    $0x28,%rsp
    5da5:	ff 15 3d 42 00 00    	call   *0x423d(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  if (data->sending == 1) {
    5dab:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
int sendm(struct BarrierTask *data) {
    5db2:	48 89 fa             	mov    %rdi,%rdx
  if (data->sending == 1) {
    5db5:	0f 85 a5 01 00 00    	jne    5f60 <sendm+0x1d0>
      for (int n = 0 ; n < data->thread_count; n++) {
    5dbb:	48 8d 9f 80 01 00 00 	lea    0x180(%rdi),%rbx
    5dc2:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    5dc8:	45 31 ff             	xor    %r15d,%r15d
    5dcb:	48 89 5d c8          	mov    %rbx,-0x38(%rbp)
    5dcf:	48 8d 9f 88 01 00 00 	lea    0x188(%rdi),%rbx
    5dd6:	48 89 5d c0          	mov    %rbx,-0x40(%rbp)
    5dda:	85 c0                	test   %eax,%eax
    5ddc:	0f 8e d6 00 00 00    	jle    5eb8 <sendm+0x128>
    5de2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (n == data->thread_index) { continue; }
    5de8:	44 39 ba 30 01 00 00 	cmp    %r15d,0x130(%rdx)
    5def:	0f 84 b6 00 00 00    	je     5eab <sendm+0x11b>
        struct Data *them = data->mailboxes[n].higher;
    5df5:	4d 89 f9             	mov    %r15,%r9
    5df8:	49 c1 e1 05          	shl    $0x5,%r9
    5dfc:	4c 03 8a 68 01 00 00 	add    0x168(%rdx),%r9
    5e03:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    5e07:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5e0b:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5e0f:	4d 39 c3             	cmp    %r8,%r11
    5e12:	0f 8d 8a 00 00 00    	jge    5ea2 <sendm+0x112>
    5e18:	4c 89 c6             	mov    %r8,%rsi
    5e1b:	48 8b 9a 08 01 00 00 	mov    0x108(%rdx),%rbx
    5e22:	4d 8b 71 10          	mov    0x10(%r9),%r14
    5e26:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5e29:	49 8b 0a             	mov    (%r10),%rcx
    5e2c:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5e30:	48 83 f8 02          	cmp    $0x2,%rax
    5e34:	0f 86 0e 01 00 00    	jbe    5f48 <sendm+0x1b8>
    5e3a:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5e42:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5e4a:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5e4e:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5e52:	4c 39 6d c8          	cmp    %r13,-0x38(%rbp)
    5e56:	73 78                	jae    5ed0 <sendm+0x140>
    5e58:	4c 8b 6d c0          	mov    -0x40(%rbp),%r13
    5e5c:	4d 39 ec             	cmp    %r13,%r12
    5e5f:	73 6f                	jae    5ed0 <sendm+0x140>
    5e61:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5e65:	48 01 cf             	add    %rcx,%rdi
    5e68:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5e70:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    5e77:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5e7b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5e7f:	4c 39 df             	cmp    %r11,%rdi
    5e82:	75 ec                	jne    5e70 <sendm+0xe0>
    5e84:	0f 1f 40 00          	nopl   0x0(%rax)
    5e88:	48 01 f3             	add    %rsi,%rbx
    5e8b:	4c 01 f6             	add    %r14,%rsi
    5e8e:	48 89 9a 08 01 00 00 	mov    %rbx,0x108(%rdx)
    5e95:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5e99:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5e9d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5ea2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5ea5:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    5eab:	49 83 c7 01          	add    $0x1,%r15
    5eaf:	44 39 f8             	cmp    %r15d,%eax
    5eb2:	0f 8f 30 ff ff ff    	jg     5de8 <sendm+0x58>
}
    5eb8:	48 83 c4 28          	add    $0x28,%rsp
    5ebc:	31 c0                	xor    %eax,%eax
    5ebe:	5b                   	pop    %rbx
    5ebf:	41 5c                	pop    %r12
    5ec1:	41 5d                	pop    %r13
    5ec3:	41 5e                	pop    %r14
    5ec5:	41 5f                	pop    %r15
    5ec7:	5d                   	pop    %rbp
    5ec8:	c3                   	ret
    5ec9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5ed0:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    5ed7:	49 89 f5             	mov    %rsi,%r13
    5eda:	4c 89 e7             	mov    %r12,%rdi
    5edd:	49 d1 ed             	shr    %r13
    5ee0:	49 c1 e5 04          	shl    $0x4,%r13
    5ee4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5ee9:	4c 89 6d b8          	mov    %r13,-0x48(%rbp)
    5eed:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5ef1:	4d 01 e5             	add    %r12,%r13
    5ef4:	f6 45 b8 10          	testb  $0x10,-0x48(%rbp)
    5ef8:	74 16                	je     5f10 <sendm+0x180>
          them->messages[them->messages_count++] = data->message; 
    5efa:	48 83 c7 10          	add    $0x10,%rdi
    5efe:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5f03:	4c 39 ef             	cmp    %r13,%rdi
    5f06:	74 18                	je     5f20 <sendm+0x190>
    5f08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          them->messages[them->messages_count++] = data->message; 
    5f10:	0f 11 07             	movups %xmm0,(%rdi)
    5f13:	48 83 c7 20          	add    $0x20,%rdi
    5f17:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5f1b:	4c 39 ef             	cmp    %r13,%rdi
    5f1e:	75 f0                	jne    5f10 <sendm+0x180>
    5f20:	48 89 f7             	mov    %rsi,%rdi
    5f23:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5f27:	4c 01 df             	add    %r11,%rdi
    5f2a:	40 f6 c6 01          	test   $0x1,%sil
    5f2e:	0f 84 54 ff ff ff    	je     5e88 <sendm+0xf8>
          them->messages[them->messages_count++] = data->message; 
    5f34:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    5f3b:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5f3f:	e9 44 ff ff ff       	jmp    5e88 <sendm+0xf8>
    5f44:	0f 1f 40 00          	nopl   0x0(%rax)
    5f48:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5f50:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5f58:	e9 04 ff ff ff       	jmp    5e61 <sendm+0xd1>
    5f5d:	0f 1f 00             	nopl   (%rax)
    5f60:	48 8d 3d ad 12 00 00 	lea    0x12ad(%rip),%rdi        # 7214 <_IO_stdin_used+0x214>
    5f67:	e8 a4 c3 ff ff       	call   2310 <puts@plt>
    5f6c:	e9 47 ff ff ff       	jmp    5eb8 <sendm+0x128>
    5f71:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5f7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005f80 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5f80:	f3 0f 1e fa          	endbr64
    5f84:	55                   	push   %rbp
    5f85:	48 89 e5             	mov    %rsp,%rbp
    5f88:	ff 15 5a 40 00 00    	call   *0x405a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
}
    5f8e:	31 c0                	xor    %eax,%eax
    5f90:	5d                   	pop    %rbp
    5f91:	c3                   	ret
    5f92:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5f9d:	0f 1f 00             	nopl   (%rax)

0000000000005fa0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5fa0:	f3 0f 1e fa          	endbr64
    5fa4:	55                   	push   %rbp
    5fa5:	48 89 e5             	mov    %rsp,%rbp
    5fa8:	ff 15 3a 40 00 00    	call   *0x403a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    5fae:	31 c0                	xor    %eax,%eax
    5fb0:	5d                   	pop    %rbp
    5fb1:	c3                   	ret
    5fb2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5fbd:	0f 1f 00             	nopl   (%rax)

0000000000005fc0 <after>:
int after(struct timespec left, struct timespec right) {
    5fc0:	f3 0f 1e fa          	endbr64
    5fc4:	55                   	push   %rbp
    5fc5:	48 89 e5             	mov    %rsp,%rbp
    5fc8:	ff 15 1a 40 00 00    	call   *0x401a(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  return left.tv_sec > right.tv_sec &&
    5fce:	31 c0                	xor    %eax,%eax
    5fd0:	48 39 d7             	cmp    %rdx,%rdi
    5fd3:	7e 08                	jle    5fdd <after+0x1d>
    5fd5:	31 c0                	xor    %eax,%eax
    5fd7:	48 39 ce             	cmp    %rcx,%rsi
    5fda:	0f 9f c0             	setg   %al
}
    5fdd:	5d                   	pop    %rbp
    5fde:	c3                   	ret
    5fdf:	90                   	nop

0000000000005fe0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5fe0:	f3 0f 1e fa          	endbr64
    5fe4:	55                   	push   %rbp
    5fe5:	48 89 e5             	mov    %rsp,%rbp
    5fe8:	ff 15 fa 3f 00 00    	call   *0x3ffa(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
  return 0;
    5fee:	31 c0                	xor    %eax,%eax
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5ff0:	4c 8b 5d 10          	mov    0x10(%rbp),%r11
    5ff4:	4c 8b 55 18          	mov    0x18(%rbp),%r10
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ff8:	48 39 d7             	cmp    %rdx,%rdi
    5ffb:	7f 18                	jg     6015 <within+0x35>
    5ffd:	4d 39 d8             	cmp    %r11,%r8
    6000:	0f 9e c2             	setle  %dl
    6003:	48 39 ce             	cmp    %rcx,%rsi
    6006:	0f 9e c0             	setle  %al
    6009:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    600b:	31 c0                	xor    %eax,%eax
    600d:	4d 39 d1             	cmp    %r10,%r9
    6010:	0f 9e c0             	setle  %al
    6013:	21 d0                	and    %edx,%eax
}
    6015:	5d                   	pop    %rbp
    6016:	c3                   	ret
    6017:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006020 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6020:	f3 0f 1e fa          	endbr64
    6024:	55                   	push   %rbp
    6025:	48 89 e5             	mov    %rsp,%rbp
    6028:	ff 15 ba 3f 00 00    	call   *0x3fba(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    602e:	48 8b 7d 10          	mov    0x10(%rbp),%rdi
    6032:	48 8b 75 30          	mov    0x30(%rbp),%rsi
    6036:	4c 8b 4d 20          	mov    0x20(%rbp),%r9
    603a:	4c 8b 55 28          	mov    0x28(%rbp),%r10
    603e:	4c 8b 45 40          	mov    0x40(%rbp),%r8
    6042:	4c 8b 5d 48          	mov    0x48(%rbp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6046:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
    604a:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  return left.tv_sec > right.tv_sec &&
    604e:	48 39 fe             	cmp    %rdi,%rsi
    6051:	7d 2d                	jge    6080 <overlap+0x60>
    6053:	48 39 ca             	cmp    %rcx,%rdx
    6056:	7d 60                	jge    60b8 <overlap+0x98>
    6058:	4d 39 da             	cmp    %r11,%r10
    605b:	7d 0a                	jge    6067 <overlap+0x47>
    return 1;
    605d:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6062:	4d 39 c1             	cmp    %r8,%r9
    6065:	7c 0f                	jl     6076 <overlap+0x56>
  return 0;
    6067:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6069:	4d 39 c1             	cmp    %r8,%r9
    606c:	7f 08                	jg     6076 <overlap+0x56>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    606e:	31 c0                	xor    %eax,%eax
    6070:	4d 39 da             	cmp    %r11,%r10
    6073:	0f 9e c0             	setle  %al
}
    6076:	5d                   	pop    %rbp
    6077:	c3                   	ret
    6078:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6080:	7e 56                	jle    60d8 <overlap+0xb8>
    6082:	48 39 ca             	cmp    %rcx,%rdx
    6085:	7f 39                	jg     60c0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6087:	75 31                	jne    60ba <overlap+0x9a>
    6089:	4d 39 c1             	cmp    %r8,%r9
    608c:	7c 2c                	jl     60ba <overlap+0x9a>
    return 1;
    608e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6093:	4d 39 da             	cmp    %r11,%r10
    6096:	7d de                	jge    6076 <overlap+0x56>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6098:	48 39 ca             	cmp    %rcx,%rdx
}
    609b:	5d                   	pop    %rbp
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    609c:	0f 94 c2             	sete   %dl
    609f:	48 39 fe             	cmp    %rdi,%rsi
    60a2:	0f 94 c0             	sete   %al
    60a5:	21 c2                	and    %eax,%edx
    60a7:	31 c0                	xor    %eax,%eax
    60a9:	4d 39 c1             	cmp    %r8,%r9
    60ac:	0f 94 c0             	sete   %al
    60af:	21 d0                	and    %edx,%eax
}
    60b1:	c3                   	ret
    60b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    60b8:	74 ad                	je     6067 <overlap+0x47>
  return 0;
    60ba:	31 c0                	xor    %eax,%eax
}
    60bc:	5d                   	pop    %rbp
    60bd:	c3                   	ret
    60be:	66 90                	xchg   %ax,%ax
  return left.tv_sec > right.tv_sec &&
    60c0:	4d 39 da             	cmp    %r11,%r10
    60c3:	7e c4                	jle    6089 <overlap+0x69>
    return 1;
    60c5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    60ca:	4d 39 c1             	cmp    %r8,%r9
    60cd:	7e ba                	jle    6089 <overlap+0x69>
    60cf:	eb a5                	jmp    6076 <overlap+0x56>
    60d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    60d8:	48 39 ca             	cmp    %rcx,%rdx
    60db:	7c 8a                	jl     6067 <overlap+0x47>
    60dd:	4d 39 c1             	cmp    %r8,%r9
    60e0:	7d ac                	jge    608e <overlap+0x6e>
    60e2:	48 39 ca             	cmp    %rcx,%rdx
    60e5:	74 87                	je     606e <overlap+0x4e>
  return 0;
    60e7:	31 c0                	xor    %eax,%eax
    60e9:	eb d1                	jmp    60bc <overlap+0x9c>
    60eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000060f0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    60f0:	f3 0f 1e fa          	endbr64
    60f4:	55                   	push   %rbp
    60f5:	48 89 e5             	mov    %rsp,%rbp
    60f8:	41 57                	push   %r15
    60fa:	41 56                	push   %r14
    60fc:	41 55                	push   %r13
    60fe:	41 54                	push   %r12
    6100:	53                   	push   %rbx
    6101:	48 83 ec 58          	sub    $0x58,%rsp
    6105:	ff 15 dd 3e 00 00    	call   *0x3edd(%rip)        # 9fe8 <mcount@GLIBC_2.2.5>
    610b:	41 89 f4             	mov    %esi,%r12d
  for (int x = 0 ; x < thread_count; x++) {
    610e:	85 f6                	test   %esi,%esi
    6110:	0f 8e df 02 00 00    	jle    63f5 <verify+0x305>
    6116:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    611a:	45 31 ff             	xor    %r15d,%r15d
    611d:	48 89 5d b8          	mov    %rbx,-0x48(%rbp)
    for (int z = 0 ; z < thread_count; z++) {
    6121:	48 89 5d c0          	mov    %rbx,-0x40(%rbp)
    6125:	45 31 ed             	xor    %r13d,%r13d
    6128:	45 89 e6             	mov    %r12d,%r14d
      if (z != x)  {
    612b:	45 39 ef             	cmp    %r13d,%r15d
    612e:	0f 84 27 02 00 00    	je     635b <verify+0x26b>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6134:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    6138:	8b 50 08             	mov    0x8(%rax),%edx
    613b:	85 d2                	test   %edx,%edx
    613d:	0f 8e 18 02 00 00    	jle    635b <verify+0x26b>
    6143:	48 89 5d 98          	mov    %rbx,-0x68(%rbp)
    6147:	45 31 e4             	xor    %r12d,%r12d
    614a:	44 89 6d 94          	mov    %r13d,-0x6c(%rbp)
    614e:	44 89 75 90          	mov    %r14d,-0x70(%rbp)
    6152:	4d 89 e6             	mov    %r12,%r14
    6155:	44 89 fa             	mov    %r15d,%edx
    6158:	48 8d 35 c1 10 00 00 	lea    0x10c1(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    615f:	bf 01 00 00 00       	mov    $0x1,%edi
    6164:	31 c0                	xor    %eax,%eax
    6166:	e8 15 c3 ff ff       	call   2480 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    616b:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    616f:	8b 40 08             	mov    0x8(%rax),%eax
    6172:	85 c0                	test   %eax,%eax
    6174:	0f 8e c3 01 00 00    	jle    633d <verify+0x24d>
    617a:	4c 89 f0             	mov    %r14,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    617d:	4c 89 75 88          	mov    %r14,-0x78(%rbp)
    6181:	31 db                	xor    %ebx,%ebx
    6183:	48 c1 e0 09          	shl    $0x9,%rax
    6187:	44 89 7d 84          	mov    %r15d,-0x7c(%rbp)
    618b:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    618f:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    6193:	4c 8b 08             	mov    (%rax),%r9
    6196:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    61a0:	4c 8b 65 c0          	mov    -0x40(%rbp),%r12
    61a4:	4c 8b 7d c8          	mov    -0x38(%rbp),%r15
    61a8:	49 89 de             	mov    %rbx,%r14
    61ab:	bf 01 00 00 00       	mov    $0x1,%edi
    61b0:	49 c1 e6 09          	shl    $0x9,%r14
    61b4:	48 8d 35 7a 10 00 00 	lea    0x107a(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    61bb:	49 8b 04 24          	mov    (%r12),%rax
    61bf:	4b 8b 8c 39 58 01 00 00 	mov    0x158(%r9,%r15,1),%rcx
    61c7:	4c 89 75 a8          	mov    %r14,-0x58(%rbp)
    61cb:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    61d3:	31 c0                	xor    %eax,%eax
    61d5:	e8 a6 c2 ff ff       	call   2480 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    61da:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    61de:	4c 8b 08             	mov    (%rax),%r9
    61e1:	4b 83 bc 39 58 01 00 00 00 	cmpq   $0x0,0x158(%r9,%r15,1)
    61ea:	0f 8e 34 01 00 00    	jle    6324 <verify+0x234>
    61f0:	4d 03 34 24          	add    (%r12),%r14
    61f4:	48 89 5d a0          	mov    %rbx,-0x60(%rbp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    61f8:	ba 01 00 00 00       	mov    $0x1,%edx
    61fd:	4d 89 f5             	mov    %r14,%r13
    6200:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    6207:	4d 85 f6             	test   %r14,%r14
    620a:	0f 8e 10 01 00 00    	jle    6320 <verify+0x230>
    6210:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6214:	49 89 d4             	mov    %rdx,%r12
    6217:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
    621b:	31 db                	xor    %ebx,%ebx
    621d:	49 c1 e4 05          	shl    $0x5,%r12
    6221:	49 83 ec 20          	sub    $0x20,%r12
    6225:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
    6229:	eb 32                	jmp    625d <verify+0x16d>
    622b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6230:	4c 39 c1             	cmp    %r8,%rcx
    6233:	0f 8d 47 01 00 00    	jge    6380 <verify+0x290>
    6239:	4c 39 d7             	cmp    %r10,%rdi
    623c:	7e 05                	jle    6243 <verify+0x153>
    623e:	49 39 c3             	cmp    %rax,%r11
    6241:	7c 75                	jl     62b8 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6243:	4c 39 d7             	cmp    %r10,%rdi
    6246:	0f 8d 9b 01 00 00    	jge    63e7 <verify+0x2f7>
    624c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6250:	48 83 c3 01          	add    $0x1,%rbx
    6254:	49 39 de             	cmp    %rbx,%r14
    6257:	0f 8e a2 00 00 00    	jle    62ff <verify+0x20f>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    625d:	49 8b 8f 48 01 00 00 	mov    0x148(%r15),%rcx
    6264:	48 89 d8             	mov    %rbx,%rax
    6267:	48 c1 e0 05          	shl    $0x5,%rax
    626b:	49 03 85 48 01 00 00 	add    0x148(%r13),%rax
    6272:	4c 01 e1             	add    %r12,%rcx
    6275:	48 8b 30             	mov    (%rax),%rsi
    6278:	48 8b 78 10          	mov    0x10(%rax),%rdi
    627c:	48 8b 11             	mov    (%rcx),%rdx
    627f:	4c 8b 41 08          	mov    0x8(%rcx),%r8
    6283:	4c 8b 51 10          	mov    0x10(%rcx),%r10
    6287:	4c 8b 59 18          	mov    0x18(%rcx),%r11
    628b:	48 8b 48 08          	mov    0x8(%rax),%rcx
    628f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6293:	48 39 d6             	cmp    %rdx,%rsi
    6296:	7c 98                	jl     6230 <verify+0x140>
    6298:	0f 8e 32 01 00 00    	jle    63d0 <verify+0x2e0>
    629e:	4c 39 c1             	cmp    %r8,%rcx
    62a1:	0f 8f e9 00 00 00    	jg     6390 <verify+0x2a0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    62a7:	75 a7                	jne    6250 <verify+0x160>
    62a9:	4c 39 d7             	cmp    %r10,%rdi
    62ac:	7f a2                	jg     6250 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    62ae:	49 39 c3             	cmp    %rax,%r11
    62b1:	7c 9d                	jl     6250 <verify+0x160>
    62b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    62b8:	49 89 c1             	mov    %rax,%r9
    62bb:	48 89 f9             	mov    %rdi,%rcx
    62be:	48 8d 35 c3 11 00 00 	lea    0x11c3(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    62c5:	31 c0                	xor    %eax,%eax
    62c7:	bf 01 00 00 00       	mov    $0x1,%edi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    62cc:	48 83 c3 01          	add    $0x1,%rbx
    62d0:	e8 ab c1 ff ff       	call   2480 <__printf_chk@plt>
    62d5:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    62d9:	4c 8b 6d a8          	mov    -0x58(%rbp),%r13
    62dd:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    62e0:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    62e4:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    62eb:	4c 8b 08             	mov    (%rax),%r9
    62ee:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    62f2:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    62f6:	49 39 de             	cmp    %rbx,%r14
    62f9:	0f 8f 5e ff ff ff    	jg     625d <verify+0x16d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    62ff:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    6303:	49 3b 97 58 01 00 00 	cmp    0x158(%r15),%rdx
    630a:	7d 14                	jge    6320 <verify+0x230>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    630c:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    6313:	48 83 c2 01          	add    $0x1,%rdx
    6317:	4d 85 f6             	test   %r14,%r14
    631a:	0f 8f f0 fe ff ff    	jg     6210 <verify+0x120>
    6320:	48 8b 5d a0          	mov    -0x60(%rbp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6324:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    6328:	48 83 c3 01          	add    $0x1,%rbx
    632c:	39 58 08             	cmp    %ebx,0x8(%rax)
    632f:	0f 8f 6b fe ff ff    	jg     61a0 <verify+0xb0>
    6335:	4c 8b 75 88          	mov    -0x78(%rbp),%r14
    6339:	44 8b 7d 84          	mov    -0x7c(%rbp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    633d:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    6341:	49 83 c6 01          	add    $0x1,%r14
    6345:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    6349:	0f 8f 06 fe ff ff    	jg     6155 <verify+0x65>
    634f:	48 8b 5d 98          	mov    -0x68(%rbp),%rbx
    6353:	44 8b 6d 94          	mov    -0x6c(%rbp),%r13d
    6357:	44 8b 75 90          	mov    -0x70(%rbp),%r14d
    for (int z = 0 ; z < thread_count; z++) {
    635b:	41 8d 45 01          	lea    0x1(%r13),%eax
    635f:	48 81 45 c0 b0 00 00 00 	addq   $0xb0,-0x40(%rbp)
    6367:	41 39 c6             	cmp    %eax,%r14d
    636a:	0f 84 96 00 00 00    	je     6406 <verify+0x316>
    6370:	41 89 c5             	mov    %eax,%r13d
    6373:	e9 b3 fd ff ff       	jmp    612b <verify+0x3b>
    6378:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6380:	0f 85 ca fe ff ff    	jne    6250 <verify+0x160>
    6386:	e9 b8 fe ff ff       	jmp    6243 <verify+0x153>
    638b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6390:	49 39 c3             	cmp    %rax,%r11
    6393:	7e 09                	jle    639e <verify+0x2ae>
    6395:	4c 39 d7             	cmp    %r10,%rdi
    6398:	0f 8c 1a ff ff ff    	jl     62b8 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    639e:	4c 39 d7             	cmp    %r10,%rdi
    63a1:	0f 8f a9 fe ff ff    	jg     6250 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    63a7:	49 39 c3             	cmp    %rax,%r11
    63aa:	0f 8d 08 ff ff ff    	jge    62b8 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    63b0:	48 39 d6             	cmp    %rdx,%rsi
    63b3:	0f 85 97 fe ff ff    	jne    6250 <verify+0x160>
    63b9:	4c 39 c1             	cmp    %r8,%rcx
    63bc:	0f 85 8e fe ff ff    	jne    6250 <verify+0x160>
    63c2:	4c 39 d7             	cmp    %r10,%rdi
    63c5:	0f 84 ed fe ff ff    	je     62b8 <verify+0x1c8>
    63cb:	e9 80 fe ff ff       	jmp    6250 <verify+0x160>
    63d0:	4c 39 c1             	cmp    %r8,%rcx
    63d3:	0f 8c 6a fe ff ff    	jl     6243 <verify+0x153>
    63d9:	4c 39 d7             	cmp    %r10,%rdi
    63dc:	7e c9                	jle    63a7 <verify+0x2b7>
    63de:	4c 39 c1             	cmp    %r8,%rcx
    63e1:	0f 85 69 fe ff ff    	jne    6250 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    63e7:	49 39 c3             	cmp    %rax,%r11
    63ea:	0f 8f 60 fe ff ff    	jg     6250 <verify+0x160>
    63f0:	e9 c3 fe ff ff       	jmp    62b8 <verify+0x1c8>
}
    63f5:	48 83 c4 58          	add    $0x58,%rsp
    63f9:	31 c0                	xor    %eax,%eax
    63fb:	5b                   	pop    %rbx
    63fc:	41 5c                	pop    %r12
    63fe:	41 5d                	pop    %r13
    6400:	41 5e                	pop    %r14
    6402:	41 5f                	pop    %r15
    6404:	5d                   	pop    %rbp
    6405:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
    6406:	48 81 45 b8 b0 00 00 00 	addq   $0xb0,-0x48(%rbp)
    640e:	45 89 f4             	mov    %r14d,%r12d
    6411:	41 8d 57 01          	lea    0x1(%r15),%edx
    6415:	45 39 ef             	cmp    %r13d,%r15d
    6418:	74 db                	je     63f5 <verify+0x305>
    641a:	41 89 d7             	mov    %edx,%r15d
    641d:	e9 ff fc ff ff       	jmp    6121 <verify+0x31>
    6422:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    642c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006430 <atexit>:
    6430:	f3 0f 1e fa          	endbr64
    6434:	48 8b 15 cd 3b 00 00 	mov    0x3bcd(%rip),%rdx        # a008 <__dso_handle>
    643b:	31 f6                	xor    %esi,%esi
    643d:	e9 8e c0 ff ff       	jmp    24d0 <__cxa_atexit@plt>
    6442:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    644c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006450 <__stack_chk_fail_local>:
    6450:	f3 0f 1e fa          	endbr64
    6454:	50                   	push   %rax
    6455:	58                   	pop    %rax
    6456:	48 83 ec 08          	sub    $0x8,%rsp
    645a:	e8 f1 be ff ff       	call   2350 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000006460 <_fini>:
    6460:	f3 0f 1e fa          	endbr64
    6464:	48 83 ec 08          	sub    $0x8,%rsp
    6468:	48 83 c4 08          	add    $0x8,%rsp
    646c:	c3                   	ret
