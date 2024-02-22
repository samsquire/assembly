
barrier-runtime-server-elapsed:     file format elf64-x86-64


Disassembly of section .init:

0000000000002000 <_init>:
    2000:	f3 0f 1e fa          	endbr64
    2004:	48 83 ec 08          	sub    $0x8,%rsp
    2008:	48 8d 05 81 12 00 00 	lea    0x1281(%rip),%rax        # 3290 <__gmon_start__>
    200f:	48 85 c0             	test   %rax,%rax
    2012:	74 02                	je     2016 <_init+0x16>
    2014:	ff d0                	call   *%rax
    2016:	48 83 c4 08          	add    $0x8,%rsp
    201a:	c3                   	ret

Disassembly of section .plt:

0000000000002020 <.plt>:
    2020:	ff 35 52 6e 00 00    	push   0x6e52(%rip)        # 8e78 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 54 6e 00 00    	jmp    *0x6e54(%rip)        # 8e80 <_GLOBAL_OFFSET_TABLE_+0x10>
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

Disassembly of section .plt.got:

00000000000022c0 <__cxa_finalize@plt>:
    22c0:	f3 0f 1e fa          	endbr64
    22c4:	ff 25 2e 6d 00 00    	jmp    *0x6d2e(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    22ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

00000000000022d0 <free@plt>:
    22d0:	f3 0f 1e fa          	endbr64
    22d4:	ff 25 ae 6b 00 00    	jmp    *0x6bae(%rip)        # 8e88 <free@GLIBC_2.2.5>
    22da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000022e0 <putchar@plt>:
    22e0:	f3 0f 1e fa          	endbr64
    22e4:	ff 25 a6 6b 00 00    	jmp    *0x6ba6(%rip)        # 8e90 <putchar@GLIBC_2.2.5>
    22ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000022f0 <puts@plt>:
    22f0:	f3 0f 1e fa          	endbr64
    22f4:	ff 25 9e 6b 00 00    	jmp    *0x6b9e(%rip)        # 8e98 <puts@GLIBC_2.2.5>
    22fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002300 <setsockopt@plt>:
    2300:	f3 0f 1e fa          	endbr64
    2304:	ff 25 96 6b 00 00    	jmp    *0x6b96(%rip)        # 8ea0 <setsockopt@GLIBC_2.2.5>
    230a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002310 <clock_gettime@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 8e 6b 00 00    	jmp    *0x6b8e(%rip)        # 8ea8 <clock_gettime@GLIBC_2.17>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002320 <strlen@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 86 6b 00 00    	jmp    *0x6b86(%rip)        # 8eb0 <strlen@GLIBC_2.2.5>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <__stack_chk_fail@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 7e 6b 00 00    	jmp    *0x6b7e(%rip)        # 8eb8 <__stack_chk_fail@GLIBC_2.4>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <io_uring_submit@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 76 6b 00 00    	jmp    *0x6b76(%rip)        # 8ec0 <io_uring_submit@LIBURING_2.0>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <nanosleep@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 6e 6b 00 00    	jmp    *0x6b6e(%rip)        # 8ec8 <nanosleep@GLIBC_2.2.5>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <strrchr@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 66 6b 00 00    	jmp    *0x6b66(%rip)        # 8ed0 <strrchr@GLIBC_2.2.5>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <close@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 5e 6b 00 00    	jmp    *0x6b5e(%rip)        # 8ed8 <close@GLIBC_2.2.5>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <strtok_r@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 56 6b 00 00    	jmp    *0x6b56(%rip)        # 8ee0 <strtok_r@GLIBC_2.2.5>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <read@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 4e 6b 00 00    	jmp    *0x6b4e(%rip)        # 8ee8 <read@GLIBC_2.2.5>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <calloc@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 46 6b 00 00    	jmp    *0x6b46(%rip)        # 8ef0 <calloc@GLIBC_2.2.5>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <strcmp@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 3e 6b 00 00    	jmp    *0x6b3e(%rip)        # 8ef8 <strcmp@GLIBC_2.2.5>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <__monstartup@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 36 6b 00 00    	jmp    *0x6b36(%rip)        # 8f00 <__monstartup@GLIBC_2.2.5>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <__memcpy_chk@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 2e 6b 00 00    	jmp    *0x6b2e(%rip)        # 8f08 <__memcpy_chk@GLIBC_2.3.4>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <stat@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 26 6b 00 00    	jmp    *0x6b26(%rip)        # 8f10 <stat@GLIBC_2.33>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <memcpy@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 1e 6b 00 00    	jmp    *0x6b1e(%rip)        # 8f18 <memcpy@GLIBC_2.14>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <io_uring_queue_init@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 16 6b 00 00    	jmp    *0x6b16(%rip)        # 8f20 <io_uring_queue_init@LIBURING_2.0>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <eventfd_write@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 0e 6b 00 00    	jmp    *0x6b0e(%rip)        # 8f28 <eventfd_write@GLIBC_2.7>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <malloc@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 06 6b 00 00    	jmp    *0x6b06(%rip)        # 8f30 <malloc@GLIBC_2.2.5>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <listen@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 fe 6a 00 00    	jmp    *0x6afe(%rip)        # 8f38 <listen@GLIBC_2.2.5>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <__strcpy_chk@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 f6 6a 00 00    	jmp    *0x6af6(%rip)        # 8f40 <__strcpy_chk@GLIBC_2.3.4>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <__io_uring_get_cqe@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 ee 6a 00 00    	jmp    *0x6aee(%rip)        # 8f48 <__io_uring_get_cqe@LIBURING_2.0>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <__printf_chk@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 e6 6a 00 00    	jmp    *0x6ae6(%rip)        # 8f50 <__printf_chk@GLIBC_2.3.4>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <bind@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 de 6a 00 00    	jmp    *0x6ade(%rip)        # 8f58 <bind@GLIBC_2.2.5>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <pthread_create@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 d6 6a 00 00    	jmp    *0x6ad6(%rip)        # 8f60 <pthread_create@GLIBC_2.34>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <open@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 ce 6a 00 00    	jmp    *0x6ace(%rip)        # 8f68 <open@GLIBC_2.2.5>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <perror@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 c6 6a 00 00    	jmp    *0x6ac6(%rip)        # 8f70 <perror@GLIBC_2.2.5>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <__cxa_atexit@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 be 6a 00 00    	jmp    *0x6abe(%rip)        # 8f78 <__cxa_atexit@GLIBC_2.2.5>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <exit@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 b6 6a 00 00    	jmp    *0x6ab6(%rip)        # 8f80 <exit@GLIBC_2.2.5>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <eventfd@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 ae 6a 00 00    	jmp    *0x6aae(%rip)        # 8f88 <eventfd@GLIBC_2.7>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <fwrite@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 a6 6a 00 00    	jmp    *0x6aa6(%rip)        # 8f90 <fwrite@GLIBC_2.2.5>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <__fprintf_chk@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 9e 6a 00 00    	jmp    *0x6a9e(%rip)        # 8f98 <__fprintf_chk@GLIBC_2.3.4>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <io_uring_register_eventfd@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 96 6a 00 00    	jmp    *0x6a96(%rip)        # 8fa0 <io_uring_register_eventfd@LIBURING_2.0>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <pthread_join@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 8e 6a 00 00    	jmp    *0x6a8e(%rip)        # 8fa8 <pthread_join@GLIBC_2.34>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <strerror@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 86 6a 00 00    	jmp    *0x6a86(%rip)        # 8fb0 <strerror@GLIBC_2.2.5>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <__ctype_tolower_loc@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 7e 6a 00 00    	jmp    *0x6a7e(%rip)        # 8fb8 <__ctype_tolower_loc@GLIBC_2.3>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002540 <__sprintf_chk@plt>:
    2540:	f3 0f 1e fa          	endbr64
    2544:	ff 25 76 6a 00 00    	jmp    *0x6a76(%rip)        # 8fc0 <__sprintf_chk@GLIBC_2.3.4>
    254a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002550 <socket@plt>:
    2550:	f3 0f 1e fa          	endbr64
    2554:	ff 25 6e 6a 00 00    	jmp    *0x6a6e(%rip)        # 8fc8 <socket@GLIBC_2.2.5>
    255a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000002560 <fatal_error>:
struct Snapshot {
  struct timespec start;
  struct timespec end;
};

void fatal_error(const char *syscall) {
    2560:	f3 0f 1e fa          	endbr64
    2564:	55                   	push   %rbp
    2565:	48 89 e5             	mov    %rsp,%rbp
    2568:	ff 15 7a 6a 00 00    	call   *0x6a7a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    perror(syscall);
    256e:	e8 2d ff ff ff       	call   24a0 <perror@plt>
    exit(1);
    2573:	bf 01 00 00 00       	mov    $0x1,%edi
    2578:	e8 43 ff ff ff       	call   24c0 <exit@plt>

000000000000257d <copy_file_contents.cold>:
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");
    257d:	48 8d 3d 7b 3c 00 00 	lea    0x3c7b(%rip),%rdi        # 61ff <_IO_stdin_used+0x1ff>
    2584:	e8 d7 ff ff ff       	call   2560 <fatal_error>

0000000000002589 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    2589:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
    258f:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2597:	0f 0b                	ud2

0000000000002599 <add_read_request.cold>:
    2599:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25a1:	0f 0b                	ud2

00000000000025a3 <_send_static_string_content.cold>:
    25a3:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    25a9:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25b1:	0f 0b                	ud2

00000000000025b3 <add_accept_request.cold>:
    25b3:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25bb:	0f 0b                	ud2

00000000000025bd <io_thread.cold>:
        break;
      }
      printf("Received wait finished\n");
      struct Request *req = (struct Request *) cqe->user_data;
      if (ret < 0)
          fatal_error("io_uring_wait_cqe");
    25bd:	48 8d 3d 0b 3c 00 00 	lea    0x3c0b(%rip),%rdi        # 61cf <_IO_stdin_used+0x1cf>
    25c4:	e8 97 ff ff ff       	call   2560 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    25c9:	48 8d 3d 83 3b 00 00 	lea    0x3b83(%rip),%rdi        # 6153 <_IO_stdin_used+0x153>
    25d0:	e8 8b ff ff ff       	call   2560 <fatal_error>
    fatal_error("listen()");
    25d5:	48 8d 3d 97 3b 00 00 	lea    0x3b97(%rip),%rdi        # 6173 <_IO_stdin_used+0x173>
    25dc:	e8 7f ff ff ff       	call   2560 <fatal_error>
    25e1:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25e9:	0f 0b                	ud2
    25eb:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25f3:	0f 0b                	ud2
      fatal_error("socket()");
    25f5:	48 8d 3d 4e 3b 00 00 	lea    0x3b4e(%rip),%rdi        # 614a <_IO_stdin_used+0x14a>
    25fc:	e8 5f ff ff ff       	call   2560 <fatal_error>
      fatal_error("bind()");
    2601:	48 8d 3d 64 3b 00 00 	lea    0x3b64(%rip),%rdi        # 616c <_IO_stdin_used+0x16c>
    2608:	e8 53 ff ff ff       	call   2560 <fatal_error>
    260d:	0f 1f 00             	nopl   (%rax)

0000000000002610 <main>:
    }


  return 0;
}
int main() {
    2610:	f3 0f 1e fa          	endbr64
    2614:	55                   	push   %rbp
    2615:	48 89 e5             	mov    %rsp,%rbp
    2618:	41 57                	push   %r15
    261a:	41 56                	push   %r14
    261c:	41 55                	push   %r13
    261e:	41 54                	push   %r12
    2620:	53                   	push   %rbx
    2621:	48 83 ec 68          	sub    $0x68,%rsp
    2625:	ff 15 bd 69 00 00    	call   *0x69bd(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    262b:	48 8d 3d 96 3e 00 00 	lea    0x3e96(%rip),%rdi        # 64c8 <_IO_stdin_used+0x4c8>
    2632:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    263b:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    263f:	31 c0                	xor    %eax,%eax
    2641:	e8 aa fc ff ff       	call   22f0 <puts@plt>
    2646:	bf 0a 00 00 00       	mov    $0xa,%edi
    264b:	e8 90 fc ff ff       	call   22e0 <putchar@plt>
    2650:	48 8d 3d db 3b 00 00 	lea    0x3bdb(%rip),%rdi        # 6232 <_IO_stdin_used+0x232>
    2657:	e8 94 fc ff ff       	call   22f0 <puts@plt>
    265c:	ba 06 00 00 00       	mov    $0x6,%edx
    2661:	48 8d 35 e6 3b 00 00 	lea    0x3be6(%rip),%rsi        # 624e <_IO_stdin_used+0x24e>
    2668:	31 c0                	xor    %eax,%eax
    266a:	bf 01 00 00 00       	mov    $0x1,%edi
    266f:	e8 ec fd ff ff       	call   2460 <__printf_chk@plt>
    2674:	ba 09 00 00 00       	mov    $0x9,%edx
    2679:	48 8d 35 e8 3b 00 00 	lea    0x3be8(%rip),%rsi        # 6268 <_IO_stdin_used+0x268>
    2680:	31 c0                	xor    %eax,%eax
    2682:	bf 01 00 00 00       	mov    $0x1,%edi
    2687:	e8 d4 fd ff ff       	call   2460 <__printf_chk@plt>
    268c:	ba 01 00 00 00       	mov    $0x1,%edx
    2691:	48 8d 35 e4 3b 00 00 	lea    0x3be4(%rip),%rsi        # 627c <_IO_stdin_used+0x27c>
    2698:	31 c0                	xor    %eax,%eax
    269a:	bf 01 00 00 00       	mov    $0x1,%edi
    269f:	e8 bc fd ff ff       	call   2460 <__printf_chk@plt>
    26a4:	ba 01 00 00 00       	mov    $0x1,%edx
    26a9:	48 8d 35 dd 3b 00 00 	lea    0x3bdd(%rip),%rsi        # 628d <_IO_stdin_used+0x28d>
    26b0:	31 c0                	xor    %eax,%eax
    26b2:	bf 01 00 00 00       	mov    $0x1,%edi
    26b7:	e8 a4 fd ff ff       	call   2460 <__printf_chk@plt>
    26bc:	ba 01 00 00 00       	mov    $0x1,%edx
    26c1:	48 8d 35 dd 3b 00 00 	lea    0x3bdd(%rip),%rsi        # 62a5 <_IO_stdin_used+0x2a5>
    26c8:	31 c0                	xor    %eax,%eax
    26ca:	bf 01 00 00 00       	mov    $0x1,%edi
    26cf:	e8 8c fd ff ff       	call   2460 <__printf_chk@plt>
    26d4:	ba 01 00 00 00       	mov    $0x1,%edx
    26d9:	48 8d 35 48 3e 00 00 	lea    0x3e48(%rip),%rsi        # 6528 <_IO_stdin_used+0x528>
    26e0:	31 c0                	xor    %eax,%eax
    26e2:	bf 01 00 00 00       	mov    $0x1,%edi
    26e7:	e8 74 fd ff ff       	call   2460 <__printf_chk@plt>
    26ec:	ba 01 00 00 00       	mov    $0x1,%edx
    26f1:	48 8d 35 60 3e 00 00 	lea    0x3e60(%rip),%rsi        # 6558 <_IO_stdin_used+0x558>
    26f8:	31 c0                	xor    %eax,%eax
    26fa:	bf 01 00 00 00       	mov    $0x1,%edi
    26ff:	e8 5c fd ff ff       	call   2460 <__printf_chk@plt>
    2704:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2709:	48 8d 35 b1 3b 00 00 	lea    0x3bb1(%rip),%rsi        # 62c1 <_IO_stdin_used+0x2c1>
    2710:	31 c0                	xor    %eax,%eax
    2712:	bf 01 00 00 00       	mov    $0x1,%edi
    2717:	e8 44 fd ff ff       	call   2460 <__printf_chk@plt>
    271c:	ba 0a 00 00 00       	mov    $0xa,%edx
    2721:	48 8d 35 b3 3b 00 00 	lea    0x3bb3(%rip),%rsi        # 62db <_IO_stdin_used+0x2db>
    2728:	31 c0                	xor    %eax,%eax
    272a:	bf 01 00 00 00       	mov    $0x1,%edi
    272f:	e8 2c fd ff ff       	call   2460 <__printf_chk@plt>
    2734:	48 8d 3d 93 39 00 00 	lea    0x3993(%rip),%rdi        # 60ce <_IO_stdin_used+0xce>
    273b:	e8 b0 fb ff ff       	call   22f0 <puts@plt>
  printf("intrathread message buffer size = %ld\n", messages_limit);
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  struct ProtectedState *protected_state = calloc(1, sizeof(struct ProtectedState));
    2740:	be 18 00 00 00       	mov    $0x18,%esi
    2745:	bf 01 00 00 00       	mov    $0x1,%edi
    274a:	e8 51 fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    274f:	be 98 00 00 00       	mov    $0x98,%esi
    2754:	bf 09 00 00 00       	mov    $0x9,%edi
  struct ProtectedState *protected_state = calloc(1, sizeof(struct ProtectedState));
    2759:	48 89 45 80          	mov    %rax,-0x80(%rbp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    275d:	e8 3e fc ff ff       	call   23a0 <calloc@plt>
  int barrier_count = thread_count;
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2762:	be 10 00 00 00       	mov    $0x10,%esi
    2767:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    276c:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2770:	e8 2b fc ff ff       	call   23a0 <calloc@plt>
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2775:	be 10 00 00 00       	mov    $0x10,%esi
    277a:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    277f:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2785:	48 89 c3             	mov    %rax,%rbx
    2788:	48 89 45 88          	mov    %rax,-0x78(%rbp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    278c:	e8 0f fc ff ff       	call   23a0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    2791:	4c 8b 45 b8          	mov    -0x48(%rbp),%r8
    }
  }
  int external_thread_index = 0;
    2795:	c7 45 90 00 00 00 00 	movl   $0x0,-0x70(%rbp)
      buffers[x].buffer[y].available = 0;
    279c:	31 c9                	xor    %ecx,%ecx
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    279e:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
    27a2:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    27a9:	4c 89 85 78 ff ff ff 	mov    %r8,-0x88(%rbp)
    thread_data[x].thread_index = x;
    27b0:	41 89 08             	mov    %ecx,(%r8)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    27b3:	be 10 00 00 00       	mov    $0x10,%esi
    27b8:	bf 64 00 00 00       	mov    $0x64,%edi
      for (int y = 0 ; y < total_barrier_count ; y++) {
    27bd:	31 db                	xor    %ebx,%ebx
    thread_data[x].threads = thread_data;
    27bf:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
    thread_data[x].task_count = total_barrier_count;
    27c6:	41 c7 40 28 07 00 00 00 	movl   $0x7,0x28(%r8)
    27ce:	89 4d b8             	mov    %ecx,-0x48(%rbp)
    thread_data[x].threads = thread_data;
    27d1:	49 89 40 10          	mov    %rax,0x10(%r8)
    thread_data[x].thread_count = thread_count;
    27d5:	48 8b 05 14 42 00 00 	mov    0x4214(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    thread_data[x].thread_index = x;
    27dc:	48 89 4d a8          	mov    %rcx,-0x58(%rbp)
    thread_data[x].thread_count = thread_count;
    27e0:	49 89 40 18          	mov    %rax,0x18(%r8)
    thread_data[x].protected_state = protected_state;
    27e4:	48 8b 45 80          	mov    -0x80(%rbp),%rax
    27e8:	4c 89 45 b0          	mov    %r8,-0x50(%rbp)
    27ec:	49 89 40 30          	mov    %rax,0x30(%r8)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    27f0:	e8 ab fb ff ff       	call   23a0 <calloc@plt>
    27f5:	4c 8b 45 b0          	mov    -0x50(%rbp),%r8
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27f9:	be 10 00 00 00       	mov    $0x10,%esi
    27fe:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2803:	49 89 40 50          	mov    %rax,0x50(%r8)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2807:	e8 94 fb ff ff       	call   23a0 <calloc@plt>
    280c:	4c 8b 45 b0          	mov    -0x50(%rbp),%r8
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2810:	be 28 00 00 00       	mov    $0x28,%esi
    thread_data[x].timestamp_count = 0;
    2815:	66 0f 6f 15 b3 41 00 00 	movdqa 0x41b3(%rip),%xmm2        # 69d0 <_IO_stdin_used+0x9d0>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    281d:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2822:	49 89 40 58          	mov    %rax,0x58(%r8)
    thread_data[x].timestamp_count = 0;
    2826:	41 0f 11 50 68       	movups %xmm2,0x68(%r8)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    282b:	e8 70 fb ff ff       	call   23a0 <calloc@plt>
    2830:	4c 8b 45 b0          	mov    -0x50(%rbp),%r8
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2834:	be 00 02 00 00       	mov    $0x200,%esi
    thread_data[x].task_timestamp_count = 0;
    2839:	66 0f 6f 1d 8f 41 00 00 	movdqa 0x418f(%rip),%xmm3        # 69d0 <_IO_stdin_used+0x9d0>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2841:	bf 07 00 00 00       	mov    $0x7,%edi
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2846:	49 89 40 78          	mov    %rax,0x78(%r8)
    thread_data[x].task_timestamp_count = 0;
    284a:	41 0f 11 98 80 00 00 00 	movups %xmm3,0x80(%r8)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2852:	e8 49 fb ff ff       	call   23a0 <calloc@plt>
      thread_data[x].tasks = barriers;
    2857:	4c 8b 45 b0          	mov    -0x50(%rbp),%r8
        thread_data[x].tasks[y].sending = 1;
    285b:	49 89 c7             	mov    %rax,%r15
      thread_data[x].tasks = barriers;
    285e:	49 89 40 20          	mov    %rax,0x20(%r8)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2862:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (x == y) {
    2868:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
            thread_data[x].tasks[y].protected = do_protected_write; 
    286c:	4c 63 eb             	movslq %ebx,%r13
    286f:	4d 89 ee             	mov    %r13,%r14
    2872:	89 45 94             	mov    %eax,-0x6c(%rbp)
    2875:	49 c1 e6 09          	shl    $0x9,%r14
        if (x == y) {
    2879:	39 c3                	cmp    %eax,%ebx
    287b:	0f 84 bf 09 00 00    	je     3240 <main+0xc30>
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2881:	be 20 00 00 00       	mov    $0x20,%esi
    2886:	bf 06 00 00 00       	mov    $0x6,%edi
    288b:	e8 10 fb ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    2890:	89 5d a0             	mov    %ebx,-0x60(%rbp)
    2893:	4c 89 6d 98          	mov    %r13,-0x68(%rbp)
    2897:	4c 8d a0 c0 00 00 00 	lea    0xc0(%rax),%r12
    289e:	4b 89 84 37 b0 01 00 00 	mov    %rax,0x1b0(%r15,%r14,1)
        for (int b = 0 ; b < thread_count ; b++) {
    28a6:	49 89 c7             	mov    %rax,%r15
    28a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    28b0:	be 08 00 00 00       	mov    $0x8,%esi
    28b5:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < thread_count ; b++) {
    28ba:	49 83 c7 20          	add    $0x20,%r15
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    28be:	e8 dd fa ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    28c3:	be 08 00 00 00       	mov    $0x8,%esi
    28c8:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    28cd:	49 89 c5             	mov    %rax,%r13
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    28d0:	e8 cb fa ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    28d5:	be 18 00 00 00       	mov    $0x18,%esi
    28da:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    28df:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    28e2:	e8 b9 fa ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    28e7:	66 0f 6f 05 f1 40 00 00 	movdqa 0x40f1(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
          mailboxes[b].higher = &data[1];
    28ef:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    28f3:	49 89 47 e0          	mov    %rax,-0x20(%r15)
          mailboxes[b].higher = &data[1];
    28f7:	49 89 77 e8          	mov    %rsi,-0x18(%r15)
          data[0].messages = messages;
    28fb:	4c 89 28             	mov    %r13,(%rax)
          data[1].messages = messages2;
    28fe:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    2902:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    2906:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < thread_count ; b++) {
    290a:	4d 39 e7             	cmp    %r12,%r15
    290d:	75 a1                	jne    28b0 <main+0x2a0>
        char *message = malloc(sizeof(char) * 256);
    290f:	be 01 00 00 00       	mov    $0x1,%esi
    2914:	bf 00 01 00 00       	mov    $0x100,%edi
    2919:	8b 5d a0             	mov    -0x60(%rbp),%ebx
    291c:	4c 8b 6d 98          	mov    -0x68(%rbp),%r13
    2920:	e8 7b fa ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2925:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    292a:	49 89 c4             	mov    %rax,%r12
        struct Message *messaged = malloc(sizeof(struct Message));
    292d:	e8 ee fa ff ff       	call   2420 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2932:	44 8b 45 b8          	mov    -0x48(%rbp),%r8d
    2936:	4c 89 e7             	mov    %r12,%rdi
    2939:	41 89 d9             	mov    %ebx,%r9d
    293c:	48 89 45 a0          	mov    %rax,-0x60(%rbp)
    2940:	48 8d 0d 39 3c 00 00 	lea    0x3c39(%rip),%rcx        # 6580 <_IO_stdin_used+0x580>
    2947:	ba 00 01 00 00       	mov    $0x100,%edx
    294c:	31 c0                	xor    %eax,%eax
    294e:	be 01 00 00 00       	mov    $0x1,%esi
    2953:	e8 e8 fb ff ff       	call   2540 <__sprintf_chk@plt>
        messaged->message = message;
    2958:	4c 8b 55 a0          	mov    -0x60(%rbp),%r10
        messaged->thread_index = x;
    295c:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2960:	ba ab aa aa aa       	mov    $0xaaaaaaab,%edx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2965:	be 20 00 00 00       	mov    $0x20,%esi
    296a:	bf 3f 42 0f 00       	mov    $0xf423f,%edi
        messaged->thread_index = x;
    296f:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2973:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
        messaged->task_index = y;
    2977:	4d 89 6a 10          	mov    %r13,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    297b:	44 8d 6b 01          	lea    0x1(%rbx),%r13d
    297f:	4c 8b 78 20          	mov    0x20(%rax),%r15
    2983:	44 89 e8             	mov    %r13d,%eax
    2986:	44 89 e9             	mov    %r13d,%ecx
        messaged->message = message;
    2989:	4d 89 22             	mov    %r12,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    298c:	48 0f af c2          	imul   %rdx,%rax
    2990:	4f 8d 24 37          	lea    (%r15,%r14,1),%r12
        thread_data[x].tasks[y].message = messaged;
    2994:	4d 89 94 24 c8 01 00 00 	mov    %r10,0x1c8(%r12)
        thread_data[x].tasks[y].snapshot_count = 999999;
    299c:	49 c7 84 24 98 01 00 00 3f 42 0f 00 	movq   $0xf423f,0x198(%r12)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    29a8:	48 c1 e8 22          	shr    $0x22,%rax
    29ac:	8d 04 40             	lea    (%rax,%rax,2),%eax
    29af:	01 c0                	add    %eax,%eax
    29b1:	29 c1                	sub    %eax,%ecx
    29b3:	41 89 8c 24 d0 01 00 00 	mov    %ecx,0x1d0(%r12)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    29bb:	e8 e0 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].thread_index = x;
    29c0:	8b 4d b8             	mov    -0x48(%rbp),%ecx
        thread_data[x].tasks[y].task_index = y;
    29c3:	41 89 1c 24          	mov    %ebx,(%r12)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    29c7:	49 89 84 24 90 01 00 00 	mov    %rax,0x190(%r12)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    29cf:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    29d3:	49 c7 84 24 a0 01 00 00 00 00 00 00 	movq   $0x0,0x1a0(%r12)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    29df:	49 89 84 24 28 01 00 00 	mov    %rax,0x128(%r12)
        thread_data[x].tasks[y].available = 1;
    29e7:	48 8b 05 0a 40 00 00 	mov    0x400a(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
        thread_data[x].tasks[y].thread_index = x;
    29ee:	41 89 8c 24 30 01 00 00 	mov    %ecx,0x130(%r12)
        thread_data[x].tasks[y].available = 1;
    29f6:	49 89 84 24 80 01 00 00 	mov    %rax,0x180(%r12)
        thread_data[x].tasks[y].sending = 1;
    29fe:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
        thread_data[x].tasks[y].arrived = 0;
    2a08:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
        thread_data[x].tasks[y].thread_count = thread_count;
    2a14:	41 c7 84 24 34 01 00 00 06 00 00 00 	movl   $0x6,0x134(%r12)
        thread_data[x].tasks[y].sending = 1;
    2a20:	49 89 84 24 c0 01 00 00 	mov    %rax,0x1c0(%r12)
        if (y == barrier_count - 1) {
    2a28:	83 fb 05             	cmp    $0x5,%ebx
    2a2b:	0f 84 ef 07 00 00    	je     3220 <main+0xc10>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2a31:	8b 45 94             	mov    -0x6c(%rbp),%eax
    2a34:	39 c3                	cmp    %eax,%ebx
    2a36:	75 60                	jne    2a98 <main+0x488>
    2a38:	8b 5d 90             	mov    -0x70(%rbp),%ebx
    2a3b:	85 db                	test   %ebx,%ebx
    2a3d:	7f 59                	jg     2a98 <main+0x488>
    2a3f:	89 ca                	mov    %ecx,%edx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2a41:	bf 01 00 00 00       	mov    $0x1,%edi
    2a46:	48 8d 35 5b 3b 00 00 	lea    0x3b5b(%rip),%rsi        # 65a8 <_IO_stdin_used+0x5a8>
    2a4d:	31 c0                	xor    %eax,%eax
    2a4f:	e8 0c fa ff ff       	call   2460 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a54:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    2a58:	48 63 c3             	movslq %ebx,%rax
    2a5b:	48 8b 7d 88          	mov    -0x78(%rbp),%rdi
    2a5f:	48 89 c1             	mov    %rax,%rcx
    2a62:	48 c1 e0 04          	shl    $0x4,%rax
    2a66:	48 01 f8             	add    %rdi,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a69:	4c 8b 7a 20          	mov    0x20(%rdx),%r15
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a6d:	48 89 42 38          	mov    %rax,0x38(%rdx)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a71:	48 8d 05 88 2c 00 00 	lea    0x2c88(%rip),%rax        # 5700 <barriered_work_ingest>
    2a78:	4b 89 84 37 18 01 00 00 	mov    %rax,0x118(%r15,%r14,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a80:	8d 41 01             	lea    0x1(%rcx),%eax
    2a83:	89 45 90             	mov    %eax,-0x70(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2a86:	41 83 fd 07          	cmp    $0x7,%r13d
    2a8a:	74 21                	je     2aad <main+0x49d>
  int external_thread_index = 0;
    2a8c:	44 89 eb             	mov    %r13d,%ebx
    2a8f:	e9 d4 fd ff ff       	jmp    2868 <main+0x258>
    2a94:	0f 1f 40 00          	nopl   0x0(%rax)
            thread_data[x].tasks[y].run = barriered_work; 
    2a98:	48 8d 05 d1 28 00 00 	lea    0x28d1(%rip),%rax        # 5370 <barriered_work>
    2a9f:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2aa7:	41 83 fd 07          	cmp    $0x7,%r13d
    2aab:	75 df                	jne    2a8c <main+0x47c>

          }
        }
      }
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2aad:	48 8d 05 4c 09 00 00 	lea    0x94c(%rip),%rax        # 3400 <barriered_reset>
    2ab4:	48 8b 4d a8          	mov    -0x58(%rbp),%rcx
    2ab8:	4c 8b 45 b0          	mov    -0x50(%rbp),%r8
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2abc:	41 c7 87 80 0c 00 00 00 00 00 00 	movl   $0x0,0xc80(%r15)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2ac7:	49 89 87 18 0d 00 00 	mov    %rax,0xd18(%r15)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
      thread_data[x].tasks[barrier_count].thread_index = x; 
    2ace:	8b 45 b8             	mov    -0x48(%rbp),%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2ad1:	48 83 c1 01          	add    $0x1,%rcx
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2ad5:	4d 89 87 28 0d 00 00 	mov    %r8,0xd28(%r15)
  for (int x = 0 ; x < total_threads ; x++) {
    2adc:	49 81 c0 98 00 00 00 	add    $0x98,%r8
      thread_data[x].tasks[barrier_count].thread_index = x; 
    2ae3:	41 89 87 30 0d 00 00 	mov    %eax,0xd30(%r15)
      thread_data[x].tasks[barrier_count].available = 1; 
    2aea:	48 8b 05 07 3f 00 00 	mov    0x3f07(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2af1:	41 c7 87 00 0c 00 00 06 00 00 00 	movl   $0x6,0xc00(%r15)
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
    2afc:	41 c7 87 34 0d 00 00 06 00 00 00 	movl   $0x6,0xd34(%r15)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2b07:	41 c7 87 c4 0d 00 00 06 00 00 00 	movl   $0x6,0xdc4(%r15)
      thread_data[x].tasks[barrier_count].available = 1; 
    2b12:	49 89 87 80 0d 00 00 	mov    %rax,0xd80(%r15)
  for (int x = 0 ; x < total_threads ; x++) {
    2b19:	48 83 f9 09          	cmp    $0x9,%rcx
    2b1d:	0f 85 8d fc ff ff    	jne    27b0 <main+0x1a0>
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].threads = thread_data;
    2b23:	4c 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%r8
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b2a:	be 38 00 00 00       	mov    $0x38,%esi
    2b2f:	bf 09 00 00 00       	mov    $0x9,%edi
  thread_data[thread_count].thread_count = thread_count;
  thread_data[thread_count].thread_index = 0;

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
  for (int x = 0 ; x < thread_count ; x++) {
    2b34:	45 31 f6             	xor    %r14d,%r14d
    2b37:	4c 8d 25 42 09 00 00 	lea    0x942(%rip),%r12        # 3480 <barriered_thread>
    thread_data[n].tasks[0].scheduled = 1;
    2b3e:	49 8b 40 20          	mov    0x20(%r8),%rax
    2b42:	4c 89 45 a8          	mov    %r8,-0x58(%rbp)
    thread_data[x].threads = thread_data;
    2b46:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    thread_data[x].thread_count = thread_count;
    2b4d:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    thread_data[x].thread_index = x;
    2b58:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    thread_data[x].task_count = total_barrier_count;
    2b63:	41 c7 80 50 04 00 00 07 00 00 00 	movl   $0x7,0x450(%r8)
    thread_data[n].tasks[0].scheduled = 1;
    2b6e:	c7 80 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rax)
    2b78:	49 8b 80 b8 00 00 00 	mov    0xb8(%r8),%rax
    2b7f:	c7 80 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rax)
    2b89:	49 8b 80 50 01 00 00 	mov    0x150(%r8),%rax
    2b90:	c7 80 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rax)
    2b9a:	49 8b 80 e8 01 00 00 	mov    0x1e8(%r8),%rax
    2ba1:	c7 80 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rax)
    2bab:	49 8b 80 80 02 00 00 	mov    0x280(%r8),%rax
    2bb2:	c7 80 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rax)
    2bbc:	49 8b 80 18 03 00 00 	mov    0x318(%r8),%rax
    2bc3:	c7 80 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rax)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bcd:	e8 ce f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bd2:	be 38 00 00 00       	mov    $0x38,%esi
    2bd7:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bdc:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bdf:	e8 bc f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2be4:	be 38 00 00 00       	mov    $0x38,%esi
    2be9:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bee:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bf2:	e8 a9 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bf7:	be 08 00 00 00       	mov    $0x8,%esi
    2bfc:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c01:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2c05:	e8 96 f7 ff ff       	call   23a0 <calloc@plt>
  thread_data[thread_count].task_count = total_barrier_count;
    2c0a:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    2c0e:	ba 06 00 00 00       	mov    $0x6,%edx
    2c13:	48 8d 35 d5 36 00 00 	lea    0x36d5(%rip),%rsi        # 62ef <_IO_stdin_used+0x2ef>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2c1a:	49 89 c5             	mov    %rax,%r13
  thread_data[thread_count].task_count = total_barrier_count;
    2c1d:	48 8b 05 dc 3d 00 00 	mov    0x3ddc(%rip),%rax        # 6a00 <_IO_stdin_used+0xa00>
    2c24:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].threads = thread_data;
    2c29:	4d 89 80 a0 03 00 00 	mov    %r8,0x3a0(%r8)
  thread_data[thread_count].task_count = total_barrier_count;
    2c30:	49 89 80 b8 03 00 00 	mov    %rax,0x3b8(%r8)
    2c37:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2c39:	41 c7 80 a8 03 00 00 06 00 00 00 	movl   $0x6,0x3a8(%r8)
  thread_data[thread_count].thread_index = 0;
    2c44:	49 c7 80 90 03 00 00 00 00 00 00 	movq   $0x0,0x390(%r8)
    2c4f:	e8 0c f8 ff ff       	call   2460 <__printf_chk@plt>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2c54:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    2c58:	49 8d 7d 30          	lea    0x30(%r13),%rdi
    2c5c:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2c63:	48 8d 15 56 0b 00 00 	lea    0xb56(%rip),%rdx        # 37c0 <timer_thread>
    2c6a:	49 8d 88 90 03 00 00 	lea    0x390(%r8),%rcx
    2c71:	e8 0a f8 ff ff       	call   2480 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2c76:	4c 89 6d a0          	mov    %r13,-0x60(%rbp)
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2c7a:	4c 8b 7d a8          	mov    -0x58(%rbp),%r15
    2c7e:	66 90                	xchg   %ax,%ax
    thread_data[x].type = WORKER;
    2c80:	41 c7 47 04 01 00 00 00 	movl   $0x1,0x4(%r15)
    2c88:	44 89 f2             	mov    %r14d,%edx
    2c8b:	bf 01 00 00 00       	mov    $0x1,%edi
    2c90:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2c92:	41 c7 47 2c 01 00 00 00 	movl   $0x1,0x2c(%r15)
    2c9a:	48 8d 35 27 39 00 00 	lea    0x3927(%rip),%rsi        # 65c8 <_IO_stdin_used+0x5c8>
  for (int x = 0 ; x < thread_count ; x++) {
    2ca1:	41 83 c6 01          	add    $0x1,%r14d
    2ca5:	e8 b6 f7 ff ff       	call   2460 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2caa:	4c 89 f9             	mov    %r15,%rcx
    2cad:	48 89 de             	mov    %rbx,%rsi
    2cb0:	4c 89 ef             	mov    %r13,%rdi
    2cb3:	4c 89 e2             	mov    %r12,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2cb6:	49 81 c7 98 00 00 00 	add    $0x98,%r15
    2cbd:	49 83 c5 08          	add    $0x8,%r13
    2cc1:	48 83 c3 38          	add    $0x38,%rbx
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2cc5:	e8 b6 f7 ff ff       	call   2480 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2cca:	41 83 fe 06          	cmp    $0x6,%r14d
    2cce:	75 b0                	jne    2c80 <main+0x670>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2cd0:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2cd4:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    2cd9:	4c 8b 6d a0          	mov    -0x60(%rbp),%r13
    2cdd:	45 31 f6             	xor    %r14d,%r14d
    thread_data[x].task_count = 0;
    2ce0:	48 8b 1d 21 3d 00 00 	mov    0x3d21(%rip),%rbx        # 6a08 <_IO_stdin_used+0xa08>
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ce7:	bf 01 00 00 00       	mov    $0x1,%edi
    2cec:	4c 8d 65 c0          	lea    -0x40(%rbp),%r12
    thread_data[x].type = IO;
    2cf0:	41 c7 80 2c 04 00 00 02 00 00 00 	movl   $0x2,0x42c(%r8)
    thread_data[x].task_count = 0;
    2cfb:	49 89 98 50 04 00 00 	mov    %rbx,0x450(%r8)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2d02:	e8 99 f6 ff ff       	call   23a0 <calloc@plt>
    2d07:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2d0b:	be 00 08 00 00       	mov    $0x800,%esi
    2d10:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2d12:	49 89 80 68 04 00 00 	mov    %rax,0x468(%r8)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2d19:	e8 b2 f7 ff ff       	call   24d0 <eventfd@plt>
    2d1e:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    2d22:	ba 07 00 00 00       	mov    $0x7,%edx
    2d27:	48 8d 35 df 35 00 00 	lea    0x35df(%rip),%rsi        # 630d <_IO_stdin_used+0x30d>
    2d2e:	bf 01 00 00 00       	mov    $0x1,%edi
    2d33:	41 89 80 70 04 00 00 	mov    %eax,0x470(%r8)
    2d3a:	31 c0                	xor    %eax,%eax
    thread_data[x].threads = thread_data;
    2d3c:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    thread_data[x].thread_count = thread_count;
    2d43:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    thread_data[x].thread_index = x;
    2d4e:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    2d59:	e8 02 f7 ff ff       	call   2460 <__printf_chk@plt>
    thread_data[x].type = IO;
    2d5e:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2d62:	48 8b 75 b8          	mov    -0x48(%rbp),%rsi
    2d66:	49 8d 7d 38          	lea    0x38(%r13),%rdi
    2d6a:	48 8d 15 af 1d 00 00 	lea    0x1daf(%rip),%rdx        # 4b20 <io_thread>
    thread_data[x].type = IO;
    2d71:	49 8d 88 28 04 00 00 	lea    0x428(%r8),%rcx
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2d78:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2d7f:	e8 fc f6 ff ff       	call   2480 <pthread_create@plt>
    2d84:	ba 08 00 00 00       	mov    $0x8,%edx
    2d89:	48 8d 35 94 35 00 00 	lea    0x3594(%rip),%rsi        # 6324 <_IO_stdin_used+0x324>
    2d90:	31 c0                	xor    %eax,%eax
    2d92:	bf 01 00 00 00       	mov    $0x1,%edi
    2d97:	e8 c4 f6 ff ff       	call   2460 <__printf_chk@plt>
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2d9c:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    thread_data[x].buffers = &buffers[buffer_index];
    2da0:	48 8b 45 88          	mov    -0x78(%rbp),%rax

    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2da4:	49 8d 7d 40          	lea    0x40(%r13),%rdi
    2da8:	48 8b 75 b0          	mov    -0x50(%rbp),%rsi
    2dac:	48 8d 15 4d 09 00 00 	lea    0x94d(%rip),%rdx        # 3700 <external_thread>
    thread_data[x].buffers = &buffers[buffer_index];
    2db3:	49 89 80 f8 04 00 00 	mov    %rax,0x4f8(%r8)
    thread_data[x].thread_count = thread_count;
    2dba:	48 8b 05 2f 3c 00 00 	mov    0x3c2f(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    thread_data[x].type = EXTERNAL;
    2dc1:	49 8d 88 c0 04 00 00 	lea    0x4c0(%r8),%rcx
    thread_data[x].task_count = 0;
    2dc8:	49 89 98 e8 04 00 00 	mov    %rbx,0x4e8(%r8)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2dcf:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    2dd6:	48 8d 1d 82 35 00 00 	lea    0x3582(%rip),%rbx        # 635f <_IO_stdin_used+0x35f>
    thread_data[x].thread_count = thread_count;
    2ddd:	49 89 80 d8 04 00 00 	mov    %rax,0x4d8(%r8)
    thread_data[x].thread_index = x;
    2de4:	48 8b 05 25 3c 00 00 	mov    0x3c25(%rip),%rax        # 6a10 <_IO_stdin_used+0xa10>
    thread_data[x].threads = thread_data;
    2deb:	4d 89 80 d0 04 00 00 	mov    %r8,0x4d0(%r8)
    thread_data[x].thread_index = x;
    2df2:	49 89 80 c0 04 00 00 	mov    %rax,0x4c0(%r8)
    thread_data[x].type = EXTERNAL;
    2df9:	4c 89 45 b8          	mov    %r8,-0x48(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2dfd:	e8 7e f6 ff ff       	call   2480 <pthread_create@plt>
    2e02:	48 8d 3d 38 35 00 00 	lea    0x3538(%rip),%rdi        # 6341 <_IO_stdin_used+0x341>
    2e09:	e8 e2 f4 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    2e0e:	4c 8b 7d b8          	mov    -0x48(%rbp),%r15
    2e12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void * result; 
    pthread_join(thread[x], &result);
    2e18:	4b 8b 7c f5 00       	mov    0x0(%r13,%r14,8),%rdi
    2e1d:	4c 89 e6             	mov    %r12,%rsi
    2e20:	e8 eb f6 ff ff       	call   2510 <pthread_join@plt>
    2e25:	44 89 f2             	mov    %r14d,%edx
    2e28:	48 89 de             	mov    %rbx,%rsi
    2e2b:	bf 01 00 00 00       	mov    $0x1,%edi
    2e30:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2e32:	49 83 c6 01          	add    $0x1,%r14
    2e36:	e8 25 f6 ff ff       	call   2460 <__printf_chk@plt>
    2e3b:	49 83 fe 09          	cmp    $0x9,%r14
    2e3f:	75 d7                	jne    2e18 <main+0x808>
    2e41:	4d 89 f8             	mov    %r15,%r8
  }
  long total = 0;
  long v = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
    2e44:	45 31 e4             	xor    %r12d,%r12d
  long sends = 0;
    2e47:	45 31 c9             	xor    %r9d,%r9d
  long total = 0;
    2e4a:	45 31 ed             	xor    %r13d,%r13d
    2e4d:	49 8d 80 b0 03 00 00 	lea    0x3b0(%r8),%rax
  long v = 0;
    2e54:	45 31 c0             	xor    %r8d,%r8d
    2e57:	4c 89 6d b8          	mov    %r13,-0x48(%rbp)
  long ingests = 0;
    2e5b:	31 c9                	xor    %ecx,%ecx
    2e5d:	48 89 45 98          	mov    %rax,-0x68(%rbp)
    2e61:	4d 8d 7f 20          	lea    0x20(%r15),%r15
  long received = 0;
    2e65:	31 db                	xor    %ebx,%ebx
    2e67:	49 89 ce             	mov    %rcx,%r14
    2e6a:	4c 89 45 b0          	mov    %r8,-0x50(%rbp)
    2e6e:	4c 89 4d a8          	mov    %r9,-0x58(%rbp)
    2e72:	4c 89 65 a0          	mov    %r12,-0x60(%rbp)
    2e76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  for (int x = 0 ; x < thread_count ; x++) {

    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2e80:	49 63 47 08          	movslq 0x8(%r15),%rax
    2e84:	85 c0                	test   %eax,%eax
    2e86:	0f 8e 99 00 00 00    	jle    2f25 <main+0x915>
    2e8c:	49 8b 17             	mov    (%r15),%rdx
    2e8f:	48 c1 e0 09          	shl    $0x9,%rax
    2e93:	4c 8b 5d b8          	mov    -0x48(%rbp),%r11
    2e97:	48 8b 4d b0          	mov    -0x50(%rbp),%rcx
    2e9b:	4c 8b 4d a8          	mov    -0x58(%rbp),%r9
    2e9f:	4c 8b 65 a0          	mov    -0x60(%rbp),%r12
    2ea3:	48 8d 34 10          	lea    (%rax,%rdx,1),%rsi
    2ea7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      total += thread_data[x].tasks[n].n;
      v += thread_data[x].tasks[n].v;
      ingests += thread_data[x].tasks[n].ingest_count;
      sends += thread_data[x].tasks[n].sends;
      for (int k = 0 ; k < thread_count ; k++) {
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2eb0:	48 8b 82 b0 01 00 00 	mov    0x1b0(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    2eb7:	4c 03 9a 08 01 00 00 	add    0x108(%rdx),%r11
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2ebe:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
      v += thread_data[x].tasks[n].v;
    2ec5:	48 03 8a 10 ff ff ff 	add    -0xf0(%rdx),%rcx
      ingests += thread_data[x].tasks[n].ingest_count;
    2ecc:	4c 03 72 a8          	add    -0x58(%rdx),%r14
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ed0:	4c 03 60 10          	add    0x10(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ed4:	48 03 58 18          	add    0x18(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ed8:	4c 03 60 30          	add    0x30(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2edc:	48 03 58 38          	add    0x38(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ee0:	4c 03 60 50          	add    0x50(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ee4:	48 03 58 58          	add    0x58(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ee8:	4c 03 60 70          	add    0x70(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2eec:	48 03 58 78          	add    0x78(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ef0:	4c 03 a0 90 00 00 00 	add    0x90(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ef7:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
      sends += thread_data[x].tasks[n].sends;
    2efe:	4c 03 4a b8          	add    -0x48(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2f02:	4c 03 a0 b0 00 00 00 	add    0xb0(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2f09:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2f10:	48 39 f2             	cmp    %rsi,%rdx
    2f13:	75 9b                	jne    2eb0 <main+0x8a0>
    2f15:	4c 89 5d b8          	mov    %r11,-0x48(%rbp)
    2f19:	48 89 4d b0          	mov    %rcx,-0x50(%rbp)
    2f1d:	4c 89 4d a8          	mov    %r9,-0x58(%rbp)
    2f21:	4c 89 65 a0          	mov    %r12,-0x60(%rbp)
      }
    }
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f25:	45 31 ed             	xor    %r13d,%r13d
    2f28:	49 83 7f 50 00       	cmpq   $0x0,0x50(%r15)
    2f2d:	0f 8e 7f 00 00 00    	jle    2fb2 <main+0x9a2>
    2f33:	4d 89 fc             	mov    %r15,%r12
    2f36:	49 89 df             	mov    %rbx,%r15
    2f39:	4c 89 eb             	mov    %r13,%rbx
    2f3c:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec start = thread_data[x].start[n];
    2f40:	49 8b 7c 24 30       	mov    0x30(%r12),%rdi
    2f45:	48 89 de             	mov    %rbx,%rsi
      struct timespec end = thread_data[x].end[n];
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2f48:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f52:	48 83 c3 01          	add    $0x1,%rbx
    2f56:	48 c1 e6 04          	shl    $0x4,%rsi
      struct timespec start = thread_data[x].start[n];
    2f5a:	48 01 f7             	add    %rsi,%rdi
      struct timespec end = thread_data[x].end[n];
    2f5d:	49 03 74 24 38       	add    0x38(%r12),%rsi
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    2f62:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    2f66:	48 2b 57 08          	sub    0x8(%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2f6a:	48 f7 e2             	mul    %rdx
    2f6d:	31 c0                	xor    %eax,%eax
    2f6f:	48 89 d1             	mov    %rdx,%rcx
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    2f72:	48 8b 16             	mov    (%rsi),%rdx
    2f75:	48 8d 35 f7 33 00 00 	lea    0x33f7(%rip),%rsi        # 6373 <_IO_stdin_used+0x373>
    2f7c:	48 2b 17             	sub    (%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2f7f:	48 c1 e9 12          	shr    $0x12,%rcx
    2f83:	bf 01 00 00 00       	mov    $0x1,%edi
    2f88:	e8 d3 f4 ff ff       	call   2460 <__printf_chk@plt>
    2f8d:	49 8b 54 24 40       	mov    0x40(%r12),%rdx
    2f92:	48 8d 35 f8 33 00 00 	lea    0x33f8(%rip),%rsi        # 6391 <_IO_stdin_used+0x391>
    2f99:	31 c0                	xor    %eax,%eax
    2f9b:	bf 01 00 00 00       	mov    $0x1,%edi
    2fa0:	e8 bb f4 ff ff       	call   2460 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2fa5:	49 39 5c 24 50       	cmp    %rbx,0x50(%r12)
    2faa:	7f 94                	jg     2f40 <main+0x930>
    2fac:	4c 89 fb             	mov    %r15,%rbx
    2faf:	4d 89 e7             	mov    %r12,%r15
      printf("%ld iterations\n", thread_data[x].iteration_count);
    }
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    2fb2:	45 31 ed             	xor    %r13d,%r13d
    2fb5:	49 83 7f 68 00       	cmpq   $0x0,0x68(%r15)
    2fba:	0f 8e 9c 00 00 00    	jle    305c <main+0xa4c>
    2fc0:	4d 89 fc             	mov    %r15,%r12
    2fc3:	49 89 df             	mov    %rbx,%r15
    2fc6:	4c 89 eb             	mov    %r13,%rbx
    2fc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    2fd0:	49 8b 44 24 58       	mov    0x58(%r12),%rax
    2fd5:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    2fd9:	48 83 ec 08          	sub    $0x8,%rsp
    2fdd:	48 8d 35 0c 36 00 00 	lea    0x360c(%rip),%rsi        # 65f0 <_IO_stdin_used+0x5f0>
    2fe4:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    2fe9:	48 83 c3 01          	add    $0x1,%rbx
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    2fed:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    2ff1:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    2ffb:	4c 8b 69 18          	mov    0x18(%rcx),%r13
    2fff:	4c 2b 69 08          	sub    0x8(%rcx),%r13
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3003:	49 f7 e5             	mul    %r13
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3006:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    300a:	4c 2b 01             	sub    (%rcx),%r8
    300d:	31 c0                	xor    %eax,%eax
    300f:	8b 49 20             	mov    0x20(%rcx),%ecx
    3012:	41 55                	push   %r13
    3014:	48 c1 ea 12          	shr    $0x12,%rdx
    3018:	49 89 d1             	mov    %rdx,%r9
    301b:	ba 06 00 00 00       	mov    $0x6,%edx
    3020:	e8 3b f4 ff ff       	call   2460 <__printf_chk@plt>
    3025:	48 8d 35 81 33 00 00 	lea    0x3381(%rip),%rsi        # 63ad <_IO_stdin_used+0x3ad>
    302c:	bf 01 00 00 00       	mov    $0x1,%edi
      printf("%ldns per thread\n", (seconds2 / thread_count));
    3031:	48 b8 ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%rax
    303b:	49 f7 e5             	mul    %r13
    303e:	31 c0                	xor    %eax,%eax
    3040:	48 c1 ea 02          	shr    $0x2,%rdx
    3044:	e8 17 f4 ff ff       	call   2460 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3049:	58                   	pop    %rax
    304a:	5a                   	pop    %rdx
    304b:	49 39 5c 24 68       	cmp    %rbx,0x68(%r12)
    3050:	0f 8f 7a ff ff ff    	jg     2fd0 <main+0x9c0>
    3056:	4c 89 fb             	mov    %r15,%rbx
    3059:	4d 89 e7             	mov    %r12,%r15
    305c:	49 8b 57 70          	mov    0x70(%r15),%rdx
    3060:	48 8d 35 3a 33 00 00 	lea    0x333a(%rip),%rsi        # 63a1 <_IO_stdin_used+0x3a1>
    3067:	bf 01 00 00 00       	mov    $0x1,%edi
    306c:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < thread_count ; x++) {
    306e:	49 81 c7 98 00 00 00 	add    $0x98,%r15
    3075:	e8 e6 f3 ff ff       	call   2460 <__printf_chk@plt>
    307a:	4c 39 7d 98          	cmp    %r15,-0x68(%rbp)
    307e:	0f 85 fc fd ff ff    	jne    2e80 <main+0x870>
    3084:	4c 8b 6d b8          	mov    -0x48(%rbp),%r13
    3088:	4c 8b 45 b0          	mov    -0x50(%rbp),%r8
    308c:	bf 01 00 00 00       	mov    $0x1,%edi
    3091:	31 c0                	xor    %eax,%eax
    3093:	48 8d 35 25 33 00 00 	lea    0x3325(%rip),%rsi        # 63bf <_IO_stdin_used+0x3bf>
    309a:	4c 8b 65 a0          	mov    -0x60(%rbp),%r12
    309e:	4c 89 75 b0          	mov    %r14,-0x50(%rbp)
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total Protected %ld\n", protected_state->protected);
  printf("Total V %ld\n", v);
  printf("\n");
  printf("Total Protected per second %ld\n", protected_state->protected / DURATION);
    30a2:	49 be 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r14
    30ac:	4c 89 ea             	mov    %r13,%rdx
    30af:	4c 89 45 b8          	mov    %r8,-0x48(%rbp)
    30b3:	e8 a8 f3 ff ff       	call   2460 <__printf_chk@plt>
    30b8:	bf 0a 00 00 00       	mov    $0xa,%edi
    30bd:	e8 1e f2 ff ff       	call   22e0 <putchar@plt>
    30c2:	4c 8b 7d 80          	mov    -0x80(%rbp),%r15
    30c6:	bf 01 00 00 00       	mov    $0x1,%edi
    30cb:	31 c0                	xor    %eax,%eax
    30cd:	48 8d 35 ff 32 00 00 	lea    0x32ff(%rip),%rsi        # 63d3 <_IO_stdin_used+0x3d3>
    30d4:	49 8b 17             	mov    (%r15),%rdx
    30d7:	e8 84 f3 ff ff       	call   2460 <__printf_chk@plt>
    30dc:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
    30e0:	bf 01 00 00 00       	mov    $0x1,%edi
    30e5:	31 c0                	xor    %eax,%eax
    30e7:	48 8d 35 fa 32 00 00 	lea    0x32fa(%rip),%rsi        # 63e8 <_IO_stdin_used+0x3e8>
    30ee:	e8 6d f3 ff ff       	call   2460 <__printf_chk@plt>
    30f3:	bf 0a 00 00 00       	mov    $0xa,%edi
    30f8:	e8 e3 f1 ff ff       	call   22e0 <putchar@plt>
    30fd:	49 8b 37             	mov    (%r15),%rsi
    3100:	bf 01 00 00 00       	mov    $0x1,%edi
    3105:	48 89 f0             	mov    %rsi,%rax
    3108:	48 c1 fe 3f          	sar    $0x3f,%rsi
    310c:	49 f7 ee             	imul   %r14
    310f:	31 c0                	xor    %eax,%eax
    3111:	48 c1 fa 02          	sar    $0x2,%rdx
    3115:	48 29 f2             	sub    %rsi,%rdx
    3118:	48 8d 35 09 35 00 00 	lea    0x3509(%rip),%rsi        # 6628 <_IO_stdin_used+0x628>
    311f:	e8 3c f3 ff ff       	call   2460 <__printf_chk@plt>
    3124:	49 8b 57 08          	mov    0x8(%r15),%rdx
    3128:	bf 01 00 00 00       	mov    $0x1,%edi
    312d:	31 c0                	xor    %eax,%eax
    312f:	48 8d 35 12 35 00 00 	lea    0x3512(%rip),%rsi        # 6648 <_IO_stdin_used+0x648>
    3136:	e8 25 f3 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    313b:	48 8b 4d b0          	mov    -0x50(%rbp),%rcx
    313f:	bf 01 00 00 00       	mov    $0x1,%edi
    3144:	48 8d 35 25 35 00 00 	lea    0x3525(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    314b:	48 89 c8             	mov    %rcx,%rax
    314e:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3152:	49 f7 ee             	imul   %r14
    3155:	31 c0                	xor    %eax,%eax
    3157:	48 c1 fa 02          	sar    $0x2,%rdx
    315b:	48 29 ca             	sub    %rcx,%rdx
    315e:	e8 fd f2 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3163:	4c 8b 4d a8          	mov    -0x58(%rbp),%r9
    3167:	bf 01 00 00 00       	mov    $0x1,%edi
    316c:	48 8d 35 2d 35 00 00 	lea    0x352d(%rip),%rsi        # 66a0 <_IO_stdin_used+0x6a0>
    3173:	4c 89 c8             	mov    %r9,%rax
    3176:	49 c1 f9 3f          	sar    $0x3f,%r9
    317a:	49 f7 ee             	imul   %r14
    317d:	31 c0                	xor    %eax,%eax
    317f:	48 c1 fa 02          	sar    $0x2,%rdx
    3183:	4c 29 ca             	sub    %r9,%rdx
    3186:	e8 d5 f2 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    318b:	4c 89 e8             	mov    %r13,%rax
    318e:	49 c1 fd 3f          	sar    $0x3f,%r13
    3192:	48 8d 35 37 35 00 00 	lea    0x3537(%rip),%rsi        # 66d0 <_IO_stdin_used+0x6d0>
    3199:	49 f7 ee             	imul   %r14
    319c:	bf 01 00 00 00       	mov    $0x1,%edi
    31a1:	48 c1 fa 02          	sar    $0x2,%rdx
    31a5:	4c 29 ea             	sub    %r13,%rdx
    31a8:	31 c0                	xor    %eax,%eax
    31aa:	e8 b1 f2 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    31af:	4c 89 e0             	mov    %r12,%rax
    31b2:	49 c1 fc 3f          	sar    $0x3f,%r12
    31b6:	48 8d 35 38 32 00 00 	lea    0x3238(%rip),%rsi        # 63f5 <_IO_stdin_used+0x3f5>
    31bd:	49 f7 ee             	imul   %r14
    31c0:	bf 01 00 00 00       	mov    $0x1,%edi
    31c5:	31 c0                	xor    %eax,%eax
    31c7:	48 c1 fa 02          	sar    $0x2,%rdx
    31cb:	4c 29 e2             	sub    %r12,%rdx
    31ce:	e8 8d f2 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    31d3:	48 89 d8             	mov    %rbx,%rax
    31d6:	48 c1 fb 3f          	sar    $0x3f,%rbx
    31da:	48 8d 35 25 32 00 00 	lea    0x3225(%rip),%rsi        # 6406 <_IO_stdin_used+0x406>
    31e1:	49 f7 ee             	imul   %r14
    31e4:	bf 01 00 00 00       	mov    $0x1,%edi
    31e9:	31 c0                	xor    %eax,%eax
    31eb:	48 c1 fa 02          	sar    $0x2,%rdx
    31ef:	48 29 da             	sub    %rbx,%rdx
    31f2:	e8 69 f2 ff ff       	call   2460 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    31f7:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    31fb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3204:	75 4e                	jne    3254 <main+0xc44>
    3206:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
    320a:	31 c0                	xor    %eax,%eax
    320c:	5b                   	pop    %rbx
    320d:	41 5c                	pop    %r12
    320f:	41 5d                	pop    %r13
    3211:	41 5e                	pop    %r14
    3213:	41 5f                	pop    %r15
    3215:	5d                   	pop    %rbp
    3216:	c3                   	ret
    3217:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          thread_data[x].tasks[y].run = barriered_work; 
    3220:	48 8d 05 49 21 00 00 	lea    0x2149(%rip),%rax        # 5370 <barriered_work>
    3227:	41 bd 06 00 00 00    	mov    $0x6,%r13d
    322d:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3235:	e9 52 f8 ff ff       	jmp    2a8c <main+0x47c>
    323a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            thread_data[x].tasks[y].protected = do_protected_write; 
    3240:	48 8d 05 69 01 00 00 	lea    0x169(%rip),%rax        # 33b0 <do_protected_write>
    3247:	4b 89 84 37 20 01 00 00 	mov    %rax,0x120(%r15,%r14,1)
    324f:	e9 2d f6 ff ff       	jmp    2881 <main+0x271>
}
    3254:	e8 d7 f0 ff ff       	call   2330 <__stack_chk_fail@plt>
    3259:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003260 <_start>:
    3260:	f3 0f 1e fa          	endbr64
    3264:	31 ed                	xor    %ebp,%ebp
    3266:	49 89 d1             	mov    %rdx,%r9
    3269:	5e                   	pop    %rsi
    326a:	48 89 e2             	mov    %rsp,%rdx
    326d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3271:	50                   	push   %rax
    3272:	54                   	push   %rsp
    3273:	45 31 c0             	xor    %r8d,%r8d
    3276:	31 c9                	xor    %ecx,%ecx
    3278:	48 8d 3d 91 f3 ff ff 	lea    -0xc6f(%rip),%rdi        # 2610 <main>
    327f:	ff 15 4b 5d 00 00    	call   *0x5d4b(%rip)        # 8fd0 <__libc_start_main@GLIBC_2.34>
    3285:	f4                   	hlt
    3286:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003290 <__gmon_start__>:
    3290:	f3 0f 1e fa          	endbr64
    3294:	8b 05 8e 5d 00 00    	mov    0x5d8e(%rip),%eax        # 9028 <called.0>
    329a:	85 c0                	test   %eax,%eax
    329c:	74 02                	je     32a0 <__gmon_start__+0x10>
    329e:	c3                   	ret
    329f:	90                   	nop
    32a0:	48 83 ec 08          	sub    $0x8,%rsp
    32a4:	48 8d 35 a2 29 00 00 	lea    0x29a2(%rip),%rsi        # 5c4d <etext>
    32ab:	48 8d 3d 4e cd ff ff 	lea    -0x32b2(%rip),%rdi        # 0 <__executable_start>
    32b2:	c7 05 6c 5d 00 00 01 00 00 00 	movl   $0x1,0x5d6c(%rip)        # 9028 <called.0>
    32bc:	e8 ff f0 ff ff       	call   23c0 <__monstartup@plt>
    32c1:	48 8b 3d 18 5d 00 00 	mov    0x5d18(%rip),%rdi        # 8fe0 <_mcleanup@GLIBC_2.2.5>
    32c8:	48 83 c4 08          	add    $0x8,%rsp
    32cc:	e9 3f 29 00 00       	jmp    5c10 <atexit>
    32d1:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    32db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000032e0 <_dl_relocate_static_pie>:
    32e0:	f3 0f 1e fa          	endbr64
    32e4:	c3                   	ret
    32e5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    32ef:	90                   	nop

00000000000032f0 <deregister_tm_clones>:
    32f0:	48 8d 3d 29 5d 00 00 	lea    0x5d29(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    32f7:	48 8d 05 22 5d 00 00 	lea    0x5d22(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    32fe:	48 39 f8             	cmp    %rdi,%rax
    3301:	74 15                	je     3318 <deregister_tm_clones+0x28>
    3303:	48 8b 05 ce 5c 00 00 	mov    0x5cce(%rip),%rax        # 8fd8 <_ITM_deregisterTMCloneTable@Base>
    330a:	48 85 c0             	test   %rax,%rax
    330d:	74 09                	je     3318 <deregister_tm_clones+0x28>
    330f:	ff e0                	jmp    *%rax
    3311:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3318:	c3                   	ret
    3319:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003320 <register_tm_clones>:
    3320:	48 8d 3d f9 5c 00 00 	lea    0x5cf9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3327:	48 8d 35 f2 5c 00 00 	lea    0x5cf2(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    332e:	48 29 fe             	sub    %rdi,%rsi
    3331:	48 89 f0             	mov    %rsi,%rax
    3334:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3338:	48 c1 f8 03          	sar    $0x3,%rax
    333c:	48 01 c6             	add    %rax,%rsi
    333f:	48 d1 fe             	sar    %rsi
    3342:	74 14                	je     3358 <register_tm_clones+0x38>
    3344:	48 8b 05 a5 5c 00 00 	mov    0x5ca5(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    334b:	48 85 c0             	test   %rax,%rax
    334e:	74 08                	je     3358 <register_tm_clones+0x38>
    3350:	ff e0                	jmp    *%rax
    3352:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3358:	c3                   	ret
    3359:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003360 <__do_global_dtors_aux>:
    3360:	f3 0f 1e fa          	endbr64
    3364:	80 3d c1 5c 00 00 00 	cmpb   $0x0,0x5cc1(%rip)        # 902c <completed.0>
    336b:	75 2b                	jne    3398 <__do_global_dtors_aux+0x38>
    336d:	55                   	push   %rbp
    336e:	48 83 3d 82 5c 00 00 00 	cmpq   $0x0,0x5c82(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    3376:	48 89 e5             	mov    %rsp,%rbp
    3379:	74 0c                	je     3387 <__do_global_dtors_aux+0x27>
    337b:	48 8b 3d 86 5c 00 00 	mov    0x5c86(%rip),%rdi        # 9008 <__dso_handle>
    3382:	e8 39 ef ff ff       	call   22c0 <__cxa_finalize@plt>
    3387:	e8 64 ff ff ff       	call   32f0 <deregister_tm_clones>
    338c:	c6 05 99 5c 00 00 01 	movb   $0x1,0x5c99(%rip)        # 902c <completed.0>
    3393:	5d                   	pop    %rbp
    3394:	c3                   	ret
    3395:	0f 1f 00             	nopl   (%rax)
    3398:	c3                   	ret
    3399:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000033a0 <frame_dummy>:
    33a0:	f3 0f 1e fa          	endbr64
    33a4:	e9 77 ff ff ff       	jmp    3320 <register_tm_clones>
    33a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000033b0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    33b0:	f3 0f 1e fa          	endbr64
    33b4:	55                   	push   %rbp
    33b5:	48 89 e5             	mov    %rsp,%rbp
    33b8:	ff 15 2a 5c 00 00    	call   *0x5c2a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  struct ProtectedState *protected = data->thread->protected_state;
    33be:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    33c5:	48 8b 40 30          	mov    0x30(%rax),%rax
  data->v++; // thread local
    33c9:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    33d1:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    33d5:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    33d9:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    33e0:	48 85 c9             	test   %rcx,%rcx
    33e3:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    33ea:	48 0f 4f d6          	cmovg  %rsi,%rdx
    33ee:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    33f2:	31 c0                	xor    %eax,%eax
    33f4:	5d                   	pop    %rbp
    33f5:	c3                   	ret
    33f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003400 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3400:	f3 0f 1e fa          	endbr64
    3404:	55                   	push   %rbp
    3405:	48 89 e5             	mov    %rsp,%rbp
    3408:	ff 15 da 5b 00 00    	call   *0x5bda(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    for (int x = 0 ; x < data->task_count ; x++) {
    340e:	48 63 8f 84 01 00 00 	movslq 0x184(%rdi),%rcx
    3415:	85 c9                	test   %ecx,%ecx
    3417:	7e 55                	jle    346e <barriered_reset+0x6e>
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    3419:	48 63 87 30 01 00 00 	movslq 0x130(%rdi),%rax
    3420:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    3427:	48 c1 e1 09          	shl    $0x9,%rcx
    342b:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    342f:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3433:	48 8b 56 10          	mov    0x10(%rsi),%rdx
      data->thread->tasks[x].available = 1; 
    3437:	48 8b 76 20          	mov    0x20(%rsi),%rsi
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    343b:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
    343f:	48 8b 50 20          	mov    0x20(%rax),%rdx
      data->thread->tasks[x].available = 1; 
    3443:	31 c0                	xor    %eax,%eax
    3445:	0f 1f 00             	nopl   (%rax)
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    3448:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index].tasks[x].prearrive++; 
    3450:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3458:	c7 84 06 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3463:	48 05 00 02 00 00    	add    $0x200,%rax
    3469:	48 39 c1             	cmp    %rax,%rcx
    346c:	75 da                	jne    3448 <barriered_reset+0x48>
  asm volatile ("mfence" ::: "memory");
    346e:	0f ae f0             	mfence
}
    3471:	31 c0                	xor    %eax,%eax
    3473:	5d                   	pop    %rbp
    3474:	c3                   	ret
    3475:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003480 <barriered_thread>:
void* barriered_thread(void *arg) {
    3480:	f3 0f 1e fa          	endbr64
    3484:	55                   	push   %rbp
    3485:	48 89 e5             	mov    %rsp,%rbp
    3488:	41 57                	push   %r15
    348a:	41 56                	push   %r14
    348c:	41 55                	push   %r13
    348e:	41 54                	push   %r12
    3490:	53                   	push   %rbx
    3491:	48 83 ec 08          	sub    $0x8,%rsp
    3495:	ff 15 4d 5b 00 00    	call   *0x5b4d(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  int waiting = 0;
    349b:	45 31 e4             	xor    %r12d,%r12d
  int t = 0;
    349e:	31 db                	xor    %ebx,%ebx
void* barriered_thread(void *arg) {
    34a0:	49 89 fe             	mov    %rdi,%r14
  while (data->running == 1) {
    34a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    34a8:	41 83 7e 2c 01       	cmpl   $0x1,0x2c(%r14)
    34ad:	0f 85 3b 02 00 00    	jne    36ee <barriered_thread+0x26e>
    if (t >= data->task_count) {
    34b3:	41 8b 46 28          	mov    0x28(%r14),%eax
    34b7:	39 d8                	cmp    %ebx,%eax
    34b9:	7f 0e                	jg     34c9 <barriered_thread+0x49>
      data->cycles++;
    34bb:	49 83 86 90 00 00 00 01 	addq   $0x1,0x90(%r14)
    for (; t < data->task_count; t++) {
    34c3:	31 db                	xor    %ebx,%ebx
    34c5:	85 c0                	test   %eax,%eax
    34c7:	7e df                	jle    34a8 <barriered_thread+0x28>
    34c9:	4c 63 eb             	movslq %ebx,%r13
    34cc:	49 c1 e5 09          	shl    $0x9,%r13
    34d0:	eb 14                	jmp    34e6 <barriered_thread+0x66>
    34d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    34d8:	83 c3 01             	add    $0x1,%ebx
    34db:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    34e2:	39 c3                	cmp    %eax,%ebx
    34e4:	7d c2                	jge    34a8 <barriered_thread+0x28>
      if (data->tasks[t].available == 1) {
    34e6:	49 8b 56 20          	mov    0x20(%r14),%rdx
    34ea:	42 83 bc 2a 80 01 00 00 01 	cmpl   $0x1,0x180(%rdx,%r13,1)
    34f3:	75 e3                	jne    34d8 <barriered_thread+0x58>
          previous = t - 1;
    34f5:	8d 53 ff             	lea    -0x1(%rbx),%edx
    34f8:	83 e8 01             	sub    $0x1,%eax
    34fb:	85 db                	test   %ebx,%ebx
    34fd:	0f 4f c2             	cmovg  %edx,%eax
        asm volatile ("sfence" ::: "memory");
    3500:	0f ae f8             	sfence
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3503:	45 8b 4e 18          	mov    0x18(%r14),%r9d
    3507:	45 85 c9             	test   %r9d,%r9d
    350a:	0f 8e 90 01 00 00    	jle    36a0 <barriered_thread+0x220>
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    3510:	48 63 c8             	movslq %eax,%rcx
    3513:	49 8b 46 20          	mov    0x20(%r14),%rax
    3517:	49 63 d1             	movslq %r9d,%rdx
        int prearrive = 0; 
    351a:	45 31 d2             	xor    %r10d,%r10d
    351d:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    3521:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    3525:	45 31 ff             	xor    %r15d,%r15d
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    3528:	4c 01 e8             	add    %r13,%rax
    352b:	48 8d 14 72          	lea    (%rdx,%rsi,2),%rdx
    352f:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
          if (data->threads[thread].tasks[previous].prearrive == data->tasks[t].prearrive) {
    3536:	8b b8 00 01 00 00    	mov    0x100(%rax),%edi
    353c:	49 8b 46 10          	mov    0x10(%r14),%rax
    3540:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3544:	0f 1f 40 00          	nopl   0x0(%rax)
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    3548:	48 8b 50 20          	mov    0x20(%rax),%rdx
    354c:	48 01 ca             	add    %rcx,%rdx
    354f:	44 3b 82 80 00 00 00 	cmp    0x80(%rdx),%r8d
    3556:	75 04                	jne    355c <barriered_thread+0xdc>
            arrived++;
    3558:	41 83 c7 01          	add    $0x1,%r15d
          if (data->threads[thread].tasks[previous].prearrive == data->tasks[t].prearrive) {
    355c:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    3562:	75 04                	jne    3568 <barriered_thread+0xe8>
            prearrive++;
    3564:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3568:	48 05 98 00 00 00    	add    $0x98,%rax
    356e:	48 39 f0             	cmp    %rsi,%rax
    3571:	75 d5                	jne    3548 <barriered_thread+0xc8>
        if (prearrive == 0 || prearrive == data->thread_count) {
    3573:	45 39 d1             	cmp    %r10d,%r9d
    3576:	0f 84 94 00 00 00    	je     3610 <barriered_thread+0x190>
    357c:	45 85 d2             	test   %r10d,%r10d
    357f:	0f 84 8b 00 00 00    	je     3610 <barriered_thread+0x190>
        if (arrived == 0 || arrived == data->thread_count) {
    3585:	45 85 ff             	test   %r15d,%r15d
    3588:	74 0a                	je     3594 <barriered_thread+0x114>
    358a:	45 39 7e 18          	cmp    %r15d,0x18(%r14)
    358e:	0f 85 14 ff ff ff    	jne    34a8 <barriered_thread+0x28>
          data->tasks[t].prearrive++;
    3594:	49 8b 56 20          	mov    0x20(%r14),%rdx
    3598:	4c 01 ea             	add    %r13,%rdx
    359b:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    35a2:	85 db                	test   %ebx,%ebx
    35a4:	75 0e                	jne    35b4 <barriered_thread+0x134>
    35a6:	49 8b 76 68          	mov    0x68(%r14),%rsi
    35aa:	49 3b 76 70          	cmp    0x70(%r14),%rsi
    35ae:	0f 8c cc 00 00 00    	jl     3680 <barriered_thread+0x200>
          data->tasks[t].available = 0;
    35b4:	c7 82 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index].tasks[t]);
    35be:	49 63 06             	movslq (%r14),%rax
    35c1:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    35c5:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    35c9:	49 8b 4e 10          	mov    0x10(%r14),%rcx
    35cd:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    35d1:	48 8b 78 20          	mov    0x20(%rax),%rdi
    35d5:	4c 01 ef             	add    %r13,%rdi
    35d8:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    35de:	49 8b 46 20          	mov    0x20(%r14),%rax
    35e2:	4c 01 e8             	add    %r13,%rax
    35e5:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          asm volatile ("sfence" ::: "memory");
    35ec:	0f ae f8             	sfence
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    35ef:	41 8b 46 28          	mov    0x28(%r14),%eax
          data->iteration_count++;
    35f3:	49 83 46 60 01       	addq   $0x1,0x60(%r14)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    35f8:	83 e8 01             	sub    $0x1,%eax
    35fb:	39 d8                	cmp    %ebx,%eax
    35fd:	74 29                	je     3628 <barriered_thread+0x1a8>
          if (waiting == 0) {
    35ff:	45 85 e4             	test   %r12d,%r12d
    3602:	74 4c                	je     3650 <barriered_thread+0x1d0>
    for (; t < data->task_count; t++) {
    3604:	41 8b 46 28          	mov    0x28(%r14),%eax
    3608:	e9 cb fe ff ff       	jmp    34d8 <barriered_thread+0x58>
    360d:	0f 1f 00             	nopl   (%rax)
          if (waiting == 1) {
    3610:	41 83 fc 01          	cmp    $0x1,%r12d
    3614:	0f 84 96 00 00 00    	je     36b0 <barriered_thread+0x230>
        int arrived = 0; 
    361a:	45 31 e4             	xor    %r12d,%r12d
    361d:	e9 63 ff ff ff       	jmp    3585 <barriered_thread+0x105>
    3622:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3628:	49 8b 76 68          	mov    0x68(%r14),%rsi
    362c:	49 3b 76 70          	cmp    0x70(%r14),%rsi
    3630:	7d cd                	jge    35ff <barriered_thread+0x17f>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    3632:	48 c1 e6 04          	shl    $0x4,%rsi
    3636:	bf 04 00 00 00       	mov    $0x4,%edi
    363b:	49 03 76 58          	add    0x58(%r14),%rsi
    363f:	e8 cc ec ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3644:	49 83 46 68 01       	addq   $0x1,0x68(%r14)
          if (waiting == 0) {
    3649:	45 85 e4             	test   %r12d,%r12d
    364c:	75 b6                	jne    3604 <barriered_thread+0x184>
    364e:	66 90                	xchg   %ax,%ax
            data->task_snapshot[data->task_timestamp_count].task = t;
    3650:	49 8b 86 80 00 00 00 	mov    0x80(%r14),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3657:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    365c:	41 bc 01 00 00 00    	mov    $0x1,%r12d
            data->task_snapshot[data->task_timestamp_count].task = t;
    3662:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3666:	49 8b 46 78          	mov    0x78(%r14),%rax
    366a:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    366e:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3671:	e8 9a ec ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3676:	41 8b 46 28          	mov    0x28(%r14),%eax
    367a:	e9 59 fe ff ff       	jmp    34d8 <barriered_thread+0x58>
    367f:	90                   	nop
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3680:	48 c1 e6 04          	shl    $0x4,%rsi
    3684:	bf 04 00 00 00       	mov    $0x4,%edi
    3689:	49 03 76 50          	add    0x50(%r14),%rsi
    368d:	e8 7e ec ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3692:	49 8b 56 20          	mov    0x20(%r14),%rdx
    3696:	4c 01 ea             	add    %r13,%rdx
    3699:	e9 16 ff ff ff       	jmp    35b4 <barriered_thread+0x134>
    369e:	66 90                	xchg   %ax,%ax
          if (waiting == 1) {
    36a0:	41 83 fc 01          	cmp    $0x1,%r12d
    36a4:	0f 85 ea fe ff ff    	jne    3594 <barriered_thread+0x114>
        int arrived = 0; 
    36aa:	45 31 ff             	xor    %r15d,%r15d
    36ad:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    36b0:	49 8b 86 80 00 00 00 	mov    0x80(%r14),%rax
    36b7:	bf 04 00 00 00       	mov    $0x4,%edi
    36bc:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    36c0:	49 8b 46 78          	mov    0x78(%r14),%rax
    36c4:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    36c9:	e8 42 ec ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    36ce:	49 8b 86 80 00 00 00 	mov    0x80(%r14),%rax
    36d5:	48 83 c0 01          	add    $0x1,%rax
    36d9:	48 99                	cqto
    36db:	49 f7 be 88 00 00 00 	idivq  0x88(%r14)
    36e2:	49 89 96 80 00 00 00 	mov    %rdx,0x80(%r14)
            waiting = 0;
    36e9:	e9 2c ff ff ff       	jmp    361a <barriered_thread+0x19a>
}
    36ee:	48 83 c4 08          	add    $0x8,%rsp
    36f2:	31 c0                	xor    %eax,%eax
    36f4:	5b                   	pop    %rbx
    36f5:	41 5c                	pop    %r12
    36f7:	41 5d                	pop    %r13
    36f9:	41 5e                	pop    %r14
    36fb:	41 5f                	pop    %r15
    36fd:	5d                   	pop    %rbp
    36fe:	c3                   	ret
    36ff:	90                   	nop

0000000000003700 <external_thread>:
void * external_thread(void *arg) {
    3700:	f3 0f 1e fa          	endbr64
    3704:	55                   	push   %rbp
    3705:	48 89 e5             	mov    %rsp,%rbp
    3708:	41 56                	push   %r14
    370a:	41 55                	push   %r13
    370c:	41 54                	push   %r12
    370e:	53                   	push   %rbx
    370f:	48 83 ec 30          	sub    $0x30,%rsp
    3713:	ff 15 cf 58 00 00    	call   *0x58cf(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  struct timespec req = {
    3719:	66 0f 6f 05 cf 31 00 00 	movdqa 0x31cf(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
void * external_thread(void *arg) {
    3721:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    372a:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    372e:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3730:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
void * external_thread(void *arg) {
    3734:	49 89 fe             	mov    %rdi,%r14
  struct timespec req = {
    3737:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
  while (data->running == 1) {
    373b:	75 5f                	jne    379c <external_thread+0x9c>
    373d:	4c 8d 65 c0          	lea    -0x40(%rbp),%r12
    3741:	48 8d 5d b0          	lea    -0x50(%rbp),%rbx
        data->buffers->buffer[x].data = "Hello world";
    3745:	4c 8d 2d b8 28 00 00 	lea    0x28b8(%rip),%r13        # 6004 <_IO_stdin_used+0x4>
    374c:	0f 1f 40 00          	nopl   0x0(%rax)
    nanosleep(&req , &rem);
    3750:	4c 89 e6             	mov    %r12,%rsi
    3753:	48 89 df             	mov    %rbx,%rdi
    3756:	e8 f5 eb ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    375b:	49 8b 46 38          	mov    0x38(%r14),%rax
    375f:	48 63 10             	movslq (%rax),%rdx
    3762:	85 d2                	test   %edx,%edx
    3764:	7e 2c                	jle    3792 <external_thread+0x92>
    3766:	48 8b 40 08          	mov    0x8(%rax),%rax
    376a:	48 c1 e2 04          	shl    $0x4,%rdx
    376e:	48 01 c2             	add    %rax,%rdx
    3771:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    3778:	8b 48 08             	mov    0x8(%rax),%ecx
    377b:	85 c9                	test   %ecx,%ecx
    377d:	75 0a                	jne    3789 <external_thread+0x89>
        data->buffers->buffer[x].data = "Hello world";
    377f:	4c 89 28             	mov    %r13,(%rax)
        data->buffers->buffer[x].available = 1;
    3782:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3789:	48 83 c0 10          	add    $0x10,%rax
    378d:	48 39 c2             	cmp    %rax,%rdx
    3790:	75 e6                	jne    3778 <external_thread+0x78>
    asm volatile ("mfence" ::: "memory");
    3792:	0f ae f0             	mfence
  while (data->running == 1) {
    3795:	41 83 7e 2c 01       	cmpl   $0x1,0x2c(%r14)
    379a:	74 b4                	je     3750 <external_thread+0x50>
}
    379c:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    37a0:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    37a9:	75 0f                	jne    37ba <external_thread+0xba>
    37ab:	48 83 c4 30          	add    $0x30,%rsp
    37af:	31 c0                	xor    %eax,%eax
    37b1:	5b                   	pop    %rbx
    37b2:	41 5c                	pop    %r12
    37b4:	41 5d                	pop    %r13
    37b6:	41 5e                	pop    %r14
    37b8:	5d                   	pop    %rbp
    37b9:	c3                   	ret
    37ba:	e8 71 eb ff ff       	call   2330 <__stack_chk_fail@plt>
    37bf:	90                   	nop

00000000000037c0 <timer_thread>:
void* timer_thread(void *arg) {
    37c0:	f3 0f 1e fa          	endbr64
    37c4:	55                   	push   %rbp
    37c5:	48 89 e5             	mov    %rsp,%rbp
    37c8:	41 57                	push   %r15
    37ca:	41 56                	push   %r14
    37cc:	41 55                	push   %r13
    37ce:	41 54                	push   %r12
    37d0:	53                   	push   %rbx
    37d1:	48 83 ec 68          	sub    $0x68,%rsp
    37d5:	ff 15 0d 58 00 00    	call   *0x580d(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    37db:	48 8d 35 2e 28 00 00 	lea    0x282e(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    37e2:	8b 17                	mov    (%rdi),%edx
    37e4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    37ed:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    37f1:	31 c0                	xor    %eax,%eax
    37f3:	49 89 fe             	mov    %rdi,%r14
    37f6:	bf 01 00 00 00       	mov    $0x1,%edi
    37fb:	e8 60 ec ff ff       	call   2460 <__printf_chk@plt>
  struct timespec preempt = {
    3800:	66 0f 6f 05 e8 30 00 00 	movdqa 0x30e8(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    3808:	ba 10 27 00 00       	mov    $0x2710,%edx
    380d:	31 c0                	xor    %eax,%eax
    380f:	48 8d 35 0c 28 00 00 	lea    0x280c(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    3816:	bf 01 00 00 00       	mov    $0x1,%edi
    381b:	0f 29 45 90          	movaps %xmm0,-0x70(%rbp)
    381f:	e8 3c ec ff ff       	call   2460 <__printf_chk@plt>
  while (data->running && n < times) {
    3824:	41 8b 46 2c          	mov    0x2c(%r14),%eax
    3828:	89 85 7c ff ff ff    	mov    %eax,-0x84(%rbp)
    382e:	85 c0                	test   %eax,%eax
    3830:	0f 84 be 00 00 00    	je     38f4 <timer_thread+0x134>
    3836:	48 8d 45 80          	lea    -0x80(%rbp),%rax
  int n = 0;
    383a:	45 31 ff             	xor    %r15d,%r15d
    383d:	4c 8d 65 90          	lea    -0x70(%rbp),%r12
    y++;
    3841:	31 db                	xor    %ebx,%ebx
  int y = 0;
    3843:	c7 85 7c ff ff ff 00 00 00 00 	movl   $0x0,-0x84(%rbp)
    384d:	48 89 85 70 ff ff ff 	mov    %rax,-0x90(%rbp)
    nanosleep(&preempt , &rem2);
    3854:	48 8b b5 70 ff ff ff 	mov    -0x90(%rbp),%rsi
    385b:	4c 89 e7             	mov    %r12,%rdi
    n++;
    385e:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3862:	e8 e9 ea ff ff       	call   2350 <nanosleep@plt>
    y++;
    3867:	8b bd 7c ff ff ff    	mov    -0x84(%rbp),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    386d:	49 63 46 18          	movslq 0x18(%r14),%rax
    y++;
    3871:	83 c7 01             	add    $0x1,%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3874:	85 c0                	test   %eax,%eax
    3876:	7e 54                	jle    38cc <timer_thread+0x10c>
        data->threads[x].tasks[y].scheduled = 0;
    3878:	4c 63 ad 7c ff ff ff 	movslq -0x84(%rbp),%r13
    387f:	49 8b 4e 10          	mov    0x10(%r14),%rcx
    3883:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3887:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    388b:	49 c1 e5 09          	shl    $0x9,%r13
    388f:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3893:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x].task_count;
    3898:	89 f8                	mov    %edi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    389a:	48 8b 71 20          	mov    0x20(%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    389e:	99                   	cltd
    389f:	f7 79 28             	idivl  0x28(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    38a2:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    38a9:	48 63 d2             	movslq %edx,%rdx
    38ac:	48 c1 e2 09          	shl    $0x9,%rdx
    38b0:	c7 84 16 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rsi,%rdx,1)
        data->threads[x].tasks[y].scheduled = 0;
    38bb:	42 c7 84 2e 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rsi,%r13,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    38c7:	49 39 c8             	cmp    %rcx,%r8
    38ca:	75 cc                	jne    3898 <timer_thread+0xd8>
    asm volatile ("mfence" ::: "memory");
    38cc:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    38cf:	49 8b 46 10          	mov    0x10(%r14),%rax
  while (data->running && n < times) {
    38d3:	41 8b 56 2c          	mov    0x2c(%r14),%edx
    y++;
    38d7:	39 78 28             	cmp    %edi,0x28(%rax)
    38da:	0f 4e fb             	cmovle %ebx,%edi
    38dd:	89 bd 7c ff ff ff    	mov    %edi,-0x84(%rbp)
  while (data->running && n < times) {
    38e3:	85 d2                	test   %edx,%edx
    38e5:	74 0d                	je     38f4 <timer_thread+0x134>
    38e7:	41 81 ff 10 27 00 00 	cmp    $0x2710,%r15d
    38ee:	0f 85 60 ff ff ff    	jne    3854 <timer_thread+0x94>
    38f4:	48 8d 3d 3d 27 00 00 	lea    0x273d(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    38fb:	e8 f0 e9 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3900:	49 63 56 1c          	movslq 0x1c(%r14),%rdx
    3904:	85 d2                	test   %edx,%edx
    3906:	7e 6c                	jle    3974 <timer_thread+0x1b4>
    for (int y = 0 ; y < data->task_count ; y++) {
    3908:	49 63 46 28          	movslq 0x28(%r14),%rax
    390c:	85 c0                	test   %eax,%eax
    390e:	7e 64                	jle    3974 <timer_thread+0x1b4>
    3910:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3914:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x].tasks[y].sending = 0;
    3918:	4d 8b 46 10          	mov    0x10(%r14),%r8
    391c:	31 f6                	xor    %esi,%esi
    391e:	48 8d 3c 4a          	lea    (%rdx,%rcx,2),%rdi
    3922:	48 89 c2             	mov    %rax,%rdx
    3925:	48 c1 e7 03          	shl    $0x3,%rdi
    for (int y = 0 ; y < data->task_count ; y++) {
    3929:	49 8b 44 30 20       	mov    0x20(%r8,%rsi,1),%rax
    392e:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    3932:	f6 c6 02             	test   $0x2,%dh
    3935:	74 15                	je     394c <timer_thread+0x18c>
      data->threads[x].tasks[y].sending = 0;
    3937:	c7 80 c0 01 00 00 00 00 00 00 	movl   $0x0,0x1c0(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3941:	48 05 00 02 00 00    	add    $0x200,%rax
    3947:	48 39 c1             	cmp    %rax,%rcx
    394a:	74 1c                	je     3968 <timer_thread+0x1a8>
      data->threads[x].tasks[y].sending = 0;
    394c:	c7 80 c0 01 00 00 00 00 00 00 	movl   $0x0,0x1c0(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3956:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x].tasks[y].sending = 0;
    395c:	c7 40 c0 00 00 00 00 	movl   $0x0,-0x40(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3963:	48 39 c1             	cmp    %rax,%rcx
    3966:	75 e4                	jne    394c <timer_thread+0x18c>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3968:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
    396f:	48 39 f7             	cmp    %rsi,%rdi
    3972:	75 b5                	jne    3929 <timer_thread+0x169>
  asm volatile ("mfence" ::: "memory");
    3974:	0f ae f0             	mfence
  struct timespec drain = {
    3977:	66 0f 6f 05 81 2f 00 00 	movdqa 0x2f81(%rip),%xmm0        # 6900 <_IO_stdin_used+0x900>
    397f:	4c 8d 25 d7 26 00 00 	lea    0x26d7(%rip),%r12        # 605d <_IO_stdin_used+0x5d>
    3986:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
    y++;
    398a:	8b 9d 7c ff ff ff    	mov    -0x84(%rbp),%ebx
    for (int x = 0 ; x < data->thread_count ; x++) {
    3990:	49 63 46 18          	movslq 0x18(%r14),%rax
    y++;
    3994:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3997:	85 c0                	test   %eax,%eax
    3999:	7e 59                	jle    39f4 <timer_thread+0x234>
        data->threads[x].tasks[y].scheduled = 0;
    399b:	4c 63 85 7c ff ff ff 	movslq -0x84(%rbp),%r8
    39a2:	49 8b 4e 10          	mov    0x10(%r14),%rcx
    39a6:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    39aa:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    39ae:	49 c1 e0 09          	shl    $0x9,%r8
    39b2:	4c 8d 14 c1          	lea    (%rcx,%rax,8),%r10
    39b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x].task_count;
    39c0:	89 f8                	mov    %edi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    39c2:	48 8b 71 20          	mov    0x20(%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    39c6:	99                   	cltd
    39c7:	f7 79 28             	idivl  0x28(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    39ca:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    39d1:	48 63 d2             	movslq %edx,%rdx
    39d4:	48 c1 e2 09          	shl    $0x9,%rdx
    39d8:	c7 84 16 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rsi,%rdx,1)
        data->threads[x].tasks[y].scheduled = 0;
    39e3:	42 c7 84 06 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    39ef:	49 39 ca             	cmp    %rcx,%r10
    39f2:	75 cc                	jne    39c0 <timer_thread+0x200>
    asm volatile ("mfence" ::: "memory");
    39f4:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    39f7:	49 8b 56 10          	mov    0x10(%r14),%rdx
    y++;
    39fb:	45 31 ed             	xor    %r13d,%r13d
    39fe:	39 7a 28             	cmp    %edi,0x28(%rdx)
    3a01:	44 0f 4f ef          	cmovg  %edi,%r13d
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a05:	41 8b 7e 18          	mov    0x18(%r14),%edi
    y++;
    3a09:	44 89 ad 7c ff ff ff 	mov    %r13d,-0x84(%rbp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a10:	85 ff                	test   %edi,%edi
    3a12:	0f 8e b9 00 00 00    	jle    3ad1 <timer_thread+0x311>
    3a18:	31 db                	xor    %ebx,%ebx
    3a1a:	45 31 ed             	xor    %r13d,%r13d
    3a1d:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    3a23:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            all_empty = 0;
    3a28:	45 31 ff             	xor    %r15d,%r15d
    3a2b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3a30:	4c 89 f8             	mov    %r15,%rax
    3a33:	48 c1 e0 09          	shl    $0x9,%rax
    3a37:	48 03 44 1a 20       	add    0x20(%rdx,%rbx,1),%rax
        for (int k = 0 ; k < data->thread_count; k++) {
    3a3c:	31 d2                	xor    %edx,%edx
    3a3e:	48 8b 80 b0 01 00 00 	mov    0x1b0(%rax),%rax
    3a45:	eb 19                	jmp    3a60 <timer_thread+0x2a0>
    3a47:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3a50:	4d 85 c0             	test   %r8,%r8
    3a53:	7f 1f                	jg     3a74 <timer_thread+0x2b4>
        for (int k = 0 ; k < data->thread_count; k++) {
    3a55:	83 c2 01             	add    $0x1,%edx
    3a58:	48 83 c0 20          	add    $0x20,%rax
    3a5c:	39 fa                	cmp    %edi,%edx
    3a5e:	74 2a                	je     3a8a <timer_thread+0x2ca>
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3a60:	48 8b 08             	mov    (%rax),%rcx
    3a63:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3a67:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3a6b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3a6f:	48 85 c9             	test   %rcx,%rcx
    3a72:	7e dc                	jle    3a50 <timer_thread+0x290>
    3a74:	bf 01 00 00 00       	mov    $0x1,%edi
    3a79:	4c 89 e6             	mov    %r12,%rsi
    3a7c:	31 c0                	xor    %eax,%eax
    3a7e:	e8 dd e9 ff ff       	call   2460 <__printf_chk@plt>
            break;
    3a83:	41 8b 7e 18          	mov    0x18(%r14),%edi
            all_empty = 0;
    3a87:	45 31 d2             	xor    %r10d,%r10d
      for (int y = 0 ; y < data->thread_count ; y++) {
    3a8a:	49 83 c7 01          	add    $0x1,%r15
    3a8e:	44 39 ff             	cmp    %r15d,%edi
    3a91:	7e 0d                	jle    3aa0 <timer_thread+0x2e0>
    3a93:	49 8b 56 10          	mov    0x10(%r14),%rdx
    3a97:	eb 97                	jmp    3a30 <timer_thread+0x270>
    3a99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3aa0:	41 83 c5 01          	add    $0x1,%r13d
    3aa4:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3aab:	44 39 ef             	cmp    %r13d,%edi
    3aae:	7e 09                	jle    3ab9 <timer_thread+0x2f9>
    3ab0:	49 8b 56 10          	mov    0x10(%r14),%rdx
    3ab4:	e9 6f ff ff ff       	jmp    3a28 <timer_thread+0x268>
    if (all_empty == 1) {
    3ab9:	41 83 fa 01          	cmp    $0x1,%r10d
    3abd:	74 12                	je     3ad1 <timer_thread+0x311>
      nanosleep(&drain , &drainrem);
    3abf:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    3ac3:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
    3ac7:	e8 84 e8 ff ff       	call   2350 <nanosleep@plt>
    3acc:	e9 b9 fe ff ff       	jmp    398a <timer_thread+0x1ca>
    3ad1:	48 8d 3d 7c 25 00 00 	lea    0x257c(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3ad8:	e8 13 e8 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3add:	41 8b 46 2c          	mov    0x2c(%r14),%eax
    3ae1:	85 c0                	test   %eax,%eax
    3ae3:	0f 84 e6 00 00 00    	je     3bcf <timer_thread+0x40f>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ae9:	41 8b 4e 1c          	mov    0x1c(%r14),%ecx
    3aed:	85 c9                	test   %ecx,%ecx
    3aef:	7e 3c                	jle    3b2d <timer_thread+0x36d>
    3af1:	49 8b 56 10          	mov    0x10(%r14),%rdx
    3af5:	31 db                	xor    %ebx,%ebx
    3af7:	45 31 e4             	xor    %r12d,%r12d
    3afa:	4c 8d 2d 6d 25 00 00 	lea    0x256d(%rip),%r13        # 606e <_IO_stdin_used+0x6e>
    3b01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->threads[x].running = 0;
    3b08:	48 8d 04 1a          	lea    (%rdx,%rbx,1),%rax
      if (data->threads[x].type == IO) {
    3b0c:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
      data->threads[x].running = 0;
    3b10:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
      if (data->threads[x].type == IO) {
    3b17:	0f 84 de 00 00 00    	je     3bfb <timer_thread+0x43b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b1d:	41 83 c4 01          	add    $0x1,%r12d
    3b21:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3b28:	41 39 cc             	cmp    %ecx,%r12d
    3b2b:	7c db                	jl     3b08 <timer_thread+0x348>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b2d:	49 63 56 18          	movslq 0x18(%r14),%rdx
    3b31:	85 d2                	test   %edx,%edx
    3b33:	0f 8e 7f 00 00 00    	jle    3bb8 <timer_thread+0x3f8>
      for (int y = 0 ; y < data->task_count ; y++) {
    3b39:	49 63 46 28          	movslq 0x28(%r14),%rax
    3b3d:	85 c0                	test   %eax,%eax
    3b3f:	7e 77                	jle    3bb8 <timer_thread+0x3f8>
    3b41:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3b45:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x].tasks[y].scheduled = 0;
    3b49:	4d 8b 46 10          	mov    0x10(%r14),%r8
    3b4d:	48 8d 3c 4a          	lea    (%rdx,%rcx,2),%rdi
    3b51:	48 89 c6             	mov    %rax,%rsi
    3b54:	31 c9                	xor    %ecx,%ecx
    3b56:	48 c1 e7 03          	shl    $0x3,%rdi
    3b5a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      for (int y = 0 ; y < data->task_count ; y++) {
    3b60:	49 8b 44 08 20       	mov    0x20(%r8,%rcx,1),%rax
    3b65:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3b69:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3b6f:	74 1f                	je     3b90 <timer_thread+0x3d0>
        data->threads[x].tasks[y].scheduled = 0;
    3b71:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3b7b:	48 05 00 02 00 00    	add    $0x200,%rax
    3b81:	48 39 d0             	cmp    %rdx,%rax
    3b84:	74 26                	je     3bac <timer_thread+0x3ec>
    3b86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        data->threads[x].tasks[y].scheduled = 0;
    3b90:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3b9a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x].tasks[y].scheduled = 0;
    3ba0:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3ba7:	48 39 d0             	cmp    %rdx,%rax
    3baa:	75 e4                	jne    3b90 <timer_thread+0x3d0>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bac:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3bb3:	48 39 f9             	cmp    %rdi,%rcx
    3bb6:	75 a8                	jne    3b60 <timer_thread+0x3a0>
    asm volatile ("mfence" ::: "memory");
    3bb8:	0f ae f0             	mfence
    3bbb:	48 8d 3d be 24 00 00 	lea    0x24be(%rip),%rdi        # 6080 <_IO_stdin_used+0x80>
    3bc2:	e8 29 e7 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3bc7:	41 c7 46 2c 00 00 00 00 	movl   $0x0,0x2c(%r14)
    3bcf:	48 8d 3d b1 24 00 00 	lea    0x24b1(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3bd6:	e8 15 e7 ff ff       	call   22f0 <puts@plt>
}
    3bdb:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    3bdf:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3be8:	75 4c                	jne    3c36 <timer_thread+0x476>
    3bea:	48 83 c4 68          	add    $0x68,%rsp
    3bee:	31 c0                	xor    %eax,%eax
    3bf0:	5b                   	pop    %rbx
    3bf1:	41 5c                	pop    %r12
    3bf3:	41 5d                	pop    %r13
    3bf5:	41 5e                	pop    %r14
    3bf7:	41 5f                	pop    %r15
    3bf9:	5d                   	pop    %rbp
    3bfa:	c3                   	ret
    3bfb:	4c 89 ef             	mov    %r13,%rdi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3bfe:	41 83 c4 01          	add    $0x1,%r12d
    3c02:	e8 e9 e6 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]._eventfd, 1);
    3c07:	49 8b 46 10          	mov    0x10(%r14),%rax
    3c0b:	be 01 00 00 00       	mov    $0x1,%esi
    3c10:	8b 7c 18 48          	mov    0x48(%rax,%rbx,1),%edi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c14:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
        eventfd_write(data->threads[x]._eventfd, 1);
    3c1b:	e8 f0 e7 ff ff       	call   2410 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c20:	41 8b 4e 1c          	mov    0x1c(%r14),%ecx
    3c24:	41 39 cc             	cmp    %ecx,%r12d
    3c27:	0f 8d 00 ff ff ff    	jge    3b2d <timer_thread+0x36d>
    3c2d:	49 8b 56 10          	mov    0x10(%r14),%rdx
    3c31:	e9 d2 fe ff ff       	jmp    3b08 <timer_thread+0x348>
}
    3c36:	e8 f5 e6 ff ff       	call   2330 <__stack_chk_fail@plt>
    3c3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003c40 <strtolower>:
void strtolower(char *str) {
    3c40:	f3 0f 1e fa          	endbr64
    3c44:	55                   	push   %rbp
    3c45:	48 89 e5             	mov    %rsp,%rbp
    3c48:	41 54                	push   %r12
    3c4a:	53                   	push   %rbx
    3c4b:	ff 15 97 53 00 00    	call   *0x5397(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    for (; *str; ++str)
    3c51:	48 0f be 1f          	movsbq (%rdi),%rbx
void strtolower(char *str) {
    3c55:	49 89 fc             	mov    %rdi,%r12
    for (; *str; ++str)
    3c58:	84 db                	test   %bl,%bl
    3c5a:	74 24                	je     3c80 <strtolower+0x40>
        *str = (char)tolower(*str);
    3c5c:	e8 cf e8 ff ff       	call   2530 <__ctype_tolower_loc@plt>
    3c61:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3c68:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3c6b:	49 83 c4 01          	add    $0x1,%r12
        *str = (char)tolower(*str);
    3c6f:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3c72:	41 88 54 24 ff       	mov    %dl,-0x1(%r12)
    for (; *str; ++str)
    3c77:	49 0f be 1c 24       	movsbq (%r12),%rbx
    3c7c:	84 db                	test   %bl,%bl
    3c7e:	75 e8                	jne    3c68 <strtolower+0x28>
}
    3c80:	5b                   	pop    %rbx
    3c81:	41 5c                	pop    %r12
    3c83:	5d                   	pop    %rbp
    3c84:	c3                   	ret
    3c85:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003c90 <zh_malloc>:
void *zh_malloc(size_t size) {
    3c90:	f3 0f 1e fa          	endbr64
    3c94:	55                   	push   %rbp
    3c95:	48 89 e5             	mov    %rsp,%rbp
    3c98:	ff 15 4a 53 00 00    	call   *0x534a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    void *buf = malloc(size);
    3c9e:	e8 7d e7 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    3ca3:	48 85 c0             	test   %rax,%rax
    3ca6:	74 02                	je     3caa <zh_malloc+0x1a>
}
    3ca8:	5d                   	pop    %rbp
    3ca9:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3caa:	48 8b 0d 6f 53 00 00 	mov    0x536f(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3cb1:	ba 28 00 00 00       	mov    $0x28,%edx
    3cb6:	be 01 00 00 00       	mov    $0x1,%esi
    3cbb:	48 8d 3d 5e 27 00 00 	lea    0x275e(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    3cc2:	e8 19 e8 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    3cc7:	bf 01 00 00 00       	mov    $0x1,%edi
    3ccc:	e8 ef e7 ff ff       	call   24c0 <exit@plt>
    3cd1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3cdc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003ce0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3ce0:	f3 0f 1e fa          	endbr64
    3ce4:	55                   	push   %rbp
    3ce5:	48 89 e5             	mov    %rsp,%rbp
    3ce8:	53                   	push   %rbx
    3ce9:	48 83 ec 08          	sub    $0x8,%rsp
    3ced:	ff 15 f5 52 00 00    	call   *0x52f5(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    const char *dot = strrchr(filename, '.');
    3cf3:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3cf8:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3cfb:	e8 60 e6 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3d00:	48 85 c0             	test   %rax,%rax
    3d03:	74 13                	je     3d18 <get_filename_ext+0x38>
    3d05:	48 39 c3             	cmp    %rax,%rbx
    3d08:	74 0e                	je     3d18 <get_filename_ext+0x38>
}
    3d0a:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    return dot + 1;
    3d0e:	48 83 c0 01          	add    $0x1,%rax
}
    3d12:	c9                   	leave
    3d13:	c3                   	ret
    3d14:	0f 1f 40 00          	nopl   0x0(%rax)
    3d18:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
        return "";
    3d1c:	48 8d 05 ac 23 00 00 	lea    0x23ac(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
}
    3d23:	c9                   	leave
    3d24:	c3                   	ret
    3d25:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003d30 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3d30:	f3 0f 1e fa          	endbr64
    3d34:	55                   	push   %rbp
    3d35:	48 89 e5             	mov    %rsp,%rbp
    3d38:	41 56                	push   %r14
    3d3a:	41 55                	push   %r13
    3d3c:	41 54                	push   %r12
    3d3e:	53                   	push   %rbx
    3d3f:	48 81 ec 10 08 00 00 	sub    $0x810,%rsp
    3d46:	ff 15 9c 52 00 00    	call   *0x529c(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    3d4c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3d55:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    3d59:	31 c0                	xor    %eax,%eax
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3d5b:	4c 8d ad d0 f7 ff ff 	lea    -0x830(%rbp),%r13
    3d62:	49 89 f6             	mov    %rsi,%r14
    3d65:	49 89 d4             	mov    %rdx,%r12
    3d68:	48 89 fe             	mov    %rdi,%rsi
    3d6b:	ba 00 04 00 00       	mov    $0x400,%edx
    3d70:	4c 89 ef             	mov    %r13,%rdi
    3d73:	e8 c8 e6 ff ff       	call   2440 <__strcpy_chk@plt>
    for (; *str; ++str)
    3d78:	48 0f be 9d d0 f7 ff ff 	movsbq -0x830(%rbp),%rbx
    3d80:	84 db                	test   %bl,%bl
    3d82:	74 1e                	je     3da2 <send_headers+0x72>
        *str = (char)tolower(*str);
    3d84:	e8 a7 e7 ff ff       	call   2530 <__ctype_tolower_loc@plt>
    3d89:	48 8b 08             	mov    (%rax),%rcx
    3d8c:	4c 89 e8             	mov    %r13,%rax
    3d8f:	90                   	nop
    3d90:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3d93:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3d97:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3d9a:	48 0f be 18          	movsbq (%rax),%rbx
    3d9e:	84 db                	test   %bl,%bl
    3da0:	75 ee                	jne    3d90 <send_headers+0x60>
    void *buf = malloc(size);
    3da2:	bf 11 00 00 00       	mov    $0x11,%edi
    3da7:	e8 74 e6 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    3dac:	48 85 c0             	test   %rax,%rax
    3daf:	0f 84 72 04 00 00    	je     4227 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3db5:	66 0f 6f 05 53 2b 00 00 	movdqa 0x2b53(%rip),%xmm0        # 6910 <_IO_stdin_used+0x910>
    iov[0].iov_base = zh_malloc(slen);
    3dbd:	49 89 04 24          	mov    %rax,(%r12)
    void *buf = malloc(size);
    3dc1:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3dc6:	49 c7 44 24 08 11 00 00 00 	movq   $0x11,0x8(%r12)
    3dcf:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3dd3:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3dd6:	e8 45 e6 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    3ddb:	48 85 c0             	test   %rax,%rax
    3dde:	0f 84 43 04 00 00    	je     4227 <send_headers+0x4f7>
    3de4:	66 0f 6f 05 34 2b 00 00 	movdqa 0x2b34(%rip),%xmm0        # 6920 <_IO_stdin_used+0x920>
    iov[1].iov_base = zh_malloc(slen);
    3dec:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    const char *dot = strrchr(filename, '.');
    3df1:	4c 89 ef             	mov    %r13,%rdi
    3df4:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3dfe:	49 c7 44 24 18 17 00 00 00 	movq   $0x17,0x18(%r12)
    3e07:	0f 11 00             	movups %xmm0,(%rax)
    3e0a:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3e0e:	be 2e 00 00 00       	mov    $0x2e,%esi
    3e13:	e8 48 e5 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3e18:	48 85 c0             	test   %rax,%rax
    3e1b:	0f 84 df 02 00 00    	je     4100 <send_headers+0x3d0>
    3e21:	4c 39 e8             	cmp    %r13,%rax
    3e24:	0f 84 d6 02 00 00    	je     4100 <send_headers+0x3d0>
    return dot + 1;
    3e2a:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3e2e:	48 8d 3d 68 22 00 00 	lea    0x2268(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3e35:	48 89 de             	mov    %rbx,%rsi
    3e38:	e8 73 e5 ff ff       	call   23b0 <strcmp@plt>
    3e3d:	85 c0                	test   %eax,%eax
    3e3f:	75 1e                	jne    3e5f <send_headers+0x12f>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3e41:	66 0f 6f 05 e7 2a 00 00 	movdqa 0x2ae7(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3e49:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    3e50:	66 0f 6f 05 e8 2a 00 00 	movdqa 0x2ae8(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3e58:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("jpeg", file_ext) == 0)
    3e5f:	48 89 de             	mov    %rbx,%rsi
    3e62:	48 8d 3d 38 22 00 00 	lea    0x2238(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3e69:	e8 42 e5 ff ff       	call   23b0 <strcmp@plt>
    3e6e:	85 c0                	test   %eax,%eax
    3e70:	75 1e                	jne    3e90 <send_headers+0x160>
    3e72:	66 0f 6f 05 b6 2a 00 00 	movdqa 0x2ab6(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3e7a:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    3e81:	66 0f 6f 05 b7 2a 00 00 	movdqa 0x2ab7(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3e89:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("png", file_ext) == 0)
    3e90:	48 89 de             	mov    %rbx,%rsi
    3e93:	48 8d 3d 0c 22 00 00 	lea    0x220c(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3e9a:	e8 11 e5 ff ff       	call   23b0 <strcmp@plt>
    3e9f:	85 c0                	test   %eax,%eax
    3ea1:	0f 84 09 02 00 00    	je     40b0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    3ea7:	48 89 de             	mov    %rbx,%rsi
    3eaa:	48 8d 3d f9 21 00 00 	lea    0x21f9(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3eb1:	e8 fa e4 ff ff       	call   23b0 <strcmp@plt>
    3eb6:	85 c0                	test   %eax,%eax
    3eb8:	0f 84 a2 02 00 00    	je     4160 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    3ebe:	48 89 de             	mov    %rbx,%rsi
    3ec1:	48 8d 3d e6 21 00 00 	lea    0x21e6(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3ec8:	e8 e3 e4 ff ff       	call   23b0 <strcmp@plt>
    3ecd:	85 c0                	test   %eax,%eax
    3ecf:	0f 84 63 02 00 00    	je     4138 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    3ed5:	48 89 de             	mov    %rbx,%rsi
    3ed8:	48 8d 3d 12 22 00 00 	lea    0x2212(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3edf:	e8 cc e4 ff ff       	call   23b0 <strcmp@plt>
    3ee4:	85 c0                	test   %eax,%eax
    3ee6:	0f 84 24 02 00 00    	je     4110 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    3eec:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3eef:	0f 84 53 01 00 00    	je     4048 <send_headers+0x318>
    if (strcmp("css", file_ext) == 0)
    3ef5:	48 89 de             	mov    %rbx,%rsi
    3ef8:	48 8d 3d b3 21 00 00 	lea    0x21b3(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3eff:	e8 ac e4 ff ff       	call   23b0 <strcmp@plt>
    3f04:	85 c0                	test   %eax,%eax
    3f06:	0f 84 a4 02 00 00    	je     41b0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    3f0c:	48 89 de             	mov    %rbx,%rsi
    3f0f:	48 8d 3d a0 21 00 00 	lea    0x21a0(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3f16:	e8 95 e4 ff ff       	call   23b0 <strcmp@plt>
    3f1b:	85 c0                	test   %eax,%eax
    3f1d:	0f 84 65 02 00 00    	je     4188 <send_headers+0x458>
    slen = strlen(send_buffer);
    3f23:	4c 8d ad d0 fb ff ff 	lea    -0x430(%rbp),%r13
    3f2a:	4c 89 ef             	mov    %r13,%rdi
    3f2d:	e8 ee e3 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    3f32:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3f35:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3f38:	e8 e3 e4 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    3f3d:	48 85 c0             	test   %rax,%rax
    3f40:	0f 84 e1 02 00 00    	je     4227 <send_headers+0x4f7>
    iov[2].iov_base = zh_malloc(slen);
    3f46:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    iov[2].iov_len = slen;
    3f4b:	49 89 5c 24 28       	mov    %rbx,0x28(%r12)
  return __builtin___memcpy_chk (__dest, __src, __len,
    3f50:	83 fb 08             	cmp    $0x8,%ebx
    3f53:	0f 83 37 01 00 00    	jae    4090 <send_headers+0x360>
    3f59:	f6 c3 04             	test   $0x4,%bl
    3f5c:	0f 85 71 02 00 00    	jne    41d3 <send_headers+0x4a3>
    3f62:	85 db                	test   %ebx,%ebx
    3f64:	74 12                	je     3f78 <send_headers+0x248>
    3f66:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    3f6d:	88 10                	mov    %dl,(%rax)
    3f6f:	f6 c3 02             	test   $0x2,%bl
    3f72:	0f 85 8b 02 00 00    	jne    4203 <send_headers+0x4d3>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3f78:	4d 89 f0             	mov    %r14,%r8
    3f7b:	48 8d 0d 38 21 00 00 	lea    0x2138(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    3f82:	4c 89 ef             	mov    %r13,%rdi
    3f85:	31 c0                	xor    %eax,%eax
    3f87:	ba 00 04 00 00       	mov    $0x400,%edx
    3f8c:	be 01 00 00 00       	mov    $0x1,%esi
    3f91:	e8 aa e5 ff ff       	call   2540 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    3f96:	4c 89 ef             	mov    %r13,%rdi
    3f99:	e8 82 e3 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    3f9e:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3fa1:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3fa4:	e8 77 e4 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    3fa9:	48 85 c0             	test   %rax,%rax
    3fac:	0f 84 75 02 00 00    	je     4227 <send_headers+0x4f7>
    iov[3].iov_base = zh_malloc(slen);
    3fb2:	49 89 44 24 30       	mov    %rax,0x30(%r12)
    iov[3].iov_len = slen;
    3fb7:	49 89 5c 24 38       	mov    %rbx,0x38(%r12)
    3fbc:	83 fb 08             	cmp    $0x8,%ebx
    3fbf:	0f 83 13 01 00 00    	jae    40d8 <send_headers+0x3a8>
    3fc5:	f6 c3 04             	test   $0x4,%bl
    3fc8:	0f 85 1d 02 00 00    	jne    41eb <send_headers+0x4bb>
    3fce:	85 db                	test   %ebx,%ebx
    3fd0:	74 12                	je     3fe4 <send_headers+0x2b4>
    3fd2:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    3fd9:	88 10                	mov    %dl,(%rax)
    3fdb:	f6 c3 02             	test   $0x2,%bl
    3fde:	0f 85 31 02 00 00    	jne    4215 <send_headers+0x4e5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3fe4:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    3fe9:	bf 02 00 00 00       	mov    $0x2,%edi
    3fee:	c6 85 d2 fb ff ff 00 	movb   $0x0,-0x42e(%rbp)
    3ff5:	66 89 85 d0 fb ff ff 	mov    %ax,-0x430(%rbp)
    3ffc:	e8 1f e4 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    4001:	48 85 c0             	test   %rax,%rax
    4004:	0f 84 1d 02 00 00    	je     4227 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    400a:	0f b7 95 d0 fb ff ff 	movzwl -0x430(%rbp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4011:	49 89 44 24 40       	mov    %rax,0x40(%r12)
    iov[4].iov_len = slen;
    4016:	49 c7 44 24 48 02 00 00 00 	movq   $0x2,0x48(%r12)
    401f:	66 89 10             	mov    %dx,(%rax)
}
    4022:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    4026:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    402f:	0f 85 19 02 00 00    	jne    424e <send_headers+0x51e>
    4035:	48 81 c4 10 08 00 00 	add    $0x810,%rsp
    403c:	5b                   	pop    %rbx
    403d:	41 5c                	pop    %r12
    403f:	41 5d                	pop    %r13
    4041:	41 5e                	pop    %r14
    4043:	5d                   	pop    %rbp
    4044:	c3                   	ret
    4045:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
    4048:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    404c:	0f 85 a3 fe ff ff    	jne    3ef5 <send_headers+0x1c5>
    4052:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4056:	0f 85 99 fe ff ff    	jne    3ef5 <send_headers+0x1c5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    405c:	66 0f 6f 05 2c 29 00 00 	movdqa 0x292c(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    4064:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    406e:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4075:	66 0f 6f 05 23 29 00 00 	movdqa 0x2923(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    407d:	0f 29 85 e0 fb ff ff 	movaps %xmm0,-0x420(%rbp)
    4084:	48 89 85 ef fb ff ff 	mov    %rax,-0x411(%rbp)
    408b:	e9 65 fe ff ff       	jmp    3ef5 <send_headers+0x1c5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4090:	89 da                	mov    %ebx,%edx
    4092:	48 89 c7             	mov    %rax,%rdi
    4095:	4c 89 ee             	mov    %r13,%rsi
    4098:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    409d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    40a2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    40a5:	c1 e9 03             	shr    $0x3,%ecx
    40a8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    40ab:	e9 c8 fe ff ff       	jmp    3f78 <send_headers+0x248>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40b0:	66 0f 6f 05 78 28 00 00 	movdqa 0x2878(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    40b8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    40bf:	66 0f 6f 05 89 28 00 00 	movdqa 0x2889(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    40c7:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    40ce:	e9 d4 fd ff ff       	jmp    3ea7 <send_headers+0x177>
    40d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    40d8:	89 da                	mov    %ebx,%edx
    40da:	48 89 c7             	mov    %rax,%rdi
    40dd:	4c 89 ee             	mov    %r13,%rsi
    40e0:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    40e5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    40ea:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    40ed:	c1 e9 03             	shr    $0x3,%ecx
    40f0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    40f3:	e9 ec fe ff ff       	jmp    3fe4 <send_headers+0x2b4>
    40f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4100:	48 8d 1d c8 1f 00 00 	lea    0x1fc8(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    4107:	e9 9b fd ff ff       	jmp    3ea7 <send_headers+0x177>
    410c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4110:	66 0f 6f 05 58 28 00 00 	movdqa 0x2858(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4118:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    411f:	66 0f 6f 05 59 28 00 00 	movdqa 0x2859(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4127:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    412e:	e9 b9 fd ff ff       	jmp    3eec <send_headers+0x1bc>
    4133:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4138:	66 0f 6f 05 30 28 00 00 	movdqa 0x2830(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4140:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4147:	66 0f 6f 05 31 28 00 00 	movdqa 0x2831(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    414f:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    4156:	e9 7a fd ff ff       	jmp    3ed5 <send_headers+0x1a5>
    415b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4160:	66 0f 6f 05 c8 27 00 00 	movdqa 0x27c8(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4168:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    416f:	66 0f 6f 05 e9 27 00 00 	movdqa 0x27e9(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    4177:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    417e:	e9 3b fd ff ff       	jmp    3ebe <send_headers+0x18e>
    4183:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4188:	66 0f 6f 05 e0 27 00 00 	movdqa 0x27e0(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4190:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4197:	66 0f 6f 05 21 28 00 00 	movdqa 0x2821(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    419f:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    41a6:	e9 78 fd ff ff       	jmp    3f23 <send_headers+0x1f3>
    41ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    41b0:	66 0f 6f 05 b8 27 00 00 	movdqa 0x27b8(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    41b8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    41bf:	66 0f 6f 05 e9 27 00 00 	movdqa 0x27e9(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    41c7:	0f 11 85 d9 fb ff ff 	movups %xmm0,-0x427(%rbp)
    41ce:	e9 39 fd ff ff       	jmp    3f0c <send_headers+0x1dc>
  return __builtin___memcpy_chk (__dest, __src, __len,
    41d3:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    41d9:	89 db                	mov    %ebx,%ebx
    41db:	89 10                	mov    %edx,(%rax)
    41dd:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    41e2:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    41e6:	e9 8d fd ff ff       	jmp    3f78 <send_headers+0x248>
    41eb:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    41f1:	89 db                	mov    %ebx,%ebx
    41f3:	89 10                	mov    %edx,(%rax)
    41f5:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    41fa:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    41fe:	e9 e1 fd ff ff       	jmp    3fe4 <send_headers+0x2b4>
    4203:	89 db                	mov    %ebx,%ebx
    4205:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    420b:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4210:	e9 63 fd ff ff       	jmp    3f78 <send_headers+0x248>
    4215:	89 db                	mov    %ebx,%ebx
    4217:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    421d:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4222:	e9 bd fd ff ff       	jmp    3fe4 <send_headers+0x2b4>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4227:	48 8b 0d f2 4d 00 00 	mov    0x4df2(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    422e:	ba 28 00 00 00       	mov    $0x28,%edx
    4233:	be 01 00 00 00       	mov    $0x1,%esi
    4238:	48 8d 3d e1 21 00 00 	lea    0x21e1(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    423f:	e8 9c e2 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    4244:	bf 01 00 00 00       	mov    $0x1,%edi
    4249:	e8 72 e2 ff ff       	call   24c0 <exit@plt>
}
    424e:	e8 dd e0 ff ff       	call   2330 <__stack_chk_fail@plt>
    4253:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    425e:	66 90                	xchg   %ax,%ax

0000000000004260 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4260:	f3 0f 1e fa          	endbr64
    4264:	55                   	push   %rbp
    4265:	48 89 e5             	mov    %rsp,%rbp
    4268:	41 56                	push   %r14
    426a:	41 55                	push   %r13
    426c:	41 54                	push   %r12
    426e:	53                   	push   %rbx
    426f:	ff 15 73 4d 00 00    	call   *0x4d73(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    4275:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    4278:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    427b:	48 89 f3             	mov    %rsi,%rbx
    427e:	49 89 d6             	mov    %rdx,%r14
    void *buf = malloc(size);
    4281:	e8 9a e1 ff ff       	call   2420 <malloc@plt>
    4286:	49 89 c4             	mov    %rax,%r12
    if (!buf) {
    4289:	48 85 c0             	test   %rax,%rax
    428c:	74 69                	je     42f7 <copy_file_contents+0x97>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    428e:	4c 89 ef             	mov    %r13,%rdi
    4291:	31 f6                	xor    %esi,%esi
    4293:	31 c0                	xor    %eax,%eax
    4295:	e8 f6 e1 ff ff       	call   2490 <open@plt>
    429a:	41 89 c5             	mov    %eax,%r13d
    if (fd < 0)
    429d:	85 c0                	test   %eax,%eax
    429f:	0f 88 d8 e2 ff ff    	js     257d <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    42a5:	48 89 da             	mov    %rbx,%rdx
    42a8:	4c 89 e6             	mov    %r12,%rsi
    42ab:	89 c7                	mov    %eax,%edi
    42ad:	e8 de e0 ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    42b2:	48 98                	cltq
    42b4:	48 39 d8             	cmp    %rbx,%rax
    42b7:	7c 1f                	jl     42d8 <copy_file_contents+0x78>
    close(fd);
    42b9:	44 89 ef             	mov    %r13d,%edi
    42bc:	e8 af e0 ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    42c1:	4d 89 26             	mov    %r12,(%r14)
    iov->iov_len = file_size;
    42c4:	49 89 5e 08          	mov    %rbx,0x8(%r14)
}
    42c8:	5b                   	pop    %rbx
    42c9:	41 5c                	pop    %r12
    42cb:	41 5d                	pop    %r13
    42cd:	41 5e                	pop    %r14
    42cf:	5d                   	pop    %rbp
    42d0:	c3                   	ret
    42d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    42d8:	48 8b 0d 41 4d 00 00 	mov    0x4d41(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    42df:	ba 1a 00 00 00       	mov    $0x1a,%edx
    42e4:	be 01 00 00 00       	mov    $0x1,%esi
    42e9:	48 8d 3d e0 1d 00 00 	lea    0x1de0(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    42f0:	e8 eb e1 ff ff       	call   24e0 <fwrite@plt>
    42f5:	eb c2                	jmp    42b9 <copy_file_contents+0x59>
    42f7:	48 8b 0d 22 4d 00 00 	mov    0x4d22(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    42fe:	ba 28 00 00 00       	mov    $0x28,%edx
    4303:	be 01 00 00 00       	mov    $0x1,%esi
    4308:	48 8d 3d 11 21 00 00 	lea    0x2111(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    430f:	e8 cc e1 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    4314:	bf 01 00 00 00       	mov    $0x1,%edi
    4319:	e8 a2 e1 ff ff       	call   24c0 <exit@plt>
    431e:	66 90                	xchg   %ax,%ax

0000000000004320 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4320:	f3 0f 1e fa          	endbr64
    4324:	55                   	push   %rbp
    4325:	48 89 e5             	mov    %rsp,%rbp
    4328:	ff 15 ba 4c 00 00    	call   *0x4cba(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    432e:	8b 46 44             	mov    0x44(%rsi),%eax
    4331:	48 89 fa             	mov    %rdi,%rdx
    4334:	48 89 f7             	mov    %rsi,%rdi
    4337:	8d 70 01             	lea    0x1(%rax),%esi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    433a:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4340:	48 8b 07             	mov    (%rdi),%rax
    4343:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4346:	f6 c1 02             	test   $0x2,%cl
    4349:	74 00                	je     434b <add_write_request+0x2b>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    434b:	89 f0                	mov    %esi,%eax
    434d:	44 29 c0             	sub    %r8d,%eax
    4350:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4353:	0f 82 30 e2 ff ff    	jb     2589 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4359:	c1 e9 0a             	shr    $0xa,%ecx
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    435c:	8b 47 44             	mov    0x44(%rdi),%eax
    435f:	23 47 58             	and    0x58(%rdi),%eax
		sq->sqe_tail = next;
    4362:	89 77 44             	mov    %esi,0x44(%rdi)
	if (ring->flags & IORING_SETUP_SQE128)
    4365:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4368:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    436b:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    436f:	d3 e0                	shl    %cl,%eax
    4371:	8b 4a 04             	mov    0x4(%rdx),%ecx
    4374:	48 c1 e0 06          	shl    $0x6,%rax
    4378:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    437c:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    4382:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4385:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4389:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    438f:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4397:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    439b:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    439e:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    43a5:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    43ad:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    43b1:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    43b5:	e8 86 df ff ff       	call   2340 <io_uring_submit@plt>
}
    43ba:	31 c0                	xor    %eax,%eax
    43bc:	5d                   	pop    %rbp
    43bd:	c3                   	ret
    43be:	66 90                	xchg   %ax,%ax

00000000000043c0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    43c0:	f3 0f 1e fa          	endbr64
    43c4:	55                   	push   %rbp
    43c5:	48 89 e5             	mov    %rsp,%rbp
    43c8:	41 56                	push   %r14
    43ca:	41 55                	push   %r13
    43cc:	41 54                	push   %r12
    43ce:	53                   	push   %rbx
    43cf:	ff 15 13 4c 00 00    	call   *0x4c13(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    43d5:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    43d8:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    43de:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    43e1:	83 c0 01             	add    $0x1,%eax
    43e4:	48 89 f3             	mov    %rsi,%rbx
    43e7:	41 89 fe             	mov    %edi,%r14d
		head = IO_URING_READ_ONCE(*sq->khead);
    43ea:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    43ec:	f6 c1 02             	test   $0x2,%cl
    43ef:	74 00                	je     43f1 <add_read_request+0x31>
	if (next - head <= sq->ring_entries) {
    43f1:	89 c2                	mov    %eax,%edx
    43f3:	29 f2                	sub    %esi,%edx
    43f5:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    43f8:	0f 82 9b e1 ff ff    	jb     2599 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    43fe:	44 8b 63 44          	mov    0x44(%rbx),%r12d
	if (ring->flags & IORING_SETUP_SQE128)
    4402:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    4405:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4408:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    440d:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4410:	44 23 63 58          	and    0x58(%rbx),%r12d
    4414:	41 d3 e4             	shl    %cl,%r12d
    4417:	49 c1 e4 06          	shl    $0x6,%r12
    441b:	4c 03 63 38          	add    0x38(%rbx),%r12
    441f:	e8 fc df ff ff       	call   2420 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    4424:	be 01 00 00 00       	mov    $0x1,%esi
    4429:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    442e:	49 89 c5             	mov    %rax,%r13
    req->iov[0].iov_base = malloc(READ_SZ);
    4431:	e8 6a df ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    4436:	45 89 75 08          	mov    %r14d,0x8(%r13)
	sqe->addr3 = 0;
    443a:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    443e:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4441:	49 89 45 10          	mov    %rax,0x10(%r13)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4445:	49 8d 45 10          	lea    0x10(%r13),%rax
    req->iov[0].iov_len = READ_SZ;
    4449:	49 c7 45 18 00 20 00 00 	movq   $0x2000,0x18(%r13)
    req->event_type = EVENT_TYPE_READ;
    4451:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
	sqe->fd = fd;
    4459:	45 89 74 24 04       	mov    %r14d,0x4(%r12)
	sqe->user_data = (unsigned long) data;
    445e:	4d 89 6c 24 20       	mov    %r13,0x20(%r12)
	sqe->opcode = (__u8) op;
    4463:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->off = offset;
    446b:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4474:	49 89 44 24 10       	mov    %rax,0x10(%r12)
	sqe->len = len;
    4479:	49 c7 44 24 18 01 00 00 00 	movq   $0x1,0x18(%r12)
	sqe->buf_index = 0;
    4482:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->addr3 = 0;
    448b:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    io_uring_submit(ring);
    4491:	e8 aa de ff ff       	call   2340 <io_uring_submit@plt>
}
    4496:	5b                   	pop    %rbx
    4497:	31 c0                	xor    %eax,%eax
    4499:	41 5c                	pop    %r12
    449b:	41 5d                	pop    %r13
    449d:	41 5e                	pop    %r14
    449f:	5d                   	pop    %rbp
    44a0:	c3                   	ret
    44a1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    44ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000044b0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    44b0:	f3 0f 1e fa          	endbr64
    44b4:	55                   	push   %rbp
    44b5:	48 89 e5             	mov    %rsp,%rbp
    44b8:	41 57                	push   %r15
    44ba:	41 56                	push   %r14
    44bc:	41 55                	push   %r13
    44be:	41 54                	push   %r12
    44c0:	53                   	push   %rbx
    44c1:	48 83 ec 08          	sub    $0x8,%rsp
    44c5:	ff 15 1d 4b 00 00    	call   *0x4b1d(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    44cb:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    44ce:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    44d3:	41 89 f7             	mov    %esi,%r15d
    44d6:	49 89 d4             	mov    %rdx,%r12
    void *buf = malloc(size);
    44d9:	e8 42 df ff ff       	call   2420 <malloc@plt>
    44de:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    44e1:	48 85 c0             	test   %rax,%rax
    44e4:	0f 84 eb 00 00 00    	je     45d5 <_send_static_string_content+0x125>
    unsigned long slen = strlen(str);
    44ea:	4c 89 ef             	mov    %r13,%rdi
    44ed:	e8 2e de ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    44f2:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    44f9:	44 89 7b 08          	mov    %r15d,0x8(%rbx)
    void *buf = malloc(size);
    44fd:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4500:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    4503:	e8 18 df ff ff       	call   2420 <malloc@plt>
    4508:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    450b:	48 85 c0             	test   %rax,%rax
    450e:	0f 84 c1 00 00 00    	je     45d5 <_send_static_string_content+0x125>
    req->iov[0].iov_base = zh_malloc(slen);
    4514:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4518:	4c 89 f2             	mov    %r14,%rdx
    451b:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    451e:	4c 89 73 18          	mov    %r14,0x18(%rbx)
    4522:	e8 c9 de ff ff       	call   23f0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4527:	41 8b 44 24 44       	mov    0x44(%r12),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    452c:	41 8b 8c 24 c0 00 00 00 	mov    0xc0(%r12),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4534:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4537:	49 8b 04 24          	mov    (%r12),%rax
    453b:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    453d:	f6 c1 02             	test   $0x2,%cl
    4540:	0f 85 8a 00 00 00    	jne    45d0 <_send_static_string_content+0x120>
	if (next - head <= sq->ring_entries) {
    4546:	89 d0                	mov    %edx,%eax
    4548:	29 f0                	sub    %esi,%eax
    454a:	41 39 44 24 5c       	cmp    %eax,0x5c(%r12)
    454f:	0f 82 4e e0 ff ff    	jb     25a3 <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4555:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4558:	41 8b 44 24 44       	mov    0x44(%r12),%eax
    455d:	41 23 44 24 58       	and    0x58(%r12),%eax
    io_uring_submit(ring);
    4562:	4c 89 e7             	mov    %r12,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    4565:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4568:	41 89 54 24 44       	mov    %edx,0x44(%r12)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    456d:	8b 53 04             	mov    0x4(%rbx),%edx
	sqe->addr3 = 0;
    4570:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4574:	d3 e0                	shl    %cl,%eax
    4576:	8b 4b 08             	mov    0x8(%rbx),%ecx
    req->event_type = EVENT_TYPE_WRITE;
    4579:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    457f:	48 c1 e0 06          	shl    $0x6,%rax
    4583:	49 03 44 24 38       	add    0x38(%r12),%rax
	sqe->fd = fd;
    4588:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    458b:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    458f:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4595:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    459d:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    45a1:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    45a4:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    45ab:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    45b3:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    45b7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    45bb:	48 83 c4 08          	add    $0x8,%rsp
    45bf:	5b                   	pop    %rbx
    45c0:	41 5c                	pop    %r12
    45c2:	41 5d                	pop    %r13
    45c4:	41 5e                	pop    %r14
    45c6:	41 5f                	pop    %r15
    45c8:	5d                   	pop    %rbp
    io_uring_submit(ring);
    45c9:	e9 72 dd ff ff       	jmp    2340 <io_uring_submit@plt>
    45ce:	66 90                	xchg   %ax,%ax
		head = io_uring_smp_load_acquire(sq->khead);
    45d0:	e9 71 ff ff ff       	jmp    4546 <_send_static_string_content+0x96>
    45d5:	48 8b 0d 44 4a 00 00 	mov    0x4a44(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    45dc:	ba 28 00 00 00       	mov    $0x28,%edx
    45e1:	be 01 00 00 00       	mov    $0x1,%esi
    45e6:	48 8d 3d 33 1e 00 00 	lea    0x1e33(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    45ed:	e8 ee de ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    45f2:	bf 01 00 00 00       	mov    $0x1,%edi
    45f7:	e8 c4 de ff ff       	call   24c0 <exit@plt>
    45fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004600 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4600:	f3 0f 1e fa          	endbr64
    4604:	55                   	push   %rbp
    4605:	48 89 e5             	mov    %rsp,%rbp
    4608:	ff 15 da 49 00 00    	call   *0x49da(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
}
    460e:	5d                   	pop    %rbp
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    460f:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4612:	89 fe                	mov    %edi,%esi
    4614:	48 8b 3d fd 49 00 00 	mov    0x49fd(%rip),%rdi        # 9018 <unimplemented_content>
    461b:	e9 90 fe ff ff       	jmp    44b0 <_send_static_string_content>

0000000000004620 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4620:	f3 0f 1e fa          	endbr64
    4624:	55                   	push   %rbp
    4625:	48 89 e5             	mov    %rsp,%rbp
    4628:	ff 15 ba 49 00 00    	call   *0x49ba(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
}
    462e:	5d                   	pop    %rbp
void handle_http_404(int client_socket, struct io_uring *ring) {
    462f:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4632:	89 fe                	mov    %edi,%esi
    4634:	48 8b 3d d5 49 00 00 	mov    0x49d5(%rip),%rdi        # 9010 <http_404_content>
    463b:	e9 70 fe ff ff       	jmp    44b0 <_send_static_string_content>

0000000000004640 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4640:	f3 0f 1e fa          	endbr64
    4644:	55                   	push   %rbp
    4645:	48 89 e5             	mov    %rsp,%rbp
    4648:	41 57                	push   %r15
    464a:	41 56                	push   %r14
    464c:	41 55                	push   %r13
    464e:	41 54                	push   %r12
    4650:	53                   	push   %rbx
    4651:	48 81 ec a8 04 00 00 	sub    $0x4a8,%rsp
    4658:	ff 15 8a 49 00 00    	call   *0x498a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    465e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4667:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    466b:	31 c0                	xor    %eax,%eax
    466d:	49 89 fc             	mov    %rdi,%r12
    4670:	41 89 f5             	mov    %esi,%r13d
    4673:	49 89 d6             	mov    %rdx,%r14
    if (path[strlen(path) - 1] == '/') {
    4676:	e8 a5 dc ff ff       	call   2320 <strlen@plt>
    467b:	41 80 7c 04 ff 2f    	cmpb   $0x2f,-0x1(%r12,%rax,1)
    4681:	48 89 c3             	mov    %rax,%rbx
    4684:	0f 84 b6 00 00 00    	je     4740 <handle_get_method+0x100>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    468a:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    468f:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4693:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4698:	4c 89 e6             	mov    %r12,%rsi
    469b:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    46a2:	66 89 85 c4 fb ff ff 	mov    %ax,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    46a9:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    46b0:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    46ba:	e8 11 dd ff ff       	call   23d0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    46bf:	48 8d b5 30 fb ff ff 	lea    -0x4d0(%rbp),%rsi
    46c6:	4c 89 ff             	mov    %r15,%rdi
    46c9:	e8 12 dd ff ff       	call   23e0 <stat@plt>
    46ce:	83 f8 ff             	cmp    $0xffffffff,%eax
    46d1:	0f 84 41 01 00 00    	je     4818 <handle_get_method+0x1d8>
        if (S_ISREG(path_stat.st_mode)) {
    46d7:	8b 85 48 fb ff ff    	mov    -0x4b8(%rbp),%eax
    46dd:	25 00 f0 00 00       	and    $0xf000,%eax
    46e2:	3d 00 80 00 00       	cmp    $0x8000,%eax
    46e7:	0f 84 b3 00 00 00    	je     47a0 <handle_get_method+0x160>
    _send_static_string_content(http_404_content, client_socket, ring);
    46ed:	48 8b 3d 1c 49 00 00 	mov    0x491c(%rip),%rdi        # 9010 <http_404_content>
    46f4:	4c 89 f2             	mov    %r14,%rdx
    46f7:	44 89 ee             	mov    %r13d,%esi
    46fa:	e8 b1 fd ff ff       	call   44b0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    46ff:	4c 89 fa             	mov    %r15,%rdx
    4702:	bf 01 00 00 00       	mov    $0x1,%edi
    4707:	31 c0                	xor    %eax,%eax
    4709:	48 8d 35 10 1a 00 00 	lea    0x1a10(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    4710:	e8 4b dd ff ff       	call   2460 <__printf_chk@plt>
}
    4715:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    4719:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4722:	0f 85 20 01 00 00    	jne    4848 <handle_get_method+0x208>
    4728:	48 81 c4 a8 04 00 00 	add    $0x4a8,%rsp
    472f:	5b                   	pop    %rbx
    4730:	41 5c                	pop    %r12
    4732:	41 5d                	pop    %r13
    4734:	41 5e                	pop    %r14
    4736:	41 5f                	pop    %r15
    4738:	5d                   	pop    %rbp
    4739:	c3                   	ret
    473a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4740:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4745:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
    474c:	4c 89 e6             	mov    %r12,%rsi
    474f:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4754:	66 89 95 c4 fb ff ff 	mov    %dx,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    475b:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    475e:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
    4765:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    476f:	e8 5c dc ff ff       	call   23d0 <__memcpy_chk@plt>
    4774:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4779:	49 8d 7c 1f 06       	lea    0x6(%r15,%rbx,1),%rdi
    477e:	ba 0b 00 00 00       	mov    $0xb,%edx
    4783:	48 29 d9             	sub    %rbx,%rcx
    4786:	48 8d 35 5e 19 00 00 	lea    0x195e(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    478d:	e8 3e dc ff ff       	call   23d0 <__memcpy_chk@plt>
    4792:	e9 28 ff ff ff       	jmp    46bf <handle_get_method+0x7f>
    4797:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    47a0:	bf 70 00 00 00       	mov    $0x70,%edi
    47a5:	e8 76 dc ff ff       	call   2420 <malloc@plt>
    47aa:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    47ad:	48 85 c0             	test   %rax,%rax
    47b0:	0f 84 97 00 00 00    	je     484d <handle_get_method+0x20d>
            req->client_socket = client_socket;
    47b6:	44 89 68 08          	mov    %r13d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    47ba:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    47c1:	48 8d 50 10          	lea    0x10(%rax),%rdx
    47c5:	4c 89 ff             	mov    %r15,%rdi
            req->iovec_count = 6;
    47c8:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    47cf:	e8 5c f5 ff ff       	call   3d30 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    47d4:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    47db:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    47df:	4c 89 ff             	mov    %r15,%rdi
    47e2:	e8 79 fa ff ff       	call   4260 <copy_file_contents>
    47e7:	4c 89 fa             	mov    %r15,%rdx
    47ea:	bf 01 00 00 00       	mov    $0x1,%edi
    47ef:	31 c0                	xor    %eax,%eax
    47f1:	48 8b 8d 60 fb ff ff 	mov    -0x4a0(%rbp),%rcx
    47f8:	48 8d 35 0f 19 00 00 	lea    0x190f(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    47ff:	e8 5c dc ff ff       	call   2460 <__printf_chk@plt>
            add_write_request(req, ring);
    4804:	4c 89 f6             	mov    %r14,%rsi
    4807:	48 89 df             	mov    %rbx,%rdi
    480a:	e8 11 fb ff ff       	call   4320 <add_write_request>
    480f:	e9 01 ff ff ff       	jmp    4715 <handle_get_method+0xd5>
    4814:	0f 1f 40 00          	nopl   0x0(%rax)
    4818:	4c 89 fa             	mov    %r15,%rdx
    481b:	4c 89 e1             	mov    %r12,%rcx
    481e:	48 8d 35 d1 18 00 00 	lea    0x18d1(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    4825:	31 c0                	xor    %eax,%eax
    4827:	bf 01 00 00 00       	mov    $0x1,%edi
    482c:	e8 2f dc ff ff       	call   2460 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    4831:	48 8b 3d d8 47 00 00 	mov    0x47d8(%rip),%rdi        # 9010 <http_404_content>
    4838:	4c 89 f2             	mov    %r14,%rdx
    483b:	44 89 ee             	mov    %r13d,%esi
    483e:	e8 6d fc ff ff       	call   44b0 <_send_static_string_content>
}
    4843:	e9 cd fe ff ff       	jmp    4715 <handle_get_method+0xd5>
}
    4848:	e8 e3 da ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    484d:	48 8b 0d cc 47 00 00 	mov    0x47cc(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4854:	ba 28 00 00 00       	mov    $0x28,%edx
    4859:	be 01 00 00 00       	mov    $0x1,%esi
    485e:	48 8d 3d bb 1b 00 00 	lea    0x1bbb(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    4865:	e8 76 dc ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    486a:	bf 01 00 00 00       	mov    $0x1,%edi
    486f:	e8 4c dc ff ff       	call   24c0 <exit@plt>
    4874:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    487f:	90                   	nop

0000000000004880 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4880:	f3 0f 1e fa          	endbr64
    4884:	55                   	push   %rbp
    4885:	48 89 e5             	mov    %rsp,%rbp
    4888:	41 57                	push   %r15
    488a:	41 56                	push   %r14
    488c:	41 55                	push   %r13
    488e:	41 54                	push   %r12
    4890:	53                   	push   %rbx
    4891:	48 83 ec 28          	sub    $0x28,%rsp
    4895:	ff 15 4d 47 00 00    	call   *0x474d(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    method = strtok_r(method_buffer, " ", &saveptr);
    489b:	4c 8d 35 e3 17 00 00 	lea    0x17e3(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    48a2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    48ab:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    48af:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    48b1:	4c 8d 7d c0          	lea    -0x40(%rbp),%r15
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    48b5:	41 89 f4             	mov    %esi,%r12d
    48b8:	49 89 d5             	mov    %rdx,%r13
    method = strtok_r(method_buffer, " ", &saveptr);
    48bb:	4c 89 f6             	mov    %r14,%rsi
    48be:	4c 89 fa             	mov    %r15,%rdx
    48c1:	e8 ba da ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    48c6:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    48c9:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    48cc:	84 d2                	test   %dl,%dl
    48ce:	88 55 bf             	mov    %dl,-0x41(%rbp)
    48d1:	74 22                	je     48f5 <handle_http_method+0x75>
        *str = (char)tolower(*str);
    48d3:	e8 58 dc ff ff       	call   2530 <__ctype_tolower_loc@plt>
    48d8:	48 0f be 55 bf       	movsbq -0x41(%rbp),%rdx
    48dd:	48 89 d9             	mov    %rbx,%rcx
    48e0:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    48e3:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    48e7:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    48ea:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    48ed:	48 0f be 11          	movsbq (%rcx),%rdx
    48f1:	84 d2                	test   %dl,%dl
    48f3:	75 eb                	jne    48e0 <handle_http_method+0x60>
    path = strtok_r(NULL, " ", &saveptr);
    48f5:	4c 89 fa             	mov    %r15,%rdx
    48f8:	4c 89 f6             	mov    %r14,%rsi
    48fb:	31 ff                	xor    %edi,%edi
    48fd:	e8 7e da ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4902:	48 8d 35 2a 18 00 00 	lea    0x182a(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    4909:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    490c:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    490f:	e8 9c da ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4914:	4c 89 ea             	mov    %r13,%rdx
    4917:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    491a:	85 c0                	test   %eax,%eax
    491c:	75 2a                	jne    4948 <handle_http_method+0xc8>
        handle_get_method(path, client_socket, ring);
    491e:	4c 89 f7             	mov    %r14,%rdi
    4921:	e8 1a fd ff ff       	call   4640 <handle_get_method>
}
    4926:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    492a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4933:	75 21                	jne    4956 <handle_http_method+0xd6>
    4935:	48 83 c4 28          	add    $0x28,%rsp
    4939:	5b                   	pop    %rbx
    493a:	41 5c                	pop    %r12
    493c:	41 5d                	pop    %r13
    493e:	41 5e                	pop    %r14
    4940:	41 5f                	pop    %r15
    4942:	5d                   	pop    %rbp
    4943:	c3                   	ret
    4944:	0f 1f 40 00          	nopl   0x0(%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4948:	48 8b 3d c9 46 00 00 	mov    0x46c9(%rip),%rdi        # 9018 <unimplemented_content>
    494f:	e8 5c fb ff ff       	call   44b0 <_send_static_string_content>
}
    4954:	eb d0                	jmp    4926 <handle_http_method+0xa6>
    4956:	e8 d5 d9 ff ff       	call   2330 <__stack_chk_fail@plt>
    495b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004960 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4960:	f3 0f 1e fa          	endbr64
    4964:	55                   	push   %rbp
    4965:	48 89 e5             	mov    %rsp,%rbp
    4968:	ff 15 7a 46 00 00    	call   *0x467a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    for (int i = 0; i < dest_sz; i++) {
    496e:	85 d2                	test   %edx,%edx
    4970:	7e 36                	jle    49a8 <get_line+0x48>
    4972:	48 63 d2             	movslq %edx,%rdx
    4975:	48 83 c7 01          	add    $0x1,%rdi
    4979:	48 01 f2             	add    %rsi,%rdx
    497c:	eb 0f                	jmp    498d <get_line+0x2d>
    497e:	66 90                	xchg   %ax,%ax
    4980:	48 83 c6 01          	add    $0x1,%rsi
    4984:	48 83 c7 01          	add    $0x1,%rdi
    4988:	48 39 d6             	cmp    %rdx,%rsi
    498b:	74 1b                	je     49a8 <get_line+0x48>
        dest[i] = src[i];
    498d:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4991:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4993:	3c 0d                	cmp    $0xd,%al
    4995:	75 e9                	jne    4980 <get_line+0x20>
    4997:	80 3f 0a             	cmpb   $0xa,(%rdi)
    499a:	75 e4                	jne    4980 <get_line+0x20>
            return 0;
    499c:	31 c0                	xor    %eax,%eax
            dest[i] = '\0';
    499e:	c6 06 00             	movb   $0x0,(%rsi)
}
    49a1:	5d                   	pop    %rbp
    49a2:	c3                   	ret
    49a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    return 1;
    49a8:	b8 01 00 00 00       	mov    $0x1,%eax
}
    49ad:	5d                   	pop    %rbp
    49ae:	c3                   	ret
    49af:	90                   	nop

00000000000049b0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    49b0:	f3 0f 1e fa          	endbr64
    49b4:	55                   	push   %rbp
    49b5:	48 89 e5             	mov    %rsp,%rbp
    49b8:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    49bf:	ff 15 23 46 00 00    	call   *0x4623(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    49c5:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    49c9:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    49d2:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
    49d6:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    49d8:	4c 8d 95 f0 fb ff ff 	lea    -0x410(%rbp),%r10
    49df:	4c 8d 4d f0          	lea    -0x10(%rbp),%r9
    49e3:	4c 89 d0             	mov    %r10,%rax
    49e6:	eb 15                	jmp    49fd <handle_client_request+0x4d>
    49e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    49f0:	48 83 c0 01          	add    $0x1,%rax
    49f4:	48 83 c1 01          	add    $0x1,%rcx
    49f8:	4c 39 c8             	cmp    %r9,%rax
    49fb:	74 43                	je     4a40 <handle_client_request+0x90>
        dest[i] = src[i];
    49fd:	44 0f b6 01          	movzbl (%rcx),%r8d
    4a01:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4a04:	41 80 f8 0d          	cmp    $0xd,%r8b
    4a08:	75 e6                	jne    49f0 <handle_client_request+0x40>
    4a0a:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4a0e:	75 e0                	jne    49f0 <handle_client_request+0x40>
            dest[i] = '\0';
    4a10:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4a13:	8b 47 08             	mov    0x8(%rdi),%eax
    4a16:	48 89 f2             	mov    %rsi,%rdx
    4a19:	4c 89 d7             	mov    %r10,%rdi
    4a1c:	89 c6                	mov    %eax,%esi
    4a1e:	e8 5d fe ff ff       	call   4880 <handle_http_method>
}
    4a23:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    4a27:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4a30:	75 35                	jne    4a67 <handle_client_request+0xb7>
    4a32:	c9                   	leave
    4a33:	31 c0                	xor    %eax,%eax
    4a35:	c3                   	ret
    4a36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4a40:	48 8b 0d d9 45 00 00 	mov    0x45d9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4a47:	ba 12 00 00 00       	mov    $0x12,%edx
    4a4c:	be 01 00 00 00       	mov    $0x1,%esi
    4a51:	48 8d 3d df 16 00 00 	lea    0x16df(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    4a58:	e8 83 da ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    4a5d:	bf 01 00 00 00       	mov    $0x1,%edi
    4a62:	e8 59 da ff ff       	call   24c0 <exit@plt>
}
    4a67:	e8 c4 d8 ff ff       	call   2330 <__stack_chk_fail@plt>
    4a6c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a70 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4a70:	f3 0f 1e fa          	endbr64
    4a74:	55                   	push   %rbp
    4a75:	48 89 e5             	mov    %rsp,%rbp
    4a78:	41 54                	push   %r12
    4a7a:	53                   	push   %rbx
    4a7b:	ff 15 67 45 00 00    	call   *0x4567(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    4a81:	8b 41 44             	mov    0x44(%rcx),%eax
    4a84:	83 c0 01             	add    $0x1,%eax
    4a87:	48 89 cb             	mov    %rcx,%rbx
	if (ring->flags & IORING_SETUP_SQE128)
    4a8a:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    4a90:	4c 8b 03             	mov    (%rbx),%r8
    4a93:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4a96:	f6 c1 02             	test   $0x2,%cl
    4a99:	74 00                	je     4a9b <add_accept_request+0x2b>
	if (next - head <= sq->ring_entries) {
    4a9b:	41 89 c0             	mov    %eax,%r8d
    4a9e:	45 29 c8             	sub    %r9d,%r8d
    4aa1:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4aa5:	0f 82 08 db ff ff    	jb     25b3 <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4aab:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4aae:	44 8b 63 44          	mov    0x44(%rbx),%r12d
    4ab2:	44 23 63 58          	and    0x58(%rbx),%r12d
		sq->sqe_tail = next;
    4ab6:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4ab9:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4abc:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ac0:	41 d3 e4             	shl    %cl,%r12d
    4ac3:	49 c1 e4 06          	shl    $0x6,%r12
    4ac7:	4c 03 63 38          	add    0x38(%rbx),%r12
	sqe->fd = fd;
    4acb:	41 89 7c 24 04       	mov    %edi,0x4(%r12)
  struct Request *req = malloc(sizeof(*req));
    4ad0:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4ad5:	41 c7 04 24 0d 00 00 00 	movl   $0xd,(%r12)
	sqe->off = offset;
    4add:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
	sqe->addr = (unsigned long) addr;
    4ae2:	49 89 74 24 10       	mov    %rsi,0x10(%r12)
	sqe->buf_index = 0;
    4ae7:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->len = len;
    4af0:	49 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%r12)
	sqe->addr3 = 0;
    4af9:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    4aff:	e8 1c d9 ff ff       	call   2420 <malloc@plt>
  io_uring_submit(ring);
    4b04:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4b07:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4b0d:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
    4b12:	5b                   	pop    %rbx
    4b13:	41 5c                	pop    %r12
    4b15:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4b16:	e9 25 d8 ff ff       	jmp    2340 <io_uring_submit@plt>
    4b1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004b20 <io_thread>:
void* io_thread(void *arg) {
    4b20:	f3 0f 1e fa          	endbr64
    4b24:	55                   	push   %rbp
    4b25:	48 89 e5             	mov    %rsp,%rbp
    4b28:	41 57                	push   %r15
    4b2a:	41 56                	push   %r14
    4b2c:	41 55                	push   %r13
    4b2e:	41 54                	push   %r12
    4b30:	53                   	push   %rbx
    4b31:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4b38:	ff 15 aa 44 00 00    	call   *0x44aa(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4b3e:	31 d2                	xor    %edx,%edx
  struct io_uring ring = *data->ring;
    4b40:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b49:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    4b4d:	48 8b 47 40          	mov    0x40(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4b51:	48 8d 9d e0 fa ff ff 	lea    -0x520(%rbp),%rbx
void* io_thread(void *arg) {
    4b58:	49 89 fc             	mov    %rdi,%r12
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4b5b:	bf 00 01 00 00       	mov    $0x100,%edi
    4b60:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4b63:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4b67:	0f 29 8d e0 fa ff ff 	movaps %xmm1,-0x520(%rbp)
    4b6e:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4b73:	0f 29 95 f0 fa ff ff 	movaps %xmm2,-0x510(%rbp)
    4b7a:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4b7f:	0f 29 9d 00 fb ff ff 	movaps %xmm3,-0x500(%rbp)
    4b86:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4b8b:	0f 29 a5 10 fb ff ff 	movaps %xmm4,-0x4f0(%rbp)
    4b92:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4b97:	0f 29 ad 20 fb ff ff 	movaps %xmm5,-0x4e0(%rbp)
    4b9e:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4ba3:	0f 29 b5 30 fb ff ff 	movaps %xmm6,-0x4d0(%rbp)
    4baa:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4baf:	0f 29 bd 40 fb ff ff 	movaps %xmm7,-0x4c0(%rbp)
    4bb6:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4bbb:	0f 29 8d 50 fb ff ff 	movaps %xmm1,-0x4b0(%rbp)
    4bc2:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4bca:	0f 29 95 60 fb ff ff 	movaps %xmm2,-0x4a0(%rbp)
    4bd1:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4bd9:	0f 29 9d 70 fb ff ff 	movaps %xmm3,-0x490(%rbp)
    4be0:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4be8:	0f 29 a5 80 fb ff ff 	movaps %xmm4,-0x480(%rbp)
    4bef:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4bf7:	0f 29 ad 90 fb ff ff 	movaps %xmm5,-0x470(%rbp)
    4bfe:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4c06:	0f 29 b5 a0 fb ff ff 	movaps %xmm6,-0x460(%rbp)
    4c0d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4c14:	48 89 85 b0 fb ff ff 	mov    %rax,-0x450(%rbp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4c1b:	e8 e0 d7 ff ff       	call   2400 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4c20:	49 8b 7c 24 40       	mov    0x40(%r12),%rdi
    4c25:	31 f6                	xor    %esi,%esi
    4c27:	e8 d4 d8 ff ff       	call   2500 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4c2c:	31 d2                	xor    %edx,%edx
    4c2e:	be 01 00 00 00       	mov    $0x1,%esi
    4c33:	bf 02 00 00 00       	mov    $0x2,%edi
    4c38:	e8 13 d9 ff ff       	call   2550 <socket@plt>
    4c3d:	89 85 ac fa ff ff    	mov    %eax,-0x554(%rbp)
  if (sock == -1)
    4c43:	83 f8 ff             	cmp    $0xffffffff,%eax
    4c46:	0f 84 a9 d9 ff ff    	je     25f5 <io_thread.cold+0x38>
    4c4c:	89 c7                	mov    %eax,%edi
  if (setsockopt(sock,
    4c4e:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4c54:	ba 02 00 00 00       	mov    $0x2,%edx
    4c59:	be 01 00 00 00       	mov    $0x1,%esi
    4c5e:	48 8d 8d b0 fa ff ff 	lea    -0x550(%rbp),%rcx
  int enable = 1;
    4c65:	c7 85 b0 fa ff ff 01 00 00 00 	movl   $0x1,-0x550(%rbp)
  if (setsockopt(sock,
    4c6f:	e8 8c d6 ff ff       	call   2300 <setsockopt@plt>
    4c74:	85 c0                	test   %eax,%eax
    4c76:	0f 88 4d d9 ff ff    	js     25c9 <io_thread.cold+0xc>
  if (bind(sock,
    4c7c:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4c82:	ba 10 00 00 00       	mov    $0x10,%edx
  return __builtin___memset_chk (__dest, __ch, __len,
    4c87:	48 8d b5 c0 fa ff ff 	lea    -0x540(%rbp),%rsi
    4c8e:	48 c7 85 c4 fa ff ff 00 00 00 00 	movq   $0x0,-0x53c(%rbp)
    4c99:	c7 85 cc fa ff ff 00 00 00 00 	movl   $0x0,-0x534(%rbp)
  srv_addr.sin_family = AF_INET;
    4ca3:	c7 85 c0 fa ff ff 02 00 18 db 	movl   $0xdb180002,-0x540(%rbp)
  if (bind(sock,
    4cad:	e8 be d7 ff ff       	call   2470 <bind@plt>
    4cb2:	85 c0                	test   %eax,%eax
    4cb4:	0f 88 47 d9 ff ff    	js     2601 <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4cba:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4cc0:	be 0a 00 00 00       	mov    $0xa,%esi
    4cc5:	e8 66 d7 ff ff       	call   2430 <listen@plt>
    4cca:	85 c0                	test   %eax,%eax
    4ccc:	0f 88 03 d9 ff ff    	js     25d5 <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4cd2:	ba db 18 00 00       	mov    $0x18db,%edx
    4cd7:	48 8d 35 9e 14 00 00 	lea    0x149e(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4cde:	bf 01 00 00 00       	mov    $0x1,%edi
    4ce3:	31 c0                	xor    %eax,%eax
    4ce5:	e8 76 d7 ff ff       	call   2460 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4cea:	48 8d 85 d0 fa ff ff 	lea    -0x530(%rbp),%rax
    4cf1:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4cf7:	48 89 d9             	mov    %rbx,%rcx
    4cfa:	48 8d 95 b4 fa ff ff 	lea    -0x54c(%rbp),%rdx
    4d01:	48 89 c6             	mov    %rax,%rsi
  socklen_t client_addr_len = sizeof(client_addr);
    4d04:	c7 85 b4 fa ff ff 10 00 00 00 	movl   $0x10,-0x54c(%rbp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4d0e:	48 89 95 88 fa ff ff 	mov    %rdx,-0x578(%rbp)
    4d15:	48 89 85 90 fa ff ff 	mov    %rax,-0x570(%rbp)
    4d1c:	e8 4f fd ff ff       	call   4a70 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4d21:	bf 01 00 00 00       	mov    $0x1,%edi
    4d26:	be 10 00 00 00       	mov    $0x10,%esi
    4d2b:	e8 70 d6 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    4d30:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4d35:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    4d38:	e8 e3 d6 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    4d3d:	48 85 c0             	test   %rax,%rax
    4d40:	0f 84 cf 04 00 00    	je     5215 <io_thread+0x6f5>
  iov->iov_base = zh_malloc(10);
    4d46:	49 89 06             	mov    %rax,(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    4d49:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4d4f:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
  iov->iov_len = 10;
    4d55:	49 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    4d5d:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4d60:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    4d67:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4d69:	f6 c1 02             	test   $0x2,%cl
    4d6c:	0f 85 2e 04 00 00    	jne    51a0 <io_thread+0x680>
	if (next - head <= sq->ring_entries) {
    4d72:	89 d0                	mov    %edx,%eax
    4d74:	29 f0                	sub    %esi,%eax
    4d76:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    4d7c:	0f 82 69 d8 ff ff    	jb     25eb <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4d82:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d85:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    4d8b:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4d8f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d92:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4d98:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4d9b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4da1:	49 8d 74 24 48       	lea    0x48(%r12),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4da6:	41 8b 54 24 48       	mov    0x48(%r12),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4dab:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4dad:	48 89 b5 98 fa ff ff 	mov    %rsi,-0x568(%rbp)
    4db4:	48 c1 e0 06          	shl    $0x6,%rax
    4db8:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    4dbf:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4dc5:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4dc8:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4dd0:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    4dd4:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4ddc:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4de4:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4de8:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4dec:	e8 4f d5 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4df1:	41 83 7c 24 2c 01    	cmpl   $0x1,0x2c(%r12)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4df7:	4c 8d 8d b8 fa ff ff 	lea    -0x548(%rbp),%r9
    4dfe:	4c 8d 95 c0 fb ff ff 	lea    -0x440(%rbp),%r10
    4e05:	0f 85 ed 01 00 00    	jne    4ff8 <io_thread+0x4d8>
    4e0b:	4c 89 8d a0 fa ff ff 	mov    %r9,-0x560(%rbp)
    4e12:	4c 89 95 80 fa ff ff 	mov    %r10,-0x580(%rbp)
    4e19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4e20:	48 8d 3d 6b 13 00 00 	lea    0x136b(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4e27:	e8 c4 d4 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4e2c:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4e32:	8b bd 90 fb ff ff    	mov    -0x470(%rbp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4e38:	c1 e9 0b             	shr    $0xb,%ecx
    4e3b:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4e3e:	48 8b 85 50 fb ff ff 	mov    -0x4b0(%rbp),%rax
    4e45:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4e47:	48 8b b5 48 fb ff ff 	mov    -0x4b8(%rbp),%rsi
    4e4e:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4e50:	39 d0                	cmp    %edx,%eax
    4e52:	74 34                	je     4e88 <io_thread+0x368>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4e54:	89 f8                	mov    %edi,%eax
    4e56:	21 d0                	and    %edx,%eax
    4e58:	d3 e0                	shl    %cl,%eax
    4e5a:	48 c1 e0 04          	shl    $0x4,%rax
    4e5e:	48 03 85 78 fb ff ff 	add    -0x488(%rbp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4e65:	f6 85 a9 fb ff ff 01 	testb  $0x1,-0x457(%rbp)
    4e6c:	0f 85 be 01 00 00    	jne    5030 <io_thread+0x510>
    4e72:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4e76:	0f 85 2c 03 00 00    	jne    51a8 <io_thread+0x688>
			if (cqe->res < 0)
    4e7c:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4e7f:	83 c2 01             	add    $0x1,%edx
    4e82:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4e84:	85 c0                	test   %eax,%eax
    4e86:	79 b6                	jns    4e3e <io_thread+0x31e>
	*cqe_ptr = cqe;
    4e88:	48 c7 85 b8 fa ff ff 00 00 00 00 	movq   $0x0,-0x548(%rbp)
	return err;
    4e93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4e98:	48 8b b5 a0 fa ff ff 	mov    -0x560(%rbp),%rsi
    4e9f:	45 31 c0             	xor    %r8d,%r8d
    4ea2:	31 d2                	xor    %edx,%edx
    4ea4:	48 89 df             	mov    %rbx,%rdi
    4ea7:	b9 01 00 00 00       	mov    $0x1,%ecx
    4eac:	e8 9f d5 ff ff       	call   2450 <__io_uring_get_cqe@plt>
    4eb1:	41 89 c5             	mov    %eax,%r13d
      if (cqe->user_data == 1) {
    4eb4:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    4ebb:	48 83 38 01          	cmpq   $0x1,(%rax)
    4ebf:	0f 84 f3 02 00 00    	je     51b8 <io_thread+0x698>
    4ec5:	48 8d 3d ec 12 00 00 	lea    0x12ec(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4ecc:	e8 1f d4 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4ed1:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    4ed8:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    4edb:	45 85 ed             	test   %r13d,%r13d
    4ede:	0f 88 d9 d6 ff ff    	js     25bd <io_thread.cold>
      if (cqe->res < 0) {
    4ee4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    4ee7:	45 8b 07             	mov    (%r15),%r8d
      if (cqe->res < 0) {
    4eea:	85 c0                	test   %eax,%eax
    4eec:	0f 88 e5 02 00 00    	js     51d7 <io_thread+0x6b7>
      switch (req->event_type) {
    4ef2:	41 83 f8 01          	cmp    $0x1,%r8d
    4ef6:	0f 84 84 01 00 00    	je     5080 <io_thread+0x560>
    4efc:	41 83 f8 02          	cmp    $0x2,%r8d
    4f00:	0f 84 aa 01 00 00    	je     50b0 <io_thread+0x590>
    4f06:	45 85 c0             	test   %r8d,%r8d
    4f09:	0f 85 59 01 00 00    	jne    5068 <io_thread+0x548>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4f0f:	48 8b 95 88 fa ff ff 	mov    -0x578(%rbp),%rdx
    4f16:	48 8b b5 90 fa ff ff 	mov    -0x570(%rbp),%rsi
    4f1d:	48 89 d9             	mov    %rbx,%rcx
    4f20:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4f26:	e8 45 fb ff ff       	call   4a70 <add_accept_request>
              add_read_request(cqe->res, &ring);
    4f2b:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    4f32:	48 89 de             	mov    %rbx,%rsi
    4f35:	8b 78 08             	mov    0x8(%rax),%edi
    4f38:	e8 83 f4 ff ff       	call   43c0 <add_read_request>
              free(req);
    4f3d:	4c 89 ff             	mov    %r15,%rdi
    4f40:	e8 8b d3 ff ff       	call   22d0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4f45:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
	if (cqe)
    4f4c:	48 85 c0             	test   %rax,%rax
    4f4f:	0f 85 13 01 00 00    	jne    5068 <io_thread+0x548>
	unsigned int head, next = sq->sqe_tail + 1;
    4f55:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4f5b:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4f61:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4f64:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    4f6b:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4f6d:	f6 c1 02             	test   $0x2,%cl
    4f70:	74 00                	je     4f72 <io_thread+0x452>
	if (next - head <= sq->ring_entries) {
    4f72:	89 d0                	mov    %edx,%eax
    4f74:	29 f0                	sub    %esi,%eax
    4f76:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    4f7c:	0f 82 5f d6 ff ff    	jb     25e1 <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    4f82:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4f85:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    4f8b:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    4f8f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4f92:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4f98:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4f9b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4fa1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4fa3:	41 8b 54 24 48       	mov    0x48(%r12),%edx
	sqe->user_data = (unsigned long) data;
    4fa8:	48 8b b5 98 fa ff ff 	mov    -0x568(%rbp),%rsi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4faf:	48 c1 e0 06          	shl    $0x6,%rax
    4fb3:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    4fba:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4fc0:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4fc3:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4fcb:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    4fcf:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4fd7:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4fdf:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4fe3:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    4fe7:	e8 54 d3 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4fec:	41 83 7c 24 2c 01    	cmpl   $0x1,0x2c(%r12)
    4ff2:	0f 84 28 fe ff ff    	je     4e20 <io_thread+0x300>
    4ff8:	48 8d 3d f2 11 00 00 	lea    0x11f2(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    4fff:	e8 ec d2 ff ff       	call   22f0 <puts@plt>
}
    5004:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    5008:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5011:	0f 85 25 02 00 00    	jne    523c <io_thread+0x71c>
    5017:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    501e:	31 c0                	xor    %eax,%eax
    5020:	5b                   	pop    %rbx
    5021:	41 5c                	pop    %r12
    5023:	41 5d                	pop    %r13
    5025:	41 5e                	pop    %r14
    5027:	41 5f                	pop    %r15
    5029:	5d                   	pop    %rbp
    502a:	c3                   	ret
    502b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    5030:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5037:	48 85 c0             	test   %rax,%rax
    503a:	0f 84 58 fe ff ff    	je     4e98 <io_thread+0x378>
      if (cqe->user_data == 1) {
    5040:	48 83 38 01          	cmpq   $0x1,(%rax)
    5044:	0f 84 6e 01 00 00    	je     51b8 <io_thread+0x698>
    504a:	48 8d 3d 67 11 00 00 	lea    0x1167(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    5051:	e8 9a d2 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5056:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    505d:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    5060:	e9 7f fe ff ff       	jmp    4ee4 <io_thread+0x3c4>
    5065:	0f 1f 00             	nopl   (%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5068:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
    506f:	8b 02                	mov    (%rdx),%eax
    5071:	83 c0 01             	add    $0x1,%eax
    5074:	89 02                	mov    %eax,(%rdx)
}
    5076:	e9 da fe ff ff       	jmp    4f55 <io_thread+0x435>
    507b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              if (!cqe->res) {
    5080:	85 c0                	test   %eax,%eax
    5082:	75 7c                	jne    5100 <io_thread+0x5e0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5084:	48 8b 0d 95 3f 00 00 	mov    0x3f95(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    508b:	ba 0f 00 00 00       	mov    $0xf,%edx
    5090:	be 01 00 00 00       	mov    $0x1,%esi
    5095:	48 8d 3d 45 11 00 00 	lea    0x1145(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    509c:	e8 3f d4 ff ff       	call   24e0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    50a1:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    50a8:	e9 9f fe ff ff       	jmp    4f4c <io_thread+0x42c>
    50ad:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    50b0:	41 8b 47 04          	mov    0x4(%r15),%eax
    50b4:	45 31 ed             	xor    %r13d,%r13d
    50b7:	85 c0                	test   %eax,%eax
    50b9:	7e 20                	jle    50db <io_thread+0x5bb>
    50bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  free(req->iov[i].iov_base);
    50c0:	4c 89 e8             	mov    %r13,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    50c3:	49 83 c5 01          	add    $0x1,%r13
                  free(req->iov[i].iov_base);
    50c7:	48 c1 e0 04          	shl    $0x4,%rax
    50cb:	49 8b 7c 07 10       	mov    0x10(%r15,%rax,1),%rdi
    50d0:	e8 fb d1 ff ff       	call   22d0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    50d5:	45 39 6f 04          	cmp    %r13d,0x4(%r15)
    50d9:	7f e5                	jg     50c0 <io_thread+0x5a0>
              close(req->client_socket);
    50db:	41 8b 7f 08          	mov    0x8(%r15),%edi
    50df:	e8 8c d2 ff ff       	call   2370 <close@plt>
              free(req);
    50e4:	4c 89 ff             	mov    %r15,%rdi
    50e7:	e8 e4 d1 ff ff       	call   22d0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    50ec:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    50f3:	e9 54 fe ff ff       	jmp    4f4c <io_thread+0x42c>
    50f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int i = 0; i < dest_sz; i++) {
    5100:	49 8b 57 10          	mov    0x10(%r15),%rdx
    5104:	48 8b 85 80 fa ff ff 	mov    -0x580(%rbp),%rax
    510b:	48 8d 75 c0          	lea    -0x40(%rbp),%rsi
    510f:	eb 14                	jmp    5125 <io_thread+0x605>
    5111:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5118:	48 83 c0 01          	add    $0x1,%rax
    511c:	48 83 c2 01          	add    $0x1,%rdx
    5120:	48 39 c6             	cmp    %rax,%rsi
    5123:	74 4b                	je     5170 <io_thread+0x650>
        dest[i] = src[i];
    5125:	0f b6 0a             	movzbl (%rdx),%ecx
    5128:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    512a:	80 f9 0d             	cmp    $0xd,%cl
    512d:	75 e9                	jne    5118 <io_thread+0x5f8>
    512f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5133:	75 e3                	jne    5118 <io_thread+0x5f8>
            dest[i] = '\0';
    5135:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5138:	48 8b bd 80 fa ff ff 	mov    -0x580(%rbp),%rdi
    513f:	48 89 da             	mov    %rbx,%rdx
    5142:	41 8b 77 08          	mov    0x8(%r15),%esi
    5146:	e8 35 f7 ff ff       	call   4880 <handle_http_method>
              free(req->iov[0].iov_base);
    514b:	49 8b 7f 10          	mov    0x10(%r15),%rdi
    514f:	e8 7c d1 ff ff       	call   22d0 <free@plt>
              free(req);
    5154:	4c 89 ff             	mov    %r15,%rdi
    5157:	e8 74 d1 ff ff       	call   22d0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    515c:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    5163:	e9 e4 fd ff ff       	jmp    4f4c <io_thread+0x42c>
    5168:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5170:	48 8b 0d a9 3e 00 00 	mov    0x3ea9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5177:	ba 12 00 00 00       	mov    $0x12,%edx
    517c:	be 01 00 00 00       	mov    $0x1,%esi
    5181:	48 8d 3d af 0f 00 00 	lea    0xfaf(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    5188:	e8 53 d3 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    518d:	bf 01 00 00 00       	mov    $0x1,%edi
    5192:	e8 29 d3 ff ff       	call   24c0 <exit@plt>
    5197:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    51a0:	e9 cd fb ff ff       	jmp    4d72 <io_thread+0x252>
    51a5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    51a8:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	return err;
    51af:	e9 8c fe ff ff       	jmp    5040 <io_thread+0x520>
    51b4:	0f 1f 40 00          	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    51b8:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    51bf:	48 8d 3d de 0f 00 00 	lea    0xfde(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    51c6:	8b 02                	mov    (%rdx),%eax
    51c8:	83 c0 01             	add    $0x1,%eax
    51cb:	89 02                	mov    %eax,(%rdx)
    51cd:	e8 1e d1 ff ff       	call   22f0 <puts@plt>
    51d2:	e9 21 fe ff ff       	jmp    4ff8 <io_thread+0x4d8>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    51d7:	f7 d8                	neg    %eax
    51d9:	44 89 85 ac fa ff ff 	mov    %r8d,-0x554(%rbp)
    51e0:	89 c7                	mov    %eax,%edi
    51e2:	e8 39 d3 ff ff       	call   2520 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    51e7:	48 8b 3d 32 3e 00 00 	mov    0x3e32(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    51ee:	be 01 00 00 00       	mov    $0x1,%esi
    51f3:	44 8b 85 ac fa ff ff 	mov    -0x554(%rbp),%r8d
    51fa:	48 89 c1             	mov    %rax,%rcx
    51fd:	48 8d 15 4c 12 00 00 	lea    0x124c(%rip),%rdx        # 6450 <_IO_stdin_used+0x450>
    5204:	31 c0                	xor    %eax,%eax
    5206:	e8 e5 d2 ff ff       	call   24f0 <__fprintf_chk@plt>
          exit(1);
    520b:	bf 01 00 00 00       	mov    $0x1,%edi
    5210:	e8 ab d2 ff ff       	call   24c0 <exit@plt>
    5215:	48 8b 0d 04 3e 00 00 	mov    0x3e04(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    521c:	ba 28 00 00 00       	mov    $0x28,%edx
    5221:	be 01 00 00 00       	mov    $0x1,%esi
    5226:	48 8d 3d f3 11 00 00 	lea    0x11f3(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    522d:	e8 ae d2 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    5232:	bf 01 00 00 00       	mov    $0x1,%edi
    5237:	e8 84 d2 ff ff       	call   24c0 <exit@plt>
}
    523c:	e8 ef d0 ff ff       	call   2330 <__stack_chk_fail@plt>
    5241:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    524c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005250 <receive>:
int receive(struct BarrierTask *data) {
    5250:	f3 0f 1e fa          	endbr64
    5254:	55                   	push   %rbp
    5255:	48 89 e5             	mov    %rsp,%rbp
    5258:	41 55                	push   %r13
    525a:	41 54                	push   %r12
    525c:	53                   	push   %rbx
    525d:	48 83 ec 08          	sub    $0x8,%rsp
    5261:	ff 15 81 3d 00 00    	call   *0x3d81(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  for (int n = 0 ; n < data->thread_count; n++) {
    5267:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
int receive(struct BarrierTask *data) {
    526d:	48 89 fa             	mov    %rdi,%rdx
  for (int n = 0 ; n < data->thread_count; n++) {
    5270:	85 c0                	test   %eax,%eax
    5272:	0f 8e de 00 00 00    	jle    5356 <receive+0x106>
    5278:	48 8b b7 b0 01 00 00 	mov    0x1b0(%rdi),%rsi
    527f:	4c 63 e8             	movslq %eax,%r13
    5282:	49 c1 e5 05          	shl    $0x5,%r13
    5286:	49 01 f5             	add    %rsi,%r13
    5289:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    struct Data *me = data->mailboxes[n].lower;
    5290:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5293:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    5298:	48 85 ff             	test   %rdi,%rdi
    529b:	0f 8e 9f 00 00 00    	jle    5340 <receive+0xf0>
      data->sends++;
    52a1:	48 8b 8a b8 01 00 00 	mov    0x1b8(%rdx),%rcx
    52a8:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    52ac:	4c 63 1a             	movslq (%rdx),%r11
    52af:	49 89 c9             	mov    %rcx,%r9
    52b2:	48 8d 41 01          	lea    0x1(%rcx),%rax
    52b6:	49 f7 d9             	neg    %r9
    52b9:	48 01 c7             	add    %rax,%rdi
    52bc:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    52c0:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    52c7:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    52cb:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    52ce:	49 29 c8             	sub    %rcx,%r8
    52d1:	eb 0e                	jmp    52e1 <receive+0x91>
    52d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    52d8:	48 83 c0 01          	add    $0x1,%rax
    52dc:	48 39 c7             	cmp    %rax,%rdi
    52df:	74 5f                	je     5340 <receive+0xf0>
      data->n++;
    52e1:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    52e5:	48 89 82 b8 01 00 00 	mov    %rax,0x1b8(%rdx)
      data->n++;
    52ec:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    52f3:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    52f7:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    52fb:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5300:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5304:	75 d2                	jne    52d8 <receive+0x88>
    5306:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    530d:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5311:	75 c5                	jne    52d8 <receive+0x88>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5313:	bf 01 00 00 00       	mov    $0x1,%edi
    5318:	b9 01 00 00 00       	mov    $0x1,%ecx
    531d:	ba 01 00 00 00       	mov    $0x1,%edx
    5322:	31 c0                	xor    %eax,%eax
    5324:	48 8d 35 4d 11 00 00 	lea    0x114d(%rip),%rsi        # 6478 <_IO_stdin_used+0x478>
    532b:	e8 30 d1 ff ff       	call   2460 <__printf_chk@plt>
        exit(1);
    5330:	bf 01 00 00 00       	mov    $0x1,%edi
    5335:	e8 86 d1 ff ff       	call   24c0 <exit@plt>
    533a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5340:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
  for (int n = 0 ; n < data->thread_count; n++) {
    5349:	48 83 c6 20          	add    $0x20,%rsi
    534d:	49 39 f5             	cmp    %rsi,%r13
    5350:	0f 85 3a ff ff ff    	jne    5290 <receive+0x40>
}
    5356:	48 83 c4 08          	add    $0x8,%rsp
    535a:	31 c0                	xor    %eax,%eax
    535c:	5b                   	pop    %rbx
    535d:	41 5c                	pop    %r12
    535f:	41 5d                	pop    %r13
    5361:	5d                   	pop    %rbp
    5362:	c3                   	ret
    5363:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    536e:	66 90                	xchg   %ax,%ax

0000000000005370 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5370:	f3 0f 1e fa          	endbr64
    5374:	55                   	push   %rbp
    5375:	48 89 e5             	mov    %rsp,%rbp
    5378:	41 57                	push   %r15
    537a:	41 56                	push   %r14
    537c:	41 55                	push   %r13
    537e:	41 54                	push   %r12
    5380:	53                   	push   %rbx
    5381:	48 83 ec 38          	sub    $0x38,%rsp
    5385:	ff 15 5d 3c 00 00    	call   *0x3c5d(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  if (data->thread_index == data->task_index) {
    538b:	8b 07                	mov    (%rdi),%eax
int barriered_work(struct BarrierTask *data) {
    538d:	48 89 fb             	mov    %rdi,%rbx
  if (data->thread_index == data->task_index) {
    5390:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    5396:	0f 84 54 01 00 00    	je     54f0 <barriered_work+0x180>
    receive(data);
    539c:	e8 af fe ff ff       	call   5250 <receive>
    while (data->scheduled == 1) {
    53a1:	83 bb 88 01 00 00 01 	cmpl   $0x1,0x188(%rbx)
    53a8:	75 1a                	jne    53c4 <barriered_work+0x54>
    53aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->n++;
    53b0:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    53b8:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    53bb:	83 bb 88 01 00 00 01 	cmpl   $0x1,0x188(%rbx)
    53c2:	74 ec                	je     53b0 <barriered_work+0x40>
    if (data->sending == 1) {
    53c4:	83 bb c0 01 00 00 01 	cmpl   $0x1,0x1c0(%rbx)
    53cb:	74 14                	je     53e1 <barriered_work+0x71>
  asm volatile ("mfence" ::: "memory");
    53cd:	0f ae f0             	mfence
}
    53d0:	48 83 c4 38          	add    $0x38,%rsp
    53d4:	31 c0                	xor    %eax,%eax
    53d6:	5b                   	pop    %rbx
    53d7:	41 5c                	pop    %r12
    53d9:	41 5d                	pop    %r13
    53db:	41 5e                	pop    %r14
    53dd:	41 5f                	pop    %r15
    53df:	5d                   	pop    %rbp
    53e0:	c3                   	ret
        for (int n = 0 ; n < data->thread_count; n++) {
    53e1:	48 63 83 34 01 00 00 	movslq 0x134(%rbx),%rax
    53e8:	85 c0                	test   %eax,%eax
    53ea:	7e e1                	jle    53cd <barriered_work+0x5d>
    53ec:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
          if (n == data->thread_index) { continue; }
    53f0:	8b b3 30 01 00 00    	mov    0x130(%rbx),%esi
    53f6:	48 8d 83 c8 01 00 00 	lea    0x1c8(%rbx),%rax
    53fd:	45 31 ff             	xor    %r15d,%r15d
    5400:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    5404:	48 8d 83 d0 01 00 00 	lea    0x1d0(%rbx),%rax
    540b:	89 75 cc             	mov    %esi,-0x34(%rbp)
    540e:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
    5412:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5418:	44 39 7d cc          	cmp    %r15d,-0x34(%rbp)
    541c:	0f 84 b1 00 00 00    	je     54d3 <barriered_work+0x163>
          struct Data *them = data->mailboxes[n].higher;
    5422:	4c 89 ff             	mov    %r15,%rdi
    5425:	48 c1 e7 05          	shl    $0x5,%rdi
    5429:	48 03 bb b0 01 00 00 	add    0x1b0(%rbx),%rdi
    5430:	4c 8b 47 08          	mov    0x8(%rdi),%r8
          for (; them->messages_count < min;) {
    5434:	4d 8b 50 08          	mov    0x8(%r8),%r10
    5438:	49 63 70 10          	movslq 0x10(%r8),%rsi
    543c:	49 39 f2             	cmp    %rsi,%r10
    543f:	0f 8d 8e 00 00 00    	jge    54d3 <barriered_work+0x163>
    5445:	49 89 f1             	mov    %rsi,%r9
    5448:	4c 8b b3 08 01 00 00 	mov    0x108(%rbx),%r14
    544f:	4c 8b 5f 10          	mov    0x10(%rdi),%r11
    5453:	4d 29 d1             	sub    %r10,%r9
            them->messages[them->messages_count++] = data->message; 
    5456:	49 8b 10             	mov    (%r8),%rdx
    5459:	49 8d 41 ff          	lea    -0x1(%r9),%rax
    545d:	48 83 f8 02          	cmp    $0x2,%rax
    5461:	0f 86 81 02 00 00    	jbe    56e8 <barriered_work+0x378>
    5467:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    546f:	48 8d 0c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rcx
    5477:	4c 8d 24 02          	lea    (%rdx,%rax,1),%r12
    547b:	4c 8d 2c 0a          	lea    (%rdx,%rcx,1),%r13
    547f:	4c 39 6d b8          	cmp    %r13,-0x48(%rbp)
    5483:	0f 83 e7 01 00 00    	jae    5670 <barriered_work+0x300>
    5489:	4c 8b 6d b0          	mov    -0x50(%rbp),%r13
    548d:	4d 39 ec             	cmp    %r13,%r12
    5490:	0f 83 da 01 00 00    	jae    5670 <barriered_work+0x300>
    5496:	4c 8d 14 02          	lea    (%rdx,%rax,1),%r10
    549a:	48 01 d1             	add    %rdx,%rcx
    549d:	0f 1f 00             	nopl   (%rax)
    54a0:	48 8b 83 c8 01 00 00 	mov    0x1c8(%rbx),%rax
          for (; them->messages_count < min;) {
    54a7:	49 83 c2 08          	add    $0x8,%r10
            them->messages[them->messages_count++] = data->message; 
    54ab:	49 89 42 f8          	mov    %rax,-0x8(%r10)
          for (; them->messages_count < min;) {
    54af:	4c 39 d1             	cmp    %r10,%rcx
    54b2:	75 ec                	jne    54a0 <barriered_work+0x130>
    54b4:	0f 1f 40 00          	nopl   0x0(%rax)
    54b8:	4b 8d 0c 0e          	lea    (%r14,%r9,1),%rcx
    54bc:	4d 01 cb             	add    %r9,%r11
    54bf:	48 89 8b 08 01 00 00 	mov    %rcx,0x108(%rbx)
    54c6:	4c 89 5f 10          	mov    %r11,0x10(%rdi)
    54ca:	49 89 70 08          	mov    %rsi,0x8(%r8)
    54ce:	48 89 44 f2 f8       	mov    %rax,-0x8(%rdx,%rsi,8)
        for (int n = 0 ; n < data->thread_count; n++) {
    54d3:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    54d7:	49 83 c7 01          	add    $0x1,%r15
    54db:	49 39 c7             	cmp    %rax,%r15
    54de:	0f 85 34 ff ff ff    	jne    5418 <barriered_work+0xa8>
    54e4:	e9 e4 fe ff ff       	jmp    53cd <barriered_work+0x5d>
    54e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      receive(data);
    54f0:	e8 5b fd ff ff       	call   5250 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    54f5:	8b 8b 34 01 00 00    	mov    0x134(%rbx),%ecx
        int t = data->task_index;
    54fb:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    54fd:	85 c9                	test   %ecx,%ecx
    54ff:	0f 8e 86 00 00 00    	jle    558b <barriered_work+0x21b>
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5505:	4c 63 e0             	movslq %eax,%r12
              int next_task = abs((t + 1) % (data->thread_count));
    5508:	83 c0 01             	add    $0x1,%eax
    550b:	4c 63 d9             	movslq %ecx,%r11
    550e:	99                   	cltd
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    550f:	49 c1 e4 09          	shl    $0x9,%r12
              int next_task = abs((t + 1) % (data->thread_count));
    5513:	f7 f9                	idiv   %ecx
    5515:	89 d0                	mov    %edx,%eax
    5517:	f7 d8                	neg    %eax
    5519:	0f 49 d0             	cmovns %eax,%edx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    551c:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    5523:	49 c1 e3 05          	shl    $0x5,%r11
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5527:	31 ff                	xor    %edi,%edi
    5529:	4c 8b 68 10          	mov    0x10(%rax),%r13
              int next_task = abs((t + 1) % (data->thread_count));
    552d:	4c 63 ca             	movslq %edx,%r9
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5530:	49 c1 e1 09          	shl    $0x9,%r9
    5534:	49 83 c5 20          	add    $0x20,%r13
    5538:	4d 89 ea             	mov    %r13,%r10
    553b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5540:	49 8b 02             	mov    (%r10),%rax
    5543:	4c 89 ea             	mov    %r13,%rdx
    5546:	4a 8b 84 20 b0 01 00 00 	mov    0x1b0(%rax,%r12,1),%rax
    554e:	4d 8d 04 03          	lea    (%r11,%rax,1),%r8
    5552:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5558:	48 8b 0a             	mov    (%rdx),%rcx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    555b:	48 8b 70 08          	mov    0x8(%rax),%rsi
          for (int b = 0; b < data->thread_count ; b++) {
    555f:	48 83 c0 20          	add    $0x20,%rax
    5563:	48 81 c2 98 00 00 00 	add    $0x98,%rdx
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    556a:	4a 8b 8c 09 b0 01 00 00 	mov    0x1b0(%rcx,%r9,1),%rcx
    5572:	48 89 34 39          	mov    %rsi,(%rcx,%rdi,1)
          for (int b = 0; b < data->thread_count ; b++) {
    5576:	49 39 c0             	cmp    %rax,%r8
    5579:	75 dd                	jne    5558 <barriered_work+0x1e8>
        for (int y = 0; y < data->thread_count ; y++) {
    557b:	48 83 c7 20          	add    $0x20,%rdi
    557f:	49 81 c2 98 00 00 00 	add    $0x98,%r10
    5586:	4c 39 df             	cmp    %r11,%rdi
    5589:	75 b5                	jne    5540 <barriered_work+0x1d0>
      asm volatile ("mfence" ::: "memory");
    558b:	0f ae f0             	mfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    558e:	48 8b b3 a0 01 00 00 	mov    0x1a0(%rbx),%rsi
    5595:	31 ff                	xor    %edi,%edi
    5597:	48 c1 e6 05          	shl    $0x5,%rsi
    559b:	48 03 b3 90 01 00 00 	add    0x190(%rbx),%rsi
    55a2:	e8 69 cd ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    55a7:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    while (data->scheduled == 1) {
    55ae:	83 bb 88 01 00 00 01 	cmpl   $0x1,0x188(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    55b5:	48 8b 42 30          	mov    0x30(%rdx),%rax
    55b9:	8b 70 10             	mov    0x10(%rax),%esi
    55bc:	44 8d 66 01          	lea    0x1(%rsi),%r12d
    55c0:	44 89 60 10          	mov    %r12d,0x10(%rax)
    while (data->scheduled == 1) {
    55c4:	74 11                	je     55d7 <barriered_work+0x267>
    55c6:	eb 68                	jmp    5630 <barriered_work+0x2c0>
    55c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    if (modcount != data->thread->protected_state->modcount) {
    55d0:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    55d7:	48 63 83 30 01 00 00 	movslq 0x130(%rbx),%rax
    55de:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    55e1:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    55e9:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    55ed:	48 c1 e7 09          	shl    $0x9,%rdi
    55f1:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    55f5:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    55f9:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    55fd:	48 03 78 20          	add    0x20(%rax),%rdi
    5601:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    5607:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    560a:	83 bb 88 01 00 00 01 	cmpl   $0x1,0x188(%rbx)
    5611:	74 bd                	je     55d0 <barriered_work+0x260>
    if (modcount != data->thread->protected_state->modcount) {
    5613:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    561a:	48 8b 40 30          	mov    0x30(%rax),%rax
    561e:	44 3b 60 10          	cmp    0x10(%rax),%r12d
    5622:	74 0c                	je     5630 <barriered_work+0x2c0>
    5624:	48 8d 3d d9 0b 00 00 	lea    0xbd9(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    562b:	e8 c0 cc ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5630:	48 8b b3 a0 01 00 00 	mov    0x1a0(%rbx),%rsi
    5637:	31 ff                	xor    %edi,%edi
    5639:	48 c1 e6 05          	shl    $0x5,%rsi
    563d:	48 03 b3 90 01 00 00 	add    0x190(%rbx),%rsi
    5644:	48 83 c6 10          	add    $0x10,%rsi
    5648:	e8 c3 cc ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    564d:	48 8b 83 a0 01 00 00 	mov    0x1a0(%rbx),%rax
    5654:	48 83 c0 01          	add    $0x1,%rax
    5658:	48 99                	cqto
    565a:	48 f7 bb 98 01 00 00 	idivq  0x198(%rbx)
    5661:	48 89 93 a0 01 00 00 	mov    %rdx,0x1a0(%rbx)
    5668:	e9 60 fd ff ff       	jmp    53cd <barriered_work+0x5d>
    566d:	0f 1f 00             	nopl   (%rax)
    5670:	48 8b 83 c8 01 00 00 	mov    0x1c8(%rbx),%rax
    5677:	4d 89 cd             	mov    %r9,%r13
    567a:	4c 89 e1             	mov    %r12,%rcx
    567d:	49 d1 ed             	shr    %r13
    5680:	49 c1 e5 04          	shl    $0x4,%r13
    5684:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5689:	4c 89 6d a8          	mov    %r13,-0x58(%rbp)
    568d:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5691:	4d 01 e5             	add    %r12,%r13
    5694:	f6 45 a8 10          	testb  $0x10,-0x58(%rbp)
    5698:	74 16                	je     56b0 <barriered_work+0x340>
            them->messages[them->messages_count++] = data->message; 
    569a:	48 83 c1 10          	add    $0x10,%rcx
    569e:	41 0f 11 04 24       	movups %xmm0,(%r12)
          for (; them->messages_count < min;) {
    56a3:	49 39 cd             	cmp    %rcx,%r13
    56a6:	74 18                	je     56c0 <barriered_work+0x350>
    56a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    56b0:	0f 11 01             	movups %xmm0,(%rcx)
    56b3:	48 83 c1 20          	add    $0x20,%rcx
    56b7:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
          for (; them->messages_count < min;) {
    56bb:	49 39 cd             	cmp    %rcx,%r13
    56be:	75 f0                	jne    56b0 <barriered_work+0x340>
    56c0:	4c 89 c9             	mov    %r9,%rcx
    56c3:	48 83 e1 fe          	and    $0xfffffffffffffffe,%rcx
    56c7:	4c 01 d1             	add    %r10,%rcx
    56ca:	41 f6 c1 01          	test   $0x1,%r9b
    56ce:	0f 84 e4 fd ff ff    	je     54b8 <barriered_work+0x148>
            them->messages[them->messages_count++] = data->message; 
    56d4:	48 8b 83 c8 01 00 00 	mov    0x1c8(%rbx),%rax
    56db:	48 89 04 ca          	mov    %rax,(%rdx,%rcx,8)
          for (; them->messages_count < min;) {
    56df:	e9 d4 fd ff ff       	jmp    54b8 <barriered_work+0x148>
    56e4:	0f 1f 40 00          	nopl   0x0(%rax)
    56e8:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    56f0:	48 8d 0c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rcx
    56f8:	e9 99 fd ff ff       	jmp    5496 <barriered_work+0x126>
    56fd:	0f 1f 00             	nopl   (%rax)

0000000000005700 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5700:	f3 0f 1e fa          	endbr64
    5704:	55                   	push   %rbp
    5705:	48 89 e5             	mov    %rsp,%rbp
    5708:	ff 15 da 38 00 00    	call   *0x38da(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    570e:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5715:	48 8b 40 38          	mov    0x38(%rax),%rax
    5719:	48 63 10             	movslq (%rax),%rdx
    571c:	85 d2                	test   %edx,%edx
    571e:	7e 2e                	jle    574e <barriered_work_ingest+0x4e>
    5720:	48 8b 40 08          	mov    0x8(%rax),%rax
    5724:	48 c1 e2 04          	shl    $0x4,%rdx
    5728:	48 01 c2             	add    %rax,%rdx
    572b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread->buffers->buffer[x].available == 1) {
    5730:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5734:	75 0f                	jne    5745 <barriered_work_ingest+0x45>
      data->ingest_count++;
    5736:	48 83 87 a8 01 00 00 01 	addq   $0x1,0x1a8(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    573e:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5745:	48 83 c0 10          	add    $0x10,%rax
    5749:	48 39 d0             	cmp    %rdx,%rax
    574c:	75 e2                	jne    5730 <barriered_work_ingest+0x30>
  asm volatile ("mfence" ::: "memory");
    574e:	0f ae f0             	mfence
  barriered_work(data);
    5751:	e8 1a fc ff ff       	call   5370 <barriered_work>
}
    5756:	31 c0                	xor    %eax,%eax
    5758:	5d                   	pop    %rbp
    5759:	c3                   	ret
    575a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005760 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5760:	f3 0f 1e fa          	endbr64
    5764:	55                   	push   %rbp
    5765:	48 89 e5             	mov    %rsp,%rbp
    5768:	ff 15 7a 38 00 00    	call   *0x387a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
}
    576e:	31 c0                	xor    %eax,%eax
    5770:	5d                   	pop    %rbp
    5771:	c3                   	ret
    5772:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    577d:	0f 1f 00             	nopl   (%rax)

0000000000005780 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5780:	f3 0f 1e fa          	endbr64
    5784:	55                   	push   %rbp
    5785:	48 89 e5             	mov    %rsp,%rbp
    5788:	ff 15 5a 38 00 00    	call   *0x385a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    578e:	31 c0                	xor    %eax,%eax
    5790:	5d                   	pop    %rbp
    5791:	c3                   	ret
    5792:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    579d:	0f 1f 00             	nopl   (%rax)

00000000000057a0 <after>:
int after(struct timespec left, struct timespec right) {
    57a0:	f3 0f 1e fa          	endbr64
    57a4:	55                   	push   %rbp
    57a5:	48 89 e5             	mov    %rsp,%rbp
    57a8:	ff 15 3a 38 00 00    	call   *0x383a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  return left.tv_sec > right.tv_sec &&
    57ae:	31 c0                	xor    %eax,%eax
    57b0:	48 39 d7             	cmp    %rdx,%rdi
    57b3:	7e 08                	jle    57bd <after+0x1d>
    57b5:	31 c0                	xor    %eax,%eax
    57b7:	48 39 ce             	cmp    %rcx,%rsi
    57ba:	0f 9f c0             	setg   %al
}
    57bd:	5d                   	pop    %rbp
    57be:	c3                   	ret
    57bf:	90                   	nop

00000000000057c0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    57c0:	f3 0f 1e fa          	endbr64
    57c4:	55                   	push   %rbp
    57c5:	48 89 e5             	mov    %rsp,%rbp
    57c8:	ff 15 1a 38 00 00    	call   *0x381a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  return 0;
    57ce:	31 c0                	xor    %eax,%eax
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    57d0:	4c 8b 5d 10          	mov    0x10(%rbp),%r11
    57d4:	4c 8b 55 18          	mov    0x18(%rbp),%r10
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    57d8:	48 39 d7             	cmp    %rdx,%rdi
    57db:	7f 18                	jg     57f5 <within+0x35>
    57dd:	4d 39 d8             	cmp    %r11,%r8
    57e0:	0f 9e c2             	setle  %dl
    57e3:	48 39 ce             	cmp    %rcx,%rsi
    57e6:	0f 9e c0             	setle  %al
    57e9:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    57eb:	31 c0                	xor    %eax,%eax
    57ed:	4d 39 d1             	cmp    %r10,%r9
    57f0:	0f 9e c0             	setle  %al
    57f3:	21 d0                	and    %edx,%eax
}
    57f5:	5d                   	pop    %rbp
    57f6:	c3                   	ret
    57f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005800 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5800:	f3 0f 1e fa          	endbr64
    5804:	55                   	push   %rbp
    5805:	48 89 e5             	mov    %rsp,%rbp
    5808:	ff 15 da 37 00 00    	call   *0x37da(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    580e:	48 8b 7d 10          	mov    0x10(%rbp),%rdi
    5812:	48 8b 75 30          	mov    0x30(%rbp),%rsi
    5816:	4c 8b 4d 20          	mov    0x20(%rbp),%r9
    581a:	4c 8b 55 28          	mov    0x28(%rbp),%r10
    581e:	4c 8b 45 40          	mov    0x40(%rbp),%r8
    5822:	4c 8b 5d 48          	mov    0x48(%rbp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5826:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
    582a:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  return left.tv_sec > right.tv_sec &&
    582e:	48 39 fe             	cmp    %rdi,%rsi
    5831:	7d 2d                	jge    5860 <overlap+0x60>
    5833:	48 39 ca             	cmp    %rcx,%rdx
    5836:	7d 60                	jge    5898 <overlap+0x98>
    5838:	4d 39 da             	cmp    %r11,%r10
    583b:	7d 0a                	jge    5847 <overlap+0x47>
    return 1;
    583d:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5842:	4d 39 c1             	cmp    %r8,%r9
    5845:	7c 0f                	jl     5856 <overlap+0x56>
  return 0;
    5847:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5849:	4d 39 c1             	cmp    %r8,%r9
    584c:	7f 08                	jg     5856 <overlap+0x56>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    584e:	31 c0                	xor    %eax,%eax
    5850:	4d 39 da             	cmp    %r11,%r10
    5853:	0f 9e c0             	setle  %al
}
    5856:	5d                   	pop    %rbp
    5857:	c3                   	ret
    5858:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5860:	7e 56                	jle    58b8 <overlap+0xb8>
    5862:	48 39 ca             	cmp    %rcx,%rdx
    5865:	7f 39                	jg     58a0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5867:	75 31                	jne    589a <overlap+0x9a>
    5869:	4d 39 c1             	cmp    %r8,%r9
    586c:	7c 2c                	jl     589a <overlap+0x9a>
    return 1;
    586e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5873:	4d 39 da             	cmp    %r11,%r10
    5876:	7d de                	jge    5856 <overlap+0x56>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5878:	48 39 ca             	cmp    %rcx,%rdx
}
    587b:	5d                   	pop    %rbp
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    587c:	0f 94 c2             	sete   %dl
    587f:	48 39 fe             	cmp    %rdi,%rsi
    5882:	0f 94 c0             	sete   %al
    5885:	21 c2                	and    %eax,%edx
    5887:	31 c0                	xor    %eax,%eax
    5889:	4d 39 c1             	cmp    %r8,%r9
    588c:	0f 94 c0             	sete   %al
    588f:	21 d0                	and    %edx,%eax
}
    5891:	c3                   	ret
    5892:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5898:	74 ad                	je     5847 <overlap+0x47>
  return 0;
    589a:	31 c0                	xor    %eax,%eax
}
    589c:	5d                   	pop    %rbp
    589d:	c3                   	ret
    589e:	66 90                	xchg   %ax,%ax
  return left.tv_sec > right.tv_sec &&
    58a0:	4d 39 da             	cmp    %r11,%r10
    58a3:	7e c4                	jle    5869 <overlap+0x69>
    return 1;
    58a5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    58aa:	4d 39 c1             	cmp    %r8,%r9
    58ad:	7e ba                	jle    5869 <overlap+0x69>
    58af:	eb a5                	jmp    5856 <overlap+0x56>
    58b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    58b8:	48 39 ca             	cmp    %rcx,%rdx
    58bb:	7c 8a                	jl     5847 <overlap+0x47>
    58bd:	4d 39 c1             	cmp    %r8,%r9
    58c0:	7d ac                	jge    586e <overlap+0x6e>
    58c2:	48 39 ca             	cmp    %rcx,%rdx
    58c5:	74 87                	je     584e <overlap+0x4e>
  return 0;
    58c7:	31 c0                	xor    %eax,%eax
    58c9:	eb d1                	jmp    589c <overlap+0x9c>
    58cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000058d0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    58d0:	f3 0f 1e fa          	endbr64
    58d4:	55                   	push   %rbp
    58d5:	48 89 e5             	mov    %rsp,%rbp
    58d8:	41 57                	push   %r15
    58da:	41 56                	push   %r14
    58dc:	41 55                	push   %r13
    58de:	41 54                	push   %r12
    58e0:	53                   	push   %rbx
    58e1:	48 83 ec 58          	sub    $0x58,%rsp
    58e5:	ff 15 fd 36 00 00    	call   *0x36fd(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    58eb:	41 89 f4             	mov    %esi,%r12d
  for (int x = 0 ; x < thread_count; x++) {
    58ee:	85 f6                	test   %esi,%esi
    58f0:	0f 8e df 02 00 00    	jle    5bd5 <verify+0x305>
    58f6:	48 8d 5f 20          	lea    0x20(%rdi),%rbx
    58fa:	45 31 ff             	xor    %r15d,%r15d
    58fd:	48 89 5d b8          	mov    %rbx,-0x48(%rbp)
    for (int z = 0 ; z < thread_count; z++) {
    5901:	48 89 5d c0          	mov    %rbx,-0x40(%rbp)
    5905:	45 31 ed             	xor    %r13d,%r13d
    5908:	45 89 e6             	mov    %r12d,%r14d
      if (z != x)  {
    590b:	45 39 ef             	cmp    %r13d,%r15d
    590e:	0f 84 27 02 00 00    	je     5b3b <verify+0x26b>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5914:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    5918:	8b 50 08             	mov    0x8(%rax),%edx
    591b:	85 d2                	test   %edx,%edx
    591d:	0f 8e 18 02 00 00    	jle    5b3b <verify+0x26b>
    5923:	48 89 5d 98          	mov    %rbx,-0x68(%rbp)
    5927:	45 31 e4             	xor    %r12d,%r12d
    592a:	44 89 6d 94          	mov    %r13d,-0x6c(%rbp)
    592e:	44 89 75 90          	mov    %r14d,-0x70(%rbp)
    5932:	4d 89 e6             	mov    %r12,%r14
    5935:	44 89 fa             	mov    %r15d,%edx
    5938:	48 8d 35 d5 08 00 00 	lea    0x8d5(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    593f:	bf 01 00 00 00       	mov    $0x1,%edi
    5944:	31 c0                	xor    %eax,%eax
    5946:	e8 15 cb ff ff       	call   2460 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    594b:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    594f:	8b 40 08             	mov    0x8(%rax),%eax
    5952:	85 c0                	test   %eax,%eax
    5954:	0f 8e c3 01 00 00    	jle    5b1d <verify+0x24d>
    595a:	4c 89 f0             	mov    %r14,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    595d:	4c 89 75 88          	mov    %r14,-0x78(%rbp)
    5961:	31 db                	xor    %ebx,%ebx
    5963:	48 c1 e0 09          	shl    $0x9,%rax
    5967:	44 89 7d 84          	mov    %r15d,-0x7c(%rbp)
    596b:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    596f:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    5973:	4c 8b 08             	mov    (%rax),%r9
    5976:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5980:	4c 8b 65 c0          	mov    -0x40(%rbp),%r12
    5984:	4c 8b 7d c8          	mov    -0x38(%rbp),%r15
    5988:	49 89 de             	mov    %rbx,%r14
    598b:	bf 01 00 00 00       	mov    $0x1,%edi
    5990:	49 c1 e6 09          	shl    $0x9,%r14
    5994:	48 8d 35 8e 08 00 00 	lea    0x88e(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    599b:	49 8b 04 24          	mov    (%r12),%rax
    599f:	4b 8b 8c 39 a0 01 00 00 	mov    0x1a0(%r9,%r15,1),%rcx
    59a7:	4c 89 75 a8          	mov    %r14,-0x58(%rbp)
    59ab:	4a 8b 94 30 a0 01 00 00 	mov    0x1a0(%rax,%r14,1),%rdx
    59b3:	31 c0                	xor    %eax,%eax
    59b5:	e8 a6 ca ff ff       	call   2460 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    59ba:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    59be:	4c 8b 08             	mov    (%rax),%r9
    59c1:	4b 83 bc 39 a0 01 00 00 00 	cmpq   $0x0,0x1a0(%r9,%r15,1)
    59ca:	0f 8e 34 01 00 00    	jle    5b04 <verify+0x234>
    59d0:	4d 03 34 24          	add    (%r12),%r14
    59d4:	48 89 5d a0          	mov    %rbx,-0x60(%rbp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    59d8:	ba 01 00 00 00       	mov    $0x1,%edx
    59dd:	4d 89 f5             	mov    %r14,%r13
    59e0:	4d 8b b5 a0 01 00 00 	mov    0x1a0(%r13),%r14
    59e7:	4d 85 f6             	test   %r14,%r14
    59ea:	0f 8e 10 01 00 00    	jle    5b00 <verify+0x230>
    59f0:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    59f4:	49 89 d4             	mov    %rdx,%r12
    59f7:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
    59fb:	31 db                	xor    %ebx,%ebx
    59fd:	49 c1 e4 05          	shl    $0x5,%r12
    5a01:	49 83 ec 20          	sub    $0x20,%r12
    5a05:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
    5a09:	eb 32                	jmp    5a3d <verify+0x16d>
    5a0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5a10:	4c 39 c1             	cmp    %r8,%rcx
    5a13:	0f 8d 47 01 00 00    	jge    5b60 <verify+0x290>
    5a19:	4c 39 d7             	cmp    %r10,%rdi
    5a1c:	7e 05                	jle    5a23 <verify+0x153>
    5a1e:	49 39 c3             	cmp    %rax,%r11
    5a21:	7c 75                	jl     5a98 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5a23:	4c 39 d7             	cmp    %r10,%rdi
    5a26:	0f 8d 9b 01 00 00    	jge    5bc7 <verify+0x2f7>
    5a2c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5a30:	48 83 c3 01          	add    $0x1,%rbx
    5a34:	49 39 de             	cmp    %rbx,%r14
    5a37:	0f 8e a2 00 00 00    	jle    5adf <verify+0x20f>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5a3d:	49 8b 8f 90 01 00 00 	mov    0x190(%r15),%rcx
    5a44:	48 89 d8             	mov    %rbx,%rax
    5a47:	48 c1 e0 05          	shl    $0x5,%rax
    5a4b:	49 03 85 90 01 00 00 	add    0x190(%r13),%rax
    5a52:	4c 01 e1             	add    %r12,%rcx
    5a55:	48 8b 30             	mov    (%rax),%rsi
    5a58:	48 8b 78 10          	mov    0x10(%rax),%rdi
    5a5c:	48 8b 11             	mov    (%rcx),%rdx
    5a5f:	4c 8b 41 08          	mov    0x8(%rcx),%r8
    5a63:	4c 8b 51 10          	mov    0x10(%rcx),%r10
    5a67:	4c 8b 59 18          	mov    0x18(%rcx),%r11
    5a6b:	48 8b 48 08          	mov    0x8(%rax),%rcx
    5a6f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    5a73:	48 39 d6             	cmp    %rdx,%rsi
    5a76:	7c 98                	jl     5a10 <verify+0x140>
    5a78:	0f 8e 32 01 00 00    	jle    5bb0 <verify+0x2e0>
    5a7e:	4c 39 c1             	cmp    %r8,%rcx
    5a81:	0f 8f e9 00 00 00    	jg     5b70 <verify+0x2a0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5a87:	75 a7                	jne    5a30 <verify+0x160>
    5a89:	4c 39 d7             	cmp    %r10,%rdi
    5a8c:	7f a2                	jg     5a30 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5a8e:	49 39 c3             	cmp    %rax,%r11
    5a91:	7c 9d                	jl     5a30 <verify+0x160>
    5a93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5a98:	49 89 c1             	mov    %rax,%r9
    5a9b:	48 89 f9             	mov    %rdi,%rcx
    5a9e:	48 8d 35 fb 09 00 00 	lea    0x9fb(%rip),%rsi        # 64a0 <_IO_stdin_used+0x4a0>
    5aa5:	31 c0                	xor    %eax,%eax
    5aa7:	bf 01 00 00 00       	mov    $0x1,%edi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5aac:	48 83 c3 01          	add    $0x1,%rbx
    5ab0:	e8 ab c9 ff ff       	call   2460 <__printf_chk@plt>
    5ab5:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    5ab9:	4c 8b 6d a8          	mov    -0x58(%rbp),%r13
    5abd:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5ac0:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5ac4:	4d 8b b5 a0 01 00 00 	mov    0x1a0(%r13),%r14
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5acb:	4c 8b 08             	mov    (%rax),%r9
    5ace:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    5ad2:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5ad6:	49 39 de             	cmp    %rbx,%r14
    5ad9:	0f 8f 5e ff ff ff    	jg     5a3d <verify+0x16d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5adf:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    5ae3:	49 3b 97 a0 01 00 00 	cmp    0x1a0(%r15),%rdx
    5aea:	7d 14                	jge    5b00 <verify+0x230>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5aec:	4d 8b b5 a0 01 00 00 	mov    0x1a0(%r13),%r14
    5af3:	48 83 c2 01          	add    $0x1,%rdx
    5af7:	4d 85 f6             	test   %r14,%r14
    5afa:	0f 8f f0 fe ff ff    	jg     59f0 <verify+0x120>
    5b00:	48 8b 5d a0          	mov    -0x60(%rbp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5b04:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    5b08:	48 83 c3 01          	add    $0x1,%rbx
    5b0c:	39 58 08             	cmp    %ebx,0x8(%rax)
    5b0f:	0f 8f 6b fe ff ff    	jg     5980 <verify+0xb0>
    5b15:	4c 8b 75 88          	mov    -0x78(%rbp),%r14
    5b19:	44 8b 7d 84          	mov    -0x7c(%rbp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5b1d:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    5b21:	49 83 c6 01          	add    $0x1,%r14
    5b25:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    5b29:	0f 8f 06 fe ff ff    	jg     5935 <verify+0x65>
    5b2f:	48 8b 5d 98          	mov    -0x68(%rbp),%rbx
    5b33:	44 8b 6d 94          	mov    -0x6c(%rbp),%r13d
    5b37:	44 8b 75 90          	mov    -0x70(%rbp),%r14d
    for (int z = 0 ; z < thread_count; z++) {
    5b3b:	41 8d 45 01          	lea    0x1(%r13),%eax
    5b3f:	48 81 45 c0 98 00 00 00 	addq   $0x98,-0x40(%rbp)
    5b47:	41 39 c6             	cmp    %eax,%r14d
    5b4a:	0f 84 96 00 00 00    	je     5be6 <verify+0x316>
    5b50:	41 89 c5             	mov    %eax,%r13d
    5b53:	e9 b3 fd ff ff       	jmp    590b <verify+0x3b>
    5b58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5b60:	0f 85 ca fe ff ff    	jne    5a30 <verify+0x160>
    5b66:	e9 b8 fe ff ff       	jmp    5a23 <verify+0x153>
    5b6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5b70:	49 39 c3             	cmp    %rax,%r11
    5b73:	7e 09                	jle    5b7e <verify+0x2ae>
    5b75:	4c 39 d7             	cmp    %r10,%rdi
    5b78:	0f 8c 1a ff ff ff    	jl     5a98 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5b7e:	4c 39 d7             	cmp    %r10,%rdi
    5b81:	0f 8f a9 fe ff ff    	jg     5a30 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5b87:	49 39 c3             	cmp    %rax,%r11
    5b8a:	0f 8d 08 ff ff ff    	jge    5a98 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5b90:	48 39 d6             	cmp    %rdx,%rsi
    5b93:	0f 85 97 fe ff ff    	jne    5a30 <verify+0x160>
    5b99:	4c 39 c1             	cmp    %r8,%rcx
    5b9c:	0f 85 8e fe ff ff    	jne    5a30 <verify+0x160>
    5ba2:	4c 39 d7             	cmp    %r10,%rdi
    5ba5:	0f 84 ed fe ff ff    	je     5a98 <verify+0x1c8>
    5bab:	e9 80 fe ff ff       	jmp    5a30 <verify+0x160>
    5bb0:	4c 39 c1             	cmp    %r8,%rcx
    5bb3:	0f 8c 6a fe ff ff    	jl     5a23 <verify+0x153>
    5bb9:	4c 39 d7             	cmp    %r10,%rdi
    5bbc:	7e c9                	jle    5b87 <verify+0x2b7>
    5bbe:	4c 39 c1             	cmp    %r8,%rcx
    5bc1:	0f 85 69 fe ff ff    	jne    5a30 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5bc7:	49 39 c3             	cmp    %rax,%r11
    5bca:	0f 8f 60 fe ff ff    	jg     5a30 <verify+0x160>
    5bd0:	e9 c3 fe ff ff       	jmp    5a98 <verify+0x1c8>
}
    5bd5:	48 83 c4 58          	add    $0x58,%rsp
    5bd9:	31 c0                	xor    %eax,%eax
    5bdb:	5b                   	pop    %rbx
    5bdc:	41 5c                	pop    %r12
    5bde:	41 5d                	pop    %r13
    5be0:	41 5e                	pop    %r14
    5be2:	41 5f                	pop    %r15
    5be4:	5d                   	pop    %rbp
    5be5:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
    5be6:	48 81 45 b8 98 00 00 00 	addq   $0x98,-0x48(%rbp)
    5bee:	45 89 f4             	mov    %r14d,%r12d
    5bf1:	41 8d 57 01          	lea    0x1(%r15),%edx
    5bf5:	45 39 ef             	cmp    %r13d,%r15d
    5bf8:	74 db                	je     5bd5 <verify+0x305>
    5bfa:	41 89 d7             	mov    %edx,%r15d
    5bfd:	e9 ff fc ff ff       	jmp    5901 <verify+0x31>
    5c02:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5c0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005c10 <atexit>:
    5c10:	f3 0f 1e fa          	endbr64
    5c14:	48 8b 15 ed 33 00 00 	mov    0x33ed(%rip),%rdx        # 9008 <__dso_handle>
    5c1b:	31 f6                	xor    %esi,%esi
    5c1d:	e9 8e c8 ff ff       	jmp    24b0 <__cxa_atexit@plt>
    5c22:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5c2c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005c30 <__stack_chk_fail_local>:
    5c30:	f3 0f 1e fa          	endbr64
    5c34:	50                   	push   %rax
    5c35:	58                   	pop    %rax
    5c36:	48 83 ec 08          	sub    $0x8,%rsp
    5c3a:	e8 f1 c6 ff ff       	call   2330 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000005c40 <_fini>:
    5c40:	f3 0f 1e fa          	endbr64
    5c44:	48 83 ec 08          	sub    $0x8,%rsp
    5c48:	48 83 c4 08          	add    $0x8,%rsp
    5c4c:	c3                   	ret
