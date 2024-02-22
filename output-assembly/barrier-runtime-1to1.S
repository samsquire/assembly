
barrier-runtime-1to1:     file format elf64-x86-64


Disassembly of section .init:

0000000000002000 <_init>:
    2000:	f3 0f 1e fa          	endbr64
    2004:	48 83 ec 08          	sub    $0x8,%rsp
    2008:	48 8d 05 71 13 00 00 	lea    0x1371(%rip),%rax        # 3380 <__gmon_start__>
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
  if (a < b) { return a; }
  if (b < a) { return b; }
  return a;
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
    262b:	48 8d 3d b6 3e 00 00 	lea    0x3eb6(%rip),%rdi        # 64e8 <_IO_stdin_used+0x4e8>
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
    26d4:	ba 0f 27 00 00       	mov    $0x270f,%edx
    26d9:	48 8d 35 68 3e 00 00 	lea    0x3e68(%rip),%rsi        # 6548 <_IO_stdin_used+0x548>
    26e0:	31 c0                	xor    %eax,%eax
    26e2:	bf 01 00 00 00       	mov    $0x1,%edi
    26e7:	e8 74 fd ff ff       	call   2460 <__printf_chk@plt>
    26ec:	ba 0f 27 00 00       	mov    $0x270f,%edx
    26f1:	48 8d 35 80 3e 00 00 	lea    0x3e80(%rip),%rsi        # 6578 <_IO_stdin_used+0x578>
    26f8:	31 c0                	xor    %eax,%eax
    26fa:	bf 01 00 00 00       	mov    $0x1,%edi
    26ff:	e8 5c fd ff ff       	call   2460 <__printf_chk@plt>
    2704:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2709:	48 8d 35 b1 3b 00 00 	lea    0x3bb1(%rip),%rsi        # 62c1 <_IO_stdin_used+0x2c1>
    2710:	31 c0                	xor    %eax,%eax
    2712:	bf 01 00 00 00       	mov    $0x1,%edi
    2717:	e8 44 fd ff ff       	call   2460 <__printf_chk@plt>
    271c:	ba 1e 00 00 00       	mov    $0x1e,%edx
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
  int barrier_count = cluster_size;
  int total_barrier_count = cluster_size + 1;
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
    277a:	bf 0f 27 00 00       	mov    $0x270f,%edi
    buffers[x].count = buffer_size;
    277f:	c7 00 0f 27 00 00    	movl   $0x270f,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2785:	48 89 c3             	mov    %rax,%rbx
    2788:	48 89 45 88          	mov    %rax,-0x78(%rbp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    278c:	e8 0f fc ff ff       	call   23a0 <calloc@plt>
    2791:	4c 8b 45 b8          	mov    -0x48(%rbp),%r8
    2795:	48 89 43 08          	mov    %rax,0x8(%rbx)
    for (int y = 0 ; y < buffer_size; y++) {
    2799:	48 8d 88 f0 70 02 00 	lea    0x270f0(%rax),%rcx
    27a0:	48 8d 50 10          	lea    0x10(%rax),%rdx
      buffers[x].buffer[y].available = 0;
    27a4:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    27ab:	c7 40 18 00 00 00 00 	movl   $0x0,0x18(%rax)
    27b2:	c7 40 28 00 00 00 00 	movl   $0x0,0x28(%rax)
    for (int y = 0 ; y < buffer_size; y++) {
    27b9:	48 8d 42 20          	lea    0x20(%rdx),%rax
    27bd:	48 39 c8             	cmp    %rcx,%rax
    27c0:	75 de                	jne    27a0 <main+0x190>
    27c2:	4c 89 45 b8          	mov    %r8,-0x48(%rbp)
    27c6:	4d 89 c7             	mov    %r8,%r15
    }
  }
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int current_thread = 0;
  for (int x = 0 ; x < thread_count; x++) {
    27c9:	31 db                	xor    %ebx,%ebx
    27cb:	4c 8d 35 ce 3d 00 00 	lea    0x3dce(%rip),%r14        # 65a0 <_IO_stdin_used+0x5a0>
    27d2:	4c 8d 25 16 3b 00 00 	lea    0x3b16(%rip),%r12        # 62ef <_IO_stdin_used+0x2ef>
    27d9:	89 da                	mov    %ebx,%edx
    27db:	4c 89 f6             	mov    %r14,%rsi
    27de:	bf 01 00 00 00       	mov    $0x1,%edi
    27e3:	31 c0                	xor    %eax,%eax
    27e5:	e8 76 fc ff ff       	call   2460 <__printf_chk@plt>
    int cluster_start = x;
    printf("Creating cluster starting from %d\n", cluster_start);
    for (int cluster_index = 0 ; cluster_index < cluster_size && x < thread_count; cluster_index++) {
    27ea:	45 31 ed             	xor    %r13d,%r13d
      thread_data[x].threads = &thread_data[cluster_start];
      thread_data[x].thread_count = cluster_size;
      thread_data[x].thread_index = cluster_index;
    27ed:	45 89 2f             	mov    %r13d,(%r15)
    27f0:	89 d9                	mov    %ebx,%ecx
    27f2:	89 da                	mov    %ebx,%edx
    27f4:	4c 89 e6             	mov    %r12,%rsi
      thread_data[x].threads = &thread_data[cluster_start];
    27f7:	4d 89 7f 10          	mov    %r15,0x10(%r15)
    27fb:	bf 01 00 00 00       	mov    $0x1,%edi
    2800:	31 c0                	xor    %eax,%eax
    for (int cluster_index = 0 ; cluster_index < cluster_size && x < thread_count; cluster_index++) {
    2802:	41 83 c5 01          	add    $0x1,%r13d
      thread_data[x].thread_count = cluster_size;
    2806:	41 c7 47 18 03 00 00 00 	movl   $0x3,0x18(%r15)
    280e:	e8 4d fc ff ff       	call   2460 <__printf_chk@plt>
    for (int cluster_index = 0 ; cluster_index < cluster_size && x < thread_count; cluster_index++) {
    2813:	41 83 fd 03          	cmp    $0x3,%r13d
    2817:	75 d4                	jne    27ed <main+0x1dd>
      printf("thread %d is in cluster %d\n", x, cluster_start);
    }
    x += cluster_size;
    2819:	8d 53 03             	lea    0x3(%rbx),%edx
    281c:	48 8d 35 e8 3a 00 00 	lea    0x3ae8(%rip),%rsi        # 630b <_IO_stdin_used+0x30b>
    2823:	bf 01 00 00 00       	mov    $0x1,%edi
    2828:	31 c0                	xor    %eax,%eax
    282a:	e8 31 fc ff ff       	call   2460 <__printf_chk@plt>
  for (int x = 0 ; x < thread_count; x++) {
    282f:	49 81 c7 60 02 00 00 	add    $0x260,%r15
    2836:	83 fb 04             	cmp    $0x4,%ebx
    2839:	74 07                	je     2842 <main+0x232>
    283b:	bb 04 00 00 00       	mov    $0x4,%ebx
    2840:	eb 97                	jmp    27d9 <main+0x1c9>
    2842:	4c 8b 45 b8          	mov    -0x48(%rbp),%r8
    2846:	48 c7 45 98 00 00 00 00 	movq   $0x0,-0x68(%rbp)
    printf("to %d\n", x);

  }

  for (int x = 0 ; x < total_threads ; x++) {
    284e:	c7 45 b8 00 00 00 00 	movl   $0x0,-0x48(%rbp)
  int external_thread_index = 0;
    2855:	c7 45 94 00 00 00 00 	movl   $0x0,-0x6c(%rbp)
    285c:	4d 89 c7             	mov    %r8,%r15
          thread_data[x].tasks[y].run = barriered_work; 
        } else {
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    285f:	4c 89 85 78 ff ff ff 	mov    %r8,-0x88(%rbp)
    2866:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    if (x < thread_count) {
    2870:	83 7d b8 05          	cmpl   $0x5,-0x48(%rbp)
    2874:	7e 13                	jle    2889 <main+0x279>
      thread_data[x].threads = thread_data;
    2876:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
      thread_data[x].thread_count = thread_count;
    287d:	41 c7 47 18 06 00 00 00 	movl   $0x6,0x18(%r15)
      thread_data[x].threads = thread_data;
    2885:	49 89 47 10          	mov    %rax,0x10(%r15)
    thread_data[x].protected_state = protected_state;
    2889:	48 8b 45 80          	mov    -0x80(%rbp),%rax
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    288d:	be 10 00 00 00       	mov    $0x10,%esi
    2892:	bf 64 00 00 00       	mov    $0x64,%edi
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2897:	31 db                	xor    %ebx,%ebx
    thread_data[x].total_thread_count = total_threads;
    2899:	41 c7 47 1c 09 00 00 00 	movl   $0x9,0x1c(%r15)
    thread_data[x].task_count = total_barrier_count;
    28a1:	41 c7 47 28 04 00 00 00 	movl   $0x4,0x28(%r15)
    thread_data[x].protected_state = protected_state;
    28a9:	49 89 47 30          	mov    %rax,0x30(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28ad:	e8 ee fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28b2:	be 10 00 00 00       	mov    $0x10,%esi
    28b7:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28bc:	49 89 47 50          	mov    %rax,0x50(%r15)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28c0:	e8 db fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28c5:	be 28 00 00 00       	mov    $0x28,%esi
    28ca:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    28cf:	66 0f 6f 05 39 41 00 00 	movdqa 0x4139(%rip),%xmm0        # 6a10 <_IO_stdin_used+0xa10>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28d7:	49 89 47 58          	mov    %rax,0x58(%r15)
    thread_data[x].timestamp_count = 0;
    28db:	41 0f 11 47 68       	movups %xmm0,0x68(%r15)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28e0:	e8 bb fa ff ff       	call   23a0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    28e5:	be 98 00 00 00       	mov    $0x98,%esi
    28ea:	bf 04 00 00 00       	mov    $0x4,%edi
    thread_data[x].task_timestamp_count = 0;
    28ef:	66 0f 6f 0d 19 41 00 00 	movdqa 0x4119(%rip),%xmm1        # 6a10 <_IO_stdin_used+0xa10>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28f7:	49 89 47 78          	mov    %rax,0x78(%r15)
    thread_data[x].task_timestamp_count = 0;
    28fb:	41 0f 11 8f 80 00 00 00 	movups %xmm1,0x80(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2903:	e8 98 fa ff ff       	call   23a0 <calloc@plt>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2908:	4c 89 7d a0          	mov    %r15,-0x60(%rbp)
      thread_data[x].tasks = barriers;
    290c:	49 89 47 20          	mov    %rax,0x20(%r15)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2910:	48 89 c2             	mov    %rax,%rdx
            thread_data[x].tasks[y].protected = do_protected_write; 
    2913:	4c 63 f3             	movslq %ebx,%r14
    2916:	4b 8d 04 f6          	lea    (%r14,%r14,8),%rax
    291a:	4d 8d 2c 46          	lea    (%r14,%rax,2),%r13
    291e:	49 c1 e5 03          	shl    $0x3,%r13
    2922:	4e 8d 24 2a          	lea    (%rdx,%r13,1),%r12
        if (x == y) {
    2926:	39 5d b8             	cmp    %ebx,-0x48(%rbp)
    2929:	0f 84 01 0a 00 00    	je     3330 <main+0xd20>
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    292f:	be 20 00 00 00       	mov    $0x20,%esi
    2934:	bf 06 00 00 00       	mov    $0x6,%edi
    2939:	e8 62 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    293e:	89 5d b0             	mov    %ebx,-0x50(%rbp)
    2941:	4c 89 6d a8          	mov    %r13,-0x58(%rbp)
    2945:	49 89 c7             	mov    %rax,%r15
    2948:	49 89 44 24 70       	mov    %rax,0x70(%r12)
        for (int b = 0 ; b < thread_count ; b++) {
    294d:	4c 8d a0 c0 00 00 00 	lea    0xc0(%rax),%r12
    2954:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2958:	be 08 00 00 00       	mov    $0x8,%esi
    295d:	bf 0f 27 00 00       	mov    $0x270f,%edi
        for (int b = 0 ; b < thread_count ; b++) {
    2962:	49 83 c7 20          	add    $0x20,%r15
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2966:	e8 35 fa ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    296b:	be 08 00 00 00       	mov    $0x8,%esi
    2970:	bf 0f 27 00 00       	mov    $0x270f,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2975:	49 89 c5             	mov    %rax,%r13
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2978:	e8 23 fa ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    297d:	be 18 00 00 00       	mov    $0x18,%esi
    2982:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2987:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    298a:	e8 11 fa ff ff       	call   23a0 <calloc@plt>
          mailboxes[b].higher = &data[1];
    298f:	48 8d 70 18          	lea    0x18(%rax),%rsi
          data[0].messages_count = 0;
    2993:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
          mailboxes[b].lower = &data[0];
    299b:	49 89 47 e0          	mov    %rax,-0x20(%r15)
          mailboxes[b].higher = &data[1];
    299f:	49 89 77 e8          	mov    %rsi,-0x18(%r15)
          data[0].messages = messages;
    29a3:	4c 89 28             	mov    %r13,(%rax)
          data[1].messages = messages2;
    29a6:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_limit = messages_limit;
    29aa:	48 c7 40 10 0f 27 00 00 	movq   $0x270f,0x10(%rax)
          data[1].messages_count = 0;
    29b2:	48 c7 40 20 00 00 00 00 	movq   $0x0,0x20(%rax)
          data[1].messages_limit = messages_limit;
    29ba:	48 c7 40 28 0f 27 00 00 	movq   $0x270f,0x28(%rax)
        for (int b = 0 ; b < thread_count ; b++) {
    29c2:	4d 39 fc             	cmp    %r15,%r12
    29c5:	75 91                	jne    2958 <main+0x348>
        char *message = malloc(sizeof(char) * 256);
    29c7:	be 01 00 00 00       	mov    $0x1,%esi
    29cc:	bf 00 01 00 00       	mov    $0x100,%edi
    29d1:	8b 5d b0             	mov    -0x50(%rbp),%ebx
    29d4:	4c 8b 6d a8          	mov    -0x58(%rbp),%r13
    29d8:	e8 c3 f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    29dd:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    29e2:	49 89 c4             	mov    %rax,%r12
        struct Message *messaged = malloc(sizeof(struct Message));
    29e5:	e8 36 fa ff ff       	call   2420 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    29ea:	44 8b 45 b8          	mov    -0x48(%rbp),%r8d
    29ee:	4c 89 e7             	mov    %r12,%rdi
    29f1:	41 89 d9             	mov    %ebx,%r9d
    29f4:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
    29f8:	48 8d 0d c9 3b 00 00 	lea    0x3bc9(%rip),%rcx        # 65c8 <_IO_stdin_used+0x5c8>
    29ff:	ba 00 01 00 00       	mov    $0x100,%edx
    2a04:	31 c0                	xor    %eax,%eax
    2a06:	be 01 00 00 00       	mov    $0x1,%esi
    2a0b:	e8 30 fb ff ff       	call   2540 <__sprintf_chk@plt>
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a10:	4c 8b 7d a0          	mov    -0x60(%rbp),%r15
        messaged->message = message;
    2a14:	4c 8b 55 b0          	mov    -0x50(%rbp),%r10
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a18:	be 20 00 00 00       	mov    $0x20,%esi
        messaged->thread_index = x;
    2a1d:	48 8b 45 98          	mov    -0x68(%rbp),%rax
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a21:	49 8b 57 20          	mov    0x20(%r15),%rdx
        messaged->message = message;
    2a25:	4d 89 22             	mov    %r12,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a28:	44 8d 63 01          	lea    0x1(%rbx),%r12d
        messaged->task_index = y;
    2a2c:	4d 89 72 10          	mov    %r14,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a30:	4e 8d 34 2a          	lea    (%rdx,%r13,1),%r14
        messaged->thread_index = x;
    2a34:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a38:	45 89 a6 90 00 00 00 	mov    %r12d,0x90(%r14)
        thread_data[x].tasks[y].message = messaged;
    2a3f:	4d 89 96 88 00 00 00 	mov    %r10,0x88(%r14)
        thread_data[x].tasks[y].sending = 1;
    2a46:	41 c7 86 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r14)
        thread_data[x].tasks[y].snapshot_count = 999999;
    2a51:	49 c7 46 58 3f 42 0f 00 	movq   $0xf423f,0x58(%r14)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a59:	49 8b 7e 58          	mov    0x58(%r14),%rdi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a5d:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a61:	e8 3a f9 ff ff       	call   23a0 <calloc@plt>
        if (y == barrier_count - 1) {
    2a66:	83 fb 02             	cmp    $0x2,%ebx
    2a69:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a6d:	49 89 46 50          	mov    %rax,0x50(%r14)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a71:	41 8b 07             	mov    (%r15),%eax
        thread_data[x].tasks[y].current_snapshot = 0;
    2a74:	49 c7 46 60 00 00 00 00 	movq   $0x0,0x60(%r14)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a7c:	41 89 46 38          	mov    %eax,0x38(%r14)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2a80:	4d 89 7e 30          	mov    %r15,0x30(%r14)
        thread_data[x].tasks[y].available = 1;
    2a84:	41 c7 46 40 01 00 00 00 	movl   $0x1,0x40(%r14)
        thread_data[x].tasks[y].arrived = 0;
    2a8c:	41 c7 46 08 00 00 00 00 	movl   $0x0,0x8(%r14)
        thread_data[x].tasks[y].thread_count = thread_count;
    2a94:	41 c7 46 3c 06 00 00 00 	movl   $0x6,0x3c(%r14)
        thread_data[x].tasks[y].task_count = total_barrier_count;
    2a9c:	41 c7 46 44 04 00 00 00 	movl   $0x4,0x44(%r14)
        thread_data[x].tasks[y].worker_count = thread_count;
    2aa4:	41 c7 86 84 00 00 00 06 00 00 00 	movl   $0x6,0x84(%r14)
        thread_data[x].tasks[y].task_index = y;
    2aaf:	41 89 1e             	mov    %ebx,(%r14)
        if (y == barrier_count - 1) {
    2ab2:	0f 84 58 08 00 00    	je     3310 <main+0xd00>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2ab8:	8b 45 b8             	mov    -0x48(%rbp),%eax
    2abb:	39 d8                	cmp    %ebx,%eax
    2abd:	75 61                	jne    2b20 <main+0x510>
    2abf:	8b 5d 94             	mov    -0x6c(%rbp),%ebx
    2ac2:	85 db                	test   %ebx,%ebx
    2ac4:	7f 5a                	jg     2b20 <main+0x510>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2ac6:	89 c2                	mov    %eax,%edx
    2ac8:	bf 01 00 00 00       	mov    $0x1,%edi
    2acd:	48 8d 35 1c 3b 00 00 	lea    0x3b1c(%rip),%rsi        # 65f0 <_IO_stdin_used+0x5f0>
    2ad4:	31 c0                	xor    %eax,%eax
    2ad6:	e8 85 f9 ff ff       	call   2460 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2adb:	48 8b 7d 88          	mov    -0x78(%rbp),%rdi
    2adf:	48 63 c3             	movslq %ebx,%rax
    2ae2:	48 89 c1             	mov    %rax,%rcx
    2ae5:	48 c1 e0 04          	shl    $0x4,%rax
    2ae9:	48 01 f8             	add    %rdi,%rax
    2aec:	48 8b 7d a0          	mov    -0x60(%rbp),%rdi
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2af0:	48 8b 57 20          	mov    0x20(%rdi),%rdx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2af4:	48 89 47 38          	mov    %rax,0x38(%rdi)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2af8:	48 8d 05 11 2c 00 00 	lea    0x2c11(%rip),%rax        # 5710 <barriered_work_ingest>
    2aff:	49 01 d5             	add    %rdx,%r13
    2b02:	49 89 45 20          	mov    %rax,0x20(%r13)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b06:	8d 41 01             	lea    0x1(%rcx),%eax
    2b09:	89 45 94             	mov    %eax,-0x6c(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b0c:	41 83 fc 04          	cmp    $0x4,%r12d
    2b10:	74 1f                	je     2b31 <main+0x521>
  int external_thread_index = 0;
    2b12:	44 89 e3             	mov    %r12d,%ebx
    2b15:	e9 f9 fd ff ff       	jmp    2913 <main+0x303>
    2b1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    2b20:	48 8d 05 59 29 00 00 	lea    0x2959(%rip),%rax        # 5480 <barriered_work>
    2b27:	49 89 46 20          	mov    %rax,0x20(%r14)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b2b:	41 83 fc 04          	cmp    $0x4,%r12d
    2b2f:	75 e1                	jne    2b12 <main+0x502>

          }
        }
      }
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b31:	4c 8b 7d a0          	mov    -0x60(%rbp),%r15
    2b35:	48 8d 05 b4 09 00 00 	lea    0x9b4(%rip),%rax        # 34f0 <barriered_reset>
  for (int x = 0 ; x < total_threads ; x++) {
    2b3c:	83 45 b8 01          	addl   $0x1,-0x48(%rbp)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b40:	48 89 82 e8 01 00 00 	mov    %rax,0x1e8(%rdx)
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2b47:	4c 89 ba f8 01 00 00 	mov    %r15,0x1f8(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2b4e:	49 81 c7 98 00 00 00 	add    $0x98,%r15
      thread_data[x].tasks[barrier_count].available = 1; 
    2b55:	c7 82 08 02 00 00 01 00 00 00 	movl   $0x1,0x208(%rdx)
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2b5f:	c7 82 d0 01 00 00 00 00 00 00 	movl   $0x0,0x1d0(%rdx)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2b69:	c7 82 c8 01 00 00 03 00 00 00 	movl   $0x3,0x1c8(%rdx)
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
    2b73:	c7 82 04 02 00 00 06 00 00 00 	movl   $0x6,0x204(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2b7d:	41 8b 87 68 ff ff ff 	mov    -0x98(%r15),%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2b84:	48 83 45 98 01       	addq   $0x1,-0x68(%rbp)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2b89:	89 82 00 02 00 00    	mov    %eax,0x200(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2b8f:	8b 45 b8             	mov    -0x48(%rbp),%eax
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2b92:	c7 82 4c 02 00 00 06 00 00 00 	movl   $0x6,0x24c(%rdx)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2b9c:	c7 82 0c 02 00 00 04 00 00 00 	movl   $0x4,0x20c(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2ba6:	83 f8 09             	cmp    $0x9,%eax
    2ba9:	0f 85 c1 fc ff ff    	jne    2870 <main+0x260>

      current_thread += cluster_size;
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].threads = thread_data;
    2baf:	4c 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%r8
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bb6:	be 38 00 00 00       	mov    $0x38,%esi
    2bbb:	bf 09 00 00 00       	mov    $0x9,%edi
  thread_data[thread_count].thread_count = thread_count;
  thread_data[thread_count].thread_index = 0;

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
  for (int x = 0 ; x < thread_count ; x++) {
    2bc0:	45 31 f6             	xor    %r14d,%r14d
    thread_data[n].tasks[0].scheduled = 1;
    2bc3:	49 8b 40 20          	mov    0x20(%r8),%rax
    2bc7:	4c 89 45 a8          	mov    %r8,-0x58(%rbp)
    thread_data[x].threads = thread_data;
    2bcb:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    thread_data[x].thread_count = thread_count;
    2bd2:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    thread_data[x].thread_index = x;
    2bdd:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    thread_data[x].task_count = total_barrier_count;
    2be8:	41 c7 80 50 04 00 00 04 00 00 00 	movl   $0x4,0x450(%r8)
    thread_data[n].tasks[0].scheduled = 1;
    2bf3:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2bfa:	49 8b 80 b8 00 00 00 	mov    0xb8(%r8),%rax
    2c01:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2c08:	49 8b 80 50 01 00 00 	mov    0x150(%r8),%rax
    2c0f:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2c16:	49 8b 80 e8 01 00 00 	mov    0x1e8(%r8),%rax
    2c1d:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2c24:	49 8b 80 80 02 00 00 	mov    0x280(%r8),%rax
    2c2b:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2c32:	49 8b 80 18 03 00 00 	mov    0x318(%r8),%rax
    2c39:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c40:	e8 5b f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c45:	be 38 00 00 00       	mov    $0x38,%esi
    2c4a:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c4f:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c52:	e8 49 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c57:	be 38 00 00 00       	mov    $0x38,%esi
    2c5c:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c61:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c65:	e8 36 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2c6a:	be 08 00 00 00       	mov    $0x8,%esi
    2c6f:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c74:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2c78:	e8 23 f7 ff ff       	call   23a0 <calloc@plt>
  thread_data[thread_count].type = TIMER;
    2c7d:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    2c81:	ba 06 00 00 00       	mov    $0x6,%edx
    2c86:	48 8d 35 85 36 00 00 	lea    0x3685(%rip),%rsi        # 6312 <_IO_stdin_used+0x312>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2c8d:	49 89 c5             	mov    %rax,%r13
    2c90:	bf 01 00 00 00       	mov    $0x1,%edi
    2c95:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].type = TIMER;
    2c97:	41 c7 80 94 03 00 00 00 00 00 00 	movl   $0x0,0x394(%r8)
  thread_data[thread_count].running = 1;
    2ca2:	4d 89 ec             	mov    %r13,%r12
    2ca5:	41 c7 80 bc 03 00 00 01 00 00 00 	movl   $0x1,0x3bc(%r8)
  thread_data[thread_count].task_count = total_barrier_count;
    2cb0:	41 c7 80 b8 03 00 00 04 00 00 00 	movl   $0x4,0x3b8(%r8)
  thread_data[thread_count].threads = thread_data;
    2cbb:	4d 89 80 a0 03 00 00 	mov    %r8,0x3a0(%r8)
  thread_data[thread_count].thread_count = thread_count;
    2cc2:	41 c7 80 a8 03 00 00 06 00 00 00 	movl   $0x6,0x3a8(%r8)
  thread_data[thread_count].thread_index = 0;
    2ccd:	41 c7 80 90 03 00 00 00 00 00 00 	movl   $0x0,0x390(%r8)
    2cd8:	e8 83 f7 ff ff       	call   2460 <__printf_chk@plt>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2cdd:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    2ce1:	49 8d 7d 30          	lea    0x30(%r13),%rdi
    2ce5:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2cec:	48 8d 15 bd 0b 00 00 	lea    0xbbd(%rip),%rdx        # 38b0 <timer_thread>
    2cf3:	49 8d 88 90 03 00 00 	lea    0x390(%r8),%rcx
    2cfa:	e8 81 f7 ff ff       	call   2480 <pthread_create@plt>
    2cff:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    2d03:	4c 89 6d a8          	mov    %r13,-0x58(%rbp)
    2d07:	45 89 f5             	mov    %r14d,%r13d
    2d0a:	4d 89 c7             	mov    %r8,%r15
    2d0d:	4d 89 c6             	mov    %r8,%r14
    thread_data[x].type = WORKER;
    2d10:	41 c7 47 04 01 00 00 00 	movl   $0x1,0x4(%r15)
    2d18:	44 89 ea             	mov    %r13d,%edx
    2d1b:	bf 01 00 00 00       	mov    $0x1,%edi
    2d20:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2d22:	41 c7 47 2c 01 00 00 00 	movl   $0x1,0x2c(%r15)
    2d2a:	48 8d 35 df 38 00 00 	lea    0x38df(%rip),%rsi        # 6610 <_IO_stdin_used+0x610>
  for (int x = 0 ; x < thread_count ; x++) {
    2d31:	41 83 c5 01          	add    $0x1,%r13d
    2d35:	e8 26 f7 ff ff       	call   2460 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2d3a:	4c 89 f9             	mov    %r15,%rcx
    2d3d:	48 89 de             	mov    %rbx,%rsi
    2d40:	4c 89 e7             	mov    %r12,%rdi
    2d43:	48 8d 15 26 08 00 00 	lea    0x826(%rip),%rdx        # 3570 <barriered_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    2d4a:	49 81 c7 98 00 00 00 	add    $0x98,%r15
    2d51:	49 83 c4 08          	add    $0x8,%r12
    2d55:	48 83 c3 38          	add    $0x38,%rbx
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2d59:	e8 22 f7 ff ff       	call   2480 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2d5e:	41 83 fd 06          	cmp    $0x6,%r13d
    2d62:	75 ac                	jne    2d10 <main+0x700>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2d64:	be d8 00 00 00       	mov    $0xd8,%esi
    2d69:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    2d6e:	4c 8b 6d a8          	mov    -0x58(%rbp),%r13
    2d72:	41 c7 86 2c 04 00 00 02 00 00 00 	movl   $0x2,0x42c(%r14)
    thread_data[x].task_count = 0;
    2d7d:	4c 89 75 a8          	mov    %r14,-0x58(%rbp)
    2d81:	4c 8d 65 c0          	lea    -0x40(%rbp),%r12
    2d85:	48 8d 1d f6 35 00 00 	lea    0x35f6(%rip),%rbx        # 6382 <_IO_stdin_used+0x382>
    thread_data[x].running = 1;
    2d8c:	41 c7 86 54 04 00 00 01 00 00 00 	movl   $0x1,0x454(%r14)
    thread_data[x].task_count = 0;
    2d97:	41 c7 86 50 04 00 00 00 00 00 00 	movl   $0x0,0x450(%r14)
    2da2:	45 31 f6             	xor    %r14d,%r14d
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2da5:	e8 f6 f5 ff ff       	call   23a0 <calloc@plt>
    2daa:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2dae:	be 00 08 00 00       	mov    $0x800,%esi
    2db3:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2db5:	49 89 80 68 04 00 00 	mov    %rax,0x468(%r8)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2dbc:	e8 0f f7 ff ff       	call   24d0 <eventfd@plt>
    2dc1:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    2dc5:	ba 07 00 00 00       	mov    $0x7,%edx
    2dca:	48 8d 35 5f 35 00 00 	lea    0x355f(%rip),%rsi        # 6330 <_IO_stdin_used+0x330>
    2dd1:	bf 01 00 00 00       	mov    $0x1,%edi
    2dd6:	41 89 80 70 04 00 00 	mov    %eax,0x470(%r8)
    2ddd:	31 c0                	xor    %eax,%eax
    thread_data[x].threads = thread_data;
    2ddf:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    thread_data[x].thread_count = thread_count;
    2de6:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    thread_data[x].thread_index = x;
    2df1:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    2dfc:	e8 5f f6 ff ff       	call   2460 <__printf_chk@plt>
    thread_data[x].type = IO;
    2e01:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2e05:	48 8b 75 b8          	mov    -0x48(%rbp),%rsi
    2e09:	49 8d 7d 38          	lea    0x38(%r13),%rdi
    2e0d:	48 8d 15 4c 1e 00 00 	lea    0x1e4c(%rip),%rdx        # 4c60 <io_thread>
    thread_data[x].type = IO;
    2e14:	49 8d 88 28 04 00 00 	lea    0x428(%r8),%rcx
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2e1b:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2e22:	e8 59 f6 ff ff       	call   2480 <pthread_create@plt>
    2e27:	ba 08 00 00 00       	mov    $0x8,%edx
    2e2c:	48 8d 35 14 35 00 00 	lea    0x3514(%rip),%rsi        # 6347 <_IO_stdin_used+0x347>
    2e33:	31 c0                	xor    %eax,%eax
    2e35:	bf 01 00 00 00       	mov    $0x1,%edi
    2e3a:	e8 21 f6 ff ff       	call   2460 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    2e3f:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    2e43:	48 8b 45 88          	mov    -0x78(%rbp),%rax

    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2e47:	49 8d 7d 40          	lea    0x40(%r13),%rdi
    2e4b:	48 8b 75 b0          	mov    -0x50(%rbp),%rsi
    2e4f:	48 8d 15 8a 09 00 00 	lea    0x98a(%rip),%rdx        # 37e0 <external_thread>
    thread_data[x].buffers = &buffers[buffer_index];
    2e56:	49 89 80 f8 04 00 00 	mov    %rax,0x4f8(%r8)
    thread_data[x].thread_count = thread_count;
    2e5d:	48 8b 05 bc 3b 00 00 	mov    0x3bbc(%rip),%rax        # 6a20 <_IO_stdin_used+0xa20>
    thread_data[x].type = EXTERNAL;
    2e64:	49 8d 88 c0 04 00 00 	lea    0x4c0(%r8),%rcx
    thread_data[x].threads = thread_data;
    2e6b:	4d 89 80 d0 04 00 00 	mov    %r8,0x4d0(%r8)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2e72:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    thread_data[x].type = EXTERNAL;
    2e79:	41 c7 80 c4 04 00 00 03 00 00 00 	movl   $0x3,0x4c4(%r8)
    thread_data[x].running = 1;
    2e84:	41 c7 80 ec 04 00 00 01 00 00 00 	movl   $0x1,0x4ec(%r8)
    thread_data[x].task_count = 0;
    2e8f:	41 c7 80 e8 04 00 00 00 00 00 00 	movl   $0x0,0x4e8(%r8)
    thread_data[x].thread_count = thread_count;
    2e9a:	49 89 80 d8 04 00 00 	mov    %rax,0x4d8(%r8)
    thread_data[x].thread_index = x;
    2ea1:	41 c7 80 c0 04 00 00 08 00 00 00 	movl   $0x8,0x4c0(%r8)
    thread_data[x].type = EXTERNAL;
    2eac:	4c 89 45 b8          	mov    %r8,-0x48(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2eb0:	e8 cb f5 ff ff       	call   2480 <pthread_create@plt>
    2eb5:	48 8d 3d a8 34 00 00 	lea    0x34a8(%rip),%rdi        # 6364 <_IO_stdin_used+0x364>
    2ebc:	e8 2f f4 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    2ec1:	4c 8b 7d b8          	mov    -0x48(%rbp),%r15
    2ec5:	0f 1f 00             	nopl   (%rax)
    void * result; 
    pthread_join(thread[x], &result);
    2ec8:	4b 8b 7c f5 00       	mov    0x0(%r13,%r14,8),%rdi
    2ecd:	4c 89 e6             	mov    %r12,%rsi
    2ed0:	e8 3b f6 ff ff       	call   2510 <pthread_join@plt>
    2ed5:	44 89 f2             	mov    %r14d,%edx
    2ed8:	48 89 de             	mov    %rbx,%rsi
    2edb:	bf 01 00 00 00       	mov    $0x1,%edi
    2ee0:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2ee2:	49 83 c6 01          	add    $0x1,%r14
    2ee6:	e8 75 f5 ff ff       	call   2460 <__printf_chk@plt>
    2eeb:	49 83 fe 09          	cmp    $0x9,%r14
    2eef:	75 d7                	jne    2ec8 <main+0x8b8>
    2ef1:	4d 89 f8             	mov    %r15,%r8
  }
  long total = 0;
  long v = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
    2ef4:	45 31 e4             	xor    %r12d,%r12d
  long sends = 0;
    2ef7:	45 31 c9             	xor    %r9d,%r9d
  long total = 0;
    2efa:	45 31 ed             	xor    %r13d,%r13d
    2efd:	49 8d 80 b0 03 00 00 	lea    0x3b0(%r8),%rax
  long v = 0;
    2f04:	45 31 c0             	xor    %r8d,%r8d
    2f07:	4c 89 6d b8          	mov    %r13,-0x48(%rbp)
  long ingests = 0;
    2f0b:	31 c9                	xor    %ecx,%ecx
    2f0d:	48 89 45 98          	mov    %rax,-0x68(%rbp)
    2f11:	4d 8d 7f 20          	lea    0x20(%r15),%r15
  long received = 0;
    2f15:	31 db                	xor    %ebx,%ebx
    2f17:	49 89 ce             	mov    %rcx,%r14
    2f1a:	4c 89 45 b0          	mov    %r8,-0x50(%rbp)
    2f1e:	4c 89 4d a8          	mov    %r9,-0x58(%rbp)
    2f22:	4c 89 65 a0          	mov    %r12,-0x60(%rbp)
    2f26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  for (int x = 0 ; x < thread_count ; x++) {

    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2f30:	49 63 57 08          	movslq 0x8(%r15),%rdx
    2f34:	85 d2                	test   %edx,%edx
    2f36:	0f 8e cb 00 00 00    	jle    3007 <main+0x9f7>
    2f3c:	49 8b 07             	mov    (%r15),%rax
    2f3f:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
    2f43:	48 8b 4d b8          	mov    -0x48(%rbp),%rcx
    2f47:	48 8d 14 72          	lea    (%rdx,%rsi,2),%rdx
    2f4b:	4c 8b 45 b0          	mov    -0x50(%rbp),%r8
    2f4f:	4c 8b 4d a8          	mov    -0x58(%rbp),%r9
    2f53:	4c 8b 65 a0          	mov    -0x60(%rbp),%r12
    2f57:	48 8d 14 d0          	lea    (%rax,%rdx,8),%rdx
    2f5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      total += thread_data[x].tasks[n].n;
    2f60:	48 8b 70 10          	mov    0x10(%rax),%rsi
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2f64:	48 05 98 00 00 00    	add    $0x98,%rax
      total += thread_data[x].tasks[n].n;
    2f6a:	48 01 f1             	add    %rsi,%rcx
      v += thread_data[x].tasks[n].v;
    2f6d:	48 8b 70 80          	mov    -0x80(%rax),%rsi
    2f71:	49 01 f0             	add    %rsi,%r8
      ingests += thread_data[x].tasks[n].ingest_count;
    2f74:	48 8b 70 d0          	mov    -0x30(%rax),%rsi
    2f78:	49 01 f6             	add    %rsi,%r14
      sends += thread_data[x].tasks[n].sends;
    2f7b:	48 8b 70 e0          	mov    -0x20(%rax),%rsi
    2f7f:	49 01 f1             	add    %rsi,%r9
      for (int k = 0 ; k < thread_count ; k++) {
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2f82:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f86:	4c 03 66 10          	add    0x10(%rsi),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2f8a:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f8e:	48 03 5e 18          	add    0x18(%rsi),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2f92:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f96:	4c 03 66 30          	add    0x30(%rsi),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2f9a:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f9e:	48 03 5e 38          	add    0x38(%rsi),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2fa2:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2fa6:	4c 03 66 50          	add    0x50(%rsi),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2faa:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2fae:	48 03 5e 58          	add    0x58(%rsi),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2fb2:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2fb6:	4c 03 66 70          	add    0x70(%rsi),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2fba:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2fbe:	48 03 5e 78          	add    0x78(%rsi),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2fc2:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2fc6:	4c 03 a6 90 00 00 00 	add    0x90(%rsi),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2fcd:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2fd1:	48 03 9e 98 00 00 00 	add    0x98(%rsi),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2fd8:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2fdc:	4c 03 a6 b0 00 00 00 	add    0xb0(%rsi),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2fe3:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2fe7:	48 03 9e b8 00 00 00 	add    0xb8(%rsi),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2fee:	48 39 d0             	cmp    %rdx,%rax
    2ff1:	0f 85 69 ff ff ff    	jne    2f60 <main+0x950>
    2ff7:	48 89 4d b8          	mov    %rcx,-0x48(%rbp)
    2ffb:	4c 89 45 b0          	mov    %r8,-0x50(%rbp)
    2fff:	4c 89 4d a8          	mov    %r9,-0x58(%rbp)
    3003:	4c 89 65 a0          	mov    %r12,-0x60(%rbp)
      }
    }
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    3007:	45 31 ed             	xor    %r13d,%r13d
    300a:	49 83 7f 50 00       	cmpq   $0x0,0x50(%r15)
    300f:	0f 8e 7d 00 00 00    	jle    3092 <main+0xa82>
    3015:	4d 89 fc             	mov    %r15,%r12
    3018:	49 89 df             	mov    %rbx,%r15
    301b:	4c 89 eb             	mov    %r13,%rbx
    301e:	66 90                	xchg   %ax,%ax
      struct timespec start = thread_data[x].start[n];
    3020:	49 8b 7c 24 30       	mov    0x30(%r12),%rdi
    3025:	48 89 de             	mov    %rbx,%rsi
      struct timespec end = thread_data[x].end[n];
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    3028:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    3032:	48 83 c3 01          	add    $0x1,%rbx
    3036:	48 c1 e6 04          	shl    $0x4,%rsi
      struct timespec start = thread_data[x].start[n];
    303a:	48 01 f7             	add    %rsi,%rdi
      struct timespec end = thread_data[x].end[n];
    303d:	49 03 74 24 38       	add    0x38(%r12),%rsi
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3042:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    3046:	48 2b 57 08          	sub    0x8(%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    304a:	48 f7 e2             	mul    %rdx
    304d:	31 c0                	xor    %eax,%eax
    304f:	48 89 d1             	mov    %rdx,%rcx
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3052:	48 8b 16             	mov    (%rsi),%rdx
    3055:	48 8d 35 3a 33 00 00 	lea    0x333a(%rip),%rsi        # 6396 <_IO_stdin_used+0x396>
    305c:	48 2b 17             	sub    (%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    305f:	48 c1 e9 12          	shr    $0x12,%rcx
    3063:	bf 01 00 00 00       	mov    $0x1,%edi
    3068:	e8 f3 f3 ff ff       	call   2460 <__printf_chk@plt>
    306d:	49 8b 54 24 40       	mov    0x40(%r12),%rdx
    3072:	48 8d 35 3b 33 00 00 	lea    0x333b(%rip),%rsi        # 63b4 <_IO_stdin_used+0x3b4>
    3079:	31 c0                	xor    %eax,%eax
    307b:	bf 01 00 00 00       	mov    $0x1,%edi
    3080:	e8 db f3 ff ff       	call   2460 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    3085:	49 39 5c 24 50       	cmp    %rbx,0x50(%r12)
    308a:	7f 94                	jg     3020 <main+0xa10>
    308c:	4c 89 fb             	mov    %r15,%rbx
    308f:	4d 89 e7             	mov    %r12,%r15
      printf("%ld iterations\n", thread_data[x].iteration_count);
    }
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3092:	45 31 ed             	xor    %r13d,%r13d
    3095:	49 83 7f 68 00       	cmpq   $0x0,0x68(%r15)
    309a:	0f 8e 99 00 00 00    	jle    3139 <main+0xb29>
    30a0:	48 89 d8             	mov    %rbx,%rax
    30a3:	4d 89 ec             	mov    %r13,%r12
    30a6:	4c 89 fb             	mov    %r15,%rbx
    30a9:	49 89 c7             	mov    %rax,%r15
    30ac:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    30b0:	48 8b 43 58          	mov    0x58(%rbx),%rax
    30b4:	4b 8d 14 a4          	lea    (%r12,%r12,4),%rdx
    30b8:	48 83 ec 08          	sub    $0x8,%rsp
    30bc:	48 8d 35 75 35 00 00 	lea    0x3575(%rip),%rsi        # 6638 <_IO_stdin_used+0x638>
    30c3:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    30c8:	49 83 c4 01          	add    $0x1,%r12
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    30cc:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    30d0:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    30da:	4c 8b 69 18          	mov    0x18(%rcx),%r13
    30de:	4c 2b 69 08          	sub    0x8(%rcx),%r13
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    30e2:	49 f7 e5             	mul    %r13
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    30e5:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    30e9:	4c 2b 01             	sub    (%rcx),%r8
    30ec:	31 c0                	xor    %eax,%eax
    30ee:	8b 49 20             	mov    0x20(%rcx),%ecx
    30f1:	41 55                	push   %r13
    30f3:	48 c1 ea 12          	shr    $0x12,%rdx
    30f7:	49 89 d1             	mov    %rdx,%r9
    30fa:	ba 06 00 00 00       	mov    $0x6,%edx
    30ff:	e8 5c f3 ff ff       	call   2460 <__printf_chk@plt>
    3104:	48 8d 35 c5 32 00 00 	lea    0x32c5(%rip),%rsi        # 63d0 <_IO_stdin_used+0x3d0>
    310b:	bf 01 00 00 00       	mov    $0x1,%edi
      printf("%ldns per thread\n", (seconds2 / thread_count));
    3110:	48 b8 ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%rax
    311a:	49 f7 e5             	mul    %r13
    311d:	31 c0                	xor    %eax,%eax
    311f:	48 c1 ea 02          	shr    $0x2,%rdx
    3123:	e8 38 f3 ff ff       	call   2460 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3128:	58                   	pop    %rax
    3129:	5a                   	pop    %rdx
    312a:	4c 39 63 68          	cmp    %r12,0x68(%rbx)
    312e:	7f 80                	jg     30b0 <main+0xaa0>
    3130:	4c 89 f8             	mov    %r15,%rax
    3133:	49 89 df             	mov    %rbx,%r15
    3136:	48 89 c3             	mov    %rax,%rbx
    3139:	49 8b 57 70          	mov    0x70(%r15),%rdx
    313d:	48 8d 35 80 32 00 00 	lea    0x3280(%rip),%rsi        # 63c4 <_IO_stdin_used+0x3c4>
    3144:	bf 01 00 00 00       	mov    $0x1,%edi
    3149:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < thread_count ; x++) {
    314b:	49 81 c7 98 00 00 00 	add    $0x98,%r15
    3152:	e8 09 f3 ff ff       	call   2460 <__printf_chk@plt>
    3157:	48 8b 45 98          	mov    -0x68(%rbp),%rax
    315b:	49 39 c7             	cmp    %rax,%r15
    315e:	0f 85 cc fd ff ff    	jne    2f30 <main+0x920>
    3164:	4c 8b 6d b8          	mov    -0x48(%rbp),%r13
    3168:	4c 8b 45 b0          	mov    -0x50(%rbp),%r8
    316c:	bf 01 00 00 00       	mov    $0x1,%edi
    3171:	31 c0                	xor    %eax,%eax
    3173:	48 8d 35 68 32 00 00 	lea    0x3268(%rip),%rsi        # 63e2 <_IO_stdin_used+0x3e2>
    317a:	4c 8b 65 a0          	mov    -0x60(%rbp),%r12
    317e:	4c 89 75 b0          	mov    %r14,-0x50(%rbp)
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total Protected %ld\n", protected_state->protected);
  printf("Total V %ld\n", v);
  printf("\n");
  printf("Total Protected per second %ld\n", protected_state->protected / DURATION);
    3182:	49 be 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%r14
    318c:	4c 89 ea             	mov    %r13,%rdx
    318f:	4c 89 45 b8          	mov    %r8,-0x48(%rbp)
    3193:	e8 c8 f2 ff ff       	call   2460 <__printf_chk@plt>
    3198:	bf 0a 00 00 00       	mov    $0xa,%edi
    319d:	e8 3e f1 ff ff       	call   22e0 <putchar@plt>
    31a2:	4c 8b 7d 80          	mov    -0x80(%rbp),%r15
    31a6:	bf 01 00 00 00       	mov    $0x1,%edi
    31ab:	31 c0                	xor    %eax,%eax
    31ad:	48 8d 35 42 32 00 00 	lea    0x3242(%rip),%rsi        # 63f6 <_IO_stdin_used+0x3f6>
    31b4:	49 8b 17             	mov    (%r15),%rdx
    31b7:	e8 a4 f2 ff ff       	call   2460 <__printf_chk@plt>
    31bc:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
    31c0:	bf 01 00 00 00       	mov    $0x1,%edi
    31c5:	31 c0                	xor    %eax,%eax
    31c7:	48 8d 35 3d 32 00 00 	lea    0x323d(%rip),%rsi        # 640b <_IO_stdin_used+0x40b>
    31ce:	e8 8d f2 ff ff       	call   2460 <__printf_chk@plt>
    31d3:	bf 0a 00 00 00       	mov    $0xa,%edi
    31d8:	e8 03 f1 ff ff       	call   22e0 <putchar@plt>
    31dd:	49 8b 37             	mov    (%r15),%rsi
    31e0:	bf 01 00 00 00       	mov    $0x1,%edi
    31e5:	48 89 f0             	mov    %rsi,%rax
    31e8:	49 f7 ee             	imul   %r14
    31eb:	31 c0                	xor    %eax,%eax
    31ed:	48 01 f2             	add    %rsi,%rdx
    31f0:	48 c1 fe 3f          	sar    $0x3f,%rsi
    31f4:	48 c1 fa 04          	sar    $0x4,%rdx
    31f8:	48 29 f2             	sub    %rsi,%rdx
    31fb:	48 8d 35 6e 34 00 00 	lea    0x346e(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    3202:	e8 59 f2 ff ff       	call   2460 <__printf_chk@plt>
    3207:	49 8b 57 08          	mov    0x8(%r15),%rdx
    320b:	bf 01 00 00 00       	mov    $0x1,%edi
    3210:	31 c0                	xor    %eax,%eax
    3212:	48 8d 35 77 34 00 00 	lea    0x3477(%rip),%rsi        # 6690 <_IO_stdin_used+0x690>
    3219:	e8 42 f2 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    321e:	48 8b 4d b0          	mov    -0x50(%rbp),%rcx
    3222:	bf 01 00 00 00       	mov    $0x1,%edi
    3227:	48 8d 35 8a 34 00 00 	lea    0x348a(%rip),%rsi        # 66b8 <_IO_stdin_used+0x6b8>
    322e:	48 89 c8             	mov    %rcx,%rax
    3231:	49 f7 ee             	imul   %r14
    3234:	31 c0                	xor    %eax,%eax
    3236:	48 01 ca             	add    %rcx,%rdx
    3239:	48 c1 f9 3f          	sar    $0x3f,%rcx
    323d:	48 c1 fa 04          	sar    $0x4,%rdx
    3241:	48 29 ca             	sub    %rcx,%rdx
    3244:	e8 17 f2 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3249:	4c 8b 4d a8          	mov    -0x58(%rbp),%r9
    324d:	bf 01 00 00 00       	mov    $0x1,%edi
    3252:	48 8d 35 8f 34 00 00 	lea    0x348f(%rip),%rsi        # 66e8 <_IO_stdin_used+0x6e8>
    3259:	4c 89 c8             	mov    %r9,%rax
    325c:	49 f7 ee             	imul   %r14
    325f:	31 c0                	xor    %eax,%eax
    3261:	4c 01 ca             	add    %r9,%rdx
    3264:	49 c1 f9 3f          	sar    $0x3f,%r9
    3268:	48 c1 fa 04          	sar    $0x4,%rdx
    326c:	4c 29 ca             	sub    %r9,%rdx
    326f:	e8 ec f1 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3274:	4c 89 e8             	mov    %r13,%rax
    3277:	bf 01 00 00 00       	mov    $0x1,%edi
    327c:	48 8d 35 95 34 00 00 	lea    0x3495(%rip),%rsi        # 6718 <_IO_stdin_used+0x718>
    3283:	49 f7 ee             	imul   %r14
    3286:	4c 01 ea             	add    %r13,%rdx
    3289:	49 c1 fd 3f          	sar    $0x3f,%r13
    328d:	31 c0                	xor    %eax,%eax
    328f:	48 c1 fa 04          	sar    $0x4,%rdx
    3293:	4c 29 ea             	sub    %r13,%rdx
    3296:	e8 c5 f1 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    329b:	4c 89 e0             	mov    %r12,%rax
    329e:	bf 01 00 00 00       	mov    $0x1,%edi
    32a3:	48 8d 35 6e 31 00 00 	lea    0x316e(%rip),%rsi        # 6418 <_IO_stdin_used+0x418>
    32aa:	49 f7 ee             	imul   %r14
    32ad:	31 c0                	xor    %eax,%eax
    32af:	4c 01 e2             	add    %r12,%rdx
    32b2:	49 c1 fc 3f          	sar    $0x3f,%r12
    32b6:	48 c1 fa 04          	sar    $0x4,%rdx
    32ba:	4c 29 e2             	sub    %r12,%rdx
    32bd:	e8 9e f1 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    32c2:	48 89 d8             	mov    %rbx,%rax
    32c5:	bf 01 00 00 00       	mov    $0x1,%edi
    32ca:	48 8d 35 58 31 00 00 	lea    0x3158(%rip),%rsi        # 6429 <_IO_stdin_used+0x429>
    32d1:	49 f7 ee             	imul   %r14
    32d4:	31 c0                	xor    %eax,%eax
    32d6:	48 01 da             	add    %rbx,%rdx
    32d9:	48 c1 fb 3f          	sar    $0x3f,%rbx
    32dd:	48 c1 fa 04          	sar    $0x4,%rdx
    32e1:	48 29 da             	sub    %rbx,%rdx
    32e4:	e8 77 f1 ff ff       	call   2460 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    32e9:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    32ed:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    32f6:	75 49                	jne    3341 <main+0xd31>
    32f8:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
    32fc:	31 c0                	xor    %eax,%eax
    32fe:	5b                   	pop    %rbx
    32ff:	41 5c                	pop    %r12
    3301:	41 5d                	pop    %r13
    3303:	41 5e                	pop    %r14
    3305:	41 5f                	pop    %r15
    3307:	5d                   	pop    %rbp
    3308:	c3                   	ret
    3309:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          thread_data[x].tasks[y].run = barriered_work; 
    3310:	48 8d 05 69 21 00 00 	lea    0x2169(%rip),%rax        # 5480 <barriered_work>
    3317:	41 bc 03 00 00 00    	mov    $0x3,%r12d
    331d:	49 89 46 20          	mov    %rax,0x20(%r14)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3321:	e9 ec f7 ff ff       	jmp    2b12 <main+0x502>
    3326:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            thread_data[x].tasks[y].protected = do_protected_write; 
    3330:	48 8d 05 69 01 00 00 	lea    0x169(%rip),%rax        # 34a0 <do_protected_write>
    3337:	49 89 44 24 28       	mov    %rax,0x28(%r12)
    333c:	e9 ee f5 ff ff       	jmp    292f <main+0x31f>
}
    3341:	e8 ea ef ff ff       	call   2330 <__stack_chk_fail@plt>
    3346:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003350 <_start>:
    3350:	f3 0f 1e fa          	endbr64
    3354:	31 ed                	xor    %ebp,%ebp
    3356:	49 89 d1             	mov    %rdx,%r9
    3359:	5e                   	pop    %rsi
    335a:	48 89 e2             	mov    %rsp,%rdx
    335d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3361:	50                   	push   %rax
    3362:	54                   	push   %rsp
    3363:	45 31 c0             	xor    %r8d,%r8d
    3366:	31 c9                	xor    %ecx,%ecx
    3368:	48 8d 3d a1 f2 ff ff 	lea    -0xd5f(%rip),%rdi        # 2610 <main>
    336f:	ff 15 5b 5c 00 00    	call   *0x5c5b(%rip)        # 8fd0 <__libc_start_main@GLIBC_2.34>
    3375:	f4                   	hlt
    3376:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003380 <__gmon_start__>:
    3380:	f3 0f 1e fa          	endbr64
    3384:	8b 05 9e 5c 00 00    	mov    0x5c9e(%rip),%eax        # 9028 <called.0>
    338a:	85 c0                	test   %eax,%eax
    338c:	74 02                	je     3390 <__gmon_start__+0x10>
    338e:	c3                   	ret
    338f:	90                   	nop
    3390:	48 83 ec 08          	sub    $0x8,%rsp
    3394:	48 8d 35 02 29 00 00 	lea    0x2902(%rip),%rsi        # 5c9d <etext>
    339b:	48 8d 3d 5e cc ff ff 	lea    -0x33a2(%rip),%rdi        # 0 <__executable_start>
    33a2:	c7 05 7c 5c 00 00 01 00 00 00 	movl   $0x1,0x5c7c(%rip)        # 9028 <called.0>
    33ac:	e8 0f f0 ff ff       	call   23c0 <__monstartup@plt>
    33b1:	48 8b 3d 28 5c 00 00 	mov    0x5c28(%rip),%rdi        # 8fe0 <_mcleanup@GLIBC_2.2.5>
    33b8:	48 83 c4 08          	add    $0x8,%rsp
    33bc:	e9 9f 28 00 00       	jmp    5c60 <atexit>
    33c1:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    33cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000033d0 <_dl_relocate_static_pie>:
    33d0:	f3 0f 1e fa          	endbr64
    33d4:	c3                   	ret
    33d5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    33df:	90                   	nop

00000000000033e0 <deregister_tm_clones>:
    33e0:	48 8d 3d 39 5c 00 00 	lea    0x5c39(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    33e7:	48 8d 05 32 5c 00 00 	lea    0x5c32(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    33ee:	48 39 f8             	cmp    %rdi,%rax
    33f1:	74 15                	je     3408 <deregister_tm_clones+0x28>
    33f3:	48 8b 05 de 5b 00 00 	mov    0x5bde(%rip),%rax        # 8fd8 <_ITM_deregisterTMCloneTable@Base>
    33fa:	48 85 c0             	test   %rax,%rax
    33fd:	74 09                	je     3408 <deregister_tm_clones+0x28>
    33ff:	ff e0                	jmp    *%rax
    3401:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3408:	c3                   	ret
    3409:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003410 <register_tm_clones>:
    3410:	48 8d 3d 09 5c 00 00 	lea    0x5c09(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3417:	48 8d 35 02 5c 00 00 	lea    0x5c02(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    341e:	48 29 fe             	sub    %rdi,%rsi
    3421:	48 89 f0             	mov    %rsi,%rax
    3424:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3428:	48 c1 f8 03          	sar    $0x3,%rax
    342c:	48 01 c6             	add    %rax,%rsi
    342f:	48 d1 fe             	sar    %rsi
    3432:	74 14                	je     3448 <register_tm_clones+0x38>
    3434:	48 8b 05 b5 5b 00 00 	mov    0x5bb5(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    343b:	48 85 c0             	test   %rax,%rax
    343e:	74 08                	je     3448 <register_tm_clones+0x38>
    3440:	ff e0                	jmp    *%rax
    3442:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3448:	c3                   	ret
    3449:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003450 <__do_global_dtors_aux>:
    3450:	f3 0f 1e fa          	endbr64
    3454:	80 3d d1 5b 00 00 00 	cmpb   $0x0,0x5bd1(%rip)        # 902c <completed.0>
    345b:	75 2b                	jne    3488 <__do_global_dtors_aux+0x38>
    345d:	55                   	push   %rbp
    345e:	48 83 3d 92 5b 00 00 00 	cmpq   $0x0,0x5b92(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    3466:	48 89 e5             	mov    %rsp,%rbp
    3469:	74 0c                	je     3477 <__do_global_dtors_aux+0x27>
    346b:	48 8b 3d 96 5b 00 00 	mov    0x5b96(%rip),%rdi        # 9008 <__dso_handle>
    3472:	e8 49 ee ff ff       	call   22c0 <__cxa_finalize@plt>
    3477:	e8 64 ff ff ff       	call   33e0 <deregister_tm_clones>
    347c:	c6 05 a9 5b 00 00 01 	movb   $0x1,0x5ba9(%rip)        # 902c <completed.0>
    3483:	5d                   	pop    %rbp
    3484:	c3                   	ret
    3485:	0f 1f 00             	nopl   (%rax)
    3488:	c3                   	ret
    3489:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003490 <frame_dummy>:
    3490:	f3 0f 1e fa          	endbr64
    3494:	e9 77 ff ff ff       	jmp    3410 <register_tm_clones>
    3499:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000034a0 <do_protected_write>:
int do_protected_write(volatile struct BarrierTask *data) {
    34a0:	f3 0f 1e fa          	endbr64
    34a4:	55                   	push   %rbp
    34a5:	48 89 e5             	mov    %rsp,%rbp
    34a8:	ff 15 3a 5b 00 00    	call   *0x5b3a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  struct ProtectedState *protected = data->thread->protected_state;
    34ae:	48 8b 47 30          	mov    0x30(%rdi),%rax
  data->v++; // thread local
    34b2:	48 8b 57 18          	mov    0x18(%rdi),%rdx
  struct ProtectedState *protected = data->thread->protected_state;
    34b6:	48 8b 40 30          	mov    0x30(%rax),%rax
  data->v++; // thread local
    34ba:	48 83 c2 01          	add    $0x1,%rdx
  if (protected->balance > 0) {
    34be:	48 8b 48 08          	mov    0x8(%rax),%rcx
  data->v++; // thread local
    34c2:	48 89 57 18          	mov    %rdx,0x18(%rdi)
  protected->protected++; // shared between all threads
    34c6:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    34ca:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    34d1:	48 85 c9             	test   %rcx,%rcx
    34d4:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    34db:	48 0f 4f d6          	cmovg  %rsi,%rdx
    34df:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    34e3:	31 c0                	xor    %eax,%eax
    34e5:	5d                   	pop    %rbp
    34e6:	c3                   	ret
    34e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000034f0 <barriered_reset>:
int barriered_reset(volatile struct BarrierTask *data) {
    34f0:	f3 0f 1e fa          	endbr64
    34f4:	55                   	push   %rbp
    34f5:	48 89 e5             	mov    %rsp,%rbp
    34f8:	ff 15 ea 5a 00 00    	call   *0x5aea(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    for (int x = 0 ; x < data->task_count ; x++) {
    34fe:	8b 47 44             	mov    0x44(%rdi),%eax
int barriered_reset(volatile struct BarrierTask *data) {
    3501:	48 89 fa             	mov    %rdi,%rdx
    for (int x = 0 ; x < data->task_count ; x++) {
    3504:	85 c0                	test   %eax,%eax
    3506:	7e 53                	jle    355b <barriered_reset+0x6b>
    3508:	31 c9                	xor    %ecx,%ecx
    350a:	31 f6                	xor    %esi,%esi
    350c:	0f 1f 40 00          	nopl   0x0(%rax)
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    3510:	48 8b 7a 30          	mov    0x30(%rdx),%rdi
    3514:	48 63 42 38          	movslq 0x38(%rdx),%rax
    for (int x = 0 ; x < data->task_count ; x++) {
    3518:	83 c6 01             	add    $0x1,%esi
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    351b:	4c 8d 04 c0          	lea    (%rax,%rax,8),%r8
    351f:	4a 8d 04 40          	lea    (%rax,%r8,2),%rax
    3523:	4c 8b 47 10          	mov    0x10(%rdi),%r8
    3527:	49 8d 04 c0          	lea    (%r8,%rax,8),%rax
    352b:	48 8b 78 20          	mov    0x20(%rax),%rdi
    352f:	48 01 cf             	add    %rcx,%rdi
    3532:	8b 47 08             	mov    0x8(%rdi),%eax
    3535:	83 c0 01             	add    $0x1,%eax
    3538:	89 47 08             	mov    %eax,0x8(%rdi)
      data->thread->tasks[x].available = 1; 
    353b:	48 8b 42 30          	mov    0x30(%rdx),%rax
    353f:	48 8b 78 20          	mov    0x20(%rax),%rdi
    3543:	48 01 cf             	add    %rcx,%rdi
    for (int x = 0 ; x < data->task_count ; x++) {
    3546:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
      data->thread->tasks[x].available = 1; 
    354d:	c7 47 40 01 00 00 00 	movl   $0x1,0x40(%rdi)
    for (int x = 0 ; x < data->task_count ; x++) {
    3554:	8b 42 44             	mov    0x44(%rdx),%eax
    3557:	39 f0                	cmp    %esi,%eax
    3559:	7f b5                	jg     3510 <barriered_reset+0x20>
  asm volatile ("mfence" ::: "memory");
    355b:	0f ae f0             	mfence
}
    355e:	31 c0                	xor    %eax,%eax
    3560:	5d                   	pop    %rbp
    3561:	c3                   	ret
    3562:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    356d:	0f 1f 00             	nopl   (%rax)

0000000000003570 <barriered_thread>:
void* barriered_thread(void *arg) {
    3570:	f3 0f 1e fa          	endbr64
    3574:	55                   	push   %rbp
    3575:	48 89 e5             	mov    %rsp,%rbp
    3578:	41 56                	push   %r14
    357a:	41 55                	push   %r13
    357c:	41 54                	push   %r12
    357e:	53                   	push   %rbx
    357f:	ff 15 63 5a 00 00    	call   *0x5a63(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  while (data->running == 1) {
    3585:	8b 47 2c             	mov    0x2c(%rdi),%eax
void* barriered_thread(void *arg) {
    3588:	49 89 fd             	mov    %rdi,%r13
  while (data->running == 1) {
    358b:	83 f8 01             	cmp    $0x1,%eax
    358e:	0f 85 79 01 00 00    	jne    370d <barriered_thread+0x19d>
    if (t >= data->task_count) {
    3594:	44 8b 57 28          	mov    0x28(%rdi),%r10d
  int waiting = 0;
    3598:	45 31 f6             	xor    %r14d,%r14d
  int t = 0;
    359b:	31 db                	xor    %ebx,%ebx
    359d:	0f 1f 00             	nopl   (%rax)
    if (t >= data->task_count) {
    35a0:	44 39 d3             	cmp    %r10d,%ebx
    35a3:	0f 8d 7f 01 00 00    	jge    3728 <barriered_thread+0x1b8>
    35a9:	48 63 c3             	movslq %ebx,%rax
    35ac:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    35b0:	4c 8d 24 50          	lea    (%rax,%rdx,2),%r12
    35b4:	49 c1 e4 03          	shl    $0x3,%r12
    35b8:	eb 19                	jmp    35d3 <barriered_thread+0x63>
    35ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (; t < data->task_count; t++) {
    35c0:	83 c3 01             	add    $0x1,%ebx
    35c3:	49 81 c4 98 00 00 00 	add    $0x98,%r12
    35ca:	44 39 d3             	cmp    %r10d,%ebx
    35cd:	0f 8d 2d 01 00 00    	jge    3700 <barriered_thread+0x190>
      if (data->tasks[t].available == 1) {
    35d3:	49 8b 55 20          	mov    0x20(%r13),%rdx
    35d7:	4c 01 e2             	add    %r12,%rdx
    35da:	8b 42 40             	mov    0x40(%rdx),%eax
    35dd:	83 f8 01             	cmp    $0x1,%eax
    35e0:	75 de                	jne    35c0 <barriered_thread+0x50>
        if (t > 0) {
    35e2:	85 db                	test   %ebx,%ebx
    35e4:	0f 8e 56 01 00 00    	jle    3740 <barriered_thread+0x1d0>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    35ea:	45 8b 5d 18          	mov    0x18(%r13),%r11d
          previous = t - 1;
    35ee:	8d 43 ff             	lea    -0x1(%rbx),%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    35f1:	45 85 db             	test   %r11d,%r11d
    35f4:	7e 6d                	jle    3663 <barriered_thread+0xf3>
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    35f6:	48 98                	cltq
    35f8:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    35fc:	4c 8d 04 48          	lea    (%rax,%rcx,2),%r8
    3600:	49 63 cb             	movslq %r11d,%rcx
    3603:	49 8b 45 10          	mov    0x10(%r13),%rax
    3607:	48 8d 34 c9          	lea    (%rcx,%rcx,8),%rsi
    360b:	49 c1 e0 03          	shl    $0x3,%r8
    360f:	48 8d 0c 71          	lea    (%rcx,%rsi,2),%rcx
    3613:	4c 8d 0c c8          	lea    (%rax,%rcx,8),%r9
        int arrived = 0; 
    3617:	31 c9                	xor    %ecx,%ecx
    3619:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    3620:	48 8b 70 20          	mov    0x20(%rax),%rsi
    3624:	4c 01 c6             	add    %r8,%rsi
    3627:	8b 76 08             	mov    0x8(%rsi),%esi
    362a:	8b 7a 08             	mov    0x8(%rdx),%edi
            arrived++;
    362d:	39 f7                	cmp    %esi,%edi
    362f:	40 0f 94 c6          	sete   %sil
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3633:	48 05 98 00 00 00    	add    $0x98,%rax
            arrived++;
    3639:	40 0f b6 f6          	movzbl %sil,%esi
    363d:	01 f1                	add    %esi,%ecx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    363f:	4c 39 c8             	cmp    %r9,%rax
    3642:	75 dc                	jne    3620 <barriered_thread+0xb0>
        if (arrived == 0 || arrived == data->thread_count) {
    3644:	44 39 d9             	cmp    %r11d,%ecx
    3647:	74 08                	je     3651 <barriered_thread+0xe1>
    3649:	85 c9                	test   %ecx,%ecx
    364b:	0f 85 af 00 00 00    	jne    3700 <barriered_thread+0x190>
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    3651:	85 db                	test   %ebx,%ebx
    3653:	75 0e                	jne    3663 <barriered_thread+0xf3>
    3655:	49 8b 75 68          	mov    0x68(%r13),%rsi
    3659:	49 3b 75 70          	cmp    0x70(%r13),%rsi
    365d:	0f 8c 65 01 00 00    	jl     37c8 <barriered_thread+0x258>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3663:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    366a:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    366e:	49 8b 45 78          	mov    0x78(%r13),%rax
          if (waiting == 1) {
    3672:	41 83 fe 01          	cmp    $0x1,%r14d
    3676:	0f 84 14 01 00 00    	je     3790 <barriered_thread+0x220>
            data->task_snapshot[data->task_timestamp_count].task = t;
    367c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3680:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3685:	41 be 01 00 00 00    	mov    $0x1,%r14d
            data->task_snapshot[data->task_timestamp_count].task = t;
    368b:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    368e:	e8 7d ec ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3693:	49 8b 45 20          	mov    0x20(%r13),%rax
    3697:	4c 01 e0             	add    %r12,%rax
    369a:	c7 40 40 00 00 00 00 	movl   $0x0,0x40(%rax)
          data->tasks[t].run(&data->threads[data->thread_index].tasks[t]);
    36a1:	48 8b 50 20          	mov    0x20(%rax),%rdx
    36a5:	49 63 45 00          	movslq 0x0(%r13),%rax
    36a9:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    36ad:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    36b1:	49 8b 4d 10          	mov    0x10(%r13),%rcx
    36b5:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    36b9:	48 8b 78 20          	mov    0x20(%rax),%rdi
    36bd:	4c 01 e7             	add    %r12,%rdi
    36c0:	ff d2                	call   *%rdx
          data->tasks[t].arrived++;
    36c2:	49 8b 55 20          	mov    0x20(%r13),%rdx
    36c6:	4c 01 e2             	add    %r12,%rdx
    36c9:	8b 42 08             	mov    0x8(%rdx),%eax
    36cc:	83 c0 01             	add    $0x1,%eax
    36cf:	89 42 08             	mov    %eax,0x8(%rdx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    36d2:	41 8b 45 28          	mov    0x28(%r13),%eax
          data->iteration_count++;
    36d6:	49 83 45 60 01       	addq   $0x1,0x60(%r13)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    36db:	83 e8 01             	sub    $0x1,%eax
    36de:	39 d8                	cmp    %ebx,%eax
    36e0:	74 7e                	je     3760 <barriered_thread+0x1f0>
          asm volatile ("mfence" ::: "memory");
    36e2:	0f ae f0             	mfence
    for (; t < data->task_count; t++) {
    36e5:	45 8b 55 28          	mov    0x28(%r13),%r10d
    36e9:	83 c3 01             	add    $0x1,%ebx
    36ec:	49 81 c4 98 00 00 00 	add    $0x98,%r12
    36f3:	44 39 d3             	cmp    %r10d,%ebx
    36f6:	0f 8c d7 fe ff ff    	jl     35d3 <barriered_thread+0x63>
    36fc:	0f 1f 40 00          	nopl   0x0(%rax)
  while (data->running == 1) {
    3700:	41 8b 45 2c          	mov    0x2c(%r13),%eax
    3704:	83 f8 01             	cmp    $0x1,%eax
    3707:	0f 84 93 fe ff ff    	je     35a0 <barriered_thread+0x30>
}
    370d:	5b                   	pop    %rbx
    370e:	31 c0                	xor    %eax,%eax
    3710:	41 5c                	pop    %r12
    3712:	41 5d                	pop    %r13
    3714:	41 5e                	pop    %r14
    3716:	5d                   	pop    %rbp
    3717:	c3                   	ret
  while (data->running == 1) {
    3718:	41 8b 45 2c          	mov    0x2c(%r13),%eax
    371c:	83 f8 01             	cmp    $0x1,%eax
    371f:	75 ec                	jne    370d <barriered_thread+0x19d>
    3721:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->cycles++;
    3728:	49 83 85 90 00 00 00 01 	addq   $0x1,0x90(%r13)
    for (; t < data->task_count; t++) {
    3730:	45 85 d2             	test   %r10d,%r10d
    3733:	7e e3                	jle    3718 <barriered_thread+0x1a8>
    3735:	31 db                	xor    %ebx,%ebx
    3737:	e9 6d fe ff ff       	jmp    35a9 <barriered_thread+0x39>
    373c:	0f 1f 40 00          	nopl   0x0(%rax)
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3740:	45 8b 5d 18          	mov    0x18(%r13),%r11d
          previous = data->task_count - 1;
    3744:	41 8d 42 ff          	lea    -0x1(%r10),%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3748:	45 85 db             	test   %r11d,%r11d
    374b:	0f 8f a5 fe ff ff    	jg     35f6 <barriered_thread+0x86>
    3751:	e9 fb fe ff ff       	jmp    3651 <barriered_thread+0xe1>
    3756:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3760:	49 8b 75 68          	mov    0x68(%r13),%rsi
    3764:	49 3b 75 70          	cmp    0x70(%r13),%rsi
    3768:	0f 8d 74 ff ff ff    	jge    36e2 <barriered_thread+0x172>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    376e:	48 c1 e6 04          	shl    $0x4,%rsi
    3772:	bf 04 00 00 00       	mov    $0x4,%edi
    3777:	49 03 75 58          	add    0x58(%r13),%rsi
    377b:	e8 90 eb ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3780:	49 83 45 68 01       	addq   $0x1,0x68(%r13)
    3785:	e9 58 ff ff ff       	jmp    36e2 <barriered_thread+0x172>
    378a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3790:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3795:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 0;
    379a:	45 31 f6             	xor    %r14d,%r14d
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    379d:	e8 6e eb ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    37a2:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    37a9:	48 83 c0 01          	add    $0x1,%rax
    37ad:	48 99                	cqto
    37af:	49 f7 bd 88 00 00 00 	idivq  0x88(%r13)
    37b6:	49 89 95 80 00 00 00 	mov    %rdx,0x80(%r13)
          if (waiting == 3) {
    37bd:	e9 d1 fe ff ff       	jmp    3693 <barriered_thread+0x123>
    37c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    37c8:	48 c1 e6 04          	shl    $0x4,%rsi
    37cc:	bf 04 00 00 00       	mov    $0x4,%edi
    37d1:	49 03 75 50          	add    0x50(%r13),%rsi
    37d5:	e8 36 eb ff ff       	call   2310 <clock_gettime@plt>
    37da:	e9 84 fe ff ff       	jmp    3663 <barriered_thread+0xf3>
    37df:	90                   	nop

00000000000037e0 <external_thread>:
void * external_thread(void *arg) {
    37e0:	f3 0f 1e fa          	endbr64
    37e4:	55                   	push   %rbp
    37e5:	48 89 e5             	mov    %rsp,%rbp
    37e8:	41 56                	push   %r14
    37ea:	41 55                	push   %r13
    37ec:	41 54                	push   %r12
    37ee:	53                   	push   %rbx
    37ef:	48 83 ec 30          	sub    $0x30,%rsp
    37f3:	ff 15 ef 57 00 00    	call   *0x57ef(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  struct timespec req = {
    37f9:	66 0f 6f 05 2f 31 00 00 	movdqa 0x312f(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
void * external_thread(void *arg) {
    3801:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    380a:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    380e:	31 c0                	xor    %eax,%eax
    3810:	49 89 fe             	mov    %rdi,%r14
  struct timespec req = {
    3813:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
  while (data->running == 1) {
    3817:	8b 47 2c             	mov    0x2c(%rdi),%eax
    381a:	83 f8 01             	cmp    $0x1,%eax
    381d:	75 5f                	jne    387e <external_thread+0x9e>
    381f:	4c 8d 65 c0          	lea    -0x40(%rbp),%r12
    3823:	48 8d 5d b0          	lea    -0x50(%rbp),%rbx
        data->buffers->buffer[x].data = "Hello world";
    3827:	4c 8d 2d d6 27 00 00 	lea    0x27d6(%rip),%r13        # 6004 <_IO_stdin_used+0x4>
    382e:	66 90                	xchg   %ax,%ax
    nanosleep(&req , &rem);
    3830:	4c 89 e6             	mov    %r12,%rsi
    3833:	48 89 df             	mov    %rbx,%rdi
    3836:	e8 15 eb ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    383b:	49 8b 46 38          	mov    0x38(%r14),%rax
    383f:	48 63 08             	movslq (%rax),%rcx
    3842:	85 c9                	test   %ecx,%ecx
    3844:	7e 2c                	jle    3872 <external_thread+0x92>
    3846:	48 8b 40 08          	mov    0x8(%rax),%rax
    384a:	48 c1 e1 04          	shl    $0x4,%rcx
    384e:	48 01 c1             	add    %rax,%rcx
    3851:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    3858:	8b 50 08             	mov    0x8(%rax),%edx
    385b:	85 d2                	test   %edx,%edx
    385d:	75 0a                	jne    3869 <external_thread+0x89>
        data->buffers->buffer[x].data = "Hello world";
    385f:	4c 89 28             	mov    %r13,(%rax)
        data->buffers->buffer[x].available = 1;
    3862:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3869:	48 83 c0 10          	add    $0x10,%rax
    386d:	48 39 c1             	cmp    %rax,%rcx
    3870:	75 e6                	jne    3858 <external_thread+0x78>
    asm volatile ("mfence" ::: "memory");
    3872:	0f ae f0             	mfence
  while (data->running == 1) {
    3875:	41 8b 46 2c          	mov    0x2c(%r14),%eax
    3879:	83 f8 01             	cmp    $0x1,%eax
    387c:	74 b2                	je     3830 <external_thread+0x50>
}
    387e:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    3882:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    388b:	75 0f                	jne    389c <external_thread+0xbc>
    388d:	48 83 c4 30          	add    $0x30,%rsp
    3891:	31 c0                	xor    %eax,%eax
    3893:	5b                   	pop    %rbx
    3894:	41 5c                	pop    %r12
    3896:	41 5d                	pop    %r13
    3898:	41 5e                	pop    %r14
    389a:	5d                   	pop    %rbp
    389b:	c3                   	ret
    389c:	e8 8f ea ff ff       	call   2330 <__stack_chk_fail@plt>
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
    38c5:	ff 15 1d 57 00 00    	call   *0x571d(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    38cb:	48 8d 35 3e 27 00 00 	lea    0x273e(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    38d2:	8b 17                	mov    (%rdi),%edx
    38d4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    38dd:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    38e1:	31 c0                	xor    %eax,%eax
    38e3:	49 89 fc             	mov    %rdi,%r12
    38e6:	bf 01 00 00 00       	mov    $0x1,%edi
    38eb:	e8 70 eb ff ff       	call   2460 <__printf_chk@plt>
  struct timespec preempt = {
    38f0:	66 0f 6f 05 38 30 00 00 	movdqa 0x3038(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    38f8:	ba 30 75 00 00       	mov    $0x7530,%edx
    38fd:	31 c0                	xor    %eax,%eax
    38ff:	48 8d 35 1c 27 00 00 	lea    0x271c(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    3906:	bf 01 00 00 00       	mov    $0x1,%edi
    390b:	0f 29 45 90          	movaps %xmm0,-0x70(%rbp)
    390f:	e8 4c eb ff ff       	call   2460 <__printf_chk@plt>
  while (data->running && n < times) {
    3914:	41 8b 44 24 2c       	mov    0x2c(%r12),%eax
    3919:	89 85 7c ff ff ff    	mov    %eax,-0x84(%rbp)
    391f:	85 c0                	test   %eax,%eax
    3921:	0f 84 c9 00 00 00    	je     39f0 <timer_thread+0x140>
    3927:	48 8d 45 90          	lea    -0x70(%rbp),%rax
  int n = 0;
    392b:	45 31 ff             	xor    %r15d,%r15d
    392e:	4c 8d 6d 80          	lea    -0x80(%rbp),%r13
    y++;
    3932:	31 db                	xor    %ebx,%ebx
  int y = 0;
    3934:	c7 85 7c ff ff ff 00 00 00 00 	movl   $0x0,-0x84(%rbp)
    393e:	48 89 85 70 ff ff ff 	mov    %rax,-0x90(%rbp)
    nanosleep(&preempt , &rem2);
    3945:	48 8b bd 70 ff ff ff 	mov    -0x90(%rbp),%rdi
    394c:	4c 89 ee             	mov    %r13,%rsi
    n++;
    394f:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3953:	e8 f8 e9 ff ff       	call   2350 <nanosleep@plt>
    y++;
    3958:	8b bd 7c ff ff ff    	mov    -0x84(%rbp),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    395e:	49 63 44 24 18       	movslq 0x18(%r12),%rax
    y++;
    3963:	83 c7 01             	add    $0x1,%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3966:	85 c0                	test   %eax,%eax
    3968:	7e 5c                	jle    39c6 <timer_thread+0x116>
        data->threads[x].tasks[y].scheduled = 0;
    396a:	4c 63 b5 7c ff ff ff 	movslq -0x84(%rbp),%r14
    3971:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
    3976:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    397a:	4d 8d 04 56          	lea    (%r14,%rdx,2),%r8
    397e:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3982:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3986:	49 c1 e0 03          	shl    $0x3,%r8
    398a:	4c 8d 14 c1          	lea    (%rcx,%rax,8),%r10
    398e:	66 90                	xchg   %ax,%ax
        int next = (y + 1) % data->threads[x].task_count;
    3990:	89 f8                	mov    %edi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    3992:	48 8b 71 20          	mov    0x20(%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    3996:	99                   	cltd
    3997:	f7 79 28             	idivl  0x28(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    399a:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    39a1:	48 63 d2             	movslq %edx,%rdx
    39a4:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    39a8:	48 8d 04 42          	lea    (%rdx,%rax,2),%rax
    39ac:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
        data->threads[x].tasks[y].scheduled = 0;
    39b0:	4c 01 c6             	add    %r8,%rsi
        data->threads[x].tasks[next].scheduled = 1;
    39b3:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
        data->threads[x].tasks[y].scheduled = 0;
    39ba:	c7 46 48 00 00 00 00 	movl   $0x0,0x48(%rsi)
    for (int x = 0 ; x < data->thread_count ; x++) {
    39c1:	49 39 ca             	cmp    %rcx,%r10
    39c4:	75 ca                	jne    3990 <timer_thread+0xe0>
    asm volatile ("mfence" ::: "memory");
    39c6:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    39c9:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    y++;
    39ce:	39 78 28             	cmp    %edi,0x28(%rax)
  while (data->running && n < times) {
    39d1:	41 8b 44 24 2c       	mov    0x2c(%r12),%eax
    y++;
    39d6:	0f 4e fb             	cmovle %ebx,%edi
    39d9:	89 bd 7c ff ff ff    	mov    %edi,-0x84(%rbp)
  while (data->running && n < times) {
    39df:	85 c0                	test   %eax,%eax
    39e1:	74 0d                	je     39f0 <timer_thread+0x140>
    39e3:	41 81 ff 30 75 00 00 	cmp    $0x7530,%r15d
    39ea:	0f 85 55 ff ff ff    	jne    3945 <timer_thread+0x95>
    39f0:	48 8d 3d 41 26 00 00 	lea    0x2641(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    39f7:	e8 f4 e8 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    39fc:	49 63 54 24 1c       	movslq 0x1c(%r12),%rdx
    3a01:	85 d2                	test   %edx,%edx
    3a03:	7e 74                	jle    3a79 <timer_thread+0x1c9>
    for (int y = 0 ; y < data->task_count ; y++) {
    3a05:	49 63 44 24 28       	movslq 0x28(%r12),%rax
    3a0a:	85 c0                	test   %eax,%eax
    3a0c:	7e 6b                	jle    3a79 <timer_thread+0x1c9>
    3a0e:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
      data->threads[x].tasks[y].sending = 0;
    3a12:	4d 8b 54 24 10       	mov    0x10(%r12),%r10
    3a17:	31 f6                	xor    %esi,%esi
    3a19:	4c 8d 04 4a          	lea    (%rdx,%rcx,2),%r8
    3a1d:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3a21:	48 8d 3c 50          	lea    (%rax,%rdx,2),%rdi
    3a25:	49 c1 e0 03          	shl    $0x3,%r8
    3a29:	48 c1 e7 03          	shl    $0x3,%rdi
    for (int y = 0 ; y < data->task_count ; y++) {
    3a2d:	49 8b 44 32 20       	mov    0x20(%r10,%rsi,1),%rax
    3a32:	48 8d 0c 07          	lea    (%rdi,%rax,1),%rcx
    3a36:	40 f6 c7 08          	test   $0x8,%dil
    3a3a:	74 15                	je     3a51 <timer_thread+0x1a1>
      data->threads[x].tasks[y].sending = 0;
    3a3c:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3a46:	48 05 98 00 00 00    	add    $0x98,%rax
    3a4c:	48 39 c1             	cmp    %rax,%rcx
    3a4f:	74 1c                	je     3a6d <timer_thread+0x1bd>
      data->threads[x].tasks[y].sending = 0;
    3a51:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3a5b:	48 05 30 01 00 00    	add    $0x130,%rax
      data->threads[x].tasks[y].sending = 0;
    3a61:	c7 40 e8 00 00 00 00 	movl   $0x0,-0x18(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3a68:	48 39 c1             	cmp    %rax,%rcx
    3a6b:	75 e4                	jne    3a51 <timer_thread+0x1a1>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3a6d:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
    3a74:	49 39 f0             	cmp    %rsi,%r8
    3a77:	75 b4                	jne    3a2d <timer_thread+0x17d>
  asm volatile ("mfence" ::: "memory");
    3a79:	0f ae f0             	mfence
  struct timespec drain = {
    3a7c:	66 0f 6f 05 bc 2e 00 00 	movdqa 0x2ebc(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3a84:	4c 8d 35 d2 25 00 00 	lea    0x25d2(%rip),%r14        # 605d <_IO_stdin_used+0x5d>
    3a8b:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
    y++;
    3a8f:	8b 9d 7c ff ff ff    	mov    -0x84(%rbp),%ebx
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a95:	49 63 44 24 18       	movslq 0x18(%r12),%rax
    y++;
    3a9a:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a9d:	85 c0                	test   %eax,%eax
    3a9f:	7e 5d                	jle    3afe <timer_thread+0x24e>
        data->threads[x].tasks[y].scheduled = 0;
    3aa1:	48 63 8d 7c ff ff ff 	movslq -0x84(%rbp),%rcx
    3aa8:	48 8d 14 c9          	lea    (%rcx,%rcx,8),%rdx
    3aac:	4c 8d 04 51          	lea    (%rcx,%rdx,2),%r8
    3ab0:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
    3ab5:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3ab9:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3abd:	49 c1 e0 03          	shl    $0x3,%r8
    3ac1:	4c 8d 14 c1          	lea    (%rcx,%rax,8),%r10
    3ac5:	0f 1f 00             	nopl   (%rax)
        int next = (y + 1) % data->threads[x].task_count;
    3ac8:	89 f8                	mov    %edi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    3aca:	48 8b 71 20          	mov    0x20(%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    3ace:	99                   	cltd
    3acf:	f7 79 28             	idivl  0x28(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ad2:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    3ad9:	48 63 c2             	movslq %edx,%rax
    3adc:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3ae0:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3ae4:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
        data->threads[x].tasks[y].scheduled = 0;
    3ae8:	4c 01 c6             	add    %r8,%rsi
        data->threads[x].tasks[next].scheduled = 1;
    3aeb:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
        data->threads[x].tasks[y].scheduled = 0;
    3af2:	c7 46 48 00 00 00 00 	movl   $0x0,0x48(%rsi)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3af9:	49 39 ca             	cmp    %rcx,%r10
    3afc:	75 ca                	jne    3ac8 <timer_thread+0x218>
    asm volatile ("mfence" ::: "memory");
    3afe:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    3b01:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    y++;
    3b06:	31 d2                	xor    %edx,%edx
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b08:	45 8b 44 24 18       	mov    0x18(%r12),%r8d
    y++;
    3b0d:	39 78 28             	cmp    %edi,0x28(%rax)
    3b10:	0f 4f d7             	cmovg  %edi,%edx
    3b13:	89 95 7c ff ff ff    	mov    %edx,-0x84(%rbp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b19:	45 85 c0             	test   %r8d,%r8d
    3b1c:	0f 8e e0 00 00 00    	jle    3c02 <timer_thread+0x352>
    3b22:	31 db                	xor    %ebx,%ebx
    3b24:	45 31 ed             	xor    %r13d,%r13d
    3b27:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    3b2d:	0f 1f 00             	nopl   (%rax)
            all_empty = 0;
    3b30:	45 31 ff             	xor    %r15d,%r15d
    3b33:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3b38:	48 8b 44 18 20       	mov    0x20(%rax,%rbx,1),%rax
    3b3d:	4b 8d 14 ff          	lea    (%r15,%r15,8),%rdx
    3b41:	49 63 f8             	movslq %r8d,%rdi
    3b44:	49 8d 14 57          	lea    (%r15,%rdx,2),%rdx
    3b48:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    3b4c:	31 c0                	xor    %eax,%eax
    3b4e:	eb 1b                	jmp    3b6b <timer_thread+0x2bb>
    3b50:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    3b54:	48 8b 74 16 08       	mov    0x8(%rsi,%rdx,1),%rsi
    3b59:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    3b5d:	48 85 f6             	test   %rsi,%rsi
    3b60:	7f 21                	jg     3b83 <timer_thread+0x2d3>
        for (int k = 0 ; k < data->thread_count; k++) {
    3b62:	48 83 c0 01          	add    $0x1,%rax
    3b66:	48 39 f8             	cmp    %rdi,%rax
    3b69:	74 4a                	je     3bb5 <timer_thread+0x305>
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3b6b:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    3b6f:	48 89 c2             	mov    %rax,%rdx
    3b72:	48 c1 e2 05          	shl    $0x5,%rdx
    3b76:	48 8b 34 16          	mov    (%rsi,%rdx,1),%rsi
    3b7a:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    3b7e:	48 85 f6             	test   %rsi,%rsi
    3b81:	7e cd                	jle    3b50 <timer_thread+0x2a0>
            printf("%d %ld %ld left\n", k, ((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count, ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count);
    3b83:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    3b87:	bf 01 00 00 00       	mov    $0x1,%edi
    3b8c:	48 8b 74 16 08       	mov    0x8(%rsi,%rdx,1),%rsi
    3b91:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3b95:	48 8b 49 70          	mov    0x70(%rcx),%rcx
    3b99:	4c 89 f6             	mov    %r14,%rsi
    3b9c:	48 8b 14 11          	mov    (%rcx,%rdx,1),%rdx
    3ba0:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    3ba4:	89 c2                	mov    %eax,%edx
    3ba6:	31 c0                	xor    %eax,%eax
    3ba8:	e8 b3 e8 ff ff       	call   2460 <__printf_chk@plt>
            break;
    3bad:	45 8b 44 24 18       	mov    0x18(%r12),%r8d
            all_empty = 0;
    3bb2:	45 31 d2             	xor    %r10d,%r10d
      for (int y = 0 ; y < data->thread_count ; y++) {
    3bb5:	49 83 c7 01          	add    $0x1,%r15
    3bb9:	45 39 f8             	cmp    %r15d,%r8d
    3bbc:	7e 12                	jle    3bd0 <timer_thread+0x320>
    3bbe:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    3bc3:	e9 70 ff ff ff       	jmp    3b38 <timer_thread+0x288>
    3bc8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bd0:	41 83 c5 01          	add    $0x1,%r13d
    3bd4:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3bdb:	45 39 e8             	cmp    %r13d,%r8d
    3bde:	7e 0a                	jle    3bea <timer_thread+0x33a>
    3be0:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    3be5:	e9 46 ff ff ff       	jmp    3b30 <timer_thread+0x280>
    if (all_empty == 1) {
    3bea:	41 83 fa 01          	cmp    $0x1,%r10d
    3bee:	74 12                	je     3c02 <timer_thread+0x352>
      nanosleep(&drain , &drainrem);
    3bf0:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    3bf4:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
    3bf8:	e8 53 e7 ff ff       	call   2350 <nanosleep@plt>
    3bfd:	e9 8d fe ff ff       	jmp    3a8f <timer_thread+0x1df>
    3c02:	48 8d 3d 4b 24 00 00 	lea    0x244b(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3c09:	4c 8d 3d 70 24 00 00 	lea    0x2470(%rip),%r15        # 6080 <_IO_stdin_used+0x80>
    3c10:	e8 db e6 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3c15:	41 8b 44 24 2c       	mov    0x2c(%r12),%eax
    3c1a:	48 8d 1d 4d 24 00 00 	lea    0x244d(%rip),%rbx        # 606e <_IO_stdin_used+0x6e>
    3c21:	85 c0                	test   %eax,%eax
    3c23:	0f 84 dd 00 00 00    	je     3d06 <timer_thread+0x456>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c29:	41 8b 4c 24 1c       	mov    0x1c(%r12),%ecx
    3c2e:	45 31 ed             	xor    %r13d,%r13d
    3c31:	45 31 f6             	xor    %r14d,%r14d
    3c34:	85 c9                	test   %ecx,%ecx
    3c36:	7e 2a                	jle    3c62 <timer_thread+0x3b2>
    3c38:	49 8b 44 24 10       	mov    0x10(%r12),%rax
      data->threads[x].running = 0;
    3c3d:	4a 8d 14 28          	lea    (%rax,%r13,1),%rdx
      if (data->threads[x].type == IO) {
    3c41:	83 7a 04 02          	cmpl   $0x2,0x4(%rdx)
      data->threads[x].running = 0;
    3c45:	c7 42 2c 00 00 00 00 	movl   $0x0,0x2c(%rdx)
      if (data->threads[x].type == IO) {
    3c4c:	0f 84 e0 00 00 00    	je     3d32 <timer_thread+0x482>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c52:	41 83 c6 01          	add    $0x1,%r14d
    3c56:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    3c5d:	41 39 ce             	cmp    %ecx,%r14d
    3c60:	7c db                	jl     3c3d <timer_thread+0x38d>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c62:	49 63 54 24 18       	movslq 0x18(%r12),%rdx
    3c67:	85 d2                	test   %edx,%edx
    3c69:	7e 7a                	jle    3ce5 <timer_thread+0x435>
      for (int y = 0 ; y < data->task_count ; y++) {
    3c6b:	49 63 44 24 28       	movslq 0x28(%r12),%rax
    3c70:	85 c0                	test   %eax,%eax
    3c72:	7e 71                	jle    3ce5 <timer_thread+0x435>
    3c74:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
        data->threads[x].tasks[y].scheduled = 0;
    3c78:	4d 8b 54 24 10       	mov    0x10(%r12),%r10
    3c7d:	31 f6                	xor    %esi,%esi
    3c7f:	4c 8d 04 4a          	lea    (%rdx,%rcx,2),%r8
    3c83:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3c87:	48 8d 3c 50          	lea    (%rax,%rdx,2),%rdi
    3c8b:	49 c1 e0 03          	shl    $0x3,%r8
    3c8f:	48 c1 e7 03          	shl    $0x3,%rdi
    3c93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int y = 0 ; y < data->task_count ; y++) {
    3c98:	49 8b 44 32 20       	mov    0x20(%r10,%rsi,1),%rax
    3c9d:	48 8d 0c 38          	lea    (%rax,%rdi,1),%rcx
    3ca1:	40 f6 c7 08          	test   $0x8,%dil
    3ca5:	74 19                	je     3cc0 <timer_thread+0x410>
        data->threads[x].tasks[y].scheduled = 0;
    3ca7:	c7 40 48 00 00 00 00 	movl   $0x0,0x48(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3cae:	48 05 98 00 00 00    	add    $0x98,%rax
    3cb4:	48 39 c8             	cmp    %rcx,%rax
    3cb7:	74 20                	je     3cd9 <timer_thread+0x429>
    3cb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x].tasks[y].scheduled = 0;
    3cc0:	c7 40 48 00 00 00 00 	movl   $0x0,0x48(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3cc7:	48 05 30 01 00 00    	add    $0x130,%rax
        data->threads[x].tasks[y].scheduled = 0;
    3ccd:	c7 40 b0 00 00 00 00 	movl   $0x0,-0x50(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3cd4:	48 39 c8             	cmp    %rcx,%rax
    3cd7:	75 e7                	jne    3cc0 <timer_thread+0x410>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3cd9:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
    3ce0:	4c 39 c6             	cmp    %r8,%rsi
    3ce3:	75 b3                	jne    3c98 <timer_thread+0x3e8>
    asm volatile ("mfence" ::: "memory");
    3ce5:	0f ae f0             	mfence
    3ce8:	4c 89 ff             	mov    %r15,%rdi
    3ceb:	e8 00 e6 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3cf0:	41 c7 44 24 2c 00 00 00 00 	movl   $0x0,0x2c(%r12)
  while (data->running) {
    3cf9:	41 8b 44 24 2c       	mov    0x2c(%r12),%eax
    3cfe:	85 c0                	test   %eax,%eax
    3d00:	0f 85 23 ff ff ff    	jne    3c29 <timer_thread+0x379>
    3d06:	48 8d 3d 7a 23 00 00 	lea    0x237a(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3d0d:	e8 de e5 ff ff       	call   22f0 <puts@plt>
}
    3d12:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    3d16:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3d1f:	75 4b                	jne    3d6c <timer_thread+0x4bc>
    3d21:	48 83 c4 68          	add    $0x68,%rsp
    3d25:	31 c0                	xor    %eax,%eax
    3d27:	5b                   	pop    %rbx
    3d28:	41 5c                	pop    %r12
    3d2a:	41 5d                	pop    %r13
    3d2c:	41 5e                	pop    %r14
    3d2e:	41 5f                	pop    %r15
    3d30:	5d                   	pop    %rbp
    3d31:	c3                   	ret
    3d32:	48 89 df             	mov    %rbx,%rdi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d35:	41 83 c6 01          	add    $0x1,%r14d
    3d39:	e8 b2 e5 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]._eventfd, 1);
    3d3e:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    3d43:	be 01 00 00 00       	mov    $0x1,%esi
    3d48:	42 8b 7c 28 48       	mov    0x48(%rax,%r13,1),%edi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d4d:	49 81 c5 98 00 00 00 	add    $0x98,%r13
        eventfd_write(data->threads[x]._eventfd, 1);
    3d54:	e8 b7 e6 ff ff       	call   2410 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d59:	41 8b 4c 24 1c       	mov    0x1c(%r12),%ecx
    3d5e:	41 39 ce             	cmp    %ecx,%r14d
    3d61:	0f 8c d1 fe ff ff    	jl     3c38 <timer_thread+0x388>
    3d67:	e9 f6 fe ff ff       	jmp    3c62 <timer_thread+0x3b2>
}
    3d6c:	e8 bf e5 ff ff       	call   2330 <__stack_chk_fail@plt>
    3d71:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3d7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003d80 <strtolower>:
void strtolower(char *str) {
    3d80:	f3 0f 1e fa          	endbr64
    3d84:	55                   	push   %rbp
    3d85:	48 89 e5             	mov    %rsp,%rbp
    3d88:	41 54                	push   %r12
    3d8a:	53                   	push   %rbx
    3d8b:	ff 15 57 52 00 00    	call   *0x5257(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    for (; *str; ++str)
    3d91:	48 0f be 1f          	movsbq (%rdi),%rbx
void strtolower(char *str) {
    3d95:	49 89 fc             	mov    %rdi,%r12
    for (; *str; ++str)
    3d98:	84 db                	test   %bl,%bl
    3d9a:	74 24                	je     3dc0 <strtolower+0x40>
        *str = (char)tolower(*str);
    3d9c:	e8 8f e7 ff ff       	call   2530 <__ctype_tolower_loc@plt>
    3da1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3da8:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3dab:	49 83 c4 01          	add    $0x1,%r12
        *str = (char)tolower(*str);
    3daf:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3db2:	41 88 54 24 ff       	mov    %dl,-0x1(%r12)
    for (; *str; ++str)
    3db7:	49 0f be 1c 24       	movsbq (%r12),%rbx
    3dbc:	84 db                	test   %bl,%bl
    3dbe:	75 e8                	jne    3da8 <strtolower+0x28>
}
    3dc0:	5b                   	pop    %rbx
    3dc1:	41 5c                	pop    %r12
    3dc3:	5d                   	pop    %rbp
    3dc4:	c3                   	ret
    3dc5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003dd0 <zh_malloc>:
void *zh_malloc(size_t size) {
    3dd0:	f3 0f 1e fa          	endbr64
    3dd4:	55                   	push   %rbp
    3dd5:	48 89 e5             	mov    %rsp,%rbp
    3dd8:	ff 15 0a 52 00 00    	call   *0x520a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    void *buf = malloc(size);
    3dde:	e8 3d e6 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    3de3:	48 85 c0             	test   %rax,%rax
    3de6:	74 02                	je     3dea <zh_malloc+0x1a>
}
    3de8:	5d                   	pop    %rbp
    3de9:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3dea:	48 8b 0d 2f 52 00 00 	mov    0x522f(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3df1:	ba 28 00 00 00       	mov    $0x28,%edx
    3df6:	be 01 00 00 00       	mov    $0x1,%esi
    3dfb:	48 8d 3d 3e 26 00 00 	lea    0x263e(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    3e02:	e8 d9 e6 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    3e07:	bf 01 00 00 00       	mov    $0x1,%edi
    3e0c:	e8 af e6 ff ff       	call   24c0 <exit@plt>
    3e11:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3e1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003e20 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3e20:	f3 0f 1e fa          	endbr64
    3e24:	55                   	push   %rbp
    3e25:	48 89 e5             	mov    %rsp,%rbp
    3e28:	53                   	push   %rbx
    3e29:	48 83 ec 08          	sub    $0x8,%rsp
    3e2d:	ff 15 b5 51 00 00    	call   *0x51b5(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    const char *dot = strrchr(filename, '.');
    3e33:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3e38:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3e3b:	e8 20 e5 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3e40:	48 85 c0             	test   %rax,%rax
    3e43:	74 13                	je     3e58 <get_filename_ext+0x38>
    3e45:	48 39 c3             	cmp    %rax,%rbx
    3e48:	74 0e                	je     3e58 <get_filename_ext+0x38>
}
    3e4a:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    return dot + 1;
    3e4e:	48 83 c0 01          	add    $0x1,%rax
}
    3e52:	c9                   	leave
    3e53:	c3                   	ret
    3e54:	0f 1f 40 00          	nopl   0x0(%rax)
    3e58:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
        return "";
    3e5c:	48 8d 05 6c 22 00 00 	lea    0x226c(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
}
    3e63:	c9                   	leave
    3e64:	c3                   	ret
    3e65:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003e70 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3e70:	f3 0f 1e fa          	endbr64
    3e74:	55                   	push   %rbp
    3e75:	48 89 e5             	mov    %rsp,%rbp
    3e78:	41 56                	push   %r14
    3e7a:	41 55                	push   %r13
    3e7c:	41 54                	push   %r12
    3e7e:	53                   	push   %rbx
    3e7f:	48 81 ec 10 08 00 00 	sub    $0x810,%rsp
    3e86:	ff 15 5c 51 00 00    	call   *0x515c(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    3e8c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3e95:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    3e99:	31 c0                	xor    %eax,%eax
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3e9b:	4c 8d ad d0 f7 ff ff 	lea    -0x830(%rbp),%r13
    3ea2:	49 89 f6             	mov    %rsi,%r14
    3ea5:	49 89 d4             	mov    %rdx,%r12
    3ea8:	48 89 fe             	mov    %rdi,%rsi
    3eab:	ba 00 04 00 00       	mov    $0x400,%edx
    3eb0:	4c 89 ef             	mov    %r13,%rdi
    3eb3:	e8 88 e5 ff ff       	call   2440 <__strcpy_chk@plt>
    for (; *str; ++str)
    3eb8:	48 0f be 9d d0 f7 ff ff 	movsbq -0x830(%rbp),%rbx
    3ec0:	84 db                	test   %bl,%bl
    3ec2:	74 1e                	je     3ee2 <send_headers+0x72>
        *str = (char)tolower(*str);
    3ec4:	e8 67 e6 ff ff       	call   2530 <__ctype_tolower_loc@plt>
    3ec9:	48 8b 08             	mov    (%rax),%rcx
    3ecc:	4c 89 e8             	mov    %r13,%rax
    3ecf:	90                   	nop
    3ed0:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3ed3:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3ed7:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3eda:	48 0f be 18          	movsbq (%rax),%rbx
    3ede:	84 db                	test   %bl,%bl
    3ee0:	75 ee                	jne    3ed0 <send_headers+0x60>
    void *buf = malloc(size);
    3ee2:	bf 11 00 00 00       	mov    $0x11,%edi
    3ee7:	e8 34 e5 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    3eec:	48 85 c0             	test   %rax,%rax
    3eef:	0f 84 72 04 00 00    	je     4367 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3ef5:	66 0f 6f 05 53 2a 00 00 	movdqa 0x2a53(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    iov[0].iov_base = zh_malloc(slen);
    3efd:	49 89 04 24          	mov    %rax,(%r12)
    void *buf = malloc(size);
    3f01:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3f06:	49 c7 44 24 08 11 00 00 00 	movq   $0x11,0x8(%r12)
    3f0f:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3f13:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3f16:	e8 05 e5 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    3f1b:	48 85 c0             	test   %rax,%rax
    3f1e:	0f 84 43 04 00 00    	je     4367 <send_headers+0x4f7>
    3f24:	66 0f 6f 05 34 2a 00 00 	movdqa 0x2a34(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    iov[1].iov_base = zh_malloc(slen);
    3f2c:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    const char *dot = strrchr(filename, '.');
    3f31:	4c 89 ef             	mov    %r13,%rdi
    3f34:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3f3e:	49 c7 44 24 18 17 00 00 00 	movq   $0x17,0x18(%r12)
    3f47:	0f 11 00             	movups %xmm0,(%rax)
    3f4a:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3f4e:	be 2e 00 00 00       	mov    $0x2e,%esi
    3f53:	e8 08 e4 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3f58:	48 85 c0             	test   %rax,%rax
    3f5b:	0f 84 df 02 00 00    	je     4240 <send_headers+0x3d0>
    3f61:	4c 39 e8             	cmp    %r13,%rax
    3f64:	0f 84 d6 02 00 00    	je     4240 <send_headers+0x3d0>
    return dot + 1;
    3f6a:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3f6e:	48 8d 3d 28 21 00 00 	lea    0x2128(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3f75:	48 89 de             	mov    %rbx,%rsi
    3f78:	e8 33 e4 ff ff       	call   23b0 <strcmp@plt>
    3f7d:	85 c0                	test   %eax,%eax
    3f7f:	75 1e                	jne    3f9f <send_headers+0x12f>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3f81:	66 0f 6f 05 e7 29 00 00 	movdqa 0x29e7(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    3f89:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    3f90:	66 0f 6f 05 e8 29 00 00 	movdqa 0x29e8(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    3f98:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("jpeg", file_ext) == 0)
    3f9f:	48 89 de             	mov    %rbx,%rsi
    3fa2:	48 8d 3d f8 20 00 00 	lea    0x20f8(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3fa9:	e8 02 e4 ff ff       	call   23b0 <strcmp@plt>
    3fae:	85 c0                	test   %eax,%eax
    3fb0:	75 1e                	jne    3fd0 <send_headers+0x160>
    3fb2:	66 0f 6f 05 b6 29 00 00 	movdqa 0x29b6(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    3fba:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    3fc1:	66 0f 6f 05 b7 29 00 00 	movdqa 0x29b7(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    3fc9:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("png", file_ext) == 0)
    3fd0:	48 89 de             	mov    %rbx,%rsi
    3fd3:	48 8d 3d cc 20 00 00 	lea    0x20cc(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3fda:	e8 d1 e3 ff ff       	call   23b0 <strcmp@plt>
    3fdf:	85 c0                	test   %eax,%eax
    3fe1:	0f 84 09 02 00 00    	je     41f0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    3fe7:	48 89 de             	mov    %rbx,%rsi
    3fea:	48 8d 3d b9 20 00 00 	lea    0x20b9(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3ff1:	e8 ba e3 ff ff       	call   23b0 <strcmp@plt>
    3ff6:	85 c0                	test   %eax,%eax
    3ff8:	0f 84 a2 02 00 00    	je     42a0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    3ffe:	48 89 de             	mov    %rbx,%rsi
    4001:	48 8d 3d a6 20 00 00 	lea    0x20a6(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    4008:	e8 a3 e3 ff ff       	call   23b0 <strcmp@plt>
    400d:	85 c0                	test   %eax,%eax
    400f:	0f 84 63 02 00 00    	je     4278 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4015:	48 89 de             	mov    %rbx,%rsi
    4018:	48 8d 3d d2 20 00 00 	lea    0x20d2(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    401f:	e8 8c e3 ff ff       	call   23b0 <strcmp@plt>
    4024:	85 c0                	test   %eax,%eax
    4026:	0f 84 24 02 00 00    	je     4250 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    402c:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    402f:	0f 84 53 01 00 00    	je     4188 <send_headers+0x318>
    if (strcmp("css", file_ext) == 0)
    4035:	48 89 de             	mov    %rbx,%rsi
    4038:	48 8d 3d 73 20 00 00 	lea    0x2073(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    403f:	e8 6c e3 ff ff       	call   23b0 <strcmp@plt>
    4044:	85 c0                	test   %eax,%eax
    4046:	0f 84 a4 02 00 00    	je     42f0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    404c:	48 89 de             	mov    %rbx,%rsi
    404f:	48 8d 3d 60 20 00 00 	lea    0x2060(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    4056:	e8 55 e3 ff ff       	call   23b0 <strcmp@plt>
    405b:	85 c0                	test   %eax,%eax
    405d:	0f 84 65 02 00 00    	je     42c8 <send_headers+0x458>
    slen = strlen(send_buffer);
    4063:	4c 8d ad d0 fb ff ff 	lea    -0x430(%rbp),%r13
    406a:	4c 89 ef             	mov    %r13,%rdi
    406d:	e8 ae e2 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4072:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4075:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4078:	e8 a3 e3 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    407d:	48 85 c0             	test   %rax,%rax
    4080:	0f 84 e1 02 00 00    	je     4367 <send_headers+0x4f7>
    iov[2].iov_base = zh_malloc(slen);
    4086:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    iov[2].iov_len = slen;
    408b:	49 89 5c 24 28       	mov    %rbx,0x28(%r12)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4090:	83 fb 08             	cmp    $0x8,%ebx
    4093:	0f 83 37 01 00 00    	jae    41d0 <send_headers+0x360>
    4099:	f6 c3 04             	test   $0x4,%bl
    409c:	0f 85 71 02 00 00    	jne    4313 <send_headers+0x4a3>
    40a2:	85 db                	test   %ebx,%ebx
    40a4:	74 12                	je     40b8 <send_headers+0x248>
    40a6:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    40ad:	88 10                	mov    %dl,(%rax)
    40af:	f6 c3 02             	test   $0x2,%bl
    40b2:	0f 85 8b 02 00 00    	jne    4343 <send_headers+0x4d3>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    40b8:	4d 89 f0             	mov    %r14,%r8
    40bb:	48 8d 0d f8 1f 00 00 	lea    0x1ff8(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    40c2:	4c 89 ef             	mov    %r13,%rdi
    40c5:	31 c0                	xor    %eax,%eax
    40c7:	ba 00 04 00 00       	mov    $0x400,%edx
    40cc:	be 01 00 00 00       	mov    $0x1,%esi
    40d1:	e8 6a e4 ff ff       	call   2540 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    40d6:	4c 89 ef             	mov    %r13,%rdi
    40d9:	e8 42 e2 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    40de:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    40e1:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    40e4:	e8 37 e3 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    40e9:	48 85 c0             	test   %rax,%rax
    40ec:	0f 84 75 02 00 00    	je     4367 <send_headers+0x4f7>
    iov[3].iov_base = zh_malloc(slen);
    40f2:	49 89 44 24 30       	mov    %rax,0x30(%r12)
    iov[3].iov_len = slen;
    40f7:	49 89 5c 24 38       	mov    %rbx,0x38(%r12)
    40fc:	83 fb 08             	cmp    $0x8,%ebx
    40ff:	0f 83 13 01 00 00    	jae    4218 <send_headers+0x3a8>
    4105:	f6 c3 04             	test   $0x4,%bl
    4108:	0f 85 1d 02 00 00    	jne    432b <send_headers+0x4bb>
    410e:	85 db                	test   %ebx,%ebx
    4110:	74 12                	je     4124 <send_headers+0x2b4>
    4112:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    4119:	88 10                	mov    %dl,(%rax)
    411b:	f6 c3 02             	test   $0x2,%bl
    411e:	0f 85 31 02 00 00    	jne    4355 <send_headers+0x4e5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4124:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4129:	bf 02 00 00 00       	mov    $0x2,%edi
    412e:	c6 85 d2 fb ff ff 00 	movb   $0x0,-0x42e(%rbp)
    4135:	66 89 85 d0 fb ff ff 	mov    %ax,-0x430(%rbp)
    413c:	e8 df e2 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    4141:	48 85 c0             	test   %rax,%rax
    4144:	0f 84 1d 02 00 00    	je     4367 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    414a:	0f b7 95 d0 fb ff ff 	movzwl -0x430(%rbp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4151:	49 89 44 24 40       	mov    %rax,0x40(%r12)
    iov[4].iov_len = slen;
    4156:	49 c7 44 24 48 02 00 00 00 	movq   $0x2,0x48(%r12)
    415f:	66 89 10             	mov    %dx,(%rax)
}
    4162:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    4166:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    416f:	0f 85 19 02 00 00    	jne    438e <send_headers+0x51e>
    4175:	48 81 c4 10 08 00 00 	add    $0x810,%rsp
    417c:	5b                   	pop    %rbx
    417d:	41 5c                	pop    %r12
    417f:	41 5d                	pop    %r13
    4181:	41 5e                	pop    %r14
    4183:	5d                   	pop    %rbp
    4184:	c3                   	ret
    4185:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
    4188:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    418c:	0f 85 a3 fe ff ff    	jne    4035 <send_headers+0x1c5>
    4192:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4196:	0f 85 99 fe ff ff    	jne    4035 <send_headers+0x1c5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    419c:	66 0f 6f 05 2c 28 00 00 	movdqa 0x282c(%rip),%xmm0        # 69d0 <_IO_stdin_used+0x9d0>
    41a4:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    41ae:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    41b5:	66 0f 6f 05 23 28 00 00 	movdqa 0x2823(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
    41bd:	0f 29 85 e0 fb ff ff 	movaps %xmm0,-0x420(%rbp)
    41c4:	48 89 85 ef fb ff ff 	mov    %rax,-0x411(%rbp)
    41cb:	e9 65 fe ff ff       	jmp    4035 <send_headers+0x1c5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    41d0:	89 da                	mov    %ebx,%edx
    41d2:	48 89 c7             	mov    %rax,%rdi
    41d5:	4c 89 ee             	mov    %r13,%rsi
    41d8:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    41dd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    41e2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    41e5:	c1 e9 03             	shr    $0x3,%ecx
    41e8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    41eb:	e9 c8 fe ff ff       	jmp    40b8 <send_headers+0x248>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    41f0:	66 0f 6f 05 78 27 00 00 	movdqa 0x2778(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    41f8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    41ff:	66 0f 6f 05 89 27 00 00 	movdqa 0x2789(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    4207:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    420e:	e9 d4 fd ff ff       	jmp    3fe7 <send_headers+0x177>
    4213:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4218:	89 da                	mov    %ebx,%edx
    421a:	48 89 c7             	mov    %rax,%rdi
    421d:	4c 89 ee             	mov    %r13,%rsi
    4220:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    4225:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    422a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    422d:	c1 e9 03             	shr    $0x3,%ecx
    4230:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4233:	e9 ec fe ff ff       	jmp    4124 <send_headers+0x2b4>
    4238:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4240:	48 8d 1d 88 1e 00 00 	lea    0x1e88(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    4247:	e9 9b fd ff ff       	jmp    3fe7 <send_headers+0x177>
    424c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4250:	66 0f 6f 05 58 27 00 00 	movdqa 0x2758(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    4258:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    425f:	66 0f 6f 05 59 27 00 00 	movdqa 0x2759(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4267:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    426e:	e9 b9 fd ff ff       	jmp    402c <send_headers+0x1bc>
    4273:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4278:	66 0f 6f 05 30 27 00 00 	movdqa 0x2730(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    4280:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4287:	66 0f 6f 05 31 27 00 00 	movdqa 0x2731(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    428f:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    4296:	e9 7a fd ff ff       	jmp    4015 <send_headers+0x1a5>
    429b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    42a0:	66 0f 6f 05 c8 26 00 00 	movdqa 0x26c8(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    42a8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    42af:	66 0f 6f 05 e9 26 00 00 	movdqa 0x26e9(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    42b7:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    42be:	e9 3b fd ff ff       	jmp    3ffe <send_headers+0x18e>
    42c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    42c8:	66 0f 6f 05 e0 26 00 00 	movdqa 0x26e0(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    42d0:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    42d7:	66 0f 6f 05 21 27 00 00 	movdqa 0x2721(%rip),%xmm0        # 6a00 <_IO_stdin_used+0xa00>
    42df:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    42e6:	e9 78 fd ff ff       	jmp    4063 <send_headers+0x1f3>
    42eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    42f0:	66 0f 6f 05 b8 26 00 00 	movdqa 0x26b8(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    42f8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    42ff:	66 0f 6f 05 e9 26 00 00 	movdqa 0x26e9(%rip),%xmm0        # 69f0 <_IO_stdin_used+0x9f0>
    4307:	0f 11 85 d9 fb ff ff 	movups %xmm0,-0x427(%rbp)
    430e:	e9 39 fd ff ff       	jmp    404c <send_headers+0x1dc>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4313:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    4319:	89 db                	mov    %ebx,%ebx
    431b:	89 10                	mov    %edx,(%rax)
    431d:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    4322:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4326:	e9 8d fd ff ff       	jmp    40b8 <send_headers+0x248>
    432b:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    4331:	89 db                	mov    %ebx,%ebx
    4333:	89 10                	mov    %edx,(%rax)
    4335:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    433a:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    433e:	e9 e1 fd ff ff       	jmp    4124 <send_headers+0x2b4>
    4343:	89 db                	mov    %ebx,%ebx
    4345:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    434b:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4350:	e9 63 fd ff ff       	jmp    40b8 <send_headers+0x248>
    4355:	89 db                	mov    %ebx,%ebx
    4357:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    435d:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4362:	e9 bd fd ff ff       	jmp    4124 <send_headers+0x2b4>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4367:	48 8b 0d b2 4c 00 00 	mov    0x4cb2(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    436e:	ba 28 00 00 00       	mov    $0x28,%edx
    4373:	be 01 00 00 00       	mov    $0x1,%esi
    4378:	48 8d 3d c1 20 00 00 	lea    0x20c1(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    437f:	e8 5c e1 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    4384:	bf 01 00 00 00       	mov    $0x1,%edi
    4389:	e8 32 e1 ff ff       	call   24c0 <exit@plt>
}
    438e:	e8 9d df ff ff       	call   2330 <__stack_chk_fail@plt>
    4393:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    439e:	66 90                	xchg   %ax,%ax

00000000000043a0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    43a0:	f3 0f 1e fa          	endbr64
    43a4:	55                   	push   %rbp
    43a5:	48 89 e5             	mov    %rsp,%rbp
    43a8:	41 56                	push   %r14
    43aa:	41 55                	push   %r13
    43ac:	41 54                	push   %r12
    43ae:	53                   	push   %rbx
    43af:	ff 15 33 4c 00 00    	call   *0x4c33(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    43b5:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    43b8:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    43bb:	48 89 f3             	mov    %rsi,%rbx
    43be:	49 89 d6             	mov    %rdx,%r14
    void *buf = malloc(size);
    43c1:	e8 5a e0 ff ff       	call   2420 <malloc@plt>
    43c6:	49 89 c4             	mov    %rax,%r12
    if (!buf) {
    43c9:	48 85 c0             	test   %rax,%rax
    43cc:	74 69                	je     4437 <copy_file_contents+0x97>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    43ce:	4c 89 ef             	mov    %r13,%rdi
    43d1:	31 f6                	xor    %esi,%esi
    43d3:	31 c0                	xor    %eax,%eax
    43d5:	e8 b6 e0 ff ff       	call   2490 <open@plt>
    43da:	41 89 c5             	mov    %eax,%r13d
    if (fd < 0)
    43dd:	85 c0                	test   %eax,%eax
    43df:	0f 88 98 e1 ff ff    	js     257d <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    43e5:	48 89 da             	mov    %rbx,%rdx
    43e8:	4c 89 e6             	mov    %r12,%rsi
    43eb:	89 c7                	mov    %eax,%edi
    43ed:	e8 9e df ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    43f2:	48 98                	cltq
    43f4:	48 39 d8             	cmp    %rbx,%rax
    43f7:	7c 1f                	jl     4418 <copy_file_contents+0x78>
    close(fd);
    43f9:	44 89 ef             	mov    %r13d,%edi
    43fc:	e8 6f df ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    4401:	4d 89 26             	mov    %r12,(%r14)
    iov->iov_len = file_size;
    4404:	49 89 5e 08          	mov    %rbx,0x8(%r14)
}
    4408:	5b                   	pop    %rbx
    4409:	41 5c                	pop    %r12
    440b:	41 5d                	pop    %r13
    440d:	41 5e                	pop    %r14
    440f:	5d                   	pop    %rbp
    4410:	c3                   	ret
    4411:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4418:	48 8b 0d 01 4c 00 00 	mov    0x4c01(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    441f:	ba 1a 00 00 00       	mov    $0x1a,%edx
    4424:	be 01 00 00 00       	mov    $0x1,%esi
    4429:	48 8d 3d a0 1c 00 00 	lea    0x1ca0(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    4430:	e8 ab e0 ff ff       	call   24e0 <fwrite@plt>
    4435:	eb c2                	jmp    43f9 <copy_file_contents+0x59>
    4437:	48 8b 0d e2 4b 00 00 	mov    0x4be2(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    443e:	ba 28 00 00 00       	mov    $0x28,%edx
    4443:	be 01 00 00 00       	mov    $0x1,%esi
    4448:	48 8d 3d f1 1f 00 00 	lea    0x1ff1(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    444f:	e8 8c e0 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    4454:	bf 01 00 00 00       	mov    $0x1,%edi
    4459:	e8 62 e0 ff ff       	call   24c0 <exit@plt>
    445e:	66 90                	xchg   %ax,%ax

0000000000004460 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4460:	f3 0f 1e fa          	endbr64
    4464:	55                   	push   %rbp
    4465:	48 89 e5             	mov    %rsp,%rbp
    4468:	ff 15 7a 4b 00 00    	call   *0x4b7a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    446e:	8b 46 44             	mov    0x44(%rsi),%eax
    4471:	48 89 fa             	mov    %rdi,%rdx
    4474:	48 89 f7             	mov    %rsi,%rdi
    4477:	8d 70 01             	lea    0x1(%rax),%esi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    447a:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4480:	48 8b 07             	mov    (%rdi),%rax
    4483:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4486:	f6 c1 02             	test   $0x2,%cl
    4489:	74 00                	je     448b <add_write_request+0x2b>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    448b:	89 f0                	mov    %esi,%eax
    448d:	44 29 c0             	sub    %r8d,%eax
    4490:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4493:	0f 82 f0 e0 ff ff    	jb     2589 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4499:	c1 e9 0a             	shr    $0xa,%ecx
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    449c:	8b 47 44             	mov    0x44(%rdi),%eax
    449f:	23 47 58             	and    0x58(%rdi),%eax
		sq->sqe_tail = next;
    44a2:	89 77 44             	mov    %esi,0x44(%rdi)
	if (ring->flags & IORING_SETUP_SQE128)
    44a5:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    44a8:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    44ab:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    44af:	d3 e0                	shl    %cl,%eax
    44b1:	8b 4a 04             	mov    0x4(%rdx),%ecx
    44b4:	48 c1 e0 06          	shl    $0x6,%rax
    44b8:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    44bc:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    44c2:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    44c5:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    44c9:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    44cf:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    44d7:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    44db:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    44de:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    44e5:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    44ed:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    44f1:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    44f5:	e8 46 de ff ff       	call   2340 <io_uring_submit@plt>
}
    44fa:	31 c0                	xor    %eax,%eax
    44fc:	5d                   	pop    %rbp
    44fd:	c3                   	ret
    44fe:	66 90                	xchg   %ax,%ax

0000000000004500 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4500:	f3 0f 1e fa          	endbr64
    4504:	55                   	push   %rbp
    4505:	48 89 e5             	mov    %rsp,%rbp
    4508:	41 56                	push   %r14
    450a:	41 55                	push   %r13
    450c:	41 54                	push   %r12
    450e:	53                   	push   %rbx
    450f:	ff 15 d3 4a 00 00    	call   *0x4ad3(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    4515:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4518:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    451e:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4521:	83 c0 01             	add    $0x1,%eax
    4524:	48 89 f3             	mov    %rsi,%rbx
    4527:	41 89 fe             	mov    %edi,%r14d
		head = IO_URING_READ_ONCE(*sq->khead);
    452a:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    452c:	f6 c1 02             	test   $0x2,%cl
    452f:	74 00                	je     4531 <add_read_request+0x31>
	if (next - head <= sq->ring_entries) {
    4531:	89 c2                	mov    %eax,%edx
    4533:	29 f2                	sub    %esi,%edx
    4535:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4538:	0f 82 5b e0 ff ff    	jb     2599 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    453e:	44 8b 63 44          	mov    0x44(%rbx),%r12d
	if (ring->flags & IORING_SETUP_SQE128)
    4542:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    4545:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4548:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    454d:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4550:	44 23 63 58          	and    0x58(%rbx),%r12d
    4554:	41 d3 e4             	shl    %cl,%r12d
    4557:	49 c1 e4 06          	shl    $0x6,%r12
    455b:	4c 03 63 38          	add    0x38(%rbx),%r12
    455f:	e8 bc de ff ff       	call   2420 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    4564:	be 01 00 00 00       	mov    $0x1,%esi
    4569:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    456e:	49 89 c5             	mov    %rax,%r13
    req->iov[0].iov_base = malloc(READ_SZ);
    4571:	e8 2a de ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    4576:	45 89 75 08          	mov    %r14d,0x8(%r13)
	sqe->addr3 = 0;
    457a:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    457e:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4581:	49 89 45 10          	mov    %rax,0x10(%r13)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4585:	49 8d 45 10          	lea    0x10(%r13),%rax
    req->iov[0].iov_len = READ_SZ;
    4589:	49 c7 45 18 00 20 00 00 	movq   $0x2000,0x18(%r13)
    req->event_type = EVENT_TYPE_READ;
    4591:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
	sqe->fd = fd;
    4599:	45 89 74 24 04       	mov    %r14d,0x4(%r12)
	sqe->user_data = (unsigned long) data;
    459e:	4d 89 6c 24 20       	mov    %r13,0x20(%r12)
	sqe->opcode = (__u8) op;
    45a3:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->off = offset;
    45ab:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    45b4:	49 89 44 24 10       	mov    %rax,0x10(%r12)
	sqe->len = len;
    45b9:	49 c7 44 24 18 01 00 00 00 	movq   $0x1,0x18(%r12)
	sqe->buf_index = 0;
    45c2:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->addr3 = 0;
    45cb:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    io_uring_submit(ring);
    45d1:	e8 6a dd ff ff       	call   2340 <io_uring_submit@plt>
}
    45d6:	5b                   	pop    %rbx
    45d7:	31 c0                	xor    %eax,%eax
    45d9:	41 5c                	pop    %r12
    45db:	41 5d                	pop    %r13
    45dd:	41 5e                	pop    %r14
    45df:	5d                   	pop    %rbp
    45e0:	c3                   	ret
    45e1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    45ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000045f0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    45f0:	f3 0f 1e fa          	endbr64
    45f4:	55                   	push   %rbp
    45f5:	48 89 e5             	mov    %rsp,%rbp
    45f8:	41 57                	push   %r15
    45fa:	41 56                	push   %r14
    45fc:	41 55                	push   %r13
    45fe:	41 54                	push   %r12
    4600:	53                   	push   %rbx
    4601:	48 83 ec 08          	sub    $0x8,%rsp
    4605:	ff 15 dd 49 00 00    	call   *0x49dd(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    460b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    460e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4613:	41 89 f7             	mov    %esi,%r15d
    4616:	49 89 d4             	mov    %rdx,%r12
    void *buf = malloc(size);
    4619:	e8 02 de ff ff       	call   2420 <malloc@plt>
    461e:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4621:	48 85 c0             	test   %rax,%rax
    4624:	0f 84 eb 00 00 00    	je     4715 <_send_static_string_content+0x125>
    unsigned long slen = strlen(str);
    462a:	4c 89 ef             	mov    %r13,%rdi
    462d:	e8 ee dc ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4632:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    4639:	44 89 7b 08          	mov    %r15d,0x8(%rbx)
    void *buf = malloc(size);
    463d:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4640:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    4643:	e8 d8 dd ff ff       	call   2420 <malloc@plt>
    4648:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    464b:	48 85 c0             	test   %rax,%rax
    464e:	0f 84 c1 00 00 00    	je     4715 <_send_static_string_content+0x125>
    req->iov[0].iov_base = zh_malloc(slen);
    4654:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4658:	4c 89 f2             	mov    %r14,%rdx
    465b:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    465e:	4c 89 73 18          	mov    %r14,0x18(%rbx)
    4662:	e8 89 dd ff ff       	call   23f0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4667:	41 8b 44 24 44       	mov    0x44(%r12),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    466c:	41 8b 8c 24 c0 00 00 00 	mov    0xc0(%r12),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4674:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4677:	49 8b 04 24          	mov    (%r12),%rax
    467b:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    467d:	f6 c1 02             	test   $0x2,%cl
    4680:	0f 85 8a 00 00 00    	jne    4710 <_send_static_string_content+0x120>
	if (next - head <= sq->ring_entries) {
    4686:	89 d0                	mov    %edx,%eax
    4688:	29 f0                	sub    %esi,%eax
    468a:	41 39 44 24 5c       	cmp    %eax,0x5c(%r12)
    468f:	0f 82 0e df ff ff    	jb     25a3 <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4695:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4698:	41 8b 44 24 44       	mov    0x44(%r12),%eax
    469d:	41 23 44 24 58       	and    0x58(%r12),%eax
    io_uring_submit(ring);
    46a2:	4c 89 e7             	mov    %r12,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    46a5:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    46a8:	41 89 54 24 44       	mov    %edx,0x44(%r12)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    46ad:	8b 53 04             	mov    0x4(%rbx),%edx
	sqe->addr3 = 0;
    46b0:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    46b4:	d3 e0                	shl    %cl,%eax
    46b6:	8b 4b 08             	mov    0x8(%rbx),%ecx
    req->event_type = EVENT_TYPE_WRITE;
    46b9:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    46bf:	48 c1 e0 06          	shl    $0x6,%rax
    46c3:	49 03 44 24 38       	add    0x38(%r12),%rax
	sqe->fd = fd;
    46c8:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    46cb:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    46cf:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    46d5:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    46dd:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    46e1:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    46e4:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    46eb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    46f3:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    46f7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    46fb:	48 83 c4 08          	add    $0x8,%rsp
    46ff:	5b                   	pop    %rbx
    4700:	41 5c                	pop    %r12
    4702:	41 5d                	pop    %r13
    4704:	41 5e                	pop    %r14
    4706:	41 5f                	pop    %r15
    4708:	5d                   	pop    %rbp
    io_uring_submit(ring);
    4709:	e9 32 dc ff ff       	jmp    2340 <io_uring_submit@plt>
    470e:	66 90                	xchg   %ax,%ax
		head = io_uring_smp_load_acquire(sq->khead);
    4710:	e9 71 ff ff ff       	jmp    4686 <_send_static_string_content+0x96>
    4715:	48 8b 0d 04 49 00 00 	mov    0x4904(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    471c:	ba 28 00 00 00       	mov    $0x28,%edx
    4721:	be 01 00 00 00       	mov    $0x1,%esi
    4726:	48 8d 3d 13 1d 00 00 	lea    0x1d13(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    472d:	e8 ae dd ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    4732:	bf 01 00 00 00       	mov    $0x1,%edi
    4737:	e8 84 dd ff ff       	call   24c0 <exit@plt>
    473c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004740 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4740:	f3 0f 1e fa          	endbr64
    4744:	55                   	push   %rbp
    4745:	48 89 e5             	mov    %rsp,%rbp
    4748:	ff 15 9a 48 00 00    	call   *0x489a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
}
    474e:	5d                   	pop    %rbp
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    474f:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4752:	89 fe                	mov    %edi,%esi
    4754:	48 8b 3d bd 48 00 00 	mov    0x48bd(%rip),%rdi        # 9018 <unimplemented_content>
    475b:	e9 90 fe ff ff       	jmp    45f0 <_send_static_string_content>

0000000000004760 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4760:	f3 0f 1e fa          	endbr64
    4764:	55                   	push   %rbp
    4765:	48 89 e5             	mov    %rsp,%rbp
    4768:	ff 15 7a 48 00 00    	call   *0x487a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
}
    476e:	5d                   	pop    %rbp
void handle_http_404(int client_socket, struct io_uring *ring) {
    476f:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4772:	89 fe                	mov    %edi,%esi
    4774:	48 8b 3d 95 48 00 00 	mov    0x4895(%rip),%rdi        # 9010 <http_404_content>
    477b:	e9 70 fe ff ff       	jmp    45f0 <_send_static_string_content>

0000000000004780 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4780:	f3 0f 1e fa          	endbr64
    4784:	55                   	push   %rbp
    4785:	48 89 e5             	mov    %rsp,%rbp
    4788:	41 57                	push   %r15
    478a:	41 56                	push   %r14
    478c:	41 55                	push   %r13
    478e:	41 54                	push   %r12
    4790:	53                   	push   %rbx
    4791:	48 81 ec a8 04 00 00 	sub    $0x4a8,%rsp
    4798:	ff 15 4a 48 00 00    	call   *0x484a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    479e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    47a7:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    47ab:	31 c0                	xor    %eax,%eax
    47ad:	49 89 fc             	mov    %rdi,%r12
    47b0:	41 89 f5             	mov    %esi,%r13d
    47b3:	49 89 d6             	mov    %rdx,%r14
    if (path[strlen(path) - 1] == '/') {
    47b6:	e8 65 db ff ff       	call   2320 <strlen@plt>
    47bb:	41 80 7c 04 ff 2f    	cmpb   $0x2f,-0x1(%r12,%rax,1)
    47c1:	48 89 c3             	mov    %rax,%rbx
    47c4:	0f 84 b6 00 00 00    	je     4880 <handle_get_method+0x100>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    47ca:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    47cf:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    47d3:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    47d8:	4c 89 e6             	mov    %r12,%rsi
    47db:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    47e2:	66 89 85 c4 fb ff ff 	mov    %ax,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    47e9:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    47f0:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    47fa:	e8 d1 db ff ff       	call   23d0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    47ff:	48 8d b5 30 fb ff ff 	lea    -0x4d0(%rbp),%rsi
    4806:	4c 89 ff             	mov    %r15,%rdi
    4809:	e8 d2 db ff ff       	call   23e0 <stat@plt>
    480e:	83 f8 ff             	cmp    $0xffffffff,%eax
    4811:	0f 84 41 01 00 00    	je     4958 <handle_get_method+0x1d8>
        if (S_ISREG(path_stat.st_mode)) {
    4817:	8b 85 48 fb ff ff    	mov    -0x4b8(%rbp),%eax
    481d:	25 00 f0 00 00       	and    $0xf000,%eax
    4822:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4827:	0f 84 b3 00 00 00    	je     48e0 <handle_get_method+0x160>
    _send_static_string_content(http_404_content, client_socket, ring);
    482d:	48 8b 3d dc 47 00 00 	mov    0x47dc(%rip),%rdi        # 9010 <http_404_content>
    4834:	4c 89 f2             	mov    %r14,%rdx
    4837:	44 89 ee             	mov    %r13d,%esi
    483a:	e8 b1 fd ff ff       	call   45f0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    483f:	4c 89 fa             	mov    %r15,%rdx
    4842:	bf 01 00 00 00       	mov    $0x1,%edi
    4847:	31 c0                	xor    %eax,%eax
    4849:	48 8d 35 d0 18 00 00 	lea    0x18d0(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    4850:	e8 0b dc ff ff       	call   2460 <__printf_chk@plt>
}
    4855:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    4859:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4862:	0f 85 20 01 00 00    	jne    4988 <handle_get_method+0x208>
    4868:	48 81 c4 a8 04 00 00 	add    $0x4a8,%rsp
    486f:	5b                   	pop    %rbx
    4870:	41 5c                	pop    %r12
    4872:	41 5d                	pop    %r13
    4874:	41 5e                	pop    %r14
    4876:	41 5f                	pop    %r15
    4878:	5d                   	pop    %rbp
    4879:	c3                   	ret
    487a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4880:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4885:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
    488c:	4c 89 e6             	mov    %r12,%rsi
    488f:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4894:	66 89 95 c4 fb ff ff 	mov    %dx,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    489b:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    489e:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
    48a5:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    48af:	e8 1c db ff ff       	call   23d0 <__memcpy_chk@plt>
    48b4:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    48b9:	49 8d 7c 1f 06       	lea    0x6(%r15,%rbx,1),%rdi
    48be:	ba 0b 00 00 00       	mov    $0xb,%edx
    48c3:	48 29 d9             	sub    %rbx,%rcx
    48c6:	48 8d 35 1e 18 00 00 	lea    0x181e(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    48cd:	e8 fe da ff ff       	call   23d0 <__memcpy_chk@plt>
    48d2:	e9 28 ff ff ff       	jmp    47ff <handle_get_method+0x7f>
    48d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    48e0:	bf 70 00 00 00       	mov    $0x70,%edi
    48e5:	e8 36 db ff ff       	call   2420 <malloc@plt>
    48ea:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    48ed:	48 85 c0             	test   %rax,%rax
    48f0:	0f 84 97 00 00 00    	je     498d <handle_get_method+0x20d>
            req->client_socket = client_socket;
    48f6:	44 89 68 08          	mov    %r13d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    48fa:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    4901:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4905:	4c 89 ff             	mov    %r15,%rdi
            req->iovec_count = 6;
    4908:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    490f:	e8 5c f5 ff ff       	call   3e70 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4914:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    491b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    491f:	4c 89 ff             	mov    %r15,%rdi
    4922:	e8 79 fa ff ff       	call   43a0 <copy_file_contents>
    4927:	4c 89 fa             	mov    %r15,%rdx
    492a:	bf 01 00 00 00       	mov    $0x1,%edi
    492f:	31 c0                	xor    %eax,%eax
    4931:	48 8b 8d 60 fb ff ff 	mov    -0x4a0(%rbp),%rcx
    4938:	48 8d 35 cf 17 00 00 	lea    0x17cf(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    493f:	e8 1c db ff ff       	call   2460 <__printf_chk@plt>
            add_write_request(req, ring);
    4944:	4c 89 f6             	mov    %r14,%rsi
    4947:	48 89 df             	mov    %rbx,%rdi
    494a:	e8 11 fb ff ff       	call   4460 <add_write_request>
    494f:	e9 01 ff ff ff       	jmp    4855 <handle_get_method+0xd5>
    4954:	0f 1f 40 00          	nopl   0x0(%rax)
    4958:	4c 89 fa             	mov    %r15,%rdx
    495b:	4c 89 e1             	mov    %r12,%rcx
    495e:	48 8d 35 91 17 00 00 	lea    0x1791(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    4965:	31 c0                	xor    %eax,%eax
    4967:	bf 01 00 00 00       	mov    $0x1,%edi
    496c:	e8 ef da ff ff       	call   2460 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    4971:	48 8b 3d 98 46 00 00 	mov    0x4698(%rip),%rdi        # 9010 <http_404_content>
    4978:	4c 89 f2             	mov    %r14,%rdx
    497b:	44 89 ee             	mov    %r13d,%esi
    497e:	e8 6d fc ff ff       	call   45f0 <_send_static_string_content>
}
    4983:	e9 cd fe ff ff       	jmp    4855 <handle_get_method+0xd5>
}
    4988:	e8 a3 d9 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    498d:	48 8b 0d 8c 46 00 00 	mov    0x468c(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4994:	ba 28 00 00 00       	mov    $0x28,%edx
    4999:	be 01 00 00 00       	mov    $0x1,%esi
    499e:	48 8d 3d 9b 1a 00 00 	lea    0x1a9b(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    49a5:	e8 36 db ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    49aa:	bf 01 00 00 00       	mov    $0x1,%edi
    49af:	e8 0c db ff ff       	call   24c0 <exit@plt>
    49b4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    49bf:	90                   	nop

00000000000049c0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    49c0:	f3 0f 1e fa          	endbr64
    49c4:	55                   	push   %rbp
    49c5:	48 89 e5             	mov    %rsp,%rbp
    49c8:	41 57                	push   %r15
    49ca:	41 56                	push   %r14
    49cc:	41 55                	push   %r13
    49ce:	41 54                	push   %r12
    49d0:	53                   	push   %rbx
    49d1:	48 83 ec 28          	sub    $0x28,%rsp
    49d5:	ff 15 0d 46 00 00    	call   *0x460d(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    method = strtok_r(method_buffer, " ", &saveptr);
    49db:	4c 8d 35 a3 16 00 00 	lea    0x16a3(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    49e2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    49eb:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    49ef:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    49f1:	4c 8d 7d c0          	lea    -0x40(%rbp),%r15
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    49f5:	41 89 f4             	mov    %esi,%r12d
    49f8:	49 89 d5             	mov    %rdx,%r13
    method = strtok_r(method_buffer, " ", &saveptr);
    49fb:	4c 89 f6             	mov    %r14,%rsi
    49fe:	4c 89 fa             	mov    %r15,%rdx
    4a01:	e8 7a d9 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4a06:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    4a09:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    4a0c:	84 d2                	test   %dl,%dl
    4a0e:	88 55 bf             	mov    %dl,-0x41(%rbp)
    4a11:	74 22                	je     4a35 <handle_http_method+0x75>
        *str = (char)tolower(*str);
    4a13:	e8 18 db ff ff       	call   2530 <__ctype_tolower_loc@plt>
    4a18:	48 0f be 55 bf       	movsbq -0x41(%rbp),%rdx
    4a1d:	48 89 d9             	mov    %rbx,%rcx
    4a20:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    4a23:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    4a27:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    4a2a:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    4a2d:	48 0f be 11          	movsbq (%rcx),%rdx
    4a31:	84 d2                	test   %dl,%dl
    4a33:	75 eb                	jne    4a20 <handle_http_method+0x60>
    path = strtok_r(NULL, " ", &saveptr);
    4a35:	4c 89 fa             	mov    %r15,%rdx
    4a38:	4c 89 f6             	mov    %r14,%rsi
    4a3b:	31 ff                	xor    %edi,%edi
    4a3d:	e8 3e d9 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4a42:	48 8d 35 ea 16 00 00 	lea    0x16ea(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    4a49:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4a4c:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    4a4f:	e8 5c d9 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4a54:	4c 89 ea             	mov    %r13,%rdx
    4a57:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4a5a:	85 c0                	test   %eax,%eax
    4a5c:	75 2a                	jne    4a88 <handle_http_method+0xc8>
        handle_get_method(path, client_socket, ring);
    4a5e:	4c 89 f7             	mov    %r14,%rdi
    4a61:	e8 1a fd ff ff       	call   4780 <handle_get_method>
}
    4a66:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    4a6a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4a73:	75 21                	jne    4a96 <handle_http_method+0xd6>
    4a75:	48 83 c4 28          	add    $0x28,%rsp
    4a79:	5b                   	pop    %rbx
    4a7a:	41 5c                	pop    %r12
    4a7c:	41 5d                	pop    %r13
    4a7e:	41 5e                	pop    %r14
    4a80:	41 5f                	pop    %r15
    4a82:	5d                   	pop    %rbp
    4a83:	c3                   	ret
    4a84:	0f 1f 40 00          	nopl   0x0(%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4a88:	48 8b 3d 89 45 00 00 	mov    0x4589(%rip),%rdi        # 9018 <unimplemented_content>
    4a8f:	e8 5c fb ff ff       	call   45f0 <_send_static_string_content>
}
    4a94:	eb d0                	jmp    4a66 <handle_http_method+0xa6>
    4a96:	e8 95 d8 ff ff       	call   2330 <__stack_chk_fail@plt>
    4a9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004aa0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4aa0:	f3 0f 1e fa          	endbr64
    4aa4:	55                   	push   %rbp
    4aa5:	48 89 e5             	mov    %rsp,%rbp
    4aa8:	ff 15 3a 45 00 00    	call   *0x453a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    for (int i = 0; i < dest_sz; i++) {
    4aae:	85 d2                	test   %edx,%edx
    4ab0:	7e 36                	jle    4ae8 <get_line+0x48>
    4ab2:	48 63 d2             	movslq %edx,%rdx
    4ab5:	48 83 c7 01          	add    $0x1,%rdi
    4ab9:	48 01 f2             	add    %rsi,%rdx
    4abc:	eb 0f                	jmp    4acd <get_line+0x2d>
    4abe:	66 90                	xchg   %ax,%ax
    4ac0:	48 83 c6 01          	add    $0x1,%rsi
    4ac4:	48 83 c7 01          	add    $0x1,%rdi
    4ac8:	48 39 d6             	cmp    %rdx,%rsi
    4acb:	74 1b                	je     4ae8 <get_line+0x48>
        dest[i] = src[i];
    4acd:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4ad1:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4ad3:	3c 0d                	cmp    $0xd,%al
    4ad5:	75 e9                	jne    4ac0 <get_line+0x20>
    4ad7:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4ada:	75 e4                	jne    4ac0 <get_line+0x20>
            return 0;
    4adc:	31 c0                	xor    %eax,%eax
            dest[i] = '\0';
    4ade:	c6 06 00             	movb   $0x0,(%rsi)
}
    4ae1:	5d                   	pop    %rbp
    4ae2:	c3                   	ret
    4ae3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    return 1;
    4ae8:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4aed:	5d                   	pop    %rbp
    4aee:	c3                   	ret
    4aef:	90                   	nop

0000000000004af0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4af0:	f3 0f 1e fa          	endbr64
    4af4:	55                   	push   %rbp
    4af5:	48 89 e5             	mov    %rsp,%rbp
    4af8:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    4aff:	ff 15 e3 44 00 00    	call   *0x44e3(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    4b05:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4b09:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b12:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
    4b16:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4b18:	4c 8d 95 f0 fb ff ff 	lea    -0x410(%rbp),%r10
    4b1f:	4c 8d 4d f0          	lea    -0x10(%rbp),%r9
    4b23:	4c 89 d0             	mov    %r10,%rax
    4b26:	eb 15                	jmp    4b3d <handle_client_request+0x4d>
    4b28:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4b30:	48 83 c0 01          	add    $0x1,%rax
    4b34:	48 83 c1 01          	add    $0x1,%rcx
    4b38:	4c 39 c8             	cmp    %r9,%rax
    4b3b:	74 43                	je     4b80 <handle_client_request+0x90>
        dest[i] = src[i];
    4b3d:	44 0f b6 01          	movzbl (%rcx),%r8d
    4b41:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4b44:	41 80 f8 0d          	cmp    $0xd,%r8b
    4b48:	75 e6                	jne    4b30 <handle_client_request+0x40>
    4b4a:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4b4e:	75 e0                	jne    4b30 <handle_client_request+0x40>
            dest[i] = '\0';
    4b50:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4b53:	8b 47 08             	mov    0x8(%rdi),%eax
    4b56:	48 89 f2             	mov    %rsi,%rdx
    4b59:	4c 89 d7             	mov    %r10,%rdi
    4b5c:	89 c6                	mov    %eax,%esi
    4b5e:	e8 5d fe ff ff       	call   49c0 <handle_http_method>
}
    4b63:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    4b67:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b70:	75 35                	jne    4ba7 <handle_client_request+0xb7>
    4b72:	c9                   	leave
    4b73:	31 c0                	xor    %eax,%eax
    4b75:	c3                   	ret
    4b76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4b80:	48 8b 0d 99 44 00 00 	mov    0x4499(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4b87:	ba 12 00 00 00       	mov    $0x12,%edx
    4b8c:	be 01 00 00 00       	mov    $0x1,%esi
    4b91:	48 8d 3d 9f 15 00 00 	lea    0x159f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    4b98:	e8 43 d9 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    4b9d:	bf 01 00 00 00       	mov    $0x1,%edi
    4ba2:	e8 19 d9 ff ff       	call   24c0 <exit@plt>
}
    4ba7:	e8 84 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
    4bac:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004bb0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4bb0:	f3 0f 1e fa          	endbr64
    4bb4:	55                   	push   %rbp
    4bb5:	48 89 e5             	mov    %rsp,%rbp
    4bb8:	41 54                	push   %r12
    4bba:	53                   	push   %rbx
    4bbb:	ff 15 27 44 00 00    	call   *0x4427(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    4bc1:	8b 41 44             	mov    0x44(%rcx),%eax
    4bc4:	83 c0 01             	add    $0x1,%eax
    4bc7:	48 89 cb             	mov    %rcx,%rbx
	if (ring->flags & IORING_SETUP_SQE128)
    4bca:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    4bd0:	4c 8b 03             	mov    (%rbx),%r8
    4bd3:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4bd6:	f6 c1 02             	test   $0x2,%cl
    4bd9:	74 00                	je     4bdb <add_accept_request+0x2b>
	if (next - head <= sq->ring_entries) {
    4bdb:	41 89 c0             	mov    %eax,%r8d
    4bde:	45 29 c8             	sub    %r9d,%r8d
    4be1:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4be5:	0f 82 c8 d9 ff ff    	jb     25b3 <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4beb:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4bee:	44 8b 63 44          	mov    0x44(%rbx),%r12d
    4bf2:	44 23 63 58          	and    0x58(%rbx),%r12d
		sq->sqe_tail = next;
    4bf6:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4bf9:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4bfc:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c00:	41 d3 e4             	shl    %cl,%r12d
    4c03:	49 c1 e4 06          	shl    $0x6,%r12
    4c07:	4c 03 63 38          	add    0x38(%rbx),%r12
	sqe->fd = fd;
    4c0b:	41 89 7c 24 04       	mov    %edi,0x4(%r12)
  struct Request *req = malloc(sizeof(*req));
    4c10:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4c15:	41 c7 04 24 0d 00 00 00 	movl   $0xd,(%r12)
	sqe->off = offset;
    4c1d:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
	sqe->addr = (unsigned long) addr;
    4c22:	49 89 74 24 10       	mov    %rsi,0x10(%r12)
	sqe->buf_index = 0;
    4c27:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->len = len;
    4c30:	49 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%r12)
	sqe->addr3 = 0;
    4c39:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    4c3f:	e8 dc d7 ff ff       	call   2420 <malloc@plt>
  io_uring_submit(ring);
    4c44:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4c47:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4c4d:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
    4c52:	5b                   	pop    %rbx
    4c53:	41 5c                	pop    %r12
    4c55:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4c56:	e9 e5 d6 ff ff       	jmp    2340 <io_uring_submit@plt>
    4c5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004c60 <io_thread>:
void* io_thread(void *arg) {
    4c60:	f3 0f 1e fa          	endbr64
    4c64:	55                   	push   %rbp
    4c65:	48 89 e5             	mov    %rsp,%rbp
    4c68:	41 57                	push   %r15
    4c6a:	41 56                	push   %r14
    4c6c:	41 55                	push   %r13
    4c6e:	41 54                	push   %r12
    4c70:	53                   	push   %rbx
    4c71:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4c78:	ff 15 6a 43 00 00    	call   *0x436a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4c7e:	31 d2                	xor    %edx,%edx
  struct io_uring ring = *data->ring;
    4c80:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4c89:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    4c8d:	48 8b 47 40          	mov    0x40(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4c91:	48 8d 9d e0 fa ff ff 	lea    -0x520(%rbp),%rbx
void* io_thread(void *arg) {
    4c98:	49 89 fc             	mov    %rdi,%r12
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4c9b:	bf 00 01 00 00       	mov    $0x100,%edi
    4ca0:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4ca3:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4ca7:	0f 29 8d e0 fa ff ff 	movaps %xmm1,-0x520(%rbp)
    4cae:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4cb3:	0f 29 95 f0 fa ff ff 	movaps %xmm2,-0x510(%rbp)
    4cba:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4cbf:	0f 29 9d 00 fb ff ff 	movaps %xmm3,-0x500(%rbp)
    4cc6:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4ccb:	0f 29 a5 10 fb ff ff 	movaps %xmm4,-0x4f0(%rbp)
    4cd2:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4cd7:	0f 29 ad 20 fb ff ff 	movaps %xmm5,-0x4e0(%rbp)
    4cde:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4ce3:	0f 29 b5 30 fb ff ff 	movaps %xmm6,-0x4d0(%rbp)
    4cea:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4cef:	0f 29 bd 40 fb ff ff 	movaps %xmm7,-0x4c0(%rbp)
    4cf6:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4cfb:	0f 29 8d 50 fb ff ff 	movaps %xmm1,-0x4b0(%rbp)
    4d02:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4d0a:	0f 29 95 60 fb ff ff 	movaps %xmm2,-0x4a0(%rbp)
    4d11:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4d19:	0f 29 9d 70 fb ff ff 	movaps %xmm3,-0x490(%rbp)
    4d20:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4d28:	0f 29 a5 80 fb ff ff 	movaps %xmm4,-0x480(%rbp)
    4d2f:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4d37:	0f 29 ad 90 fb ff ff 	movaps %xmm5,-0x470(%rbp)
    4d3e:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4d46:	0f 29 b5 a0 fb ff ff 	movaps %xmm6,-0x460(%rbp)
    4d4d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4d54:	48 89 85 b0 fb ff ff 	mov    %rax,-0x450(%rbp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4d5b:	e8 a0 d6 ff ff       	call   2400 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4d60:	49 8b 7c 24 40       	mov    0x40(%r12),%rdi
    4d65:	31 f6                	xor    %esi,%esi
    4d67:	e8 94 d7 ff ff       	call   2500 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4d6c:	31 d2                	xor    %edx,%edx
    4d6e:	be 01 00 00 00       	mov    $0x1,%esi
    4d73:	bf 02 00 00 00       	mov    $0x2,%edi
    4d78:	e8 d3 d7 ff ff       	call   2550 <socket@plt>
    4d7d:	89 85 ac fa ff ff    	mov    %eax,-0x554(%rbp)
  if (sock == -1)
    4d83:	83 f8 ff             	cmp    $0xffffffff,%eax
    4d86:	0f 84 69 d8 ff ff    	je     25f5 <io_thread.cold+0x38>
    4d8c:	89 c7                	mov    %eax,%edi
  if (setsockopt(sock,
    4d8e:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4d94:	ba 02 00 00 00       	mov    $0x2,%edx
    4d99:	be 01 00 00 00       	mov    $0x1,%esi
    4d9e:	48 8d 8d b0 fa ff ff 	lea    -0x550(%rbp),%rcx
  int enable = 1;
    4da5:	c7 85 b0 fa ff ff 01 00 00 00 	movl   $0x1,-0x550(%rbp)
  if (setsockopt(sock,
    4daf:	e8 4c d5 ff ff       	call   2300 <setsockopt@plt>
    4db4:	85 c0                	test   %eax,%eax
    4db6:	0f 88 0d d8 ff ff    	js     25c9 <io_thread.cold+0xc>
  if (bind(sock,
    4dbc:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4dc2:	ba 10 00 00 00       	mov    $0x10,%edx
  return __builtin___memset_chk (__dest, __ch, __len,
    4dc7:	48 8d b5 c0 fa ff ff 	lea    -0x540(%rbp),%rsi
    4dce:	48 c7 85 c4 fa ff ff 00 00 00 00 	movq   $0x0,-0x53c(%rbp)
    4dd9:	c7 85 cc fa ff ff 00 00 00 00 	movl   $0x0,-0x534(%rbp)
  srv_addr.sin_family = AF_INET;
    4de3:	c7 85 c0 fa ff ff 02 00 00 50 	movl   $0x50000002,-0x540(%rbp)
  if (bind(sock,
    4ded:	e8 7e d6 ff ff       	call   2470 <bind@plt>
    4df2:	85 c0                	test   %eax,%eax
    4df4:	0f 88 07 d8 ff ff    	js     2601 <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4dfa:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4e00:	be 0a 00 00 00       	mov    $0xa,%esi
    4e05:	e8 26 d6 ff ff       	call   2430 <listen@plt>
    4e0a:	85 c0                	test   %eax,%eax
    4e0c:	0f 88 c3 d7 ff ff    	js     25d5 <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4e12:	ba 50 00 00 00       	mov    $0x50,%edx
    4e17:	48 8d 35 5e 13 00 00 	lea    0x135e(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4e1e:	bf 01 00 00 00       	mov    $0x1,%edi
    4e23:	31 c0                	xor    %eax,%eax
    4e25:	e8 36 d6 ff ff       	call   2460 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4e2a:	48 8d 85 d0 fa ff ff 	lea    -0x530(%rbp),%rax
    4e31:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4e37:	48 89 d9             	mov    %rbx,%rcx
    4e3a:	48 8d 95 b4 fa ff ff 	lea    -0x54c(%rbp),%rdx
    4e41:	48 89 c6             	mov    %rax,%rsi
  socklen_t client_addr_len = sizeof(client_addr);
    4e44:	c7 85 b4 fa ff ff 10 00 00 00 	movl   $0x10,-0x54c(%rbp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4e4e:	48 89 95 90 fa ff ff 	mov    %rdx,-0x570(%rbp)
    4e55:	48 89 85 88 fa ff ff 	mov    %rax,-0x578(%rbp)
    4e5c:	e8 4f fd ff ff       	call   4bb0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4e61:	bf 01 00 00 00       	mov    $0x1,%edi
    4e66:	be 10 00 00 00       	mov    $0x10,%esi
    4e6b:	e8 30 d5 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    4e70:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4e75:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    4e78:	e8 a3 d5 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    4e7d:	48 85 c0             	test   %rax,%rax
    4e80:	0f 84 cf 04 00 00    	je     5355 <io_thread+0x6f5>
  iov->iov_base = zh_malloc(10);
    4e86:	49 89 06             	mov    %rax,(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    4e89:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e8f:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
  iov->iov_len = 10;
    4e95:	49 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    4e9d:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4ea0:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    4ea7:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4ea9:	f6 c1 02             	test   $0x2,%cl
    4eac:	0f 85 2e 04 00 00    	jne    52e0 <io_thread+0x680>
	if (next - head <= sq->ring_entries) {
    4eb2:	89 d0                	mov    %edx,%eax
    4eb4:	29 f0                	sub    %esi,%eax
    4eb6:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    4ebc:	0f 82 29 d7 ff ff    	jb     25eb <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4ec2:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ec5:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    4ecb:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4ecf:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ed2:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4ed8:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4edb:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4ee1:	49 8d 74 24 48       	lea    0x48(%r12),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4ee6:	41 8b 54 24 48       	mov    0x48(%r12),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4eeb:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4eed:	48 89 b5 98 fa ff ff 	mov    %rsi,-0x568(%rbp)
    4ef4:	48 c1 e0 06          	shl    $0x6,%rax
    4ef8:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    4eff:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4f05:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4f08:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4f10:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    4f14:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4f1c:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4f24:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4f28:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4f2c:	e8 0f d4 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4f31:	41 8b 44 24 2c       	mov    0x2c(%r12),%eax
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4f36:	4c 8d 8d b8 fa ff ff 	lea    -0x548(%rbp),%r9
    4f3d:	4c 8d 95 c0 fb ff ff 	lea    -0x440(%rbp),%r10
    4f44:	83 f8 01             	cmp    $0x1,%eax
    4f47:	0f 85 ed 01 00 00    	jne    513a <io_thread+0x4da>
    4f4d:	4c 89 8d a0 fa ff ff 	mov    %r9,-0x560(%rbp)
    4f54:	4c 89 95 80 fa ff ff 	mov    %r10,-0x580(%rbp)
    4f5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4f60:	48 8d 3d 2b 12 00 00 	lea    0x122b(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4f67:	e8 84 d3 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4f6c:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4f72:	8b bd 90 fb ff ff    	mov    -0x470(%rbp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4f78:	c1 e9 0b             	shr    $0xb,%ecx
    4f7b:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4f7e:	48 8b 85 50 fb ff ff 	mov    -0x4b0(%rbp),%rax
    4f85:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4f87:	48 8b b5 48 fb ff ff 	mov    -0x4b8(%rbp),%rsi
    4f8e:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4f90:	39 d0                	cmp    %edx,%eax
    4f92:	74 34                	je     4fc8 <io_thread+0x368>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4f94:	89 f8                	mov    %edi,%eax
    4f96:	21 d0                	and    %edx,%eax
    4f98:	d3 e0                	shl    %cl,%eax
    4f9a:	48 c1 e0 04          	shl    $0x4,%rax
    4f9e:	48 03 85 78 fb ff ff 	add    -0x488(%rbp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4fa5:	f6 85 a9 fb ff ff 01 	testb  $0x1,-0x457(%rbp)
    4fac:	0f 85 be 01 00 00    	jne    5170 <io_thread+0x510>
    4fb2:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4fb6:	0f 85 2c 03 00 00    	jne    52e8 <io_thread+0x688>
			if (cqe->res < 0)
    4fbc:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4fbf:	83 c2 01             	add    $0x1,%edx
    4fc2:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4fc4:	85 c0                	test   %eax,%eax
    4fc6:	79 b6                	jns    4f7e <io_thread+0x31e>
	*cqe_ptr = cqe;
    4fc8:	48 c7 85 b8 fa ff ff 00 00 00 00 	movq   $0x0,-0x548(%rbp)
	return err;
    4fd3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4fd8:	48 8b b5 a0 fa ff ff 	mov    -0x560(%rbp),%rsi
    4fdf:	45 31 c0             	xor    %r8d,%r8d
    4fe2:	31 d2                	xor    %edx,%edx
    4fe4:	48 89 df             	mov    %rbx,%rdi
    4fe7:	b9 01 00 00 00       	mov    $0x1,%ecx
    4fec:	e8 5f d4 ff ff       	call   2450 <__io_uring_get_cqe@plt>
    4ff1:	41 89 c5             	mov    %eax,%r13d
      if (cqe->user_data == 1) {
    4ff4:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    4ffb:	48 83 38 01          	cmpq   $0x1,(%rax)
    4fff:	0f 84 f3 02 00 00    	je     52f8 <io_thread+0x698>
    5005:	48 8d 3d ac 11 00 00 	lea    0x11ac(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    500c:	e8 df d2 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5011:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    5018:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    501b:	45 85 ed             	test   %r13d,%r13d
    501e:	0f 88 99 d5 ff ff    	js     25bd <io_thread.cold>
      if (cqe->res < 0) {
    5024:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5027:	45 8b 07             	mov    (%r15),%r8d
      if (cqe->res < 0) {
    502a:	85 c0                	test   %eax,%eax
    502c:	0f 88 e5 02 00 00    	js     5317 <io_thread+0x6b7>
      switch (req->event_type) {
    5032:	41 83 f8 01          	cmp    $0x1,%r8d
    5036:	0f 84 84 01 00 00    	je     51c0 <io_thread+0x560>
    503c:	41 83 f8 02          	cmp    $0x2,%r8d
    5040:	0f 84 aa 01 00 00    	je     51f0 <io_thread+0x590>
    5046:	45 85 c0             	test   %r8d,%r8d
    5049:	0f 85 59 01 00 00    	jne    51a8 <io_thread+0x548>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    504f:	48 8b 95 90 fa ff ff 	mov    -0x570(%rbp),%rdx
    5056:	48 8b b5 88 fa ff ff 	mov    -0x578(%rbp),%rsi
    505d:	48 89 d9             	mov    %rbx,%rcx
    5060:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    5066:	e8 45 fb ff ff       	call   4bb0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    506b:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    5072:	48 89 de             	mov    %rbx,%rsi
    5075:	8b 78 08             	mov    0x8(%rax),%edi
    5078:	e8 83 f4 ff ff       	call   4500 <add_read_request>
              free(req);
    507d:	4c 89 ff             	mov    %r15,%rdi
    5080:	e8 4b d2 ff ff       	call   22d0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5085:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
	if (cqe)
    508c:	48 85 c0             	test   %rax,%rax
    508f:	0f 85 13 01 00 00    	jne    51a8 <io_thread+0x548>
	unsigned int head, next = sq->sqe_tail + 1;
    5095:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    509b:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    50a1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    50a4:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    50ab:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    50ad:	f6 c1 02             	test   $0x2,%cl
    50b0:	74 00                	je     50b2 <io_thread+0x452>
	if (next - head <= sq->ring_entries) {
    50b2:	89 d0                	mov    %edx,%eax
    50b4:	29 f0                	sub    %esi,%eax
    50b6:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    50bc:	0f 82 1f d5 ff ff    	jb     25e1 <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    50c2:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50c5:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    50cb:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    50cf:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50d2:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    50d8:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    50db:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
	sqe->user_data = (unsigned long) data;
    50e1:	48 8b b5 98 fa ff ff 	mov    -0x568(%rbp),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    50e8:	41 8b 54 24 48       	mov    0x48(%r12),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50ed:	d3 e0                	shl    %cl,%eax
    50ef:	48 c1 e0 06          	shl    $0x6,%rax
    50f3:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    50fa:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5100:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5103:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    510b:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    510f:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5117:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    511f:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5123:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5127:	e8 14 d2 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    512c:	41 8b 44 24 2c       	mov    0x2c(%r12),%eax
    5131:	83 f8 01             	cmp    $0x1,%eax
    5134:	0f 84 26 fe ff ff    	je     4f60 <io_thread+0x300>
    513a:	48 8d 3d b0 10 00 00 	lea    0x10b0(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    5141:	e8 aa d1 ff ff       	call   22f0 <puts@plt>
}
    5146:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    514a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5153:	0f 85 23 02 00 00    	jne    537c <io_thread+0x71c>
    5159:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5160:	31 c0                	xor    %eax,%eax
    5162:	5b                   	pop    %rbx
    5163:	41 5c                	pop    %r12
    5165:	41 5d                	pop    %r13
    5167:	41 5e                	pop    %r14
    5169:	41 5f                	pop    %r15
    516b:	5d                   	pop    %rbp
    516c:	c3                   	ret
    516d:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5170:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5177:	48 85 c0             	test   %rax,%rax
    517a:	0f 84 58 fe ff ff    	je     4fd8 <io_thread+0x378>
      if (cqe->user_data == 1) {
    5180:	48 83 38 01          	cmpq   $0x1,(%rax)
    5184:	0f 84 6e 01 00 00    	je     52f8 <io_thread+0x698>
    518a:	48 8d 3d 27 10 00 00 	lea    0x1027(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    5191:	e8 5a d1 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5196:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    519d:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    51a0:	e9 7f fe ff ff       	jmp    5024 <io_thread+0x3c4>
    51a5:	0f 1f 00             	nopl   (%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    51a8:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
    51af:	8b 02                	mov    (%rdx),%eax
    51b1:	83 c0 01             	add    $0x1,%eax
    51b4:	89 02                	mov    %eax,(%rdx)
}
    51b6:	e9 da fe ff ff       	jmp    5095 <io_thread+0x435>
    51bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              if (!cqe->res) {
    51c0:	85 c0                	test   %eax,%eax
    51c2:	75 7c                	jne    5240 <io_thread+0x5e0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    51c4:	48 8b 0d 55 3e 00 00 	mov    0x3e55(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    51cb:	ba 0f 00 00 00       	mov    $0xf,%edx
    51d0:	be 01 00 00 00       	mov    $0x1,%esi
    51d5:	48 8d 3d 05 10 00 00 	lea    0x1005(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    51dc:	e8 ff d2 ff ff       	call   24e0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    51e1:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    51e8:	e9 9f fe ff ff       	jmp    508c <io_thread+0x42c>
    51ed:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    51f0:	41 8b 47 04          	mov    0x4(%r15),%eax
    51f4:	45 31 ed             	xor    %r13d,%r13d
    51f7:	85 c0                	test   %eax,%eax
    51f9:	7e 20                	jle    521b <io_thread+0x5bb>
    51fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  free(req->iov[i].iov_base);
    5200:	4c 89 e8             	mov    %r13,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5203:	49 83 c5 01          	add    $0x1,%r13
                  free(req->iov[i].iov_base);
    5207:	48 c1 e0 04          	shl    $0x4,%rax
    520b:	49 8b 7c 07 10       	mov    0x10(%r15,%rax,1),%rdi
    5210:	e8 bb d0 ff ff       	call   22d0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5215:	45 39 6f 04          	cmp    %r13d,0x4(%r15)
    5219:	7f e5                	jg     5200 <io_thread+0x5a0>
              close(req->client_socket);
    521b:	41 8b 7f 08          	mov    0x8(%r15),%edi
    521f:	e8 4c d1 ff ff       	call   2370 <close@plt>
              free(req);
    5224:	4c 89 ff             	mov    %r15,%rdi
    5227:	e8 a4 d0 ff ff       	call   22d0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    522c:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    5233:	e9 54 fe ff ff       	jmp    508c <io_thread+0x42c>
    5238:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int i = 0; i < dest_sz; i++) {
    5240:	49 8b 57 10          	mov    0x10(%r15),%rdx
    5244:	48 8b 85 80 fa ff ff 	mov    -0x580(%rbp),%rax
    524b:	48 8d 75 c0          	lea    -0x40(%rbp),%rsi
    524f:	eb 14                	jmp    5265 <io_thread+0x605>
    5251:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5258:	48 83 c0 01          	add    $0x1,%rax
    525c:	48 83 c2 01          	add    $0x1,%rdx
    5260:	48 39 c6             	cmp    %rax,%rsi
    5263:	74 4b                	je     52b0 <io_thread+0x650>
        dest[i] = src[i];
    5265:	0f b6 0a             	movzbl (%rdx),%ecx
    5268:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    526a:	80 f9 0d             	cmp    $0xd,%cl
    526d:	75 e9                	jne    5258 <io_thread+0x5f8>
    526f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5273:	75 e3                	jne    5258 <io_thread+0x5f8>
            dest[i] = '\0';
    5275:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5278:	48 8b bd 80 fa ff ff 	mov    -0x580(%rbp),%rdi
    527f:	48 89 da             	mov    %rbx,%rdx
    5282:	41 8b 77 08          	mov    0x8(%r15),%esi
    5286:	e8 35 f7 ff ff       	call   49c0 <handle_http_method>
              free(req->iov[0].iov_base);
    528b:	49 8b 7f 10          	mov    0x10(%r15),%rdi
    528f:	e8 3c d0 ff ff       	call   22d0 <free@plt>
              free(req);
    5294:	4c 89 ff             	mov    %r15,%rdi
    5297:	e8 34 d0 ff ff       	call   22d0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    529c:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    52a3:	e9 e4 fd ff ff       	jmp    508c <io_thread+0x42c>
    52a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    52b0:	48 8b 0d 69 3d 00 00 	mov    0x3d69(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    52b7:	ba 12 00 00 00       	mov    $0x12,%edx
    52bc:	be 01 00 00 00       	mov    $0x1,%esi
    52c1:	48 8d 3d 6f 0e 00 00 	lea    0xe6f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    52c8:	e8 13 d2 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    52cd:	bf 01 00 00 00       	mov    $0x1,%edi
    52d2:	e8 e9 d1 ff ff       	call   24c0 <exit@plt>
    52d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    52e0:	e9 cd fb ff ff       	jmp    4eb2 <io_thread+0x252>
    52e5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    52e8:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	return err;
    52ef:	e9 8c fe ff ff       	jmp    5180 <io_thread+0x520>
    52f4:	0f 1f 40 00          	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    52f8:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    52ff:	48 8d 3d 9e 0e 00 00 	lea    0xe9e(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    5306:	8b 02                	mov    (%rdx),%eax
    5308:	83 c0 01             	add    $0x1,%eax
    530b:	89 02                	mov    %eax,(%rdx)
    530d:	e8 de cf ff ff       	call   22f0 <puts@plt>
    5312:	e9 23 fe ff ff       	jmp    513a <io_thread+0x4da>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5317:	f7 d8                	neg    %eax
    5319:	44 89 85 ac fa ff ff 	mov    %r8d,-0x554(%rbp)
    5320:	89 c7                	mov    %eax,%edi
    5322:	e8 f9 d1 ff ff       	call   2520 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5327:	48 8b 3d f2 3c 00 00 	mov    0x3cf2(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    532e:	be 01 00 00 00       	mov    $0x1,%esi
    5333:	44 8b 85 ac fa ff ff 	mov    -0x554(%rbp),%r8d
    533a:	48 89 c1             	mov    %rax,%rcx
    533d:	48 8d 15 2c 11 00 00 	lea    0x112c(%rip),%rdx        # 6470 <_IO_stdin_used+0x470>
    5344:	31 c0                	xor    %eax,%eax
    5346:	e8 a5 d1 ff ff       	call   24f0 <__fprintf_chk@plt>
          exit(1);
    534b:	bf 01 00 00 00       	mov    $0x1,%edi
    5350:	e8 6b d1 ff ff       	call   24c0 <exit@plt>
    5355:	48 8b 0d c4 3c 00 00 	mov    0x3cc4(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    535c:	ba 28 00 00 00       	mov    $0x28,%edx
    5361:	be 01 00 00 00       	mov    $0x1,%esi
    5366:	48 8d 3d d3 10 00 00 	lea    0x10d3(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    536d:	e8 6e d1 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    5372:	bf 01 00 00 00       	mov    $0x1,%edi
    5377:	e8 44 d1 ff ff       	call   24c0 <exit@plt>
}
    537c:	e8 af cf ff ff       	call   2330 <__stack_chk_fail@plt>
    5381:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    538c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005390 <receive>:
int receive(volatile struct BarrierTask *data) {
    5390:	f3 0f 1e fa          	endbr64
    5394:	55                   	push   %rbp
    5395:	48 89 e5             	mov    %rsp,%rbp
    5398:	ff 15 4a 3c 00 00    	call   *0x3c4a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  for (int n = 0 ; n < data->thread_count; n++) {
    539e:	8b 57 3c             	mov    0x3c(%rdi),%edx
int receive(volatile struct BarrierTask *data) {
    53a1:	48 89 f8             	mov    %rdi,%rax
  for (int n = 0 ; n < data->thread_count; n++) {
    53a4:	85 d2                	test   %edx,%edx
    53a6:	0f 8e cc 00 00 00    	jle    5478 <receive+0xe8>
    53ac:	45 31 d2             	xor    %r10d,%r10d
    53af:	90                   	nop
    struct Data *me = data->mailboxes[n].lower;
    53b0:	48 8b 50 70          	mov    0x70(%rax),%rdx
    53b4:	4c 89 d7             	mov    %r10,%rdi
    53b7:	48 c1 e7 05          	shl    $0x5,%rdi
    53bb:	4c 8b 04 3a          	mov    (%rdx,%rdi,1),%r8
    for (int x = 0 ; x < me->messages_count ; x++) {
    53bf:	49 8b 50 08          	mov    0x8(%r8),%rdx
    53c3:	48 85 d2             	test   %rdx,%rdx
    53c6:	0f 8e 94 00 00 00    	jle    5460 <receive+0xd0>
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    53cc:	4d 8b 08             	mov    (%r8),%r9
    53cf:	31 d2                	xor    %edx,%edx
    53d1:	eb 12                	jmp    53e5 <receive+0x55>
    53d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    53d8:	49 8b 48 08          	mov    0x8(%r8),%rcx
    53dc:	48 83 c2 01          	add    $0x1,%rdx
    53e0:	48 39 d1             	cmp    %rdx,%rcx
    53e3:	7e 7b                	jle    5460 <receive+0xd0>
      data->sends++;
    53e5:	48 8b 48 78          	mov    0x78(%rax),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    53e9:	49 8b 34 d1          	mov    (%r9,%rdx,8),%rsi
      data->sends++;
    53ed:	48 83 c1 01          	add    $0x1,%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    53f1:	4c 8b 5e 10          	mov    0x10(%rsi),%r11
      data->sends++;
    53f5:	48 89 48 78          	mov    %rcx,0x78(%rax)
      data->n++;
    53f9:	48 8b 48 10          	mov    0x10(%rax),%rcx
    53fd:	48 83 c1 01          	add    $0x1,%rcx
    5401:	48 89 48 10          	mov    %rcx,0x10(%rax)
      data->mailboxes[n].received++;
    5405:	48 8b 48 70          	mov    0x70(%rax),%rcx
    5409:	48 83 44 39 18 01    	addq   $0x1,0x18(%rcx,%rdi,1)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    540f:	48 63 08             	movslq (%rax),%rcx
    5412:	49 39 cb             	cmp    %rcx,%r11
    5415:	75 c1                	jne    53d8 <receive+0x48>
    5417:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    541b:	48 63 48 38          	movslq 0x38(%rax),%rcx
    541f:	48 39 ce             	cmp    %rcx,%rsi
    5422:	75 b4                	jne    53d8 <receive+0x48>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread_index);
    5424:	48 63 50 38          	movslq 0x38(%rax),%rdx
    5428:	48 63 00             	movslq (%rax),%rax
    542b:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    542d:	bf 01 00 00 00       	mov    $0x1,%edi
    5432:	48 39 f2             	cmp    %rsi,%rdx
    5435:	48 8d 35 5c 10 00 00 	lea    0x105c(%rip),%rsi        # 6498 <_IO_stdin_used+0x498>
    543c:	0f 94 c1             	sete   %cl
    543f:	31 d2                	xor    %edx,%edx
    5441:	4c 39 d8             	cmp    %r11,%rax
    5444:	0f 94 c2             	sete   %dl
    5447:	31 c0                	xor    %eax,%eax
    5449:	e8 12 d0 ff ff       	call   2460 <__printf_chk@plt>
        exit(1);
    544e:	bf 01 00 00 00       	mov    $0x1,%edi
    5453:	e8 68 d0 ff ff       	call   24c0 <exit@plt>
    5458:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5460:	49 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%r8)
  for (int n = 0 ; n < data->thread_count; n++) {
    5468:	8b 50 3c             	mov    0x3c(%rax),%edx
    546b:	49 83 c2 01          	add    $0x1,%r10
    546f:	44 39 d2             	cmp    %r10d,%edx
    5472:	0f 8f 38 ff ff ff    	jg     53b0 <receive+0x20>
}
    5478:	5d                   	pop    %rbp
    5479:	c3                   	ret
    547a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005480 <barriered_work>:
int barriered_work(volatile struct BarrierTask *data) {
    5480:	f3 0f 1e fa          	endbr64
    5484:	55                   	push   %rbp
    5485:	48 89 e5             	mov    %rsp,%rbp
    5488:	41 56                	push   %r14
    548a:	41 55                	push   %r13
    548c:	41 54                	push   %r12
    548e:	53                   	push   %rbx
    548f:	ff 15 53 3b 00 00    	call   *0x3b53(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  if (data->thread_index == data->task_index) {
    5495:	8b 57 38             	mov    0x38(%rdi),%edx
    5498:	8b 07                	mov    (%rdi),%eax
int barriered_work(volatile struct BarrierTask *data) {
    549a:	48 89 fb             	mov    %rdi,%rbx
  if (data->thread_index == data->task_index) {
    549d:	39 c2                	cmp    %eax,%edx
    549f:	0f 84 cb 00 00 00    	je     5570 <barriered_work+0xf0>
    receive(data);
    54a5:	e8 e6 fe ff ff       	call   5390 <receive>
    while (data->scheduled == 1) {
    54aa:	8b 43 48             	mov    0x48(%rbx),%eax
    54ad:	83 f8 01             	cmp    $0x1,%eax
    54b0:	75 1a                	jne    54cc <barriered_work+0x4c>
    54b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->n++;
    54b8:	48 8b 43 10          	mov    0x10(%rbx),%rax
    54bc:	48 83 c0 01          	add    $0x1,%rax
    54c0:	48 89 43 10          	mov    %rax,0x10(%rbx)
    while (data->scheduled == 1) {
    54c4:	8b 43 48             	mov    0x48(%rbx),%eax
    54c7:	83 f8 01             	cmp    $0x1,%eax
    54ca:	74 ec                	je     54b8 <barriered_work+0x38>
    if (data->sending == 1) {
    54cc:	8b 83 80 00 00 00    	mov    0x80(%rbx),%eax
    54d2:	83 f8 01             	cmp    $0x1,%eax
    54d5:	74 0e                	je     54e5 <barriered_work+0x65>
  asm volatile ("mfence" ::: "memory");
    54d7:	0f ae f0             	mfence
}
    54da:	31 c0                	xor    %eax,%eax
    54dc:	5b                   	pop    %rbx
    54dd:	41 5c                	pop    %r12
    54df:	41 5d                	pop    %r13
    54e1:	41 5e                	pop    %r14
    54e3:	5d                   	pop    %rbp
    54e4:	c3                   	ret
        for (int n = 0 ; n < data->thread_count; n++) {
    54e5:	8b 43 3c             	mov    0x3c(%rbx),%eax
    54e8:	85 c0                	test   %eax,%eax
    54ea:	7e eb                	jle    54d7 <barriered_work+0x57>
    54ec:	45 31 c9             	xor    %r9d,%r9d
    54ef:	90                   	nop
          if (n == data->thread_index) { continue; }
    54f0:	8b 43 38             	mov    0x38(%rbx),%eax
    54f3:	44 39 c8             	cmp    %r9d,%eax
    54f6:	74 5e                	je     5556 <barriered_work+0xd6>
          struct Data *them = data->mailboxes[n].higher;
    54f8:	48 8b 43 70          	mov    0x70(%rbx),%rax
    54fc:	4c 89 c9             	mov    %r9,%rcx
    54ff:	48 c1 e1 05          	shl    $0x5,%rcx
    5503:	48 8b 54 08 08       	mov    0x8(%rax,%rcx,1),%rdx
          for (; them->messages_count < min;) {
    5508:	48 8b 42 08          	mov    0x8(%rdx),%rax
    550c:	48 63 7a 10          	movslq 0x10(%rdx),%rdi
    5510:	48 39 f8             	cmp    %rdi,%rax
    5513:	7d 41                	jge    5556 <barriered_work+0xd6>
            them->messages[them->messages_count++] = data->message; 
    5515:	4c 8b 02             	mov    (%rdx),%r8
    5518:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
            data->n++;
    5520:	48 8b 43 10          	mov    0x10(%rbx),%rax
    5524:	48 83 c0 01          	add    $0x1,%rax
    5528:	48 89 43 10          	mov    %rax,0x10(%rbx)
            data->mailboxes[n].sent++;
    552c:	48 8b 43 70          	mov    0x70(%rbx),%rax
    5530:	48 83 44 08 10 01    	addq   $0x1,0x10(%rax,%rcx,1)
            them->messages[them->messages_count++] = data->message; 
    5536:	48 8b 42 08          	mov    0x8(%rdx),%rax
    553a:	48 8d 70 01          	lea    0x1(%rax),%rsi
    553e:	48 89 72 08          	mov    %rsi,0x8(%rdx)
    5542:	48 8b b3 88 00 00 00 	mov    0x88(%rbx),%rsi
    5549:	49 89 34 c0          	mov    %rsi,(%r8,%rax,8)
          for (; them->messages_count < min;) {
    554d:	48 8b 42 08          	mov    0x8(%rdx),%rax
    5551:	48 39 f8             	cmp    %rdi,%rax
    5554:	7c ca                	jl     5520 <barriered_work+0xa0>
        for (int n = 0 ; n < data->thread_count; n++) {
    5556:	8b 43 3c             	mov    0x3c(%rbx),%eax
    5559:	49 83 c1 01          	add    $0x1,%r9
    555d:	44 39 c8             	cmp    %r9d,%eax
    5560:	7f 8e                	jg     54f0 <barriered_work+0x70>
    5562:	e9 70 ff ff ff       	jmp    54d7 <barriered_work+0x57>
    5567:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      receive(data);
    5570:	e8 1b fe ff ff       	call   5390 <receive>
        int t = data->task_index;
    5575:	8b 3b                	mov    (%rbx),%edi
        for (int y = 0; y < data->thread_count ; y++) {
    5577:	8b 43 3c             	mov    0x3c(%rbx),%eax
    557a:	85 c0                	test   %eax,%eax
    557c:	0f 8e b4 00 00 00    	jle    5636 <barriered_work+0x1b6>
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5582:	48 63 c7             	movslq %edi,%rax
    5585:	45 31 d2             	xor    %r10d,%r10d
    5588:	45 31 ed             	xor    %r13d,%r13d
              int next_task = abs((t + 1) % (data->thread_count));
    558b:	83 c7 01             	add    $0x1,%edi
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    558e:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    5592:	4c 8d 24 50          	lea    (%rax,%rdx,2),%r12
    5596:	49 c1 e4 03          	shl    $0x3,%r12
    559a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          for (int b = 0; b < data->thread_count ; b++) {
    55a0:	8b 43 3c             	mov    0x3c(%rbx),%eax
    55a3:	4d 89 eb             	mov    %r13,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    55a6:	31 f6                	xor    %esi,%esi
    55a8:	31 c9                	xor    %ecx,%ecx
    55aa:	49 c1 e3 05          	shl    $0x5,%r11
          for (int b = 0; b < data->thread_count ; b++) {
    55ae:	85 c0                	test   %eax,%eax
    55b0:	7e 6d                	jle    561f <barriered_work+0x19f>
    55b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              int next_task = abs((t + 1) % (data->thread_count));
    55b8:	44 8b 73 3c          	mov    0x3c(%rbx),%r14d
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    55bc:	48 8b 43 30          	mov    0x30(%rbx),%rax
    55c0:	48 8b 40 10          	mov    0x10(%rax),%rax
    55c4:	4a 8b 54 10 20       	mov    0x20(%rax,%r10,1),%rdx
    55c9:	4c 01 e2             	add    %r12,%rdx
    55cc:	4c 8b 42 70          	mov    0x70(%rdx),%r8
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    55d0:	48 8b 43 30          	mov    0x30(%rbx),%rax
    55d4:	4c 8b 48 10          	mov    0x10(%rax),%r9
              int next_task = abs((t + 1) % (data->thread_count));
    55d8:	89 f8                	mov    %edi,%eax
    55da:	99                   	cltd
    55db:	41 f7 fe             	idiv   %r14d
    55de:	89 d0                	mov    %edx,%eax
    55e0:	f7 d8                	neg    %eax
    55e2:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    55e5:	48 63 d2             	movslq %edx,%rdx
    55e8:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    55ec:	48 8d 14 42          	lea    (%rdx,%rax,2),%rdx
    55f0:	49 8b 44 31 20       	mov    0x20(%r9,%rsi,1),%rax
          for (int b = 0; b < data->thread_count ; b++) {
    55f5:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    55fc:	48 8d 04 d0          	lea    (%rax,%rdx,8),%rax
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5600:	48 89 ca             	mov    %rcx,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5603:	48 83 c1 01          	add    $0x1,%rcx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5607:	48 c1 e2 05          	shl    $0x5,%rdx
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    560b:	48 8b 40 70          	mov    0x70(%rax),%rax
    560f:	49 8b 54 10 08       	mov    0x8(%r8,%rdx,1),%rdx
    5614:	4a 89 14 18          	mov    %rdx,(%rax,%r11,1)
          for (int b = 0; b < data->thread_count ; b++) {
    5618:	8b 43 3c             	mov    0x3c(%rbx),%eax
    561b:	39 c8                	cmp    %ecx,%eax
    561d:	7f 99                	jg     55b8 <barriered_work+0x138>
        for (int y = 0; y < data->thread_count ; y++) {
    561f:	8b 43 3c             	mov    0x3c(%rbx),%eax
    5622:	49 83 c5 01          	add    $0x1,%r13
    5626:	49 81 c2 98 00 00 00 	add    $0x98,%r10
    562d:	44 39 e8             	cmp    %r13d,%eax
    5630:	0f 8f 6a ff ff ff    	jg     55a0 <barriered_work+0x120>
      asm volatile ("mfence" ::: "memory");
    5636:	0f ae f0             	mfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5639:	48 8b 73 50          	mov    0x50(%rbx),%rsi
    563d:	48 8b 43 60          	mov    0x60(%rbx),%rax
    5641:	31 ff                	xor    %edi,%edi
    5643:	48 c1 e0 05          	shl    $0x5,%rax
    5647:	48 01 c6             	add    %rax,%rsi
    564a:	e8 c1 cc ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    564f:	48 8b 43 30          	mov    0x30(%rbx),%rax
    5653:	48 8b 40 30          	mov    0x30(%rax),%rax
    5657:	8b 78 10             	mov    0x10(%rax),%edi
    565a:	44 8d 67 01          	lea    0x1(%rdi),%r12d
    565e:	44 89 60 10          	mov    %r12d,0x10(%rax)
    while (data->scheduled == 1) {
    5662:	8b 43 48             	mov    0x48(%rbx),%eax
    5665:	83 f8 01             	cmp    $0x1,%eax
    5668:	75 4b                	jne    56b5 <barriered_work+0x235>
    566a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->n++;
    5670:	48 8b 43 10          	mov    0x10(%rbx),%rax
    5674:	48 83 c0 01          	add    $0x1,%rax
    5678:	48 89 43 10          	mov    %rax,0x10(%rbx)
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    567c:	48 8b 4b 28          	mov    0x28(%rbx),%rcx
    5680:	48 8b 73 30          	mov    0x30(%rbx),%rsi
    5684:	48 63 43 38          	movslq 0x38(%rbx),%rax
    5688:	48 63 13             	movslq (%rbx),%rdx
    568b:	48 8d 3c c0          	lea    (%rax,%rax,8),%rdi
    568f:	48 8d 04 78          	lea    (%rax,%rdi,2),%rax
    5693:	48 8b 7e 10          	mov    0x10(%rsi),%rdi
    5697:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
    569b:	48 8d 14 72          	lea    (%rdx,%rsi,2),%rdx
    569f:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    56a3:	48 8b 40 20          	mov    0x20(%rax),%rax
    56a7:	48 8d 3c d0          	lea    (%rax,%rdx,8),%rdi
    56ab:	ff d1                	call   *%rcx
    while (data->scheduled == 1) {
    56ad:	8b 43 48             	mov    0x48(%rbx),%eax
    56b0:	83 f8 01             	cmp    $0x1,%eax
    56b3:	74 bb                	je     5670 <barriered_work+0x1f0>
    if (modcount != data->thread->protected_state->modcount) {
    56b5:	48 8b 43 30          	mov    0x30(%rbx),%rax
    56b9:	48 8b 40 30          	mov    0x30(%rax),%rax
    56bd:	44 3b 60 10          	cmp    0x10(%rax),%r12d
    56c1:	75 32                	jne    56f5 <barriered_work+0x275>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    56c3:	48 8b 53 50          	mov    0x50(%rbx),%rdx
    56c7:	48 8b 43 60          	mov    0x60(%rbx),%rax
    56cb:	31 ff                	xor    %edi,%edi
    56cd:	48 c1 e0 05          	shl    $0x5,%rax
    56d1:	48 8d 74 02 10       	lea    0x10(%rdx,%rax,1),%rsi
    56d6:	e8 35 cc ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    56db:	48 8b 43 60          	mov    0x60(%rbx),%rax
    56df:	48 8b 4b 58          	mov    0x58(%rbx),%rcx
    56e3:	48 83 c0 01          	add    $0x1,%rax
    56e7:	48 99                	cqto
    56e9:	48 f7 f9             	idiv   %rcx
    56ec:	48 89 53 60          	mov    %rdx,0x60(%rbx)
    56f0:	e9 e2 fd ff ff       	jmp    54d7 <barriered_work+0x57>
    56f5:	48 8d 3d 08 0b 00 00 	lea    0xb08(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    56fc:	e8 ef cb ff ff       	call   22f0 <puts@plt>
    5701:	eb c0                	jmp    56c3 <barriered_work+0x243>
    5703:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    570e:	66 90                	xchg   %ax,%ax

0000000000005710 <barriered_work_ingest>:
int barriered_work_ingest(volatile struct BarrierTask *data) {
    5710:	f3 0f 1e fa          	endbr64
    5714:	55                   	push   %rbp
    5715:	48 89 e5             	mov    %rsp,%rbp
    5718:	ff 15 ca 38 00 00    	call   *0x38ca(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    571e:	48 8b 47 30          	mov    0x30(%rdi),%rax
    5722:	48 8b 40 38          	mov    0x38(%rax),%rax
    5726:	8b 00                	mov    (%rax),%eax
    5728:	85 c0                	test   %eax,%eax
    572a:	7e 51                	jle    577d <barriered_work_ingest+0x6d>
    572c:	31 c0                	xor    %eax,%eax
    572e:	66 90                	xchg   %ax,%ax
    if (data->thread->buffers->buffer[x].available == 1) {
    5730:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
    5734:	48 89 c2             	mov    %rax,%rdx
    5737:	48 c1 e2 04          	shl    $0x4,%rdx
    573b:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    573f:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    5743:	48 01 d6             	add    %rdx,%rsi
    5746:	8b 4e 08             	mov    0x8(%rsi),%ecx
    5749:	83 f9 01             	cmp    $0x1,%ecx
    574c:	75 1f                	jne    576d <barriered_work_ingest+0x5d>
      data->ingest_count++;
    574e:	48 8b 4f 68          	mov    0x68(%rdi),%rcx
    5752:	48 83 c1 01          	add    $0x1,%rcx
    5756:	48 89 4f 68          	mov    %rcx,0x68(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    575a:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
    575e:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    5762:	48 03 51 08          	add    0x8(%rcx),%rdx
    5766:	c7 42 08 00 00 00 00 	movl   $0x0,0x8(%rdx)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    576d:	48 8b 57 30          	mov    0x30(%rdi),%rdx
    5771:	48 83 c0 01          	add    $0x1,%rax
    5775:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    5779:	39 02                	cmp    %eax,(%rdx)
    577b:	7f b3                	jg     5730 <barriered_work_ingest+0x20>
  asm volatile ("mfence" ::: "memory");
    577d:	0f ae f0             	mfence
  barriered_work(data);
    5780:	e8 fb fc ff ff       	call   5480 <barriered_work>
}
    5785:	31 c0                	xor    %eax,%eax
    5787:	5d                   	pop    %rbp
    5788:	c3                   	ret
    5789:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005790 <barriered_nulltask>:
int barriered_nulltask(volatile struct BarrierTask *data) {
    5790:	f3 0f 1e fa          	endbr64
    5794:	55                   	push   %rbp
    5795:	48 89 e5             	mov    %rsp,%rbp
    5798:	ff 15 4a 38 00 00    	call   *0x384a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
}
    579e:	31 c0                	xor    %eax,%eax
    57a0:	5d                   	pop    %rbp
    57a1:	c3                   	ret
    57a2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    57ad:	0f 1f 00             	nopl   (%rax)

00000000000057b0 <barriered_steal>:
int barriered_steal(volatile struct BarrierTask *data) {
    57b0:	f3 0f 1e fa          	endbr64
    57b4:	55                   	push   %rbp
    57b5:	48 89 e5             	mov    %rsp,%rbp
    57b8:	ff 15 2a 38 00 00    	call   *0x382a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    57be:	31 c0                	xor    %eax,%eax
    57c0:	5d                   	pop    %rbp
    57c1:	c3                   	ret
    57c2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    57cd:	0f 1f 00             	nopl   (%rax)

00000000000057d0 <after>:
int after(struct timespec left, struct timespec right) {
    57d0:	f3 0f 1e fa          	endbr64
    57d4:	55                   	push   %rbp
    57d5:	48 89 e5             	mov    %rsp,%rbp
    57d8:	ff 15 0a 38 00 00    	call   *0x380a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  return left.tv_sec > right.tv_sec &&
    57de:	31 c0                	xor    %eax,%eax
    57e0:	48 39 d7             	cmp    %rdx,%rdi
    57e3:	7e 08                	jle    57ed <after+0x1d>
    57e5:	31 c0                	xor    %eax,%eax
    57e7:	48 39 ce             	cmp    %rcx,%rsi
    57ea:	0f 9f c0             	setg   %al
}
    57ed:	5d                   	pop    %rbp
    57ee:	c3                   	ret
    57ef:	90                   	nop

00000000000057f0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    57f0:	f3 0f 1e fa          	endbr64
    57f4:	55                   	push   %rbp
    57f5:	48 89 e5             	mov    %rsp,%rbp
    57f8:	ff 15 ea 37 00 00    	call   *0x37ea(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  return 0;
    57fe:	31 c0                	xor    %eax,%eax
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5800:	4c 8b 5d 10          	mov    0x10(%rbp),%r11
    5804:	4c 8b 55 18          	mov    0x18(%rbp),%r10
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5808:	48 39 d7             	cmp    %rdx,%rdi
    580b:	7f 18                	jg     5825 <within+0x35>
    580d:	4d 39 d8             	cmp    %r11,%r8
    5810:	0f 9e c2             	setle  %dl
    5813:	48 39 ce             	cmp    %rcx,%rsi
    5816:	0f 9e c0             	setle  %al
    5819:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    581b:	31 c0                	xor    %eax,%eax
    581d:	4d 39 d1             	cmp    %r10,%r9
    5820:	0f 9e c0             	setle  %al
    5823:	21 d0                	and    %edx,%eax
}
    5825:	5d                   	pop    %rbp
    5826:	c3                   	ret
    5827:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005830 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5830:	f3 0f 1e fa          	endbr64
    5834:	55                   	push   %rbp
    5835:	48 89 e5             	mov    %rsp,%rbp
    5838:	ff 15 aa 37 00 00    	call   *0x37aa(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    583e:	48 8b 7d 10          	mov    0x10(%rbp),%rdi
    5842:	48 8b 75 30          	mov    0x30(%rbp),%rsi
    5846:	4c 8b 4d 20          	mov    0x20(%rbp),%r9
    584a:	4c 8b 55 28          	mov    0x28(%rbp),%r10
    584e:	4c 8b 45 40          	mov    0x40(%rbp),%r8
    5852:	4c 8b 5d 48          	mov    0x48(%rbp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5856:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
    585a:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  return left.tv_sec > right.tv_sec &&
    585e:	48 39 fe             	cmp    %rdi,%rsi
    5861:	7d 2d                	jge    5890 <overlap+0x60>
    5863:	48 39 ca             	cmp    %rcx,%rdx
    5866:	7d 60                	jge    58c8 <overlap+0x98>
    5868:	4d 39 da             	cmp    %r11,%r10
    586b:	7d 0a                	jge    5877 <overlap+0x47>
    return 1;
    586d:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5872:	4d 39 c1             	cmp    %r8,%r9
    5875:	7c 0f                	jl     5886 <overlap+0x56>
  return 0;
    5877:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5879:	4d 39 c1             	cmp    %r8,%r9
    587c:	7f 08                	jg     5886 <overlap+0x56>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    587e:	31 c0                	xor    %eax,%eax
    5880:	4d 39 da             	cmp    %r11,%r10
    5883:	0f 9e c0             	setle  %al
}
    5886:	5d                   	pop    %rbp
    5887:	c3                   	ret
    5888:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5890:	7e 56                	jle    58e8 <overlap+0xb8>
    5892:	48 39 ca             	cmp    %rcx,%rdx
    5895:	7f 39                	jg     58d0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5897:	75 31                	jne    58ca <overlap+0x9a>
    5899:	4d 39 c1             	cmp    %r8,%r9
    589c:	7c 2c                	jl     58ca <overlap+0x9a>
    return 1;
    589e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    58a3:	4d 39 da             	cmp    %r11,%r10
    58a6:	7d de                	jge    5886 <overlap+0x56>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    58a8:	48 39 ca             	cmp    %rcx,%rdx
}
    58ab:	5d                   	pop    %rbp
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    58ac:	0f 94 c2             	sete   %dl
    58af:	48 39 fe             	cmp    %rdi,%rsi
    58b2:	0f 94 c0             	sete   %al
    58b5:	21 c2                	and    %eax,%edx
    58b7:	31 c0                	xor    %eax,%eax
    58b9:	4d 39 c1             	cmp    %r8,%r9
    58bc:	0f 94 c0             	sete   %al
    58bf:	21 d0                	and    %edx,%eax
}
    58c1:	c3                   	ret
    58c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    58c8:	74 ad                	je     5877 <overlap+0x47>
  return 0;
    58ca:	31 c0                	xor    %eax,%eax
}
    58cc:	5d                   	pop    %rbp
    58cd:	c3                   	ret
    58ce:	66 90                	xchg   %ax,%ax
  return left.tv_sec > right.tv_sec &&
    58d0:	4d 39 da             	cmp    %r11,%r10
    58d3:	7e c4                	jle    5899 <overlap+0x69>
    return 1;
    58d5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    58da:	4d 39 c1             	cmp    %r8,%r9
    58dd:	7e ba                	jle    5899 <overlap+0x69>
    58df:	eb a5                	jmp    5886 <overlap+0x56>
    58e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    58e8:	48 39 ca             	cmp    %rcx,%rdx
    58eb:	7c 8a                	jl     5877 <overlap+0x47>
    58ed:	4d 39 c1             	cmp    %r8,%r9
    58f0:	7d ac                	jge    589e <overlap+0x6e>
    58f2:	48 39 ca             	cmp    %rcx,%rdx
    58f5:	74 87                	je     587e <overlap+0x4e>
  return 0;
    58f7:	31 c0                	xor    %eax,%eax
    58f9:	eb d1                	jmp    58cc <overlap+0x9c>
    58fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005900 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5900:	f3 0f 1e fa          	endbr64
    5904:	55                   	push   %rbp
    5905:	48 89 e5             	mov    %rsp,%rbp
    5908:	41 57                	push   %r15
    590a:	41 56                	push   %r14
    590c:	41 55                	push   %r13
    590e:	41 54                	push   %r12
    5910:	53                   	push   %rbx
    5911:	48 83 ec 58          	sub    $0x58,%rsp
    5915:	ff 15 cd 36 00 00    	call   *0x36cd(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  for (int x = 0 ; x < thread_count; x++) {
    591b:	85 f6                	test   %esi,%esi
    591d:	0f 8e e2 02 00 00    	jle    5c05 <verify+0x305>
    5923:	4c 8d 6f 20          	lea    0x20(%rdi),%r13
    5927:	45 31 ff             	xor    %r15d,%r15d
    592a:	41 89 f6             	mov    %esi,%r14d
    592d:	4c 89 6d c0          	mov    %r13,-0x40(%rbp)
    for (int z = 0 ; z < thread_count; z++) {
    5931:	4c 89 6d c8          	mov    %r13,-0x38(%rbp)
    5935:	45 31 e4             	xor    %r12d,%r12d
    5938:	4c 89 6d 90          	mov    %r13,-0x70(%rbp)
      if (z != x)  {
    593c:	45 39 e7             	cmp    %r12d,%r15d
    593f:	0f 84 28 02 00 00    	je     5b6d <verify+0x26d>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5945:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    5949:	8b 50 08             	mov    0x8(%rax),%edx
    594c:	85 d2                	test   %edx,%edx
    594e:	0f 8e 19 02 00 00    	jle    5b6d <verify+0x26d>
    5954:	48 c7 45 b8 00 00 00 00 	movq   $0x0,-0x48(%rbp)
    595c:	44 89 fb             	mov    %r15d,%ebx
    595f:	c7 45 9c 00 00 00 00 	movl   $0x0,-0x64(%rbp)
    5966:	89 da                	mov    %ebx,%edx
    5968:	48 8d 35 a5 08 00 00 	lea    0x8a5(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    596f:	bf 01 00 00 00       	mov    $0x1,%edi
    5974:	31 c0                	xor    %eax,%eax
    5976:	e8 e5 ca ff ff       	call   2460 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    597b:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    597f:	8b 40 08             	mov    0x8(%rax),%eax
    5982:	85 c0                	test   %eax,%eax
    5984:	0f 8e c4 01 00 00    	jle    5b4e <verify+0x24e>
    598a:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    598e:	45 31 ed             	xor    %r13d,%r13d
    5991:	4c 8b 7d b8          	mov    -0x48(%rbp),%r15
    5995:	44 89 75 8c          	mov    %r14d,-0x74(%rbp)
    5999:	44 89 65 98          	mov    %r12d,-0x68(%rbp)
    599d:	4d 89 ec             	mov    %r13,%r12
    59a0:	4c 03 38             	add    (%rax),%r15
    59a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    59a8:	48 8b 7d c8          	mov    -0x38(%rbp),%rdi
    59ac:	4b 8d 04 e4          	lea    (%r12,%r12,8),%rax
    59b0:	49 8b 4f 60          	mov    0x60(%r15),%rcx
    59b4:	48 8d 35 6e 08 00 00 	lea    0x86e(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    59bb:	49 8d 04 44          	lea    (%r12,%rax,2),%rax
    59bf:	4c 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%r14
    59c7:	48 8b 07             	mov    (%rdi),%rax
    59ca:	bf 01 00 00 00       	mov    $0x1,%edi
    59cf:	4c 01 f0             	add    %r14,%rax
    59d2:	48 8b 50 60          	mov    0x60(%rax),%rdx
    59d6:	31 c0                	xor    %eax,%eax
    59d8:	e8 83 ca ff ff       	call   2460 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    59dd:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    59e1:	4c 8b 7d b8          	mov    -0x48(%rbp),%r15
    59e5:	4c 03 38             	add    (%rax),%r15
    59e8:	49 8b 47 60          	mov    0x60(%r15),%rax
    59ec:	48 85 c0             	test   %rax,%rax
    59ef:	0f 8e 3f 01 00 00    	jle    5b34 <verify+0x234>
    59f5:	48 8b 7d c8          	mov    -0x38(%rbp),%rdi
    59f9:	4c 89 65 a0          	mov    %r12,-0x60(%rbp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    59fd:	45 31 ed             	xor    %r13d,%r13d
    5a00:	4c 89 75 a8          	mov    %r14,-0x58(%rbp)
    5a04:	48 8b 17             	mov    (%rdi),%rdx
    5a07:	4c 01 f2             	add    %r14,%rdx
    5a0a:	41 89 de             	mov    %ebx,%r14d
    5a0d:	0f 1f 00             	nopl   (%rax)
    5a10:	48 8b 42 60          	mov    0x60(%rdx),%rax
    5a14:	4d 89 ec             	mov    %r13,%r12
    5a17:	31 db                	xor    %ebx,%ebx
    5a19:	49 c1 e4 05          	shl    $0x5,%r12
    5a1d:	48 85 c0             	test   %rax,%rax
    5a20:	0f 8e f6 00 00 00    	jle    5b1c <verify+0x21c>
    5a26:	4c 89 6d b0          	mov    %r13,-0x50(%rbp)
    5a2a:	eb 35                	jmp    5a61 <verify+0x161>
    5a2c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5a30:	48 39 fe             	cmp    %rdi,%rsi
    5a33:	0f 8d 57 01 00 00    	jge    5b90 <verify+0x290>
    5a39:	4d 39 d3             	cmp    %r10,%r11
    5a3c:	7e 05                	jle    5a43 <verify+0x143>
    5a3e:	49 39 c5             	cmp    %rax,%r13
    5a41:	7c 75                	jl     5ab8 <verify+0x1b8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5a43:	4d 39 d3             	cmp    %r10,%r11
    5a46:	0f 8d ab 01 00 00    	jge    5bf7 <verify+0x2f7>
    5a4c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5a50:	48 8b 42 60          	mov    0x60(%rdx),%rax
    5a54:	48 83 c3 01          	add    $0x1,%rbx
    5a58:	48 39 d8             	cmp    %rbx,%rax
    5a5b:	0f 8e b7 00 00 00    	jle    5b18 <verify+0x218>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5a61:	48 8b 42 50          	mov    0x50(%rdx),%rax
    5a65:	48 89 d9             	mov    %rbx,%rcx
    5a68:	49 8b 77 50          	mov    0x50(%r15),%rsi
    5a6c:	48 c1 e1 05          	shl    $0x5,%rcx
    5a70:	4c 01 e6             	add    %r12,%rsi
    5a73:	48 01 c8             	add    %rcx,%rax
    5a76:	4c 8b 0e             	mov    (%rsi),%r9
    5a79:	4c 8b 00             	mov    (%rax),%r8
    5a7c:	48 8b 7e 08          	mov    0x8(%rsi),%rdi
    5a80:	4c 8b 56 10          	mov    0x10(%rsi),%r10
    5a84:	4c 8b 6e 18          	mov    0x18(%rsi),%r13
    5a88:	4c 8b 58 10          	mov    0x10(%rax),%r11
    5a8c:	48 8b 70 08          	mov    0x8(%rax),%rsi
    5a90:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    5a94:	4d 39 c8             	cmp    %r9,%r8
    5a97:	7c 97                	jl     5a30 <verify+0x130>
    5a99:	0f 8e 41 01 00 00    	jle    5be0 <verify+0x2e0>
    5a9f:	48 39 fe             	cmp    %rdi,%rsi
    5aa2:	0f 8f f8 00 00 00    	jg     5ba0 <verify+0x2a0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5aa8:	75 a6                	jne    5a50 <verify+0x150>
    5aaa:	4d 39 d3             	cmp    %r10,%r11
    5aad:	7f a1                	jg     5a50 <verify+0x150>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5aaf:	49 39 c5             	cmp    %rax,%r13
    5ab2:	7c 9c                	jl     5a50 <verify+0x150>
    5ab4:	0f 1f 40 00          	nopl   0x0(%rax)
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
    5ab8:	48 8b 7a 50          	mov    0x50(%rdx),%rdi
    5abc:	49 8b 77 50          	mov    0x50(%r15),%rsi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5ac0:	48 83 c3 01          	add    $0x1,%rbx
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
    5ac4:	48 8b 42 50          	mov    0x50(%rdx),%rax
    5ac8:	49 8b 57 50          	mov    0x50(%r15),%rdx
    5acc:	4c 8b 4c 0f 18       	mov    0x18(%rdi,%rcx,1),%r9
    5ad1:	4e 8b 44 26 08       	mov    0x8(%rsi,%r12,1),%r8
    5ad6:	bf 01 00 00 00       	mov    $0x1,%edi
    5adb:	48 8d 35 de 09 00 00 	lea    0x9de(%rip),%rsi        # 64c0 <_IO_stdin_used+0x4c0>
    5ae2:	48 8b 44 08 10       	mov    0x10(%rax,%rcx,1),%rax
    5ae7:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    5aeb:	48 89 c1             	mov    %rax,%rcx
    5aee:	31 c0                	xor    %eax,%eax
    5af0:	e8 6b c9 ff ff       	call   2460 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5af5:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    5af9:	4c 8b 7d b8          	mov    -0x48(%rbp),%r15
    5afd:	48 8b 55 a8          	mov    -0x58(%rbp),%rdx
    5b01:	4c 03 38             	add    (%rax),%r15
    5b04:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    5b08:	48 03 10             	add    (%rax),%rdx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5b0b:	48 8b 42 60          	mov    0x60(%rdx),%rax
    5b0f:	48 39 d8             	cmp    %rbx,%rax
    5b12:	0f 8f 49 ff ff ff    	jg     5a61 <verify+0x161>
    5b18:	4c 8b 6d b0          	mov    -0x50(%rbp),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5b1c:	49 8b 47 60          	mov    0x60(%r15),%rax
    5b20:	49 83 c5 01          	add    $0x1,%r13
    5b24:	4c 39 e8             	cmp    %r13,%rax
    5b27:	0f 8f e3 fe ff ff    	jg     5a10 <verify+0x110>
    5b2d:	4c 8b 65 a0          	mov    -0x60(%rbp),%r12
    5b31:	44 89 f3             	mov    %r14d,%ebx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5b34:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    5b38:	49 83 c4 01          	add    $0x1,%r12
    5b3c:	44 39 60 08          	cmp    %r12d,0x8(%rax)
    5b40:	0f 8f 62 fe ff ff    	jg     59a8 <verify+0xa8>
    5b46:	44 8b 65 98          	mov    -0x68(%rbp),%r12d
    5b4a:	44 8b 75 8c          	mov    -0x74(%rbp),%r14d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5b4e:	48 8b 7d c0          	mov    -0x40(%rbp),%rdi
    5b52:	83 45 9c 01          	addl   $0x1,-0x64(%rbp)
    5b56:	48 81 45 b8 98 00 00 00 	addq   $0x98,-0x48(%rbp)
    5b5e:	8b 45 9c             	mov    -0x64(%rbp),%eax
    5b61:	39 47 08             	cmp    %eax,0x8(%rdi)
    5b64:	0f 8f fc fd ff ff    	jg     5966 <verify+0x66>
    5b6a:	41 89 df             	mov    %ebx,%r15d
    for (int z = 0 ; z < thread_count; z++) {
    5b6d:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    5b72:	48 81 45 c8 98 00 00 00 	addq   $0x98,-0x38(%rbp)
    5b7a:	41 39 c6             	cmp    %eax,%r14d
    5b7d:	0f 84 93 00 00 00    	je     5c16 <verify+0x316>
    5b83:	41 89 c4             	mov    %eax,%r12d
    5b86:	e9 b1 fd ff ff       	jmp    593c <verify+0x3c>
    5b8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5b90:	0f 85 ba fe ff ff    	jne    5a50 <verify+0x150>
    5b96:	e9 a8 fe ff ff       	jmp    5a43 <verify+0x143>
    5b9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5ba0:	49 39 c5             	cmp    %rax,%r13
    5ba3:	7e 09                	jle    5bae <verify+0x2ae>
    5ba5:	4d 39 d3             	cmp    %r10,%r11
    5ba8:	0f 8c 0a ff ff ff    	jl     5ab8 <verify+0x1b8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5bae:	4d 39 d3             	cmp    %r10,%r11
    5bb1:	0f 8f 99 fe ff ff    	jg     5a50 <verify+0x150>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5bb7:	49 39 c5             	cmp    %rax,%r13
    5bba:	0f 8d f8 fe ff ff    	jge    5ab8 <verify+0x1b8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5bc0:	4d 39 c8             	cmp    %r9,%r8
    5bc3:	0f 85 87 fe ff ff    	jne    5a50 <verify+0x150>
    5bc9:	48 39 fe             	cmp    %rdi,%rsi
    5bcc:	0f 85 7e fe ff ff    	jne    5a50 <verify+0x150>
    5bd2:	4d 39 d3             	cmp    %r10,%r11
    5bd5:	0f 84 dd fe ff ff    	je     5ab8 <verify+0x1b8>
    5bdb:	e9 70 fe ff ff       	jmp    5a50 <verify+0x150>
    5be0:	48 39 fe             	cmp    %rdi,%rsi
    5be3:	0f 8c 5a fe ff ff    	jl     5a43 <verify+0x143>
    5be9:	4d 39 d3             	cmp    %r10,%r11
    5bec:	7e c9                	jle    5bb7 <verify+0x2b7>
    5bee:	48 39 fe             	cmp    %rdi,%rsi
    5bf1:	0f 85 59 fe ff ff    	jne    5a50 <verify+0x150>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5bf7:	49 39 c5             	cmp    %rax,%r13
    5bfa:	0f 8f 50 fe ff ff    	jg     5a50 <verify+0x150>
    5c00:	e9 b3 fe ff ff       	jmp    5ab8 <verify+0x1b8>
}
    5c05:	48 83 c4 58          	add    $0x58,%rsp
    5c09:	31 c0                	xor    %eax,%eax
    5c0b:	5b                   	pop    %rbx
    5c0c:	41 5c                	pop    %r12
    5c0e:	41 5d                	pop    %r13
    5c10:	41 5e                	pop    %r14
    5c12:	41 5f                	pop    %r15
    5c14:	5d                   	pop    %rbp
    5c15:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
    5c16:	48 81 45 c0 98 00 00 00 	addq   $0x98,-0x40(%rbp)
    5c1e:	4c 8b 6d 90          	mov    -0x70(%rbp),%r13
    5c22:	41 8d 47 01          	lea    0x1(%r15),%eax
    5c26:	45 39 e7             	cmp    %r12d,%r15d
    5c29:	74 da                	je     5c05 <verify+0x305>
    5c2b:	41 89 c7             	mov    %eax,%r15d
    5c2e:	e9 fe fc ff ff       	jmp    5931 <verify+0x31>
    5c33:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5c3e:	66 90                	xchg   %ax,%ax

0000000000005c40 <min>:
int min(int a, int b) {
    5c40:	f3 0f 1e fa          	endbr64
    5c44:	55                   	push   %rbp
    5c45:	48 89 e5             	mov    %rsp,%rbp
    5c48:	ff 15 9a 33 00 00    	call   *0x339a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
}
    5c4e:	5d                   	pop    %rbp
  if (b < a) { return b; }
    5c4f:	39 f7                	cmp    %esi,%edi
    5c51:	89 f0                	mov    %esi,%eax
    5c53:	0f 4e c7             	cmovle %edi,%eax
}
    5c56:	c3                   	ret
    5c57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005c60 <atexit>:
    5c60:	f3 0f 1e fa          	endbr64
    5c64:	48 8b 15 9d 33 00 00 	mov    0x339d(%rip),%rdx        # 9008 <__dso_handle>
    5c6b:	31 f6                	xor    %esi,%esi
    5c6d:	e9 3e c8 ff ff       	jmp    24b0 <__cxa_atexit@plt>
    5c72:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5c7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005c80 <__stack_chk_fail_local>:
    5c80:	f3 0f 1e fa          	endbr64
    5c84:	50                   	push   %rax
    5c85:	58                   	pop    %rax
    5c86:	48 83 ec 08          	sub    $0x8,%rsp
    5c8a:	e8 a1 c6 ff ff       	call   2330 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000005c90 <_fini>:
    5c90:	f3 0f 1e fa          	endbr64
    5c94:	48 83 ec 08          	sub    $0x8,%rsp
    5c98:	48 83 c4 08          	add    $0x8,%rsp
    5c9c:	c3                   	ret
