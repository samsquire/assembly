
barrier-runtime-tsansafe:     file format elf64-x86-64


Disassembly of section .init:

0000000000002000 <_init>:
    2000:	f3 0f 1e fa          	endbr64
    2004:	48 83 ec 08          	sub    $0x8,%rsp
    2008:	48 8d 05 b1 12 00 00 	lea    0x12b1(%rip),%rax        # 32c0 <__gmon_start__>
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
    2621:	48 83 ec 78          	sub    $0x78,%rsp
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
    2759:	48 89 85 78 ff ff ff 	mov    %rax,-0x88(%rbp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2760:	e8 3b fc ff ff       	call   23a0 <calloc@plt>
  int barrier_count = thread_count;
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2765:	be 10 00 00 00       	mov    $0x10,%esi
    276a:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    276f:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2773:	e8 28 fc ff ff       	call   23a0 <calloc@plt>
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2778:	be 10 00 00 00       	mov    $0x10,%esi
    277d:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    2782:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2788:	48 89 c3             	mov    %rax,%rbx
    278b:	48 89 45 80          	mov    %rax,-0x80(%rbp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    278f:	e8 0c fc ff ff       	call   23a0 <calloc@plt>
    2794:	4c 8b 5d b8          	mov    -0x48(%rbp),%r11
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    }
  }
  int external_thread_index = 0;
    2798:	c7 45 88 00 00 00 00 	movl   $0x0,-0x78(%rbp)
      buffers[x].buffer[y].available = 0;
    279f:	31 c9                	xor    %ecx,%ecx
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27a1:	48 89 43 08          	mov    %rax,0x8(%rbx)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    27a5:	49 89 c8             	mov    %rcx,%r8
      buffers[x].buffer[y].available = 0;
    27a8:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
            thread_data[x].tasks[y].run = barriered_work; 
    27af:	4d 89 dc             	mov    %r11,%r12
    27b2:	4c 89 9d 70 ff ff ff 	mov    %r11,-0x90(%rbp)
    27b9:	4c 89 9d 68 ff ff ff 	mov    %r11,-0x98(%rbp)
    thread_data[x].thread_index = x;
    27c0:	45 89 04 24          	mov    %r8d,(%r12)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    27c4:	be 10 00 00 00       	mov    $0x10,%esi
    27c9:	bf 64 00 00 00       	mov    $0x64,%edi
      for (int y = 0 ; y < total_barrier_count ; y++) {
    27ce:	31 db                	xor    %ebx,%ebx
    thread_data[x].threads = thread_data;
    27d0:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
    27d7:	44 89 45 b8          	mov    %r8d,-0x48(%rbp)
    thread_data[x].task_count = total_barrier_count;
    27db:	41 c7 44 24 28 07 00 00 00 	movl   $0x7,0x28(%r12)
    thread_data[x].threads = thread_data;
    27e4:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    thread_data[x].thread_count = thread_count;
    27e9:	48 8b 05 00 42 00 00 	mov    0x4200(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    thread_data[x].thread_index = x;
    27f0:	4c 89 45 a8          	mov    %r8,-0x58(%rbp)
    thread_data[x].thread_count = thread_count;
    27f4:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    thread_data[x].protected_state = protected_state;
    27f9:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
    2800:	49 89 44 24 30       	mov    %rax,0x30(%r12)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2805:	e8 96 fb ff ff       	call   23a0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    280a:	be 10 00 00 00       	mov    $0x10,%esi
    280f:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2814:	49 89 44 24 50       	mov    %rax,0x50(%r12)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2819:	e8 82 fb ff ff       	call   23a0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    281e:	be 28 00 00 00       	mov    $0x28,%esi
    2823:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    2828:	66 0f 6f 15 a0 41 00 00 	movdqa 0x41a0(%rip),%xmm2        # 69d0 <_IO_stdin_used+0x9d0>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2830:	49 89 44 24 58       	mov    %rax,0x58(%r12)
    thread_data[x].timestamp_count = 0;
    2835:	41 0f 11 54 24 68    	movups %xmm2,0x68(%r12)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    283b:	e8 60 fb ff ff       	call   23a0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2840:	be 80 02 00 00       	mov    $0x280,%esi
    2845:	bf 07 00 00 00       	mov    $0x7,%edi
    thread_data[x].task_timestamp_count = 0;
    284a:	66 0f 6f 1d 7e 41 00 00 	movdqa 0x417e(%rip),%xmm3        # 69d0 <_IO_stdin_used+0x9d0>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2852:	49 89 44 24 78       	mov    %rax,0x78(%r12)
    thread_data[x].task_timestamp_count = 0;
    2857:	41 0f 11 9c 24 80 00 00 00 	movups %xmm3,0x80(%r12)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2860:	e8 3b fb ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    2865:	4c 89 65 b0          	mov    %r12,-0x50(%rbp)
      thread_data[x].tasks = barriers;
    2869:	49 89 44 24 20       	mov    %rax,0x20(%r12)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    286e:	49 89 c7             	mov    %rax,%r15
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2871:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (x == y) {
    2878:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
            thread_data[x].tasks[y].protected = do_protected_write; 
    287c:	4c 63 f3             	movslq %ebx,%r14
    287f:	4f 8d 2c b6          	lea    (%r14,%r14,4),%r13
    2883:	89 45 90             	mov    %eax,-0x70(%rbp)
    2886:	49 c1 e5 07          	shl    $0x7,%r13
        if (x == y) {
    288a:	39 c3                	cmp    %eax,%ebx
    288c:	0f 84 de 09 00 00    	je     3270 <main+0xc60>
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2892:	be 20 00 00 00       	mov    $0x20,%esi
    2897:	bf 06 00 00 00       	mov    $0x6,%edi
    289c:	e8 ff fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    28a1:	89 5d a0             	mov    %ebx,-0x60(%rbp)
    28a4:	4c 89 6d 98          	mov    %r13,-0x68(%rbp)
    28a8:	4c 8d a0 c0 00 00 00 	lea    0xc0(%rax),%r12
    28af:	4b 89 84 2f 28 02 00 00 	mov    %rax,0x228(%r15,%r13,1)
        for (int b = 0 ; b < thread_count ; b++) {
    28b7:	49 89 c7             	mov    %rax,%r15
    28ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    28c0:	be 08 00 00 00       	mov    $0x8,%esi
    28c5:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < thread_count ; b++) {
    28ca:	49 83 c7 20          	add    $0x20,%r15
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    28ce:	e8 cd fa ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    28d3:	be 08 00 00 00       	mov    $0x8,%esi
    28d8:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    28dd:	49 89 c5             	mov    %rax,%r13
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    28e0:	e8 bb fa ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    28e5:	be 00 01 00 00       	mov    $0x100,%esi
    28ea:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    28ef:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    28f2:	e8 a9 fa ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    28f7:	66 0f 6f 05 e1 40 00 00 	movdqa 0x40e1(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
          mailboxes[b].higher = &data[1];
    28ff:	48 8d b0 00 01 00 00 	lea    0x100(%rax),%rsi
          mailboxes[b].lower = &data[0];
    2906:	49 89 47 e0          	mov    %rax,-0x20(%r15)
          mailboxes[b].higher = &data[1];
    290a:	49 89 77 e8          	mov    %rsi,-0x18(%r15)
          data[0].messages = messages;
    290e:	4c 89 28             	mov    %r13,(%rax)
          data[1].messages = messages2;
    2911:	48 89 98 00 01 00 00 	mov    %rbx,0x100(%rax)
          data[0].messages_count = 0;
    2918:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
          data[1].messages_count = 0;
    291f:	0f 29 80 80 01 00 00 	movaps %xmm0,0x180(%rax)
        for (int b = 0 ; b < thread_count ; b++) {
    2926:	4d 39 fc             	cmp    %r15,%r12
    2929:	75 95                	jne    28c0 <main+0x2b0>
        char *message = malloc(sizeof(char) * 256);
    292b:	be 01 00 00 00       	mov    $0x1,%esi
    2930:	bf 00 01 00 00       	mov    $0x100,%edi
    2935:	8b 5d a0             	mov    -0x60(%rbp),%ebx
    2938:	4c 8b 6d 98          	mov    -0x68(%rbp),%r13
    293c:	e8 5f fa ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2941:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2946:	49 89 c4             	mov    %rax,%r12
        struct Message *messaged = malloc(sizeof(struct Message));
    2949:	e8 d2 fa ff ff       	call   2420 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    294e:	44 8b 45 b8          	mov    -0x48(%rbp),%r8d
    2952:	4c 89 e7             	mov    %r12,%rdi
    2955:	41 89 d9             	mov    %ebx,%r9d
    2958:	48 89 45 a0          	mov    %rax,-0x60(%rbp)
    295c:	48 8d 0d 1d 3c 00 00 	lea    0x3c1d(%rip),%rcx        # 6580 <_IO_stdin_used+0x580>
    2963:	ba 00 01 00 00       	mov    $0x100,%edx
    2968:	31 c0                	xor    %eax,%eax
    296a:	be 01 00 00 00       	mov    $0x1,%esi
    296f:	e8 cc fb ff ff       	call   2540 <__sprintf_chk@plt>
        messaged->message = message;
    2974:	4c 8b 55 a0          	mov    -0x60(%rbp),%r10
        messaged->thread_index = x;
    2978:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    297c:	ba ab aa aa aa       	mov    $0xaaaaaaab,%edx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2981:	be 20 00 00 00       	mov    $0x20,%esi
    2986:	bf 3f 42 0f 00       	mov    $0xf423f,%edi
        messaged->thread_index = x;
    298b:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    298f:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
        messaged->task_index = y;
    2993:	4d 89 72 10          	mov    %r14,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2997:	44 8d 73 01          	lea    0x1(%rbx),%r14d
    299b:	4c 8b 78 20          	mov    0x20(%rax),%r15
    299f:	44 89 f0             	mov    %r14d,%eax
    29a2:	44 89 f1             	mov    %r14d,%ecx
        messaged->message = message;
    29a5:	4d 89 22             	mov    %r12,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    29a8:	48 0f af c2          	imul   %rdx,%rax
    29ac:	4f 8d 24 2f          	lea    (%r15,%r13,1),%r12
        thread_data[x].tasks[y].message = messaged;
    29b0:	4d 89 94 24 40 02 00 00 	mov    %r10,0x240(%r12)
        thread_data[x].tasks[y].snapshot_count = 999999;
    29b8:	49 c7 84 24 10 02 00 00 3f 42 0f 00 	movq   $0xf423f,0x210(%r12)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    29c4:	48 c1 e8 22          	shr    $0x22,%rax
    29c8:	8d 04 40             	lea    (%rax,%rax,2),%eax
    29cb:	01 c0                	add    %eax,%eax
    29cd:	29 c1                	sub    %eax,%ecx
    29cf:	41 89 8c 24 48 02 00 00 	mov    %ecx,0x248(%r12)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    29d7:	e8 c4 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].thread_index = x;
    29dc:	8b 4d b8             	mov    -0x48(%rbp),%ecx
        thread_data[x].tasks[y].task_index = y;
    29df:	41 89 1c 24          	mov    %ebx,(%r12)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    29e3:	49 89 84 24 08 02 00 00 	mov    %rax,0x208(%r12)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    29eb:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    29ef:	49 c7 84 24 18 02 00 00 00 00 00 00 	movq   $0x0,0x218(%r12)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    29fb:	49 89 84 24 28 01 00 00 	mov    %rax,0x128(%r12)
        thread_data[x].tasks[y].available = 1;
    2a03:	48 8b 05 ee 3f 00 00 	mov    0x3fee(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
        thread_data[x].tasks[y].thread_index = x;
    2a0a:	41 89 8c 24 30 01 00 00 	mov    %ecx,0x130(%r12)
        thread_data[x].tasks[y].available = 1;
    2a12:	49 89 84 24 80 01 00 00 	mov    %rax,0x180(%r12)
        thread_data[x].tasks[y].sending = 1;
    2a1a:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
        thread_data[x].tasks[y].arrived = 0;
    2a24:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
        thread_data[x].tasks[y].thread_count = thread_count;
    2a30:	41 c7 84 24 34 01 00 00 06 00 00 00 	movl   $0x6,0x134(%r12)
        thread_data[x].tasks[y].sending = 1;
    2a3c:	49 89 84 24 38 02 00 00 	mov    %rax,0x238(%r12)
        if (y == barrier_count - 1) {
    2a44:	83 fb 05             	cmp    $0x5,%ebx
    2a47:	0f 84 03 08 00 00    	je     3250 <main+0xc40>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2a4d:	8b 45 90             	mov    -0x70(%rbp),%eax
    2a50:	39 c3                	cmp    %eax,%ebx
    2a52:	75 5c                	jne    2ab0 <main+0x4a0>
    2a54:	8b 5d 88             	mov    -0x78(%rbp),%ebx
    2a57:	85 db                	test   %ebx,%ebx
    2a59:	7f 55                	jg     2ab0 <main+0x4a0>
    2a5b:	89 ca                	mov    %ecx,%edx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2a5d:	bf 01 00 00 00       	mov    $0x1,%edi
    2a62:	48 8d 35 3f 3b 00 00 	lea    0x3b3f(%rip),%rsi        # 65a8 <_IO_stdin_used+0x5a8>
    2a69:	31 c0                	xor    %eax,%eax
    2a6b:	e8 f0 f9 ff ff       	call   2460 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a70:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    2a74:	48 63 c3             	movslq %ebx,%rax
    2a77:	48 8b 7d 80          	mov    -0x80(%rbp),%rdi
    2a7b:	48 89 c1             	mov    %rax,%rcx
    2a7e:	48 c1 e0 04          	shl    $0x4,%rax
    2a82:	48 01 f8             	add    %rdi,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a85:	4c 8b 7a 20          	mov    0x20(%rdx),%r15
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a89:	48 89 42 38          	mov    %rax,0x38(%rdx)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a8d:	48 8d 05 ec 2c 00 00 	lea    0x2cec(%rip),%rax        # 5780 <barriered_work_ingest>
    2a94:	4b 89 84 2f 18 01 00 00 	mov    %rax,0x118(%r15,%r13,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a9c:	8d 41 01             	lea    0x1(%rcx),%eax
    2a9f:	89 45 88             	mov    %eax,-0x78(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2aa2:	41 83 fe 07          	cmp    $0x7,%r14d
    2aa6:	74 1d                	je     2ac5 <main+0x4b5>
  int external_thread_index = 0;
    2aa8:	44 89 f3             	mov    %r14d,%ebx
    2aab:	e9 c8 fd ff ff       	jmp    2878 <main+0x268>
            thread_data[x].tasks[y].run = barriered_work; 
    2ab0:	48 8d 05 39 29 00 00 	lea    0x2939(%rip),%rax        # 53f0 <barriered_work>
    2ab7:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2abf:	41 83 fe 07          	cmp    $0x7,%r14d
    2ac3:	75 e3                	jne    2aa8 <main+0x498>

          }
        }
      }
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2ac5:	48 8d 05 64 09 00 00 	lea    0x964(%rip),%rax        # 3430 <barriered_reset>
    2acc:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    2ad0:	4c 8b 65 b0          	mov    -0x50(%rbp),%r12
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2ad4:	41 c7 87 80 0f 00 00 00 00 00 00 	movl   $0x0,0xf80(%r15)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2adf:	49 89 87 18 10 00 00 	mov    %rax,0x1018(%r15)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
      thread_data[x].tasks[barrier_count].thread_index = x; 
    2ae6:	8b 45 b8             	mov    -0x48(%rbp),%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2ae9:	49 83 c0 01          	add    $0x1,%r8
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2aed:	4d 89 a7 28 10 00 00 	mov    %r12,0x1028(%r15)
  for (int x = 0 ; x < total_threads ; x++) {
    2af4:	49 81 c4 98 00 00 00 	add    $0x98,%r12
      thread_data[x].tasks[barrier_count].thread_index = x; 
    2afb:	41 89 87 30 10 00 00 	mov    %eax,0x1030(%r15)
      thread_data[x].tasks[barrier_count].available = 1; 
    2b02:	48 8b 05 ef 3e 00 00 	mov    0x3eef(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2b09:	41 c7 87 00 0f 00 00 06 00 00 00 	movl   $0x6,0xf00(%r15)
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
    2b14:	41 c7 87 34 10 00 00 06 00 00 00 	movl   $0x6,0x1034(%r15)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2b1f:	41 c7 87 3c 11 00 00 06 00 00 00 	movl   $0x6,0x113c(%r15)
      thread_data[x].tasks[barrier_count].available = 1; 
    2b2a:	49 89 87 80 10 00 00 	mov    %rax,0x1080(%r15)
  for (int x = 0 ; x < total_threads ; x++) {
    2b31:	49 83 f8 09          	cmp    $0x9,%r8
    2b35:	0f 85 85 fc ff ff    	jne    27c0 <main+0x1b0>
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].threads = thread_data;
    2b3b:	4c 8b 9d 70 ff ff ff 	mov    -0x90(%rbp),%r11
    2b42:	4c 8b 85 68 ff ff ff 	mov    -0x98(%rbp),%r8
    thread_data[x].thread_index = x;
    thread_data[x].task_count = total_barrier_count;
  }
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
    2b49:	b9 01 00 00 00       	mov    $0x1,%ecx
    2b4e:	49 8d b3 b0 03 00 00 	lea    0x3b0(%r11),%rsi
    2b55:	4d 8d 7b 20          	lea    0x20(%r11),%r15
    thread_data[x].threads = thread_data;
    2b59:	4d 89 9b 38 04 00 00 	mov    %r11,0x438(%r11)
    thread_data[x].thread_count = thread_count;
    2b60:	41 c7 83 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r11)
    thread_data[x].task_count = total_barrier_count;
    2b6b:	4c 89 f8             	mov    %r15,%rax
    thread_data[x].thread_index = x;
    2b6e:	41 c7 83 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r11)
    thread_data[x].task_count = total_barrier_count;
    2b79:	41 c7 83 50 04 00 00 07 00 00 00 	movl   $0x7,0x450(%r11)
  for (int n = 0 ; n < thread_count ; n++) {
    2b84:	48 89 75 98          	mov    %rsi,-0x68(%rbp)
    2b88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    thread_data[n].tasks[0].scheduled = 1;
    2b90:	48 8b 10             	mov    (%rax),%rdx
    2b93:	89 cf                	mov    %ecx,%edi
    2b95:	87 ba 00 02 00 00    	xchg   %edi,0x200(%rdx)
  for (int n = 0 ; n < thread_count ; n++) {
    2b9b:	48 05 98 00 00 00    	add    $0x98,%rax
    2ba1:	48 39 f0             	cmp    %rsi,%rax
    2ba4:	75 ea                	jne    2b90 <main+0x580>
  }

  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ba6:	be 38 00 00 00       	mov    $0x38,%esi
    2bab:	bf 09 00 00 00       	mov    $0x9,%edi
    2bb0:	4c 89 45 88          	mov    %r8,-0x78(%rbp)
  thread_data[thread_count].thread_count = thread_count;
  thread_data[thread_count].thread_index = 0;

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
  for (int x = 0 ; x < thread_count ; x++) {
    2bb4:	45 31 f6             	xor    %r14d,%r14d
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bb7:	4c 89 5d a8          	mov    %r11,-0x58(%rbp)
    2bbb:	4c 8d 25 fe 08 00 00 	lea    0x8fe(%rip),%r12        # 34c0 <barriered_thread>
    2bc2:	e8 d9 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bc7:	be 38 00 00 00       	mov    $0x38,%esi
    2bcc:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bd1:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bd4:	e8 c7 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bd9:	be 38 00 00 00       	mov    $0x38,%esi
    2bde:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2be3:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2be7:	e8 b4 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bec:	be 08 00 00 00       	mov    $0x8,%esi
    2bf1:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bf6:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bfa:	e8 a1 f7 ff ff       	call   23a0 <calloc@plt>
  thread_data[thread_count].task_count = total_barrier_count;
    2bff:	4c 8b 5d a8          	mov    -0x58(%rbp),%r11
    2c03:	ba 06 00 00 00       	mov    $0x6,%edx
    2c08:	48 8d 35 e0 36 00 00 	lea    0x36e0(%rip),%rsi        # 62ef <_IO_stdin_used+0x2ef>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2c0f:	49 89 c5             	mov    %rax,%r13
  thread_data[thread_count].task_count = total_barrier_count;
    2c12:	48 8b 05 e7 3d 00 00 	mov    0x3de7(%rip),%rax        # 6a00 <_IO_stdin_used+0xa00>
    2c19:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].threads = thread_data;
    2c1e:	4d 89 9b a0 03 00 00 	mov    %r11,0x3a0(%r11)
  thread_data[thread_count].task_count = total_barrier_count;
    2c25:	49 89 83 b8 03 00 00 	mov    %rax,0x3b8(%r11)
    2c2c:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2c2e:	41 c7 83 a8 03 00 00 06 00 00 00 	movl   $0x6,0x3a8(%r11)
  thread_data[thread_count].thread_index = 0;
    2c39:	49 c7 83 90 03 00 00 00 00 00 00 	movq   $0x0,0x390(%r11)
    2c44:	e8 17 f8 ff ff       	call   2460 <__printf_chk@plt>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2c49:	4c 8b 5d a8          	mov    -0x58(%rbp),%r11
    2c4d:	49 8d 7d 30          	lea    0x30(%r13),%rdi
    2c51:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2c58:	48 8d 15 d1 0b 00 00 	lea    0xbd1(%rip),%rdx        # 3830 <timer_thread>
    2c5f:	49 8d 8b 90 03 00 00 	lea    0x390(%r11),%rcx
    2c66:	e8 15 f8 ff ff       	call   2480 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2c6b:	4c 89 6d a0          	mov    %r13,-0x60(%rbp)
    2c6f:	4c 89 7d 90          	mov    %r15,-0x70(%rbp)
    2c73:	4c 8b 7d 88          	mov    -0x78(%rbp),%r15
    2c77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
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
    2cd0:	4c 8b 5d a8          	mov    -0x58(%rbp),%r11
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
    thread_data[x].type = IO;
    2cec:	4c 8b 7d 90          	mov    -0x70(%rbp),%r15
    2cf0:	4c 8d 65 c0          	lea    -0x40(%rbp),%r12
    2cf4:	41 c7 83 2c 04 00 00 02 00 00 00 	movl   $0x2,0x42c(%r11)
    thread_data[x].task_count = 0;
    2cff:	49 89 9b 50 04 00 00 	mov    %rbx,0x450(%r11)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2d06:	e8 95 f6 ff ff       	call   23a0 <calloc@plt>
    2d0b:	4c 8b 5d a8          	mov    -0x58(%rbp),%r11
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2d0f:	be 00 08 00 00       	mov    $0x800,%esi
    2d14:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2d16:	49 89 83 68 04 00 00 	mov    %rax,0x468(%r11)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2d1d:	e8 ae f7 ff ff       	call   24d0 <eventfd@plt>
    2d22:	4c 8b 5d a8          	mov    -0x58(%rbp),%r11
    2d26:	ba 07 00 00 00       	mov    $0x7,%edx
    2d2b:	48 8d 35 db 35 00 00 	lea    0x35db(%rip),%rsi        # 630d <_IO_stdin_used+0x30d>
    2d32:	bf 01 00 00 00       	mov    $0x1,%edi
    2d37:	41 89 83 70 04 00 00 	mov    %eax,0x470(%r11)
    2d3e:	31 c0                	xor    %eax,%eax
    thread_data[x].threads = thread_data;
    2d40:	4d 89 9b 38 04 00 00 	mov    %r11,0x438(%r11)
    thread_data[x].thread_count = thread_count;
    2d47:	41 c7 83 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r11)
    thread_data[x].thread_index = x;
    2d52:	41 c7 83 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r11)
    2d5d:	e8 fe f6 ff ff       	call   2460 <__printf_chk@plt>
    thread_data[x].type = IO;
    2d62:	4c 8b 5d a8          	mov    -0x58(%rbp),%r11
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2d66:	48 8b 75 b8          	mov    -0x48(%rbp),%rsi
    2d6a:	49 8d 7d 38          	lea    0x38(%r13),%rdi
    2d6e:	48 8d 15 2b 1e 00 00 	lea    0x1e2b(%rip),%rdx        # 4ba0 <io_thread>
    thread_data[x].type = IO;
    2d75:	49 8d 8b 28 04 00 00 	lea    0x428(%r11),%rcx
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2d7c:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2d83:	e8 f8 f6 ff ff       	call   2480 <pthread_create@plt>
    2d88:	ba 08 00 00 00       	mov    $0x8,%edx
    2d8d:	48 8d 35 90 35 00 00 	lea    0x3590(%rip),%rsi        # 6324 <_IO_stdin_used+0x324>
    2d94:	31 c0                	xor    %eax,%eax
    2d96:	bf 01 00 00 00       	mov    $0x1,%edi
    2d9b:	e8 c0 f6 ff ff       	call   2460 <__printf_chk@plt>
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2da0:	4c 8b 5d a8          	mov    -0x58(%rbp),%r11
    thread_data[x].buffers = &buffers[buffer_index];
    2da4:	48 8b 45 80          	mov    -0x80(%rbp),%rax

    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2da8:	49 8d 7d 40          	lea    0x40(%r13),%rdi
    2dac:	48 8b 75 b0          	mov    -0x50(%rbp),%rsi
    2db0:	48 8d 15 b9 09 00 00 	lea    0x9b9(%rip),%rdx        # 3770 <external_thread>
    thread_data[x].buffers = &buffers[buffer_index];
    2db7:	49 89 83 f8 04 00 00 	mov    %rax,0x4f8(%r11)
    thread_data[x].thread_count = thread_count;
    2dbe:	48 8b 05 2b 3c 00 00 	mov    0x3c2b(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    thread_data[x].type = EXTERNAL;
    2dc5:	49 8d 8b c0 04 00 00 	lea    0x4c0(%r11),%rcx
    thread_data[x].task_count = 0;
    2dcc:	49 89 9b e8 04 00 00 	mov    %rbx,0x4e8(%r11)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2dd3:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    2dda:	48 8d 1d 7e 35 00 00 	lea    0x357e(%rip),%rbx        # 635f <_IO_stdin_used+0x35f>
    thread_data[x].thread_count = thread_count;
    2de1:	49 89 83 d8 04 00 00 	mov    %rax,0x4d8(%r11)
    thread_data[x].thread_index = x;
    2de8:	48 8b 05 21 3c 00 00 	mov    0x3c21(%rip),%rax        # 6a10 <_IO_stdin_used+0xa10>
    thread_data[x].threads = thread_data;
    2def:	4d 89 9b d0 04 00 00 	mov    %r11,0x4d0(%r11)
    thread_data[x].thread_index = x;
    2df6:	49 89 83 c0 04 00 00 	mov    %rax,0x4c0(%r11)
    thread_data[x].type = EXTERNAL;
    2dfd:	4c 89 5d b8          	mov    %r11,-0x48(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2e01:	e8 7a f6 ff ff       	call   2480 <pthread_create@plt>
    2e06:	48 8d 3d 34 35 00 00 	lea    0x3534(%rip),%rdi        # 6341 <_IO_stdin_used+0x341>
    2e0d:	e8 de f4 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
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
  long total = 0;
  long v = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    2e41:	4c 8b 5d b8          	mov    -0x48(%rbp),%r11
  long sents = 0;
    2e45:	45 31 e4             	xor    %r12d,%r12d
  long sends = 0;
    2e48:	45 31 c9             	xor    %r9d,%r9d
  long v = 0;
    2e4b:	45 31 c0             	xor    %r8d,%r8d
  long total = 0;
    2e4e:	45 31 ed             	xor    %r13d,%r13d
    2e51:	4c 89 45 b0          	mov    %r8,-0x50(%rbp)
  long ingests = 0;
    2e55:	31 c9                	xor    %ecx,%ecx
  long received = 0;
    2e57:	31 db                	xor    %ebx,%ebx
    2e59:	4c 89 6d b8          	mov    %r13,-0x48(%rbp)
    2e5d:	49 89 ce             	mov    %rcx,%r14
    2e60:	4c 89 5d 90          	mov    %r11,-0x70(%rbp)
    2e64:	4c 89 4d a8          	mov    %r9,-0x58(%rbp)
    2e68:	4c 89 65 a0          	mov    %r12,-0x60(%rbp)
    2e6c:	0f 1f 40 00          	nopl   0x0(%rax)
  for (int x = 0 ; x < thread_count ; x++) {

    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2e70:	49 63 47 08          	movslq 0x8(%r15),%rax
    2e74:	85 c0                	test   %eax,%eax
    2e76:	0f 8e a3 00 00 00    	jle    2f1f <main+0x90f>
    2e7c:	49 8b 0f             	mov    (%r15),%rcx
    2e7f:	48 8d 34 80          	lea    (%rax,%rax,4),%rsi
    2e83:	4c 8b 45 b0          	mov    -0x50(%rbp),%r8
    2e87:	48 c1 e6 07          	shl    $0x7,%rsi
    2e8b:	4c 8b 4d a8          	mov    -0x58(%rbp),%r9
    2e8f:	4c 8b 65 a0          	mov    -0x60(%rbp),%r12
    2e93:	48 8d 91 08 01 00 00 	lea    0x108(%rcx),%rdx
    2e9a:	48 8b 4d b8          	mov    -0x48(%rbp),%rcx
    2e9e:	48 01 d6             	add    %rdx,%rsi
    2ea1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      total += thread_data[x].tasks[n].n;
    2ea8:	48 03 0a             	add    (%rdx),%rcx
      v += thread_data[x].tasks[n].v;
      ingests += thread_data[x].tasks[n].ingest_count;
      sends += thread_data[x].tasks[n].sends;
      for (int k = 0 ; k < thread_count ; k++) {
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2eab:	48 8b 82 20 01 00 00 	mov    0x120(%rdx),%rax
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2eb2:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
      v += thread_data[x].tasks[n].v;
    2eb9:	4c 03 82 88 fd ff ff 	add    -0x278(%rdx),%r8
      ingests += thread_data[x].tasks[n].ingest_count;
    2ec0:	4c 03 b2 98 fe ff ff 	add    -0x168(%rdx),%r14
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ec7:	4c 03 60 10          	add    0x10(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ecb:	48 03 58 18          	add    0x18(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ecf:	4c 03 60 30          	add    0x30(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ed3:	48 03 58 38          	add    0x38(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ed7:	4c 03 60 50          	add    0x50(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2edb:	48 03 58 58          	add    0x58(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2edf:	4c 03 60 70          	add    0x70(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ee3:	48 03 58 78          	add    0x78(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ee7:	4c 03 a0 90 00 00 00 	add    0x90(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2eee:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
      sends += thread_data[x].tasks[n].sends;
    2ef5:	4c 03 8a a8 fe ff ff 	add    -0x158(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2efc:	4c 03 a0 b0 00 00 00 	add    0xb0(%rax),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2f03:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2f0a:	48 39 f2             	cmp    %rsi,%rdx
    2f0d:	75 99                	jne    2ea8 <main+0x898>
    2f0f:	48 89 4d b8          	mov    %rcx,-0x48(%rbp)
    2f13:	4c 89 45 b0          	mov    %r8,-0x50(%rbp)
    2f17:	4c 89 4d a8          	mov    %r9,-0x58(%rbp)
    2f1b:	4c 89 65 a0          	mov    %r12,-0x60(%rbp)
      }
    }
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f1f:	45 31 ed             	xor    %r13d,%r13d
    2f22:	49 83 7f 50 00       	cmpq   $0x0,0x50(%r15)
    2f27:	0f 8e 85 00 00 00    	jle    2fb2 <main+0x9a2>
    2f2d:	4d 89 fc             	mov    %r15,%r12
    2f30:	49 89 df             	mov    %rbx,%r15
    2f33:	4c 89 eb             	mov    %r13,%rbx
    2f36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
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
    307e:	0f 85 ec fd ff ff    	jne    2e70 <main+0x860>
    3084:	4c 8b 6d b8          	mov    -0x48(%rbp),%r13
    3088:	4c 8b 45 b0          	mov    -0x50(%rbp),%r8
    308c:	bf 01 00 00 00       	mov    $0x1,%edi
    3091:	31 c0                	xor    %eax,%eax
    3093:	4c 8b 5d 90          	mov    -0x70(%rbp),%r11
    3097:	4c 8b 4d a8          	mov    -0x58(%rbp),%r9
    309b:	48 8d 35 1d 33 00 00 	lea    0x331d(%rip),%rsi        # 63bf <_IO_stdin_used+0x3bf>
    30a2:	4c 89 75 a8          	mov    %r14,-0x58(%rbp)
    30a6:	4c 89 ea             	mov    %r13,%rdx
    30a9:	4c 89 45 b8          	mov    %r8,-0x48(%rbp)
    30ad:	4c 8b 65 a0          	mov    -0x60(%rbp),%r12
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total Protected %ld\n", protected_state->protected);
  printf("Total V %ld\n", v);
  printf("\n");
  printf("Total Protected per second %ld\n", protected_state->protected / DURATION);
    30b1:	49 be 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%r14
    30bb:	4c 89 5d b0          	mov    %r11,-0x50(%rbp)
    30bf:	4c 89 4d a0          	mov    %r9,-0x60(%rbp)
    30c3:	e8 98 f3 ff ff       	call   2460 <__printf_chk@plt>
    30c8:	bf 0a 00 00 00       	mov    $0xa,%edi
    30cd:	e8 0e f2 ff ff       	call   22e0 <putchar@plt>
    30d2:	4c 8b bd 78 ff ff ff 	mov    -0x88(%rbp),%r15
    30d9:	48 8d 35 f3 32 00 00 	lea    0x32f3(%rip),%rsi        # 63d3 <_IO_stdin_used+0x3d3>
    30e0:	31 c0                	xor    %eax,%eax
    30e2:	bf 01 00 00 00       	mov    $0x1,%edi
    30e7:	49 8b 17             	mov    (%r15),%rdx
    30ea:	e8 71 f3 ff ff       	call   2460 <__printf_chk@plt>
    30ef:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
    30f3:	bf 01 00 00 00       	mov    $0x1,%edi
    30f8:	31 c0                	xor    %eax,%eax
    30fa:	48 8d 35 e7 32 00 00 	lea    0x32e7(%rip),%rsi        # 63e8 <_IO_stdin_used+0x3e8>
    3101:	e8 5a f3 ff ff       	call   2460 <__printf_chk@plt>
    3106:	bf 0a 00 00 00       	mov    $0xa,%edi
    310b:	e8 d0 f1 ff ff       	call   22e0 <putchar@plt>
    3110:	49 8b 37             	mov    (%r15),%rsi
    3113:	bf 01 00 00 00       	mov    $0x1,%edi
    3118:	48 89 f0             	mov    %rsi,%rax
    311b:	49 f7 ee             	imul   %r14
    311e:	31 c0                	xor    %eax,%eax
    3120:	48 01 f2             	add    %rsi,%rdx
    3123:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3127:	48 c1 fa 04          	sar    $0x4,%rdx
    312b:	48 29 f2             	sub    %rsi,%rdx
    312e:	48 8d 35 f3 34 00 00 	lea    0x34f3(%rip),%rsi        # 6628 <_IO_stdin_used+0x628>
    3135:	e8 26 f3 ff ff       	call   2460 <__printf_chk@plt>
    313a:	49 8b 57 08          	mov    0x8(%r15),%rdx
    313e:	bf 01 00 00 00       	mov    $0x1,%edi
    3143:	31 c0                	xor    %eax,%eax
    3145:	48 8d 35 fc 34 00 00 	lea    0x34fc(%rip),%rsi        # 6648 <_IO_stdin_used+0x648>
    314c:	e8 0f f3 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3151:	48 8b 4d a8          	mov    -0x58(%rbp),%rcx
    3155:	bf 01 00 00 00       	mov    $0x1,%edi
    315a:	48 8d 35 0f 35 00 00 	lea    0x350f(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    3161:	48 89 c8             	mov    %rcx,%rax
    3164:	49 f7 ee             	imul   %r14
    3167:	31 c0                	xor    %eax,%eax
    3169:	48 01 ca             	add    %rcx,%rdx
    316c:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3170:	48 c1 fa 04          	sar    $0x4,%rdx
    3174:	48 29 ca             	sub    %rcx,%rdx
    3177:	e8 e4 f2 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    317c:	4c 8b 4d a0          	mov    -0x60(%rbp),%r9
    3180:	bf 01 00 00 00       	mov    $0x1,%edi
    3185:	48 8d 35 14 35 00 00 	lea    0x3514(%rip),%rsi        # 66a0 <_IO_stdin_used+0x6a0>
    318c:	4c 89 c8             	mov    %r9,%rax
    318f:	49 f7 ee             	imul   %r14
    3192:	31 c0                	xor    %eax,%eax
    3194:	4c 01 ca             	add    %r9,%rdx
    3197:	49 c1 f9 3f          	sar    $0x3f,%r9
    319b:	48 c1 fa 04          	sar    $0x4,%rdx
    319f:	4c 29 ca             	sub    %r9,%rdx
    31a2:	e8 b9 f2 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    31a7:	4c 89 e8             	mov    %r13,%rax
    31aa:	bf 01 00 00 00       	mov    $0x1,%edi
    31af:	48 8d 35 1a 35 00 00 	lea    0x351a(%rip),%rsi        # 66d0 <_IO_stdin_used+0x6d0>
    31b6:	49 f7 ee             	imul   %r14
    31b9:	4c 01 ea             	add    %r13,%rdx
    31bc:	49 c1 fd 3f          	sar    $0x3f,%r13
    31c0:	31 c0                	xor    %eax,%eax
    31c2:	48 c1 fa 04          	sar    $0x4,%rdx
    31c6:	4c 29 ea             	sub    %r13,%rdx
    31c9:	e8 92 f2 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    31ce:	4c 89 e0             	mov    %r12,%rax
    31d1:	bf 01 00 00 00       	mov    $0x1,%edi
    31d6:	48 8d 35 18 32 00 00 	lea    0x3218(%rip),%rsi        # 63f5 <_IO_stdin_used+0x3f5>
    31dd:	49 f7 ee             	imul   %r14
    31e0:	31 c0                	xor    %eax,%eax
    31e2:	4c 01 e2             	add    %r12,%rdx
    31e5:	49 c1 fc 3f          	sar    $0x3f,%r12
    31e9:	48 c1 fa 04          	sar    $0x4,%rdx
    31ed:	4c 29 e2             	sub    %r12,%rdx
    31f0:	e8 6b f2 ff ff       	call   2460 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    31f5:	48 89 d8             	mov    %rbx,%rax
    31f8:	bf 01 00 00 00       	mov    $0x1,%edi
    31fd:	48 8d 35 02 32 00 00 	lea    0x3202(%rip),%rsi        # 6406 <_IO_stdin_used+0x406>
    3204:	49 f7 ee             	imul   %r14
    3207:	31 c0                	xor    %eax,%eax
    3209:	48 01 da             	add    %rbx,%rdx
    320c:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3210:	48 c1 fa 04          	sar    $0x4,%rdx
    3214:	48 29 da             	sub    %rbx,%rdx
    3217:	e8 44 f2 ff ff       	call   2460 <__printf_chk@plt>
  verify(thread_data, thread_count);
    321c:	48 8b 7d b0          	mov    -0x50(%rbp),%rdi
    3220:	be 06 00 00 00       	mov    $0x6,%esi
    3225:	e8 26 27 00 00       	call   5950 <verify>
  return 0;

}
    322a:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    322e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3237:	75 4b                	jne    3284 <main+0xc74>
    3239:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
    323d:	31 c0                	xor    %eax,%eax
    323f:	5b                   	pop    %rbx
    3240:	41 5c                	pop    %r12
    3242:	41 5d                	pop    %r13
    3244:	41 5e                	pop    %r14
    3246:	41 5f                	pop    %r15
    3248:	5d                   	pop    %rbp
    3249:	c3                   	ret
    324a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          thread_data[x].tasks[y].run = barriered_work; 
    3250:	48 8d 05 99 21 00 00 	lea    0x2199(%rip),%rax        # 53f0 <barriered_work>
    3257:	41 be 06 00 00 00    	mov    $0x6,%r14d
    325d:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3265:	e9 3e f8 ff ff       	jmp    2aa8 <main+0x498>
    326a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            thread_data[x].tasks[y].protected = do_protected_write; 
    3270:	48 8d 05 69 01 00 00 	lea    0x169(%rip),%rax        # 33e0 <do_protected_write>
    3277:	4b 89 84 2f 20 01 00 00 	mov    %rax,0x120(%r15,%r13,1)
    327f:	e9 0e f6 ff ff       	jmp    2892 <main+0x282>
}
    3284:	e8 a7 f0 ff ff       	call   2330 <__stack_chk_fail@plt>
    3289:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003290 <_start>:
    3290:	f3 0f 1e fa          	endbr64
    3294:	31 ed                	xor    %ebp,%ebp
    3296:	49 89 d1             	mov    %rdx,%r9
    3299:	5e                   	pop    %rsi
    329a:	48 89 e2             	mov    %rsp,%rdx
    329d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    32a1:	50                   	push   %rax
    32a2:	54                   	push   %rsp
    32a3:	45 31 c0             	xor    %r8d,%r8d
    32a6:	31 c9                	xor    %ecx,%ecx
    32a8:	48 8d 3d 61 f3 ff ff 	lea    -0xc9f(%rip),%rdi        # 2610 <main>
    32af:	ff 15 1b 5d 00 00    	call   *0x5d1b(%rip)        # 8fd0 <__libc_start_main@GLIBC_2.34>
    32b5:	f4                   	hlt
    32b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000032c0 <__gmon_start__>:
    32c0:	f3 0f 1e fa          	endbr64
    32c4:	8b 05 5e 5d 00 00    	mov    0x5d5e(%rip),%eax        # 9028 <called.0>
    32ca:	85 c0                	test   %eax,%eax
    32cc:	74 02                	je     32d0 <__gmon_start__+0x10>
    32ce:	c3                   	ret
    32cf:	90                   	nop
    32d0:	48 83 ec 08          	sub    $0x8,%rsp
    32d4:	48 8d 35 02 2a 00 00 	lea    0x2a02(%rip),%rsi        # 5cdd <etext>
    32db:	48 8d 3d 1e cd ff ff 	lea    -0x32e2(%rip),%rdi        # 0 <__executable_start>
    32e2:	c7 05 3c 5d 00 00 01 00 00 00 	movl   $0x1,0x5d3c(%rip)        # 9028 <called.0>
    32ec:	e8 cf f0 ff ff       	call   23c0 <__monstartup@plt>
    32f1:	48 8b 3d e8 5c 00 00 	mov    0x5ce8(%rip),%rdi        # 8fe0 <_mcleanup@GLIBC_2.2.5>
    32f8:	48 83 c4 08          	add    $0x8,%rsp
    32fc:	e9 9f 29 00 00       	jmp    5ca0 <atexit>
    3301:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    330b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003310 <_dl_relocate_static_pie>:
    3310:	f3 0f 1e fa          	endbr64
    3314:	c3                   	ret
    3315:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    331f:	90                   	nop

0000000000003320 <deregister_tm_clones>:
    3320:	48 8d 3d f9 5c 00 00 	lea    0x5cf9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3327:	48 8d 05 f2 5c 00 00 	lea    0x5cf2(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    332e:	48 39 f8             	cmp    %rdi,%rax
    3331:	74 15                	je     3348 <deregister_tm_clones+0x28>
    3333:	48 8b 05 9e 5c 00 00 	mov    0x5c9e(%rip),%rax        # 8fd8 <_ITM_deregisterTMCloneTable@Base>
    333a:	48 85 c0             	test   %rax,%rax
    333d:	74 09                	je     3348 <deregister_tm_clones+0x28>
    333f:	ff e0                	jmp    *%rax
    3341:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3348:	c3                   	ret
    3349:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003350 <register_tm_clones>:
    3350:	48 8d 3d c9 5c 00 00 	lea    0x5cc9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3357:	48 8d 35 c2 5c 00 00 	lea    0x5cc2(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    335e:	48 29 fe             	sub    %rdi,%rsi
    3361:	48 89 f0             	mov    %rsi,%rax
    3364:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3368:	48 c1 f8 03          	sar    $0x3,%rax
    336c:	48 01 c6             	add    %rax,%rsi
    336f:	48 d1 fe             	sar    %rsi
    3372:	74 14                	je     3388 <register_tm_clones+0x38>
    3374:	48 8b 05 75 5c 00 00 	mov    0x5c75(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    337b:	48 85 c0             	test   %rax,%rax
    337e:	74 08                	je     3388 <register_tm_clones+0x38>
    3380:	ff e0                	jmp    *%rax
    3382:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3388:	c3                   	ret
    3389:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003390 <__do_global_dtors_aux>:
    3390:	f3 0f 1e fa          	endbr64
    3394:	80 3d 91 5c 00 00 00 	cmpb   $0x0,0x5c91(%rip)        # 902c <completed.0>
    339b:	75 2b                	jne    33c8 <__do_global_dtors_aux+0x38>
    339d:	55                   	push   %rbp
    339e:	48 83 3d 52 5c 00 00 00 	cmpq   $0x0,0x5c52(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    33a6:	48 89 e5             	mov    %rsp,%rbp
    33a9:	74 0c                	je     33b7 <__do_global_dtors_aux+0x27>
    33ab:	48 8b 3d 56 5c 00 00 	mov    0x5c56(%rip),%rdi        # 9008 <__dso_handle>
    33b2:	e8 09 ef ff ff       	call   22c0 <__cxa_finalize@plt>
    33b7:	e8 64 ff ff ff       	call   3320 <deregister_tm_clones>
    33bc:	c6 05 69 5c 00 00 01 	movb   $0x1,0x5c69(%rip)        # 902c <completed.0>
    33c3:	5d                   	pop    %rbp
    33c4:	c3                   	ret
    33c5:	0f 1f 00             	nopl   (%rax)
    33c8:	c3                   	ret
    33c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000033d0 <frame_dummy>:
    33d0:	f3 0f 1e fa          	endbr64
    33d4:	e9 77 ff ff ff       	jmp    3350 <register_tm_clones>
    33d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000033e0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    33e0:	f3 0f 1e fa          	endbr64
    33e4:	55                   	push   %rbp
    33e5:	48 89 e5             	mov    %rsp,%rbp
    33e8:	ff 15 fa 5b 00 00    	call   *0x5bfa(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  struct ProtectedState *protected = data->thread->protected_state;
    33ee:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    33f5:	48 8b 40 30          	mov    0x30(%rax),%rax
  data->v++; // thread local
    33f9:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3401:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    3405:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3409:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3410:	48 85 c9             	test   %rcx,%rcx
    3413:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    341a:	48 0f 4f d6          	cmovg  %rsi,%rdx
    341e:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3422:	31 c0                	xor    %eax,%eax
    3424:	5d                   	pop    %rbp
    3425:	c3                   	ret
    3426:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003430 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3430:	f3 0f 1e fa          	endbr64
    3434:	55                   	push   %rbp
    3435:	48 89 e5             	mov    %rsp,%rbp
    3438:	ff 15 aa 5b 00 00    	call   *0x5baa(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    for (int x = 0 ; x < data->task_count ; x++) {
    343e:	48 63 8f 84 01 00 00 	movslq 0x184(%rdi),%rcx
    3445:	85 c9                	test   %ecx,%ecx
    3447:	7e 6a                	jle    34b3 <barriered_reset+0x83>
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    3449:	48 63 87 30 01 00 00 	movslq 0x130(%rdi),%rax
    3450:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    3457:	48 8d 0c 89          	lea    (%rcx,%rcx,4),%rcx
    345b:	48 c1 e1 07          	shl    $0x7,%rcx
    345f:	48 8d 3c c0          	lea    (%rax,%rax,8),%rdi
      data->thread->tasks[x].available = 1; 
    3463:	49 8b 70 20          	mov    0x20(%r8),%rsi
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    3467:	48 8d 04 78          	lea    (%rax,%rdi,2),%rax
    346b:	49 8b 78 10          	mov    0x10(%r8),%rdi
    346f:	48 8d 96 80 01 00 00 	lea    0x180(%rsi),%rdx
    3476:	48 8d 8c 0e 80 01 00 00 	lea    0x180(%rsi,%rcx,1),%rcx
    347e:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3482:	48 8b 40 20          	mov    0x20(%rax),%rax
    3486:	48 05 00 01 00 00    	add    $0x100,%rax
    348c:	0f 1f 40 00          	nopl   0x0(%rax)
    3490:	83 40 80 01          	addl   $0x1,-0x80(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
    3494:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
      data->thread->threads[data->thread_index].tasks[x].prearrive++; 
    349b:	83 00 01             	addl   $0x1,(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
    349e:	48 05 80 02 00 00    	add    $0x280,%rax
      data->thread->tasks[x].available = 1; 
    34a4:	c7 82 80 fd ff ff 01 00 00 00 	movl   $0x1,-0x280(%rdx)
    for (int x = 0 ; x < data->task_count ; x++) {
    34ae:	48 39 ca             	cmp    %rcx,%rdx
    34b1:	75 dd                	jne    3490 <barriered_reset+0x60>
  asm volatile ("mfence" ::: "memory");
    34b3:	0f ae f0             	mfence
}
    34b6:	31 c0                	xor    %eax,%eax
    34b8:	5d                   	pop    %rbp
    34b9:	c3                   	ret
    34ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000034c0 <barriered_thread>:
void* barriered_thread(void *arg) {
    34c0:	f3 0f 1e fa          	endbr64
    34c4:	55                   	push   %rbp
    34c5:	48 89 e5             	mov    %rsp,%rbp
    34c8:	41 57                	push   %r15
    34ca:	41 56                	push   %r14
    34cc:	41 55                	push   %r13
    34ce:	41 54                	push   %r12
    34d0:	53                   	push   %rbx
    34d1:	48 83 ec 18          	sub    $0x18,%rsp
    34d5:	ff 15 0d 5b 00 00    	call   *0x5b0d(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  int waiting = 0;
    34db:	45 31 ff             	xor    %r15d,%r15d
  int t = 0;
    34de:	31 db                	xor    %ebx,%ebx
            waiting = 0;
    34e0:	45 31 ed             	xor    %r13d,%r13d
void* barriered_thread(void *arg) {
    34e3:	49 89 fe             	mov    %rdi,%r14
  while (data->running == 1) {
    34e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    34f0:	41 83 7e 2c 01       	cmpl   $0x1,0x2c(%r14)
    34f5:	0f 85 56 02 00 00    	jne    3751 <barriered_thread+0x291>
    if (t >= data->task_count) {
    34fb:	41 8b 56 28          	mov    0x28(%r14),%edx
    34ff:	39 da                	cmp    %ebx,%edx
    3501:	7f 0e                	jg     3511 <barriered_thread+0x51>
      data->cycles++;
    3503:	49 83 86 90 00 00 00 01 	addq   $0x1,0x90(%r14)
    for (; t < data->task_count; t++) {
    350b:	31 db                	xor    %ebx,%ebx
    350d:	85 d2                	test   %edx,%edx
    350f:	7e df                	jle    34f0 <barriered_thread+0x30>
    3511:	48 63 c3             	movslq %ebx,%rax
    3514:	4c 8d 24 80          	lea    (%rax,%rax,4),%r12
    3518:	49 c1 e4 07          	shl    $0x7,%r12
    351c:	eb 10                	jmp    352e <barriered_thread+0x6e>
    351e:	66 90                	xchg   %ax,%ax
    3520:	83 c3 01             	add    $0x1,%ebx
    3523:	49 81 c4 80 02 00 00 	add    $0x280,%r12
    352a:	39 d3                	cmp    %edx,%ebx
    352c:	7d c2                	jge    34f0 <barriered_thread+0x30>
      if (data->tasks[t].available == 1) {
    352e:	49 8b 46 20          	mov    0x20(%r14),%rax
    3532:	4a 8d 0c 20          	lea    (%rax,%r12,1),%rcx
    3536:	83 b9 80 01 00 00 01 	cmpl   $0x1,0x180(%rcx)
    353d:	75 e1                	jne    3520 <barriered_thread+0x60>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    353f:	41 8b 7e 18          	mov    0x18(%r14),%edi
          previous = t - 1;
    3543:	83 ea 01             	sub    $0x1,%edx
    3546:	8d 73 ff             	lea    -0x1(%rbx),%esi
    3549:	85 db                	test   %ebx,%ebx
    354b:	0f 4f d6             	cmovg  %esi,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    354e:	85 ff                	test   %edi,%edi
    3550:	0f 8e ea 01 00 00    	jle    3740 <barriered_thread+0x280>
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    3556:	48 63 d2             	movslq %edx,%rdx
    3559:	44 8b 91 80 00 00 00 	mov    0x80(%rcx),%r10d
    3560:	49 8b 46 10          	mov    0x10(%r14),%rax
        int prearrive = 0; 
    3564:	45 31 db             	xor    %r11d,%r11d
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    3567:	48 8d 34 92          	lea    (%rdx,%rdx,4),%rsi
    356b:	48 63 d7             	movslq %edi,%rdx
          if (data->threads[thread].tasks[previous].prearrive == data->tasks[t].prearrive) {
    356e:	44 8b 89 00 01 00 00 	mov    0x100(%rcx),%r9d
    3575:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    3579:	48 c1 e6 07          	shl    $0x7,%rsi
    357d:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
        int arrived = 0; 
    3581:	31 c9                	xor    %ecx,%ecx
    3583:	4c 8d 04 d0          	lea    (%rax,%rdx,8),%r8
    3587:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    3590:	48 8b 50 20          	mov    0x20(%rax),%rdx
    3594:	48 01 f2             	add    %rsi,%rdx
    3597:	44 3b 92 80 00 00 00 	cmp    0x80(%rdx),%r10d
    359e:	75 03                	jne    35a3 <barriered_thread+0xe3>
            arrived++;
    35a0:	83 c1 01             	add    $0x1,%ecx
          if (data->threads[thread].tasks[previous].prearrive == data->tasks[t].prearrive) {
    35a3:	44 3b 8a 00 01 00 00 	cmp    0x100(%rdx),%r9d
    35aa:	75 04                	jne    35b0 <barriered_thread+0xf0>
            prearrive++;
    35ac:	41 83 c3 01          	add    $0x1,%r11d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    35b0:	48 05 98 00 00 00    	add    $0x98,%rax
    35b6:	4c 39 c0             	cmp    %r8,%rax
    35b9:	75 d5                	jne    3590 <barriered_thread+0xd0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    35bb:	44 39 df             	cmp    %r11d,%edi
    35be:	0f 84 9c 00 00 00    	je     3660 <barriered_thread+0x1a0>
    35c4:	45 85 db             	test   %r11d,%r11d
    35c7:	0f 84 93 00 00 00    	je     3660 <barriered_thread+0x1a0>
        if (arrived == 0 || arrived == data->thread_count) {
    35cd:	85 c9                	test   %ecx,%ecx
    35cf:	74 0a                	je     35db <barriered_thread+0x11b>
    35d1:	41 39 4e 18          	cmp    %ecx,0x18(%r14)
    35d5:	0f 85 15 ff ff ff    	jne    34f0 <barriered_thread+0x30>
    35db:	49 8b 46 20          	mov    0x20(%r14),%rax
          data->tasks[t].prearrive++;
    35df:	4c 01 e0             	add    %r12,%rax
    35e2:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    35e9:	85 db                	test   %ebx,%ebx
    35eb:	75 0e                	jne    35fb <barriered_thread+0x13b>
    35ed:	49 8b 76 68          	mov    0x68(%r14),%rsi
    35f1:	49 3b 76 70          	cmp    0x70(%r14),%rsi
    35f5:	0f 8c 25 01 00 00    	jl     3720 <barriered_thread+0x260>
          data->tasks[t].available = 0;
    35fb:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
          data->tasks[t].run(&data->threads[data->thread_index].tasks[t]);
    3605:	49 63 16             	movslq (%r14),%rdx
    3608:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    360c:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
    3610:	49 8b 4e 10          	mov    0x10(%r14),%rcx
    3614:	48 8d 14 d1          	lea    (%rcx,%rdx,8),%rdx
    3618:	48 8b 7a 20          	mov    0x20(%rdx),%rdi
    361c:	4c 01 e7             	add    %r12,%rdi
    361f:	ff 90 18 01 00 00    	call   *0x118(%rax)
          data->tasks[t].arrived++;
    3625:	49 8b 46 20          	mov    0x20(%r14),%rax
    3629:	4c 01 e0             	add    %r12,%rax
    362c:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3633:	41 8b 46 28          	mov    0x28(%r14),%eax
          data->iteration_count++;
    3637:	49 83 46 60 01       	addq   $0x1,0x60(%r14)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    363c:	83 e8 01             	sub    $0x1,%eax
    363f:	39 d8                	cmp    %ebx,%eax
    3641:	74 75                	je     36b8 <barriered_thread+0x1f8>
          asm volatile ("mfence" ::: "memory");
    3643:	0f ae f0             	mfence
          if (waiting == 0) {
    3646:	45 85 ff             	test   %r15d,%r15d
    3649:	0f 84 99 00 00 00    	je     36e8 <barriered_thread+0x228>
            waiting = 0;
    364f:	41 83 ff 03          	cmp    $0x3,%r15d
    for (; t < data->task_count; t++) {
    3653:	41 8b 56 28          	mov    0x28(%r14),%edx
            waiting = 0;
    3657:	45 0f 44 fd          	cmove  %r13d,%r15d
    365b:	e9 c0 fe ff ff       	jmp    3520 <barriered_thread+0x60>
          if (waiting == 1) {
    3660:	41 83 ff 01          	cmp    $0x1,%r15d
    3664:	0f 85 63 ff ff ff    	jne    35cd <barriered_thread+0x10d>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    366a:	49 8b 86 80 00 00 00 	mov    0x80(%r14),%rax
    3671:	bf 04 00 00 00       	mov    $0x4,%edi
    3676:	89 4d cc             	mov    %ecx,-0x34(%rbp)
            waiting = 3;
    3679:	41 bf 03 00 00 00    	mov    $0x3,%r15d
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    367f:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3683:	49 8b 46 78          	mov    0x78(%r14),%rax
    3687:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    368c:	e8 7f ec ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3691:	49 8b 86 80 00 00 00 	mov    0x80(%r14),%rax
            waiting = 3;
    3698:	8b 4d cc             	mov    -0x34(%rbp),%ecx
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    369b:	48 83 c0 01          	add    $0x1,%rax
    369f:	48 99                	cqto
    36a1:	49 f7 be 88 00 00 00 	idivq  0x88(%r14)
    36a8:	49 89 96 80 00 00 00 	mov    %rdx,0x80(%r14)
            waiting = 3;
    36af:	e9 19 ff ff ff       	jmp    35cd <barriered_thread+0x10d>
    36b4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    36b8:	49 8b 76 68          	mov    0x68(%r14),%rsi
    36bc:	49 3b 76 70          	cmp    0x70(%r14),%rsi
    36c0:	0f 8d 7d ff ff ff    	jge    3643 <barriered_thread+0x183>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    36c6:	48 c1 e6 04          	shl    $0x4,%rsi
    36ca:	bf 04 00 00 00       	mov    $0x4,%edi
    36cf:	49 03 76 58          	add    0x58(%r14),%rsi
    36d3:	e8 38 ec ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    36d8:	49 83 46 68 01       	addq   $0x1,0x68(%r14)
    36dd:	e9 61 ff ff ff       	jmp    3643 <barriered_thread+0x183>
    36e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    36e8:	49 8b 86 80 00 00 00 	mov    0x80(%r14),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    36ef:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    36f4:	41 bf 01 00 00 00    	mov    $0x1,%r15d
            data->task_snapshot[data->task_timestamp_count].task = t;
    36fa:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    36fe:	49 8b 46 78          	mov    0x78(%r14),%rax
    3702:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3706:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3709:	e8 02 ec ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    370e:	41 8b 56 28          	mov    0x28(%r14),%edx
    3712:	e9 09 fe ff ff       	jmp    3520 <barriered_thread+0x60>
    3717:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3720:	48 c1 e6 04          	shl    $0x4,%rsi
    3724:	bf 04 00 00 00       	mov    $0x4,%edi
    3729:	49 03 76 50          	add    0x50(%r14),%rsi
    372d:	e8 de eb ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3732:	49 8b 46 20          	mov    0x20(%r14),%rax
    3736:	4c 01 e0             	add    %r12,%rax
    3739:	e9 bd fe ff ff       	jmp    35fb <barriered_thread+0x13b>
    373e:	66 90                	xchg   %ax,%ax
          if (waiting == 1) {
    3740:	41 83 ff 01          	cmp    $0x1,%r15d
    3744:	0f 85 95 fe ff ff    	jne    35df <barriered_thread+0x11f>
        int arrived = 0; 
    374a:	31 c9                	xor    %ecx,%ecx
    374c:	e9 19 ff ff ff       	jmp    366a <barriered_thread+0x1aa>
}
    3751:	48 83 c4 18          	add    $0x18,%rsp
    3755:	31 c0                	xor    %eax,%eax
    3757:	5b                   	pop    %rbx
    3758:	41 5c                	pop    %r12
    375a:	41 5d                	pop    %r13
    375c:	41 5e                	pop    %r14
    375e:	41 5f                	pop    %r15
    3760:	5d                   	pop    %rbp
    3761:	c3                   	ret
    3762:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    376d:	0f 1f 00             	nopl   (%rax)

0000000000003770 <external_thread>:
void * external_thread(void *arg) {
    3770:	f3 0f 1e fa          	endbr64
    3774:	55                   	push   %rbp
    3775:	48 89 e5             	mov    %rsp,%rbp
    3778:	41 56                	push   %r14
    377a:	41 55                	push   %r13
    377c:	41 54                	push   %r12
    377e:	53                   	push   %rbx
    377f:	48 83 ec 30          	sub    $0x30,%rsp
    3783:	ff 15 5f 58 00 00    	call   *0x585f(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  struct timespec req = {
    3789:	66 0f 6f 05 5f 31 00 00 	movdqa 0x315f(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
void * external_thread(void *arg) {
    3791:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    379a:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    379e:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    37a0:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
void * external_thread(void *arg) {
    37a4:	49 89 fe             	mov    %rdi,%r14
  struct timespec req = {
    37a7:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
  while (data->running == 1) {
    37ab:	75 5f                	jne    380c <external_thread+0x9c>
    37ad:	4c 8d 65 c0          	lea    -0x40(%rbp),%r12
    37b1:	48 8d 5d b0          	lea    -0x50(%rbp),%rbx
        data->buffers->buffer[x].data = "Hello world";
    37b5:	4c 8d 2d 48 28 00 00 	lea    0x2848(%rip),%r13        # 6004 <_IO_stdin_used+0x4>
    37bc:	0f 1f 40 00          	nopl   0x0(%rax)
    nanosleep(&req , &rem);
    37c0:	4c 89 e6             	mov    %r12,%rsi
    37c3:	48 89 df             	mov    %rbx,%rdi
    37c6:	e8 85 eb ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    37cb:	49 8b 46 38          	mov    0x38(%r14),%rax
    37cf:	48 63 10             	movslq (%rax),%rdx
    37d2:	85 d2                	test   %edx,%edx
    37d4:	7e 2c                	jle    3802 <external_thread+0x92>
    37d6:	48 8b 40 08          	mov    0x8(%rax),%rax
    37da:	48 c1 e2 04          	shl    $0x4,%rdx
    37de:	48 01 c2             	add    %rax,%rdx
    37e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    37e8:	8b 48 08             	mov    0x8(%rax),%ecx
    37eb:	85 c9                	test   %ecx,%ecx
    37ed:	75 0a                	jne    37f9 <external_thread+0x89>
        data->buffers->buffer[x].data = "Hello world";
    37ef:	4c 89 28             	mov    %r13,(%rax)
        data->buffers->buffer[x].available = 1;
    37f2:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    37f9:	48 83 c0 10          	add    $0x10,%rax
    37fd:	48 39 c2             	cmp    %rax,%rdx
    3800:	75 e6                	jne    37e8 <external_thread+0x78>
    asm volatile ("mfence" ::: "memory");
    3802:	0f ae f0             	mfence
  while (data->running == 1) {
    3805:	41 83 7e 2c 01       	cmpl   $0x1,0x2c(%r14)
    380a:	74 b4                	je     37c0 <external_thread+0x50>
}
    380c:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    3810:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3819:	75 0f                	jne    382a <external_thread+0xba>
    381b:	48 83 c4 30          	add    $0x30,%rsp
    381f:	31 c0                	xor    %eax,%eax
    3821:	5b                   	pop    %rbx
    3822:	41 5c                	pop    %r12
    3824:	41 5d                	pop    %r13
    3826:	41 5e                	pop    %r14
    3828:	5d                   	pop    %rbp
    3829:	c3                   	ret
    382a:	e8 01 eb ff ff       	call   2330 <__stack_chk_fail@plt>
    382f:	90                   	nop

0000000000003830 <timer_thread>:
void* timer_thread(void *arg) {
    3830:	f3 0f 1e fa          	endbr64
    3834:	55                   	push   %rbp
    3835:	48 89 e5             	mov    %rsp,%rbp
    3838:	41 57                	push   %r15
    383a:	41 56                	push   %r14
    383c:	41 55                	push   %r13
    383e:	41 54                	push   %r12
    3840:	53                   	push   %rbx
    3841:	48 83 ec 68          	sub    $0x68,%rsp
    3845:	ff 15 9d 57 00 00    	call   *0x579d(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    384b:	48 8d 35 be 27 00 00 	lea    0x27be(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    3852:	8b 17                	mov    (%rdi),%edx
    3854:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    385d:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    3861:	31 c0                	xor    %eax,%eax
    3863:	49 89 ff             	mov    %rdi,%r15
    3866:	bf 01 00 00 00       	mov    $0x1,%edi
    386b:	e8 f0 eb ff ff       	call   2460 <__printf_chk@plt>
  struct timespec preempt = {
    3870:	66 0f 6f 05 78 30 00 00 	movdqa 0x3078(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    3878:	ba 30 75 00 00       	mov    $0x7530,%edx
    387d:	31 c0                	xor    %eax,%eax
    387f:	48 8d 35 9c 27 00 00 	lea    0x279c(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    3886:	bf 01 00 00 00       	mov    $0x1,%edi
    388b:	0f 29 45 90          	movaps %xmm0,-0x70(%rbp)
    388f:	e8 cc eb ff ff       	call   2460 <__printf_chk@plt>
  while (data->running && n < times) {
    3894:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3898:	89 85 7c ff ff ff    	mov    %eax,-0x84(%rbp)
    389e:	85 c0                	test   %eax,%eax
    38a0:	0f 84 cf 00 00 00    	je     3975 <timer_thread+0x145>
  int n = 0;
    38a6:	45 31 f6             	xor    %r14d,%r14d
    38a9:	4c 8d 65 80          	lea    -0x80(%rbp),%r12
    38ad:	48 8d 5d 90          	lea    -0x70(%rbp),%rbx
        data->threads[x].tasks[y].scheduled = 0;
    38b1:	45 31 ed             	xor    %r13d,%r13d
  int y = 0;
    38b4:	c7 85 7c ff ff ff 00 00 00 00 	movl   $0x0,-0x84(%rbp)
    nanosleep(&preempt , &rem2);
    38be:	48 89 df             	mov    %rbx,%rdi
    38c1:	4c 89 e6             	mov    %r12,%rsi
    n++;
    38c4:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    38c8:	e8 83 ea ff ff       	call   2350 <nanosleep@plt>
    y++;
    38cd:	8b 85 7c ff ff ff    	mov    -0x84(%rbp),%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    38d3:	45 8b 47 18          	mov    0x18(%r15),%r8d
    y++;
    38d7:	8d 78 01             	lea    0x1(%rax),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    38da:	45 85 c0             	test   %r8d,%r8d
    38dd:	7e 6d                	jle    394c <timer_thread+0x11c>
        data->threads[x].tasks[y].scheduled = 0;
    38df:	48 63 85 7c ff ff ff 	movslq -0x84(%rbp),%rax
    38e6:	31 c9                	xor    %ecx,%ecx
    for (int x = 0 ; x < data->thread_count ; x++) {
    38e8:	31 f6                	xor    %esi,%esi
        data->threads[x].tasks[next].scheduled = 1;
    38ea:	41 b9 01 00 00 00    	mov    $0x1,%r9d
        data->threads[x].tasks[y].scheduled = 0;
    38f0:	4c 8d 04 80          	lea    (%rax,%rax,4),%r8
    38f4:	49 c1 e0 07          	shl    $0x7,%r8
    38f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x].task_count;
    3900:	4d 8b 5f 10          	mov    0x10(%r15),%r11
    3904:	89 f8                	mov    %edi,%eax
    3906:	99                   	cltd
    3907:	49 01 cb             	add    %rcx,%r11
    390a:	41 f7 7b 28          	idivl  0x28(%r11)
        data->threads[x].tasks[next].scheduled = 1;
    390e:	48 63 d2             	movslq %edx,%rdx
    3911:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    3915:	44 89 ca             	mov    %r9d,%edx
    3918:	48 c1 e0 07          	shl    $0x7,%rax
    391c:	49 03 43 20          	add    0x20(%r11),%rax
    3920:	48 05 00 02 00 00    	add    $0x200,%rax
    3926:	87 10                	xchg   %edx,(%rax)
        data->threads[x].tasks[y].scheduled = 0;
    3928:	49 8b 47 10          	mov    0x10(%r15),%rax
    392c:	48 8b 44 08 20       	mov    0x20(%rax,%rcx,1),%rax
    3931:	44 89 ea             	mov    %r13d,%edx
    3934:	42 87 94 00 00 02 00 00 	xchg   %edx,0x200(%rax,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    393c:	83 c6 01             	add    $0x1,%esi
    393f:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3946:	41 39 77 18          	cmp    %esi,0x18(%r15)
    394a:	7f b4                	jg     3900 <timer_thread+0xd0>
    asm volatile ("mfence" ::: "memory");
    394c:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    394f:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3953:	41 8b 77 2c          	mov    0x2c(%r15),%esi
    y++;
    3957:	39 78 28             	cmp    %edi,0x28(%rax)
    395a:	41 0f 4e fd          	cmovle %r13d,%edi
    395e:	89 bd 7c ff ff ff    	mov    %edi,-0x84(%rbp)
  while (data->running && n < times) {
    3964:	85 f6                	test   %esi,%esi
    3966:	74 0d                	je     3975 <timer_thread+0x145>
    3968:	41 81 fe 30 75 00 00 	cmp    $0x7530,%r14d
    396f:	0f 85 49 ff ff ff    	jne    38be <timer_thread+0x8e>
    3975:	48 8d 3d bc 26 00 00 	lea    0x26bc(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    397c:	e8 6f e9 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3981:	49 63 47 1c          	movslq 0x1c(%r15),%rax
    3985:	85 c0                	test   %eax,%eax
    3987:	0f 8e 8c 00 00 00    	jle    3a19 <timer_thread+0x1e9>
    for (int y = 0 ; y < data->task_count ; y++) {
    398d:	41 8b 57 28          	mov    0x28(%r15),%edx
    3991:	85 d2                	test   %edx,%edx
    3993:	0f 8e 80 00 00 00    	jle    3a19 <timer_thread+0x1e9>
    3999:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
      data->threads[x].tasks[y].sending = 0;
    399d:	4d 8b 4f 10          	mov    0x10(%r15),%r9
    39a1:	48 8d 3c 48          	lea    (%rax,%rcx,2),%rdi
    39a5:	48 63 c2             	movslq %edx,%rax
    39a8:	31 c9                	xor    %ecx,%ecx
    39aa:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    39ae:	48 c1 e7 03          	shl    $0x3,%rdi
    39b2:	48 c1 e0 07          	shl    $0x7,%rax
    39b6:	4c 8d 80 38 02 00 00 	lea    0x238(%rax),%r8
    39bd:	49 8b 74 09 20       	mov    0x20(%r9,%rcx,1),%rsi
    39c2:	4a 8d 14 06          	lea    (%rsi,%r8,1),%rdx
    39c6:	48 8d 86 38 02 00 00 	lea    0x238(%rsi),%rax
    39cd:	49 89 d3             	mov    %rdx,%r11
    39d0:	49 29 c3             	sub    %rax,%r11
    39d3:	41 81 e3 80 00 00 00 	and    $0x80,%r11d
    39da:	74 16                	je     39f2 <timer_thread+0x1c2>
    for (int y = 0 ; y < data->task_count ; y++) {
    39dc:	48 8d 86 b8 04 00 00 	lea    0x4b8(%rsi),%rax
      data->threads[x].tasks[y].sending = 0;
    39e3:	c7 86 38 02 00 00 00 00 00 00 	movl   $0x0,0x238(%rsi)
    for (int y = 0 ; y < data->task_count ; y++) {
    39ed:	48 39 c2             	cmp    %rax,%rdx
    39f0:	74 1b                	je     3a0d <timer_thread+0x1dd>
      data->threads[x].tasks[y].sending = 0;
    39f2:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    39f8:	48 05 00 05 00 00    	add    $0x500,%rax
      data->threads[x].tasks[y].sending = 0;
    39fe:	c7 80 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3a08:	48 39 c2             	cmp    %rax,%rdx
    3a0b:	75 e5                	jne    39f2 <timer_thread+0x1c2>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3a0d:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3a14:	48 39 cf             	cmp    %rcx,%rdi
    3a17:	75 a4                	jne    39bd <timer_thread+0x18d>
  asm volatile ("mfence" ::: "memory");
    3a19:	0f ae f0             	mfence
  struct timespec drain = {
    3a1c:	66 0f 6f 05 dc 2e 00 00 	movdqa 0x2edc(%rip),%xmm0        # 6900 <_IO_stdin_used+0x900>
    3a24:	4c 8d 25 32 26 00 00 	lea    0x2632(%rip),%r12        # 605d <_IO_stdin_used+0x5d>
    3a2b:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
    y++;
    3a2f:	8b 85 7c ff ff ff    	mov    -0x84(%rbp),%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a35:	41 8b 57 18          	mov    0x18(%r15),%edx
    y++;
    3a39:	8d 70 01             	lea    0x1(%rax),%esi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a3c:	85 d2                	test   %edx,%edx
    3a3e:	7e 65                	jle    3aa5 <timer_thread+0x275>
        data->threads[x].tasks[y].scheduled = 0;
    3a40:	48 63 85 7c ff ff ff 	movslq -0x84(%rbp),%rax
    3a47:	31 c9                	xor    %ecx,%ecx
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a49:	31 ff                	xor    %edi,%edi
        data->threads[x].tasks[y].scheduled = 0;
    3a4b:	4c 8d 04 80          	lea    (%rax,%rax,4),%r8
    3a4f:	49 c1 e0 07          	shl    $0x7,%r8
    3a53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x].task_count;
    3a58:	4d 8b 4f 10          	mov    0x10(%r15),%r9
    3a5c:	89 f0                	mov    %esi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    3a5e:	bb 01 00 00 00       	mov    $0x1,%ebx
        int next = (y + 1) % data->threads[x].task_count;
    3a63:	99                   	cltd
    3a64:	49 01 c9             	add    %rcx,%r9
    3a67:	41 f7 79 28          	idivl  0x28(%r9)
        data->threads[x].tasks[next].scheduled = 1;
    3a6b:	48 63 c2             	movslq %edx,%rax
    3a6e:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3a72:	48 c1 e0 07          	shl    $0x7,%rax
    3a76:	49 03 41 20          	add    0x20(%r9),%rax
    3a7a:	48 05 00 02 00 00    	add    $0x200,%rax
    3a80:	87 18                	xchg   %ebx,(%rax)
        data->threads[x].tasks[y].scheduled = 0;
    3a82:	31 db                	xor    %ebx,%ebx
    3a84:	49 8b 47 10          	mov    0x10(%r15),%rax
    3a88:	48 8b 44 08 20       	mov    0x20(%rax,%rcx,1),%rax
    3a8d:	42 87 9c 00 00 02 00 00 	xchg   %ebx,0x200(%rax,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a95:	83 c7 01             	add    $0x1,%edi
    3a98:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3a9f:	41 39 7f 18          	cmp    %edi,0x18(%r15)
    3aa3:	7f b3                	jg     3a58 <timer_thread+0x228>
    asm volatile ("mfence" ::: "memory");
    3aa5:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    3aa8:	49 8b 57 10          	mov    0x10(%r15),%rdx
    y++;
    3aac:	31 c0                	xor    %eax,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3aae:	41 8b 7f 18          	mov    0x18(%r15),%edi
    y++;
    3ab2:	39 72 28             	cmp    %esi,0x28(%rdx)
    3ab5:	0f 4e f0             	cmovle %eax,%esi
    3ab8:	89 b5 7c ff ff ff    	mov    %esi,-0x84(%rbp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3abe:	85 ff                	test   %edi,%edi
    3ac0:	0f 8e bb 00 00 00    	jle    3b81 <timer_thread+0x351>
    3ac6:	31 db                	xor    %ebx,%ebx
    3ac8:	45 31 ed             	xor    %r13d,%r13d
    3acb:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    3ad1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            all_empty = 0;
    3ad8:	45 31 f6             	xor    %r14d,%r14d
    3adb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3ae0:	4b 8d 04 b6          	lea    (%r14,%r14,4),%rax
    3ae4:	48 c1 e0 07          	shl    $0x7,%rax
    3ae8:	48 03 44 1a 20       	add    0x20(%rdx,%rbx,1),%rax
        for (int k = 0 ; k < data->thread_count; k++) {
    3aed:	31 d2                	xor    %edx,%edx
    3aef:	48 8b 80 28 02 00 00 	mov    0x228(%rax),%rax
    3af6:	eb 18                	jmp    3b10 <timer_thread+0x2e0>
    3af8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3b00:	4d 85 c0             	test   %r8,%r8
    3b03:	7f 25                	jg     3b2a <timer_thread+0x2fa>
        for (int k = 0 ; k < data->thread_count; k++) {
    3b05:	83 c2 01             	add    $0x1,%edx
    3b08:	48 83 c0 20          	add    $0x20,%rax
    3b0c:	39 fa                	cmp    %edi,%edx
    3b0e:	74 30                	je     3b40 <timer_thread+0x310>
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3b10:	48 8b 08             	mov    (%rax),%rcx
    3b13:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3b17:	48 8b 89 80 00 00 00 	mov    0x80(%rcx),%rcx
    3b1e:	4c 8b 86 80 00 00 00 	mov    0x80(%rsi),%r8
    3b25:	48 85 c9             	test   %rcx,%rcx
    3b28:	7e d6                	jle    3b00 <timer_thread+0x2d0>
    3b2a:	bf 01 00 00 00       	mov    $0x1,%edi
    3b2f:	4c 89 e6             	mov    %r12,%rsi
    3b32:	31 c0                	xor    %eax,%eax
    3b34:	e8 27 e9 ff ff       	call   2460 <__printf_chk@plt>
            break;
    3b39:	41 8b 7f 18          	mov    0x18(%r15),%edi
            all_empty = 0;
    3b3d:	45 31 db             	xor    %r11d,%r11d
      for (int y = 0 ; y < data->thread_count ; y++) {
    3b40:	49 83 c6 01          	add    $0x1,%r14
    3b44:	44 39 f7             	cmp    %r14d,%edi
    3b47:	7e 07                	jle    3b50 <timer_thread+0x320>
    3b49:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3b4d:	eb 91                	jmp    3ae0 <timer_thread+0x2b0>
    3b4f:	90                   	nop
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b50:	41 83 c5 01          	add    $0x1,%r13d
    3b54:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3b5b:	44 39 ef             	cmp    %r13d,%edi
    3b5e:	7e 09                	jle    3b69 <timer_thread+0x339>
    3b60:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3b64:	e9 6f ff ff ff       	jmp    3ad8 <timer_thread+0x2a8>
    if (all_empty == 1) {
    3b69:	41 83 fb 01          	cmp    $0x1,%r11d
    3b6d:	74 12                	je     3b81 <timer_thread+0x351>
      nanosleep(&drain , &drainrem);
    3b6f:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    3b73:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
    3b77:	e8 d4 e7 ff ff       	call   2350 <nanosleep@plt>
    3b7c:	e9 ae fe ff ff       	jmp    3a2f <timer_thread+0x1ff>
    3b81:	48 8d 3d cc 24 00 00 	lea    0x24cc(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3b88:	e8 63 e7 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3b8d:	41 8b 4f 2c          	mov    0x2c(%r15),%ecx
    3b91:	85 c9                	test   %ecx,%ecx
    3b93:	0f 84 ba 00 00 00    	je     3c53 <timer_thread+0x423>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b99:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3b9d:	85 c9                	test   %ecx,%ecx
    3b9f:	7e 3c                	jle    3bdd <timer_thread+0x3ad>
    3ba1:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3ba5:	31 db                	xor    %ebx,%ebx
    3ba7:	45 31 e4             	xor    %r12d,%r12d
    3baa:	4c 8d 2d bd 24 00 00 	lea    0x24bd(%rip),%r13        # 606e <_IO_stdin_used+0x6e>
    3bb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->threads[x].running = 0;
    3bb8:	48 8d 04 1a          	lea    (%rdx,%rbx,1),%rax
      if (data->threads[x].type == IO) {
    3bbc:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
      data->threads[x].running = 0;
    3bc0:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
      if (data->threads[x].type == IO) {
    3bc7:	0f 84 b2 00 00 00    	je     3c7f <timer_thread+0x44f>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3bcd:	41 83 c4 01          	add    $0x1,%r12d
    3bd1:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3bd8:	41 39 cc             	cmp    %ecx,%r12d
    3bdb:	7c db                	jl     3bb8 <timer_thread+0x388>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bdd:	41 8b 47 18          	mov    0x18(%r15),%eax
    3be1:	85 c0                	test   %eax,%eax
    3be3:	7e 57                	jle    3c3c <timer_thread+0x40c>
      for (int y = 0 ; y < data->task_count ; y++) {
    3be5:	41 8b 47 28          	mov    0x28(%r15),%eax
    3be9:	31 f6                	xor    %esi,%esi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3beb:	45 31 c0             	xor    %r8d,%r8d
        data->threads[x].tasks[y].scheduled = 0;
    3bee:	31 ff                	xor    %edi,%edi
      for (int y = 0 ; y < data->task_count ; y++) {
    3bf0:	85 c0                	test   %eax,%eax
    3bf2:	7e 48                	jle    3c3c <timer_thread+0x40c>
    3bf4:	31 d2                	xor    %edx,%edx
    3bf6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        data->threads[x].tasks[y].scheduled = 0;
    3c00:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3c04:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    3c08:	89 fb                	mov    %edi,%ebx
    3c0a:	48 c1 e0 07          	shl    $0x7,%rax
    3c0e:	48 03 44 31 20       	add    0x20(%rcx,%rsi,1),%rax
    3c13:	48 05 00 02 00 00    	add    $0x200,%rax
    3c19:	87 18                	xchg   %ebx,(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3c1b:	41 8b 47 28          	mov    0x28(%r15),%eax
    3c1f:	48 83 c2 01          	add    $0x1,%rdx
    3c23:	39 d0                	cmp    %edx,%eax
    3c25:	7f d9                	jg     3c00 <timer_thread+0x3d0>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c27:	41 83 c0 01          	add    $0x1,%r8d
    3c2b:	45 3b 47 18          	cmp    0x18(%r15),%r8d
    3c2f:	7d 0b                	jge    3c3c <timer_thread+0x40c>
    3c31:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
      for (int y = 0 ; y < data->task_count ; y++) {
    3c38:	85 c0                	test   %eax,%eax
    3c3a:	7f b8                	jg     3bf4 <timer_thread+0x3c4>
    asm volatile ("mfence" ::: "memory");
    3c3c:	0f ae f0             	mfence
    3c3f:	48 8d 3d 3a 24 00 00 	lea    0x243a(%rip),%rdi        # 6080 <_IO_stdin_used+0x80>
    3c46:	e8 a5 e6 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3c4b:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
    3c53:	48 8d 3d 2d 24 00 00 	lea    0x242d(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3c5a:	e8 91 e6 ff ff       	call   22f0 <puts@plt>
}
    3c5f:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    3c63:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3c6c:	75 4c                	jne    3cba <timer_thread+0x48a>
    3c6e:	48 83 c4 68          	add    $0x68,%rsp
    3c72:	31 c0                	xor    %eax,%eax
    3c74:	5b                   	pop    %rbx
    3c75:	41 5c                	pop    %r12
    3c77:	41 5d                	pop    %r13
    3c79:	41 5e                	pop    %r14
    3c7b:	41 5f                	pop    %r15
    3c7d:	5d                   	pop    %rbp
    3c7e:	c3                   	ret
    3c7f:	4c 89 ef             	mov    %r13,%rdi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c82:	41 83 c4 01          	add    $0x1,%r12d
    3c86:	e8 65 e6 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]._eventfd, 1);
    3c8b:	49 8b 47 10          	mov    0x10(%r15),%rax
    3c8f:	be 01 00 00 00       	mov    $0x1,%esi
    3c94:	8b 7c 18 48          	mov    0x48(%rax,%rbx,1),%edi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c98:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
        eventfd_write(data->threads[x]._eventfd, 1);
    3c9f:	e8 6c e7 ff ff       	call   2410 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ca4:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3ca8:	41 39 cc             	cmp    %ecx,%r12d
    3cab:	0f 8d 2c ff ff ff    	jge    3bdd <timer_thread+0x3ad>
    3cb1:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3cb5:	e9 fe fe ff ff       	jmp    3bb8 <timer_thread+0x388>
}
    3cba:	e8 71 e6 ff ff       	call   2330 <__stack_chk_fail@plt>
    3cbf:	90                   	nop

0000000000003cc0 <strtolower>:
void strtolower(char *str) {
    3cc0:	f3 0f 1e fa          	endbr64
    3cc4:	55                   	push   %rbp
    3cc5:	48 89 e5             	mov    %rsp,%rbp
    3cc8:	41 54                	push   %r12
    3cca:	53                   	push   %rbx
    3ccb:	ff 15 17 53 00 00    	call   *0x5317(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    for (; *str; ++str)
    3cd1:	48 0f be 1f          	movsbq (%rdi),%rbx
void strtolower(char *str) {
    3cd5:	49 89 fc             	mov    %rdi,%r12
    for (; *str; ++str)
    3cd8:	84 db                	test   %bl,%bl
    3cda:	74 24                	je     3d00 <strtolower+0x40>
        *str = (char)tolower(*str);
    3cdc:	e8 4f e8 ff ff       	call   2530 <__ctype_tolower_loc@plt>
    3ce1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3ce8:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3ceb:	49 83 c4 01          	add    $0x1,%r12
        *str = (char)tolower(*str);
    3cef:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3cf2:	41 88 54 24 ff       	mov    %dl,-0x1(%r12)
    for (; *str; ++str)
    3cf7:	49 0f be 1c 24       	movsbq (%r12),%rbx
    3cfc:	84 db                	test   %bl,%bl
    3cfe:	75 e8                	jne    3ce8 <strtolower+0x28>
}
    3d00:	5b                   	pop    %rbx
    3d01:	41 5c                	pop    %r12
    3d03:	5d                   	pop    %rbp
    3d04:	c3                   	ret
    3d05:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003d10 <zh_malloc>:
void *zh_malloc(size_t size) {
    3d10:	f3 0f 1e fa          	endbr64
    3d14:	55                   	push   %rbp
    3d15:	48 89 e5             	mov    %rsp,%rbp
    3d18:	ff 15 ca 52 00 00    	call   *0x52ca(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    void *buf = malloc(size);
    3d1e:	e8 fd e6 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    3d23:	48 85 c0             	test   %rax,%rax
    3d26:	74 02                	je     3d2a <zh_malloc+0x1a>
}
    3d28:	5d                   	pop    %rbp
    3d29:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3d2a:	48 8b 0d ef 52 00 00 	mov    0x52ef(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3d31:	ba 28 00 00 00       	mov    $0x28,%edx
    3d36:	be 01 00 00 00       	mov    $0x1,%esi
    3d3b:	48 8d 3d de 26 00 00 	lea    0x26de(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    3d42:	e8 99 e7 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    3d47:	bf 01 00 00 00       	mov    $0x1,%edi
    3d4c:	e8 6f e7 ff ff       	call   24c0 <exit@plt>
    3d51:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3d5c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003d60 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3d60:	f3 0f 1e fa          	endbr64
    3d64:	55                   	push   %rbp
    3d65:	48 89 e5             	mov    %rsp,%rbp
    3d68:	53                   	push   %rbx
    3d69:	48 83 ec 08          	sub    $0x8,%rsp
    3d6d:	ff 15 75 52 00 00    	call   *0x5275(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    const char *dot = strrchr(filename, '.');
    3d73:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3d78:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3d7b:	e8 e0 e5 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3d80:	48 85 c0             	test   %rax,%rax
    3d83:	74 13                	je     3d98 <get_filename_ext+0x38>
    3d85:	48 39 c3             	cmp    %rax,%rbx
    3d88:	74 0e                	je     3d98 <get_filename_ext+0x38>
}
    3d8a:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    return dot + 1;
    3d8e:	48 83 c0 01          	add    $0x1,%rax
}
    3d92:	c9                   	leave
    3d93:	c3                   	ret
    3d94:	0f 1f 40 00          	nopl   0x0(%rax)
    3d98:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
        return "";
    3d9c:	48 8d 05 2c 23 00 00 	lea    0x232c(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
}
    3da3:	c9                   	leave
    3da4:	c3                   	ret
    3da5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003db0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3db0:	f3 0f 1e fa          	endbr64
    3db4:	55                   	push   %rbp
    3db5:	48 89 e5             	mov    %rsp,%rbp
    3db8:	41 56                	push   %r14
    3dba:	41 55                	push   %r13
    3dbc:	41 54                	push   %r12
    3dbe:	53                   	push   %rbx
    3dbf:	48 81 ec 10 08 00 00 	sub    $0x810,%rsp
    3dc6:	ff 15 1c 52 00 00    	call   *0x521c(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    3dcc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3dd5:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    3dd9:	31 c0                	xor    %eax,%eax
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3ddb:	4c 8d ad d0 f7 ff ff 	lea    -0x830(%rbp),%r13
    3de2:	49 89 f6             	mov    %rsi,%r14
    3de5:	49 89 d4             	mov    %rdx,%r12
    3de8:	48 89 fe             	mov    %rdi,%rsi
    3deb:	ba 00 04 00 00       	mov    $0x400,%edx
    3df0:	4c 89 ef             	mov    %r13,%rdi
    3df3:	e8 48 e6 ff ff       	call   2440 <__strcpy_chk@plt>
    for (; *str; ++str)
    3df8:	48 0f be 9d d0 f7 ff ff 	movsbq -0x830(%rbp),%rbx
    3e00:	84 db                	test   %bl,%bl
    3e02:	74 1e                	je     3e22 <send_headers+0x72>
        *str = (char)tolower(*str);
    3e04:	e8 27 e7 ff ff       	call   2530 <__ctype_tolower_loc@plt>
    3e09:	48 8b 08             	mov    (%rax),%rcx
    3e0c:	4c 89 e8             	mov    %r13,%rax
    3e0f:	90                   	nop
    3e10:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3e13:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3e17:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3e1a:	48 0f be 18          	movsbq (%rax),%rbx
    3e1e:	84 db                	test   %bl,%bl
    3e20:	75 ee                	jne    3e10 <send_headers+0x60>
    void *buf = malloc(size);
    3e22:	bf 11 00 00 00       	mov    $0x11,%edi
    3e27:	e8 f4 e5 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    3e2c:	48 85 c0             	test   %rax,%rax
    3e2f:	0f 84 72 04 00 00    	je     42a7 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3e35:	66 0f 6f 05 d3 2a 00 00 	movdqa 0x2ad3(%rip),%xmm0        # 6910 <_IO_stdin_used+0x910>
    iov[0].iov_base = zh_malloc(slen);
    3e3d:	49 89 04 24          	mov    %rax,(%r12)
    void *buf = malloc(size);
    3e41:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3e46:	49 c7 44 24 08 11 00 00 00 	movq   $0x11,0x8(%r12)
    3e4f:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3e53:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3e56:	e8 c5 e5 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    3e5b:	48 85 c0             	test   %rax,%rax
    3e5e:	0f 84 43 04 00 00    	je     42a7 <send_headers+0x4f7>
    3e64:	66 0f 6f 05 b4 2a 00 00 	movdqa 0x2ab4(%rip),%xmm0        # 6920 <_IO_stdin_used+0x920>
    iov[1].iov_base = zh_malloc(slen);
    3e6c:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    const char *dot = strrchr(filename, '.');
    3e71:	4c 89 ef             	mov    %r13,%rdi
    3e74:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3e7e:	49 c7 44 24 18 17 00 00 00 	movq   $0x17,0x18(%r12)
    3e87:	0f 11 00             	movups %xmm0,(%rax)
    3e8a:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3e8e:	be 2e 00 00 00       	mov    $0x2e,%esi
    3e93:	e8 c8 e4 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3e98:	48 85 c0             	test   %rax,%rax
    3e9b:	0f 84 df 02 00 00    	je     4180 <send_headers+0x3d0>
    3ea1:	4c 39 e8             	cmp    %r13,%rax
    3ea4:	0f 84 d6 02 00 00    	je     4180 <send_headers+0x3d0>
    return dot + 1;
    3eaa:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3eae:	48 8d 3d e8 21 00 00 	lea    0x21e8(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3eb5:	48 89 de             	mov    %rbx,%rsi
    3eb8:	e8 f3 e4 ff ff       	call   23b0 <strcmp@plt>
    3ebd:	85 c0                	test   %eax,%eax
    3ebf:	75 1e                	jne    3edf <send_headers+0x12f>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3ec1:	66 0f 6f 05 67 2a 00 00 	movdqa 0x2a67(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3ec9:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    3ed0:	66 0f 6f 05 68 2a 00 00 	movdqa 0x2a68(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3ed8:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("jpeg", file_ext) == 0)
    3edf:	48 89 de             	mov    %rbx,%rsi
    3ee2:	48 8d 3d b8 21 00 00 	lea    0x21b8(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3ee9:	e8 c2 e4 ff ff       	call   23b0 <strcmp@plt>
    3eee:	85 c0                	test   %eax,%eax
    3ef0:	75 1e                	jne    3f10 <send_headers+0x160>
    3ef2:	66 0f 6f 05 36 2a 00 00 	movdqa 0x2a36(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3efa:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    3f01:	66 0f 6f 05 37 2a 00 00 	movdqa 0x2a37(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3f09:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("png", file_ext) == 0)
    3f10:	48 89 de             	mov    %rbx,%rsi
    3f13:	48 8d 3d 8c 21 00 00 	lea    0x218c(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3f1a:	e8 91 e4 ff ff       	call   23b0 <strcmp@plt>
    3f1f:	85 c0                	test   %eax,%eax
    3f21:	0f 84 09 02 00 00    	je     4130 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    3f27:	48 89 de             	mov    %rbx,%rsi
    3f2a:	48 8d 3d 79 21 00 00 	lea    0x2179(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3f31:	e8 7a e4 ff ff       	call   23b0 <strcmp@plt>
    3f36:	85 c0                	test   %eax,%eax
    3f38:	0f 84 a2 02 00 00    	je     41e0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    3f3e:	48 89 de             	mov    %rbx,%rsi
    3f41:	48 8d 3d 66 21 00 00 	lea    0x2166(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3f48:	e8 63 e4 ff ff       	call   23b0 <strcmp@plt>
    3f4d:	85 c0                	test   %eax,%eax
    3f4f:	0f 84 63 02 00 00    	je     41b8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    3f55:	48 89 de             	mov    %rbx,%rsi
    3f58:	48 8d 3d 92 21 00 00 	lea    0x2192(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3f5f:	e8 4c e4 ff ff       	call   23b0 <strcmp@plt>
    3f64:	85 c0                	test   %eax,%eax
    3f66:	0f 84 24 02 00 00    	je     4190 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    3f6c:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3f6f:	0f 84 53 01 00 00    	je     40c8 <send_headers+0x318>
    if (strcmp("css", file_ext) == 0)
    3f75:	48 89 de             	mov    %rbx,%rsi
    3f78:	48 8d 3d 33 21 00 00 	lea    0x2133(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3f7f:	e8 2c e4 ff ff       	call   23b0 <strcmp@plt>
    3f84:	85 c0                	test   %eax,%eax
    3f86:	0f 84 a4 02 00 00    	je     4230 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    3f8c:	48 89 de             	mov    %rbx,%rsi
    3f8f:	48 8d 3d 20 21 00 00 	lea    0x2120(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3f96:	e8 15 e4 ff ff       	call   23b0 <strcmp@plt>
    3f9b:	85 c0                	test   %eax,%eax
    3f9d:	0f 84 65 02 00 00    	je     4208 <send_headers+0x458>
    slen = strlen(send_buffer);
    3fa3:	4c 8d ad d0 fb ff ff 	lea    -0x430(%rbp),%r13
    3faa:	4c 89 ef             	mov    %r13,%rdi
    3fad:	e8 6e e3 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    3fb2:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3fb5:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3fb8:	e8 63 e4 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    3fbd:	48 85 c0             	test   %rax,%rax
    3fc0:	0f 84 e1 02 00 00    	je     42a7 <send_headers+0x4f7>
    iov[2].iov_base = zh_malloc(slen);
    3fc6:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    iov[2].iov_len = slen;
    3fcb:	49 89 5c 24 28       	mov    %rbx,0x28(%r12)
  return __builtin___memcpy_chk (__dest, __src, __len,
    3fd0:	83 fb 08             	cmp    $0x8,%ebx
    3fd3:	0f 83 37 01 00 00    	jae    4110 <send_headers+0x360>
    3fd9:	f6 c3 04             	test   $0x4,%bl
    3fdc:	0f 85 71 02 00 00    	jne    4253 <send_headers+0x4a3>
    3fe2:	85 db                	test   %ebx,%ebx
    3fe4:	74 12                	je     3ff8 <send_headers+0x248>
    3fe6:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    3fed:	88 10                	mov    %dl,(%rax)
    3fef:	f6 c3 02             	test   $0x2,%bl
    3ff2:	0f 85 8b 02 00 00    	jne    4283 <send_headers+0x4d3>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3ff8:	4d 89 f0             	mov    %r14,%r8
    3ffb:	48 8d 0d b8 20 00 00 	lea    0x20b8(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    4002:	4c 89 ef             	mov    %r13,%rdi
    4005:	31 c0                	xor    %eax,%eax
    4007:	ba 00 04 00 00       	mov    $0x400,%edx
    400c:	be 01 00 00 00       	mov    $0x1,%esi
    4011:	e8 2a e5 ff ff       	call   2540 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4016:	4c 89 ef             	mov    %r13,%rdi
    4019:	e8 02 e3 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    401e:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4021:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4024:	e8 f7 e3 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    4029:	48 85 c0             	test   %rax,%rax
    402c:	0f 84 75 02 00 00    	je     42a7 <send_headers+0x4f7>
    iov[3].iov_base = zh_malloc(slen);
    4032:	49 89 44 24 30       	mov    %rax,0x30(%r12)
    iov[3].iov_len = slen;
    4037:	49 89 5c 24 38       	mov    %rbx,0x38(%r12)
    403c:	83 fb 08             	cmp    $0x8,%ebx
    403f:	0f 83 13 01 00 00    	jae    4158 <send_headers+0x3a8>
    4045:	f6 c3 04             	test   $0x4,%bl
    4048:	0f 85 1d 02 00 00    	jne    426b <send_headers+0x4bb>
    404e:	85 db                	test   %ebx,%ebx
    4050:	74 12                	je     4064 <send_headers+0x2b4>
    4052:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    4059:	88 10                	mov    %dl,(%rax)
    405b:	f6 c3 02             	test   $0x2,%bl
    405e:	0f 85 31 02 00 00    	jne    4295 <send_headers+0x4e5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4064:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4069:	bf 02 00 00 00       	mov    $0x2,%edi
    406e:	c6 85 d2 fb ff ff 00 	movb   $0x0,-0x42e(%rbp)
    4075:	66 89 85 d0 fb ff ff 	mov    %ax,-0x430(%rbp)
    407c:	e8 9f e3 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    4081:	48 85 c0             	test   %rax,%rax
    4084:	0f 84 1d 02 00 00    	je     42a7 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    408a:	0f b7 95 d0 fb ff ff 	movzwl -0x430(%rbp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4091:	49 89 44 24 40       	mov    %rax,0x40(%r12)
    iov[4].iov_len = slen;
    4096:	49 c7 44 24 48 02 00 00 00 	movq   $0x2,0x48(%r12)
    409f:	66 89 10             	mov    %dx,(%rax)
}
    40a2:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    40a6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    40af:	0f 85 19 02 00 00    	jne    42ce <send_headers+0x51e>
    40b5:	48 81 c4 10 08 00 00 	add    $0x810,%rsp
    40bc:	5b                   	pop    %rbx
    40bd:	41 5c                	pop    %r12
    40bf:	41 5d                	pop    %r13
    40c1:	41 5e                	pop    %r14
    40c3:	5d                   	pop    %rbp
    40c4:	c3                   	ret
    40c5:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
    40c8:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    40cc:	0f 85 a3 fe ff ff    	jne    3f75 <send_headers+0x1c5>
    40d2:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    40d6:	0f 85 99 fe ff ff    	jne    3f75 <send_headers+0x1c5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40dc:	66 0f 6f 05 ac 28 00 00 	movdqa 0x28ac(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    40e4:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    40ee:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    40f5:	66 0f 6f 05 a3 28 00 00 	movdqa 0x28a3(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    40fd:	0f 29 85 e0 fb ff ff 	movaps %xmm0,-0x420(%rbp)
    4104:	48 89 85 ef fb ff ff 	mov    %rax,-0x411(%rbp)
    410b:	e9 65 fe ff ff       	jmp    3f75 <send_headers+0x1c5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4110:	89 da                	mov    %ebx,%edx
    4112:	48 89 c7             	mov    %rax,%rdi
    4115:	4c 89 ee             	mov    %r13,%rsi
    4118:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    411d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4122:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4125:	c1 e9 03             	shr    $0x3,%ecx
    4128:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    412b:	e9 c8 fe ff ff       	jmp    3ff8 <send_headers+0x248>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4130:	66 0f 6f 05 f8 27 00 00 	movdqa 0x27f8(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4138:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    413f:	66 0f 6f 05 09 28 00 00 	movdqa 0x2809(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    4147:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    414e:	e9 d4 fd ff ff       	jmp    3f27 <send_headers+0x177>
    4153:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4158:	89 da                	mov    %ebx,%edx
    415a:	48 89 c7             	mov    %rax,%rdi
    415d:	4c 89 ee             	mov    %r13,%rsi
    4160:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    4165:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    416a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    416d:	c1 e9 03             	shr    $0x3,%ecx
    4170:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4173:	e9 ec fe ff ff       	jmp    4064 <send_headers+0x2b4>
    4178:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4180:	48 8d 1d 48 1f 00 00 	lea    0x1f48(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    4187:	e9 9b fd ff ff       	jmp    3f27 <send_headers+0x177>
    418c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4190:	66 0f 6f 05 d8 27 00 00 	movdqa 0x27d8(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4198:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    419f:	66 0f 6f 05 d9 27 00 00 	movdqa 0x27d9(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    41a7:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    41ae:	e9 b9 fd ff ff       	jmp    3f6c <send_headers+0x1bc>
    41b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    41b8:	66 0f 6f 05 b0 27 00 00 	movdqa 0x27b0(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    41c0:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    41c7:	66 0f 6f 05 b1 27 00 00 	movdqa 0x27b1(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    41cf:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    41d6:	e9 7a fd ff ff       	jmp    3f55 <send_headers+0x1a5>
    41db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    41e0:	66 0f 6f 05 48 27 00 00 	movdqa 0x2748(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    41e8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    41ef:	66 0f 6f 05 69 27 00 00 	movdqa 0x2769(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    41f7:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    41fe:	e9 3b fd ff ff       	jmp    3f3e <send_headers+0x18e>
    4203:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4208:	66 0f 6f 05 60 27 00 00 	movdqa 0x2760(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4210:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4217:	66 0f 6f 05 a1 27 00 00 	movdqa 0x27a1(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    421f:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    4226:	e9 78 fd ff ff       	jmp    3fa3 <send_headers+0x1f3>
    422b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4230:	66 0f 6f 05 38 27 00 00 	movdqa 0x2738(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4238:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    423f:	66 0f 6f 05 69 27 00 00 	movdqa 0x2769(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    4247:	0f 11 85 d9 fb ff ff 	movups %xmm0,-0x427(%rbp)
    424e:	e9 39 fd ff ff       	jmp    3f8c <send_headers+0x1dc>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4253:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    4259:	89 db                	mov    %ebx,%ebx
    425b:	89 10                	mov    %edx,(%rax)
    425d:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    4262:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4266:	e9 8d fd ff ff       	jmp    3ff8 <send_headers+0x248>
    426b:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    4271:	89 db                	mov    %ebx,%ebx
    4273:	89 10                	mov    %edx,(%rax)
    4275:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    427a:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    427e:	e9 e1 fd ff ff       	jmp    4064 <send_headers+0x2b4>
    4283:	89 db                	mov    %ebx,%ebx
    4285:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    428b:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4290:	e9 63 fd ff ff       	jmp    3ff8 <send_headers+0x248>
    4295:	89 db                	mov    %ebx,%ebx
    4297:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    429d:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    42a2:	e9 bd fd ff ff       	jmp    4064 <send_headers+0x2b4>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    42a7:	48 8b 0d 72 4d 00 00 	mov    0x4d72(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    42ae:	ba 28 00 00 00       	mov    $0x28,%edx
    42b3:	be 01 00 00 00       	mov    $0x1,%esi
    42b8:	48 8d 3d 61 21 00 00 	lea    0x2161(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    42bf:	e8 1c e2 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    42c4:	bf 01 00 00 00       	mov    $0x1,%edi
    42c9:	e8 f2 e1 ff ff       	call   24c0 <exit@plt>
}
    42ce:	e8 5d e0 ff ff       	call   2330 <__stack_chk_fail@plt>
    42d3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    42de:	66 90                	xchg   %ax,%ax

00000000000042e0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    42e0:	f3 0f 1e fa          	endbr64
    42e4:	55                   	push   %rbp
    42e5:	48 89 e5             	mov    %rsp,%rbp
    42e8:	41 56                	push   %r14
    42ea:	41 55                	push   %r13
    42ec:	41 54                	push   %r12
    42ee:	53                   	push   %rbx
    42ef:	ff 15 f3 4c 00 00    	call   *0x4cf3(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    42f5:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    42f8:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    42fb:	48 89 f3             	mov    %rsi,%rbx
    42fe:	49 89 d6             	mov    %rdx,%r14
    void *buf = malloc(size);
    4301:	e8 1a e1 ff ff       	call   2420 <malloc@plt>
    4306:	49 89 c4             	mov    %rax,%r12
    if (!buf) {
    4309:	48 85 c0             	test   %rax,%rax
    430c:	74 69                	je     4377 <copy_file_contents+0x97>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    430e:	4c 89 ef             	mov    %r13,%rdi
    4311:	31 f6                	xor    %esi,%esi
    4313:	31 c0                	xor    %eax,%eax
    4315:	e8 76 e1 ff ff       	call   2490 <open@plt>
    431a:	41 89 c5             	mov    %eax,%r13d
    if (fd < 0)
    431d:	85 c0                	test   %eax,%eax
    431f:	0f 88 58 e2 ff ff    	js     257d <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4325:	48 89 da             	mov    %rbx,%rdx
    4328:	4c 89 e6             	mov    %r12,%rsi
    432b:	89 c7                	mov    %eax,%edi
    432d:	e8 5e e0 ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    4332:	48 98                	cltq
    4334:	48 39 d8             	cmp    %rbx,%rax
    4337:	7c 1f                	jl     4358 <copy_file_contents+0x78>
    close(fd);
    4339:	44 89 ef             	mov    %r13d,%edi
    433c:	e8 2f e0 ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    4341:	4d 89 26             	mov    %r12,(%r14)
    iov->iov_len = file_size;
    4344:	49 89 5e 08          	mov    %rbx,0x8(%r14)
}
    4348:	5b                   	pop    %rbx
    4349:	41 5c                	pop    %r12
    434b:	41 5d                	pop    %r13
    434d:	41 5e                	pop    %r14
    434f:	5d                   	pop    %rbp
    4350:	c3                   	ret
    4351:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4358:	48 8b 0d c1 4c 00 00 	mov    0x4cc1(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    435f:	ba 1a 00 00 00       	mov    $0x1a,%edx
    4364:	be 01 00 00 00       	mov    $0x1,%esi
    4369:	48 8d 3d 60 1d 00 00 	lea    0x1d60(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    4370:	e8 6b e1 ff ff       	call   24e0 <fwrite@plt>
    4375:	eb c2                	jmp    4339 <copy_file_contents+0x59>
    4377:	48 8b 0d a2 4c 00 00 	mov    0x4ca2(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    437e:	ba 28 00 00 00       	mov    $0x28,%edx
    4383:	be 01 00 00 00       	mov    $0x1,%esi
    4388:	48 8d 3d 91 20 00 00 	lea    0x2091(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    438f:	e8 4c e1 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    4394:	bf 01 00 00 00       	mov    $0x1,%edi
    4399:	e8 22 e1 ff ff       	call   24c0 <exit@plt>
    439e:	66 90                	xchg   %ax,%ax

00000000000043a0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    43a0:	f3 0f 1e fa          	endbr64
    43a4:	55                   	push   %rbp
    43a5:	48 89 e5             	mov    %rsp,%rbp
    43a8:	ff 15 3a 4c 00 00    	call   *0x4c3a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    43ae:	8b 46 44             	mov    0x44(%rsi),%eax
    43b1:	48 89 fa             	mov    %rdi,%rdx
    43b4:	48 89 f7             	mov    %rsi,%rdi
    43b7:	8d 70 01             	lea    0x1(%rax),%esi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    43ba:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    43c0:	48 8b 07             	mov    (%rdi),%rax
    43c3:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    43c6:	f6 c1 02             	test   $0x2,%cl
    43c9:	74 00                	je     43cb <add_write_request+0x2b>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    43cb:	89 f0                	mov    %esi,%eax
    43cd:	44 29 c0             	sub    %r8d,%eax
    43d0:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    43d3:	0f 82 b0 e1 ff ff    	jb     2589 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    43d9:	c1 e9 0a             	shr    $0xa,%ecx
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    43dc:	8b 47 44             	mov    0x44(%rdi),%eax
    43df:	23 47 58             	and    0x58(%rdi),%eax
		sq->sqe_tail = next;
    43e2:	89 77 44             	mov    %esi,0x44(%rdi)
	if (ring->flags & IORING_SETUP_SQE128)
    43e5:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    43e8:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    43eb:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    43ef:	d3 e0                	shl    %cl,%eax
    43f1:	8b 4a 04             	mov    0x4(%rdx),%ecx
    43f4:	48 c1 e0 06          	shl    $0x6,%rax
    43f8:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    43fc:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    4402:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4405:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4409:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    440f:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4417:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    441b:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    441e:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4425:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    442d:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    4431:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    4435:	e8 06 df ff ff       	call   2340 <io_uring_submit@plt>
}
    443a:	31 c0                	xor    %eax,%eax
    443c:	5d                   	pop    %rbp
    443d:	c3                   	ret
    443e:	66 90                	xchg   %ax,%ax

0000000000004440 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4440:	f3 0f 1e fa          	endbr64
    4444:	55                   	push   %rbp
    4445:	48 89 e5             	mov    %rsp,%rbp
    4448:	41 56                	push   %r14
    444a:	41 55                	push   %r13
    444c:	41 54                	push   %r12
    444e:	53                   	push   %rbx
    444f:	ff 15 93 4b 00 00    	call   *0x4b93(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    4455:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4458:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    445e:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4461:	83 c0 01             	add    $0x1,%eax
    4464:	48 89 f3             	mov    %rsi,%rbx
    4467:	41 89 fe             	mov    %edi,%r14d
		head = IO_URING_READ_ONCE(*sq->khead);
    446a:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    446c:	f6 c1 02             	test   $0x2,%cl
    446f:	74 00                	je     4471 <add_read_request+0x31>
	if (next - head <= sq->ring_entries) {
    4471:	89 c2                	mov    %eax,%edx
    4473:	29 f2                	sub    %esi,%edx
    4475:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4478:	0f 82 1b e1 ff ff    	jb     2599 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    447e:	44 8b 63 44          	mov    0x44(%rbx),%r12d
	if (ring->flags & IORING_SETUP_SQE128)
    4482:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    4485:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4488:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    448d:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4490:	44 23 63 58          	and    0x58(%rbx),%r12d
    4494:	41 d3 e4             	shl    %cl,%r12d
    4497:	49 c1 e4 06          	shl    $0x6,%r12
    449b:	4c 03 63 38          	add    0x38(%rbx),%r12
    449f:	e8 7c df ff ff       	call   2420 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    44a4:	be 01 00 00 00       	mov    $0x1,%esi
    44a9:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    44ae:	49 89 c5             	mov    %rax,%r13
    req->iov[0].iov_base = malloc(READ_SZ);
    44b1:	e8 ea de ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    44b6:	45 89 75 08          	mov    %r14d,0x8(%r13)
	sqe->addr3 = 0;
    44ba:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    44be:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    44c1:	49 89 45 10          	mov    %rax,0x10(%r13)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    44c5:	49 8d 45 10          	lea    0x10(%r13),%rax
    req->iov[0].iov_len = READ_SZ;
    44c9:	49 c7 45 18 00 20 00 00 	movq   $0x2000,0x18(%r13)
    req->event_type = EVENT_TYPE_READ;
    44d1:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
	sqe->fd = fd;
    44d9:	45 89 74 24 04       	mov    %r14d,0x4(%r12)
	sqe->user_data = (unsigned long) data;
    44de:	4d 89 6c 24 20       	mov    %r13,0x20(%r12)
	sqe->opcode = (__u8) op;
    44e3:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->off = offset;
    44eb:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    44f4:	49 89 44 24 10       	mov    %rax,0x10(%r12)
	sqe->len = len;
    44f9:	49 c7 44 24 18 01 00 00 00 	movq   $0x1,0x18(%r12)
	sqe->buf_index = 0;
    4502:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->addr3 = 0;
    450b:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    io_uring_submit(ring);
    4511:	e8 2a de ff ff       	call   2340 <io_uring_submit@plt>
}
    4516:	5b                   	pop    %rbx
    4517:	31 c0                	xor    %eax,%eax
    4519:	41 5c                	pop    %r12
    451b:	41 5d                	pop    %r13
    451d:	41 5e                	pop    %r14
    451f:	5d                   	pop    %rbp
    4520:	c3                   	ret
    4521:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    452c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004530 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4530:	f3 0f 1e fa          	endbr64
    4534:	55                   	push   %rbp
    4535:	48 89 e5             	mov    %rsp,%rbp
    4538:	41 57                	push   %r15
    453a:	41 56                	push   %r14
    453c:	41 55                	push   %r13
    453e:	41 54                	push   %r12
    4540:	53                   	push   %rbx
    4541:	48 83 ec 08          	sub    $0x8,%rsp
    4545:	ff 15 9d 4a 00 00    	call   *0x4a9d(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    454b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    454e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4553:	41 89 f7             	mov    %esi,%r15d
    4556:	49 89 d4             	mov    %rdx,%r12
    void *buf = malloc(size);
    4559:	e8 c2 de ff ff       	call   2420 <malloc@plt>
    455e:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4561:	48 85 c0             	test   %rax,%rax
    4564:	0f 84 eb 00 00 00    	je     4655 <_send_static_string_content+0x125>
    unsigned long slen = strlen(str);
    456a:	4c 89 ef             	mov    %r13,%rdi
    456d:	e8 ae dd ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4572:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    4579:	44 89 7b 08          	mov    %r15d,0x8(%rbx)
    void *buf = malloc(size);
    457d:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4580:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    4583:	e8 98 de ff ff       	call   2420 <malloc@plt>
    4588:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    458b:	48 85 c0             	test   %rax,%rax
    458e:	0f 84 c1 00 00 00    	je     4655 <_send_static_string_content+0x125>
    req->iov[0].iov_base = zh_malloc(slen);
    4594:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4598:	4c 89 f2             	mov    %r14,%rdx
    459b:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    459e:	4c 89 73 18          	mov    %r14,0x18(%rbx)
    45a2:	e8 49 de ff ff       	call   23f0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    45a7:	41 8b 44 24 44       	mov    0x44(%r12),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    45ac:	41 8b 8c 24 c0 00 00 00 	mov    0xc0(%r12),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    45b4:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    45b7:	49 8b 04 24          	mov    (%r12),%rax
    45bb:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    45bd:	f6 c1 02             	test   $0x2,%cl
    45c0:	0f 85 8a 00 00 00    	jne    4650 <_send_static_string_content+0x120>
	if (next - head <= sq->ring_entries) {
    45c6:	89 d0                	mov    %edx,%eax
    45c8:	29 f0                	sub    %esi,%eax
    45ca:	41 39 44 24 5c       	cmp    %eax,0x5c(%r12)
    45cf:	0f 82 ce df ff ff    	jb     25a3 <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    45d5:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    45d8:	41 8b 44 24 44       	mov    0x44(%r12),%eax
    45dd:	41 23 44 24 58       	and    0x58(%r12),%eax
    io_uring_submit(ring);
    45e2:	4c 89 e7             	mov    %r12,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    45e5:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    45e8:	41 89 54 24 44       	mov    %edx,0x44(%r12)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    45ed:	8b 53 04             	mov    0x4(%rbx),%edx
	sqe->addr3 = 0;
    45f0:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    45f4:	d3 e0                	shl    %cl,%eax
    45f6:	8b 4b 08             	mov    0x8(%rbx),%ecx
    req->event_type = EVENT_TYPE_WRITE;
    45f9:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    45ff:	48 c1 e0 06          	shl    $0x6,%rax
    4603:	49 03 44 24 38       	add    0x38(%r12),%rax
	sqe->fd = fd;
    4608:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    460b:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    460f:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4615:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    461d:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4621:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4624:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    462b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4633:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    4637:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    463b:	48 83 c4 08          	add    $0x8,%rsp
    463f:	5b                   	pop    %rbx
    4640:	41 5c                	pop    %r12
    4642:	41 5d                	pop    %r13
    4644:	41 5e                	pop    %r14
    4646:	41 5f                	pop    %r15
    4648:	5d                   	pop    %rbp
    io_uring_submit(ring);
    4649:	e9 f2 dc ff ff       	jmp    2340 <io_uring_submit@plt>
    464e:	66 90                	xchg   %ax,%ax
		head = io_uring_smp_load_acquire(sq->khead);
    4650:	e9 71 ff ff ff       	jmp    45c6 <_send_static_string_content+0x96>
    4655:	48 8b 0d c4 49 00 00 	mov    0x49c4(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    465c:	ba 28 00 00 00       	mov    $0x28,%edx
    4661:	be 01 00 00 00       	mov    $0x1,%esi
    4666:	48 8d 3d b3 1d 00 00 	lea    0x1db3(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    466d:	e8 6e de ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    4672:	bf 01 00 00 00       	mov    $0x1,%edi
    4677:	e8 44 de ff ff       	call   24c0 <exit@plt>
    467c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004680 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4680:	f3 0f 1e fa          	endbr64
    4684:	55                   	push   %rbp
    4685:	48 89 e5             	mov    %rsp,%rbp
    4688:	ff 15 5a 49 00 00    	call   *0x495a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
}
    468e:	5d                   	pop    %rbp
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    468f:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4692:	89 fe                	mov    %edi,%esi
    4694:	48 8b 3d 7d 49 00 00 	mov    0x497d(%rip),%rdi        # 9018 <unimplemented_content>
    469b:	e9 90 fe ff ff       	jmp    4530 <_send_static_string_content>

00000000000046a0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    46a0:	f3 0f 1e fa          	endbr64
    46a4:	55                   	push   %rbp
    46a5:	48 89 e5             	mov    %rsp,%rbp
    46a8:	ff 15 3a 49 00 00    	call   *0x493a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
}
    46ae:	5d                   	pop    %rbp
void handle_http_404(int client_socket, struct io_uring *ring) {
    46af:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    46b2:	89 fe                	mov    %edi,%esi
    46b4:	48 8b 3d 55 49 00 00 	mov    0x4955(%rip),%rdi        # 9010 <http_404_content>
    46bb:	e9 70 fe ff ff       	jmp    4530 <_send_static_string_content>

00000000000046c0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    46c0:	f3 0f 1e fa          	endbr64
    46c4:	55                   	push   %rbp
    46c5:	48 89 e5             	mov    %rsp,%rbp
    46c8:	41 57                	push   %r15
    46ca:	41 56                	push   %r14
    46cc:	41 55                	push   %r13
    46ce:	41 54                	push   %r12
    46d0:	53                   	push   %rbx
    46d1:	48 81 ec a8 04 00 00 	sub    $0x4a8,%rsp
    46d8:	ff 15 0a 49 00 00    	call   *0x490a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    46de:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    46e7:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    46eb:	31 c0                	xor    %eax,%eax
    46ed:	49 89 fc             	mov    %rdi,%r12
    46f0:	41 89 f5             	mov    %esi,%r13d
    46f3:	49 89 d6             	mov    %rdx,%r14
    if (path[strlen(path) - 1] == '/') {
    46f6:	e8 25 dc ff ff       	call   2320 <strlen@plt>
    46fb:	41 80 7c 04 ff 2f    	cmpb   $0x2f,-0x1(%r12,%rax,1)
    4701:	48 89 c3             	mov    %rax,%rbx
    4704:	0f 84 b6 00 00 00    	je     47c0 <handle_get_method+0x100>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    470a:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    470f:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4713:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4718:	4c 89 e6             	mov    %r12,%rsi
    471b:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4722:	66 89 85 c4 fb ff ff 	mov    %ax,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4729:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4730:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    473a:	e8 91 dc ff ff       	call   23d0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    473f:	48 8d b5 30 fb ff ff 	lea    -0x4d0(%rbp),%rsi
    4746:	4c 89 ff             	mov    %r15,%rdi
    4749:	e8 92 dc ff ff       	call   23e0 <stat@plt>
    474e:	83 f8 ff             	cmp    $0xffffffff,%eax
    4751:	0f 84 41 01 00 00    	je     4898 <handle_get_method+0x1d8>
        if (S_ISREG(path_stat.st_mode)) {
    4757:	8b 85 48 fb ff ff    	mov    -0x4b8(%rbp),%eax
    475d:	25 00 f0 00 00       	and    $0xf000,%eax
    4762:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4767:	0f 84 b3 00 00 00    	je     4820 <handle_get_method+0x160>
    _send_static_string_content(http_404_content, client_socket, ring);
    476d:	48 8b 3d 9c 48 00 00 	mov    0x489c(%rip),%rdi        # 9010 <http_404_content>
    4774:	4c 89 f2             	mov    %r14,%rdx
    4777:	44 89 ee             	mov    %r13d,%esi
    477a:	e8 b1 fd ff ff       	call   4530 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    477f:	4c 89 fa             	mov    %r15,%rdx
    4782:	bf 01 00 00 00       	mov    $0x1,%edi
    4787:	31 c0                	xor    %eax,%eax
    4789:	48 8d 35 90 19 00 00 	lea    0x1990(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    4790:	e8 cb dc ff ff       	call   2460 <__printf_chk@plt>
}
    4795:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    4799:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    47a2:	0f 85 20 01 00 00    	jne    48c8 <handle_get_method+0x208>
    47a8:	48 81 c4 a8 04 00 00 	add    $0x4a8,%rsp
    47af:	5b                   	pop    %rbx
    47b0:	41 5c                	pop    %r12
    47b2:	41 5d                	pop    %r13
    47b4:	41 5e                	pop    %r14
    47b6:	41 5f                	pop    %r15
    47b8:	5d                   	pop    %rbp
    47b9:	c3                   	ret
    47ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    47c0:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    47c5:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
    47cc:	4c 89 e6             	mov    %r12,%rsi
    47cf:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    47d4:	66 89 95 c4 fb ff ff 	mov    %dx,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    47db:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    47de:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
    47e5:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    47ef:	e8 dc db ff ff       	call   23d0 <__memcpy_chk@plt>
    47f4:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    47f9:	49 8d 7c 1f 06       	lea    0x6(%r15,%rbx,1),%rdi
    47fe:	ba 0b 00 00 00       	mov    $0xb,%edx
    4803:	48 29 d9             	sub    %rbx,%rcx
    4806:	48 8d 35 de 18 00 00 	lea    0x18de(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    480d:	e8 be db ff ff       	call   23d0 <__memcpy_chk@plt>
    4812:	e9 28 ff ff ff       	jmp    473f <handle_get_method+0x7f>
    4817:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4820:	bf 70 00 00 00       	mov    $0x70,%edi
    4825:	e8 f6 db ff ff       	call   2420 <malloc@plt>
    482a:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    482d:	48 85 c0             	test   %rax,%rax
    4830:	0f 84 97 00 00 00    	je     48cd <handle_get_method+0x20d>
            req->client_socket = client_socket;
    4836:	44 89 68 08          	mov    %r13d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    483a:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    4841:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4845:	4c 89 ff             	mov    %r15,%rdi
            req->iovec_count = 6;
    4848:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    484f:	e8 5c f5 ff ff       	call   3db0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4854:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    485b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    485f:	4c 89 ff             	mov    %r15,%rdi
    4862:	e8 79 fa ff ff       	call   42e0 <copy_file_contents>
    4867:	4c 89 fa             	mov    %r15,%rdx
    486a:	bf 01 00 00 00       	mov    $0x1,%edi
    486f:	31 c0                	xor    %eax,%eax
    4871:	48 8b 8d 60 fb ff ff 	mov    -0x4a0(%rbp),%rcx
    4878:	48 8d 35 8f 18 00 00 	lea    0x188f(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    487f:	e8 dc db ff ff       	call   2460 <__printf_chk@plt>
            add_write_request(req, ring);
    4884:	4c 89 f6             	mov    %r14,%rsi
    4887:	48 89 df             	mov    %rbx,%rdi
    488a:	e8 11 fb ff ff       	call   43a0 <add_write_request>
    488f:	e9 01 ff ff ff       	jmp    4795 <handle_get_method+0xd5>
    4894:	0f 1f 40 00          	nopl   0x0(%rax)
    4898:	4c 89 fa             	mov    %r15,%rdx
    489b:	4c 89 e1             	mov    %r12,%rcx
    489e:	48 8d 35 51 18 00 00 	lea    0x1851(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    48a5:	31 c0                	xor    %eax,%eax
    48a7:	bf 01 00 00 00       	mov    $0x1,%edi
    48ac:	e8 af db ff ff       	call   2460 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    48b1:	48 8b 3d 58 47 00 00 	mov    0x4758(%rip),%rdi        # 9010 <http_404_content>
    48b8:	4c 89 f2             	mov    %r14,%rdx
    48bb:	44 89 ee             	mov    %r13d,%esi
    48be:	e8 6d fc ff ff       	call   4530 <_send_static_string_content>
}
    48c3:	e9 cd fe ff ff       	jmp    4795 <handle_get_method+0xd5>
}
    48c8:	e8 63 da ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    48cd:	48 8b 0d 4c 47 00 00 	mov    0x474c(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    48d4:	ba 28 00 00 00       	mov    $0x28,%edx
    48d9:	be 01 00 00 00       	mov    $0x1,%esi
    48de:	48 8d 3d 3b 1b 00 00 	lea    0x1b3b(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    48e5:	e8 f6 db ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    48ea:	bf 01 00 00 00       	mov    $0x1,%edi
    48ef:	e8 cc db ff ff       	call   24c0 <exit@plt>
    48f4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    48ff:	90                   	nop

0000000000004900 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4900:	f3 0f 1e fa          	endbr64
    4904:	55                   	push   %rbp
    4905:	48 89 e5             	mov    %rsp,%rbp
    4908:	41 57                	push   %r15
    490a:	41 56                	push   %r14
    490c:	41 55                	push   %r13
    490e:	41 54                	push   %r12
    4910:	53                   	push   %rbx
    4911:	48 83 ec 28          	sub    $0x28,%rsp
    4915:	ff 15 cd 46 00 00    	call   *0x46cd(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    method = strtok_r(method_buffer, " ", &saveptr);
    491b:	4c 8d 35 63 17 00 00 	lea    0x1763(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4922:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    492b:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    492f:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4931:	4c 8d 7d c0          	lea    -0x40(%rbp),%r15
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4935:	41 89 f4             	mov    %esi,%r12d
    4938:	49 89 d5             	mov    %rdx,%r13
    method = strtok_r(method_buffer, " ", &saveptr);
    493b:	4c 89 f6             	mov    %r14,%rsi
    493e:	4c 89 fa             	mov    %r15,%rdx
    4941:	e8 3a da ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4946:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    4949:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    494c:	84 d2                	test   %dl,%dl
    494e:	88 55 bf             	mov    %dl,-0x41(%rbp)
    4951:	74 22                	je     4975 <handle_http_method+0x75>
        *str = (char)tolower(*str);
    4953:	e8 d8 db ff ff       	call   2530 <__ctype_tolower_loc@plt>
    4958:	48 0f be 55 bf       	movsbq -0x41(%rbp),%rdx
    495d:	48 89 d9             	mov    %rbx,%rcx
    4960:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    4963:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    4967:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    496a:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    496d:	48 0f be 11          	movsbq (%rcx),%rdx
    4971:	84 d2                	test   %dl,%dl
    4973:	75 eb                	jne    4960 <handle_http_method+0x60>
    path = strtok_r(NULL, " ", &saveptr);
    4975:	4c 89 fa             	mov    %r15,%rdx
    4978:	4c 89 f6             	mov    %r14,%rsi
    497b:	31 ff                	xor    %edi,%edi
    497d:	e8 fe d9 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4982:	48 8d 35 aa 17 00 00 	lea    0x17aa(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    4989:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    498c:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    498f:	e8 1c da ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4994:	4c 89 ea             	mov    %r13,%rdx
    4997:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    499a:	85 c0                	test   %eax,%eax
    499c:	75 2a                	jne    49c8 <handle_http_method+0xc8>
        handle_get_method(path, client_socket, ring);
    499e:	4c 89 f7             	mov    %r14,%rdi
    49a1:	e8 1a fd ff ff       	call   46c0 <handle_get_method>
}
    49a6:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    49aa:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    49b3:	75 21                	jne    49d6 <handle_http_method+0xd6>
    49b5:	48 83 c4 28          	add    $0x28,%rsp
    49b9:	5b                   	pop    %rbx
    49ba:	41 5c                	pop    %r12
    49bc:	41 5d                	pop    %r13
    49be:	41 5e                	pop    %r14
    49c0:	41 5f                	pop    %r15
    49c2:	5d                   	pop    %rbp
    49c3:	c3                   	ret
    49c4:	0f 1f 40 00          	nopl   0x0(%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    49c8:	48 8b 3d 49 46 00 00 	mov    0x4649(%rip),%rdi        # 9018 <unimplemented_content>
    49cf:	e8 5c fb ff ff       	call   4530 <_send_static_string_content>
}
    49d4:	eb d0                	jmp    49a6 <handle_http_method+0xa6>
    49d6:	e8 55 d9 ff ff       	call   2330 <__stack_chk_fail@plt>
    49db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000049e0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    49e0:	f3 0f 1e fa          	endbr64
    49e4:	55                   	push   %rbp
    49e5:	48 89 e5             	mov    %rsp,%rbp
    49e8:	ff 15 fa 45 00 00    	call   *0x45fa(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    for (int i = 0; i < dest_sz; i++) {
    49ee:	85 d2                	test   %edx,%edx
    49f0:	7e 36                	jle    4a28 <get_line+0x48>
    49f2:	48 63 d2             	movslq %edx,%rdx
    49f5:	48 83 c7 01          	add    $0x1,%rdi
    49f9:	48 01 f2             	add    %rsi,%rdx
    49fc:	eb 0f                	jmp    4a0d <get_line+0x2d>
    49fe:	66 90                	xchg   %ax,%ax
    4a00:	48 83 c6 01          	add    $0x1,%rsi
    4a04:	48 83 c7 01          	add    $0x1,%rdi
    4a08:	48 39 d6             	cmp    %rdx,%rsi
    4a0b:	74 1b                	je     4a28 <get_line+0x48>
        dest[i] = src[i];
    4a0d:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4a11:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4a13:	3c 0d                	cmp    $0xd,%al
    4a15:	75 e9                	jne    4a00 <get_line+0x20>
    4a17:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4a1a:	75 e4                	jne    4a00 <get_line+0x20>
            return 0;
    4a1c:	31 c0                	xor    %eax,%eax
            dest[i] = '\0';
    4a1e:	c6 06 00             	movb   $0x0,(%rsi)
}
    4a21:	5d                   	pop    %rbp
    4a22:	c3                   	ret
    4a23:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    return 1;
    4a28:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4a2d:	5d                   	pop    %rbp
    4a2e:	c3                   	ret
    4a2f:	90                   	nop

0000000000004a30 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4a30:	f3 0f 1e fa          	endbr64
    4a34:	55                   	push   %rbp
    4a35:	48 89 e5             	mov    %rsp,%rbp
    4a38:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    4a3f:	ff 15 a3 45 00 00    	call   *0x45a3(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    4a45:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4a49:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a52:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
    4a56:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4a58:	4c 8d 95 f0 fb ff ff 	lea    -0x410(%rbp),%r10
    4a5f:	4c 8d 4d f0          	lea    -0x10(%rbp),%r9
    4a63:	4c 89 d0             	mov    %r10,%rax
    4a66:	eb 15                	jmp    4a7d <handle_client_request+0x4d>
    4a68:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4a70:	48 83 c0 01          	add    $0x1,%rax
    4a74:	48 83 c1 01          	add    $0x1,%rcx
    4a78:	4c 39 c8             	cmp    %r9,%rax
    4a7b:	74 43                	je     4ac0 <handle_client_request+0x90>
        dest[i] = src[i];
    4a7d:	44 0f b6 01          	movzbl (%rcx),%r8d
    4a81:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4a84:	41 80 f8 0d          	cmp    $0xd,%r8b
    4a88:	75 e6                	jne    4a70 <handle_client_request+0x40>
    4a8a:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4a8e:	75 e0                	jne    4a70 <handle_client_request+0x40>
            dest[i] = '\0';
    4a90:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4a93:	8b 47 08             	mov    0x8(%rdi),%eax
    4a96:	48 89 f2             	mov    %rsi,%rdx
    4a99:	4c 89 d7             	mov    %r10,%rdi
    4a9c:	89 c6                	mov    %eax,%esi
    4a9e:	e8 5d fe ff ff       	call   4900 <handle_http_method>
}
    4aa3:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    4aa7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4ab0:	75 35                	jne    4ae7 <handle_client_request+0xb7>
    4ab2:	c9                   	leave
    4ab3:	31 c0                	xor    %eax,%eax
    4ab5:	c3                   	ret
    4ab6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4ac0:	48 8b 0d 59 45 00 00 	mov    0x4559(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4ac7:	ba 12 00 00 00       	mov    $0x12,%edx
    4acc:	be 01 00 00 00       	mov    $0x1,%esi
    4ad1:	48 8d 3d 5f 16 00 00 	lea    0x165f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    4ad8:	e8 03 da ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    4add:	bf 01 00 00 00       	mov    $0x1,%edi
    4ae2:	e8 d9 d9 ff ff       	call   24c0 <exit@plt>
}
    4ae7:	e8 44 d8 ff ff       	call   2330 <__stack_chk_fail@plt>
    4aec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004af0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4af0:	f3 0f 1e fa          	endbr64
    4af4:	55                   	push   %rbp
    4af5:	48 89 e5             	mov    %rsp,%rbp
    4af8:	41 54                	push   %r12
    4afa:	53                   	push   %rbx
    4afb:	ff 15 e7 44 00 00    	call   *0x44e7(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    4b01:	8b 41 44             	mov    0x44(%rcx),%eax
    4b04:	83 c0 01             	add    $0x1,%eax
    4b07:	48 89 cb             	mov    %rcx,%rbx
	if (ring->flags & IORING_SETUP_SQE128)
    4b0a:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    4b10:	4c 8b 03             	mov    (%rbx),%r8
    4b13:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4b16:	f6 c1 02             	test   $0x2,%cl
    4b19:	74 00                	je     4b1b <add_accept_request+0x2b>
	if (next - head <= sq->ring_entries) {
    4b1b:	41 89 c0             	mov    %eax,%r8d
    4b1e:	45 29 c8             	sub    %r9d,%r8d
    4b21:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4b25:	0f 82 88 da ff ff    	jb     25b3 <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4b2b:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4b2e:	44 8b 63 44          	mov    0x44(%rbx),%r12d
    4b32:	44 23 63 58          	and    0x58(%rbx),%r12d
		sq->sqe_tail = next;
    4b36:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4b39:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4b3c:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4b40:	41 d3 e4             	shl    %cl,%r12d
    4b43:	49 c1 e4 06          	shl    $0x6,%r12
    4b47:	4c 03 63 38          	add    0x38(%rbx),%r12
	sqe->fd = fd;
    4b4b:	41 89 7c 24 04       	mov    %edi,0x4(%r12)
  struct Request *req = malloc(sizeof(*req));
    4b50:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4b55:	41 c7 04 24 0d 00 00 00 	movl   $0xd,(%r12)
	sqe->off = offset;
    4b5d:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
	sqe->addr = (unsigned long) addr;
    4b62:	49 89 74 24 10       	mov    %rsi,0x10(%r12)
	sqe->buf_index = 0;
    4b67:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->len = len;
    4b70:	49 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%r12)
	sqe->addr3 = 0;
    4b79:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    4b7f:	e8 9c d8 ff ff       	call   2420 <malloc@plt>
  io_uring_submit(ring);
    4b84:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4b87:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4b8d:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
    4b92:	5b                   	pop    %rbx
    4b93:	41 5c                	pop    %r12
    4b95:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4b96:	e9 a5 d7 ff ff       	jmp    2340 <io_uring_submit@plt>
    4b9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004ba0 <io_thread>:
void* io_thread(void *arg) {
    4ba0:	f3 0f 1e fa          	endbr64
    4ba4:	55                   	push   %rbp
    4ba5:	48 89 e5             	mov    %rsp,%rbp
    4ba8:	41 57                	push   %r15
    4baa:	41 56                	push   %r14
    4bac:	41 55                	push   %r13
    4bae:	41 54                	push   %r12
    4bb0:	53                   	push   %rbx
    4bb1:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4bb8:	ff 15 2a 44 00 00    	call   *0x442a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4bbe:	31 d2                	xor    %edx,%edx
  struct io_uring ring = *data->ring;
    4bc0:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4bc9:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    4bcd:	48 8b 47 40          	mov    0x40(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4bd1:	48 8d 9d e0 fa ff ff 	lea    -0x520(%rbp),%rbx
void* io_thread(void *arg) {
    4bd8:	49 89 fc             	mov    %rdi,%r12
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4bdb:	bf 00 01 00 00       	mov    $0x100,%edi
    4be0:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4be3:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4be7:	0f 29 8d e0 fa ff ff 	movaps %xmm1,-0x520(%rbp)
    4bee:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4bf3:	0f 29 95 f0 fa ff ff 	movaps %xmm2,-0x510(%rbp)
    4bfa:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4bff:	0f 29 9d 00 fb ff ff 	movaps %xmm3,-0x500(%rbp)
    4c06:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4c0b:	0f 29 a5 10 fb ff ff 	movaps %xmm4,-0x4f0(%rbp)
    4c12:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4c17:	0f 29 ad 20 fb ff ff 	movaps %xmm5,-0x4e0(%rbp)
    4c1e:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4c23:	0f 29 b5 30 fb ff ff 	movaps %xmm6,-0x4d0(%rbp)
    4c2a:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4c2f:	0f 29 bd 40 fb ff ff 	movaps %xmm7,-0x4c0(%rbp)
    4c36:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4c3b:	0f 29 8d 50 fb ff ff 	movaps %xmm1,-0x4b0(%rbp)
    4c42:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4c4a:	0f 29 95 60 fb ff ff 	movaps %xmm2,-0x4a0(%rbp)
    4c51:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4c59:	0f 29 9d 70 fb ff ff 	movaps %xmm3,-0x490(%rbp)
    4c60:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4c68:	0f 29 a5 80 fb ff ff 	movaps %xmm4,-0x480(%rbp)
    4c6f:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4c77:	0f 29 ad 90 fb ff ff 	movaps %xmm5,-0x470(%rbp)
    4c7e:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4c86:	0f 29 b5 a0 fb ff ff 	movaps %xmm6,-0x460(%rbp)
    4c8d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4c94:	48 89 85 b0 fb ff ff 	mov    %rax,-0x450(%rbp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4c9b:	e8 60 d7 ff ff       	call   2400 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4ca0:	49 8b 7c 24 40       	mov    0x40(%r12),%rdi
    4ca5:	31 f6                	xor    %esi,%esi
    4ca7:	e8 54 d8 ff ff       	call   2500 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4cac:	31 d2                	xor    %edx,%edx
    4cae:	be 01 00 00 00       	mov    $0x1,%esi
    4cb3:	bf 02 00 00 00       	mov    $0x2,%edi
    4cb8:	e8 93 d8 ff ff       	call   2550 <socket@plt>
    4cbd:	89 85 ac fa ff ff    	mov    %eax,-0x554(%rbp)
  if (sock == -1)
    4cc3:	83 f8 ff             	cmp    $0xffffffff,%eax
    4cc6:	0f 84 29 d9 ff ff    	je     25f5 <io_thread.cold+0x38>
    4ccc:	89 c7                	mov    %eax,%edi
  if (setsockopt(sock,
    4cce:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4cd4:	ba 02 00 00 00       	mov    $0x2,%edx
    4cd9:	be 01 00 00 00       	mov    $0x1,%esi
    4cde:	48 8d 8d b0 fa ff ff 	lea    -0x550(%rbp),%rcx
  int enable = 1;
    4ce5:	c7 85 b0 fa ff ff 01 00 00 00 	movl   $0x1,-0x550(%rbp)
  if (setsockopt(sock,
    4cef:	e8 0c d6 ff ff       	call   2300 <setsockopt@plt>
    4cf4:	85 c0                	test   %eax,%eax
    4cf6:	0f 88 cd d8 ff ff    	js     25c9 <io_thread.cold+0xc>
  if (bind(sock,
    4cfc:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4d02:	ba 10 00 00 00       	mov    $0x10,%edx
  return __builtin___memset_chk (__dest, __ch, __len,
    4d07:	48 8d b5 c0 fa ff ff 	lea    -0x540(%rbp),%rsi
    4d0e:	48 c7 85 c4 fa ff ff 00 00 00 00 	movq   $0x0,-0x53c(%rbp)
    4d19:	c7 85 cc fa ff ff 00 00 00 00 	movl   $0x0,-0x534(%rbp)
  srv_addr.sin_family = AF_INET;
    4d23:	c7 85 c0 fa ff ff 02 00 18 db 	movl   $0xdb180002,-0x540(%rbp)
  if (bind(sock,
    4d2d:	e8 3e d7 ff ff       	call   2470 <bind@plt>
    4d32:	85 c0                	test   %eax,%eax
    4d34:	0f 88 c7 d8 ff ff    	js     2601 <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4d3a:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4d40:	be 0a 00 00 00       	mov    $0xa,%esi
    4d45:	e8 e6 d6 ff ff       	call   2430 <listen@plt>
    4d4a:	85 c0                	test   %eax,%eax
    4d4c:	0f 88 83 d8 ff ff    	js     25d5 <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4d52:	ba db 18 00 00       	mov    $0x18db,%edx
    4d57:	48 8d 35 1e 14 00 00 	lea    0x141e(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4d5e:	bf 01 00 00 00       	mov    $0x1,%edi
    4d63:	31 c0                	xor    %eax,%eax
    4d65:	e8 f6 d6 ff ff       	call   2460 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4d6a:	48 8d 85 d0 fa ff ff 	lea    -0x530(%rbp),%rax
    4d71:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4d77:	48 89 d9             	mov    %rbx,%rcx
    4d7a:	48 8d 95 b4 fa ff ff 	lea    -0x54c(%rbp),%rdx
    4d81:	48 89 c6             	mov    %rax,%rsi
  socklen_t client_addr_len = sizeof(client_addr);
    4d84:	c7 85 b4 fa ff ff 10 00 00 00 	movl   $0x10,-0x54c(%rbp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4d8e:	48 89 95 88 fa ff ff 	mov    %rdx,-0x578(%rbp)
    4d95:	48 89 85 90 fa ff ff 	mov    %rax,-0x570(%rbp)
    4d9c:	e8 4f fd ff ff       	call   4af0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4da1:	bf 01 00 00 00       	mov    $0x1,%edi
    4da6:	be 10 00 00 00       	mov    $0x10,%esi
    4dab:	e8 f0 d5 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    4db0:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4db5:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    4db8:	e8 63 d6 ff ff       	call   2420 <malloc@plt>
    if (!buf) {
    4dbd:	48 85 c0             	test   %rax,%rax
    4dc0:	0f 84 cf 04 00 00    	je     5295 <io_thread+0x6f5>
  iov->iov_base = zh_malloc(10);
    4dc6:	49 89 06             	mov    %rax,(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    4dc9:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4dcf:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
  iov->iov_len = 10;
    4dd5:	49 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    4ddd:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4de0:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    4de7:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4de9:	f6 c1 02             	test   $0x2,%cl
    4dec:	0f 85 2e 04 00 00    	jne    5220 <io_thread+0x680>
	if (next - head <= sq->ring_entries) {
    4df2:	89 d0                	mov    %edx,%eax
    4df4:	29 f0                	sub    %esi,%eax
    4df6:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    4dfc:	0f 82 e9 d7 ff ff    	jb     25eb <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4e02:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e05:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    4e0b:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4e0f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e12:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e18:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4e1b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4e21:	49 8d 74 24 48       	lea    0x48(%r12),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4e26:	41 8b 54 24 48       	mov    0x48(%r12),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e2b:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4e2d:	48 89 b5 98 fa ff ff 	mov    %rsi,-0x568(%rbp)
    4e34:	48 c1 e0 06          	shl    $0x6,%rax
    4e38:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    4e3f:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4e45:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4e48:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4e50:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    4e54:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4e5c:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4e64:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4e68:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4e6c:	e8 cf d4 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4e71:	41 83 7c 24 2c 01    	cmpl   $0x1,0x2c(%r12)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4e77:	4c 8d 8d b8 fa ff ff 	lea    -0x548(%rbp),%r9
    4e7e:	4c 8d 95 c0 fb ff ff 	lea    -0x440(%rbp),%r10
    4e85:	0f 85 ed 01 00 00    	jne    5078 <io_thread+0x4d8>
    4e8b:	4c 89 8d a0 fa ff ff 	mov    %r9,-0x560(%rbp)
    4e92:	4c 89 95 80 fa ff ff 	mov    %r10,-0x580(%rbp)
    4e99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4ea0:	48 8d 3d eb 12 00 00 	lea    0x12eb(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4ea7:	e8 44 d4 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4eac:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4eb2:	8b bd 90 fb ff ff    	mov    -0x470(%rbp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4eb8:	c1 e9 0b             	shr    $0xb,%ecx
    4ebb:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4ebe:	48 8b 85 50 fb ff ff 	mov    -0x4b0(%rbp),%rax
    4ec5:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4ec7:	48 8b b5 48 fb ff ff 	mov    -0x4b8(%rbp),%rsi
    4ece:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4ed0:	39 d0                	cmp    %edx,%eax
    4ed2:	74 34                	je     4f08 <io_thread+0x368>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4ed4:	89 f8                	mov    %edi,%eax
    4ed6:	21 d0                	and    %edx,%eax
    4ed8:	d3 e0                	shl    %cl,%eax
    4eda:	48 c1 e0 04          	shl    $0x4,%rax
    4ede:	48 03 85 78 fb ff ff 	add    -0x488(%rbp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4ee5:	f6 85 a9 fb ff ff 01 	testb  $0x1,-0x457(%rbp)
    4eec:	0f 85 be 01 00 00    	jne    50b0 <io_thread+0x510>
    4ef2:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4ef6:	0f 85 2c 03 00 00    	jne    5228 <io_thread+0x688>
			if (cqe->res < 0)
    4efc:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4eff:	83 c2 01             	add    $0x1,%edx
    4f02:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4f04:	85 c0                	test   %eax,%eax
    4f06:	79 b6                	jns    4ebe <io_thread+0x31e>
	*cqe_ptr = cqe;
    4f08:	48 c7 85 b8 fa ff ff 00 00 00 00 	movq   $0x0,-0x548(%rbp)
	return err;
    4f13:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4f18:	48 8b b5 a0 fa ff ff 	mov    -0x560(%rbp),%rsi
    4f1f:	45 31 c0             	xor    %r8d,%r8d
    4f22:	31 d2                	xor    %edx,%edx
    4f24:	48 89 df             	mov    %rbx,%rdi
    4f27:	b9 01 00 00 00       	mov    $0x1,%ecx
    4f2c:	e8 1f d5 ff ff       	call   2450 <__io_uring_get_cqe@plt>
    4f31:	41 89 c5             	mov    %eax,%r13d
      if (cqe->user_data == 1) {
    4f34:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    4f3b:	48 83 38 01          	cmpq   $0x1,(%rax)
    4f3f:	0f 84 f3 02 00 00    	je     5238 <io_thread+0x698>
    4f45:	48 8d 3d 6c 12 00 00 	lea    0x126c(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4f4c:	e8 9f d3 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4f51:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    4f58:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    4f5b:	45 85 ed             	test   %r13d,%r13d
    4f5e:	0f 88 59 d6 ff ff    	js     25bd <io_thread.cold>
      if (cqe->res < 0) {
    4f64:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    4f67:	45 8b 07             	mov    (%r15),%r8d
      if (cqe->res < 0) {
    4f6a:	85 c0                	test   %eax,%eax
    4f6c:	0f 88 e5 02 00 00    	js     5257 <io_thread+0x6b7>
      switch (req->event_type) {
    4f72:	41 83 f8 01          	cmp    $0x1,%r8d
    4f76:	0f 84 84 01 00 00    	je     5100 <io_thread+0x560>
    4f7c:	41 83 f8 02          	cmp    $0x2,%r8d
    4f80:	0f 84 aa 01 00 00    	je     5130 <io_thread+0x590>
    4f86:	45 85 c0             	test   %r8d,%r8d
    4f89:	0f 85 59 01 00 00    	jne    50e8 <io_thread+0x548>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4f8f:	48 8b 95 88 fa ff ff 	mov    -0x578(%rbp),%rdx
    4f96:	48 8b b5 90 fa ff ff 	mov    -0x570(%rbp),%rsi
    4f9d:	48 89 d9             	mov    %rbx,%rcx
    4fa0:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    4fa6:	e8 45 fb ff ff       	call   4af0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    4fab:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    4fb2:	48 89 de             	mov    %rbx,%rsi
    4fb5:	8b 78 08             	mov    0x8(%rax),%edi
    4fb8:	e8 83 f4 ff ff       	call   4440 <add_read_request>
              free(req);
    4fbd:	4c 89 ff             	mov    %r15,%rdi
    4fc0:	e8 0b d3 ff ff       	call   22d0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4fc5:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
	if (cqe)
    4fcc:	48 85 c0             	test   %rax,%rax
    4fcf:	0f 85 13 01 00 00    	jne    50e8 <io_thread+0x548>
	unsigned int head, next = sq->sqe_tail + 1;
    4fd5:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4fdb:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4fe1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4fe4:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    4feb:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4fed:	f6 c1 02             	test   $0x2,%cl
    4ff0:	74 00                	je     4ff2 <io_thread+0x452>
	if (next - head <= sq->ring_entries) {
    4ff2:	89 d0                	mov    %edx,%eax
    4ff4:	29 f0                	sub    %esi,%eax
    4ff6:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    4ffc:	0f 82 df d5 ff ff    	jb     25e1 <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5002:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5005:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    500b:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    500f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5012:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5018:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    501b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5021:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5023:	41 8b 54 24 48       	mov    0x48(%r12),%edx
	sqe->user_data = (unsigned long) data;
    5028:	48 8b b5 98 fa ff ff 	mov    -0x568(%rbp),%rsi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    502f:	48 c1 e0 06          	shl    $0x6,%rax
    5033:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    503a:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5040:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5043:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    504b:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    504f:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5057:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    505f:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5063:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5067:	e8 d4 d2 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    506c:	41 83 7c 24 2c 01    	cmpl   $0x1,0x2c(%r12)
    5072:	0f 84 28 fe ff ff    	je     4ea0 <io_thread+0x300>
    5078:	48 8d 3d 72 11 00 00 	lea    0x1172(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    507f:	e8 6c d2 ff ff       	call   22f0 <puts@plt>
}
    5084:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    5088:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5091:	0f 85 25 02 00 00    	jne    52bc <io_thread+0x71c>
    5097:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    509e:	31 c0                	xor    %eax,%eax
    50a0:	5b                   	pop    %rbx
    50a1:	41 5c                	pop    %r12
    50a3:	41 5d                	pop    %r13
    50a5:	41 5e                	pop    %r14
    50a7:	41 5f                	pop    %r15
    50a9:	5d                   	pop    %rbp
    50aa:	c3                   	ret
    50ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    50b0:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    50b7:	48 85 c0             	test   %rax,%rax
    50ba:	0f 84 58 fe ff ff    	je     4f18 <io_thread+0x378>
      if (cqe->user_data == 1) {
    50c0:	48 83 38 01          	cmpq   $0x1,(%rax)
    50c4:	0f 84 6e 01 00 00    	je     5238 <io_thread+0x698>
    50ca:	48 8d 3d e7 10 00 00 	lea    0x10e7(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    50d1:	e8 1a d2 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    50d6:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    50dd:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    50e0:	e9 7f fe ff ff       	jmp    4f64 <io_thread+0x3c4>
    50e5:	0f 1f 00             	nopl   (%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    50e8:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
    50ef:	8b 02                	mov    (%rdx),%eax
    50f1:	83 c0 01             	add    $0x1,%eax
    50f4:	89 02                	mov    %eax,(%rdx)
}
    50f6:	e9 da fe ff ff       	jmp    4fd5 <io_thread+0x435>
    50fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              if (!cqe->res) {
    5100:	85 c0                	test   %eax,%eax
    5102:	75 7c                	jne    5180 <io_thread+0x5e0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5104:	48 8b 0d 15 3f 00 00 	mov    0x3f15(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    510b:	ba 0f 00 00 00       	mov    $0xf,%edx
    5110:	be 01 00 00 00       	mov    $0x1,%esi
    5115:	48 8d 3d c5 10 00 00 	lea    0x10c5(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    511c:	e8 bf d3 ff ff       	call   24e0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5121:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    5128:	e9 9f fe ff ff       	jmp    4fcc <io_thread+0x42c>
    512d:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    5130:	41 8b 47 04          	mov    0x4(%r15),%eax
    5134:	45 31 ed             	xor    %r13d,%r13d
    5137:	85 c0                	test   %eax,%eax
    5139:	7e 20                	jle    515b <io_thread+0x5bb>
    513b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  free(req->iov[i].iov_base);
    5140:	4c 89 e8             	mov    %r13,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5143:	49 83 c5 01          	add    $0x1,%r13
                  free(req->iov[i].iov_base);
    5147:	48 c1 e0 04          	shl    $0x4,%rax
    514b:	49 8b 7c 07 10       	mov    0x10(%r15,%rax,1),%rdi
    5150:	e8 7b d1 ff ff       	call   22d0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5155:	45 39 6f 04          	cmp    %r13d,0x4(%r15)
    5159:	7f e5                	jg     5140 <io_thread+0x5a0>
              close(req->client_socket);
    515b:	41 8b 7f 08          	mov    0x8(%r15),%edi
    515f:	e8 0c d2 ff ff       	call   2370 <close@plt>
              free(req);
    5164:	4c 89 ff             	mov    %r15,%rdi
    5167:	e8 64 d1 ff ff       	call   22d0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    516c:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    5173:	e9 54 fe ff ff       	jmp    4fcc <io_thread+0x42c>
    5178:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int i = 0; i < dest_sz; i++) {
    5180:	49 8b 57 10          	mov    0x10(%r15),%rdx
    5184:	48 8b 85 80 fa ff ff 	mov    -0x580(%rbp),%rax
    518b:	48 8d 75 c0          	lea    -0x40(%rbp),%rsi
    518f:	eb 14                	jmp    51a5 <io_thread+0x605>
    5191:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5198:	48 83 c0 01          	add    $0x1,%rax
    519c:	48 83 c2 01          	add    $0x1,%rdx
    51a0:	48 39 c6             	cmp    %rax,%rsi
    51a3:	74 4b                	je     51f0 <io_thread+0x650>
        dest[i] = src[i];
    51a5:	0f b6 0a             	movzbl (%rdx),%ecx
    51a8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    51aa:	80 f9 0d             	cmp    $0xd,%cl
    51ad:	75 e9                	jne    5198 <io_thread+0x5f8>
    51af:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    51b3:	75 e3                	jne    5198 <io_thread+0x5f8>
            dest[i] = '\0';
    51b5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    51b8:	48 8b bd 80 fa ff ff 	mov    -0x580(%rbp),%rdi
    51bf:	48 89 da             	mov    %rbx,%rdx
    51c2:	41 8b 77 08          	mov    0x8(%r15),%esi
    51c6:	e8 35 f7 ff ff       	call   4900 <handle_http_method>
              free(req->iov[0].iov_base);
    51cb:	49 8b 7f 10          	mov    0x10(%r15),%rdi
    51cf:	e8 fc d0 ff ff       	call   22d0 <free@plt>
              free(req);
    51d4:	4c 89 ff             	mov    %r15,%rdi
    51d7:	e8 f4 d0 ff ff       	call   22d0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    51dc:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    51e3:	e9 e4 fd ff ff       	jmp    4fcc <io_thread+0x42c>
    51e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    51f0:	48 8b 0d 29 3e 00 00 	mov    0x3e29(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    51f7:	ba 12 00 00 00       	mov    $0x12,%edx
    51fc:	be 01 00 00 00       	mov    $0x1,%esi
    5201:	48 8d 3d 2f 0f 00 00 	lea    0xf2f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    5208:	e8 d3 d2 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    520d:	bf 01 00 00 00       	mov    $0x1,%edi
    5212:	e8 a9 d2 ff ff       	call   24c0 <exit@plt>
    5217:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5220:	e9 cd fb ff ff       	jmp    4df2 <io_thread+0x252>
    5225:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5228:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	return err;
    522f:	e9 8c fe ff ff       	jmp    50c0 <io_thread+0x520>
    5234:	0f 1f 40 00          	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5238:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    523f:	48 8d 3d 5e 0f 00 00 	lea    0xf5e(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    5246:	8b 02                	mov    (%rdx),%eax
    5248:	83 c0 01             	add    $0x1,%eax
    524b:	89 02                	mov    %eax,(%rdx)
    524d:	e8 9e d0 ff ff       	call   22f0 <puts@plt>
    5252:	e9 21 fe ff ff       	jmp    5078 <io_thread+0x4d8>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5257:	f7 d8                	neg    %eax
    5259:	44 89 85 ac fa ff ff 	mov    %r8d,-0x554(%rbp)
    5260:	89 c7                	mov    %eax,%edi
    5262:	e8 b9 d2 ff ff       	call   2520 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5267:	48 8b 3d b2 3d 00 00 	mov    0x3db2(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    526e:	be 01 00 00 00       	mov    $0x1,%esi
    5273:	44 8b 85 ac fa ff ff 	mov    -0x554(%rbp),%r8d
    527a:	48 89 c1             	mov    %rax,%rcx
    527d:	48 8d 15 cc 11 00 00 	lea    0x11cc(%rip),%rdx        # 6450 <_IO_stdin_used+0x450>
    5284:	31 c0                	xor    %eax,%eax
    5286:	e8 65 d2 ff ff       	call   24f0 <__fprintf_chk@plt>
          exit(1);
    528b:	bf 01 00 00 00       	mov    $0x1,%edi
    5290:	e8 2b d2 ff ff       	call   24c0 <exit@plt>
    5295:	48 8b 0d 84 3d 00 00 	mov    0x3d84(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    529c:	ba 28 00 00 00       	mov    $0x28,%edx
    52a1:	be 01 00 00 00       	mov    $0x1,%esi
    52a6:	48 8d 3d 73 11 00 00 	lea    0x1173(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    52ad:	e8 2e d2 ff ff       	call   24e0 <fwrite@plt>
        exit(1);
    52b2:	bf 01 00 00 00       	mov    $0x1,%edi
    52b7:	e8 04 d2 ff ff       	call   24c0 <exit@plt>
}
    52bc:	e8 6f d0 ff ff       	call   2330 <__stack_chk_fail@plt>
    52c1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    52cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000052d0 <receive>:
int receive(struct BarrierTask *data) {
    52d0:	f3 0f 1e fa          	endbr64
    52d4:	55                   	push   %rbp
    52d5:	48 89 e5             	mov    %rsp,%rbp
    52d8:	41 55                	push   %r13
    52da:	41 54                	push   %r12
    52dc:	53                   	push   %rbx
    52dd:	48 83 ec 08          	sub    $0x8,%rsp
    52e1:	ff 15 01 3d 00 00    	call   *0x3d01(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  for (int n = 0 ; n < data->thread_count; n++) {
    52e7:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
int receive(struct BarrierTask *data) {
    52ed:	48 89 fa             	mov    %rdi,%rdx
  for (int n = 0 ; n < data->thread_count; n++) {
    52f0:	85 c0                	test   %eax,%eax
    52f2:	0f 8e e9 00 00 00    	jle    53e1 <receive+0x111>
    52f8:	48 8b b7 28 02 00 00 	mov    0x228(%rdi),%rsi
    52ff:	4c 63 e8             	movslq %eax,%r13
    5302:	49 c1 e5 05          	shl    $0x5,%r13
    5306:	49 01 f5             	add    %rsi,%r13
    5309:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    struct Data *me = data->mailboxes[n].lower;
    5310:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5313:	49 8b bc 24 80 00 00 00 	mov    0x80(%r12),%rdi
    531b:	48 85 ff             	test   %rdi,%rdi
    531e:	0f 8e a4 00 00 00    	jle    53c8 <receive+0xf8>
      data->sends++;
    5324:	48 8b 8a 30 02 00 00 	mov    0x230(%rdx),%rcx
    532b:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    532f:	4c 63 1a             	movslq (%rdx),%r11
    5332:	49 89 c9             	mov    %rcx,%r9
    5335:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5339:	49 f7 d9             	neg    %r9
    533c:	48 01 c7             	add    %rax,%rdi
    533f:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    5343:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    534a:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    534e:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    5351:	49 29 c8             	sub    %rcx,%r8
    5354:	eb 13                	jmp    5369 <receive+0x99>
    5356:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5360:	48 83 c0 01          	add    $0x1,%rax
    5364:	48 39 c7             	cmp    %rax,%rdi
    5367:	74 5f                	je     53c8 <receive+0xf8>
      data->n++;
    5369:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    536d:	48 89 82 30 02 00 00 	mov    %rax,0x230(%rdx)
      data->n++;
    5374:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    537b:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    537f:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5383:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5388:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    538c:	75 d2                	jne    5360 <receive+0x90>
    538e:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    5395:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5399:	75 c5                	jne    5360 <receive+0x90>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    539b:	bf 01 00 00 00       	mov    $0x1,%edi
    53a0:	b9 01 00 00 00       	mov    $0x1,%ecx
    53a5:	ba 01 00 00 00       	mov    $0x1,%edx
    53aa:	31 c0                	xor    %eax,%eax
    53ac:	48 8d 35 c5 10 00 00 	lea    0x10c5(%rip),%rsi        # 6478 <_IO_stdin_used+0x478>
    53b3:	e8 a8 d0 ff ff       	call   2460 <__printf_chk@plt>
        exit(1);
    53b8:	bf 01 00 00 00       	mov    $0x1,%edi
    53bd:	e8 fe d0 ff ff       	call   24c0 <exit@plt>
    53c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    53c8:	49 c7 84 24 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%r12)
  for (int n = 0 ; n < data->thread_count; n++) {
    53d4:	48 83 c6 20          	add    $0x20,%rsi
    53d8:	49 39 f5             	cmp    %rsi,%r13
    53db:	0f 85 2f ff ff ff    	jne    5310 <receive+0x40>
}
    53e1:	48 83 c4 08          	add    $0x8,%rsp
    53e5:	31 c0                	xor    %eax,%eax
    53e7:	5b                   	pop    %rbx
    53e8:	41 5c                	pop    %r12
    53ea:	41 5d                	pop    %r13
    53ec:	5d                   	pop    %rbp
    53ed:	c3                   	ret
    53ee:	66 90                	xchg   %ax,%ax

00000000000053f0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    53f0:	f3 0f 1e fa          	endbr64
    53f4:	55                   	push   %rbp
    53f5:	48 89 e5             	mov    %rsp,%rbp
    53f8:	41 57                	push   %r15
    53fa:	41 56                	push   %r14
    53fc:	41 55                	push   %r13
    53fe:	41 54                	push   %r12
    5400:	53                   	push   %rbx
    5401:	48 83 ec 38          	sub    $0x38,%rsp
    5405:	ff 15 dd 3b 00 00    	call   *0x3bdd(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  if (data->thread_index == data->task_index) {
    540b:	8b 07                	mov    (%rdi),%eax
int barriered_work(struct BarrierTask *data) {
    540d:	48 89 fb             	mov    %rdi,%rbx
  if (data->thread_index == data->task_index) {
    5410:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    5416:	0f 84 54 01 00 00    	je     5570 <barriered_work+0x180>
    receive(data);
    541c:	e8 af fe ff ff       	call   52d0 <receive>
    while (data->scheduled == 1) {
    5421:	eb 10                	jmp    5433 <barriered_work+0x43>
    5423:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->n++;
    5428:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    5430:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5433:	8b 83 00 02 00 00    	mov    0x200(%rbx),%eax
    5439:	83 f8 01             	cmp    $0x1,%eax
    543c:	74 ea                	je     5428 <barriered_work+0x38>
    if (data->sending == 1) {
    543e:	83 bb 38 02 00 00 01 	cmpl   $0x1,0x238(%rbx)
    5445:	74 14                	je     545b <barriered_work+0x6b>
  asm volatile ("mfence" ::: "memory");
    5447:	0f ae f0             	mfence
}
    544a:	48 83 c4 38          	add    $0x38,%rsp
    544e:	31 c0                	xor    %eax,%eax
    5450:	5b                   	pop    %rbx
    5451:	41 5c                	pop    %r12
    5453:	41 5d                	pop    %r13
    5455:	41 5e                	pop    %r14
    5457:	41 5f                	pop    %r15
    5459:	5d                   	pop    %rbp
    545a:	c3                   	ret
        for (int n = 0 ; n < data->thread_count; n++) {
    545b:	48 63 83 34 01 00 00 	movslq 0x134(%rbx),%rax
    5462:	85 c0                	test   %eax,%eax
    5464:	7e e1                	jle    5447 <barriered_work+0x57>
    5466:	48 89 45 c0          	mov    %rax,-0x40(%rbp)
          if (n == data->thread_index) { continue; }
    546a:	8b b3 30 01 00 00    	mov    0x130(%rbx),%esi
    5470:	48 8d 83 40 02 00 00 	lea    0x240(%rbx),%rax
    5477:	45 31 ff             	xor    %r15d,%r15d
    547a:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    547e:	48 8d 83 48 02 00 00 	lea    0x248(%rbx),%rax
    5485:	89 75 cc             	mov    %esi,-0x34(%rbp)
    5488:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
    548c:	0f 1f 40 00          	nopl   0x0(%rax)
    5490:	44 39 7d cc          	cmp    %r15d,-0x34(%rbp)
    5494:	0f 84 bc 00 00 00    	je     5556 <barriered_work+0x166>
          struct Data *them = data->mailboxes[n].higher;
    549a:	4c 89 ff             	mov    %r15,%rdi
    549d:	48 c1 e7 05          	shl    $0x5,%rdi
    54a1:	48 03 bb 28 02 00 00 	add    0x228(%rbx),%rdi
    54a8:	4c 8b 47 08          	mov    0x8(%rdi),%r8
          for (; them->messages_count < min;) {
    54ac:	4d 8b 90 80 00 00 00 	mov    0x80(%r8),%r10
    54b3:	49 63 b0 88 00 00 00 	movslq 0x88(%r8),%rsi
    54ba:	49 39 f2             	cmp    %rsi,%r10
    54bd:	0f 8d 93 00 00 00    	jge    5556 <barriered_work+0x166>
    54c3:	49 89 f1             	mov    %rsi,%r9
    54c6:	4c 8b b3 08 01 00 00 	mov    0x108(%rbx),%r14
    54cd:	4c 8b 5f 10          	mov    0x10(%rdi),%r11
    54d1:	4d 29 d1             	sub    %r10,%r9
            them->messages[them->messages_count++] = data->message; 
    54d4:	49 8b 10             	mov    (%r8),%rdx
    54d7:	49 8d 41 ff          	lea    -0x1(%r9),%rax
    54db:	48 83 f8 02          	cmp    $0x2,%rax
    54df:	0f 86 83 02 00 00    	jbe    5768 <barriered_work+0x378>
    54e5:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    54ed:	48 8d 0c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rcx
    54f5:	4c 8d 24 02          	lea    (%rdx,%rax,1),%r12
    54f9:	4c 8d 2c 0a          	lea    (%rdx,%rcx,1),%r13
    54fd:	4c 39 6d b8          	cmp    %r13,-0x48(%rbp)
    5501:	0f 83 f1 01 00 00    	jae    56f8 <barriered_work+0x308>
    5507:	4c 8b 6d b0          	mov    -0x50(%rbp),%r13
    550b:	4d 39 ec             	cmp    %r13,%r12
    550e:	0f 83 e4 01 00 00    	jae    56f8 <barriered_work+0x308>
    5514:	4c 8d 14 02          	lea    (%rdx,%rax,1),%r10
    5518:	48 01 d1             	add    %rdx,%rcx
    551b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5520:	48 8b 83 40 02 00 00 	mov    0x240(%rbx),%rax
          for (; them->messages_count < min;) {
    5527:	49 83 c2 08          	add    $0x8,%r10
            them->messages[them->messages_count++] = data->message; 
    552b:	49 89 42 f8          	mov    %rax,-0x8(%r10)
          for (; them->messages_count < min;) {
    552f:	4c 39 d1             	cmp    %r10,%rcx
    5532:	75 ec                	jne    5520 <barriered_work+0x130>
    5534:	0f 1f 40 00          	nopl   0x0(%rax)
    5538:	4b 8d 0c 0e          	lea    (%r14,%r9,1),%rcx
    553c:	4d 01 cb             	add    %r9,%r11
    553f:	48 89 8b 08 01 00 00 	mov    %rcx,0x108(%rbx)
    5546:	4c 89 5f 10          	mov    %r11,0x10(%rdi)
    554a:	49 89 b0 80 00 00 00 	mov    %rsi,0x80(%r8)
    5551:	48 89 44 f2 f8       	mov    %rax,-0x8(%rdx,%rsi,8)
        for (int n = 0 ; n < data->thread_count; n++) {
    5556:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    555a:	49 83 c7 01          	add    $0x1,%r15
    555e:	49 39 c7             	cmp    %rax,%r15
    5561:	0f 85 29 ff ff ff    	jne    5490 <barriered_work+0xa0>
    5567:	e9 db fe ff ff       	jmp    5447 <barriered_work+0x57>
    556c:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    5570:	e8 5b fd ff ff       	call   52d0 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    5575:	8b 8b 34 01 00 00    	mov    0x134(%rbx),%ecx
        int t = data->task_index;
    557b:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    557d:	85 c9                	test   %ecx,%ecx
    557f:	0f 8e 8e 00 00 00    	jle    5613 <barriered_work+0x223>
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5585:	48 63 d0             	movslq %eax,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
    5588:	83 c0 01             	add    $0x1,%eax
    558b:	4c 63 d9             	movslq %ecx,%r11
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    558e:	4c 8d 24 92          	lea    (%rdx,%rdx,4),%r12
              int next_task = abs((t + 1) % (data->thread_count));
    5592:	99                   	cltd
    5593:	f7 f9                	idiv   %ecx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5595:	49 c1 e4 07          	shl    $0x7,%r12
              int next_task = abs((t + 1) % (data->thread_count));
    5599:	89 d0                	mov    %edx,%eax
    559b:	f7 d8                	neg    %eax
    559d:	0f 48 c2             	cmovs  %edx,%eax
    55a0:	49 c1 e3 05          	shl    $0x5,%r11
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    55a4:	31 ff                	xor    %edi,%edi
    55a6:	48 98                	cltq
    55a8:	4c 8d 0c 80          	lea    (%rax,%rax,4),%r9
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    55ac:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    55b3:	49 c1 e1 07          	shl    $0x7,%r9
    55b7:	4c 8b 68 10          	mov    0x10(%rax),%r13
    55bb:	49 83 c5 20          	add    $0x20,%r13
    55bf:	4d 89 ea             	mov    %r13,%r10
    55c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    55c8:	49 8b 02             	mov    (%r10),%rax
    55cb:	4c 89 ea             	mov    %r13,%rdx
    55ce:	4a 8b 84 20 28 02 00 00 	mov    0x228(%rax,%r12,1),%rax
    55d6:	4d 8d 04 03          	lea    (%r11,%rax,1),%r8
    55da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    55e0:	48 8b 0a             	mov    (%rdx),%rcx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    55e3:	48 8b 70 08          	mov    0x8(%rax),%rsi
          for (int b = 0; b < data->thread_count ; b++) {
    55e7:	48 83 c0 20          	add    $0x20,%rax
    55eb:	48 81 c2 98 00 00 00 	add    $0x98,%rdx
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    55f2:	4a 8b 8c 09 28 02 00 00 	mov    0x228(%rcx,%r9,1),%rcx
    55fa:	48 89 34 39          	mov    %rsi,(%rcx,%rdi,1)
          for (int b = 0; b < data->thread_count ; b++) {
    55fe:	4c 39 c0             	cmp    %r8,%rax
    5601:	75 dd                	jne    55e0 <barriered_work+0x1f0>
        for (int y = 0; y < data->thread_count ; y++) {
    5603:	48 83 c7 20          	add    $0x20,%rdi
    5607:	49 81 c2 98 00 00 00 	add    $0x98,%r10
    560e:	4c 39 df             	cmp    %r11,%rdi
    5611:	75 b5                	jne    55c8 <barriered_work+0x1d8>
      asm volatile ("mfence" ::: "memory");
    5613:	0f ae f0             	mfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5616:	48 8b b3 18 02 00 00 	mov    0x218(%rbx),%rsi
    561d:	31 ff                	xor    %edi,%edi
    561f:	48 c1 e6 05          	shl    $0x5,%rsi
    5623:	48 03 b3 08 02 00 00 	add    0x208(%rbx),%rsi
    562a:	e8 e1 cc ff ff       	call   2310 <clock_gettime@plt>
    int modcount = data->thread->protected_state->modcount + 1;
    562f:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    5636:	48 8b 40 30          	mov    0x30(%rax),%rax
    563a:	8b 70 10             	mov    0x10(%rax),%esi
    563d:	44 8d 66 01          	lea    0x1(%rsi),%r12d
    data->thread->protected_state->modcount = modcount;
    5641:	44 89 60 10          	mov    %r12d,0x10(%rax)
    while (data->scheduled == 1) {
    5645:	eb 47                	jmp    568e <barriered_work+0x29e>
    5647:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    5650:	48 63 83 30 01 00 00 	movslq 0x130(%rbx),%rax
    5657:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
      data->n++;
    565e:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    5666:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    566a:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    566e:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    5672:	48 63 13             	movslq (%rbx),%rdx
    5675:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    5679:	48 8d 3c 92          	lea    (%rdx,%rdx,4),%rdi
    567d:	48 c1 e7 07          	shl    $0x7,%rdi
    5681:	48 03 78 20          	add    0x20(%rax),%rdi
    5685:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    568b:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    568e:	8b 83 00 02 00 00    	mov    0x200(%rbx),%eax
    5694:	83 f8 01             	cmp    $0x1,%eax
    5697:	74 b7                	je     5650 <barriered_work+0x260>
    if (modcount != data->thread->protected_state->modcount) {
    5699:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    56a0:	48 8b 40 30          	mov    0x30(%rax),%rax
    56a4:	44 39 60 10          	cmp    %r12d,0x10(%rax)
    56a8:	75 3d                	jne    56e7 <barriered_work+0x2f7>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    56aa:	48 8b b3 18 02 00 00 	mov    0x218(%rbx),%rsi
    56b1:	31 ff                	xor    %edi,%edi
    56b3:	48 c1 e6 05          	shl    $0x5,%rsi
    56b7:	48 03 b3 08 02 00 00 	add    0x208(%rbx),%rsi
    56be:	48 83 c6 10          	add    $0x10,%rsi
    56c2:	e8 49 cc ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    56c7:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    56ce:	48 83 c0 01          	add    $0x1,%rax
    56d2:	48 99                	cqto
    56d4:	48 f7 bb 10 02 00 00 	idivq  0x210(%rbx)
    56db:	48 89 93 18 02 00 00 	mov    %rdx,0x218(%rbx)
    56e2:	e9 60 fd ff ff       	jmp    5447 <barriered_work+0x57>
    56e7:	48 8d 3d 16 0b 00 00 	lea    0xb16(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    56ee:	e8 fd cb ff ff       	call   22f0 <puts@plt>
    56f3:	eb b5                	jmp    56aa <barriered_work+0x2ba>
    56f5:	0f 1f 00             	nopl   (%rax)
    56f8:	48 8b 83 40 02 00 00 	mov    0x240(%rbx),%rax
    56ff:	4d 89 cd             	mov    %r9,%r13
    5702:	4c 89 e1             	mov    %r12,%rcx
    5705:	49 d1 ed             	shr    %r13
    5708:	49 c1 e5 04          	shl    $0x4,%r13
    570c:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5711:	4c 89 6d a8          	mov    %r13,-0x58(%rbp)
    5715:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5719:	4d 01 e5             	add    %r12,%r13
    571c:	f6 45 a8 10          	testb  $0x10,-0x58(%rbp)
    5720:	74 0e                	je     5730 <barriered_work+0x340>
            them->messages[them->messages_count++] = data->message; 
    5722:	48 83 c1 10          	add    $0x10,%rcx
    5726:	41 0f 11 04 24       	movups %xmm0,(%r12)
          for (; them->messages_count < min;) {
    572b:	49 39 cd             	cmp    %rcx,%r13
    572e:	74 10                	je     5740 <barriered_work+0x350>
            them->messages[them->messages_count++] = data->message; 
    5730:	0f 11 01             	movups %xmm0,(%rcx)
    5733:	48 83 c1 20          	add    $0x20,%rcx
    5737:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
          for (; them->messages_count < min;) {
    573b:	49 39 cd             	cmp    %rcx,%r13
    573e:	75 f0                	jne    5730 <barriered_work+0x340>
    5740:	4c 89 c9             	mov    %r9,%rcx
    5743:	48 83 e1 fe          	and    $0xfffffffffffffffe,%rcx
    5747:	4c 01 d1             	add    %r10,%rcx
    574a:	41 f6 c1 01          	test   $0x1,%r9b
    574e:	0f 84 e4 fd ff ff    	je     5538 <barriered_work+0x148>
            them->messages[them->messages_count++] = data->message; 
    5754:	48 8b 83 40 02 00 00 	mov    0x240(%rbx),%rax
    575b:	48 89 04 ca          	mov    %rax,(%rdx,%rcx,8)
          for (; them->messages_count < min;) {
    575f:	e9 d4 fd ff ff       	jmp    5538 <barriered_work+0x148>
    5764:	0f 1f 40 00          	nopl   0x0(%rax)
    5768:	4a 8d 04 d5 00 00 00 00 	lea    0x0(,%r10,8),%rax
    5770:	48 8d 0c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rcx
    5778:	e9 97 fd ff ff       	jmp    5514 <barriered_work+0x124>
    577d:	0f 1f 00             	nopl   (%rax)

0000000000005780 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5780:	f3 0f 1e fa          	endbr64
    5784:	55                   	push   %rbp
    5785:	48 89 e5             	mov    %rsp,%rbp
    5788:	ff 15 5a 38 00 00    	call   *0x385a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    578e:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5795:	48 8b 40 38          	mov    0x38(%rax),%rax
    5799:	48 63 10             	movslq (%rax),%rdx
    579c:	85 d2                	test   %edx,%edx
    579e:	7e 2e                	jle    57ce <barriered_work_ingest+0x4e>
    57a0:	48 8b 40 08          	mov    0x8(%rax),%rax
    57a4:	48 c1 e2 04          	shl    $0x4,%rdx
    57a8:	48 01 c2             	add    %rax,%rdx
    57ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread->buffers->buffer[x].available == 1) {
    57b0:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    57b4:	75 0f                	jne    57c5 <barriered_work_ingest+0x45>
      data->ingest_count++;
    57b6:	48 83 87 20 02 00 00 01 	addq   $0x1,0x220(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    57be:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    57c5:	48 83 c0 10          	add    $0x10,%rax
    57c9:	48 39 d0             	cmp    %rdx,%rax
    57cc:	75 e2                	jne    57b0 <barriered_work_ingest+0x30>
  asm volatile ("mfence" ::: "memory");
    57ce:	0f ae f0             	mfence
  barriered_work(data);
    57d1:	e8 1a fc ff ff       	call   53f0 <barriered_work>
}
    57d6:	31 c0                	xor    %eax,%eax
    57d8:	5d                   	pop    %rbp
    57d9:	c3                   	ret
    57da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000057e0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    57e0:	f3 0f 1e fa          	endbr64
    57e4:	55                   	push   %rbp
    57e5:	48 89 e5             	mov    %rsp,%rbp
    57e8:	ff 15 fa 37 00 00    	call   *0x37fa(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
}
    57ee:	31 c0                	xor    %eax,%eax
    57f0:	5d                   	pop    %rbp
    57f1:	c3                   	ret
    57f2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    57fd:	0f 1f 00             	nopl   (%rax)

0000000000005800 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5800:	f3 0f 1e fa          	endbr64
    5804:	55                   	push   %rbp
    5805:	48 89 e5             	mov    %rsp,%rbp
    5808:	ff 15 da 37 00 00    	call   *0x37da(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    580e:	31 c0                	xor    %eax,%eax
    5810:	5d                   	pop    %rbp
    5811:	c3                   	ret
    5812:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    581d:	0f 1f 00             	nopl   (%rax)

0000000000005820 <after>:
int after(struct timespec left, struct timespec right) {
    5820:	f3 0f 1e fa          	endbr64
    5824:	55                   	push   %rbp
    5825:	48 89 e5             	mov    %rsp,%rbp
    5828:	ff 15 ba 37 00 00    	call   *0x37ba(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  return left.tv_sec > right.tv_sec &&
    582e:	31 c0                	xor    %eax,%eax
    5830:	48 39 d7             	cmp    %rdx,%rdi
    5833:	7e 08                	jle    583d <after+0x1d>
    5835:	31 c0                	xor    %eax,%eax
    5837:	48 39 ce             	cmp    %rcx,%rsi
    583a:	0f 9f c0             	setg   %al
}
    583d:	5d                   	pop    %rbp
    583e:	c3                   	ret
    583f:	90                   	nop

0000000000005840 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5840:	f3 0f 1e fa          	endbr64
    5844:	55                   	push   %rbp
    5845:	48 89 e5             	mov    %rsp,%rbp
    5848:	ff 15 9a 37 00 00    	call   *0x379a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
  return 0;
    584e:	31 c0                	xor    %eax,%eax
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5850:	4c 8b 5d 10          	mov    0x10(%rbp),%r11
    5854:	4c 8b 55 18          	mov    0x18(%rbp),%r10
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5858:	48 39 d7             	cmp    %rdx,%rdi
    585b:	7f 18                	jg     5875 <within+0x35>
    585d:	4d 39 d8             	cmp    %r11,%r8
    5860:	0f 9e c2             	setle  %dl
    5863:	48 39 ce             	cmp    %rcx,%rsi
    5866:	0f 9e c0             	setle  %al
    5869:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    586b:	31 c0                	xor    %eax,%eax
    586d:	4d 39 d1             	cmp    %r10,%r9
    5870:	0f 9e c0             	setle  %al
    5873:	21 d0                	and    %edx,%eax
}
    5875:	5d                   	pop    %rbp
    5876:	c3                   	ret
    5877:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005880 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5880:	f3 0f 1e fa          	endbr64
    5884:	55                   	push   %rbp
    5885:	48 89 e5             	mov    %rsp,%rbp
    5888:	ff 15 5a 37 00 00    	call   *0x375a(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    588e:	48 8b 7d 10          	mov    0x10(%rbp),%rdi
    5892:	48 8b 75 30          	mov    0x30(%rbp),%rsi
    5896:	4c 8b 4d 20          	mov    0x20(%rbp),%r9
    589a:	4c 8b 55 28          	mov    0x28(%rbp),%r10
    589e:	4c 8b 45 40          	mov    0x40(%rbp),%r8
    58a2:	4c 8b 5d 48          	mov    0x48(%rbp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    58a6:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
    58aa:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  return left.tv_sec > right.tv_sec &&
    58ae:	48 39 fe             	cmp    %rdi,%rsi
    58b1:	7d 2d                	jge    58e0 <overlap+0x60>
    58b3:	48 39 ca             	cmp    %rcx,%rdx
    58b6:	7d 60                	jge    5918 <overlap+0x98>
    58b8:	4d 39 da             	cmp    %r11,%r10
    58bb:	7d 0a                	jge    58c7 <overlap+0x47>
    return 1;
    58bd:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    58c2:	4d 39 c1             	cmp    %r8,%r9
    58c5:	7c 0f                	jl     58d6 <overlap+0x56>
  return 0;
    58c7:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    58c9:	4d 39 c1             	cmp    %r8,%r9
    58cc:	7f 08                	jg     58d6 <overlap+0x56>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    58ce:	31 c0                	xor    %eax,%eax
    58d0:	4d 39 da             	cmp    %r11,%r10
    58d3:	0f 9e c0             	setle  %al
}
    58d6:	5d                   	pop    %rbp
    58d7:	c3                   	ret
    58d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    58e0:	7e 56                	jle    5938 <overlap+0xb8>
    58e2:	48 39 ca             	cmp    %rcx,%rdx
    58e5:	7f 39                	jg     5920 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    58e7:	75 31                	jne    591a <overlap+0x9a>
    58e9:	4d 39 c1             	cmp    %r8,%r9
    58ec:	7c 2c                	jl     591a <overlap+0x9a>
    return 1;
    58ee:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    58f3:	4d 39 da             	cmp    %r11,%r10
    58f6:	7d de                	jge    58d6 <overlap+0x56>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    58f8:	48 39 ca             	cmp    %rcx,%rdx
}
    58fb:	5d                   	pop    %rbp
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    58fc:	0f 94 c2             	sete   %dl
    58ff:	48 39 fe             	cmp    %rdi,%rsi
    5902:	0f 94 c0             	sete   %al
    5905:	21 c2                	and    %eax,%edx
    5907:	31 c0                	xor    %eax,%eax
    5909:	4d 39 c1             	cmp    %r8,%r9
    590c:	0f 94 c0             	sete   %al
    590f:	21 d0                	and    %edx,%eax
}
    5911:	c3                   	ret
    5912:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5918:	74 ad                	je     58c7 <overlap+0x47>
  return 0;
    591a:	31 c0                	xor    %eax,%eax
}
    591c:	5d                   	pop    %rbp
    591d:	c3                   	ret
    591e:	66 90                	xchg   %ax,%ax
  return left.tv_sec > right.tv_sec &&
    5920:	4d 39 da             	cmp    %r11,%r10
    5923:	7e c4                	jle    58e9 <overlap+0x69>
    return 1;
    5925:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    592a:	4d 39 c1             	cmp    %r8,%r9
    592d:	7e ba                	jle    58e9 <overlap+0x69>
    592f:	eb a5                	jmp    58d6 <overlap+0x56>
    5931:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5938:	48 39 ca             	cmp    %rcx,%rdx
    593b:	7c 8a                	jl     58c7 <overlap+0x47>
    593d:	4d 39 c1             	cmp    %r8,%r9
    5940:	7d ac                	jge    58ee <overlap+0x6e>
    5942:	48 39 ca             	cmp    %rcx,%rdx
    5945:	74 87                	je     58ce <overlap+0x4e>
  return 0;
    5947:	31 c0                	xor    %eax,%eax
    5949:	eb d1                	jmp    591c <overlap+0x9c>
    594b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005950 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5950:	f3 0f 1e fa          	endbr64
    5954:	55                   	push   %rbp
    5955:	48 89 e5             	mov    %rsp,%rbp
    5958:	41 57                	push   %r15
    595a:	41 56                	push   %r14
    595c:	41 55                	push   %r13
    595e:	41 54                	push   %r12
    5960:	53                   	push   %rbx
    5961:	48 83 ec 58          	sub    $0x58,%rsp
    5965:	ff 15 7d 36 00 00    	call   *0x367d(%rip)        # 8fe8 <mcount@GLIBC_2.2.5>
    596b:	41 89 f4             	mov    %esi,%r12d
  for (int x = 0 ; x < thread_count; x++) {
    596e:	85 f6                	test   %esi,%esi
    5970:	0f 8e ef 02 00 00    	jle    5c65 <verify+0x315>
    5976:	48 8d 5f 20          	lea    0x20(%rdi),%rbx
    597a:	45 31 ff             	xor    %r15d,%r15d
    597d:	48 89 5d b8          	mov    %rbx,-0x48(%rbp)
    for (int z = 0 ; z < thread_count; z++) {
    5981:	48 89 5d c0          	mov    %rbx,-0x40(%rbp)
    5985:	45 31 ed             	xor    %r13d,%r13d
    5988:	45 89 e6             	mov    %r12d,%r14d
      if (z != x)  {
    598b:	45 39 ef             	cmp    %r13d,%r15d
    598e:	0f 84 37 02 00 00    	je     5bcb <verify+0x27b>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5994:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    5998:	8b 50 08             	mov    0x8(%rax),%edx
    599b:	85 d2                	test   %edx,%edx
    599d:	0f 8e 28 02 00 00    	jle    5bcb <verify+0x27b>
    59a3:	48 c7 45 c8 00 00 00 00 	movq   $0x0,-0x38(%rbp)
    59ab:	45 31 e4             	xor    %r12d,%r12d
    59ae:	48 89 5d 98          	mov    %rbx,-0x68(%rbp)
    59b2:	44 89 6d 94          	mov    %r13d,-0x6c(%rbp)
    59b6:	44 89 75 90          	mov    %r14d,-0x70(%rbp)
    59ba:	45 89 e6             	mov    %r12d,%r14d
    59bd:	44 89 fa             	mov    %r15d,%edx
    59c0:	48 8d 35 4d 08 00 00 	lea    0x84d(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    59c7:	bf 01 00 00 00       	mov    $0x1,%edi
    59cc:	31 c0                	xor    %eax,%eax
    59ce:	e8 8d ca ff ff       	call   2460 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    59d3:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    59d7:	8b 40 08             	mov    0x8(%rax),%eax
    59da:	85 c0                	test   %eax,%eax
    59dc:	0f 8e c3 01 00 00    	jle    5ba5 <verify+0x255>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    59e2:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    59e6:	44 89 75 8c          	mov    %r14d,-0x74(%rbp)
    59ea:	31 db                	xor    %ebx,%ebx
    59ec:	44 89 7d 88          	mov    %r15d,-0x78(%rbp)
    59f0:	48 8b 00             	mov    (%rax),%rax
    59f3:	49 89 c1             	mov    %rax,%r9
    59f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5a00:	4c 8b 65 c0          	mov    -0x40(%rbp),%r12
    5a04:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    5a08:	4c 8b 7d c8          	mov    -0x38(%rbp),%r15
    5a0c:	48 8d 35 16 08 00 00 	lea    0x816(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    5a13:	49 89 c6             	mov    %rax,%r14
    5a16:	bf 01 00 00 00       	mov    $0x1,%edi
    5a1b:	49 8b 04 24          	mov    (%r12),%rax
    5a1f:	49 c1 e6 07          	shl    $0x7,%r14
    5a23:	4b 8b 8c 39 18 02 00 00 	mov    0x218(%r9,%r15,1),%rcx
    5a2b:	4c 89 75 a8          	mov    %r14,-0x58(%rbp)
    5a2f:	4a 8b 94 30 18 02 00 00 	mov    0x218(%rax,%r14,1),%rdx
    5a37:	31 c0                	xor    %eax,%eax
    5a39:	e8 22 ca ff ff       	call   2460 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5a3e:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    5a42:	4c 8b 08             	mov    (%rax),%r9
    5a45:	4b 83 bc 39 18 02 00 00 00 	cmpq   $0x0,0x218(%r9,%r15,1)
    5a4e:	0f 8e 38 01 00 00    	jle    5b8c <verify+0x23c>
    5a54:	4d 03 34 24          	add    (%r12),%r14
    5a58:	48 89 5d a0          	mov    %rbx,-0x60(%rbp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5a5c:	ba 01 00 00 00       	mov    $0x1,%edx
    5a61:	4d 89 f5             	mov    %r14,%r13
    5a64:	4d 8b b5 18 02 00 00 	mov    0x218(%r13),%r14
    5a6b:	4d 85 f6             	test   %r14,%r14
    5a6e:	0f 8e 14 01 00 00    	jle    5b88 <verify+0x238>
    5a74:	0f 1f 40 00          	nopl   0x0(%rax)
    5a78:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5a7c:	49 89 d4             	mov    %rdx,%r12
    5a7f:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
    5a83:	31 db                	xor    %ebx,%ebx
    5a85:	49 c1 e4 05          	shl    $0x5,%r12
    5a89:	49 83 ec 20          	sub    $0x20,%r12
    5a8d:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
    5a91:	eb 32                	jmp    5ac5 <verify+0x175>
    5a93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5a98:	4c 39 c1             	cmp    %r8,%rcx
    5a9b:	0f 8d 4f 01 00 00    	jge    5bf0 <verify+0x2a0>
    5aa1:	4c 39 d7             	cmp    %r10,%rdi
    5aa4:	7e 05                	jle    5aab <verify+0x15b>
    5aa6:	49 39 c3             	cmp    %rax,%r11
    5aa9:	7c 75                	jl     5b20 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5aab:	4c 39 d7             	cmp    %r10,%rdi
    5aae:	0f 8d a3 01 00 00    	jge    5c57 <verify+0x307>
    5ab4:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5ab8:	48 83 c3 01          	add    $0x1,%rbx
    5abc:	49 39 de             	cmp    %rbx,%r14
    5abf:	0f 8e a2 00 00 00    	jle    5b67 <verify+0x217>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5ac5:	49 8b 8f 08 02 00 00 	mov    0x208(%r15),%rcx
    5acc:	48 89 d8             	mov    %rbx,%rax
    5acf:	48 c1 e0 05          	shl    $0x5,%rax
    5ad3:	49 03 85 08 02 00 00 	add    0x208(%r13),%rax
    5ada:	4c 01 e1             	add    %r12,%rcx
    5add:	48 8b 30             	mov    (%rax),%rsi
    5ae0:	48 8b 78 10          	mov    0x10(%rax),%rdi
    5ae4:	48 8b 11             	mov    (%rcx),%rdx
    5ae7:	4c 8b 41 08          	mov    0x8(%rcx),%r8
    5aeb:	4c 8b 51 10          	mov    0x10(%rcx),%r10
    5aef:	4c 8b 59 18          	mov    0x18(%rcx),%r11
    5af3:	48 8b 48 08          	mov    0x8(%rax),%rcx
    5af7:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    5afb:	48 39 d6             	cmp    %rdx,%rsi
    5afe:	7c 98                	jl     5a98 <verify+0x148>
    5b00:	0f 8e 3a 01 00 00    	jle    5c40 <verify+0x2f0>
    5b06:	4c 39 c1             	cmp    %r8,%rcx
    5b09:	0f 8f f1 00 00 00    	jg     5c00 <verify+0x2b0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5b0f:	75 a7                	jne    5ab8 <verify+0x168>
    5b11:	4c 39 d7             	cmp    %r10,%rdi
    5b14:	7f a2                	jg     5ab8 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5b16:	49 39 c3             	cmp    %rax,%r11
    5b19:	7c 9d                	jl     5ab8 <verify+0x168>
    5b1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5b20:	49 89 c1             	mov    %rax,%r9
    5b23:	48 89 f9             	mov    %rdi,%rcx
    5b26:	48 8d 35 73 09 00 00 	lea    0x973(%rip),%rsi        # 64a0 <_IO_stdin_used+0x4a0>
    5b2d:	31 c0                	xor    %eax,%eax
    5b2f:	bf 01 00 00 00       	mov    $0x1,%edi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5b34:	48 83 c3 01          	add    $0x1,%rbx
    5b38:	e8 23 c9 ff ff       	call   2460 <__printf_chk@plt>
    5b3d:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    5b41:	4c 8b 6d a8          	mov    -0x58(%rbp),%r13
    5b45:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5b48:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5b4c:	4d 8b b5 18 02 00 00 	mov    0x218(%r13),%r14
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5b53:	4c 8b 08             	mov    (%rax),%r9
    5b56:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    5b5a:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5b5e:	49 39 de             	cmp    %rbx,%r14
    5b61:	0f 8f 5e ff ff ff    	jg     5ac5 <verify+0x175>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5b67:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    5b6b:	49 3b 97 18 02 00 00 	cmp    0x218(%r15),%rdx
    5b72:	7d 14                	jge    5b88 <verify+0x238>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5b74:	4d 8b b5 18 02 00 00 	mov    0x218(%r13),%r14
    5b7b:	48 83 c2 01          	add    $0x1,%rdx
    5b7f:	4d 85 f6             	test   %r14,%r14
    5b82:	0f 8f f0 fe ff ff    	jg     5a78 <verify+0x128>
    5b88:	48 8b 5d a0          	mov    -0x60(%rbp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5b8c:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    5b90:	48 83 c3 01          	add    $0x1,%rbx
    5b94:	39 58 08             	cmp    %ebx,0x8(%rax)
    5b97:	0f 8f 63 fe ff ff    	jg     5a00 <verify+0xb0>
    5b9d:	44 8b 75 8c          	mov    -0x74(%rbp),%r14d
    5ba1:	44 8b 7d 88          	mov    -0x78(%rbp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5ba5:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    5ba9:	48 81 45 c8 80 02 00 00 	addq   $0x280,-0x38(%rbp)
    5bb1:	41 83 c6 01          	add    $0x1,%r14d
    5bb5:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    5bb9:	0f 8f fe fd ff ff    	jg     59bd <verify+0x6d>
    5bbf:	48 8b 5d 98          	mov    -0x68(%rbp),%rbx
    5bc3:	44 8b 6d 94          	mov    -0x6c(%rbp),%r13d
    5bc7:	44 8b 75 90          	mov    -0x70(%rbp),%r14d
    for (int z = 0 ; z < thread_count; z++) {
    5bcb:	41 8d 45 01          	lea    0x1(%r13),%eax
    5bcf:	48 81 45 c0 98 00 00 00 	addq   $0x98,-0x40(%rbp)
    5bd7:	41 39 c6             	cmp    %eax,%r14d
    5bda:	0f 84 96 00 00 00    	je     5c76 <verify+0x326>
    5be0:	41 89 c5             	mov    %eax,%r13d
    5be3:	e9 a3 fd ff ff       	jmp    598b <verify+0x3b>
    5be8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5bf0:	0f 85 c2 fe ff ff    	jne    5ab8 <verify+0x168>
    5bf6:	e9 b0 fe ff ff       	jmp    5aab <verify+0x15b>
    5bfb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5c00:	49 39 c3             	cmp    %rax,%r11
    5c03:	7e 09                	jle    5c0e <verify+0x2be>
    5c05:	4c 39 d7             	cmp    %r10,%rdi
    5c08:	0f 8c 12 ff ff ff    	jl     5b20 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5c0e:	4c 39 d7             	cmp    %r10,%rdi
    5c11:	0f 8f a1 fe ff ff    	jg     5ab8 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5c17:	49 39 c3             	cmp    %rax,%r11
    5c1a:	0f 8d 00 ff ff ff    	jge    5b20 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5c20:	48 39 d6             	cmp    %rdx,%rsi
    5c23:	0f 85 8f fe ff ff    	jne    5ab8 <verify+0x168>
    5c29:	4c 39 c1             	cmp    %r8,%rcx
    5c2c:	0f 85 86 fe ff ff    	jne    5ab8 <verify+0x168>
    5c32:	4c 39 d7             	cmp    %r10,%rdi
    5c35:	0f 84 e5 fe ff ff    	je     5b20 <verify+0x1d0>
    5c3b:	e9 78 fe ff ff       	jmp    5ab8 <verify+0x168>
    5c40:	4c 39 c1             	cmp    %r8,%rcx
    5c43:	0f 8c 62 fe ff ff    	jl     5aab <verify+0x15b>
    5c49:	4c 39 d7             	cmp    %r10,%rdi
    5c4c:	7e c9                	jle    5c17 <verify+0x2c7>
    5c4e:	4c 39 c1             	cmp    %r8,%rcx
    5c51:	0f 85 61 fe ff ff    	jne    5ab8 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5c57:	49 39 c3             	cmp    %rax,%r11
    5c5a:	0f 8f 58 fe ff ff    	jg     5ab8 <verify+0x168>
    5c60:	e9 bb fe ff ff       	jmp    5b20 <verify+0x1d0>
}
    5c65:	48 83 c4 58          	add    $0x58,%rsp
    5c69:	31 c0                	xor    %eax,%eax
    5c6b:	5b                   	pop    %rbx
    5c6c:	41 5c                	pop    %r12
    5c6e:	41 5d                	pop    %r13
    5c70:	41 5e                	pop    %r14
    5c72:	41 5f                	pop    %r15
    5c74:	5d                   	pop    %rbp
    5c75:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
    5c76:	48 81 45 b8 98 00 00 00 	addq   $0x98,-0x48(%rbp)
    5c7e:	45 89 f4             	mov    %r14d,%r12d
    5c81:	41 8d 57 01          	lea    0x1(%r15),%edx
    5c85:	45 39 ef             	cmp    %r13d,%r15d
    5c88:	74 db                	je     5c65 <verify+0x315>
    5c8a:	41 89 d7             	mov    %edx,%r15d
    5c8d:	e9 ef fc ff ff       	jmp    5981 <verify+0x31>
    5c92:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5c9c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005ca0 <atexit>:
    5ca0:	f3 0f 1e fa          	endbr64
    5ca4:	48 8b 15 5d 33 00 00 	mov    0x335d(%rip),%rdx        # 9008 <__dso_handle>
    5cab:	31 f6                	xor    %esi,%esi
    5cad:	e9 fe c7 ff ff       	jmp    24b0 <__cxa_atexit@plt>
    5cb2:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5cbc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005cc0 <__stack_chk_fail_local>:
    5cc0:	f3 0f 1e fa          	endbr64
    5cc4:	50                   	push   %rax
    5cc5:	58                   	pop    %rax
    5cc6:	48 83 ec 08          	sub    $0x8,%rsp
    5cca:	e8 61 c6 ff ff       	call   2330 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000005cd0 <_fini>:
    5cd0:	f3 0f 1e fa          	endbr64
    5cd4:	48 83 ec 08          	sub    $0x8,%rsp
    5cd8:	48 83 c4 08          	add    $0x8,%rsp
    5cdc:	c3                   	ret
