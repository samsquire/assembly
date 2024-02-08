
multibarrier-evented:     file format elf64-x86-64


Disassembly of section .init:

0000000000002000 <_init>:
    2000:	f3 0f 1e fa          	endbr64
    2004:	48 83 ec 08          	sub    $0x8,%rsp
    2008:	48 8b 05 d9 8f 00 00 	mov    0x8fd9(%rip),%rax        # afe8 <__gmon_start__@Base>
    200f:	48 85 c0             	test   %rax,%rax
    2012:	74 02                	je     2016 <_init+0x16>
    2014:	ff d0                	call   *%rax
    2016:	48 83 c4 08          	add    $0x8,%rsp
    201a:	c3                   	ret

Disassembly of section .plt:

0000000000002020 <.plt>:
    2020:	ff 35 4a 8e 00 00    	push   0x8e4a(%rip)        # ae70 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 4c 8e 00 00    	jmp    *0x8e4c(%rip)        # ae78 <_GLOBAL_OFFSET_TABLE_+0x10>
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
    22d0:	f3 0f 1e fa          	endbr64
    22d4:	68 2a 00 00 00       	push   $0x2a
    22d9:	e9 42 fd ff ff       	jmp    2020 <_init+0x20>
    22de:	66 90                	xchg   %ax,%ax

Disassembly of section .plt.got:

00000000000022e0 <__cxa_finalize@plt>:
    22e0:	f3 0f 1e fa          	endbr64
    22e4:	ff 25 0e 8d 00 00    	jmp    *0x8d0e(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    22ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

00000000000022f0 <free@plt>:
    22f0:	f3 0f 1e fa          	endbr64
    22f4:	ff 25 86 8b 00 00    	jmp    *0x8b86(%rip)        # ae80 <free@GLIBC_2.2.5>
    22fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002300 <putchar@plt>:
    2300:	f3 0f 1e fa          	endbr64
    2304:	ff 25 7e 8b 00 00    	jmp    *0x8b7e(%rip)        # ae88 <putchar@GLIBC_2.2.5>
    230a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002310 <pthread_setaffinity_np@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 76 8b 00 00    	jmp    *0x8b76(%rip)        # ae90 <pthread_setaffinity_np@GLIBC_2.34>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002320 <puts@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 6e 8b 00 00    	jmp    *0x8b6e(%rip)        # ae98 <puts@GLIBC_2.2.5>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <setsockopt@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 66 8b 00 00    	jmp    *0x8b66(%rip)        # aea0 <setsockopt@GLIBC_2.2.5>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <clock_gettime@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 5e 8b 00 00    	jmp    *0x8b5e(%rip)        # aea8 <clock_gettime@GLIBC_2.17>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <fclose@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 56 8b 00 00    	jmp    *0x8b56(%rip)        # aeb0 <fclose@GLIBC_2.2.5>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <strlen@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 4e 8b 00 00    	jmp    *0x8b4e(%rip)        # aeb8 <strlen@GLIBC_2.2.5>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <__stack_chk_fail@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 46 8b 00 00    	jmp    *0x8b46(%rip)        # aec0 <__stack_chk_fail@GLIBC_2.4>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <io_uring_submit@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 3e 8b 00 00    	jmp    *0x8b3e(%rip)        # aec8 <io_uring_submit@LIBURING_2.0>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <nanosleep@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 36 8b 00 00    	jmp    *0x8b36(%rip)        # aed0 <nanosleep@GLIBC_2.2.5>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <strrchr@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 2e 8b 00 00    	jmp    *0x8b2e(%rip)        # aed8 <strrchr@GLIBC_2.2.5>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <fputs@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 26 8b 00 00    	jmp    *0x8b26(%rip)        # aee0 <fputs@GLIBC_2.2.5>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <close@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 1e 8b 00 00    	jmp    *0x8b1e(%rip)        # aee8 <close@GLIBC_2.2.5>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <strtok_r@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 16 8b 00 00    	jmp    *0x8b16(%rip)        # aef0 <strtok_r@GLIBC_2.2.5>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <read@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 0e 8b 00 00    	jmp    *0x8b0e(%rip)        # aef8 <read@GLIBC_2.2.5>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <calloc@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 06 8b 00 00    	jmp    *0x8b06(%rip)        # af00 <calloc@GLIBC_2.2.5>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <strcmp@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 fe 8a 00 00    	jmp    *0x8afe(%rip)        # af08 <strcmp@GLIBC_2.2.5>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <__memcpy_chk@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 f6 8a 00 00    	jmp    *0x8af6(%rip)        # af10 <__memcpy_chk@GLIBC_2.3.4>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <stat@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 ee 8a 00 00    	jmp    *0x8aee(%rip)        # af18 <stat@GLIBC_2.33>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <memcpy@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 e6 8a 00 00    	jmp    *0x8ae6(%rip)        # af20 <memcpy@GLIBC_2.14>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <io_uring_queue_init@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 de 8a 00 00    	jmp    *0x8ade(%rip)        # af28 <io_uring_queue_init@LIBURING_2.0>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <eventfd_write@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 d6 8a 00 00    	jmp    *0x8ad6(%rip)        # af30 <eventfd_write@GLIBC_2.7>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <malloc@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 ce 8a 00 00    	jmp    *0x8ace(%rip)        # af38 <malloc@GLIBC_2.2.5>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <listen@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 c6 8a 00 00    	jmp    *0x8ac6(%rip)        # af40 <listen@GLIBC_2.2.5>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <__strcpy_chk@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 be 8a 00 00    	jmp    *0x8abe(%rip)        # af48 <__strcpy_chk@GLIBC_2.3.4>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <__io_uring_get_cqe@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 b6 8a 00 00    	jmp    *0x8ab6(%rip)        # af50 <__io_uring_get_cqe@LIBURING_2.0>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <__printf_chk@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 ae 8a 00 00    	jmp    *0x8aae(%rip)        # af58 <__printf_chk@GLIBC_2.3.4>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <bind@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 a6 8a 00 00    	jmp    *0x8aa6(%rip)        # af60 <bind@GLIBC_2.2.5>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <pthread_create@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 9e 8a 00 00    	jmp    *0x8a9e(%rip)        # af68 <pthread_create@GLIBC_2.34>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <open@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 96 8a 00 00    	jmp    *0x8a96(%rip)        # af70 <open@GLIBC_2.2.5>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <fopen@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 8e 8a 00 00    	jmp    *0x8a8e(%rip)        # af78 <fopen@GLIBC_2.2.5>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <perror@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 86 8a 00 00    	jmp    *0x8a86(%rip)        # af80 <perror@GLIBC_2.2.5>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <exit@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 7e 8a 00 00    	jmp    *0x8a7e(%rip)        # af88 <exit@GLIBC_2.2.5>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <eventfd@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 76 8a 00 00    	jmp    *0x8a76(%rip)        # af90 <eventfd@GLIBC_2.7>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <fwrite@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 6e 8a 00 00    	jmp    *0x8a6e(%rip)        # af98 <fwrite@GLIBC_2.2.5>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <__fprintf_chk@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 66 8a 00 00    	jmp    *0x8a66(%rip)        # afa0 <__fprintf_chk@GLIBC_2.3.4>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002540 <io_uring_register_eventfd@plt>:
    2540:	f3 0f 1e fa          	endbr64
    2544:	ff 25 5e 8a 00 00    	jmp    *0x8a5e(%rip)        # afa8 <io_uring_register_eventfd@LIBURING_2.0>
    254a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002550 <pthread_join@plt>:
    2550:	f3 0f 1e fa          	endbr64
    2554:	ff 25 56 8a 00 00    	jmp    *0x8a56(%rip)        # afb0 <pthread_join@GLIBC_2.34>
    255a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002560 <strerror@plt>:
    2560:	f3 0f 1e fa          	endbr64
    2564:	ff 25 4e 8a 00 00    	jmp    *0x8a4e(%rip)        # afb8 <strerror@GLIBC_2.2.5>
    256a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002570 <__ctype_tolower_loc@plt>:
    2570:	f3 0f 1e fa          	endbr64
    2574:	ff 25 46 8a 00 00    	jmp    *0x8a46(%rip)        # afc0 <__ctype_tolower_loc@GLIBC_2.3>
    257a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002580 <__sprintf_chk@plt>:
    2580:	f3 0f 1e fa          	endbr64
    2584:	ff 25 3e 8a 00 00    	jmp    *0x8a3e(%rip)        # afc8 <__sprintf_chk@GLIBC_2.3.4>
    258a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002590 <socket@plt>:
    2590:	f3 0f 1e fa          	endbr64
    2594:	ff 25 36 8a 00 00    	jmp    *0x8a36(%rip)        # afd0 <socket@GLIBC_2.2.5>
    259a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

00000000000025a0 <fatal_error>:
struct Snapshot {
  struct timespec start;
  struct timespec end;
};

void fatal_error(const char *syscall) {
    25a0:	f3 0f 1e fa          	endbr64
    25a4:	50                   	push   %rax
    25a5:	58                   	pop    %rax
    25a6:	50                   	push   %rax
    perror(syscall);
    25a7:	e8 44 ff ff ff       	call   24f0 <perror@plt>
    exit(1);
    25ac:	bf 01 00 00 00       	mov    $0x1,%edi
    25b1:	e8 4a ff ff ff       	call   2500 <exit@plt>

00000000000025b6 <copy_file_contents.cold>:
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");
    25b6:	48 8d 3d 63 5c 00 00 	lea    0x5c63(%rip),%rdi        # 8220 <_IO_stdin_used+0x220>
    25bd:	e8 de ff ff ff       	call   25a0 <fatal_error>

00000000000025c2 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    25c2:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
    25c8:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25d0:	0f 0b                	ud2

00000000000025d2 <add_read_request.cold>:
    25d2:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25da:	0f 0b                	ud2

00000000000025dc <_send_static_string_content.cold>:
    25dc:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    25e2:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25ea:	0f 0b                	ud2

00000000000025ec <add_accept_request.cold>:
    25ec:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25f4:	0f 0b                	ud2

00000000000025f6 <io_thread.cold>:
        break;
      }
      printf("Received wait finished\n");
      struct Request *req = (struct Request *) cqe->user_data;
      if (ret < 0)
          fatal_error("io_uring_wait_cqe");
    25f6:	48 8d 3d f3 5b 00 00 	lea    0x5bf3(%rip),%rdi        # 81f0 <_IO_stdin_used+0x1f0>
    25fd:	e8 9e ff ff ff       	call   25a0 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    2602:	48 8d 3d 6b 5b 00 00 	lea    0x5b6b(%rip),%rdi        # 8174 <_IO_stdin_used+0x174>
    2609:	e8 92 ff ff ff       	call   25a0 <fatal_error>
    fatal_error("listen()");
    260e:	48 8d 3d 7f 5b 00 00 	lea    0x5b7f(%rip),%rdi        # 8194 <_IO_stdin_used+0x194>
    2615:	e8 86 ff ff ff       	call   25a0 <fatal_error>
    261a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2622:	0f 0b                	ud2
    2624:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    262c:	0f 0b                	ud2
      fatal_error("socket()");
    262e:	48 8d 3d 36 5b 00 00 	lea    0x5b36(%rip),%rdi        # 816b <_IO_stdin_used+0x16b>
    2635:	e8 66 ff ff ff       	call   25a0 <fatal_error>
      fatal_error("bind()");
    263a:	48 8d 3d 4c 5b 00 00 	lea    0x5b4c(%rip),%rdi        # 818d <_IO_stdin_used+0x18d>
    2641:	e8 5a ff ff ff       	call   25a0 <fatal_error>
    2646:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000002650 <main>:
    }


  return 0;
}
int main() {
    2650:	f3 0f 1e fa          	endbr64
    2654:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2656:	48 8d 3d 03 60 00 00 	lea    0x6003(%rip),%rdi        # 8660 <_IO_stdin_used+0x660>
    265d:	41 56                	push   %r14
    265f:	41 55                	push   %r13
    2661:	41 54                	push   %r12
    2663:	55                   	push   %rbp
    2664:	53                   	push   %rbx
    2665:	48 81 ec d8 00 00 00 	sub    $0xd8,%rsp
    266c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2675:	48 89 84 24 c8 00 00 00 	mov    %rax,0xc8(%rsp)
    267d:	48 8d 05 dc 1b 00 00 	lea    0x1bdc(%rip),%rax        # 4260 <barriered_reset>
    2684:	66 48 0f 6e f0       	movq   %rax,%xmm6
    2689:	0f 16 35 d0 85 00 00 	movhps 0x85d0(%rip),%xmm6        # ac60 <__do_global_dtors_aux_fini_array_entry+0x8>
    2690:	0f 29 74 24 70       	movaps %xmm6,0x70(%rsp)
    2695:	e8 86 fc ff ff       	call   2320 <puts@plt>
    269a:	bf 0a 00 00 00       	mov    $0xa,%edi
    269f:	e8 5c fc ff ff       	call   2300 <putchar@plt>
    26a4:	ba 01 00 00 00       	mov    $0x1,%edx
    26a9:	48 8d 35 be 5b 00 00 	lea    0x5bbe(%rip),%rsi        # 826e <_IO_stdin_used+0x26e>
    26b0:	31 c0                	xor    %eax,%eax
    26b2:	bf 01 00 00 00       	mov    $0x1,%edi
    26b7:	e8 e4 fd ff ff       	call   24a0 <__printf_chk@plt>
    26bc:	ba 04 00 00 00       	mov    $0x4,%edx
    26c1:	48 8d 35 b6 5b 00 00 	lea    0x5bb6(%rip),%rsi        # 827e <_IO_stdin_used+0x27e>
    26c8:	31 c0                	xor    %eax,%eax
    26ca:	bf 01 00 00 00       	mov    $0x1,%edi
    26cf:	e8 cc fd ff ff       	call   24a0 <__printf_chk@plt>
    26d4:	ba 02 00 00 00       	mov    $0x2,%edx
    26d9:	48 8d 35 b3 5b 00 00 	lea    0x5bb3(%rip),%rsi        # 8293 <_IO_stdin_used+0x293>
    26e0:	31 c0                	xor    %eax,%eax
    26e2:	bf 01 00 00 00       	mov    $0x1,%edi
    26e7:	e8 b4 fd ff ff       	call   24a0 <__printf_chk@plt>
    26ec:	ba 02 00 00 00       	mov    $0x2,%edx
    26f1:	48 8d 35 ab 5b 00 00 	lea    0x5bab(%rip),%rsi        # 82a3 <_IO_stdin_used+0x2a3>
    26f8:	31 c0                	xor    %eax,%eax
    26fa:	bf 01 00 00 00       	mov    $0x1,%edi
    26ff:	e8 9c fd ff ff       	call   24a0 <__printf_chk@plt>
    2704:	48 8d 3d ae 5b 00 00 	lea    0x5bae(%rip),%rdi        # 82b9 <_IO_stdin_used+0x2b9>
    270b:	e8 10 fc ff ff       	call   2320 <puts@plt>
    2710:	ba 02 00 00 00       	mov    $0x2,%edx
    2715:	48 8d 35 b9 5b 00 00 	lea    0x5bb9(%rip),%rsi        # 82d5 <_IO_stdin_used+0x2d5>
    271c:	31 c0                	xor    %eax,%eax
    271e:	bf 01 00 00 00       	mov    $0x1,%edi
    2723:	e8 78 fd ff ff       	call   24a0 <__printf_chk@plt>
    2728:	ba 08 00 00 00       	mov    $0x8,%edx
    272d:	48 8d 35 bb 5b 00 00 	lea    0x5bbb(%rip),%rsi        # 82ef <_IO_stdin_used+0x2ef>
    2734:	31 c0                	xor    %eax,%eax
    2736:	bf 01 00 00 00       	mov    $0x1,%edi
    273b:	e8 60 fd ff ff       	call   24a0 <__printf_chk@plt>
    2740:	ba 01 00 00 00       	mov    $0x1,%edx
    2745:	48 8d 35 b7 5b 00 00 	lea    0x5bb7(%rip),%rsi        # 8303 <_IO_stdin_used+0x303>
    274c:	31 c0                	xor    %eax,%eax
    274e:	bf 01 00 00 00       	mov    $0x1,%edi
    2753:	e8 48 fd ff ff       	call   24a0 <__printf_chk@plt>
    2758:	ba 01 00 00 00       	mov    $0x1,%edx
    275d:	48 8d 35 b0 5b 00 00 	lea    0x5bb0(%rip),%rsi        # 8314 <_IO_stdin_used+0x314>
    2764:	31 c0                	xor    %eax,%eax
    2766:	bf 01 00 00 00       	mov    $0x1,%edi
    276b:	e8 30 fd ff ff       	call   24a0 <__printf_chk@plt>
    2770:	ba 02 00 00 00       	mov    $0x2,%edx
    2775:	48 8d 35 b0 5b 00 00 	lea    0x5bb0(%rip),%rsi        # 832c <_IO_stdin_used+0x32c>
    277c:	31 c0                	xor    %eax,%eax
    277e:	bf 01 00 00 00       	mov    $0x1,%edi
    2783:	e8 18 fd ff ff       	call   24a0 <__printf_chk@plt>
    2788:	ba 01 00 00 00       	mov    $0x1,%edx
    278d:	48 8d 35 34 5f 00 00 	lea    0x5f34(%rip),%rsi        # 86c8 <_IO_stdin_used+0x6c8>
    2794:	31 c0                	xor    %eax,%eax
    2796:	bf 01 00 00 00       	mov    $0x1,%edi
    279b:	e8 00 fd ff ff       	call   24a0 <__printf_chk@plt>
    27a0:	ba 01 00 00 00       	mov    $0x1,%edx
    27a5:	48 8d 35 4c 5f 00 00 	lea    0x5f4c(%rip),%rsi        # 86f8 <_IO_stdin_used+0x6f8>
    27ac:	31 c0                	xor    %eax,%eax
    27ae:	bf 01 00 00 00       	mov    $0x1,%edi
    27b3:	e8 e8 fc ff ff       	call   24a0 <__printf_chk@plt>
    27b8:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    27bd:	48 8d 35 84 5b 00 00 	lea    0x5b84(%rip),%rsi        # 8348 <_IO_stdin_used+0x348>
    27c4:	31 c0                	xor    %eax,%eax
    27c6:	bf 01 00 00 00       	mov    $0x1,%edi
    27cb:	e8 d0 fc ff ff       	call   24a0 <__printf_chk@plt>
    27d0:	ba 05 00 00 00       	mov    $0x5,%edx
    27d5:	48 8d 35 86 5b 00 00 	lea    0x5b86(%rip),%rsi        # 8362 <_IO_stdin_used+0x362>
    27dc:	31 c0                	xor    %eax,%eax
    27de:	bf 01 00 00 00       	mov    $0x1,%edi
    27e3:	e8 b8 fc ff ff       	call   24a0 <__printf_chk@plt>
    27e8:	48 8d 3d 00 59 00 00 	lea    0x5900(%rip),%rdi        # 80ef <_IO_stdin_used+0xef>
    27ef:	e8 2c fb ff ff       	call   2320 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    27f4:	be 18 00 00 00       	mov    $0x18,%esi
    27f9:	bf 02 00 00 00       	mov    $0x2,%edi
    27fe:	e8 ed fb ff ff       	call   23f0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2803:	be c8 00 00 00       	mov    $0xc8,%esi
    2808:	bf 08 00 00 00       	mov    $0x8,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    280d:	48 89 84 24 80 00 00 00 	mov    %rax,0x80(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2815:	e8 d6 fb ff ff       	call   23f0 <calloc@plt>
    281a:	ba 04 00 00 00       	mov    $0x4,%edx
    281f:	bf 01 00 00 00       	mov    $0x1,%edi
    2824:	48 8d 35 4b 5b 00 00 	lea    0x5b4b(%rip),%rsi        # 8376 <_IO_stdin_used+0x376>
    282b:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2830:	31 c0                	xor    %eax,%eax
    2832:	e8 69 fc ff ff       	call   24a0 <__printf_chk@plt>
    2837:	ba 08 00 00 00       	mov    $0x8,%edx
    283c:	48 8d 35 49 5b 00 00 	lea    0x5b49(%rip),%rsi        # 838c <_IO_stdin_used+0x38c>
    2843:	31 c0                	xor    %eax,%eax
    2845:	bf 01 00 00 00       	mov    $0x1,%edi
    284a:	e8 51 fc ff ff       	call   24a0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    284f:	be 10 00 00 00       	mov    $0x10,%esi
    2854:	bf 08 00 00 00       	mov    $0x8,%edi
    2859:	e8 92 fb ff ff       	call   23f0 <calloc@plt>
    285e:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    2866:	49 89 c4             	mov    %rax,%r12
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    2869:	48 8d 98 80 00 00 00 	lea    0x80(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2870:	49 89 c5             	mov    %rax,%r13
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2873:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    2878:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2880:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2885:	49 83 c5 10          	add    $0x10,%r13
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2889:	e8 62 fb ff ff       	call   23f0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    288e:	be 20 00 00 00       	mov    $0x20,%esi
    2893:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2898:	49 89 45 f8          	mov    %rax,-0x8(%r13)
    289c:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
    289f:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    28a9:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    28b3:	e8 38 fb ff ff       	call   23f0 <calloc@plt>
    28b8:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    28bf:	49 39 dd             	cmp    %rbx,%r13
    28c2:	75 af                	jne    2873 <main+0x223>
    28c4:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    28c9:	4c 89 e0             	mov    %r12,%rax
    28cc:	ba 03 00 00 00       	mov    $0x3,%edx
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
  for (int k = 0 ; k < group_count ; k++) {
    28d1:	45 31 f6             	xor    %r14d,%r14d
    28d4:	48 8b b4 24 80 00 00 00 	mov    0x80(%rsp),%rsi
  int cur_buffer = 0;
    28dc:	c7 44 24 60 00 00 00 00 	movl   $0x0,0x60(%rsp)
  int dataid = 0;
    28e4:	45 31 ff             	xor    %r15d,%r15d
  int curcpu = 0;
    28e7:	c7 44 24 5c 00 00 00 00 	movl   $0x0,0x5c(%rsp)
    28ef:	49 89 dc             	mov    %rbx,%r12
    28f2:	48 89 b4 24 98 00 00 00 	mov    %rsi,0x98(%rsp)
    28fa:	48 89 9c 24 90 00 00 00 	mov    %rbx,0x90(%rsp)
    2902:	48 89 c3             	mov    %rax,%rbx
    for (int d = 0 ; d < threads_per_group ; d++) {
    2905:	48 63 44 24 60       	movslq 0x60(%rsp),%rax
    290a:	8d 7a fe             	lea    -0x2(%rdx),%edi
    290d:	89 54 24 64          	mov    %edx,0x64(%rsp)
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2911:	4d 89 e1             	mov    %r12,%r9
    2914:	89 7c 24 20          	mov    %edi,0x20(%rsp)
    2918:	48 c1 e0 04          	shl    $0x4,%rax
    291c:	48 89 b4 24 a0 00 00 00 	mov    %rsi,0xa0(%rsp)
    2924:	4c 89 a4 24 b0 00 00 00 	mov    %r12,0xb0(%rsp)
    292c:	48 01 d8             	add    %rbx,%rax
    292f:	48 89 9c 24 b8 00 00 00 	mov    %rbx,0xb8(%rsp)
    2937:	48 89 c3             	mov    %rax,%rbx
    293a:	8b 44 24 20          	mov    0x20(%rsp),%eax
    293e:	44 89 fa             	mov    %r15d,%edx
    2941:	bf 01 00 00 00       	mov    $0x1,%edi
    2946:	4c 89 0c 24          	mov    %r9,(%rsp)
    294a:	48 8d 35 cf 5d 00 00 	lea    0x5dcf(%rip),%rsi        # 8720 <_IO_stdin_used+0x720>
    2951:	44 8d 40 ff          	lea    -0x1(%rax),%r8d
    2955:	31 c0                	xor    %eax,%eax
    2957:	44 89 c1             	mov    %r8d,%ecx
    295a:	44 89 44 24 18       	mov    %r8d,0x18(%rsp)
    295f:	45 89 c5             	mov    %r8d,%r13d
    2962:	e8 39 fb ff ff       	call   24a0 <__printf_chk@plt>
      int x = (k * threads_per_group) + d;
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2967:	be 08 00 00 00       	mov    $0x8,%esi
    296c:	bf 02 00 00 00       	mov    $0x2,%edi
    2971:	e8 7a fa ff ff       	call   23f0 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2976:	be 80 00 00 00       	mov    $0x80,%esi
    297b:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2980:	48 89 c5             	mov    %rax,%rbp
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2983:	e8 68 fa ff ff       	call   23f0 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2988:	45 89 e8             	mov    %r13d,%r8d
    298b:	4c 8b 0c 24          	mov    (%rsp),%r9
    298f:	41 83 e0 01          	and    $0x1,%r8d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2993:	49 89 c4             	mov    %rax,%r12
      if (x % 2 == 1) {
    2996:	44 89 44 24 50       	mov    %r8d,0x50(%rsp)
    299b:	0f 84 a4 08 00 00    	je     3245 <main+0xbf5>
        other = abs(x - 1) % total_threads;
    29a1:	8b 44 24 20          	mov    0x20(%rsp),%eax
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    29a5:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
        my_thread_data[1] = &thread_data[x]; 
    29aa:	4c 89 ca             	mov    %r9,%rdx
        other = abs(x - 1) % total_threads;
    29ad:	83 e8 02             	sub    $0x2,%eax
    29b0:	48 89 c1             	mov    %rax,%rcx
        my_thread_data[0] = &thread_data[other]; 
    29b3:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    29b7:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    29bb:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    29bf:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
    29c3:	48 89 7c 24 40       	mov    %rdi,0x40(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    29c8:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
    29d0:	44 8b 6c 24 18       	mov    0x18(%rsp),%r13d
        thread_data[x].thread_index = 1;
    29d5:	45 89 41 04          	mov    %r8d,0x4(%r9)
    29d9:	48 8d 35 70 5d 00 00 	lea    0x5d70(%rip),%rsi        # 8750 <_IO_stdin_used+0x750>
    29e0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
        thread_data[x].protected_state = &protected_state[k];
    29e4:	49 89 79 48          	mov    %rdi,0x48(%r9)
    29e8:	44 89 ea             	mov    %r13d,%edx
    29eb:	bf 01 00 00 00       	mov    $0x1,%edi
    29f0:	48 89 45 00          	mov    %rax,0x0(%rbp)
    29f4:	31 c0                	xor    %eax,%eax
    29f6:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    29fb:	89 0c 24             	mov    %ecx,(%rsp)
    29fe:	e8 9d fa ff ff       	call   24a0 <__printf_chk@plt>
      thread_data[x].other = other;
    2a03:	8b 0c 24             	mov    (%rsp),%ecx
    2a06:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2a0b:	31 c0                	xor    %eax,%eax
    2a0d:	44 89 ea             	mov    %r13d,%edx
    2a10:	48 8d 35 69 5d 00 00 	lea    0x5d69(%rip),%rsi        # 8780 <_IO_stdin_used+0x780>
    2a17:	bf 01 00 00 00       	mov    $0x1,%edi
    2a1c:	41 89 89 b8 00 00 00 	mov    %ecx,0xb8(%r9)
    2a23:	8b 4c 24 5c          	mov    0x5c(%rsp),%ecx
    2a27:	4c 89 0c 24          	mov    %r9,(%rsp)
    2a2b:	e8 70 fa ff ff       	call   24a0 <__printf_chk@plt>
        if (x < thread_count) {
    2a30:	41 83 fd 01          	cmp    $0x1,%r13d
    2a34:	4c 8b 0c 24          	mov    (%rsp),%r9
    2a38:	0f 8f 2e 08 00 00    	jg     326c <main+0xc1c>
          CPU_SET(curcpu, sendercpu);
    2a3e:	48 63 44 24 5c       	movslq 0x5c(%rsp),%rax
    2a43:	48 89 c7             	mov    %rax,%rdi
    2a46:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2a4c:	77 12                	ja     2a60 <main+0x410>
    2a4e:	48 c1 e8 06          	shr    $0x6,%rax
    2a52:	ba 01 00 00 00       	mov    $0x1,%edx
    2a57:	89 f9                	mov    %edi,%ecx
    2a59:	48 d3 e2             	shl    %cl,%rdx
    2a5c:	49 09 14 c4          	or     %rdx,(%r12,%rax,8)
          curcpu += 2;
    2a60:	83 44 24 5c 02       	addl   $0x2,0x5c(%rsp)
      thread_data[x].real_thread_index = x;
    2a65:	8b 44 24 18          	mov    0x18(%rsp),%eax
      thread_data[x].threads = my_thread_data;
    2a69:	49 89 69 18          	mov    %rbp,0x18(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a6d:	be 10 00 00 00       	mov    $0x10,%esi
    2a72:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].kind = KERNEL_THREAD;
    2a77:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a7e:	31 ed                	xor    %ebp,%ebp
      thread_data[x].real_thread_index = x;
    2a80:	41 89 41 08          	mov    %eax,0x8(%r9)
      thread_data[x].all_threads = thread_data;
    2a84:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
      thread_data[x].cpu_set = sendercpu;
    2a89:	4d 89 a1 b0 00 00 00 	mov    %r12,0xb0(%r9)
      thread_data[x].all_threads = thread_data;
    2a90:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2a94:	48 8b 05 f5 61 00 00 	mov    0x61f5(%rip),%rax        # 8c90 <_IO_stdin_used+0xc90>
      thread_data[x].task_count = total_barrier_count;
    2a9b:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].group_count = group_count;
    2aa3:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
      thread_data[x].thread_count = 2;
    2aaa:	48 8b 05 ef 61 00 00 	mov    0x61ef(%rip),%rax        # 8ca0 <_IO_stdin_used+0xca0>
      thread_data[x].task_count = total_barrier_count;
    2ab1:	4c 89 0c 24          	mov    %r9,(%rsp)
      thread_data[x].thread_count = 2;
    2ab5:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2ab9:	e8 32 f9 ff ff       	call   23f0 <calloc@plt>
    2abe:	4c 8b 0c 24          	mov    (%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2ac2:	be 10 00 00 00       	mov    $0x10,%esi
    2ac7:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2acc:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2ad0:	e8 1b f9 ff ff       	call   23f0 <calloc@plt>
    2ad5:	4c 8b 0c 24          	mov    (%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2ad9:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2ade:	66 0f 6f 3d 8a 61 00 00 	movdqa 0x618a(%rip),%xmm7        # 8c70 <_IO_stdin_used+0xc70>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2ae6:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2aeb:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2aef:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2af7:	e8 f4 f8 ff ff       	call   23f0 <calloc@plt>
    2afc:	4c 8b 0c 24          	mov    (%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2b00:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_timestamp_count = 0;
    2b05:	66 0f 6f 35 63 61 00 00 	movdqa 0x6163(%rip),%xmm6        # 8c70 <_IO_stdin_used+0xc70>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2b0d:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2b12:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2b19:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2b21:	e8 ca f8 ff ff       	call   23f0 <calloc@plt>
        thread_data[x].tasks = barriers;
    2b26:	4c 8b 0c 24          	mov    (%rsp),%r9
              data[0].messages_count = 0;
    2b2a:	48 89 9c 24 a8 00 00 00 	mov    %rbx,0xa8(%rsp)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2b32:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks = barriers;
    2b35:	49 89 41 38          	mov    %rax,0x38(%r9)
              data[0].messages_count = 0;
    2b39:	4d 89 cd             	mov    %r9,%r13
          thread_data[x].tasks[y].protected = do_protected_write; 
    2b3c:	48 63 c5             	movslq %ebp,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2b3f:	be 38 00 00 00       	mov    $0x38,%esi
    2b44:	bf 04 00 00 00       	mov    $0x4,%edi
          thread_data[x].tasks[y].protected = do_protected_write; 
    2b49:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2b4e:	48 c1 e0 09          	shl    $0x9,%rax
    2b52:	4c 8d 24 02          	lea    (%rdx,%rax,1),%r12
    2b56:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2b5b:	48 8d 05 be 16 00 00 	lea    0x16be(%rip),%rax        # 4220 <do_protected_write>
    2b62:	49 89 84 24 20 01 00 00 	mov    %rax,0x120(%r12)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2b6a:	e8 81 f8 ff ff       	call   23f0 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2b6f:	8b 54 24 50          	mov    0x50(%rsp),%edx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2b73:	4c 89 2c 24          	mov    %r13,(%rsp)
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2b77:	49 89 84 24 70 01 00 00 	mov    %rax,0x170(%r12)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2b7f:	45 31 e4             	xor    %r12d,%r12d
    2b82:	49 89 c5             	mov    %rax,%r13
    2b85:	85 d2                	test   %edx,%edx
    2b87:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2b8c:	0f 84 36 04 00 00    	je     2fc8 <main+0x978>
            int group_of = b / threads_per_group;
    2b92:	44 89 e3             	mov    %r12d,%ebx
    2b95:	31 c0                	xor    %eax,%eax
    2b97:	44 89 e2             	mov    %r12d,%edx
    2b9a:	bf 01 00 00 00       	mov    $0x1,%edi
    2b9f:	d1 fb                	sar    %ebx
    2ba1:	48 8d 35 fe 57 00 00 	lea    0x57fe(%rip),%rsi        # 83a6 <_IO_stdin_used+0x3a6>
    2ba8:	89 d9                	mov    %ebx,%ecx
    2baa:	e8 f1 f8 ff ff       	call   24a0 <__printf_chk@plt>
            if (k == group_of) {
    2baf:	41 39 df             	cmp    %ebx,%r15d
    2bb2:	0f 84 49 04 00 00    	je     3001 <main+0x9b1>
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2bb8:	41 83 c4 01          	add    $0x1,%r12d
    2bbc:	49 83 c5 38          	add    $0x38,%r13
    2bc0:	41 83 fc 04          	cmp    $0x4,%r12d
    2bc4:	75 cc                	jne    2b92 <main+0x542>
    2bc6:	4c 8b 2c 24          	mov    (%rsp),%r13
    2bca:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2bcf:	45 31 e4             	xor    %r12d,%r12d
    2bd2:	44 89 3c 24          	mov    %r15d,(%rsp)
    2bd6:	44 89 e3             	mov    %r12d,%ebx
    2bd9:	41 89 ef             	mov    %ebp,%r15d
    2bdc:	4c 89 6c 24 48       	mov    %r13,0x48(%rsp)
    2be1:	44 8b 6c 24 18       	mov    0x18(%rsp),%r13d
    2be6:	48 89 cd             	mov    %rcx,%rbp
            int group_of = b / threads_per_group;
    2be9:	89 d8                	mov    %ebx,%eax
    2beb:	d1 f8                	sar    %eax
            if (k == group_of) {
    2bed:	39 04 24             	cmp    %eax,(%rsp)
    2bf0:	0f 84 54 01 00 00    	je     2d4a <main+0x6fa>
    2bf6:	89 da                	mov    %ebx,%edx
    2bf8:	48 8d 35 b7 57 00 00 	lea    0x57b7(%rip),%rsi        # 83b6 <_IO_stdin_used+0x3b6>
    2bff:	bf 01 00 00 00       	mov    $0x1,%edi
    2c04:	31 c0                	xor    %eax,%eax
    2c06:	e8 95 f8 ff ff       	call   24a0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2c0b:	be 08 00 00 00       	mov    $0x8,%esi
    2c10:	bf 01 00 00 00       	mov    $0x1,%edi
    2c15:	e8 d6 f7 ff ff       	call   23f0 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2c1a:	be 08 00 00 00       	mov    $0x8,%esi
    2c1f:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2c24:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2c29:	e8 c2 f7 ff ff       	call   23f0 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    2c2e:	be 80 03 00 00       	mov    $0x380,%esi
    2c33:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2c38:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
            struct Data *data = calloc(3, sizeof(struct Data));
    2c3d:	e8 ae f7 ff ff       	call   23f0 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    2c42:	be 80 03 00 00       	mov    $0x380,%esi
    2c47:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    2c4c:	49 89 c4             	mov    %rax,%r12
            struct Data **stack = calloc(3, sizeof(struct Data));
    2c4f:	e8 9c f7 ff ff       	call   23f0 <calloc@plt>
            data[0].id = dataid++;
    2c54:	41 8d 76 01          	lea    0x1(%r14),%esi
            data[0].messages = messages;
    2c58:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
            data[1].messages = messages2;
    2c5d:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
            data[1].id = dataid++;
    2c62:	41 89 b4 24 a8 06 00 00 	mov    %esi,0x6a8(%r12)
            mailboxes[b].higher = &data[1];
    2c6a:	49 8d b4 24 80 03 00 00 	lea    0x380(%r12),%rsi
            data[0].messages_count = 0;
    2c72:	66 0f 6f 25 06 60 00 00 	movdqa 0x6006(%rip),%xmm4        # 8c80 <_IO_stdin_used+0xc80>
            data[0].kind = MAILBOX_LOWER;
    2c7a:	41 c7 84 24 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r12)
            data[0].a = x;
    2c86:	45 89 ac 24 1c 03 00 00 	mov    %r13d,0x31c(%r12)
            data[0].b = y;
    2c8e:	45 89 bc 24 20 03 00 00 	mov    %r15d,0x320(%r12)
            data[0].c = b;
    2c96:	41 89 9c 24 24 03 00 00 	mov    %ebx,0x324(%r12)
            data[1].kind = MAILBOX_HIGHER;
    2c9e:	41 c7 84 24 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r12)
            data[1].a = x;
    2caa:	45 89 ac 24 9c 06 00 00 	mov    %r13d,0x69c(%r12)
            data[1].b = y;
    2cb2:	45 89 bc 24 a0 06 00 00 	mov    %r15d,0x6a0(%r12)
            data[1].c = b;
    2cba:	41 89 9c 24 a4 06 00 00 	mov    %ebx,0x6a4(%r12)
            mailboxes[b].lower = &data[0];
    2cc2:	4c 89 65 00          	mov    %r12,0x0(%rbp)
            mailboxes[b].my_lower = &data[0];
    2cc6:	4c 89 65 20          	mov    %r12,0x20(%rbp)
            mailboxes[b].higher = &data[1];
    2cca:	48 89 75 08          	mov    %rsi,0x8(%rbp)
            data[0].finished_reading = 1;
    2cce:	41 c7 84 24 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r12)
            mailboxes[b].my_higher = &data[1];
    2cda:	48 89 75 28          	mov    %rsi,0x28(%rbp)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2cde:	c7 45 30 02 00 00 00 	movl   $0x2,0x30(%rbp)
            stack[0] = mailboxes[b].lower;
    2ce5:	4c 89 20             	mov    %r12,(%rax)
            stack[1] = mailboxes[b].higher;
    2ce8:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    2cec:	48 89 45 18          	mov    %rax,0x18(%rbp)
            data[0].available_sending = 0;
    2cf0:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
            data[0].available_receiving = 0;
    2cfc:	41 c7 84 24 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r12)
            data[0].messages = messages;
    2d08:	4d 89 0c 24          	mov    %r9,(%r12)
            data[1].messages = messages2;
    2d0c:	49 89 94 24 80 03 00 00 	mov    %rdx,0x380(%r12)
            data[1].available_sending = 1;
    2d14:	41 c7 84 24 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r12)
            data[1].available_receiving = 0;
    2d20:	41 c7 84 24 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r12)
            data[0].id = dataid++;
    2d2c:	45 89 b4 24 28 03 00 00 	mov    %r14d,0x328(%r12)
            data[1].id = dataid++;
    2d34:	41 83 c6 02          	add    $0x2,%r14d
            data[0].messages_count = 0;
    2d38:	41 0f 29 a4 24 80 00 00 00 	movaps %xmm4,0x80(%r12)
            data[1].messages_count = 0;
    2d41:	41 0f 29 a4 24 00 04 00 00 	movaps %xmm4,0x400(%r12)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d4a:	83 c3 01             	add    $0x1,%ebx
    2d4d:	48 83 c5 38          	add    $0x38,%rbp
    2d51:	83 fb 04             	cmp    $0x4,%ebx
    2d54:	0f 85 8f fe ff ff    	jne    2be9 <main+0x599>
          char *message = malloc(sizeof(char) * 256);
    2d5a:	be 01 00 00 00       	mov    $0x1,%esi
    2d5f:	bf 00 01 00 00       	mov    $0x100,%edi
    2d64:	4c 8b 6c 24 48       	mov    0x48(%rsp),%r13
    2d69:	44 89 fd             	mov    %r15d,%ebp
    2d6c:	44 8b 3c 24          	mov    (%rsp),%r15d
    2d70:	e8 7b f6 ff ff       	call   23f0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2d75:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    2d7a:	49 89 c4             	mov    %rax,%r12
          struct Message *messaged = malloc(sizeof(struct Message));
    2d7d:	e8 de f6 ff ff       	call   2460 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2d82:	48 83 ec 08          	sub    $0x8,%rsp
    2d86:	4c 89 e7             	mov    %r12,%rdi
    2d89:	41 89 e9             	mov    %ebp,%r9d
    2d8c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2d91:	48 8d 0d 30 5a 00 00 	lea    0x5a30(%rip),%rcx        # 87c8 <_IO_stdin_used+0x7c8>
    2d98:	ba 00 01 00 00       	mov    $0x100,%edx
    2d9d:	31 c0                	xor    %eax,%eax
    2d9f:	41 57                	push   %r15
    2da1:	44 8b 44 24 28       	mov    0x28(%rsp),%r8d
    2da6:	be 01 00 00 00       	mov    $0x1,%esi
    2dab:	e8 d0 f7 ff ff       	call   2580 <__sprintf_chk@plt>
          messaged->message = message;
    2db0:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
          messaged->task_index = y;
    2db5:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2dba:	be 20 00 00 00       	mov    $0x20,%esi
          thread_data[x].tasks[y].group = k;
    2dbf:	49 8b 55 38          	mov    0x38(%r13),%rdx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2dc3:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->task_index = y;
    2dc8:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2dcc:	49 63 45 08          	movslq 0x8(%r13),%rax
          messaged->message = message;
    2dd0:	4d 89 22             	mov    %r12,(%r10)
          thread_data[x].tasks[y].group = k;
    2dd3:	4c 8b 64 24 38       	mov    0x38(%rsp),%r12
          messaged->thread_index = thread_data[x].real_thread_index;
    2dd8:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2ddc:	8d 45 01             	lea    0x1(%rbp),%eax
          thread_data[x].tasks[y].group = k;
    2ddf:	49 01 d4             	add    %rdx,%r12
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2de2:	83 e0 01             	and    $0x1,%eax
          messaged->group = k;
    2de5:	45 89 7a 18          	mov    %r15d,0x18(%r10)
          thread_data[x].tasks[y].group = k;
    2de9:	45 89 bc 24 94 01 00 00 	mov    %r15d,0x194(%r12)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2df1:	41 c7 04 24 41 00 00 00 	movl   $0x41,(%r12)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2df9:	41 89 84 24 90 01 00 00 	mov    %eax,0x190(%r12)
          thread_data[x].tasks[y].message = messaged;
    2e01:	4d 89 94 24 88 01 00 00 	mov    %r10,0x188(%r12)
          thread_data[x].tasks[y].sending = 1;
    2e09:	41 c7 84 24 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r12)
          thread_data[x].tasks[y].snapshot_count = 99;
    2e15:	49 c7 84 24 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%r12)
          thread_data[x].tasks[y].group = k;
    2e21:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2e26:	e8 c5 f5 ff ff       	call   23f0 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    2e2b:	49 c7 84 24 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%r12)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2e37:	49 89 84 24 50 01 00 00 	mov    %rax,0x150(%r12)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2e3f:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    2e44:	48 8b 00             	mov    (%rax),%rax
    2e47:	8b 48 04             	mov    0x4(%rax),%ecx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2e4a:	4c 39 e8             	cmp    %r13,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2e4d:	49 89 84 24 28 01 00 00 	mov    %rax,0x128(%r12)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2e55:	41 89 8c 24 30 01 00 00 	mov    %ecx,0x130(%r12)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2e5d:	41 5b                	pop    %r11
    2e5f:	5b                   	pop    %rbx
    2e60:	48 8b 14 24          	mov    (%rsp),%rdx
    2e64:	0f 85 ad 12 00 00    	jne    4117 <main+0x1ac7>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2e6a:	66 0f 6f 05 1e 5e 00 00 	movdqa 0x5e1e(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
          thread_data[x].tasks[y].available = 1;
    2e72:	48 8b 0d 2f 5e 00 00 	mov    0x5e2f(%rip),%rcx        # 8ca8 <_IO_stdin_used+0xca8>
          thread_data[x].tasks[y].arrived = 0;
    2e79:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
    2e85:	41 c7 84 24 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%r12)
          thread_data[x].tasks[y].available = 1;
    2e91:	49 89 8c 24 44 01 00 00 	mov    %rcx,0x144(%r12)
          thread_data[x].tasks[y].task_index = y;
    2e99:	41 89 6c 24 04       	mov    %ebp,0x4(%r12)
          thread_data[x].tasks[y].thread_count = 2;
    2e9e:	41 0f 11 84 24 34 01 00 00 	movups %xmm0,0x134(%r12)
          if (y == barrier_count - 1) {
    2ea7:	83 fd 01             	cmp    $0x1,%ebp
    2eaa:	0f 84 87 03 00 00    	je     3237 <main+0xbe7>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2eb0:	85 ed                	test   %ebp,%ebp
    2eb2:	0f 84 66 03 00 00    	je     321e <main+0xbce>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    2eb8:	48 8d 05 31 37 00 00 	lea    0x3731(%rip),%rax        # 65f0 <barriered_work>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2ebf:	bf 01 00 00 00       	mov    $0x1,%edi
    2ec4:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    2ec9:	48 8b 9c 24 a8 00 00 00 	mov    0xa8(%rsp),%rbx
    2ed1:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
        thread_data[x].buffers_count = buffers_per_thread;
    2ed9:	41 c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r13)
               thread_data[x].tasks[y].run = barriered_work; 
    2ee4:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
        thread_data[x].buffers_count = buffers_per_thread;
    2ee9:	4c 89 2c 24          	mov    %r13,(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2eed:	e8 fe f4 ff ff       	call   23f0 <calloc@plt>
    2ef2:	4c 8b 0c 24          	mov    (%rsp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2ef6:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    2efb:	66 0f 6f 74 24 70    	movdqa 0x70(%rsp),%xmm6
    for (int d = 0 ; d < threads_per_group ; d++) {
    2f01:	8b 7c 24 64          	mov    0x64(%rsp),%edi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2f05:	48 89 18             	mov    %rbx,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2f08:	48 83 c3 10          	add    $0x10,%rbx
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2f0c:	49 89 41 50          	mov    %rax,0x50(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2f10:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    2f15:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
    2f1c:	83 44 24 20 01       	addl   $0x1,0x20(%rsp)
        thread_data[x].tasks[barrier_count].available = 1; 
    2f21:	48 8b 0d 80 5d 00 00 	mov    0x5d80(%rip),%rcx        # 8ca8 <_IO_stdin_used+0xca8>
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2f28:	48 8b 00             	mov    (%rax),%rax
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2f2b:	83 44 24 60 01       	addl   $0x1,0x60(%rsp)
        thread_data[x].tasks[barrier_count].arrived = 0; 
    2f30:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2f3a:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2f41:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    2f4b:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2f55:	41 8b 81 3c ff ff ff 	mov    -0xc4(%r9),%eax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2f5c:	0f 11 b2 18 05 00 00 	movups %xmm6,0x518(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2f63:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2f69:	8b 44 24 20          	mov    0x20(%rsp),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2f6d:	c7 82 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
    2f77:	48 89 8a 44 05 00 00 	mov    %rcx,0x544(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2f7e:	39 f8                	cmp    %edi,%eax
    2f80:	0f 85 b4 f9 ff ff    	jne    293a <main+0x2ea>
    2f86:	48 8b b4 24 a0 00 00 00 	mov    0xa0(%rsp),%rsi
    2f8e:	4c 8b a4 24 b0 00 00 00 	mov    0xb0(%rsp),%r12
    2f96:	89 fa                	mov    %edi,%edx
    2f98:	48 8b 9c 24 b8 00 00 00 	mov    0xb8(%rsp),%rbx
  for (int k = 0 ; k < group_count ; k++) {
    2fa0:	83 c2 02             	add    $0x2,%edx
    2fa3:	48 83 c6 18          	add    $0x18,%rsi
    2fa7:	49 81 c4 90 01 00 00 	add    $0x190,%r12
    2fae:	45 85 ff             	test   %r15d,%r15d
    2fb1:	0f 85 c2 02 00 00    	jne    3279 <main+0xc29>
    2fb7:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    2fbd:	e9 43 f9 ff ff       	jmp    2905 <main+0x2b5>
    2fc2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            int group_of = b / threads_per_group;
    2fc8:	44 89 e3             	mov    %r12d,%ebx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2fcb:	31 c0                	xor    %eax,%eax
    2fcd:	44 89 e2             	mov    %r12d,%edx
    2fd0:	bf 01 00 00 00       	mov    $0x1,%edi
    2fd5:	d1 fb                	sar    %ebx
    2fd7:	48 8d 35 c8 53 00 00 	lea    0x53c8(%rip),%rsi        # 83a6 <_IO_stdin_used+0x3a6>
    2fde:	89 d9                	mov    %ebx,%ecx
    2fe0:	e8 bb f4 ff ff       	call   24a0 <__printf_chk@plt>
            if (k == group_of) {
    2fe5:	41 39 df             	cmp    %ebx,%r15d
    2fe8:	0f 84 22 01 00 00    	je     3110 <main+0xac0>
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2fee:	41 83 c4 01          	add    $0x1,%r12d
    2ff2:	49 83 c5 38          	add    $0x38,%r13
    2ff6:	41 83 fc 04          	cmp    $0x4,%r12d
    2ffa:	75 cc                	jne    2fc8 <main+0x978>
    2ffc:	e9 c5 fb ff ff       	jmp    2bc6 <main+0x576>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3001:	be 08 00 00 00       	mov    $0x8,%esi
    3006:	bf 01 00 00 00       	mov    $0x1,%edi
    300b:	e8 e0 f3 ff ff       	call   23f0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3010:	be 08 00 00 00       	mov    $0x8,%esi
    3015:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    301a:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    301f:	e8 cc f3 ff ff       	call   23f0 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    3024:	be 80 03 00 00       	mov    $0x380,%esi
    3029:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    302e:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    3033:	e8 b8 f3 ff ff       	call   23f0 <calloc@plt>
              data[0].a = x;
    3038:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    303c:	44 89 e2             	mov    %r12d,%edx
              mailboxes[b].kind = MAILBOX_FRIEND;
    303f:	41 c7 45 30 01 00 00 00 	movl   $0x1,0x30(%r13)
              struct Data *data = calloc(3, sizeof(struct Data));
    3047:	49 89 c0             	mov    %rax,%r8
              data[0].b = y;
    304a:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
    3050:	48 8d 35 49 57 00 00 	lea    0x5749(%rip),%rsi        # 87a0 <_IO_stdin_used+0x7a0>
              data[0].a = x;
    3057:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].kind = MAILBOX_LOWER;
    305d:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].c = b;
    3067:	44 89 a0 24 03 00 00 	mov    %r12d,0x324(%rax)
              data[0].id = dataid++;
    306e:	41 8d 46 01          	lea    0x1(%r14),%eax
              data[1].id = dataid++;
    3072:	41 89 80 a8 06 00 00 	mov    %eax,0x6a8(%r8)
              mailboxes[b].higher = &data[1];
    3079:	49 8d 80 80 03 00 00 	lea    0x380(%r8),%rax
    3080:	49 89 45 08          	mov    %rax,0x8(%r13)
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    3084:	8b 44 24 20          	mov    0x20(%rsp),%eax
              data[0].id = dataid++;
    3088:	45 89 b0 28 03 00 00 	mov    %r14d,0x328(%r8)
              data[1].id = dataid++;
    308f:	41 83 c6 02          	add    $0x2,%r14d
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    3093:	8d 48 fe             	lea    -0x2(%rax),%ecx
              data[1].a = x;
    3096:	41 89 b8 9c 06 00 00 	mov    %edi,0x69c(%r8)
    309d:	31 c0                	xor    %eax,%eax
    309f:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].kind = MAILBOX_HIGHER;
    30a4:	41 c7 80 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r8)
              data[1].b = y;
    30af:	41 89 a8 a0 06 00 00 	mov    %ebp,0x6a0(%r8)
              data[1].c = b;
    30b6:	45 89 a0 a4 06 00 00 	mov    %r12d,0x6a4(%r8)
              mailboxes[b].lower = &data[0];
    30bd:	4d 89 45 00          	mov    %r8,0x0(%r13)
              data[0].finished_reading = 1;
    30c1:	41 c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r8)
    30cc:	41 89 4d 34          	mov    %ecx,0x34(%r13)
    30d0:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    30d5:	e8 c6 f3 ff ff       	call   24a0 <__printf_chk@plt>
              data[0].messages = messages;
    30da:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    30df:	4c 8b 54 24 68       	mov    0x68(%rsp),%r10
              data[0].messages_count = 0;
    30e4:	66 0f 6f 3d 94 5b 00 00 	movdqa 0x5b94(%rip),%xmm7        # 8c80 <_IO_stdin_used+0xc80>
              data[1].messages = messages2;
    30ec:	4c 8b 4c 24 48       	mov    0x48(%rsp),%r9
              data[0].messages = messages;
    30f1:	4d 89 10             	mov    %r10,(%r8)
              data[1].messages = messages2;
    30f4:	4d 89 88 80 03 00 00 	mov    %r9,0x380(%r8)
              data[0].messages_count = 0;
    30fb:	41 0f 29 b8 80 00 00 00 	movaps %xmm7,0x80(%r8)
              data[1].messages_count = 0;
    3103:	41 0f 29 b8 00 04 00 00 	movaps %xmm7,0x400(%r8)
    310b:	e9 a8 fa ff ff       	jmp    2bb8 <main+0x568>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3110:	be 08 00 00 00       	mov    $0x8,%esi
    3115:	bf 01 00 00 00       	mov    $0x1,%edi
    311a:	e8 d1 f2 ff ff       	call   23f0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    311f:	be 08 00 00 00       	mov    $0x8,%esi
    3124:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3129:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    312e:	e8 bd f2 ff ff       	call   23f0 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    3133:	be 80 03 00 00       	mov    $0x380,%esi
    3138:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    313d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    3142:	e8 a9 f2 ff ff       	call   23f0 <calloc@plt>
              data[0].a = x;
    3147:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    314b:	44 89 e2             	mov    %r12d,%edx
              mailboxes[b].kind = MAILBOX_FRIEND;
    314e:	41 c7 45 30 01 00 00 00 	movl   $0x1,0x30(%r13)
              struct Data *data = calloc(3, sizeof(struct Data));
    3156:	49 89 c0             	mov    %rax,%r8
              data[0].b = y;
    3159:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
    315f:	48 8d 35 3a 56 00 00 	lea    0x563a(%rip),%rsi        # 87a0 <_IO_stdin_used+0x7a0>
              data[0].a = x;
    3166:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].kind = MAILBOX_LOWER;
    316c:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].c = b;
    3176:	44 89 a0 24 03 00 00 	mov    %r12d,0x324(%rax)
              data[0].id = dataid++;
    317d:	41 8d 46 01          	lea    0x1(%r14),%eax
              data[1].id = dataid++;
    3181:	41 89 80 a8 06 00 00 	mov    %eax,0x6a8(%r8)
              mailboxes[b].higher = &data[1];
    3188:	49 8d 80 80 03 00 00 	lea    0x380(%r8),%rax
    318f:	49 89 45 08          	mov    %rax,0x8(%r13)
    3193:	8b 44 24 20          	mov    0x20(%rsp),%eax
              data[0].id = dataid++;
    3197:	45 89 b0 28 03 00 00 	mov    %r14d,0x328(%r8)
              data[1].id = dataid++;
    319e:	41 83 c6 02          	add    $0x2,%r14d
              data[1].a = x;
    31a2:	41 89 b8 9c 06 00 00 	mov    %edi,0x69c(%r8)
    31a9:	89 c1                	mov    %eax,%ecx
    31ab:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].kind = MAILBOX_HIGHER;
    31b0:	41 c7 80 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r8)
              data[1].b = y;
    31bb:	41 89 a8 a0 06 00 00 	mov    %ebp,0x6a0(%r8)
              data[1].c = b;
    31c2:	45 89 a0 a4 06 00 00 	mov    %r12d,0x6a4(%r8)
              mailboxes[b].lower = &data[0];
    31c9:	4d 89 45 00          	mov    %r8,0x0(%r13)
              data[0].finished_reading = 1;
    31cd:	41 c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r8)
    31d8:	41 89 45 34          	mov    %eax,0x34(%r13)
    31dc:	31 c0                	xor    %eax,%eax
    31de:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    31e3:	e8 b8 f2 ff ff       	call   24a0 <__printf_chk@plt>
              data[0].messages = messages;
    31e8:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    31ed:	4c 8b 54 24 68       	mov    0x68(%rsp),%r10
              data[0].messages_count = 0;
    31f2:	66 0f 6f 35 86 5a 00 00 	movdqa 0x5a86(%rip),%xmm6        # 8c80 <_IO_stdin_used+0xc80>
              data[1].messages = messages2;
    31fa:	4c 8b 4c 24 48       	mov    0x48(%rsp),%r9
              data[0].messages = messages;
    31ff:	4d 89 10             	mov    %r10,(%r8)
              data[1].messages = messages2;
    3202:	4d 89 88 80 03 00 00 	mov    %r9,0x380(%r8)
              data[0].messages_count = 0;
    3209:	41 0f 29 b0 80 00 00 00 	movaps %xmm6,0x80(%r8)
              data[1].messages_count = 0;
    3211:	41 0f 29 b0 00 04 00 00 	movaps %xmm6,0x400(%r8)
    3219:	e9 d0 fd ff ff       	jmp    2fee <main+0x99e>
    321e:	48 8d 05 6b 39 00 00 	lea    0x396b(%rip),%rax        # 6b90 <barriered_work_ingest_andwork>
    3225:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    322a:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    3232:	e9 05 f9 ff ff       	jmp    2b3c <main+0x4ec>
    3237:	48 8d 05 b2 33 00 00 	lea    0x33b2(%rip),%rax        # 65f0 <barriered_work>
    323e:	bd 02 00 00 00       	mov    $0x2,%ebp
    3243:	eb e5                	jmp    322a <main+0xbda>
        other = (x + 1) % total_threads;
    3245:	8b 44 24 20          	mov    0x20(%rsp),%eax
        my_thread_data[1] = &thread_data[other]; 
    3249:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    324e:	48 89 6c 24 40       	mov    %rbp,0x40(%rsp)
    3253:	45 31 c0             	xor    %r8d,%r8d
        other = (x + 1) % total_threads;
    3256:	89 c1                	mov    %eax,%ecx
        my_thread_data[1] = &thread_data[other]; 
    3258:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    325c:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3260:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
        my_thread_data[0] = &thread_data[x]; 
    3264:	4c 89 c8             	mov    %r9,%rax
    3267:	e9 5c f7 ff ff       	jmp    29c8 <main+0x378>
            CPU_SET(j, sendercpu);
    326c:	49 81 0c 24 ff 0f 00 00 	orq    $0xfff,(%r12)
          for (int j = 0 ; j < cores ; j++) {
    3274:	e9 ec f7 ff ff       	jmp    2a65 <main+0x415>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(200, sizeof(struct Data*)); 
    3279:	be 08 00 00 00       	mov    $0x8,%esi
    327e:	bf c8 00 00 00       	mov    $0xc8,%edi
    3283:	45 89 fe             	mov    %r15d,%r14d
  int datas_size = 0; 
    3286:	31 ed                	xor    %ebp,%ebp
  struct Data ** cdatas = calloc(200, sizeof(struct Data*)); 
    3288:	e8 63 f1 ff ff       	call   23f0 <calloc@plt>
    328d:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    3292:	49 89 c7             	mov    %rax,%r15
    3295:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3297:	49 89 d1             	mov    %rdx,%r9
    329a:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    329c:	45 8b 51 40          	mov    0x40(%r9),%r10d
    32a0:	45 85 d2             	test   %r10d,%r10d
    32a3:	7e 70                	jle    3315 <main+0xcc5>
    32a5:	49 8b 79 38          	mov    0x38(%r9),%rdi
    32a9:	4d 63 c2             	movslq %r10d,%r8
    32ac:	48 63 cd             	movslq %ebp,%rcx
    32af:	49 c1 e0 09          	shl    $0x9,%r8
    32b3:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    32b7:	49 01 f8             	add    %rdi,%r8
    32ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    32c0:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    32c7:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    32ce:	48 83 c6 40          	add    $0x40,%rsi
    32d2:	f3 0f 7e 51 38       	movq   0x38(%rcx),%xmm2
    32d7:	f3 0f 7e 49 70       	movq   0x70(%rcx),%xmm1
    32dc:	f3 0f 7e 81 a8 00 00 00 	movq   0xa8(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    32e4:	f3 0f 7e 19          	movq   (%rcx),%xmm3
    32e8:	0f 16 51 40          	movhps 0x40(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    32ec:	0f 16 49 78          	movhps 0x78(%rcx),%xmm1
    32f0:	0f 16 81 b0 00 00 00 	movhps 0xb0(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    32f7:	0f 16 59 08          	movhps 0x8(%rcx),%xmm3
    32fb:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    32ff:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3303:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3307:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    330b:	49 39 f8             	cmp    %rdi,%r8
    330e:	75 b0                	jne    32c0 <main+0xc70>
    3310:	42 8d 6c d5 00       	lea    0x0(%rbp,%r10,8),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    3315:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
    331c:	85 db                	test   %ebx,%ebx
    331e:	75 08                	jne    3328 <main+0xcd8>
    3320:	44 89 f3             	mov    %r14d,%ebx
    3323:	e9 74 ff ff ff       	jmp    329c <main+0xc4c>
  for (int k = 0 ; k < group_count ; k++) {
    3328:	83 c0 02             	add    $0x2,%eax
    332b:	48 81 c2 90 01 00 00 	add    $0x190,%rdx
    3332:	83 f8 04             	cmp    $0x4,%eax
    3335:	0f 85 5c ff ff ff    	jne    3297 <main+0xc47>
    333b:	48 8d 3d 92 50 00 00 	lea    0x5092(%rip),%rdi        # 83d4 <_IO_stdin_used+0x3d4>
    3342:	e8 d9 ef ff ff       	call   2320 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    3347:	48 8d 35 9b 50 00 00 	lea    0x509b(%rip),%rsi        # 83e9 <_IO_stdin_used+0x3e9>
    334e:	48 8d 3d 96 50 00 00 	lea    0x5096(%rip),%rdi        # 83eb <_IO_stdin_used+0x3eb>
    3355:	e8 86 f1 ff ff       	call   24e0 <fopen@plt>
    335a:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < datas_size; x++) {
    335d:	85 ed                	test   %ebp,%ebp
    335f:	0f 8e 98 00 00 00    	jle    33fd <main+0xdad>
    3365:	48 63 ed             	movslq %ebp,%rbp
    3368:	4c 8d 2d 9d 50 00 00 	lea    0x509d(%rip),%r13        # 840c <_IO_stdin_used+0x40c>
    336f:	4c 8d 25 ae 50 00 00 	lea    0x50ae(%rip),%r12        # 8424 <_IO_stdin_used+0x424>
    3376:	49 8d 04 ef          	lea    (%r15,%rbp,8),%rax
    337a:	48 89 04 24          	mov    %rax,(%rsp)
    char * c = calloc(250, sizeof(char));
    337e:	be 01 00 00 00       	mov    $0x1,%esi
    3383:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    3388:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    338c:	e8 5f f0 ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3391:	48 83 ec 08          	sub    $0x8,%rsp
    3395:	4c 89 e9             	mov    %r13,%rcx
    3398:	be 01 00 00 00       	mov    $0x1,%esi
    339d:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d %d %d %d %d\n", cdatas[x]->id, cdatas[x]->kind, cdatas[x]->a, cdatas[x]->b, cdatas[x]->c);
    33a0:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    33a4:	48 89 ef             	mov    %rbp,%rdi
    33a7:	8b 90 24 03 00 00    	mov    0x324(%rax),%edx
    33ad:	44 8b 88 18 03 00 00 	mov    0x318(%rax),%r9d
    33b4:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    33bb:	52                   	push   %rdx
    33bc:	8b 90 20 03 00 00    	mov    0x320(%rax),%edx
    33c2:	52                   	push   %rdx
    33c3:	8b 80 1c 03 00 00    	mov    0x31c(%rax),%eax
    33c9:	ba fa 00 00 00       	mov    $0xfa,%edx
    33ce:	50                   	push   %rax
    33cf:	31 c0                	xor    %eax,%eax
    33d1:	e8 aa f1 ff ff       	call   2580 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    33d6:	48 83 c4 20          	add    $0x20,%rsp
    33da:	48 89 ea             	mov    %rbp,%rdx
    33dd:	4c 89 e6             	mov    %r12,%rsi
    33e0:	bf 01 00 00 00       	mov    $0x1,%edi
    33e5:	31 c0                	xor    %eax,%eax
    33e7:	e8 b4 f0 ff ff       	call   24a0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    33ec:	4c 89 f6             	mov    %r14,%rsi
    33ef:	48 89 ef             	mov    %rbp,%rdi
    33f2:	e8 b9 ef ff ff       	call   23b0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    33f7:	4c 39 3c 24          	cmp    %r15,(%rsp)
    33fb:	75 81                	jne    337e <main+0xd2e>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    33fd:	4c 89 f7             	mov    %r14,%rdi

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    3400:	45 31 e4             	xor    %r12d,%r12d
    3403:	4c 8d 35 44 50 00 00 	lea    0x5044(%rip),%r14        # 844e <_IO_stdin_used+0x44e>
  fclose(m1);
    340a:	e8 41 ef ff ff       	call   2350 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    340f:	48 8d 3d de 4f 00 00 	lea    0x4fde(%rip),%rdi        # 83f4 <_IO_stdin_used+0x3f4>
    3416:	e8 05 ef ff ff       	call   2320 <puts@plt>
    341b:	4c 8b 7c 24 30       	mov    0x30(%rsp),%r15
    3420:	44 89 e2             	mov    %r12d,%edx
    3423:	48 8d 35 fd 4f 00 00 	lea    0x4ffd(%rip),%rsi        # 8427 <_IO_stdin_used+0x427>
    342a:	31 c0                	xor    %eax,%eax
    342c:	89 14 24             	mov    %edx,(%rsp)
    342f:	4d 89 fc             	mov    %r15,%r12
    3432:	bf 01 00 00 00       	mov    $0x1,%edi
    3437:	e8 64 f0 ff ff       	call   24a0 <__printf_chk@plt>
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    343c:	8b 14 24             	mov    (%rsp),%edx
    343f:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    3444:	41 89 df             	mov    %ebx,%r15d
    3447:	44 8d 2c 12          	lea    (%rdx,%rdx,1),%r13d
    344b:	31 d2                	xor    %edx,%edx
    344d:	44 89 6c 24 08       	mov    %r13d,0x8(%rsp)
      int x = (k * threads_per_group) + d;
    3452:	8b 44 24 08          	mov    0x8(%rsp),%eax
    3456:	bf 01 00 00 00       	mov    $0x1,%edi
    345b:	89 54 24 20          	mov    %edx,0x20(%rsp)
    345f:	45 31 ed             	xor    %r13d,%r13d
    3462:	48 8d 35 c8 4f 00 00 	lea    0x4fc8(%rip),%rsi        # 8431 <_IO_stdin_used+0x431>
    3469:	8d 0c 02             	lea    (%rdx,%rax,1),%ecx
    346c:	31 c0                	xor    %eax,%eax
    346e:	e8 2d f0 ff ff       	call   24a0 <__printf_chk@plt>
    3473:	44 89 7c 24 18       	mov    %r15d,0x18(%rsp)
    3478:	44 89 ea             	mov    %r13d,%edx
    347b:	48 8d 35 c1 4f 00 00 	lea    0x4fc1(%rip),%rsi        # 8443 <_IO_stdin_used+0x443>
    3482:	31 c0                	xor    %eax,%eax
    3484:	4c 89 ed             	mov    %r13,%rbp
    3487:	bf 01 00 00 00       	mov    $0x1,%edi
    348c:	48 c1 e5 09          	shl    $0x9,%rbp
    3490:	45 31 ff             	xor    %r15d,%r15d
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3493:	31 db                	xor    %ebx,%ebx
    3495:	e8 06 f0 ff ff       	call   24a0 <__printf_chk@plt>
          char * mailbox_kind = calloc(100, sizeof(char));
    349a:	be 01 00 00 00       	mov    $0x1,%esi
    349f:	bf 64 00 00 00       	mov    $0x64,%edi
    34a4:	e8 47 ef ff ff       	call   23f0 <calloc@plt>
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    34a9:	49 8b 74 24 38       	mov    0x38(%r12),%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
    34ae:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    34b1:	48 8b 84 2e 70 01 00 00 	mov    0x170(%rsi,%rbp,1),%rax
    34b9:	4c 01 f8             	add    %r15,%rax
    34bc:	8b 50 30             	mov    0x30(%rax),%edx
    34bf:	83 fa 02             	cmp    $0x2,%edx
    34c2:	74 4c                	je     3510 <main+0xec0>
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    34c4:	83 fa 01             	cmp    $0x1,%edx
    34c7:	74 61                	je     352a <main+0xeda>
    34c9:	44 8b 40 34          	mov    0x34(%rax),%r8d
    34cd:	89 da                	mov    %ebx,%edx
    34cf:	4c 89 f6             	mov    %r14,%rsi
    34d2:	bf 01 00 00 00       	mov    $0x1,%edi
    34d7:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    34d9:	83 c3 01             	add    $0x1,%ebx
    34dc:	49 83 c7 38          	add    $0x38,%r15
    34e0:	e8 bb ef ff ff       	call   24a0 <__printf_chk@plt>
    34e5:	83 fb 04             	cmp    $0x4,%ebx
    34e8:	75 b0                	jne    349a <main+0xe4a>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    34ea:	49 83 c5 01          	add    $0x1,%r13
    34ee:	49 83 fd 03          	cmp    $0x3,%r13
    34f2:	75 84                	jne    3478 <main+0xe28>
    for (int d = 0 ; d < threads_per_group ; d++) {
    34f4:	8b 54 24 20          	mov    0x20(%rsp),%edx
    34f8:	44 8b 7c 24 18       	mov    0x18(%rsp),%r15d
    34fd:	49 81 c4 c8 00 00 00 	add    $0xc8,%r12
    3504:	85 d2                	test   %edx,%edx
    3506:	75 3c                	jne    3544 <main+0xef4>
    3508:	44 89 fa             	mov    %r15d,%edx
    350b:	e9 42 ff ff ff       	jmp    3452 <main+0xe02>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3510:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    351a:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    351d:	48 8b 84 2e 70 01 00 00 	mov    0x170(%rsi,%rbp,1),%rax
    3525:	4c 01 f8             	add    %r15,%rax
    3528:	eb 9f                	jmp    34c9 <main+0xe79>
    352a:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3530:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    3537:	48 8b 84 2e 70 01 00 00 	mov    0x170(%rsi,%rbp,1),%rax
    353f:	4c 01 f8             	add    %r15,%rax
    3542:	eb 85                	jmp    34c9 <main+0xe79>
  for (int k = 0 ; k < group_count ; k++) {
    3544:	44 89 fb             	mov    %r15d,%ebx
    3547:	89 d5                	mov    %edx,%ebp
    3549:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    354e:	8b 14 24             	mov    (%rsp),%edx
    3551:	49 81 c7 90 01 00 00 	add    $0x190,%r15
    3558:	85 d2                	test   %edx,%edx
    355a:	75 07                	jne    3563 <main+0xf13>
    355c:	89 ea                	mov    %ebp,%edx
    355e:	e9 c0 fe ff ff       	jmp    3423 <main+0xdd3>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3563:	41 89 d4             	mov    %edx,%r12d
    3566:	48 8d 35 fc 4e 00 00 	lea    0x4efc(%rip),%rsi        # 8469 <_IO_stdin_used+0x469>
    356d:	ba 05 00 00 00       	mov    $0x5,%edx
    3572:	31 c0                	xor    %eax,%eax
    3574:	bf 01 00 00 00       	mov    $0x1,%edi
    3579:	e8 22 ef ff ff       	call   24a0 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    357e:	be 08 00 00 00       	mov    $0x8,%esi
    3583:	bf 02 00 00 00       	mov    $0x2,%edi
    3588:	e8 63 ee ff ff       	call   23f0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    358d:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3592:	be 38 00 00 00       	mov    $0x38,%esi
    my_thread_data[0] = &thread_data[x]; 
    3597:	4c 8d bf e8 03 00 00 	lea    0x3e8(%rdi),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    359e:	48 89 78 08          	mov    %rdi,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    35a2:	4c 8d b7 c8 00 00 00 	lea    0xc8(%rdi),%r14
    thread_data[x].threads = my_thread_data;
    35a9:	48 89 87 00 04 00 00 	mov    %rax,0x400(%rdi)
    my_thread_data[0] = &thread_data[x]; 
    35b0:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    35b3:	48 8b 47 38          	mov    0x38(%rdi),%rax
    thread_data[x].thread_count = 2;
    35b7:	c7 87 10 04 00 00 02 00 00 00 	movl   $0x2,0x410(%rdi)
    thread_data[x].thread_index = 0;
    35c1:	c7 87 ec 03 00 00 00 00 00 00 	movl   $0x0,0x3ec(%rdi)
    thread_data[x].task_count = total_barrier_count;
    35cb:	c7 87 28 04 00 00 03 00 00 00 	movl   $0x3,0x428(%rdi)
    thread_data[n].tasks[0].scheduled = 1;
    35d5:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    35df:	48 8b 87 00 01 00 00 	mov    0x100(%rdi),%rax
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    35e6:	bf 08 00 00 00       	mov    $0x8,%edi
    thread_data[n].tasks[0].scheduled = 1;
    35eb:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    35f5:	e8 f6 ed ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    35fa:	be 38 00 00 00       	mov    $0x38,%esi
    35ff:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3604:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3607:	e8 e4 ed ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    360c:	be 38 00 00 00       	mov    $0x38,%esi
    3611:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3616:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3619:	e8 d2 ed ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    361e:	be 38 00 00 00       	mov    $0x38,%esi
    3623:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3628:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    362c:	e8 bf ed ff ff       	call   23f0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3631:	be 08 00 00 00       	mov    $0x8,%esi
    3636:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    363b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3640:	e8 ab ed ff ff       	call   23f0 <calloc@plt>


  int timer_threadi = group_count * thread_count;
  thread_data[timer_threadi].type = TIMER;
    3645:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    364a:	be 08 00 00 00       	mov    $0x8,%esi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    364f:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    3652:	48 8b 05 57 56 00 00 	mov    0x5657(%rip),%rax        # 8cb0 <_IO_stdin_used+0xcb0>
  thread_data[timer_threadi].type = TIMER;
    3659:	c7 87 2c 03 00 00 00 00 00 00 	movl   $0x0,0x32c(%rdi)
  thread_data[timer_threadi].task_count = total_barrier_count;
    3663:	48 89 87 60 03 00 00 	mov    %rax,0x360(%rdi)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    366a:	bf 08 00 00 00       	mov    $0x8,%edi
    366f:	e8 7c ed ff ff       	call   23f0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    3674:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    3679:	4c 89 78 28          	mov    %r15,0x28(%rax)
    367d:	48 8d 97 90 01 00 00 	lea    0x190(%rdi),%rdx
    3684:	48 8d 8f 20 03 00 00 	lea    0x320(%rdi),%rcx
    368b:	48 89 38             	mov    %rdi,(%rax)
    368e:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3692:	48 8d 97 58 02 00 00 	lea    0x258(%rdi),%rdx
    3699:	48 8d b7 b0 04 00 00 	lea    0x4b0(%rdi),%rsi
    36a0:	48 89 50 18          	mov    %rdx,0x18(%rax)
    36a4:	48 8d 97 78 05 00 00 	lea    0x578(%rdi),%rdx
    36ab:	48 89 48 20          	mov    %rcx,0x20(%rax)
    36af:	48 89 70 30          	mov    %rsi,0x30(%rax)
    36b3:	48 89 50 38          	mov    %rdx,0x38(%rax)
    36b7:	ba 04 00 00 00       	mov    $0x4,%edx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    36bc:	48 89 87 38 03 00 00 	mov    %rax,0x338(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    36c3:	4c 89 70 08          	mov    %r14,0x8(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    36c7:	48 8b 05 ea 55 00 00 	mov    0x55ea(%rip),%rax        # 8cb8 <_IO_stdin_used+0xcb8>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    36ce:	c7 87 50 03 00 00 04 00 00 00 	movl   $0x4,0x350(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    36d8:	48 89 87 48 03 00 00 	mov    %rax,0x348(%rdi)
    36df:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    36e1:	c7 87 24 03 00 00 00 00 00 00 	movl   $0x0,0x324(%rdi)
    36eb:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    36f0:	48 89 74 24 10       	mov    %rsi,0x10(%rsp)
    36f5:	48 8d 35 7c 4d 00 00 	lea    0x4d7c(%rip),%rsi        # 8478 <_IO_stdin_used+0x478>
    36fc:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    3701:	e8 9a ed ff ff       	call   24a0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3706:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    370b:	48 8d b5 e0 00 00 00 	lea    0xe0(%rbp),%rsi
  for (int k = 0 ; k < group_count ; k++) {
    3712:	31 ed                	xor    %ebp,%ebp
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3714:	48 8d 15 c5 0c 00 00 	lea    0xcc5(%rip),%rdx        # 43e0 <timer_thread>
    371b:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
    371f:	e8 9c ed ff ff       	call   24c0 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    3724:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    3729:	44 89 e6             	mov    %r12d,%esi
    372c:	48 89 d9             	mov    %rbx,%rcx
    372f:	4c 89 74 24 28       	mov    %r14,0x28(%rsp)
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3734:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    3739:	4c 89 e8             	mov    %r13,%rax
    373c:	41 89 ec             	mov    %ebp,%r12d
    373f:	41 b9 02 00 00 00    	mov    $0x2,%r9d
    3745:	4c 89 7c 24 18       	mov    %r15,0x18(%rsp)
    374a:	45 89 cf             	mov    %r9d,%r15d
    for (int d = 0 ; d < threads_per_group ; d++) {
    374d:	89 74 24 38          	mov    %esi,0x38(%rsp)
    3751:	43 8d 2c 24          	lea    (%r12,%r12,1),%ebp
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3755:	49 89 c6             	mov    %rax,%r14
    3758:	48 89 cb             	mov    %rcx,%rbx
    375b:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    3760:	49 89 d5             	mov    %rdx,%r13
    3763:	48 89 4c 24 48       	mov    %rcx,0x48(%rsp)
    3768:	48 89 54 24 50       	mov    %rdx,0x50(%rsp)
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    376d:	41 c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%r13)
    3775:	89 ea                	mov    %ebp,%edx
    3777:	44 89 e1             	mov    %r12d,%ecx
    377a:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    377c:	41 c7 45 44 01 00 00 00 	movl   $0x1,0x44(%r13)
    3784:	48 8d 35 6d 50 00 00 	lea    0x506d(%rip),%rsi        # 87f8 <_IO_stdin_used+0x7f8>
    378b:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    3790:	83 c5 01             	add    $0x1,%ebp
    3793:	e8 08 ed ff ff       	call   24a0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3798:	4c 89 e9             	mov    %r13,%rcx
    379b:	4c 89 f6             	mov    %r14,%rsi
    379e:	48 89 df             	mov    %rbx,%rdi
    37a1:	48 8d 15 98 29 00 00 	lea    0x2998(%rip),%rdx        # 6140 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    37a8:	49 81 c5 c8 00 00 00 	add    $0xc8,%r13
    37af:	48 83 c3 08          	add    $0x8,%rbx
    37b3:	49 83 c6 38          	add    $0x38,%r14
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    37b7:	e8 04 ed ff ff       	call   24c0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    37bc:	49 8b 55 e8          	mov    -0x18(%r13),%rdx
    37c0:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    37c4:	be 08 00 00 00       	mov    $0x8,%esi
    37c9:	e8 42 eb ff ff       	call   2310 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    37ce:	41 39 ef             	cmp    %ebp,%r15d
    37d1:	75 9a                	jne    376d <main+0x111d>
  for (int k = 0 ; k < group_count ; k++) {
    37d3:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    37d8:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    37dd:	41 83 c7 02          	add    $0x2,%r15d
    37e1:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
    37e6:	8b 74 24 38          	mov    0x38(%rsp),%esi
    37ea:	48 83 c1 10          	add    $0x10,%rcx
    37ee:	48 83 c0 70          	add    $0x70,%rax
    37f2:	48 81 c2 90 01 00 00 	add    $0x190,%rdx
    37f9:	45 85 e4             	test   %r12d,%r12d
    37fc:	75 08                	jne    3806 <main+0x11b6>
    37fe:	41 89 f4             	mov    %esi,%r12d
    3801:	e9 47 ff ff ff       	jmp    374d <main+0x10fd>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    3806:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    380b:	48 8b 05 ae 54 00 00 	mov    0x54ae(%rip),%rax        # 8cc0 <_IO_stdin_used+0xcc0>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3812:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    3817:	44 89 e5             	mov    %r12d,%ebp
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    381a:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    381f:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    3824:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
    3829:	41 c7 85 f4 03 00 00 02 00 00 00 	movl   $0x2,0x3f4(%r13)
    3834:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    thread_data[x].task_count = 0;
    3839:	49 89 85 28 04 00 00 	mov    %rax,0x428(%r13)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3840:	4c 8d 63 30          	lea    0x30(%rbx),%r12
    3844:	e8 a7 eb ff ff       	call   23f0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3849:	be 00 08 00 00       	mov    $0x800,%esi
    384e:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3850:	49 89 85 40 04 00 00 	mov    %rax,0x440(%r13)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3857:	e8 b4 ec ff ff       	call   2510 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    385c:	be 08 00 00 00       	mov    $0x8,%esi
    3861:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3866:	41 89 85 48 04 00 00 	mov    %eax,0x448(%r13)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    386d:	e8 7e eb ff ff       	call   23f0 <calloc@plt>
    3872:	ba 05 00 00 00       	mov    $0x5,%edx
    3877:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    387c:	41 c7 85 10 04 00 00 02 00 00 00 	movl   $0x2,0x410(%r13)
      my_thread_data[n] = &thread_data[n]; 
    3887:	4c 89 28             	mov    %r13,(%rax)
    388a:	48 8d 35 05 4c 00 00 	lea    0x4c05(%rip),%rsi        # 8496 <_IO_stdin_used+0x496>
    thread_data[x].threads = my_thread_data;
    3891:	49 89 85 00 04 00 00 	mov    %rax,0x400(%r13)
      my_thread_data[n] = &thread_data[n]; 
    3898:	4c 89 70 08          	mov    %r14,0x8(%rax)
    389c:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    389e:	41 c7 85 ec 03 00 00 05 00 00 00 	movl   $0x5,0x3ec(%r13)
    38a9:	e8 f2 eb ff ff       	call   24a0 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    38ae:	48 8b 34 24          	mov    (%rsp),%rsi
    38b2:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
    38b6:	4c 89 f9             	mov    %r15,%rcx
    38b9:	48 8d 15 90 20 00 00 	lea    0x2090(%rip),%rdx        # 5950 <io_thread>
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    38c0:	41 bf 06 00 00 00    	mov    $0x6,%r15d
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    38c6:	48 81 c6 18 01 00 00 	add    $0x118,%rsi
    38cd:	e8 ee eb ff ff       	call   24c0 <pthread_create@plt>
    38d2:	ba 06 00 00 00       	mov    $0x6,%edx
    38d7:	48 8d 35 cf 4b 00 00 	lea    0x4bcf(%rip),%rsi        # 84ad <_IO_stdin_used+0x4ad>
    38de:	31 c0                	xor    %eax,%eax
    38e0:	bf 01 00 00 00       	mov    $0x1,%edi
    38e5:	e8 b6 eb ff ff       	call   24a0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    38ea:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    38ef:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    38f4:	48 05 50 01 00 00    	add    $0x150,%rax
    38fa:	48 89 04 24          	mov    %rax,(%rsp)
    38fe:	89 e8                	mov    %ebp,%eax
    3900:	48 89 dd             	mov    %rbx,%rbp
    3903:	89 c3                	mov    %eax,%ebx
    3905:	44 89 fa             	mov    %r15d,%edx
    3908:	48 8d 35 b4 4b 00 00 	lea    0x4bb4(%rip),%rsi        # 84c3 <_IO_stdin_used+0x4c3>
    390f:	bf 01 00 00 00       	mov    $0x1,%edi
    3914:	31 c0                	xor    %eax,%eax
    3916:	e8 85 eb ff ff       	call   24a0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    391b:	be 08 00 00 00       	mov    $0x8,%esi
    3920:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3925:	48 8b 05 94 53 00 00 	mov    0x5394(%rip),%rax        # 8cc0 <_IO_stdin_used+0xcc0>
    thread_data[x].type = EXTERNAL;
    392c:	41 c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%r13)
    thread_data[x].task_count = 0;
    3934:	49 89 45 40          	mov    %rax,0x40(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3938:	e8 b3 ea ff ff       	call   23f0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    393d:	48 8b bc 24 88 00 00 00 	mov    0x88(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3945:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    394a:	41 c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3955:	49 89 45 50          	mov    %rax,0x50(%r13)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3959:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    395c:	bf 02 00 00 00       	mov    $0x2,%edi
    3961:	e8 8a ea ff ff       	call   23f0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3966:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    396b:	4c 89 e9             	mov    %r13,%rcx
    396e:	4c 89 e7             	mov    %r12,%rdi
    thread_data[x].threads = my_thread_data;
    3971:	49 89 45 18          	mov    %rax,0x18(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3975:	48 8d 15 54 09 00 00 	lea    0x954(%rip),%rdx        # 42d0 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    397c:	49 83 c4 08          	add    $0x8,%r12
    3980:	49 81 c5 c8 00 00 00 	add    $0xc8,%r13
      my_thread_data[n] = &thread_data[n]; 
    3987:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    398a:	48 8b 34 24          	mov    (%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    398e:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3992:	48 8b 05 07 53 00 00 	mov    0x5307(%rip),%rax        # 8ca0 <_IO_stdin_used+0xca0>
    thread_data[x].thread_index = x;
    3999:	45 89 bd 3c ff ff ff 	mov    %r15d,-0xc4(%r13)
    thread_data[x].thread_count = thread_count;
    39a0:	49 89 85 60 ff ff ff 	mov    %rax,-0xa0(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    39a7:	e8 14 eb ff ff       	call   24c0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    39ac:	48 83 04 24 38       	addq   $0x38,(%rsp)
    39b1:	48 83 84 24 88 00 00 00 10 	addq   $0x10,0x88(%rsp)
    39ba:	41 83 ff 06          	cmp    $0x6,%r15d
    39be:	75 0b                	jne    39cb <main+0x137b>
    39c0:	41 bf 07 00 00 00    	mov    $0x7,%r15d
    39c6:	e9 3a ff ff ff       	jmp    3905 <main+0x12b5>
    39cb:	89 d8                	mov    %ebx,%eax
    39cd:	48 89 eb             	mov    %rbp,%rbx
    39d0:	4c 8d 25 09 4b 00 00 	lea    0x4b09(%rip),%r12        # 84e0 <_IO_stdin_used+0x4e0>
    39d7:	89 c5                	mov    %eax,%ebp
    39d9:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    39de:	4c 8d 70 04          	lea    0x4(%rax),%r14
    39e2:	4c 8d a8 44 06 00 00 	lea    0x644(%rax),%r13
    39e9:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    39ed:	41 8b 16             	mov    (%r14),%edx
    39f0:	4c 89 e6             	mov    %r12,%rsi
    39f3:	bf 01 00 00 00       	mov    $0x1,%edi
    39f8:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    39fa:	49 81 c6 c8 00 00 00 	add    $0xc8,%r14
    3a01:	e8 9a ea ff ff       	call   24a0 <__printf_chk@plt>
    3a06:	4d 39 f5             	cmp    %r14,%r13
    3a09:	75 de                	jne    39e9 <main+0x1399>
    3a0b:	48 8d 3d e1 4a 00 00 	lea    0x4ae1(%rip),%rdi        # 84f3 <_IO_stdin_used+0x4f3>
    3a12:	45 31 f6             	xor    %r14d,%r14d
    3a15:	4c 8d ac 24 c0 00 00 00 	lea    0xc0(%rsp),%r13
    3a1d:	e8 fe e8 ff ff       	call   2320 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3a22:	4c 8d 25 e8 4a 00 00 	lea    0x4ae8(%rip),%r12        # 8511 <_IO_stdin_used+0x511>
    void * result; 
    pthread_join(thread[x], &result);
    3a29:	4a 8b 3c f3          	mov    (%rbx,%r14,8),%rdi
    3a2d:	4c 89 ee             	mov    %r13,%rsi
    3a30:	e8 1b eb ff ff       	call   2550 <pthread_join@plt>
    3a35:	44 89 f2             	mov    %r14d,%edx
    3a38:	4c 89 e6             	mov    %r12,%rsi
    3a3b:	bf 01 00 00 00       	mov    $0x1,%edi
    3a40:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3a42:	49 83 c6 01          	add    $0x1,%r14
    3a46:	e8 55 ea ff ff       	call   24a0 <__printf_chk@plt>
    3a4b:	49 83 fe 08          	cmp    $0x8,%r14
    3a4f:	75 d8                	jne    3a29 <main+0x13d9>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(200, sizeof(struct Data*)); 
    3a51:	be 08 00 00 00       	mov    $0x8,%esi
    3a56:	bf c8 00 00 00       	mov    $0xc8,%edi
  int datas2_size = 0; 
    3a5b:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(200, sizeof(struct Data*)); 
    3a5d:	e8 8e e9 ff ff       	call   23f0 <calloc@plt>
    3a62:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    3a67:	49 89 c6             	mov    %rax,%r14
    3a6a:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3a6c:	49 89 d1             	mov    %rdx,%r9
    3a6f:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3a72:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3a76:	45 85 d2             	test   %r10d,%r10d
    3a79:	7e 69                	jle    3ae4 <main+0x1494>
    3a7b:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3a7f:	4d 63 c2             	movslq %r10d,%r8
    3a82:	48 63 cb             	movslq %ebx,%rcx
    3a85:	49 c1 e0 09          	shl    $0x9,%r8
    3a89:	49 8d 34 ce          	lea    (%r14,%rcx,8),%rsi
    3a8d:	49 01 f8             	add    %rdi,%r8
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3a90:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3a97:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3a9e:	48 83 c6 40          	add    $0x40,%rsi
    3aa2:	f3 0f 7e 51 38       	movq   0x38(%rcx),%xmm2
    3aa7:	f3 0f 7e 49 70       	movq   0x70(%rcx),%xmm1
    3aac:	f3 0f 7e 81 a8 00 00 00 	movq   0xa8(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3ab4:	f3 0f 7e 19          	movq   (%rcx),%xmm3
    3ab8:	0f 16 51 40          	movhps 0x40(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3abc:	0f 16 49 78          	movhps 0x78(%rcx),%xmm1
    3ac0:	0f 16 81 b0 00 00 00 	movhps 0xb0(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3ac7:	0f 16 59 08          	movhps 0x8(%rcx),%xmm3
    3acb:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3acf:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3ad3:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3ad7:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3adb:	49 39 f8             	cmp    %rdi,%r8
    3ade:	75 b0                	jne    3a90 <main+0x1440>
    3ae0:	42 8d 1c d3          	lea    (%rbx,%r10,8),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    3ae4:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
    3aeb:	45 85 db             	test   %r11d,%r11d
    3aee:	75 08                	jne    3af8 <main+0x14a8>
    3af0:	41 89 eb             	mov    %ebp,%r11d
    3af3:	e9 7a ff ff ff       	jmp    3a72 <main+0x1422>
  for (int k = 0 ; k < group_count ; k++) {
    3af8:	83 c0 02             	add    $0x2,%eax
    3afb:	48 81 c2 90 01 00 00 	add    $0x190,%rdx
    3b02:	83 f8 04             	cmp    $0x4,%eax
    3b05:	0f 85 61 ff ff ff    	jne    3a6c <main+0x141c>
    3b0b:	48 8d 3d 13 4a 00 00 	lea    0x4a13(%rip),%rdi        # 8525 <_IO_stdin_used+0x525>
    3b12:	e8 09 e8 ff ff       	call   2320 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3b17:	48 8d 35 cb 48 00 00 	lea    0x48cb(%rip),%rsi        # 83e9 <_IO_stdin_used+0x3e9>
    3b1e:	48 8d 3d 18 4a 00 00 	lea    0x4a18(%rip),%rdi        # 853d <_IO_stdin_used+0x53d>
    3b25:	e8 b6 e9 ff ff       	call   24e0 <fopen@plt>
    3b2a:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas2_size; x++) {
    3b2d:	85 db                	test   %ebx,%ebx
    3b2f:	0f 8e 93 00 00 00    	jle    3bc8 <main+0x1578>
    3b35:	48 63 db             	movslq %ebx,%rbx
    3b38:	4c 8d 2d cd 48 00 00 	lea    0x48cd(%rip),%r13        # 840c <_IO_stdin_used+0x40c>
    3b3f:	4c 8d 25 de 48 00 00 	lea    0x48de(%rip),%r12        # 8424 <_IO_stdin_used+0x424>
    3b46:	49 8d 2c de          	lea    (%r14,%rbx,8),%rbp
    char * c = calloc(250, sizeof(char));
    3b4a:	be 01 00 00 00       	mov    $0x1,%esi
    3b4f:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3b54:	49 83 c6 08          	add    $0x8,%r14
    char * c = calloc(250, sizeof(char));
    3b58:	e8 93 e8 ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3b5d:	48 83 ec 08          	sub    $0x8,%rsp
    3b61:	4c 89 e9             	mov    %r13,%rcx
    3b64:	be 01 00 00 00       	mov    $0x1,%esi
    3b69:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d %d %d %d %d\n", datas[x]->id, datas[x]->kind, datas[x]->a, datas[x]->b, datas[x]->c);
    3b6c:	49 8b 46 f8          	mov    -0x8(%r14),%rax
    3b70:	48 89 df             	mov    %rbx,%rdi
    3b73:	8b 90 24 03 00 00    	mov    0x324(%rax),%edx
    3b79:	44 8b 88 18 03 00 00 	mov    0x318(%rax),%r9d
    3b80:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3b87:	52                   	push   %rdx
    3b88:	8b 90 20 03 00 00    	mov    0x320(%rax),%edx
    3b8e:	52                   	push   %rdx
    3b8f:	8b 80 1c 03 00 00    	mov    0x31c(%rax),%eax
    3b95:	ba fa 00 00 00       	mov    $0xfa,%edx
    3b9a:	50                   	push   %rax
    3b9b:	31 c0                	xor    %eax,%eax
    3b9d:	e8 de e9 ff ff       	call   2580 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3ba2:	48 83 c4 20          	add    $0x20,%rsp
    3ba6:	48 89 da             	mov    %rbx,%rdx
    3ba9:	4c 89 e6             	mov    %r12,%rsi
    3bac:	bf 01 00 00 00       	mov    $0x1,%edi
    3bb1:	31 c0                	xor    %eax,%eax
    3bb3:	e8 e8 e8 ff ff       	call   24a0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3bb8:	4c 89 fe             	mov    %r15,%rsi
    3bbb:	48 89 df             	mov    %rbx,%rdi
    3bbe:	e8 ed e7 ff ff       	call   23b0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3bc3:	49 39 ee             	cmp    %rbp,%r14
    3bc6:	75 82                	jne    3b4a <main+0x14fa>
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
    3bc8:	4c 89 ff             	mov    %r15,%rdi
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    3bcb:	45 31 ed             	xor    %r13d,%r13d
  long sents = 0;
    3bce:	45 31 e4             	xor    %r12d,%r12d
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3bd1:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  fclose(m2);
    3bdb:	e8 70 e7 ff ff       	call   2350 <fclose@plt>
    3be0:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
  long sends = 0;
    3be5:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  long ingests = 0;
    3bee:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
  long total = 0;
    3bf7:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  int datas2_size = 0; 
    3c00:	48 8b bc 24 98 00 00 00 	mov    0x98(%rsp),%rdi
    3c08:	89 44 24 08          	mov    %eax,0x8(%rsp)
    3c0c:	83 c0 02             	add    $0x2,%eax
    3c0f:	89 44 24 40          	mov    %eax,0x40(%rsp)
    3c13:	4c 8b bc 24 90 00 00 00 	mov    0x90(%rsp),%r15
    3c1b:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
      int x = (k * threads_per_group) + d;
    3c20:	8b 7c 24 08          	mov    0x8(%rsp),%edi
    3c24:	89 f8                	mov    %edi,%eax
    3c26:	83 c7 01             	add    $0x1,%edi
        other = abs(x - 1) % total_threads;
    3c29:	8d 50 02             	lea    0x2(%rax),%edx
    3c2c:	89 7c 24 08          	mov    %edi,0x8(%rsp)
    3c30:	83 e7 01             	and    $0x1,%edi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3c33:	bf 0a 00 00 00       	mov    $0xa,%edi
    3c38:	0f 44 c2             	cmove  %edx,%eax
    3c3b:	48 63 d8             	movslq %eax,%rbx
    3c3e:	e8 bd e6 ff ff       	call   2300 <putchar@plt>
    3c43:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3c48:	bf 01 00 00 00       	mov    $0x1,%edi
    3c4d:	48 8d 35 f2 48 00 00 	lea    0x48f2(%rip),%rsi        # 8546 <_IO_stdin_used+0x546>
    3c54:	48 8b 10             	mov    (%rax),%rdx
    3c57:	31 c0                	xor    %eax,%eax
    3c59:	e8 42 e8 ff ff       	call   24a0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3c5e:	41 8b 57 40          	mov    0x40(%r15),%edx
    3c62:	85 d2                	test   %edx,%edx
    3c64:	0f 8e a6 04 00 00    	jle    4110 <main+0x1ac0>
    3c6a:	48 63 ca             	movslq %edx,%rcx
    3c6d:	49 8b 47 38          	mov    0x38(%r15),%rax
      long v = 0;
    3c71:	31 d2                	xor    %edx,%edx
    3c73:	48 c1 e1 09          	shl    $0x9,%rcx
    3c77:	48 01 c1             	add    %rax,%rcx
    3c7a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    3c80:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3c87:	48 05 00 02 00 00    	add    $0x200,%rax
    3c8d:	48 39 c8             	cmp    %rcx,%rax
    3c90:	75 ee                	jne    3c80 <main+0x1630>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3c92:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    3c97:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    3c9b:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3c9f:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3ca3:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3ca7:	85 c9                	test   %ecx,%ecx
    3ca9:	7e 27                	jle    3cd2 <main+0x1682>
    3cab:	48 8b 40 38          	mov    0x38(%rax),%rax
    3caf:	48 c1 e1 09          	shl    $0x9,%rcx
    3cb3:	48 01 c1             	add    %rax,%rcx
    3cb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3cc0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3cc7:	48 05 00 02 00 00    	add    $0x200,%rax
    3ccd:	48 39 c8             	cmp    %rcx,%rax
    3cd0:	75 ee                	jne    3cc0 <main+0x1670>
    3cd2:	48 8d 35 82 48 00 00 	lea    0x4882(%rip),%rsi        # 855b <_IO_stdin_used+0x55b>
    3cd9:	bf 01 00 00 00       	mov    $0x1,%edi
    3cde:	31 c0                	xor    %eax,%eax
    3ce0:	e8 bb e7 ff ff       	call   24a0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3ce5:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3cea:	bf 01 00 00 00       	mov    $0x1,%edi
    3cef:	48 8d 35 32 4b 00 00 	lea    0x4b32(%rip),%rsi        # 8828 <_IO_stdin_used+0x828>
    3cf6:	48 8b 08             	mov    (%rax),%rcx
    3cf9:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3d03:	48 f7 e9             	imul   %rcx
    3d06:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3d0a:	31 c0                	xor    %eax,%eax
    3d0c:	48 d1 fa             	sar    %rdx
    3d0f:	48 29 ca             	sub    %rcx,%rdx
    3d12:	e8 89 e7 ff ff       	call   24a0 <__printf_chk@plt>
    3d17:	bf 0a 00 00 00       	mov    $0xa,%edi
    3d1c:	e8 df e5 ff ff       	call   2300 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3d21:	45 8b 57 40          	mov    0x40(%r15),%r10d
    3d25:	45 85 d2             	test   %r10d,%r10d
    3d28:	0f 8e ea 00 00 00    	jle    3e18 <main+0x17c8>
        total += thread_data[x].tasks[n].n;
    3d2e:	49 8b 57 38          	mov    0x38(%r15),%rdx
    3d32:	4c 8b 44 24 28       	mov    0x28(%rsp),%r8
    3d37:	31 c9                	xor    %ecx,%ecx
    3d39:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3d3e:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3d43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3d48:	49 89 ce             	mov    %rcx,%r14
    3d4b:	89 0c 24             	mov    %ecx,(%rsp)
        sends += thread_data[x].tasks[n].sends;
    3d4e:	31 db                	xor    %ebx,%ebx
    3d50:	49 c1 e6 09          	shl    $0x9,%r14
    3d54:	48 89 4c 24 28       	mov    %rcx,0x28(%rsp)
        total += thread_data[x].tasks[n].n;
    3d59:	4c 01 f2             	add    %r14,%rdx
    3d5c:	4c 03 82 08 01 00 00 	add    0x108(%rdx),%r8
        ingests += thread_data[x].tasks[n].ingest_count;
    3d63:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
        sends += thread_data[x].tasks[n].sends;
    3d6a:	48 03 ba 78 01 00 00 	add    0x178(%rdx),%rdi
    3d71:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    3d76:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    3d7b:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
    3d80:	8b 0c 24             	mov    (%rsp),%ecx
    3d83:	8b 54 24 08          	mov    0x8(%rsp),%edx
    3d87:	41 89 d8             	mov    %ebx,%r8d
    3d8a:	bf 01 00 00 00       	mov    $0x1,%edi
    3d8f:	48 8d 35 d2 47 00 00 	lea    0x47d2(%rip),%rsi        # 8568 <_IO_stdin_used+0x568>
    3d96:	31 c0                	xor    %eax,%eax
    3d98:	e8 03 e7 ff ff       	call   24a0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3d9d:	49 8b 57 38          	mov    0x38(%r15),%rdx
    3da1:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    3da9:	48 29 d8             	sub    %rbx,%rax
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3dac:	48 83 c3 01          	add    $0x1,%rbx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3db0:	4a 8b 8c 32 70 01 00 00 	mov    0x170(%rdx,%r14,1),%rcx
    3db8:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    3dbc:	48 8b 08             	mov    (%rax),%rcx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3dbf:	48 8b 40 08          	mov    0x8(%rax),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3dc3:	4c 8b 89 08 03 00 00 	mov    0x308(%rcx),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3dca:	4c 8b 91 10 03 00 00 	mov    0x310(%rcx),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3dd1:	4d 01 e1             	add    %r12,%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3dd4:	4d 01 ea             	add    %r13,%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3dd7:	4c 03 88 08 03 00 00 	add    0x308(%rax),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3dde:	4c 03 90 10 03 00 00 	add    0x310(%rax),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3de5:	4d 89 cc             	mov    %r9,%r12
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3de8:	4d 89 d5             	mov    %r10,%r13
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3deb:	48 83 fb 04          	cmp    $0x4,%rbx
    3def:	75 8f                	jne    3d80 <main+0x1730>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3df1:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3df6:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    3dfb:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3e00:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3e05:	48 83 c1 01          	add    $0x1,%rcx
    3e09:	41 39 4f 40          	cmp    %ecx,0x40(%r15)
    3e0d:	0f 8f 35 ff ff ff    	jg     3d48 <main+0x16f8>
    3e13:	4c 89 44 24 28       	mov    %r8,0x28(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3e18:	45 31 f6             	xor    %r14d,%r14d
    3e1b:	49 83 bf a0 00 00 00 00 	cmpq   $0x0,0xa0(%r15)
    3e23:	48 8d 1d 1e 4a 00 00 	lea    0x4a1e(%rip),%rbx        # 8848 <_IO_stdin_used+0x848>
    3e2a:	7e 5c                	jle    3e88 <main+0x1838>
    3e2c:	0f 1f 40 00          	nopl   0x0(%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3e30:	49 8b 87 90 00 00 00 	mov    0x90(%r15),%rax
    3e37:	4b 8d 14 b6          	lea    (%r14,%r14,4),%rdx
    3e3b:	48 83 ec 08          	sub    $0x8,%rsp
    3e3f:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3e44:	49 83 c6 01          	add    $0x1,%r14
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3e48:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3e4c:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3e50:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3e54:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3e57:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3e5b:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3e5e:	48 f7 e5             	mul    %rbp
    3e61:	8b 49 20             	mov    0x20(%rcx),%ecx
    3e64:	56                   	push   %rsi
    3e65:	31 c0                	xor    %eax,%eax
    3e67:	48 89 de             	mov    %rbx,%rsi
    3e6a:	48 c1 ea 12          	shr    $0x12,%rdx
    3e6e:	49 89 d1             	mov    %rdx,%r9
    3e71:	ba 02 00 00 00       	mov    $0x2,%edx
    3e76:	e8 25 e6 ff ff       	call   24a0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3e7b:	41 58                	pop    %r8
    3e7d:	41 59                	pop    %r9
    3e7f:	4d 39 b7 a0 00 00 00 	cmp    %r14,0xa0(%r15)
    3e86:	7f a8                	jg     3e30 <main+0x17e0>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3e88:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    3e8f:	85 c9                	test   %ecx,%ecx
    3e91:	0f 8e fe 00 00 00    	jle    3f95 <main+0x1945>
    3e97:	4c 89 64 24 48       	mov    %r12,0x48(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3e9c:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    3ea0:	31 db                	xor    %ebx,%ebx
    3ea2:	4c 89 6c 24 50       	mov    %r13,0x50(%rsp)
    3ea7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3eb0:	49 8b 04 d9          	mov    (%r9,%rbx,8),%rax
    3eb4:	41 89 dc             	mov    %ebx,%r12d
    3eb7:	4c 8d 2c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r13
    3ebf:	8b 30                	mov    (%rax),%esi
    3ec1:	85 f6                	test   %esi,%esi
    3ec3:	0f 8e b6 00 00 00    	jle    3f7f <main+0x192f>
    3ec9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3ece:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3ed2:	31 ff                	xor    %edi,%edi
    3ed4:	0f 1f 40 00          	nopl   0x0(%rax)
    3ed8:	48 89 fb             	mov    %rdi,%rbx
    3edb:	45 31 f6             	xor    %r14d,%r14d
    3ede:	48 c1 e3 08          	shl    $0x8,%rbx
    3ee2:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    3ee6:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    3eec:	85 d2                	test   %edx,%edx
    3eee:	7e 77                	jle    3f67 <main+0x1917>
    3ef0:	48 89 3c 24          	mov    %rdi,(%rsp)
    3ef4:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3ef8:	4c 89 f1             	mov    %r14,%rcx
    3efb:	48 83 ec 08          	sub    $0x8,%rsp
    3eff:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3f04:	49 83 c6 01          	add    $0x1,%r14
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3f08:	48 c1 e1 05          	shl    $0x5,%rcx
    3f0c:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3f13:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3f17:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3f1b:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3f1e:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3f22:	4c 2b 01             	sub    (%rcx),%r8
    3f25:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3f26:	48 f7 e5             	mul    %rbp
    3f29:	44 89 e1             	mov    %r12d,%ecx
    3f2c:	48 8d 35 65 49 00 00 	lea    0x4965(%rip),%rsi        # 8898 <_IO_stdin_used+0x898>
    3f33:	31 c0                	xor    %eax,%eax
    3f35:	48 c1 ea 12          	shr    $0x12,%rdx
    3f39:	49 89 d1             	mov    %rdx,%r9
    3f3c:	ba 02 00 00 00       	mov    $0x2,%edx
    3f41:	e8 5a e5 ff ff       	call   24a0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3f46:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    3f4a:	5e                   	pop    %rsi
    3f4b:	5f                   	pop    %rdi
    3f4c:	4b 8b 14 29          	mov    (%r9,%r13,1),%rdx
    3f50:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    3f54:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    3f58:	44 39 b0 94 00 00 00 	cmp    %r14d,0x94(%rax)
    3f5f:	7f 97                	jg     3ef8 <main+0x18a8>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3f61:	48 8b 3c 24          	mov    (%rsp),%rdi
    3f65:	8b 32                	mov    (%rdx),%esi
    3f67:	48 83 c7 01          	add    $0x1,%rdi
    3f6b:	39 fe                	cmp    %edi,%esi
    3f6d:	0f 8f 65 ff ff ff    	jg     3ed8 <main+0x1888>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3f73:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    3f78:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    3f7f:	48 83 c3 01          	add    $0x1,%rbx
    3f83:	39 d9                	cmp    %ebx,%ecx
    3f85:	0f 8f 25 ff ff ff    	jg     3eb0 <main+0x1860>
    3f8b:	4c 8b 64 24 48       	mov    0x48(%rsp),%r12
    3f90:	4c 8b 6c 24 50       	mov    0x50(%rsp),%r13
    for (int d = 0 ; d < threads_per_group ; d++) {
    3f95:	48 83 44 24 38 18    	addq   $0x18,0x38(%rsp)
    3f9b:	8b 7c 24 40          	mov    0x40(%rsp),%edi
    3f9f:	49 81 c7 c8 00 00 00 	add    $0xc8,%r15
    3fa6:	39 7c 24 08          	cmp    %edi,0x8(%rsp)
    3faa:	0f 85 70 fc ff ff    	jne    3c20 <main+0x15d0>
  for (int k = 0 ; k < group_count ; k++) {
    3fb0:	48 83 84 24 98 00 00 00 30 	addq   $0x30,0x98(%rsp)
    3fb9:	b8 01 00 00 00       	mov    $0x1,%eax
    3fbe:	48 81 84 24 90 00 00 00 90 01 00 00 	addq   $0x190,0x90(%rsp)
    3fca:	83 7c 24 08 03       	cmpl   $0x3,0x8(%rsp)
    3fcf:	0f 85 2b fc ff ff    	jne    3c00 <main+0x15b0>
    3fd5:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    3fda:	48 8d 35 97 45 00 00 	lea    0x4597(%rip),%rsi        # 8578 <_IO_stdin_used+0x578>
    3fe1:	bf 01 00 00 00       	mov    $0x1,%edi
    3fe6:	31 c0                	xor    %eax,%eax
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3fe8:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    3ff2:	4c 89 fa             	mov    %r15,%rdx
    3ff5:	e8 a6 e4 ff ff       	call   24a0 <__printf_chk@plt>
    3ffa:	bf 0a 00 00 00       	mov    $0xa,%edi
    3fff:	e8 fc e2 ff ff       	call   2300 <putchar@plt>
    4004:	48 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%rdi
    400c:	48 8d 35 dd 48 00 00 	lea    0x48dd(%rip),%rsi        # 88f0 <_IO_stdin_used+0x8f0>
    4013:	31 c0                	xor    %eax,%eax
    4015:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    4019:	bf 01 00 00 00       	mov    $0x1,%edi
    401e:	e8 7d e4 ff ff       	call   24a0 <__printf_chk@plt>
    4023:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    4028:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    402d:	48 8d 35 e4 48 00 00 	lea    0x48e4(%rip),%rsi        # 8918 <_IO_stdin_used+0x918>
    4034:	48 f7 eb             	imul   %rbx
    4037:	48 c1 ff 3f          	sar    $0x3f,%rdi
    403b:	31 c0                	xor    %eax,%eax
    403d:	48 d1 fa             	sar    %rdx
    4040:	48 29 fa             	sub    %rdi,%rdx
    4043:	bf 01 00 00 00       	mov    $0x1,%edi
    4048:	e8 53 e4 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    404d:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4052:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    4057:	48 8d 35 ea 48 00 00 	lea    0x48ea(%rip),%rsi        # 8948 <_IO_stdin_used+0x948>
    405e:	48 f7 eb             	imul   %rbx
    4061:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4065:	31 c0                	xor    %eax,%eax
    4067:	48 d1 fa             	sar    %rdx
    406a:	48 29 fa             	sub    %rdi,%rdx
    406d:	bf 01 00 00 00       	mov    $0x1,%edi
    4072:	e8 29 e4 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    4077:	4c 89 f8             	mov    %r15,%rax
    407a:	4c 89 ff             	mov    %r15,%rdi
    407d:	48 8d 35 f4 48 00 00 	lea    0x48f4(%rip),%rsi        # 8978 <_IO_stdin_used+0x978>
    4084:	48 f7 eb             	imul   %rbx
    4087:	48 c1 ff 3f          	sar    $0x3f,%rdi
    408b:	31 c0                	xor    %eax,%eax
    408d:	48 d1 fa             	sar    %rdx
    4090:	48 29 fa             	sub    %rdi,%rdx
    4093:	bf 01 00 00 00       	mov    $0x1,%edi
    4098:	e8 03 e4 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    409d:	4c 89 e0             	mov    %r12,%rax
    40a0:	bf 01 00 00 00       	mov    $0x1,%edi
    40a5:	48 8d 35 e0 44 00 00 	lea    0x44e0(%rip),%rsi        # 858c <_IO_stdin_used+0x58c>
    40ac:	48 f7 eb             	imul   %rbx
    40af:	4c 89 e0             	mov    %r12,%rax
    40b2:	48 c1 f8 3f          	sar    $0x3f,%rax
    40b6:	48 d1 fa             	sar    %rdx
    40b9:	48 29 c2             	sub    %rax,%rdx
    40bc:	31 c0                	xor    %eax,%eax
    40be:	e8 dd e3 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    40c3:	4c 89 e8             	mov    %r13,%rax
    40c6:	bf 01 00 00 00       	mov    $0x1,%edi
    40cb:	48 8d 35 cb 44 00 00 	lea    0x44cb(%rip),%rsi        # 859d <_IO_stdin_used+0x59d>
    40d2:	48 f7 eb             	imul   %rbx
    40d5:	4c 89 e8             	mov    %r13,%rax
    40d8:	48 c1 f8 3f          	sar    $0x3f,%rax
    40dc:	48 d1 fa             	sar    %rdx
    40df:	48 29 c2             	sub    %rax,%rdx
    40e2:	31 c0                	xor    %eax,%eax
    40e4:	e8 b7 e3 ff ff       	call   24a0 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    40e9:	48 8b 84 24 c8 00 00 00 	mov    0xc8(%rsp),%rax
    40f1:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    40fa:	75 25                	jne    4121 <main+0x1ad1>
    40fc:	48 81 c4 d8 00 00 00 	add    $0xd8,%rsp
    4103:	31 c0                	xor    %eax,%eax
    4105:	5b                   	pop    %rbx
    4106:	5d                   	pop    %rbp
    4107:	41 5c                	pop    %r12
    4109:	41 5d                	pop    %r13
    410b:	41 5e                	pop    %r14
    410d:	41 5f                	pop    %r15
    410f:	c3                   	ret
      long v = 0;
    4110:	31 d2                	xor    %edx,%edx
    4112:	e9 7b fb ff ff       	jmp    3c92 <main+0x1642>
            exit(1);
    4117:	bf 01 00 00 00       	mov    $0x1,%edi
    411c:	e8 df e3 ff ff       	call   2500 <exit@plt>
}
    4121:	e8 4a e2 ff ff       	call   2370 <__stack_chk_fail@plt>
    4126:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004130 <_start>:
    4130:	f3 0f 1e fa          	endbr64
    4134:	31 ed                	xor    %ebp,%ebp
    4136:	49 89 d1             	mov    %rdx,%r9
    4139:	5e                   	pop    %rsi
    413a:	48 89 e2             	mov    %rsp,%rdx
    413d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4141:	50                   	push   %rax
    4142:	54                   	push   %rsp
    4143:	45 31 c0             	xor    %r8d,%r8d
    4146:	31 c9                	xor    %ecx,%ecx
    4148:	48 8d 3d 01 e5 ff ff 	lea    -0x1aff(%rip),%rdi        # 2650 <main>
    414f:	ff 15 83 6e 00 00    	call   *0x6e83(%rip)        # afd8 <__libc_start_main@GLIBC_2.34>
    4155:	f4                   	hlt
    4156:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004160 <deregister_tm_clones>:
    4160:	48 8d 3d b9 6e 00 00 	lea    0x6eb9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4167:	48 8d 05 b2 6e 00 00 	lea    0x6eb2(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    416e:	48 39 f8             	cmp    %rdi,%rax
    4171:	74 15                	je     4188 <deregister_tm_clones+0x28>
    4173:	48 8b 05 66 6e 00 00 	mov    0x6e66(%rip),%rax        # afe0 <_ITM_deregisterTMCloneTable@Base>
    417a:	48 85 c0             	test   %rax,%rax
    417d:	74 09                	je     4188 <deregister_tm_clones+0x28>
    417f:	ff e0                	jmp    *%rax
    4181:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4188:	c3                   	ret
    4189:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004190 <register_tm_clones>:
    4190:	48 8d 3d 89 6e 00 00 	lea    0x6e89(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4197:	48 8d 35 82 6e 00 00 	lea    0x6e82(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    419e:	48 29 fe             	sub    %rdi,%rsi
    41a1:	48 89 f0             	mov    %rsi,%rax
    41a4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    41a8:	48 c1 f8 03          	sar    $0x3,%rax
    41ac:	48 01 c6             	add    %rax,%rsi
    41af:	48 d1 fe             	sar    %rsi
    41b2:	74 14                	je     41c8 <register_tm_clones+0x38>
    41b4:	48 8b 05 35 6e 00 00 	mov    0x6e35(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    41bb:	48 85 c0             	test   %rax,%rax
    41be:	74 08                	je     41c8 <register_tm_clones+0x38>
    41c0:	ff e0                	jmp    *%rax
    41c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    41c8:	c3                   	ret
    41c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000041d0 <__do_global_dtors_aux>:
    41d0:	f3 0f 1e fa          	endbr64
    41d4:	80 3d 4d 6e 00 00 00 	cmpb   $0x0,0x6e4d(%rip)        # b028 <completed.0>
    41db:	75 2b                	jne    4208 <__do_global_dtors_aux+0x38>
    41dd:	55                   	push   %rbp
    41de:	48 83 3d 12 6e 00 00 00 	cmpq   $0x0,0x6e12(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    41e6:	48 89 e5             	mov    %rsp,%rbp
    41e9:	74 0c                	je     41f7 <__do_global_dtors_aux+0x27>
    41eb:	48 8b 3d 16 6e 00 00 	mov    0x6e16(%rip),%rdi        # b008 <__dso_handle>
    41f2:	e8 e9 e0 ff ff       	call   22e0 <__cxa_finalize@plt>
    41f7:	e8 64 ff ff ff       	call   4160 <deregister_tm_clones>
    41fc:	c6 05 25 6e 00 00 01 	movb   $0x1,0x6e25(%rip)        # b028 <completed.0>
    4203:	5d                   	pop    %rbp
    4204:	c3                   	ret
    4205:	0f 1f 00             	nopl   (%rax)
    4208:	c3                   	ret
    4209:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004210 <frame_dummy>:
    4210:	f3 0f 1e fa          	endbr64
    4214:	e9 77 ff ff ff       	jmp    4190 <register_tm_clones>
    4219:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004220 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    4220:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    4224:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    422b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    422f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    4237:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    423b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    423f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4246:	48 85 c9             	test   %rcx,%rcx
    4249:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4250:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4254:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    4258:	31 c0                	xor    %eax,%eax
    425a:	c3                   	ret
    425b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004260 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    4260:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    4264:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    426b:	85 c9                	test   %ecx,%ecx
    426d:	7e 4f                	jle    42be <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    426f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    4276:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    427d:	48 c1 e1 09          	shl    $0x9,%rcx
    4281:	48 8b 50 18          	mov    0x18(%rax),%rdx
    4285:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    4289:	48 8b 70 38          	mov    0x38(%rax),%rsi
    428d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    428f:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4293:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4298:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    42a0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    42a8:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    42b3:	48 05 00 02 00 00    	add    $0x200,%rax
    42b9:	48 39 c1             	cmp    %rax,%rcx
    42bc:	75 da                	jne    4298 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    42be:	0f ae f8             	sfence
}
    42c1:	31 c0                	xor    %eax,%eax
    42c3:	c3                   	ret
    42c4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    42cf:	90                   	nop

00000000000042d0 <external_thread>:
void * external_thread(void *arg) {
    42d0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    42d4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    42d8:	0f 85 fb 00 00 00    	jne    43d9 <external_thread+0x109>
void * external_thread(void *arg) {
    42de:	41 57                	push   %r15
    42e0:	49 89 ff             	mov    %rdi,%r15
    42e3:	41 56                	push   %r14
    42e5:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    42e7:	4c 8d 2d 16 3d 00 00 	lea    0x3d16(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    42ee:	41 54                	push   %r12
    42f0:	55                   	push   %rbp
    42f1:	53                   	push   %rbx
    42f2:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    42f6:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    42fc:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    4300:	85 c9                	test   %ecx,%ecx
    4302:	7e 6e                	jle    4372 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4304:	45 31 e4             	xor    %r12d,%r12d
    4307:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4310:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    4318:	31 db                	xor    %ebx,%ebx
    431a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    431e:	48 8b 06             	mov    (%rsi),%rax
    4321:	8b 10                	mov    (%rax),%edx
    4323:	85 d2                	test   %edx,%edx
    4325:	7e 2a                	jle    4351 <external_thread+0x81>
    4327:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    432b:	48 89 dd             	mov    %rbx,%rbp
    432e:	48 c1 e5 08          	shl    $0x8,%rbp
    4332:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4336:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    433d:	45 85 c0             	test   %r8d,%r8d
    4340:	74 36                	je     4378 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4342:	48 83 c3 01          	add    $0x1,%rbx
    4346:	39 da                	cmp    %ebx,%edx
    4348:	7f e1                	jg     432b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    434a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    4351:	49 83 c4 01          	add    $0x1,%r12
    4355:	44 39 e1             	cmp    %r12d,%ecx
    4358:	7f b6                	jg     4310 <external_thread+0x40>
  while (data->running == 1) {
    435a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    435f:	74 9f                	je     4300 <external_thread+0x30>
}
    4361:	48 83 c4 08          	add    $0x8,%rsp
    4365:	31 c0                	xor    %eax,%eax
    4367:	5b                   	pop    %rbx
    4368:	5d                   	pop    %rbp
    4369:	41 5c                	pop    %r12
    436b:	41 5d                	pop    %r13
    436d:	41 5e                	pop    %r14
    436f:	41 5f                	pop    %r15
    4371:	c3                   	ret
  while (data->running == 1) {
    4372:	eb fe                	jmp    4372 <external_thread+0xa2>
    4374:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    4378:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    437b:	48 8b 06             	mov    (%rsi),%rax
    437e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4382:	48 01 ef             	add    %rbp,%rdi
    4385:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    438c:	48 c1 e6 05          	shl    $0x5,%rsi
    4390:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4397:	bf 04 00 00 00       	mov    $0x4,%edi
    439c:	e8 9f df ff ff       	call   2340 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    43a1:	49 8b 47 50          	mov    0x50(%r15),%rax
    43a5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    43a9:	48 8b 40 08          	mov    0x8(%rax),%rax
    43ad:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    43b8:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    43bb:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    43bf:	48 83 c3 01          	add    $0x1,%rbx
    43c3:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    43c7:	48 8b 06             	mov    (%rsi),%rax
    43ca:	8b 10                	mov    (%rax),%edx
    43cc:	39 da                	cmp    %ebx,%edx
    43ce:	0f 8f 53 ff ff ff    	jg     4327 <external_thread+0x57>
    43d4:	e9 71 ff ff ff       	jmp    434a <external_thread+0x7a>
}
    43d9:	31 c0                	xor    %eax,%eax
    43db:	c3                   	ret
    43dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000043e0 <timer_thread>:
void* timer_thread(void *arg) {
    43e0:	f3 0f 1e fa          	endbr64
    43e4:	41 57                	push   %r15
    43e6:	48 8d 35 23 3c 00 00 	lea    0x3c23(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    43ed:	41 56                	push   %r14
    43ef:	41 55                	push   %r13
    43f1:	41 54                	push   %r12
    43f3:	55                   	push   %rbp
    43f4:	48 89 fd             	mov    %rdi,%rbp
    43f7:	53                   	push   %rbx
    43f8:	48 83 ec 58          	sub    $0x58,%rsp
    43fc:	8b 57 04             	mov    0x4(%rdi),%edx
    43ff:	bf 01 00 00 00       	mov    $0x1,%edi
    4404:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    440d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    4412:	31 c0                	xor    %eax,%eax
    4414:	e8 87 e0 ff ff       	call   24a0 <__printf_chk@plt>
  struct timespec preempt = {
    4419:	66 0f 6f 05 6f 47 00 00 	movdqa 0x476f(%rip),%xmm0        # 8b90 <_IO_stdin_used+0xb90>
    4421:	ba 88 13 00 00       	mov    $0x1388,%edx
    4426:	31 c0                	xor    %eax,%eax
    4428:	48 8d 35 f3 3b 00 00 	lea    0x3bf3(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    442f:	bf 01 00 00 00       	mov    $0x1,%edi
    4434:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    4439:	e8 62 e0 ff ff       	call   24a0 <__printf_chk@plt>
  while (data->running && n < times) {
    443e:	44 8b 65 44          	mov    0x44(%rbp),%r12d
    4442:	45 85 e4             	test   %r12d,%r12d
    4445:	0f 84 9b 00 00 00    	je     44e6 <timer_thread+0x106>
  int n = 0;
    444b:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    444e:	45 31 e4             	xor    %r12d,%r12d
    4451:	49 89 e6             	mov    %rsp,%r14
    y++;
    4454:	31 db                	xor    %ebx,%ebx
    4456:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    nanosleep(&preempt , &rem2);
    445b:	4c 89 ef             	mov    %r13,%rdi
    445e:	4c 89 f6             	mov    %r14,%rsi
    n++;
    4461:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    4465:	e8 26 df ff ff       	call   2390 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    446a:	48 63 45 30          	movslq 0x30(%rbp),%rax
    y++;
    446e:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4473:	85 c0                	test   %eax,%eax
    4475:	7e 46                	jle    44bd <timer_thread+0xdd>
    4477:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    447b:	49 c1 e4 09          	shl    $0x9,%r12
    447f:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4483:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    4488:	4c 8b 19             	mov    (%rcx),%r11
    448b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    448d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4491:	99                   	cltd
    4492:	41 f7 7b 40          	idivl  0x40(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    4496:	49 8b 73 38          	mov    0x38(%r11),%rsi
    449a:	48 63 d2             	movslq %edx,%rdx
    449d:	48 c1 e2 09          	shl    $0x9,%rdx
    44a1:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    44ac:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    44b8:	49 39 c8             	cmp    %rcx,%r8
    44bb:	75 cb                	jne    4488 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    44bd:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    44c0:	48 8b 45 18          	mov    0x18(%rbp),%rax
  while (data->running && n < times) {
    44c4:	44 8b 45 44          	mov    0x44(%rbp),%r8d
    if (y >= data->threads[0]->task_count) {
    44c8:	48 8b 00             	mov    (%rax),%rax
    y++;
    44cb:	39 78 40             	cmp    %edi,0x40(%rax)
    44ce:	0f 4e fb             	cmovle %ebx,%edi
    44d1:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    44d4:	45 85 c0             	test   %r8d,%r8d
    44d7:	74 0d                	je     44e6 <timer_thread+0x106>
    44d9:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    44e0:	0f 85 75 ff ff ff    	jne    445b <timer_thread+0x7b>
    44e6:	48 8d 3d 4b 3b 00 00 	lea    0x3b4b(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    44ed:	e8 2e de ff ff       	call   2320 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    44f2:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    44f6:	85 d2                	test   %edx,%edx
    44f8:	7e 6b                	jle    4565 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    44fa:	48 63 45 40          	movslq 0x40(%rbp),%rax
    44fe:	85 c0                	test   %eax,%eax
    4500:	7e 63                	jle    4565 <timer_thread+0x185>
    4502:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    4506:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    450a:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4512:	31 c9                	xor    %ecx,%ecx
    4514:	48 89 c6             	mov    %rax,%rsi
    4517:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    451b:	48 8b 40 38          	mov    0x38(%rax),%rax
    451f:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4523:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4529:	74 15                	je     4540 <timer_thread+0x160>
    452b:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4535:	48 05 00 02 00 00    	add    $0x200,%rax
    453b:	48 39 c2             	cmp    %rax,%rdx
    453e:	74 1c                	je     455c <timer_thread+0x17c>
      data->threads[x]->tasks[y].sending = 0;
    4540:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    454a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4550:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4557:	48 39 c2             	cmp    %rax,%rdx
    455a:	75 e4                	jne    4540 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    455c:	48 83 c1 08          	add    $0x8,%rcx
    4560:	48 39 cf             	cmp    %rcx,%rdi
    4563:	75 b2                	jne    4517 <timer_thread+0x137>
  asm volatile ("mfence" ::: "memory");
    4565:	0f ae f0             	mfence
  struct timespec drain = {
    4568:	66 0f 6f 05 30 46 00 00 	movdqa 0x4630(%rip),%xmm0        # 8ba0 <_IO_stdin_used+0xba0>
    4570:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4575:	48 63 45 28          	movslq 0x28(%rbp),%rax
    y++;
    4579:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    457e:	85 c0                	test   %eax,%eax
    4580:	7e 4a                	jle    45cc <timer_thread+0x1ec>
    4582:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4586:	4d 63 e4             	movslq %r12d,%r12
    4589:	49 c1 e4 09          	shl    $0x9,%r12
    458d:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4591:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4598:	48 8b 19             	mov    (%rcx),%rbx
    459b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    459d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    45a1:	99                   	cltd
    45a2:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    45a5:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    45a9:	48 63 d2             	movslq %edx,%rdx
    45ac:	48 c1 e2 09          	shl    $0x9,%rdx
    45b0:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    45bb:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    45c7:	49 39 c8             	cmp    %rcx,%r8
    45ca:	75 cc                	jne    4598 <timer_thread+0x1b8>
    asm volatile ("mfence" ::: "memory");
    45cc:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    45cf:	48 8b 45 18          	mov    0x18(%rbp),%rax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    45d3:	8b 4d 30             	mov    0x30(%rbp),%ecx
    y++;
    45d6:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    45d9:	48 8b 00             	mov    (%rax),%rax
    y++;
    45dc:	39 78 40             	cmp    %edi,0x40(%rax)
    45df:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    45e3:	85 c9                	test   %ecx,%ecx
    45e5:	0f 8e 16 01 00 00    	jle    4701 <timer_thread+0x321>
    45eb:	31 db                	xor    %ebx,%ebx
    int all_empty = 1;
    45ed:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    45f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int y = 0 ; y < 2 ; y++) {
    45f8:	45 31 f6             	xor    %r14d,%r14d
    45fb:	41 89 dd             	mov    %ebx,%r13d
    45fe:	4c 8d 3c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r15
    4606:	44 89 f6             	mov    %r14d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4609:	85 c9                	test   %ecx,%ecx
    460b:	0f 8e af 00 00 00    	jle    46c0 <timer_thread+0x2e0>
    4611:	4c 89 f7             	mov    %r14,%rdi
      y = 0;
    4614:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4616:	45 31 c0             	xor    %r8d,%r8d
    4619:	48 c1 e7 09          	shl    $0x9,%rdi
    461d:	0f 1f 00             	nopl   (%rax)
          if (x == k) { continue; }
    4620:	41 39 d8             	cmp    %ebx,%r8d
    4623:	74 36                	je     465b <timer_thread+0x27b>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4625:	48 8b 55 18          	mov    0x18(%rbp),%rdx
    4629:	4a 8b 14 3a          	mov    (%rdx,%r15,1),%rdx
    462d:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4631:	4c 8b 94 3a 70 01 00 00 	mov    0x170(%rdx,%rdi,1),%r10
    4639:	49 01 c2             	add    %rax,%r10
    463c:	4d 8b 0a             	mov    (%r10),%r9
    463f:	49 8b 52 08          	mov    0x8(%r10),%rdx
    4643:	4d 8b 89 80 00 00 00 	mov    0x80(%r9),%r9
    464a:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    4651:	4d 85 c9             	test   %r9,%r9
    4654:	7f 2a                	jg     4680 <timer_thread+0x2a0>
    4656:	48 85 d2             	test   %rdx,%rdx
    4659:	7f 25                	jg     4680 <timer_thread+0x2a0>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    465b:	41 83 c0 01          	add    $0x1,%r8d
    465f:	48 83 c0 38          	add    $0x38,%rax
    4663:	41 39 c8             	cmp    %ecx,%r8d
    4666:	75 b8                	jne    4620 <timer_thread+0x240>
      for (int y = 0 ; y < 2 ; y++) {
    4668:	49 83 fe 01          	cmp    $0x1,%r14
    466c:	74 52                	je     46c0 <timer_thread+0x2e0>
    466e:	49 83 c6 01          	add    $0x1,%r14
    4672:	44 89 f6             	mov    %r14d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4675:	eb 9a                	jmp    4611 <timer_thread+0x231>
    4677:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4680:	48 83 ec 08          	sub    $0x8,%rsp
    4684:	89 f1                	mov    %esi,%ecx
    4686:	bf 01 00 00 00       	mov    $0x1,%edi
    468b:	31 c0                	xor    %eax,%eax
    468d:	52                   	push   %rdx
    468e:	48 8d 35 c8 39 00 00 	lea    0x39c8(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    4695:	44 89 ea             	mov    %r13d,%edx
    4698:	e8 03 de ff ff       	call   24a0 <__printf_chk@plt>
      for (int y = 0 ; y < 2 ; y++) {
    469d:	5a                   	pop    %rdx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    469e:	8b 4d 30             	mov    0x30(%rbp),%ecx
      for (int y = 0 ; y < 2 ; y++) {
    46a1:	5e                   	pop    %rsi
    46a2:	49 83 fe 01          	cmp    $0x1,%r14
    46a6:	74 48                	je     46f0 <timer_thread+0x310>
    46a8:	49 83 c6 01          	add    $0x1,%r14
    46ac:	45 31 db             	xor    %r11d,%r11d
    46af:	44 89 f6             	mov    %r14d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    46b2:	85 c9                	test   %ecx,%ecx
    46b4:	0f 8f 57 ff ff ff    	jg     4611 <timer_thread+0x231>
    46ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46c0:	48 83 c3 01          	add    $0x1,%rbx
    46c4:	39 d9                	cmp    %ebx,%ecx
    46c6:	0f 8f 2c ff ff ff    	jg     45f8 <timer_thread+0x218>
    if (all_empty == 1) {
    46cc:	41 83 fb 01          	cmp    $0x1,%r11d
    46d0:	74 2f                	je     4701 <timer_thread+0x321>
      nanosleep(&drain , &drainrem);
    46d2:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    46d7:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    46dc:	e8 af dc ff ff       	call   2390 <nanosleep@plt>
    46e1:	e9 8f fe ff ff       	jmp    4575 <timer_thread+0x195>
    46e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46f0:	48 83 c3 01          	add    $0x1,%rbx
    46f4:	45 31 db             	xor    %r11d,%r11d
    46f7:	39 d9                	cmp    %ebx,%ecx
    46f9:	0f 8f f9 fe ff ff    	jg     45f8 <timer_thread+0x218>
    46ff:	eb cb                	jmp    46cc <timer_thread+0x2ec>
    4701:	48 8d 3d 4c 39 00 00 	lea    0x394c(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4708:	e8 13 dc ff ff       	call   2320 <puts@plt>
  while (data->running) {
    470d:	8b 7d 44             	mov    0x44(%rbp),%edi
    4710:	85 ff                	test   %edi,%edi
    4712:	0f 84 e6 00 00 00    	je     47fe <timer_thread+0x41e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4718:	8b 45 2c             	mov    0x2c(%rbp),%eax
    471b:	31 db                	xor    %ebx,%ebx
    471d:	4c 8d 25 50 39 00 00 	lea    0x3950(%rip),%r12        # 8074 <_IO_stdin_used+0x74>
    4724:	4c 8d 2d 64 39 00 00 	lea    0x3964(%rip),%r13        # 808f <_IO_stdin_used+0x8f>
    472b:	85 c0                	test   %eax,%eax
    472d:	7e 34                	jle    4763 <timer_thread+0x383>
    472f:	90                   	nop
    4730:	31 c0                	xor    %eax,%eax
    4732:	89 da                	mov    %ebx,%edx
    4734:	4c 89 e6             	mov    %r12,%rsi
    4737:	bf 01 00 00 00       	mov    $0x1,%edi
    473c:	e8 5f dd ff ff       	call   24a0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4741:	48 8b 45 18          	mov    0x18(%rbp),%rax
    4745:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4749:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    474d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4754:	0f 84 d1 00 00 00    	je     482b <timer_thread+0x44b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    475a:	48 83 c3 01          	add    $0x1,%rbx
    475e:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    4761:	7f cd                	jg     4730 <timer_thread+0x350>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4763:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    4767:	85 d2                	test   %edx,%edx
    4769:	7e 7d                	jle    47e8 <timer_thread+0x408>
      for (int y = 0 ; y < data->task_count ; y++) {
    476b:	8b 45 40             	mov    0x40(%rbp),%eax
    476e:	85 c0                	test   %eax,%eax
    4770:	7e 76                	jle    47e8 <timer_thread+0x408>
    4772:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4775:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    4779:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4781:	31 c9                	xor    %ecx,%ecx
    4783:	48 c1 e6 09          	shl    $0x9,%rsi
    4787:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4790:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4794:	48 8b 40 38          	mov    0x38(%rax),%rax
    4798:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    479c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    47a2:	74 1c                	je     47c0 <timer_thread+0x3e0>
    47a4:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    47ae:	48 05 00 02 00 00    	add    $0x200,%rax
    47b4:	48 39 c2             	cmp    %rax,%rdx
    47b7:	74 26                	je     47df <timer_thread+0x3ff>
    47b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    47c0:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    47ca:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    47d0:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    47da:	48 39 c2             	cmp    %rax,%rdx
    47dd:	75 e1                	jne    47c0 <timer_thread+0x3e0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    47df:	48 83 c1 08          	add    $0x8,%rcx
    47e3:	48 39 f9             	cmp    %rdi,%rcx
    47e6:	75 a8                	jne    4790 <timer_thread+0x3b0>
    asm volatile ("mfence" ::: "memory");
    47e8:	0f ae f0             	mfence
    47eb:	48 8d 3d af 38 00 00 	lea    0x38af(%rip),%rdi        # 80a1 <_IO_stdin_used+0xa1>
    47f2:	e8 29 db ff ff       	call   2320 <puts@plt>
    data->running = 0;
    47f7:	c7 45 44 00 00 00 00 	movl   $0x0,0x44(%rbp)
    47fe:	48 8d 3d a3 38 00 00 	lea    0x38a3(%rip),%rdi        # 80a8 <_IO_stdin_used+0xa8>
    4805:	e8 16 db ff ff       	call   2320 <puts@plt>
}
    480a:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    480f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4818:	75 40                	jne    485a <timer_thread+0x47a>
    481a:	48 83 c4 58          	add    $0x58,%rsp
    481e:	31 c0                	xor    %eax,%eax
    4820:	5b                   	pop    %rbx
    4821:	5d                   	pop    %rbp
    4822:	41 5c                	pop    %r12
    4824:	41 5d                	pop    %r13
    4826:	41 5e                	pop    %r14
    4828:	41 5f                	pop    %r15
    482a:	c3                   	ret
    482b:	4c 89 ef             	mov    %r13,%rdi
    482e:	e8 ed da ff ff       	call   2320 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4833:	48 8b 45 18          	mov    0x18(%rbp),%rax
    4837:	be 01 00 00 00       	mov    $0x1,%esi
    483c:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4840:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4844:	8b 78 60             	mov    0x60(%rax),%edi
    4847:	e8 04 dc ff ff       	call   2450 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    484c:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    484f:	0f 8f db fe ff ff    	jg     4730 <timer_thread+0x350>
    4855:	e9 09 ff ff ff       	jmp    4763 <timer_thread+0x383>
}
    485a:	e8 11 db ff ff       	call   2370 <__stack_chk_fail@plt>
    485f:	90                   	nop

0000000000004860 <sendm.part.0>:
int sendm(struct BarrierTask *data) {
    4860:	41 57                	push   %r15
    4862:	41 56                	push   %r14
    4864:	41 55                	push   %r13
    4866:	41 54                	push   %r12
    4868:	55                   	push   %rbp
    4869:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    486a:	8b af 40 01 00 00    	mov    0x140(%rdi),%ebp
    4870:	85 ed                	test   %ebp,%ebp
    4872:	0f 8e 7a 01 00 00    	jle    49f2 <sendm.part.0+0x192>
        if (n == data->thread->real_thread_index) { continue; }
    4878:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    487f:	49 89 ff             	mov    %rdi,%r15
    4882:	45 31 f6             	xor    %r14d,%r14d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    4885:	45 31 ed             	xor    %r13d,%r13d
    4888:	41 89 ec             	mov    %ebp,%r12d
        if (n == data->thread->real_thread_index) { continue; }
    488b:	8b 40 08             	mov    0x8(%rax),%eax
    488e:	89 44 24 cc          	mov    %eax,-0x34(%rsp)
    4892:	48 8d 87 88 01 00 00 	lea    0x188(%rdi),%rax
    4899:	48 89 44 24 e8       	mov    %rax,-0x18(%rsp)
    489e:	48 8d 87 90 01 00 00 	lea    0x190(%rdi),%rax
    48a5:	48 89 44 24 f0       	mov    %rax,-0x10(%rsp)
    48aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    48b0:	44 39 6c 24 cc       	cmp    %r13d,-0x34(%rsp)
    48b5:	0f 84 26 01 00 00    	je     49e1 <sendm.part.0+0x181>
        struct Data *them = data->mailboxes[n].higher;
    48bb:	49 8b 87 70 01 00 00 	mov    0x170(%r15),%rax
    48c2:	4c 01 f0             	add    %r14,%rax
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    48c5:	44 8b 40 30          	mov    0x30(%rax),%r8d
        struct Data *them = data->mailboxes[n].higher;
    48c9:	48 8b 48 08          	mov    0x8(%rax),%rcx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    48cd:	41 83 f8 02          	cmp    $0x2,%r8d
    48d1:	0f 84 29 01 00 00    	je     4a00 <sendm.part.0+0x1a0>
        for (; them->messages_count < min;) {
    48d7:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    48de:	48 63 a9 88 00 00 00 	movslq 0x88(%rcx),%rbp
    48e5:	48 39 ee             	cmp    %rbp,%rsi
    48e8:	0f 8d f3 00 00 00    	jge    49e1 <sendm.part.0+0x181>
    48ee:	49 8b 87 08 01 00 00 	mov    0x108(%r15),%rax
    48f5:	48 39 ee             	cmp    %rbp,%rsi
    48f8:	49 89 eb             	mov    %rbp,%r11
          them->messages[them->messages_count++] = data->message; 
    48fb:	48 8b 11             	mov    (%rcx),%rdx
    48fe:	41 0f 9c c1          	setl   %r9b
    4902:	49 29 f3             	sub    %rsi,%r11
    4905:	48 89 44 24 d0       	mov    %rax,-0x30(%rsp)
    490a:	48 8b 81 08 03 00 00 	mov    0x308(%rcx),%rax
    4911:	49 8d 5b ff          	lea    -0x1(%r11),%rbx
    4915:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    491a:	48 89 44 24 d8       	mov    %rax,-0x28(%rsp)
    491f:	48 83 fb 02          	cmp    $0x2,%rbx
    4923:	0f 86 a7 01 00 00    	jbe    4ad0 <sendm.part.0+0x270>
    4929:	45 84 c9             	test   %r9b,%r9b
    492c:	0f 84 9e 01 00 00    	je     4ad0 <sendm.part.0+0x270>
    4932:	4c 8d 14 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r10
    493a:	4a 8d 04 12          	lea    (%rdx,%r10,1),%rax
    493e:	48 89 44 24 e0       	mov    %rax,-0x20(%rsp)
    4943:	49 89 c3             	mov    %rax,%r11
    4946:	48 8d 04 ea          	lea    (%rdx,%rbp,8),%rax
    494a:	48 39 44 24 e8       	cmp    %rax,-0x18(%rsp)
    494f:	0f 83 cb 00 00 00    	jae    4a20 <sendm.part.0+0x1c0>
    4955:	4c 89 d8             	mov    %r11,%rax
    4958:	4c 8b 5c 24 f0       	mov    -0x10(%rsp),%r11
    495d:	48 89 f7             	mov    %rsi,%rdi
    4960:	4c 39 d8             	cmp    %r11,%rax
    4963:	0f 83 b7 00 00 00    	jae    4a20 <sendm.part.0+0x1c0>
    4969:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4970:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    4977:	48 89 04 fa          	mov    %rax,(%rdx,%rdi,8)
        for (; them->messages_count < min;) {
    497b:	48 83 c7 01          	add    $0x1,%rdi
    497f:	48 39 fd             	cmp    %rdi,%rbp
    4982:	7f ec                	jg     4970 <sendm.part.0+0x110>
    4984:	0f 1f 40 00          	nopl   0x0(%rax)
    4988:	31 ff                	xor    %edi,%edi
    498a:	45 84 c9             	test   %r9b,%r9b
    498d:	4c 8b 5c 24 d0       	mov    -0x30(%rsp),%r11
    4992:	48 0f 45 fb          	cmovne %rbx,%rdi
    4996:	4d 8d 5c 3b 01       	lea    0x1(%r11,%rdi,1),%r11
    499b:	48 8d 74 3e 01       	lea    0x1(%rsi,%rdi,1),%rsi
    49a0:	4d 89 9f 08 01 00 00 	mov    %r11,0x108(%r15)
    49a7:	4c 8b 5c 24 d8       	mov    -0x28(%rsp),%r11
    49ac:	48 89 b1 80 00 00 00 	mov    %rsi,0x80(%rcx)
    49b3:	48 8d 34 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rsi
    49bb:	bb 00 00 00 00       	mov    $0x0,%ebx
    49c0:	48 0f 44 f3          	cmove  %rbx,%rsi
    49c4:	4d 8d 5c 3b 01       	lea    0x1(%r11,%rdi,1),%r11
    49c9:	4c 01 d2             	add    %r10,%rdx
    49cc:	4c 89 99 08 03 00 00 	mov    %r11,0x308(%rcx)
    49d3:	48 89 04 32          	mov    %rax,(%rdx,%rsi,1)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    49d7:	41 83 f8 02          	cmp    $0x2,%r8d
    49db:	0f 84 bf 00 00 00    	je     4aa0 <sendm.part.0+0x240>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    49e1:	41 83 c5 01          	add    $0x1,%r13d
    49e5:	49 83 c6 38          	add    $0x38,%r14
    49e9:	45 39 e5             	cmp    %r12d,%r13d
    49ec:	0f 85 be fe ff ff    	jne    48b0 <sendm.part.0+0x50>
      asm volatile ("sfence" ::: "memory");
    49f2:	0f ae f8             	sfence
}
    49f5:	5b                   	pop    %rbx
    49f6:	5d                   	pop    %rbp
    49f7:	41 5c                	pop    %r12
    49f9:	41 5d                	pop    %r13
    49fb:	41 5e                	pop    %r14
    49fd:	41 5f                	pop    %r15
    49ff:	c3                   	ret
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    4a00:	8b 81 00 01 00 00    	mov    0x100(%rcx),%eax
    4a06:	83 f8 01             	cmp    $0x1,%eax
    4a09:	0f 84 d1 00 00 00    	je     4ae0 <sendm.part.0+0x280>
        else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    4a0f:	85 c0                	test   %eax,%eax
    4a11:	74 ce                	je     49e1 <sendm.part.0+0x181>
    4a13:	e9 bf fe ff ff       	jmp    48d7 <sendm.part.0+0x77>
    4a18:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4a20:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    4a25:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    4a2c:	48 8b 7c 24 e0       	mov    -0x20(%rsp),%rdi
    4a31:	49 d1 eb             	shr    %r11
    4a34:	66 48 0f 6e c0       	movq   %rax,%xmm0
    4a39:	4c 89 dd             	mov    %r11,%rbp
    4a3c:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    4a40:	48 c1 e5 04          	shl    $0x4,%rbp
    4a44:	49 89 eb             	mov    %rbp,%r11
    4a47:	48 01 fd             	add    %rdi,%rbp
    4a4a:	41 83 e3 10          	and    $0x10,%r11d
    4a4e:	74 11                	je     4a61 <sendm.part.0+0x201>
          them->messages[them->messages_count++] = data->message; 
    4a50:	0f 11 07             	movups %xmm0,(%rdi)
        for (; them->messages_count < min;) {
    4a53:	48 83 c7 10          	add    $0x10,%rdi
    4a57:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    4a5c:	48 39 fd             	cmp    %rdi,%rbp
    4a5f:	74 1a                	je     4a7b <sendm.part.0+0x21b>
    4a61:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
          them->messages[them->messages_count++] = data->message; 
    4a66:	0f 11 07             	movups %xmm0,(%rdi)
    4a69:	48 83 c7 20          	add    $0x20,%rdi
    4a6d:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    4a71:	48 39 fd             	cmp    %rdi,%rbp
    4a74:	75 f0                	jne    4a66 <sendm.part.0+0x206>
    4a76:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    4a7b:	4c 89 df             	mov    %r11,%rdi
    4a7e:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    4a82:	48 01 f7             	add    %rsi,%rdi
    4a85:	41 83 e3 01          	and    $0x1,%r11d
    4a89:	0f 84 f9 fe ff ff    	je     4988 <sendm.part.0+0x128>
          them->messages[them->messages_count++] = data->message; 
    4a8f:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    4a96:	48 89 04 fa          	mov    %rax,(%rdx,%rdi,8)
        for (; them->messages_count < min;) {
    4a9a:	e9 e9 fe ff ff       	jmp    4988 <sendm.part.0+0x128>
    4a9f:	90                   	nop
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    4aa0:	83 b9 00 01 00 00 01 	cmpl   $0x1,0x100(%rcx)
    4aa7:	0f 85 34 ff ff ff    	jne    49e1 <sendm.part.0+0x181>
          them->available_sending = 0;
    4aad:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
          them->available_receiving = 1;
    4ab7:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
          them->finished_reading = 0;
    4ac1:	c7 81 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rcx)
    4acb:	e9 11 ff ff ff       	jmp    49e1 <sendm.part.0+0x181>
          them->messages[them->messages_count++] = data->message; 
    4ad0:	48 89 f7             	mov    %rsi,%rdi
    4ad3:	4c 8d 14 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r10
    4adb:	e9 90 fe ff ff       	jmp    4970 <sendm.part.0+0x110>
        for (; them->messages_count < min;) {
    4ae0:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    4ae7:	48 63 a9 88 00 00 00 	movslq 0x88(%rcx),%rbp
    4aee:	48 39 f5             	cmp    %rsi,%rbp
    4af1:	0f 8f f7 fd ff ff    	jg     48ee <sendm.part.0+0x8e>
    4af7:	eb b4                	jmp    4aad <sendm.part.0+0x24d>
    4af9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004b00 <strtolower>:
void strtolower(char *str) {
    4b00:	f3 0f 1e fa          	endbr64
    4b04:	55                   	push   %rbp
    4b05:	53                   	push   %rbx
    4b06:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    4b0a:	48 0f be 1f          	movsbq (%rdi),%rbx
    4b0e:	84 db                	test   %bl,%bl
    4b10:	74 24                	je     4b36 <strtolower+0x36>
    4b12:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4b15:	e8 56 da ff ff       	call   2570 <__ctype_tolower_loc@plt>
    4b1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b20:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4b23:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4b27:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4b2a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    4b2d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4b32:	84 db                	test   %bl,%bl
    4b34:	75 ea                	jne    4b20 <strtolower+0x20>
}
    4b36:	48 83 c4 08          	add    $0x8,%rsp
    4b3a:	5b                   	pop    %rbx
    4b3b:	5d                   	pop    %rbp
    4b3c:	c3                   	ret
    4b3d:	0f 1f 00             	nopl   (%rax)

0000000000004b40 <zh_malloc>:
void *zh_malloc(size_t size) {
    4b40:	f3 0f 1e fa          	endbr64
    4b44:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4b48:	e8 13 d9 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4b4d:	48 85 c0             	test   %rax,%rax
    4b50:	74 05                	je     4b57 <zh_malloc+0x17>
}
    4b52:	48 83 c4 08          	add    $0x8,%rsp
    4b56:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4b57:	48 8b 0d c2 64 00 00 	mov    0x64c2(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4b5e:	ba 28 00 00 00       	mov    $0x28,%edx
    4b63:	be 01 00 00 00       	mov    $0x1,%esi
    4b68:	48 8d 3d 49 3a 00 00 	lea    0x3a49(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    4b6f:	e8 ac d9 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4b74:	bf 01 00 00 00       	mov    $0x1,%edi
    4b79:	e8 82 d9 ff ff       	call   2500 <exit@plt>
    4b7e:	66 90                	xchg   %ax,%ax

0000000000004b80 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4b80:	f3 0f 1e fa          	endbr64
    4b84:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4b85:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    4b8a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    4b8d:	e8 0e d8 ff ff       	call   23a0 <strrchr@plt>
    if (!dot || dot == filename)
    4b92:	48 85 c0             	test   %rax,%rax
    4b95:	74 11                	je     4ba8 <get_filename_ext+0x28>
    4b97:	48 39 c3             	cmp    %rax,%rbx
    4b9a:	74 0c                	je     4ba8 <get_filename_ext+0x28>
    return dot + 1;
    4b9c:	48 83 c0 01          	add    $0x1,%rax
}
    4ba0:	5b                   	pop    %rbx
    4ba1:	c3                   	ret
    4ba2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4ba8:	48 8d 05 41 35 00 00 	lea    0x3541(%rip),%rax        # 80f0 <_IO_stdin_used+0xf0>
}
    4baf:	5b                   	pop    %rbx
    4bb0:	c3                   	ret
    4bb1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4bbc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004bc0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4bc0:	f3 0f 1e fa          	endbr64
    4bc4:	41 55                	push   %r13
    4bc6:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4bc9:	48 89 fe             	mov    %rdi,%rsi
    4bcc:	41 54                	push   %r12
    4bce:	55                   	push   %rbp
    4bcf:	48 89 d5             	mov    %rdx,%rbp
    4bd2:	ba 00 04 00 00       	mov    $0x400,%edx
    4bd7:	53                   	push   %rbx
    4bd8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4bdf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4be8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4bf0:	31 c0                	xor    %eax,%eax
    4bf2:	49 89 e4             	mov    %rsp,%r12
    4bf5:	4c 89 e7             	mov    %r12,%rdi
    4bf8:	e8 83 d8 ff ff       	call   2480 <__strcpy_chk@plt>
    for (; *str; ++str)
    4bfd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4c02:	84 db                	test   %bl,%bl
    4c04:	74 24                	je     4c2a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4c06:	e8 65 d9 ff ff       	call   2570 <__ctype_tolower_loc@plt>
    4c0b:	48 8b 08             	mov    (%rax),%rcx
    4c0e:	4c 89 e0             	mov    %r12,%rax
    4c11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4c18:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4c1b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4c1f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4c22:	48 0f be 18          	movsbq (%rax),%rbx
    4c26:	84 db                	test   %bl,%bl
    4c28:	75 ee                	jne    4c18 <send_headers+0x58>
    void *buf = malloc(size);
    4c2a:	bf 11 00 00 00       	mov    $0x11,%edi
    4c2f:	e8 2c d8 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4c34:	48 85 c0             	test   %rax,%rax
    4c37:	0f 84 7e 04 00 00    	je     50bb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4c3d:	66 0f 6f 05 6b 3f 00 00 	movdqa 0x3f6b(%rip),%xmm0        # 8bb0 <_IO_stdin_used+0xbb0>
    iov[0].iov_base = zh_malloc(slen);
    4c45:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4c49:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4c4e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4c56:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4c5a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4c5d:	e8 fe d7 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4c62:	48 85 c0             	test   %rax,%rax
    4c65:	0f 84 50 04 00 00    	je     50bb <send_headers+0x4fb>
    4c6b:	66 0f 6f 05 4d 3f 00 00 	movdqa 0x3f4d(%rip),%xmm0        # 8bc0 <_IO_stdin_used+0xbc0>
    iov[1].iov_base = zh_malloc(slen);
    4c73:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4c77:	4c 89 e7             	mov    %r12,%rdi
    4c7a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4c84:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4c8c:	0f 11 00             	movups %xmm0,(%rax)
    4c8f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4c93:	be 2e 00 00 00       	mov    $0x2e,%esi
    4c98:	e8 03 d7 ff ff       	call   23a0 <strrchr@plt>
    if (!dot || dot == filename)
    4c9d:	48 85 c0             	test   %rax,%rax
    4ca0:	0f 84 ea 02 00 00    	je     4f90 <send_headers+0x3d0>
    4ca6:	4c 39 e0             	cmp    %r12,%rax
    4ca9:	0f 84 e1 02 00 00    	je     4f90 <send_headers+0x3d0>
    return dot + 1;
    4caf:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4cb3:	48 8d 3d 04 34 00 00 	lea    0x3404(%rip),%rdi        # 80be <_IO_stdin_used+0xbe>
    4cba:	48 89 de             	mov    %rbx,%rsi
    4cbd:	e8 3e d7 ff ff       	call   2400 <strcmp@plt>
    4cc2:	85 c0                	test   %eax,%eax
    4cc4:	75 20                	jne    4ce6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4cc6:	66 0f 6f 05 02 3f 00 00 	movdqa 0x3f02(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4cce:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4cd6:	66 0f 6f 05 02 3f 00 00 	movdqa 0x3f02(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4cde:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4ce6:	48 89 de             	mov    %rbx,%rsi
    4ce9:	48 8d 3d d2 33 00 00 	lea    0x33d2(%rip),%rdi        # 80c2 <_IO_stdin_used+0xc2>
    4cf0:	e8 0b d7 ff ff       	call   2400 <strcmp@plt>
    4cf5:	85 c0                	test   %eax,%eax
    4cf7:	75 20                	jne    4d19 <send_headers+0x159>
    4cf9:	66 0f 6f 05 cf 3e 00 00 	movdqa 0x3ecf(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4d01:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4d09:	66 0f 6f 05 cf 3e 00 00 	movdqa 0x3ecf(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4d11:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4d19:	48 89 de             	mov    %rbx,%rsi
    4d1c:	48 8d 3d a4 33 00 00 	lea    0x33a4(%rip),%rdi        # 80c7 <_IO_stdin_used+0xc7>
    4d23:	e8 d8 d6 ff ff       	call   2400 <strcmp@plt>
    4d28:	85 c0                	test   %eax,%eax
    4d2a:	0f 84 10 02 00 00    	je     4f40 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4d30:	48 89 de             	mov    %rbx,%rsi
    4d33:	48 8d 3d 91 33 00 00 	lea    0x3391(%rip),%rdi        # 80cb <_IO_stdin_used+0xcb>
    4d3a:	e8 c1 d6 ff ff       	call   2400 <strcmp@plt>
    4d3f:	85 c0                	test   %eax,%eax
    4d41:	0f 84 a9 02 00 00    	je     4ff0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4d47:	48 89 de             	mov    %rbx,%rsi
    4d4a:	48 8d 3d 7e 33 00 00 	lea    0x337e(%rip),%rdi        # 80cf <_IO_stdin_used+0xcf>
    4d51:	e8 aa d6 ff ff       	call   2400 <strcmp@plt>
    4d56:	85 c0                	test   %eax,%eax
    4d58:	0f 84 6a 02 00 00    	je     4fc8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4d5e:	48 89 de             	mov    %rbx,%rsi
    4d61:	48 8d 3d aa 33 00 00 	lea    0x33aa(%rip),%rdi        # 8112 <_IO_stdin_used+0x112>
    4d68:	e8 93 d6 ff ff       	call   2400 <strcmp@plt>
    4d6d:	85 c0                	test   %eax,%eax
    4d6f:	0f 84 2b 02 00 00    	je     4fa0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4d75:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4d78:	0f 84 52 01 00 00    	je     4ed0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4d7e:	48 89 de             	mov    %rbx,%rsi
    4d81:	48 8d 3d 4b 33 00 00 	lea    0x334b(%rip),%rdi        # 80d3 <_IO_stdin_used+0xd3>
    4d88:	e8 73 d6 ff ff       	call   2400 <strcmp@plt>
    4d8d:	85 c0                	test   %eax,%eax
    4d8f:	0f 84 ab 02 00 00    	je     5040 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4d95:	48 89 de             	mov    %rbx,%rsi
    4d98:	48 8d 3d 38 33 00 00 	lea    0x3338(%rip),%rdi        # 80d7 <_IO_stdin_used+0xd7>
    4d9f:	e8 5c d6 ff ff       	call   2400 <strcmp@plt>
    4da4:	85 c0                	test   %eax,%eax
    4da6:	0f 84 6c 02 00 00    	je     5018 <send_headers+0x458>
    slen = strlen(send_buffer);
    4dac:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4db4:	4c 89 e7             	mov    %r12,%rdi
    4db7:	e8 a4 d5 ff ff       	call   2360 <strlen@plt>
    void *buf = malloc(size);
    4dbc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4dbf:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4dc2:	e8 99 d6 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4dc7:	48 85 c0             	test   %rax,%rax
    4dca:	0f 84 eb 02 00 00    	je     50bb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4dd0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4dd4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4dd8:	83 fb 08             	cmp    $0x8,%ebx
    4ddb:	0f 83 3f 01 00 00    	jae    4f20 <send_headers+0x360>
    4de1:	f6 c3 04             	test   $0x4,%bl
    4de4:	0f 85 7b 02 00 00    	jne    5065 <send_headers+0x4a5>
    4dea:	85 db                	test   %ebx,%ebx
    4dec:	74 13                	je     4e01 <send_headers+0x241>
    4dee:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4df6:	88 10                	mov    %dl,(%rax)
    4df8:	f6 c3 02             	test   $0x2,%bl
    4dfb:	0f 85 96 02 00 00    	jne    5097 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4e01:	4d 89 e8             	mov    %r13,%r8
    4e04:	48 8d 0d d0 32 00 00 	lea    0x32d0(%rip),%rcx        # 80db <_IO_stdin_used+0xdb>
    4e0b:	4c 89 e7             	mov    %r12,%rdi
    4e0e:	31 c0                	xor    %eax,%eax
    4e10:	ba 00 04 00 00       	mov    $0x400,%edx
    4e15:	be 01 00 00 00       	mov    $0x1,%esi
    4e1a:	e8 61 d7 ff ff       	call   2580 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4e1f:	4c 89 e7             	mov    %r12,%rdi
    4e22:	e8 39 d5 ff ff       	call   2360 <strlen@plt>
    void *buf = malloc(size);
    4e27:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4e2a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4e2d:	e8 2e d6 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4e32:	48 85 c0             	test   %rax,%rax
    4e35:	0f 84 80 02 00 00    	je     50bb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4e3b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4e3f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4e43:	83 fb 08             	cmp    $0x8,%ebx
    4e46:	0f 83 1c 01 00 00    	jae    4f68 <send_headers+0x3a8>
    4e4c:	f6 c3 04             	test   $0x4,%bl
    4e4f:	0f 85 29 02 00 00    	jne    507e <send_headers+0x4be>
    4e55:	85 db                	test   %ebx,%ebx
    4e57:	74 13                	je     4e6c <send_headers+0x2ac>
    4e59:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4e61:	88 10                	mov    %dl,(%rax)
    4e63:	f6 c3 02             	test   $0x2,%bl
    4e66:	0f 85 3d 02 00 00    	jne    50a9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4e6c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4e71:	bf 02 00 00 00       	mov    $0x2,%edi
    4e76:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4e7e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4e86:	e8 d5 d5 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4e8b:	48 85 c0             	test   %rax,%rax
    4e8e:	0f 84 27 02 00 00    	je     50bb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4e94:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4e9c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4ea0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4ea8:	66 89 10             	mov    %dx,(%rax)
}
    4eab:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4eb3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4ebc:	0f 85 20 02 00 00    	jne    50e2 <send_headers+0x522>
    4ec2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4ec9:	5b                   	pop    %rbx
    4eca:	5d                   	pop    %rbp
    4ecb:	41 5c                	pop    %r12
    4ecd:	41 5d                	pop    %r13
    4ecf:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4ed0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4ed4:	0f 85 a4 fe ff ff    	jne    4d7e <send_headers+0x1be>
    4eda:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4ede:	0f 85 9a fe ff ff    	jne    4d7e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ee4:	66 0f 6f 05 44 3d 00 00 	movdqa 0x3d44(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    4eec:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4ef6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4efe:	66 0f 6f 05 3a 3d 00 00 	movdqa 0x3d3a(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    4f06:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4f0e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4f16:	e9 63 fe ff ff       	jmp    4d7e <send_headers+0x1be>
    4f1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4f20:	89 da                	mov    %ebx,%edx
    4f22:	48 89 c7             	mov    %rax,%rdi
    4f25:	4c 89 e6             	mov    %r12,%rsi
    4f28:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4f2d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4f32:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4f35:	c1 e9 03             	shr    $0x3,%ecx
    4f38:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4f3b:	e9 c1 fe ff ff       	jmp    4e01 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f40:	66 0f 6f 05 88 3c 00 00 	movdqa 0x3c88(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4f48:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f50:	66 0f 6f 05 98 3c 00 00 	movdqa 0x3c98(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    4f58:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4f60:	e9 cb fd ff ff       	jmp    4d30 <send_headers+0x170>
    4f65:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4f68:	89 da                	mov    %ebx,%edx
    4f6a:	48 89 c7             	mov    %rax,%rdi
    4f6d:	4c 89 e6             	mov    %r12,%rsi
    4f70:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4f75:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4f7a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4f7d:	c1 e9 03             	shr    $0x3,%ecx
    4f80:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4f83:	e9 e4 fe ff ff       	jmp    4e6c <send_headers+0x2ac>
    4f88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4f90:	48 8d 1d 59 31 00 00 	lea    0x3159(%rip),%rbx        # 80f0 <_IO_stdin_used+0xf0>
    4f97:	e9 94 fd ff ff       	jmp    4d30 <send_headers+0x170>
    4f9c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4fa0:	66 0f 6f 05 68 3c 00 00 	movdqa 0x3c68(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4fa8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4fb0:	66 0f 6f 05 68 3c 00 00 	movdqa 0x3c68(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4fb8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4fc0:	e9 b0 fd ff ff       	jmp    4d75 <send_headers+0x1b5>
    4fc5:	0f 1f 00             	nopl   (%rax)
    4fc8:	66 0f 6f 05 40 3c 00 00 	movdqa 0x3c40(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4fd0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4fd8:	66 0f 6f 05 40 3c 00 00 	movdqa 0x3c40(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4fe0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4fe8:	e9 71 fd ff ff       	jmp    4d5e <send_headers+0x19e>
    4fed:	0f 1f 00             	nopl   (%rax)
    4ff0:	66 0f 6f 05 d8 3b 00 00 	movdqa 0x3bd8(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4ff8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5000:	66 0f 6f 05 f8 3b 00 00 	movdqa 0x3bf8(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    5008:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5010:	e9 32 fd ff ff       	jmp    4d47 <send_headers+0x187>
    5015:	0f 1f 00             	nopl   (%rax)
    5018:	66 0f 6f 05 f0 3b 00 00 	movdqa 0x3bf0(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    5020:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5028:	66 0f 6f 05 30 3c 00 00 	movdqa 0x3c30(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    5030:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    5038:	e9 6f fd ff ff       	jmp    4dac <send_headers+0x1ec>
    503d:	0f 1f 00             	nopl   (%rax)
    5040:	66 0f 6f 05 c8 3b 00 00 	movdqa 0x3bc8(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    5048:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5050:	66 0f 6f 05 f8 3b 00 00 	movdqa 0x3bf8(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5058:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    5060:	e9 30 fd ff ff       	jmp    4d95 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    5065:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    506c:	89 db                	mov    %ebx,%ebx
    506e:	89 10                	mov    %edx,(%rax)
    5070:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    5075:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5079:	e9 83 fd ff ff       	jmp    4e01 <send_headers+0x241>
    507e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    5085:	89 db                	mov    %ebx,%ebx
    5087:	89 10                	mov    %edx,(%rax)
    5089:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    508e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5092:	e9 d5 fd ff ff       	jmp    4e6c <send_headers+0x2ac>
    5097:	89 db                	mov    %ebx,%ebx
    5099:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    509f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    50a4:	e9 58 fd ff ff       	jmp    4e01 <send_headers+0x241>
    50a9:	89 db                	mov    %ebx,%ebx
    50ab:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    50b1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    50b6:	e9 b1 fd ff ff       	jmp    4e6c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    50bb:	48 8b 0d 5e 5f 00 00 	mov    0x5f5e(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    50c2:	ba 28 00 00 00       	mov    $0x28,%edx
    50c7:	be 01 00 00 00       	mov    $0x1,%esi
    50cc:	48 8d 3d e5 34 00 00 	lea    0x34e5(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    50d3:	e8 48 d4 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    50d8:	bf 01 00 00 00       	mov    $0x1,%edi
    50dd:	e8 1e d4 ff ff       	call   2500 <exit@plt>
}
    50e2:	e8 89 d2 ff ff       	call   2370 <__stack_chk_fail@plt>
    50e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000050f0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    50f0:	f3 0f 1e fa          	endbr64
    50f4:	41 55                	push   %r13
    50f6:	49 89 d5             	mov    %rdx,%r13
    50f9:	41 54                	push   %r12
    50fb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    50fe:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5101:	55                   	push   %rbp
    5102:	53                   	push   %rbx
    5103:	48 89 f3             	mov    %rsi,%rbx
    5106:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    510a:	e8 51 d3 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    510f:	48 85 c0             	test   %rax,%rax
    5112:	74 6b                	je     517f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    5114:	4c 89 e7             	mov    %r12,%rdi
    5117:	48 89 c5             	mov    %rax,%rbp
    511a:	31 f6                	xor    %esi,%esi
    511c:	31 c0                	xor    %eax,%eax
    511e:	e8 ad d3 ff ff       	call   24d0 <open@plt>
    5123:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    5126:	85 c0                	test   %eax,%eax
    5128:	0f 88 88 d4 ff ff    	js     25b6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    512e:	48 89 da             	mov    %rbx,%rdx
    5131:	48 89 ee             	mov    %rbp,%rsi
    5134:	89 c7                	mov    %eax,%edi
    5136:	e8 a5 d2 ff ff       	call   23e0 <read@plt>
    if (ret < file_size) {
    513b:	48 98                	cltq
    513d:	48 39 d8             	cmp    %rbx,%rax
    5140:	7c 1e                	jl     5160 <copy_file_contents+0x70>
    close(fd);
    5142:	44 89 e7             	mov    %r12d,%edi
    5145:	e8 76 d2 ff ff       	call   23c0 <close@plt>
    iov->iov_base = buf;
    514a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    514e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    5152:	48 83 c4 08          	add    $0x8,%rsp
    5156:	5b                   	pop    %rbx
    5157:	5d                   	pop    %rbp
    5158:	41 5c                	pop    %r12
    515a:	41 5d                	pop    %r13
    515c:	c3                   	ret
    515d:	0f 1f 00             	nopl   (%rax)
    5160:	48 8b 0d b9 5e 00 00 	mov    0x5eb9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5167:	ba 1a 00 00 00       	mov    $0x1a,%edx
    516c:	be 01 00 00 00       	mov    $0x1,%esi
    5171:	48 8d 3d 79 2f 00 00 	lea    0x2f79(%rip),%rdi        # 80f1 <_IO_stdin_used+0xf1>
    5178:	e8 a3 d3 ff ff       	call   2520 <fwrite@plt>
    517d:	eb c3                	jmp    5142 <copy_file_contents+0x52>
    517f:	48 8b 0d 9a 5e 00 00 	mov    0x5e9a(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5186:	ba 28 00 00 00       	mov    $0x28,%edx
    518b:	be 01 00 00 00       	mov    $0x1,%esi
    5190:	48 8d 3d 21 34 00 00 	lea    0x3421(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    5197:	e8 84 d3 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    519c:	bf 01 00 00 00       	mov    $0x1,%edi
    51a1:	e8 5a d3 ff ff       	call   2500 <exit@plt>
    51a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000051b0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    51b0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    51b4:	8b 46 44             	mov    0x44(%rsi),%eax
    51b7:	48 89 fa             	mov    %rdi,%rdx
    51ba:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    51bd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    51c3:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    51c6:	48 8b 07             	mov    (%rdi),%rax
    51c9:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    51cc:	f6 c1 02             	test   $0x2,%cl
    51cf:	74 00                	je     51d1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    51d1:	89 f0                	mov    %esi,%eax
    51d3:	44 29 c0             	sub    %r8d,%eax
    51d6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    51d9:	0f 82 e3 d3 ff ff    	jb     25c2 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    51df:	c1 e9 0a             	shr    $0xa,%ecx
    51e2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    51e6:	8b 47 44             	mov    0x44(%rdi),%eax
    51e9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    51ec:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    51ef:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    51f2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    51f5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    51f9:	d3 e0                	shl    %cl,%eax
    51fb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    51fe:	48 c1 e0 06          	shl    $0x6,%rax
    5202:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    5206:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    520c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    520f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    5213:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5219:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5221:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    5225:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    5228:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    522f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5237:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    523b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    523f:	e8 3c d1 ff ff       	call   2380 <io_uring_submit@plt>
}
    5244:	31 c0                	xor    %eax,%eax
    5246:	48 83 c4 08          	add    $0x8,%rsp
    524a:	c3                   	ret
    524b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005250 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    5250:	f3 0f 1e fa          	endbr64
    5254:	41 55                	push   %r13
    5256:	41 89 fd             	mov    %edi,%r13d
    5259:	41 54                	push   %r12
    525b:	55                   	push   %rbp
    525c:	53                   	push   %rbx
    525d:	48 89 f3             	mov    %rsi,%rbx
    5260:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    5264:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5267:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    526d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    5270:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5273:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5275:	f6 c1 02             	test   $0x2,%cl
    5278:	74 00                	je     527a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    527a:	89 c2                	mov    %eax,%edx
    527c:	29 f2                	sub    %esi,%edx
    527e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5281:	0f 82 4b d3 ff ff    	jb     25d2 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5287:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    528a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    528d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5290:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    5295:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5298:	23 6b 58             	and    0x58(%rbx),%ebp
    529b:	d3 e5                	shl    %cl,%ebp
    529d:	48 c1 e5 06          	shl    $0x6,%rbp
    52a1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    52a5:	e8 b6 d1 ff ff       	call   2460 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    52aa:	be 01 00 00 00       	mov    $0x1,%esi
    52af:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    52b4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    52b7:	e8 34 d1 ff ff       	call   23f0 <calloc@plt>
    req->client_socket = client_socket;
    52bc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    52c1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    52c5:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    52c8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    52cd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    52d2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    52db:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    52e3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    52e7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    52eb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    52f2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    52fa:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    52fe:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    5306:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    530e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    5312:	e8 69 d0 ff ff       	call   2380 <io_uring_submit@plt>
}
    5317:	48 83 c4 08          	add    $0x8,%rsp
    531b:	31 c0                	xor    %eax,%eax
    531d:	5b                   	pop    %rbx
    531e:	5d                   	pop    %rbp
    531f:	41 5c                	pop    %r12
    5321:	41 5d                	pop    %r13
    5323:	c3                   	ret
    5324:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    532f:	90                   	nop

0000000000005330 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5330:	f3 0f 1e fa          	endbr64
    5334:	41 56                	push   %r14
    5336:	41 89 f6             	mov    %esi,%r14d
    5339:	41 55                	push   %r13
    533b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    533e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5343:	41 54                	push   %r12
    5345:	55                   	push   %rbp
    5346:	48 89 d5             	mov    %rdx,%rbp
    5349:	53                   	push   %rbx
    void *buf = malloc(size);
    534a:	e8 11 d1 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    534f:	48 85 c0             	test   %rax,%rax
    5352:	0f 84 dd 00 00 00    	je     5435 <_send_static_string_content+0x105>
    5358:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    535b:	4c 89 ef             	mov    %r13,%rdi
    535e:	e8 fd cf ff ff       	call   2360 <strlen@plt>
    req->iovec_count = 1;
    5363:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    536a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    536e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    5371:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    5374:	e8 e7 d0 ff ff       	call   2460 <malloc@plt>
    5379:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    537c:	48 85 c0             	test   %rax,%rax
    537f:	0f 84 b0 00 00 00    	je     5435 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    5385:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5389:	4c 89 e2             	mov    %r12,%rdx
    538c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    538f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    5393:	e8 98 d0 ff ff       	call   2430 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5398:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    539b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    53a1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    53a4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    53a8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    53aa:	f6 c1 02             	test   $0x2,%cl
    53ad:	0f 85 7d 00 00 00    	jne    5430 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    53b3:	89 d0                	mov    %edx,%eax
    53b5:	29 f0                	sub    %esi,%eax
    53b7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    53ba:	0f 82 1c d2 ff ff    	jb     25dc <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    53c0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53c3:	8b 45 44             	mov    0x44(%rbp),%eax
    53c6:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    53c9:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    53cc:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    53cf:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    53d2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    53d8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53dc:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    53de:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    53e1:	48 89 ef             	mov    %rbp,%rdi
    53e4:	48 c1 e0 06          	shl    $0x6,%rax
    53e8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    53ec:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    53ef:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    53f3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    53f9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5401:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    5405:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    5408:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    540f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5417:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    541b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    541f:	5b                   	pop    %rbx
    5420:	5d                   	pop    %rbp
    5421:	41 5c                	pop    %r12
    5423:	41 5d                	pop    %r13
    5425:	41 5e                	pop    %r14
    io_uring_submit(ring);
    5427:	e9 54 cf ff ff       	jmp    2380 <io_uring_submit@plt>
    542c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    5430:	e9 7e ff ff ff       	jmp    53b3 <_send_static_string_content+0x83>
    5435:	48 8b 0d e4 5b 00 00 	mov    0x5be4(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    543c:	ba 28 00 00 00       	mov    $0x28,%edx
    5441:	be 01 00 00 00       	mov    $0x1,%esi
    5446:	48 8d 3d 6b 31 00 00 	lea    0x316b(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    544d:	e8 ce d0 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5452:	bf 01 00 00 00       	mov    $0x1,%edi
    5457:	e8 a4 d0 ff ff       	call   2500 <exit@plt>
    545c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005460 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    5460:	f3 0f 1e fa          	endbr64
    5464:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5467:	89 fe                	mov    %edi,%esi
    5469:	48 8b 3d a8 5b 00 00 	mov    0x5ba8(%rip),%rdi        # b018 <unimplemented_content>
    5470:	e9 bb fe ff ff       	jmp    5330 <_send_static_string_content>
    5475:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005480 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    5480:	f3 0f 1e fa          	endbr64
    5484:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    5487:	89 fe                	mov    %edi,%esi
    5489:	48 8b 3d 80 5b 00 00 	mov    0x5b80(%rip),%rdi        # b010 <http_404_content>
    5490:	e9 9b fe ff ff       	jmp    5330 <_send_static_string_content>
    5495:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000054a0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    54a0:	f3 0f 1e fa          	endbr64
    54a4:	41 56                	push   %r14
    54a6:	41 55                	push   %r13
    54a8:	49 89 d5             	mov    %rdx,%r13
    54ab:	41 54                	push   %r12
    54ad:	41 89 f4             	mov    %esi,%r12d
    54b0:	55                   	push   %rbp
    54b1:	48 89 fd             	mov    %rdi,%rbp
    54b4:	53                   	push   %rbx
    54b5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    54bc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    54c5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    54cd:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    54cf:	e8 8c ce ff ff       	call   2360 <strlen@plt>
    54d4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    54d9:	48 89 c3             	mov    %rax,%rbx
    54dc:	0f 84 b6 00 00 00    	je     5598 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    54e2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    54e7:	48 89 ee             	mov    %rbp,%rsi
    54ea:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    54ee:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    54f3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    54fb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5503:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    550e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5516:	e8 f5 ce ff ff       	call   2410 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    551b:	48 89 e6             	mov    %rsp,%rsi
    551e:	4c 89 f7             	mov    %r14,%rdi
    5521:	e8 fa ce ff ff       	call   2420 <stat@plt>
    5526:	83 f8 ff             	cmp    $0xffffffff,%eax
    5529:	0f 84 d3 00 00 00    	je     5602 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    552f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5533:	25 00 f0 00 00       	and    $0xf000,%eax
    5538:	3d 00 80 00 00       	cmp    $0x8000,%eax
    553d:	0f 84 f5 00 00 00    	je     5638 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    5543:	48 8b 3d c6 5a 00 00 	mov    0x5ac6(%rip),%rdi        # b010 <http_404_content>
    554a:	4c 89 ea             	mov    %r13,%rdx
    554d:	44 89 e6             	mov    %r12d,%esi
    5550:	e8 db fd ff ff       	call   5330 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5555:	4c 89 f2             	mov    %r14,%rdx
    5558:	bf 01 00 00 00       	mov    $0x1,%edi
    555d:	31 c0                	xor    %eax,%eax
    555f:	48 8d 35 db 2b 00 00 	lea    0x2bdb(%rip),%rsi        # 8141 <_IO_stdin_used+0x141>
    5566:	e8 35 cf ff ff       	call   24a0 <__printf_chk@plt>
}
    556b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5573:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    557c:	0f 85 20 01 00 00    	jne    56a2 <handle_get_method+0x202>
    5582:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5589:	5b                   	pop    %rbx
    558a:	5d                   	pop    %rbp
    558b:	41 5c                	pop    %r12
    558d:	41 5d                	pop    %r13
    558f:	41 5e                	pop    %r14
    5591:	c3                   	ret
    5592:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5598:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    559d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    55a5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    55aa:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    55ad:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    55b5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    55b8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    55c0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    55cb:	e8 40 ce ff ff       	call   2410 <__memcpy_chk@plt>
    55d0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    55d5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    55da:	48 8d 35 2b 2b 00 00 	lea    0x2b2b(%rip),%rsi        # 810c <_IO_stdin_used+0x10c>
    55e1:	48 29 d9             	sub    %rbx,%rcx
    55e4:	ba 0b 00 00 00       	mov    $0xb,%edx
    55e9:	e8 22 ce ff ff       	call   2410 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    55ee:	48 89 e6             	mov    %rsp,%rsi
    55f1:	4c 89 f7             	mov    %r14,%rdi
    55f4:	e8 27 ce ff ff       	call   2420 <stat@plt>
    55f9:	83 f8 ff             	cmp    $0xffffffff,%eax
    55fc:	0f 85 2d ff ff ff    	jne    552f <handle_get_method+0x8f>
    5602:	4c 89 f2             	mov    %r14,%rdx
    5605:	48 89 e9             	mov    %rbp,%rcx
    5608:	48 8d 35 08 2b 00 00 	lea    0x2b08(%rip),%rsi        # 8117 <_IO_stdin_used+0x117>
    560f:	31 c0                	xor    %eax,%eax
    5611:	bf 01 00 00 00       	mov    $0x1,%edi
    5616:	e8 85 ce ff ff       	call   24a0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    561b:	48 8b 3d ee 59 00 00 	mov    0x59ee(%rip),%rdi        # b010 <http_404_content>
    5622:	4c 89 ea             	mov    %r13,%rdx
    5625:	44 89 e6             	mov    %r12d,%esi
    5628:	e8 03 fd ff ff       	call   5330 <_send_static_string_content>
}
    562d:	e9 39 ff ff ff       	jmp    556b <handle_get_method+0xcb>
    5632:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5638:	bf 70 00 00 00       	mov    $0x70,%edi
    563d:	e8 1e ce ff ff       	call   2460 <malloc@plt>
    5642:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5645:	48 85 c0             	test   %rax,%rax
    5648:	74 5d                	je     56a7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    564a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    564e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5653:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5657:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    565a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    5661:	e8 5a f5 ff ff       	call   4bc0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5666:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    566b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    566f:	4c 89 f7             	mov    %r14,%rdi
    5672:	e8 79 fa ff ff       	call   50f0 <copy_file_contents>
    5677:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    567c:	4c 89 f2             	mov    %r14,%rdx
    567f:	31 c0                	xor    %eax,%eax
    5681:	48 8d 35 a7 2a 00 00 	lea    0x2aa7(%rip),%rsi        # 812f <_IO_stdin_used+0x12f>
    5688:	bf 01 00 00 00       	mov    $0x1,%edi
    568d:	e8 0e ce ff ff       	call   24a0 <__printf_chk@plt>
            add_write_request(req, ring);
    5692:	4c 89 ee             	mov    %r13,%rsi
    5695:	48 89 df             	mov    %rbx,%rdi
    5698:	e8 13 fb ff ff       	call   51b0 <add_write_request>
    569d:	e9 c9 fe ff ff       	jmp    556b <handle_get_method+0xcb>
}
    56a2:	e8 c9 cc ff ff       	call   2370 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    56a7:	48 8b 0d 72 59 00 00 	mov    0x5972(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    56ae:	ba 28 00 00 00       	mov    $0x28,%edx
    56b3:	be 01 00 00 00       	mov    $0x1,%esi
    56b8:	48 8d 3d f9 2e 00 00 	lea    0x2ef9(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    56bf:	e8 5c ce ff ff       	call   2520 <fwrite@plt>
        exit(1);
    56c4:	bf 01 00 00 00       	mov    $0x1,%edi
    56c9:	e8 32 ce ff ff       	call   2500 <exit@plt>
    56ce:	66 90                	xchg   %ax,%ax

00000000000056d0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    56d0:	f3 0f 1e fa          	endbr64
    56d4:	41 57                	push   %r15
    56d6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    56d8:	4c 8d 35 c7 29 00 00 	lea    0x29c7(%rip),%r14        # 80a6 <_IO_stdin_used+0xa6>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    56df:	41 55                	push   %r13
    56e1:	49 89 d5             	mov    %rdx,%r13
    56e4:	41 54                	push   %r12
    56e6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    56e9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    56ec:	55                   	push   %rbp
    56ed:	53                   	push   %rbx
    56ee:	48 83 ec 18          	sub    $0x18,%rsp
    56f2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    56fb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5700:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5702:	49 89 e7             	mov    %rsp,%r15
    5705:	4c 89 fa             	mov    %r15,%rdx
    5708:	e8 c3 cc ff ff       	call   23d0 <strtok_r@plt>
    for (; *str; ++str)
    570d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    5711:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    5714:	84 db                	test   %bl,%bl
    5716:	74 1d                	je     5735 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    5718:	e8 53 ce ff ff       	call   2570 <__ctype_tolower_loc@plt>
    571d:	48 89 ea             	mov    %rbp,%rdx
    5720:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    5723:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    5727:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    572a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    572d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5731:	84 db                	test   %bl,%bl
    5733:	75 eb                	jne    5720 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    5735:	4c 89 fa             	mov    %r15,%rdx
    5738:	4c 89 f6             	mov    %r14,%rsi
    573b:	31 ff                	xor    %edi,%edi
    573d:	e8 8e cc ff ff       	call   23d0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5742:	48 8d 35 0b 2a 00 00 	lea    0x2a0b(%rip),%rsi        # 8154 <_IO_stdin_used+0x154>
    5749:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    574c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    574f:	e8 ac cc ff ff       	call   2400 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    5754:	4c 89 ea             	mov    %r13,%rdx
    5757:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    575a:	85 c0                	test   %eax,%eax
    575c:	75 2a                	jne    5788 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    575e:	48 89 df             	mov    %rbx,%rdi
    5761:	e8 3a fd ff ff       	call   54a0 <handle_get_method>
}
    5766:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    576b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5774:	75 20                	jne    5796 <handle_http_method+0xc6>
    5776:	48 83 c4 18          	add    $0x18,%rsp
    577a:	5b                   	pop    %rbx
    577b:	5d                   	pop    %rbp
    577c:	41 5c                	pop    %r12
    577e:	41 5d                	pop    %r13
    5780:	41 5e                	pop    %r14
    5782:	41 5f                	pop    %r15
    5784:	c3                   	ret
    5785:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5788:	48 8b 3d 89 58 00 00 	mov    0x5889(%rip),%rdi        # b018 <unimplemented_content>
    578f:	e8 9c fb ff ff       	call   5330 <_send_static_string_content>
}
    5794:	eb d0                	jmp    5766 <handle_http_method+0x96>
    5796:	e8 d5 cb ff ff       	call   2370 <__stack_chk_fail@plt>
    579b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000057a0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    57a0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    57a4:	85 d2                	test   %edx,%edx
    57a6:	7e 38                	jle    57e0 <get_line+0x40>
    57a8:	48 63 d2             	movslq %edx,%rdx
    57ab:	48 83 c7 01          	add    $0x1,%rdi
    57af:	48 01 f2             	add    %rsi,%rdx
    57b2:	eb 11                	jmp    57c5 <get_line+0x25>
    57b4:	0f 1f 40 00          	nopl   0x0(%rax)
    57b8:	48 83 c6 01          	add    $0x1,%rsi
    57bc:	48 83 c7 01          	add    $0x1,%rdi
    57c0:	48 39 d6             	cmp    %rdx,%rsi
    57c3:	74 1b                	je     57e0 <get_line+0x40>
        dest[i] = src[i];
    57c5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    57c9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    57cb:	3c 0d                	cmp    $0xd,%al
    57cd:	75 e9                	jne    57b8 <get_line+0x18>
    57cf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    57d2:	75 e4                	jne    57b8 <get_line+0x18>
            dest[i] = '\0';
    57d4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    57d7:	31 c0                	xor    %eax,%eax
    57d9:	c3                   	ret
    57da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    57e0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    57e5:	c3                   	ret
    57e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000057f0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    57f0:	f3 0f 1e fa          	endbr64
    57f4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    57fb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    57ff:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5808:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5810:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5812:	49 89 e2             	mov    %rsp,%r10
    5815:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    581d:	4c 89 d0             	mov    %r10,%rax
    5820:	eb 13                	jmp    5835 <handle_client_request+0x45>
    5822:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5828:	48 83 c0 01          	add    $0x1,%rax
    582c:	48 83 c1 01          	add    $0x1,%rcx
    5830:	4c 39 c8             	cmp    %r9,%rax
    5833:	74 4b                	je     5880 <handle_client_request+0x90>
        dest[i] = src[i];
    5835:	44 0f b6 01          	movzbl (%rcx),%r8d
    5839:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    583c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5840:	75 e6                	jne    5828 <handle_client_request+0x38>
    5842:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5846:	75 e0                	jne    5828 <handle_client_request+0x38>
            dest[i] = '\0';
    5848:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    584b:	8b 47 08             	mov    0x8(%rdi),%eax
    584e:	48 89 f2             	mov    %rsi,%rdx
    5851:	4c 89 d7             	mov    %r10,%rdi
    5854:	89 c6                	mov    %eax,%esi
    5856:	e8 75 fe ff ff       	call   56d0 <handle_http_method>
}
    585b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5863:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    586c:	75 39                	jne    58a7 <handle_client_request+0xb7>
    586e:	31 c0                	xor    %eax,%eax
    5870:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5877:	c3                   	ret
    5878:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5880:	48 8b 0d 99 57 00 00 	mov    0x5799(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5887:	ba 12 00 00 00       	mov    $0x12,%edx
    588c:	be 01 00 00 00       	mov    $0x1,%esi
    5891:	48 8d 3d c0 28 00 00 	lea    0x28c0(%rip),%rdi        # 8158 <_IO_stdin_used+0x158>
    5898:	e8 83 cc ff ff       	call   2520 <fwrite@plt>
        exit(1);
    589d:	bf 01 00 00 00       	mov    $0x1,%edi
    58a2:	e8 59 cc ff ff       	call   2500 <exit@plt>
}
    58a7:	e8 c4 ca ff ff       	call   2370 <__stack_chk_fail@plt>
    58ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000058b0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    58b0:	f3 0f 1e fa          	endbr64
    58b4:	55                   	push   %rbp
    58b5:	53                   	push   %rbx
    58b6:	48 89 cb             	mov    %rcx,%rbx
    58b9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    58bd:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    58c0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    58c3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    58c9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    58cc:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    58cf:	f6 c1 02             	test   $0x2,%cl
    58d2:	74 00                	je     58d4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    58d4:	41 89 c0             	mov    %eax,%r8d
    58d7:	45 29 c8             	sub    %r9d,%r8d
    58da:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    58de:	0f 82 08 cd ff ff    	jb     25ec <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    58e4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    58e7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    58ea:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    58ed:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    58f0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    58f3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    58f7:	d3 e5                	shl    %cl,%ebp
    58f9:	48 c1 e5 06          	shl    $0x6,%rbp
    58fd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5901:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5904:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5909:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5910:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5914:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5918:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    5920:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    5928:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    592c:	e8 2f cb ff ff       	call   2460 <malloc@plt>
  io_uring_submit(ring);
    5931:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5934:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    593a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    593e:	48 83 c4 08          	add    $0x8,%rsp
    5942:	5b                   	pop    %rbx
    5943:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5944:	e9 37 ca ff ff       	jmp    2380 <io_uring_submit@plt>
    5949:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005950 <io_thread>:
void* io_thread(void *arg) {
    5950:	f3 0f 1e fa          	endbr64
    5954:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5956:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5958:	41 56                	push   %r14
    595a:	41 55                	push   %r13
    595c:	41 54                	push   %r12
    595e:	55                   	push   %rbp
    595f:	48 89 fd             	mov    %rdi,%rbp
    5962:	53                   	push   %rbx
    5963:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    596a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5973:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    597b:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    597f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5984:	bf 00 01 00 00       	mov    $0x100,%edi
    5989:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    598c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5990:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5995:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    599a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    599f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    59a4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    59ac:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    59b1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    59b9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    59be:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    59c6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    59cb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    59d3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    59d8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    59e0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    59e5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    59ed:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    59f5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    59fd:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5a05:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    5a0d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5a15:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5a1d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5a25:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5a2d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5a35:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5a3d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5a44:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5a4c:	e8 ef c9 ff ff       	call   2440 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5a51:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5a55:	31 f6                	xor    %esi,%esi
    5a57:	e8 e4 ca ff ff       	call   2540 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    5a5c:	31 d2                	xor    %edx,%edx
    5a5e:	be 01 00 00 00       	mov    $0x1,%esi
    5a63:	bf 02 00 00 00       	mov    $0x2,%edi
    5a68:	e8 23 cb ff ff       	call   2590 <socket@plt>
  if (sock == -1)
    5a6d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5a70:	0f 84 b8 cb ff ff    	je     262e <io_thread.cold+0x38>
  if (setsockopt(sock,
    5a76:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5a7b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5a81:	89 c7                	mov    %eax,%edi
    5a83:	41 89 c4             	mov    %eax,%r12d
    5a86:	ba 02 00 00 00       	mov    $0x2,%edx
    5a8b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5a90:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5a98:	e8 93 c8 ff ff       	call   2330 <setsockopt@plt>
    5a9d:	85 c0                	test   %eax,%eax
    5a9f:	0f 88 5d cb ff ff    	js     2602 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5aa5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    5aaa:	ba 10 00 00 00       	mov    $0x10,%edx
    5aaf:	44 89 e7             	mov    %r12d,%edi
    5ab2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5abb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5ac3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    5acb:	e8 e0 c9 ff ff       	call   24b0 <bind@plt>
    5ad0:	85 c0                	test   %eax,%eax
    5ad2:	0f 88 62 cb ff ff    	js     263a <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5ad8:	be 0a 00 00 00       	mov    $0xa,%esi
    5add:	44 89 e7             	mov    %r12d,%edi
    5ae0:	e8 8b c9 ff ff       	call   2470 <listen@plt>
    5ae5:	85 c0                	test   %eax,%eax
    5ae7:	0f 88 21 cb ff ff    	js     260e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5aed:	ba db 18 00 00       	mov    $0x18db,%edx
    5af2:	48 8d 35 a4 26 00 00 	lea    0x26a4(%rip),%rsi        # 819d <_IO_stdin_used+0x19d>
    5af9:	bf 01 00 00 00       	mov    $0x1,%edi
    5afe:	31 c0                	xor    %eax,%eax
    5b00:	e8 9b c9 ff ff       	call   24a0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5b05:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5b0a:	48 89 d9             	mov    %rbx,%rcx
    5b0d:	44 89 e7             	mov    %r12d,%edi
    5b10:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5b15:	48 89 c6             	mov    %rax,%rsi
    5b18:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5b1d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5b22:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5b2a:	e8 81 fd ff ff       	call   58b0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5b2f:	bf 01 00 00 00       	mov    $0x1,%edi
    5b34:	be 10 00 00 00       	mov    $0x10,%esi
    5b39:	e8 b2 c8 ff ff       	call   23f0 <calloc@plt>
    void *buf = malloc(size);
    5b3e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5b43:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5b46:	e8 15 c9 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    5b4b:	48 85 c0             	test   %rax,%rax
    5b4e:	0f 84 ae 04 00 00    	je     6002 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5b54:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5b58:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5b5f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5b66:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5b6e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5b71:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5b76:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5b78:	f6 c1 02             	test   $0x2,%cl
    5b7b:	0f 85 0f 04 00 00    	jne    5f90 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5b81:	89 d0                	mov    %edx,%eax
    5b83:	29 f0                	sub    %esi,%eax
    5b85:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5b8c:	0f 82 92 ca ff ff    	jb     2624 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5b92:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5b95:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5b99:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5b9d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5ba0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5ba7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5baa:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5bb1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5bb8:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5bba:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5bbd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5bc2:	48 c1 e0 06          	shl    $0x6,%rax
    5bc6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5bce:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5bd4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5bd7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5bdf:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5be3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5beb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5bf3:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5bf7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5bfb:	e8 80 c7 ff ff       	call   2380 <io_uring_submit@plt>
  while (data->running == 1) {
    5c00:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5c04:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5c09:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5c11:	0f 85 d7 01 00 00    	jne    5dee <io_thread+0x49e>
    5c17:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5c1c:	4d 89 ce             	mov    %r9,%r14
    5c1f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5c24:	0f 1f 40 00          	nopl   0x0(%rax)
    5c28:	48 8d 3d 84 25 00 00 	lea    0x2584(%rip),%rdi        # 81b3 <_IO_stdin_used+0x1b3>
    5c2f:	e8 ec c6 ff ff       	call   2320 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5c34:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5c3b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5c42:	c1 e9 0b             	shr    $0xb,%ecx
    5c45:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5c48:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5c50:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5c52:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5c5a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5c5c:	39 d0                	cmp    %edx,%eax
    5c5e:	74 36                	je     5c96 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5c60:	89 f8                	mov    %edi,%eax
    5c62:	21 d0                	and    %edx,%eax
    5c64:	d3 e0                	shl    %cl,%eax
    5c66:	48 c1 e0 04          	shl    $0x4,%rax
    5c6a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5c72:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5c7a:	0f 85 a8 01 00 00    	jne    5e28 <io_thread+0x4d8>
    5c80:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5c84:	0f 85 0e 03 00 00    	jne    5f98 <io_thread+0x648>
			if (cqe->res < 0)
    5c8a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5c8d:	83 c2 01             	add    $0x1,%edx
    5c90:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5c92:	85 c0                	test   %eax,%eax
    5c94:	79 b2                	jns    5c48 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5c96:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    5c9f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5ca0:	45 31 c0             	xor    %r8d,%r8d
    5ca3:	31 d2                	xor    %edx,%edx
    5ca5:	b9 01 00 00 00       	mov    $0x1,%ecx
    5caa:	4c 89 f6             	mov    %r14,%rsi
    5cad:	48 89 df             	mov    %rbx,%rdi
    5cb0:	e8 db c7 ff ff       	call   2490 <__io_uring_get_cqe@plt>
    5cb5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5cb8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5cbd:	48 83 38 01          	cmpq   $0x1,(%rax)
    5cc1:	0f 84 e1 02 00 00    	je     5fa8 <io_thread+0x658>
    5cc7:	48 8d 3d 0b 25 00 00 	lea    0x250b(%rip),%rdi        # 81d9 <_IO_stdin_used+0x1d9>
    5cce:	e8 4d c6 ff ff       	call   2320 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5cd3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5cd8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5cdb:	45 85 ff             	test   %r15d,%r15d
    5cde:	0f 88 12 c9 ff ff    	js     25f6 <io_thread.cold>
      if (cqe->res < 0) {
    5ce4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5ce7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    5ceb:	85 c0                	test   %eax,%eax
    5ced:	0f 88 d5 02 00 00    	js     5fc8 <io_thread+0x678>
      switch (req->event_type) {
    5cf3:	41 83 f8 01          	cmp    $0x1,%r8d
    5cf7:	0f 84 7b 01 00 00    	je     5e78 <io_thread+0x528>
    5cfd:	41 83 f8 02          	cmp    $0x2,%r8d
    5d01:	0f 84 a1 01 00 00    	je     5ea8 <io_thread+0x558>
    5d07:	45 85 c0             	test   %r8d,%r8d
    5d0a:	0f 85 50 01 00 00    	jne    5e60 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5d10:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5d15:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5d1a:	48 89 d9             	mov    %rbx,%rcx
    5d1d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5d21:	e8 8a fb ff ff       	call   58b0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5d26:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5d2b:	48 89 de             	mov    %rbx,%rsi
    5d2e:	8b 78 08             	mov    0x8(%rax),%edi
    5d31:	e8 1a f5 ff ff       	call   5250 <add_read_request>
              free(req);
    5d36:	4c 89 e7             	mov    %r12,%rdi
    5d39:	e8 b2 c5 ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5d3e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5d43:	48 85 c0             	test   %rax,%rax
    5d46:	0f 85 14 01 00 00    	jne    5e60 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    5d4c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5d53:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5d5a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5d5d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5d62:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5d64:	f6 c1 02             	test   $0x2,%cl
    5d67:	74 00                	je     5d69 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5d69:	89 d0                	mov    %edx,%eax
    5d6b:	29 f0                	sub    %esi,%eax
    5d6d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5d74:	0f 82 a0 c8 ff ff    	jb     261a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5d7a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    5d7d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5d82:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5d86:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d89:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5d90:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d93:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5d9a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5da1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5da3:	8b 55 60             	mov    0x60(%rbp),%edx
    5da6:	48 c1 e0 06          	shl    $0x6,%rax
    5daa:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5db2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5db8:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5dbb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5dc3:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5dc7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5dcf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5dd7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5ddb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5ddf:	e8 9c c5 ff ff       	call   2380 <io_uring_submit@plt>
  while (data->running == 1) {
    5de4:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5de8:	0f 84 3a fe ff ff    	je     5c28 <io_thread+0x2d8>
    5dee:	48 8d 3d 1d 24 00 00 	lea    0x241d(%rip),%rdi        # 8212 <_IO_stdin_used+0x212>
    5df5:	e8 26 c5 ff ff       	call   2320 <puts@plt>
}
    5dfa:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5e02:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5e0b:	0f 85 18 02 00 00    	jne    6029 <io_thread+0x6d9>
    5e11:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5e18:	31 c0                	xor    %eax,%eax
    5e1a:	5b                   	pop    %rbx
    5e1b:	5d                   	pop    %rbp
    5e1c:	41 5c                	pop    %r12
    5e1e:	41 5d                	pop    %r13
    5e20:	41 5e                	pop    %r14
    5e22:	41 5f                	pop    %r15
    5e24:	c3                   	ret
    5e25:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5e28:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5e2d:	48 85 c0             	test   %rax,%rax
    5e30:	0f 84 6a fe ff ff    	je     5ca0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5e36:	48 83 38 01          	cmpq   $0x1,(%rax)
    5e3a:	0f 84 68 01 00 00    	je     5fa8 <io_thread+0x658>
    5e40:	48 8d 3d 92 23 00 00 	lea    0x2392(%rip),%rdi        # 81d9 <_IO_stdin_used+0x1d9>
    5e47:	e8 d4 c4 ff ff       	call   2320 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5e4c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5e51:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5e54:	e9 8b fe ff ff       	jmp    5ce4 <io_thread+0x394>
    5e59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5e60:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5e68:	8b 02                	mov    (%rdx),%eax
    5e6a:	83 c0 01             	add    $0x1,%eax
    5e6d:	89 02                	mov    %eax,(%rdx)
}
    5e6f:	e9 d8 fe ff ff       	jmp    5d4c <io_thread+0x3fc>
    5e74:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5e78:	85 c0                	test   %eax,%eax
    5e7a:	75 74                	jne    5ef0 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5e7c:	48 8b 0d 9d 51 00 00 	mov    0x519d(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5e83:	ba 0f 00 00 00       	mov    $0xf,%edx
    5e88:	be 01 00 00 00       	mov    $0x1,%esi
    5e8d:	48 8d 3d 6e 23 00 00 	lea    0x236e(%rip),%rdi        # 8202 <_IO_stdin_used+0x202>
    5e94:	e8 87 c6 ff ff       	call   2520 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5e99:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5e9e:	e9 a0 fe ff ff       	jmp    5d43 <io_thread+0x3f3>
    5ea3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5ea8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5ead:	45 31 ff             	xor    %r15d,%r15d
    5eb0:	85 c0                	test   %eax,%eax
    5eb2:	7e 20                	jle    5ed4 <io_thread+0x584>
    5eb4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5eb8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5ebb:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    5ebf:	48 c1 e0 04          	shl    $0x4,%rax
    5ec3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5ec8:	e8 23 c4 ff ff       	call   22f0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5ecd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5ed2:	7f e4                	jg     5eb8 <io_thread+0x568>
              close(req->client_socket);
    5ed4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5ed9:	e8 e2 c4 ff ff       	call   23c0 <close@plt>
              free(req);
    5ede:	4c 89 e7             	mov    %r12,%rdi
    5ee1:	e8 0a c4 ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5ee6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5eeb:	e9 53 fe ff ff       	jmp    5d43 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5ef0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5ef5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5efa:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5f02:	eb 11                	jmp    5f15 <io_thread+0x5c5>
    5f04:	0f 1f 40 00          	nopl   0x0(%rax)
    5f08:	48 83 c0 01          	add    $0x1,%rax
    5f0c:	48 83 c2 01          	add    $0x1,%rdx
    5f10:	48 39 c6             	cmp    %rax,%rsi
    5f13:	74 4b                	je     5f60 <io_thread+0x610>
        dest[i] = src[i];
    5f15:	0f b6 0a             	movzbl (%rdx),%ecx
    5f18:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5f1a:	80 f9 0d             	cmp    $0xd,%cl
    5f1d:	75 e9                	jne    5f08 <io_thread+0x5b8>
    5f1f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5f23:	75 e3                	jne    5f08 <io_thread+0x5b8>
            dest[i] = '\0';
    5f25:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5f28:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    5f2d:	48 89 da             	mov    %rbx,%rdx
    5f30:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5f35:	e8 96 f7 ff ff       	call   56d0 <handle_http_method>
              free(req->iov[0].iov_base);
    5f3a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    5f3f:	e8 ac c3 ff ff       	call   22f0 <free@plt>
              free(req);
    5f44:	4c 89 e7             	mov    %r12,%rdi
    5f47:	e8 a4 c3 ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5f4c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5f51:	e9 ed fd ff ff       	jmp    5d43 <io_thread+0x3f3>
    5f56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5f60:	48 8b 0d b9 50 00 00 	mov    0x50b9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5f67:	ba 12 00 00 00       	mov    $0x12,%edx
    5f6c:	be 01 00 00 00       	mov    $0x1,%esi
    5f71:	48 8d 3d e0 21 00 00 	lea    0x21e0(%rip),%rdi        # 8158 <_IO_stdin_used+0x158>
    5f78:	e8 a3 c5 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5f7d:	bf 01 00 00 00       	mov    $0x1,%edi
    5f82:	e8 79 c5 ff ff       	call   2500 <exit@plt>
    5f87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5f90:	e9 ec fb ff ff       	jmp    5b81 <io_thread+0x231>
    5f95:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5f98:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    5f9d:	e9 94 fe ff ff       	jmp    5e36 <io_thread+0x4e6>
    5fa2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5fa8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5fb0:	48 8d 3d 0e 22 00 00 	lea    0x220e(%rip),%rdi        # 81c5 <_IO_stdin_used+0x1c5>
    5fb7:	8b 02                	mov    (%rdx),%eax
    5fb9:	83 c0 01             	add    $0x1,%eax
    5fbc:	89 02                	mov    %eax,(%rdx)
    5fbe:	e8 5d c3 ff ff       	call   2320 <puts@plt>
    5fc3:	e9 26 fe ff ff       	jmp    5dee <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5fc8:	f7 d8                	neg    %eax
    5fca:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5fcf:	89 c7                	mov    %eax,%edi
    5fd1:	e8 8a c5 ff ff       	call   2560 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5fd6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5fdb:	be 01 00 00 00       	mov    $0x1,%esi
    5fe0:	48 8b 3d 39 50 00 00 	mov    0x5039(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    5fe7:	48 89 c1             	mov    %rax,%rcx
    5fea:	48 8d 15 f7 25 00 00 	lea    0x25f7(%rip),%rdx        # 85e8 <_IO_stdin_used+0x5e8>
    5ff1:	31 c0                	xor    %eax,%eax
    5ff3:	e8 38 c5 ff ff       	call   2530 <__fprintf_chk@plt>
          exit(1);
    5ff8:	bf 01 00 00 00       	mov    $0x1,%edi
    5ffd:	e8 fe c4 ff ff       	call   2500 <exit@plt>
    6002:	48 8b 0d 17 50 00 00 	mov    0x5017(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6009:	ba 28 00 00 00       	mov    $0x28,%edx
    600e:	be 01 00 00 00       	mov    $0x1,%esi
    6013:	48 8d 3d 9e 25 00 00 	lea    0x259e(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    601a:	e8 01 c5 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    601f:	bf 01 00 00 00       	mov    $0x1,%edi
    6024:	e8 d7 c4 ff ff       	call   2500 <exit@plt>
}
    6029:	e8 42 c3 ff ff       	call   2370 <__stack_chk_fail@plt>
    602e:	66 90                	xchg   %ax,%ax

0000000000006030 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    6030:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    6034:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    603b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    6041:	85 c9                	test   %ecx,%ecx
    6043:	0f 8e ea 00 00 00    	jle    6133 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    6049:	41 56                	push   %r14
    604b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    604d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    6050:	41 54                	push   %r12
    6052:	49 89 fc             	mov    %rdi,%r12
    6055:	55                   	push   %rbp
    6056:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    6057:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    605b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6060:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    6064:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    606c:	31 db                	xor    %ebx,%ebx
    606e:	8b 10                	mov    (%rax),%edx
    6070:	85 d2                	test   %edx,%edx
    6072:	7e 26                	jle    609a <barriered_work_ingest+0x6a>
    6074:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    6078:	48 89 dd             	mov    %rbx,%rbp
    607b:	48 c1 e5 08          	shl    $0x8,%rbp
    607f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    6083:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    608a:	74 24                	je     60b0 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    608c:	48 83 c3 01          	add    $0x1,%rbx
    6090:	39 da                	cmp    %ebx,%edx
    6092:	7f e4                	jg     6078 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    6094:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    609a:	49 83 c5 01          	add    $0x1,%r13
    609e:	44 39 e9             	cmp    %r13d,%ecx
    60a1:	7f bd                	jg     6060 <barriered_work_ingest+0x30>
}
    60a3:	5b                   	pop    %rbx
    60a4:	31 c0                	xor    %eax,%eax
    60a6:	5d                   	pop    %rbp
    60a7:	41 5c                	pop    %r12
    60a9:	41 5d                	pop    %r13
    60ab:	41 5e                	pop    %r14
    60ad:	c3                   	ret
    60ae:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    60b0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    60b9:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    60c0:	bf 04 00 00 00       	mov    $0x4,%edi
    60c5:	48 c1 e6 05          	shl    $0x5,%rsi
    60c9:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    60d0:	48 83 c6 10          	add    $0x10,%rsi
    60d4:	e8 67 c2 ff ff       	call   2340 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    60d9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    60e1:	48 8b 40 50          	mov    0x50(%rax),%rax
    60e5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    60e9:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    60ed:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    60f7:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    60fd:	83 c0 01             	add    $0x1,%eax
    6100:	99                   	cltd
    6101:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    6107:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    610d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    6110:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    6118:	48 83 c3 01          	add    $0x1,%rbx
    611c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    6120:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    6124:	8b 10                	mov    (%rax),%edx
    6126:	39 da                	cmp    %ebx,%edx
    6128:	0f 8f 46 ff ff ff    	jg     6074 <barriered_work_ingest+0x44>
    612e:	e9 61 ff ff ff       	jmp    6094 <barriered_work_ingest+0x64>
}
    6133:	31 c0                	xor    %eax,%eax
    6135:	c3                   	ret
    6136:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006140 <barriered_thread>:
void* barriered_thread(void *arg) {
    6140:	f3 0f 1e fa          	endbr64
    6144:	41 56                	push   %r14
    6146:	41 55                	push   %r13
    6148:	41 54                	push   %r12
  int t = 0;
    614a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    614d:	55                   	push   %rbp
  int waiting = 0;
    614e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    6150:	53                   	push   %rbx
    6151:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    6154:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6158:	0f 85 74 02 00 00    	jne    63d2 <barriered_thread+0x292>
    if (t >= data->task_count) {
    615e:	8b 43 40             	mov    0x40(%rbx),%eax
    6161:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6168:	41 39 c4             	cmp    %eax,%r12d
    616b:	0f 8d 6f 01 00 00    	jge    62e0 <barriered_thread+0x1a0>
    6171:	49 63 fc             	movslq %r12d,%rdi
    6174:	48 c1 e7 09          	shl    $0x9,%rdi
    6178:	49 89 fd             	mov    %rdi,%r13
    617b:	eb 32                	jmp    61af <barriered_thread+0x6f>
    617d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    6180:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6184:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6188:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    618c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6190:	4c 01 ef             	add    %r13,%rdi
    6193:	e8 98 fe ff ff       	call   6030 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    6198:	8b 43 40             	mov    0x40(%rbx),%eax
    619b:	41 83 c4 01          	add    $0x1,%r12d
    619f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    61a6:	44 39 e0             	cmp    %r12d,%eax
    61a9:	0f 8e 19 02 00 00    	jle    63c8 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    61af:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    61b3:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    61b7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    61be:	75 c0                	jne    6180 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    61c0:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    61c4:	83 e8 01             	sub    $0x1,%eax
    61c7:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    61cc:	45 85 e4             	test   %r12d,%r12d
    61cf:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    61d2:	45 85 c0             	test   %r8d,%r8d
    61d5:	0f 8e 2d 01 00 00    	jle    6308 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    61db:	48 63 c8             	movslq %eax,%rcx
    61de:	48 8b 43 18          	mov    0x18(%rbx),%rax
    61e2:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    61e5:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    61eb:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    61f2:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    61f6:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    61f9:	45 31 f6             	xor    %r14d,%r14d
    61fc:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6200:	48 8b 10             	mov    (%rax),%rdx
    6203:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6207:	49 01 cb             	add    %rcx,%r11
    620a:	4c 89 da             	mov    %r11,%rdx
    620d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6214:	75 04                	jne    621a <barriered_thread+0xda>
            arrived++;
    6216:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    621a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    6220:	75 04                	jne    6226 <barriered_thread+0xe6>
            prearrive++;
    6222:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6226:	48 83 c0 08          	add    $0x8,%rax
    622a:	48 39 c6             	cmp    %rax,%rsi
    622d:	75 d1                	jne    6200 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    622f:	45 85 d2             	test   %r10d,%r10d
    6232:	0f 84 c0 00 00 00    	je     62f8 <barriered_thread+0x1b8>
    6238:	45 39 d0             	cmp    %r10d,%r8d
    623b:	0f 84 b7 00 00 00    	je     62f8 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    6241:	45 85 f6             	test   %r14d,%r14d
    6244:	74 0a                	je     6250 <barriered_thread+0x110>
    6246:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    624a:	0f 85 ae 01 00 00    	jne    63fe <barriered_thread+0x2be>
    6250:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    6254:	4c 01 ea             	add    %r13,%rdx
    6257:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    625e:	45 85 e4             	test   %r12d,%r12d
    6261:	75 14                	jne    6277 <barriered_thread+0x137>
    6263:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    626a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    6271:	0f 8c 69 01 00 00    	jl     63e0 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6277:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    627b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    627f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6289:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    628d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6291:	4c 01 ef             	add    %r13,%rdi
    6294:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    629a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    629e:	4c 01 e8             	add    %r13,%rax
    62a1:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    62a8:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    62ab:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    62b0:	83 e8 01             	sub    $0x1,%eax
    62b3:	44 39 e0             	cmp    %r12d,%eax
    62b6:	0f 84 a4 00 00 00    	je     6360 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    62bc:	0f ae f8             	sfence
          if (waiting == 0) {
    62bf:	85 ed                	test   %ebp,%ebp
    62c1:	0f 84 d1 00 00 00    	je     6398 <barriered_thread+0x258>
        int arrived = 0; 
    62c7:	bd 01 00 00 00       	mov    $0x1,%ebp
    62cc:	e9 c7 fe ff ff       	jmp    6198 <barriered_thread+0x58>
  while (data->running == 1) {
    62d1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    62d5:	0f 85 f7 00 00 00    	jne    63d2 <barriered_thread+0x292>
    62db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    62e0:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    62e8:	85 c0                	test   %eax,%eax
    62ea:	7e e5                	jle    62d1 <barriered_thread+0x191>
    62ec:	45 31 e4             	xor    %r12d,%r12d
    62ef:	e9 7d fe ff ff       	jmp    6171 <barriered_thread+0x31>
    62f4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    62f8:	83 fd 01             	cmp    $0x1,%ebp
    62fb:	74 1b                	je     6318 <barriered_thread+0x1d8>
        int arrived = 0; 
    62fd:	31 ed                	xor    %ebp,%ebp
    62ff:	e9 3d ff ff ff       	jmp    6241 <barriered_thread+0x101>
    6304:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6308:	83 fd 01             	cmp    $0x1,%ebp
    630b:	0f 85 43 ff ff ff    	jne    6254 <barriered_thread+0x114>
        int arrived = 0; 
    6311:	45 31 f6             	xor    %r14d,%r14d
    6314:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    6318:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    631f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    6324:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    6326:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    632a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6331:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    6336:	e8 05 c0 ff ff       	call   2340 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    633b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6342:	48 83 c0 01          	add    $0x1,%rax
    6346:	48 99                	cqto
    6348:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    634f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    6356:	e9 e6 fe ff ff       	jmp    6241 <barriered_thread+0x101>
    635b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6360:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6367:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    636e:	0f 8d 48 ff ff ff    	jge    62bc <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    6374:	48 c1 e6 04          	shl    $0x4,%rsi
    6378:	bf 04 00 00 00       	mov    $0x4,%edi
    637d:	48 03 73 70          	add    0x70(%rbx),%rsi
    6381:	e8 ba bf ff ff       	call   2340 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    6386:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    638e:	e9 29 ff ff ff       	jmp    62bc <barriered_thread+0x17c>
    6393:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    6398:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    639f:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    63a4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    63a8:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    63af:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    63b3:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    63b7:	e8 84 bf ff ff       	call   2340 <clock_gettime@plt>
            waiting = 1;
    63bc:	e9 06 ff ff ff       	jmp    62c7 <barriered_thread+0x187>
    63c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    63c8:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    63cc:	0f 84 96 fd ff ff    	je     6168 <barriered_thread+0x28>
}
    63d2:	5b                   	pop    %rbx
    63d3:	31 c0                	xor    %eax,%eax
    63d5:	5d                   	pop    %rbp
    63d6:	41 5c                	pop    %r12
    63d8:	41 5d                	pop    %r13
    63da:	41 5e                	pop    %r14
    63dc:	c3                   	ret
    63dd:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    63e0:	48 c1 e6 04          	shl    $0x4,%rsi
    63e4:	bf 04 00 00 00       	mov    $0x4,%edi
    63e9:	48 03 73 68          	add    0x68(%rbx),%rsi
    63ed:	e8 4e bf ff ff       	call   2340 <clock_gettime@plt>
          data->tasks[t].available = 0;
    63f2:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    63f6:	4c 01 ea             	add    %r13,%rdx
    63f9:	e9 79 fe ff ff       	jmp    6277 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    63fe:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6402:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6406:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    640a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    640e:	4c 01 ef             	add    %r13,%rdi
    6411:	e8 1a fc ff ff       	call   6030 <barriered_work_ingest>
          break;
    6416:	e9 39 fd ff ff       	jmp    6154 <barriered_thread+0x14>
    641b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006420 <receive>:
int receive(struct BarrierTask *data) {
    6420:	f3 0f 1e fa          	endbr64
    6424:	41 57                	push   %r15
    6426:	41 56                	push   %r14
    6428:	41 55                	push   %r13
    642a:	41 54                	push   %r12
    642c:	55                   	push   %rbp
    642d:	53                   	push   %rbx
    642e:	48 83 ec 18          	sub    $0x18,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6432:	44 8b b7 40 01 00 00 	mov    0x140(%rdi),%r14d
    6439:	45 85 f6             	test   %r14d,%r14d
    643c:	0f 8e 17 01 00 00    	jle    6559 <receive+0x139>
    if (n == data->thread->real_thread_index) { continue; }
    6442:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    6449:	48 89 f9             	mov    %rdi,%rcx
    644c:	45 31 e4             	xor    %r12d,%r12d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    644f:	31 db                	xor    %ebx,%ebx
    if (n == data->thread->real_thread_index) { continue; }
    6451:	48 63 68 08          	movslq 0x8(%rax),%rbp
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    6455:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    if (n == data->thread->real_thread_index) { continue; }
    645a:	49 89 ef             	mov    %rbp,%r15
    645d:	0f 1f 00             	nopl   (%rax)
    6460:	41 39 df             	cmp    %ebx,%r15d
    6463:	0f 84 e0 00 00 00    	je     6549 <receive+0x129>
    struct Data *me = data->mailboxes[n].lower;
    6469:	48 8b 81 70 01 00 00 	mov    0x170(%rcx),%rax
    6470:	4c 01 e0             	add    %r12,%rax
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    6473:	44 8b 68 30          	mov    0x30(%rax),%r13d
    struct Data *me = data->mailboxes[n].lower;
    6477:	48 8b 10             	mov    (%rax),%rdx
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    647a:	41 83 fd 02          	cmp    $0x2,%r13d
    647e:	0f 84 24 01 00 00    	je     65a8 <receive+0x188>
    for (int x = 0 ; x < me->messages_count ; x++) {
    6484:	48 83 ba 80 00 00 00 00 	cmpq   $0x0,0x80(%rdx)
    648c:	0f 8e 3b 01 00 00    	jle    65cd <receive+0x1ad>
      data->sends++;
    6492:	4c 8b 81 78 01 00 00 	mov    0x178(%rcx),%r8
      data->n++;
    6499:	48 8b b9 08 01 00 00 	mov    0x108(%rcx),%rdi
      me->received++;
    64a0:	31 c0                	xor    %eax,%eax
    64a2:	48 8b b2 10 03 00 00 	mov    0x310(%rdx),%rsi
      if (me->messages[x]->group == data->group) {
    64a9:	4c 8b 1a             	mov    (%rdx),%r11
    64ac:	4d 8d 48 01          	lea    0x1(%r8),%r9
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    64b0:	4c 63 51 04          	movslq 0x4(%rcx),%r10
    64b4:	4c 8d 47 01          	lea    0x1(%rdi),%r8
    64b8:	48 8d 7e 01          	lea    0x1(%rsi),%rdi
    64bc:	eb 0f                	jmp    64cd <receive+0xad>
    64be:	66 90                	xchg   %ax,%ax
    for (int x = 0 ; x < me->messages_count ; x++) {
    64c0:	48 83 c0 01          	add    $0x1,%rax
    64c4:	48 39 82 80 00 00 00 	cmp    %rax,0x80(%rdx)
    64cb:	7e 6b                	jle    6538 <receive+0x118>
      data->sends++;
    64cd:	49 8d 34 01          	lea    (%r9,%rax,1),%rsi
    64d1:	48 89 b1 78 01 00 00 	mov    %rsi,0x178(%rcx)
      data->n++;
    64d8:	49 8d 34 00          	lea    (%r8,%rax,1),%rsi
    64dc:	48 89 b1 08 01 00 00 	mov    %rsi,0x108(%rcx)
      me->received++;
    64e3:	48 8d 34 07          	lea    (%rdi,%rax,1),%rsi
    64e7:	48 89 b2 10 03 00 00 	mov    %rsi,0x310(%rdx)
      if (me->messages[x]->group == data->group) {
    64ee:	49 8b 34 c3          	mov    (%r11,%rax,8),%rsi
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    64f2:	4c 39 56 10          	cmp    %r10,0x10(%rsi)
    64f6:	75 c8                	jne    64c0 <receive+0xa0>
    64f8:	48 39 6e 08          	cmp    %rbp,0x8(%rsi)
    64fc:	75 c2                	jne    64c0 <receive+0xa0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    64fe:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6503:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6505:	bf 01 00 00 00       	mov    $0x1,%edi
    650a:	ba 01 00 00 00       	mov    $0x1,%edx
    650f:	48 8d 35 fa 20 00 00 	lea    0x20fa(%rip),%rsi        # 8610 <_IO_stdin_used+0x610>
    6516:	48 63 40 04          	movslq 0x4(%rax),%rax
    651a:	48 39 e8             	cmp    %rbp,%rax
    651d:	0f 94 c1             	sete   %cl
    6520:	31 c0                	xor    %eax,%eax
    6522:	e8 79 bf ff ff       	call   24a0 <__printf_chk@plt>
        exit(1);
    6527:	bf 01 00 00 00       	mov    $0x1,%edi
    652c:	e8 cf bf ff ff       	call   2500 <exit@plt>
    6531:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    me->messages_count = 0;
    6538:	48 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rdx)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    6543:	41 83 fd 02          	cmp    $0x2,%r13d
    6547:	74 27                	je     6570 <receive+0x150>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6549:	83 c3 01             	add    $0x1,%ebx
    654c:	49 83 c4 38          	add    $0x38,%r12
    6550:	44 39 f3             	cmp    %r14d,%ebx
    6553:	0f 85 07 ff ff ff    	jne    6460 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    6559:	0f ae f8             	sfence
}
    655c:	48 83 c4 18          	add    $0x18,%rsp
    6560:	31 c0                	xor    %eax,%eax
    6562:	5b                   	pop    %rbx
    6563:	5d                   	pop    %rbp
    6564:	41 5c                	pop    %r12
    6566:	41 5d                	pop    %r13
    6568:	41 5e                	pop    %r14
    656a:	41 5f                	pop    %r15
    656c:	c3                   	ret
    656d:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    6570:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    6576:	83 f8 01             	cmp    $0x1,%eax
    6579:	75 ce                	jne    6549 <receive+0x129>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    657b:	83 c3 01             	add    $0x1,%ebx
    657e:	49 83 c4 38          	add    $0x38,%r12
      me->available_reading = 0;
    6582:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    658c:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6596:	44 39 f3             	cmp    %r14d,%ebx
    6599:	0f 85 c1 fe ff ff    	jne    6460 <receive+0x40>
    659f:	eb b8                	jmp    6559 <receive+0x139>
    65a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    65a8:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    65ae:	85 c0                	test   %eax,%eax
    65b0:	74 97                	je     6549 <receive+0x129>
    for (int x = 0 ; x < me->messages_count ; x++) {
    65b2:	48 83 ba 80 00 00 00 00 	cmpq   $0x0,0x80(%rdx)
    65ba:	0f 8f d2 fe ff ff    	jg     6492 <receive+0x72>
    me->messages_count = 0;
    65c0:	48 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rdx)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    65cb:	eb a9                	jmp    6576 <receive+0x156>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    65cd:	83 c3 01             	add    $0x1,%ebx
    65d0:	49 83 c4 38          	add    $0x38,%r12
    me->messages_count = 0;
    65d4:	48 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    65df:	44 39 f3             	cmp    %r14d,%ebx
    65e2:	0f 85 78 fe ff ff    	jne    6460 <receive+0x40>
    65e8:	e9 6c ff ff ff       	jmp    6559 <receive+0x139>
    65ed:	0f 1f 00             	nopl   (%rax)

00000000000065f0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    65f0:	f3 0f 1e fa          	endbr64
    65f4:	41 57                	push   %r15
    65f6:	41 56                	push   %r14
    65f8:	41 55                	push   %r13
    65fa:	49 89 fd             	mov    %rdi,%r13
    65fd:	41 54                	push   %r12
    65ff:	55                   	push   %rbp
    6600:	53                   	push   %rbx
    6601:	48 83 ec 68          	sub    $0x68,%rsp
  if (data->thread_index == data->task_index) {
    6605:	8b 47 04             	mov    0x4(%rdi),%eax
    6608:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    660e:	74 4b                	je     665b <barriered_work+0x6b>
    receive(data);
    6610:	e8 0b fe ff ff       	call   6420 <receive>
    while (data->scheduled == 1) {
    6615:	41 83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r13)
    661d:	75 16                	jne    6635 <barriered_work+0x45>
    661f:	90                   	nop
      data->n++;
    6620:	49 83 85 08 01 00 00 01 	addq   $0x1,0x108(%r13)
      asm volatile ("sfence" ::: "memory");
    6628:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    662b:	41 83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r13)
    6633:	74 eb                	je     6620 <barriered_work+0x30>
  if (data->sending == 1) {
    6635:	41 83 bd 80 01 00 00 01 	cmpl   $0x1,0x180(%r13)
    663d:	75 08                	jne    6647 <barriered_work+0x57>
    663f:	4c 89 ef             	mov    %r13,%rdi
    6642:	e8 19 e2 ff ff       	call   4860 <sendm.part.0>
  asm volatile ("sfence" ::: "memory");
    6647:	0f ae f8             	sfence
}
    664a:	48 83 c4 68          	add    $0x68,%rsp
    664e:	31 c0                	xor    %eax,%eax
    6650:	5b                   	pop    %rbx
    6651:	5d                   	pop    %rbp
    6652:	41 5c                	pop    %r12
    6654:	41 5d                	pop    %r13
    6656:	41 5e                	pop    %r14
    6658:	41 5f                	pop    %r15
    665a:	c3                   	ret
       receive(data);
    665b:	e8 c0 fd ff ff       	call   6420 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6660:	41 8b bd 40 01 00 00 	mov    0x140(%r13),%edi
        int t = data->task_index;
    6667:	41 8b 45 04          	mov    0x4(%r13),%eax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    666b:	85 ff                	test   %edi,%edi
    666d:	0f 8e 26 04 00 00    	jle    6a99 <barriered_work+0x4a9>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    6673:	48 63 d0             	movslq %eax,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
    6676:	83 c0 01             	add    $0x1,%eax
    6679:	89 7c 24 50          	mov    %edi,0x50(%rsp)
    667d:	4c 63 ff             	movslq %edi,%r15
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    6680:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    6689:	48 c1 e2 09          	shl    $0x9,%rdx
    668d:	4d 8b 95 28 01 00 00 	mov    0x128(%r13),%r10
    6694:	4d 89 ec             	mov    %r13,%r12
    6697:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    66a0:	49 89 d6             	mov    %rdx,%r14
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    66a3:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
              int next_task = abs((t + 1) % (data->thread_count));
    66ab:	89 44 24 2c          	mov    %eax,0x2c(%rsp)
    66af:	90                   	nop
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    66b0:	8b 7c 24 28          	mov    0x28(%rsp),%edi
int barriered_work(struct BarrierTask *data) {
    66b4:	45 31 ed             	xor    %r13d,%r13d
    66b7:	31 c9                	xor    %ecx,%ecx
    66b9:	4d 89 f1             	mov    %r14,%r9
    66bc:	eb 16                	jmp    66d4 <barriered_work+0xe4>
    66be:	66 90                	xchg   %ax,%ax
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    66c0:	48 83 c1 01          	add    $0x1,%rcx
    66c4:	49 81 c5 c8 00 00 00 	add    $0xc8,%r13
    66cb:	49 39 cf             	cmp    %rcx,%r15
    66ce:	0f 84 94 02 00 00    	je     6968 <barriered_work+0x378>
              if (y == b) { continue; }
    66d4:	39 cf                	cmp    %ecx,%edi
    66d6:	74 e8                	je     66c0 <barriered_work+0xd0>
              int next_task = abs((t + 1) % (data->thread_count));
    66d8:	41 8b b4 24 34 01 00 00 	mov    0x134(%r12),%esi
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    66e0:	41 39 4a 08          	cmp    %ecx,0x8(%r10)
    66e4:	75 da                	jne    66c0 <barriered_work+0xd0>
    66e6:	49 8b 42 20          	mov    0x20(%r10),%rax
    66ea:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    66ef:	4e 8b 5c 28 38       	mov    0x38(%rax,%r13,1),%r11
    66f4:	4b 03 9c 0b 70 01 00 00 	add    0x170(%r11,%r9,1),%rbx
    66fc:	83 7b 30 02          	cmpl   $0x2,0x30(%rbx)
    6700:	75 be                	jne    66c0 <barriered_work+0xd0>
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    6702:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
    6707:	4c 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r8
    670f:	49 29 c8             	sub    %rcx,%r8
    6712:	48 8b 44 10 38       	mov    0x38(%rax,%rdx,1),%rax
    6717:	49 c1 e0 03          	shl    $0x3,%r8
    671b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    6720:	85 f6                	test   %esi,%esi
    6722:	7e 76                	jle    679a <barriered_work+0x1aa>
    6724:	48 63 ee             	movslq %esi,%rbp
                  int all_wrote = 1;
    6727:	89 74 24 10          	mov    %esi,0x10(%rsp)
    672b:	49 89 c6             	mov    %rax,%r14
    672e:	ba 01 00 00 00       	mov    $0x1,%edx
    6733:	48 c1 e5 09          	shl    $0x9,%rbp
    6737:	48 01 c5             	add    %rax,%rbp
    673a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
                    if (((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving == 0) {
    6740:	48 8b b0 70 01 00 00 	mov    0x170(%rax),%rsi
    6747:	4a 8b 74 06 08       	mov    0x8(%rsi,%r8,1),%rsi
                      all_wrote = 0;
    674c:	8b b6 80 01 00 00    	mov    0x180(%rsi),%esi
    6752:	85 f6                	test   %esi,%esi
    6754:	be 00 00 00 00       	mov    $0x0,%esi
    6759:	0f 44 d6             	cmove  %esi,%edx
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    675c:	48 05 00 02 00 00    	add    $0x200,%rax
    6762:	48 39 c5             	cmp    %rax,%rbp
    6765:	75 d9                	jne    6740 <barriered_work+0x150>
                  if (all_finished == 1 && all_wrote == 1 /*&& ((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available == 0 */) {
    6767:	8b 74 24 10          	mov    0x10(%rsp),%esi
    676b:	83 fa 01             	cmp    $0x1,%edx
    676e:	0f 85 4c ff ff ff    	jne    66c0 <barriered_work+0xd0>
    6774:	0f 1f 40 00          	nopl   0x0(%rax)
                        ((struct Data*)data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving = 0;
    6778:	49 8b 86 70 01 00 00 	mov    0x170(%r14),%rax
                      for (int nn = 0 ; nn < data->thread_count; nn++) {
    677f:	49 81 c6 00 02 00 00 	add    $0x200,%r14
                        ((struct Data*)data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving = 0;
    6786:	4a 8b 44 00 08       	mov    0x8(%rax,%r8,1),%rax
    678b:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
                      for (int nn = 0 ; nn < data->thread_count; nn++) {
    6795:	4c 39 f5             	cmp    %r14,%rbp
    6798:	75 de                	jne    6778 <barriered_work+0x188>
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    679a:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    679f:	4a 8b 84 0d 70 01 00 00 	mov    0x170(%rbp,%r9,1),%rax
    67a7:	4e 8b 54 00 18       	mov    0x18(%rax,%r8,1),%r10
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    67ac:	48 8b 43 18          	mov    0x18(%rbx),%rax
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    67b0:	4d 8b 32             	mov    (%r10),%r14
    67b3:	4c 89 74 24 30       	mov    %r14,0x30(%rsp)
                      void * right = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1];
    67b8:	4d 8b 72 08          	mov    0x8(%r10),%r14
    67bc:	4c 89 74 24 38       	mov    %r14,0x38(%rsp)
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    67c1:	4c 8b 30             	mov    (%rax),%r14
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    67c4:	48 8b 40 08          	mov    0x8(%rax),%rax
    67c8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              int next_task = abs((t + 1) % (data->thread_count));
    67cd:	8b 44 24 2c          	mov    0x2c(%rsp),%eax
    67d1:	99                   	cltd
    67d2:	f7 fe                	idiv   %esi
    67d4:	89 d0                	mov    %edx,%eax
    67d6:	f7 d8                	neg    %eax
    67d8:	0f 48 c2             	cmovs  %edx,%eax
    mailbox->lower = data;
    67db:	48 8b 53 08          	mov    0x8(%rbx),%rdx
                      void * left2 = data->thread->all_threads[b].tasks[next_task].mailboxes[y].stack[0];
    67df:	48 98                	cltq
                      struct Data* a = ((struct Data*) data->thread->all_threads[y].tasks[next_task].mailboxes[b].higher);
    67e1:	48 c1 e0 09          	shl    $0x9,%rax
    67e5:	48 8b ac 05 70 01 00 00 	mov    0x170(%rbp,%rax,1),%rbp
    67ed:	4c 01 c5             	add    %r8,%rbp
    return mailbox->higher;
    67f0:	f3 0f 6f 45 00       	movdqu 0x0(%rbp),%xmm0
    mailbox->lower = data;
    67f5:	48 89 55 00          	mov    %rdx,0x0(%rbp)
    return mailbox->lower;
    67f9:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
    mailbox->lower = data;
    67fe:	0f 11 03             	movups %xmm0,(%rbx)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6801:	85 f6                	test   %esi,%esi
    6803:	0f 8e 5a 03 00 00    	jle    6b63 <barriered_work+0x573>
    6809:	48 63 c6             	movslq %esi,%rax
    680c:	4c 89 4c 24 40       	mov    %r9,0x40(%rsp)
    6811:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6816:	ba 70 01 00 00       	mov    $0x170,%edx
    681b:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    6820:	48 c1 e0 09          	shl    $0x9,%rax
    6824:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    6829:	89 7c 24 54          	mov    %edi,0x54(%rsp)
    682d:	48 05 70 01 00 00    	add    $0x170,%rax
    6833:	4c 89 74 24 58       	mov    %r14,0x58(%rsp)
    6838:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    683d:	0f 1f 00             	nopl   (%rax)
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_reading = 0;
    6840:	49 8b 3c 13          	mov    (%r11,%rdx,1),%rdi
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_reading = 0;
    6844:	49 8b 34 16          	mov    (%r14,%rdx,1),%rsi
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_reading = 0;
    6848:	48 01 df             	add    %rbx,%rdi
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_reading = 0;
    684b:	4c 01 c6             	add    %r8,%rsi
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_reading = 0;
    684e:	4c 8b 57 08          	mov    0x8(%rdi),%r10
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_reading = 0;
    6852:	4c 8b 4e 08          	mov    0x8(%rsi),%r9
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->available_reading = 1;
    6856:	48 8b 3f             	mov    (%rdi),%rdi
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].lower)->available_reading = 1;
    6859:	48 8b 36             	mov    (%rsi),%rsi
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_reading = 0;
    685c:	41 c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%r10)
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_reading = 0;
    6867:	41 c7 81 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%r9)
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->available_reading = 1;
    6872:	c7 87 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdi)
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].lower)->available_reading = 1;
    687c:	c7 86 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rsi)
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_sending = 1;
    6886:	41 c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r10)
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_sending = 1;
    6891:	41 c7 81 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r9)
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    689c:	48 39 f7             	cmp    %rsi,%rdi
    689f:	0f 84 c8 02 00 00    	je     6b6d <barriered_work+0x57d>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    68a5:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    68ac:	48 39 d0             	cmp    %rdx,%rax
    68af:	75 8f                	jne    6840 <barriered_work+0x250>
    68b1:	48 89 6c 24 10       	mov    %rbp,0x10(%rsp)
    68b6:	4c 8b 4c 24 40       	mov    0x40(%rsp),%r9
    68bb:	48 89 ee             	mov    %rbp,%rsi
    68be:	4c 8b 54 24 48       	mov    0x48(%rsp),%r10
    68c3:	8b 7c 24 54          	mov    0x54(%rsp),%edi
    68c7:	4c 8b 74 24 58       	mov    0x58(%rsp),%r14
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0] = right;
    68cc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1] = left;
    68d1:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    68d6:	48 83 c1 01          	add    $0x1,%rcx
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0] = right;
    68da:	49 89 02             	mov    %rax,(%r10)
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1] = left;
    68dd:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    68e5:	48 8b 40 20          	mov    0x20(%rax),%rax
    68e9:	48 8b 44 10 38       	mov    0x38(%rax,%rdx,1),%rax
    68ee:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    68f3:	4a 8b 84 08 70 01 00 00 	mov    0x170(%rax,%r9,1),%rax
    68fb:	4a 8b 44 00 18       	mov    0x18(%rax,%r8,1),%rax
    6900:	48 89 50 08          	mov    %rdx,0x8(%rax)
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0] = right3;
    6904:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    690c:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    6911:	48 8b 40 20          	mov    0x20(%rax),%rax
    6915:	4a 8b 44 28 38       	mov    0x38(%rax,%r13,1),%rax
    691a:	4a 8b 84 08 70 01 00 00 	mov    0x170(%rax,%r9,1),%rax
    6922:	48 8b 44 10 18       	mov    0x18(%rax,%rdx,1),%rax
    6927:	48 89 30             	mov    %rsi,(%rax)
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1] = left3;
    692a:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    6932:	48 8b 40 20          	mov    0x20(%rax),%rax
    6936:	4a 8b 44 28 38       	mov    0x38(%rax,%r13,1),%rax
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    693b:	49 81 c5 c8 00 00 00 	add    $0xc8,%r13
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1] = left3;
    6942:	4a 8b 84 08 70 01 00 00 	mov    0x170(%rax,%r9,1),%rax
    694a:	48 8b 44 10 18       	mov    0x18(%rax,%rdx,1),%rax
    694f:	4c 89 70 08          	mov    %r14,0x8(%rax)
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6953:	4d 8b 94 24 28 01 00 00 	mov    0x128(%r12),%r10
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    695b:	49 39 cf             	cmp    %rcx,%r15
    695e:	0f 85 70 fd ff ff    	jne    66d4 <barriered_work+0xe4>
    6964:	0f 1f 40 00          	nopl   0x0(%rax)
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6968:	49 63 8a c4 00 00 00 	movslq 0xc4(%r10),%rcx
          int k = data->group;
    696f:	41 8b b4 24 94 01 00 00 	mov    0x194(%r12),%esi
    6977:	4d 89 ce             	mov    %r9,%r14
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    697a:	85 c9                	test   %ecx,%ecx
    697c:	0f 8e f0 00 00 00    	jle    6a72 <barriered_work+0x482>
              int next_task = abs((t + 1) % (data->thread_count));
    6982:	8b 44 24 2c          	mov    0x2c(%rsp),%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6986:	4d 89 d1             	mov    %r10,%r9
              int next_task = abs((t + 1) % (data->thread_count));
    6989:	99                   	cltd
    698a:	41 f7 bc 24 34 01 00 00 	idivl  0x134(%r12)
    6992:	89 d0                	mov    %edx,%eax
    6994:	f7 d8                	neg    %eax
    6996:	0f 49 d0             	cmovns %eax,%edx
            int y = (k * data->thread->threads_per_group) + d;
    6999:	0f af f1             	imul   %ecx,%esi
              int next_task = abs((t + 1) % (data->thread_count));
    699c:	48 63 da             	movslq %edx,%rbx
    699f:	48 63 c6             	movslq %esi,%rax
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    69a2:	48 c1 e3 09          	shl    $0x9,%rbx
    69a6:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    69aa:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    69b2:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    69b7:	48 8d 34 92          	lea    (%rdx,%rdx,4),%rsi
    69bb:	48 29 c5             	sub    %rax,%rbp
    69be:	49 8b 52 20          	mov    0x20(%r10),%rdx
    69c2:	48 01 c8             	add    %rcx,%rax
    69c5:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    69cd:	48 c1 e5 03          	shl    $0x3,%rbp
    69d1:	4c 8d 2c f2          	lea    (%rdx,%rsi,8),%r13
    69d5:	48 29 c1             	sub    %rax,%rcx
    69d8:	49 89 eb             	mov    %rbp,%r11
    69db:	48 c1 e1 03          	shl    $0x3,%rcx
    69df:	4d 89 e8             	mov    %r13,%r8
    69e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    69e8:	4d 8b 50 38          	mov    0x38(%r8),%r10
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    69ec:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    69f1:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    69f6:	4c 89 ea             	mov    %r13,%rdx
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    69f9:	4b 8b b4 32 70 01 00 00 	mov    0x170(%r10,%r14,1),%rsi
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6a01:	49 01 c2             	add    %rax,%r10
    6a04:	48 89 e8             	mov    %rbp,%rax
    6a07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
              if (kind == MAILBOX_FRIEND) {
    6a10:	83 7c 06 30 01       	cmpl   $0x1,0x30(%rsi,%rax,1)
    6a15:	75 2f                	jne    6a46 <barriered_work+0x456>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    6a17:	48 8b 7a 38          	mov    0x38(%rdx),%rdi
    6a1b:	4a 8b 9c 37 70 01 00 00 	mov    0x170(%rdi,%r14,1),%rbx
    6a23:	4c 01 db             	add    %r11,%rbx
    6a26:	48 89 df             	mov    %rbx,%rdi
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6a29:	49 8b 9a 70 01 00 00 	mov    0x170(%r10),%rbx
    mailbox->lower = data;
    6a30:	4c 8b 47 08          	mov    0x8(%rdi),%r8
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6a34:	48 01 c3             	add    %rax,%rbx
    return mailbox->higher;
    6a37:	f3 0f 6f 03          	movdqu (%rbx),%xmm0
    mailbox->lower = data;
    6a3b:	4c 89 03             	mov    %r8,(%rbx)
    return mailbox->lower;
    6a3e:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
    mailbox->lower = data;
    6a43:	0f 11 07             	movups %xmm0,(%rdi)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6a46:	48 83 c0 38          	add    $0x38,%rax
    6a4a:	48 81 c2 c8 00 00 00 	add    $0xc8,%rdx
    6a51:	48 39 c1             	cmp    %rax,%rcx
    6a54:	75 ba                	jne    6a10 <barriered_work+0x420>
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6a56:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    6a5b:	49 83 c3 38          	add    $0x38,%r11
    6a5f:	49 81 c0 c8 00 00 00 	add    $0xc8,%r8
    6a66:	49 39 cb             	cmp    %rcx,%r11
    6a69:	0f 85 79 ff ff ff    	jne    69e8 <barriered_work+0x3f8>
    6a6f:	4d 89 ca             	mov    %r9,%r10
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6a72:	83 44 24 28 01       	addl   $0x1,0x28(%rsp)
    6a77:	8b 54 24 50          	mov    0x50(%rsp),%edx
    6a7b:	8b 44 24 28          	mov    0x28(%rsp),%eax
    6a7f:	48 83 44 24 18 38    	addq   $0x38,0x18(%rsp)
    6a85:	48 81 44 24 20 c8 00 00 00 	addq   $0xc8,0x20(%rsp)
    6a8e:	39 d0                	cmp    %edx,%eax
    6a90:	0f 85 1a fc ff ff    	jne    66b0 <barriered_work+0xc0>
    6a96:	4d 89 e5             	mov    %r12,%r13
      asm volatile ("sfence" ::: "memory");
    6a99:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6a9c:	49 8b b5 60 01 00 00 	mov    0x160(%r13),%rsi
    6aa3:	31 ff                	xor    %edi,%edi
    6aa5:	48 c1 e6 05          	shl    $0x5,%rsi
    6aa9:	49 03 b5 50 01 00 00 	add    0x150(%r13),%rsi
    6ab0:	e8 8b b8 ff ff       	call   2340 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6ab5:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
    while (data->scheduled == 1) {
    6abc:	41 83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r13)
    int modcount = ++data->thread->protected_state->modcount;
    6ac4:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6ac8:	8b 7a 10             	mov    0x10(%rdx),%edi
    6acb:	8d 5f 01             	lea    0x1(%rdi),%ebx
    6ace:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    6ad1:	75 53                	jne    6b26 <barriered_work+0x536>
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6ad3:	49 63 95 30 01 00 00 	movslq 0x130(%r13),%rdx
    6ada:	48 8b 40 18          	mov    0x18(%rax),%rax
    6ade:	49 63 7d 04          	movslq 0x4(%r13),%rdi
      data->n++;
    6ae2:	49 83 85 08 01 00 00 01 	addq   $0x1,0x108(%r13)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6aea:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6aee:	48 c1 e7 09          	shl    $0x9,%rdi
    6af2:	48 03 78 38          	add    0x38(%rax),%rdi
    6af6:	41 ff 95 20 01 00 00 	call   *0x120(%r13)
      asm volatile ("sfence" ::: "memory");
    6afd:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6b00:	41 83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r13)
    if (modcount != data->thread->protected_state->modcount) {
    6b08:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
    while (data->scheduled == 1) {
    6b0f:	74 c2                	je     6ad3 <barriered_work+0x4e3>
    if (modcount != data->thread->protected_state->modcount) {
    6b11:	48 8b 40 48          	mov    0x48(%rax),%rax
    6b15:	3b 58 10             	cmp    0x10(%rax),%ebx
    6b18:	74 0c                	je     6b26 <barriered_work+0x536>
    6b1a:	48 8d 3d 1f 17 00 00 	lea    0x171f(%rip),%rdi        # 8240 <_IO_stdin_used+0x240>
    6b21:	e8 fa b7 ff ff       	call   2320 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6b26:	49 8b b5 60 01 00 00 	mov    0x160(%r13),%rsi
    6b2d:	31 ff                	xor    %edi,%edi
    6b2f:	48 c1 e6 05          	shl    $0x5,%rsi
    6b33:	49 03 b5 50 01 00 00 	add    0x150(%r13),%rsi
    6b3a:	48 83 c6 10          	add    $0x10,%rsi
    6b3e:	e8 fd b7 ff ff       	call   2340 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6b43:	49 8b 85 60 01 00 00 	mov    0x160(%r13),%rax
    6b4a:	48 83 c0 01          	add    $0x1,%rax
    6b4e:	48 99                	cqto
    6b50:	49 f7 bd 58 01 00 00 	idivq  0x158(%r13)
    6b57:	49 89 95 60 01 00 00 	mov    %rdx,0x160(%r13)
    6b5e:	e9 d2 fa ff ff       	jmp    6635 <barriered_work+0x45>
    6b63:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    6b68:	e9 5f fd ff ff       	jmp    68cc <barriered_work+0x2dc>
    6b6d:	bf 01 00 00 00       	mov    $0x1,%edi
    6b72:	48 8d 35 ac 16 00 00 	lea    0x16ac(%rip),%rsi        # 8225 <_IO_stdin_used+0x225>
    6b79:	31 c0                	xor    %eax,%eax
    6b7b:	e8 20 b9 ff ff       	call   24a0 <__printf_chk@plt>
                          exit(1);
    6b80:	bf 01 00 00 00       	mov    $0x1,%edi
    6b85:	e8 76 b9 ff ff       	call   2500 <exit@plt>
    6b8a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000006b90 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6b90:	f3 0f 1e fa          	endbr64
    6b94:	53                   	push   %rbx
    6b95:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6b98:	e8 93 f4 ff ff       	call   6030 <barriered_work_ingest>
  barriered_work(data);
    6b9d:	48 89 df             	mov    %rbx,%rdi
}
    6ba0:	5b                   	pop    %rbx
  barriered_work(data);
    6ba1:	e9 4a fa ff ff       	jmp    65f0 <barriered_work>
    6ba6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006bb0 <sendm>:
int sendm(struct BarrierTask *data) {
    6bb0:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    6bb4:	83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%rdi)
    6bbb:	74 03                	je     6bc0 <sendm+0x10>
}
    6bbd:	31 c0                	xor    %eax,%eax
    6bbf:	c3                   	ret
int sendm(struct BarrierTask *data) {
    6bc0:	48 83 ec 08          	sub    $0x8,%rsp
    6bc4:	e8 97 dc ff ff       	call   4860 <sendm.part.0>
}
    6bc9:	31 c0                	xor    %eax,%eax
    6bcb:	48 83 c4 08          	add    $0x8,%rsp
    6bcf:	c3                   	ret

0000000000006bd0 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    6bd0:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6bd4:	85 f6                	test   %esi,%esi
    6bd6:	74 10                	je     6be8 <mailboxkind+0x18>
  return NULL;
    6bd8:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    6bda:	83 fe 01             	cmp    $0x1,%esi
    6bdd:	74 01                	je     6be0 <mailboxkind+0x10>
}
    6bdf:	c3                   	ret
    return mailbox->higher;
    6be0:	48 8b 47 08          	mov    0x8(%rdi),%rax
}
    6be4:	c3                   	ret
    6be5:	0f 1f 00             	nopl   (%rax)
    return mailbox->lower;
    6be8:	48 8b 07             	mov    (%rdi),%rax
    6beb:	c3                   	ret
    6bec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006bf0 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    6bf0:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6bf4:	85 d2                	test   %edx,%edx
    6bf6:	75 08                	jne    6c00 <setmailboxkind+0x10>
    mailbox->lower = data;
    6bf8:	48 89 37             	mov    %rsi,(%rdi)
}
    6bfb:	31 c0                	xor    %eax,%eax
    6bfd:	c3                   	ret
    6bfe:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    6c00:	83 fa 01             	cmp    $0x1,%edx
    6c03:	75 f6                	jne    6bfb <setmailboxkind+0xb>
    mailbox->higher = data;
    6c05:	48 89 77 08          	mov    %rsi,0x8(%rdi)
}
    6c09:	31 c0                	xor    %eax,%eax
    6c0b:	c3                   	ret
    6c0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006c10 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6c10:	f3 0f 1e fa          	endbr64
}
    6c14:	31 c0                	xor    %eax,%eax
    6c16:	c3                   	ret
    6c17:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006c20 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6c20:	f3 0f 1e fa          	endbr64
    6c24:	31 c0                	xor    %eax,%eax
    6c26:	c3                   	ret
    6c27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006c30 <after>:
int after(struct timespec left, struct timespec right) {
    6c30:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6c34:	31 c0                	xor    %eax,%eax
    6c36:	48 39 d7             	cmp    %rdx,%rdi
    6c39:	7e 08                	jle    6c43 <after+0x13>
    6c3b:	31 c0                	xor    %eax,%eax
    6c3d:	48 39 ce             	cmp    %rcx,%rsi
    6c40:	0f 9f c0             	setg   %al
}
    6c43:	c3                   	ret
    6c44:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6c4f:	90                   	nop

0000000000006c50 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6c50:	f3 0f 1e fa          	endbr64
    6c54:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6c59:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    6c5e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6c60:	48 39 d7             	cmp    %rdx,%rdi
    6c63:	7f 18                	jg     6c7d <within+0x2d>
    6c65:	4d 39 d8             	cmp    %r11,%r8
    6c68:	0f 9e c2             	setle  %dl
    6c6b:	48 39 ce             	cmp    %rcx,%rsi
    6c6e:	0f 9e c0             	setle  %al
    6c71:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6c73:	31 c0                	xor    %eax,%eax
    6c75:	4d 39 d1             	cmp    %r10,%r9
    6c78:	0f 9e c0             	setle  %al
    6c7b:	21 d0                	and    %edx,%eax
}
    6c7d:	c3                   	ret
    6c7e:	66 90                	xchg   %ax,%ax

0000000000006c80 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6c80:	f3 0f 1e fa          	endbr64
    6c84:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6c89:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    6c8e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6c93:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6c98:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    6c9d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6ca2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6ca7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    6cac:	48 39 fe             	cmp    %rdi,%rsi
    6caf:	7d 2f                	jge    6ce0 <overlap+0x60>
    6cb1:	48 39 ca             	cmp    %rcx,%rdx
    6cb4:	7d 62                	jge    6d18 <overlap+0x98>
    6cb6:	4d 39 da             	cmp    %r11,%r10
    6cb9:	7d 0e                	jge    6cc9 <overlap+0x49>
    return 1;
    6cbb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6cc0:	4d 39 c1             	cmp    %r8,%r9
    6cc3:	0f 8c 7f 00 00 00    	jl     6d48 <overlap+0xc8>
  return 0;
    6cc9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6ccb:	4d 39 c1             	cmp    %r8,%r9
    6cce:	7f 4c                	jg     6d1c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6cd0:	31 c0                	xor    %eax,%eax
    6cd2:	4d 39 da             	cmp    %r11,%r10
    6cd5:	0f 9e c0             	setle  %al
    6cd8:	c3                   	ret
    6cd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6ce0:	7e 4e                	jle    6d30 <overlap+0xb0>
    6ce2:	48 39 ca             	cmp    %rcx,%rdx
    6ce5:	7f 39                	jg     6d20 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6ce7:	75 31                	jne    6d1a <overlap+0x9a>
    6ce9:	4d 39 c1             	cmp    %r8,%r9
    6cec:	7c 2c                	jl     6d1a <overlap+0x9a>
    return 1;
    6cee:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6cf3:	4d 39 da             	cmp    %r11,%r10
    6cf6:	7d 24                	jge    6d1c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6cf8:	48 39 ca             	cmp    %rcx,%rdx
    6cfb:	0f 94 c2             	sete   %dl
    6cfe:	48 39 fe             	cmp    %rdi,%rsi
    6d01:	0f 94 c0             	sete   %al
    6d04:	21 c2                	and    %eax,%edx
    6d06:	31 c0                	xor    %eax,%eax
    6d08:	4d 39 c1             	cmp    %r8,%r9
    6d0b:	0f 94 c0             	sete   %al
    6d0e:	21 d0                	and    %edx,%eax
    6d10:	c3                   	ret
    6d11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6d18:	74 af                	je     6cc9 <overlap+0x49>
  return 0;
    6d1a:	31 c0                	xor    %eax,%eax
}
    6d1c:	c3                   	ret
    6d1d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6d20:	4d 39 da             	cmp    %r11,%r10
    6d23:	7e c4                	jle    6ce9 <overlap+0x69>
    return 1;
    6d25:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6d2a:	4d 39 c1             	cmp    %r8,%r9
    6d2d:	7e ba                	jle    6ce9 <overlap+0x69>
    6d2f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6d30:	48 39 ca             	cmp    %rcx,%rdx
    6d33:	7c 94                	jl     6cc9 <overlap+0x49>
    6d35:	4d 39 c1             	cmp    %r8,%r9
    6d38:	7d b4                	jge    6cee <overlap+0x6e>
    6d3a:	48 39 ca             	cmp    %rcx,%rdx
    6d3d:	74 91                	je     6cd0 <overlap+0x50>
    6d3f:	eb d9                	jmp    6d1a <overlap+0x9a>
    6d41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6d48:	c3                   	ret
    6d49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006d50 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6d50:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6d54:	85 f6                	test   %esi,%esi
    6d56:	0f 8e 44 03 00 00    	jle    70a0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    6d5c:	41 57                	push   %r15
    6d5e:	41 89 f7             	mov    %esi,%r15d
    6d61:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6d63:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6d66:	41 55                	push   %r13
    6d68:	41 54                	push   %r12
    6d6a:	55                   	push   %rbp
    6d6b:	53                   	push   %rbx
    6d6c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6d70:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6d74:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6d79:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    6d7e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6d81:	45 39 e6             	cmp    %r12d,%r14d
    6d84:	0f 84 4e 02 00 00    	je     6fd8 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6d8a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6d8f:	8b 50 08             	mov    0x8(%rax),%edx
    6d92:	85 d2                	test   %edx,%edx
    6d94:	0f 8e 3e 02 00 00    	jle    6fd8 <verify+0x288>
    6d9a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    6d9f:	31 c9                	xor    %ecx,%ecx
    6da1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    6da6:	31 c0                	xor    %eax,%eax
    6da8:	44 89 f2             	mov    %r14d,%edx
    6dab:	bf 01 00 00 00       	mov    $0x1,%edi
    6db0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6db5:	48 8d 35 94 14 00 00 	lea    0x1494(%rip),%rsi        # 8250 <_IO_stdin_used+0x250>
    6dbc:	e8 df b6 ff ff       	call   24a0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6dc1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6dc6:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    6dcb:	8b 40 08             	mov    0x8(%rax),%eax
    6dce:	85 c0                	test   %eax,%eax
    6dd0:	0f 8e e6 01 00 00    	jle    6fbc <verify+0x26c>
    6dd6:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6dd9:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    6dde:	31 db                	xor    %ebx,%ebx
    6de0:	48 c1 e0 09          	shl    $0x9,%rax
    6de4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6de9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    6dee:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6df3:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6df8:	4c 8b 20             	mov    (%rax),%r12
    6dfb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6e00:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6e05:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    6e0a:	49 89 de             	mov    %rbx,%r14
    6e0d:	48 8d 35 51 14 00 00 	lea    0x1451(%rip),%rsi        # 8265 <_IO_stdin_used+0x265>
    6e14:	49 c1 e6 09          	shl    $0x9,%r14
    6e18:	bf 01 00 00 00       	mov    $0x1,%edi
    6e1d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6e21:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    6e29:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    6e2e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    6e36:	31 c0                	xor    %eax,%eax
    6e38:	e8 63 b6 ff ff       	call   24a0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6e3d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6e42:	4c 8b 20             	mov    (%rax),%r12
    6e45:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    6e4e:	0f 8e 47 01 00 00    	jle    6f9b <verify+0x24b>
    6e54:	4c 03 75 00          	add    0x0(%rbp),%r14
    6e58:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6e5d:	ba 01 00 00 00       	mov    $0x1,%edx
    6e62:	4d 89 f5             	mov    %r14,%r13
    6e65:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6e6c:	4d 85 f6             	test   %r14,%r14
    6e6f:	0f 8e 21 01 00 00    	jle    6f96 <verify+0x246>
    6e75:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6e78:	48 89 d5             	mov    %rdx,%rbp
    6e7b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6e80:	31 db                	xor    %ebx,%ebx
    6e82:	4d 89 f2             	mov    %r14,%r10
    6e85:	48 c1 e5 05          	shl    $0x5,%rbp
    6e89:	48 83 ed 20          	sub    $0x20,%rbp
    6e8d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6e91:	49 89 ee             	mov    %rbp,%r14
    6e94:	48 89 dd             	mov    %rbx,%rbp
    6e97:	48 89 d3             	mov    %rdx,%rbx
    6e9a:	eb 31                	jmp    6ecd <verify+0x17d>
    6e9c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6ea0:	4c 39 c2             	cmp    %r8,%rdx
    6ea3:	0f 8d 57 01 00 00    	jge    7000 <verify+0x2b0>
    6ea9:	4c 39 df             	cmp    %r11,%rdi
    6eac:	7e 05                	jle    6eb3 <verify+0x163>
    6eae:	49 39 c1             	cmp    %rax,%r9
    6eb1:	7c 75                	jl     6f28 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6eb3:	4c 39 df             	cmp    %r11,%rdi
    6eb6:	0f 8d ab 01 00 00    	jge    7067 <verify+0x317>
    6ebc:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6ec0:	48 83 c5 01          	add    $0x1,%rbp
    6ec4:	49 39 ea             	cmp    %rbp,%r10
    6ec7:	0f 8e a9 00 00 00    	jle    6f76 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6ecd:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    6ed4:	48 89 e8             	mov    %rbp,%rax
    6ed7:	48 c1 e0 05          	shl    $0x5,%rax
    6edb:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    6ee2:	4c 01 f2             	add    %r14,%rdx
    6ee5:	48 8b 08             	mov    (%rax),%rcx
    6ee8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    6eec:	48 8b 32             	mov    (%rdx),%rsi
    6eef:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6ef3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6ef7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    6efb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    6eff:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6f03:	48 39 f1             	cmp    %rsi,%rcx
    6f06:	7c 98                	jl     6ea0 <verify+0x150>
    6f08:	0f 8e 42 01 00 00    	jle    7050 <verify+0x300>
    6f0e:	4c 39 c2             	cmp    %r8,%rdx
    6f11:	0f 8f f9 00 00 00    	jg     7010 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f17:	75 a7                	jne    6ec0 <verify+0x170>
    6f19:	4c 39 df             	cmp    %r11,%rdi
    6f1c:	7f a2                	jg     6ec0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6f1e:	49 39 c1             	cmp    %rax,%r9
    6f21:	7c 9d                	jl     6ec0 <verify+0x170>
    6f23:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6f28:	49 89 c1             	mov    %rax,%r9
    6f2b:	48 89 f9             	mov    %rdi,%rcx
    6f2e:	48 89 f2             	mov    %rsi,%rdx
    6f31:	bf 01 00 00 00       	mov    $0x1,%edi
    6f36:	48 8d 35 fb 16 00 00 	lea    0x16fb(%rip),%rsi        # 8638 <_IO_stdin_used+0x638>
    6f3d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6f3f:	48 83 c5 01          	add    $0x1,%rbp
    6f43:	e8 58 b5 ff ff       	call   24a0 <__printf_chk@plt>
    6f48:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6f4d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    6f52:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6f55:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6f5a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6f61:	4c 8b 20             	mov    (%rax),%r12
    6f64:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6f69:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6f6d:	49 39 ea             	cmp    %rbp,%r10
    6f70:	0f 8f 57 ff ff ff    	jg     6ecd <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6f76:	48 89 da             	mov    %rbx,%rdx
    6f79:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    6f80:	7d 14                	jge    6f96 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6f82:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6f89:	48 83 c2 01          	add    $0x1,%rdx
    6f8d:	4d 85 f6             	test   %r14,%r14
    6f90:	0f 8f e2 fe ff ff    	jg     6e78 <verify+0x128>
    6f96:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6f9b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6fa0:	48 83 c3 01          	add    $0x1,%rbx
    6fa4:	39 58 08             	cmp    %ebx,0x8(%rax)
    6fa7:	0f 8f 53 fe ff ff    	jg     6e00 <verify+0xb0>
    6fad:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6fb2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6fb7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6fbc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6fc1:	48 83 c1 01          	add    $0x1,%rcx
    6fc5:	39 48 08             	cmp    %ecx,0x8(%rax)
    6fc8:	0f 8f d8 fd ff ff    	jg     6da6 <verify+0x56>
    6fce:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6fd3:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6fd8:	48 81 44 24 10 c8 00 00 00 	addq   $0xc8,0x10(%rsp)
    6fe1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6fe6:	41 39 c7             	cmp    %eax,%r15d
    6fe9:	0f 84 86 00 00 00    	je     7075 <verify+0x325>
    6fef:	41 89 c4             	mov    %eax,%r12d
    6ff2:	e9 8a fd ff ff       	jmp    6d81 <verify+0x31>
    6ff7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7000:	0f 85 ba fe ff ff    	jne    6ec0 <verify+0x170>
    7006:	e9 a8 fe ff ff       	jmp    6eb3 <verify+0x163>
    700b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    7010:	49 39 c1             	cmp    %rax,%r9
    7013:	7e 09                	jle    701e <verify+0x2ce>
    7015:	4c 39 df             	cmp    %r11,%rdi
    7018:	0f 8c 0a ff ff ff    	jl     6f28 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    701e:	4c 39 df             	cmp    %r11,%rdi
    7021:	0f 8f 99 fe ff ff    	jg     6ec0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7027:	49 39 c1             	cmp    %rax,%r9
    702a:	0f 8d f8 fe ff ff    	jge    6f28 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7030:	48 39 f1             	cmp    %rsi,%rcx
    7033:	0f 85 87 fe ff ff    	jne    6ec0 <verify+0x170>
    7039:	4c 39 c2             	cmp    %r8,%rdx
    703c:	0f 85 7e fe ff ff    	jne    6ec0 <verify+0x170>
    7042:	4c 39 df             	cmp    %r11,%rdi
    7045:	0f 84 dd fe ff ff    	je     6f28 <verify+0x1d8>
    704b:	e9 70 fe ff ff       	jmp    6ec0 <verify+0x170>
    7050:	4c 39 c2             	cmp    %r8,%rdx
    7053:	0f 8c 5a fe ff ff    	jl     6eb3 <verify+0x163>
    7059:	4c 39 df             	cmp    %r11,%rdi
    705c:	7e c9                	jle    7027 <verify+0x2d7>
    705e:	4c 39 c2             	cmp    %r8,%rdx
    7061:	0f 85 59 fe ff ff    	jne    6ec0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7067:	49 39 c1             	cmp    %rax,%r9
    706a:	0f 8f 50 fe ff ff    	jg     6ec0 <verify+0x170>
    7070:	e9 b3 fe ff ff       	jmp    6f28 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    7075:	48 81 44 24 18 c8 00 00 00 	addq   $0xc8,0x18(%rsp)
    707e:	41 8d 46 01          	lea    0x1(%r14),%eax
    7082:	45 39 e6             	cmp    %r12d,%r14d
    7085:	74 08                	je     708f <verify+0x33f>
    7087:	41 89 c6             	mov    %eax,%r14d
    708a:	e9 ea fc ff ff       	jmp    6d79 <verify+0x29>
}
    708f:	48 83 c4 58          	add    $0x58,%rsp
    7093:	31 c0                	xor    %eax,%eax
    7095:	5b                   	pop    %rbx
    7096:	5d                   	pop    %rbp
    7097:	41 5c                	pop    %r12
    7099:	41 5d                	pop    %r13
    709b:	41 5e                	pop    %r14
    709d:	41 5f                	pop    %r15
    709f:	c3                   	ret
    70a0:	31 c0                	xor    %eax,%eax
    70a2:	c3                   	ret

Disassembly of section .fini:

00000000000070a4 <_fini>:
    70a4:	f3 0f 1e fa          	endbr64
    70a8:	48 83 ec 08          	sub    $0x8,%rsp
    70ac:	48 83 c4 08          	add    $0x8,%rsp
    70b0:	c3                   	ret
