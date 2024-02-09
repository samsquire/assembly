
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
    25b6:	48 8d 3d 69 5c 00 00 	lea    0x5c69(%rip),%rdi        # 8226 <_IO_stdin_used+0x226>
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
    25f6:	48 8d 3d f9 5b 00 00 	lea    0x5bf9(%rip),%rdi        # 81f6 <_IO_stdin_used+0x1f6>
    25fd:	e8 9e ff ff ff       	call   25a0 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    2602:	48 8d 3d 71 5b 00 00 	lea    0x5b71(%rip),%rdi        # 817a <_IO_stdin_used+0x17a>
    2609:	e8 92 ff ff ff       	call   25a0 <fatal_error>
    fatal_error("listen()");
    260e:	48 8d 3d 85 5b 00 00 	lea    0x5b85(%rip),%rdi        # 819a <_IO_stdin_used+0x19a>
    2615:	e8 86 ff ff ff       	call   25a0 <fatal_error>
    261a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2622:	0f 0b                	ud2
    2624:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    262c:	0f 0b                	ud2
      fatal_error("socket()");
    262e:	48 8d 3d 3c 5b 00 00 	lea    0x5b3c(%rip),%rdi        # 8171 <_IO_stdin_used+0x171>
    2635:	e8 66 ff ff ff       	call   25a0 <fatal_error>
      fatal_error("bind()");
    263a:	48 8d 3d 52 5b 00 00 	lea    0x5b52(%rip),%rdi        # 8193 <_IO_stdin_used+0x193>
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
    2656:	48 8d 3d fb 5f 00 00 	lea    0x5ffb(%rip),%rdi        # 8658 <_IO_stdin_used+0x658>
    265d:	41 56                	push   %r14
    265f:	41 55                	push   %r13
    2661:	41 54                	push   %r12
    2663:	55                   	push   %rbp
    2664:	53                   	push   %rbx
    2665:	48 81 ec e8 00 00 00 	sub    $0xe8,%rsp
    266c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2675:	48 89 84 24 d8 00 00 00 	mov    %rax,0xd8(%rsp)
    267d:	48 8d 05 9c 1c 00 00 	lea    0x1c9c(%rip),%rax        # 4320 <barriered_reset>
    2684:	66 48 0f 6e f0       	movq   %rax,%xmm6
    2689:	0f 16 35 d0 85 00 00 	movhps 0x85d0(%rip),%xmm6        # ac60 <__do_global_dtors_aux_fini_array_entry+0x8>
    2690:	0f 29 b4 24 a0 00 00 00 	movaps %xmm6,0xa0(%rsp)
    2698:	e8 83 fc ff ff       	call   2320 <puts@plt>
    269d:	bf 0a 00 00 00       	mov    $0xa,%edi
    26a2:	e8 59 fc ff ff       	call   2300 <putchar@plt>
    26a7:	ba 01 00 00 00       	mov    $0x1,%edx
    26ac:	48 8d 35 cf 5b 00 00 	lea    0x5bcf(%rip),%rsi        # 8282 <_IO_stdin_used+0x282>
    26b3:	31 c0                	xor    %eax,%eax
    26b5:	bf 01 00 00 00       	mov    $0x1,%edi
    26ba:	e8 e1 fd ff ff       	call   24a0 <__printf_chk@plt>
    26bf:	ba 06 00 00 00       	mov    $0x6,%edx
    26c4:	48 8d 35 c7 5b 00 00 	lea    0x5bc7(%rip),%rsi        # 8292 <_IO_stdin_used+0x292>
    26cb:	31 c0                	xor    %eax,%eax
    26cd:	bf 01 00 00 00       	mov    $0x1,%edi
    26d2:	e8 c9 fd ff ff       	call   24a0 <__printf_chk@plt>
    26d7:	ba 03 00 00 00       	mov    $0x3,%edx
    26dc:	48 8d 35 c4 5b 00 00 	lea    0x5bc4(%rip),%rsi        # 82a7 <_IO_stdin_used+0x2a7>
    26e3:	31 c0                	xor    %eax,%eax
    26e5:	bf 01 00 00 00       	mov    $0x1,%edi
    26ea:	e8 b1 fd ff ff       	call   24a0 <__printf_chk@plt>
    26ef:	ba 02 00 00 00       	mov    $0x2,%edx
    26f4:	48 8d 35 bc 5b 00 00 	lea    0x5bbc(%rip),%rsi        # 82b7 <_IO_stdin_used+0x2b7>
    26fb:	31 c0                	xor    %eax,%eax
    26fd:	bf 01 00 00 00       	mov    $0x1,%edi
    2702:	e8 99 fd ff ff       	call   24a0 <__printf_chk@plt>
    2707:	48 8d 3d bf 5b 00 00 	lea    0x5bbf(%rip),%rdi        # 82cd <_IO_stdin_used+0x2cd>
    270e:	e8 0d fc ff ff       	call   2320 <puts@plt>
    2713:	ba 02 00 00 00       	mov    $0x2,%edx
    2718:	48 8d 35 ca 5b 00 00 	lea    0x5bca(%rip),%rsi        # 82e9 <_IO_stdin_used+0x2e9>
    271f:	31 c0                	xor    %eax,%eax
    2721:	bf 01 00 00 00       	mov    $0x1,%edi
    2726:	e8 75 fd ff ff       	call   24a0 <__printf_chk@plt>
    272b:	ba 0a 00 00 00       	mov    $0xa,%edx
    2730:	48 8d 35 cc 5b 00 00 	lea    0x5bcc(%rip),%rsi        # 8303 <_IO_stdin_used+0x303>
    2737:	31 c0                	xor    %eax,%eax
    2739:	bf 01 00 00 00       	mov    $0x1,%edi
    273e:	e8 5d fd ff ff       	call   24a0 <__printf_chk@plt>
    2743:	ba 01 00 00 00       	mov    $0x1,%edx
    2748:	48 8d 35 c8 5b 00 00 	lea    0x5bc8(%rip),%rsi        # 8317 <_IO_stdin_used+0x317>
    274f:	31 c0                	xor    %eax,%eax
    2751:	bf 01 00 00 00       	mov    $0x1,%edi
    2756:	e8 45 fd ff ff       	call   24a0 <__printf_chk@plt>
    275b:	ba 01 00 00 00       	mov    $0x1,%edx
    2760:	48 8d 35 c1 5b 00 00 	lea    0x5bc1(%rip),%rsi        # 8328 <_IO_stdin_used+0x328>
    2767:	31 c0                	xor    %eax,%eax
    2769:	bf 01 00 00 00       	mov    $0x1,%edi
    276e:	e8 2d fd ff ff       	call   24a0 <__printf_chk@plt>
    2773:	ba 02 00 00 00       	mov    $0x2,%edx
    2778:	48 8d 35 c1 5b 00 00 	lea    0x5bc1(%rip),%rsi        # 8340 <_IO_stdin_used+0x340>
    277f:	31 c0                	xor    %eax,%eax
    2781:	bf 01 00 00 00       	mov    $0x1,%edi
    2786:	e8 15 fd ff ff       	call   24a0 <__printf_chk@plt>
    278b:	ba 01 00 00 00       	mov    $0x1,%edx
    2790:	48 8d 35 29 5f 00 00 	lea    0x5f29(%rip),%rsi        # 86c0 <_IO_stdin_used+0x6c0>
    2797:	31 c0                	xor    %eax,%eax
    2799:	bf 01 00 00 00       	mov    $0x1,%edi
    279e:	e8 fd fc ff ff       	call   24a0 <__printf_chk@plt>
    27a3:	ba 01 00 00 00       	mov    $0x1,%edx
    27a8:	48 8d 35 41 5f 00 00 	lea    0x5f41(%rip),%rsi        # 86f0 <_IO_stdin_used+0x6f0>
    27af:	31 c0                	xor    %eax,%eax
    27b1:	bf 01 00 00 00       	mov    $0x1,%edi
    27b6:	e8 e5 fc ff ff       	call   24a0 <__printf_chk@plt>
    27bb:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    27c0:	48 8d 35 95 5b 00 00 	lea    0x5b95(%rip),%rsi        # 835c <_IO_stdin_used+0x35c>
    27c7:	31 c0                	xor    %eax,%eax
    27c9:	bf 01 00 00 00       	mov    $0x1,%edi
    27ce:	e8 cd fc ff ff       	call   24a0 <__printf_chk@plt>
    27d3:	ba 05 00 00 00       	mov    $0x5,%edx
    27d8:	48 8d 35 97 5b 00 00 	lea    0x5b97(%rip),%rsi        # 8376 <_IO_stdin_used+0x376>
    27df:	31 c0                	xor    %eax,%eax
    27e1:	bf 01 00 00 00       	mov    $0x1,%edi
    27e6:	e8 b5 fc ff ff       	call   24a0 <__printf_chk@plt>
    27eb:	48 8d 3d 03 59 00 00 	lea    0x5903(%rip),%rdi        # 80f5 <_IO_stdin_used+0xf5>
    27f2:	e8 29 fb ff ff       	call   2320 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    27f7:	be 18 00 00 00       	mov    $0x18,%esi
    27fc:	bf 03 00 00 00       	mov    $0x3,%edi
    2801:	e8 ea fb ff ff       	call   23f0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2806:	be c8 00 00 00       	mov    $0xc8,%esi
    280b:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2810:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2818:	e8 d3 fb ff ff       	call   23f0 <calloc@plt>
    281d:	ba 06 00 00 00       	mov    $0x6,%edx
    2822:	bf 01 00 00 00       	mov    $0x1,%edi
    2827:	48 8d 35 5c 5b 00 00 	lea    0x5b5c(%rip),%rsi        # 838a <_IO_stdin_used+0x38a>
    282e:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2833:	31 c0                	xor    %eax,%eax
    2835:	e8 66 fc ff ff       	call   24a0 <__printf_chk@plt>
    283a:	ba 0c 00 00 00       	mov    $0xc,%edx
    283f:	48 8d 35 5a 5b 00 00 	lea    0x5b5a(%rip),%rsi        # 83a0 <_IO_stdin_used+0x3a0>
    2846:	31 c0                	xor    %eax,%eax
    2848:	bf 01 00 00 00       	mov    $0x1,%edi
    284d:	e8 4e fc ff ff       	call   24a0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2852:	be 10 00 00 00       	mov    $0x10,%esi
    2857:	bf 0c 00 00 00       	mov    $0xc,%edi
    285c:	e8 8f fb ff ff       	call   23f0 <calloc@plt>
    2861:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
    2869:	49 89 c7             	mov    %rax,%r15
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    286c:	48 8d 98 c0 00 00 00 	lea    0xc0(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2873:	49 89 c6             	mov    %rax,%r14
    buffers[x].count = buffer_size;
    2876:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    287d:	be 00 01 00 00       	mov    $0x100,%esi
    2882:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2887:	49 83 c6 10          	add    $0x10,%r14
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    288b:	e8 60 fb ff ff       	call   23f0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2890:	be 20 00 00 00       	mov    $0x20,%esi
    2895:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    289a:	49 89 46 f8          	mov    %rax,-0x8(%r14)
    289e:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
    28a1:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    28ab:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    28b5:	e8 36 fb ff ff       	call   23f0 <calloc@plt>
    28ba:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    28c1:	4c 39 f3             	cmp    %r14,%rbx
    28c4:	75 b0                	jne    2876 <main+0x226>
    28c6:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
    28ce:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
  int dataid = 0;
    28d3:	45 31 ed             	xor    %r13d,%r13d
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
    28d6:	c7 44 24 70 00 00 00 00 	movl   $0x0,0x70(%rsp)
  int curcpu = 0;
    28de:	c7 44 24 74 00 00 00 00 	movl   $0x0,0x74(%rsp)
  int swapcount = 0;
  for (int k = 0 ; k < group_count ; k++) {
    28e6:	45 31 e4             	xor    %r12d,%r12d
    28e9:	48 89 b4 24 b0 00 00 00 	mov    %rsi,0xb0(%rsp)
    28f1:	48 89 dd             	mov    %rbx,%rbp
    28f4:	48 89 9c 24 80 00 00 00 	mov    %rbx,0x80(%rsp)
    28fc:	4c 89 fb             	mov    %r15,%rbx
    28ff:	45 89 ef             	mov    %r13d,%r15d
    for (int d = 0 ; d < threads_per_group ; d++) {
    2902:	48 63 44 24 70       	movslq 0x70(%rsp),%rax
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2907:	49 89 e9             	mov    %rbp,%r9
    290a:	45 89 e6             	mov    %r12d,%r14d
    290d:	48 89 ac 24 c0 00 00 00 	mov    %rbp,0xc0(%rsp)
    2915:	48 89 b4 24 b8 00 00 00 	mov    %rsi,0xb8(%rsp)
    291d:	48 c1 e0 04          	shl    $0x4,%rax
    2921:	48 89 9c 24 c8 00 00 00 	mov    %rbx,0xc8(%rsp)
    2929:	48 01 d8             	add    %rbx,%rax
    292c:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2931:	43 8d 04 24          	lea    (%r12,%r12,1),%eax
    2935:	8d 78 01             	lea    0x1(%rax),%edi
    2938:	83 c0 03             	add    $0x3,%eax
    293b:	89 7c 24 20          	mov    %edi,0x20(%rsp)
    293f:	89 84 24 8c 00 00 00 	mov    %eax,0x8c(%rsp)
    2946:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    294b:	44 89 f2             	mov    %r14d,%edx
    294e:	bf 01 00 00 00       	mov    $0x1,%edi
    2953:	31 c0                	xor    %eax,%eax
    2955:	48 8d 35 bc 5d 00 00 	lea    0x5dbc(%rip),%rsi        # 8718 <_IO_stdin_used+0x718>
    295c:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      int x = (k * threads_per_group) + d;
    2961:	45 8d 44 24 ff       	lea    -0x1(%r12),%r8d
    2966:	44 89 c1             	mov    %r8d,%ecx
    2969:	44 89 44 24 18       	mov    %r8d,0x18(%rsp)
    296e:	45 89 c5             	mov    %r8d,%r13d
    2971:	e8 2a fb ff ff       	call   24a0 <__printf_chk@plt>
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2976:	be 08 00 00 00       	mov    $0x8,%esi
    297b:	bf 02 00 00 00       	mov    $0x2,%edi
    2980:	e8 6b fa ff ff       	call   23f0 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2985:	be 80 00 00 00       	mov    $0x80,%esi
    298a:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    298f:	48 89 c3             	mov    %rax,%rbx
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2992:	e8 59 fa ff ff       	call   23f0 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2997:	45 89 e8             	mov    %r13d,%r8d
    299a:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    299f:	41 83 e0 01          	and    $0x1,%r8d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    29a3:	48 89 c5             	mov    %rax,%rbp
      if (x % 2 == 1) {
    29a6:	44 89 44 24 50       	mov    %r8d,0x50(%rsp)
    29ab:	0f 84 81 10 00 00    	je     3a32 <main+0x13e2>
        other = abs(x - 1) % total_threads;
    29b1:	41 8d 44 24 fe       	lea    -0x2(%r12),%eax
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    29b6:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
        my_thread_data[1] = &thread_data[x]; 
    29bb:	4c 89 ca             	mov    %r9,%rdx
        other = abs(x - 1) % total_threads;
    29be:	49 89 c5             	mov    %rax,%r13
        my_thread_data[0] = &thread_data[other]; 
    29c1:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    29c5:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    29c9:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    29cd:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    29d1:	48 89 7c 24 40       	mov    %rdi,0x40(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    29d6:	48 8b bc 24 b8 00 00 00 	mov    0xb8(%rsp),%rdi
    29de:	48 89 03             	mov    %rax,(%rbx)
    29e1:	44 89 e9             	mov    %r13d,%ecx
    29e4:	48 8d 35 5d 5d 00 00 	lea    0x5d5d(%rip),%rsi        # 8748 <_IO_stdin_used+0x748>
        thread_data[x].thread_index = 1;
    29eb:	45 89 41 04          	mov    %r8d,0x4(%r9)
    29ef:	31 c0                	xor    %eax,%eax
        thread_data[x].protected_state = &protected_state[k];
    29f1:	49 89 79 48          	mov    %rdi,0x48(%r9)
    29f5:	bf 01 00 00 00       	mov    $0x1,%edi
    29fa:	48 89 53 08          	mov    %rdx,0x8(%rbx)
    29fe:	8b 54 24 18          	mov    0x18(%rsp),%edx
    2a02:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2a07:	e8 94 fa ff ff       	call   24a0 <__printf_chk@plt>
      thread_data[x].other = other;
    2a0c:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2a11:	8b 4c 24 74          	mov    0x74(%rsp),%ecx
    2a15:	31 c0                	xor    %eax,%eax
    2a17:	48 8d 35 5a 5d 00 00 	lea    0x5d5a(%rip),%rsi        # 8778 <_IO_stdin_used+0x778>
    2a1e:	bf 01 00 00 00       	mov    $0x1,%edi
    2a23:	45 89 a9 b8 00 00 00 	mov    %r13d,0xb8(%r9)
    2a2a:	44 8b 6c 24 18       	mov    0x18(%rsp),%r13d
    2a2f:	44 89 ea             	mov    %r13d,%edx
    2a32:	e8 69 fa ff ff       	call   24a0 <__printf_chk@plt>
        if (x < thread_count) {
    2a37:	41 83 fd 01          	cmp    $0x1,%r13d
    2a3b:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2a40:	0f 87 15 10 00 00    	ja     3a5b <main+0x140b>
          CPU_SET(curcpu, sendercpu);
    2a46:	48 63 44 24 74       	movslq 0x74(%rsp),%rax
    2a4b:	48 89 c7             	mov    %rax,%rdi
    2a4e:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2a54:	77 13                	ja     2a69 <main+0x419>
    2a56:	48 c1 e8 06          	shr    $0x6,%rax
    2a5a:	ba 01 00 00 00       	mov    $0x1,%edx
    2a5f:	89 f9                	mov    %edi,%ecx
    2a61:	48 d3 e2             	shl    %cl,%rdx
    2a64:	48 09 54 c5 00       	or     %rdx,0x0(%rbp,%rax,8)
          curcpu += 2;
    2a69:	83 44 24 74 02       	addl   $0x2,0x74(%rsp)
      thread_data[x].real_thread_index = x;
    2a6e:	8b 44 24 18          	mov    0x18(%rsp),%eax
      thread_data[x].cpu_set = sendercpu;
    2a72:	49 89 a9 b0 00 00 00 	mov    %rbp,0xb0(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a79:	31 ed                	xor    %ebp,%ebp
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a7b:	be 10 00 00 00       	mov    $0x10,%esi
      thread_data[x].kind = KERNEL_THREAD;
    2a80:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a87:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].real_thread_index = x;
    2a8c:	41 89 41 08          	mov    %eax,0x8(%r9)
      thread_data[x].all_threads = thread_data;
    2a90:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    2a95:	49 89 59 18          	mov    %rbx,0x18(%r9)
      thread_data[x].all_threads = thread_data;
    2a99:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2a9d:	48 8b 05 fc 61 00 00 	mov    0x61fc(%rip),%rax        # 8ca0 <_IO_stdin_used+0xca0>
      thread_data[x].task_count = total_barrier_count;
    2aa4:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].group_count = group_count;
    2aac:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
      thread_data[x].thread_count = 2;
    2ab3:	48 8b 05 ee 61 00 00 	mov    0x61ee(%rip),%rax        # 8ca8 <_IO_stdin_used+0xca8>
      thread_data[x].task_count = total_barrier_count;
    2aba:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].thread_count = 2;
    2abf:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2ac3:	e8 28 f9 ff ff       	call   23f0 <calloc@plt>
    2ac8:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2acd:	be 10 00 00 00       	mov    $0x10,%esi
    2ad2:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2ad7:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2adb:	e8 10 f9 ff ff       	call   23f0 <calloc@plt>
    2ae0:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2ae5:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2aea:	66 0f 6f 3d 7e 61 00 00 	movdqa 0x617e(%rip),%xmm7        # 8c70 <_IO_stdin_used+0xc70>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2af2:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2af7:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2afb:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2b03:	e8 e8 f8 ff ff       	call   23f0 <calloc@plt>
    2b08:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2b0d:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2b12:	66 0f 6f 35 56 61 00 00 	movdqa 0x6156(%rip),%xmm6        # 8c70 <_IO_stdin_used+0xc70>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2b1a:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2b1f:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2b26:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2b2e:	e8 bd f8 ff ff       	call   23f0 <calloc@plt>
        thread_data[x].tasks = barriers;
    2b33:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2b38:	4c 89 e7             	mov    %r12,%rdi
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2b3b:	49 89 c5             	mov    %rax,%r13
        thread_data[x].tasks = barriers;
    2b3e:	49 89 41 38          	mov    %rax,0x38(%r9)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2b42:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
            data[0].messages_count = 0;
    2b47:	4c 89 e9             	mov    %r13,%rcx
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2b4a:	48 0f af f8          	imul   %rax,%rdi
            data[0].messages_count = 0;
    2b4e:	4c 89 4c 24 48       	mov    %r9,0x48(%rsp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2b53:	48 c1 ef 22          	shr    $0x22,%rdi
    2b57:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2b5a:	8b 7c 24 20          	mov    0x20(%rsp),%edi
    2b5e:	01 c0                	add    %eax,%eax
    2b60:	29 c7                	sub    %eax,%edi
            data[0].messages_count = 0;
    2b62:	89 bc 24 88 00 00 00 	mov    %edi,0x88(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2b69:	48 63 c5             	movslq %ebp,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2b6c:	be 38 00 00 00       	mov    $0x38,%esi
    2b71:	bf 06 00 00 00       	mov    $0x6,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2b76:	45 31 ed             	xor    %r13d,%r13d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2b79:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2b7e:	48 c1 e0 09          	shl    $0x9,%rax
    2b82:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    2b86:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2b8b:	48 8d 05 4e 17 00 00 	lea    0x174e(%rip),%rax        # 42e0 <do_protected_write>
    2b92:	49 89 84 24 20 01 00 00 	mov    %rax,0x120(%r12)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2b9a:	e8 51 f8 ff ff       	call   23f0 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2b9f:	49 89 84 24 70 01 00 00 	mov    %rax,0x170(%r12)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2ba7:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2baa:	8b 44 24 50          	mov    0x50(%rsp),%eax
    2bae:	85 c0                	test   %eax,%eax
    2bb0:	0f 84 31 06 00 00    	je     31e7 <main+0xb97>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2bb6:	8b 44 24 20          	mov    0x20(%rsp),%eax
    2bba:	48 89 4c 24 78       	mov    %rcx,0x78(%rsp)
    2bbf:	49 89 cc             	mov    %rcx,%r12
    2bc2:	83 e8 02             	sub    $0x2,%eax
    2bc5:	89 44 24 68          	mov    %eax,0x68(%rsp)
    2bc9:	eb 17                	jmp    2be2 <main+0x592>
    2bcb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2bd0:	41 83 c5 01          	add    $0x1,%r13d
    2bd4:	49 83 c4 38          	add    $0x38,%r12
    2bd8:	41 83 fd 06          	cmp    $0x6,%r13d
    2bdc:	0f 84 4a 01 00 00    	je     2d2c <main+0x6dc>
            int group_of = b / threads_per_group;
    2be2:	44 89 eb             	mov    %r13d,%ebx
    2be5:	31 c0                	xor    %eax,%eax
    2be7:	44 89 ea             	mov    %r13d,%edx
    2bea:	bf 01 00 00 00       	mov    $0x1,%edi
    2bef:	d1 fb                	sar    %ebx
    2bf1:	48 8d 35 c2 57 00 00 	lea    0x57c2(%rip),%rsi        # 83ba <_IO_stdin_used+0x3ba>
    2bf8:	89 d9                	mov    %ebx,%ecx
    2bfa:	e8 a1 f8 ff ff       	call   24a0 <__printf_chk@plt>
            if (k == group_of) {
    2bff:	41 39 de             	cmp    %ebx,%r14d
    2c02:	75 cc                	jne    2bd0 <main+0x580>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2c04:	be 08 00 00 00       	mov    $0x8,%esi
    2c09:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c0e:	49 83 c4 38          	add    $0x38,%r12
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2c12:	e8 d9 f7 ff ff       	call   23f0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2c17:	be 08 00 00 00       	mov    $0x8,%esi
    2c1c:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2c21:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2c26:	e8 c5 f7 ff ff       	call   23f0 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2c2b:	be 80 03 00 00       	mov    $0x380,%esi
    2c30:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2c35:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2c3a:	e8 b1 f7 ff ff       	call   23f0 <calloc@plt>
              data[0].a = x;
    2c3f:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    2c43:	44 89 ea             	mov    %r13d,%edx
              mailboxes[b].pending = NULL;
    2c46:	49 c7 44 24 d8 00 00 00 00 	movq   $0x0,-0x28(%r12)
              struct Data *data = calloc(3, sizeof(struct Data));
    2c4f:	49 89 c1             	mov    %rax,%r9
              data[0].c = b;
    2c52:	44 89 a8 24 03 00 00 	mov    %r13d,0x324(%rax)
    2c59:	48 8d 35 38 5b 00 00 	lea    0x5b38(%rip),%rsi        # 8798 <_IO_stdin_used+0x798>
              data[0].a = x;
    2c60:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].kind = MAILBOX_LOWER;
    2c66:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].b = y;
    2c70:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].id = dataid++;
    2c76:	41 8d 47 01          	lea    0x1(%r15),%eax
              data[1].id = dataid++;
    2c7a:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    2c81:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    2c88:	49 89 44 24 d0       	mov    %rax,-0x30(%r12)
    2c8d:	8b 44 24 68          	mov    0x68(%rsp),%eax
              data[0].id = dataid++;
    2c91:	45 89 b9 28 03 00 00 	mov    %r15d,0x328(%r9)
              data[1].id = dataid++;
    2c98:	41 83 c7 02          	add    $0x2,%r15d
              data[1].a = x;
    2c9c:	41 89 b9 9c 06 00 00 	mov    %edi,0x69c(%r9)
    2ca3:	89 c1                	mov    %eax,%ecx
    2ca5:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].c = b;
    2caa:	45 89 a9 a4 06 00 00 	mov    %r13d,0x6a4(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2cb1:	41 83 c5 01          	add    $0x1,%r13d
              mailboxes[b].lower = &data[0];
    2cb5:	4d 89 4c 24 c8       	mov    %r9,-0x38(%r12)
    2cba:	41 89 44 24 fc       	mov    %eax,-0x4(%r12)
    2cbf:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    2cc1:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].b = y;
    2ccc:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[0].finished_reading = 1;
    2cd3:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2cde:	41 c7 44 24 f8 01 00 00 00 	movl   $0x1,-0x8(%r12)
              data[0].finished_reading = 1;
    2ce7:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2cec:	e8 af f7 ff ff       	call   24a0 <__printf_chk@plt>
              data[0].messages = messages;
    2cf1:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2cf6:	4c 8b 5c 24 58       	mov    0x58(%rsp),%r11
              data[0].messages_count = 0;
    2cfb:	66 0f 6f 35 7d 5f 00 00 	movdqa 0x5f7d(%rip),%xmm6        # 8c80 <_IO_stdin_used+0xc80>
              data[1].messages = messages2;
    2d03:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
              data[0].messages = messages;
    2d08:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2d0b:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    2d12:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    2d1a:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d22:	41 83 fd 06          	cmp    $0x6,%r13d
    2d26:	0f 85 b6 fe ff ff    	jne    2be2 <main+0x592>
    2d2c:	48 8b 4c 24 78       	mov    0x78(%rsp),%rcx
    2d31:	44 89 74 24 08       	mov    %r14d,0x8(%rsp)
    2d36:	31 db                	xor    %ebx,%ebx
    2d38:	49 89 cc             	mov    %rcx,%r12
    2d3b:	41 89 ee             	mov    %ebp,%r14d
    2d3e:	66 90                	xchg   %ax,%ax
            int group_of = b / threads_per_group;
    2d40:	89 d8                	mov    %ebx,%eax
    2d42:	d1 f8                	sar    %eax
            if (k == group_of) {
    2d44:	39 44 24 08          	cmp    %eax,0x8(%rsp)
    2d48:	0f 84 4d 01 00 00    	je     2e9b <main+0x84b>
    2d4e:	89 da                	mov    %ebx,%edx
    2d50:	48 8d 35 73 56 00 00 	lea    0x5673(%rip),%rsi        # 83ca <_IO_stdin_used+0x3ca>
    2d57:	bf 01 00 00 00       	mov    $0x1,%edi
    2d5c:	31 c0                	xor    %eax,%eax
    2d5e:	e8 3d f7 ff ff       	call   24a0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d63:	be 08 00 00 00       	mov    $0x8,%esi
    2d68:	bf 01 00 00 00       	mov    $0x1,%edi
    2d6d:	e8 7e f6 ff ff       	call   23f0 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d72:	be 08 00 00 00       	mov    $0x8,%esi
    2d77:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d7c:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d81:	e8 6a f6 ff ff       	call   23f0 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    2d86:	be 80 03 00 00       	mov    $0x380,%esi
    2d8b:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d90:	48 89 c5             	mov    %rax,%rbp
            struct Data *data = calloc(3, sizeof(struct Data));
    2d93:	e8 58 f6 ff ff       	call   23f0 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    2d98:	be 80 03 00 00       	mov    $0x380,%esi
    2d9d:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    2da2:	49 89 c5             	mov    %rax,%r13
            struct Data **stack = calloc(3, sizeof(struct Data));
    2da5:	e8 46 f6 ff ff       	call   23f0 <calloc@plt>
            data[0].id = dataid++;
    2daa:	41 8d 77 01          	lea    0x1(%r15),%esi
            data[0].a = x;
    2dae:	8b 7c 24 18          	mov    0x18(%rsp),%edi
            data[0].messages = messages;
    2db2:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
            data[1].id = dataid++;
    2db7:	41 89 b5 a8 06 00 00 	mov    %esi,0x6a8(%r13)
            mailboxes[b].higher = &data[1];
    2dbe:	49 8d b5 80 03 00 00 	lea    0x380(%r13),%rsi
            data[0].messages_count = 0;
    2dc5:	66 0f 6f 35 b3 5e 00 00 	movdqa 0x5eb3(%rip),%xmm6        # 8c80 <_IO_stdin_used+0xc80>
            data[0].kind = MAILBOX_LOWER;
    2dcd:	41 c7 85 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r13)
            data[0].a = x;
    2dd8:	41 89 bd 1c 03 00 00 	mov    %edi,0x31c(%r13)
            data[0].b = y;
    2ddf:	45 89 b5 20 03 00 00 	mov    %r14d,0x320(%r13)
            data[0].c = b;
    2de6:	41 89 9d 24 03 00 00 	mov    %ebx,0x324(%r13)
            data[1].kind = MAILBOX_HIGHER;
    2ded:	41 c7 85 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r13)
            data[1].a = x;
    2df8:	41 89 bd 9c 06 00 00 	mov    %edi,0x69c(%r13)
            data[1].b = y;
    2dff:	45 89 b5 a0 06 00 00 	mov    %r14d,0x6a0(%r13)
            data[1].c = b;
    2e06:	41 89 9d a4 06 00 00 	mov    %ebx,0x6a4(%r13)
            mailboxes[b].lower = &data[0];
    2e0d:	4d 89 2c 24          	mov    %r13,(%r12)
            mailboxes[b].my_lower = &data[0];
    2e11:	4d 89 6c 24 20       	mov    %r13,0x20(%r12)
            mailboxes[b].higher = &data[1];
    2e16:	49 89 74 24 08       	mov    %rsi,0x8(%r12)
            mailboxes[b].pending = NULL;
    2e1b:	49 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%r12)
            data[0].finished_reading = 1;
    2e24:	41 c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r13)
            mailboxes[b].my_higher = &data[1];
    2e2f:	49 89 74 24 28       	mov    %rsi,0x28(%r12)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2e34:	41 c7 44 24 30 02 00 00 00 	movl   $0x2,0x30(%r12)
            stack[0] = mailboxes[b].lower;
    2e3d:	4c 89 28             	mov    %r13,(%rax)
            stack[1] = mailboxes[b].higher;
    2e40:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    2e44:	49 89 44 24 18       	mov    %rax,0x18(%r12)
            data[0].available_sending = 0;
    2e49:	41 c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r13)
            data[0].available_receiving = 0;
    2e54:	41 c7 85 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r13)
            data[0].messages = messages;
    2e5f:	49 89 55 00          	mov    %rdx,0x0(%r13)
            data[1].messages = messages2;
    2e63:	49 89 ad 80 03 00 00 	mov    %rbp,0x380(%r13)
            data[1].available_sending = 1;
    2e6a:	41 c7 85 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r13)
            data[1].available_receiving = 0;
    2e75:	41 c7 85 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r13)
            data[0].id = dataid++;
    2e80:	45 89 bd 28 03 00 00 	mov    %r15d,0x328(%r13)
            data[1].id = dataid++;
    2e87:	41 83 c7 02          	add    $0x2,%r15d
            data[0].messages_count = 0;
    2e8b:	41 0f 29 b5 80 00 00 00 	movaps %xmm6,0x80(%r13)
            data[1].messages_count = 0;
    2e93:	41 0f 29 b5 00 04 00 00 	movaps %xmm6,0x400(%r13)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e9b:	83 c3 01             	add    $0x1,%ebx
    2e9e:	49 83 c4 38          	add    $0x38,%r12
    2ea2:	83 fb 06             	cmp    $0x6,%ebx
    2ea5:	0f 85 95 fe ff ff    	jne    2d40 <main+0x6f0>
          char *message = malloc(sizeof(char) * 256);
    2eab:	be 01 00 00 00       	mov    $0x1,%esi
    2eb0:	bf 00 01 00 00       	mov    $0x100,%edi
    2eb5:	44 89 f5             	mov    %r14d,%ebp
    2eb8:	44 8b 74 24 08       	mov    0x8(%rsp),%r14d
    2ebd:	e8 2e f5 ff ff       	call   23f0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2ec2:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    2ec7:	49 89 c4             	mov    %rax,%r12
          struct Message *messaged = malloc(sizeof(struct Message));
    2eca:	e8 91 f5 ff ff       	call   2460 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2ecf:	48 83 ec 08          	sub    $0x8,%rsp
    2ed3:	4c 89 e7             	mov    %r12,%rdi
    2ed6:	41 89 e9             	mov    %ebp,%r9d
    2ed9:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2ede:	48 8d 0d db 58 00 00 	lea    0x58db(%rip),%rcx        # 87c0 <_IO_stdin_used+0x7c0>
    2ee5:	ba 00 01 00 00       	mov    $0x100,%edx
    2eea:	31 c0                	xor    %eax,%eax
    2eec:	41 56                	push   %r14
    2eee:	44 8b 44 24 28       	mov    0x28(%rsp),%r8d
    2ef3:	be 01 00 00 00       	mov    $0x1,%esi
    2ef8:	e8 83 f6 ff ff       	call   2580 <__sprintf_chk@plt>
          messaged->message = message;
    2efd:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
          messaged->thread_index = thread_data[x].real_thread_index;
    2f02:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2f07:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->task_index = y;
    2f0c:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
          thread_data[x].tasks[y].group = k;
    2f11:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2f16:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].group = k;
    2f1b:	48 8b 4b 38          	mov    0x38(%rbx),%rcx
          messaged->message = message;
    2f1f:	4d 89 22             	mov    %r12,(%r10)
          messaged->task_index = y;
    2f22:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2f26:	48 63 43 08          	movslq 0x8(%rbx),%rax
          thread_data[x].tasks[y].group = k;
    2f2a:	48 01 ca             	add    %rcx,%rdx
          messaged->group = k;
    2f2d:	45 89 72 18          	mov    %r14d,0x18(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2f31:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2f35:	8d 45 01             	lea    0x1(%rbp),%eax
    2f38:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].group = k;
    2f3b:	44 89 b2 94 01 00 00 	mov    %r14d,0x194(%rdx)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2f42:	c7 02 41 00 00 00    	movl   $0x41,(%rdx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2f48:	89 82 90 01 00 00    	mov    %eax,0x190(%rdx)
          thread_data[x].tasks[y].message = messaged;
    2f4e:	4c 89 92 88 01 00 00 	mov    %r10,0x188(%rdx)
          thread_data[x].tasks[y].sending = 1;
    2f55:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
          thread_data[x].tasks[y].snapshot_count = 99;
    2f5f:	48 c7 82 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rdx)
          thread_data[x].tasks[y].group = k;
    2f6a:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
          thread_data[x].tasks[y].snapshot_count = 99;
    2f6f:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2f74:	e8 77 f4 ff ff       	call   23f0 <calloc@plt>
    2f79:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    2f7e:	48 89 82 50 01 00 00 	mov    %rax,0x150(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2f85:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
          thread_data[x].tasks[y].current_snapshot = 0;
    2f8a:	48 c7 82 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2f95:	48 8b 00             	mov    (%rax),%rax
    2f98:	8b 70 04             	mov    0x4(%rax),%esi
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2f9b:	48 39 d8             	cmp    %rbx,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2f9e:	48 89 82 28 01 00 00 	mov    %rax,0x128(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2fa5:	89 b2 30 01 00 00    	mov    %esi,0x130(%rdx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2fab:	41 5b                	pop    %r11
    2fad:	41 5c                	pop    %r12
    2faf:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2fb4:	0f 85 1d 12 00 00    	jne    41d7 <main+0x1b87>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2fba:	66 0f 6f 05 ce 5c 00 00 	movdqa 0x5cce(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2fc2:	89 6a 04             	mov    %ebp,0x4(%rdx)
          thread_data[x].tasks[y].available = 1;
    2fc5:	4c 8b 25 e4 5c 00 00 	mov    0x5ce4(%rip),%r12        # 8cb0 <_IO_stdin_used+0xcb0>
          thread_data[x].tasks[y].arrived = 0;
    2fcc:	c7 82 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rdx)
          thread_data[x].tasks[y].worker_count = thread_count;
    2fd6:	c7 82 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rdx)
          thread_data[x].tasks[y].available = 1;
    2fe0:	4c 89 a2 44 01 00 00 	mov    %r12,0x144(%rdx)
          thread_data[x].tasks[y].thread_count = 2;
    2fe7:	0f 11 82 34 01 00 00 	movups %xmm0,0x134(%rdx)
          if (y == barrier_count - 1) {
    2fee:	83 fd 01             	cmp    $0x1,%ebp
    2ff1:	0f 84 7d 03 00 00    	je     3374 <main+0xd24>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2ff7:	85 ed                	test   %ebp,%ebp
    2ff9:	0f 84 5d 03 00 00    	je     335c <main+0xd0c>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    2fff:	4c 8b 4c 24 48       	mov    0x48(%rsp),%r9
    3004:	48 8d 05 05 36 00 00 	lea    0x3605(%rip),%rax        # 6610 <barriered_work>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    300b:	bf 01 00 00 00       	mov    $0x1,%edi
               thread_data[x].tasks[y].run = barriered_work; 
    3010:	49 89 cd             	mov    %rcx,%r13
    3013:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    301a:	be 08 00 00 00       	mov    $0x8,%esi
        thread_data[x].buffers_count = buffers_per_thread;
    301f:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    302a:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    302f:	e8 bc f3 ff ff       	call   23f0 <calloc@plt>
    3034:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3039:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    303e:	66 0f 6f bc 24 a0 00 00 00 	movdqa 0xa0(%rsp),%xmm7
    for (int d = 0 ; d < threads_per_group ; d++) {
    3047:	83 44 24 20 01       	addl   $0x1,0x20(%rsp)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    304c:	48 89 38             	mov    %rdi,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    304f:	48 83 c7 10          	add    $0x10,%rdi
    3053:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    305a:	49 89 41 88          	mov    %rax,-0x78(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    305e:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3063:	83 44 24 70 01       	addl   $0x1,0x70(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3068:	48 8b 00             	mov    (%rax),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    306b:	48 89 7c 24 60       	mov    %rdi,0x60(%rsp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    3070:	41 c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r13)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    307b:	49 89 85 28 05 00 00 	mov    %rax,0x528(%r13)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    3082:	41 c7 85 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r13)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    308d:	41 c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r13)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    3098:	41 8b 81 3c ff ff ff 	mov    -0xc4(%r9),%eax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    309f:	41 0f 11 bd 18 05 00 00 	movups %xmm7,0x518(%r13)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    30a7:	41 89 85 30 05 00 00 	mov    %eax,0x530(%r13)
    for (int d = 0 ; d < threads_per_group ; d++) {
    30ae:	8b 44 24 20          	mov    0x20(%rsp),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    30b2:	41 c7 85 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r13)
        thread_data[x].tasks[barrier_count].available = 1; 
    30bd:	4d 89 a5 44 05 00 00 	mov    %r12,0x544(%r13)
    for (int d = 0 ; d < threads_per_group ; d++) {
    30c4:	39 84 24 8c 00 00 00 	cmp    %eax,0x8c(%rsp)
    30cb:	0f 85 75 f8 ff ff    	jne    2946 <main+0x2f6>
    30d1:	48 8b ac 24 c0 00 00 00 	mov    0xc0(%rsp),%rbp
    30d9:	48 8b b4 24 b8 00 00 00 	mov    0xb8(%rsp),%rsi
    30e1:	45 89 f4             	mov    %r14d,%r12d
  for (int k = 0 ; k < group_count ; k++) {
    30e4:	41 83 c4 01          	add    $0x1,%r12d
    30e8:	48 8b 9c 24 c8 00 00 00 	mov    0xc8(%rsp),%rbx
    30f0:	48 83 c6 18          	add    $0x18,%rsi
    30f4:	48 81 c5 90 01 00 00 	add    $0x190,%rbp
    30fb:	41 83 fc 03          	cmp    $0x3,%r12d
    30ff:	0f 85 fd f7 ff ff    	jne    2902 <main+0x2b2>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3105:	be 08 00 00 00       	mov    $0x8,%esi
    310a:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    310f:	45 31 e4             	xor    %r12d,%r12d
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3112:	e8 d9 f2 ff ff       	call   23f0 <calloc@plt>
    3117:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    311c:	48 89 c5             	mov    %rax,%rbp
    311f:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3121:	49 89 d1             	mov    %rdx,%r9
    3124:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3126:	45 8b 51 40          	mov    0x40(%r9),%r10d
    312a:	45 85 d2             	test   %r10d,%r10d
    312d:	0f 8e 9b 00 00 00    	jle    31ce <main+0xb7e>
    3133:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3137:	4d 63 c2             	movslq %r10d,%r8
    313a:	49 63 cc             	movslq %r12d,%rcx
    313d:	49 c1 e0 09          	shl    $0x9,%r8
    3141:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    3146:	49 01 f8             	add    %rdi,%r8
    3149:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3150:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3157:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    315e:	48 83 c6 60          	add    $0x60,%rsi
    3162:	f3 0f 7e 61 38       	movq   0x38(%rcx),%xmm4
    3167:	f3 0f 7e 59 70       	movq   0x70(%rcx),%xmm3
    316c:	f3 0f 7e 91 a8 00 00 00 	movq   0xa8(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3174:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3178:	f3 0f 7e 89 e0 00 00 00 	movq   0xe0(%rcx),%xmm1
    3180:	0f 16 61 40          	movhps 0x40(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3184:	0f 16 59 78          	movhps 0x78(%rcx),%xmm3
    3188:	f3 0f 7e 81 18 01 00 00 	movq   0x118(%rcx),%xmm0
    3190:	0f 16 91 b0 00 00 00 	movhps 0xb0(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3197:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    319b:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    319f:	0f 16 89 e8 00 00 00 	movhps 0xe8(%rcx),%xmm1
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    31a6:	0f 16 81 20 01 00 00 	movhps 0x120(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    31ad:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    31b1:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    31b5:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    31b9:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    31bd:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    31c1:	49 39 f8             	cmp    %rdi,%r8
    31c4:	75 8a                	jne    3150 <main+0xb00>
    31c6:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    31ca:	45 8d 24 8c          	lea    (%r12,%rcx,4),%r12d
    for (int d = 0 ; d < threads_per_group ; d++) {
    31ce:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
    31d5:	85 db                	test   %ebx,%ebx
    31d7:	0f 85 a5 01 00 00    	jne    3382 <main+0xd32>
    31dd:	bb 01 00 00 00       	mov    $0x1,%ebx
    31e2:	e9 3f ff ff ff       	jmp    3126 <main+0xad6>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    31e7:	45 89 ec             	mov    %r13d,%r12d
    31ea:	48 89 4c 24 68       	mov    %rcx,0x68(%rsp)
    31ef:	49 89 cd             	mov    %rcx,%r13
    31f2:	eb 16                	jmp    320a <main+0xbba>
    31f4:	0f 1f 40 00          	nopl   0x0(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    31f8:	41 83 c4 01          	add    $0x1,%r12d
    31fc:	49 83 c5 38          	add    $0x38,%r13
    3200:	41 83 fc 06          	cmp    $0x6,%r12d
    3204:	0f 84 48 01 00 00    	je     3352 <main+0xd02>
            int group_of = b / threads_per_group;
    320a:	44 89 e3             	mov    %r12d,%ebx
    320d:	31 c0                	xor    %eax,%eax
    320f:	44 89 e2             	mov    %r12d,%edx
    3212:	bf 01 00 00 00       	mov    $0x1,%edi
    3217:	d1 fb                	sar    %ebx
    3219:	48 8d 35 9a 51 00 00 	lea    0x519a(%rip),%rsi        # 83ba <_IO_stdin_used+0x3ba>
    3220:	89 d9                	mov    %ebx,%ecx
    3222:	e8 79 f2 ff ff       	call   24a0 <__printf_chk@plt>
            if (k == group_of) {
    3227:	41 39 de             	cmp    %ebx,%r14d
    322a:	75 cc                	jne    31f8 <main+0xba8>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    322c:	be 08 00 00 00       	mov    $0x8,%esi
    3231:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3236:	49 83 c5 38          	add    $0x38,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    323a:	e8 b1 f1 ff ff       	call   23f0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    323f:	be 08 00 00 00       	mov    $0x8,%esi
    3244:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3249:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    324e:	e8 9d f1 ff ff       	call   23f0 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    3253:	be 80 03 00 00       	mov    $0x380,%esi
    3258:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    325d:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    3262:	e8 89 f1 ff ff       	call   23f0 <calloc@plt>
              data[0].a = x;
    3267:	8b 7c 24 18          	mov    0x18(%rsp),%edi
              mailboxes[b].pending = NULL;
    326b:	49 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%r13)
    3273:	44 89 e2             	mov    %r12d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
    3276:	49 89 c1             	mov    %rax,%r9
              data[0].c = b;
    3279:	44 89 a0 24 03 00 00 	mov    %r12d,0x324(%rax)
    3280:	48 8d 35 11 55 00 00 	lea    0x5511(%rip),%rsi        # 8798 <_IO_stdin_used+0x798>
              data[0].a = x;
    3287:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].kind = MAILBOX_LOWER;
    328d:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].b = y;
    3297:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].id = dataid++;
    329d:	41 8d 47 01          	lea    0x1(%r15),%eax
              data[1].id = dataid++;
    32a1:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    32a8:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    32af:	49 89 45 d0          	mov    %rax,-0x30(%r13)
    32b3:	8b 84 24 88 00 00 00 	mov    0x88(%rsp),%eax
              data[0].id = dataid++;
    32ba:	45 89 b9 28 03 00 00 	mov    %r15d,0x328(%r9)
              data[1].id = dataid++;
    32c1:	41 83 c7 02          	add    $0x2,%r15d
              data[1].a = x;
    32c5:	41 89 b9 9c 06 00 00 	mov    %edi,0x69c(%r9)
    32cc:	89 c1                	mov    %eax,%ecx
    32ce:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].c = b;
    32d3:	45 89 a1 a4 06 00 00 	mov    %r12d,0x6a4(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    32da:	41 83 c4 01          	add    $0x1,%r12d
              mailboxes[b].lower = &data[0];
    32de:	4d 89 4d c8          	mov    %r9,-0x38(%r13)
    32e2:	41 89 45 fc          	mov    %eax,-0x4(%r13)
    32e6:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    32e8:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].b = y;
    32f3:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[0].finished_reading = 1;
    32fa:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              mailboxes[b].kind = MAILBOX_FRIEND;
    3305:	41 c7 45 f8 01 00 00 00 	movl   $0x1,-0x8(%r13)
              data[0].finished_reading = 1;
    330d:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    3312:	e8 89 f1 ff ff       	call   24a0 <__printf_chk@plt>
              data[0].messages = messages;
    3317:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    331c:	4c 8b 5c 24 58       	mov    0x58(%rsp),%r11
              data[0].messages_count = 0;
    3321:	66 0f 6f 35 57 59 00 00 	movdqa 0x5957(%rip),%xmm6        # 8c80 <_IO_stdin_used+0xc80>
              data[1].messages = messages2;
    3329:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
              data[0].messages = messages;
    332e:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    3331:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    3338:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    3340:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3348:	41 83 fc 06          	cmp    $0x6,%r12d
    334c:	0f 85 b8 fe ff ff    	jne    320a <main+0xbba>
    3352:	48 8b 4c 24 68       	mov    0x68(%rsp),%rcx
    3357:	e9 d5 f9 ff ff       	jmp    2d31 <main+0x6e1>
    335c:	48 8d 05 4d 3a 00 00 	lea    0x3a4d(%rip),%rax        # 6db0 <barriered_work_ingest_andwork>
    3363:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    3368:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    336f:	e9 f5 f7 ff ff       	jmp    2b69 <main+0x519>
    3374:	48 8d 05 95 32 00 00 	lea    0x3295(%rip),%rax        # 6610 <barriered_work>
    337b:	bd 02 00 00 00       	mov    $0x2,%ebp
    3380:	eb e6                	jmp    3368 <main+0xd18>
  for (int k = 0 ; k < group_count ; k++) {
    3382:	83 c0 02             	add    $0x2,%eax
    3385:	48 81 c2 90 01 00 00 	add    $0x190,%rdx
    338c:	83 f8 06             	cmp    $0x6,%eax
    338f:	0f 85 8c fd ff ff    	jne    3121 <main+0xad1>
    3395:	48 8d 3d 4c 50 00 00 	lea    0x504c(%rip),%rdi        # 83e8 <_IO_stdin_used+0x3e8>
    339c:	e8 7f ef ff ff       	call   2320 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    33a1:	48 8d 35 aa 4e 00 00 	lea    0x4eaa(%rip),%rsi        # 8252 <_IO_stdin_used+0x252>
    33a8:	48 8d 3d 4e 50 00 00 	lea    0x504e(%rip),%rdi        # 83fd <_IO_stdin_used+0x3fd>
    33af:	e8 2c f1 ff ff       	call   24e0 <fopen@plt>
    33b4:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas_size; x++) {
    33b7:	45 85 e4             	test   %r12d,%r12d
    33ba:	7e 7a                	jle    3436 <main+0xde6>
    33bc:	48 8d 05 5b 50 00 00 	lea    0x505b(%rip),%rax        # 841e <_IO_stdin_used+0x41e>
    33c3:	4d 63 e4             	movslq %r12d,%r12
    33c6:	49 89 ed             	mov    %rbp,%r13
    33c9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    33ce:	4a 8d 6c e5 00       	lea    0x0(%rbp,%r12,8),%rbp
    33d3:	4c 8d 35 02 50 00 00 	lea    0x5002(%rip),%r14        # 83dc <_IO_stdin_used+0x3dc>
    char * c = calloc(250, sizeof(char));
    33da:	be 01 00 00 00       	mov    $0x1,%esi
    33df:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    33e4:	49 83 c5 08          	add    $0x8,%r13
    char * c = calloc(250, sizeof(char));
    33e8:	e8 03 f0 ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    33ed:	4c 89 f1             	mov    %r14,%rcx
    33f0:	ba fa 00 00 00       	mov    $0xfa,%edx
    33f5:	be 01 00 00 00       	mov    $0x1,%esi
    33fa:	49 89 c4             	mov    %rax,%r12
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    33fd:	49 8b 45 f8          	mov    -0x8(%r13),%rax
    3401:	4c 89 e7             	mov    %r12,%rdi
    3404:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    340b:	31 c0                	xor    %eax,%eax
    340d:	e8 6e f1 ff ff       	call   2580 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3412:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3417:	4c 89 e2             	mov    %r12,%rdx
    341a:	31 c0                	xor    %eax,%eax
    341c:	bf 01 00 00 00       	mov    $0x1,%edi
    3421:	e8 7a f0 ff ff       	call   24a0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3426:	4c 89 fe             	mov    %r15,%rsi
    3429:	4c 89 e7             	mov    %r12,%rdi
    342c:	e8 7f ef ff ff       	call   23b0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    3431:	4c 39 ed             	cmp    %r13,%rbp
    3434:	75 a4                	jne    33da <main+0xd8a>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    3436:	4c 89 ff             	mov    %r15,%rdi

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    3439:	31 ed                	xor    %ebp,%ebp
    343b:	4c 8d 35 06 50 00 00 	lea    0x5006(%rip),%r14        # 8448 <_IO_stdin_used+0x448>
  fclose(m1);
    3442:	e8 09 ef ff ff       	call   2350 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3447:	48 8d 3d b8 4f 00 00 	lea    0x4fb8(%rip),%rdi        # 8406 <_IO_stdin_used+0x406>
    344e:	41 89 ec             	mov    %ebp,%r12d
    3451:	e8 ca ee ff ff       	call   2320 <puts@plt>
    3456:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    345b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3460:	44 89 e2             	mov    %r12d,%edx
    3463:	48 8d 35 b7 4f 00 00 	lea    0x4fb7(%rip),%rsi        # 8421 <_IO_stdin_used+0x421>
    346a:	31 c0                	xor    %eax,%eax
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    346c:	45 31 ed             	xor    %r13d,%r13d
    346f:	bf 01 00 00 00       	mov    $0x1,%edi
    3474:	47 8d 3c 24          	lea    (%r12,%r12,1),%r15d
    3478:	e8 23 f0 ff ff       	call   24a0 <__printf_chk@plt>
    347d:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    3482:	44 89 7c 24 10       	mov    %r15d,0x10(%rsp)
    3487:	44 89 e8             	mov    %r13d,%eax
    348a:	49 89 ed             	mov    %rbp,%r13
    348d:	89 dd                	mov    %ebx,%ebp
    348f:	89 c3                	mov    %eax,%ebx
      int x = (k * threads_per_group) + d;
    3491:	8b 44 24 10          	mov    0x10(%rsp),%eax
    3495:	89 da                	mov    %ebx,%edx
    3497:	48 8d 35 8d 4f 00 00 	lea    0x4f8d(%rip),%rsi        # 842b <_IO_stdin_used+0x42b>
    349e:	45 31 ff             	xor    %r15d,%r15d
    34a1:	bf 01 00 00 00       	mov    $0x1,%edi
    34a6:	8d 0c 03             	lea    (%rbx,%rax,1),%ecx
    34a9:	31 c0                	xor    %eax,%eax
    34ab:	e8 f0 ef ff ff       	call   24a0 <__printf_chk@plt>
    34b0:	89 6c 24 18          	mov    %ebp,0x18(%rsp)
    34b4:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
    34b9:	89 5c 24 28          	mov    %ebx,0x28(%rsp)
    34bd:	44 89 fa             	mov    %r15d,%edx
    34c0:	48 8d 35 76 4f 00 00 	lea    0x4f76(%rip),%rsi        # 843d <_IO_stdin_used+0x43d>
    34c7:	31 c0                	xor    %eax,%eax
    34c9:	4c 89 fb             	mov    %r15,%rbx
    34cc:	bf 01 00 00 00       	mov    $0x1,%edi
    34d1:	48 c1 e3 09          	shl    $0x9,%rbx
    34d5:	45 31 e4             	xor    %r12d,%r12d
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    34d8:	31 ed                	xor    %ebp,%ebp
    34da:	e8 c1 ef ff ff       	call   24a0 <__printf_chk@plt>
    34df:	eb 31                	jmp    3512 <main+0xec2>
    34e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    34e8:	83 fa 01             	cmp    $0x1,%edx
    34eb:	0f 84 91 00 00 00    	je     3582 <main+0xf32>
    34f1:	44 8b 40 34          	mov    0x34(%rax),%r8d
    34f5:	89 ea                	mov    %ebp,%edx
    34f7:	4c 89 f6             	mov    %r14,%rsi
    34fa:	bf 01 00 00 00       	mov    $0x1,%edi
    34ff:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3501:	83 c5 01             	add    $0x1,%ebp
    3504:	49 83 c4 38          	add    $0x38,%r12
    3508:	e8 93 ef ff ff       	call   24a0 <__printf_chk@plt>
    350d:	83 fd 06             	cmp    $0x6,%ebp
    3510:	74 43                	je     3555 <main+0xf05>
          char * mailbox_kind = calloc(100, sizeof(char));
    3512:	be 01 00 00 00       	mov    $0x1,%esi
    3517:	bf 64 00 00 00       	mov    $0x64,%edi
    351c:	e8 cf ee ff ff       	call   23f0 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3521:	49 8b 75 38          	mov    0x38(%r13),%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
    3525:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3528:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    3530:	4c 01 e0             	add    %r12,%rax
    3533:	8b 50 30             	mov    0x30(%rax),%edx
    3536:	83 fa 02             	cmp    $0x2,%edx
    3539:	75 ad                	jne    34e8 <main+0xe98>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    353b:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    3545:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    3548:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    3550:	4c 01 e0             	add    %r12,%rax
    3553:	eb 9c                	jmp    34f1 <main+0xea1>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3555:	49 83 c7 01          	add    $0x1,%r15
    3559:	49 83 ff 03          	cmp    $0x3,%r15
    355d:	0f 85 5a ff ff ff    	jne    34bd <main+0xe6d>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3563:	8b 5c 24 28          	mov    0x28(%rsp),%ebx
    3567:	8b 6c 24 18          	mov    0x18(%rsp),%ebp
    356b:	49 81 c5 c8 00 00 00 	add    $0xc8,%r13
    3572:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    3577:	85 db                	test   %ebx,%ebx
    3579:	75 24                	jne    359f <main+0xf4f>
    357b:	89 eb                	mov    %ebp,%ebx
    357d:	e9 0f ff ff ff       	jmp    3491 <main+0xe41>
    3582:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3588:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    358f:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    3597:	4c 01 e0             	add    %r12,%rax
    359a:	e9 52 ff ff ff       	jmp    34f1 <main+0xea1>
  for (int k = 0 ; k < group_count ; k++) {
    359f:	48 81 44 24 08 90 01 00 00 	addq   $0x190,0x8(%rsp)
    35a8:	41 83 c4 01          	add    $0x1,%r12d
    35ac:	41 89 dd             	mov    %ebx,%r13d
    35af:	89 eb                	mov    %ebp,%ebx
    35b1:	41 83 fc 03          	cmp    $0x3,%r12d
    35b5:	0f 85 a5 fe ff ff    	jne    3460 <main+0xe10>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    35bb:	ba 07 00 00 00       	mov    $0x7,%edx
    35c0:	bf 01 00 00 00       	mov    $0x1,%edi
    35c5:	31 c0                	xor    %eax,%eax
    35c7:	45 89 ec             	mov    %r13d,%r12d
    35ca:	48 8d 35 92 4e 00 00 	lea    0x4e92(%rip),%rsi        # 8463 <_IO_stdin_used+0x463>
    35d1:	e8 ca ee ff ff       	call   24a0 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    35d6:	be 08 00 00 00       	mov    $0x8,%esi
    35db:	bf 02 00 00 00       	mov    $0x2,%edi
    35e0:	e8 0b ee ff ff       	call   23f0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    35e5:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    35ea:	be 38 00 00 00       	mov    $0x38,%esi
    35ef:	bf 0a 00 00 00       	mov    $0xa,%edi
    my_thread_data[0] = &thread_data[x]; 
    35f4:	4c 8d b5 78 05 00 00 	lea    0x578(%rbp),%r14
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    35fb:	48 89 68 08          	mov    %rbp,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    35ff:	4c 8d ad c8 00 00 00 	lea    0xc8(%rbp),%r13
    thread_data[x].threads = my_thread_data;
    3606:	48 89 85 90 05 00 00 	mov    %rax,0x590(%rbp)
    my_thread_data[0] = &thread_data[x]; 
    360d:	4c 89 30             	mov    %r14,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3610:	48 8b 45 38          	mov    0x38(%rbp),%rax
    thread_data[x].thread_count = 2;
    3614:	c7 85 a0 05 00 00 02 00 00 00 	movl   $0x2,0x5a0(%rbp)
    thread_data[x].thread_index = 0;
    361e:	c7 85 7c 05 00 00 00 00 00 00 	movl   $0x0,0x57c(%rbp)
    thread_data[x].task_count = total_barrier_count;
    3628:	c7 85 b8 05 00 00 03 00 00 00 	movl   $0x3,0x5b8(%rbp)
    thread_data[n].tasks[0].scheduled = 1;
    3632:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    363c:	48 8b 85 00 01 00 00 	mov    0x100(%rbp),%rax
    3643:	4c 89 6c 24 08       	mov    %r13,0x8(%rsp)
    3648:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3652:	e8 99 ed ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3657:	be 38 00 00 00       	mov    $0x38,%esi
    365c:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3661:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3666:	e8 85 ed ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    366b:	be 38 00 00 00       	mov    $0x38,%esi
    3670:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3675:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3678:	e8 73 ed ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    367d:	be 38 00 00 00       	mov    $0x38,%esi
    3682:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3687:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    368c:	e8 5f ed ff ff       	call   23f0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3691:	be 08 00 00 00       	mov    $0x8,%esi
    3696:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    369b:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    36a0:	e8 4b ed ff ff       	call   23f0 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    36a5:	be 08 00 00 00       	mov    $0x8,%esi
    36aa:	bf 0a 00 00 00       	mov    $0xa,%edi
  thread_data[timer_threadi].type = TIMER;
    36af:	c7 85 bc 04 00 00 00 00 00 00 	movl   $0x0,0x4bc(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    36b9:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    36bc:	48 8b 05 f5 55 00 00 	mov    0x55f5(%rip),%rax        # 8cb8 <_IO_stdin_used+0xcb8>
    36c3:	48 89 85 f0 04 00 00 	mov    %rax,0x4f0(%rbp)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    36ca:	e8 21 ed ff ff       	call   23f0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    36cf:	48 8d 95 90 01 00 00 	lea    0x190(%rbp),%rdx
    36d6:	bf 01 00 00 00       	mov    $0x1,%edi
    36db:	48 8d 8d b0 04 00 00 	lea    0x4b0(%rbp),%rcx
    36e2:	48 89 50 10          	mov    %rdx,0x10(%rax)
    36e6:	48 8d 95 58 02 00 00 	lea    0x258(%rbp),%rdx
    36ed:	48 8d 35 7e 4d 00 00 	lea    0x4d7e(%rip),%rsi        # 8472 <_IO_stdin_used+0x472>
    36f4:	48 89 50 18          	mov    %rdx,0x18(%rax)
    36f8:	48 8d 95 20 03 00 00 	lea    0x320(%rbp),%rdx
    36ff:	48 89 50 20          	mov    %rdx,0x20(%rax)
    3703:	48 8d 95 e8 03 00 00 	lea    0x3e8(%rbp),%rdx
    370a:	4c 89 68 08          	mov    %r13,0x8(%rax)
    370e:	4c 8d ad 40 06 00 00 	lea    0x640(%rbp),%r13
    3715:	48 89 50 28          	mov    %rdx,0x28(%rax)
    3719:	48 8d 95 08 07 00 00 	lea    0x708(%rbp),%rdx
    3720:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3724:	4c 89 70 38          	mov    %r14,0x38(%rax)
    3728:	48 89 50 48          	mov    %rdx,0x48(%rax)
    372c:	ba 06 00 00 00       	mov    $0x6,%edx
    3731:	48 89 28             	mov    %rbp,(%rax)
    3734:	4c 89 68 40          	mov    %r13,0x40(%rax)
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3738:	48 89 85 c8 04 00 00 	mov    %rax,0x4c8(%rbp)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    373f:	48 8b 05 7a 55 00 00 	mov    0x557a(%rip),%rax        # 8cc0 <_IO_stdin_used+0xcc0>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3746:	c7 85 e0 04 00 00 06 00 00 00 	movl   $0x6,0x4e0(%rbp)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3750:	48 89 85 d8 04 00 00 	mov    %rax,0x4d8(%rbp)
    3757:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    3759:	c7 85 b4 04 00 00 00 00 00 00 	movl   $0x0,0x4b4(%rbp)
    my_thread_data[n] = &thread_data[n]; 
    3763:	48 89 4c 24 28       	mov    %rcx,0x28(%rsp)
    3768:	e8 33 ed ff ff       	call   24a0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    376d:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3772:	49 8d b7 50 01 00 00 	lea    0x150(%r15),%rsi
  for (int k = 0 ; k < group_count ; k++) {
    3779:	45 31 ff             	xor    %r15d,%r15d
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    377c:	48 8d 15 1d 0d 00 00 	lea    0xd1d(%rip),%rdx        # 44a0 <timer_thread>
    3783:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    3787:	e8 34 ed ff ff       	call   24c0 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    378c:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    3791:	48 89 d9             	mov    %rbx,%rcx
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3794:	48 89 ea             	mov    %rbp,%rdx
    3797:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    379c:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    37a2:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    37a7:	4c 89 6c 24 40       	mov    %r13,0x40(%rsp)
    37ac:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    37b1:	45 89 d6             	mov    %r10d,%r14d
    for (int d = 0 ; d < threads_per_group ; d++) {
    37b4:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    37b9:	47 8d 24 3f          	lea    (%r15,%r15,1),%r12d
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    37bd:	49 89 c5             	mov    %rax,%r13
    37c0:	48 89 cb             	mov    %rcx,%rbx
    37c3:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    37c8:	48 89 d5             	mov    %rdx,%rbp
    37cb:	48 89 54 24 58       	mov    %rdx,0x58(%rsp)
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    37d0:	c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%rbp)
    37d7:	44 89 e2             	mov    %r12d,%edx
    37da:	44 89 f9             	mov    %r15d,%ecx
    37dd:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    37df:	c7 45 44 01 00 00 00 	movl   $0x1,0x44(%rbp)
    37e6:	48 8d 35 03 50 00 00 	lea    0x5003(%rip),%rsi        # 87f0 <_IO_stdin_used+0x7f0>
    37ed:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    37f2:	41 83 c4 01          	add    $0x1,%r12d
    37f6:	e8 a5 ec ff ff       	call   24a0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    37fb:	48 89 e9             	mov    %rbp,%rcx
    37fe:	4c 89 ee             	mov    %r13,%rsi
    3801:	48 89 df             	mov    %rbx,%rdi
    3804:	48 8d 15 95 27 00 00 	lea    0x2795(%rip),%rdx        # 5fa0 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    380b:	48 81 c5 c8 00 00 00 	add    $0xc8,%rbp
    3812:	48 83 c3 08          	add    $0x8,%rbx
    3816:	49 83 c5 38          	add    $0x38,%r13
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    381a:	e8 a1 ec ff ff       	call   24c0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    381f:	48 8b 55 e8          	mov    -0x18(%rbp),%rdx
    3823:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    3827:	be 08 00 00 00       	mov    $0x8,%esi
    382c:	e8 df ea ff ff       	call   2310 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3831:	45 39 e6             	cmp    %r12d,%r14d
    3834:	75 9a                	jne    37d0 <main+0x1180>
  for (int k = 0 ; k < group_count ; k++) {
    3836:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    383b:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    3840:	41 83 c7 01          	add    $0x1,%r15d
    3844:	41 83 c6 02          	add    $0x2,%r14d
    3848:	48 8b 54 24 58       	mov    0x58(%rsp),%rdx
    384d:	48 83 c1 10          	add    $0x10,%rcx
    3851:	48 83 c0 70          	add    $0x70,%rax
    3855:	48 81 c2 90 01 00 00 	add    $0x190,%rdx
    385c:	41 83 ff 03          	cmp    $0x3,%r15d
    3860:	0f 85 4e ff ff ff    	jne    37b4 <main+0x1164>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    3866:	4c 8b 7c 24 38       	mov    0x38(%rsp),%r15
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    386b:	be d8 00 00 00       	mov    $0xd8,%esi
    3870:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3875:	48 8b 05 4c 54 00 00 	mov    0x544c(%rip),%rax        # 8cc8 <_IO_stdin_used+0xcc8>
    thread_data[x].type = IO;
    387c:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    3881:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
    3886:	41 c7 87 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r15)
    3891:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    thread_data[x].task_count = 0;
    3896:	49 89 87 b8 05 00 00 	mov    %rax,0x5b8(%r15)
    thread_data[x].type = IO;
    389d:	4c 8b 6c 24 40       	mov    0x40(%rsp),%r13
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    38a2:	e8 49 eb ff ff       	call   23f0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    38a7:	be 00 08 00 00       	mov    $0x800,%esi
    38ac:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    38ae:	49 89 87 d0 05 00 00 	mov    %rax,0x5d0(%r15)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    38b5:	e8 56 ec ff ff       	call   2510 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    38ba:	be 08 00 00 00       	mov    $0x8,%esi
    38bf:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    38c4:	41 89 87 d8 05 00 00 	mov    %eax,0x5d8(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    38cb:	e8 20 eb ff ff       	call   23f0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    38d0:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    38d5:	41 c7 87 a0 05 00 00 02 00 00 00 	movl   $0x2,0x5a0(%r15)
    38e0:	ba 07 00 00 00       	mov    $0x7,%edx
      my_thread_data[n] = &thread_data[n]; 
    38e5:	4c 89 38             	mov    %r15,(%rax)
    38e8:	48 8d 35 a1 4b 00 00 	lea    0x4ba1(%rip),%rsi        # 8490 <_IO_stdin_used+0x490>
    38ef:	48 89 78 08          	mov    %rdi,0x8(%rax)
    38f3:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].threads = my_thread_data;
    38f8:	49 89 87 90 05 00 00 	mov    %rax,0x590(%r15)
    38ff:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3901:	41 c7 87 7c 05 00 00 07 00 00 00 	movl   $0x7,0x57c(%r15)
    390c:	4d 89 ef             	mov    %r13,%r15
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    390f:	41 bd 08 00 00 00    	mov    $0x8,%r13d
    3915:	e8 86 eb ff ff       	call   24a0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    391a:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    391f:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3923:	4c 89 f1             	mov    %r14,%rcx
    3926:	48 8d 15 83 1e 00 00 	lea    0x1e83(%rip),%rdx        # 57b0 <io_thread>
    392d:	4c 8d 73 40          	lea    0x40(%rbx),%r14
    3931:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3938:	e8 83 eb ff ff       	call   24c0 <pthread_create@plt>
    393d:	ba 08 00 00 00       	mov    $0x8,%edx
    3942:	48 8d 35 5e 4b 00 00 	lea    0x4b5e(%rip),%rsi        # 84a7 <_IO_stdin_used+0x4a7>
    3949:	31 c0                	xor    %eax,%eax
    394b:	bf 01 00 00 00       	mov    $0x1,%edi
    3950:	e8 4b eb ff ff       	call   24a0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3955:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    395a:	44 89 e0             	mov    %r12d,%eax
    395d:	49 89 dc             	mov    %rbx,%r12
    3960:	89 c3                	mov    %eax,%ebx
    3962:	48 81 c5 c0 01 00 00 	add    $0x1c0,%rbp
    3969:	44 89 ea             	mov    %r13d,%edx
    396c:	48 8d 35 4a 4b 00 00 	lea    0x4b4a(%rip),%rsi        # 84bd <_IO_stdin_used+0x4bd>
    3973:	bf 01 00 00 00       	mov    $0x1,%edi
    3978:	31 c0                	xor    %eax,%eax
    397a:	e8 21 eb ff ff       	call   24a0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    397f:	be 08 00 00 00       	mov    $0x8,%esi
    3984:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3989:	48 8b 05 38 53 00 00 	mov    0x5338(%rip),%rax        # 8cc8 <_IO_stdin_used+0xcc8>
    thread_data[x].type = EXTERNAL;
    3990:	41 c7 47 0c 03 00 00 00 	movl   $0x3,0xc(%r15)
    thread_data[x].task_count = 0;
    3998:	49 89 47 40          	mov    %rax,0x40(%r15)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    399c:	e8 4f ea ff ff       	call   23f0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    39a1:	48 8b bc 24 98 00 00 00 	mov    0x98(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    39a9:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    39ae:	41 c7 87 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r15)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    39b9:	49 89 47 50          	mov    %rax,0x50(%r15)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    39bd:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    39c0:	bf 02 00 00 00       	mov    $0x2,%edi
    39c5:	e8 26 ea ff ff       	call   23f0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    39ca:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    39cf:	4c 89 f9             	mov    %r15,%rcx
    39d2:	4c 89 f7             	mov    %r14,%rdi
    thread_data[x].threads = my_thread_data;
    39d5:	49 89 47 18          	mov    %rax,0x18(%r15)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    39d9:	48 8d 15 b0 09 00 00 	lea    0x9b0(%rip),%rdx        # 4390 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    39e0:	49 83 c6 08          	add    $0x8,%r14
    39e4:	49 81 c7 c8 00 00 00 	add    $0xc8,%r15
      my_thread_data[n] = &thread_data[n]; 
    39eb:	48 89 30             	mov    %rsi,(%rax)
    39ee:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    thread_data[x].thread_index = x;
    39f3:	45 89 af 3c ff ff ff 	mov    %r13d,-0xc4(%r15)
      my_thread_data[n] = &thread_data[n]; 
    39fa:	48 89 70 08          	mov    %rsi,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    39fe:	48 8b 05 a3 52 00 00 	mov    0x52a3(%rip),%rax        # 8ca8 <_IO_stdin_used+0xca8>
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3a05:	48 89 ee             	mov    %rbp,%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a08:	48 83 c5 38          	add    $0x38,%rbp
    thread_data[x].thread_count = thread_count;
    3a0c:	49 89 87 60 ff ff ff 	mov    %rax,-0xa0(%r15)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3a13:	e8 a8 ea ff ff       	call   24c0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a18:	48 83 84 24 98 00 00 00 10 	addq   $0x10,0x98(%rsp)
    3a21:	41 83 fd 08          	cmp    $0x8,%r13d
    3a25:	75 41                	jne    3a68 <main+0x1418>
    3a27:	41 bd 09 00 00 00    	mov    $0x9,%r13d
    3a2d:	e9 37 ff ff ff       	jmp    3969 <main+0x1319>
        other = (x + 1) % total_threads;
    3a32:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
        my_thread_data[1] = &thread_data[other]; 
    3a37:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3a3c:	48 89 5c 24 40       	mov    %rbx,0x40(%rsp)
    3a41:	45 31 c0             	xor    %r8d,%r8d
    3a44:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
        other = (x + 1) % total_threads;
    3a48:	45 89 e5             	mov    %r12d,%r13d
        my_thread_data[1] = &thread_data[other]; 
    3a4b:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3a4f:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
        my_thread_data[0] = &thread_data[x]; 
    3a53:	4c 89 c8             	mov    %r9,%rax
    3a56:	e9 7b ef ff ff       	jmp    29d6 <main+0x386>
            CPU_SET(j, sendercpu);
    3a5b:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
          for (int j = 0 ; j < cores ; j++) {
    3a63:	e9 06 f0 ff ff       	jmp    2a6e <main+0x41e>
    3a68:	89 d8                	mov    %ebx,%eax
    3a6a:	4c 89 e3             	mov    %r12,%rbx
    3a6d:	48 8d 2d 66 4a 00 00 	lea    0x4a66(%rip),%rbp        # 84da <_IO_stdin_used+0x4da>
    3a74:	41 89 c4             	mov    %eax,%r12d
    3a77:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3a7c:	4c 8d 70 04          	lea    0x4(%rax),%r14
    3a80:	4c 8d a8 d4 07 00 00 	lea    0x7d4(%rax),%r13
    3a87:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    3a8b:	41 8b 16             	mov    (%r14),%edx
    3a8e:	48 89 ee             	mov    %rbp,%rsi
    3a91:	bf 01 00 00 00       	mov    $0x1,%edi
    3a96:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3a98:	49 81 c6 c8 00 00 00 	add    $0xc8,%r14
    3a9f:	e8 fc e9 ff ff       	call   24a0 <__printf_chk@plt>
    3aa4:	4d 39 f5             	cmp    %r14,%r13
    3aa7:	75 de                	jne    3a87 <main+0x1437>
    3aa9:	48 8d 3d 3d 4a 00 00 	lea    0x4a3d(%rip),%rdi        # 84ed <_IO_stdin_used+0x4ed>
    3ab0:	45 31 f6             	xor    %r14d,%r14d
    3ab3:	4c 8d ac 24 d0 00 00 00 	lea    0xd0(%rsp),%r13
    3abb:	e8 60 e8 ff ff       	call   2320 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3ac0:	48 8d 2d 44 4a 00 00 	lea    0x4a44(%rip),%rbp        # 850b <_IO_stdin_used+0x50b>
    void * result; 
    pthread_join(thread[x], &result);
    3ac7:	4a 8b 3c f3          	mov    (%rbx,%r14,8),%rdi
    3acb:	4c 89 ee             	mov    %r13,%rsi
    3ace:	e8 7d ea ff ff       	call   2550 <pthread_join@plt>
    3ad3:	44 89 f2             	mov    %r14d,%edx
    3ad6:	48 89 ee             	mov    %rbp,%rsi
    3ad9:	bf 01 00 00 00       	mov    $0x1,%edi
    3ade:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3ae0:	49 83 c6 01          	add    $0x1,%r14
    3ae4:	e8 b7 e9 ff ff       	call   24a0 <__printf_chk@plt>
    3ae9:	49 83 fe 0a          	cmp    $0xa,%r14
    3aed:	75 d8                	jne    3ac7 <main+0x1477>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3aef:	be 08 00 00 00       	mov    $0x8,%esi
    3af4:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    3af9:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3afb:	e8 f0 e8 ff ff       	call   23f0 <calloc@plt>
    3b00:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3b05:	49 89 c7             	mov    %rax,%r15
    3b08:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3b0a:	49 89 d1             	mov    %rdx,%r9
    3b0d:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3b10:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3b14:	45 85 d2             	test   %r10d,%r10d
    3b17:	0f 8e 98 00 00 00    	jle    3bb5 <main+0x1565>
    3b1d:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3b21:	4d 63 c2             	movslq %r10d,%r8
    3b24:	48 63 cb             	movslq %ebx,%rcx
    3b27:	49 c1 e0 09          	shl    $0x9,%r8
    3b2b:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    3b2f:	49 01 f8             	add    %rdi,%r8
    3b32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3b38:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3b3f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3b46:	48 83 c6 60          	add    $0x60,%rsi
    3b4a:	f3 0f 7e 61 38       	movq   0x38(%rcx),%xmm4
    3b4f:	f3 0f 7e 59 70       	movq   0x70(%rcx),%xmm3
    3b54:	f3 0f 7e 91 a8 00 00 00 	movq   0xa8(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3b5c:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3b60:	f3 0f 7e 89 e0 00 00 00 	movq   0xe0(%rcx),%xmm1
    3b68:	0f 16 61 40          	movhps 0x40(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3b6c:	0f 16 59 78          	movhps 0x78(%rcx),%xmm3
    3b70:	f3 0f 7e 81 18 01 00 00 	movq   0x118(%rcx),%xmm0
    3b78:	0f 16 91 b0 00 00 00 	movhps 0xb0(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3b7f:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    3b83:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3b87:	0f 16 89 e8 00 00 00 	movhps 0xe8(%rcx),%xmm1
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3b8e:	0f 16 81 20 01 00 00 	movhps 0x120(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3b95:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3b99:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3b9d:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3ba1:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3ba5:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3ba9:	4c 39 c7             	cmp    %r8,%rdi
    3bac:	75 8a                	jne    3b38 <main+0x14e8>
    3bae:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3bb2:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    3bb5:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
    3bbc:	45 85 db             	test   %r11d,%r11d
    3bbf:	75 08                	jne    3bc9 <main+0x1579>
    3bc1:	45 89 e3             	mov    %r12d,%r11d
    3bc4:	e9 47 ff ff ff       	jmp    3b10 <main+0x14c0>
  for (int k = 0 ; k < group_count ; k++) {
    3bc9:	83 c0 02             	add    $0x2,%eax
    3bcc:	48 81 c2 90 01 00 00 	add    $0x190,%rdx
    3bd3:	83 f8 06             	cmp    $0x6,%eax
    3bd6:	0f 85 2e ff ff ff    	jne    3b0a <main+0x14ba>
    3bdc:	48 8d 3d 3c 49 00 00 	lea    0x493c(%rip),%rdi        # 851f <_IO_stdin_used+0x51f>
    3be3:	e8 38 e7 ff ff       	call   2320 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3be8:	48 8d 35 63 46 00 00 	lea    0x4663(%rip),%rsi        # 8252 <_IO_stdin_used+0x252>
    3bef:	48 8d 3d 41 49 00 00 	lea    0x4941(%rip),%rdi        # 8537 <_IO_stdin_used+0x537>
    3bf6:	e8 e5 e8 ff ff       	call   24e0 <fopen@plt>
    3bfb:	49 89 c4             	mov    %rax,%r12
  for (int x = 0 ; x < datas2_size; x++) {
    3bfe:	85 db                	test   %ebx,%ebx
    3c00:	7e 76                	jle    3c78 <main+0x1628>
    3c02:	48 8d 05 15 48 00 00 	lea    0x4815(%rip),%rax        # 841e <_IO_stdin_used+0x41e>
    3c09:	48 63 db             	movslq %ebx,%rbx
    3c0c:	4c 8d 35 c9 47 00 00 	lea    0x47c9(%rip),%r14        # 83dc <_IO_stdin_used+0x3dc>
    3c13:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3c18:	49 8d 2c df          	lea    (%r15,%rbx,8),%rbp
    char * c = calloc(250, sizeof(char));
    3c1c:	be 01 00 00 00       	mov    $0x1,%esi
    3c21:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3c26:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    3c2a:	e8 c1 e7 ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3c2f:	4c 89 f1             	mov    %r14,%rcx
    3c32:	ba fa 00 00 00       	mov    $0xfa,%edx
    3c37:	be 01 00 00 00       	mov    $0x1,%esi
    3c3c:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3c3f:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3c43:	48 89 df             	mov    %rbx,%rdi
    3c46:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3c4d:	31 c0                	xor    %eax,%eax
    3c4f:	e8 2c e9 ff ff       	call   2580 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3c54:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3c59:	48 89 da             	mov    %rbx,%rdx
    3c5c:	31 c0                	xor    %eax,%eax
    3c5e:	bf 01 00 00 00       	mov    $0x1,%edi
    3c63:	e8 38 e8 ff ff       	call   24a0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3c68:	4c 89 e6             	mov    %r12,%rsi
    3c6b:	48 89 df             	mov    %rbx,%rdi
    3c6e:	e8 3d e7 ff ff       	call   23b0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3c73:	49 39 ef             	cmp    %rbp,%r15
    3c76:	75 a4                	jne    3c1c <main+0x15cc>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3c78:	49 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r13
  fclose(m2);
    3c82:	4c 89 e7             	mov    %r12,%rdi
  long received = 0;
    3c85:	45 31 f6             	xor    %r14d,%r14d
  long sents = 0;
    3c88:	45 31 e4             	xor    %r12d,%r12d
  fclose(m2);
    3c8b:	e8 c0 e6 ff ff       	call   2350 <fclose@plt>
    3c90:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
  long sends = 0;
    3c95:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  long ingests = 0;
    3c9e:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  long total = 0;
    3ca7:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  int datas2_size = 0; 
    3cb0:	48 8b bc 24 b0 00 00 00 	mov    0xb0(%rsp),%rdi
    3cb8:	8d 48 02             	lea    0x2(%rax),%ecx
    3cbb:	89 44 24 10          	mov    %eax,0x10(%rsp)
    3cbf:	89 4c 24 48          	mov    %ecx,0x48(%rsp)
    3cc3:	4c 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%r15
    3ccb:	48 89 7c 24 40       	mov    %rdi,0x40(%rsp)
      int x = (k * threads_per_group) + d;
    3cd0:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    3cd4:	89 f8                	mov    %edi,%eax
    3cd6:	83 c7 01             	add    $0x1,%edi
        other = abs(x - 1) % total_threads;
    3cd9:	8d 50 02             	lea    0x2(%rax),%edx
    3cdc:	89 7c 24 10          	mov    %edi,0x10(%rsp)
    3ce0:	83 e7 01             	and    $0x1,%edi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3ce3:	bf 0a 00 00 00       	mov    $0xa,%edi
    3ce8:	0f 44 c2             	cmove  %edx,%eax
    3ceb:	48 63 d8             	movslq %eax,%rbx
    3cee:	e8 0d e6 ff ff       	call   2300 <putchar@plt>
    3cf3:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3cf8:	bf 01 00 00 00       	mov    $0x1,%edi
    3cfd:	48 8d 35 3c 48 00 00 	lea    0x483c(%rip),%rsi        # 8540 <_IO_stdin_used+0x540>
    3d04:	48 8b 10             	mov    (%rax),%rdx
    3d07:	31 c0                	xor    %eax,%eax
    3d09:	e8 92 e7 ff ff       	call   24a0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3d0e:	41 8b 57 40          	mov    0x40(%r15),%edx
    3d12:	85 d2                	test   %edx,%edx
    3d14:	0f 8e b6 04 00 00    	jle    41d0 <main+0x1b80>
    3d1a:	48 63 ca             	movslq %edx,%rcx
    3d1d:	49 8b 47 38          	mov    0x38(%r15),%rax
      long v = 0;
    3d21:	31 d2                	xor    %edx,%edx
    3d23:	48 c1 e1 09          	shl    $0x9,%rcx
    3d27:	48 01 c1             	add    %rax,%rcx
    3d2a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    3d30:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3d37:	48 05 00 02 00 00    	add    $0x200,%rax
    3d3d:	48 39 c8             	cmp    %rcx,%rax
    3d40:	75 ee                	jne    3d30 <main+0x16e0>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3d42:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3d47:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    3d4b:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3d4f:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3d53:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3d57:	85 c9                	test   %ecx,%ecx
    3d59:	7e 27                	jle    3d82 <main+0x1732>
    3d5b:	48 8b 40 38          	mov    0x38(%rax),%rax
    3d5f:	48 c1 e1 09          	shl    $0x9,%rcx
    3d63:	48 01 c1             	add    %rax,%rcx
    3d66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3d70:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3d77:	48 05 00 02 00 00    	add    $0x200,%rax
    3d7d:	48 39 c8             	cmp    %rcx,%rax
    3d80:	75 ee                	jne    3d70 <main+0x1720>
    3d82:	48 8d 35 cc 47 00 00 	lea    0x47cc(%rip),%rsi        # 8555 <_IO_stdin_used+0x555>
    3d89:	bf 01 00 00 00       	mov    $0x1,%edi
    3d8e:	31 c0                	xor    %eax,%eax
    3d90:	e8 0b e7 ff ff       	call   24a0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3d95:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3d9a:	bf 01 00 00 00       	mov    $0x1,%edi
    3d9f:	48 8d 35 7a 4a 00 00 	lea    0x4a7a(%rip),%rsi        # 8820 <_IO_stdin_used+0x820>
    3da6:	48 8b 08             	mov    (%rax),%rcx
    3da9:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3db3:	48 f7 e9             	imul   %rcx
    3db6:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3dba:	31 c0                	xor    %eax,%eax
    3dbc:	48 d1 fa             	sar    %rdx
    3dbf:	48 29 ca             	sub    %rcx,%rdx
    3dc2:	e8 d9 e6 ff ff       	call   24a0 <__printf_chk@plt>
    3dc7:	bf 0a 00 00 00       	mov    $0xa,%edi
    3dcc:	e8 2f e5 ff ff       	call   2300 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3dd1:	45 8b 57 40          	mov    0x40(%r15),%r10d
    3dd5:	45 85 d2             	test   %r10d,%r10d
    3dd8:	0f 8e 01 01 00 00    	jle    3edf <main+0x188f>
        total += thread_data[x].tasks[n].n;
    3dde:	49 8b 4f 38          	mov    0x38(%r15),%rcx
    3de2:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
    3de7:	31 d2                	xor    %edx,%edx
    3de9:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    3dee:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    3df3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3df8:	48 89 d5             	mov    %rdx,%rbp
    3dfb:	89 54 24 08          	mov    %edx,0x8(%rsp)
        sends += thread_data[x].tasks[n].sends;
    3dff:	31 db                	xor    %ebx,%ebx
    3e01:	48 c1 e5 09          	shl    $0x9,%rbp
    3e05:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
        total += thread_data[x].tasks[n].n;
    3e0a:	48 01 e9             	add    %rbp,%rcx
        sends += thread_data[x].tasks[n].sends;
    3e0d:	48 89 e8             	mov    %rbp,%rax
    3e10:	4c 89 e5             	mov    %r12,%rbp
    3e13:	4d 89 f4             	mov    %r14,%r12
        total += thread_data[x].tasks[n].n;
    3e16:	4c 03 81 08 01 00 00 	add    0x108(%rcx),%r8
        ingests += thread_data[x].tasks[n].ingest_count;
    3e1d:	48 03 b1 68 01 00 00 	add    0x168(%rcx),%rsi
        sends += thread_data[x].tasks[n].sends;
    3e24:	49 89 c6             	mov    %rax,%r14
    3e27:	48 03 b9 78 01 00 00 	add    0x178(%rcx),%rdi
    3e2e:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    3e33:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    3e38:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    3e3d:	0f 1f 00             	nopl   (%rax)
    3e40:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    3e44:	8b 54 24 10          	mov    0x10(%rsp),%edx
    3e48:	41 89 d8             	mov    %ebx,%r8d
    3e4b:	bf 01 00 00 00       	mov    $0x1,%edi
    3e50:	48 8d 35 0b 47 00 00 	lea    0x470b(%rip),%rsi        # 8562 <_IO_stdin_used+0x562>
    3e57:	31 c0                	xor    %eax,%eax
    3e59:	e8 42 e6 ff ff       	call   24a0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3e5e:	49 8b 4f 38          	mov    0x38(%r15),%rcx
    3e62:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    3e6a:	48 29 d8             	sub    %rbx,%rax
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3e6d:	48 83 c3 01          	add    $0x1,%rbx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3e71:	4a 8b 94 31 70 01 00 00 	mov    0x170(%rcx,%r14,1),%rdx
    3e79:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
    3e7d:	48 8b 10             	mov    (%rax),%rdx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3e80:	48 8b 40 08          	mov    0x8(%rax),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3e84:	4c 8b 8a 08 03 00 00 	mov    0x308(%rdx),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3e8b:	4c 8b 92 10 03 00 00 	mov    0x310(%rdx),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3e92:	49 01 e9             	add    %rbp,%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3e95:	4d 01 e2             	add    %r12,%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3e98:	4c 03 88 08 03 00 00 	add    0x308(%rax),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3e9f:	4c 03 90 10 03 00 00 	add    0x310(%rax),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3ea6:	4c 89 cd             	mov    %r9,%rbp
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3ea9:	4d 89 d4             	mov    %r10,%r12
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3eac:	48 83 fb 06          	cmp    $0x6,%rbx
    3eb0:	75 8e                	jne    3e40 <main+0x17f0>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3eb2:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    3eb7:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    3ebc:	4d 89 d6             	mov    %r10,%r14
    3ebf:	4d 89 cc             	mov    %r9,%r12
    3ec2:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    3ec7:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    3ecc:	48 83 c2 01          	add    $0x1,%rdx
    3ed0:	41 39 57 40          	cmp    %edx,0x40(%r15)
    3ed4:	0f 8f 1e ff ff ff    	jg     3df8 <main+0x17a8>
    3eda:	4c 89 44 24 30       	mov    %r8,0x30(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3edf:	31 ed                	xor    %ebp,%ebp
    3ee1:	49 83 bf a0 00 00 00 00 	cmpq   $0x0,0xa0(%r15)
    3ee9:	48 8d 1d 50 49 00 00 	lea    0x4950(%rip),%rbx        # 8840 <_IO_stdin_used+0x840>
    3ef0:	7e 5f                	jle    3f51 <main+0x1901>
    3ef2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3ef8:	49 8b 87 90 00 00 00 	mov    0x90(%r15),%rax
    3eff:	48 8d 54 ad 00       	lea    0x0(%rbp,%rbp,4),%rdx
    3f04:	48 83 ec 08          	sub    $0x8,%rsp
    3f08:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3f0d:	48 83 c5 01          	add    $0x1,%rbp
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3f11:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3f15:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3f19:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3f1d:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3f20:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3f24:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3f27:	49 f7 e5             	mul    %r13
    3f2a:	8b 49 20             	mov    0x20(%rcx),%ecx
    3f2d:	56                   	push   %rsi
    3f2e:	31 c0                	xor    %eax,%eax
    3f30:	48 89 de             	mov    %rbx,%rsi
    3f33:	48 c1 ea 12          	shr    $0x12,%rdx
    3f37:	49 89 d1             	mov    %rdx,%r9
    3f3a:	ba 02 00 00 00       	mov    $0x2,%edx
    3f3f:	e8 5c e5 ff ff       	call   24a0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3f44:	41 58                	pop    %r8
    3f46:	41 59                	pop    %r9
    3f48:	49 39 af a0 00 00 00 	cmp    %rbp,0xa0(%r15)
    3f4f:	7f a7                	jg     3ef8 <main+0x18a8>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3f51:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    3f58:	85 c9                	test   %ecx,%ecx
    3f5a:	0f 8e f5 00 00 00    	jle    4055 <main+0x1a05>
    3f60:	4c 89 64 24 50       	mov    %r12,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3f65:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    3f69:	31 db                	xor    %ebx,%ebx
    3f6b:	4c 89 74 24 58       	mov    %r14,0x58(%rsp)
    3f70:	49 8b 04 d9          	mov    (%r9,%rbx,8),%rax
    3f74:	41 89 dc             	mov    %ebx,%r12d
    3f77:	4c 8d 34 dd 00 00 00 00 	lea    0x0(,%rbx,8),%r14
    3f7f:	8b 30                	mov    (%rax),%esi
    3f81:	85 f6                	test   %esi,%esi
    3f83:	0f 8e b6 00 00 00    	jle    403f <main+0x19ef>
    3f89:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3f8e:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3f92:	31 ff                	xor    %edi,%edi
    3f94:	0f 1f 40 00          	nopl   0x0(%rax)
    3f98:	48 89 fb             	mov    %rdi,%rbx
    3f9b:	31 ed                	xor    %ebp,%ebp
    3f9d:	48 c1 e3 08          	shl    $0x8,%rbx
    3fa1:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    3fa5:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    3fab:	85 d2                	test   %edx,%edx
    3fad:	7e 78                	jle    4027 <main+0x19d7>
    3faf:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    3fb4:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3fb8:	48 89 e9             	mov    %rbp,%rcx
    3fbb:	48 83 ec 08          	sub    $0x8,%rsp
    3fbf:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3fc4:	48 83 c5 01          	add    $0x1,%rbp
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3fc8:	48 c1 e1 05          	shl    $0x5,%rcx
    3fcc:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3fd3:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3fd7:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3fdb:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3fde:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3fe2:	4c 2b 01             	sub    (%rcx),%r8
    3fe5:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3fe6:	49 f7 e5             	mul    %r13
    3fe9:	44 89 e1             	mov    %r12d,%ecx
    3fec:	48 8d 35 9d 48 00 00 	lea    0x489d(%rip),%rsi        # 8890 <_IO_stdin_used+0x890>
    3ff3:	31 c0                	xor    %eax,%eax
    3ff5:	48 c1 ea 12          	shr    $0x12,%rdx
    3ff9:	49 89 d1             	mov    %rdx,%r9
    3ffc:	ba 02 00 00 00       	mov    $0x2,%edx
    4001:	e8 9a e4 ff ff       	call   24a0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    4006:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    400a:	5e                   	pop    %rsi
    400b:	5f                   	pop    %rdi
    400c:	4b 8b 14 31          	mov    (%r9,%r14,1),%rdx
    4010:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    4014:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    4018:	39 a8 94 00 00 00    	cmp    %ebp,0x94(%rax)
    401e:	7f 98                	jg     3fb8 <main+0x1968>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4020:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    4025:	8b 32                	mov    (%rdx),%esi
    4027:	48 83 c7 01          	add    $0x1,%rdi
    402b:	39 fe                	cmp    %edi,%esi
    402d:	0f 8f 65 ff ff ff    	jg     3f98 <main+0x1948>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    4033:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    4038:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    403f:	48 83 c3 01          	add    $0x1,%rbx
    4043:	39 d9                	cmp    %ebx,%ecx
    4045:	0f 8f 25 ff ff ff    	jg     3f70 <main+0x1920>
    404b:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    4050:	4c 8b 74 24 58       	mov    0x58(%rsp),%r14
    for (int d = 0 ; d < threads_per_group ; d++) {
    4055:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    405b:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    405f:	49 81 c7 c8 00 00 00 	add    $0xc8,%r15
    4066:	39 7c 24 48          	cmp    %edi,0x48(%rsp)
    406a:	0f 85 60 fc ff ff    	jne    3cd0 <main+0x1680>
  for (int k = 0 ; k < group_count ; k++) {
    4070:	48 81 84 24 80 00 00 00 90 01 00 00 	addq   $0x190,0x80(%rsp)
    407c:	8b 4c 24 48          	mov    0x48(%rsp),%ecx
    4080:	48 83 84 24 b0 00 00 00 30 	addq   $0x30,0xb0(%rsp)
    4089:	83 f9 05             	cmp    $0x5,%ecx
    408c:	74 07                	je     4095 <main+0x1a45>
    408e:	89 c8                	mov    %ecx,%eax
    4090:	e9 1b fc ff ff       	jmp    3cb0 <main+0x1660>
    4095:	4c 8b 7c 24 30       	mov    0x30(%rsp),%r15
    409a:	48 8d 35 d1 44 00 00 	lea    0x44d1(%rip),%rsi        # 8572 <_IO_stdin_used+0x572>
    40a1:	bf 01 00 00 00       	mov    $0x1,%edi
    40a6:	31 c0                	xor    %eax,%eax
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    40a8:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    40b2:	4c 89 fa             	mov    %r15,%rdx
    40b5:	e8 e6 e3 ff ff       	call   24a0 <__printf_chk@plt>
    40ba:	bf 0a 00 00 00       	mov    $0xa,%edi
    40bf:	e8 3c e2 ff ff       	call   2300 <putchar@plt>
    40c4:	48 8b bc 24 90 00 00 00 	mov    0x90(%rsp),%rdi
    40cc:	48 8d 35 15 48 00 00 	lea    0x4815(%rip),%rsi        # 88e8 <_IO_stdin_used+0x8e8>
    40d3:	31 c0                	xor    %eax,%eax
    40d5:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    40d9:	bf 01 00 00 00       	mov    $0x1,%edi
    40de:	e8 bd e3 ff ff       	call   24a0 <__printf_chk@plt>
    40e3:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    40e8:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    40ed:	48 8d 35 1c 48 00 00 	lea    0x481c(%rip),%rsi        # 8910 <_IO_stdin_used+0x910>
    40f4:	48 f7 eb             	imul   %rbx
    40f7:	48 c1 ff 3f          	sar    $0x3f,%rdi
    40fb:	31 c0                	xor    %eax,%eax
    40fd:	48 d1 fa             	sar    %rdx
    4100:	48 29 fa             	sub    %rdi,%rdx
    4103:	bf 01 00 00 00       	mov    $0x1,%edi
    4108:	e8 93 e3 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    410d:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4112:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    4117:	48 8d 35 22 48 00 00 	lea    0x4822(%rip),%rsi        # 8940 <_IO_stdin_used+0x940>
    411e:	48 f7 eb             	imul   %rbx
    4121:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4125:	31 c0                	xor    %eax,%eax
    4127:	48 d1 fa             	sar    %rdx
    412a:	48 29 fa             	sub    %rdi,%rdx
    412d:	bf 01 00 00 00       	mov    $0x1,%edi
    4132:	e8 69 e3 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    4137:	4c 89 f8             	mov    %r15,%rax
    413a:	4c 89 ff             	mov    %r15,%rdi
    413d:	48 8d 35 2c 48 00 00 	lea    0x482c(%rip),%rsi        # 8970 <_IO_stdin_used+0x970>
    4144:	48 f7 eb             	imul   %rbx
    4147:	48 c1 ff 3f          	sar    $0x3f,%rdi
    414b:	31 c0                	xor    %eax,%eax
    414d:	48 d1 fa             	sar    %rdx
    4150:	48 29 fa             	sub    %rdi,%rdx
    4153:	bf 01 00 00 00       	mov    $0x1,%edi
    4158:	e8 43 e3 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    415d:	4c 89 e0             	mov    %r12,%rax
    4160:	bf 01 00 00 00       	mov    $0x1,%edi
    4165:	48 8d 35 1a 44 00 00 	lea    0x441a(%rip),%rsi        # 8586 <_IO_stdin_used+0x586>
    416c:	48 f7 eb             	imul   %rbx
    416f:	4c 89 e0             	mov    %r12,%rax
    4172:	48 c1 f8 3f          	sar    $0x3f,%rax
    4176:	48 d1 fa             	sar    %rdx
    4179:	48 29 c2             	sub    %rax,%rdx
    417c:	31 c0                	xor    %eax,%eax
    417e:	e8 1d e3 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    4183:	4c 89 f0             	mov    %r14,%rax
    4186:	bf 01 00 00 00       	mov    $0x1,%edi
    418b:	48 8d 35 05 44 00 00 	lea    0x4405(%rip),%rsi        # 8597 <_IO_stdin_used+0x597>
    4192:	48 f7 eb             	imul   %rbx
    4195:	4c 89 f0             	mov    %r14,%rax
    4198:	48 c1 f8 3f          	sar    $0x3f,%rax
    419c:	48 d1 fa             	sar    %rdx
    419f:	48 29 c2             	sub    %rax,%rdx
    41a2:	31 c0                	xor    %eax,%eax
    41a4:	e8 f7 e2 ff ff       	call   24a0 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    41a9:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
    41b1:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    41ba:	75 25                	jne    41e1 <main+0x1b91>
    41bc:	48 81 c4 e8 00 00 00 	add    $0xe8,%rsp
    41c3:	31 c0                	xor    %eax,%eax
    41c5:	5b                   	pop    %rbx
    41c6:	5d                   	pop    %rbp
    41c7:	41 5c                	pop    %r12
    41c9:	41 5d                	pop    %r13
    41cb:	41 5e                	pop    %r14
    41cd:	41 5f                	pop    %r15
    41cf:	c3                   	ret
      long v = 0;
    41d0:	31 d2                	xor    %edx,%edx
    41d2:	e9 6b fb ff ff       	jmp    3d42 <main+0x16f2>
            exit(1);
    41d7:	bf 01 00 00 00       	mov    $0x1,%edi
    41dc:	e8 1f e3 ff ff       	call   2500 <exit@plt>
}
    41e1:	e8 8a e1 ff ff       	call   2370 <__stack_chk_fail@plt>
    41e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000041f0 <_start>:
    41f0:	f3 0f 1e fa          	endbr64
    41f4:	31 ed                	xor    %ebp,%ebp
    41f6:	49 89 d1             	mov    %rdx,%r9
    41f9:	5e                   	pop    %rsi
    41fa:	48 89 e2             	mov    %rsp,%rdx
    41fd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4201:	50                   	push   %rax
    4202:	54                   	push   %rsp
    4203:	45 31 c0             	xor    %r8d,%r8d
    4206:	31 c9                	xor    %ecx,%ecx
    4208:	48 8d 3d 41 e4 ff ff 	lea    -0x1bbf(%rip),%rdi        # 2650 <main>
    420f:	ff 15 c3 6d 00 00    	call   *0x6dc3(%rip)        # afd8 <__libc_start_main@GLIBC_2.34>
    4215:	f4                   	hlt
    4216:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004220 <deregister_tm_clones>:
    4220:	48 8d 3d f9 6d 00 00 	lea    0x6df9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4227:	48 8d 05 f2 6d 00 00 	lea    0x6df2(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    422e:	48 39 f8             	cmp    %rdi,%rax
    4231:	74 15                	je     4248 <deregister_tm_clones+0x28>
    4233:	48 8b 05 a6 6d 00 00 	mov    0x6da6(%rip),%rax        # afe0 <_ITM_deregisterTMCloneTable@Base>
    423a:	48 85 c0             	test   %rax,%rax
    423d:	74 09                	je     4248 <deregister_tm_clones+0x28>
    423f:	ff e0                	jmp    *%rax
    4241:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4248:	c3                   	ret
    4249:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004250 <register_tm_clones>:
    4250:	48 8d 3d c9 6d 00 00 	lea    0x6dc9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4257:	48 8d 35 c2 6d 00 00 	lea    0x6dc2(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    425e:	48 29 fe             	sub    %rdi,%rsi
    4261:	48 89 f0             	mov    %rsi,%rax
    4264:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4268:	48 c1 f8 03          	sar    $0x3,%rax
    426c:	48 01 c6             	add    %rax,%rsi
    426f:	48 d1 fe             	sar    %rsi
    4272:	74 14                	je     4288 <register_tm_clones+0x38>
    4274:	48 8b 05 75 6d 00 00 	mov    0x6d75(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    427b:	48 85 c0             	test   %rax,%rax
    427e:	74 08                	je     4288 <register_tm_clones+0x38>
    4280:	ff e0                	jmp    *%rax
    4282:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4288:	c3                   	ret
    4289:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004290 <__do_global_dtors_aux>:
    4290:	f3 0f 1e fa          	endbr64
    4294:	80 3d 8d 6d 00 00 00 	cmpb   $0x0,0x6d8d(%rip)        # b028 <completed.0>
    429b:	75 2b                	jne    42c8 <__do_global_dtors_aux+0x38>
    429d:	55                   	push   %rbp
    429e:	48 83 3d 52 6d 00 00 00 	cmpq   $0x0,0x6d52(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    42a6:	48 89 e5             	mov    %rsp,%rbp
    42a9:	74 0c                	je     42b7 <__do_global_dtors_aux+0x27>
    42ab:	48 8b 3d 56 6d 00 00 	mov    0x6d56(%rip),%rdi        # b008 <__dso_handle>
    42b2:	e8 29 e0 ff ff       	call   22e0 <__cxa_finalize@plt>
    42b7:	e8 64 ff ff ff       	call   4220 <deregister_tm_clones>
    42bc:	c6 05 65 6d 00 00 01 	movb   $0x1,0x6d65(%rip)        # b028 <completed.0>
    42c3:	5d                   	pop    %rbp
    42c4:	c3                   	ret
    42c5:	0f 1f 00             	nopl   (%rax)
    42c8:	c3                   	ret
    42c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000042d0 <frame_dummy>:
    42d0:	f3 0f 1e fa          	endbr64
    42d4:	e9 77 ff ff ff       	jmp    4250 <register_tm_clones>
    42d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000042e0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    42e0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    42e4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    42eb:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    42ef:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    42f7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    42fb:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    42ff:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4306:	48 85 c9             	test   %rcx,%rcx
    4309:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4310:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4314:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    4318:	31 c0                	xor    %eax,%eax
    431a:	c3                   	ret
    431b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004320 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    4320:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    4324:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    432b:	85 c9                	test   %ecx,%ecx
    432d:	7e 4f                	jle    437e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    432f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    4336:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    433d:	48 c1 e1 09          	shl    $0x9,%rcx
    4341:	48 8b 50 18          	mov    0x18(%rax),%rdx
    4345:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    4349:	48 8b 70 38          	mov    0x38(%rax),%rsi
    434d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    434f:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4353:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4358:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    4360:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    4368:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    4373:	48 05 00 02 00 00    	add    $0x200,%rax
    4379:	48 39 c1             	cmp    %rax,%rcx
    437c:	75 da                	jne    4358 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    437e:	0f ae f8             	sfence
}
    4381:	31 c0                	xor    %eax,%eax
    4383:	c3                   	ret
    4384:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    438f:	90                   	nop

0000000000004390 <external_thread>:
void * external_thread(void *arg) {
    4390:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    4394:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    4398:	0f 85 fb 00 00 00    	jne    4499 <external_thread+0x109>
void * external_thread(void *arg) {
    439e:	41 57                	push   %r15
    43a0:	49 89 ff             	mov    %rdi,%r15
    43a3:	41 56                	push   %r14
    43a5:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    43a7:	4c 8d 2d 56 3c 00 00 	lea    0x3c56(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    43ae:	41 54                	push   %r12
    43b0:	55                   	push   %rbp
    43b1:	53                   	push   %rbx
    43b2:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    43b6:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    43bc:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    43c0:	85 c9                	test   %ecx,%ecx
    43c2:	7e 6e                	jle    4432 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    43c4:	45 31 e4             	xor    %r12d,%r12d
    43c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    43d0:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    43d8:	31 db                	xor    %ebx,%ebx
    43da:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    43de:	48 8b 06             	mov    (%rsi),%rax
    43e1:	8b 10                	mov    (%rax),%edx
    43e3:	85 d2                	test   %edx,%edx
    43e5:	7e 2a                	jle    4411 <external_thread+0x81>
    43e7:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    43eb:	48 89 dd             	mov    %rbx,%rbp
    43ee:	48 c1 e5 08          	shl    $0x8,%rbp
    43f2:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    43f6:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    43fd:	45 85 c0             	test   %r8d,%r8d
    4400:	74 36                	je     4438 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4402:	48 83 c3 01          	add    $0x1,%rbx
    4406:	39 da                	cmp    %ebx,%edx
    4408:	7f e1                	jg     43eb <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    440a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    4411:	49 83 c4 01          	add    $0x1,%r12
    4415:	44 39 e1             	cmp    %r12d,%ecx
    4418:	7f b6                	jg     43d0 <external_thread+0x40>
  while (data->running == 1) {
    441a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    441f:	74 9f                	je     43c0 <external_thread+0x30>
}
    4421:	48 83 c4 08          	add    $0x8,%rsp
    4425:	31 c0                	xor    %eax,%eax
    4427:	5b                   	pop    %rbx
    4428:	5d                   	pop    %rbp
    4429:	41 5c                	pop    %r12
    442b:	41 5d                	pop    %r13
    442d:	41 5e                	pop    %r14
    442f:	41 5f                	pop    %r15
    4431:	c3                   	ret
  while (data->running == 1) {
    4432:	eb fe                	jmp    4432 <external_thread+0xa2>
    4434:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    4438:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    443b:	48 8b 06             	mov    (%rsi),%rax
    443e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4442:	48 01 ef             	add    %rbp,%rdi
    4445:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    444c:	48 c1 e6 05          	shl    $0x5,%rsi
    4450:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4457:	bf 04 00 00 00       	mov    $0x4,%edi
    445c:	e8 df de ff ff       	call   2340 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    4461:	49 8b 47 50          	mov    0x50(%r15),%rax
    4465:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    4469:	48 8b 40 08          	mov    0x8(%rax),%rax
    446d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    4478:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    447b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    447f:	48 83 c3 01          	add    $0x1,%rbx
    4483:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    4487:	48 8b 06             	mov    (%rsi),%rax
    448a:	8b 10                	mov    (%rax),%edx
    448c:	39 da                	cmp    %ebx,%edx
    448e:	0f 8f 53 ff ff ff    	jg     43e7 <external_thread+0x57>
    4494:	e9 71 ff ff ff       	jmp    440a <external_thread+0x7a>
}
    4499:	31 c0                	xor    %eax,%eax
    449b:	c3                   	ret
    449c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000044a0 <timer_thread>:
void* timer_thread(void *arg) {
    44a0:	f3 0f 1e fa          	endbr64
    44a4:	41 57                	push   %r15
    44a6:	48 8d 35 63 3b 00 00 	lea    0x3b63(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    44ad:	41 56                	push   %r14
    44af:	41 55                	push   %r13
    44b1:	41 54                	push   %r12
    44b3:	55                   	push   %rbp
    44b4:	53                   	push   %rbx
    44b5:	48 89 fb             	mov    %rdi,%rbx
    44b8:	48 83 ec 68          	sub    $0x68,%rsp
    44bc:	8b 57 04             	mov    0x4(%rdi),%edx
    44bf:	bf 01 00 00 00       	mov    $0x1,%edi
    44c4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    44cd:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    44d2:	31 c0                	xor    %eax,%eax
    44d4:	e8 c7 df ff ff       	call   24a0 <__printf_chk@plt>
  struct timespec preempt = {
    44d9:	66 0f 6f 05 af 46 00 00 	movdqa 0x46af(%rip),%xmm0        # 8b90 <_IO_stdin_used+0xb90>
    44e1:	ba 88 13 00 00       	mov    $0x1388,%edx
    44e6:	31 c0                	xor    %eax,%eax
    44e8:	48 8d 35 33 3b 00 00 	lea    0x3b33(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    44ef:	bf 01 00 00 00       	mov    $0x1,%edi
    44f4:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
    44f9:	e8 a2 df ff ff       	call   24a0 <__printf_chk@plt>
  while (data->running && n < times) {
    44fe:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4501:	85 ed                	test   %ebp,%ebp
    4503:	0f 84 9b 00 00 00    	je     45a4 <timer_thread+0x104>
  int n = 0;
    4509:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    450c:	31 ed                	xor    %ebp,%ebp
    450e:	4c 8d 74 24 10       	lea    0x10(%rsp),%r14
    y++;
    4513:	45 31 e4             	xor    %r12d,%r12d
    4516:	4c 8d 6c 24 20       	lea    0x20(%rsp),%r13
    nanosleep(&preempt , &rem2);
    451b:	4c 89 ef             	mov    %r13,%rdi
    451e:	4c 89 f6             	mov    %r14,%rsi
    n++;
    4521:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    4525:	e8 66 de ff ff       	call   2390 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    452a:	48 63 43 30          	movslq 0x30(%rbx),%rax
    y++;
    452e:	8d 7d 01             	lea    0x1(%rbp),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4531:	85 c0                	test   %eax,%eax
    4533:	7e 48                	jle    457d <timer_thread+0xdd>
    4535:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4539:	4c 63 c5             	movslq %ebp,%r8
    453c:	49 c1 e0 09          	shl    $0x9,%r8
    4540:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4544:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4548:	4c 8b 19             	mov    (%rcx),%r11
    454b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    454d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4551:	99                   	cltd
    4552:	41 f7 7b 40          	idivl  0x40(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    4556:	49 8b 73 38          	mov    0x38(%r11),%rsi
    455a:	48 63 d2             	movslq %edx,%rdx
    455d:	48 c1 e2 09          	shl    $0x9,%rdx
    4561:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    456c:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4578:	49 39 c9             	cmp    %rcx,%r9
    457b:	75 cb                	jne    4548 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    457d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4580:	48 8b 43 18          	mov    0x18(%rbx),%rax
  while (data->running && n < times) {
    4584:	8b 4b 44             	mov    0x44(%rbx),%ecx
    if (y >= data->threads[0]->task_count) {
    4587:	48 8b 00             	mov    (%rax),%rax
    y++;
    458a:	39 78 40             	cmp    %edi,0x40(%rax)
    458d:	41 0f 4e fc          	cmovle %r12d,%edi
    4591:	89 fd                	mov    %edi,%ebp
  while (data->running && n < times) {
    4593:	85 c9                	test   %ecx,%ecx
    4595:	74 0d                	je     45a4 <timer_thread+0x104>
    4597:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    459e:	0f 85 77 ff ff ff    	jne    451b <timer_thread+0x7b>
    45a4:	48 8d 3d 8d 3a 00 00 	lea    0x3a8d(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    45ab:	e8 70 dd ff ff       	call   2320 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    45b0:	48 63 53 30          	movslq 0x30(%rbx),%rdx
    45b4:	85 d2                	test   %edx,%edx
    45b6:	7e 6d                	jle    4625 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    45b8:	48 63 43 40          	movslq 0x40(%rbx),%rax
    45bc:	85 c0                	test   %eax,%eax
    45be:	7e 65                	jle    4625 <timer_thread+0x185>
    45c0:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    45c4:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    45c8:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    45d0:	31 c9                	xor    %ecx,%ecx
    45d2:	48 89 c6             	mov    %rax,%rsi
    45d5:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    45d9:	48 8b 40 38          	mov    0x38(%rax),%rax
    45dd:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    45e1:	f7 c6 00 02 00 00    	test   $0x200,%esi
    45e7:	74 17                	je     4600 <timer_thread+0x160>
    45e9:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    45f3:	48 05 00 02 00 00    	add    $0x200,%rax
    45f9:	48 39 c2             	cmp    %rax,%rdx
    45fc:	74 1e                	je     461c <timer_thread+0x17c>
    45fe:	66 90                	xchg   %ax,%ax
      data->threads[x]->tasks[y].sending = 0;
    4600:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    460a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4610:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4617:	48 39 c2             	cmp    %rax,%rdx
    461a:	75 e4                	jne    4600 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    461c:	48 83 c1 08          	add    $0x8,%rcx
    4620:	48 39 cf             	cmp    %rcx,%rdi
    4623:	75 b0                	jne    45d5 <timer_thread+0x135>
  asm volatile ("mfence" ::: "memory");
    4625:	0f ae f0             	mfence
  struct timespec drain = {
    4628:	66 0f 6f 05 70 45 00 00 	movdqa 0x4570(%rip),%xmm0        # 8ba0 <_IO_stdin_used+0xba0>
    4630:	4c 8d 3d 26 3a 00 00 	lea    0x3a26(%rip),%r15        # 805d <_IO_stdin_used+0x5d>
    4637:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    463c:	48 63 43 28          	movslq 0x28(%rbx),%rax
    y++;
    4640:	8d 7d 01             	lea    0x1(%rbp),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    4643:	85 c0                	test   %eax,%eax
    4645:	7e 4e                	jle    4695 <timer_thread+0x1f5>
    4647:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    464b:	4c 63 c5             	movslq %ebp,%r8
    464e:	49 c1 e0 09          	shl    $0x9,%r8
    4652:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4656:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    4660:	4c 8b 11             	mov    (%rcx),%r10
    4663:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    4665:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4669:	99                   	cltd
    466a:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    466e:	49 8b 72 38          	mov    0x38(%r10),%rsi
    4672:	48 63 d2             	movslq %edx,%rdx
    4675:	48 c1 e2 09          	shl    $0x9,%rdx
    4679:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4684:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4690:	4c 39 c9             	cmp    %r9,%rcx
    4693:	75 cb                	jne    4660 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    4695:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4698:	48 8b 43 18          	mov    0x18(%rbx),%rax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    469c:	44 8b 53 30          	mov    0x30(%rbx),%r10d
    if (y >= data->threads[0]->task_count) {
    46a0:	48 8b 00             	mov    (%rax),%rax
    y++;
    46a3:	39 78 40             	cmp    %edi,0x40(%rax)
    46a6:	b8 00 00 00 00       	mov    $0x0,%eax
    46ab:	0f 4f c7             	cmovg  %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46ae:	45 85 d2             	test   %r10d,%r10d
    46b1:	0f 8e 45 01 00 00    	jle    47fc <timer_thread+0x35c>
    int all_empty = 1;
    46b7:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46bb:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    46be:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    46c4:	0f 1f 40 00          	nopl   0x0(%rax)
      for (int y = 0 ; y < 2 ; y++) {
    46c8:	45 31 ed             	xor    %r13d,%r13d
    46cb:	44 89 f5             	mov    %r14d,%ebp
    46ce:	4e 8d 24 f5 00 00 00 00 	lea    0x0(,%r14,8),%r12
    46d6:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    46d9:	45 85 d2             	test   %r10d,%r10d
    46dc:	0f 8e bd 00 00 00    	jle    479f <timer_thread+0x2ff>
    46e2:	44 89 5c 24 08       	mov    %r11d,0x8(%rsp)
    46e7:	4d 89 eb             	mov    %r13,%r11
      y = 0;
    46ea:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    46ec:	45 31 c0             	xor    %r8d,%r8d
    46ef:	49 c1 e3 09          	shl    $0x9,%r11
    46f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (x == k) { continue; }
    46f8:	45 39 f0             	cmp    %r14d,%r8d
    46fb:	74 36                	je     4733 <timer_thread+0x293>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    46fd:	48 8b 53 18          	mov    0x18(%rbx),%rdx
    4701:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    4705:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4709:	4a 8b 8c 1a 70 01 00 00 	mov    0x170(%rdx,%r11,1),%rcx
    4711:	48 01 c1             	add    %rax,%rcx
    4714:	48 8b 11             	mov    (%rcx),%rdx
    4717:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    471b:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    4722:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    4729:	4d 85 c9             	test   %r9,%r9
    472c:	7f 2a                	jg     4758 <timer_thread+0x2b8>
    472e:	48 85 f6             	test   %rsi,%rsi
    4731:	7f 25                	jg     4758 <timer_thread+0x2b8>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4733:	41 83 c0 01          	add    $0x1,%r8d
    4737:	48 83 c0 38          	add    $0x38,%rax
    473b:	45 39 d0             	cmp    %r10d,%r8d
    473e:	75 b8                	jne    46f8 <timer_thread+0x258>
      for (int y = 0 ; y < 2 ; y++) {
    4740:	49 83 fd 01          	cmp    $0x1,%r13
    4744:	0f 84 9e 00 00 00    	je     47e8 <timer_thread+0x348>
    474a:	49 83 c5 01          	add    $0x1,%r13
    474e:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4751:	eb 94                	jmp    46e7 <timer_thread+0x247>
    4753:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4758:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
    475e:	48 83 ec 08          	sub    $0x8,%rsp
    4762:	89 f9                	mov    %edi,%ecx
    4764:	bf 01 00 00 00       	mov    $0x1,%edi
    4769:	50                   	push   %rax
    476a:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    4770:	89 ea                	mov    %ebp,%edx
    4772:	50                   	push   %rax
    4773:	31 c0                	xor    %eax,%eax
    4775:	56                   	push   %rsi
    4776:	4c 89 fe             	mov    %r15,%rsi
    4779:	e8 22 dd ff ff       	call   24a0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    477e:	44 8b 53 30          	mov    0x30(%rbx),%r10d
      for (int y = 0 ; y < 2 ; y++) {
    4782:	48 83 c4 20          	add    $0x20,%rsp
    4786:	49 83 fd 01          	cmp    $0x1,%r13
    478a:	74 44                	je     47d0 <timer_thread+0x330>
    478c:	49 83 c5 01          	add    $0x1,%r13
    4790:	45 31 db             	xor    %r11d,%r11d
    4793:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4796:	45 85 d2             	test   %r10d,%r10d
    4799:	0f 8f 43 ff ff ff    	jg     46e2 <timer_thread+0x242>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    479f:	49 83 c6 01          	add    $0x1,%r14
    47a3:	45 39 f2             	cmp    %r14d,%r10d
    47a6:	0f 8f 1c ff ff ff    	jg     46c8 <timer_thread+0x228>
    47ac:	8b 6c 24 0c          	mov    0xc(%rsp),%ebp
    if (all_empty == 1) {
    47b0:	41 83 fb 01          	cmp    $0x1,%r11d
    47b4:	74 46                	je     47fc <timer_thread+0x35c>
      nanosleep(&drain , &drainrem);
    47b6:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    47bb:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    47c0:	e8 cb db ff ff       	call   2390 <nanosleep@plt>
    47c5:	e9 72 fe ff ff       	jmp    463c <timer_thread+0x19c>
    47ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    47d0:	49 83 c6 01          	add    $0x1,%r14
    47d4:	45 31 db             	xor    %r11d,%r11d
    47d7:	45 39 f2             	cmp    %r14d,%r10d
    47da:	0f 8f e8 fe ff ff    	jg     46c8 <timer_thread+0x228>
    47e0:	eb ca                	jmp    47ac <timer_thread+0x30c>
    47e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    47e8:	49 83 c6 01          	add    $0x1,%r14
    47ec:	44 8b 5c 24 08       	mov    0x8(%rsp),%r11d
    47f1:	45 39 f2             	cmp    %r14d,%r10d
    47f4:	0f 8f ce fe ff ff    	jg     46c8 <timer_thread+0x228>
    47fa:	eb b0                	jmp    47ac <timer_thread+0x30c>
    47fc:	48 8d 3d 51 38 00 00 	lea    0x3851(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4803:	e8 18 db ff ff       	call   2320 <puts@plt>
  while (data->running) {
    4808:	8b 53 44             	mov    0x44(%rbx),%edx
    480b:	85 d2                	test   %edx,%edx
    480d:	0f 84 eb 00 00 00    	je     48fe <timer_thread+0x45e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4813:	8b 43 2c             	mov    0x2c(%rbx),%eax
    4816:	31 ed                	xor    %ebp,%ebp
    4818:	4c 8d 25 5b 38 00 00 	lea    0x385b(%rip),%r12        # 807a <_IO_stdin_used+0x7a>
    481f:	4c 8d 2d 6f 38 00 00 	lea    0x386f(%rip),%r13        # 8095 <_IO_stdin_used+0x95>
    4826:	85 c0                	test   %eax,%eax
    4828:	7e 39                	jle    4863 <timer_thread+0x3c3>
    482a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4830:	31 c0                	xor    %eax,%eax
    4832:	89 ea                	mov    %ebp,%edx
    4834:	4c 89 e6             	mov    %r12,%rsi
    4837:	bf 01 00 00 00       	mov    $0x1,%edi
    483c:	e8 5f dc ff ff       	call   24a0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4841:	48 8b 43 18          	mov    0x18(%rbx),%rax
    4845:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
      if (data->threads[x]->type == IO) {
    4849:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    484d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4854:	0f 84 d1 00 00 00    	je     492b <timer_thread+0x48b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    485a:	48 83 c5 01          	add    $0x1,%rbp
    485e:	39 6b 2c             	cmp    %ebp,0x2c(%rbx)
    4861:	7f cd                	jg     4830 <timer_thread+0x390>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4863:	48 63 53 30          	movslq 0x30(%rbx),%rdx
    4867:	85 d2                	test   %edx,%edx
    4869:	7e 7d                	jle    48e8 <timer_thread+0x448>
      for (int y = 0 ; y < data->task_count ; y++) {
    486b:	8b 43 40             	mov    0x40(%rbx),%eax
    486e:	85 c0                	test   %eax,%eax
    4870:	7e 76                	jle    48e8 <timer_thread+0x448>
    4872:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4875:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    4879:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4881:	31 c9                	xor    %ecx,%ecx
    4883:	48 c1 e6 09          	shl    $0x9,%rsi
    4887:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4890:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4894:	48 8b 40 38          	mov    0x38(%rax),%rax
    4898:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    489c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    48a2:	74 1c                	je     48c0 <timer_thread+0x420>
    48a4:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    48ae:	48 05 00 02 00 00    	add    $0x200,%rax
    48b4:	48 39 d0             	cmp    %rdx,%rax
    48b7:	74 26                	je     48df <timer_thread+0x43f>
    48b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    48c0:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    48ca:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    48d0:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    48da:	48 39 d0             	cmp    %rdx,%rax
    48dd:	75 e1                	jne    48c0 <timer_thread+0x420>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48df:	48 83 c1 08          	add    $0x8,%rcx
    48e3:	48 39 f9             	cmp    %rdi,%rcx
    48e6:	75 a8                	jne    4890 <timer_thread+0x3f0>
    asm volatile ("mfence" ::: "memory");
    48e8:	0f ae f0             	mfence
    48eb:	48 8d 3d b5 37 00 00 	lea    0x37b5(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    48f2:	e8 29 da ff ff       	call   2320 <puts@plt>
    data->running = 0;
    48f7:	c7 43 44 00 00 00 00 	movl   $0x0,0x44(%rbx)
    48fe:	48 8d 3d a9 37 00 00 	lea    0x37a9(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4905:	e8 16 da ff ff       	call   2320 <puts@plt>
}
    490a:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    490f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4918:	75 40                	jne    495a <timer_thread+0x4ba>
    491a:	48 83 c4 68          	add    $0x68,%rsp
    491e:	31 c0                	xor    %eax,%eax
    4920:	5b                   	pop    %rbx
    4921:	5d                   	pop    %rbp
    4922:	41 5c                	pop    %r12
    4924:	41 5d                	pop    %r13
    4926:	41 5e                	pop    %r14
    4928:	41 5f                	pop    %r15
    492a:	c3                   	ret
    492b:	4c 89 ef             	mov    %r13,%rdi
    492e:	e8 ed d9 ff ff       	call   2320 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4933:	48 8b 43 18          	mov    0x18(%rbx),%rax
    4937:	be 01 00 00 00       	mov    $0x1,%esi
    493c:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4940:	48 83 c5 01          	add    $0x1,%rbp
        eventfd_write(data->threads[x]->_eventfd, 1);
    4944:	8b 78 60             	mov    0x60(%rax),%edi
    4947:	e8 04 db ff ff       	call   2450 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    494c:	39 6b 2c             	cmp    %ebp,0x2c(%rbx)
    494f:	0f 8f db fe ff ff    	jg     4830 <timer_thread+0x390>
    4955:	e9 09 ff ff ff       	jmp    4863 <timer_thread+0x3c3>
}
    495a:	e8 11 da ff ff       	call   2370 <__stack_chk_fail@plt>
    495f:	90                   	nop

0000000000004960 <strtolower>:
void strtolower(char *str) {
    4960:	f3 0f 1e fa          	endbr64
    4964:	55                   	push   %rbp
    4965:	53                   	push   %rbx
    4966:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    496a:	48 0f be 1f          	movsbq (%rdi),%rbx
    496e:	84 db                	test   %bl,%bl
    4970:	74 24                	je     4996 <strtolower+0x36>
    4972:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4975:	e8 f6 db ff ff       	call   2570 <__ctype_tolower_loc@plt>
    497a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4980:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4983:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4987:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    498a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    498d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4992:	84 db                	test   %bl,%bl
    4994:	75 ea                	jne    4980 <strtolower+0x20>
}
    4996:	48 83 c4 08          	add    $0x8,%rsp
    499a:	5b                   	pop    %rbx
    499b:	5d                   	pop    %rbp
    499c:	c3                   	ret
    499d:	0f 1f 00             	nopl   (%rax)

00000000000049a0 <zh_malloc>:
void *zh_malloc(size_t size) {
    49a0:	f3 0f 1e fa          	endbr64
    49a4:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    49a8:	e8 b3 da ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    49ad:	48 85 c0             	test   %rax,%rax
    49b0:	74 05                	je     49b7 <zh_malloc+0x17>
}
    49b2:	48 83 c4 08          	add    $0x8,%rsp
    49b6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    49b7:	48 8b 0d 62 66 00 00 	mov    0x6662(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    49be:	ba 28 00 00 00       	mov    $0x28,%edx
    49c3:	be 01 00 00 00       	mov    $0x1,%esi
    49c8:	48 8d 3d e1 3b 00 00 	lea    0x3be1(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    49cf:	e8 4c db ff ff       	call   2520 <fwrite@plt>
        exit(1);
    49d4:	bf 01 00 00 00       	mov    $0x1,%edi
    49d9:	e8 22 db ff ff       	call   2500 <exit@plt>
    49de:	66 90                	xchg   %ax,%ax

00000000000049e0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    49e0:	f3 0f 1e fa          	endbr64
    49e4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    49e5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    49ea:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    49ed:	e8 ae d9 ff ff       	call   23a0 <strrchr@plt>
    if (!dot || dot == filename)
    49f2:	48 85 c0             	test   %rax,%rax
    49f5:	74 11                	je     4a08 <get_filename_ext+0x28>
    49f7:	48 39 c3             	cmp    %rax,%rbx
    49fa:	74 0c                	je     4a08 <get_filename_ext+0x28>
    return dot + 1;
    49fc:	48 83 c0 01          	add    $0x1,%rax
}
    4a00:	5b                   	pop    %rbx
    4a01:	c3                   	ret
    4a02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4a08:	48 8d 05 e7 36 00 00 	lea    0x36e7(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
}
    4a0f:	5b                   	pop    %rbx
    4a10:	c3                   	ret
    4a11:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4a1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a20 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4a20:	f3 0f 1e fa          	endbr64
    4a24:	41 55                	push   %r13
    4a26:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a29:	48 89 fe             	mov    %rdi,%rsi
    4a2c:	41 54                	push   %r12
    4a2e:	55                   	push   %rbp
    4a2f:	48 89 d5             	mov    %rdx,%rbp
    4a32:	ba 00 04 00 00       	mov    $0x400,%edx
    4a37:	53                   	push   %rbx
    4a38:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4a3f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a48:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4a50:	31 c0                	xor    %eax,%eax
    4a52:	49 89 e4             	mov    %rsp,%r12
    4a55:	4c 89 e7             	mov    %r12,%rdi
    4a58:	e8 23 da ff ff       	call   2480 <__strcpy_chk@plt>
    for (; *str; ++str)
    4a5d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4a62:	84 db                	test   %bl,%bl
    4a64:	74 24                	je     4a8a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4a66:	e8 05 db ff ff       	call   2570 <__ctype_tolower_loc@plt>
    4a6b:	48 8b 08             	mov    (%rax),%rcx
    4a6e:	4c 89 e0             	mov    %r12,%rax
    4a71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4a78:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4a7b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4a7f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4a82:	48 0f be 18          	movsbq (%rax),%rbx
    4a86:	84 db                	test   %bl,%bl
    4a88:	75 ee                	jne    4a78 <send_headers+0x58>
    void *buf = malloc(size);
    4a8a:	bf 11 00 00 00       	mov    $0x11,%edi
    4a8f:	e8 cc d9 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4a94:	48 85 c0             	test   %rax,%rax
    4a97:	0f 84 7e 04 00 00    	je     4f1b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4a9d:	66 0f 6f 05 0b 41 00 00 	movdqa 0x410b(%rip),%xmm0        # 8bb0 <_IO_stdin_used+0xbb0>
    iov[0].iov_base = zh_malloc(slen);
    4aa5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4aa9:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4aae:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4ab6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4aba:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4abd:	e8 9e d9 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4ac2:	48 85 c0             	test   %rax,%rax
    4ac5:	0f 84 50 04 00 00    	je     4f1b <send_headers+0x4fb>
    4acb:	66 0f 6f 05 ed 40 00 00 	movdqa 0x40ed(%rip),%xmm0        # 8bc0 <_IO_stdin_used+0xbc0>
    iov[1].iov_base = zh_malloc(slen);
    4ad3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4ad7:	4c 89 e7             	mov    %r12,%rdi
    4ada:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4ae4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4aec:	0f 11 00             	movups %xmm0,(%rax)
    4aef:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4af3:	be 2e 00 00 00       	mov    $0x2e,%esi
    4af8:	e8 a3 d8 ff ff       	call   23a0 <strrchr@plt>
    if (!dot || dot == filename)
    4afd:	48 85 c0             	test   %rax,%rax
    4b00:	0f 84 ea 02 00 00    	je     4df0 <send_headers+0x3d0>
    4b06:	4c 39 e0             	cmp    %r12,%rax
    4b09:	0f 84 e1 02 00 00    	je     4df0 <send_headers+0x3d0>
    return dot + 1;
    4b0f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4b13:	48 8d 3d aa 35 00 00 	lea    0x35aa(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4b1a:	48 89 de             	mov    %rbx,%rsi
    4b1d:	e8 de d8 ff ff       	call   2400 <strcmp@plt>
    4b22:	85 c0                	test   %eax,%eax
    4b24:	75 20                	jne    4b46 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4b26:	66 0f 6f 05 a2 40 00 00 	movdqa 0x40a2(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4b2e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b36:	66 0f 6f 05 a2 40 00 00 	movdqa 0x40a2(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4b3e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4b46:	48 89 de             	mov    %rbx,%rsi
    4b49:	48 8d 3d 78 35 00 00 	lea    0x3578(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4b50:	e8 ab d8 ff ff       	call   2400 <strcmp@plt>
    4b55:	85 c0                	test   %eax,%eax
    4b57:	75 20                	jne    4b79 <send_headers+0x159>
    4b59:	66 0f 6f 05 6f 40 00 00 	movdqa 0x406f(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4b61:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b69:	66 0f 6f 05 6f 40 00 00 	movdqa 0x406f(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4b71:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4b79:	48 89 de             	mov    %rbx,%rsi
    4b7c:	48 8d 3d 4a 35 00 00 	lea    0x354a(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4b83:	e8 78 d8 ff ff       	call   2400 <strcmp@plt>
    4b88:	85 c0                	test   %eax,%eax
    4b8a:	0f 84 10 02 00 00    	je     4da0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4b90:	48 89 de             	mov    %rbx,%rsi
    4b93:	48 8d 3d 37 35 00 00 	lea    0x3537(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4b9a:	e8 61 d8 ff ff       	call   2400 <strcmp@plt>
    4b9f:	85 c0                	test   %eax,%eax
    4ba1:	0f 84 a9 02 00 00    	je     4e50 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4ba7:	48 89 de             	mov    %rbx,%rsi
    4baa:	48 8d 3d 24 35 00 00 	lea    0x3524(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4bb1:	e8 4a d8 ff ff       	call   2400 <strcmp@plt>
    4bb6:	85 c0                	test   %eax,%eax
    4bb8:	0f 84 6a 02 00 00    	je     4e28 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4bbe:	48 89 de             	mov    %rbx,%rsi
    4bc1:	48 8d 3d 50 35 00 00 	lea    0x3550(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4bc8:	e8 33 d8 ff ff       	call   2400 <strcmp@plt>
    4bcd:	85 c0                	test   %eax,%eax
    4bcf:	0f 84 2b 02 00 00    	je     4e00 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4bd5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4bd8:	0f 84 52 01 00 00    	je     4d30 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4bde:	48 89 de             	mov    %rbx,%rsi
    4be1:	48 8d 3d f1 34 00 00 	lea    0x34f1(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4be8:	e8 13 d8 ff ff       	call   2400 <strcmp@plt>
    4bed:	85 c0                	test   %eax,%eax
    4bef:	0f 84 ab 02 00 00    	je     4ea0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4bf5:	48 89 de             	mov    %rbx,%rsi
    4bf8:	48 8d 3d de 34 00 00 	lea    0x34de(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4bff:	e8 fc d7 ff ff       	call   2400 <strcmp@plt>
    4c04:	85 c0                	test   %eax,%eax
    4c06:	0f 84 6c 02 00 00    	je     4e78 <send_headers+0x458>
    slen = strlen(send_buffer);
    4c0c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4c14:	4c 89 e7             	mov    %r12,%rdi
    4c17:	e8 44 d7 ff ff       	call   2360 <strlen@plt>
    void *buf = malloc(size);
    4c1c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4c1f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4c22:	e8 39 d8 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4c27:	48 85 c0             	test   %rax,%rax
    4c2a:	0f 84 eb 02 00 00    	je     4f1b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4c30:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4c34:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4c38:	83 fb 08             	cmp    $0x8,%ebx
    4c3b:	0f 83 3f 01 00 00    	jae    4d80 <send_headers+0x360>
    4c41:	f6 c3 04             	test   $0x4,%bl
    4c44:	0f 85 7b 02 00 00    	jne    4ec5 <send_headers+0x4a5>
    4c4a:	85 db                	test   %ebx,%ebx
    4c4c:	74 13                	je     4c61 <send_headers+0x241>
    4c4e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4c56:	88 10                	mov    %dl,(%rax)
    4c58:	f6 c3 02             	test   $0x2,%bl
    4c5b:	0f 85 96 02 00 00    	jne    4ef7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4c61:	4d 89 e8             	mov    %r13,%r8
    4c64:	48 8d 0d 76 34 00 00 	lea    0x3476(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4c6b:	4c 89 e7             	mov    %r12,%rdi
    4c6e:	31 c0                	xor    %eax,%eax
    4c70:	ba 00 04 00 00       	mov    $0x400,%edx
    4c75:	be 01 00 00 00       	mov    $0x1,%esi
    4c7a:	e8 01 d9 ff ff       	call   2580 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4c7f:	4c 89 e7             	mov    %r12,%rdi
    4c82:	e8 d9 d6 ff ff       	call   2360 <strlen@plt>
    void *buf = malloc(size);
    4c87:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4c8a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4c8d:	e8 ce d7 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4c92:	48 85 c0             	test   %rax,%rax
    4c95:	0f 84 80 02 00 00    	je     4f1b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4c9b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4c9f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4ca3:	83 fb 08             	cmp    $0x8,%ebx
    4ca6:	0f 83 1c 01 00 00    	jae    4dc8 <send_headers+0x3a8>
    4cac:	f6 c3 04             	test   $0x4,%bl
    4caf:	0f 85 29 02 00 00    	jne    4ede <send_headers+0x4be>
    4cb5:	85 db                	test   %ebx,%ebx
    4cb7:	74 13                	je     4ccc <send_headers+0x2ac>
    4cb9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4cc1:	88 10                	mov    %dl,(%rax)
    4cc3:	f6 c3 02             	test   $0x2,%bl
    4cc6:	0f 85 3d 02 00 00    	jne    4f09 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ccc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4cd1:	bf 02 00 00 00       	mov    $0x2,%edi
    4cd6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4cde:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4ce6:	e8 75 d7 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4ceb:	48 85 c0             	test   %rax,%rax
    4cee:	0f 84 27 02 00 00    	je     4f1b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4cf4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4cfc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4d00:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4d08:	66 89 10             	mov    %dx,(%rax)
}
    4d0b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4d13:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d1c:	0f 85 20 02 00 00    	jne    4f42 <send_headers+0x522>
    4d22:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4d29:	5b                   	pop    %rbx
    4d2a:	5d                   	pop    %rbp
    4d2b:	41 5c                	pop    %r12
    4d2d:	41 5d                	pop    %r13
    4d2f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4d30:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4d34:	0f 85 a4 fe ff ff    	jne    4bde <send_headers+0x1be>
    4d3a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4d3e:	0f 85 9a fe ff ff    	jne    4bde <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d44:	66 0f 6f 05 e4 3e 00 00 	movdqa 0x3ee4(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    4d4c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4d56:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4d5e:	66 0f 6f 05 da 3e 00 00 	movdqa 0x3eda(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    4d66:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4d6e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4d76:	e9 63 fe ff ff       	jmp    4bde <send_headers+0x1be>
    4d7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4d80:	89 da                	mov    %ebx,%edx
    4d82:	48 89 c7             	mov    %rax,%rdi
    4d85:	4c 89 e6             	mov    %r12,%rsi
    4d88:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4d8d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4d92:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4d95:	c1 e9 03             	shr    $0x3,%ecx
    4d98:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4d9b:	e9 c1 fe ff ff       	jmp    4c61 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4da0:	66 0f 6f 05 28 3e 00 00 	movdqa 0x3e28(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4da8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4db0:	66 0f 6f 05 38 3e 00 00 	movdqa 0x3e38(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    4db8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4dc0:	e9 cb fd ff ff       	jmp    4b90 <send_headers+0x170>
    4dc5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4dc8:	89 da                	mov    %ebx,%edx
    4dca:	48 89 c7             	mov    %rax,%rdi
    4dcd:	4c 89 e6             	mov    %r12,%rsi
    4dd0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4dd5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4dda:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4ddd:	c1 e9 03             	shr    $0x3,%ecx
    4de0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4de3:	e9 e4 fe ff ff       	jmp    4ccc <send_headers+0x2ac>
    4de8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4df0:	48 8d 1d ff 32 00 00 	lea    0x32ff(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    4df7:	e9 94 fd ff ff       	jmp    4b90 <send_headers+0x170>
    4dfc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4e00:	66 0f 6f 05 08 3e 00 00 	movdqa 0x3e08(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4e08:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e10:	66 0f 6f 05 08 3e 00 00 	movdqa 0x3e08(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4e18:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e20:	e9 b0 fd ff ff       	jmp    4bd5 <send_headers+0x1b5>
    4e25:	0f 1f 00             	nopl   (%rax)
    4e28:	66 0f 6f 05 e0 3d 00 00 	movdqa 0x3de0(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4e30:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e38:	66 0f 6f 05 e0 3d 00 00 	movdqa 0x3de0(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4e40:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e48:	e9 71 fd ff ff       	jmp    4bbe <send_headers+0x19e>
    4e4d:	0f 1f 00             	nopl   (%rax)
    4e50:	66 0f 6f 05 78 3d 00 00 	movdqa 0x3d78(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4e58:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e60:	66 0f 6f 05 98 3d 00 00 	movdqa 0x3d98(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    4e68:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e70:	e9 32 fd ff ff       	jmp    4ba7 <send_headers+0x187>
    4e75:	0f 1f 00             	nopl   (%rax)
    4e78:	66 0f 6f 05 90 3d 00 00 	movdqa 0x3d90(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4e80:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e88:	66 0f 6f 05 d0 3d 00 00 	movdqa 0x3dd0(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    4e90:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4e98:	e9 6f fd ff ff       	jmp    4c0c <send_headers+0x1ec>
    4e9d:	0f 1f 00             	nopl   (%rax)
    4ea0:	66 0f 6f 05 68 3d 00 00 	movdqa 0x3d68(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4ea8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4eb0:	66 0f 6f 05 98 3d 00 00 	movdqa 0x3d98(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    4eb8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4ec0:	e9 30 fd ff ff       	jmp    4bf5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ec5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4ecc:	89 db                	mov    %ebx,%ebx
    4ece:	89 10                	mov    %edx,(%rax)
    4ed0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4ed5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4ed9:	e9 83 fd ff ff       	jmp    4c61 <send_headers+0x241>
    4ede:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4ee5:	89 db                	mov    %ebx,%ebx
    4ee7:	89 10                	mov    %edx,(%rax)
    4ee9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4eee:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4ef2:	e9 d5 fd ff ff       	jmp    4ccc <send_headers+0x2ac>
    4ef7:	89 db                	mov    %ebx,%ebx
    4ef9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4eff:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4f04:	e9 58 fd ff ff       	jmp    4c61 <send_headers+0x241>
    4f09:	89 db                	mov    %ebx,%ebx
    4f0b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4f11:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4f16:	e9 b1 fd ff ff       	jmp    4ccc <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4f1b:	48 8b 0d fe 60 00 00 	mov    0x60fe(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4f22:	ba 28 00 00 00       	mov    $0x28,%edx
    4f27:	be 01 00 00 00       	mov    $0x1,%esi
    4f2c:	48 8d 3d 7d 36 00 00 	lea    0x367d(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    4f33:	e8 e8 d5 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4f38:	bf 01 00 00 00       	mov    $0x1,%edi
    4f3d:	e8 be d5 ff ff       	call   2500 <exit@plt>
}
    4f42:	e8 29 d4 ff ff       	call   2370 <__stack_chk_fail@plt>
    4f47:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004f50 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4f50:	f3 0f 1e fa          	endbr64
    4f54:	41 55                	push   %r13
    4f56:	49 89 d5             	mov    %rdx,%r13
    4f59:	41 54                	push   %r12
    4f5b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    4f5e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4f61:	55                   	push   %rbp
    4f62:	53                   	push   %rbx
    4f63:	48 89 f3             	mov    %rsi,%rbx
    4f66:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4f6a:	e8 f1 d4 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4f6f:	48 85 c0             	test   %rax,%rax
    4f72:	74 6b                	je     4fdf <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4f74:	4c 89 e7             	mov    %r12,%rdi
    4f77:	48 89 c5             	mov    %rax,%rbp
    4f7a:	31 f6                	xor    %esi,%esi
    4f7c:	31 c0                	xor    %eax,%eax
    4f7e:	e8 4d d5 ff ff       	call   24d0 <open@plt>
    4f83:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4f86:	85 c0                	test   %eax,%eax
    4f88:	0f 88 28 d6 ff ff    	js     25b6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4f8e:	48 89 da             	mov    %rbx,%rdx
    4f91:	48 89 ee             	mov    %rbp,%rsi
    4f94:	89 c7                	mov    %eax,%edi
    4f96:	e8 45 d4 ff ff       	call   23e0 <read@plt>
    if (ret < file_size) {
    4f9b:	48 98                	cltq
    4f9d:	48 39 d8             	cmp    %rbx,%rax
    4fa0:	7c 1e                	jl     4fc0 <copy_file_contents+0x70>
    close(fd);
    4fa2:	44 89 e7             	mov    %r12d,%edi
    4fa5:	e8 16 d4 ff ff       	call   23c0 <close@plt>
    iov->iov_base = buf;
    4faa:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    4fae:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4fb2:	48 83 c4 08          	add    $0x8,%rsp
    4fb6:	5b                   	pop    %rbx
    4fb7:	5d                   	pop    %rbp
    4fb8:	41 5c                	pop    %r12
    4fba:	41 5d                	pop    %r13
    4fbc:	c3                   	ret
    4fbd:	0f 1f 00             	nopl   (%rax)
    4fc0:	48 8b 0d 59 60 00 00 	mov    0x6059(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4fc7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    4fcc:	be 01 00 00 00       	mov    $0x1,%esi
    4fd1:	48 8d 3d 1f 31 00 00 	lea    0x311f(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    4fd8:	e8 43 d5 ff ff       	call   2520 <fwrite@plt>
    4fdd:	eb c3                	jmp    4fa2 <copy_file_contents+0x52>
    4fdf:	48 8b 0d 3a 60 00 00 	mov    0x603a(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4fe6:	ba 28 00 00 00       	mov    $0x28,%edx
    4feb:	be 01 00 00 00       	mov    $0x1,%esi
    4ff0:	48 8d 3d b9 35 00 00 	lea    0x35b9(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    4ff7:	e8 24 d5 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4ffc:	bf 01 00 00 00       	mov    $0x1,%edi
    5001:	e8 fa d4 ff ff       	call   2500 <exit@plt>
    5006:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005010 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    5010:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    5014:	8b 46 44             	mov    0x44(%rsi),%eax
    5017:	48 89 fa             	mov    %rdi,%rdx
    501a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    501d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5023:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    5026:	48 8b 07             	mov    (%rdi),%rax
    5029:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    502c:	f6 c1 02             	test   $0x2,%cl
    502f:	74 00                	je     5031 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    5031:	89 f0                	mov    %esi,%eax
    5033:	44 29 c0             	sub    %r8d,%eax
    5036:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    5039:	0f 82 83 d5 ff ff    	jb     25c2 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    503f:	c1 e9 0a             	shr    $0xa,%ecx
    5042:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5046:	8b 47 44             	mov    0x44(%rdi),%eax
    5049:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    504c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    504f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    5052:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    5055:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5059:	d3 e0                	shl    %cl,%eax
    505b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    505e:	48 c1 e0 06          	shl    $0x6,%rax
    5062:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    5066:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    506c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    506f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    5073:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5079:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5081:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    5085:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    5088:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    508f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5097:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    509b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    509f:	e8 dc d2 ff ff       	call   2380 <io_uring_submit@plt>
}
    50a4:	31 c0                	xor    %eax,%eax
    50a6:	48 83 c4 08          	add    $0x8,%rsp
    50aa:	c3                   	ret
    50ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000050b0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    50b0:	f3 0f 1e fa          	endbr64
    50b4:	41 55                	push   %r13
    50b6:	41 89 fd             	mov    %edi,%r13d
    50b9:	41 54                	push   %r12
    50bb:	55                   	push   %rbp
    50bc:	53                   	push   %rbx
    50bd:	48 89 f3             	mov    %rsi,%rbx
    50c0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    50c4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    50c7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    50cd:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    50d0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    50d3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    50d5:	f6 c1 02             	test   $0x2,%cl
    50d8:	74 00                	je     50da <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    50da:	89 c2                	mov    %eax,%edx
    50dc:	29 f2                	sub    %esi,%edx
    50de:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    50e1:	0f 82 eb d4 ff ff    	jb     25d2 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50e7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    50ea:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    50ed:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    50f0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    50f5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50f8:	23 6b 58             	and    0x58(%rbx),%ebp
    50fb:	d3 e5                	shl    %cl,%ebp
    50fd:	48 c1 e5 06          	shl    $0x6,%rbp
    5101:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5105:	e8 56 d3 ff ff       	call   2460 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    510a:	be 01 00 00 00       	mov    $0x1,%esi
    510f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5114:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    5117:	e8 d4 d2 ff ff       	call   23f0 <calloc@plt>
    req->client_socket = client_socket;
    511c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    5121:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    5125:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    5128:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    512d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    5132:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    513b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    5143:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    5147:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    514b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    5152:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    515a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    515e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    5166:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    516e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    5172:	e8 09 d2 ff ff       	call   2380 <io_uring_submit@plt>
}
    5177:	48 83 c4 08          	add    $0x8,%rsp
    517b:	31 c0                	xor    %eax,%eax
    517d:	5b                   	pop    %rbx
    517e:	5d                   	pop    %rbp
    517f:	41 5c                	pop    %r12
    5181:	41 5d                	pop    %r13
    5183:	c3                   	ret
    5184:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    518f:	90                   	nop

0000000000005190 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5190:	f3 0f 1e fa          	endbr64
    5194:	41 56                	push   %r14
    5196:	41 89 f6             	mov    %esi,%r14d
    5199:	41 55                	push   %r13
    519b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    519e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    51a3:	41 54                	push   %r12
    51a5:	55                   	push   %rbp
    51a6:	48 89 d5             	mov    %rdx,%rbp
    51a9:	53                   	push   %rbx
    void *buf = malloc(size);
    51aa:	e8 b1 d2 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    51af:	48 85 c0             	test   %rax,%rax
    51b2:	0f 84 dd 00 00 00    	je     5295 <_send_static_string_content+0x105>
    51b8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    51bb:	4c 89 ef             	mov    %r13,%rdi
    51be:	e8 9d d1 ff ff       	call   2360 <strlen@plt>
    req->iovec_count = 1;
    51c3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    51ca:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    51ce:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    51d1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    51d4:	e8 87 d2 ff ff       	call   2460 <malloc@plt>
    51d9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    51dc:	48 85 c0             	test   %rax,%rax
    51df:	0f 84 b0 00 00 00    	je     5295 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    51e5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    51e9:	4c 89 e2             	mov    %r12,%rdx
    51ec:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    51ef:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    51f3:	e8 38 d2 ff ff       	call   2430 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    51f8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    51fb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5201:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5204:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5208:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    520a:	f6 c1 02             	test   $0x2,%cl
    520d:	0f 85 7d 00 00 00    	jne    5290 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    5213:	89 d0                	mov    %edx,%eax
    5215:	29 f0                	sub    %esi,%eax
    5217:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    521a:	0f 82 bc d3 ff ff    	jb     25dc <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5220:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5223:	8b 45 44             	mov    0x44(%rbp),%eax
    5226:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    5229:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    522c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    522f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    5232:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    5238:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    523c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    523e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    5241:	48 89 ef             	mov    %rbp,%rdi
    5244:	48 c1 e0 06          	shl    $0x6,%rax
    5248:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    524c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    524f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    5253:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5259:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5261:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    5265:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    5268:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    526f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5277:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    527b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    527f:	5b                   	pop    %rbx
    5280:	5d                   	pop    %rbp
    5281:	41 5c                	pop    %r12
    5283:	41 5d                	pop    %r13
    5285:	41 5e                	pop    %r14
    io_uring_submit(ring);
    5287:	e9 f4 d0 ff ff       	jmp    2380 <io_uring_submit@plt>
    528c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    5290:	e9 7e ff ff ff       	jmp    5213 <_send_static_string_content+0x83>
    5295:	48 8b 0d 84 5d 00 00 	mov    0x5d84(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    529c:	ba 28 00 00 00       	mov    $0x28,%edx
    52a1:	be 01 00 00 00       	mov    $0x1,%esi
    52a6:	48 8d 3d 03 33 00 00 	lea    0x3303(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    52ad:	e8 6e d2 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    52b2:	bf 01 00 00 00       	mov    $0x1,%edi
    52b7:	e8 44 d2 ff ff       	call   2500 <exit@plt>
    52bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000052c0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    52c0:	f3 0f 1e fa          	endbr64
    52c4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    52c7:	89 fe                	mov    %edi,%esi
    52c9:	48 8b 3d 48 5d 00 00 	mov    0x5d48(%rip),%rdi        # b018 <unimplemented_content>
    52d0:	e9 bb fe ff ff       	jmp    5190 <_send_static_string_content>
    52d5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000052e0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    52e0:	f3 0f 1e fa          	endbr64
    52e4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    52e7:	89 fe                	mov    %edi,%esi
    52e9:	48 8b 3d 20 5d 00 00 	mov    0x5d20(%rip),%rdi        # b010 <http_404_content>
    52f0:	e9 9b fe ff ff       	jmp    5190 <_send_static_string_content>
    52f5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005300 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    5300:	f3 0f 1e fa          	endbr64
    5304:	41 56                	push   %r14
    5306:	41 55                	push   %r13
    5308:	49 89 d5             	mov    %rdx,%r13
    530b:	41 54                	push   %r12
    530d:	41 89 f4             	mov    %esi,%r12d
    5310:	55                   	push   %rbp
    5311:	48 89 fd             	mov    %rdi,%rbp
    5314:	53                   	push   %rbx
    5315:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    531c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5325:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    532d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    532f:	e8 2c d0 ff ff       	call   2360 <strlen@plt>
    5334:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    5339:	48 89 c3             	mov    %rax,%rbx
    533c:	0f 84 b6 00 00 00    	je     53f8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5342:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5347:	48 89 ee             	mov    %rbp,%rsi
    534a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    534e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5353:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    535b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5363:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    536e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5376:	e8 95 d0 ff ff       	call   2410 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    537b:	48 89 e6             	mov    %rsp,%rsi
    537e:	4c 89 f7             	mov    %r14,%rdi
    5381:	e8 9a d0 ff ff       	call   2420 <stat@plt>
    5386:	83 f8 ff             	cmp    $0xffffffff,%eax
    5389:	0f 84 d3 00 00 00    	je     5462 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    538f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5393:	25 00 f0 00 00       	and    $0xf000,%eax
    5398:	3d 00 80 00 00       	cmp    $0x8000,%eax
    539d:	0f 84 f5 00 00 00    	je     5498 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    53a3:	48 8b 3d 66 5c 00 00 	mov    0x5c66(%rip),%rdi        # b010 <http_404_content>
    53aa:	4c 89 ea             	mov    %r13,%rdx
    53ad:	44 89 e6             	mov    %r12d,%esi
    53b0:	e8 db fd ff ff       	call   5190 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    53b5:	4c 89 f2             	mov    %r14,%rdx
    53b8:	bf 01 00 00 00       	mov    $0x1,%edi
    53bd:	31 c0                	xor    %eax,%eax
    53bf:	48 8d 35 81 2d 00 00 	lea    0x2d81(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    53c6:	e8 d5 d0 ff ff       	call   24a0 <__printf_chk@plt>
}
    53cb:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    53d3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    53dc:	0f 85 20 01 00 00    	jne    5502 <handle_get_method+0x202>
    53e2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    53e9:	5b                   	pop    %rbx
    53ea:	5d                   	pop    %rbp
    53eb:	41 5c                	pop    %r12
    53ed:	41 5d                	pop    %r13
    53ef:	41 5e                	pop    %r14
    53f1:	c3                   	ret
    53f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    53f8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    53fd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5405:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    540a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    540d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5415:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5418:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5420:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    542b:	e8 e0 cf ff ff       	call   2410 <__memcpy_chk@plt>
    5430:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5435:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    543a:	48 8d 35 d1 2c 00 00 	lea    0x2cd1(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    5441:	48 29 d9             	sub    %rbx,%rcx
    5444:	ba 0b 00 00 00       	mov    $0xb,%edx
    5449:	e8 c2 cf ff ff       	call   2410 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    544e:	48 89 e6             	mov    %rsp,%rsi
    5451:	4c 89 f7             	mov    %r14,%rdi
    5454:	e8 c7 cf ff ff       	call   2420 <stat@plt>
    5459:	83 f8 ff             	cmp    $0xffffffff,%eax
    545c:	0f 85 2d ff ff ff    	jne    538f <handle_get_method+0x8f>
    5462:	4c 89 f2             	mov    %r14,%rdx
    5465:	48 89 e9             	mov    %rbp,%rcx
    5468:	48 8d 35 ae 2c 00 00 	lea    0x2cae(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    546f:	31 c0                	xor    %eax,%eax
    5471:	bf 01 00 00 00       	mov    $0x1,%edi
    5476:	e8 25 d0 ff ff       	call   24a0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    547b:	48 8b 3d 8e 5b 00 00 	mov    0x5b8e(%rip),%rdi        # b010 <http_404_content>
    5482:	4c 89 ea             	mov    %r13,%rdx
    5485:	44 89 e6             	mov    %r12d,%esi
    5488:	e8 03 fd ff ff       	call   5190 <_send_static_string_content>
}
    548d:	e9 39 ff ff ff       	jmp    53cb <handle_get_method+0xcb>
    5492:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5498:	bf 70 00 00 00       	mov    $0x70,%edi
    549d:	e8 be cf ff ff       	call   2460 <malloc@plt>
    54a2:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    54a5:	48 85 c0             	test   %rax,%rax
    54a8:	74 5d                	je     5507 <handle_get_method+0x207>
            req->client_socket = client_socket;
    54aa:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    54ae:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    54b3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    54b7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    54ba:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    54c1:	e8 5a f5 ff ff       	call   4a20 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    54c6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    54cb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    54cf:	4c 89 f7             	mov    %r14,%rdi
    54d2:	e8 79 fa ff ff       	call   4f50 <copy_file_contents>
    54d7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    54dc:	4c 89 f2             	mov    %r14,%rdx
    54df:	31 c0                	xor    %eax,%eax
    54e1:	48 8d 35 4d 2c 00 00 	lea    0x2c4d(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    54e8:	bf 01 00 00 00       	mov    $0x1,%edi
    54ed:	e8 ae cf ff ff       	call   24a0 <__printf_chk@plt>
            add_write_request(req, ring);
    54f2:	4c 89 ee             	mov    %r13,%rsi
    54f5:	48 89 df             	mov    %rbx,%rdi
    54f8:	e8 13 fb ff ff       	call   5010 <add_write_request>
    54fd:	e9 c9 fe ff ff       	jmp    53cb <handle_get_method+0xcb>
}
    5502:	e8 69 ce ff ff       	call   2370 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5507:	48 8b 0d 12 5b 00 00 	mov    0x5b12(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    550e:	ba 28 00 00 00       	mov    $0x28,%edx
    5513:	be 01 00 00 00       	mov    $0x1,%esi
    5518:	48 8d 3d 91 30 00 00 	lea    0x3091(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    551f:	e8 fc cf ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5524:	bf 01 00 00 00       	mov    $0x1,%edi
    5529:	e8 d2 cf ff ff       	call   2500 <exit@plt>
    552e:	66 90                	xchg   %ax,%ax

0000000000005530 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5530:	f3 0f 1e fa          	endbr64
    5534:	41 57                	push   %r15
    5536:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5538:	4c 8d 35 6d 2b 00 00 	lea    0x2b6d(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    553f:	41 55                	push   %r13
    5541:	49 89 d5             	mov    %rdx,%r13
    5544:	41 54                	push   %r12
    5546:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    5549:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    554c:	55                   	push   %rbp
    554d:	53                   	push   %rbx
    554e:	48 83 ec 18          	sub    $0x18,%rsp
    5552:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    555b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5560:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5562:	49 89 e7             	mov    %rsp,%r15
    5565:	4c 89 fa             	mov    %r15,%rdx
    5568:	e8 63 ce ff ff       	call   23d0 <strtok_r@plt>
    for (; *str; ++str)
    556d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    5571:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    5574:	84 db                	test   %bl,%bl
    5576:	74 1d                	je     5595 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    5578:	e8 f3 cf ff ff       	call   2570 <__ctype_tolower_loc@plt>
    557d:	48 89 ea             	mov    %rbp,%rdx
    5580:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    5583:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    5587:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    558a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    558d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5591:	84 db                	test   %bl,%bl
    5593:	75 eb                	jne    5580 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    5595:	4c 89 fa             	mov    %r15,%rdx
    5598:	4c 89 f6             	mov    %r14,%rsi
    559b:	31 ff                	xor    %edi,%edi
    559d:	e8 2e ce ff ff       	call   23d0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    55a2:	48 8d 35 b1 2b 00 00 	lea    0x2bb1(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    55a9:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    55ac:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    55af:	e8 4c ce ff ff       	call   2400 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    55b4:	4c 89 ea             	mov    %r13,%rdx
    55b7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    55ba:	85 c0                	test   %eax,%eax
    55bc:	75 2a                	jne    55e8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    55be:	48 89 df             	mov    %rbx,%rdi
    55c1:	e8 3a fd ff ff       	call   5300 <handle_get_method>
}
    55c6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    55cb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    55d4:	75 20                	jne    55f6 <handle_http_method+0xc6>
    55d6:	48 83 c4 18          	add    $0x18,%rsp
    55da:	5b                   	pop    %rbx
    55db:	5d                   	pop    %rbp
    55dc:	41 5c                	pop    %r12
    55de:	41 5d                	pop    %r13
    55e0:	41 5e                	pop    %r14
    55e2:	41 5f                	pop    %r15
    55e4:	c3                   	ret
    55e5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    55e8:	48 8b 3d 29 5a 00 00 	mov    0x5a29(%rip),%rdi        # b018 <unimplemented_content>
    55ef:	e8 9c fb ff ff       	call   5190 <_send_static_string_content>
}
    55f4:	eb d0                	jmp    55c6 <handle_http_method+0x96>
    55f6:	e8 75 cd ff ff       	call   2370 <__stack_chk_fail@plt>
    55fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005600 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5600:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5604:	85 d2                	test   %edx,%edx
    5606:	7e 38                	jle    5640 <get_line+0x40>
    5608:	48 63 d2             	movslq %edx,%rdx
    560b:	48 83 c7 01          	add    $0x1,%rdi
    560f:	48 01 f2             	add    %rsi,%rdx
    5612:	eb 11                	jmp    5625 <get_line+0x25>
    5614:	0f 1f 40 00          	nopl   0x0(%rax)
    5618:	48 83 c6 01          	add    $0x1,%rsi
    561c:	48 83 c7 01          	add    $0x1,%rdi
    5620:	48 39 d6             	cmp    %rdx,%rsi
    5623:	74 1b                	je     5640 <get_line+0x40>
        dest[i] = src[i];
    5625:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5629:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    562b:	3c 0d                	cmp    $0xd,%al
    562d:	75 e9                	jne    5618 <get_line+0x18>
    562f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5632:	75 e4                	jne    5618 <get_line+0x18>
            dest[i] = '\0';
    5634:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5637:	31 c0                	xor    %eax,%eax
    5639:	c3                   	ret
    563a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5640:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5645:	c3                   	ret
    5646:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005650 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    5650:	f3 0f 1e fa          	endbr64
    5654:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    565b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    565f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5668:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5670:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5672:	49 89 e2             	mov    %rsp,%r10
    5675:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    567d:	4c 89 d0             	mov    %r10,%rax
    5680:	eb 13                	jmp    5695 <handle_client_request+0x45>
    5682:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5688:	48 83 c0 01          	add    $0x1,%rax
    568c:	48 83 c1 01          	add    $0x1,%rcx
    5690:	4c 39 c8             	cmp    %r9,%rax
    5693:	74 4b                	je     56e0 <handle_client_request+0x90>
        dest[i] = src[i];
    5695:	44 0f b6 01          	movzbl (%rcx),%r8d
    5699:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    569c:	41 80 f8 0d          	cmp    $0xd,%r8b
    56a0:	75 e6                	jne    5688 <handle_client_request+0x38>
    56a2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    56a6:	75 e0                	jne    5688 <handle_client_request+0x38>
            dest[i] = '\0';
    56a8:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    56ab:	8b 47 08             	mov    0x8(%rdi),%eax
    56ae:	48 89 f2             	mov    %rsi,%rdx
    56b1:	4c 89 d7             	mov    %r10,%rdi
    56b4:	89 c6                	mov    %eax,%esi
    56b6:	e8 75 fe ff ff       	call   5530 <handle_http_method>
}
    56bb:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    56c3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    56cc:	75 39                	jne    5707 <handle_client_request+0xb7>
    56ce:	31 c0                	xor    %eax,%eax
    56d0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    56d7:	c3                   	ret
    56d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    56e0:	48 8b 0d 39 59 00 00 	mov    0x5939(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    56e7:	ba 12 00 00 00       	mov    $0x12,%edx
    56ec:	be 01 00 00 00       	mov    $0x1,%esi
    56f1:	48 8d 3d 66 2a 00 00 	lea    0x2a66(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    56f8:	e8 23 ce ff ff       	call   2520 <fwrite@plt>
        exit(1);
    56fd:	bf 01 00 00 00       	mov    $0x1,%edi
    5702:	e8 f9 cd ff ff       	call   2500 <exit@plt>
}
    5707:	e8 64 cc ff ff       	call   2370 <__stack_chk_fail@plt>
    570c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005710 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5710:	f3 0f 1e fa          	endbr64
    5714:	55                   	push   %rbp
    5715:	53                   	push   %rbx
    5716:	48 89 cb             	mov    %rcx,%rbx
    5719:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    571d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5720:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5723:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5729:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    572c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    572f:	f6 c1 02             	test   $0x2,%cl
    5732:	74 00                	je     5734 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    5734:	41 89 c0             	mov    %eax,%r8d
    5737:	45 29 c8             	sub    %r9d,%r8d
    573a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    573e:	0f 82 a8 ce ff ff    	jb     25ec <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5744:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5747:	8b 6b 44             	mov    0x44(%rbx),%ebp
    574a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    574d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5750:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5753:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5757:	d3 e5                	shl    %cl,%ebp
    5759:	48 c1 e5 06          	shl    $0x6,%rbp
    575d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5761:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5764:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5769:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5770:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5774:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5778:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    5780:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    5788:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    578c:	e8 cf cc ff ff       	call   2460 <malloc@plt>
  io_uring_submit(ring);
    5791:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5794:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    579a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    579e:	48 83 c4 08          	add    $0x8,%rsp
    57a2:	5b                   	pop    %rbx
    57a3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    57a4:	e9 d7 cb ff ff       	jmp    2380 <io_uring_submit@plt>
    57a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000057b0 <io_thread>:
void* io_thread(void *arg) {
    57b0:	f3 0f 1e fa          	endbr64
    57b4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    57b6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    57b8:	41 56                	push   %r14
    57ba:	41 55                	push   %r13
    57bc:	41 54                	push   %r12
    57be:	55                   	push   %rbp
    57bf:	48 89 fd             	mov    %rdi,%rbp
    57c2:	53                   	push   %rbx
    57c3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    57ca:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    57d3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    57db:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    57df:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    57e4:	bf 00 01 00 00       	mov    $0x100,%edi
    57e9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    57ec:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    57f0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    57f5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    57fa:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    57ff:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5804:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    580c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5811:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5819:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    581e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5826:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    582b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5833:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5838:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5840:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5845:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    584d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5855:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    585d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5865:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    586d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5875:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    587d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5885:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    588d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5895:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    589d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    58a4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    58ac:	e8 8f cb ff ff       	call   2440 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    58b1:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    58b5:	31 f6                	xor    %esi,%esi
    58b7:	e8 84 cc ff ff       	call   2540 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    58bc:	31 d2                	xor    %edx,%edx
    58be:	be 01 00 00 00       	mov    $0x1,%esi
    58c3:	bf 02 00 00 00       	mov    $0x2,%edi
    58c8:	e8 c3 cc ff ff       	call   2590 <socket@plt>
  if (sock == -1)
    58cd:	83 f8 ff             	cmp    $0xffffffff,%eax
    58d0:	0f 84 58 cd ff ff    	je     262e <io_thread.cold+0x38>
  if (setsockopt(sock,
    58d6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    58db:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    58e1:	89 c7                	mov    %eax,%edi
    58e3:	41 89 c4             	mov    %eax,%r12d
    58e6:	ba 02 00 00 00       	mov    $0x2,%edx
    58eb:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    58f0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    58f8:	e8 33 ca ff ff       	call   2330 <setsockopt@plt>
    58fd:	85 c0                	test   %eax,%eax
    58ff:	0f 88 fd cc ff ff    	js     2602 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5905:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    590a:	ba 10 00 00 00       	mov    $0x10,%edx
    590f:	44 89 e7             	mov    %r12d,%edi
    5912:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    591b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5923:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    592b:	e8 80 cb ff ff       	call   24b0 <bind@plt>
    5930:	85 c0                	test   %eax,%eax
    5932:	0f 88 02 cd ff ff    	js     263a <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5938:	be 0a 00 00 00       	mov    $0xa,%esi
    593d:	44 89 e7             	mov    %r12d,%edi
    5940:	e8 2b cb ff ff       	call   2470 <listen@plt>
    5945:	85 c0                	test   %eax,%eax
    5947:	0f 88 c1 cc ff ff    	js     260e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    594d:	ba db 18 00 00       	mov    $0x18db,%edx
    5952:	48 8d 35 4a 28 00 00 	lea    0x284a(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5959:	bf 01 00 00 00       	mov    $0x1,%edi
    595e:	31 c0                	xor    %eax,%eax
    5960:	e8 3b cb ff ff       	call   24a0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5965:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    596a:	48 89 d9             	mov    %rbx,%rcx
    596d:	44 89 e7             	mov    %r12d,%edi
    5970:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5975:	48 89 c6             	mov    %rax,%rsi
    5978:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    597d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5982:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    598a:	e8 81 fd ff ff       	call   5710 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    598f:	bf 01 00 00 00       	mov    $0x1,%edi
    5994:	be 10 00 00 00       	mov    $0x10,%esi
    5999:	e8 52 ca ff ff       	call   23f0 <calloc@plt>
    void *buf = malloc(size);
    599e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    59a3:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    59a6:	e8 b5 ca ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    59ab:	48 85 c0             	test   %rax,%rax
    59ae:	0f 84 ae 04 00 00    	je     5e62 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    59b4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    59b8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    59bf:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    59c6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    59ce:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    59d1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    59d6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    59d8:	f6 c1 02             	test   $0x2,%cl
    59db:	0f 85 0f 04 00 00    	jne    5df0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    59e1:	89 d0                	mov    %edx,%eax
    59e3:	29 f0                	sub    %esi,%eax
    59e5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    59ec:	0f 82 32 cc ff ff    	jb     2624 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    59f2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    59f5:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    59f9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    59fd:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a00:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5a07:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a0a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5a11:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a18:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5a1a:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5a1d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5a22:	48 c1 e0 06          	shl    $0x6,%rax
    5a26:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5a2e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5a34:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5a37:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5a3f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5a43:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5a4b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5a53:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5a57:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5a5b:	e8 20 c9 ff ff       	call   2380 <io_uring_submit@plt>
  while (data->running == 1) {
    5a60:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5a64:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5a69:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5a71:	0f 85 d7 01 00 00    	jne    5c4e <io_thread+0x49e>
    5a77:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5a7c:	4d 89 ce             	mov    %r9,%r14
    5a7f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5a84:	0f 1f 40 00          	nopl   0x0(%rax)
    5a88:	48 8d 3d 2a 27 00 00 	lea    0x272a(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5a8f:	e8 8c c8 ff ff       	call   2320 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5a94:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5a9b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5aa2:	c1 e9 0b             	shr    $0xb,%ecx
    5aa5:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5aa8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5ab0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5ab2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5aba:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5abc:	39 d0                	cmp    %edx,%eax
    5abe:	74 36                	je     5af6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5ac0:	89 f8                	mov    %edi,%eax
    5ac2:	21 d0                	and    %edx,%eax
    5ac4:	d3 e0                	shl    %cl,%eax
    5ac6:	48 c1 e0 04          	shl    $0x4,%rax
    5aca:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5ad2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5ada:	0f 85 a8 01 00 00    	jne    5c88 <io_thread+0x4d8>
    5ae0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5ae4:	0f 85 0e 03 00 00    	jne    5df8 <io_thread+0x648>
			if (cqe->res < 0)
    5aea:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5aed:	83 c2 01             	add    $0x1,%edx
    5af0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5af2:	85 c0                	test   %eax,%eax
    5af4:	79 b2                	jns    5aa8 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5af6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    5aff:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5b00:	45 31 c0             	xor    %r8d,%r8d
    5b03:	31 d2                	xor    %edx,%edx
    5b05:	b9 01 00 00 00       	mov    $0x1,%ecx
    5b0a:	4c 89 f6             	mov    %r14,%rsi
    5b0d:	48 89 df             	mov    %rbx,%rdi
    5b10:	e8 7b c9 ff ff       	call   2490 <__io_uring_get_cqe@plt>
    5b15:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5b18:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5b1d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5b21:	0f 84 e1 02 00 00    	je     5e08 <io_thread+0x658>
    5b27:	48 8d 3d b1 26 00 00 	lea    0x26b1(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5b2e:	e8 ed c7 ff ff       	call   2320 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5b33:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5b38:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5b3b:	45 85 ff             	test   %r15d,%r15d
    5b3e:	0f 88 b2 ca ff ff    	js     25f6 <io_thread.cold>
      if (cqe->res < 0) {
    5b44:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5b47:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    5b4b:	85 c0                	test   %eax,%eax
    5b4d:	0f 88 d5 02 00 00    	js     5e28 <io_thread+0x678>
      switch (req->event_type) {
    5b53:	41 83 f8 01          	cmp    $0x1,%r8d
    5b57:	0f 84 7b 01 00 00    	je     5cd8 <io_thread+0x528>
    5b5d:	41 83 f8 02          	cmp    $0x2,%r8d
    5b61:	0f 84 a1 01 00 00    	je     5d08 <io_thread+0x558>
    5b67:	45 85 c0             	test   %r8d,%r8d
    5b6a:	0f 85 50 01 00 00    	jne    5cc0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5b70:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5b75:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5b7a:	48 89 d9             	mov    %rbx,%rcx
    5b7d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5b81:	e8 8a fb ff ff       	call   5710 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5b86:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5b8b:	48 89 de             	mov    %rbx,%rsi
    5b8e:	8b 78 08             	mov    0x8(%rax),%edi
    5b91:	e8 1a f5 ff ff       	call   50b0 <add_read_request>
              free(req);
    5b96:	4c 89 e7             	mov    %r12,%rdi
    5b99:	e8 52 c7 ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5b9e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5ba3:	48 85 c0             	test   %rax,%rax
    5ba6:	0f 85 14 01 00 00    	jne    5cc0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    5bac:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5bb3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5bba:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5bbd:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5bc2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5bc4:	f6 c1 02             	test   $0x2,%cl
    5bc7:	74 00                	je     5bc9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5bc9:	89 d0                	mov    %edx,%eax
    5bcb:	29 f0                	sub    %esi,%eax
    5bcd:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5bd4:	0f 82 40 ca ff ff    	jb     261a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5bda:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    5bdd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5be2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5be6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5be9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5bf0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5bf3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5bfa:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5c01:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5c03:	8b 55 60             	mov    0x60(%rbp),%edx
    5c06:	48 c1 e0 06          	shl    $0x6,%rax
    5c0a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5c12:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5c18:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5c1b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5c23:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5c27:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5c2f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5c37:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5c3b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5c3f:	e8 3c c7 ff ff       	call   2380 <io_uring_submit@plt>
  while (data->running == 1) {
    5c44:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5c48:	0f 84 3a fe ff ff    	je     5a88 <io_thread+0x2d8>
    5c4e:	48 8d 3d c3 25 00 00 	lea    0x25c3(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5c55:	e8 c6 c6 ff ff       	call   2320 <puts@plt>
}
    5c5a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5c62:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5c6b:	0f 85 18 02 00 00    	jne    5e89 <io_thread+0x6d9>
    5c71:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5c78:	31 c0                	xor    %eax,%eax
    5c7a:	5b                   	pop    %rbx
    5c7b:	5d                   	pop    %rbp
    5c7c:	41 5c                	pop    %r12
    5c7e:	41 5d                	pop    %r13
    5c80:	41 5e                	pop    %r14
    5c82:	41 5f                	pop    %r15
    5c84:	c3                   	ret
    5c85:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5c88:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5c8d:	48 85 c0             	test   %rax,%rax
    5c90:	0f 84 6a fe ff ff    	je     5b00 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5c96:	48 83 38 01          	cmpq   $0x1,(%rax)
    5c9a:	0f 84 68 01 00 00    	je     5e08 <io_thread+0x658>
    5ca0:	48 8d 3d 38 25 00 00 	lea    0x2538(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5ca7:	e8 74 c6 ff ff       	call   2320 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5cac:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5cb1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5cb4:	e9 8b fe ff ff       	jmp    5b44 <io_thread+0x394>
    5cb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5cc0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5cc8:	8b 02                	mov    (%rdx),%eax
    5cca:	83 c0 01             	add    $0x1,%eax
    5ccd:	89 02                	mov    %eax,(%rdx)
}
    5ccf:	e9 d8 fe ff ff       	jmp    5bac <io_thread+0x3fc>
    5cd4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5cd8:	85 c0                	test   %eax,%eax
    5cda:	75 74                	jne    5d50 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5cdc:	48 8b 0d 3d 53 00 00 	mov    0x533d(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5ce3:	ba 0f 00 00 00       	mov    $0xf,%edx
    5ce8:	be 01 00 00 00       	mov    $0x1,%esi
    5ced:	48 8d 3d 14 25 00 00 	lea    0x2514(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    5cf4:	e8 27 c8 ff ff       	call   2520 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5cf9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5cfe:	e9 a0 fe ff ff       	jmp    5ba3 <io_thread+0x3f3>
    5d03:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5d08:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5d0d:	45 31 ff             	xor    %r15d,%r15d
    5d10:	85 c0                	test   %eax,%eax
    5d12:	7e 20                	jle    5d34 <io_thread+0x584>
    5d14:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5d18:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5d1b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    5d1f:	48 c1 e0 04          	shl    $0x4,%rax
    5d23:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5d28:	e8 c3 c5 ff ff       	call   22f0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5d2d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5d32:	7f e4                	jg     5d18 <io_thread+0x568>
              close(req->client_socket);
    5d34:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5d39:	e8 82 c6 ff ff       	call   23c0 <close@plt>
              free(req);
    5d3e:	4c 89 e7             	mov    %r12,%rdi
    5d41:	e8 aa c5 ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5d46:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5d4b:	e9 53 fe ff ff       	jmp    5ba3 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5d50:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5d55:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5d5a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5d62:	eb 11                	jmp    5d75 <io_thread+0x5c5>
    5d64:	0f 1f 40 00          	nopl   0x0(%rax)
    5d68:	48 83 c0 01          	add    $0x1,%rax
    5d6c:	48 83 c2 01          	add    $0x1,%rdx
    5d70:	48 39 c6             	cmp    %rax,%rsi
    5d73:	74 4b                	je     5dc0 <io_thread+0x610>
        dest[i] = src[i];
    5d75:	0f b6 0a             	movzbl (%rdx),%ecx
    5d78:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5d7a:	80 f9 0d             	cmp    $0xd,%cl
    5d7d:	75 e9                	jne    5d68 <io_thread+0x5b8>
    5d7f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5d83:	75 e3                	jne    5d68 <io_thread+0x5b8>
            dest[i] = '\0';
    5d85:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5d88:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    5d8d:	48 89 da             	mov    %rbx,%rdx
    5d90:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5d95:	e8 96 f7 ff ff       	call   5530 <handle_http_method>
              free(req->iov[0].iov_base);
    5d9a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    5d9f:	e8 4c c5 ff ff       	call   22f0 <free@plt>
              free(req);
    5da4:	4c 89 e7             	mov    %r12,%rdi
    5da7:	e8 44 c5 ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5dac:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5db1:	e9 ed fd ff ff       	jmp    5ba3 <io_thread+0x3f3>
    5db6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5dc0:	48 8b 0d 59 52 00 00 	mov    0x5259(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5dc7:	ba 12 00 00 00       	mov    $0x12,%edx
    5dcc:	be 01 00 00 00       	mov    $0x1,%esi
    5dd1:	48 8d 3d 86 23 00 00 	lea    0x2386(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5dd8:	e8 43 c7 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5ddd:	bf 01 00 00 00       	mov    $0x1,%edi
    5de2:	e8 19 c7 ff ff       	call   2500 <exit@plt>
    5de7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5df0:	e9 ec fb ff ff       	jmp    59e1 <io_thread+0x231>
    5df5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5df8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    5dfd:	e9 94 fe ff ff       	jmp    5c96 <io_thread+0x4e6>
    5e02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5e08:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5e10:	48 8d 3d b4 23 00 00 	lea    0x23b4(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    5e17:	8b 02                	mov    (%rdx),%eax
    5e19:	83 c0 01             	add    $0x1,%eax
    5e1c:	89 02                	mov    %eax,(%rdx)
    5e1e:	e8 fd c4 ff ff       	call   2320 <puts@plt>
    5e23:	e9 26 fe ff ff       	jmp    5c4e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5e28:	f7 d8                	neg    %eax
    5e2a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5e2f:	89 c7                	mov    %eax,%edi
    5e31:	e8 2a c7 ff ff       	call   2560 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5e36:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5e3b:	be 01 00 00 00       	mov    $0x1,%esi
    5e40:	48 8b 3d d9 51 00 00 	mov    0x51d9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    5e47:	48 89 c1             	mov    %rax,%rcx
    5e4a:	48 8d 15 8f 27 00 00 	lea    0x278f(%rip),%rdx        # 85e0 <_IO_stdin_used+0x5e0>
    5e51:	31 c0                	xor    %eax,%eax
    5e53:	e8 d8 c6 ff ff       	call   2530 <__fprintf_chk@plt>
          exit(1);
    5e58:	bf 01 00 00 00       	mov    $0x1,%edi
    5e5d:	e8 9e c6 ff ff       	call   2500 <exit@plt>
    5e62:	48 8b 0d b7 51 00 00 	mov    0x51b7(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5e69:	ba 28 00 00 00       	mov    $0x28,%edx
    5e6e:	be 01 00 00 00       	mov    $0x1,%esi
    5e73:	48 8d 3d 36 27 00 00 	lea    0x2736(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    5e7a:	e8 a1 c6 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5e7f:	bf 01 00 00 00       	mov    $0x1,%edi
    5e84:	e8 77 c6 ff ff       	call   2500 <exit@plt>
}
    5e89:	e8 e2 c4 ff ff       	call   2370 <__stack_chk_fail@plt>
    5e8e:	66 90                	xchg   %ax,%ax

0000000000005e90 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5e90:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5e94:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5e9b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5ea1:	85 c9                	test   %ecx,%ecx
    5ea3:	0f 8e ea 00 00 00    	jle    5f93 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    5ea9:	41 56                	push   %r14
    5eab:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5ead:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    5eb0:	41 54                	push   %r12
    5eb2:	49 89 fc             	mov    %rdi,%r12
    5eb5:	55                   	push   %rbp
    5eb6:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5eb7:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5ebb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5ec0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    5ec4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    5ecc:	31 db                	xor    %ebx,%ebx
    5ece:	8b 10                	mov    (%rax),%edx
    5ed0:	85 d2                	test   %edx,%edx
    5ed2:	7e 26                	jle    5efa <barriered_work_ingest+0x6a>
    5ed4:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    5ed8:	48 89 dd             	mov    %rbx,%rbp
    5edb:	48 c1 e5 08          	shl    $0x8,%rbp
    5edf:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    5ee3:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    5eea:	74 24                	je     5f10 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5eec:	48 83 c3 01          	add    $0x1,%rbx
    5ef0:	39 da                	cmp    %ebx,%edx
    5ef2:	7f e4                	jg     5ed8 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5ef4:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5efa:	49 83 c5 01          	add    $0x1,%r13
    5efe:	44 39 e9             	cmp    %r13d,%ecx
    5f01:	7f bd                	jg     5ec0 <barriered_work_ingest+0x30>
}
    5f03:	5b                   	pop    %rbx
    5f04:	31 c0                	xor    %eax,%eax
    5f06:	5d                   	pop    %rbp
    5f07:	41 5c                	pop    %r12
    5f09:	41 5d                	pop    %r13
    5f0b:	41 5e                	pop    %r14
    5f0d:	c3                   	ret
    5f0e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    5f10:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5f19:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5f20:	bf 04 00 00 00       	mov    $0x4,%edi
    5f25:	48 c1 e6 05          	shl    $0x5,%rsi
    5f29:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5f30:	48 83 c6 10          	add    $0x10,%rsi
    5f34:	e8 07 c4 ff ff       	call   2340 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5f39:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5f41:	48 8b 40 50          	mov    0x50(%rax),%rax
    5f45:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5f49:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    5f4d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5f57:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    5f5d:	83 c0 01             	add    $0x1,%eax
    5f60:	99                   	cltd
    5f61:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5f67:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    5f6d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5f70:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5f78:	48 83 c3 01          	add    $0x1,%rbx
    5f7c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5f80:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5f84:	8b 10                	mov    (%rax),%edx
    5f86:	39 da                	cmp    %ebx,%edx
    5f88:	0f 8f 46 ff ff ff    	jg     5ed4 <barriered_work_ingest+0x44>
    5f8e:	e9 61 ff ff ff       	jmp    5ef4 <barriered_work_ingest+0x64>
}
    5f93:	31 c0                	xor    %eax,%eax
    5f95:	c3                   	ret
    5f96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005fa0 <barriered_thread>:
void* barriered_thread(void *arg) {
    5fa0:	f3 0f 1e fa          	endbr64
    5fa4:	41 56                	push   %r14
    5fa6:	41 55                	push   %r13
    5fa8:	41 54                	push   %r12
  int t = 0;
    5faa:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    5fad:	55                   	push   %rbp
  int waiting = 0;
    5fae:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    5fb0:	53                   	push   %rbx
    5fb1:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    5fb4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5fb8:	0f 85 74 02 00 00    	jne    6232 <barriered_thread+0x292>
    if (t >= data->task_count) {
    5fbe:	8b 43 40             	mov    0x40(%rbx),%eax
    5fc1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5fc8:	41 39 c4             	cmp    %eax,%r12d
    5fcb:	0f 8d 6f 01 00 00    	jge    6140 <barriered_thread+0x1a0>
    5fd1:	49 63 fc             	movslq %r12d,%rdi
    5fd4:	48 c1 e7 09          	shl    $0x9,%rdi
    5fd8:	49 89 fd             	mov    %rdi,%r13
    5fdb:	eb 32                	jmp    600f <barriered_thread+0x6f>
    5fdd:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5fe0:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5fe4:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5fe8:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5fec:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5ff0:	4c 01 ef             	add    %r13,%rdi
    5ff3:	e8 98 fe ff ff       	call   5e90 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    5ff8:	8b 43 40             	mov    0x40(%rbx),%eax
    5ffb:	41 83 c4 01          	add    $0x1,%r12d
    5fff:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    6006:	44 39 e0             	cmp    %r12d,%eax
    6009:	0f 8e 19 02 00 00    	jle    6228 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    600f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6013:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    6017:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    601e:	75 c0                	jne    5fe0 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6020:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    6024:	83 e8 01             	sub    $0x1,%eax
    6027:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    602c:	45 85 e4             	test   %r12d,%r12d
    602f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6032:	45 85 c0             	test   %r8d,%r8d
    6035:	0f 8e 2d 01 00 00    	jle    6168 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    603b:	48 63 c8             	movslq %eax,%rcx
    603e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6042:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    6045:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    604b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    6052:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    6056:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    6059:	45 31 f6             	xor    %r14d,%r14d
    605c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6060:	48 8b 10             	mov    (%rax),%rdx
    6063:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6067:	49 01 cb             	add    %rcx,%r11
    606a:	4c 89 da             	mov    %r11,%rdx
    606d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6074:	75 04                	jne    607a <barriered_thread+0xda>
            arrived++;
    6076:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    607a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    6080:	75 04                	jne    6086 <barriered_thread+0xe6>
            prearrive++;
    6082:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6086:	48 83 c0 08          	add    $0x8,%rax
    608a:	48 39 c6             	cmp    %rax,%rsi
    608d:	75 d1                	jne    6060 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    608f:	45 85 d2             	test   %r10d,%r10d
    6092:	0f 84 c0 00 00 00    	je     6158 <barriered_thread+0x1b8>
    6098:	45 39 d0             	cmp    %r10d,%r8d
    609b:	0f 84 b7 00 00 00    	je     6158 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    60a1:	45 85 f6             	test   %r14d,%r14d
    60a4:	74 0a                	je     60b0 <barriered_thread+0x110>
    60a6:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    60aa:	0f 85 ae 01 00 00    	jne    625e <barriered_thread+0x2be>
    60b0:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    60b4:	4c 01 ea             	add    %r13,%rdx
    60b7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    60be:	45 85 e4             	test   %r12d,%r12d
    60c1:	75 14                	jne    60d7 <barriered_thread+0x137>
    60c3:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    60ca:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    60d1:	0f 8c 69 01 00 00    	jl     6240 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    60d7:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    60db:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    60df:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    60e9:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    60ed:	48 8b 78 38          	mov    0x38(%rax),%rdi
    60f1:	4c 01 ef             	add    %r13,%rdi
    60f4:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    60fa:	48 8b 43 38          	mov    0x38(%rbx),%rax
    60fe:	4c 01 e8             	add    %r13,%rax
    6101:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6108:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    610b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6110:	83 e8 01             	sub    $0x1,%eax
    6113:	44 39 e0             	cmp    %r12d,%eax
    6116:	0f 84 a4 00 00 00    	je     61c0 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    611c:	0f ae f8             	sfence
          if (waiting == 0) {
    611f:	85 ed                	test   %ebp,%ebp
    6121:	0f 84 d1 00 00 00    	je     61f8 <barriered_thread+0x258>
        int arrived = 0; 
    6127:	bd 01 00 00 00       	mov    $0x1,%ebp
    612c:	e9 c7 fe ff ff       	jmp    5ff8 <barriered_thread+0x58>
  while (data->running == 1) {
    6131:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6135:	0f 85 f7 00 00 00    	jne    6232 <barriered_thread+0x292>
    613b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    6140:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    6148:	85 c0                	test   %eax,%eax
    614a:	7e e5                	jle    6131 <barriered_thread+0x191>
    614c:	45 31 e4             	xor    %r12d,%r12d
    614f:	e9 7d fe ff ff       	jmp    5fd1 <barriered_thread+0x31>
    6154:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6158:	83 fd 01             	cmp    $0x1,%ebp
    615b:	74 1b                	je     6178 <barriered_thread+0x1d8>
        int arrived = 0; 
    615d:	31 ed                	xor    %ebp,%ebp
    615f:	e9 3d ff ff ff       	jmp    60a1 <barriered_thread+0x101>
    6164:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6168:	83 fd 01             	cmp    $0x1,%ebp
    616b:	0f 85 43 ff ff ff    	jne    60b4 <barriered_thread+0x114>
        int arrived = 0; 
    6171:	45 31 f6             	xor    %r14d,%r14d
    6174:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    6178:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    617f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    6184:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    6186:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    618a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6191:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    6196:	e8 a5 c1 ff ff       	call   2340 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    619b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    61a2:	48 83 c0 01          	add    $0x1,%rax
    61a6:	48 99                	cqto
    61a8:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    61af:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    61b6:	e9 e6 fe ff ff       	jmp    60a1 <barriered_thread+0x101>
    61bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    61c0:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    61c7:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    61ce:	0f 8d 48 ff ff ff    	jge    611c <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    61d4:	48 c1 e6 04          	shl    $0x4,%rsi
    61d8:	bf 04 00 00 00       	mov    $0x4,%edi
    61dd:	48 03 73 70          	add    0x70(%rbx),%rsi
    61e1:	e8 5a c1 ff ff       	call   2340 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    61e6:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    61ee:	e9 29 ff ff ff       	jmp    611c <barriered_thread+0x17c>
    61f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    61f8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    61ff:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    6204:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6208:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    620f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    6213:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    6217:	e8 24 c1 ff ff       	call   2340 <clock_gettime@plt>
            waiting = 1;
    621c:	e9 06 ff ff ff       	jmp    6127 <barriered_thread+0x187>
    6221:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    6228:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    622c:	0f 84 96 fd ff ff    	je     5fc8 <barriered_thread+0x28>
}
    6232:	5b                   	pop    %rbx
    6233:	31 c0                	xor    %eax,%eax
    6235:	5d                   	pop    %rbp
    6236:	41 5c                	pop    %r12
    6238:	41 5d                	pop    %r13
    623a:	41 5e                	pop    %r14
    623c:	c3                   	ret
    623d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    6240:	48 c1 e6 04          	shl    $0x4,%rsi
    6244:	bf 04 00 00 00       	mov    $0x4,%edi
    6249:	48 03 73 68          	add    0x68(%rbx),%rsi
    624d:	e8 ee c0 ff ff       	call   2340 <clock_gettime@plt>
          data->tasks[t].available = 0;
    6252:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6256:	4c 01 ea             	add    %r13,%rdx
    6259:	e9 79 fe ff ff       	jmp    60d7 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    625e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6262:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6266:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    626a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    626e:	4c 01 ef             	add    %r13,%rdi
    6271:	e8 1a fc ff ff       	call   5e90 <barriered_work_ingest>
          break;
    6276:	e9 39 fd ff ff       	jmp    5fb4 <barriered_thread+0x14>
    627b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006280 <receive>:
int receive(struct BarrierTask *data) {
    6280:	f3 0f 1e fa          	endbr64
    6284:	41 57                	push   %r15
    6286:	41 56                	push   %r14
    6288:	41 55                	push   %r13
    628a:	41 54                	push   %r12
    628c:	55                   	push   %rbp
    628d:	53                   	push   %rbx
    628e:	48 83 ec 08          	sub    $0x8,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6292:	44 8b b7 40 01 00 00 	mov    0x140(%rdi),%r14d
    6299:	45 85 f6             	test   %r14d,%r14d
    629c:	0f 8e 25 01 00 00    	jle    63c7 <receive+0x147>
    if (n == data->thread->real_thread_index) { continue; }
    62a2:	4c 8b bf 28 01 00 00 	mov    0x128(%rdi),%r15
    62a9:	48 89 f9             	mov    %rdi,%rcx
    62ac:	31 ed                	xor    %ebp,%ebp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    62ae:	31 db                	xor    %ebx,%ebx
    if (n == data->thread->real_thread_index) { continue; }
    62b0:	4d 63 67 08          	movslq 0x8(%r15),%r12
    62b4:	4d 89 e5             	mov    %r12,%r13
    62b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    62c0:	41 39 dd             	cmp    %ebx,%r13d
    62c3:	0f 84 ee 00 00 00    	je     63b7 <receive+0x137>
    struct Data *me = data->mailboxes[n].lower;
    62c9:	48 8b 81 70 01 00 00 	mov    0x170(%rcx),%rax
    62d0:	48 8b 34 28          	mov    (%rax,%rbp,1),%rsi
    else if (me->available_reading == 0) {
    62d4:	8b 86 00 02 00 00    	mov    0x200(%rsi),%eax
    62da:	85 c0                	test   %eax,%eax
    62dc:	0f 84 d5 00 00 00    	je     63b7 <receive+0x137>
    for (int x = 0 ; x < me->messages_count ; x++) {
    62e2:	48 8b be 80 00 00 00 	mov    0x80(%rsi),%rdi
    62e9:	48 85 ff             	test   %rdi,%rdi
    62ec:	0f 8e a6 00 00 00    	jle    6398 <receive+0x118>
      data->sends++;
    62f2:	48 8b 91 78 01 00 00 	mov    0x178(%rcx),%rdx
    62f9:	4c 8b 06             	mov    (%rsi),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    62fc:	4c 63 59 04          	movslq 0x4(%rcx),%r11
    6300:	49 89 d1             	mov    %rdx,%r9
    6303:	48 8d 42 01          	lea    0x1(%rdx),%rax
    6307:	49 f7 d9             	neg    %r9
    630a:	48 01 c7             	add    %rax,%rdi
    630d:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    6311:	4c 8b 89 08 01 00 00 	mov    0x108(%rcx),%r9
      me->received++;
    6318:	4c 8b 86 10 03 00 00 	mov    0x310(%rsi),%r8
      data->n++;
    631f:	49 29 d1             	sub    %rdx,%r9
      me->received++;
    6322:	49 29 d0             	sub    %rdx,%r8
    6325:	eb 12                	jmp    6339 <receive+0xb9>
    6327:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    6330:	48 83 c0 01          	add    $0x1,%rax
    6334:	48 39 c7             	cmp    %rax,%rdi
    6337:	74 5f                	je     6398 <receive+0x118>
      data->n++;
    6339:	49 8d 14 01          	lea    (%r9,%rax,1),%rdx
      data->sends++;
    633d:	48 89 81 78 01 00 00 	mov    %rax,0x178(%rcx)
      data->n++;
    6344:	48 89 91 08 01 00 00 	mov    %rdx,0x108(%rcx)
      me->received++;
    634b:	49 8d 14 00          	lea    (%r8,%rax,1),%rdx
    634f:	48 89 96 10 03 00 00 	mov    %rdx,0x310(%rsi)
      if (me->messages[x]->group == data->group) {
    6356:	49 8b 54 c2 f8       	mov    -0x8(%r10,%rax,8),%rdx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    635b:	4c 39 5a 10          	cmp    %r11,0x10(%rdx)
    635f:	75 cf                	jne    6330 <receive+0xb0>
    6361:	4c 39 62 08          	cmp    %r12,0x8(%rdx)
    6365:	75 c9                	jne    6330 <receive+0xb0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    6367:	49 63 47 04          	movslq 0x4(%r15),%rax
    636b:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    636d:	bf 01 00 00 00       	mov    $0x1,%edi
    6372:	ba 01 00 00 00       	mov    $0x1,%edx
    6377:	48 8d 35 8a 22 00 00 	lea    0x228a(%rip),%rsi        # 8608 <_IO_stdin_used+0x608>
    637e:	4c 39 e0             	cmp    %r12,%rax
    6381:	0f 94 c1             	sete   %cl
    6384:	31 c0                	xor    %eax,%eax
    6386:	e8 15 c1 ff ff       	call   24a0 <__printf_chk@plt>
        exit(1);
    638b:	bf 01 00 00 00       	mov    $0x1,%edi
    6390:	e8 6b c1 ff ff       	call   2500 <exit@plt>
    6395:	0f 1f 00             	nopl   (%rax)
    me->messages_count = 0;
    6398:	48 c7 86 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rsi)
      me->available_reading = 0;
    63a3:	c7 86 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi)
      me->finished_reading = 1;
    63ad:	c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rsi)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    63b7:	83 c3 01             	add    $0x1,%ebx
    63ba:	48 83 c5 38          	add    $0x38,%rbp
    63be:	41 39 de             	cmp    %ebx,%r14d
    63c1:	0f 85 f9 fe ff ff    	jne    62c0 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    63c7:	0f ae f8             	sfence
}
    63ca:	48 83 c4 08          	add    $0x8,%rsp
    63ce:	31 c0                	xor    %eax,%eax
    63d0:	5b                   	pop    %rbx
    63d1:	5d                   	pop    %rbp
    63d2:	41 5c                	pop    %r12
    63d4:	41 5d                	pop    %r13
    63d6:	41 5e                	pop    %r14
    63d8:	41 5f                	pop    %r15
    63da:	c3                   	ret
    63db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000063e0 <sendm>:
int sendm(struct BarrierTask *data) {
    63e0:	f3 0f 1e fa          	endbr64
    63e4:	41 57                	push   %r15
    63e6:	41 56                	push   %r14
    63e8:	41 55                	push   %r13
    63ea:	41 54                	push   %r12
    63ec:	55                   	push   %rbp
    63ed:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    63ee:	44 8b a7 40 01 00 00 	mov    0x140(%rdi),%r12d
    63f5:	45 85 e4             	test   %r12d,%r12d
    63f8:	0f 8e 72 01 00 00    	jle    6570 <sendm+0x190>
        if (n == data->thread->real_thread_index) { continue; }
    63fe:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    6405:	48 89 f9             	mov    %rdi,%rcx
    6408:	31 f6                	xor    %esi,%esi
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    640a:	31 d2                	xor    %edx,%edx
        if (n == data->thread->real_thread_index) { continue; }
    640c:	44 8b 68 08          	mov    0x8(%rax),%r13d
    6410:	eb 53                	jmp    6465 <sendm+0x85>
    6412:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (data->sending == 1) {
    6418:	83 b9 80 01 00 00 01 	cmpl   $0x1,0x180(%rcx)
          data->mailboxes[n].higher = them;
    641f:	48 89 47 08          	mov    %rax,0x8(%rdi)
          data->mailboxes[n].pending = NULL;
    6423:	48 c7 47 10 00 00 00 00 	movq   $0x0,0x10(%rdi)
          them->available_sending = 1;
    642b:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
        if (data->sending == 1) {
    6435:	74 69                	je     64a0 <sendm+0xc0>
          them->available_sending = 0;
    6437:	c7 80 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rax)
          them->available_receiving = 1;
    6441:	c7 80 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rax)
          them->finished_reading = 0;
    644b:	c7 80 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rax)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6455:	83 c2 01             	add    $0x1,%edx
    6458:	48 83 c6 38          	add    $0x38,%rsi
    645c:	44 39 e2             	cmp    %r12d,%edx
    645f:	0f 84 0b 01 00 00    	je     6570 <sendm+0x190>
        if (n == data->thread->real_thread_index) { continue; }
    6465:	41 39 d5             	cmp    %edx,%r13d
    6468:	74 eb                	je     6455 <sendm+0x75>
        struct Data *them = data->mailboxes[n].higher;
    646a:	48 8b b9 70 01 00 00 	mov    0x170(%rcx),%rdi
    6471:	48 01 f7             	add    %rsi,%rdi
        if (data->mailboxes[n].pending != NULL) {
    6474:	48 8b 47 10          	mov    0x10(%rdi),%rax
        struct Data *them = data->mailboxes[n].higher;
    6478:	4c 8b 47 08          	mov    0x8(%rdi),%r8
        if (data->mailboxes[n].pending != NULL) {
    647c:	48 85 c0             	test   %rax,%rax
    647f:	75 97                	jne    6418 <sendm+0x38>
        else if (them->available_sending == 0) {
    6481:	41 8b 80 00 01 00 00 	mov    0x100(%r8),%eax
    6488:	85 c0                	test   %eax,%eax
    648a:	74 c9                	je     6455 <sendm+0x75>
        if (data->sending == 1) {
    648c:	83 b9 80 01 00 00 01 	cmpl   $0x1,0x180(%rcx)
    6493:	4c 89 c0             	mov    %r8,%rax
    6496:	75 9f                	jne    6437 <sendm+0x57>
    6498:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        for (; them->messages_count < min;) {
    64a0:	48 8b 98 80 00 00 00 	mov    0x80(%rax),%rbx
    64a7:	4c 63 98 88 00 00 00 	movslq 0x88(%rax),%r11
    64ae:	4c 39 db             	cmp    %r11,%rbx
    64b1:	7d 84                	jge    6437 <sendm+0x57>
    64b3:	48 8b b9 08 01 00 00 	mov    0x108(%rcx),%rdi
    64ba:	4d 89 da             	mov    %r11,%r10
          them->messages[them->messages_count++] = data->message; 
    64bd:	4c 8b 08             	mov    (%rax),%r9
    64c0:	49 29 da             	sub    %rbx,%r10
    64c3:	48 89 7c 24 f0       	mov    %rdi,-0x10(%rsp)
    64c8:	48 8b b8 08 03 00 00 	mov    0x308(%rax),%rdi
    64cf:	48 89 7c 24 e8       	mov    %rdi,-0x18(%rsp)
    64d4:	49 8d 7a ff          	lea    -0x1(%r10),%rdi
    64d8:	48 83 ff 02          	cmp    $0x2,%rdi
    64dc:	0f 86 9e 00 00 00    	jbe    6580 <sendm+0x1a0>
    64e2:	4e 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%r8
    64ea:	48 8d 3c dd 00 00 00 00 	lea    0x0(,%rbx,8),%rdi
    64f2:	4f 8d 34 01          	lea    (%r9,%r8,1),%r14
    64f6:	4c 8d b9 88 01 00 00 	lea    0x188(%rcx),%r15
    64fd:	49 8d 2c 39          	lea    (%r9,%rdi,1),%rbp
    6501:	4d 39 f7             	cmp    %r14,%r15
    6504:	0f 83 8e 00 00 00    	jae    6598 <sendm+0x1b8>
    650a:	4c 8d b1 90 01 00 00 	lea    0x190(%rcx),%r14
    6511:	4c 39 f5             	cmp    %r14,%rbp
    6514:	0f 83 7e 00 00 00    	jae    6598 <sendm+0x1b8>
    651a:	4c 01 cf             	add    %r9,%rdi
    651d:	4b 8d 1c 01          	lea    (%r9,%r8,1),%rbx
    6521:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6528:	4c 8b 81 88 01 00 00 	mov    0x188(%rcx),%r8
        for (; them->messages_count < min;) {
    652f:	48 83 c7 08          	add    $0x8,%rdi
          them->messages[them->messages_count++] = data->message; 
    6533:	4c 89 47 f8          	mov    %r8,-0x8(%rdi)
        for (; them->messages_count < min;) {
    6537:	48 39 fb             	cmp    %rdi,%rbx
    653a:	75 ec                	jne    6528 <sendm+0x148>
    653c:	0f 1f 40 00          	nopl   0x0(%rax)
    6540:	48 8b 7c 24 f0       	mov    -0x10(%rsp),%rdi
    6545:	48 8b 5c 24 e8       	mov    -0x18(%rsp),%rbx
    654a:	4c 01 d7             	add    %r10,%rdi
    654d:	4c 01 d3             	add    %r10,%rbx
    6550:	48 89 b9 08 01 00 00 	mov    %rdi,0x108(%rcx)
    6557:	48 89 98 08 03 00 00 	mov    %rbx,0x308(%rax)
    655e:	4c 89 98 80 00 00 00 	mov    %r11,0x80(%rax)
    6565:	4f 89 44 d9 f8       	mov    %r8,-0x8(%r9,%r11,8)
    656a:	e9 c8 fe ff ff       	jmp    6437 <sendm+0x57>
    656f:	90                   	nop
      asm volatile ("sfence" ::: "memory");
    6570:	0f ae f8             	sfence
}
    6573:	31 c0                	xor    %eax,%eax
    6575:	5b                   	pop    %rbx
    6576:	5d                   	pop    %rbp
    6577:	41 5c                	pop    %r12
    6579:	41 5d                	pop    %r13
    657b:	41 5e                	pop    %r14
    657d:	41 5f                	pop    %r15
    657f:	c3                   	ret
    6580:	48 8d 3c dd 00 00 00 00 	lea    0x0(,%rbx,8),%rdi
    6588:	4e 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%r8
    6590:	eb 88                	jmp    651a <sendm+0x13a>
    6592:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6598:	4d 89 d6             	mov    %r10,%r14
    659b:	4c 8b 81 88 01 00 00 	mov    0x188(%rcx),%r8
    65a2:	48 89 ef             	mov    %rbp,%rdi
    65a5:	49 d1 ee             	shr    %r14
    65a8:	49 c1 e6 04          	shl    $0x4,%r14
    65ac:	66 49 0f 6e c0       	movq   %r8,%xmm0
    65b1:	4e 8d 7c 35 00       	lea    0x0(%rbp,%r14,1),%r15
    65b6:	41 83 e6 10          	and    $0x10,%r14d
    65ba:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    65be:	74 10                	je     65d0 <sendm+0x1f0>
          them->messages[them->messages_count++] = data->message; 
    65c0:	48 83 c7 10          	add    $0x10,%rdi
    65c4:	0f 11 45 00          	movups %xmm0,0x0(%rbp)
        for (; them->messages_count < min;) {
    65c8:	4c 39 ff             	cmp    %r15,%rdi
    65cb:	74 13                	je     65e0 <sendm+0x200>
    65cd:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    65d0:	0f 11 07             	movups %xmm0,(%rdi)
    65d3:	48 83 c7 20          	add    $0x20,%rdi
    65d7:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    65db:	4c 39 ff             	cmp    %r15,%rdi
    65de:	75 f0                	jne    65d0 <sendm+0x1f0>
    65e0:	4c 89 d7             	mov    %r10,%rdi
    65e3:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    65e7:	48 01 df             	add    %rbx,%rdi
    65ea:	41 f6 c2 01          	test   $0x1,%r10b
    65ee:	0f 84 4c ff ff ff    	je     6540 <sendm+0x160>
          them->messages[them->messages_count++] = data->message; 
    65f4:	4c 8b 81 88 01 00 00 	mov    0x188(%rcx),%r8
    65fb:	4d 89 04 f9          	mov    %r8,(%r9,%rdi,8)
        for (; them->messages_count < min;) {
    65ff:	e9 3c ff ff ff       	jmp    6540 <sendm+0x160>
    6604:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    660f:	90                   	nop

0000000000006610 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    6610:	f3 0f 1e fa          	endbr64
    6614:	41 57                	push   %r15
    6616:	41 56                	push   %r14
    6618:	41 55                	push   %r13
    661a:	41 54                	push   %r12
    661c:	55                   	push   %rbp
    661d:	53                   	push   %rbx
    661e:	48 83 ec 48          	sub    $0x48,%rsp
  if (data->thread_index == data->task_index) {
    6622:	8b 5f 04             	mov    0x4(%rdi),%ebx
    6625:	39 9f 30 01 00 00    	cmp    %ebx,0x130(%rdi)
      receive(data);
    662b:	48 89 fb             	mov    %rdi,%rbx
int barriered_work(struct BarrierTask *data) {
    662e:	48 89 7c 24 10       	mov    %rdi,0x10(%rsp)
  if (data->thread_index == data->task_index) {
    6633:	74 45                	je     667a <barriered_work+0x6a>
    receive(data);
    6635:	e8 46 fc ff ff       	call   6280 <receive>
    while (data->scheduled == 1) {
    663a:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6641:	75 19                	jne    665c <barriered_work+0x4c>
    6643:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
      data->n++;
    6648:	48 83 80 08 01 00 00 01 	addq   $0x1,0x108(%rax)
      asm volatile ("sfence" ::: "memory");
    6650:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6653:	83 b8 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rax)
    665a:	74 ec                	je     6648 <barriered_work+0x38>
    sendm(data);
    665c:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    6661:	e8 7a fd ff ff       	call   63e0 <sendm>
  asm volatile ("sfence" ::: "memory");
    6666:	0f ae f8             	sfence
}
    6669:	48 83 c4 48          	add    $0x48,%rsp
    666d:	31 c0                	xor    %eax,%eax
    666f:	5b                   	pop    %rbx
    6670:	5d                   	pop    %rbp
    6671:	41 5c                	pop    %r12
    6673:	41 5d                	pop    %r13
    6675:	41 5e                	pop    %r14
    6677:	41 5f                	pop    %r15
    6679:	c3                   	ret
      receive(data);
    667a:	e8 01 fc ff ff       	call   6280 <receive>
        int t = data->task_index;
    667f:	48 63 43 04          	movslq 0x4(%rbx),%rax
    6683:	48 89 d9             	mov    %rbx,%rcx
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6686:	8b 9b 40 01 00 00    	mov    0x140(%rbx),%ebx
    668c:	85 db                	test   %ebx,%ebx
    668e:	0f 8e b3 02 00 00    	jle    6947 <barriered_work+0x337>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    6694:	48 c1 e0 09          	shl    $0x9,%rax
    6698:	45 31 e4             	xor    %r12d,%r12d
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    669b:	31 d2                	xor    %edx,%edx
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    669d:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    66a6:	49 89 c6             	mov    %rax,%r14
    66a9:	48 89 c8             	mov    %rcx,%rax
    66ac:	48 8b 89 28 01 00 00 	mov    0x128(%rcx),%rcx
int barriered_work(struct BarrierTask *data) {
    66b3:	31 ff                	xor    %edi,%edi
    66b5:	45 31 c0             	xor    %r8d,%r8d
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    66b8:	31 f6                	xor    %esi,%esi
    66ba:	41 89 d2             	mov    %edx,%r10d
    66bd:	48 89 c5             	mov    %rax,%rbp
    66c0:	eb 1c                	jmp    66de <barriered_work+0xce>
    66c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    66c8:	83 c6 01             	add    $0x1,%esi
    66cb:	49 81 c0 c8 00 00 00 	add    $0xc8,%r8
    66d2:	48 83 c7 38          	add    $0x38,%rdi
    66d6:	39 de                	cmp    %ebx,%esi
    66d8:	0f 84 c2 00 00 00    	je     67a0 <barriered_work+0x190>
              if (y == b) { continue; }
    66de:	41 39 f2             	cmp    %esi,%r10d
    66e1:	74 e5                	je     66c8 <barriered_work+0xb8>
              int next_task = abs((t + 1) % (data->thread_count));
    66e3:	44 8b bd 34 01 00 00 	mov    0x134(%rbp),%r15d
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    66ea:	39 71 08             	cmp    %esi,0x8(%rcx)
    66ed:	75 d9                	jne    66c8 <barriered_work+0xb8>
    66ef:	48 8b 41 20          	mov    0x20(%rcx),%rax
    66f3:	4e 8b 4c 00 38       	mov    0x38(%rax,%r8,1),%r9
    66f8:	4b 8b 94 31 70 01 00 00 	mov    0x170(%r9,%r14,1),%rdx
    6700:	42 83 7c 22 30 02    	cmpl   $0x2,0x30(%rdx,%r12,1)
    6706:	75 c0                	jne    66c8 <barriered_work+0xb8>
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    6708:	45 85 ff             	test   %r15d,%r15d
    670b:	7e bb                	jle    66c8 <barriered_work+0xb8>
                    if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->finished_reading == 0) {
    670d:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    6712:	4c 8b 5c 10 38       	mov    0x38(%rax,%rdx,1),%r11
    6717:	4b 8b 94 33 70 01 00 00 	mov    0x170(%r11,%r14,1),%rdx
    671f:	48 01 fa             	add    %rdi,%rdx
    6722:	48 8b 02             	mov    (%rdx),%rax
                    if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available_receiving == 0) {
    6725:	48 8b 52 08          	mov    0x8(%rdx),%rdx
                    if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->finished_reading == 0) {
    6729:	8b 80 00 03 00 00    	mov    0x300(%rax),%eax
    672f:	8b 92 80 01 00 00    	mov    0x180(%rdx),%edx
    6735:	83 f8 01             	cmp    $0x1,%eax
    6738:	19 c0                	sbb    %eax,%eax
    673a:	83 c0 01             	add    $0x1,%eax
    673d:	85 d2                	test   %edx,%edx
    673f:	74 08                	je     6749 <barriered_work+0x139>
                  if (all_finished == 1 && all_wrote == 1) {
    6741:	85 c0                	test   %eax,%eax
    6743:	0f 85 29 05 00 00    	jne    6c72 <barriered_work+0x662>
    6749:	49 63 d7             	movslq %r15d,%rdx
                  for (int nn = 0 ; nn < data->thread_count ; nn++) {
    674c:	b8 70 01 00 00       	mov    $0x170,%eax
    6751:	48 c1 e2 09          	shl    $0x9,%rdx
    6755:	48 81 c2 70 01 00 00 	add    $0x170,%rdx
    675c:	eb 11                	jmp    676f <barriered_work+0x15f>
    675e:	66 90                	xchg   %ax,%ax
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6760:	48 05 00 02 00 00    	add    $0x200,%rax
    6766:	48 39 c2             	cmp    %rax,%rdx
    6769:	0f 84 59 ff ff ff    	je     66c8 <barriered_work+0xb8>
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    676f:	4d 8b 2c 03          	mov    (%r11,%rax,1),%r13
    6773:	4d 8b 3c 01          	mov    (%r9,%rax,1),%r15
    6777:	4d 8b 6c 3d 00       	mov    0x0(%r13,%rdi,1),%r13
    677c:	4f 39 2c 27          	cmp    %r13,(%r15,%r12,1)
    6780:	75 de                	jne    6760 <barriered_work+0x150>
    6782:	bf 01 00 00 00       	mov    $0x1,%edi
    6787:	48 8d 35 9d 1a 00 00 	lea    0x1a9d(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    678e:	31 c0                	xor    %eax,%eax
    6790:	e8 0b bd ff ff       	call   24a0 <__printf_chk@plt>
                          exit(1);
    6795:	bf 01 00 00 00       	mov    $0x1,%edi
    679a:	e8 61 bd ff ff       	call   2500 <exit@plt>
    679f:	90                   	nop
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    67a0:	4c 63 81 c4 00 00 00 	movslq 0xc4(%rcx),%r8
          int k = data->group;
    67a7:	8b b5 94 01 00 00    	mov    0x194(%rbp),%esi
    67ad:	44 89 d2             	mov    %r10d,%edx
    67b0:	48 89 e8             	mov    %rbp,%rax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    67b3:	45 85 c0             	test   %r8d,%r8d
    67b6:	0f 8e 73 01 00 00    	jle    692f <barriered_work+0x31f>
            int y = (k * data->thread->threads_per_group) + d;
    67bc:	41 0f af f0          	imul   %r8d,%esi
              int next_task = abs((t + 1) % (data->thread_count));
    67c0:	8b bd 34 01 00 00    	mov    0x134(%rbp),%edi
            int y = (k * data->thread->threads_per_group) + d;
    67c6:	89 54 24 20          	mov    %edx,0x20(%rsp)
    67ca:	89 5c 24 24          	mov    %ebx,0x24(%rsp)
    67ce:	4c 89 64 24 28       	mov    %r12,0x28(%rsp)
    67d3:	48 63 f6             	movslq %esi,%rsi
    67d6:	48 89 4c 24 30       	mov    %rcx,0x30(%rsp)
    67db:	4c 8d 0c b6          	lea    (%rsi,%rsi,4),%r9
    67df:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    67e4:	4f 8d 14 89          	lea    (%r9,%r9,4),%r10
    67e8:	4c 8b 49 20          	mov    0x20(%rcx),%r9
    67ec:	4f 8d 0c d1          	lea    (%r9,%r10,8),%r9
    67f0:	4c 8d 14 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r10
    67f8:	49 29 f2             	sub    %rsi,%r10
    67fb:	4c 01 c6             	add    %r8,%rsi
    67fe:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    6803:	4d 89 c8             	mov    %r9,%r8
    6806:	48 8d 2c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rbp
    680e:	49 c1 e2 03          	shl    $0x3,%r10
    6812:	48 29 f5             	sub    %rsi,%rbp
    6815:	4d 89 d5             	mov    %r10,%r13
    6818:	48 c1 e5 03          	shl    $0x3,%rbp
    681c:	0f 1f 40 00          	nopl   0x0(%rax)
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6820:	4d 8b 60 38          	mov    0x38(%r8),%r12
    6824:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    6829:	4c 89 04 24          	mov    %r8,(%rsp)
    682d:	4c 89 d6             	mov    %r10,%rsi
    6830:	4f 8b bc 34 70 01 00 00 	mov    0x170(%r12,%r14,1),%r15
    6838:	eb 1a                	jmp    6854 <barriered_work+0x244>
    683a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6840:	48 83 c6 38          	add    $0x38,%rsi
    6844:	48 81 c3 c8 00 00 00 	add    $0xc8,%rbx
    684b:	48 39 f5             	cmp    %rsi,%rbp
    684e:	0f 84 ac 00 00 00    	je     6900 <barriered_work+0x2f0>
              if (kind == MAILBOX_FRIEND) {
    6854:	41 83 7c 37 30 01    	cmpl   $0x1,0x30(%r15,%rsi,1)
    685a:	75 e4                	jne    6840 <barriered_work+0x230>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    685c:	48 8b 43 38          	mov    0x38(%rbx),%rax
    6860:	4e 8b 9c 30 70 01 00 00 	mov    0x170(%rax,%r14,1),%r11
    6868:	4d 01 eb             	add    %r13,%r11
                   for (int nn = 0 ; nn < data->thread_count ; nn++) {
    686b:	85 ff                	test   %edi,%edi
    686d:	7e d1                	jle    6840 <barriered_work+0x230>
    return mailbox->lower;
    686f:	4d 8b 0b             	mov    (%r11),%r9
    return mailbox->higher;
    6872:	4d 8b 43 08          	mov    0x8(%r11),%r8
                   for (int nn = 0 ; nn < data->thread_count ; nn++) {
    6876:	31 c9                	xor    %ecx,%ecx
    6878:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                    int next_task = abs((nn + 1) % (data->thread_count));
    6880:	83 c1 01             	add    $0x1,%ecx
    6883:	89 c8                	mov    %ecx,%eax
    6885:	99                   	cltd
    6886:	f7 ff                	idiv   %edi
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6888:	48 63 d2             	movslq %edx,%rdx
    688b:	48 c1 e2 09          	shl    $0x9,%rdx
    688f:	49 8b 84 14 70 01 00 00 	mov    0x170(%r12,%rdx,1),%rax
    6897:	4c 89 ca             	mov    %r9,%rdx
    689a:	48 01 f0             	add    %rsi,%rax
    return mailbox->higher;
    689d:	f3 0f 6f 00          	movdqu (%rax),%xmm0
    68a1:	4c 8b 48 08          	mov    0x8(%rax),%r9
    mailbox->lower = data;
    68a5:	4c 89 00             	mov    %r8,(%rax)
    return mailbox->lower;
    68a8:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
    mailbox->lower = data;
    68ad:	41 0f 11 03          	movups %xmm0,(%r11)
    mailbox->higher = data;
    68b1:	48 89 50 08          	mov    %rdx,0x8(%rax)
                    ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    68b5:	48 8b 00             	mov    (%rax),%rax
                    ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    68b8:	41 c7 81 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%r9)
                    ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_sending = 1;
    68c3:	4d 8b 43 08          	mov    0x8(%r11),%r8
                    ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    68c7:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                    ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].higher)->available_sending = 1;
    68d1:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
                    ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_sending = 1;
    68db:	41 c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r8)
                   for (int nn = 0 ; nn < data->thread_count ; nn++) {
    68e6:	39 cf                	cmp    %ecx,%edi
    68e8:	75 96                	jne    6880 <barriered_work+0x270>
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    68ea:	48 83 c6 38          	add    $0x38,%rsi
    68ee:	48 81 c3 c8 00 00 00 	add    $0xc8,%rbx
    68f5:	48 39 f5             	cmp    %rsi,%rbp
    68f8:	0f 85 56 ff ff ff    	jne    6854 <barriered_work+0x244>
    68fe:	66 90                	xchg   %ax,%ax
    6900:	4c 8b 04 24          	mov    (%rsp),%r8
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6904:	49 83 c5 38          	add    $0x38,%r13
    6908:	49 81 c0 c8 00 00 00 	add    $0xc8,%r8
    690f:	4c 39 ed             	cmp    %r13,%rbp
    6912:	0f 85 08 ff ff ff    	jne    6820 <barriered_work+0x210>
    6918:	8b 54 24 20          	mov    0x20(%rsp),%edx
    691c:	8b 5c 24 24          	mov    0x24(%rsp),%ebx
    6920:	4c 8b 64 24 28       	mov    0x28(%rsp),%r12
    6925:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    692a:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    692f:	48 81 44 24 18 c8 00 00 00 	addq   $0xc8,0x18(%rsp)
    6938:	83 c2 01             	add    $0x1,%edx
    693b:	49 83 c4 38          	add    $0x38,%r12
    693f:	39 da                	cmp    %ebx,%edx
    6941:	0f 85 6c fd ff ff    	jne    66b3 <barriered_work+0xa3>
      struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    6947:	be 08 00 00 00       	mov    $0x8,%esi
    694c:	bf 00 04 00 00       	mov    $0x400,%edi
    6951:	e8 9a ba ff ff       	call   23f0 <calloc@plt>
    6956:	49 89 c4             	mov    %rax,%r12
      for (int k = 0 ; k < data->thread->group_count ; k++) {
    6959:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    695e:	48 8b 90 28 01 00 00 	mov    0x128(%rax),%rdx
    6965:	8b 82 c0 00 00 00    	mov    0xc0(%rdx),%eax
    696b:	89 44 24 18          	mov    %eax,0x18(%rsp)
    696f:	85 c0                	test   %eax,%eax
    6971:	0f 8e cf 03 00 00    	jle    6d46 <barriered_work+0x736>
        for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6977:	8b 82 c4 00 00 00    	mov    0xc4(%rdx),%eax
    697d:	44 8d 5b fe          	lea    -0x2(%rbx),%r11d
    6981:	31 f6                	xor    %esi,%esi
    6983:	48 89 d7             	mov    %rdx,%rdi
    6986:	44 8d 6b ff          	lea    -0x1(%rbx),%r13d
    698a:	49 83 c3 01          	add    $0x1,%r11
      for (int k = 0 ; k < data->thread->group_count ; k++) {
    698e:	31 c9                	xor    %ecx,%ecx
      int datas2_size = 0; 
    6990:	31 ed                	xor    %ebp,%ebp
    6992:	89 c2                	mov    %eax,%edx
    6994:	47 8d 44 2d 00       	lea    0x0(%r13,%r13,1),%r8d
    6999:	89 f0                	mov    %esi,%eax
    699b:	49 c1 e3 04          	shl    $0x4,%r11
    699f:	48 89 fe             	mov    %rdi,%rsi
        for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    69a2:	85 d2                	test   %edx,%edx
    69a4:	0f 8e f4 00 00 00    	jle    6a9e <barriered_work+0x48e>
    69aa:	4c 63 c8             	movslq %eax,%r9
          for (int n = 0 ; n < data->thread->all_threads[x].task_count ; n++) {
    69ad:	4c 8b 56 20          	mov    0x20(%rsi),%r10
    69b1:	89 4c 24 24          	mov    %ecx,0x24(%rsp)
    69b5:	4b 8d 3c 89          	lea    (%r9,%r9,4),%rdi
    69b9:	89 44 24 20          	mov    %eax,0x20(%rsp)
    69bd:	89 d0                	mov    %edx,%eax
    69bf:	48 8d 3c bf          	lea    (%rdi,%rdi,4),%rdi
    69c3:	4d 8d 34 fa          	lea    (%r10,%rdi,8),%r14
    69c7:	48 63 fa             	movslq %edx,%rdi
    69ca:	48 89 f2             	mov    %rsi,%rdx
    69cd:	4c 01 cf             	add    %r9,%rdi
    69d0:	48 8d 3c bf          	lea    (%rdi,%rdi,4),%rdi
    69d4:	48 8d 3c bf          	lea    (%rdi,%rdi,4),%rdi
    69d8:	4d 8d 3c fa          	lea    (%r10,%rdi,8),%r15
    69dc:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    69e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    69e8:	41 8b 4e 40          	mov    0x40(%r14),%ecx
    69ec:	85 c9                	test   %ecx,%ecx
    69ee:	0f 8e 8b 00 00 00    	jle    6a7f <barriered_work+0x46f>
    69f4:	4c 63 c9             	movslq %ecx,%r9
    69f7:	31 c9                	xor    %ecx,%ecx
    69f9:	49 c1 e1 09          	shl    $0x9,%r9
            for (int kk = 0 ; kk < data->mailbox_thread_count ; kk++) {
    69fd:	85 db                	test   %ebx,%ebx
    69ff:	0f 8e 91 03 00 00    	jle    6d96 <barriered_work+0x786>
    6a05:	4d 8b 56 38          	mov    0x38(%r14),%r10
    6a09:	4c 89 14 24          	mov    %r10,(%rsp)
    6a0d:	0f 1f 00             	nopl   (%rax)
              datas[datas2_size++] = ((struct Data*) ((struct Mailbox)data->thread->all_threads[x].tasks[n].mailboxes[kk]).lower);
    6a10:	48 8b 3c 24          	mov    (%rsp),%rdi
    6a14:	4c 8b bc 0f 70 01 00 00 	mov    0x170(%rdi,%rcx,1),%r15
    6a1c:	83 fb 01             	cmp    $0x1,%ebx
    6a1f:	0f 84 43 02 00 00    	je     6c68 <barriered_work+0x658>
    6a25:	48 63 f5             	movslq %ebp,%rsi
    6a28:	4c 89 ff             	mov    %r15,%rdi
    6a2b:	49 8d 34 f4          	lea    (%r12,%rsi,8),%rsi
    6a2f:	4d 8d 14 33          	lea    (%r11,%rsi,1),%r10
    6a33:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6a38:	f3 0f 6f 17          	movdqu (%rdi),%xmm2
    6a3c:	48 83 c6 10          	add    $0x10,%rsi
    6a40:	48 83 c7 38          	add    $0x38,%rdi
    6a44:	0f 11 56 f0          	movups %xmm2,-0x10(%rsi)
            for (int kk = 0 ; kk < data->mailbox_thread_count ; kk++) {
    6a48:	4c 39 d6             	cmp    %r10,%rsi
    6a4b:	75 eb                	jne    6a38 <barriered_work+0x428>
    6a4d:	46 8d 54 05 00       	lea    0x0(%rbp,%r8,1),%r10d
    6a52:	49 63 f5             	movslq %r13d,%rsi
              datas[datas2_size++] = ((struct Data*) ((struct Mailbox)data->thread->all_threads[x].tasks[n].mailboxes[kk]).lower);
    6a55:	48 8d 3c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rdi
    6a5d:	4d 63 d2             	movslq %r10d,%r10
    6a60:	42 8d 6c 05 02       	lea    0x2(%rbp,%r8,1),%ebp
          for (int n = 0 ; n < data->thread->all_threads[x].task_count ; n++) {
    6a65:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
              datas[datas2_size++] = ((struct Data*) ((struct Mailbox)data->thread->all_threads[x].tasks[n].mailboxes[kk]).lower);
    6a6c:	48 29 f7             	sub    %rsi,%rdi
    6a6f:	f3 41 0f 6f 04 ff    	movdqu (%r15,%rdi,8),%xmm0
    6a75:	43 0f 11 04 d4       	movups %xmm0,(%r12,%r10,8)
          for (int n = 0 ; n < data->thread->all_threads[x].task_count ; n++) {
    6a7a:	4c 39 c9             	cmp    %r9,%rcx
    6a7d:	75 91                	jne    6a10 <barriered_work+0x400>
        for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6a7f:	49 81 c6 c8 00 00 00 	add    $0xc8,%r14
    6a86:	4c 39 74 24 08       	cmp    %r14,0x8(%rsp)
    6a8b:	0f 85 57 ff ff ff    	jne    69e8 <barriered_work+0x3d8>
    6a91:	48 89 d6             	mov    %rdx,%rsi
    6a94:	8b 4c 24 24          	mov    0x24(%rsp),%ecx
    6a98:	89 c2                	mov    %eax,%edx
    6a9a:	8b 44 24 20          	mov    0x20(%rsp),%eax
      for (int k = 0 ; k < data->thread->group_count ; k++) {
    6a9e:	83 c1 01             	add    $0x1,%ecx
    6aa1:	01 d0                	add    %edx,%eax
    6aa3:	39 4c 24 18          	cmp    %ecx,0x18(%rsp)
    6aa7:	0f 85 f5 fe ff ff    	jne    69a2 <barriered_work+0x392>
      char * name = calloc(100, sizeof(char));
    6aad:	48 89 34 24          	mov    %rsi,(%rsp)
    6ab1:	bf 64 00 00 00       	mov    $0x64,%edi
    6ab6:	be 01 00 00 00       	mov    $0x1,%esi
    6abb:	e8 30 b9 ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    6ac0:	48 8b 14 24          	mov    (%rsp),%rdx
    6ac4:	be 01 00 00 00       	mov    $0x1,%esi
    6ac9:	48 8d 0d 76 17 00 00 	lea    0x1776(%rip),%rcx        # 8246 <_IO_stdin_used+0x246>
    6ad0:	48 89 c3             	mov    %rax,%rbx
    6ad3:	48 89 c7             	mov    %rax,%rdi
    6ad6:	31 c0                	xor    %eax,%eax
    6ad8:	44 8b 42 08          	mov    0x8(%rdx),%r8d
    6adc:	ba 64 00 00 00       	mov    $0x64,%edx
    6ae1:	e8 9a ba ff ff       	call   2580 <__sprintf_chk@plt>
      m2 = fopen(name, "w");
    6ae6:	48 89 df             	mov    %rbx,%rdi
    6ae9:	48 8d 35 62 17 00 00 	lea    0x1762(%rip),%rsi        # 8252 <_IO_stdin_used+0x252>
    6af0:	e8 eb b9 ff ff       	call   24e0 <fopen@plt>
    6af5:	48 89 c3             	mov    %rax,%rbx
      for (int x = 0 ; x < datas2_size; x++) {
    6af8:	85 ed                	test   %ebp,%ebp
    6afa:	7e 59                	jle    6b55 <barriered_work+0x545>
    6afc:	48 63 ed             	movslq %ebp,%rbp
    6aff:	4d 89 e5             	mov    %r12,%r13
    6b02:	4c 8d 35 d3 18 00 00 	lea    0x18d3(%rip),%r14        # 83dc <_IO_stdin_used+0x3dc>
    6b09:	4d 8d 3c ec          	lea    (%r12,%rbp,8),%r15
        char * c = calloc(250, sizeof(char));
    6b0d:	be 01 00 00 00       	mov    $0x1,%esi
    6b12:	bf fa 00 00 00       	mov    $0xfa,%edi
      for (int x = 0 ; x < datas2_size; x++) {
    6b17:	49 83 c5 08          	add    $0x8,%r13
        char * c = calloc(250, sizeof(char));
    6b1b:	e8 d0 b8 ff ff       	call   23f0 <calloc@plt>
    6b20:	4c 89 f1             	mov    %r14,%rcx
    6b23:	ba fa 00 00 00       	mov    $0xfa,%edx
    6b28:	be 01 00 00 00       	mov    $0x1,%esi
    6b2d:	48 89 c5             	mov    %rax,%rbp
        sprintf(c, "mailbox %d\n", datas[x]->id);
    6b30:	49 8b 45 f8          	mov    -0x8(%r13),%rax
    6b34:	48 89 ef             	mov    %rbp,%rdi
    6b37:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    6b3e:	31 c0                	xor    %eax,%eax
    6b40:	e8 3b ba ff ff       	call   2580 <__sprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6b45:	48 89 de             	mov    %rbx,%rsi
    6b48:	48 89 ef             	mov    %rbp,%rdi
    6b4b:	e8 60 b8 ff ff       	call   23b0 <fputs@plt>
      for (int x = 0 ; x < datas2_size; x++) {
    6b50:	4d 39 fd             	cmp    %r15,%r13
    6b53:	75 b8                	jne    6b0d <barriered_work+0x4fd>
      fclose(m2);
    6b55:	48 89 df             	mov    %rbx,%rdi
    6b58:	e8 f3 b7 ff ff       	call   2350 <fclose@plt>
      free(datas);
    6b5d:	4c 89 e7             	mov    %r12,%rdi
    6b60:	e8 8b b7 ff ff       	call   22f0 <free@plt>
      asm volatile ("sfence" ::: "memory");
    6b65:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6b68:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6b6d:	31 ff                	xor    %edi,%edi
    6b6f:	48 8b 9d 60 01 00 00 	mov    0x160(%rbp),%rbx
    6b76:	48 89 de             	mov    %rbx,%rsi
    6b79:	48 89 1c 24          	mov    %rbx,(%rsp)
    6b7d:	48 c1 e6 05          	shl    $0x5,%rsi
    6b81:	48 03 b5 50 01 00 00 	add    0x150(%rbp),%rsi
    6b88:	e8 b3 b7 ff ff       	call   2340 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6b8d:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    6b94:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6b98:	8b 5a 10             	mov    0x10(%rdx),%ebx
    6b9b:	83 c3 01             	add    $0x1,%ebx
    while (data->scheduled == 1) {
    6b9e:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    int modcount = ++data->thread->protected_state->modcount;
    6ba5:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    6ba8:	74 0d                	je     6bb7 <barriered_work+0x5a7>
    6baa:	eb 61                	jmp    6c0d <barriered_work+0x5fd>
    6bac:	0f 1f 40 00          	nopl   0x0(%rax)
    if (modcount != data->thread->protected_state->modcount) {
    6bb0:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6bb7:	48 63 95 30 01 00 00 	movslq 0x130(%rbp),%rdx
    6bbe:	48 8b 40 18          	mov    0x18(%rax),%rax
    6bc2:	48 63 7d 04          	movslq 0x4(%rbp),%rdi
      data->n++;
    6bc6:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6bce:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6bd2:	48 c1 e7 09          	shl    $0x9,%rdi
    6bd6:	48 03 78 38          	add    0x38(%rax),%rdi
    6bda:	ff 95 20 01 00 00    	call   *0x120(%rbp)
      asm volatile ("sfence" ::: "memory");
    6be0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6be3:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    6bea:	74 c4                	je     6bb0 <barriered_work+0x5a0>
    if (modcount != data->thread->protected_state->modcount) {
    6bec:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6bf1:	48 8b 80 28 01 00 00 	mov    0x128(%rax),%rax
    6bf8:	48 8b 40 48          	mov    0x48(%rax),%rax
    6bfc:	3b 58 10             	cmp    0x10(%rax),%ebx
    6bff:	74 0c                	je     6c0d <barriered_work+0x5fd>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6c01:	48 8d 3d 4c 16 00 00 	lea    0x164c(%rip),%rdi        # 8254 <_IO_stdin_used+0x254>
    6c08:	e8 13 b7 ff ff       	call   2320 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6c0d:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    6c12:	31 ff                	xor    %edi,%edi
    6c14:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6c1b:	48 89 c6             	mov    %rax,%rsi
    6c1e:	48 89 04 24          	mov    %rax,(%rsp)
    6c22:	48 c1 e6 05          	shl    $0x5,%rsi
    6c26:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6c2d:	48 83 c6 10          	add    $0x10,%rsi
    6c31:	e8 0a b7 ff ff       	call   2340 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6c36:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    sendm(data);
    6c3d:	48 89 df             	mov    %rbx,%rdi
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6c40:	48 89 04 24          	mov    %rax,(%rsp)
    6c44:	48 83 c0 01          	add    $0x1,%rax
    6c48:	48 99                	cqto
    6c4a:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6c51:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    sendm(data);
    6c58:	e8 83 f7 ff ff       	call   63e0 <sendm>
    6c5d:	e9 04 fa ff ff       	jmp    6666 <barriered_work+0x56>
    6c62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              datas[datas2_size++] = ((struct Data*) ((struct Mailbox)data->thread->all_threads[x].tasks[n].mailboxes[kk]).lower);
    6c68:	41 89 ea             	mov    %ebp,%r10d
            for (int kk = 0 ; kk < data->mailbox_thread_count ; kk++) {
    6c6b:	31 f6                	xor    %esi,%esi
    6c6d:	e9 e3 fd ff ff       	jmp    6a55 <barriered_work+0x445>
                  for (int nn = 0 ; nn < data->thread_count ; nn++) {
    6c72:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    6c77:	49 8d 81 70 01 00 00 	lea    0x170(%r9),%rax
    6c7e:	31 d2                	xor    %edx,%edx
    6c80:	4c 89 0c 24          	mov    %r9,(%rsp)
    6c84:	41 89 d1             	mov    %edx,%r9d
    6c87:	44 89 54 24 20       	mov    %r10d,0x20(%rsp)
    6c8c:	49 89 c2             	mov    %rax,%r10
                    int next_task = abs(nn + 1) % data->thread_count;
    6c8f:	41 83 c1 01          	add    $0x1,%r9d
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6c93:	4d 8b 32             	mov    (%r10),%r14
                  for (int nn = 0 ; nn < data->thread_count ; nn++) {
    6c96:	49 81 c2 00 02 00 00 	add    $0x200,%r10
                    int next_task = abs(nn + 1) % data->thread_count;
    6c9d:	44 89 c8             	mov    %r9d,%eax
    6ca0:	99                   	cltd
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6ca1:	4d 01 e6             	add    %r12,%r14
                    int next_task = abs(nn + 1) % data->thread_count;
    6ca4:	41 f7 ff             	idiv   %r15d
    return mailbox->lower;
    6ca7:	4d 8b 2e             	mov    (%r14),%r13
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6caa:	48 63 d2             	movslq %edx,%rdx
    6cad:	48 c1 e2 09          	shl    $0x9,%rdx
    6cb1:	49 8b 84 13 70 01 00 00 	mov    0x170(%r11,%rdx,1),%rax
    6cb9:	48 01 f8             	add    %rdi,%rax
    return mailbox->higher;
    6cbc:	f3 0f 6f 00          	movdqu (%rax),%xmm0
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6cc0:	48 89 c2             	mov    %rax,%rdx
    mailbox->lower = data;
    6cc3:	49 8b 46 08          	mov    0x8(%r14),%rax
    return mailbox->lower;
    6cc7:	66 0f 6f c8          	movdqa %xmm0,%xmm1
    mailbox->lower = data;
    6ccb:	48 89 02             	mov    %rax,(%rdx)
                        ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6cce:	0f 12 d8             	movhlps %xmm0,%xmm3
    return mailbox->lower;
    6cd1:	66 0f c6 c8 01       	shufpd $0x1,%xmm0,%xmm1
    mailbox->lower = data;
    6cd6:	41 0f 11 0e          	movups %xmm1,(%r14)
                        ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6cda:	66 48 0f 7e d8       	movq   %xmm3,%rax
    mailbox->higher = data;
    6cdf:	4c 89 6a 08          	mov    %r13,0x8(%rdx)
                         ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
    6ce3:	4d 8b 76 08          	mov    0x8(%r14),%r14
    6ce7:	41 c7 86 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%r14)
                        ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6cf2:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                        ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6cfc:	48 8b 02             	mov    (%rdx),%rax
    6cff:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                        ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_sending = 1;
    6d09:	41 c7 86 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r14)
                        ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 0;
    6d14:	41 c7 86 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r14)
                        ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].higher)->available_receiving = 0;
    6d1f:	41 c7 85 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r13)
                  for (int nn = 0 ; nn < data->thread_count ; nn++) {
    6d2a:	45 39 cf             	cmp    %r9d,%r15d
    6d2d:	0f 85 5c ff ff ff    	jne    6c8f <barriered_work+0x67f>
    6d33:	4c 8b 0c 24          	mov    (%rsp),%r9
    6d37:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    6d3c:	44 8b 54 24 20       	mov    0x20(%rsp),%r10d
    6d41:	e9 03 fa ff ff       	jmp    6749 <barriered_work+0x139>
      char * name = calloc(100, sizeof(char));
    6d46:	be 01 00 00 00       	mov    $0x1,%esi
    6d4b:	bf 64 00 00 00       	mov    $0x64,%edi
    6d50:	48 89 14 24          	mov    %rdx,(%rsp)
    6d54:	e8 97 b6 ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    6d59:	48 8b 14 24          	mov    (%rsp),%rdx
    6d5d:	be 01 00 00 00       	mov    $0x1,%esi
    6d62:	48 8d 0d dd 14 00 00 	lea    0x14dd(%rip),%rcx        # 8246 <_IO_stdin_used+0x246>
    6d69:	48 89 c3             	mov    %rax,%rbx
    6d6c:	48 89 c7             	mov    %rax,%rdi
    6d6f:	31 c0                	xor    %eax,%eax
    6d71:	44 8b 42 08          	mov    0x8(%rdx),%r8d
    6d75:	ba 64 00 00 00       	mov    $0x64,%edx
    6d7a:	e8 01 b8 ff ff       	call   2580 <__sprintf_chk@plt>
      m2 = fopen(name, "w");
    6d7f:	48 89 df             	mov    %rbx,%rdi
    6d82:	48 8d 35 c9 14 00 00 	lea    0x14c9(%rip),%rsi        # 8252 <_IO_stdin_used+0x252>
    6d89:	e8 52 b7 ff ff       	call   24e0 <fopen@plt>
    6d8e:	48 89 c3             	mov    %rax,%rbx
      for (int x = 0 ; x < datas2_size; x++) {
    6d91:	e9 bf fd ff ff       	jmp    6b55 <barriered_work+0x545>
          for (int n = 0 ; n < data->thread->all_threads[x].task_count ; n++) {
    6d96:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
    6d9d:	4c 39 c9             	cmp    %r9,%rcx
    6da0:	0f 85 57 fc ff ff    	jne    69fd <barriered_work+0x3ed>
    6da6:	e9 d4 fc ff ff       	jmp    6a7f <barriered_work+0x46f>
    6dab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006db0 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6db0:	f3 0f 1e fa          	endbr64
    6db4:	53                   	push   %rbx
    6db5:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6db8:	e8 d3 f0 ff ff       	call   5e90 <barriered_work_ingest>
  barriered_work(data);
    6dbd:	48 89 df             	mov    %rbx,%rdi
}
    6dc0:	5b                   	pop    %rbx
  barriered_work(data);
    6dc1:	e9 4a f8 ff ff       	jmp    6610 <barriered_work>
    6dc6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006dd0 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    6dd0:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6dd4:	85 f6                	test   %esi,%esi
    6dd6:	74 10                	je     6de8 <mailboxkind+0x18>
  return NULL;
    6dd8:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    6dda:	83 fe 01             	cmp    $0x1,%esi
    6ddd:	74 01                	je     6de0 <mailboxkind+0x10>
}
    6ddf:	c3                   	ret
    return mailbox->higher;
    6de0:	48 8b 47 08          	mov    0x8(%rdi),%rax
}
    6de4:	c3                   	ret
    6de5:	0f 1f 00             	nopl   (%rax)
    return mailbox->lower;
    6de8:	48 8b 07             	mov    (%rdi),%rax
    6deb:	c3                   	ret
    6dec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006df0 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    6df0:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6df4:	85 d2                	test   %edx,%edx
    6df6:	75 08                	jne    6e00 <setmailboxkind+0x10>
    mailbox->lower = data;
    6df8:	48 89 37             	mov    %rsi,(%rdi)
}
    6dfb:	31 c0                	xor    %eax,%eax
    6dfd:	c3                   	ret
    6dfe:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    6e00:	83 fa 01             	cmp    $0x1,%edx
    6e03:	74 13                	je     6e18 <setmailboxkind+0x28>
  if (kind == 2) {
    6e05:	83 fa 02             	cmp    $0x2,%edx
    6e08:	75 f1                	jne    6dfb <setmailboxkind+0xb>
    mailbox->pending = data;
    6e0a:	48 89 77 10          	mov    %rsi,0x10(%rdi)
}
    6e0e:	31 c0                	xor    %eax,%eax
    6e10:	c3                   	ret
    6e11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    mailbox->higher = data;
    6e18:	48 89 77 08          	mov    %rsi,0x8(%rdi)
}
    6e1c:	31 c0                	xor    %eax,%eax
    6e1e:	c3                   	ret
    6e1f:	90                   	nop

0000000000006e20 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6e20:	f3 0f 1e fa          	endbr64
}
    6e24:	31 c0                	xor    %eax,%eax
    6e26:	c3                   	ret
    6e27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006e30 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6e30:	f3 0f 1e fa          	endbr64
    6e34:	31 c0                	xor    %eax,%eax
    6e36:	c3                   	ret
    6e37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006e40 <after>:
int after(struct timespec left, struct timespec right) {
    6e40:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6e44:	31 c0                	xor    %eax,%eax
    6e46:	48 39 d7             	cmp    %rdx,%rdi
    6e49:	7e 08                	jle    6e53 <after+0x13>
    6e4b:	31 c0                	xor    %eax,%eax
    6e4d:	48 39 ce             	cmp    %rcx,%rsi
    6e50:	0f 9f c0             	setg   %al
}
    6e53:	c3                   	ret
    6e54:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6e5f:	90                   	nop

0000000000006e60 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6e60:	f3 0f 1e fa          	endbr64
    6e64:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6e69:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    6e6e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6e70:	48 39 d7             	cmp    %rdx,%rdi
    6e73:	7f 18                	jg     6e8d <within+0x2d>
    6e75:	4d 39 d8             	cmp    %r11,%r8
    6e78:	0f 9e c2             	setle  %dl
    6e7b:	48 39 ce             	cmp    %rcx,%rsi
    6e7e:	0f 9e c0             	setle  %al
    6e81:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6e83:	31 c0                	xor    %eax,%eax
    6e85:	4d 39 d1             	cmp    %r10,%r9
    6e88:	0f 9e c0             	setle  %al
    6e8b:	21 d0                	and    %edx,%eax
}
    6e8d:	c3                   	ret
    6e8e:	66 90                	xchg   %ax,%ax

0000000000006e90 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6e90:	f3 0f 1e fa          	endbr64
    6e94:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6e99:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    6e9e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6ea3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6ea8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    6ead:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6eb2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6eb7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    6ebc:	48 39 fe             	cmp    %rdi,%rsi
    6ebf:	7d 2f                	jge    6ef0 <overlap+0x60>
    6ec1:	48 39 ca             	cmp    %rcx,%rdx
    6ec4:	7d 62                	jge    6f28 <overlap+0x98>
    6ec6:	4d 39 da             	cmp    %r11,%r10
    6ec9:	7d 0e                	jge    6ed9 <overlap+0x49>
    return 1;
    6ecb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6ed0:	4d 39 c1             	cmp    %r8,%r9
    6ed3:	0f 8c 7f 00 00 00    	jl     6f58 <overlap+0xc8>
  return 0;
    6ed9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6edb:	4d 39 c1             	cmp    %r8,%r9
    6ede:	7f 4c                	jg     6f2c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6ee0:	31 c0                	xor    %eax,%eax
    6ee2:	4d 39 da             	cmp    %r11,%r10
    6ee5:	0f 9e c0             	setle  %al
    6ee8:	c3                   	ret
    6ee9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6ef0:	7e 4e                	jle    6f40 <overlap+0xb0>
    6ef2:	48 39 ca             	cmp    %rcx,%rdx
    6ef5:	7f 39                	jg     6f30 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6ef7:	75 31                	jne    6f2a <overlap+0x9a>
    6ef9:	4d 39 c1             	cmp    %r8,%r9
    6efc:	7c 2c                	jl     6f2a <overlap+0x9a>
    return 1;
    6efe:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6f03:	4d 39 da             	cmp    %r11,%r10
    6f06:	7d 24                	jge    6f2c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f08:	48 39 ca             	cmp    %rcx,%rdx
    6f0b:	0f 94 c2             	sete   %dl
    6f0e:	48 39 fe             	cmp    %rdi,%rsi
    6f11:	0f 94 c0             	sete   %al
    6f14:	21 c2                	and    %eax,%edx
    6f16:	31 c0                	xor    %eax,%eax
    6f18:	4d 39 c1             	cmp    %r8,%r9
    6f1b:	0f 94 c0             	sete   %al
    6f1e:	21 d0                	and    %edx,%eax
    6f20:	c3                   	ret
    6f21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6f28:	74 af                	je     6ed9 <overlap+0x49>
  return 0;
    6f2a:	31 c0                	xor    %eax,%eax
}
    6f2c:	c3                   	ret
    6f2d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6f30:	4d 39 da             	cmp    %r11,%r10
    6f33:	7e c4                	jle    6ef9 <overlap+0x69>
    return 1;
    6f35:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6f3a:	4d 39 c1             	cmp    %r8,%r9
    6f3d:	7e ba                	jle    6ef9 <overlap+0x69>
    6f3f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f40:	48 39 ca             	cmp    %rcx,%rdx
    6f43:	7c 94                	jl     6ed9 <overlap+0x49>
    6f45:	4d 39 c1             	cmp    %r8,%r9
    6f48:	7d b4                	jge    6efe <overlap+0x6e>
    6f4a:	48 39 ca             	cmp    %rcx,%rdx
    6f4d:	74 91                	je     6ee0 <overlap+0x50>
    6f4f:	eb d9                	jmp    6f2a <overlap+0x9a>
    6f51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6f58:	c3                   	ret
    6f59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006f60 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6f60:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6f64:	85 f6                	test   %esi,%esi
    6f66:	0f 8e 44 03 00 00    	jle    72b0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    6f6c:	41 57                	push   %r15
    6f6e:	41 89 f7             	mov    %esi,%r15d
    6f71:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6f73:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6f76:	41 55                	push   %r13
    6f78:	41 54                	push   %r12
    6f7a:	55                   	push   %rbp
    6f7b:	53                   	push   %rbx
    6f7c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6f80:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6f84:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6f89:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    6f8e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6f91:	45 39 e6             	cmp    %r12d,%r14d
    6f94:	0f 84 4e 02 00 00    	je     71e8 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6f9a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6f9f:	8b 50 08             	mov    0x8(%rax),%edx
    6fa2:	85 d2                	test   %edx,%edx
    6fa4:	0f 8e 3e 02 00 00    	jle    71e8 <verify+0x288>
    6faa:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    6faf:	31 c9                	xor    %ecx,%ecx
    6fb1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6fb6:	31 c0                	xor    %eax,%eax
    6fb8:	44 89 f2             	mov    %r14d,%edx
    6fbb:	bf 01 00 00 00       	mov    $0x1,%edi
    6fc0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6fc5:	48 8d 35 98 12 00 00 	lea    0x1298(%rip),%rsi        # 8264 <_IO_stdin_used+0x264>
    6fcc:	e8 cf b4 ff ff       	call   24a0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6fd1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6fd6:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    6fdb:	8b 40 08             	mov    0x8(%rax),%eax
    6fde:	85 c0                	test   %eax,%eax
    6fe0:	0f 8e e6 01 00 00    	jle    71cc <verify+0x26c>
    6fe6:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6fe9:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    6fee:	31 db                	xor    %ebx,%ebx
    6ff0:	48 c1 e0 09          	shl    $0x9,%rax
    6ff4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6ff9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    6ffe:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7003:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    7008:	4c 8b 20             	mov    (%rax),%r12
    700b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7010:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    7015:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    701a:	49 89 de             	mov    %rbx,%r14
    701d:	48 8d 35 55 12 00 00 	lea    0x1255(%rip),%rsi        # 8279 <_IO_stdin_used+0x279>
    7024:	49 c1 e6 09          	shl    $0x9,%r14
    7028:	bf 01 00 00 00       	mov    $0x1,%edi
    702d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    7031:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    7039:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    703e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    7046:	31 c0                	xor    %eax,%eax
    7048:	e8 53 b4 ff ff       	call   24a0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    704d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7052:	4c 8b 20             	mov    (%rax),%r12
    7055:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    705e:	0f 8e 47 01 00 00    	jle    71ab <verify+0x24b>
    7064:	4c 03 75 00          	add    0x0(%rbp),%r14
    7068:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    706d:	ba 01 00 00 00       	mov    $0x1,%edx
    7072:	4d 89 f5             	mov    %r14,%r13
    7075:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    707c:	4d 85 f6             	test   %r14,%r14
    707f:	0f 8e 21 01 00 00    	jle    71a6 <verify+0x246>
    7085:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    7088:	48 89 d5             	mov    %rdx,%rbp
    708b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7090:	31 db                	xor    %ebx,%ebx
    7092:	4d 89 f2             	mov    %r14,%r10
    7095:	48 c1 e5 05          	shl    $0x5,%rbp
    7099:	48 83 ed 20          	sub    $0x20,%rbp
    709d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    70a1:	49 89 ee             	mov    %rbp,%r14
    70a4:	48 89 dd             	mov    %rbx,%rbp
    70a7:	48 89 d3             	mov    %rdx,%rbx
    70aa:	eb 31                	jmp    70dd <verify+0x17d>
    70ac:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    70b0:	4c 39 c2             	cmp    %r8,%rdx
    70b3:	0f 8d 57 01 00 00    	jge    7210 <verify+0x2b0>
    70b9:	4c 39 df             	cmp    %r11,%rdi
    70bc:	7e 05                	jle    70c3 <verify+0x163>
    70be:	49 39 c1             	cmp    %rax,%r9
    70c1:	7c 75                	jl     7138 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    70c3:	4c 39 df             	cmp    %r11,%rdi
    70c6:	0f 8d ab 01 00 00    	jge    7277 <verify+0x317>
    70cc:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    70d0:	48 83 c5 01          	add    $0x1,%rbp
    70d4:	49 39 ea             	cmp    %rbp,%r10
    70d7:	0f 8e a9 00 00 00    	jle    7186 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    70dd:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    70e4:	48 89 e8             	mov    %rbp,%rax
    70e7:	48 c1 e0 05          	shl    $0x5,%rax
    70eb:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    70f2:	4c 01 f2             	add    %r14,%rdx
    70f5:	48 8b 08             	mov    (%rax),%rcx
    70f8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    70fc:	48 8b 32             	mov    (%rdx),%rsi
    70ff:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    7103:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    7107:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    710b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    710f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    7113:	48 39 f1             	cmp    %rsi,%rcx
    7116:	7c 98                	jl     70b0 <verify+0x150>
    7118:	0f 8e 42 01 00 00    	jle    7260 <verify+0x300>
    711e:	4c 39 c2             	cmp    %r8,%rdx
    7121:	0f 8f f9 00 00 00    	jg     7220 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7127:	75 a7                	jne    70d0 <verify+0x170>
    7129:	4c 39 df             	cmp    %r11,%rdi
    712c:	7f a2                	jg     70d0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    712e:	49 39 c1             	cmp    %rax,%r9
    7131:	7c 9d                	jl     70d0 <verify+0x170>
    7133:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7138:	49 89 c1             	mov    %rax,%r9
    713b:	48 89 f9             	mov    %rdi,%rcx
    713e:	48 89 f2             	mov    %rsi,%rdx
    7141:	bf 01 00 00 00       	mov    $0x1,%edi
    7146:	48 8d 35 e3 14 00 00 	lea    0x14e3(%rip),%rsi        # 8630 <_IO_stdin_used+0x630>
    714d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    714f:	48 83 c5 01          	add    $0x1,%rbp
    7153:	e8 48 b3 ff ff       	call   24a0 <__printf_chk@plt>
    7158:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    715d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    7162:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7165:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    716a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7171:	4c 8b 20             	mov    (%rax),%r12
    7174:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7179:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    717d:	49 39 ea             	cmp    %rbp,%r10
    7180:	0f 8f 57 ff ff ff    	jg     70dd <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7186:	48 89 da             	mov    %rbx,%rdx
    7189:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    7190:	7d 14                	jge    71a6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7192:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7199:	48 83 c2 01          	add    $0x1,%rdx
    719d:	4d 85 f6             	test   %r14,%r14
    71a0:	0f 8f e2 fe ff ff    	jg     7088 <verify+0x128>
    71a6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    71ab:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    71b0:	48 83 c3 01          	add    $0x1,%rbx
    71b4:	39 58 08             	cmp    %ebx,0x8(%rax)
    71b7:	0f 8f 53 fe ff ff    	jg     7010 <verify+0xb0>
    71bd:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    71c2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    71c7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    71cc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    71d1:	48 83 c1 01          	add    $0x1,%rcx
    71d5:	39 48 08             	cmp    %ecx,0x8(%rax)
    71d8:	0f 8f d8 fd ff ff    	jg     6fb6 <verify+0x56>
    71de:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    71e3:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    71e8:	48 81 44 24 10 c8 00 00 00 	addq   $0xc8,0x10(%rsp)
    71f1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    71f6:	41 39 c7             	cmp    %eax,%r15d
    71f9:	0f 84 86 00 00 00    	je     7285 <verify+0x325>
    71ff:	41 89 c4             	mov    %eax,%r12d
    7202:	e9 8a fd ff ff       	jmp    6f91 <verify+0x31>
    7207:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7210:	0f 85 ba fe ff ff    	jne    70d0 <verify+0x170>
    7216:	e9 a8 fe ff ff       	jmp    70c3 <verify+0x163>
    721b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    7220:	49 39 c1             	cmp    %rax,%r9
    7223:	7e 09                	jle    722e <verify+0x2ce>
    7225:	4c 39 df             	cmp    %r11,%rdi
    7228:	0f 8c 0a ff ff ff    	jl     7138 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    722e:	4c 39 df             	cmp    %r11,%rdi
    7231:	0f 8f 99 fe ff ff    	jg     70d0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7237:	49 39 c1             	cmp    %rax,%r9
    723a:	0f 8d f8 fe ff ff    	jge    7138 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7240:	48 39 f1             	cmp    %rsi,%rcx
    7243:	0f 85 87 fe ff ff    	jne    70d0 <verify+0x170>
    7249:	4c 39 c2             	cmp    %r8,%rdx
    724c:	0f 85 7e fe ff ff    	jne    70d0 <verify+0x170>
    7252:	4c 39 df             	cmp    %r11,%rdi
    7255:	0f 84 dd fe ff ff    	je     7138 <verify+0x1d8>
    725b:	e9 70 fe ff ff       	jmp    70d0 <verify+0x170>
    7260:	4c 39 c2             	cmp    %r8,%rdx
    7263:	0f 8c 5a fe ff ff    	jl     70c3 <verify+0x163>
    7269:	4c 39 df             	cmp    %r11,%rdi
    726c:	7e c9                	jle    7237 <verify+0x2d7>
    726e:	4c 39 c2             	cmp    %r8,%rdx
    7271:	0f 85 59 fe ff ff    	jne    70d0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7277:	49 39 c1             	cmp    %rax,%r9
    727a:	0f 8f 50 fe ff ff    	jg     70d0 <verify+0x170>
    7280:	e9 b3 fe ff ff       	jmp    7138 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    7285:	48 81 44 24 18 c8 00 00 00 	addq   $0xc8,0x18(%rsp)
    728e:	41 8d 46 01          	lea    0x1(%r14),%eax
    7292:	45 39 e6             	cmp    %r12d,%r14d
    7295:	74 08                	je     729f <verify+0x33f>
    7297:	41 89 c6             	mov    %eax,%r14d
    729a:	e9 ea fc ff ff       	jmp    6f89 <verify+0x29>
}
    729f:	48 83 c4 58          	add    $0x58,%rsp
    72a3:	31 c0                	xor    %eax,%eax
    72a5:	5b                   	pop    %rbx
    72a6:	5d                   	pop    %rbp
    72a7:	41 5c                	pop    %r12
    72a9:	41 5d                	pop    %r13
    72ab:	41 5e                	pop    %r14
    72ad:	41 5f                	pop    %r15
    72af:	c3                   	ret
    72b0:	31 c0                	xor    %eax,%eax
    72b2:	c3                   	ret

Disassembly of section .fini:

00000000000072b4 <_fini>:
    72b4:	f3 0f 1e fa          	endbr64
    72b8:	48 83 ec 08          	sub    $0x8,%rsp
    72bc:	48 83 c4 08          	add    $0x8,%rsp
    72c0:	c3                   	ret
