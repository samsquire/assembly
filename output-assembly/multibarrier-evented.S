
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
    267d:	48 8d 05 dc 1c 00 00 	lea    0x1cdc(%rip),%rax        # 4360 <barriered_reset>
    2684:	66 48 0f 6e f0       	movq   %rax,%xmm6
    2689:	0f 16 35 d0 85 00 00 	movhps 0x85d0(%rip),%xmm6        # ac60 <__do_global_dtors_aux_fini_array_entry+0x8>
    2690:	0f 29 b4 24 a0 00 00 00 	movaps %xmm6,0xa0(%rsp)
    2698:	e8 83 fc ff ff       	call   2320 <puts@plt>
    269d:	bf 0a 00 00 00       	mov    $0xa,%edi
    26a2:	e8 59 fc ff ff       	call   2300 <putchar@plt>
    26a7:	ba 01 00 00 00       	mov    $0x1,%edx
    26ac:	48 8d 35 c1 5b 00 00 	lea    0x5bc1(%rip),%rsi        # 8274 <_IO_stdin_used+0x274>
    26b3:	31 c0                	xor    %eax,%eax
    26b5:	bf 01 00 00 00       	mov    $0x1,%edi
    26ba:	e8 e1 fd ff ff       	call   24a0 <__printf_chk@plt>
    26bf:	ba 06 00 00 00       	mov    $0x6,%edx
    26c4:	48 8d 35 b9 5b 00 00 	lea    0x5bb9(%rip),%rsi        # 8284 <_IO_stdin_used+0x284>
    26cb:	31 c0                	xor    %eax,%eax
    26cd:	bf 01 00 00 00       	mov    $0x1,%edi
    26d2:	e8 c9 fd ff ff       	call   24a0 <__printf_chk@plt>
    26d7:	ba 03 00 00 00       	mov    $0x3,%edx
    26dc:	48 8d 35 b6 5b 00 00 	lea    0x5bb6(%rip),%rsi        # 8299 <_IO_stdin_used+0x299>
    26e3:	31 c0                	xor    %eax,%eax
    26e5:	bf 01 00 00 00       	mov    $0x1,%edi
    26ea:	e8 b1 fd ff ff       	call   24a0 <__printf_chk@plt>
    26ef:	ba 02 00 00 00       	mov    $0x2,%edx
    26f4:	48 8d 35 ae 5b 00 00 	lea    0x5bae(%rip),%rsi        # 82a9 <_IO_stdin_used+0x2a9>
    26fb:	31 c0                	xor    %eax,%eax
    26fd:	bf 01 00 00 00       	mov    $0x1,%edi
    2702:	e8 99 fd ff ff       	call   24a0 <__printf_chk@plt>
    2707:	48 8d 3d b1 5b 00 00 	lea    0x5bb1(%rip),%rdi        # 82bf <_IO_stdin_used+0x2bf>
    270e:	e8 0d fc ff ff       	call   2320 <puts@plt>
    2713:	ba 02 00 00 00       	mov    $0x2,%edx
    2718:	48 8d 35 bc 5b 00 00 	lea    0x5bbc(%rip),%rsi        # 82db <_IO_stdin_used+0x2db>
    271f:	31 c0                	xor    %eax,%eax
    2721:	bf 01 00 00 00       	mov    $0x1,%edi
    2726:	e8 75 fd ff ff       	call   24a0 <__printf_chk@plt>
    272b:	ba 0a 00 00 00       	mov    $0xa,%edx
    2730:	48 8d 35 be 5b 00 00 	lea    0x5bbe(%rip),%rsi        # 82f5 <_IO_stdin_used+0x2f5>
    2737:	31 c0                	xor    %eax,%eax
    2739:	bf 01 00 00 00       	mov    $0x1,%edi
    273e:	e8 5d fd ff ff       	call   24a0 <__printf_chk@plt>
    2743:	ba 01 00 00 00       	mov    $0x1,%edx
    2748:	48 8d 35 ba 5b 00 00 	lea    0x5bba(%rip),%rsi        # 8309 <_IO_stdin_used+0x309>
    274f:	31 c0                	xor    %eax,%eax
    2751:	bf 01 00 00 00       	mov    $0x1,%edi
    2756:	e8 45 fd ff ff       	call   24a0 <__printf_chk@plt>
    275b:	ba 01 00 00 00       	mov    $0x1,%edx
    2760:	48 8d 35 b3 5b 00 00 	lea    0x5bb3(%rip),%rsi        # 831a <_IO_stdin_used+0x31a>
    2767:	31 c0                	xor    %eax,%eax
    2769:	bf 01 00 00 00       	mov    $0x1,%edi
    276e:	e8 2d fd ff ff       	call   24a0 <__printf_chk@plt>
    2773:	ba 02 00 00 00       	mov    $0x2,%edx
    2778:	48 8d 35 b3 5b 00 00 	lea    0x5bb3(%rip),%rsi        # 8332 <_IO_stdin_used+0x332>
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
    27c0:	48 8d 35 87 5b 00 00 	lea    0x5b87(%rip),%rsi        # 834e <_IO_stdin_used+0x34e>
    27c7:	31 c0                	xor    %eax,%eax
    27c9:	bf 01 00 00 00       	mov    $0x1,%edi
    27ce:	e8 cd fc ff ff       	call   24a0 <__printf_chk@plt>
    27d3:	ba 05 00 00 00       	mov    $0x5,%edx
    27d8:	48 8d 35 89 5b 00 00 	lea    0x5b89(%rip),%rsi        # 8368 <_IO_stdin_used+0x368>
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
    2827:	48 8d 35 4e 5b 00 00 	lea    0x5b4e(%rip),%rsi        # 837c <_IO_stdin_used+0x37c>
    282e:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2833:	31 c0                	xor    %eax,%eax
    2835:	e8 66 fc ff ff       	call   24a0 <__printf_chk@plt>
    283a:	ba 0c 00 00 00       	mov    $0xc,%edx
    283f:	48 8d 35 4c 5b 00 00 	lea    0x5b4c(%rip),%rsi        # 8392 <_IO_stdin_used+0x392>
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
    29ab:	0f 84 a1 10 00 00    	je     3a52 <main+0x1402>
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
    2a40:	0f 87 35 10 00 00    	ja     3a7b <main+0x142b>
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
    2b8b:	48 8d 05 8e 17 00 00 	lea    0x178e(%rip),%rax        # 4320 <do_protected_write>
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
    2bb0:	0f 84 49 06 00 00    	je     31ff <main+0xbaf>
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
    2bdc:	0f 84 55 01 00 00    	je     2d37 <main+0x6e7>
            int group_of = b / threads_per_group;
    2be2:	44 89 eb             	mov    %r13d,%ebx
    2be5:	31 c0                	xor    %eax,%eax
    2be7:	44 89 ea             	mov    %r13d,%edx
    2bea:	bf 01 00 00 00       	mov    $0x1,%edi
    2bef:	d1 fb                	sar    %ebx
    2bf1:	48 8d 35 b4 57 00 00 	lea    0x57b4(%rip),%rsi        # 83ac <_IO_stdin_used+0x3ac>
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
              data[1].finished_reading = 1;
    2cde:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2ce9:	41 c7 44 24 f8 01 00 00 00 	movl   $0x1,-0x8(%r12)
              data[1].finished_reading = 1;
    2cf2:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2cf7:	e8 a4 f7 ff ff       	call   24a0 <__printf_chk@plt>
              data[0].messages = messages;
    2cfc:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2d01:	4c 8b 5c 24 58       	mov    0x58(%rsp),%r11
              data[0].messages_count = 0;
    2d06:	66 0f 6f 35 72 5f 00 00 	movdqa 0x5f72(%rip),%xmm6        # 8c80 <_IO_stdin_used+0xc80>
              data[1].messages = messages2;
    2d0e:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
              data[0].messages = messages;
    2d13:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2d16:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    2d1d:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    2d25:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d2d:	41 83 fd 06          	cmp    $0x6,%r13d
    2d31:	0f 85 ab fe ff ff    	jne    2be2 <main+0x592>
    2d37:	48 8b 4c 24 78       	mov    0x78(%rsp),%rcx
    2d3c:	44 89 74 24 08       	mov    %r14d,0x8(%rsp)
    2d41:	31 db                	xor    %ebx,%ebx
    2d43:	49 89 cc             	mov    %rcx,%r12
    2d46:	41 89 ee             	mov    %ebp,%r14d
    2d49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            int group_of = b / threads_per_group;
    2d50:	89 d8                	mov    %ebx,%eax
    2d52:	d1 f8                	sar    %eax
            if (k == group_of) {
    2d54:	39 44 24 08          	cmp    %eax,0x8(%rsp)
    2d58:	0f 84 58 01 00 00    	je     2eb6 <main+0x866>
    2d5e:	89 da                	mov    %ebx,%edx
    2d60:	48 8d 35 55 56 00 00 	lea    0x5655(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    2d67:	bf 01 00 00 00       	mov    $0x1,%edi
    2d6c:	31 c0                	xor    %eax,%eax
    2d6e:	e8 2d f7 ff ff       	call   24a0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d73:	be 08 00 00 00       	mov    $0x8,%esi
    2d78:	bf 01 00 00 00       	mov    $0x1,%edi
    2d7d:	e8 6e f6 ff ff       	call   23f0 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d82:	be 08 00 00 00       	mov    $0x8,%esi
    2d87:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d8c:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d91:	e8 5a f6 ff ff       	call   23f0 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    2d96:	be 80 03 00 00       	mov    $0x380,%esi
    2d9b:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2da0:	48 89 c5             	mov    %rax,%rbp
            struct Data *data = calloc(3, sizeof(struct Data));
    2da3:	e8 48 f6 ff ff       	call   23f0 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    2da8:	be 80 03 00 00       	mov    $0x380,%esi
    2dad:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    2db2:	49 89 c5             	mov    %rax,%r13
            struct Data **stack = calloc(3, sizeof(struct Data));
    2db5:	e8 36 f6 ff ff       	call   23f0 <calloc@plt>
            data[0].id = dataid++;
    2dba:	41 8d 77 01          	lea    0x1(%r15),%esi
            data[0].a = x;
    2dbe:	8b 7c 24 18          	mov    0x18(%rsp),%edi
            data[0].messages = messages;
    2dc2:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
            data[1].id = dataid++;
    2dc7:	41 89 b5 a8 06 00 00 	mov    %esi,0x6a8(%r13)
            mailboxes[b].higher = &data[1];
    2dce:	49 8d b5 80 03 00 00 	lea    0x380(%r13),%rsi
            data[0].messages_count = 0;
    2dd5:	66 0f 6f 35 a3 5e 00 00 	movdqa 0x5ea3(%rip),%xmm6        # 8c80 <_IO_stdin_used+0xc80>
            data[0].kind = MAILBOX_LOWER;
    2ddd:	41 c7 85 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r13)
            data[0].a = x;
    2de8:	41 89 bd 1c 03 00 00 	mov    %edi,0x31c(%r13)
            data[0].b = y;
    2def:	45 89 b5 20 03 00 00 	mov    %r14d,0x320(%r13)
            data[0].c = b;
    2df6:	41 89 9d 24 03 00 00 	mov    %ebx,0x324(%r13)
            data[1].kind = MAILBOX_HIGHER;
    2dfd:	41 c7 85 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r13)
            data[1].a = x;
    2e08:	41 89 bd 9c 06 00 00 	mov    %edi,0x69c(%r13)
            data[1].b = y;
    2e0f:	45 89 b5 a0 06 00 00 	mov    %r14d,0x6a0(%r13)
            data[1].c = b;
    2e16:	41 89 9d a4 06 00 00 	mov    %ebx,0x6a4(%r13)
            mailboxes[b].lower = &data[0];
    2e1d:	4d 89 2c 24          	mov    %r13,(%r12)
            mailboxes[b].my_lower = &data[0];
    2e21:	4d 89 6c 24 20       	mov    %r13,0x20(%r12)
            mailboxes[b].higher = &data[1];
    2e26:	49 89 74 24 08       	mov    %rsi,0x8(%r12)
            mailboxes[b].pending = NULL;
    2e2b:	49 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%r12)
            data[0].finished_reading = 1;
    2e34:	41 c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r13)
            data[1].finished_reading = 1;
    2e3f:	41 c7 85 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r13)
            mailboxes[b].my_higher = &data[1];
    2e4a:	49 89 74 24 28       	mov    %rsi,0x28(%r12)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2e4f:	41 c7 44 24 30 02 00 00 00 	movl   $0x2,0x30(%r12)
            stack[0] = mailboxes[b].lower;
    2e58:	4c 89 28             	mov    %r13,(%rax)
            stack[1] = mailboxes[b].higher;
    2e5b:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    2e5f:	49 89 44 24 18       	mov    %rax,0x18(%r12)
            data[0].available_sending = 0;
    2e64:	41 c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r13)
            data[0].available_receiving = 0;
    2e6f:	41 c7 85 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r13)
            data[0].messages = messages;
    2e7a:	49 89 55 00          	mov    %rdx,0x0(%r13)
            data[1].messages = messages2;
    2e7e:	49 89 ad 80 03 00 00 	mov    %rbp,0x380(%r13)
            data[1].available_sending = 1;
    2e85:	41 c7 85 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r13)
            data[1].available_receiving = 0;
    2e90:	41 c7 85 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r13)
            data[0].id = dataid++;
    2e9b:	45 89 bd 28 03 00 00 	mov    %r15d,0x328(%r13)
            data[1].id = dataid++;
    2ea2:	41 83 c7 02          	add    $0x2,%r15d
            data[0].messages_count = 0;
    2ea6:	41 0f 29 b5 80 00 00 00 	movaps %xmm6,0x80(%r13)
            data[1].messages_count = 0;
    2eae:	41 0f 29 b5 00 04 00 00 	movaps %xmm6,0x400(%r13)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2eb6:	83 c3 01             	add    $0x1,%ebx
    2eb9:	49 83 c4 38          	add    $0x38,%r12
    2ebd:	83 fb 06             	cmp    $0x6,%ebx
    2ec0:	0f 85 8a fe ff ff    	jne    2d50 <main+0x700>
          char *message = malloc(sizeof(char) * 256);
    2ec6:	be 01 00 00 00       	mov    $0x1,%esi
    2ecb:	bf 00 01 00 00       	mov    $0x100,%edi
    2ed0:	44 89 f5             	mov    %r14d,%ebp
    2ed3:	44 8b 74 24 08       	mov    0x8(%rsp),%r14d
    2ed8:	e8 13 f5 ff ff       	call   23f0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2edd:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    2ee2:	49 89 c4             	mov    %rax,%r12
          struct Message *messaged = malloc(sizeof(struct Message));
    2ee5:	e8 76 f5 ff ff       	call   2460 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2eea:	48 83 ec 08          	sub    $0x8,%rsp
    2eee:	4c 89 e7             	mov    %r12,%rdi
    2ef1:	41 89 e9             	mov    %ebp,%r9d
    2ef4:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2ef9:	48 8d 0d c0 58 00 00 	lea    0x58c0(%rip),%rcx        # 87c0 <_IO_stdin_used+0x7c0>
    2f00:	ba 00 01 00 00       	mov    $0x100,%edx
    2f05:	31 c0                	xor    %eax,%eax
    2f07:	41 56                	push   %r14
    2f09:	44 8b 44 24 28       	mov    0x28(%rsp),%r8d
    2f0e:	be 01 00 00 00       	mov    $0x1,%esi
    2f13:	e8 68 f6 ff ff       	call   2580 <__sprintf_chk@plt>
          messaged->message = message;
    2f18:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
          messaged->thread_index = thread_data[x].real_thread_index;
    2f1d:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2f22:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->task_index = y;
    2f27:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
          thread_data[x].tasks[y].group = k;
    2f2c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2f31:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].group = k;
    2f36:	48 8b 4b 38          	mov    0x38(%rbx),%rcx
          messaged->message = message;
    2f3a:	4d 89 22             	mov    %r12,(%r10)
          messaged->task_index = y;
    2f3d:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2f41:	48 63 43 08          	movslq 0x8(%rbx),%rax
          thread_data[x].tasks[y].group = k;
    2f45:	48 01 ca             	add    %rcx,%rdx
          messaged->group = k;
    2f48:	45 89 72 18          	mov    %r14d,0x18(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2f4c:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2f50:	8d 45 01             	lea    0x1(%rbp),%eax
    2f53:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].group = k;
    2f56:	44 89 b2 94 01 00 00 	mov    %r14d,0x194(%rdx)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2f5d:	c7 02 41 00 00 00    	movl   $0x41,(%rdx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2f63:	89 82 90 01 00 00    	mov    %eax,0x190(%rdx)
          thread_data[x].tasks[y].message = messaged;
    2f69:	4c 89 92 88 01 00 00 	mov    %r10,0x188(%rdx)
          thread_data[x].tasks[y].sending = 1;
    2f70:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
          thread_data[x].tasks[y].snapshot_count = 99;
    2f7a:	48 c7 82 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rdx)
          thread_data[x].tasks[y].group = k;
    2f85:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
          thread_data[x].tasks[y].snapshot_count = 99;
    2f8a:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2f8f:	e8 5c f4 ff ff       	call   23f0 <calloc@plt>
    2f94:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    2f99:	48 89 82 50 01 00 00 	mov    %rax,0x150(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2fa0:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
          thread_data[x].tasks[y].current_snapshot = 0;
    2fa5:	48 c7 82 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2fb0:	48 8b 00             	mov    (%rax),%rax
    2fb3:	8b 70 04             	mov    0x4(%rax),%esi
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2fb6:	48 39 d8             	cmp    %rbx,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2fb9:	48 89 82 28 01 00 00 	mov    %rax,0x128(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2fc0:	89 b2 30 01 00 00    	mov    %esi,0x130(%rdx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2fc6:	41 5b                	pop    %r11
    2fc8:	41 5c                	pop    %r12
    2fca:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2fcf:	0f 85 44 12 00 00    	jne    4219 <main+0x1bc9>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2fd5:	66 0f 6f 05 b3 5c 00 00 	movdqa 0x5cb3(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2fdd:	89 6a 04             	mov    %ebp,0x4(%rdx)
          thread_data[x].tasks[y].available = 1;
    2fe0:	4c 8b 25 c9 5c 00 00 	mov    0x5cc9(%rip),%r12        # 8cb0 <_IO_stdin_used+0xcb0>
          thread_data[x].tasks[y].arrived = 0;
    2fe7:	c7 82 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rdx)
          thread_data[x].tasks[y].worker_count = thread_count;
    2ff1:	c7 82 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rdx)
          thread_data[x].tasks[y].available = 1;
    2ffb:	4c 89 a2 44 01 00 00 	mov    %r12,0x144(%rdx)
          thread_data[x].tasks[y].thread_count = 2;
    3002:	0f 11 82 34 01 00 00 	movups %xmm0,0x134(%rdx)
          if (y == barrier_count - 1) {
    3009:	83 fd 01             	cmp    $0x1,%ebp
    300c:	0f 84 85 03 00 00    	je     3397 <main+0xd47>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    3012:	85 ed                	test   %ebp,%ebp
    3014:	0f 84 65 03 00 00    	je     337f <main+0xd2f>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    301a:	4c 8b 4c 24 48       	mov    0x48(%rsp),%r9
    301f:	48 8d 05 5a 36 00 00 	lea    0x365a(%rip),%rax        # 6680 <barriered_work>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3026:	bf 01 00 00 00       	mov    $0x1,%edi
               thread_data[x].tasks[y].run = barriered_work; 
    302b:	49 89 cd             	mov    %rcx,%r13
    302e:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3035:	be 08 00 00 00       	mov    $0x8,%esi
        thread_data[x].buffers_count = buffers_per_thread;
    303a:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    3045:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    304a:	e8 a1 f3 ff ff       	call   23f0 <calloc@plt>
    304f:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3054:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    3059:	66 0f 6f bc 24 a0 00 00 00 	movdqa 0xa0(%rsp),%xmm7
    for (int d = 0 ; d < threads_per_group ; d++) {
    3062:	83 44 24 20 01       	addl   $0x1,0x20(%rsp)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3067:	48 89 38             	mov    %rdi,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    306a:	48 83 c7 10          	add    $0x10,%rdi
    306e:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3075:	49 89 41 88          	mov    %rax,-0x78(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3079:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    307e:	83 44 24 70 01       	addl   $0x1,0x70(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3083:	48 8b 00             	mov    (%rax),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    3086:	48 89 7c 24 60       	mov    %rdi,0x60(%rsp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    308b:	41 c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r13)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3096:	49 89 85 28 05 00 00 	mov    %rax,0x528(%r13)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    309d:	41 c7 85 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r13)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    30a8:	41 c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r13)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    30b3:	41 8b 81 3c ff ff ff 	mov    -0xc4(%r9),%eax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    30ba:	41 0f 11 bd 18 05 00 00 	movups %xmm7,0x518(%r13)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    30c2:	41 89 85 30 05 00 00 	mov    %eax,0x530(%r13)
    for (int d = 0 ; d < threads_per_group ; d++) {
    30c9:	8b 44 24 20          	mov    0x20(%rsp),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    30cd:	41 c7 85 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r13)
        thread_data[x].tasks[barrier_count].available = 1; 
    30d8:	4d 89 a5 44 05 00 00 	mov    %r12,0x544(%r13)
    for (int d = 0 ; d < threads_per_group ; d++) {
    30df:	39 84 24 8c 00 00 00 	cmp    %eax,0x8c(%rsp)
    30e6:	0f 85 5a f8 ff ff    	jne    2946 <main+0x2f6>
    30ec:	48 8b ac 24 c0 00 00 00 	mov    0xc0(%rsp),%rbp
    30f4:	48 8b b4 24 b8 00 00 00 	mov    0xb8(%rsp),%rsi
    30fc:	45 89 f4             	mov    %r14d,%r12d
  for (int k = 0 ; k < group_count ; k++) {
    30ff:	41 83 c4 01          	add    $0x1,%r12d
    3103:	48 8b 9c 24 c8 00 00 00 	mov    0xc8(%rsp),%rbx
    310b:	48 83 c6 18          	add    $0x18,%rsi
    310f:	48 81 c5 90 01 00 00 	add    $0x190,%rbp
    3116:	41 83 fc 03          	cmp    $0x3,%r12d
    311a:	0f 85 e2 f7 ff ff    	jne    2902 <main+0x2b2>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3120:	be 08 00 00 00       	mov    $0x8,%esi
    3125:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    312a:	45 31 e4             	xor    %r12d,%r12d
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    312d:	e8 be f2 ff ff       	call   23f0 <calloc@plt>
    3132:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3137:	48 89 c5             	mov    %rax,%rbp
    313a:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    313c:	49 89 d1             	mov    %rdx,%r9
    313f:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3141:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3145:	45 85 d2             	test   %r10d,%r10d
    3148:	0f 8e 98 00 00 00    	jle    31e6 <main+0xb96>
    314e:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3152:	4d 63 c2             	movslq %r10d,%r8
    3155:	49 63 cc             	movslq %r12d,%rcx
    3158:	49 c1 e0 09          	shl    $0x9,%r8
    315c:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    3161:	49 01 f8             	add    %rdi,%r8
    3164:	0f 1f 40 00          	nopl   0x0(%rax)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3168:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    316f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3176:	48 83 c6 60          	add    $0x60,%rsi
    317a:	f3 0f 7e 61 38       	movq   0x38(%rcx),%xmm4
    317f:	f3 0f 7e 59 70       	movq   0x70(%rcx),%xmm3
    3184:	f3 0f 7e 91 a8 00 00 00 	movq   0xa8(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    318c:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3190:	f3 0f 7e 89 e0 00 00 00 	movq   0xe0(%rcx),%xmm1
    3198:	0f 16 61 40          	movhps 0x40(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    319c:	0f 16 59 78          	movhps 0x78(%rcx),%xmm3
    31a0:	f3 0f 7e 81 18 01 00 00 	movq   0x118(%rcx),%xmm0
    31a8:	0f 16 91 b0 00 00 00 	movhps 0xb0(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    31af:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    31b3:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    31b7:	0f 16 89 e8 00 00 00 	movhps 0xe8(%rcx),%xmm1
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    31be:	0f 16 81 20 01 00 00 	movhps 0x120(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    31c5:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    31c9:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    31cd:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    31d1:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    31d5:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    31d9:	49 39 f8             	cmp    %rdi,%r8
    31dc:	75 8a                	jne    3168 <main+0xb18>
    31de:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    31e2:	45 8d 24 8c          	lea    (%r12,%rcx,4),%r12d
    for (int d = 0 ; d < threads_per_group ; d++) {
    31e6:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
    31ed:	85 db                	test   %ebx,%ebx
    31ef:	0f 85 b0 01 00 00    	jne    33a5 <main+0xd55>
    31f5:	bb 01 00 00 00       	mov    $0x1,%ebx
    31fa:	e9 42 ff ff ff       	jmp    3141 <main+0xaf1>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    31ff:	45 89 ec             	mov    %r13d,%r12d
    3202:	48 89 4c 24 68       	mov    %rcx,0x68(%rsp)
    3207:	49 89 cd             	mov    %rcx,%r13
    320a:	eb 16                	jmp    3222 <main+0xbd2>
    320c:	0f 1f 40 00          	nopl   0x0(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3210:	41 83 c4 01          	add    $0x1,%r12d
    3214:	49 83 c5 38          	add    $0x38,%r13
    3218:	41 83 fc 06          	cmp    $0x6,%r12d
    321c:	0f 84 53 01 00 00    	je     3375 <main+0xd25>
            int group_of = b / threads_per_group;
    3222:	44 89 e3             	mov    %r12d,%ebx
    3225:	31 c0                	xor    %eax,%eax
    3227:	44 89 e2             	mov    %r12d,%edx
    322a:	bf 01 00 00 00       	mov    $0x1,%edi
    322f:	d1 fb                	sar    %ebx
    3231:	48 8d 35 74 51 00 00 	lea    0x5174(%rip),%rsi        # 83ac <_IO_stdin_used+0x3ac>
    3238:	89 d9                	mov    %ebx,%ecx
    323a:	e8 61 f2 ff ff       	call   24a0 <__printf_chk@plt>
            if (k == group_of) {
    323f:	41 39 de             	cmp    %ebx,%r14d
    3242:	75 cc                	jne    3210 <main+0xbc0>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3244:	be 08 00 00 00       	mov    $0x8,%esi
    3249:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    324e:	49 83 c5 38          	add    $0x38,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3252:	e8 99 f1 ff ff       	call   23f0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3257:	be 08 00 00 00       	mov    $0x8,%esi
    325c:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3261:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3266:	e8 85 f1 ff ff       	call   23f0 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    326b:	be 80 03 00 00       	mov    $0x380,%esi
    3270:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3275:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    327a:	e8 71 f1 ff ff       	call   23f0 <calloc@plt>
              data[0].a = x;
    327f:	8b 7c 24 18          	mov    0x18(%rsp),%edi
              mailboxes[b].pending = NULL;
    3283:	49 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%r13)
    328b:	44 89 e2             	mov    %r12d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
    328e:	49 89 c1             	mov    %rax,%r9
              data[0].c = b;
    3291:	44 89 a0 24 03 00 00 	mov    %r12d,0x324(%rax)
    3298:	48 8d 35 f9 54 00 00 	lea    0x54f9(%rip),%rsi        # 8798 <_IO_stdin_used+0x798>
              data[0].a = x;
    329f:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].kind = MAILBOX_LOWER;
    32a5:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].b = y;
    32af:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].id = dataid++;
    32b5:	41 8d 47 01          	lea    0x1(%r15),%eax
              data[1].id = dataid++;
    32b9:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    32c0:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    32c7:	49 89 45 d0          	mov    %rax,-0x30(%r13)
    32cb:	8b 84 24 88 00 00 00 	mov    0x88(%rsp),%eax
              data[0].id = dataid++;
    32d2:	45 89 b9 28 03 00 00 	mov    %r15d,0x328(%r9)
              data[1].id = dataid++;
    32d9:	41 83 c7 02          	add    $0x2,%r15d
              data[1].a = x;
    32dd:	41 89 b9 9c 06 00 00 	mov    %edi,0x69c(%r9)
    32e4:	89 c1                	mov    %eax,%ecx
    32e6:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].c = b;
    32eb:	45 89 a1 a4 06 00 00 	mov    %r12d,0x6a4(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    32f2:	41 83 c4 01          	add    $0x1,%r12d
              mailboxes[b].lower = &data[0];
    32f6:	4d 89 4d c8          	mov    %r9,-0x38(%r13)
    32fa:	41 89 45 fc          	mov    %eax,-0x4(%r13)
    32fe:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    3300:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].b = y;
    330b:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[0].finished_reading = 1;
    3312:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    331d:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].kind = MAILBOX_FRIEND;
    3328:	41 c7 45 f8 01 00 00 00 	movl   $0x1,-0x8(%r13)
              data[1].finished_reading = 1;
    3330:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    3335:	e8 66 f1 ff ff       	call   24a0 <__printf_chk@plt>
              data[0].messages = messages;
    333a:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    333f:	4c 8b 5c 24 58       	mov    0x58(%rsp),%r11
              data[0].messages_count = 0;
    3344:	66 0f 6f 35 34 59 00 00 	movdqa 0x5934(%rip),%xmm6        # 8c80 <_IO_stdin_used+0xc80>
              data[1].messages = messages2;
    334c:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
              data[0].messages = messages;
    3351:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    3354:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    335b:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    3363:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    336b:	41 83 fc 06          	cmp    $0x6,%r12d
    336f:	0f 85 ad fe ff ff    	jne    3222 <main+0xbd2>
    3375:	48 8b 4c 24 68       	mov    0x68(%rsp),%rcx
    337a:	e9 bd f9 ff ff       	jmp    2d3c <main+0x6ec>
    337f:	48 8d 05 4a 38 00 00 	lea    0x384a(%rip),%rax        # 6bd0 <barriered_work_ingest_andwork>
    3386:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    338b:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    3392:	e9 d2 f7 ff ff       	jmp    2b69 <main+0x519>
    3397:	48 8d 05 e2 32 00 00 	lea    0x32e2(%rip),%rax        # 6680 <barriered_work>
    339e:	bd 02 00 00 00       	mov    $0x2,%ebp
    33a3:	eb e6                	jmp    338b <main+0xd3b>
  for (int k = 0 ; k < group_count ; k++) {
    33a5:	83 c0 02             	add    $0x2,%eax
    33a8:	48 81 c2 90 01 00 00 	add    $0x190,%rdx
    33af:	83 f8 06             	cmp    $0x6,%eax
    33b2:	0f 85 84 fd ff ff    	jne    313c <main+0xaec>
    33b8:	48 8d 3d 1b 50 00 00 	lea    0x501b(%rip),%rdi        # 83da <_IO_stdin_used+0x3da>
    33bf:	e8 5c ef ff ff       	call   2320 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    33c4:	48 8d 35 24 50 00 00 	lea    0x5024(%rip),%rsi        # 83ef <_IO_stdin_used+0x3ef>
    33cb:	48 8d 3d 1f 50 00 00 	lea    0x501f(%rip),%rdi        # 83f1 <_IO_stdin_used+0x3f1>
    33d2:	e8 09 f1 ff ff       	call   24e0 <fopen@plt>
    33d7:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas_size; x++) {
    33da:	45 85 e4             	test   %r12d,%r12d
    33dd:	7e 7a                	jle    3459 <main+0xe09>
    33df:	48 8d 05 2c 50 00 00 	lea    0x502c(%rip),%rax        # 8412 <_IO_stdin_used+0x412>
    33e6:	4d 63 e4             	movslq %r12d,%r12
    33e9:	49 89 ed             	mov    %rbp,%r13
    33ec:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    33f1:	4a 8d 6c e5 00       	lea    0x0(%rbp,%r12,8),%rbp
    33f6:	4c 8d 35 d1 4f 00 00 	lea    0x4fd1(%rip),%r14        # 83ce <_IO_stdin_used+0x3ce>
    char * c = calloc(250, sizeof(char));
    33fd:	be 01 00 00 00       	mov    $0x1,%esi
    3402:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    3407:	49 83 c5 08          	add    $0x8,%r13
    char * c = calloc(250, sizeof(char));
    340b:	e8 e0 ef ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3410:	4c 89 f1             	mov    %r14,%rcx
    3413:	ba fa 00 00 00       	mov    $0xfa,%edx
    3418:	be 01 00 00 00       	mov    $0x1,%esi
    341d:	49 89 c4             	mov    %rax,%r12
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    3420:	49 8b 45 f8          	mov    -0x8(%r13),%rax
    3424:	4c 89 e7             	mov    %r12,%rdi
    3427:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    342e:	31 c0                	xor    %eax,%eax
    3430:	e8 4b f1 ff ff       	call   2580 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3435:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    343a:	4c 89 e2             	mov    %r12,%rdx
    343d:	31 c0                	xor    %eax,%eax
    343f:	bf 01 00 00 00       	mov    $0x1,%edi
    3444:	e8 57 f0 ff ff       	call   24a0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3449:	4c 89 fe             	mov    %r15,%rsi
    344c:	4c 89 e7             	mov    %r12,%rdi
    344f:	e8 5c ef ff ff       	call   23b0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    3454:	4c 39 ed             	cmp    %r13,%rbp
    3457:	75 a4                	jne    33fd <main+0xdad>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    3459:	4c 89 ff             	mov    %r15,%rdi

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    345c:	31 ed                	xor    %ebp,%ebp
    345e:	4c 8d 35 d7 4f 00 00 	lea    0x4fd7(%rip),%r14        # 843c <_IO_stdin_used+0x43c>
  fclose(m1);
    3465:	e8 e6 ee ff ff       	call   2350 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    346a:	48 8d 3d 89 4f 00 00 	lea    0x4f89(%rip),%rdi        # 83fa <_IO_stdin_used+0x3fa>
    3471:	41 89 ec             	mov    %ebp,%r12d
    3474:	e8 a7 ee ff ff       	call   2320 <puts@plt>
    3479:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    347e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3483:	44 89 e2             	mov    %r12d,%edx
    3486:	48 8d 35 88 4f 00 00 	lea    0x4f88(%rip),%rsi        # 8415 <_IO_stdin_used+0x415>
    348d:	31 c0                	xor    %eax,%eax
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    348f:	45 31 ed             	xor    %r13d,%r13d
    3492:	bf 01 00 00 00       	mov    $0x1,%edi
    3497:	47 8d 3c 24          	lea    (%r12,%r12,1),%r15d
    349b:	e8 00 f0 ff ff       	call   24a0 <__printf_chk@plt>
    34a0:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    34a5:	44 89 7c 24 10       	mov    %r15d,0x10(%rsp)
    34aa:	44 89 e8             	mov    %r13d,%eax
    34ad:	49 89 ed             	mov    %rbp,%r13
    34b0:	89 dd                	mov    %ebx,%ebp
    34b2:	89 c3                	mov    %eax,%ebx
      int x = (k * threads_per_group) + d;
    34b4:	8b 44 24 10          	mov    0x10(%rsp),%eax
    34b8:	89 da                	mov    %ebx,%edx
    34ba:	48 8d 35 5e 4f 00 00 	lea    0x4f5e(%rip),%rsi        # 841f <_IO_stdin_used+0x41f>
    34c1:	45 31 ff             	xor    %r15d,%r15d
    34c4:	bf 01 00 00 00       	mov    $0x1,%edi
    34c9:	8d 0c 03             	lea    (%rbx,%rax,1),%ecx
    34cc:	31 c0                	xor    %eax,%eax
    34ce:	e8 cd ef ff ff       	call   24a0 <__printf_chk@plt>
    34d3:	89 6c 24 18          	mov    %ebp,0x18(%rsp)
    34d7:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
    34dc:	89 5c 24 28          	mov    %ebx,0x28(%rsp)
    34e0:	44 89 fa             	mov    %r15d,%edx
    34e3:	48 8d 35 47 4f 00 00 	lea    0x4f47(%rip),%rsi        # 8431 <_IO_stdin_used+0x431>
    34ea:	31 c0                	xor    %eax,%eax
    34ec:	4c 89 fb             	mov    %r15,%rbx
    34ef:	bf 01 00 00 00       	mov    $0x1,%edi
    34f4:	48 c1 e3 09          	shl    $0x9,%rbx
    34f8:	45 31 e4             	xor    %r12d,%r12d
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    34fb:	31 ed                	xor    %ebp,%ebp
    34fd:	e8 9e ef ff ff       	call   24a0 <__printf_chk@plt>
    3502:	eb 2e                	jmp    3532 <main+0xee2>
    3504:	0f 1f 40 00          	nopl   0x0(%rax)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    3508:	83 fa 01             	cmp    $0x1,%edx
    350b:	0f 84 91 00 00 00    	je     35a2 <main+0xf52>
    3511:	44 8b 40 34          	mov    0x34(%rax),%r8d
    3515:	89 ea                	mov    %ebp,%edx
    3517:	4c 89 f6             	mov    %r14,%rsi
    351a:	bf 01 00 00 00       	mov    $0x1,%edi
    351f:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3521:	83 c5 01             	add    $0x1,%ebp
    3524:	49 83 c4 38          	add    $0x38,%r12
    3528:	e8 73 ef ff ff       	call   24a0 <__printf_chk@plt>
    352d:	83 fd 06             	cmp    $0x6,%ebp
    3530:	74 43                	je     3575 <main+0xf25>
          char * mailbox_kind = calloc(100, sizeof(char));
    3532:	be 01 00 00 00       	mov    $0x1,%esi
    3537:	bf 64 00 00 00       	mov    $0x64,%edi
    353c:	e8 af ee ff ff       	call   23f0 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3541:	49 8b 75 38          	mov    0x38(%r13),%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
    3545:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3548:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    3550:	4c 01 e0             	add    %r12,%rax
    3553:	8b 50 30             	mov    0x30(%rax),%edx
    3556:	83 fa 02             	cmp    $0x2,%edx
    3559:	75 ad                	jne    3508 <main+0xeb8>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    355b:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    3565:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    3568:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    3570:	4c 01 e0             	add    %r12,%rax
    3573:	eb 9c                	jmp    3511 <main+0xec1>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3575:	49 83 c7 01          	add    $0x1,%r15
    3579:	49 83 ff 03          	cmp    $0x3,%r15
    357d:	0f 85 5d ff ff ff    	jne    34e0 <main+0xe90>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3583:	8b 5c 24 28          	mov    0x28(%rsp),%ebx
    3587:	8b 6c 24 18          	mov    0x18(%rsp),%ebp
    358b:	49 81 c5 c8 00 00 00 	add    $0xc8,%r13
    3592:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    3597:	85 db                	test   %ebx,%ebx
    3599:	75 24                	jne    35bf <main+0xf6f>
    359b:	89 eb                	mov    %ebp,%ebx
    359d:	e9 12 ff ff ff       	jmp    34b4 <main+0xe64>
    35a2:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    35a8:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    35af:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    35b7:	4c 01 e0             	add    %r12,%rax
    35ba:	e9 52 ff ff ff       	jmp    3511 <main+0xec1>
  for (int k = 0 ; k < group_count ; k++) {
    35bf:	48 81 44 24 08 90 01 00 00 	addq   $0x190,0x8(%rsp)
    35c8:	41 83 c4 01          	add    $0x1,%r12d
    35cc:	41 89 dd             	mov    %ebx,%r13d
    35cf:	89 eb                	mov    %ebp,%ebx
    35d1:	41 83 fc 03          	cmp    $0x3,%r12d
    35d5:	0f 85 a8 fe ff ff    	jne    3483 <main+0xe33>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    35db:	ba 07 00 00 00       	mov    $0x7,%edx
    35e0:	bf 01 00 00 00       	mov    $0x1,%edi
    35e5:	31 c0                	xor    %eax,%eax
    35e7:	45 89 ec             	mov    %r13d,%r12d
    35ea:	48 8d 35 66 4e 00 00 	lea    0x4e66(%rip),%rsi        # 8457 <_IO_stdin_used+0x457>
    35f1:	e8 aa ee ff ff       	call   24a0 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    35f6:	be 08 00 00 00       	mov    $0x8,%esi
    35fb:	bf 02 00 00 00       	mov    $0x2,%edi
    3600:	e8 eb ed ff ff       	call   23f0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    3605:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    360a:	be 38 00 00 00       	mov    $0x38,%esi
    360f:	bf 0a 00 00 00       	mov    $0xa,%edi
    my_thread_data[0] = &thread_data[x]; 
    3614:	4c 8d b5 78 05 00 00 	lea    0x578(%rbp),%r14
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    361b:	48 89 68 08          	mov    %rbp,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    361f:	4c 8d ad c8 00 00 00 	lea    0xc8(%rbp),%r13
    thread_data[x].threads = my_thread_data;
    3626:	48 89 85 90 05 00 00 	mov    %rax,0x590(%rbp)
    my_thread_data[0] = &thread_data[x]; 
    362d:	4c 89 30             	mov    %r14,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3630:	48 8b 45 38          	mov    0x38(%rbp),%rax
    thread_data[x].thread_count = 2;
    3634:	c7 85 a0 05 00 00 02 00 00 00 	movl   $0x2,0x5a0(%rbp)
    thread_data[x].thread_index = 0;
    363e:	c7 85 7c 05 00 00 00 00 00 00 	movl   $0x0,0x57c(%rbp)
    thread_data[x].task_count = total_barrier_count;
    3648:	c7 85 b8 05 00 00 03 00 00 00 	movl   $0x3,0x5b8(%rbp)
    thread_data[n].tasks[0].scheduled = 1;
    3652:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    365c:	48 8b 85 00 01 00 00 	mov    0x100(%rbp),%rax
    3663:	4c 89 6c 24 08       	mov    %r13,0x8(%rsp)
    3668:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3672:	e8 79 ed ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3677:	be 38 00 00 00       	mov    $0x38,%esi
    367c:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3681:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3686:	e8 65 ed ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    368b:	be 38 00 00 00       	mov    $0x38,%esi
    3690:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3695:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3698:	e8 53 ed ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    369d:	be 38 00 00 00       	mov    $0x38,%esi
    36a2:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    36a7:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    36ac:	e8 3f ed ff ff       	call   23f0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    36b1:	be 08 00 00 00       	mov    $0x8,%esi
    36b6:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    36bb:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    36c0:	e8 2b ed ff ff       	call   23f0 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    36c5:	be 08 00 00 00       	mov    $0x8,%esi
    36ca:	bf 0a 00 00 00       	mov    $0xa,%edi
  thread_data[timer_threadi].type = TIMER;
    36cf:	c7 85 bc 04 00 00 00 00 00 00 	movl   $0x0,0x4bc(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    36d9:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    36dc:	48 8b 05 d5 55 00 00 	mov    0x55d5(%rip),%rax        # 8cb8 <_IO_stdin_used+0xcb8>
    36e3:	48 89 85 f0 04 00 00 	mov    %rax,0x4f0(%rbp)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    36ea:	e8 01 ed ff ff       	call   23f0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    36ef:	48 8d 95 90 01 00 00 	lea    0x190(%rbp),%rdx
    36f6:	bf 01 00 00 00       	mov    $0x1,%edi
    36fb:	48 8d 8d b0 04 00 00 	lea    0x4b0(%rbp),%rcx
    3702:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3706:	48 8d 95 58 02 00 00 	lea    0x258(%rbp),%rdx
    370d:	48 8d 35 52 4d 00 00 	lea    0x4d52(%rip),%rsi        # 8466 <_IO_stdin_used+0x466>
    3714:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3718:	48 8d 95 20 03 00 00 	lea    0x320(%rbp),%rdx
    371f:	48 89 50 20          	mov    %rdx,0x20(%rax)
    3723:	48 8d 95 e8 03 00 00 	lea    0x3e8(%rbp),%rdx
    372a:	4c 89 68 08          	mov    %r13,0x8(%rax)
    372e:	4c 8d ad 40 06 00 00 	lea    0x640(%rbp),%r13
    3735:	48 89 50 28          	mov    %rdx,0x28(%rax)
    3739:	48 8d 95 08 07 00 00 	lea    0x708(%rbp),%rdx
    3740:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3744:	4c 89 70 38          	mov    %r14,0x38(%rax)
    3748:	48 89 50 48          	mov    %rdx,0x48(%rax)
    374c:	ba 06 00 00 00       	mov    $0x6,%edx
    3751:	48 89 28             	mov    %rbp,(%rax)
    3754:	4c 89 68 40          	mov    %r13,0x40(%rax)
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3758:	48 89 85 c8 04 00 00 	mov    %rax,0x4c8(%rbp)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    375f:	48 8b 05 5a 55 00 00 	mov    0x555a(%rip),%rax        # 8cc0 <_IO_stdin_used+0xcc0>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3766:	c7 85 e0 04 00 00 06 00 00 00 	movl   $0x6,0x4e0(%rbp)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3770:	48 89 85 d8 04 00 00 	mov    %rax,0x4d8(%rbp)
    3777:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    3779:	c7 85 b4 04 00 00 00 00 00 00 	movl   $0x0,0x4b4(%rbp)
    my_thread_data[n] = &thread_data[n]; 
    3783:	48 89 4c 24 28       	mov    %rcx,0x28(%rsp)
    3788:	e8 13 ed ff ff       	call   24a0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    378d:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3792:	49 8d b7 50 01 00 00 	lea    0x150(%r15),%rsi
  for (int k = 0 ; k < group_count ; k++) {
    3799:	45 31 ff             	xor    %r15d,%r15d
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    379c:	48 8d 15 3d 0d 00 00 	lea    0xd3d(%rip),%rdx        # 44e0 <timer_thread>
    37a3:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    37a7:	e8 14 ed ff ff       	call   24c0 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    37ac:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    37b1:	48 89 d9             	mov    %rbx,%rcx
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    37b4:	48 89 ea             	mov    %rbp,%rdx
    37b7:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    37bc:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    37c2:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    37c7:	4c 89 6c 24 40       	mov    %r13,0x40(%rsp)
    37cc:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    37d1:	45 89 d6             	mov    %r10d,%r14d
    for (int d = 0 ; d < threads_per_group ; d++) {
    37d4:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    37d9:	47 8d 24 3f          	lea    (%r15,%r15,1),%r12d
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    37dd:	49 89 c5             	mov    %rax,%r13
    37e0:	48 89 cb             	mov    %rcx,%rbx
    37e3:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    37e8:	48 89 d5             	mov    %rdx,%rbp
    37eb:	48 89 54 24 58       	mov    %rdx,0x58(%rsp)
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    37f0:	c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%rbp)
    37f7:	44 89 e2             	mov    %r12d,%edx
    37fa:	44 89 f9             	mov    %r15d,%ecx
    37fd:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    37ff:	c7 45 44 01 00 00 00 	movl   $0x1,0x44(%rbp)
    3806:	48 8d 35 e3 4f 00 00 	lea    0x4fe3(%rip),%rsi        # 87f0 <_IO_stdin_used+0x7f0>
    380d:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    3812:	41 83 c4 01          	add    $0x1,%r12d
    3816:	e8 85 ec ff ff       	call   24a0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    381b:	48 89 e9             	mov    %rbp,%rcx
    381e:	4c 89 ee             	mov    %r13,%rsi
    3821:	48 89 df             	mov    %rbx,%rdi
    3824:	48 8d 15 b5 27 00 00 	lea    0x27b5(%rip),%rdx        # 5fe0 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    382b:	48 81 c5 c8 00 00 00 	add    $0xc8,%rbp
    3832:	48 83 c3 08          	add    $0x8,%rbx
    3836:	49 83 c5 38          	add    $0x38,%r13
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    383a:	e8 81 ec ff ff       	call   24c0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    383f:	48 8b 55 e8          	mov    -0x18(%rbp),%rdx
    3843:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    3847:	be 08 00 00 00       	mov    $0x8,%esi
    384c:	e8 bf ea ff ff       	call   2310 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3851:	45 39 e6             	cmp    %r12d,%r14d
    3854:	75 9a                	jne    37f0 <main+0x11a0>
  for (int k = 0 ; k < group_count ; k++) {
    3856:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    385b:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    3860:	41 83 c7 01          	add    $0x1,%r15d
    3864:	41 83 c6 02          	add    $0x2,%r14d
    3868:	48 8b 54 24 58       	mov    0x58(%rsp),%rdx
    386d:	48 83 c1 10          	add    $0x10,%rcx
    3871:	48 83 c0 70          	add    $0x70,%rax
    3875:	48 81 c2 90 01 00 00 	add    $0x190,%rdx
    387c:	41 83 ff 03          	cmp    $0x3,%r15d
    3880:	0f 85 4e ff ff ff    	jne    37d4 <main+0x1184>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    3886:	4c 8b 7c 24 38       	mov    0x38(%rsp),%r15
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    388b:	be d8 00 00 00       	mov    $0xd8,%esi
    3890:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3895:	48 8b 05 2c 54 00 00 	mov    0x542c(%rip),%rax        # 8cc8 <_IO_stdin_used+0xcc8>
    thread_data[x].type = IO;
    389c:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    38a1:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
    38a6:	41 c7 87 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r15)
    38b1:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    thread_data[x].task_count = 0;
    38b6:	49 89 87 b8 05 00 00 	mov    %rax,0x5b8(%r15)
    thread_data[x].type = IO;
    38bd:	4c 8b 6c 24 40       	mov    0x40(%rsp),%r13
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    38c2:	e8 29 eb ff ff       	call   23f0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    38c7:	be 00 08 00 00       	mov    $0x800,%esi
    38cc:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    38ce:	49 89 87 d0 05 00 00 	mov    %rax,0x5d0(%r15)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    38d5:	e8 36 ec ff ff       	call   2510 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    38da:	be 08 00 00 00       	mov    $0x8,%esi
    38df:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    38e4:	41 89 87 d8 05 00 00 	mov    %eax,0x5d8(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    38eb:	e8 00 eb ff ff       	call   23f0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    38f0:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    38f5:	41 c7 87 a0 05 00 00 02 00 00 00 	movl   $0x2,0x5a0(%r15)
    3900:	ba 07 00 00 00       	mov    $0x7,%edx
      my_thread_data[n] = &thread_data[n]; 
    3905:	4c 89 38             	mov    %r15,(%rax)
    3908:	48 8d 35 75 4b 00 00 	lea    0x4b75(%rip),%rsi        # 8484 <_IO_stdin_used+0x484>
    390f:	48 89 78 08          	mov    %rdi,0x8(%rax)
    3913:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].threads = my_thread_data;
    3918:	49 89 87 90 05 00 00 	mov    %rax,0x590(%r15)
    391f:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3921:	41 c7 87 7c 05 00 00 07 00 00 00 	movl   $0x7,0x57c(%r15)
    392c:	4d 89 ef             	mov    %r13,%r15
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    392f:	41 bd 08 00 00 00    	mov    $0x8,%r13d
    3935:	e8 66 eb ff ff       	call   24a0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    393a:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    393f:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3943:	4c 89 f1             	mov    %r14,%rcx
    3946:	48 8d 15 a3 1e 00 00 	lea    0x1ea3(%rip),%rdx        # 57f0 <io_thread>
    394d:	4c 8d 73 40          	lea    0x40(%rbx),%r14
    3951:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3958:	e8 63 eb ff ff       	call   24c0 <pthread_create@plt>
    395d:	ba 08 00 00 00       	mov    $0x8,%edx
    3962:	48 8d 35 32 4b 00 00 	lea    0x4b32(%rip),%rsi        # 849b <_IO_stdin_used+0x49b>
    3969:	31 c0                	xor    %eax,%eax
    396b:	bf 01 00 00 00       	mov    $0x1,%edi
    3970:	e8 2b eb ff ff       	call   24a0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3975:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    397a:	44 89 e0             	mov    %r12d,%eax
    397d:	49 89 dc             	mov    %rbx,%r12
    3980:	89 c3                	mov    %eax,%ebx
    3982:	48 81 c5 c0 01 00 00 	add    $0x1c0,%rbp
    3989:	44 89 ea             	mov    %r13d,%edx
    398c:	48 8d 35 1e 4b 00 00 	lea    0x4b1e(%rip),%rsi        # 84b1 <_IO_stdin_used+0x4b1>
    3993:	bf 01 00 00 00       	mov    $0x1,%edi
    3998:	31 c0                	xor    %eax,%eax
    399a:	e8 01 eb ff ff       	call   24a0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    399f:	be 08 00 00 00       	mov    $0x8,%esi
    39a4:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    39a9:	48 8b 05 18 53 00 00 	mov    0x5318(%rip),%rax        # 8cc8 <_IO_stdin_used+0xcc8>
    thread_data[x].type = EXTERNAL;
    39b0:	41 c7 47 0c 03 00 00 00 	movl   $0x3,0xc(%r15)
    thread_data[x].task_count = 0;
    39b8:	49 89 47 40          	mov    %rax,0x40(%r15)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    39bc:	e8 2f ea ff ff       	call   23f0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    39c1:	48 8b bc 24 98 00 00 00 	mov    0x98(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    39c9:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    39ce:	41 c7 87 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r15)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    39d9:	49 89 47 50          	mov    %rax,0x50(%r15)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    39dd:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    39e0:	bf 02 00 00 00       	mov    $0x2,%edi
    39e5:	e8 06 ea ff ff       	call   23f0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    39ea:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    39ef:	4c 89 f9             	mov    %r15,%rcx
    39f2:	4c 89 f7             	mov    %r14,%rdi
    thread_data[x].threads = my_thread_data;
    39f5:	49 89 47 18          	mov    %rax,0x18(%r15)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    39f9:	48 8d 15 d0 09 00 00 	lea    0x9d0(%rip),%rdx        # 43d0 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a00:	49 83 c6 08          	add    $0x8,%r14
    3a04:	49 81 c7 c8 00 00 00 	add    $0xc8,%r15
      my_thread_data[n] = &thread_data[n]; 
    3a0b:	48 89 30             	mov    %rsi,(%rax)
    3a0e:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    thread_data[x].thread_index = x;
    3a13:	45 89 af 3c ff ff ff 	mov    %r13d,-0xc4(%r15)
      my_thread_data[n] = &thread_data[n]; 
    3a1a:	48 89 70 08          	mov    %rsi,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3a1e:	48 8b 05 83 52 00 00 	mov    0x5283(%rip),%rax        # 8ca8 <_IO_stdin_used+0xca8>
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3a25:	48 89 ee             	mov    %rbp,%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a28:	48 83 c5 38          	add    $0x38,%rbp
    thread_data[x].thread_count = thread_count;
    3a2c:	49 89 87 60 ff ff ff 	mov    %rax,-0xa0(%r15)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3a33:	e8 88 ea ff ff       	call   24c0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a38:	48 83 84 24 98 00 00 00 10 	addq   $0x10,0x98(%rsp)
    3a41:	41 83 fd 08          	cmp    $0x8,%r13d
    3a45:	75 41                	jne    3a88 <main+0x1438>
    3a47:	41 bd 09 00 00 00    	mov    $0x9,%r13d
    3a4d:	e9 37 ff ff ff       	jmp    3989 <main+0x1339>
        other = (x + 1) % total_threads;
    3a52:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
        my_thread_data[1] = &thread_data[other]; 
    3a57:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3a5c:	48 89 5c 24 40       	mov    %rbx,0x40(%rsp)
    3a61:	45 31 c0             	xor    %r8d,%r8d
    3a64:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
        other = (x + 1) % total_threads;
    3a68:	45 89 e5             	mov    %r12d,%r13d
        my_thread_data[1] = &thread_data[other]; 
    3a6b:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3a6f:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
        my_thread_data[0] = &thread_data[x]; 
    3a73:	4c 89 c8             	mov    %r9,%rax
    3a76:	e9 5b ef ff ff       	jmp    29d6 <main+0x386>
            CPU_SET(j, sendercpu);
    3a7b:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
          for (int j = 0 ; j < cores ; j++) {
    3a83:	e9 e6 ef ff ff       	jmp    2a6e <main+0x41e>
    3a88:	89 d8                	mov    %ebx,%eax
    3a8a:	4c 89 e3             	mov    %r12,%rbx
    3a8d:	48 8d 2d 3a 4a 00 00 	lea    0x4a3a(%rip),%rbp        # 84ce <_IO_stdin_used+0x4ce>
    3a94:	41 89 c4             	mov    %eax,%r12d
    3a97:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3a9c:	4c 8d 70 04          	lea    0x4(%rax),%r14
    3aa0:	4c 8d a8 d4 07 00 00 	lea    0x7d4(%rax),%r13
    3aa7:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    3aab:	41 8b 16             	mov    (%r14),%edx
    3aae:	48 89 ee             	mov    %rbp,%rsi
    3ab1:	bf 01 00 00 00       	mov    $0x1,%edi
    3ab6:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3ab8:	49 81 c6 c8 00 00 00 	add    $0xc8,%r14
    3abf:	e8 dc e9 ff ff       	call   24a0 <__printf_chk@plt>
    3ac4:	4d 39 f5             	cmp    %r14,%r13
    3ac7:	75 de                	jne    3aa7 <main+0x1457>
    3ac9:	48 8d 3d 11 4a 00 00 	lea    0x4a11(%rip),%rdi        # 84e1 <_IO_stdin_used+0x4e1>
    3ad0:	45 31 f6             	xor    %r14d,%r14d
    3ad3:	4c 8d ac 24 d0 00 00 00 	lea    0xd0(%rsp),%r13
    3adb:	e8 40 e8 ff ff       	call   2320 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3ae0:	48 8d 2d 18 4a 00 00 	lea    0x4a18(%rip),%rbp        # 84ff <_IO_stdin_used+0x4ff>
    void * result; 
    pthread_join(thread[x], &result);
    3ae7:	4a 8b 3c f3          	mov    (%rbx,%r14,8),%rdi
    3aeb:	4c 89 ee             	mov    %r13,%rsi
    3aee:	e8 5d ea ff ff       	call   2550 <pthread_join@plt>
    3af3:	44 89 f2             	mov    %r14d,%edx
    3af6:	48 89 ee             	mov    %rbp,%rsi
    3af9:	bf 01 00 00 00       	mov    $0x1,%edi
    3afe:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3b00:	49 83 c6 01          	add    $0x1,%r14
    3b04:	e8 97 e9 ff ff       	call   24a0 <__printf_chk@plt>
    3b09:	49 83 fe 0a          	cmp    $0xa,%r14
    3b0d:	75 d8                	jne    3ae7 <main+0x1497>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3b0f:	be 08 00 00 00       	mov    $0x8,%esi
    3b14:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    3b19:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3b1b:	e8 d0 e8 ff ff       	call   23f0 <calloc@plt>
    3b20:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3b25:	49 89 c7             	mov    %rax,%r15
    3b28:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3b2a:	49 89 d1             	mov    %rdx,%r9
    3b2d:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3b30:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3b34:	45 85 d2             	test   %r10d,%r10d
    3b37:	0f 8e 98 00 00 00    	jle    3bd5 <main+0x1585>
    3b3d:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3b41:	4d 63 c2             	movslq %r10d,%r8
    3b44:	48 63 cb             	movslq %ebx,%rcx
    3b47:	49 c1 e0 09          	shl    $0x9,%r8
    3b4b:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    3b4f:	49 01 f8             	add    %rdi,%r8
    3b52:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3b58:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3b5f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3b66:	48 83 c6 60          	add    $0x60,%rsi
    3b6a:	f3 0f 7e 61 38       	movq   0x38(%rcx),%xmm4
    3b6f:	f3 0f 7e 59 70       	movq   0x70(%rcx),%xmm3
    3b74:	f3 0f 7e 91 a8 00 00 00 	movq   0xa8(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3b7c:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3b80:	f3 0f 7e 89 e0 00 00 00 	movq   0xe0(%rcx),%xmm1
    3b88:	0f 16 61 40          	movhps 0x40(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3b8c:	0f 16 59 78          	movhps 0x78(%rcx),%xmm3
    3b90:	f3 0f 7e 81 18 01 00 00 	movq   0x118(%rcx),%xmm0
    3b98:	0f 16 91 b0 00 00 00 	movhps 0xb0(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3b9f:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    3ba3:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3ba7:	0f 16 89 e8 00 00 00 	movhps 0xe8(%rcx),%xmm1
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3bae:	0f 16 81 20 01 00 00 	movhps 0x120(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3bb5:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3bb9:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3bbd:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3bc1:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3bc5:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3bc9:	4c 39 c7             	cmp    %r8,%rdi
    3bcc:	75 8a                	jne    3b58 <main+0x1508>
    3bce:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3bd2:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    3bd5:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
    3bdc:	45 85 db             	test   %r11d,%r11d
    3bdf:	75 08                	jne    3be9 <main+0x1599>
    3be1:	45 89 e3             	mov    %r12d,%r11d
    3be4:	e9 47 ff ff ff       	jmp    3b30 <main+0x14e0>
  for (int k = 0 ; k < group_count ; k++) {
    3be9:	83 c0 02             	add    $0x2,%eax
    3bec:	48 81 c2 90 01 00 00 	add    $0x190,%rdx
    3bf3:	83 f8 06             	cmp    $0x6,%eax
    3bf6:	0f 85 2e ff ff ff    	jne    3b2a <main+0x14da>
    3bfc:	48 8d 3d 10 49 00 00 	lea    0x4910(%rip),%rdi        # 8513 <_IO_stdin_used+0x513>
    3c03:	e8 18 e7 ff ff       	call   2320 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3c08:	48 8d 35 e0 47 00 00 	lea    0x47e0(%rip),%rsi        # 83ef <_IO_stdin_used+0x3ef>
    3c0f:	48 8d 3d 15 49 00 00 	lea    0x4915(%rip),%rdi        # 852b <_IO_stdin_used+0x52b>
    3c16:	e8 c5 e8 ff ff       	call   24e0 <fopen@plt>
    3c1b:	49 89 c4             	mov    %rax,%r12
  for (int x = 0 ; x < datas2_size; x++) {
    3c1e:	85 db                	test   %ebx,%ebx
    3c20:	7e 76                	jle    3c98 <main+0x1648>
    3c22:	48 8d 05 e9 47 00 00 	lea    0x47e9(%rip),%rax        # 8412 <_IO_stdin_used+0x412>
    3c29:	48 63 db             	movslq %ebx,%rbx
    3c2c:	4c 8d 35 9b 47 00 00 	lea    0x479b(%rip),%r14        # 83ce <_IO_stdin_used+0x3ce>
    3c33:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3c38:	49 8d 2c df          	lea    (%r15,%rbx,8),%rbp
    char * c = calloc(250, sizeof(char));
    3c3c:	be 01 00 00 00       	mov    $0x1,%esi
    3c41:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3c46:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    3c4a:	e8 a1 e7 ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3c4f:	4c 89 f1             	mov    %r14,%rcx
    3c52:	ba fa 00 00 00       	mov    $0xfa,%edx
    3c57:	be 01 00 00 00       	mov    $0x1,%esi
    3c5c:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3c5f:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3c63:	48 89 df             	mov    %rbx,%rdi
    3c66:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3c6d:	31 c0                	xor    %eax,%eax
    3c6f:	e8 0c e9 ff ff       	call   2580 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3c74:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3c79:	48 89 da             	mov    %rbx,%rdx
    3c7c:	31 c0                	xor    %eax,%eax
    3c7e:	bf 01 00 00 00       	mov    $0x1,%edi
    3c83:	e8 18 e8 ff ff       	call   24a0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3c88:	4c 89 e6             	mov    %r12,%rsi
    3c8b:	48 89 df             	mov    %rbx,%rdi
    3c8e:	e8 1d e7 ff ff       	call   23b0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3c93:	49 39 ef             	cmp    %rbp,%r15
    3c96:	75 a4                	jne    3c3c <main+0x15ec>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3c98:	49 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r13
  fclose(m2);
    3ca2:	4c 89 e7             	mov    %r12,%rdi
  long received = 0;
    3ca5:	45 31 f6             	xor    %r14d,%r14d
  long sents = 0;
    3ca8:	45 31 e4             	xor    %r12d,%r12d
  fclose(m2);
    3cab:	e8 a0 e6 ff ff       	call   2350 <fclose@plt>
    3cb0:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
  long sends = 0;
    3cb5:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  long ingests = 0;
    3cbe:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  long total = 0;
    3cc7:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  int datas2_size = 0; 
    3cd0:	48 8b bc 24 b0 00 00 00 	mov    0xb0(%rsp),%rdi
    3cd8:	8d 48 02             	lea    0x2(%rax),%ecx
    3cdb:	89 44 24 10          	mov    %eax,0x10(%rsp)
    3cdf:	89 4c 24 48          	mov    %ecx,0x48(%rsp)
    3ce3:	4c 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%r15
    3ceb:	48 89 7c 24 40       	mov    %rdi,0x40(%rsp)
      int x = (k * threads_per_group) + d;
    3cf0:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    3cf4:	89 f8                	mov    %edi,%eax
    3cf6:	83 c7 01             	add    $0x1,%edi
        other = abs(x - 1) % total_threads;
    3cf9:	8d 50 02             	lea    0x2(%rax),%edx
    3cfc:	89 7c 24 10          	mov    %edi,0x10(%rsp)
    3d00:	83 e7 01             	and    $0x1,%edi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3d03:	bf 0a 00 00 00       	mov    $0xa,%edi
    3d08:	0f 44 c2             	cmove  %edx,%eax
    3d0b:	48 63 d8             	movslq %eax,%rbx
    3d0e:	e8 ed e5 ff ff       	call   2300 <putchar@plt>
    3d13:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3d18:	bf 01 00 00 00       	mov    $0x1,%edi
    3d1d:	48 8d 35 10 48 00 00 	lea    0x4810(%rip),%rsi        # 8534 <_IO_stdin_used+0x534>
    3d24:	48 8b 10             	mov    (%rax),%rdx
    3d27:	31 c0                	xor    %eax,%eax
    3d29:	e8 72 e7 ff ff       	call   24a0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3d2e:	41 8b 57 40          	mov    0x40(%r15),%edx
    3d32:	85 d2                	test   %edx,%edx
    3d34:	0f 8e d8 04 00 00    	jle    4212 <main+0x1bc2>
    3d3a:	48 63 ca             	movslq %edx,%rcx
    3d3d:	49 8b 47 38          	mov    0x38(%r15),%rax
      long v = 0;
    3d41:	31 d2                	xor    %edx,%edx
    3d43:	48 c1 e1 09          	shl    $0x9,%rcx
    3d47:	48 01 c1             	add    %rax,%rcx
    3d4a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    3d50:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3d57:	48 05 00 02 00 00    	add    $0x200,%rax
    3d5d:	48 39 c8             	cmp    %rcx,%rax
    3d60:	75 ee                	jne    3d50 <main+0x1700>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3d62:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3d67:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    3d6b:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3d6f:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3d73:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3d77:	85 c9                	test   %ecx,%ecx
    3d79:	7e 27                	jle    3da2 <main+0x1752>
    3d7b:	48 8b 40 38          	mov    0x38(%rax),%rax
    3d7f:	48 c1 e1 09          	shl    $0x9,%rcx
    3d83:	48 01 c1             	add    %rax,%rcx
    3d86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3d90:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3d97:	48 05 00 02 00 00    	add    $0x200,%rax
    3d9d:	48 39 c8             	cmp    %rcx,%rax
    3da0:	75 ee                	jne    3d90 <main+0x1740>
    3da2:	48 8d 35 a0 47 00 00 	lea    0x47a0(%rip),%rsi        # 8549 <_IO_stdin_used+0x549>
    3da9:	bf 01 00 00 00       	mov    $0x1,%edi
    3dae:	31 c0                	xor    %eax,%eax
    3db0:	e8 eb e6 ff ff       	call   24a0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3db5:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3dba:	bf 01 00 00 00       	mov    $0x1,%edi
    3dbf:	48 8d 35 5a 4a 00 00 	lea    0x4a5a(%rip),%rsi        # 8820 <_IO_stdin_used+0x820>
    3dc6:	48 8b 08             	mov    (%rax),%rcx
    3dc9:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3dd3:	48 f7 e9             	imul   %rcx
    3dd6:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3dda:	31 c0                	xor    %eax,%eax
    3ddc:	48 d1 fa             	sar    %rdx
    3ddf:	48 29 ca             	sub    %rcx,%rdx
    3de2:	e8 b9 e6 ff ff       	call   24a0 <__printf_chk@plt>
    3de7:	bf 0a 00 00 00       	mov    $0xa,%edi
    3dec:	e8 0f e5 ff ff       	call   2300 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3df1:	45 8b 57 40          	mov    0x40(%r15),%r10d
    3df5:	45 85 d2             	test   %r10d,%r10d
    3df8:	0f 8e 01 01 00 00    	jle    3eff <main+0x18af>
        total += thread_data[x].tasks[n].n;
    3dfe:	49 8b 4f 38          	mov    0x38(%r15),%rcx
    3e02:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
    3e07:	31 d2                	xor    %edx,%edx
    3e09:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    3e0e:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    3e13:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3e18:	48 89 d5             	mov    %rdx,%rbp
    3e1b:	89 54 24 08          	mov    %edx,0x8(%rsp)
        sends += thread_data[x].tasks[n].sends;
    3e1f:	31 db                	xor    %ebx,%ebx
    3e21:	48 c1 e5 09          	shl    $0x9,%rbp
    3e25:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
        total += thread_data[x].tasks[n].n;
    3e2a:	48 01 e9             	add    %rbp,%rcx
        sends += thread_data[x].tasks[n].sends;
    3e2d:	48 89 e8             	mov    %rbp,%rax
    3e30:	4c 89 e5             	mov    %r12,%rbp
    3e33:	4d 89 f4             	mov    %r14,%r12
        total += thread_data[x].tasks[n].n;
    3e36:	4c 03 81 08 01 00 00 	add    0x108(%rcx),%r8
        ingests += thread_data[x].tasks[n].ingest_count;
    3e3d:	48 03 b1 68 01 00 00 	add    0x168(%rcx),%rsi
        sends += thread_data[x].tasks[n].sends;
    3e44:	49 89 c6             	mov    %rax,%r14
    3e47:	48 03 b9 78 01 00 00 	add    0x178(%rcx),%rdi
    3e4e:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    3e53:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    3e58:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    3e5d:	0f 1f 00             	nopl   (%rax)
    3e60:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    3e64:	8b 54 24 10          	mov    0x10(%rsp),%edx
    3e68:	41 89 d8             	mov    %ebx,%r8d
    3e6b:	bf 01 00 00 00       	mov    $0x1,%edi
    3e70:	48 8d 35 df 46 00 00 	lea    0x46df(%rip),%rsi        # 8556 <_IO_stdin_used+0x556>
    3e77:	31 c0                	xor    %eax,%eax
    3e79:	e8 22 e6 ff ff       	call   24a0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3e7e:	49 8b 4f 38          	mov    0x38(%r15),%rcx
    3e82:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    3e8a:	48 29 d8             	sub    %rbx,%rax
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3e8d:	48 83 c3 01          	add    $0x1,%rbx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3e91:	4a 8b 94 31 70 01 00 00 	mov    0x170(%rcx,%r14,1),%rdx
    3e99:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
    3e9d:	48 8b 10             	mov    (%rax),%rdx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3ea0:	48 8b 40 08          	mov    0x8(%rax),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3ea4:	4c 8b 8a 08 03 00 00 	mov    0x308(%rdx),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3eab:	4c 8b 92 10 03 00 00 	mov    0x310(%rdx),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3eb2:	49 01 e9             	add    %rbp,%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3eb5:	4d 01 e2             	add    %r12,%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3eb8:	4c 03 88 08 03 00 00 	add    0x308(%rax),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3ebf:	4c 03 90 10 03 00 00 	add    0x310(%rax),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3ec6:	4c 89 cd             	mov    %r9,%rbp
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3ec9:	4d 89 d4             	mov    %r10,%r12
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3ecc:	48 83 fb 06          	cmp    $0x6,%rbx
    3ed0:	75 8e                	jne    3e60 <main+0x1810>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3ed2:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    3ed7:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    3edc:	4d 89 d6             	mov    %r10,%r14
    3edf:	4d 89 cc             	mov    %r9,%r12
    3ee2:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    3ee7:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    3eec:	48 83 c2 01          	add    $0x1,%rdx
    3ef0:	41 39 57 40          	cmp    %edx,0x40(%r15)
    3ef4:	0f 8f 1e ff ff ff    	jg     3e18 <main+0x17c8>
    3efa:	4c 89 44 24 30       	mov    %r8,0x30(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3eff:	31 ed                	xor    %ebp,%ebp
    3f01:	49 83 bf a0 00 00 00 00 	cmpq   $0x0,0xa0(%r15)
    3f09:	48 8d 1d 30 49 00 00 	lea    0x4930(%rip),%rbx        # 8840 <_IO_stdin_used+0x840>
    3f10:	7e 5f                	jle    3f71 <main+0x1921>
    3f12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3f18:	49 8b 87 90 00 00 00 	mov    0x90(%r15),%rax
    3f1f:	48 8d 54 ad 00       	lea    0x0(%rbp,%rbp,4),%rdx
    3f24:	48 83 ec 08          	sub    $0x8,%rsp
    3f28:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3f2d:	48 83 c5 01          	add    $0x1,%rbp
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3f31:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3f35:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3f39:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3f3d:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3f40:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3f44:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3f47:	49 f7 e5             	mul    %r13
    3f4a:	8b 49 20             	mov    0x20(%rcx),%ecx
    3f4d:	56                   	push   %rsi
    3f4e:	31 c0                	xor    %eax,%eax
    3f50:	48 89 de             	mov    %rbx,%rsi
    3f53:	48 c1 ea 12          	shr    $0x12,%rdx
    3f57:	49 89 d1             	mov    %rdx,%r9
    3f5a:	ba 02 00 00 00       	mov    $0x2,%edx
    3f5f:	e8 3c e5 ff ff       	call   24a0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3f64:	41 58                	pop    %r8
    3f66:	41 59                	pop    %r9
    3f68:	49 39 af a0 00 00 00 	cmp    %rbp,0xa0(%r15)
    3f6f:	7f a7                	jg     3f18 <main+0x18c8>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3f71:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    3f78:	85 c9                	test   %ecx,%ecx
    3f7a:	0f 8e f5 00 00 00    	jle    4075 <main+0x1a25>
    3f80:	4c 89 64 24 50       	mov    %r12,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3f85:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    3f89:	31 db                	xor    %ebx,%ebx
    3f8b:	4c 89 74 24 58       	mov    %r14,0x58(%rsp)
    3f90:	49 8b 04 d9          	mov    (%r9,%rbx,8),%rax
    3f94:	41 89 dc             	mov    %ebx,%r12d
    3f97:	4c 8d 34 dd 00 00 00 00 	lea    0x0(,%rbx,8),%r14
    3f9f:	8b 30                	mov    (%rax),%esi
    3fa1:	85 f6                	test   %esi,%esi
    3fa3:	0f 8e b6 00 00 00    	jle    405f <main+0x1a0f>
    3fa9:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3fae:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3fb2:	31 ff                	xor    %edi,%edi
    3fb4:	0f 1f 40 00          	nopl   0x0(%rax)
    3fb8:	48 89 fb             	mov    %rdi,%rbx
    3fbb:	31 ed                	xor    %ebp,%ebp
    3fbd:	48 c1 e3 08          	shl    $0x8,%rbx
    3fc1:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    3fc5:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    3fcb:	85 d2                	test   %edx,%edx
    3fcd:	7e 78                	jle    4047 <main+0x19f7>
    3fcf:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    3fd4:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3fd8:	48 89 e9             	mov    %rbp,%rcx
    3fdb:	48 83 ec 08          	sub    $0x8,%rsp
    3fdf:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3fe4:	48 83 c5 01          	add    $0x1,%rbp
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3fe8:	48 c1 e1 05          	shl    $0x5,%rcx
    3fec:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3ff3:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3ff7:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3ffb:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3ffe:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    4002:	4c 2b 01             	sub    (%rcx),%r8
    4005:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    4006:	49 f7 e5             	mul    %r13
    4009:	44 89 e1             	mov    %r12d,%ecx
    400c:	48 8d 35 7d 48 00 00 	lea    0x487d(%rip),%rsi        # 8890 <_IO_stdin_used+0x890>
    4013:	31 c0                	xor    %eax,%eax
    4015:	48 c1 ea 12          	shr    $0x12,%rdx
    4019:	49 89 d1             	mov    %rdx,%r9
    401c:	ba 02 00 00 00       	mov    $0x2,%edx
    4021:	e8 7a e4 ff ff       	call   24a0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    4026:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    402a:	5e                   	pop    %rsi
    402b:	5f                   	pop    %rdi
    402c:	4b 8b 14 31          	mov    (%r9,%r14,1),%rdx
    4030:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    4034:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    4038:	39 a8 94 00 00 00    	cmp    %ebp,0x94(%rax)
    403e:	7f 98                	jg     3fd8 <main+0x1988>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4040:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    4045:	8b 32                	mov    (%rdx),%esi
    4047:	48 83 c7 01          	add    $0x1,%rdi
    404b:	39 fe                	cmp    %edi,%esi
    404d:	0f 8f 65 ff ff ff    	jg     3fb8 <main+0x1968>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    4053:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    4058:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    405f:	48 83 c3 01          	add    $0x1,%rbx
    4063:	39 d9                	cmp    %ebx,%ecx
    4065:	0f 8f 25 ff ff ff    	jg     3f90 <main+0x1940>
    406b:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    4070:	4c 8b 74 24 58       	mov    0x58(%rsp),%r14
    for (int d = 0 ; d < threads_per_group ; d++) {
    4075:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    407b:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    407f:	49 81 c7 c8 00 00 00 	add    $0xc8,%r15
    4086:	39 7c 24 48          	cmp    %edi,0x48(%rsp)
    408a:	0f 85 60 fc ff ff    	jne    3cf0 <main+0x16a0>
  for (int k = 0 ; k < group_count ; k++) {
    4090:	48 81 84 24 80 00 00 00 90 01 00 00 	addq   $0x190,0x80(%rsp)
    409c:	8b 4c 24 48          	mov    0x48(%rsp),%ecx
    40a0:	48 83 84 24 b0 00 00 00 30 	addq   $0x30,0xb0(%rsp)
    40a9:	83 f9 05             	cmp    $0x5,%ecx
    40ac:	74 07                	je     40b5 <main+0x1a65>
    40ae:	89 c8                	mov    %ecx,%eax
    40b0:	e9 1b fc ff ff       	jmp    3cd0 <main+0x1680>
    40b5:	4c 8b 7c 24 30       	mov    0x30(%rsp),%r15
    40ba:	48 8d 35 a5 44 00 00 	lea    0x44a5(%rip),%rsi        # 8566 <_IO_stdin_used+0x566>
    40c1:	bf 01 00 00 00       	mov    $0x1,%edi
    40c6:	31 c0                	xor    %eax,%eax
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    40c8:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    40d2:	4c 89 fa             	mov    %r15,%rdx
    40d5:	e8 c6 e3 ff ff       	call   24a0 <__printf_chk@plt>
    40da:	bf 0a 00 00 00       	mov    $0xa,%edi
    40df:	e8 1c e2 ff ff       	call   2300 <putchar@plt>
    40e4:	48 8b bc 24 90 00 00 00 	mov    0x90(%rsp),%rdi
    40ec:	48 8d 35 f5 47 00 00 	lea    0x47f5(%rip),%rsi        # 88e8 <_IO_stdin_used+0x8e8>
    40f3:	31 c0                	xor    %eax,%eax
    40f5:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    40f9:	bf 01 00 00 00       	mov    $0x1,%edi
    40fe:	e8 9d e3 ff ff       	call   24a0 <__printf_chk@plt>
    4103:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4108:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    410d:	48 8d 35 fc 47 00 00 	lea    0x47fc(%rip),%rsi        # 8910 <_IO_stdin_used+0x910>
    4114:	48 f7 eb             	imul   %rbx
    4117:	48 c1 ff 3f          	sar    $0x3f,%rdi
    411b:	31 c0                	xor    %eax,%eax
    411d:	48 d1 fa             	sar    %rdx
    4120:	48 29 fa             	sub    %rdi,%rdx
    4123:	bf 01 00 00 00       	mov    $0x1,%edi
    4128:	e8 73 e3 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    412d:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4132:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    4137:	48 8d 35 02 48 00 00 	lea    0x4802(%rip),%rsi        # 8940 <_IO_stdin_used+0x940>
    413e:	48 f7 eb             	imul   %rbx
    4141:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4145:	31 c0                	xor    %eax,%eax
    4147:	48 d1 fa             	sar    %rdx
    414a:	48 29 fa             	sub    %rdi,%rdx
    414d:	bf 01 00 00 00       	mov    $0x1,%edi
    4152:	e8 49 e3 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    4157:	4c 89 f8             	mov    %r15,%rax
    415a:	4c 89 ff             	mov    %r15,%rdi
    415d:	48 8d 35 0c 48 00 00 	lea    0x480c(%rip),%rsi        # 8970 <_IO_stdin_used+0x970>
    4164:	48 f7 eb             	imul   %rbx
    4167:	48 c1 ff 3f          	sar    $0x3f,%rdi
    416b:	31 c0                	xor    %eax,%eax
    416d:	48 d1 fa             	sar    %rdx
    4170:	48 29 fa             	sub    %rdi,%rdx
    4173:	bf 01 00 00 00       	mov    $0x1,%edi
    4178:	e8 23 e3 ff ff       	call   24a0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    417d:	4c 89 e0             	mov    %r12,%rax
    4180:	bf 01 00 00 00       	mov    $0x1,%edi
    4185:	48 8d 35 ee 43 00 00 	lea    0x43ee(%rip),%rsi        # 857a <_IO_stdin_used+0x57a>
    418c:	48 f7 eb             	imul   %rbx
    418f:	4c 89 e0             	mov    %r12,%rax
    4192:	48 c1 f8 3f          	sar    $0x3f,%rax
    4196:	48 d1 fa             	sar    %rdx
    4199:	48 29 c2             	sub    %rax,%rdx
    419c:	31 c0                	xor    %eax,%eax
    419e:	48 89 d5             	mov    %rdx,%rbp
    41a1:	e8 fa e2 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total sents %ld\n", sentdur);
  long recdur = received / DURATION;
    41a6:	4c 89 f0             	mov    %r14,%rax
    41a9:	bf 01 00 00 00       	mov    $0x1,%edi
    41ae:	48 8d 35 d6 43 00 00 	lea    0x43d6(%rip),%rsi        # 858b <_IO_stdin_used+0x58b>
    41b5:	48 f7 eb             	imul   %rbx
    41b8:	4c 89 f0             	mov    %r14,%rax
    41bb:	48 c1 f8 3f          	sar    $0x3f,%rax
    41bf:	48 89 d3             	mov    %rdx,%rbx
    41c2:	48 d1 fb             	sar    %rbx
    41c5:	48 29 c3             	sub    %rax,%rbx
    41c8:	31 c0                	xor    %eax,%eax
    41ca:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    41cd:	48 29 eb             	sub    %rbp,%rbx
    41d0:	e8 cb e2 ff ff       	call   24a0 <__printf_chk@plt>
    41d5:	31 c0                	xor    %eax,%eax
    41d7:	48 89 da             	mov    %rbx,%rdx
    41da:	bf 01 00 00 00       	mov    $0x1,%edi
    41df:	48 8d 35 b9 43 00 00 	lea    0x43b9(%rip),%rsi        # 859f <_IO_stdin_used+0x59f>
    41e6:	e8 b5 e2 ff ff       	call   24a0 <__printf_chk@plt>
  return 0;

}
    41eb:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
    41f3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    41fc:	75 25                	jne    4223 <main+0x1bd3>
    41fe:	48 81 c4 e8 00 00 00 	add    $0xe8,%rsp
    4205:	31 c0                	xor    %eax,%eax
    4207:	5b                   	pop    %rbx
    4208:	5d                   	pop    %rbp
    4209:	41 5c                	pop    %r12
    420b:	41 5d                	pop    %r13
    420d:	41 5e                	pop    %r14
    420f:	41 5f                	pop    %r15
    4211:	c3                   	ret
      long v = 0;
    4212:	31 d2                	xor    %edx,%edx
    4214:	e9 49 fb ff ff       	jmp    3d62 <main+0x1712>
            exit(1);
    4219:	bf 01 00 00 00       	mov    $0x1,%edi
    421e:	e8 dd e2 ff ff       	call   2500 <exit@plt>
}
    4223:	e8 48 e1 ff ff       	call   2370 <__stack_chk_fail@plt>
    4228:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000004230 <_start>:
    4230:	f3 0f 1e fa          	endbr64
    4234:	31 ed                	xor    %ebp,%ebp
    4236:	49 89 d1             	mov    %rdx,%r9
    4239:	5e                   	pop    %rsi
    423a:	48 89 e2             	mov    %rsp,%rdx
    423d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4241:	50                   	push   %rax
    4242:	54                   	push   %rsp
    4243:	45 31 c0             	xor    %r8d,%r8d
    4246:	31 c9                	xor    %ecx,%ecx
    4248:	48 8d 3d 01 e4 ff ff 	lea    -0x1bff(%rip),%rdi        # 2650 <main>
    424f:	ff 15 83 6d 00 00    	call   *0x6d83(%rip)        # afd8 <__libc_start_main@GLIBC_2.34>
    4255:	f4                   	hlt
    4256:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004260 <deregister_tm_clones>:
    4260:	48 8d 3d b9 6d 00 00 	lea    0x6db9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4267:	48 8d 05 b2 6d 00 00 	lea    0x6db2(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    426e:	48 39 f8             	cmp    %rdi,%rax
    4271:	74 15                	je     4288 <deregister_tm_clones+0x28>
    4273:	48 8b 05 66 6d 00 00 	mov    0x6d66(%rip),%rax        # afe0 <_ITM_deregisterTMCloneTable@Base>
    427a:	48 85 c0             	test   %rax,%rax
    427d:	74 09                	je     4288 <deregister_tm_clones+0x28>
    427f:	ff e0                	jmp    *%rax
    4281:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4288:	c3                   	ret
    4289:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004290 <register_tm_clones>:
    4290:	48 8d 3d 89 6d 00 00 	lea    0x6d89(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4297:	48 8d 35 82 6d 00 00 	lea    0x6d82(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    429e:	48 29 fe             	sub    %rdi,%rsi
    42a1:	48 89 f0             	mov    %rsi,%rax
    42a4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    42a8:	48 c1 f8 03          	sar    $0x3,%rax
    42ac:	48 01 c6             	add    %rax,%rsi
    42af:	48 d1 fe             	sar    %rsi
    42b2:	74 14                	je     42c8 <register_tm_clones+0x38>
    42b4:	48 8b 05 35 6d 00 00 	mov    0x6d35(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    42bb:	48 85 c0             	test   %rax,%rax
    42be:	74 08                	je     42c8 <register_tm_clones+0x38>
    42c0:	ff e0                	jmp    *%rax
    42c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    42c8:	c3                   	ret
    42c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000042d0 <__do_global_dtors_aux>:
    42d0:	f3 0f 1e fa          	endbr64
    42d4:	80 3d 4d 6d 00 00 00 	cmpb   $0x0,0x6d4d(%rip)        # b028 <completed.0>
    42db:	75 2b                	jne    4308 <__do_global_dtors_aux+0x38>
    42dd:	55                   	push   %rbp
    42de:	48 83 3d 12 6d 00 00 00 	cmpq   $0x0,0x6d12(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    42e6:	48 89 e5             	mov    %rsp,%rbp
    42e9:	74 0c                	je     42f7 <__do_global_dtors_aux+0x27>
    42eb:	48 8b 3d 16 6d 00 00 	mov    0x6d16(%rip),%rdi        # b008 <__dso_handle>
    42f2:	e8 e9 df ff ff       	call   22e0 <__cxa_finalize@plt>
    42f7:	e8 64 ff ff ff       	call   4260 <deregister_tm_clones>
    42fc:	c6 05 25 6d 00 00 01 	movb   $0x1,0x6d25(%rip)        # b028 <completed.0>
    4303:	5d                   	pop    %rbp
    4304:	c3                   	ret
    4305:	0f 1f 00             	nopl   (%rax)
    4308:	c3                   	ret
    4309:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004310 <frame_dummy>:
    4310:	f3 0f 1e fa          	endbr64
    4314:	e9 77 ff ff ff       	jmp    4290 <register_tm_clones>
    4319:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004320 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    4320:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    4324:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    432b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    432f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    4337:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    433b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    433f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4346:	48 85 c9             	test   %rcx,%rcx
    4349:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4350:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4354:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    4358:	31 c0                	xor    %eax,%eax
    435a:	c3                   	ret
    435b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004360 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    4360:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    4364:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    436b:	85 c9                	test   %ecx,%ecx
    436d:	7e 4f                	jle    43be <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    436f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    4376:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    437d:	48 c1 e1 09          	shl    $0x9,%rcx
    4381:	48 8b 50 18          	mov    0x18(%rax),%rdx
    4385:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    4389:	48 8b 70 38          	mov    0x38(%rax),%rsi
    438d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    438f:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4393:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4398:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    43a0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    43a8:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    43b3:	48 05 00 02 00 00    	add    $0x200,%rax
    43b9:	48 39 c1             	cmp    %rax,%rcx
    43bc:	75 da                	jne    4398 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    43be:	0f ae f8             	sfence
}
    43c1:	31 c0                	xor    %eax,%eax
    43c3:	c3                   	ret
    43c4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    43cf:	90                   	nop

00000000000043d0 <external_thread>:
void * external_thread(void *arg) {
    43d0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    43d4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    43d8:	0f 85 fb 00 00 00    	jne    44d9 <external_thread+0x109>
void * external_thread(void *arg) {
    43de:	41 57                	push   %r15
    43e0:	49 89 ff             	mov    %rdi,%r15
    43e3:	41 56                	push   %r14
    43e5:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    43e7:	4c 8d 2d 16 3c 00 00 	lea    0x3c16(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    43ee:	41 54                	push   %r12
    43f0:	55                   	push   %rbp
    43f1:	53                   	push   %rbx
    43f2:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    43f6:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    43fc:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    4400:	85 c9                	test   %ecx,%ecx
    4402:	7e 6e                	jle    4472 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4404:	45 31 e4             	xor    %r12d,%r12d
    4407:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4410:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    4418:	31 db                	xor    %ebx,%ebx
    441a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    441e:	48 8b 06             	mov    (%rsi),%rax
    4421:	8b 10                	mov    (%rax),%edx
    4423:	85 d2                	test   %edx,%edx
    4425:	7e 2a                	jle    4451 <external_thread+0x81>
    4427:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    442b:	48 89 dd             	mov    %rbx,%rbp
    442e:	48 c1 e5 08          	shl    $0x8,%rbp
    4432:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4436:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    443d:	45 85 c0             	test   %r8d,%r8d
    4440:	74 36                	je     4478 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4442:	48 83 c3 01          	add    $0x1,%rbx
    4446:	39 da                	cmp    %ebx,%edx
    4448:	7f e1                	jg     442b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    444a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    4451:	49 83 c4 01          	add    $0x1,%r12
    4455:	44 39 e1             	cmp    %r12d,%ecx
    4458:	7f b6                	jg     4410 <external_thread+0x40>
  while (data->running == 1) {
    445a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    445f:	74 9f                	je     4400 <external_thread+0x30>
}
    4461:	48 83 c4 08          	add    $0x8,%rsp
    4465:	31 c0                	xor    %eax,%eax
    4467:	5b                   	pop    %rbx
    4468:	5d                   	pop    %rbp
    4469:	41 5c                	pop    %r12
    446b:	41 5d                	pop    %r13
    446d:	41 5e                	pop    %r14
    446f:	41 5f                	pop    %r15
    4471:	c3                   	ret
  while (data->running == 1) {
    4472:	eb fe                	jmp    4472 <external_thread+0xa2>
    4474:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    4478:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    447b:	48 8b 06             	mov    (%rsi),%rax
    447e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4482:	48 01 ef             	add    %rbp,%rdi
    4485:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    448c:	48 c1 e6 05          	shl    $0x5,%rsi
    4490:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4497:	bf 04 00 00 00       	mov    $0x4,%edi
    449c:	e8 9f de ff ff       	call   2340 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    44a1:	49 8b 47 50          	mov    0x50(%r15),%rax
    44a5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    44a9:	48 8b 40 08          	mov    0x8(%rax),%rax
    44ad:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    44b8:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    44bb:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    44bf:	48 83 c3 01          	add    $0x1,%rbx
    44c3:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    44c7:	48 8b 06             	mov    (%rsi),%rax
    44ca:	8b 10                	mov    (%rax),%edx
    44cc:	39 da                	cmp    %ebx,%edx
    44ce:	0f 8f 53 ff ff ff    	jg     4427 <external_thread+0x57>
    44d4:	e9 71 ff ff ff       	jmp    444a <external_thread+0x7a>
}
    44d9:	31 c0                	xor    %eax,%eax
    44db:	c3                   	ret
    44dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000044e0 <timer_thread>:
void* timer_thread(void *arg) {
    44e0:	f3 0f 1e fa          	endbr64
    44e4:	41 57                	push   %r15
    44e6:	48 8d 35 23 3b 00 00 	lea    0x3b23(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    44ed:	41 56                	push   %r14
    44ef:	41 55                	push   %r13
    44f1:	41 54                	push   %r12
    44f3:	55                   	push   %rbp
    44f4:	53                   	push   %rbx
    44f5:	48 89 fb             	mov    %rdi,%rbx
    44f8:	48 83 ec 68          	sub    $0x68,%rsp
    44fc:	8b 57 04             	mov    0x4(%rdi),%edx
    44ff:	bf 01 00 00 00       	mov    $0x1,%edi
    4504:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    450d:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    4512:	31 c0                	xor    %eax,%eax
    4514:	e8 87 df ff ff       	call   24a0 <__printf_chk@plt>
  struct timespec preempt = {
    4519:	66 0f 6f 05 6f 46 00 00 	movdqa 0x466f(%rip),%xmm0        # 8b90 <_IO_stdin_used+0xb90>
    4521:	ba 88 13 00 00       	mov    $0x1388,%edx
    4526:	31 c0                	xor    %eax,%eax
    4528:	48 8d 35 f3 3a 00 00 	lea    0x3af3(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    452f:	bf 01 00 00 00       	mov    $0x1,%edi
    4534:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
    4539:	e8 62 df ff ff       	call   24a0 <__printf_chk@plt>
  while (data->running && n < times) {
    453e:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4541:	85 ed                	test   %ebp,%ebp
    4543:	0f 84 9b 00 00 00    	je     45e4 <timer_thread+0x104>
  int n = 0;
    4549:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    454c:	31 ed                	xor    %ebp,%ebp
    454e:	4c 8d 74 24 10       	lea    0x10(%rsp),%r14
    y++;
    4553:	45 31 e4             	xor    %r12d,%r12d
    4556:	4c 8d 6c 24 20       	lea    0x20(%rsp),%r13
    nanosleep(&preempt , &rem2);
    455b:	4c 89 ef             	mov    %r13,%rdi
    455e:	4c 89 f6             	mov    %r14,%rsi
    n++;
    4561:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    4565:	e8 26 de ff ff       	call   2390 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    456a:	48 63 43 30          	movslq 0x30(%rbx),%rax
    y++;
    456e:	8d 7d 01             	lea    0x1(%rbp),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4571:	85 c0                	test   %eax,%eax
    4573:	7e 48                	jle    45bd <timer_thread+0xdd>
    4575:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4579:	4c 63 c5             	movslq %ebp,%r8
    457c:	49 c1 e0 09          	shl    $0x9,%r8
    4580:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4584:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4588:	4c 8b 19             	mov    (%rcx),%r11
    458b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    458d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4591:	99                   	cltd
    4592:	41 f7 7b 40          	idivl  0x40(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    4596:	49 8b 73 38          	mov    0x38(%r11),%rsi
    459a:	48 63 d2             	movslq %edx,%rdx
    459d:	48 c1 e2 09          	shl    $0x9,%rdx
    45a1:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    45ac:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    45b8:	49 39 c9             	cmp    %rcx,%r9
    45bb:	75 cb                	jne    4588 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    45bd:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    45c0:	48 8b 43 18          	mov    0x18(%rbx),%rax
  while (data->running && n < times) {
    45c4:	8b 4b 44             	mov    0x44(%rbx),%ecx
    if (y >= data->threads[0]->task_count) {
    45c7:	48 8b 00             	mov    (%rax),%rax
    y++;
    45ca:	39 78 40             	cmp    %edi,0x40(%rax)
    45cd:	41 0f 4e fc          	cmovle %r12d,%edi
    45d1:	89 fd                	mov    %edi,%ebp
  while (data->running && n < times) {
    45d3:	85 c9                	test   %ecx,%ecx
    45d5:	74 0d                	je     45e4 <timer_thread+0x104>
    45d7:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    45de:	0f 85 77 ff ff ff    	jne    455b <timer_thread+0x7b>
    45e4:	48 8d 3d 4d 3a 00 00 	lea    0x3a4d(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    45eb:	e8 30 dd ff ff       	call   2320 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    45f0:	48 63 53 30          	movslq 0x30(%rbx),%rdx
    45f4:	85 d2                	test   %edx,%edx
    45f6:	7e 6d                	jle    4665 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    45f8:	48 63 43 40          	movslq 0x40(%rbx),%rax
    45fc:	85 c0                	test   %eax,%eax
    45fe:	7e 65                	jle    4665 <timer_thread+0x185>
    4600:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    4604:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    4608:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4610:	31 c9                	xor    %ecx,%ecx
    4612:	48 89 c6             	mov    %rax,%rsi
    4615:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4619:	48 8b 40 38          	mov    0x38(%rax),%rax
    461d:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4621:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4627:	74 17                	je     4640 <timer_thread+0x160>
    4629:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4633:	48 05 00 02 00 00    	add    $0x200,%rax
    4639:	48 39 c2             	cmp    %rax,%rdx
    463c:	74 1e                	je     465c <timer_thread+0x17c>
    463e:	66 90                	xchg   %ax,%ax
      data->threads[x]->tasks[y].sending = 0;
    4640:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    464a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4650:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4657:	48 39 c2             	cmp    %rax,%rdx
    465a:	75 e4                	jne    4640 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    465c:	48 83 c1 08          	add    $0x8,%rcx
    4660:	48 39 cf             	cmp    %rcx,%rdi
    4663:	75 b0                	jne    4615 <timer_thread+0x135>
  asm volatile ("mfence" ::: "memory");
    4665:	0f ae f0             	mfence
  struct timespec drain = {
    4668:	66 0f 6f 05 30 45 00 00 	movdqa 0x4530(%rip),%xmm0        # 8ba0 <_IO_stdin_used+0xba0>
    4670:	4c 8d 3d e6 39 00 00 	lea    0x39e6(%rip),%r15        # 805d <_IO_stdin_used+0x5d>
    4677:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    467c:	48 63 43 28          	movslq 0x28(%rbx),%rax
    y++;
    4680:	8d 7d 01             	lea    0x1(%rbp),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    4683:	85 c0                	test   %eax,%eax
    4685:	7e 4e                	jle    46d5 <timer_thread+0x1f5>
    4687:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    468b:	4c 63 c5             	movslq %ebp,%r8
    468e:	49 c1 e0 09          	shl    $0x9,%r8
    4692:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4696:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    46a0:	4c 8b 11             	mov    (%rcx),%r10
    46a3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    46a5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    46a9:	99                   	cltd
    46aa:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    46ae:	49 8b 72 38          	mov    0x38(%r10),%rsi
    46b2:	48 63 d2             	movslq %edx,%rdx
    46b5:	48 c1 e2 09          	shl    $0x9,%rdx
    46b9:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    46c4:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    46d0:	4c 39 c9             	cmp    %r9,%rcx
    46d3:	75 cb                	jne    46a0 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    46d5:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    46d8:	48 8b 43 18          	mov    0x18(%rbx),%rax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46dc:	44 8b 53 30          	mov    0x30(%rbx),%r10d
    if (y >= data->threads[0]->task_count) {
    46e0:	48 8b 00             	mov    (%rax),%rax
    y++;
    46e3:	39 78 40             	cmp    %edi,0x40(%rax)
    46e6:	b8 00 00 00 00       	mov    $0x0,%eax
    46eb:	0f 4f c7             	cmovg  %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46ee:	45 85 d2             	test   %r10d,%r10d
    46f1:	0f 8e 45 01 00 00    	jle    483c <timer_thread+0x35c>
    int all_empty = 1;
    46f7:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46fb:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    46fe:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    4704:	0f 1f 40 00          	nopl   0x0(%rax)
      for (int y = 0 ; y < 2 ; y++) {
    4708:	45 31 ed             	xor    %r13d,%r13d
    470b:	44 89 f5             	mov    %r14d,%ebp
    470e:	4e 8d 24 f5 00 00 00 00 	lea    0x0(,%r14,8),%r12
    4716:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4719:	45 85 d2             	test   %r10d,%r10d
    471c:	0f 8e bd 00 00 00    	jle    47df <timer_thread+0x2ff>
    4722:	44 89 5c 24 08       	mov    %r11d,0x8(%rsp)
    4727:	4d 89 eb             	mov    %r13,%r11
      y = 0;
    472a:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    472c:	45 31 c0             	xor    %r8d,%r8d
    472f:	49 c1 e3 09          	shl    $0x9,%r11
    4733:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (x == k) { continue; }
    4738:	45 39 f0             	cmp    %r14d,%r8d
    473b:	74 36                	je     4773 <timer_thread+0x293>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    473d:	48 8b 53 18          	mov    0x18(%rbx),%rdx
    4741:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    4745:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4749:	4a 8b 8c 1a 70 01 00 00 	mov    0x170(%rdx,%r11,1),%rcx
    4751:	48 01 c1             	add    %rax,%rcx
    4754:	48 8b 11             	mov    (%rcx),%rdx
    4757:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    475b:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    4762:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    4769:	4d 85 c9             	test   %r9,%r9
    476c:	7f 2a                	jg     4798 <timer_thread+0x2b8>
    476e:	48 85 f6             	test   %rsi,%rsi
    4771:	7f 25                	jg     4798 <timer_thread+0x2b8>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4773:	41 83 c0 01          	add    $0x1,%r8d
    4777:	48 83 c0 38          	add    $0x38,%rax
    477b:	45 39 d0             	cmp    %r10d,%r8d
    477e:	75 b8                	jne    4738 <timer_thread+0x258>
      for (int y = 0 ; y < 2 ; y++) {
    4780:	49 83 fd 01          	cmp    $0x1,%r13
    4784:	0f 84 9e 00 00 00    	je     4828 <timer_thread+0x348>
    478a:	49 83 c5 01          	add    $0x1,%r13
    478e:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4791:	eb 94                	jmp    4727 <timer_thread+0x247>
    4793:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4798:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
    479e:	48 83 ec 08          	sub    $0x8,%rsp
    47a2:	89 f9                	mov    %edi,%ecx
    47a4:	bf 01 00 00 00       	mov    $0x1,%edi
    47a9:	50                   	push   %rax
    47aa:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    47b0:	89 ea                	mov    %ebp,%edx
    47b2:	50                   	push   %rax
    47b3:	31 c0                	xor    %eax,%eax
    47b5:	56                   	push   %rsi
    47b6:	4c 89 fe             	mov    %r15,%rsi
    47b9:	e8 e2 dc ff ff       	call   24a0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    47be:	44 8b 53 30          	mov    0x30(%rbx),%r10d
      for (int y = 0 ; y < 2 ; y++) {
    47c2:	48 83 c4 20          	add    $0x20,%rsp
    47c6:	49 83 fd 01          	cmp    $0x1,%r13
    47ca:	74 44                	je     4810 <timer_thread+0x330>
    47cc:	49 83 c5 01          	add    $0x1,%r13
    47d0:	45 31 db             	xor    %r11d,%r11d
    47d3:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    47d6:	45 85 d2             	test   %r10d,%r10d
    47d9:	0f 8f 43 ff ff ff    	jg     4722 <timer_thread+0x242>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    47df:	49 83 c6 01          	add    $0x1,%r14
    47e3:	45 39 f2             	cmp    %r14d,%r10d
    47e6:	0f 8f 1c ff ff ff    	jg     4708 <timer_thread+0x228>
    47ec:	8b 6c 24 0c          	mov    0xc(%rsp),%ebp
    if (all_empty == 1) {
    47f0:	41 83 fb 01          	cmp    $0x1,%r11d
    47f4:	74 46                	je     483c <timer_thread+0x35c>
      nanosleep(&drain , &drainrem);
    47f6:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    47fb:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    4800:	e8 8b db ff ff       	call   2390 <nanosleep@plt>
    4805:	e9 72 fe ff ff       	jmp    467c <timer_thread+0x19c>
    480a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4810:	49 83 c6 01          	add    $0x1,%r14
    4814:	45 31 db             	xor    %r11d,%r11d
    4817:	45 39 f2             	cmp    %r14d,%r10d
    481a:	0f 8f e8 fe ff ff    	jg     4708 <timer_thread+0x228>
    4820:	eb ca                	jmp    47ec <timer_thread+0x30c>
    4822:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4828:	49 83 c6 01          	add    $0x1,%r14
    482c:	44 8b 5c 24 08       	mov    0x8(%rsp),%r11d
    4831:	45 39 f2             	cmp    %r14d,%r10d
    4834:	0f 8f ce fe ff ff    	jg     4708 <timer_thread+0x228>
    483a:	eb b0                	jmp    47ec <timer_thread+0x30c>
    483c:	48 8d 3d 11 38 00 00 	lea    0x3811(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4843:	e8 d8 da ff ff       	call   2320 <puts@plt>
  while (data->running) {
    4848:	8b 53 44             	mov    0x44(%rbx),%edx
    484b:	85 d2                	test   %edx,%edx
    484d:	0f 84 eb 00 00 00    	je     493e <timer_thread+0x45e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4853:	8b 43 2c             	mov    0x2c(%rbx),%eax
    4856:	31 ed                	xor    %ebp,%ebp
    4858:	4c 8d 25 1b 38 00 00 	lea    0x381b(%rip),%r12        # 807a <_IO_stdin_used+0x7a>
    485f:	4c 8d 2d 2f 38 00 00 	lea    0x382f(%rip),%r13        # 8095 <_IO_stdin_used+0x95>
    4866:	85 c0                	test   %eax,%eax
    4868:	7e 39                	jle    48a3 <timer_thread+0x3c3>
    486a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4870:	31 c0                	xor    %eax,%eax
    4872:	89 ea                	mov    %ebp,%edx
    4874:	4c 89 e6             	mov    %r12,%rsi
    4877:	bf 01 00 00 00       	mov    $0x1,%edi
    487c:	e8 1f dc ff ff       	call   24a0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4881:	48 8b 43 18          	mov    0x18(%rbx),%rax
    4885:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
      if (data->threads[x]->type == IO) {
    4889:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    488d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4894:	0f 84 d1 00 00 00    	je     496b <timer_thread+0x48b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    489a:	48 83 c5 01          	add    $0x1,%rbp
    489e:	39 6b 2c             	cmp    %ebp,0x2c(%rbx)
    48a1:	7f cd                	jg     4870 <timer_thread+0x390>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48a3:	48 63 53 30          	movslq 0x30(%rbx),%rdx
    48a7:	85 d2                	test   %edx,%edx
    48a9:	7e 7d                	jle    4928 <timer_thread+0x448>
      for (int y = 0 ; y < data->task_count ; y++) {
    48ab:	8b 43 40             	mov    0x40(%rbx),%eax
    48ae:	85 c0                	test   %eax,%eax
    48b0:	7e 76                	jle    4928 <timer_thread+0x448>
    48b2:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    48b5:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    48b9:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    48c1:	31 c9                	xor    %ecx,%ecx
    48c3:	48 c1 e6 09          	shl    $0x9,%rsi
    48c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    48d0:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    48d4:	48 8b 40 38          	mov    0x38(%rax),%rax
    48d8:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    48dc:	f7 c6 00 02 00 00    	test   $0x200,%esi
    48e2:	74 1c                	je     4900 <timer_thread+0x420>
    48e4:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    48ee:	48 05 00 02 00 00    	add    $0x200,%rax
    48f4:	48 39 d0             	cmp    %rdx,%rax
    48f7:	74 26                	je     491f <timer_thread+0x43f>
    48f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4900:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    490a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4910:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    491a:	48 39 d0             	cmp    %rdx,%rax
    491d:	75 e1                	jne    4900 <timer_thread+0x420>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    491f:	48 83 c1 08          	add    $0x8,%rcx
    4923:	48 39 f9             	cmp    %rdi,%rcx
    4926:	75 a8                	jne    48d0 <timer_thread+0x3f0>
    asm volatile ("mfence" ::: "memory");
    4928:	0f ae f0             	mfence
    492b:	48 8d 3d 75 37 00 00 	lea    0x3775(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4932:	e8 e9 d9 ff ff       	call   2320 <puts@plt>
    data->running = 0;
    4937:	c7 43 44 00 00 00 00 	movl   $0x0,0x44(%rbx)
    493e:	48 8d 3d 69 37 00 00 	lea    0x3769(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4945:	e8 d6 d9 ff ff       	call   2320 <puts@plt>
}
    494a:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    494f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4958:	75 40                	jne    499a <timer_thread+0x4ba>
    495a:	48 83 c4 68          	add    $0x68,%rsp
    495e:	31 c0                	xor    %eax,%eax
    4960:	5b                   	pop    %rbx
    4961:	5d                   	pop    %rbp
    4962:	41 5c                	pop    %r12
    4964:	41 5d                	pop    %r13
    4966:	41 5e                	pop    %r14
    4968:	41 5f                	pop    %r15
    496a:	c3                   	ret
    496b:	4c 89 ef             	mov    %r13,%rdi
    496e:	e8 ad d9 ff ff       	call   2320 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4973:	48 8b 43 18          	mov    0x18(%rbx),%rax
    4977:	be 01 00 00 00       	mov    $0x1,%esi
    497c:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4980:	48 83 c5 01          	add    $0x1,%rbp
        eventfd_write(data->threads[x]->_eventfd, 1);
    4984:	8b 78 60             	mov    0x60(%rax),%edi
    4987:	e8 c4 da ff ff       	call   2450 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    498c:	39 6b 2c             	cmp    %ebp,0x2c(%rbx)
    498f:	0f 8f db fe ff ff    	jg     4870 <timer_thread+0x390>
    4995:	e9 09 ff ff ff       	jmp    48a3 <timer_thread+0x3c3>
}
    499a:	e8 d1 d9 ff ff       	call   2370 <__stack_chk_fail@plt>
    499f:	90                   	nop

00000000000049a0 <strtolower>:
void strtolower(char *str) {
    49a0:	f3 0f 1e fa          	endbr64
    49a4:	55                   	push   %rbp
    49a5:	53                   	push   %rbx
    49a6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    49aa:	48 0f be 1f          	movsbq (%rdi),%rbx
    49ae:	84 db                	test   %bl,%bl
    49b0:	74 24                	je     49d6 <strtolower+0x36>
    49b2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    49b5:	e8 b6 db ff ff       	call   2570 <__ctype_tolower_loc@plt>
    49ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    49c0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    49c3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    49c7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    49ca:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    49cd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    49d2:	84 db                	test   %bl,%bl
    49d4:	75 ea                	jne    49c0 <strtolower+0x20>
}
    49d6:	48 83 c4 08          	add    $0x8,%rsp
    49da:	5b                   	pop    %rbx
    49db:	5d                   	pop    %rbp
    49dc:	c3                   	ret
    49dd:	0f 1f 00             	nopl   (%rax)

00000000000049e0 <zh_malloc>:
void *zh_malloc(size_t size) {
    49e0:	f3 0f 1e fa          	endbr64
    49e4:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    49e8:	e8 73 da ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    49ed:	48 85 c0             	test   %rax,%rax
    49f0:	74 05                	je     49f7 <zh_malloc+0x17>
}
    49f2:	48 83 c4 08          	add    $0x8,%rsp
    49f6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    49f7:	48 8b 0d 22 66 00 00 	mov    0x6622(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    49fe:	ba 28 00 00 00       	mov    $0x28,%edx
    4a03:	be 01 00 00 00       	mov    $0x1,%esi
    4a08:	48 8d 3d a1 3b 00 00 	lea    0x3ba1(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    4a0f:	e8 0c db ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4a14:	bf 01 00 00 00       	mov    $0x1,%edi
    4a19:	e8 e2 da ff ff       	call   2500 <exit@plt>
    4a1e:	66 90                	xchg   %ax,%ax

0000000000004a20 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4a20:	f3 0f 1e fa          	endbr64
    4a24:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4a25:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    4a2a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    4a2d:	e8 6e d9 ff ff       	call   23a0 <strrchr@plt>
    if (!dot || dot == filename)
    4a32:	48 85 c0             	test   %rax,%rax
    4a35:	74 11                	je     4a48 <get_filename_ext+0x28>
    4a37:	48 39 c3             	cmp    %rax,%rbx
    4a3a:	74 0c                	je     4a48 <get_filename_ext+0x28>
    return dot + 1;
    4a3c:	48 83 c0 01          	add    $0x1,%rax
}
    4a40:	5b                   	pop    %rbx
    4a41:	c3                   	ret
    4a42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4a48:	48 8d 05 a7 36 00 00 	lea    0x36a7(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
}
    4a4f:	5b                   	pop    %rbx
    4a50:	c3                   	ret
    4a51:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4a5c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a60 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4a60:	f3 0f 1e fa          	endbr64
    4a64:	41 55                	push   %r13
    4a66:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a69:	48 89 fe             	mov    %rdi,%rsi
    4a6c:	41 54                	push   %r12
    4a6e:	55                   	push   %rbp
    4a6f:	48 89 d5             	mov    %rdx,%rbp
    4a72:	ba 00 04 00 00       	mov    $0x400,%edx
    4a77:	53                   	push   %rbx
    4a78:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4a7f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a88:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4a90:	31 c0                	xor    %eax,%eax
    4a92:	49 89 e4             	mov    %rsp,%r12
    4a95:	4c 89 e7             	mov    %r12,%rdi
    4a98:	e8 e3 d9 ff ff       	call   2480 <__strcpy_chk@plt>
    for (; *str; ++str)
    4a9d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4aa2:	84 db                	test   %bl,%bl
    4aa4:	74 24                	je     4aca <send_headers+0x6a>
        *str = (char)tolower(*str);
    4aa6:	e8 c5 da ff ff       	call   2570 <__ctype_tolower_loc@plt>
    4aab:	48 8b 08             	mov    (%rax),%rcx
    4aae:	4c 89 e0             	mov    %r12,%rax
    4ab1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4ab8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4abb:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4abf:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4ac2:	48 0f be 18          	movsbq (%rax),%rbx
    4ac6:	84 db                	test   %bl,%bl
    4ac8:	75 ee                	jne    4ab8 <send_headers+0x58>
    void *buf = malloc(size);
    4aca:	bf 11 00 00 00       	mov    $0x11,%edi
    4acf:	e8 8c d9 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4ad4:	48 85 c0             	test   %rax,%rax
    4ad7:	0f 84 7e 04 00 00    	je     4f5b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4add:	66 0f 6f 05 cb 40 00 00 	movdqa 0x40cb(%rip),%xmm0        # 8bb0 <_IO_stdin_used+0xbb0>
    iov[0].iov_base = zh_malloc(slen);
    4ae5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4ae9:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4aee:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4af6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4afa:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4afd:	e8 5e d9 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4b02:	48 85 c0             	test   %rax,%rax
    4b05:	0f 84 50 04 00 00    	je     4f5b <send_headers+0x4fb>
    4b0b:	66 0f 6f 05 ad 40 00 00 	movdqa 0x40ad(%rip),%xmm0        # 8bc0 <_IO_stdin_used+0xbc0>
    iov[1].iov_base = zh_malloc(slen);
    4b13:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4b17:	4c 89 e7             	mov    %r12,%rdi
    4b1a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4b24:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4b2c:	0f 11 00             	movups %xmm0,(%rax)
    4b2f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4b33:	be 2e 00 00 00       	mov    $0x2e,%esi
    4b38:	e8 63 d8 ff ff       	call   23a0 <strrchr@plt>
    if (!dot || dot == filename)
    4b3d:	48 85 c0             	test   %rax,%rax
    4b40:	0f 84 ea 02 00 00    	je     4e30 <send_headers+0x3d0>
    4b46:	4c 39 e0             	cmp    %r12,%rax
    4b49:	0f 84 e1 02 00 00    	je     4e30 <send_headers+0x3d0>
    return dot + 1;
    4b4f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4b53:	48 8d 3d 6a 35 00 00 	lea    0x356a(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4b5a:	48 89 de             	mov    %rbx,%rsi
    4b5d:	e8 9e d8 ff ff       	call   2400 <strcmp@plt>
    4b62:	85 c0                	test   %eax,%eax
    4b64:	75 20                	jne    4b86 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4b66:	66 0f 6f 05 62 40 00 00 	movdqa 0x4062(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4b6e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b76:	66 0f 6f 05 62 40 00 00 	movdqa 0x4062(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4b7e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4b86:	48 89 de             	mov    %rbx,%rsi
    4b89:	48 8d 3d 38 35 00 00 	lea    0x3538(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4b90:	e8 6b d8 ff ff       	call   2400 <strcmp@plt>
    4b95:	85 c0                	test   %eax,%eax
    4b97:	75 20                	jne    4bb9 <send_headers+0x159>
    4b99:	66 0f 6f 05 2f 40 00 00 	movdqa 0x402f(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4ba1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ba9:	66 0f 6f 05 2f 40 00 00 	movdqa 0x402f(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4bb1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4bb9:	48 89 de             	mov    %rbx,%rsi
    4bbc:	48 8d 3d 0a 35 00 00 	lea    0x350a(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4bc3:	e8 38 d8 ff ff       	call   2400 <strcmp@plt>
    4bc8:	85 c0                	test   %eax,%eax
    4bca:	0f 84 10 02 00 00    	je     4de0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4bd0:	48 89 de             	mov    %rbx,%rsi
    4bd3:	48 8d 3d f7 34 00 00 	lea    0x34f7(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4bda:	e8 21 d8 ff ff       	call   2400 <strcmp@plt>
    4bdf:	85 c0                	test   %eax,%eax
    4be1:	0f 84 a9 02 00 00    	je     4e90 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4be7:	48 89 de             	mov    %rbx,%rsi
    4bea:	48 8d 3d e4 34 00 00 	lea    0x34e4(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4bf1:	e8 0a d8 ff ff       	call   2400 <strcmp@plt>
    4bf6:	85 c0                	test   %eax,%eax
    4bf8:	0f 84 6a 02 00 00    	je     4e68 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4bfe:	48 89 de             	mov    %rbx,%rsi
    4c01:	48 8d 3d 10 35 00 00 	lea    0x3510(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4c08:	e8 f3 d7 ff ff       	call   2400 <strcmp@plt>
    4c0d:	85 c0                	test   %eax,%eax
    4c0f:	0f 84 2b 02 00 00    	je     4e40 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4c15:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4c18:	0f 84 52 01 00 00    	je     4d70 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4c1e:	48 89 de             	mov    %rbx,%rsi
    4c21:	48 8d 3d b1 34 00 00 	lea    0x34b1(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4c28:	e8 d3 d7 ff ff       	call   2400 <strcmp@plt>
    4c2d:	85 c0                	test   %eax,%eax
    4c2f:	0f 84 ab 02 00 00    	je     4ee0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4c35:	48 89 de             	mov    %rbx,%rsi
    4c38:	48 8d 3d 9e 34 00 00 	lea    0x349e(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4c3f:	e8 bc d7 ff ff       	call   2400 <strcmp@plt>
    4c44:	85 c0                	test   %eax,%eax
    4c46:	0f 84 6c 02 00 00    	je     4eb8 <send_headers+0x458>
    slen = strlen(send_buffer);
    4c4c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4c54:	4c 89 e7             	mov    %r12,%rdi
    4c57:	e8 04 d7 ff ff       	call   2360 <strlen@plt>
    void *buf = malloc(size);
    4c5c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4c5f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4c62:	e8 f9 d7 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4c67:	48 85 c0             	test   %rax,%rax
    4c6a:	0f 84 eb 02 00 00    	je     4f5b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4c70:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4c74:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4c78:	83 fb 08             	cmp    $0x8,%ebx
    4c7b:	0f 83 3f 01 00 00    	jae    4dc0 <send_headers+0x360>
    4c81:	f6 c3 04             	test   $0x4,%bl
    4c84:	0f 85 7b 02 00 00    	jne    4f05 <send_headers+0x4a5>
    4c8a:	85 db                	test   %ebx,%ebx
    4c8c:	74 13                	je     4ca1 <send_headers+0x241>
    4c8e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4c96:	88 10                	mov    %dl,(%rax)
    4c98:	f6 c3 02             	test   $0x2,%bl
    4c9b:	0f 85 96 02 00 00    	jne    4f37 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4ca1:	4d 89 e8             	mov    %r13,%r8
    4ca4:	48 8d 0d 36 34 00 00 	lea    0x3436(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4cab:	4c 89 e7             	mov    %r12,%rdi
    4cae:	31 c0                	xor    %eax,%eax
    4cb0:	ba 00 04 00 00       	mov    $0x400,%edx
    4cb5:	be 01 00 00 00       	mov    $0x1,%esi
    4cba:	e8 c1 d8 ff ff       	call   2580 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4cbf:	4c 89 e7             	mov    %r12,%rdi
    4cc2:	e8 99 d6 ff ff       	call   2360 <strlen@plt>
    void *buf = malloc(size);
    4cc7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4cca:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4ccd:	e8 8e d7 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4cd2:	48 85 c0             	test   %rax,%rax
    4cd5:	0f 84 80 02 00 00    	je     4f5b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4cdb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4cdf:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4ce3:	83 fb 08             	cmp    $0x8,%ebx
    4ce6:	0f 83 1c 01 00 00    	jae    4e08 <send_headers+0x3a8>
    4cec:	f6 c3 04             	test   $0x4,%bl
    4cef:	0f 85 29 02 00 00    	jne    4f1e <send_headers+0x4be>
    4cf5:	85 db                	test   %ebx,%ebx
    4cf7:	74 13                	je     4d0c <send_headers+0x2ac>
    4cf9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4d01:	88 10                	mov    %dl,(%rax)
    4d03:	f6 c3 02             	test   $0x2,%bl
    4d06:	0f 85 3d 02 00 00    	jne    4f49 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d0c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4d11:	bf 02 00 00 00       	mov    $0x2,%edi
    4d16:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4d1e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4d26:	e8 35 d7 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4d2b:	48 85 c0             	test   %rax,%rax
    4d2e:	0f 84 27 02 00 00    	je     4f5b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4d34:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4d3c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4d40:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4d48:	66 89 10             	mov    %dx,(%rax)
}
    4d4b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4d53:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d5c:	0f 85 20 02 00 00    	jne    4f82 <send_headers+0x522>
    4d62:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4d69:	5b                   	pop    %rbx
    4d6a:	5d                   	pop    %rbp
    4d6b:	41 5c                	pop    %r12
    4d6d:	41 5d                	pop    %r13
    4d6f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4d70:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4d74:	0f 85 a4 fe ff ff    	jne    4c1e <send_headers+0x1be>
    4d7a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4d7e:	0f 85 9a fe ff ff    	jne    4c1e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d84:	66 0f 6f 05 a4 3e 00 00 	movdqa 0x3ea4(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    4d8c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4d96:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4d9e:	66 0f 6f 05 9a 3e 00 00 	movdqa 0x3e9a(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    4da6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4dae:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4db6:	e9 63 fe ff ff       	jmp    4c1e <send_headers+0x1be>
    4dbb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4dc0:	89 da                	mov    %ebx,%edx
    4dc2:	48 89 c7             	mov    %rax,%rdi
    4dc5:	4c 89 e6             	mov    %r12,%rsi
    4dc8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4dcd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4dd2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4dd5:	c1 e9 03             	shr    $0x3,%ecx
    4dd8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4ddb:	e9 c1 fe ff ff       	jmp    4ca1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4de0:	66 0f 6f 05 e8 3d 00 00 	movdqa 0x3de8(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4de8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4df0:	66 0f 6f 05 f8 3d 00 00 	movdqa 0x3df8(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    4df8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e00:	e9 cb fd ff ff       	jmp    4bd0 <send_headers+0x170>
    4e05:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4e08:	89 da                	mov    %ebx,%edx
    4e0a:	48 89 c7             	mov    %rax,%rdi
    4e0d:	4c 89 e6             	mov    %r12,%rsi
    4e10:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4e15:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4e1a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4e1d:	c1 e9 03             	shr    $0x3,%ecx
    4e20:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4e23:	e9 e4 fe ff ff       	jmp    4d0c <send_headers+0x2ac>
    4e28:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4e30:	48 8d 1d bf 32 00 00 	lea    0x32bf(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    4e37:	e9 94 fd ff ff       	jmp    4bd0 <send_headers+0x170>
    4e3c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4e40:	66 0f 6f 05 c8 3d 00 00 	movdqa 0x3dc8(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4e48:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e50:	66 0f 6f 05 c8 3d 00 00 	movdqa 0x3dc8(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4e58:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e60:	e9 b0 fd ff ff       	jmp    4c15 <send_headers+0x1b5>
    4e65:	0f 1f 00             	nopl   (%rax)
    4e68:	66 0f 6f 05 a0 3d 00 00 	movdqa 0x3da0(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4e70:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e78:	66 0f 6f 05 a0 3d 00 00 	movdqa 0x3da0(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4e80:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e88:	e9 71 fd ff ff       	jmp    4bfe <send_headers+0x19e>
    4e8d:	0f 1f 00             	nopl   (%rax)
    4e90:	66 0f 6f 05 38 3d 00 00 	movdqa 0x3d38(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4e98:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ea0:	66 0f 6f 05 58 3d 00 00 	movdqa 0x3d58(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    4ea8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4eb0:	e9 32 fd ff ff       	jmp    4be7 <send_headers+0x187>
    4eb5:	0f 1f 00             	nopl   (%rax)
    4eb8:	66 0f 6f 05 50 3d 00 00 	movdqa 0x3d50(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4ec0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ec8:	66 0f 6f 05 90 3d 00 00 	movdqa 0x3d90(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    4ed0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4ed8:	e9 6f fd ff ff       	jmp    4c4c <send_headers+0x1ec>
    4edd:	0f 1f 00             	nopl   (%rax)
    4ee0:	66 0f 6f 05 28 3d 00 00 	movdqa 0x3d28(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4ee8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ef0:	66 0f 6f 05 58 3d 00 00 	movdqa 0x3d58(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    4ef8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4f00:	e9 30 fd ff ff       	jmp    4c35 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4f05:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4f0c:	89 db                	mov    %ebx,%ebx
    4f0e:	89 10                	mov    %edx,(%rax)
    4f10:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4f15:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4f19:	e9 83 fd ff ff       	jmp    4ca1 <send_headers+0x241>
    4f1e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4f25:	89 db                	mov    %ebx,%ebx
    4f27:	89 10                	mov    %edx,(%rax)
    4f29:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4f2e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4f32:	e9 d5 fd ff ff       	jmp    4d0c <send_headers+0x2ac>
    4f37:	89 db                	mov    %ebx,%ebx
    4f39:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4f3f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4f44:	e9 58 fd ff ff       	jmp    4ca1 <send_headers+0x241>
    4f49:	89 db                	mov    %ebx,%ebx
    4f4b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4f51:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4f56:	e9 b1 fd ff ff       	jmp    4d0c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4f5b:	48 8b 0d be 60 00 00 	mov    0x60be(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4f62:	ba 28 00 00 00       	mov    $0x28,%edx
    4f67:	be 01 00 00 00       	mov    $0x1,%esi
    4f6c:	48 8d 3d 3d 36 00 00 	lea    0x363d(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    4f73:	e8 a8 d5 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4f78:	bf 01 00 00 00       	mov    $0x1,%edi
    4f7d:	e8 7e d5 ff ff       	call   2500 <exit@plt>
}
    4f82:	e8 e9 d3 ff ff       	call   2370 <__stack_chk_fail@plt>
    4f87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004f90 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4f90:	f3 0f 1e fa          	endbr64
    4f94:	41 55                	push   %r13
    4f96:	49 89 d5             	mov    %rdx,%r13
    4f99:	41 54                	push   %r12
    4f9b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    4f9e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4fa1:	55                   	push   %rbp
    4fa2:	53                   	push   %rbx
    4fa3:	48 89 f3             	mov    %rsi,%rbx
    4fa6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4faa:	e8 b1 d4 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4faf:	48 85 c0             	test   %rax,%rax
    4fb2:	74 6b                	je     501f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4fb4:	4c 89 e7             	mov    %r12,%rdi
    4fb7:	48 89 c5             	mov    %rax,%rbp
    4fba:	31 f6                	xor    %esi,%esi
    4fbc:	31 c0                	xor    %eax,%eax
    4fbe:	e8 0d d5 ff ff       	call   24d0 <open@plt>
    4fc3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4fc6:	85 c0                	test   %eax,%eax
    4fc8:	0f 88 e8 d5 ff ff    	js     25b6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4fce:	48 89 da             	mov    %rbx,%rdx
    4fd1:	48 89 ee             	mov    %rbp,%rsi
    4fd4:	89 c7                	mov    %eax,%edi
    4fd6:	e8 05 d4 ff ff       	call   23e0 <read@plt>
    if (ret < file_size) {
    4fdb:	48 98                	cltq
    4fdd:	48 39 d8             	cmp    %rbx,%rax
    4fe0:	7c 1e                	jl     5000 <copy_file_contents+0x70>
    close(fd);
    4fe2:	44 89 e7             	mov    %r12d,%edi
    4fe5:	e8 d6 d3 ff ff       	call   23c0 <close@plt>
    iov->iov_base = buf;
    4fea:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    4fee:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4ff2:	48 83 c4 08          	add    $0x8,%rsp
    4ff6:	5b                   	pop    %rbx
    4ff7:	5d                   	pop    %rbp
    4ff8:	41 5c                	pop    %r12
    4ffa:	41 5d                	pop    %r13
    4ffc:	c3                   	ret
    4ffd:	0f 1f 00             	nopl   (%rax)
    5000:	48 8b 0d 19 60 00 00 	mov    0x6019(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5007:	ba 1a 00 00 00       	mov    $0x1a,%edx
    500c:	be 01 00 00 00       	mov    $0x1,%esi
    5011:	48 8d 3d df 30 00 00 	lea    0x30df(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    5018:	e8 03 d5 ff ff       	call   2520 <fwrite@plt>
    501d:	eb c3                	jmp    4fe2 <copy_file_contents+0x52>
    501f:	48 8b 0d fa 5f 00 00 	mov    0x5ffa(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5026:	ba 28 00 00 00       	mov    $0x28,%edx
    502b:	be 01 00 00 00       	mov    $0x1,%esi
    5030:	48 8d 3d 79 35 00 00 	lea    0x3579(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    5037:	e8 e4 d4 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    503c:	bf 01 00 00 00       	mov    $0x1,%edi
    5041:	e8 ba d4 ff ff       	call   2500 <exit@plt>
    5046:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005050 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    5050:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    5054:	8b 46 44             	mov    0x44(%rsi),%eax
    5057:	48 89 fa             	mov    %rdi,%rdx
    505a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    505d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5063:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    5066:	48 8b 07             	mov    (%rdi),%rax
    5069:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    506c:	f6 c1 02             	test   $0x2,%cl
    506f:	74 00                	je     5071 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    5071:	89 f0                	mov    %esi,%eax
    5073:	44 29 c0             	sub    %r8d,%eax
    5076:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    5079:	0f 82 43 d5 ff ff    	jb     25c2 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    507f:	c1 e9 0a             	shr    $0xa,%ecx
    5082:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5086:	8b 47 44             	mov    0x44(%rdi),%eax
    5089:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    508c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    508f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    5092:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    5095:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5099:	d3 e0                	shl    %cl,%eax
    509b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    509e:	48 c1 e0 06          	shl    $0x6,%rax
    50a2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    50a6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    50ac:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    50af:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    50b3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    50b9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    50c1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    50c5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    50c8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    50cf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    50d7:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    50db:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    50df:	e8 9c d2 ff ff       	call   2380 <io_uring_submit@plt>
}
    50e4:	31 c0                	xor    %eax,%eax
    50e6:	48 83 c4 08          	add    $0x8,%rsp
    50ea:	c3                   	ret
    50eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000050f0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    50f0:	f3 0f 1e fa          	endbr64
    50f4:	41 55                	push   %r13
    50f6:	41 89 fd             	mov    %edi,%r13d
    50f9:	41 54                	push   %r12
    50fb:	55                   	push   %rbp
    50fc:	53                   	push   %rbx
    50fd:	48 89 f3             	mov    %rsi,%rbx
    5100:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    5104:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5107:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    510d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    5110:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5113:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5115:	f6 c1 02             	test   $0x2,%cl
    5118:	74 00                	je     511a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    511a:	89 c2                	mov    %eax,%edx
    511c:	29 f2                	sub    %esi,%edx
    511e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5121:	0f 82 ab d4 ff ff    	jb     25d2 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5127:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    512a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    512d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5130:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    5135:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5138:	23 6b 58             	and    0x58(%rbx),%ebp
    513b:	d3 e5                	shl    %cl,%ebp
    513d:	48 c1 e5 06          	shl    $0x6,%rbp
    5141:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5145:	e8 16 d3 ff ff       	call   2460 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    514a:	be 01 00 00 00       	mov    $0x1,%esi
    514f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5154:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    5157:	e8 94 d2 ff ff       	call   23f0 <calloc@plt>
    req->client_socket = client_socket;
    515c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    5161:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    5165:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    5168:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    516d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    5172:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    517b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    5183:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    5187:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    518b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    5192:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    519a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    519e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    51a6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    51ae:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    51b2:	e8 c9 d1 ff ff       	call   2380 <io_uring_submit@plt>
}
    51b7:	48 83 c4 08          	add    $0x8,%rsp
    51bb:	31 c0                	xor    %eax,%eax
    51bd:	5b                   	pop    %rbx
    51be:	5d                   	pop    %rbp
    51bf:	41 5c                	pop    %r12
    51c1:	41 5d                	pop    %r13
    51c3:	c3                   	ret
    51c4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    51cf:	90                   	nop

00000000000051d0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    51d0:	f3 0f 1e fa          	endbr64
    51d4:	41 56                	push   %r14
    51d6:	41 89 f6             	mov    %esi,%r14d
    51d9:	41 55                	push   %r13
    51db:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    51de:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    51e3:	41 54                	push   %r12
    51e5:	55                   	push   %rbp
    51e6:	48 89 d5             	mov    %rdx,%rbp
    51e9:	53                   	push   %rbx
    void *buf = malloc(size);
    51ea:	e8 71 d2 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    51ef:	48 85 c0             	test   %rax,%rax
    51f2:	0f 84 dd 00 00 00    	je     52d5 <_send_static_string_content+0x105>
    51f8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    51fb:	4c 89 ef             	mov    %r13,%rdi
    51fe:	e8 5d d1 ff ff       	call   2360 <strlen@plt>
    req->iovec_count = 1;
    5203:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    520a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    520e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    5211:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    5214:	e8 47 d2 ff ff       	call   2460 <malloc@plt>
    5219:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    521c:	48 85 c0             	test   %rax,%rax
    521f:	0f 84 b0 00 00 00    	je     52d5 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    5225:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5229:	4c 89 e2             	mov    %r12,%rdx
    522c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    522f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    5233:	e8 f8 d1 ff ff       	call   2430 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5238:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    523b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5241:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5244:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5248:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    524a:	f6 c1 02             	test   $0x2,%cl
    524d:	0f 85 7d 00 00 00    	jne    52d0 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    5253:	89 d0                	mov    %edx,%eax
    5255:	29 f0                	sub    %esi,%eax
    5257:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    525a:	0f 82 7c d3 ff ff    	jb     25dc <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5260:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5263:	8b 45 44             	mov    0x44(%rbp),%eax
    5266:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    5269:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    526c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    526f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    5272:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    5278:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    527c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    527e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    5281:	48 89 ef             	mov    %rbp,%rdi
    5284:	48 c1 e0 06          	shl    $0x6,%rax
    5288:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    528c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    528f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    5293:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5299:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    52a1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    52a5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    52a8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    52af:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    52b7:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    52bb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    52bf:	5b                   	pop    %rbx
    52c0:	5d                   	pop    %rbp
    52c1:	41 5c                	pop    %r12
    52c3:	41 5d                	pop    %r13
    52c5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    52c7:	e9 b4 d0 ff ff       	jmp    2380 <io_uring_submit@plt>
    52cc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    52d0:	e9 7e ff ff ff       	jmp    5253 <_send_static_string_content+0x83>
    52d5:	48 8b 0d 44 5d 00 00 	mov    0x5d44(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    52dc:	ba 28 00 00 00       	mov    $0x28,%edx
    52e1:	be 01 00 00 00       	mov    $0x1,%esi
    52e6:	48 8d 3d c3 32 00 00 	lea    0x32c3(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    52ed:	e8 2e d2 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    52f2:	bf 01 00 00 00       	mov    $0x1,%edi
    52f7:	e8 04 d2 ff ff       	call   2500 <exit@plt>
    52fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005300 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    5300:	f3 0f 1e fa          	endbr64
    5304:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5307:	89 fe                	mov    %edi,%esi
    5309:	48 8b 3d 08 5d 00 00 	mov    0x5d08(%rip),%rdi        # b018 <unimplemented_content>
    5310:	e9 bb fe ff ff       	jmp    51d0 <_send_static_string_content>
    5315:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005320 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    5320:	f3 0f 1e fa          	endbr64
    5324:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    5327:	89 fe                	mov    %edi,%esi
    5329:	48 8b 3d e0 5c 00 00 	mov    0x5ce0(%rip),%rdi        # b010 <http_404_content>
    5330:	e9 9b fe ff ff       	jmp    51d0 <_send_static_string_content>
    5335:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005340 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    5340:	f3 0f 1e fa          	endbr64
    5344:	41 56                	push   %r14
    5346:	41 55                	push   %r13
    5348:	49 89 d5             	mov    %rdx,%r13
    534b:	41 54                	push   %r12
    534d:	41 89 f4             	mov    %esi,%r12d
    5350:	55                   	push   %rbp
    5351:	48 89 fd             	mov    %rdi,%rbp
    5354:	53                   	push   %rbx
    5355:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    535c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5365:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    536d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    536f:	e8 ec cf ff ff       	call   2360 <strlen@plt>
    5374:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    5379:	48 89 c3             	mov    %rax,%rbx
    537c:	0f 84 b6 00 00 00    	je     5438 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5382:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5387:	48 89 ee             	mov    %rbp,%rsi
    538a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    538e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5393:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    539b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    53a3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    53ae:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    53b6:	e8 55 d0 ff ff       	call   2410 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    53bb:	48 89 e6             	mov    %rsp,%rsi
    53be:	4c 89 f7             	mov    %r14,%rdi
    53c1:	e8 5a d0 ff ff       	call   2420 <stat@plt>
    53c6:	83 f8 ff             	cmp    $0xffffffff,%eax
    53c9:	0f 84 d3 00 00 00    	je     54a2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    53cf:	8b 44 24 18          	mov    0x18(%rsp),%eax
    53d3:	25 00 f0 00 00       	and    $0xf000,%eax
    53d8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    53dd:	0f 84 f5 00 00 00    	je     54d8 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    53e3:	48 8b 3d 26 5c 00 00 	mov    0x5c26(%rip),%rdi        # b010 <http_404_content>
    53ea:	4c 89 ea             	mov    %r13,%rdx
    53ed:	44 89 e6             	mov    %r12d,%esi
    53f0:	e8 db fd ff ff       	call   51d0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    53f5:	4c 89 f2             	mov    %r14,%rdx
    53f8:	bf 01 00 00 00       	mov    $0x1,%edi
    53fd:	31 c0                	xor    %eax,%eax
    53ff:	48 8d 35 41 2d 00 00 	lea    0x2d41(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    5406:	e8 95 d0 ff ff       	call   24a0 <__printf_chk@plt>
}
    540b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5413:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    541c:	0f 85 20 01 00 00    	jne    5542 <handle_get_method+0x202>
    5422:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5429:	5b                   	pop    %rbx
    542a:	5d                   	pop    %rbp
    542b:	41 5c                	pop    %r12
    542d:	41 5d                	pop    %r13
    542f:	41 5e                	pop    %r14
    5431:	c3                   	ret
    5432:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5438:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    543d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5445:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    544a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    544d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5455:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5458:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5460:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    546b:	e8 a0 cf ff ff       	call   2410 <__memcpy_chk@plt>
    5470:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5475:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    547a:	48 8d 35 91 2c 00 00 	lea    0x2c91(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    5481:	48 29 d9             	sub    %rbx,%rcx
    5484:	ba 0b 00 00 00       	mov    $0xb,%edx
    5489:	e8 82 cf ff ff       	call   2410 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    548e:	48 89 e6             	mov    %rsp,%rsi
    5491:	4c 89 f7             	mov    %r14,%rdi
    5494:	e8 87 cf ff ff       	call   2420 <stat@plt>
    5499:	83 f8 ff             	cmp    $0xffffffff,%eax
    549c:	0f 85 2d ff ff ff    	jne    53cf <handle_get_method+0x8f>
    54a2:	4c 89 f2             	mov    %r14,%rdx
    54a5:	48 89 e9             	mov    %rbp,%rcx
    54a8:	48 8d 35 6e 2c 00 00 	lea    0x2c6e(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    54af:	31 c0                	xor    %eax,%eax
    54b1:	bf 01 00 00 00       	mov    $0x1,%edi
    54b6:	e8 e5 cf ff ff       	call   24a0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    54bb:	48 8b 3d 4e 5b 00 00 	mov    0x5b4e(%rip),%rdi        # b010 <http_404_content>
    54c2:	4c 89 ea             	mov    %r13,%rdx
    54c5:	44 89 e6             	mov    %r12d,%esi
    54c8:	e8 03 fd ff ff       	call   51d0 <_send_static_string_content>
}
    54cd:	e9 39 ff ff ff       	jmp    540b <handle_get_method+0xcb>
    54d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    54d8:	bf 70 00 00 00       	mov    $0x70,%edi
    54dd:	e8 7e cf ff ff       	call   2460 <malloc@plt>
    54e2:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    54e5:	48 85 c0             	test   %rax,%rax
    54e8:	74 5d                	je     5547 <handle_get_method+0x207>
            req->client_socket = client_socket;
    54ea:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    54ee:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    54f3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    54f7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    54fa:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    5501:	e8 5a f5 ff ff       	call   4a60 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5506:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    550b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    550f:	4c 89 f7             	mov    %r14,%rdi
    5512:	e8 79 fa ff ff       	call   4f90 <copy_file_contents>
    5517:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    551c:	4c 89 f2             	mov    %r14,%rdx
    551f:	31 c0                	xor    %eax,%eax
    5521:	48 8d 35 0d 2c 00 00 	lea    0x2c0d(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    5528:	bf 01 00 00 00       	mov    $0x1,%edi
    552d:	e8 6e cf ff ff       	call   24a0 <__printf_chk@plt>
            add_write_request(req, ring);
    5532:	4c 89 ee             	mov    %r13,%rsi
    5535:	48 89 df             	mov    %rbx,%rdi
    5538:	e8 13 fb ff ff       	call   5050 <add_write_request>
    553d:	e9 c9 fe ff ff       	jmp    540b <handle_get_method+0xcb>
}
    5542:	e8 29 ce ff ff       	call   2370 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5547:	48 8b 0d d2 5a 00 00 	mov    0x5ad2(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    554e:	ba 28 00 00 00       	mov    $0x28,%edx
    5553:	be 01 00 00 00       	mov    $0x1,%esi
    5558:	48 8d 3d 51 30 00 00 	lea    0x3051(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    555f:	e8 bc cf ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5564:	bf 01 00 00 00       	mov    $0x1,%edi
    5569:	e8 92 cf ff ff       	call   2500 <exit@plt>
    556e:	66 90                	xchg   %ax,%ax

0000000000005570 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5570:	f3 0f 1e fa          	endbr64
    5574:	41 57                	push   %r15
    5576:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5578:	4c 8d 35 2d 2b 00 00 	lea    0x2b2d(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    557f:	41 55                	push   %r13
    5581:	49 89 d5             	mov    %rdx,%r13
    5584:	41 54                	push   %r12
    5586:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    5589:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    558c:	55                   	push   %rbp
    558d:	53                   	push   %rbx
    558e:	48 83 ec 18          	sub    $0x18,%rsp
    5592:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    559b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    55a0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    55a2:	49 89 e7             	mov    %rsp,%r15
    55a5:	4c 89 fa             	mov    %r15,%rdx
    55a8:	e8 23 ce ff ff       	call   23d0 <strtok_r@plt>
    for (; *str; ++str)
    55ad:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    55b1:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    55b4:	84 db                	test   %bl,%bl
    55b6:	74 1d                	je     55d5 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    55b8:	e8 b3 cf ff ff       	call   2570 <__ctype_tolower_loc@plt>
    55bd:	48 89 ea             	mov    %rbp,%rdx
    55c0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    55c3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    55c7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    55ca:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    55cd:	48 0f be 1a          	movsbq (%rdx),%rbx
    55d1:	84 db                	test   %bl,%bl
    55d3:	75 eb                	jne    55c0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    55d5:	4c 89 fa             	mov    %r15,%rdx
    55d8:	4c 89 f6             	mov    %r14,%rsi
    55db:	31 ff                	xor    %edi,%edi
    55dd:	e8 ee cd ff ff       	call   23d0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    55e2:	48 8d 35 71 2b 00 00 	lea    0x2b71(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    55e9:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    55ec:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    55ef:	e8 0c ce ff ff       	call   2400 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    55f4:	4c 89 ea             	mov    %r13,%rdx
    55f7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    55fa:	85 c0                	test   %eax,%eax
    55fc:	75 2a                	jne    5628 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    55fe:	48 89 df             	mov    %rbx,%rdi
    5601:	e8 3a fd ff ff       	call   5340 <handle_get_method>
}
    5606:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    560b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5614:	75 20                	jne    5636 <handle_http_method+0xc6>
    5616:	48 83 c4 18          	add    $0x18,%rsp
    561a:	5b                   	pop    %rbx
    561b:	5d                   	pop    %rbp
    561c:	41 5c                	pop    %r12
    561e:	41 5d                	pop    %r13
    5620:	41 5e                	pop    %r14
    5622:	41 5f                	pop    %r15
    5624:	c3                   	ret
    5625:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5628:	48 8b 3d e9 59 00 00 	mov    0x59e9(%rip),%rdi        # b018 <unimplemented_content>
    562f:	e8 9c fb ff ff       	call   51d0 <_send_static_string_content>
}
    5634:	eb d0                	jmp    5606 <handle_http_method+0x96>
    5636:	e8 35 cd ff ff       	call   2370 <__stack_chk_fail@plt>
    563b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005640 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5640:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5644:	85 d2                	test   %edx,%edx
    5646:	7e 38                	jle    5680 <get_line+0x40>
    5648:	48 63 d2             	movslq %edx,%rdx
    564b:	48 83 c7 01          	add    $0x1,%rdi
    564f:	48 01 f2             	add    %rsi,%rdx
    5652:	eb 11                	jmp    5665 <get_line+0x25>
    5654:	0f 1f 40 00          	nopl   0x0(%rax)
    5658:	48 83 c6 01          	add    $0x1,%rsi
    565c:	48 83 c7 01          	add    $0x1,%rdi
    5660:	48 39 d6             	cmp    %rdx,%rsi
    5663:	74 1b                	je     5680 <get_line+0x40>
        dest[i] = src[i];
    5665:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5669:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    566b:	3c 0d                	cmp    $0xd,%al
    566d:	75 e9                	jne    5658 <get_line+0x18>
    566f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5672:	75 e4                	jne    5658 <get_line+0x18>
            dest[i] = '\0';
    5674:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5677:	31 c0                	xor    %eax,%eax
    5679:	c3                   	ret
    567a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5680:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5685:	c3                   	ret
    5686:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005690 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    5690:	f3 0f 1e fa          	endbr64
    5694:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    569b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    569f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    56a8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    56b0:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    56b2:	49 89 e2             	mov    %rsp,%r10
    56b5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    56bd:	4c 89 d0             	mov    %r10,%rax
    56c0:	eb 13                	jmp    56d5 <handle_client_request+0x45>
    56c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    56c8:	48 83 c0 01          	add    $0x1,%rax
    56cc:	48 83 c1 01          	add    $0x1,%rcx
    56d0:	4c 39 c8             	cmp    %r9,%rax
    56d3:	74 4b                	je     5720 <handle_client_request+0x90>
        dest[i] = src[i];
    56d5:	44 0f b6 01          	movzbl (%rcx),%r8d
    56d9:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    56dc:	41 80 f8 0d          	cmp    $0xd,%r8b
    56e0:	75 e6                	jne    56c8 <handle_client_request+0x38>
    56e2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    56e6:	75 e0                	jne    56c8 <handle_client_request+0x38>
            dest[i] = '\0';
    56e8:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    56eb:	8b 47 08             	mov    0x8(%rdi),%eax
    56ee:	48 89 f2             	mov    %rsi,%rdx
    56f1:	4c 89 d7             	mov    %r10,%rdi
    56f4:	89 c6                	mov    %eax,%esi
    56f6:	e8 75 fe ff ff       	call   5570 <handle_http_method>
}
    56fb:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5703:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    570c:	75 39                	jne    5747 <handle_client_request+0xb7>
    570e:	31 c0                	xor    %eax,%eax
    5710:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5717:	c3                   	ret
    5718:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5720:	48 8b 0d f9 58 00 00 	mov    0x58f9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5727:	ba 12 00 00 00       	mov    $0x12,%edx
    572c:	be 01 00 00 00       	mov    $0x1,%esi
    5731:	48 8d 3d 26 2a 00 00 	lea    0x2a26(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5738:	e8 e3 cd ff ff       	call   2520 <fwrite@plt>
        exit(1);
    573d:	bf 01 00 00 00       	mov    $0x1,%edi
    5742:	e8 b9 cd ff ff       	call   2500 <exit@plt>
}
    5747:	e8 24 cc ff ff       	call   2370 <__stack_chk_fail@plt>
    574c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005750 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5750:	f3 0f 1e fa          	endbr64
    5754:	55                   	push   %rbp
    5755:	53                   	push   %rbx
    5756:	48 89 cb             	mov    %rcx,%rbx
    5759:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    575d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5760:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5763:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5769:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    576c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    576f:	f6 c1 02             	test   $0x2,%cl
    5772:	74 00                	je     5774 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    5774:	41 89 c0             	mov    %eax,%r8d
    5777:	45 29 c8             	sub    %r9d,%r8d
    577a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    577e:	0f 82 68 ce ff ff    	jb     25ec <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5784:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5787:	8b 6b 44             	mov    0x44(%rbx),%ebp
    578a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    578d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5790:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5793:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5797:	d3 e5                	shl    %cl,%ebp
    5799:	48 c1 e5 06          	shl    $0x6,%rbp
    579d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    57a1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    57a4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    57a9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    57b0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    57b4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    57b8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    57c0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    57c8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    57cc:	e8 8f cc ff ff       	call   2460 <malloc@plt>
  io_uring_submit(ring);
    57d1:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    57d4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    57da:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    57de:	48 83 c4 08          	add    $0x8,%rsp
    57e2:	5b                   	pop    %rbx
    57e3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    57e4:	e9 97 cb ff ff       	jmp    2380 <io_uring_submit@plt>
    57e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000057f0 <io_thread>:
void* io_thread(void *arg) {
    57f0:	f3 0f 1e fa          	endbr64
    57f4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    57f6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    57f8:	41 56                	push   %r14
    57fa:	41 55                	push   %r13
    57fc:	41 54                	push   %r12
    57fe:	55                   	push   %rbp
    57ff:	48 89 fd             	mov    %rdi,%rbp
    5802:	53                   	push   %rbx
    5803:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    580a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5813:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    581b:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    581f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5824:	bf 00 01 00 00       	mov    $0x100,%edi
    5829:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    582c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5830:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5835:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    583a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    583f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5844:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    584c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5851:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5859:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    585e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5866:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    586b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5873:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5878:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5880:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5885:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    588d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5895:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    589d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    58a5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    58ad:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    58b5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    58bd:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    58c5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    58cd:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    58d5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    58dd:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    58e4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    58ec:	e8 4f cb ff ff       	call   2440 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    58f1:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    58f5:	31 f6                	xor    %esi,%esi
    58f7:	e8 44 cc ff ff       	call   2540 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    58fc:	31 d2                	xor    %edx,%edx
    58fe:	be 01 00 00 00       	mov    $0x1,%esi
    5903:	bf 02 00 00 00       	mov    $0x2,%edi
    5908:	e8 83 cc ff ff       	call   2590 <socket@plt>
  if (sock == -1)
    590d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5910:	0f 84 18 cd ff ff    	je     262e <io_thread.cold+0x38>
  if (setsockopt(sock,
    5916:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    591b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5921:	89 c7                	mov    %eax,%edi
    5923:	41 89 c4             	mov    %eax,%r12d
    5926:	ba 02 00 00 00       	mov    $0x2,%edx
    592b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5930:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5938:	e8 f3 c9 ff ff       	call   2330 <setsockopt@plt>
    593d:	85 c0                	test   %eax,%eax
    593f:	0f 88 bd cc ff ff    	js     2602 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5945:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    594a:	ba 10 00 00 00       	mov    $0x10,%edx
    594f:	44 89 e7             	mov    %r12d,%edi
    5952:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    595b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5963:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    596b:	e8 40 cb ff ff       	call   24b0 <bind@plt>
    5970:	85 c0                	test   %eax,%eax
    5972:	0f 88 c2 cc ff ff    	js     263a <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5978:	be 0a 00 00 00       	mov    $0xa,%esi
    597d:	44 89 e7             	mov    %r12d,%edi
    5980:	e8 eb ca ff ff       	call   2470 <listen@plt>
    5985:	85 c0                	test   %eax,%eax
    5987:	0f 88 81 cc ff ff    	js     260e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    598d:	ba db 18 00 00       	mov    $0x18db,%edx
    5992:	48 8d 35 0a 28 00 00 	lea    0x280a(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5999:	bf 01 00 00 00       	mov    $0x1,%edi
    599e:	31 c0                	xor    %eax,%eax
    59a0:	e8 fb ca ff ff       	call   24a0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    59a5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    59aa:	48 89 d9             	mov    %rbx,%rcx
    59ad:	44 89 e7             	mov    %r12d,%edi
    59b0:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    59b5:	48 89 c6             	mov    %rax,%rsi
    59b8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    59bd:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    59c2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    59ca:	e8 81 fd ff ff       	call   5750 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    59cf:	bf 01 00 00 00       	mov    $0x1,%edi
    59d4:	be 10 00 00 00       	mov    $0x10,%esi
    59d9:	e8 12 ca ff ff       	call   23f0 <calloc@plt>
    void *buf = malloc(size);
    59de:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    59e3:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    59e6:	e8 75 ca ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    59eb:	48 85 c0             	test   %rax,%rax
    59ee:	0f 84 ae 04 00 00    	je     5ea2 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    59f4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    59f8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    59ff:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5a06:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5a0e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5a11:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5a16:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5a18:	f6 c1 02             	test   $0x2,%cl
    5a1b:	0f 85 0f 04 00 00    	jne    5e30 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5a21:	89 d0                	mov    %edx,%eax
    5a23:	29 f0                	sub    %esi,%eax
    5a25:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5a2c:	0f 82 f2 cb ff ff    	jb     2624 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5a32:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5a35:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5a39:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5a3d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a40:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5a47:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a4a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5a51:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a58:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5a5a:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5a5d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5a62:	48 c1 e0 06          	shl    $0x6,%rax
    5a66:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5a6e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5a74:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5a77:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5a7f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5a83:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5a8b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5a93:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5a97:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5a9b:	e8 e0 c8 ff ff       	call   2380 <io_uring_submit@plt>
  while (data->running == 1) {
    5aa0:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5aa4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5aa9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5ab1:	0f 85 d7 01 00 00    	jne    5c8e <io_thread+0x49e>
    5ab7:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5abc:	4d 89 ce             	mov    %r9,%r14
    5abf:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5ac4:	0f 1f 40 00          	nopl   0x0(%rax)
    5ac8:	48 8d 3d ea 26 00 00 	lea    0x26ea(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5acf:	e8 4c c8 ff ff       	call   2320 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5ad4:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5adb:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5ae2:	c1 e9 0b             	shr    $0xb,%ecx
    5ae5:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5ae8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5af0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5af2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5afa:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5afc:	39 d0                	cmp    %edx,%eax
    5afe:	74 36                	je     5b36 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5b00:	89 f8                	mov    %edi,%eax
    5b02:	21 d0                	and    %edx,%eax
    5b04:	d3 e0                	shl    %cl,%eax
    5b06:	48 c1 e0 04          	shl    $0x4,%rax
    5b0a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5b12:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5b1a:	0f 85 a8 01 00 00    	jne    5cc8 <io_thread+0x4d8>
    5b20:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5b24:	0f 85 0e 03 00 00    	jne    5e38 <io_thread+0x648>
			if (cqe->res < 0)
    5b2a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5b2d:	83 c2 01             	add    $0x1,%edx
    5b30:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5b32:	85 c0                	test   %eax,%eax
    5b34:	79 b2                	jns    5ae8 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5b36:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    5b3f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5b40:	45 31 c0             	xor    %r8d,%r8d
    5b43:	31 d2                	xor    %edx,%edx
    5b45:	b9 01 00 00 00       	mov    $0x1,%ecx
    5b4a:	4c 89 f6             	mov    %r14,%rsi
    5b4d:	48 89 df             	mov    %rbx,%rdi
    5b50:	e8 3b c9 ff ff       	call   2490 <__io_uring_get_cqe@plt>
    5b55:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5b58:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5b5d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5b61:	0f 84 e1 02 00 00    	je     5e48 <io_thread+0x658>
    5b67:	48 8d 3d 71 26 00 00 	lea    0x2671(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5b6e:	e8 ad c7 ff ff       	call   2320 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5b73:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5b78:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5b7b:	45 85 ff             	test   %r15d,%r15d
    5b7e:	0f 88 72 ca ff ff    	js     25f6 <io_thread.cold>
      if (cqe->res < 0) {
    5b84:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5b87:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    5b8b:	85 c0                	test   %eax,%eax
    5b8d:	0f 88 d5 02 00 00    	js     5e68 <io_thread+0x678>
      switch (req->event_type) {
    5b93:	41 83 f8 01          	cmp    $0x1,%r8d
    5b97:	0f 84 7b 01 00 00    	je     5d18 <io_thread+0x528>
    5b9d:	41 83 f8 02          	cmp    $0x2,%r8d
    5ba1:	0f 84 a1 01 00 00    	je     5d48 <io_thread+0x558>
    5ba7:	45 85 c0             	test   %r8d,%r8d
    5baa:	0f 85 50 01 00 00    	jne    5d00 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5bb0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5bb5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5bba:	48 89 d9             	mov    %rbx,%rcx
    5bbd:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5bc1:	e8 8a fb ff ff       	call   5750 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5bc6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5bcb:	48 89 de             	mov    %rbx,%rsi
    5bce:	8b 78 08             	mov    0x8(%rax),%edi
    5bd1:	e8 1a f5 ff ff       	call   50f0 <add_read_request>
              free(req);
    5bd6:	4c 89 e7             	mov    %r12,%rdi
    5bd9:	e8 12 c7 ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5bde:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5be3:	48 85 c0             	test   %rax,%rax
    5be6:	0f 85 14 01 00 00    	jne    5d00 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    5bec:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5bf3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5bfa:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5bfd:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5c02:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5c04:	f6 c1 02             	test   $0x2,%cl
    5c07:	74 00                	je     5c09 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5c09:	89 d0                	mov    %edx,%eax
    5c0b:	29 f0                	sub    %esi,%eax
    5c0d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5c14:	0f 82 00 ca ff ff    	jb     261a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5c1a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    5c1d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5c22:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5c26:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5c29:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5c30:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5c33:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5c3a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5c41:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5c43:	8b 55 60             	mov    0x60(%rbp),%edx
    5c46:	48 c1 e0 06          	shl    $0x6,%rax
    5c4a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5c52:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5c58:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5c5b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5c63:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5c67:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5c6f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5c77:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5c7b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5c7f:	e8 fc c6 ff ff       	call   2380 <io_uring_submit@plt>
  while (data->running == 1) {
    5c84:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5c88:	0f 84 3a fe ff ff    	je     5ac8 <io_thread+0x2d8>
    5c8e:	48 8d 3d 83 25 00 00 	lea    0x2583(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5c95:	e8 86 c6 ff ff       	call   2320 <puts@plt>
}
    5c9a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5ca2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5cab:	0f 85 18 02 00 00    	jne    5ec9 <io_thread+0x6d9>
    5cb1:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5cb8:	31 c0                	xor    %eax,%eax
    5cba:	5b                   	pop    %rbx
    5cbb:	5d                   	pop    %rbp
    5cbc:	41 5c                	pop    %r12
    5cbe:	41 5d                	pop    %r13
    5cc0:	41 5e                	pop    %r14
    5cc2:	41 5f                	pop    %r15
    5cc4:	c3                   	ret
    5cc5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5cc8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5ccd:	48 85 c0             	test   %rax,%rax
    5cd0:	0f 84 6a fe ff ff    	je     5b40 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5cd6:	48 83 38 01          	cmpq   $0x1,(%rax)
    5cda:	0f 84 68 01 00 00    	je     5e48 <io_thread+0x658>
    5ce0:	48 8d 3d f8 24 00 00 	lea    0x24f8(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5ce7:	e8 34 c6 ff ff       	call   2320 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5cec:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5cf1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5cf4:	e9 8b fe ff ff       	jmp    5b84 <io_thread+0x394>
    5cf9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5d00:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5d08:	8b 02                	mov    (%rdx),%eax
    5d0a:	83 c0 01             	add    $0x1,%eax
    5d0d:	89 02                	mov    %eax,(%rdx)
}
    5d0f:	e9 d8 fe ff ff       	jmp    5bec <io_thread+0x3fc>
    5d14:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5d18:	85 c0                	test   %eax,%eax
    5d1a:	75 74                	jne    5d90 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5d1c:	48 8b 0d fd 52 00 00 	mov    0x52fd(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5d23:	ba 0f 00 00 00       	mov    $0xf,%edx
    5d28:	be 01 00 00 00       	mov    $0x1,%esi
    5d2d:	48 8d 3d d4 24 00 00 	lea    0x24d4(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    5d34:	e8 e7 c7 ff ff       	call   2520 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5d39:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5d3e:	e9 a0 fe ff ff       	jmp    5be3 <io_thread+0x3f3>
    5d43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5d48:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5d4d:	45 31 ff             	xor    %r15d,%r15d
    5d50:	85 c0                	test   %eax,%eax
    5d52:	7e 20                	jle    5d74 <io_thread+0x584>
    5d54:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5d58:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5d5b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    5d5f:	48 c1 e0 04          	shl    $0x4,%rax
    5d63:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5d68:	e8 83 c5 ff ff       	call   22f0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5d6d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5d72:	7f e4                	jg     5d58 <io_thread+0x568>
              close(req->client_socket);
    5d74:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5d79:	e8 42 c6 ff ff       	call   23c0 <close@plt>
              free(req);
    5d7e:	4c 89 e7             	mov    %r12,%rdi
    5d81:	e8 6a c5 ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5d86:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5d8b:	e9 53 fe ff ff       	jmp    5be3 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5d90:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5d95:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5d9a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5da2:	eb 11                	jmp    5db5 <io_thread+0x5c5>
    5da4:	0f 1f 40 00          	nopl   0x0(%rax)
    5da8:	48 83 c0 01          	add    $0x1,%rax
    5dac:	48 83 c2 01          	add    $0x1,%rdx
    5db0:	48 39 c6             	cmp    %rax,%rsi
    5db3:	74 4b                	je     5e00 <io_thread+0x610>
        dest[i] = src[i];
    5db5:	0f b6 0a             	movzbl (%rdx),%ecx
    5db8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5dba:	80 f9 0d             	cmp    $0xd,%cl
    5dbd:	75 e9                	jne    5da8 <io_thread+0x5b8>
    5dbf:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5dc3:	75 e3                	jne    5da8 <io_thread+0x5b8>
            dest[i] = '\0';
    5dc5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5dc8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    5dcd:	48 89 da             	mov    %rbx,%rdx
    5dd0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5dd5:	e8 96 f7 ff ff       	call   5570 <handle_http_method>
              free(req->iov[0].iov_base);
    5dda:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    5ddf:	e8 0c c5 ff ff       	call   22f0 <free@plt>
              free(req);
    5de4:	4c 89 e7             	mov    %r12,%rdi
    5de7:	e8 04 c5 ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5dec:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5df1:	e9 ed fd ff ff       	jmp    5be3 <io_thread+0x3f3>
    5df6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5e00:	48 8b 0d 19 52 00 00 	mov    0x5219(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5e07:	ba 12 00 00 00       	mov    $0x12,%edx
    5e0c:	be 01 00 00 00       	mov    $0x1,%esi
    5e11:	48 8d 3d 46 23 00 00 	lea    0x2346(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5e18:	e8 03 c7 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5e1d:	bf 01 00 00 00       	mov    $0x1,%edi
    5e22:	e8 d9 c6 ff ff       	call   2500 <exit@plt>
    5e27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5e30:	e9 ec fb ff ff       	jmp    5a21 <io_thread+0x231>
    5e35:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5e38:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    5e3d:	e9 94 fe ff ff       	jmp    5cd6 <io_thread+0x4e6>
    5e42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5e48:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5e50:	48 8d 3d 74 23 00 00 	lea    0x2374(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    5e57:	8b 02                	mov    (%rdx),%eax
    5e59:	83 c0 01             	add    $0x1,%eax
    5e5c:	89 02                	mov    %eax,(%rdx)
    5e5e:	e8 bd c4 ff ff       	call   2320 <puts@plt>
    5e63:	e9 26 fe ff ff       	jmp    5c8e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5e68:	f7 d8                	neg    %eax
    5e6a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5e6f:	89 c7                	mov    %eax,%edi
    5e71:	e8 ea c6 ff ff       	call   2560 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5e76:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5e7b:	be 01 00 00 00       	mov    $0x1,%esi
    5e80:	48 8b 3d 99 51 00 00 	mov    0x5199(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    5e87:	48 89 c1             	mov    %rax,%rcx
    5e8a:	48 8d 15 4f 27 00 00 	lea    0x274f(%rip),%rdx        # 85e0 <_IO_stdin_used+0x5e0>
    5e91:	31 c0                	xor    %eax,%eax
    5e93:	e8 98 c6 ff ff       	call   2530 <__fprintf_chk@plt>
          exit(1);
    5e98:	bf 01 00 00 00       	mov    $0x1,%edi
    5e9d:	e8 5e c6 ff ff       	call   2500 <exit@plt>
    5ea2:	48 8b 0d 77 51 00 00 	mov    0x5177(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5ea9:	ba 28 00 00 00       	mov    $0x28,%edx
    5eae:	be 01 00 00 00       	mov    $0x1,%esi
    5eb3:	48 8d 3d f6 26 00 00 	lea    0x26f6(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    5eba:	e8 61 c6 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5ebf:	bf 01 00 00 00       	mov    $0x1,%edi
    5ec4:	e8 37 c6 ff ff       	call   2500 <exit@plt>
}
    5ec9:	e8 a2 c4 ff ff       	call   2370 <__stack_chk_fail@plt>
    5ece:	66 90                	xchg   %ax,%ax

0000000000005ed0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5ed0:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5ed4:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5edb:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5ee1:	85 c9                	test   %ecx,%ecx
    5ee3:	0f 8e ea 00 00 00    	jle    5fd3 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    5ee9:	41 56                	push   %r14
    5eeb:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5eed:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    5ef0:	41 54                	push   %r12
    5ef2:	49 89 fc             	mov    %rdi,%r12
    5ef5:	55                   	push   %rbp
    5ef6:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5ef7:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5efb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5f00:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    5f04:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    5f0c:	31 db                	xor    %ebx,%ebx
    5f0e:	8b 10                	mov    (%rax),%edx
    5f10:	85 d2                	test   %edx,%edx
    5f12:	7e 26                	jle    5f3a <barriered_work_ingest+0x6a>
    5f14:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    5f18:	48 89 dd             	mov    %rbx,%rbp
    5f1b:	48 c1 e5 08          	shl    $0x8,%rbp
    5f1f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    5f23:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    5f2a:	74 24                	je     5f50 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5f2c:	48 83 c3 01          	add    $0x1,%rbx
    5f30:	39 da                	cmp    %ebx,%edx
    5f32:	7f e4                	jg     5f18 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5f34:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5f3a:	49 83 c5 01          	add    $0x1,%r13
    5f3e:	44 39 e9             	cmp    %r13d,%ecx
    5f41:	7f bd                	jg     5f00 <barriered_work_ingest+0x30>
}
    5f43:	5b                   	pop    %rbx
    5f44:	31 c0                	xor    %eax,%eax
    5f46:	5d                   	pop    %rbp
    5f47:	41 5c                	pop    %r12
    5f49:	41 5d                	pop    %r13
    5f4b:	41 5e                	pop    %r14
    5f4d:	c3                   	ret
    5f4e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    5f50:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5f59:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5f60:	bf 04 00 00 00       	mov    $0x4,%edi
    5f65:	48 c1 e6 05          	shl    $0x5,%rsi
    5f69:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5f70:	48 83 c6 10          	add    $0x10,%rsi
    5f74:	e8 c7 c3 ff ff       	call   2340 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5f79:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5f81:	48 8b 40 50          	mov    0x50(%rax),%rax
    5f85:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5f89:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    5f8d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5f97:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    5f9d:	83 c0 01             	add    $0x1,%eax
    5fa0:	99                   	cltd
    5fa1:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5fa7:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    5fad:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5fb0:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5fb8:	48 83 c3 01          	add    $0x1,%rbx
    5fbc:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5fc0:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5fc4:	8b 10                	mov    (%rax),%edx
    5fc6:	39 da                	cmp    %ebx,%edx
    5fc8:	0f 8f 46 ff ff ff    	jg     5f14 <barriered_work_ingest+0x44>
    5fce:	e9 61 ff ff ff       	jmp    5f34 <barriered_work_ingest+0x64>
}
    5fd3:	31 c0                	xor    %eax,%eax
    5fd5:	c3                   	ret
    5fd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005fe0 <barriered_thread>:
void* barriered_thread(void *arg) {
    5fe0:	f3 0f 1e fa          	endbr64
    5fe4:	41 56                	push   %r14
    5fe6:	41 55                	push   %r13
    5fe8:	41 54                	push   %r12
  int t = 0;
    5fea:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    5fed:	55                   	push   %rbp
  int waiting = 0;
    5fee:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    5ff0:	53                   	push   %rbx
    5ff1:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    5ff4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5ff8:	0f 85 74 02 00 00    	jne    6272 <barriered_thread+0x292>
    if (t >= data->task_count) {
    5ffe:	8b 43 40             	mov    0x40(%rbx),%eax
    6001:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6008:	41 39 c4             	cmp    %eax,%r12d
    600b:	0f 8d 6f 01 00 00    	jge    6180 <barriered_thread+0x1a0>
    6011:	49 63 fc             	movslq %r12d,%rdi
    6014:	48 c1 e7 09          	shl    $0x9,%rdi
    6018:	49 89 fd             	mov    %rdi,%r13
    601b:	eb 32                	jmp    604f <barriered_thread+0x6f>
    601d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    6020:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6024:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6028:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    602c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6030:	4c 01 ef             	add    %r13,%rdi
    6033:	e8 98 fe ff ff       	call   5ed0 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    6038:	8b 43 40             	mov    0x40(%rbx),%eax
    603b:	41 83 c4 01          	add    $0x1,%r12d
    603f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    6046:	44 39 e0             	cmp    %r12d,%eax
    6049:	0f 8e 19 02 00 00    	jle    6268 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    604f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6053:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    6057:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    605e:	75 c0                	jne    6020 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6060:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    6064:	83 e8 01             	sub    $0x1,%eax
    6067:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    606c:	45 85 e4             	test   %r12d,%r12d
    606f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6072:	45 85 c0             	test   %r8d,%r8d
    6075:	0f 8e 2d 01 00 00    	jle    61a8 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    607b:	48 63 c8             	movslq %eax,%rcx
    607e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6082:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    6085:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    608b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    6092:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    6096:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    6099:	45 31 f6             	xor    %r14d,%r14d
    609c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    60a0:	48 8b 10             	mov    (%rax),%rdx
    60a3:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    60a7:	49 01 cb             	add    %rcx,%r11
    60aa:	4c 89 da             	mov    %r11,%rdx
    60ad:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    60b4:	75 04                	jne    60ba <barriered_thread+0xda>
            arrived++;
    60b6:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    60ba:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    60c0:	75 04                	jne    60c6 <barriered_thread+0xe6>
            prearrive++;
    60c2:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    60c6:	48 83 c0 08          	add    $0x8,%rax
    60ca:	48 39 c6             	cmp    %rax,%rsi
    60cd:	75 d1                	jne    60a0 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    60cf:	45 85 d2             	test   %r10d,%r10d
    60d2:	0f 84 c0 00 00 00    	je     6198 <barriered_thread+0x1b8>
    60d8:	45 39 d0             	cmp    %r10d,%r8d
    60db:	0f 84 b7 00 00 00    	je     6198 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    60e1:	45 85 f6             	test   %r14d,%r14d
    60e4:	74 0a                	je     60f0 <barriered_thread+0x110>
    60e6:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    60ea:	0f 85 ae 01 00 00    	jne    629e <barriered_thread+0x2be>
    60f0:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    60f4:	4c 01 ea             	add    %r13,%rdx
    60f7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    60fe:	45 85 e4             	test   %r12d,%r12d
    6101:	75 14                	jne    6117 <barriered_thread+0x137>
    6103:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    610a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    6111:	0f 8c 69 01 00 00    	jl     6280 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6117:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    611b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    611f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6129:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    612d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6131:	4c 01 ef             	add    %r13,%rdi
    6134:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    613a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    613e:	4c 01 e8             	add    %r13,%rax
    6141:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6148:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    614b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6150:	83 e8 01             	sub    $0x1,%eax
    6153:	44 39 e0             	cmp    %r12d,%eax
    6156:	0f 84 a4 00 00 00    	je     6200 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    615c:	0f ae f8             	sfence
          if (waiting == 0) {
    615f:	85 ed                	test   %ebp,%ebp
    6161:	0f 84 d1 00 00 00    	je     6238 <barriered_thread+0x258>
        int arrived = 0; 
    6167:	bd 01 00 00 00       	mov    $0x1,%ebp
    616c:	e9 c7 fe ff ff       	jmp    6038 <barriered_thread+0x58>
  while (data->running == 1) {
    6171:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6175:	0f 85 f7 00 00 00    	jne    6272 <barriered_thread+0x292>
    617b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    6180:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    6188:	85 c0                	test   %eax,%eax
    618a:	7e e5                	jle    6171 <barriered_thread+0x191>
    618c:	45 31 e4             	xor    %r12d,%r12d
    618f:	e9 7d fe ff ff       	jmp    6011 <barriered_thread+0x31>
    6194:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6198:	83 fd 01             	cmp    $0x1,%ebp
    619b:	74 1b                	je     61b8 <barriered_thread+0x1d8>
        int arrived = 0; 
    619d:	31 ed                	xor    %ebp,%ebp
    619f:	e9 3d ff ff ff       	jmp    60e1 <barriered_thread+0x101>
    61a4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    61a8:	83 fd 01             	cmp    $0x1,%ebp
    61ab:	0f 85 43 ff ff ff    	jne    60f4 <barriered_thread+0x114>
        int arrived = 0; 
    61b1:	45 31 f6             	xor    %r14d,%r14d
    61b4:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    61b8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    61bf:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    61c4:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    61c6:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    61ca:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    61d1:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    61d6:	e8 65 c1 ff ff       	call   2340 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    61db:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    61e2:	48 83 c0 01          	add    $0x1,%rax
    61e6:	48 99                	cqto
    61e8:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    61ef:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    61f6:	e9 e6 fe ff ff       	jmp    60e1 <barriered_thread+0x101>
    61fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6200:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6207:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    620e:	0f 8d 48 ff ff ff    	jge    615c <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    6214:	48 c1 e6 04          	shl    $0x4,%rsi
    6218:	bf 04 00 00 00       	mov    $0x4,%edi
    621d:	48 03 73 70          	add    0x70(%rbx),%rsi
    6221:	e8 1a c1 ff ff       	call   2340 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    6226:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    622e:	e9 29 ff ff ff       	jmp    615c <barriered_thread+0x17c>
    6233:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    6238:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    623f:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    6244:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6248:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    624f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    6253:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    6257:	e8 e4 c0 ff ff       	call   2340 <clock_gettime@plt>
            waiting = 1;
    625c:	e9 06 ff ff ff       	jmp    6167 <barriered_thread+0x187>
    6261:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    6268:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    626c:	0f 84 96 fd ff ff    	je     6008 <barriered_thread+0x28>
}
    6272:	5b                   	pop    %rbx
    6273:	31 c0                	xor    %eax,%eax
    6275:	5d                   	pop    %rbp
    6276:	41 5c                	pop    %r12
    6278:	41 5d                	pop    %r13
    627a:	41 5e                	pop    %r14
    627c:	c3                   	ret
    627d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    6280:	48 c1 e6 04          	shl    $0x4,%rsi
    6284:	bf 04 00 00 00       	mov    $0x4,%edi
    6289:	48 03 73 68          	add    0x68(%rbx),%rsi
    628d:	e8 ae c0 ff ff       	call   2340 <clock_gettime@plt>
          data->tasks[t].available = 0;
    6292:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6296:	4c 01 ea             	add    %r13,%rdx
    6299:	e9 79 fe ff ff       	jmp    6117 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    629e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    62a2:	48 8b 43 18          	mov    0x18(%rbx),%rax
    62a6:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    62aa:	48 8b 78 38          	mov    0x38(%rax),%rdi
    62ae:	4c 01 ef             	add    %r13,%rdi
    62b1:	e8 1a fc ff ff       	call   5ed0 <barriered_work_ingest>
          break;
    62b6:	e9 39 fd ff ff       	jmp    5ff4 <barriered_thread+0x14>
    62bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000062c0 <receive>:
int receive(struct BarrierTask *data) {
    62c0:	f3 0f 1e fa          	endbr64
    62c4:	41 57                	push   %r15
    62c6:	41 56                	push   %r14
    62c8:	41 55                	push   %r13
    62ca:	41 54                	push   %r12
    62cc:	55                   	push   %rbp
    62cd:	53                   	push   %rbx
    62ce:	48 83 ec 08          	sub    $0x8,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    62d2:	44 8b b7 40 01 00 00 	mov    0x140(%rdi),%r14d
    62d9:	45 85 f6             	test   %r14d,%r14d
    62dc:	0f 8e 37 01 00 00    	jle    6419 <receive+0x159>
    if (n == data->thread->real_thread_index) { continue; }
    62e2:	4c 8b bf 28 01 00 00 	mov    0x128(%rdi),%r15
    62e9:	48 89 f9             	mov    %rdi,%rcx
    62ec:	45 31 e4             	xor    %r12d,%r12d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    62ef:	31 db                	xor    %ebx,%ebx
    if (n == data->thread->real_thread_index) { continue; }
    62f1:	49 63 6f 08          	movslq 0x8(%r15),%rbp
    62f5:	49 89 ed             	mov    %rbp,%r13
    62f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6300:	41 39 dd             	cmp    %ebx,%r13d
    6303:	0f 84 00 01 00 00    	je     6409 <receive+0x149>
    struct Data *me = data->mailboxes[n].lower;
    6309:	48 8b 81 70 01 00 00 	mov    0x170(%rcx),%rax
    6310:	4a 8b 34 20          	mov    (%rax,%r12,1),%rsi
    if (me->available_reading == 1) {
    6314:	8b 86 00 02 00 00    	mov    0x200(%rsi),%eax
    631a:	83 f8 01             	cmp    $0x1,%eax
    631d:	74 11                	je     6330 <receive+0x70>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    631f:	83 be 18 03 00 00 02 	cmpl   $0x2,0x318(%rsi)
    6326:	75 08                	jne    6330 <receive+0x70>
    6328:	85 c0                	test   %eax,%eax
    632a:	0f 84 d9 00 00 00    	je     6409 <receive+0x149>
    for (int x = 0 ; x < me->messages_count ; x++) {
    6330:	48 8b be 80 00 00 00 	mov    0x80(%rsi),%rdi
    6337:	48 85 ff             	test   %rdi,%rdi
    633a:	0f 8e a0 00 00 00    	jle    63e0 <receive+0x120>
      data->sends++;
    6340:	48 8b 91 78 01 00 00 	mov    0x178(%rcx),%rdx
    6347:	4c 8b 06             	mov    (%rsi),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    634a:	4c 63 59 04          	movslq 0x4(%rcx),%r11
    634e:	49 89 d1             	mov    %rdx,%r9
    6351:	48 8d 42 01          	lea    0x1(%rdx),%rax
    6355:	49 f7 d9             	neg    %r9
    6358:	48 01 c7             	add    %rax,%rdi
    635b:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    635f:	4c 8b 89 08 01 00 00 	mov    0x108(%rcx),%r9
      me->received++;
    6366:	4c 8b 86 10 03 00 00 	mov    0x310(%rsi),%r8
      data->n++;
    636d:	49 29 d1             	sub    %rdx,%r9
      me->received++;
    6370:	49 29 d0             	sub    %rdx,%r8
    6373:	eb 0c                	jmp    6381 <receive+0xc1>
    6375:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    6378:	48 83 c0 01          	add    $0x1,%rax
    637c:	48 39 c7             	cmp    %rax,%rdi
    637f:	74 5f                	je     63e0 <receive+0x120>
      data->n++;
    6381:	49 8d 14 01          	lea    (%r9,%rax,1),%rdx
      data->sends++;
    6385:	48 89 81 78 01 00 00 	mov    %rax,0x178(%rcx)
      data->n++;
    638c:	48 89 91 08 01 00 00 	mov    %rdx,0x108(%rcx)
      me->received++;
    6393:	49 8d 14 00          	lea    (%r8,%rax,1),%rdx
    6397:	48 89 96 10 03 00 00 	mov    %rdx,0x310(%rsi)
      if (me->messages[x]->group == data->group) {
    639e:	49 8b 54 c2 f8       	mov    -0x8(%r10,%rax,8),%rdx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    63a3:	4c 39 5a 10          	cmp    %r11,0x10(%rdx)
    63a7:	75 cf                	jne    6378 <receive+0xb8>
    63a9:	48 39 6a 08          	cmp    %rbp,0x8(%rdx)
    63ad:	75 c9                	jne    6378 <receive+0xb8>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    63af:	49 63 47 04          	movslq 0x4(%r15),%rax
    63b3:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    63b5:	bf 01 00 00 00       	mov    $0x1,%edi
    63ba:	ba 01 00 00 00       	mov    $0x1,%edx
    63bf:	48 8d 35 42 22 00 00 	lea    0x2242(%rip),%rsi        # 8608 <_IO_stdin_used+0x608>
    63c6:	48 39 e8             	cmp    %rbp,%rax
    63c9:	0f 94 c1             	sete   %cl
    63cc:	31 c0                	xor    %eax,%eax
    63ce:	e8 cd c0 ff ff       	call   24a0 <__printf_chk@plt>
        exit(1);
    63d3:	bf 01 00 00 00       	mov    $0x1,%edi
    63d8:	e8 23 c1 ff ff       	call   2500 <exit@plt>
    63dd:	0f 1f 00             	nopl   (%rax)
    me->messages_count = 0;
    63e0:	48 c7 86 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rsi)
      me->available_reading = 0;
    63eb:	c7 86 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi)
      me->finished_reading = 1;
    63f5:	c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rsi)
      me->available_sending = 1;
    63ff:	c7 86 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rsi)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6409:	83 c3 01             	add    $0x1,%ebx
    640c:	49 83 c4 38          	add    $0x38,%r12
    6410:	44 39 f3             	cmp    %r14d,%ebx
    6413:	0f 85 e7 fe ff ff    	jne    6300 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    6419:	0f ae f8             	sfence
}
    641c:	48 83 c4 08          	add    $0x8,%rsp
    6420:	31 c0                	xor    %eax,%eax
    6422:	5b                   	pop    %rbx
    6423:	5d                   	pop    %rbp
    6424:	41 5c                	pop    %r12
    6426:	41 5d                	pop    %r13
    6428:	41 5e                	pop    %r14
    642a:	41 5f                	pop    %r15
    642c:	c3                   	ret
    642d:	0f 1f 00             	nopl   (%rax)

0000000000006430 <sendm>:
int sendm(struct BarrierTask *data) {
    6430:	f3 0f 1e fa          	endbr64
    6434:	41 57                	push   %r15
    6436:	41 56                	push   %r14
    6438:	41 55                	push   %r13
    643a:	41 54                	push   %r12
    643c:	55                   	push   %rbp
    643d:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    643e:	44 8b a7 40 01 00 00 	mov    0x140(%rdi),%r12d
    6445:	45 85 e4             	test   %r12d,%r12d
    6448:	0f 8e ae 00 00 00    	jle    64fc <sendm+0xcc>
        if (n == data->thread->real_thread_index) { continue; }
    644e:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    6455:	48 89 fe             	mov    %rdi,%rsi
    6458:	31 d2                	xor    %edx,%edx
    645a:	44 8b 68 08          	mov    0x8(%rax),%r13d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    645e:	31 c0                	xor    %eax,%eax
    6460:	eb 38                	jmp    649a <sendm+0x6a>
    6462:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          data->mailboxes[n].higher = them;
    6468:	4c 89 47 08          	mov    %r8,0x8(%rdi)
          them = data->mailboxes[n].pending;
    646c:	4c 89 c1             	mov    %r8,%rcx
          data->mailboxes[n].pending = NULL;
    646f:	48 c7 47 10 00 00 00 00 	movq   $0x0,0x10(%rdi)
        if (them->messages_count > 0) {
    6477:	49 8b b8 80 00 00 00 	mov    0x80(%r8),%rdi
          them->available_sending = 1;
    647e:	41 c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r8)
        if (them->messages_count > 0) {
    6489:	48 85 ff             	test   %rdi,%rdi
    648c:	7e 4f                	jle    64dd <sendm+0xad>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    648e:	83 c0 01             	add    $0x1,%eax
    6491:	48 83 c2 38          	add    $0x38,%rdx
    6495:	44 39 e0             	cmp    %r12d,%eax
    6498:	74 62                	je     64fc <sendm+0xcc>
        if (n == data->thread->real_thread_index) { continue; }
    649a:	41 39 c5             	cmp    %eax,%r13d
    649d:	74 ef                	je     648e <sendm+0x5e>
        struct Data *them = data->mailboxes[n].higher;
    649f:	48 8b be 70 01 00 00 	mov    0x170(%rsi),%rdi
    64a6:	48 01 d7             	add    %rdx,%rdi
        if (data->mailboxes[n].pending != NULL) {
    64a9:	4c 8b 47 10          	mov    0x10(%rdi),%r8
        struct Data *them = data->mailboxes[n].higher;
    64ad:	48 8b 4f 08          	mov    0x8(%rdi),%rcx
        if (data->mailboxes[n].pending != NULL) {
    64b1:	4d 85 c0             	test   %r8,%r8
    64b4:	75 b2                	jne    6468 <sendm+0x38>
        if (them->messages_count > 0) {
    64b6:	48 8b b9 80 00 00 00 	mov    0x80(%rcx),%rdi
    64bd:	48 85 ff             	test   %rdi,%rdi
    64c0:	7f cc                	jg     648e <sendm+0x5e>
        if (them->available_sending == 1) {
    64c2:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    64c9:	41 83 f8 01          	cmp    $0x1,%r8d
    64cd:	74 0e                	je     64dd <sendm+0xad>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    64cf:	83 b9 18 03 00 00 02 	cmpl   $0x2,0x318(%rcx)
    64d6:	75 05                	jne    64dd <sendm+0xad>
    64d8:	45 85 c0             	test   %r8d,%r8d
    64db:	74 b1                	je     648e <sendm+0x5e>
        if (data->sending == 1) {
    64dd:	83 be 80 01 00 00 01 	cmpl   $0x1,0x180(%rsi)
    64e4:	74 2a                	je     6510 <sendm+0xe0>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    64e6:	83 c0 01             	add    $0x1,%eax
    64e9:	48 83 c2 38          	add    $0x38,%rdx
          them->available_receiving = 1;
    64ed:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    64f7:	44 39 e0             	cmp    %r12d,%eax
    64fa:	75 9e                	jne    649a <sendm+0x6a>
      asm volatile ("sfence" ::: "memory");
    64fc:	0f ae f8             	sfence
}
    64ff:	31 c0                	xor    %eax,%eax
    6501:	5b                   	pop    %rbx
    6502:	5d                   	pop    %rbp
    6503:	41 5c                	pop    %r12
    6505:	41 5d                	pop    %r13
    6507:	41 5e                	pop    %r14
    6509:	41 5f                	pop    %r15
    650b:	c3                   	ret
    650c:	0f 1f 40 00          	nopl   0x0(%rax)
          for (; them->messages_count < min;) {
    6510:	48 63 99 88 00 00 00 	movslq 0x88(%rcx),%rbx
    6517:	48 39 df             	cmp    %rbx,%rdi
    651a:	0f 8d b2 00 00 00    	jge    65d2 <sendm+0x1a2>
    6520:	49 89 db             	mov    %rbx,%r11
    6523:	4c 8b be 08 01 00 00 	mov    0x108(%rsi),%r15
    652a:	4c 8b b1 08 03 00 00 	mov    0x308(%rcx),%r14
    6531:	49 29 fb             	sub    %rdi,%r11
            them->messages[them->messages_count++] = data->message; 
    6534:	4c 8b 11             	mov    (%rcx),%r10
    6537:	4d 8d 43 ff          	lea    -0x1(%r11),%r8
    653b:	4c 89 7c 24 e8       	mov    %r15,-0x18(%rsp)
    6540:	4c 89 74 24 f0       	mov    %r14,-0x10(%rsp)
    6545:	49 83 f8 02          	cmp    $0x2,%r8
    6549:	0f 86 11 01 00 00    	jbe    6660 <sendm+0x230>
    654f:	4c 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r9
    6557:	4c 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%r8
    655f:	4f 8d 34 0a          	lea    (%r10,%r9,1),%r14
    6563:	4c 8d be 88 01 00 00 	lea    0x188(%rsi),%r15
    656a:	4b 8d 2c 02          	lea    (%r10,%r8,1),%rbp
    656e:	4d 39 f7             	cmp    %r14,%r15
    6571:	73 75                	jae    65e8 <sendm+0x1b8>
    6573:	4c 8d b6 90 01 00 00 	lea    0x190(%rsi),%r14
    657a:	4c 39 f5             	cmp    %r14,%rbp
    657d:	73 69                	jae    65e8 <sendm+0x1b8>
    657f:	4d 01 d0             	add    %r10,%r8
    6582:	4b 8d 3c 0a          	lea    (%r10,%r9,1),%rdi
    6586:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6590:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
          for (; them->messages_count < min;) {
    6597:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
    659b:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
          for (; them->messages_count < min;) {
    659f:	4c 39 c7             	cmp    %r8,%rdi
    65a2:	75 ec                	jne    6590 <sendm+0x160>
    65a4:	0f 1f 40 00          	nopl   0x0(%rax)
    65a8:	48 8b 7c 24 e8       	mov    -0x18(%rsp),%rdi
    65ad:	4c 01 df             	add    %r11,%rdi
    65b0:	48 89 be 08 01 00 00 	mov    %rdi,0x108(%rsi)
    65b7:	48 8b 7c 24 f0       	mov    -0x10(%rsp),%rdi
    65bc:	48 89 99 80 00 00 00 	mov    %rbx,0x80(%rcx)
    65c3:	4c 01 df             	add    %r11,%rdi
    65c6:	48 89 b9 08 03 00 00 	mov    %rdi,0x308(%rcx)
    65cd:	4d 89 4c da f8       	mov    %r9,-0x8(%r10,%rbx,8)
          them->available_sending = 0;
    65d2:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
    65dc:	e9 05 ff ff ff       	jmp    64e6 <sendm+0xb6>
    65e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    65e8:	4d 89 de             	mov    %r11,%r14
    65eb:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
    65f2:	49 89 e8             	mov    %rbp,%r8
    65f5:	49 d1 ee             	shr    %r14
    65f8:	49 c1 e6 04          	shl    $0x4,%r14
    65fc:	66 49 0f 6e c1       	movq   %r9,%xmm0
    6601:	4e 8d 7c 35 00       	lea    0x0(%rbp,%r14,1),%r15
    6606:	41 83 e6 10          	and    $0x10,%r14d
    660a:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    660e:	74 10                	je     6620 <sendm+0x1f0>
            them->messages[them->messages_count++] = data->message; 
    6610:	49 83 c0 10          	add    $0x10,%r8
    6614:	0f 11 45 00          	movups %xmm0,0x0(%rbp)
          for (; them->messages_count < min;) {
    6618:	4d 39 f8             	cmp    %r15,%r8
    661b:	74 15                	je     6632 <sendm+0x202>
    661d:	0f 1f 00             	nopl   (%rax)
            them->messages[them->messages_count++] = data->message; 
    6620:	41 0f 11 00          	movups %xmm0,(%r8)
    6624:	49 83 c0 20          	add    $0x20,%r8
    6628:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
          for (; them->messages_count < min;) {
    662d:	4d 39 f8             	cmp    %r15,%r8
    6630:	75 ee                	jne    6620 <sendm+0x1f0>
    6632:	4d 89 d8             	mov    %r11,%r8
    6635:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    6639:	4c 01 c7             	add    %r8,%rdi
    663c:	41 f6 c3 01          	test   $0x1,%r11b
    6640:	0f 84 62 ff ff ff    	je     65a8 <sendm+0x178>
            them->messages[them->messages_count++] = data->message; 
    6646:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
    664d:	4d 89 0c fa          	mov    %r9,(%r10,%rdi,8)
          for (; them->messages_count < min;) {
    6651:	e9 52 ff ff ff       	jmp    65a8 <sendm+0x178>
    6656:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6660:	4c 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%r8
    6668:	4c 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r9
    6670:	e9 0a ff ff ff       	jmp    657f <sendm+0x14f>
    6675:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000006680 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    6680:	f3 0f 1e fa          	endbr64
    6684:	41 57                	push   %r15
    6686:	41 56                	push   %r14
    6688:	41 55                	push   %r13
    668a:	41 54                	push   %r12
    668c:	55                   	push   %rbp
    668d:	48 89 fd             	mov    %rdi,%rbp
    6690:	53                   	push   %rbx
    6691:	48 83 ec 68          	sub    $0x68,%rsp
  if (data->thread_index == data->task_index) {
    6695:	8b 47 04             	mov    0x4(%rdi),%eax
    6698:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    669e:	74 40                	je     66e0 <barriered_work+0x60>
    receive(data);
    66a0:	e8 1b fc ff ff       	call   62c0 <receive>
    while (data->scheduled == 1) {
    66a5:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    66ac:	75 16                	jne    66c4 <barriered_work+0x44>
    66ae:	66 90                	xchg   %ax,%ax
      data->n++;
    66b0:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      asm volatile ("sfence" ::: "memory");
    66b8:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    66bb:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    66c2:	74 ec                	je     66b0 <barriered_work+0x30>
    sendm(data);
    66c4:	48 89 ef             	mov    %rbp,%rdi
    66c7:	e8 64 fd ff ff       	call   6430 <sendm>
  asm volatile ("sfence" ::: "memory");
    66cc:	0f ae f8             	sfence
}
    66cf:	48 83 c4 68          	add    $0x68,%rsp
    66d3:	31 c0                	xor    %eax,%eax
    66d5:	5b                   	pop    %rbx
    66d6:	5d                   	pop    %rbp
    66d7:	41 5c                	pop    %r12
    66d9:	41 5d                	pop    %r13
    66db:	41 5e                	pop    %r14
    66dd:	41 5f                	pop    %r15
    66df:	c3                   	ret
      receive(data);
    66e0:	e8 db fb ff ff       	call   62c0 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    66e5:	8b 8d 40 01 00 00    	mov    0x140(%rbp),%ecx
        int t = data->task_index;
    66eb:	48 63 45 04          	movslq 0x4(%rbp),%rax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    66ef:	85 c9                	test   %ecx,%ecx
    66f1:	0f 8e 29 02 00 00    	jle    6920 <barriered_work+0x2a0>
              int b = data->thread->real_thread_index;
    66f7:	48 8b 9d 28 01 00 00 	mov    0x128(%rbp),%rbx
                  if (b == data->thread->real_thread_index && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    66fe:	48 c1 e0 09          	shl    $0x9,%rax
                      all_finished = 0;
    6702:	48 89 6c 24 48       	mov    %rbp,0x48(%rsp)
    6707:	45 31 ff             	xor    %r15d,%r15d
                  if (b == data->thread->real_thread_index && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    670a:	49 89 c0             	mov    %rax,%r8
              int next_task = abs((t + 1) % (data->thread_count));
    670d:	44 8b b5 34 01 00 00 	mov    0x134(%rbp),%r14d
              int b = data->thread->real_thread_index;
    6714:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    6719:	8b 5b 08             	mov    0x8(%rbx),%ebx
                  if (b == data->thread->real_thread_index && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    671c:	48 63 c3             	movslq %ebx,%rax
              int b = data->thread->real_thread_index;
    671f:	89 5c 24 58          	mov    %ebx,0x58(%rsp)
                  if (b == data->thread->real_thread_index && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6723:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
    672b:	48 29 c2             	sub    %rax,%rdx
                    if (((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->finished_reading == 0) {
    672e:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6732:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
                  if (b == data->thread->real_thread_index && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6736:	48 8d 34 d5 00 00 00 00 	lea    0x0(,%rdx,8),%rsi
                    for (int nn = 0 ; nn < data->thread_count - 1; nn++) {
    673e:	31 d2                	xor    %edx,%edx
                    if (((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->finished_reading == 0) {
    6740:	48 c1 e0 03          	shl    $0x3,%rax
                      all_finished = 0;
    6744:	48 89 d5             	mov    %rdx,%rbp
                    if (((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->finished_reading == 0) {
    6747:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
                    for (int nn = 0 ; nn < data->thread_count - 1; nn++) {
    674c:	41 8d 46 ff          	lea    -0x1(%r14),%eax
    6750:	89 44 24 5c          	mov    %eax,0x5c(%rsp)
    6754:	48 63 c1             	movslq %ecx,%rax
    6757:	31 c9                	xor    %ecx,%ecx
    6759:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    675e:	49 63 c6             	movslq %r14d,%rax
    6761:	48 c1 e0 09          	shl    $0x9,%rax
    6765:	4c 8d 98 70 01 00 00 	lea    0x170(%rax),%r11
    676c:	0f 1f 40 00          	nopl   0x0(%rax)
              if (y == b) { continue; }
    6770:	39 6c 24 58          	cmp    %ebp,0x58(%rsp)
    6774:	0f 84 8e 01 00 00    	je     6908 <barriered_work+0x288>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    677a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    677f:	4c 8b 60 20          	mov    0x20(%rax),%r12
    6783:	48 8d 44 ad 00       	lea    0x0(%rbp,%rbp,4),%rax
    6788:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    678c:	49 8b 7c c4 38       	mov    0x38(%r12,%rax,8),%rdi
    6791:	4a 8b 84 07 70 01 00 00 	mov    0x170(%rdi,%r8,1),%rax
    6799:	83 7c 30 30 02       	cmpl   $0x2,0x30(%rax,%rsi,1)
    679e:	0f 84 53 02 00 00    	je     69f7 <barriered_work+0x377>
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    67a4:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
          int k = data->group;
    67a9:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    67ae:	48 63 93 c4 00 00 00 	movslq 0xc4(%rbx),%rdx
          int k = data->group;
    67b5:	8b 80 94 01 00 00    	mov    0x194(%rax),%eax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    67bb:	85 d2                	test   %edx,%edx
    67bd:	0f 8e 45 01 00 00    	jle    6908 <barriered_work+0x288>
            int y = (k * data->thread->threads_per_group) + d;
    67c3:	0f af c2             	imul   %edx,%eax
    67c6:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    67cb:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    67d0:	48 89 6c 24 28       	mov    %rbp,0x28(%rsp)
    67d5:	48 98                	cltq
    67d7:	48 89 74 24 38       	mov    %rsi,0x38(%rsp)
    67dc:	48 8d 3c 80          	lea    (%rax,%rax,4),%rdi
    67e0:	4c 89 5c 24 30       	mov    %r11,0x30(%rsp)
    67e5:	48 8d 3c bf          	lea    (%rdi,%rdi,4),%rdi
    67e9:	4d 8d 2c fc          	lea    (%r12,%rdi,8),%r13
    67ed:	48 8d 3c c5 00 00 00 00 	lea    0x0(,%rax,8),%rdi
    67f5:	48 29 c7             	sub    %rax,%rdi
    67f8:	48 01 d0             	add    %rdx,%rax
    67fb:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    6800:	4d 89 e9             	mov    %r13,%r9
    6803:	48 8d 1c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbx
    680b:	4c 8d 24 fd 00 00 00 00 	lea    0x0(,%rdi,8),%r12
    6813:	48 29 c3             	sub    %rax,%rbx
    6816:	4d 89 e2             	mov    %r12,%r10
    6819:	4d 89 e3             	mov    %r12,%r11
    681c:	48 c1 e3 03          	shl    $0x3,%rbx
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6820:	49 8b 69 38          	mov    0x38(%r9),%rbp
    6824:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6829:	4c 89 de             	mov    %r11,%rsi
    682c:	4d 89 c8             	mov    %r9,%r8
    682f:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    6834:	4c 8b a4 05 70 01 00 00 	mov    0x170(%rbp,%rax,1),%r12
    683c:	eb 16                	jmp    6854 <barriered_work+0x1d4>
    683e:	66 90                	xchg   %ax,%ax
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6840:	48 83 c6 38          	add    $0x38,%rsi
    6844:	48 81 c7 c8 00 00 00 	add    $0xc8,%rdi
    684b:	48 39 de             	cmp    %rbx,%rsi
    684e:	0f 84 84 00 00 00    	je     68d8 <barriered_work+0x258>
              if (kind == MAILBOX_FRIEND) {
    6854:	41 83 7c 34 30 01    	cmpl   $0x1,0x30(%r12,%rsi,1)
    685a:	75 e4                	jne    6840 <barriered_work+0x1c0>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    685c:	4c 8b 4f 38          	mov    0x38(%rdi),%r9
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6860:	45 85 f6             	test   %r14d,%r14d
    6863:	7e db                	jle    6840 <barriered_work+0x1c0>
    6865:	48 89 3c 24          	mov    %rdi,(%rsp)
    6869:	49 81 c1 70 01 00 00 	add    $0x170,%r9
    6870:	31 c9                	xor    %ecx,%ecx
    6872:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
                    int next_task = abs((nn + 1) % (data->thread_count));
    6878:	83 c1 01             	add    $0x1,%ecx
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    687b:	49 8b 39             	mov    (%r9),%rdi
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    687e:	49 81 c1 00 02 00 00 	add    $0x200,%r9
                    int next_task = abs((nn + 1) % (data->thread_count));
    6885:	89 c8                	mov    %ecx,%eax
    6887:	99                   	cltd
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6888:	4c 01 d7             	add    %r10,%rdi
                    int next_task = abs((nn + 1) % (data->thread_count));
    688b:	41 f7 fe             	idiv   %r14d
    return mailbox->lower;
    688e:	4c 8b 2f             	mov    (%rdi),%r13
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6891:	48 63 d2             	movslq %edx,%rdx
    6894:	48 c1 e2 09          	shl    $0x9,%rdx
    6898:	48 8b 84 15 70 01 00 00 	mov    0x170(%rbp,%rdx,1),%rax
    mailbox->lower = data;
    68a0:	48 8b 57 08          	mov    0x8(%rdi),%rdx
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    68a4:	48 01 f0             	add    %rsi,%rax
    return mailbox->higher;
    68a7:	f3 0f 6f 00          	movdqu (%rax),%xmm0
    mailbox->lower = data;
    68ab:	48 89 10             	mov    %rdx,(%rax)
    return mailbox->lower;
    68ae:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
    mailbox->lower = data;
    68b3:	0f 11 07             	movups %xmm0,(%rdi)
    mailbox->higher = data;
    68b6:	4c 89 68 08          	mov    %r13,0x8(%rax)
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    68ba:	41 39 ce             	cmp    %ecx,%r14d
    68bd:	75 b9                	jne    6878 <barriered_work+0x1f8>
    68bf:	48 8b 3c 24          	mov    (%rsp),%rdi
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    68c3:	48 83 c6 38          	add    $0x38,%rsi
    68c7:	48 81 c7 c8 00 00 00 	add    $0xc8,%rdi
    68ce:	48 39 de             	cmp    %rbx,%rsi
    68d1:	75 81                	jne    6854 <barriered_work+0x1d4>
    68d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    68d8:	4d 89 c1             	mov    %r8,%r9
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    68db:	49 83 c2 38          	add    $0x38,%r10
    68df:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
    68e6:	4c 39 d3             	cmp    %r10,%rbx
    68e9:	0f 85 31 ff ff ff    	jne    6820 <barriered_work+0x1a0>
    68ef:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    68f4:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    68f9:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
    68fe:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    6903:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6908:	48 83 c5 01          	add    $0x1,%rbp
    690c:	48 83 c1 38          	add    $0x38,%rcx
    6910:	48 39 6c 24 40       	cmp    %rbp,0x40(%rsp)
    6915:	0f 85 55 fe ff ff    	jne    6770 <barriered_work+0xf0>
    691b:	48 8b 6c 24 48       	mov    0x48(%rsp),%rbp
      receive(data);
    6920:	48 89 ef             	mov    %rbp,%rdi
    6923:	e8 98 f9 ff ff       	call   62c0 <receive>
      asm volatile ("sfence" ::: "memory");
    6928:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    692b:	48 8b b5 60 01 00 00 	mov    0x160(%rbp),%rsi
    6932:	31 ff                	xor    %edi,%edi
    6934:	48 c1 e6 05          	shl    $0x5,%rsi
    6938:	48 03 b5 50 01 00 00 	add    0x150(%rbp),%rsi
    693f:	e8 fc b9 ff ff       	call   2340 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6944:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    694b:	48 8b 50 48          	mov    0x48(%rax),%rdx
    694f:	8b 5a 10             	mov    0x10(%rdx),%ebx
    6952:	83 c3 01             	add    $0x1,%ebx
    while (data->scheduled == 1) {
    6955:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    int modcount = ++data->thread->protected_state->modcount;
    695c:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    695f:	75 51                	jne    69b2 <barriered_work+0x332>
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6961:	48 63 95 30 01 00 00 	movslq 0x130(%rbp),%rdx
    6968:	48 8b 40 18          	mov    0x18(%rax),%rax
    696c:	48 63 7d 04          	movslq 0x4(%rbp),%rdi
      data->n++;
    6970:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6978:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    697c:	48 c1 e7 09          	shl    $0x9,%rdi
    6980:	48 03 78 38          	add    0x38(%rax),%rdi
    6984:	ff 95 20 01 00 00    	call   *0x120(%rbp)
      asm volatile ("sfence" ::: "memory");
    698a:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    698d:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    if (modcount != data->thread->protected_state->modcount) {
    6994:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    while (data->scheduled == 1) {
    699b:	74 c4                	je     6961 <barriered_work+0x2e1>
    if (modcount != data->thread->protected_state->modcount) {
    699d:	48 8b 40 48          	mov    0x48(%rax),%rax
    69a1:	3b 58 10             	cmp    0x10(%rax),%ebx
    69a4:	74 0c                	je     69b2 <barriered_work+0x332>
    69a6:	48 8d 3d 99 18 00 00 	lea    0x1899(%rip),%rdi        # 8246 <_IO_stdin_used+0x246>
    69ad:	e8 6e b9 ff ff       	call   2320 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    69b2:	48 8b b5 60 01 00 00 	mov    0x160(%rbp),%rsi
    69b9:	31 ff                	xor    %edi,%edi
    69bb:	48 c1 e6 05          	shl    $0x5,%rsi
    69bf:	48 03 b5 50 01 00 00 	add    0x150(%rbp),%rsi
    69c6:	48 83 c6 10          	add    $0x10,%rsi
    69ca:	e8 71 b9 ff ff       	call   2340 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    69cf:	48 8b 85 60 01 00 00 	mov    0x160(%rbp),%rax
    sendm(data);
    69d6:	48 89 ef             	mov    %rbp,%rdi
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    69d9:	48 83 c0 01          	add    $0x1,%rax
    69dd:	48 99                	cqto
    69df:	48 f7 bd 58 01 00 00 	idivq  0x158(%rbp)
    69e6:	48 89 95 60 01 00 00 	mov    %rdx,0x160(%rbp)
    sendm(data);
    69ed:	e8 3e fa ff ff       	call   6430 <sendm>
    69f2:	e9 d5 fc ff ff       	jmp    66cc <barriered_work+0x4c>
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    69f7:	45 85 f6             	test   %r14d,%r14d
    69fa:	0f 8e a4 fd ff ff    	jle    67a4 <barriered_work+0x124>
                    if (((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->finished_reading == 0) {
    6a00:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
                  int all_finished = 1;
    6a05:	41 b9 01 00 00 00    	mov    $0x1,%r9d
                    if (((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->finished_reading == 0) {
    6a0b:	4d 8b 54 04 38       	mov    0x38(%r12,%rax,1),%r10
    6a10:	b8 70 01 00 00       	mov    $0x170,%eax
    6a15:	0f 1f 00             	nopl   (%rax)
                    if (((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].lower)->finished_reading == 0) {
    6a18:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    6a1c:	48 8b 14 32          	mov    (%rdx,%rsi,1),%rdx
                      all_finished = 0;
    6a20:	8b 92 00 03 00 00    	mov    0x300(%rdx),%edx
    6a26:	85 d2                	test   %edx,%edx
                    if (((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->finished_reading == 0) {
    6a28:	49 8b 14 02          	mov    (%r10,%rax,1),%rdx
                      all_finished = 0;
    6a2c:	45 0f 44 cf          	cmove  %r15d,%r9d
                    if (((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->finished_reading == 0) {
    6a30:	48 8b 14 0a          	mov    (%rdx,%rcx,1),%rdx
                      all_finished = 0;
    6a34:	8b 9a 00 03 00 00    	mov    0x300(%rdx),%ebx
    6a3a:	85 db                	test   %ebx,%ebx
    6a3c:	45 0f 44 cf          	cmove  %r15d,%r9d
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    6a40:	48 05 00 02 00 00    	add    $0x200,%rax
    6a46:	49 39 c3             	cmp    %rax,%r11
    6a49:	75 cd                	jne    6a18 <barriered_work+0x398>
    6a4b:	b8 70 01 00 00       	mov    $0x170,%eax
                  int all_wrote = 1;
    6a50:	ba 01 00 00 00       	mov    $0x1,%edx
    6a55:	0f 1f 00             	nopl   (%rax)
                    if (((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_receiving == 0) {
    6a58:	49 8b 1c 02          	mov    (%r10,%rax,1),%rbx
    6a5c:	48 8b 5c 0b 08       	mov    0x8(%rbx,%rcx,1),%rbx
                      all_wrote = 0;
    6a61:	8b 9b 80 01 00 00    	mov    0x180(%rbx),%ebx
    6a67:	85 db                	test   %ebx,%ebx
                    if (((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving == 0) {
    6a69:	48 8b 1c 07          	mov    (%rdi,%rax,1),%rbx
                      all_wrote = 0;
    6a6d:	41 0f 44 d7          	cmove  %r15d,%edx
                    if (((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving == 0) {
    6a71:	48 8b 5c 33 08       	mov    0x8(%rbx,%rsi,1),%rbx
                      all_wrote = 0;
    6a76:	44 8b ab 80 01 00 00 	mov    0x180(%rbx),%r13d
    6a7d:	45 85 ed             	test   %r13d,%r13d
    6a80:	41 0f 44 d7          	cmove  %r15d,%edx
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    6a84:	48 05 00 02 00 00    	add    $0x200,%rax
    6a8a:	4c 39 d8             	cmp    %r11,%rax
    6a8d:	75 c9                	jne    6a58 <barriered_work+0x3d8>
                  if (all_finished == 1 && all_wrote == 1) {
    6a8f:	41 85 d1             	test   %edx,%r9d
    6a92:	75 5c                	jne    6af0 <barriered_work+0x470>
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6a94:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    6a99:	4d 8b 54 04 38       	mov    0x38(%r12,%rax,1),%r10
    6a9e:	b8 70 01 00 00       	mov    $0x170,%eax
    6aa3:	eb 12                	jmp    6ab7 <barriered_work+0x437>
    6aa5:	0f 1f 00             	nopl   (%rax)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6aa8:	48 05 00 02 00 00    	add    $0x200,%rax
    6aae:	4c 39 d8             	cmp    %r11,%rax
    6ab1:	0f 84 ed fc ff ff    	je     67a4 <barriered_work+0x124>
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6ab7:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    6abb:	4d 8b 0c 02          	mov    (%r10,%rax,1),%r9
    6abf:	48 8b 1c 32          	mov    (%rdx,%rsi,1),%rbx
    6ac3:	49 39 1c 09          	cmp    %rbx,(%r9,%rcx,1)
    6ac7:	75 df                	jne    6aa8 <barriered_work+0x428>
    6ac9:	bf 01 00 00 00       	mov    $0x1,%edi
    6ace:	48 8d 35 56 17 00 00 	lea    0x1756(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    6ad5:	31 c0                	xor    %eax,%eax
    6ad7:	e8 c4 b9 ff ff       	call   24a0 <__printf_chk@plt>
                          exit(1);
    6adc:	bf 01 00 00 00       	mov    $0x1,%edi
    6ae1:	e8 1a ba ff ff       	call   2500 <exit@plt>
    6ae6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
                    for (int nn = 0 ; nn < data->thread_count - 1; nn++) {
    6af0:	41 83 fe 01          	cmp    $0x1,%r14d
    6af4:	74 9e                	je     6a94 <barriered_work+0x414>
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6af6:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
                    for (int nn = 0 ; nn < data->thread_count - 1; nn++) {
    6afb:	4c 89 24 24          	mov    %r12,(%rsp)
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6aff:	bb 70 01 00 00       	mov    $0x170,%ebx
                    for (int nn = 0 ; nn < data->thread_count - 1; nn++) {
    6b04:	45 31 c9             	xor    %r9d,%r9d
    6b07:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    6b0c:	44 8b 44 24 5c       	mov    0x5c(%rsp),%r8d
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6b11:	4d 8b 6c 04 38       	mov    0x38(%r12,%rax,1),%r13
                      int next_task = abs(nn + 1) % data->thread_count;
    6b16:	41 83 c1 01          	add    $0x1,%r9d
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6b1a:	4d 8b 54 1d 00       	mov    0x0(%r13,%rbx,1),%r10
                      int next_task = abs(nn + 1) % data->thread_count;
    6b1f:	44 89 c8             	mov    %r9d,%eax
    6b22:	99                   	cltd
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6b23:	49 01 ca             	add    %rcx,%r10
                      int next_task = abs(nn + 1) % data->thread_count;
    6b26:	41 f7 fe             	idiv   %r14d
    return mailbox->lower;
    6b29:	4d 8b 22             	mov    (%r10),%r12
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6b2c:	48 63 d2             	movslq %edx,%rdx
    6b2f:	48 c1 e2 09          	shl    $0x9,%rdx
    6b33:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    mailbox->lower = data;
    6b3b:	49 8b 52 08          	mov    0x8(%r10),%rdx
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6b3f:	48 01 f0             	add    %rsi,%rax
    return mailbox->higher;
    6b42:	f3 0f 6f 00          	movdqu (%rax),%xmm0
    mailbox->lower = data;
    6b46:	48 89 10             	mov    %rdx,(%rax)
    return mailbox->lower;
    6b49:	66 0f 6f c8          	movdqa %xmm0,%xmm1
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6b4d:	0f 12 d0             	movhlps %xmm0,%xmm2
    return mailbox->lower;
    6b50:	66 0f c6 c8 01       	shufpd $0x1,%xmm0,%xmm1
    mailbox->lower = data;
    6b55:	41 0f 11 0a          	movups %xmm1,(%r10)
    mailbox->higher = data;
    6b59:	4c 89 60 08          	mov    %r12,0x8(%rax)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    6b5d:	48 8b 14 1f          	mov    (%rdi,%rbx,1),%rdx
                    for (int nn = 0 ; nn < data->thread_count - 1; nn++) {
    6b61:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
    6b68:	4d 8b 52 08          	mov    0x8(%r10),%r10
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6b6c:	48 8b 00             	mov    (%rax),%rax
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    6b6f:	48 8b 54 32 08       	mov    0x8(%rdx,%rsi,1),%rdx
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
    6b74:	41 c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%r10)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    6b7f:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    6b89:	41 c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r10)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    6b94:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6b9e:	66 48 0f 7e d2       	movq   %xmm2,%rdx
    6ba3:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6bad:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                    for (int nn = 0 ; nn < data->thread_count - 1; nn++) {
    6bb7:	45 39 c1             	cmp    %r8d,%r9d
    6bba:	0f 8c 56 ff ff ff    	jl     6b16 <barriered_work+0x496>
    6bc0:	4c 8b 24 24          	mov    (%rsp),%r12
    6bc4:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    6bc9:	e9 c6 fe ff ff       	jmp    6a94 <barriered_work+0x414>
    6bce:	66 90                	xchg   %ax,%ax

0000000000006bd0 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6bd0:	f3 0f 1e fa          	endbr64
    6bd4:	53                   	push   %rbx
    6bd5:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6bd8:	e8 f3 f2 ff ff       	call   5ed0 <barriered_work_ingest>
  barriered_work(data);
    6bdd:	48 89 df             	mov    %rbx,%rdi
}
    6be0:	5b                   	pop    %rbx
  barriered_work(data);
    6be1:	e9 9a fa ff ff       	jmp    6680 <barriered_work>
    6be6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006bf0 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    6bf0:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6bf4:	85 f6                	test   %esi,%esi
    6bf6:	74 10                	je     6c08 <mailboxkind+0x18>
  return NULL;
    6bf8:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    6bfa:	83 fe 01             	cmp    $0x1,%esi
    6bfd:	74 01                	je     6c00 <mailboxkind+0x10>
}
    6bff:	c3                   	ret
    return mailbox->higher;
    6c00:	48 8b 47 08          	mov    0x8(%rdi),%rax
}
    6c04:	c3                   	ret
    6c05:	0f 1f 00             	nopl   (%rax)
    return mailbox->lower;
    6c08:	48 8b 07             	mov    (%rdi),%rax
    6c0b:	c3                   	ret
    6c0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006c10 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    6c10:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6c14:	85 d2                	test   %edx,%edx
    6c16:	75 08                	jne    6c20 <setmailboxkind+0x10>
    mailbox->lower = data;
    6c18:	48 89 37             	mov    %rsi,(%rdi)
}
    6c1b:	31 c0                	xor    %eax,%eax
    6c1d:	c3                   	ret
    6c1e:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    6c20:	83 fa 01             	cmp    $0x1,%edx
    6c23:	74 13                	je     6c38 <setmailboxkind+0x28>
  if (kind == 2) {
    6c25:	83 fa 02             	cmp    $0x2,%edx
    6c28:	75 f1                	jne    6c1b <setmailboxkind+0xb>
    mailbox->pending = data;
    6c2a:	48 89 77 10          	mov    %rsi,0x10(%rdi)
}
    6c2e:	31 c0                	xor    %eax,%eax
    6c30:	c3                   	ret
    6c31:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    mailbox->higher = data;
    6c38:	48 89 77 08          	mov    %rsi,0x8(%rdi)
}
    6c3c:	31 c0                	xor    %eax,%eax
    6c3e:	c3                   	ret
    6c3f:	90                   	nop

0000000000006c40 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6c40:	f3 0f 1e fa          	endbr64
}
    6c44:	31 c0                	xor    %eax,%eax
    6c46:	c3                   	ret
    6c47:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006c50 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6c50:	f3 0f 1e fa          	endbr64
    6c54:	31 c0                	xor    %eax,%eax
    6c56:	c3                   	ret
    6c57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006c60 <after>:
int after(struct timespec left, struct timespec right) {
    6c60:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6c64:	31 c0                	xor    %eax,%eax
    6c66:	48 39 d7             	cmp    %rdx,%rdi
    6c69:	7e 08                	jle    6c73 <after+0x13>
    6c6b:	31 c0                	xor    %eax,%eax
    6c6d:	48 39 ce             	cmp    %rcx,%rsi
    6c70:	0f 9f c0             	setg   %al
}
    6c73:	c3                   	ret
    6c74:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6c7f:	90                   	nop

0000000000006c80 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6c80:	f3 0f 1e fa          	endbr64
    6c84:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6c89:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    6c8e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6c90:	48 39 d7             	cmp    %rdx,%rdi
    6c93:	7f 18                	jg     6cad <within+0x2d>
    6c95:	4d 39 d8             	cmp    %r11,%r8
    6c98:	0f 9e c2             	setle  %dl
    6c9b:	48 39 ce             	cmp    %rcx,%rsi
    6c9e:	0f 9e c0             	setle  %al
    6ca1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6ca3:	31 c0                	xor    %eax,%eax
    6ca5:	4d 39 d1             	cmp    %r10,%r9
    6ca8:	0f 9e c0             	setle  %al
    6cab:	21 d0                	and    %edx,%eax
}
    6cad:	c3                   	ret
    6cae:	66 90                	xchg   %ax,%ax

0000000000006cb0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6cb0:	f3 0f 1e fa          	endbr64
    6cb4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6cb9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    6cbe:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6cc3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6cc8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    6ccd:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6cd2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6cd7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    6cdc:	48 39 fe             	cmp    %rdi,%rsi
    6cdf:	7d 2f                	jge    6d10 <overlap+0x60>
    6ce1:	48 39 ca             	cmp    %rcx,%rdx
    6ce4:	7d 62                	jge    6d48 <overlap+0x98>
    6ce6:	4d 39 da             	cmp    %r11,%r10
    6ce9:	7d 0e                	jge    6cf9 <overlap+0x49>
    return 1;
    6ceb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6cf0:	4d 39 c1             	cmp    %r8,%r9
    6cf3:	0f 8c 7f 00 00 00    	jl     6d78 <overlap+0xc8>
  return 0;
    6cf9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6cfb:	4d 39 c1             	cmp    %r8,%r9
    6cfe:	7f 4c                	jg     6d4c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6d00:	31 c0                	xor    %eax,%eax
    6d02:	4d 39 da             	cmp    %r11,%r10
    6d05:	0f 9e c0             	setle  %al
    6d08:	c3                   	ret
    6d09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6d10:	7e 4e                	jle    6d60 <overlap+0xb0>
    6d12:	48 39 ca             	cmp    %rcx,%rdx
    6d15:	7f 39                	jg     6d50 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6d17:	75 31                	jne    6d4a <overlap+0x9a>
    6d19:	4d 39 c1             	cmp    %r8,%r9
    6d1c:	7c 2c                	jl     6d4a <overlap+0x9a>
    return 1;
    6d1e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6d23:	4d 39 da             	cmp    %r11,%r10
    6d26:	7d 24                	jge    6d4c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6d28:	48 39 ca             	cmp    %rcx,%rdx
    6d2b:	0f 94 c2             	sete   %dl
    6d2e:	48 39 fe             	cmp    %rdi,%rsi
    6d31:	0f 94 c0             	sete   %al
    6d34:	21 c2                	and    %eax,%edx
    6d36:	31 c0                	xor    %eax,%eax
    6d38:	4d 39 c1             	cmp    %r8,%r9
    6d3b:	0f 94 c0             	sete   %al
    6d3e:	21 d0                	and    %edx,%eax
    6d40:	c3                   	ret
    6d41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6d48:	74 af                	je     6cf9 <overlap+0x49>
  return 0;
    6d4a:	31 c0                	xor    %eax,%eax
}
    6d4c:	c3                   	ret
    6d4d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6d50:	4d 39 da             	cmp    %r11,%r10
    6d53:	7e c4                	jle    6d19 <overlap+0x69>
    return 1;
    6d55:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6d5a:	4d 39 c1             	cmp    %r8,%r9
    6d5d:	7e ba                	jle    6d19 <overlap+0x69>
    6d5f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6d60:	48 39 ca             	cmp    %rcx,%rdx
    6d63:	7c 94                	jl     6cf9 <overlap+0x49>
    6d65:	4d 39 c1             	cmp    %r8,%r9
    6d68:	7d b4                	jge    6d1e <overlap+0x6e>
    6d6a:	48 39 ca             	cmp    %rcx,%rdx
    6d6d:	74 91                	je     6d00 <overlap+0x50>
    6d6f:	eb d9                	jmp    6d4a <overlap+0x9a>
    6d71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6d78:	c3                   	ret
    6d79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006d80 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6d80:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6d84:	85 f6                	test   %esi,%esi
    6d86:	0f 8e 44 03 00 00    	jle    70d0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    6d8c:	41 57                	push   %r15
    6d8e:	41 89 f7             	mov    %esi,%r15d
    6d91:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6d93:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6d96:	41 55                	push   %r13
    6d98:	41 54                	push   %r12
    6d9a:	55                   	push   %rbp
    6d9b:	53                   	push   %rbx
    6d9c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6da0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6da4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6da9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    6dae:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6db1:	45 39 e6             	cmp    %r12d,%r14d
    6db4:	0f 84 4e 02 00 00    	je     7008 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6dba:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6dbf:	8b 50 08             	mov    0x8(%rax),%edx
    6dc2:	85 d2                	test   %edx,%edx
    6dc4:	0f 8e 3e 02 00 00    	jle    7008 <verify+0x288>
    6dca:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    6dcf:	31 c9                	xor    %ecx,%ecx
    6dd1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    6dd6:	31 c0                	xor    %eax,%eax
    6dd8:	44 89 f2             	mov    %r14d,%edx
    6ddb:	bf 01 00 00 00       	mov    $0x1,%edi
    6de0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6de5:	48 8d 35 6a 14 00 00 	lea    0x146a(%rip),%rsi        # 8256 <_IO_stdin_used+0x256>
    6dec:	e8 af b6 ff ff       	call   24a0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6df1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6df6:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    6dfb:	8b 40 08             	mov    0x8(%rax),%eax
    6dfe:	85 c0                	test   %eax,%eax
    6e00:	0f 8e e6 01 00 00    	jle    6fec <verify+0x26c>
    6e06:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6e09:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    6e0e:	31 db                	xor    %ebx,%ebx
    6e10:	48 c1 e0 09          	shl    $0x9,%rax
    6e14:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6e19:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    6e1e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6e23:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6e28:	4c 8b 20             	mov    (%rax),%r12
    6e2b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6e30:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6e35:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    6e3a:	49 89 de             	mov    %rbx,%r14
    6e3d:	48 8d 35 27 14 00 00 	lea    0x1427(%rip),%rsi        # 826b <_IO_stdin_used+0x26b>
    6e44:	49 c1 e6 09          	shl    $0x9,%r14
    6e48:	bf 01 00 00 00       	mov    $0x1,%edi
    6e4d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6e51:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    6e59:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    6e5e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    6e66:	31 c0                	xor    %eax,%eax
    6e68:	e8 33 b6 ff ff       	call   24a0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6e6d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6e72:	4c 8b 20             	mov    (%rax),%r12
    6e75:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    6e7e:	0f 8e 47 01 00 00    	jle    6fcb <verify+0x24b>
    6e84:	4c 03 75 00          	add    0x0(%rbp),%r14
    6e88:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6e8d:	ba 01 00 00 00       	mov    $0x1,%edx
    6e92:	4d 89 f5             	mov    %r14,%r13
    6e95:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6e9c:	4d 85 f6             	test   %r14,%r14
    6e9f:	0f 8e 21 01 00 00    	jle    6fc6 <verify+0x246>
    6ea5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6ea8:	48 89 d5             	mov    %rdx,%rbp
    6eab:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6eb0:	31 db                	xor    %ebx,%ebx
    6eb2:	4d 89 f2             	mov    %r14,%r10
    6eb5:	48 c1 e5 05          	shl    $0x5,%rbp
    6eb9:	48 83 ed 20          	sub    $0x20,%rbp
    6ebd:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6ec1:	49 89 ee             	mov    %rbp,%r14
    6ec4:	48 89 dd             	mov    %rbx,%rbp
    6ec7:	48 89 d3             	mov    %rdx,%rbx
    6eca:	eb 31                	jmp    6efd <verify+0x17d>
    6ecc:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6ed0:	4c 39 c2             	cmp    %r8,%rdx
    6ed3:	0f 8d 57 01 00 00    	jge    7030 <verify+0x2b0>
    6ed9:	4c 39 df             	cmp    %r11,%rdi
    6edc:	7e 05                	jle    6ee3 <verify+0x163>
    6ede:	49 39 c1             	cmp    %rax,%r9
    6ee1:	7c 75                	jl     6f58 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6ee3:	4c 39 df             	cmp    %r11,%rdi
    6ee6:	0f 8d ab 01 00 00    	jge    7097 <verify+0x317>
    6eec:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6ef0:	48 83 c5 01          	add    $0x1,%rbp
    6ef4:	49 39 ea             	cmp    %rbp,%r10
    6ef7:	0f 8e a9 00 00 00    	jle    6fa6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6efd:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    6f04:	48 89 e8             	mov    %rbp,%rax
    6f07:	48 c1 e0 05          	shl    $0x5,%rax
    6f0b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    6f12:	4c 01 f2             	add    %r14,%rdx
    6f15:	48 8b 08             	mov    (%rax),%rcx
    6f18:	48 8b 78 10          	mov    0x10(%rax),%rdi
    6f1c:	48 8b 32             	mov    (%rdx),%rsi
    6f1f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6f23:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6f27:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    6f2b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    6f2f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6f33:	48 39 f1             	cmp    %rsi,%rcx
    6f36:	7c 98                	jl     6ed0 <verify+0x150>
    6f38:	0f 8e 42 01 00 00    	jle    7080 <verify+0x300>
    6f3e:	4c 39 c2             	cmp    %r8,%rdx
    6f41:	0f 8f f9 00 00 00    	jg     7040 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f47:	75 a7                	jne    6ef0 <verify+0x170>
    6f49:	4c 39 df             	cmp    %r11,%rdi
    6f4c:	7f a2                	jg     6ef0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6f4e:	49 39 c1             	cmp    %rax,%r9
    6f51:	7c 9d                	jl     6ef0 <verify+0x170>
    6f53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6f58:	49 89 c1             	mov    %rax,%r9
    6f5b:	48 89 f9             	mov    %rdi,%rcx
    6f5e:	48 89 f2             	mov    %rsi,%rdx
    6f61:	bf 01 00 00 00       	mov    $0x1,%edi
    6f66:	48 8d 35 c3 16 00 00 	lea    0x16c3(%rip),%rsi        # 8630 <_IO_stdin_used+0x630>
    6f6d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6f6f:	48 83 c5 01          	add    $0x1,%rbp
    6f73:	e8 28 b5 ff ff       	call   24a0 <__printf_chk@plt>
    6f78:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6f7d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    6f82:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6f85:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6f8a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6f91:	4c 8b 20             	mov    (%rax),%r12
    6f94:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6f99:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6f9d:	49 39 ea             	cmp    %rbp,%r10
    6fa0:	0f 8f 57 ff ff ff    	jg     6efd <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6fa6:	48 89 da             	mov    %rbx,%rdx
    6fa9:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    6fb0:	7d 14                	jge    6fc6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6fb2:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6fb9:	48 83 c2 01          	add    $0x1,%rdx
    6fbd:	4d 85 f6             	test   %r14,%r14
    6fc0:	0f 8f e2 fe ff ff    	jg     6ea8 <verify+0x128>
    6fc6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6fcb:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6fd0:	48 83 c3 01          	add    $0x1,%rbx
    6fd4:	39 58 08             	cmp    %ebx,0x8(%rax)
    6fd7:	0f 8f 53 fe ff ff    	jg     6e30 <verify+0xb0>
    6fdd:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6fe2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6fe7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6fec:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6ff1:	48 83 c1 01          	add    $0x1,%rcx
    6ff5:	39 48 08             	cmp    %ecx,0x8(%rax)
    6ff8:	0f 8f d8 fd ff ff    	jg     6dd6 <verify+0x56>
    6ffe:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    7003:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    7008:	48 81 44 24 10 c8 00 00 00 	addq   $0xc8,0x10(%rsp)
    7011:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    7016:	41 39 c7             	cmp    %eax,%r15d
    7019:	0f 84 86 00 00 00    	je     70a5 <verify+0x325>
    701f:	41 89 c4             	mov    %eax,%r12d
    7022:	e9 8a fd ff ff       	jmp    6db1 <verify+0x31>
    7027:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7030:	0f 85 ba fe ff ff    	jne    6ef0 <verify+0x170>
    7036:	e9 a8 fe ff ff       	jmp    6ee3 <verify+0x163>
    703b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    7040:	49 39 c1             	cmp    %rax,%r9
    7043:	7e 09                	jle    704e <verify+0x2ce>
    7045:	4c 39 df             	cmp    %r11,%rdi
    7048:	0f 8c 0a ff ff ff    	jl     6f58 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    704e:	4c 39 df             	cmp    %r11,%rdi
    7051:	0f 8f 99 fe ff ff    	jg     6ef0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7057:	49 39 c1             	cmp    %rax,%r9
    705a:	0f 8d f8 fe ff ff    	jge    6f58 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7060:	48 39 f1             	cmp    %rsi,%rcx
    7063:	0f 85 87 fe ff ff    	jne    6ef0 <verify+0x170>
    7069:	4c 39 c2             	cmp    %r8,%rdx
    706c:	0f 85 7e fe ff ff    	jne    6ef0 <verify+0x170>
    7072:	4c 39 df             	cmp    %r11,%rdi
    7075:	0f 84 dd fe ff ff    	je     6f58 <verify+0x1d8>
    707b:	e9 70 fe ff ff       	jmp    6ef0 <verify+0x170>
    7080:	4c 39 c2             	cmp    %r8,%rdx
    7083:	0f 8c 5a fe ff ff    	jl     6ee3 <verify+0x163>
    7089:	4c 39 df             	cmp    %r11,%rdi
    708c:	7e c9                	jle    7057 <verify+0x2d7>
    708e:	4c 39 c2             	cmp    %r8,%rdx
    7091:	0f 85 59 fe ff ff    	jne    6ef0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7097:	49 39 c1             	cmp    %rax,%r9
    709a:	0f 8f 50 fe ff ff    	jg     6ef0 <verify+0x170>
    70a0:	e9 b3 fe ff ff       	jmp    6f58 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    70a5:	48 81 44 24 18 c8 00 00 00 	addq   $0xc8,0x18(%rsp)
    70ae:	41 8d 46 01          	lea    0x1(%r14),%eax
    70b2:	45 39 e6             	cmp    %r12d,%r14d
    70b5:	74 08                	je     70bf <verify+0x33f>
    70b7:	41 89 c6             	mov    %eax,%r14d
    70ba:	e9 ea fc ff ff       	jmp    6da9 <verify+0x29>
}
    70bf:	48 83 c4 58          	add    $0x58,%rsp
    70c3:	31 c0                	xor    %eax,%eax
    70c5:	5b                   	pop    %rbx
    70c6:	5d                   	pop    %rbp
    70c7:	41 5c                	pop    %r12
    70c9:	41 5d                	pop    %r13
    70cb:	41 5e                	pop    %r14
    70cd:	41 5f                	pop    %r15
    70cf:	c3                   	ret
    70d0:	31 c0                	xor    %eax,%eax
    70d2:	c3                   	ret

Disassembly of section .fini:

00000000000070d4 <_fini>:
    70d4:	f3 0f 1e fa          	endbr64
    70d8:	48 83 ec 08          	sub    $0x8,%rsp
    70dc:	48 83 c4 08          	add    $0x8,%rsp
    70e0:	c3                   	ret
