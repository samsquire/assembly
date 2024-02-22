
multibarrier-evented3-fswap:     file format elf64-x86-64


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
    2020:	ff 35 42 8e 00 00    	push   0x8e42(%rip)        # ae68 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 44 8e 00 00    	jmp    *0x8e44(%rip)        # ae70 <_GLOBAL_OFFSET_TABLE_+0x10>
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
    22e0:	f3 0f 1e fa          	endbr64
    22e4:	68 2b 00 00 00       	push   $0x2b
    22e9:	e9 32 fd ff ff       	jmp    2020 <_init+0x20>
    22ee:	66 90                	xchg   %ax,%ax

Disassembly of section .plt.got:

00000000000022f0 <__cxa_finalize@plt>:
    22f0:	f3 0f 1e fa          	endbr64
    22f4:	ff 25 fe 8c 00 00    	jmp    *0x8cfe(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    22fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000002300 <free@plt>:
    2300:	f3 0f 1e fa          	endbr64
    2304:	ff 25 6e 8b 00 00    	jmp    *0x8b6e(%rip)        # ae78 <free@GLIBC_2.2.5>
    230a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002310 <putchar@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 66 8b 00 00    	jmp    *0x8b66(%rip)        # ae80 <putchar@GLIBC_2.2.5>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002320 <pthread_setaffinity_np@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 5e 8b 00 00    	jmp    *0x8b5e(%rip)        # ae88 <pthread_setaffinity_np@GLIBC_2.34>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <puts@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 56 8b 00 00    	jmp    *0x8b56(%rip)        # ae90 <puts@GLIBC_2.2.5>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <setsockopt@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 4e 8b 00 00    	jmp    *0x8b4e(%rip)        # ae98 <setsockopt@GLIBC_2.2.5>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <clock_gettime@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 46 8b 00 00    	jmp    *0x8b46(%rip)        # aea0 <clock_gettime@GLIBC_2.17>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <fclose@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 3e 8b 00 00    	jmp    *0x8b3e(%rip)        # aea8 <fclose@GLIBC_2.2.5>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <strlen@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 36 8b 00 00    	jmp    *0x8b36(%rip)        # aeb0 <strlen@GLIBC_2.2.5>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <__stack_chk_fail@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 2e 8b 00 00    	jmp    *0x8b2e(%rip)        # aeb8 <__stack_chk_fail@GLIBC_2.4>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <io_uring_submit@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 26 8b 00 00    	jmp    *0x8b26(%rip)        # aec0 <io_uring_submit@LIBURING_2.0>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <nanosleep@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 1e 8b 00 00    	jmp    *0x8b1e(%rip)        # aec8 <nanosleep@GLIBC_2.2.5>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <strrchr@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 16 8b 00 00    	jmp    *0x8b16(%rip)        # aed0 <strrchr@GLIBC_2.2.5>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <fputs@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 0e 8b 00 00    	jmp    *0x8b0e(%rip)        # aed8 <fputs@GLIBC_2.2.5>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <close@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 06 8b 00 00    	jmp    *0x8b06(%rip)        # aee0 <close@GLIBC_2.2.5>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <strtok_r@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 fe 8a 00 00    	jmp    *0x8afe(%rip)        # aee8 <strtok_r@GLIBC_2.2.5>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <read@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 f6 8a 00 00    	jmp    *0x8af6(%rip)        # aef0 <read@GLIBC_2.2.5>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <calloc@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 ee 8a 00 00    	jmp    *0x8aee(%rip)        # aef8 <calloc@GLIBC_2.2.5>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <strcmp@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 e6 8a 00 00    	jmp    *0x8ae6(%rip)        # af00 <strcmp@GLIBC_2.2.5>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <__memcpy_chk@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 de 8a 00 00    	jmp    *0x8ade(%rip)        # af08 <__memcpy_chk@GLIBC_2.3.4>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <stat@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 d6 8a 00 00    	jmp    *0x8ad6(%rip)        # af10 <stat@GLIBC_2.33>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <memcpy@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 ce 8a 00 00    	jmp    *0x8ace(%rip)        # af18 <memcpy@GLIBC_2.14>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <io_uring_queue_init@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 c6 8a 00 00    	jmp    *0x8ac6(%rip)        # af20 <io_uring_queue_init@LIBURING_2.0>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <eventfd_write@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 be 8a 00 00    	jmp    *0x8abe(%rip)        # af28 <eventfd_write@GLIBC_2.7>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <malloc@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 b6 8a 00 00    	jmp    *0x8ab6(%rip)        # af30 <malloc@GLIBC_2.2.5>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <listen@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 ae 8a 00 00    	jmp    *0x8aae(%rip)        # af38 <listen@GLIBC_2.2.5>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <__strcpy_chk@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 a6 8a 00 00    	jmp    *0x8aa6(%rip)        # af40 <__strcpy_chk@GLIBC_2.3.4>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <__io_uring_get_cqe@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 9e 8a 00 00    	jmp    *0x8a9e(%rip)        # af48 <__io_uring_get_cqe@LIBURING_2.0>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <__printf_chk@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 96 8a 00 00    	jmp    *0x8a96(%rip)        # af50 <__printf_chk@GLIBC_2.3.4>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <bind@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 8e 8a 00 00    	jmp    *0x8a8e(%rip)        # af58 <bind@GLIBC_2.2.5>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <pthread_create@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 86 8a 00 00    	jmp    *0x8a86(%rip)        # af60 <pthread_create@GLIBC_2.34>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <open@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 7e 8a 00 00    	jmp    *0x8a7e(%rip)        # af68 <open@GLIBC_2.2.5>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <fopen@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 76 8a 00 00    	jmp    *0x8a76(%rip)        # af70 <fopen@GLIBC_2.2.5>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <perror@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 6e 8a 00 00    	jmp    *0x8a6e(%rip)        # af78 <perror@GLIBC_2.2.5>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <exit@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 66 8a 00 00    	jmp    *0x8a66(%rip)        # af80 <exit@GLIBC_2.2.5>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <eventfd@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 5e 8a 00 00    	jmp    *0x8a5e(%rip)        # af88 <eventfd@GLIBC_2.7>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <fwrite@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 56 8a 00 00    	jmp    *0x8a56(%rip)        # af90 <fwrite@GLIBC_2.2.5>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002540 <__fprintf_chk@plt>:
    2540:	f3 0f 1e fa          	endbr64
    2544:	ff 25 4e 8a 00 00    	jmp    *0x8a4e(%rip)        # af98 <__fprintf_chk@GLIBC_2.3.4>
    254a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002550 <io_uring_register_eventfd@plt>:
    2550:	f3 0f 1e fa          	endbr64
    2554:	ff 25 46 8a 00 00    	jmp    *0x8a46(%rip)        # afa0 <io_uring_register_eventfd@LIBURING_2.0>
    255a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002560 <pthread_join@plt>:
    2560:	f3 0f 1e fa          	endbr64
    2564:	ff 25 3e 8a 00 00    	jmp    *0x8a3e(%rip)        # afa8 <pthread_join@GLIBC_2.34>
    256a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002570 <strerror@plt>:
    2570:	f3 0f 1e fa          	endbr64
    2574:	ff 25 36 8a 00 00    	jmp    *0x8a36(%rip)        # afb0 <strerror@GLIBC_2.2.5>
    257a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002580 <pthread_mutex_init@plt>:
    2580:	f3 0f 1e fa          	endbr64
    2584:	ff 25 2e 8a 00 00    	jmp    *0x8a2e(%rip)        # afb8 <pthread_mutex_init@GLIBC_2.2.5>
    258a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002590 <__ctype_tolower_loc@plt>:
    2590:	f3 0f 1e fa          	endbr64
    2594:	ff 25 26 8a 00 00    	jmp    *0x8a26(%rip)        # afc0 <__ctype_tolower_loc@GLIBC_2.3>
    259a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025a0 <__sprintf_chk@plt>:
    25a0:	f3 0f 1e fa          	endbr64
    25a4:	ff 25 1e 8a 00 00    	jmp    *0x8a1e(%rip)        # afc8 <__sprintf_chk@GLIBC_2.3.4>
    25aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025b0 <socket@plt>:
    25b0:	f3 0f 1e fa          	endbr64
    25b4:	ff 25 16 8a 00 00    	jmp    *0x8a16(%rip)        # afd0 <socket@GLIBC_2.2.5>
    25ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

00000000000025c0 <fatal_error>:
    25c0:	f3 0f 1e fa          	endbr64
    25c4:	50                   	push   %rax
    25c5:	58                   	pop    %rax
    25c6:	50                   	push   %rax
    25c7:	e8 34 ff ff ff       	call   2500 <perror@plt>
    25cc:	bf 01 00 00 00       	mov    $0x1,%edi
    25d1:	e8 3a ff ff ff       	call   2510 <exit@plt>

00000000000025d6 <copy_file_contents.cold>:
    25d6:	48 8d 3d 49 5c 00 00 	lea    0x5c49(%rip),%rdi        # 8226 <_IO_stdin_used+0x226>
    25dd:	e8 de ff ff ff       	call   25c0 <fatal_error>

00000000000025e2 <add_write_request.cold>:
    25e2:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    25e8:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25f0:	0f 0b                	ud2

00000000000025f2 <add_read_request.cold>:
    25f2:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25fa:	0f 0b                	ud2

00000000000025fc <_send_static_string_content.cold>:
    25fc:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    2602:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    260a:	0f 0b                	ud2

000000000000260c <add_accept_request.cold>:
    260c:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2614:	0f 0b                	ud2

0000000000002616 <io_thread.cold>:
    2616:	48 8d 3d d9 5b 00 00 	lea    0x5bd9(%rip),%rdi        # 81f6 <_IO_stdin_used+0x1f6>
    261d:	e8 9e ff ff ff       	call   25c0 <fatal_error>
    2622:	48 8d 3d 51 5b 00 00 	lea    0x5b51(%rip),%rdi        # 817a <_IO_stdin_used+0x17a>
    2629:	e8 92 ff ff ff       	call   25c0 <fatal_error>
    262e:	48 8d 3d 65 5b 00 00 	lea    0x5b65(%rip),%rdi        # 819a <_IO_stdin_used+0x19a>
    2635:	e8 86 ff ff ff       	call   25c0 <fatal_error>
    263a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2642:	0f 0b                	ud2
    2644:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    264c:	0f 0b                	ud2
    264e:	48 8d 3d 1c 5b 00 00 	lea    0x5b1c(%rip),%rdi        # 8171 <_IO_stdin_used+0x171>
    2655:	e8 66 ff ff ff       	call   25c0 <fatal_error>
    265a:	48 8d 3d 32 5b 00 00 	lea    0x5b32(%rip),%rdi        # 8193 <_IO_stdin_used+0x193>
    2661:	e8 5a ff ff ff       	call   25c0 <fatal_error>
    2666:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000002670 <main>:
    2670:	f3 0f 1e fa          	endbr64
    2674:	41 57                	push   %r15
    2676:	48 8d 3d e3 5f 00 00 	lea    0x5fe3(%rip),%rdi        # 8660 <_IO_stdin_used+0x660>
    267d:	41 56                	push   %r14
    267f:	41 55                	push   %r13
    2681:	41 54                	push   %r12
    2683:	55                   	push   %rbp
    2684:	48 8d 2d f1 5c 00 00 	lea    0x5cf1(%rip),%rbp        # 837c <_IO_stdin_used+0x37c>
    268b:	53                   	push   %rbx
    268c:	48 81 ec 08 01 00 00 	sub    $0x108,%rsp
    2693:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    269c:	48 89 84 24 f8 00 00 00 	mov    %rax,0xf8(%rsp)
    26a4:	48 8d 05 85 1e 00 00 	lea    0x1e85(%rip),%rax        # 4530 <barriered_reset>
    26ab:	66 48 0f 6e f0       	movq   %rax,%xmm6
    26b0:	0f 16 35 a1 85 00 00 	movhps 0x85a1(%rip),%xmm6        # ac58 <__do_global_dtors_aux_fini_array_entry+0x8>
    26b7:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    26bf:	e8 6c fc ff ff       	call   2330 <puts@plt>
    26c4:	bf 0a 00 00 00       	mov    $0xa,%edi
    26c9:	e8 42 fc ff ff       	call   2310 <putchar@plt>
    26ce:	ba 01 00 00 00       	mov    $0x1,%edx
    26d3:	48 8d 35 9a 5b 00 00 	lea    0x5b9a(%rip),%rsi        # 8274 <_IO_stdin_used+0x274>
    26da:	31 c0                	xor    %eax,%eax
    26dc:	bf 01 00 00 00       	mov    $0x1,%edi
    26e1:	e8 ca fd ff ff       	call   24b0 <__printf_chk@plt>
    26e6:	ba 06 00 00 00       	mov    $0x6,%edx
    26eb:	48 8d 35 92 5b 00 00 	lea    0x5b92(%rip),%rsi        # 8284 <_IO_stdin_used+0x284>
    26f2:	31 c0                	xor    %eax,%eax
    26f4:	bf 01 00 00 00       	mov    $0x1,%edi
    26f9:	e8 b2 fd ff ff       	call   24b0 <__printf_chk@plt>
    26fe:	ba 03 00 00 00       	mov    $0x3,%edx
    2703:	48 8d 35 8f 5b 00 00 	lea    0x5b8f(%rip),%rsi        # 8299 <_IO_stdin_used+0x299>
    270a:	31 c0                	xor    %eax,%eax
    270c:	bf 01 00 00 00       	mov    $0x1,%edi
    2711:	e8 9a fd ff ff       	call   24b0 <__printf_chk@plt>
    2716:	ba 02 00 00 00       	mov    $0x2,%edx
    271b:	48 8d 35 87 5b 00 00 	lea    0x5b87(%rip),%rsi        # 82a9 <_IO_stdin_used+0x2a9>
    2722:	31 c0                	xor    %eax,%eax
    2724:	bf 01 00 00 00       	mov    $0x1,%edi
    2729:	e8 82 fd ff ff       	call   24b0 <__printf_chk@plt>
    272e:	48 8d 3d 8a 5b 00 00 	lea    0x5b8a(%rip),%rdi        # 82bf <_IO_stdin_used+0x2bf>
    2735:	e8 f6 fb ff ff       	call   2330 <puts@plt>
    273a:	ba 02 00 00 00       	mov    $0x2,%edx
    273f:	48 8d 35 95 5b 00 00 	lea    0x5b95(%rip),%rsi        # 82db <_IO_stdin_used+0x2db>
    2746:	31 c0                	xor    %eax,%eax
    2748:	bf 01 00 00 00       	mov    $0x1,%edi
    274d:	e8 5e fd ff ff       	call   24b0 <__printf_chk@plt>
    2752:	ba 0a 00 00 00       	mov    $0xa,%edx
    2757:	48 8d 35 97 5b 00 00 	lea    0x5b97(%rip),%rsi        # 82f5 <_IO_stdin_used+0x2f5>
    275e:	31 c0                	xor    %eax,%eax
    2760:	bf 01 00 00 00       	mov    $0x1,%edi
    2765:	e8 46 fd ff ff       	call   24b0 <__printf_chk@plt>
    276a:	ba 01 00 00 00       	mov    $0x1,%edx
    276f:	48 8d 35 93 5b 00 00 	lea    0x5b93(%rip),%rsi        # 8309 <_IO_stdin_used+0x309>
    2776:	31 c0                	xor    %eax,%eax
    2778:	bf 01 00 00 00       	mov    $0x1,%edi
    277d:	e8 2e fd ff ff       	call   24b0 <__printf_chk@plt>
    2782:	ba 01 00 00 00       	mov    $0x1,%edx
    2787:	48 8d 35 8c 5b 00 00 	lea    0x5b8c(%rip),%rsi        # 831a <_IO_stdin_used+0x31a>
    278e:	31 c0                	xor    %eax,%eax
    2790:	bf 01 00 00 00       	mov    $0x1,%edi
    2795:	e8 16 fd ff ff       	call   24b0 <__printf_chk@plt>
    279a:	ba 02 00 00 00       	mov    $0x2,%edx
    279f:	48 8d 35 8c 5b 00 00 	lea    0x5b8c(%rip),%rsi        # 8332 <_IO_stdin_used+0x332>
    27a6:	31 c0                	xor    %eax,%eax
    27a8:	bf 01 00 00 00       	mov    $0x1,%edi
    27ad:	e8 fe fc ff ff       	call   24b0 <__printf_chk@plt>
    27b2:	ba 01 00 00 00       	mov    $0x1,%edx
    27b7:	48 8d 35 0a 5f 00 00 	lea    0x5f0a(%rip),%rsi        # 86c8 <_IO_stdin_used+0x6c8>
    27be:	31 c0                	xor    %eax,%eax
    27c0:	bf 01 00 00 00       	mov    $0x1,%edi
    27c5:	e8 e6 fc ff ff       	call   24b0 <__printf_chk@plt>
    27ca:	ba 01 00 00 00       	mov    $0x1,%edx
    27cf:	48 8d 35 22 5f 00 00 	lea    0x5f22(%rip),%rsi        # 86f8 <_IO_stdin_used+0x6f8>
    27d6:	31 c0                	xor    %eax,%eax
    27d8:	bf 01 00 00 00       	mov    $0x1,%edi
    27dd:	e8 ce fc ff ff       	call   24b0 <__printf_chk@plt>
    27e2:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    27e7:	48 8d 35 60 5b 00 00 	lea    0x5b60(%rip),%rsi        # 834e <_IO_stdin_used+0x34e>
    27ee:	31 c0                	xor    %eax,%eax
    27f0:	bf 01 00 00 00       	mov    $0x1,%edi
    27f5:	e8 b6 fc ff ff       	call   24b0 <__printf_chk@plt>
    27fa:	ba 05 00 00 00       	mov    $0x5,%edx
    27ff:	48 8d 35 62 5b 00 00 	lea    0x5b62(%rip),%rsi        # 8368 <_IO_stdin_used+0x368>
    2806:	31 c0                	xor    %eax,%eax
    2808:	bf 01 00 00 00       	mov    $0x1,%edi
    280d:	e8 9e fc ff ff       	call   24b0 <__printf_chk@plt>
    2812:	48 8d 3d dc 58 00 00 	lea    0x58dc(%rip),%rdi        # 80f5 <_IO_stdin_used+0xf5>
    2819:	e8 12 fb ff ff       	call   2330 <puts@plt>
    281e:	be 18 00 00 00       	mov    $0x18,%esi
    2823:	bf 03 00 00 00       	mov    $0x3,%edi
    2828:	e8 d3 fb ff ff       	call   2400 <calloc@plt>
    282d:	be d8 00 00 00       	mov    $0xd8,%esi
    2832:	45 31 f6             	xor    %r14d,%r14d
    2835:	45 31 ed             	xor    %r13d,%r13d
    2838:	bf 0a 00 00 00       	mov    $0xa,%edi
    283d:	48 89 84 24 a0 00 00 00 	mov    %rax,0xa0(%rsp)
    2845:	e8 b6 fb ff ff       	call   2400 <calloc@plt>
    284a:	be 28 00 00 00       	mov    $0x28,%esi
    284f:	bf 01 00 00 00       	mov    $0x1,%edi
    2854:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2859:	e8 a2 fb ff ff       	call   2400 <calloc@plt>
    285e:	be 28 00 00 00       	mov    $0x28,%esi
    2863:	bf 64 00 00 00       	mov    $0x64,%edi
    2868:	48 89 84 24 d0 00 00 00 	mov    %rax,0xd0(%rsp)
    2870:	e8 8b fb ff ff       	call   2400 <calloc@plt>
    2875:	48 89 84 24 d8 00 00 00 	mov    %rax,0xd8(%rsp)
    287d:	49 89 c7             	mov    %rax,%r15
    2880:	4d 89 fc             	mov    %r15,%r12
    2883:	31 db                	xor    %ebx,%ebx
    2885:	0f 1f 00             	nopl   (%rax)
    2888:	41 8d 54 1d 00       	lea    0x0(%r13,%rbx,1),%edx
    288d:	41 89 d8             	mov    %ebx,%r8d
    2890:	44 89 f1             	mov    %r14d,%ecx
    2893:	48 89 ee             	mov    %rbp,%rsi
    2896:	bf 01 00 00 00       	mov    $0x1,%edi
    289b:	31 c0                	xor    %eax,%eax
    289d:	83 c3 01             	add    $0x1,%ebx
    28a0:	e8 0b fc ff ff       	call   24b0 <__printf_chk@plt>
    28a5:	4c 89 e7             	mov    %r12,%rdi
    28a8:	31 f6                	xor    %esi,%esi
    28aa:	49 83 c4 28          	add    $0x28,%r12
    28ae:	e8 cd fc ff ff       	call   2580 <pthread_mutex_init@plt>
    28b3:	83 fb 0a             	cmp    $0xa,%ebx
    28b6:	75 d0                	jne    2888 <main+0x218>
    28b8:	41 83 c5 0a          	add    $0xa,%r13d
    28bc:	41 83 c6 01          	add    $0x1,%r14d
    28c0:	49 81 c7 90 01 00 00 	add    $0x190,%r15
    28c7:	41 83 fd 64          	cmp    $0x64,%r13d
    28cb:	75 b3                	jne    2880 <main+0x210>
    28cd:	ba 06 00 00 00       	mov    $0x6,%edx
    28d2:	48 8d 35 b3 5a 00 00 	lea    0x5ab3(%rip),%rsi        # 838c <_IO_stdin_used+0x38c>
    28d9:	bf 01 00 00 00       	mov    $0x1,%edi
    28de:	31 c0                	xor    %eax,%eax
    28e0:	e8 cb fb ff ff       	call   24b0 <__printf_chk@plt>
    28e5:	ba 0c 00 00 00       	mov    $0xc,%edx
    28ea:	48 8d 35 b1 5a 00 00 	lea    0x5ab1(%rip),%rsi        # 83a2 <_IO_stdin_used+0x3a2>
    28f1:	31 c0                	xor    %eax,%eax
    28f3:	bf 01 00 00 00       	mov    $0x1,%edi
    28f8:	e8 b3 fb ff ff       	call   24b0 <__printf_chk@plt>
    28fd:	be 10 00 00 00       	mov    $0x10,%esi
    2902:	bf 0c 00 00 00       	mov    $0xc,%edi
    2907:	e8 f4 fa ff ff       	call   2400 <calloc@plt>
    290c:	48 89 84 24 c0 00 00 00 	mov    %rax,0xc0(%rsp)
    2914:	49 89 c7             	mov    %rax,%r15
    2917:	48 8d 98 c0 00 00 00 	lea    0xc0(%rax),%rbx
    291e:	49 89 c5             	mov    %rax,%r13
    2921:	be 00 01 00 00       	mov    $0x100,%esi
    2926:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    292e:	bf 01 00 00 00       	mov    $0x1,%edi
    2933:	49 83 c5 10          	add    $0x10,%r13
    2937:	e8 c4 fa ff ff       	call   2400 <calloc@plt>
    293c:	be 20 00 00 00       	mov    $0x20,%esi
    2941:	bf 64 00 00 00       	mov    $0x64,%edi
    2946:	49 89 45 f8          	mov    %rax,-0x8(%r13)
    294a:	48 89 c5             	mov    %rax,%rbp
    294d:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    2957:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
    2961:	e8 9a fa ff ff       	call   2400 <calloc@plt>
    2966:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
    296d:	4c 39 eb             	cmp    %r13,%rbx
    2970:	75 af                	jne    2921 <main+0x2b1>
    2972:	48 8b b4 24 a0 00 00 00 	mov    0xa0(%rsp),%rsi
    297a:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    297f:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
    2987:	45 31 f6             	xor    %r14d,%r14d
    298a:	c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rsp)
    2995:	45 31 e4             	xor    %r12d,%r12d
    2998:	48 89 b4 24 90 00 00 00 	mov    %rsi,0x90(%rsp)
    29a0:	48 89 dd             	mov    %rbx,%rbp
    29a3:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
    29ab:	48 89 9c 24 a8 00 00 00 	mov    %rbx,0xa8(%rsp)
    29b3:	4c 89 fb             	mov    %r15,%rbx
    29b6:	45 89 f7             	mov    %r14d,%r15d
    29b9:	48 63 84 24 80 00 00 00 	movslq 0x80(%rsp),%rax
    29c1:	44 89 bc 24 84 00 00 00 	mov    %r15d,0x84(%rsp)
    29c9:	49 89 e9             	mov    %rbp,%r9
    29cc:	48 89 ac 24 e0 00 00 00 	mov    %rbp,0xe0(%rsp)
    29d4:	48 c1 e0 04          	shl    $0x4,%rax
    29d8:	48 89 b4 24 c8 00 00 00 	mov    %rsi,0xc8(%rsp)
    29e0:	48 01 d8             	add    %rbx,%rax
    29e3:	48 89 9c 24 e8 00 00 00 	mov    %rbx,0xe8(%rsp)
    29eb:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    29f0:	43 8d 04 3f          	lea    (%r15,%r15,1),%eax
    29f4:	8d 78 01             	lea    0x1(%rax),%edi
    29f7:	83 c0 03             	add    $0x3,%eax
    29fa:	89 7c 24 20          	mov    %edi,0x20(%rsp)
    29fe:	89 84 24 9c 00 00 00 	mov    %eax,0x9c(%rsp)
    2a05:	44 8b 74 24 20       	mov    0x20(%rsp),%r14d
    2a0a:	8b 94 24 84 00 00 00 	mov    0x84(%rsp),%edx
    2a11:	48 8d 35 08 5d 00 00 	lea    0x5d08(%rip),%rsi        # 8720 <_IO_stdin_used+0x720>
    2a18:	31 c0                	xor    %eax,%eax
    2a1a:	bf 01 00 00 00       	mov    $0x1,%edi
    2a1f:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2a24:	45 8d 7e ff          	lea    -0x1(%r14),%r15d
    2a28:	44 89 f9             	mov    %r15d,%ecx
    2a2b:	e8 80 fa ff ff       	call   24b0 <__printf_chk@plt>
    2a30:	be 08 00 00 00       	mov    $0x8,%esi
    2a35:	bf 02 00 00 00       	mov    $0x2,%edi
    2a3a:	e8 c1 f9 ff ff       	call   2400 <calloc@plt>
    2a3f:	be 80 00 00 00       	mov    $0x80,%esi
    2a44:	bf 01 00 00 00       	mov    $0x1,%edi
    2a49:	48 89 c3             	mov    %rax,%rbx
    2a4c:	e8 af f9 ff ff       	call   2400 <calloc@plt>
    2a51:	45 89 f8             	mov    %r15d,%r8d
    2a54:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2a59:	41 83 e0 01          	and    $0x1,%r8d
    2a5d:	48 89 c5             	mov    %rax,%rbp
    2a60:	44 89 44 24 58       	mov    %r8d,0x58(%rsp)
    2a65:	0f 84 53 11 00 00    	je     3bbe <main+0x154e>
    2a6b:	45 89 f5             	mov    %r14d,%r13d
    2a6e:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    2a73:	4c 89 ca             	mov    %r9,%rdx
    2a76:	41 8d 45 fe          	lea    -0x2(%r13),%eax
    2a7a:	49 89 c6             	mov    %rax,%r14
    2a7d:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    2a81:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    2a85:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    2a89:	48 8d 73 08          	lea    0x8(%rbx),%rsi
    2a8d:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
    2a92:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
    2a9a:	48 89 03             	mov    %rax,(%rbx)
    2a9d:	44 89 f1             	mov    %r14d,%ecx
    2aa0:	48 8d 35 a9 5c 00 00 	lea    0x5ca9(%rip),%rsi        # 8750 <_IO_stdin_used+0x750>
    2aa7:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2aab:	31 c0                	xor    %eax,%eax
    2aad:	49 89 79 48          	mov    %rdi,0x48(%r9)
    2ab1:	bf 01 00 00 00       	mov    $0x1,%edi
    2ab6:	48 89 53 08          	mov    %rdx,0x8(%rbx)
    2aba:	44 89 fa             	mov    %r15d,%edx
    2abd:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2ac2:	e8 e9 f9 ff ff       	call   24b0 <__printf_chk@plt>
    2ac7:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2acc:	8b 4c 24 7c          	mov    0x7c(%rsp),%ecx
    2ad0:	31 c0                	xor    %eax,%eax
    2ad2:	44 89 fa             	mov    %r15d,%edx
    2ad5:	48 8d 35 a4 5c 00 00 	lea    0x5ca4(%rip),%rsi        # 8780 <_IO_stdin_used+0x780>
    2adc:	bf 01 00 00 00       	mov    $0x1,%edi
    2ae1:	45 89 b1 b8 00 00 00 	mov    %r14d,0xb8(%r9)
    2ae8:	e8 c3 f9 ff ff       	call   24b0 <__printf_chk@plt>
    2aed:	41 83 ff 01          	cmp    $0x1,%r15d
    2af1:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2af6:	0f 87 ec 10 00 00    	ja     3be8 <main+0x1578>
    2afc:	48 63 44 24 7c       	movslq 0x7c(%rsp),%rax
    2b01:	48 89 c7             	mov    %rax,%rdi
    2b04:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2b0a:	77 13                	ja     2b1f <main+0x4af>
    2b0c:	48 c1 e8 06          	shr    $0x6,%rax
    2b10:	ba 01 00 00 00       	mov    $0x1,%edx
    2b15:	89 f9                	mov    %edi,%ecx
    2b17:	48 d3 e2             	shl    %cl,%rdx
    2b1a:	48 09 54 c5 00       	or     %rdx,0x0(%rbp,%rax,8)
    2b1f:	83 44 24 7c 02       	addl   $0x2,0x7c(%rsp)
    2b24:	45 89 79 08          	mov    %r15d,0x8(%r9)
    2b28:	be 10 00 00 00       	mov    $0x10,%esi
    2b2d:	bf 64 00 00 00       	mov    $0x64,%edi
    2b32:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
    2b3a:	49 89 a9 b0 00 00 00 	mov    %rbp,0xb0(%r9)
    2b41:	31 ed                	xor    %ebp,%ebp
    2b43:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
    2b4a:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    2b52:	49 89 59 18          	mov    %rbx,0x18(%r9)
    2b56:	44 89 fb             	mov    %r15d,%ebx
    2b59:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
    2b60:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2b65:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
    2b6c:	49 89 41 20          	mov    %rax,0x20(%r9)
    2b70:	48 8b 05 69 61 00 00 	mov    0x6169(%rip),%rax        # 8ce0 <_IO_stdin_used+0xce0>
    2b77:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
    2b7f:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
    2b86:	48 8b 05 5b 61 00 00 	mov    0x615b(%rip),%rax        # 8ce8 <_IO_stdin_used+0xce8>
    2b8d:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2b92:	49 89 41 28          	mov    %rax,0x28(%r9)
    2b96:	e8 65 f8 ff ff       	call   2400 <calloc@plt>
    2b9b:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2ba0:	be 10 00 00 00       	mov    $0x10,%esi
    2ba5:	bf 64 00 00 00       	mov    $0x64,%edi
    2baa:	49 89 41 68          	mov    %rax,0x68(%r9)
    2bae:	e8 4d f8 ff ff       	call   2400 <calloc@plt>
    2bb3:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2bb8:	be 28 00 00 00       	mov    $0x28,%esi
    2bbd:	66 0f 6f 3d eb 60 00 00 	movdqa 0x60eb(%rip),%xmm7        # 8cb0 <_IO_stdin_used+0xcb0>
    2bc5:	bf 64 00 00 00       	mov    $0x64,%edi
    2bca:	49 89 41 70          	mov    %rax,0x70(%r9)
    2bce:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
    2bd6:	e8 25 f8 ff ff       	call   2400 <calloc@plt>
    2bdb:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2be0:	bf 03 00 00 00       	mov    $0x3,%edi
    2be5:	66 0f 6f 35 c3 60 00 00 	movdqa 0x60c3(%rip),%xmm6        # 8cb0 <_IO_stdin_used+0xcb0>
    2bed:	be 00 02 00 00       	mov    $0x200,%esi
    2bf2:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
    2bf9:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
    2c01:	e8 fa f7 ff ff       	call   2400 <calloc@plt>
    2c06:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2c0b:	4c 89 ef             	mov    %r13,%rdi
    2c0e:	44 8b bc 24 84 00 00 00 	mov    0x84(%rsp),%r15d
    2c16:	49 89 c6             	mov    %rax,%r14
    2c19:	49 89 41 38          	mov    %rax,0x38(%r9)
    2c1d:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
    2c22:	4c 89 f1             	mov    %r14,%rcx
    2c25:	48 0f af f8          	imul   %rax,%rdi
    2c29:	4c 89 4c 24 50       	mov    %r9,0x50(%rsp)
    2c2e:	48 c1 ef 22          	shr    $0x22,%rdi
    2c32:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2c35:	8b 7c 24 20          	mov    0x20(%rsp),%edi
    2c39:	01 c0                	add    %eax,%eax
    2c3b:	29 c7                	sub    %eax,%edi
    2c3d:	89 bc 24 98 00 00 00 	mov    %edi,0x98(%rsp)
    2c44:	48 63 c5             	movslq %ebp,%rax
    2c47:	be 00 01 00 00       	mov    $0x100,%esi
    2c4c:	bf 06 00 00 00       	mov    $0x6,%edi
    2c51:	45 31 f6             	xor    %r14d,%r14d
    2c54:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2c59:	48 c1 e0 09          	shl    $0x9,%rax
    2c5d:	4c 8d 2c 01          	lea    (%rcx,%rax,1),%r13
    2c61:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2c66:	48 8d 05 83 18 00 00 	lea    0x1883(%rip),%rax        # 44f0 <do_protected_write>
    2c6d:	49 89 85 20 01 00 00 	mov    %rax,0x120(%r13)
    2c74:	e8 87 f7 ff ff       	call   2400 <calloc@plt>
    2c79:	8b 74 24 58          	mov    0x58(%rsp),%esi
    2c7d:	49 89 85 70 01 00 00 	mov    %rax,0x170(%r13)
    2c84:	48 89 c1             	mov    %rax,%rcx
    2c87:	85 f6                	test   %esi,%esi
    2c89:	0f 84 91 01 00 00    	je     2e20 <main+0x7b0>
    2c8f:	8b 44 24 20          	mov    0x20(%rsp),%eax
    2c93:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    2c97:	49 89 cd             	mov    %rcx,%r13
    2c9a:	48 89 8c 24 88 00 00 00 	mov    %rcx,0x88(%rsp)
    2ca2:	83 e8 02             	sub    $0x2,%eax
    2ca5:	89 44 24 70          	mov    %eax,0x70(%rsp)
    2ca9:	eb 1a                	jmp    2cc5 <main+0x655>
    2cab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2cb0:	41 83 c6 01          	add    $0x1,%r14d
    2cb4:	49 81 c5 00 01 00 00 	add    $0x100,%r13
    2cbb:	41 83 fe 06          	cmp    $0x6,%r14d
    2cbf:	0f 84 de 02 00 00    	je     2fa3 <main+0x933>
    2cc5:	44 89 f3             	mov    %r14d,%ebx
    2cc8:	31 c0                	xor    %eax,%eax
    2cca:	44 89 f2             	mov    %r14d,%edx
    2ccd:	bf 01 00 00 00       	mov    $0x1,%edi
    2cd2:	d1 fb                	sar    %ebx
    2cd4:	48 8d 35 e1 56 00 00 	lea    0x56e1(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    2cdb:	89 d9                	mov    %ebx,%ecx
    2cdd:	e8 ce f7 ff ff       	call   24b0 <__printf_chk@plt>
    2ce2:	41 39 df             	cmp    %ebx,%r15d
    2ce5:	75 c9                	jne    2cb0 <main+0x640>
    2ce7:	be 08 00 00 00       	mov    $0x8,%esi
    2cec:	bf 01 00 00 00       	mov    $0x1,%edi
    2cf1:	e8 0a f7 ff ff       	call   2400 <calloc@plt>
    2cf6:	be 08 00 00 00       	mov    $0x8,%esi
    2cfb:	bf 01 00 00 00       	mov    $0x1,%edi
    2d00:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2d05:	e8 f6 f6 ff ff       	call   2400 <calloc@plt>
    2d0a:	be 80 04 00 00       	mov    $0x480,%esi
    2d0f:	bf 03 00 00 00       	mov    $0x3,%edi
    2d14:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2d19:	e8 e2 f6 ff ff       	call   2400 <calloc@plt>
    2d1e:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2d22:	44 89 f2             	mov    %r14d,%edx
    2d25:	49 c7 85 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r13)
    2d30:	49 89 c1             	mov    %rax,%r9
    2d33:	89 a8 10 04 00 00    	mov    %ebp,0x410(%rax)
    2d39:	48 8d 35 60 5a 00 00 	lea    0x5a60(%rip),%rsi        # 87a0 <_IO_stdin_used+0x7a0>
    2d40:	bf 01 00 00 00       	mov    $0x1,%edi
    2d45:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
    2d4f:	89 98 0c 04 00 00    	mov    %ebx,0x40c(%rax)
    2d55:	44 89 b0 14 04 00 00 	mov    %r14d,0x414(%rax)
    2d5c:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    2d61:	41 89 81 98 08 00 00 	mov    %eax,0x898(%r9)
    2d68:	49 8d 81 80 04 00 00 	lea    0x480(%r9),%rax
    2d6f:	49 89 85 80 00 00 00 	mov    %rax,0x80(%r13)
    2d76:	8b 44 24 70          	mov    0x70(%rsp),%eax
    2d7a:	45 89 a1 18 04 00 00 	mov    %r12d,0x418(%r9)
    2d81:	41 83 c4 02          	add    $0x2,%r12d
    2d85:	41 c7 81 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r9)
    2d90:	89 c1                	mov    %eax,%ecx
    2d92:	41 89 99 8c 08 00 00 	mov    %ebx,0x88c(%r9)
    2d99:	41 89 a9 90 08 00 00 	mov    %ebp,0x890(%r9)
    2da0:	45 89 b1 94 08 00 00 	mov    %r14d,0x894(%r9)
    2da7:	4d 89 4d 00          	mov    %r9,0x0(%r13)
    2dab:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
    2db6:	41 c7 81 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r9)
    2dc1:	41 89 85 b4 00 00 00 	mov    %eax,0xb4(%r13)
    2dc8:	31 c0                	xor    %eax,%eax
    2dca:	49 c7 85 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r13)
    2dd5:	41 c7 85 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%r13)
    2de0:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2de5:	e8 c6 f6 ff ff       	call   24b0 <__printf_chk@plt>
    2dea:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2def:	4c 8b 5c 24 60       	mov    0x60(%rsp),%r11
    2df4:	66 0f 6f 35 c4 5e 00 00 	movdqa 0x5ec4(%rip),%xmm6        # 8cc0 <_IO_stdin_used+0xcc0>
    2dfc:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    2e01:	4d 89 19             	mov    %r11,(%r9)
    2e04:	4d 89 91 80 04 00 00 	mov    %r10,0x480(%r9)
    2e0b:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
    2e13:	41 0f 29 b1 00 05 00 00 	movaps %xmm6,0x500(%r9)
    2e1b:	e9 90 fe ff ff       	jmp    2cb0 <main+0x640>
    2e20:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    2e24:	49 89 c5             	mov    %rax,%r13
    2e27:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
    2e2c:	eb 17                	jmp    2e45 <main+0x7d5>
    2e2e:	66 90                	xchg   %ax,%ax
    2e30:	41 83 c6 01          	add    $0x1,%r14d
    2e34:	49 81 c5 00 01 00 00 	add    $0x100,%r13
    2e3b:	41 83 fe 06          	cmp    $0x6,%r14d
    2e3f:	0f 84 81 06 00 00    	je     34c6 <main+0xe56>
    2e45:	44 89 f3             	mov    %r14d,%ebx
    2e48:	31 c0                	xor    %eax,%eax
    2e4a:	44 89 f2             	mov    %r14d,%edx
    2e4d:	bf 01 00 00 00       	mov    $0x1,%edi
    2e52:	d1 fb                	sar    %ebx
    2e54:	48 8d 35 61 55 00 00 	lea    0x5561(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    2e5b:	89 d9                	mov    %ebx,%ecx
    2e5d:	e8 4e f6 ff ff       	call   24b0 <__printf_chk@plt>
    2e62:	41 39 df             	cmp    %ebx,%r15d
    2e65:	75 c9                	jne    2e30 <main+0x7c0>
    2e67:	be 08 00 00 00       	mov    $0x8,%esi
    2e6c:	bf 01 00 00 00       	mov    $0x1,%edi
    2e71:	e8 8a f5 ff ff       	call   2400 <calloc@plt>
    2e76:	be 08 00 00 00       	mov    $0x8,%esi
    2e7b:	bf 01 00 00 00       	mov    $0x1,%edi
    2e80:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2e85:	e8 76 f5 ff ff       	call   2400 <calloc@plt>
    2e8a:	be 80 04 00 00       	mov    $0x480,%esi
    2e8f:	bf 03 00 00 00       	mov    $0x3,%edi
    2e94:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2e99:	e8 62 f5 ff ff       	call   2400 <calloc@plt>
    2e9e:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2ea2:	44 89 f2             	mov    %r14d,%edx
    2ea5:	49 c7 85 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r13)
    2eb0:	49 89 c1             	mov    %rax,%r9
    2eb3:	89 a8 10 04 00 00    	mov    %ebp,0x410(%rax)
    2eb9:	48 8d 35 e0 58 00 00 	lea    0x58e0(%rip),%rsi        # 87a0 <_IO_stdin_used+0x7a0>
    2ec0:	bf 01 00 00 00       	mov    $0x1,%edi
    2ec5:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
    2ecf:	89 98 0c 04 00 00    	mov    %ebx,0x40c(%rax)
    2ed5:	44 89 b0 14 04 00 00 	mov    %r14d,0x414(%rax)
    2edc:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    2ee1:	41 89 81 98 08 00 00 	mov    %eax,0x898(%r9)
    2ee8:	49 8d 81 80 04 00 00 	lea    0x480(%r9),%rax
    2eef:	49 89 85 80 00 00 00 	mov    %rax,0x80(%r13)
    2ef6:	8b 84 24 98 00 00 00 	mov    0x98(%rsp),%eax
    2efd:	45 89 a1 18 04 00 00 	mov    %r12d,0x418(%r9)
    2f04:	41 83 c4 02          	add    $0x2,%r12d
    2f08:	41 c7 81 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r9)
    2f13:	89 c1                	mov    %eax,%ecx
    2f15:	41 89 99 8c 08 00 00 	mov    %ebx,0x88c(%r9)
    2f1c:	41 89 a9 90 08 00 00 	mov    %ebp,0x890(%r9)
    2f23:	45 89 b1 94 08 00 00 	mov    %r14d,0x894(%r9)
    2f2a:	4d 89 4d 00          	mov    %r9,0x0(%r13)
    2f2e:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
    2f39:	41 c7 81 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r9)
    2f44:	41 89 85 b4 00 00 00 	mov    %eax,0xb4(%r13)
    2f4b:	31 c0                	xor    %eax,%eax
    2f4d:	49 c7 85 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r13)
    2f58:	41 c7 85 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%r13)
    2f63:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2f68:	e8 43 f5 ff ff       	call   24b0 <__printf_chk@plt>
    2f6d:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2f72:	4c 8b 5c 24 60       	mov    0x60(%rsp),%r11
    2f77:	66 0f 6f 35 41 5d 00 00 	movdqa 0x5d41(%rip),%xmm6        # 8cc0 <_IO_stdin_used+0xcc0>
    2f7f:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    2f84:	4d 89 19             	mov    %r11,(%r9)
    2f87:	4d 89 91 80 04 00 00 	mov    %r10,0x480(%r9)
    2f8e:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
    2f96:	41 0f 29 b1 00 05 00 00 	movaps %xmm6,0x500(%r9)
    2f9e:	e9 8d fe ff ff       	jmp    2e30 <main+0x7c0>
    2fa3:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2fa7:	48 8b 8c 24 88 00 00 00 	mov    0x88(%rsp),%rcx
    2faf:	45 31 ed             	xor    %r13d,%r13d
    2fb2:	44 89 7c 24 08       	mov    %r15d,0x8(%rsp)
    2fb7:	41 89 e8             	mov    %ebp,%r8d
    2fba:	41 89 df             	mov    %ebx,%r15d
    2fbd:	44 89 eb             	mov    %r13d,%ebx
    2fc0:	49 89 cd             	mov    %rcx,%r13
    2fc3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2fc8:	89 d8                	mov    %ebx,%eax
    2fca:	d1 f8                	sar    %eax
    2fcc:	39 44 24 08          	cmp    %eax,0x8(%rsp)
    2fd0:	0f 84 75 01 00 00    	je     314b <main+0xadb>
    2fd6:	89 da                	mov    %ebx,%edx
    2fd8:	48 8d 35 ed 53 00 00 	lea    0x53ed(%rip),%rsi        # 83cc <_IO_stdin_used+0x3cc>
    2fdf:	bf 01 00 00 00       	mov    $0x1,%edi
    2fe4:	31 c0                	xor    %eax,%eax
    2fe6:	44 89 44 24 18       	mov    %r8d,0x18(%rsp)
    2feb:	e8 c0 f4 ff ff       	call   24b0 <__printf_chk@plt>
    2ff0:	be 08 00 00 00       	mov    $0x8,%esi
    2ff5:	bf 01 00 00 00       	mov    $0x1,%edi
    2ffa:	e8 01 f4 ff ff       	call   2400 <calloc@plt>
    2fff:	be 08 00 00 00       	mov    $0x8,%esi
    3004:	bf 01 00 00 00       	mov    $0x1,%edi
    3009:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    300e:	e8 ed f3 ff ff       	call   2400 <calloc@plt>
    3013:	be 80 04 00 00       	mov    $0x480,%esi
    3018:	bf 03 00 00 00       	mov    $0x3,%edi
    301d:	48 89 c5             	mov    %rax,%rbp
    3020:	e8 db f3 ff ff       	call   2400 <calloc@plt>
    3025:	be 80 04 00 00       	mov    $0x480,%esi
    302a:	bf 03 00 00 00       	mov    $0x3,%edi
    302f:	49 89 c6             	mov    %rax,%r14
    3032:	e8 c9 f3 ff ff       	call   2400 <calloc@plt>
    3037:	44 8b 44 24 18       	mov    0x18(%rsp),%r8d
    303c:	41 8d 74 24 01       	lea    0x1(%r12),%esi
    3041:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    3046:	66 0f 6f 35 72 5c 00 00 	movdqa 0x5c72(%rip),%xmm6        # 8cc0 <_IO_stdin_used+0xcc0>
    304e:	4d 89 75 00          	mov    %r14,0x0(%r13)
    3052:	41 89 b6 98 08 00 00 	mov    %esi,0x898(%r14)
    3059:	49 8d b6 80 04 00 00 	lea    0x480(%r14),%rsi
    3060:	45 89 a6 18 04 00 00 	mov    %r12d,0x418(%r14)
    3067:	41 83 c4 02          	add    $0x2,%r12d
    306b:	41 c7 86 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%r14)
    3076:	45 89 be 0c 04 00 00 	mov    %r15d,0x40c(%r14)
    307d:	45 89 86 10 04 00 00 	mov    %r8d,0x410(%r14)
    3084:	41 89 9e 14 04 00 00 	mov    %ebx,0x414(%r14)
    308b:	41 c7 86 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r14)
    3096:	45 89 be 8c 08 00 00 	mov    %r15d,0x88c(%r14)
    309d:	45 89 86 90 08 00 00 	mov    %r8d,0x890(%r14)
    30a4:	41 89 9e 94 08 00 00 	mov    %ebx,0x894(%r14)
    30ab:	4d 89 b5 a0 00 00 00 	mov    %r14,0xa0(%r13)
    30b2:	49 89 b5 80 00 00 00 	mov    %rsi,0x80(%r13)
    30b9:	49 c7 85 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r13)
    30c4:	49 c7 85 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r13)
    30cf:	41 c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r14)
    30da:	41 c7 86 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r14)
    30e5:	49 89 b5 a8 00 00 00 	mov    %rsi,0xa8(%r13)
    30ec:	41 c7 85 b0 00 00 00 02 00 00 00 	movl   $0x2,0xb0(%r13)
    30f7:	4c 89 30             	mov    %r14,(%rax)
    30fa:	48 89 70 08          	mov    %rsi,0x8(%rax)
    30fe:	49 89 85 98 00 00 00 	mov    %rax,0x98(%r13)
    3105:	41 c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r14)
    3110:	41 c7 86 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r14)
    311b:	49 89 16             	mov    %rdx,(%r14)
    311e:	49 89 ae 80 04 00 00 	mov    %rbp,0x480(%r14)
    3125:	41 c7 86 80 05 00 00 01 00 00 00 	movl   $0x1,0x580(%r14)
    3130:	41 c7 86 00 06 00 00 00 00 00 00 	movl   $0x0,0x600(%r14)
    313b:	41 0f 29 b6 80 00 00 00 	movaps %xmm6,0x80(%r14)
    3143:	41 0f 29 b6 00 05 00 00 	movaps %xmm6,0x500(%r14)
    314b:	83 c3 01             	add    $0x1,%ebx
    314e:	49 81 c5 00 01 00 00 	add    $0x100,%r13
    3155:	83 fb 06             	cmp    $0x6,%ebx
    3158:	0f 85 6a fe ff ff    	jne    2fc8 <main+0x958>
    315e:	be 01 00 00 00       	mov    $0x1,%esi
    3163:	bf 00 01 00 00       	mov    $0x100,%edi
    3168:	44 89 c5             	mov    %r8d,%ebp
    316b:	44 89 fb             	mov    %r15d,%ebx
    316e:	44 8b 7c 24 08       	mov    0x8(%rsp),%r15d
    3173:	e8 88 f2 ff ff       	call   2400 <calloc@plt>
    3178:	bf 20 00 00 00       	mov    $0x20,%edi
    317d:	49 89 c5             	mov    %rax,%r13
    3180:	e8 eb f2 ff ff       	call   2470 <malloc@plt>
    3185:	48 83 ec 08          	sub    $0x8,%rsp
    3189:	4c 89 ef             	mov    %r13,%rdi
    318c:	41 89 e9             	mov    %ebp,%r9d
    318f:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    3194:	41 89 d8             	mov    %ebx,%r8d
    3197:	ba 00 01 00 00       	mov    $0x100,%edx
    319c:	31 c0                	xor    %eax,%eax
    319e:	41 57                	push   %r15
    31a0:	48 8d 0d 21 56 00 00 	lea    0x5621(%rip),%rcx        # 87c8 <_IO_stdin_used+0x7c8>
    31a7:	be 01 00 00 00       	mov    $0x1,%esi
    31ac:	e8 ef f3 ff ff       	call   25a0 <__sprintf_chk@plt>
    31b1:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    31b6:	4c 8b 74 24 60       	mov    0x60(%rsp),%r14
    31bb:	be 20 00 00 00       	mov    $0x20,%esi
    31c0:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    31c5:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    31ca:	bf 63 00 00 00       	mov    $0x63,%edi
    31cf:	49 8b 4e 38          	mov    0x38(%r14),%rcx
    31d3:	4d 89 2a             	mov    %r13,(%r10)
    31d6:	49 89 42 10          	mov    %rax,0x10(%r10)
    31da:	49 63 46 08          	movslq 0x8(%r14),%rax
    31de:	48 01 ca             	add    %rcx,%rdx
    31e1:	45 89 7a 18          	mov    %r15d,0x18(%r10)
    31e5:	49 89 42 08          	mov    %rax,0x8(%r10)
    31e9:	8b 44 24 38          	mov    0x38(%rsp),%eax
    31ed:	44 89 ba 9c 01 00 00 	mov    %r15d,0x19c(%rdx)
    31f4:	89 82 a0 01 00 00    	mov    %eax,0x1a0(%rdx)
    31fa:	83 c0 01             	add    $0x1,%eax
    31fd:	89 44 24 38          	mov    %eax,0x38(%rsp)
    3201:	8d 45 01             	lea    0x1(%rbp),%eax
    3204:	83 e0 01             	and    $0x1,%eax
    3207:	c7 02 41 00 00 00    	movl   $0x41,(%rdx)
    320d:	89 82 98 01 00 00    	mov    %eax,0x198(%rdx)
    3213:	4c 89 92 90 01 00 00 	mov    %r10,0x190(%rdx)
    321a:	c7 82 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rdx)
    3224:	48 c7 82 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rdx)
    322f:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    3234:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    3239:	e8 c2 f1 ff ff       	call   2400 <calloc@plt>
    323e:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    3243:	48 89 82 50 01 00 00 	mov    %rax,0x150(%rdx)
    324a:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    324f:	48 c7 82 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rdx)
    325a:	48 8b 00             	mov    (%rax),%rax
    325d:	8b 70 04             	mov    0x4(%rax),%esi
    3260:	4c 39 f0             	cmp    %r14,%rax
    3263:	48 89 82 28 01 00 00 	mov    %rax,0x128(%rdx)
    326a:	89 b2 30 01 00 00    	mov    %esi,0x130(%rdx)
    3270:	41 5d                	pop    %r13
    3272:	59                   	pop    %rcx
    3273:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    3278:	0f 85 6e 11 00 00    	jne    43ec <main+0x1d7c>
    327e:	66 0f 6f 05 4a 5a 00 00 	movdqa 0x5a4a(%rip),%xmm0        # 8cd0 <_IO_stdin_used+0xcd0>
    3286:	89 6a 04             	mov    %ebp,0x4(%rdx)
    3289:	4c 8b 2d 60 5a 00 00 	mov    0x5a60(%rip),%r13        # 8cf0 <_IO_stdin_used+0xcf0>
    3290:	c7 82 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rdx)
    329a:	c7 82 8c 01 00 00 02 00 00 00 	movl   $0x2,0x18c(%rdx)
    32a4:	4c 89 aa 44 01 00 00 	mov    %r13,0x144(%rdx)
    32ab:	0f 11 82 34 01 00 00 	movups %xmm0,0x134(%rdx)
    32b2:	83 fd 01             	cmp    $0x1,%ebp
    32b5:	0f 84 31 02 00 00    	je     34ec <main+0xe7c>
    32bb:	85 ed                	test   %ebp,%ebp
    32bd:	0f 84 11 02 00 00    	je     34d4 <main+0xe64>
    32c3:	4c 8b 4c 24 50       	mov    0x50(%rsp),%r9
    32c8:	48 8d 05 71 37 00 00 	lea    0x3771(%rip),%rax        # 6a40 <barriered_work>
    32cf:	be 08 00 00 00       	mov    $0x8,%esi
    32d4:	49 89 ce             	mov    %rcx,%r14
    32d7:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
    32de:	bf 01 00 00 00       	mov    $0x1,%edi
    32e3:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    32ee:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    32f3:	e8 08 f1 ff ff       	call   2400 <calloc@plt>
    32f8:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    32fd:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
    3302:	66 0f 6f bc 24 b0 00 00 00 	movdqa 0xb0(%rsp),%xmm7
    330b:	83 44 24 20 01       	addl   $0x1,0x20(%rsp)
    3310:	48 89 18             	mov    %rbx,(%rax)
    3313:	48 83 c3 10          	add    $0x10,%rbx
    3317:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    331e:	49 89 81 78 ff ff ff 	mov    %rax,-0x88(%r9)
    3325:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    332a:	83 84 24 80 00 00 00 01 	addl   $0x1,0x80(%rsp)
    3332:	48 8b 00             	mov    (%rax),%rax
    3335:	48 89 5c 24 68       	mov    %rbx,0x68(%rsp)
    333a:	41 c7 86 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r14)
    3345:	49 89 86 28 05 00 00 	mov    %rax,0x528(%r14)
    334c:	41 c7 86 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r14)
    3357:	41 c7 86 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r14)
    3362:	41 8b 81 2c ff ff ff 	mov    -0xd4(%r9),%eax
    3369:	41 0f 11 be 18 05 00 00 	movups %xmm7,0x518(%r14)
    3371:	41 89 86 30 05 00 00 	mov    %eax,0x530(%r14)
    3378:	8b 44 24 20          	mov    0x20(%rsp),%eax
    337c:	41 c7 86 8c 05 00 00 02 00 00 00 	movl   $0x2,0x58c(%r14)
    3387:	4d 89 ae 44 05 00 00 	mov    %r13,0x544(%r14)
    338e:	39 84 24 9c 00 00 00 	cmp    %eax,0x9c(%rsp)
    3395:	0f 85 6a f6 ff ff    	jne    2a05 <main+0x395>
    339b:	44 8b bc 24 84 00 00 00 	mov    0x84(%rsp),%r15d
    33a3:	48 8b ac 24 e0 00 00 00 	mov    0xe0(%rsp),%rbp
    33ab:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    33b3:	48 8b 9c 24 e8 00 00 00 	mov    0xe8(%rsp),%rbx
    33bb:	41 83 c7 01          	add    $0x1,%r15d
    33bf:	48 81 c5 b0 01 00 00 	add    $0x1b0,%rbp
    33c6:	48 83 c6 18          	add    $0x18,%rsi
    33ca:	41 83 ff 03          	cmp    $0x3,%r15d
    33ce:	0f 85 e5 f5 ff ff    	jne    29b9 <main+0x349>
    33d4:	be 08 00 00 00       	mov    $0x8,%esi
    33d9:	bf 00 04 00 00       	mov    $0x400,%edi
    33de:	31 ed                	xor    %ebp,%ebp
    33e0:	e8 1b f0 ff ff       	call   2400 <calloc@plt>
    33e5:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    33ea:	49 89 c7             	mov    %rax,%r15
    33ed:	31 c0                	xor    %eax,%eax
    33ef:	49 89 d1             	mov    %rdx,%r9
    33f2:	31 db                	xor    %ebx,%ebx
    33f4:	45 8b 51 40          	mov    0x40(%r9),%r10d
    33f8:	45 85 d2             	test   %r10d,%r10d
    33fb:	0f 8e b0 00 00 00    	jle    34b1 <main+0xe41>
    3401:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3405:	4d 63 c2             	movslq %r10d,%r8
    3408:	48 63 cd             	movslq %ebp,%rcx
    340b:	49 c1 e0 09          	shl    $0x9,%r8
    340f:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    3413:	49 01 f8             	add    %rdi,%r8
    3416:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3420:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
    3427:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    342e:	48 83 c6 60          	add    $0x60,%rsi
    3432:	f3 0f 7e a1 00 01 00 00 	movq   0x100(%rcx),%xmm4
    343a:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    343e:	f3 0f 7e 99 00 02 00 00 	movq   0x200(%rcx),%xmm3
    3446:	f3 0f 7e 91 00 03 00 00 	movq   0x300(%rcx),%xmm2
    344e:	f3 0f 7e 89 00 04 00 00 	movq   0x400(%rcx),%xmm1
    3456:	0f 16 a1 80 01 00 00 	movhps 0x180(%rcx),%xmm4
    345d:	f3 0f 7e 81 00 05 00 00 	movq   0x500(%rcx),%xmm0
    3465:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    346c:	0f 16 99 80 02 00 00 	movhps 0x280(%rcx),%xmm3
    3473:	0f 16 91 80 03 00 00 	movhps 0x380(%rcx),%xmm2
    347a:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    347e:	0f 16 89 80 04 00 00 	movhps 0x480(%rcx),%xmm1
    3485:	0f 16 81 80 05 00 00 	movhps 0x580(%rcx),%xmm0
    348c:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3490:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3494:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3498:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    349c:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
    34a0:	49 39 f8             	cmp    %rdi,%r8
    34a3:	0f 85 77 ff ff ff    	jne    3420 <main+0xdb0>
    34a9:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    34ad:	8d 6c 8d 00          	lea    0x0(%rbp,%rcx,4),%ebp
    34b1:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    34b8:	85 db                	test   %ebx,%ebx
    34ba:	75 3e                	jne    34fa <main+0xe8a>
    34bc:	bb 01 00 00 00       	mov    $0x1,%ebx
    34c1:	e9 2e ff ff ff       	jmp    33f4 <main+0xd84>
    34c6:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    34ca:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    34cf:	e9 db fa ff ff       	jmp    2faf <main+0x93f>
    34d4:	48 8d 05 d5 39 00 00 	lea    0x39d5(%rip),%rax        # 6eb0 <barriered_work_ingest_andwork>
    34db:	bd 01 00 00 00       	mov    $0x1,%ebp
    34e0:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
    34e7:	e9 58 f7 ff ff       	jmp    2c44 <main+0x5d4>
    34ec:	48 8d 05 4d 35 00 00 	lea    0x354d(%rip),%rax        # 6a40 <barriered_work>
    34f3:	bd 02 00 00 00       	mov    $0x2,%ebp
    34f8:	eb e6                	jmp    34e0 <main+0xe70>
    34fa:	83 c0 02             	add    $0x2,%eax
    34fd:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    3504:	83 f8 06             	cmp    $0x6,%eax
    3507:	0f 85 e2 fe ff ff    	jne    33ef <main+0xd7f>
    350d:	48 8d 3d d6 4e 00 00 	lea    0x4ed6(%rip),%rdi        # 83ea <_IO_stdin_used+0x3ea>
    3514:	e8 17 ee ff ff       	call   2330 <puts@plt>
    3519:	48 8d 35 df 4e 00 00 	lea    0x4edf(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3520:	48 8d 3d da 4e 00 00 	lea    0x4eda(%rip),%rdi        # 8401 <_IO_stdin_used+0x401>
    3527:	e8 c4 ef ff ff       	call   24f0 <fopen@plt>
    352c:	49 89 c6             	mov    %rax,%r14
    352f:	85 ed                	test   %ebp,%ebp
    3531:	7e 76                	jle    35a9 <main+0xf39>
    3533:	48 63 ed             	movslq %ebp,%rbp
    3536:	4c 8d 2d a1 4e 00 00 	lea    0x4ea1(%rip),%r13        # 83de <_IO_stdin_used+0x3de>
    353d:	4c 8d 25 de 4e 00 00 	lea    0x4ede(%rip),%r12        # 8422 <_IO_stdin_used+0x422>
    3544:	49 8d 04 ef          	lea    (%r15,%rbp,8),%rax
    3548:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    354d:	be 01 00 00 00       	mov    $0x1,%esi
    3552:	bf fa 00 00 00       	mov    $0xfa,%edi
    3557:	49 83 c7 08          	add    $0x8,%r15
    355b:	e8 a0 ee ff ff       	call   2400 <calloc@plt>
    3560:	4c 89 e9             	mov    %r13,%rcx
    3563:	ba fa 00 00 00       	mov    $0xfa,%edx
    3568:	be 01 00 00 00       	mov    $0x1,%esi
    356d:	48 89 c5             	mov    %rax,%rbp
    3570:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3574:	48 89 ef             	mov    %rbp,%rdi
    3577:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    357e:	31 c0                	xor    %eax,%eax
    3580:	e8 1b f0 ff ff       	call   25a0 <__sprintf_chk@plt>
    3585:	48 89 ea             	mov    %rbp,%rdx
    3588:	4c 89 e6             	mov    %r12,%rsi
    358b:	bf 01 00 00 00       	mov    $0x1,%edi
    3590:	31 c0                	xor    %eax,%eax
    3592:	e8 19 ef ff ff       	call   24b0 <__printf_chk@plt>
    3597:	4c 89 f6             	mov    %r14,%rsi
    359a:	48 89 ef             	mov    %rbp,%rdi
    359d:	e8 1e ee ff ff       	call   23c0 <fputs@plt>
    35a2:	4c 39 7c 24 08       	cmp    %r15,0x8(%rsp)
    35a7:	75 a4                	jne    354d <main+0xedd>
    35a9:	4c 89 f7             	mov    %r14,%rdi
    35ac:	45 31 f6             	xor    %r14d,%r14d
    35af:	4c 8d 25 96 4e 00 00 	lea    0x4e96(%rip),%r12        # 844c <_IO_stdin_used+0x44c>
    35b6:	e8 a5 ed ff ff       	call   2360 <fclose@plt>
    35bb:	48 8d 3d 48 4e 00 00 	lea    0x4e48(%rip),%rdi        # 840a <_IO_stdin_used+0x40a>
    35c2:	45 89 f7             	mov    %r14d,%r15d
    35c5:	41 89 de             	mov    %ebx,%r14d
    35c8:	e8 63 ed ff ff       	call   2330 <puts@plt>
    35cd:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    35d2:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    35d7:	44 89 fa             	mov    %r15d,%edx
    35da:	48 8d 35 44 4e 00 00 	lea    0x4e44(%rip),%rsi        # 8425 <_IO_stdin_used+0x425>
    35e1:	31 c0                	xor    %eax,%eax
    35e3:	31 ed                	xor    %ebp,%ebp
    35e5:	bf 01 00 00 00       	mov    $0x1,%edi
    35ea:	47 8d 2c 3f          	lea    (%r15,%r15,1),%r13d
    35ee:	e8 bd ee ff ff       	call   24b0 <__printf_chk@plt>
    35f3:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    35f8:	44 89 7c 24 18       	mov    %r15d,0x18(%rsp)
    35fd:	48 89 d8             	mov    %rbx,%rax
    3600:	89 eb                	mov    %ebp,%ebx
    3602:	48 89 c5             	mov    %rax,%rbp
    3605:	42 8d 0c 2b          	lea    (%rbx,%r13,1),%ecx
    3609:	89 da                	mov    %ebx,%edx
    360b:	48 8d 35 1d 4e 00 00 	lea    0x4e1d(%rip),%rsi        # 842f <_IO_stdin_used+0x42f>
    3612:	31 c0                	xor    %eax,%eax
    3614:	bf 01 00 00 00       	mov    $0x1,%edi
    3619:	45 31 ff             	xor    %r15d,%r15d
    361c:	e8 8f ee ff ff       	call   24b0 <__printf_chk@plt>
    3621:	89 5c 24 20          	mov    %ebx,0x20(%rsp)
    3625:	4c 89 f9             	mov    %r15,%rcx
    3628:	45 89 ef             	mov    %r13d,%r15d
    362b:	44 89 74 24 28       	mov    %r14d,0x28(%rsp)
    3630:	89 ca                	mov    %ecx,%edx
    3632:	48 8d 35 08 4e 00 00 	lea    0x4e08(%rip),%rsi        # 8441 <_IO_stdin_used+0x441>
    3639:	bf 01 00 00 00       	mov    $0x1,%edi
    363e:	31 c0                	xor    %eax,%eax
    3640:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    3645:	45 31 ed             	xor    %r13d,%r13d
    3648:	e8 63 ee ff ff       	call   24b0 <__printf_chk@plt>
    364d:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    3652:	48 c1 e3 09          	shl    $0x9,%rbx
    3656:	eb 34                	jmp    368c <main+0x101c>
    3658:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3660:	83 fe 01             	cmp    $0x1,%esi
    3663:	0f 84 a5 00 00 00    	je     370e <main+0x109e>
    3669:	44 89 f2             	mov    %r14d,%edx
    366c:	4c 89 e6             	mov    %r12,%rsi
    366f:	bf 01 00 00 00       	mov    $0x1,%edi
    3674:	49 83 c5 01          	add    $0x1,%r13
    3678:	44 8b 80 b4 00 00 00 	mov    0xb4(%rax),%r8d
    367f:	31 c0                	xor    %eax,%eax
    3681:	e8 2a ee ff ff       	call   24b0 <__printf_chk@plt>
    3686:	49 83 fd 06          	cmp    $0x6,%r13
    368a:	74 50                	je     36dc <main+0x106c>
    368c:	be 01 00 00 00       	mov    $0x1,%esi
    3691:	bf 64 00 00 00       	mov    $0x64,%edi
    3696:	45 89 ee             	mov    %r13d,%r14d
    3699:	e8 62 ed ff ff       	call   2400 <calloc@plt>
    369e:	4c 8b 45 38          	mov    0x38(%rbp),%r8
    36a2:	4c 89 ef             	mov    %r13,%rdi
    36a5:	48 89 c1             	mov    %rax,%rcx
    36a8:	48 c1 e7 08          	shl    $0x8,%rdi
    36ac:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    36b4:	48 01 f8             	add    %rdi,%rax
    36b7:	8b b0 b0 00 00 00    	mov    0xb0(%rax),%esi
    36bd:	83 fe 02             	cmp    $0x2,%esi
    36c0:	75 9e                	jne    3660 <main+0xff0>
    36c2:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    36cc:	48 89 01             	mov    %rax,(%rcx)
    36cf:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    36d7:	48 01 f8             	add    %rdi,%rax
    36da:	eb 8d                	jmp    3669 <main+0xff9>
    36dc:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    36e1:	48 83 c1 01          	add    $0x1,%rcx
    36e5:	48 83 f9 03          	cmp    $0x3,%rcx
    36e9:	0f 85 41 ff ff ff    	jne    3630 <main+0xfc0>
    36ef:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    36f3:	44 8b 74 24 28       	mov    0x28(%rsp),%r14d
    36f8:	45 89 fd             	mov    %r15d,%r13d
    36fb:	48 81 c5 d8 00 00 00 	add    $0xd8,%rbp
    3702:	85 db                	test   %ebx,%ebx
    3704:	75 25                	jne    372b <main+0x10bb>
    3706:	44 89 f3             	mov    %r14d,%ebx
    3709:	e9 f7 fe ff ff       	jmp    3605 <main+0xf95>
    370e:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3714:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    371b:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3723:	48 01 f8             	add    %rdi,%rax
    3726:	e9 3e ff ff ff       	jmp    3669 <main+0xff9>
    372b:	48 81 44 24 10 b0 01 00 00 	addq   $0x1b0,0x10(%rsp)
    3734:	44 8b 7c 24 18       	mov    0x18(%rsp),%r15d
    3739:	41 83 c7 01          	add    $0x1,%r15d
    373d:	41 83 ff 03          	cmp    $0x3,%r15d
    3741:	0f 85 90 fe ff ff    	jne    35d7 <main+0xf67>
    3747:	ba 07 00 00 00       	mov    $0x7,%edx
    374c:	bf 01 00 00 00       	mov    $0x1,%edi
    3751:	31 c0                	xor    %eax,%eax
    3753:	41 89 df             	mov    %ebx,%r15d
    3756:	48 8d 35 0a 4d 00 00 	lea    0x4d0a(%rip),%rsi        # 8467 <_IO_stdin_used+0x467>
    375d:	e8 4e ed ff ff       	call   24b0 <__printf_chk@plt>
    3762:	be 08 00 00 00       	mov    $0x8,%esi
    3767:	bf 02 00 00 00       	mov    $0x2,%edi
    376c:	e8 8f ec ff ff       	call   2400 <calloc@plt>
    3771:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3776:	be 38 00 00 00       	mov    $0x38,%esi
    377b:	4c 8d af e8 05 00 00 	lea    0x5e8(%rdi),%r13
    3782:	48 89 78 08          	mov    %rdi,0x8(%rax)
    3786:	4c 8d a7 d8 00 00 00 	lea    0xd8(%rdi),%r12
    378d:	48 89 87 00 06 00 00 	mov    %rax,0x600(%rdi)
    3794:	4c 89 28             	mov    %r13,(%rax)
    3797:	48 8b 47 38          	mov    0x38(%rdi),%rax
    379b:	c7 87 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%rdi)
    37a5:	c7 87 ec 05 00 00 00 00 00 00 	movl   $0x0,0x5ec(%rdi)
    37af:	c7 87 28 06 00 00 03 00 00 00 	movl   $0x3,0x628(%rdi)
    37b9:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    37c3:	48 8b 87 10 01 00 00 	mov    0x110(%rdi),%rax
    37ca:	bf 0a 00 00 00       	mov    $0xa,%edi
    37cf:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    37d9:	e8 22 ec ff ff       	call   2400 <calloc@plt>
    37de:	be 38 00 00 00       	mov    $0x38,%esi
    37e3:	bf 0a 00 00 00       	mov    $0xa,%edi
    37e8:	49 89 c6             	mov    %rax,%r14
    37eb:	e8 10 ec ff ff       	call   2400 <calloc@plt>
    37f0:	be 38 00 00 00       	mov    $0x38,%esi
    37f5:	bf 0a 00 00 00       	mov    $0xa,%edi
    37fa:	48 89 c5             	mov    %rax,%rbp
    37fd:	e8 fe eb ff ff       	call   2400 <calloc@plt>
    3802:	be 38 00 00 00       	mov    $0x38,%esi
    3807:	bf 0a 00 00 00       	mov    $0xa,%edi
    380c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3811:	e8 ea eb ff ff       	call   2400 <calloc@plt>
    3816:	be 08 00 00 00       	mov    $0x8,%esi
    381b:	bf 0a 00 00 00       	mov    $0xa,%edi
    3820:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    3825:	e8 d6 eb ff ff       	call   2400 <calloc@plt>
    382a:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    382f:	be 08 00 00 00       	mov    $0x8,%esi
    3834:	48 89 c3             	mov    %rax,%rbx
    3837:	48 8b 05 ba 54 00 00 	mov    0x54ba(%rip),%rax        # 8cf8 <_IO_stdin_used+0xcf8>
    383e:	c7 87 1c 05 00 00 00 00 00 00 	movl   $0x0,0x51c(%rdi)
    3848:	48 89 87 50 05 00 00 	mov    %rax,0x550(%rdi)
    384f:	bf 0a 00 00 00       	mov    $0xa,%edi
    3854:	e8 a7 eb ff ff       	call   2400 <calloc@plt>
    3859:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    385e:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3862:	48 8d 97 b0 01 00 00 	lea    0x1b0(%rdi),%rdx
    3869:	48 8d 8f 10 05 00 00 	lea    0x510(%rdi),%rcx
    3870:	48 89 38             	mov    %rdi,(%rax)
    3873:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3877:	48 8d 97 88 02 00 00 	lea    0x288(%rdi),%rdx
    387e:	48 8d b7 c0 06 00 00 	lea    0x6c0(%rdi),%rsi
    3885:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3889:	48 8d 97 60 03 00 00 	lea    0x360(%rdi),%rdx
    3890:	48 89 50 20          	mov    %rdx,0x20(%rax)
    3894:	48 8d 97 38 04 00 00 	lea    0x438(%rdi),%rdx
    389b:	48 89 50 28          	mov    %rdx,0x28(%rax)
    389f:	48 8d 97 98 07 00 00 	lea    0x798(%rdi),%rdx
    38a6:	48 89 48 30          	mov    %rcx,0x30(%rax)
    38aa:	48 89 70 40          	mov    %rsi,0x40(%rax)
    38ae:	48 89 50 48          	mov    %rdx,0x48(%rax)
    38b2:	ba 06 00 00 00       	mov    $0x6,%edx
    38b7:	48 89 87 28 05 00 00 	mov    %rax,0x528(%rdi)
    38be:	4c 89 68 38          	mov    %r13,0x38(%rax)
    38c2:	48 8b 05 37 54 00 00 	mov    0x5437(%rip),%rax        # 8d00 <_IO_stdin_used+0xd00>
    38c9:	c7 87 40 05 00 00 06 00 00 00 	movl   $0x6,0x540(%rdi)
    38d3:	48 89 87 38 05 00 00 	mov    %rax,0x538(%rdi)
    38da:	31 c0                	xor    %eax,%eax
    38dc:	c7 87 14 05 00 00 00 00 00 00 	movl   $0x0,0x514(%rdi)
    38e6:	bf 01 00 00 00       	mov    $0x1,%edi
    38eb:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    38f0:	48 8d 35 7f 4b 00 00 	lea    0x4b7f(%rip),%rsi        # 8476 <_IO_stdin_used+0x476>
    38f7:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    38fc:	e8 af eb ff ff       	call   24b0 <__printf_chk@plt>
    3901:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    3906:	48 8d 15 a3 0d 00 00 	lea    0xda3(%rip),%rdx        # 46b0 <timer_thread>
    390d:	48 8d b5 50 01 00 00 	lea    0x150(%rbp),%rsi
    3914:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    3918:	e8 b3 eb ff ff       	call   24d0 <pthread_create@plt>
    391d:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    3922:	4c 89 f0             	mov    %r14,%rax
    3925:	48 89 d9             	mov    %rbx,%rcx
    3928:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    392d:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    3933:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3938:	45 31 f6             	xor    %r14d,%r14d
    393b:	4c 89 64 24 40       	mov    %r12,0x40(%rsp)
    3940:	44 89 7c 24 20       	mov    %r15d,0x20(%rsp)
    3945:	45 89 d7             	mov    %r10d,%r15d
    3948:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    394d:	47 8d 24 36          	lea    (%r14,%r14,1),%r12d
    3951:	49 89 c5             	mov    %rax,%r13
    3954:	48 89 cb             	mov    %rcx,%rbx
    3957:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    395c:	48 89 d5             	mov    %rdx,%rbp
    395f:	48 89 54 24 58       	mov    %rdx,0x58(%rsp)
    3964:	c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%rbp)
    396b:	44 89 e2             	mov    %r12d,%edx
    396e:	44 89 f1             	mov    %r14d,%ecx
    3971:	31 c0                	xor    %eax,%eax
    3973:	c7 45 44 01 00 00 00 	movl   $0x1,0x44(%rbp)
    397a:	48 8d 35 77 4e 00 00 	lea    0x4e77(%rip),%rsi        # 87f8 <_IO_stdin_used+0x7f8>
    3981:	bf 01 00 00 00       	mov    $0x1,%edi
    3986:	41 83 c4 01          	add    $0x1,%r12d
    398a:	e8 21 eb ff ff       	call   24b0 <__printf_chk@plt>
    398f:	48 89 e9             	mov    %rbp,%rcx
    3992:	4c 89 ee             	mov    %r13,%rsi
    3995:	48 89 df             	mov    %rbx,%rdi
    3998:	48 8d 15 91 28 00 00 	lea    0x2891(%rip),%rdx        # 6230 <barriered_thread>
    399f:	48 81 c5 d8 00 00 00 	add    $0xd8,%rbp
    39a6:	48 83 c3 08          	add    $0x8,%rbx
    39aa:	49 83 c5 38          	add    $0x38,%r13
    39ae:	e8 1d eb ff ff       	call   24d0 <pthread_create@plt>
    39b3:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
    39b7:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    39bb:	be 08 00 00 00       	mov    $0x8,%esi
    39c0:	e8 5b e9 ff ff       	call   2320 <pthread_setaffinity_np@plt>
    39c5:	45 39 e7             	cmp    %r12d,%r15d
    39c8:	75 9a                	jne    3964 <main+0x12f4>
    39ca:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    39cf:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    39d4:	41 83 c6 01          	add    $0x1,%r14d
    39d8:	41 83 c7 02          	add    $0x2,%r15d
    39dc:	48 8b 54 24 58       	mov    0x58(%rsp),%rdx
    39e1:	48 83 c1 10          	add    $0x10,%rcx
    39e5:	48 83 c0 70          	add    $0x70,%rax
    39e9:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    39f0:	41 83 fe 03          	cmp    $0x3,%r14d
    39f4:	0f 85 4e ff ff ff    	jne    3948 <main+0x12d8>
    39fa:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    39ff:	be d8 00 00 00       	mov    $0xd8,%esi
    3a04:	bf 01 00 00 00       	mov    $0x1,%edi
    3a09:	48 8b 05 f8 52 00 00 	mov    0x52f8(%rip),%rax        # 8d08 <_IO_stdin_used+0xd08>
    3a10:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    3a15:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    3a1a:	41 c7 86 f4 05 00 00 02 00 00 00 	movl   $0x2,0x5f4(%r14)
    3a25:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    3a2a:	49 89 86 28 06 00 00 	mov    %rax,0x628(%r14)
    3a31:	44 8b 7c 24 20       	mov    0x20(%rsp),%r15d
    3a36:	48 8d 6b 40          	lea    0x40(%rbx),%rbp
    3a3a:	e8 c1 e9 ff ff       	call   2400 <calloc@plt>
    3a3f:	be 00 08 00 00       	mov    $0x800,%esi
    3a44:	31 ff                	xor    %edi,%edi
    3a46:	49 89 86 40 06 00 00 	mov    %rax,0x640(%r14)
    3a4d:	e8 ce ea ff ff       	call   2520 <eventfd@plt>
    3a52:	be 08 00 00 00       	mov    $0x8,%esi
    3a57:	bf 02 00 00 00       	mov    $0x2,%edi
    3a5c:	41 89 86 48 06 00 00 	mov    %eax,0x648(%r14)
    3a63:	e8 98 e9 ff ff       	call   2400 <calloc@plt>
    3a68:	ba 07 00 00 00       	mov    $0x7,%edx
    3a6d:	bf 01 00 00 00       	mov    $0x1,%edi
    3a72:	41 c7 86 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%r14)
    3a7d:	4c 89 30             	mov    %r14,(%rax)
    3a80:	48 8d 35 0d 4a 00 00 	lea    0x4a0d(%rip),%rsi        # 8494 <_IO_stdin_used+0x494>
    3a87:	49 89 86 00 06 00 00 	mov    %rax,0x600(%r14)
    3a8e:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3a92:	31 c0                	xor    %eax,%eax
    3a94:	41 c7 86 ec 05 00 00 07 00 00 00 	movl   $0x7,0x5ec(%r14)
    3a9f:	41 be 08 00 00 00    	mov    $0x8,%r14d
    3aa5:	e8 06 ea ff ff       	call   24b0 <__printf_chk@plt>
    3aaa:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3aaf:	4c 89 e9             	mov    %r13,%rcx
    3ab2:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3ab6:	48 8d 15 83 1f 00 00 	lea    0x1f83(%rip),%rdx        # 5a40 <io_thread>
    3abd:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3ac4:	e8 07 ea ff ff       	call   24d0 <pthread_create@plt>
    3ac9:	ba 08 00 00 00       	mov    $0x8,%edx
    3ace:	48 8d 35 d6 49 00 00 	lea    0x49d6(%rip),%rsi        # 84ab <_IO_stdin_used+0x4ab>
    3ad5:	31 c0                	xor    %eax,%eax
    3ad7:	bf 01 00 00 00       	mov    $0x1,%edi
    3adc:	e8 cf e9 ff ff       	call   24b0 <__printf_chk@plt>
    3ae1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3ae6:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    3aeb:	48 05 c0 01 00 00    	add    $0x1c0,%rax
    3af1:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3af6:	44 89 f2             	mov    %r14d,%edx
    3af9:	48 8d 35 c1 49 00 00 	lea    0x49c1(%rip),%rsi        # 84c1 <_IO_stdin_used+0x4c1>
    3b00:	bf 01 00 00 00       	mov    $0x1,%edi
    3b05:	31 c0                	xor    %eax,%eax
    3b07:	e8 a4 e9 ff ff       	call   24b0 <__printf_chk@plt>
    3b0c:	be 08 00 00 00       	mov    $0x8,%esi
    3b11:	bf 01 00 00 00       	mov    $0x1,%edi
    3b16:	48 8b 05 eb 51 00 00 	mov    0x51eb(%rip),%rax        # 8d08 <_IO_stdin_used+0xd08>
    3b1d:	41 c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%r13)
    3b25:	49 89 45 40          	mov    %rax,0x40(%r13)
    3b29:	e8 d2 e8 ff ff       	call   2400 <calloc@plt>
    3b2e:	48 8b bc 24 c0 00 00 00 	mov    0xc0(%rsp),%rdi
    3b36:	be 08 00 00 00       	mov    $0x8,%esi
    3b3b:	41 c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r13)
    3b46:	49 89 45 50          	mov    %rax,0x50(%r13)
    3b4a:	48 89 38             	mov    %rdi,(%rax)
    3b4d:	bf 02 00 00 00       	mov    $0x2,%edi
    3b52:	e8 a9 e8 ff ff       	call   2400 <calloc@plt>
    3b57:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    3b5c:	4c 89 e9             	mov    %r13,%rcx
    3b5f:	48 89 ef             	mov    %rbp,%rdi
    3b62:	49 89 45 18          	mov    %rax,0x18(%r13)
    3b66:	48 8d 15 33 0a 00 00 	lea    0xa33(%rip),%rdx        # 45a0 <external_thread>
    3b6d:	48 83 c5 08          	add    $0x8,%rbp
    3b71:	49 81 c5 d8 00 00 00 	add    $0xd8,%r13
    3b78:	48 89 30             	mov    %rsi,(%rax)
    3b7b:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3b80:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3b84:	48 8b 05 5d 51 00 00 	mov    0x515d(%rip),%rax        # 8ce8 <_IO_stdin_used+0xce8>
    3b8b:	45 89 b5 2c ff ff ff 	mov    %r14d,-0xd4(%r13)
    3b92:	49 89 85 50 ff ff ff 	mov    %rax,-0xb0(%r13)
    3b99:	e8 32 e9 ff ff       	call   24d0 <pthread_create@plt>
    3b9e:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3ba4:	48 83 84 24 c0 00 00 00 10 	addq   $0x10,0xc0(%rsp)
    3bad:	41 83 fe 08          	cmp    $0x8,%r14d
    3bb1:	75 42                	jne    3bf5 <main+0x1585>
    3bb3:	41 be 09 00 00 00    	mov    $0x9,%r14d
    3bb9:	e9 38 ff ff ff       	jmp    3af6 <main+0x1486>
    3bbe:	44 8b 6c 24 20       	mov    0x20(%rsp),%r13d
    3bc3:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3bc8:	48 89 5c 24 48       	mov    %rbx,0x48(%rsp)
    3bcd:	45 31 c0             	xor    %r8d,%r8d
    3bd0:	4b 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%rax
    3bd5:	45 89 ee             	mov    %r13d,%r14d
    3bd8:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3bdc:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
    3be0:	4c 89 c8             	mov    %r9,%rax
    3be3:	e9 aa ee ff ff       	jmp    2a92 <main+0x422>
    3be8:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
    3bf0:	e9 2f ef ff ff       	jmp    2b24 <main+0x4b4>
    3bf5:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3bfa:	48 8d 2d dd 48 00 00 	lea    0x48dd(%rip),%rbp        # 84de <_IO_stdin_used+0x4de>
    3c01:	4c 8d 68 04          	lea    0x4(%rax),%r13
    3c05:	4c 8d a0 74 08 00 00 	lea    0x874(%rax),%r12
    3c0c:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    3c10:	41 8b 55 00          	mov    0x0(%r13),%edx
    3c14:	48 89 ee             	mov    %rbp,%rsi
    3c17:	bf 01 00 00 00       	mov    $0x1,%edi
    3c1c:	31 c0                	xor    %eax,%eax
    3c1e:	49 81 c5 d8 00 00 00 	add    $0xd8,%r13
    3c25:	e8 86 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c2a:	4d 39 ec             	cmp    %r13,%r12
    3c2d:	75 dd                	jne    3c0c <main+0x159c>
    3c2f:	48 8d 3d bb 48 00 00 	lea    0x48bb(%rip),%rdi        # 84f1 <_IO_stdin_used+0x4f1>
    3c36:	45 31 ed             	xor    %r13d,%r13d
    3c39:	4c 8d a4 24 f0 00 00 00 	lea    0xf0(%rsp),%r12
    3c41:	e8 ea e6 ff ff       	call   2330 <puts@plt>
    3c46:	48 8d 2d c2 48 00 00 	lea    0x48c2(%rip),%rbp        # 850f <_IO_stdin_used+0x50f>
    3c4d:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    3c51:	4c 89 e6             	mov    %r12,%rsi
    3c54:	e8 07 e9 ff ff       	call   2560 <pthread_join@plt>
    3c59:	44 89 ea             	mov    %r13d,%edx
    3c5c:	48 89 ee             	mov    %rbp,%rsi
    3c5f:	bf 01 00 00 00       	mov    $0x1,%edi
    3c64:	31 c0                	xor    %eax,%eax
    3c66:	49 83 c5 01          	add    $0x1,%r13
    3c6a:	e8 41 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c6f:	49 83 fd 0a          	cmp    $0xa,%r13
    3c73:	75 d8                	jne    3c4d <main+0x15dd>
    3c75:	be 08 00 00 00       	mov    $0x8,%esi
    3c7a:	bf 00 04 00 00       	mov    $0x400,%edi
    3c7f:	31 db                	xor    %ebx,%ebx
    3c81:	e8 7a e7 ff ff       	call   2400 <calloc@plt>
    3c86:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3c8b:	48 89 c5             	mov    %rax,%rbp
    3c8e:	31 c0                	xor    %eax,%eax
    3c90:	49 89 d1             	mov    %rdx,%r9
    3c93:	45 31 db             	xor    %r11d,%r11d
    3c96:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3c9a:	45 85 d2             	test   %r10d,%r10d
    3c9d:	0f 8e ad 00 00 00    	jle    3d50 <main+0x16e0>
    3ca3:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3ca7:	4d 63 c2             	movslq %r10d,%r8
    3caa:	48 63 cb             	movslq %ebx,%rcx
    3cad:	49 c1 e0 09          	shl    $0x9,%r8
    3cb1:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    3cb6:	49 01 f8             	add    %rdi,%r8
    3cb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3cc0:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
    3cc7:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3cce:	48 83 c6 60          	add    $0x60,%rsi
    3cd2:	f3 0f 7e a1 00 01 00 00 	movq   0x100(%rcx),%xmm4
    3cda:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3cde:	f3 0f 7e 99 00 02 00 00 	movq   0x200(%rcx),%xmm3
    3ce6:	f3 0f 7e 91 00 03 00 00 	movq   0x300(%rcx),%xmm2
    3cee:	f3 0f 7e 89 00 04 00 00 	movq   0x400(%rcx),%xmm1
    3cf6:	0f 16 a1 80 01 00 00 	movhps 0x180(%rcx),%xmm4
    3cfd:	f3 0f 7e 81 00 05 00 00 	movq   0x500(%rcx),%xmm0
    3d05:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    3d0c:	0f 16 99 80 02 00 00 	movhps 0x280(%rcx),%xmm3
    3d13:	0f 16 91 80 03 00 00 	movhps 0x380(%rcx),%xmm2
    3d1a:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3d1e:	0f 16 89 80 04 00 00 	movhps 0x480(%rcx),%xmm1
    3d25:	0f 16 81 80 05 00 00 	movhps 0x580(%rcx),%xmm0
    3d2c:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3d30:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3d34:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3d38:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3d3c:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
    3d40:	4c 39 c7             	cmp    %r8,%rdi
    3d43:	0f 85 77 ff ff ff    	jne    3cc0 <main+0x1650>
    3d49:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3d4d:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    3d50:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    3d57:	45 85 db             	test   %r11d,%r11d
    3d5a:	75 08                	jne    3d64 <main+0x16f4>
    3d5c:	45 89 fb             	mov    %r15d,%r11d
    3d5f:	e9 32 ff ff ff       	jmp    3c96 <main+0x1626>
    3d64:	83 c0 02             	add    $0x2,%eax
    3d67:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    3d6e:	83 f8 06             	cmp    $0x6,%eax
    3d71:	0f 85 19 ff ff ff    	jne    3c90 <main+0x1620>
    3d77:	48 8d 3d a5 47 00 00 	lea    0x47a5(%rip),%rdi        # 8523 <_IO_stdin_used+0x523>
    3d7e:	e8 ad e5 ff ff       	call   2330 <puts@plt>
    3d83:	48 8d 35 75 46 00 00 	lea    0x4675(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3d8a:	48 8d 3d aa 47 00 00 	lea    0x47aa(%rip),%rdi        # 853b <_IO_stdin_used+0x53b>
    3d91:	e8 5a e7 ff ff       	call   24f0 <fopen@plt>
    3d96:	49 89 c6             	mov    %rax,%r14
    3d99:	85 db                	test   %ebx,%ebx
    3d9b:	7e 73                	jle    3e10 <main+0x17a0>
    3d9d:	48 63 db             	movslq %ebx,%rbx
    3da0:	49 89 ef             	mov    %rbp,%r15
    3da3:	4c 8d 2d 34 46 00 00 	lea    0x4634(%rip),%r13        # 83de <_IO_stdin_used+0x3de>
    3daa:	48 8d 6c dd 00       	lea    0x0(%rbp,%rbx,8),%rbp
    3daf:	4c 8d 25 6c 46 00 00 	lea    0x466c(%rip),%r12        # 8422 <_IO_stdin_used+0x422>
    3db6:	be 01 00 00 00       	mov    $0x1,%esi
    3dbb:	bf fa 00 00 00       	mov    $0xfa,%edi
    3dc0:	49 83 c7 08          	add    $0x8,%r15
    3dc4:	e8 37 e6 ff ff       	call   2400 <calloc@plt>
    3dc9:	4c 89 e9             	mov    %r13,%rcx
    3dcc:	ba fa 00 00 00       	mov    $0xfa,%edx
    3dd1:	be 01 00 00 00       	mov    $0x1,%esi
    3dd6:	48 89 c3             	mov    %rax,%rbx
    3dd9:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3ddd:	48 89 df             	mov    %rbx,%rdi
    3de0:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3de7:	31 c0                	xor    %eax,%eax
    3de9:	e8 b2 e7 ff ff       	call   25a0 <__sprintf_chk@plt>
    3dee:	48 89 da             	mov    %rbx,%rdx
    3df1:	4c 89 e6             	mov    %r12,%rsi
    3df4:	bf 01 00 00 00       	mov    $0x1,%edi
    3df9:	31 c0                	xor    %eax,%eax
    3dfb:	e8 b0 e6 ff ff       	call   24b0 <__printf_chk@plt>
    3e00:	4c 89 f6             	mov    %r14,%rsi
    3e03:	48 89 df             	mov    %rbx,%rdi
    3e06:	e8 b5 e5 ff ff       	call   23c0 <fputs@plt>
    3e0b:	49 39 ef             	cmp    %rbp,%r15
    3e0e:	75 a6                	jne    3db6 <main+0x1746>
    3e10:	4c 89 f7             	mov    %r14,%rdi
    3e13:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
    3e19:	31 db                	xor    %ebx,%ebx
    3e1b:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
    3e25:	e8 36 e5 ff ff       	call   2360 <fclose@plt>
    3e2a:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
    3e33:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    3e3c:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    3e45:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
    3e4e:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
    3e56:	45 8d 44 24 02       	lea    0x2(%r12),%r8d
    3e5b:	4c 8b b4 24 a8 00 00 00 	mov    0xa8(%rsp),%r14
    3e63:	45 89 e5             	mov    %r12d,%r13d
    3e66:	44 89 44 24 48       	mov    %r8d,0x48(%rsp)
    3e6b:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    3e70:	44 89 e8             	mov    %r13d,%eax
    3e73:	41 83 c5 01          	add    $0x1,%r13d
    3e77:	bf 0a 00 00 00       	mov    $0xa,%edi
    3e7c:	41 f6 c5 01          	test   $0x1,%r13b
    3e80:	8d 50 02             	lea    0x2(%rax),%edx
    3e83:	0f 44 c2             	cmove  %edx,%eax
    3e86:	4c 63 e0             	movslq %eax,%r12
    3e89:	e8 82 e4 ff ff       	call   2310 <putchar@plt>
    3e8e:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3e93:	bf 01 00 00 00       	mov    $0x1,%edi
    3e98:	48 8d 35 a5 46 00 00 	lea    0x46a5(%rip),%rsi        # 8544 <_IO_stdin_used+0x544>
    3e9f:	48 8b 10             	mov    (%rax),%rdx
    3ea2:	31 c0                	xor    %eax,%eax
    3ea4:	e8 07 e6 ff ff       	call   24b0 <__printf_chk@plt>
    3ea9:	41 8b 56 40          	mov    0x40(%r14),%edx
    3ead:	85 d2                	test   %edx,%edx
    3eaf:	0f 8e 30 05 00 00    	jle    43e5 <main+0x1d75>
    3eb5:	48 63 ca             	movslq %edx,%rcx
    3eb8:	49 8b 46 38          	mov    0x38(%r14),%rax
    3ebc:	31 d2                	xor    %edx,%edx
    3ebe:	48 c1 e1 09          	shl    $0x9,%rcx
    3ec2:	48 01 c1             	add    %rax,%rcx
    3ec5:	0f 1f 00             	nopl   (%rax)
    3ec8:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    3ecf:	48 05 00 02 00 00    	add    $0x200,%rax
    3ed5:	48 39 c8             	cmp    %rcx,%rax
    3ed8:	75 ee                	jne    3ec8 <main+0x1858>
    3eda:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3edf:	4b 8d 04 64          	lea    (%r12,%r12,2),%rax
    3ee3:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3ee7:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3eeb:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3eef:	85 c9                	test   %ecx,%ecx
    3ef1:	7e 1f                	jle    3f12 <main+0x18a2>
    3ef3:	48 8b 40 38          	mov    0x38(%rax),%rax
    3ef7:	48 c1 e1 09          	shl    $0x9,%rcx
    3efb:	48 01 c1             	add    %rax,%rcx
    3efe:	66 90                	xchg   %ax,%ax
    3f00:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    3f07:	48 05 00 02 00 00    	add    $0x200,%rax
    3f0d:	48 39 c8             	cmp    %rcx,%rax
    3f10:	75 ee                	jne    3f00 <main+0x1890>
    3f12:	48 8d 35 40 46 00 00 	lea    0x4640(%rip),%rsi        # 8559 <_IO_stdin_used+0x559>
    3f19:	bf 01 00 00 00       	mov    $0x1,%edi
    3f1e:	31 c0                	xor    %eax,%eax
    3f20:	e8 8b e5 ff ff       	call   24b0 <__printf_chk@plt>
    3f25:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3f2a:	bf 01 00 00 00       	mov    $0x1,%edi
    3f2f:	48 8d 35 f2 48 00 00 	lea    0x48f2(%rip),%rsi        # 8828 <_IO_stdin_used+0x828>
    3f36:	48 8b 08             	mov    (%rax),%rcx
    3f39:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3f43:	48 f7 e9             	imul   %rcx
    3f46:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3f4a:	31 c0                	xor    %eax,%eax
    3f4c:	48 d1 fa             	sar    %rdx
    3f4f:	48 29 ca             	sub    %rcx,%rdx
    3f52:	e8 59 e5 ff ff       	call   24b0 <__printf_chk@plt>
    3f57:	bf 0a 00 00 00       	mov    $0xa,%edi
    3f5c:	e8 af e3 ff ff       	call   2310 <putchar@plt>
    3f61:	45 8b 66 40          	mov    0x40(%r14),%r12d
    3f65:	45 85 e4             	test   %r12d,%r12d
    3f68:	0f 8e 47 01 00 00    	jle    40b5 <main+0x1a45>
    3f6e:	44 89 6c 24 08       	mov    %r13d,0x8(%rsp)
    3f73:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    3f78:	31 d2                	xor    %edx,%edx
    3f7a:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3f7f:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3f84:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    3f89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3f90:	49 8b 46 38          	mov    0x38(%r14),%rax
    3f94:	49 89 d1             	mov    %rdx,%r9
    3f97:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
    3f9c:	41 89 d5             	mov    %edx,%r13d
    3f9f:	49 c1 e1 09          	shl    $0x9,%r9
    3fa3:	45 31 e4             	xor    %r12d,%r12d
    3fa6:	4c 01 c8             	add    %r9,%rax
    3fa9:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    3fae:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
    3fb5:	48 03 b0 68 01 00 00 	add    0x168(%rax),%rsi
    3fbc:	48 03 b8 80 01 00 00 	add    0x180(%rax),%rdi
    3fc3:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    3fc8:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    3fcd:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    3fd2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3fd8:	8b 54 24 08          	mov    0x8(%rsp),%edx
    3fdc:	45 89 e0             	mov    %r12d,%r8d
    3fdf:	44 89 e9             	mov    %r13d,%ecx
    3fe2:	bf 01 00 00 00       	mov    $0x1,%edi
    3fe7:	48 8d 35 78 45 00 00 	lea    0x4578(%rip),%rsi        # 8566 <_IO_stdin_used+0x566>
    3fee:	31 c0                	xor    %eax,%eax
    3ff0:	e8 bb e4 ff ff       	call   24b0 <__printf_chk@plt>
    3ff5:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    3ffa:	4c 89 e0             	mov    %r12,%rax
    3ffd:	45 89 e0             	mov    %r12d,%r8d
    4000:	49 8b 56 38          	mov    0x38(%r14),%rdx
    4004:	48 c1 e0 08          	shl    $0x8,%rax
    4008:	48 83 ec 08          	sub    $0x8,%rsp
    400c:	49 83 c4 01          	add    $0x1,%r12
    4010:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    4018:	48 8b 38             	mov    (%rax),%rdi
    401b:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    4022:	48 8b 87 00 04 00 00 	mov    0x400(%rdi),%rax
    4029:	48 8b 96 80 03 00 00 	mov    0x380(%rsi),%rdx
    4030:	48 8b b6 00 04 00 00 	mov    0x400(%rsi),%rsi
    4037:	48 8b 8f 80 03 00 00 	mov    0x380(%rdi),%rcx
    403e:	bf 01 00 00 00       	mov    $0x1,%edi
    4043:	48 01 c3             	add    %rax,%rbx
    4046:	48 01 f0             	add    %rsi,%rax
    4049:	49 01 cf             	add    %rcx,%r15
    404c:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
    4050:	48 01 f3             	add    %rsi,%rbx
    4053:	50                   	push   %rax
    4054:	49 01 d7             	add    %rdx,%r15
    4057:	8b 54 24 18          	mov    0x18(%rsp),%edx
    405b:	44 89 e9             	mov    %r13d,%ecx
    405e:	48 8d 35 e3 47 00 00 	lea    0x47e3(%rip),%rsi        # 8848 <_IO_stdin_used+0x848>
    4065:	31 c0                	xor    %eax,%eax
    4067:	e8 44 e4 ff ff       	call   24b0 <__printf_chk@plt>
    406c:	41 5a                	pop    %r10
    406e:	41 5b                	pop    %r11
    4070:	49 83 fc 06          	cmp    $0x6,%r12
    4074:	0f 85 5e ff ff ff    	jne    3fd8 <main+0x1968>
    407a:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    407f:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    4084:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    4089:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    408e:	48 83 c2 01          	add    $0x1,%rdx
    4092:	41 39 56 40          	cmp    %edx,0x40(%r14)
    4096:	0f 8f f4 fe ff ff    	jg     3f90 <main+0x1920>
    409c:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
    40a1:	44 8b 6c 24 08       	mov    0x8(%rsp),%r13d
    40a6:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    40ab:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
    40b0:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    40b5:	45 31 ff             	xor    %r15d,%r15d
    40b8:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    40c0:	4c 8d 25 a1 47 00 00 	lea    0x47a1(%rip),%r12        # 8868 <_IO_stdin_used+0x868>
    40c7:	7e 5f                	jle    4128 <main+0x1ab8>
    40c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    40d0:	49 8b 86 90 00 00 00 	mov    0x90(%r14),%rax
    40d7:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    40db:	48 83 ec 08          	sub    $0x8,%rsp
    40df:	bf 01 00 00 00       	mov    $0x1,%edi
    40e4:	49 83 c7 01          	add    $0x1,%r15
    40e8:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    40ec:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    40f0:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    40f4:	48 89 f0             	mov    %rsi,%rax
    40f7:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    40fb:	4c 2b 01             	sub    (%rcx),%r8
    40fe:	48 f7 e5             	mul    %rbp
    4101:	8b 49 20             	mov    0x20(%rcx),%ecx
    4104:	56                   	push   %rsi
    4105:	31 c0                	xor    %eax,%eax
    4107:	4c 89 e6             	mov    %r12,%rsi
    410a:	48 c1 ea 12          	shr    $0x12,%rdx
    410e:	49 89 d1             	mov    %rdx,%r9
    4111:	ba 02 00 00 00       	mov    $0x2,%edx
    4116:	e8 95 e3 ff ff       	call   24b0 <__printf_chk@plt>
    411b:	41 58                	pop    %r8
    411d:	41 59                	pop    %r9
    411f:	4d 39 be a0 00 00 00 	cmp    %r15,0xa0(%r14)
    4126:	7f a8                	jg     40d0 <main+0x1a60>
    4128:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    412f:	85 d2                	test   %edx,%edx
    4131:	0f 8e 0a 01 00 00    	jle    4241 <main+0x1bd1>
    4137:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
    413c:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4140:	45 31 ff             	xor    %r15d,%r15d
    4143:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
    4148:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4150:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    4154:	44 89 fb             	mov    %r15d,%ebx
    4157:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    415f:	8b 30                	mov    (%rax),%esi
    4161:	85 f6                	test   %esi,%esi
    4163:	0f 8e c1 00 00 00    	jle    422a <main+0x1bba>
    4169:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    416e:	31 d2                	xor    %edx,%edx
    4170:	48 8b 48 08          	mov    0x8(%rax),%rcx
    4174:	49 89 f8             	mov    %rdi,%r8
    4177:	48 89 d7             	mov    %rdx,%rdi
    417a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4180:	49 89 fc             	mov    %rdi,%r12
    4183:	45 31 ff             	xor    %r15d,%r15d
    4186:	49 c1 e4 08          	shl    $0x8,%r12
    418a:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    418e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    4194:	85 d2                	test   %edx,%edx
    4196:	7e 77                	jle    420f <main+0x1b9f>
    4198:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    419d:	0f 1f 00             	nopl   (%rax)
    41a0:	4c 89 f9             	mov    %r15,%rcx
    41a3:	48 83 ec 08          	sub    $0x8,%rsp
    41a7:	bf 01 00 00 00       	mov    $0x1,%edi
    41ac:	49 83 c7 01          	add    $0x1,%r15
    41b0:	48 c1 e1 05          	shl    $0x5,%rcx
    41b4:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
    41bb:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    41bf:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    41c3:	48 89 f0             	mov    %rsi,%rax
    41c6:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    41ca:	4c 2b 01             	sub    (%rcx),%r8
    41cd:	56                   	push   %rsi
    41ce:	48 f7 e5             	mul    %rbp
    41d1:	89 d9                	mov    %ebx,%ecx
    41d3:	48 8d 35 de 46 00 00 	lea    0x46de(%rip),%rsi        # 88b8 <_IO_stdin_used+0x8b8>
    41da:	31 c0                	xor    %eax,%eax
    41dc:	48 c1 ea 12          	shr    $0x12,%rdx
    41e0:	49 89 d1             	mov    %rdx,%r9
    41e3:	ba 02 00 00 00       	mov    $0x2,%edx
    41e8:	e8 c3 e2 ff ff       	call   24b0 <__printf_chk@plt>
    41ed:	4d 8b 46 50          	mov    0x50(%r14),%r8
    41f1:	5e                   	pop    %rsi
    41f2:	5f                   	pop    %rdi
    41f3:	4b 8b 14 28          	mov    (%r8,%r13,1),%rdx
    41f7:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    41fb:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    41ff:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    4206:	7f 98                	jg     41a0 <main+0x1b30>
    4208:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    420d:	8b 32                	mov    (%rdx),%esi
    420f:	48 83 c7 01          	add    $0x1,%rdi
    4213:	39 fe                	cmp    %edi,%esi
    4215:	0f 8f 65 ff ff ff    	jg     4180 <main+0x1b10>
    421b:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    4220:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    4227:	4c 89 c7             	mov    %r8,%rdi
    422a:	49 83 c7 01          	add    $0x1,%r15
    422e:	44 39 fa             	cmp    %r15d,%edx
    4231:	0f 8f 19 ff ff ff    	jg     4150 <main+0x1ae0>
    4237:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    423c:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    4241:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    4247:	49 81 c6 d8 00 00 00 	add    $0xd8,%r14
    424e:	44 39 6c 24 48       	cmp    %r13d,0x48(%rsp)
    4253:	0f 85 17 fc ff ff    	jne    3e70 <main+0x1800>
    4259:	48 83 84 24 90 00 00 00 30 	addq   $0x30,0x90(%rsp)
    4262:	44 8b 44 24 48       	mov    0x48(%rsp),%r8d
    4267:	48 81 84 24 a8 00 00 00 b0 01 00 00 	addq   $0x1b0,0xa8(%rsp)
    4273:	41 83 f8 05          	cmp    $0x5,%r8d
    4277:	74 08                	je     4281 <main+0x1c11>
    4279:	45 89 c4             	mov    %r8d,%r12d
    427c:	e9 cd fb ff ff       	jmp    3e4e <main+0x17de>
    4281:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    4286:	bf 01 00 00 00       	mov    $0x1,%edi
    428b:	31 c0                	xor    %eax,%eax
    428d:	49 89 df             	mov    %rbx,%r15
    4290:	48 8d 35 df 42 00 00 	lea    0x42df(%rip),%rsi        # 8576 <_IO_stdin_used+0x576>
    4297:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    42a1:	4c 89 f2             	mov    %r14,%rdx
    42a4:	e8 07 e2 ff ff       	call   24b0 <__printf_chk@plt>
    42a9:	bf 0a 00 00 00       	mov    $0xa,%edi
    42ae:	e8 5d e0 ff ff       	call   2310 <putchar@plt>
    42b3:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
    42bb:	48 8d 35 4e 46 00 00 	lea    0x464e(%rip),%rsi        # 8910 <_IO_stdin_used+0x910>
    42c2:	31 c0                	xor    %eax,%eax
    42c4:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    42c8:	bf 01 00 00 00       	mov    $0x1,%edi
    42cd:	e8 de e1 ff ff       	call   24b0 <__printf_chk@plt>
    42d2:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    42d7:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    42dc:	48 8d 35 55 46 00 00 	lea    0x4655(%rip),%rsi        # 8938 <_IO_stdin_used+0x938>
    42e3:	48 f7 eb             	imul   %rbx
    42e6:	48 c1 ff 3f          	sar    $0x3f,%rdi
    42ea:	31 c0                	xor    %eax,%eax
    42ec:	48 d1 fa             	sar    %rdx
    42ef:	48 29 fa             	sub    %rdi,%rdx
    42f2:	bf 01 00 00 00       	mov    $0x1,%edi
    42f7:	e8 b4 e1 ff ff       	call   24b0 <__printf_chk@plt>
    42fc:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4301:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    4306:	48 8d 35 5b 46 00 00 	lea    0x465b(%rip),%rsi        # 8968 <_IO_stdin_used+0x968>
    430d:	48 f7 eb             	imul   %rbx
    4310:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4314:	31 c0                	xor    %eax,%eax
    4316:	48 d1 fa             	sar    %rdx
    4319:	48 29 fa             	sub    %rdi,%rdx
    431c:	bf 01 00 00 00       	mov    $0x1,%edi
    4321:	e8 8a e1 ff ff       	call   24b0 <__printf_chk@plt>
    4326:	4c 89 f0             	mov    %r14,%rax
    4329:	bf 01 00 00 00       	mov    $0x1,%edi
    432e:	48 8d 35 63 46 00 00 	lea    0x4663(%rip),%rsi        # 8998 <_IO_stdin_used+0x998>
    4335:	48 f7 eb             	imul   %rbx
    4338:	4c 89 f0             	mov    %r14,%rax
    433b:	48 c1 f8 3f          	sar    $0x3f,%rax
    433f:	48 d1 fa             	sar    %rdx
    4342:	48 29 c2             	sub    %rax,%rdx
    4345:	31 c0                	xor    %eax,%eax
    4347:	e8 64 e1 ff ff       	call   24b0 <__printf_chk@plt>
    434c:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4351:	bf 01 00 00 00       	mov    $0x1,%edi
    4356:	48 8d 35 2d 42 00 00 	lea    0x422d(%rip),%rsi        # 858a <_IO_stdin_used+0x58a>
    435d:	48 f7 eb             	imul   %rbx
    4360:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4365:	48 c1 f8 3f          	sar    $0x3f,%rax
    4369:	48 d1 fa             	sar    %rdx
    436c:	48 29 c2             	sub    %rax,%rdx
    436f:	31 c0                	xor    %eax,%eax
    4371:	48 89 d5             	mov    %rdx,%rbp
    4374:	e8 37 e1 ff ff       	call   24b0 <__printf_chk@plt>
    4379:	4c 89 f8             	mov    %r15,%rax
    437c:	bf 01 00 00 00       	mov    $0x1,%edi
    4381:	48 8d 35 30 46 00 00 	lea    0x4630(%rip),%rsi        # 89b8 <_IO_stdin_used+0x9b8>
    4388:	48 f7 eb             	imul   %rbx
    438b:	4c 89 f8             	mov    %r15,%rax
    438e:	48 c1 f8 3f          	sar    $0x3f,%rax
    4392:	48 89 d3             	mov    %rdx,%rbx
    4395:	48 d1 fb             	sar    %rbx
    4398:	48 29 c3             	sub    %rax,%rbx
    439b:	31 c0                	xor    %eax,%eax
    439d:	48 89 da             	mov    %rbx,%rdx
    43a0:	48 29 eb             	sub    %rbp,%rbx
    43a3:	e8 08 e1 ff ff       	call   24b0 <__printf_chk@plt>
    43a8:	31 c0                	xor    %eax,%eax
    43aa:	48 89 da             	mov    %rbx,%rdx
    43ad:	bf 01 00 00 00       	mov    $0x1,%edi
    43b2:	48 8d 35 ed 41 00 00 	lea    0x41ed(%rip),%rsi        # 85a6 <_IO_stdin_used+0x5a6>
    43b9:	e8 f2 e0 ff ff       	call   24b0 <__printf_chk@plt>
    43be:	48 8b 84 24 f8 00 00 00 	mov    0xf8(%rsp),%rax
    43c6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    43cf:	75 25                	jne    43f6 <main+0x1d86>
    43d1:	48 81 c4 08 01 00 00 	add    $0x108,%rsp
    43d8:	31 c0                	xor    %eax,%eax
    43da:	5b                   	pop    %rbx
    43db:	5d                   	pop    %rbp
    43dc:	41 5c                	pop    %r12
    43de:	41 5d                	pop    %r13
    43e0:	41 5e                	pop    %r14
    43e2:	41 5f                	pop    %r15
    43e4:	c3                   	ret
    43e5:	31 d2                	xor    %edx,%edx
    43e7:	e9 ee fa ff ff       	jmp    3eda <main+0x186a>
    43ec:	bf 01 00 00 00       	mov    $0x1,%edi
    43f1:	e8 1a e1 ff ff       	call   2510 <exit@plt>
    43f6:	e8 85 df ff ff       	call   2380 <__stack_chk_fail@plt>
    43fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004400 <_start>:
    4400:	f3 0f 1e fa          	endbr64
    4404:	31 ed                	xor    %ebp,%ebp
    4406:	49 89 d1             	mov    %rdx,%r9
    4409:	5e                   	pop    %rsi
    440a:	48 89 e2             	mov    %rsp,%rdx
    440d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4411:	50                   	push   %rax
    4412:	54                   	push   %rsp
    4413:	45 31 c0             	xor    %r8d,%r8d
    4416:	31 c9                	xor    %ecx,%ecx
    4418:	48 8d 3d 51 e2 ff ff 	lea    -0x1daf(%rip),%rdi        # 2670 <main>
    441f:	ff 15 b3 6b 00 00    	call   *0x6bb3(%rip)        # afd8 <__libc_start_main@GLIBC_2.34>
    4425:	f4                   	hlt
    4426:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004430 <deregister_tm_clones>:
    4430:	48 8d 3d e9 6b 00 00 	lea    0x6be9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4437:	48 8d 05 e2 6b 00 00 	lea    0x6be2(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    443e:	48 39 f8             	cmp    %rdi,%rax
    4441:	74 15                	je     4458 <deregister_tm_clones+0x28>
    4443:	48 8b 05 96 6b 00 00 	mov    0x6b96(%rip),%rax        # afe0 <_ITM_deregisterTMCloneTable@Base>
    444a:	48 85 c0             	test   %rax,%rax
    444d:	74 09                	je     4458 <deregister_tm_clones+0x28>
    444f:	ff e0                	jmp    *%rax
    4451:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4458:	c3                   	ret
    4459:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004460 <register_tm_clones>:
    4460:	48 8d 3d b9 6b 00 00 	lea    0x6bb9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4467:	48 8d 35 b2 6b 00 00 	lea    0x6bb2(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    446e:	48 29 fe             	sub    %rdi,%rsi
    4471:	48 89 f0             	mov    %rsi,%rax
    4474:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4478:	48 c1 f8 03          	sar    $0x3,%rax
    447c:	48 01 c6             	add    %rax,%rsi
    447f:	48 d1 fe             	sar    %rsi
    4482:	74 14                	je     4498 <register_tm_clones+0x38>
    4484:	48 8b 05 65 6b 00 00 	mov    0x6b65(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    448b:	48 85 c0             	test   %rax,%rax
    448e:	74 08                	je     4498 <register_tm_clones+0x38>
    4490:	ff e0                	jmp    *%rax
    4492:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4498:	c3                   	ret
    4499:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000044a0 <__do_global_dtors_aux>:
    44a0:	f3 0f 1e fa          	endbr64
    44a4:	80 3d 7d 6b 00 00 00 	cmpb   $0x0,0x6b7d(%rip)        # b028 <completed.0>
    44ab:	75 2b                	jne    44d8 <__do_global_dtors_aux+0x38>
    44ad:	55                   	push   %rbp
    44ae:	48 83 3d 42 6b 00 00 00 	cmpq   $0x0,0x6b42(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    44b6:	48 89 e5             	mov    %rsp,%rbp
    44b9:	74 0c                	je     44c7 <__do_global_dtors_aux+0x27>
    44bb:	48 8b 3d 46 6b 00 00 	mov    0x6b46(%rip),%rdi        # b008 <__dso_handle>
    44c2:	e8 29 de ff ff       	call   22f0 <__cxa_finalize@plt>
    44c7:	e8 64 ff ff ff       	call   4430 <deregister_tm_clones>
    44cc:	c6 05 55 6b 00 00 01 	movb   $0x1,0x6b55(%rip)        # b028 <completed.0>
    44d3:	5d                   	pop    %rbp
    44d4:	c3                   	ret
    44d5:	0f 1f 00             	nopl   (%rax)
    44d8:	c3                   	ret
    44d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000044e0 <frame_dummy>:
    44e0:	f3 0f 1e fa          	endbr64
    44e4:	e9 77 ff ff ff       	jmp    4460 <register_tm_clones>
    44e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000044f0 <do_protected_write>:
    44f0:	f3 0f 1e fa          	endbr64
    44f4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    44fb:	48 8b 40 48          	mov    0x48(%rax),%rax
    44ff:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
    4507:	48 8b 48 08          	mov    0x8(%rax),%rcx
    450b:	48 83 00 01          	addq   $0x1,(%rax)
    450f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4516:	48 85 c9             	test   %rcx,%rcx
    4519:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4520:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4524:	48 89 50 08          	mov    %rdx,0x8(%rax)
    4528:	31 c0                	xor    %eax,%eax
    452a:	c3                   	ret
    452b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004530 <barriered_reset>:
    4530:	f3 0f 1e fa          	endbr64
    4534:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    453b:	85 c9                	test   %ecx,%ecx
    453d:	7e 4f                	jle    458e <barriered_reset+0x5e>
    453f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    4546:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    454d:	48 c1 e1 09          	shl    $0x9,%rcx
    4551:	48 8b 50 18          	mov    0x18(%rax),%rdx
    4555:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
    4559:	48 8b 70 38          	mov    0x38(%rax),%rsi
    455d:	31 c0                	xor    %eax,%eax
    455f:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4563:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4568:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
    4570:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
    4578:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    4583:	48 05 00 02 00 00    	add    $0x200,%rax
    4589:	48 39 c1             	cmp    %rax,%rcx
    458c:	75 da                	jne    4568 <barriered_reset+0x38>
    458e:	0f ae f8             	sfence
    4591:	31 c0                	xor    %eax,%eax
    4593:	c3                   	ret
    4594:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    459f:	90                   	nop

00000000000045a0 <external_thread>:
    45a0:	f3 0f 1e fa          	endbr64
    45a4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    45a8:	0f 85 fb 00 00 00    	jne    46a9 <external_thread+0x109>
    45ae:	41 57                	push   %r15
    45b0:	49 89 ff             	mov    %rdi,%r15
    45b3:	41 56                	push   %r14
    45b5:	41 55                	push   %r13
    45b7:	4c 8d 2d 46 3a 00 00 	lea    0x3a46(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
    45be:	41 54                	push   %r12
    45c0:	55                   	push   %rbp
    45c1:	53                   	push   %rbx
    45c2:	48 83 ec 08          	sub    $0x8,%rsp
    45c6:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    45cc:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    45d0:	85 c9                	test   %ecx,%ecx
    45d2:	7e 6e                	jle    4642 <external_thread+0xa2>
    45d4:	45 31 e4             	xor    %r12d,%r12d
    45d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    45e0:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    45e8:	31 db                	xor    %ebx,%ebx
    45ea:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    45ee:	48 8b 06             	mov    (%rsi),%rax
    45f1:	8b 10                	mov    (%rax),%edx
    45f3:	85 d2                	test   %edx,%edx
    45f5:	7e 2a                	jle    4621 <external_thread+0x81>
    45f7:	48 8b 48 08          	mov    0x8(%rax),%rcx
    45fb:	48 89 dd             	mov    %rbx,%rbp
    45fe:	48 c1 e5 08          	shl    $0x8,%rbp
    4602:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4606:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    460d:	45 85 c0             	test   %r8d,%r8d
    4610:	74 36                	je     4648 <external_thread+0xa8>
    4612:	48 83 c3 01          	add    $0x1,%rbx
    4616:	39 da                	cmp    %ebx,%edx
    4618:	7f e1                	jg     45fb <external_thread+0x5b>
    461a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    4621:	49 83 c4 01          	add    $0x1,%r12
    4625:	44 39 e1             	cmp    %r12d,%ecx
    4628:	7f b6                	jg     45e0 <external_thread+0x40>
    462a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    462f:	74 9f                	je     45d0 <external_thread+0x30>
    4631:	48 83 c4 08          	add    $0x8,%rsp
    4635:	31 c0                	xor    %eax,%eax
    4637:	5b                   	pop    %rbx
    4638:	5d                   	pop    %rbp
    4639:	41 5c                	pop    %r12
    463b:	41 5d                	pop    %r13
    463d:	41 5e                	pop    %r14
    463f:	41 5f                	pop    %r15
    4641:	c3                   	ret
    4642:	eb fe                	jmp    4642 <external_thread+0xa2>
    4644:	0f 1f 40 00          	nopl   0x0(%rax)
    4648:	4c 89 28             	mov    %r13,(%rax)
    464b:	48 8b 06             	mov    (%rsi),%rax
    464e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4652:	48 01 ef             	add    %rbp,%rdi
    4655:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    465c:	48 c1 e6 05          	shl    $0x5,%rsi
    4660:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4667:	bf 04 00 00 00       	mov    $0x4,%edi
    466c:	e8 df dc ff ff       	call   2350 <clock_gettime@plt>
    4671:	49 8b 47 50          	mov    0x50(%r15),%rax
    4675:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    4679:	48 8b 40 08          	mov    0x8(%rax),%rax
    467d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
    4688:	0f ae f8             	sfence
    468b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    468f:	48 83 c3 01          	add    $0x1,%rbx
    4693:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    4697:	48 8b 06             	mov    (%rsi),%rax
    469a:	8b 10                	mov    (%rax),%edx
    469c:	39 da                	cmp    %ebx,%edx
    469e:	0f 8f 53 ff ff ff    	jg     45f7 <external_thread+0x57>
    46a4:	e9 71 ff ff ff       	jmp    461a <external_thread+0x7a>
    46a9:	31 c0                	xor    %eax,%eax
    46ab:	c3                   	ret
    46ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000046b0 <timer_thread>:
    46b0:	f3 0f 1e fa          	endbr64
    46b4:	41 57                	push   %r15
    46b6:	48 8d 35 53 39 00 00 	lea    0x3953(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    46bd:	49 89 ff             	mov    %rdi,%r15
    46c0:	41 56                	push   %r14
    46c2:	41 55                	push   %r13
    46c4:	41 54                	push   %r12
    46c6:	55                   	push   %rbp
    46c7:	53                   	push   %rbx
    46c8:	48 83 ec 58          	sub    $0x58,%rsp
    46cc:	8b 57 04             	mov    0x4(%rdi),%edx
    46cf:	bf 01 00 00 00       	mov    $0x1,%edi
    46d4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    46dd:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    46e2:	31 c0                	xor    %eax,%eax
    46e4:	e8 c7 dd ff ff       	call   24b0 <__printf_chk@plt>
    46e9:	66 0f 6f 05 df 44 00 00 	movdqa 0x44df(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    46f1:	ba 88 13 00 00       	mov    $0x1388,%edx
    46f6:	31 c0                	xor    %eax,%eax
    46f8:	48 8d 35 23 39 00 00 	lea    0x3923(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    46ff:	bf 01 00 00 00       	mov    $0x1,%edi
    4704:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    4709:	e8 a2 dd ff ff       	call   24b0 <__printf_chk@plt>
    470e:	41 8b 47 44          	mov    0x44(%r15),%eax
    4712:	89 c3                	mov    %eax,%ebx
    4714:	85 c0                	test   %eax,%eax
    4716:	0f 84 9a 00 00 00    	je     47b6 <timer_thread+0x106>
    471c:	45 31 f6             	xor    %r14d,%r14d
    471f:	31 db                	xor    %ebx,%ebx
    4721:	49 89 e5             	mov    %rsp,%r13
    4724:	31 ed                	xor    %ebp,%ebp
    4726:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
    472b:	4c 89 e7             	mov    %r12,%rdi
    472e:	4c 89 ee             	mov    %r13,%rsi
    4731:	41 83 c6 01          	add    $0x1,%r14d
    4735:	e8 66 dc ff ff       	call   23a0 <nanosleep@plt>
    473a:	49 63 47 30          	movslq 0x30(%r15),%rax
    473e:	8d 7b 01             	lea    0x1(%rbx),%edi
    4741:	85 c0                	test   %eax,%eax
    4743:	7e 4a                	jle    478f <timer_thread+0xdf>
    4745:	49 8b 4f 18          	mov    0x18(%r15),%rcx
    4749:	4c 63 c3             	movslq %ebx,%r8
    474c:	49 c1 e0 09          	shl    $0x9,%r8
    4750:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4754:	0f 1f 40 00          	nopl   0x0(%rax)
    4758:	48 8b 19             	mov    (%rcx),%rbx
    475b:	89 f8                	mov    %edi,%eax
    475d:	48 83 c1 08          	add    $0x8,%rcx
    4761:	99                   	cltd
    4762:	f7 7b 40             	idivl  0x40(%rbx)
    4765:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4769:	83 ea 01             	sub    $0x1,%edx
    476c:	48 63 d2             	movslq %edx,%rdx
    476f:	48 c1 e2 09          	shl    $0x9,%rdx
    4773:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    477e:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    478a:	49 39 c9             	cmp    %rcx,%r9
    478d:	75 c9                	jne    4758 <timer_thread+0xa8>
    478f:	0f ae f0             	mfence
    4792:	49 8b 47 18          	mov    0x18(%r15),%rax
    4796:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    479a:	89 fb                	mov    %edi,%ebx
    479c:	48 8b 00             	mov    (%rax),%rax
    479f:	39 78 40             	cmp    %edi,0x40(%rax)
    47a2:	0f 4e dd             	cmovle %ebp,%ebx
    47a5:	85 c9                	test   %ecx,%ecx
    47a7:	74 0d                	je     47b6 <timer_thread+0x106>
    47a9:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    47b0:	0f 85 75 ff ff ff    	jne    472b <timer_thread+0x7b>
    47b6:	48 8d 3d 7b 38 00 00 	lea    0x387b(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    47bd:	e8 6e db ff ff       	call   2330 <puts@plt>
    47c2:	49 63 57 30          	movslq 0x30(%r15),%rdx
    47c6:	85 d2                	test   %edx,%edx
    47c8:	7e 6b                	jle    4835 <timer_thread+0x185>
    47ca:	49 63 47 40          	movslq 0x40(%r15),%rax
    47ce:	85 c0                	test   %eax,%eax
    47d0:	7e 63                	jle    4835 <timer_thread+0x185>
    47d2:	48 c1 e0 09          	shl    $0x9,%rax
    47d6:	4d 8b 47 18          	mov    0x18(%r15),%r8
    47da:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    47e2:	31 c9                	xor    %ecx,%ecx
    47e4:	48 89 c6             	mov    %rax,%rsi
    47e7:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    47eb:	48 8b 40 38          	mov    0x38(%rax),%rax
    47ef:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    47f3:	f7 c6 00 02 00 00    	test   $0x200,%esi
    47f9:	74 15                	je     4810 <timer_thread+0x160>
    47fb:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    4805:	48 05 00 02 00 00    	add    $0x200,%rax
    480b:	48 39 c2             	cmp    %rax,%rdx
    480e:	74 1c                	je     482c <timer_thread+0x17c>
    4810:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    481a:	48 05 00 04 00 00    	add    $0x400,%rax
    4820:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
    4827:	48 39 c2             	cmp    %rax,%rdx
    482a:	75 e4                	jne    4810 <timer_thread+0x160>
    482c:	48 83 c1 08          	add    $0x8,%rcx
    4830:	48 39 cf             	cmp    %rcx,%rdi
    4833:	75 b2                	jne    47e7 <timer_thread+0x137>
    4835:	0f ae f0             	mfence
    4838:	66 0f 6f 05 a0 43 00 00 	movdqa 0x43a0(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4840:	41 89 dc             	mov    %ebx,%r12d
    4843:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    4848:	49 63 47 28          	movslq 0x28(%r15),%rax
    484c:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    4851:	85 c0                	test   %eax,%eax
    4853:	7e 46                	jle    489b <timer_thread+0x1eb>
    4855:	49 8b 4f 18          	mov    0x18(%r15),%rcx
    4859:	49 63 ec             	movslq %r12d,%rbp
    485c:	48 c1 e5 09          	shl    $0x9,%rbp
    4860:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4864:	0f 1f 40 00          	nopl   0x0(%rax)
    4868:	48 8b 19             	mov    (%rcx),%rbx
    486b:	89 f8                	mov    %edi,%eax
    486d:	48 83 c1 08          	add    $0x8,%rcx
    4871:	99                   	cltd
    4872:	f7 7b 40             	idivl  0x40(%rbx)
    4875:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4879:	48 63 d2             	movslq %edx,%rdx
    487c:	48 c1 e2 09          	shl    $0x9,%rdx
    4880:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    488b:	c7 84 2e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rbp,1)
    4896:	49 39 c8             	cmp    %rcx,%r8
    4899:	75 cd                	jne    4868 <timer_thread+0x1b8>
    489b:	0f ae f0             	mfence
    489e:	49 8b 77 18          	mov    0x18(%r15),%rsi
    48a2:	45 31 e4             	xor    %r12d,%r12d
    48a5:	48 8b 06             	mov    (%rsi),%rax
    48a8:	39 78 40             	cmp    %edi,0x40(%rax)
    48ab:	44 0f 4f e7          	cmovg  %edi,%r12d
    48af:	41 8b 7f 30          	mov    0x30(%r15),%edi
    48b3:	85 ff                	test   %edi,%edi
    48b5:	0f 8e a9 01 00 00    	jle    4a64 <timer_thread+0x3b4>
    48bb:	45 31 f6             	xor    %r14d,%r14d
    48be:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    48c4:	4c 89 f5             	mov    %r14,%rbp
    48c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    48d0:	89 eb                	mov    %ebp,%ebx
    48d2:	4c 8d 2c ed 00 00 00 00 	lea    0x0(,%rbp,8),%r13
    48da:	45 31 f6             	xor    %r14d,%r14d
    48dd:	85 ff                	test   %edi,%edi
    48df:	7e 77                	jle    4958 <timer_thread+0x2a8>
    48e1:	4c 89 f6             	mov    %r14,%rsi
    48e4:	48 63 cf             	movslq %edi,%rcx
    48e7:	45 31 c0             	xor    %r8d,%r8d
    48ea:	48 c1 e6 09          	shl    $0x9,%rsi
    48ee:	66 90                	xchg   %ax,%ax
    48f0:	41 39 e8             	cmp    %ebp,%r8d
    48f3:	74 45                	je     493a <timer_thread+0x28a>
    48f5:	49 8b 47 18          	mov    0x18(%r15),%rax
    48f9:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
    48fd:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4901:	4c 89 c0             	mov    %r8,%rax
    4904:	48 c1 e0 08          	shl    $0x8,%rax
    4908:	48 03 84 32 70 01 00 00 	add    0x170(%rdx,%rsi,1),%rax
    4910:	48 8b 10             	mov    (%rax),%rdx
    4913:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    491a:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    4921:	4c 8b 98 80 00 00 00 	mov    0x80(%rax),%r11
    4928:	4d 85 c9             	test   %r9,%r9
    492b:	0f 8f 97 00 00 00    	jg     49c8 <timer_thread+0x318>
    4931:	4d 85 db             	test   %r11,%r11
    4934:	0f 8f 8e 00 00 00    	jg     49c8 <timer_thread+0x318>
    493a:	49 83 c0 01          	add    $0x1,%r8
    493e:	4c 39 c1             	cmp    %r8,%rcx
    4941:	75 ad                	jne    48f0 <timer_thread+0x240>
    4943:	49 83 fe 01          	cmp    $0x1,%r14
    4947:	74 0f                	je     4958 <timer_thread+0x2a8>
    4949:	41 be 01 00 00 00    	mov    $0x1,%r14d
    494f:	85 ff                	test   %edi,%edi
    4951:	7f 8e                	jg     48e1 <timer_thread+0x231>
    4953:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4958:	48 83 c5 01          	add    $0x1,%rbp
    495c:	39 ef                	cmp    %ebp,%edi
    495e:	0f 8f 6c ff ff ff    	jg     48d0 <timer_thread+0x220>
    4964:	44 89 d5             	mov    %r10d,%ebp
    4967:	85 ff                	test   %edi,%edi
    4969:	7e 3b                	jle    49a6 <timer_thread+0x2f6>
    496b:	31 db                	xor    %ebx,%ebx
    496d:	bf 01 00 00 00       	mov    $0x1,%edi
    4972:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4976:	41 8b 57 40          	mov    0x40(%r15),%edx
    497a:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    497e:	48 8b 40 38          	mov    0x38(%rax),%rax
    4982:	8b 88 a4 01 00 00    	mov    0x1a4(%rax),%ecx
    4988:	39 d1                	cmp    %edx,%ecx
    498a:	0f 8c a8 00 00 00    	jl     4a38 <timer_thread+0x388>
    4990:	8b 80 a4 03 00 00    	mov    0x3a4(%rax),%eax
    4996:	39 d0                	cmp    %edx,%eax
    4998:	7c 6e                	jl     4a08 <timer_thread+0x358>
    499a:	48 83 c3 01          	add    $0x1,%rbx
    499e:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    49a2:	7f d6                	jg     497a <timer_thread+0x2ca>
    49a4:	21 fd                	and    %edi,%ebp
    49a6:	85 ed                	test   %ebp,%ebp
    49a8:	0f 85 b6 00 00 00    	jne    4a64 <timer_thread+0x3b4>
    49ae:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    49b3:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    49b8:	e8 e3 d9 ff ff       	call   23a0 <nanosleep@plt>
    49bd:	e9 86 fe ff ff       	jmp    4848 <timer_thread+0x198>
    49c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    49c8:	8b 80 18 04 00 00    	mov    0x418(%rax),%eax
    49ce:	48 83 ec 08          	sub    $0x8,%rsp
    49d2:	bf 01 00 00 00       	mov    $0x1,%edi
    49d7:	44 89 f1             	mov    %r14d,%ecx
    49da:	48 8d 35 7c 36 00 00 	lea    0x367c(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    49e1:	50                   	push   %rax
    49e2:	8b 82 18 04 00 00    	mov    0x418(%rdx),%eax
    49e8:	89 da                	mov    %ebx,%edx
    49ea:	50                   	push   %rax
    49eb:	31 c0                	xor    %eax,%eax
    49ed:	41 53                	push   %r11
    49ef:	e8 bc da ff ff       	call   24b0 <__printf_chk@plt>
    49f4:	41 8b 7f 30          	mov    0x30(%r15),%edi
    49f8:	48 83 c4 20          	add    $0x20,%rsp
    49fc:	45 31 d2             	xor    %r10d,%r10d
    49ff:	e9 3f ff ff ff       	jmp    4943 <timer_thread+0x293>
    4a04:	0f 1f 40 00          	nopl   0x0(%rax)
    4a08:	89 c2                	mov    %eax,%edx
    4a0a:	bf 01 00 00 00       	mov    $0x1,%edi
    4a0f:	31 c0                	xor    %eax,%eax
    4a11:	48 83 c3 01          	add    $0x1,%rbx
    4a15:	48 8d 35 e9 38 00 00 	lea    0x38e9(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    4a1c:	e8 8f da ff ff       	call   24b0 <__printf_chk@plt>
    4a21:	31 ff                	xor    %edi,%edi
    4a23:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4a27:	0f 8f 45 ff ff ff    	jg     4972 <timer_thread+0x2c2>
    4a2d:	e9 72 ff ff ff       	jmp    49a4 <timer_thread+0x2f4>
    4a32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4a38:	89 ca                	mov    %ecx,%edx
    4a3a:	48 8d 35 c4 38 00 00 	lea    0x38c4(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    4a41:	bf 01 00 00 00       	mov    $0x1,%edi
    4a46:	31 c0                	xor    %eax,%eax
    4a48:	e8 63 da ff ff       	call   24b0 <__printf_chk@plt>
    4a4d:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4a51:	41 8b 57 40          	mov    0x40(%r15),%edx
    4a55:	31 ff                	xor    %edi,%edi
    4a57:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4a5b:	48 8b 40 38          	mov    0x38(%rax),%rax
    4a5f:	e9 2c ff ff ff       	jmp    4990 <timer_thread+0x2e0>
    4a64:	48 8d 3d e9 35 00 00 	lea    0x35e9(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4a6b:	e8 c0 d8 ff ff       	call   2330 <puts@plt>
    4a70:	41 8b 57 44          	mov    0x44(%r15),%edx
    4a74:	85 d2                	test   %edx,%edx
    4a76:	0f 84 eb 00 00 00    	je     4b67 <timer_thread+0x4b7>
    4a7c:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    4a80:	31 db                	xor    %ebx,%ebx
    4a82:	48 8d 2d f1 35 00 00 	lea    0x35f1(%rip),%rbp        # 807a <_IO_stdin_used+0x7a>
    4a89:	4c 8d 25 05 36 00 00 	lea    0x3605(%rip),%r12        # 8095 <_IO_stdin_used+0x95>
    4a90:	85 c0                	test   %eax,%eax
    4a92:	7e 38                	jle    4acc <timer_thread+0x41c>
    4a94:	0f 1f 40 00          	nopl   0x0(%rax)
    4a98:	31 c0                	xor    %eax,%eax
    4a9a:	89 da                	mov    %ebx,%edx
    4a9c:	48 89 ee             	mov    %rbp,%rsi
    4a9f:	bf 01 00 00 00       	mov    $0x1,%edi
    4aa4:	e8 07 da ff ff       	call   24b0 <__printf_chk@plt>
    4aa9:	49 8b 47 18          	mov    0x18(%r15),%rax
    4aad:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4ab1:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
    4ab5:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
    4abc:	0f 84 d2 00 00 00    	je     4b94 <timer_thread+0x4e4>
    4ac2:	48 83 c3 01          	add    $0x1,%rbx
    4ac6:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4aca:	7f cc                	jg     4a98 <timer_thread+0x3e8>
    4acc:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4ad0:	85 d2                	test   %edx,%edx
    4ad2:	7e 7c                	jle    4b50 <timer_thread+0x4a0>
    4ad4:	41 8b 47 40          	mov    0x40(%r15),%eax
    4ad8:	85 c0                	test   %eax,%eax
    4ada:	7e 74                	jle    4b50 <timer_thread+0x4a0>
    4adc:	48 63 f0             	movslq %eax,%rsi
    4adf:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4ae3:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4aeb:	31 c9                	xor    %ecx,%ecx
    4aed:	48 c1 e6 09          	shl    $0x9,%rsi
    4af1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4af8:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4afc:	48 8b 40 38          	mov    0x38(%rax),%rax
    4b00:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4b04:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4b0a:	74 1c                	je     4b28 <timer_thread+0x478>
    4b0c:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    4b16:	48 05 00 02 00 00    	add    $0x200,%rax
    4b1c:	48 39 d0             	cmp    %rdx,%rax
    4b1f:	74 26                	je     4b47 <timer_thread+0x497>
    4b21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4b28:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    4b32:	48 05 00 04 00 00    	add    $0x400,%rax
    4b38:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
    4b42:	48 39 d0             	cmp    %rdx,%rax
    4b45:	75 e1                	jne    4b28 <timer_thread+0x478>
    4b47:	48 83 c1 08          	add    $0x8,%rcx
    4b4b:	48 39 cf             	cmp    %rcx,%rdi
    4b4e:	75 a8                	jne    4af8 <timer_thread+0x448>
    4b50:	0f ae f0             	mfence
    4b53:	48 8d 3d 4d 35 00 00 	lea    0x354d(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4b5a:	e8 d1 d7 ff ff       	call   2330 <puts@plt>
    4b5f:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    4b67:	48 8d 3d 40 35 00 00 	lea    0x3540(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4b6e:	e8 bd d7 ff ff       	call   2330 <puts@plt>
    4b73:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    4b78:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b81:	75 41                	jne    4bc4 <timer_thread+0x514>
    4b83:	48 83 c4 58          	add    $0x58,%rsp
    4b87:	31 c0                	xor    %eax,%eax
    4b89:	5b                   	pop    %rbx
    4b8a:	5d                   	pop    %rbp
    4b8b:	41 5c                	pop    %r12
    4b8d:	41 5d                	pop    %r13
    4b8f:	41 5e                	pop    %r14
    4b91:	41 5f                	pop    %r15
    4b93:	c3                   	ret
    4b94:	4c 89 e7             	mov    %r12,%rdi
    4b97:	e8 94 d7 ff ff       	call   2330 <puts@plt>
    4b9c:	49 8b 47 18          	mov    0x18(%r15),%rax
    4ba0:	be 01 00 00 00       	mov    $0x1,%esi
    4ba5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4ba9:	48 83 c3 01          	add    $0x1,%rbx
    4bad:	8b 78 60             	mov    0x60(%rax),%edi
    4bb0:	e8 ab d8 ff ff       	call   2460 <eventfd_write@plt>
    4bb5:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4bb9:	0f 8f d9 fe ff ff    	jg     4a98 <timer_thread+0x3e8>
    4bbf:	e9 08 ff ff ff       	jmp    4acc <timer_thread+0x41c>
    4bc4:	e8 b7 d7 ff ff       	call   2380 <__stack_chk_fail@plt>
    4bc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004bd0 <minf>:
    4bd0:	f3 0f 1e fa          	endbr64
    4bd4:	39 f7                	cmp    %esi,%edi
    4bd6:	89 f0                	mov    %esi,%eax
    4bd8:	0f 4e c7             	cmovle %edi,%eax
    4bdb:	c3                   	ret
    4bdc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004be0 <maxf>:
    4be0:	f3 0f 1e fa          	endbr64
    4be4:	39 f7                	cmp    %esi,%edi
    4be6:	89 f0                	mov    %esi,%eax
    4be8:	0f 4d c7             	cmovge %edi,%eax
    4beb:	c3                   	ret
    4bec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004bf0 <strtolower>:
    4bf0:	f3 0f 1e fa          	endbr64
    4bf4:	55                   	push   %rbp
    4bf5:	53                   	push   %rbx
    4bf6:	48 83 ec 08          	sub    $0x8,%rsp
    4bfa:	48 0f be 1f          	movsbq (%rdi),%rbx
    4bfe:	84 db                	test   %bl,%bl
    4c00:	74 24                	je     4c26 <strtolower+0x36>
    4c02:	48 89 fd             	mov    %rdi,%rbp
    4c05:	e8 86 d9 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4c0a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4c10:	48 8b 10             	mov    (%rax),%rdx
    4c13:	48 83 c5 01          	add    $0x1,%rbp
    4c17:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4c1a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    4c1d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4c22:	84 db                	test   %bl,%bl
    4c24:	75 ea                	jne    4c10 <strtolower+0x20>
    4c26:	48 83 c4 08          	add    $0x8,%rsp
    4c2a:	5b                   	pop    %rbx
    4c2b:	5d                   	pop    %rbp
    4c2c:	c3                   	ret
    4c2d:	0f 1f 00             	nopl   (%rax)

0000000000004c30 <zh_malloc>:
    4c30:	f3 0f 1e fa          	endbr64
    4c34:	48 83 ec 08          	sub    $0x8,%rsp
    4c38:	e8 33 d8 ff ff       	call   2470 <malloc@plt>
    4c3d:	48 85 c0             	test   %rax,%rax
    4c40:	74 05                	je     4c47 <zh_malloc+0x17>
    4c42:	48 83 c4 08          	add    $0x8,%rsp
    4c46:	c3                   	ret
    4c47:	48 8b 0d d2 63 00 00 	mov    0x63d2(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4c4e:	ba 28 00 00 00       	mov    $0x28,%edx
    4c53:	be 01 00 00 00       	mov    $0x1,%esi
    4c58:	48 8d 3d 59 39 00 00 	lea    0x3959(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    4c5f:	e8 cc d8 ff ff       	call   2530 <fwrite@plt>
    4c64:	bf 01 00 00 00       	mov    $0x1,%edi
    4c69:	e8 a2 d8 ff ff       	call   2510 <exit@plt>
    4c6e:	66 90                	xchg   %ax,%ax

0000000000004c70 <get_filename_ext>:
    4c70:	f3 0f 1e fa          	endbr64
    4c74:	53                   	push   %rbx
    4c75:	be 2e 00 00 00       	mov    $0x2e,%esi
    4c7a:	48 89 fb             	mov    %rdi,%rbx
    4c7d:	e8 2e d7 ff ff       	call   23b0 <strrchr@plt>
    4c82:	48 85 c0             	test   %rax,%rax
    4c85:	74 11                	je     4c98 <get_filename_ext+0x28>
    4c87:	48 39 c3             	cmp    %rax,%rbx
    4c8a:	74 0c                	je     4c98 <get_filename_ext+0x28>
    4c8c:	48 83 c0 01          	add    $0x1,%rax
    4c90:	5b                   	pop    %rbx
    4c91:	c3                   	ret
    4c92:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4c98:	48 8d 05 57 34 00 00 	lea    0x3457(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
    4c9f:	5b                   	pop    %rbx
    4ca0:	c3                   	ret
    4ca1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4cac:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004cb0 <send_headers>:
    4cb0:	f3 0f 1e fa          	endbr64
    4cb4:	41 55                	push   %r13
    4cb6:	49 89 f5             	mov    %rsi,%r13
    4cb9:	48 89 fe             	mov    %rdi,%rsi
    4cbc:	41 54                	push   %r12
    4cbe:	55                   	push   %rbp
    4cbf:	48 89 d5             	mov    %rdx,%rbp
    4cc2:	ba 00 04 00 00       	mov    $0x400,%edx
    4cc7:	53                   	push   %rbx
    4cc8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4ccf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4cd8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4ce0:	31 c0                	xor    %eax,%eax
    4ce2:	49 89 e4             	mov    %rsp,%r12
    4ce5:	4c 89 e7             	mov    %r12,%rdi
    4ce8:	e8 a3 d7 ff ff       	call   2490 <__strcpy_chk@plt>
    4ced:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4cf2:	84 db                	test   %bl,%bl
    4cf4:	74 24                	je     4d1a <send_headers+0x6a>
    4cf6:	e8 95 d8 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4cfb:	48 8b 08             	mov    (%rax),%rcx
    4cfe:	4c 89 e0             	mov    %r12,%rax
    4d01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4d08:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    4d0b:	48 83 c0 01          	add    $0x1,%rax
    4d0f:	88 50 ff             	mov    %dl,-0x1(%rax)
    4d12:	48 0f be 18          	movsbq (%rax),%rbx
    4d16:	84 db                	test   %bl,%bl
    4d18:	75 ee                	jne    4d08 <send_headers+0x58>
    4d1a:	bf 11 00 00 00       	mov    $0x11,%edi
    4d1f:	e8 4c d7 ff ff       	call   2470 <malloc@plt>
    4d24:	48 85 c0             	test   %rax,%rax
    4d27:	0f 84 7e 04 00 00    	je     51ab <send_headers+0x4fb>
    4d2d:	66 0f 6f 05 bb 3e 00 00 	movdqa 0x3ebb(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    4d35:	48 89 45 00          	mov    %rax,0x0(%rbp)
    4d39:	bf 17 00 00 00       	mov    $0x17,%edi
    4d3e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4d46:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4d4a:	0f 11 00             	movups %xmm0,(%rax)
    4d4d:	e8 1e d7 ff ff       	call   2470 <malloc@plt>
    4d52:	48 85 c0             	test   %rax,%rax
    4d55:	0f 84 50 04 00 00    	je     51ab <send_headers+0x4fb>
    4d5b:	66 0f 6f 05 9d 3e 00 00 	movdqa 0x3e9d(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    4d63:	48 89 45 10          	mov    %rax,0x10(%rbp)
    4d67:	4c 89 e7             	mov    %r12,%rdi
    4d6a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    4d74:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4d7c:	0f 11 00             	movups %xmm0,(%rax)
    4d7f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    4d83:	be 2e 00 00 00       	mov    $0x2e,%esi
    4d88:	e8 23 d6 ff ff       	call   23b0 <strrchr@plt>
    4d8d:	48 85 c0             	test   %rax,%rax
    4d90:	0f 84 ea 02 00 00    	je     5080 <send_headers+0x3d0>
    4d96:	4c 39 e0             	cmp    %r12,%rax
    4d99:	0f 84 e1 02 00 00    	je     5080 <send_headers+0x3d0>
    4d9f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    4da3:	48 8d 3d 1a 33 00 00 	lea    0x331a(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4daa:	48 89 de             	mov    %rbx,%rsi
    4dad:	e8 5e d6 ff ff       	call   2410 <strcmp@plt>
    4db2:	85 c0                	test   %eax,%eax
    4db4:	75 20                	jne    4dd6 <send_headers+0x126>
    4db6:	66 0f 6f 05 52 3e 00 00 	movdqa 0x3e52(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4dbe:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4dc6:	66 0f 6f 05 52 3e 00 00 	movdqa 0x3e52(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4dce:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4dd6:	48 89 de             	mov    %rbx,%rsi
    4dd9:	48 8d 3d e8 32 00 00 	lea    0x32e8(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4de0:	e8 2b d6 ff ff       	call   2410 <strcmp@plt>
    4de5:	85 c0                	test   %eax,%eax
    4de7:	75 20                	jne    4e09 <send_headers+0x159>
    4de9:	66 0f 6f 05 1f 3e 00 00 	movdqa 0x3e1f(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4df1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4df9:	66 0f 6f 05 1f 3e 00 00 	movdqa 0x3e1f(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4e01:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4e09:	48 89 de             	mov    %rbx,%rsi
    4e0c:	48 8d 3d ba 32 00 00 	lea    0x32ba(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4e13:	e8 f8 d5 ff ff       	call   2410 <strcmp@plt>
    4e18:	85 c0                	test   %eax,%eax
    4e1a:	0f 84 10 02 00 00    	je     5030 <send_headers+0x380>
    4e20:	48 89 de             	mov    %rbx,%rsi
    4e23:	48 8d 3d a7 32 00 00 	lea    0x32a7(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4e2a:	e8 e1 d5 ff ff       	call   2410 <strcmp@plt>
    4e2f:	85 c0                	test   %eax,%eax
    4e31:	0f 84 a9 02 00 00    	je     50e0 <send_headers+0x430>
    4e37:	48 89 de             	mov    %rbx,%rsi
    4e3a:	48 8d 3d 94 32 00 00 	lea    0x3294(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4e41:	e8 ca d5 ff ff       	call   2410 <strcmp@plt>
    4e46:	85 c0                	test   %eax,%eax
    4e48:	0f 84 6a 02 00 00    	je     50b8 <send_headers+0x408>
    4e4e:	48 89 de             	mov    %rbx,%rsi
    4e51:	48 8d 3d c0 32 00 00 	lea    0x32c0(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4e58:	e8 b3 d5 ff ff       	call   2410 <strcmp@plt>
    4e5d:	85 c0                	test   %eax,%eax
    4e5f:	0f 84 2b 02 00 00    	je     5090 <send_headers+0x3e0>
    4e65:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4e68:	0f 84 52 01 00 00    	je     4fc0 <send_headers+0x310>
    4e6e:	48 89 de             	mov    %rbx,%rsi
    4e71:	48 8d 3d 61 32 00 00 	lea    0x3261(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4e78:	e8 93 d5 ff ff       	call   2410 <strcmp@plt>
    4e7d:	85 c0                	test   %eax,%eax
    4e7f:	0f 84 ab 02 00 00    	je     5130 <send_headers+0x480>
    4e85:	48 89 de             	mov    %rbx,%rsi
    4e88:	48 8d 3d 4e 32 00 00 	lea    0x324e(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4e8f:	e8 7c d5 ff ff       	call   2410 <strcmp@plt>
    4e94:	85 c0                	test   %eax,%eax
    4e96:	0f 84 6c 02 00 00    	je     5108 <send_headers+0x458>
    4e9c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4ea4:	4c 89 e7             	mov    %r12,%rdi
    4ea7:	e8 c4 d4 ff ff       	call   2370 <strlen@plt>
    4eac:	48 89 c7             	mov    %rax,%rdi
    4eaf:	48 89 c3             	mov    %rax,%rbx
    4eb2:	e8 b9 d5 ff ff       	call   2470 <malloc@plt>
    4eb7:	48 85 c0             	test   %rax,%rax
    4eba:	0f 84 eb 02 00 00    	je     51ab <send_headers+0x4fb>
    4ec0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4ec4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    4ec8:	83 fb 08             	cmp    $0x8,%ebx
    4ecb:	0f 83 3f 01 00 00    	jae    5010 <send_headers+0x360>
    4ed1:	f6 c3 04             	test   $0x4,%bl
    4ed4:	0f 85 7b 02 00 00    	jne    5155 <send_headers+0x4a5>
    4eda:	85 db                	test   %ebx,%ebx
    4edc:	74 13                	je     4ef1 <send_headers+0x241>
    4ede:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4ee6:	88 10                	mov    %dl,(%rax)
    4ee8:	f6 c3 02             	test   $0x2,%bl
    4eeb:	0f 85 96 02 00 00    	jne    5187 <send_headers+0x4d7>
    4ef1:	4d 89 e8             	mov    %r13,%r8
    4ef4:	48 8d 0d e6 31 00 00 	lea    0x31e6(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4efb:	4c 89 e7             	mov    %r12,%rdi
    4efe:	31 c0                	xor    %eax,%eax
    4f00:	ba 00 04 00 00       	mov    $0x400,%edx
    4f05:	be 01 00 00 00       	mov    $0x1,%esi
    4f0a:	e8 91 d6 ff ff       	call   25a0 <__sprintf_chk@plt>
    4f0f:	4c 89 e7             	mov    %r12,%rdi
    4f12:	e8 59 d4 ff ff       	call   2370 <strlen@plt>
    4f17:	48 89 c7             	mov    %rax,%rdi
    4f1a:	48 89 c3             	mov    %rax,%rbx
    4f1d:	e8 4e d5 ff ff       	call   2470 <malloc@plt>
    4f22:	48 85 c0             	test   %rax,%rax
    4f25:	0f 84 80 02 00 00    	je     51ab <send_headers+0x4fb>
    4f2b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    4f2f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4f33:	83 fb 08             	cmp    $0x8,%ebx
    4f36:	0f 83 1c 01 00 00    	jae    5058 <send_headers+0x3a8>
    4f3c:	f6 c3 04             	test   $0x4,%bl
    4f3f:	0f 85 29 02 00 00    	jne    516e <send_headers+0x4be>
    4f45:	85 db                	test   %ebx,%ebx
    4f47:	74 13                	je     4f5c <send_headers+0x2ac>
    4f49:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4f51:	88 10                	mov    %dl,(%rax)
    4f53:	f6 c3 02             	test   $0x2,%bl
    4f56:	0f 85 3d 02 00 00    	jne    5199 <send_headers+0x4e9>
    4f5c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    4f61:	bf 02 00 00 00       	mov    $0x2,%edi
    4f66:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4f6e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4f76:	e8 f5 d4 ff ff       	call   2470 <malloc@plt>
    4f7b:	48 85 c0             	test   %rax,%rax
    4f7e:	0f 84 27 02 00 00    	je     51ab <send_headers+0x4fb>
    4f84:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    4f8c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    4f90:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4f98:	66 89 10             	mov    %dx,(%rax)
    4f9b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4fa3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4fac:	0f 85 20 02 00 00    	jne    51d2 <send_headers+0x522>
    4fb2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4fb9:	5b                   	pop    %rbx
    4fba:	5d                   	pop    %rbp
    4fbb:	41 5c                	pop    %r12
    4fbd:	41 5d                	pop    %r13
    4fbf:	c3                   	ret
    4fc0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4fc4:	0f 85 a4 fe ff ff    	jne    4e6e <send_headers+0x1be>
    4fca:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4fce:	0f 85 9a fe ff ff    	jne    4e6e <send_headers+0x1be>
    4fd4:	66 0f 6f 05 94 3c 00 00 	movdqa 0x3c94(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    4fdc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4fe6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4fee:	66 0f 6f 05 8a 3c 00 00 	movdqa 0x3c8a(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    4ff6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4ffe:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    5006:	e9 63 fe ff ff       	jmp    4e6e <send_headers+0x1be>
    500b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5010:	89 da                	mov    %ebx,%edx
    5012:	48 89 c7             	mov    %rax,%rdi
    5015:	4c 89 e6             	mov    %r12,%rsi
    5018:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    501d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    5022:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    5025:	c1 e9 03             	shr    $0x3,%ecx
    5028:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    502b:	e9 c1 fe ff ff       	jmp    4ef1 <send_headers+0x241>
    5030:	66 0f 6f 05 d8 3b 00 00 	movdqa 0x3bd8(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    5038:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5040:	66 0f 6f 05 e8 3b 00 00 	movdqa 0x3be8(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    5048:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5050:	e9 cb fd ff ff       	jmp    4e20 <send_headers+0x170>
    5055:	0f 1f 00             	nopl   (%rax)
    5058:	89 da                	mov    %ebx,%edx
    505a:	48 89 c7             	mov    %rax,%rdi
    505d:	4c 89 e6             	mov    %r12,%rsi
    5060:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    5065:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    506a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    506d:	c1 e9 03             	shr    $0x3,%ecx
    5070:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    5073:	e9 e4 fe ff ff       	jmp    4f5c <send_headers+0x2ac>
    5078:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5080:	48 8d 1d 6f 30 00 00 	lea    0x306f(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    5087:	e9 94 fd ff ff       	jmp    4e20 <send_headers+0x170>
    508c:	0f 1f 40 00          	nopl   0x0(%rax)
    5090:	66 0f 6f 05 b8 3b 00 00 	movdqa 0x3bb8(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5098:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50a0:	66 0f 6f 05 b8 3b 00 00 	movdqa 0x3bb8(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    50a8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    50b0:	e9 b0 fd ff ff       	jmp    4e65 <send_headers+0x1b5>
    50b5:	0f 1f 00             	nopl   (%rax)
    50b8:	66 0f 6f 05 90 3b 00 00 	movdqa 0x3b90(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    50c0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50c8:	66 0f 6f 05 90 3b 00 00 	movdqa 0x3b90(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    50d0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    50d8:	e9 71 fd ff ff       	jmp    4e4e <send_headers+0x19e>
    50dd:	0f 1f 00             	nopl   (%rax)
    50e0:	66 0f 6f 05 28 3b 00 00 	movdqa 0x3b28(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    50e8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50f0:	66 0f 6f 05 48 3b 00 00 	movdqa 0x3b48(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    50f8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5100:	e9 32 fd ff ff       	jmp    4e37 <send_headers+0x187>
    5105:	0f 1f 00             	nopl   (%rax)
    5108:	66 0f 6f 05 40 3b 00 00 	movdqa 0x3b40(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5110:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5118:	66 0f 6f 05 80 3b 00 00 	movdqa 0x3b80(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
    5120:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    5128:	e9 6f fd ff ff       	jmp    4e9c <send_headers+0x1ec>
    512d:	0f 1f 00             	nopl   (%rax)
    5130:	66 0f 6f 05 18 3b 00 00 	movdqa 0x3b18(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5138:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5140:	66 0f 6f 05 48 3b 00 00 	movdqa 0x3b48(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    5148:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    5150:	e9 30 fd ff ff       	jmp    4e85 <send_headers+0x1d5>
    5155:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    515c:	89 db                	mov    %ebx,%ebx
    515e:	89 10                	mov    %edx,(%rax)
    5160:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    5165:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5169:	e9 83 fd ff ff       	jmp    4ef1 <send_headers+0x241>
    516e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    5175:	89 db                	mov    %ebx,%ebx
    5177:	89 10                	mov    %edx,(%rax)
    5179:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    517e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5182:	e9 d5 fd ff ff       	jmp    4f5c <send_headers+0x2ac>
    5187:	89 db                	mov    %ebx,%ebx
    5189:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    518f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5194:	e9 58 fd ff ff       	jmp    4ef1 <send_headers+0x241>
    5199:	89 db                	mov    %ebx,%ebx
    519b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    51a1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    51a6:	e9 b1 fd ff ff       	jmp    4f5c <send_headers+0x2ac>
    51ab:	48 8b 0d 6e 5e 00 00 	mov    0x5e6e(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    51b2:	ba 28 00 00 00       	mov    $0x28,%edx
    51b7:	be 01 00 00 00       	mov    $0x1,%esi
    51bc:	48 8d 3d f5 33 00 00 	lea    0x33f5(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    51c3:	e8 68 d3 ff ff       	call   2530 <fwrite@plt>
    51c8:	bf 01 00 00 00       	mov    $0x1,%edi
    51cd:	e8 3e d3 ff ff       	call   2510 <exit@plt>
    51d2:	e8 a9 d1 ff ff       	call   2380 <__stack_chk_fail@plt>
    51d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000051e0 <copy_file_contents>:
    51e0:	f3 0f 1e fa          	endbr64
    51e4:	41 55                	push   %r13
    51e6:	49 89 d5             	mov    %rdx,%r13
    51e9:	41 54                	push   %r12
    51eb:	49 89 fc             	mov    %rdi,%r12
    51ee:	48 89 f7             	mov    %rsi,%rdi
    51f1:	55                   	push   %rbp
    51f2:	53                   	push   %rbx
    51f3:	48 89 f3             	mov    %rsi,%rbx
    51f6:	48 83 ec 08          	sub    $0x8,%rsp
    51fa:	e8 71 d2 ff ff       	call   2470 <malloc@plt>
    51ff:	48 85 c0             	test   %rax,%rax
    5202:	74 6b                	je     526f <copy_file_contents+0x8f>
    5204:	4c 89 e7             	mov    %r12,%rdi
    5207:	48 89 c5             	mov    %rax,%rbp
    520a:	31 f6                	xor    %esi,%esi
    520c:	31 c0                	xor    %eax,%eax
    520e:	e8 cd d2 ff ff       	call   24e0 <open@plt>
    5213:	41 89 c4             	mov    %eax,%r12d
    5216:	85 c0                	test   %eax,%eax
    5218:	0f 88 b8 d3 ff ff    	js     25d6 <copy_file_contents.cold>
    521e:	48 89 da             	mov    %rbx,%rdx
    5221:	48 89 ee             	mov    %rbp,%rsi
    5224:	89 c7                	mov    %eax,%edi
    5226:	e8 c5 d1 ff ff       	call   23f0 <read@plt>
    522b:	48 98                	cltq
    522d:	48 39 d8             	cmp    %rbx,%rax
    5230:	7c 1e                	jl     5250 <copy_file_contents+0x70>
    5232:	44 89 e7             	mov    %r12d,%edi
    5235:	e8 96 d1 ff ff       	call   23d0 <close@plt>
    523a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    523e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    5242:	48 83 c4 08          	add    $0x8,%rsp
    5246:	5b                   	pop    %rbx
    5247:	5d                   	pop    %rbp
    5248:	41 5c                	pop    %r12
    524a:	41 5d                	pop    %r13
    524c:	c3                   	ret
    524d:	0f 1f 00             	nopl   (%rax)
    5250:	48 8b 0d c9 5d 00 00 	mov    0x5dc9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5257:	ba 1a 00 00 00       	mov    $0x1a,%edx
    525c:	be 01 00 00 00       	mov    $0x1,%esi
    5261:	48 8d 3d 8f 2e 00 00 	lea    0x2e8f(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    5268:	e8 c3 d2 ff ff       	call   2530 <fwrite@plt>
    526d:	eb c3                	jmp    5232 <copy_file_contents+0x52>
    526f:	48 8b 0d aa 5d 00 00 	mov    0x5daa(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5276:	ba 28 00 00 00       	mov    $0x28,%edx
    527b:	be 01 00 00 00       	mov    $0x1,%esi
    5280:	48 8d 3d 31 33 00 00 	lea    0x3331(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    5287:	e8 a4 d2 ff ff       	call   2530 <fwrite@plt>
    528c:	bf 01 00 00 00       	mov    $0x1,%edi
    5291:	e8 7a d2 ff ff       	call   2510 <exit@plt>
    5296:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000052a0 <add_write_request>:
    52a0:	f3 0f 1e fa          	endbr64
    52a4:	8b 46 44             	mov    0x44(%rsi),%eax
    52a7:	48 89 fa             	mov    %rdi,%rdx
    52aa:	48 89 f7             	mov    %rsi,%rdi
    52ad:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    52b3:	8d 70 01             	lea    0x1(%rax),%esi
    52b6:	48 8b 07             	mov    (%rdi),%rax
    52b9:	44 8b 00             	mov    (%rax),%r8d
    52bc:	f6 c1 02             	test   $0x2,%cl
    52bf:	74 00                	je     52c1 <add_write_request+0x21>
    52c1:	89 f0                	mov    %esi,%eax
    52c3:	44 29 c0             	sub    %r8d,%eax
    52c6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    52c9:	0f 82 13 d3 ff ff    	jb     25e2 <add_write_request.cold>
    52cf:	c1 e9 0a             	shr    $0xa,%ecx
    52d2:	48 83 ec 08          	sub    $0x8,%rsp
    52d6:	8b 47 44             	mov    0x44(%rdi),%eax
    52d9:	23 47 58             	and    0x58(%rdi),%eax
    52dc:	83 e1 01             	and    $0x1,%ecx
    52df:	89 77 44             	mov    %esi,0x44(%rdi)
    52e2:	8b 72 08             	mov    0x8(%rdx),%esi
    52e5:	66 0f ef c0          	pxor   %xmm0,%xmm0
    52e9:	d3 e0                	shl    %cl,%eax
    52eb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    52ee:	48 c1 e0 06          	shl    $0x6,%rax
    52f2:	48 03 47 38          	add    0x38(%rdi),%rax
    52f6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    52fc:	89 70 04             	mov    %esi,0x4(%rax)
    52ff:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    5303:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    5309:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5311:	48 89 70 10          	mov    %rsi,0x10(%rax)
    5315:	89 48 18             	mov    %ecx,0x18(%rax)
    5318:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    531f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5327:	48 89 50 20          	mov    %rdx,0x20(%rax)
    532b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    532f:	e8 5c d0 ff ff       	call   2390 <io_uring_submit@plt>
    5334:	31 c0                	xor    %eax,%eax
    5336:	48 83 c4 08          	add    $0x8,%rsp
    533a:	c3                   	ret
    533b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005340 <add_read_request>:
    5340:	f3 0f 1e fa          	endbr64
    5344:	41 55                	push   %r13
    5346:	41 89 fd             	mov    %edi,%r13d
    5349:	41 54                	push   %r12
    534b:	55                   	push   %rbp
    534c:	53                   	push   %rbx
    534d:	48 89 f3             	mov    %rsi,%rbx
    5350:	48 83 ec 08          	sub    $0x8,%rsp
    5354:	8b 46 44             	mov    0x44(%rsi),%eax
    5357:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    535d:	48 8b 16             	mov    (%rsi),%rdx
    5360:	83 c0 01             	add    $0x1,%eax
    5363:	8b 32                	mov    (%rdx),%esi
    5365:	f6 c1 02             	test   $0x2,%cl
    5368:	74 00                	je     536a <add_read_request+0x2a>
    536a:	89 c2                	mov    %eax,%edx
    536c:	29 f2                	sub    %esi,%edx
    536e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5371:	0f 82 7b d2 ff ff    	jb     25f2 <add_read_request.cold>
    5377:	8b 6b 44             	mov    0x44(%rbx),%ebp
    537a:	c1 e9 0a             	shr    $0xa,%ecx
    537d:	89 43 44             	mov    %eax,0x44(%rbx)
    5380:	bf 20 00 00 00       	mov    $0x20,%edi
    5385:	83 e1 01             	and    $0x1,%ecx
    5388:	23 6b 58             	and    0x58(%rbx),%ebp
    538b:	d3 e5                	shl    %cl,%ebp
    538d:	48 c1 e5 06          	shl    $0x6,%rbp
    5391:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5395:	e8 d6 d0 ff ff       	call   2470 <malloc@plt>
    539a:	be 01 00 00 00       	mov    $0x1,%esi
    539f:	bf 00 20 00 00       	mov    $0x2000,%edi
    53a4:	49 89 c4             	mov    %rax,%r12
    53a7:	e8 54 d0 ff ff       	call   2400 <calloc@plt>
    53ac:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    53b1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    53b5:	48 89 df             	mov    %rbx,%rdi
    53b8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    53bd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    53c2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    53cb:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    53d3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    53d7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    53db:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    53e2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    53ea:	48 89 45 10          	mov    %rax,0x10(%rbp)
    53ee:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    53f6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    53fe:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    5402:	e8 89 cf ff ff       	call   2390 <io_uring_submit@plt>
    5407:	48 83 c4 08          	add    $0x8,%rsp
    540b:	31 c0                	xor    %eax,%eax
    540d:	5b                   	pop    %rbx
    540e:	5d                   	pop    %rbp
    540f:	41 5c                	pop    %r12
    5411:	41 5d                	pop    %r13
    5413:	c3                   	ret
    5414:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    541f:	90                   	nop

0000000000005420 <_send_static_string_content>:
    5420:	f3 0f 1e fa          	endbr64
    5424:	41 56                	push   %r14
    5426:	41 89 f6             	mov    %esi,%r14d
    5429:	41 55                	push   %r13
    542b:	49 89 fd             	mov    %rdi,%r13
    542e:	bf 20 00 00 00       	mov    $0x20,%edi
    5433:	41 54                	push   %r12
    5435:	55                   	push   %rbp
    5436:	48 89 d5             	mov    %rdx,%rbp
    5439:	53                   	push   %rbx
    543a:	e8 31 d0 ff ff       	call   2470 <malloc@plt>
    543f:	48 85 c0             	test   %rax,%rax
    5442:	0f 84 dd 00 00 00    	je     5525 <_send_static_string_content+0x105>
    5448:	48 89 c3             	mov    %rax,%rbx
    544b:	4c 89 ef             	mov    %r13,%rdi
    544e:	e8 1d cf ff ff       	call   2370 <strlen@plt>
    5453:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    545a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    545e:	48 89 c7             	mov    %rax,%rdi
    5461:	49 89 c4             	mov    %rax,%r12
    5464:	e8 07 d0 ff ff       	call   2470 <malloc@plt>
    5469:	48 89 c7             	mov    %rax,%rdi
    546c:	48 85 c0             	test   %rax,%rax
    546f:	0f 84 b0 00 00 00    	je     5525 <_send_static_string_content+0x105>
    5475:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5479:	4c 89 e2             	mov    %r12,%rdx
    547c:	4c 89 ee             	mov    %r13,%rsi
    547f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    5483:	e8 b8 cf ff ff       	call   2440 <memcpy@plt>
    5488:	8b 45 44             	mov    0x44(%rbp),%eax
    548b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    5491:	8d 50 01             	lea    0x1(%rax),%edx
    5494:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5498:	8b 30                	mov    (%rax),%esi
    549a:	f6 c1 02             	test   $0x2,%cl
    549d:	0f 85 7d 00 00 00    	jne    5520 <_send_static_string_content+0x100>
    54a3:	89 d0                	mov    %edx,%eax
    54a5:	29 f0                	sub    %esi,%eax
    54a7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    54aa:	0f 82 4c d1 ff ff    	jb     25fc <_send_static_string_content.cold>
    54b0:	c1 e9 0a             	shr    $0xa,%ecx
    54b3:	8b 45 44             	mov    0x44(%rbp),%eax
    54b6:	23 45 58             	and    0x58(%rbp),%eax
    54b9:	89 55 44             	mov    %edx,0x44(%rbp)
    54bc:	83 e1 01             	and    $0x1,%ecx
    54bf:	8b 53 04             	mov    0x4(%rbx),%edx
    54c2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    54c8:	66 0f ef c0          	pxor   %xmm0,%xmm0
    54cc:	d3 e0                	shl    %cl,%eax
    54ce:	8b 4b 08             	mov    0x8(%rbx),%ecx
    54d1:	48 89 ef             	mov    %rbp,%rdi
    54d4:	48 c1 e0 06          	shl    $0x6,%rax
    54d8:	48 03 45 38          	add    0x38(%rbp),%rax
    54dc:	89 48 04             	mov    %ecx,0x4(%rax)
    54df:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    54e3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    54e9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    54f1:	48 89 48 10          	mov    %rcx,0x10(%rax)
    54f5:	89 50 18             	mov    %edx,0x18(%rax)
    54f8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    54ff:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5507:	48 89 58 20          	mov    %rbx,0x20(%rax)
    550b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    550f:	5b                   	pop    %rbx
    5510:	5d                   	pop    %rbp
    5511:	41 5c                	pop    %r12
    5513:	41 5d                	pop    %r13
    5515:	41 5e                	pop    %r14
    5517:	e9 74 ce ff ff       	jmp    2390 <io_uring_submit@plt>
    551c:	0f 1f 40 00          	nopl   0x0(%rax)
    5520:	e9 7e ff ff ff       	jmp    54a3 <_send_static_string_content+0x83>
    5525:	48 8b 0d f4 5a 00 00 	mov    0x5af4(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    552c:	ba 28 00 00 00       	mov    $0x28,%edx
    5531:	be 01 00 00 00       	mov    $0x1,%esi
    5536:	48 8d 3d 7b 30 00 00 	lea    0x307b(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    553d:	e8 ee cf ff ff       	call   2530 <fwrite@plt>
    5542:	bf 01 00 00 00       	mov    $0x1,%edi
    5547:	e8 c4 cf ff ff       	call   2510 <exit@plt>
    554c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005550 <handle_unimplemented_method>:
    5550:	f3 0f 1e fa          	endbr64
    5554:	48 89 f2             	mov    %rsi,%rdx
    5557:	89 fe                	mov    %edi,%esi
    5559:	48 8b 3d b8 5a 00 00 	mov    0x5ab8(%rip),%rdi        # b018 <unimplemented_content>
    5560:	e9 bb fe ff ff       	jmp    5420 <_send_static_string_content>
    5565:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005570 <handle_http_404>:
    5570:	f3 0f 1e fa          	endbr64
    5574:	48 89 f2             	mov    %rsi,%rdx
    5577:	89 fe                	mov    %edi,%esi
    5579:	48 8b 3d 90 5a 00 00 	mov    0x5a90(%rip),%rdi        # b010 <http_404_content>
    5580:	e9 9b fe ff ff       	jmp    5420 <_send_static_string_content>
    5585:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005590 <handle_get_method>:
    5590:	f3 0f 1e fa          	endbr64
    5594:	41 56                	push   %r14
    5596:	41 55                	push   %r13
    5598:	49 89 d5             	mov    %rdx,%r13
    559b:	41 54                	push   %r12
    559d:	41 89 f4             	mov    %esi,%r12d
    55a0:	55                   	push   %rbp
    55a1:	48 89 fd             	mov    %rdi,%rbp
    55a4:	53                   	push   %rbx
    55a5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    55ac:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    55b5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    55bd:	31 c0                	xor    %eax,%eax
    55bf:	e8 ac cd ff ff       	call   2370 <strlen@plt>
    55c4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    55c9:	48 89 c3             	mov    %rax,%rbx
    55cc:	0f 84 b6 00 00 00    	je     5688 <handle_get_method+0xf8>
    55d2:	b8 69 63 00 00       	mov    $0x6369,%eax
    55d7:	48 89 ee             	mov    %rbp,%rsi
    55da:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    55de:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    55e3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    55eb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    55f3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    55fe:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    5606:	e8 15 ce ff ff       	call   2420 <__memcpy_chk@plt>
    560b:	48 89 e6             	mov    %rsp,%rsi
    560e:	4c 89 f7             	mov    %r14,%rdi
    5611:	e8 1a ce ff ff       	call   2430 <stat@plt>
    5616:	83 f8 ff             	cmp    $0xffffffff,%eax
    5619:	0f 84 d3 00 00 00    	je     56f2 <handle_get_method+0x162>
    561f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5623:	25 00 f0 00 00       	and    $0xf000,%eax
    5628:	3d 00 80 00 00       	cmp    $0x8000,%eax
    562d:	0f 84 f5 00 00 00    	je     5728 <handle_get_method+0x198>
    5633:	48 8b 3d d6 59 00 00 	mov    0x59d6(%rip),%rdi        # b010 <http_404_content>
    563a:	4c 89 ea             	mov    %r13,%rdx
    563d:	44 89 e6             	mov    %r12d,%esi
    5640:	e8 db fd ff ff       	call   5420 <_send_static_string_content>
    5645:	4c 89 f2             	mov    %r14,%rdx
    5648:	bf 01 00 00 00       	mov    $0x1,%edi
    564d:	31 c0                	xor    %eax,%eax
    564f:	48 8d 35 f1 2a 00 00 	lea    0x2af1(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    5656:	e8 55 ce ff ff       	call   24b0 <__printf_chk@plt>
    565b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5663:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    566c:	0f 85 20 01 00 00    	jne    5792 <handle_get_method+0x202>
    5672:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5679:	5b                   	pop    %rbx
    567a:	5d                   	pop    %rbp
    567b:	41 5c                	pop    %r12
    567d:	41 5d                	pop    %r13
    567f:	41 5e                	pop    %r14
    5681:	c3                   	ret
    5682:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5688:	ba 69 63 00 00       	mov    $0x6369,%edx
    568d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5695:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    569a:	48 89 ee             	mov    %rbp,%rsi
    569d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    56a5:	48 89 c2             	mov    %rax,%rdx
    56a8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    56b0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    56bb:	e8 60 cd ff ff       	call   2420 <__memcpy_chk@plt>
    56c0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    56c5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    56ca:	48 8d 35 41 2a 00 00 	lea    0x2a41(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    56d1:	48 29 d9             	sub    %rbx,%rcx
    56d4:	ba 0b 00 00 00       	mov    $0xb,%edx
    56d9:	e8 42 cd ff ff       	call   2420 <__memcpy_chk@plt>
    56de:	48 89 e6             	mov    %rsp,%rsi
    56e1:	4c 89 f7             	mov    %r14,%rdi
    56e4:	e8 47 cd ff ff       	call   2430 <stat@plt>
    56e9:	83 f8 ff             	cmp    $0xffffffff,%eax
    56ec:	0f 85 2d ff ff ff    	jne    561f <handle_get_method+0x8f>
    56f2:	4c 89 f2             	mov    %r14,%rdx
    56f5:	48 89 e9             	mov    %rbp,%rcx
    56f8:	48 8d 35 1e 2a 00 00 	lea    0x2a1e(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    56ff:	31 c0                	xor    %eax,%eax
    5701:	bf 01 00 00 00       	mov    $0x1,%edi
    5706:	e8 a5 cd ff ff       	call   24b0 <__printf_chk@plt>
    570b:	48 8b 3d fe 58 00 00 	mov    0x58fe(%rip),%rdi        # b010 <http_404_content>
    5712:	4c 89 ea             	mov    %r13,%rdx
    5715:	44 89 e6             	mov    %r12d,%esi
    5718:	e8 03 fd ff ff       	call   5420 <_send_static_string_content>
    571d:	e9 39 ff ff ff       	jmp    565b <handle_get_method+0xcb>
    5722:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5728:	bf 70 00 00 00       	mov    $0x70,%edi
    572d:	e8 3e cd ff ff       	call   2470 <malloc@plt>
    5732:	48 89 c3             	mov    %rax,%rbx
    5735:	48 85 c0             	test   %rax,%rax
    5738:	74 5d                	je     5797 <handle_get_method+0x207>
    573a:	44 89 60 08          	mov    %r12d,0x8(%rax)
    573e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5743:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5747:	4c 89 f7             	mov    %r14,%rdi
    574a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    5751:	e8 5a f5 ff ff       	call   4cb0 <send_headers>
    5756:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    575b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    575f:	4c 89 f7             	mov    %r14,%rdi
    5762:	e8 79 fa ff ff       	call   51e0 <copy_file_contents>
    5767:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    576c:	4c 89 f2             	mov    %r14,%rdx
    576f:	31 c0                	xor    %eax,%eax
    5771:	48 8d 35 bd 29 00 00 	lea    0x29bd(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    5778:	bf 01 00 00 00       	mov    $0x1,%edi
    577d:	e8 2e cd ff ff       	call   24b0 <__printf_chk@plt>
    5782:	4c 89 ee             	mov    %r13,%rsi
    5785:	48 89 df             	mov    %rbx,%rdi
    5788:	e8 13 fb ff ff       	call   52a0 <add_write_request>
    578d:	e9 c9 fe ff ff       	jmp    565b <handle_get_method+0xcb>
    5792:	e8 e9 cb ff ff       	call   2380 <__stack_chk_fail@plt>
    5797:	48 8b 0d 82 58 00 00 	mov    0x5882(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    579e:	ba 28 00 00 00       	mov    $0x28,%edx
    57a3:	be 01 00 00 00       	mov    $0x1,%esi
    57a8:	48 8d 3d 09 2e 00 00 	lea    0x2e09(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    57af:	e8 7c cd ff ff       	call   2530 <fwrite@plt>
    57b4:	bf 01 00 00 00       	mov    $0x1,%edi
    57b9:	e8 52 cd ff ff       	call   2510 <exit@plt>
    57be:	66 90                	xchg   %ax,%ax

00000000000057c0 <handle_http_method>:
    57c0:	f3 0f 1e fa          	endbr64
    57c4:	41 57                	push   %r15
    57c6:	41 56                	push   %r14
    57c8:	4c 8d 35 dd 28 00 00 	lea    0x28dd(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
    57cf:	41 55                	push   %r13
    57d1:	49 89 d5             	mov    %rdx,%r13
    57d4:	41 54                	push   %r12
    57d6:	41 89 f4             	mov    %esi,%r12d
    57d9:	4c 89 f6             	mov    %r14,%rsi
    57dc:	55                   	push   %rbp
    57dd:	53                   	push   %rbx
    57de:	48 83 ec 18          	sub    $0x18,%rsp
    57e2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    57eb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    57f0:	31 c0                	xor    %eax,%eax
    57f2:	49 89 e7             	mov    %rsp,%r15
    57f5:	4c 89 fa             	mov    %r15,%rdx
    57f8:	e8 e3 cb ff ff       	call   23e0 <strtok_r@plt>
    57fd:	48 0f be 18          	movsbq (%rax),%rbx
    5801:	48 89 c5             	mov    %rax,%rbp
    5804:	84 db                	test   %bl,%bl
    5806:	74 1d                	je     5825 <handle_http_method+0x65>
    5808:	e8 83 cd ff ff       	call   2590 <__ctype_tolower_loc@plt>
    580d:	48 89 ea             	mov    %rbp,%rdx
    5810:	48 8b 08             	mov    (%rax),%rcx
    5813:	48 83 c2 01          	add    $0x1,%rdx
    5817:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    581a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    581d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5821:	84 db                	test   %bl,%bl
    5823:	75 eb                	jne    5810 <handle_http_method+0x50>
    5825:	4c 89 fa             	mov    %r15,%rdx
    5828:	4c 89 f6             	mov    %r14,%rsi
    582b:	31 ff                	xor    %edi,%edi
    582d:	e8 ae cb ff ff       	call   23e0 <strtok_r@plt>
    5832:	48 8d 35 21 29 00 00 	lea    0x2921(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    5839:	48 89 ef             	mov    %rbp,%rdi
    583c:	48 89 c3             	mov    %rax,%rbx
    583f:	e8 cc cb ff ff       	call   2410 <strcmp@plt>
    5844:	4c 89 ea             	mov    %r13,%rdx
    5847:	44 89 e6             	mov    %r12d,%esi
    584a:	85 c0                	test   %eax,%eax
    584c:	75 2a                	jne    5878 <handle_http_method+0xb8>
    584e:	48 89 df             	mov    %rbx,%rdi
    5851:	e8 3a fd ff ff       	call   5590 <handle_get_method>
    5856:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    585b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5864:	75 20                	jne    5886 <handle_http_method+0xc6>
    5866:	48 83 c4 18          	add    $0x18,%rsp
    586a:	5b                   	pop    %rbx
    586b:	5d                   	pop    %rbp
    586c:	41 5c                	pop    %r12
    586e:	41 5d                	pop    %r13
    5870:	41 5e                	pop    %r14
    5872:	41 5f                	pop    %r15
    5874:	c3                   	ret
    5875:	0f 1f 00             	nopl   (%rax)
    5878:	48 8b 3d 99 57 00 00 	mov    0x5799(%rip),%rdi        # b018 <unimplemented_content>
    587f:	e8 9c fb ff ff       	call   5420 <_send_static_string_content>
    5884:	eb d0                	jmp    5856 <handle_http_method+0x96>
    5886:	e8 f5 ca ff ff       	call   2380 <__stack_chk_fail@plt>
    588b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005890 <get_line>:
    5890:	f3 0f 1e fa          	endbr64
    5894:	85 d2                	test   %edx,%edx
    5896:	7e 38                	jle    58d0 <get_line+0x40>
    5898:	48 63 d2             	movslq %edx,%rdx
    589b:	48 83 c7 01          	add    $0x1,%rdi
    589f:	48 01 f2             	add    %rsi,%rdx
    58a2:	eb 11                	jmp    58b5 <get_line+0x25>
    58a4:	0f 1f 40 00          	nopl   0x0(%rax)
    58a8:	48 83 c6 01          	add    $0x1,%rsi
    58ac:	48 83 c7 01          	add    $0x1,%rdi
    58b0:	48 39 d6             	cmp    %rdx,%rsi
    58b3:	74 1b                	je     58d0 <get_line+0x40>
    58b5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    58b9:	88 06                	mov    %al,(%rsi)
    58bb:	3c 0d                	cmp    $0xd,%al
    58bd:	75 e9                	jne    58a8 <get_line+0x18>
    58bf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    58c2:	75 e4                	jne    58a8 <get_line+0x18>
    58c4:	c6 06 00             	movb   $0x0,(%rsi)
    58c7:	31 c0                	xor    %eax,%eax
    58c9:	c3                   	ret
    58ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    58d0:	b8 01 00 00 00       	mov    $0x1,%eax
    58d5:	c3                   	ret
    58d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000058e0 <handle_client_request>:
    58e0:	f3 0f 1e fa          	endbr64
    58e4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    58eb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    58ef:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    58f8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5900:	31 c0                	xor    %eax,%eax
    5902:	49 89 e2             	mov    %rsp,%r10
    5905:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    590d:	4c 89 d0             	mov    %r10,%rax
    5910:	eb 13                	jmp    5925 <handle_client_request+0x45>
    5912:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5918:	48 83 c0 01          	add    $0x1,%rax
    591c:	48 83 c1 01          	add    $0x1,%rcx
    5920:	4c 39 c8             	cmp    %r9,%rax
    5923:	74 4b                	je     5970 <handle_client_request+0x90>
    5925:	44 0f b6 01          	movzbl (%rcx),%r8d
    5929:	44 88 00             	mov    %r8b,(%rax)
    592c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5930:	75 e6                	jne    5918 <handle_client_request+0x38>
    5932:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5936:	75 e0                	jne    5918 <handle_client_request+0x38>
    5938:	c6 00 00             	movb   $0x0,(%rax)
    593b:	8b 47 08             	mov    0x8(%rdi),%eax
    593e:	48 89 f2             	mov    %rsi,%rdx
    5941:	4c 89 d7             	mov    %r10,%rdi
    5944:	89 c6                	mov    %eax,%esi
    5946:	e8 75 fe ff ff       	call   57c0 <handle_http_method>
    594b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5953:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    595c:	75 39                	jne    5997 <handle_client_request+0xb7>
    595e:	31 c0                	xor    %eax,%eax
    5960:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5967:	c3                   	ret
    5968:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5970:	48 8b 0d a9 56 00 00 	mov    0x56a9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5977:	ba 12 00 00 00       	mov    $0x12,%edx
    597c:	be 01 00 00 00       	mov    $0x1,%esi
    5981:	48 8d 3d d6 27 00 00 	lea    0x27d6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5988:	e8 a3 cb ff ff       	call   2530 <fwrite@plt>
    598d:	bf 01 00 00 00       	mov    $0x1,%edi
    5992:	e8 79 cb ff ff       	call   2510 <exit@plt>
    5997:	e8 e4 c9 ff ff       	call   2380 <__stack_chk_fail@plt>
    599c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000059a0 <add_accept_request>:
    59a0:	f3 0f 1e fa          	endbr64
    59a4:	55                   	push   %rbp
    59a5:	53                   	push   %rbx
    59a6:	48 89 cb             	mov    %rcx,%rbx
    59a9:	48 83 ec 08          	sub    $0x8,%rsp
    59ad:	8b 41 44             	mov    0x44(%rcx),%eax
    59b0:	4c 8b 03             	mov    (%rbx),%r8
    59b3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    59b9:	83 c0 01             	add    $0x1,%eax
    59bc:	45 8b 08             	mov    (%r8),%r9d
    59bf:	f6 c1 02             	test   $0x2,%cl
    59c2:	74 00                	je     59c4 <add_accept_request+0x24>
    59c4:	41 89 c0             	mov    %eax,%r8d
    59c7:	45 29 c8             	sub    %r9d,%r8d
    59ca:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    59ce:	0f 82 38 cc ff ff    	jb     260c <add_accept_request.cold>
    59d4:	c1 e9 0a             	shr    $0xa,%ecx
    59d7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    59da:	23 6b 58             	and    0x58(%rbx),%ebp
    59dd:	89 43 44             	mov    %eax,0x44(%rbx)
    59e0:	83 e1 01             	and    $0x1,%ecx
    59e3:	66 0f ef c0          	pxor   %xmm0,%xmm0
    59e7:	d3 e5                	shl    %cl,%ebp
    59e9:	48 c1 e5 06          	shl    $0x6,%rbp
    59ed:	48 03 6b 38          	add    0x38(%rbx),%rbp
    59f1:	89 7d 04             	mov    %edi,0x4(%rbp)
    59f4:	bf 10 00 00 00       	mov    $0x10,%edi
    59f9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    5a00:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    5a04:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    5a08:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    5a10:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    5a18:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    5a1c:	e8 4f ca ff ff       	call   2470 <malloc@plt>
    5a21:	48 89 df             	mov    %rbx,%rdi
    5a24:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    5a2a:	48 89 45 20          	mov    %rax,0x20(%rbp)
    5a2e:	48 83 c4 08          	add    $0x8,%rsp
    5a32:	5b                   	pop    %rbx
    5a33:	5d                   	pop    %rbp
    5a34:	e9 57 c9 ff ff       	jmp    2390 <io_uring_submit@plt>
    5a39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005a40 <io_thread>:
    5a40:	f3 0f 1e fa          	endbr64
    5a44:	41 57                	push   %r15
    5a46:	31 d2                	xor    %edx,%edx
    5a48:	41 56                	push   %r14
    5a4a:	41 55                	push   %r13
    5a4c:	41 54                	push   %r12
    5a4e:	55                   	push   %rbp
    5a4f:	48 89 fd             	mov    %rdi,%rbp
    5a52:	53                   	push   %rbx
    5a53:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    5a5a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5a63:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    5a6b:	48 8b 47 58          	mov    0x58(%rdi),%rax
    5a6f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5a74:	bf 00 01 00 00       	mov    $0x100,%edi
    5a79:	48 89 de             	mov    %rbx,%rsi
    5a7c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5a80:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5a85:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    5a8a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    5a8f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5a94:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    5a9c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5aa1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5aa9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5aae:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5ab6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5abb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5ac3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5ac8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5ad0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5ad5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    5add:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5ae5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    5aed:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5af5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    5afd:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5b05:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5b0d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5b15:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5b1d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5b25:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5b2d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5b34:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    5b3c:	e8 0f c9 ff ff       	call   2450 <io_uring_queue_init@plt>
    5b41:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5b45:	31 f6                	xor    %esi,%esi
    5b47:	e8 04 ca ff ff       	call   2550 <io_uring_register_eventfd@plt>
    5b4c:	31 d2                	xor    %edx,%edx
    5b4e:	be 01 00 00 00       	mov    $0x1,%esi
    5b53:	bf 02 00 00 00       	mov    $0x2,%edi
    5b58:	e8 53 ca ff ff       	call   25b0 <socket@plt>
    5b5d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5b60:	0f 84 e8 ca ff ff    	je     264e <io_thread.cold+0x38>
    5b66:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5b6b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5b71:	89 c7                	mov    %eax,%edi
    5b73:	41 89 c4             	mov    %eax,%r12d
    5b76:	ba 02 00 00 00       	mov    $0x2,%edx
    5b7b:	be 01 00 00 00       	mov    $0x1,%esi
    5b80:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    5b88:	e8 b3 c7 ff ff       	call   2340 <setsockopt@plt>
    5b8d:	85 c0                	test   %eax,%eax
    5b8f:	0f 88 8d ca ff ff    	js     2622 <io_thread.cold+0xc>
    5b95:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    5b9a:	ba 10 00 00 00       	mov    $0x10,%edx
    5b9f:	44 89 e7             	mov    %r12d,%edi
    5ba2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5bab:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    5bb3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
    5bbb:	e8 00 c9 ff ff       	call   24c0 <bind@plt>
    5bc0:	85 c0                	test   %eax,%eax
    5bc2:	0f 88 92 ca ff ff    	js     265a <io_thread.cold+0x44>
    5bc8:	be 0a 00 00 00       	mov    $0xa,%esi
    5bcd:	44 89 e7             	mov    %r12d,%edi
    5bd0:	e8 ab c8 ff ff       	call   2480 <listen@plt>
    5bd5:	85 c0                	test   %eax,%eax
    5bd7:	0f 88 51 ca ff ff    	js     262e <io_thread.cold+0x18>
    5bdd:	ba db 18 00 00       	mov    $0x18db,%edx
    5be2:	48 8d 35 ba 25 00 00 	lea    0x25ba(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5be9:	bf 01 00 00 00       	mov    $0x1,%edi
    5bee:	31 c0                	xor    %eax,%eax
    5bf0:	e8 bb c8 ff ff       	call   24b0 <__printf_chk@plt>
    5bf5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5bfa:	48 89 d9             	mov    %rbx,%rcx
    5bfd:	44 89 e7             	mov    %r12d,%edi
    5c00:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5c05:	48 89 c6             	mov    %rax,%rsi
    5c08:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5c0d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    5c12:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    5c1a:	e8 81 fd ff ff       	call   59a0 <add_accept_request>
    5c1f:	bf 01 00 00 00       	mov    $0x1,%edi
    5c24:	be 10 00 00 00       	mov    $0x10,%esi
    5c29:	e8 d2 c7 ff ff       	call   2400 <calloc@plt>
    5c2e:	bf 0a 00 00 00       	mov    $0xa,%edi
    5c33:	49 89 c5             	mov    %rax,%r13
    5c36:	e8 35 c8 ff ff       	call   2470 <malloc@plt>
    5c3b:	48 85 c0             	test   %rax,%rax
    5c3e:	0f 84 ae 04 00 00    	je     60f2 <io_thread+0x6b2>
    5c44:	49 89 45 00          	mov    %rax,0x0(%r13)
    5c48:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5c4f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5c56:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    5c5e:	8d 50 01             	lea    0x1(%rax),%edx
    5c61:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5c66:	8b 30                	mov    (%rax),%esi
    5c68:	f6 c1 02             	test   $0x2,%cl
    5c6b:	0f 85 0f 04 00 00    	jne    6080 <io_thread+0x640>
    5c71:	89 d0                	mov    %edx,%eax
    5c73:	29 f0                	sub    %esi,%eax
    5c75:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5c7c:	0f 82 c2 c9 ff ff    	jb     2644 <io_thread.cold+0x2e>
    5c82:	c1 e9 0a             	shr    $0xa,%ecx
    5c85:	48 8d 75 60          	lea    0x60(%rbp),%rsi
    5c89:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5c8d:	48 89 df             	mov    %rbx,%rdi
    5c90:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5c97:	83 e1 01             	and    $0x1,%ecx
    5c9a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5ca1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5ca8:	d3 e0                	shl    %cl,%eax
    5caa:	8b 55 60             	mov    0x60(%rbp),%edx
    5cad:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5cb2:	48 c1 e0 06          	shl    $0x6,%rax
    5cb6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5cbe:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5cc4:	89 50 04             	mov    %edx,0x4(%rax)
    5cc7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5ccf:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5cd3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5cdb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5ce3:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5ce7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5ceb:	e8 a0 c6 ff ff       	call   2390 <io_uring_submit@plt>
    5cf0:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5cf4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5cf9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5d01:	0f 85 d7 01 00 00    	jne    5ede <io_thread+0x49e>
    5d07:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5d0c:	4d 89 ce             	mov    %r9,%r14
    5d0f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5d14:	0f 1f 40 00          	nopl   0x0(%rax)
    5d18:	48 8d 3d 9a 24 00 00 	lea    0x249a(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5d1f:	e8 0c c6 ff ff       	call   2330 <puts@plt>
    5d24:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5d2b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    5d32:	c1 e9 0b             	shr    $0xb,%ecx
    5d35:	83 e1 01             	and    $0x1,%ecx
    5d38:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5d40:	8b 00                	mov    (%rax),%eax
    5d42:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5d4a:	8b 16                	mov    (%rsi),%edx
    5d4c:	39 d0                	cmp    %edx,%eax
    5d4e:	74 36                	je     5d86 <io_thread+0x346>
    5d50:	89 f8                	mov    %edi,%eax
    5d52:	21 d0                	and    %edx,%eax
    5d54:	d3 e0                	shl    %cl,%eax
    5d56:	48 c1 e0 04          	shl    $0x4,%rax
    5d5a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    5d62:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5d6a:	0f 85 a8 01 00 00    	jne    5f18 <io_thread+0x4d8>
    5d70:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5d74:	0f 85 0e 03 00 00    	jne    6088 <io_thread+0x648>
    5d7a:	8b 40 08             	mov    0x8(%rax),%eax
    5d7d:	83 c2 01             	add    $0x1,%edx
    5d80:	89 16                	mov    %edx,(%rsi)
    5d82:	85 c0                	test   %eax,%eax
    5d84:	79 b2                	jns    5d38 <io_thread+0x2f8>
    5d86:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    5d8f:	90                   	nop
    5d90:	45 31 c0             	xor    %r8d,%r8d
    5d93:	31 d2                	xor    %edx,%edx
    5d95:	b9 01 00 00 00       	mov    $0x1,%ecx
    5d9a:	4c 89 f6             	mov    %r14,%rsi
    5d9d:	48 89 df             	mov    %rbx,%rdi
    5da0:	e8 fb c6 ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    5da5:	41 89 c7             	mov    %eax,%r15d
    5da8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5dad:	48 83 38 01          	cmpq   $0x1,(%rax)
    5db1:	0f 84 e1 02 00 00    	je     6098 <io_thread+0x658>
    5db7:	48 8d 3d 21 24 00 00 	lea    0x2421(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5dbe:	e8 6d c5 ff ff       	call   2330 <puts@plt>
    5dc3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5dc8:	4c 8b 22             	mov    (%rdx),%r12
    5dcb:	45 85 ff             	test   %r15d,%r15d
    5dce:	0f 88 42 c8 ff ff    	js     2616 <io_thread.cold>
    5dd4:	8b 42 08             	mov    0x8(%rdx),%eax
    5dd7:	45 8b 04 24          	mov    (%r12),%r8d
    5ddb:	85 c0                	test   %eax,%eax
    5ddd:	0f 88 d5 02 00 00    	js     60b8 <io_thread+0x678>
    5de3:	41 83 f8 01          	cmp    $0x1,%r8d
    5de7:	0f 84 7b 01 00 00    	je     5f68 <io_thread+0x528>
    5ded:	41 83 f8 02          	cmp    $0x2,%r8d
    5df1:	0f 84 a1 01 00 00    	je     5f98 <io_thread+0x558>
    5df7:	45 85 c0             	test   %r8d,%r8d
    5dfa:	0f 85 50 01 00 00    	jne    5f50 <io_thread+0x510>
    5e00:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5e05:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5e0a:	48 89 d9             	mov    %rbx,%rcx
    5e0d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5e11:	e8 8a fb ff ff       	call   59a0 <add_accept_request>
    5e16:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5e1b:	48 89 de             	mov    %rbx,%rsi
    5e1e:	8b 78 08             	mov    0x8(%rax),%edi
    5e21:	e8 1a f5 ff ff       	call   5340 <add_read_request>
    5e26:	4c 89 e7             	mov    %r12,%rdi
    5e29:	e8 d2 c4 ff ff       	call   2300 <free@plt>
    5e2e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5e33:	48 85 c0             	test   %rax,%rax
    5e36:	0f 85 14 01 00 00    	jne    5f50 <io_thread+0x510>
    5e3c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5e43:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5e4a:	8d 50 01             	lea    0x1(%rax),%edx
    5e4d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5e52:	8b 30                	mov    (%rax),%esi
    5e54:	f6 c1 02             	test   $0x2,%cl
    5e57:	74 00                	je     5e59 <io_thread+0x419>
    5e59:	89 d0                	mov    %edx,%eax
    5e5b:	29 f0                	sub    %esi,%eax
    5e5d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5e64:	0f 82 d0 c7 ff ff    	jb     263a <io_thread.cold+0x24>
    5e6a:	c1 e9 0a             	shr    $0xa,%ecx
    5e6d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    5e72:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5e76:	48 89 df             	mov    %rbx,%rdi
    5e79:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5e80:	83 e1 01             	and    $0x1,%ecx
    5e83:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5e8a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5e91:	d3 e0                	shl    %cl,%eax
    5e93:	8b 55 60             	mov    0x60(%rbp),%edx
    5e96:	48 c1 e0 06          	shl    $0x6,%rax
    5e9a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5ea2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5ea8:	89 50 04             	mov    %edx,0x4(%rax)
    5eab:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5eb3:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5eb7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5ebf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5ec7:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5ecb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5ecf:	e8 bc c4 ff ff       	call   2390 <io_uring_submit@plt>
    5ed4:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5ed8:	0f 84 3a fe ff ff    	je     5d18 <io_thread+0x2d8>
    5ede:	48 8d 3d 33 23 00 00 	lea    0x2333(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5ee5:	e8 46 c4 ff ff       	call   2330 <puts@plt>
    5eea:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5ef2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5efb:	0f 85 18 02 00 00    	jne    6119 <io_thread+0x6d9>
    5f01:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5f08:	31 c0                	xor    %eax,%eax
    5f0a:	5b                   	pop    %rbx
    5f0b:	5d                   	pop    %rbp
    5f0c:	41 5c                	pop    %r12
    5f0e:	41 5d                	pop    %r13
    5f10:	41 5e                	pop    %r14
    5f12:	41 5f                	pop    %r15
    5f14:	c3                   	ret
    5f15:	0f 1f 00             	nopl   (%rax)
    5f18:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    5f1d:	48 85 c0             	test   %rax,%rax
    5f20:	0f 84 6a fe ff ff    	je     5d90 <io_thread+0x350>
    5f26:	48 83 38 01          	cmpq   $0x1,(%rax)
    5f2a:	0f 84 68 01 00 00    	je     6098 <io_thread+0x658>
    5f30:	48 8d 3d a8 22 00 00 	lea    0x22a8(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5f37:	e8 f4 c3 ff ff       	call   2330 <puts@plt>
    5f3c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5f41:	4c 8b 22             	mov    (%rdx),%r12
    5f44:	e9 8b fe ff ff       	jmp    5dd4 <io_thread+0x394>
    5f49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5f50:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5f58:	8b 02                	mov    (%rdx),%eax
    5f5a:	83 c0 01             	add    $0x1,%eax
    5f5d:	89 02                	mov    %eax,(%rdx)
    5f5f:	e9 d8 fe ff ff       	jmp    5e3c <io_thread+0x3fc>
    5f64:	0f 1f 40 00          	nopl   0x0(%rax)
    5f68:	85 c0                	test   %eax,%eax
    5f6a:	75 74                	jne    5fe0 <io_thread+0x5a0>
    5f6c:	48 8b 0d ad 50 00 00 	mov    0x50ad(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5f73:	ba 0f 00 00 00       	mov    $0xf,%edx
    5f78:	be 01 00 00 00       	mov    $0x1,%esi
    5f7d:	48 8d 3d 84 22 00 00 	lea    0x2284(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    5f84:	e8 a7 c5 ff ff       	call   2530 <fwrite@plt>
    5f89:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5f8e:	e9 a0 fe ff ff       	jmp    5e33 <io_thread+0x3f3>
    5f93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5f98:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5f9d:	45 31 ff             	xor    %r15d,%r15d
    5fa0:	85 c0                	test   %eax,%eax
    5fa2:	7e 20                	jle    5fc4 <io_thread+0x584>
    5fa4:	0f 1f 40 00          	nopl   0x0(%rax)
    5fa8:	4c 89 f8             	mov    %r15,%rax
    5fab:	49 83 c7 01          	add    $0x1,%r15
    5faf:	48 c1 e0 04          	shl    $0x4,%rax
    5fb3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5fb8:	e8 43 c3 ff ff       	call   2300 <free@plt>
    5fbd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5fc2:	7f e4                	jg     5fa8 <io_thread+0x568>
    5fc4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5fc9:	e8 02 c4 ff ff       	call   23d0 <close@plt>
    5fce:	4c 89 e7             	mov    %r12,%rdi
    5fd1:	e8 2a c3 ff ff       	call   2300 <free@plt>
    5fd6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5fdb:	e9 53 fe ff ff       	jmp    5e33 <io_thread+0x3f3>
    5fe0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5fe5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5fea:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5ff2:	eb 11                	jmp    6005 <io_thread+0x5c5>
    5ff4:	0f 1f 40 00          	nopl   0x0(%rax)
    5ff8:	48 83 c0 01          	add    $0x1,%rax
    5ffc:	48 83 c2 01          	add    $0x1,%rdx
    6000:	48 39 c6             	cmp    %rax,%rsi
    6003:	74 4b                	je     6050 <io_thread+0x610>
    6005:	0f b6 0a             	movzbl (%rdx),%ecx
    6008:	88 08                	mov    %cl,(%rax)
    600a:	80 f9 0d             	cmp    $0xd,%cl
    600d:	75 e9                	jne    5ff8 <io_thread+0x5b8>
    600f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    6013:	75 e3                	jne    5ff8 <io_thread+0x5b8>
    6015:	c6 00 00             	movb   $0x0,(%rax)
    6018:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    601d:	48 89 da             	mov    %rbx,%rdx
    6020:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    6025:	e8 96 f7 ff ff       	call   57c0 <handle_http_method>
    602a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    602f:	e8 cc c2 ff ff       	call   2300 <free@plt>
    6034:	4c 89 e7             	mov    %r12,%rdi
    6037:	e8 c4 c2 ff ff       	call   2300 <free@plt>
    603c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    6041:	e9 ed fd ff ff       	jmp    5e33 <io_thread+0x3f3>
    6046:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6050:	48 8b 0d c9 4f 00 00 	mov    0x4fc9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6057:	ba 12 00 00 00       	mov    $0x12,%edx
    605c:	be 01 00 00 00       	mov    $0x1,%esi
    6061:	48 8d 3d f6 20 00 00 	lea    0x20f6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    6068:	e8 c3 c4 ff ff       	call   2530 <fwrite@plt>
    606d:	bf 01 00 00 00       	mov    $0x1,%edi
    6072:	e8 99 c4 ff ff       	call   2510 <exit@plt>
    6077:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    6080:	e9 ec fb ff ff       	jmp    5c71 <io_thread+0x231>
    6085:	0f 1f 00             	nopl   (%rax)
    6088:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    608d:	e9 94 fe ff ff       	jmp    5f26 <io_thread+0x4e6>
    6092:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6098:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    60a0:	48 8d 3d 24 21 00 00 	lea    0x2124(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    60a7:	8b 02                	mov    (%rdx),%eax
    60a9:	83 c0 01             	add    $0x1,%eax
    60ac:	89 02                	mov    %eax,(%rdx)
    60ae:	e8 7d c2 ff ff       	call   2330 <puts@plt>
    60b3:	e9 26 fe ff ff       	jmp    5ede <io_thread+0x49e>
    60b8:	f7 d8                	neg    %eax
    60ba:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    60bf:	89 c7                	mov    %eax,%edi
    60c1:	e8 aa c4 ff ff       	call   2570 <strerror@plt>
    60c6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    60cb:	be 01 00 00 00       	mov    $0x1,%esi
    60d0:	48 8b 3d 49 4f 00 00 	mov    0x4f49(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    60d7:	48 89 c1             	mov    %rax,%rcx
    60da:	48 8d 15 07 25 00 00 	lea    0x2507(%rip),%rdx        # 85e8 <_IO_stdin_used+0x5e8>
    60e1:	31 c0                	xor    %eax,%eax
    60e3:	e8 58 c4 ff ff       	call   2540 <__fprintf_chk@plt>
    60e8:	bf 01 00 00 00       	mov    $0x1,%edi
    60ed:	e8 1e c4 ff ff       	call   2510 <exit@plt>
    60f2:	48 8b 0d 27 4f 00 00 	mov    0x4f27(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    60f9:	ba 28 00 00 00       	mov    $0x28,%edx
    60fe:	be 01 00 00 00       	mov    $0x1,%esi
    6103:	48 8d 3d ae 24 00 00 	lea    0x24ae(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    610a:	e8 21 c4 ff ff       	call   2530 <fwrite@plt>
    610f:	bf 01 00 00 00       	mov    $0x1,%edi
    6114:	e8 f7 c3 ff ff       	call   2510 <exit@plt>
    6119:	e8 62 c2 ff ff       	call   2380 <__stack_chk_fail@plt>
    611e:	66 90                	xchg   %ax,%ax

0000000000006120 <barriered_work_ingest>:
    6120:	f3 0f 1e fa          	endbr64
    6124:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    612b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    6131:	85 c9                	test   %ecx,%ecx
    6133:	0f 8e ea 00 00 00    	jle    6223 <barriered_work_ingest+0x103>
    6139:	41 56                	push   %r14
    613b:	41 55                	push   %r13
    613d:	45 31 ed             	xor    %r13d,%r13d
    6140:	41 54                	push   %r12
    6142:	49 89 fc             	mov    %rdi,%r12
    6145:	55                   	push   %rbp
    6146:	53                   	push   %rbx
    6147:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    614b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6150:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    6154:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    615c:	31 db                	xor    %ebx,%ebx
    615e:	8b 10                	mov    (%rax),%edx
    6160:	85 d2                	test   %edx,%edx
    6162:	7e 26                	jle    618a <barriered_work_ingest+0x6a>
    6164:	48 8b 48 08          	mov    0x8(%rax),%rcx
    6168:	48 89 dd             	mov    %rbx,%rbp
    616b:	48 c1 e5 08          	shl    $0x8,%rbp
    616f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    6173:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    617a:	74 24                	je     61a0 <barriered_work_ingest+0x80>
    617c:	48 83 c3 01          	add    $0x1,%rbx
    6180:	39 da                	cmp    %ebx,%edx
    6182:	7f e4                	jg     6168 <barriered_work_ingest+0x48>
    6184:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    618a:	49 83 c5 01          	add    $0x1,%r13
    618e:	44 39 e9             	cmp    %r13d,%ecx
    6191:	7f bd                	jg     6150 <barriered_work_ingest+0x30>
    6193:	5b                   	pop    %rbx
    6194:	31 c0                	xor    %eax,%eax
    6196:	5d                   	pop    %rbp
    6197:	41 5c                	pop    %r12
    6199:	41 5d                	pop    %r13
    619b:	41 5e                	pop    %r14
    619d:	c3                   	ret
    619e:	66 90                	xchg   %ax,%ax
    61a0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
    61a9:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    61b0:	bf 04 00 00 00       	mov    $0x4,%edi
    61b5:	48 c1 e6 05          	shl    $0x5,%rsi
    61b9:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    61c0:	48 83 c6 10          	add    $0x10,%rsi
    61c4:	e8 87 c1 ff ff       	call   2350 <clock_gettime@plt>
    61c9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    61d1:	48 8b 40 50          	mov    0x50(%rax),%rax
    61d5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    61d9:	48 03 68 08          	add    0x8(%rax),%rbp
    61dd:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
    61e7:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    61ed:	83 c0 01             	add    $0x1,%eax
    61f0:	99                   	cltd
    61f1:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    61f7:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
    61fd:	0f ae f8             	sfence
    6200:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    6208:	48 83 c3 01          	add    $0x1,%rbx
    620c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    6210:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    6214:	8b 10                	mov    (%rax),%edx
    6216:	39 da                	cmp    %ebx,%edx
    6218:	0f 8f 46 ff ff ff    	jg     6164 <barriered_work_ingest+0x44>
    621e:	e9 61 ff ff ff       	jmp    6184 <barriered_work_ingest+0x64>
    6223:	31 c0                	xor    %eax,%eax
    6225:	c3                   	ret
    6226:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006230 <barriered_thread>:
    6230:	f3 0f 1e fa          	endbr64
    6234:	41 56                	push   %r14
    6236:	41 55                	push   %r13
    6238:	41 54                	push   %r12
    623a:	45 31 e4             	xor    %r12d,%r12d
    623d:	55                   	push   %rbp
    623e:	31 ed                	xor    %ebp,%ebp
    6240:	53                   	push   %rbx
    6241:	48 89 fb             	mov    %rdi,%rbx
    6244:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6248:	0f 85 74 02 00 00    	jne    64c2 <barriered_thread+0x292>
    624e:	8b 43 40             	mov    0x40(%rbx),%eax
    6251:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6258:	41 39 c4             	cmp    %eax,%r12d
    625b:	0f 8d 6f 01 00 00    	jge    63d0 <barriered_thread+0x1a0>
    6261:	49 63 fc             	movslq %r12d,%rdi
    6264:	48 c1 e7 09          	shl    $0x9,%rdi
    6268:	49 89 fd             	mov    %rdi,%r13
    626b:	eb 32                	jmp    629f <barriered_thread+0x6f>
    626d:	0f 1f 00             	nopl   (%rax)
    6270:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6274:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6278:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    627c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6280:	4c 01 ef             	add    %r13,%rdi
    6283:	e8 98 fe ff ff       	call   6120 <barriered_work_ingest>
    6288:	8b 43 40             	mov    0x40(%rbx),%eax
    628b:	41 83 c4 01          	add    $0x1,%r12d
    628f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    6296:	44 39 e0             	cmp    %r12d,%eax
    6299:	0f 8e 19 02 00 00    	jle    64b8 <barriered_thread+0x288>
    629f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    62a3:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    62a7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    62ae:	75 c0                	jne    6270 <barriered_thread+0x40>
    62b0:	44 8b 43 28          	mov    0x28(%rbx),%r8d
    62b4:	83 e8 01             	sub    $0x1,%eax
    62b7:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    62bc:	45 85 e4             	test   %r12d,%r12d
    62bf:	0f 4f c1             	cmovg  %ecx,%eax
    62c2:	45 85 c0             	test   %r8d,%r8d
    62c5:	0f 8e 2d 01 00 00    	jle    63f8 <barriered_thread+0x1c8>
    62cb:	48 63 c8             	movslq %eax,%rcx
    62ce:	48 8b 43 18          	mov    0x18(%rbx),%rax
    62d2:	49 63 d0             	movslq %r8d,%rdx
    62d5:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
    62db:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    62e2:	48 c1 e1 09          	shl    $0x9,%rcx
    62e6:	45 31 d2             	xor    %r10d,%r10d
    62e9:	45 31 f6             	xor    %r14d,%r14d
    62ec:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    62f0:	48 8b 10             	mov    (%rax),%rdx
    62f3:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    62f7:	49 01 cb             	add    %rcx,%r11
    62fa:	4c 89 da             	mov    %r11,%rdx
    62fd:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6304:	75 04                	jne    630a <barriered_thread+0xda>
    6306:	41 83 c6 01          	add    $0x1,%r14d
    630a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    6310:	75 04                	jne    6316 <barriered_thread+0xe6>
    6312:	41 83 c2 01          	add    $0x1,%r10d
    6316:	48 83 c0 08          	add    $0x8,%rax
    631a:	48 39 c6             	cmp    %rax,%rsi
    631d:	75 d1                	jne    62f0 <barriered_thread+0xc0>
    631f:	45 85 d2             	test   %r10d,%r10d
    6322:	0f 84 c0 00 00 00    	je     63e8 <barriered_thread+0x1b8>
    6328:	45 39 d0             	cmp    %r10d,%r8d
    632b:	0f 84 b7 00 00 00    	je     63e8 <barriered_thread+0x1b8>
    6331:	45 85 f6             	test   %r14d,%r14d
    6334:	74 0a                	je     6340 <barriered_thread+0x110>
    6336:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    633a:	0f 85 ae 01 00 00    	jne    64ee <barriered_thread+0x2be>
    6340:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6344:	4c 01 ea             	add    %r13,%rdx
    6347:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
    634e:	45 85 e4             	test   %r12d,%r12d
    6351:	75 14                	jne    6367 <barriered_thread+0x137>
    6353:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    635a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    6361:	0f 8c 69 01 00 00    	jl     64d0 <barriered_thread+0x2a0>
    6367:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    636b:	48 8b 43 18          	mov    0x18(%rbx),%rax
    636f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
    6379:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    637d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6381:	4c 01 ef             	add    %r13,%rdi
    6384:	ff 92 18 01 00 00    	call   *0x118(%rdx)
    638a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    638e:	4c 01 e8             	add    %r13,%rax
    6391:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
    6398:	8b 43 40             	mov    0x40(%rbx),%eax
    639b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
    63a0:	83 e8 01             	sub    $0x1,%eax
    63a3:	44 39 e0             	cmp    %r12d,%eax
    63a6:	0f 84 a4 00 00 00    	je     6450 <barriered_thread+0x220>
    63ac:	0f ae f8             	sfence
    63af:	85 ed                	test   %ebp,%ebp
    63b1:	0f 84 d1 00 00 00    	je     6488 <barriered_thread+0x258>
    63b7:	bd 01 00 00 00       	mov    $0x1,%ebp
    63bc:	e9 c7 fe ff ff       	jmp    6288 <barriered_thread+0x58>
    63c1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    63c5:	0f 85 f7 00 00 00    	jne    64c2 <barriered_thread+0x292>
    63cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    63d0:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    63d8:	85 c0                	test   %eax,%eax
    63da:	7e e5                	jle    63c1 <barriered_thread+0x191>
    63dc:	45 31 e4             	xor    %r12d,%r12d
    63df:	e9 7d fe ff ff       	jmp    6261 <barriered_thread+0x31>
    63e4:	0f 1f 40 00          	nopl   0x0(%rax)
    63e8:	83 fd 01             	cmp    $0x1,%ebp
    63eb:	74 1b                	je     6408 <barriered_thread+0x1d8>
    63ed:	31 ed                	xor    %ebp,%ebp
    63ef:	e9 3d ff ff ff       	jmp    6331 <barriered_thread+0x101>
    63f4:	0f 1f 40 00          	nopl   0x0(%rax)
    63f8:	83 fd 01             	cmp    $0x1,%ebp
    63fb:	0f 85 43 ff ff ff    	jne    6344 <barriered_thread+0x114>
    6401:	45 31 f6             	xor    %r14d,%r14d
    6404:	0f 1f 40 00          	nopl   0x0(%rax)
    6408:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    640f:	bf 04 00 00 00       	mov    $0x4,%edi
    6414:	31 ed                	xor    %ebp,%ebp
    6416:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    641a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6421:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    6426:	e8 25 bf ff ff       	call   2350 <clock_gettime@plt>
    642b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6432:	48 83 c0 01          	add    $0x1,%rax
    6436:	48 99                	cqto
    6438:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    643f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
    6446:	e9 e6 fe ff ff       	jmp    6331 <barriered_thread+0x101>
    644b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6450:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6457:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    645e:	0f 8d 48 ff ff ff    	jge    63ac <barriered_thread+0x17c>
    6464:	48 c1 e6 04          	shl    $0x4,%rsi
    6468:	bf 04 00 00 00       	mov    $0x4,%edi
    646d:	48 03 73 70          	add    0x70(%rbx),%rsi
    6471:	e8 da be ff ff       	call   2350 <clock_gettime@plt>
    6476:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    647e:	e9 29 ff ff ff       	jmp    63ac <barriered_thread+0x17c>
    6483:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6488:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    648f:	bf 04 00 00 00       	mov    $0x4,%edi
    6494:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6498:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    649f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    64a3:	44 89 66 20          	mov    %r12d,0x20(%rsi)
    64a7:	e8 a4 be ff ff       	call   2350 <clock_gettime@plt>
    64ac:	e9 06 ff ff ff       	jmp    63b7 <barriered_thread+0x187>
    64b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    64b8:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    64bc:	0f 84 96 fd ff ff    	je     6258 <barriered_thread+0x28>
    64c2:	5b                   	pop    %rbx
    64c3:	31 c0                	xor    %eax,%eax
    64c5:	5d                   	pop    %rbp
    64c6:	41 5c                	pop    %r12
    64c8:	41 5d                	pop    %r13
    64ca:	41 5e                	pop    %r14
    64cc:	c3                   	ret
    64cd:	0f 1f 00             	nopl   (%rax)
    64d0:	48 c1 e6 04          	shl    $0x4,%rsi
    64d4:	bf 04 00 00 00       	mov    $0x4,%edi
    64d9:	48 03 73 68          	add    0x68(%rbx),%rsi
    64dd:	e8 6e be ff ff       	call   2350 <clock_gettime@plt>
    64e2:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    64e6:	4c 01 ea             	add    %r13,%rdx
    64e9:	e9 79 fe ff ff       	jmp    6367 <barriered_thread+0x137>
    64ee:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    64f2:	48 8b 43 18          	mov    0x18(%rbx),%rax
    64f6:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    64fa:	48 8b 78 38          	mov    0x38(%rax),%rdi
    64fe:	4c 01 ef             	add    %r13,%rdi
    6501:	e8 1a fc ff ff       	call   6120 <barriered_work_ingest>
    6506:	e9 39 fd ff ff       	jmp    6244 <barriered_thread+0x14>
    650b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006510 <receive>:
    6510:	f3 0f 1e fa          	endbr64
    6514:	41 56                	push   %r14
    6516:	41 55                	push   %r13
    6518:	41 54                	push   %r12
    651a:	55                   	push   %rbp
    651b:	53                   	push   %rbx
    651c:	4c 63 a7 40 01 00 00 	movslq 0x140(%rdi),%r12
    6523:	45 85 e4             	test   %r12d,%r12d
    6526:	0f 8e 27 01 00 00    	jle    6653 <receive+0x143>
    652c:	4c 8b b7 28 01 00 00 	mov    0x128(%rdi),%r14
    6533:	48 89 fe             	mov    %rdi,%rsi
    6536:	31 db                	xor    %ebx,%ebx
    6538:	49 63 6e 08          	movslq 0x8(%r14),%rbp
    653c:	49 89 ed             	mov    %rbp,%r13
    653f:	90                   	nop
    6540:	41 39 dd             	cmp    %ebx,%r13d
    6543:	0f 84 fd 00 00 00    	je     6646 <receive+0x136>
    6549:	48 89 d8             	mov    %rbx,%rax
    654c:	48 c1 e0 08          	shl    $0x8,%rax
    6550:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    6557:	48 8b 10             	mov    (%rax),%rdx
    655a:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    6560:	83 f8 01             	cmp    $0x1,%eax
    6563:	74 11                	je     6576 <receive+0x66>
    6565:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    656c:	75 08                	jne    6576 <receive+0x66>
    656e:	85 c0                	test   %eax,%eax
    6570:	0f 84 d0 00 00 00    	je     6646 <receive+0x136>
    6576:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    657d:	48 85 ff             	test   %rdi,%rdi
    6580:	0f 8e a2 00 00 00    	jle    6628 <receive+0x118>
    6586:	4c 8b 8e 80 01 00 00 	mov    0x180(%rsi),%r9
    658d:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    6594:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    6598:	4c 8b 1a             	mov    (%rdx),%r11
    659b:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    659f:	49 01 f9             	add    %rdi,%r9
    65a2:	49 01 f8             	add    %rdi,%r8
    65a5:	48 03 ba 00 04 00 00 	add    0x400(%rdx),%rdi
    65ac:	eb 08                	jmp    65b6 <receive+0xa6>
    65ae:	66 90                	xchg   %ax,%ax
    65b0:	48 83 e8 01          	sub    $0x1,%rax
    65b4:	72 72                	jb     6628 <receive+0x118>
    65b6:	4c 89 c9             	mov    %r9,%rcx
    65b9:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
    65c0:	48 29 c1             	sub    %rax,%rcx
    65c3:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
    65ca:	4c 89 c1             	mov    %r8,%rcx
    65cd:	48 29 c1             	sub    %rax,%rcx
    65d0:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
    65d7:	48 89 f9             	mov    %rdi,%rcx
    65da:	48 29 c1             	sub    %rax,%rcx
    65dd:	48 89 8a 00 04 00 00 	mov    %rcx,0x400(%rdx)
    65e4:	48 63 c8             	movslq %eax,%rcx
    65e7:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
    65eb:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    65ef:	75 bf                	jne    65b0 <receive+0xa0>
    65f1:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    65f5:	75 b9                	jne    65b0 <receive+0xa0>
    65f7:	49 63 46 04          	movslq 0x4(%r14),%rax
    65fb:	31 c9                	xor    %ecx,%ecx
    65fd:	bf 01 00 00 00       	mov    $0x1,%edi
    6602:	ba 01 00 00 00       	mov    $0x1,%edx
    6607:	48 8d 35 02 20 00 00 	lea    0x2002(%rip),%rsi        # 8610 <_IO_stdin_used+0x610>
    660e:	48 39 e8             	cmp    %rbp,%rax
    6611:	0f 94 c1             	sete   %cl
    6614:	31 c0                	xor    %eax,%eax
    6616:	e8 95 be ff ff       	call   24b0 <__printf_chk@plt>
    661b:	bf 01 00 00 00       	mov    $0x1,%edi
    6620:	e8 eb be ff ff       	call   2510 <exit@plt>
    6625:	0f 1f 00             	nopl   (%rax)
    6628:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
    6632:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
    663c:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
    6646:	48 83 c3 01          	add    $0x1,%rbx
    664a:	49 39 dc             	cmp    %rbx,%r12
    664d:	0f 85 ed fe ff ff    	jne    6540 <receive+0x30>
    6653:	0f ae f8             	sfence
    6656:	31 c0                	xor    %eax,%eax
    6658:	5b                   	pop    %rbx
    6659:	5d                   	pop    %rbp
    665a:	41 5c                	pop    %r12
    665c:	41 5d                	pop    %r13
    665e:	41 5e                	pop    %r14
    6660:	c3                   	ret
    6661:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    666c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006670 <sendm>:
    6670:	f3 0f 1e fa          	endbr64
    6674:	41 57                	push   %r15
    6676:	48 89 f9             	mov    %rdi,%rcx
    6679:	41 56                	push   %r14
    667b:	41 55                	push   %r13
    667d:	41 54                	push   %r12
    667f:	55                   	push   %rbp
    6680:	53                   	push   %rbx
    6681:	48 63 bf 40 01 00 00 	movslq 0x140(%rdi),%rdi
    6688:	85 ff                	test   %edi,%edi
    668a:	7e 67                	jle    66f3 <sendm+0x83>
    668c:	48 8b 81 28 01 00 00 	mov    0x128(%rcx),%rax
    6693:	44 8b 48 08          	mov    0x8(%rax),%r9d
    6697:	31 c0                	xor    %eax,%eax
    6699:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    66a0:	41 39 c1             	cmp    %eax,%r9d
    66a3:	74 45                	je     66ea <sendm+0x7a>
    66a5:	48 89 c2             	mov    %rax,%rdx
    66a8:	48 c1 e2 08          	shl    $0x8,%rdx
    66ac:	48 03 91 70 01 00 00 	add    0x170(%rcx),%rdx
    66b3:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    66ba:	48 8b b2 80 00 00 00 	mov    0x80(%rdx),%rsi
    66c1:	48 85 f6             	test   %rsi,%rsi
    66c4:	7f 24                	jg     66ea <sendm+0x7a>
    66c6:	44 8b 82 00 01 00 00 	mov    0x100(%rdx),%r8d
    66cd:	41 83 f8 01          	cmp    $0x1,%r8d
    66d1:	74 0e                	je     66e1 <sendm+0x71>
    66d3:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    66da:	75 05                	jne    66e1 <sendm+0x71>
    66dc:	45 85 c0             	test   %r8d,%r8d
    66df:	74 09                	je     66ea <sendm+0x7a>
    66e1:	83 b9 88 01 00 00 01 	cmpl   $0x1,0x188(%rcx)
    66e8:	74 1e                	je     6708 <sendm+0x98>
    66ea:	48 83 c0 01          	add    $0x1,%rax
    66ee:	48 39 c7             	cmp    %rax,%rdi
    66f1:	75 ad                	jne    66a0 <sendm+0x30>
    66f3:	0f ae f8             	sfence
    66f6:	31 c0                	xor    %eax,%eax
    66f8:	5b                   	pop    %rbx
    66f9:	5d                   	pop    %rbp
    66fa:	41 5c                	pop    %r12
    66fc:	41 5d                	pop    %r13
    66fe:	41 5e                	pop    %r14
    6700:	41 5f                	pop    %r15
    6702:	c3                   	ret
    6703:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6708:	48 63 aa 88 00 00 00 	movslq 0x88(%rdx),%rbp
    670f:	48 39 ee             	cmp    %rbp,%rsi
    6712:	0f 8d a5 00 00 00    	jge    67bd <sendm+0x14d>
    6718:	48 8b 99 08 01 00 00 	mov    0x108(%rcx),%rbx
    671f:	4c 8b aa 80 03 00 00 	mov    0x380(%rdx),%r13
    6726:	4c 8b 1a             	mov    (%rdx),%r11
    6729:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    672e:	48 89 eb             	mov    %rbp,%rbx
    6731:	48 29 f3             	sub    %rsi,%rbx
    6734:	4c 8d 43 ff          	lea    -0x1(%rbx),%r8
    6738:	49 83 f8 02          	cmp    $0x2,%r8
    673c:	0f 86 0e 01 00 00    	jbe    6850 <sendm+0x1e0>
    6742:	4c 8d 14 ed 00 00 00 00 	lea    0x0(,%rbp,8),%r10
    674a:	4c 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r8
    6752:	4f 8d 34 13          	lea    (%r11,%r10,1),%r14
    6756:	4c 8d b9 90 01 00 00 	lea    0x190(%rcx),%r15
    675d:	4f 8d 24 03          	lea    (%r11,%r8,1),%r12
    6761:	4d 39 f7             	cmp    %r14,%r15
    6764:	73 7a                	jae    67e0 <sendm+0x170>
    6766:	4c 8d b1 98 01 00 00 	lea    0x198(%rcx),%r14
    676d:	4d 39 f4             	cmp    %r14,%r12
    6770:	73 6e                	jae    67e0 <sendm+0x170>
    6772:	4d 01 d8             	add    %r11,%r8
    6775:	4b 8d 34 13          	lea    (%r11,%r10,1),%rsi
    6779:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6780:	4c 8b 91 90 01 00 00 	mov    0x190(%rcx),%r10
    6787:	49 83 c0 08          	add    $0x8,%r8
    678b:	4d 89 50 f8          	mov    %r10,-0x8(%r8)
    678f:	4c 39 c6             	cmp    %r8,%rsi
    6792:	75 ec                	jne    6780 <sendm+0x110>
    6794:	0f 1f 40 00          	nopl   0x0(%rax)
    6798:	48 8b 74 24 f0       	mov    -0x10(%rsp),%rsi
    679d:	48 01 de             	add    %rbx,%rsi
    67a0:	4c 01 eb             	add    %r13,%rbx
    67a3:	48 89 b1 08 01 00 00 	mov    %rsi,0x108(%rcx)
    67aa:	48 89 9a 80 03 00 00 	mov    %rbx,0x380(%rdx)
    67b1:	48 89 aa 80 00 00 00 	mov    %rbp,0x80(%rdx)
    67b8:	4d 89 54 eb f8       	mov    %r10,-0x8(%r11,%rbp,8)
    67bd:	c7 82 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdx)
    67c7:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
    67d1:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
    67db:	e9 0a ff ff ff       	jmp    66ea <sendm+0x7a>
    67e0:	49 89 de             	mov    %rbx,%r14
    67e3:	4c 8b 91 90 01 00 00 	mov    0x190(%rcx),%r10
    67ea:	4d 89 e0             	mov    %r12,%r8
    67ed:	49 d1 ee             	shr    %r14
    67f0:	49 c1 e6 04          	shl    $0x4,%r14
    67f4:	66 49 0f 6e c2       	movq   %r10,%xmm0
    67f9:	4f 8d 3c 34          	lea    (%r12,%r14,1),%r15
    67fd:	41 83 e6 10          	and    $0x10,%r14d
    6801:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    6805:	74 11                	je     6818 <sendm+0x1a8>
    6807:	49 83 c0 10          	add    $0x10,%r8
    680b:	41 0f 11 04 24       	movups %xmm0,(%r12)
    6810:	4d 39 f8             	cmp    %r15,%r8
    6813:	74 15                	je     682a <sendm+0x1ba>
    6815:	0f 1f 00             	nopl   (%rax)
    6818:	41 0f 11 00          	movups %xmm0,(%r8)
    681c:	49 83 c0 20          	add    $0x20,%r8
    6820:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
    6825:	4d 39 f8             	cmp    %r15,%r8
    6828:	75 ee                	jne    6818 <sendm+0x1a8>
    682a:	49 89 d8             	mov    %rbx,%r8
    682d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    6831:	4c 01 c6             	add    %r8,%rsi
    6834:	f6 c3 01             	test   $0x1,%bl
    6837:	0f 84 5b ff ff ff    	je     6798 <sendm+0x128>
    683d:	4c 8b 91 90 01 00 00 	mov    0x190(%rcx),%r10
    6844:	4d 89 14 f3          	mov    %r10,(%r11,%rsi,8)
    6848:	e9 4b ff ff ff       	jmp    6798 <sendm+0x128>
    684d:	0f 1f 00             	nopl   (%rax)
    6850:	4c 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r8
    6858:	4c 8d 14 ed 00 00 00 00 	lea    0x0(,%rbp,8),%r10
    6860:	e9 0d ff ff ff       	jmp    6772 <sendm+0x102>
    6865:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000006870 <mailboxkind>:
    6870:	f3 0f 1e fa          	endbr64
    6874:	85 f6                	test   %esi,%esi
    6876:	74 18                	je     6890 <mailboxkind+0x20>
    6878:	31 c0                	xor    %eax,%eax
    687a:	83 fe 01             	cmp    $0x1,%esi
    687d:	74 01                	je     6880 <mailboxkind+0x10>
    687f:	c3                   	ret
    6880:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
    6887:	c3                   	ret
    6888:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6890:	48 8b 07             	mov    (%rdi),%rax
    6893:	c3                   	ret
    6894:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    689f:	90                   	nop

00000000000068a0 <setmailboxkind>:
    68a0:	f3 0f 1e fa          	endbr64
    68a4:	85 d2                	test   %edx,%edx
    68a6:	75 08                	jne    68b0 <setmailboxkind+0x10>
    68a8:	48 89 37             	mov    %rsi,(%rdi)
    68ab:	31 c0                	xor    %eax,%eax
    68ad:	c3                   	ret
    68ae:	66 90                	xchg   %ax,%ax
    68b0:	83 fa 01             	cmp    $0x1,%edx
    68b3:	74 13                	je     68c8 <setmailboxkind+0x28>
    68b5:	83 fa 02             	cmp    $0x2,%edx
    68b8:	75 1e                	jne    68d8 <setmailboxkind+0x38>
    68ba:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
    68c1:	31 c0                	xor    %eax,%eax
    68c3:	c3                   	ret
    68c4:	0f 1f 40 00          	nopl   0x0(%rax)
    68c8:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
    68cf:	31 c0                	xor    %eax,%eax
    68d1:	c3                   	ret
    68d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    68d8:	83 fa 03             	cmp    $0x3,%edx
    68db:	75 ce                	jne    68ab <setmailboxkind+0xb>
    68dd:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
    68e4:	31 c0                	xor    %eax,%eax
    68e6:	c3                   	ret
    68e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000068f0 <fswap>:
    68f0:	f3 0f 1e fa          	endbr64
    68f4:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    68fb:	8b 97 9c 01 00 00    	mov    0x19c(%rdi),%edx
    6901:	44 8b 97 30 01 00 00 	mov    0x130(%rdi),%r10d
    6908:	48 63 4f 04          	movslq 0x4(%rdi),%rcx
    690c:	8b 86 c4 00 00 00    	mov    0xc4(%rsi),%eax
    6912:	0f af d0             	imul   %eax,%edx
    6915:	41 01 d2             	add    %edx,%r10d
    6918:	85 c0                	test   %eax,%eax
    691a:	0f 8e 1b 01 00 00    	jle    6a3b <fswap+0x14b>
    6920:	4d 63 d2             	movslq %r10d,%r10
    6923:	41 56                	push   %r14
    6925:	48 63 d2             	movslq %edx,%rdx
    6928:	48 c1 e1 09          	shl    $0x9,%rcx
    692c:	41 55                	push   %r13
    692e:	4c 63 d8             	movslq %eax,%r11
    6931:	41 54                	push   %r12
    6933:	49 01 d3             	add    %rdx,%r11
    6936:	55                   	push   %rbp
    6937:	49 c1 e3 08          	shl    $0x8,%r11
    693b:	53                   	push   %rbx
    693c:	48 8b 76 20          	mov    0x20(%rsi),%rsi
    6940:	44 8b 87 34 01 00 00 	mov    0x134(%rdi),%r8d
    6947:	4b 8d 3c 52          	lea    (%r10,%r10,2),%rdi
    694b:	49 c1 e2 08          	shl    $0x8,%r10
    694f:	48 8d 3c ff          	lea    (%rdi,%rdi,8),%rdi
    6953:	48 8b 5c fe 38       	mov    0x38(%rsi,%rdi,8),%rbx
    6958:	48 8b ac 0b 70 01 00 00 	mov    0x170(%rbx,%rcx,1),%rbp
    6960:	48 8d 0c 52          	lea    (%rdx,%rdx,2),%rcx
    6964:	48 8d 0c c9          	lea    (%rcx,%rcx,8),%rcx
    6968:	4c 8d 0c ce          	lea    (%rsi,%rcx,8),%r9
    696c:	48 89 d6             	mov    %rdx,%rsi
    696f:	48 c1 e6 08          	shl    $0x8,%rsi
    6973:	eb 1a                	jmp    698f <fswap+0x9f>
    6975:	0f 1f 00             	nopl   (%rax)
    6978:	48 81 c6 00 01 00 00 	add    $0x100,%rsi
    697f:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    6986:	49 39 f3             	cmp    %rsi,%r11
    6989:	0f 84 a1 00 00 00    	je     6a30 <fswap+0x140>
    698f:	83 bc 35 b0 00 00 00 01 	cmpl   $0x1,0xb0(%rbp,%rsi,1)
    6997:	75 df                	jne    6978 <fswap+0x88>
    6999:	49 8b 79 38          	mov    0x38(%r9),%rdi
    699d:	45 85 c0             	test   %r8d,%r8d
    69a0:	7e d6                	jle    6978 <fswap+0x88>
    69a2:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    69a9:	31 c9                	xor    %ecx,%ecx
    69ab:	eb 58                	jmp    6a05 <fswap+0x115>
    69ad:	0f 1f 00             	nopl   (%rax)
    69b0:	48 63 d2             	movslq %edx,%rdx
    69b3:	48 c1 e2 09          	shl    $0x9,%rdx
    69b7:	4c 8b ac 13 70 01 00 00 	mov    0x170(%rbx,%rdx,1),%r13
    69bf:	49 01 f5             	add    %rsi,%r13
    69c2:	4c 89 ea             	mov    %r13,%rdx
    69c5:	4d 8b 6d 00          	mov    0x0(%r13),%r13
    69c9:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    69d1:	75 22                	jne    69f5 <fswap+0x105>
    69d3:	4c 8b b0 80 00 00 00 	mov    0x80(%rax),%r14
    69da:	4c 89 32             	mov    %r14,(%rdx)
    69dd:	4c 8b b2 80 00 00 00 	mov    0x80(%rdx),%r14
    69e4:	4c 89 a8 80 00 00 00 	mov    %r13,0x80(%rax)
    69eb:	4c 89 30             	mov    %r14,(%rax)
    69ee:	4c 89 a2 80 00 00 00 	mov    %r12,0x80(%rdx)
    69f5:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    69fc:	41 39 c8             	cmp    %ecx,%r8d
    69ff:	0f 84 73 ff ff ff    	je     6978 <fswap+0x88>
    6a05:	83 c1 01             	add    $0x1,%ecx
    6a08:	89 c8                	mov    %ecx,%eax
    6a0a:	99                   	cltd
    6a0b:	41 f7 f8             	idiv   %r8d
    6a0e:	48 8b 07             	mov    (%rdi),%rax
    6a11:	4c 01 d0             	add    %r10,%rax
    6a14:	4c 8b 20             	mov    (%rax),%r12
    6a17:	49 83 bc 24 80 00 00 00 00 	cmpq   $0x0,0x80(%r12)
    6a20:	74 8e                	je     69b0 <fswap+0xc0>
    6a22:	e9 51 ff ff ff       	jmp    6978 <fswap+0x88>
    6a27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    6a30:	5b                   	pop    %rbx
    6a31:	31 c0                	xor    %eax,%eax
    6a33:	5d                   	pop    %rbp
    6a34:	41 5c                	pop    %r12
    6a36:	41 5d                	pop    %r13
    6a38:	41 5e                	pop    %r14
    6a3a:	c3                   	ret
    6a3b:	31 c0                	xor    %eax,%eax
    6a3d:	c3                   	ret
    6a3e:	66 90                	xchg   %ax,%ax

0000000000006a40 <barriered_work>:
    6a40:	f3 0f 1e fa          	endbr64
    6a44:	41 57                	push   %r15
    6a46:	41 56                	push   %r14
    6a48:	41 55                	push   %r13
    6a4a:	41 54                	push   %r12
    6a4c:	55                   	push   %rbp
    6a4d:	53                   	push   %rbx
    6a4e:	48 89 fb             	mov    %rdi,%rbx
    6a51:	48 83 ec 58          	sub    $0x58,%rsp
    6a55:	44 8b 67 04          	mov    0x4(%rdi),%r12d
    6a59:	44 39 a7 30 01 00 00 	cmp    %r12d,0x130(%rdi)
    6a60:	74 5e                	je     6ac0 <barriered_work+0x80>
    6a62:	e8 a9 fa ff ff       	call   6510 <receive>
    6a67:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6a6e:	75 14                	jne    6a84 <barriered_work+0x44>
    6a70:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    6a78:	0f ae f8             	sfence
    6a7b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6a82:	74 ec                	je     6a70 <barriered_work+0x30>
    6a84:	48 89 df             	mov    %rbx,%rdi
    6a87:	e8 e4 fb ff ff       	call   6670 <sendm>
    6a8c:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6a92:	83 e8 01             	sub    $0x1,%eax
    6a95:	44 39 e0             	cmp    %r12d,%eax
    6a98:	0f 84 7d 03 00 00    	je     6e1b <barriered_work+0x3db>
    6a9e:	c7 83 a0 01 00 00 00 00 00 00 	movl   $0x0,0x1a0(%rbx)
    6aa8:	0f ae f8             	sfence
    6aab:	48 83 c4 58          	add    $0x58,%rsp
    6aaf:	31 c0                	xor    %eax,%eax
    6ab1:	5b                   	pop    %rbx
    6ab2:	5d                   	pop    %rbp
    6ab3:	41 5c                	pop    %r12
    6ab5:	41 5d                	pop    %r13
    6ab7:	41 5e                	pop    %r14
    6ab9:	41 5f                	pop    %r15
    6abb:	c3                   	ret
    6abc:	0f 1f 40 00          	nopl   0x0(%rax)
    6ac0:	e8 4b fa ff ff       	call   6510 <receive>
    6ac5:	48 63 93 40 01 00 00 	movslq 0x140(%rbx),%rdx
    6acc:	85 d2                	test   %edx,%edx
    6ace:	0f 8e 5f 02 00 00    	jle    6d33 <barriered_work+0x2f3>
    6ad4:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6ada:	4c 8b bb 28 01 00 00 	mov    0x128(%rbx),%r15
    6ae1:	31 f6                	xor    %esi,%esi
    6ae3:	49 89 d2             	mov    %rdx,%r10
    6ae6:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    6aee:	89 44 24 1c          	mov    %eax,0x1c(%rsp)
    6af2:	45 8b 77 08          	mov    0x8(%r15),%r14d
    6af6:	49 63 c4             	movslq %r12d,%rax
    6af9:	48 c1 e0 09          	shl    $0x9,%rax
    6afd:	49 89 c5             	mov    %rax,%r13
    6b00:	49 63 c6             	movslq %r14d,%rax
    6b03:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
    6b07:	48 c1 e0 08          	shl    $0x8,%rax
    6b0b:	48 8d 0c c9          	lea    (%rcx,%rcx,8),%rcx
    6b0f:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    6b14:	48 8d 2c cd 00 00 00 00 	lea    0x0(,%rcx,8),%rbp
    6b1c:	44 89 e1             	mov    %r12d,%ecx
    6b1f:	eb 20                	jmp    6b41 <barriered_work+0x101>
    6b21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6b28:	48 83 04 24 01       	addq   $0x1,(%rsp)
    6b2d:	48 8b 04 24          	mov    (%rsp),%rax
    6b31:	48 81 c6 d8 00 00 00 	add    $0xd8,%rsi
    6b38:	49 39 c2             	cmp    %rax,%r10
    6b3b:	0f 84 ef 01 00 00    	je     6d30 <barriered_work+0x2f0>
    6b41:	8b 04 24             	mov    (%rsp),%eax
    6b44:	41 39 c6             	cmp    %eax,%r14d
    6b47:	74 df                	je     6b28 <barriered_work+0xe8>
    6b49:	49 8b 57 20          	mov    0x20(%r15),%rdx
    6b4d:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    6b52:	4a 8d 04 2f          	lea    (%rdi,%r13,1),%rax
    6b56:	44 8b 80 a0 01 00 00 	mov    0x1a0(%rax),%r8d
    6b5d:	45 85 c0             	test   %r8d,%r8d
    6b60:	75 c6                	jne    6b28 <barriered_work+0xe8>
    6b62:	4c 8b 44 2a 38       	mov    0x38(%rdx,%rbp,1),%r8
    6b67:	4b 8d 14 28          	lea    (%r8,%r13,1),%rdx
    6b6b:	44 8b 8a a0 01 00 00 	mov    0x1a0(%rdx),%r9d
    6b72:	45 85 c9             	test   %r9d,%r9d
    6b75:	75 b1                	jne    6b28 <barriered_work+0xe8>
    6b77:	4c 8b 24 24          	mov    (%rsp),%r12
    6b7b:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    6b82:	49 c1 e4 08          	shl    $0x8,%r12
    6b86:	42 83 bc 22 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r12,1)
    6b8f:	75 97                	jne    6b28 <barriered_work+0xe8>
    6b91:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    6b98:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    6b9d:	83 bc 10 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rdx,1)
    6ba5:	75 81                	jne    6b28 <barriered_work+0xe8>
    6ba7:	48 63 44 24 1c       	movslq 0x1c(%rsp),%rax
    6bac:	85 c0                	test   %eax,%eax
    6bae:	0f 8e 74 ff ff ff    	jle    6b28 <barriered_work+0xe8>
    6bb4:	48 89 c2             	mov    %rax,%rdx
    6bb7:	4c 89 7c 24 20       	mov    %r15,0x20(%rsp)
    6bbc:	b8 70 01 00 00       	mov    $0x170,%eax
    6bc1:	48 c1 e2 09          	shl    $0x9,%rdx
    6bc5:	89 4c 24 30          	mov    %ecx,0x30(%rsp)
    6bc9:	44 89 74 24 34       	mov    %r14d,0x34(%rsp)
    6bce:	4c 8d 9a a0 01 00 00 	lea    0x1a0(%rdx),%r11
    6bd5:	48 89 54 24 48       	mov    %rdx,0x48(%rsp)
    6bda:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    6bdf:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    6be4:	4c 89 54 24 38       	mov    %r10,0x38(%rsp)
    6be9:	44 8b 54 24 1c       	mov    0x1c(%rsp),%r10d
    6bee:	48 89 74 24 40       	mov    %rsi,0x40(%rsp)
    6bf3:	48 89 c6             	mov    %rax,%rsi
    6bf6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6c00:	41 83 c1 01          	add    $0x1,%r9d
    6c04:	49 8b 0c 30          	mov    (%r8,%rsi,1),%rcx
    6c08:	44 89 c8             	mov    %r9d,%eax
    6c0b:	99                   	cltd
    6c0c:	4c 01 e1             	add    %r12,%rcx
    6c0f:	41 f7 fa             	idiv   %r10d
    6c12:	4c 8b 31             	mov    (%rcx),%r14
    6c15:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    6c1a:	4c 8b b1 80 00 00 00 	mov    0x80(%rcx),%r14
    6c21:	48 63 d2             	movslq %edx,%rdx
    6c24:	48 c1 e2 09          	shl    $0x9,%rdx
    6c28:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    6c30:	4c 01 e8             	add    %r13,%rax
    6c33:	4c 8b 38             	mov    (%rax),%r15
    6c36:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    6c3d:	4c 89 30             	mov    %r14,(%rax)
    6c40:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    6c45:	4c 89 b0 80 00 00 00 	mov    %r14,0x80(%rax)
    6c4c:	48 89 11             	mov    %rdx,(%rcx)
    6c4f:	4c 89 b9 80 00 00 00 	mov    %r15,0x80(%rcx)
    6c56:	b9 a0 01 00 00       	mov    $0x1a0,%ecx
    6c5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6c60:	41 c7 04 08 01 00 00 00 	movl   $0x1,(%r8,%rcx,1)
    6c68:	c7 04 0f 01 00 00 00 	movl   $0x1,(%rdi,%rcx,1)
    6c6f:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
    6c76:	49 39 cb             	cmp    %rcx,%r11
    6c79:	75 e5                	jne    6c60 <barriered_work+0x220>
    6c7b:	48 8b 0c 37          	mov    (%rdi,%rsi,1),%rcx
    6c7f:	48 8b 00             	mov    (%rax),%rax
    6c82:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
    6c8d:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    6c94:	4a 8b 8c 29 80 00 00 00 	mov    0x80(%rcx,%r13,1),%rcx
    6c9c:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
    6ca6:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
    6cb0:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    6cba:	45 39 ca             	cmp    %r9d,%r10d
    6cbd:	0f 85 3d ff ff ff    	jne    6c00 <barriered_work+0x1c0>
    6cc3:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
    6cc8:	48 8b 54 24 48       	mov    0x48(%rsp),%rdx
    6ccd:	b8 70 01 00 00       	mov    $0x170,%eax
    6cd2:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    6cd7:	8b 4c 24 30          	mov    0x30(%rsp),%ecx
    6cdb:	44 8b 74 24 34       	mov    0x34(%rsp),%r14d
    6ce0:	4c 8b 54 24 38       	mov    0x38(%rsp),%r10
    6ce5:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    6cea:	4c 8d 9a 70 01 00 00 	lea    0x170(%rdx),%r11
    6cf1:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    6cf6:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    6cfb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6d00:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    6d04:	4d 8b 0c 00          	mov    (%r8,%rax,1),%r9
    6d08:	4a 8b 14 3a          	mov    (%rdx,%r15,1),%rdx
    6d0c:	4b 39 14 21          	cmp    %rdx,(%r9,%r12,1)
    6d10:	0f 84 78 01 00 00    	je     6e8e <barriered_work+0x44e>
    6d16:	48 05 00 02 00 00    	add    $0x200,%rax
    6d1c:	49 39 c3             	cmp    %rax,%r11
    6d1f:	75 df                	jne    6d00 <barriered_work+0x2c0>
    6d21:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    6d26:	e9 fd fd ff ff       	jmp    6b28 <barriered_work+0xe8>
    6d2b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6d30:	41 89 cc             	mov    %ecx,%r12d
    6d33:	48 89 df             	mov    %rbx,%rdi
    6d36:	e8 b5 fb ff ff       	call   68f0 <fswap>
    6d3b:	48 89 df             	mov    %rbx,%rdi
    6d3e:	e8 cd f7 ff ff       	call   6510 <receive>
    6d43:	0f ae f8             	sfence
    6d46:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6d4d:	31 ff                	xor    %edi,%edi
    6d4f:	48 c1 e6 05          	shl    $0x5,%rsi
    6d53:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6d5a:	e8 f1 b5 ff ff       	call   2350 <clock_gettime@plt>
    6d5f:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6d66:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6d6d:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6d71:	8b 72 10             	mov    0x10(%rdx),%esi
    6d74:	8d 6e 01             	lea    0x1(%rsi),%ebp
    6d77:	89 6a 10             	mov    %ebp,0x10(%rdx)
    6d7a:	75 55                	jne    6dd1 <barriered_work+0x391>
    6d7c:	0f 1f 40 00          	nopl   0x0(%rax)
    6d80:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    6d87:	48 8b 40 18          	mov    0x18(%rax),%rax
    6d8b:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
    6d8f:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    6d97:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6d9b:	48 c1 e7 09          	shl    $0x9,%rdi
    6d9f:	48 03 78 38          	add    0x38(%rax),%rdi
    6da3:	ff 93 20 01 00 00    	call   *0x120(%rbx)
    6da9:	0f ae f8             	sfence
    6dac:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6db3:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6dba:	74 c4                	je     6d80 <barriered_work+0x340>
    6dbc:	48 8b 40 48          	mov    0x48(%rax),%rax
    6dc0:	3b 68 10             	cmp    0x10(%rax),%ebp
    6dc3:	74 0c                	je     6dd1 <barriered_work+0x391>
    6dc5:	48 8d 3d 7a 14 00 00 	lea    0x147a(%rip),%rdi        # 8246 <_IO_stdin_used+0x246>
    6dcc:	e8 5f b5 ff ff       	call   2330 <puts@plt>
    6dd1:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6dd8:	31 ff                	xor    %edi,%edi
    6dda:	48 c1 e6 05          	shl    $0x5,%rsi
    6dde:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6de5:	48 83 c6 10          	add    $0x10,%rsi
    6de9:	e8 62 b5 ff ff       	call   2350 <clock_gettime@plt>
    6dee:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6df5:	48 83 c0 01          	add    $0x1,%rax
    6df9:	48 99                	cqto
    6dfb:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6e02:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6e08:	83 e8 01             	sub    $0x1,%eax
    6e0b:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    6e12:	44 39 e0             	cmp    %r12d,%eax
    6e15:	0f 85 83 fc ff ff    	jne    6a9e <barriered_work+0x5e>
    6e1b:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    6e22:	85 d2                	test   %edx,%edx
    6e24:	0f 8e 74 fc ff ff    	jle    6a9e <barriered_work+0x5e>
    6e2a:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    6e31:	48 c1 e2 09          	shl    $0x9,%rdx
    6e35:	48 63 41 08          	movslq 0x8(%rcx),%rax
    6e39:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    6e3d:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    6e41:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    6e45:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    6e49:	48 8b 40 38          	mov    0x38(%rax),%rax
    6e4d:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    6e51:	80 e6 02             	and    $0x2,%dh
    6e54:	74 1a                	je     6e70 <barriered_work+0x430>
    6e56:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    6e5d:	48 05 00 02 00 00    	add    $0x200,%rax
    6e63:	48 39 c8             	cmp    %rcx,%rax
    6e66:	0f 84 32 fc ff ff    	je     6a9e <barriered_work+0x5e>
    6e6c:	0f 1f 40 00          	nopl   0x0(%rax)
    6e70:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    6e77:	83 80 a4 03 00 00 01 	addl   $0x1,0x3a4(%rax)
    6e7e:	48 05 00 04 00 00    	add    $0x400,%rax
    6e84:	48 39 c8             	cmp    %rcx,%rax
    6e87:	75 e7                	jne    6e70 <barriered_work+0x430>
    6e89:	e9 10 fc ff ff       	jmp    6a9e <barriered_work+0x5e>
    6e8e:	bf 01 00 00 00       	mov    $0x1,%edi
    6e93:	48 8d 35 91 13 00 00 	lea    0x1391(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    6e9a:	31 c0                	xor    %eax,%eax
    6e9c:	e8 0f b6 ff ff       	call   24b0 <__printf_chk@plt>
    6ea1:	bf 01 00 00 00       	mov    $0x1,%edi
    6ea6:	e8 65 b6 ff ff       	call   2510 <exit@plt>
    6eab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006eb0 <barriered_work_ingest_andwork>:
    6eb0:	f3 0f 1e fa          	endbr64
    6eb4:	53                   	push   %rbx
    6eb5:	48 89 fb             	mov    %rdi,%rbx
    6eb8:	e8 63 f2 ff ff       	call   6120 <barriered_work_ingest>
    6ebd:	48 89 df             	mov    %rbx,%rdi
    6ec0:	5b                   	pop    %rbx
    6ec1:	e9 7a fb ff ff       	jmp    6a40 <barriered_work>
    6ec6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006ed0 <barriered_nulltask>:
    6ed0:	f3 0f 1e fa          	endbr64
    6ed4:	31 c0                	xor    %eax,%eax
    6ed6:	c3                   	ret
    6ed7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006ee0 <barriered_steal>:
    6ee0:	f3 0f 1e fa          	endbr64
    6ee4:	31 c0                	xor    %eax,%eax
    6ee6:	c3                   	ret
    6ee7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006ef0 <after>:
    6ef0:	f3 0f 1e fa          	endbr64
    6ef4:	31 c0                	xor    %eax,%eax
    6ef6:	48 39 d7             	cmp    %rdx,%rdi
    6ef9:	7e 08                	jle    6f03 <after+0x13>
    6efb:	31 c0                	xor    %eax,%eax
    6efd:	48 39 ce             	cmp    %rcx,%rsi
    6f00:	0f 9f c0             	setg   %al
    6f03:	c3                   	ret
    6f04:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6f0f:	90                   	nop

0000000000006f10 <within>:
    6f10:	f3 0f 1e fa          	endbr64
    6f14:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6f19:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    6f1e:	31 c0                	xor    %eax,%eax
    6f20:	48 39 d7             	cmp    %rdx,%rdi
    6f23:	7f 18                	jg     6f3d <within+0x2d>
    6f25:	4d 39 d8             	cmp    %r11,%r8
    6f28:	0f 9e c2             	setle  %dl
    6f2b:	48 39 ce             	cmp    %rcx,%rsi
    6f2e:	0f 9e c0             	setle  %al
    6f31:	21 c2                	and    %eax,%edx
    6f33:	31 c0                	xor    %eax,%eax
    6f35:	4d 39 d1             	cmp    %r10,%r9
    6f38:	0f 9e c0             	setle  %al
    6f3b:	21 d0                	and    %edx,%eax
    6f3d:	c3                   	ret
    6f3e:	66 90                	xchg   %ax,%ax

0000000000006f40 <overlap>:
    6f40:	f3 0f 1e fa          	endbr64
    6f44:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6f49:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    6f4e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6f53:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6f58:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    6f5d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
    6f62:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6f67:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    6f6c:	48 39 fe             	cmp    %rdi,%rsi
    6f6f:	7d 2f                	jge    6fa0 <overlap+0x60>
    6f71:	48 39 ca             	cmp    %rcx,%rdx
    6f74:	7d 62                	jge    6fd8 <overlap+0x98>
    6f76:	4d 39 da             	cmp    %r11,%r10
    6f79:	7d 0e                	jge    6f89 <overlap+0x49>
    6f7b:	b8 01 00 00 00       	mov    $0x1,%eax
    6f80:	4d 39 c1             	cmp    %r8,%r9
    6f83:	0f 8c 7f 00 00 00    	jl     7008 <overlap+0xc8>
    6f89:	31 c0                	xor    %eax,%eax
    6f8b:	4d 39 c1             	cmp    %r8,%r9
    6f8e:	7f 4c                	jg     6fdc <overlap+0x9c>
    6f90:	31 c0                	xor    %eax,%eax
    6f92:	4d 39 da             	cmp    %r11,%r10
    6f95:	0f 9e c0             	setle  %al
    6f98:	c3                   	ret
    6f99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6fa0:	7e 4e                	jle    6ff0 <overlap+0xb0>
    6fa2:	48 39 ca             	cmp    %rcx,%rdx
    6fa5:	7f 39                	jg     6fe0 <overlap+0xa0>
    6fa7:	75 31                	jne    6fda <overlap+0x9a>
    6fa9:	4d 39 c1             	cmp    %r8,%r9
    6fac:	7c 2c                	jl     6fda <overlap+0x9a>
    6fae:	b8 01 00 00 00       	mov    $0x1,%eax
    6fb3:	4d 39 da             	cmp    %r11,%r10
    6fb6:	7d 24                	jge    6fdc <overlap+0x9c>
    6fb8:	48 39 ca             	cmp    %rcx,%rdx
    6fbb:	0f 94 c2             	sete   %dl
    6fbe:	48 39 fe             	cmp    %rdi,%rsi
    6fc1:	0f 94 c0             	sete   %al
    6fc4:	21 c2                	and    %eax,%edx
    6fc6:	31 c0                	xor    %eax,%eax
    6fc8:	4d 39 c1             	cmp    %r8,%r9
    6fcb:	0f 94 c0             	sete   %al
    6fce:	21 d0                	and    %edx,%eax
    6fd0:	c3                   	ret
    6fd1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6fd8:	74 af                	je     6f89 <overlap+0x49>
    6fda:	31 c0                	xor    %eax,%eax
    6fdc:	c3                   	ret
    6fdd:	0f 1f 00             	nopl   (%rax)
    6fe0:	4d 39 da             	cmp    %r11,%r10
    6fe3:	7e c4                	jle    6fa9 <overlap+0x69>
    6fe5:	b8 01 00 00 00       	mov    $0x1,%eax
    6fea:	4d 39 c1             	cmp    %r8,%r9
    6fed:	7e ba                	jle    6fa9 <overlap+0x69>
    6fef:	c3                   	ret
    6ff0:	48 39 ca             	cmp    %rcx,%rdx
    6ff3:	7c 94                	jl     6f89 <overlap+0x49>
    6ff5:	4d 39 c1             	cmp    %r8,%r9
    6ff8:	7d b4                	jge    6fae <overlap+0x6e>
    6ffa:	48 39 ca             	cmp    %rcx,%rdx
    6ffd:	74 91                	je     6f90 <overlap+0x50>
    6fff:	eb d9                	jmp    6fda <overlap+0x9a>
    7001:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7008:	c3                   	ret
    7009:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000007010 <verify>:
    7010:	f3 0f 1e fa          	endbr64
    7014:	85 f6                	test   %esi,%esi
    7016:	0f 8e 44 03 00 00    	jle    7360 <verify+0x350>
    701c:	41 57                	push   %r15
    701e:	41 89 f7             	mov    %esi,%r15d
    7021:	41 56                	push   %r14
    7023:	45 31 f6             	xor    %r14d,%r14d
    7026:	41 55                	push   %r13
    7028:	41 54                	push   %r12
    702a:	55                   	push   %rbp
    702b:	53                   	push   %rbx
    702c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    7030:	48 83 ec 58          	sub    $0x58,%rsp
    7034:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    7039:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    703e:	45 31 e4             	xor    %r12d,%r12d
    7041:	45 39 e6             	cmp    %r12d,%r14d
    7044:	0f 84 4e 02 00 00    	je     7298 <verify+0x288>
    704a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    704f:	8b 50 08             	mov    0x8(%rax),%edx
    7052:	85 d2                	test   %edx,%edx
    7054:	0f 8e 3e 02 00 00    	jle    7298 <verify+0x288>
    705a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    705f:	31 c9                	xor    %ecx,%ecx
    7061:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    7066:	31 c0                	xor    %eax,%eax
    7068:	44 89 f2             	mov    %r14d,%edx
    706b:	bf 01 00 00 00       	mov    $0x1,%edi
    7070:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    7075:	48 8d 35 da 11 00 00 	lea    0x11da(%rip),%rsi        # 8256 <_IO_stdin_used+0x256>
    707c:	e8 2f b4 ff ff       	call   24b0 <__printf_chk@plt>
    7081:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7086:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    708b:	8b 40 08             	mov    0x8(%rax),%eax
    708e:	85 c0                	test   %eax,%eax
    7090:	0f 8e e6 01 00 00    	jle    727c <verify+0x26c>
    7096:	48 89 c8             	mov    %rcx,%rax
    7099:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    709e:	31 db                	xor    %ebx,%ebx
    70a0:	48 c1 e0 09          	shl    $0x9,%rax
    70a4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    70a9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    70ae:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    70b3:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    70b8:	4c 8b 20             	mov    (%rax),%r12
    70bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    70c0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    70c5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    70ca:	49 89 de             	mov    %rbx,%r14
    70cd:	48 8d 35 97 11 00 00 	lea    0x1197(%rip),%rsi        # 826b <_IO_stdin_used+0x26b>
    70d4:	49 c1 e6 09          	shl    $0x9,%r14
    70d8:	bf 01 00 00 00       	mov    $0x1,%edi
    70dd:	48 8b 45 00          	mov    0x0(%rbp),%rax
    70e1:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    70e9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    70ee:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    70f6:	31 c0                	xor    %eax,%eax
    70f8:	e8 b3 b3 ff ff       	call   24b0 <__printf_chk@plt>
    70fd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7102:	4c 8b 20             	mov    (%rax),%r12
    7105:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    710e:	0f 8e 47 01 00 00    	jle    725b <verify+0x24b>
    7114:	4c 03 75 00          	add    0x0(%rbp),%r14
    7118:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    711d:	ba 01 00 00 00       	mov    $0x1,%edx
    7122:	4d 89 f5             	mov    %r14,%r13
    7125:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    712c:	4d 85 f6             	test   %r14,%r14
    712f:	0f 8e 21 01 00 00    	jle    7256 <verify+0x246>
    7135:	0f 1f 00             	nopl   (%rax)
    7138:	48 89 d5             	mov    %rdx,%rbp
    713b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7140:	31 db                	xor    %ebx,%ebx
    7142:	4d 89 f2             	mov    %r14,%r10
    7145:	48 c1 e5 05          	shl    $0x5,%rbp
    7149:	48 83 ed 20          	sub    $0x20,%rbp
    714d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    7151:	49 89 ee             	mov    %rbp,%r14
    7154:	48 89 dd             	mov    %rbx,%rbp
    7157:	48 89 d3             	mov    %rdx,%rbx
    715a:	eb 31                	jmp    718d <verify+0x17d>
    715c:	0f 1f 40 00          	nopl   0x0(%rax)
    7160:	4c 39 c2             	cmp    %r8,%rdx
    7163:	0f 8d 57 01 00 00    	jge    72c0 <verify+0x2b0>
    7169:	4c 39 df             	cmp    %r11,%rdi
    716c:	7e 05                	jle    7173 <verify+0x163>
    716e:	49 39 c1             	cmp    %rax,%r9
    7171:	7c 75                	jl     71e8 <verify+0x1d8>
    7173:	4c 39 df             	cmp    %r11,%rdi
    7176:	0f 8d ab 01 00 00    	jge    7327 <verify+0x317>
    717c:	0f 1f 40 00          	nopl   0x0(%rax)
    7180:	48 83 c5 01          	add    $0x1,%rbp
    7184:	49 39 ea             	cmp    %rbp,%r10
    7187:	0f 8e a9 00 00 00    	jle    7236 <verify+0x226>
    718d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    7194:	48 89 e8             	mov    %rbp,%rax
    7197:	48 c1 e0 05          	shl    $0x5,%rax
    719b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    71a2:	4c 01 f2             	add    %r14,%rdx
    71a5:	48 8b 08             	mov    (%rax),%rcx
    71a8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    71ac:	48 8b 32             	mov    (%rdx),%rsi
    71af:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    71b3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    71b7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    71bb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    71bf:	48 8b 40 18          	mov    0x18(%rax),%rax
    71c3:	48 39 f1             	cmp    %rsi,%rcx
    71c6:	7c 98                	jl     7160 <verify+0x150>
    71c8:	0f 8e 42 01 00 00    	jle    7310 <verify+0x300>
    71ce:	4c 39 c2             	cmp    %r8,%rdx
    71d1:	0f 8f f9 00 00 00    	jg     72d0 <verify+0x2c0>
    71d7:	75 a7                	jne    7180 <verify+0x170>
    71d9:	4c 39 df             	cmp    %r11,%rdi
    71dc:	7f a2                	jg     7180 <verify+0x170>
    71de:	49 39 c1             	cmp    %rax,%r9
    71e1:	7c 9d                	jl     7180 <verify+0x170>
    71e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    71e8:	49 89 c1             	mov    %rax,%r9
    71eb:	48 89 f9             	mov    %rdi,%rcx
    71ee:	48 89 f2             	mov    %rsi,%rdx
    71f1:	bf 01 00 00 00       	mov    $0x1,%edi
    71f6:	48 8d 35 3b 14 00 00 	lea    0x143b(%rip),%rsi        # 8638 <_IO_stdin_used+0x638>
    71fd:	31 c0                	xor    %eax,%eax
    71ff:	48 83 c5 01          	add    $0x1,%rbp
    7203:	e8 a8 b2 ff ff       	call   24b0 <__printf_chk@plt>
    7208:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    720d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    7212:	4c 03 28             	add    (%rax),%r13
    7215:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    721a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
    7221:	4c 8b 20             	mov    (%rax),%r12
    7224:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7229:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    722d:	49 39 ea             	cmp    %rbp,%r10
    7230:	0f 8f 57 ff ff ff    	jg     718d <verify+0x17d>
    7236:	48 89 da             	mov    %rbx,%rdx
    7239:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    7240:	7d 14                	jge    7256 <verify+0x246>
    7242:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7249:	48 83 c2 01          	add    $0x1,%rdx
    724d:	4d 85 f6             	test   %r14,%r14
    7250:	0f 8f e2 fe ff ff    	jg     7138 <verify+0x128>
    7256:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    725b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7260:	48 83 c3 01          	add    $0x1,%rbx
    7264:	39 58 08             	cmp    %ebx,0x8(%rax)
    7267:	0f 8f 53 fe ff ff    	jg     70c0 <verify+0xb0>
    726d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    7272:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    7277:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
    727c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7281:	48 83 c1 01          	add    $0x1,%rcx
    7285:	39 48 08             	cmp    %ecx,0x8(%rax)
    7288:	0f 8f d8 fd ff ff    	jg     7066 <verify+0x56>
    728e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    7293:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    7298:	48 81 44 24 10 d8 00 00 00 	addq   $0xd8,0x10(%rsp)
    72a1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    72a6:	41 39 c7             	cmp    %eax,%r15d
    72a9:	0f 84 86 00 00 00    	je     7335 <verify+0x325>
    72af:	41 89 c4             	mov    %eax,%r12d
    72b2:	e9 8a fd ff ff       	jmp    7041 <verify+0x31>
    72b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    72c0:	0f 85 ba fe ff ff    	jne    7180 <verify+0x170>
    72c6:	e9 a8 fe ff ff       	jmp    7173 <verify+0x163>
    72cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    72d0:	49 39 c1             	cmp    %rax,%r9
    72d3:	7e 09                	jle    72de <verify+0x2ce>
    72d5:	4c 39 df             	cmp    %r11,%rdi
    72d8:	0f 8c 0a ff ff ff    	jl     71e8 <verify+0x1d8>
    72de:	4c 39 df             	cmp    %r11,%rdi
    72e1:	0f 8f 99 fe ff ff    	jg     7180 <verify+0x170>
    72e7:	49 39 c1             	cmp    %rax,%r9
    72ea:	0f 8d f8 fe ff ff    	jge    71e8 <verify+0x1d8>
    72f0:	48 39 f1             	cmp    %rsi,%rcx
    72f3:	0f 85 87 fe ff ff    	jne    7180 <verify+0x170>
    72f9:	4c 39 c2             	cmp    %r8,%rdx
    72fc:	0f 85 7e fe ff ff    	jne    7180 <verify+0x170>
    7302:	4c 39 df             	cmp    %r11,%rdi
    7305:	0f 84 dd fe ff ff    	je     71e8 <verify+0x1d8>
    730b:	e9 70 fe ff ff       	jmp    7180 <verify+0x170>
    7310:	4c 39 c2             	cmp    %r8,%rdx
    7313:	0f 8c 5a fe ff ff    	jl     7173 <verify+0x163>
    7319:	4c 39 df             	cmp    %r11,%rdi
    731c:	7e c9                	jle    72e7 <verify+0x2d7>
    731e:	4c 39 c2             	cmp    %r8,%rdx
    7321:	0f 85 59 fe ff ff    	jne    7180 <verify+0x170>
    7327:	49 39 c1             	cmp    %rax,%r9
    732a:	0f 8f 50 fe ff ff    	jg     7180 <verify+0x170>
    7330:	e9 b3 fe ff ff       	jmp    71e8 <verify+0x1d8>
    7335:	48 81 44 24 18 d8 00 00 00 	addq   $0xd8,0x18(%rsp)
    733e:	41 8d 46 01          	lea    0x1(%r14),%eax
    7342:	45 39 e6             	cmp    %r12d,%r14d
    7345:	74 08                	je     734f <verify+0x33f>
    7347:	41 89 c6             	mov    %eax,%r14d
    734a:	e9 ea fc ff ff       	jmp    7039 <verify+0x29>
    734f:	48 83 c4 58          	add    $0x58,%rsp
    7353:	31 c0                	xor    %eax,%eax
    7355:	5b                   	pop    %rbx
    7356:	5d                   	pop    %rbp
    7357:	41 5c                	pop    %r12
    7359:	41 5d                	pop    %r13
    735b:	41 5e                	pop    %r14
    735d:	41 5f                	pop    %r15
    735f:	c3                   	ret
    7360:	31 c0                	xor    %eax,%eax
    7362:	c3                   	ret

Disassembly of section .fini:

0000000000007364 <_fini>:
    7364:	f3 0f 1e fa          	endbr64
    7368:	48 83 ec 08          	sub    $0x8,%rsp
    736c:	48 83 c4 08          	add    $0x8,%rsp
    7370:	c3                   	ret
