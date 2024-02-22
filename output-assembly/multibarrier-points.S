
multibarrier-points:     file format elf64-x86-64


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
    2676:	48 8d 3d 13 60 00 00 	lea    0x6013(%rip),%rdi        # 8690 <_IO_stdin_used+0x690>
    267d:	41 56                	push   %r14
    267f:	41 55                	push   %r13
    2681:	41 54                	push   %r12
    2683:	55                   	push   %rbp
    2684:	48 8d 2d 13 5d 00 00 	lea    0x5d13(%rip),%rbp        # 839e <_IO_stdin_used+0x39e>
    268b:	53                   	push   %rbx
    268c:	48 81 ec f8 00 00 00 	sub    $0xf8,%rsp
    2693:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    269c:	48 89 84 24 e8 00 00 00 	mov    %rax,0xe8(%rsp)
    26a4:	48 8d 05 45 1e 00 00 	lea    0x1e45(%rip),%rax        # 44f0 <barriered_reset>
    26ab:	66 48 0f 6e f0       	movq   %rax,%xmm6
    26b0:	0f 16 35 a1 85 00 00 	movhps 0x85a1(%rip),%xmm6        # ac58 <__do_global_dtors_aux_fini_array_entry+0x8>
    26b7:	0f 29 b4 24 a0 00 00 00 	movaps %xmm6,0xa0(%rsp)
    26bf:	e8 6c fc ff ff       	call   2330 <puts@plt>
    26c4:	bf 0a 00 00 00       	mov    $0xa,%edi
    26c9:	e8 42 fc ff ff       	call   2310 <putchar@plt>
    26ce:	ba 01 00 00 00       	mov    $0x1,%edx
    26d3:	48 8d 35 ac 5b 00 00 	lea    0x5bac(%rip),%rsi        # 8286 <_IO_stdin_used+0x286>
    26da:	31 c0                	xor    %eax,%eax
    26dc:	bf 01 00 00 00       	mov    $0x1,%edi
    26e1:	e8 ca fd ff ff       	call   24b0 <__printf_chk@plt>
    26e6:	ba 04 00 00 00       	mov    $0x4,%edx
    26eb:	48 8d 35 a4 5b 00 00 	lea    0x5ba4(%rip),%rsi        # 8296 <_IO_stdin_used+0x296>
    26f2:	31 c0                	xor    %eax,%eax
    26f4:	bf 01 00 00 00       	mov    $0x1,%edi
    26f9:	e8 b2 fd ff ff       	call   24b0 <__printf_chk@plt>
    26fe:	ba 02 00 00 00       	mov    $0x2,%edx
    2703:	48 8d 35 a1 5b 00 00 	lea    0x5ba1(%rip),%rsi        # 82ab <_IO_stdin_used+0x2ab>
    270a:	31 c0                	xor    %eax,%eax
    270c:	bf 01 00 00 00       	mov    $0x1,%edi
    2711:	e8 9a fd ff ff       	call   24b0 <__printf_chk@plt>
    2716:	ba 02 00 00 00       	mov    $0x2,%edx
    271b:	48 8d 35 99 5b 00 00 	lea    0x5b99(%rip),%rsi        # 82bb <_IO_stdin_used+0x2bb>
    2722:	31 c0                	xor    %eax,%eax
    2724:	bf 01 00 00 00       	mov    $0x1,%edi
    2729:	e8 82 fd ff ff       	call   24b0 <__printf_chk@plt>
    272e:	48 8d 3d 9c 5b 00 00 	lea    0x5b9c(%rip),%rdi        # 82d1 <_IO_stdin_used+0x2d1>
    2735:	e8 f6 fb ff ff       	call   2330 <puts@plt>
    273a:	ba 02 00 00 00       	mov    $0x2,%edx
    273f:	48 8d 35 a7 5b 00 00 	lea    0x5ba7(%rip),%rsi        # 82ed <_IO_stdin_used+0x2ed>
    2746:	31 c0                	xor    %eax,%eax
    2748:	bf 01 00 00 00       	mov    $0x1,%edi
    274d:	e8 5e fd ff ff       	call   24b0 <__printf_chk@plt>
    2752:	ba 08 00 00 00       	mov    $0x8,%edx
    2757:	48 8d 35 a9 5b 00 00 	lea    0x5ba9(%rip),%rsi        # 8307 <_IO_stdin_used+0x307>
    275e:	31 c0                	xor    %eax,%eax
    2760:	bf 01 00 00 00       	mov    $0x1,%edi
    2765:	e8 46 fd ff ff       	call   24b0 <__printf_chk@plt>
    276a:	ba 01 00 00 00       	mov    $0x1,%edx
    276f:	48 8d 35 a5 5b 00 00 	lea    0x5ba5(%rip),%rsi        # 831b <_IO_stdin_used+0x31b>
    2776:	31 c0                	xor    %eax,%eax
    2778:	bf 01 00 00 00       	mov    $0x1,%edi
    277d:	e8 2e fd ff ff       	call   24b0 <__printf_chk@plt>
    2782:	ba 01 00 00 00       	mov    $0x1,%edx
    2787:	48 8d 35 9e 5b 00 00 	lea    0x5b9e(%rip),%rsi        # 832c <_IO_stdin_used+0x32c>
    278e:	31 c0                	xor    %eax,%eax
    2790:	bf 01 00 00 00       	mov    $0x1,%edi
    2795:	e8 16 fd ff ff       	call   24b0 <__printf_chk@plt>
    279a:	ba 02 00 00 00       	mov    $0x2,%edx
    279f:	48 8d 35 9e 5b 00 00 	lea    0x5b9e(%rip),%rsi        # 8344 <_IO_stdin_used+0x344>
    27a6:	31 c0                	xor    %eax,%eax
    27a8:	bf 01 00 00 00       	mov    $0x1,%edi
    27ad:	e8 fe fc ff ff       	call   24b0 <__printf_chk@plt>
    27b2:	ba 01 00 00 00       	mov    $0x1,%edx
    27b7:	48 8d 35 3a 5f 00 00 	lea    0x5f3a(%rip),%rsi        # 86f8 <_IO_stdin_used+0x6f8>
    27be:	31 c0                	xor    %eax,%eax
    27c0:	bf 01 00 00 00       	mov    $0x1,%edi
    27c5:	e8 e6 fc ff ff       	call   24b0 <__printf_chk@plt>
    27ca:	ba 01 00 00 00       	mov    $0x1,%edx
    27cf:	48 8d 35 52 5f 00 00 	lea    0x5f52(%rip),%rsi        # 8728 <_IO_stdin_used+0x728>
    27d6:	31 c0                	xor    %eax,%eax
    27d8:	bf 01 00 00 00       	mov    $0x1,%edi
    27dd:	e8 ce fc ff ff       	call   24b0 <__printf_chk@plt>
    27e2:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    27e7:	48 8d 35 72 5b 00 00 	lea    0x5b72(%rip),%rsi        # 8360 <_IO_stdin_used+0x360>
    27ee:	31 c0                	xor    %eax,%eax
    27f0:	bf 01 00 00 00       	mov    $0x1,%edi
    27f5:	e8 b6 fc ff ff       	call   24b0 <__printf_chk@plt>
    27fa:	ba 05 00 00 00       	mov    $0x5,%edx
    27ff:	48 8d 35 74 5b 00 00 	lea    0x5b74(%rip),%rsi        # 837a <_IO_stdin_used+0x37a>
    2806:	31 c0                	xor    %eax,%eax
    2808:	bf 01 00 00 00       	mov    $0x1,%edi
    280d:	e8 9e fc ff ff       	call   24b0 <__printf_chk@plt>
    2812:	ba 05 00 00 00       	mov    $0x5,%edx
    2817:	48 8d 35 71 5b 00 00 	lea    0x5b71(%rip),%rsi        # 838f <_IO_stdin_used+0x38f>
    281e:	31 c0                	xor    %eax,%eax
    2820:	bf 01 00 00 00       	mov    $0x1,%edi
    2825:	e8 86 fc ff ff       	call   24b0 <__printf_chk@plt>
    282a:	48 8d 3d c4 58 00 00 	lea    0x58c4(%rip),%rdi        # 80f5 <_IO_stdin_used+0xf5>
    2831:	45 31 f6             	xor    %r14d,%r14d
    2834:	45 31 ed             	xor    %r13d,%r13d
    2837:	e8 f4 fa ff ff       	call   2330 <puts@plt>
    283c:	be 18 00 00 00       	mov    $0x18,%esi
    2841:	bf 02 00 00 00       	mov    $0x2,%edi
    2846:	e8 b5 fb ff ff       	call   2400 <calloc@plt>
    284b:	be 80 01 00 00       	mov    $0x180,%esi
    2850:	bf 08 00 00 00       	mov    $0x8,%edi
    2855:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    285a:	e8 a1 fb ff ff       	call   2400 <calloc@plt>
    285f:	be 28 00 00 00       	mov    $0x28,%esi
    2864:	bf 01 00 00 00       	mov    $0x1,%edi
    2869:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    286e:	e8 8d fb ff ff       	call   2400 <calloc@plt>
    2873:	be 28 00 00 00       	mov    $0x28,%esi
    2878:	bf 40 00 00 00       	mov    $0x40,%edi
    287d:	48 89 84 24 b8 00 00 00 	mov    %rax,0xb8(%rsp)
    2885:	e8 76 fb ff ff       	call   2400 <calloc@plt>
    288a:	48 89 84 24 c0 00 00 00 	mov    %rax,0xc0(%rsp)
    2892:	49 89 c7             	mov    %rax,%r15
    2895:	4d 89 fc             	mov    %r15,%r12
    2898:	31 db                	xor    %ebx,%ebx
    289a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    28a0:	42 8d 14 2b          	lea    (%rbx,%r13,1),%edx
    28a4:	41 89 d8             	mov    %ebx,%r8d
    28a7:	44 89 f1             	mov    %r14d,%ecx
    28aa:	48 89 ee             	mov    %rbp,%rsi
    28ad:	bf 01 00 00 00       	mov    $0x1,%edi
    28b2:	31 c0                	xor    %eax,%eax
    28b4:	83 c3 01             	add    $0x1,%ebx
    28b7:	e8 f4 fb ff ff       	call   24b0 <__printf_chk@plt>
    28bc:	4c 89 e7             	mov    %r12,%rdi
    28bf:	31 f6                	xor    %esi,%esi
    28c1:	49 83 c4 28          	add    $0x28,%r12
    28c5:	e8 b6 fc ff ff       	call   2580 <pthread_mutex_init@plt>
    28ca:	83 fb 08             	cmp    $0x8,%ebx
    28cd:	75 d1                	jne    28a0 <main+0x230>
    28cf:	41 83 c5 08          	add    $0x8,%r13d
    28d3:	41 83 c6 01          	add    $0x1,%r14d
    28d7:	49 81 c7 40 01 00 00 	add    $0x140,%r15
    28de:	41 83 fd 40          	cmp    $0x40,%r13d
    28e2:	75 b1                	jne    2895 <main+0x225>
    28e4:	ba 04 00 00 00       	mov    $0x4,%edx
    28e9:	48 8d 35 be 5a 00 00 	lea    0x5abe(%rip),%rsi        # 83ae <_IO_stdin_used+0x3ae>
    28f0:	bf 01 00 00 00       	mov    $0x1,%edi
    28f5:	31 c0                	xor    %eax,%eax
    28f7:	e8 b4 fb ff ff       	call   24b0 <__printf_chk@plt>
    28fc:	ba 08 00 00 00       	mov    $0x8,%edx
    2901:	48 8d 35 bc 5a 00 00 	lea    0x5abc(%rip),%rsi        # 83c4 <_IO_stdin_used+0x3c4>
    2908:	31 c0                	xor    %eax,%eax
    290a:	bf 01 00 00 00       	mov    $0x1,%edi
    290f:	e8 9c fb ff ff       	call   24b0 <__printf_chk@plt>
    2914:	be 10 00 00 00       	mov    $0x10,%esi
    2919:	bf 08 00 00 00       	mov    $0x8,%edi
    291e:	e8 dd fa ff ff       	call   2400 <calloc@plt>
    2923:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
    292b:	49 89 c4             	mov    %rax,%r12
    292e:	48 8d 98 80 00 00 00 	lea    0x80(%rax),%rbx
    2935:	49 89 c5             	mov    %rax,%r13
    2938:	be 00 01 00 00       	mov    $0x100,%esi
    293d:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    2945:	bf 01 00 00 00       	mov    $0x1,%edi
    294a:	49 83 c5 10          	add    $0x10,%r13
    294e:	e8 ad fa ff ff       	call   2400 <calloc@plt>
    2953:	be 20 00 00 00       	mov    $0x20,%esi
    2958:	bf 64 00 00 00       	mov    $0x64,%edi
    295d:	49 89 45 f8          	mov    %rax,-0x8(%r13)
    2961:	48 89 c5             	mov    %rax,%rbp
    2964:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    296e:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
    2978:	e8 83 fa ff ff       	call   2400 <calloc@plt>
    297d:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
    2984:	49 39 dd             	cmp    %rbx,%r13
    2987:	75 af                	jne    2938 <main+0x2c8>
    2989:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    298e:	31 db                	xor    %ebx,%ebx
    2990:	45 31 f6             	xor    %r14d,%r14d
    2993:	c7 44 24 30 00 00 00 00 	movl   $0x0,0x30(%rsp)
    299b:	c7 84 24 d0 00 00 00 00 00 00 00 	movl   $0x0,0xd0(%rsp)
    29a6:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
    29ae:	c7 44 24 74 00 00 00 00 	movl   $0x0,0x74(%rsp)
    29b6:	bf 05 00 00 00       	mov    $0x5,%edi
    29bb:	be 04 00 00 00       	mov    $0x4,%esi
    29c0:	89 5c 24 28          	mov    %ebx,0x28(%rsp)
    29c4:	e8 37 fa ff ff       	call   2400 <calloc@plt>
    29c9:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    29ce:	48 89 84 24 c8 00 00 00 	mov    %rax,0xc8(%rsp)
    29d6:	48 89 d8             	mov    %rbx,%rax
    29d9:	48 f7 d8             	neg    %rax
    29dc:	25 00 03 00 00       	and    $0x300,%eax
    29e1:	4c 8d 1c 38          	lea    (%rax,%rdi,1),%r11
    29e5:	48 63 84 24 d0 00 00 00 	movslq 0xd0(%rsp),%rax
    29ed:	48 c1 e0 04          	shl    $0x4,%rax
    29f1:	49 8d 2c 04          	lea    (%r12,%rax,1),%rbp
    29f5:	8d 04 1b             	lea    (%rbx,%rbx,1),%eax
    29f8:	8d 78 01             	lea    0x1(%rax),%edi
    29fb:	83 c0 03             	add    $0x3,%eax
    29fe:	48 89 ac 24 b0 00 00 00 	mov    %rbp,0xb0(%rsp)
    2a06:	89 7c 24 50          	mov    %edi,0x50(%rsp)
    2a0a:	89 84 24 d4 00 00 00 	mov    %eax,0xd4(%rsp)
    2a11:	44 8b 6c 24 50       	mov    0x50(%rsp),%r13d
    2a16:	8b 54 24 28          	mov    0x28(%rsp),%edx
    2a1a:	bf 01 00 00 00       	mov    $0x1,%edi
    2a1f:	31 c0                	xor    %eax,%eax
    2a21:	48 8d 35 28 5d 00 00 	lea    0x5d28(%rip),%rsi        # 8750 <_IO_stdin_used+0x750>
    2a28:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    2a2d:	41 8d 6d ff          	lea    -0x1(%r13),%ebp
    2a31:	89 e9                	mov    %ebp,%ecx
    2a33:	e8 78 fa ff ff       	call   24b0 <__printf_chk@plt>
    2a38:	be 08 00 00 00       	mov    $0x8,%esi
    2a3d:	bf 02 00 00 00       	mov    $0x2,%edi
    2a42:	e8 b9 f9 ff ff       	call   2400 <calloc@plt>
    2a47:	be 80 00 00 00       	mov    $0x80,%esi
    2a4c:	bf 01 00 00 00       	mov    $0x1,%edi
    2a51:	49 89 c7             	mov    %rax,%r15
    2a54:	e8 a7 f9 ff ff       	call   2400 <calloc@plt>
    2a59:	41 89 e8             	mov    %ebp,%r8d
    2a5c:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    2a61:	41 83 e0 01          	and    $0x1,%r8d
    2a65:	49 89 c1             	mov    %rax,%r9
    2a68:	44 89 44 24 68       	mov    %r8d,0x68(%rsp)
    2a6d:	0f 84 6b 09 00 00    	je     33de <main+0xd6e>
    2a73:	41 8d 45 fe          	lea    -0x2(%r13),%eax
    2a77:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    2a7c:	4c 89 da             	mov    %r11,%rdx
    2a7f:	48 89 c1             	mov    %rax,%rcx
    2a82:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    2a86:	48 c1 e0 07          	shl    $0x7,%rax
    2a8a:	48 01 f8             	add    %rdi,%rax
    2a8d:	49 8d 7f 08          	lea    0x8(%r15),%rdi
    2a91:	48 89 7c 24 60       	mov    %rdi,0x60(%rsp)
    2a96:	48 8b bc 24 98 00 00 00 	mov    0x98(%rsp),%rdi
    2a9e:	45 89 43 04          	mov    %r8d,0x4(%r11)
    2aa2:	48 8d 35 d7 5c 00 00 	lea    0x5cd7(%rip),%rsi        # 8780 <_IO_stdin_used+0x780>
    2aa9:	49 89 57 08          	mov    %rdx,0x8(%r15)
    2aad:	89 ea                	mov    %ebp,%edx
    2aaf:	49 89 7b 48          	mov    %rdi,0x48(%r11)
    2ab3:	bf 01 00 00 00       	mov    $0x1,%edi
    2ab8:	49 89 07             	mov    %rax,(%r15)
    2abb:	31 c0                	xor    %eax,%eax
    2abd:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    2ac2:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    2ac7:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2acb:	e8 e0 f9 ff ff       	call   24b0 <__printf_chk@plt>
    2ad0:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2ad4:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2ad9:	31 c0                	xor    %eax,%eax
    2adb:	89 ea                	mov    %ebp,%edx
    2add:	48 8d 35 cc 5c 00 00 	lea    0x5ccc(%rip),%rsi        # 87b0 <_IO_stdin_used+0x7b0>
    2ae4:	bf 01 00 00 00       	mov    $0x1,%edi
    2ae9:	41 89 8b b8 00 00 00 	mov    %ecx,0xb8(%r11)
    2af0:	8b 4c 24 74          	mov    0x74(%rsp),%ecx
    2af4:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    2af9:	e8 b2 f9 ff ff       	call   24b0 <__printf_chk@plt>
    2afe:	83 fd 01             	cmp    $0x1,%ebp
    2b01:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    2b06:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    2b0b:	0f 8f f3 08 00 00    	jg     3404 <main+0xd94>
    2b11:	48 63 44 24 74       	movslq 0x74(%rsp),%rax
    2b16:	48 89 c7             	mov    %rax,%rdi
    2b19:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2b1f:	77 12                	ja     2b33 <main+0x4c3>
    2b21:	48 c1 e8 06          	shr    $0x6,%rax
    2b25:	ba 01 00 00 00       	mov    $0x1,%edx
    2b2a:	89 f9                	mov    %edi,%ecx
    2b2c:	48 d3 e2             	shl    %cl,%rdx
    2b2f:	49 09 14 c1          	or     %rdx,(%r9,%rax,8)
    2b33:	83 44 24 74 02       	addl   $0x2,0x74(%rsp)
    2b38:	48 8b 84 24 c8 00 00 00 	mov    0xc8(%rsp),%rax
    2b40:	41 89 6b 08          	mov    %ebp,0x8(%r11)
    2b44:	be 10 00 00 00       	mov    $0x10,%esi
    2b49:	bf 64 00 00 00       	mov    $0x64,%edi
    2b4e:	4d 89 8b b0 00 00 00 	mov    %r9,0xb0(%r11)
    2b55:	45 31 ed             	xor    %r13d,%r13d
    2b58:	49 89 83 00 01 00 00 	mov    %rax,0x100(%r11)
    2b5f:	48 8b 84 24 c0 00 00 00 	mov    0xc0(%rsp),%rax
    2b67:	41 c7 83 08 01 00 00 05 00 00 00 	movl   $0x5,0x108(%r11)
    2b72:	49 89 83 c8 00 00 00 	mov    %rax,0xc8(%r11)
    2b79:	48 8b 84 24 b8 00 00 00 	mov    0xb8(%rsp),%rax
    2b81:	41 c7 03 5f 00 00 00 	movl   $0x5f,(%r11)
    2b88:	49 89 83 d0 00 00 00 	mov    %rax,0xd0(%r11)
    2b8f:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2b94:	4d 89 7b 18          	mov    %r15,0x18(%r11)
    2b98:	49 89 43 20          	mov    %rax,0x20(%r11)
    2b9c:	48 8b 05 5d 61 00 00 	mov    0x615d(%rip),%rax        # 8d00 <_IO_stdin_used+0xd00>
    2ba3:	41 c7 43 40 03 00 00 00 	movl   $0x3,0x40(%r11)
    2bab:	49 89 83 c0 00 00 00 	mov    %rax,0xc0(%r11)
    2bb2:	48 8b 05 57 61 00 00 	mov    0x6157(%rip),%rax        # 8d10 <_IO_stdin_used+0xd10>
    2bb9:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    2bbe:	49 89 43 28          	mov    %rax,0x28(%r11)
    2bc2:	e8 39 f8 ff ff       	call   2400 <calloc@plt>
    2bc7:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    2bcc:	be 10 00 00 00       	mov    $0x10,%esi
    2bd1:	bf 64 00 00 00       	mov    $0x64,%edi
    2bd6:	49 89 43 68          	mov    %rax,0x68(%r11)
    2bda:	e8 21 f8 ff ff       	call   2400 <calloc@plt>
    2bdf:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    2be4:	be 28 00 00 00       	mov    $0x28,%esi
    2be9:	66 0f 6f 35 ef 60 00 00 	movdqa 0x60ef(%rip),%xmm6        # 8ce0 <_IO_stdin_used+0xce0>
    2bf1:	bf 64 00 00 00       	mov    $0x64,%edi
    2bf6:	49 89 43 70          	mov    %rax,0x70(%r11)
    2bfa:	41 0f 29 b3 80 00 00 00 	movaps %xmm6,0x80(%r11)
    2c02:	e8 f9 f7 ff ff       	call   2400 <calloc@plt>
    2c07:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    2c0c:	be 00 02 00 00       	mov    $0x200,%esi
    2c11:	66 0f 6f 35 c7 60 00 00 	movdqa 0x60c7(%rip),%xmm6        # 8ce0 <_IO_stdin_used+0xce0>
    2c19:	bf 03 00 00 00       	mov    $0x3,%edi
    2c1e:	49 89 83 90 00 00 00 	mov    %rax,0x90(%r11)
    2c25:	41 0f 11 b3 98 00 00 00 	movups %xmm6,0x98(%r11)
    2c2d:	e8 ce f7 ff ff       	call   2400 <calloc@plt>
    2c32:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    2c37:	4c 89 a4 24 d8 00 00 00 	mov    %r12,0xd8(%rsp)
    2c3f:	48 89 c2             	mov    %rax,%rdx
    2c42:	49 89 43 38          	mov    %rax,0x38(%r11)
    2c46:	4c 89 5c 24 20       	mov    %r11,0x20(%rsp)
    2c4b:	4c 89 e8             	mov    %r13,%rax
    2c4e:	be 00 01 00 00       	mov    $0x100,%esi
    2c53:	bf 04 00 00 00       	mov    $0x4,%edi
    2c58:	45 89 ec             	mov    %r13d,%r12d
    2c5b:	48 c1 e0 09          	shl    $0x9,%rax
    2c5f:	44 89 6c 24 40       	mov    %r13d,0x40(%rsp)
    2c64:	4c 8d 3c 02          	lea    (%rdx,%rax,1),%r15
    2c68:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    2c6d:	48 8d 05 3c 18 00 00 	lea    0x183c(%rip),%rax        # 44b0 <do_protected_write>
    2c74:	49 89 87 20 01 00 00 	mov    %rax,0x120(%r15)
    2c7b:	e8 80 f7 ff ff       	call   2400 <calloc@plt>
    2c80:	8b 74 24 68          	mov    0x68(%rsp),%esi
    2c84:	31 d2                	xor    %edx,%edx
    2c86:	89 6c 24 08          	mov    %ebp,0x8(%rsp)
    2c8a:	49 89 87 70 01 00 00 	mov    %rax,0x170(%r15)
    2c91:	85 f6                	test   %esi,%esi
    2c93:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    2c98:	0f 84 70 04 00 00    	je     310e <main+0xa9e>
    2c9e:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2ca3:	49 89 c5             	mov    %rax,%r13
    2ca6:	41 89 d7             	mov    %edx,%r15d
    2ca9:	44 89 fd             	mov    %r15d,%ebp
    2cac:	31 c0                	xor    %eax,%eax
    2cae:	44 89 fa             	mov    %r15d,%edx
    2cb1:	bf 01 00 00 00       	mov    $0x1,%edi
    2cb6:	d1 fd                	sar    %ebp
    2cb8:	48 8d 35 1f 57 00 00 	lea    0x571f(%rip),%rsi        # 83de <_IO_stdin_used+0x3de>
    2cbf:	89 e9                	mov    %ebp,%ecx
    2cc1:	e8 ea f7 ff ff       	call   24b0 <__printf_chk@plt>
    2cc6:	39 dd                	cmp    %ebx,%ebp
    2cc8:	0f 84 86 04 00 00    	je     3154 <main+0xae4>
    2cce:	41 83 c7 01          	add    $0x1,%r15d
    2cd2:	49 81 c5 00 01 00 00 	add    $0x100,%r13
    2cd9:	41 83 ff 04          	cmp    $0x4,%r15d
    2cdd:	75 ca                	jne    2ca9 <main+0x639>
    2cdf:	8b 6c 24 08          	mov    0x8(%rsp),%ebp
    2ce3:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    2ce8:	45 31 ff             	xor    %r15d,%r15d
    2ceb:	45 89 e0             	mov    %r12d,%r8d
    2cee:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    2cf3:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    2cf8:	4c 89 6c 24 58       	mov    %r13,0x58(%rsp)
    2cfd:	41 89 ed             	mov    %ebp,%r13d
    2d00:	44 89 fd             	mov    %r15d,%ebp
    2d03:	48 89 cb             	mov    %rcx,%rbx
    2d06:	89 e8                	mov    %ebp,%eax
    2d08:	8b 7c 24 08          	mov    0x8(%rsp),%edi
    2d0c:	d1 f8                	sar    %eax
    2d0e:	39 f8                	cmp    %edi,%eax
    2d10:	0f 84 72 01 00 00    	je     2e88 <main+0x818>
    2d16:	89 ea                	mov    %ebp,%edx
    2d18:	48 8d 35 cf 56 00 00 	lea    0x56cf(%rip),%rsi        # 83ee <_IO_stdin_used+0x3ee>
    2d1f:	bf 01 00 00 00       	mov    $0x1,%edi
    2d24:	31 c0                	xor    %eax,%eax
    2d26:	44 89 44 24 18       	mov    %r8d,0x18(%rsp)
    2d2b:	e8 80 f7 ff ff       	call   24b0 <__printf_chk@plt>
    2d30:	be 08 00 00 00       	mov    $0x8,%esi
    2d35:	bf 01 00 00 00       	mov    $0x1,%edi
    2d3a:	e8 c1 f6 ff ff       	call   2400 <calloc@plt>
    2d3f:	be 08 00 00 00       	mov    $0x8,%esi
    2d44:	bf 01 00 00 00       	mov    $0x1,%edi
    2d49:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2d4e:	e8 ad f6 ff ff       	call   2400 <calloc@plt>
    2d53:	be 80 04 00 00       	mov    $0x480,%esi
    2d58:	bf 03 00 00 00       	mov    $0x3,%edi
    2d5d:	49 89 c4             	mov    %rax,%r12
    2d60:	e8 9b f6 ff ff       	call   2400 <calloc@plt>
    2d65:	be 80 04 00 00       	mov    $0x480,%esi
    2d6a:	bf 03 00 00 00       	mov    $0x3,%edi
    2d6f:	49 89 c7             	mov    %rax,%r15
    2d72:	e8 89 f6 ff ff       	call   2400 <calloc@plt>
    2d77:	44 8b 44 24 18       	mov    0x18(%rsp),%r8d
    2d7c:	4c 89 3b             	mov    %r15,(%rbx)
    2d7f:	41 8d 76 01          	lea    0x1(%r14),%esi
    2d83:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    2d88:	66 0f 6f 25 60 5f 00 00 	movdqa 0x5f60(%rip),%xmm4        # 8cf0 <_IO_stdin_used+0xcf0>
    2d90:	41 89 b7 98 08 00 00 	mov    %esi,0x898(%r15)
    2d97:	49 8d b7 80 04 00 00 	lea    0x480(%r15),%rsi
    2d9e:	45 89 b7 18 04 00 00 	mov    %r14d,0x418(%r15)
    2da5:	41 83 c6 02          	add    $0x2,%r14d
    2da9:	41 c7 87 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%r15)
    2db4:	45 89 af 0c 04 00 00 	mov    %r13d,0x40c(%r15)
    2dbb:	45 89 87 10 04 00 00 	mov    %r8d,0x410(%r15)
    2dc2:	41 89 af 14 04 00 00 	mov    %ebp,0x414(%r15)
    2dc9:	41 c7 87 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r15)
    2dd4:	45 89 af 8c 08 00 00 	mov    %r13d,0x88c(%r15)
    2ddb:	45 89 87 90 08 00 00 	mov    %r8d,0x890(%r15)
    2de2:	41 89 af 94 08 00 00 	mov    %ebp,0x894(%r15)
    2de9:	4c 89 bb a0 00 00 00 	mov    %r15,0xa0(%rbx)
    2df0:	48 89 b3 80 00 00 00 	mov    %rsi,0x80(%rbx)
    2df7:	48 c7 83 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%rbx)
    2e02:	48 c7 83 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%rbx)
    2e0d:	41 c7 87 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r15)
    2e18:	41 c7 87 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r15)
    2e23:	48 89 b3 a8 00 00 00 	mov    %rsi,0xa8(%rbx)
    2e2a:	c7 83 b0 00 00 00 02 00 00 00 	movl   $0x2,0xb0(%rbx)
    2e34:	4c 89 38             	mov    %r15,(%rax)
    2e37:	48 89 70 08          	mov    %rsi,0x8(%rax)
    2e3b:	48 89 83 98 00 00 00 	mov    %rax,0x98(%rbx)
    2e42:	41 c7 87 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r15)
    2e4d:	41 c7 87 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r15)
    2e58:	49 89 17             	mov    %rdx,(%r15)
    2e5b:	4d 89 a7 80 04 00 00 	mov    %r12,0x480(%r15)
    2e62:	41 c7 87 80 05 00 00 01 00 00 00 	movl   $0x1,0x580(%r15)
    2e6d:	41 c7 87 00 06 00 00 00 00 00 00 	movl   $0x0,0x600(%r15)
    2e78:	41 0f 29 a7 80 00 00 00 	movaps %xmm4,0x80(%r15)
    2e80:	41 0f 29 a7 00 05 00 00 	movaps %xmm4,0x500(%r15)
    2e88:	83 c5 01             	add    $0x1,%ebp
    2e8b:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    2e92:	83 fd 04             	cmp    $0x4,%ebp
    2e95:	0f 85 6b fe ff ff    	jne    2d06 <main+0x696>
    2e9b:	be 01 00 00 00       	mov    $0x1,%esi
    2ea0:	bf 00 01 00 00       	mov    $0x100,%edi
    2ea5:	45 89 c4             	mov    %r8d,%r12d
    2ea8:	44 89 ed             	mov    %r13d,%ebp
    2eab:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    2eb0:	4c 8b 6c 24 58       	mov    0x58(%rsp),%r13
    2eb5:	e8 46 f5 ff ff       	call   2400 <calloc@plt>
    2eba:	bf 20 00 00 00       	mov    $0x20,%edi
    2ebf:	49 89 c7             	mov    %rax,%r15
    2ec2:	e8 a9 f5 ff ff       	call   2470 <malloc@plt>
    2ec7:	48 83 ec 08          	sub    $0x8,%rsp
    2ecb:	45 89 e1             	mov    %r12d,%r9d
    2ece:	41 89 e8             	mov    %ebp,%r8d
    2ed1:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2ed6:	8b 7c 24 30          	mov    0x30(%rsp),%edi
    2eda:	ba 00 01 00 00       	mov    $0x100,%edx
    2edf:	31 c0                	xor    %eax,%eax
    2ee1:	48 8d 0d 10 59 00 00 	lea    0x5910(%rip),%rcx        # 87f8 <_IO_stdin_used+0x7f8>
    2ee8:	be 01 00 00 00       	mov    $0x1,%esi
    2eed:	57                   	push   %rdi
    2eee:	4c 89 ff             	mov    %r15,%rdi
    2ef1:	e8 aa f6 ff ff       	call   25a0 <__sprintf_chk@plt>
    2ef6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    2efb:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    2f00:	8b 7c 24 38          	mov    0x38(%rsp),%edi
    2f04:	48 63 46 08          	movslq 0x8(%rsi),%rax
    2f08:	48 8b 56 38          	mov    0x38(%rsi),%rdx
    2f0c:	4d 89 3a             	mov    %r15,(%r10)
    2f0f:	be 20 00 00 00       	mov    $0x20,%esi
    2f14:	4c 8b 7c 24 58       	mov    0x58(%rsp),%r15
    2f19:	41 89 7a 18          	mov    %edi,0x18(%r10)
    2f1d:	49 89 42 08          	mov    %rax,0x8(%r10)
    2f21:	8b 44 24 40          	mov    0x40(%rsp),%eax
    2f25:	49 01 d7             	add    %rdx,%r15
    2f28:	4d 89 6a 10          	mov    %r13,0x10(%r10)
    2f2c:	41 89 87 a0 01 00 00 	mov    %eax,0x1a0(%r15)
    2f33:	83 c0 01             	add    $0x1,%eax
    2f36:	89 44 24 40          	mov    %eax,0x40(%rsp)
    2f3a:	8b 44 24 50          	mov    0x50(%rsp),%eax
    2f3e:	41 89 bf 9c 01 00 00 	mov    %edi,0x19c(%r15)
    2f45:	bf 63 00 00 00       	mov    $0x63,%edi
    2f4a:	83 c0 01             	add    $0x1,%eax
    2f4d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    2f52:	83 e0 01             	and    $0x1,%eax
    2f55:	41 c7 07 41 00 00 00 	movl   $0x41,(%r15)
    2f5c:	41 89 87 98 01 00 00 	mov    %eax,0x198(%r15)
    2f63:	4d 89 97 90 01 00 00 	mov    %r10,0x190(%r15)
    2f6a:	41 c7 87 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%r15)
    2f75:	49 c7 87 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%r15)
    2f80:	e8 7b f4 ff ff       	call   2400 <calloc@plt>
    2f85:	49 c7 87 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%r15)
    2f90:	49 89 87 50 01 00 00 	mov    %rax,0x150(%r15)
    2f97:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    2f9c:	48 8b 00             	mov    (%rax),%rax
    2f9f:	8b 48 04             	mov    0x4(%rax),%ecx
    2fa2:	49 89 87 28 01 00 00 	mov    %rax,0x128(%r15)
    2fa9:	41 89 8f 30 01 00 00 	mov    %ecx,0x130(%r15)
    2fb0:	5a                   	pop    %rdx
    2fb1:	59                   	pop    %rcx
    2fb2:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    2fb7:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    2fbc:	48 39 f0             	cmp    %rsi,%rax
    2fbf:	0f 85 e8 13 00 00    	jne    43ad <main+0x1d3d>
    2fc5:	66 0f 6f 05 33 5d 00 00 	movdqa 0x5d33(%rip),%xmm0        # 8d00 <_IO_stdin_used+0xd00>
    2fcd:	48 8b 0d 44 5d 00 00 	mov    0x5d44(%rip),%rcx        # 8d18 <_IO_stdin_used+0xd18>
    2fd4:	49 83 c5 01          	add    $0x1,%r13
    2fd8:	45 89 67 04          	mov    %r12d,0x4(%r15)
    2fdc:	48 8d 05 9d 3b 00 00 	lea    0x3b9d(%rip),%rax        # 6b80 <barriered_work_ingest_andwork>
    2fe3:	41 c7 87 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r15)
    2fee:	49 89 8f 44 01 00 00 	mov    %rcx,0x144(%r15)
    2ff5:	41 c7 87 8c 01 00 00 02 00 00 00 	movl   $0x2,0x18c(%r15)
    3000:	49 89 87 18 01 00 00 	mov    %rax,0x118(%r15)
    3007:	41 0f 11 87 34 01 00 00 	movups %xmm0,0x134(%r15)
    300f:	49 83 fd 03          	cmp    $0x3,%r13
    3013:	0f 85 32 fc ff ff    	jne    2c4b <main+0x5db>
    3019:	c7 86 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%rsi)
    3023:	bf 01 00 00 00       	mov    $0x1,%edi
    3028:	4c 8b a4 24 d8 00 00 00 	mov    0xd8(%rsp),%r12
    3030:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    3035:	be 08 00 00 00       	mov    $0x8,%esi
    303a:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    303f:	e8 bc f3 ff ff       	call   2400 <calloc@plt>
    3044:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    3049:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    304e:	48 8b bc 24 b0 00 00 00 	mov    0xb0(%rsp),%rdi
    3056:	83 44 24 50 01       	addl   $0x1,0x50(%rsp)
    305b:	49 89 43 50          	mov    %rax,0x50(%r11)
    305f:	48 8b 0d b2 5c 00 00 	mov    0x5cb2(%rip),%rcx        # 8d18 <_IO_stdin_used+0xd18>
    3066:	49 81 c3 80 01 00 00 	add    $0x180,%r11
    306d:	66 0f 6f bc 24 a0 00 00 00 	movdqa 0xa0(%rsp),%xmm7
    3076:	48 89 38             	mov    %rdi,(%rax)
    3079:	48 83 c7 10          	add    $0x10,%rdi
    307d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    3082:	48 89 bc 24 b0 00 00 00 	mov    %rdi,0xb0(%rsp)
    308a:	8b bc 24 d4 00 00 00 	mov    0xd4(%rsp),%edi
    3091:	83 84 24 d0 00 00 00 01 	addl   $0x1,0xd0(%rsp)
    3099:	48 8b 00             	mov    (%rax),%rax
    309c:	0f 11 ba 18 05 00 00 	movups %xmm7,0x518(%rdx)
    30a3:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
    30ad:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
    30b4:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
    30be:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
    30c8:	41 8b 83 84 fe ff ff 	mov    -0x17c(%r11),%eax
    30cf:	c7 82 8c 05 00 00 02 00 00 00 	movl   $0x2,0x58c(%rdx)
    30d9:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
    30df:	8b 44 24 50          	mov    0x50(%rsp),%eax
    30e3:	48 89 8a 44 05 00 00 	mov    %rcx,0x544(%rdx)
    30ea:	39 f8                	cmp    %edi,%eax
    30ec:	0f 85 1f f9 ff ff    	jne    2a11 <main+0x3a1>
    30f2:	48 83 84 24 98 00 00 00 18 	addq   $0x18,0x98(%rsp)
    30fb:	48 85 db             	test   %rbx,%rbx
    30fe:	0f 85 0c 03 00 00    	jne    3410 <main+0xda0>
    3104:	bb 01 00 00 00       	mov    $0x1,%ebx
    3109:	e9 a8 f8 ff ff       	jmp    29b6 <main+0x346>
    310e:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    3113:	41 89 d5             	mov    %edx,%r13d
    3116:	49 89 c7             	mov    %rax,%r15
    3119:	44 89 ed             	mov    %r13d,%ebp
    311c:	31 c0                	xor    %eax,%eax
    311e:	44 89 ea             	mov    %r13d,%edx
    3121:	bf 01 00 00 00       	mov    $0x1,%edi
    3126:	d1 fd                	sar    %ebp
    3128:	48 8d 35 af 52 00 00 	lea    0x52af(%rip),%rsi        # 83de <_IO_stdin_used+0x3de>
    312f:	89 e9                	mov    %ebp,%ecx
    3131:	e8 7a f3 ff ff       	call   24b0 <__printf_chk@plt>
    3136:	39 dd                	cmp    %ebx,%ebp
    3138:	0f 84 5c 01 00 00    	je     329a <main+0xc2a>
    313e:	41 83 c5 01          	add    $0x1,%r13d
    3142:	49 81 c7 00 01 00 00 	add    $0x100,%r15
    3149:	41 83 fd 04          	cmp    $0x4,%r13d
    314d:	75 ca                	jne    3119 <main+0xaa9>
    314f:	e9 8b fb ff ff       	jmp    2cdf <main+0x66f>
    3154:	be 08 00 00 00       	mov    $0x8,%esi
    3159:	bf 01 00 00 00       	mov    $0x1,%edi
    315e:	e8 9d f2 ff ff       	call   2400 <calloc@plt>
    3163:	be 08 00 00 00       	mov    $0x8,%esi
    3168:	bf 01 00 00 00       	mov    $0x1,%edi
    316d:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    3175:	e8 86 f2 ff ff       	call   2400 <calloc@plt>
    317a:	be 80 04 00 00       	mov    $0x480,%esi
    317f:	bf 03 00 00 00       	mov    $0x3,%edi
    3184:	48 89 84 24 80 00 00 00 	mov    %rax,0x80(%rsp)
    318c:	e8 6f f2 ff ff       	call   2400 <calloc@plt>
    3191:	8b 7c 24 08          	mov    0x8(%rsp),%edi
    3195:	44 89 fa             	mov    %r15d,%edx
    3198:	49 c7 85 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r13)
    31a3:	49 89 c1             	mov    %rax,%r9
    31a6:	44 89 a0 10 04 00 00 	mov    %r12d,0x410(%rax)
    31ad:	48 8d 35 1c 56 00 00 	lea    0x561c(%rip),%rsi        # 87d0 <_IO_stdin_used+0x7d0>
    31b4:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
    31ba:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
    31c4:	44 89 b8 14 04 00 00 	mov    %r15d,0x414(%rax)
    31cb:	41 8d 46 01          	lea    0x1(%r14),%eax
    31cf:	41 89 81 98 08 00 00 	mov    %eax,0x898(%r9)
    31d6:	49 8d 81 80 04 00 00 	lea    0x480(%r9),%rax
    31dd:	49 89 85 80 00 00 00 	mov    %rax,0x80(%r13)
    31e4:	8b 44 24 50          	mov    0x50(%rsp),%eax
    31e8:	45 89 b1 18 04 00 00 	mov    %r14d,0x418(%r9)
    31ef:	41 83 c6 02          	add    $0x2,%r14d
    31f3:	8d 48 fe             	lea    -0x2(%rax),%ecx
    31f6:	41 89 b9 8c 08 00 00 	mov    %edi,0x88c(%r9)
    31fd:	31 c0                	xor    %eax,%eax
    31ff:	bf 01 00 00 00       	mov    $0x1,%edi
    3204:	41 c7 81 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r9)
    320f:	45 89 a1 90 08 00 00 	mov    %r12d,0x890(%r9)
    3216:	45 89 b9 94 08 00 00 	mov    %r15d,0x894(%r9)
    321d:	4d 89 4d 00          	mov    %r9,0x0(%r13)
    3221:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
    322c:	41 c7 81 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r9)
    3237:	49 c7 85 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r13)
    3242:	41 c7 85 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%r13)
    324d:	41 89 8d b4 00 00 00 	mov    %ecx,0xb4(%r13)
    3254:	4c 89 4c 24 58       	mov    %r9,0x58(%rsp)
    3259:	e8 52 f2 ff ff       	call   24b0 <__printf_chk@plt>
    325e:	4c 8b 4c 24 58       	mov    0x58(%rsp),%r9
    3263:	66 0f 6f 3d 85 5a 00 00 	movdqa 0x5a85(%rip),%xmm7        # 8cf0 <_IO_stdin_used+0xcf0>
    326b:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    3273:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
    327b:	41 0f 29 b9 80 00 00 00 	movaps %xmm7,0x80(%r9)
    3283:	4d 89 19             	mov    %r11,(%r9)
    3286:	4d 89 91 80 04 00 00 	mov    %r10,0x480(%r9)
    328d:	41 0f 29 b9 00 05 00 00 	movaps %xmm7,0x500(%r9)
    3295:	e9 34 fa ff ff       	jmp    2cce <main+0x65e>
    329a:	be 08 00 00 00       	mov    $0x8,%esi
    329f:	bf 01 00 00 00       	mov    $0x1,%edi
    32a4:	e8 57 f1 ff ff       	call   2400 <calloc@plt>
    32a9:	be 08 00 00 00       	mov    $0x8,%esi
    32ae:	bf 01 00 00 00       	mov    $0x1,%edi
    32b3:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    32bb:	e8 40 f1 ff ff       	call   2400 <calloc@plt>
    32c0:	be 80 04 00 00       	mov    $0x480,%esi
    32c5:	bf 03 00 00 00       	mov    $0x3,%edi
    32ca:	48 89 84 24 80 00 00 00 	mov    %rax,0x80(%rsp)
    32d2:	e8 29 f1 ff ff       	call   2400 <calloc@plt>
    32d7:	8b 7c 24 08          	mov    0x8(%rsp),%edi
    32db:	44 89 ea             	mov    %r13d,%edx
    32de:	49 c7 87 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r15)
    32e9:	49 89 c1             	mov    %rax,%r9
    32ec:	44 89 a0 10 04 00 00 	mov    %r12d,0x410(%rax)
    32f3:	48 8d 35 d6 54 00 00 	lea    0x54d6(%rip),%rsi        # 87d0 <_IO_stdin_used+0x7d0>
    32fa:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
    3300:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
    330a:	44 89 a8 14 04 00 00 	mov    %r13d,0x414(%rax)
    3311:	41 8d 46 01          	lea    0x1(%r14),%eax
    3315:	41 89 81 98 08 00 00 	mov    %eax,0x898(%r9)
    331c:	49 8d 81 80 04 00 00 	lea    0x480(%r9),%rax
    3323:	49 89 87 80 00 00 00 	mov    %rax,0x80(%r15)
    332a:	8b 44 24 50          	mov    0x50(%rsp),%eax
    332e:	45 89 b1 18 04 00 00 	mov    %r14d,0x418(%r9)
    3335:	41 83 c6 02          	add    $0x2,%r14d
    3339:	41 89 b9 8c 08 00 00 	mov    %edi,0x88c(%r9)
    3340:	89 c1                	mov    %eax,%ecx
    3342:	bf 01 00 00 00       	mov    $0x1,%edi
    3347:	41 c7 81 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r9)
    3352:	45 89 a1 90 08 00 00 	mov    %r12d,0x890(%r9)
    3359:	45 89 a9 94 08 00 00 	mov    %r13d,0x894(%r9)
    3360:	4d 89 0f             	mov    %r9,(%r15)
    3363:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
    336e:	41 c7 81 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r9)
    3379:	41 89 87 b4 00 00 00 	mov    %eax,0xb4(%r15)
    3380:	31 c0                	xor    %eax,%eax
    3382:	49 c7 87 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r15)
    338d:	41 c7 87 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%r15)
    3398:	4c 89 4c 24 58       	mov    %r9,0x58(%rsp)
    339d:	e8 0e f1 ff ff       	call   24b0 <__printf_chk@plt>
    33a2:	4c 8b 4c 24 58       	mov    0x58(%rsp),%r9
    33a7:	66 0f 6f 35 41 59 00 00 	movdqa 0x5941(%rip),%xmm6        # 8cf0 <_IO_stdin_used+0xcf0>
    33af:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    33b7:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
    33bf:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
    33c7:	4d 89 19             	mov    %r11,(%r9)
    33ca:	4d 89 91 80 04 00 00 	mov    %r10,0x480(%r9)
    33d1:	41 0f 29 b1 00 05 00 00 	movaps %xmm6,0x500(%r9)
    33d9:	e9 60 fd ff ff       	jmp    313e <main+0xace>
    33de:	8b 44 24 50          	mov    0x50(%rsp),%eax
    33e2:	4c 89 7c 24 60       	mov    %r15,0x60(%rsp)
    33e7:	45 31 c0             	xor    %r8d,%r8d
    33ea:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
    33ee:	89 c1                	mov    %eax,%ecx
    33f0:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    33f5:	48 c1 e2 07          	shl    $0x7,%rdx
    33f9:	48 01 c2             	add    %rax,%rdx
    33fc:	4c 89 d8             	mov    %r11,%rax
    33ff:	e9 92 f6 ff ff       	jmp    2a96 <main+0x426>
    3404:	49 81 09 ff 0f 00 00 	orq    $0xfff,(%r9)
    340b:	e9 28 f7 ff ff       	jmp    2b38 <main+0x4c8>
    3410:	be 08 00 00 00       	mov    $0x8,%esi
    3415:	bf 00 04 00 00       	mov    $0x400,%edi
    341a:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    341f:	31 ed                	xor    %ebp,%ebp
    3421:	e8 da ef ff ff       	call   2400 <calloc@plt>
    3426:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    342b:	49 89 c7             	mov    %rax,%r15
    342e:	31 c0                	xor    %eax,%eax
    3430:	49 89 d1             	mov    %rdx,%r9
    3433:	45 31 db             	xor    %r11d,%r11d
    3436:	45 8b 51 40          	mov    0x40(%r9),%r10d
    343a:	45 85 d2             	test   %r10d,%r10d
    343d:	7e 7d                	jle    34bc <main+0xe4c>
    343f:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3443:	4d 63 c2             	movslq %r10d,%r8
    3446:	48 63 cd             	movslq %ebp,%rcx
    3449:	49 c1 e0 09          	shl    $0x9,%r8
    344d:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    3451:	49 01 f8             	add    %rdi,%r8
    3454:	0f 1f 40 00          	nopl   0x0(%rax)
    3458:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
    345f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3466:	48 83 c6 40          	add    $0x40,%rsi
    346a:	f3 0f 7e 91 00 01 00 00 	movq   0x100(%rcx),%xmm2
    3472:	f3 0f 7e 19          	movq   (%rcx),%xmm3
    3476:	f3 0f 7e 89 00 02 00 00 	movq   0x200(%rcx),%xmm1
    347e:	f3 0f 7e 81 00 03 00 00 	movq   0x300(%rcx),%xmm0
    3486:	0f 16 91 80 01 00 00 	movhps 0x180(%rcx),%xmm2
    348d:	0f 16 99 80 00 00 00 	movhps 0x80(%rcx),%xmm3
    3494:	0f 16 89 80 02 00 00 	movhps 0x280(%rcx),%xmm1
    349b:	0f 16 81 80 03 00 00 	movhps 0x380(%rcx),%xmm0
    34a2:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    34a6:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    34aa:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    34ae:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
    34b2:	49 39 f8             	cmp    %rdi,%r8
    34b5:	75 a1                	jne    3458 <main+0xde8>
    34b7:	42 8d 6c d5 00       	lea    0x0(%rbp,%r10,8),%ebp
    34bc:	49 81 c1 80 01 00 00 	add    $0x180,%r9
    34c3:	45 85 db             	test   %r11d,%r11d
    34c6:	75 0b                	jne    34d3 <main+0xe63>
    34c8:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    34ce:	e9 63 ff ff ff       	jmp    3436 <main+0xdc6>
    34d3:	83 c0 02             	add    $0x2,%eax
    34d6:	48 81 c2 00 03 00 00 	add    $0x300,%rdx
    34dd:	83 f8 04             	cmp    $0x4,%eax
    34e0:	0f 85 4a ff ff ff    	jne    3430 <main+0xdc0>
    34e6:	48 8d 3d 1f 4f 00 00 	lea    0x4f1f(%rip),%rdi        # 840c <_IO_stdin_used+0x40c>
    34ed:	44 89 5c 24 10       	mov    %r11d,0x10(%rsp)
    34f2:	e8 39 ee ff ff       	call   2330 <puts@plt>
    34f7:	48 8d 35 23 4f 00 00 	lea    0x4f23(%rip),%rsi        # 8421 <_IO_stdin_used+0x421>
    34fe:	48 8d 3d 1e 4f 00 00 	lea    0x4f1e(%rip),%rdi        # 8423 <_IO_stdin_used+0x423>
    3505:	e8 e6 ef ff ff       	call   24f0 <fopen@plt>
    350a:	49 89 c6             	mov    %rax,%r14
    350d:	85 ed                	test   %ebp,%ebp
    350f:	7e 6f                	jle    3580 <main+0xf10>
    3511:	48 63 ed             	movslq %ebp,%rbp
    3514:	4c 8d 25 e5 4e 00 00 	lea    0x4ee5(%rip),%r12        # 8400 <_IO_stdin_used+0x400>
    351b:	4d 8d 2c ef          	lea    (%r15,%rbp,8),%r13
    351f:	48 8d 2d 1e 4f 00 00 	lea    0x4f1e(%rip),%rbp        # 8444 <_IO_stdin_used+0x444>
    3526:	be 01 00 00 00       	mov    $0x1,%esi
    352b:	bf fa 00 00 00       	mov    $0xfa,%edi
    3530:	49 83 c7 08          	add    $0x8,%r15
    3534:	e8 c7 ee ff ff       	call   2400 <calloc@plt>
    3539:	4c 89 e1             	mov    %r12,%rcx
    353c:	ba fa 00 00 00       	mov    $0xfa,%edx
    3541:	be 01 00 00 00       	mov    $0x1,%esi
    3546:	48 89 c3             	mov    %rax,%rbx
    3549:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    354d:	48 89 df             	mov    %rbx,%rdi
    3550:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3557:	31 c0                	xor    %eax,%eax
    3559:	e8 42 f0 ff ff       	call   25a0 <__sprintf_chk@plt>
    355e:	48 89 da             	mov    %rbx,%rdx
    3561:	48 89 ee             	mov    %rbp,%rsi
    3564:	bf 01 00 00 00       	mov    $0x1,%edi
    3569:	31 c0                	xor    %eax,%eax
    356b:	e8 40 ef ff ff       	call   24b0 <__printf_chk@plt>
    3570:	4c 89 f6             	mov    %r14,%rsi
    3573:	48 89 df             	mov    %rbx,%rdi
    3576:	e8 45 ee ff ff       	call   23c0 <fputs@plt>
    357b:	4d 39 fd             	cmp    %r15,%r13
    357e:	75 a6                	jne    3526 <main+0xeb6>
    3580:	4c 89 f7             	mov    %r14,%rdi
    3583:	31 ed                	xor    %ebp,%ebp
    3585:	4c 8d 25 e2 4e 00 00 	lea    0x4ee2(%rip),%r12        # 846e <_IO_stdin_used+0x46e>
    358c:	e8 cf ed ff ff       	call   2360 <fclose@plt>
    3591:	48 8d 3d 94 4e 00 00 	lea    0x4e94(%rip),%rdi        # 842c <_IO_stdin_used+0x42c>
    3598:	e8 93 ed ff ff       	call   2330 <puts@plt>
    359d:	89 ea                	mov    %ebp,%edx
    359f:	48 8d 35 a1 4e 00 00 	lea    0x4ea1(%rip),%rsi        # 8447 <_IO_stdin_used+0x447>
    35a6:	bf 01 00 00 00       	mov    $0x1,%edi
    35ab:	31 c0                	xor    %eax,%eax
    35ad:	e8 fe ee ff ff       	call   24b0 <__printf_chk@plt>
    35b2:	49 89 ed             	mov    %rbp,%r13
    35b5:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    35ba:	31 db                	xor    %ebx,%ebx
    35bc:	49 f7 dd             	neg    %r13
    35bf:	44 8d 74 2d 00       	lea    0x0(%rbp,%rbp,1),%r14d
    35c4:	41 81 e5 00 03 00 00 	and    $0x300,%r13d
    35cb:	45 89 f7             	mov    %r14d,%r15d
    35ce:	49 89 ee             	mov    %rbp,%r14
    35d1:	49 01 c5             	add    %rax,%r13
    35d4:	42 8d 0c 3b          	lea    (%rbx,%r15,1),%ecx
    35d8:	89 da                	mov    %ebx,%edx
    35da:	48 8d 35 70 4e 00 00 	lea    0x4e70(%rip),%rsi        # 8451 <_IO_stdin_used+0x451>
    35e1:	31 c0                	xor    %eax,%eax
    35e3:	bf 01 00 00 00       	mov    $0x1,%edi
    35e8:	31 ed                	xor    %ebp,%ebp
    35ea:	e8 c1 ee ff ff       	call   24b0 <__printf_chk@plt>
    35ef:	89 5c 24 20          	mov    %ebx,0x20(%rsp)
    35f3:	44 89 7c 24 28       	mov    %r15d,0x28(%rsp)
    35f8:	89 ea                	mov    %ebp,%edx
    35fa:	48 8d 35 62 4e 00 00 	lea    0x4e62(%rip),%rsi        # 8463 <_IO_stdin_used+0x463>
    3601:	bf 01 00 00 00       	mov    $0x1,%edi
    3606:	31 c0                	xor    %eax,%eax
    3608:	e8 a3 ee ff ff       	call   24b0 <__printf_chk@plt>
    360d:	48 89 6c 24 08       	mov    %rbp,0x8(%rsp)
    3612:	48 89 eb             	mov    %rbp,%rbx
    3615:	45 31 ff             	xor    %r15d,%r15d
    3618:	48 c1 e3 09          	shl    $0x9,%rbx
    361c:	be 01 00 00 00       	mov    $0x1,%esi
    3621:	bf 64 00 00 00       	mov    $0x64,%edi
    3626:	44 89 fd             	mov    %r15d,%ebp
    3629:	e8 d2 ed ff ff       	call   2400 <calloc@plt>
    362e:	4d 8b 45 38          	mov    0x38(%r13),%r8
    3632:	4c 89 ff             	mov    %r15,%rdi
    3635:	48 89 c1             	mov    %rax,%rcx
    3638:	48 c1 e7 08          	shl    $0x8,%rdi
    363c:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3644:	48 01 f8             	add    %rdi,%rax
    3647:	8b b0 b0 00 00 00    	mov    0xb0(%rax),%esi
    364d:	83 fe 02             	cmp    $0x2,%esi
    3650:	74 57                	je     36a9 <main+0x1039>
    3652:	83 fe 01             	cmp    $0x1,%esi
    3655:	74 6c                	je     36c3 <main+0x1053>
    3657:	44 8b 80 b4 00 00 00 	mov    0xb4(%rax),%r8d
    365e:	89 ea                	mov    %ebp,%edx
    3660:	4c 89 e6             	mov    %r12,%rsi
    3663:	31 c0                	xor    %eax,%eax
    3665:	bf 01 00 00 00       	mov    $0x1,%edi
    366a:	49 83 c7 01          	add    $0x1,%r15
    366e:	e8 3d ee ff ff       	call   24b0 <__printf_chk@plt>
    3673:	49 83 ff 04          	cmp    $0x4,%r15
    3677:	75 a3                	jne    361c <main+0xfac>
    3679:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    367e:	48 83 c5 01          	add    $0x1,%rbp
    3682:	48 83 fd 03          	cmp    $0x3,%rbp
    3686:	0f 85 6c ff ff ff    	jne    35f8 <main+0xf88>
    368c:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    3690:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
    3695:	49 81 c5 80 01 00 00 	add    $0x180,%r13
    369c:	85 db                	test   %ebx,%ebx
    369e:	75 40                	jne    36e0 <main+0x1070>
    36a0:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    36a4:	e9 2b ff ff ff       	jmp    35d4 <main+0xf64>
    36a9:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    36b3:	48 89 01             	mov    %rax,(%rcx)
    36b6:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    36be:	48 01 f8             	add    %rdi,%rax
    36c1:	eb 94                	jmp    3657 <main+0xfe7>
    36c3:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    36c9:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    36d0:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    36d8:	48 01 f8             	add    %rdi,%rax
    36db:	e9 77 ff ff ff       	jmp    3657 <main+0xfe7>
    36e0:	4d 85 f6             	test   %r14,%r14
    36e3:	75 0a                	jne    36ef <main+0x107f>
    36e5:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    36ea:	e9 ae fe ff ff       	jmp    359d <main+0xf2d>
    36ef:	ba 05 00 00 00       	mov    $0x5,%edx
    36f4:	bf 01 00 00 00       	mov    $0x1,%edi
    36f9:	31 c0                	xor    %eax,%eax
    36fb:	41 89 df             	mov    %ebx,%r15d
    36fe:	48 8d 35 84 4d 00 00 	lea    0x4d84(%rip),%rsi        # 8489 <_IO_stdin_used+0x489>
    3705:	4c 89 74 24 58       	mov    %r14,0x58(%rsp)
    370a:	e8 a1 ed ff ff       	call   24b0 <__printf_chk@plt>
    370f:	be 08 00 00 00       	mov    $0x8,%esi
    3714:	bf 02 00 00 00       	mov    $0x2,%edi
    3719:	e8 e2 ec ff ff       	call   2400 <calloc@plt>
    371e:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    3723:	be 38 00 00 00       	mov    $0x38,%esi
    3728:	bf 08 00 00 00       	mov    $0x8,%edi
    372d:	4d 8d a6 80 07 00 00 	lea    0x780(%r14),%r12
    3734:	4c 89 70 08          	mov    %r14,0x8(%rax)
    3738:	4d 8d ae 80 01 00 00 	lea    0x180(%r14),%r13
    373f:	49 89 86 98 07 00 00 	mov    %rax,0x798(%r14)
    3746:	4c 89 20             	mov    %r12,(%rax)
    3749:	49 8b 46 38          	mov    0x38(%r14),%rax
    374d:	41 c7 86 a8 07 00 00 02 00 00 00 	movl   $0x2,0x7a8(%r14)
    3758:	41 c7 86 84 07 00 00 00 00 00 00 	movl   $0x0,0x784(%r14)
    3763:	41 c7 86 c0 07 00 00 03 00 00 00 	movl   $0x3,0x7c0(%r14)
    376e:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3778:	49 8b 86 b8 01 00 00 	mov    0x1b8(%r14),%rax
    377f:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3789:	e8 72 ec ff ff       	call   2400 <calloc@plt>
    378e:	be 38 00 00 00       	mov    $0x38,%esi
    3793:	bf 08 00 00 00       	mov    $0x8,%edi
    3798:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    379d:	e8 5e ec ff ff       	call   2400 <calloc@plt>
    37a2:	be 38 00 00 00       	mov    $0x38,%esi
    37a7:	bf 08 00 00 00       	mov    $0x8,%edi
    37ac:	48 89 c5             	mov    %rax,%rbp
    37af:	e8 4c ec ff ff       	call   2400 <calloc@plt>
    37b4:	be 38 00 00 00       	mov    $0x38,%esi
    37b9:	bf 08 00 00 00       	mov    $0x8,%edi
    37be:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    37c3:	e8 38 ec ff ff       	call   2400 <calloc@plt>
    37c8:	be 08 00 00 00       	mov    $0x8,%esi
    37cd:	bf 08 00 00 00       	mov    $0x8,%edi
    37d2:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    37d7:	e8 24 ec ff ff       	call   2400 <calloc@plt>
    37dc:	be 08 00 00 00       	mov    $0x8,%esi
    37e1:	bf 08 00 00 00       	mov    $0x8,%edi
    37e6:	41 c7 86 0c 06 00 00 00 00 00 00 	movl   $0x0,0x60c(%r14)
    37f1:	48 89 c3             	mov    %rax,%rbx
    37f4:	48 8b 05 25 55 00 00 	mov    0x5525(%rip),%rax        # 8d20 <_IO_stdin_used+0xd20>
    37fb:	49 89 86 40 06 00 00 	mov    %rax,0x640(%r14)
    3802:	e8 f9 eb ff ff       	call   2400 <calloc@plt>
    3807:	49 8d 96 00 03 00 00 	lea    0x300(%r14),%rdx
    380e:	4c 89 f7             	mov    %r14,%rdi
    3811:	49 8d 8e 00 06 00 00 	lea    0x600(%r14),%rcx
    3818:	48 89 50 10          	mov    %rdx,0x10(%rax)
    381c:	49 8d 96 80 04 00 00 	lea    0x480(%r14),%rdx
    3823:	48 8d 35 6e 4c 00 00 	lea    0x4c6e(%rip),%rsi        # 8498 <_IO_stdin_used+0x498>
    382a:	4c 89 30             	mov    %r14,(%rax)
    382d:	4d 8d b6 00 09 00 00 	lea    0x900(%r14),%r14
    3834:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3838:	48 8d 97 80 0a 00 00 	lea    0xa80(%rdi),%rdx
    383f:	4c 89 68 08          	mov    %r13,0x8(%rax)
    3843:	48 89 48 20          	mov    %rcx,0x20(%rax)
    3847:	4c 89 70 30          	mov    %r14,0x30(%rax)
    384b:	48 89 50 38          	mov    %rdx,0x38(%rax)
    384f:	ba 04 00 00 00       	mov    $0x4,%edx
    3854:	48 89 87 18 06 00 00 	mov    %rax,0x618(%rdi)
    385b:	4c 89 60 28          	mov    %r12,0x28(%rax)
    385f:	48 8b 05 c2 54 00 00 	mov    0x54c2(%rip),%rax        # 8d28 <_IO_stdin_used+0xd28>
    3866:	c7 87 30 06 00 00 04 00 00 00 	movl   $0x4,0x630(%rdi)
    3870:	48 89 87 28 06 00 00 	mov    %rax,0x628(%rdi)
    3877:	31 c0                	xor    %eax,%eax
    3879:	c7 87 04 06 00 00 00 00 00 00 	movl   $0x0,0x604(%rdi)
    3883:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
    3888:	bf 01 00 00 00       	mov    $0x1,%edi
    388d:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    3892:	e8 19 ec ff ff       	call   24b0 <__printf_chk@plt>
    3897:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    389c:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
    38a0:	48 8d b5 e0 00 00 00 	lea    0xe0(%rbp),%rsi
    38a7:	48 8d 15 c2 0d 00 00 	lea    0xdc2(%rip),%rdx        # 4670 <timer_thread>
    38ae:	31 ed                	xor    %ebp,%ebp
    38b0:	e8 1b ec ff ff       	call   24d0 <pthread_create@plt>
    38b5:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    38ba:	48 89 d9             	mov    %rbx,%rcx
    38bd:	4c 89 e6             	mov    %r12,%rsi
    38c0:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    38c5:	41 b9 02 00 00 00    	mov    $0x2,%r9d
    38cb:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    38d0:	4c 89 74 24 28       	mov    %r14,0x28(%rsp)
    38d5:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    38da:	45 89 ce             	mov    %r9d,%r14d
    38dd:	41 89 ed             	mov    %ebp,%r13d
    38e0:	48 89 c7             	mov    %rax,%rdi
    38e3:	44 89 f8             	mov    %r15d,%eax
    38e6:	49 89 ff             	mov    %rdi,%r15
    38e9:	89 44 24 40          	mov    %eax,0x40(%rsp)
    38ed:	47 8d 64 2d 00       	lea    0x0(%r13,%r13,1),%r12d
    38f2:	48 89 cd             	mov    %rcx,%rbp
    38f5:	48 89 d3             	mov    %rdx,%rbx
    38f8:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    38fd:	48 89 54 24 60       	mov    %rdx,0x60(%rsp)
    3902:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    3907:	4c 89 7c 24 48       	mov    %r15,0x48(%rsp)
    390c:	49 89 f7             	mov    %rsi,%r15
    390f:	c7 43 0c 01 00 00 00 	movl   $0x1,0xc(%rbx)
    3916:	44 89 e2             	mov    %r12d,%edx
    3919:	44 89 e9             	mov    %r13d,%ecx
    391c:	31 c0                	xor    %eax,%eax
    391e:	c7 43 44 01 00 00 00 	movl   $0x1,0x44(%rbx)
    3925:	48 8d 35 fc 4e 00 00 	lea    0x4efc(%rip),%rsi        # 8828 <_IO_stdin_used+0x828>
    392c:	bf 01 00 00 00       	mov    $0x1,%edi
    3931:	41 83 c4 01          	add    $0x1,%r12d
    3935:	e8 76 eb ff ff       	call   24b0 <__printf_chk@plt>
    393a:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    393f:	48 89 d9             	mov    %rbx,%rcx
    3942:	48 89 ef             	mov    %rbp,%rdi
    3945:	48 8d 15 44 33 00 00 	lea    0x3344(%rip),%rdx        # 6c90 <barriered_thread>
    394c:	48 81 c3 80 01 00 00 	add    $0x180,%rbx
    3953:	48 83 c5 08          	add    $0x8,%rbp
    3957:	e8 74 eb ff ff       	call   24d0 <pthread_create@plt>
    395c:	48 8b 93 30 ff ff ff 	mov    -0xd0(%rbx),%rdx
    3963:	48 8b 7d f8          	mov    -0x8(%rbp),%rdi
    3967:	be 08 00 00 00       	mov    $0x8,%esi
    396c:	e8 af e9 ff ff       	call   2320 <pthread_setaffinity_np@plt>
    3971:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3977:	45 39 e6             	cmp    %r12d,%r14d
    397a:	75 93                	jne    390f <main+0x129f>
    397c:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    3981:	4c 89 fe             	mov    %r15,%rsi
    3984:	8b 44 24 40          	mov    0x40(%rsp),%eax
    3988:	41 83 c6 02          	add    $0x2,%r14d
    398c:	4c 8b 7c 24 48       	mov    0x48(%rsp),%r15
    3991:	48 8b 54 24 60       	mov    0x60(%rsp),%rdx
    3996:	48 83 c1 10          	add    $0x10,%rcx
    399a:	48 81 c2 00 03 00 00 	add    $0x300,%rdx
    39a1:	49 83 c7 70          	add    $0x70,%r15
    39a5:	45 85 ed             	test   %r13d,%r13d
    39a8:	75 08                	jne    39b2 <main+0x1342>
    39aa:	41 89 c5             	mov    %eax,%r13d
    39ad:	e9 37 ff ff ff       	jmp    38e9 <main+0x1279>
    39b2:	4c 8b 7c 24 38       	mov    0x38(%rsp),%r15
    39b7:	49 89 f4             	mov    %rsi,%r12
    39ba:	bf 01 00 00 00       	mov    $0x1,%edi
    39bf:	44 89 ed             	mov    %r13d,%ebp
    39c2:	be d8 00 00 00       	mov    $0xd8,%esi
    39c7:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    39cc:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    39d1:	48 8b 05 58 53 00 00 	mov    0x5358(%rip),%rax        # 8d30 <_IO_stdin_used+0xd30>
    39d8:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    39dd:	41 c7 87 8c 07 00 00 02 00 00 00 	movl   $0x2,0x78c(%r15)
    39e8:	49 89 87 c0 07 00 00 	mov    %rax,0x7c0(%r15)
    39ef:	e8 0c ea ff ff       	call   2400 <calloc@plt>
    39f4:	be 00 08 00 00       	mov    $0x800,%esi
    39f9:	31 ff                	xor    %edi,%edi
    39fb:	49 89 87 d8 07 00 00 	mov    %rax,0x7d8(%r15)
    3a02:	e8 19 eb ff ff       	call   2520 <eventfd@plt>
    3a07:	be 08 00 00 00       	mov    $0x8,%esi
    3a0c:	bf 02 00 00 00       	mov    $0x2,%edi
    3a11:	41 89 87 e0 07 00 00 	mov    %eax,0x7e0(%r15)
    3a18:	e8 e3 e9 ff ff       	call   2400 <calloc@plt>
    3a1d:	ba 05 00 00 00       	mov    $0x5,%edx
    3a22:	bf 01 00 00 00       	mov    $0x1,%edi
    3a27:	41 c7 87 a8 07 00 00 02 00 00 00 	movl   $0x2,0x7a8(%r15)
    3a32:	4c 89 38             	mov    %r15,(%rax)
    3a35:	48 8d 35 7a 4a 00 00 	lea    0x4a7a(%rip),%rsi        # 84b6 <_IO_stdin_used+0x4b6>
    3a3c:	49 89 87 98 07 00 00 	mov    %rax,0x798(%r15)
    3a43:	4c 89 68 08          	mov    %r13,0x8(%rax)
    3a47:	31 c0                	xor    %eax,%eax
    3a49:	41 c7 87 84 07 00 00 05 00 00 00 	movl   $0x5,0x784(%r15)
    3a54:	4d 89 f7             	mov    %r14,%r15
    3a57:	41 be 06 00 00 00    	mov    $0x6,%r14d
    3a5d:	e8 4e ea ff ff       	call   24b0 <__printf_chk@plt>
    3a62:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    3a67:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
    3a6b:	4c 89 e1             	mov    %r12,%rcx
    3a6e:	48 8d 15 8b 1f 00 00 	lea    0x1f8b(%rip),%rdx        # 5a00 <io_thread>
    3a75:	4c 8d 63 30          	lea    0x30(%rbx),%r12
    3a79:	48 81 c6 18 01 00 00 	add    $0x118,%rsi
    3a80:	e8 4b ea ff ff       	call   24d0 <pthread_create@plt>
    3a85:	ba 06 00 00 00       	mov    $0x6,%edx
    3a8a:	48 8d 35 3c 4a 00 00 	lea    0x4a3c(%rip),%rsi        # 84cd <_IO_stdin_used+0x4cd>
    3a91:	31 c0                	xor    %eax,%eax
    3a93:	bf 01 00 00 00       	mov    $0x1,%edi
    3a98:	e8 13 ea ff ff       	call   24b0 <__printf_chk@plt>
    3a9d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3aa2:	48 05 50 01 00 00    	add    $0x150,%rax
    3aa8:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3aad:	89 e8                	mov    %ebp,%eax
    3aaf:	48 89 dd             	mov    %rbx,%rbp
    3ab2:	89 c3                	mov    %eax,%ebx
    3ab4:	44 89 f2             	mov    %r14d,%edx
    3ab7:	48 8d 35 25 4a 00 00 	lea    0x4a25(%rip),%rsi        # 84e3 <_IO_stdin_used+0x4e3>
    3abe:	bf 01 00 00 00       	mov    $0x1,%edi
    3ac3:	31 c0                	xor    %eax,%eax
    3ac5:	e8 e6 e9 ff ff       	call   24b0 <__printf_chk@plt>
    3aca:	be 08 00 00 00       	mov    $0x8,%esi
    3acf:	bf 01 00 00 00       	mov    $0x1,%edi
    3ad4:	48 8b 05 55 52 00 00 	mov    0x5255(%rip),%rax        # 8d30 <_IO_stdin_used+0xd30>
    3adb:	41 c7 47 0c 03 00 00 00 	movl   $0x3,0xc(%r15)
    3ae3:	49 89 47 40          	mov    %rax,0x40(%r15)
    3ae7:	e8 14 e9 ff ff       	call   2400 <calloc@plt>
    3aec:	48 8b bc 24 90 00 00 00 	mov    0x90(%rsp),%rdi
    3af4:	be 08 00 00 00       	mov    $0x8,%esi
    3af9:	41 c7 87 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r15)
    3b04:	49 89 47 50          	mov    %rax,0x50(%r15)
    3b08:	48 89 38             	mov    %rdi,(%rax)
    3b0b:	bf 02 00 00 00       	mov    $0x2,%edi
    3b10:	e8 eb e8 ff ff       	call   2400 <calloc@plt>
    3b15:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    3b1a:	4c 89 f9             	mov    %r15,%rcx
    3b1d:	4c 89 e7             	mov    %r12,%rdi
    3b20:	49 89 47 18          	mov    %rax,0x18(%r15)
    3b24:	48 8d 15 35 0a 00 00 	lea    0xa35(%rip),%rdx        # 4560 <external_thread>
    3b2b:	49 83 c4 08          	add    $0x8,%r12
    3b2f:	49 81 c7 80 01 00 00 	add    $0x180,%r15
    3b36:	48 89 30             	mov    %rsi,(%rax)
    3b39:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3b3e:	4c 89 68 08          	mov    %r13,0x8(%rax)
    3b42:	48 8b 05 c7 51 00 00 	mov    0x51c7(%rip),%rax        # 8d10 <_IO_stdin_used+0xd10>
    3b49:	45 89 b7 84 fe ff ff 	mov    %r14d,-0x17c(%r15)
    3b50:	49 89 87 a8 fe ff ff 	mov    %rax,-0x158(%r15)
    3b57:	e8 74 e9 ff ff       	call   24d0 <pthread_create@plt>
    3b5c:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3b62:	48 83 84 24 90 00 00 00 10 	addq   $0x10,0x90(%rsp)
    3b6b:	41 83 fe 06          	cmp    $0x6,%r14d
    3b6f:	75 0b                	jne    3b7c <main+0x150c>
    3b71:	41 be 07 00 00 00    	mov    $0x7,%r14d
    3b77:	e9 38 ff ff ff       	jmp    3ab4 <main+0x1444>
    3b7c:	89 d8                	mov    %ebx,%eax
    3b7e:	48 89 eb             	mov    %rbp,%rbx
    3b81:	4c 8d 25 78 49 00 00 	lea    0x4978(%rip),%r12        # 8500 <_IO_stdin_used+0x500>
    3b88:	89 c5                	mov    %eax,%ebp
    3b8a:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3b8f:	4c 8d 78 04          	lea    0x4(%rax),%r15
    3b93:	4c 8d a8 04 0c 00 00 	lea    0xc04(%rax),%r13
    3b9a:	41 8b 4f 04          	mov    0x4(%r15),%ecx
    3b9e:	41 8b 17             	mov    (%r15),%edx
    3ba1:	4c 89 e6             	mov    %r12,%rsi
    3ba4:	bf 01 00 00 00       	mov    $0x1,%edi
    3ba9:	31 c0                	xor    %eax,%eax
    3bab:	49 81 c7 80 01 00 00 	add    $0x180,%r15
    3bb2:	e8 f9 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3bb7:	4d 39 fd             	cmp    %r15,%r13
    3bba:	75 de                	jne    3b9a <main+0x152a>
    3bbc:	48 8d 3d 50 49 00 00 	lea    0x4950(%rip),%rdi        # 8513 <_IO_stdin_used+0x513>
    3bc3:	45 31 ff             	xor    %r15d,%r15d
    3bc6:	4c 8d ac 24 e0 00 00 00 	lea    0xe0(%rsp),%r13
    3bce:	e8 5d e7 ff ff       	call   2330 <puts@plt>
    3bd3:	4c 8d 25 57 49 00 00 	lea    0x4957(%rip),%r12        # 8531 <_IO_stdin_used+0x531>
    3bda:	4a 8b 3c fb          	mov    (%rbx,%r15,8),%rdi
    3bde:	4c 89 ee             	mov    %r13,%rsi
    3be1:	e8 7a e9 ff ff       	call   2560 <pthread_join@plt>
    3be6:	44 89 fa             	mov    %r15d,%edx
    3be9:	4c 89 e6             	mov    %r12,%rsi
    3bec:	bf 01 00 00 00       	mov    $0x1,%edi
    3bf1:	31 c0                	xor    %eax,%eax
    3bf3:	49 83 c7 01          	add    $0x1,%r15
    3bf7:	e8 b4 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3bfc:	49 83 ff 08          	cmp    $0x8,%r15
    3c00:	75 d8                	jne    3bda <main+0x156a>
    3c02:	be 08 00 00 00       	mov    $0x8,%esi
    3c07:	bf 00 04 00 00       	mov    $0x400,%edi
    3c0c:	45 31 e4             	xor    %r12d,%r12d
    3c0f:	e8 ec e7 ff ff       	call   2400 <calloc@plt>
    3c14:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3c19:	49 89 c6             	mov    %rax,%r14
    3c1c:	31 c0                	xor    %eax,%eax
    3c1e:	49 89 d1             	mov    %rdx,%r9
    3c21:	45 31 db             	xor    %r11d,%r11d
    3c24:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3c28:	45 85 d2             	test   %r10d,%r10d
    3c2b:	7e 7e                	jle    3cab <main+0x163b>
    3c2d:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3c31:	4d 63 c2             	movslq %r10d,%r8
    3c34:	49 63 cc             	movslq %r12d,%rcx
    3c37:	49 c1 e0 09          	shl    $0x9,%r8
    3c3b:	49 8d 34 ce          	lea    (%r14,%rcx,8),%rsi
    3c3f:	49 01 f8             	add    %rdi,%r8
    3c42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c48:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
    3c4f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3c56:	48 83 c6 40          	add    $0x40,%rsi
    3c5a:	f3 0f 7e 91 00 01 00 00 	movq   0x100(%rcx),%xmm2
    3c62:	f3 0f 7e 19          	movq   (%rcx),%xmm3
    3c66:	f3 0f 7e 89 00 02 00 00 	movq   0x200(%rcx),%xmm1
    3c6e:	f3 0f 7e 81 00 03 00 00 	movq   0x300(%rcx),%xmm0
    3c76:	0f 16 91 80 01 00 00 	movhps 0x180(%rcx),%xmm2
    3c7d:	0f 16 99 80 00 00 00 	movhps 0x80(%rcx),%xmm3
    3c84:	0f 16 89 80 02 00 00 	movhps 0x280(%rcx),%xmm1
    3c8b:	0f 16 81 80 03 00 00 	movhps 0x380(%rcx),%xmm0
    3c92:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3c96:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3c9a:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3c9e:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
    3ca2:	49 39 f8             	cmp    %rdi,%r8
    3ca5:	75 a1                	jne    3c48 <main+0x15d8>
    3ca7:	47 8d 24 d4          	lea    (%r12,%r10,8),%r12d
    3cab:	49 81 c1 80 01 00 00 	add    $0x180,%r9
    3cb2:	45 85 db             	test   %r11d,%r11d
    3cb5:	75 08                	jne    3cbf <main+0x164f>
    3cb7:	41 89 eb             	mov    %ebp,%r11d
    3cba:	e9 65 ff ff ff       	jmp    3c24 <main+0x15b4>
    3cbf:	83 c0 02             	add    $0x2,%eax
    3cc2:	48 81 c2 00 03 00 00 	add    $0x300,%rdx
    3cc9:	83 f8 04             	cmp    $0x4,%eax
    3ccc:	0f 85 4c ff ff ff    	jne    3c1e <main+0x15ae>
    3cd2:	48 8d 3d 6c 48 00 00 	lea    0x486c(%rip),%rdi        # 8545 <_IO_stdin_used+0x545>
    3cd9:	e8 52 e6 ff ff       	call   2330 <puts@plt>
    3cde:	48 8d 35 3c 47 00 00 	lea    0x473c(%rip),%rsi        # 8421 <_IO_stdin_used+0x421>
    3ce5:	48 8d 3d 71 48 00 00 	lea    0x4871(%rip),%rdi        # 855d <_IO_stdin_used+0x55d>
    3cec:	e8 ff e7 ff ff       	call   24f0 <fopen@plt>
    3cf1:	49 89 c7             	mov    %rax,%r15
    3cf4:	45 85 e4             	test   %r12d,%r12d
    3cf7:	7e 6f                	jle    3d68 <main+0x16f8>
    3cf9:	4d 63 e4             	movslq %r12d,%r12
    3cfc:	48 8d 2d 41 47 00 00 	lea    0x4741(%rip),%rbp        # 8444 <_IO_stdin_used+0x444>
    3d03:	4f 8d 2c e6          	lea    (%r14,%r12,8),%r13
    3d07:	4c 8d 25 f2 46 00 00 	lea    0x46f2(%rip),%r12        # 8400 <_IO_stdin_used+0x400>
    3d0e:	be 01 00 00 00       	mov    $0x1,%esi
    3d13:	bf fa 00 00 00       	mov    $0xfa,%edi
    3d18:	49 83 c6 08          	add    $0x8,%r14
    3d1c:	e8 df e6 ff ff       	call   2400 <calloc@plt>
    3d21:	4c 89 e1             	mov    %r12,%rcx
    3d24:	ba fa 00 00 00       	mov    $0xfa,%edx
    3d29:	be 01 00 00 00       	mov    $0x1,%esi
    3d2e:	48 89 c3             	mov    %rax,%rbx
    3d31:	49 8b 46 f8          	mov    -0x8(%r14),%rax
    3d35:	48 89 df             	mov    %rbx,%rdi
    3d38:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3d3f:	31 c0                	xor    %eax,%eax
    3d41:	e8 5a e8 ff ff       	call   25a0 <__sprintf_chk@plt>
    3d46:	48 89 da             	mov    %rbx,%rdx
    3d49:	48 89 ee             	mov    %rbp,%rsi
    3d4c:	bf 01 00 00 00       	mov    $0x1,%edi
    3d51:	31 c0                	xor    %eax,%eax
    3d53:	e8 58 e7 ff ff       	call   24b0 <__printf_chk@plt>
    3d58:	4c 89 fe             	mov    %r15,%rsi
    3d5b:	48 89 df             	mov    %rbx,%rdi
    3d5e:	e8 5d e6 ff ff       	call   23c0 <fputs@plt>
    3d63:	4d 39 ee             	cmp    %r13,%r14
    3d66:	75 a6                	jne    3d0e <main+0x169e>
    3d68:	49 be db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r14
    3d72:	4c 89 ff             	mov    %r15,%rdi
    3d75:	45 31 e4             	xor    %r12d,%r12d
    3d78:	e8 e3 e5 ff ff       	call   2360 <fclose@plt>
    3d7d:	4c 89 e3             	mov    %r12,%rbx
    3d80:	48 c7 44 24 48 00 00 00 00 	movq   $0x0,0x48(%rsp)
    3d89:	48 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%rsp)
    3d92:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
    3d9b:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    3da4:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    3dad:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
    3db6:	48 89 d8             	mov    %rbx,%rax
    3db9:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3dbe:	44 8d 0c 1b          	lea    (%rbx,%rbx,1),%r9d
    3dc2:	48 89 5c 24 68       	mov    %rbx,0x68(%rsp)
    3dc7:	48 f7 d8             	neg    %rax
    3dca:	44 89 4c 24 74       	mov    %r9d,0x74(%rsp)
    3dcf:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    3dd4:	41 8d 69 ff          	lea    -0x1(%r9),%ebp
    3dd8:	49 89 c2             	mov    %rax,%r10
    3ddb:	83 e0 30             	and    $0x30,%eax
    3dde:	41 81 e2 00 03 00 00 	and    $0x300,%r10d
    3de5:	4e 8d 2c 17          	lea    (%rdi,%r10,1),%r13
    3de9:	48 8b 7c 24 78       	mov    0x78(%rsp),%rdi
    3dee:	4d 89 ec             	mov    %r13,%r12
    3df1:	48 01 f8             	add    %rdi,%rax
    3df4:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    3df9:	89 ef                	mov    %ebp,%edi
    3dfb:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3e00:	89 6c 24 50          	mov    %ebp,0x50(%rsp)
    3e04:	83 c5 01             	add    $0x1,%ebp
    3e07:	49 03 84 24 10 01 00 00 	add    0x110(%r12),%rax
    3e0f:	40 f6 c5 01          	test   $0x1,%bpl
    3e13:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    3e18:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3e1d:	8d 47 02             	lea    0x2(%rdi),%eax
    3e20:	0f 45 c7             	cmovne %edi,%eax
    3e23:	bf 0a 00 00 00       	mov    $0xa,%edi
    3e28:	41 89 c5             	mov    %eax,%r13d
    3e2b:	e8 e0 e4 ff ff       	call   2310 <putchar@plt>
    3e30:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3e35:	bf 01 00 00 00       	mov    $0x1,%edi
    3e3a:	48 8d 35 25 47 00 00 	lea    0x4725(%rip),%rsi        # 8566 <_IO_stdin_used+0x566>
    3e41:	48 8b 10             	mov    (%rax),%rdx
    3e44:	31 c0                	xor    %eax,%eax
    3e46:	e8 65 e6 ff ff       	call   24b0 <__printf_chk@plt>
    3e4b:	41 8b 54 24 40       	mov    0x40(%r12),%edx
    3e50:	85 d2                	test   %edx,%edx
    3e52:	0f 8e 4e 05 00 00    	jle    43a6 <main+0x1d36>
    3e58:	48 63 ca             	movslq %edx,%rcx
    3e5b:	49 8b 44 24 38       	mov    0x38(%r12),%rax
    3e60:	31 d2                	xor    %edx,%edx
    3e62:	48 c1 e1 09          	shl    $0x9,%rcx
    3e66:	48 01 c1             	add    %rax,%rcx
    3e69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3e70:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    3e77:	48 05 00 02 00 00    	add    $0x200,%rax
    3e7d:	48 39 c8             	cmp    %rcx,%rax
    3e80:	75 ee                	jne    3e70 <main+0x1800>
    3e82:	49 63 c5             	movslq %r13d,%rax
    3e85:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3e8a:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    3e8e:	48 c1 e0 07          	shl    $0x7,%rax
    3e92:	48 01 f8             	add    %rdi,%rax
    3e95:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3e99:	85 c9                	test   %ecx,%ecx
    3e9b:	7e 25                	jle    3ec2 <main+0x1852>
    3e9d:	48 8b 40 38          	mov    0x38(%rax),%rax
    3ea1:	48 c1 e1 09          	shl    $0x9,%rcx
    3ea5:	48 01 c1             	add    %rax,%rcx
    3ea8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3eb0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    3eb7:	48 05 00 02 00 00    	add    $0x200,%rax
    3ebd:	48 39 c8             	cmp    %rcx,%rax
    3ec0:	75 ee                	jne    3eb0 <main+0x1840>
    3ec2:	48 8d 35 b2 46 00 00 	lea    0x46b2(%rip),%rsi        # 857b <_IO_stdin_used+0x57b>
    3ec9:	bf 01 00 00 00       	mov    $0x1,%edi
    3ece:	31 c0                	xor    %eax,%eax
    3ed0:	e8 db e5 ff ff       	call   24b0 <__printf_chk@plt>
    3ed5:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3eda:	bf 01 00 00 00       	mov    $0x1,%edi
    3edf:	48 8d 35 72 49 00 00 	lea    0x4972(%rip),%rsi        # 8858 <_IO_stdin_used+0x858>
    3ee6:	48 8b 08             	mov    (%rax),%rcx
    3ee9:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3ef3:	48 f7 e9             	imul   %rcx
    3ef6:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3efa:	31 c0                	xor    %eax,%eax
    3efc:	48 d1 fa             	sar    %rdx
    3eff:	48 29 ca             	sub    %rcx,%rdx
    3f02:	e8 a9 e5 ff ff       	call   24b0 <__printf_chk@plt>
    3f07:	bf 0a 00 00 00       	mov    $0xa,%edi
    3f0c:	e8 ff e3 ff ff       	call   2310 <putchar@plt>
    3f11:	45 8b 6c 24 40       	mov    0x40(%r12),%r13d
    3f16:	45 85 ed             	test   %r13d,%r13d
    3f19:	0f 8e 3f 01 00 00    	jle    405e <main+0x19ee>
    3f1f:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    3f24:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3f29:	89 6c 24 08          	mov    %ebp,0x8(%rsp)
    3f2d:	31 d2                	xor    %edx,%edx
    3f2f:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3f34:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    3f39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3f40:	49 8b 44 24 38       	mov    0x38(%r12),%rax
    3f45:	49 89 d1             	mov    %rdx,%r9
    3f48:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
    3f4d:	89 d5                	mov    %edx,%ebp
    3f4f:	49 c1 e1 09          	shl    $0x9,%r9
    3f53:	45 31 ed             	xor    %r13d,%r13d
    3f56:	4c 01 c8             	add    %r9,%rax
    3f59:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    3f5e:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
    3f65:	48 03 b0 68 01 00 00 	add    0x168(%rax),%rsi
    3f6c:	48 03 b8 80 01 00 00 	add    0x180(%rax),%rdi
    3f73:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    3f78:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    3f7d:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    3f82:	8b 54 24 08          	mov    0x8(%rsp),%edx
    3f86:	45 89 e8             	mov    %r13d,%r8d
    3f89:	89 e9                	mov    %ebp,%ecx
    3f8b:	48 8d 35 f6 45 00 00 	lea    0x45f6(%rip),%rsi        # 8588 <_IO_stdin_used+0x588>
    3f92:	bf 01 00 00 00       	mov    $0x1,%edi
    3f97:	31 c0                	xor    %eax,%eax
    3f99:	e8 12 e5 ff ff       	call   24b0 <__printf_chk@plt>
    3f9e:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    3fa3:	4c 89 e8             	mov    %r13,%rax
    3fa6:	45 89 e8             	mov    %r13d,%r8d
    3fa9:	49 8b 54 24 38       	mov    0x38(%r12),%rdx
    3fae:	48 c1 e0 08          	shl    $0x8,%rax
    3fb2:	48 83 ec 08          	sub    $0x8,%rsp
    3fb6:	49 83 c5 01          	add    $0x1,%r13
    3fba:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    3fc2:	48 8b 38             	mov    (%rax),%rdi
    3fc5:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    3fcc:	48 8b 87 00 04 00 00 	mov    0x400(%rdi),%rax
    3fd3:	48 8b 96 80 03 00 00 	mov    0x380(%rsi),%rdx
    3fda:	48 8b b6 00 04 00 00 	mov    0x400(%rsi),%rsi
    3fe1:	48 8b 8f 80 03 00 00 	mov    0x380(%rdi),%rcx
    3fe8:	bf 01 00 00 00       	mov    $0x1,%edi
    3fed:	48 01 c3             	add    %rax,%rbx
    3ff0:	48 01 f0             	add    %rsi,%rax
    3ff3:	49 01 cf             	add    %rcx,%r15
    3ff6:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
    3ffa:	48 01 f3             	add    %rsi,%rbx
    3ffd:	50                   	push   %rax
    3ffe:	49 01 d7             	add    %rdx,%r15
    4001:	8b 54 24 18          	mov    0x18(%rsp),%edx
    4005:	89 e9                	mov    %ebp,%ecx
    4007:	48 8d 35 6a 48 00 00 	lea    0x486a(%rip),%rsi        # 8878 <_IO_stdin_used+0x878>
    400e:	31 c0                	xor    %eax,%eax
    4010:	e8 9b e4 ff ff       	call   24b0 <__printf_chk@plt>
    4015:	41 5a                	pop    %r10
    4017:	41 5b                	pop    %r11
    4019:	49 83 fd 04          	cmp    $0x4,%r13
    401d:	0f 85 5f ff ff ff    	jne    3f82 <main+0x1912>
    4023:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    4028:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    402d:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    4032:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    4037:	48 83 c2 01          	add    $0x1,%rdx
    403b:	41 39 54 24 40       	cmp    %edx,0x40(%r12)
    4040:	0f 8f fa fe ff ff    	jg     3f40 <main+0x18d0>
    4046:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
    404b:	8b 6c 24 08          	mov    0x8(%rsp),%ebp
    404f:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    4054:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
    4059:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    405e:	45 31 ed             	xor    %r13d,%r13d
    4061:	4c 8d 3d 30 48 00 00 	lea    0x4830(%rip),%r15        # 8898 <_IO_stdin_used+0x898>
    4068:	49 83 bc 24 a0 00 00 00 00 	cmpq   $0x0,0xa0(%r12)
    4071:	7e 60                	jle    40d3 <main+0x1a63>
    4073:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4078:	4b 8d 54 ad 00       	lea    0x0(%r13,%r13,4),%rdx
    407d:	48 83 ec 08          	sub    $0x8,%rsp
    4081:	bf 01 00 00 00       	mov    $0x1,%edi
    4086:	49 8b 84 24 90 00 00 00 	mov    0x90(%r12),%rax
    408e:	49 83 c5 01          	add    $0x1,%r13
    4092:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    4096:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    409a:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    409e:	48 89 f0             	mov    %rsi,%rax
    40a1:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    40a5:	4c 2b 01             	sub    (%rcx),%r8
    40a8:	49 f7 e6             	mul    %r14
    40ab:	8b 49 20             	mov    0x20(%rcx),%ecx
    40ae:	56                   	push   %rsi
    40af:	31 c0                	xor    %eax,%eax
    40b1:	4c 89 fe             	mov    %r15,%rsi
    40b4:	48 c1 ea 12          	shr    $0x12,%rdx
    40b8:	49 89 d1             	mov    %rdx,%r9
    40bb:	ba 02 00 00 00       	mov    $0x2,%edx
    40c0:	e8 eb e3 ff ff       	call   24b0 <__printf_chk@plt>
    40c5:	41 58                	pop    %r8
    40c7:	41 59                	pop    %r9
    40c9:	4d 39 ac 24 a0 00 00 00 	cmp    %r13,0xa0(%r12)
    40d1:	7f a5                	jg     4078 <main+0x1a08>
    40d3:	41 8b 94 24 bc 00 00 00 	mov    0xbc(%r12),%edx
    40db:	85 d2                	test   %edx,%edx
    40dd:	0f 8e 15 01 00 00    	jle    41f8 <main+0x1b88>
    40e3:	89 ac 24 80 00 00 00 	mov    %ebp,0x80(%rsp)
    40ea:	49 8b 7c 24 50       	mov    0x50(%r12),%rdi
    40ef:	45 31 ff             	xor    %r15d,%r15d
    40f2:	48 89 9c 24 88 00 00 00 	mov    %rbx,0x88(%rsp)
    40fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4100:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    4104:	44 89 fb             	mov    %r15d,%ebx
    4107:	4a 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%rbp
    410f:	8b 30                	mov    (%rax),%esi
    4111:	85 f6                	test   %esi,%esi
    4113:	0f 8e c3 00 00 00    	jle    41dc <main+0x1b6c>
    4119:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    411e:	31 d2                	xor    %edx,%edx
    4120:	48 8b 48 08          	mov    0x8(%rax),%rcx
    4124:	49 89 f8             	mov    %rdi,%r8
    4127:	48 89 d7             	mov    %rdx,%rdi
    412a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4130:	49 89 fd             	mov    %rdi,%r13
    4133:	45 31 ff             	xor    %r15d,%r15d
    4136:	49 c1 e5 08          	shl    $0x8,%r13
    413a:	4a 8d 04 29          	lea    (%rcx,%r13,1),%rax
    413e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    4144:	85 d2                	test   %edx,%edx
    4146:	7e 78                	jle    41c0 <main+0x1b50>
    4148:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    414d:	0f 1f 00             	nopl   (%rax)
    4150:	4c 89 f9             	mov    %r15,%rcx
    4153:	48 83 ec 08          	sub    $0x8,%rsp
    4157:	bf 01 00 00 00       	mov    $0x1,%edi
    415c:	49 83 c7 01          	add    $0x1,%r15
    4160:	48 c1 e1 05          	shl    $0x5,%rcx
    4164:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
    416b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    416f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    4173:	48 89 f0             	mov    %rsi,%rax
    4176:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    417a:	4c 2b 01             	sub    (%rcx),%r8
    417d:	56                   	push   %rsi
    417e:	49 f7 e6             	mul    %r14
    4181:	89 d9                	mov    %ebx,%ecx
    4183:	48 8d 35 5e 47 00 00 	lea    0x475e(%rip),%rsi        # 88e8 <_IO_stdin_used+0x8e8>
    418a:	31 c0                	xor    %eax,%eax
    418c:	48 c1 ea 12          	shr    $0x12,%rdx
    4190:	49 89 d1             	mov    %rdx,%r9
    4193:	ba 02 00 00 00       	mov    $0x2,%edx
    4198:	e8 13 e3 ff ff       	call   24b0 <__printf_chk@plt>
    419d:	4d 8b 44 24 50       	mov    0x50(%r12),%r8
    41a2:	5e                   	pop    %rsi
    41a3:	5f                   	pop    %rdi
    41a4:	49 8b 14 28          	mov    (%r8,%rbp,1),%rdx
    41a8:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    41ac:	4a 8d 04 29          	lea    (%rcx,%r13,1),%rax
    41b0:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    41b7:	7f 97                	jg     4150 <main+0x1ae0>
    41b9:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    41be:	8b 32                	mov    (%rdx),%esi
    41c0:	48 83 c7 01          	add    $0x1,%rdi
    41c4:	39 fe                	cmp    %edi,%esi
    41c6:	0f 8f 64 ff ff ff    	jg     4130 <main+0x1ac0>
    41cc:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    41d1:	41 8b 94 24 bc 00 00 00 	mov    0xbc(%r12),%edx
    41d9:	4c 89 c7             	mov    %r8,%rdi
    41dc:	49 83 c7 01          	add    $0x1,%r15
    41e0:	44 39 fa             	cmp    %r15d,%edx
    41e3:	0f 8f 17 ff ff ff    	jg     4100 <main+0x1a90>
    41e9:	8b ac 24 80 00 00 00 	mov    0x80(%rsp),%ebp
    41f0:	48 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%rbx
    41f8:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    41fe:	8b 7c 24 50          	mov    0x50(%rsp),%edi
    4202:	49 81 c4 80 01 00 00 	add    $0x180,%r12
    4209:	39 7c 24 74          	cmp    %edi,0x74(%rsp)
    420d:	0f 85 e6 fb ff ff    	jne    3df9 <main+0x1789>
    4213:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    4218:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
    421d:	48 85 db             	test   %rbx,%rbx
    4220:	75 0a                	jne    422c <main+0x1bbc>
    4222:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
    4227:	e9 8a fb ff ff       	jmp    3db6 <main+0x1746>
    422c:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    4231:	48 8d 35 60 43 00 00 	lea    0x4360(%rip),%rsi        # 8598 <_IO_stdin_used+0x598>
    4238:	bf 01 00 00 00       	mov    $0x1,%edi
    423d:	31 c0                	xor    %eax,%eax
    423f:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    4249:	4c 89 f2             	mov    %r14,%rdx
    424c:	e8 5f e2 ff ff       	call   24b0 <__printf_chk@plt>
    4251:	bf 0a 00 00 00       	mov    $0xa,%edi
    4256:	e8 b5 e0 ff ff       	call   2310 <putchar@plt>
    425b:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    4260:	bf 01 00 00 00       	mov    $0x1,%edi
    4265:	48 8d 35 d4 46 00 00 	lea    0x46d4(%rip),%rsi        # 8940 <_IO_stdin_used+0x940>
    426c:	48 8b 50 08          	mov    0x8(%rax),%rdx
    4270:	31 c0                	xor    %eax,%eax
    4272:	e8 39 e2 ff ff       	call   24b0 <__printf_chk@plt>
    4277:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    427c:	bf 01 00 00 00       	mov    $0x1,%edi
    4281:	48 8d 35 e0 46 00 00 	lea    0x46e0(%rip),%rsi        # 8968 <_IO_stdin_used+0x968>
    4288:	48 f7 eb             	imul   %rbx
    428b:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    4290:	48 c1 f8 3f          	sar    $0x3f,%rax
    4294:	48 d1 fa             	sar    %rdx
    4297:	48 29 c2             	sub    %rax,%rdx
    429a:	31 c0                	xor    %eax,%eax
    429c:	e8 0f e2 ff ff       	call   24b0 <__printf_chk@plt>
    42a1:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    42a6:	bf 01 00 00 00       	mov    $0x1,%edi
    42ab:	48 8d 35 e6 46 00 00 	lea    0x46e6(%rip),%rsi        # 8998 <_IO_stdin_used+0x998>
    42b2:	48 f7 eb             	imul   %rbx
    42b5:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    42ba:	48 c1 f8 3f          	sar    $0x3f,%rax
    42be:	48 d1 fa             	sar    %rdx
    42c1:	48 29 c2             	sub    %rax,%rdx
    42c4:	31 c0                	xor    %eax,%eax
    42c6:	e8 e5 e1 ff ff       	call   24b0 <__printf_chk@plt>
    42cb:	4c 89 f0             	mov    %r14,%rax
    42ce:	bf 01 00 00 00       	mov    $0x1,%edi
    42d3:	48 8d 35 ee 46 00 00 	lea    0x46ee(%rip),%rsi        # 89c8 <_IO_stdin_used+0x9c8>
    42da:	48 f7 eb             	imul   %rbx
    42dd:	4c 89 f0             	mov    %r14,%rax
    42e0:	48 c1 f8 3f          	sar    $0x3f,%rax
    42e4:	48 d1 fa             	sar    %rdx
    42e7:	48 29 c2             	sub    %rax,%rdx
    42ea:	31 c0                	xor    %eax,%eax
    42ec:	e8 bf e1 ff ff       	call   24b0 <__printf_chk@plt>
    42f1:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    42f6:	bf 01 00 00 00       	mov    $0x1,%edi
    42fb:	48 8d 35 aa 42 00 00 	lea    0x42aa(%rip),%rsi        # 85ac <_IO_stdin_used+0x5ac>
    4302:	48 f7 eb             	imul   %rbx
    4305:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    430a:	48 c1 f8 3f          	sar    $0x3f,%rax
    430e:	48 d1 fa             	sar    %rdx
    4311:	48 29 c2             	sub    %rax,%rdx
    4314:	31 c0                	xor    %eax,%eax
    4316:	48 89 d5             	mov    %rdx,%rbp
    4319:	e8 92 e1 ff ff       	call   24b0 <__printf_chk@plt>
    431e:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4323:	bf 01 00 00 00       	mov    $0x1,%edi
    4328:	48 8d 35 b9 46 00 00 	lea    0x46b9(%rip),%rsi        # 89e8 <_IO_stdin_used+0x9e8>
    432f:	48 f7 eb             	imul   %rbx
    4332:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4337:	48 c1 f8 3f          	sar    $0x3f,%rax
    433b:	48 89 d3             	mov    %rdx,%rbx
    433e:	48 d1 fb             	sar    %rbx
    4341:	48 29 c3             	sub    %rax,%rbx
    4344:	31 c0                	xor    %eax,%eax
    4346:	48 89 da             	mov    %rbx,%rdx
    4349:	48 29 eb             	sub    %rbp,%rbx
    434c:	e8 5f e1 ff ff       	call   24b0 <__printf_chk@plt>
    4351:	48 89 da             	mov    %rbx,%rdx
    4354:	bf 01 00 00 00       	mov    $0x1,%edi
    4359:	31 c0                	xor    %eax,%eax
    435b:	48 8d 35 66 42 00 00 	lea    0x4266(%rip),%rsi        # 85c8 <_IO_stdin_used+0x5c8>
    4362:	e8 49 e1 ff ff       	call   24b0 <__printf_chk@plt>
    4367:	48 8b 54 24 60       	mov    0x60(%rsp),%rdx
    436c:	31 c0                	xor    %eax,%eax
    436e:	48 8d 35 63 42 00 00 	lea    0x4263(%rip),%rsi        # 85d8 <_IO_stdin_used+0x5d8>
    4375:	bf 01 00 00 00       	mov    $0x1,%edi
    437a:	e8 31 e1 ff ff       	call   24b0 <__printf_chk@plt>
    437f:	48 8b 84 24 e8 00 00 00 	mov    0xe8(%rsp),%rax
    4387:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4390:	75 25                	jne    43b7 <main+0x1d47>
    4392:	48 81 c4 f8 00 00 00 	add    $0xf8,%rsp
    4399:	31 c0                	xor    %eax,%eax
    439b:	5b                   	pop    %rbx
    439c:	5d                   	pop    %rbp
    439d:	41 5c                	pop    %r12
    439f:	41 5d                	pop    %r13
    43a1:	41 5e                	pop    %r14
    43a3:	41 5f                	pop    %r15
    43a5:	c3                   	ret
    43a6:	31 d2                	xor    %edx,%edx
    43a8:	e9 d5 fa ff ff       	jmp    3e82 <main+0x1812>
    43ad:	bf 01 00 00 00       	mov    $0x1,%edi
    43b2:	e8 59 e1 ff ff       	call   2510 <exit@plt>
    43b7:	e8 c4 df ff ff       	call   2380 <__stack_chk_fail@plt>
    43bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000043c0 <_start>:
    43c0:	f3 0f 1e fa          	endbr64
    43c4:	31 ed                	xor    %ebp,%ebp
    43c6:	49 89 d1             	mov    %rdx,%r9
    43c9:	5e                   	pop    %rsi
    43ca:	48 89 e2             	mov    %rsp,%rdx
    43cd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    43d1:	50                   	push   %rax
    43d2:	54                   	push   %rsp
    43d3:	45 31 c0             	xor    %r8d,%r8d
    43d6:	31 c9                	xor    %ecx,%ecx
    43d8:	48 8d 3d 91 e2 ff ff 	lea    -0x1d6f(%rip),%rdi        # 2670 <main>
    43df:	ff 15 f3 6b 00 00    	call   *0x6bf3(%rip)        # afd8 <__libc_start_main@GLIBC_2.34>
    43e5:	f4                   	hlt
    43e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000043f0 <deregister_tm_clones>:
    43f0:	48 8d 3d 29 6c 00 00 	lea    0x6c29(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    43f7:	48 8d 05 22 6c 00 00 	lea    0x6c22(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    43fe:	48 39 f8             	cmp    %rdi,%rax
    4401:	74 15                	je     4418 <deregister_tm_clones+0x28>
    4403:	48 8b 05 d6 6b 00 00 	mov    0x6bd6(%rip),%rax        # afe0 <_ITM_deregisterTMCloneTable@Base>
    440a:	48 85 c0             	test   %rax,%rax
    440d:	74 09                	je     4418 <deregister_tm_clones+0x28>
    440f:	ff e0                	jmp    *%rax
    4411:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4418:	c3                   	ret
    4419:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004420 <register_tm_clones>:
    4420:	48 8d 3d f9 6b 00 00 	lea    0x6bf9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4427:	48 8d 35 f2 6b 00 00 	lea    0x6bf2(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    442e:	48 29 fe             	sub    %rdi,%rsi
    4431:	48 89 f0             	mov    %rsi,%rax
    4434:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4438:	48 c1 f8 03          	sar    $0x3,%rax
    443c:	48 01 c6             	add    %rax,%rsi
    443f:	48 d1 fe             	sar    %rsi
    4442:	74 14                	je     4458 <register_tm_clones+0x38>
    4444:	48 8b 05 a5 6b 00 00 	mov    0x6ba5(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    444b:	48 85 c0             	test   %rax,%rax
    444e:	74 08                	je     4458 <register_tm_clones+0x38>
    4450:	ff e0                	jmp    *%rax
    4452:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4458:	c3                   	ret
    4459:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004460 <__do_global_dtors_aux>:
    4460:	f3 0f 1e fa          	endbr64
    4464:	80 3d bd 6b 00 00 00 	cmpb   $0x0,0x6bbd(%rip)        # b028 <completed.0>
    446b:	75 2b                	jne    4498 <__do_global_dtors_aux+0x38>
    446d:	55                   	push   %rbp
    446e:	48 83 3d 82 6b 00 00 00 	cmpq   $0x0,0x6b82(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    4476:	48 89 e5             	mov    %rsp,%rbp
    4479:	74 0c                	je     4487 <__do_global_dtors_aux+0x27>
    447b:	48 8b 3d 86 6b 00 00 	mov    0x6b86(%rip),%rdi        # b008 <__dso_handle>
    4482:	e8 69 de ff ff       	call   22f0 <__cxa_finalize@plt>
    4487:	e8 64 ff ff ff       	call   43f0 <deregister_tm_clones>
    448c:	c6 05 95 6b 00 00 01 	movb   $0x1,0x6b95(%rip)        # b028 <completed.0>
    4493:	5d                   	pop    %rbp
    4494:	c3                   	ret
    4495:	0f 1f 00             	nopl   (%rax)
    4498:	c3                   	ret
    4499:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000044a0 <frame_dummy>:
    44a0:	f3 0f 1e fa          	endbr64
    44a4:	e9 77 ff ff ff       	jmp    4420 <register_tm_clones>
    44a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000044b0 <do_protected_write>:
    44b0:	f3 0f 1e fa          	endbr64
    44b4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    44bb:	48 8b 40 48          	mov    0x48(%rax),%rax
    44bf:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
    44c7:	48 8b 48 08          	mov    0x8(%rax),%rcx
    44cb:	48 83 00 01          	addq   $0x1,(%rax)
    44cf:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    44d6:	48 85 c9             	test   %rcx,%rcx
    44d9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    44e0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    44e4:	48 89 50 08          	mov    %rdx,0x8(%rax)
    44e8:	31 c0                	xor    %eax,%eax
    44ea:	c3                   	ret
    44eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000044f0 <barriered_reset>:
    44f0:	f3 0f 1e fa          	endbr64
    44f4:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    44fb:	85 c9                	test   %ecx,%ecx
    44fd:	7e 4f                	jle    454e <barriered_reset+0x5e>
    44ff:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    4506:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    450d:	48 c1 e1 09          	shl    $0x9,%rcx
    4511:	48 8b 50 18          	mov    0x18(%rax),%rdx
    4515:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
    4519:	48 8b 70 38          	mov    0x38(%rax),%rsi
    451d:	31 c0                	xor    %eax,%eax
    451f:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4523:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4528:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
    4530:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
    4538:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    4543:	48 05 00 02 00 00    	add    $0x200,%rax
    4549:	48 39 c1             	cmp    %rax,%rcx
    454c:	75 da                	jne    4528 <barriered_reset+0x38>
    454e:	0f ae f8             	sfence
    4551:	31 c0                	xor    %eax,%eax
    4553:	c3                   	ret
    4554:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    455f:	90                   	nop

0000000000004560 <external_thread>:
    4560:	f3 0f 1e fa          	endbr64
    4564:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    4568:	0f 85 fb 00 00 00    	jne    4669 <external_thread+0x109>
    456e:	41 57                	push   %r15
    4570:	49 89 ff             	mov    %rdi,%r15
    4573:	41 56                	push   %r14
    4575:	41 55                	push   %r13
    4577:	4c 8d 2d 86 3a 00 00 	lea    0x3a86(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
    457e:	41 54                	push   %r12
    4580:	55                   	push   %rbp
    4581:	53                   	push   %rbx
    4582:	48 83 ec 08          	sub    $0x8,%rsp
    4586:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    458c:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    4590:	85 c9                	test   %ecx,%ecx
    4592:	7e 6e                	jle    4602 <external_thread+0xa2>
    4594:	45 31 e4             	xor    %r12d,%r12d
    4597:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    45a0:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    45a8:	31 db                	xor    %ebx,%ebx
    45aa:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    45ae:	48 8b 06             	mov    (%rsi),%rax
    45b1:	8b 10                	mov    (%rax),%edx
    45b3:	85 d2                	test   %edx,%edx
    45b5:	7e 2a                	jle    45e1 <external_thread+0x81>
    45b7:	48 8b 48 08          	mov    0x8(%rax),%rcx
    45bb:	48 89 dd             	mov    %rbx,%rbp
    45be:	48 c1 e5 08          	shl    $0x8,%rbp
    45c2:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    45c6:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    45cd:	45 85 c0             	test   %r8d,%r8d
    45d0:	74 36                	je     4608 <external_thread+0xa8>
    45d2:	48 83 c3 01          	add    $0x1,%rbx
    45d6:	39 da                	cmp    %ebx,%edx
    45d8:	7f e1                	jg     45bb <external_thread+0x5b>
    45da:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    45e1:	49 83 c4 01          	add    $0x1,%r12
    45e5:	44 39 e1             	cmp    %r12d,%ecx
    45e8:	7f b6                	jg     45a0 <external_thread+0x40>
    45ea:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    45ef:	74 9f                	je     4590 <external_thread+0x30>
    45f1:	48 83 c4 08          	add    $0x8,%rsp
    45f5:	31 c0                	xor    %eax,%eax
    45f7:	5b                   	pop    %rbx
    45f8:	5d                   	pop    %rbp
    45f9:	41 5c                	pop    %r12
    45fb:	41 5d                	pop    %r13
    45fd:	41 5e                	pop    %r14
    45ff:	41 5f                	pop    %r15
    4601:	c3                   	ret
    4602:	eb fe                	jmp    4602 <external_thread+0xa2>
    4604:	0f 1f 40 00          	nopl   0x0(%rax)
    4608:	4c 89 28             	mov    %r13,(%rax)
    460b:	48 8b 06             	mov    (%rsi),%rax
    460e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4612:	48 01 ef             	add    %rbp,%rdi
    4615:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    461c:	48 c1 e6 05          	shl    $0x5,%rsi
    4620:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4627:	bf 04 00 00 00       	mov    $0x4,%edi
    462c:	e8 1f dd ff ff       	call   2350 <clock_gettime@plt>
    4631:	49 8b 47 50          	mov    0x50(%r15),%rax
    4635:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    4639:	48 8b 40 08          	mov    0x8(%rax),%rax
    463d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
    4648:	0f ae f8             	sfence
    464b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    464f:	48 83 c3 01          	add    $0x1,%rbx
    4653:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    4657:	48 8b 06             	mov    (%rsi),%rax
    465a:	8b 10                	mov    (%rax),%edx
    465c:	39 da                	cmp    %ebx,%edx
    465e:	0f 8f 53 ff ff ff    	jg     45b7 <external_thread+0x57>
    4664:	e9 71 ff ff ff       	jmp    45da <external_thread+0x7a>
    4669:	31 c0                	xor    %eax,%eax
    466b:	c3                   	ret
    466c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004670 <timer_thread>:
    4670:	f3 0f 1e fa          	endbr64
    4674:	41 57                	push   %r15
    4676:	48 8d 35 93 39 00 00 	lea    0x3993(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    467d:	49 89 ff             	mov    %rdi,%r15
    4680:	41 56                	push   %r14
    4682:	41 55                	push   %r13
    4684:	41 54                	push   %r12
    4686:	55                   	push   %rbp
    4687:	53                   	push   %rbx
    4688:	48 83 ec 58          	sub    $0x58,%rsp
    468c:	8b 57 04             	mov    0x4(%rdi),%edx
    468f:	bf 01 00 00 00       	mov    $0x1,%edi
    4694:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    469d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    46a2:	31 c0                	xor    %eax,%eax
    46a4:	e8 07 de ff ff       	call   24b0 <__printf_chk@plt>
    46a9:	66 0f 6f 05 4f 45 00 00 	movdqa 0x454f(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    46b1:	ba 88 13 00 00       	mov    $0x1388,%edx
    46b6:	31 c0                	xor    %eax,%eax
    46b8:	48 8d 35 63 39 00 00 	lea    0x3963(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    46bf:	bf 01 00 00 00       	mov    $0x1,%edi
    46c4:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    46c9:	e8 e2 dd ff ff       	call   24b0 <__printf_chk@plt>
    46ce:	41 8b 47 44          	mov    0x44(%r15),%eax
    46d2:	89 c3                	mov    %eax,%ebx
    46d4:	85 c0                	test   %eax,%eax
    46d6:	0f 84 9a 00 00 00    	je     4776 <timer_thread+0x106>
    46dc:	45 31 f6             	xor    %r14d,%r14d
    46df:	31 db                	xor    %ebx,%ebx
    46e1:	49 89 e5             	mov    %rsp,%r13
    46e4:	31 ed                	xor    %ebp,%ebp
    46e6:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
    46eb:	4c 89 e7             	mov    %r12,%rdi
    46ee:	4c 89 ee             	mov    %r13,%rsi
    46f1:	41 83 c6 01          	add    $0x1,%r14d
    46f5:	e8 a6 dc ff ff       	call   23a0 <nanosleep@plt>
    46fa:	49 63 47 30          	movslq 0x30(%r15),%rax
    46fe:	8d 7b 01             	lea    0x1(%rbx),%edi
    4701:	85 c0                	test   %eax,%eax
    4703:	7e 4a                	jle    474f <timer_thread+0xdf>
    4705:	49 8b 4f 18          	mov    0x18(%r15),%rcx
    4709:	4c 63 c3             	movslq %ebx,%r8
    470c:	49 c1 e0 09          	shl    $0x9,%r8
    4710:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4714:	0f 1f 40 00          	nopl   0x0(%rax)
    4718:	48 8b 19             	mov    (%rcx),%rbx
    471b:	89 f8                	mov    %edi,%eax
    471d:	48 83 c1 08          	add    $0x8,%rcx
    4721:	99                   	cltd
    4722:	f7 7b 40             	idivl  0x40(%rbx)
    4725:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4729:	83 ea 01             	sub    $0x1,%edx
    472c:	48 63 d2             	movslq %edx,%rdx
    472f:	48 c1 e2 09          	shl    $0x9,%rdx
    4733:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    473e:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    474a:	49 39 c9             	cmp    %rcx,%r9
    474d:	75 c9                	jne    4718 <timer_thread+0xa8>
    474f:	0f ae f0             	mfence
    4752:	49 8b 47 18          	mov    0x18(%r15),%rax
    4756:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    475a:	89 fb                	mov    %edi,%ebx
    475c:	48 8b 00             	mov    (%rax),%rax
    475f:	39 78 40             	cmp    %edi,0x40(%rax)
    4762:	0f 4e dd             	cmovle %ebp,%ebx
    4765:	85 c9                	test   %ecx,%ecx
    4767:	74 0d                	je     4776 <timer_thread+0x106>
    4769:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    4770:	0f 85 75 ff ff ff    	jne    46eb <timer_thread+0x7b>
    4776:	48 8d 3d bb 38 00 00 	lea    0x38bb(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    477d:	e8 ae db ff ff       	call   2330 <puts@plt>
    4782:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4786:	85 d2                	test   %edx,%edx
    4788:	7e 6b                	jle    47f5 <timer_thread+0x185>
    478a:	49 63 47 40          	movslq 0x40(%r15),%rax
    478e:	85 c0                	test   %eax,%eax
    4790:	7e 63                	jle    47f5 <timer_thread+0x185>
    4792:	48 c1 e0 09          	shl    $0x9,%rax
    4796:	4d 8b 47 18          	mov    0x18(%r15),%r8
    479a:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    47a2:	31 c9                	xor    %ecx,%ecx
    47a4:	48 89 c6             	mov    %rax,%rsi
    47a7:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    47ab:	48 8b 40 38          	mov    0x38(%rax),%rax
    47af:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    47b3:	f7 c6 00 02 00 00    	test   $0x200,%esi
    47b9:	74 15                	je     47d0 <timer_thread+0x160>
    47bb:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    47c5:	48 05 00 02 00 00    	add    $0x200,%rax
    47cb:	48 39 c2             	cmp    %rax,%rdx
    47ce:	74 1c                	je     47ec <timer_thread+0x17c>
    47d0:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    47da:	48 05 00 04 00 00    	add    $0x400,%rax
    47e0:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
    47e7:	48 39 c2             	cmp    %rax,%rdx
    47ea:	75 e4                	jne    47d0 <timer_thread+0x160>
    47ec:	48 83 c1 08          	add    $0x8,%rcx
    47f0:	48 39 cf             	cmp    %rcx,%rdi
    47f3:	75 b2                	jne    47a7 <timer_thread+0x137>
    47f5:	0f ae f0             	mfence
    47f8:	66 0f 6f 05 10 44 00 00 	movdqa 0x4410(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4800:	41 89 dc             	mov    %ebx,%r12d
    4803:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    4808:	49 63 47 28          	movslq 0x28(%r15),%rax
    480c:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    4811:	85 c0                	test   %eax,%eax
    4813:	7e 46                	jle    485b <timer_thread+0x1eb>
    4815:	49 8b 4f 18          	mov    0x18(%r15),%rcx
    4819:	49 63 ec             	movslq %r12d,%rbp
    481c:	48 c1 e5 09          	shl    $0x9,%rbp
    4820:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4824:	0f 1f 40 00          	nopl   0x0(%rax)
    4828:	48 8b 19             	mov    (%rcx),%rbx
    482b:	89 f8                	mov    %edi,%eax
    482d:	48 83 c1 08          	add    $0x8,%rcx
    4831:	99                   	cltd
    4832:	f7 7b 40             	idivl  0x40(%rbx)
    4835:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4839:	48 63 d2             	movslq %edx,%rdx
    483c:	48 c1 e2 09          	shl    $0x9,%rdx
    4840:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    484b:	c7 84 2e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rbp,1)
    4856:	49 39 c8             	cmp    %rcx,%r8
    4859:	75 cd                	jne    4828 <timer_thread+0x1b8>
    485b:	0f ae f0             	mfence
    485e:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4862:	45 31 e4             	xor    %r12d,%r12d
    4865:	48 8b 06             	mov    (%rsi),%rax
    4868:	39 78 40             	cmp    %edi,0x40(%rax)
    486b:	44 0f 4f e7          	cmovg  %edi,%r12d
    486f:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4873:	85 ff                	test   %edi,%edi
    4875:	0f 8e a9 01 00 00    	jle    4a24 <timer_thread+0x3b4>
    487b:	45 31 f6             	xor    %r14d,%r14d
    487e:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    4884:	4c 89 f5             	mov    %r14,%rbp
    4887:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4890:	89 eb                	mov    %ebp,%ebx
    4892:	4c 8d 2c ed 00 00 00 00 	lea    0x0(,%rbp,8),%r13
    489a:	45 31 f6             	xor    %r14d,%r14d
    489d:	85 ff                	test   %edi,%edi
    489f:	7e 77                	jle    4918 <timer_thread+0x2a8>
    48a1:	4c 89 f6             	mov    %r14,%rsi
    48a4:	48 63 cf             	movslq %edi,%rcx
    48a7:	45 31 c0             	xor    %r8d,%r8d
    48aa:	48 c1 e6 09          	shl    $0x9,%rsi
    48ae:	66 90                	xchg   %ax,%ax
    48b0:	41 39 e8             	cmp    %ebp,%r8d
    48b3:	74 45                	je     48fa <timer_thread+0x28a>
    48b5:	49 8b 47 18          	mov    0x18(%r15),%rax
    48b9:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
    48bd:	48 8b 50 38          	mov    0x38(%rax),%rdx
    48c1:	4c 89 c0             	mov    %r8,%rax
    48c4:	48 c1 e0 08          	shl    $0x8,%rax
    48c8:	48 03 84 32 70 01 00 00 	add    0x170(%rdx,%rsi,1),%rax
    48d0:	48 8b 10             	mov    (%rax),%rdx
    48d3:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    48da:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    48e1:	4c 8b 98 80 00 00 00 	mov    0x80(%rax),%r11
    48e8:	4d 85 c9             	test   %r9,%r9
    48eb:	0f 8f 97 00 00 00    	jg     4988 <timer_thread+0x318>
    48f1:	4d 85 db             	test   %r11,%r11
    48f4:	0f 8f 8e 00 00 00    	jg     4988 <timer_thread+0x318>
    48fa:	49 83 c0 01          	add    $0x1,%r8
    48fe:	4c 39 c1             	cmp    %r8,%rcx
    4901:	75 ad                	jne    48b0 <timer_thread+0x240>
    4903:	49 83 fe 01          	cmp    $0x1,%r14
    4907:	74 0f                	je     4918 <timer_thread+0x2a8>
    4909:	41 be 01 00 00 00    	mov    $0x1,%r14d
    490f:	85 ff                	test   %edi,%edi
    4911:	7f 8e                	jg     48a1 <timer_thread+0x231>
    4913:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4918:	48 83 c5 01          	add    $0x1,%rbp
    491c:	39 ef                	cmp    %ebp,%edi
    491e:	0f 8f 6c ff ff ff    	jg     4890 <timer_thread+0x220>
    4924:	44 89 d5             	mov    %r10d,%ebp
    4927:	85 ff                	test   %edi,%edi
    4929:	7e 3b                	jle    4966 <timer_thread+0x2f6>
    492b:	31 db                	xor    %ebx,%ebx
    492d:	bf 01 00 00 00       	mov    $0x1,%edi
    4932:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4936:	41 8b 57 40          	mov    0x40(%r15),%edx
    493a:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    493e:	48 8b 40 38          	mov    0x38(%rax),%rax
    4942:	8b 88 a4 01 00 00    	mov    0x1a4(%rax),%ecx
    4948:	39 d1                	cmp    %edx,%ecx
    494a:	0f 8c a8 00 00 00    	jl     49f8 <timer_thread+0x388>
    4950:	8b 80 a4 03 00 00    	mov    0x3a4(%rax),%eax
    4956:	39 d0                	cmp    %edx,%eax
    4958:	7c 6e                	jl     49c8 <timer_thread+0x358>
    495a:	48 83 c3 01          	add    $0x1,%rbx
    495e:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4962:	7f d6                	jg     493a <timer_thread+0x2ca>
    4964:	21 fd                	and    %edi,%ebp
    4966:	85 ed                	test   %ebp,%ebp
    4968:	0f 85 b6 00 00 00    	jne    4a24 <timer_thread+0x3b4>
    496e:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4973:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4978:	e8 23 da ff ff       	call   23a0 <nanosleep@plt>
    497d:	e9 86 fe ff ff       	jmp    4808 <timer_thread+0x198>
    4982:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4988:	8b 80 18 04 00 00    	mov    0x418(%rax),%eax
    498e:	48 83 ec 08          	sub    $0x8,%rsp
    4992:	bf 01 00 00 00       	mov    $0x1,%edi
    4997:	44 89 f1             	mov    %r14d,%ecx
    499a:	48 8d 35 bc 36 00 00 	lea    0x36bc(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    49a1:	50                   	push   %rax
    49a2:	8b 82 18 04 00 00    	mov    0x418(%rdx),%eax
    49a8:	89 da                	mov    %ebx,%edx
    49aa:	50                   	push   %rax
    49ab:	31 c0                	xor    %eax,%eax
    49ad:	41 53                	push   %r11
    49af:	e8 fc da ff ff       	call   24b0 <__printf_chk@plt>
    49b4:	41 8b 7f 30          	mov    0x30(%r15),%edi
    49b8:	48 83 c4 20          	add    $0x20,%rsp
    49bc:	45 31 d2             	xor    %r10d,%r10d
    49bf:	e9 3f ff ff ff       	jmp    4903 <timer_thread+0x293>
    49c4:	0f 1f 40 00          	nopl   0x0(%rax)
    49c8:	89 c2                	mov    %eax,%edx
    49ca:	bf 01 00 00 00       	mov    $0x1,%edi
    49cf:	31 c0                	xor    %eax,%eax
    49d1:	48 83 c3 01          	add    $0x1,%rbx
    49d5:	48 8d 35 3b 39 00 00 	lea    0x393b(%rip),%rsi        # 8317 <_IO_stdin_used+0x317>
    49dc:	e8 cf da ff ff       	call   24b0 <__printf_chk@plt>
    49e1:	31 ff                	xor    %edi,%edi
    49e3:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    49e7:	0f 8f 45 ff ff ff    	jg     4932 <timer_thread+0x2c2>
    49ed:	e9 72 ff ff ff       	jmp    4964 <timer_thread+0x2f4>
    49f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    49f8:	89 ca                	mov    %ecx,%edx
    49fa:	48 8d 35 16 39 00 00 	lea    0x3916(%rip),%rsi        # 8317 <_IO_stdin_used+0x317>
    4a01:	bf 01 00 00 00       	mov    $0x1,%edi
    4a06:	31 c0                	xor    %eax,%eax
    4a08:	e8 a3 da ff ff       	call   24b0 <__printf_chk@plt>
    4a0d:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4a11:	41 8b 57 40          	mov    0x40(%r15),%edx
    4a15:	31 ff                	xor    %edi,%edi
    4a17:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4a1b:	48 8b 40 38          	mov    0x38(%rax),%rax
    4a1f:	e9 2c ff ff ff       	jmp    4950 <timer_thread+0x2e0>
    4a24:	48 8d 3d 29 36 00 00 	lea    0x3629(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4a2b:	e8 00 d9 ff ff       	call   2330 <puts@plt>
    4a30:	41 8b 57 44          	mov    0x44(%r15),%edx
    4a34:	85 d2                	test   %edx,%edx
    4a36:	0f 84 eb 00 00 00    	je     4b27 <timer_thread+0x4b7>
    4a3c:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    4a40:	31 db                	xor    %ebx,%ebx
    4a42:	48 8d 2d 31 36 00 00 	lea    0x3631(%rip),%rbp        # 807a <_IO_stdin_used+0x7a>
    4a49:	4c 8d 25 45 36 00 00 	lea    0x3645(%rip),%r12        # 8095 <_IO_stdin_used+0x95>
    4a50:	85 c0                	test   %eax,%eax
    4a52:	7e 38                	jle    4a8c <timer_thread+0x41c>
    4a54:	0f 1f 40 00          	nopl   0x0(%rax)
    4a58:	31 c0                	xor    %eax,%eax
    4a5a:	89 da                	mov    %ebx,%edx
    4a5c:	48 89 ee             	mov    %rbp,%rsi
    4a5f:	bf 01 00 00 00       	mov    $0x1,%edi
    4a64:	e8 47 da ff ff       	call   24b0 <__printf_chk@plt>
    4a69:	49 8b 47 18          	mov    0x18(%r15),%rax
    4a6d:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4a71:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
    4a75:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
    4a7c:	0f 84 d2 00 00 00    	je     4b54 <timer_thread+0x4e4>
    4a82:	48 83 c3 01          	add    $0x1,%rbx
    4a86:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4a8a:	7f cc                	jg     4a58 <timer_thread+0x3e8>
    4a8c:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4a90:	85 d2                	test   %edx,%edx
    4a92:	7e 7c                	jle    4b10 <timer_thread+0x4a0>
    4a94:	41 8b 47 40          	mov    0x40(%r15),%eax
    4a98:	85 c0                	test   %eax,%eax
    4a9a:	7e 74                	jle    4b10 <timer_thread+0x4a0>
    4a9c:	48 63 f0             	movslq %eax,%rsi
    4a9f:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4aa3:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4aab:	31 c9                	xor    %ecx,%ecx
    4aad:	48 c1 e6 09          	shl    $0x9,%rsi
    4ab1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4ab8:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4abc:	48 8b 40 38          	mov    0x38(%rax),%rax
    4ac0:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4ac4:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4aca:	74 1c                	je     4ae8 <timer_thread+0x478>
    4acc:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    4ad6:	48 05 00 02 00 00    	add    $0x200,%rax
    4adc:	48 39 d0             	cmp    %rdx,%rax
    4adf:	74 26                	je     4b07 <timer_thread+0x497>
    4ae1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4ae8:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    4af2:	48 05 00 04 00 00    	add    $0x400,%rax
    4af8:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
    4b02:	48 39 d0             	cmp    %rdx,%rax
    4b05:	75 e1                	jne    4ae8 <timer_thread+0x478>
    4b07:	48 83 c1 08          	add    $0x8,%rcx
    4b0b:	48 39 cf             	cmp    %rcx,%rdi
    4b0e:	75 a8                	jne    4ab8 <timer_thread+0x448>
    4b10:	0f ae f0             	mfence
    4b13:	48 8d 3d 8d 35 00 00 	lea    0x358d(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4b1a:	e8 11 d8 ff ff       	call   2330 <puts@plt>
    4b1f:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    4b27:	48 8d 3d 80 35 00 00 	lea    0x3580(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4b2e:	e8 fd d7 ff ff       	call   2330 <puts@plt>
    4b33:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    4b38:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b41:	75 41                	jne    4b84 <timer_thread+0x514>
    4b43:	48 83 c4 58          	add    $0x58,%rsp
    4b47:	31 c0                	xor    %eax,%eax
    4b49:	5b                   	pop    %rbx
    4b4a:	5d                   	pop    %rbp
    4b4b:	41 5c                	pop    %r12
    4b4d:	41 5d                	pop    %r13
    4b4f:	41 5e                	pop    %r14
    4b51:	41 5f                	pop    %r15
    4b53:	c3                   	ret
    4b54:	4c 89 e7             	mov    %r12,%rdi
    4b57:	e8 d4 d7 ff ff       	call   2330 <puts@plt>
    4b5c:	49 8b 47 18          	mov    0x18(%r15),%rax
    4b60:	be 01 00 00 00       	mov    $0x1,%esi
    4b65:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4b69:	48 83 c3 01          	add    $0x1,%rbx
    4b6d:	8b 78 60             	mov    0x60(%rax),%edi
    4b70:	e8 eb d8 ff ff       	call   2460 <eventfd_write@plt>
    4b75:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4b79:	0f 8f d9 fe ff ff    	jg     4a58 <timer_thread+0x3e8>
    4b7f:	e9 08 ff ff ff       	jmp    4a8c <timer_thread+0x41c>
    4b84:	e8 f7 d7 ff ff       	call   2380 <__stack_chk_fail@plt>
    4b89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004b90 <minf>:
    4b90:	f3 0f 1e fa          	endbr64
    4b94:	39 f7                	cmp    %esi,%edi
    4b96:	89 f0                	mov    %esi,%eax
    4b98:	0f 4e c7             	cmovle %edi,%eax
    4b9b:	c3                   	ret
    4b9c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004ba0 <maxf>:
    4ba0:	f3 0f 1e fa          	endbr64
    4ba4:	39 f7                	cmp    %esi,%edi
    4ba6:	89 f0                	mov    %esi,%eax
    4ba8:	0f 4d c7             	cmovge %edi,%eax
    4bab:	c3                   	ret
    4bac:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004bb0 <strtolower>:
    4bb0:	f3 0f 1e fa          	endbr64
    4bb4:	55                   	push   %rbp
    4bb5:	53                   	push   %rbx
    4bb6:	48 83 ec 08          	sub    $0x8,%rsp
    4bba:	48 0f be 1f          	movsbq (%rdi),%rbx
    4bbe:	84 db                	test   %bl,%bl
    4bc0:	74 24                	je     4be6 <strtolower+0x36>
    4bc2:	48 89 fd             	mov    %rdi,%rbp
    4bc5:	e8 c6 d9 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4bca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4bd0:	48 8b 10             	mov    (%rax),%rdx
    4bd3:	48 83 c5 01          	add    $0x1,%rbp
    4bd7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4bda:	88 55 ff             	mov    %dl,-0x1(%rbp)
    4bdd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4be2:	84 db                	test   %bl,%bl
    4be4:	75 ea                	jne    4bd0 <strtolower+0x20>
    4be6:	48 83 c4 08          	add    $0x8,%rsp
    4bea:	5b                   	pop    %rbx
    4beb:	5d                   	pop    %rbp
    4bec:	c3                   	ret
    4bed:	0f 1f 00             	nopl   (%rax)

0000000000004bf0 <zh_malloc>:
    4bf0:	f3 0f 1e fa          	endbr64
    4bf4:	48 83 ec 08          	sub    $0x8,%rsp
    4bf8:	e8 73 d8 ff ff       	call   2470 <malloc@plt>
    4bfd:	48 85 c0             	test   %rax,%rax
    4c00:	74 05                	je     4c07 <zh_malloc+0x17>
    4c02:	48 83 c4 08          	add    $0x8,%rsp
    4c06:	c3                   	ret
    4c07:	48 8b 0d 12 64 00 00 	mov    0x6412(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4c0e:	ba 28 00 00 00       	mov    $0x28,%edx
    4c13:	be 01 00 00 00       	mov    $0x1,%esi
    4c18:	48 8d 3d c9 39 00 00 	lea    0x39c9(%rip),%rdi        # 85e8 <_IO_stdin_used+0x5e8>
    4c1f:	e8 0c d9 ff ff       	call   2530 <fwrite@plt>
    4c24:	bf 01 00 00 00       	mov    $0x1,%edi
    4c29:	e8 e2 d8 ff ff       	call   2510 <exit@plt>
    4c2e:	66 90                	xchg   %ax,%ax

0000000000004c30 <get_filename_ext>:
    4c30:	f3 0f 1e fa          	endbr64
    4c34:	53                   	push   %rbx
    4c35:	be 2e 00 00 00       	mov    $0x2e,%esi
    4c3a:	48 89 fb             	mov    %rdi,%rbx
    4c3d:	e8 6e d7 ff ff       	call   23b0 <strrchr@plt>
    4c42:	48 85 c0             	test   %rax,%rax
    4c45:	74 11                	je     4c58 <get_filename_ext+0x28>
    4c47:	48 39 c3             	cmp    %rax,%rbx
    4c4a:	74 0c                	je     4c58 <get_filename_ext+0x28>
    4c4c:	48 83 c0 01          	add    $0x1,%rax
    4c50:	5b                   	pop    %rbx
    4c51:	c3                   	ret
    4c52:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4c58:	48 8d 05 97 34 00 00 	lea    0x3497(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
    4c5f:	5b                   	pop    %rbx
    4c60:	c3                   	ret
    4c61:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4c6c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004c70 <send_headers>:
    4c70:	f3 0f 1e fa          	endbr64
    4c74:	41 55                	push   %r13
    4c76:	49 89 f5             	mov    %rsi,%r13
    4c79:	48 89 fe             	mov    %rdi,%rsi
    4c7c:	41 54                	push   %r12
    4c7e:	55                   	push   %rbp
    4c7f:	48 89 d5             	mov    %rdx,%rbp
    4c82:	ba 00 04 00 00       	mov    $0x400,%edx
    4c87:	53                   	push   %rbx
    4c88:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4c8f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4c98:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4ca0:	31 c0                	xor    %eax,%eax
    4ca2:	49 89 e4             	mov    %rsp,%r12
    4ca5:	4c 89 e7             	mov    %r12,%rdi
    4ca8:	e8 e3 d7 ff ff       	call   2490 <__strcpy_chk@plt>
    4cad:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4cb2:	84 db                	test   %bl,%bl
    4cb4:	74 24                	je     4cda <send_headers+0x6a>
    4cb6:	e8 d5 d8 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4cbb:	48 8b 08             	mov    (%rax),%rcx
    4cbe:	4c 89 e0             	mov    %r12,%rax
    4cc1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4cc8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    4ccb:	48 83 c0 01          	add    $0x1,%rax
    4ccf:	88 50 ff             	mov    %dl,-0x1(%rax)
    4cd2:	48 0f be 18          	movsbq (%rax),%rbx
    4cd6:	84 db                	test   %bl,%bl
    4cd8:	75 ee                	jne    4cc8 <send_headers+0x58>
    4cda:	bf 11 00 00 00       	mov    $0x11,%edi
    4cdf:	e8 8c d7 ff ff       	call   2470 <malloc@plt>
    4ce4:	48 85 c0             	test   %rax,%rax
    4ce7:	0f 84 7e 04 00 00    	je     516b <send_headers+0x4fb>
    4ced:	66 0f 6f 05 2b 3f 00 00 	movdqa 0x3f2b(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4cf5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    4cf9:	bf 17 00 00 00       	mov    $0x17,%edi
    4cfe:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4d06:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4d0a:	0f 11 00             	movups %xmm0,(%rax)
    4d0d:	e8 5e d7 ff ff       	call   2470 <malloc@plt>
    4d12:	48 85 c0             	test   %rax,%rax
    4d15:	0f 84 50 04 00 00    	je     516b <send_headers+0x4fb>
    4d1b:	66 0f 6f 05 0d 3f 00 00 	movdqa 0x3f0d(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    4d23:	48 89 45 10          	mov    %rax,0x10(%rbp)
    4d27:	4c 89 e7             	mov    %r12,%rdi
    4d2a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    4d34:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4d3c:	0f 11 00             	movups %xmm0,(%rax)
    4d3f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    4d43:	be 2e 00 00 00       	mov    $0x2e,%esi
    4d48:	e8 63 d6 ff ff       	call   23b0 <strrchr@plt>
    4d4d:	48 85 c0             	test   %rax,%rax
    4d50:	0f 84 ea 02 00 00    	je     5040 <send_headers+0x3d0>
    4d56:	4c 39 e0             	cmp    %r12,%rax
    4d59:	0f 84 e1 02 00 00    	je     5040 <send_headers+0x3d0>
    4d5f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    4d63:	48 8d 3d 5a 33 00 00 	lea    0x335a(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4d6a:	48 89 de             	mov    %rbx,%rsi
    4d6d:	e8 9e d6 ff ff       	call   2410 <strcmp@plt>
    4d72:	85 c0                	test   %eax,%eax
    4d74:	75 20                	jne    4d96 <send_headers+0x126>
    4d76:	66 0f 6f 05 c2 3e 00 00 	movdqa 0x3ec2(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    4d7e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4d86:	66 0f 6f 05 c2 3e 00 00 	movdqa 0x3ec2(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    4d8e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4d96:	48 89 de             	mov    %rbx,%rsi
    4d99:	48 8d 3d 28 33 00 00 	lea    0x3328(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4da0:	e8 6b d6 ff ff       	call   2410 <strcmp@plt>
    4da5:	85 c0                	test   %eax,%eax
    4da7:	75 20                	jne    4dc9 <send_headers+0x159>
    4da9:	66 0f 6f 05 8f 3e 00 00 	movdqa 0x3e8f(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    4db1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4db9:	66 0f 6f 05 8f 3e 00 00 	movdqa 0x3e8f(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    4dc1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4dc9:	48 89 de             	mov    %rbx,%rsi
    4dcc:	48 8d 3d fa 32 00 00 	lea    0x32fa(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4dd3:	e8 38 d6 ff ff       	call   2410 <strcmp@plt>
    4dd8:	85 c0                	test   %eax,%eax
    4dda:	0f 84 10 02 00 00    	je     4ff0 <send_headers+0x380>
    4de0:	48 89 de             	mov    %rbx,%rsi
    4de3:	48 8d 3d e7 32 00 00 	lea    0x32e7(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4dea:	e8 21 d6 ff ff       	call   2410 <strcmp@plt>
    4def:	85 c0                	test   %eax,%eax
    4df1:	0f 84 a9 02 00 00    	je     50a0 <send_headers+0x430>
    4df7:	48 89 de             	mov    %rbx,%rsi
    4dfa:	48 8d 3d d4 32 00 00 	lea    0x32d4(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4e01:	e8 0a d6 ff ff       	call   2410 <strcmp@plt>
    4e06:	85 c0                	test   %eax,%eax
    4e08:	0f 84 6a 02 00 00    	je     5078 <send_headers+0x408>
    4e0e:	48 89 de             	mov    %rbx,%rsi
    4e11:	48 8d 3d 00 33 00 00 	lea    0x3300(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4e18:	e8 f3 d5 ff ff       	call   2410 <strcmp@plt>
    4e1d:	85 c0                	test   %eax,%eax
    4e1f:	0f 84 2b 02 00 00    	je     5050 <send_headers+0x3e0>
    4e25:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4e28:	0f 84 52 01 00 00    	je     4f80 <send_headers+0x310>
    4e2e:	48 89 de             	mov    %rbx,%rsi
    4e31:	48 8d 3d a1 32 00 00 	lea    0x32a1(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4e38:	e8 d3 d5 ff ff       	call   2410 <strcmp@plt>
    4e3d:	85 c0                	test   %eax,%eax
    4e3f:	0f 84 ab 02 00 00    	je     50f0 <send_headers+0x480>
    4e45:	48 89 de             	mov    %rbx,%rsi
    4e48:	48 8d 3d 8e 32 00 00 	lea    0x328e(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4e4f:	e8 bc d5 ff ff       	call   2410 <strcmp@plt>
    4e54:	85 c0                	test   %eax,%eax
    4e56:	0f 84 6c 02 00 00    	je     50c8 <send_headers+0x458>
    4e5c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4e64:	4c 89 e7             	mov    %r12,%rdi
    4e67:	e8 04 d5 ff ff       	call   2370 <strlen@plt>
    4e6c:	48 89 c7             	mov    %rax,%rdi
    4e6f:	48 89 c3             	mov    %rax,%rbx
    4e72:	e8 f9 d5 ff ff       	call   2470 <malloc@plt>
    4e77:	48 85 c0             	test   %rax,%rax
    4e7a:	0f 84 eb 02 00 00    	je     516b <send_headers+0x4fb>
    4e80:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4e84:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    4e88:	83 fb 08             	cmp    $0x8,%ebx
    4e8b:	0f 83 3f 01 00 00    	jae    4fd0 <send_headers+0x360>
    4e91:	f6 c3 04             	test   $0x4,%bl
    4e94:	0f 85 7b 02 00 00    	jne    5115 <send_headers+0x4a5>
    4e9a:	85 db                	test   %ebx,%ebx
    4e9c:	74 13                	je     4eb1 <send_headers+0x241>
    4e9e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4ea6:	88 10                	mov    %dl,(%rax)
    4ea8:	f6 c3 02             	test   $0x2,%bl
    4eab:	0f 85 96 02 00 00    	jne    5147 <send_headers+0x4d7>
    4eb1:	4d 89 e8             	mov    %r13,%r8
    4eb4:	48 8d 0d 26 32 00 00 	lea    0x3226(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4ebb:	4c 89 e7             	mov    %r12,%rdi
    4ebe:	31 c0                	xor    %eax,%eax
    4ec0:	ba 00 04 00 00       	mov    $0x400,%edx
    4ec5:	be 01 00 00 00       	mov    $0x1,%esi
    4eca:	e8 d1 d6 ff ff       	call   25a0 <__sprintf_chk@plt>
    4ecf:	4c 89 e7             	mov    %r12,%rdi
    4ed2:	e8 99 d4 ff ff       	call   2370 <strlen@plt>
    4ed7:	48 89 c7             	mov    %rax,%rdi
    4eda:	48 89 c3             	mov    %rax,%rbx
    4edd:	e8 8e d5 ff ff       	call   2470 <malloc@plt>
    4ee2:	48 85 c0             	test   %rax,%rax
    4ee5:	0f 84 80 02 00 00    	je     516b <send_headers+0x4fb>
    4eeb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    4eef:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4ef3:	83 fb 08             	cmp    $0x8,%ebx
    4ef6:	0f 83 1c 01 00 00    	jae    5018 <send_headers+0x3a8>
    4efc:	f6 c3 04             	test   $0x4,%bl
    4eff:	0f 85 29 02 00 00    	jne    512e <send_headers+0x4be>
    4f05:	85 db                	test   %ebx,%ebx
    4f07:	74 13                	je     4f1c <send_headers+0x2ac>
    4f09:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4f11:	88 10                	mov    %dl,(%rax)
    4f13:	f6 c3 02             	test   $0x2,%bl
    4f16:	0f 85 3d 02 00 00    	jne    5159 <send_headers+0x4e9>
    4f1c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    4f21:	bf 02 00 00 00       	mov    $0x2,%edi
    4f26:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4f2e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4f36:	e8 35 d5 ff ff       	call   2470 <malloc@plt>
    4f3b:	48 85 c0             	test   %rax,%rax
    4f3e:	0f 84 27 02 00 00    	je     516b <send_headers+0x4fb>
    4f44:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    4f4c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    4f50:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4f58:	66 89 10             	mov    %dx,(%rax)
    4f5b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4f63:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4f6c:	0f 85 20 02 00 00    	jne    5192 <send_headers+0x522>
    4f72:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4f79:	5b                   	pop    %rbx
    4f7a:	5d                   	pop    %rbp
    4f7b:	41 5c                	pop    %r12
    4f7d:	41 5d                	pop    %r13
    4f7f:	c3                   	ret
    4f80:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4f84:	0f 85 a4 fe ff ff    	jne    4e2e <send_headers+0x1be>
    4f8a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4f8e:	0f 85 9a fe ff ff    	jne    4e2e <send_headers+0x1be>
    4f94:	66 0f 6f 05 04 3d 00 00 	movdqa 0x3d04(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
    4f9c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4fa6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4fae:	66 0f 6f 05 fa 3c 00 00 	movdqa 0x3cfa(%rip),%xmm0        # 8cb0 <_IO_stdin_used+0xcb0>
    4fb6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4fbe:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4fc6:	e9 63 fe ff ff       	jmp    4e2e <send_headers+0x1be>
    4fcb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4fd0:	89 da                	mov    %ebx,%edx
    4fd2:	48 89 c7             	mov    %rax,%rdi
    4fd5:	4c 89 e6             	mov    %r12,%rsi
    4fd8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4fdd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4fe2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4fe5:	c1 e9 03             	shr    $0x3,%ecx
    4fe8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4feb:	e9 c1 fe ff ff       	jmp    4eb1 <send_headers+0x241>
    4ff0:	66 0f 6f 05 48 3c 00 00 	movdqa 0x3c48(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    4ff8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5000:	66 0f 6f 05 58 3c 00 00 	movdqa 0x3c58(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    5008:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5010:	e9 cb fd ff ff       	jmp    4de0 <send_headers+0x170>
    5015:	0f 1f 00             	nopl   (%rax)
    5018:	89 da                	mov    %ebx,%edx
    501a:	48 89 c7             	mov    %rax,%rdi
    501d:	4c 89 e6             	mov    %r12,%rsi
    5020:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    5025:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    502a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    502d:	c1 e9 03             	shr    $0x3,%ecx
    5030:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    5033:	e9 e4 fe ff ff       	jmp    4f1c <send_headers+0x2ac>
    5038:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5040:	48 8d 1d af 30 00 00 	lea    0x30af(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    5047:	e9 94 fd ff ff       	jmp    4de0 <send_headers+0x170>
    504c:	0f 1f 40 00          	nopl   0x0(%rax)
    5050:	66 0f 6f 05 28 3c 00 00 	movdqa 0x3c28(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    5058:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5060:	66 0f 6f 05 28 3c 00 00 	movdqa 0x3c28(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    5068:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5070:	e9 b0 fd ff ff       	jmp    4e25 <send_headers+0x1b5>
    5075:	0f 1f 00             	nopl   (%rax)
    5078:	66 0f 6f 05 00 3c 00 00 	movdqa 0x3c00(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    5080:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5088:	66 0f 6f 05 00 3c 00 00 	movdqa 0x3c00(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    5090:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5098:	e9 71 fd ff ff       	jmp    4e0e <send_headers+0x19e>
    509d:	0f 1f 00             	nopl   (%rax)
    50a0:	66 0f 6f 05 98 3b 00 00 	movdqa 0x3b98(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    50a8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50b0:	66 0f 6f 05 b8 3b 00 00 	movdqa 0x3bb8(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    50b8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    50c0:	e9 32 fd ff ff       	jmp    4df7 <send_headers+0x187>
    50c5:	0f 1f 00             	nopl   (%rax)
    50c8:	66 0f 6f 05 b0 3b 00 00 	movdqa 0x3bb0(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    50d0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50d8:	66 0f 6f 05 f0 3b 00 00 	movdqa 0x3bf0(%rip),%xmm0        # 8cd0 <_IO_stdin_used+0xcd0>
    50e0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    50e8:	e9 6f fd ff ff       	jmp    4e5c <send_headers+0x1ec>
    50ed:	0f 1f 00             	nopl   (%rax)
    50f0:	66 0f 6f 05 88 3b 00 00 	movdqa 0x3b88(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    50f8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5100:	66 0f 6f 05 b8 3b 00 00 	movdqa 0x3bb8(%rip),%xmm0        # 8cc0 <_IO_stdin_used+0xcc0>
    5108:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    5110:	e9 30 fd ff ff       	jmp    4e45 <send_headers+0x1d5>
    5115:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    511c:	89 db                	mov    %ebx,%ebx
    511e:	89 10                	mov    %edx,(%rax)
    5120:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    5125:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5129:	e9 83 fd ff ff       	jmp    4eb1 <send_headers+0x241>
    512e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    5135:	89 db                	mov    %ebx,%ebx
    5137:	89 10                	mov    %edx,(%rax)
    5139:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    513e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5142:	e9 d5 fd ff ff       	jmp    4f1c <send_headers+0x2ac>
    5147:	89 db                	mov    %ebx,%ebx
    5149:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    514f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5154:	e9 58 fd ff ff       	jmp    4eb1 <send_headers+0x241>
    5159:	89 db                	mov    %ebx,%ebx
    515b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    5161:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5166:	e9 b1 fd ff ff       	jmp    4f1c <send_headers+0x2ac>
    516b:	48 8b 0d ae 5e 00 00 	mov    0x5eae(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5172:	ba 28 00 00 00       	mov    $0x28,%edx
    5177:	be 01 00 00 00       	mov    $0x1,%esi
    517c:	48 8d 3d 65 34 00 00 	lea    0x3465(%rip),%rdi        # 85e8 <_IO_stdin_used+0x5e8>
    5183:	e8 a8 d3 ff ff       	call   2530 <fwrite@plt>
    5188:	bf 01 00 00 00       	mov    $0x1,%edi
    518d:	e8 7e d3 ff ff       	call   2510 <exit@plt>
    5192:	e8 e9 d1 ff ff       	call   2380 <__stack_chk_fail@plt>
    5197:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000051a0 <copy_file_contents>:
    51a0:	f3 0f 1e fa          	endbr64
    51a4:	41 55                	push   %r13
    51a6:	49 89 d5             	mov    %rdx,%r13
    51a9:	41 54                	push   %r12
    51ab:	49 89 fc             	mov    %rdi,%r12
    51ae:	48 89 f7             	mov    %rsi,%rdi
    51b1:	55                   	push   %rbp
    51b2:	53                   	push   %rbx
    51b3:	48 89 f3             	mov    %rsi,%rbx
    51b6:	48 83 ec 08          	sub    $0x8,%rsp
    51ba:	e8 b1 d2 ff ff       	call   2470 <malloc@plt>
    51bf:	48 85 c0             	test   %rax,%rax
    51c2:	74 6b                	je     522f <copy_file_contents+0x8f>
    51c4:	4c 89 e7             	mov    %r12,%rdi
    51c7:	48 89 c5             	mov    %rax,%rbp
    51ca:	31 f6                	xor    %esi,%esi
    51cc:	31 c0                	xor    %eax,%eax
    51ce:	e8 0d d3 ff ff       	call   24e0 <open@plt>
    51d3:	41 89 c4             	mov    %eax,%r12d
    51d6:	85 c0                	test   %eax,%eax
    51d8:	0f 88 f8 d3 ff ff    	js     25d6 <copy_file_contents.cold>
    51de:	48 89 da             	mov    %rbx,%rdx
    51e1:	48 89 ee             	mov    %rbp,%rsi
    51e4:	89 c7                	mov    %eax,%edi
    51e6:	e8 05 d2 ff ff       	call   23f0 <read@plt>
    51eb:	48 98                	cltq
    51ed:	48 39 d8             	cmp    %rbx,%rax
    51f0:	7c 1e                	jl     5210 <copy_file_contents+0x70>
    51f2:	44 89 e7             	mov    %r12d,%edi
    51f5:	e8 d6 d1 ff ff       	call   23d0 <close@plt>
    51fa:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    51fe:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    5202:	48 83 c4 08          	add    $0x8,%rsp
    5206:	5b                   	pop    %rbx
    5207:	5d                   	pop    %rbp
    5208:	41 5c                	pop    %r12
    520a:	41 5d                	pop    %r13
    520c:	c3                   	ret
    520d:	0f 1f 00             	nopl   (%rax)
    5210:	48 8b 0d 09 5e 00 00 	mov    0x5e09(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5217:	ba 1a 00 00 00       	mov    $0x1a,%edx
    521c:	be 01 00 00 00       	mov    $0x1,%esi
    5221:	48 8d 3d cf 2e 00 00 	lea    0x2ecf(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    5228:	e8 03 d3 ff ff       	call   2530 <fwrite@plt>
    522d:	eb c3                	jmp    51f2 <copy_file_contents+0x52>
    522f:	48 8b 0d ea 5d 00 00 	mov    0x5dea(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5236:	ba 28 00 00 00       	mov    $0x28,%edx
    523b:	be 01 00 00 00       	mov    $0x1,%esi
    5240:	48 8d 3d a1 33 00 00 	lea    0x33a1(%rip),%rdi        # 85e8 <_IO_stdin_used+0x5e8>
    5247:	e8 e4 d2 ff ff       	call   2530 <fwrite@plt>
    524c:	bf 01 00 00 00       	mov    $0x1,%edi
    5251:	e8 ba d2 ff ff       	call   2510 <exit@plt>
    5256:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005260 <add_write_request>:
    5260:	f3 0f 1e fa          	endbr64
    5264:	8b 46 44             	mov    0x44(%rsi),%eax
    5267:	48 89 fa             	mov    %rdi,%rdx
    526a:	48 89 f7             	mov    %rsi,%rdi
    526d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    5273:	8d 70 01             	lea    0x1(%rax),%esi
    5276:	48 8b 07             	mov    (%rdi),%rax
    5279:	44 8b 00             	mov    (%rax),%r8d
    527c:	f6 c1 02             	test   $0x2,%cl
    527f:	74 00                	je     5281 <add_write_request+0x21>
    5281:	89 f0                	mov    %esi,%eax
    5283:	44 29 c0             	sub    %r8d,%eax
    5286:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    5289:	0f 82 53 d3 ff ff    	jb     25e2 <add_write_request.cold>
    528f:	c1 e9 0a             	shr    $0xa,%ecx
    5292:	48 83 ec 08          	sub    $0x8,%rsp
    5296:	8b 47 44             	mov    0x44(%rdi),%eax
    5299:	23 47 58             	and    0x58(%rdi),%eax
    529c:	83 e1 01             	and    $0x1,%ecx
    529f:	89 77 44             	mov    %esi,0x44(%rdi)
    52a2:	8b 72 08             	mov    0x8(%rdx),%esi
    52a5:	66 0f ef c0          	pxor   %xmm0,%xmm0
    52a9:	d3 e0                	shl    %cl,%eax
    52ab:	8b 4a 04             	mov    0x4(%rdx),%ecx
    52ae:	48 c1 e0 06          	shl    $0x6,%rax
    52b2:	48 03 47 38          	add    0x38(%rdi),%rax
    52b6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    52bc:	89 70 04             	mov    %esi,0x4(%rax)
    52bf:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    52c3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    52c9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    52d1:	48 89 70 10          	mov    %rsi,0x10(%rax)
    52d5:	89 48 18             	mov    %ecx,0x18(%rax)
    52d8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    52df:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    52e7:	48 89 50 20          	mov    %rdx,0x20(%rax)
    52eb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    52ef:	e8 9c d0 ff ff       	call   2390 <io_uring_submit@plt>
    52f4:	31 c0                	xor    %eax,%eax
    52f6:	48 83 c4 08          	add    $0x8,%rsp
    52fa:	c3                   	ret
    52fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005300 <add_read_request>:
    5300:	f3 0f 1e fa          	endbr64
    5304:	41 55                	push   %r13
    5306:	41 89 fd             	mov    %edi,%r13d
    5309:	41 54                	push   %r12
    530b:	55                   	push   %rbp
    530c:	53                   	push   %rbx
    530d:	48 89 f3             	mov    %rsi,%rbx
    5310:	48 83 ec 08          	sub    $0x8,%rsp
    5314:	8b 46 44             	mov    0x44(%rsi),%eax
    5317:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    531d:	48 8b 16             	mov    (%rsi),%rdx
    5320:	83 c0 01             	add    $0x1,%eax
    5323:	8b 32                	mov    (%rdx),%esi
    5325:	f6 c1 02             	test   $0x2,%cl
    5328:	74 00                	je     532a <add_read_request+0x2a>
    532a:	89 c2                	mov    %eax,%edx
    532c:	29 f2                	sub    %esi,%edx
    532e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5331:	0f 82 bb d2 ff ff    	jb     25f2 <add_read_request.cold>
    5337:	8b 6b 44             	mov    0x44(%rbx),%ebp
    533a:	c1 e9 0a             	shr    $0xa,%ecx
    533d:	89 43 44             	mov    %eax,0x44(%rbx)
    5340:	bf 20 00 00 00       	mov    $0x20,%edi
    5345:	83 e1 01             	and    $0x1,%ecx
    5348:	23 6b 58             	and    0x58(%rbx),%ebp
    534b:	d3 e5                	shl    %cl,%ebp
    534d:	48 c1 e5 06          	shl    $0x6,%rbp
    5351:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5355:	e8 16 d1 ff ff       	call   2470 <malloc@plt>
    535a:	be 01 00 00 00       	mov    $0x1,%esi
    535f:	bf 00 20 00 00       	mov    $0x2000,%edi
    5364:	49 89 c4             	mov    %rax,%r12
    5367:	e8 94 d0 ff ff       	call   2400 <calloc@plt>
    536c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    5371:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5375:	48 89 df             	mov    %rbx,%rdi
    5378:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    537d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    5382:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    538b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    5393:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    5397:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    539b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    53a2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    53aa:	48 89 45 10          	mov    %rax,0x10(%rbp)
    53ae:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    53b6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    53be:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    53c2:	e8 c9 cf ff ff       	call   2390 <io_uring_submit@plt>
    53c7:	48 83 c4 08          	add    $0x8,%rsp
    53cb:	31 c0                	xor    %eax,%eax
    53cd:	5b                   	pop    %rbx
    53ce:	5d                   	pop    %rbp
    53cf:	41 5c                	pop    %r12
    53d1:	41 5d                	pop    %r13
    53d3:	c3                   	ret
    53d4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    53df:	90                   	nop

00000000000053e0 <_send_static_string_content>:
    53e0:	f3 0f 1e fa          	endbr64
    53e4:	41 56                	push   %r14
    53e6:	41 89 f6             	mov    %esi,%r14d
    53e9:	41 55                	push   %r13
    53eb:	49 89 fd             	mov    %rdi,%r13
    53ee:	bf 20 00 00 00       	mov    $0x20,%edi
    53f3:	41 54                	push   %r12
    53f5:	55                   	push   %rbp
    53f6:	48 89 d5             	mov    %rdx,%rbp
    53f9:	53                   	push   %rbx
    53fa:	e8 71 d0 ff ff       	call   2470 <malloc@plt>
    53ff:	48 85 c0             	test   %rax,%rax
    5402:	0f 84 dd 00 00 00    	je     54e5 <_send_static_string_content+0x105>
    5408:	48 89 c3             	mov    %rax,%rbx
    540b:	4c 89 ef             	mov    %r13,%rdi
    540e:	e8 5d cf ff ff       	call   2370 <strlen@plt>
    5413:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    541a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    541e:	48 89 c7             	mov    %rax,%rdi
    5421:	49 89 c4             	mov    %rax,%r12
    5424:	e8 47 d0 ff ff       	call   2470 <malloc@plt>
    5429:	48 89 c7             	mov    %rax,%rdi
    542c:	48 85 c0             	test   %rax,%rax
    542f:	0f 84 b0 00 00 00    	je     54e5 <_send_static_string_content+0x105>
    5435:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5439:	4c 89 e2             	mov    %r12,%rdx
    543c:	4c 89 ee             	mov    %r13,%rsi
    543f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    5443:	e8 f8 cf ff ff       	call   2440 <memcpy@plt>
    5448:	8b 45 44             	mov    0x44(%rbp),%eax
    544b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    5451:	8d 50 01             	lea    0x1(%rax),%edx
    5454:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5458:	8b 30                	mov    (%rax),%esi
    545a:	f6 c1 02             	test   $0x2,%cl
    545d:	0f 85 7d 00 00 00    	jne    54e0 <_send_static_string_content+0x100>
    5463:	89 d0                	mov    %edx,%eax
    5465:	29 f0                	sub    %esi,%eax
    5467:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    546a:	0f 82 8c d1 ff ff    	jb     25fc <_send_static_string_content.cold>
    5470:	c1 e9 0a             	shr    $0xa,%ecx
    5473:	8b 45 44             	mov    0x44(%rbp),%eax
    5476:	23 45 58             	and    0x58(%rbp),%eax
    5479:	89 55 44             	mov    %edx,0x44(%rbp)
    547c:	83 e1 01             	and    $0x1,%ecx
    547f:	8b 53 04             	mov    0x4(%rbx),%edx
    5482:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    5488:	66 0f ef c0          	pxor   %xmm0,%xmm0
    548c:	d3 e0                	shl    %cl,%eax
    548e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    5491:	48 89 ef             	mov    %rbp,%rdi
    5494:	48 c1 e0 06          	shl    $0x6,%rax
    5498:	48 03 45 38          	add    0x38(%rbp),%rax
    549c:	89 48 04             	mov    %ecx,0x4(%rax)
    549f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    54a3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    54a9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    54b1:	48 89 48 10          	mov    %rcx,0x10(%rax)
    54b5:	89 50 18             	mov    %edx,0x18(%rax)
    54b8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    54bf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    54c7:	48 89 58 20          	mov    %rbx,0x20(%rax)
    54cb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    54cf:	5b                   	pop    %rbx
    54d0:	5d                   	pop    %rbp
    54d1:	41 5c                	pop    %r12
    54d3:	41 5d                	pop    %r13
    54d5:	41 5e                	pop    %r14
    54d7:	e9 b4 ce ff ff       	jmp    2390 <io_uring_submit@plt>
    54dc:	0f 1f 40 00          	nopl   0x0(%rax)
    54e0:	e9 7e ff ff ff       	jmp    5463 <_send_static_string_content+0x83>
    54e5:	48 8b 0d 34 5b 00 00 	mov    0x5b34(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    54ec:	ba 28 00 00 00       	mov    $0x28,%edx
    54f1:	be 01 00 00 00       	mov    $0x1,%esi
    54f6:	48 8d 3d eb 30 00 00 	lea    0x30eb(%rip),%rdi        # 85e8 <_IO_stdin_used+0x5e8>
    54fd:	e8 2e d0 ff ff       	call   2530 <fwrite@plt>
    5502:	bf 01 00 00 00       	mov    $0x1,%edi
    5507:	e8 04 d0 ff ff       	call   2510 <exit@plt>
    550c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005510 <handle_unimplemented_method>:
    5510:	f3 0f 1e fa          	endbr64
    5514:	48 89 f2             	mov    %rsi,%rdx
    5517:	89 fe                	mov    %edi,%esi
    5519:	48 8b 3d f8 5a 00 00 	mov    0x5af8(%rip),%rdi        # b018 <unimplemented_content>
    5520:	e9 bb fe ff ff       	jmp    53e0 <_send_static_string_content>
    5525:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005530 <handle_http_404>:
    5530:	f3 0f 1e fa          	endbr64
    5534:	48 89 f2             	mov    %rsi,%rdx
    5537:	89 fe                	mov    %edi,%esi
    5539:	48 8b 3d d0 5a 00 00 	mov    0x5ad0(%rip),%rdi        # b010 <http_404_content>
    5540:	e9 9b fe ff ff       	jmp    53e0 <_send_static_string_content>
    5545:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005550 <handle_get_method>:
    5550:	f3 0f 1e fa          	endbr64
    5554:	41 56                	push   %r14
    5556:	41 55                	push   %r13
    5558:	49 89 d5             	mov    %rdx,%r13
    555b:	41 54                	push   %r12
    555d:	41 89 f4             	mov    %esi,%r12d
    5560:	55                   	push   %rbp
    5561:	48 89 fd             	mov    %rdi,%rbp
    5564:	53                   	push   %rbx
    5565:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    556c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5575:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    557d:	31 c0                	xor    %eax,%eax
    557f:	e8 ec cd ff ff       	call   2370 <strlen@plt>
    5584:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    5589:	48 89 c3             	mov    %rax,%rbx
    558c:	0f 84 b6 00 00 00    	je     5648 <handle_get_method+0xf8>
    5592:	b8 69 63 00 00       	mov    $0x6369,%eax
    5597:	48 89 ee             	mov    %rbp,%rsi
    559a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    559e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    55a3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    55ab:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    55b3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    55be:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    55c6:	e8 55 ce ff ff       	call   2420 <__memcpy_chk@plt>
    55cb:	48 89 e6             	mov    %rsp,%rsi
    55ce:	4c 89 f7             	mov    %r14,%rdi
    55d1:	e8 5a ce ff ff       	call   2430 <stat@plt>
    55d6:	83 f8 ff             	cmp    $0xffffffff,%eax
    55d9:	0f 84 d3 00 00 00    	je     56b2 <handle_get_method+0x162>
    55df:	8b 44 24 18          	mov    0x18(%rsp),%eax
    55e3:	25 00 f0 00 00       	and    $0xf000,%eax
    55e8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    55ed:	0f 84 f5 00 00 00    	je     56e8 <handle_get_method+0x198>
    55f3:	48 8b 3d 16 5a 00 00 	mov    0x5a16(%rip),%rdi        # b010 <http_404_content>
    55fa:	4c 89 ea             	mov    %r13,%rdx
    55fd:	44 89 e6             	mov    %r12d,%esi
    5600:	e8 db fd ff ff       	call   53e0 <_send_static_string_content>
    5605:	4c 89 f2             	mov    %r14,%rdx
    5608:	bf 01 00 00 00       	mov    $0x1,%edi
    560d:	31 c0                	xor    %eax,%eax
    560f:	48 8d 35 31 2b 00 00 	lea    0x2b31(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    5616:	e8 95 ce ff ff       	call   24b0 <__printf_chk@plt>
    561b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5623:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    562c:	0f 85 20 01 00 00    	jne    5752 <handle_get_method+0x202>
    5632:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5639:	5b                   	pop    %rbx
    563a:	5d                   	pop    %rbp
    563b:	41 5c                	pop    %r12
    563d:	41 5d                	pop    %r13
    563f:	41 5e                	pop    %r14
    5641:	c3                   	ret
    5642:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5648:	ba 69 63 00 00       	mov    $0x6369,%edx
    564d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5655:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    565a:	48 89 ee             	mov    %rbp,%rsi
    565d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    5665:	48 89 c2             	mov    %rax,%rdx
    5668:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5670:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    567b:	e8 a0 cd ff ff       	call   2420 <__memcpy_chk@plt>
    5680:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5685:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    568a:	48 8d 35 81 2a 00 00 	lea    0x2a81(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    5691:	48 29 d9             	sub    %rbx,%rcx
    5694:	ba 0b 00 00 00       	mov    $0xb,%edx
    5699:	e8 82 cd ff ff       	call   2420 <__memcpy_chk@plt>
    569e:	48 89 e6             	mov    %rsp,%rsi
    56a1:	4c 89 f7             	mov    %r14,%rdi
    56a4:	e8 87 cd ff ff       	call   2430 <stat@plt>
    56a9:	83 f8 ff             	cmp    $0xffffffff,%eax
    56ac:	0f 85 2d ff ff ff    	jne    55df <handle_get_method+0x8f>
    56b2:	4c 89 f2             	mov    %r14,%rdx
    56b5:	48 89 e9             	mov    %rbp,%rcx
    56b8:	48 8d 35 5e 2a 00 00 	lea    0x2a5e(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    56bf:	31 c0                	xor    %eax,%eax
    56c1:	bf 01 00 00 00       	mov    $0x1,%edi
    56c6:	e8 e5 cd ff ff       	call   24b0 <__printf_chk@plt>
    56cb:	48 8b 3d 3e 59 00 00 	mov    0x593e(%rip),%rdi        # b010 <http_404_content>
    56d2:	4c 89 ea             	mov    %r13,%rdx
    56d5:	44 89 e6             	mov    %r12d,%esi
    56d8:	e8 03 fd ff ff       	call   53e0 <_send_static_string_content>
    56dd:	e9 39 ff ff ff       	jmp    561b <handle_get_method+0xcb>
    56e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    56e8:	bf 70 00 00 00       	mov    $0x70,%edi
    56ed:	e8 7e cd ff ff       	call   2470 <malloc@plt>
    56f2:	48 89 c3             	mov    %rax,%rbx
    56f5:	48 85 c0             	test   %rax,%rax
    56f8:	74 5d                	je     5757 <handle_get_method+0x207>
    56fa:	44 89 60 08          	mov    %r12d,0x8(%rax)
    56fe:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5703:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5707:	4c 89 f7             	mov    %r14,%rdi
    570a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    5711:	e8 5a f5 ff ff       	call   4c70 <send_headers>
    5716:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    571b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    571f:	4c 89 f7             	mov    %r14,%rdi
    5722:	e8 79 fa ff ff       	call   51a0 <copy_file_contents>
    5727:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    572c:	4c 89 f2             	mov    %r14,%rdx
    572f:	31 c0                	xor    %eax,%eax
    5731:	48 8d 35 fd 29 00 00 	lea    0x29fd(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    5738:	bf 01 00 00 00       	mov    $0x1,%edi
    573d:	e8 6e cd ff ff       	call   24b0 <__printf_chk@plt>
    5742:	4c 89 ee             	mov    %r13,%rsi
    5745:	48 89 df             	mov    %rbx,%rdi
    5748:	e8 13 fb ff ff       	call   5260 <add_write_request>
    574d:	e9 c9 fe ff ff       	jmp    561b <handle_get_method+0xcb>
    5752:	e8 29 cc ff ff       	call   2380 <__stack_chk_fail@plt>
    5757:	48 8b 0d c2 58 00 00 	mov    0x58c2(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    575e:	ba 28 00 00 00       	mov    $0x28,%edx
    5763:	be 01 00 00 00       	mov    $0x1,%esi
    5768:	48 8d 3d 79 2e 00 00 	lea    0x2e79(%rip),%rdi        # 85e8 <_IO_stdin_used+0x5e8>
    576f:	e8 bc cd ff ff       	call   2530 <fwrite@plt>
    5774:	bf 01 00 00 00       	mov    $0x1,%edi
    5779:	e8 92 cd ff ff       	call   2510 <exit@plt>
    577e:	66 90                	xchg   %ax,%ax

0000000000005780 <handle_http_method>:
    5780:	f3 0f 1e fa          	endbr64
    5784:	41 57                	push   %r15
    5786:	41 56                	push   %r14
    5788:	4c 8d 35 1d 29 00 00 	lea    0x291d(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
    578f:	41 55                	push   %r13
    5791:	49 89 d5             	mov    %rdx,%r13
    5794:	41 54                	push   %r12
    5796:	41 89 f4             	mov    %esi,%r12d
    5799:	4c 89 f6             	mov    %r14,%rsi
    579c:	55                   	push   %rbp
    579d:	53                   	push   %rbx
    579e:	48 83 ec 18          	sub    $0x18,%rsp
    57a2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    57ab:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    57b0:	31 c0                	xor    %eax,%eax
    57b2:	49 89 e7             	mov    %rsp,%r15
    57b5:	4c 89 fa             	mov    %r15,%rdx
    57b8:	e8 23 cc ff ff       	call   23e0 <strtok_r@plt>
    57bd:	48 0f be 18          	movsbq (%rax),%rbx
    57c1:	48 89 c5             	mov    %rax,%rbp
    57c4:	84 db                	test   %bl,%bl
    57c6:	74 1d                	je     57e5 <handle_http_method+0x65>
    57c8:	e8 c3 cd ff ff       	call   2590 <__ctype_tolower_loc@plt>
    57cd:	48 89 ea             	mov    %rbp,%rdx
    57d0:	48 8b 08             	mov    (%rax),%rcx
    57d3:	48 83 c2 01          	add    $0x1,%rdx
    57d7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    57da:	88 4a ff             	mov    %cl,-0x1(%rdx)
    57dd:	48 0f be 1a          	movsbq (%rdx),%rbx
    57e1:	84 db                	test   %bl,%bl
    57e3:	75 eb                	jne    57d0 <handle_http_method+0x50>
    57e5:	4c 89 fa             	mov    %r15,%rdx
    57e8:	4c 89 f6             	mov    %r14,%rsi
    57eb:	31 ff                	xor    %edi,%edi
    57ed:	e8 ee cb ff ff       	call   23e0 <strtok_r@plt>
    57f2:	48 8d 35 61 29 00 00 	lea    0x2961(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    57f9:	48 89 ef             	mov    %rbp,%rdi
    57fc:	48 89 c3             	mov    %rax,%rbx
    57ff:	e8 0c cc ff ff       	call   2410 <strcmp@plt>
    5804:	4c 89 ea             	mov    %r13,%rdx
    5807:	44 89 e6             	mov    %r12d,%esi
    580a:	85 c0                	test   %eax,%eax
    580c:	75 2a                	jne    5838 <handle_http_method+0xb8>
    580e:	48 89 df             	mov    %rbx,%rdi
    5811:	e8 3a fd ff ff       	call   5550 <handle_get_method>
    5816:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    581b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5824:	75 20                	jne    5846 <handle_http_method+0xc6>
    5826:	48 83 c4 18          	add    $0x18,%rsp
    582a:	5b                   	pop    %rbx
    582b:	5d                   	pop    %rbp
    582c:	41 5c                	pop    %r12
    582e:	41 5d                	pop    %r13
    5830:	41 5e                	pop    %r14
    5832:	41 5f                	pop    %r15
    5834:	c3                   	ret
    5835:	0f 1f 00             	nopl   (%rax)
    5838:	48 8b 3d d9 57 00 00 	mov    0x57d9(%rip),%rdi        # b018 <unimplemented_content>
    583f:	e8 9c fb ff ff       	call   53e0 <_send_static_string_content>
    5844:	eb d0                	jmp    5816 <handle_http_method+0x96>
    5846:	e8 35 cb ff ff       	call   2380 <__stack_chk_fail@plt>
    584b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005850 <get_line>:
    5850:	f3 0f 1e fa          	endbr64
    5854:	85 d2                	test   %edx,%edx
    5856:	7e 38                	jle    5890 <get_line+0x40>
    5858:	48 63 d2             	movslq %edx,%rdx
    585b:	48 83 c7 01          	add    $0x1,%rdi
    585f:	48 01 f2             	add    %rsi,%rdx
    5862:	eb 11                	jmp    5875 <get_line+0x25>
    5864:	0f 1f 40 00          	nopl   0x0(%rax)
    5868:	48 83 c6 01          	add    $0x1,%rsi
    586c:	48 83 c7 01          	add    $0x1,%rdi
    5870:	48 39 d6             	cmp    %rdx,%rsi
    5873:	74 1b                	je     5890 <get_line+0x40>
    5875:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5879:	88 06                	mov    %al,(%rsi)
    587b:	3c 0d                	cmp    $0xd,%al
    587d:	75 e9                	jne    5868 <get_line+0x18>
    587f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5882:	75 e4                	jne    5868 <get_line+0x18>
    5884:	c6 06 00             	movb   $0x0,(%rsi)
    5887:	31 c0                	xor    %eax,%eax
    5889:	c3                   	ret
    588a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5890:	b8 01 00 00 00       	mov    $0x1,%eax
    5895:	c3                   	ret
    5896:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000058a0 <handle_client_request>:
    58a0:	f3 0f 1e fa          	endbr64
    58a4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    58ab:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    58af:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    58b8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    58c0:	31 c0                	xor    %eax,%eax
    58c2:	49 89 e2             	mov    %rsp,%r10
    58c5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    58cd:	4c 89 d0             	mov    %r10,%rax
    58d0:	eb 13                	jmp    58e5 <handle_client_request+0x45>
    58d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    58d8:	48 83 c0 01          	add    $0x1,%rax
    58dc:	48 83 c1 01          	add    $0x1,%rcx
    58e0:	4c 39 c8             	cmp    %r9,%rax
    58e3:	74 4b                	je     5930 <handle_client_request+0x90>
    58e5:	44 0f b6 01          	movzbl (%rcx),%r8d
    58e9:	44 88 00             	mov    %r8b,(%rax)
    58ec:	41 80 f8 0d          	cmp    $0xd,%r8b
    58f0:	75 e6                	jne    58d8 <handle_client_request+0x38>
    58f2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    58f6:	75 e0                	jne    58d8 <handle_client_request+0x38>
    58f8:	c6 00 00             	movb   $0x0,(%rax)
    58fb:	8b 47 08             	mov    0x8(%rdi),%eax
    58fe:	48 89 f2             	mov    %rsi,%rdx
    5901:	4c 89 d7             	mov    %r10,%rdi
    5904:	89 c6                	mov    %eax,%esi
    5906:	e8 75 fe ff ff       	call   5780 <handle_http_method>
    590b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5913:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    591c:	75 39                	jne    5957 <handle_client_request+0xb7>
    591e:	31 c0                	xor    %eax,%eax
    5920:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5927:	c3                   	ret
    5928:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5930:	48 8b 0d e9 56 00 00 	mov    0x56e9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5937:	ba 12 00 00 00       	mov    $0x12,%edx
    593c:	be 01 00 00 00       	mov    $0x1,%esi
    5941:	48 8d 3d 16 28 00 00 	lea    0x2816(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5948:	e8 e3 cb ff ff       	call   2530 <fwrite@plt>
    594d:	bf 01 00 00 00       	mov    $0x1,%edi
    5952:	e8 b9 cb ff ff       	call   2510 <exit@plt>
    5957:	e8 24 ca ff ff       	call   2380 <__stack_chk_fail@plt>
    595c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005960 <add_accept_request>:
    5960:	f3 0f 1e fa          	endbr64
    5964:	55                   	push   %rbp
    5965:	53                   	push   %rbx
    5966:	48 89 cb             	mov    %rcx,%rbx
    5969:	48 83 ec 08          	sub    $0x8,%rsp
    596d:	8b 41 44             	mov    0x44(%rcx),%eax
    5970:	4c 8b 03             	mov    (%rbx),%r8
    5973:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    5979:	83 c0 01             	add    $0x1,%eax
    597c:	45 8b 08             	mov    (%r8),%r9d
    597f:	f6 c1 02             	test   $0x2,%cl
    5982:	74 00                	je     5984 <add_accept_request+0x24>
    5984:	41 89 c0             	mov    %eax,%r8d
    5987:	45 29 c8             	sub    %r9d,%r8d
    598a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    598e:	0f 82 78 cc ff ff    	jb     260c <add_accept_request.cold>
    5994:	c1 e9 0a             	shr    $0xa,%ecx
    5997:	8b 6b 44             	mov    0x44(%rbx),%ebp
    599a:	23 6b 58             	and    0x58(%rbx),%ebp
    599d:	89 43 44             	mov    %eax,0x44(%rbx)
    59a0:	83 e1 01             	and    $0x1,%ecx
    59a3:	66 0f ef c0          	pxor   %xmm0,%xmm0
    59a7:	d3 e5                	shl    %cl,%ebp
    59a9:	48 c1 e5 06          	shl    $0x6,%rbp
    59ad:	48 03 6b 38          	add    0x38(%rbx),%rbp
    59b1:	89 7d 04             	mov    %edi,0x4(%rbp)
    59b4:	bf 10 00 00 00       	mov    $0x10,%edi
    59b9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    59c0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    59c4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    59c8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    59d0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    59d8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    59dc:	e8 8f ca ff ff       	call   2470 <malloc@plt>
    59e1:	48 89 df             	mov    %rbx,%rdi
    59e4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    59ea:	48 89 45 20          	mov    %rax,0x20(%rbp)
    59ee:	48 83 c4 08          	add    $0x8,%rsp
    59f2:	5b                   	pop    %rbx
    59f3:	5d                   	pop    %rbp
    59f4:	e9 97 c9 ff ff       	jmp    2390 <io_uring_submit@plt>
    59f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005a00 <io_thread>:
    5a00:	f3 0f 1e fa          	endbr64
    5a04:	41 57                	push   %r15
    5a06:	31 d2                	xor    %edx,%edx
    5a08:	41 56                	push   %r14
    5a0a:	41 55                	push   %r13
    5a0c:	41 54                	push   %r12
    5a0e:	55                   	push   %rbp
    5a0f:	48 89 fd             	mov    %rdi,%rbp
    5a12:	53                   	push   %rbx
    5a13:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    5a1a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5a23:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    5a2b:	48 8b 47 58          	mov    0x58(%rdi),%rax
    5a2f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5a34:	bf 00 01 00 00       	mov    $0x100,%edi
    5a39:	48 89 de             	mov    %rbx,%rsi
    5a3c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5a40:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5a45:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    5a4a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    5a4f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5a54:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    5a5c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5a61:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5a69:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5a6e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5a76:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5a7b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5a83:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5a88:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5a90:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5a95:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    5a9d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5aa5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    5aad:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5ab5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    5abd:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5ac5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5acd:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5ad5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5add:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5ae5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5aed:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5af4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    5afc:	e8 4f c9 ff ff       	call   2450 <io_uring_queue_init@plt>
    5b01:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5b05:	31 f6                	xor    %esi,%esi
    5b07:	e8 44 ca ff ff       	call   2550 <io_uring_register_eventfd@plt>
    5b0c:	31 d2                	xor    %edx,%edx
    5b0e:	be 01 00 00 00       	mov    $0x1,%esi
    5b13:	bf 02 00 00 00       	mov    $0x2,%edi
    5b18:	e8 93 ca ff ff       	call   25b0 <socket@plt>
    5b1d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5b20:	0f 84 28 cb ff ff    	je     264e <io_thread.cold+0x38>
    5b26:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5b2b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5b31:	89 c7                	mov    %eax,%edi
    5b33:	41 89 c4             	mov    %eax,%r12d
    5b36:	ba 02 00 00 00       	mov    $0x2,%edx
    5b3b:	be 01 00 00 00       	mov    $0x1,%esi
    5b40:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    5b48:	e8 f3 c7 ff ff       	call   2340 <setsockopt@plt>
    5b4d:	85 c0                	test   %eax,%eax
    5b4f:	0f 88 cd ca ff ff    	js     2622 <io_thread.cold+0xc>
    5b55:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    5b5a:	ba 10 00 00 00       	mov    $0x10,%edx
    5b5f:	44 89 e7             	mov    %r12d,%edi
    5b62:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5b6b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    5b73:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
    5b7b:	e8 40 c9 ff ff       	call   24c0 <bind@plt>
    5b80:	85 c0                	test   %eax,%eax
    5b82:	0f 88 d2 ca ff ff    	js     265a <io_thread.cold+0x44>
    5b88:	be 0a 00 00 00       	mov    $0xa,%esi
    5b8d:	44 89 e7             	mov    %r12d,%edi
    5b90:	e8 eb c8 ff ff       	call   2480 <listen@plt>
    5b95:	85 c0                	test   %eax,%eax
    5b97:	0f 88 91 ca ff ff    	js     262e <io_thread.cold+0x18>
    5b9d:	ba db 18 00 00       	mov    $0x18db,%edx
    5ba2:	48 8d 35 fa 25 00 00 	lea    0x25fa(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5ba9:	bf 01 00 00 00       	mov    $0x1,%edi
    5bae:	31 c0                	xor    %eax,%eax
    5bb0:	e8 fb c8 ff ff       	call   24b0 <__printf_chk@plt>
    5bb5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5bba:	48 89 d9             	mov    %rbx,%rcx
    5bbd:	44 89 e7             	mov    %r12d,%edi
    5bc0:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5bc5:	48 89 c6             	mov    %rax,%rsi
    5bc8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5bcd:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    5bd2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    5bda:	e8 81 fd ff ff       	call   5960 <add_accept_request>
    5bdf:	bf 01 00 00 00       	mov    $0x1,%edi
    5be4:	be 10 00 00 00       	mov    $0x10,%esi
    5be9:	e8 12 c8 ff ff       	call   2400 <calloc@plt>
    5bee:	bf 0a 00 00 00       	mov    $0xa,%edi
    5bf3:	49 89 c5             	mov    %rax,%r13
    5bf6:	e8 75 c8 ff ff       	call   2470 <malloc@plt>
    5bfb:	48 85 c0             	test   %rax,%rax
    5bfe:	0f 84 ae 04 00 00    	je     60b2 <io_thread+0x6b2>
    5c04:	49 89 45 00          	mov    %rax,0x0(%r13)
    5c08:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5c0f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5c16:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    5c1e:	8d 50 01             	lea    0x1(%rax),%edx
    5c21:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5c26:	8b 30                	mov    (%rax),%esi
    5c28:	f6 c1 02             	test   $0x2,%cl
    5c2b:	0f 85 0f 04 00 00    	jne    6040 <io_thread+0x640>
    5c31:	89 d0                	mov    %edx,%eax
    5c33:	29 f0                	sub    %esi,%eax
    5c35:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5c3c:	0f 82 02 ca ff ff    	jb     2644 <io_thread.cold+0x2e>
    5c42:	c1 e9 0a             	shr    $0xa,%ecx
    5c45:	48 8d 75 60          	lea    0x60(%rbp),%rsi
    5c49:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5c4d:	48 89 df             	mov    %rbx,%rdi
    5c50:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5c57:	83 e1 01             	and    $0x1,%ecx
    5c5a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5c61:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5c68:	d3 e0                	shl    %cl,%eax
    5c6a:	8b 55 60             	mov    0x60(%rbp),%edx
    5c6d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5c72:	48 c1 e0 06          	shl    $0x6,%rax
    5c76:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5c7e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5c84:	89 50 04             	mov    %edx,0x4(%rax)
    5c87:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5c8f:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5c93:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5c9b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5ca3:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5ca7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5cab:	e8 e0 c6 ff ff       	call   2390 <io_uring_submit@plt>
    5cb0:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5cb4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5cb9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5cc1:	0f 85 d7 01 00 00    	jne    5e9e <io_thread+0x49e>
    5cc7:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5ccc:	4d 89 ce             	mov    %r9,%r14
    5ccf:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5cd4:	0f 1f 40 00          	nopl   0x0(%rax)
    5cd8:	48 8d 3d da 24 00 00 	lea    0x24da(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5cdf:	e8 4c c6 ff ff       	call   2330 <puts@plt>
    5ce4:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5ceb:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    5cf2:	c1 e9 0b             	shr    $0xb,%ecx
    5cf5:	83 e1 01             	and    $0x1,%ecx
    5cf8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5d00:	8b 00                	mov    (%rax),%eax
    5d02:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5d0a:	8b 16                	mov    (%rsi),%edx
    5d0c:	39 d0                	cmp    %edx,%eax
    5d0e:	74 36                	je     5d46 <io_thread+0x346>
    5d10:	89 f8                	mov    %edi,%eax
    5d12:	21 d0                	and    %edx,%eax
    5d14:	d3 e0                	shl    %cl,%eax
    5d16:	48 c1 e0 04          	shl    $0x4,%rax
    5d1a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    5d22:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5d2a:	0f 85 a8 01 00 00    	jne    5ed8 <io_thread+0x4d8>
    5d30:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5d34:	0f 85 0e 03 00 00    	jne    6048 <io_thread+0x648>
    5d3a:	8b 40 08             	mov    0x8(%rax),%eax
    5d3d:	83 c2 01             	add    $0x1,%edx
    5d40:	89 16                	mov    %edx,(%rsi)
    5d42:	85 c0                	test   %eax,%eax
    5d44:	79 b2                	jns    5cf8 <io_thread+0x2f8>
    5d46:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    5d4f:	90                   	nop
    5d50:	45 31 c0             	xor    %r8d,%r8d
    5d53:	31 d2                	xor    %edx,%edx
    5d55:	b9 01 00 00 00       	mov    $0x1,%ecx
    5d5a:	4c 89 f6             	mov    %r14,%rsi
    5d5d:	48 89 df             	mov    %rbx,%rdi
    5d60:	e8 3b c7 ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    5d65:	41 89 c7             	mov    %eax,%r15d
    5d68:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5d6d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5d71:	0f 84 e1 02 00 00    	je     6058 <io_thread+0x658>
    5d77:	48 8d 3d 61 24 00 00 	lea    0x2461(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5d7e:	e8 ad c5 ff ff       	call   2330 <puts@plt>
    5d83:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5d88:	4c 8b 22             	mov    (%rdx),%r12
    5d8b:	45 85 ff             	test   %r15d,%r15d
    5d8e:	0f 88 82 c8 ff ff    	js     2616 <io_thread.cold>
    5d94:	8b 42 08             	mov    0x8(%rdx),%eax
    5d97:	45 8b 04 24          	mov    (%r12),%r8d
    5d9b:	85 c0                	test   %eax,%eax
    5d9d:	0f 88 d5 02 00 00    	js     6078 <io_thread+0x678>
    5da3:	41 83 f8 01          	cmp    $0x1,%r8d
    5da7:	0f 84 7b 01 00 00    	je     5f28 <io_thread+0x528>
    5dad:	41 83 f8 02          	cmp    $0x2,%r8d
    5db1:	0f 84 a1 01 00 00    	je     5f58 <io_thread+0x558>
    5db7:	45 85 c0             	test   %r8d,%r8d
    5dba:	0f 85 50 01 00 00    	jne    5f10 <io_thread+0x510>
    5dc0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5dc5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5dca:	48 89 d9             	mov    %rbx,%rcx
    5dcd:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5dd1:	e8 8a fb ff ff       	call   5960 <add_accept_request>
    5dd6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5ddb:	48 89 de             	mov    %rbx,%rsi
    5dde:	8b 78 08             	mov    0x8(%rax),%edi
    5de1:	e8 1a f5 ff ff       	call   5300 <add_read_request>
    5de6:	4c 89 e7             	mov    %r12,%rdi
    5de9:	e8 12 c5 ff ff       	call   2300 <free@plt>
    5dee:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5df3:	48 85 c0             	test   %rax,%rax
    5df6:	0f 85 14 01 00 00    	jne    5f10 <io_thread+0x510>
    5dfc:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5e03:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5e0a:	8d 50 01             	lea    0x1(%rax),%edx
    5e0d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5e12:	8b 30                	mov    (%rax),%esi
    5e14:	f6 c1 02             	test   $0x2,%cl
    5e17:	74 00                	je     5e19 <io_thread+0x419>
    5e19:	89 d0                	mov    %edx,%eax
    5e1b:	29 f0                	sub    %esi,%eax
    5e1d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5e24:	0f 82 10 c8 ff ff    	jb     263a <io_thread.cold+0x24>
    5e2a:	c1 e9 0a             	shr    $0xa,%ecx
    5e2d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    5e32:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5e36:	48 89 df             	mov    %rbx,%rdi
    5e39:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5e40:	83 e1 01             	and    $0x1,%ecx
    5e43:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5e4a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5e51:	d3 e0                	shl    %cl,%eax
    5e53:	8b 55 60             	mov    0x60(%rbp),%edx
    5e56:	48 c1 e0 06          	shl    $0x6,%rax
    5e5a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5e62:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5e68:	89 50 04             	mov    %edx,0x4(%rax)
    5e6b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5e73:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5e77:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5e7f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5e87:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5e8b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5e8f:	e8 fc c4 ff ff       	call   2390 <io_uring_submit@plt>
    5e94:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5e98:	0f 84 3a fe ff ff    	je     5cd8 <io_thread+0x2d8>
    5e9e:	48 8d 3d 73 23 00 00 	lea    0x2373(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5ea5:	e8 86 c4 ff ff       	call   2330 <puts@plt>
    5eaa:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5eb2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5ebb:	0f 85 18 02 00 00    	jne    60d9 <io_thread+0x6d9>
    5ec1:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5ec8:	31 c0                	xor    %eax,%eax
    5eca:	5b                   	pop    %rbx
    5ecb:	5d                   	pop    %rbp
    5ecc:	41 5c                	pop    %r12
    5ece:	41 5d                	pop    %r13
    5ed0:	41 5e                	pop    %r14
    5ed2:	41 5f                	pop    %r15
    5ed4:	c3                   	ret
    5ed5:	0f 1f 00             	nopl   (%rax)
    5ed8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    5edd:	48 85 c0             	test   %rax,%rax
    5ee0:	0f 84 6a fe ff ff    	je     5d50 <io_thread+0x350>
    5ee6:	48 83 38 01          	cmpq   $0x1,(%rax)
    5eea:	0f 84 68 01 00 00    	je     6058 <io_thread+0x658>
    5ef0:	48 8d 3d e8 22 00 00 	lea    0x22e8(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5ef7:	e8 34 c4 ff ff       	call   2330 <puts@plt>
    5efc:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5f01:	4c 8b 22             	mov    (%rdx),%r12
    5f04:	e9 8b fe ff ff       	jmp    5d94 <io_thread+0x394>
    5f09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5f10:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5f18:	8b 02                	mov    (%rdx),%eax
    5f1a:	83 c0 01             	add    $0x1,%eax
    5f1d:	89 02                	mov    %eax,(%rdx)
    5f1f:	e9 d8 fe ff ff       	jmp    5dfc <io_thread+0x3fc>
    5f24:	0f 1f 40 00          	nopl   0x0(%rax)
    5f28:	85 c0                	test   %eax,%eax
    5f2a:	75 74                	jne    5fa0 <io_thread+0x5a0>
    5f2c:	48 8b 0d ed 50 00 00 	mov    0x50ed(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5f33:	ba 0f 00 00 00       	mov    $0xf,%edx
    5f38:	be 01 00 00 00       	mov    $0x1,%esi
    5f3d:	48 8d 3d c4 22 00 00 	lea    0x22c4(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    5f44:	e8 e7 c5 ff ff       	call   2530 <fwrite@plt>
    5f49:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5f4e:	e9 a0 fe ff ff       	jmp    5df3 <io_thread+0x3f3>
    5f53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5f58:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5f5d:	45 31 ff             	xor    %r15d,%r15d
    5f60:	85 c0                	test   %eax,%eax
    5f62:	7e 20                	jle    5f84 <io_thread+0x584>
    5f64:	0f 1f 40 00          	nopl   0x0(%rax)
    5f68:	4c 89 f8             	mov    %r15,%rax
    5f6b:	49 83 c7 01          	add    $0x1,%r15
    5f6f:	48 c1 e0 04          	shl    $0x4,%rax
    5f73:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5f78:	e8 83 c3 ff ff       	call   2300 <free@plt>
    5f7d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5f82:	7f e4                	jg     5f68 <io_thread+0x568>
    5f84:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5f89:	e8 42 c4 ff ff       	call   23d0 <close@plt>
    5f8e:	4c 89 e7             	mov    %r12,%rdi
    5f91:	e8 6a c3 ff ff       	call   2300 <free@plt>
    5f96:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5f9b:	e9 53 fe ff ff       	jmp    5df3 <io_thread+0x3f3>
    5fa0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5fa5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5faa:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5fb2:	eb 11                	jmp    5fc5 <io_thread+0x5c5>
    5fb4:	0f 1f 40 00          	nopl   0x0(%rax)
    5fb8:	48 83 c0 01          	add    $0x1,%rax
    5fbc:	48 83 c2 01          	add    $0x1,%rdx
    5fc0:	48 39 c6             	cmp    %rax,%rsi
    5fc3:	74 4b                	je     6010 <io_thread+0x610>
    5fc5:	0f b6 0a             	movzbl (%rdx),%ecx
    5fc8:	88 08                	mov    %cl,(%rax)
    5fca:	80 f9 0d             	cmp    $0xd,%cl
    5fcd:	75 e9                	jne    5fb8 <io_thread+0x5b8>
    5fcf:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5fd3:	75 e3                	jne    5fb8 <io_thread+0x5b8>
    5fd5:	c6 00 00             	movb   $0x0,(%rax)
    5fd8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    5fdd:	48 89 da             	mov    %rbx,%rdx
    5fe0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5fe5:	e8 96 f7 ff ff       	call   5780 <handle_http_method>
    5fea:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    5fef:	e8 0c c3 ff ff       	call   2300 <free@plt>
    5ff4:	4c 89 e7             	mov    %r12,%rdi
    5ff7:	e8 04 c3 ff ff       	call   2300 <free@plt>
    5ffc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    6001:	e9 ed fd ff ff       	jmp    5df3 <io_thread+0x3f3>
    6006:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6010:	48 8b 0d 09 50 00 00 	mov    0x5009(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6017:	ba 12 00 00 00       	mov    $0x12,%edx
    601c:	be 01 00 00 00       	mov    $0x1,%esi
    6021:	48 8d 3d 36 21 00 00 	lea    0x2136(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    6028:	e8 03 c5 ff ff       	call   2530 <fwrite@plt>
    602d:	bf 01 00 00 00       	mov    $0x1,%edi
    6032:	e8 d9 c4 ff ff       	call   2510 <exit@plt>
    6037:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    6040:	e9 ec fb ff ff       	jmp    5c31 <io_thread+0x231>
    6045:	0f 1f 00             	nopl   (%rax)
    6048:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    604d:	e9 94 fe ff ff       	jmp    5ee6 <io_thread+0x4e6>
    6052:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6058:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    6060:	48 8d 3d 64 21 00 00 	lea    0x2164(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    6067:	8b 02                	mov    (%rdx),%eax
    6069:	83 c0 01             	add    $0x1,%eax
    606c:	89 02                	mov    %eax,(%rdx)
    606e:	e8 bd c2 ff ff       	call   2330 <puts@plt>
    6073:	e9 26 fe ff ff       	jmp    5e9e <io_thread+0x49e>
    6078:	f7 d8                	neg    %eax
    607a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    607f:	89 c7                	mov    %eax,%edi
    6081:	e8 ea c4 ff ff       	call   2570 <strerror@plt>
    6086:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    608b:	be 01 00 00 00       	mov    $0x1,%esi
    6090:	48 8b 3d 89 4f 00 00 	mov    0x4f89(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    6097:	48 89 c1             	mov    %rax,%rcx
    609a:	48 8d 15 77 25 00 00 	lea    0x2577(%rip),%rdx        # 8618 <_IO_stdin_used+0x618>
    60a1:	31 c0                	xor    %eax,%eax
    60a3:	e8 98 c4 ff ff       	call   2540 <__fprintf_chk@plt>
    60a8:	bf 01 00 00 00       	mov    $0x1,%edi
    60ad:	e8 5e c4 ff ff       	call   2510 <exit@plt>
    60b2:	48 8b 0d 67 4f 00 00 	mov    0x4f67(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    60b9:	ba 28 00 00 00       	mov    $0x28,%edx
    60be:	be 01 00 00 00       	mov    $0x1,%esi
    60c3:	48 8d 3d 1e 25 00 00 	lea    0x251e(%rip),%rdi        # 85e8 <_IO_stdin_used+0x5e8>
    60ca:	e8 61 c4 ff ff       	call   2530 <fwrite@plt>
    60cf:	bf 01 00 00 00       	mov    $0x1,%edi
    60d4:	e8 37 c4 ff ff       	call   2510 <exit@plt>
    60d9:	e8 a2 c2 ff ff       	call   2380 <__stack_chk_fail@plt>
    60de:	66 90                	xchg   %ax,%ax

00000000000060e0 <barriered_work_ingest>:
    60e0:	f3 0f 1e fa          	endbr64
    60e4:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    60eb:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    60f1:	85 c9                	test   %ecx,%ecx
    60f3:	0f 8e ea 00 00 00    	jle    61e3 <barriered_work_ingest+0x103>
    60f9:	41 56                	push   %r14
    60fb:	41 55                	push   %r13
    60fd:	45 31 ed             	xor    %r13d,%r13d
    6100:	41 54                	push   %r12
    6102:	49 89 fc             	mov    %rdi,%r12
    6105:	55                   	push   %rbp
    6106:	53                   	push   %rbx
    6107:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    610b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6110:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    6114:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    611c:	31 db                	xor    %ebx,%ebx
    611e:	8b 10                	mov    (%rax),%edx
    6120:	85 d2                	test   %edx,%edx
    6122:	7e 26                	jle    614a <barriered_work_ingest+0x6a>
    6124:	48 8b 48 08          	mov    0x8(%rax),%rcx
    6128:	48 89 dd             	mov    %rbx,%rbp
    612b:	48 c1 e5 08          	shl    $0x8,%rbp
    612f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    6133:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    613a:	74 24                	je     6160 <barriered_work_ingest+0x80>
    613c:	48 83 c3 01          	add    $0x1,%rbx
    6140:	39 da                	cmp    %ebx,%edx
    6142:	7f e4                	jg     6128 <barriered_work_ingest+0x48>
    6144:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    614a:	49 83 c5 01          	add    $0x1,%r13
    614e:	44 39 e9             	cmp    %r13d,%ecx
    6151:	7f bd                	jg     6110 <barriered_work_ingest+0x30>
    6153:	5b                   	pop    %rbx
    6154:	31 c0                	xor    %eax,%eax
    6156:	5d                   	pop    %rbp
    6157:	41 5c                	pop    %r12
    6159:	41 5d                	pop    %r13
    615b:	41 5e                	pop    %r14
    615d:	c3                   	ret
    615e:	66 90                	xchg   %ax,%ax
    6160:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
    6169:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    6170:	bf 04 00 00 00       	mov    $0x4,%edi
    6175:	48 c1 e6 05          	shl    $0x5,%rsi
    6179:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    6180:	48 83 c6 10          	add    $0x10,%rsi
    6184:	e8 c7 c1 ff ff       	call   2350 <clock_gettime@plt>
    6189:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    6191:	48 8b 40 50          	mov    0x50(%rax),%rax
    6195:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    6199:	48 03 68 08          	add    0x8(%rax),%rbp
    619d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
    61a7:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    61ad:	83 c0 01             	add    $0x1,%eax
    61b0:	99                   	cltd
    61b1:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    61b7:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
    61bd:	0f ae f8             	sfence
    61c0:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    61c8:	48 83 c3 01          	add    $0x1,%rbx
    61cc:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    61d0:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    61d4:	8b 10                	mov    (%rax),%edx
    61d6:	39 da                	cmp    %ebx,%edx
    61d8:	0f 8f 46 ff ff ff    	jg     6124 <barriered_work_ingest+0x44>
    61de:	e9 61 ff ff ff       	jmp    6144 <barriered_work_ingest+0x64>
    61e3:	31 c0                	xor    %eax,%eax
    61e5:	c3                   	ret
    61e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000061f0 <receive>:
    61f0:	f3 0f 1e fa          	endbr64
    61f4:	41 56                	push   %r14
    61f6:	41 55                	push   %r13
    61f8:	41 54                	push   %r12
    61fa:	55                   	push   %rbp
    61fb:	53                   	push   %rbx
    61fc:	4c 63 a7 40 01 00 00 	movslq 0x140(%rdi),%r12
    6203:	45 85 e4             	test   %r12d,%r12d
    6206:	0f 8e 27 01 00 00    	jle    6333 <receive+0x143>
    620c:	4c 8b b7 28 01 00 00 	mov    0x128(%rdi),%r14
    6213:	48 89 fe             	mov    %rdi,%rsi
    6216:	31 db                	xor    %ebx,%ebx
    6218:	49 63 6e 08          	movslq 0x8(%r14),%rbp
    621c:	49 89 ed             	mov    %rbp,%r13
    621f:	90                   	nop
    6220:	41 39 dd             	cmp    %ebx,%r13d
    6223:	0f 84 fd 00 00 00    	je     6326 <receive+0x136>
    6229:	48 89 d8             	mov    %rbx,%rax
    622c:	48 c1 e0 08          	shl    $0x8,%rax
    6230:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    6237:	48 8b 10             	mov    (%rax),%rdx
    623a:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    6240:	83 f8 01             	cmp    $0x1,%eax
    6243:	74 11                	je     6256 <receive+0x66>
    6245:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    624c:	75 08                	jne    6256 <receive+0x66>
    624e:	85 c0                	test   %eax,%eax
    6250:	0f 84 d0 00 00 00    	je     6326 <receive+0x136>
    6256:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    625d:	48 85 ff             	test   %rdi,%rdi
    6260:	0f 8e a2 00 00 00    	jle    6308 <receive+0x118>
    6266:	4c 8b 8e 80 01 00 00 	mov    0x180(%rsi),%r9
    626d:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    6274:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    6278:	4c 8b 1a             	mov    (%rdx),%r11
    627b:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    627f:	49 01 f9             	add    %rdi,%r9
    6282:	49 01 f8             	add    %rdi,%r8
    6285:	48 03 ba 00 04 00 00 	add    0x400(%rdx),%rdi
    628c:	eb 08                	jmp    6296 <receive+0xa6>
    628e:	66 90                	xchg   %ax,%ax
    6290:	48 83 e8 01          	sub    $0x1,%rax
    6294:	72 72                	jb     6308 <receive+0x118>
    6296:	4c 89 c9             	mov    %r9,%rcx
    6299:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
    62a0:	48 29 c1             	sub    %rax,%rcx
    62a3:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
    62aa:	4c 89 c1             	mov    %r8,%rcx
    62ad:	48 29 c1             	sub    %rax,%rcx
    62b0:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
    62b7:	48 89 f9             	mov    %rdi,%rcx
    62ba:	48 29 c1             	sub    %rax,%rcx
    62bd:	48 89 8a 00 04 00 00 	mov    %rcx,0x400(%rdx)
    62c4:	48 63 c8             	movslq %eax,%rcx
    62c7:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
    62cb:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    62cf:	75 bf                	jne    6290 <receive+0xa0>
    62d1:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    62d5:	75 b9                	jne    6290 <receive+0xa0>
    62d7:	49 63 46 04          	movslq 0x4(%r14),%rax
    62db:	31 c9                	xor    %ecx,%ecx
    62dd:	bf 01 00 00 00       	mov    $0x1,%edi
    62e2:	ba 01 00 00 00       	mov    $0x1,%edx
    62e7:	48 8d 35 52 23 00 00 	lea    0x2352(%rip),%rsi        # 8640 <_IO_stdin_used+0x640>
    62ee:	48 39 e8             	cmp    %rbp,%rax
    62f1:	0f 94 c1             	sete   %cl
    62f4:	31 c0                	xor    %eax,%eax
    62f6:	e8 b5 c1 ff ff       	call   24b0 <__printf_chk@plt>
    62fb:	bf 01 00 00 00       	mov    $0x1,%edi
    6300:	e8 0b c2 ff ff       	call   2510 <exit@plt>
    6305:	0f 1f 00             	nopl   (%rax)
    6308:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
    6312:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
    631c:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
    6326:	48 83 c3 01          	add    $0x1,%rbx
    632a:	49 39 dc             	cmp    %rbx,%r12
    632d:	0f 85 ed fe ff ff    	jne    6220 <receive+0x30>
    6333:	0f ae f8             	sfence
    6336:	31 c0                	xor    %eax,%eax
    6338:	5b                   	pop    %rbx
    6339:	5d                   	pop    %rbp
    633a:	41 5c                	pop    %r12
    633c:	41 5d                	pop    %r13
    633e:	41 5e                	pop    %r14
    6340:	c3                   	ret
    6341:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    634c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006350 <sendm>:
    6350:	f3 0f 1e fa          	endbr64
    6354:	41 57                	push   %r15
    6356:	48 89 f9             	mov    %rdi,%rcx
    6359:	41 56                	push   %r14
    635b:	41 55                	push   %r13
    635d:	41 54                	push   %r12
    635f:	55                   	push   %rbp
    6360:	53                   	push   %rbx
    6361:	48 63 bf 40 01 00 00 	movslq 0x140(%rdi),%rdi
    6368:	85 ff                	test   %edi,%edi
    636a:	7e 67                	jle    63d3 <sendm+0x83>
    636c:	48 8b 81 28 01 00 00 	mov    0x128(%rcx),%rax
    6373:	44 8b 48 08          	mov    0x8(%rax),%r9d
    6377:	31 c0                	xor    %eax,%eax
    6379:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6380:	41 39 c1             	cmp    %eax,%r9d
    6383:	74 45                	je     63ca <sendm+0x7a>
    6385:	48 89 c2             	mov    %rax,%rdx
    6388:	48 c1 e2 08          	shl    $0x8,%rdx
    638c:	48 03 91 70 01 00 00 	add    0x170(%rcx),%rdx
    6393:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    639a:	48 8b b2 80 00 00 00 	mov    0x80(%rdx),%rsi
    63a1:	48 85 f6             	test   %rsi,%rsi
    63a4:	7f 24                	jg     63ca <sendm+0x7a>
    63a6:	44 8b 82 00 01 00 00 	mov    0x100(%rdx),%r8d
    63ad:	41 83 f8 01          	cmp    $0x1,%r8d
    63b1:	74 0e                	je     63c1 <sendm+0x71>
    63b3:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    63ba:	75 05                	jne    63c1 <sendm+0x71>
    63bc:	45 85 c0             	test   %r8d,%r8d
    63bf:	74 09                	je     63ca <sendm+0x7a>
    63c1:	83 b9 88 01 00 00 01 	cmpl   $0x1,0x188(%rcx)
    63c8:	74 1e                	je     63e8 <sendm+0x98>
    63ca:	48 83 c0 01          	add    $0x1,%rax
    63ce:	48 39 c7             	cmp    %rax,%rdi
    63d1:	75 ad                	jne    6380 <sendm+0x30>
    63d3:	0f ae f8             	sfence
    63d6:	31 c0                	xor    %eax,%eax
    63d8:	5b                   	pop    %rbx
    63d9:	5d                   	pop    %rbp
    63da:	41 5c                	pop    %r12
    63dc:	41 5d                	pop    %r13
    63de:	41 5e                	pop    %r14
    63e0:	41 5f                	pop    %r15
    63e2:	c3                   	ret
    63e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    63e8:	48 63 aa 88 00 00 00 	movslq 0x88(%rdx),%rbp
    63ef:	48 39 ee             	cmp    %rbp,%rsi
    63f2:	0f 8d a5 00 00 00    	jge    649d <sendm+0x14d>
    63f8:	48 8b 99 08 01 00 00 	mov    0x108(%rcx),%rbx
    63ff:	4c 8b aa 80 03 00 00 	mov    0x380(%rdx),%r13
    6406:	4c 8b 1a             	mov    (%rdx),%r11
    6409:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    640e:	48 89 eb             	mov    %rbp,%rbx
    6411:	48 29 f3             	sub    %rsi,%rbx
    6414:	4c 8d 43 ff          	lea    -0x1(%rbx),%r8
    6418:	49 83 f8 02          	cmp    $0x2,%r8
    641c:	0f 86 0e 01 00 00    	jbe    6530 <sendm+0x1e0>
    6422:	4c 8d 14 ed 00 00 00 00 	lea    0x0(,%rbp,8),%r10
    642a:	4c 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r8
    6432:	4f 8d 34 13          	lea    (%r11,%r10,1),%r14
    6436:	4c 8d b9 90 01 00 00 	lea    0x190(%rcx),%r15
    643d:	4f 8d 24 03          	lea    (%r11,%r8,1),%r12
    6441:	4d 39 f7             	cmp    %r14,%r15
    6444:	73 7a                	jae    64c0 <sendm+0x170>
    6446:	4c 8d b1 98 01 00 00 	lea    0x198(%rcx),%r14
    644d:	4d 39 f4             	cmp    %r14,%r12
    6450:	73 6e                	jae    64c0 <sendm+0x170>
    6452:	4d 01 d8             	add    %r11,%r8
    6455:	4b 8d 34 13          	lea    (%r11,%r10,1),%rsi
    6459:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6460:	4c 8b 91 90 01 00 00 	mov    0x190(%rcx),%r10
    6467:	49 83 c0 08          	add    $0x8,%r8
    646b:	4d 89 50 f8          	mov    %r10,-0x8(%r8)
    646f:	4c 39 c6             	cmp    %r8,%rsi
    6472:	75 ec                	jne    6460 <sendm+0x110>
    6474:	0f 1f 40 00          	nopl   0x0(%rax)
    6478:	48 8b 74 24 f0       	mov    -0x10(%rsp),%rsi
    647d:	48 01 de             	add    %rbx,%rsi
    6480:	4c 01 eb             	add    %r13,%rbx
    6483:	48 89 b1 08 01 00 00 	mov    %rsi,0x108(%rcx)
    648a:	48 89 9a 80 03 00 00 	mov    %rbx,0x380(%rdx)
    6491:	48 89 aa 80 00 00 00 	mov    %rbp,0x80(%rdx)
    6498:	4d 89 54 eb f8       	mov    %r10,-0x8(%r11,%rbp,8)
    649d:	c7 82 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdx)
    64a7:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
    64b1:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
    64bb:	e9 0a ff ff ff       	jmp    63ca <sendm+0x7a>
    64c0:	49 89 de             	mov    %rbx,%r14
    64c3:	4c 8b 91 90 01 00 00 	mov    0x190(%rcx),%r10
    64ca:	4d 89 e0             	mov    %r12,%r8
    64cd:	49 d1 ee             	shr    %r14
    64d0:	49 c1 e6 04          	shl    $0x4,%r14
    64d4:	66 49 0f 6e c2       	movq   %r10,%xmm0
    64d9:	4f 8d 3c 34          	lea    (%r12,%r14,1),%r15
    64dd:	41 83 e6 10          	and    $0x10,%r14d
    64e1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    64e5:	74 11                	je     64f8 <sendm+0x1a8>
    64e7:	49 83 c0 10          	add    $0x10,%r8
    64eb:	41 0f 11 04 24       	movups %xmm0,(%r12)
    64f0:	4d 39 f8             	cmp    %r15,%r8
    64f3:	74 15                	je     650a <sendm+0x1ba>
    64f5:	0f 1f 00             	nopl   (%rax)
    64f8:	41 0f 11 00          	movups %xmm0,(%r8)
    64fc:	49 83 c0 20          	add    $0x20,%r8
    6500:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
    6505:	4d 39 f8             	cmp    %r15,%r8
    6508:	75 ee                	jne    64f8 <sendm+0x1a8>
    650a:	49 89 d8             	mov    %rbx,%r8
    650d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    6511:	4c 01 c6             	add    %r8,%rsi
    6514:	f6 c3 01             	test   $0x1,%bl
    6517:	0f 84 5b ff ff ff    	je     6478 <sendm+0x128>
    651d:	4c 8b 91 90 01 00 00 	mov    0x190(%rcx),%r10
    6524:	4d 89 14 f3          	mov    %r10,(%r11,%rsi,8)
    6528:	e9 4b ff ff ff       	jmp    6478 <sendm+0x128>
    652d:	0f 1f 00             	nopl   (%rax)
    6530:	4c 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r8
    6538:	4c 8d 14 ed 00 00 00 00 	lea    0x0(,%rbp,8),%r10
    6540:	e9 0d ff ff ff       	jmp    6452 <sendm+0x102>
    6545:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000006550 <mailboxkind>:
    6550:	f3 0f 1e fa          	endbr64
    6554:	85 f6                	test   %esi,%esi
    6556:	74 18                	je     6570 <mailboxkind+0x20>
    6558:	31 c0                	xor    %eax,%eax
    655a:	83 fe 01             	cmp    $0x1,%esi
    655d:	74 01                	je     6560 <mailboxkind+0x10>
    655f:	c3                   	ret
    6560:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
    6567:	c3                   	ret
    6568:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6570:	48 8b 07             	mov    (%rdi),%rax
    6573:	c3                   	ret
    6574:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    657f:	90                   	nop

0000000000006580 <setmailboxkind>:
    6580:	f3 0f 1e fa          	endbr64
    6584:	85 d2                	test   %edx,%edx
    6586:	75 08                	jne    6590 <setmailboxkind+0x10>
    6588:	48 89 37             	mov    %rsi,(%rdi)
    658b:	31 c0                	xor    %eax,%eax
    658d:	c3                   	ret
    658e:	66 90                	xchg   %ax,%ax
    6590:	83 fa 01             	cmp    $0x1,%edx
    6593:	74 13                	je     65a8 <setmailboxkind+0x28>
    6595:	83 fa 02             	cmp    $0x2,%edx
    6598:	75 1e                	jne    65b8 <setmailboxkind+0x38>
    659a:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
    65a1:	31 c0                	xor    %eax,%eax
    65a3:	c3                   	ret
    65a4:	0f 1f 40 00          	nopl   0x0(%rax)
    65a8:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
    65af:	31 c0                	xor    %eax,%eax
    65b1:	c3                   	ret
    65b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    65b8:	83 fa 03             	cmp    $0x3,%edx
    65bb:	75 ce                	jne    658b <setmailboxkind+0xb>
    65bd:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
    65c4:	31 c0                	xor    %eax,%eax
    65c6:	c3                   	ret
    65c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000065d0 <fswap>:
    65d0:	f3 0f 1e fa          	endbr64
    65d4:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    65db:	8b 97 9c 01 00 00    	mov    0x19c(%rdi),%edx
    65e1:	44 8b 97 30 01 00 00 	mov    0x130(%rdi),%r10d
    65e8:	48 63 4f 04          	movslq 0x4(%rdi),%rcx
    65ec:	8b 86 c4 00 00 00    	mov    0xc4(%rsi),%eax
    65f2:	0f af d0             	imul   %eax,%edx
    65f5:	41 01 d2             	add    %edx,%r10d
    65f8:	85 c0                	test   %eax,%eax
    65fa:	0f 8e 1b 01 00 00    	jle    671b <fswap+0x14b>
    6600:	4d 63 d2             	movslq %r10d,%r10
    6603:	41 56                	push   %r14
    6605:	48 63 d2             	movslq %edx,%rdx
    6608:	48 c1 e1 09          	shl    $0x9,%rcx
    660c:	41 55                	push   %r13
    660e:	4c 63 d8             	movslq %eax,%r11
    6611:	41 54                	push   %r12
    6613:	49 01 d3             	add    %rdx,%r11
    6616:	55                   	push   %rbp
    6617:	49 c1 e3 08          	shl    $0x8,%r11
    661b:	53                   	push   %rbx
    661c:	48 8b 76 20          	mov    0x20(%rsi),%rsi
    6620:	44 8b 87 34 01 00 00 	mov    0x134(%rdi),%r8d
    6627:	4b 8d 3c 52          	lea    (%r10,%r10,2),%rdi
    662b:	49 c1 e2 08          	shl    $0x8,%r10
    662f:	48 c1 e7 07          	shl    $0x7,%rdi
    6633:	48 8b 5c 3e 38       	mov    0x38(%rsi,%rdi,1),%rbx
    6638:	48 8b ac 0b 70 01 00 00 	mov    0x170(%rbx,%rcx,1),%rbp
    6640:	48 8d 0c 52          	lea    (%rdx,%rdx,2),%rcx
    6644:	48 c1 e1 07          	shl    $0x7,%rcx
    6648:	4c 8d 4c 0e 38       	lea    0x38(%rsi,%rcx,1),%r9
    664d:	48 89 d6             	mov    %rdx,%rsi
    6650:	48 c1 e6 08          	shl    $0x8,%rsi
    6654:	eb 21                	jmp    6677 <fswap+0xa7>
    6656:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6660:	48 81 c6 00 01 00 00 	add    $0x100,%rsi
    6667:	49 81 c1 80 01 00 00 	add    $0x180,%r9
    666e:	49 39 f3             	cmp    %rsi,%r11
    6671:	0f 84 99 00 00 00    	je     6710 <fswap+0x140>
    6677:	83 bc 35 b0 00 00 00 01 	cmpl   $0x1,0xb0(%rbp,%rsi,1)
    667f:	75 df                	jne    6660 <fswap+0x90>
    6681:	49 8b 39             	mov    (%r9),%rdi
    6684:	45 85 c0             	test   %r8d,%r8d
    6687:	7e d7                	jle    6660 <fswap+0x90>
    6689:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    6690:	31 c9                	xor    %ecx,%ecx
    6692:	eb 59                	jmp    66ed <fswap+0x11d>
    6694:	0f 1f 40 00          	nopl   0x0(%rax)
    6698:	48 63 d2             	movslq %edx,%rdx
    669b:	48 c1 e2 09          	shl    $0x9,%rdx
    669f:	4c 8b ac 13 70 01 00 00 	mov    0x170(%rbx,%rdx,1),%r13
    66a7:	49 01 f5             	add    %rsi,%r13
    66aa:	4c 89 ea             	mov    %r13,%rdx
    66ad:	4d 8b 6d 00          	mov    0x0(%r13),%r13
    66b1:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    66b9:	75 22                	jne    66dd <fswap+0x10d>
    66bb:	4c 8b b0 80 00 00 00 	mov    0x80(%rax),%r14
    66c2:	4c 89 32             	mov    %r14,(%rdx)
    66c5:	4c 8b b2 80 00 00 00 	mov    0x80(%rdx),%r14
    66cc:	4c 89 a8 80 00 00 00 	mov    %r13,0x80(%rax)
    66d3:	4c 89 30             	mov    %r14,(%rax)
    66d6:	4c 89 a2 80 00 00 00 	mov    %r12,0x80(%rdx)
    66dd:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    66e4:	41 39 c8             	cmp    %ecx,%r8d
    66e7:	0f 84 73 ff ff ff    	je     6660 <fswap+0x90>
    66ed:	83 c1 01             	add    $0x1,%ecx
    66f0:	89 c8                	mov    %ecx,%eax
    66f2:	99                   	cltd
    66f3:	41 f7 f8             	idiv   %r8d
    66f6:	48 8b 07             	mov    (%rdi),%rax
    66f9:	4c 01 d0             	add    %r10,%rax
    66fc:	4c 8b 20             	mov    (%rax),%r12
    66ff:	49 83 bc 24 80 00 00 00 00 	cmpq   $0x0,0x80(%r12)
    6708:	74 8e                	je     6698 <fswap+0xc8>
    670a:	e9 51 ff ff ff       	jmp    6660 <fswap+0x90>
    670f:	90                   	nop
    6710:	5b                   	pop    %rbx
    6711:	31 c0                	xor    %eax,%eax
    6713:	5d                   	pop    %rbp
    6714:	41 5c                	pop    %r12
    6716:	41 5d                	pop    %r13
    6718:	41 5e                	pop    %r14
    671a:	c3                   	ret
    671b:	31 c0                	xor    %eax,%eax
    671d:	c3                   	ret
    671e:	66 90                	xchg   %ax,%ax

0000000000006720 <barriered_work>:
    6720:	f3 0f 1e fa          	endbr64
    6724:	41 57                	push   %r15
    6726:	41 56                	push   %r14
    6728:	41 55                	push   %r13
    672a:	41 54                	push   %r12
    672c:	55                   	push   %rbp
    672d:	53                   	push   %rbx
    672e:	48 89 fb             	mov    %rdi,%rbx
    6731:	48 83 ec 58          	sub    $0x58,%rsp
    6735:	44 8b 67 04          	mov    0x4(%rdi),%r12d
    6739:	44 39 a7 30 01 00 00 	cmp    %r12d,0x130(%rdi)
    6740:	74 5e                	je     67a0 <barriered_work+0x80>
    6742:	e8 a9 fa ff ff       	call   61f0 <receive>
    6747:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    674e:	75 14                	jne    6764 <barriered_work+0x44>
    6750:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    6758:	0f ae f8             	sfence
    675b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6762:	74 ec                	je     6750 <barriered_work+0x30>
    6764:	48 89 df             	mov    %rbx,%rdi
    6767:	e8 e4 fb ff ff       	call   6350 <sendm>
    676c:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6772:	83 e8 01             	sub    $0x1,%eax
    6775:	44 39 e0             	cmp    %r12d,%eax
    6778:	0f 84 6d 03 00 00    	je     6aeb <barriered_work+0x3cb>
    677e:	c7 83 a0 01 00 00 00 00 00 00 	movl   $0x0,0x1a0(%rbx)
    6788:	0f ae f8             	sfence
    678b:	48 83 c4 58          	add    $0x58,%rsp
    678f:	31 c0                	xor    %eax,%eax
    6791:	5b                   	pop    %rbx
    6792:	5d                   	pop    %rbp
    6793:	41 5c                	pop    %r12
    6795:	41 5d                	pop    %r13
    6797:	41 5e                	pop    %r14
    6799:	41 5f                	pop    %r15
    679b:	c3                   	ret
    679c:	0f 1f 40 00          	nopl   0x0(%rax)
    67a0:	e8 4b fa ff ff       	call   61f0 <receive>
    67a5:	48 63 93 40 01 00 00 	movslq 0x140(%rbx),%rdx
    67ac:	85 d2                	test   %edx,%edx
    67ae:	0f 8e 4f 02 00 00    	jle    6a03 <barriered_work+0x2e3>
    67b4:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    67ba:	4c 8b bb 28 01 00 00 	mov    0x128(%rbx),%r15
    67c1:	31 f6                	xor    %esi,%esi
    67c3:	49 89 d2             	mov    %rdx,%r10
    67c6:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    67ce:	89 44 24 1c          	mov    %eax,0x1c(%rsp)
    67d2:	45 8b 77 08          	mov    0x8(%r15),%r14d
    67d6:	49 63 c4             	movslq %r12d,%rax
    67d9:	48 c1 e0 09          	shl    $0x9,%rax
    67dd:	49 89 c5             	mov    %rax,%r13
    67e0:	49 63 c6             	movslq %r14d,%rax
    67e3:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
    67e7:	48 c1 e0 08          	shl    $0x8,%rax
    67eb:	48 c1 e1 07          	shl    $0x7,%rcx
    67ef:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    67f4:	48 89 cd             	mov    %rcx,%rbp
    67f7:	44 89 e1             	mov    %r12d,%ecx
    67fa:	eb 1d                	jmp    6819 <barriered_work+0xf9>
    67fc:	0f 1f 40 00          	nopl   0x0(%rax)
    6800:	48 83 04 24 01       	addq   $0x1,(%rsp)
    6805:	48 8b 04 24          	mov    (%rsp),%rax
    6809:	48 81 c6 80 01 00 00 	add    $0x180,%rsi
    6810:	49 39 c2             	cmp    %rax,%r10
    6813:	0f 84 e7 01 00 00    	je     6a00 <barriered_work+0x2e0>
    6819:	8b 04 24             	mov    (%rsp),%eax
    681c:	41 39 c6             	cmp    %eax,%r14d
    681f:	74 df                	je     6800 <barriered_work+0xe0>
    6821:	49 8b 57 20          	mov    0x20(%r15),%rdx
    6825:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    682a:	4a 8d 04 2f          	lea    (%rdi,%r13,1),%rax
    682e:	44 8b 80 a0 01 00 00 	mov    0x1a0(%rax),%r8d
    6835:	45 85 c0             	test   %r8d,%r8d
    6838:	75 c6                	jne    6800 <barriered_work+0xe0>
    683a:	4c 8b 44 2a 38       	mov    0x38(%rdx,%rbp,1),%r8
    683f:	4b 8d 14 28          	lea    (%r8,%r13,1),%rdx
    6843:	44 8b 8a a0 01 00 00 	mov    0x1a0(%rdx),%r9d
    684a:	45 85 c9             	test   %r9d,%r9d
    684d:	75 b1                	jne    6800 <barriered_work+0xe0>
    684f:	4c 8b 24 24          	mov    (%rsp),%r12
    6853:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    685a:	49 c1 e4 08          	shl    $0x8,%r12
    685e:	42 83 bc 22 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r12,1)
    6867:	75 97                	jne    6800 <barriered_work+0xe0>
    6869:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    6870:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    6875:	83 bc 10 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rdx,1)
    687d:	75 81                	jne    6800 <barriered_work+0xe0>
    687f:	48 63 44 24 1c       	movslq 0x1c(%rsp),%rax
    6884:	85 c0                	test   %eax,%eax
    6886:	0f 8e 74 ff ff ff    	jle    6800 <barriered_work+0xe0>
    688c:	48 89 c2             	mov    %rax,%rdx
    688f:	4c 89 7c 24 20       	mov    %r15,0x20(%rsp)
    6894:	b8 70 01 00 00       	mov    $0x170,%eax
    6899:	48 c1 e2 09          	shl    $0x9,%rdx
    689d:	89 4c 24 30          	mov    %ecx,0x30(%rsp)
    68a1:	44 89 74 24 34       	mov    %r14d,0x34(%rsp)
    68a6:	4c 8d 9a a0 01 00 00 	lea    0x1a0(%rdx),%r11
    68ad:	48 89 54 24 48       	mov    %rdx,0x48(%rsp)
    68b2:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    68b7:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    68bc:	4c 89 54 24 38       	mov    %r10,0x38(%rsp)
    68c1:	44 8b 54 24 1c       	mov    0x1c(%rsp),%r10d
    68c6:	48 89 74 24 40       	mov    %rsi,0x40(%rsp)
    68cb:	48 89 c6             	mov    %rax,%rsi
    68ce:	66 90                	xchg   %ax,%ax
    68d0:	41 83 c1 01          	add    $0x1,%r9d
    68d4:	49 8b 0c 30          	mov    (%r8,%rsi,1),%rcx
    68d8:	44 89 c8             	mov    %r9d,%eax
    68db:	99                   	cltd
    68dc:	4c 01 e1             	add    %r12,%rcx
    68df:	41 f7 fa             	idiv   %r10d
    68e2:	4c 8b 31             	mov    (%rcx),%r14
    68e5:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    68ea:	4c 8b b1 80 00 00 00 	mov    0x80(%rcx),%r14
    68f1:	48 63 d2             	movslq %edx,%rdx
    68f4:	48 c1 e2 09          	shl    $0x9,%rdx
    68f8:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    6900:	4c 01 e8             	add    %r13,%rax
    6903:	4c 8b 38             	mov    (%rax),%r15
    6906:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    690d:	4c 89 30             	mov    %r14,(%rax)
    6910:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    6915:	4c 89 b0 80 00 00 00 	mov    %r14,0x80(%rax)
    691c:	48 89 11             	mov    %rdx,(%rcx)
    691f:	4c 89 b9 80 00 00 00 	mov    %r15,0x80(%rcx)
    6926:	b9 a0 01 00 00       	mov    $0x1a0,%ecx
    692b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6930:	41 c7 04 08 01 00 00 00 	movl   $0x1,(%r8,%rcx,1)
    6938:	c7 04 0f 01 00 00 00 	movl   $0x1,(%rdi,%rcx,1)
    693f:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
    6946:	49 39 cb             	cmp    %rcx,%r11
    6949:	75 e5                	jne    6930 <barriered_work+0x210>
    694b:	48 8b 0c 37          	mov    (%rdi,%rsi,1),%rcx
    694f:	48 8b 00             	mov    (%rax),%rax
    6952:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
    695d:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    6964:	4a 8b 8c 29 80 00 00 00 	mov    0x80(%rcx,%r13,1),%rcx
    696c:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
    6976:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
    6980:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    698a:	45 39 ca             	cmp    %r9d,%r10d
    698d:	0f 85 3d ff ff ff    	jne    68d0 <barriered_work+0x1b0>
    6993:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
    6998:	48 8b 54 24 48       	mov    0x48(%rsp),%rdx
    699d:	b8 70 01 00 00       	mov    $0x170,%eax
    69a2:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    69a7:	8b 4c 24 30          	mov    0x30(%rsp),%ecx
    69ab:	44 8b 74 24 34       	mov    0x34(%rsp),%r14d
    69b0:	4c 8b 54 24 38       	mov    0x38(%rsp),%r10
    69b5:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    69ba:	4c 8d 9a 70 01 00 00 	lea    0x170(%rdx),%r11
    69c1:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    69c6:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    69cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    69d0:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    69d4:	4d 8b 0c 00          	mov    (%r8,%rax,1),%r9
    69d8:	4a 8b 14 3a          	mov    (%rdx,%r15,1),%rdx
    69dc:	4b 39 14 21          	cmp    %rdx,(%r9,%r12,1)
    69e0:	0f 84 78 01 00 00    	je     6b5e <barriered_work+0x43e>
    69e6:	48 05 00 02 00 00    	add    $0x200,%rax
    69ec:	49 39 c3             	cmp    %rax,%r11
    69ef:	75 df                	jne    69d0 <barriered_work+0x2b0>
    69f1:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    69f6:	e9 05 fe ff ff       	jmp    6800 <barriered_work+0xe0>
    69fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6a00:	41 89 cc             	mov    %ecx,%r12d
    6a03:	48 89 df             	mov    %rbx,%rdi
    6a06:	e8 c5 fb ff ff       	call   65d0 <fswap>
    6a0b:	48 89 df             	mov    %rbx,%rdi
    6a0e:	e8 dd f7 ff ff       	call   61f0 <receive>
    6a13:	0f ae f8             	sfence
    6a16:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6a1d:	31 ff                	xor    %edi,%edi
    6a1f:	48 c1 e6 05          	shl    $0x5,%rsi
    6a23:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6a2a:	e8 21 b9 ff ff       	call   2350 <clock_gettime@plt>
    6a2f:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6a36:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6a3d:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6a41:	8b 72 10             	mov    0x10(%rdx),%esi
    6a44:	8d 6e 01             	lea    0x1(%rsi),%ebp
    6a47:	89 6a 10             	mov    %ebp,0x10(%rdx)
    6a4a:	75 55                	jne    6aa1 <barriered_work+0x381>
    6a4c:	0f 1f 40 00          	nopl   0x0(%rax)
    6a50:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    6a57:	48 8b 40 18          	mov    0x18(%rax),%rax
    6a5b:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
    6a5f:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    6a67:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6a6b:	48 c1 e7 09          	shl    $0x9,%rdi
    6a6f:	48 03 78 38          	add    0x38(%rax),%rdi
    6a73:	ff 93 20 01 00 00    	call   *0x120(%rbx)
    6a79:	0f ae f8             	sfence
    6a7c:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6a83:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6a8a:	74 c4                	je     6a50 <barriered_work+0x330>
    6a8c:	48 8b 40 48          	mov    0x48(%rax),%rax
    6a90:	3b 68 10             	cmp    0x10(%rax),%ebp
    6a93:	74 0c                	je     6aa1 <barriered_work+0x381>
    6a95:	48 8d 3d aa 17 00 00 	lea    0x17aa(%rip),%rdi        # 8246 <_IO_stdin_used+0x246>
    6a9c:	e8 8f b8 ff ff       	call   2330 <puts@plt>
    6aa1:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6aa8:	31 ff                	xor    %edi,%edi
    6aaa:	48 c1 e6 05          	shl    $0x5,%rsi
    6aae:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6ab5:	48 83 c6 10          	add    $0x10,%rsi
    6ab9:	e8 92 b8 ff ff       	call   2350 <clock_gettime@plt>
    6abe:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6ac5:	48 83 c0 01          	add    $0x1,%rax
    6ac9:	48 99                	cqto
    6acb:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6ad2:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6ad8:	83 e8 01             	sub    $0x1,%eax
    6adb:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    6ae2:	44 39 e0             	cmp    %r12d,%eax
    6ae5:	0f 85 93 fc ff ff    	jne    677e <barriered_work+0x5e>
    6aeb:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    6af2:	85 d2                	test   %edx,%edx
    6af4:	0f 8e 84 fc ff ff    	jle    677e <barriered_work+0x5e>
    6afa:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    6b01:	48 c1 e2 09          	shl    $0x9,%rdx
    6b05:	48 63 41 08          	movslq 0x8(%rcx),%rax
    6b09:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    6b0d:	48 c1 e0 07          	shl    $0x7,%rax
    6b11:	48 03 41 20          	add    0x20(%rcx),%rax
    6b15:	48 8b 40 38          	mov    0x38(%rax),%rax
    6b19:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    6b1d:	80 e6 02             	and    $0x2,%dh
    6b20:	74 1e                	je     6b40 <barriered_work+0x420>
    6b22:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    6b29:	48 05 00 02 00 00    	add    $0x200,%rax
    6b2f:	48 39 c8             	cmp    %rcx,%rax
    6b32:	0f 84 46 fc ff ff    	je     677e <barriered_work+0x5e>
    6b38:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6b40:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    6b47:	83 80 a4 03 00 00 01 	addl   $0x1,0x3a4(%rax)
    6b4e:	48 05 00 04 00 00    	add    $0x400,%rax
    6b54:	48 39 c8             	cmp    %rcx,%rax
    6b57:	75 e7                	jne    6b40 <barriered_work+0x420>
    6b59:	e9 20 fc ff ff       	jmp    677e <barriered_work+0x5e>
    6b5e:	bf 01 00 00 00       	mov    $0x1,%edi
    6b63:	48 8d 35 c1 16 00 00 	lea    0x16c1(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    6b6a:	31 c0                	xor    %eax,%eax
    6b6c:	e8 3f b9 ff ff       	call   24b0 <__printf_chk@plt>
    6b71:	bf 01 00 00 00       	mov    $0x1,%edi
    6b76:	e8 95 b9 ff ff       	call   2510 <exit@plt>
    6b7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006b80 <barriered_work_ingest_andwork>:
    6b80:	f3 0f 1e fa          	endbr64
    6b84:	53                   	push   %rbx
    6b85:	48 89 fb             	mov    %rdi,%rbx
    6b88:	e8 53 f5 ff ff       	call   60e0 <barriered_work_ingest>
    6b8d:	48 89 df             	mov    %rbx,%rdi
    6b90:	5b                   	pop    %rbx
    6b91:	e9 8a fb ff ff       	jmp    6720 <barriered_work>
    6b96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006ba0 <microtasks>:
    6ba0:	f3 0f 1e fa          	endbr64
    6ba4:	49 89 f0             	mov    %rsi,%r8
    6ba7:	8d 47 ff             	lea    -0x1(%rdi),%eax
    6baa:	85 ff                	test   %edi,%edi
    6bac:	7f 06                	jg     6bb4 <microtasks+0x14>
    6bae:	8b 46 40             	mov    0x40(%rsi),%eax
    6bb1:	83 e8 01             	sub    $0x1,%eax
    6bb4:	83 fa ff             	cmp    $0xffffffff,%edx
    6bb7:	0f 84 b3 00 00 00    	je     6c70 <microtasks+0xd0>
    6bbd:	41 83 78 44 01       	cmpl   $0x1,0x44(%r8)
    6bc2:	0f 85 a8 00 00 00    	jne    6c70 <microtasks+0xd0>
    6bc8:	49 8b 48 18          	mov    0x18(%r8),%rcx
    6bcc:	48 63 d2             	movslq %edx,%rdx
    6bcf:	4c 63 d8             	movslq %eax,%r11
    6bd2:	4c 63 d7             	movslq %edi,%r10
    6bd5:	49 c1 e3 09          	shl    $0x9,%r11
    6bd9:	49 c1 e2 09          	shl    $0x9,%r10
    6bdd:	4d 03 50 38          	add    0x38(%r8),%r10
    6be1:	48 8b 14 d1          	mov    (%rcx,%rdx,8),%rdx
    6be5:	4c 03 5a 38          	add    0x38(%rdx),%r11
    6be9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6bf0:	41 8b 83 80 00 00 00 	mov    0x80(%r11),%eax
    6bf7:	41 3b 82 80 00 00 00 	cmp    0x80(%r10),%eax
    6bfe:	7d 70                	jge    6c70 <microtasks+0xd0>
    6c00:	41 8b b8 08 01 00 00 	mov    0x108(%r8),%edi
    6c07:	85 ff                	test   %edi,%edi
    6c09:	7e 6d                	jle    6c78 <microtasks+0xd8>
    6c0b:	4d 8b 88 00 01 00 00 	mov    0x100(%r8),%r9
    6c12:	31 d2                	xor    %edx,%edx
    6c14:	0f 1f 40 00          	nopl   0x0(%rax)
    6c18:	41 8b 0c 91          	mov    (%r9,%rdx,4),%ecx
    6c1c:	89 ce                	mov    %ecx,%esi
    6c1e:	c1 ee 1f             	shr    $0x1f,%esi
    6c21:	8d 04 31             	lea    (%rcx,%rsi,1),%eax
    6c24:	83 e0 01             	and    $0x1,%eax
    6c27:	29 f0                	sub    %esi,%eax
    6c29:	41 3b 40 04          	cmp    0x4(%r8),%eax
    6c2d:	74 11                	je     6c40 <microtasks+0xa0>
    6c2f:	48 83 c2 01          	add    $0x1,%rdx
    6c33:	39 d7                	cmp    %edx,%edi
    6c35:	7f e1                	jg     6c18 <microtasks+0x78>
    6c37:	41 83 78 44 01       	cmpl   $0x1,0x44(%r8)
    6c3c:	74 b2                	je     6bf0 <microtasks+0x50>
    6c3e:	c3                   	ret
    6c3f:	90                   	nop
    6c40:	83 c1 01             	add    $0x1,%ecx
    6c43:	41 89 0c 91          	mov    %ecx,(%r9,%rdx,4)
    6c47:	41 8b b8 08 01 00 00 	mov    0x108(%r8),%edi
    6c4e:	48 83 c2 01          	add    $0x1,%rdx
    6c52:	49 83 80 10 01 00 00 01 	addq   $0x1,0x110(%r8)
    6c5a:	39 d7                	cmp    %edx,%edi
    6c5c:	7f ba                	jg     6c18 <microtasks+0x78>
    6c5e:	41 83 78 44 01       	cmpl   $0x1,0x44(%r8)
    6c63:	74 8b                	je     6bf0 <microtasks+0x50>
    6c65:	c3                   	ret
    6c66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6c70:	c3                   	ret
    6c71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6c78:	41 8b 92 80 00 00 00 	mov    0x80(%r10),%edx
    6c7f:	39 c2                	cmp    %eax,%edx
    6c81:	7f fc                	jg     6c7f <microtasks+0xdf>
    6c83:	c3                   	ret
    6c84:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6c8f:	90                   	nop

0000000000006c90 <barriered_thread>:
    6c90:	f3 0f 1e fa          	endbr64
    6c94:	41 57                	push   %r15
    6c96:	41 56                	push   %r14
    6c98:	41 55                	push   %r13
    6c9a:	45 31 ed             	xor    %r13d,%r13d
    6c9d:	41 54                	push   %r12
    6c9f:	45 31 e4             	xor    %r12d,%r12d
    6ca2:	55                   	push   %rbp
    6ca3:	bd ff ff ff ff       	mov    $0xffffffff,%ebp
    6ca8:	53                   	push   %rbx
    6ca9:	48 89 fb             	mov    %rdi,%rbx
    6cac:	48 83 ec 18          	sub    $0x18,%rsp
    6cb0:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6cb4:	0f 85 30 02 00 00    	jne    6eea <barriered_thread+0x25a>
    6cba:	8b 43 40             	mov    0x40(%rbx),%eax
    6cbd:	0f 1f 00             	nopl   (%rax)
    6cc0:	41 39 c5             	cmp    %eax,%r13d
    6cc3:	7c 13                	jl     6cd8 <barriered_thread+0x48>
    6cc5:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    6ccd:	45 31 ed             	xor    %r13d,%r13d
    6cd0:	85 c0                	test   %eax,%eax
    6cd2:	0f 8e 08 02 00 00    	jle    6ee0 <barriered_thread+0x250>
    6cd8:	4d 63 f5             	movslq %r13d,%r14
    6cdb:	49 c1 e6 09          	shl    $0x9,%r14
    6cdf:	eb 59                	jmp    6d3a <barriered_thread+0xaa>
    6ce1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6ce8:	48 8d 35 67 15 00 00 	lea    0x1567(%rip),%rsi        # 8256 <_IO_stdin_used+0x256>
    6cef:	44 89 ea             	mov    %r13d,%edx
    6cf2:	bf 01 00 00 00       	mov    $0x1,%edi
    6cf7:	31 c0                	xor    %eax,%eax
    6cf9:	e8 b2 b7 ff ff       	call   24b0 <__printf_chk@plt>
    6cfe:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6d02:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6d06:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6d0a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6d0e:	4c 01 f7             	add    %r14,%rdi
    6d11:	e8 ca f3 ff ff       	call   60e0 <barriered_work_ingest>
    6d16:	89 ea                	mov    %ebp,%edx
    6d18:	48 89 de             	mov    %rbx,%rsi
    6d1b:	44 89 ef             	mov    %r13d,%edi
    6d1e:	e8 7d fe ff ff       	call   6ba0 <microtasks>
    6d23:	8b 43 40             	mov    0x40(%rbx),%eax
    6d26:	41 83 c5 01          	add    $0x1,%r13d
    6d2a:	49 81 c6 00 02 00 00 	add    $0x200,%r14
    6d31:	44 39 e8             	cmp    %r13d,%eax
    6d34:	0f 8e a6 01 00 00    	jle    6ee0 <barriered_thread+0x250>
    6d3a:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6d3e:	4a 8d 34 32          	lea    (%rdx,%r14,1),%rsi
    6d42:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    6d49:	75 9d                	jne    6ce8 <barriered_thread+0x58>
    6d4b:	44 8b 5b 28          	mov    0x28(%rbx),%r11d
    6d4f:	83 e8 01             	sub    $0x1,%eax
    6d52:	41 8d 4d ff          	lea    -0x1(%r13),%ecx
    6d56:	45 85 ed             	test   %r13d,%r13d
    6d59:	0f 4f c1             	cmovg  %ecx,%eax
    6d5c:	45 85 db             	test   %r11d,%r11d
    6d5f:	0f 8e bb 01 00 00    	jle    6f20 <barriered_thread+0x290>
    6d65:	48 63 c8             	movslq %eax,%rcx
    6d68:	44 8b 86 80 00 00 00 	mov    0x80(%rsi),%r8d
    6d6f:	4c 8b 4b 18          	mov    0x18(%rbx),%r9
    6d73:	31 c0                	xor    %eax,%eax
    6d75:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
    6d7b:	48 c1 e1 09          	shl    $0x9,%rcx
    6d7f:	49 63 f3             	movslq %r11d,%rsi
    6d82:	45 31 d2             	xor    %r10d,%r10d
    6d85:	44 89 5c 24 0c       	mov    %r11d,0xc(%rsp)
    6d8a:	45 31 ff             	xor    %r15d,%r15d
    6d8d:	eb 18                	jmp    6da7 <barriered_thread+0x117>
    6d8f:	90                   	nop
    6d90:	89 c5                	mov    %eax,%ebp
    6d92:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    6d98:	75 04                	jne    6d9e <barriered_thread+0x10e>
    6d9a:	41 83 c2 01          	add    $0x1,%r10d
    6d9e:	48 83 c0 01          	add    $0x1,%rax
    6da2:	48 39 c6             	cmp    %rax,%rsi
    6da5:	74 21                	je     6dc8 <barriered_thread+0x138>
    6da7:	49 8b 14 c1          	mov    (%r9,%rax,8),%rdx
    6dab:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6daf:	49 01 cb             	add    %rcx,%r11
    6db2:	4c 89 da             	mov    %r11,%rdx
    6db5:	45 3b 83 80 00 00 00 	cmp    0x80(%r11),%r8d
    6dbc:	75 d2                	jne    6d90 <barriered_thread+0x100>
    6dbe:	41 83 c7 01          	add    $0x1,%r15d
    6dc2:	eb ce                	jmp    6d92 <barriered_thread+0x102>
    6dc4:	0f 1f 40 00          	nopl   0x0(%rax)
    6dc8:	44 8b 5c 24 0c       	mov    0xc(%rsp),%r11d
    6dcd:	45 85 d2             	test   %r10d,%r10d
    6dd0:	0f 84 9a 00 00 00    	je     6e70 <barriered_thread+0x1e0>
    6dd6:	45 39 d3             	cmp    %r10d,%r11d
    6dd9:	0f 84 91 00 00 00    	je     6e70 <barriered_thread+0x1e0>
    6ddf:	45 85 ff             	test   %r15d,%r15d
    6de2:	74 0a                	je     6dee <barriered_thread+0x15e>
    6de4:	44 39 7b 28          	cmp    %r15d,0x28(%rbx)
    6de8:	0f 85 83 01 00 00    	jne    6f71 <barriered_thread+0x2e1>
    6dee:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6df2:	4c 01 f2             	add    %r14,%rdx
    6df5:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
    6dfc:	45 85 ed             	test   %r13d,%r13d
    6dff:	75 14                	jne    6e15 <barriered_thread+0x185>
    6e01:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6e08:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    6e0f:	0f 8c eb 00 00 00    	jl     6f00 <barriered_thread+0x270>
    6e15:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    6e19:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6e1d:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
    6e27:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    6e2b:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6e2f:	4c 01 f7             	add    %r14,%rdi
    6e32:	ff 92 18 01 00 00    	call   *0x118(%rdx)
    6e38:	48 8b 43 38          	mov    0x38(%rbx),%rax
    6e3c:	4c 01 f0             	add    %r14,%rax
    6e3f:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
    6e46:	8b 43 40             	mov    0x40(%rbx),%eax
    6e49:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
    6e4e:	83 e8 01             	sub    $0x1,%eax
    6e51:	44 39 e8             	cmp    %r13d,%eax
    6e54:	74 32                	je     6e88 <barriered_thread+0x1f8>
    6e56:	0f ae f8             	sfence
    6e59:	45 85 e4             	test   %r12d,%r12d
    6e5c:	74 5a                	je     6eb8 <barriered_thread+0x228>
    6e5e:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    6e64:	e9 ba fe ff ff       	jmp    6d23 <barriered_thread+0x93>
    6e69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6e70:	41 83 fc 01          	cmp    $0x1,%r12d
    6e74:	0f 84 b6 00 00 00    	je     6f30 <barriered_thread+0x2a0>
    6e7a:	45 31 e4             	xor    %r12d,%r12d
    6e7d:	e9 5d ff ff ff       	jmp    6ddf <barriered_thread+0x14f>
    6e82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6e88:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6e8f:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    6e96:	7d be                	jge    6e56 <barriered_thread+0x1c6>
    6e98:	48 c1 e6 04          	shl    $0x4,%rsi
    6e9c:	bf 04 00 00 00       	mov    $0x4,%edi
    6ea1:	48 03 73 70          	add    0x70(%rbx),%rsi
    6ea5:	e8 a6 b4 ff ff       	call   2350 <clock_gettime@plt>
    6eaa:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    6eb2:	eb a2                	jmp    6e56 <barriered_thread+0x1c6>
    6eb4:	0f 1f 40 00          	nopl   0x0(%rax)
    6eb8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6ebf:	bf 04 00 00 00       	mov    $0x4,%edi
    6ec4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6ec8:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6ecf:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    6ed3:	44 89 6e 20          	mov    %r13d,0x20(%rsi)
    6ed7:	e8 74 b4 ff ff       	call   2350 <clock_gettime@plt>
    6edc:	eb 80                	jmp    6e5e <barriered_thread+0x1ce>
    6ede:	66 90                	xchg   %ax,%ax
    6ee0:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6ee4:	0f 84 d6 fd ff ff    	je     6cc0 <barriered_thread+0x30>
    6eea:	48 83 c4 18          	add    $0x18,%rsp
    6eee:	31 c0                	xor    %eax,%eax
    6ef0:	5b                   	pop    %rbx
    6ef1:	5d                   	pop    %rbp
    6ef2:	41 5c                	pop    %r12
    6ef4:	41 5d                	pop    %r13
    6ef6:	41 5e                	pop    %r14
    6ef8:	41 5f                	pop    %r15
    6efa:	c3                   	ret
    6efb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6f00:	48 c1 e6 04          	shl    $0x4,%rsi
    6f04:	bf 04 00 00 00       	mov    $0x4,%edi
    6f09:	48 03 73 68          	add    0x68(%rbx),%rsi
    6f0d:	e8 3e b4 ff ff       	call   2350 <clock_gettime@plt>
    6f12:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6f16:	4c 01 f2             	add    %r14,%rdx
    6f19:	e9 f7 fe ff ff       	jmp    6e15 <barriered_thread+0x185>
    6f1e:	66 90                	xchg   %ax,%ax
    6f20:	41 83 fc 01          	cmp    $0x1,%r12d
    6f24:	0f 85 c8 fe ff ff    	jne    6df2 <barriered_thread+0x162>
    6f2a:	45 31 ff             	xor    %r15d,%r15d
    6f2d:	0f 1f 00             	nopl   (%rax)
    6f30:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6f37:	bf 04 00 00 00       	mov    $0x4,%edi
    6f3c:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6f40:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6f47:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    6f4c:	e8 ff b3 ff ff       	call   2350 <clock_gettime@plt>
    6f51:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6f58:	48 83 c0 01          	add    $0x1,%rax
    6f5c:	48 99                	cqto
    6f5e:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    6f65:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
    6f6c:	e9 09 ff ff ff       	jmp    6e7a <barriered_thread+0x1ea>
    6f71:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6f75:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6f79:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6f7d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6f81:	4c 01 f7             	add    %r14,%rdi
    6f84:	e8 57 f1 ff ff       	call   60e0 <barriered_work_ingest>
    6f89:	89 ea                	mov    %ebp,%edx
    6f8b:	48 89 de             	mov    %rbx,%rsi
    6f8e:	44 89 ef             	mov    %r13d,%edi
    6f91:	e8 0a fc ff ff       	call   6ba0 <microtasks>
    6f96:	e9 15 fd ff ff       	jmp    6cb0 <barriered_thread+0x20>
    6f9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006fa0 <barriered_nulltask>:
    6fa0:	f3 0f 1e fa          	endbr64
    6fa4:	31 c0                	xor    %eax,%eax
    6fa6:	c3                   	ret
    6fa7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006fb0 <barriered_steal>:
    6fb0:	f3 0f 1e fa          	endbr64
    6fb4:	31 c0                	xor    %eax,%eax
    6fb6:	c3                   	ret
    6fb7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006fc0 <after>:
    6fc0:	f3 0f 1e fa          	endbr64
    6fc4:	31 c0                	xor    %eax,%eax
    6fc6:	48 39 d7             	cmp    %rdx,%rdi
    6fc9:	7e 08                	jle    6fd3 <after+0x13>
    6fcb:	31 c0                	xor    %eax,%eax
    6fcd:	48 39 ce             	cmp    %rcx,%rsi
    6fd0:	0f 9f c0             	setg   %al
    6fd3:	c3                   	ret
    6fd4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6fdf:	90                   	nop

0000000000006fe0 <within>:
    6fe0:	f3 0f 1e fa          	endbr64
    6fe4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6fe9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    6fee:	31 c0                	xor    %eax,%eax
    6ff0:	48 39 d7             	cmp    %rdx,%rdi
    6ff3:	7f 18                	jg     700d <within+0x2d>
    6ff5:	4d 39 d8             	cmp    %r11,%r8
    6ff8:	0f 9e c2             	setle  %dl
    6ffb:	48 39 ce             	cmp    %rcx,%rsi
    6ffe:	0f 9e c0             	setle  %al
    7001:	21 c2                	and    %eax,%edx
    7003:	31 c0                	xor    %eax,%eax
    7005:	4d 39 d1             	cmp    %r10,%r9
    7008:	0f 9e c0             	setle  %al
    700b:	21 d0                	and    %edx,%eax
    700d:	c3                   	ret
    700e:	66 90                	xchg   %ax,%ax

0000000000007010 <overlap>:
    7010:	f3 0f 1e fa          	endbr64
    7014:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    7019:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    701e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    7023:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    7028:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    702d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
    7032:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    7037:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    703c:	48 39 fe             	cmp    %rdi,%rsi
    703f:	7d 2f                	jge    7070 <overlap+0x60>
    7041:	48 39 ca             	cmp    %rcx,%rdx
    7044:	7d 62                	jge    70a8 <overlap+0x98>
    7046:	4d 39 da             	cmp    %r11,%r10
    7049:	7d 0e                	jge    7059 <overlap+0x49>
    704b:	b8 01 00 00 00       	mov    $0x1,%eax
    7050:	4d 39 c1             	cmp    %r8,%r9
    7053:	0f 8c 7f 00 00 00    	jl     70d8 <overlap+0xc8>
    7059:	31 c0                	xor    %eax,%eax
    705b:	4d 39 c1             	cmp    %r8,%r9
    705e:	7f 4c                	jg     70ac <overlap+0x9c>
    7060:	31 c0                	xor    %eax,%eax
    7062:	4d 39 da             	cmp    %r11,%r10
    7065:	0f 9e c0             	setle  %al
    7068:	c3                   	ret
    7069:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7070:	7e 4e                	jle    70c0 <overlap+0xb0>
    7072:	48 39 ca             	cmp    %rcx,%rdx
    7075:	7f 39                	jg     70b0 <overlap+0xa0>
    7077:	75 31                	jne    70aa <overlap+0x9a>
    7079:	4d 39 c1             	cmp    %r8,%r9
    707c:	7c 2c                	jl     70aa <overlap+0x9a>
    707e:	b8 01 00 00 00       	mov    $0x1,%eax
    7083:	4d 39 da             	cmp    %r11,%r10
    7086:	7d 24                	jge    70ac <overlap+0x9c>
    7088:	48 39 ca             	cmp    %rcx,%rdx
    708b:	0f 94 c2             	sete   %dl
    708e:	48 39 fe             	cmp    %rdi,%rsi
    7091:	0f 94 c0             	sete   %al
    7094:	21 c2                	and    %eax,%edx
    7096:	31 c0                	xor    %eax,%eax
    7098:	4d 39 c1             	cmp    %r8,%r9
    709b:	0f 94 c0             	sete   %al
    709e:	21 d0                	and    %edx,%eax
    70a0:	c3                   	ret
    70a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    70a8:	74 af                	je     7059 <overlap+0x49>
    70aa:	31 c0                	xor    %eax,%eax
    70ac:	c3                   	ret
    70ad:	0f 1f 00             	nopl   (%rax)
    70b0:	4d 39 da             	cmp    %r11,%r10
    70b3:	7e c4                	jle    7079 <overlap+0x69>
    70b5:	b8 01 00 00 00       	mov    $0x1,%eax
    70ba:	4d 39 c1             	cmp    %r8,%r9
    70bd:	7e ba                	jle    7079 <overlap+0x69>
    70bf:	c3                   	ret
    70c0:	48 39 ca             	cmp    %rcx,%rdx
    70c3:	7c 94                	jl     7059 <overlap+0x49>
    70c5:	4d 39 c1             	cmp    %r8,%r9
    70c8:	7d b4                	jge    707e <overlap+0x6e>
    70ca:	48 39 ca             	cmp    %rcx,%rdx
    70cd:	74 91                	je     7060 <overlap+0x50>
    70cf:	eb d9                	jmp    70aa <overlap+0x9a>
    70d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    70d8:	c3                   	ret
    70d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000070e0 <verify>:
    70e0:	f3 0f 1e fa          	endbr64
    70e4:	85 f6                	test   %esi,%esi
    70e6:	0f 8e 44 03 00 00    	jle    7430 <verify+0x350>
    70ec:	41 57                	push   %r15
    70ee:	41 89 f7             	mov    %esi,%r15d
    70f1:	41 56                	push   %r14
    70f3:	45 31 f6             	xor    %r14d,%r14d
    70f6:	41 55                	push   %r13
    70f8:	41 54                	push   %r12
    70fa:	55                   	push   %rbp
    70fb:	53                   	push   %rbx
    70fc:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    7100:	48 83 ec 58          	sub    $0x58,%rsp
    7104:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    7109:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    710e:	45 31 e4             	xor    %r12d,%r12d
    7111:	45 39 e6             	cmp    %r12d,%r14d
    7114:	0f 84 4e 02 00 00    	je     7368 <verify+0x288>
    711a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    711f:	8b 50 08             	mov    0x8(%rax),%edx
    7122:	85 d2                	test   %edx,%edx
    7124:	0f 8e 3e 02 00 00    	jle    7368 <verify+0x288>
    712a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    712f:	31 c9                	xor    %ecx,%ecx
    7131:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    7136:	31 c0                	xor    %eax,%eax
    7138:	44 89 f2             	mov    %r14d,%edx
    713b:	bf 01 00 00 00       	mov    $0x1,%edi
    7140:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    7145:	48 8d 35 1c 11 00 00 	lea    0x111c(%rip),%rsi        # 8268 <_IO_stdin_used+0x268>
    714c:	e8 5f b3 ff ff       	call   24b0 <__printf_chk@plt>
    7151:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7156:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    715b:	8b 40 08             	mov    0x8(%rax),%eax
    715e:	85 c0                	test   %eax,%eax
    7160:	0f 8e e6 01 00 00    	jle    734c <verify+0x26c>
    7166:	48 89 c8             	mov    %rcx,%rax
    7169:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    716e:	31 db                	xor    %ebx,%ebx
    7170:	48 c1 e0 09          	shl    $0x9,%rax
    7174:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    7179:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    717e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7183:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    7188:	4c 8b 20             	mov    (%rax),%r12
    718b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7190:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    7195:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    719a:	49 89 de             	mov    %rbx,%r14
    719d:	48 8d 35 d9 10 00 00 	lea    0x10d9(%rip),%rsi        # 827d <_IO_stdin_used+0x27d>
    71a4:	49 c1 e6 09          	shl    $0x9,%r14
    71a8:	bf 01 00 00 00       	mov    $0x1,%edi
    71ad:	48 8b 45 00          	mov    0x0(%rbp),%rax
    71b1:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    71b9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    71be:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    71c6:	31 c0                	xor    %eax,%eax
    71c8:	e8 e3 b2 ff ff       	call   24b0 <__printf_chk@plt>
    71cd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    71d2:	4c 8b 20             	mov    (%rax),%r12
    71d5:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    71de:	0f 8e 47 01 00 00    	jle    732b <verify+0x24b>
    71e4:	4c 03 75 00          	add    0x0(%rbp),%r14
    71e8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    71ed:	ba 01 00 00 00       	mov    $0x1,%edx
    71f2:	4d 89 f5             	mov    %r14,%r13
    71f5:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    71fc:	4d 85 f6             	test   %r14,%r14
    71ff:	0f 8e 21 01 00 00    	jle    7326 <verify+0x246>
    7205:	0f 1f 00             	nopl   (%rax)
    7208:	48 89 d5             	mov    %rdx,%rbp
    720b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7210:	31 db                	xor    %ebx,%ebx
    7212:	4d 89 f2             	mov    %r14,%r10
    7215:	48 c1 e5 05          	shl    $0x5,%rbp
    7219:	48 83 ed 20          	sub    $0x20,%rbp
    721d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    7221:	49 89 ee             	mov    %rbp,%r14
    7224:	48 89 dd             	mov    %rbx,%rbp
    7227:	48 89 d3             	mov    %rdx,%rbx
    722a:	eb 31                	jmp    725d <verify+0x17d>
    722c:	0f 1f 40 00          	nopl   0x0(%rax)
    7230:	4c 39 c2             	cmp    %r8,%rdx
    7233:	0f 8d 57 01 00 00    	jge    7390 <verify+0x2b0>
    7239:	4c 39 df             	cmp    %r11,%rdi
    723c:	7e 05                	jle    7243 <verify+0x163>
    723e:	49 39 c1             	cmp    %rax,%r9
    7241:	7c 75                	jl     72b8 <verify+0x1d8>
    7243:	4c 39 df             	cmp    %r11,%rdi
    7246:	0f 8d ab 01 00 00    	jge    73f7 <verify+0x317>
    724c:	0f 1f 40 00          	nopl   0x0(%rax)
    7250:	48 83 c5 01          	add    $0x1,%rbp
    7254:	49 39 ea             	cmp    %rbp,%r10
    7257:	0f 8e a9 00 00 00    	jle    7306 <verify+0x226>
    725d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    7264:	48 89 e8             	mov    %rbp,%rax
    7267:	48 c1 e0 05          	shl    $0x5,%rax
    726b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    7272:	4c 01 f2             	add    %r14,%rdx
    7275:	48 8b 08             	mov    (%rax),%rcx
    7278:	48 8b 78 10          	mov    0x10(%rax),%rdi
    727c:	48 8b 32             	mov    (%rdx),%rsi
    727f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    7283:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    7287:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    728b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    728f:	48 8b 40 18          	mov    0x18(%rax),%rax
    7293:	48 39 f1             	cmp    %rsi,%rcx
    7296:	7c 98                	jl     7230 <verify+0x150>
    7298:	0f 8e 42 01 00 00    	jle    73e0 <verify+0x300>
    729e:	4c 39 c2             	cmp    %r8,%rdx
    72a1:	0f 8f f9 00 00 00    	jg     73a0 <verify+0x2c0>
    72a7:	75 a7                	jne    7250 <verify+0x170>
    72a9:	4c 39 df             	cmp    %r11,%rdi
    72ac:	7f a2                	jg     7250 <verify+0x170>
    72ae:	49 39 c1             	cmp    %rax,%r9
    72b1:	7c 9d                	jl     7250 <verify+0x170>
    72b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    72b8:	49 89 c1             	mov    %rax,%r9
    72bb:	48 89 f9             	mov    %rdi,%rcx
    72be:	48 89 f2             	mov    %rsi,%rdx
    72c1:	bf 01 00 00 00       	mov    $0x1,%edi
    72c6:	48 8d 35 9b 13 00 00 	lea    0x139b(%rip),%rsi        # 8668 <_IO_stdin_used+0x668>
    72cd:	31 c0                	xor    %eax,%eax
    72cf:	48 83 c5 01          	add    $0x1,%rbp
    72d3:	e8 d8 b1 ff ff       	call   24b0 <__printf_chk@plt>
    72d8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    72dd:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    72e2:	4c 03 28             	add    (%rax),%r13
    72e5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    72ea:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
    72f1:	4c 8b 20             	mov    (%rax),%r12
    72f4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    72f9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    72fd:	49 39 ea             	cmp    %rbp,%r10
    7300:	0f 8f 57 ff ff ff    	jg     725d <verify+0x17d>
    7306:	48 89 da             	mov    %rbx,%rdx
    7309:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    7310:	7d 14                	jge    7326 <verify+0x246>
    7312:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7319:	48 83 c2 01          	add    $0x1,%rdx
    731d:	4d 85 f6             	test   %r14,%r14
    7320:	0f 8f e2 fe ff ff    	jg     7208 <verify+0x128>
    7326:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    732b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7330:	48 83 c3 01          	add    $0x1,%rbx
    7334:	39 58 08             	cmp    %ebx,0x8(%rax)
    7337:	0f 8f 53 fe ff ff    	jg     7190 <verify+0xb0>
    733d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    7342:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    7347:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
    734c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7351:	48 83 c1 01          	add    $0x1,%rcx
    7355:	39 48 08             	cmp    %ecx,0x8(%rax)
    7358:	0f 8f d8 fd ff ff    	jg     7136 <verify+0x56>
    735e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    7363:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    7368:	48 81 44 24 10 80 01 00 00 	addq   $0x180,0x10(%rsp)
    7371:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    7376:	41 39 c7             	cmp    %eax,%r15d
    7379:	0f 84 86 00 00 00    	je     7405 <verify+0x325>
    737f:	41 89 c4             	mov    %eax,%r12d
    7382:	e9 8a fd ff ff       	jmp    7111 <verify+0x31>
    7387:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    7390:	0f 85 ba fe ff ff    	jne    7250 <verify+0x170>
    7396:	e9 a8 fe ff ff       	jmp    7243 <verify+0x163>
    739b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    73a0:	49 39 c1             	cmp    %rax,%r9
    73a3:	7e 09                	jle    73ae <verify+0x2ce>
    73a5:	4c 39 df             	cmp    %r11,%rdi
    73a8:	0f 8c 0a ff ff ff    	jl     72b8 <verify+0x1d8>
    73ae:	4c 39 df             	cmp    %r11,%rdi
    73b1:	0f 8f 99 fe ff ff    	jg     7250 <verify+0x170>
    73b7:	49 39 c1             	cmp    %rax,%r9
    73ba:	0f 8d f8 fe ff ff    	jge    72b8 <verify+0x1d8>
    73c0:	48 39 f1             	cmp    %rsi,%rcx
    73c3:	0f 85 87 fe ff ff    	jne    7250 <verify+0x170>
    73c9:	4c 39 c2             	cmp    %r8,%rdx
    73cc:	0f 85 7e fe ff ff    	jne    7250 <verify+0x170>
    73d2:	4c 39 df             	cmp    %r11,%rdi
    73d5:	0f 84 dd fe ff ff    	je     72b8 <verify+0x1d8>
    73db:	e9 70 fe ff ff       	jmp    7250 <verify+0x170>
    73e0:	4c 39 c2             	cmp    %r8,%rdx
    73e3:	0f 8c 5a fe ff ff    	jl     7243 <verify+0x163>
    73e9:	4c 39 df             	cmp    %r11,%rdi
    73ec:	7e c9                	jle    73b7 <verify+0x2d7>
    73ee:	4c 39 c2             	cmp    %r8,%rdx
    73f1:	0f 85 59 fe ff ff    	jne    7250 <verify+0x170>
    73f7:	49 39 c1             	cmp    %rax,%r9
    73fa:	0f 8f 50 fe ff ff    	jg     7250 <verify+0x170>
    7400:	e9 b3 fe ff ff       	jmp    72b8 <verify+0x1d8>
    7405:	48 81 44 24 18 80 01 00 00 	addq   $0x180,0x18(%rsp)
    740e:	41 8d 46 01          	lea    0x1(%r14),%eax
    7412:	45 39 e6             	cmp    %r12d,%r14d
    7415:	74 08                	je     741f <verify+0x33f>
    7417:	41 89 c6             	mov    %eax,%r14d
    741a:	e9 ea fc ff ff       	jmp    7109 <verify+0x29>
    741f:	48 83 c4 58          	add    $0x58,%rsp
    7423:	31 c0                	xor    %eax,%eax
    7425:	5b                   	pop    %rbx
    7426:	5d                   	pop    %rbp
    7427:	41 5c                	pop    %r12
    7429:	41 5d                	pop    %r13
    742b:	41 5e                	pop    %r14
    742d:	41 5f                	pop    %r15
    742f:	c3                   	ret
    7430:	31 c0                	xor    %eax,%eax
    7432:	c3                   	ret

Disassembly of section .fini:

0000000000007434 <_fini>:
    7434:	f3 0f 1e fa          	endbr64
    7438:	48 83 ec 08          	sub    $0x8,%rsp
    743c:	48 83 c4 08          	add    $0x8,%rsp
    7440:	c3                   	ret
